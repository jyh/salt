/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S13MSelect2
import Salt.MR.M4AssemblyFrames

/-!
# ⟦W-EPS⟧ — THE `εr` GROUP OF `S13CapGatePerBlock`, SUPPLIED AT THE SOCKET

**PURELY ADDITIVE.**  No landed declaration is touched; nothing here is imported by
`Salt/MR/All.lean` until the seal (CAPGATE ruling 10).

This page supplies the SEVEN `εr`/`EP₂` fields of `S13FramesB.S13CapGatePerBlock` at the
working point `SocketBase R M H L q j A s` + `loglogFloor50 ≤ R.Hlo`, base `X_d = A + s`:

| field | line | how |
|---|---|---|
| `epsr_nonneg` | 1078 | `S13MSelect2.s13_theta293_margin_lo` |
| `abs8640` | 1080 | `S13MSelect2.s13_abs8640_at_shift`, byte-exact at `εr = θ₂₉₃ − 1/500` |
| `EP2_gate` | 1082 | §3 — the three row bounds, simultaneously |
| `q_arcDen` | 1086 | `SocketBase`'s own modulus field |
| `phi_row` | 1090 | `le_max` at the witness `s13CapEP2` |
| `p2_row` | 1092 | `le_max` at the witness `s13CapEP2` |
| `tail_row` | 1097 | `le_max` at the witness `s13CapEP2` |

## ⟦THE DESIGN⟧ — `EP₂` as the MAX of the three rows

`phi_row`, `p2_row` and `tail_row` all read `· ≤ EP₂` while `EP2_gate` reads
`12·EP₂ ≤ (log X_d)^{−θ₂₉₃+εr}`.  Taking

  `EP₂ := max (φ-row LHS) (max (p²-row LHS) (tail-row LHS))`   (`s13CapEP2`)

makes the three rows `le_max` — FREE — and concentrates the whole group into ONE demand:
each row LHS is `≤ (1/12)·(log X_d)^{−1/500}`.  §3 proves the three.

## ⟦THE SCALE THIS CLOSES ON⟧ — the x-scale, NOT `gArmEge`

Every estimate below is priced against `S13MSelect2.s13_socketBase_loglogA_sharp`:

  `Λ := loglog X_d ≥ ½·log H ≥ ½·e^{50} = 2.59·10²¹` ,

FIFTEEN orders above `M4AssemblyFrames.gArmEge`'s own floor `8500·loglog H + 7800`.  The
`φ(q)` ledger is `SocketBase`'s `q ≤ arcDen 12 H = (log H)^{12}`, so every charge the group
carries is a POLYNOMIAL in `u := log H` against the EXPONENTIAL `(log X_d)^{εr} = e^{εr·Λ}`
with `Λ ≥ u/2`.  §1's `capeps_master` is that comparison, once, at slack `≤ 50` in the log —
which is why one stone serves all four charges (`49920`, `3072·C`, `24576`, `49152`).

## ⟦THE HYPOTHESIS REGISTER⟧ (what `s13CapEps_all` asks beyond the socket)

* `hεr : θ₂₉₃ − 1/500 ≤ εr` — the pin, in its monotone-WEAKENING form (all three `εr`
  readers get EASIER as `εr` grows; `θ₂₉₃ − 1/500` is the maximum the window allows, and
  instantiating there is `le_rfl`).
* `hT0 : 0 ≤ Tann`, `hTX : Tann ≤ X_d` — the family's own `2·T ≤ A + s` (`S13FramesB`
  §8f's `hThi`), verbatim.
* `hP83 : P₈₃ X_d θ₂₉₃ ≤ P` — the bundle's own `P_low` field.
* `hgrade : log P/log Q ≤ 2·(loglog X_d)·(log X_d)^{−θ₂₉₃}` — `M4RowSupply`'s landed
  `m4_tail_grade_rounded`, i.e. the ℕ-pins `P = ⌈P₈₃⌉₊`, `Q = ⌊Q₈₃⌋₊`.  Without a grade
  bound the tail row is FALSE (at `P = Q` the ratio is `1`).
* `hC0 : 0 < C`, `hC : log C ≤ 40` — the coprime-tail constant's size.  `C` is opaque
  (`TypicalPrice.blockfree_sum_le`'s `∃ C`), so its numeric gate rides the statement, the
  same genre as `M4RowSupply.m4_ep2_budget_at_band`'s own `2688·C·loglog X ≤ (log X)^ε`
  (law #253).  The corpus value is `2·e^{19/log 2} + 1 = 1.6·10¹² ≤ e^{28.1}`.
-/

open Salt.Entropy.Chowla

noncomputable section

namespace Salt.MR

/-! ## §1 — the numerals and ⟦THE MASTER STONE⟧ -/

/-- `10²¹ ≤ e^{50}` (true value `5.18·10²¹`), via `e^{10} ≥ 22026`. -/
theorem capeps_ten21_le_exp50 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.exp 50 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h10 : (22026 : ℝ) ≤ Real.exp 10 := by
    have hh : Real.exp 10 = (Real.exp 1) ^ (10 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    rw [hh]
    have hc : (2.7182818283 : ℝ) ^ (10 : ℕ) ≤ (Real.exp 1) ^ (10 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 10
    have : (22026 : ℝ) ≤ (2.7182818283 : ℝ) ^ (10 : ℕ) := by norm_num
    linarith
  have h50 : Real.exp 50 = (Real.exp 10) ^ (5 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : (22026 : ℝ) ^ (5 : ℕ) ≤ (Real.exp 10) ^ (5 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h10 5
  have hn : (10 : ℝ) ^ (21 : ℕ) ≤ (22026 : ℝ) ^ (5 : ℕ) := by norm_num
  rw [h50]; linarith

/-- `y²/4 ≤ e^y` at `y ≥ 0` — `e^y = (e^{y/2})²` against `y/2 ≤ e^{y/2}`. -/
theorem capeps_sq_le_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 2 / 4 ≤ Real.exp y := by
  have hhalf : y / 2 ≤ Real.exp (y / 2) := by
    have := Real.add_one_le_exp (y / 2); linarith
  have hsq : Real.exp y = (Real.exp (y / 2)) ^ (2 : ℕ) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hsq]
  nlinarith [hhalf, hy]

/-- **⟦THE MASTER STONE⟧** (`capeps_master`) — at the socket's x-scale floor
(`u = log H ≥ 10²¹`, `Λ = loglog X_d ≥ u/2`) any charge `t ≤ 50` plus the modulus ledger's
`12·log u` plus `log Λ` is swallowed by `(14/10000)·Λ`, the `εr`-window's own coefficient
(`s13_theta293_margin_lo`).  Certified margin at the floor: `~10¹⁵×`. -/
theorem capeps_master {u Λ t : ℝ} (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hΛ : u / 2 ≤ Λ)
    (ht : t ≤ 50) : t + 12 * Real.log u + Real.log Λ ≤ 14 / 10000 * Λ := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hu2L : u ≤ 2 * Λ := by linarith
  have hlogu : Real.log u ≤ 1 + Real.log Λ := by
    have h1 : Real.log u ≤ Real.log (2 * Λ) := Real.log_le_log hu0 hu2L
    have h2 : Real.log (2 * Λ) = Real.log 2 + Real.log Λ :=
      Real.log_mul (by norm_num) (ne_of_gt hΛ0)
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith
  have hsq0 : (0 : ℝ) < Real.sqrt Λ := Real.sqrt_pos.mpr hΛ0
  have hsqrt : Real.log Λ ≤ 2 * Real.sqrt Λ := by
    have h := Real.log_le_sub_one_of_pos hsq0
    have hs : Real.log (Real.sqrt Λ) = Real.log Λ / 2 := Real.log_sqrt hΛ0.le
    rw [hs] at h; linarith
  have hsu : Real.sqrt Λ * Real.sqrt Λ = Λ := Real.mul_self_sqrt hΛ0.le
  have hLbig : (5 : ℝ) * 10 ^ (20 : ℕ) ≤ Λ := by
    have : (10 : ℝ) ^ (21 : ℕ) = 2 * (5 * 10 ^ (20 : ℕ)) := by norm_num
    linarith
  have hs10 : (2 : ℝ) * 10 ^ (10 : ℕ) ≤ Real.sqrt Λ := by
    nlinarith [hsu, hLbig, hsq0]
  nlinarith [hsqrt, hsu, hs10, hsq0, hlogu, ht]

/-! ## §2 — the three exponential stones -/

section Stones

variable {u μ t : ℝ}

/-- `u¹² = e^{12·log u}`. -/
theorem capeps_pow12 (hu0 : 0 < u) : u ^ (12 : ℕ) = Real.exp (12 * Real.log u) := by
  rw [show (12 : ℝ) * Real.log u = ((12 : ℕ) : ℝ) * Real.log u by norm_num,
    ← Real.log_pow, Real.exp_log (pow_pos hu0 12)]

/-- **⟦THE `εr`-BUDGET STONE⟧** `e^t·u¹²·Λ ≤ μ^{θ₂₉₃−1/500}` at `t ≤ 50`. -/
theorem capeps_expbound (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (ht : t ≤ 50) :
    Real.exp t * u ^ (12 : ℕ) * Real.log μ ≤ μ ^ (theta293 - 1 / 500) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hmas := capeps_master hu hΛ ht
  have hθ := s13_theta293_margin_lo
  have hlhs : Real.exp (t + 12 * Real.log u + Real.log (Real.log μ))
      = Real.exp t * u ^ (12 : ℕ) * Real.log μ := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hΛ0, ← capeps_pow12 hu0]
  rw [← hlhs, Real.rpow_def_of_pos hμ0]
  refine Real.exp_le_exp.mpr ?_
  have : 14 / 10000 * Real.log μ ≤ Real.log μ * (theta293 - 1 / 500) := by nlinarith
  linarith

/-- **⟦THE BASE-SIZED STONE⟧** `e^t·u¹²·μ² ≤ e^{μ−Λ/500}` — the `1/X_d` crumbs' home
(`μ = e^Λ ≥ Λ²/4 ≥ 3Λ` at the socket floor). -/
theorem capeps_bigexp (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (ht : t ≤ 50) :
    Real.exp t * u ^ (12 : ℕ) * μ ^ 2 ≤ Real.exp (μ - Real.log μ / 500) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hΛbig : (5 : ℝ) * 10 ^ (20 : ℕ) ≤ Real.log μ := by
    have : (10 : ℝ) ^ (21 : ℕ) = 2 * (5 * 10 ^ (20 : ℕ)) := by norm_num
    linarith
  have hmas := capeps_master hu hΛ ht
  have hlogΛ : 0 ≤ Real.log (Real.log μ) := Real.log_nonneg (by linarith)
  have hsq : (Real.log μ) ^ 2 / 4 ≤ μ := by
    have h := capeps_sq_le_exp hΛ0.le
    rwa [Real.exp_log hμ0] at h
  have h3Λ : 3 * Real.log μ ≤ μ := by nlinarith [hsq, hΛbig, hΛ0]
  have hμ2 : μ ^ 2 = Real.exp (2 * Real.log μ) := by
    rw [show (2 : ℝ) * Real.log μ = ((2 : ℕ) : ℝ) * Real.log μ by norm_num,
      ← Real.log_pow, Real.exp_log (pow_pos hμ0 2)]
  have hlhs : Real.exp (t + 12 * Real.log u + 2 * Real.log μ)
      = Real.exp t * u ^ (12 : ℕ) * μ ^ 2 := by
    rw [Real.exp_add, Real.exp_add, ← capeps_pow12 hu0, ← hμ2]
  rw [← hlhs]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **⟦THE `P₈₃` STONE⟧** `e^{11}·u¹²·μ·μ^{1/500} ≤ e^{μ^{1−θ₂₉₃}}` — the `p²` row's
`1/P` leg, against `μ^{1−θ₂₉₃} ≥ e^{Λ/2} ≥ Λ²/16`. -/
theorem capeps_Pbig (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) :
    Real.exp 11 * u ^ (12 : ℕ) * μ * μ ^ ((1 : ℝ) / 500)
      ≤ Real.exp (μ ^ (1 - theta293)) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hΛbig : (5 : ℝ) * 10 ^ (20 : ℕ) ≤ Real.log μ := by
    have : (10 : ℝ) ^ (21 : ℕ) = 2 * (5 * 10 ^ (20 : ℕ)) := by norm_num
    linarith
  have hmas := capeps_master hu hΛ (by norm_num : (11 : ℝ) ≤ 50)
  have hlogΛ : 0 ≤ Real.log (Real.log μ) := Real.log_nonneg (by linarith)
  have hθ32 : theta293 < 1 / 32 := theta293_lt_one_div_32
  have hθ0 : (0 : ℝ) < theta293 := theta293_pos
  have hrw : μ ^ (1 - theta293) = Real.exp ((1 - theta293) * Real.log μ) := by
    rw [Real.rpow_def_of_pos hμ0]; ring_nf
  have hhalf : Real.exp (Real.log μ / 2) ≤ μ ^ (1 - theta293) := by
    rw [hrw]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hsq : (Real.log μ / 2) ^ 2 / 4 ≤ Real.exp (Real.log μ / 2) :=
    capeps_sq_le_exp (by linarith)
  have hbig : 2 * Real.log μ ≤ μ ^ (1 - theta293) := by nlinarith [hsq, hhalf, hΛbig, hΛ0]
  have h500 : μ ^ ((1 : ℝ) / 500) = Real.exp (Real.log μ / 500) := by
    rw [Real.rpow_def_of_pos hμ0]; ring_nf
  have hlhs : Real.exp (11 + 12 * Real.log u + Real.log μ + Real.log μ / 500)
      = Real.exp 11 * u ^ (12 : ℕ) * μ * μ ^ ((1 : ℝ) / 500) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, ← capeps_pow12 hu0, Real.exp_log hμ0,
      ← h500]
  rw [← hlhs]
  exact Real.exp_le_exp.mpr (le_trans (by linarith) hbig)

/-- `X·μ^{−1/500} = e^{μ−Λ/500}` at `log X = μ` — the shape both `1/X_d` crumbs price at. -/
theorem capeps_Xmu {X : ℝ} (hX0 : 0 < X) (hXlog : Real.log X = μ) (hμ0 : 0 < μ) :
    X * μ ^ (-(1 / 500) : ℝ) = Real.exp (μ - Real.log μ / 500) := by
  have hX : X = Real.exp μ := by rw [← hXlog, Real.exp_log hX0]
  rw [hX, Real.rpow_def_of_pos hμ0, ← Real.exp_add]
  congr 1
  ring

end Stones

/-! ## §3 — the three row bounds, abstractly

Each is `12·(row LHS) ≤ (log X_d)^{−1/500}`, i.e. the row's own twelfth of the `EP2_gate`
budget.  `W` is the shared co-factor prefactor `4·(2φ(q)·T_ann + 7φ(q)·2X_d/q)`, priced at
`W ≤ 64·u¹²·X_d` in §4. -/

section Rows

variable {u μ X W C r β Pr φ : ℝ}

/-- **⟦THE `φ(q)` ROW⟧** `12·(4160·φ(q)·μ^{−θ₂₉₃}) ≤ μ^{−1/500}` — i.e. the `E_ge` line
`49920·φ(q) ≤ μ^{εr}`, at the modulus ledger `φ(q) ≤ q ≤ u¹²`. -/
theorem capeps_row_phi (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (hφ0 : 0 ≤ φ) (hφ : φ ≤ u ^ (12 : ℕ)) :
    12 * (4160 * φ * μ ^ (-theta293)) ≤ μ ^ (-(1 / 500) : ℝ) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Real.log μ := by linarith
  have hp12 : (0 : ℝ) < u ^ (12 : ℕ) := pow_pos hu0 12
  have he11 : (49920 : ℝ) ≤ Real.exp 11 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hh : Real.exp 11 = (Real.exp 1) ^ (11 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7182818283 : ℝ) ^ (11 : ℕ) ≤ (Real.exp 1) ^ (11 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 11
    have : (49920 : ℝ) ≤ (2.7182818283 : ℝ) ^ (11 : ℕ) := by norm_num
    rw [hh]; linarith
  have hstone := capeps_expbound hu hμ hΛ (by norm_num : (11 : ℝ) ≤ 50)
  have hkey : 49920 * φ ≤ μ ^ (theta293 - 1 / 500) := by
    have h1 : 49920 * φ ≤ Real.exp 11 * u ^ (12 : ℕ) := by nlinarith
    have h2 : Real.exp 11 * u ^ (12 : ℕ)
        ≤ Real.exp 11 * u ^ (12 : ℕ) * Real.log μ := by
      nlinarith [Real.exp_pos (11 : ℝ)]
    linarith
  have hT0 : (0 : ℝ) < μ ^ (-theta293) := Real.rpow_pos_of_pos hμ0 _
  have hsplit : μ ^ (-theta293) * μ ^ (theta293 - 1 / 500) = μ ^ (-(1 / 500) : ℝ) := by
    rw [← Real.rpow_add hμ0]; congr 1; ring
  calc 12 * (4160 * φ * μ ^ (-theta293)) = (49920 * φ) * μ ^ (-theta293) := by ring
    _ ≤ μ ^ (theta293 - 1 / 500) * μ ^ (-theta293) :=
        mul_le_mul_of_nonneg_right hkey hT0.le
    _ = μ ^ (-theta293) * μ ^ (theta293 - 1 / 500) := by ring
    _ = μ ^ (-(1 / 500) : ℝ) := hsplit

/-- **⟦THE COPRIME-TAIL ROW⟧** `12·(W·M_tail) ≤ μ^{−1/500}` at the band grade
`r ≤ 2·Λ·μ^{−θ₂₉₃}` (`M4RowSupply.m4_tail_grade_rounded`).  The two legs: `3072·C·u¹²·Λ`
against `μ^{εr}` (§2's `εr`-budget stone at `t = 38`), and `1536·u¹²` against
`X_d·μ^{−1/500}` (the base-sized stone at `t = 8`). -/
theorem capeps_row_tail (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (hX0 : 0 < X) (hXlog : Real.log X = μ)
    (hW0 : 0 ≤ W) (hW : W ≤ 64 * u ^ (12 : ℕ) * X) (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hr : r ≤ 2 * (Real.log μ * μ ^ (-theta293))) :
    12 * (W * (C * r / X + 1 / X ^ 2)) ≤ μ ^ (-(1 / 500) : ℝ) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Real.log μ := by linarith
  have hp12 : (0 : ℝ) < u ^ (12 : ℕ) := pow_pos hu0 12
  have hT0 : (0 : ℝ) < μ ^ (-theta293) := Real.rpow_pos_of_pos hμ0 _
  have hXne : X ≠ 0 := ne_of_gt hX0
  -- ⟦the grade, into the second factor⟧
  have hinv : (0 : ℝ) ≤ X⁻¹ := by positivity
  have hstep : C * r / X + 1 / X ^ 2
      ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2 := by
    have h1 : C * r ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) :=
      mul_le_mul_of_nonneg_left hr hC0.le
    have h2 : C * r / X ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) / X := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h1 hinv
    linarith
  have hS0 : (0 : ℝ) ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2 := by
    have : (0 : ℝ) ≤ C * (2 * (Real.log μ * μ ^ (-theta293))) / X := by positivity
    have h2 : (0 : ℝ) ≤ 1 / X ^ 2 := by positivity
    linarith
  have hprod : W * (C * r / X + 1 / X ^ 2)
      ≤ 64 * u ^ (12 : ℕ) * X * (C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2) :=
    le_trans (mul_le_mul_of_nonneg_left hstep hW0) (mul_le_mul_of_nonneg_right hW hS0)
  have hval : 64 * u ^ (12 : ℕ) * X
        * (C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2)
      = 128 * C * u ^ (12 : ℕ) * Real.log μ * μ ^ (-theta293) + 64 * u ^ (12 : ℕ) / X := by
    field_simp
    ring
  -- ⟦leg 1⟧ `3072·C·u¹²·Λ ≤ μ^{θ₂₉₃−1/500}`
  have hCle : C ≤ Real.exp 40 := by
    have := Real.exp_le_exp.mpr hC
    rwa [Real.exp_log hC0] at this
  have h3072 : (3072 : ℝ) ≤ Real.exp 9 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hh : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7182818283 : ℝ) ^ (9 : ℕ) ≤ (Real.exp 1) ^ (9 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 9
    have : (3072 : ℝ) ≤ (2.7182818283 : ℝ) ^ (9 : ℕ) := by norm_num
    rw [hh]; linarith
  have h38 : (3072 : ℝ) * C ≤ Real.exp 49 := by
    have hsum : Real.exp 49 = Real.exp 9 * Real.exp 40 := by rw [← Real.exp_add]; norm_num
    rw [hsum]
    exact mul_le_mul h3072 hCle hC0.le (Real.exp_pos 9).le
  have hlegA : 1536 * C * u ^ (12 : ℕ) * Real.log μ * μ ^ (-theta293)
      ≤ μ ^ (-(1 / 500) : ℝ) / 2 := by
    have hstone := capeps_expbound hu hμ hΛ (by norm_num : (49 : ℝ) ≤ 50)
    have hmul : 3072 * C * (u ^ (12 : ℕ) * Real.log μ)
        ≤ Real.exp 49 * (u ^ (12 : ℕ) * Real.log μ) :=
      mul_le_mul_of_nonneg_right h38 (by positivity)
    have h1 : 3072 * C * u ^ (12 : ℕ) * Real.log μ ≤ μ ^ (theta293 - 1 / 500) := by
      linarith [hmul, hstone]
    have h2 : 3072 * C * u ^ (12 : ℕ) * Real.log μ * μ ^ (-theta293)
        ≤ μ ^ (theta293 - 1 / 500) * μ ^ (-theta293) :=
      mul_le_mul_of_nonneg_right h1 hT0.le
    have hsplit : μ ^ (theta293 - 1 / 500) * μ ^ (-theta293) = μ ^ (-(1 / 500) : ℝ) := by
      rw [← Real.rpow_add hμ0]; congr 1; ring
    rw [hsplit] at h2
    linarith
  -- ⟦leg 2⟧ `1536·u¹² ≤ X·μ^{−1/500}`
  have hlegB : 64 * u ^ (12 : ℕ) / X ≤ μ ^ (-(1 / 500) : ℝ) / 24 := by
    have hstone := capeps_bigexp hu hμ hΛ (by norm_num : (8 : ℝ) ≤ 50)
    have he8 : (1536 : ℝ) ≤ Real.exp 8 := by
      have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have hh : Real.exp 8 = (Real.exp 1) ^ (8 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have hc : (2.7182818283 : ℝ) ^ (8 : ℕ) ≤ (Real.exp 1) ^ (8 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) h1.le 8
      have : (1536 : ℝ) ≤ (2.7182818283 : ℝ) ^ (8 : ℕ) := by norm_num
      rw [hh]; linarith
    have hμ2 : (1 : ℝ) ≤ μ ^ 2 := by nlinarith
    have ha : 1536 * u ^ (12 : ℕ) ≤ Real.exp 8 * u ^ (12 : ℕ) :=
      mul_le_mul_of_nonneg_right he8 hp12.le
    have hbb : Real.exp 8 * u ^ (12 : ℕ) ≤ Real.exp 8 * u ^ (12 : ℕ) * μ ^ 2 :=
      le_mul_of_one_le_right (by positivity) hμ2
    have h1 : 1536 * u ^ (12 : ℕ) ≤ Real.exp 8 * u ^ (12 : ℕ) * μ ^ 2 := by linarith
    have h2 : 1536 * u ^ (12 : ℕ) ≤ X * μ ^ (-(1 / 500) : ℝ) := by
      rw [capeps_Xmu hX0 hXlog hμ0]; linarith
    rw [div_le_div_iff₀ hX0 (by norm_num : (0 : ℝ) < 24)]
    nlinarith [h2]
  calc 12 * (W * (C * r / X + 1 / X ^ 2))
      ≤ 12 * (64 * u ^ (12 : ℕ) * X
          * (C * (2 * (Real.log μ * μ ^ (-theta293))) / X + 1 / X ^ 2)) := by linarith
    _ = 12 * (128 * C * u ^ (12 : ℕ) * Real.log μ * μ ^ (-theta293)
          + 64 * u ^ (12 : ℕ) / X) := by rw [hval]
    _ ≤ μ ^ (-(1 / 500) : ℝ) := by linarith

/-- **⟦THE `p²`/END-MASS ROW⟧** `12·(W·(16β/(X·P) + 4β²/X²)) ≤ μ^{−1/500}` at
`β = log₂(2X_d) ≤ 2μ` and `P ≥ P₈₃ = e^{μ^{1−θ₂₉₃}}`.  Both legs are free by
FOUR exponentiations: `P` is `e^{e^{(1−θ)Λ}}`-large and `X_d` is `e^{e^Λ}`-large. -/
theorem capeps_row_p2 (hu : (10 : ℝ) ^ (21 : ℕ) ≤ u) (hμ : (2000 : ℝ) ≤ μ)
    (hΛ : u / 2 ≤ Real.log μ) (hX0 : 0 < X) (hXlog : Real.log X = μ)
    (hW0 : 0 ≤ W) (hW : W ≤ 64 * u ^ (12 : ℕ) * X) (hβ0 : 0 ≤ β) (hβ : β ≤ 2 * μ)
    (hPr : Real.exp (μ ^ (1 - theta293)) ≤ Pr) :
    12 * (W * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2)) ≤ μ ^ (-(1 / 500) : ℝ) := by
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Real.log μ := by linarith
  have hp12 : (0 : ℝ) < u ^ (12 : ℕ) := pow_pos hu0 12
  have hPr0 : (0 : ℝ) < Pr := lt_of_lt_of_le (Real.exp_pos _) hPr
  have hXne : X ≠ 0 := ne_of_gt hX0
  have hPne : Pr ≠ 0 := ne_of_gt hPr0
  have hK0 : (0 : ℝ) < μ ^ (-(1 / 500) : ℝ) := Real.rpow_pos_of_pos hμ0 _
  have hS0 : (0 : ℝ) ≤ 16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2 := by
    have h1 : (0 : ℝ) ≤ 16 * β / (X * Pr) := by positivity
    have h2 : (0 : ℝ) ≤ 4 * β ^ 2 / X ^ 2 := by positivity
    linarith
  have hprod : W * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2)
      ≤ 64 * u ^ (12 : ℕ) * X * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2) :=
    mul_le_mul_of_nonneg_right hW hS0
  have hval : 64 * u ^ (12 : ℕ) * X * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2)
      = 1024 * u ^ (12 : ℕ) * β / Pr + 256 * u ^ (12 : ℕ) * β ^ 2 / X := by
    field_simp
    ring
  -- ⟦leg 1⟧ `49152·u¹²·μ·μ^{1/500} ≤ P`
  have he11 : (49152 : ℝ) ≤ Real.exp 11 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hh : Real.exp 11 = (Real.exp 1) ^ (11 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7182818283 : ℝ) ^ (11 : ℕ) ≤ (Real.exp 1) ^ (11 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 11
    have : (49152 : ℝ) ≤ (2.7182818283 : ℝ) ^ (11 : ℕ) := by norm_num
    rw [hh]; linarith
  have hlegA : 12 * (1024 * u ^ (12 : ℕ) * β / Pr) ≤ μ ^ (-(1 / 500) : ℝ) / 2 := by
    have hstone := capeps_Pbig hu hμ hΛ
    have h500 : (0 : ℝ) < μ ^ ((1 : ℝ) / 500) := Real.rpow_pos_of_pos hμ0 _
    have hPb : 49152 * u ^ (12 : ℕ) * μ * μ ^ ((1 : ℝ) / 500) ≤ Pr := by
      have h1 : 49152 * (u ^ (12 : ℕ) * μ * μ ^ ((1 : ℝ) / 500))
          ≤ Real.exp 11 * (u ^ (12 : ℕ) * μ * μ ^ ((1 : ℝ) / 500)) :=
        mul_le_mul_of_nonneg_right he11 (by positivity)
      linarith
    have hmul : 49152 * u ^ (12 : ℕ) * μ * (μ ^ ((1 : ℝ) / 500) * μ ^ (-(1 / 500) : ℝ))
        ≤ Pr * μ ^ (-(1 / 500) : ℝ) := by
      have := mul_le_mul_of_nonneg_right hPb hK0.le
      nlinarith [this]
    have hone : μ ^ ((1 : ℝ) / 500) * μ ^ (-(1 / 500) : ℝ) = 1 := by
      rw [← Real.rpow_add hμ0, show (1 : ℝ) / 500 + -(1 / 500) = 0 by ring, Real.rpow_zero]
    rw [hone, mul_one] at hmul
    have hβμ : 12 * (1024 * u ^ (12 : ℕ) * β) ≤ 24576 * u ^ (12 : ℕ) * μ := by nlinarith
    rw [mul_div_assoc', div_le_iff₀ hPr0]
    linarith [hmul, hβμ]
  -- ⟦leg 2⟧ `24576·u¹²·μ² ≤ X·μ^{−1/500}`
  have hlegB : 12 * (256 * u ^ (12 : ℕ) * β ^ 2 / X) ≤ μ ^ (-(1 / 500) : ℝ) / 2 := by
    have hstone := capeps_bigexp hu hμ hΛ (by norm_num : (11 : ℝ) ≤ 50)
    have h1 : 24576 * u ^ (12 : ℕ) * μ ^ 2 ≤ X * μ ^ (-(1 / 500) : ℝ) := by
      rw [capeps_Xmu hX0 hXlog hμ0]
      have hmul : 24576 * (u ^ (12 : ℕ) * μ ^ 2) ≤ Real.exp 11 * (u ^ (12 : ℕ) * μ ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith : (24576 : ℝ) ≤ Real.exp 11) (by positivity)
      linarith [hmul, hstone]
    have hβsq : β ^ 2 ≤ 4 * μ ^ 2 := by nlinarith
    have h2 : 12 * (256 * u ^ (12 : ℕ) * β ^ 2) ≤ 12288 * u ^ (12 : ℕ) * μ ^ 2 := by
      nlinarith [hp12]
    rw [mul_div_assoc', div_le_div_iff₀ hX0 (by norm_num : (0 : ℝ) < 2)]
    linarith [h1, h2]
  calc 12 * (W * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2))
      ≤ 12 * (64 * u ^ (12 : ℕ) * X * (16 * β / (X * Pr) + 4 * β ^ 2 / X ^ 2)) := by
        linarith
    _ = 12 * (1024 * u ^ (12 : ℕ) * β / Pr) + 12 * (256 * u ^ (12 : ℕ) * β ^ 2 / X) := by
        rw [hval]; ring
    _ ≤ μ ^ (-(1 / 500) : ℝ) := by linarith

end Rows

/-! ## §4 — ⟦THE SOCKET REGISTER⟧ -/

/-- **⟦THE REGISTER⟧** (`s13_capEps_register`) — the four facts every estimate of §3 reads,
off `SocketBase` and the capstone's absorbed `loglogFloor50`, at the wire's base `X_d = A+s`:
`u := log H ≥ 10²¹`, `μ := log X_d ≥ 2000`, `Λ := loglog X_d ≥ u/2`, `φ(q) ≤ u¹²`. -/
theorem s13_capEps_register {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (H : ℝ)
      ∧ (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ)
      ∧ Real.log (H : ℝ) / 2 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ))
      ∧ (q.totient : ℝ) ≤ (Real.log (H : ℝ)) ^ (12 : ℕ) := by
  have hlo : R.Hlo ≤ H := hb.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have hu21 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (H : ℝ) :=
    le_trans capeps_ten21_le_exp50 hexp50
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
  have hsharp := s13_socketBase_loglogA_sharp hfl hb
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hmono : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := Real.log_le_log hA0 hAX
  have hll : Real.log (Real.log (A : ℝ)) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    Real.log_le_log (by linarith) hmono
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hqQ : (q : ℝ) ≤ arcDen 12 H := hb.2.2.2.2.1
  have htot : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  exact ⟨hu21, by linarith, by linarith, by rw [← harcpow]; linarith⟩

/-! ## §5 — ⟦THE WITNESS⟧ and the seven fields -/

/-- ⟦THE SHARED CO-FACTOR PREFACTOR⟧ `W = 4·(2φ(q)·T_ann + 7φ(q)·2X_d/q)`, the head of
BOTH the `p²` row and the coprime-tail row of `S13CapGatePerBlock`. -/
def s13CapEpsW (q Nd : ℕ) (Tann : ℝ) : ℝ :=
  4 * (2 * (q.totient : ℝ) * Tann + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)

/-- **⟦THE `EP₂` WITNESS⟧** (`s13CapEP2`) — the MAX of the three row left-hand sides.  The
three `· ≤ EP₂` fields become `le_max`; the whole group concentrates into `EP2_gate`. -/
def s13CapEP2 (C : ℝ) (q Nd P Q : ℕ) (Tann : ℝ) : ℝ :=
  max (4160 * (q.totient : ℝ) * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293))
    (max (s13CapEpsW q Nd Tann
        * (16 * Real.logb 2 (2 * ((Nd : ℕ) : ℝ)) / (((Nd : ℕ) : ℝ) * (P : ℝ))
            + endMass Nd))
      (s13CapEpsW q Nd Tann * s13MtailBand C Nd P Q))

/-- ⟦`phi_row`⟧ at the witness — `le_max`. -/
theorem s13CapEps_phi_row (C : ℝ) (q Nd P Q : ℕ) (Tann : ℝ) :
    4160 * (q.totient : ℝ) * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293)
      ≤ s13CapEP2 C q Nd P Q Tann := le_max_left _ _

/-- ⟦`p2_row`⟧ at the witness — `le_max`. -/
theorem s13CapEps_p2_row (C : ℝ) (q Nd P Q : ℕ) (Tann : ℝ) :
    4 * (2 * (q.totient : ℝ) * Tann
        + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
      * (16 * Real.logb 2 (2 * ((Nd : ℕ) : ℝ)) / (((Nd : ℕ) : ℝ) * (P : ℝ)) + endMass Nd)
    ≤ s13CapEP2 C q Nd P Q Tann := le_max_of_le_right (le_max_left _ _)

/-- ⟦`tail_row`⟧ at the witness — `le_max`. -/
theorem s13CapEps_tail_row (C : ℝ) (q Nd P Q : ℕ) (Tann : ℝ) :
    4 * (2 * (q.totient : ℝ) * Tann
        + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q) * s13MtailBand C Nd P Q
    ≤ s13CapEP2 C q Nd P Q Tann := le_max_of_le_right (le_max_right _ _)

/-- ⟦`epsr_nonneg`⟧ at the pin, in the monotone form. -/
theorem s13CapEps_epsr_nonneg {εr : ℝ} (hεr : theta293 - 1 / 500 ≤ εr) : 0 ≤ εr := by
  have := s13_theta293_margin_lo; linarith

/-- ⟦`abs8640`⟧ at the socket, in the monotone form — `s13_abs8640_at_shift` plus the
exponent's own monotonicity at `log X_d ≥ 1`. -/
theorem s13CapEps_abs8640 {R : ChowlaRegime} {M H L q j A s : ℕ} {εr : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hεr : theta293 - 1 / 500 ≤ εr) :
    (8640 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ εr := by
  obtain ⟨-, hμ, -, -⟩ := s13_capEps_register hfl hb
  exact le_trans (s13_abs8640_at_shift hfl hb)
    (Real.rpow_le_rpow_of_exponent_le (by linarith) hεr)

/-- ⟦`q_arcDen`⟧ — `SocketBase`'s own modulus field, verbatim. -/
theorem s13CapEps_q_arcDen {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBase R M H L q j A s) : (q : ℝ) ≤ arcDen 12 H := hb.2.2.2.2.1

/-- **⟦`EP2_gate` AT THE WITNESS⟧** (`s13CapEps_EP2_gate`) — the whole `EP₂` group, in one
inequality.  Each of the three rows spends at most a twelfth of `(log X_d)^{−1/500}`; §3
proves the three against the x-scale floor `Λ ≥ ½·log H ≥ 2.59·10²¹`. -/
theorem s13CapEps_EP2_gate {R : ChowlaRegime} {M H L q j A s P Q : ℕ} {C Tann εr : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hεr : theta293 - 1 / 500 ≤ εr) (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hT0 : 0 ≤ Tann) (hTX : Tann ≤ (((A + s : ℕ)) : ℝ))
    (hP83 : P83 (((A + s : ℕ)) : ℝ) theta293 ≤ (P : ℝ))
    (hgrade : Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log (((A + s : ℕ)) : ℝ))
              * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293))) :
    12 * s13CapEP2 C q (A + s) P Q Tann
      ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + εr) := by
  obtain ⟨hu, hμ, hΛ, hφ⟩ := s13_capEps_register hfl hb
  set u : ℝ := Real.log (H : ℝ) with hudef
  set X : ℝ := (((A + s : ℕ)) : ℝ) with hXdef
  set μ : ℝ := Real.log X with hμdef
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hX1 : (1 : ℝ) < X := by
    rcases lt_or_ge 1 X with hc | hc
    · exact hc
    · have hnp : Real.log X ≤ 0 := Real.log_nonpos (by positivity) hc
      rw [← hμdef] at hnp
      linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hp12 : (0 : ℝ) < u ^ (12 : ℕ) := pow_pos hu0 12
  have hu121 : (1 : ℝ) ≤ u ^ (12 : ℕ) := one_le_pow₀ (by linarith)
  have hφ0 : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  have hq : 0 < q := hb.2.2.2.1
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have htot : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  -- ⟦the shared prefactor⟧ `W ≤ 64·u¹²·X`
  have hWval : s13CapEpsW q (A + s) Tann
      = 4 * (2 * (q.totient : ℝ) * Tann + 7 * (q.totient : ℝ) * (2 * X) / q) := by
    simp only [s13CapEpsW, hXdef]
    push_cast
    ring
  have hW0 : 0 ≤ s13CapEpsW q (A + s) Tann := by
    rw [hWval]
    have h1 : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * Tann := by positivity
    have h2 : (0 : ℝ) ≤ 7 * (q.totient : ℝ) * (2 * X) / q := by positivity
    linarith
  have hW : s13CapEpsW q (A + s) Tann ≤ 64 * u ^ (12 : ℕ) * X := by
    rw [hWval]
    have h1 : 2 * (q.totient : ℝ) * Tann ≤ 2 * u ^ (12 : ℕ) * X := by nlinarith
    have hfrac : 7 * (q.totient : ℝ) * (2 * X) / q ≤ 14 * X := by
      rw [div_le_iff₀ hqR]
      nlinarith
    nlinarith
  -- ⟦the three rows⟧
  have hrow1 : 12 * (4160 * (q.totient : ℝ) * μ ^ (-theta293)) ≤ μ ^ (-(1 / 500) : ℝ) :=
    capeps_row_phi hu hμ hΛ hφ0 hφ
  have hrow3 : 12 * (s13CapEpsW q (A + s) Tann * s13MtailBand C (A + s) P Q)
      ≤ μ ^ (-(1 / 500) : ℝ) := by
    rw [s13MtailBand]
    exact capeps_row_tail hu hμ hΛ hX0 rfl hW0 hW hC0 hC hgrade
  have hrow2 : 12 * (s13CapEpsW q (A + s) Tann
      * (16 * Real.logb 2 (2 * X) / (X * (P : ℝ)) + endMass (A + s)))
      ≤ μ ^ (-(1 / 500) : ℝ) := by
    have hend : endMass (A + s) = 4 * (Real.logb 2 (2 * X)) ^ 2 / X ^ 2 := by
      rw [endMass]
    have hβ0 : (0 : ℝ) ≤ Real.logb 2 (2 * X) :=
      Real.logb_nonneg (by norm_num) (by linarith)
    have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hβ : Real.logb 2 (2 * X) ≤ 2 * μ := by
      have hlog : Real.log (2 * X) = Real.log 2 + μ := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hX0)]
      rw [Real.logb, hlog, div_le_iff₀ (by linarith)]
      nlinarith
    have hPr : Real.exp (μ ^ (1 - theta293)) ≤ (P : ℝ) := by
      have : P83 X theta293 = Real.exp (μ ^ (1 - theta293)) := by rw [P83]
      rw [← this]; exact hP83
    rw [hend]
    exact capeps_row_p2 hu hμ hΛ hX0 rfl hW0 hW hβ0 hβ hPr
  -- ⟦the max⟧
  have hmax : s13CapEP2 C q (A + s) P Q Tann ≤ μ ^ (-(1 / 500) : ℝ) / 12 := by
    rw [s13CapEP2]
    refine max_le (by linarith) (max_le ?_ (by linarith))
    have := hrow2
    linarith
  have hmono : μ ^ (-(1 / 500) : ℝ) ≤ μ ^ (-theta293 + εr) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  linarith

/-- **⟦THE `εr` GROUP, BUNDLED⟧** (`s13CapEps_all`) — the seven fields of
`S13FramesB.S13CapGatePerBlock` in STRUCTURE ORDER (`epsr_nonneg`, `abs8640`, `EP2_gate`,
`q_arcDen`, `phi_row`, `p2_row`, `tail_row`), at `Hreg := H`, `Nd := A + s`,
`EP₂ := s13CapEP2 C q (A+s) P Q Tann`.  The hypothesis register is the file header's. -/
theorem s13CapEps_all {R : ChowlaRegime} {M H L q j A s P Q : ℕ} {C Tann εr : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hεr : theta293 - 1 / 500 ≤ εr) (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hT0 : 0 ≤ Tann) (hTX : Tann ≤ (((A + s : ℕ)) : ℝ))
    (hP83 : P83 (((A + s : ℕ)) : ℝ) theta293 ≤ (P : ℝ))
    (hgrade : Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log (((A + s : ℕ)) : ℝ))
              * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293))) :
    0 ≤ εr
      ∧ (8640 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ εr
      ∧ 12 * s13CapEP2 C q (A + s) P Q Tann
          ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + εr)
      ∧ (q : ℝ) ≤ arcDen 12 H
      ∧ 4160 * (q.totient : ℝ) * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
          ≤ s13CapEP2 C q (A + s) P Q Tann
      ∧ 4 * (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * (A + s) : ℕ)) : ℝ) / q)
          * (16 * Real.logb 2 (2 * (((A + s : ℕ)) : ℝ))
              / ((((A + s : ℕ)) : ℝ) * (P : ℝ)) + endMass (A + s))
          ≤ s13CapEP2 C q (A + s) P Q Tann
      ∧ 4 * (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * (A + s) : ℕ)) : ℝ) / q)
          * s13MtailBand C (A + s) P Q
          ≤ s13CapEP2 C q (A + s) P Q Tann :=
  ⟨s13CapEps_epsr_nonneg hεr, s13CapEps_abs8640 hfl hb hεr,
    s13CapEps_EP2_gate hfl hb hεr hC0 hC hT0 hTX hP83 hgrade,
    s13CapEps_q_arcDen hb, s13CapEps_phi_row C q (A + s) P Q Tann,
    s13CapEps_p2_row C q (A + s) P Q Tann, s13CapEps_tail_row C q (A + s) P Q Tann⟩

/-! ## §5b — ⟦THE GRID PINS⟧: `hP83` and `hgrade` discharged at `⌈P₈₃⌉₊`, `⌊Q₈₃⌋₊`

`M4RowSupply` §4's own choice of band endpoints.  Nothing here chooses the grid — it shows
that IF the grid wave pins `P := ⌈P₈₃ X_d θ₂₉₃⌉₊` and `Q := ⌊Q₈₃ X_d⌋₊` (the corpus's
`m4_tail_grade_rounded` pins), then `s13CapEps_all`'s last two hypotheses are FREE. -/

/-- ⟦THE PINS' TWO SIDE FACTS⟧ `4 ≤ log P₈₃` and `4 ≤ log Q₈₃` at the socket base —
`m4_tail_grade_rounded`'s own hypotheses.  Both are astronomically slack: `log P₈₃ =
μ^{1−θ₂₉₃} ≥ e^{Λ/2}` and `log Q₈₃ = μ/Λ ≥ Λ/4`. -/
theorem s13CapEps_pin_floors {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    (4 : ℝ) ≤ Real.log (P83 (((A + s : ℕ)) : ℝ) theta293)
      ∧ (4 : ℝ) ≤ Real.log (Q83 (((A + s : ℕ)) : ℝ)) := by
  obtain ⟨hu, hμ, hΛ, -⟩ := s13_capEps_register hfl hb
  set X : ℝ := (((A + s : ℕ)) : ℝ) with hXdef
  set μ : ℝ := Real.log X with hμdef
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛbig : (5 : ℝ) * 10 ^ (20 : ℕ) ≤ Real.log μ := by
    have : (10 : ℝ) ^ (21 : ℕ) = 2 * (5 * 10 ^ (20 : ℕ)) := by norm_num
    linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by linarith
  have hθ32 : theta293 < 1 / 32 := theta293_lt_one_div_32
  have hθ0 : (0 : ℝ) < theta293 := theta293_pos
  constructor
  · rw [P83, Real.log_exp]
    have hrw : μ ^ (1 - theta293) = Real.exp ((1 - theta293) * Real.log μ) := by
      rw [Real.rpow_def_of_pos hμ0]; ring_nf
    have hhalf : Real.exp (Real.log μ / 2) ≤ μ ^ (1 - theta293) := by
      rw [hrw]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hlin : Real.log μ / 2 + 1 ≤ Real.exp (Real.log μ / 2) :=
      Real.add_one_le_exp _
    linarith
  · rw [Q83, Real.log_exp, le_div_iff₀ hΛ0]
    have hsq : (Real.log μ) ^ 2 / 4 ≤ μ := by
      have h := capeps_sq_le_exp hΛ0.le
      rwa [Real.exp_log hμ0] at h
    nlinarith [hsq, hΛbig, hΛ0]

/-- ⟦THE PINS SUPPLY⟧ `s13CapEps_all`'s `hP83` and `hgrade`, at the corpus's own ℕ-band
`P = ⌈P₈₃⌉₊`, `Q = ⌊Q₈₃⌋₊` (`M4RowSupply.m4_tail_grade_rounded`). -/
theorem s13CapEps_pins_supply {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    P83 (((A + s : ℕ)) : ℝ) theta293
        ≤ ((⌈P83 (((A + s : ℕ)) : ℝ) theta293⌉₊ : ℕ) : ℝ)
      ∧ Real.log ((⌈P83 (((A + s : ℕ)) : ℝ) theta293⌉₊ : ℕ) : ℝ)
            / Real.log ((⌊Q83 (((A + s : ℕ)) : ℝ)⌋₊ : ℕ) : ℝ)
          ≤ 2 * (Real.log (Real.log (((A + s : ℕ)) : ℝ))
                  * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)) := by
  obtain ⟨hu, hμ, hΛ, -⟩ := s13_capEps_register hfl hb
  obtain ⟨hP4, hQ4⟩ := s13CapEps_pin_floors hfl hb
  have hpos : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  refine ⟨Nat.le_ceil _, m4_tail_grade_rounded (by linarith) (by linarith) hP4 hQ4⟩

