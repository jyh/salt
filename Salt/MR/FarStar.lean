/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FarClose
import Salt.MR.SeamGate

/-!
# FAR-STAR — the far arm re-pinned at `T* = y·k^{1/log y}` (`FarStar`)

`FarClose`'s arithmetic verdict: at the truncation height `T = L⁴` the far socket

  `(1/π)·η²·(Ffar·Kfar) ≤ Cfar·k·(log X)^{−1/(32e)}`,  `Cfar` ABSOLUTE

is **FALSE** — the low leg's `ℓ¹` window mass carries `(k/y)^{η−1/L} = e^{L/(4 log L)−2+o(1)}`,
superpolynomial in `L`.  `⟦V3e⟧` of `docs/exploration/hsup-design.md` rules repair (i): raise
the height to

  `T* := y·k^{1/log y} = L⁴·k^{1/(4 log L)} = L⁴·e^{L/(4 log L)}`  (`Tstar`, §1).

At that height the `k`-power of `T*` cancels the `ℓ¹` excess EXACTLY: `k^{η} = k^{1/log y}`,
and the residual `k^{−1/L}·y^{−η} = e^{−2}` is a constant.  This file re-runs the whole
`FarClose` chain at `T*`, with the socket DISCHARGED.

## What lands here

* **FS-1 `Tstar`** — the height, with `Tstar_pos`, `Tstar_ge` (`L⁴ ≤ T*`), `Tstar_eq_pin`
  (`T* = y·k^η` at the pin), and **FS-1m `Tstar_mono`**: `k ↦ T*(k, log k)` is monotone on
  `k ≥ e^e`.  The gate is honest and sharp in shape: the exponent `log k/(4 log log k)` is
  increasing exactly where `log log k ≥ 1`, i.e. `k ≥ e^e ≈ 15.2` — far below the corpus
  gate `k ≥ e^64`.  (Proof without derivatives: `x/log x` is increasing for `x ≥ e` because
  `log M − log L ≤ (M−L)/L` and `(M−L)(log L − 1) ≥ 0`.)
* **FS-2 `farKfarStar` / `far_kernel_bound_star`** — `FarClose.far_kernel_bound_T` (the stone
  already stated at a FREE `T`) instantiated at `T := T*`.
* **FS-3 `far_kfar_star_le` / `hfar_star`** — THE SOCKET, now TRUE, with the constant
  `farCStar` exhibited and ABSOLUTE.
* **FS-4 `seamGateRstar` / `seam_gate_star_of_nonempty` / `seam_gate_star_package`** —
  `SeamGate`'s route (b) at the new height: the gate radius `T_ann + seamRad X + T*(2X) + 1`,
  with FS-1m's monotonicity in place of `log_pow_four_le_of_le_two_mul`.
* **FS-5 `rhs_grade_at_scale_closed_star` / `hRHS_socket_star` / `ball_sup_closed_star`** —
  the closed chain: `FarClose`'s F-4 / crown re-run at `T*`, with `hfar` and `hKfar`
  DISCHARGED (no arithmetic socket left) and `hgate` discharged from nonemptiness.

## THE MARGIN, as proven (the honest exponent page)

With `y = L⁴`, `η = 1/log y = 1/(4 log L)`, `h = k/√L`, `L = log k ≥ 64`:

  `Kfar(T*) ≤ S(c₀−η)·S(c₀)·(k+h)^{c₀}·(4(√L+1)/T*)`      (FS-2)
  `S(c₀−η)·S(c₀) ≤ (log 4+4)²·[(k/y)^{η−1/L}·y^{−1/L}]·(1+2/(η−1/L))·(2+L)`   (F-2b)

and the three numerals that make the `L`-page:

  `η − 1/L ≥ 1/(8 log L)`  (from `8 log L ≤ L`, `L ≥ 64`)  ⟹ `1 + 2/(η−1/L) ≤ 17 log L`;
  `2 + L ≤ 2L`;  `(k+h)^{c₀} ≤ 9k`;  `4(√L+1) ≤ 8√L`,

so `Kfar(T*) ≤ 2448·(log 4+4)²·k·(log L)·√L/L³`, whence

  `(1/π)·η²·(Ffar·Kfar(T*)) ≤ (153/π)·C_S·C_F·e^{24/e}·(log 4+4)²·k·√L/((log L)·L²)`,

which against the crown's currency `(log X)^{−1/(32e)} ≥ 1/(2L)` (valid for `X ≤ 2k`) leaves
the margin `√L·2L/((log L)·L²) = 2/(√L·log L) ≤ 1` — i.e. the ratio is
`O(L^{−1/2}/log L)`, DECREASING, with `Cfar := farCStar` absolute.  (`FarClose`'s report
prices the same page as `L^{−3/2}/log L` against `k·(log X)^{−1/(32e)}` with `log X ≍ L`;
the extra `L` here is the honest price of the crude `log X ≤ 2L` step, which is all the
crown's `⌊X⌋₊ ≤ k` supplies.  Both are decreasing; the socket holds at every `L ≥ 64`.)

**No statement anywhere is changed** (Iron rule 1); no existing file is touched.  The `§0`
privates are `FarClose`'s own, re-derived verbatim (they are `private` there), plus the new
`8 log L ≤ L` and the `x/log x` monotonicity.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## §0 — the pin's arithmetic, re-derived

`FarClose`'s `four_log_le_selfF` / `four_log_lt_selfF` / `pin_basic64F` and `GradeConst`'s
`pin_rpow_scale` are `private`; re-derived verbatim, plus the new `8·log L ≤ L` (which is
what the `ℓ¹` shift `η − 1/L ≥ 1/(8 log L)` needs) and the `x/log x` monotonicity of FS-1m. -/

/-- `4·log L ≤ L` for `L ≥ 64`.  Re-derivation of `FarClose`'s private `four_log_le_selfF`. -/
private lemma four_log_le_selfT {L : ℝ} (h : 64 ≤ L) : 4 * Real.log L ≤ L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt h
  have hlog : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 := Real.log_le_sub_one_of_pos hs0
  have hhalf : Real.log (Real.sqrt L) = Real.log L / 2 := Real.log_sqrt hL0.le
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  nlinarith

/-- `4·log L < L` for `L ≥ 64` — the STRICT form (`FarClose`'s `four_log_lt_selfF`). -/
private lemma four_log_lt_selfT {L : ℝ} (h : 64 ≤ L) : 4 * Real.log L < L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt h
  have hlog : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 := Real.log_le_sub_one_of_pos hs0
  have hhalf : Real.log (Real.sqrt L) = Real.log L / 2 := Real.log_sqrt hL0.le
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  nlinarith

/-- **`8·log L ≤ L` for `L ≥ 64`** — the sharper self-bound the `ℓ¹` shift needs.  The
`√L − 1` majorant of `four_log_le_selfT` is too lossy here (it needs `√L ≥ 14.9`); the
`log s ≤ s/e` majorant is not (`16/e ≤ 8 ≤ √L`). -/
private lemma eight_log_le_selfT {L : ℝ} (h : 64 ≤ L) : 8 * Real.log L ≤ L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt h
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hlog : Real.log (Real.sqrt L) ≤ Real.sqrt L / Real.exp 1 := by
    have h1 : Real.log (Real.sqrt L / Real.exp 1) ≤ Real.sqrt L / Real.exp 1 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hs0.ne' (Real.exp_ne_zero 1), Real.log_exp] at h1
    linarith
  have hhalf : Real.log (Real.sqrt L) = Real.log L / 2 := Real.log_sqrt hL0.le
  have hdiv : Real.sqrt L / Real.exp 1 ≤ Real.sqrt L / 2 :=
    div_le_div_of_nonneg_left hs0.le (by norm_num) he2
  rw [hhalf] at hlog
  nlinarith

/-- The pin's elementary arithmetic at the `e^{64}` gate (`FarClose`'s `pin_basic64F`). -/
private lemma pin_basic64T {k L y η : ℝ} (hk : Real.exp 64 ≤ k) (hL : L = Real.log k)
    (hy : y = L ^ 4) (hη : η = 1 / Real.log y) :
    0 < k ∧ 64 ≤ L ∧ (131072 : ℝ) ≤ y ∧ Real.log y = 4 * Real.log L ∧ 0 < η ∧ η ≤ 1 / 8
      ∧ 1 / L < η ∧ L ^ 4 ≤ k := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 64) hk
  have hL64 : (64 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hy131072 : (131072 : ℝ) ≤ y := by
    rw [hy]
    have h4 : (64 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL64 4
    norm_num at h4
    linarith
  have hlogy : Real.log y = 4 * Real.log L := by rw [hy, Real.log_pow]; norm_num
  have he2 : Real.exp 2 ≤ 64 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hlogL2 : (2 : ℝ) ≤ Real.log L := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) (by linarith)
  refine ⟨hk0, hL64, hy131072, hlogy, by rw [hη, hlogy]; positivity, ?_, ?_, ?_⟩
  · rw [hη, hlogy, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 8)]
    linarith
  · rw [hη, hlogy, div_lt_div_iff₀ hL0 (by linarith)]
    linarith [four_log_lt_selfT hL64]
  · have h1 : Real.log (L ^ 4) ≤ Real.log k := by
      rw [Real.log_pow, ← hL]; push_cast; linarith [four_log_le_selfT hL64]
    have h2 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by positivity), Real.exp_log hk0] at h2

/-- The pin's scale factor `(k+h)^{c₀} ≤ 9·k` (`GradeConst`'s private `pin_rpow_scale`). -/
private lemma pin_rpow_scaleT {k h L c₀ : ℝ} (hk : Real.exp 64 ≤ k) (hL : L = Real.log k)
    (hh : h = k / Real.sqrt L) (hc₀ : c₀ = 1 + 1 / L) :
    (k + h) ^ c₀ ≤ 9 * k := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 64) hk
  have hL64 : (64 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]; exact Real.sqrt_le_sqrt hL64
  have hh0 : (0 : ℝ) < h := by rw [hh]; positivity
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hk65 : (65 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (64 : ℝ)]
  have hk1 : (1 : ℝ) ≤ k := by linarith
  have hhk : h ≤ k / 8 := by
    rw [hh, div_le_div_iff₀ hs0 (by norm_num)]; nlinarith
  have hkh98 : k + h ≤ 9 / 8 * k := by linarith
  have hlogkh : Real.log (k + h) ≤ 2 * L := by
    have hsq : k + h ≤ k * k := by nlinarith
    have h1 : Real.log (k + h) ≤ Real.log (k * k) := Real.log_le_log hkh0 hsq
    rw [Real.log_mul hk0.ne' hk0.ne', ← hL] at h1
    linarith
  have he2 : Real.exp 2 ≤ 8 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hfrac : (k + h) ^ (1 / L : ℝ) ≤ 8 := by
    rw [Real.rpow_def_of_pos hkh0]
    have hexp : Real.log (k + h) * (1 / L) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hL0]; linarith
    calc Real.exp (Real.log (k + h) * (1 / L)) ≤ Real.exp 2 := Real.exp_le_exp.mpr hexp
      _ ≤ 8 := he2
  have hsplit : (k + h) ^ c₀ = (k + h) * (k + h) ^ (1 / L : ℝ) := by
    rw [hc₀, Real.rpow_add hkh0, Real.rpow_one]
  rw [hsplit]
  calc (k + h) * (k + h) ^ (1 / L : ℝ) ≤ (9 / 8 * k) * 8 :=
        mul_le_mul hkh98 hfrac (Real.rpow_nonneg hkh0.le _) (by linarith)
    _ = 9 * k := by ring

/-- **`x/log x` is increasing on `x ≥ e`** — FS-1m's analytic content, derivative-free:
`log M − log L = log(M/L) ≤ M/L − 1`, so `L·log M ≤ L·log L + (M−L) ≤ M·log L` exactly when
`(M−L)(log L − 1) ≥ 0`.  The gate `e ≤ L` is SHARP for this shape. -/
private lemma div_log_monoT {L M : ℝ} (hL : Real.exp 1 ≤ L) (hLM : L ≤ M) :
    L / Real.log L ≤ M / Real.log M := by
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (Real.exp_pos 1) hL
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le hL0 hLM
  have hlogL : (1 : ℝ) ≤ Real.log L := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hL
  have hlogM : (1 : ℝ) ≤ Real.log M := le_trans hlogL (Real.log_le_log hL0 hLM)
  have hstep : Real.log M - Real.log L ≤ (M - L) / L := by
    have h1 : Real.log (M / L) ≤ M / L - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hM0.ne' hL0.ne'] at h1
    have h2 : M / L - 1 = (M - L) / L := by field_simp
    linarith [h1, h2.le, h2.ge]
  have hmul : L * Real.log M ≤ M * Real.log L := by
    have h3 : L * (Real.log M - Real.log L) ≤ M - L := by
      have h4 : L * ((M - L) / L) = M - L := by field_simp
      calc L * (Real.log M - Real.log L) ≤ L * ((M - L) / L) :=
            mul_le_mul_of_nonneg_left hstep hL0.le
        _ = M - L := h4
    nlinarith
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  exact hmul

/-! ## §1 — FS-1: the truncation height `T*` -/

/-- **FS-1 — the re-pinned truncation height.**  `T* := y·k^{1/log y}` at the corpus pin
`y = L⁴` (so `log y = 4 log L`):

  `Tstar k L = L⁴·k^{1/(4 log L)}`,

which at `L = log k` is `L⁴·e^{L/(4 log L)} = X^{1/(4 log log X)}·(log X)⁴` — SUB-POLYNOMIAL
in the scale, which is what keeps `⟦V3e⟧`'s gate radius `R ≪ X` in the `polyT` regime. -/
def Tstar (k L : ℝ) : ℝ := L ^ 4 * k ^ (1 / (4 * Real.log L))

lemma Tstar_pos {k L : ℝ} (hk : 0 < k) (hL : 0 < L) : 0 < Tstar k L := by
  unfold Tstar
  exact mul_pos (by positivity) (Real.rpow_pos_of_pos hk _)

/-- `T* = y·k^η` at the pin — the shape `⟦V3e⟧` names (`y·k^{1/log y}`). -/
lemma Tstar_eq_pin {k L y η : ℝ} (hy : y = L ^ 4) (hη : η = 1 / Real.log y) :
    Tstar k L = y * k ^ η := by
  have hlogy : Real.log y = 4 * Real.log L := by rw [hy, Real.log_pow]; norm_num
  rw [hy, hη, hlogy]
  rfl

/-- `L⁴ ≤ T*`: the new height dominates the old one, so every `L⁴`-shaped bound survives. -/
lemma Tstar_ge {k L : ℝ} (hk : 1 ≤ k) (hL : 1 ≤ L) : L ^ 4 ≤ Tstar k L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL
  have hexp : (0 : ℝ) ≤ 1 / (4 * Real.log L) := by positivity
  have h1 : (1 : ℝ) ≤ k ^ (1 / (4 * Real.log L)) := Real.one_le_rpow hk hexp
  have h4 : (0 : ℝ) ≤ L ^ 4 := by positivity
  calc L ^ 4 = L ^ 4 * 1 := by ring
    _ ≤ L ^ 4 * k ^ (1 / (4 * Real.log L)) := by
        exact mul_le_mul_of_nonneg_left h1 h4
    _ = Tstar k L := rfl

/-- **FS-1m — the per-`k` monotonicity (`Tstar_mono`).**  `k ↦ T*(k, log k)` is increasing on
`k ≥ e^e`.  Both factors climb: `(log k)⁴` trivially, and the exponent
`log k/(4 log log k)` by `div_log_monoT` — whose gate `log k ≥ e` is exactly where the
derivative `(log log x − 1)/(4x(log log x)²)` turns nonnegative.  `e^e ≈ 15.15`, so the corpus
gate `k ≥ e^64` clears it by a wide margin; this is what `seamGateRstar` needs. -/
theorem Tstar_mono {k K : ℝ} (hk : Real.exp (Real.exp 1) ≤ k) (hkK : k ≤ K) :
    Tstar k (Real.log k) ≤ Tstar K (Real.log K) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos _) hk
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le hk0 hkK
  have hLk : Real.exp 1 ≤ Real.log k := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hk
  have hLkK : Real.log k ≤ Real.log K := Real.log_le_log hk0 hkK
  have hLk0 : (0 : ℝ) < Real.log k := lt_of_lt_of_le (Real.exp_pos 1) hLk
  have hLK0 : (0 : ℝ) < Real.log K := lt_of_lt_of_le hLk0 hLkK
  have hllk : (1 : ℝ) ≤ Real.log (Real.log k) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hLk
  have hllK : (1 : ℝ) ≤ Real.log (Real.log K) :=
    le_trans hllk (Real.log_le_log hLk0 hLkK)
  have hllk0 : Real.log (Real.log k) ≠ 0 := by linarith
  have hllK0 : Real.log (Real.log K) ≠ 0 := by linarith
  have h1 : Real.log k ^ 4 ≤ Real.log K ^ 4 := pow_le_pow_left₀ hLk0.le hLkK 4
  have hdl := div_log_monoT hLk hLkK
  have h2 : k ^ (1 / (4 * Real.log (Real.log k))) ≤ K ^ (1 / (4 * Real.log (Real.log K))) := by
    rw [Real.rpow_def_of_pos hk0, Real.rpow_def_of_pos hK0]
    refine Real.exp_le_exp.mpr ?_
    have e1 : Real.log k * (1 / (4 * Real.log (Real.log k)))
        = Real.log k / Real.log (Real.log k) / 4 := by field_simp
    have e2 : Real.log K * (1 / (4 * Real.log (Real.log K)))
        = Real.log K / Real.log (Real.log K) / 4 := by field_simp
    rw [e1, e2]
    linarith
  unfold Tstar
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hk0.le _) (by positivity)

/-! ## §2 — FS-2: the far kernel binder at `T*` -/

/-- **FS-2 — the far kernel value at `T*` (`farKfarStar`).**  `FarClose.far_kernel_bound_T`'s
right-hand side at the pin (`y = L⁴`, `c₀ = 1+1/L`, `η = 1/log y`, `h = k/√L`) and at the
truncation height `T := Tstar k L`.  This is the `Kfar` the closed chain is run with: the two
`ℓ¹` window masses, the amplitude `(k+h)^{c₀}`, and the Poisson tail `4(√L+1)/T*`. -/
def farKfarStar (d : ℕ → ℂ) (k L : ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioo ⌊L ^ 4⌋₊ ⌈k / L ^ 4⌉₊,
      ‖lambdaLin (restrictAbove (L ^ 4) d) n‖ / (n : ℝ) ^ (1 + 1 / L - 1 / Real.log (L ^ 4)))
    * (∑ n ∈ Finset.Ioo ⌊L ^ 4⌋₊ ⌈k / L ^ 4⌉₊,
        ‖lambdaLin (restrictAbove (L ^ 4) d) n‖ / (n : ℝ) ^ (1 + 1 / L))
    * ((k + k / Real.sqrt L) ^ (1 + 1 / L) * (4 * (Real.sqrt L + 1) / Tstar k L))

/-- **FS-2 — the `hKfar` binder at `T*` (`far_kernel_bound_star`).**
`FarClose.far_kernel_bound_T` — the free-`T` stone — instantiated at `T := Tstar k L`.  No new
analysis: the only input is `0 < T*`. -/
theorem far_kernel_bound_star {d : ℕ → ℂ} {t₀' k L c₀ y η : ℝ}
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) :
    ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar d k (k / Real.sqrt L) y c₀ t₀' α β (Tstar k L) ≤ farKfarStar d k L := by
  obtain ⟨hk0, hL64, -, -, -, -, -, -⟩ := pin_basic64T hk hL hy hη
  have hT : 0 < Tstar k L := Tstar_pos hk0 (by linarith)
  intro α hα β hβ
  have hmain := far_kernel_bound_T (d := d) (t₀' := t₀') hk hL hy hη hc₀ hT α hα β hβ
  subst hy
  subst hη
  subst hc₀
  exact hmain

/-! ## §3 — FS-3: THE SOCKET, now true

The `L`-page of `⟦V3e⟧`.  Everything here is the composition of `FarClose`'s own numerals with
ONE new cancellation: `T*`'s `k`-power is exactly the low leg's `ℓ¹` excess, and the residual
is the constant `k^{−1/L}·y^{−η} = e^{−1}·e^{−1}`. -/

/-- **The exact cancellation.**  `(k/y)^{η−1/L}·y^{−1/L} = k^{η}/e²` at `L = log k`,
`y = L⁴`, `η = 1/log y`: the `ℓ¹` excess IS a `k`-power `k^{η} = k^{1/log y}`, and the two
residual factors `k^{−1/L}` and `y^{−η}` are each exactly `e^{−1}` (the pin's own two
`X^{1/log X} = e` identities).  This is why `T* := y·k^{1/log y}` is the right height and not
merely a large one. -/
private lemma far_mass_cancel {k L : ℝ} (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) :
    (k / L ^ 4) ^ (1 / (4 * Real.log L) - 1 / L) * (L ^ 4) ^ (-(1 / L))
      = k ^ (1 / (4 * Real.log L)) / (Real.exp 1 * Real.exp 1) := by
  obtain ⟨hk0, hL64, -, -, -, -, -, -⟩ := pin_basic64T hk hL rfl rfl
  have hL0 : (0 : ℝ) < L := by linarith
  have hy0 : (0 : ℝ) < L ^ 4 := by positivity
  have he2 : Real.exp 2 ≤ 64 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hlogL2 : (2 : ℝ) ≤ Real.log L := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) (by linarith)
  have hlogL0 : Real.log L ≠ 0 := by linarith
  rw [Real.rpow_def_of_pos (div_pos hk0 hy0), Real.rpow_def_of_pos hy0,
    Real.rpow_def_of_pos hk0, ← Real.exp_add,
    show Real.exp 1 * Real.exp 1 = Real.exp 2 from by rw [← Real.exp_add]; norm_num,
    ← Real.exp_sub, Real.log_div hk0.ne' hy0.ne', Real.log_pow, ← hL]
  congr 1
  push_cast
  field_simp
  ring

/-- **FS-3a — the `Kfar` numeral at `T*` (`far_kfar_star_le`).**

  `Kfar(T*) ≤ 2448·(log 4 + 4)²·k·(log L)·√L / L³`.

The four numerals: `1 + 2/(η−1/L) ≤ 17 log L` (from `η − 1/L ≥ 1/(8 log L)`, i.e. from
`8 log L ≤ L`), `2 + L ≤ 2L`, `(k+h)^{c₀} ≤ 9k`, `4(√L+1) ≤ 8√L`; and the cancellation
`far_mass_cancel`, which turns `[(k/y)^{η−1/L}·y^{−1/L}]/T*` into `1/(e²·L⁴)`. -/
theorem far_kfar_star_le {d : ℕ → ℂ} (hd : ∀ p, p.Prime → ‖d p‖ ≤ 1) {k L : ℝ}
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) :
    farKfarStar d k L
      ≤ 2448 * (Real.log 4 + 4) ^ 2 * (k * Real.log L * Real.sqrt L / L ^ 3) := by
  obtain ⟨hk0, hL64, -, hlogy, -, -, -, -⟩ := pin_basic64T hk hL rfl rfl
  have hL0 : (0 : ℝ) < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]; exact Real.sqrt_le_sqrt hL64
  have he2 : Real.exp 2 ≤ 64 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hlogL2 : (2 : ℝ) ≤ Real.log L := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) (by linarith)
  have hlogL0 : (0 : ℝ) < Real.log L := by linarith
  have hkη0 : (0 : ℝ) < k ^ (1 / (4 * Real.log L)) := Real.rpow_pos_of_pos hk0 _
  have hT0 : (0 : ℝ) < Tstar k L := Tstar_pos hk0 hL0
  -- the mass product, with `log (L⁴)` normalised to `4 log L`
  have hMass := far_window_mass_le hd hk hL rfl rfl rfl
  rw [hlogy] at hMass
  -- the `ℓ¹` shift is at least `1/(8 log L)`
  have hgap : 1 / (8 * Real.log L) ≤ 1 / (4 * Real.log L) - 1 / L := by
    have h8 := eight_log_le_selfT hL64
    have h1 : 1 / L ≤ 1 / (8 * Real.log L) :=
      one_div_le_one_div_of_le (by positivity) h8
    have h2 : 1 / (4 * Real.log L) = 2 * (1 / (8 * Real.log L)) := by field_simp; ring
    linarith
  have hgap0 : (0 : ℝ) < 1 / (4 * Real.log L) - 1 / L :=
    lt_of_lt_of_le (by positivity) hgap
  -- the two `min` numerals
  have hM1 : min (Real.log (⌈k / L ^ 4⌉₊ : ℝ) + (Real.log 4 + 4))
      (1 + 2 / (1 / (4 * Real.log L) - 1 / L)) ≤ 17 * Real.log L := by
    refine le_trans (min_le_right _ _) ?_
    have h2 : 2 / (1 / (4 * Real.log L) - 1 / L) ≤ 2 / (1 / (8 * Real.log L)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hgap
    have h3 : 2 / (1 / (8 * Real.log L)) = 16 * Real.log L := by field_simp; ring
    rw [h3] at h2
    linarith
  have hM2 : min (Real.log (⌈k / L ^ 4⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / (1 / L))
      ≤ 2 * L := by
    refine le_trans (min_le_right _ _) ?_
    rw [one_div_one_div]
    linarith
  have hM10 : (0 : ℝ) ≤ min (Real.log (⌈k / L ^ 4⌉₊ : ℝ) + (Real.log 4 + 4))
      (1 + 2 / (1 / (4 * Real.log L) - 1 / L)) := by
    refine le_min window_grade_pos.le ?_
    have : (0 : ℝ) ≤ 2 / (1 / (4 * Real.log L) - 1 / L) := by
      exact div_nonneg (by norm_num) hgap0.le
    linarith
  have hM20 : (0 : ℝ) ≤ min (Real.log (⌈k / L ^ 4⌉₊ : ℝ) + (Real.log 4 + 4))
      (2 + 1 / (1 / L)) := by
    refine le_min window_grade_pos.le ?_
    rw [one_div_one_div]
    linarith
  -- the mass product against the `L`-page
  have hWW : (∑ n ∈ Finset.Ioo ⌊L ^ 4⌋₊ ⌈k / L ^ 4⌉₊,
        ‖lambdaLin (restrictAbove (L ^ 4) d) n‖ / (n : ℝ) ^ (1 + 1 / L - 1 / (4 * Real.log L)))
      * (∑ n ∈ Finset.Ioo ⌊L ^ 4⌋₊ ⌈k / L ^ 4⌉₊,
        ‖lambdaLin (restrictAbove (L ^ 4) d) n‖ / (n : ℝ) ^ (1 + 1 / L))
      ≤ (Real.log 4 + 4) ^ 2 * (k ^ (1 / (4 * Real.log L)) / (Real.exp 1 * Real.exp 1))
          * (17 * Real.log L * (2 * L)) := by
    refine hMass.trans ?_
    rw [far_mass_cancel hk hL]
    refine mul_le_mul_of_nonneg_left (mul_le_mul hM1 hM2 hM20 (by positivity)) ?_
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hWW0 : (0 : ℝ) ≤ (∑ n ∈ Finset.Ioo ⌊L ^ 4⌋₊ ⌈k / L ^ 4⌉₊,
        ‖lambdaLin (restrictAbove (L ^ 4) d) n‖ / (n : ℝ) ^ (1 + 1 / L - 1 / (4 * Real.log L)))
      * (∑ n ∈ Finset.Ioo ⌊L ^ 4⌋₊ ⌈k / L ^ 4⌉₊,
        ‖lambdaLin (restrictAbove (L ^ 4) d) n‖ / (n : ℝ) ^ (1 + 1 / L)) :=
    mul_nonneg (window_mass_nonneg d k (L ^ 4) _) (window_mass_nonneg d k (L ^ 4) _)
  -- the amplitude × tail factor
  have hfac : (k + k / Real.sqrt L) ^ (1 + 1 / L) * (4 * (Real.sqrt L + 1) / Tstar k L)
      ≤ 9 * k * (8 * Real.sqrt L / (L ^ 4 * k ^ (1 / (4 * Real.log L)))) := by
    have hsc : (k + k / Real.sqrt L) ^ (1 + 1 / L) ≤ 9 * k := pin_rpow_scaleT hk hL rfl rfl
    have hrat : 4 * (Real.sqrt L + 1) / Tstar k L
        ≤ 8 * Real.sqrt L / (L ^ 4 * k ^ (1 / (4 * Real.log L))) := by
      have hTeq : Tstar k L = L ^ 4 * k ^ (1 / (4 * Real.log L)) := rfl
      have hden : (0 : ℝ) < L ^ 4 * k ^ (1 / (4 * Real.log L)) := by positivity
      rw [hTeq, div_le_div_iff₀ hden hden]
      nlinarith [hs8, hden]
    refine mul_le_mul hsc hrat ?_ (by positivity)
    exact div_nonneg (by positivity) hT0.le
  have hfac0 : (0 : ℝ) ≤ (k + k / Real.sqrt L) ^ (1 + 1 / L)
      * (4 * (Real.sqrt L + 1) / Tstar k L) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (div_nonneg (by positivity) hT0.le)
  have hB0 : (0 : ℝ) ≤ (Real.log 4 + 4) ^ 2
      * (k ^ (1 / (4 * Real.log L)) / (Real.exp 1 * Real.exp 1)) * (17 * Real.log L * (2 * L)) := by
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  -- assemble
  unfold farKfarStar
  rw [hlogy]
  refine (mul_le_mul hWW hfac hfac0 hB0).trans ?_
  have hEq : (Real.log 4 + 4) ^ 2 * (k ^ (1 / (4 * Real.log L)) / (Real.exp 1 * Real.exp 1))
        * (17 * Real.log L * (2 * L))
        * (9 * k * (8 * Real.sqrt L / (L ^ 4 * k ^ (1 / (4 * Real.log L)))))
      = 2448 * (Real.log 4 + 4) ^ 2 * (k * Real.log L * Real.sqrt L / L ^ 3)
          * (1 / (Real.exp 1 * Real.exp 1)) := by
    field_simp
    ring
  rw [hEq]
  have hone : 1 / (Real.exp 1 * Real.exp 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  have hR0 : (0 : ℝ) ≤ 2448 * (Real.log 4 + 4) ^ 2 * (k * Real.log L * Real.sqrt L / L ^ 3) := by
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  nlinarith [hR0, hone]

/-- **The crown's currency, floored (`log_price_floor`).**  `(log X)^{−1/(32e)} ≥ 1/(2L)`
whenever `log X ≤ 2L` — which is all the crown's `⌊X⌋₊ ≤ k` supplies (`X < k+1 ≤ 2k`).  The
exponent `1/(32e) ≈ 0.0115` is far below `1`, so the crude `(log X)^{−1} ` floor is
enormously lossy and still leaves the far page a `√L·log L` margin. -/
private lemma log_price_floor {X L : ℝ} (hXe : Real.exp 1 ≤ X) (hXL : Real.log X ≤ 2 * L) :
    1 / (2 * L) ≤ Real.log X ^ (-(1 / (32 * Real.exp 1))) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hu1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hXe
  have hu0 : (0 : ℝ) < Real.log X := by linarith
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have ha1 : 1 / (32 * Real.exp 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have h1 : Real.log X ^ (-(1 : ℝ)) ≤ Real.log X ^ (-(1 / (32 * Real.exp 1))) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
  have h2 : Real.log X ^ (-(1 : ℝ)) = (Real.log X)⁻¹ := by
    rw [Real.rpow_neg hu0.le, Real.rpow_one]
  have h3 : 1 / (2 * L) ≤ (Real.log X)⁻¹ := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hu0 hXL
  rw [h2] at h1
  linarith

/-! ### The supply shelf at grade `1/16` (E34 V0s)

The E34 refuter fold found — and the helm re-verified at these bytes — that the printed
exponent `1/(32e)` in `log_price_floor`/`hfar_star` is a DELIBERATELY LOSSY weakening:
the proof's only use of it is `1/(32e) ≤ 1`, so the identical proof runs at `1/16`.  The
two theorems below make **"the corpus supplies A.6's grade summand at `1/16`"** a kernel
shelf instead of a fold claim (the helm's E34 ladder-repair commission, 2026-08-31, in
the private record).  Nothing consuming the `1/(32e)` form moves — these are siblings. -/

/-- **The far price floor at grade `1/16`** — sibling of `log_price_floor` at exponent
`−1/16`, proof identical: the exponent step needs only `1/16 ≤ 1`. -/
theorem far_price_floor_16 {X L : ℝ} (hXe : Real.exp 1 ≤ X) (hXL : Real.log X ≤ 2 * L) :
    1 / (2 * L) ≤ Real.log X ^ (-(1 / 16 : ℝ)) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hu1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hXe
  have hu0 : (0 : ℝ) < Real.log X := by linarith
  have ha1 : (1 : ℝ) / 16 ≤ 1 := by norm_num
  have h1 : Real.log X ^ (-(1 : ℝ)) ≤ Real.log X ^ (-(1 / 16 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
  have h2 : Real.log X ^ (-(1 : ℝ)) = (Real.log X)⁻¹ := by
    rw [Real.rpow_neg hu0.le, Real.rpow_one]
  have h3 : 1 / (2 * L) ≤ (Real.log X)⁻¹ := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hu0 hXL
  rw [h2] at h1
  linarith

/-- **The desmooth term is already under grade `1/16`** — `caseAS`'s third summand
`(log W)^{−1/2+1/1000}` decays FASTER than `(log W)^{−1/16}`.  Stated over `1 ≤ L`;
consume at `L = log W`. -/
theorem desmooth_under_grade16 {L : ℝ} (hL : 1 ≤ L) :
    L ^ (-(1 : ℝ) / 2 + 1 / 1000) ≤ L ^ (-(1 : ℝ) / 16) :=
  Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

/-- **The far arm's ABSOLUTE constant at `T*`** —
`Cfar = (306/π)·C_S·C_F·e^{24/e}·(log 4+4)²`.  No `k`, no `X`, no `L`: this is what
`FarClose`'s verdict says does not exist at `T = L⁴`. -/
def farCStar : ℝ := 306 * rhsCSF * Real.exp (24 / Real.exp 1) * (Real.log 4 + 4) ^ 2 / Real.pi

lemma farCStar_nonneg : 0 ≤ farCStar := by
  have h := rhsCSF_pos
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  unfold farCStar
  positivity

/-- **FS-3 — THE FAR SOCKET AT `T*` (`hfar_star`).**  `FarClose.rhs_grade_at_scale_closed`'s
`hfar` binder — the M-free purely arithmetic hypothesis its verdict shows is FALSE at
`T = L⁴` — DISCHARGED at `T := Tstar k L`, with `Cfar := farCStar` absolute:

  `(1/π)·η²·(Ffar·Kfar(T*)) ≤ farCStar·k·(log X)^{−1/(32e)}`.

The page: `Ffar = C_S·C_F·e^{24/e}·L`, `η² = 1/(16(log L)²)`, `Kfar(T*)` by
`far_kfar_star_le`, and the crown's currency floored by `log_price_floor`.  The residual
margin is `√L/(L·log L) ≤ 1` — decreasing, so the socket only gets easier with scale.

`hX2k : X ≤ 2k` is the crown's own `⌊X⌋₊ ≤ k` (`X < ⌊X⌋₊ + 1 ≤ k + 1 ≤ 2k`). -/
theorem hfar_star {d : ℕ → ℂ} (hd : ∀ p, p.Prime → ‖d p‖ ≤ 1) {k L y η X : ℝ}
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hXe : Real.exp 1 ≤ X) (hX2k : X ≤ 2 * k) :
    (1 / Real.pi) * (η ^ 2 * (farFbound L * farKfarStar d k L))
      ≤ farCStar * k * Real.log X ^ (-(1 / (32 * Real.exp 1))) := by
  obtain ⟨hk0, hL64, -, hlogy, -, -, -, -⟩ := pin_basic64T hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]; exact Real.sqrt_le_sqrt hL64
  have he2 : Real.exp 2 ≤ 64 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hlogL2 : (2 : ℝ) ≤ Real.log L := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) (by linarith)
  have hlogL0 : Real.log L ≠ 0 := by linarith
  -- the crown's currency, floored
  have hlogX : Real.log X ≤ 2 * L := by
    have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
    have h1 : Real.log X ≤ Real.log (2 * k) := Real.log_le_log hX0 hX2k
    rw [Real.log_mul (by norm_num) hk0.ne', ← hL] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    linarith
  have hfloor := log_price_floor hXe hlogX
  have hC0 : (0 : ℝ) ≤ farCStar * k := mul_nonneg farCStar_nonneg hk0.le
  -- the `Kfar` numeral and the `Ffar`/`η²` page
  have hK := far_kfar_star_le hd hk hL
  have hFnn : (0 : ℝ) ≤ farFbound L := farFbound_nonneg hL0.le
  calc (1 / Real.pi) * (η ^ 2 * (farFbound L * farKfarStar d k L))
      ≤ (1 / Real.pi) * (η ^ 2 * (farFbound L
          * (2448 * (Real.log 4 + 4) ^ 2 * (k * Real.log L * Real.sqrt L / L ^ 3)))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hFnn) (by positivity))
          (by positivity)
    _ = farCStar * k * (1 / (2 * L)) * (Real.sqrt L / (Real.log L * L)) := by
        rw [hη, hlogy]
        unfold farFbound farCStar
        field_simp
        ring
    _ ≤ farCStar * k * (1 / (2 * L)) * 1 := by
        have hfrac : Real.sqrt L / (Real.log L * L) ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith
        refine mul_le_mul_of_nonneg_left hfrac ?_
        have : (0 : ℝ) ≤ 1 / (2 * L) := by positivity
        exact mul_nonneg hC0 this
    _ = farCStar * k * (1 / (2 * L)) := by ring
    _ ≤ farCStar * k * Real.log X ^ (-(1 / (32 * Real.exp 1))) :=
        mul_le_mul_of_nonneg_left hfloor hC0

/-! ## §4 — FS-4: the seam gate at the new height

`SeamGate`'s route (b) is height-agnostic: the geometry bounds `|t₁| ≤ T_ann + seamRad X` with
no reference to the truncation height at all, so raising the height only changes the ONE
monotonicity step (`log_pow_four_le_of_le_two_mul` there, `Tstar_mono` here). -/

/-- **FS-4 — the gate radius at `T*` (`seamGateRstar`).**
`R := T_ann + seamRad X + T*(2X, log 2X) + 1` — `SeamGate.seamGateR` with the row's largest
presentable truncation height raised from `(log 2X)⁴` to `T*(2X)`.  `T*(2X)` is
`(log 2X)⁴·(2X)^{1/(4 log log 2X)}` — SUB-POLYNOMIAL in `X`, so in the `polyT` regime the
radius still satisfies `R ≪ X` and `⟦V3d⟧`'s strong two-`M` direction survives. -/
def seamGateRstar (X T : ℝ) : ℝ := T + seamRad X + Tstar (2 * X) (Real.log (2 * X)) + 1

lemma seamGateRstar_nonneg {X T : ℝ} (hT : 0 ≤ T) (hX : 1 ≤ X) : 0 ≤ seamGateRstar X T := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hLX : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX
  have hr : (0 : ℝ) ≤ seamRad X := seamRad_nonneg hLX
  have hL2X : (0 : ℝ) < Real.log (2 * X) := by
    have h1 : Real.log 2 ≤ Real.log (2 * X) := by
      refine Real.log_le_log (by norm_num) ?_; linarith
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hTs : (0 : ℝ) < Tstar (2 * X) (Real.log (2 * X)) := Tstar_pos (by linarith) hL2X
  unfold seamGateRstar
  linarith

/-- **FS-4 — THE GATE AT `T*` (`seam_gate_star_of_nonempty`).**  `SeamGate`'s
`seam_gate_of_nonempty` with `Tstar_mono` in place of `log_pow_four_le_of_le_two_mul`:
on the ball leg's own domain, at the minimality radius `seamGateRstar X T_ann`,

  `|t₁| + T*(k, log k) ≤ seamGateRstar X T_ann`  for every `e^e ≤ k ≤ 2X`.

Still no `hgap`, no localization, no numeral shift, and no reference to `X` as a bound on
`|t₁|`.  The gate on `k` is FS-1m's honest one (`k ≥ e^e`), which the corpus scale gate
`k ≥ e^64` clears. -/
theorem seam_gate_star_of_nonempty {X T t₁ k : ℝ} (hk : Real.exp (Real.exp 1) ≤ k)
    (hkX : k ≤ 2 * X) (hne : (seamAnn X T ∩ seamBall X t₁).Nonempty) :
    |t₁| + Tstar k (Real.log k) ≤ seamGateRstar X T := by
  have h1 := seamAnn_inter_seamBall_center_le hne
  have h2 := Tstar_mono hk hkX
  unfold seamGateRstar
  linarith

/-- **FS-4 — the minimizer at the star radius (`exists_min_gate_star`).**
`CompactMin.exists_min_dist_abs` at `R := seamGateRstar X T_ann`. -/
theorem exists_min_gate_star (f : ℕ → ℂ) {X T : ℝ} (hT : 0 ≤ T) (hX : 1 ≤ X) :
    ∃ t₁ : ℝ, |t₁| ≤ seamGateRstar X T ∧ ∀ v : ℝ, |v| ≤ seamGateRstar X T →
      pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist v) X :=
  exists_min_dist_abs f X (seamGateRstar_nonneg hT hX)

/-- **FS-4 — the bundle (`seam_gate_star_package`).**  `SeamGate.seam_gate_package` at the new
height: ONE centre carrying the compact minimality at radius `seamGateRstar X T_ann` and, on
the ball leg's own domain, the recentring gate at every `T*(k, log k)`, `e^e ≤ k ≤ 2X`. -/
theorem seam_gate_star_package (f : ℕ → ℂ) {X T : ℝ} (hT : 0 ≤ T) (hX : 1 ≤ X) :
    ∃ t₁ : ℝ,
      (∀ v : ℝ, |v| ≤ seamGateRstar X T →
        pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist v) X)
      ∧ ∀ k : ℝ, Real.exp (Real.exp 1) ≤ k → k ≤ 2 * X →
          (seamAnn X T ∩ seamBall X t₁).Nonempty →
          |t₁| + Tstar k (Real.log k) ≤ seamGateRstar X T := by
  obtain ⟨t₁, -, hmin⟩ := exists_min_gate_star f hT hX
  exact ⟨t₁, hmin, fun k hk hkX hne => seam_gate_star_of_nonempty hk hkX hne⟩

/-! ## §5 — FS-5: the closed chain at `T*`

`FarClose`'s F-4 / `hRHS` / crown, re-run at `T := Tstar k L`, `R := seamGateRstar X T_ann`,
`Cfar := farCStar`.  Both of `FarClose`'s carried sockets are gone: `hKfar` and `hfar` by §2/§3,
`hgate` by §4.  What is left is the pin, the scale gate, the ball geometry and upstream's own
integrability. -/

set_option maxHeartbeats 800000 in
-- The composition instantiates `rhs_grade_at_scale_closed`'s eight sockets, each carrying the
-- five pin expressions; the unification exceeds the default budget (as it does at F-4).
/-- **FS-5a — THE CLOSED GRADE AT SCALE, AT `T*` (`rhs_grade_at_scale_closed_star`).**
`FarClose.rhs_grade_at_scale_closed` at `T := Tstar k L`, `R := seamGateRstar X T_ann`, with

* `hKfar` discharged by `far_kernel_bound_star` (FS-2),
* `hfar` discharged by `hfar_star` (FS-3) — the socket `FarClose` had to carry,
* `hgate` discharged by `seam_gate_star_of_nonempty` (FS-4) from the ball leg's nonemptiness,

leaving the ONE-term exit with the ABSOLUTE constant `gradeAbsConst Cb + farCStar`:

  `‖prop21RHS‖ ≤ (gradeAbsConst Cb + farCStar)·k·e^{−(1/(2e))·𝔻²}`.

**The carried hypotheses, enumerated.**  (1) the pin equations `hL/hy/hη/hc₀/hh` and the scale
gate `e^{64} ≤ k`; (2) `hXk : ⌊X⌋₊ ≤ ⌊k⌋₊`, `hXe : e ≤ X`, and the row's two scale relations
`hX2k : X ≤ 2k` (the crown's own, `X < ⌊X⌋₊+1 ≤ k+1`) and `hkX : k ≤ 2X` (the dyadic row);
(3) `hne`, the ball leg's domain being nonempty (the empty arm is `SeamGate`'s
`ball_leg_of_inter_empty`); (4) `hmin`, the compact minimality at radius `seamGateRstar X T_ann`;
(5) `hMcap`, the crown's A-10 ball cap; (6) the `JointIntegrableAt` bundle.  **No far socket,
no kernel socket, no gate socket.** -/
theorem rhs_grade_at_scale_closed_star {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Cb t₀ t₁ X k L c₀ y η h Tann : ℝ}
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L)
    (hXk : ⌊X⌋₊ ≤ ⌊k⌋₊) (hXe : Real.exp 1 ≤ X) (hX2k : X ≤ 2 * k) (hkX : k ≤ 2 * X)
    (hne : (seamAnn X Tann ∩ seamBall X t₁).Nonempty)
    (hmin : ∀ v : ℝ, |v| ≤ seamGateRstar X Tann →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hMcap : pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
      ≤ 1 / 16 * Real.log (Real.log X))
    (hInt : JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
      (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) k L c₀ y η h) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁) k h c₀ y η‖
      ≤ (gradeAbsConst Cb + farCStar) * k
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
  have hgtw : ∀ p, p.Prime →
      ‖(fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist (t₀ + t₁) hp.one_lt.le, mul_one]
    exact hg p hp
  have hee : Real.exp (Real.exp 1) ≤ k :=
    le_trans (Real.exp_le_exp.mpr (by linarith [Real.exp_one_lt_d9])) hk
  have hgate : |t₁| + Tstar k L ≤ seamGateRstar X Tann := by
    rw [hL]
    exact seam_gate_star_of_nonempty hee hkX hne
  refine rhs_grade_at_scale_closed hg hCb0 hCbound farCStar_nonneg hk hL hy hη hc₀ hh hXk hXe
    hgate hmin hMcap ?_ (hfar_star hgtw hk hL hy hη hXe hX2k) hInt
  rw [hh]
  exact far_kernel_bound_star hk hL hy hη hc₀

set_option maxHeartbeats 800000 in
-- As at `FarClose.hRHS_socket_of_far`: the crown's binder shape, five pin expressions per
-- socket, unified against the closed grade's own pin equations.
/-- **FS-5b — THE CROWN'S `hRHS` BINDER AT `T*` (`hRHS_socket_star`).**
`FarClose.hRHS_socket_of_far` with `T k := T*(k, log k)` and `Kfar k := farKfarStar`, and with
its three per-scale sockets (`hgate`, `hKf`, `hfar`) DISCHARGED.  The statement is
`CenterSupply.ball_sup_supplied`'s `hRHS` hypothesis byte-for-byte at
`C₁ := gradeAbsConst Cb + farCStar`; what remains quantified over the scale is only the gate
`e^{64} ≤ k` and upstream's own integrability. -/
theorem hRHS_socket_star {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Cb t₀ t₁ X Tann : ℝ} {N : ℕ}
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb) (hXe : Real.exp 1 ≤ X)
    (hN2X : (N : ℝ) ≤ 2 * X)
    (hmin : ∀ v : ℝ, |v| ≤ seamGateRstar X Tann →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hMcap : pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
      ≤ 1 / 16 * Real.log (Real.log X))
    (hk64 : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Real.exp 64 ≤ (k : ℝ))
    (hne : (seamAnn X Tann ∩ seamBall X t₁).Nonempty)
    (hInt : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
        (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) (k : ℝ)
        (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
        (1 / Real.log (Real.log (k : ℝ) ^ 4)) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) :
    ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
          (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
          (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
        ≤ (gradeAbsConst Cb + farCStar) * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
  have hgtw : ∀ p, p.Prime →
      ‖(fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist (t₀ + t₁) hp.one_lt.le, mul_one]
    exact hg p hp
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  intro k hk1 hk2
  have hk := hk64 k hk1 hk2
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 64) hk
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by
    have h65 : (65 : ℝ) ≤ (k : ℝ) := by linarith [Real.add_one_le_exp (64 : ℝ)]
    linarith
  have hXk : ⌊X⌋₊ ≤ ⌊(k : ℝ)⌋₊ := by rw [Nat.floor_natCast]; exact hk1
  have hX2k : X ≤ 2 * (k : ℝ) := by
    have h1 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
    have h2 : (⌊X⌋₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hkX : (k : ℝ) ≤ 2 * X := le_trans (by exact_mod_cast hk2) hN2X
  exact rhs_grade_at_scale_closed_star hg hCb0 hCbound hk rfl rfl rfl rfl rfl hXk hXe hX2k hkX
    hne hmin hMcap (hInt k hk1 hk2)

set_option maxHeartbeats 800000 in
-- The crown's binder block is instantiated wholesale (eight sockets, five pin expressions
-- each); the unification exceeds the default budget, as at `FarClose.ball_sup_closed`.
/-- **FS-5c — THE CROWN AT `T*` (`ball_sup_closed_star`).**
`FarClose.ball_sup_closed` with `Cfar := farCStar`, `R := seamGateRstar X T_ann`,
`T k := T*(k, log k)`, `Kfar k := farKfarStar`, and its two carried sockets DISCHARGED: the
`hfar` arithmetic (FS-3) and the recentring gate (FS-4, from the ball leg's nonemptiness).

  `‖spolyA a t m‖ ≤ ballSupS X (C₁·e^{−(1/(2e))·𝔻²} + 4(log X)^{−1/2+1/1000})·m/(1+|t−t₁|)`,
  `C₁ = gradeAbsConst Cb + farCStar` ABSOLUTE.

**The carried hypotheses, enumerated** (this is the whole list):
(1) `hg`, the primes' norm bound;
(2) the scale frame `X₀ ≤ X`, `e ≤ X`, `X ≤ N ≤ 2X`;
(3) `0 ≤ Cb` and `ShortIntervalDatum Cb` (the short-interval Chebyshev datum);
(4) the coefficient equations for `a` (`0` below `X`, the seam datum above);
(5) `hmin`, the COMPACT minimality at radius `seamGateRstar X T_ann` (non-vacuous: `|v| ≤ R`
    only — supplied at a chosen centre by `seam_gate_star_package`, though not at THIS `t₁`,
    which the statement fixes before `X`; the honest instantiation is the consumer's);
(6) `hMcap`, the crown's A-10 ball cap on `[X, 2X]`;
(7) `hk64`, the scale gate `e^{64} ≤ k` on the row's range;
(8) `hne`, the ball leg's domain nonempty — the ONLY new hypothesis versus `ball_sup_closed`,
    and the empty arm is `SeamGate.ball_leg_of_inter_empty` (`0 ≤ 8S²`, any `S`);
(9) the four `JointIntegrableAt` sockets, upstream's own.

Gone versus `FarClose.ball_sup_closed`: `0 ≤ Cfar`, the free `T`/`Kfar` functions, the kernel
binder `hKf`, the far arithmetic `hfar` (FALSE at `L⁴`, TRUE here), and the gate `hgate`. -/
theorem ball_sup_closed_star {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t₁ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (Tb Cb Tann : ℝ) (a : ℕ → ℂ),
        X₀ ≤ X → Real.exp 1 ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X →
        0 ≤ Cb → ShortIntervalDatum Cb →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        (∀ v : ℝ, |v| ≤ seamGateRstar X Tann →
          pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
            ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
          pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
            ≤ (1 / 16) * Real.log (Real.log X)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Real.exp 64 ≤ (k : ℝ)) →
        (seamAnn X Tann ∩ seamBall X t₁).Nonempty →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
            (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) (k : ℝ)
            (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
            (1 / Real.log (Real.log (k : ℝ) ^ 4))
            ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) →
      ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tb → |t - t₁| ≤ seamRad X →
        ∀ m : ℕ, m ≤ N →
          ‖spolyA a t m‖
            ≤ ballSupS X ((gradeAbsConst Cb + farCStar)
                  * Real.exp (-(1 / (2 * Real.exp 1))
                      * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * m / (1 + |t - t₁|) := by
  obtain ⟨X₀, hX₀0, H⟩ := ball_sup_supplied hg t₀ t₁
  refine ⟨X₀, hX₀0, ?_⟩
  intro X N Tb Cb Tann a hXlb hXe hXN hN2 hCb0 hCbound hsupp hDatum hmin hMcapX hk64 hne hInt
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  exact H X N Tb (gradeAbsConst Cb + farCStar) a hXlb hXN hN2
    (by have := gradeAbsConst_nonneg hCb0; have := farCStar_nonneg; linarith) hsupp hDatum
    (hRHS_socket_star hg hCb0 hCbound hXe hN2 hmin (hMcapX X le_rfl (by linarith)) hk64 hne
      hInt) hMcapX

end Salt.MR
