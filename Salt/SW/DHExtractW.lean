/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.SelOpt
import Salt.SW.DHClose2
import Salt.SW.DHCore
import Salt.SW.DHBal2
import Salt.SW.DHExtract
import Salt.SW.DHRepulsion
import Salt.HardyLittlewood.Sharp

/-!
# The weighted pole-cancelled extraction (`T-BAL` R6) — `dh_extraction_upper_W`

The JYH-ratified **R6 freeze** (`docs/exploration/r6-freeze.md`, survived 0/2). This module lands
the weighted extraction: the Selberg-mollified detector's `β₀`-twisted partial sum is `L(1,χ)`-main
plus a `Y^{1/2−β₀}` error, via an EXACT template reduction to the landed `m = 1` template (no third
convolution ever materializes).

The eight rungs (freeze §RUNGS):

* **R6-1** `kernel_abel_sum_real` — the real-scale kernel-Abel identity + the MVT upper tangent.
* **R6-2** `dhAbel_inner_abs_le` — the TWO-SIDED per-`t` inner bound (re-assembly of DHCore legs).
* **R6-3** `unmoll_extraction_abs_real` — the real-scale two-sided extraction (`C₂ = 4·C_w`).
* **R6-4** `dhA_kernel_reduction` — THE EXACT REDUCTION to the template at rescaled real scales.
* **R6-5** `selHmul_collection` — the signed `(g,k)` collection into `selHmul`.
* **R6-6** support + moment stones (`gcW` sqfree-`z`-support, the `z(1+log z²)⁹` moment).
* **R6-7** `sum_gcW_selNu_eq_selMainTerm` — the SIGNED main-term collection into `selMainTerm`.
* **R6-8** `dh_extraction_upper_W` — the assembly.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
Numeric certs: `scripts/tbal_ledgers/r6_verify.py` (+ the refuter).
-/

open Finset
open ArithmeticFunction
open scoped ArithmeticFunction.omega

noncomputable section

namespace Salt.SW

variable {q : ℕ}

/-! ## §0 — the real-scale unmollified detector `D₀` -/

/-- **The real-scale unmollified `β₀`-detector.** `D₀(x) = Σ_{s≤⌊x⌋} dhA χ s · s^{−β₀}·(1 − s/x)`
for real `x`. The rescaled template the reduction (R6-4) targets: at scale `x = Y/(mk)` the
per-`(g,k)` main term is `L₁·x^{1−β₀}/((1−β₀)(2−β₀))`, controlled two-sidedly by R6-3. -/
def dhD0 (χ : DirichletCharacter ℂ q) (β₀ x : ℝ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 ⌊x⌋₊, dhA χ s * (s : ℝ) ^ (-β₀) * (1 - (s : ℝ) / x)

/-! ## §1 — R6-1 : the real-scale kernel-Abel identity + the MVT upper tangent -/

/-- **R6-1 (kernel-Abel, real scale).** For any `a : ℕ → ℝ` and `x ≥ 1`, with `T = ⌊x⌋`,
`Σ_{s≤T} a_s·(1 − s/x) = (1/x)·[(x − T)·A(T) + Σ_{t≤T−1} A(t)]`, `A(t) = Σ_{s≤t} a_s`. Summation
by parts (`sum_mul_index_eq`) against the linear kernel; the boundary term `(x − T)·A(T)` is the
real-floor correction (`= 0` at integer `x`). -/
theorem kernel_abel_sum_real (a : ℕ → ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ∑ s ∈ Finset.Icc 1 ⌊x⌋₊, a s * (1 - (s : ℝ) / x)
      = (1 / x) * ((x - (⌊x⌋₊ : ℝ)) * (∑ s ∈ Finset.Icc 1 ⌊x⌋₊, a s)
          + ∑ t ∈ Finset.Icc 1 (⌊x⌋₊ - 1), ∑ s ∈ Finset.Icc 1 t, a s) := by
  have hx0 : (0 : ℝ) < x := by linarith
  set T : ℕ := ⌊x⌋₊ with hTdef
  have hT1 : 1 ≤ T := by rw [hTdef, Nat.le_floor_iff (by linarith)]; exact_mod_cast hx
  have hkey := sum_mul_index_eq a hT1
  have hexpand : ∑ s ∈ Finset.Icc 1 T, a s * (1 - (s : ℝ) / x)
      = (∑ s ∈ Finset.Icc 1 T, a s) - (1 / x) * ∑ s ∈ Finset.Icc 1 T, (s : ℝ) * a s := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  rw [hexpand, hkey]
  field_simp
  ring

/-- **The MVT upper tangent** (`c ∈ [1,2]`). For `x ≥ 1`, `x^c − (x−1)^c ≤ c·x^{c−1}`. Mean value
theorem for `z ↦ z^c` on `[x−1, x]` plus `ξ^{c−1} ≤ x^{c−1}` (`ξ ≤ x`, exponent `c−1 ≥ 0`). Mirror
of `rpow_sub_le_tangent` for the `[1,2]` exponent range (the real-scale Riemann sandwich). -/
theorem rpow_sub_le_tangent_upper {c : ℝ} (hc1 : 1 ≤ c) {x : ℝ} (hx : 1 ≤ x) :
    x ^ c - (x - 1) ^ c ≤ c * x ^ (c - 1) := by
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hlt : x - 1 < x := by linarith
  have hcont : ContinuousOn (fun z : ℝ => z ^ c) (Set.Icc (x - 1) x) :=
    ContinuousOn.rpow_const continuousOn_id (fun z _ => Or.inr hc0)
  have hderiv : ∀ z ∈ Set.Ioo (x - 1) x, HasDerivAt (fun z : ℝ => z ^ c) (c * z ^ (c - 1)) z := by
    intro z hz
    have hz0 : 0 < z := lt_of_le_of_lt (by linarith) hz.1
    exact Real.hasDerivAt_rpow_const (Or.inl hz0.ne')
  obtain ⟨ξ, hξ, hslope⟩ :=
    exists_hasDerivAt_eq_slope (fun z : ℝ => z ^ c) (fun z => c * z ^ (c - 1)) hlt hcont hderiv
  have hξ0 : 0 < ξ := lt_of_le_of_lt (by linarith) hξ.1
  have hξx : ξ ≤ x := le_of_lt hξ.2
  have hmono : ξ ^ (c - 1) ≤ x ^ (c - 1) := Real.rpow_le_rpow hξ0.le hξx (by linarith)
  have heq : x ^ c - (x - 1) ^ c = c * ξ ^ (c - 1) := by
    have hden : x - (x - 1) = 1 := by ring
    rw [hden] at hslope
    field_simp at hslope ⊢
    linarith [hslope]
  rw [heq]
  exact mul_le_mul_of_nonneg_left hmono hc0

/-! ## §2 — R6-2 : the TWO-SIDED per-`t` inner bound -/

/-- **R6-2 (`dhAbel_inner_abs_le`).** The two-sided companion of `dhAbel_inner_le`: for a real
primitive `χ` at a real zero `β₀`,
`|A(t) − L(1,χ).re·t^{1−β₀}/(1−β₀)| ≤ C_w·t^{1/2−β₀}`, `A(t) = Σ_{n≤t} dhA χ n·n^{−β₀}`,
`C_w = 34 + 12M + 12M·Z₀ + 36M/(1−β₀)`, `M = √q(1+log q)`. Re-assembly of the DHCore hyperbola
legs: `A = Leg₁ + Leg₂ − Corner`, with `|Leg₁ − main| ≤ (34+12MZ₀+24M/u)D` (`dhAbel_leg1_le`),
`|Leg₂| ≤ 12M·D`, `|Corner| ≤ 12M/u·D` (the two proof-local blocks copied from `dhAbel_inner_le`),
whence the triangle inequality gives `C_w`. -/
theorem dhAbel_inner_abs_le [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β₀ : ℝ}
    (hzero : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0) (hlo : 1 / 2 ≤ β₀) (hhi : β₀ < 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {t : ℕ} (ht : 1 ≤ t) :
    |(∑ n ∈ Finset.Icc 1 t, dhA χ n * (n : ℝ) ^ (-β₀))
        - (DirichletCharacter.LFunction χ 1).re * (t : ℝ) ^ (1 - β₀) / (1 - β₀)|
      ≤ (34 + 12 * (Real.sqrt q * (1 + Real.log q))
          + 12 * (Real.sqrt q * (1 + Real.log q)) * Z₀
          + 36 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀)) * (t : ℝ) ^ (1 / 2 - β₀) := by
  set M : ℝ := Real.sqrt q * (1 + Real.log q) with hMdef
  set r : ℕ := Nat.sqrt t with hrdef
  set D : ℝ := (t : ℝ) ^ (1 / 2 - β₀) with hDdef
  set L₁ : ℝ := (DirichletCharacter.LFunction χ 1).re with hL1def
  have hβ0 : 0 < β₀ := by linarith
  have hu : 0 < 1 - β₀ := by linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hDnn : 0 ≤ D := Real.rpow_nonneg ht0.le _
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hr1 : 1 ≤ r := by
    rw [hrdef]; calc 1 = Nat.sqrt 1 := Nat.sqrt_one.symm
      _ ≤ Nat.sqrt t := Nat.sqrt_le_sqrt ht
  have hrt : r ≤ t := by rw [hrdef]; exact Nat.sqrt_le_self t
  have hB : ∀ m : ℕ, 1 ≤ m →
      |∑ d ∈ Finset.Icc 1 m, chiRe χ d * (d : ℝ) ^ (-β₀)| ≤ 6 * M * (m : ℝ) ^ (-β₀) :=
    fun m hm => chiRe_partial_at_zero_le χ hχ hsq hq hzero hβ0 (by linarith) hm
  rw [dhAbel_hyperbola χ t, ← hrdef]
  -- LEG 2 bound : `|Σ_{e≤r} e^{−β₀}·B(⌊t/e⌋)| ≤ 12M·D` (copied from `dhAbel_inner_le`)
  have hLeg2 : |∑ e ∈ Finset.Icc 1 r, (e : ℝ) ^ (-β₀)
        * ∑ d ∈ Finset.Icc 1 (t / e), chiRe χ d * (d : ℝ) ^ (-β₀)| ≤ 12 * M * D := by
    have hstep : ∀ e ∈ Finset.Icc 1 r,
        |(e : ℝ) ^ (-β₀) * ∑ d ∈ Finset.Icc 1 (t / e), chiRe χ d * (d : ℝ) ^ (-β₀)|
          ≤ 6 * M * (2 * (t : ℝ) ^ (-β₀)) := by
      intro e he
      rw [Finset.mem_Icc] at he
      have het : e ≤ t := le_trans he.2 hrt
      have hte1 : 1 ≤ t / e := (Nat.one_le_div_iff (by omega)).mpr het
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      calc (e : ℝ) ^ (-β₀) * |∑ d ∈ Finset.Icc 1 (t / e), chiRe χ d * (d : ℝ) ^ (-β₀)|
          ≤ (e : ℝ) ^ (-β₀) * (6 * M * ((t / e : ℕ) : ℝ) ^ (-β₀)) :=
            mul_le_mul_of_nonneg_left (hB (t / e) hte1) (Real.rpow_nonneg (by positivity) _)
        _ = 6 * M * ((e : ℝ) ^ (-β₀) * ((t / e : ℕ) : ℝ) ^ (-β₀)) := by ring
        _ ≤ 6 * M * (2 * (t : ℝ) ^ (-β₀)) := by
            apply mul_le_mul_of_nonneg_left
              (term_rpow_le (by linarith) (by linarith) he.1 het) (by positivity)
    calc |∑ e ∈ Finset.Icc 1 r, (e : ℝ) ^ (-β₀)
            * ∑ d ∈ Finset.Icc 1 (t / e), chiRe χ d * (d : ℝ) ^ (-β₀)|
        ≤ ∑ e ∈ Finset.Icc 1 r, |(e : ℝ) ^ (-β₀)
            * ∑ d ∈ Finset.Icc 1 (t / e), chiRe χ d * (d : ℝ) ^ (-β₀)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ Finset.Icc 1 r, 6 * M * (2 * (t : ℝ) ^ (-β₀)) := Finset.sum_le_sum hstep
      _ = (r : ℝ) * (12 * M * (t : ℝ) ^ (-β₀)) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
      _ ≤ 12 * M * D := by
          rw [hDdef, hrdef]
          have := natSqrt_mul_rpow_le (β := β₀) ht
          nlinarith [this, hMnn, natSqrt_le_sqrt t, Real.sqrt_nonneg (t : ℝ)]
  -- CORNER bound : `|B(⌊√t⌋)·T(⌊√t⌋)| ≤ 12M/(1−β₀)·D` (copied from `dhAbel_inner_le`)
  have hCorner : |(∑ d ∈ Finset.Icc 1 r, chiRe χ d * (d : ℝ) ^ (-β₀))
        * ∑ e ∈ Finset.Icc 1 r, (e : ℝ) ^ (-β₀)| ≤ 12 * M / (1 - β₀) * D := by
    rw [abs_mul]
    have hTr : |∑ e ∈ Finset.Icc 1 r, (e : ℝ) ^ (-β₀)| ≤ (r : ℝ) ^ (1 - β₀) / (1 - β₀) := by
      rw [abs_of_nonneg (Finset.sum_nonneg (fun e _ => Real.rpow_nonneg (by positivity) _))]
      exact sum_rpow_neg_le (by linarith) hhi r
    have hr1m2 : (r : ℝ) ^ (-β₀) * (r : ℝ) ^ (1 - β₀) ≤ 2 * D := by
      have hb := sqrt_pow_bound (a := (1 - 2 * β₀)) (by linarith) (by linarith) (t := t) ht
      rw [← hrdef] at hb
      have hcomb : (r : ℝ) ^ (-β₀) * (r : ℝ) ^ (1 - β₀) = (r : ℝ) ^ (1 - 2 * β₀) := by
        rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < r))]; congr 1; ring
      rw [hcomb]
      have hhalf : (1 - 2 * β₀) / 2 = 1 / 2 - β₀ := by ring
      rw [hhalf] at hb; rw [hDdef]; exact hb
    calc |∑ d ∈ Finset.Icc 1 r, chiRe χ d * (d : ℝ) ^ (-β₀)|
            * |∑ e ∈ Finset.Icc 1 r, (e : ℝ) ^ (-β₀)|
        ≤ (6 * M * (r : ℝ) ^ (-β₀)) * ((r : ℝ) ^ (1 - β₀) / (1 - β₀)) :=
          mul_le_mul (hB r hr1) hTr (abs_nonneg _) (by positivity)
      _ = 6 * M / (1 - β₀) * ((r : ℝ) ^ (-β₀) * (r : ℝ) ^ (1 - β₀)) := by ring
      _ ≤ 6 * M / (1 - β₀) * (2 * D) := by
          apply mul_le_mul_of_nonneg_left hr1m2 (by positivity)
      _ = 12 * M / (1 - β₀) * D := by ring
  -- LEG 1 : the main-term leg (exported abs bound)
  have hLeg1 := dhAbel_leg1_le χ hχ hsq hq hzero hlo hhi hZ ht
  rw [← hrdef, ← hMdef, ← hDdef, ← hL1def] at hLeg1
  -- triangle inequality
  have hsplit : (34 + 12 * M + 12 * M * Z₀ + 36 * M / (1 - β₀)) * D
      = (34 + 12 * M * Z₀ + 24 * M / (1 - β₀)) * D + 12 * M * D + 12 * M / (1 - β₀) * D := by ring
  rw [hsplit, abs_le]
  have h1 := abs_le.mp hLeg1
  have h2 := abs_le.mp hLeg2
  have h3 := abs_le.mp hCorner
  exact ⟨by linarith [h1.1, h2.1, h3.2], by linarith [h1.2, h2.2, h3.1]⟩

/-! ## §3 — R6-3 : the real-scale two-sided extraction -/

/-- **Lower power-sum cap.** For `c ≥ 0`, `n^{c+1}/(c+1) ≤ Σ_{1≤t≤n} t^c`. Telescoping the MVT
upper tangent `(n+1)^{c+1} − n^{c+1} ≤ (c+1)(n+1)^c` (`rpow_sub_le_tangent_upper`). The lower
Riemann leg of the real-scale main-term sandwich (no integral machinery). -/
theorem sum_rpow_ge {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    (n : ℝ) ^ (c + 1) / (c + 1) ≤ ∑ t ∈ Finset.Icc 1 n, (t : ℝ) ^ c := by
  have hc1 : (0 : ℝ) < c + 1 := by linarith
  induction n with
  | zero => simp [Real.zero_rpow hc1.ne']
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have htan := rpow_sub_le_tangent_upper (c := c + 1) (by linarith)
      (x := (n : ℝ) + 1) (le_add_of_nonneg_left (Nat.cast_nonneg n))
    have hnn : ((n : ℝ) + 1) - 1 = (n : ℝ) := by ring
    have hexp : (c + 1) - 1 = c := by ring
    rw [hnn, hexp] at htan
    have hstep : ((n : ℝ) + 1) ^ (c + 1) / (c + 1)
        ≤ (n : ℝ) ^ (c + 1) / (c + 1) + ((n : ℝ) + 1) ^ c := by
      rw [div_add' _ _ _ hc1.ne', div_le_div_iff_of_pos_right hc1]
      linarith [htan]
    push_cast
    linarith [ih, hstep]

/-- **The real-scale main-term Riemann sandwich.** For `0 ≤ c ≤ 1`, `x ≥ 2` and `T = ⌊x⌋`,
`|(x − T)·T^c + Σ_{1≤t≤T−1} t^c − x^{c+1}/(c+1)| ≤ 2·x^c`. Upper leg from `sum_rpow_le_integral`;
lower leg from `sum_rpow_ge`; the floor gap `x − (T−1) ≤ 2` is closed by two applications of the
MVT upper tangent. The `Y^{1/2−β₀}`-grade error of the real-scale extraction's main term. -/
theorem sum_rpow_sandwich {c : ℝ} (hc0 : 0 ≤ c) (_hc1 : c ≤ 1) {x : ℝ} (hx : 2 ≤ x)
    {T : ℕ} (hT1 : 1 ≤ T) (hTx : (T : ℝ) ≤ x) (hxT : x < (T : ℝ) + 1) :
    |((x - (T : ℝ)) * (T : ℝ) ^ c + ∑ t ∈ Finset.Icc 1 (T - 1), (t : ℝ) ^ c)
        - x ^ (c + 1) / (c + 1)| ≤ 2 * x ^ c := by
  have hc1p : (0 : ℝ) < c + 1 := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hxT0 : (0 : ℝ) ≤ x - (T : ℝ) := by linarith
  have hxT1 : x - (T : ℝ) ≤ 1 := by linarith
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT1
  have hTcast : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by rw [Nat.cast_sub hT1]; push_cast; ring
  have hTc_nn : (0 : ℝ) ≤ (T : ℝ) ^ c := Real.rpow_nonneg hTpos.le _
  have hxc_nn : (0 : ℝ) ≤ x ^ c := Real.rpow_nonneg hx0.le _
  have hTc_le : (T : ℝ) ^ c ≤ x ^ c := Real.rpow_le_rpow hTpos.le hTx hc0
  -- UPPER leg
  have hSum_le : ∑ t ∈ Finset.Icc 1 (T - 1), (t : ℝ) ^ c ≤ (x : ℝ) ^ (c + 1) / (c + 1) := by
    have h := sum_rpow_le_integral (r := c) hc0 (T - 1)
    rw [hTcast, sub_add_cancel] at h
    have hTx1 : (T : ℝ) ^ (c + 1) ≤ x ^ (c + 1) := Real.rpow_le_rpow hTpos.le hTx (by linarith)
    have hmono : ((T : ℝ) ^ (c + 1) - 1) / (c + 1) ≤ (x : ℝ) ^ (c + 1) / (c + 1) := by
      rw [div_le_div_iff_of_pos_right hc1p]; linarith [hTx1]
    linarith [h, hmono]
  have hcorner_le : (x - (T : ℝ)) * (T : ℝ) ^ c ≤ x ^ c := by
    calc (x - (T : ℝ)) * (T : ℝ) ^ c ≤ 1 * x ^ c :=
          mul_le_mul hxT1 hTc_le hTc_nn (by norm_num)
      _ = x ^ c := one_mul _
  -- LOWER leg
  have hSum_ge : ((T : ℝ) - 1) ^ (c + 1) / (c + 1) ≤ ∑ t ∈ Finset.Icc 1 (T - 1), (t : ℝ) ^ c := by
    have h := sum_rpow_ge hc0 (T - 1); rwa [hTcast] at h
  have htan1 := rpow_sub_le_tangent_upper (c := c + 1) (by linarith) (x := x) (by linarith)
  have htan2 := rpow_sub_le_tangent_upper (c := c + 1) (by linarith) (x := x - 1) (by linarith)
  rw [show x - 1 - 1 = x - 2 by ring, show c + 1 - 1 = c by ring] at htan2
  rw [show c + 1 - 1 = c by ring] at htan1
  have hx1c : (x - 1) ^ c ≤ x ^ c := Real.rpow_le_rpow (by linarith) (by linarith) hc0
  have hT1x2 : (x - 2) ^ (c + 1) ≤ ((T : ℝ) - 1) ^ (c + 1) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  -- x^{c+1} − (T−1)^{c+1} ≤ 2(c+1)x^c
  have hgap : x ^ (c + 1) - ((T : ℝ) - 1) ^ (c + 1) ≤ 2 * (c + 1) * x ^ c := by
    nlinarith [htan1, htan2, hx1c, hT1x2]
  rw [abs_le]
  constructor
  · -- lower: −2x^c ≤ (corner + sum) − x^{c+1}/(c+1)
    have hdiv : (x ^ (c + 1) - ((T : ℝ) - 1) ^ (c + 1)) / (c + 1) ≤ 2 * x ^ c := by
      rw [div_le_iff₀ hc1p]; nlinarith [hgap]
    have : x ^ (c + 1) / (c + 1) - ((T : ℝ) - 1) ^ (c + 1) / (c + 1)
        = (x ^ (c + 1) - ((T : ℝ) - 1) ^ (c + 1)) / (c + 1) := by ring
    nlinarith [hSum_ge, hxT0, hTc_nn, mul_nonneg hxT0 hTc_nn, hdiv, this]
  · -- upper: (corner + sum) − x^{c+1}/(c+1) ≤ 2x^c
    linarith [hSum_le, hcorner_le, hxc_nn]

set_option maxHeartbeats 1200000 in
-- Many error/main legs + field_simp/ring over the (1−β₀)(2−β₀) denominators exceed the default.
/-- **R6-3 (`unmoll_extraction_abs_real`).** The real-scale two-sided extraction. For a real
primitive `χ` at a real zero `β₀` and real `x ≥ 2`,
`|D₀(x) − L(1,χ).re·x^{1−β₀}/((1−β₀)(2−β₀))| ≤ C₂·x^{1/2−β₀}`,
`C₂ = 4·C_w = 136 + 48M + 48M·Z₀ + 144M/(1−β₀)`, `M = √q(1+log q)`. The real-scale kernel-Abel
identity (R6-1) reduces `D₀(x)` to `(1/x)[(x−T)A(T) + Σ_{t<T} A(t)]`, `T = ⌊x⌋`; the two-sided
per-`t` bound (R6-2) gives the `3C_w` error legs and the main-term Riemann sandwich
(`sum_rpow_sandwich`) with `L₁ ≤ 18M` (`LFunction_apply_one_norm_le`) gives the last `C_w`. -/
theorem unmoll_extraction_abs_real [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β₀ : ℝ}
    (hzero : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0) (hlo : 1 / 2 ≤ β₀) (hhi : β₀ < 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {x : ℝ} (hx : 2 ≤ x) :
    |dhD0 χ β₀ x
        - (DirichletCharacter.LFunction χ 1).re * x ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))|
      ≤ (136 + 48 * (Real.sqrt q * (1 + Real.log q))
          + 48 * (Real.sqrt q * (1 + Real.log q)) * Z₀
          + 144 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀)) * x ^ (1 / 2 - β₀) := by
  set M : ℝ := Real.sqrt q * (1 + Real.log q) with hMdef
  set L₁ : ℝ := (DirichletCharacter.LFunction χ 1).re with hL1def
  set Cw : ℝ := 34 + 12 * M + 12 * M * Z₀ + 36 * M / (1 - β₀) with hCwdef
  set T : ℕ := ⌊x⌋₊ with hTdef
  set main : ℝ := L₁ * x ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)) with hmaindef
  have hβ0 : 0 < β₀ := by linarith
  have hu : 0 < 1 - β₀ := by linarith
  have hu2 : 0 < 2 - β₀ := by linarith
  have hune : (1 - β₀) ≠ 0 := hu.ne'
  have hu2ne : (2 - β₀) ≠ 0 := hu2.ne'
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hZ0nn : 0 ≤ Z₀ := le_trans (norm_nonneg _)
    (hZ (β₀ : ℂ) (by rw [Complex.ofReal_re]; linarith) (by rw [Complex.ofReal_re]; linarith)
      (by rw [Complex.ofReal_im]; simp))
  have hCwnn : 0 ≤ Cw := by rw [hCwdef]; positivity
  have hne' : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hL1nn : 0 ≤ L₁ := by
    rw [hL1def]; exact le_of_lt ((Complex.lt_def.mp (LFunction_apply_one_pos hne' hsq)).1)
  have hT1 : 1 ≤ T := by rw [hTdef, Nat.le_floor_iff hx0.le]; exact_mod_cast hx1
  have hTx : (T : ℝ) ≤ x := by rw [hTdef]; exact Nat.floor_le hx0.le
  have hxT : x < (T : ℝ) + 1 := by rw [hTdef]; exact Nat.lt_floor_add_one x
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT1
  have hxc32 : (0 : ℝ) ≤ x ^ (3 / 2 - β₀) := Real.rpow_nonneg hx0.le _
  -- `L₁ ≤ 18M`
  have hL1_le : L₁ ≤ 18 * M := by
    have hnorm := LFunction_apply_one_norm_le χ hχ hq
    have hre : L₁ ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
      rw [hL1def]; exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
    have hlogq0 : (0 : ℝ) ≤ 1 + Real.log q := by linarith
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1.4 : ℝ) = Real.sqrt (1.4 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsq14 : (1.4 : ℝ) ≤ Real.sqrt q := le_trans hs2 (Real.sqrt_le_sqrt hq2)
    have h5e : 5 * Real.exp 1 ≤ 18 * Real.sqrt q := by nlinarith [Real.exp_one_lt_d9, hsq14]
    rw [hMdef]
    nlinarith [hre, hnorm, mul_le_mul_of_nonneg_right h5e hlogq0]
  -- R6-1 : the real-scale kernel-Abel identity
  have hAbel : dhD0 χ β₀ x = (1 / x) * ((x - (T : ℝ))
        * (∑ s ∈ Finset.Icc 1 T, dhA χ s * (s : ℝ) ^ (-β₀))
        + ∑ t ∈ Finset.Icc 1 (T - 1), ∑ s ∈ Finset.Icc 1 t, dhA χ s * (s : ℝ) ^ (-β₀)) := by
    have hk := kernel_abel_sum_real (fun s => dhA χ s * (s : ℝ) ^ (-β₀)) hx1
    rw [← hTdef] at hk; rw [dhD0, ← hTdef]; exact hk
  set ST : ℝ := ∑ s ∈ Finset.Icc 1 T, dhA χ s * (s : ℝ) ^ (-β₀) with hSTdef
  set SP : ℝ := ∑ t ∈ Finset.Icc 1 (T - 1), (t : ℝ) ^ (1 - β₀) with hSPdef
  set S : ℝ := (x - (T : ℝ)) * (T : ℝ) ^ (1 - β₀) + SP with hSdef
  set R : ℝ := (x - (T : ℝ)) * ST
      + ∑ t ∈ Finset.Icc 1 (T - 1), ∑ s ∈ Finset.Icc 1 t, dhA χ s * (s : ℝ) ^ (-β₀) with hRdef
  -- the per-`t` two-sided bound (R6-2)
  have hR2 : ∀ t : ℕ, 1 ≤ t →
      |(∑ s ∈ Finset.Icc 1 t, dhA χ s * (s : ℝ) ^ (-β₀)) - L₁ * (t : ℝ) ^ (1 - β₀) / (1 - β₀)|
        ≤ Cw * (t : ℝ) ^ (1 / 2 - β₀) := by
    intro t ht
    have h := dhAbel_inner_abs_le χ hχ hsq hq hzero hlo hhi hZ ht
    rw [← hMdef, ← hL1def, ← hCwdef] at h; exact h
  -- the exact main/error split of `R − x·main`
  have hxx : x * x ^ (1 - β₀) = x ^ (2 - β₀) := by
    nth_rewrite 1 [← Real.rpow_one x]; rw [← Real.rpow_add hx0]; congr 1; ring
  have hxmain : x * main = L₁ * x ^ (2 - β₀) / ((1 - β₀) * (2 - β₀)) := by
    rw [hmaindef, show x * (L₁ * x ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)))
      = L₁ * (x * x ^ (1 - β₀)) / ((1 - β₀) * (2 - β₀)) by ring, hxx]
  have hRsplit : R - x * main
      = (L₁ / (1 - β₀)) * (S - x ^ (2 - β₀) / (2 - β₀))
        + ((x - (T : ℝ)) * (ST - L₁ * (T : ℝ) ^ (1 - β₀) / (1 - β₀))
           + ∑ t ∈ Finset.Icc 1 (T - 1),
               ((∑ s ∈ Finset.Icc 1 t, dhA χ s * (s : ℝ) ^ (-β₀))
                 - L₁ * (t : ℝ) ^ (1 - β₀) / (1 - β₀))) := by
    have hEsum : (∑ t ∈ Finset.Icc 1 (T - 1),
          ((∑ s ∈ Finset.Icc 1 t, dhA χ s * (s : ℝ) ^ (-β₀))
            - L₁ * (t : ℝ) ^ (1 - β₀) / (1 - β₀)))
        = (∑ t ∈ Finset.Icc 1 (T - 1), ∑ s ∈ Finset.Icc 1 t, dhA χ s * (s : ℝ) ^ (-β₀))
          - (L₁ / (1 - β₀)) * SP := by
      rw [Finset.sum_sub_distrib]; congr 1
      rw [hSPdef, Finset.mul_sum]; exact Finset.sum_congr rfl (fun t _ => by ring)
    rw [hRdef, hxmain, hEsum, hSdef]; field_simp; ring
  -- bound the main defect `Bmain`
  have hSbound := sum_rpow_sandwich (c := 1 - β₀) (by linarith) (by linarith) hx hT1 hTx hxT
  rw [show 1 - β₀ + 1 = 2 - β₀ by ring, ← hSPdef, ← hSdef] at hSbound
  have hBmain : |(L₁ / (1 - β₀)) * (S - x ^ (2 - β₀) / (2 - β₀))|
      ≤ (L₁ / (1 - β₀)) * (2 * x ^ (1 - β₀)) := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hL1nn hu.le)]
    exact mul_le_mul_of_nonneg_left hSbound (div_nonneg hL1nn hu.le)
  -- bound the error `Berr`
  have hBerr : |(x - (T : ℝ)) * (ST - L₁ * (T : ℝ) ^ (1 - β₀) / (1 - β₀))
        + ∑ t ∈ Finset.Icc 1 (T - 1),
            ((∑ s ∈ Finset.Icc 1 t, dhA χ s * (s : ℝ) ^ (-β₀))
              - L₁ * (t : ℝ) ^ (1 - β₀) / (1 - β₀))|
      ≤ 3 * Cw * x ^ (3 / 2 - β₀) := by
    have hterm1 : |(x - (T : ℝ)) * (ST - L₁ * (T : ℝ) ^ (1 - β₀) / (1 - β₀))|
        ≤ Cw * x ^ (3 / 2 - β₀) := by
      rw [abs_mul, abs_of_nonneg (by linarith [hTx] : (0 : ℝ) ≤ x - (T : ℝ))]
      have hTle1 : (T : ℝ) ^ (1 / 2 - β₀) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT1) (by linarith)
      have h1x : (1 : ℝ) ≤ x ^ (3 / 2 - β₀) :=
        Real.one_le_rpow hx1 (by linarith)
      calc (x - (T : ℝ)) * |ST - L₁ * (T : ℝ) ^ (1 - β₀) / (1 - β₀)|
          ≤ 1 * (Cw * (T : ℝ) ^ (1 / 2 - β₀)) :=
            mul_le_mul (by linarith [hxT]) (hR2 T hT1) (abs_nonneg _) (by norm_num)
        _ ≤ Cw * x ^ (3 / 2 - β₀) := by
            rw [one_mul]; calc Cw * (T : ℝ) ^ (1 / 2 - β₀) ≤ Cw * 1 :=
                  mul_le_mul_of_nonneg_left hTle1 hCwnn
              _ ≤ Cw * x ^ (3 / 2 - β₀) := by rw [mul_one]; nlinarith [hCwnn, h1x]
    have hterm2 : |∑ t ∈ Finset.Icc 1 (T - 1),
          ((∑ s ∈ Finset.Icc 1 t, dhA χ s * (s : ℝ) ^ (-β₀))
            - L₁ * (t : ℝ) ^ (1 - β₀) / (1 - β₀))| ≤ 2 * Cw * x ^ (3 / 2 - β₀) := by
      calc |∑ t ∈ Finset.Icc 1 (T - 1),
              ((∑ s ∈ Finset.Icc 1 t, dhA χ s * (s : ℝ) ^ (-β₀))
                - L₁ * (t : ℝ) ^ (1 - β₀) / (1 - β₀))|
          ≤ ∑ t ∈ Finset.Icc 1 (T - 1), Cw * (t : ℝ) ^ (1 / 2 - β₀) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun t ht => ?_))
            rw [Finset.mem_Icc] at ht; exact hR2 t (by omega)
        _ = Cw * ∑ t ∈ Finset.Icc 1 (T - 1), (t : ℝ) ^ (1 / 2 - β₀) := by rw [Finset.mul_sum]
        _ ≤ Cw * (2 * x ^ (3 / 2 - β₀)) := by
            apply mul_le_mul_of_nonneg_left _ hCwnn
            have h := sum_rpow_neg_le (β := β₀ - 1 / 2) (by linarith) (by linarith) (T - 1)
            rw [show -(β₀ - 1 / 2) = 1 / 2 - β₀ by ring,
              show 1 - (β₀ - 1 / 2) = 3 / 2 - β₀ by ring] at h
            have hym1 : ((T - 1 : ℕ) : ℝ) ≤ x := le_trans (by
              rw [Nat.cast_sub hT1]; push_cast; linarith) hTx
            have hbase : ((T - 1 : ℕ) : ℝ) ^ (3 / 2 - β₀) ≤ x ^ (3 / 2 - β₀) :=
              Real.rpow_le_rpow (by positivity) hym1 (by linarith)
            have h32 : (0 : ℝ) < 3 / 2 - β₀ := by linarith
            calc ∑ t ∈ Finset.Icc 1 (T - 1), (t : ℝ) ^ (1 / 2 - β₀)
                ≤ ((T - 1 : ℕ) : ℝ) ^ (3 / 2 - β₀) / (3 / 2 - β₀) := h
              _ ≤ x ^ (3 / 2 - β₀) / (3 / 2 - β₀) :=
                  (div_le_div_iff_of_pos_right h32).mpr hbase
              _ ≤ 2 * x ^ (3 / 2 - β₀) := by
                  rw [div_le_iff₀ h32]; nlinarith [hxc32]
        _ = 2 * Cw * x ^ (3 / 2 - β₀) := by ring
    calc |(x - (T : ℝ)) * (ST - L₁ * (T : ℝ) ^ (1 - β₀) / (1 - β₀))
            + ∑ t ∈ Finset.Icc 1 (T - 1),
                ((∑ s ∈ Finset.Icc 1 t, dhA χ s * (s : ℝ) ^ (-β₀))
                  - L₁ * (t : ℝ) ^ (1 - β₀) / (1 - β₀))|
        ≤ |(x - (T : ℝ)) * (ST - L₁ * (T : ℝ) ^ (1 - β₀) / (1 - β₀))|
          + |∑ t ∈ Finset.Icc 1 (T - 1),
              ((∑ s ∈ Finset.Icc 1 t, dhA χ s * (s : ℝ) ^ (-β₀))
                - L₁ * (t : ℝ) ^ (1 - β₀) / (1 - β₀))| := abs_add_le _ _
      _ ≤ Cw * x ^ (3 / 2 - β₀) + 2 * Cw * x ^ (3 / 2 - β₀) := add_le_add hterm1 hterm2
      _ = 3 * Cw * x ^ (3 / 2 - β₀) := by ring
  -- combine
  have hlast : (L₁ / (1 - β₀)) * (2 * x ^ (1 - β₀)) ≤ Cw * x ^ (3 / 2 - β₀) := by
    have hx13 : x ^ (1 - β₀) ≤ x ^ (3 / 2 - β₀) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hCwmul : Cw * (1 - β₀) = (34 + 12 * M + 12 * M * Z₀) * (1 - β₀) + 36 * M := by
      rw [hCwdef]; field_simp
    have hprod : (0 : ℝ) ≤ (34 + 12 * M + 12 * M * Z₀) * (1 - β₀) :=
      mul_nonneg (by nlinarith [hMnn, mul_nonneg hMnn hZ0nn]) hu.le
    have h2L1 : 2 * L₁ ≤ Cw * (1 - β₀) := by rw [hCwmul]; linarith [hL1_le, hprod]
    have hcoef : 2 * L₁ / (1 - β₀) ≤ Cw := by rw [div_le_iff₀ hu]; linarith [h2L1]
    have hnn2 : (0 : ℝ) ≤ 2 * L₁ / (1 - β₀) := div_nonneg (by linarith [hL1nn]) hu.le
    calc (L₁ / (1 - β₀)) * (2 * x ^ (1 - β₀)) = (2 * L₁ / (1 - β₀)) * x ^ (1 - β₀) := by ring
      _ ≤ (2 * L₁ / (1 - β₀)) * x ^ (3 / 2 - β₀) := mul_le_mul_of_nonneg_left hx13 hnn2
      _ ≤ Cw * x ^ (3 / 2 - β₀) := mul_le_mul_of_nonneg_right hcoef hxc32
  have hRbound : |R - x * main| ≤ 4 * Cw * x ^ (3 / 2 - β₀) := by
    rw [hRsplit]
    calc |(L₁ / (1 - β₀)) * (S - x ^ (2 - β₀) / (2 - β₀))
            + ((x - (T : ℝ)) * (ST - L₁ * (T : ℝ) ^ (1 - β₀) / (1 - β₀))
               + ∑ t ∈ Finset.Icc 1 (T - 1),
                   ((∑ s ∈ Finset.Icc 1 t, dhA χ s * (s : ℝ) ^ (-β₀))
                     - L₁ * (t : ℝ) ^ (1 - β₀) / (1 - β₀)))|
        ≤ |(L₁ / (1 - β₀)) * (S - x ^ (2 - β₀) / (2 - β₀))|
          + |(x - (T : ℝ)) * (ST - L₁ * (T : ℝ) ^ (1 - β₀) / (1 - β₀))
             + ∑ t ∈ Finset.Icc 1 (T - 1),
                 ((∑ s ∈ Finset.Icc 1 t, dhA χ s * (s : ℝ) ^ (-β₀))
                   - L₁ * (t : ℝ) ^ (1 - β₀) / (1 - β₀))| := abs_add_le _ _
      _ ≤ (L₁ / (1 - β₀)) * (2 * x ^ (1 - β₀)) + 3 * Cw * x ^ (3 / 2 - β₀) :=
          add_le_add hBmain hBerr
      _ ≤ 4 * Cw * x ^ (3 / 2 - β₀) := by linarith [hlast]
  have heq : 1 / x * R - main = (R - x * main) / x := by field_simp
  have hfinal : |dhD0 χ β₀ x - main| = |R - x * main| / x := by
    rw [hAbel, heq, abs_div, abs_of_pos hx0]
  rw [hfinal, div_le_iff₀ hx0]
  have hxpow : x ^ (1 / 2 - β₀) * x = x ^ (3 / 2 - β₀) := by
    nth_rewrite 2 [← Real.rpow_one x]; rw [← Real.rpow_add hx0]; congr 1; ring
  calc |R - x * main| ≤ 4 * Cw * x ^ (3 / 2 - β₀) := hRbound
    _ = (136 + 48 * M + 48 * M * Z₀ + 144 * M / (1 - β₀)) * x ^ (1 / 2 - β₀) * x := by
        rw [← hxpow, hCwdef]; ring

/-! ## §4 — R6-4 : the EXACT reduction to the template -/

/-- **Weighted `inner_cop_swap`.** The coprime-restricted divisor swap carrying an arbitrary
per-`t` weight `w`: `Σ_{t≤y} (Σ_{d∣t,(d,κ)=1} χℝ(d))·w(t) = Σ_{d≤y,(d,κ)=1} χℝ(d)·Σ_{s≤y/d} w(d·s)`.
Generalizes `inner_cop_swap` (`w ≡ ⌊y/d⌋` counts multiples) to a `t`-dependent weight
(`sum_dvd_reindex` on the multiples). -/
lemma inner_cop_swap_wt (χ : DirichletCharacter ℂ q) (w : ℕ → ℝ) (κ y : ℕ) :
    ∑ t ∈ Finset.Icc 1 y,
        (∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d κ), chiRe χ d) * w t
      = ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Nat.Coprime d κ),
          chiRe χ d * ∑ s ∈ Finset.Icc 1 (y / d), w (d * s) := by
  have hstep : ∀ t ∈ Finset.Icc 1 y,
      (∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d κ), chiRe χ d) * w t
        = ∑ d ∈ Finset.Icc 1 y, (if d ∣ t ∧ Nat.Coprime d κ then chiRe χ d * w t else 0) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have hset : t.divisors.filter (fun d => Nat.Coprime d κ)
        = (Finset.Icc 1 y).filter (fun d => d ∣ t ∧ Nat.Coprime d κ) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hdvd, _⟩, hcop⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) ht.2⟩, hdvd, hcop⟩
      · rintro ⟨⟨hd1, _⟩, hdvd, hcop⟩
        exact ⟨⟨hdvd, by omega⟩, hcop⟩
    rw [hset, Finset.sum_filter, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun d _ => by split_ifs <;> ring)
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  by_cases hcop : Nat.Coprime d κ
  · rw [if_pos hcop,
        Finset.sum_congr rfl (fun t _ => if_congr (and_iff_left hcop) rfl rfl),
        ← Finset.sum_filter, ← Finset.mul_sum, sum_dvd_reindex hd.1 w]
  · rw [if_neg hcop]
    exact Finset.sum_eq_zero (fun t _ => if_neg (fun h => hcop h.2))

/-- **Weighted character-count fold.** For any per-value weight `h`,
`Σ_{N≤L} dhA χ N·h(N) = Σ_{e≤L} χℝ(e)·Σ_{s≤L/e} h(e·s)` — the `dhA = χℝ ∗ 1` divisor swap
(`N = e·s`). Weighted generalization of `dhA_mass_eq_char_count`; consumed in REVERSE to
reconstitute the template `D₀` after the coprime unfold. -/
lemma weighted_char_count (χ : DirichletCharacter ℂ q) (h : ℕ → ℝ) (L : ℕ) :
    ∑ N ∈ Finset.Icc 1 L, dhA χ N * h N
      = ∑ e ∈ Finset.Icc 1 L, chiRe χ e * ∑ s ∈ Finset.Icc 1 (L / e), h (e * s) := by
  have hstep : ∀ N ∈ Finset.Icc 1 L, dhA χ N * h N
      = ∑ e ∈ Finset.Icc 1 L, (if e ∣ N then chiRe χ e * h N else 0) := by
    intro N hN
    rw [Finset.mem_Icc] at hN
    have hset : N.divisors = (Finset.Icc 1 L).filter (fun e => e ∣ N) := by
      ext e
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) hN.2⟩, hdvd⟩
      · rintro ⟨_, hdvd⟩; exact ⟨hdvd, by omega⟩
    rw [dhA, hset, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Finset.mem_Icc] at he
  rw [← Finset.sum_filter, ← Finset.mul_sum, sum_dvd_reindex he.1 h]

/-- **R6-4 per-`g` core.** For `g ∣ m`, the `g`-leg of the reduction: the `κ = m/g`-coprime inner
sum against the kernel weight collapses onto the template `D₀` at the rescaled real scales
`Y/(m·k)`. Route: weighted `inner_cop_swap` + coprime Möbius unfold + weighted char-count fold
(reconstituting `dhA`) + the kernel factorization `(m·k·N)^{−β₀} = (m·k)^{−β₀}·N^{−β₀}`,
`1 − m·k·N/Y = 1 − N/(Y/(m·k))`. -/
lemma dhA_kernel_reduction_inner (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {β₀ : ℝ}
    {m : ℕ} (hm : 1 ≤ m) {g : ℕ} (hg : g ∈ m.divisors) (Y : ℕ) :
    ∑ t ∈ Finset.Icc 1 (Y / m),
        (∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d (m / g)), chiRe χ d)
          * (((m * t : ℕ) : ℝ) ^ (-β₀) * (1 - ((m * t : ℕ) : ℝ) / (Y : ℝ)))
      = ∑ k ∈ (m / g).divisors,
          (moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
            * dhD0 χ β₀ ((Y : ℝ) / ((m * k : ℕ) : ℝ)) := by
  have hg1 : 1 ≤ g := Nat.pos_of_mem_divisors hg
  have hgm : g ∣ m := Nat.dvd_of_mem_divisors hg
  have hκ1 : 1 ≤ m / g := (Nat.one_le_div_iff hg1).mpr (Nat.le_of_dvd (by omega) hgm)
  rw [inner_cop_swap_wt χ
        (fun t => ((m * t : ℕ) : ℝ) ^ (-β₀) * (1 - ((m * t : ℕ) : ℝ) / (Y : ℝ))) (m / g) (Y / m),
      sum_coprime_eq_moebius_multiples (m / g) (Y / m) hκ1
        (fun d => chiRe χ d * ∑ s ∈ Finset.Icc 1 (Y / m / d),
          ((m * (d * s) : ℕ) : ℝ) ^ (-β₀) * (1 - ((m * (d * s) : ℕ) : ℝ) / (Y : ℝ)))]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk1 : 1 ≤ k := Nat.pos_of_mem_divisors hk
  have hfold : (∑ e ∈ Finset.Icc 1 (Y / m / k),
        chiRe χ (k * e) * ∑ s ∈ Finset.Icc 1 (Y / m / (k * e)),
          ((m * (k * e * s) : ℕ) : ℝ) ^ (-β₀) * (1 - ((m * (k * e * s) : ℕ) : ℝ) / (Y : ℝ)))
      = chiRe χ k * ∑ N ∈ Finset.Icc 1 (Y / m / k), dhA χ N
          * (((m * (k * N) : ℕ) : ℝ) ^ (-β₀) * (1 - ((m * (k * N) : ℕ) : ℝ) / (Y : ℝ))) := by
    rw [weighted_char_count χ (fun N => ((m * (k * N) : ℕ) : ℝ) ^ (-β₀)
          * (1 - ((m * (k * N) : ℕ) : ℝ) / (Y : ℝ))) (Y / m / k), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [chiRe_mul χ hsq k e, ← Nat.div_div_eq_div_mul, mul_assoc]
    congr 1
    congr 1
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [mul_assoc k e s]
  have hval : (∑ N ∈ Finset.Icc 1 (Y / m / k), dhA χ N
        * (((m * (k * N) : ℕ) : ℝ) ^ (-β₀) * (1 - ((m * (k * N) : ℕ) : ℝ) / (Y : ℝ))))
      = ((m * k : ℕ) : ℝ) ^ (-β₀) * dhD0 χ β₀ ((Y : ℝ) / ((m * k : ℕ) : ℝ)) := by
    have hfloor : ⌊(Y : ℝ) / ((m * k : ℕ) : ℝ)⌋₊ = Y / (m * k) := Nat.floor_div_eq_div Y (m * k)
    have hLeq : Y / m / k = Y / (m * k) := Nat.div_div_eq_div_mul Y m k
    rw [dhD0, hfloor, hLeq, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun N _ => ?_)
    have hcast : ((m * (k * N) : ℕ) : ℝ) = ((m * k : ℕ) : ℝ) * (N : ℝ) := by
      rw [show m * (k * N) = m * k * N by ring]; push_cast; ring
    rw [hcast, Real.mul_rpow (by positivity) (by positivity)]
    have hmk0 : (0 : ℝ) < ((m * k : ℕ) : ℝ) := by
      have : 1 ≤ m * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    rw [show ((m * k : ℕ) : ℝ) * (N : ℝ) / (Y : ℝ)
          = (N : ℝ) / ((Y : ℝ) / ((m * k : ℕ) : ℝ)) by
        rw [div_div_eq_mul_div]; ring]
    ring
  rw [hfold, hval]; ring

/-- **R6-4 (`dhA_kernel_reduction`) — THE EXACT REDUCTION.** For every `m ≥ 1` (certified
off-squarefree), the per-`m` kernel-restricted detector sum reduces EXACTLY (an identity, no
estimate) to the `m = 1` template at the rescaled real scales `Y/(m·k)`:
`Σ_{n≤Y, m∣n} dhA χ n·n^{−β₀}·(1 − n/Y)
   = Σ_{g∣m} χℝ(g)·Σ_{k∣(m/g)} μ(k)·χℝ(k)·(m·k)^{−β₀}·D₀(Y/(m·k))`.
No third convolution materializes: only the 2-fold `χℝ ∗ 1` template at `3^{ω(m)}` scales. Route:
`n = m·t` reindex (`sum_dvd_reindex`) + the `(†)` divisor split (`dhA_mul_eq_sum`) + the per-`g`
core (`dhA_kernel_reduction_inner`). -/
theorem dhA_kernel_reduction (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {β₀ : ℝ}
    {m : ℕ} (hm : 1 ≤ m) (Y : ℕ) :
    ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n),
        dhA χ n * (n : ℝ) ^ (-β₀) * (1 - (n : ℝ) / (Y : ℝ))
      = ∑ g ∈ m.divisors, chiRe χ g * ∑ k ∈ (m / g).divisors,
          (moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
            * dhD0 χ β₀ ((Y : ℝ) / ((m * k : ℕ) : ℝ)) := by
  rw [sum_dvd_reindex hm (fun n => dhA χ n * (n : ℝ) ^ (-β₀) * (1 - (n : ℝ) / (Y : ℝ)))]
  have hstep : ∀ t ∈ Finset.Icc 1 (Y / m),
      dhA χ (m * t) * ((m * t : ℕ) : ℝ) ^ (-β₀) * (1 - ((m * t : ℕ) : ℝ) / (Y : ℝ))
        = ∑ g ∈ m.divisors, chiRe χ g
            * ((∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d (m / g)), chiRe χ d)
                * (((m * t : ℕ) : ℝ) ^ (-β₀) * (1 - ((m * t : ℕ) : ℝ) / (Y : ℝ)))) := by
    intro t _
    rw [dhA_mul_eq_sum χ hsq hm t, mul_assoc, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun g _ => by ring)
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [← Finset.mul_sum, dhA_kernel_reduction_inner χ hsq hm hg Y]

/-! ## §5–7 support : `selWeight`/`gcW` vanishing -/

/-- `selWeight` is squarefree-supported. -/
lemma selWeight_ne_zero_squarefree (χ : DirichletCharacter ℂ q) (z : ℕ) {d : ℕ}
    (h : selWeight χ z d ≠ 0) : Squarefree d := by
  by_contra hsf
  exact h (by rw [selWeight, if_neg (fun hc => hsf hc.2)])

/-- `selWeight χ z d = 0` for `d > z`. -/
lemma selWeight_ne_zero_le (χ : DirichletCharacter ℂ q) (z : ℕ) {d : ℕ}
    (h : selWeight χ z d ≠ 0) : d ≤ z := by
  by_contra hc
  exact h (by rw [selWeight, if_neg (fun hg => hc hg.1)])

/-- **`gcW(selWeight)` vanishes above `z²`.** Any nonzero `lcm`-pair `(d1,d2)` for `m` forces
`d1, d2 ≤ z` squarefree, whence `m = lcm(d1,d2) ≤ d1·d2 ≤ z²`. The `2z⁴ ≤ Y` guard's structural
half (`m ≤ z²` on the `gcW`-support gives the template scale `Y/(m·k) ≥ 2`). -/
lemma gcW_selWeight_eq_zero_of_gt_sq (χ : DirichletCharacter ℂ q) {z m : ℕ} (hm : z ^ 2 < m) :
    gcW (selWeight χ z) m = 0 := by
  rw [gcW_eq]
  refine Finset.sum_eq_zero (fun d1 _ => Finset.sum_eq_zero (fun d2 _ => ?_))
  split_ifs with heq
  · by_contra hne
    have h1 : selWeight χ z d1 ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have h2 : selWeight χ z d2 ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hd1z : d1 ≤ z := selWeight_ne_zero_le χ z h1
    have hd2z : d2 ≤ z := selWeight_ne_zero_le χ z h2
    have hd1n : d1 ≠ 0 := (selWeight_ne_zero_squarefree χ z h1).ne_zero
    have hd2n : d2 ≠ 0 := (selWeight_ne_zero_squarefree χ z h2).ne_zero
    have hlcm : Nat.lcm d1 d2 ≤ d1 * d2 :=
      Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega))
        (Nat.lcm_dvd (Nat.dvd_mul_right d1 d2) (Nat.dvd_mul_left d2 d1))
    have hmle : m ≤ z ^ 2 := by
      rw [heq]
      calc Nat.lcm d1 d2 ≤ d1 * d2 := hlcm
        _ ≤ z * z := Nat.mul_le_mul hd1z hd2z
        _ = z ^ 2 := (sq z).symm
    omega
  · rfl

/-- Kernel rescaling (main): `a^{−β₀}·(Y/a)^{1−β₀} = Y^{1−β₀}/a`. -/
lemma dhD0_scale_main {β₀ : ℝ} {a Y : ℕ} (ha : 1 ≤ a) (hY : 1 ≤ Y) :
    ((a : ℕ) : ℝ) ^ (-β₀) * ((Y : ℝ) / ((a : ℕ) : ℝ)) ^ (1 - β₀)
      = (Y : ℝ) ^ (1 - β₀) / ((a : ℕ) : ℝ) := by
  have ha0 : (0 : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast ha
  have hY0 : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  rw [Real.div_rpow hY0.le ha0.le,
      show ((a : ℕ) : ℝ) ^ (-β₀) * ((Y : ℝ) ^ (1 - β₀) / ((a : ℕ) : ℝ) ^ (1 - β₀))
        = (Y : ℝ) ^ (1 - β₀) * (((a : ℕ) : ℝ) ^ (-β₀) / ((a : ℕ) : ℝ) ^ (1 - β₀)) by ring,
      ← Real.rpow_sub ha0, show -β₀ - (1 - β₀) = -1 by ring, Real.rpow_neg_one, div_eq_mul_inv]

/-- Kernel rescaling (error): `a^{−β₀}·(Y/a)^{1/2−β₀} = Y^{1/2−β₀}·a^{−1/2}`. -/
lemma dhD0_scale_err {β₀ : ℝ} {a Y : ℕ} (ha : 1 ≤ a) (hY : 1 ≤ Y) :
    ((a : ℕ) : ℝ) ^ (-β₀) * ((Y : ℝ) / ((a : ℕ) : ℝ)) ^ (1 / 2 - β₀)
      = (Y : ℝ) ^ (1 / 2 - β₀) * ((a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have ha0 : (0 : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast ha
  have hY0 : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  rw [Real.div_rpow hY0.le ha0.le,
      show ((a : ℕ) : ℝ) ^ (-β₀) * ((Y : ℝ) ^ (1 / 2 - β₀) / ((a : ℕ) : ℝ) ^ (1 / 2 - β₀))
        = (Y : ℝ) ^ (1 / 2 - β₀) * (((a : ℕ) : ℝ) ^ (-β₀) / ((a : ℕ) : ℝ) ^ (1 / 2 - β₀)) by ring,
      ← Real.rpow_sub ha0, show -β₀ - (1 / 2 - β₀) = -(1 / 2 : ℝ) by ring]

/-! ## §5 — R6-5 : the signed collection into `selHmul` -/

/-- **R6-5 (`selHmul_collection`).** For squarefree `m`,
`Σ_{g∣m} χℝ(g)·Σ_{k∣(m/g)} μ(k)·χℝ(k)/k = selHmul χ m`. Via the multiplicative `prodPrimeFactors`
algebra: `F = χℝ ∗ (μ·χℝ/id)` is multiplicative with `F(p) = 1 + χℝ(p) − χℝ(p)/p = selH p`. -/
lemma selHmul_collection (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ}
    (hmsf : Squarefree m) :
    ∑ g ∈ m.divisors, chiRe χ g * ∑ k ∈ (m / g).divisors, (moebius k : ℝ) * chiRe χ k / (k : ℝ)
      = selHmul χ m := by
  have hfAmult := chiReArith_mult χ hsq
  set B : ℕ → ℝ := fun p => 1 - chiRe χ p / (p : ℝ) with hBdef
  have hfBmult : (ArithmeticFunction.prodPrimeFactors B).IsMultiplicative :=
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors B
  have hprodterm : ∀ {a : ℕ}, Squarefree a →
      ∏ p ∈ a.primeFactors, (-(chiRe χ p / (p : ℝ))) = (moebius a : ℝ) * chiRe χ a / (a : ℝ) := by
    intro a hasf
    have ha0 : a ≠ 0 := hasf.ne_zero
    have hmu : (moebius a : ℝ) = (-1 : ℝ) ^ a.primeFactors.card := by
      have hnodup : a.primeFactorsList.Nodup :=
        (Nat.squarefree_iff_nodup_primeFactorsList ha0).mp hasf
      have hcard : ArithmeticFunction.cardFactors a = a.primeFactors.card := by
        rw [ArithmeticFunction.cardFactors_apply, ← Nat.toFinset_factors,
          List.toFinset_card_of_nodup hnodup]
      rw [ArithmeticFunction.moebius_apply_of_squarefree hasf, hcard]; push_cast; ring
    have hchi : ∏ p ∈ a.primeFactors, chiRe χ p = chiRe χ a := by
      have hpf := hfAmult.prod_primeFactors hasf
      calc ∏ p ∈ a.primeFactors, chiRe χ p
          = ∏ p ∈ a.primeFactors, chiReArith χ p := by
            refine Finset.prod_congr rfl (fun p hp => ?_)
            rw [chiReArith_apply, if_neg (Nat.prime_of_mem_primeFactors hp).ne_zero]
        _ = chiReArith χ a := hpf
        _ = chiRe χ a := by rw [chiReArith_apply, if_neg ha0]
    have ha_eq : (a : ℝ) = ∏ p ∈ a.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hasf]
    calc ∏ p ∈ a.primeFactors, (-(chiRe χ p / (p : ℝ)))
        = ∏ p ∈ a.primeFactors, ((-1 : ℝ) * chiRe χ p * (p : ℝ)⁻¹) := by
          refine Finset.prod_congr rfl (fun p _ => ?_); rw [div_eq_mul_inv]; ring
      _ = (∏ p ∈ a.primeFactors, (-1 : ℝ)) * (∏ p ∈ a.primeFactors, chiRe χ p)
            * (∏ p ∈ a.primeFactors, (p : ℝ)⁻¹) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      _ = (-1 : ℝ) ^ a.primeFactors.card * chiRe χ a * (a : ℝ)⁻¹ := by
          rw [Finset.prod_const, hchi, Finset.prod_inv_distrib, ← ha_eq]
      _ = (moebius a : ℝ) * chiRe χ a / (a : ℝ) := by rw [hmu]; ring
  have hinner : ∀ {j : ℕ}, Squarefree j →
      (∑ k ∈ j.divisors, (moebius k : ℝ) * chiRe χ k / (k : ℝ))
        = ArithmeticFunction.prodPrimeFactors B j := by
    intro j hjsf
    rw [ArithmeticFunction.prodPrimeFactors_apply hjsf.ne_zero]
    have hdiv := sum_divisors_prod_primeFactors (f := fun p => -(chiRe χ p / (p : ℝ))) hjsf
    have hBeq : ∏ p ∈ j.primeFactors, B p
        = ∏ p ∈ j.primeFactors, (-(chiRe χ p / (p : ℝ)) + 1) := by
      refine Finset.prod_congr rfl (fun p _ => ?_); simp only [hBdef]; ring
    rw [hBeq, hdiv]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    exact (hprodterm (hjsf.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))).symm
  have hstep : ∀ g ∈ m.divisors,
      chiRe χ g * (∑ k ∈ (m / g).divisors, (moebius k : ℝ) * chiRe χ k / (k : ℝ))
        = chiReArith χ g * ArithmeticFunction.prodPrimeFactors B (m / g) := by
    intro g hg
    have hgm : g ∣ m := Nat.dvd_of_mem_divisors hg
    have hmgsf : Squarefree (m / g) := hmsf.squarefree_of_dvd (Nat.div_dvd_of_dvd hgm)
    rw [hinner hmgsf, chiReArith_apply, if_neg (Nat.pos_of_mem_divisors hg).ne']
  rw [Finset.sum_congr rfl hstep,
      ← Nat.sum_divisorsAntidiagonal
        (fun d e => chiReArith χ d * ArithmeticFunction.prodPrimeFactors B e),
      ← ArithmeticFunction.mul_apply,
      ← ArithmeticFunction.IsMultiplicative.prodPrimeFactors_add_of_squarefree hfAmult hfBmult hmsf,
      ArithmeticFunction.prodPrimeFactors_apply hmsf.ne_zero]
  unfold selHmul
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [ArithmeticFunction.add_apply, chiReArith_apply, if_neg hpp.ne_zero,
      ArithmeticFunction.prodPrimeFactors_apply hpp.ne_zero, hpp.primeFactors,
      Finset.prod_singleton]
  change chiRe χ p + (1 - chiRe χ p / (p : ℝ)) = 1 + chiRe χ p - chiRe χ p / (p : ℝ)
  ring

/-! ## §7 — R6-7 : the SIGNED main-term collection into `selMainTerm` -/

/-- **R6-7 (`sum_gcW_selNu_eq_selMainTerm`).** The signed main-term collection: for `z² ≤ Y`,
`Σ_{m≤Y} gcW(selWeight χ z) m · selNu χ m = selMainTerm χ z` (`= 1/H(z)` by `selberg_opt_eq`). -/
lemma sum_gcW_selNu_eq_selMainTerm (χ : DirichletCharacter ℂ q) (_hsq : χ ^ 2 = 1) {z Y : ℕ}
    (_hz : 1 ≤ z) (hzY : z ^ 2 ≤ Y) :
    ∑ m ∈ Finset.Icc 1 Y, gcW (selWeight χ z) m * selNu χ m = selMainTerm χ z := by
  classical
  set θ : ℕ → ℝ := selWeight χ z with hθ
  set Sz : Finset ℕ := (Finset.Icc 1 z).filter Squarefree with hSz
  have hguard : ∀ d, θ d ≠ 0 → d ≤ z ∧ Squarefree d := by
    intro d hd; by_contra h; exact hd (by rw [hθ, selWeight, if_neg h])
  have hmemSz : ∀ d, θ d ≠ 0 → d ∈ Sz := by
    intro d hd
    obtain ⟨hdz, hdsf⟩ := hguard d hd
    rw [hSz, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hdsf.ne_zero, hdz⟩, hdsf⟩
  have hzero_of_not : ∀ d, d ∉ Sz → θ d = 0 := by
    intro d hd; by_contra h; exact hd (hmemSz d h)
  have hSz_bd : ∀ d ∈ Sz, 1 ≤ d ∧ d ≤ z := by
    intro d hd; rw [hSz, Finset.mem_filter, Finset.mem_Icc] at hd; exact hd.1
  have claim : ∀ m ∈ Finset.Icc 1 Y,
      (∑ d1 ∈ m.divisors, ∑ d2 ∈ m.divisors,
          if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0)
        = ∑ d1 ∈ Sz, ∑ d2 ∈ Sz, if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0 := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : m ≠ 0 := by omega
    set Szm : Finset ℕ := Sz.filter (fun d => d ∣ m) with hSzm
    have hGz_dvd1 : ∀ d1 d2, ¬ d1 ∣ m →
        (if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0) = 0 := by
      intro d1 d2 h; rw [if_neg]; intro heq; exact h (heq ▸ Nat.dvd_lcm_left d1 d2)
    have hGz_dvd2 : ∀ d1 d2, ¬ d2 ∣ m →
        (if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0) = 0 := by
      intro d1 d2 h; rw [if_neg]; intro heq; exact h (heq ▸ Nat.dvd_lcm_right d1 d2)
    have hGz_θ1 : ∀ d1 d2, θ d1 = 0 →
        (if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0) = 0 := by
      intro d1 d2 h; split_ifs <;> simp [h]
    have hGz_θ2 : ∀ d1 d2, θ d2 = 0 →
        (if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0) = 0 := by
      intro d1 d2 h; split_ifs <;> simp [h]
    have hSzm_div : Szm ⊆ m.divisors := by
      intro d hd; rw [hSzm, Finset.mem_filter] at hd
      rw [Nat.mem_divisors]; exact ⟨hd.2, hm0⟩
    have hSzm_Sz : Szm ⊆ Sz := Finset.filter_subset _ _
    have hinner1 : ∀ d1 ∈ m.divisors,
        (∑ d2 ∈ m.divisors, if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0)
          = ∑ d2 ∈ Szm, if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0 := by
      intro d1 _
      refine (Finset.sum_subset hSzm_div (fun d2 hd2 hd2' => ?_)).symm
      refine hGz_θ2 d1 d2 (hzero_of_not d2 (fun hd2Sz => hd2' ?_))
      rw [hSzm, Finset.mem_filter]; exact ⟨hd2Sz, (Nat.mem_divisors.mp hd2).1⟩
    have hD1 : (∑ d1 ∈ m.divisors, ∑ d2 ∈ m.divisors,
          if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0)
        = ∑ d1 ∈ Szm, ∑ d2 ∈ Szm, if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0 := by
      rw [Finset.sum_congr rfl hinner1]
      refine (Finset.sum_subset hSzm_div (fun d1 hd1 hd1' => ?_)).symm
      refine Finset.sum_eq_zero (fun d2 _ => hGz_θ1 d1 d2
        (hzero_of_not d1 (fun hd1Sz => hd1' ?_)))
      rw [hSzm, Finset.mem_filter]; exact ⟨hd1Sz, (Nat.mem_divisors.mp hd1).1⟩
    have hinner2 : ∀ d1 ∈ Sz,
        (∑ d2 ∈ Sz, if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0)
          = ∑ d2 ∈ Szm, if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0 := by
      intro d1 _
      refine (Finset.sum_subset hSzm_Sz (fun d2 hd2 hd2' => ?_)).symm
      refine hGz_dvd2 d1 d2 (fun hd2m => hd2' ?_)
      rw [hSzm, Finset.mem_filter]; exact ⟨hd2, hd2m⟩
    have hD2 : (∑ d1 ∈ Sz, ∑ d2 ∈ Sz, if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0)
        = ∑ d1 ∈ Szm, ∑ d2 ∈ Szm, if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0 := by
      rw [Finset.sum_congr rfl hinner2]
      refine (Finset.sum_subset hSzm_Sz (fun d1 hd1 hd1' => ?_)).symm
      refine Finset.sum_eq_zero (fun d2 _ => hGz_dvd1 d1 d2 (fun hd1m => hd1' ?_))
      rw [hSzm, Finset.mem_filter]; exact ⟨hd1, hd1m⟩
    rw [hD1, hD2]
  have hLHS : ∀ m ∈ Finset.Icc 1 Y, gcW θ m * selNu χ m
      = ∑ d1 ∈ Sz, ∑ d2 ∈ Sz,
          (if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0) * selNu χ m := by
    intro m hm
    rw [gcW_eq, claim m hm, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun d1 _ => Finset.sum_mul _ _ _)
  rw [Finset.sum_congr rfl hLHS, Finset.sum_comm, selMainTerm, ← hSz]
  refine Finset.sum_congr rfl (fun d1 hd1 => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d2 hd2 => ?_)
  have hlcm_mem : Nat.lcm d1 d2 ∈ Finset.Icc 1 Y := by
    obtain ⟨hd11, hd1z⟩ := hSz_bd d1 hd1
    obtain ⟨hd21, hd2z⟩ := hSz_bd d2 hd2
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
    · calc Nat.lcm d1 d2 ≤ d1 * d2 := Nat.le_of_dvd (by positivity) (Nat.lcm_dvd_mul d1 d2)
        _ ≤ z * z := Nat.mul_le_mul hd1z hd2z
        _ = z ^ 2 := (sq z).symm
        _ ≤ Y := hzY
  have hcollapse : ∀ m, (if m = Nat.lcm d1 d2 then θ d1 * θ d2 else 0) * selNu χ m
      = if m = Nat.lcm d1 d2 then θ d1 * θ d2 * selNu χ m else 0 := by
    intro m; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun m _ => hcollapse m),
    Finset.sum_ite_eq' (Finset.Icc 1 Y) (Nat.lcm d1 d2) (fun m => θ d1 * θ d2 * selNu χ m),
    if_pos hlcm_mem, hθ]

/-! ## §6 — R6-6 : the collection moment -/

/-- `ω m = m.primeFactors.card`. -/
lemma omega_eq_primeFactors_card (m : ℕ) : ω m = m.primeFactors.card := by
  rw [cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

/-- Pair-count: for squarefree `m`, `Σ_{g∣m} σ₀(m/g) = 3^{ω m}`. -/
lemma paircount (m : ℕ) (hmsf : Squarefree m) :
    ∑ g ∈ m.divisors, ((m / g).divisors.card : ℝ) = (3 : ℝ) ^ (m.primeFactors.card) := by
  rw [Nat.sum_div_divisors m (fun a => ((a.divisors.card : ℝ)))]
  have hcard : ∀ a ∈ m.divisors, ((a.divisors.card : ℝ)) = (2 : ℝ) ^ (a.primeFactors.card) := by
    intro a ha
    have hasf : Squarefree a := hmsf.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha)
    rw [sqfree_card_divisors hasf]; push_cast; ring
  rw [Finset.sum_congr rfl hcard]
  have hprod := sum_divisors_prod_primeFactors (f := fun _ => (2 : ℝ)) hmsf
  have h2 : ∏ p ∈ m.primeFactors, ((2 : ℝ) + 1) = (3 : ℝ) ^ (m.primeFactors.card) := by
    rw [show ((2 : ℝ) + 1) = 3 by norm_num, Finset.prod_const]
  rw [← h2, hprod]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.prod_const]

/-- Per-`m` pair-kernel bound: for squarefree `m`,
`Σ_{g∣m} Σ_{k∣(m/g)} (m·k)^{−1/2} ≤ m^{−1/2}·3^{ω m}`. -/
lemma pairkernel_per_m (m : ℕ) (hm1 : 1 ≤ m) (hmsf : Squarefree m) :
    ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (m.primeFactors.card) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmnn : (0 : ℝ) ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hmpos.le _
  have hinner : ∀ g ∈ m.divisors,
      ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) * ((m / g).divisors.card : ℝ) := by
    intro g _
    have hstep : ∀ k ∈ (m / g).divisors,
        ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) * 1 := by
      intro k hk
      have hk1 : 1 ≤ k := Nat.pos_of_mem_divisors hk
      rw [show ((m * k : ℕ) : ℝ) = (m : ℝ) * (k : ℝ) by push_cast; ring,
        Real.mul_rpow hmpos.le (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk1) (by norm_num)) hmnn
    calc ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ ∑ _k ∈ (m / g).divisors, (m : ℝ) ^ (-(1 / 2 : ℝ)) * 1 := Finset.sum_le_sum hstep
      _ = (m : ℝ) ^ (-(1 / 2 : ℝ)) * ((m / g).divisors.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  calc ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ ∑ g ∈ m.divisors, (m : ℝ) ^ (-(1 / 2 : ℝ)) * ((m / g).divisors.card : ℝ) :=
        Finset.sum_le_sum hinner
    _ = (m : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ g ∈ m.divisors, ((m / g).divisors.card : ℝ) := by
        rw [Finset.mul_sum]
    _ = (m : ℝ) ^ (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (m.primeFactors.card) := by rw [paircount m hmsf]

/-- **R6-6 (`sum_gcW_pairkernel_le`).** The collection moment: the signed pair-kernel mass of the
Selberg weight is `≤ z·(1+log z²)⁹`. Support to squarefree `m ≤ z²`, `|gcW| ≤ 3^ω`, pair-sum
`≤ m^{−1/2}·3^ω`, then `9^ω m^{−1/2} ≤ z·9^ω/m` and `z·tau6W(z²,9) ≤ z·(1+log z²)⁹`. -/
lemma sum_gcW_pairkernel_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z Y : ℕ}
    (hz : 1 ≤ z) (hzY : z ^ 2 ≤ Y) :
    ∑ m ∈ Finset.Icc 1 Y, |gcW (selWeight χ z) m|
        * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 := by
  have hsupp : ∀ d, |selWeight χ z d| ≤ 1 := fun d => selweight_abs_le_one χ hsq
  have hsfsupp : ∀ d, selWeight χ z d ≠ 0 → Squarefree d :=
    fun d h => selWeight_ne_zero_squarefree χ z h
  have hsub : (Finset.Icc 1 (z ^ 2)).filter Squarefree ⊆ Finset.Icc 1 Y := by
    intro m hm; rw [Finset.mem_filter, Finset.mem_Icc] at hm; rw [Finset.mem_Icc]
    exact ⟨hm.1.1, le_trans hm.1.2 hzY⟩
  rw [← Finset.sum_subset hsub (fun m hmY hmnot => ?_)]
  · have hbnd : ∀ m ∈ (Finset.Icc 1 (z ^ 2)).filter Squarefree,
        |gcW (selWeight χ z) m|
            * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
          ≤ (z : ℝ) * ((9 : ℝ) ^ (m.primeFactors.card) / (m : ℝ)) := by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨hm1, hmz2⟩, hmsf⟩ := hm
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
      have hgcw : |gcW (selWeight χ z) m| ≤ (3 : ℝ) ^ (m.primeFactors.card) := by
        have := abs_gcW_le hsupp hsfsupp m; rwa [omega_eq_primeFactors_card] at this
      have hpair := pairkernel_per_m m hm1 hmsf
      have hpairnn : (0 : ℝ) ≤ ∑ g ∈ m.divisors,
          ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Finset.sum_nonneg
          (fun g _ => Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (by positivity) _))
      have hstep1 : |gcW (selWeight χ z) m|
            * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
          ≤ (9 : ℝ) ^ (m.primeFactors.card) * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
        calc |gcW (selWeight χ z) m|
              * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
            ≤ (3 : ℝ) ^ (m.primeFactors.card)
                * ((m : ℝ) ^ (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (m.primeFactors.card)) :=
              mul_le_mul hgcw hpair hpairnn (by positivity)
          _ = (9 : ℝ) ^ (m.primeFactors.card) * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
              rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]; ring
      have hmhalf : (m : ℝ) ^ (-(1 / 2 : ℝ)) * (m : ℝ) = (m : ℝ) ^ (1 / 2 : ℝ) := by
        nth_rewrite 2 [← Real.rpow_one (m : ℝ)]
        rw [← Real.rpow_add hmpos]; norm_num
      have hsqrtle : (m : ℝ) ^ (1 / 2 : ℝ) ≤ (z : ℝ) := by
        have hmz2' : (m : ℝ) ≤ (z : ℝ) ^ 2 := by exact_mod_cast hmz2
        calc (m : ℝ) ^ (1 / 2 : ℝ)
            ≤ ((z : ℝ) ^ 2) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hmz2' (by norm_num)
          _ = (z : ℝ) := by
              rw [← Real.rpow_natCast (z : ℝ) 2, ← Real.rpow_mul (by positivity)]; norm_num
      have hmz : (m : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (z : ℝ) / (m : ℝ) := by
        rw [le_div_iff₀ hmpos, hmhalf]; exact hsqrtle
      calc |gcW (selWeight χ z) m|
            * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
          ≤ (9 : ℝ) ^ (m.primeFactors.card) * (m : ℝ) ^ (-(1 / 2 : ℝ)) := hstep1
        _ ≤ (9 : ℝ) ^ (m.primeFactors.card) * ((z : ℝ) / (m : ℝ)) :=
            mul_le_mul_of_nonneg_left hmz (by positivity)
        _ = (z : ℝ) * ((9 : ℝ) ^ (m.primeFactors.card) / (m : ℝ)) := by ring
    calc ∑ m ∈ (Finset.Icc 1 (z ^ 2)).filter Squarefree,
            |gcW (selWeight χ z) m|
              * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ ∑ m ∈ (Finset.Icc 1 (z ^ 2)).filter Squarefree,
            (z : ℝ) * ((9 : ℝ) ^ (m.primeFactors.card) / (m : ℝ)) := Finset.sum_le_sum hbnd
      _ = (z : ℝ) * Salt.HardyLittlewood.tau6W (z ^ 2) 9 := by
          rw [Salt.HardyLittlewood.tau6W, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by norm_num)
      _ ≤ (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := Salt.HardyLittlewood.tau6W_le (z ^ 2) 9
          rwa [show ((z ^ 2 : ℕ) : ℝ) = (z : ℝ) ^ 2 by push_cast; ring] at this
  · rw [Finset.mem_Icc] at hmY
    have hgcw0 : gcW (selWeight χ z) m = 0 := by
      by_cases hmsf : Squarefree m
      · refine gcW_selWeight_eq_zero_of_gt_sq χ ?_
        by_contra hle
        exact hmnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmY.1, by omega⟩, hmsf⟩)
      · exact gcW_eq_zero_of_not_squarefree hsfsupp hmsf
    rw [hgcw0, abs_zero, zero_mul]

/-! ## §8 — R6-8 : the assembly `dh_extraction_upper_W` -/

set_option maxHeartbeats 1200000 in
-- The per-m residual assembles a double-sum triangle bound over the exact main collection.
/-- **R6-8 per-`m` residual.** For squarefree `m ≤ z²`,
`|red(m) − mainval(m)| ≤ C₂·Y^{1/2−β₀}·Σ_{g,k}(m·k)^{−1/2}`: the exact main collection
`mainval(m) = Σ_{g,k} coeff·main(Y/(mk))` (via `dhD0_scale_main` + `selHmul_collection` + `selNu`),
then `red − mainval = Σ_{g,k} coeff·(D₀ − main)`, triangle over `(g,k)` with R6-3 (`x ≥ 2` guard)
and `dhD0_scale_err`. -/
lemma dh_extraction_per_m [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β₀ : ℝ}
    (hzero : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0) (hlo : 1 / 2 ≤ β₀) (hhi : β₀ < 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {z Y m : ℕ} (hz : 1 ≤ z) (hY : 2 * z ^ 4 ≤ Y) (hm1 : 1 ≤ m) (hmsf : Squarefree m)
    (hmz2 : m ≤ z ^ 2) :
    |(∑ g ∈ m.divisors, chiRe χ g * ∑ k ∈ (m / g).divisors,
          (moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
            * dhD0 χ β₀ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
       - (DirichletCharacter.LFunction χ 1).re * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))
           * selNu χ m|
      ≤ (136 + 48 * (Real.sqrt q * (1 + Real.log q))
          + 48 * (Real.sqrt q * (1 + Real.log q)) * Z₀
          + 144 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀)) * (Y : ℝ) ^ (1 / 2 - β₀)
        * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  set L₁ := (DirichletCharacter.LFunction χ 1).re with hL1def
  set C₂ := 136 + 48 * (Real.sqrt q * (1 + Real.log q))
      + 48 * (Real.sqrt q * (1 + Real.log q)) * Z₀
      + 144 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀) with hC2def
  have hu : 0 < 1 - β₀ := by linarith
  have hu2 : 0 < 2 - β₀ := by linarith
  have hune : (1 - β₀) ≠ 0 := hu.ne'
  have hu2ne : (2 - β₀) ≠ 0 := hu2.ne'
  have hm0 : m ≠ 0 := by omega
  have hz4 : 1 ≤ z ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hYm : 1 ≤ Y := by omega
  have hmR0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
  have hmu_le : ∀ k : ℕ, |(moebius k : ℝ)| ≤ 1 :=
    fun k => by rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
  have hguard : ∀ g ∈ m.divisors, ∀ k ∈ (m / g).divisors,
      (1 : ℕ) ≤ m * k ∧ (2 : ℝ) ≤ (Y : ℝ) / ((m * k : ℕ) : ℝ) := by
    intro g hg k hk
    have hg1 : 1 ≤ g := Nat.pos_of_mem_divisors hg
    have hgm : g ∣ m := Nat.dvd_of_mem_divisors hg
    have hk1 : 1 ≤ k := Nat.pos_of_mem_divisors hk
    have hmgpos : 0 < m / g := Nat.div_pos (Nat.le_of_dvd (by omega) hgm) hg1
    have hkm : k ≤ m :=
      le_trans (Nat.le_of_dvd hmgpos (Nat.dvd_of_mem_divisors hk)) (Nat.div_le_self m g)
    have hmk1 : 1 ≤ m * k := Nat.mul_pos hm1 hk1
    have hmkz4 : m * k ≤ z ^ 4 := by
      calc m * k ≤ m * m := Nat.mul_le_mul (le_refl m) hkm
        _ ≤ z ^ 2 * z ^ 2 := Nat.mul_le_mul hmz2 hmz2
        _ = z ^ 4 := by ring
    have h2mk : 2 * (m * k) ≤ Y := le_trans (by omega) hY
    have hmkR : (0 : ℝ) < ((m * k : ℕ) : ℝ) := by exact_mod_cast hmk1
    refine ⟨hmk1, ?_⟩
    rw [le_div_iff₀ hmkR]
    calc (2 : ℝ) * ((m * k : ℕ) : ℝ) = ((2 * (m * k) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Y : ℝ) := by exact_mod_cast h2mk
  have hterm : ∀ g ∈ m.divisors, ∀ k ∈ (m / g).divisors,
      (moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
          * (L₁ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)))
        = (L₁ * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)) * (1 / (m : ℝ)))
            * ((moebius k : ℝ) * chiRe χ k / (k : ℝ)) := by
    intro g hg k hk
    obtain ⟨hmk1, -⟩ := hguard g hg k hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have : k ≠ 0 := by have := Nat.pos_of_mem_divisors hk; omega
      exact_mod_cast this
    have hsc := dhD0_scale_main (β₀ := β₀) (a := m * k) (Y := Y) hmk1 hYm
    have hmkcast : ((m * k : ℕ) : ℝ) = (m : ℝ) * (k : ℝ) := by push_cast; ring
    rw [show (moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
            * (L₁ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)))
          = (moebius k : ℝ) * chiRe χ k * L₁ / ((1 - β₀) * (2 - β₀))
            * (((m * k : ℕ) : ℝ) ^ (-β₀) * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 - β₀)) by ring,
        hsc, hmkcast]
    field_simp
  have hmainval : (∑ g ∈ m.divisors, chiRe χ g * ∑ k ∈ (m / g).divisors,
        (moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
          * (L₁ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))))
      = L₁ * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)) * selNu χ m := by
    calc (∑ g ∈ m.divisors, chiRe χ g * ∑ k ∈ (m / g).divisors,
            (moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
              * (L₁ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))))
        = ∑ g ∈ m.divisors, chiRe χ g * ∑ k ∈ (m / g).divisors,
            (L₁ * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)) * (1 / (m : ℝ)))
              * ((moebius k : ℝ) * chiRe χ k / (k : ℝ)) := by
          refine Finset.sum_congr rfl (fun g hg => ?_)
          congr 1
          exact Finset.sum_congr rfl (fun k hk => hterm g hg k hk)
      _ = (L₁ * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)) * (1 / (m : ℝ)))
            * ∑ g ∈ m.divisors, chiRe χ g
                * ∑ k ∈ (m / g).divisors, (moebius k : ℝ) * chiRe χ k / (k : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun g _ => ?_)
          rw [← Finset.mul_sum]; ring
      _ = (L₁ * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)) * (1 / (m : ℝ))) * selHmul χ m := by
          rw [selHmul_collection χ hsq hmsf]
      _ = L₁ * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)) * selNu χ m := by
          rw [selNu]; field_simp
  rw [← hmainval, ← Finset.sum_sub_distrib]
  have hcombine : ∀ g ∈ m.divisors,
      chiRe χ g * (∑ k ∈ (m / g).divisors, (moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
          * dhD0 χ β₀ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
        - chiRe χ g * ∑ k ∈ (m / g).divisors,
            (moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
            * (L₁ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)))
      = ∑ k ∈ (m / g).divisors, chiRe χ g * ((moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
          * (dhD0 χ β₀ ((Y : ℝ) / ((m * k : ℕ) : ℝ))
            - L₁ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)))) := by
    intro g _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [Finset.sum_congr rfl hcombine]
  calc |∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors,
          chiRe χ g * ((moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
            * (dhD0 χ β₀ ((Y : ℝ) / ((m * k : ℕ) : ℝ))
              - L₁ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))))|
      ≤ ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors,
          C₂ * (Y : ℝ) ^ (1 / 2 - β₀) * ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun g hg => ?_))
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k hk => ?_))
        obtain ⟨hmk1, hx2⟩ := hguard g hg k hk
        have hmkR0 : (0 : ℝ) ≤ ((m * k : ℕ) : ℝ) := by positivity
        have hmkrp : (0 : ℝ) ≤ ((m * k : ℕ) : ℝ) ^ (-β₀) := Real.rpow_nonneg hmkR0 _
        have hR3 := unmoll_extraction_abs_real χ hχ hsq hq hzero hlo hhi hZ
          (x := (Y : ℝ) / ((m * k : ℕ) : ℝ)) hx2
        rw [← hL1def, ← hC2def] at hR3
        have herr := dhD0_scale_err (β₀ := β₀) (a := m * k) (Y := Y) hmk1 hYm
        calc |chiRe χ g * ((moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
                * (dhD0 χ β₀ ((Y : ℝ) / ((m * k : ℕ) : ℝ))
                  - L₁ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))))|
            = |chiRe χ g| * (|(moebius k : ℝ)| * |chiRe χ k| * ((m * k : ℕ) : ℝ) ^ (-β₀)
                * |dhD0 χ β₀ ((Y : ℝ) / ((m * k : ℕ) : ℝ))
                  - L₁ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))|) := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hmkrp]
          _ ≤ 1 * (1 * 1 * ((m * k : ℕ) : ℝ) ^ (-β₀)
                * (C₂ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 / 2 - β₀))) := by
              gcongr
              · exact chiRe_abs_le_one χ g
              · exact hmu_le k
              · exact chiRe_abs_le_one χ k
          _ = C₂ * (Y : ℝ) ^ (1 / 2 - β₀) * ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
              rw [show (1 : ℝ) * (1 * 1 * ((m * k : ℕ) : ℝ) ^ (-β₀)
                    * (C₂ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 / 2 - β₀)))
                  = C₂ * (((m * k : ℕ) : ℝ) ^ (-β₀)
                    * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 / 2 - β₀)) by ring, herr]
              ring
    _ = C₂ * (Y : ℝ) ^ (1 / 2 - β₀)
          * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [Finset.mul_sum]

set_option maxHeartbeats 1200000 in
-- The capstone: regroup + exact reduction + signed main collection + residual moment.
/-- **R6-8 (`dh_extraction_upper_W`) — the weighted extraction (T-BAL's last hard rung).** The
Selberg-mollified `β₀`-detector's partial sum is `L(1,χ)·selMainTerm` main plus a `Y^{1/2−β₀}`
error, `C₂ = 4·C_w = 136+48M+48M·Z₀+144M/(1−β₀)`, under the guard `2z⁴ ≤ Y`. STEP 1 regroup
(`dhExtractionW_regroup`) + kernel (`dhKernR_eq`) + the EXACT reduction (`dhA_kernel_reduction`);
STEP 2 the signed main collected EXACTLY (`sum_gcW_selNu_eq_selMainTerm`); STEP 3 signed
subtraction; STEP 4 triangle on the residual only (`dh_extraction_per_m` + `sum_gcW_pairkernel_le`,
`gcW = 0` off squarefree/`> z²`). -/
theorem dh_extraction_upper_W [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β₀ : ℝ}
    (hzero : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0) (hlo : 1 / 2 ≤ β₀) (hhi : β₀ < 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {z Y : ℕ} (hz : 1 ≤ z) (hY : 2 * z ^ 4 ≤ Y) :
    |∑ n ∈ Finset.Icc 1 Y,
        dhCoeffW χ (selWeight χ z) n * (n : ℝ) ^ (-β₀) * dhKernR ((n : ℝ) / (Y : ℝ))
       - (DirichletCharacter.LFunction χ 1).re * selMainTerm χ z
           * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))|
      ≤ (136 + 48 * (Real.sqrt q * (1 + Real.log q))
          + 48 * (Real.sqrt q * (1 + Real.log q)) * Z₀
          + 144 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀))
        * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀) := by
  set M := Real.sqrt q * (1 + Real.log q) with hMdef
  set L₁ := (DirichletCharacter.LFunction χ 1).re with hL1def
  set C₂ := 136 + 48 * M + 48 * M * Z₀ + 144 * M / (1 - β₀) with hC2def
  have hu : 0 < 1 - β₀ := by linarith
  have hu2 : 0 < 2 - β₀ := by linarith
  have hune : (1 - β₀) ≠ 0 := hu.ne'
  have hu2ne : (2 - β₀) ≠ 0 := hu2.ne'
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hZ0nn : 0 ≤ Z₀ := le_trans (norm_nonneg _)
    (hZ (β₀ : ℂ) (by rw [Complex.ofReal_re]; linarith) (by rw [Complex.ofReal_re]; linarith)
      (by rw [Complex.ofReal_im]; simp))
  have hC2nn : 0 ≤ C₂ := by rw [hC2def]; positivity
  have hY1 : 1 ≤ Y := by have := Nat.one_le_pow 4 z (by omega); omega
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY1
  have hz2Y : z ^ 2 ≤ Y := by
    have h1 : z ^ 2 ≤ z ^ 4 := Nat.pow_le_pow_right hz (by norm_num)
    omega
  have hsfsupp : ∀ d, selWeight χ z d ≠ 0 → Squarefree d :=
    fun d h => selWeight_ne_zero_squarefree χ z h
  rw [Finset.sum_congr rfl (fun n _ => mul_assoc _ _ _),
      dhExtractionW_regroup χ (selWeight χ z)
        (fun n => (n : ℝ) ^ (-β₀) * dhKernR ((n : ℝ) / (Y : ℝ))) Y]
  have hred : ∀ m ∈ Finset.Icc 1 Y,
      gcW (selWeight χ z) m * (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n),
          dhA χ n * ((n : ℝ) ^ (-β₀) * dhKernR ((n : ℝ) / (Y : ℝ))))
        = gcW (selWeight χ z) m * (∑ g ∈ m.divisors, chiRe χ g * ∑ k ∈ (m / g).divisors,
            (moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
              * dhD0 χ β₀ ((Y : ℝ) / ((m * k : ℕ) : ℝ))) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    congr 1
    rw [← dhA_kernel_reduction χ hsq (by omega : 1 ≤ m) Y]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [dhKernR_eq (by rw [div_le_one hYpos]; exact_mod_cast hn.1.2), ← mul_assoc]
  rw [Finset.sum_congr rfl hred]
  have htarget : (∑ m ∈ Finset.Icc 1 Y, gcW (selWeight χ z) m
        * (L₁ * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)) * selNu χ m))
      = L₁ * selMainTerm χ z * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)) := by
    rw [show (∑ m ∈ Finset.Icc 1 Y, gcW (selWeight χ z) m
            * (L₁ * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)) * selNu χ m))
          = L₁ * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))
              * ∑ m ∈ Finset.Icc 1 Y, gcW (selWeight χ z) m * selNu χ m from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring),
      sum_gcW_selNu_eq_selMainTerm χ hsq hz hz2Y]
    ring
  rw [← htarget, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun m _ => by ring :
      ∀ m ∈ Finset.Icc 1 Y,
        gcW (selWeight χ z) m * (∑ g ∈ m.divisors, chiRe χ g * ∑ k ∈ (m / g).divisors,
              (moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
                * dhD0 χ β₀ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
          - gcW (selWeight χ z) m
              * (L₁ * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)) * selNu χ m)
        = gcW (selWeight χ z) m
            * ((∑ g ∈ m.divisors, chiRe χ g * ∑ k ∈ (m / g).divisors,
                (moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
                  * dhD0 χ β₀ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
              - L₁ * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)) * selNu χ m))]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hpm : ∀ m ∈ Finset.Icc 1 Y,
      |gcW (selWeight χ z) m
          * ((∑ g ∈ m.divisors, chiRe χ g * ∑ k ∈ (m / g).divisors,
              (moebius k : ℝ) * chiRe χ k * ((m * k : ℕ) : ℝ) ^ (-β₀)
                * dhD0 χ β₀ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
            - L₁ * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀)) * selNu χ m)|
        ≤ |gcW (selWeight χ z) m| * (C₂ * (Y : ℝ) ^ (1 / 2 - β₀)
            * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
    intro m hm
    rw [abs_mul]
    rcases eq_or_ne (gcW (selWeight χ z) m) 0 with hg0 | hg0
    · rw [hg0, abs_zero, zero_mul, zero_mul]
    · have hmsf : Squarefree m := by
        by_contra h; exact hg0 (gcW_eq_zero_of_not_squarefree hsfsupp h)
      have hmz2 : m ≤ z ^ 2 := by
        by_contra h; exact hg0 (gcW_selWeight_eq_zero_of_gt_sq χ (by omega))
      have hm1 : 1 ≤ m := by rw [Finset.mem_Icc] at hm; omega
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have := dh_extraction_per_m χ hχ hsq hq hzero hlo hhi hZ hz hY hm1 hmsf hmz2
      rw [← hL1def, ← hMdef, ← hC2def] at this
      exact this
  refine (Finset.sum_le_sum hpm).trans ?_
  have hYrp : (0 : ℝ) ≤ (Y : ℝ) ^ (1 / 2 - β₀) := Real.rpow_nonneg hYpos.le _
  calc ∑ m ∈ Finset.Icc 1 Y, |gcW (selWeight χ z) m| * (C₂ * (Y : ℝ) ^ (1 / 2 - β₀)
          * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))
      = C₂ * (Y : ℝ) ^ (1 / 2 - β₀) * ∑ m ∈ Finset.Icc 1 Y, |gcW (selWeight χ z) m|
          * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)
    _ ≤ C₂ * (Y : ℝ) ^ (1 / 2 - β₀) * ((z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9) :=
        mul_le_mul_of_nonneg_left (sum_gcW_pairkernel_le χ hsq hz hz2Y)
          (mul_nonneg hC2nn hYrp)
    _ = C₂ * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀) := by ring

end Salt.SW

end
