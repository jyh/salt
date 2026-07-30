/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MobiusChiRateClose
import Salt.MR.ZetaPowLower
import Salt.MR.HalaszPrimesCore
import Salt.SW.ZetaInvShallow

/-!
# ⟦THE ζ SHALLOW STONE⟧ — `Salt.MR.ZetaInvShallowVk`, discharged

The last analytic residue of the KMT port's mirror (`Salt/MR/MobiusChiRateClose.lean` §6):
the `q = 1` twin of `lFunctionInvShallowVkSharp_holds`, i.e. `Salt.SW.zeta_inv_shallow` moved
from the CLASSICAL width `c₄/log⁹(|t|+2)` to the VK width
`vkShallowWidthSharp c₄ 1 H = c₄/((log H)^{3/4}(log log H)⁴)`.

## What the file does

Both conjuncts of `ZetaInvShallowVk`:

1. **the box is ζ-zero-free** (`zeta_no_zero_in_shallow_box`) — a composition of landed
   material, exactly as the mirror's residue note predicted: above the VK floor the power
   region `Salt.Vk.zeta_zero_free_region_pow` (width `c/((log|γ|)^{3/4}(loglog|γ|)³)`,
   monotone in the height, hence uniform over `|γ| ≤ H+1`), below the floor the classical
   `Salt.SW.zeta_zero_free_region` (width `c₃/log(|γ|+2)`, a CONSTANT there).  No `q` gate
   appears — at `q = 1` the twisted machinery's `(log q + 1)` factors are all `1`;
2. **the shallow bound** `‖mmuG(σ+iτ)‖ ≤ K(log H)⁵` on `1 − W ≤ σ ≤ 2`, `|τ| ≤ H`, in two
   height regimes split at a CONSTANT `T₁ = T₀ + t₀ + 4`:
   * `|τ| ≤ T₁` — the landed `Salt.SW.zeta_inv_shallow` verbatim, whose classical width
     `c₄'/log⁹(|τ|+2) ≥ c₄'/log⁹(T₁+2)` is a constant there and whose value
     `C·log⁷(|τ|+2) ≤ C·log⁷(T₁+2)` is a constant too.  **This is what handles the near-pole
     corner**: the pole patch `Salt.SW.Zc_patch_lower` is already inside that theorem, and at
     `s = 1` exactly `mmuG 1 = 0`.  No re-proof of the private `zeta_near_bound_core` is needed;
   * `|τ| ≥ T₁` — §1 of `Salt/MR/LFunctionInvShallow.lean` re-run at the `Zc` normalization
     (`norm_Zc_lower_of_shallow_ball`): `Zc = (·−1)ζ` is ENTIRE, the Landau ball
     (`Salt.Vk.entire_norm_logDeriv_sub_sum_scaled`) sits entirely inside the zero-free region
     so its zero set is EMPTY, and one horizontal mean-value transport of `log‖Zc‖` from
     `(1+W)+iτ` down to `σ+iτ` costs `≤ 1`.  Negative heights by `Zc_conj`.

## The pole, and why it is free

The mirror banked the pole handling and it is confirmed: `‖Zc‖ ≍ |τ|·‖ζ‖` is far too big for a
raw ceiling, but the Landau core only ever sees the RATIO `‖Zc z / Zc c‖`, and on the ball
`‖z−1‖ ≤ ‖c−1‖ + 1/8 ≤ 2‖c−1‖` because `‖c−1‖ ≥ |τ| ≥ 2`.  So the pole factor cancels up to a
`2`, and the ratio ceiling is `M₀ ≤ 64·Kg·log(H+1)/W` — no `H`, only `log H`
(`norm_Zc_ratio_le_of_shallow_ball`).  The reference floor is the landed
`Salt.MR.zeta_pow_lower_far` (`‖ζ((1+W)+iτ)‖ ≥ W/32`, unconditional), the exact ζ analogue of
`LFunction_near_one_lower`, and the closing constant is `256/W`.

## The budget, and the constants

The ball scale is `λ = cR/(10⁵·(log H)^{3/4}(loglog H)³)` — a fixed fraction of the region's own
width shape — and the Borel–Carathéodory cost is `(120/λ)·log(4M₀)` per unit length with
`log(4M₀) ≤ (675 + log(512 Kg) + log(1/c₄))·loglog H/100` (`zeta_budget_log_bound`): the whole
cost is `≍ loglog H`, never `log H`, which is precisely why the width has to carry
`(loglog H)⁴ = (loglog H)³ (region) × loglog H (the transport)`.  The gate is the same
`c₄·log(1/c₄) → 0` shape as §4's, discharged by `exists_zetaShallowGate` (which rides the landed
`sq_div_sixteen_log_le`), with

  `c₄ ≤ B := min 1 (min (cR/10⁶) (c₄'/log⁹(T₁+2)))`,
  `cR := min 1 (min c_pow (c₃/(2 log(T₀+2))))`,

so every one of the four scale constraints (reach, growth strip, region depth, classical
below-floor leg) is a single `min` arm.  All of them are astronomically lazy; only the SHAPE
`(log H)^{3/4}(loglog H)⁴` is load-bearing, and it matches the consumer byte-for-byte.
-/

noncomputable section

namespace Salt.MR

open Complex Metric Set DirichletCharacter
open Salt.SW Salt.Vk
open scoped LSeries.notation

/-! ## §0 — the width at `q = 1`, the gate witness, the scale facts -/

/-- The sharp shallow width read at `q = 1`: the `(log q + 1)²` factor is `1`. -/
lemma vkShallowWidthSharp_one (c₄ H : ℝ) :
    vkShallowWidthSharp c₄ 1 H
      = c₄ / (Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (4 : ℕ)) := by
  rw [vkShallowWidthSharp, Nat.cast_one, Real.log_one, zero_add, one_pow, one_mul]

/-- **The `c₄`-gate witness, in general shape.**  For every `A ≥ 1` and every `B ∈ (0,1]` there is
a `c ∈ (0,B]` with `c·(A + log(1/c)) ≤ B`.  Rides the landed `sq_div_sixteen_log_le`; the extra
conclusion `c ≤ B` is what lets a single gate serve all the scale constraints. -/
lemma exists_zetaShallowGate {A B : ℝ} (hA : 1 ≤ A) (hB0 : 0 < B) (hB1 : B ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ c ≤ B ∧ c * (A + Real.log (1 / c)) ≤ B := by
  have hA0 : (0 : ℝ) < A := by linarith
  set x : ℝ := B / A with hxdef
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hxB : x ≤ B := by rw [hxdef]; exact div_le_self hB0.le hA
  have hx1 : x ≤ 1 := le_trans hxB hB1
  refine ⟨x ^ 2 / 16, by positivity, ?_, ?_⟩
  · nlinarith [hx0, hx1, hxB]
  · have hS : (0 : ℝ) ≤ Real.log (1 / (x ^ 2 / 16)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hx0, hx1]
    have hkey := sq_div_sixteen_log_le hx0 hx1
    have hc : (0 : ℝ) ≤ x ^ 2 / 16 := by positivity
    have hsplit : x ^ 2 / 16 * (A + Real.log (1 / (x ^ 2 / 16)))
        ≤ A * (x ^ 2 / 16 * (1 + Real.log (1 / (x ^ 2 / 16)))) := by
      nlinarith [hS, hA, hc, mul_nonneg hc hS]
    have hfin : A * (x ^ 2 / 16 * (1 + Real.log (1 / (x ^ 2 / 16)))) ≤ A * x :=
      mul_le_mul_of_nonneg_left hkey hA0.le
    have hval : A * x = B := by rw [hxdef]; field_simp
    linarith

/-- The standing log scales at `H ≥ exp(exp 100) + 1`: `log H ≥ e^100`, `loglog H ≥ 100`, and the
`H` vs `H+1` pair, each within a factor `2`. -/
lemma zeta_shallow_scales {H : ℝ} (hH : Real.exp (Real.exp 100) + 1 ≤ H) :
    Real.exp 100 ≤ Real.log H ∧ (100 : ℝ) ≤ Real.log (Real.log H) ∧
      Real.log H ≤ Real.log (H + 1) ∧ Real.log (H + 1) ≤ 2 * Real.log H ∧
      Real.log (Real.log (H + 1)) ≤ 2 * Real.log (Real.log H) ∧ Real.exp 1 < H := by
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hLg : Real.exp 100 ≤ Real.log H := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLg0 : (0 : ℝ) < Real.log H := by linarith
  have hℓ : (100 : ℝ) ≤ Real.log (Real.log H) := by
    rw [← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLg
  have hLgp : Real.log H ≤ Real.log (H + 1) := Real.log_le_log hHpos (by linarith)
  have hLgp2 : Real.log (H + 1) ≤ 2 * Real.log H := by
    have h1 : H + 1 ≤ H * H := by nlinarith [hEbig]
    have h2 : Real.log (H + 1) ≤ Real.log (H * H) := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by linarith) (by linarith)] at h2
    linarith
  have hℓp : Real.log (Real.log (H + 1)) ≤ 2 * Real.log (Real.log H) := by
    have h1 : Real.log (Real.log (H + 1)) ≤ Real.log (2 * Real.log H) :=
      Real.log_le_log (by linarith) hLgp2
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    linarith
  have hHe : Real.exp 1 < H := by
    have h1 : Real.exp 1 < Real.exp (Real.exp 100) := Real.exp_lt_exp.mpr (by linarith)
    linarith
  exact ⟨hLg, hℓ, hLgp, hLgp2, hℓp, hHe⟩

/-- **The Borel–Carathéodory cost is `≍ loglog H`, nothing more.**  For `x ≤ 512·Kg·L·R·ℓ⁴/c₄`
with `log L = ℓ ≥ 100` and `log R = (3/4)ℓ` (i.e. `R = L^{3/4}`),

  `log x ≤ (675 + log(512 Kg) + log(1/c₄))·ℓ/100`.

The four contributions are `log(512Kg)` and `log(1/c₄)` (constants, absorbed by `ℓ ≥ 100`), the
growth's `log L = ℓ`, the width's `log R = (3/4)ℓ`, and `4 log ℓ ≤ 4ℓ`.  It is THIS bound —
`≍ ℓ`, not `≍ L` — that the sharp width's fourth `loglog` divides out. -/
lemma zeta_budget_log_bound {Kg c₄ Lg ℓ R x : ℝ} (hKg : 1 ≤ Kg)
    (hc₄0 : 0 < c₄) (hc₄1 : c₄ ≤ 1) (hℓ : 100 ≤ ℓ)
    (hL0 : 0 < Lg) (hLℓ : Real.log Lg = ℓ) (hR0 : 0 < R) (hlogR : Real.log R = 3 / 4 * ℓ)
    (hx0 : 0 < x) (hxub : x ≤ 512 * Kg * Lg * (R * ℓ ^ (4 : ℕ)) / c₄) :
    Real.log x ≤ (675 + Real.log (512 * Kg) + Real.log (1 / c₄)) * ℓ / 100 := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hlogKg : (0 : ℝ) ≤ Real.log (512 * Kg) := Real.log_nonneg (by nlinarith)
  have hS0 : (0 : ℝ) ≤ Real.log (1 / c₄) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hc₄0]; linarith
  have hlogc : Real.log (1 / c₄) = -Real.log c₄ := by rw [one_div, Real.log_inv]
  have hlogℓ : Real.log ℓ ≤ ℓ := by linarith [Real.log_le_sub_one_of_pos hℓ0]
  have hsplit : Real.log (512 * Kg * Lg * (R * ℓ ^ (4 : ℕ)) / c₄)
      = Real.log (512 * Kg) + ℓ + 3 / 4 * ℓ + 4 * Real.log ℓ - Real.log c₄ := by
    rw [Real.log_div (by positivity) (ne_of_gt hc₄0),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (ne_of_gt hL0),
      Real.log_mul (ne_of_gt hR0) (by positivity),
      Real.log_pow, hLℓ, hlogR]
    push_cast; ring
  have hmain := Real.log_le_log hx0 hxub
  rw [hsplit] at hmain
  have hab0 : (0 : ℝ) ≤ Real.log (512 * Kg) - Real.log c₄ := by
    rw [hlogc] at hS0; linarith
  have hconst : Real.log (512 * Kg) - Real.log c₄
      ≤ (Real.log (512 * Kg) - Real.log c₄) * ℓ / 100 := by
    nlinarith [mul_nonneg hab0 (by linarith : (0 : ℝ) ≤ ℓ - 100)]
  rw [hlogc]
  linarith [hmain, hconst, hlogℓ, hℓ]

/-- `mmuG s = (ζ s)⁻¹` off `s = 1`, with NO non-vanishing hypothesis: the landed
`Salt.SW.mmuG_eq_zeta_inv` never uses its `hζ` argument (both sides are `0` at a zero), and this
file needs the hypothesis-free form. -/
lemma mmuG_eq_zeta_inv' {s : ℂ} (hs1 : s ≠ 1) : mmuG s = (riemannZeta s)⁻¹ := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [mmuG, Zc_eq_of_ne hs1, div_mul_eq_div_div, div_self h1, one_div]

/-- `mmuG` has conjugation-symmetric modulus: the negative-height leg of the shallow bound. -/
lemma norm_mmuG_neg_im (σ τ : ℝ) :
    ‖mmuG ((σ : ℂ) + ((-τ : ℝ) : ℂ) * I)‖ = ‖mmuG ((σ : ℂ) + (τ : ℂ) * I)‖ := by
  set w : ℂ := (σ : ℂ) + (τ : ℂ) * I with hwdef
  have hpt : (σ : ℂ) + ((-τ : ℝ) : ℂ) * I = (starRingEnd ℂ) w := by
    rw [hwdef]
    simp only [Complex.ofReal_neg, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hkey : mmuG ((starRingEnd ℂ) w) = (starRingEnd ℂ) (mmuG w) := by
    rw [mmuG, mmuG, Zc_conj, show (starRingEnd ℂ) w - 1 = (starRingEnd ℂ) (w - 1) by simp,
      ← map_div₀]
  rw [hpt, hkey, Complex.norm_conj]

/-! ## §1 — THE CORE: a zero-free Landau ball forces the `Zc` floor

The `Zc` twin of `norm_LFunction_inv_shallow_of_ball` (`Salt/MR/LFunctionInvShallow.lean` §1).
Same geometry, same empty zero set, same transport; the only change is that the ceiling enters
as a RATIO (`‖Zc z / Zc c‖ ≤ M₀`), which is what makes the pole factor cancel. -/

/-- **THE ζ SHALLOW CORE.**  Let `c = (1+W) + iτ`.  If

* `‖Zc z / Zc c‖ ≤ M₀` on the closed ball of radius `7λ/4` about `c` (the ratio ceiling),
* `Zc` has NO zero in the open ball of radius `3λ/2` about `c` (the region),
* `2W ≤ 23λ/20` (the segment `[1−W, 1+W] + iτ` sits inside Landau's inner ball), and
* `240·W·log(4M₀) ≤ λ` (the budget),

then `‖Zc c‖/4 ≤ ‖Zc(σ+iτ)‖` throughout `1 − W ≤ σ ≤ 1 + W`.

Route: `Salt.Vk.entire_norm_logDeriv_sub_sum_scaled` at `G = Zc/Zc(c)` (entire — this is the
pole patch: `Zc` is entire and `Zc 1 = 1` — with `G c = 1`), whose zero set is EMPTY by the
second hypothesis, so the numeric conjunct is the bare `‖logDeriv Zc‖ ≤ (120/λ)·log(4M₀)` on
the inner ball; the mean-value inequality transports `log‖Zc‖` from `c` to `σ+iτ` at cost `≤ 1`,
and `e ≤ 4`. -/
theorem norm_Zc_lower_of_shallow_ball {τ W lam M₀ : ℝ}
    (hW0 : 0 < W) (hlam0 : 0 < lam) (hM₀ : 1 ≤ M₀)
    (hreach : 2 * W ≤ 23 / 20 * lam)
    (hball : ∀ z : ℂ, ‖z - (((1 + W : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ 7 / 4 * lam →
        ‖Zc z / Zc (((1 + W : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ M₀)
    (hzf : ∀ z : ℂ, ‖z - (((1 + W : ℝ) : ℂ) + (τ : ℂ) * I)‖ < 3 / 2 * lam → Zc z ≠ 0)
    (hbudget : 240 * W * Real.log (4 * M₀) ≤ lam)
    {σ : ℝ} (hσlo : 1 - W ≤ σ) (hσhi : σ ≤ 1 + W) :
    ‖Zc (((1 + W : ℝ) : ℂ) + (τ : ℂ) * I)‖ / 4 ≤ ‖Zc ((σ : ℂ) + (τ : ℂ) * I)‖ := by
  classical
  set c : ℂ := ((1 + W : ℝ) : ℂ) + (τ : ℂ) * I with hcdef
  have hZcc : Zc c ≠ 0 := by
    refine hzf c ?_
    rw [sub_self, norm_zero]; positivity
  have hZccpos : 0 < ‖Zc c‖ := norm_pos_iff.mpr hZcc
  have hM₀pos : 0 < M₀ := lt_of_lt_of_le zero_lt_one hM₀
  have hlog4 : 0 < Real.log (4 * M₀) := Real.log_pos (by nlinarith)
  have hZdiff : Differentiable ℂ Zc := Zc_differentiable
  have hG_diff : Differentiable ℂ (fun z => Zc z / Zc c) := fun z => (hZdiff z).div_const _
  have hGc_floor : (1 : ℝ) / 4 ≤ ‖Zc c / Zc c‖ := by
    rw [div_self hZcc, norm_one]; norm_num
  have hLDG : ∀ z, logDeriv (fun w => Zc w / Zc c) z = logDeriv Zc z := by
    intro z
    have hGeq : (fun w => Zc w / Zc c) = fun w => (Zc c)⁻¹ * Zc w := by funext w; ring
    rw [hGeq, logDeriv_const_mul z (Zc c)⁻¹ (inv_ne_zero hZcc)]
  have hsph : ∀ r : ℝ, r ≤ 7 / 4 * lam → ∀ z ∈ sphere c r, ‖Zc z / Zc c‖ ≤ M₀ := by
    intro r hr z hz
    have hzc : ‖z - c‖ = r := by rw [mem_sphere_iff_norm] at hz; exact hz
    exact hball z (by rw [hzc]; exact hr)
  obtain ⟨Z, m, _hh, hmemb, -, -, -, -, hnum⟩ :=
    entire_norm_logDeriv_sub_sum_scaled hG_diff hlam0 hM₀ hGc_floor
      (hsph _ le_rfl) (hsph _ (by linarith))
  -- THE ZERO SET IS EMPTY
  have hZempty : Z = ∅ := by
    refine Finset.eq_empty_of_forall_notMem (fun ρ hρ => ?_)
    obtain ⟨hballρ, hzero⟩ := hmemb ρ hρ
    have hZρ : Zc ρ = 0 := (div_eq_zero_iff.mp hzero).resolve_right hZcc
    rw [mem_ball, dist_eq_norm] at hballρ
    exact hzf ρ hballρ hZρ
  set K : ℝ := 120 / lam * Real.log (4 * M₀) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hnumbd : ∀ u : ℝ, |u - (1 + W)| ≤ 2 * W →
      ‖logDeriv Zc ((u : ℂ) + (τ : ℂ) * I)‖ ≤ K := by
    intro u hu
    have hsub : ((u : ℂ) + (τ : ℂ) * I) - c = ((u - (1 + W) : ℝ) : ℂ) := by
      rw [hcdef]; push_cast; ring
    have hdist : ‖((u : ℂ) + (τ : ℂ) * I) - c‖ ≤ 23 / 20 * lam := by
      rw [hsub, Complex.norm_real, Real.norm_eq_abs]; linarith [hu, hreach]
    have hne : Zc ((u : ℂ) + (τ : ℂ) * I) / Zc c ≠ 0 := by
      refine div_ne_zero (hzf _ ?_) hZcc
      calc ‖((u : ℂ) + (τ : ℂ) * I) - c‖ ≤ 23 / 20 * lam := hdist
        _ < 3 / 2 * lam := by nlinarith
    have hres := hnum ((u : ℂ) + (τ : ℂ) * I) hdist hne
    rw [hLDG, hZempty] at hres
    simpa [hKdef] using hres
  -- the horizontal transport of `log‖Zc‖`
  have hmemIcc : ∀ v ∈ Set.Icc (1 - W) (1 + W), |v - (1 + W)| ≤ 2 * W := by
    intro v hv
    rw [abs_le]
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hZne : ∀ v ∈ Set.Icc (1 - W) (1 + W), Zc ((v : ℂ) + (τ : ℂ) * I) ≠ 0 := by
    intro v hv
    refine hzf _ ?_
    have hsub : ((v : ℂ) + (τ : ℂ) * I) - c = ((v - (1 + W) : ℝ) : ℂ) := by
      rw [hcdef]; push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs]
    have hvb := hmemIcc v hv
    linarith [hreach]
  have hderiv : ∀ v ∈ Set.Icc (1 - W) (1 + W),
      HasDerivWithinAt (fun w : ℝ => Real.log ‖Zc ((w : ℂ) + (τ : ℂ) * I)‖)
        ((logDeriv Zc ((v : ℂ) + (τ : ℂ) * I)).re) (Set.Icc (1 - W) (1 + W)) v := by
    intro v hv
    exact (hasDerivAt_log_norm_horiz (hZdiff _) (hZne v hv)).hasDerivWithinAt
  have hbnd : ∀ v ∈ Set.Icc (1 - W) (1 + W),
      ‖(logDeriv Zc ((v : ℂ) + (τ : ℂ) * I)).re‖ ≤ K := by
    intro v hv
    calc ‖(logDeriv Zc ((v : ℂ) + (τ : ℂ) * I)).re‖
        ≤ ‖logDeriv Zc ((v : ℂ) + (τ : ℂ) * I)‖ := by
          rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
      _ ≤ K := hnumbd v (hmemIcc v hv)
  have hmvt := (convex_Icc (1 - W) (1 + W)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbnd (Set.right_mem_Icc.mpr (by linarith)) (Set.mem_Icc.mpr ⟨hσlo, hσhi⟩)
  have hstep : |σ - (1 + W)| ≤ 2 * W := hmemIcc σ (Set.mem_Icc.mpr ⟨hσlo, hσhi⟩)
  have hloss : K * ‖σ - (1 + W)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    have h1 : K * |σ - (1 + W)| ≤ K * (2 * W) :=
      mul_le_mul_of_nonneg_left hstep hKpos.le
    have h2 : K * (2 * W) ≤ 1 := by
      rw [hKdef, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_one hlam0]
      linarith [hbudget]
    linarith
  have hZσpos : 0 < ‖Zc ((σ : ℂ) + (τ : ℂ) * I)‖ := by
    rw [norm_pos_iff]
    exact hZne σ (Set.mem_Icc.mpr ⟨hσlo, hσhi⟩)
  have hφlow : Real.log ‖Zc c‖ - 1 ≤ Real.log ‖Zc ((σ : ℂ) + (τ : ℂ) * I)‖ := by
    have hkey : |Real.log ‖Zc ((σ : ℂ) + (τ : ℂ) * I)‖
        - Real.log ‖Zc (((1 + W : ℝ) : ℂ) + (τ : ℂ) * I)‖| ≤ 1 := by
      rw [← Real.norm_eq_abs]
      exact le_trans hmvt hloss
    have h2 := (abs_le.mp hkey).1
    rw [show (((1 + W : ℝ) : ℂ) + (τ : ℂ) * I) = c from rfl] at h2
    linarith
  have hexp : Real.exp (Real.log ‖Zc c‖ - 1) ≤ ‖Zc ((σ : ℂ) + (τ : ℂ) * I)‖ := by
    rw [← Real.exp_log hZσpos]
    exact Real.exp_le_exp.mpr hφlow
  refine le_trans ?_ hexp
  rw [Real.exp_sub, Real.exp_log hZccpos]
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hepos]
  nlinarith [hZccpos]

/-! ## §2 — the ball's two hypotheses, from the LANDED VK growth and the landed floor -/

/-- **The ratio ceiling on the shallow ball — the pole cancels.**  On the closed ball of radius
`r ≤ min (1/8) (vkTheta (H+1))` about `c = (1+W)+iτ` (heights `τ ∈ [t₀+1, H]`, `τ ≥ 2`):

  `‖Zc z / Zc c‖ ≤ 64·Kg·log(H+1)/W`.

The numerator's pole factor `‖z−1‖` is within `2` of the denominator's `‖c−1‖` (because
`‖c−1‖ ≥ |τ| ≥ 2 ≥ 16r`), the ζ ceiling is the landed VK strip growth `Kg·log(Im z)` (the ball
stays inside the strip since `r ≤ vkTheta(H+1) ≤ vkTheta(Im z)`, `vkTheta` antitone), and the ζ
floor at the center is the landed `zeta_pow_lower_far` (`≥ W/32`). -/
lemma norm_Zc_ratio_le_of_shallow_ball {Kg t₀ H W τ r : ℝ} (hKg : 1 ≤ Kg)
    (hgrow : ∀ σ' t : ℝ, t₀ ≤ t → 1 - vkTheta t ≤ σ' → σ' ≤ 3 →
        ‖riemannZeta ((σ' : ℂ) + (t : ℂ) * I)‖ ≤ Kg * Real.log t)
    (hW0 : 0 < W) (hW1 : W ≤ 1)
    (_hr0 : 0 ≤ r) (hr8 : r ≤ 1 / 8) (hrΘ : r ≤ vkTheta (H + 1))
    (hτ2 : 2 ≤ τ) (hτt₀ : t₀ + 1 ≤ τ) (hτe : Real.exp 1 < τ - 1) (hτH : τ ≤ H)
    {z : ℂ} (hz : ‖z - (((1 + W : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ r) :
    ‖Zc z / Zc (((1 + W : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ 64 * Kg * Real.log (H + 1) / W := by
  set c : ℂ := ((1 + W : ℝ) : ℂ) + (τ : ℂ) * I with hcdef
  have hcre : c.re = 1 + W := by rw [hcdef]; simp
  have hcim : c.im = τ := by rw [hcdef]; simp
  have hre : |z.re - (1 + W)| ≤ r := by
    have h := Complex.abs_re_le_norm (z - c)
    rw [Complex.sub_re, hcre] at h; linarith
  have him : |z.im - τ| ≤ r := by
    have h := Complex.abs_im_le_norm (z - c)
    rw [Complex.sub_im, hcim] at h; linarith
  have hLH0 : (0 : ℝ) < Real.log (H + 1) := Real.log_pos (by linarith)
  have hLH1 : (1 : ℝ) ≤ Real.log (H + 1) := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ H + 1 by linarith)
    rwa [Real.log_exp] at h
  -- the ζ ceiling on the ball
  have hzim_lo : τ - r ≤ z.im := by linarith [(abs_le.mp him).1]
  have hzim_hi : z.im ≤ τ + r := by linarith [(abs_le.mp him).2]
  have hzimt₀ : t₀ ≤ z.im := by linarith
  have hzim_e : Real.exp 1 < z.im := by linarith
  have hzimH1 : z.im ≤ H + 1 := by linarith
  have hΘ : vkTheta (H + 1) ≤ vkTheta z.im := vkTheta_anti hzim_e hzimH1
  have hzre_lo : 1 - vkTheta z.im ≤ z.re := by
    have h := (abs_le.mp hre).1
    linarith
  have hzre_hi : z.re ≤ 3 := by linarith [(abs_le.mp hre).2]
  have hgz : ‖riemannZeta z‖ ≤ Kg * Real.log (H + 1) := by
    have h := hgrow z.re z.im hzimt₀ hzre_lo hzre_hi
    rw [Complex.re_add_im z] at h
    have hlogz : Real.log z.im ≤ Real.log (H + 1) :=
      Real.log_le_log (by linarith [Real.exp_pos (1 : ℝ)]) hzimH1
    calc ‖riemannZeta z‖ ≤ Kg * Real.log z.im := h
      _ ≤ Kg * Real.log (H + 1) := mul_le_mul_of_nonneg_left hlogz (by linarith)
  -- the ζ floor at the center
  have hτabs : (2 : ℝ) ≤ |τ| := by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ)]; linarith
  have hζc : (1 / 32 : ℝ) * W ≤ ‖riemannZeta c‖ := by
    rw [hcdef]; exact zeta_pow_lower_far hW0 hW1 hτabs
  have hζcpos : 0 < ‖riemannZeta c‖ := lt_of_lt_of_le (by positivity) hζc
  -- the pole factors
  have hcm1_im : (c - 1).im = τ := by rw [hcdef]; simp
  have hcm1_norm : τ ≤ ‖c - 1‖ := by
    have h := Complex.abs_im_le_norm (c - 1)
    rw [hcm1_im, abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ)] at h
    exact h
  have hcm1pos : 0 < ‖c - 1‖ := by linarith
  have hzm1 : ‖z - 1‖ ≤ 2 * ‖c - 1‖ := by
    have hsplit : z - 1 = (z - c) + (c - 1) := by ring
    have h1 : ‖z - 1‖ ≤ ‖z - c‖ + ‖c - 1‖ := by rw [hsplit]; exact norm_add_le _ _
    linarith
  have hz1 : z ≠ 1 := by
    intro h
    have him0 : z.im = 0 := by rw [h]; simp
    linarith
  have hcne1 : c ≠ 1 := by
    intro h
    have h1 : c.re = 1 := by rw [h]; simp
    rw [hcre] at h1; linarith
  have hZcz : ‖Zc z‖ = ‖z - 1‖ * ‖riemannZeta z‖ := by rw [Zc_eq_of_ne hz1, norm_mul]
  have hZcc : ‖Zc c‖ = ‖c - 1‖ * ‖riemannZeta c‖ := by rw [Zc_eq_of_ne hcne1, norm_mul]
  rw [norm_div, hZcz, hZcc, div_le_div_iff₀ (by positivity) hW0]
  calc ‖z - 1‖ * ‖riemannZeta z‖ * W
      ≤ (2 * ‖c - 1‖) * (Kg * Real.log (H + 1)) * W := by
        have h1 : ‖z - 1‖ * ‖riemannZeta z‖ ≤ (2 * ‖c - 1‖) * (Kg * Real.log (H + 1)) :=
          mul_le_mul hzm1 hgz (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right h1 hW0.le
    _ = 64 * Kg * Real.log (H + 1) * (‖c - 1‖ * ((1 / 32 : ℝ) * W)) := by ring
    _ ≤ 64 * Kg * Real.log (H + 1) * (‖c - 1‖ * ‖riemannZeta c‖) := by
        have h2 : ‖c - 1‖ * ((1 / 32 : ℝ) * W) ≤ ‖c - 1‖ * ‖riemannZeta c‖ :=
          mul_le_mul_of_nonneg_left hζc hcm1pos.le
        exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-! ## §3 — the two height regimes -/

set_option maxHeartbeats 1600000 in
-- The two-case dispatch threads §1's core, the two pole cancellations and the landed far floor
-- through one declaration whose `calc` chains carry degree-3 products in `‖c−1‖, W, ‖ζ c‖`; the
-- default budget dies in the left branch's closing arithmetic.
/-- **The FAR regime** (`τ ≥ max(2, t₀+1)`, `τ ≤ H`): the ball argument closes the shallow box
at `‖mmuG(σ+iτ)‖ ≤ 256/W` for the whole range `1 − W ≤ σ ≤ 2`.  Left of `1+W` it is §1's core
plus the two pole cancellations; right of `1+W` it is the landed `zeta_pow_lower_far` alone. -/
theorem norm_mmuG_shallow_far {Kg t₀ H W lam τ σ : ℝ} (hKg : 1 ≤ Kg)
    (hgrow : ∀ σ' t : ℝ, t₀ ≤ t → 1 - vkTheta t ≤ σ' → σ' ≤ 3 →
        ‖riemannZeta ((σ' : ℂ) + (t : ℂ) * I)‖ ≤ Kg * Real.log t)
    (hbox : ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 - 3 / 2 * lam ≤ ρ.re → |ρ.im| ≤ H + 1 → False)
    (hW0 : 0 < W) (hW1 : W ≤ 1) (hlam0 : 0 < lam)
    (hlam8 : 7 / 4 * lam ≤ 1 / 8) (hlamΘ : 7 / 4 * lam ≤ vkTheta (H + 1))
    (hreach : 2 * W ≤ 23 / 20 * lam)
    (hbudget : 240 * W * Real.log (4 * (64 * Kg * Real.log (H + 1) / W)) ≤ lam)
    (hτ2 : 2 ≤ τ) (hτt₀ : t₀ + 1 ≤ τ) (hτe : Real.exp 1 < τ - 1) (hτH : τ ≤ H)
    (hσlo : 1 - W ≤ σ) (hσhi : σ ≤ 2) :
    ‖mmuG ((σ : ℂ) + (τ : ℂ) * I)‖ ≤ 256 / W := by
  set c : ℂ := ((1 + W : ℝ) : ℂ) + (τ : ℂ) * I with hcdef
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * I with hsdef
  have hLH0 : (0 : ℝ) < Real.log (H + 1) := Real.log_pos (by linarith)
  have hLH1 : (1 : ℝ) ≤ Real.log (H + 1) := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ H + 1 by linarith)
    rwa [Real.log_exp] at h
  have hτabs : (2 : ℝ) ≤ |τ| := by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ)]; linarith
  have hs1 : s ≠ 1 := by
    intro h
    have him0 : s.im = 0 := by rw [h]; simp
    rw [hsdef] at him0; simp at him0; linarith
  rcases le_or_gt σ (1 + W) with hcase | hcase
  · -- ⟦LEFT of `1+W`⟧: the core
    have hM₀ : (1 : ℝ) ≤ 64 * Kg * Real.log (H + 1) / W := by
      rw [le_div_iff₀ hW0]; nlinarith
    have hball : ∀ z : ℂ, ‖z - c‖ ≤ 7 / 4 * lam →
        ‖Zc z / Zc c‖ ≤ 64 * Kg * Real.log (H + 1) / W := by
      intro z hzb
      rw [hcdef] at hzb ⊢
      exact norm_Zc_ratio_le_of_shallow_ball hKg hgrow hW0 hW1 (by positivity) hlam8
        hlamΘ hτ2 hτt₀ hτe hτH hzb
    have hzf : ∀ z : ℂ, ‖z - c‖ < 3 / 2 * lam → Zc z ≠ 0 := by
      intro z hzb
      have hcre : c.re = 1 + W := by rw [hcdef]; simp
      have hcim : c.im = τ := by rw [hcdef]; simp
      have hre : |z.re - (1 + W)| ≤ 3 / 2 * lam := by
        have h := Complex.abs_re_le_norm (z - c)
        rw [Complex.sub_re, hcre] at h; linarith
      have him : |z.im - τ| ≤ 3 / 2 * lam := by
        have h := Complex.abs_im_le_norm (z - c)
        rw [Complex.sub_im, hcim] at h; linarith
      have hzim_lo : τ - 3 / 2 * lam ≤ z.im := by linarith [(abs_le.mp him).1]
      have hzim_hi : z.im ≤ τ + 3 / 2 * lam := by linarith [(abs_le.mp him).2]
      have hz1 : z ≠ 1 := by
        intro h
        have him0 : z.im = 0 := by rw [h]; simp
        linarith
      rw [Zc_eq_of_ne hz1]
      refine mul_ne_zero (sub_ne_zero.mpr hz1) (fun hζ => hbox z hζ ?_ ?_)
      · linarith [(abs_le.mp hre).1]
      · rw [abs_le]; constructor <;> linarith
    have hcore := norm_Zc_lower_of_shallow_ball hW0 hlam0 hM₀ hreach hball hzf hbudget
      hσlo hcase
    rw [← hcdef, ← hsdef] at hcore
    have hζc : (1 / 32 : ℝ) * W ≤ ‖riemannZeta c‖ := by
      rw [hcdef]; exact zeta_pow_lower_far hW0 hW1 hτabs
    have hζcpos : 0 < ‖riemannZeta c‖ := lt_of_lt_of_le (by positivity) hζc
    have hcm1_im : (c - 1).im = τ := by rw [hcdef]; simp
    have hcm1_norm : τ ≤ ‖c - 1‖ := by
      have h := Complex.abs_im_le_norm (c - 1)
      rw [hcm1_im, abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ)] at h
      exact h
    have hcm1pos : 0 < ‖c - 1‖ := by linarith
    have hsc : ‖s - c‖ ≤ 2 * W := by
      have hsub : s - c = ((σ - (1 + W) : ℝ) : ℂ) := by
        rw [hsdef, hcdef]; push_cast; ring
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hsm1 : ‖s - 1‖ ≤ 2 * ‖c - 1‖ := by
      have hsplit : s - 1 = (s - c) + (c - 1) := by ring
      have h1 : ‖s - 1‖ ≤ ‖s - c‖ + ‖c - 1‖ := by rw [hsplit]; exact norm_add_le _ _
      linarith
    have hZcc : ‖Zc c‖ = ‖c - 1‖ * ‖riemannZeta c‖ := by
      have hcne1 : c ≠ 1 := by
        intro h
        have h1 : c.re = 1 := by rw [h]; simp
        have hcre : c.re = 1 + W := by rw [hcdef]; simp
        rw [hcre] at h1; linarith
      rw [Zc_eq_of_ne hcne1, norm_mul]
    have hZclow : ‖c - 1‖ * W / 128 ≤ ‖Zc s‖ := by
      refine le_trans ?_ hcore
      rw [hZcc, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      have h1 : ‖c - 1‖ * ((1 / 32 : ℝ) * W) ≤ ‖c - 1‖ * ‖riemannZeta c‖ :=
        mul_le_mul_of_nonneg_left hζc hcm1pos.le
      nlinarith [h1]
    have hZcspos : 0 < ‖Zc s‖ := lt_of_lt_of_le (by positivity) hZclow
    rw [mmuG, norm_div, div_le_div_iff₀ hZcspos hW0]
    calc ‖s - 1‖ * W ≤ (2 * ‖c - 1‖) * W := mul_le_mul_of_nonneg_right hsm1 hW0.le
      _ = 256 * (‖c - 1‖ * W / 128) := by ring
      _ ≤ 256 * ‖Zc s‖ := mul_le_mul_of_nonneg_left hZclow (by norm_num)
  · -- ⟦RIGHT of `1+W`⟧: the landed far floor alone
    have hd0 : 0 < σ - 1 := by linarith
    have hd1 : σ - 1 ≤ 1 := by linarith
    have hζs : (1 / 32 : ℝ) * (σ - 1) ≤ ‖riemannZeta s‖ := by
      have h := zeta_pow_lower_far hd0 hd1 hτabs
      rw [hsdef, show (σ : ℂ) = ((1 + (σ - 1) : ℝ) : ℂ) by push_cast; ring]
      exact h
    have hζspos : 0 < ‖riemannZeta s‖ := lt_of_lt_of_le (by positivity) hζs
    rw [mmuG_eq_zeta_inv' hs1, norm_inv, inv_eq_one_div, div_le_div_iff₀ hζspos hW0]
    nlinarith [hζs, hW0]

/-- **The NEAR regime** (`|τ| ≤ T₁`, `T₁` a CONSTANT): the landed `Salt.SW.zeta_inv_shallow`
verbatim.  Its classical width is a constant here, and so is its value; the near-pole corner
(including `s = 1`, where `mmuG 1 = 0`) is inside that theorem's own pole patch. -/
lemma norm_mmuG_shallow_near {c₄' C W T₁ σ τ : ℝ} (hC0 : 0 < C)
    (Hinv : ∀ σ' t : ℝ, 1 - c₄' / Real.log (|t| + 2) ^ 9 ≤ σ' →
        (σ' : ℂ) + (t : ℂ) * I ≠ 1 →
        ‖(riemannZeta ((σ' : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ C * Real.log (|t| + 2) ^ 7)
    (hc₄'0 : 0 < c₄') (hT₁ : 0 ≤ T₁) (hW : W ≤ c₄' / Real.log (T₁ + 2) ^ 9)
    (hτ : |τ| ≤ T₁) (hσ : 1 - W ≤ σ) :
    ‖mmuG ((σ : ℂ) + (τ : ℂ) * I)‖ ≤ C * Real.log (T₁ + 2) ^ 7 := by
  have hl2 : (0 : ℝ) < Real.log (|τ| + 2) := Real.log_pos (by linarith [abs_nonneg τ])
  have hlT : (0 : ℝ) < Real.log (T₁ + 2) := Real.log_pos (by linarith)
  have hmonolog : Real.log (|τ| + 2) ≤ Real.log (T₁ + 2) :=
    Real.log_le_log (by linarith [abs_nonneg τ]) (by linarith)
  by_cases hs1 : (σ : ℂ) + (τ : ℂ) * I = 1
  · rw [hs1, mmuG, sub_self, Zc_one, zero_div, norm_zero]
    positivity
  · have hmono : c₄' / Real.log (T₁ + 2) ^ 9 ≤ c₄' / Real.log (|τ| + 2) ^ 9 := by
      refine div_le_div_of_nonneg_left hc₄'0.le (by positivity) ?_
      exact pow_le_pow_left₀ hl2.le hmonolog 9
    have h := Hinv σ τ (by linarith) hs1
    rw [mmuG_eq_zeta_inv' hs1]
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ hC0.le)
    exact pow_le_pow_left₀ hl2.le hmonolog 7

/-! ## §4 — the box's ζ-zero-freeness, and the `Prop` -/

/-- **The shallow box is ζ-zero-free** — the first conjunct, a composition of landed material.
Above the power region's floor `T₀` the region itself (its width is antitone in the height, so
the value at `H+1` serves the whole box); below `T₀` the classical
`Salt.SW.zeta_zero_free_region`, whose width `c₃/log(T₀+2)` is a CONSTANT there.  Both arms are
paid by the two scale hypotheses `hdreg`, `hdcl`. -/
lemma zeta_no_zero_in_shallow_box {cR' c₃ T₀ H d : ℝ}
    (Hreg : ∀ ρ : ℂ, riemannZeta ρ = 0 → T₀ ≤ |ρ.im| →
        ρ.re ≤ 1 - cR' / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ)))
    (Hzfr : ∀ {ρ : ℂ}, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re →
        ρ.re ≤ 1 - c₃ / Real.log (|ρ.im| + 2))
    (hT₀3 : 3 ≤ T₀) (hcR'0 : 0 < cR') (hc₃0 : 0 < c₃) (hd2 : d ≤ 1 / 2)
    (hdreg : d < cR' / ((Real.log (H + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (H + 1))) ^ (3 : ℕ)))
    (hdcl : d < c₃ / Real.log (T₀ + 2))
    (hH : Real.exp (Real.exp 100) + 1 ≤ H)
    (ρ : ℂ) (hρ0 : riemannZeta ρ = 0) (hρre : 1 - d ≤ ρ.re) (hρim : |ρ.im| ≤ H + 1) : False := by
  obtain ⟨hLg, hℓ, hLgp, hLgp2, hℓp, hHe⟩ := zeta_shallow_scales hH
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hLgp0 : (0 : ℝ) < Real.log (H + 1) := by linarith
  rcases le_or_gt T₀ |ρ.im| with hhi | hlo
  · -- ⟦above the VK floor⟧
    have hima : (3 : ℝ) ≤ |ρ.im| := le_trans hT₀3 hhi
    have hL3 : (1 : ℝ) < Real.log |ρ.im| := by
      have h1 : Real.log 3 ≤ Real.log |ρ.im| := Real.log_le_log (by norm_num) hima
      have h2 : (1 : ℝ) < Real.log 3 := by
        have h := Real.log_lt_log (Real.exp_pos 1)
          (show Real.exp 1 < 3 by linarith [Real.exp_one_lt_d9])
        rwa [Real.log_exp] at h
      linarith
    have hLmono : Real.log |ρ.im| ≤ Real.log (H + 1) :=
      Real.log_le_log (by linarith) hρim
    have hℓmono : Real.log (Real.log |ρ.im|) ≤ Real.log (Real.log (H + 1)) :=
      Real.log_le_log (by linarith) hLmono
    have hℓ0 : (0 : ℝ) < Real.log (Real.log |ρ.im|) := Real.log_pos hL3
    have hR0 : (0 : ℝ) < (Real.log |ρ.im|) ^ ((3 : ℝ) / 4) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hRmono : (Real.log |ρ.im|) ^ ((3 : ℝ) / 4) ≤ (Real.log (H + 1)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (by linarith) hLmono (by norm_num)
    have hR'0 : (0 : ℝ) < (Real.log (H + 1)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_pos_of_pos hLgp0 _
    have hden : (Real.log |ρ.im|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ)
        ≤ (Real.log (H + 1)) ^ ((3 : ℝ) / 4) * (Real.log (Real.log (H + 1))) ^ (3 : ℕ) :=
      mul_le_mul hRmono (pow_le_pow_left₀ hℓ0.le hℓmono 3) (by positivity) hR'0.le
    have hstep : cR' / ((Real.log (H + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (H + 1))) ^ (3 : ℕ))
        ≤ cR' / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ)) :=
      div_le_div_of_nonneg_left hcR'0.le (by positivity) hden
    linarith [Hreg ρ hρ0 hhi, hstep, hdreg]
  · -- ⟦below the VK floor: the classical region⟧
    have hlogpos : (0 : ℝ) < Real.log (|ρ.im| + 2) :=
      Real.log_pos (by linarith [abs_nonneg ρ.im])
    have hlogT : Real.log (|ρ.im| + 2) ≤ Real.log (T₀ + 2) :=
      Real.log_le_log (by linarith [abs_nonneg ρ.im]) (by linarith)
    have hlogT0 : (0 : ℝ) < Real.log (T₀ + 2) := by linarith
    have hmono : c₃ / Real.log (T₀ + 2) ≤ c₃ / Real.log (|ρ.im| + 2) :=
      div_le_div_of_nonneg_left hc₃0.le hlogpos hlogT
    have hhalf : 1 / 2 ≤ ρ.re := by linarith
    linarith [Hzfr hρ0 hhalf, hmono, hdcl]

set_option maxHeartbeats 4000000 in
-- The discharge threads FOUR nested scale ladders (the `H` vs `H+1` log pair, the rpow `3/4`
-- factor, the region/`vkTheta` widths and the budget's `log(4M₀)`) through one assembly; the
-- elaborator needs the same headroom `norm_LFunction_inv_shallow_sharp` takes.
/-- **⟦THE ζ SHALLOW STONE, DISCHARGED⟧.**  `Salt.MR.ZetaInvShallowVk` holds, with `m = 5`:

* the box zero-free conjunct from `Salt.Vk.zeta_zero_free_region_pow` (above the floor) and
  `Salt.SW.zeta_zero_free_region` (below it);
* the shallow bound from `Salt.SW.zeta_inv_shallow` at heights `|τ| ≤ T₁` and from the `Zc`
  Landau ball (`norm_Zc_lower_of_shallow_ball`, growth `Salt.Vk.zeta_growth_pow`, floor
  `Salt.MR.zeta_pow_lower_far`) above them; negative heights by `Zc_conj`.

No new axioms, no `sorry`, no Jensen zero count — and no re-proof of the private
`zeta_near_bound_core`: the near-pole corner is `Salt.SW.zeta_inv_shallow`'s own pole patch. -/
theorem zetaInvShallowVk_holds : ZetaInvShallowVk := by
  obtain ⟨cR', T₀, hcR'0, hT₀3, Hreg⟩ := pow_region_width
  obtain ⟨Kg, t₀, hKg, ht₀3, Hgrow⟩ := Salt.Vk.zeta_growth_pow
  obtain ⟨c₃, hc₃0, Hzfr⟩ := Salt.SW.zeta_zero_free_region
  obtain ⟨c₄', hc₄'0, C, hC0, Hinv⟩ := Salt.SW.zeta_inv_shallow
  have hlogT₀ : (0 : ℝ) < Real.log (T₀ + 2) := Real.log_pos (by linarith)
  set T₁ : ℝ := T₀ + t₀ + 4 with hT₁def
  have hT₁10 : (10 : ℝ) ≤ T₁ := by rw [hT₁def]; linarith
  have hlogT₁ : (0 : ℝ) < Real.log (T₁ + 2) := Real.log_pos (by linarith)
  -- the region-scale constant, carrying the classical arm's constraint
  set cR : ℝ := min 1 (min cR' (c₃ / (2 * Real.log (T₀ + 2)))) with hcRdef
  have hcR0 : 0 < cR := by
    rw [hcRdef]; exact lt_min zero_lt_one (lt_min hcR'0 (by positivity))
  have hcR1 : cR ≤ 1 := by rw [hcRdef]; exact min_le_left _ _
  have hcRreg : cR ≤ cR' := le_trans (by rw [hcRdef]; exact min_le_right _ _) (min_le_left _ _)
  have hcRcl : cR ≤ c₃ / (2 * Real.log (T₀ + 2)) :=
    le_trans (by rw [hcRdef]; exact min_le_right _ _) (min_le_right _ _)
  -- the gate
  set A : ℝ := 675 + Real.log (512 * Kg) with hAdef
  have hA1 : 1 ≤ A := by
    have h : (0 : ℝ) ≤ Real.log (512 * Kg) := Real.log_nonneg (by nlinarith)
    rw [hAdef]; linarith
  set B : ℝ := min 1 (min (cR / 10 ^ 6) (c₄' / Real.log (T₁ + 2) ^ 9)) with hBdef
  have hB0 : 0 < B := by
    rw [hBdef]; exact lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hB1 : B ≤ 1 := by rw [hBdef]; exact min_le_left _ _
  have hBcR : B ≤ cR / 10 ^ 6 :=
    le_trans (by rw [hBdef]; exact min_le_right _ _) (min_le_left _ _)
  have hBnear : B ≤ c₄' / Real.log (T₁ + 2) ^ 9 :=
    le_trans (by rw [hBdef]; exact min_le_right _ _) (min_le_right _ _)
  obtain ⟨c₄, hc₄0, hc₄B, hgate⟩ := exists_zetaShallowGate hA1 hB0 hB1
  have hc₄1 : c₄ ≤ 1 := le_trans hc₄B hB1
  have hc₄cR : c₄ ≤ cR / 10 ^ 6 := le_trans hc₄B hBcR
  refine ⟨c₄, 256 / c₄ + C * Real.log (T₁ + 2) ^ 7, 5, hc₄0, by positivity, ?_⟩
  intro H hH
  obtain ⟨hLg, hℓ, hLgp, hLgp2, hℓp, hHe⟩ := zeta_shallow_scales hH
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hWval : vkShallowWidthSharp c₄ 1 H
      = c₄ / (Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (4 : ℕ)) :=
    vkShallowWidthSharp_one c₄ H
  set Lg : ℝ := Real.log H with hLdef
  set ℓ : ℝ := Real.log Lg with hℓdef
  set R : ℝ := Lg ^ ((3 : ℝ) / 4) with hRdef
  have hL0 : (0 : ℝ) < Lg := by linarith
  have hL1 : (1 : ℝ) ≤ Lg := by linarith
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hR0 : (0 : ℝ) < R := by rw [hRdef]; exact Real.rpow_pos_of_pos hL0 _
  have hR1 : (1 : ℝ) ≤ R := by rw [hRdef]; exact Real.one_le_rpow hL1 (by norm_num)
  have hRL : R ≤ Lg := by
    rw [hRdef]
    have h := Real.rpow_le_rpow_of_exponent_le hL1 (show (3 : ℝ) / 4 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hℓLg : ℓ ≤ Lg := by rw [hℓdef]; linarith [Real.log_le_sub_one_of_pos hL0]
  have hLH0 : (0 : ℝ) < Real.log (H + 1) := by linarith
  have hlogR : Real.log R = 3 / 4 * ℓ := by rw [hRdef, Real.log_rpow hL0, ← hℓdef]
  -- the widths
  set W : ℝ := c₄ / (R * ℓ ^ (4 : ℕ)) with hWdef
  have hRℓ40 : (0 : ℝ) < R * ℓ ^ (4 : ℕ) := by positivity
  have hRℓ41 : (1 : ℝ) ≤ R * ℓ ^ (4 : ℕ) := by
    have h1 : (1 : ℝ) ≤ ℓ ^ (4 : ℕ) := one_le_pow₀ (by linarith)
    nlinarith
  have hW0 : 0 < W := by rw [hWdef]; positivity
  have hWc₄ : W ≤ c₄ := by rw [hWdef, div_le_iff₀ hRℓ40]; nlinarith
  have hW1 : W ≤ 1 := by linarith
  set lam : ℝ := cR / (10 ^ 5 * (R * ℓ ^ (3 : ℕ))) with hlamdef
  have hRℓ30 : (0 : ℝ) < R * ℓ ^ (3 : ℕ) := by positivity
  have hRℓ31 : (1 : ℝ) ≤ R * ℓ ^ (3 : ℕ) := by
    have h1 : (1 : ℝ) ≤ ℓ ^ (3 : ℕ) := one_le_pow₀ (by linarith)
    nlinarith
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  have hlamsmall : lam ≤ cR / 10 ^ 5 := by
    rw [hlamdef]
    exact div_le_div_of_nonneg_left hcR0.le (by norm_num) (by nlinarith)
  have hlam8 : 7 / 4 * lam ≤ 1 / 8 := by
    have h2 : cR / 10 ^ 5 ≤ 1 / 10 ^ 5 := by linarith
    linarith
  -- ⟦the growth strip⟧
  have hR'0 : (0 : ℝ) < Real.log (H + 1) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hLH0 _
  have hm'0 : (0 : ℝ) < Real.log (Real.log (H + 1)) := Real.log_pos (by linarith)
  have hR'2R : Real.log (H + 1) ^ ((3 : ℝ) / 4) ≤ 2 * R := by
    have h1 : Real.log (H + 1) ^ ((3 : ℝ) / 4) ≤ (2 * Lg) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hLH0.le hLgp2 (by norm_num)
    have h2 : (2 * Lg) ^ ((3 : ℝ) / 4) = 2 ^ ((3 : ℝ) / 4) * R := by
      rw [hRdef, Real.mul_rpow (by norm_num) hL0.le]
    have h3 : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show (3 : ℝ) / 4 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    rw [h2] at h1
    nlinarith [h1, h3, hR0]
  have hlamΘ : 7 / 4 * lam ≤ vkTheta (H + 1) := by
    have hstepa : 7 / 4 * lam ≤ 1 / (10 ^ 4 * (R * ℓ ^ (3 : ℕ))) := by
      rw [hlamdef, show (7 : ℝ) / 4 * (cR / (10 ^ 5 * (R * ℓ ^ (3 : ℕ))))
          = 7 * cR / (4 * (10 ^ 5 * (R * ℓ ^ (3 : ℕ)))) by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hcR1, hRℓ30, hcR0]
    have hm'sq : Real.log (Real.log (H + 1)) ^ (2 : ℕ) ≤ 4 * ℓ ^ (2 : ℕ) := by
      have h := pow_le_pow_left₀ hm'0.le hℓp 2
      calc Real.log (Real.log (H + 1)) ^ (2 : ℕ) ≤ (2 * ℓ) ^ (2 : ℕ) := h
        _ = 4 * ℓ ^ (2 : ℕ) := by ring
    have hstepb : 1 / (10 ^ 4 * (R * ℓ ^ (3 : ℕ))) ≤ vkTheta (H + 1) := by
      rw [vkTheta, div_le_div_iff₀ (by positivity) (by positivity)]
      have hprod : Real.log (H + 1) ^ ((3 : ℝ) / 4)
            * Real.log (Real.log (H + 1)) ^ (2 : ℕ) ≤ (2 * R) * (4 * ℓ ^ (2 : ℕ)) :=
        mul_le_mul hR'2R hm'sq (by positivity) (by linarith)
      nlinarith [hprod, hR0, hℓ0, hℓ,
        mul_nonneg (mul_nonneg hR0.le (pow_nonneg hℓ0.le 2))
          (by linarith : (0 : ℝ) ≤ 10 * ℓ - 8)]
    linarith
  -- ⟦the reach⟧
  have hreach : 2 * W ≤ 23 / 20 * lam := by
    have hkey : 2 * W ≤ lam := by
      rw [hWdef, hlamdef, show (2 : ℝ) * (c₄ / (R * ℓ ^ (4 : ℕ)))
          = 2 * c₄ / (R * ℓ ^ (4 : ℕ)) by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have s1 : 2 * 10 ^ 5 * c₄ ≤ cR := by linarith
      have s2 : (0 : ℝ) ≤ cR * ℓ - 2 * 10 ^ 5 * c₄ := by
        nlinarith [mul_nonneg hcR0.le (by linarith : (0 : ℝ) ≤ ℓ - 100), s1]
      nlinarith [mul_nonneg (mul_nonneg hR0.le (pow_nonneg hℓ0.le 3)) s2]
    linarith
  -- ⟦the budget⟧
  have hxub : 4 * (64 * Kg * Real.log (H + 1) / W)
      ≤ 512 * Kg * Lg * (R * ℓ ^ (4 : ℕ)) / c₄ := by
    have heq : 4 * (64 * Kg * Real.log (H + 1) / W)
        = 256 * Kg * Real.log (H + 1) * (R * ℓ ^ (4 : ℕ)) / c₄ := by
      rw [hWdef]; field_simp; ring
    rw [heq, div_le_div_iff_of_pos_right hc₄0]
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 256 * Kg) hRℓ40.le)
      (by linarith : (0 : ℝ) ≤ 2 * Lg - Real.log (H + 1))]
  have hlogbudget : Real.log (4 * (64 * Kg * Real.log (H + 1) / W))
      ≤ (A + Real.log (1 / c₄)) * ℓ / 100 := by
    rw [hAdef]
    exact zeta_budget_log_bound hKg hc₄0 hc₄1 hℓ hL0 hℓdef.symm hR0 hlogR
      (by positivity) hxub
  have hbudget : 240 * W * Real.log (4 * (64 * Kg * Real.log (H + 1) / W)) ≤ lam := by
    have h1 : 240 * W * Real.log (4 * (64 * Kg * Real.log (H + 1) / W))
        ≤ 240 * W * ((A + Real.log (1 / c₄)) * ℓ / 100) :=
      mul_le_mul_of_nonneg_left hlogbudget (by positivity)
    refine le_trans h1 ?_
    have hident : 240 * W * ((A + Real.log (1 / c₄)) * ℓ / 100)
        = 12 * (c₄ * (A + Real.log (1 / c₄))) / (5 * (R * ℓ ^ (3 : ℕ))) := by
      rw [hWdef]
      have hRne : R ≠ 0 := ne_of_gt hR0
      have hℓne : ℓ ≠ 0 := ne_of_gt hℓ0
      field_simp
      ring
    rw [hident, hlamdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have hg : c₄ * (A + Real.log (1 / c₄)) ≤ cR / 10 ^ 6 := le_trans hgate hBcR
    nlinarith [mul_nonneg hRℓ30.le
      (by linarith : (0 : ℝ) ≤ 5 * cR - 12 * 10 ^ 5 * (c₄ * (A + Real.log (1 / c₄))))]
  -- ⟦the box⟧
  have hdreg : 3 / 2 * lam < cR' / (Real.log (H + 1) ^ ((3 : ℝ) / 4)
      * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) := by
    have hm'3 : Real.log (Real.log (H + 1)) ^ (3 : ℕ) ≤ 8 * ℓ ^ (3 : ℕ) := by
      have h := pow_le_pow_left₀ hm'0.le hℓp 3
      calc Real.log (Real.log (H + 1)) ^ (3 : ℕ) ≤ (2 * ℓ) ^ (3 : ℕ) := h
        _ = 8 * ℓ ^ (3 : ℕ) := by ring
    have hden16 : Real.log (H + 1) ^ ((3 : ℝ) / 4)
        * Real.log (Real.log (H + 1)) ^ (3 : ℕ) ≤ 16 * (R * ℓ ^ (3 : ℕ)) := by
      have h : Real.log (H + 1) ^ ((3 : ℝ) / 4) * Real.log (Real.log (H + 1)) ^ (3 : ℕ)
          ≤ (2 * R) * (8 * ℓ ^ (3 : ℕ)) :=
        mul_le_mul hR'2R hm'3 (by positivity) (by linarith)
      nlinarith [h]
    have hstep1 : cR / (16 * (R * ℓ ^ (3 : ℕ)))
        ≤ cR' / (Real.log (H + 1) ^ ((3 : ℝ) / 4)
          * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) := by
      calc cR / (16 * (R * ℓ ^ (3 : ℕ)))
          ≤ cR / (Real.log (H + 1) ^ ((3 : ℝ) / 4)
            * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) :=
            div_le_div_of_nonneg_left hcR0.le (by positivity) hden16
        _ ≤ cR' / (Real.log (H + 1) ^ ((3 : ℝ) / 4)
            * Real.log (Real.log (H + 1)) ^ (3 : ℕ)) := by
            rw [div_le_div_iff_of_pos_right (by positivity)]; exact hcRreg
    have hstep2 : 3 / 2 * lam < cR / (16 * (R * ℓ ^ (3 : ℕ))) := by
      rw [hlamdef, show (3 : ℝ) / 2 * (cR / (10 ^ 5 * (R * ℓ ^ (3 : ℕ))))
          = 3 * cR / (2 * (10 ^ 5 * (R * ℓ ^ (3 : ℕ)))) by ring,
        div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hcR0 hRℓ30]
    linarith
  have hdcl : 3 / 2 * lam < c₃ / Real.log (T₀ + 2) := by
    have h4 : c₃ / (2 * Real.log (T₀ + 2)) = c₃ / Real.log (T₀ + 2) / 2 := by
      rw [div_div]; ring
    have hG0 : (0 : ℝ) < c₃ / Real.log (T₀ + 2) := by positivity
    rw [h4] at hcRcl
    have h5 : cR / 10 ^ 5 ≤ c₃ / Real.log (T₀ + 2) / 2 / 10 ^ 5 := by linarith
    linarith
  have hbox : ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 - 3 / 2 * lam ≤ ρ.re →
      |ρ.im| ≤ H + 1 → False := by
    intro ρ hρ0 hρre hρim
    exact zeta_no_zero_in_shallow_box Hreg Hzfr hT₀3 hcR'0 hc₃0 (by linarith) hdreg hdcl hH
      ρ hρ0 hρre hρim
  -- ⟦the two conjuncts⟧
  have hT₁t₀ : t₀ + 7 ≤ T₁ := by rw [hT₁def]; linarith
  have hL5 : (1 : ℝ) ≤ Lg ^ (5 : ℕ) := one_le_pow₀ hL1
  have hKpos : (0 : ℝ) < 256 / c₄ := by positivity
  have hCT : (0 : ℝ) ≤ C * Real.log (T₁ + 2) ^ 7 := by positivity
  have h256 : 256 / W ≤ 256 / c₄ * Lg ^ (5 : ℕ) := by
    rw [hWdef, div_div_eq_mul_div, div_le_iff₀ hc₄0]
    have hcancel : 256 / c₄ * Lg ^ (5 : ℕ) * c₄ = 256 * Lg ^ (5 : ℕ) := by field_simp
    rw [hcancel]
    have hRℓ4L : R * ℓ ^ (4 : ℕ) ≤ Lg ^ (5 : ℕ) := by
      have h1 : ℓ ^ (4 : ℕ) ≤ Lg ^ (4 : ℕ) := pow_le_pow_left₀ hℓ0.le hℓLg 4
      calc R * ℓ ^ (4 : ℕ) ≤ Lg * Lg ^ (4 : ℕ) :=
            mul_le_mul hRL h1 (by positivity) (by linarith)
        _ = Lg ^ (5 : ℕ) := by ring
    linarith
  have hshape : 256 / c₄ * Lg ^ (5 : ℕ)
      ≤ (256 / c₄ + C * Real.log (T₁ + 2) ^ 7) * Lg ^ (5 : ℕ) := by
    nlinarith [mul_nonneg hCT (pow_nonneg hL0.le 5)]
  rw [hWval]
  refine ⟨?_, ?_⟩
  · -- ⟦conjunct 1: the box is ζ-zero-free⟧
    intro ρ hρ0 hρre hρim
    exact hbox ρ hρ0 (by linarith) (by linarith)
  · -- ⟦conjunct 2: the shallow bound⟧
    intro σ τ hσlo hσhi hτH
    have hfar : ∀ v : ℝ, T₁ ≤ v → v ≤ H → ‖mmuG ((σ : ℂ) + (v : ℂ) * I)‖ ≤ 256 / W := by
      intro v hv1 hv2
      exact norm_mmuG_shallow_far hKg Hgrow hbox hW0 hW1 hlam0 hlam8 hlamΘ hreach hbudget
        (by linarith) (by linarith) (by linarith [Real.exp_one_lt_d9]) hv2 hσlo hσhi
    rcases le_or_gt |τ| T₁ with hnear | hfarcase
    · -- the near regime: the landed classical-width bound, at constant height
      have h := norm_mmuG_shallow_near hC0 Hinv hc₄'0 (by linarith)
        (le_trans hWc₄ (le_trans hc₄B hBnear)) hnear hσlo
      have hstep : C * Real.log (T₁ + 2) ^ 7
          ≤ (256 / c₄ + C * Real.log (T₁ + 2) ^ 7) * Lg ^ (5 : ℕ) := by
        nlinarith [mul_nonneg
          (by positivity : (0 : ℝ) ≤ 256 / c₄ + C * Real.log (T₁ + 2) ^ 7)
          (by linarith : (0 : ℝ) ≤ Lg ^ (5 : ℕ) - 1)]
      linarith
    · -- the far regime, both signs of the height
      rcases le_or_gt 0 τ with hsign | hsign
      · have habs : |τ| = τ := abs_of_nonneg hsign
        have hτT₁ : T₁ ≤ τ := by rw [habs] at hfarcase; linarith
        have hτH' : τ ≤ H := by rw [habs] at hτH; exact hτH
        exact le_trans (le_trans (hfar τ hτT₁ hτH') h256) hshape
      · have habs : |τ| = -τ := abs_of_neg hsign
        have hτT₁ : T₁ ≤ -τ := by rw [habs] at hfarcase; linarith
        have hτH' : -τ ≤ H := by rw [habs] at hτH; exact hτH
        have hsym : ‖mmuG ((σ : ℂ) + (τ : ℂ) * I)‖
            = ‖mmuG ((σ : ℂ) + ((-τ : ℝ) : ℂ) * I)‖ := by
          have h := norm_mmuG_neg_im σ (-τ)
          rw [neg_neg] at h
          exact h
        rw [hsym]
        exact le_trans (le_trans (hfar (-τ) hτT₁ hτH') h256) hshape

/-! ## §5 — the mirror's chain, fired -/

/-- The χ₀ row, unconditionally: `MmuChiRatePrincipal` from the landed mirror plus §4's stone. -/
theorem mmuChiRatePrincipal_holds : MmuChiRatePrincipal :=
  mmuChiRatePrincipal_of_zetaShallow zetaInvShallowVk_holds

/-- **The mirror's deliverable at ONE input.**  `MmuChiRate` now needs only the ξ₁/Siegel
carve-out (wave P-7's fold): the ζ shallow stone is discharged. -/
theorem mmuChiRate_of_carve
    (hxi : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ ρ : ℂ, LFunction χ⁻¹ ρ = 0 → ρ.im = 0 → ρ.re < 1 / 2) : MmuChiRate :=
  mmuChiRate_of_carve_and_zetaShallow hxi zetaInvShallowVk_holds

/-- The O3 bridge at ONE input. -/
theorem lambdaChiSummatory_of_carve
    (hxi : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ ρ : ℂ, LFunction χ⁻¹ ρ = 0 → ρ.im = 0 → ρ.re < 1 / 2)
    (A : ℝ) (hA : 0 < A) : LambdaChiSummatory A :=
  lambdaChiSummatory_of_carve_and_zetaShallow hxi zetaInvShallowVk_holds A hA

end Salt.MR

end
