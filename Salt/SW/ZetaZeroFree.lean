/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.ZeroFree
import Salt.SW.ZetaPartialFractions

/-!
# The SW rung, node S3f — the quantitative ζ zero-free region (de la Vallée Poussin)

Design: `docs/blueprints/sw.md`, wave S3; the flag "SW S3f" in `docs/blueprints/flags.md`.
This module lands the classical zero-free region for the Riemann ζ-function — the `q = 1`
instance that S3d (`Salt/SW/ZeroFree.lean`, `zero_free_region`, stated for `χ ≠ 1`) does not
cover — which the S5c χ₀ contour variant and S6's χ₀ main term are gated on.

## The two differences from the Dirichlet case (S3d/S3d-b)

Every slot of the 3-4-1 `ζ³·|ζ(σ+iγ)|⁴·|ζ(σ+2iγ)|` is `ζ` itself, so **the pole at `s = 1`
appears in all three carriers**, including the `γ`-slot (with coefficient `4`). Bounding that
extra pole term `4·Re(1/(σ+iγ−1))` by `1/(σ−1)` is fatal for small `|γ|` (the conjugate-zero
trick of `ZeroFreeReal` cannot compensate a coefficient-`4` pole). The honest split is therefore
on the *height* `|γ|`, not on `|γ|` vs `σ−1`:

1. **`|γ| ≥ 1`** — the pole terms are tiny (`Re(1/(σ+iγ−1)) ≤ 1/‖s−1‖ ≤ 1/|γ| ≤ 1`), so the
   plain keep-one 3-4-1 closes: `4/(σ−β) ≤ 3/(σ−1) + 5408·L` gives `1−β ≥ dd/(7L)`.
2. **`|γ| ≤ 1`** — a *fixed* zero-free strip `Re ρ ≤ 1 − ε₀`, obtained by compactness: the
   Re = 1 segment `{1 + it : |t| ≤ 1}` is a positive distance `ε₀` from the closed zero set
   (`isClosed_riemannZetaZeros`), which is disjoint from it by `riemannZeta_ne_zero_of_one_le_re`.
   This covers the real zeros (`γ = 0`) too.

Combining with `c₃ = min(1/75712, ε₀·log 2)` yields the region uniform in `γ`.

## Machinery consumed
* Z2ζ (`ZetaPartialFractions`): `Zc`, `entire_norm_logDeriv_sub_sum'`, `neg_logDeriv_zeta_split`,
  `zeta_neg_re_logDeriv_le` (drop-all at `σ+2iγ`), `M0zeta`/`Zc_sphere_bound`/`Zc_center_lower`.
* S3c (`ZetaPole`): `neg_logDeriv_zeta_le` (real-`σ` pole bound).
* S3a (`ThreeFourOne`): `three_four_one_logDeriv` at the trivial character mod `1`.
* S3d (`ZeroFree`): `neg_logDeriv_LSeries_eq`, `neg_re_logDeriv_le`, `term_re_nonneg`,
  `zero_free_extraction`.
* Mathlib: `LFunction_modOne_eq` (`ζ = L(·, 1 mod 1)`), `riemannZeta_ne_zero_of_one_le_re`,
  `isClosed_riemannZetaZeros`, `riemannZeta_neg_two_mul_nat_add_one`, `Metric.infDist` API.
-/

namespace Salt.SW

open Complex DirichletCharacter Filter Metric
open scoped LSeries.notation Topology

/-! ## 1. A ball-zero lies in the partial-fraction zero set (generic base) -/

/-- The `mem_zeros_of_factorization` mechanism for an arbitrary base function `F` (not just a
Dirichlet `LFunction`): any zero `ρ` of `F` inside the ball, where `F = P·h` with `h`
non-vanishing, lies in the finite zero set `Z` with multiplicity `≥ 1`. -/
lemma mem_zeros_of_factorization_gen {F h : ℂ → ℂ} {c : ℂ} {r : ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (hne_h : ∀ z ∈ ball c r, h z ≠ 0)
    (hEqOn : Set.EqOn F (fun z => (∏ ρ' ∈ Z, (z - ρ') ^ (m ρ')) * h z) (ball c r))
    {ρ : ℂ} (hρball : ρ ∈ ball c r) (hρ0 : F ρ = 0) :
    ρ ∈ Z ∧ 1 ≤ m ρ := by
  have hval : F ρ = (∏ ρ' ∈ Z, (ρ - ρ') ^ (m ρ')) * h ρ := hEqOn hρball
  rw [hρ0] at hval
  have hhρ : h ρ ≠ 0 := hne_h ρ hρball
  have hP0 : (∏ ρ' ∈ Z, (ρ - ρ') ^ (m ρ')) = 0 :=
    (mul_eq_zero.mp hval.symm).resolve_right hhρ
  rw [Finset.prod_eq_zero_iff] at hP0
  obtain ⟨ρ', hρ'Z, hpow⟩ := hP0
  rw [pow_eq_zero_iff'] at hpow
  obtain ⟨hsub, hm⟩ := hpow
  have hρeq : ρ = ρ' := by rwa [sub_eq_zero] at hsub
  subst hρeq
  exact ⟨hρ'Z, Nat.one_le_iff_ne_zero.mpr hm⟩

/-! ## 2. The `O(log)` collapse of the ζ growth quantity at height `t₀` -/

/-- `log(4·M₀ζ(t₀)) ≤ 9·log(|t₀|+2)` — the `t₀`-diagonal collapse (`4 M₀ζ(t₀) ≤ 100(|t₀|+2)²`,
`log 100 ≤ 7 log 2 ≤ 7 log(|t₀|+2)`). Companion to `log_4M0zeta_le` (the `2γ` instance). -/
lemma log_4M0zeta_le_self (t₀ : ℝ) :
    Real.log (4 * M0zeta t₀) ≤ 9 * Real.log (|t₀| + 2) := by
  have hx : (0 : ℝ) ≤ |t₀| := abs_nonneg t₀
  have hbound4 : 4 * M0zeta t₀ ≤ 100 * (|t₀| + 2) ^ 2 := by rw [M0zeta]; nlinarith [hx]
  have hM0pos : (0 : ℝ) < 4 * M0zeta t₀ := by have := one_le_M0zeta t₀; linarith
  have hlog2le : Real.log 2 ≤ Real.log (|t₀| + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hlog100 : Real.log 100 ≤ 7 * Real.log (|t₀| + 2) := by
    have h128 : Real.log 100 ≤ 7 * Real.log 2 := by
      rw [show (7 : ℝ) * Real.log 2 = Real.log (2 ^ (7 : ℕ)) by rw [Real.log_pow]; push_cast; ring]
      exact Real.log_le_log (by norm_num) (by norm_num)
    linarith
  calc Real.log (4 * M0zeta t₀) ≤ Real.log (100 * (|t₀| + 2) ^ 2) :=
        Real.log_le_log hM0pos hbound4
    _ = Real.log 100 + 2 * Real.log (|t₀| + 2) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    _ ≤ 9 * Real.log (|t₀| + 2) := by linarith [hlog100]

/-! ## 3. The keep-one ζ log-derivative bound at `s = σ + iγ` -/

/-- **The retained-zero ζ bound.** For a zero `ρ` of `ζ` with `1/2 < Re ρ < 1` and `1 < σ < 2`,
at `s = σ + i·Im ρ` the zero `ρ` lies in the `Zc` partial-fraction set, so its positive term
`1/(σ − Re ρ)` is retained:
`Re(−ζ'/ζ(s)) ≤ Re(1/(s−1)) + 1080·log(|Im ρ|+2) − 1/(σ − Re ρ)`.
The mirror of `neg_reLogDeriv_le_keep` for `ζ` via the pole split `−ζ'/ζ = 1/(s−1) − Zc'/Zc`. -/
theorem zeta_neg_re_logDeriv_le_keep {ρ : ℂ} (hρ0 : riemannZeta ρ = 0)
    (hβlt : 1 / 2 < ρ.re) (hβ1 : ρ.re < 1) {σ : ℝ} (h1 : 1 < σ) (h2 : σ < 2) :
    (-logDeriv riemannZeta ((σ : ℂ) + (ρ.im : ℂ) * I)).re
      ≤ (1 / (((σ : ℂ) + (ρ.im : ℂ) * I) - 1)).re + 1080 * Real.log (|ρ.im| + 2)
        - 1 / (σ - ρ.re) := by
  set γ : ℝ := ρ.im with hγ
  set s : ℂ := (σ : ℂ) + (γ : ℂ) * I with hs
  set c : ℂ := 2 + (γ : ℂ) * I with hc
  have hsre : s.re = σ := by rw [hs]; simp [Complex.add_re, Complex.mul_re]
  have hσC : (1 : ℝ) < s.re := by rw [hsre]; exact h1
  have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hσC; norm_num at hσC
  have hζs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hσC)
  have hsplit := neg_logDeriv_zeta_split hs_ne1 hζs
  have hsphere74 : ∀ z ∈ sphere c (7 / 4), ‖Zc z‖ ≤ M0zeta γ := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz; exact Zc_sphere_bound γ (le_refl _) hz
  have hsphere32 : ∀ z ∈ sphere c (3 / 2), ‖Zc z‖ ≤ M0zeta γ := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz; exact Zc_sphere_bound γ (by norm_num) hz
  obtain ⟨Z, m, h, hmemb, -, hne_h, hEqOn, -, hnum⟩ :=
    entire_norm_logDeriv_sub_sum' Zc_differentiable (one_le_M0zeta γ) (Zc_center_lower γ)
      hsphere74 hsphere32
  have hscnorm : ‖s - c‖ ≤ 23 / 20 := by
    have hsub : s - c = ((σ - 2 : ℝ) : ℂ) := by rw [hs, hc]; push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    linarith
  have hZcs : Zc s ≠ 0 := by
    rw [Zc_eq_of_ne hs_ne1]; exact mul_ne_zero (sub_ne_zero.mpr hs_ne1) hζs
  have hre := neg_re_logDeriv_le (hnum s hscnorm hZcs)
  -- `ρ` is a zero of `Zc` inside the ball
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hβ1; norm_num at hβ1
  have hZcρ : Zc ρ = 0 := by rw [Zc_eq_of_ne hρ1, hρ0, mul_zero]
  have hρball : ρ ∈ ball c (3 / 2) := by
    rw [mem_ball, dist_eq_norm]
    have hsub : ρ - c = ((ρ.re - 2 : ℝ) : ℂ) := by
      rw [hc, hγ]; apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : ρ.re - 2 ≤ 0)]
    linarith
  obtain ⟨hρZ, hmρ⟩ := mem_zeros_of_factorization_gen hne_h hEqOn hρball hZcρ
  have hpos : ∀ ρ' ∈ Z, 0 < (s - ρ').re := by
    intro ρ' hρ'
    have hρ'0 : Zc ρ' = 0 := (hmemb ρ' hρ').2
    have hρ'1 : ρ' ≠ 1 := fun h => by rw [h, Zc_one] at hρ'0; exact one_ne_zero hρ'0
    have hζρ' : riemannZeta ρ' = 0 := by
      rw [Zc_eq_of_ne hρ'1] at hρ'0
      exact (mul_eq_zero.mp hρ'0).resolve_left (sub_ne_zero.mpr hρ'1)
    have hlt : ρ'.re < 1 := by
      by_contra hcn; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcn) hζρ'
    rw [Complex.sub_re]; linarith [hσC]
  have hsρ : s - ρ = ((σ - ρ.re : ℝ) : ℂ) := by
    rw [hs, hγ]; apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
  have hσρpos : 0 < σ - ρ.re := by linarith
  have hterm_re : (1 / (s - ρ)).re = 1 / (σ - ρ.re) := by
    rw [hsρ, show (1 : ℂ) / ((σ - ρ.re : ℝ) : ℂ) = (((1 / (σ - ρ.re)) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have hsingle : (m ρ : ℝ) * (1 / (s - ρ)).re ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re :=
    Finset.single_le_sum (term_re_nonneg m hpos) hρZ
  have hlow : 1 / (σ - ρ.re) ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re := by
    have hm1 : (1 : ℝ) ≤ (m ρ : ℝ) := by exact_mod_cast hmρ
    have hnn : (0 : ℝ) ≤ 1 / (σ - ρ.re) := by positivity
    have h3 : 1 / (σ - ρ.re) ≤ (m ρ : ℝ) * (1 / (s - ρ)).re := by rw [hterm_re]; nlinarith
    linarith [h3, hsingle]
  have hcollapse : 120 * Real.log (4 * M0zeta γ) ≤ 1080 * Real.log (|γ| + 2) := by
    linarith [log_4M0zeta_le_self γ]
  rw [hsplit]
  linarith [hre, hlow, hcollapse]

/-! ## 4. The fixed zero-free strip near the real axis (`|Im ρ| ≤ 1`) -/

/-- **The fixed zero-free strip.** There is `ε₀ > 0` with `Re ρ ≤ 1 − ε₀` for every zero `ρ` of
`ζ` with `|Im ρ| ≤ 1` (real zeros included). Route: the compact Re = 1 segment
`{1 + it : |t| ≤ 1}` is disjoint from the closed zero set (`riemannZeta_ne_zero_of_one_le_re`), so
the continuous positive `infDist` to the zero set attains a positive minimum `ε₀` on the segment;
any low-height zero at horizontal distance `1 − Re ρ` from the segment is at least `ε₀` away. -/
theorem zeta_zero_free_strip :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {ρ : ℂ}, riemannZeta ρ = 0 → |ρ.im| ≤ 1 → ρ.re ≤ 1 - ε₀ := by
  -- the zero set is closed and nonempty (trivial zero at `-2`)
  have hZne : riemannZetaZeros.Nonempty := by
    refine ⟨-2, ?_⟩
    rw [mem_riemannZetaZeros]
    have h := riemannZeta_neg_two_mul_nat_add_one 0
    simpa using h
  -- the compact Re = 1 segment
  set L₀ : Set ℂ := (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) '' Set.Icc (-1 : ℝ) 1 with hL₀
  have hL₀compact : IsCompact L₀ :=
    isCompact_Icc.image (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hL₀ne : L₀.Nonempty := (Set.nonempty_Icc.mpr (by norm_num)).image _
  -- positive `infDist` at every segment point (`Re = 1 ⇒ ζ ≠ 0`)
  have hpos : ∀ x ∈ L₀, 0 < infDist x riemannZetaZeros := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := hx
    have hxre : ((1 : ℂ) + (t : ℂ) * I).re = 1 := by simp
    have hne : (1 : ℂ) + (t : ℂ) * I ∉ riemannZetaZeros := by
      rw [mem_riemannZetaZeros]
      exact riemannZeta_ne_zero_of_one_le_re (le_of_eq hxre.symm)
    exact (isClosed_riemannZetaZeros.notMem_iff_infDist_pos hZne).mp hne
  -- the minimum over the compact segment
  obtain ⟨x₀, hx₀L, hx₀min⟩ := hL₀compact.exists_isMinOn hL₀ne
    (continuous_infDist_pt (s := riemannZetaZeros)).continuousOn
  refine ⟨infDist x₀ riemannZetaZeros, hpos x₀ hx₀L, ?_⟩
  intro ρ hρ0 hγ
  have hρZ : ρ ∈ riemannZetaZeros := mem_riemannZetaZeros.mpr hρ0
  have hxL : (1 : ℂ) + (ρ.im : ℂ) * I ∈ L₀ := ⟨ρ.im, Set.mem_Icc.mpr (abs_le.mp hγ), rfl⟩
  have hmin : infDist x₀ riemannZetaZeros ≤ infDist ((1 : ℂ) + (ρ.im : ℂ) * I) riemannZetaZeros :=
    isMinOn_iff.mp hx₀min _ hxL
  have hle : infDist ((1 : ℂ) + (ρ.im : ℂ) * I) riemannZetaZeros
      ≤ dist ((1 : ℂ) + (ρ.im : ℂ) * I) ρ := infDist_le_dist_of_mem hρZ
  have hρre : ρ.re < 1 := by
    by_contra h; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hρ0
  have hdist : dist ((1 : ℂ) + (ρ.im : ℂ) * I) ρ = 1 - ρ.re := by
    rw [Complex.dist_eq]
    have hsub : ((1 : ℂ) + (ρ.im : ℂ) * I) - ρ = ((1 - ρ.re : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ρ.re)]
  rw [hdist] at hle
  linarith [hmin, hle]

/-! ## 5. The quantitative ζ zero-free region -/

set_option maxHeartbeats 800000 in
-- The 3-4-1 assembly rewrites the heavy `LFunction`/`LSeries` log-derivatives at three points and
-- runs the Davenport chain in one declaration; it needs more than the default budget.
/-- **S3f — the quantitative ζ zero-free region (de la Vallée Poussin).** There is an explicit
constant `c₃ > 0` such that every zero `ρ` of `ζ` with `Re ρ ≥ 1/2` satisfies
`Re ρ ≤ 1 − c₃ / log(|Im ρ| + 2)`. Here `c₃ = min(1/75712, ε₀·log 2)`, `ε₀` the fixed-strip
constant. -/
theorem zeta_zero_free_region :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∀ {ρ : ℂ}, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re →
      ρ.re ≤ 1 - c₃ / Real.log (|ρ.im| + 2) := by
  obtain ⟨ε₀, hε₀pos, hstrip⟩ := zeta_zero_free_strip
  refine ⟨min (1 / 75712) (ε₀ * Real.log 2),
    lt_min (by norm_num) (mul_pos hε₀pos (Real.log_pos (by norm_num))), ?_⟩
  intro ρ hzero hre
  set c₃ : ℝ := min (1 / 75712) (ε₀ * Real.log 2) with hc₃
  set Lv : ℝ := Real.log (|ρ.im| + 2) with hLdef
  have hLlog2 : Real.log 2 ≤ Lv := by
    rw [hLdef]; exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg ρ.im])
  have hLpos : 0 < Lv := lt_of_lt_of_le (Real.log_pos (by norm_num)) hLlog2
  have hβ1 : ρ.re < 1 := by
    by_contra h; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hzero
  rcases le_or_gt 1 |ρ.im| with hγ1 | hγ1
  · -- Case `|γ| ≥ 1`: the 3-4-1 keep-one region
    have hL1 : (1 : ℝ) ≤ Lv := by
      rw [hLdef]
      have hexp : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      have h3 : (1 : ℝ) ≤ Real.log 3 := by
        rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hexp
      exact le_trans h3 (Real.log_le_log (by norm_num) (by linarith [hγ1]))
    rcases le_or_gt ρ.re (1 / 2) with hβ | hβ
    · -- `Re ρ ≤ 1/2`: trivial (`c₃/Lv ≤ 1/2`)
      have hc₃Lv : c₃ / Lv ≤ 1 / 2 := by
        have hc1 : c₃ ≤ 1 / 75712 := min_le_left _ _
        rw [div_le_iff₀ hLpos]; nlinarith [hL1, hc1]
      linarith [hβ, hc₃Lv]
    · -- `1/2 < Re ρ`: the Davenport extraction
      set dd : ℝ := 1 / 10816 with hdddef
      have hddpos : (0 : ℝ) < dd := by norm_num
      have hddlt1 : dd < 1 := by rw [hdddef]; norm_num
      set σ : ℝ := 1 + dd / Lv with hσdef
      have hddL : dd / Lv ≤ dd := by rw [div_le_iff₀ hLpos]; nlinarith [hL1, hddpos]
      have hσ1 : 1 < σ := by
        rw [hσdef]; have : 0 < dd / Lv := div_pos hddpos hLpos; linarith
      have hσ2 : σ < 2 := by rw [hσdef]; linarith [hddL, hddlt1]
      -- the ζ 3-4-1 at the trivial character mod `1`
      have h341 := three_four_one_logDeriv (1 : DirichletCharacter ℂ 1) hσ1 ρ.im
      rw [show ((1 : DirichletCharacter ℂ 1) ^ 2) = 1 from one_pow 2] at h341
      set s1 : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hs1def
      set s2 : ℂ := (σ : ℂ) + 2 * (ρ.im : ℂ) * I with hs2def
      have hσ0C : (1 : ℝ) < ((σ : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact hσ1
      have hσ1C : (1 : ℝ) < s1.re := by rw [hs1def]; simpa using hσ1
      have hσ2C : (1 : ℝ) < s2.re := by rw [hs2def]; simpa using hσ1
      rw [neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ0C,
          neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ1C,
          neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ2C] at h341
      simp only [LFunction_modOne_eq] at h341
      -- A₀ : the sharp real-`σ` pole bound
      have hA0 : (-logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
        rw [logDeriv_apply, ← neg_div]; exact neg_logDeriv_zeta_le hσ1 hσ2.le
      -- A₁ : the retained-zero bound at `s₁`
      have hA1 : (-logDeriv riemannZeta s1).re
          ≤ (1 / (s1 - 1)).re + 1080 * Real.log (|ρ.im| + 2) - 1 / (σ - ρ.re) := by
        have h := zeta_neg_re_logDeriv_le_keep hzero hβ hβ1 hσ1 hσ2
        rw [← hs1def] at h; exact h
      -- A₂ : the drop-all bound at `s₂`
      have hA2 : (-logDeriv riemannZeta s2).re
          ≤ (1 / (s2 - 1)).re + 1080 * Real.log (|ρ.im| + 2) := by
        have h := zeta_neg_re_logDeriv_le hσ1 hσ2.le (γ := ρ.im)
        rw [← hs2def] at h; exact h
      -- the pole real parts are `≤ 1` (heights `|γ| ≥ 1`, `|2γ| ≥ 2`)
      have hP1 : (1 / (s1 - 1)).re ≤ 1 := by
        have him : (s1 - 1).im = ρ.im := by
          rw [hs1def]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        have hn : (1 : ℝ) ≤ ‖s1 - 1‖ := by
          have h := Complex.abs_im_le_norm (s1 - 1); rw [him] at h; linarith [hγ1]
        calc (1 / (s1 - 1)).re ≤ ‖1 / (s1 - 1)‖ :=
              le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
          _ = 1 / ‖s1 - 1‖ := by rw [norm_div, norm_one]
          _ ≤ 1 := by rw [div_le_one (by linarith : (0 : ℝ) < ‖s1 - 1‖)]; exact hn
      have hP2 : (1 / (s2 - 1)).re ≤ 1 := by
        have him : (s2 - 1).im = 2 * ρ.im := by
          rw [hs2def]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        have hn : (1 : ℝ) ≤ ‖s2 - 1‖ := by
          have h := Complex.abs_im_le_norm (s2 - 1); rw [him] at h
          have h2 : (2 : ℝ) * |ρ.im| = |2 * ρ.im| := by rw [abs_mul]; norm_num
          nlinarith [hγ1, h, h2, abs_nonneg (2 * ρ.im)]
        calc (1 / (s2 - 1)).re ≤ ‖1 / (s2 - 1)‖ :=
              le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
          _ = 1 / ‖s2 - 1‖ := by rw [norm_div, norm_one]
          _ ≤ 1 := by rw [div_le_one (by linarith : (0 : ℝ) < ‖s2 - 1‖)]; exact hn
      -- the Davenport chain `4/(σ−β) ≤ 3/(σ−1) + 5408 Lv`
      have e8 : (8 : ℝ) ≤ 8 * Lv := by nlinarith [hL1]
      have key : 4 * (1 / (σ - ρ.re)) ≤ 3 * (1 / (σ - 1)) + 5408 * Lv := by
        linarith [h341, hA0, hA1, hA2, hP1, hP2, e8, hLdef]
      have hchain' : 4 / (dd / Lv + (1 - ρ.re)) ≤ 3 / (dd / Lv) + 5408 * Lv := by
        rw [mul_one_div, mul_one_div] at key
        have e1 : σ - ρ.re = dd / Lv + (1 - ρ.re) := by rw [hσdef]; ring
        have e2 : σ - 1 = dd / Lv := by rw [hσdef]; ring
        rw [e1, e2] at key; exact key
      have hCdd : (5408 : ℝ) * dd = 1 / 2 := by rw [hdddef]; norm_num
      have hext := zero_free_extraction hLpos hddpos hCdd hβ1 hchain'
      have hfin : c₃ / Lv ≤ dd / (7 * Lv) := by
        rw [show dd / (7 * Lv) = dd / 7 / Lv from (div_div dd 7 Lv).symm,
            div_le_div_iff_of_pos_right hLpos]
        have hval : dd / 7 = 1 / 75712 := by rw [hdddef]; norm_num
        rw [hval]; exact min_le_left _ _
      linarith [hext, hfin]
  · -- Case `|γ| < 1`: the fixed zero-free strip
    have hst := hstrip hzero (le_of_lt hγ1)
    have hc₃le : c₃ ≤ ε₀ * Lv :=
      le_trans (min_le_right _ _) (mul_le_mul_of_nonneg_left hLlog2 hε₀pos.le)
    have hc₃Lv : c₃ / Lv ≤ ε₀ := by rw [div_le_iff₀ hLpos]; linarith [hc₃le]
    linarith [hst, hc₃Lv]

end Salt.SW
