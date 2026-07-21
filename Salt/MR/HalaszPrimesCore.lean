/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HalaszPrimes
import Salt.MR.HalaszKernel
import Salt.MR.PerronTrunc

/-!
# L11-CORE — the Perron representation of the pairwise prime sum + the LEFT shift

The R1-core of node **L11** (`halasz_primes_pow`): the Perron/Mellin representation
of the pairwise prime sum and its contour shift into the VK zero-free region.  This
closes the resistance flagged at the foot of `Salt/MR/HalaszPrimes.lean`.

Route: Matomäki–Radziwiłł Lemma 11 (`docs/sources/1501.04585v4.pdf` pp.17–18), as
transcribed in `docs/exploration/l11-core-freeze.md` (BINDING).  The stone ladder
(LANDED this session: **W-KER, REP, TRUNC** — the Perron-representation core):

* **W-KER** `primeWindow` / `windowKernel` / `primeWindow_contour_rep` — the two-sided
  ramp window `w`, a difference of two landed `hatK` instances (plateau `⊇ [P, 2P]`,
  support `⊆ [P/2, 3P]`, `0 ≤ w ≤ 1`), with its EXACT combined-integral contour
  representation from `hat_contour_rep` (two applications, `integral_sub` on the shared
  Dirichlet factor).  The corpus replacement for MR's smooth cutoff `f`; the Mellin
  kernel `windowKernel = hatKernel(2P,P) − hatKernel(P/2,P/2)`.
* **REP** `lambda_window_rep` — specialise to `aₙ = Λ(n)·n^{iu}`: the twist re-indexes
  the Dirichlet series (`LSeries Λ ((c+it) − iu) = −ζ′/ζ` at the shifted argument, MR
  (15)), giving `Σ_n Λ(n)·n^{iu}·w(n) = (1/2π)∫ (−ζ′/ζ)((c+it)−iu)·windowKernel dt`.
* **TRUNC** `rep_truncated` — truncate the contour at `[−T', T']`; the complement tail
  is `(Σ‖aₙ‖/nᶜ)·Cₖ(P,c)·(2/T')`-grade (`c`-line ζ′/ζ price × quadratic kernel decay).
* Reusable infrastructure landed: `norm_logDeriv_zeta_cline_le` (the `c`-line ζ′/ζ
  bound `≤ Σ Λ(n)/nᶜ`), `integrable_dseries_mul_hatKernel` / `integrable_windowKernel`,
  `norm_hatKernel_le` / `norm_windowKernel_le`, `integral_Ioi_inv_c_sq_le` /
  `integral_compl_Icc_inv_c_sq_le` (the quadratic tail integrals).

RESIDUAL (deeper C-tier stones, to be landed next): ZFREE-RECT (the shifted rectangle is
ζ-zero-free — compactness on `{Re=1}×[−M,M]` handling the pole at `1` via
`riemannZeta_residue_one`, + the pow region at height `5T`), EDGE (the LEFT-strip Landau
price via `near_norm_logDeriv_Zc_le`), RES (the pole residue `W(1+iu)`), POLE-ROW (the
convergent `Σ_j P/(1+j²)` spacing sum), ASM (`halasz_primes_pow`, the frozen shape + `P ≤ T^10`).

The window is `w(n) = hatK (2P) P n − hatK (P/2) (P/2) n`:

* for `n ≤ P/2` both hats are `1` ⟹ `w = 0`;
* on `[P/2, P]` the upper hat is `1`, the lower ramps `1 → 0` ⟹ `w` ramps `0 → 1`;
* on `[P, 2P]` upper `= 1`, lower `= 0` ⟹ `w = 1` (the plateau);
* on `[2P, 3P]` upper ramps `1 → 0`, lower `= 0` ⟹ `w` ramps `1 → 0`;
* for `n ≥ 3P` both are `0` ⟹ `w = 0`.

## The frozen shape (BINDING — iron rule 1)

`halasz_primes_pow` closes at the frozen header of `Salt/MR/HalaszPrimes.lean`
plus Amendment L11-T's `P ≤ T^10` plus the `∃ C c T₀` packaging (quantifiers
`∃ C c T₀` outermost).  See the freeze.
-/

namespace Salt.MR

open scoped BigOperators
open Complex MeasureTheory Set ArithmeticFunction
open scoped LSeries.notation

/-! ## W-KER — the two-sided ramp window and its Mellin kernel -/

/-- **The prime window** (W-KER).  `primeWindow P n` is the two-sided ramp window:
`1` on `[P, 2P]`, supported on `[P/2, 3P]`, built as a difference of two landed
`hatK` instances — the upper cutoff at `2P` (ramp `[2P, 3P]`) minus the lower
cutoff at `P/2` (ramp `[P/2, P]`).  The corpus replacement for MR's smooth cutoff. -/
noncomputable def primeWindow (P : ℝ) (n : ℕ) : ℝ :=
  hatK (2 * P) P n - hatK (P / 2) (P / 2) n

/-- **The window Mellin kernel** (W-KER).  `windowKernel = hatKernel(2P,P) −
hatKernel(P/2,P/2)`, the per-`t` contour factor of the window representation. -/
noncomputable def windowKernel (P c t : ℝ) : ℂ :=
  hatKernel (2 * P) P c t - hatKernel (P / 2) (P / 2) c t

/-! ### Pointwise facts about `primeWindow`. -/

/-- Boundary-inclusive vanishing of `hatK` past the ramp: `hatK X h n = 0` once
`X + h ≤ n` (the closed endpoint, unlike `hatK_eq_zero`'s strict `X + h < n`).
Needed because the plateau boundary `n = P` sits exactly at `X + h` of the lower hat. -/
lemma hatK_eq_zero_le {X h : ℝ} (hh : 0 ≤ h) {n : ℕ} (hn : X + h ≤ (n : ℝ)) : hatK X h n = 0 := by
  rw [hatK, max_eq_right (by linarith : X + h - (n : ℝ) ≤ 0),
    max_eq_right (by linarith : X - (n : ℝ) ≤ 0)]; simp

/-- `0 ≤ primeWindow P n` (the lower hat never exceeds the upper hat). -/
lemma primeWindow_nonneg {P : ℝ} (hP : 0 < P) (n : ℕ) : 0 ≤ primeWindow P n := by
  rw [primeWindow, sub_nonneg]
  by_cases h : P ≤ (n : ℝ)
  · rw [hatK_eq_zero_le (by linarith) (by linarith : P / 2 + P / 2 ≤ (n : ℝ))]
    exact hatK_nonneg (by linarith) n
  · have h' : (n : ℝ) < P := not_le.mp h
    rw [hatK_eq_one (by linarith) (by linarith : (n : ℝ) ≤ 2 * P)]
    exact hatK_le_one (by linarith) n

/-- `primeWindow P n ≤ 1`. -/
lemma primeWindow_le_one {P : ℝ} (hP : 0 < P) (n : ℕ) : primeWindow P n ≤ 1 := by
  rw [primeWindow]
  have h1 : hatK (2 * P) P n ≤ 1 := hatK_le_one (by linarith) n
  have h2 : 0 ≤ hatK (P / 2) (P / 2) n := hatK_nonneg (by linarith) n
  linarith

/-- **The plateau** `w = 1` on `[P, 2P]`. -/
lemma primeWindow_eq_one {P : ℝ} (hP : 0 < P) {n : ℕ} (h1 : P ≤ (n : ℝ))
    (h2 : (n : ℝ) ≤ 2 * P) : primeWindow P n = 1 := by
  rw [primeWindow, hatK_eq_one (by linarith) h2,
    hatK_eq_zero_le (by linarith) (by linarith : P / 2 + P / 2 ≤ (n : ℝ))]; ring

/-- **Lower support** `w = 0` for `n ≤ P/2`. -/
lemma primeWindow_eq_zero_lower {P : ℝ} (hP : 0 < P) {n : ℕ} (h : (n : ℝ) ≤ P / 2) :
    primeWindow P n = 0 := by
  rw [primeWindow, hatK_eq_one (by linarith) (by linarith : (n : ℝ) ≤ 2 * P),
    hatK_eq_one (by linarith) (by linarith : (n : ℝ) ≤ P / 2)]; ring

/-- **Upper support** `w = 0` for `3P ≤ n`. -/
lemma primeWindow_eq_zero_upper {P : ℝ} (hP : 0 < P) {n : ℕ} (h : 3 * P ≤ (n : ℝ)) :
    primeWindow P n = 0 := by
  rw [primeWindow, hatK_eq_zero_le (by linarith) (by linarith : 2 * P + P ≤ (n : ℝ)),
    hatK_eq_zero_le (by linarith) (by linarith : P / 2 + P / 2 ≤ (n : ℝ))]; ring

/-! ### W-KER — the exact contour representation

Transfer the landed `hat_contour_rep` (two applications, linearity) to the window.
`windowKernel P c t = hatKernel(2P,P,c,t) − hatKernel(P/2,P/2,c,t)` is the exact
Mellin factor. -/

/-- Summability transfer: the Dirichlet `L¹` condition `Σ ‖aₙ‖/nᶜ` implies the
`hat_contour_rep`-shaped condition `Σ ‖aₙ‖·(A/n)ᶜ` for any `A ≥ 0`. -/
lemma summable_norm_div_rpow_mul {a : ℕ → ℂ} {c : ℝ}
    (hsum : Summable fun n => ‖a n‖ / (n : ℝ) ^ c) {A : ℝ} (hA : 0 ≤ A) :
    Summable fun n => ‖a n‖ * (A / (n : ℝ)) ^ c := by
  refine (hsum.mul_left (A ^ c)).congr (fun n => ?_)
  rw [Real.div_rpow hA (by positivity)]; ring

/-- `n ↦ aₙ · hatK X h n` is summable (finite support: `hatK` vanishes past the ramp). -/
lemma summable_mul_hatK (a : ℕ → ℂ) {X h : ℝ} (hh : 0 < h) :
    Summable (fun n => a n * (hatK X h n : ℂ)) := by
  apply summable_of_ne_finset_zero (s := Finset.range (⌊X + h⌋₊ + 1))
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  have hgt : X + h < (n : ℝ) := by
    have h1 := Nat.lt_floor_add_one (X + h)
    have h2 : ((⌊X + h⌋₊ : ℕ) + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [hatK_eq_zero hh hgt, Complex.ofReal_zero, mul_zero]

/-- The hat Mellin kernel `hatKernel X h c` is continuous in `t`. -/
lemma continuous_hatKernel {X h c : ℝ} (hX : 0 < X) (hh : 0 < h) (hc : 0 < c) :
    Continuous (fun t : ℝ => hatKernel X h c t) := by
  have hXh : (0 : ℝ) < X + h := by linarith
  simp only [hatKernel]
  refine Continuous.div ?_ (by fun_prop) (fun t => ?_)
  · refine Continuous.sub ?_ ?_
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hXh.ne'))
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne')
      (mul_ne_zero (Salt.SW.s_ne_zero hc t) (Salt.SW.s1_ne_zero hc t))

/-- The per-`n` norm of a Dirichlet term on the `c`-line: `‖aₙ/n^{c+it}‖ = ‖aₙ‖/nᶜ`. -/
lemma norm_dseries_term {a : ℕ → ℂ} {c : ℝ} (hc : 0 < c) (n : ℕ) (t : ℝ) :
    ‖a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ = ‖a n‖ / (n : ℝ) ^ c := by
  rw [norm_div]
  congr 1
  rw [← Complex.ofReal_natCast, Salt.SW.norm_ofReal_cpow_vert (by positivity) hc]

/-- Uniform bound on the Dirichlet factor along the `c`-line: `‖Σ aₙ/n^{c+it}‖ ≤ Σ ‖aₙ‖/nᶜ`. -/
lemma norm_dseries_le {a : ℕ → ℂ} {c : ℝ} (hc : 0 < c)
    (hsum : Summable fun n => ‖a n‖ / (n : ℝ) ^ c) (t : ℝ) :
    ‖∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ≤ ∑' n, ‖a n‖ / (n : ℝ) ^ c := by
  refine le_trans (norm_tsum_le_tsum_norm ?_) (le_of_eq ?_)
  · exact hsum.congr (fun n => (norm_dseries_term hc n t).symm)
  · exact tsum_congr (fun n => norm_dseries_term hc n t)

/-- **Kernel norm bound** (branch 2).  The hat Mellin kernel decays quadratically:
`‖hatKernel X h c t‖ ≤ (2(X+h)^{c+1}/h)·(c²+t²)⁻¹`. -/
lemma norm_hatKernel_le {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) (t : ℝ) :
    ‖hatKernel X h c t‖ ≤ (2 * (X + h) ^ (c + 1) / h) * (c ^ 2 + t ^ 2)⁻¹ := by
  have hXh : (0 : ℝ) < X + h := by linarith
  have hmb := hat_mellin_bound hX hh hc t
  have hs2 : ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
  have hXhc : (X + h) ^ c * (X + h) = (X + h) ^ (c + 1) := by
    rw [Real.rpow_add hXh, Real.rpow_one]
  calc ‖hatKernel X h c t‖
      ≤ (X + h) ^ c * (2 * (X + h) / (h * ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)) :=
        le_trans hmb (mul_le_mul_of_nonneg_left (min_le_right _ _)
          (Real.rpow_nonneg hXh.le c))
    _ = (2 * (X + h) ^ (c + 1) / h) * (c ^ 2 + t ^ 2)⁻¹ := by
        have hDne : (c ^ 2 + t ^ 2) ≠ 0 := by positivity
        rw [hs2, ← hXhc]; field_simp

/-- **W-KER integrability.**  The Dirichlet-series × hat-kernel integrand on the
`c`-line is integrable (bounded Dirichlet factor × quadratically-decaying kernel). -/
lemma integrable_dseries_mul_hatKernel (a : ℕ → ℂ) (ha0 : a 0 = 0) {X h c : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c)
    (hsum : Summable fun n => ‖a n‖ / (n : ℝ) ^ c) :
    Integrable (fun t : ℝ =>
      (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * hatKernel X h c t) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hXh : (0 : ℝ) < X + h := by linarith
  set S : ℝ := ∑' n, ‖a n‖ / (n : ℝ) ^ c with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; exact tsum_nonneg (fun n => by positivity)
  -- per-n continuity of the Dirichlet terms
  have hfcont : ∀ n : ℕ, Continuous (fun t : ℝ => a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [ha0, zero_div]; exact continuous_const
    · have hne : ∀ t : ℝ, ((n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) ≠ 0 := by
        intro t
        exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn.ne'))
      exact Continuous.div continuous_const
        (Continuous.const_cpow (by fun_prop) (Or.inr (fun t => Salt.SW.s_ne_zero hc t))) hne
  -- continuity of the Dirichlet series G
  have hGcont : Continuous (fun t : ℝ => ∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) :=
    continuous_tsum hfcont hsum (fun n t => le_of_eq (norm_dseries_term hc n t))
  -- uniform bound ‖G t‖ ≤ S
  have hGbound : ∀ t : ℝ, ‖∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ≤ S :=
    fun t => norm_dseries_le hc hsum t
  -- domination by K₀·(c²+t²)⁻¹
  set K₀ : ℝ := S * (2 * (X + h) ^ (c + 1) / h) with hK₀def
  refine ((Salt.SW.integrable_inv_c_sq_add_sq hc).const_mul K₀).mono'
    (hGcont.mul (continuous_hatKernel hX0 hh hc)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => ?_))
  rw [norm_mul]
  calc ‖∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ * ‖hatKernel X h c t‖
      ≤ S * ((2 * (X + h) ^ (c + 1) / h) * (c ^ 2 + t ^ 2)⁻¹) :=
        mul_le_mul (hGbound t) (norm_hatKernel_le hX hh hc t) (norm_nonneg _) hS0
    _ = K₀ * (c ^ 2 + t ^ 2)⁻¹ := by rw [hK₀def]; ring

/-- **W-KER — the exact window contour representation.**  The corpus replacement for
MR's Perron step: `Σ_n aₙ·w(n) = (1/2π)∫ (Σ_n aₙ/n^{c+it})·windowKernel(P,c,t) dt`, the
window `w = primeWindow P` written against the difference kernel `windowKernel =
hatKernel(2P,P) − hatKernel(P/2,P/2)`.  Two applications of the landed `hat_contour_rep`
combined by linearity (`integral_sub` on the shared Dirichlet factor).  The single
side condition is the Dirichlet `L¹` bound `Σ ‖aₙ‖/nᶜ` at the contour abscissa `c`. -/
theorem primeWindow_contour_rep (a : ℕ → ℂ) (ha0 : a 0 = 0) {P c : ℝ}
    (hP : 2 ≤ P) (hc : 0 < c)
    (hsum : Summable fun n => ‖a n‖ / (n : ℝ) ^ c) :
    ∑' n, a n * (primeWindow P n : ℂ)
      = (1 / (2 * Real.pi)) • ∫ t : ℝ,
          (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * windowKernel P c t := by
  have hP0 : (0 : ℝ) < P := by linarith
  -- summability in the two hat forms
  have hsumU : Summable fun n => ‖a n‖ * ((2 * P + P) / (n : ℝ)) ^ c :=
    summable_norm_div_rpow_mul hsum (by linarith)
  have hsumL : Summable fun n => ‖a n‖ * ((P / 2 + P / 2) / (n : ℝ)) ^ c :=
    summable_norm_div_rpow_mul hsum (by linarith)
  -- the two hat_contour_rep applications, folded to `hatKernel` (defeq)
  have repU : ∑' n, a n * (hatK (2 * P) P n : ℂ)
      = (1 / (2 * Real.pi)) • ∫ t : ℝ,
          (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * hatKernel (2 * P) P c t :=
    hat_contour_rep a ha0 (by linarith) hP0 hc hsumU
  have repL : ∑' n, a n * (hatK (P / 2) (P / 2) n : ℂ)
      = (1 / (2 * Real.pi)) • ∫ t : ℝ,
          (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * hatKernel (P / 2) (P / 2) c t :=
    hat_contour_rep a ha0 (by linarith) (by linarith) hc hsumL
  -- LHS splits into the two hat tsums
  have hsplit : ∑' n, a n * (primeWindow P n : ℂ)
      = (∑' n, a n * (hatK (2 * P) P n : ℂ)) - (∑' n, a n * (hatK (P / 2) (P / 2) n : ℂ)) := by
    rw [← Summable.tsum_sub (summable_mul_hatK a hP0) (summable_mul_hatK a (by linarith))]
    refine tsum_congr (fun n => ?_)
    simp only [primeWindow]; push_cast; ring
  rw [hsplit, repU, repL, ← smul_sub]
  congr 1
  rw [← integral_sub
        (integrable_dseries_mul_hatKernel a ha0 (by linarith) hP0 hc hsum)
        (integrable_dseries_mul_hatKernel a ha0 (by linarith) (by linarith) hc hsum)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only [windowKernel]; ring

/-! ## REP — the per-`u` Perron representation of the log-weighted window sum

Specialize `primeWindow_contour_rep` to `aₙ = Λ(n)·n^{iu}`.  The twist `n^{iu}`
re-indexes the Dirichlet series: `Σ_n Λ(n)·n^{iu}/n^{c+it} = LSeries Λ ((c+it) − iu)`,
which for `c > 1` is `−ζ′/ζ` at the shifted argument (MR (15), the argument-shift form
of the twist — no χ-twist at `q = 1`). -/

/-- The Dirichlet `L¹`-summability of the von Mangoldt series at real abscissa `c > 1`
(absolute convergence of `Σ Λ(n)/nᶜ`). -/
lemma summable_vonMangoldt_div_rpow {c : ℝ} (hc : 1 < c) :
    Summable (fun n => vonMangoldt n / (n : ℝ) ^ c) := by
  have hLS : Summable (fun n => LSeries.term ↗vonMangoldt (c : ℂ) n) :=
    LSeriesSummable_vonMangoldt (by simpa using hc)
  have heq : ∀ n : ℕ, LSeries.term ↗vonMangoldt (c : ℂ) n
      = (((vonMangoldt n / (n : ℝ) ^ c : ℝ)) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn.ne']
      rw [show ((c : ℝ) : ℂ) = ((c : ℝ) : ℂ) from rfl, Complex.ofReal_div,
        ← Complex.ofReal_natCast (n := n), ← Complex.ofReal_cpow (by positivity)]
  rw [← Complex.summable_ofReal]
  exact hLS.congr heq

/-- **REP — the per-`u` Perron representation.**  For `2 ≤ P`, `1 < c`, and any twist
`u`, the log-weighted window sum has the exact contour representation
`Σ_n Λ(n)·n^{iu}·w(n) = (1/2π)∫ (−ζ′/ζ)((c+it) − iu)·windowKernel(P,c,t) dt`.  Rides
`primeWindow_contour_rep` (W-KER) + the argument-shift of the von Mangoldt L-series
(`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`). -/
theorem lambda_window_rep {P c u : ℝ} (hP : 2 ≤ P) (hc : 1 < c) :
    ∑' n, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ)
      = (1 / (2 * Real.pi)) • ∫ t : ℝ,
          (- logDeriv riemannZeta ((c : ℂ) + (t : ℂ) * I - (u : ℂ) * I))
            * windowKernel P c t := by
  set a : ℕ → ℂ := fun n => (vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I) with hadef
  have hc0 : (0 : ℝ) < c := by linarith
  -- a 0 = 0
  have ha0 : a 0 = 0 := by
    rw [hadef]; simp
  -- ‖a n‖ = Λ n
  have hnorm_a : ∀ n : ℕ, ‖a n‖ = vonMangoldt n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ha0]; simp
    · rw [hadef]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      rw [← Complex.ofReal_natCast (n := n),
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
      simp
  -- Dirichlet L¹ summability
  have hsum : Summable (fun n => ‖a n‖ / (n : ℝ) ^ c) := by
    refine (summable_vonMangoldt_div_rpow hc).congr (fun n => ?_)
    rw [hnorm_a n]
  rw [show (∑' n, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
      = ∑' n, a n * (primeWindow P n : ℂ) from rfl,
    primeWindow_contour_rep a ha0 hP hc0 hsum]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  congr 1
  -- the twist re-indexes: Σ aₙ/n^{c+it} = LSeries Λ ((c+it) − iu) = −logDeriv ζ (…)
  set w : ℂ := (c : ℂ) + (t : ℂ) * I - (u : ℂ) * I with hwdef
  have hwre : 1 < w.re := by rw [hwdef]; simp; linarith
  have hterm : ∀ n : ℕ, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      = LSeries.term ↗vonMangoldt w n := by
    intro n
    rw [LSeries.term_def₀ (by simp) w n]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ha0]; simp
    · have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      rw [hadef]
      simp only
      rw [mul_div_assoc]
      congr 1
      rw [div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hne]
      congr 1
      rw [hwdef]; ring
  have hLSeries : (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) = LSeries ↗vonMangoldt w :=
    tsum_congr hterm
  rw [hLSeries, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hwre, logDeriv_apply, neg_div]

/-! ## TRUNC — the `c`-line ζ′/ζ bound (the truncation-tail price)

The uniform bound on the shifted integrand along the contour `Re = c > 1`, from the
Dirichlet series `−ζ′/ζ(w) = Σ Λ(n)/n^w` dominated by its value at the real point `c`.
This is the `1/(c−1)`-grade price of the freeze (= `log P`-grade at `c = 1 + 1/log P`),
carried in-statement as `Σ Λ(n)/nᶜ` (a growing quantity, #253). -/

/-- **TRUNC `c`-line bound.**  On the vertical line `Re = c > 1`, the ζ log-derivative
is dominated by the real Dirichlet sum: `‖ζ′/ζ(c+is)‖ ≤ Σ_n Λ(n)/nᶜ`, uniformly in `s`
(and hence in the twist `u`, since the shifted argument `(c+it) − iu = c + i(t−u)` lies
on the same line). -/
lemma norm_logDeriv_zeta_cline_le {c : ℝ} (hc : 1 < c) (s : ℝ) :
    ‖logDeriv riemannZeta ((c : ℂ) + (s : ℂ) * I)‖ ≤ ∑' n, vonMangoldt n / (n : ℝ) ^ c := by
  set w : ℂ := (c : ℂ) + (s : ℂ) * I with hwdef
  have hwre : (1 : ℝ) < w.re := by rw [hwdef]; simp; linarith
  have hnt : ∀ n : ℕ, ‖LSeries.term ↗vonMangoldt w n‖ = vonMangoldt n / (n : ℝ) ^ c := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg hn.ne']
      congr 1
      · simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      · rw [hwdef]; simp
  have hsummN : Summable (fun n => ‖LSeries.term ↗vonMangoldt w n‖) :=
    (summable_vonMangoldt_div_rpow hc).congr (fun n => (hnt n).symm)
  have hld : ‖logDeriv riemannZeta w‖ = ‖LSeries ↗vonMangoldt w‖ := by
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hwre, logDeriv_apply, norm_div, norm_div,
      norm_neg]
  rw [hld]
  calc ‖LSeries ↗vonMangoldt w‖
      ≤ ∑' n, ‖LSeries.term ↗vonMangoldt w n‖ := norm_tsum_le_tsum_norm hsummN
    _ = ∑' n, vonMangoldt n / (n : ℝ) ^ c := tsum_congr hnt

/-- The hat Mellin kernel is integrable on the `c`-line (quadratic decay). -/
lemma integrable_hatKernel {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) :
    Integrable (fun t : ℝ => hatKernel X h c t) := by
  refine ((Salt.SW.integrable_inv_c_sq_add_sq hc).const_mul (2 * (X + h) ^ (c + 1) / h)).mono'
    (continuous_hatKernel (by linarith) hh hc).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => norm_hatKernel_le hX hh hc t))

/-- The window Mellin kernel is integrable on the `c`-line. -/
lemma integrable_windowKernel {P c : ℝ} (hP : 2 ≤ P) (hc : 0 < c) :
    Integrable (fun t : ℝ => windowKernel P c t) := by
  simp only [windowKernel]
  exact (integrable_hatKernel (by linarith) (by linarith) hc).sub
    (integrable_hatKernel (by linarith) (by linarith) hc)

/-- **Window kernel norm bound.**  `‖windowKernel P c t‖ ≤ Cₖ(P,c)·(c²+t²)⁻¹`, the
quadratic tail decay with `Cₖ(P,c) = 2(3P)^{c+1}/P + 2·Pᶜ⁺¹/(P/2)` (sum of the two
hat-kernel branch-2 constants; `2P+P = 3P`, `P/2+P/2 = P`). -/
lemma norm_windowKernel_le {P c : ℝ} (hP : 2 ≤ P) (hc : 0 < c) (t : ℝ) :
    ‖windowKernel P c t‖
      ≤ (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2))
        * (c ^ 2 + t ^ 2)⁻¹ := by
  simp only [windowKernel]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 := norm_hatKernel_le (X := 2 * P) (h := P) (by linarith) (by linarith) hc t
  have h2 := norm_hatKernel_le (X := P / 2) (h := P / 2) (by linarith) (by linarith) hc t
  rw [add_mul]
  linarith [h1, h2]

/-- **Quadratic tail integral** (one-sided).  `∫_{t > T'} (c²+t²)⁻¹ ≤ 1/T'` for `T' > 0`
(mirrors `hat_tail`'s inner estimate: `(c²+t²)⁻¹ ≤ t⁻²`, then the `∫ t⁻² = 1/T'`). -/
lemma integral_Ioi_inv_c_sq_le {c T' : ℝ} (hc : 0 < c) (hT' : 0 < T') :
    ∫ t in Set.Ioi T', (c ^ 2 + t ^ 2)⁻¹ ≤ 1 / T' := by
  have hInt1 : IntegrableOn (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) (Set.Ioi T') :=
    (Salt.SW.integrable_inv_c_sq_add_sq hc).integrableOn
  have hInt2 : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi T') :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hT'
  calc ∫ t in Set.Ioi T', (c ^ 2 + t ^ 2)⁻¹
      ≤ ∫ t in Set.Ioi T', t ^ (-2 : ℝ) := by
        refine setIntegral_mono_on hInt1 hInt2 measurableSet_Ioi (fun t ht => ?_)
        rw [Set.mem_Ioi] at ht
        have ht0 : (0 : ℝ) < t := by linarith
        rw [Real.rpow_neg ht0.le, Real.rpow_two]
        exact inv_anti₀ (pow_pos ht0 2) (by nlinarith [sq_nonneg c])
    _ = 1 / T' := by
        rw [integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hT',
          show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        field_simp

/-- **Quadratic tail integral** (two-sided).  `∫_{|t| > T'} (c²+t²)⁻¹ ≤ 2/T'` — the
complement of `[−T', T']`, via the one-sided bound and the reflection `t ↦ −t`. -/
lemma integral_compl_Icc_inv_c_sq_le {c T' : ℝ} (hc : 0 < c) (hT' : 0 < T') :
    ∫ t in (Set.Icc (-T') T')ᶜ, (c ^ 2 + t ^ 2)⁻¹ ≤ 2 / T' := by
  have hg : Integrable (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) := Salt.SW.integrable_inv_c_sq_add_sq hc
  have hcompl : (Set.Icc (-T') T')ᶜ = Set.Iio (-T') ∪ Set.Ioi T' := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, Set.mem_union, Set.mem_Iio,
      Set.mem_Ioi]
  have hdisj : Disjoint (Set.Iio (-T')) (Set.Ioi T') := by
    rw [Set.disjoint_left]; intro x hx hx'
    simp only [Set.mem_Iio] at hx; simp only [Set.mem_Ioi] at hx'; linarith
  rw [hcompl, setIntegral_union hdisj measurableSet_Ioi hg.integrableOn hg.integrableOn]
  have hIoi := integral_Ioi_inv_c_sq_le hc hT'
  have hIio : ∫ t in Set.Iio (-T'), (c ^ 2 + t ^ 2)⁻¹ ≤ 1 / T' := by
    rw [setIntegral_congr_set (Iio_ae_eq_Iic)]
    have hrefl : (∫ t in Set.Iic (-T'), (c ^ 2 + t ^ 2)⁻¹)
        = ∫ t in Set.Ioi T', (c ^ 2 + t ^ 2)⁻¹ := by
      rw [← integral_comp_neg_Ioi T' (fun t => (c ^ 2 + t ^ 2)⁻¹)]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      simp only [neg_sq]
    rw [hrefl]; exact hIoi
  have h2 : (1 : ℝ) / T' + 1 / T' = 2 / T' := by ring
  linarith [hIoi, hIio, h2]

/-! ## TRUNC — the truncation of the contour integral at height `T' := 3T`

Cut the vertical line integral at `|Im s| = T'`; the tail over the complement of
`[−T', T']` is `P·log P/T`-grade, controlled by the `c`-line bound (`Σ Λ(n)/nᶜ` ≍
`log P`) times the window kernel's quadratic decay (`1/T'`).  Stated in the generic
Dirichlet-factor carrier so REP/ASM specialise it to `−ζ′/ζ` afterwards; the honest
tail constant is carried in-statement (Amendment L11-T's headroom, #253). -/

/-- **TRUNC — the truncation-tail bound.**  Truncating the contour integral of
`(Σ aₙ/n^{c+it})·windowKernel` to the height window `[−T', T']` costs at most
`(Σ ‖aₙ‖/nᶜ)·Cₖ(P,c)·(2/T')`: the Dirichlet factor is uniformly `≤ Σ ‖aₙ‖/nᶜ`, the
window kernel decays as `Cₖ(P,c)·(c²+t²)⁻¹`, and the complement tail integrates to
`2/T'`.  Boundary convention: the truncated integral is the closed set integral over
`Set.Icc (-T') T'`. -/
theorem rep_truncated (a : ℕ → ℂ) (ha0 : a 0 = 0) {P c T' : ℝ}
    (hP : 2 ≤ P) (hc : 0 < c) (hT' : 0 < T')
    (hsum : Summable fun n => ‖a n‖ / (n : ℝ) ^ c) :
    ‖(∫ t : ℝ, (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * windowKernel P c t)
        - ∫ t in Set.Icc (-T') T',
            (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * windowKernel P c t‖
      ≤ (∑' n, ‖a n‖ / (n : ℝ) ^ c)
          * (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2))
          * (2 / T') := by
  set F : ℝ → ℂ :=
    fun t => (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * windowKernel P c t with hFdef
  have hS0 : 0 ≤ ∑' n, ‖a n‖ / (n : ℝ) ^ c := tsum_nonneg (fun n => by positivity)
  have hCk0 : 0 ≤ 2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2) := by
    have : (0 : ℝ) < P := by linarith
    positivity
  -- F is integrable (difference of the two hat-kernel integrands)
  have hF_int : Integrable F := by
    rw [hFdef]
    have hU := integrable_dseries_mul_hatKernel a ha0 (X := 2 * P) (h := P)
      (by linarith) (by linarith) hc hsum
    have hL := integrable_dseries_mul_hatKernel a ha0 (X := P / 2) (h := P / 2)
      (by linarith) (by linarith) hc hsum
    have hrw : (fun (t : ℝ) => (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * windowKernel P c t)
        = fun (t : ℝ) => (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * hatKernel (2 * P) P c t
            - (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * hatKernel (P / 2) (P / 2) c t := by
      funext t; simp only [windowKernel]; ring
    rw [hrw]; exact hU.sub hL
  -- the truncation error is the complement integral
  have hsplit : (∫ t, F t) - (∫ t in Set.Icc (-T') T', F t)
      = ∫ t in (Set.Icc (-T') T')ᶜ, F t := by
    have h := integral_add_compl (measurableSet_Icc (a := -T') (b := T')) hF_int
    rw [← h]; ring
  rw [hsplit]
  calc ‖∫ t in (Set.Icc (-T') T')ᶜ, F t‖
      ≤ ∫ t in (Set.Icc (-T') T')ᶜ, ‖F t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in (Set.Icc (-T') T')ᶜ,
          (∑' n, ‖a n‖ / (n : ℝ) ^ c)
            * (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2))
            * (c ^ 2 + t ^ 2)⁻¹ := by
        refine setIntegral_mono_on hF_int.norm.integrableOn
          ((Salt.SW.integrable_inv_c_sq_add_sq hc).const_mul _).integrableOn
          measurableSet_Icc.compl (fun t _ => ?_)
        simp only [hFdef, norm_mul]
        exact (mul_le_mul (norm_dseries_le hc hsum t) (norm_windowKernel_le hP hc t)
          (norm_nonneg _) hS0).trans_eq (by ring)
    _ = (∑' n, ‖a n‖ / (n : ℝ) ^ c)
          * (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2))
          * ∫ t in (Set.Icc (-T') T')ᶜ, (c ^ 2 + t ^ 2)⁻¹ := by
        rw [← integral_const_mul]
    _ ≤ (∑' n, ‖a n‖ / (n : ℝ) ^ c)
          * (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2))
          * (2 / T') :=
        mul_le_mul_of_nonneg_left (integral_compl_Icc_inv_c_sq_le hc hT') (by positivity)

/-! ## ZFREE-RECT — the shifted rectangle is ζ-zero-free

The rectangle `[σ₀, c]×[−T', T']` shifted by `iu` (`|u| ≤ 2T`, `T' = 3T`, so the ζ argument
reaches height `≤ T' + 2T = 5T` EXACTLY — the R-3 refuter-audited budget) avoids every ζ-zero,
with `σ₀ = 1 − (c_vk/2)/D₃(5T)`, `D₃(t) = (log t)^{3/4}(loglog t)³`.

Two mathlib inputs (verified): `zeta_zero_free_region_pow` (`Vk/GrowthPow.lean`, the power region
`Re ρ ≤ 1 − c/D₃(|Im ρ|)` for `|Im ρ| ≥ T₀^pow`) covers the high heights via the monotonicity
`logD3_mono`; the compact `Re = 1` segment at height `≤ M := T₀^pow` is a positive `infDist`
from the closed zero set (`zeta_zero_free_strip_height`, the height-`M` generalization of the
landed `Salt.SW.zeta_zero_free_strip`) — REF-A's "compactness ALONE closes it".  The threshold
`T₁` makes `(c_vk/2)/D₃(5T)` finer than the fixed strip margin `ε₀`. -/

section ZFreeRect
open Metric

/-- **`D₃` monotonicity.**  `D₃(t) = (log t)^{3/4}(loglog t)³` is increasing above `e`
(both factors nonnegative and monotone once `log t > 1`).  The `vkTheta_anti` pattern,
non-reciprocated. -/
private lemma logD3_mono {t₁ t₂ : ℝ} (h1 : Real.exp 1 < t₁) (h12 : t₁ ≤ t₂) :
    (Real.log t₁) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t₁)) ^ (3 : ℕ)
      ≤ (Real.log t₂) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t₂)) ^ (3 : ℕ) := by
  have ht1pos : 0 < t₁ := lt_trans (Real.exp_pos 1) h1
  have hlog1 : 1 < Real.log t₁ := by
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) h1
  have hlog12 : Real.log t₁ ≤ Real.log t₂ := Real.log_le_log ht1pos h12
  have hll1 : 0 < Real.log (Real.log t₁) := Real.log_pos hlog1
  have hll12 : Real.log (Real.log t₁) ≤ Real.log (Real.log t₂) :=
    Real.log_le_log (by linarith) hlog12
  have hbase : (Real.log t₁) ^ ((3 : ℝ) / 4) ≤ (Real.log t₂) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow (by linarith) hlog12 (by norm_num)
  have hll3 : (Real.log (Real.log t₁)) ^ (3 : ℕ) ≤ (Real.log (Real.log t₂)) ^ (3 : ℕ) :=
    pow_le_pow_left₀ hll1.le hll12 3
  exact mul_le_mul hbase hll3 (by positivity) (Real.rpow_nonneg (by linarith) _)

/-- **The fixed zero-free strip at height `M`** (the compactness sub-stone).  For any `M ≥ 0`
there is `ε₀ > 0` with `Re ρ ≤ 1 − ε₀` for every ζ-zero `ρ` of height `|Im ρ| ≤ M`.  The
compact `Re = 1` segment `{1 + it : |t| ≤ M}` is disjoint from the closed zero set
(`riemannZeta_ne_zero_of_one_le_re`), so its continuous positive `infDist` to the zero set
attains a positive minimum `ε₀`; any low-height zero is at horizontal distance `1 − Re ρ ≥ ε₀`.
The height-`M` generalization of the landed `Salt.SW.zeta_zero_free_strip` (`M = 1`). -/
lemma zeta_zero_free_strip_height {M : ℝ} (hM : 0 ≤ M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {ρ : ℂ}, riemannZeta ρ = 0 → |ρ.im| ≤ M → ρ.re ≤ 1 - ε₀ := by
  have hZne : riemannZetaZeros.Nonempty := by
    refine ⟨-2, ?_⟩
    rw [mem_riemannZetaZeros]
    have h := riemannZeta_neg_two_mul_nat_add_one 0
    simpa using h
  set L₀ : Set ℂ := (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) '' Set.Icc (-M : ℝ) M with hL₀
  have hL₀compact : IsCompact L₀ :=
    isCompact_Icc.image (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hL₀ne : L₀.Nonempty := (Set.nonempty_Icc.mpr (by linarith)).image _
  have hpos : ∀ x ∈ L₀, 0 < infDist x riemannZetaZeros := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := hx
    have hxre : ((1 : ℂ) + (t : ℂ) * I).re = 1 := by simp
    have hne : (1 : ℂ) + (t : ℂ) * I ∉ riemannZetaZeros := by
      rw [mem_riemannZetaZeros]
      exact riemannZeta_ne_zero_of_one_le_re (le_of_eq hxre.symm)
    exact (isClosed_riemannZetaZeros.notMem_iff_infDist_pos hZne).mp hne
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

/-- **ZFREE-RECT (the zero margin).**  There are `c_vk > 0`, `T₁ ≥ 3` such that for `T ≥ T₁`
the denominator `D₃(5T)` is positive, and every ζ-zero `ρ` of height `|Im ρ| ≤ 5T` obeys the
uniform region margin `Re ρ ≤ 1 − c_vk/D₃(5T)`.  High heights `|Im ρ| ≥ M := T₀^pow` come from
`zeta_zero_free_region_pow` + `logD3_mono` (`D₃(|Im ρ|) ≤ D₃(5T)`); low heights `|Im ρ| ≤ M`
from `zeta_zero_free_strip_height` (`Re ρ ≤ 1 − ε₀ ≤ 1 − c_vk/D₃(5T)`, the threshold `T₁`
forcing `c_vk/D₃(5T) ≤ ε₀`).  This is the deliverable EDGE rides for its `hdist` min-distance. -/
theorem rect_zero_free_margin :
    ∃ (c_vk T₁ : ℝ), 0 < c_vk ∧ 3 ≤ T₁ ∧
      ∀ (T : ℝ), T₁ ≤ T →
        0 < (Real.log (5 * T)) ^ ((3 : ℝ) / 4) * (Real.log (Real.log (5 * T))) ^ (3 : ℕ) ∧
        ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≤ 5 * T →
          ρ.re ≤ 1 - c_vk / ((Real.log (5 * T)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T))) ^ (3 : ℕ)) := by
  obtain ⟨c_pow, M, hc_pow, hM3, hregion⟩ := Salt.Vk.zeta_zero_free_region_pow
  obtain ⟨ε₀, hε₀, hstrip⟩ := zeta_zero_free_strip_height (M := M) (by linarith : (0 : ℝ) ≤ M)
  set B : ℝ := c_pow / ε₀ with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set E : ℝ := Real.exp (Real.exp 1 + B ^ ((4 : ℝ) / 3)) with hEdef
  set T₁ : ℝ := max 3 (max M E) with hT₁def
  refine ⟨c_pow, T₁, hc_pow, le_max_left _ _, ?_⟩
  intro T hT
  have hMle : M ≤ T := le_trans (le_trans (le_max_left M E) (le_max_right 3 _)) hT
  have hEle : E ≤ T := le_trans (le_trans (le_max_right M E) (le_max_right 3 _)) hT
  have hT0 : (0 : ℝ) < T := by linarith [le_trans (le_max_left 3 _) hT]
  have hE5T : E ≤ 5 * T := by linarith
  -- the key height fact: log(5T) ≥ e + B^{4/3}
  have hL5 : Real.exp 1 + B ^ ((4 : ℝ) / 3) ≤ Real.log (5 * T) := by
    rw [← Real.log_exp (Real.exp 1 + B ^ ((4 : ℝ) / 3)), ← hEdef]
    exact Real.log_le_log (Real.exp_pos _) hE5T
  have hB43nn : (0 : ℝ) ≤ B ^ ((4 : ℝ) / 3) := Real.rpow_nonneg hB0 _
  have hexp1_2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL5e : Real.exp 1 ≤ Real.log (5 * T) := by linarith
  have hL5_1 : (1 : ℝ) < Real.log (5 * T) := by linarith
  have hL5pos : (0 : ℝ) < Real.log (5 * T) := by linarith
  have hℓ5 : (1 : ℝ) ≤ Real.log (Real.log (5 * T)) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hL5e
  have hℓ5cube : (1 : ℝ) ≤ (Real.log (Real.log (5 * T))) ^ (3 : ℕ) := one_le_pow₀ hℓ5
  have hL534pos : (0 : ℝ) < (Real.log (5 * T)) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL5pos _
  set D : ℝ := (Real.log (5 * T)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * T))) ^ (3 : ℕ) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  -- L5^{3/4} ≥ B  (so D ≥ B)
  have hBrpow : B = (B ^ ((4 : ℝ) / 3)) ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_mul hB0]; norm_num
  have hL534geB : B ≤ (Real.log (5 * T)) ^ ((3 : ℝ) / 4) := by
    rw [hBrpow]
    exact Real.rpow_le_rpow hB43nn (by linarith) (by norm_num)
  have hDgeB : B ≤ D := by
    rw [hDdef]
    calc B = B * 1 := (mul_one B).symm
      _ ≤ (Real.log (5 * T)) ^ ((3 : ℝ) / 4) * (Real.log (Real.log (5 * T))) ^ (3 : ℕ) :=
          mul_le_mul hL534geB hℓ5cube (by norm_num) hL534pos.le
  -- c_pow / D ≤ ε₀
  have hcpowD : c_pow / D ≤ ε₀ := by
    rw [div_le_iff₀ hDpos]
    have hcε : c_pow = ε₀ * B := by rw [hBdef]; field_simp
    calc c_pow = ε₀ * B := hcε
      _ ≤ ε₀ * D := mul_le_mul_of_nonneg_left hDgeB hε₀.le
  refine ⟨hDpos, ?_⟩
  intro ρ hρ0 hρim
  by_cases hcase : M ≤ |ρ.im|
  · -- high height: the power region + `D₃` monotonicity
    have hργ : Real.exp 1 < |ρ.im| := by
      have h3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      exact lt_of_lt_of_le h3 (le_trans hM3 hcase)
    have hreg := hregion ρ hρ0 hcase
    have hmono := logD3_mono hργ hρim
    have hden_ρ_pos : 0 < (Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ) := by
      have hlρ : 1 < Real.log |ρ.im| := by
        rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hργ
      have : 0 < Real.log (Real.log |ρ.im|) := Real.log_pos hlρ
      positivity
    have hstep : c_pow / D ≤ c_pow / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ)) :=
      div_le_div_of_nonneg_left hc_pow.le hden_ρ_pos (by rw [hDdef]; exact hmono)
    linarith [hreg, hstep]
  · -- low height: the fixed strip
    have hlow : |ρ.im| < M := not_le.mp hcase
    have hst := hstrip hρ0 (le_of_lt hlow)
    linarith [hst, hcpowD]

/-- **ZFREE-RECT.**  There are `c_vk > 0`, `T₁ ≥ 3` such that for `T ≥ T₁`, every point `w`
with `Re w ≥ σ₀ := 1 − (c_vk/2)/D₃(5T)` and `|Im w| ≤ 5T` has `ζ(w) ≠ 0`: the shifted rectangle
is ζ-zero-free.  Strict corollary of `rect_zero_free_margin` (a zero would have
`Re w ≤ 1 − c_vk/D₃(5T) < 1 − (c_vk/2)/D₃(5T) = σ₀`, contradicting `Re w ≥ σ₀`). -/
theorem rect_zero_free :
    ∃ (c_vk T₁ : ℝ), 0 < c_vk ∧ 3 ≤ T₁ ∧
      ∀ (T : ℝ), T₁ ≤ T → ∀ w : ℂ,
        1 - (c_vk / 2) / ((Real.log (5 * T)) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log (5 * T))) ^ (3 : ℕ)) ≤ w.re →
        |w.im| ≤ 5 * T → riemannZeta w ≠ 0 := by
  obtain ⟨c_vk, T₁, hc, hT₁, hmargin⟩ := rect_zero_free_margin
  refine ⟨c_vk, T₁, hc, hT₁, ?_⟩
  intro T hT w hwre hwim hw0
  obtain ⟨hDpos, hmarg⟩ := hmargin T hT
  set D : ℝ := (Real.log (5 * T)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * T))) ^ (3 : ℕ) with hDdef
  have hmr := hmarg w hw0 hwim
  -- (c_vk/2)/D < c_vk/D since c_vk/2 < c_vk and D > 0
  have hlt : (c_vk / 2) / D < c_vk / D := by
    have h1 : c_vk / D - (c_vk / 2) / D = (c_vk / 2) / D := by ring
    have h2 : 0 < (c_vk / 2) / D := div_pos (by linarith) hDpos
    linarith [h1, h2]
  linarith [hwre, hmr, hlt]

end ZFreeRect

/-! ## POLE-ROW — the convergent pole-row sum

For a fixed shift `t'`, summing the pole main term `‖W(1 + i(t − t'))‖` over ALL `t ∈ 𝒯`
(INCLUDING the diagonal `t = t'`, per REF-A's no-split repair — `W(1) ≍ P`, one finite entry)
is `≤ c_W·P`.  The Mellin kernel decays quadratically (`‖windowKernel P 1 u‖ ≤ 22P/(1+u²)`,
`norm_windowKernel_le` at abscissa `1`); well-spacing (`1`-separation) makes
`Σ_{t∈𝒯} 1/(1+(t−t')²)` convergent, bounded by `2π` via the unit-window integral comparison
`sum_intervalIntegral_le` and `∫_ℝ 1/(1+x²) = π`.  A NEW convergent-series stone (not
`primePoly_wellspaced_l2`, whose bound is `T`-linear and would blow the frozen `P`-term). -/

section PoleRow
open intervalIntegral

/-- **POLE-ROW.**  For a well-spaced `𝒯 ⊆ [−T, T]`, a fixed shift `t'`, and `2 ≤ P`, the pole-row
sum of the window Mellin kernel over the diagonal-inclusive set is `≤ 44π·P`:
`Σ_{t∈𝒯} ‖windowKernel P 1 (t − t')‖ ≤ 44·π·P`.  The `P·Σ|η|²` pole contribution of the ASM
assembly. -/
theorem pole_row_sum {P T : ℝ} (hP : 2 ≤ P) (hT : 0 ≤ T) (𝒯 : Finset ℝ)
    (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) (t' : ℝ) :
    ∑ t ∈ 𝒯, ‖windowKernel P 1 (t - t')‖ ≤ 44 * Real.pi * P := by
  have hP0 : 0 < P := by linarith
  have hPne : P ≠ 0 := hP0.ne'
  -- the kernel constant `Cₖ(P,1) = 22P`
  have hexp : ((1 : ℝ) + 1) = ((2 : ℕ) : ℝ) := by norm_num
  have hCk : 2 * (2 * P + P) ^ ((1 : ℝ) + 1) / P + 2 * (P / 2 + P / 2) ^ ((1 : ℝ) + 1) / (P / 2)
      = 22 * P := by
    rw [hexp, Real.rpow_natCast, Real.rpow_natCast]; field_simp; ring
  -- per-term quadratic norm bound
  have hnorm : ∀ t : ℝ, ‖windowKernel P 1 (t - t')‖ ≤ 22 * P * (1 + (t - t') ^ 2)⁻¹ := by
    intro t
    have h := norm_windowKernel_le (P := P) (c := 1) hP (by norm_num) (t - t')
    refine h.trans (le_of_eq ?_)
    rw [one_pow, hCk]
  -- the continuous nonneg cutoff `g s = 1/(1+(s-t')²)`
  set g : ℝ → ℝ := fun s => (1 + (s - t') ^ 2)⁻¹ with hgdef
  have hg_cont : Continuous g := by
    rw [hgdef]; apply Continuous.inv₀
    · fun_prop
    · intro s; exact (by positivity : (0 : ℝ) < 1 + (s - t') ^ 2).ne'
  have hg_nonneg : ∀ s, 0 ≤ g s := fun s => by rw [hgdef]; positivity
  -- per-term lower bound: `1/(1+(t-t')²) ≤ 2·∫_{t-½}^{t+½} g`
  have hlb : ∀ t : ℝ, (1 + (t - t') ^ 2)⁻¹ ≤ 2 * ∫ s in (t - 1 / 2)..(t + 1 / 2), g s := by
    intro t
    have hle : (1 / 2) * (1 + (t - t') ^ 2)⁻¹ ≤ ∫ s in (t - 1 / 2)..(t + 1 / 2), g s := by
      have hconst : ∫ _s in (t - 1 / 2)..(t + 1 / 2), (1 / 2) * (1 + (t - t') ^ 2)⁻¹
          ≤ ∫ s in (t - 1 / 2)..(t + 1 / 2), g s := by
        refine intervalIntegral.integral_mono_on (by linarith)
          intervalIntegral.intervalIntegrable_const
          (hg_cont.intervalIntegrable _ _) (fun s hs => ?_)
        rw [Set.mem_Icc] at hs
        change (1 / 2) * (1 + (t - t') ^ 2)⁻¹ ≤ (1 + (s - t') ^ 2)⁻¹
        have hb : 1 + (s - t') ^ 2 ≤ 2 * (1 + (t - t') ^ 2) := by
          nlinarith [sq_nonneg (s - 2 * t + t'),
            mul_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ s - (t - 1 / 2))
              (by linarith [hs.2] : (0 : ℝ) ≤ (t + 1 / 2) - s)]
        have hpos_s : (0 : ℝ) < 1 + (s - t') ^ 2 := by positivity
        rw [show (1 / 2) * (1 + (t - t') ^ 2)⁻¹ = (2 * (1 + (t - t') ^ 2))⁻¹ from by
          rw [mul_inv]; ring]
        exact inv_anti₀ hpos_s hb
      rw [intervalIntegral.integral_const, smul_eq_mul] at hconst
      have : (t + 1 / 2 - (t - 1 / 2)) = 1 := by ring
      rw [this, one_mul] at hconst
      exact hconst
    linarith
  -- the interval integral `∫_A^B g ≤ π`
  set A : ℝ := -T - 1 / 2 with hA
  set B : ℝ := T + 1 / 2 with hB
  have hAB : A ≤ B := by rw [hA, hB]; linarith
  have hInt_le : ∫ s in A..B, g s ≤ Real.pi := by
    have hcomp : (∫ s in A..B, g s) = ∫ x in (A - t')..(B - t'), (1 + x ^ 2)⁻¹ := by
      rw [hgdef]; exact intervalIntegral.integral_comp_sub_right (fun x => (1 + x ^ 2)⁻¹) t'
    rw [hcomp, integral_inv_one_add_sq]
    have h1 : Real.arctan (B - t') ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two _).le
    have h2 : -(Real.pi / 2) ≤ Real.arctan (A - t') := (Real.neg_pi_div_two_lt_arctan _).le
    linarith
  -- the well-spaced window sum
  have hwin : ∀ t ∈ 𝒯, Set.Ioc (t - 1 / 2) (t + 1 / 2) ⊆ Set.Ioc A B := by
    intro t ht
    have h := Set.mem_Icc.mp (hsub t ht)
    exact Set.Ioc_subset_Ioc (by rw [hA]; linarith [h.1]) (by rw [hB]; linarith [h.2])
  have hsum_int : ∑ t ∈ 𝒯, (∫ s in (t - 1 / 2)..(t + 1 / 2), g s) ≤ ∫ s in A..B, g s :=
    sum_intervalIntegral_le g hg_cont hg_nonneg 𝒯 A B hAB hws hwin
  -- assemble
  have hseries : ∑ t ∈ 𝒯, (1 + (t - t') ^ 2)⁻¹ ≤ 2 * Real.pi := by
    calc ∑ t ∈ 𝒯, (1 + (t - t') ^ 2)⁻¹
        ≤ ∑ t ∈ 𝒯, 2 * ∫ s in (t - 1 / 2)..(t + 1 / 2), g s :=
          Finset.sum_le_sum (fun t _ => hlb t)
      _ = 2 * ∑ t ∈ 𝒯, (∫ s in (t - 1 / 2)..(t + 1 / 2), g s) := by rw [Finset.mul_sum]
      _ ≤ 2 * Real.pi := by linarith [hsum_int, hInt_le]
  calc ∑ t ∈ 𝒯, ‖windowKernel P 1 (t - t')‖
      ≤ ∑ t ∈ 𝒯, 22 * P * (1 + (t - t') ^ 2)⁻¹ := Finset.sum_le_sum (fun t _ => hnorm t)
    _ = 22 * P * ∑ t ∈ 𝒯, (1 + (t - t') ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 22 * P * (2 * Real.pi) := by
        apply mul_le_mul_of_nonneg_left hseries (by positivity)
    _ = 44 * Real.pi * P := by ring

end PoleRow

end Salt.MR
