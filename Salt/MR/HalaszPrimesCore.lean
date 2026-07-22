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
reaches height `≤ T' + 2T = 5T` — the R-3 refuter-audited budget; Amendment L11-W′ prices the
disc-core's zeros at the honest `5T+1`, so all height evaluations downstream read `5T+1`), avoids
every ζ-zero, with `σ₀ = 1 − (c_vk/2)/D₃(5T+1)`, `D₃(t) = (log t)^{3/4}(loglog t)³`.

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

/-! ## RES infrastructure — the window Mellin kernel as a holomorphic function of `s`

The landed `windowKernel P c t` is the per-abscissa/height boundary trace; to shift the
contour it must be recognised as the boundary value of a function `windowMellin P s`
holomorphic in the complex variable `s` away from its own poles `{0, −1}` (which sit far to
the LEFT of the shifted rectangle `Re s ∈ [σ₀, c]`, `σ₀ ≈ 1`).  `hatMellin X h s` is the
Mellin factor of a single hat; `windowMellin` the difference. -/

section WindowMellin

/-- The hat Mellin factor as a holomorphic function of `s`:
`hatMellin X h s = ((X+h)^{s+1} − X^{s+1})/(h·s·(s+1))`.  Definitionally
`hatKernel X h c t = hatMellin X h (c + it)`. -/
noncomputable def hatMellin (X h : ℝ) (s : ℂ) : ℂ :=
  (((X + h : ℝ) : ℂ) ^ (s + 1) - ((X : ℝ) : ℂ) ^ (s + 1)) / ((h : ℂ) * (s * (s + 1)))

/-- The window Mellin factor `windowMellin P s = hatMellin(2P,P,s) − hatMellin(P/2,P/2,s)`. -/
noncomputable def windowMellin (P : ℝ) (s : ℂ) : ℂ :=
  hatMellin (2 * P) P s - hatMellin (P / 2) (P / 2) s

/-- `hatKernel X h c t = hatMellin X h (c + it)` (definitional). -/
lemma hatKernel_eq_hatMellin (X h c t : ℝ) :
    hatKernel X h c t = hatMellin X h ((c : ℂ) + (t : ℂ) * I) := rfl

/-- `windowKernel P c t = windowMellin P (c + it)` (definitional). -/
lemma windowKernel_eq_windowMellin (P c t : ℝ) :
    windowKernel P c t = windowMellin P ((c : ℂ) + (t : ℂ) * I) := rfl

/-- `hatMellin X h` is differentiable at every `s ∉ {0, −1}` (given `X, h > 0`). -/
lemma hatMellin_differentiableAt {X h : ℝ} (hX : 0 < X) (hh : 0 < h) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) : DifferentiableAt ℂ (hatMellin X h) s := by
  have hXhC : ((X + h : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hXC : ((X : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hhC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  apply DifferentiableAt.div
  · exact ((differentiableAt_id.add_const 1).const_cpow (Or.inl hXhC)).sub
      ((differentiableAt_id.add_const 1).const_cpow (Or.inl hXC))
  · exact (differentiableAt_id.mul (differentiableAt_id.add_const 1)).const_mul (h : ℂ)
  · exact mul_ne_zero hhC (mul_ne_zero hs0 hs1)

/-- `windowMellin P` is differentiable at every `s ∉ {0, −1}` (given `P > 0`). -/
lemma windowMellin_differentiableAt {P : ℝ} (hP : 0 < P) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) : DifferentiableAt ℂ (windowMellin P) s :=
  (hatMellin_differentiableAt (by linarith) (by linarith) hs0 hs1).sub
    (hatMellin_differentiableAt (by linarith) (by linarith) hs0 hs1)

end WindowMellin

/-! ## RES — the pole residue term of the shifted rectangle

The shifted rectangle `[σ₀, c] × [−T', T']`, ζ-zero-free on the argument `s − iu`, carries a
SINGLE interior pole of `−ζ′/ζ(s − iu)` at `s = 1 + iu` (residue `+1`).  The boundary integral
extracts it: `∮ = 2πi·windowMellin P (1 + iu) = 2πi·windowKernel P 1 u`.

Route (the `perron_trunc` residue device, generalised): write the integrand
`(−ζ′/ζ)(s − iu)·windowMellin P s` as `φ(s)/(s − p)` with
`φ(s) = windowMellin P s − (s − p)·logDeriv Zc(s − iu)·windowMellin P s` analytic on the closed
rectangle (`Zc = (·−1)ζ` entire, nonvanishing on the zero-free argument; `windowMellin` analytic
away from its poles `{0,−1}`), then `rectBI_cif_eq` gives `2πi·φ(p) = 2πi·windowMellin P p`. -/

section PoleResidue
open Complex Salt.SW

/-- `Zc w ≠ 0` whenever `ζ w ≠ 0` (the pole point `w = 1` has `Zc 1 = 1 ≠ 0`). -/
lemma Zc_ne_zero_of_zeta_ne {w : ℂ} (h : riemannZeta w ≠ 0) : Zc w ≠ 0 := by
  rcases eq_or_ne w 1 with rfl | hw
  · rw [Zc_one]; norm_num
  · rw [Zc_eq_of_ne hw]; exact mul_ne_zero (sub_ne_zero.mpr hw) h

/-- `logDeriv Zc` is analytic at every `w` with `Zc w ≠ 0` (`Zc` entire, `deriv Zc` entire). -/
lemma logDeriv_Zc_analyticAt {w : ℂ} (hw : Zc w ≠ 0) : AnalyticAt ℂ (logDeriv Zc) w := by
  have hZana : AnalyticOnNhd ℂ Zc univ :=
    Zc_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hdana : AnalyticOnNhd ℂ (deriv Zc) univ := hZana.deriv
  have h : AnalyticAt ℂ (fun z => deriv Zc z / Zc z) w :=
    (hdana w (mem_univ _)).div (hZana w (mem_univ _)) hw
  rw [show logDeriv Zc = fun z => deriv Zc z / Zc z from rfl]; exact h

/-- `s ↦ logDeriv Zc (s − iu)` is differentiable on any set where `ζ(s − iu) ≠ 0`. -/
lemma logDeriv_Zc_shift_differentiableOn {u : ℝ} {K : Set ℂ}
    (hK : ∀ s ∈ K, riemannZeta (s - (u : ℂ) * I) ≠ 0) :
    DifferentiableOn ℂ (fun s => logDeriv Zc (s - (u : ℂ) * I)) K := by
  intro s hs
  have hZne : Zc (s - (u : ℂ) * I) ≠ 0 := Zc_ne_zero_of_zeta_ne (hK s hs)
  have h1 : DifferentiableAt ℂ (logDeriv Zc) (s - (u : ℂ) * I) :=
    (logDeriv_Zc_analyticAt hZne).differentiableAt
  exact (h1.comp s (differentiableAt_id.sub_const _)).differentiableWithinAt

/-- `windowMellin P` is differentiable on any set whose real parts stay `≥ σ₀ > 0`. -/
lemma windowMellin_differentiableOn {P σ₀ : ℝ} (hP : 0 < P) (hσ₀ : 0 < σ₀) {K : Set ℂ}
    (hK : ∀ s ∈ K, σ₀ ≤ s.re) : DifferentiableOn ℂ (windowMellin P) K := by
  intro s hs
  have hsre : 0 < s.re := lt_of_lt_of_le hσ₀ (hK s hs)
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
  have hs1 : s + 1 ≠ 0 := fun h => by
    have : (s + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at this; linarith
  exact (windowMellin_differentiableAt hP hs0 hs1).differentiableWithinAt

/-- **RES — the pole residue term.**  For the shifted rectangle `[σ₀, c] × [−T', T']`
(`0 < σ₀ < 1 < c`, `|u| < T'`) that is ζ-zero-free on the shifted argument `s − iu`, the
boundary integral of `(−ζ′/ζ)(s − iu)·windowMellin P s` equals `2πi·windowMellin P (1 + iu)`
(the residue of `−ζ′/ζ` at its single interior pole `s = 1 + iu` is `+1`, and
`windowMellin P (1 + iu) = windowKernel P 1 u`). -/
theorem pole_residue_term {P σ₀ c u T' : ℝ} (hP : 0 < P)
    (hσ₀0 : 0 < σ₀) (hσ₀1 : σ₀ < 1) (h1c : 1 < c) (hu : |u| < T')
    (hzf : ∀ s : ℂ, s ∈ closedRect ((σ₀ : ℂ) + ((-T' : ℝ) : ℂ) * I) ((c : ℂ) + (T' : ℂ) * I) →
        riemannZeta (s - (u : ℂ) * I) ≠ 0) :
    rectBI ((σ₀ : ℂ) + ((-T' : ℝ) : ℂ) * I) ((c : ℂ) + (T' : ℂ) * I)
        (fun s => (-logDeriv riemannZeta (s - (u : ℂ) * I)) * windowMellin P s)
      = 2 * (Real.pi : ℂ) * I * windowMellin P ((1 : ℂ) + (u : ℂ) * I) := by
  set z : ℂ := (σ₀ : ℂ) + ((-T' : ℝ) : ℂ) * I with hz
  set w : ℂ := (c : ℂ) + (T' : ℂ) * I with hw
  set p : ℂ := (1 : ℂ) + (u : ℂ) * I with hp
  have hzre : z.re = σ₀ := by rw [hz]; simp
  have hzim : z.im = -T' := by rw [hz]; simp
  have hwre : w.re = c := by rw [hw]; simp
  have hwim : w.im = T' := by rw [hw]; simp
  have hpre : p.re = 1 := by rw [hp]; simp
  have hpim : p.im = u := by rw [hp]; simp
  have hT'0 : 0 < T' := lt_of_le_of_lt (abs_nonneg u) hu
  have hσ₀c : σ₀ < c := lt_trans hσ₀1 h1c
  obtain ⟨hulb, huub⟩ := abs_lt.mp hu
  -- the analytic numerator φ
  set φ : ℂ → ℂ :=
    fun s => windowMellin P s - (s - p) * logDeriv Zc (s - (u : ℂ) * I) * windowMellin P s
    with hφdef
  -- coordinate helpers for the boundary points
  have hre_pt : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * I).re = a := fun a b => by simp
  have him_pt : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * I).im = b := fun a b => by simp
  -- membership: closedRect real parts lie in [σ₀, c]
  have hmem_re : ∀ s ∈ closedRect z w, σ₀ ≤ s.re := by
    intro s hs
    rw [closedRect, Complex.mem_reProdIm] at hs
    have h := hs.1
    rw [hzre, hwre, Set.uIcc_of_le hσ₀c.le, Set.mem_Icc] at h
    exact h.1
  -- windowMellin analytic on the rectangle
  have hWM_diff : DifferentiableOn ℂ (windowMellin P) (closedRect z w) :=
    windowMellin_differentiableOn hP hσ₀0 hmem_re
  -- logDeriv Zc (·−iu) differentiable on the rectangle
  have hLD_diff : DifferentiableOn ℂ (fun s => logDeriv Zc (s - (u : ℂ) * I)) (closedRect z w) :=
    logDeriv_Zc_shift_differentiableOn hzf
  -- φ analytic on the rectangle
  have hφ_diff : DifferentiableOn ℂ φ (closedRect z w) := by
    rw [hφdef]
    exact hWM_diff.sub
      ((((differentiableOn_id.sub_const p).mul hLD_diff).mul hWM_diff))
  -- the pointwise split off the pole
  have hsplit_pt : ∀ s : ℂ, riemannZeta (s - (u : ℂ) * I) ≠ 0 → s ≠ p →
      (-logDeriv riemannZeta (s - (u : ℂ) * I)) * windowMellin P s = φ s / (s - p) := by
    intro s hζ hsp
    have hw1 : s - (u : ℂ) * I ≠ 1 := by
      intro h
      apply hsp
      rw [hp]; rw [sub_eq_iff_eq_add] at h; rw [h]
    have hspne : s - p ≠ 0 := sub_ne_zero.mpr hsp
    have hsub : (s - (u : ℂ) * I) - 1 = s - p := by rw [hp]; ring
    have hpole := logDeriv_zeta_eq hw1 hζ
    rw [hpole, hsub, hφdef]
    field_simp
    ring
  -- edge-agreement EqOn facts (beta-reduced, matching the `simp only [rectBI]` shape)
  have hbot : Set.EqOn
      (fun x : ℝ => (-logDeriv riemannZeta (((x : ℂ) + (z.im : ℂ) * I) - (u : ℂ) * I))
        * windowMellin P ((x : ℂ) + (z.im : ℂ) * I))
      (fun x : ℝ => φ ((x : ℂ) + (z.im : ℂ) * I) / (((x : ℂ) + (z.im : ℂ) * I) - p))
      (Set.uIcc z.re w.re) := by
    intro x hx
    have hmem : ((x : ℂ) + (z.im : ℂ) * I) ∈ closedRect z w := by
      rw [closedRect, Complex.mem_reProdIm]
      exact ⟨by rw [hre_pt x z.im]; exact hx, by rw [him_pt x z.im]; exact left_mem_uIcc⟩
    refine hsplit_pt _ (hzf _ hmem) (fun h => ?_)
    have hne := congrArg Complex.im h; rw [him_pt x z.im, hzim, hpim] at hne; linarith
  have htop : Set.EqOn
      (fun x : ℝ => (-logDeriv riemannZeta (((x : ℂ) + (w.im : ℂ) * I) - (u : ℂ) * I))
        * windowMellin P ((x : ℂ) + (w.im : ℂ) * I))
      (fun x : ℝ => φ ((x : ℂ) + (w.im : ℂ) * I) / (((x : ℂ) + (w.im : ℂ) * I) - p))
      (Set.uIcc z.re w.re) := by
    intro x hx
    have hmem : ((x : ℂ) + (w.im : ℂ) * I) ∈ closedRect z w := by
      rw [closedRect, Complex.mem_reProdIm]
      exact ⟨by rw [hre_pt x w.im]; exact hx, by rw [him_pt x w.im]; exact right_mem_uIcc⟩
    refine hsplit_pt _ (hzf _ hmem) (fun h => ?_)
    have hne := congrArg Complex.im h; rw [him_pt x w.im, hwim, hpim] at hne; linarith
  have hright : Set.EqOn
      (fun y : ℝ => (-logDeriv riemannZeta (((w.re : ℂ) + (y : ℂ) * I) - (u : ℂ) * I))
        * windowMellin P ((w.re : ℂ) + (y : ℂ) * I))
      (fun y : ℝ => φ ((w.re : ℂ) + (y : ℂ) * I) / (((w.re : ℂ) + (y : ℂ) * I) - p))
      (Set.uIcc z.im w.im) := by
    intro y hy
    have hmem : ((w.re : ℂ) + (y : ℂ) * I) ∈ closedRect z w := by
      rw [closedRect, Complex.mem_reProdIm]
      exact ⟨by rw [hre_pt w.re y]; exact right_mem_uIcc, by rw [him_pt w.re y]; exact hy⟩
    refine hsplit_pt _ (hzf _ hmem) (fun h => ?_)
    have hne := congrArg Complex.re h; rw [hre_pt w.re y, hwre, hpre] at hne; linarith
  have hleft : Set.EqOn
      (fun y : ℝ => (-logDeriv riemannZeta (((z.re : ℂ) + (y : ℂ) * I) - (u : ℂ) * I))
        * windowMellin P ((z.re : ℂ) + (y : ℂ) * I))
      (fun y : ℝ => φ ((z.re : ℂ) + (y : ℂ) * I) / (((z.re : ℂ) + (y : ℂ) * I) - p))
      (Set.uIcc z.im w.im) := by
    intro y hy
    have hmem : ((z.re : ℂ) + (y : ℂ) * I) ∈ closedRect z w := by
      rw [closedRect, Complex.mem_reProdIm]
      exact ⟨by rw [hre_pt z.re y]; exact left_mem_uIcc, by rw [him_pt z.re y]; exact hy⟩
    refine hsplit_pt _ (hzf _ hmem) (fun h => ?_)
    have hne := congrArg Complex.re h; rw [hre_pt z.re y, hzre, hpre] at hne; linarith
  -- assemble the rectBI congruence
  have hcongr : rectBI z w (fun s => (-logDeriv riemannZeta (s - (u : ℂ) * I)) * windowMellin P s)
      = rectBI z w (fun s => φ s / (s - p)) := by
    simp only [rectBI]
    rw [intervalIntegral.integral_congr hbot, intervalIntegral.integral_congr htop,
      intervalIntegral.integral_congr hright, intervalIntegral.integral_congr hleft]
  rw [hcongr]
  -- the residue extraction
  have hcif := rectBI_cif_eq (z := z) (w := w) (p := p) (φ := φ) hφ_diff
    (by rw [hzre, hwre]; exact hσ₀c)
    (by rw [hzim, hwim]; linarith)
    ⟨by rw [hzre, hpre]; exact hσ₀1, by rw [hwre, hpre]; exact h1c⟩
    ⟨by rw [hzim, hpim]; exact hulb, by rw [hwim, hpim]; exact huub⟩
  rw [hcif]
  -- φ p = windowMellin P p
  have hφp : φ p = windowMellin P p := by rw [hφdef]; simp
  rw [hφp, hp]

end PoleResidue

/-! ## EDGE support — the compact-max bound on `logDeriv Zc`

The moderate-height regime of the left edge (`|Im| ≤ M`, the strip threshold): via
`logDeriv ζ = logDeriv Zc − 1/(z−1)` the entire nonvanishing factor `logDeriv Zc` is continuous
on the compact box `[1−δ₀, c] × [−M, M]` (zero-free by the fixed strip; pole point `z = 1` exempt
via `Zc 1 = 1 ≠ 0`), hence bounded by a constant `C₀`.  The `1/(z−1)` pole is priced separately
(`1/dist`-grade, `≤ D₃`-grade on the left edge) in the ASM assembly. -/

section EdgeSupport
open Complex Set Salt.SW

/-- **EDGE moderate-height max.**  For any height cap `M ≥ 0` and abscissa cap `c ≥ 1` there are
`δ₀ > 0`, `C₀` with `‖logDeriv Zc z‖ ≤ C₀` for every `z` with `1 − δ₀ ≤ Re z ≤ c`, `|Im z| ≤ M`:
`Zc = (·−1)ζ` is entire and (by the fixed zero-free strip at height `M`, `δ₀` finer than its
margin `ε₀`) nonvanishing on the box, so `logDeriv Zc` is continuous on the compact box and
attains a finite bound. -/
lemma logDeriv_Zc_compact_bound {M c : ℝ} (hM : 0 ≤ M) (_hc : 1 ≤ c) :
    ∃ (δ₀ C₀ : ℝ), 0 < δ₀ ∧
      ∀ z : ℂ, 1 - δ₀ ≤ z.re → z.re ≤ c → |z.im| ≤ M → ‖logDeriv Zc z‖ ≤ C₀ := by
  obtain ⟨ε₀, hε₀, hstrip⟩ := zeta_zero_free_strip_height hM
  set δ₀ : ℝ := ε₀ / 2 with hδ₀def
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀def]; linarith
  set K : Set ℂ := (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * I)
    '' (Set.Icc (1 - δ₀) c ×ˢ Set.Icc (-M) M) with hKdef
  have hKcompact : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  -- Zc nonvanishing on K
  have hZne : ∀ z ∈ K, Zc z ≠ 0 := by
    intro z hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hz
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hab
    obtain ⟨⟨ha1, _ha2⟩, hb1, hb2⟩ := hab
    have hzre : ((a : ℂ) + (b : ℂ) * I).re = a := by simp
    have hzim : ((a : ℂ) + (b : ℂ) * I).im = b := by simp
    apply Zc_ne_zero_of_zeta_ne
    by_cases h1 : 1 ≤ a
    · exact riemannZeta_ne_zero_of_one_le_re (by rw [hzre]; exact h1)
    · intro hζ0
      have hb' : |((a : ℂ) + (b : ℂ) * I).im| ≤ M := by rw [hzim, abs_le]; exact ⟨hb1, hb2⟩
      have hstr := hstrip hζ0 hb'
      rw [hzre] at hstr
      linarith
  -- logDeriv Zc continuous on K
  have hLD_cont : ContinuousOn (logDeriv Zc) K := by
    have hderiv_cont : Continuous (deriv Zc) := continuousOn_univ.mp
      (Zc_differentiable.differentiableOn.analyticOnNhd isOpen_univ).deriv.continuousOn
    have h : ContinuousOn (fun z => deriv Zc z / Zc z) K :=
      hderiv_cont.continuousOn.div Zc_differentiable.continuous.continuousOn hZne
    exact h
  obtain ⟨C₀, hC₀⟩ := hKcompact.exists_bound_of_continuousOn hLD_cont
  refine ⟨δ₀, C₀, hδ₀pos, ?_⟩
  intro z hre1 hre2 him
  refine hC₀ z ⟨(z.re, z.im), ?_, Complex.re_add_im z⟩
  rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
  exact ⟨⟨hre1, hre2⟩, (abs_le.mp him).1, (abs_le.mp him).2⟩

end EdgeSupport

/-! ## EDGE (STONE 1) — the disc-core high-height price on the left spine

The high-height half of `shifted_edge_price`: for the shifted rectangle's LEFT spine point
`z = σ₀ + iγ` (`σ₀ = 1 − (c_vk/2)/D₃(5T+1)`) at a height `γ ≤ 5T` above the strip threshold,
the entire factor `logDeriv Zc` is priced at the honest `D₄(5T+1)`-grade
`(log(5T+1))^{3/4}(loglog(5T+1))⁴`.  The tuned mirror of `zeta_near_bound_core`
(`ZetaPowLower.lean:449`) at the LEFT point: same sphere discharge (`Zc_ratio_sphere_bound`),
same `Pinv/W/Mζ` region numerics, but the point sits LEFT of the 1-line, so `hZcs`/`hdist` come
from the shifted-rectangle margin (`rect_zero_free_margin`, supplied as `hmargin`) and the
centering `hsc` runs the honest `(17/35)` constant-chase.  Amendment L11-W′: the disc at height
`γ ≤ 5T` reaches zeros up to `|ρ.im| ≤ 5T + 9/14 ≤ 5T+1`, so the margin is fed at height `5T+1`
(the caller invokes `rect_zero_free_margin` at `T + 1/5`); the honest min-distance is
`(c_vk/2)/D₃(5T+1)`.  `hsc_thr` is the T-threshold of the constant-chase
(`9000·c_vk ≤ loglog(5T+1)`). -/

section ShiftedEdge
open Complex Salt.SW Salt.Vk Metric Set

set_option maxHeartbeats 12800000 in
-- The tuned disc-core mirror threads the sphere discharge, the region `Pinv/W/Mζ` numerics, the
-- LEFT-point constant-chase and the closing `D₄` assembly through one declaration; the default
-- heartbeat budget dies in the closing arithmetic (the template `zeta_near_bound_core` needs 12.8M).
/-- **EDGE disc-core high half** (STONE 1).  At the left spine point `s = σ₀ + iγ`, `σ₀ =
1 − (c_vk/2)/D₃(5T+1)`, height `γ ≤ 5T` above the astronomically-lazy strip threshold, the entire
factor `logDeriv Zc` is `D₄(5T+1)`-grade: `‖logDeriv Zc s‖ ≤ (10⁸ + 200/c_vk)·(log(5T+1))^{3/4}
(loglog(5T+1))⁴`.  Rides `near_norm_logDeriv_Zc_le` on the pow-region disc (scale
`Θ = vkTheta(3γ)`); the sphere discharge / region numerics mirror `zeta_near_bound_core`; the
`hsc`/`hZcs`/`hdist`
adapt to the LEFT point via the supplied margin `hmargin`. -/
lemma shifted_edge_disc_core {K t₀K c_vk : ℝ} (hK : 1 ≤ K) (ht₀K : 3 ≤ t₀K)
    (hg : ∀ σ t : ℝ, t₀K ≤ t → 1 - vkTheta t ≤ σ → σ ≤ 3 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K * Real.log t)
    (hc_vk : 0 < c_vk)
    {T γ : ℝ}
    (hγ : Real.exp (Real.exp (8 * Real.log (20000 * K) + 1100)) + t₀K + 3 ≤ γ)
    (hγT : γ ≤ 5 * T)
    (hsc_thr : 9000 * c_vk ≤ Real.log (Real.log (5 * T + 1)))
    (hmargin : ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ))) :
    ‖logDeriv Zc ((1 - (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)) : ℝ) + (γ : ℂ) * Complex.I)‖
      ≤ (10 ^ 8 + 200 / c_vk) * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) := by
  -- the 5T+1 denominators (fold the goal)
  set LT : ℝ := Real.log (5 * T + 1) with hLTdef
  set ℓT : ℝ := Real.log LT with hℓTdef
  set D3T : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) with hD3Tdef
  set w : ℝ := (c_vk / 2) / D3T with hwdef
  set s : ℂ := ((1 - w : ℝ) : ℂ) + (γ : ℂ) * Complex.I with hsdef
  -- === template height thresholds (γ-only, verbatim + inlined `pow_height_facts`) ===
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  set A : ℝ := 8 * Real.log (20000 * K) + 1100 with hAdef
  have hA1100 : 1100 ≤ A := by
    have : (0:ℝ) ≤ Real.log (20000 * K) := Real.log_nonneg (by nlinarith [hK])
    rw [hAdef]; linarith
  have hEpos : 0 < Real.exp (Real.exp A) := Real.exp_pos _
  have hγim : Real.exp (Real.exp A) + t₀K + 3 ≤ γ := hγ
  have hσimE : Real.exp (Real.exp A) ≤ γ := by linarith [ht₀K, hγim]
  have hγpos : 0 < γ := lt_of_lt_of_le hEpos hσimE
  have hγ2 : (2:ℝ) ≤ γ := by linarith [hEpos, ht₀K, hγim]
  have hexpA1 : 1 < Real.exp A := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith [hA1100])
  have hEe : Real.exp 1 < Real.exp (Real.exp A) := Real.exp_lt_exp.mpr hexpA1
  have hγe : Real.exp 1 < γ - 1 := by linarith [hEe, hγim, ht₀K, hEpos]
  have hγt₀ : t₀K ≤ γ - 1 := by linarith [hEpos, hγim]
  have hfactsγ : 3 ≤ Real.log γ ∧ A ≤ Real.log (Real.log γ) := by
    have hlogE : Real.log (Real.exp (Real.exp A)) = Real.exp A := Real.log_exp _
    have hlogx : Real.exp A ≤ Real.log γ := by rw [← hlogE]; exact Real.log_le_log hEpos hσimE
    have hexp2 : (3:ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
    have hexpA3 : (3:ℝ) ≤ Real.exp A := le_trans hexp2 (Real.exp_le_exp.mpr (by linarith [hA1100]))
    refine ⟨le_trans hexpA3 hlogx, ?_⟩
    calc A = Real.log (Real.exp A) := (Real.log_exp A).symm
      _ ≤ Real.log (Real.log γ) := Real.log_le_log (Real.exp_pos A) hlogx
  -- abbreviations
  set Lg : ℝ := Real.log γ with hLdef
  set ℓ : ℝ := Real.log Lg with hℓdef
  have hL3 : (3:ℝ) ≤ Lg := hfactsγ.1
  have hℓA : A ≤ ℓ := hfactsγ.2
  have hℓ1100 : (1100:ℝ) ≤ ℓ := le_trans hA1100 hℓA
  have hL0 : 0 < Lg := by linarith [hL3]
  have hℓ0 : 0 < ℓ := by linarith [hℓ1100]
  -- log 3γ facts
  set L3 : ℝ := Real.log (3 * γ) with hL3def
  have hlog3le2 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)]
  have hL3eq : L3 = Real.log 3 + Lg := by rw [hL3def, Real.log_mul (by norm_num) hγpos.ne']
  have hL3lb : Lg ≤ L3 := by rw [hL3eq]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]
  have hL3ub : L3 ≤ 2 * Lg := by rw [hL3eq]; linarith [hlog3le2, hL3]
  have hL30 : 0 < L3 := by linarith [hL3lb, hL0]
  set ℓ3 : ℝ := Real.log L3 with hℓ3def
  have hℓ3lb : ℓ ≤ ℓ3 := by rw [hℓ3def, hℓdef]; exact Real.log_le_log hL0 hL3lb
  have hlog2le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
  have hℓ3ub : ℓ3 ≤ 2 * ℓ := by
    rw [hℓ3def]
    calc Real.log L3 ≤ Real.log (2 * Lg) := Real.log_le_log hL30 hL3ub
      _ = Real.log 2 + ℓ := by rw [Real.log_mul (by norm_num) hL0.ne', ← hℓdef]
      _ ≤ 2 * ℓ := by linarith [hlog2le1, hℓ1100]
  have hℓ30 : 0 < ℓ3 := by linarith [hℓ3lb, hℓ0]
  have hℓ31100 : (1100:ℝ) ≤ ℓ3 := by linarith [hℓ3lb, hℓ1100]
  -- region parameters (verbatim)
  set Θ : ℝ := vkTheta (3 * γ) with hΘdef
  set Pinv : ℝ := 1000 * L3 ^ ((3:ℝ)/4) * ℓ3 ^ (2:ℕ) with hPinvdef
  have hL34pos : 0 < L3 ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos hL30 _
  have hPinvpos : 0 < Pinv := by rw [hPinvdef]; positivity
  have hΘval : Θ = 1 / 1000 / (L3 ^ ((3:ℝ)/4) * ℓ3 ^ (2:ℕ)) := by
    rw [hΘdef, vkTheta, ← hL3def, ← hℓ3def]
  have hΘPinv : Θ = 1 / Pinv := by
    rw [eq_div_iff (ne_of_gt hPinvpos), hΘval, hPinvdef]
    field_simp [ne_of_gt hL34pos, ne_of_gt hℓ30]
  have hΘ0 : 0 < Θ := by rw [hΘPinv]; positivity
  set Mζ : ℝ := K * L3 with hMζdef
  have hMζpos : 0 < Mζ := by rw [hMζdef]; positivity
  have hMζ1 : (1:ℝ) ≤ Mζ := by rw [hMζdef]; nlinarith [hK, hL3lb, hL3]
  have hPinv2 : (2:ℝ) ≤ Pinv := by
    rw [hPinvdef]
    have h1 : (1:ℝ) ≤ L3 ^ ((3:ℝ)/4) := Real.one_le_rpow (by linarith [hL3lb, hL3]) (by norm_num)
    have h2 : (1:ℝ) ≤ ℓ3 ^ (2:ℕ) := one_le_pow₀ (by linarith [hℓ31100])
    nlinarith [h1, h2]
  have hΘ12 : Θ ≤ 1 / 2 := by
    rw [hΘPinv]; rw [div_le_div_iff₀ hPinvpos (by norm_num)]; linarith [hPinv2]
  have hgrowth : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → γ - 1 ≤ z.im → z.im ≤ 3 * γ →
      ‖riemannZeta z‖ ≤ Mζ := by
    intro z h1 h2 h3 h4
    rw [hΘdef] at h1; rw [hMζdef]
    exact pow_uniform_growth hK ht₀K hg hγe hγt₀ z h1 h2 h3 h4
  set W : ℝ := Real.log (20 * Pinv * Mζ) with hWdef
  have hWeq : W = Real.log (20000 * K) + (7 / 4) * ℓ3 + 2 * Real.log ℓ3 := by
    have hPinvne : Pinv ≠ 0 := ne_of_gt hPinvpos
    have hL3ne : L3 ≠ 0 := ne_of_gt hL30
    have hℓ3ne : ℓ3 ≠ 0 := ne_of_gt hℓ30
    have h20000 : Real.log (20000 * K) = Real.log 20 + Real.log 1000 + Real.log K := by
      rw [show (20000:ℝ) * K = 20 * 1000 * K by ring, Real.log_mul (by norm_num) hKpos.ne',
        Real.log_mul (by norm_num) (by norm_num)]
    rw [hWdef, Real.log_mul (by positivity) (ne_of_gt hMζpos),
      Real.log_mul (by norm_num) hPinvne, hMζdef, Real.log_mul hKpos.ne' hL3ne,
      hPinvdef, Real.log_mul (by positivity) (pow_ne_zero 2 hℓ3ne),
      Real.log_mul (by norm_num) (ne_of_gt hL34pos), Real.log_rpow hL30, Real.log_pow,
      ← hℓ3def, h20000]
    push_cast; ring
  have hlog20K : Real.log (20000 * K) ≤ ℓ / 8 := by rw [hAdef] at hℓA; linarith
  have hlogℓ3le : Real.log ℓ3 ≤ ℓ3 := by linarith [Real.log_le_sub_one_of_pos hℓ30]
  have hWub : W ≤ 8 * ℓ := by
    rw [hWeq]; linarith [hlog20K, hℓ3ub, hlogℓ3le]
  have hW0 : 0 ≤ W := by
    rw [hWdef]; apply Real.log_nonneg
    nlinarith [hPinv2, hMζ1, hMζpos, hPinvpos]
  have hγ1 : (1:ℝ) ≤ |γ| := by rw [abs_of_nonneg hγpos.le]; linarith [hγ2]
  -- sphere discharge (verbatim, height γ)
  have hsph : ∀ R : ℝ, 0 ≤ R → R ≤ 3 / 2 * Θ →
      ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) R,
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 5 * Mζ / Θ := by
    intro R hR0 hR z hz
    have hzc : ‖z - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ = R := by
      rw [← dist_eq_norm, ← mem_sphere]; exact hz
    have hcre : (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I).re = 1 + Θ / 2 := by simp
    have hcim : (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I).im = γ := by simp
    have hreb : |z.re - (1 + Θ / 2)| ≤ R := by
      have h := Complex.abs_re_le_norm (z - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I))
      rw [Complex.sub_re, hcre, hzc] at h; exact h
    have himb : |z.im - γ| ≤ R := by
      have h := Complex.abs_im_le_norm (z - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I))
      rw [Complex.sub_im, hcim, hzc] at h; exact h
    have hre1 : 1 - Θ ≤ z.re := by have := (abs_le.mp hreb).1; nlinarith [hR, hΘ12]
    have hre2 : z.re ≤ 2 := by have := (abs_le.mp hreb).2; nlinarith [hR, hΘ12]
    have him1 : γ - 1 ≤ z.im := by have := (abs_le.mp himb).1; nlinarith [hR, hΘ12]
    have him2 : z.im ≤ 3 * γ := by have := (abs_le.mp himb).2; nlinarith [hR, hΘ12, hγ2]
    exact Zc_ratio_sphere_bound hΘ0 hΘ12 hγ1 hMζ1 hR0 hR hz (hgrowth z hre1 hre2 him1 him2)
  have hR74 : (7:ℝ) / 4 * (6 * Θ / 7) ≤ 3 / 2 * Θ := by nlinarith [hΘ0]
  have hR32 : (3:ℝ) / 2 * (6 * Θ / 7) ≤ 3 / 2 * Θ := by nlinarith [hΘ0]
  have hsphere74 := hsph (7 / 4 * (6 * Θ / 7)) (by positivity) hR74
  have hsphere32 := hsph (3 / 2 * (6 * Θ / 7)) (by positivity) hR32
  have hM₀1 : (1:ℝ) ≤ 5 * Mζ / Θ := by rw [le_div_iff₀ hΘ0]; nlinarith [hMζ1, hΘ12, hΘ0]
  -- === the 5T+1 denominators: positivity + monotonicity ===
  have hγ5T1 : γ ≤ 5 * T + 1 := by linarith [hγT]
  have hLTpos : 0 < LT := by rw [hLTdef]; exact Real.log_pos (by linarith [hγ2, hγT])
  have hLgLT : Lg ≤ LT := by rw [hLdef, hLTdef]; exact Real.log_le_log hγpos hγ5T1
  have hℓTpos : 0 < ℓT := by rw [hℓTdef]; exact Real.log_pos (by linarith [hL3, hLgLT])
  have hℓℓT : ℓ ≤ ℓT := by rw [hℓdef, hℓTdef]; exact Real.log_le_log hL0 hLgLT
  have hℓT1100 : (1100:ℝ) ≤ ℓT := le_trans hℓ1100 hℓℓT
  have hℓT1 : (1:ℝ) ≤ ℓT := by linarith [hℓT1100]
  have hD3Tpos : 0 < D3T := by rw [hD3Tdef]; positivity
  have hw0 : 0 < w := by rw [hwdef]; exact div_pos (by linarith [hc_vk]) hD3Tpos
  have hsre : s.re = 1 - w := by rw [hsdef]; simp
  have hsim : s.im = γ := by rw [hsdef]; simp
  -- L3 ≤ 2 LT, ℓ3 ≤ 2 ℓT (the constant-chase monotonicity)
  have hTpos : 0 < T := by linarith [hγpos, hγT]
  have hL3_2LT : L3 ≤ 2 * LT := by
    have h1 : (3:ℝ) * γ ≤ (5 * T + 1) ^ 2 := by nlinarith [hγT, hTpos, sq_nonneg (5 * T - 1)]
    have h2 : Real.log (3 * γ) ≤ Real.log ((5 * T + 1) ^ 2) := Real.log_le_log (by positivity) h1
    rw [hL3def]
    calc Real.log (3 * γ) ≤ Real.log ((5 * T + 1) ^ 2) := h2
      _ = 2 * LT := by rw [Real.log_pow, ← hLTdef]; push_cast; ring
  have hℓ3_2ℓT : ℓ3 ≤ 2 * ℓT := by
    rw [hℓ3def]
    calc Real.log L3 ≤ Real.log (2 * LT) := Real.log_le_log hL30 hL3_2LT
      _ = Real.log 2 + ℓT := by rw [Real.log_mul (by norm_num) hLTpos.ne', ← hℓTdef]
      _ ≤ 2 * ℓT := by linarith [hlog2le1, hℓT1]
  -- Pinv ≤ 8000 · LT^{3/4} · ℓT²
  have hPinv5 : Pinv ≤ 8000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (2:ℕ)) := by
    have hL34 : L3 ^ ((3:ℝ)/4) ≤ 2 * LT ^ ((3:ℝ)/4) := by
      calc L3 ^ ((3:ℝ)/4) ≤ (2 * LT) ^ ((3:ℝ)/4) := Real.rpow_le_rpow hL30.le hL3_2LT (by norm_num)
        _ = 2 ^ ((3:ℝ)/4) * LT ^ ((3:ℝ)/4) := Real.mul_rpow (by norm_num) hLTpos.le
        _ ≤ 2 * LT ^ ((3:ℝ)/4) := by
            have h2 : (2:ℝ) ^ ((3:ℝ)/4) ≤ 2 := by
              calc (2:ℝ) ^ ((3:ℝ)/4) ≤ (2:ℝ) ^ (1:ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one 2
            nlinarith [h2, Real.rpow_nonneg hLTpos.le ((3:ℝ)/4)]
    have hℓ3sq : ℓ3 ^ (2:ℕ) ≤ 4 * ℓT ^ (2:ℕ) := by
      calc ℓ3 ^ (2:ℕ) ≤ (2 * ℓT) ^ (2:ℕ) := pow_le_pow_left₀ hℓ30.le hℓ3_2ℓT 2
        _ = 4 * ℓT ^ (2:ℕ) := by ring
    calc Pinv = 1000 * (L3 ^ ((3:ℝ)/4) * ℓ3 ^ (2:ℕ)) := by rw [hPinvdef]; ring
      _ ≤ 1000 * ((2 * LT ^ ((3:ℝ)/4)) * (4 * ℓT ^ (2:ℕ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hL34 hℓ3sq (by positivity) (by positivity)
      _ = 8000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (2:ℕ)) := by ring
  -- === centering, zero-freeness, min-distance (the LEFT-point adaptations) ===
  have hsc : ‖s - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 23 / 20 * (6 * Θ / 7) := by
    have hsub : s - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
        = (((1 - w) - (1 + Θ / 2) : ℝ) : ℂ) := by
      rw [hsdef]; push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs]
    have hnp : (1 - w) - (1 + Θ / 2) ≤ 0 := by nlinarith [hw0, hΘ0]
    rw [abs_of_nonpos hnp]
    -- goal: -(1 - w - (1 + Θ/2)) ≤ 23/20*(6Θ/7), i.e. w + Θ/2 ≤ 69Θ/70; use w ≤ 17Θ/35
    have hwPinv : w * Pinv ≤ 17 / 35 := by
      rw [hwdef, div_mul_eq_mul_div, div_le_iff₀ hD3Tpos, hD3Tdef]
      have hcc : (4000:ℝ) * c_vk ≤ 17 / 35 * ℓT := by nlinarith [hsc_thr, hc_vk]
      have hAle : c_vk / 2 * Pinv ≤ c_vk / 2 * (8000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (2:ℕ))) :=
        mul_le_mul_of_nonneg_left hPinv5 (by linarith [hc_vk])
      nlinarith [hAle, hcc, Real.rpow_nonneg hLTpos.le ((3:ℝ)/4), pow_nonneg hℓTpos.le 2,
        mul_nonneg (Real.rpow_nonneg hLTpos.le ((3:ℝ)/4)) (pow_nonneg hℓTpos.le 2), hℓTpos]
    have hsc_key : w ≤ 17 * Θ / 35 := by
      rw [hΘPinv, show (17:ℝ) * (1 / Pinv) / 35 = 17 / (35 * Pinv) by field_simp]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hwPinv, hPinvpos]
    nlinarith [hsc_key, hΘ0]
  have hs1 : s ≠ 1 := by
    rw [hsdef]; intro h
    have := congrArg Complex.im h; simp at this; linarith [hγ2, this]
  have hζs : riemannZeta s ≠ 0 := by
    intro hζ0
    have him : |s.im| ≤ 5 * T + 1 := by
      rw [hsim, abs_of_nonneg hγpos.le]; linarith [hγT]
    have hmr := hmargin s hζ0 him
    rw [hsre] at hmr
    have hlt : w < c_vk / D3T := by
      rw [hwdef, div_lt_div_iff₀ hD3Tpos hD3Tpos]; nlinarith [hc_vk, hD3Tpos]
    linarith [hmr, hlt]
  have hZcs : Zc s ≠ 0 := Zc_ne_zero_of_zeta_ne hζs
  have hdist : ∀ ρ : ℂ, Zc ρ = 0 →
      ρ ∈ ball (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (3 / 2 * (6 * Θ / 7)) →
        w ≤ ‖s - ρ‖ := by
    intro ρ hZcρ hρball
    rw [mem_ball, dist_eq_norm] at hρball
    have hcim : (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I).im = γ := by simp
    have himb : |ρ.im - γ| ≤ 3 / 2 * (6 * Θ / 7) := by
      have h := Complex.abs_im_le_norm (ρ - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I))
      rw [Complex.sub_im, hcim] at h; linarith [h, hρball]
    have hrad : 3 / 2 * (6 * Θ / 7) ≤ 9 / 14 := by nlinarith [hΘ12, hΘ0]
    have hρim_lb : γ - 9 / 14 ≤ ρ.im := by have := (abs_le.mp himb).1; linarith [hrad]
    have hρim_ub : ρ.im ≤ γ + 9 / 14 := by have := (abs_le.mp himb).2; linarith [hrad]
    have hρimpos : 0 < ρ.im := by linarith [hρim_lb, hγ2]
    have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hρimpos; simp at hρimpos
    have hζρ : riemannZeta ρ = 0 := by
      rw [Zc_eq_of_ne hρ1] at hZcρ
      exact (mul_eq_zero.mp hZcρ).resolve_left (sub_ne_zero.mpr hρ1)
    have hρimabs : |ρ.im| ≤ 5 * T + 1 := by
      rw [abs_of_nonneg hρimpos.le]; linarith [hρim_ub, hγT]
    have hmr := hmargin ρ hζρ hρimabs
    have hdist_re : w ≤ s.re - ρ.re := by
      rw [hsre]
      have hww : w = c_vk / D3T - (c_vk / 2) / D3T := by rw [hwdef]; field_simp; ring
      linarith [hmr, hww]
    have h := Complex.abs_re_le_norm (s - ρ)
    rw [Complex.sub_re] at h
    linarith [h, le_abs_self (s.re - ρ.re), hdist_re]
  -- === run the near-region lemma + the rewrites (verbatim) ===
  have hnear := near_norm_logDeriv_Zc_le hΘ0 hM₀1 hw0 hsc hZcs hsphere74 hsphere32 hdist
  have h140 : (120:ℝ) / (6 * Θ / 7) = 140 * Pinv := by
    rw [hΘPinv]; field_simp [ne_of_gt hPinvpos]; ring
  have h4M : (4:ℝ) * (5 * Mζ / Θ) = 20 * Pinv * Mζ := by
    rw [hΘPinv]; field_simp [ne_of_gt hPinvpos]; ring
  have hlog4M : Real.log (4 * (5 * Mζ / Θ)) = W := by rw [h4M]
  rw [h140, hlog4M] at hnear
  -- hnear : ‖logDeriv Zc s‖ ≤ 140 * Pinv * W + W / Real.log (7/6) / w
  -- === the final D₄(5T+1) numeric ===
  have hD4nn : (0:ℝ) ≤ LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ) :=
    mul_nonneg (Real.rpow_nonneg hLTpos.le _) (pow_nonneg hℓTpos.le _)
  have hℓT34 : LT ^ ((3:ℝ)/4) * ℓT ^ (3:ℕ) ≤ LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ) := by
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hLTpos.le _)
    exact pow_le_pow_right₀ hℓT1 (by norm_num)
  have hW8ℓT : W ≤ 8 * ℓT := le_trans hWub (by linarith [hℓℓT])
  have hterm1 : 140 * Pinv * W ≤ 10 ^ 8 * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := by
    have hPW : Pinv * W ≤ 64000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (3:ℕ)) := by
      calc Pinv * W ≤ (8000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (2:ℕ))) * (8 * ℓT) :=
            mul_le_mul hPinv5 hW8ℓT hW0 (by positivity)
        _ = 64000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (3:ℕ)) := by ring
    calc 140 * Pinv * W = 140 * (Pinv * W) := by ring
      _ ≤ 140 * (64000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (3:ℕ))) :=
          mul_le_mul_of_nonneg_left hPW (by norm_num)
      _ = 8960000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (3:ℕ)) := by ring
      _ ≤ 8960000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := mul_le_mul_of_nonneg_left hℓT34 (by norm_num)
      _ ≤ 10 ^ 8 * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := by nlinarith [hD4nn]
  have h76pos : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have h76ge : (1:ℝ) / 7 ≤ Real.log (7 / 6) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 6 / 7 by norm_num)
    rw [show (6:ℝ) / 7 = (7 / 6)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hWlog : W / Real.log (7 / 6) ≤ 56 * ℓT := by
    rw [div_le_iff₀ h76pos]
    nlinarith [hW8ℓT, mul_nonneg (by positivity : (0:ℝ) ≤ 56 * ℓT) (sub_nonneg.mpr h76ge), hℓTpos]
  have h1overw : (1:ℝ) / w = 2 * D3T / c_vk := by
    rw [hwdef]; field_simp
  have hterm2 : W / Real.log (7 / 6) / w ≤ 200 / c_vk * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := by
    rw [div_eq_mul_one_div (W / Real.log (7 / 6)) w, h1overw]
    have hstep : W / Real.log (7 / 6) * (2 * D3T / c_vk) ≤ 56 * ℓT * (2 * D3T / c_vk) :=
      mul_le_mul_of_nonneg_right hWlog (by positivity)
    refine le_trans hstep ?_
    rw [hD3Tdef]
    have hXc : (0:ℝ) ≤ (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) / c_vk := div_nonneg hD4nn hc_vk.le
    calc 56 * ℓT * (2 * (LT ^ ((3:ℝ)/4) * ℓT ^ (3:ℕ)) / c_vk)
        = 112 * ((LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) / c_vk) := by ring
      _ ≤ 200 * ((LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) / c_vk) :=
          mul_le_mul_of_nonneg_right (by norm_num) hXc
      _ = 200 / c_vk * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := by ring
  calc ‖logDeriv Zc s‖ ≤ 140 * Pinv * W + W / Real.log (7 / 6) / w := hnear
    _ ≤ 10 ^ 8 * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) + 200 / c_vk * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := by
        linarith [hterm1, hterm2]
    _ = (10 ^ 8 + 200 / c_vk) * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := by ring

/-- `Zc` commutes with complex conjugation (`Zc = (·−1)ζ` has real Taylor coefficients;
`riemannZeta_conj` off the pole, `Zc 1 = 1` real at it). -/
lemma Zc_conj (w : ℂ) : Zc ((starRingEnd ℂ) w) = (starRingEnd ℂ) (Zc w) := by
  rcases eq_or_ne w 1 with rfl | hw
  · simp [Zc_one]
  · have hcw : (starRingEnd ℂ) w ≠ 1 := fun h => hw (by
      have := congrArg (starRingEnd ℂ) h; rwa [Complex.conj_conj, map_one] at this)
    rw [Zc_eq_of_ne hcw, Zc_eq_of_ne hw, riemannZeta_conj hw, map_mul, map_sub, map_one]

/-- The `logDeriv Zc` norm is conjugation-invariant: `‖logDeriv Zc (conj w)‖ = ‖logDeriv Zc w‖`.
Rides `Zc_conj` + `HasDerivAt.conj_conj` (so `deriv Zc (conj w) = conj (deriv Zc w)`). -/
lemma logDeriv_Zc_norm_conj (w : ℂ) :
    ‖logDeriv Zc ((starRingEnd ℂ) w)‖ = ‖logDeriv Zc w‖ := by
  have hderiv : deriv Zc ((starRingEnd ℂ) w) = (starRingEnd ℂ) (deriv Zc w) := by
    have hw' : HasDerivAt Zc (deriv Zc w) w := (Zc_differentiable w).hasDerivAt
    have href := hw'.conj_conj
    have hEq : (⇑(starRingEnd ℂ) ∘ Zc ∘ ⇑(starRingEnd ℂ)) = Zc := by
      funext z; simp only [Function.comp_apply]; rw [Zc_conj, Complex.conj_conj]
    rw [hEq] at href
    exact href.deriv
  rw [logDeriv_apply, logDeriv_apply, hderiv, Zc_conj, ← map_div₀, Complex.norm_conj]

set_option maxHeartbeats 800000 in
-- The glue case-splits on `|γ|` (disc-core high / conjugation / compact moderate) after several
-- exp/log threshold discharges (the `δ₀`, `hsc` and margin thresholds); the default budget is tight.
/-- **EDGE — the full shifted-edge price** (STONE 1, glued).  Packages the disc-core high half
(`shifted_edge_disc_core`) with the moderate-height compact bound (`logDeriv_Zc_compact_bound`)
and the sign symmetry (`logDeriv_Zc_norm_conj`): there are `c_vk > 0`, `CE > 0`, `T₀ ≥ 3` such that
for `T ≥ T₀`, the shifted rectangle is ζ-zero-free with margin `c_vk/D₃(5T+1)` (the first clause,
the `rect_zero_free_margin` at height `5T+1` that RES/ASM reuse), and `logDeriv Zc` on the entire
LEFT spine `s = σ₀ + iγ`, `σ₀ = 1 − (c_vk/2)/D₃(5T+1)`, `|γ| ≤ 5T`, is `D₄(5T+1)`-graded:
`‖logDeriv Zc s‖ ≤ CE·(log(5T+1))^{3/4}(loglog(5T+1))⁴`. -/
theorem shifted_edge_price :
    ∃ (c_vk CE T₀ : ℝ), 0 < c_vk ∧ 0 < CE ∧ 3 ≤ T₀ ∧
      (∀ (T : ℝ), T₀ ≤ T → ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
          ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ))) ∧
      ∀ (T γ : ℝ), T₀ ≤ T → |γ| ≤ 5 * T →
        ‖logDeriv Zc ((1 - (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)) : ℝ) + (γ : ℂ) * Complex.I)‖
          ≤ CE * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) := by
  obtain ⟨c_vk, T₁, hc_vk0, hT₁, hmarg⟩ := rect_zero_free_margin
  obtain ⟨K, t₀K, hK, ht₀K, hg⟩ := Salt.Vk.zeta_growth_pow
  set H : ℝ := Real.exp (Real.exp (8 * Real.log (20000 * K) + 1100)) + t₀K + 3 with hHdef
  have hH0 : 0 ≤ H := by
    rw [hHdef]; have := Real.exp_pos (Real.exp (8 * Real.log (20000 * K) + 1100)); linarith [ht₀K]
  obtain ⟨δ₀, C₀, hδ₀0, hcpt⟩ := logDeriv_Zc_compact_bound (M := H) (c := 1) hH0 (le_refl 1)
  set Cbig : ℝ := 9000 * c_vk + c_vk / (2 * δ₀) + 1 with hCbigdef
  set CE : ℝ := (10 ^ 8 + 200 / c_vk) + (|C₀| + 1) with hCEdef
  set T₀ : ℝ := max (max T₁ 3) (Real.exp (Real.exp Cbig)) with hT₀def
  have hCE0 : 0 < CE := by rw [hCEdef]; positivity
  refine ⟨c_vk, CE, T₀, hc_vk0, hCE0, le_trans (le_max_right _ _) (le_max_left _ _), ?_, ?_⟩
  · -- the margin clause (used by RES/ASM): rect_zero_free_margin at T + 1/5 (so 5(T+1/5) = 5T+1)
    intro T hT ρ hρ0 hρim
    have hTT₁ : T₁ ≤ T + 1 / 5 := by
      have := le_trans (le_trans (le_max_left T₁ 3) (le_max_left _ _)) hT; linarith
    have h := (hmarg (T + 1 / 5) hTT₁).2 ρ hρ0
    rw [show 5 * (T + 1 / 5) = 5 * T + 1 by ring] at h
    exact h hρim
  · -- the edge bound
    intro T γ hT hγ5T
    have hTT₁ : T₁ ≤ T + 1 / 5 := by
      have := le_trans (le_trans (le_max_left T₁ 3) (le_max_left _ _)) hT; linarith
    have hTexp : Real.exp (Real.exp Cbig) ≤ T := le_trans (le_max_right _ _) hT
    have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hTexp
    have h5T1exp : Real.exp (Real.exp Cbig) ≤ 5 * T + 1 := by linarith [hTexp, hTpos]
    have ha5 : 0 < Real.log (5 * T + 1) :=
      lt_of_lt_of_le (Real.exp_pos _) (by
        rw [← Real.log_exp (Real.exp Cbig)]; exact Real.log_le_log (Real.exp_pos _) h5T1exp)
    have hlog5T1 : Real.exp Cbig ≤ Real.log (5 * T + 1) := by
      rw [← Real.log_exp (Real.exp Cbig)]; exact Real.log_le_log (Real.exp_pos _) h5T1exp
    have hloglog : Cbig ≤ Real.log (Real.log (5 * T + 1)) := by
      rw [← Real.log_exp Cbig]; exact Real.log_le_log (Real.exp_pos _) hlog5T1
    -- the reused margin fact at 5T+1
    have hmargT : ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)) := by
      intro ρ hρ0 hρim
      have h := (hmarg (T + 1 / 5) hTT₁).2 ρ hρ0
      rw [show 5 * (T + 1 / 5) = 5 * T + 1 by ring] at h
      exact h hρim
    -- the hsc threshold for the disc
    have hsc_thr : 9000 * c_vk ≤ Real.log (Real.log (5 * T + 1)) := by
      have hnn : (0:ℝ) ≤ c_vk / (2 * δ₀) := by positivity
      have hle : 9000 * c_vk ≤ Cbig := by rw [hCbigdef]; linarith [hnn]
      linarith [hle, hloglog]
    -- D₃(5T+1), D₄(5T+1) facts
    set LT : ℝ := Real.log (5 * T + 1) with hLTdef
    set ℓT : ℝ := Real.log LT with hℓTdef
    have hℓTge : (1:ℝ) ≤ ℓT := by
      have hnn : (0:ℝ) ≤ 9000 * c_vk + c_vk / (2 * δ₀) := by positivity
      have hle : (1:ℝ) ≤ Cbig := by rw [hCbigdef]; linarith [hnn]
      linarith [hle, hloglog]
    have hℓTpos : 0 < ℓT := by linarith [hℓTge]
    have hLTge : Real.exp 1 ≤ LT := by
      have h1 : Real.exp 1 ≤ Real.exp ℓT := Real.exp_le_exp.mpr hℓTge
      rwa [hℓTdef, Real.exp_log ha5] at h1
    have hLT1 : (1:ℝ) ≤ LT := le_trans (by linarith [Real.add_one_le_exp (1:ℝ)]) hLTge
    have hLTpos : 0 < LT := by linarith [hLT1]
    set D3T : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) with hD3Tdef
    have hLT34ge : (1:ℝ) ≤ LT ^ ((3 : ℝ) / 4) := Real.one_le_rpow hLT1 (by norm_num)
    have hℓT4ge : (1:ℝ) ≤ ℓT ^ (4 : ℕ) := one_le_pow₀ hℓTge
    have hD3Tpos : 0 < D3T := by rw [hD3Tdef]; positivity
    have hD4nn : (0:ℝ) ≤ LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ) :=
      mul_nonneg (Real.rpow_nonneg hLTpos.le _) (pow_nonneg hℓTpos.le _)
    have hD41 : (1:ℝ) ≤ LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ) := by nlinarith [hLT34ge, hℓT4ge]
    -- the δ₀ condition: (c_vk/2)/D₃(5T+1) ≤ δ₀
    have hδcond : (c_vk / 2) / D3T ≤ δ₀ := by
      have hbase : c_vk / (2 * δ₀) ≤ ℓT := by
        have hnn : (0:ℝ) ≤ 9000 * c_vk := by positivity
        have hle : c_vk / (2 * δ₀) ≤ Cbig := by rw [hCbigdef]; linarith [hnn]
        linarith [hle, hloglog]
      have hcube3 : ℓT ≤ ℓT ^ (3 : ℕ) := by
        have h2 : (1:ℝ) ≤ ℓT ^ (2:ℕ) := one_le_pow₀ hℓTge
        nlinarith [mul_le_mul_of_nonneg_left h2 hℓTpos.le]
      have hD3ge : c_vk / (2 * δ₀) ≤ D3T := by
        rw [hD3Tdef]
        calc c_vk / (2 * δ₀) ≤ ℓT ^ (3 : ℕ) := le_trans hbase hcube3
          _ = 1 * ℓT ^ (3 : ℕ) := (one_mul _).symm
          _ ≤ LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) :=
              mul_le_mul_of_nonneg_right hLT34ge (pow_nonneg hℓTpos.le _)
      have hδpos : 0 < 2 * δ₀ := by linarith [hδ₀0]
      rw [div_le_iff₀ hδpos] at hD3ge
      rw [div_le_iff₀ hD3Tpos]
      nlinarith [hD3ge, hδ₀0, hD3Tpos]
    -- case split on |γ| vs H
    by_cases hcase : H ≤ |γ|
    · -- high height: disc-core (+ conjugation for γ < 0)
      by_cases hsign : (0:ℝ) ≤ γ
      · have hγH : H ≤ γ := by rwa [abs_of_nonneg hsign] at hcase
        have hγT5 : γ ≤ 5 * T := by rwa [abs_of_nonneg hsign] at hγ5T
        have hbound := shifted_edge_disc_core hK ht₀K hg hc_vk0 (by rw [hHdef] at hγH; exact hγH)
          hγT5 hsc_thr hmargT
        rw [← hLTdef, ← hℓTdef, ← hD3Tdef] at hbound
        refine le_trans hbound ?_
        exact mul_le_mul_of_nonneg_right (by rw [hCEdef]; linarith [abs_nonneg C₀]) hD4nn
      · have hsignlt : γ < 0 := not_le.mp hsign
        have hγH : H ≤ -γ := by rw [abs_of_neg hsignlt] at hcase; exact hcase
        have hγT5 : -γ ≤ 5 * T := by rw [abs_of_neg hsignlt] at hγ5T; exact hγ5T
        have hbound := shifted_edge_disc_core hK ht₀K hg hc_vk0 (by rw [hHdef] at hγH; exact hγH)
          hγT5 hsc_thr hmargT
        rw [← hLTdef, ← hℓTdef, ← hD3Tdef] at hbound
        have hconj : ((1 - (c_vk / 2) / D3T : ℝ) : ℂ) + (γ : ℂ) * Complex.I
            = (starRingEnd ℂ) (((1 - (c_vk / 2) / D3T : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * Complex.I) := by
          rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
          push_cast; ring
        rw [hconj, logDeriv_Zc_norm_conj]
        refine le_trans hbound ?_
        exact mul_le_mul_of_nonneg_right (by rw [hCEdef]; linarith [abs_nonneg C₀]) hD4nn
    · -- moderate height: the compact bound
      rw [not_le] at hcase
      set z : ℂ := ((1 - (c_vk / 2) / D3T : ℝ) : ℂ) + (γ : ℂ) * Complex.I with hzdef
      have hzre : z.re = 1 - (c_vk / 2) / D3T := by rw [hzdef]; simp
      have hzim : z.im = γ := by rw [hzdef]; simp
      have hσ₀ge : 1 - δ₀ ≤ z.re := by rw [hzre]; linarith [hδcond]
      have hσ₀le : z.re ≤ 1 := by
        rw [hzre]; have hnn : 0 ≤ (c_vk / 2) / D3T := by positivity
        linarith
      have himle : |z.im| ≤ H := by rw [hzim]; exact le_of_lt hcase
      have hcptb := hcpt z hσ₀ge hσ₀le himle
      refine le_trans hcptb ?_
      calc C₀ ≤ |C₀| := le_abs_self _
        _ ≤ CE := by
          rw [hCEdef]
          have h200 : (0:ℝ) ≤ 200 / c_vk := by positivity
          linarith [h200]
        _ = CE * 1 := (mul_one _).symm
        _ ≤ CE * (LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ)) :=
            mul_le_mul_of_nonneg_left hD41 hCE0.le

end ShiftedEdge

/-! ## W-DOM — window domination + the prime-power discard

The two stones ASM consumes to pass from the log-weighted RESTRICTED prime sum
`Σ_{P≤p≤2P} log p·|Σ_t η_t p^{it}|²` to the full von Mangoldt window sum
`Σ_n Λ(n)·w(n)·|Σ_t η_t n^{it}|²`, then discard the `k ≥ 2` prime powers.  The
nonnegative weight `|Σ_t η_t n^{it}|²` is carried ABSTRACTLY as `g n` (ASM plugs the
honest square — `inner_sum_sq_le` below supplies its uniform bound `B = |𝒯|·Σ|η|²`).

* **`window_dominates`** — the REF-B R-6 direction chain (blessed):
    `log P · Σ_{p∈S} g p`
      `≤ Σ_{p∈S} log p · g p`     (step 1: `log p ≥ log P` on `[P,2P]`, `g ≥ 0`)
      `= Σ_{p∈S} Λ(p)·w(p)·g p`    (on the plateau `Λ(p) = log p`, `w(p) = 1`)
      `≤ Σ'_n Λ(n)·w(n)·g n`.      (step 2: every dropped term — ramp zones AND prime
                                     powers — is `≥ 0`, they ADD, never subtract)
  The `≥ log P` step (R-6 kill-check) touches ONLY the restricted `[P,2P]` sum, so the
  `P/2`-supported ramp mass never enters it.
* **`prime_power_count_le`** — the count of proper prime powers `p^k` (`k ≥ 2`) in
  `[1, M]` is `≤ √M · log₂ M` (each `n = p^k ≤ M` has `p ≤ √M` from `p² ≤ p^k`, and
  `k ≤ log₂ M` from `2^k ≤ p^k`; `n ↦ (minFac n, factorization)` is injective by unique
  factorisation).
* **`inner_sum_sq_le`** — Cauchy–Schwarz on the inner sum: `‖Σ_t ψ_t·b_t‖² ≤ |𝒯|·Σ‖b_t‖²`
  for unit-modulus multipliers (`norm_conj_prime_cpow`: `‖conj(n^{-it})‖ = 1`).
* **`prime_power_discard`** — the weighted-sum discard shape ASM subtracts:
  `Σ Λ(n)·w(n)·g n ≤ log(3P)·(√⌊3P⌋·log₂⌊3P⌋)·B` for any uniform `g ≤ B` (`Λ ≤ log(3P)`,
  `w ≤ 1` on `n ≤ 3P`, folding the count). -/

section WindowDominate
open Finset

/-- **W-DOM — window domination** (REF-B R-6 direction chain).  For `2 ≤ P`, a nonnegative
weight `g` (ASM: `g n = ‖Σ_t η_t n^{it}‖²`), and a prime set `S ⊆ [P, 2P]`,
`log P · Σ_{p∈S} g p ≤ Σ'_n Λ(n)·(primeWindow P n)·g n`.  Step 1 (`log p ≥ log P` on the
window, `g ≥ 0`) is fused with step 2 (`Λ(p) = log p`, `primeWindow P p = 1` on the plateau)
into the per-prime identity `log P · g p ≤ Λ(p)·w(p)·g p`; the passage to the full sum drops
only nonnegative terms (`Λ, w, g ≥ 0`), so `S`'s finite sum is `≤` the total `tsum`. -/
theorem window_dominates {P : ℝ} (hP : 2 ≤ P) {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n)
    {S : Finset ℕ} (hS : ∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) :
    Real.log P * ∑ p ∈ S, g p
      ≤ ∑' n, vonMangoldt n * primeWindow P n * g n := by
  have hP0 : (0 : ℝ) < P := by linarith
  -- the full sum is summable (finite support: `primeWindow P n = 0` past `3P`)
  have hsumm : Summable (fun n => vonMangoldt n * primeWindow P n * g n) := by
    apply summable_of_ne_finset_zero (s := Finset.range (⌊3 * P⌋₊ + 1))
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hge : 3 * P ≤ (n : ℝ) := by
      have h1 : (3 * P : ℝ) < (⌊3 * P⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (3 * P)
      have h2 : ((⌊3 * P⌋₊ : ℕ) + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [primeWindow_eq_zero_upper hP0 hge, mul_zero, zero_mul]
  -- steps 1+2: the per-prime domination
  have hstep : Real.log P * ∑ p ∈ S, g p
      ≤ ∑ p ∈ S, vonMangoldt p * primeWindow P p * g p := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    obtain ⟨hpp, hlb, hub⟩ := hS p hp
    rw [primeWindow_eq_one hP0 hlb hub, vonMangoldt_apply_prime hpp, mul_one]
    exact mul_le_mul_of_nonneg_right (Real.log_le_log hP0 hlb) (hg p)
  -- step 3: the restricted sum ≤ the total (nonnegative terms)
  refine hstep.trans (hsumm.sum_le_tsum S (fun n _ => ?_))
  exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (primeWindow_nonneg hP0 n)) (hg n)

/-- **W-DOM — the prime-power count.**  The number of proper prime powers `p^k` (`k ≥ 2`,
i.e. `IsPrimePow n ∧ ¬ n.Prime`) in `[1, M]` is at most `√M · log₂ M`.  Each such `n = p^k ≤ M`
has `p = minFac n ≤ √M` (from `p² ≤ p^k = n ≤ M`) and `k = n.factorization p ≤ log₂ M` (from
`2^k ≤ p^k = n ≤ M`); the map `n ↦ (minFac n, n.factorization (minFac n))` is injective by
`IsPrimePow.minFac_pow_factorization_eq` (unique factorisation), so the count is bounded by the
product-set cardinality. -/
theorem prime_power_count_le (M : ℕ) :
    ((Finset.Icc 1 M).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)).card
      ≤ Nat.sqrt M * Nat.log 2 M := by
  have hcard : (Finset.Icc 1 (Nat.sqrt M) ×ˢ Finset.Icc 1 (Nat.log 2 M)).card
      = Nat.sqrt M * Nat.log 2 M := by
    rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc, Nat.add_sub_cancel, Nat.add_sub_cancel]
  refine le_trans (Finset.card_le_card_of_injOn
    (fun n => (n.minFac, n.factorization n.minFac)) ?_ ?_) (le_of_eq hcard)
  · -- MapsTo: the (minFac, exponent) pair lands in `[1, √M] × [1, log₂ M]`
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨_, hnM⟩, hpp, hnp⟩ := hn
    have hne1 : n ≠ 1 := hpp.ne_one
    have hpprime : (n.minFac).Prime := Nat.minFac_prime hne1
    have hp2 : 2 ≤ n.minFac := hpprime.two_le
    have hpk : n.minFac ^ n.factorization n.minFac = n := hpp.minFac_pow_factorization_eq
    have hk1 : n.factorization n.minFac ≠ 0 := by
      intro h; rw [h, pow_zero] at hpk; exact hne1 hpk.symm
    have hkne1 : n.factorization n.minFac ≠ 1 := by
      intro h; rw [h, pow_one] at hpk; exact hnp (hpk ▸ hpprime)
    have hk2 : 2 ≤ n.factorization n.minFac := by omega
    have hMpos : M ≠ 0 := by have := hpp.two_le; omega
    have hp_bound : n.minFac ≤ Nat.sqrt M := by
      rw [Nat.le_sqrt']
      calc n.minFac ^ 2 ≤ n.minFac ^ n.factorization n.minFac :=
            Nat.pow_le_pow_right (by omega) hk2
        _ = n := hpk
        _ ≤ M := hnM
    have hk_bound : n.factorization n.minFac ≤ Nat.log 2 M := by
      rw [Nat.le_log_iff_pow_le Nat.one_lt_two hMpos]
      calc 2 ^ n.factorization n.minFac ≤ n.minFac ^ n.factorization n.minFac :=
            Nat.pow_le_pow_left hp2 _
        _ = n := hpk
        _ ≤ M := hnM
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨by omega, hp_bound⟩, ⟨by omega, hk_bound⟩⟩
  · -- InjOn: unique factorisation
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    calc a = a.minFac ^ a.factorization a.minFac := ha.2.1.minFac_pow_factorization_eq.symm
      _ = b.minFac ^ b.factorization b.minFac := by rw [h2, h1]
      _ = b := hb.2.1.minFac_pow_factorization_eq

/-- Unit modulus of the twist multiplier: `‖conj(p^{-it})‖ = 1` for `p ≥ 1` (the exponent
`-(t)·I` is purely imaginary, so the norm is `p^0 = 1`).  Supplies the `‖ψ t‖ ≤ 1` hypothesis
of `inner_sum_sq_le` for the honest `ψ t = conj((p:ℂ)^(-it))` of `primes_dual_iff`. -/
lemma norm_conj_prime_cpow {p : ℕ} (hp : 1 ≤ p) (t : ℝ) :
    ‖(starRingEnd ℂ) ((p : ℂ) ^ (-(t : ℂ) * I))‖ = 1 := by
  have hre : (-(t : ℂ) * I).re = 0 := by simp [Complex.mul_re]
  rw [Complex.norm_conj, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (show 0 < p by omega)), hre,
    Real.rpow_zero]

/-- **W-DOM — Cauchy–Schwarz on the inner sum.**  For unit-modulus multipliers `ψ`
(`‖ψ t‖ ≤ 1`), `‖Σ_{t∈𝒯} ψ_t·b_t‖² ≤ |𝒯|·Σ_{t∈𝒯}‖b_t‖²`.  The uniform bound `B = |𝒯|·Σ|η|²`
that `prime_power_discard` consumes: `‖Σ_t p^{it} η_t‖² ≤ |𝒯|·Σ|η_t|²` (via
`norm_conj_prime_cpow`). -/
lemma inner_sum_sq_le {ψ : ℝ → ℂ} (hψ : ∀ t, ‖ψ t‖ ≤ 1) (𝒯 : Finset ℝ) (b : ℝ → ℂ) :
    ‖∑ t ∈ 𝒯, ψ t * b t‖ ^ 2 ≤ (𝒯.card : ℝ) * ∑ t ∈ 𝒯, ‖b t‖ ^ 2 := by
  have hnorm : ‖∑ t ∈ 𝒯, ψ t * b t‖ ≤ ∑ t ∈ 𝒯, ‖b t‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun t _ => ?_))
    rw [norm_mul]
    calc ‖ψ t‖ * ‖b t‖ ≤ 1 * ‖b t‖ := mul_le_mul_of_nonneg_right (hψ t) (norm_nonneg _)
      _ = ‖b t‖ := one_mul _
  calc ‖∑ t ∈ 𝒯, ψ t * b t‖ ^ 2
      ≤ (∑ t ∈ 𝒯, ‖b t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (𝒯.card : ℝ) * ∑ t ∈ 𝒯, ‖b t‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := 𝒯) (f := fun t => ‖b t‖)

/-- **W-DOM — the prime-power discard.**  For `2 ≤ P`, a nonnegative weight `g` with a uniform
bound `g ≤ B` on the proper prime powers of `[1, ⌊3P⌋]` (ASM: `g n = ‖Σ_t η_t n^{it}‖²`,
`B = |𝒯|·Σ|η|²` from `inner_sum_sq_le`), the `k ≥ 2` contribution to the window sum is
`Σ_n Λ(n)·(primeWindow P n)·g n ≤ log(3P)·(√⌊3P⌋·log₂⌊3P⌋)·B`: each term is `≤ log(3P)·B`
(`Λ(n) ≤ log n ≤ log(3P)` on `n ≤ 3P`, `primeWindow P n ≤ 1`, `g n ≤ B`), and the count is
folded by `prime_power_count_le`.  This is the error row ASM subtracts. -/
theorem prime_power_discard {P : ℝ} (hP : 2 ≤ P) {g : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hg0 : ∀ n, 0 ≤ g n)
    (hgB : ∀ n ∈ (Finset.Icc 1 ⌊3 * P⌋₊).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n),
        g n ≤ B) :
    ∑ n ∈ (Finset.Icc 1 ⌊3 * P⌋₊).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n),
        vonMangoldt n * primeWindow P n * g n
      ≤ Real.log (3 * P) * ((Nat.sqrt ⌊3 * P⌋₊ * Nat.log 2 ⌊3 * P⌋₊ : ℕ) : ℝ) * B := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hlog3P : 0 ≤ Real.log (3 * P) := Real.log_nonneg (by linarith)
  have hfloor : (⌊3 * P⌋₊ : ℝ) ≤ 3 * P := Nat.floor_le (by linarith)
  set PP := (Finset.Icc 1 ⌊3 * P⌋₊).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n) with hPPdef
  -- per-term bound `Λ(n)·w(n)·g n ≤ log(3P)·B`
  have hterm : ∀ n ∈ PP, vonMangoldt n * primeWindow P n * g n ≤ Real.log (3 * P) * B := by
    intro n hn
    have hmem := (Finset.mem_filter.mp hn).1
    rw [Finset.mem_Icc] at hmem
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hmem.1
    have hnle : (n : ℝ) ≤ 3 * P := le_trans (by exact_mod_cast hmem.2) hfloor
    have hΛ : vonMangoldt n ≤ Real.log (3 * P) :=
      le_trans (vonMangoldt_le_log (n := n)) (Real.log_le_log hnpos hnle)
    have hΛw : vonMangoldt n * primeWindow P n ≤ Real.log (3 * P) := by
      calc vonMangoldt n * primeWindow P n
          ≤ Real.log (3 * P) * 1 :=
            mul_le_mul hΛ (primeWindow_le_one hP0 n) (primeWindow_nonneg hP0 n) hlog3P
        _ = Real.log (3 * P) := mul_one _
    exact mul_le_mul hΛw (hgB n hn) (hg0 n) hlog3P
  -- sum ≤ card·(log3P·B), then fold the count
  calc ∑ n ∈ PP, vonMangoldt n * primeWindow P n * g n
      ≤ ∑ _n ∈ PP, Real.log (3 * P) * B := Finset.sum_le_sum hterm
    _ = (PP.card : ℝ) * (Real.log (3 * P) * B) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Nat.sqrt ⌊3 * P⌋₊ * Nat.log 2 ⌊3 * P⌋₊ : ℕ) : ℝ) * (Real.log (3 * P) * B) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hlog3P hB)
        have hcnt := prime_power_count_le ⌊3 * P⌋₊
        rw [← hPPdef] at hcnt
        exact_mod_cast hcnt
    _ = Real.log (3 * P) * ((Nat.sqrt ⌊3 * P⌋₊ * Nat.log 2 ⌊3 * P⌋₊ : ℕ) : ℝ) * B := by ring

end WindowDominate


/-! ## A-1 — the per-pair contour estimate (`per_pair_contour`)

The reconciliation of `rep_truncated`'s truncated vertical line with `pole_residue_term`'s
rectangle boundary: the orientation `I·V_right = 2πi·windowMellin(1+iu) − (B_bot−B_top) + I·V_left`
(RES = the rectBI residue), the LEFT edge priced by `shifted_edge_price` × the `P^{σ₀}` kernel mass
(`∫(σ₀²+v²)⁻¹ = π/σ₀ ≤ 2π` at `σ₀ ≥ 1/2`), the HORIZONTALS priced by the region bound
(`shifted_edge_disc_core_gen` on the near-1 strip `x ∈ [σ₀, 1+w]`, the `Zc`-Chebyshev
`sum_vonMangoldt_le_pole_add_Zc` on the sliver `x ∈ (1+w, c]`), the tail by TRUNC.  The six `T₀`
thresholds (incl. `shifted_edge_price`'s own `exp(exp(9000·c_vk + c_vk/(2δ₀) + 1))`) auto-inherit
by destructuring `shifted_edge_price`. -/

section PerPairContour
open Complex Salt.SW Salt.Vk Metric intervalIntegral

-- Helper 1: the Zc-Chebyshev sliver bound.
lemma sum_vonMangoldt_le_pole_add_Zc {x : ℝ} (hx : 1 < x) :
    ∑' n, vonMangoldt n / (n : ℝ) ^ x ≤ 1 / (x - 1) + ‖logDeriv Zc (x : ℂ)‖ := by
  set S : ℝ := ∑' n, vonMangoldt n / (n : ℝ) ^ x with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact tsum_nonneg (fun n =>
      div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) x))
  have hxre : ((x : ℂ)).re = x := Complex.ofReal_re x
  have hxc : (1 : ℝ) < ((x : ℂ)).re := by rw [hxre]; exact hx
  have hζ : riemannZeta (x : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hxre]; linarith)
  have hx1 : (x : ℂ) ≠ 1 := by
    intro h; rw [h] at hxre; simp at hxre; linarith
  -- the real sum, cast to ℂ, equals the LSeries
  have hsummR : Summable (fun n => vonMangoldt n / (n : ℝ) ^ x) := summable_vonMangoldt_div_rpow hx
  have hSC : (S : ℂ) = LSeries ↗vonMangoldt (x : ℂ) := by
    have hterm : ∀ n : ℕ, ((vonMangoldt n / (n : ℝ) ^ x : ℝ) : ℂ)
        = LSeries.term ↗vonMangoldt (x : ℂ) n := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [LSeries.term_of_ne_zero hn.ne']
        rw [Complex.ofReal_div, ← Complex.ofReal_natCast (n := n),
          ← Complex.ofReal_cpow (by positivity)]
    rw [hSdef]
    rw [show ((∑' n, vonMangoldt n / (n : ℝ) ^ x : ℝ) : ℂ)
        = ∑' n, ((vonMangoldt n / (n : ℝ) ^ x : ℝ) : ℂ) from
        (Complex.ofRealCLM.map_tsum hsummR)]
    exact tsum_congr hterm
  have hLS : LSeries ↗vonMangoldt (x : ℂ) = - logDeriv riemannZeta (x : ℂ) := by
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hxc, logDeriv_apply, neg_div]
  have hsplit : (S : ℂ) = 1 / ((x : ℂ) - 1) - logDeriv Zc (x : ℂ) := by
    rw [hSC, hLS, logDeriv_zeta_eq hx1 hζ]; ring
  -- take norms
  have hnormpole : ‖(1 : ℂ) / ((x : ℂ) - 1)‖ = 1 / (x - 1) := by
    rw [norm_div, norm_one]
    congr 1
    rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  calc S = ‖(S : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
    _ = ‖(1 : ℂ) / ((x : ℂ) - 1) - logDeriv Zc (x : ℂ)‖ := by rw [hsplit]
    _ ≤ ‖(1 : ℂ) / ((x : ℂ) - 1)‖ + ‖logDeriv Zc (x : ℂ)‖ := norm_sub_le _ _
    _ = 1 / (x - 1) + ‖logDeriv Zc (x : ℂ)‖ := by rw [hnormpole]

/-- **The c-line Dirichlet sum bound.**  There is `C₀ ≥ 0` such that for every `2 ≤ P`, at the
contour abscissa `c = 1 + 1/log P`, `∑ Λ(n)/nᶜ ≤ log P + C₀`.  The pole part `1/(c−1) = log P`
(`sum_vonMangoldt_le_pole_add_Zc`); the entire factor `‖logDeriv Zc c‖ ≤ C₀` uniformly on the
compact real segment `[1, 1+1/log 2]` (`logDeriv_Zc_compact_bound` at height `0`). -/
lemma sum_vonMangoldt_cline_bound :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {P : ℝ}, 2 ≤ P →
      ∑' n, vonMangoldt n / (n : ℝ) ^ (1 + (Real.log P)⁻¹) ≤ Real.log P + C₀ := by
  obtain ⟨δ₀, C₀, hδ₀, hcpt⟩ :=
    logDeriv_Zc_compact_bound (M := 0) (c := 1 + 1 / Real.log 2) (le_refl 0)
      (by have h : 0 < Real.log 2 := Real.log_pos (by norm_num); linarith [div_pos one_pos h])
  refine ⟨|C₀|, abs_nonneg _, ?_⟩
  intro P hP
  have hP0 : (0:ℝ) < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlog2P : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := 1 + (Real.log P)⁻¹ with hcdef
  have hc1 : 1 < c := by rw [hcdef]; have := inv_pos.mpr hlogP; linarith
  have hbase := sum_vonMangoldt_le_pole_add_Zc hc1
  have hcm1 : c - 1 = (Real.log P)⁻¹ := by rw [hcdef]; ring
  have hpole : 1 / (c - 1) = Real.log P := by rw [hcm1, one_div, inv_inv]
  have hcre : ((c:ℂ)).re = c := Complex.ofReal_re c
  have hcim : ((c:ℂ)).im = 0 := Complex.ofReal_im c
  have hcub : c ≤ 1 + 1 / Real.log 2 := by
    rw [hcdef]
    have : (Real.log P)⁻¹ ≤ (Real.log 2)⁻¹ := inv_anti₀ hlog2 hlog2P
    rw [one_div]; linarith
  have hZcbd : ‖logDeriv Zc (c:ℂ)‖ ≤ |C₀| := by
    refine le_trans (hcpt (c:ℂ) ?_ ?_ ?_) (le_abs_self C₀)
    · rw [hcre]; linarith
    · rw [hcre]; exact hcub
    · rw [hcim]; norm_num
  calc ∑' n, vonMangoldt n / (n : ℝ) ^ c ≤ 1 / (c - 1) + ‖logDeriv Zc (c:ℂ)‖ := hbase
    _ ≤ Real.log P + |C₀| := by rw [hpole]; linarith [hZcbd]

/-- **The truncation-kernel constant bound.**  At the contour abscissa `c = 1 + 1/log P`, the
`rep_truncated` kernel constant `Cₖ(P,c) = 2·(3P)^{c+1}/P + 2·P^{c+1}/(P/2)` is `≤
(18·3^{1/log 2}+4)·e·P` — linear in `P` (the `P^c = e·P` cancellation, `3^{c+1} ≤ 9·3^{1/log 2}`).
Feeds the truncation-tail bound `(Σ Λ/nᶜ)·Cₖ·(2/T') ≍ P·log P/T`. -/
lemma truncKernel_const_le {P : ℝ} (hP : 2 ≤ P) :
    2 * (2 * P + P) ^ ((1 + (Real.log P)⁻¹) + 1) / P
        + 2 * (P / 2 + P / 2) ^ ((1 + (Real.log P)⁻¹) + 1) / (P / 2)
      ≤ (2 * 9 * (3:ℝ) ^ ((Real.log 2)⁻¹) + 4) * Real.exp 1 * P := by
  have hP0 : (0:ℝ) < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2P : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  set c : ℝ := 1 + (Real.log P)⁻¹ with hcdef
  -- P^c = e·P
  have hPc : P ^ c = Real.exp 1 * P := by
    rw [hcdef, Real.rpow_add hP0, Real.rpow_one, mul_comm]
    congr 1
    rw [Real.rpow_def_of_pos hP0, mul_inv_cancel₀ hlogP.ne']
  -- P^(c+1) = P^c · P
  have hPc1 : P ^ (c + 1) = P ^ c * P := by rw [Real.rpow_add hP0, Real.rpow_one]
  -- 3^(c+1) = 9 · 3^(1/logP) ≤ 9 · 3^(1/log2)
  have h3c1 : (3:ℝ) ^ (c + 1) ≤ 9 * (3:ℝ) ^ ((Real.log 2)⁻¹) := by
    have : c + 1 = 2 + (Real.log P)⁻¹ := by rw [hcdef]; ring
    rw [this, Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    have h9 : (3:ℝ) ^ (2:ℝ) = 9 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [h9]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact inv_anti₀ hlog2 hlog2P
  -- (3P)^(c+1) = 3^(c+1)·P^(c+1)
  have h3Pc1 : (3 * P) ^ (c + 1) = (3:ℝ) ^ (c + 1) * P ^ (c + 1) :=
    Real.mul_rpow (by norm_num) hP0.le
  have hPcnn : 0 ≤ P ^ c := Real.rpow_nonneg hP0.le c
  -- rewrite each term
  have e1 : 2 * (2 * P + P) ^ (c + 1) / P = 2 * (3:ℝ) ^ (c + 1) * P ^ c := by
    rw [show 2 * P + P = 3 * P by ring, h3Pc1, hPc1]; field_simp
  have e2 : 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2) = 4 * P ^ c := by
    rw [show P / 2 + P / 2 = P by ring, hPc1]; field_simp; norm_num
  rw [e1, e2]
  have hkey : 2 * (3:ℝ) ^ (c + 1) * P ^ c ≤ 2 * (9 * (3:ℝ) ^ ((Real.log 2)⁻¹)) * P ^ c :=
    mul_le_mul_of_nonneg_right (by linarith [h3c1]) hPcnn
  have hstep : 2 * (3:ℝ) ^ (c + 1) * P ^ c + 4 * P ^ c
      ≤ 2 * (9 * (3:ℝ) ^ ((Real.log 2)⁻¹)) * P ^ c + 4 * P ^ c := by linarith [hkey]
  refine le_trans hstep ?_
  rw [hPc]; apply le_of_eq; ring

set_option maxHeartbeats 12800000 in
-- The σ-generalized disc-core copies `shifted_edge_disc_core`'s sphere discharge + `Pinv/W/Mζ`
-- region numerics + closing `D₄` assembly verbatim (only `hsc`/`hζs`/`hdist` adapt to the general
-- real part `x ∈ [σ₀, 1+w]`); the closing arithmetic needs the same 12.8M budget as its template.
lemma shifted_edge_disc_core_gen {K t₀K c_vk : ℝ} (hK : 1 ≤ K) (ht₀K : 3 ≤ t₀K)
    (hg : ∀ σ t : ℝ, t₀K ≤ t → 1 - vkTheta t ≤ σ → σ ≤ 3 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K * Real.log t)
    (hc_vk : 0 < c_vk)
    {T γ x : ℝ}
    (hxlb : 1 - (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)) ≤ x)
    (hxub : x ≤ 1 + (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)))
    (hγ : Real.exp (Real.exp (8 * Real.log (20000 * K) + 1100)) + t₀K + 3 ≤ γ)
    (hγT : γ ≤ 5 * T)
    (hsc_thr : 9000 * c_vk ≤ Real.log (Real.log (5 * T + 1)))
    (hmargin : ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ))) :
    ‖logDeriv Zc ((x : ℂ) + (γ : ℂ) * Complex.I)‖
      ≤ (10 ^ 8 + 200 / c_vk) * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) := by
  -- the 5T+1 denominators (fold the goal)
  set LT : ℝ := Real.log (5 * T + 1) with hLTdef
  set ℓT : ℝ := Real.log LT with hℓTdef
  set D3T : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) with hD3Tdef
  set w : ℝ := (c_vk / 2) / D3T with hwdef
  set s : ℂ := (x : ℂ) + (γ : ℂ) * Complex.I with hsdef
  -- === template height thresholds (γ-only, verbatim + inlined `pow_height_facts`) ===
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  set A : ℝ := 8 * Real.log (20000 * K) + 1100 with hAdef
  have hA1100 : 1100 ≤ A := by
    have : (0:ℝ) ≤ Real.log (20000 * K) := Real.log_nonneg (by nlinarith [hK])
    rw [hAdef]; linarith
  have hEpos : 0 < Real.exp (Real.exp A) := Real.exp_pos _
  have hγim : Real.exp (Real.exp A) + t₀K + 3 ≤ γ := hγ
  have hσimE : Real.exp (Real.exp A) ≤ γ := by linarith [ht₀K, hγim]
  have hγpos : 0 < γ := lt_of_lt_of_le hEpos hσimE
  have hγ2 : (2:ℝ) ≤ γ := by linarith [hEpos, ht₀K, hγim]
  have hexpA1 : 1 < Real.exp A := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith [hA1100])
  have hEe : Real.exp 1 < Real.exp (Real.exp A) := Real.exp_lt_exp.mpr hexpA1
  have hγe : Real.exp 1 < γ - 1 := by linarith [hEe, hγim, ht₀K, hEpos]
  have hγt₀ : t₀K ≤ γ - 1 := by linarith [hEpos, hγim]
  have hfactsγ : 3 ≤ Real.log γ ∧ A ≤ Real.log (Real.log γ) := by
    have hlogE : Real.log (Real.exp (Real.exp A)) = Real.exp A := Real.log_exp _
    have hlogx : Real.exp A ≤ Real.log γ := by rw [← hlogE]; exact Real.log_le_log hEpos hσimE
    have hexp2 : (3:ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
    have hexpA3 : (3:ℝ) ≤ Real.exp A := le_trans hexp2 (Real.exp_le_exp.mpr (by linarith [hA1100]))
    refine ⟨le_trans hexpA3 hlogx, ?_⟩
    calc A = Real.log (Real.exp A) := (Real.log_exp A).symm
      _ ≤ Real.log (Real.log γ) := Real.log_le_log (Real.exp_pos A) hlogx
  -- abbreviations
  set Lg : ℝ := Real.log γ with hLdef
  set ℓ : ℝ := Real.log Lg with hℓdef
  have hL3 : (3:ℝ) ≤ Lg := hfactsγ.1
  have hℓA : A ≤ ℓ := hfactsγ.2
  have hℓ1100 : (1100:ℝ) ≤ ℓ := le_trans hA1100 hℓA
  have hL0 : 0 < Lg := by linarith [hL3]
  have hℓ0 : 0 < ℓ := by linarith [hℓ1100]
  -- log 3γ facts
  set L3 : ℝ := Real.log (3 * γ) with hL3def
  have hlog3le2 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)]
  have hL3eq : L3 = Real.log 3 + Lg := by rw [hL3def, Real.log_mul (by norm_num) hγpos.ne']
  have hL3lb : Lg ≤ L3 := by rw [hL3eq]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]
  have hL3ub : L3 ≤ 2 * Lg := by rw [hL3eq]; linarith [hlog3le2, hL3]
  have hL30 : 0 < L3 := by linarith [hL3lb, hL0]
  set ℓ3 : ℝ := Real.log L3 with hℓ3def
  have hℓ3lb : ℓ ≤ ℓ3 := by rw [hℓ3def, hℓdef]; exact Real.log_le_log hL0 hL3lb
  have hlog2le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
  have hℓ3ub : ℓ3 ≤ 2 * ℓ := by
    rw [hℓ3def]
    calc Real.log L3 ≤ Real.log (2 * Lg) := Real.log_le_log hL30 hL3ub
      _ = Real.log 2 + ℓ := by rw [Real.log_mul (by norm_num) hL0.ne', ← hℓdef]
      _ ≤ 2 * ℓ := by linarith [hlog2le1, hℓ1100]
  have hℓ30 : 0 < ℓ3 := by linarith [hℓ3lb, hℓ0]
  have hℓ31100 : (1100:ℝ) ≤ ℓ3 := by linarith [hℓ3lb, hℓ1100]
  -- region parameters (verbatim)
  set Θ : ℝ := vkTheta (3 * γ) with hΘdef
  set Pinv : ℝ := 1000 * L3 ^ ((3:ℝ)/4) * ℓ3 ^ (2:ℕ) with hPinvdef
  have hL34pos : 0 < L3 ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos hL30 _
  have hPinvpos : 0 < Pinv := by rw [hPinvdef]; positivity
  have hΘval : Θ = 1 / 1000 / (L3 ^ ((3:ℝ)/4) * ℓ3 ^ (2:ℕ)) := by
    rw [hΘdef, vkTheta, ← hL3def, ← hℓ3def]
  have hΘPinv : Θ = 1 / Pinv := by
    rw [eq_div_iff (ne_of_gt hPinvpos), hΘval, hPinvdef]
    field_simp [ne_of_gt hL34pos, ne_of_gt hℓ30]
  have hΘ0 : 0 < Θ := by rw [hΘPinv]; positivity
  set Mζ : ℝ := K * L3 with hMζdef
  have hMζpos : 0 < Mζ := by rw [hMζdef]; positivity
  have hMζ1 : (1:ℝ) ≤ Mζ := by rw [hMζdef]; nlinarith [hK, hL3lb, hL3]
  have hPinv2 : (2:ℝ) ≤ Pinv := by
    rw [hPinvdef]
    have h1 : (1:ℝ) ≤ L3 ^ ((3:ℝ)/4) := Real.one_le_rpow (by linarith [hL3lb, hL3]) (by norm_num)
    have h2 : (1:ℝ) ≤ ℓ3 ^ (2:ℕ) := one_le_pow₀ (by linarith [hℓ31100])
    nlinarith [h1, h2]
  have hΘ12 : Θ ≤ 1 / 2 := by
    rw [hΘPinv]; rw [div_le_div_iff₀ hPinvpos (by norm_num)]; linarith [hPinv2]
  have hgrowth : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → γ - 1 ≤ z.im → z.im ≤ 3 * γ →
      ‖riemannZeta z‖ ≤ Mζ := by
    intro z h1 h2 h3 h4
    rw [hΘdef] at h1; rw [hMζdef]
    exact pow_uniform_growth hK ht₀K hg hγe hγt₀ z h1 h2 h3 h4
  set W : ℝ := Real.log (20 * Pinv * Mζ) with hWdef
  have hWeq : W = Real.log (20000 * K) + (7 / 4) * ℓ3 + 2 * Real.log ℓ3 := by
    have hPinvne : Pinv ≠ 0 := ne_of_gt hPinvpos
    have hL3ne : L3 ≠ 0 := ne_of_gt hL30
    have hℓ3ne : ℓ3 ≠ 0 := ne_of_gt hℓ30
    have h20000 : Real.log (20000 * K) = Real.log 20 + Real.log 1000 + Real.log K := by
      rw [show (20000:ℝ) * K = 20 * 1000 * K by ring, Real.log_mul (by norm_num) hKpos.ne',
        Real.log_mul (by norm_num) (by norm_num)]
    rw [hWdef, Real.log_mul (by positivity) (ne_of_gt hMζpos),
      Real.log_mul (by norm_num) hPinvne, hMζdef, Real.log_mul hKpos.ne' hL3ne,
      hPinvdef, Real.log_mul (by positivity) (pow_ne_zero 2 hℓ3ne),
      Real.log_mul (by norm_num) (ne_of_gt hL34pos), Real.log_rpow hL30, Real.log_pow,
      ← hℓ3def, h20000]
    push_cast; ring
  have hlog20K : Real.log (20000 * K) ≤ ℓ / 8 := by rw [hAdef] at hℓA; linarith
  have hlogℓ3le : Real.log ℓ3 ≤ ℓ3 := by linarith [Real.log_le_sub_one_of_pos hℓ30]
  have hWub : W ≤ 8 * ℓ := by
    rw [hWeq]; linarith [hlog20K, hℓ3ub, hlogℓ3le]
  have hW0 : 0 ≤ W := by
    rw [hWdef]; apply Real.log_nonneg
    nlinarith [hPinv2, hMζ1, hMζpos, hPinvpos]
  have hγ1 : (1:ℝ) ≤ |γ| := by rw [abs_of_nonneg hγpos.le]; linarith [hγ2]
  -- sphere discharge (verbatim, height γ)
  have hsph : ∀ R : ℝ, 0 ≤ R → R ≤ 3 / 2 * Θ →
      ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) R,
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 5 * Mζ / Θ := by
    intro R hR0 hR z hz
    have hzc : ‖z - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ = R := by
      rw [← dist_eq_norm, ← mem_sphere]; exact hz
    have hcre : (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I).re = 1 + Θ / 2 := by simp
    have hcim : (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I).im = γ := by simp
    have hreb : |z.re - (1 + Θ / 2)| ≤ R := by
      have h := Complex.abs_re_le_norm (z - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I))
      rw [Complex.sub_re, hcre, hzc] at h; exact h
    have himb : |z.im - γ| ≤ R := by
      have h := Complex.abs_im_le_norm (z - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I))
      rw [Complex.sub_im, hcim, hzc] at h; exact h
    have hre1 : 1 - Θ ≤ z.re := by have := (abs_le.mp hreb).1; nlinarith [hR, hΘ12]
    have hre2 : z.re ≤ 2 := by have := (abs_le.mp hreb).2; nlinarith [hR, hΘ12]
    have him1 : γ - 1 ≤ z.im := by have := (abs_le.mp himb).1; nlinarith [hR, hΘ12]
    have him2 : z.im ≤ 3 * γ := by have := (abs_le.mp himb).2; nlinarith [hR, hΘ12, hγ2]
    exact Zc_ratio_sphere_bound hΘ0 hΘ12 hγ1 hMζ1 hR0 hR hz (hgrowth z hre1 hre2 him1 him2)
  have hR74 : (7:ℝ) / 4 * (6 * Θ / 7) ≤ 3 / 2 * Θ := by nlinarith [hΘ0]
  have hR32 : (3:ℝ) / 2 * (6 * Θ / 7) ≤ 3 / 2 * Θ := by nlinarith [hΘ0]
  have hsphere74 := hsph (7 / 4 * (6 * Θ / 7)) (by positivity) hR74
  have hsphere32 := hsph (3 / 2 * (6 * Θ / 7)) (by positivity) hR32
  have hM₀1 : (1:ℝ) ≤ 5 * Mζ / Θ := by rw [le_div_iff₀ hΘ0]; nlinarith [hMζ1, hΘ12, hΘ0]
  -- === the 5T+1 denominators: positivity + monotonicity ===
  have hγ5T1 : γ ≤ 5 * T + 1 := by linarith [hγT]
  have hLTpos : 0 < LT := by rw [hLTdef]; exact Real.log_pos (by linarith [hγ2, hγT])
  have hLgLT : Lg ≤ LT := by rw [hLdef, hLTdef]; exact Real.log_le_log hγpos hγ5T1
  have hℓTpos : 0 < ℓT := by rw [hℓTdef]; exact Real.log_pos (by linarith [hL3, hLgLT])
  have hℓℓT : ℓ ≤ ℓT := by rw [hℓdef, hℓTdef]; exact Real.log_le_log hL0 hLgLT
  have hℓT1100 : (1100:ℝ) ≤ ℓT := le_trans hℓ1100 hℓℓT
  have hℓT1 : (1:ℝ) ≤ ℓT := by linarith [hℓT1100]
  have hD3Tpos : 0 < D3T := by rw [hD3Tdef]; positivity
  have hw0 : 0 < w := by rw [hwdef]; exact div_pos (by linarith [hc_vk]) hD3Tpos
  have hsre : s.re = x := by rw [hsdef]; simp
  have hsim : s.im = γ := by rw [hsdef]; simp
  -- L3 ≤ 2 LT, ℓ3 ≤ 2 ℓT (the constant-chase monotonicity)
  have hTpos : 0 < T := by linarith [hγpos, hγT]
  have hL3_2LT : L3 ≤ 2 * LT := by
    have h1 : (3:ℝ) * γ ≤ (5 * T + 1) ^ 2 := by nlinarith [hγT, hTpos, sq_nonneg (5 * T - 1)]
    have h2 : Real.log (3 * γ) ≤ Real.log ((5 * T + 1) ^ 2) := Real.log_le_log (by positivity) h1
    rw [hL3def]
    calc Real.log (3 * γ) ≤ Real.log ((5 * T + 1) ^ 2) := h2
      _ = 2 * LT := by rw [Real.log_pow, ← hLTdef]; push_cast; ring
  have hℓ3_2ℓT : ℓ3 ≤ 2 * ℓT := by
    rw [hℓ3def]
    calc Real.log L3 ≤ Real.log (2 * LT) := Real.log_le_log hL30 hL3_2LT
      _ = Real.log 2 + ℓT := by rw [Real.log_mul (by norm_num) hLTpos.ne', ← hℓTdef]
      _ ≤ 2 * ℓT := by linarith [hlog2le1, hℓT1]
  -- Pinv ≤ 8000 · LT^{3/4} · ℓT²
  have hPinv5 : Pinv ≤ 8000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (2:ℕ)) := by
    have hL34 : L3 ^ ((3:ℝ)/4) ≤ 2 * LT ^ ((3:ℝ)/4) := by
      calc L3 ^ ((3:ℝ)/4) ≤ (2 * LT) ^ ((3:ℝ)/4) := Real.rpow_le_rpow hL30.le hL3_2LT (by norm_num)
        _ = 2 ^ ((3:ℝ)/4) * LT ^ ((3:ℝ)/4) := Real.mul_rpow (by norm_num) hLTpos.le
        _ ≤ 2 * LT ^ ((3:ℝ)/4) := by
            have h2 : (2:ℝ) ^ ((3:ℝ)/4) ≤ 2 := by
              calc (2:ℝ) ^ ((3:ℝ)/4) ≤ (2:ℝ) ^ (1:ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one 2
            nlinarith [h2, Real.rpow_nonneg hLTpos.le ((3:ℝ)/4)]
    have hℓ3sq : ℓ3 ^ (2:ℕ) ≤ 4 * ℓT ^ (2:ℕ) := by
      calc ℓ3 ^ (2:ℕ) ≤ (2 * ℓT) ^ (2:ℕ) := pow_le_pow_left₀ hℓ30.le hℓ3_2ℓT 2
        _ = 4 * ℓT ^ (2:ℕ) := by ring
    calc Pinv = 1000 * (L3 ^ ((3:ℝ)/4) * ℓ3 ^ (2:ℕ)) := by rw [hPinvdef]; ring
      _ ≤ 1000 * ((2 * LT ^ ((3:ℝ)/4)) * (4 * ℓT ^ (2:ℕ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hL34 hℓ3sq (by positivity) (by positivity)
      _ = 8000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (2:ℕ)) := by ring
  -- === centering, zero-freeness, min-distance (the LEFT-point adaptations) ===
  have hsc : ‖s - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 23 / 20 * (6 * Θ / 7) := by
    have hsub : s - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
        = ((x - (1 + Θ / 2) : ℝ) : ℂ) := by
      rw [hsdef]; push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs]
    have hwPinv : w * Pinv ≤ 17 / 35 := by
      rw [hwdef, div_mul_eq_mul_div, div_le_iff₀ hD3Tpos, hD3Tdef]
      have hcc : (4000:ℝ) * c_vk ≤ 17 / 35 * ℓT := by nlinarith [hsc_thr, hc_vk]
      have hAle : c_vk / 2 * Pinv ≤ c_vk / 2 * (8000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (2:ℕ))) :=
        mul_le_mul_of_nonneg_left hPinv5 (by linarith [hc_vk])
      nlinarith [hAle, hcc, Real.rpow_nonneg hLTpos.le ((3:ℝ)/4), pow_nonneg hℓTpos.le 2,
        mul_nonneg (Real.rpow_nonneg hLTpos.le ((3:ℝ)/4)) (pow_nonneg hℓTpos.le 2), hℓTpos]
    have hsc_key : w ≤ 17 * Θ / 35 := by
      rw [hΘPinv, show (17:ℝ) * (1 / Pinv) / 35 = 17 / (35 * Pinv) by field_simp]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hwPinv, hPinvpos]
    rw [abs_le]
    exact ⟨by nlinarith [hsc_key, hΘ0, hxlb, hw0], by nlinarith [hsc_key, hΘ0, hxub, hw0]⟩
  have hs1 : s ≠ 1 := by
    rw [hsdef]; intro h
    have := congrArg Complex.im h; simp at this; linarith [hγ2, this]
  have hζs : riemannZeta s ≠ 0 := by
    intro hζ0
    have him : |s.im| ≤ 5 * T + 1 := by
      rw [hsim, abs_of_nonneg hγpos.le]; linarith [hγT]
    have hmr := hmargin s hζ0 him
    rw [hsre] at hmr
    have hlt : w < c_vk / D3T := by
      rw [hwdef, div_lt_div_iff₀ hD3Tpos hD3Tpos]; nlinarith [hc_vk, hD3Tpos]
    linarith [hmr, hlt, hxlb]
  have hZcs : Zc s ≠ 0 := Zc_ne_zero_of_zeta_ne hζs
  have hdist : ∀ ρ : ℂ, Zc ρ = 0 →
      ρ ∈ ball (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (3 / 2 * (6 * Θ / 7)) →
        w ≤ ‖s - ρ‖ := by
    intro ρ hZcρ hρball
    rw [mem_ball, dist_eq_norm] at hρball
    have hcim : (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I).im = γ := by simp
    have himb : |ρ.im - γ| ≤ 3 / 2 * (6 * Θ / 7) := by
      have h := Complex.abs_im_le_norm (ρ - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I))
      rw [Complex.sub_im, hcim] at h; linarith [h, hρball]
    have hrad : 3 / 2 * (6 * Θ / 7) ≤ 9 / 14 := by nlinarith [hΘ12, hΘ0]
    have hρim_lb : γ - 9 / 14 ≤ ρ.im := by have := (abs_le.mp himb).1; linarith [hrad]
    have hρim_ub : ρ.im ≤ γ + 9 / 14 := by have := (abs_le.mp himb).2; linarith [hrad]
    have hρimpos : 0 < ρ.im := by linarith [hρim_lb, hγ2]
    have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hρimpos; simp at hρimpos
    have hζρ : riemannZeta ρ = 0 := by
      rw [Zc_eq_of_ne hρ1] at hZcρ
      exact (mul_eq_zero.mp hZcρ).resolve_left (sub_ne_zero.mpr hρ1)
    have hρimabs : |ρ.im| ≤ 5 * T + 1 := by
      rw [abs_of_nonneg hρimpos.le]; linarith [hρim_ub, hγT]
    have hmr := hmargin ρ hζρ hρimabs
    have hdist_re : w ≤ s.re - ρ.re := by
      rw [hsre]
      have hww : w = c_vk / D3T - (c_vk / 2) / D3T := by rw [hwdef]; field_simp; ring
      linarith [hmr, hww, hxlb]
    have h := Complex.abs_re_le_norm (s - ρ)
    rw [Complex.sub_re] at h
    linarith [h, le_abs_self (s.re - ρ.re), hdist_re]
  -- === run the near-region lemma + the rewrites (verbatim) ===
  have hnear := near_norm_logDeriv_Zc_le hΘ0 hM₀1 hw0 hsc hZcs hsphere74 hsphere32 hdist
  have h140 : (120:ℝ) / (6 * Θ / 7) = 140 * Pinv := by
    rw [hΘPinv]; field_simp [ne_of_gt hPinvpos]; ring
  have h4M : (4:ℝ) * (5 * Mζ / Θ) = 20 * Pinv * Mζ := by
    rw [hΘPinv]; field_simp [ne_of_gt hPinvpos]; ring
  have hlog4M : Real.log (4 * (5 * Mζ / Θ)) = W := by rw [h4M]
  rw [h140, hlog4M] at hnear
  -- hnear : ‖logDeriv Zc s‖ ≤ 140 * Pinv * W + W / Real.log (7/6) / w
  -- === the final D₄(5T+1) numeric ===
  have hD4nn : (0:ℝ) ≤ LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ) :=
    mul_nonneg (Real.rpow_nonneg hLTpos.le _) (pow_nonneg hℓTpos.le _)
  have hℓT34 : LT ^ ((3:ℝ)/4) * ℓT ^ (3:ℕ) ≤ LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ) := by
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hLTpos.le _)
    exact pow_le_pow_right₀ hℓT1 (by norm_num)
  have hW8ℓT : W ≤ 8 * ℓT := le_trans hWub (by linarith [hℓℓT])
  have hterm1 : 140 * Pinv * W ≤ 10 ^ 8 * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := by
    have hPW : Pinv * W ≤ 64000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (3:ℕ)) := by
      calc Pinv * W ≤ (8000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (2:ℕ))) * (8 * ℓT) :=
            mul_le_mul hPinv5 hW8ℓT hW0 (by positivity)
        _ = 64000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (3:ℕ)) := by ring
    calc 140 * Pinv * W = 140 * (Pinv * W) := by ring
      _ ≤ 140 * (64000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (3:ℕ))) :=
          mul_le_mul_of_nonneg_left hPW (by norm_num)
      _ = 8960000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (3:ℕ)) := by ring
      _ ≤ 8960000 * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := mul_le_mul_of_nonneg_left hℓT34 (by norm_num)
      _ ≤ 10 ^ 8 * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := by nlinarith [hD4nn]
  have h76pos : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have h76ge : (1:ℝ) / 7 ≤ Real.log (7 / 6) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 6 / 7 by norm_num)
    rw [show (6:ℝ) / 7 = (7 / 6)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hWlog : W / Real.log (7 / 6) ≤ 56 * ℓT := by
    rw [div_le_iff₀ h76pos]
    nlinarith [hW8ℓT, mul_nonneg (by positivity : (0:ℝ) ≤ 56 * ℓT) (sub_nonneg.mpr h76ge), hℓTpos]
  have h1overw : (1:ℝ) / w = 2 * D3T / c_vk := by
    rw [hwdef]; field_simp
  have hterm2 : W / Real.log (7 / 6) / w ≤ 200 / c_vk * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := by
    rw [div_eq_mul_one_div (W / Real.log (7 / 6)) w, h1overw]
    have hstep : W / Real.log (7 / 6) * (2 * D3T / c_vk) ≤ 56 * ℓT * (2 * D3T / c_vk) :=
      mul_le_mul_of_nonneg_right hWlog (by positivity)
    refine le_trans hstep ?_
    rw [hD3Tdef]
    have hXc : (0:ℝ) ≤ (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) / c_vk := div_nonneg hD4nn hc_vk.le
    calc 56 * ℓT * (2 * (LT ^ ((3:ℝ)/4) * ℓT ^ (3:ℕ)) / c_vk)
        = 112 * ((LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) / c_vk) := by ring
      _ ≤ 200 * ((LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) / c_vk) :=
          mul_le_mul_of_nonneg_right (by norm_num) hXc
      _ = 200 / c_vk * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := by ring
  calc ‖logDeriv Zc s‖ ≤ 140 * Pinv * W + W / Real.log (7 / 6) / w := hnear
    _ ≤ 10 ^ 8 * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) + 200 / c_vk * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := by
        linarith [hterm1, hterm2]
    _ = (10 ^ 8 + 200 / c_vk) * (LT ^ ((3:ℝ)/4) * ℓT ^ (4:ℕ)) := by ring


set_option maxHeartbeats 800000 in
-- The strip generalization threads the same threshold/disc-core assembly as `shifted_edge_price`
-- across `x ∈ [1−w, 1+w]`; the default budget is tight for the packaged case split.
theorem shifted_edge_price_strip :
    ∃ (c_vk CE T₀ : ℝ), 0 < c_vk ∧ 0 < CE ∧ 3 ≤ T₀ ∧
      (∀ (T : ℝ), T₀ ≤ T → ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
          ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ))) ∧
      ∀ (T x γ : ℝ), T₀ ≤ T →
          1 - (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)) ≤ x →
          x ≤ 1 + (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)) →
          |γ| ≤ 5 * T →
        ‖logDeriv Zc ((x : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ CE * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) := by
  obtain ⟨c_vk, T₁, hc_vk0, hT₁, hmarg⟩ := rect_zero_free_margin
  obtain ⟨K, t₀K, hK, ht₀K, hg⟩ := Salt.Vk.zeta_growth_pow
  set H : ℝ := Real.exp (Real.exp (8 * Real.log (20000 * K) + 1100)) + t₀K + 3 with hHdef
  have hH0 : 0 ≤ H := by
    rw [hHdef]; have := Real.exp_pos (Real.exp (8 * Real.log (20000 * K) + 1100)); linarith [ht₀K]
  obtain ⟨δ₀, C₀, hδ₀0, hcpt⟩ := logDeriv_Zc_compact_bound (M := H) (c := 2) hH0 (by norm_num)
  set Cbig : ℝ := 9000 * c_vk + c_vk / (2 * δ₀) + 1 with hCbigdef
  set CE : ℝ := (10 ^ 8 + 200 / c_vk) + (|C₀| + 1) with hCEdef
  set T₀ : ℝ := max (max T₁ 3) (Real.exp (Real.exp Cbig)) with hT₀def
  have hCE0 : 0 < CE := by rw [hCEdef]; positivity
  refine ⟨c_vk, CE, T₀, hc_vk0, hCE0, le_trans (le_max_right _ _) (le_max_left _ _), ?_, ?_⟩
  · -- the margin clause (used by RES/ASM)
    intro T hT ρ hρ0 hρim
    have hTT₁ : T₁ ≤ T + 1 / 5 := by
      have := le_trans (le_trans (le_max_left T₁ 3) (le_max_left _ _)) hT; linarith
    have h := (hmarg (T + 1 / 5) hTT₁).2 ρ hρ0
    rw [show 5 * (T + 1 / 5) = 5 * T + 1 by ring] at h
    exact h hρim
  · -- the strip bound
    intro T x γ hT hxlb hxub hγ5T
    have hTT₁ : T₁ ≤ T + 1 / 5 := by
      have := le_trans (le_trans (le_max_left T₁ 3) (le_max_left _ _)) hT; linarith
    have hTexp : Real.exp (Real.exp Cbig) ≤ T := le_trans (le_max_right _ _) hT
    have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hTexp
    have h5T1exp : Real.exp (Real.exp Cbig) ≤ 5 * T + 1 := by linarith [hTexp, hTpos]
    have ha5 : 0 < Real.log (5 * T + 1) :=
      lt_of_lt_of_le (Real.exp_pos _) (by
        rw [← Real.log_exp (Real.exp Cbig)]; exact Real.log_le_log (Real.exp_pos _) h5T1exp)
    have hlog5T1 : Real.exp Cbig ≤ Real.log (5 * T + 1) := by
      rw [← Real.log_exp (Real.exp Cbig)]; exact Real.log_le_log (Real.exp_pos _) h5T1exp
    have hloglog : Cbig ≤ Real.log (Real.log (5 * T + 1)) := by
      rw [← Real.log_exp Cbig]; exact Real.log_le_log (Real.exp_pos _) hlog5T1
    -- the reused margin fact at 5T+1
    have hmargT : ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)) := by
      intro ρ hρ0 hρim
      have h := (hmarg (T + 1 / 5) hTT₁).2 ρ hρ0
      rw [show 5 * (T + 1 / 5) = 5 * T + 1 by ring] at h
      exact h hρim
    -- the hsc threshold for the disc
    have hsc_thr : 9000 * c_vk ≤ Real.log (Real.log (5 * T + 1)) := by
      have hnn : (0:ℝ) ≤ c_vk / (2 * δ₀) := by positivity
      have hle : 9000 * c_vk ≤ Cbig := by rw [hCbigdef]; linarith [hnn]
      linarith [hle, hloglog]
    -- D₃(5T+1), D₄(5T+1) facts
    set LT : ℝ := Real.log (5 * T + 1) with hLTdef
    set ℓT : ℝ := Real.log LT with hℓTdef
    have hℓTge : (1:ℝ) ≤ ℓT := by
      have hnn : (0:ℝ) ≤ 9000 * c_vk + c_vk / (2 * δ₀) := by positivity
      have hle : (1:ℝ) ≤ Cbig := by rw [hCbigdef]; linarith [hnn]
      linarith [hle, hloglog]
    have hℓTpos : 0 < ℓT := by linarith [hℓTge]
    have hLTge : Real.exp 1 ≤ LT := by
      have h1 : Real.exp 1 ≤ Real.exp ℓT := Real.exp_le_exp.mpr hℓTge
      rwa [hℓTdef, Real.exp_log ha5] at h1
    have hLT1 : (1:ℝ) ≤ LT := le_trans (by linarith [Real.add_one_le_exp (1:ℝ)]) hLTge
    have hLTpos : 0 < LT := by linarith [hLT1]
    set D3T : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) with hD3Tdef
    have hLT34ge : (1:ℝ) ≤ LT ^ ((3 : ℝ) / 4) := Real.one_le_rpow hLT1 (by norm_num)
    have hℓT4ge : (1:ℝ) ≤ ℓT ^ (4 : ℕ) := one_le_pow₀ hℓTge
    have hD3Tpos : 0 < D3T := by rw [hD3Tdef]; positivity
    have hD4nn : (0:ℝ) ≤ LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ) :=
      mul_nonneg (Real.rpow_nonneg hLTpos.le _) (pow_nonneg hℓTpos.le _)
    have hD41 : (1:ℝ) ≤ LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ) := by nlinarith [hLT34ge, hℓT4ge]
    -- the δ₀ condition: (c_vk/2)/D₃(5T+1) ≤ δ₀
    have hδcond : (c_vk / 2) / D3T ≤ δ₀ := by
      have hbase : c_vk / (2 * δ₀) ≤ ℓT := by
        have hnn : (0:ℝ) ≤ 9000 * c_vk := by positivity
        have hle : c_vk / (2 * δ₀) ≤ Cbig := by rw [hCbigdef]; linarith [hnn]
        linarith [hle, hloglog]
      have hcube3 : ℓT ≤ ℓT ^ (3 : ℕ) := by
        have h2 : (1:ℝ) ≤ ℓT ^ (2:ℕ) := one_le_pow₀ hℓTge
        nlinarith [mul_le_mul_of_nonneg_left h2 hℓTpos.le]
      have hD3ge : c_vk / (2 * δ₀) ≤ D3T := by
        rw [hD3Tdef]
        calc c_vk / (2 * δ₀) ≤ ℓT ^ (3 : ℕ) := le_trans hbase hcube3
          _ = 1 * ℓT ^ (3 : ℕ) := (one_mul _).symm
          _ ≤ LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) :=
              mul_le_mul_of_nonneg_right hLT34ge (pow_nonneg hℓTpos.le _)
      have hδpos : 0 < 2 * δ₀ := by linarith [hδ₀0]
      rw [div_le_iff₀ hδpos] at hD3ge
      rw [div_le_iff₀ hD3Tpos]
      nlinarith [hD3ge, hδ₀0, hD3Tpos]
    -- the strip's upper endpoint: (c_vk/2)/D₃(5T+1) ≤ 1, so 1+w ≤ 2
    have hwle1 : (c_vk / 2) / D3T ≤ 1 := by
      rw [div_le_one hD3Tpos]
      have hchalf : c_vk / 2 ≤ ℓT := by linarith [hsc_thr, hc_vk0]
      have hcube3 : ℓT ≤ ℓT ^ (3 : ℕ) := by
        have h2 : (1:ℝ) ≤ ℓT ^ (2:ℕ) := one_le_pow₀ hℓTge
        nlinarith [mul_le_mul_of_nonneg_left h2 hℓTpos.le]
      have hD3ge : ℓT ^ (3 : ℕ) ≤ D3T := by
        rw [hD3Tdef]
        calc ℓT ^ (3 : ℕ) = 1 * ℓT ^ (3 : ℕ) := (one_mul _).symm
          _ ≤ LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) :=
              mul_le_mul_of_nonneg_right hLT34ge (pow_nonneg hℓTpos.le _)
      linarith [hchalf, hcube3, hD3ge]
    -- case split on |γ| vs H
    by_cases hcase : H ≤ |γ|
    · -- high height: disc-core-gen (+ conjugation for γ < 0)
      by_cases hsign : (0:ℝ) ≤ γ
      · have hγH : H ≤ γ := by rwa [abs_of_nonneg hsign] at hcase
        have hγT5 : γ ≤ 5 * T := by rwa [abs_of_nonneg hsign] at hγ5T
        have hbound := shifted_edge_disc_core_gen (T := T) (x := x) hK ht₀K hg hc_vk0 hxlb hxub
          (by rw [hHdef] at hγH; exact hγH) hγT5 hsc_thr hmargT
        rw [← hLTdef, ← hℓTdef] at hbound
        refine le_trans hbound ?_
        exact mul_le_mul_of_nonneg_right (by rw [hCEdef]; linarith [abs_nonneg C₀]) hD4nn
      · have hsignlt : γ < 0 := not_le.mp hsign
        have hγH : H ≤ -γ := by rw [abs_of_neg hsignlt] at hcase; exact hcase
        have hγT5 : -γ ≤ 5 * T := by rw [abs_of_neg hsignlt] at hγ5T; exact hγ5T
        have hbound := shifted_edge_disc_core_gen (T := T) (x := x) hK ht₀K hg hc_vk0 hxlb hxub
          (by rw [hHdef] at hγH; exact hγH) hγT5 hsc_thr hmargT
        rw [← hLTdef, ← hℓTdef] at hbound
        have hconj : (x : ℂ) + (γ : ℂ) * Complex.I
            = (starRingEnd ℂ) ((x : ℂ) + ((-γ : ℝ) : ℂ) * Complex.I) := by
          rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
          push_cast; ring
        rw [hconj, logDeriv_Zc_norm_conj]
        refine le_trans hbound ?_
        exact mul_le_mul_of_nonneg_right (by rw [hCEdef]; linarith [abs_nonneg C₀]) hD4nn
    · -- moderate height: the compact bound
      rw [not_le] at hcase
      set z : ℂ := (x : ℂ) + (γ : ℂ) * Complex.I with hzdef
      have hzre : z.re = x := by rw [hzdef]; simp
      have hzim : z.im = γ := by rw [hzdef]; simp
      have hσ₀ge : 1 - δ₀ ≤ z.re := by rw [hzre]; linarith [hδcond, hxlb]
      have hσ₀le : z.re ≤ 2 := by rw [hzre]; linarith [hwle1, hxub]
      have himle : |z.im| ≤ H := by rw [hzim]; exact le_of_lt hcase
      have hcptb := hcpt z hσ₀ge hσ₀le himle
      refine le_trans hcptb ?_
      calc C₀ ≤ |C₀| := le_abs_self _
        _ ≤ CE := by
          rw [hCEdef]
          have h200 : (0:ℝ) ≤ 200 / c_vk := by positivity
          linarith [h200]
        _ = CE * 1 := (mul_one _).symm
        _ ≤ CE * (LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ)) :=
            mul_le_mul_of_nonneg_left hD41 hCE0.le

set_option maxHeartbeats 12800000 in
-- The full contour assembly (four sub-bounds + orientation glue) is heavy; the disc-core-grade
-- 12.8M budget is warranted for the whole-theorem elaboration.
theorem per_pair_contour :
    ∃ (c_vk C₁ C₂ C₃ T₀ : ℝ), 0 < c_vk ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 3 ≤ T₀ ∧
      ∀ (T P u : ℝ), T₀ ≤ T → 2 ≤ P → |u| ≤ 2 * T →
        ‖(∑' n, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
              - windowKernel P 1 u‖
          ≤ C₁ * P * Real.exp (-(c_vk / 2) * Real.log P
                / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                    * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)))
              * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                  * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ))
            + C₂ * P * Real.log P / T
            + C₃ * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                  * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) * P / T ^ 2 := by
  obtain ⟨c_vk, CE, T₀s, hc_vk0, hCE0, hT₀s3, hmargin, hstrip⟩ := shifted_edge_price_strip
  obtain ⟨C₀, hC₀0, hcline⟩ := sum_vonMangoldt_cline_bound
  -- constants
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set Kc : ℝ := (2 * 9 * (3 : ℝ) ^ ((Real.log 2)⁻¹) + 4) * Real.exp 1 with hKcdef
  have hKcpos : 0 < Kc := by rw [hKcdef]; positivity
  set Cζ : ℝ := 2 / c_vk + CE + 1 with hCζdef
  have hCζpos : 0 < Cζ := by rw [hCζdef]; positivity
  set CL : ℝ := 44 * Real.pi * (2 / c_vk + CE) with hCLdef
  have hCLpos : 0 < CL := by rw [hCLdef]; positivity
  set CH : ℝ := Cζ * Kc * (1 / Real.log 2 + 1 / 2) / 9 with hCHdef
  have hCHpos : 0 < CH := by rw [hCHdef]; positivity
  set CT : ℝ := 2 / 3 * Kc * (1 + C₀ / Real.log 2) with hCTdef
  have hCTpos : 0 < CT := by rw [hCTdef]; positivity
  refine ⟨c_vk, CL / (2 * Real.pi), CT / (2 * Real.pi), 2 * CH / (2 * Real.pi),
    max (max T₀s 3) (Real.exp (Real.exp (c_vk + 1))), hc_vk0,
    div_pos hCLpos (by positivity), div_pos hCTpos (by positivity),
    div_pos (by positivity) (by positivity), ?_, ?_⟩
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  intro T P u hT hP hu
  -- unpack the T-threshold
  have hTT₀s : T₀s ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTexp : Real.exp (Real.exp (c_vk + 1)) ≤ T := le_trans (le_max_right _ _) hT
  have hT3 : (3 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hP0 : (0 : ℝ) < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  -- abbreviations D3, D4, w, σ₀, c, T'
  set LT : ℝ := Real.log (5 * T + 1) with hLTdef
  set ℓT : ℝ := Real.log LT with hℓTdef
  set D3 : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) with hD3def
  set D4 : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ) with hD4def
  have h5T1 : (1 : ℝ) < 5 * T + 1 := by linarith
  have hLTpos : 0 < LT := Real.log_pos h5T1
  -- loglog bound from the threshold
  have hTlogexp : Real.exp (c_vk + 1) ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp (c_vk + 1))]; exact Real.log_le_log (Real.exp_pos _) hTexp
  have hLTge : Real.exp (c_vk + 1) ≤ LT := by
    rw [hLTdef]; exact le_trans hTlogexp (Real.log_le_log hT0 (by linarith))
  have hℓTge : c_vk + 1 ≤ ℓT := by
    rw [hℓTdef, ← Real.log_exp (c_vk + 1)]; exact Real.log_le_log (Real.exp_pos _) hLTge
  have hℓT1 : (1 : ℝ) ≤ ℓT := by linarith
  have hℓTpos : 0 < ℓT := by linarith
  have hD3pos : 0 < D3 := by rw [hD3def]; positivity
  have hD4pos : 0 < D4 := by rw [hD4def]; positivity
  set w : ℝ := (c_vk / 2) / D3 with hwdef
  have hw0 : 0 < w := by rw [hwdef]; positivity
  -- D3 ≥ c_vk (so w ≤ 1/2, σ₀ ≥ 1/2)
  have hLT34ge : (1 : ℝ) ≤ LT ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow (by linarith [hLTge, Real.exp_pos (c_vk+1), Real.add_one_le_exp (c_vk+1)])
      (by norm_num)
  have hℓT3ge : c_vk ≤ ℓT ^ (3 : ℕ) := by
    have : c_vk + 1 ≤ ℓT ^ (3 : ℕ) := by
      calc c_vk + 1 ≤ ℓT := hℓTge
        _ = ℓT ^ 1 := (pow_one _).symm
        _ ≤ ℓT ^ (3 : ℕ) := pow_le_pow_right₀ hℓT1 (by norm_num)
    linarith
  have hD3gecvk : c_vk ≤ D3 := by
    rw [hD3def]
    calc c_vk ≤ ℓT ^ (3 : ℕ) := hℓT3ge
      _ = 1 * ℓT ^ (3 : ℕ) := (one_mul _).symm
      _ ≤ LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) := by
          apply mul_le_mul_of_nonneg_right hLT34ge (by positivity)
  have hwle : w ≤ 1 / 2 := by
    rw [hwdef, div_le_div_iff₀ hD3pos (by norm_num)]; nlinarith [hD3gecvk, hc_vk0]
  set σ₀ : ℝ := 1 - w with hσ₀def
  have hσ₀_eq : σ₀ = 1 - (c_vk / 2) / D3 := by rw [hσ₀def, hwdef]
  have hσ₀half : (1 : ℝ) / 2 ≤ σ₀ := by rw [hσ₀def]; linarith
  have hσ₀0 : 0 < σ₀ := by linarith
  have hσ₀1 : σ₀ < 1 := by rw [hσ₀def]; linarith
  have hσ₀xlb : 1 - (c_vk / 2) / D3 ≤ σ₀ := le_of_eq hσ₀_eq.symm
  have hσ₀xub : σ₀ ≤ 1 + (c_vk / 2) / D3 := by
    rw [hσ₀_eq]
    have hpos : (0 : ℝ) < (c_vk / 2) / D3 := by positivity
    linarith
  set c : ℝ := 1 + (Real.log P)⁻¹ with hcdef
  have hc1 : 1 < c := by rw [hcdef]; have := inv_pos.mpr hlogP; linarith
  have hcpos : 0 < c := by linarith
  set Tp : ℝ := 3 * T with hTpdef
  have hTp0 : 0 < Tp := by rw [hTpdef]; linarith
  have huTp : |u| < Tp := by rw [hTpdef]; linarith [hu, abs_nonneg u]
  -- the contour integrand F
  set F : ℂ → ℂ := fun s => (- logDeriv riemannZeta (s - (u : ℂ) * I)) * windowMellin P s with hFdef
  -- the rectangle corners
  set zc : ℂ := (σ₀ : ℂ) + ((-Tp : ℝ) : ℂ) * I with hzc
  set wc : ℂ := (c : ℂ) + (Tp : ℂ) * I with hwc
  have hzc_re : zc.re = σ₀ := by rw [hzc]; simp
  have hzc_im : zc.im = -Tp := by rw [hzc]; simp
  have hwc_re : wc.re = c := by rw [hwc]; simp
  have hwc_im : wc.im = Tp := by rw [hwc]; simp
  -- ζ zero-freeness on the shifted rectangle
  have hzf : ∀ s : ℂ, s ∈ closedRect zc wc → riemannZeta (s - (u : ℂ) * I) ≠ 0 := by
    intro s hs
    rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm,
      Set.uIcc_of_le (by linarith : σ₀ ≤ c),
      Set.uIcc_of_le (by linarith : -Tp ≤ Tp)] at hs
    obtain ⟨hsre, hsim⟩ := hs
    simp only [Set.mem_Icc] at hsre hsim
    have hshim : |(s - (u : ℂ) * I).im| ≤ 5 * T + 1 := by
      have him : (s - (u : ℂ) * I).im = s.im - u := by simp
      have hb := abs_le.mp hu
      rw [hTpdef] at hsim
      rw [him, abs_le]
      constructor <;> nlinarith [hsim.1, hsim.2, hb.1, hb.2]
    intro hz0
    by_cases h1 : (1 : ℝ) ≤ (s - (u : ℂ) * I).re
    · exact riemannZeta_ne_zero_of_one_le_re h1 hz0
    · have hsre' : (s - (u : ℂ) * I).re = s.re := by simp
      have hmr := hmargin T hTT₀s (s - (u : ℂ) * I) hz0 hshim
      rw [hsre'] at hmr
      have : s.re < 1 := by rw [hsre'] at h1; linarith [not_le.mp h1]
      have hlt : (c_vk / 2) / D3 < c_vk / D3 := by
        rw [div_lt_div_iff₀ hD3pos hD3pos]; nlinarith [hc_vk0, hD3pos]
      rw [← hD3def] at hmr
      have : σ₀ ≤ s.re := hsre.1
      rw [hσ₀def, hwdef] at this
      linarith [hmr, hlt]
  -- pole residue term
  have hpr0 := pole_residue_term (P := P) (σ₀ := σ₀) (c := c) (u := u) (T' := Tp)
    hP0 hσ₀0 hσ₀1 hc1 huTp hzf
  -- the four edges
  set BOT : ℂ := ∫ x in σ₀..c, F ((x : ℂ) + ((-Tp : ℝ) : ℂ) * I) with hBOTdef
  set TOP : ℂ := ∫ x in σ₀..c, F ((x : ℂ) + (Tp : ℂ) * I) with hTOPdef
  set RIGHT : ℂ := ∫ v in (-Tp)..Tp, F ((c : ℂ) + (v : ℂ) * I) with hRIGHTdef
  set LEFT : ℂ := ∫ v in (-Tp)..Tp, F ((σ₀ : ℂ) + (v : ℂ) * I) with hLEFTdef
  set wK : ℂ := windowKernel P 1 u with hwKdef
  have hwM : windowMellin P ((1 : ℂ) + (u : ℂ) * I) = wK := by
    rw [hwKdef, windowKernel_eq_windowMellin]; norm_num
  rw [hwM] at hpr0
  -- unfold rectBI to the four edges
  have hunf : rectBI zc wc F = BOT - TOP + I * RIGHT - I * LEFT := by
    rw [rectBI, hzc_re, hzc_im, hwc_re, hwc_im, hBOTdef, hTOPdef, hRIGHTdef, hLEFTdef]
  rw [hunf] at hpr0
  -- hpr0 : BOT - TOP + I * RIGHT - I * LEFT = 2 * ↑π * I * wK
  -- residue rearrangement
  have hrearr : RIGHT - (2 * (Real.pi : ℂ)) * wK = LEFT - I * (TOP - BOT) := by
    have key : I * (RIGHT - (2 * (Real.pi : ℂ)) * wK) = I * (LEFT - I * (TOP - BOT)) := by
      have expand : I * (LEFT - I * (TOP - BOT)) = I * LEFT + (TOP - BOT) := by
        have hII : I * (I * (TOP - BOT)) = -(TOP - BOT) := by
          rw [← mul_assoc, Complex.I_mul_I]; ring
        rw [mul_sub, hII]; ring
      rw [expand]; linear_combination hpr0
    exact mul_left_cancel₀ Complex.I_ne_zero key
  -- the REP bridge
  set a : ℕ → ℂ := fun n => (vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I) with hadef
  have ha0 : a 0 = 0 := by rw [hadef]; simp
  have hnorm_a : ∀ n : ℕ, ‖a n‖ = vonMangoldt n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ha0]; simp
    · rw [hadef]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      rw [← Complex.ofReal_natCast (n := n),
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
      simp
  have hsum : Summable (fun n => ‖a n‖ / (n : ℝ) ^ c) := by
    refine (summable_vonMangoldt_div_rpow hc1).congr (fun n => ?_)
    rw [hnorm_a n]
  -- Dirichlet ↔ ζ conversion (per t)
  have hdir : ∀ v : ℝ, (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
      = - logDeriv riemannZeta ((c : ℂ) + (v : ℂ) * I - (u : ℂ) * I) := by
    intro v
    set wv : ℂ := (c : ℂ) + (v : ℂ) * I - (u : ℂ) * I with hwvdef
    have hwvre : 1 < wv.re := by rw [hwvdef]; simp; linarith
    have hterm : ∀ n : ℕ, a n / (n : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)
        = LSeries.term ↗vonMangoldt wv n := by
      intro n
      rw [LSeries.term_def₀ (by simp) wv n]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [ha0]; simp
      · have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
        rw [hadef]; simp only; rw [mul_div_assoc]; congr 1
        rw [div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hne]
        congr 1; rw [hwvdef]; ring
    have hLSeries : (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)) = LSeries ↗vonMangoldt wv :=
      tsum_congr hterm
    rw [hLSeries, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hwvre, logDeriv_apply, neg_div]
  -- F(c+vI) equals the Dirichlet integrand
  have hFdir : ∀ v : ℝ, F ((c : ℂ) + (v : ℂ) * I)
      = (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)) * windowKernel P c v := by
    intro v
    rw [hFdef, hdir v, windowKernel_eq_windowMellin]
  -- the bridge
  have hbridge : (∑' n, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
      = (1 / (2 * Real.pi)) • ∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I) := by
    rw [show (∑' n, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
        = ∑' n, a n * (primeWindow P n : ℂ) from rfl,
      primeWindow_contour_rep a ha0 hP hcpos hsum]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    exact (hFdir v).symm
  -- truncation via rep_truncated
  have htrunc := rep_truncated a ha0 hP hcpos hTp0 hsum
  -- identify the two integrals in htrunc with ∫F and RIGHT
  have hI1 : (∫ t : ℝ, (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * windowKernel P c t)
      = ∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_)); exact (hFdir v).symm
  have hI2 : (∫ t in Set.Icc (-Tp) Tp,
        (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * windowKernel P c t) = RIGHT := by
    rw [hRIGHTdef, intervalIntegral.integral_of_le (by linarith : (-Tp : ℝ) ≤ Tp),
      ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc (fun v _ => ?_); exact (hFdir v).symm
  rw [hI1, hI2] at htrunc
  set TAILval : ℂ := (∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I)) - RIGHT with hTAILdef
  have hInt_split : (∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I)) = RIGHT + TAILval := by
    rw [hTAILdef]; ring
  -- htrunc : ‖TAILval‖ ≤ tailbound  (after rewriting)
  have hTAILnorm : ‖TAILval‖ ≤ (∑' n, ‖a n‖ / (n : ℝ) ^ c)
      * (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2)) * (2 / Tp) := by
    rw [hTAILdef]; exact htrunc
  -- SUB-BOUNDS (to be proven)
  have hLEFTb : ‖LEFT‖
      ≤ CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4 := by
    have hPσ0nn : (0 : ℝ) ≤ (P : ℝ) ^ σ₀ := Real.rpow_nonneg hP0.le σ₀
    have hPσ₀ : (P : ℝ) ^ σ₀ = P * Real.exp (-(c_vk / 2) * Real.log P / D3) := by
      rw [Real.rpow_def_of_pos hP0, hσ₀_eq,
        show Real.log P * (1 - (c_vk / 2) / D3)
          = Real.log P + (-(c_vk / 2) * Real.log P / D3) by ring, Real.exp_add]
      congr 1; exact Real.exp_log hP0
    set Bσ : ℝ := 1 / w + CE * D4 with hBσdef
    have hBσ0 : 0 ≤ Bσ := by rw [hBσdef]; positivity
    -- kernel bound
    have hkerL : ∀ v : ℝ, ‖windowMellin P ((σ₀ : ℂ) + (v : ℂ) * I)‖
        ≤ 22 * (P : ℝ) ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
      intro v
      rw [← windowKernel_eq_windowMellin]
      refine le_trans (norm_windowKernel_le hP hσ₀0 v) ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h3Pσ : ((3 : ℝ) * P) ^ (σ₀ + 1) = (3 : ℝ) ^ (σ₀ + 1) * (P : ℝ) ^ (σ₀ + 1) :=
        Real.mul_rpow (by norm_num) hP0.le
      have hPσ1 : (P : ℝ) ^ (σ₀ + 1) = (P : ℝ) ^ σ₀ * P := by
        rw [Real.rpow_add hP0, Real.rpow_one]
      have e1 : 2 * (2 * P + P) ^ (σ₀ + 1) / P = 2 * (3 : ℝ) ^ (σ₀ + 1) * (P : ℝ) ^ σ₀ := by
        rw [show 2 * P + P = 3 * P by ring, h3Pσ, hPσ1]; field_simp
      have e2 : 2 * (P / 2 + P / 2) ^ (σ₀ + 1) / (P / 2) = 4 * (P : ℝ) ^ σ₀ := by
        rw [show P / 2 + P / 2 = P by ring, hPσ1]; field_simp; ring
      rw [e1, e2]
      have h3 : (3 : ℝ) ^ (σ₀ + 1) ≤ 9 := by
        rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hσ₀1])
      nlinarith [h3, hPσ0nn]
    -- ζ'/ζ bound on the left edge
    have hzetaL : ∀ v : ℝ, v ∈ Set.Icc (-Tp) Tp →
        ‖(- logDeriv riemannZeta (((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I))‖ ≤ Bσ := by
      intro v hv
      simp only [Set.mem_Icc] at hv
      set s' : ℂ := ((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I with hs'def
      have hs'eq : s' = (σ₀ : ℂ) + ((v - u : ℝ) : ℂ) * I := by rw [hs'def]; push_cast; ring
      have hs're : s'.re = σ₀ := by rw [hs'eq]; simp
      have hvu5T : |v - u| ≤ 5 * T := by
        have hb := abs_le.mp hu; rw [hTpdef] at hv; rw [abs_le]; constructor <;> nlinarith [hv.1, hv.2, hb.1, hb.2]
      have hmem : ((σ₀ : ℂ) + (v : ℂ) * I) ∈ closedRect zc wc := by
        rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm,
          Set.uIcc_of_le (by linarith : σ₀ ≤ c), Set.uIcc_of_le (by linarith : -Tp ≤ Tp)]
        refine ⟨?_, ?_⟩
        · rw [Set.mem_Icc]; exact ⟨by simp, by simp; linarith [hσ₀1]⟩
        · rw [Set.mem_Icc]; simp; exact ⟨hv.1, hv.2⟩
      have hζs' : riemannZeta s' ≠ 0 := hzf _ hmem
      have hs'ne1 : s' ≠ 1 := by
        intro h; rw [h] at hs're; simp at hs're; linarith [hσ₀1]
      have hsplit : (- logDeriv riemannZeta s') = 1 / (s' - 1) - logDeriv Zc s' := by
        rw [logDeriv_zeta_eq hs'ne1 hζs']; ring
      rw [hsplit]
      refine le_trans (norm_sub_le _ _) ?_
      have hpole : ‖(1 : ℂ) / (s' - 1)‖ ≤ 1 / w := by
        rw [norm_div, norm_one]
        have hge : w ≤ ‖s' - 1‖ := by
          have h := Complex.abs_re_le_norm (s' - 1)
          rw [Complex.sub_re, hs're, Complex.one_re,
            show σ₀ - 1 = -w by rw [hσ₀def]; ring, abs_neg, abs_of_pos hw0] at h
          exact h
        exact one_div_le_one_div_of_le hw0 hge
      have hZc : ‖logDeriv Zc s'‖ ≤ CE * D4 := by
        rw [hs'eq]
        have h := hstrip T σ₀ (v - u) hTT₀s hσ₀xlb hσ₀xub hvu5T
        rw [← hLTdef, ← hℓTdef, ← hD4def] at h
        exact h
      rw [hBσdef]; linarith [hpole, hZc]
    -- pointwise ‖F‖ bound and the integral
    have hg_int : Integrable (fun v : ℝ => Bσ * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹) :=
      (Salt.SW.integrable_inv_c_sq_add_sq hσ₀0).const_mul _
    have hgnn : ∀ v : ℝ, (0 : ℝ) ≤ Bσ * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
      fun v => by positivity
    have hpt : ∀ v ∈ Set.Icc (-Tp) Tp,
        ‖F ((σ₀ : ℂ) + (v : ℂ) * I)‖ ≤ Bσ * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
      intro v hv
      rw [hFdef]
      simp only
      rw [norm_mul]
      calc ‖(- logDeriv riemannZeta (((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I))‖
              * ‖windowMellin P ((σ₀ : ℂ) + (v : ℂ) * I)‖
          ≤ Bσ * (22 * (P : ℝ) ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹) :=
            mul_le_mul (hzetaL v hv) (hkerL v) (norm_nonneg _) hBσ0
        _ = Bσ * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by ring
    have hFleft_ii : IntervalIntegrable (fun v : ℝ => F ((σ₀ : ℂ) + (v : ℂ) * I)) volume (-Tp) Tp := by
      have hζAON : AnalyticOnNhd ℂ riemannZeta (({(1 : ℂ)} : Set ℂ)ᶜ) := by
        apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
        intro z hz; exact (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
      apply ContinuousOn.intervalIntegrable
      intro v hv
      rw [Set.uIcc_of_le (by linarith : (-Tp : ℝ) ≤ Tp), Set.mem_Icc] at hv
      have hs0mem : ((σ₀ : ℂ) + (v : ℂ) * I) ∈ closedRect zc wc := by
        rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm,
          Set.uIcc_of_le (by linarith : σ₀ ≤ c), Set.uIcc_of_le (by linarith : (-Tp : ℝ) ≤ Tp)]
        refine ⟨?_, ?_⟩
        · rw [Set.mem_Icc]; exact ⟨by simp, by simp; linarith [hσ₀1]⟩
        · rw [Set.mem_Icc]; simp; exact hv
      have hs0re : ((σ₀ : ℂ) + (v : ℂ) * I).re = σ₀ := by simp
      have hζ : riemannZeta (((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I) ≠ 0 := hzf _ hs0mem
      have hne1 : ((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I ≠ 1 := by
        intro h; have hre := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, mul_zero, mul_one, sub_zero,
          add_zero] at hre
        linarith [hσ₀1]
      have hw_mem : (((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I) ∈ (({(1 : ℂ)} : Set ℂ)ᶜ) := by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hne1
      have hlogDζ : AnalyticAt ℂ (logDeriv riemannZeta) (((σ₀ : ℂ) + (v : ℂ) * I) - (u : ℂ) * I) := by
        rw [show logDeriv riemannZeta = fun z => deriv riemannZeta z / riemannZeta z from rfl]
        exact (hζAON.deriv _ hw_mem).div (hζAON _ hw_mem) hζ
      have hldζ : DifferentiableAt ℂ
          (fun z => - logDeriv riemannZeta (z - (u : ℂ) * I)) ((σ₀ : ℂ) + (v : ℂ) * I) := by
        have hg : DifferentiableAt ℂ (fun z : ℂ => z - (u : ℂ) * I) ((σ₀ : ℂ) + (v : ℂ) * I) := by
          fun_prop
        exact (DifferentiableAt.comp ((σ₀ : ℂ) + (v : ℂ) * I) (hlogDζ.differentiableAt) hg).neg
      have hWM : DifferentiableAt ℂ (windowMellin P) ((σ₀ : ℂ) + (v : ℂ) * I) := by
        apply windowMellin_differentiableAt hP0
        · intro h; rw [h] at hs0re; simp at hs0re; linarith [hσ₀0]
        · intro h; have hre : (((σ₀ : ℂ) + (v : ℂ) * I) + 1).re = 0 := by rw [h]; simp
          rw [Complex.add_re, Complex.one_re, hs0re] at hre; linarith [hσ₀0]
      have hFdiffC : DifferentiableAt ℂ F ((σ₀ : ℂ) + (v : ℂ) * I) := by
        rw [hFdef]; exact hldζ.mul hWM
      have hgdiff : DifferentiableAt ℝ (fun v : ℝ => (σ₀ : ℂ) + (v : ℂ) * I) v := by
        apply DifferentiableAt.const_add
        exact (Complex.ofRealCLM.differentiable.differentiableAt).mul_const I
      exact (((hFdiffC.restrictScalars ℝ).comp v hgdiff).continuousAt).continuousWithinAt
    calc ‖LEFT‖
        = ‖∫ v in (-Tp)..Tp, F ((σ₀ : ℂ) + (v : ℂ) * I)‖ := by rw [hLEFTdef]
      _ ≤ ∫ v in (-Tp)..Tp, ‖F ((σ₀ : ℂ) + (v : ℂ) * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ v in (-Tp)..Tp, Bσ * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
          intervalIntegral.integral_mono_on (by linarith) hFleft_ii.norm
            hg_int.intervalIntegrable hpt
      _ ≤ ∫ v : ℝ, Bσ * (22 * (P : ℝ) ^ σ₀) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
          rw [intervalIntegral.integral_of_le (by linarith : (-Tp : ℝ) ≤ Tp)]
          exact setIntegral_le_integral hg_int (Filter.Eventually.of_forall hgnn)
      _ = Bσ * (22 * (P : ℝ) ^ σ₀) * (Real.pi / σ₀) := by
          rw [MeasureTheory.integral_const_mul, Salt.SW.integral_inv_sq_add hσ₀0]
      _ ≤ CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4 := by
          have hD3leD4 : D3 ≤ D4 := by
            rw [hD3def, hD4def]
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hLTpos.le _)
            exact pow_le_pow_right₀ hℓT1 (by norm_num)
          have hBσle : Bσ ≤ (2 / c_vk + CE) * D4 := by
            rw [hBσdef, add_mul]
            have he : (1 : ℝ) / w = 2 * D3 / c_vk := by rw [hwdef, one_div_div]; ring
            have h1 : (1 : ℝ) / w ≤ 2 / c_vk * D4 := by
              rw [he, show (2 : ℝ) / c_vk * D4 = 2 * D4 / c_vk by ring,
                div_le_div_iff₀ hc_vk0 hc_vk0]
              nlinarith [hD3leD4, hc_vk0]
            linarith [h1]
          have hπσ₀ : Real.pi / σ₀ ≤ 2 * Real.pi := by
            rw [div_le_iff₀ hσ₀0]; nlinarith [Real.pi_pos, hσ₀half]
          have hexpnn : (0 : ℝ) ≤ Real.exp (-(c_vk / 2) * Real.log P / D3) := (Real.exp_pos _).le
          rw [hPσ₀]
          have hfac_nn : (0 : ℝ) ≤ 22 * (P * Real.exp (-(c_vk / 2) * Real.log P / D3)) := by
            apply mul_nonneg (by norm_num); exact mul_nonneg hP0.le hexpnn
          have hD4nn : (0 : ℝ) ≤ D4 := hD4pos.le
          have hCEfac_nn : (0 : ℝ) ≤ (2 / c_vk + CE) * D4 :=
            mul_nonneg (by positivity) hD4nn
          calc Bσ * (22 * (P * Real.exp (-(c_vk / 2) * Real.log P / D3))) * (Real.pi / σ₀)
              ≤ ((2 / c_vk + CE) * D4) * (22 * (P * Real.exp (-(c_vk / 2) * Real.log P / D3)))
                  * (2 * Real.pi) := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right hBσle hfac_nn) hπσ₀
                  (div_nonneg Real.pi_pos.le hσ₀0.le)
                  (mul_nonneg hCEfac_nn hfac_nn)
            _ = CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4 := by rw [hCLdef]; ring
  -- === HORIZONTAL sub-bound infrastructure ===
  have hD41 : (1 : ℝ) ≤ D4 := by
    rw [hD4def]; nlinarith [hLT34ge, one_le_pow₀ hℓT1 (n := 4), Real.rpow_nonneg hLTpos.le ((3:ℝ)/4)]
  have hTle : (1 : ℝ) ≤ T := by linarith [hT3]
  have hD3leD4' : D3 ≤ D4 := by
    rw [hD3def, hD4def]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hLTpos.le _)
    exact pow_le_pow_right₀ hℓT1 (by norm_num)
  have h1w_inv : (1 : ℝ) / w ≤ 2 / c_vk * D4 := by
    have he : (1 : ℝ) / w = 2 * D3 / c_vk := by rw [hwdef, one_div_div]; ring
    rw [he, show (2 : ℝ) / c_vk * D4 = 2 * D4 / c_vk by ring, div_le_div_iff₀ hc_vk0 hc_vk0]
    nlinarith [hD3leD4', hc_vk0]
  -- ζ'/ζ bound on both horizontals
  have hζhoriz : ∀ x τ : ℝ, σ₀ ≤ x → x ≤ c → |τ| = Tp →
      ‖(- logDeriv riemannZeta (((x : ℂ) + (τ : ℂ) * I) - (u : ℂ) * I))‖ ≤ Cζ * D4 := by
    intro x τ hxl hxu hτ
    set s' : ℂ := ((x : ℂ) + (τ : ℂ) * I) - (u : ℂ) * I with hs'def
    have hs'eq : s' = (x : ℂ) + ((τ - u : ℝ) : ℂ) * I := by rw [hs'def]; push_cast; ring
    have hs're : s'.re = x := by rw [hs'eq]; simp
    have hs'im : s'.im = τ - u := by rw [hs'eq]; simp
    have hτuge : (T : ℝ) ≤ |τ - u| := by
      have h1 : |τ| - |u| ≤ |τ - u| := abs_sub_abs_le_abs_sub τ u
      rw [hτ, hTpdef] at h1
      linarith [hu]
    have hτule : |τ - u| ≤ 5 * T := by
      have hb := abs_le.mp hu
      rw [abs_le]; rw [abs_eq (by linarith [hTp0] : (0:ℝ) ≤ Tp)] at hτ
      rcases hτ with h | h <;> rw [hTpdef] at h <;> constructor <;> nlinarith [hb.1, hb.2]
    by_cases hx1w : x ≤ 1 + w
    · have hmem : ((x : ℂ) + (τ : ℂ) * I) ∈ closedRect zc wc := by
        rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm,
          Set.uIcc_of_le (by linarith : σ₀ ≤ c), Set.uIcc_of_le (by linarith : -Tp ≤ Tp)]
        refine ⟨?_, ?_⟩
        · rw [Set.mem_Icc]; exact ⟨by simp; linarith, by simp; linarith⟩
        · rw [Set.mem_Icc]
          rw [abs_eq (by linarith [hTp0] : (0:ℝ) ≤ Tp)] at hτ
          rcases hτ with h | h <;> simp <;> constructor <;> linarith
      have hζs' : riemannZeta s' ≠ 0 := hzf _ hmem
      have hs'ne1 : s' ≠ 1 := by
        intro h; have := congrArg Complex.im h; rw [hs'im] at this; simp at this
        rw [this] at hτuge; simp at hτuge; linarith [hTle]
      have hsplit : (- logDeriv riemannZeta s') = 1 / (s' - 1) - logDeriv Zc s' := by
        rw [logDeriv_zeta_eq hs'ne1 hζs']; ring
      rw [hsplit]
      refine le_trans (norm_sub_le _ _) ?_
      have hpole : ‖(1 : ℂ) / (s' - 1)‖ ≤ 1 / T := by
        rw [norm_div, norm_one]
        have hge : T ≤ ‖s' - 1‖ := by
          have h := Complex.abs_im_le_norm (s' - 1)
          rw [Complex.sub_im, hs'im, Complex.one_im, sub_zero] at h
          linarith [h, hτuge, le_abs_self (τ - u), neg_abs_le (τ - u)]
        exact one_div_le_one_div_of_le hT0 hge
      have hZc : ‖logDeriv Zc s'‖ ≤ CE * D4 := by
        rw [hs'eq]
        have h := hstrip T x (τ - u) hTT₀s (le_trans hσ₀xlb hxl)
          (by rw [← hwdef]; exact hx1w) hτule
        rw [← hLTdef, ← hℓTdef, ← hD4def] at h
        exact h
      have hTinv : (1 : ℝ) / T ≤ D4 := le_trans (by rw [div_le_one hT0]; linarith [hTle]) hD41
      have hchain : ‖(1 : ℂ) / (s' - 1)‖ ≤ D4 := le_trans hpole hTinv
      have h2cD4 : (0 : ℝ) ≤ 2 / c_vk * D4 := mul_nonneg (by positivity) hD4pos.le
      rw [hCζdef, show (2 / c_vk + CE + 1) * D4 = 2 / c_vk * D4 + CE * D4 + D4 by ring]
      linarith [hchain, hZc, h2cD4]
    · rw [not_le] at hx1w
      have hx1 : (1 : ℝ) < x := by linarith [hw0]
      rw [norm_neg]
      have hcl := norm_logDeriv_zeta_cline_le hx1 (τ - u)
      have hmatch : ((x : ℂ) + ((τ - u : ℝ) : ℂ) * I) = s' := hs'eq.symm
      rw [hmatch] at hcl
      -- Σ Λ/n^x ≤ Σ Λ/n^{1+w}
      have h1w1 : (1 : ℝ) < 1 + w := by linarith [hw0]
      have hmono : (∑' n, vonMangoldt n / (n : ℝ) ^ x)
          ≤ ∑' n, vonMangoldt n / (n : ℝ) ^ (1 + w) := by
        refine (summable_vonMangoldt_div_rpow hx1).tsum_le_tsum (fun n => ?_)
          (summable_vonMangoldt_div_rpow h1w1)
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · have hle : (n : ℝ) ^ (1 + w) ≤ (n : ℝ) ^ x :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
          exact div_le_div_of_nonneg_left vonMangoldt_nonneg
            (Real.rpow_pos_of_pos (by exact_mod_cast hn) _) hle
      have hpole1w := sum_vonMangoldt_le_pole_add_Zc h1w1
      have hZc1w : ‖logDeriv Zc ((1 + w : ℝ) : ℂ)‖ ≤ CE * D4 := by
        have h := hstrip T (1 + w) 0 hTT₀s
          (by rw [← hwdef]; linarith [hw0]) (by rw [← hwdef])
          (by rw [abs_zero]; linarith [hT0])
        rw [← hLTdef, ← hℓTdef, ← hD4def] at h
        simpa using h
      have hpole1w2 : (1 : ℝ) / ((1 + w) - 1) = 1 / w := by ring_nf
      refine le_trans hcl ?_
      calc (∑' n, vonMangoldt n / (n : ℝ) ^ x)
          ≤ ∑' n, vonMangoldt n / (n : ℝ) ^ (1 + w) := hmono
        _ ≤ 1 / ((1 + w) - 1) + ‖logDeriv Zc ((1 + w : ℝ) : ℂ)‖ := hpole1w
        _ ≤ 1 / w + CE * D4 := by rw [hpole1w2]; linarith [hZc1w]
        _ ≤ 2 / c_vk * D4 + CE * D4 := by linarith [h1w_inv]
        _ ≤ Cζ * D4 := by rw [hCζdef]; nlinarith [hD41, hc_vk0, hCE0]
  -- kernel bound on both horizontals
  have hkerhoriz : ∀ x τ : ℝ, σ₀ ≤ x → x ≤ c → |τ| = Tp →
      ‖windowMellin P ((x : ℂ) + (τ : ℂ) * I)‖ ≤ Kc * P / (9 * T ^ 2) := by
    intro x τ hxl hxu hτ
    rw [← windowKernel_eq_windowMellin]
    have hx0 : 0 < x := by linarith [hσ₀0]
    refine le_trans (norm_windowKernel_le hP hx0 τ) ?_
    have hτ2 : τ ^ 2 = 9 * T ^ 2 := by
      have : |τ| ^ 2 = τ ^ 2 := sq_abs τ
      rw [← this, hτ, hTpdef]; ring
    have hCkx : 2 * (2 * P + P) ^ (x + 1) / P + 2 * (P / 2 + P / 2) ^ (x + 1) / (P / 2) ≤ Kc * P := by
      have h3Px : ((3 : ℝ) * P) ^ (x + 1) = (3 : ℝ) ^ (x + 1) * (P : ℝ) ^ (x + 1) :=
        Real.mul_rpow (by norm_num) hP0.le
      have hPx1 : (P : ℝ) ^ (x + 1) = (P : ℝ) ^ x * P := by rw [Real.rpow_add hP0, Real.rpow_one]
      have e1 : 2 * (2 * P + P) ^ (x + 1) / P = 2 * (3 : ℝ) ^ (x + 1) * (P : ℝ) ^ x := by
        rw [show 2 * P + P = 3 * P by ring, h3Px, hPx1]; field_simp
      have e2 : 2 * (P / 2 + P / 2) ^ (x + 1) / (P / 2) = 4 * (P : ℝ) ^ x := by
        rw [show P / 2 + P / 2 = P by ring, hPx1]; field_simp; ring
      rw [e1, e2]
      have hlog2P : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
      have hxc : x + 1 ≤ 2 + (Real.log 2)⁻¹ := by
        have : (Real.log P)⁻¹ ≤ (Real.log 2)⁻¹ := inv_anti₀ hlog2 hlog2P
        rw [hcdef] at hxu; linarith
      have h3x : (3 : ℝ) ^ (x + 1) ≤ 9 * (3 : ℝ) ^ ((Real.log 2)⁻¹) := by
        rw [show (9 : ℝ) * (3 : ℝ) ^ ((Real.log 2)⁻¹) = (3 : ℝ) ^ (2 + (Real.log 2)⁻¹) by
          rw [Real.rpow_add (by norm_num),
            show (3 : ℝ) ^ (2 : ℝ) = 9 by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hxc
      have hPxc : (P : ℝ) ^ x ≤ Real.exp 1 * P := by
        have hPc : (P : ℝ) ^ c = Real.exp 1 * P := by
          rw [hcdef, Real.rpow_add hP0, Real.rpow_one, mul_comm]; congr 1
          rw [Real.rpow_def_of_pos hP0, mul_inv_cancel₀ hlogP.ne']
        calc (P : ℝ) ^ x ≤ (P : ℝ) ^ c := Real.rpow_le_rpow_of_exponent_le (by linarith [hP]) hxu
          _ = Real.exp 1 * P := hPc
      have hPxnn : (0 : ℝ) ≤ (P : ℝ) ^ x := Real.rpow_nonneg hP0.le x
      rw [hKcdef]
      nlinarith [h3x, hPxc, hPxnn, Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) ((Real.log 2)⁻¹),
        mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) ((Real.log 2)⁻¹)) hP0.le]
    have hinv : (x ^ 2 + τ ^ 2)⁻¹ ≤ (9 * T ^ 2)⁻¹ := by
      rw [hτ2]; apply inv_anti₀ (by positivity); nlinarith [sq_nonneg x]
    calc (2 * (2 * P + P) ^ (x + 1) / P + 2 * (P / 2 + P / 2) ^ (x + 1) / (P / 2))
            * (x ^ 2 + τ ^ 2)⁻¹
        ≤ (Kc * P) * (9 * T ^ 2)⁻¹ :=
          mul_le_mul hCkx hinv (by positivity) (by positivity)
      _ = Kc * P / (9 * T ^ 2) := by ring
  -- pointwise F bound on the horizontals
  have hFhoriz : ∀ τ : ℝ, |τ| = Tp → ∀ x ∈ Set.uIoc σ₀ c,
      ‖F ((x : ℂ) + (τ : ℂ) * I)‖ ≤ Cζ * D4 * (Kc * P / (9 * T ^ 2)) := by
    intro τ hτ x hx
    rw [Set.uIoc_of_le (by linarith : σ₀ ≤ c), Set.mem_Ioc] at hx
    rw [hFdef]; simp only; rw [norm_mul]
    exact mul_le_mul (hζhoriz x τ (le_of_lt hx.1) hx.2 hτ) (hkerhoriz x τ (le_of_lt hx.1) hx.2 hτ)
      (norm_nonneg _) (by positivity)
  -- c − σ₀ width
  have hcσ₀w : c - σ₀ ≤ 1 / Real.log 2 + 1 / 2 := by
    have hlogPinv : (Real.log P)⁻¹ ≤ (Real.log 2)⁻¹ :=
      inv_anti₀ hlog2 (Real.log_le_log (by norm_num) hP)
    rw [hcdef, hσ₀def, one_div]; linarith [hlogPinv, hwle]
  have hCbnd_nn : (0 : ℝ) ≤ Cζ * D4 * (Kc * P / (9 * T ^ 2)) := by positivity
  have hTOPb : ‖TOP‖ ≤ CH * D4 * P / T ^ 2 := by
    rw [hTOPdef]
    have hτ : |Tp| = Tp := abs_of_pos hTp0
    calc ‖∫ x in σ₀..c, F ((x : ℂ) + (Tp : ℂ) * I)‖
        ≤ (Cζ * D4 * (Kc * P / (9 * T ^ 2))) * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hFhoriz Tp hτ)
      _ ≤ (Cζ * D4 * (Kc * P / (9 * T ^ 2))) * (1 / Real.log 2 + 1 / 2) := by
          apply mul_le_mul_of_nonneg_left _ hCbnd_nn
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c - σ₀)]; exact hcσ₀w
      _ = CH * D4 * P / T ^ 2 := by rw [hCHdef]; field_simp
  have hBOTb : ‖BOT‖ ≤ CH * D4 * P / T ^ 2 := by
    rw [hBOTdef]
    have hτ : |(-Tp : ℝ)| = Tp := by rw [abs_neg]; exact abs_of_pos hTp0
    calc ‖∫ x in σ₀..c, F ((x : ℂ) + ((-Tp : ℝ) : ℂ) * I)‖
        ≤ (Cζ * D4 * (Kc * P / (9 * T ^ 2))) * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hFhoriz (-Tp) hτ)
      _ ≤ (Cζ * D4 * (Kc * P / (9 * T ^ 2))) * (1 / Real.log 2 + 1 / 2) := by
          apply mul_le_mul_of_nonneg_left _ hCbnd_nn
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c - σ₀)]; exact hcσ₀w
      _ = CH * D4 * P / T ^ 2 := by rw [hCHdef]; field_simp
  have hTAILb : ‖TAILval‖ ≤ CT * P * Real.log P / T := by
    have hsuma : (∑' n, ‖a n‖ / (n : ℝ) ^ c) ≤ Real.log P + C₀ := by
      have hcong : (∑' n, ‖a n‖ / (n : ℝ) ^ c) = ∑' n, vonMangoldt n / (n : ℝ) ^ c :=
        tsum_congr (fun n => by rw [hnorm_a n])
      rw [hcong, hcdef]; exact hcline hP
    have hsuma0 : (0 : ℝ) ≤ ∑' n, ‖a n‖ / (n : ℝ) ^ c := tsum_nonneg (fun n => by positivity)
    have hCk : (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2)) ≤ Kc * P := by
      rw [hcdef, hKcdef]; exact truncKernel_const_le hP
    have hCk0 : (0 : ℝ) ≤ 2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2) := by
      have : (0 : ℝ) < P := hP0; positivity
    have h2Tp : (2 : ℝ) / Tp = 2 / (3 * T) := by rw [hTpdef]
    have hstep : (∑' n, ‖a n‖ / (n : ℝ) ^ c)
          * (2 * (2 * P + P) ^ (c + 1) / P + 2 * (P / 2 + P / 2) ^ (c + 1) / (P / 2)) * (2 / Tp)
        ≤ (Real.log P + C₀) * (Kc * P) * (2 / (3 * T)) := by
      rw [h2Tp]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hsuma hCk hCk0 (by linarith [hlogP, hC₀0])) (by positivity)
    have hkeylog : Real.log P + C₀ ≤ (1 + C₀ / Real.log 2) * Real.log P := by
      have hlog2P : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
      have hh : C₀ * Real.log 2 ≤ C₀ * Real.log P := by nlinarith [hC₀0, hlog2P]
      rw [add_mul, one_mul, div_mul_eq_mul_div]
      have : C₀ ≤ C₀ * Real.log P / Real.log 2 := by rw [le_div_iff₀ hlog2]; linarith [hh]
      linarith
    refine le_trans hTAILnorm (le_trans hstep ?_)
    calc (Real.log P + C₀) * (Kc * P) * (2 / (3 * T))
        ≤ ((1 + C₀ / Real.log 2) * Real.log P) * (Kc * P) * (2 / (3 * T)) := by
          apply mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hkeylog (by positivity)) (by positivity)
      _ = CT * P * Real.log P / T := by rw [hCTdef]; field_simp
  -- assemble
  rw [hbridge, hInt_split]
  have hval : (1 / (2 * Real.pi)) • (RIGHT + TAILval) - wK
      = (1 / (2 * Real.pi) : ℝ) • (LEFT - I * (TOP - BOT) + TAILval) := by
    rw [Complex.real_smul, Complex.real_smul]
    have hrw : wK = (↑(1 / (2 * Real.pi)) : ℂ) * ((2 * (Real.pi : ℂ)) * wK) := by
      have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast; field_simp
    rw [hrw, ← mul_sub]
    congr 1
    rw [show (RIGHT + TAILval) - (2 * (Real.pi : ℂ)) * wK
        = (RIGHT - (2 * (Real.pi : ℂ)) * wK) + TAILval by ring, hrearr]
  rw [hval, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have htri : ‖LEFT - I * (TOP - BOT) + TAILval‖ ≤ ‖LEFT‖ + ‖TOP‖ + ‖BOT‖ + ‖TAILval‖ := by
    calc ‖LEFT - I * (TOP - BOT) + TAILval‖
        ≤ ‖LEFT - I * (TOP - BOT)‖ + ‖TAILval‖ := norm_add_le _ _
      _ ≤ (‖LEFT‖ + ‖I * (TOP - BOT)‖) + ‖TAILval‖ := by linarith [norm_sub_le LEFT (I * (TOP - BOT))]
      _ = ‖LEFT‖ + ‖TOP - BOT‖ + ‖TAILval‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ‖LEFT‖ + ‖TOP‖ + ‖BOT‖ + ‖TAILval‖ := by linarith [norm_sub_le TOP BOT]
  -- final arithmetic
  have hN : ‖LEFT - I * (TOP - BOT) + TAILval‖
      ≤ CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4
        + CT * P * Real.log P / T + 2 * CH * D4 * P / T ^ 2 := by
    calc ‖LEFT - I * (TOP - BOT) + TAILval‖
        ≤ ‖LEFT‖ + ‖TOP‖ + ‖BOT‖ + ‖TAILval‖ := htri
      _ ≤ (CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4)
            + (CH * D4 * P / T ^ 2) + (CH * D4 * P / T ^ 2) + (CT * P * Real.log P / T) := by
          linarith [hLEFTb, hTOPb, hBOTb, hTAILb]
      _ = CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4
            + CT * P * Real.log P / T + 2 * CH * D4 * P / T ^ 2 := by ring
  calc (1 / (2 * Real.pi)) * ‖LEFT - I * (TOP - BOT) + TAILval‖
      ≤ (1 / (2 * Real.pi)) * (CL * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4
          + CT * P * Real.log P / T + 2 * CH * D4 * P / T ^ 2) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ = CL / (2 * Real.pi) * P * Real.exp (-(c_vk / 2) * Real.log P / D3) * D4
          + CT / (2 * Real.pi) * P * Real.log P / T
          + 2 * CH / (2 * Real.pi) * D4 * P / T ^ 2 := by ring


end PerPairContour

end Salt.MR
