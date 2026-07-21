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

end Salt.MR
