/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HalaszSeam
import Salt.MR.PropA3Core

/-!
# PART 3 — the terminal chain's opening stones (T-0b + T-0 PREPARATION)

The terminal-assembly freeze (`docs/exploration/terminal-assembly-freeze.md`,
PART 3, refuter-repaired). This file lands:

## T-0b — the SHARP diagonal (`k4_plan_le_diag_sharp`, MANDATORY)

TERM-REF's power-counting kill made T-0b **mandatory**: the wired head's crude
diagonal `k4_plan_le_diag` (`HalaszSeam.lean:481`) bounds the Plancherel integral
by `(π/c)·(∑_{n∈F}‖bₙ‖)²`, which has ZERO decay in `n` — `crude/sharp ~ (X/y)²`,
so no `supF` can rescue the `e^{-M}` main term. The sharpening RETAINS the `n^{-c}`
decay that the crude proof discards (`HalaszSeam.lean:493`, `(mn)^{-c} ≤ 1`):

  `∫ ‖k4Poly F b c t‖²/(c²+t²) dt ≤ (π/c)·(∑_{n∈F} ‖bₙ‖/nᶜ)²`.

**ROUTE CHOICE (documented, honest).**  The freeze offered two grains — the
log-gap kernel (`offdiag_int_bound`/`log_diff_ge`) or the sharp MVT
(`dirichlet_poly_l2_mvt_final`).  Both target the FULLY-collapsed *linear*
diagonal `(π/c)·∑‖bₙ‖²/n^{2c}`.  That clean bound is **FALSE**: the Plancherel
kernel `exp(−c|log(m/n)|)·(mn)^{−c} = 1/max(m,n)^{2c}` has row-sum `≍ N` (the
integers are dense at scale `m`), so the off-diagonal cannot be absorbed into the
diagonal without the mean-value theorem's intrinsic `+N` term (a `≥ N`-grade
constant; e.g. `bₙ=1, c=1+1/L` already forces a `log X` gap).  The honest CLEAN
sharpening keeps the SEPARABLE `(mn)^{−c} = m^{−c}·n^{−c}` factor and drops only
`exp(−c|log(m/n)|) ≤ 1`, factoring the double sum into `(∑‖bₙ‖/nᶜ)²`.  This is a
genuine, load-bearing sharpening: it inserts the `n^{−c}` decay (turning the crude
`(∑Λ)² ≍ (X/y)²` into `(∑Λ/nᶜ)² ≍ L²`-grade), which is exactly the M-independent
factor TERM-REF demanded.  The fully-linear GHS diagonal `∑Λ/n^{2c}` (the sharpest
form, requiring the `+N` MVT layer-cake over the Poisson weight) is the further
refinement, recorded as a residual — not clean, and NOT needed for the
M-dependence power-count (the `(mn)^{−c}` decay alone kills the `(X/y)²`).

## T-0 PREPARATION — the fgJ-instantiated ball-decay scaffolding

The T-0 assembly (Lift Step 3) discharges `halasz_ball_decay`'s three binders
(`HalaszCore.lean:404-406`) `hsplit`/`hhead`/`htail` at the concrete seam data,
producing `halasz_ball_decay_unconditional` ⟹ `T1_pointwise_decay` unconditional.
The `hhead` binder awaits Part 1's `prop21_unconditional` (H-EXIT); it is NOT
available yet.  This file lands the pieces that consume ONLY landed inputs:

* `head_prep_utail` — the `htail` discharge from `s2_tail_ledger` (the tail ledger
  restated in the `(log X)^{−1/2}` rpow shape `halasz_ball_decay` demands).
* `hhead_supplier_fgJ` — the fgJ-instantiated `halasz_ball_decay`, carrying the
  S1′-produced `hhead` as a NAMED hypothesis (the conditional-assembly house form,
  awaiting Part 1's H-EXIT).
* `T1_decay_fgJ` — the fgJ-instantiated `T1_pointwise_decay`, likewise conditional.

**fgJ-instantiation architecture note (freeze, verified at dispatch).**  `ball_decay`
is applied with its `f`-slot = `fgJ f t₀ y Y` (the seam's windowed–twisted `f`),
1-bounded via `norm_fgJ_le` (non-multiplicative — but `ball_decay` needs only
1-boundedness, so it type-checks), and its `g`-slot = the center character
`costwist t` (1-bounded via `norm_costwist_le`).  The center squared-distance is
`M = pretDistSq (fgJ f t₀ y Y) (costwist t) X`.  The analytic `hhead`/`htail`/`hsplit`
must be established FOR fgJ through the prop21 seam — exactly what the S1′ chain
(Part 1) supplies; the scaffolding below is the socket into which H-EXIT plugs.
-/

noncomputable section

namespace Salt.MR

open MeasureTheory Complex Set
open scoped BigOperators

/-! ## T-0b — the sharp diagonal

The primary content: sharpen `k4_plan_le_diag` by retaining the `n^{−c}` decay.
The Cauchy–Schwarz cross bound (`k4_cross_le_sqrt` in `HalaszSeam`, private there)
is re-derived here as `k4_cross_CS` so `contour_A13_A14_head_sharp` is
unconditional, a true drop-in for `contour_A13_A14_head_wired`. -/

/-- `k4Poly F b c` is continuous in `t` (re-derivation of `HalaszSeam`'s private
`k4Poly_continuous`, needed for the CS integrability gate). -/
private lemma k4Poly_cont (F : Finset ℕ) (b : ℕ → ℂ) {c : ℝ}
    (hF : ∀ n ∈ F, 1 ≤ n) : Continuous (fun t : ℝ => k4Poly F b c t) := by
  simp only [k4Poly_eq]
  refine continuous_finsetSum _ (fun n hn => ?_)
  have hn1 : 1 ≤ n := hF n hn
  have hnpos : 0 < n := hn1
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn1
  have hbase : Continuous (fun t : ℝ => (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) :=
    (by fun_prop : Continuous fun t : ℝ => (c : ℂ) + (t : ℂ) * I).const_cpow (Or.inl hn0)
  refine continuous_const.div hbase (fun t => ?_)
  have hne : ‖(n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ≠ 0 := by
    rw [Complex.norm_natCast_cpow_of_pos hnpos]
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hnpos) _).ne'
  exact fun h => hne (by rw [h, norm_zero])

/-- Pointwise coefficient-mass bound (re-derivation of the private `k4Poly_norm_le`). -/
private lemma k4Poly_massle {F : Finset ℕ} {b : ℕ → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ n ∈ F, 1 ≤ n) (t : ℝ) :
    ‖k4Poly F b c t‖ ≤ ∑ n ∈ F, ‖b n‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
  have hn1 : 1 ≤ n := hF n hn
  have hnpos : 0 < n := hn1
  rw [norm_div, Complex.norm_natCast_cpow_of_pos hnpos]
  have hre : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
  rw [hre]
  exact div_le_self (norm_nonneg _) (Real.one_le_rpow (by exact_mod_cast hn1) hc)

/-- Poisson-weighted square integrability (re-derivation of `k4Poly_sq_integrable`). -/
private lemma k4Poly_sqInt {F : Finset ℕ} {b : ℕ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : ∀ n ∈ F, 1 ≤ n) :
    Integrable (fun t : ℝ => ‖k4Poly F b c t‖ ^ 2 / (c ^ 2 + t ^ 2)) := by
  have hcont : Continuous (fun t : ℝ => ‖k4Poly F b c t‖ ^ 2 / (c ^ 2 + t ^ 2)) :=
    (((k4Poly_cont (c := c) F b hF).norm).pow 2).div (by fun_prop)
      (fun t => by positivity)
  refine ((Salt.SW.integrable_inv_c_sq_add_sq hc).const_mul ((∑ n ∈ F, ‖b n‖) ^ 2)).mono'
    hcont.aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (by positivity), div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact pow_le_pow_left₀ (norm_nonneg _) (k4Poly_massle hc.le hF t) 2

/-- **CS cross bound** (re-derivation of `HalaszSeam`'s private `k4_cross_le_sqrt`).
The weighted `L²` Cauchy–Schwarz on the Poisson kernel; EXACT (no log). -/
private lemma k4_cross_CS {F G : Finset ℕ} {bA bB : ℕ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : ∀ n ∈ F, 1 ≤ n) (hG : ∀ n ∈ G, 1 ≤ n) :
    (∫ t : ℝ, ‖k4Poly F bA c t‖ * ‖k4Poly G bB c t‖ / (c ^ 2 + t ^ 2))
      ≤ Real.sqrt (∫ t : ℝ, ‖k4Poly F bA c t‖ ^ 2 / (c ^ 2 + t ^ 2))
        * Real.sqrt (∫ t : ℝ, ‖k4Poly G bB c t‖ ^ 2 / (c ^ 2 + t ^ 2)) := by
  have hwpos : ∀ t : ℝ, (0 : ℝ) < c ^ 2 + t ^ 2 := fun t => by positivity
  have hden : Continuous (fun t : ℝ => Real.sqrt (c ^ 2 + t ^ 2)) := by fun_prop
  set u : ℝ → ℝ := fun t => ‖k4Poly F bA c t‖ / Real.sqrt (c ^ 2 + t ^ 2) with hu
  set v : ℝ → ℝ := fun t => ‖k4Poly G bB c t‖ / Real.sqrt (c ^ 2 + t ^ 2) with hv
  have huv : ∀ t : ℝ, u t * v t
      = ‖k4Poly F bA c t‖ * ‖k4Poly G bB c t‖ / (c ^ 2 + t ^ 2) := by
    intro t; simp only [hu, hv, div_mul_div_comm, Real.mul_self_sqrt (hwpos t).le]
  have husq : ∀ t : ℝ, u t ^ (2 : ℝ) = ‖k4Poly F bA c t‖ ^ 2 / (c ^ 2 + t ^ 2) := by
    intro t; simp only [hu, Real.rpow_two, div_pow, Real.sq_sqrt (hwpos t).le]
  have hvsq : ∀ t : ℝ, v t ^ (2 : ℝ) = ‖k4Poly G bB c t‖ ^ 2 / (c ^ 2 + t ^ 2) := by
    intro t; simp only [hv, Real.rpow_two, div_pow, Real.sq_sqrt (hwpos t).le]
  have husq2 : ∀ t : ℝ, u t ^ 2 = ‖k4Poly F bA c t‖ ^ 2 / (c ^ 2 + t ^ 2) := by
    intro t; simp only [hu, div_pow, Real.sq_sqrt (hwpos t).le]
  have hvsq2 : ∀ t : ℝ, v t ^ 2 = ‖k4Poly G bB c t‖ ^ 2 / (c ^ 2 + t ^ 2) := by
    intro t; simp only [hv, div_pow, Real.sq_sqrt (hwpos t).le]
  have hcontu : Continuous u :=
    (k4Poly_cont (c := c) F bA hF).norm.div hden
      (fun t => (Real.sqrt_pos.mpr (hwpos t)).ne')
  have hcontv : Continuous v :=
    (k4Poly_cont (c := c) G bB hG).norm.div hden
      (fun t => (Real.sqrt_pos.mpr (hwpos t)).ne')
  have humem : MemLp u 2 volume := by
    rw [memLp_two_iff_integrable_sq hcontu.aestronglyMeasurable]
    exact (k4Poly_sqInt hc hF).congr
      (Filter.Eventually.of_forall (fun t => (husq2 t).symm))
  have hvmem : MemLp v 2 volume := by
    rw [memLp_two_iff_integrable_sq hcontv.aestronglyMeasurable]
    exact (k4Poly_sqInt hc hG).congr
      (Filter.Eventually.of_forall (fun t => (hvsq2 t).symm))
  have humem2 : MemLp u (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 from by simp]; exact humem
  have hvmem2 : MemLp v (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 from by simp]; exact hvmem
  have hunn : (0 : ℝ → ℝ) ≤ᵐ[volume] u :=
    Filter.Eventually.of_forall (fun t => by simp only [hu, Pi.zero_apply]; positivity)
  have hvnn : (0 : ℝ → ℝ) ≤ᵐ[volume] v :=
    Filter.Eventually.of_forall (fun t => by simp only [hv, Pi.zero_apply]; positivity)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two hunn hvnn humem2 hvmem2
  have eLHS : (∫ t : ℝ, ‖k4Poly F bA c t‖ * ‖k4Poly G bB c t‖ / (c ^ 2 + t ^ 2))
      = ∫ t : ℝ, u t * v t :=
    integral_congr_ae (Filter.Eventually.of_forall (fun t => (huv t).symm))
  have eA : (∫ t : ℝ, u t ^ (2 : ℝ)) = ∫ t : ℝ, ‖k4Poly F bA c t‖ ^ 2 / (c ^ 2 + t ^ 2) :=
    integral_congr_ae (Filter.Eventually.of_forall husq)
  have eB : (∫ t : ℝ, v t ^ (2 : ℝ)) = ∫ t : ℝ, ‖k4Poly G bB c t‖ ^ 2 / (c ^ 2 + t ^ 2) :=
    integral_congr_ae (Filter.Eventually.of_forall hvsq)
  rw [eLHS, ← eA, ← eB, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hholder

/-- **T-0b — the sharp diagonal (`k4_plan_le_diag_sharp`).**  The Plancherel
integral bounded by the `n^{−c}`-WEIGHTED coefficient-mass square.  Where the crude
`k4_plan_le_diag` discards the `(mn)^{−c}` decay (`(mn)^{−c} ≤ 1`), this keeps it,
factoring the double sum by the separable weight `(mn)^{−c} = m^{−c}·n^{−c}`:

  `∫ ‖k4Poly F b c t‖²/(c²+t²) dt ≤ (π/c)·(∑_{n∈F} ‖bₙ‖/nᶜ)²`.

`exp(−c|log(m/n)|) ≤ 1` is the ONLY thing dropped here; the load-bearing decay is
the retained `(mn)^{−c}` (see the module docstring for why the fully-linear
`∑‖bₙ‖²/n^{2c}` is not a clean bound). -/
theorem k4_plan_le_diag_sharp {F : Finset ℕ} {b : ℕ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : ∀ n ∈ F, 1 ≤ n) :
    (∫ t : ℝ, ‖k4Poly F b c t‖ ^ 2 / (c ^ 2 + t ^ 2))
      ≤ Real.pi / c * (∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) ^ 2 := by
  simp only [k4Poly_eq]
  rw [dirichlet_plancherel F b hc hF, pow_two, Finset.sum_mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn => ?_))
  have hm1 : 1 ≤ m := hF m hm
  have hn1 : 1 ≤ n := hF n hn
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hDeq : ((m * n : ℕ) : ℝ) ^ c = (m : ℝ) ^ c * (n : ℝ) ^ c := by
    push_cast; rw [Real.mul_rpow hmr.le hnr.le]
  have hmc : (0 : ℝ) < (m : ℝ) ^ c := Real.rpow_pos_of_pos hmr c
  have hnc : (0 : ℝ) < (n : ℝ) ^ c := Real.rpow_pos_of_pos hnr c
  have hre : (b m * starRingEnd ℂ (b n)).re ≤ ‖b m‖ * ‖b n‖ := by
    have h1 : (b m * starRingEnd ℂ (b n)).re ≤ ‖b m * starRingEnd ℂ (b n)‖ :=
      Complex.re_le_norm _
    rwa [norm_mul, Complex.norm_conj] at h1
  have hE1 : Real.exp (-(c * |Real.log m - Real.log n|)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hE0 : (0 : ℝ) ≤ Real.exp (-(c * |Real.log m - Real.log n|)) := (Real.exp_pos _).le
  calc (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(c * |Real.log m - Real.log n|))
      = (b m * starRingEnd ℂ (b n)).re
          * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(c * |Real.log m - Real.log n|))) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ ‖b m‖ * ‖b n‖
          * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(c * |Real.log m - Real.log n|))) :=
        mul_le_mul_of_nonneg_right hre (mul_nonneg (by positivity) hE0)
    _ ≤ ‖b m‖ * ‖b n‖ * (((m : ℝ) ^ c * (n : ℝ) ^ c)⁻¹ * 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hDeq]
        exact mul_le_mul_of_nonneg_left hE1 (by positivity)
    _ = ‖b m‖ / (m : ℝ) ^ c * (‖b n‖ / (n : ℝ) ^ c) := by
        rw [mul_one, mul_inv]; ring

/-- **T-0b — the sharp wired head (`contour_A13_A14_head_sharp`).**  The K4′
reconciliation `contour_A13_A14_head_wired` (`HalaszSeam.lean:525`) with the crude
coefficient-mass² diagonal `(π/c)·((log 4+4)·b)²` REPLACED by the sharp
`n^{−c}`-weighted diagonal `(π/c)·(∑_{n∈window} ‖lambdaLin g n‖/nᶜ)²`.  The CS cross
bound (`k4_cross_CS`) and both diagonal bounds (`k4_plan_le_diag_sharp`) are
discharged, so this is unconditional — a drop-in sharpening of the wired head.  The
window coefficient mass is kept `n^{−c}`-weighted (NOT collapsed to `(log 4+4)·b`);
that retained decay is the M-independent factor the terminal chain needs. -/
theorem contour_A13_A14_head_sharp
    {gA gB : ℕ → ℂ} {c X supF : ℝ} (hc : 0 < c) (hX : 0 ≤ X) (hsupF : 0 ≤ supF)
    (aA bA aB bB : ℕ) :
    X * supF * (∫ t : ℝ, ‖k4Poly (Finset.Ioc aA bA) (lambdaLin gA) c t‖
        * ‖k4Poly (Finset.Ioc aB bB) (lambdaLin gB) c t‖ / (c ^ 2 + t ^ 2))
      ≤ X * supF * (Real.sqrt (Real.pi / c
              * (∑ n ∈ Finset.Ioc aA bA, ‖lambdaLin gA n‖ / (n : ℝ) ^ c) ^ 2)
          * Real.sqrt (Real.pi / c
              * (∑ n ∈ Finset.Ioc aB bB, ‖lambdaLin gB n‖ / (n : ℝ) ^ c) ^ 2)) := by
  have hFmem : ∀ n ∈ Finset.Ioc aA bA, 1 ≤ n := fun n hn => by
    have := (Finset.mem_Ioc.mp hn).1; omega
  have hGmem : ∀ n ∈ Finset.Ioc aB bB, 1 ≤ n := fun n hn => by
    have := (Finset.mem_Ioc.mp hn).1; omega
  exact contour_A13_A14_head hX hsupF
    (k4_cross_CS (F := Finset.Ioc aA bA) (G := Finset.Ioc aB bB)
      (bA := lambdaLin gA) (bB := lambdaLin gB) hc hFmem hGmem)
    (k4_plan_le_diag_sharp (F := Finset.Ioc aA bA) (b := lambdaLin gA) hc hFmem)
    (k4_plan_le_diag_sharp (F := Finset.Ioc aB bB) (b := lambdaLin gB) hc hGmem)

/-! ## T-0 PREPARATION — the fgJ-instantiated ball-decay scaffolding

Everything below consumes ONLY landed inputs (`s2_tail_ledger`, `halasz_ball_decay`,
`T1_pointwise_decay`, `norm_fgJ_le`, `norm_costwist_le`).  The `hhead` binder is
carried as a NAMED hypothesis, awaiting Part 1's `prop21_unconditional` (H-EXIT). -/

/-- **`htail` discharge (`head_prep_utail`).**  The S2′ tail ledger `s2_tail_ledger`
restated in the `(log X)^{−1/2}` rpow shape that `halasz_ball_decay`'s `htail` binder
demands.  Bridges `Csup·X/√L = Csup·X·L^{−1/2}` (`Real.sqrt L = L^{1/2}`).  Consumes
only `s2_tail_ledger`. -/
theorem head_prep_utail {Lx X Csup : ℝ} (hL : 1 < Lx) (hX : 0 ≤ X) (hC : 0 ≤ Csup) :
    (Csup * Lx ^ 3) * (Real.sqrt Lx * X * (Lx ^ 4)⁻¹)
      ≤ Csup * X * Lx ^ (-(1 : ℝ) / 2) := by
  have hLpos : (0 : ℝ) < Lx := by linarith
  refine (s2_tail_ledger hL hX hC).trans ?_
  have hbridge : Csup * X / Real.sqrt Lx = Csup * X * Lx ^ (-(1 : ℝ) / 2) := by
    rw [div_eq_mul_inv]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hLpos.le,
      show -(1 / 2 : ℝ) = -(1 : ℝ) / 2 by norm_num]
  rw [hbridge]

/-- **`hsplit` bookkeeping (`head_prep_split`).**  The ball contribution `U` is,
by construction, the sum of its head and tail parts (the S1′ representation's
head/tail split of `U`).  Vacuous algebra — recorded so the assembly's three
binders are all named. -/
theorem head_prep_split (Uhead Utail : ℝ) : Uhead + Utail = Uhead + Utail := rfl

/-- **The fgJ-instantiated ball decay (`hhead_supplier_fgJ`).**  `halasz_ball_decay`
applied at `f`-slot `= fgJ f t₀ y Y` (1-bounded via `norm_fgJ_le`) and `g`-slot `=
costwist t` (1-bounded via `norm_costwist_le`), with `M = 𝔻(fgJ, costwist t; X)²`.
The `hhead` binder (the S2′ centered head, K4′/S1′-conditional) is carried as a NAMED
hypothesis — this is the socket Part 1's H-EXIT plugs into.  `htail` is discharged
downstream by `head_prep_utail`; `hsplit` by construction.  Consumes only landed
inputs.

**AMENDMENT J0 (JYH-ratified 2026-07-23).**  `M = M_range (fgJ f t₀ y Y) X T` is GHS
Lemma 1's range-minimum (was the center value `pretDistSq (fgJ f t₀ y Y) (costwist t) X`);
the range-min never drifts below the landed floor (`Mrange_one_floor`) and restores the
frozen `prop_A3'` semantics.  The `t` slot survives (it fixes the retained `costwist t`
ball-center character fed to `halasz_ball_decay`'s `g` socket).

**AMENDMENT B4 (JYH-ratified 2026-07-23).**  `hhead`/conclusion re-frozen to the
elementary B-route `C·e^{−cM}` shape (`c = 1/e`, coefficient `C₁ + C₂`), tracking
`halasz_ball_decay`. -/
theorem hhead_supplier_fgJ {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t₀ y Y t : ℝ)
    {X ε U Uhead Utail C₁ C₂ T : ℝ}
    (hX : Real.exp 1 ≤ X) (hε : 0 ≤ ε) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : U = Uhead + Utail)
    (hhead : Uhead ≤ C₁ * X * Real.exp (-(1 / Real.exp 1) * M_range (fgJ f t₀ y Y) X T))
    (htail : Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2)) :
    U ≤ (C₁ + C₂) * X
        * (Real.exp (-(1 / Real.exp 1) * M_range (fgJ f t₀ y Y) X T)
          + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) :=
  halasz_ball_decay (norm_fgJ_le hf t₀ y Y) (norm_costwist_le t) hX hε hC₁ hC₂
    hsplit hhead htail

/-- **The fgJ-instantiated T1 decay (`T1_decay_fgJ`).**  `T1_pointwise_decay` at the
fgJ instantiation, carrying the R3.1 floor `M ≥ (1/32)·loglog X` and the (still
conditional) `hhead`.  Concludes the `≪ X·(log X)^{−1/(32e)+o(1)}` grade for the
windowed–twisted seam datum (AMENDMENT B4: `hhead` in the `e^{−cM}` shape, `c = 1/e`).
Consumes only landed inputs; awaits Part 1 for the `hhead` discharge.

**AMENDMENT J0 (JYH-ratified 2026-07-23).**  `M = M_range (fgJ f t₀ y Y) X T` is GHS
Lemma 1's range-minimum (was center-M); the floor `hfloor` is now the range-min form,
`Mrange_seam_floor_column`-supplied (formerly over-claimed as `Mrange_one_floor`), restoring the frozen `prop_A3'` semantics. -/
theorem T1_decay_fgJ {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t₀ y Y t : ℝ)
    {X ε U Uhead Utail C₁ C₂ T : ℝ}
    (hX : Real.exp 1 ≤ X) (hε : 0 ≤ ε) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : U = Uhead + Utail)
    (hhead : Uhead ≤ C₁ * X * Real.exp (-(1 / Real.exp 1) * M_range (fgJ f t₀ y Y) X T))
    (htail : Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2))
    (hfloor : (1 / 32) * Real.log (Real.log X)
        ≤ M_range (fgJ f t₀ y Y) X T) :
    U ≤ (C₁ + C₂) * X *
        ((Real.log X) ^ (-(1 / Real.exp 1) / 32) + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) :=
  T1_pointwise_decay (norm_fgJ_le hf t₀ y Y) (norm_costwist_le t) hX hε hC₁ hC₂
    hsplit hhead htail hfloor

/-! ## V5-7 — the UNWINDOWED T-chain scaffolds (the v5 aligned route)

The V5-0 seam un-windowing (JYH-ratified, `terminal-assembly-freeze.md`) makes the
seam carrier the TRIVIAL indicator `fun _ => 1` — H-EXIT delivers the FULL twisted
hat-smoothed sum, GHS (2.2) faithful.  The stones below are the unwindowed twins of
the `fgJ` scaffolds above: `T1_decay_trivial`/`hhead_supplier_trivial` supersede
`T1_decay_fgJ`/`hhead_supplier_fgJ` on the v5 chain (the `fgJ` versions stay landed —
heritage + the branch floors still reference them until the T-chain rewires).

The keystone is `seamCoeff_trivial_dist_eq`: the EXACT distance identity
`𝔻(seamCoeff f (fun _ => 1) t₀, costwist t; X)² = 𝔻(f, costwist(t+t₀); X)²` — the
twist-shift algebra ONLY, NO out-of-window mass (the trivial indicator has no window,
so `DistWindow.dist_window_restrict`'s deficit term vanishes and the `≥` becomes `=`).
With it the consumer hands the UNWINDOWED floor `𝔻(f, costwist(t+t₀))²` straight into
the twin, and the T-1 window-restriction conversion is unnecessary on this chain. -/

/-- The seam twist `n ↦ n^{−it₀}` equals the character `costwist (−t₀)` (re-derivation
of `DistWindow`'s private `natCpow_neg_costwist`, needed here since `HalaszHead` does
not import `DistWindow`). -/
private lemma head_natCpow_neg_costwist (t₀ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) ^ (-(t₀ : ℂ) * I) = costwist (-t₀) n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  unfold costwist
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- **V5-7 — the EXACT unwindowed distance identity (`seamCoeff_trivial_dist_eq`).**
At the TRIVIAL seam indicator `fun _ => 1`, the pretentious distance of the twisted
seam datum against the center `costwist t` equals the distance of the bare `f` against
the SHIFTED center `costwist (t+t₀)`:

  `𝔻(seamCoeff f (fun _ => 1) t₀, costwist t; X)² = 𝔻(f, costwist(t+t₀); X)²`.

An EXACT identity (no out-of-window mass, no error term): with the trivial indicator
every prime is "in window", so `DistWindow.dist_window_restrict`'s out-of-window deficit
vanishes and the `≥` collapses to `=`.  Per-prime, the seam twist `n^{−it₀}` folds into
the character (`head_natCpow_neg_costwist` + `costwist_conj`/`costwist_add`), shifting
the center frequency by `t₀`.  This is what lets the v5 consumer feed the UNWINDOWED
floor directly (the T-1 window conversion is unnecessary on this chain). -/
theorem seamCoeff_trivial_dist_eq {f : ℕ → ℂ} (t₀ t X : ℝ) :
    pretDistSq (seamCoeff f (fun _ => 1) t₀) (costwist t) X
      = pretDistSq f (costwist (t + t₀)) X := by
  unfold pretDistSq
  refine Finset.sum_congr rfl (fun p hp => ?_)
  obtain ⟨_, hpp⟩ := Finset.mem_filter.mp hp
  have hp1 : 1 ≤ p := hpp.one_lt.le
  have hpne : p ≠ 0 := Nat.one_le_iff_ne_zero.mp hp1
  have hsc : seamCoeff f (fun _ => 1) t₀ p = f p * costwist (-t₀) p := by
    unfold seamCoeff
    rw [if_neg hpne]
    simp only [head_natCpow_neg_costwist t₀ hp1, mul_one]
  have heq : seamCoeff f (fun _ => 1) t₀ p * (starRingEnd ℂ) (costwist t p)
      = f p * (starRingEnd ℂ) (costwist (t + t₀) p) := by
    rw [hsc, costwist_conj t p, costwist_conj (t + t₀) p, mul_assoc,
      costwist_add (-t₀) (-t) p, show -t₀ + -t = -(t + t₀) from by ring]
  rw [heq]

/-- The trivial seam indicator `fun _ => 1` is 1-bounded (`‖(1 : ℂ)‖ = 1`) — the norm
gate the unwindowed twins discharge trivially. -/
private lemma norm_trivialInd_le : ∀ n : ℕ, ‖(fun _ : ℕ => (1 : ℂ)) n‖ ≤ 1 :=
  fun _ => le_of_eq norm_one

/-- **The unwindowed ball decay (`hhead_supplier_trivial`).**  The v5 twin of
`hhead_supplier_fgJ`: `halasz_ball_decay` at `f`-slot `= seamCoeff f (fun _ => 1) t₀`
(the FULL twisted seam datum, 1-bounded via `norm_seamCoeff_le` with the trivial
indicator's `‖(1:ℂ)‖ ≤ 1`) and `g`-slot `= costwist t`, with
`M = 𝔻(seamCoeff f (fun _ => 1) t₀, costwist t; X)²`.  The `hhead` binder (the S2′
centered head, K4′/S1′-conditional) is carried as a NAMED hypothesis — the socket the
v5 H-EXIT plugs into.  **Supersedes `hhead_supplier_fgJ` on the v5 chain** (V5-0 seam
un-windowing); `hhead_supplier_fgJ` stays landed as heritage.  The consumer re-expresses
the distance hypothesis via `seamCoeff_trivial_dist_eq`, handing in the UNWINDOWED floor
directly (no T-1 window conversion).

**AMENDMENT J0 (JYH-ratified 2026-07-23).**  `M = M_range (seamCoeff f (fun _ => 1) t₀) X T`
is GHS Lemma 1's range-minimum (was center-M `pretDistSq (seamCoeff f (fun _ => 1) t₀)
(costwist t) X`); restores the frozen `prop_A3'` semantics.  The exact identity
`seamCoeff_trivial_dist_eq` still serves the downstream floor supplier — the twist-shift
`t₀` now lives INSIDE the range's offset variable (the consumer that discharges the
`M_range` floor threads the window/`t₀` bookkeeping; carried here as a hypothesis).

**AMENDMENT B4 (JYH-ratified 2026-07-23).**  `hhead`/conclusion re-frozen to the
elementary B-route `C·e^{−cM}` shape (`c = 1/e`, coefficient `C₁ + C₂`), tracking
`halasz_ball_decay`. -/
theorem hhead_supplier_trivial {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t₀ t : ℝ)
    {X ε U Uhead Utail C₁ C₂ T : ℝ}
    (hX : Real.exp 1 ≤ X) (hε : 0 ≤ ε) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : U = Uhead + Utail)
    (hhead : Uhead ≤ C₁ * X
        * Real.exp (-(1 / Real.exp 1) * M_range (seamCoeff f (fun _ => 1) t₀) X T))
    (htail : Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2)) :
    U ≤ (C₁ + C₂) * X
        * (Real.exp (-(1 / Real.exp 1) * M_range (seamCoeff f (fun _ => 1) t₀) X T)
          + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) :=
  halasz_ball_decay (norm_seamCoeff_le hf norm_trivialInd_le t₀) (norm_costwist_le t)
    hX hε hC₁ hC₂ hsplit hhead htail

/-- **The unwindowed T1 decay (`T1_decay_trivial`).**  The v5 twin of `T1_decay_fgJ`:
`T1_pointwise_decay` at `f`-slot `= seamCoeff f (fun _ => 1) t₀` (the FULL twisted seam
datum, 1-bounded via the trivial indicator) and `g`-slot `= costwist t`, carrying the
R3.1 floor `M ≥ (1/32)·loglog X` and the (still conditional) `hhead`.  Concludes the
`≪ X·(log X)^{−1/(32e)+o(1)}` grade for the UNWINDOWED seam datum (AMENDMENT B4: `hhead`
in the `e^{−cM}` shape, `c = 1/e`).  **Supersedes `T1_decay_fgJ` on the v5 chain**
(V5-0 seam un-windowing); `T1_decay_fgJ` stays landed as heritage.  The floor hypothesis
is the unwindowed `𝔻(seamCoeff f (fun _ => 1) t₀,
costwist t; X)²`, which the consumer obtains from the bare `𝔻(f, costwist(t+t₀))²` floor
EXACTLY via `seamCoeff_trivial_dist_eq` — the T-1 window-restriction conversion is
unnecessary on this chain.

**AMENDMENT J0 (JYH-ratified 2026-07-23).**  `M = M_range (seamCoeff f (fun _ => 1) t₀) X T`
is GHS Lemma 1's range-minimum (was center-M); the floor `hfloor` is now the range-min
form (`Mrange_seam_floor_column`-supplied (formerly over-claimed as `Mrange_one_floor`) via `seamCoeff_trivial_dist_eq`'s twist-shift absorbed
into the offset variable), restoring the frozen `prop_A3'` semantics. -/
theorem T1_decay_trivial {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t₀ t : ℝ)
    {X ε U Uhead Utail C₁ C₂ T : ℝ}
    (hX : Real.exp 1 ≤ X) (hε : 0 ≤ ε) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : U = Uhead + Utail)
    (hhead : Uhead ≤ C₁ * X
        * Real.exp (-(1 / Real.exp 1) * M_range (seamCoeff f (fun _ => 1) t₀) X T))
    (htail : Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2))
    (hfloor : (1 / 32) * Real.log (Real.log X)
        ≤ M_range (seamCoeff f (fun _ => 1) t₀) X T) :
    U ≤ (C₁ + C₂) * X *
        ((Real.log X) ^ (-(1 / Real.exp 1) / 32) + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) :=
  T1_pointwise_decay (norm_seamCoeff_le hf norm_trivialInd_le t₀) (norm_costwist_le t)
    hX hε hC₁ hC₂ hsplit hhead htail hfloor

end Salt.MR
