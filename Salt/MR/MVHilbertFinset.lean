/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MVCore2

/-!
# KMT port, wave P-2, stages S1–S2: the Finset re-cut of the L² mean-value theorem

Freeze: `docs/exploration/port-freeze-0729.md` (wave P-2, the hybrid MVT).  Refuter
verdict R-P3 (`docs/blueprints/flags.md`, ⟦THE PORT REFUTER PASS⟧): the **Finset re-cut
is mandatory** — running the mean-value theorem class-by-class on `Finset.Icc 1 N` and
then summing loses a factor `q` (fatal for KMT Lemma 6.2's `φ(q)·N/q` term).  The cure
is to run the theorem on the *arithmetic-progression* index set itself, where the
log-frequency gap is `q/N` rather than `1/N`.

## S1 — the AP gap lemma

`log_gap_ge_of_modEq`: for `m ≠ n` in `Icc 1 N` with `m ≡ n [MOD q]`,
`q/N ≤ |log m − log n|`.  Sharp (`n − m ≥ q` is attained), and **no coprimality is
needed**.  Derivation: WLOG `n > m`, then `q ∣ n − m` forces `n − m ≥ q`, and
`log n − log m ≥ 1 − m/n = (n−m)/n ≥ q/n ≥ q/N`.  This is `log_gap_ge`
(`Salt/MR/MVHilbert.lean`) with the `1` replaced by `q`.

## S2 — the Finset MVT

The landed assembly of `Salt/MR/MVHilbert.lean` re-cut from `Finset.Icc 1 N` to an
arbitrary `s : Finset ℕ` with `1 ≤ n` on `s`, and with the frequency separation `δ`
now a *parameter* rather than `1/N`:

`dpolyS`, `hilbertLogSumS`, `dpolyS_l2_expand`, `dpolyS_l2_diagonal`,
`offdiag_eq_hilbertS`, `norm_hilbertLogSumS_le`, and the exit
`dpolyS_l2_mvt_final : ∫_{-T}^{T} ‖∑_{n∈s} aₙ n^{it}‖² ≤ (2T + 2π/δ)·∑_{n∈s}‖aₙ‖²`.

The Montgomery–Vaughan hard core is *consumed verbatim*: `MVHilbertUniform` is already
stated for an arbitrary `s : Finset ℕ` and arbitrary real frequencies `lam`, and
`mvHilbertUniform_holds` (`Salt/MR/MVCore2.lean`) discharges it unconditionally.  The
landed `Icc`-shaped originals are untouched.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory intervalIntegral

/-! ## S1 — the arithmetic-progression gap -/

/-- **S1 (the AP gap lemma).**  Distinct integers `m, n ∈ [1, N]` lying in the *same*
residue class mod `q` have log-gap at least `q/N`:
`q/N ≤ |log m − log n|`.

Sharp: `n − m = q` is attained (and then `log n − log m ≈ q/n`).  No coprimality
hypothesis is needed — only `m ≡ n [MOD q]`.  This is the `q`-fold sharpening of
`log_gap_ge` that makes the per-class mean-value theorem pay `N/q` instead of `N`. -/
lemma log_gap_ge_of_modEq {N q m n : ℕ} (hq : 0 < q)
    (hm : m ∈ Finset.Icc 1 N) (hn : n ∈ Finset.Icc 1 N) (hmn : m ≠ n)
    (hcong : m ≡ n [MOD q]) :
    (q : ℝ) / N ≤ |Real.log m - Real.log n| := by
  -- the one-sided core: for `r < p` in `[1,N]` congruent mod `q`, `q/N ≤ log p − log r`
  have main : ∀ p r : ℕ, p ∈ Finset.Icc 1 N → r ∈ Finset.Icc 1 N → r < p →
      r ≡ p [MOD q] → (q : ℝ) / N ≤ Real.log p - Real.log r := by
    intro p r hp hr hrp hcong'
    rcases Finset.mem_Icc.1 hp with ⟨hp1, hpN⟩
    rcases Finset.mem_Icc.1 hr with ⟨hr1, _⟩
    have hNr : (0 : ℝ) < N := by
      have : (1 : ℕ) ≤ N := le_trans hp1 hpN
      exact_mod_cast lt_of_lt_of_le Nat.one_pos this
    have hppos : (0 : ℝ) < p := by exact_mod_cast lt_of_lt_of_le Nat.one_pos hp1
    have hrpos : (0 : ℝ) < r := by exact_mod_cast lt_of_lt_of_le Nat.one_pos hr1
    have hpN' : (p : ℝ) ≤ N := by exact_mod_cast hpN
    -- the arithmetic step: `q ∣ p − r` and `p − r > 0` give `q ≤ p − r`
    have hqdvd : q ∣ p - r := (Nat.modEq_iff_dvd' (le_of_lt hrp)).1 hcong'
    have hqle : q ≤ p - r := Nat.le_of_dvd (Nat.sub_pos_of_lt hrp) hqdvd
    have hqleR : (q : ℝ) ≤ (p : ℝ) - r := by
      have h1 : ((p - r : ℕ) : ℝ) = (p : ℝ) - r := by
        have : (r : ℕ) ≤ p := le_of_lt hrp
        push_cast [this]; ring
      have h2 : (q : ℝ) ≤ ((p - r : ℕ) : ℝ) := by exact_mod_cast hqle
      linarith [h1 ▸ h2]
    -- the analytic step: `log(r/p) ≤ r/p − 1`
    have h1 : Real.log ((r : ℝ) / p) ≤ (r : ℝ) / p - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log ((r : ℝ) / p) = Real.log r - Real.log p := by
      rw [Real.log_div (ne_of_gt hrpos) (ne_of_gt hppos)]
    have h3 : 1 - (r : ℝ) / p ≤ Real.log p - Real.log r := by rw [h2] at h1; linarith
    -- `q/N ≤ q/p ≤ (p − r)/p = 1 − r/p`
    have hqNpos : (0 : ℝ) ≤ (q : ℝ) := by positivity
    have hlow : (q : ℝ) / N ≤ 1 - (r : ℝ) / p := by
      rw [le_sub_iff_add_le, div_add_div _ _ (ne_of_gt hNr) (ne_of_gt hppos),
        div_le_one (by positivity)]
      nlinarith [hqleR, hpN', hNr, hppos, hqNpos]
    linarith [hlow, h3]
  have hqNnn : (0 : ℝ) ≤ (q : ℝ) / N := by positivity
  rcases lt_or_gt_of_ne hmn with h | h
  · have hval := main n m hn hm h hcong
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact hval
  · have hval := main m n hm hn h hcong.symm
    rw [abs_of_nonneg (by linarith)]
    exact hval

/-! ## S2 — the Finset-indexed Dirichlet polynomial and its L² mean value -/

/-- The Dirichlet polynomial over an arbitrary finite index set:
`F(t) = ∑_{n ∈ s} aₙ · n^{it} = ∑_{n ∈ s} aₙ · exp(i·t·log n)`.  The `Icc 1 N`-shaped
`dpoly` (`Salt/MR/L2MVT.lean`) is the special case `s = Finset.Icc 1 N`. -/
noncomputable def dpolyS (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, a n * Complex.exp (Complex.I * (t : ℂ) * Real.log n)

/-- `dpolyS s a = dpoly N a` at `s = Finset.Icc 1 N` (the re-cut is a genuine
generalization, not a variant). -/
lemma dpolyS_Icc (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : dpolyS (Finset.Icc 1 N) a t = dpoly N a t := rfl

/-- `dpolyS s a` is continuous (a finite sum of continuous terms). -/
lemma continuous_dpolyS (s : Finset ℕ) (a : ℕ → ℂ) : Continuous (dpolyS s a) := by
  unfold dpolyS
  apply continuous_finsetSum
  intro n _
  fun_prop

/-- **Pointwise expansion** at `s`: `‖F(t)‖²`, as a complex number, is the double sum
`∑_{n∈s} ∑_{m∈s} conj(aₙ)·aₘ · exp(i·t·(log m − log n))`. -/
lemma sq_norm_dpolyS_eq (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ((‖dpolyS s a t‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ s, ∑ m ∈ s,
          (starRingEnd ℂ) (a n) * a m
            * Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))) := by
  have hcm : ((‖dpolyS s a t‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) (dpolyS s a t) * dpolyS s a t := by
    rw [Complex.sq_norm]; exact Complex.normSq_eq_conj_mul_self
  rw [hcm]
  have hconj : (starRingEnd ℂ) (dpolyS s a t)
      = ∑ n ∈ s,
          (starRingEnd ℂ) (a n)
            * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ))) := by
    unfold dpolyS
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hconj]
  unfold dpolyS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  have hexp :
      Complex.exp (Complex.I * (t : ℂ) * (Real.log m : ℂ))
          * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))
        = Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [show (starRingEnd ℂ) (a n)
          * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))
          * (a m * Complex.exp (Complex.I * (t : ℂ) * (Real.log m : ℂ)))
        = (starRingEnd ℂ) (a n) * a m
            * (Complex.exp (Complex.I * (t : ℂ) * (Real.log m : ℂ))
                * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) from by ring,
      hexp]

/-- The `s`-indexed twin of `dirichlet_poly_l2_expand`: the mean-square integral expands
into the double sum of term integrals. -/
theorem dpolyS_l2_expand (s : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) :
    ((∫ t in (-T)..T, ‖dpolyS s a t‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ s, ∑ m ∈ s,
          (starRingEnd ℂ) (a n) * a m
            * ∫ t in (-T)..T,
                Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))) := by
  have hInt1 : ∀ n m : ℕ, IntervalIntegrable
      (fun t => (starRingEnd ℂ) (a n) * a m
        * Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))))
      volume (-T) T := by
    intro n m; apply Continuous.intervalIntegrable; fun_prop
  have hInt2 : ∀ n ∈ s, IntervalIntegrable
      (fun t => ∑ m ∈ s, (starRingEnd ℂ) (a n) * a m
        * Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))))
      volume (-T) T := by
    intro n _; apply Continuous.intervalIntegrable
    apply continuous_finsetSum; intro m _; fun_prop
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [sq_norm_dpolyS_eq s a]
  rw [intervalIntegral.integral_finsetSum hInt2]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun m _ => hInt1 n m)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_const_mul]

/-- The `s`-indexed twin of `dirichlet_poly_l2_diagonal`: the diagonal is exactly
`2T·∑_{n∈s}‖aₙ‖²`, and the off-diagonal is the `erase`-indexed remainder. -/
theorem dpolyS_l2_diagonal (s : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) :
    ((∫ t in (-T)..T, ‖dpolyS s a t‖ ^ 2 : ℝ) : ℂ)
      = ((2 * T : ℝ) : ℂ) * ∑ n ∈ s, ((‖a n‖ ^ 2 : ℝ) : ℂ)
        + ∑ n ∈ s, ∑ m ∈ s.erase n,
            (starRingEnd ℂ) (a n) * a m
              * ∫ t in (-T)..T,
                  Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))) := by
  rw [dpolyS_l2_expand]
  have hdiag : ∀ n : ℕ, (∫ t in (-T)..T,
      Complex.exp (Complex.I * (t : ℂ) * ((Real.log n : ℂ) - (Real.log n : ℂ))))
      = ((2 * T : ℝ) : ℂ) := by
    intro n
    simp only [sub_self, mul_zero, Complex.exp_zero]
    rw [intervalIntegral.integral_const, Complex.real_smul, mul_one]
    push_cast; ring
  have hconjsq : ∀ n : ℕ, (starRingEnd ℂ) (a n) * a n = ((‖a n‖ ^ 2 : ℝ) : ℂ) := by
    intro n; rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  have hsplit : ∀ n ∈ s,
      (∑ m ∈ s, (starRingEnd ℂ) (a n) * a m
          * ∫ t in (-T)..T,
              Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))))
        = ((‖a n‖ ^ 2 : ℝ) : ℂ) * ((2 * T : ℝ) : ℂ)
          + ∑ m ∈ s.erase n, (starRingEnd ℂ) (a n) * a m
              * ∫ t in (-T)..T,
                  Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))) := by
    intro n hn
    rw [← Finset.add_sum_erase _ _ hn]
    congr 1
    rw [hdiag n, hconjsq n]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- The pure Hilbert bilinear form at log-frequencies, over an arbitrary index set:
`H(x) = ∑_{n∈s} ∑_{m∈s, m≠n} xₘ·conj(xₙ)/(log m − log n)`. -/
noncomputable def hilbertLogSumS (s : Finset ℕ) (x : ℕ → ℂ) : ℂ :=
  ∑ n ∈ s, ∑ m ∈ s.erase n,
    x m * (starRingEnd ℂ) (x n) / ((Real.log m : ℂ) - (Real.log n : ℂ))

/-- `hilbertLogSumS s = hilbertLogSum N` at `s = Finset.Icc 1 N`. -/
lemma hilbertLogSumS_Icc (N : ℕ) (x : ℕ → ℂ) :
    hilbertLogSumS (Finset.Icc 1 N) x = hilbertLogSum N x := rfl

/-- **The sin-free off-diagonal identity at `s`.**  `i · OD = H(c) − H(d)` for the twisted
coefficients `c = twistPos a T`, `d = twistNeg a T`.  The per-term algebra is the landed
`offdiag_term_hilbert` (already index-set agnostic); only the index set moves. -/
lemma offdiag_eq_hilbertS (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (a : ℕ → ℂ) (T : ℝ) :
    Complex.I * (∑ n ∈ s, ∑ m ∈ s.erase n,
        (starRingEnd ℂ) (a n) * a m
          * ∫ t in (-T)..T,
              Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))))
      = hilbertLogSumS s (twistPos a T) - hilbertLogSumS s (twistNeg a T) := by
  rw [Finset.mul_sum, hilbertLogSumS, hilbertLogSumS, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≠ n := Finset.ne_of_mem_erase hm
  have hm1 : 1 ≤ m := hs m (Finset.mem_of_mem_erase hm)
  have hn1 : 1 ≤ n := hs n hn
  exact offdiag_term_hilbert a T hmn hm1 hn1

/-- Montgomery–Vaughan at `s`, with the separation `δ` a parameter: the hard core
`MVHilbertUniform` is already stated for an arbitrary `Finset ℕ` and arbitrary real
frequencies, so this is a pure specialization. -/
lemma norm_hilbertLogSumS_le (hMV : MVHilbertUniform) (s : Finset ℕ) (x : ℕ → ℂ) {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |Real.log i - Real.log j|) :
    ‖hilbertLogSumS s x‖ ≤ Real.pi / δ * ∑ n ∈ s, ‖x n‖ ^ 2 := by
  have h := hMV s (fun k => Real.log k) x δ hδ hgap
  simpa [hilbertLogSumS] using h

/-- **S2 — the Finset L² mean-value theorem** (`(2T + 2π/δ)` shape).  For any finite
`s ⊆ [1, ∞)` whose log-frequencies are `δ`-separated,
`∫_{-T}^{T} ‖∑_{n∈s} aₙ n^{it}‖² dt ≤ (2T + 2π/δ)·∑_{n∈s}‖aₙ‖²`.

The `Icc`-shaped `dirichlet_poly_l2_mvt` is the case `s = Icc 1 N`, `δ = 1/N`
(then `2π/δ = 2πN ≤ 20N`).  The point of the re-cut is that on an arithmetic
progression mod `q` the separation is `q/N`, so `2π/δ = 2πN/q ≤ 7N/q`. -/
theorem dpolyS_l2_mvt (hMV : MVHilbertUniform) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    (a : ℕ → ℂ) (T : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |Real.log i - Real.log j|) :
    (∫ t in (-T)..T, ‖dpolyS s a t‖ ^ 2)
      ≤ (2 * T + 2 * Real.pi / δ) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  set P := ∑ n ∈ s, ‖a n‖ ^ 2 with hPdef
  have hPnn : 0 ≤ P := by rw [hPdef]; exact Finset.sum_nonneg (fun n _ => by positivity)
  have hdiag := dpolyS_l2_diagonal s a T
  have hIeq := offdiag_eq_hilbertS s hs a T
  set S := ∫ t in (-T)..T, ‖dpolyS s a t‖ ^ 2 with hSdef
  set OD := ∑ n ∈ s, ∑ m ∈ s.erase n,
      (starRingEnd ℂ) (a n) * a m
        * ∫ t in (-T)..T,
            Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ)))
    with hODdef
  have hsumcast : (∑ n ∈ s, ((‖a n‖ ^ 2 : ℝ) : ℂ)) = ((P : ℝ) : ℂ) := by
    rw [hPdef, Complex.ofReal_sum]
  rw [hsumcast] at hdiag
  have hODreal : OD = ((S - 2 * T * P : ℝ) : ℂ) := by
    have h2 : OD = (S : ℂ) - ((2 * T : ℝ) : ℂ) * ((P : ℝ) : ℂ) := by rw [hdiag]; ring
    rw [h2]; push_cast; ring
  have hnormOD : ‖OD‖ = ‖(S - 2 * T * P : ℝ)‖ := by rw [hODreal, Complex.norm_real]
  have hnorm_I : ‖OD‖
      = ‖hilbertLogSumS s (twistPos a T) - hilbertLogSumS s (twistNeg a T)‖ := by
    rw [← hIeq, norm_mul, Complex.norm_I, one_mul]
  have hc := norm_hilbertLogSumS_le hMV s (twistPos a T) hδ hgap
  have hd := norm_hilbertLogSumS_le hMV s (twistNeg a T) hδ hgap
  have hsumc : (∑ n ∈ s, ‖twistPos a T n‖ ^ 2) = P := by
    rw [hPdef]; exact Finset.sum_congr rfl (fun n _ => by rw [norm_twistPos])
  have hsumd : (∑ n ∈ s, ‖twistNeg a T n‖ ^ 2) = P := by
    rw [hPdef]; exact Finset.sum_congr rfl (fun n _ => by rw [norm_twistNeg])
  rw [hsumc] at hc
  rw [hsumd] at hd
  have hOD_bound : ‖OD‖ ≤ 2 * (Real.pi / δ) * P := by
    rw [hnorm_I]
    calc ‖hilbertLogSumS s (twistPos a T) - hilbertLogSumS s (twistNeg a T)‖
        ≤ ‖hilbertLogSumS s (twistPos a T)‖ + ‖hilbertLogSumS s (twistNeg a T)‖ :=
          norm_sub_le _ _
      _ ≤ Real.pi / δ * P + Real.pi / δ * P := add_le_add hc hd
      _ = 2 * (Real.pi / δ) * P := by ring
  have hSle : S - 2 * T * P ≤ 2 * (Real.pi / δ) * P := by
    have h1 : S - 2 * T * P ≤ ‖(S - 2 * T * P : ℝ)‖ := Real.le_norm_self _
    rw [← hnormOD] at h1
    linarith [h1, hOD_bound]
  calc S ≤ 2 * T * P + 2 * (Real.pi / δ) * P := by linarith [hSle]
    _ = (2 * T + 2 * Real.pi / δ) * P := by ring

/-- **S2, unconditional.**  `dpolyS_l2_mvt` with the Montgomery–Vaughan hypothesis
discharged by `mvHilbertUniform_holds`. -/
theorem dpolyS_l2_mvt_final (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (a : ℕ → ℂ) (T : ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |Real.log i - Real.log j|) :
    (∫ t in (-T)..T, ‖dpolyS s a t‖ ^ 2)
      ≤ (2 * T + 2 * Real.pi / δ) * ∑ n ∈ s, ‖a n‖ ^ 2 :=
  dpolyS_l2_mvt mvHilbertUniform_holds s hs a T hδ hgap

/-- The mean square over a *symmetric* window is invariant under `t ↦ −t`, i.e. under the
`n^{it}` ↔ `n^{-it}` sign convention (CATCH #B: the corpus's large-value callers write
`P(1−it)`, KMT's Lemma 6.2 writes `n^{+it}`).  Immediate from
`intervalIntegral.integral_comp_neg`. -/
lemma dpolyS_meanSq_reflect (s : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) :
    (∫ t in (-T)..T, ‖dpolyS s a (-t)‖ ^ 2) = ∫ t in (-T)..T, ‖dpolyS s a t‖ ^ 2 := by
  rw [intervalIntegral.integral_comp_neg (fun t => ‖dpolyS s a t‖ ^ 2), neg_neg]

end Salt.MR
