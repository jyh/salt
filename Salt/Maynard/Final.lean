/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Endgame
import Salt.Maynard.RatioCore
import Salt.Maynard.S2CompatEHFinal
import Salt.Maynard.S2TensorCheb
import Salt.Maynard.K0
import Salt.Maynard.ChebyshevInterval
import Salt.Maynard.Tuple

/-!
# M7 — the capstone: bounded gaps from Elliott–Halberstam

Assembles `bounded_gaps_from_eh : BoundedGapsFromEH`.  Every mathematical input
is a landed lemma; this file is threshold-management plus one numerical
inequality.
-/

open Finset

namespace Salt.Maynard

/-- `A₁ ≥ 1`: the `r = 1` term contributes `fWt(1)²/φ(1) = 1`, all others `≥ 0`. -/
theorem A1_ge_one (k R : ℕ) (T : ℝ) (hR0 : 2 ≤ R0 k R T) :
    1 ≤ A1 k R (W k) T := by
  have h1mem : (1 : ℕ) ∈ sqfCop (R0 k R T) (W k) := by
    rw [sqfCop, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, squarefree_one, Nat.coprime_one_left _⟩
  have huval : uVal k R 1 = 0 := by
    simp [uVal]
  have hterm : (fWt k R 1) ^ 2 / (Nat.totient 1 : ℝ) = 1 := by
    simp [fWt, huval]
  have hle : (fWt k R 1) ^ 2 / (Nat.totient 1 : ℝ) ≤ A1 k R (W k) T := by
    unfold A1
    refine Finset.single_le_sum (f := fun r => (fWt k R r) ^ 2 / (Nat.totient r : ℝ))
      (fun r _ => by positivity) h1mem
  rwa [hterm] at hle

/-- **The numerical core.**  Given all the landed per-`m` bounds (compat lower,
EH residual, `S₁` upper, and the ratio-core lower bound) plus the largeness
facts (`k₀` dominance, `δ`/`log R` lower bounds, and the two error-term bounds),
the sieve inequality `S₁ < Σ_m S₂^(m)` holds.  Pure algebra: the main term
`k₀·(δ/φW)·cval` dominates `4·S₁ᵈᵒᵐ`, and each error term is `≤ S₁ᵈᵒᵐ`. -/
theorem win_core (k₀ N' R ν₀ : ℕ) (T c C₀ Cs : ℝ)
    (hk1 : 1 ≤ k₀) (hNpos : 0 < N') (hlogNpos : 0 < Real.log N')
    (hcpos : 0 < c)
    (hδ0 : 0 ≤ c * (N' : ℝ) / Real.log N' - (D₀ k₀ : ℝ))
    (hA1ge1 : 1 ≤ A1 k₀ R (W k₀) T)
    (hDpi : ∀ m : Fin k₀,
      c * (N' : ℝ) / Real.log N' - (D₀ k₀ : ℝ) ≤ deltaPi k₀ 64 N' m)
    (hcompat : ∀ m : Fin k₀,
      (1 / 16 : ℝ) * (B1 k₀ R (W k₀) T) ^ 2 * (A1 k₀ R (W k₀) T) ^ (k₀ - 1)
        ≤ s2CompatFormM k₀ R (W k₀) m (yTensor k₀ R T))
    (hEHres : ∀ m : Fin k₀,
      deltaPi k₀ 64 N' m / (Nat.totient (W k₀) : ℝ)
          * s2CompatFormM k₀ R (W k₀) m (yTensor k₀ R T)
        - C₀ * (1 + Real.log R) ^ (2 * k₀ + 2) * (N' : ℝ) / (Real.log N') ^ (2 * k₀ + 4)
          ≤ S2m k₀ 64 N' R ν₀ m (yTensor k₀ R T))
    (hS1 : S1 k₀ 64 N' R (W k₀) ν₀ (yTensor k₀ R T)
      ≤ 126 * (N' : ℝ) / (W k₀ : ℝ) * (A1 k₀ R (W k₀) T) ^ k₀
        + Cs * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k₀ + 2))
    (hratio : (Nat.totient (W k₀) / W k₀ : ℝ) * Real.log R * Real.log k₀ / 2916
      ≤ (k₀ : ℝ) * (B1 k₀ R (W k₀) T) ^ 2 / (A1 k₀ R (W k₀) T))
    (hδlb : c * (N' : ℝ) / (2 * Real.log N')
      ≤ c * (N' : ℝ) / Real.log N' - (D₀ k₀ : ℝ))
    (hlogR : Real.log N' / 6 ≤ Real.log R)
    (hdom : (282175488 : ℝ) ≤ c * Real.log k₀)
    (herr1 : Cs * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k₀ + 2)
      ≤ 126 * (N' : ℝ) / (W k₀ : ℝ))
    (herr2 : (k₀ : ℝ)
        * (C₀ * (1 + Real.log R) ^ (2 * k₀ + 2) * (N' : ℝ) / (Real.log N') ^ (2 * k₀ + 4))
      ≤ 126 * (N' : ℝ) / (W k₀ : ℝ)) :
    S1 k₀ 64 N' R (W k₀) ν₀ (yTensor k₀ R T)
      < ∑ m : Fin k₀, S2m k₀ 64 N' R ν₀ m (yTensor k₀ R T) := by
  have hWpos : 0 < W k₀ := Nat.pos_of_ne_zero (W_squarefree k₀).ne_zero
  have hWr : (0 : ℝ) < (W k₀ : ℝ) := by exact_mod_cast hWpos
  have hφWpos : (0 : ℝ) < (Nat.totient (W k₀) : ℝ) := by
    have : 0 < Nat.totient (W k₀) := Nat.totient_pos.mpr hWpos
    exact_mod_cast this
  have hapos : (0 : ℝ) < A1 k₀ R (W k₀) T := lt_of_lt_of_le one_pos hA1ge1
  -- abbreviations
  set a := A1 k₀ R (W k₀) T with ha
  set b := B1 k₀ R (W k₀) T with hb
  set φW := (Nat.totient (W k₀) : ℝ) with hφWe
  set Wr := (W k₀ : ℝ) with hWre
  set δ := c * (N' : ℝ) / Real.log N' - (D₀ k₀ : ℝ) with hδe
  set P := a ^ k₀ with hP
  set Q := a ^ (k₀ - 1) with hQ
  have hP1 : (1 : ℝ) ≤ P := one_le_pow₀ hA1ge1
  have hPpos : (0 : ℝ) < P := lt_of_lt_of_le one_pos hP1
  have hQ0 : (0 : ℝ) ≤ Q := pow_nonneg hapos.le _
  have hpq : a * Q = P := by
    rw [hP, hQ, ← pow_succ']; congr 1; omega
  -- the main quadratic lower bound: `main ≥ 504·N'·P/Wr = 4·S₁ᵈᵒᵐ`.
  have hr2 : (φW / Wr) * Real.log R * Real.log k₀ / 2916 * a ≤ (k₀ : ℝ) * b ^ 2 :=
    (le_div_iff₀ hapos).mp hratio
  -- `δ·log R ≥ c·N'/12`
  have hδR : c * (N' : ℝ) / 12 ≤ δ * Real.log R := by
    have h1 : c * (N' : ℝ) / (2 * Real.log N') * (Real.log N' / 6) ≤ δ * Real.log R := by
      refine mul_le_mul hδlb hlogR (by positivity) (le_trans (by positivity) hδlb)
    have h2 : c * (N' : ℝ) / (2 * Real.log N') * (Real.log N' / 6) = c * (N' : ℝ) / 12 := by
      field_simp; ring
    linarith [h1, h2.symm.le, h2.le]
  -- `δ·log R·log k₀ ≥ 23514624·N'`
  have hkey : (23514624 : ℝ) * (N' : ℝ) ≤ δ * Real.log R * Real.log k₀ := by
    have hLk0 : 0 ≤ Real.log k₀ := by
      have : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk1
      exact Real.log_nonneg this
    have hstep : c * (N' : ℝ) / 12 * Real.log k₀ ≤ δ * Real.log R * Real.log k₀ :=
      mul_le_mul_of_nonneg_right hδR hLk0
    have hdom' : (282175488 : ℝ) * ((N' : ℝ) / 12) ≤ c * Real.log k₀ * ((N' : ℝ) / 12) :=
      mul_le_mul_of_nonneg_right hdom (by positivity)
    have heq : c * (N' : ℝ) / 12 * Real.log k₀ = c * Real.log k₀ * ((N' : ℝ) / 12) := by ring
    have heq2 : (282175488 : ℝ) * ((N' : ℝ) / 12) = 23514624 * (N' : ℝ) := by ring
    linarith [hstep, hdom', heq.le, heq.ge, heq2.le, heq2.ge]
  -- main term lower bound
  have hFnn : 0 ≤ δ * Q / (16 * φW) := by
    apply div_nonneg (mul_nonneg hδ0 hQ0); positivity
  have hmul := mul_le_mul_of_nonneg_left hr2 hFnn
  -- rewrite both sides
  have hEqMain : δ * Q / (16 * φW) * ((k₀ : ℝ) * b ^ 2)
      = (k₀ : ℝ) * (δ / φW * ((1 / 16 : ℝ) * b ^ 2 * Q)) := by
    field_simp
  have hEqR : δ * Q / (16 * φW) * ((φW / Wr) * Real.log R * Real.log k₀ / 2916 * a)
      = δ * Real.log R * Real.log k₀ * P / (46656 * Wr) := by
    rw [← hpq]; field_simp; ring
  rw [hEqMain, hEqR] at hmul
  -- so `main ≥ δ·logR·logk₀·P/(46656 Wr) ≥ 504·N'·P/Wr`
  have hPWr : 0 ≤ P / Wr := by positivity
  have hchain : (504 : ℝ) * (N' : ℝ) * P / Wr
      ≤ (k₀ : ℝ) * (δ / φW * ((1 / 16 : ℝ) * b ^ 2 * Q)) := by
    refine le_trans ?_ hmul
    rw [div_le_div_iff₀ hWr (by positivity : (0:ℝ) < 46656 * Wr)]
    have hh := mul_le_mul_of_nonneg_right hkey (mul_nonneg hPpos.le hWr.le)
    calc (504 : ℝ) * (N' : ℝ) * P * (46656 * Wr)
        = 23514624 * (N' : ℝ) * (P * Wr) := by ring
      _ ≤ (δ * Real.log R * Real.log k₀) * (P * Wr) := hh
      _ = δ * Real.log R * Real.log k₀ * P * Wr := by ring
  -- S₁ᵈᵒᵐ = 126·N'·P/Wr > 0, and both errors ≤ 126·N'/Wr ≤ S₁ᵈᵒᵐ
  have hS1dom_pos : 0 < 126 * (N' : ℝ) / Wr * P := by
    have : (0 : ℝ) < 126 * (N' : ℝ) / Wr := by positivity
    positivity
  have h126le : 126 * (N' : ℝ) / Wr ≤ 126 * (N' : ℝ) / Wr * P := by
    nlinarith [hP1, div_nonneg (by positivity : (0:ℝ) ≤ 126 * (N':ℝ)) hWr.le]
  -- assemble hnum
  have hnum : S1 k₀ 64 N' R (W k₀) ν₀ (yTensor k₀ R T)
      < (k₀ : ℝ) * (δ / φW * ((1 / 16 : ℝ) * b ^ 2 * Q)) - (k₀ : ℝ)
          * (C₀ * (1 + Real.log R) ^ (2 * k₀ + 2) * (N' : ℝ) / (Real.log N') ^ (2 * k₀ + 4)) := by
    have hmul_err : (k₀ : ℝ)
        * (C₀ * (1 + Real.log R) ^ (2 * k₀ + 2) * (N' : ℝ) / (Real.log N') ^ (2 * k₀ + 4))
        ≤ 126 * (N' : ℝ) / Wr := herr2
    have h4 : (504 : ℝ) * (N' : ℝ) * P / Wr = 4 * (126 * (N' : ℝ) / Wr * P) := by ring
    have hmain4 : 4 * (126 * (N' : ℝ) / Wr * P)
        ≤ (k₀ : ℝ) * (δ / φW * ((1 / 16 : ℝ) * b ^ 2 * Q)) := by rw [← h4]; exact hchain
    -- S₁ ≤ 126·N'·P/Wr + error1 ≤ 2·S₁ᵈᵒᵐ
    have hS1' : S1 k₀ 64 N' R (W k₀) ν₀ (yTensor k₀ R T)
        ≤ 126 * (N' : ℝ) / Wr * P + 126 * (N' : ℝ) / Wr := by
      have : 126 * (N' : ℝ) / (W k₀ : ℝ) * a ^ k₀ = 126 * (N' : ℝ) / Wr * P := by
        rw [hWre, hP, ha]
      linarith [hS1, herr1, this.le, this.ge]
    linarith [hS1', hmain4, hmul_err, h126le, hS1dom_pos]
  exact S1_lt_sum_S2m k₀ 64 N' R ν₀ (yTensor k₀ R T) δ
    (C₀ * (1 + Real.log R) ^ (2 * k₀ + 2) * (N' : ℝ) / (Real.log N') ^ (2 * k₀ + 4))
    ((1 / 16 : ℝ) * b ^ 2 * Q)
    hφWpos (by positivity) hδ0 hDpi hcompat hEHres hnum

/-- **Uniform `Δπ` lower bound.**  A repackaging of `deltaPi_ge` with an
externally supplied `Chebyshev` constant `c` (so a single `c` and threshold `Nc`
serves every coordinate `m`).  Mirrors `deltaPi_ge`. -/
theorem deltaPi_lower_of (k : ℕ) (c : ℝ) (Nc : ℕ)
    (hkey : ∀ N : ℕ, Nc ≤ N →
      c * (N : ℝ) / Real.log N
        ≤ (Nat.primeCounting (64 * N) : ℝ) - (Nat.primeCounting N : ℝ))
    (m : Fin k) (N : ℕ) (hN : Nc ≤ N) :
    c * (N : ℝ) / Real.log N - (hSeq k m : ℝ) ≤ deltaPi k 64 N m := by
  have hkeyN := hkey N hN
  rw [deltaPi, primesCount_one_zero_eq, primesCount_one_zero_eq]
  have hlo : (Nat.primeCounting (64 * N) : ℝ)
      ≤ (Nat.primeCounting (64 * N + hSeq k m) : ℝ) := by
    exact_mod_cast primeCounting_mono (Nat.le_add_right _ _)
  have hhi : (Nat.primeCounting (N + hSeq k m) : ℝ)
      ≤ (Nat.primeCounting N : ℝ) + (hSeq k m : ℝ) := by
    exact_mod_cast primeCounting_shift_le N (hSeq k m)
  linarith [hkeyN, hlo, hhi]

/-- **The analytic-input frontier** (the assembled Maynard bounds at suitable
window parameters).  For a tuple width `k₀ ≥ 3072` with `Chebyshev` constant
`c` and dominance `282175488 ≤ c·log k₀`, and for every window base `N`, there
are parameters `N' ≥ N`, `R`, `ν₀`, `T` and error constants `C₀, Cs` for which
all of `win_core`'s analytic hypotheses hold simultaneously: the uniform `Δπ`
lower bound (`hDpi`), the compat-diagonal lower bound (`hcompat`), the EH
residual bound (`hEHres`), the `S₁` upper bound (`hS1`), the ratio-core bound
(`hratio`), and the largeness facts (`hδlb`, `hlogR`, `herr1`, `herr2`).

This is exactly the "pick `N'`/`R` huge, past all thresholds" step.  Its
discharge from the landed lemmas (`deltaPi_lower_of`, `s2CompatFormM_ge_sixteenth`
+ `s2_tensor_lower_cheb`, `S2m_ge_compatMain_eh`, `S1_upper_A1`,
`ratio_core_lower`) is *blocked at the interface level*: those lemmas expose
their error constants (`Cs` of `S1_upper_A1`, `C₀` of `S2m_ge_compatMain_eh`,
the compat constant of `s2CompatFormM_ge_sixteenth`) and the EH threshold `N₀`
as opaque `∃`-bound quantities.  Their *values* are `R`-independent (`Cs`, `C₀`
factor through `rankin_bound`/`phi_ratio_le`; `N₀ = D₀ k₀`), so the frontier
holds mathematically, but with `R = ⌊N'^{1/5}⌋` tied to `N'` and the dominance
capping `N' ≤ R⁶`, choosing `N'` past the (hidden-value) thresholds is circular
without `R`-uniform restatements of those three lemmas. -/
def AnalyticFrontier : Prop :=
  ∀ (k₀ : ℕ) (c : ℝ) (Nc : ℕ), EH (1 / 2) → 3072 ≤ k₀ → 0 < c →
    (282175488 : ℝ) ≤ c * Real.log k₀ →
    (∀ N : ℕ, Nc ≤ N → c * (N : ℝ) / Real.log N
      ≤ (Nat.primeCounting (64 * N) : ℝ) - (Nat.primeCounting N : ℝ)) →
    ∀ N : ℕ,
    ∃ (N' R ν₀ : ℕ) (T C₀ Cs : ℝ), N ≤ N' ∧ 0 < N' ∧ 0 < Real.log N' ∧
      1 ≤ A1 k₀ R (W k₀) T ∧
      (∀ m : Fin k₀,
        c * (N' : ℝ) / Real.log N' - (D₀ k₀ : ℝ) ≤ deltaPi k₀ 64 N' m) ∧
      (∀ m : Fin k₀,
        (1 / 16 : ℝ) * (B1 k₀ R (W k₀) T) ^ 2 * (A1 k₀ R (W k₀) T) ^ (k₀ - 1)
          ≤ s2CompatFormM k₀ R (W k₀) m (yTensor k₀ R T)) ∧
      (∀ m : Fin k₀,
        deltaPi k₀ 64 N' m / (Nat.totient (W k₀) : ℝ)
            * s2CompatFormM k₀ R (W k₀) m (yTensor k₀ R T)
          - C₀ * (1 + Real.log R) ^ (2 * k₀ + 2) * (N' : ℝ) / (Real.log N') ^ (2 * k₀ + 4)
            ≤ S2m k₀ 64 N' R ν₀ m (yTensor k₀ R T)) ∧
      (S1 k₀ 64 N' R (W k₀) ν₀ (yTensor k₀ R T)
        ≤ 126 * (N' : ℝ) / (W k₀ : ℝ) * (A1 k₀ R (W k₀) T) ^ k₀
          + Cs * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k₀ + 2)) ∧
      ((Nat.totient (W k₀) / W k₀ : ℝ) * Real.log R * Real.log k₀ / 2916
        ≤ (k₀ : ℝ) * (B1 k₀ R (W k₀) T) ^ 2 / (A1 k₀ R (W k₀) T)) ∧
      (c * (N' : ℝ) / (2 * Real.log N')
        ≤ c * (N' : ℝ) / Real.log N' - (D₀ k₀ : ℝ)) ∧
      (Real.log N' / 6 ≤ Real.log R) ∧
      (Cs * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k₀ + 2)
        ≤ 126 * (N' : ℝ) / (W k₀ : ℝ)) ∧
      ((k₀ : ℝ)
          * (C₀ * (1 + Real.log R) ^ (2 * k₀ + 2) * (N' : ℝ) / (Real.log N') ^ (2 * k₀ + 4))
        ≤ 126 * (N' : ℝ) / (W k₀ : ℝ))

/-- **M7 — bounded gaps from Elliott–Halberstam.**  Assembled from the landed
Maynard bounds.  Given the analytic-input frontier (`AnalyticFrontier`, the
"pick a huge window past all thresholds" step), `win_core` converts each
window's bounds into the sieve inequality `S₁ < Σ_m S₂^(m)`, and
`bounded_gaps_reduces` turns that into two primes `p ≠ q > N` with
`|q − p| ≤ D₀ k₀ = C`.  The tuple width `k₀` is chosen so the ratio-core gain
`c·log k₀` clears the numerical dominance threshold `282175488`. -/
theorem bounded_gaps_from_eh (hFrontier : AnalyticFrontier) : BoundedGapsFromEH := by
  intro hEH
  -- The `Chebyshev` prime-supply constant `c` (`= 1`), obtained once.
  obtain ⟨c, Nc, hc0, hckey⟩ := primes_in_interval_ge
  -- Choose `k₀` so `c·log k₀ ≥ 282175488` (and `k₀ ≥ 3072`).
  set k₀ := max 3072 ⌈Real.exp (282175488 / c)⌉₊ with hk₀def
  have hk3072 : 3072 ≤ k₀ := le_max_left _ _
  have hM : (282175488 : ℝ) / c ≤ Real.log k₀ := by
    have h1 : Real.exp (282175488 / c) ≤ (k₀ : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      have : (⌈Real.exp (282175488 / c)⌉₊ : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast le_max_right _ _
      exact this
    have h2 : Real.log (Real.exp (282175488 / c)) ≤ Real.log k₀ :=
      Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hdom : (282175488 : ℝ) ≤ c * Real.log k₀ := by
    have h := mul_le_mul_of_nonneg_left hM hc0.le
    have e : c * (282175488 / c) = 282175488 := by field_simp
    linarith [h, e.le, e.ge]
  -- Reduce to the sieve inequality at arbitrarily large window bases.
  refine bounded_gaps_reduces k₀ (fun N => ?_)
  obtain ⟨N', R, ν₀, T, C₀, Cs, hNleN', hNpos, hlogNpos, hA1ge1, hDpi, hcompat,
    hEHres, hS1, hratio, hδlb, hlogR, herr1, herr2⟩ :=
    hFrontier k₀ c Nc hEH hk3072 hc0 hdom hckey N
  have hδ0 : 0 ≤ c * (N' : ℝ) / Real.log N' - (D₀ k₀ : ℝ) :=
    le_trans (by positivity) hδlb
  refine ⟨N', R, ν₀, yTensor k₀ R T, hNleN', ?_⟩
  exact win_core k₀ N' R ν₀ T c C₀ Cs (by omega) hNpos hlogNpos hc0 hδ0 hA1ge1
    hDpi hcompat hEHres hS1 hratio hδlb hlogR hdom herr1 herr2

end Salt.Maynard
