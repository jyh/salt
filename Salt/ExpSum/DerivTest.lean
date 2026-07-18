/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.Basic
import Salt.ExpSum.VdCorput2

/-!
# van der Corput's higher-derivative test (the A^{k-2} iteration)

This file iterates the Weyl–van der Corput A-process (`weyl_vdC_expSum`,
`Salt/ExpSum/Basic.lean`) onto the landed second-derivative test
(`vdC_second_derivative`, `Salt/ExpSum/VdCorput2.lean`) to obtain the
**third-derivative test** (`vdC_third_derivative`): one A-step onto the base.

## Mathematics (Graham–Kolesnik Thm 2.6, the `k = 3` case)

For a phase `f : ℤ → ℝ` whose third differences obey `λ ≤ Δ³f ≤ cλ` on the
range (`0 < λ`, `1 ≤ c`), the exponential sum over a window of length `N`
satisfies, with `L = N`,
`‖∑ eR (f n)‖ ≤ 12·√c·(L·λ^{1/6} + L^{1/2}·λ^{-1/6})`.
The exponents `1/6 = 1/(2^3-2)` and `1/2 = 1 - 2^{2-3}` are the classical
`k = 3` shape; the `c`-grade `c^{1/2} = c^{2^{2-k}}` is the honest one.

### The engine

The A-process bounds `‖S‖²` by an average over shifts `|h| ≤ H` of the
*differenced* sums `S_h = ∑ eR (f(n+h) − f n)`.  The differenced phase
`g_h(n) = f(n+h) − f(n)` has **second** differences
`Δ²g_h(n) = Δ²f(n+h) − Δ²f(n) = ∑_{j<h} Δ³f(n+j) ∈ [hλ, hcλ]`
(for `h ≥ 1`), so the *second*-derivative test bounds each `‖S_h‖`.  Negative
shifts are handled by conjugation symmetry (`‖S_{-h}‖ = ‖S_h‖`).  Choosing
`H ≍ λ^{-1/3}` balances the resulting three-term estimate.

The paper arithmetic (the H-optimization) is worked in the docstring of
`vdC_third_derivative`.

## Base conversions

The A-process is `ℤ`-indexed with the character `eR`; the base test is
`ℕ`-indexed with the (byte-identical) character `eK`.  Section 1 pays this
impedance once: `eR_eq_eK` bridges the characters and `vdC_2nd_ZR` reindexes
the base test to an `ℤ`-window with `eR`.
-/

namespace Salt.ExpSum

open Real Finset
open scoped ComplexConjugate

/-! ## Section 1 — the character bridge and the `ℤ`/`eR` second-derivative test -/

/-- The two additive characters coincide (`Basic.eR` and `Kusmin.eK` have the
same underlying `Complex.exp`). -/
lemma eR_eq_eK (x : ℝ) : eR x = eK x := by
  rw [eR, eK]; congr 1; push_cast; ring

/-- **Second-derivative test, `ℤ`-indexed with `eR`.**  A reindexing wrapper of
`vdC_second_derivative`: for `φ : ℤ → ℝ` on an integer window `Ioc a b` whose
second differences lie in `[μ, cμ]`, the exponential sum obeys the same bound
with `L = b − a`.  This is the form the A-process consumes at the base. -/
theorem vdC_2nd_ZR (φ : ℤ → ℝ) (a b : ℤ) (μ c : ℝ)
    (hab : a ≤ b) (hμ : 0 < μ) (hc : 1 ≤ c)
    (hlb : ∀ n : ℤ, a < n → n < b → μ ≤ (φ (n + 2) - φ (n + 1)) - (φ (n + 1) - φ n))
    (hub : ∀ n : ℤ, a < n → n < b → (φ (n + 2) - φ (n + 1)) - (φ (n + 1) - φ n) ≤ c * μ) :
    ‖∑ n ∈ Finset.Ioc a b, eR (φ n)‖
      ≤ 8 * (c * ((b : ℝ) - a) * Real.sqrt μ + 1 / Real.sqrt μ) := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, b = a + M := ⟨(b - a).toNat, by omega⟩
  set F : ℕ → ℝ := fun j => φ (a + (j : ℤ)) with hF
  -- reindex the integer window to `Ioc (0:ℕ) M` and switch `eR → eK`
  have hsum : ∑ n ∈ Finset.Ioc a (a + (M : ℤ)), eR (φ n)
      = ∑ j ∈ Finset.Ioc (0 : ℕ) M, eK (F j) := by
    apply Finset.sum_nbij' (i := fun n : ℤ => (n - a).toNat) (j := fun k : ℕ => a + (k : ℤ))
    · intro n hn; rw [Finset.mem_Ioc] at hn ⊢; omega
    · intro k hk; rw [Finset.mem_Ioc] at hk ⊢; omega
    · intro n hn; rw [Finset.mem_Ioc] at hn; omega
    · intro k hk; rw [Finset.mem_Ioc] at hk; omega
    · intro n hn; rw [Finset.mem_Ioc] at hn
      rw [eR_eq_eK]; simp only [hF]
      rw [show (a + ((n - a).toNat : ℤ)) = n from by omega]
  rw [hsum]
  -- transfer the second-difference hypotheses to `F` on `Ioc (0:ℕ) M`
  have hlb' : ∀ n : ℕ, 0 < n → n < M →
      μ ≤ (F (n + 1 + 1) - F (n + 1)) - (F (n + 1) - F n) := by
    intro n hn0 hnM
    have h := hlb (a + (n : ℤ)) (by omega) (by omega)
    simp only [hF]
    have e0 : a + ((n : ℤ)) + 1 = a + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    have e1 : a + ((n : ℤ)) + 2 = a + ((n + 1 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e0, e1] at h; exact h
  have hub' : ∀ n : ℕ, 0 < n → n < M →
      (F (n + 1 + 1) - F (n + 1)) - (F (n + 1) - F n) ≤ c * μ := by
    intro n hn0 hnM
    have h := hub (a + (n : ℤ)) (by omega) (by omega)
    simp only [hF]
    have e0 : a + ((n : ℤ)) + 1 = a + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    have e1 : a + ((n : ℤ)) + 2 = a + ((n + 1 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e0, e1] at h; exact h
  have h2 := vdC_second_derivative (f := F) (a := 0) (b := M) (Nat.zero_le M) hμ hc hlb' hub'
  have hMcast : ((M : ℝ) - (0 : ℕ)) = ((a + (M : ℤ) : ℤ) : ℝ) - (a : ℝ) := by push_cast; ring
  calc ‖∑ j ∈ Finset.Ioc (0 : ℕ) M, eK (F j)‖
      ≤ 8 * (c * ((M : ℝ) - ((0 : ℕ) : ℝ)) * Real.sqrt μ + 1 / Real.sqrt μ) := h2
    _ = 8 * (c * (((a + (M : ℤ) : ℤ) : ℝ) - a) * Real.sqrt μ + 1 / Real.sqrt μ) := by
        rw [hMcast]

/-! ## Section 2 — power sums and the symmetric shift split -/

/-- `∑_{i<H} √(i+1) ≤ H·√H` (crude: `H` terms each `≤ √H`). -/
lemma sum_sqrt_range (H : ℕ) :
    ∑ i ∈ Finset.range H, Real.sqrt ((i : ℝ) + 1) ≤ (H : ℝ) * Real.sqrt H := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_range_succ]
      have hmono : Real.sqrt (H : ℝ) ≤ Real.sqrt ((H : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      have hmono2 : Real.sqrt ((H : ℝ) + 1) = Real.sqrt ((H : ℕ) + 1 : ℕ) := by
        push_cast; ring_nf
      have hnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
      push_cast
      nlinarith [ih, hmono, Real.sqrt_nonneg ((H : ℝ) + 1), Real.sqrt_nonneg (H : ℝ),
        mul_le_mul_of_nonneg_left hmono hnn]

/-- `∑_{i<H} 1/√(i+1) ≤ 2·√H` (telescoping `1/√(H+1) ≤ 2(√(H+1)−√H)` via AM–GM). -/
lemma sum_inv_sqrt_range (H : ℕ) :
    ∑ i ∈ Finset.range H, 1 / Real.sqrt ((i : ℝ) + 1) ≤ 2 * Real.sqrt H := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_range_succ]
      set s := Real.sqrt (H : ℝ) with hs
      set t := Real.sqrt ((H : ℝ) + 1) with ht
      have hs2 : s ^ 2 = (H : ℝ) := Real.sq_sqrt (Nat.cast_nonneg H)
      have ht2 : t ^ 2 = (H : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have htpos : 0 < t := Real.sqrt_pos.mpr (by positivity)
      have hsnn : 0 ≤ s := Real.sqrt_nonneg _
      have hkey : 1 / t ≤ 2 * (t - s) := by
        rw [div_le_iff₀ htpos]
        nlinarith [sq_nonneg (t - s), hs2, ht2, htpos, hsnn]
      have hcast : Real.sqrt ((H : ℝ) + 1) = Real.sqrt ((H + 1 : ℕ) : ℝ) := by
        push_cast; ring_nf
      calc ∑ i ∈ Finset.range H, 1 / Real.sqrt ((i : ℝ) + 1) + 1 / Real.sqrt ((H : ℝ) + 1)
          ≤ 2 * s + 1 / t := by rw [← ht]; linarith [ih]
        _ ≤ 2 * t := by linarith [hkey]
        _ = 2 * Real.sqrt ((H + 1 : ℕ) : ℝ) := by rw [ht, hcast]

/-- Splitting a symmetric shift sum `∑_{|h|≤H}` into the `h = 0` term and the
positive shifts paired with their negatives. -/
lemma sum_Icc_symm {M : Type*} [AddCommMonoid M] (H : ℕ) (φ : ℤ → M) :
    ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), φ h
      = φ 0 + ∑ i ∈ Finset.range H, (φ ((i : ℤ) + 1) + φ (-((i : ℤ) + 1))) := by
  induction H with
  | zero => simp
  | succ H ih =>
      have hset : Finset.Icc (-((H : ℤ) + 1)) ((H : ℤ) + 1)
          = insert ((H : ℤ) + 1) (insert (-((H : ℤ) + 1)) (Finset.Icc (-(H : ℤ)) (H : ℤ))) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnm1 : -((H : ℤ) + 1) ∉ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
        simp only [Finset.mem_Icc]; omega
      have hnm2 : ((H : ℤ) + 1)
          ∉ insert (-((H : ℤ) + 1)) (Finset.Icc (-(H : ℤ)) (H : ℤ)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have hcast : (-(((H + 1 : ℕ)) : ℤ)) = -((H : ℤ) + 1) := by push_cast; ring
      have hcast2 : (((H + 1 : ℕ)) : ℤ) = (H : ℤ) + 1 := by push_cast; ring
      rw [hcast, hcast2, hset, Finset.sum_insert hnm2, Finset.sum_insert hnm1, ih,
        Finset.sum_range_succ]
      abel

/-! ## Section 3 — integer step accumulation

`diff2_accum` accumulates a per-step bound `F(m+1) − F m ≤ β` into
`F(n+k) − F n ≤ k·β`.  Applied with `F = Δ²f` (whose steps are the third
differences `Δ³f`) it yields the `[hλ, hcλ]` window bounds the base test
consumes; the lower bound comes from running it on `−Δ²f`. -/

lemma diff2_accum (F : ℤ → ℝ) {lo hi : ℤ} {β : ℝ}
    (hstep : ∀ m, lo ≤ m → m < hi → F (m + 1) - F m ≤ β)
    (n : ℤ) (hn : lo ≤ n) :
    ∀ k : ℕ, n + (k : ℤ) ≤ hi → F (n + (k : ℤ)) - F n ≤ (k : ℝ) * β := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have h1 : F (n + (k : ℤ)) - F n ≤ (k : ℝ) * β := ih (by push_cast at hk ⊢; omega)
      have h2 : F (n + (k : ℤ) + 1) - F (n + (k : ℤ)) ≤ β :=
        hstep (n + (k : ℤ)) (by omega) (by push_cast at hk; omega)
      have he : n + ((k + 1 : ℕ) : ℤ) = n + (k : ℤ) + 1 := by push_cast; ring
      have hc : ((k + 1 : ℕ) : ℝ) * β = (k : ℝ) * β + β := by push_cast; ring
      rw [he, hc]; linarith

/-! ## Section 4 — the per-shift bound and the third-derivative test -/

/-- **Conjugation symmetry.**  The negative-shift differenced sum is the complex
conjugate of the positive-shift one, so their norms agree. -/
lemma Gh_norm_symm (f : ℤ → ℝ) (a : ℤ) (N : ℕ) (h : ℤ) :
    ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter (fun n => n + (-h) ∈ Finset.Ioc a (a + (N : ℤ))),
        eR (f (n + (-h)) - f n)‖
      = ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter (fun n => n + h ∈ Finset.Ioc a (a + (N : ℤ))),
        eR (f (n + h) - f n)‖ := by
  have hAconj :
      (∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter (fun n => n + (-h) ∈ Finset.Ioc a (a + (N : ℤ))),
          eR (f (n + (-h)) - f n))
        = conj (∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
            (fun n => n + h ∈ Finset.Ioc a (a + (N : ℤ))), eR (f (n + h) - f n)) := by
    rw [map_sum]
    apply Finset.sum_nbij' (i := fun n : ℤ => n - h) (j := fun m : ℤ => m + h)
    · intro n hn; simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢; omega
    · intro m hm; simp only [Finset.mem_filter, Finset.mem_Ioc] at hm ⊢; omega
    · intro n _; show n - h + h = n; ring
    · intro m _; show m + h - h = m; ring
    · intro n _; show eR (f (n + (-h)) - f n) = conj (eR (f (n - h + h) - f (n - h)))
      rw [conj_eR]; congr 1
      rw [show n + (-h) = n - h from by ring, show n - h + h = n from by ring]; ring
  rw [hAconj, RCLike.norm_conj]

/-- **The optimization core** (pure arithmetic).  With `u = λ^{1/6}`, `t = √H`,
`p = u·t` clamped to `p² ≤ 1 ≤ 2p²` by the choice `H ≍ λ^{-1/3}`, the three-term
A-process estimate collapses to `144·c·(N²u² + N/u²)`. -/
lemma opt_core (Nr u t c : ℝ) (hN : 0 ≤ Nr) (hu : 0 < u) (ht : 0 < t) (hc : 1 ≤ c)
    (hp1 : (u * t) ^ 2 ≤ 1) (hp2 : 1 ≤ 2 * (u * t) ^ 2) :
    2 * Nr ^ 2 / t ^ 2 + 32 * c * Nr ^ 2 * u ^ 3 * t + 64 * Nr / (u ^ 3 * t)
      ≤ 144 * c * (Nr ^ 2 * u ^ 2 + Nr / u ^ 2) := by
  set p := u * t with hp
  have hppos : 0 < p := mul_pos hu ht
  have hu2 : 0 < u ^ 2 := by positivity
  have ht2 : 0 < t ^ 2 := by positivity
  have hu3t : 0 < u ^ 3 * t := by positivity
  have hple1 : p ≤ 1 := by nlinarith [hp1, hppos]
  have hphalf : 1 / 2 ≤ p := by nlinarith [hp1, hp2, hple1, hppos]
  have hupt : u ^ 3 * t = u ^ 2 * p := by rw [hp]; ring
  -- three sub-bounds
  have hb1 : 2 * Nr ^ 2 / t ^ 2 ≤ 4 * Nr ^ 2 * u ^ 2 := by
    rw [div_le_iff₀ ht2]
    nlinarith [hp2, sq_nonneg Nr,
      mul_nonneg (sq_nonneg Nr) (by nlinarith [hp2] : (0 : ℝ) ≤ 2 * (u * t) ^ 2 - 1)]
  have hb2 : 32 * c * Nr ^ 2 * u ^ 3 * t ≤ 32 * c * Nr ^ 2 * u ^ 2 := by
    rw [show 32 * c * Nr ^ 2 * u ^ 3 * t = 32 * c * Nr ^ 2 * (u ^ 3 * t) from by ring, hupt]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c) (sq_nonneg Nr))
      (le_of_lt hu2)) (by linarith [hple1] : (0 : ℝ) ≤ 1 - p)]
  have hb3 : 64 * Nr / (u ^ 3 * t) ≤ 128 * Nr / u ^ 2 := by
    rw [div_le_div_iff₀ hu3t hu2, hupt]
    nlinarith [mul_nonneg (mul_nonneg hN (le_of_lt hu2))
      (by linarith [hphalf] : (0 : ℝ) ≤ 2 * p - 1)]
  -- combine
  have hNu2 : 0 ≤ Nr / u ^ 2 := div_nonneg hN (le_of_lt hu2)
  have hNr2u2 : 0 ≤ Nr ^ 2 * u ^ 2 := by positivity
  have hsum : 2 * Nr ^ 2 / t ^ 2 + 32 * c * Nr ^ 2 * u ^ 3 * t + 64 * Nr / (u ^ 3 * t)
      ≤ 4 * Nr ^ 2 * u ^ 2 + 32 * c * Nr ^ 2 * u ^ 2 + 128 * Nr / u ^ 2 :=
    add_le_add (add_le_add hb1 hb2) hb3
  have hrhs : 4 * Nr ^ 2 * u ^ 2 + 32 * c * Nr ^ 2 * u ^ 2 + 128 * Nr / u ^ 2
      ≤ 144 * c * (Nr ^ 2 * u ^ 2 + Nr / u ^ 2) := by
    rw [mul_div_assoc]
    nlinarith [hc, hNu2, hNr2u2, mul_nonneg (by linarith : (0 : ℝ) ≤ c - 1) hNr2u2,
      mul_nonneg (by linarith : (0 : ℝ) ≤ c - 1) hNu2]
  linarith [hsum, hrhs]

/-- **Per-shift bound.**  For a positive shift `1 ≤ h ≤ N`, the differenced sum
`∑ eR (f(n+h) − f n)` over the overlap window is bounded by the second-derivative
test applied to `g_h`, whose second differences lie in `[hλ, hcλ]`. -/
lemma Gh_bound_pos (f : ℤ → ℝ) (a : ℤ) (N : ℕ) (lam c : ℝ)
    (hlam : 0 < lam) (hc : 1 ≤ c)
    (h3_lb : ∀ n : ℤ, a < n → n < a + N → lam ≤ f (n+3) - 3 * f (n+2) + 3 * f (n+1) - f n)
    (h3_ub : ∀ n : ℤ, a < n → n < a + N → f (n+3) - 3 * f (n+2) + 3 * f (n+1) - f n ≤ c * lam)
    (h : ℤ) (hh1 : 1 ≤ h) (hhN : h ≤ (N : ℤ)) :
    ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter (fun n => n + h ∈ Finset.Ioc a (a + (N : ℤ))),
        eR (f (n + h) - f n)‖
      ≤ 8 * (c * (N : ℝ) * Real.sqrt ((h : ℝ) * lam) + 1 / Real.sqrt ((h : ℝ) * lam)) := by
  set D2f : ℤ → ℝ := fun m => f (m + 2) - 2 * f (m + 1) + f m with hD2f
  -- the third-difference identity `Δ²f(m+1) − Δ²f m = Δ³f m`
  have hid : ∀ m : ℤ, D2f (m + 1) - D2f m = f (m+3) - 3 * f (m+2) + 3 * f (m+1) - f m := by
    intro m; simp only [hD2f]
    rw [show m + 1 + 2 = m + 3 from by ring, show m + 1 + 1 = m + 2 from by ring]; ring
  -- the connection `Δ²g_h(n) = Δ²f(n+h) − Δ²f n`
  have hconn : ∀ n : ℤ,
      (((f ((n+2) + h) - f (n+2)) - (f ((n+1) + h) - f (n+1)))
        - ((f ((n+1) + h) - f (n+1)) - (f (n + h) - f n)))
        = D2f (n + h) - D2f n := by
    intro n; simp only [hD2f]
    rw [show n + 2 + h = n + h + 2 from by ring, show n + 1 + h = n + h + 1 from by ring]; ring
  -- rewrite the filter to the sub-window `Ioc a (a + N − h)`
  have hfilter : (Finset.Ioc a (a + (N : ℤ))).filter (fun n => n + h ∈ Finset.Ioc a (a + (N : ℤ)))
      = Finset.Ioc a (a + (N : ℤ) - h) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_Ioc]; omega
  rw [hfilter]
  -- positivity facts
  have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < h)
  have hmu : 0 < (h : ℝ) * lam := mul_pos hhpos hlam
  -- accumulation setup
  set k₀ : ℕ := h.toNat with hk0
  have hk0Z : (k₀ : ℤ) = h := Int.toNat_of_nonneg (by omega)
  have hk0R : (k₀ : ℝ) = (h : ℝ) := by exact_mod_cast hk0Z
  -- per-step bounds for the accumulation
  have hstepU : ∀ m, a + 1 ≤ m → m < a + (N : ℤ) → D2f (m + 1) - D2f m ≤ c * lam := by
    intro m hm1 hm2; rw [hid m]; exact h3_ub m (by omega) hm2
  have hstepL : ∀ m, a + 1 ≤ m → m < a + (N : ℤ) →
      (fun x => -(D2f x)) (m + 1) - (fun x => -(D2f x)) m ≤ -lam := by
    intro m hm1 hm2; simp only
    rw [show -(D2f (m+1)) - -(D2f m) = -(D2f (m+1) - D2f m) from by ring, hid m]
    linarith [h3_lb m (by omega) hm2]
  -- the second-derivative test hypotheses for `g_h`
  have hlbφ : ∀ n : ℤ, a < n → n < a + (N : ℤ) - h →
      (h : ℝ) * lam ≤ ((fun m => f (m + h) - f m) (n+2) - (fun m => f (m + h) - f m) (n+1))
        - ((fun m => f (m + h) - f m) (n+1) - (fun m => f (m + h) - f m) n) := by
    intro n hn1 hn2; simp only; rw [hconn n]
    have hacc : -(D2f (n + (k₀ : ℤ))) - -(D2f n) ≤ (k₀ : ℝ) * (-lam) :=
      diff2_accum (fun x => -(D2f x)) hstepL n (by omega) k₀ (by rw [hk0Z]; omega)
    rw [hk0Z, hk0R] at hacc; linarith
  have hubφ : ∀ n : ℤ, a < n → n < a + (N : ℤ) - h →
      ((fun m => f (m + h) - f m) (n+2) - (fun m => f (m + h) - f m) (n+1))
        - ((fun m => f (m + h) - f m) (n+1) - (fun m => f (m + h) - f m) n)
        ≤ c * ((h : ℝ) * lam) := by
    intro n hn1 hn2; simp only; rw [hconn n]
    have hacc := diff2_accum D2f hstepU n (by omega) k₀ (by rw [hk0Z]; omega)
    rw [hk0Z, hk0R] at hacc; nlinarith [hacc]
  -- apply the base test on the sub-window
  have hbase := vdC_2nd_ZR (fun m => f (m + h) - f m) a (a + (N : ℤ) - h) ((h : ℝ) * lam) c
    (by omega) hmu hc hlbφ hubφ
  refine le_trans hbase ?_
  have hlen : (((a + (N : ℤ) - h : ℤ)) : ℝ) - (a : ℝ) ≤ (N : ℝ) := by push_cast; linarith
  have hsnn : 0 ≤ Real.sqrt ((h : ℝ) * lam) := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := by linarith
  gcongr

/-- Subadditivity of `√` (used to split `√(N²u² + N/u²)`). -/
lemma Real_sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have key : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt key
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

/-- **The third-derivative test, main regime.**  Assuming a shift parameter `H`
with `1 ≤ H ≤ N` chosen so that `H ≤ λ^{-1/3} < H+1` (i.e. `H = ⌊λ^{-1/3}⌋₊`),
the A-process + second-derivative test give the target bound. -/
lemma vdC_third_main (f : ℤ → ℝ) (a : ℤ) (N : ℕ) (lam c : ℝ)
    (hlam : 0 < lam) (hc : 1 ≤ c)
    (h3_lb : ∀ n : ℤ, a < n → n < a + N → lam ≤ f (n+3) - 3 * f (n+2) + 3 * f (n+1) - f n)
    (h3_ub : ∀ n : ℤ, a < n → n < a + N → f (n+3) - 3 * f (n+2) + 3 * f (n+1) - f n ≤ c * lam)
    (H : ℕ) (hH1 : 1 ≤ H) (hHN : H ≤ N)
    (hHlo : (H : ℝ) ≤ lam ^ (-1/3 : ℝ)) (hHhi : lam ^ (-1/3 : ℝ) < (H : ℝ) + 1) :
    ‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖
      ≤ 12 * Real.sqrt c * ((N : ℝ) * lam ^ (1/6 : ℝ)
          + (N : ℝ) ^ (1/2 : ℝ) * lam ^ (-(1/6) : ℝ)) := by
  classical
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hHRpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH1
  have hHR1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hslam : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  set u := lam ^ (1/6 : ℝ) with hu
  have hupos : 0 < u := Real.rpow_pos_of_pos hlam _
  set t := Real.sqrt (H : ℝ) with ht
  have htpos : 0 < t := Real.sqrt_pos.mpr hHRpos
  have ht2 : (H : ℝ) = t ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg H)).symm
  -- rpow identities
  have hu2eq : u ^ 2 = lam ^ (1/3 : ℝ) := by
    rw [hu, ← Real.rpow_natCast (lam ^ (1/6 : ℝ)) 2, ← Real.rpow_mul (le_of_lt hlam)]; norm_num
  have hu3eq : u ^ 3 = Real.sqrt lam := by
    rw [hu, ← Real.rpow_natCast (lam ^ (1/6 : ℝ)) 3, ← Real.rpow_mul (le_of_lt hlam),
      Real.sqrt_eq_rpow]; norm_num
  have hlaminv : lam ^ (-1/3 : ℝ) * lam ^ (1/3 : ℝ) = 1 := by
    rw [← Real.rpow_add hlam]; norm_num
  -- clamping facts p² ≤ 1 ≤ 2p²  (p = u·t)
  have hut2 : (u * t) ^ 2 = lam ^ (1/3 : ℝ) * (H : ℝ) := by rw [mul_pow, hu2eq, ← ht2]
  have hl3pos : (0 : ℝ) < lam ^ (1/3 : ℝ) := Real.rpow_pos_of_pos hlam _
  have hp1 : (u * t) ^ 2 ≤ 1 := by
    rw [hut2]
    nlinarith [hHlo, hlaminv, hl3pos, mul_nonneg (le_of_lt hl3pos)
      (by linarith [hHlo] : (0 : ℝ) ≤ lam ^ (-1/3 : ℝ) - (H : ℝ))]
  have hp2 : 1 ≤ 2 * (u * t) ^ 2 := by
    rw [hut2]
    nlinarith [hHhi, hlaminv, hl3pos, hHR1, mul_nonneg (le_of_lt hl3pos)
      (by linarith [hHhi, hHR1] : (0 : ℝ) ≤ 2 * (H : ℝ) - lam ^ (-1/3 : ℝ))]
  -- the A-process
  have hA := weyl_vdC_expSum f a N H hH1 hHN
  set base : ℤ → ℝ :=
    fun m => 8 * (c * (N : ℝ) * Real.sqrt ((m : ℝ) * lam) + 1 / Real.sqrt ((m : ℝ) * lam))
    with hbasedef
  -- symmetric split of the shift sum
  have hsymm := sum_Icc_symm H (fun h : ℤ =>
    ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter (fun n => n + h ∈ Finset.Ioc a (a + (N : ℤ))),
        eR (f (n + h) - f n)‖)
  -- the `h = 0` term
  have hphi0 : ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
        (fun n => n + (0 : ℤ) ∈ Finset.Ioc a (a + (N : ℤ))), eR (f (n + 0) - f n)‖ ≤ (N : ℝ) := by
    calc ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
              (fun n => n + (0 : ℤ) ∈ Finset.Ioc a (a + (N : ℤ))), eR (f (n + 0) - f n)‖
        ≤ ∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
              (fun n => n + (0 : ℤ) ∈ Finset.Ioc a (a + (N : ℤ))), ‖eR (f (n + 0) - f n)‖ :=
          norm_sum_le _ _
      _ = ∑ _n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
              (fun n => n + (0 : ℤ) ∈ Finset.Ioc a (a + (N : ℤ))), (1 : ℝ) := by simp only [norm_eR]
      _ = (((Finset.Ioc a (a + (N : ℤ))).filter
              (fun n => n + (0 : ℤ) ∈ Finset.Ioc a (a + (N : ℤ)))).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ((Finset.Ioc a (a + (N : ℤ))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = (N : ℝ) := by
          rw [Int.card_Ioc, show a + (N : ℤ) - a = (N : ℤ) from by ring]; simp
  -- the paired terms:  ‖G(i+1)‖ + ‖G(-(i+1))‖ ≤ 2·base(i+1)
  have hpair : ∀ i ∈ Finset.range H,
      ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
          (fun n => n + ((i : ℤ) + 1) ∈ Finset.Ioc a (a + (N : ℤ))),
          eR (f (n + ((i : ℤ) + 1)) - f n)‖
        + ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
          (fun n => n + (-((i : ℤ) + 1)) ∈ Finset.Ioc a (a + (N : ℤ))),
          eR (f (n + (-((i : ℤ) + 1))) - f n)‖
      ≤ 2 * base ((i : ℤ) + 1) := by
    intro i hi
    have hiH : i < H := Finset.mem_range.mp hi
    rw [Gh_norm_symm f a N ((i : ℤ) + 1)]
    have hb : ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
        (fun n => n + ((i : ℤ) + 1) ∈ Finset.Ioc a (a + (N : ℤ))),
          eR (f (n + ((i : ℤ) + 1)) - f n)‖ ≤ base ((i : ℤ) + 1) :=
      Gh_bound_pos f a N lam c hlam hc h3_lb h3_ub ((i : ℤ) + 1) (by omega) (by omega)
    linarith [hb]
  -- assemble the shift-sum bound
  have hsumle : ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
        ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
            (fun n => n + h ∈ Finset.Ioc a (a + (N : ℤ))), eR (f (n + h) - f n)‖
      ≤ (N : ℝ) + 2 * ∑ i ∈ Finset.range H, base ((i : ℤ) + 1) := by
    rw [hsymm, Finset.mul_sum]
    have hpairsum : ∑ i ∈ Finset.range H,
        (‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
            (fun n => n + ((i : ℤ) + 1) ∈ Finset.Ioc a (a + (N : ℤ))),
            eR (f (n + ((i : ℤ) + 1)) - f n)‖
          + ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
            (fun n => n + (-((i : ℤ) + 1)) ∈ Finset.Ioc a (a + (N : ℤ))),
            eR (f (n + (-((i : ℤ) + 1))) - f n)‖)
        ≤ ∑ i ∈ Finset.range H, 2 * base ((i : ℤ) + 1) := Finset.sum_le_sum hpair
    linarith [hphi0, hpairsum]
  -- power-sum bound on ∑ base
  have hbase_split : ∑ i ∈ Finset.range H, base ((i : ℤ) + 1)
      = 8 * c * (N : ℝ) * Real.sqrt lam * (∑ i ∈ Finset.range H, Real.sqrt ((i : ℝ) + 1))
        + 8 * (1 / Real.sqrt lam) * (∑ i ∈ Finset.range H, 1 / Real.sqrt ((i : ℝ) + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hbasedef]
    rw [show (((i : ℤ) + 1 : ℤ) : ℝ) * lam = ((i : ℝ) + 1) * lam from by push_cast; ring,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)]
    have h1 : Real.sqrt ((i : ℝ) + 1) ≠ 0 := by positivity
    have h2 : Real.sqrt lam ≠ 0 := ne_of_gt hslam
    field_simp
  have hbasesum : ∑ i ∈ Finset.range H, base ((i : ℤ) + 1)
      ≤ 8 * c * (N : ℝ) * Real.sqrt lam * ((H : ℝ) * Real.sqrt (H : ℝ))
        + 8 * (1 / Real.sqrt lam) * (2 * Real.sqrt (H : ℝ)) := by
    rw [hbase_split]
    have hcoef1 : (0 : ℝ) ≤ 8 * c * (N : ℝ) * Real.sqrt lam :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc0) hN) (Real.sqrt_nonneg _)
    have hcoef2 : (0 : ℝ) ≤ 8 * (1 / Real.sqrt lam) := by positivity
    exact add_le_add (mul_le_mul_of_nonneg_left (sum_sqrt_range H) hcoef1)
      (mul_le_mul_of_nonneg_left (sum_inv_sqrt_range H) hcoef2)
  -- ‖S‖² ≤ P, then opt_core
  have hbase_nn : (0 : ℝ) ≤ ∑ i ∈ Finset.range H, base ((i : ℤ) + 1) :=
    Finset.sum_nonneg fun i _ => by
      simp only [hbasedef]
      have : (0 : ℝ) ≤ c * (N : ℝ) * Real.sqrt (((i : ℤ) + 1 : ℤ) * lam : ℝ) :=
        mul_nonneg (mul_nonneg hc0 hN) (Real.sqrt_nonneg _)
      have h2 : (0 : ℝ) ≤ 1 / Real.sqrt (((i : ℤ) + 1 : ℤ) * lam : ℝ) := by positivity
      linarith
  have hfactor : ((N : ℝ) + (H : ℝ)) / ((H : ℝ) + 1) ≤ 2 * (N : ℝ) / (H : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hHRpos]
    have hHNr : (H : ℝ) ≤ (N : ℝ) := by exact_mod_cast hHN
    nlinarith [hHNr, hHRpos, hN]
  have hQeq : (2 * (N : ℝ) / (H : ℝ)) * ((N : ℝ) + 2 * (8 * c * (N : ℝ) * Real.sqrt lam
        * ((H : ℝ) * Real.sqrt (H : ℝ)) + 8 * (1 / Real.sqrt lam) * (2 * Real.sqrt (H : ℝ))))
      = 2 * (N : ℝ) ^ 2 / t ^ 2 + 32 * c * (N : ℝ) ^ 2 * u ^ 3 * t
        + 64 * (N : ℝ) / (u ^ 3 * t) := by
    rw [← ht, ← hu3eq, ht2]
    have htne : t ≠ 0 := ne_of_gt htpos
    have hune : u ≠ 0 := ne_of_gt hupos
    field_simp
    ring
  have hP : ‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖ ^ 2
      ≤ 144 * c * ((N : ℝ) ^ 2 * u ^ 2 + (N : ℝ) / u ^ 2) := by
    calc ‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖ ^ 2
        ≤ ((N : ℝ) + (H : ℝ)) / ((H : ℝ) + 1)
            * ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
              ‖∑ n ∈ (Finset.Ioc a (a + (N : ℤ))).filter
                  (fun n => n + h ∈ Finset.Ioc a (a + (N : ℤ))), eR (f (n + h) - f n)‖ := hA
      _ ≤ ((N : ℝ) + (H : ℝ)) / ((H : ℝ) + 1)
            * ((N : ℝ) + 2 * ∑ i ∈ Finset.range H, base ((i : ℤ) + 1)) :=
          mul_le_mul_of_nonneg_left hsumle (by positivity)
      _ ≤ (2 * (N : ℝ) / (H : ℝ)) * ((N : ℝ) + 2 * (8 * c * (N : ℝ) * Real.sqrt lam
              * ((H : ℝ) * Real.sqrt (H : ℝ))
              + 8 * (1 / Real.sqrt lam) * (2 * Real.sqrt (H : ℝ)))) :=
          mul_le_mul hfactor (by linarith [hbasesum]) (by linarith [hbase_nn]) (by positivity)
      _ = 2 * (N : ℝ) ^ 2 / t ^ 2 + 32 * c * (N : ℝ) ^ 2 * u ^ 3 * t
            + 64 * (N : ℝ) / (u ^ 3 * t) := hQeq
      _ ≤ 144 * c * ((N : ℝ) ^ 2 * u ^ 2 + (N : ℝ) / u ^ 2) :=
          opt_core (N : ℝ) u t c hN hupos htpos hc hp1 hp2
  -- take square roots
  have hune : u ≠ 0 := ne_of_gt hupos
  have hsub : Real.sqrt ((N : ℝ) ^ 2 * u ^ 2 + (N : ℝ) / u ^ 2)
      ≤ (N : ℝ) * u + (N : ℝ) ^ (1/2 : ℝ) * u⁻¹ := by
    have e1 : Real.sqrt ((N : ℝ) ^ 2 * u ^ 2) = (N : ℝ) * u := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hN, Real.sqrt_sq (le_of_lt hupos)]
    have e2 : Real.sqrt ((N : ℝ) / u ^ 2) = (N : ℝ) ^ (1/2 : ℝ) * u⁻¹ := by
      rw [Real.sqrt_div hN, Real.sqrt_sq (le_of_lt hupos), Real.sqrt_eq_rpow, div_eq_mul_inv]
    calc Real.sqrt ((N : ℝ) ^ 2 * u ^ 2 + (N : ℝ) / u ^ 2)
        ≤ Real.sqrt ((N : ℝ) ^ 2 * u ^ 2) + Real.sqrt ((N : ℝ) / u ^ 2) :=
          Real_sqrt_add_le _ _ (by positivity) (by positivity)
      _ = (N : ℝ) * u + (N : ℝ) ^ (1/2 : ℝ) * u⁻¹ := by rw [e1, e2]
  have hinv6 : lam ^ (-(1/6) : ℝ) = u⁻¹ := by
    rw [hu, ← Real.rpow_neg (le_of_lt hlam)]
  have h144 : Real.sqrt (144 : ℝ) = 12 := by
    rw [show (144 : ℝ) = 12 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 12)]
  have hsplit : Real.sqrt (144 * c * ((N : ℝ) ^ 2 * u ^ 2 + (N : ℝ) / u ^ 2))
      = 12 * Real.sqrt c * Real.sqrt ((N : ℝ) ^ 2 * u ^ 2 + (N : ℝ) / u ^ 2) := by
    rw [show (144 : ℝ) * c * ((N : ℝ) ^ 2 * u ^ 2 + (N : ℝ) / u ^ 2)
          = 144 * (c * ((N : ℝ) ^ 2 * u ^ 2 + (N : ℝ) / u ^ 2)) from by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 144), h144, Real.sqrt_mul hc0]
    ring
  rw [hinv6]
  calc ‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖
      = Real.sqrt (‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (144 * c * ((N : ℝ) ^ 2 * u ^ 2 + (N : ℝ) / u ^ 2)) := Real.sqrt_le_sqrt hP
    _ = 12 * Real.sqrt c * Real.sqrt ((N : ℝ) ^ 2 * u ^ 2 + (N : ℝ) / u ^ 2) := hsplit
    _ ≤ 12 * Real.sqrt c * ((N : ℝ) * u + (N : ℝ) ^ (1/2 : ℝ) * u⁻¹) :=
        mul_le_mul_of_nonneg_left hsub (by positivity)

/-- **van der Corput's third-derivative test.**  For a phase `f : ℤ → ℝ` whose
third differences obey `λ ≤ Δ³f ≤ cλ` on the range `a < n < a+N` (`0 < λ`,
`1 ≤ c`), the exponential sum over the length-`N` window is bounded by
`12·√c·(N·λ^{1/6} + N^{1/2}·λ^{-1/6})`.

The exponents `1/6 = 1/(2³−2)` and `1/2 = 1 − 2^{2−3}` are the classical `k = 3`
Graham–Kolesnik shape; the `c`-grade `√c = c^{2^{2−k}}` is the honest one.  One
A-process step reduces `‖S‖²` to the second-derivative test applied to the
shifted phases `g_h`, with `H ≍ λ^{-1/3}` optimizing the resulting estimate. -/
theorem vdC_third_derivative (f : ℤ → ℝ) (a : ℤ) (N : ℕ) (lam c : ℝ)
    (hlam : 0 < lam) (hc : 1 ≤ c)
    (h3_lb : ∀ n : ℤ, a < n → n < a + N → lam ≤ f (n+3) - 3 * f (n+2) + 3 * f (n+1) - f n)
    (h3_ub : ∀ n : ℤ, a < n → n < a + N → f (n+3) - 3 * f (n+2) + 3 * f (n+1) - f n ≤ c * lam) :
    ‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖
      ≤ 12 * Real.sqrt c * ((N : ℝ) * lam ^ (1/6 : ℝ)
          + (N : ℝ) ^ (1/2 : ℝ) * lam ^ (-(1/6) : ℝ)) := by
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hsqc1 : (1 : ℝ) ≤ Real.sqrt c := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hc
  have hu_pos : (0 : ℝ) < lam ^ (1/6 : ℝ) := Real.rpow_pos_of_pos hlam _
  have hinv_pos : (0 : ℝ) < lam ^ (-(1/6) : ℝ) := Real.rpow_pos_of_pos hlam _
  have hxpos : (0 : ℝ) < lam ^ (-1/3 : ℝ) := Real.rpow_pos_of_pos hlam _
  -- the trivial norm bound
  have htriv : ‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖ ≤ (N : ℝ) := by
    calc ‖∑ n ∈ Finset.Ioc a (a + (N : ℤ)), eR (f n)‖
        ≤ ∑ n ∈ Finset.Ioc a (a + (N : ℤ)), ‖eR (f n)‖ := norm_sum_le _ _
      _ = ∑ _n ∈ Finset.Ioc a (a + (N : ℤ)), (1 : ℝ) := by simp only [norm_eR]
      _ = ((Finset.Ioc a (a + (N : ℤ))).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = (N : ℝ) := by rw [Int.card_Ioc, show a + (N : ℤ) - a = (N : ℤ) from by ring]; simp
  by_cases hmain : 1 ≤ lam ^ (-1/3 : ℝ) ∧ lam ^ (-1/3 : ℝ) ≤ (N : ℝ)
  · -- main regime: `1 ≤ λ^{-1/3} ≤ N`, take `H = ⌊λ^{-1/3}⌋₊`
    have hH1 : 1 ≤ ⌊lam ^ (-1/3 : ℝ)⌋₊ := (Nat.one_le_floor_iff _).mpr hmain.1
    have hHle : (⌊lam ^ (-1/3 : ℝ)⌋₊ : ℝ) ≤ lam ^ (-1/3 : ℝ) := Nat.floor_le (le_of_lt hxpos)
    have hHlt : lam ^ (-1/3 : ℝ) < (⌊lam ^ (-1/3 : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hHN : ⌊lam ^ (-1/3 : ℝ)⌋₊ ≤ N := by
      have : (⌊lam ^ (-1/3 : ℝ)⌋₊ : ℝ) ≤ (N : ℝ) := le_trans hHle hmain.2
      exact_mod_cast this
    exact vdC_third_main f a N lam c hlam hc h3_lb h3_ub _ hH1 hHN hHle hHlt
  · -- trivial regime: `λ^{-1/3} < 1` or `λ^{-1/3} > N`; the trivial bound wins
    rw [not_and_or, not_le, not_le] at hmain
    refine le_trans htriv ?_
    rcases hmain with hlt | hgt
    · -- `λ^{-1/3} < 1` forces `λ^{1/6} ≥ 1`
      have hu2eq : (lam ^ (1/6 : ℝ)) ^ 2 = lam ^ (1/3 : ℝ) := by
        rw [← Real.rpow_natCast (lam ^ (1/6 : ℝ)) 2, ← Real.rpow_mul (le_of_lt hlam)]; norm_num
      have hxu2mul : lam ^ (-1/3 : ℝ) * (lam ^ (1/6 : ℝ)) ^ 2 = 1 := by
        rw [hu2eq, ← Real.rpow_add hlam]; norm_num
      have hu1 : (1 : ℝ) ≤ lam ^ (1/6 : ℝ) := by nlinarith [hxu2mul, hlt, hu_pos]
      have hcu : (1 : ℝ) ≤ Real.sqrt c * lam ^ (1/6 : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hsqc1) (sub_nonneg.mpr hu1), hsqc1, hu1]
      have hnn2 : (0 : ℝ) ≤ (N : ℝ) ^ (1/2 : ℝ) * lam ^ (-(1/6) : ℝ) := by positivity
      have hcum1 : (0 : ℝ) ≤ Real.sqrt c * lam ^ (1/6 : ℝ) - 1 := by linarith [hcu]
      nlinarith [hcu, hN, hnn2, mul_nonneg hN hcum1]
    · -- `λ^{-1/3} > N` forces `λ^{-1/6} ≥ N^{1/2}`
      have hinv_eq : lam ^ (-(1/6) : ℝ) = (lam ^ (-1/3 : ℝ)) ^ (1/2 : ℝ) := by
        rw [← Real.rpow_mul (le_of_lt hlam)]; norm_num
      have hNhalf : (N : ℝ) ^ (1/2 : ℝ) * (N : ℝ) ^ (1/2 : ℝ) = (N : ℝ) := by
        rw [← Real.sqrt_eq_rpow]; exact Real.mul_self_sqrt hN
      have hxge : (N : ℝ) ^ (1/2 : ℝ) ≤ (lam ^ (-1/3 : ℝ)) ^ (1/2 : ℝ) :=
        Real.rpow_le_rpow hN (le_of_lt hgt) (by norm_num)
      have hprod : (N : ℝ) ≤ (N : ℝ) ^ (1/2 : ℝ) * lam ^ (-(1/6) : ℝ) := by
        rw [hinv_eq]
        calc (N : ℝ) = (N : ℝ) ^ (1/2 : ℝ) * (N : ℝ) ^ (1/2 : ℝ) := hNhalf.symm
          _ ≤ (N : ℝ) ^ (1/2 : ℝ) * (lam ^ (-1/3 : ℝ)) ^ (1/2 : ℝ) :=
              mul_le_mul_of_nonneg_left hxge (by positivity)
      have hAnn : (0 : ℝ) ≤ (N : ℝ) ^ (1/2 : ℝ) * lam ^ (-(1/6) : ℝ) := by positivity
      have hNu_nn : (0 : ℝ) ≤ 12 * Real.sqrt c * ((N : ℝ) * lam ^ (1/6 : ℝ)) := by positivity
      nlinarith [hprod, hsqc1, hAnn, hNu_nn,
        mul_nonneg hAnn (by linarith [hsqc1] : (0 : ℝ) ≤ 12 * Real.sqrt c - 1)]

end Salt.ExpSum
