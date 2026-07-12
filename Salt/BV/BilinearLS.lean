/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.Completion
import Salt.LS.CharLS

/-!
# V2.LS-bil — the bilinear large sieve (fixed-shell form)

Design: `docs/blueprints/bv.md`, node `V2.LS-bil`. This file lands the
**fixed-cutoff** bilinear large sieve `bilinear_LS_shell`: for a sharp cutoff
`m·n ≤ Y` (no maximum over the cutoff), the `(q/φq)`-weighted, primitive-character
`L¹` norm of the bilinear character sum obeys the frozen
`(M+Q²)^{1/2}(N+Q²)^{1/2}‖a‖₂‖b‖₂` structure with a single polylog factor
(`κ = 1`).

## The mechanism (L2–L4 of the recon, at a fixed shell)

Fix `Y`.  For each modulus `q`, primitive `χ`:

* **L2 — completion.**  `bilinear_factorization` (V2.Perron) splits the sharp
  cutoff into `H` clean product twists:
  `∑_{mn≤Y} a_m b_n χ(mn) = ∑_{h<H} A_{χ,h}·B_{χ,h}`, with
  `A_{χ,h} = ∑_{m≤M} a_m ĉ_h(min(⌊Y/m⌋,H)) χ(m)` and
  `B_{χ,h} = ∑_{n≤H} b_n e(hn/H) χ(n)`.
* **triangle + L3 — CS in (q,χ).**  `‖∑_h A_{χ,h}B_{χ,h}‖ ≤ ∑_h ‖A_{χ,h}‖‖B_{χ,h}‖`,
  then a nested weighted Cauchy–Schwarz over `(q,χ)` (`cs_over_q_chi`) splits each
  `h`-term into an `A`-factor and a `B`-factor.
* **L4 — `char_LS` ×2.**  Each factor is a single-character sum, handled by the
  character large sieve `char_LS` (`Salt/LS/CharLS.lean`).  The `A`-side coefficient
  mass carries `‖ĉ_h(·)‖² ≤ γ_h²` (P4, `Z`-uniform), the `B`-side is `γ`-free
  (`‖e‖ = 1`).
* **collapse.**  `∑_h γ_h ≤ 2 + log H` (`sum_gamma_le`, the P3 harmonic bound)
  contracts the `h`-sum, giving `κ = 1`.

## Scope note (the maximal form)

The FROZEN target for `V2.LS-bil` additionally carries an inner
`max_{y ≤ MH}` over the cutoff (with a second polylog factor, `κ = 2`).  That
maximal form is **not** landed here — see `docs/blueprints/flags.md` (node
`V2.LS-bil`): the `interval_decomp` route pays `√(#blocks)` (a *power*, not a
log) once the per-level `sup'` over dyadic blocks is pushed through the bilinear
completion, so the clean `κ = 2` does not close via the available toolkit.  Per
the PB-floor, this fixed-shell lemma is the deliverable; `V2b` supplies its own
dyadic-in-`y` assembly on top.

Only `[propext, Classical.choice, Quot.sound]` are used (via `char_LS`).

The private lemmas `dist_lbP`/`term_leP`/`sum_H_leP` are **replicas** of the
(private) PV/Completion harmonic-sum kernel of the same names, re-proved locally
per the house rule against editing merged files (de-privating queued).
-/

namespace Salt.BV

open scoped BigOperators
open Salt.LS

/-! ### Replicas of the harmonic-sum kernel (see module docstring) -/

/-- **Denominator-sharp lower bound** (replica of Completion `dist_lbP`). -/
private lemma dist_lbP (f k : ℕ) (hk : 0 < k) (hkf : k < f) :
    (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 ≤ dist₁ ((k : ℝ) / (f : ℝ)) 0 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkfR : (k : ℝ) < f := by exact_mod_cast hkf
  have hf0 : (0 : ℝ) < f := by linarith
  have hfne : (f : ℝ) ≠ 0 := hf0.ne'
  have hkfpos : (0 : ℝ) < (k : ℝ) / (f : ℝ) := div_pos hkR hf0
  have key : ∀ n : ℤ,
      (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 ≤ |(k : ℝ) / (f : ℝ) - (n : ℝ)| := by
    intro n
    have h1 : (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 ≤ (k : ℝ) / (f : ℝ) := by
      rw [div_le_div_iff₀ (pow_pos hf0 2) hf0]
      nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) hf0.le]
    have h2 : (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 ≤ ((f : ℝ) - k) / (f : ℝ) := by
      rw [div_le_div_iff₀ (pow_pos hf0 2) hf0]
      nlinarith [mul_nonneg (sq_nonneg ((f : ℝ) - k)) hf0.le]
    rcases le_or_gt (n : ℝ) 0 with hn | hn
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnZ
      have hkf1 : (k : ℝ) / (f : ℝ) < 1 := by rw [div_lt_one hf0]; exact hkfR
      rw [abs_of_nonpos (by linarith)]
      have hfk_eq : ((f : ℝ) - k) / (f : ℝ) = 1 - (k : ℝ) / (f : ℝ) := by field_simp
      linarith
  have hdd : dist₁ ((k : ℝ) / (f : ℝ)) 0
      = |(k : ℝ) / (f : ℝ) - (round ((k : ℝ) / (f : ℝ)) : ℝ)| := by
    unfold dist₁; simp only [sub_zero]
  rw [hdd]
  exact key (round ((k : ℝ) / (f : ℝ)))

/-- **Per-term harmonic bound** (replica of Completion `term_leP`). -/
private lemma term_leP (f k : ℕ) (hk : 0 < k) (hkf : k < f) :
    1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0)
      ≤ ((f : ℝ) / 2) * (1 / (k : ℝ) + 1 / ((f : ℝ) - k)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkfR : (k : ℝ) < f := by exact_mod_cast hkf
  have hfkR : (0 : ℝ) < (f : ℝ) - k := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hlb := dist_lbP f k hk hkf
  have hBpos : (0 : ℝ) < (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 :=
    div_pos (mul_pos hkR hfkR) (pow_pos hf0 2)
  have step1 : 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0)
      ≤ 1 / (2 * ((k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2)) := by
    apply one_div_le_one_div_of_le
    · linarith
    · linarith
  have step2 : 1 / (2 * ((k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2))
      = ((f : ℝ) / 2) * (1 / (k : ℝ) + 1 / ((f : ℝ) - k)) := by
    rw [eq_comm]
    field_simp
    ring
  rw [step2] at step1
  exact step1

/-- **The harmonic sum** (replica of Completion `sum_H_leP`). -/
private lemma sum_H_leP (f : ℕ) (hf : 2 ≤ f) :
    ∑ k ∈ Finset.range f,
        (if k = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0))
      ≤ (f : ℝ) * (1 + Real.log f) := by
  have hEq : ((harmonic (f - 1) : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 (f - 1), (1 : ℝ) / k := by
    rw [harmonic_eq_sum_Icc]; push_cast
    apply Finset.sum_congr rfl; intro k _; rw [one_div]
  have hA : ∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / k ≤ 1 + Real.log f := by
    have hIco : Finset.Ico 1 f = Finset.Icc 1 (f - 1) := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIco, ← hEq]
    calc ((harmonic (f - 1) : ℚ) : ℝ) ≤ 1 + Real.log ((f - 1 : ℕ) : ℝ) :=
          harmonic_le_one_add_log (f - 1)
      _ ≤ 1 + Real.log f := by
          have h01 : (0 : ℝ) < ((f - 1 : ℕ) : ℝ) := by
            have : 0 < f - 1 := by omega
            exact_mod_cast this
          have hle : ((f - 1 : ℕ) : ℝ) ≤ (f : ℝ) := by exact_mod_cast Nat.sub_le f 1
          have := Real.log_le_log h01 hle
          linarith
  have hBA : ∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / ((f : ℝ) - k)
      = ∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / k := by
    apply Finset.sum_nbij' (fun k => f - k) (fun k => f - k)
    · intro k hk; rw [Finset.mem_Ico] at hk ⊢; omega
    · intro k hk; rw [Finset.mem_Ico] at hk ⊢; omega
    · intro k hk; rw [Finset.mem_Ico] at hk; omega
    · intro k hk; rw [Finset.mem_Ico] at hk; omega
    · intro k hk; rw [Finset.mem_Ico] at hk; rw [Nat.cast_sub hk.2.le]
  have hB : ∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / ((f : ℝ) - k) ≤ 1 + Real.log f := by
    rw [hBA]; exact hA
  have hconv : ∀ k : ℕ,
      (if k = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0))
        = (if k ≠ 0 then 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0) else 0) := by
    intro k; by_cases h : k = 0 <;> simp [h]
  have hrange :
      ∑ k ∈ Finset.range f,
          (if k = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0))
        = ∑ k ∈ Finset.Ico 1 f, 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0) := by
    rw [Finset.sum_congr rfl (fun k _ => hconv k), ← Finset.sum_filter]
    congr 1
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hrange]
  calc ∑ k ∈ Finset.Ico 1 f, 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0)
      ≤ ∑ k ∈ Finset.Ico 1 f, ((f : ℝ) / 2) * (1 / (k : ℝ) + 1 / ((f : ℝ) - k)) := by
        apply Finset.sum_le_sum; intro k hk
        rw [Finset.mem_Ico] at hk
        exact term_leP f k hk.1 hk.2
    _ = ((f : ℝ) / 2)
        * ((∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / k)
            + (∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / ((f : ℝ) - k))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ ((f : ℝ) / 2) * (2 * (1 + Real.log f)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hA, hB]
    _ = (f : ℝ) * (1 + Real.log f) := by ring

/-! ### The uniform coefficient bound `γ_h` and its harmonic mass -/

/-- The `Z`-uniform bound on `‖ĉ_h(Z)‖` from P4: `1` at `h = 0`, and the geometric
`(1/H)·(2·dist₁(h/H,0))⁻¹` for `h ≠ 0`. -/
noncomputable def gammaH (H h : ℕ) : ℝ :=
  if h = 0 then (1 : ℝ) else (1 / (H : ℝ)) * (1 / (2 * dist₁ ((h : ℝ) / (H : ℝ)) 0))

/-- `γ_h ≥ 0`. -/
private lemma gammaH_nonneg (H h : ℕ) : 0 ≤ gammaH H h := by
  unfold gammaH
  by_cases h0 : h = 0
  · rw [if_pos h0]; norm_num
  · rw [if_neg h0]
    have : (0 : ℝ) ≤ 2 * dist₁ ((h : ℝ) / (H : ℝ)) 0 := by
      have := dist₁_nonneg ((h : ℝ) / (H : ℝ)) 0; linarith
    exact mul_nonneg (by positivity) (by positivity)

/-- **P4, packaged.** `‖ĉ_h(min(⌊Y/m⌋,H))‖ ≤ γ_h` for every `m`, uniformly.  The
`h = 0` coefficient is `Z/H ≤ 1`; for `1 ≤ h < H` it is the geometric bound. -/
private lemma norm_fourierCutoff_le_gammaH (H Y m h : ℕ) (hH : 0 < H) (hhH : h < H) :
    ‖fourierCutoff H (min (Y / m) H) h‖ ≤ gammaH H h := by
  unfold gammaH
  by_cases h0 : h = 0
  · rw [if_pos h0]
    -- `ĉ_0(Z) = Z/H`, norm `≤ 1` since `Z ≤ H`.
    subst h0
    have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
    have hZH : min (Y / m) H ≤ H := min_le_right _ _
    have hval : fourierCutoff H (min (Y / m) H) 0 = ((min (Y / m) H : ℕ) : ℂ) / (H : ℂ) := by
      unfold fourierCutoff
      simp only [Nat.cast_zero, zero_mul, neg_zero, zero_div, e_zero, Finset.sum_const,
                 Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
      ring
    rw [hval, norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_one hHR]
    exact_mod_cast hZH
  · rw [if_neg h0]
    exact norm_fourierCutoff_le H (min (Y / m) H) h (Nat.one_le_iff_ne_zero.mpr h0) hhH

/-- **P3 mass.** `∑_{h<H} γ_h ≤ 2 + log H`, uniformly in the coefficient data:
the `h = 0` term is `1`, and the `h ≠ 0` terms sum (via `sum_H_leP`) to `≤ 1 + log H`. -/
private lemma sum_gammaH_le (H : ℕ) (hH : 0 < H) :
    ∑ h ∈ Finset.range H, gammaH H h ≤ 2 + Real.log H := by
  rcases lt_or_ge H 2 with hH1 | hH2
  · have hHeq : H = 1 := by omega
    subst hHeq
    rw [Finset.range_one, Finset.sum_singleton, Nat.cast_one, Real.log_one]
    norm_num [gammaH]
  · have hHne : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
    calc ∑ h ∈ Finset.range H, gammaH H h
        = 1 + (1 / (H : ℝ)) *
            ∑ h ∈ Finset.range H,
              (if h = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((h : ℝ) / (H : ℝ)) 0)) := by
          have hpt : ∀ h : ℕ, gammaH H h
              = (if h = 0 then (1 : ℝ) else 0)
                + (1 / (H : ℝ)) *
                  (if h = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((h : ℝ) / (H : ℝ)) 0)) := by
            intro h; unfold gammaH; by_cases h0 : h = 0 <;> simp [h0]
          rw [Finset.sum_congr rfl (fun h _ => hpt h), Finset.sum_add_distrib, ← Finset.mul_sum]
          have hone : ∑ h ∈ Finset.range H, (if h = 0 then (1 : ℝ) else 0) = 1 := by
            simp [hH]
          rw [hone]
      _ ≤ 1 + (1 / (H : ℝ)) * ((H : ℝ) * (1 + Real.log H)) := by
          have hstep := mul_le_mul_of_nonneg_left (sum_H_leP H hH2)
            (by positivity : (0 : ℝ) ≤ 1 / (H : ℝ))
          linarith [hstep]
      _ = 2 + Real.log H := by
          rw [← mul_assoc, one_div, inv_mul_cancel₀ hHne, one_mul]; ring

/-! ### The nested weighted Cauchy–Schwarz over `(q, χ)` -/

/-- **Nested weighted Cauchy–Schwarz.** For `w q ≥ 0` and per-modulus data
`P, R, C : ℕ → ℝ` with `C q ≤ √(P q)·√(R q)`,
`∑_q w_q C_q ≤ √(∑_q w_q P_q)·√(∑_q w_q R_q)`.  In use, `P q = ∑_χ ‖A‖²`,
`R q = ∑_χ ‖B‖²`, `C q = ∑_χ ‖A‖‖B‖` (the inner per-`q` CS supplies the hypothesis). -/
private lemma cs_over_q_chi (Q : ℕ) (w P R C : ℕ → ℝ)
    (hw : ∀ q, 0 ≤ w q) (hP : ∀ q, 0 ≤ P q) (hR : ∀ q, 0 ≤ R q)
    (hC : ∀ q, C q ≤ Real.sqrt (P q) * Real.sqrt (R q)) :
    ∑ q ∈ Finset.Icc 1 Q, w q * C q
      ≤ Real.sqrt (∑ q ∈ Finset.Icc 1 Q, w q * P q)
        * Real.sqrt (∑ q ∈ Finset.Icc 1 Q, w q * R q) := by
  have hsumP : 0 ≤ ∑ q ∈ Finset.Icc 1 Q, w q * P q :=
    Finset.sum_nonneg (fun q _ => mul_nonneg (hw q) (hP q))
  have hstep1 : ∑ q ∈ Finset.Icc 1 Q, w q * C q
      ≤ ∑ q ∈ Finset.Icc 1 Q, Real.sqrt (w q * P q) * Real.sqrt (w q * R q) := by
    apply Finset.sum_le_sum
    intro q _
    calc w q * C q ≤ w q * (Real.sqrt (P q) * Real.sqrt (R q)) :=
          mul_le_mul_of_nonneg_left (hC q) (hw q)
      _ = Real.sqrt (w q * P q) * Real.sqrt (w q * R q) := by
          rw [Real.sqrt_mul (hw q), Real.sqrt_mul (hw q), mul_mul_mul_comm,
              Real.mul_self_sqrt (hw q)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 Q)
    (fun q => Real.sqrt (w q * P q)) (fun q => Real.sqrt (w q * R q))
  have hsqP : ∀ q, (Real.sqrt (w q * P q)) ^ 2 = w q * P q := fun q =>
    Real.sq_sqrt (mul_nonneg (hw q) (hP q))
  have hsqR : ∀ q, (Real.sqrt (w q * R q)) ^ 2 = w q * R q := fun q =>
    Real.sq_sqrt (mul_nonneg (hw q) (hR q))
  simp only [hsqP, hsqR] at hcs
  have hLHSnn : 0 ≤ ∑ q ∈ Finset.Icc 1 Q, Real.sqrt (w q * P q) * Real.sqrt (w q * R q) :=
    Finset.sum_nonneg (fun q _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hfin : (∑ q ∈ Finset.Icc 1 Q, Real.sqrt (w q * P q) * Real.sqrt (w q * R q))
      ≤ Real.sqrt (∑ q ∈ Finset.Icc 1 Q, w q * P q)
        * Real.sqrt (∑ q ∈ Finset.Icc 1 Q, w q * R q) := by
    rw [← Real.sqrt_mul hsumP, ← Real.sqrt_sq hLHSnn]
    exact Real.sqrt_le_sqrt hcs
  exact le_trans hstep1 hfin

/-! ### The `char_LS`-compatible bilinear coefficients -/

/-- The `A`-side (range-form) coefficient `m ↦ a_m·ĉ_h(min(⌊Y/m⌋,H))`, guarded to
vanish at `m = 0` so the `range (M+1)` sum matches the `Icc 1 M` sum of
`bilinear_factorization`. -/
noncomputable def bilinCoeffA (a : ℕ → ℂ) (H Y h : ℕ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else a m * fourierCutoff H (min (Y / m) H) h

/-- The `B`-side (range-form) coefficient `n ↦ b_n·e(hn/H)`, guarded at `n = 0`. -/
noncomputable def bilinCoeffB (b : ℕ → ℂ) (H h : ℕ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else b n * e ((h : ℝ) * (n : ℝ) / (H : ℝ))

/-- The range-form `A`-factor equals the `Icc`-form `A`-factor of
`bilinear_factorization` (the `m = 0` term vanishes). -/
private lemma bilinCoeffA_sum_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ℕ → ℂ)
    (H Y h M : ℕ) :
    ∑ m ∈ Finset.range (M + 1), bilinCoeffA a H Y h m * χ ((m : ℕ) : ZMod q)
      = ∑ m ∈ Finset.Icc 1 M,
          a m * fourierCutoff H (min (Y / m) H) h * χ ((m : ℕ) : ZMod q) := by
  have hsub : Finset.Icc 1 M ⊆ Finset.range (M + 1) := by
    intro m hm; rw [Finset.mem_Icc] at hm; rw [Finset.mem_range]; omega
  have hcompl : ∀ m ∈ Finset.range (M + 1), m ∉ Finset.Icc 1 M →
      bilinCoeffA a H Y h m * χ ((m : ℕ) : ZMod q) = 0 := by
    intro m hmr hm
    rw [Finset.mem_range] at hmr
    rw [Finset.mem_Icc] at hm
    have hm0 : m = 0 := by omega
    subst hm0
    simp [bilinCoeffA]
  rw [← Finset.sum_subset hsub hcompl]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm0 : m ≠ 0 := by rw [Finset.mem_Icc] at hm; omega
  simp only [bilinCoeffA, if_neg hm0]

/-- The range-form `B`-factor equals the `Icc`-form `B`-factor of
`bilinear_factorization` (the `n = 0` term vanishes). -/
private lemma bilinCoeffB_sum_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℕ → ℂ)
    (H h H' : ℕ) :
    ∑ n ∈ Finset.range (H' + 1), bilinCoeffB b H h n * χ ((n : ℕ) : ZMod q)
      = ∑ n ∈ Finset.Icc 1 H',
          b n * e ((h : ℝ) * (n : ℝ) / (H : ℝ)) * χ ((n : ℕ) : ZMod q) := by
  have hsub : Finset.Icc 1 H' ⊆ Finset.range (H' + 1) := by
    intro n hn; rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega
  have hcompl : ∀ n ∈ Finset.range (H' + 1), n ∉ Finset.Icc 1 H' →
      bilinCoeffB b H h n * χ ((n : ℕ) : ZMod q) = 0 := by
    intro n hnr hn
    rw [Finset.mem_range] at hnr
    rw [Finset.mem_Icc] at hn
    have hn0 : n = 0 := by omega
    subst hn0
    simp [bilinCoeffB]
  rw [← Finset.sum_subset hsub hcompl]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn0 : n ≠ 0 := by rw [Finset.mem_Icc] at hn; omega
  simp only [bilinCoeffB, if_neg hn0]

/-- The `A`-side coefficient mass is controlled by `γ_h²·∑‖a‖²` (P4). -/
private lemma bilinCoeffA_mass_le (a : ℕ → ℂ) (H Y h M : ℕ) (hH : 0 < H) (hhH : h < H) :
    ∑ m ∈ Finset.range (M + 1), ‖bilinCoeffA a H Y h m‖ ^ 2
      ≤ (gammaH H h) ^ 2 * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2 := by
  have hsub : Finset.Icc 1 M ⊆ Finset.range (M + 1) := by
    intro m hm; rw [Finset.mem_Icc] at hm; rw [Finset.mem_range]; omega
  have hzero : ∀ m ∈ Finset.range (M + 1), m ∉ Finset.Icc 1 M →
      ‖bilinCoeffA a H Y h m‖ ^ 2 = 0 := by
    intro m hmr hm
    have hm0 : m = 0 := by
      rw [Finset.mem_range] at hmr; rw [Finset.mem_Icc] at hm; omega
    simp only [bilinCoeffA, if_pos hm0, norm_zero]; ring
  rw [← Finset.sum_subset hsub hzero, Finset.mul_sum]
  refine Finset.sum_le_sum (fun m hm => ?_)
  have hm0 : m ≠ 0 := by rw [Finset.mem_Icc] at hm; omega
  have hfc : ‖fourierCutoff H (min (Y / m) H) h‖ ≤ gammaH H h :=
    norm_fourierCutoff_le_gammaH H Y m h hH hhH
  calc ‖bilinCoeffA a H Y h m‖ ^ 2
      = ‖a m‖ ^ 2 * ‖fourierCutoff H (min (Y / m) H) h‖ ^ 2 := by
        simp only [bilinCoeffA, if_neg hm0, norm_mul, mul_pow]
    _ ≤ ‖a m‖ ^ 2 * (gammaH H h) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact pow_le_pow_left₀ (norm_nonneg _) hfc 2
    _ = gammaH H h ^ 2 * ‖a m‖ ^ 2 := by ring

/-- The `B`-side coefficient mass equals `∑‖b‖²` (`‖e‖ = 1`). -/
private lemma bilinCoeffB_mass_eq (b : ℕ → ℂ) (H h H' : ℕ) :
    ∑ n ∈ Finset.range (H' + 1), ‖bilinCoeffB b H h n‖ ^ 2
      = ∑ n ∈ Finset.Icc 1 H', ‖b n‖ ^ 2 := by
  have hsub : Finset.Icc 1 H' ⊆ Finset.range (H' + 1) := by
    intro n hn; rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega
  have hzero : ∀ n ∈ Finset.range (H' + 1), n ∉ Finset.Icc 1 H' →
      ‖bilinCoeffB b H h n‖ ^ 2 = 0 := by
    intro n hnr hn
    have hn0 : n = 0 := by
      rw [Finset.mem_range] at hnr; rw [Finset.mem_Icc] at hn; omega
    simp only [bilinCoeffB, if_pos hn0, norm_zero]; ring
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn0 : n ≠ 0 := by rw [Finset.mem_Icc] at hn; omega
  simp only [bilinCoeffB, if_neg hn0, norm_mul, norm_e, mul_one]

/-! ### The fixed-shell bilinear large sieve -/

open Classical in
/-- **V2.LS-bil (fixed-shell form).**  For `2 ≤ Q`, `0 < H`, coefficient sequences
`a, b`, and a sharp cutoff `m·n ≤ Y`,
```
∑_{q≤Q} (q/φq) ∑_{χ prim} ‖∑_{m≤M} ∑_{n≤H, mn≤Y} a_m b_n χ(mn)‖
  ≤ 2·(1 + log H)·√(Q²+13(M+1))·√(Q²+13(H+1))·√(∑‖a‖²)·√(∑‖b‖²).
```
The `(M+Q²)^{1/2}(N+Q²)^{1/2}‖a‖₂‖b‖₂` structure and the `L¹`-in-`(q,χ)` form are
the frozen target's; the single `(1 + log H)` factor is `κ = 1` (the maximal
`κ = 2` form is deferred, see the module docstring / flags). -/
theorem bilinear_LS_shell {M H Q : ℕ} (hQ : 2 ≤ Q) (hH : 0 < H) (a b : ℕ → ℂ) (Y : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 H).filter (fun n => m * n ≤ Y),
              a m * b n * χ ((m * n : ℕ) : ZMod q)‖
      ≤ 2 * (1 + Real.log H)
          * Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((M : ℝ) + 1))
          * Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((H : ℝ) + 1))
          * Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
          * Real.sqrt (∑ n ∈ Finset.Icc 1 H, ‖b n‖ ^ 2) := by
  classical
  -- Abbreviations.
  set w : ℕ → ℝ := fun q => (q : ℝ) / (q.totient : ℝ) with hw_def
  have hw_nonneg : ∀ q, 0 ≤ w q := fun q => by rw [hw_def]; positivity
  set KA := Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((M : ℝ) + 1)) with hKA
  set KB := Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((H : ℝ) + 1)) with hKB
  set Sa := Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) with hSa
  set Sb := Real.sqrt (∑ n ∈ Finset.Icc 1 H, ‖b n‖ ^ 2) with hSb
  have hKAnn : 0 ≤ KA := Real.sqrt_nonneg _
  have hKBnn : 0 ≤ KB := Real.sqrt_nonneg _
  have hSann : 0 ≤ Sa := Real.sqrt_nonneg _
  have hSbnn : 0 ≤ Sb := Real.sqrt_nonneg _
  -- The `char_LS`-form factors `Af`, `Bf` and their per-`q` `(P,R,C)` data.
  set Af : (q : ℕ) → DirichletCharacter ℂ q → ℕ → ℂ :=
    fun q χ h => ∑ m ∈ Finset.range (M + 1), bilinCoeffA a H Y h m * χ ((m : ℕ) : ZMod q)
      with hAf_def
  set Bf : (q : ℕ) → DirichletCharacter ℂ q → ℕ → ℂ :=
    fun q χ h => ∑ n ∈ Finset.range (H + 1), bilinCoeffB b H h n * χ ((n : ℕ) : ZMod q)
      with hBf_def
  set P : ℕ → ℕ → ℝ := fun h q =>
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
      ‖Af q χ h‖ ^ 2 with hP_def
  set R : ℕ → ℕ → ℝ := fun h q =>
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
      ‖Bf q χ h‖ ^ 2 with hR_def
  set C : ℕ → ℕ → ℝ := fun h q =>
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
      ‖Af q χ h‖ * ‖Bf q χ h‖ with hC_def
  -- Per-`h`, per-`q` nonnegativity + inner Cauchy–Schwarz.
  have hPnn : ∀ h q, 0 ≤ P h q := fun h q => by
    rw [hP_def]; exact Finset.sum_nonneg (fun χ _ => sq_nonneg _)
  have hRnn : ∀ h q, 0 ≤ R h q := fun h q => by
    rw [hR_def]; exact Finset.sum_nonneg (fun χ _ => sq_nonneg _)
  have hCle : ∀ h q, C h q ≤ Real.sqrt (P h q) * Real.sqrt (R h q) := by
    intro h q
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive))
      (fun χ => ‖Af q χ h‖) (fun χ => ‖Bf q χ h‖)
    have hCnn : 0 ≤ C h q := by
      rw [hC_def]; exact Finset.sum_nonneg (fun χ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    calc C h q = Real.sqrt ((C h q) ^ 2) := (Real.sqrt_sq hCnn).symm
      _ ≤ Real.sqrt (P h q * R h q) := by
          apply Real.sqrt_le_sqrt
          rw [hC_def, hP_def, hR_def]; exact hcs
      _ = Real.sqrt (P h q) * Real.sqrt (R h q) := Real.sqrt_mul (hPnn h q) _
  -- `char_LS` on the `A`-side: `∑_q w_q P_q ≤ (Q²+13(M+1))·γ_h²·∑‖a‖²`.
  have hAfactor : ∀ h, h < H →
      ∑ q ∈ Finset.Icc 1 Q, w q * P h q
        ≤ ((Q : ℝ) ^ 2 + 13 * ((M : ℝ) + 1))
          * ((gammaH H h) ^ 2 * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) := by
    intro h hhH
    have hls := char_LS (N := M + 1) hQ (bilinCoeffA a H Y h)
    have hcast : ((Q : ℝ) ^ 2 + 13 * ((M + 1 : ℕ) : ℝ))
        = (Q : ℝ) ^ 2 + 13 * ((M : ℝ) + 1) := by push_cast; ring
    rw [hcast] at hls
    calc ∑ q ∈ Finset.Icc 1 Q, w q * P h q
        = ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
              ‖∑ m ∈ Finset.range (M + 1), bilinCoeffA a H Y h m * χ ((m : ℕ) : ZMod q)‖ ^ 2 := by
          rw [hP_def, hw_def, hAf_def]
      _ ≤ ((Q : ℝ) ^ 2 + 13 * ((M : ℝ) + 1))
            * ∑ m ∈ Finset.range (M + 1), ‖bilinCoeffA a H Y h m‖ ^ 2 := hls
      _ ≤ ((Q : ℝ) ^ 2 + 13 * ((M : ℝ) + 1))
            * ((gammaH H h) ^ 2 * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left (bilinCoeffA_mass_le a H Y h M hH hhH)
          positivity
  -- `char_LS` on the `B`-side: `∑_q w_q R_q ≤ (Q²+13(H+1))·∑‖b‖²`.
  have hBfactor : ∀ h,
      ∑ q ∈ Finset.Icc 1 Q, w q * R h q
        ≤ ((Q : ℝ) ^ 2 + 13 * ((H : ℝ) + 1)) * ∑ n ∈ Finset.Icc 1 H, ‖b n‖ ^ 2 := by
    intro h
    have hls := char_LS (N := H + 1) hQ (bilinCoeffB b H h)
    have hcast : ((Q : ℝ) ^ 2 + 13 * ((H + 1 : ℕ) : ℝ))
        = (Q : ℝ) ^ 2 + 13 * ((H : ℝ) + 1) := by push_cast; ring
    rw [hcast] at hls
    calc ∑ q ∈ Finset.Icc 1 Q, w q * R h q
        = ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
              ‖∑ n ∈ Finset.range (H + 1), bilinCoeffB b H h n * χ ((n : ℕ) : ZMod q)‖ ^ 2 := by
          rw [hR_def, hw_def, hBf_def]
      _ ≤ ((Q : ℝ) ^ 2 + 13 * ((H : ℝ) + 1))
            * ∑ n ∈ Finset.range (H + 1), ‖bilinCoeffB b H h n‖ ^ 2 := hls
      _ = ((Q : ℝ) ^ 2 + 13 * ((H : ℝ) + 1)) * ∑ n ∈ Finset.Icc 1 H, ‖b n‖ ^ 2 := by
          rw [bilinCoeffB_mass_eq b H h H]
  -- The per-`h` bound: `∑_q w_q C_q ≤ γ_h · (KA·KB·Sa·Sb)`.
  have hperh : ∀ h ∈ Finset.range H,
      ∑ q ∈ Finset.Icc 1 Q, w q * C h q ≤ gammaH H h * (KA * KB * Sa * Sb) := by
    intro h hh
    rw [Finset.mem_range] at hh
    have hcs := cs_over_q_chi Q w (P h) (R h) (C h) hw_nonneg (hPnn h) (hRnn h) (hCle h)
    -- `√(∑ w P) ≤ KA · γ_h · Sa`.
    have hAsqrt : Real.sqrt (∑ q ∈ Finset.Icc 1 Q, w q * P h q)
        ≤ KA * (gammaH H h * Sa) := by
      calc Real.sqrt (∑ q ∈ Finset.Icc 1 Q, w q * P h q)
          ≤ Real.sqrt (((Q : ℝ) ^ 2 + 13 * ((M : ℝ) + 1))
              * ((gammaH H h) ^ 2 * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)) :=
            Real.sqrt_le_sqrt (hAfactor h hh)
        _ = KA * (gammaH H h * Sa) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _),
                Real.sqrt_sq (gammaH_nonneg H h), hKA, hSa]
    -- `√(∑ w R) ≤ KB · Sb`.
    have hBsqrt : Real.sqrt (∑ q ∈ Finset.Icc 1 Q, w q * R h q) ≤ KB * Sb := by
      calc Real.sqrt (∑ q ∈ Finset.Icc 1 Q, w q * R h q)
          ≤ Real.sqrt (((Q : ℝ) ^ 2 + 13 * ((H : ℝ) + 1))
              * ∑ n ∈ Finset.Icc 1 H, ‖b n‖ ^ 2) := Real.sqrt_le_sqrt (hBfactor h)
        _ = KB * Sb := by rw [Real.sqrt_mul (by positivity), hKB, hSb]
    calc ∑ q ∈ Finset.Icc 1 Q, w q * C h q
        ≤ Real.sqrt (∑ q ∈ Finset.Icc 1 Q, w q * P h q)
            * Real.sqrt (∑ q ∈ Finset.Icc 1 Q, w q * R h q) := hcs
      _ ≤ (KA * (gammaH H h * Sa)) * (KB * Sb) := by
          apply mul_le_mul hAsqrt hBsqrt (Real.sqrt_nonneg _)
          exact mul_nonneg hKAnn (mul_nonneg (gammaH_nonneg H h) hSann)
      _ = gammaH H h * (KA * KB * Sa * Sb) := by ring
  -- Assemble: reduce the cutoff via factorization, triangle, swap `h` out, per-`h`.
  calc ∑ q ∈ Finset.Icc 1 Q, w q *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 H).filter (fun n => m * n ≤ Y),
                a m * b n * χ ((m * n : ℕ) : ZMod q)‖
      ≤ ∑ q ∈ Finset.Icc 1 Q, w q *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ∑ h ∈ Finset.range H, ‖Af q χ h‖ * ‖Bf q χ h‖ := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        haveI : NeZero q := ⟨by omega⟩
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => ?_)) (hw_nonneg q)
        -- `‖cutoff‖ = ‖∑_h Af·Bf‖ ≤ ∑_h ‖Af‖‖Bf‖`.
        have hfac : ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 H).filter (fun n => m * n ≤ Y),
              a m * b n * χ ((m * n : ℕ) : ZMod q)
            = ∑ h ∈ Finset.range H, Af q χ h * Bf q χ h := by
          rw [bilinear_factorization χ a b Y M H hH]
          refine Finset.sum_congr rfl (fun h _ => ?_)
          simp only [hAf_def, hBf_def]
          rw [bilinCoeffA_sum_eq χ a H Y h M, bilinCoeffB_sum_eq χ b H h H]
        rw [hfac]
        calc ‖∑ h ∈ Finset.range H, Af q χ h * Bf q χ h‖
            ≤ ∑ h ∈ Finset.range H, ‖Af q χ h * Bf q χ h‖ := norm_sum_le _ _
          _ = ∑ h ∈ Finset.range H, ‖Af q χ h‖ * ‖Bf q χ h‖ := by
              refine Finset.sum_congr rfl (fun h _ => ?_); rw [norm_mul]
    _ = ∑ h ∈ Finset.range H, ∑ q ∈ Finset.Icc 1 Q, w q * C h q := by
        have hstep : ∀ q,
            w q * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
                ∑ h ∈ Finset.range H, ‖Af q χ h‖ * ‖Bf q χ h‖
              = ∑ h ∈ Finset.range H, w q * C h q := by
          intro q
          rw [Finset.sum_comm, Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun q _ => hstep q), Finset.sum_comm]
    _ ≤ ∑ h ∈ Finset.range H, gammaH H h * (KA * KB * Sa * Sb) :=
        Finset.sum_le_sum hperh
    _ = (∑ h ∈ Finset.range H, gammaH H h) * (KA * KB * Sa * Sb) := by rw [Finset.sum_mul]
    _ ≤ (2 + Real.log H) * (KA * KB * Sa * Sb) := by
        apply mul_le_mul_of_nonneg_right (sum_gammaH_le H hH)
        positivity
    _ ≤ 2 * (1 + Real.log H) * KA * KB * Sa * Sb := by
        have hlogH : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hH)
        have hle : (2 : ℝ) + Real.log H ≤ 2 * (1 + Real.log H) := by linarith
        have hprod : 0 ≤ KA * KB * Sa * Sb := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hle hprod]

end Salt.BV
