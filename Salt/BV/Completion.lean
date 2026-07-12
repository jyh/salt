/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.Defs
import Salt.LS.Dist
import Salt.LS.TypeSums
import Salt.BV.PolyaVinogradov

/-!
# V2.Perron — the cutoff-completion kernel (Route S)

Design: `docs/blueprints/bv.md`, node `V2.Perron` (FROZEN Route S). This is the
*elementary finite-Fourier completion* of the sharp interval indicator
`1_{n ≤ Z}`, an **exact identity** (no error term) built as the second harvest of
the Pólya–Vinogradov kernel `Salt/BV/PolyaVinogradov.lean`.

The sub-DAG P1–P4:

* **P1** (`sum_e_eq`): additive orthogonality — the geometric sum of `H`-th roots
  of unity `∑_{h<H} e(h·r/H) = H·1_{H ∣ r}` for `r : ℤ`.
* **P2** (`fourierCutoff_indicator`): the interval-indicator DFT — for
  `1 ≤ n ≤ H`, `Z ≤ H`,
  `1_{n ≤ Z} = ∑_{h<H} ĉ_h(Z)·e(hn/H)`, `ĉ_h(Z) = (1/H)∑_{k∈Icc 1 Z} e(−hk/H)`.
  The one genuinely new C piece (period bookkeeping via `H ∣ (n − k) ↔ n = k`).
* **P4** (`norm_fourierCutoff_le`): the per-coefficient `Z`-uniform bound
  `‖ĉ_h(Z)‖ ≤ (1/H)·(2·dist₁(h/H, 0))⁻¹` for `h ≢ 0 (mod H)`.  A verbatim
  re-application of the PV geometric bound.
* **P3** (`sum_norm_fourierCutoff_le`): the L¹ mass `∑_{h<H} ‖ĉ_h(Z)‖ ≤ 2 + log H`,
  **uniform in `Z`** (the harmonic sum, mirroring PV's `sum_H_le`).

The bilinear factorization corollary (`bilinear_factorization`) feeds the L2
consumer of `V2.LS-bil`: it splits a sharp-cutoff bilinear form
`∑_{m,n : mn ≤ Y} a_m b_n χ(mn)` into `H` clean product twists.

The analytic-kernel lemmas (`chord`, `geom_e_bound`, `dist_lb`, `dist_pos`,
`term_le`, `sum_H_le`) are the **public** kernel of
`Salt/BV/PolyaVinogradov.lean`, reused directly here: the close-out
de-privating sweep dropped the former `P`-suffix replica block, per the
kernel-visibility doctrine (`docs/blueprints/tactics.md`).
-/

namespace Salt.BV

open scoped BigOperators
open Salt.LS

/-! ### `e`-arithmetic helpers -/

/-- `e (n·x) = (e x)^n` for `n : ℕ` (additive-to-multiplicative). -/
private lemma e_nat_mul (n : ℕ) (x : ℝ) : e ((n : ℝ) * x) = (e x) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hk : ((k + 1 : ℕ) : ℝ) * x = (k : ℝ) * x + x := by push_cast; ring
      rw [hk, e_add, ih, pow_succ]

/-- `e (r) = 1` at every integer `r` (`e` is 1-periodic). -/
private lemma e_intCast (r : ℤ) : e ((r : ℝ)) = 1 := by
  have h : e ((r : ℝ)) = Complex.exp ((r : ℂ) * (2 * Real.pi * Complex.I)) := by
    unfold e; congr 1; push_cast; ring
  rw [h]; exact Complex.exp_int_mul_two_pi_mul_I r

/-- `dist₁` is negation-symmetric at `0`: `dist₁ (−x) 0 = dist₁ x 0`. -/
private lemma dist₁_neg_zero (x : ℝ) : dist₁ (-x) 0 = dist₁ x 0 := by
  have h : dist₁ (-x) 0 = dist₁ 0 x := by unfold dist₁; simp only [sub_zero, zero_sub]
  rw [h, dist₁_comm]

/-! ### P1 — additive orthogonality -/

/-- **P1 (additive orthogonality).** The geometric sum of the `H`-th roots of
unity `e(h·r/H)` over `h < H` collapses to `H·1_{H ∣ r}` for every integer `r`.
The `H ∣ r` case: every summand is `1`; otherwise the geometric ratio
`ζ = e(r/H) ≠ 1` while `ζ^H = e(r) = 1`, so the sum vanishes. -/
theorem sum_e_eq (H : ℕ) (hH : 0 < H) (r : ℤ) :
    ∑ h ∈ Finset.range H, e ((h : ℝ) * (r : ℝ) / (H : ℝ))
      = if (H : ℤ) ∣ r then (H : ℂ) else 0 := by
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hterm : ∀ h : ℕ, e ((h : ℝ) * (r : ℝ) / (H : ℝ)) = (e ((r : ℝ) / (H : ℝ))) ^ h := by
    intro h; rw [mul_div_assoc, e_nat_mul]
  simp_rw [hterm]
  have hpow : (e ((r : ℝ) / (H : ℝ))) ^ H = 1 := by
    rw [← e_nat_mul, show (H : ℝ) * ((r : ℝ) / (H : ℝ)) = (r : ℝ) from by field_simp, e_intCast]
  by_cases hd : (H : ℤ) ∣ r
  · rw [if_pos hd]
    obtain ⟨s, hs⟩ := hd
    have hζ : e ((r : ℝ) / (H : ℝ)) = 1 := by
      have hrs : (r : ℝ) / (H : ℝ) = (s : ℝ) := by rw [hs]; push_cast; field_simp
      rw [hrs, e_intCast]
    rw [hζ]; simp
  · rw [if_neg hd]
    have hζne : e ((r : ℝ) / (H : ℝ)) ≠ 1 := by
      intro hζ
      apply hd
      have hd0 : dist₁ ((r : ℝ) / (H : ℝ)) 0 = 0 := by
        have hc := chord ((r : ℝ) / (H : ℝ))
        rw [hζ, sub_self, norm_zero] at hc
        have := dist₁_nonneg ((r : ℝ) / (H : ℝ)) 0
        linarith
      obtain ⟨m, hm⟩ := (dist₁_eq_zero_iff ((r : ℝ) / (H : ℝ)) 0).mp hd0
      rw [sub_zero] at hm
      have hrmR : (r : ℝ) = (H : ℝ) * (m : ℝ) := by rw [← hm]; field_simp
      have hrm : r = H * m := by exact_mod_cast hrmR
      exact ⟨m, hrm⟩
    rw [geom_sum_eq hζne H, hpow, sub_self, zero_div]

/-! ### P2 — the interval-indicator DFT -/

/-- **Period bookkeeping.** For `n, k ∈ [1, H]`, `H ∣ (n − k) ↔ n = k`
(both lie in a window of length `H`, so a nonzero multiple of `H` is impossible). -/
private lemma dvd_sub_eq_of_bounds {H n k : ℕ} (hn1 : 1 ≤ n) (hnH : n ≤ H)
    (hk1 : 1 ≤ k) (hkH : k ≤ H) :
    ((H : ℤ) ∣ ((n : ℤ) - (k : ℤ))) ↔ n = k := by
  constructor
  · intro hdvd
    have hn1' : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn1
    have hnH' : (n : ℤ) ≤ (H : ℤ) := by exact_mod_cast hnH
    have hk1' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk1
    have hkH' : (k : ℤ) ≤ (H : ℤ) := by exact_mod_cast hkH
    rcases lt_trichotomy ((n : ℤ) - (k : ℤ)) 0 with hlt | heq | hgt
    · exfalso
      have hle := Int.le_of_dvd (by linarith : (0 : ℤ) < -((n : ℤ) - (k : ℤ))) (dvd_neg.mpr hdvd)
      omega
    · omega
    · exfalso
      have hle := Int.le_of_dvd hgt hdvd
      omega
  · intro h; subst h; simp

/-- The finite-Fourier cutoff coefficient `ĉ_h(Z) = (1/H)∑_{k∈Icc 1 Z} e(−hk/H)`.
Convention: the inner sum runs over `Icc 1 Z` (so `Z = 0` gives the empty sum),
and the exponent uses the real argument `−(h·k)/H`. -/
noncomputable def fourierCutoff (H Z h : ℕ) : ℂ :=
  (1 / (H : ℂ)) * ∑ k ∈ Finset.Icc 1 Z, e (-((h : ℝ) * (k : ℝ)) / (H : ℝ))

/-- **P2 (interval-indicator DFT — the exact identity).** For `1 ≤ n ≤ H` and
`Z ≤ H`, the sharp indicator `1_{n ≤ Z}` is the finite Fourier series
`∑_{h<H} ĉ_h(Z)·e(hn/H)`.  Route: expand, swap sums, collapse the inner
`∑_{h<H} e(h(n−k)/H) = H·1_{H ∣ n−k}` via P1, then `H ∣ (n−k) ↔ n = k`. -/
theorem fourierCutoff_indicator (H Z n : ℕ) (hH : 0 < H) (hn1 : 1 ≤ n) (hnH : n ≤ H)
    (hZH : Z ≤ H) :
    (if n ≤ Z then (1 : ℂ) else 0)
      = ∑ h ∈ Finset.range H, fourierCutoff H Z h * e ((h : ℝ) * (n : ℝ) / (H : ℝ)) := by
  have hHC : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  symm
  have hcomb : ∀ h k : ℕ,
      e (-((h : ℝ) * (k : ℝ)) / (H : ℝ)) * e ((h : ℝ) * (n : ℝ) / (H : ℝ))
        = e ((h : ℝ) * (((n : ℤ) - (k : ℤ) : ℤ) : ℝ) / (H : ℝ)) := by
    intro h k
    rw [← e_add]; congr 1; push_cast; ring
  calc ∑ h ∈ Finset.range H, fourierCutoff H Z h * e ((h : ℝ) * (n : ℝ) / (H : ℝ))
      = ∑ h ∈ Finset.range H, ∑ k ∈ Finset.Icc 1 Z,
          (1 / (H : ℂ)) * e ((h : ℝ) * (((n : ℤ) - (k : ℤ) : ℤ) : ℝ) / (H : ℝ)) := by
        refine Finset.sum_congr rfl (fun h _ => ?_)
        unfold fourierCutoff
        rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hcomb h k]
    _ = ∑ k ∈ Finset.Icc 1 Z, ∑ h ∈ Finset.range H,
          (1 / (H : ℂ)) * e ((h : ℝ) * (((n : ℤ) - (k : ℤ) : ℤ) : ℝ) / (H : ℝ)) := Finset.sum_comm
    _ = ∑ k ∈ Finset.Icc 1 Z, (1 / (H : ℂ)) *
          (if (H : ℤ) ∣ ((n : ℤ) - (k : ℤ)) then (H : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.mul_sum, sum_e_eq H hH ((n : ℤ) - (k : ℤ))]
    _ = ∑ k ∈ Finset.Icc 1 Z, (if (H : ℤ) ∣ ((n : ℤ) - (k : ℤ)) then (1 : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        by_cases hdv : (H : ℤ) ∣ ((n : ℤ) - (k : ℤ))
        · rw [if_pos hdv, if_pos hdv, one_div, inv_mul_cancel₀ hHC]
        · rw [if_neg hdv, if_neg hdv, mul_zero]
    _ = ∑ k ∈ Finset.Icc 1 Z, (if n = k then (1 : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_Icc] at hk
        have hkH : k ≤ H := le_trans hk.2 hZH
        by_cases hnk : n = k
        · rw [if_pos hnk, if_pos (show (H : ℤ) ∣ ((n : ℤ) - (k : ℤ)) from by rw [hnk]; simp)]
        · have hnd : ¬ (H : ℤ) ∣ ((n : ℤ) - (k : ℤ)) :=
            fun hdv => hnk ((dvd_sub_eq_of_bounds hn1 hnH hk.1 hkH).mp hdv)
          rw [if_neg hnd, if_neg hnk]
    _ = (if n ≤ Z then (1 : ℂ) else 0) := by
        rw [Finset.sum_ite_eq (Finset.Icc 1 Z) n (fun _ => (1 : ℂ))]
        by_cases hnz : n ≤ Z
        · rw [if_pos hnz, if_pos (Finset.mem_Icc.mpr ⟨hn1, hnz⟩)]
        · rw [if_neg hnz, if_neg (fun hmem => hnz (Finset.mem_Icc.mp hmem).2)]

/-! ### P4 — the per-coefficient `Z`-uniform bound -/

/-- **P4 (per-coefficient bound).** For `1 ≤ h < H`, the cutoff coefficient obeys
`‖ĉ_h(Z)‖ ≤ (1/H)·(2·dist₁(h/H, 0))⁻¹`, **uniformly in `Z`** — the geometric bound
`geom_e_bound` re-applied after factoring off the length-`Z` prefix. -/
theorem norm_fourierCutoff_le (H Z h : ℕ) (hh1 : 1 ≤ h) (hhH : h < H) :
    ‖fourierCutoff H Z h‖ ≤ (1 / (H : ℝ)) * (1 / (2 * dist₁ ((h : ℝ) / (H : ℝ)) 0)) := by
  unfold fourierCutoff
  rw [norm_mul]
  have hnorm1 : ‖(1 / (H : ℂ))‖ = 1 / (H : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [hnorm1]
  have hterm : ∀ k : ℕ,
      e (-((h : ℝ) * (k : ℝ)) / (H : ℝ)) = (e (-((h : ℝ) / (H : ℝ)))) ^ k := by
    intro k; rw [← e_nat_mul]; congr 1; ring
  have hsum : ‖∑ k ∈ Finset.Icc 1 Z, e (-((h : ℝ) * (k : ℝ)) / (H : ℝ))‖
      ≤ 1 / (2 * dist₁ ((h : ℝ) / (H : ℝ)) 0) := by
    simp_rw [hterm]
    have hfactor : (∑ k ∈ Finset.Icc 1 Z, (e (-((h : ℝ) / (H : ℝ)))) ^ k)
        = e (-((h : ℝ) / (H : ℝ))) * ∑ j ∈ Finset.range Z, (e (-((h : ℝ) / (H : ℝ)))) ^ j := by
      have hIcc : Finset.Icc 1 Z = Finset.Ico 1 (Z + 1) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [pow_add, pow_one]
    rw [hfactor, norm_mul, norm_e, one_mul]
    have hdθ : 0 < dist₁ (-((h : ℝ) / (H : ℝ))) 0 := by
      rw [dist₁_neg_zero]; exact dist_pos H h hh1 hhH
    have hb := geom_e_bound (-((h : ℝ) / (H : ℝ))) Z hdθ
    rwa [dist₁_neg_zero] at hb
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-! ### P3 — the L¹ mass -/

/-- The `h = 0` coefficient is `Z/H`, hence `‖ĉ_0(Z)‖ ≤ 1` (using `Z ≤ H`). -/
private lemma norm_fourierCutoff_zero_le (H Z : ℕ) (hH : 0 < H) (hZH : Z ≤ H) :
    ‖fourierCutoff H Z 0‖ ≤ 1 := by
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hval : fourierCutoff H Z 0 = (Z : ℂ) / (H : ℂ) := by
    unfold fourierCutoff
    simp only [Nat.cast_zero, zero_mul, neg_zero, zero_div, e_zero, Finset.sum_const,
               Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
    ring
  rw [hval, norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_one hHR]
  exact_mod_cast hZH

/-- **P3 (the L¹ mass).** `∑_{h<H} ‖ĉ_h(Z)‖ ≤ 2 + log H`, **uniformly in `Z`**:
the `h = 0` term is `≤ 1`, and the `h ≠ 0` terms sum (via P4 and the harmonic
`sum_H_le`) to `≤ 1 + log H`. -/
theorem sum_norm_fourierCutoff_le (H Z : ℕ) (hH : 0 < H) (hZH : Z ≤ H) :
    ∑ h ∈ Finset.range H, ‖fourierCutoff H Z h‖ ≤ 2 + Real.log H := by
  rcases lt_or_ge H 2 with hH1 | hH2
  · -- `0 < H < 2`, i.e. `H = 1`: a single `h = 0` term.
    have hHeq : H = 1 := by omega
    subst hHeq
    rw [Finset.range_one, Finset.sum_singleton]
    have hb := norm_fourierCutoff_zero_le 1 Z (by norm_num) hZH
    simp only [Nat.cast_one, Real.log_one]
    linarith [hb]
  · have hHne : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
    have hbound : ∀ h ∈ Finset.range H, ‖fourierCutoff H Z h‖
        ≤ (if h = 0 then (1 : ℝ) else (1 / (H : ℝ)) * (1 / (2 * dist₁ ((h : ℝ) / (H : ℝ)) 0))) := by
      intro h hh
      rw [Finset.mem_range] at hh
      by_cases h0 : h = 0
      · rw [if_pos h0, h0]
        exact norm_fourierCutoff_zero_le H Z hH hZH
      · rw [if_neg h0]
        exact norm_fourierCutoff_le H Z h (Nat.one_le_iff_ne_zero.mpr h0) hh
    calc ∑ h ∈ Finset.range H, ‖fourierCutoff H Z h‖
        ≤ ∑ h ∈ Finset.range H,
            (if h = 0 then (1 : ℝ) else (1 / (H : ℝ)) * (1 / (2 * dist₁ ((h : ℝ) / (H : ℝ)) 0))) :=
          Finset.sum_le_sum hbound
      _ = 1 + (1 / (H : ℝ)) *
            ∑ h ∈ Finset.range H,
              (if h = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((h : ℝ) / (H : ℝ)) 0)) := by
          have hpt : ∀ h : ℕ,
              (if h = 0 then (1 : ℝ) else (1 / (H : ℝ)) * (1 / (2 * dist₁ ((h : ℝ) / (H : ℝ)) 0)))
                = (if h = 0 then (1 : ℝ) else 0)
                  + (1 / (H : ℝ)) *
                    (if h = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((h : ℝ) / (H : ℝ)) 0)) := by
            intro h; by_cases h0 : h = 0 <;> simp [h0]
          rw [Finset.sum_congr rfl (fun h _ => hpt h), Finset.sum_add_distrib, ← Finset.mul_sum]
          have hone : ∑ h ∈ Finset.range H, (if h = 0 then (1 : ℝ) else 0) = 1 := by
            simp [hH]
          rw [hone]
      _ ≤ 1 + (1 / (H : ℝ)) * ((H : ℝ) * (1 + Real.log H)) := by
          have hstep := mul_le_mul_of_nonneg_left (sum_H_le H hH2)
            (by positivity : (0 : ℝ) ≤ 1 / (H : ℝ))
          linarith [hstep]
      _ = 2 + Real.log H := by
          rw [← mul_assoc, one_div, inv_mul_cancel₀ hHne, one_mul]; ring

/-! ### The bilinear factorization corollary (feeds L2) -/

/-- **Bilinear factorization (feeds V2.LS-bil's L2).** A sharp-cutoff bilinear
character sum splits into `H` clean product twists.  The cutoff length
`Z m = min (Y / m, H)` (Nat division) sits on the `m`-side (it carries the
`m`-dependent `mn ≤ Y` constraint), while `e(hn/H)` twists the `n`-side; the
`Z`-uniformity of P3/P4 is what makes the `m`-dependent lengths harmless.

On `n ∈ [1, H]` with `m ≥ 1`, `n ≤ Z m ↔ m·n ≤ Y`, so P2 replaces the indicator
`1_{mn ≤ Y}` and `χ(mn) = χ(m)χ(n)` separates the variables. -/
theorem bilinear_factorization {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b : ℕ → ℂ) (Y M H : ℕ) (hH : 0 < H) :
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 H).filter (fun n => m * n ≤ Y),
        a m * b n * χ ((m * n : ℕ) : ZMod q))
      = ∑ h ∈ Finset.range H,
          (∑ m ∈ Finset.Icc 1 M,
              a m * fourierCutoff H (min (Y / m) H) h * χ ((m : ℕ) : ZMod q))
            * (∑ n ∈ Finset.Icc 1 H,
                b n * e ((h : ℝ) * (n : ℝ) / (H : ℝ)) * χ ((n : ℕ) : ZMod q)) := by
  have hstep :
      (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 H).filter (fun n => m * n ≤ Y),
          a m * b n * χ ((m * n : ℕ) : ZMod q))
        = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 H, ∑ h ∈ Finset.range H,
            (a m * fourierCutoff H (min (Y / m) H) h * χ ((m : ℕ) : ZMod q))
              * (b n * e ((h : ℝ) * (n : ℝ) / (H : ℝ)) * χ ((n : ℕ) : ZMod q)) := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_Icc] at hm
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_Icc] at hn
    have hZle : min (Y / m) H ≤ H := min_le_right _ _
    have hequiv : (m * n ≤ Y) ↔ (n ≤ min (Y / m) H) := by
      rw [le_min_iff, Nat.le_div_iff_mul_le hm.1]
      constructor
      · intro h; exact ⟨by rw [mul_comm]; exact h, hn.2⟩
      · intro h; rw [mul_comm]; exact h.1
    have hind : (if m * n ≤ Y then (a m * b n * χ ((m * n : ℕ) : ZMod q)) else 0)
        = (∑ h ∈ Finset.range H,
              fourierCutoff H (min (Y / m) H) h * e ((h : ℝ) * (n : ℝ) / (H : ℝ)))
            * (a m * b n * χ ((m * n : ℕ) : ZMod q)) := by
      rw [← fourierCutoff_indicator H (min (Y / m) H) n hH hn.1 hn.2 hZle]
      by_cases hc : m * n ≤ Y
      · rw [if_pos hc, if_pos (hequiv.mp hc), one_mul]
      · rw [if_neg hc, if_neg (fun hh => hc (hequiv.mpr hh)), zero_mul]
    rw [hind, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [chi_cast_mul]
    ring
  rw [hstep, Finset.sum_congr rfl (fun m _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.sum_mul_sum (Finset.Icc 1 M) (Finset.Icc 1 H)
        (fun m => a m * fourierCutoff H (min (Y / m) H) h * χ ((m : ℕ) : ZMod q))
        (fun n => b n * e ((h : ℝ) * (n : ℝ) / (H : ℝ)) * χ ((n : ℕ) : ZMod q))]

end Salt.BV
