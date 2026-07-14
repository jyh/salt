/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.BilinearLS
import Salt.LS.DvdLS

/-!
# Large sieve track, node PE3c-2: the δ-restricted bilinear shell

Design: `docs/blueprints/flags.md`, entries `2026-07-13 PE3c RECON` and `PE3c-1`.

This file lands the **δ-restricted** fixed-cutoff bilinear large sieve
`bilinear_LS_shell_dvd`: it is the exact `δ`-copy of `Salt.BV.bilinear_LS_shell`
(`Salt/BV/BilinearLS.lean`) with every modulus sum restricted to the multiples of
a fixed `δ ≥ 1` — `(Finset.Icc 1 Q).filter (δ ∣ ·)` — so that the two `char_LS`
consumptions become `char_LS_dvd` (`Salt/LS/DvdLS.lean`) and the frozen
`√(Q²+13N)` factors sharpen to `√(Q²/δ+13N)`.  The improved diagonal is the whole
point: it is what the `α`-side large-conductor discharge (`Salt/Chen/AlphaSide.lean`,
the C3c″ FLAG) needs, in the shape `∑_{f ≤ Q, δ∣f} (f/φf)·bilinPrimEnergy ≤ [shell
with the Q²/δ diagonal]`.

## Structure

The coefficient machinery of `bilinear_LS_shell` — `gammaH`, `bilinCoeffA`,
`bilinCoeffB` (public defs, reused verbatim), and their support lemmas — is
**independent of the modulus index set**; only the character-sieve consumption and
the Cauchy–Schwarz-over-`q` step see the filter.  Because the support lemmas are
`private` to `Salt/BV/BilinearLS.lean`, they are reproven here (identical proofs).
The genuinely new pieces:

* `cs_over_finset_chi` — `cs_over_q_chi` generalized to sum over an **arbitrary**
  `Finset` (both the un-restricted shell and this δ-shell could share it; the
  landed one is stated over `Icc 1 Q` but never uses that structure).
* `bilinear_LS_shell_dvd` — the shell itself, consuming `char_LS_dvd`.

The `δ = 1` specialization recovers the landed (un-restricted) shell; see the
`example` at the end.

Only `[propext, Classical.choice, Quot.sound]` are used (via `char_LS_dvd`).

**Wiring.**  Add to `Salt/BV/All.lean` next to `import Salt.BV.BilinearLS`.
-/

namespace Salt.BV

open scoped BigOperators
open Salt.LS

/-! ### The uniform coefficient bound `γ_h` support (reproved private kernel) -/

/-- `γ_h ≥ 0` (reproof of the `Salt/BV/BilinearLS.lean` private lemma). -/
private lemma gammaH_nonneg (H h : ℕ) : 0 ≤ gammaH H h := by
  unfold gammaH
  by_cases h0 : h = 0
  · rw [if_pos h0]; norm_num
  · rw [if_neg h0]
    have : (0 : ℝ) ≤ 2 * dist₁ ((h : ℝ) / (H : ℝ)) 0 := by
      have := dist₁_nonneg ((h : ℝ) / (H : ℝ)) 0; linarith
    exact mul_nonneg (by positivity) (by positivity)

/-- **P4, packaged** (reproof).  `‖ĉ_h(min(⌊Y/m⌋,H))‖ ≤ γ_h`. -/
private lemma norm_fourierCutoff_le_gammaH (H Y m h : ℕ) (hH : 0 < H) (hhH : h < H) :
    ‖fourierCutoff H (min (Y / m) H) h‖ ≤ gammaH H h := by
  unfold gammaH
  by_cases h0 : h = 0
  · rw [if_pos h0]
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

/-- **P3 mass** (reproof).  `∑_{h<H} γ_h ≤ 2 + log H`. -/
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
          have hstep := mul_le_mul_of_nonneg_left (sum_H_le H hH2)
            (by positivity : (0 : ℝ) ≤ 1 / (H : ℝ))
          linarith [hstep]
      _ = 2 + Real.log H := by
          rw [← mul_assoc, one_div, inv_mul_cancel₀ hHne, one_mul]; ring

/-! ### The nested weighted Cauchy–Schwarz over an arbitrary `Finset` -/

/-- **Nested weighted Cauchy–Schwarz (arbitrary index set).**  The generalization of
`Salt/BV/BilinearLS.lean`'s private `cs_over_q_chi` (stated over `Icc 1 Q`, but its
proof never uses that structure) to an **arbitrary** `Finset`.  For `w q ≥ 0` and
per-index data `P, R, C` with `C q ≤ √(P q)·√(R q)`,
`∑_q w_q C_q ≤ √(∑_q w_q P_q)·√(∑_q w_q R_q)`.  Both the un-restricted shell and the
δ-restricted shell (`bilinear_LS_shell_dvd`) can consume this. -/
theorem cs_over_finset_chi {ι : Type*} (s : Finset ι) (w P R C : ι → ℝ)
    (hw : ∀ q, 0 ≤ w q) (hP : ∀ q, 0 ≤ P q) (hR : ∀ q, 0 ≤ R q)
    (hC : ∀ q, C q ≤ Real.sqrt (P q) * Real.sqrt (R q)) :
    ∑ q ∈ s, w q * C q
      ≤ Real.sqrt (∑ q ∈ s, w q * P q) * Real.sqrt (∑ q ∈ s, w q * R q) := by
  have hsumP : 0 ≤ ∑ q ∈ s, w q * P q :=
    Finset.sum_nonneg (fun q _ => mul_nonneg (hw q) (hP q))
  have hstep1 : ∑ q ∈ s, w q * C q
      ≤ ∑ q ∈ s, Real.sqrt (w q * P q) * Real.sqrt (w q * R q) := by
    apply Finset.sum_le_sum
    intro q _
    calc w q * C q ≤ w q * (Real.sqrt (P q) * Real.sqrt (R q)) :=
          mul_le_mul_of_nonneg_left (hC q) (hw q)
      _ = Real.sqrt (w q * P q) * Real.sqrt (w q * R q) := by
          rw [Real.sqrt_mul (hw q), Real.sqrt_mul (hw q), mul_mul_mul_comm,
              Real.mul_self_sqrt (hw q)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun q => Real.sqrt (w q * P q)) (fun q => Real.sqrt (w q * R q))
  have hsqP : ∀ q, (Real.sqrt (w q * P q)) ^ 2 = w q * P q := fun q =>
    Real.sq_sqrt (mul_nonneg (hw q) (hP q))
  have hsqR : ∀ q, (Real.sqrt (w q * R q)) ^ 2 = w q * R q := fun q =>
    Real.sq_sqrt (mul_nonneg (hw q) (hR q))
  simp only [hsqP, hsqR] at hcs
  have hLHSnn : 0 ≤ ∑ q ∈ s, Real.sqrt (w q * P q) * Real.sqrt (w q * R q) :=
    Finset.sum_nonneg (fun q _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hfin : (∑ q ∈ s, Real.sqrt (w q * P q) * Real.sqrt (w q * R q))
      ≤ Real.sqrt (∑ q ∈ s, w q * P q) * Real.sqrt (∑ q ∈ s, w q * R q) := by
    rw [← Real.sqrt_mul hsumP, ← Real.sqrt_sq hLHSnn]
    exact Real.sqrt_le_sqrt hcs
  exact le_trans hstep1 hfin

/-! ### The `char_LS`-compatible bilinear coefficients (reproved private support) -/

/-- The range-form `A`-factor equals the `Icc`-form `A`-factor (reproof). -/
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

/-- The range-form `B`-factor equals the `Icc`-form `B`-factor (reproof). -/
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

/-- The `A`-side coefficient mass is controlled by `γ_h²·∑‖a‖²` (reproof). -/
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

/-- The `B`-side coefficient mass equals `∑‖b‖²` (reproof). -/
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

/-! ### The δ-restricted fixed-shell bilinear large sieve -/

open Classical in
/-- **PE3c-2 — V2.LS-bil, δ-restricted fixed-shell form.**  The exact `δ`-copy of
`Salt.BV.bilinear_LS_shell`: for `1 ≤ δ`, `2 ≤ Q`, `0 < H`, coefficient sequences
`a, b`, and a sharp cutoff `m·n ≤ Y`, restricting the modulus sum to the multiples of
`δ` sharpens the frozen `√(Q²+13N)` factors to `√(Q²/δ+13N)`:
```
∑_{q≤Q, δ∣q} (q/φq) ∑_{χ prim} ‖∑_{m≤M} ∑_{n≤H, mn≤Y} a_m b_n χ(mn)‖
  ≤ 2·(1+log H)·√(Q²/δ+13(M+1))·√(Q²/δ+13(H+1))·√(∑‖a‖²)·√(∑‖b‖²).
```
Proof: the landed proof structure verbatim, with `char_LS` replaced by `char_LS_dvd`
(the modulus filter is the only change to the two character-sieve consumptions) and
the Cauchy–Schwarz-over-`q` step handled by `cs_over_finset_chi` over the filtered
index set.  The `κ = 1` collapse (`∑_h γ_h ≤ 2+log H`) is unchanged (the coefficient
machinery is modulus-set-independent). -/
theorem bilinear_LS_shell_dvd {M H Q δ : ℕ} (hδ1 : 1 ≤ δ) (hQ : 2 ≤ Q) (hH : 0 < H)
    (a b : ℕ → ℂ) (Y : ℕ) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => δ ∣ q), ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 H).filter (fun n => m * n ≤ Y),
              a m * b n * χ ((m * n : ℕ) : ZMod q)‖
      ≤ 2 * (1 + Real.log H)
          * Real.sqrt ((Q : ℝ) ^ 2 / δ + 13 * ((M : ℝ) + 1))
          * Real.sqrt ((Q : ℝ) ^ 2 / δ + 13 * ((H : ℝ) + 1))
          * Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
          * Real.sqrt (∑ n ∈ Finset.Icc 1 H, ‖b n‖ ^ 2) := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 Q).filter (fun q => δ ∣ q) with hS
  -- Abbreviations (mirroring `bilinear_LS_shell`).
  set w : ℕ → ℝ := fun q => (q : ℝ) / (q.totient : ℝ) with hw_def
  have hw_nonneg : ∀ q, 0 ≤ w q := fun q => by rw [hw_def]; positivity
  set KA := Real.sqrt ((Q : ℝ) ^ 2 / δ + 13 * ((M : ℝ) + 1)) with hKA
  set KB := Real.sqrt ((Q : ℝ) ^ 2 / δ + 13 * ((H : ℝ) + 1)) with hKB
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
  -- `char_LS_dvd` on the `A`-side: `∑_q w_q P_q ≤ (Q²/δ+13(M+1))·γ_h²·∑‖a‖²`.
  have hAfactor : ∀ h, h < H →
      ∑ q ∈ S, w q * P h q
        ≤ ((Q : ℝ) ^ 2 / δ + 13 * ((M : ℝ) + 1))
          * ((gammaH H h) ^ 2 * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) := by
    intro h hhH
    have hls := char_LS_dvd (N := M + 1) (Q := Q) (δ := δ) hδ1 (bilinCoeffA a H Y h)
    rw [← hS] at hls
    have hcast : ((Q : ℝ) ^ 2 / δ + 13 * ((M + 1 : ℕ) : ℝ))
        = (Q : ℝ) ^ 2 / δ + 13 * ((M : ℝ) + 1) := by push_cast; ring
    rw [hcast] at hls
    calc ∑ q ∈ S, w q * P h q
        = ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
              ‖∑ m ∈ Finset.range (M + 1), bilinCoeffA a H Y h m * χ ((m : ℕ) : ZMod q)‖ ^ 2 := by
          rw [hP_def, hw_def, hAf_def]
      _ ≤ ((Q : ℝ) ^ 2 / δ + 13 * ((M : ℝ) + 1))
            * ∑ m ∈ Finset.range (M + 1), ‖bilinCoeffA a H Y h m‖ ^ 2 := hls
      _ ≤ ((Q : ℝ) ^ 2 / δ + 13 * ((M : ℝ) + 1))
            * ((gammaH H h) ^ 2 * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left (bilinCoeffA_mass_le a H Y h M hH hhH)
          positivity
  -- `char_LS_dvd` on the `B`-side: `∑_q w_q R_q ≤ (Q²/δ+13(H+1))·∑‖b‖²`.
  have hBfactor : ∀ h,
      ∑ q ∈ S, w q * R h q
        ≤ ((Q : ℝ) ^ 2 / δ + 13 * ((H : ℝ) + 1)) * ∑ n ∈ Finset.Icc 1 H, ‖b n‖ ^ 2 := by
    intro h
    have hls := char_LS_dvd (N := H + 1) (Q := Q) (δ := δ) hδ1 (bilinCoeffB b H h)
    rw [← hS] at hls
    have hcast : ((Q : ℝ) ^ 2 / δ + 13 * ((H + 1 : ℕ) : ℝ))
        = (Q : ℝ) ^ 2 / δ + 13 * ((H : ℝ) + 1) := by push_cast; ring
    rw [hcast] at hls
    calc ∑ q ∈ S, w q * R h q
        = ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
              ‖∑ n ∈ Finset.range (H + 1), bilinCoeffB b H h n * χ ((n : ℕ) : ZMod q)‖ ^ 2 := by
          rw [hR_def, hw_def, hBf_def]
      _ ≤ ((Q : ℝ) ^ 2 / δ + 13 * ((H : ℝ) + 1))
            * ∑ n ∈ Finset.range (H + 1), ‖bilinCoeffB b H h n‖ ^ 2 := hls
      _ = ((Q : ℝ) ^ 2 / δ + 13 * ((H : ℝ) + 1)) * ∑ n ∈ Finset.Icc 1 H, ‖b n‖ ^ 2 := by
          rw [bilinCoeffB_mass_eq b H h H]
  -- The per-`h` bound: `∑_q w_q C_q ≤ γ_h · (KA·KB·Sa·Sb)`.
  have hperh : ∀ h ∈ Finset.range H,
      ∑ q ∈ S, w q * C h q ≤ gammaH H h * (KA * KB * Sa * Sb) := by
    intro h hh
    rw [Finset.mem_range] at hh
    have hcs := cs_over_finset_chi S w (P h) (R h) (C h) hw_nonneg (hPnn h) (hRnn h) (hCle h)
    -- `√(∑ w P) ≤ KA · γ_h · Sa`.
    have hAsqrt : Real.sqrt (∑ q ∈ S, w q * P h q)
        ≤ KA * (gammaH H h * Sa) := by
      calc Real.sqrt (∑ q ∈ S, w q * P h q)
          ≤ Real.sqrt (((Q : ℝ) ^ 2 / δ + 13 * ((M : ℝ) + 1))
              * ((gammaH H h) ^ 2 * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)) :=
            Real.sqrt_le_sqrt (hAfactor h hh)
        _ = KA * (gammaH H h * Sa) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _),
                Real.sqrt_sq (gammaH_nonneg H h), hKA, hSa]
    -- `√(∑ w R) ≤ KB · Sb`.
    have hBsqrt : Real.sqrt (∑ q ∈ S, w q * R h q) ≤ KB * Sb := by
      calc Real.sqrt (∑ q ∈ S, w q * R h q)
          ≤ Real.sqrt (((Q : ℝ) ^ 2 / δ + 13 * ((H : ℝ) + 1))
              * ∑ n ∈ Finset.Icc 1 H, ‖b n‖ ^ 2) := Real.sqrt_le_sqrt (hBfactor h)
        _ = KB * Sb := by rw [Real.sqrt_mul (by positivity), hKB, hSb]
    calc ∑ q ∈ S, w q * C h q
        ≤ Real.sqrt (∑ q ∈ S, w q * P h q)
            * Real.sqrt (∑ q ∈ S, w q * R h q) := hcs
      _ ≤ (KA * (gammaH H h * Sa)) * (KB * Sb) := by
          apply mul_le_mul hAsqrt hBsqrt (Real.sqrt_nonneg _)
          exact mul_nonneg hKAnn (mul_nonneg (gammaH_nonneg H h) hSann)
      _ = gammaH H h * (KA * KB * Sa * Sb) := by ring
  -- Assemble: reduce the cutoff via factorization, triangle, swap `h` out, per-`h`.
  calc ∑ q ∈ S, w q *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 H).filter (fun n => m * n ≤ Y),
                a m * b n * χ ((m * n : ℕ) : ZMod q)‖
      ≤ ∑ q ∈ S, w q *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ∑ h ∈ Finset.range H, ‖Af q χ h‖ * ‖Bf q χ h‖ := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        rw [hS, Finset.mem_filter, Finset.mem_Icc] at hq
        have hq1 : 1 ≤ q := hq.1.1
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
    _ = ∑ h ∈ Finset.range H, ∑ q ∈ S, w q * C h q := by
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

/-! ## Sanity: `δ = 1` recovers the landed (un-restricted) shell. -/

open Classical in
/-- At `δ = 1`, `bilinear_LS_shell_dvd` recovers `Salt.BV.bilinear_LS_shell`'s shape:
the filter `(Icc 1 Q).filter (1∣·)` is all of `Icc 1 Q` and `Q²/1 = Q²`. -/
example {M H Q : ℕ} (hQ : 2 ≤ Q) (hH : 0 < H) (a b : ℕ → ℂ) (Y : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 H).filter (fun n => m * n ≤ Y),
              a m * b n * χ ((m * n : ℕ) : ZMod q)‖
      ≤ 2 * (1 + Real.log H)
          * Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((M : ℝ) + 1))
          * Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((H : ℝ) + 1))
          * Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
          * Real.sqrt (∑ n ∈ Finset.Icc 1 H, ‖b n‖ ^ 2) := by
  have h := bilinear_LS_shell_dvd (M := M) (H := H) (Q := Q) (δ := 1) (le_refl 1) hQ hH a b Y
  have hf : (Finset.Icc 1 Q).filter (fun q => (1 : ℕ) ∣ q) = Finset.Icc 1 Q :=
    Finset.filter_true_of_mem (fun q _ => one_dvd q)
  rw [hf] at h
  simpa only [Nat.cast_one, div_one] using h

end Salt.BV
