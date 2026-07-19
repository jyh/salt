/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHExtractW
import Salt.SW.DHBal
import Salt.SW.ZetaEM

/-!
# The weighted pole-cancelled extraction at the COMPLEX zero (`T-BAL` R6@ρ) — `dhAbel_inner_rho`

The complex analog of the DHCore `dhAbel` chain (the β₀ template `dhAbel_inner_le`/
`dhAbel_leg1_le`), run at a NON-REAL zero `ρ` of `L(·,χ)` with `1/2 ≤ Re ρ < 1`, `|Im ρ| ≤ 1`.
Everything is `‖·‖`-level (norm-level): the L(1,χ) main term is now the FULL complex L-value
`L(1,χ)·t^{1−ρ}/(1−ρ)`, and the error carries `1/‖1−ρ‖` (→ `L₂/c₀` via `zfr_harvest`
downstream) in place of the β₀ template's `1/(1−β₀)`.

## The mechanism (the residue carrying `L(1,χ)`)

`A_ρ(t) = Σ_{n≤t} dhA(n)·n^{−ρ}`. Via the symmetric √t hyperbola, the long leg
`Σ_{d≤√t} χ(d)d^{−ρ}·T_ρ(⌊t/d⌋)`, `T_ρ(m) = Σ_{e≤m} e^{−ρ}`, carries the main term: the a-sum
pole (`zeta_partial_em`: `T_ρ(m) = m^{1−ρ}/(1−ρ) + ζ(ρ) + O(m^{−σ})`) shifts the effective
character sum from `s = ρ` (killed: `L(ρ,χ) = 0`) to `s = 1` (`Σ_d χ(d)/d ≈ L(1,χ)`, strip@1).
The `ζ(ρ)` stream and the two short legs are killed by `partial_sum_at_zero_small`.

## Main results

* `norm_zeta_rho_le` — `‖ζ(ρ)‖ ≤ Z₀ + 1/‖1−ρ‖` (complex analog of `abs_zeta_re_le`).
* `norm_cpow_pos_floor_sub_le` — the complex floor/tangent bound `‖y^{1−ρ} − m^{1−ρ}‖ ≤
  ‖1−ρ‖·m^{−σ}` (MVT on the real segment `[m, y]`).
* `dhAbel_hyperbola_rho` — the complex symmetric √t hyperbola for `A_ρ(t)`.
* `emrho_perterm` — the per-`d` EM split of `T_ρ(⌊t/d⌋)` (pole form + floor correction).
* `dhAbel_leg1_rho` — the long-leg main-term extraction (the `L(1,χ)` residue).
* `dhAbel_inner_rho` — the per-`t` inner bound (R6-2@ρ, the analytic heart).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open Complex
open Finset

noncomputable section

namespace Salt.SW

variable {q : ℕ}

/-! ## §0 — the complex `ζ(ρ)` size bound (the `1/‖1−ρ‖` dust) -/

/-- **`‖ζ(ρ)‖` bound.** For `1/2 ≤ Re ρ ≤ 1`, `|Im ρ| ≤ 1`, `ρ ≠ 1`,
`‖ζ(ρ)‖ ≤ Z₀ + 1/‖1−ρ‖` where `Z₀` is the `zetaHol_bound` compactness constant. Complex analog
of `abs_zeta_re_le`: `ζ(ρ) = 1/(ρ−1) + zetaHol ρ`, `‖1/(ρ−1)‖ = 1/‖1−ρ‖`, `‖zetaHol ρ‖ ≤ Z₀`. -/
theorem norm_zeta_rho_le {Z₀ : ℝ}
    (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {ρ : ℂ} (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re ≤ 1) (him : |ρ.im| ≤ 1) (hne : ρ ≠ 1) :
    ‖riemannZeta ρ‖ ≤ Z₀ + 1 / ‖1 - ρ‖ := by
  have hsplit : riemannZeta ρ = 1 / (ρ - 1) + zetaHol ρ := riemannZeta_eq_add_zetaHol hne
  have hZb : ‖zetaHol ρ‖ ≤ Z₀ := hZ ρ hlo hhi him
  have hpole : ‖(1 : ℂ) / (ρ - 1)‖ = 1 / ‖1 - ρ‖ := by
    rw [norm_div, norm_one, ← norm_neg (ρ - 1), neg_sub]
  calc ‖riemannZeta ρ‖ = ‖1 / (ρ - 1) + zetaHol ρ‖ := by rw [hsplit]
    _ ≤ ‖(1 : ℂ) / (ρ - 1)‖ + ‖zetaHol ρ‖ := norm_add_le _ _
    _ ≤ 1 / ‖1 - ρ‖ + Z₀ := by rw [hpole]; linarith
    _ = Z₀ + 1 / ‖1 - ρ‖ := by ring

/-! ## §1 — the complex floor/tangent bound (the `⌊t/d⌋ → t/d` correction) -/

/-- **The complex floor/tangent bound.** For `0 < Re ρ`, `Re ρ < 1`, `1 ≤ m` and `m ≤ y ≤ m+1`,
`‖(y:ℂ)^{1−ρ} − (m:ℂ)^{1−ρ}‖ ≤ ‖1−ρ‖·m^{−Re ρ}`. Mean value inequality for `u ↦ (u:ℂ)^{1−ρ}` on
the real segment `[m, y]`: derivative `(1−ρ)(u:ℂ)^{−ρ}`, norm `‖1−ρ‖·u^{−Re ρ} ≤ ‖1−ρ‖·m^{−Re ρ}`,
times the width `y − m ≤ 1`. -/
theorem norm_cpow_pos_floor_sub_le {ρ : ℂ} (hσ0 : 0 < ρ.re) (hσ1 : ρ.re < 1) {m : ℕ} (hm : 1 ≤ m)
    {y : ℝ} (hmy : (m : ℝ) ≤ y) (hy1 : y ≤ (m : ℝ) + 1) :
    ‖(y : ℂ) ^ (1 - ρ) - ((m : ℕ) : ℂ) ^ (1 - ρ)‖ ≤ ‖1 - ρ‖ * ((m : ℕ) : ℝ) ^ (-ρ.re) := by
  set s : ℂ := 1 - ρ with hs
  have hsne : s ≠ 0 := by rw [hs]; intro h; apply hσ1.ne'; have := sub_eq_zero.mp h; simp [← this]
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set S : Set ℝ := Set.Icc (m : ℝ) y with hSdef
  have hconv : Convex ℝ S := convex_Icc _ _
  have hderiv : ∀ x ∈ S,
      HasDerivWithinAt (fun u : ℝ => (u : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) S x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rw [hSdef, Set.mem_Icc] at hx; have : (0 : ℝ) < x := lt_of_lt_of_le hm0 hx.1; linarith
    exact (hasDerivAt_ofReal_cpow_const hx0 hsne).hasDerivWithinAt
  have hbound : ∀ x ∈ S, ‖s * (x : ℂ) ^ (s - 1)‖ ≤ ‖s‖ * ((m : ℕ) : ℝ) ^ (-ρ.re) := by
    intro x hx
    rw [hSdef, Set.mem_Icc] at hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hm0 hx.1
    have hnormx : ‖(x : ℂ) ^ (s - 1)‖ = x ^ (s - 1).re := Complex.norm_cpow_eq_rpow_re_of_pos hx0 _
    have hsre : (s - 1).re = -ρ.re := by rw [hs]; simp
    have hmono : x ^ (-ρ.re) ≤ ((m : ℕ) : ℝ) ^ (-ρ.re) :=
      Real.rpow_le_rpow_of_nonpos hm0 hx.1 (by linarith)
    rw [norm_mul, hnormx, hsre]
    exact mul_le_mul_of_nonneg_left hmono (norm_nonneg s)
  have hmS : (m : ℝ) ∈ S := by rw [hSdef, Set.mem_Icc]; exact ⟨le_refl _, hmy⟩
  have hyS : y ∈ S := by rw [hSdef, Set.mem_Icc]; exact ⟨hmy, le_refl _⟩
  have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hmS hyS
  have hcast : ((m : ℝ) : ℂ) = ((m : ℕ) : ℂ) := by push_cast; ring
  rw [hcast, hs] at hmvt
  have hwidth : ‖y - (m : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
  have hCnn : (0 : ℝ) ≤ ‖s‖ * ((m : ℕ) : ℝ) ^ (-ρ.re) :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hm0.le _)
  calc ‖(y : ℂ) ^ (1 - ρ) - ((m : ℕ) : ℂ) ^ (1 - ρ)‖
      ≤ (‖s‖ * ((m : ℕ) : ℝ) ^ (-ρ.re)) * ‖y - (m : ℝ)‖ := hmvt
    _ ≤ (‖s‖ * ((m : ℕ) : ℝ) ^ (-ρ.re)) * 1 := mul_le_mul_of_nonneg_left hwidth hCnn
    _ = ‖1 - ρ‖ * ((m : ℕ) : ℝ) ^ (-ρ.re) := by rw [mul_one, hs]

/-! ## §2 — the complex symmetric √t hyperbola -/

/-- **The complex symmetric √t hyperbola.** For any `χ`, `ρ`, `t`,
`A_ρ(t) = Σ_{n≤t} dhA(n)·n^{−ρ}` factors as `Leg₁ + Leg₂ − Corner` over the symmetric cut `√t`,
with `Leg₁ = Σ_{d≤√t} χ_ℝ(d)d^{−ρ}·T_ρ(⌊t/d⌋)`, `Leg₂` the transpose, `Corner` the overlap. The
complex analog of `dhAbel_hyperbola` (`sum_divisors_eq_hyperbola_symm` at `ℂ`). -/
theorem dhAbel_hyperbola_rho (χ : DirichletCharacter ℂ q) {ρ : ℂ} (t : ℕ) :
    ∑ n ∈ Finset.Icc 1 t, (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ)
      = (∑ d ∈ Finset.Icc 1 (Nat.sqrt t), ((chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ))
            * ∑ e ∈ Finset.Icc 1 (t / d), (e : ℂ) ^ (-ρ))
        + (∑ e ∈ Finset.Icc 1 (Nat.sqrt t), (e : ℂ) ^ (-ρ)
            * ∑ d ∈ Finset.Icc 1 (t / e), (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ))
        - (∑ d ∈ Finset.Icc 1 (Nat.sqrt t), (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ))
          * ∑ e ∈ Finset.Icc 1 (Nat.sqrt t), (e : ℂ) ^ (-ρ) := by
  have hrw : (∑ n ∈ Finset.Icc 1 t, (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ))
      = ∑ n ∈ Finset.Icc 1 t, ∑ d ∈ n.divisors,
          ((chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)) * ((n / d : ℕ) : ℂ) ^ (-ρ) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_Icc] at hn
    have hdhA : (dhA χ n : ℂ) = ∑ d ∈ n.divisors, (chiRe χ d : ℂ) := by
      rw [dhA, Complex.ofReal_sum]
    rw [hdhA, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hsplit : (n : ℂ) ^ (-ρ) = (d : ℂ) ^ (-ρ) * ((n / d : ℕ) : ℂ) ^ (-ρ) := by
      have hmul := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg (n / d)) (-ρ)
      simp only [Complex.ofReal_natCast] at hmul
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd] at hmul
      rw [hmul]
    rw [hsplit]; ring
  rw [hrw]
  exact sum_divisors_eq_hyperbola_symm (fun d => (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ))
    (fun e => (e : ℂ) ^ (-ρ)) t

/-! ## §3 — the per-`d` EM split of `T_ρ(⌊t/d⌋)` -/

/-- **The per-`d` EM split.** For `1/2 ≤ Re ρ < 1`, `|Im ρ| ≤ 1` and `1 ≤ d ≤ t`,
`‖T_ρ(⌊t/d⌋) − (t/d)^{1−ρ}/(1−ρ) − ζ(ρ)‖ ≤ (9 + 8‖ρ‖)·⌊t/d⌋^{−Re ρ}`,
`T_ρ(m) = Σ_{e≤m} e^{−ρ}`, the real ratio `t/d` in the main. The `zeta_partial_em` pole form at
`s = ρ`, `y = ⌊t/d⌋`, plus the floor correction `⌊t/d⌋ → t/d` (`norm_cpow_pos_floor_sub_le`). -/
theorem emrho_perterm {ρ : ℂ} (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re < 1) (him : |ρ.im| ≤ 1)
    {d t : ℕ} (hd : 1 ≤ d) (hdt : d ≤ t) :
    ‖(∑ e ∈ Finset.Icc 1 (t / d), (e : ℂ) ^ (-ρ))
        - ((t : ℂ) / (d : ℂ)) ^ (1 - ρ) / (1 - ρ) - riemannZeta ρ‖
      ≤ (9 + 8 * ‖ρ‖) * ((t / d : ℕ) : ℝ) ^ (-ρ.re) := by
  have hσ0 : 0 < ρ.re := by linarith
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdt1 : 1 ≤ t / d := (Nat.one_le_div_iff (by omega)).mpr hdt
  have hf0 : (0 : ℝ) < ((t / d : ℕ) : ℝ) := by exact_mod_cast hdt1
  have hfnn : (0 : ℝ) ≤ ((t / d : ℕ) : ℝ) ^ (-ρ.re) := Real.rpow_nonneg hf0.le _
  have hsne : (1 - ρ) ≠ 0 := by
    intro h
    have he : (1 : ℂ) = ρ := sub_eq_zero.mp h
    have hre : ρ.re = 1 := by rw [← he]; simp
    linarith [hhi]
  have hcastdiv : ((((t : ℝ) / (d : ℝ)) : ℝ) : ℂ) = (t : ℂ) / (d : ℂ) := by
    push_cast; ring
  -- the EM pole form at `y = ⌊t/d⌋`
  have hem := zeta_partial_em (s := ρ) hlo hhi him hdt1
  -- the floor correction `⌊t/d⌋ → t/d`
  have hle : ((t / d : ℕ) : ℝ) ≤ (t : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hlt : (t : ℝ) / (d : ℝ) ≤ ((t / d : ℕ) : ℝ) + 1 := by
    have hmod : t < (t / d + 1) * d := by
      have h1 := Nat.div_add_mod t d
      have h2 : t % d < d := Nat.mod_lt t (by omega)
      nlinarith
    have hR : (t : ℝ) < (((t / d : ℕ) : ℝ) + 1) * (d : ℝ) := by exact_mod_cast hmod
    rw [div_le_iff₀ hd0]; nlinarith [hR]
  have hFE := norm_cpow_pos_floor_sub_le hσ0 hhi hdt1 hle hlt
  rw [hcastdiv] at hFE
  have hFEdiv : ‖((t / d : ℕ) : ℂ) ^ (1 - ρ) / (1 - ρ)
        - ((t : ℂ) / (d : ℂ)) ^ (1 - ρ) / (1 - ρ)‖
      ≤ ((t / d : ℕ) : ℝ) ^ (-ρ.re) := by
    rw [div_sub_div_same, norm_div]
    rw [div_le_iff₀ (norm_pos_iff.mpr hsne)]
    calc ‖((t / d : ℕ) : ℂ) ^ (1 - ρ) - ((t : ℂ) / (d : ℂ)) ^ (1 - ρ)‖
        = ‖((t : ℂ) / (d : ℂ)) ^ (1 - ρ) - ((t / d : ℕ) : ℂ) ^ (1 - ρ)‖ := norm_sub_rev _ _
      _ ≤ ‖1 - ρ‖ * ((t / d : ℕ) : ℝ) ^ (-ρ.re) := hFE
      _ = ((t / d : ℕ) : ℝ) ^ (-ρ.re) * ‖1 - ρ‖ := by ring
  -- combine
  have hsplit : (∑ e ∈ Finset.Icc 1 (t / d), (e : ℂ) ^ (-ρ))
        - ((t : ℂ) / (d : ℂ)) ^ (1 - ρ) / (1 - ρ) - riemannZeta ρ
      = ((∑ e ∈ Finset.Icc 1 (t / d), (e : ℂ) ^ (-ρ))
            - (((t / d : ℕ) : ℂ) ^ (1 - ρ) / (1 - ρ) + riemannZeta ρ))
        + (((t / d : ℕ) : ℂ) ^ (1 - ρ) / (1 - ρ)
            - ((t : ℂ) / (d : ℂ)) ^ (1 - ρ) / (1 - ρ)) := by ring
  rw [hsplit]
  calc ‖((∑ e ∈ Finset.Icc 1 (t / d), (e : ℂ) ^ (-ρ))
            - (((t / d : ℕ) : ℂ) ^ (1 - ρ) / (1 - ρ) + riemannZeta ρ))
        + (((t / d : ℕ) : ℂ) ^ (1 - ρ) / (1 - ρ)
            - ((t : ℂ) / (d : ℂ)) ^ (1 - ρ) / (1 - ρ))‖
      ≤ ‖(∑ e ∈ Finset.Icc 1 (t / d), (e : ℂ) ^ (-ρ))
            - (((t / d : ℕ) : ℂ) ^ (1 - ρ) / (1 - ρ) + riemannZeta ρ)‖
        + ‖((t / d : ℕ) : ℂ) ^ (1 - ρ) / (1 - ρ)
            - ((t : ℂ) / (d : ℂ)) ^ (1 - ρ) / (1 - ρ)‖ := norm_add_le _ _
    _ ≤ 8 * (1 + ‖ρ‖) * ((t / d : ℕ) : ℝ) ^ (-ρ.re) + ((t / d : ℕ) : ℝ) ^ (-ρ.re) :=
        add_le_add hem hFEdiv
    _ ≤ (9 + 8 * ‖ρ‖) * ((t / d : ℕ) : ℝ) ^ (-ρ.re) := by nlinarith [hfnn]

/-! ## §4 — the clean-main cpow identity + the long-leg extraction -/

/-- **The clean-main cpow identity.** For `1 ≤ d`, `(d:ℂ)^{−ρ}·(t/d)^{1−ρ} = (t:ℂ)^{1−ρ}/(d:ℂ)`.
The complex analog of the real `hclean` cpow algebra (`Complex.mul_cpow_ofReal_nonneg` +
`Complex.inv_cpow` + `cpow_add`). -/
lemma clean_cpow_term {d t : ℕ} (hd : 1 ≤ d) (ρ : ℂ) :
    (d : ℂ) ^ (-ρ) * ((t : ℂ) / (d : ℂ)) ^ (1 - ρ) = (t : ℂ) ^ (1 - ρ) / (d : ℂ) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have harg : (d : ℂ).arg ≠ Real.pi := by
    rw [show (d : ℂ) = (((d : ℝ)) : ℂ) from by push_cast; ring,
      Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg d)]
    exact fun h => Real.pi_ne_zero h.symm
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have hdinv0 : (0 : ℝ) ≤ ((d : ℝ))⁻¹ := by positivity
  have hcast_t : (t : ℂ) = (((t : ℝ)) : ℂ) := by push_cast; ring
  have hcast_dinv : (d : ℂ)⁻¹ = ((((d : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; ring
  have hdiv : ((t : ℂ) / (d : ℂ)) ^ (1 - ρ) = (t : ℂ) ^ (1 - ρ) * ((d : ℂ) ^ (1 - ρ))⁻¹ := by
    rw [div_eq_mul_inv, hcast_t, hcast_dinv, Complex.mul_cpow_ofReal_nonneg ht0 hdinv0,
      ← hcast_t, ← hcast_dinv, Complex.inv_cpow _ _ harg]
  rw [hdiv]
  have hexp : (d : ℂ) ^ (-ρ) * ((d : ℂ) ^ (1 - ρ))⁻¹ = (d : ℂ)⁻¹ := by
    rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hd0,
      show -ρ + -(1 - ρ) = (-1 : ℂ) by ring, Complex.cpow_neg, Complex.cpow_one]
  calc (d : ℂ) ^ (-ρ) * ((t : ℂ) ^ (1 - ρ) * ((d : ℂ) ^ (1 - ρ))⁻¹)
      = (t : ℂ) ^ (1 - ρ) * ((d : ℂ) ^ (-ρ) * ((d : ℂ) ^ (1 - ρ))⁻¹) := by ring
    _ = (t : ℂ) ^ (1 - ρ) * (d : ℂ)⁻¹ := by rw [hexp]
    _ = (t : ℂ) ^ (1 - ρ) / (d : ℂ) := by rw [div_eq_mul_inv]

/-- **The long-leg extraction (the `L(1,χ)` residue).** For a primitive real `χ` at a NON-REAL
zero `ρ` (`1/2 ≤ Re ρ < 1`, `|Im ρ| ≤ 1`),
`‖Leg₁ − L(1,χ)·t^{1−ρ}/(1−ρ)‖ ≤ (12M/‖1−ρ‖ + 2(9+8‖ρ‖) + 2(Z₀+1/‖1−ρ‖)·P)·t^{1/2−Re ρ}`,
`Leg₁ = Σ_{d≤√t} χ_ℝ(d)d^{−ρ}·T_ρ(⌊t/d⌋)`, `P = 3M(1+‖ρ‖/Re ρ)`. The a-sum pole
(`emrho_perterm`) extracts `L(1,χ)` from `Σ_{d≤√t} χ(d)/d` (strip@1); the `ζ(ρ)` stream is killed
by `partial_sum_at_zero_small`. Complex analog of `dhAbel_leg1_le`. -/
theorem dhAbel_leg1_rho [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re < 1)
    (him : |ρ.im| ≤ 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {t : ℕ} (ht : 1 ≤ t) :
    ‖(∑ d ∈ Finset.Icc 1 (Nat.sqrt t), ((chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ))
          * ∑ e ∈ Finset.Icc 1 (t / d), (e : ℂ) ^ (-ρ))
        - DirichletCharacter.LFunction χ 1 * (t : ℂ) ^ (1 - ρ) / (1 - ρ)‖
      ≤ (12 * (Real.sqrt q * (1 + Real.log q)) / ‖1 - ρ‖ + 2 * (9 + 8 * ‖ρ‖)
          + 2 * (Z₀ + 1 / ‖1 - ρ‖)
            * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re)))
        * (t : ℝ) ^ (1 / 2 - ρ.re) := by
  set M : ℝ := Real.sqrt q * (1 + Real.log q) with hMdef
  set r : ℕ := Nat.sqrt t with hrdef
  set D : ℝ := (t : ℝ) ^ (1 / 2 - ρ.re) with hDdef
  set L₁ : ℂ := DirichletCharacter.LFunction χ 1 with hL1def
  set Zρ : ℂ := riemannZeta ρ with hZρdef
  set P : ℝ := 3 * M * (1 + ‖ρ‖ / ρ.re) with hPdef
  set Wρ : ℝ := Z₀ + 1 / ‖1 - ρ‖ with hWρdef
  have hσ0 : 0 < ρ.re := by linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hne : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  haveI : Fact (1 < q) := ⟨by omega⟩
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at hhi; simp at hhi
  have hsne : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (fun h => hρ1 h.symm)
  have hnpos : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hsne
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hDnn : 0 ≤ D := Real.rpow_nonneg ht0.le _
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    have h2 : 0 ≤ 1 + ‖ρ‖ / ρ.re := by
      have := div_nonneg (norm_nonneg ρ) hσ0.le; linarith
    exact mul_nonneg (mul_nonneg (by norm_num) hMnn) h2
  have hWρnn : 0 ≤ Wρ := by
    rw [hWρdef]
    have hZ0nn : 0 ≤ Z₀ := le_trans (norm_nonneg _) (hZ ρ hlo hhi.le him)
    have hpos : 0 ≤ 1 / ‖1 - ρ‖ := by positivity
    linarith
  have hr1 : 1 ≤ r := by
    rw [hrdef]; calc 1 = Nat.sqrt 1 := Nat.sqrt_one.symm
      _ ≤ Nat.sqrt t := Nat.sqrt_le_sqrt ht
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hrt : r ≤ t := by rw [hrdef]; exact Nat.sqrt_le_self t
  have hPV : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod q)‖ ≤ M :=
    fun u => Salt.BV.polya_vinogradov χ hχ hq u
  -- the norm of the complex power `‖t^{1−ρ}‖ = t^{1−σ}`
  have htnorm : ‖(t : ℂ) ^ (1 - ρ)‖ = (t : ℝ) ^ (1 - ρ.re) := by
    rw [show (t : ℂ) = (((t : ℝ)) : ℂ) from by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
  -- STEP 1 : the clean-main identity
  have hclean : (∑ d ∈ Finset.Icc 1 r,
        ((chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)) * ((t : ℂ) / (d : ℂ)) ^ (1 - ρ) / (1 - ρ))
      = (t : ℂ) ^ (1 - ρ) / (1 - ρ) * ∑ d ∈ Finset.Icc 1 r, (chiRe χ d : ℂ) * (d : ℂ)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.mem_Icc] at hd
    rw [show ((chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)) * ((t : ℂ) / (d : ℂ)) ^ (1 - ρ) / (1 - ρ)
        = ((chiRe χ d : ℂ) / (1 - ρ)) * ((d : ℂ) ^ (-ρ) * ((t : ℂ) / (d : ℂ)) ^ (1 - ρ)) by ring,
      clean_cpow_term (d := d) (t := t) hd.1 ρ]
    ring
  -- STEP 2 : `‖Sr − L₁‖ ≤ 6M/r`
  set Sr : ℂ := ∑ d ∈ Finset.Icc 1 r, (chiRe χ d : ℂ) * (d : ℂ)⁻¹ with hSrdef
  have hSrL1 : ‖L₁ - Sr‖ ≤ 6 * M / (r : ℝ) := by
    have hstrip := norm_LFunction_sub_partial_le_strip χ hne hq hPV (s := (1 : ℂ))
      (by rw [Complex.one_re]; norm_num) (le_of_eq Complex.one_re) hr1
    have hval : 3 * M * (1 + ‖(1 : ℂ)‖ / (1 : ℂ).re) * (r : ℝ) ^ (-(1 : ℂ).re)
        = 6 * M / (r : ℝ) := by
      rw [Complex.one_re, norm_one, Real.rpow_neg (Nat.cast_nonneg r), Real.rpow_one,
        div_eq_mul_inv]; ring
    have hconv : ∑ d ∈ Finset.Icc 1 r, χ (d : ZMod q) * (d : ℂ) ^ (-(1 : ℂ)) = Sr := by
      rw [hSrdef]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [chiRe_ofReal χ hsq d, Complex.cpow_neg, Complex.cpow_one]
    rw [hval, hconv, ← hL1def] at hstrip; exact hstrip
  -- STEP 3 : `‖clean_main − L₁·main₀‖ ≤ 12M/‖1−ρ‖·D`
  have hrinv : (t : ℝ) ^ (1 - ρ.re) * (r : ℝ)⁻¹ ≤ 2 * D := by
    have hb := sqrt_pow_bound (a := (-1 : ℝ)) (by norm_num) (by norm_num) (t := t) ht
    rw [← hrdef, Real.rpow_neg_one] at hb
    calc (t : ℝ) ^ (1 - ρ.re) * (r : ℝ)⁻¹
        ≤ (t : ℝ) ^ (1 - ρ.re) * (2 * (t : ℝ) ^ ((-1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht0.le _)
      _ = 2 * ((t : ℝ) ^ (1 - ρ.re) * (t : ℝ) ^ ((-1 : ℝ) / 2)) := by ring
      _ = 2 * D := by rw [hDdef, ← Real.rpow_add ht0]; congr 2; ring
  have hCM : ‖(t : ℂ) ^ (1 - ρ) / (1 - ρ) * Sr - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ)‖
      ≤ 12 * M / ‖1 - ρ‖ * D := by
    have heq : (t : ℂ) ^ (1 - ρ) / (1 - ρ) * Sr - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ)
        = ((t : ℂ) ^ (1 - ρ) / (1 - ρ)) * (Sr - L₁) := by ring
    rw [heq, norm_mul, norm_div, htnorm, norm_sub_rev Sr L₁]
    calc (t : ℝ) ^ (1 - ρ.re) / ‖1 - ρ‖ * ‖L₁ - Sr‖
        ≤ (t : ℝ) ^ (1 - ρ.re) / ‖1 - ρ‖ * (6 * M / (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hSrL1 (by positivity)
      _ = 6 * M / ‖1 - ρ‖ * ((t : ℝ) ^ (1 - ρ.re) * (r : ℝ)⁻¹) := by
          rw [div_eq_mul_inv (6 * M)]; ring
      _ ≤ 6 * M / ‖1 - ρ‖ * (2 * D) := by
          apply mul_le_mul_of_nonneg_left hrinv (by positivity)
      _ = 12 * M / ‖1 - ρ‖ * D := by ring
  -- STEP 4 : the remainder `G` and the `ζ(ρ)` stream `Zρ·Br`
  set Br : ℂ := ∑ d ∈ Finset.Icc 1 r, (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ) with hBrdef
  set G : ℂ := ∑ d ∈ Finset.Icc 1 r, ((chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ))
      * ((∑ e ∈ Finset.Icc 1 (t / d), (e : ℂ) ^ (-ρ))
          - ((t : ℂ) / (d : ℂ)) ^ (1 - ρ) / (1 - ρ) - Zρ) with hGdef
  have hLeg1eq : (∑ d ∈ Finset.Icc 1 r, ((chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ))
        * ∑ e ∈ Finset.Icc 1 (t / d), (e : ℂ) ^ (-ρ))
      = (∑ d ∈ Finset.Icc 1 r,
            ((chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)) * ((t : ℂ) / (d : ℂ)) ^ (1 - ρ) / (1 - ρ))
        + (G + Zρ * Br) := by
    rw [hGdef, hBrdef, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  -- `‖G‖ ≤ 2(9+8‖ρ‖)·D`
  have hGbound : ‖G‖ ≤ 2 * (9 + 8 * ‖ρ‖) * D := by
    have h1 : ‖G‖ ≤ ∑ d ∈ Finset.Icc 1 r, (d : ℝ) ^ (-ρ.re)
        * ((9 + 8 * ‖ρ‖) * ((t / d : ℕ) : ℝ) ^ (-ρ.re)) := by
      rw [hGdef]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d hd => ?_))
      rw [Finset.mem_Icc] at hd
      rw [norm_mul]
      apply mul_le_mul _ (emrho_perterm hlo hhi him hd.1 (le_trans hd.2 hrt))
        (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
      rw [norm_mul, norm_natCast_cpow_neg hσ0 d]
      calc ‖(chiRe χ d : ℂ)‖ * (d : ℝ) ^ (-ρ.re)
          ≤ 1 * (d : ℝ) ^ (-ρ.re) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
            rw [Complex.norm_real, Real.norm_eq_abs]; exact chiRe_abs_le_one χ d
        _ = (d : ℝ) ^ (-ρ.re) := one_mul _
    have h2 : ∑ d ∈ Finset.Icc 1 r, (d : ℝ) ^ (-ρ.re)
          * ((9 + 8 * ‖ρ‖) * ((t / d : ℕ) : ℝ) ^ (-ρ.re))
        ≤ ∑ d ∈ Finset.Icc 1 r, (9 + 8 * ‖ρ‖) * (2 * (t : ℝ) ^ (-ρ.re)) := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      rw [Finset.mem_Icc] at hd
      have htr := term_rpow_le (β := ρ.re) (by linarith) (by linarith) (e := d) (t := t)
        hd.1 (le_trans hd.2 hrt)
      have hcoefnn : (0 : ℝ) ≤ 9 + 8 * ‖ρ‖ := by positivity
      calc (d : ℝ) ^ (-ρ.re) * ((9 + 8 * ‖ρ‖) * ((t / d : ℕ) : ℝ) ^ (-ρ.re))
          = (9 + 8 * ‖ρ‖) * ((d : ℝ) ^ (-ρ.re) * ((t / d : ℕ) : ℝ) ^ (-ρ.re)) := by ring
        _ ≤ (9 + 8 * ‖ρ‖) * (2 * (t : ℝ) ^ (-ρ.re)) :=
            mul_le_mul_of_nonneg_left htr hcoefnn
    have h3 : ∑ d ∈ Finset.Icc 1 r, (9 + 8 * ‖ρ‖) * (2 * (t : ℝ) ^ (-ρ.re))
        = 2 * (9 + 8 * ‖ρ‖) * ((r : ℝ) * (t : ℝ) ^ (-ρ.re)) := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
    have h4 : (r : ℝ) * (t : ℝ) ^ (-ρ.re) ≤ D := by
      rw [hDdef, hrdef]; exact natSqrt_mul_rpow_le ht
    have hcoefnn : (0 : ℝ) ≤ 2 * (9 + 8 * ‖ρ‖) := by positivity
    calc ‖G‖ ≤ ∑ d ∈ Finset.Icc 1 r, (d : ℝ) ^ (-ρ.re)
              * ((9 + 8 * ‖ρ‖) * ((t / d : ℕ) : ℝ) ^ (-ρ.re)) := h1
      _ ≤ ∑ d ∈ Finset.Icc 1 r, (9 + 8 * ‖ρ‖) * (2 * (t : ℝ) ^ (-ρ.re)) := h2
      _ = 2 * (9 + 8 * ‖ρ‖) * ((r : ℝ) * (t : ℝ) ^ (-ρ.re)) := h3
      _ ≤ 2 * (9 + 8 * ‖ρ‖) * D := mul_le_mul_of_nonneg_left h4 hcoefnn
  -- `‖Zρ·Br‖ ≤ 2·Wρ·P·D`
  have hBr_bound : ‖Br‖ ≤ P * (r : ℝ) ^ (-ρ.re) := by
    rw [hBrdef, hPdef]
    have hconv : ∑ d ∈ Finset.Icc 1 r, (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)
        = ∑ d ∈ Finset.Icc 1 r, χ (d : ZMod q) * (d : ℂ) ^ (-ρ) := by
      refine Finset.sum_congr rfl (fun d _ => by rw [chiRe_ofReal χ hsq d])
    rw [hconv]
    exact partial_sum_at_zero_small χ hχ hq hzero hσ0 hhi.le hr1
  have hrb : (r : ℝ) ^ (-ρ.re) ≤ 2 * D := by
    have hb := sqrt_pow_bound (a := (-ρ.re)) (by linarith) (by linarith) (t := t) ht
    rw [← hrdef] at hb
    have hmono : (t : ℝ) ^ ((-ρ.re) / 2) ≤ (t : ℝ) ^ (1 / 2 - ρ.re) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast ht) (by linarith)
    calc (r : ℝ) ^ (-ρ.re) ≤ 2 * (t : ℝ) ^ ((-ρ.re) / 2) := hb
      _ ≤ 2 * (t : ℝ) ^ (1 / 2 - ρ.re) := by linarith [hmono]
      _ = 2 * D := by rw [hDdef]
  have hZρ : ‖Zρ‖ ≤ Wρ := by rw [hZρdef, hWρdef]; exact norm_zeta_rho_le hZ hlo hhi.le him hρ1
  have hZρBr : ‖Zρ * Br‖ ≤ 2 * Wρ * P * D := by
    rw [norm_mul]
    calc ‖Zρ‖ * ‖Br‖ ≤ Wρ * (P * (r : ℝ) ^ (-ρ.re)) :=
          mul_le_mul hZρ hBr_bound (norm_nonneg _) hWρnn
      _ ≤ Wρ * (P * (2 * D)) := by
          apply mul_le_mul_of_nonneg_left _ hWρnn
          exact mul_le_mul_of_nonneg_left hrb hPnn
      _ = 2 * Wρ * P * D := by ring
  -- FINAL combination
  rw [hLeg1eq, hclean]
  have hsplit : (t : ℂ) ^ (1 - ρ) / (1 - ρ) * Sr + (G + Zρ * Br)
        - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ)
      = ((t : ℂ) ^ (1 - ρ) / (1 - ρ) * Sr - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))
          + (G + Zρ * Br) := by ring
  rw [hsplit]
  calc ‖((t : ℂ) ^ (1 - ρ) / (1 - ρ) * Sr - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ)) + (G + Zρ * Br)‖
      ≤ ‖(t : ℂ) ^ (1 - ρ) / (1 - ρ) * Sr - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ)‖
          + ‖G + Zρ * Br‖ := norm_add_le _ _
    _ ≤ 12 * M / ‖1 - ρ‖ * D + (‖G‖ + ‖Zρ * Br‖) :=
        add_le_add hCM (norm_add_le _ _)
    _ ≤ 12 * M / ‖1 - ρ‖ * D + (2 * (9 + 8 * ‖ρ‖) * D + 2 * Wρ * P * D) :=
        add_le_add (le_refl _) (add_le_add hGbound hZρBr)
    _ = (12 * M / ‖1 - ρ‖ + 2 * (9 + 8 * ‖ρ‖) + 2 * Wρ * P) * D := by ring

/-! ## §5 — the per-`t` inner bound (R6-2@ρ, the analytic heart) -/

/-- **R6-2@ρ (`dhAbel_inner_rho`) — the per-`t` inner bound (the analytic heart).** For a primitive
real `χ` at a NON-REAL zero `ρ` (`1/2 ≤ Re ρ < 1`, `|Im ρ| ≤ 1`),
`‖A_ρ(t) − L(1,χ)·t^{1−ρ}/(1−ρ)‖ ≤ C_{w,ρ}·t^{1/2−Re ρ}`,
`A_ρ(t) = Σ_{n≤t} dhA(n)·n^{−ρ}`, `P = 3M(1+‖ρ‖/Re ρ)`, `M = √q(1+log q)`,
`C_{w,ρ} = 12M/‖1−ρ‖ + 2(9+8‖ρ‖) + 2(Z₀+1/‖1−ρ‖)P + 2P + 2P/(1−Re ρ)`. The symmetric-hyperbola
long leg (`dhAbel_leg1_rho`) carries the `L(1,χ)` residue; the two short legs and the corner are
zero-killed (`partial_sum_at_zero_small`). Complex analog of `dhAbel_inner_le`/`dhAbel_inner_abs_le`
at the complex zero — `‖·‖`-level throughout, no reality tricks (catch #119). -/
theorem dhAbel_inner_rho [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re < 1)
    (him : |ρ.im| ≤ 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {t : ℕ} (ht : 1 ≤ t) :
    ‖(∑ n ∈ Finset.Icc 1 t, (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ))
        - DirichletCharacter.LFunction χ 1 * (t : ℂ) ^ (1 - ρ) / (1 - ρ)‖
      ≤ (12 * (Real.sqrt q * (1 + Real.log q)) / ‖1 - ρ‖ + 2 * (9 + 8 * ‖ρ‖)
          + 2 * (Z₀ + 1 / ‖1 - ρ‖) * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re))
          + 2 * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re))
          + 2 * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re)) / (1 - ρ.re))
        * (t : ℝ) ^ (1 / 2 - ρ.re) := by
  set M : ℝ := Real.sqrt q * (1 + Real.log q) with hMdef
  set r : ℕ := Nat.sqrt t with hrdef
  set D : ℝ := (t : ℝ) ^ (1 / 2 - ρ.re) with hDdef
  set P : ℝ := 3 * M * (1 + ‖ρ‖ / ρ.re) with hPdef
  have hσ0 : 0 < ρ.re := by linarith
  have hu : 0 < 1 - ρ.re := by linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hDnn : 0 ≤ D := Real.rpow_nonneg ht0.le _
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    have h2 : 0 ≤ 1 + ‖ρ‖ / ρ.re := by
      have := div_nonneg (norm_nonneg ρ) hσ0.le; linarith
    exact mul_nonneg (mul_nonneg (by norm_num) hMnn) h2
  have hr1 : 1 ≤ r := by
    rw [hrdef]; calc 1 = Nat.sqrt 1 := Nat.sqrt_one.symm
      _ ≤ Nat.sqrt t := Nat.sqrt_le_sqrt ht
  have hrt : r ≤ t := by rw [hrdef]; exact Nat.sqrt_le_self t
  -- the uniform T1 kill: `‖Σ_{d≤m} χℝ(d)d^{−ρ}‖ ≤ P·m^{−σ}`
  have hBnorm : ∀ m : ℕ, 1 ≤ m →
      ‖∑ d ∈ Finset.Icc 1 m, (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)‖ ≤ P * (m : ℝ) ^ (-ρ.re) := by
    intro m hm
    have hconv : ∑ d ∈ Finset.Icc 1 m, (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)
        = ∑ d ∈ Finset.Icc 1 m, χ (d : ZMod q) * (d : ℂ) ^ (-ρ) :=
      Finset.sum_congr rfl (fun d _ => by rw [chiRe_ofReal χ hsq d])
    rw [hconv, hPdef]
    exact partial_sum_at_zero_small χ hχ hq hzero hσ0 hhi.le hm
  -- LEG 2 : `‖Σ_{e≤r} e^{−ρ}·B_ρ(⌊t/e⌋)‖ ≤ 2P·D`
  have hLeg2 : ‖∑ e ∈ Finset.Icc 1 r, (e : ℂ) ^ (-ρ)
        * ∑ d ∈ Finset.Icc 1 (t / e), (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)‖ ≤ 2 * P * D := by
    have hstep : ∀ e ∈ Finset.Icc 1 r,
        ‖(e : ℂ) ^ (-ρ) * ∑ d ∈ Finset.Icc 1 (t / e), (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)‖
          ≤ P * (2 * (t : ℝ) ^ (-ρ.re)) := by
      intro e he
      rw [Finset.mem_Icc] at he
      have het : e ≤ t := le_trans he.2 hrt
      have hte1 : 1 ≤ t / e := (Nat.one_le_div_iff (by omega)).mpr het
      rw [norm_mul, norm_natCast_cpow_neg hσ0 e]
      calc (e : ℝ) ^ (-ρ.re)
            * ‖∑ d ∈ Finset.Icc 1 (t / e), (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)‖
          ≤ (e : ℝ) ^ (-ρ.re) * (P * ((t / e : ℕ) : ℝ) ^ (-ρ.re)) :=
            mul_le_mul_of_nonneg_left (hBnorm (t / e) hte1) (Real.rpow_nonneg (by positivity) _)
        _ = P * ((e : ℝ) ^ (-ρ.re) * ((t / e : ℕ) : ℝ) ^ (-ρ.re)) := by ring
        _ ≤ P * (2 * (t : ℝ) ^ (-ρ.re)) :=
            mul_le_mul_of_nonneg_left
              (term_rpow_le (by linarith) (by linarith) he.1 het) hPnn
    calc ‖∑ e ∈ Finset.Icc 1 r, (e : ℂ) ^ (-ρ)
            * ∑ d ∈ Finset.Icc 1 (t / e), (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)‖
        ≤ ∑ e ∈ Finset.Icc 1 r, P * (2 * (t : ℝ) ^ (-ρ.re)) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hstep)
      _ = (r : ℝ) * (P * (2 * (t : ℝ) ^ (-ρ.re))) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      _ ≤ 2 * P * D := by
          have hrt' : (r : ℝ) * (t : ℝ) ^ (-ρ.re) ≤ D := by
            rw [hDdef, hrdef]; exact natSqrt_mul_rpow_le ht
          have heq2 : (r : ℝ) * (P * (2 * (t : ℝ) ^ (-ρ.re)))
              = 2 * P * ((r : ℝ) * (t : ℝ) ^ (-ρ.re)) := by ring
          rw [heq2]
          exact mul_le_mul_of_nonneg_left hrt' (mul_nonneg (by norm_num) hPnn)
  -- CORNER : `‖B_ρ(r)·T_ρ(r)‖ ≤ 2P/(1−σ)·D`
  have hTr : ‖∑ e ∈ Finset.Icc 1 r, (e : ℂ) ^ (-ρ)‖ ≤ (r : ℝ) ^ (1 - ρ.re) / (1 - ρ.re) := by
    refine (norm_sum_le _ _).trans ?_
    have heq : ∑ e ∈ Finset.Icc 1 r, ‖(e : ℂ) ^ (-ρ)‖ = ∑ e ∈ Finset.Icc 1 r, (e : ℝ) ^ (-ρ.re) :=
      Finset.sum_congr rfl (fun e he => by
        rw [Finset.mem_Icc] at he; exact norm_natCast_cpow_neg hσ0 e)
    rw [heq]; exact sum_rpow_neg_le (by linarith) hhi r
  have hCorner : ‖(∑ d ∈ Finset.Icc 1 r, (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ))
        * ∑ e ∈ Finset.Icc 1 r, (e : ℂ) ^ (-ρ)‖ ≤ 2 * P / (1 - ρ.re) * D := by
    rw [norm_mul]
    have hr1m2 : (r : ℝ) ^ (-ρ.re) * (r : ℝ) ^ (1 - ρ.re) ≤ 2 * D := by
      have hb := sqrt_pow_bound (a := 1 - 2 * ρ.re) (by linarith) (by linarith) (t := t) ht
      rw [← hrdef] at hb
      have hcomb : (r : ℝ) ^ (-ρ.re) * (r : ℝ) ^ (1 - ρ.re) = (r : ℝ) ^ (1 - 2 * ρ.re) := by
        rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < r))]; congr 1; ring
      rw [show (1 - 2 * ρ.re) / 2 = 1 / 2 - ρ.re by ring] at hb
      rw [hcomb, hDdef]; exact hb
    calc ‖∑ d ∈ Finset.Icc 1 r, (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)‖
            * ‖∑ e ∈ Finset.Icc 1 r, (e : ℂ) ^ (-ρ)‖
        ≤ (P * (r : ℝ) ^ (-ρ.re)) * ((r : ℝ) ^ (1 - ρ.re) / (1 - ρ.re)) :=
          mul_le_mul (hBnorm r hr1) hTr (norm_nonneg _) (by positivity)
      _ = P / (1 - ρ.re) * ((r : ℝ) ^ (-ρ.re) * (r : ℝ) ^ (1 - ρ.re)) := by ring
      _ ≤ P / (1 - ρ.re) * (2 * D) := by
          apply mul_le_mul_of_nonneg_left hr1m2 (by positivity)
      _ = 2 * P / (1 - ρ.re) * D := by ring
  -- LEG 1 : the main-term residue leg
  have hLeg1 := dhAbel_leg1_rho χ hχ hsq hq hzero hlo hhi him hZ ht
  rw [← hMdef, ← hrdef, ← hDdef, ← hPdef] at hLeg1
  -- assemble
  rw [dhAbel_hyperbola_rho χ t, ← hrdef]
  set Leg1 : ℂ := ∑ d ∈ Finset.Icc 1 r, ((chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ))
      * ∑ e ∈ Finset.Icc 1 (t / d), (e : ℂ) ^ (-ρ) with hLeg1def
  set Leg2 : ℂ := ∑ e ∈ Finset.Icc 1 r, (e : ℂ) ^ (-ρ)
      * ∑ d ∈ Finset.Icc 1 (t / e), (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ) with hLeg2def
  set Cor : ℂ := (∑ d ∈ Finset.Icc 1 r, (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ))
      * ∑ e ∈ Finset.Icc 1 r, (e : ℂ) ^ (-ρ) with hCordef
  set main₀ : ℂ := DirichletCharacter.LFunction χ 1 * (t : ℂ) ^ (1 - ρ) / (1 - ρ) with hmain₀
  have hsplit : Leg1 + Leg2 - Cor - main₀ = (Leg1 - main₀) + Leg2 - Cor := by ring
  rw [hsplit]
  calc ‖(Leg1 - main₀) + Leg2 - Cor‖
      ≤ ‖(Leg1 - main₀) + Leg2‖ + ‖Cor‖ := norm_sub_le _ _
    _ ≤ (‖Leg1 - main₀‖ + ‖Leg2‖) + ‖Cor‖ := add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ ((12 * M / ‖1 - ρ‖ + 2 * (9 + 8 * ‖ρ‖) + 2 * (Z₀ + 1 / ‖1 - ρ‖) * P) * D
            + 2 * P * D) + 2 * P / (1 - ρ.re) * D :=
          add_le_add (add_le_add hLeg1 hLeg2) hCorner
    _ = (12 * M / ‖1 - ρ‖ + 2 * (9 + 8 * ‖ρ‖) + 2 * (Z₀ + 1 / ‖1 - ρ‖) * P
          + 2 * P + 2 * P / (1 - ρ.re)) * D := by ring

end Salt.SW

end
