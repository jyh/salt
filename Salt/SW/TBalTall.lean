/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.TauExt

/-!
# ⟦TAU-EXT-2⟧ — **`dh_repulsion_tall`: the Deuring–Heilbronn contract off the unit box**

The residual named and priced by ⟦TAU-EXT⟧ (`docs/exploration/tau-ext-scope.md`): the landed
`dh_repulsion_ordered` (`Salt/SW/TBalR8.lean`) hypothesizes `|Im ρ| ≤ 1`, while N2's exit lemma
`efZeroSumM_spend_at_efHeight` needs the contract on the campaign box `|Im ρ| ≤ efHeight q + 2`.
TAU-EXT's scope read said the restriction is PACKAGING, not analysis. This file cashes that read:
it re-threads the ρ-side chain with the height binder generalized, and lands the contract with **no
height binder at all** — `dh_repulsion_tall` holds at every zero off the real axis in the window,
at the zero's own base `Q = q(|Im ρ| + 2)`.

Everything here is ADDITIVE: the ten original statements are untouched; each twin carries the
`_tall` suffix.

## The three design moves (beyond the mechanical re-thread)

1. **`Z₀` splits in two.** The chain feeds `hZ` — the `zetaHol` packaging — at exactly two kinds of
   point: the complex zero `ρ` (the ρ-side: `norm_zeta_rho_le`, `dhAbel_leg1_rho`,
   `dh_extraction_upper_rho`) and the REAL point `β₀` (the β₀-side: `dh_extraction_upper_W`,
   `H_lower`). Those two consumers do **not** have to share a constant. `dh_master_ray_tall`
   therefore takes TWO: `Zρ` at the tall gate `|Im s| ≤ H`, and `Zβ` at the unit gate. The β₀ side
   keeps the numeral `Zβ = 5` (`zetaHol_bound_five`), so **every `Z₀`-carrying `c`-threshold on the
   β₀ side stays a numeral** — and `row_Eβ_cap`, `tbal_hcov`, `tbal_hscale`, `tbal_hguard` need no
   twins at all. Only the ρ-side constant grows with the height.
2. **The ρ-side growth is charged to `Q`.** With the gate at `H = |Im ρ|`, `zetaHol_bound_tall`
   gives `Zρ = 3 + 2|Im ρ| ≤ 2Q`, and `‖ρ‖ ≤ 1 + |Im ρ| ≤ Q`, both because `Q = q(|Im ρ| + 2)` is
   the contract's own base and `q ≥ 2`. `C2Rho_le_tall` charges both to the `Q`-exponent:
   `Q^{1/2} ⇝ Q^{5/2}`, constant `(564 + 72Z₀) ⇝ 570`. `row_Eρ_cap_tall` then absorbs the two extra
   `Q`-powers into the exponent-balance slack (`b = 680` against `α = 5/2 + 12 + 104(1/2 − σ) < 0`
   on the window `σ ≥ 16/17`) — the balance never tightens, and the `Eρ` threshold on `c` becomes
   `Z₀`-free.
3. **The height binder disappears.** Because the tall gate can be taken AT the zero
   (`H = |Im ρ|`, `him = le_rfl`), the final contract carries no `|Im ρ| ≤ T` hypothesis; the
   box-shaped form at any `T` is the same statement with the binder ignored.

`b = 680`, `k = 14` are UNCHANGED. `c` moves: its `Z₀`-graded arms `(1/KEβ)⁸`, `(c₀/KEρ)⁸`,
`1/(3A₀)` become the numerals below at `Zβ = 5` / the re-priced `KEρ = 16·570·248⁹`, and the arm
`1/(Z₀+1)` is retired (it existed only to buy `Z₀·u ≤ 1` for `tbal_hcov`, which at `Zβ = 5` is
bought by `c ≤ 1/576`).

## Main results

* `zeta_partial_em_free` — `zeta_partial_em` with its (unused) height slot removed.
* the ρ-chain twins: `norm_zeta_rho_le_tall`, `emrho_perterm_tall` (height-free),
  `dhAbel_leg1_rho_tall`, `dhAbel_inner_rho_tall`, `unmoll_extraction_rho_tall`,
  `dh_extraction_per_m_rho_tall`, `dh_extraction_upper_rho_tall`, `dh_master_ray_tall`.
* `C2Rho_le_tall`, `row_Eρ_cap_tall` — the two re-priced estimates.
* `dh_repulsion_tall` — **the contract, height-free.**
* `boxZeros_re_le_at_efHeight` — the plug: `boxZeros_re_le_of_repulsion` fired at
  `T = efHeight q + 2`, i.e. the `β`-supplier at the campaign box. The artillery is COMPLETE for
  N4; the three named side hypotheses (`hord`/`hreal`/`hceil`, plus the regime statement `hN`)
  are carried, exactly as in `boxZeros_re_le_unit_box`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open Complex
open Finset

noncomputable section

namespace Salt.SW

variable {q : ℕ}

/-! ## §0 — the height-free Euler–Maclaurin partial -/

/-- **`zeta_partial_em` without the height slot.**  `zeta_partial_em` (`ZetaEM.lean`) carries a
binder `|Im s| ≤ 1` that its proof never reads (it is literally named `_him` there): the estimate
factors through the height-free `norm_zeta_sub_approx_le_strip`. This is the same statement with
the slot removed — the first stone of the tall re-thread. -/
lemma zeta_partial_em_free {s : ℂ} (hσ : 1 / 2 ≤ s.re) (hσ1 : s.re < 1)
    {y : ℕ} (hy : 1 ≤ y) :
    ‖(∑ a ∈ Finset.Icc 1 y, (a : ℂ) ^ (-s))
        - ((y : ℂ) ^ (1 - s) / (1 - s) + riemannZeta s)‖
      ≤ 8 * (1 + ‖s‖) * (y : ℝ) ^ (-s.re) := by
  have hσ0 : 0 < s.re := by linarith
  have hneg : (∑ a ∈ Finset.Icc 1 y, (a : ℂ) ^ (-s))
        - ((y : ℂ) ^ (1 - s) / (1 - s) + riemannZeta s)
      = -(riemannZeta s - (∑ a ∈ Finset.Icc 1 y, (a : ℂ) ^ (-s))
          - (y : ℂ) ^ (1 - s) / (s - 1)) := by
    rw [show (s - 1 : ℂ) = -(1 - s) from by ring, div_neg]; ring
  rw [hneg, norm_neg]
  refine le_trans (norm_zeta_sub_approx_le_strip hσ0 hσ1 hy) ?_
  have hyp : (0 : ℝ) ≤ (y : ℝ) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
  have hσinv : ‖s‖ / s.re ≤ 8 * (1 + ‖s‖) := by
    rw [div_le_iff₀ hσ0]
    nlinarith [norm_nonneg s, hσ,
      mul_nonneg (add_nonneg zero_le_one (norm_nonneg s)) (sub_nonneg.mpr hσ)]
  calc ‖s‖ * (y : ℝ) ^ (-s.re) / s.re
      = (‖s‖ / s.re) * (y : ℝ) ^ (-s.re) := by ring
    _ ≤ (8 * (1 + ‖s‖)) * (y : ℝ) ^ (-s.re) := mul_le_mul_of_nonneg_right hσinv hyp
    _ = 8 * (1 + ‖s‖) * (y : ℝ) ^ (-s.re) := by ring

/-! ## §1 — the ρ-chain twins (the height binder `≤ 1` generalized to `≤ H`) -/

/-- **`‖ζ(ρ)‖` bound.** For `1/2 ≤ Re ρ ≤ 1`, `|Im ρ| ≤ 1`, `ρ ≠ 1`,
`‖ζ(ρ)‖ ≤ Z₀ + 1/‖1−ρ‖` where `Z₀` is the `zetaHol_bound` compactness constant. Complex analog
of `abs_zeta_re_le`: `ζ(ρ) = 1/(ρ−1) + zetaHol ρ`, `‖1/(ρ−1)‖ = 1/‖1−ρ‖`, `‖zetaHol ρ‖ ≤ Z₀`. -/
theorem norm_zeta_rho_le_tall {Z₀ : ℝ}
    (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ H → ‖zetaHol s‖ ≤ Z₀)
    {ρ : ℂ} (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re ≤ 1) (him : |ρ.im| ≤ H) (hne : ρ ≠ 1) :
    ‖riemannZeta ρ‖ ≤ Z₀ + 1 / ‖1 - ρ‖ := by
  have hsplit : riemannZeta ρ = 1 / (ρ - 1) + zetaHol ρ := riemannZeta_eq_add_zetaHol hne
  have hZb : ‖zetaHol ρ‖ ≤ Z₀ := hZ ρ hlo hhi him
  have hpole : ‖(1 : ℂ) / (ρ - 1)‖ = 1 / ‖1 - ρ‖ := by
    rw [norm_div, norm_one, ← norm_neg (ρ - 1), neg_sub]
  calc ‖riemannZeta ρ‖ = ‖1 / (ρ - 1) + zetaHol ρ‖ := by rw [hsplit]
    _ ≤ ‖(1 : ℂ) / (ρ - 1)‖ + ‖zetaHol ρ‖ := norm_add_le _ _
    _ ≤ 1 / ‖1 - ρ‖ + Z₀ := by rw [hpole]; linarith
    _ = Z₀ + 1 / ‖1 - ρ‖ := by ring

/-- **The per-`d` EM split.** For `1/2 ≤ Re ρ < 1` and `1 ≤ d ≤ t` (NO height gate),
`‖T_ρ(⌊t/d⌋) − (t/d)^{1−ρ}/(1−ρ) − ζ(ρ)‖ ≤ (9 + 8‖ρ‖)·⌊t/d⌋^{−Re ρ}`,
`T_ρ(m) = Σ_{e≤m} e^{−ρ}`, the real ratio `t/d` in the main. The `zeta_partial_em` pole form at
`s = ρ`, `y = ⌊t/d⌋`, plus the floor correction `⌊t/d⌋ → t/d` (`norm_cpow_pos_floor_sub_le`). -/
theorem emrho_perterm_tall {ρ : ℂ} (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re < 1)
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
  have hem := zeta_partial_em_free (s := ρ) hlo hhi hdt1
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

/-- **The long-leg extraction (the `L(1,χ)` residue).** For a primitive real `χ` at a NON-REAL
zero `ρ` (`1/2 ≤ Re ρ < 1`, `|Im ρ| ≤ 1`),
`‖Leg₁ − L(1,χ)·t^{1−ρ}/(1−ρ)‖ ≤ (12M/‖1−ρ‖ + 2(9+8‖ρ‖) + 2(Z₀+1/‖1−ρ‖)·P)·t^{1/2−Re ρ}`,
`Leg₁ = Σ_{d≤√t} χ_ℝ(d)d^{−ρ}·T_ρ(⌊t/d⌋)`, `P = 3M(1+‖ρ‖/Re ρ)`. The a-sum pole
(`emrho_perterm_tall`) extracts `L(1,χ)` from `Σ_{d≤√t} χ(d)/d` (strip@1); the `ζ(ρ)` stream is
killed
by `partial_sum_at_zero_small`. Complex analog of `dhAbel_leg1_le`. -/
theorem dhAbel_leg1_rho_tall [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re < 1)
    {H : ℝ} (him : |ρ.im| ≤ H)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ H → ‖zetaHol s‖ ≤ Z₀)
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
      apply mul_le_mul _ (emrho_perterm_tall hlo hhi hd.1 (le_trans hd.2 hrt))
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
  have hZρ : ‖Zρ‖ ≤ Wρ := by rw [hZρdef, hWρdef]; exact norm_zeta_rho_le_tall hZ hlo hhi.le him hρ1
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

/-- **R6-2@ρ (`dhAbel_inner_rho_tall`) — the per-`t` inner bound (the analytic heart).** For a
primitive real `χ` at a NON-REAL zero `ρ` (`1/2 ≤ Re ρ < 1`, `|Im ρ| ≤ 1`),
`‖A_ρ(t) − L(1,χ)·t^{1−ρ}/(1−ρ)‖ ≤ C_{w,ρ}·t^{1/2−Re ρ}`,
`A_ρ(t) = Σ_{n≤t} dhA(n)·n^{−ρ}`, `P = 3M(1+‖ρ‖/Re ρ)`, `M = √q(1+log q)`,
`C_{w,ρ} = 12M/‖1−ρ‖ + 2(9+8‖ρ‖) + 2(Z₀+1/‖1−ρ‖)P + 2P + 2P/(1−Re ρ)`. The symmetric-hyperbola
long leg (`dhAbel_leg1_rho_tall`) carries the `L(1,χ)` residue; the two short legs and the corner
are zero-killed (`partial_sum_at_zero_small`). Complex analog of
`dhAbel_inner_le`/`dhAbel_inner_abs_le` at the complex zero — `‖·‖`-level throughout, no reality
tricks (catch #119). -/
theorem dhAbel_inner_rho_tall [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re < 1)
    {H : ℝ} (him : |ρ.im| ≤ H)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ H → ‖zetaHol s‖ ≤ Z₀)
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
  have hLeg1 := dhAbel_leg1_rho_tall χ hχ hsq hq hzero hlo hhi him hZ ht
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

set_option maxHeartbeats 1600000 in
-- Many error/main legs + field_simp/ring over the (1−ρ)(2−ρ) denominators exceed the default.
/-- **R6-3@ρ (`unmoll_extraction_rho_tall`) — the complex-scale two-sided extraction.** For a
primitive real `χ` at a NON-REAL zero `ρ` (`1/2 ≤ Re ρ < 1`, `|Im ρ| ≤ 1`) and real `x ≥ 2`,
`‖D₀^ρ(x) − L(1,χ)·x^{1−ρ}/((1−ρ)(2−ρ))‖ ≤ C₂ρ·x^{1/2−Re ρ}`. The complex analog of
`unmoll_extraction_abs_real`: the complex kernel-Abel (`kernel_abel_sum_rho`) reduces `D₀^ρ` to
`(1/x)[(x−T)A_ρ(T)+Σ_{t<T}A_ρ(t)]`; the per-`t` heart (`dhAbel_inner_rho_tall`) gives the `3Cwρ`
error legs and the complex power-sum sandwich (`sum_cpow_sandwich_rho`, with `‖L(1,χ)‖ ≤ 18M`)
gives the main leg. -/
theorem unmoll_extraction_rho_tall [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re < 1)
    {H : ℝ} (him : |ρ.im| ≤ H)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ H → ‖zetaHol s‖ ≤ Z₀)
    {x : ℝ} (hx : 2 ≤ x) :
    ‖dhD0rho χ ρ x
        - DirichletCharacter.LFunction χ 1 * (x : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))‖
      ≤ C2Rho q Z₀ ρ * x ^ (1 / 2 - ρ.re) := by
  set M : ℝ := Real.sqrt q * (1 + Real.log q) with hMdef
  set L₁ : ℂ := DirichletCharacter.LFunction χ 1 with hL1def
  set Cwρ : ℝ := CwRho q Z₀ ρ with hCwρdef
  set T : ℕ := ⌊x⌋₊ with hTdef
  set main : ℂ := L₁ * (x : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) with hmaindef
  have hσ0 : 0 < ρ.re := by linarith
  have hu : 0 < 1 - ρ.re := by linarith
  have hu2 : 0 < 2 - ρ.re := by linarith
  have hne : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  haveI : Fact (1 < q) := ⟨by omega⟩
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hhi; simp at hhi
  have hsne : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (fun h => hρ1 h.symm)
  have h2ρne : (2 - ρ) ≠ 0 := by
    intro h; have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, Complex.re_ofNat] at this; linarith
  have hnpos : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hsne
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxC0 : (x : ℂ) ≠ 0 := by simp only [ne_eq, Complex.ofReal_eq_zero]; exact hx0.ne'
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hxc : (0 : ℝ) ≤ x ^ (3 / 2 - ρ.re) := Real.rpow_nonneg hx0.le _
  have hT1 : 1 ≤ T := by rw [hTdef, Nat.le_floor_iff hx0.le]; exact_mod_cast hx1
  have hT2 : 2 ≤ T := by rw [hTdef, Nat.le_floor_iff hx0.le]; exact_mod_cast hx
  have hTx : (T : ℝ) ≤ x := by rw [hTdef]; exact Nat.floor_le hx0.le
  have hxT : x < (T : ℝ) + 1 := by rw [hTdef]; exact Nat.lt_floor_add_one x
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT1
  -- ‖L₁‖ ≤ 18M
  have hL1_le : ‖L₁‖ ≤ 18 * M := by
    have hnorm := LFunction_apply_one_norm_le χ hχ hq
    rw [← hL1def] at hnorm
    have hlogq0 : (0 : ℝ) ≤ 1 + Real.log q := by linarith
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1.4 : ℝ) = Real.sqrt (1.4 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsq14 : (1.4 : ℝ) ≤ Real.sqrt q := le_trans hs2 (Real.sqrt_le_sqrt hq2)
    have h5e : 5 * Real.exp 1 ≤ 18 * Real.sqrt q := by nlinarith [Real.exp_one_lt_d9, hsq14]
    rw [hMdef]
    nlinarith [hnorm, mul_le_mul_of_nonneg_right h5e hlogq0]
  -- R6-1@ρ : the complex kernel-Abel identity
  have hAbel : dhD0rho χ ρ x = (1 / (x : ℂ)) * (((x : ℂ) - (T : ℂ))
        * (∑ s ∈ Finset.Icc 1 T, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
        + ∑ t ∈ Finset.Icc 1 (T - 1), ∑ s ∈ Finset.Icc 1 t,
            (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ)) := by
    rw [dhD0rho, ← hTdef]
    exact kernel_abel_sum_rho (fun s => (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ)) hx1
  set ST : ℂ := ∑ s ∈ Finset.Icc 1 T, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ) with hSTdef
  set SP : ℂ := ∑ t ∈ Finset.Icc 1 (T - 1), (t : ℂ) ^ (1 - ρ) with hSPdef
  set S : ℂ := ((x : ℂ) - (T : ℂ)) * (T : ℂ) ^ (1 - ρ) + SP with hSdef
  set R : ℂ := ((x : ℂ) - (T : ℂ)) * ST
      + ∑ t ∈ Finset.Icc 1 (T - 1), ∑ s ∈ Finset.Icc 1 t,
          (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ) with hRdef
  -- per-`t` heart bound
  have hR2 : ∀ t : ℕ, 1 ≤ t →
      ‖(∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ)) - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ)‖
        ≤ Cwρ * (t : ℝ) ^ (1 / 2 - ρ.re) := by
    intro t ht
    have h := dhAbel_inner_rho_tall χ hχ hsq hq hzero hlo hhi him hZ ht
    rw [← hL1def] at h
    rw [hCwρdef]; simp only [CwRho]
    exact h
  -- the exact main/error split of `R − x·main`
  have hxx : (x : ℂ) * (x : ℂ) ^ (1 - ρ) = (x : ℂ) ^ (2 - ρ) := by
    nth_rewrite 1 [← Complex.cpow_one (x : ℂ)]
    rw [← Complex.cpow_add _ _ hxC0]; congr 1; ring
  have hxmain : (x : ℂ) * main = L₁ * (x : ℂ) ^ (2 - ρ) / ((1 - ρ) * (2 - ρ)) := by
    rw [hmaindef, show (x : ℂ) * (L₁ * (x : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)))
      = L₁ * ((x : ℂ) * (x : ℂ) ^ (1 - ρ)) / ((1 - ρ) * (2 - ρ)) by ring, hxx]
  have hRsplit : R - (x : ℂ) * main
      = (L₁ / (1 - ρ)) * (S - (x : ℂ) ^ (2 - ρ) / (2 - ρ))
        + (((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))
           + ∑ t ∈ Finset.Icc 1 (T - 1),
               ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
                 - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))) := by
    have hEsum : (∑ t ∈ Finset.Icc 1 (T - 1),
          ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
            - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ)))
        = (∑ t ∈ Finset.Icc 1 (T - 1), ∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
          - (L₁ / (1 - ρ)) * SP := by
      rw [Finset.sum_sub_distrib]; congr 1
      rw [hSPdef, Finset.mul_sum]; exact Finset.sum_congr rfl (fun t _ => by ring)
    rw [hRdef, hxmain, hEsum, hSdef]; field_simp; ring
  -- bound the main defect via the sandwich
  have hSbound := sum_cpow_sandwich_rho hσ0 hhi hx hT2 hTx hxT
  rw [← hSPdef] at hSbound
  have hSbound' : ‖S - (x : ℂ) ^ (2 - ρ) / (2 - ρ)‖
      ≤ (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (1 - ρ.re) := by
    rw [hSdef]; exact hSbound
  have hBmain : ‖(L₁ / (1 - ρ)) * (S - (x : ℂ) ^ (2 - ρ) / (2 - ρ))‖
      ≤ (‖L₁‖ / ‖1 - ρ‖) * ((5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (1 - ρ.re)) := by
    rw [norm_mul, norm_div]
    exact mul_le_mul_of_nonneg_left hSbound' (by positivity)
  -- bound the error legs `≤ 3·Cwρ·x^{3/2−ρ.re}`
  have hCwρnn : 0 ≤ Cwρ := by
    have := hR2 1 (le_refl 1)
    exact le_trans (norm_nonneg _) (le_trans this (le_of_eq (by
      rw [Nat.cast_one, Real.one_rpow, mul_one])))
  have hBerr : ‖((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))
        + ∑ t ∈ Finset.Icc 1 (T - 1),
            ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
              - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))‖
      ≤ 3 * Cwρ * x ^ (3 / 2 - ρ.re) := by
    have hxTnorm : ‖(x : ℂ) - (T : ℂ)‖ ≤ 1 := by
      rw [show (x : ℂ) - (T : ℂ) = (((x - (T : ℝ)) : ℝ) : ℂ) from by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
    have hterm1 : ‖((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))‖
        ≤ Cwρ * x ^ (3 / 2 - ρ.re) := by
      rw [norm_mul]
      have hTle1 : (T : ℝ) ^ (1 / 2 - ρ.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT1) (by linarith)
      have h1x : (1 : ℝ) ≤ x ^ (3 / 2 - ρ.re) := Real.one_le_rpow hx1 (by linarith)
      calc ‖(x : ℂ) - (T : ℂ)‖ * ‖ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ)‖
          ≤ 1 * (Cwρ * (T : ℝ) ^ (1 / 2 - ρ.re)) :=
            mul_le_mul hxTnorm (hR2 T hT1) (norm_nonneg _) (by norm_num)
        _ ≤ Cwρ * x ^ (3 / 2 - ρ.re) := by
            rw [one_mul]
            calc Cwρ * (T : ℝ) ^ (1 / 2 - ρ.re) ≤ Cwρ * 1 :=
                  mul_le_mul_of_nonneg_left hTle1 hCwρnn
              _ ≤ Cwρ * x ^ (3 / 2 - ρ.re) := by rw [mul_one]; nlinarith [hCwρnn, h1x]
    have hterm2 : ‖∑ t ∈ Finset.Icc 1 (T - 1),
          ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
            - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))‖ ≤ 2 * Cwρ * x ^ (3 / 2 - ρ.re) := by
      calc ‖∑ t ∈ Finset.Icc 1 (T - 1),
              ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
                - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))‖
          ≤ ∑ t ∈ Finset.Icc 1 (T - 1), Cwρ * (t : ℝ) ^ (1 / 2 - ρ.re) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun t ht => ?_))
            rw [Finset.mem_Icc] at ht; exact hR2 t (by omega)
        _ = Cwρ * ∑ t ∈ Finset.Icc 1 (T - 1), (t : ℝ) ^ (1 / 2 - ρ.re) := by rw [Finset.mul_sum]
        _ ≤ Cwρ * (2 * x ^ (3 / 2 - ρ.re)) := by
            apply mul_le_mul_of_nonneg_left _ hCwρnn
            have h := sum_rpow_neg_le (β := ρ.re - 1 / 2) (by linarith)
              (by linarith) (T - 1)
            rw [show -(ρ.re - 1 / 2) = 1 / 2 - ρ.re by ring,
              show 1 - (ρ.re - 1 / 2) = 3 / 2 - ρ.re by ring] at h
            have hym1 : ((T - 1 : ℕ) : ℝ) ≤ x := le_trans (by
              rw [Nat.cast_sub hT1]; push_cast; linarith) hTx
            have hbase : ((T - 1 : ℕ) : ℝ) ^ (3 / 2 - ρ.re) ≤ x ^ (3 / 2 - ρ.re) :=
              Real.rpow_le_rpow (by positivity) hym1 (by linarith)
            have h32 : (0 : ℝ) < 3 / 2 - ρ.re := by linarith
            calc ∑ t ∈ Finset.Icc 1 (T - 1), (t : ℝ) ^ (1 / 2 - ρ.re)
                ≤ ((T - 1 : ℕ) : ℝ) ^ (3 / 2 - ρ.re) / (3 / 2 - ρ.re) := h
              _ ≤ x ^ (3 / 2 - ρ.re) / (3 / 2 - ρ.re) := (div_le_div_iff_of_pos_right h32).mpr hbase
              _ ≤ 2 * x ^ (3 / 2 - ρ.re) := by rw [div_le_iff₀ h32]; nlinarith [hxc]
        _ = 2 * Cwρ * x ^ (3 / 2 - ρ.re) := by ring
    calc ‖((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))
            + ∑ t ∈ Finset.Icc 1 (T - 1),
                ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
                  - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))‖
        ≤ ‖((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))‖
          + ‖∑ t ∈ Finset.Icc 1 (T - 1),
              ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
                - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))‖ := norm_add_le _ _
      _ ≤ Cwρ * x ^ (3 / 2 - ρ.re) + 2 * Cwρ * x ^ (3 / 2 - ρ.re) := add_le_add hterm1 hterm2
      _ = 3 * Cwρ * x ^ (3 / 2 - ρ.re) := by ring
  -- combine : ‖R − x·main‖ ≤ C₂ρ·x^{3/2−ρ.re}
  have hBmain' : ‖(L₁ / (1 - ρ)) * (S - (x : ℂ) ^ (2 - ρ) / (2 - ρ))‖
      ≤ 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (3 / 2 - ρ.re) := by
    have hx13 : x ^ (1 - ρ.re) ≤ x ^ (3 / 2 - ρ.re) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hKnn : (0 : ℝ) ≤ 5 + 4 * ‖1 - ρ‖ / (1 - ρ.re) := by
      have : (0:ℝ) ≤ 4 * ‖1 - ρ‖ / (1 - ρ.re) := by positivity
      linarith
    calc ‖(L₁ / (1 - ρ)) * (S - (x : ℂ) ^ (2 - ρ) / (2 - ρ))‖
        ≤ (‖L₁‖ / ‖1 - ρ‖) * ((5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (1 - ρ.re)) := hBmain
      _ ≤ (18 * M / ‖1 - ρ‖) * ((5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (3 / 2 - ρ.re)) := by
          apply mul_le_mul
          · exact (div_le_div_iff_of_pos_right hnpos).mpr hL1_le
          · exact mul_le_mul_of_nonneg_left hx13 hKnn
          · positivity
          · positivity
      _ = 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (3 / 2 - ρ.re) := by ring
  have hRbound : ‖R - (x : ℂ) * main‖ ≤ C2Rho q Z₀ ρ * x ^ (3 / 2 - ρ.re) := by
    rw [hRsplit]
    have hcomb : C2Rho q Z₀ ρ * x ^ (3 / 2 - ρ.re)
        = 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (3 / 2 - ρ.re)
          + 3 * Cwρ * x ^ (3 / 2 - ρ.re) := by
      rw [C2Rho, ← hMdef, ← hCwρdef]; ring
    rw [hcomb]
    calc ‖(L₁ / (1 - ρ)) * (S - (x : ℂ) ^ (2 - ρ) / (2 - ρ))
            + (((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))
               + ∑ t ∈ Finset.Icc 1 (T - 1),
                   ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
                     - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ)))‖
        ≤ ‖(L₁ / (1 - ρ)) * (S - (x : ℂ) ^ (2 - ρ) / (2 - ρ))‖
          + ‖((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))
             + ∑ t ∈ Finset.Icc 1 (T - 1),
                 ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
                   - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))‖ := norm_add_le _ _
      _ ≤ 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (3 / 2 - ρ.re)
            + 3 * Cwρ * x ^ (3 / 2 - ρ.re) := add_le_add hBmain' hBerr
  -- divide by x
  have heq : (1 / (x : ℂ)) * R - main = (R - (x : ℂ) * main) / (x : ℂ) := by field_simp
  have hfinal : ‖dhD0rho χ ρ x - main‖ = ‖R - (x : ℂ) * main‖ / x := by
    rw [hAbel, heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  rw [hfinal, div_le_iff₀ hx0]
  have hxpow : x ^ (1 / 2 - ρ.re) * x = x ^ (3 / 2 - ρ.re) := by
    nth_rewrite 2 [← Real.rpow_one x]; rw [← Real.rpow_add hx0]; congr 1; ring
  calc ‖R - (x : ℂ) * main‖ ≤ C2Rho q Z₀ ρ * x ^ (3 / 2 - ρ.re) := hRbound
    _ = C2Rho q Z₀ ρ * x ^ (1 / 2 - ρ.re) * x := by rw [← hxpow]; ring

section Compose

open ArithmeticFunction

/-! ### The ℂ reindex/regroup primitives of `Salt/SW/TBalCompose.lean`

Verbatim `private` copies (no statement or proof change, and height-free): the compose-side twins
below call them, and the originals are `private` to their own module. -/

/-! ## §1 — the ℂ reindex primitives (ℂ re-runs of the ℝ-weight infra) -/

/-- ℂ re-run of `sum_dvd_reindex` (pure reindex bijection `d = k·e`). -/
private lemma sum_dvd_reindex_C {k N : ℕ} (hk : 1 ≤ k) (F : ℕ → ℂ) :
    ∑ d ∈ (Finset.Icc 1 N).filter (fun d => k ∣ d), F d
      = ∑ e ∈ Finset.Icc 1 (N / k), F (k * e) := by
  have himg : (Finset.Icc 1 N).filter (fun d => k ∣ d)
      = (Finset.Icc 1 (N / k)).image (fun e => k * e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hd1, hdN⟩, hkd⟩
      obtain ⟨e, rfl⟩ := hkd
      refine ⟨e, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos e with rfl | he
        · simp at hd1
        · exact he
      · exact (Nat.le_div_iff_mul_le hk).mpr (by rw [mul_comm]; exact hdN)
    · rintro ⟨e, ⟨he1, heN⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hk he1, ?_⟩, Dvd.intro e rfl⟩
      rw [mul_comm]; exact (Nat.le_div_iff_mul_le hk).mp heN
  rw [himg, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hk hxy

/-- ℂ re-run of `sum_divisors_moebius_real` (`Σ_{k∣m} μ(k) = [m=1]`). -/
private lemma sum_divisors_moebius_C (m : ℕ) :
    ∑ k ∈ m.divisors, (moebius k : ℂ) = if m = 1 then (1 : ℂ) else 0 := by
  have hint : ∑ k ∈ m.divisors, (moebius k : ℤ) = if m = 1 then (1 : ℤ) else 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
        ArithmeticFunction.one_apply]
  have hcast : ∑ k ∈ m.divisors, (moebius k : ℂ)
      = ((∑ k ∈ m.divisors, (moebius k : ℤ) : ℤ) : ℂ) := by push_cast; rfl
  rw [hcast, hint]; split_ifs <;> norm_num

/-- ℂ re-run of `sum_coprime_eq_moebius_multiples`. -/
private lemma sum_coprime_eq_moebius_multiples_C (g N : ℕ) (hg : 1 ≤ g) (F : ℕ → ℂ) :
    ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d g), F d
      = ∑ k ∈ g.divisors, (moebius k : ℂ) * ∑ e ∈ Finset.Icc 1 (N / k), F (k * e) := by
  have hg0 : g ≠ 0 := by omega
  have hset : ∀ d : ℕ, g.divisors.filter (fun k => k ∣ d) = (Nat.gcd g d).divisors := by
    intro d
    ext k
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hgcd0 : Nat.gcd g d ≠ 0 := by
      have : 0 < Nat.gcd g d := Nat.gcd_pos_of_pos_left d (by omega)
      omega
    constructor
    · rintro ⟨⟨hkg, _⟩, hkd⟩; exact ⟨⟨hkg, hkd⟩, hgcd0⟩
    · rintro ⟨⟨hkg, hkd⟩, _⟩; exact ⟨⟨hkg, hg0⟩, hkd⟩
  have hpt : ∀ d : ℕ, ∑ k ∈ g.divisors, (moebius k : ℂ) * (if k ∣ d then F d else 0)
      = if Nat.Coprime d g then F d else 0 := by
    intro d
    have hrw : ∑ k ∈ g.divisors, (moebius k : ℂ) * (if k ∣ d then F d else 0)
        = F d * ∑ k ∈ g.divisors.filter (fun k => k ∣ d), (moebius k : ℂ) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      exact Finset.sum_congr rfl (fun k _ => by split_ifs <;> ring)
    rw [hrw, hset d, sum_divisors_moebius_C]
    by_cases hc : Nat.Coprime d g
    · have hg1 : Nat.gcd g d = 1 := by rw [Nat.gcd_comm]; exact hc
      rw [if_pos hg1, if_pos hc, mul_one]
    · have hg1 : ¬ Nat.gcd g d = 1 := by rw [Nat.gcd_comm]; exact hc
      rw [if_neg hg1, if_neg hc, mul_zero]
  have hRHS : ∑ k ∈ g.divisors, (moebius k : ℂ) * ∑ e ∈ Finset.Icc 1 (N / k), F (k * e)
      = ∑ d ∈ Finset.Icc 1 N, (if Nat.Coprime d g then F d else 0) := by
    have e1 : ∀ k ∈ g.divisors, (moebius k : ℂ) * ∑ e ∈ Finset.Icc 1 (N / k), F (k * e)
        = ∑ d ∈ Finset.Icc 1 N, (moebius k : ℂ) * (if k ∣ d then F d else 0) := by
      intro k hk
      rw [← sum_dvd_reindex_C (Nat.pos_of_mem_divisors hk) F, Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun d _ => hpt d)
  rw [Finset.sum_filter, hRHS]

/-- ℂ re-run of `inner_cop_swap_wt` (weighted coprime divisor swap). -/
private lemma inner_cop_swap_wt_C (χ : DirichletCharacter ℂ q) (w : ℕ → ℂ) (κ y : ℕ) :
    ∑ t ∈ Finset.Icc 1 y,
        (∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d κ), (chiRe χ d : ℂ)) * w t
      = ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Nat.Coprime d κ),
          (chiRe χ d : ℂ) * ∑ s ∈ Finset.Icc 1 (y / d), w (d * s) := by
  have hstep : ∀ t ∈ Finset.Icc 1 y,
      (∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d κ), (chiRe χ d : ℂ)) * w t
        = ∑ d ∈ Finset.Icc 1 y,
            (if d ∣ t ∧ Nat.Coprime d κ then (chiRe χ d : ℂ) * w t else 0) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have hset : t.divisors.filter (fun d => Nat.Coprime d κ)
        = (Finset.Icc 1 y).filter (fun d => d ∣ t ∧ Nat.Coprime d κ) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hdvd, _⟩, hcop⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) ht.2⟩, hdvd, hcop⟩
      · rintro ⟨⟨hd1, _⟩, hdvd, hcop⟩
        exact ⟨⟨hdvd, by omega⟩, hcop⟩
    rw [hset, Finset.sum_filter, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun d _ => by split_ifs <;> ring)
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  by_cases hcop : Nat.Coprime d κ
  · rw [if_pos hcop,
        Finset.sum_congr rfl (fun t _ => if_congr (and_iff_left hcop) rfl rfl),
        ← Finset.sum_filter, ← Finset.mul_sum, sum_dvd_reindex_C hd.1 w]
  · rw [if_neg hcop]
    exact Finset.sum_eq_zero (fun t _ => if_neg (fun h => hcop h.2))

/-- ℂ re-run of `weighted_char_count` (the `dhA = χ_ℝ ∗ 1` weighted swap). -/
private lemma weighted_char_count_C (χ : DirichletCharacter ℂ q) (h : ℕ → ℂ) (L : ℕ) :
    ∑ N ∈ Finset.Icc 1 L, (dhA χ N : ℂ) * h N
      = ∑ e ∈ Finset.Icc 1 L, (chiRe χ e : ℂ) * ∑ s ∈ Finset.Icc 1 (L / e), h (e * s) := by
  have hstep : ∀ N ∈ Finset.Icc 1 L, (dhA χ N : ℂ) * h N
      = ∑ e ∈ Finset.Icc 1 L, (if e ∣ N then (chiRe χ e : ℂ) * h N else 0) := by
    intro N hN
    rw [Finset.mem_Icc] at hN
    have hset : N.divisors = (Finset.Icc 1 L).filter (fun e => e ∣ N) := by
      ext e
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) hN.2⟩, hdvd⟩
      · rintro ⟨_, hdvd⟩; exact ⟨hdvd, by omega⟩
    have hdhA : (dhA χ N : ℂ) = ∑ d ∈ N.divisors, (chiRe χ d : ℂ) := by
      rw [dhA]; push_cast; rfl
    rw [hdhA, hset, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Finset.mem_Icc] at he
  rw [← Finset.sum_filter, ← Finset.mul_sum, sum_dvd_reindex_C he.1 h]

/-! ## §2 — R6-4@ρ : the EXACT reduction to the `dhD0rho` template -/

/-- **R6-4@ρ per-`g` core.** ℂ re-run of `dhA_kernel_reduction_inner`: for `g ∣ m`, the
`κ = m/g`-coprime inner sum against the complex kernel weight collapses onto `dhD0rho` at the
rescaled real scales `Y/(m·k)`. -/
private lemma dhA_kernel_reduction_inner_rho (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (ρ : ℂ) {m : ℕ} (hm : 1 ≤ m) {g : ℕ} (hg : g ∈ m.divisors) (Y : ℕ) :
    ∑ t ∈ Finset.Icc 1 (Y / m),
        (∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d (m / g)), (chiRe χ d : ℂ))
          * (((m * t : ℕ) : ℂ) ^ (-ρ) * ((1 - ((m * t : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ))
      = ∑ k ∈ (m / g).divisors,
          (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
            * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)) := by
  have hg1 : 1 ≤ g := Nat.pos_of_mem_divisors hg
  have hgm : g ∣ m := Nat.dvd_of_mem_divisors hg
  have hκ1 : 1 ≤ m / g := (Nat.one_le_div_iff hg1).mpr (Nat.le_of_dvd (by omega) hgm)
  rw [inner_cop_swap_wt_C χ
        (fun t => ((m * t : ℕ) : ℂ) ^ (-ρ) * ((1 - ((m * t : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ))
        (m / g) (Y / m),
      sum_coprime_eq_moebius_multiples_C (m / g) (Y / m) hκ1
        (fun d => (chiRe χ d : ℂ) * ∑ s ∈ Finset.Icc 1 (Y / m / d),
          ((m * (d * s) : ℕ) : ℂ) ^ (-ρ) * ((1 - ((m * (d * s) : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ))]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk1 : 1 ≤ k := Nat.pos_of_mem_divisors hk
  have hfold : (∑ e ∈ Finset.Icc 1 (Y / m / k),
        (chiRe χ (k * e) : ℂ) * ∑ s ∈ Finset.Icc 1 (Y / m / (k * e)),
          ((m * (k * e * s) : ℕ) : ℂ) ^ (-ρ)
            * ((1 - ((m * (k * e * s) : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ))
      = (chiRe χ k : ℂ) * ∑ N ∈ Finset.Icc 1 (Y / m / k), (dhA χ N : ℂ)
          * (((m * (k * N) : ℕ) : ℂ) ^ (-ρ)
            * ((1 - ((m * (k * N) : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)) := by
    rw [weighted_char_count_C χ (fun N => ((m * (k * N) : ℕ) : ℂ) ^ (-ρ)
          * ((1 - ((m * (k * N) : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)) (Y / m / k), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    have hchi : (chiRe χ (k * e) : ℂ) = (chiRe χ k : ℂ) * (chiRe χ e : ℂ) := by
      rw [chiRe_mul χ hsq k e]; push_cast; ring
    have hidx : Y / m / (k * e) = Y / m / k / e := (Nat.div_div_eq_div_mul (Y / m) k e).symm
    rw [hchi, hidx, mul_assoc]
    congr 1
    congr 1
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [mul_assoc k e s]
  have hval : (∑ N ∈ Finset.Icc 1 (Y / m / k), (dhA χ N : ℂ)
        * (((m * (k * N) : ℕ) : ℂ) ^ (-ρ) * ((1 - ((m * (k * N) : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)))
      = ((m * k : ℕ) : ℂ) ^ (-ρ) * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)) := by
    have hfloor : ⌊(Y : ℝ) / ((m * k : ℕ) : ℝ)⌋₊ = Y / (m * k) := Nat.floor_div_eq_div Y (m * k)
    have hLeq : Y / m / k = Y / (m * k) := Nat.div_div_eq_div_mul Y m k
    rw [dhD0rho, hfloor, hLeq, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun N _ => ?_)
    have hcpow : ((m * (k * N) : ℕ) : ℂ) ^ (-ρ)
        = ((m * k : ℕ) : ℂ) ^ (-ρ) * (N : ℂ) ^ (-ρ) := by
      rw [show ((m * (k * N) : ℕ) : ℂ) = (((m * k : ℕ) : ℝ) : ℂ) * ((N : ℝ) : ℂ) by
          push_cast; ring, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
      push_cast; ring
    have hkerR : (1 - ((m * (k * N) : ℕ) : ℝ) / (Y : ℝ))
        = (1 - (N : ℝ) / ((Y : ℝ) / ((m * k : ℕ) : ℝ))) := by
      rw [show ((m * (k * N) : ℕ) : ℝ) = ((m * k : ℕ) : ℝ) * (N : ℝ) by push_cast; ring,
        div_div_eq_mul_div]; ring
    rw [hcpow, show ((1 - ((m * (k * N) : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)
          = ((1 - (N : ℝ) / ((Y : ℝ) / ((m * k : ℕ) : ℝ)) : ℝ) : ℂ) from by rw [hkerR]]
    ring
  rw [hfold, hval]; ring

/-- **R6-4@ρ (`dhA_kernel_reduction_rho`) — THE EXACT REDUCTION at `n^{−ρ}·kernel`.** ℂ re-run of
`dhA_kernel_reduction`: the per-`m` kernel-restricted complex detector sum reduces EXACTLY to the
`m = 1` template `dhD0rho` at rescaled real scales `Y/(m·k)`. The `(†)` split `dhA_mul_eq_sum` is
coefficient-generic (cast to `ℂ`). -/
private lemma dhA_kernel_reduction_rho (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (ρ : ℂ) {m : ℕ} (hm : 1 ≤ m) (Y : ℕ) :
    ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n),
        (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ) * ((1 - (n : ℝ) / (Y : ℝ) : ℝ) : ℂ)
      = ∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
          (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
            * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)) := by
  rw [sum_dvd_reindex_C hm
      (fun n => (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ) * ((1 - (n : ℝ) / (Y : ℝ) : ℝ) : ℂ))]
  have hstep : ∀ t ∈ Finset.Icc 1 (Y / m),
      (dhA χ (m * t) : ℂ) * ((m * t : ℕ) : ℂ) ^ (-ρ)
          * ((1 - ((m * t : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)
        = ∑ g ∈ m.divisors, (chiRe χ g : ℂ)
            * ((∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d (m / g)), (chiRe χ d : ℂ))
                * (((m * t : ℕ) : ℂ) ^ (-ρ)
                  * ((1 - ((m * t : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ))) := by
    intro t _
    have hcast : (dhA χ (m * t) : ℂ) = ∑ g ∈ m.divisors, (chiRe χ g : ℂ)
        * ∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d (m / g)), (chiRe χ d : ℂ) := by
      rw [dhA_mul_eq_sum χ hsq hm t]; push_cast; rfl
    rw [show (dhA χ (m * t) : ℂ) * ((m * t : ℕ) : ℂ) ^ (-ρ)
            * ((1 - ((m * t : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)
          = (dhA χ (m * t) : ℂ) * (((m * t : ℕ) : ℂ) ^ (-ρ)
              * ((1 - ((m * t : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)) by ring, hcast, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun g _ => by ring)
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [← Finset.mul_sum, dhA_kernel_reduction_inner_rho χ hsq ρ hm hg Y]

/-! ## §3 — the ℂ regroup + the per-`m` residual (collection R6-5/6/7@ρ, reused) -/

/-- ℂ re-run of `dhExtractionW_regroup` (the `gcW` swap, generic in the ℂ factor `f`). -/
private lemma dhExtractionW_regroup_C (χ : DirichletCharacter ℂ q) (lam : ℕ → ℝ) (f : ℕ → ℂ)
    (Y : ℕ) :
    ∑ n ∈ Finset.Icc 1 Y, (dhCoeffW χ lam n : ℂ) * f n
      = ∑ m ∈ Finset.Icc 1 Y, (gcW lam m : ℂ)
          * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n), (dhA χ n : ℂ) * f n := by
  have hstep : ∀ n ∈ Finset.Icc 1 Y, (dhCoeffW χ lam n : ℂ) * f n
      = ∑ m ∈ n.divisors, (gcW lam m : ℂ) * ((dhA χ n : ℂ) * f n) := by
    intro n _
    have hc : (dhCoeffW χ lam n : ℂ)
        = (dhA χ n : ℂ) * ∑ m ∈ n.divisors, (gcW lam m : ℂ) := by
      rw [dhCoeffW, dhWeightSqW_eq_sum_gcW]; push_cast; ring
    rw [hc, show (dhA χ n : ℂ) * (∑ m ∈ n.divisors, (gcW lam m : ℂ)) * f n
        = (∑ m ∈ n.divisors, (gcW lam m : ℂ)) * ((dhA χ n : ℂ) * f n) by ring, Finset.sum_mul]
  have hcomm : ∀ (n m : ℕ), (n ∈ Finset.Icc 1 Y ∧ m ∈ n.divisors)
      ↔ (n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n) ∧ m ∈ Finset.Icc 1 Y) := by
    intro n m
    simp only [Finset.mem_Icc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn1, hnY⟩, hmn, _⟩
      have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos hmn (by omega)
      have hmn' : m ≤ n := Nat.le_of_dvd (by omega) hmn
      exact ⟨⟨⟨hn1, hnY⟩, hmn⟩, hm1, le_trans hmn' hnY⟩
    · rintro ⟨⟨⟨hn1, hnY⟩, hmn⟩, _, _⟩
      exact ⟨⟨hn1, hnY⟩, hmn, by omega⟩
  calc ∑ n ∈ Finset.Icc 1 Y, (dhCoeffW χ lam n : ℂ) * f n
      = ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ n.divisors, (gcW lam m : ℂ) * ((dhA χ n : ℂ) * f n) :=
        Finset.sum_congr rfl hstep
    _ = ∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n),
          (gcW lam m : ℂ) * ((dhA χ n : ℂ) * f n) := Finset.sum_comm' hcomm
    _ = ∑ m ∈ Finset.Icc 1 Y, (gcW lam m : ℂ)
          * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n), (dhA χ n : ℂ) * f n := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]

set_option maxHeartbeats 1200000 in
-- The per-m residual assembles a double-sum norm-triangle over the exact complex main collection
-- (the `clean_cpow_term`/`selHmul_collection` cast + field_simp over `(1−ρ)(2−ρ)`) exceeds default.
/-- **R6-8@ρ per-`m` residual (collection R6-5/6/7@ρ reused).** ℂ/norm analog of
`dh_extraction_per_m`: for squarefree `m ≤ z²`, the per-`m` complex reduction differs from the
EXACT complex main `L(1,χ)·Y^{1−ρ}/((1−ρ)(2−ρ))·selNu(m)` by at most `C₂ρ·Y^{1/2−σ}·Σ_{g,k}
(m·k)^{−1/2}`. The signed main collects EXACTLY (`clean_cpow_term` + `selHmul_collection` cast,
`selNu`); the residual is a norm-triangle over `(g,k)` with `unmoll_extraction_rho_tall` (`x ≥ 2`
guard), `‖(m·k)^{−ρ}‖ = (m·k)^{−σ}`, and `dhD0_scale_err` at `β₀ = ρ.re`. -/
private lemma dh_extraction_per_m_rho_tall [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re < 1)
    {H : ℝ} (him : |ρ.im| ≤ H)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ H → ‖zetaHol s‖ ≤ Z₀)
    {z Y m : ℕ} (hz : 1 ≤ z) (hY : 2 * z ^ 4 ≤ Y) (hm1 : 1 ≤ m) (hmsf : Squarefree m)
    (hmz2 : m ≤ z ^ 2) :
    ‖(∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
          (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
            * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
       - DirichletCharacter.LFunction χ 1 * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))
           * (selNu χ m : ℂ)‖
      ≤ C2Rho q Z₀ ρ * (Y : ℝ) ^ (1 / 2 - ρ.re)
        * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  set L₁ : ℂ := DirichletCharacter.LFunction χ 1 with hL1def
  set C₂ρ : ℝ := C2Rho q Z₀ ρ with hC2def
  have hu : 0 < 1 - ρ.re := by linarith
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hhi; simp at hhi
  have hsne : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (fun h => hρ1 h.symm)
  have h2ρne : (2 - ρ) ≠ 0 := by
    intro h; have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, Complex.re_ofNat] at this; linarith
  have hm0 : m ≠ 0 := by omega
  have hz4 : 1 ≤ z ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hYm : 1 ≤ Y := by omega
  have hmC0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  have hmu_le : ∀ k : ℕ, ‖(moebius k : ℂ)‖ ≤ 1 := by
    intro k; rw [show (moebius k : ℂ) = ((moebius k : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
  have hguard : ∀ g ∈ m.divisors, ∀ k ∈ (m / g).divisors,
      (1 : ℕ) ≤ m * k ∧ (2 : ℝ) ≤ (Y : ℝ) / ((m * k : ℕ) : ℝ) := by
    intro g hg k hk
    have hg1 : 1 ≤ g := Nat.pos_of_mem_divisors hg
    have hgm : g ∣ m := Nat.dvd_of_mem_divisors hg
    have hk1 : 1 ≤ k := Nat.pos_of_mem_divisors hk
    have hmgpos : 0 < m / g := Nat.div_pos (Nat.le_of_dvd (by omega) hgm) hg1
    have hkm : k ≤ m :=
      le_trans (Nat.le_of_dvd hmgpos (Nat.dvd_of_mem_divisors hk)) (Nat.div_le_self m g)
    have hmk1 : 1 ≤ m * k := Nat.mul_pos hm1 hk1
    have hmkz4 : m * k ≤ z ^ 4 := by
      calc m * k ≤ m * m := Nat.mul_le_mul (le_refl m) hkm
        _ ≤ z ^ 2 * z ^ 2 := Nat.mul_le_mul hmz2 hmz2
        _ = z ^ 4 := by ring
    have h2mk : 2 * (m * k) ≤ Y := le_trans (by omega) hY
    have hmkR : (0 : ℝ) < ((m * k : ℕ) : ℝ) := by exact_mod_cast hmk1
    refine ⟨hmk1, ?_⟩
    rw [le_div_iff₀ hmkR]
    calc (2 : ℝ) * ((m * k : ℕ) : ℝ) = ((2 * (m * k) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Y : ℝ) := by exact_mod_cast h2mk
  -- STEP 1 : the exact main collection
  have hterm : ∀ g ∈ m.divisors, ∀ k ∈ (m / g).divisors,
      (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
          * (L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)))
        = (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (1 / (m : ℂ)))
            * ((moebius k : ℂ) * (chiRe χ k : ℂ) / (k : ℂ)) := by
    intro g hg k hk
    obtain ⟨hmk1, -⟩ := hguard g hg k hk
    have hk0 : (k : ℂ) ≠ 0 := by
      have : k ≠ 0 := by have := Nat.pos_of_mem_divisors hk; omega
      exact_mod_cast this
    have hscale : ((m * k : ℕ) : ℂ) ^ (-ρ)
        * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ)
        = (Y : ℂ) ^ (1 - ρ) / ((m * k : ℕ) : ℂ) := by
      rw [show (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) = (Y : ℂ) / ((m * k : ℕ) : ℂ) by
          push_cast; ring]
      exact clean_cpow_term (d := m * k) (t := Y) hmk1 ρ
    rw [show (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
            * (L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)))
          = (moebius k : ℂ) * (chiRe χ k : ℂ) * L₁ / ((1 - ρ) * (2 - ρ))
            * (((m * k : ℕ) : ℂ) ^ (-ρ)
              * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ)) by ring,
        hscale, show ((m * k : ℕ) : ℂ) = (m : ℂ) * (k : ℂ) by push_cast; ring]
    field_simp
  have hcollC : ∑ g ∈ m.divisors, (chiRe χ g : ℂ)
        * ∑ k ∈ (m / g).divisors, (moebius k : ℂ) * (chiRe χ k : ℂ) / (k : ℂ)
      = (selHmul χ m : ℂ) := by
    rw [← selHmul_collection χ hsq hmsf]; push_cast; rfl
  have hmainval : (∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
        (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
          * (L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))))
      = L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ) := by
    calc (∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
            (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
              * (L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))))
        = ∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
            (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (1 / (m : ℂ)))
              * ((moebius k : ℂ) * (chiRe χ k : ℂ) / (k : ℂ)) := by
          refine Finset.sum_congr rfl (fun g hg => ?_)
          congr 1
          exact Finset.sum_congr rfl (fun k hk => hterm g hg k hk)
      _ = (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (1 / (m : ℂ)))
            * ∑ g ∈ m.divisors, (chiRe χ g : ℂ)
                * ∑ k ∈ (m / g).divisors, (moebius k : ℂ) * (chiRe χ k : ℂ) / (k : ℂ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun g _ => ?_)
          rw [← Finset.mul_sum]; ring
      _ = (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (1 / (m : ℂ))) * (selHmul χ m : ℂ) := by
          rw [hcollC]
      _ = L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ) := by
          rw [selNu, show (selHmul χ m / (m : ℝ) : ℝ) = selHmul χ m / (m : ℝ) from rfl]
          push_cast; field_simp
  rw [← hmainval, ← Finset.sum_sub_distrib]
  -- STEP 2 : the signed residual and its norm triangle
  have hcombine : ∀ g ∈ m.divisors,
      (chiRe χ g : ℂ) * (∑ k ∈ (m / g).divisors, (moebius k : ℂ) * (chiRe χ k : ℂ)
          * ((m * k : ℕ) : ℂ) ^ (-ρ) * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
        - (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
            (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
            * (L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)))
      = ∑ k ∈ (m / g).divisors, (chiRe χ g : ℂ) * ((moebius k : ℂ) * (chiRe χ k : ℂ)
          * ((m * k : ℕ) : ℂ) ^ (-ρ)
          * (dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ))
            - L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)))) := by
    intro g _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [Finset.sum_congr rfl hcombine]
  calc ‖∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors,
          (chiRe χ g : ℂ) * ((moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
            * (dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ))
              - L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))))‖
      ≤ ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors,
          C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re) * ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun g hg => ?_))
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => ?_))
        obtain ⟨hmk1, hx2⟩ := hguard g hg k hk
        have hmkR0 : (0 : ℝ) < ((m * k : ℕ) : ℝ) := by exact_mod_cast hmk1
        have hR3 := unmoll_extraction_rho_tall χ hχ hsq hq hzero hlo hhi him hZ
          (x := (Y : ℝ) / ((m * k : ℕ) : ℝ)) hx2
        rw [← hL1def, ← hC2def] at hR3
        have hcpownorm : ‖((m * k : ℕ) : ℂ) ^ (-ρ)‖ = ((m * k : ℕ) : ℝ) ^ (-ρ.re) := by
          rw [show ((m * k : ℕ) : ℂ) = (((m * k : ℕ) : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_cpow_eq_rpow_re_of_pos hmkR0]
          rw [Complex.neg_re]
        have herr := dhD0_scale_err (β₀ := ρ.re) (a := m * k) (Y := Y) hmk1 hYm
        calc ‖(chiRe χ g : ℂ) * ((moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
                * (dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ))
                  - L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))))‖
            = ‖(chiRe χ g : ℂ)‖ * (‖(moebius k : ℂ)‖ * ‖(chiRe χ k : ℂ)‖
                * ((m * k : ℕ) : ℝ) ^ (-ρ.re)
                * ‖dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ))
                  - L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ)
                      / ((1 - ρ) * (2 - ρ))‖) := by
              rw [norm_mul, norm_mul, norm_mul, norm_mul, hcpownorm]
          _ ≤ 1 * (1 * 1 * ((m * k : ℕ) : ℝ) ^ (-ρ.re)
                * (C₂ρ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 / 2 - ρ.re))) := by
              gcongr
              · rw [Complex.norm_real, Real.norm_eq_abs]; exact chiRe_abs_le_one χ g
              · exact hmu_le k
              · rw [Complex.norm_real, Real.norm_eq_abs]; exact chiRe_abs_le_one χ k
          _ = C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re) * ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
              rw [show (1 : ℝ) * (1 * 1 * ((m * k : ℕ) : ℝ) ^ (-ρ.re)
                    * (C₂ρ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 / 2 - ρ.re)))
                  = C₂ρ * (((m * k : ℕ) : ℝ) ^ (-ρ.re)
                    * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 / 2 - ρ.re)) by ring, herr]
              ring
    _ = C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re)
          * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [Finset.mul_sum]

set_option maxHeartbeats 1200000 in
-- The capstone: ℂ regroup + exact reduction (R6-4@ρ) + signed complex main collection + the
-- per-m residual moment; the double-sum norm-triangle exceeds the default heartbeat budget.
/-- **E(ρ) assembly (`dh_extraction_upper_rho_tall`) — the complex-scale weighted extraction.**
The ℂ analog of `dh_extraction_upper_W`: the Selberg-mollified `ρ`-detector's partial sum is
`L(1,χ)·selMainTerm` main (the FULL complex `L`-value, `/((1−ρ)(2−ρ))`) plus a `Y^{1/2−σ}`
error, `C₂ρ = C2Rho q Z₀ ρ`, under the guard `2z⁴ ≤ Y`. STEP 1 ℂ regroup
(`dhExtractionW_regroup_C`) + kernel (`dhKernR_eq`) + the EXACT reduction
(`dhA_kernel_reduction_rho`); STEP 2 the signed complex main collected EXACTLY
(`sum_gcW_selNu_eq_selMainTerm` cast); STEP 3 signed
subtraction; STEP 4 norm-triangle on the residual only (`dh_extraction_per_m_rho_tall` +
`sum_gcW_pairkernel_le`, `gcW = 0` off squarefree/`> z²`). -/
theorem dh_extraction_upper_rho_tall [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re < 1)
    {H : ℝ} (him : |ρ.im| ≤ H)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ H → ‖zetaHol s‖ ≤ Z₀)
    {z Y : ℕ} (hz : 1 ≤ z) (hY : 2 * z ^ 4 ≤ Y) :
    ‖∑ n ∈ Finset.Icc 1 Y,
        (dhCoeffW χ (selWeight χ z) n : ℂ) * (n : ℂ) ^ (-ρ)
          * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ)
       - DirichletCharacter.LFunction χ 1 * (selMainTerm χ z : ℂ)
           * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))‖
      ≤ C2Rho q Z₀ ρ * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - ρ.re) := by
  set L₁ : ℂ := DirichletCharacter.LFunction χ 1 with hL1def
  set C₂ρ : ℝ := C2Rho q Z₀ ρ with hC2def
  have hσ0 : 0 < ρ.re := by linarith
  have hu : 0 < 1 - ρ.re := by linarith
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hhi; simp at hhi
  have hsne : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (fun h => hρ1 h.symm)
  have hnpos : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hsne
  have h2ρne : (2 - ρ) ≠ 0 := by
    intro h; have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, Complex.re_ofNat] at this; linarith
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hMnn : 0 ≤ Real.sqrt q * (1 + Real.log q) := by positivity
  have hZ0nn : 0 ≤ Z₀ := le_trans (norm_nonneg _)
    (hZ ρ hlo hhi.le him)
  have hC2nn : 0 ≤ C₂ρ := by
    rw [hC2def, C2Rho, CwRho]
    have h1 : (0:ℝ) ≤ ‖ρ‖ / ρ.re := div_nonneg (norm_nonneg _) hσ0.le
    positivity
  have hY1 : 1 ≤ Y := by have := Nat.one_le_pow 4 z (by omega); omega
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY1
  have hz2Y : z ^ 2 ≤ Y := by
    have h1 : z ^ 2 ≤ z ^ 4 := Nat.pow_le_pow_right hz (by norm_num)
    omega
  have hsfsupp : ∀ d, selWeight χ z d ≠ 0 → Squarefree d :=
    fun d h => selWeight_ne_zero_squarefree χ z h
  -- STEP 1 : ℂ regroup + exact reduction (R6-4@ρ)
  rw [Finset.sum_congr rfl (fun n _ => mul_assoc _ _ _),
      dhExtractionW_regroup_C χ (selWeight χ z)
        (fun n => (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ)) Y]
  have hred : ∀ m ∈ Finset.Icc 1 Y,
      (gcW (selWeight χ z) m : ℂ) * (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n),
          (dhA χ n : ℂ) * ((n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ)))
        = (gcW (selWeight χ z) m : ℂ) * (∑ g ∈ m.divisors, (chiRe χ g : ℂ)
            * ∑ k ∈ (m / g).divisors, (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
              * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ))) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    congr 1
    rw [← dhA_kernel_reduction_rho χ hsq ρ (by omega : 1 ≤ m) Y]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [dhKernR_eq (by rw [div_le_one hYpos]; exact_mod_cast hn.1.2), ← mul_assoc]
  rw [Finset.sum_congr rfl hred]
  -- STEP 2 : the signed complex main collected EXACTLY
  have hgcwselnuC : ∑ m ∈ Finset.Icc 1 Y, (gcW (selWeight χ z) m : ℂ) * (selNu χ m : ℂ)
      = (selMainTerm χ z : ℂ) := by
    rw [← sum_gcW_selNu_eq_selMainTerm χ hsq hz hz2Y]; push_cast; rfl
  have htarget : (∑ m ∈ Finset.Icc 1 Y, (gcW (selWeight χ z) m : ℂ)
        * (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ)))
      = L₁ * (selMainTerm χ z : ℂ) * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) := by
    rw [show (∑ m ∈ Finset.Icc 1 Y, (gcW (selWeight χ z) m : ℂ)
            * (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ)))
          = L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))
              * ∑ m ∈ Finset.Icc 1 Y, (gcW (selWeight χ z) m : ℂ) * (selNu χ m : ℂ) from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring),
      hgcwselnuC]
    ring
  rw [← htarget, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun m _ => by ring :
      ∀ m ∈ Finset.Icc 1 Y,
        (gcW (selWeight χ z) m : ℂ) * (∑ g ∈ m.divisors, (chiRe χ g : ℂ)
              * ∑ k ∈ (m / g).divisors, (moebius k : ℂ) * (chiRe χ k : ℂ)
                  * ((m * k : ℕ) : ℂ) ^ (-ρ) * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
          - (gcW (selWeight χ z) m : ℂ)
              * (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ))
        = (gcW (selWeight χ z) m : ℂ)
            * ((∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
                (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
                  * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
              - L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ)))]
  -- STEP 3 : norm-triangle on the residual
  refine (norm_sum_le _ _).trans ?_
  have hpm : ∀ m ∈ Finset.Icc 1 Y,
      ‖(gcW (selWeight χ z) m : ℂ)
          * ((∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
              (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
                * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
            - L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ))‖
        ≤ |gcW (selWeight χ z) m| * (C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re)
            * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
    intro m hm
    rw [norm_mul, show ‖(gcW (selWeight χ z) m : ℂ)‖ = |gcW (selWeight χ z) m| from by
      rw [Complex.norm_real, Real.norm_eq_abs]]
    rcases eq_or_ne (gcW (selWeight χ z) m) 0 with hg0 | hg0
    · rw [hg0, abs_zero, zero_mul, zero_mul]
    · have hmsf : Squarefree m := by
        by_contra h; exact hg0 (gcW_eq_zero_of_not_squarefree hsfsupp h)
      have hmz2 : m ≤ z ^ 2 := by
        by_contra h; exact hg0 (gcW_selWeight_eq_zero_of_gt_sq χ (by omega))
      have hm1 : 1 ≤ m := by rw [Finset.mem_Icc] at hm; omega
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have := dh_extraction_per_m_rho_tall χ hχ hsq hq hzero hlo hhi him hZ hz hY hm1 hmsf hmz2
      rw [← hL1def, ← hC2def] at this
      exact this
  refine (Finset.sum_le_sum hpm).trans ?_
  have hYrp : (0 : ℝ) ≤ (Y : ℝ) ^ (1 / 2 - ρ.re) := Real.rpow_nonneg hYpos.le _
  calc ∑ m ∈ Finset.Icc 1 Y, |gcW (selWeight χ z) m| * (C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re)
          * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))
      = C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re) * ∑ m ∈ Finset.Icc 1 Y, |gcW (selWeight χ z) m|
          * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)
    _ ≤ C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re) * ((z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9) :=
        mul_le_mul_of_nonneg_left (sum_gcW_pairkernel_le χ hsq hz hz2Y)
          (mul_nonneg hC2nn hYrp)
    _ = C₂ρ * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - ρ.re) := by ring

end Compose

/-! ## §2 — the master, the re-priced estimates, and the per-instance assembly -/

set_option maxHeartbeats 1600000 in
-- The balance chain threads floor + shift + β₀-cancellation + ρ-norm over the
-- `(1−ρ)(2−ρ)`/selMainTerm denominators; the rearrangement exceeds the default budget (as in
-- `dh_balance`).
/-- **The tight ray master.** Same guards as `dh_balance`, but the balance is kept in TIGHT form:
the `x^u−1` cancellation (`tail_shift_to_beta0`, the `−(1−1/Y)`) is RETAINED, and the ρ-main term
`L₁·selMainTerm·Y^{1−σ}/(‖1−ρ‖‖2−ρ‖)` is bounded via `H_lower` (`L₁·selMainTerm ≤ (1−β₀)(2−β₀)`),
injecting its `u = 1−β₀` factor.  The result is the freeze master `1 − 1/Y ≤ (ρ-row) + (Eρ-row) +
Y^{β₀−σ}((Y^{1−β₀}+Eβ) − (1−1/Y))`, each RHS row small on the ray `u < τ` (the on-ray caps of §3
close the contradiction). -/
theorem dh_master_ray_tall [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β₀ : ℝ}
    (hzeroβ : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0) (hloβ : 1 / 2 ≤ β₀) (hhiβ : β₀ < 1)
    {ρ : ℂ} (hzeroρ : DirichletCharacter.LFunction χ ρ = 0) (hloρ : 1 / 2 ≤ ρ.re) (hhiρ : ρ.re < 1)
    {H : ℝ} (himρ : |ρ.im| ≤ H) (hord : ρ.re ≤ β₀)
    {Zρ Zβ : ℝ}
    (hZρ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ H → ‖zetaHol s‖ ≤ Zρ)
    (hZβ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Zβ)
    {N : ℕ} (hN : 4 ≤ N) (hscale : (N : ℝ) ^ (1 - β₀) ≤ Real.exp 1)
    (hguard : 2 * (34 + 12 * (Real.sqrt q * (1 + Real.log q))
        + 12 * (Real.sqrt q * (1 + Real.log q)) * Zβ
        + 36 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀)) * (N : ℝ) ^ (1 / 2 - β₀) ≤ 1 / 64)
    {z Y : ℕ} (hz : 2 ≤ z) (hY : 2 * z ^ 4 ≤ Y)
    (hcov : crushErr q Zβ β₀ z ≤ 27 / 100 * ((1 - β₀) * (z : ℝ) ^ (1 - β₀))) :
    1 - 1 / (Y : ℝ)
      ≤ (1 - β₀) * (2 - β₀) * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖)
        + C2Rho q Zρ ρ * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - ρ.re)
        + (Y : ℝ) ^ (β₀ - ρ.re) * ((Y : ℝ) ^ (1 - β₀)
            + (136 + 48 * (Real.sqrt q * (1 + Real.log q))
                + 48 * (Real.sqrt q * (1 + Real.log q)) * Zβ
                + 144 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀))
              * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀)
            - (1 - 1 / (Y : ℝ))) := by
  set L₁re : ℝ := (DirichletCharacter.LFunction χ 1).re with hL1re
  set Eβ : ℝ := (136 + 48 * (Real.sqrt q * (1 + Real.log q))
      + 48 * (Real.sqrt q * (1 + Real.log q)) * Zβ
      + 144 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀))
    * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀) with hEβ
  set Eρ : ℝ := C2Rho q Zρ ρ * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9
    * (Y : ℝ) ^ (1 / 2 - ρ.re) with hEρ
  have hσ0 : 0 < ρ.re := by linarith
  have hu : 0 < 1 - β₀ := by linarith
  have hu2 : 0 < 2 - β₀ := by linarith
  have hDpos : 0 < (1 - β₀) * (2 - β₀) := mul_pos hu hu2
  have hz1 : 1 ≤ z := by omega
  have hY1 : 1 ≤ Y := by have := Nat.one_le_pow 4 z (by omega); omega
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY1
  have hne : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hhiρ; simp at hhiρ
  have hsne : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (fun h => hρ1 h.symm)
  have hnpos : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hsne
  have h2ρne : (2 - ρ) ≠ 0 := by
    intro h; have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, Complex.re_ofNat] at this; linarith
  have h2npos : 0 < ‖2 - ρ‖ := norm_pos_iff.mpr h2ρne
  have hselM : 0 < selMainTerm χ z := by
    rw [selberg_opt_eq χ hsq hz1]; exact one_div_pos.mpr (selHSum_pos χ hsq hz1)
  -- coefficient facts
  have hcnn : ∀ n, 0 ≤ dhCoeffW χ (selWeight χ z) n := by
    intro n; rcases eq_or_ne n 0 with rfl | hn
    · simp [dhCoeffW, dhWeightSqW, dhA]
    · exact dhCoeffW_nonneg χ hsq _ hn
  have hc1 : dhCoeffW χ (selWeight χ z) 1 = 1 := by
    rw [dhCoeffW_one, selWeight_apply_one χ hsq hz1, one_pow]
  -- floor : 1 − 1/Y ≤ ‖D_ρ‖ + S₀
  have hfloor := dhW_detector_floor_rho χ hsq hσ0 hz1 hY1
  -- R1 shift (TIGHT) : S₀ ≤ Y^{β₀−σ}·(D₀^{β₀} − (1−1/Y))
  have hshift := tail_shift_to_beta0 (c := dhCoeffW χ (selWeight χ z)) hcnn hc1
    (x := (Y : ℝ)) (by exact_mod_cast hY1) (N := Y) hY1 (σ := ρ.re) (β₀ := β₀) hord
  -- β₀-side : D₀^{β₀} ≤ Y^{1−β₀} + E(β₀)
  have hR6β := dh_extraction_upper_W χ hχ hsq hq hzeroβ hloβ hhiβ hZβ hz1 hY
  have hHl := H_lower χ hχ hsq hq hzeroβ hloβ hhiβ hZβ hN hscale hguard hz hcov
  have hopt := selberg_opt_eq χ hsq hz1
  have hHpos := selHSum_pos χ hsq hz1
  have hYβrp : (0 : ℝ) ≤ (Y : ℝ) ^ (1 - β₀) := Real.rpow_nonneg hYpos.le _
  have hcancel : L₁re * selMainTerm χ z * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))
      ≤ (Y : ℝ) ^ (1 - β₀) := by
    rw [hopt]
    have hrw : L₁re * (1 / selHSum χ z) * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))
        = (L₁re / ((1 - β₀) * (2 - β₀)) / selHSum χ z) * (Y : ℝ) ^ (1 - β₀) := by field_simp
    rw [hrw]
    calc (L₁re / ((1 - β₀) * (2 - β₀)) / selHSum χ z) * (Y : ℝ) ^ (1 - β₀)
        ≤ 1 * (Y : ℝ) ^ (1 - β₀) :=
          mul_le_mul_of_nonneg_right ((div_le_one hHpos).mpr hHl) hYβrp
      _ = (Y : ℝ) ^ (1 - β₀) := one_mul _
  have hD0β : ∑ n ∈ Finset.Icc 1 Y, dhCoeffW χ (selWeight χ z) n * (n : ℝ) ^ (-β₀)
        * dhKernR ((n : ℝ) / (Y : ℝ))
      ≤ (Y : ℝ) ^ (1 - β₀) + Eβ := by
    rw [← hL1re, ← hEβ] at *
    linarith [(abs_le.mp hR6β).2, hcancel]
  -- the ρ-main norm identity and the u-injection
  have hR6ρ := dh_extraction_upper_rho_tall χ hχ hsq hq hzeroρ hloρ hhiρ himρ hZρ hz1 hY
  rw [← hEρ] at hR6ρ
  have hmain_norm : ‖DirichletCharacter.LFunction χ 1 * (selMainTerm χ z : ℂ) * (Y : ℂ) ^ (1 - ρ)
        / ((1 - ρ) * (2 - ρ))‖
      = L₁re * selMainTerm χ z * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_LFunction_one_eq_re χ hne hsq, ← hL1re,
      show ‖(selMainTerm χ z : ℂ)‖ = selMainTerm χ z from by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hselM.le],
      show ‖(Y : ℂ) ^ (1 - ρ)‖ = (Y : ℝ) ^ (1 - ρ.re) from by
        rw [show (Y : ℂ) = ((Y : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
        rw [Complex.sub_re, Complex.one_re]]
  have hDρnorm : ‖∑ n ∈ Finset.Icc 1 Y, (dhCoeffW χ (selWeight χ z) n : ℂ) * (n : ℂ) ^ (-ρ)
        * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ)‖
      ≤ L₁re * selMainTerm χ z * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖) + Eρ := by
    have htri := norm_sub_norm_le (∑ n ∈ Finset.Icc 1 Y, (dhCoeffW χ (selWeight χ z) n : ℂ)
        * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ))
      (DirichletCharacter.LFunction χ 1 * (selMainTerm χ z : ℂ) * (Y : ℂ) ^ (1 - ρ)
        / ((1 - ρ) * (2 - ρ)))
    rw [hmain_norm] at htri
    linarith [htri, hR6ρ]
  -- u-injection : L₁re·selMainTerm ≤ (1−β₀)(2−β₀)
  have hLselM : L₁re * selMainTerm χ z ≤ (1 - β₀) * (2 - β₀) := by
    have hle : L₁re ≤ selHSum χ z * ((1 - β₀) * (2 - β₀)) := (div_le_iff₀ hDpos).mp hHl
    rw [hopt, mul_one_div, div_le_iff₀ hHpos]
    nlinarith [hle]
  have hKnn : (0 : ℝ) ≤ (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖) := by positivity
  have hmainρ_le : L₁re * selMainTerm χ z * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖)
      ≤ (1 - β₀) * (2 - β₀) * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖) := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hLselM hKnn
  -- combine : the tight master
  have hYβσ : (0 : ℝ) ≤ (Y : ℝ) ^ (β₀ - ρ.re) := Real.rpow_nonneg hYpos.le _
  have hSshift : ∑ n ∈ Finset.Icc 2 Y, dhCoeffW χ (selWeight χ z) n * (n : ℝ) ^ (-ρ.re)
        * dhKernR ((n : ℝ) / (Y : ℝ))
      ≤ (Y : ℝ) ^ (β₀ - ρ.re) * (((Y : ℝ) ^ (1 - β₀) + Eβ) - (1 - 1 / (Y : ℝ))) := by
    refine le_trans hshift ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hD0β]) hYβσ
  linarith [hfloor, hSshift, hDρnorm, hmainρ_le]

set_option maxHeartbeats 800000 in
-- The C2Rho/CwRho unfolding produces a 6-term sum whose per-term division bounds + the two folds
-- (into `r = L₂/c₀`, then `M·Q² ≤ Q^{5/2}L₂`) exceed the default budget.
/-- **The ρ-extraction constant bound, TALL.**  `C2Rho q Z₀ ρ ≤ 570·Q^{5/2}·L₂²/c₀` via the ZFR
pole floors `1/‖1−ρ‖, 1/(1−σ) ≤ L₂/c₀` and the TALL crude bounds `‖ρ‖ ≤ Q`, `Z₀ ≤ 2Q`.

This is `C2Rho_le` re-priced. The landed version reads the height through `‖ρ‖ ≤ 2` (from
`|Im ρ| ≤ 1`), which fixes `2(9+8‖ρ‖) ≤ 50` and `‖ρ‖/σ ≤ 3`. Off the unit box both grow linearly
in the height, and both are `≤ Q` because `Q = q(|Im ρ| + 2)` with `q ≥ 2` is the contract's own
base. Charging BOTH growths plus the `Z₀ ≤ 2Q` growth to the `Q`-exponent costs exactly two
powers: `Q^{1/2} ⇝ Q^{5/2}`, and the `Z₀`-carrying coefficient `(564 + 72Z₀)` collapses to the
numeral `570 = 102 + 108 + 162 + 198` — exactly `hfold2`'s four folds.

**TAU-SHARP S6.** The statement was landed at `636`, but `hfold2` below always proved `570`;
the `636` was slack the assembly never used.  Retiring it is `−0.88` on `log(1/c)` (the `KEρ`
arm) and costs no proof step: `hfold2`, `hfold2r`, `hfinaleq` are numeral-agnostic. -/
lemma C2Rho_le_tall {q : ℕ} {Z₀ Q L₂ c₀ : ℝ} {ρ : ℂ}
    (hσlo : 16 / 17 ≤ ρ.re) (hσ1 : ρ.re < 1) (hQ1 : 1 ≤ Q) (hρQ : ‖ρ‖ ≤ Q)
    (hZ0 : 0 ≤ Z₀) (hZ0Q : Z₀ ≤ 2 * Q) (hc0 : 0 < c₀) (hLc : 1 ≤ L₂ / c₀) (hL2' : 1 ≤ L₂)
    (hMQ : Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) ≤ Q ^ (1 / 2 : ℝ) * L₂)
    (hMnn : 0 ≤ Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)))
    (hBpos : 1 ≤ Q ^ (1 / 2 : ℝ) * L₂)
    (hpole : 1 / ‖1 - ρ‖ ≤ L₂ / c₀) (hsig : 1 / (1 - ρ.re) ≤ L₂ / c₀)
    (hnpos : 0 < ‖1 - ρ‖) :
    C2Rho q Z₀ ρ ≤ 570 * (Q ^ (5 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀) := by
  rw [C2Rho, CwRho]
  set M : ℝ := Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) with hMdef
  set B : ℝ := Q ^ (1 / 2 : ℝ) * L₂ with hBdef
  set r : ℝ := L₂ / c₀ with hrdef
  have hσ0 : 0 < ρ.re := by linarith
  have hσn : 0 < 1 - ρ.re := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hr1 : 1 ≤ r := hLc
  have hrnn : 0 ≤ r := by linarith
  have hρnn : 0 ≤ ‖ρ‖ := norm_nonneg _
  have hBnn : 0 ≤ B := by linarith
  have hMQnn : 0 ≤ M * Q := mul_nonneg hMnn hQ0.le
  -- the two TALL crude bounds
  have hρσ : ‖ρ‖ / ρ.re ≤ 2 * Q := by
    rw [div_le_iff₀ hσ0]
    nlinarith [hρQ, hQ0.le, mul_nonneg hQ0.le (by linarith : (0 : ℝ) ≤ ρ.re - 16 / 17)]
  have hρσnn : 0 ≤ ‖ρ‖ / ρ.re := div_nonneg hρnn hσ0.le
  set P : ℝ := 3 * M * (1 + ‖ρ‖ / ρ.re) with hPdef
  have hPnn : 0 ≤ P := by rw [hPdef]; positivity
  have hPle : P ≤ 9 * (M * Q) := by
    rw [hPdef]
    nlinarith [mul_le_mul_of_nonneg_left hρσ (by positivity : (0 : ℝ) ≤ 3 * M),
      mul_nonneg hMnn (by linarith : (0 : ℝ) ≤ Q - 1)]
  -- per-term bounds (into r and Q)
  have hA : 12 * M / ‖1 - ρ‖ ≤ 12 * M * r := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hpole (by positivity)
  have hB' : 2 * (9 + 8 * ‖ρ‖) ≤ 34 * Q := by nlinarith [hρQ, hQ1]
  have hC : 2 * (Z₀ + 1 / ‖1 - ρ‖) * P ≤ 18 * (M * Q) * Z₀ + 18 * (M * Q) * r := by
    have h1 : Z₀ + 1 / ‖1 - ρ‖ ≤ Z₀ + r := by linarith [hpole]
    have h2 : 2 * (Z₀ + 1 / ‖1 - ρ‖) * P ≤ 2 * (Z₀ + r) * (9 * (M * Q)) := by
      apply mul_le_mul _ hPle hPnn (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    nlinarith [h2]
  have hD : 2 * P ≤ 18 * (M * Q) := by linarith [hPle]
  have hE : 2 * P / (1 - ρ.re) ≤ 18 * (M * Q) * r := by
    rw [div_eq_mul_one_div]
    have h1 : 2 * P * (1 / (1 - ρ.re)) ≤ 2 * (9 * (M * Q)) * r := by
      apply mul_le_mul _ hsig (by positivity) (by positivity)
      linarith [hPle]
    linarith [h1]
  have hExtra : 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) ≤ 162 * M * r := by
    have hdist : 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re))
        = 90 * M / ‖1 - ρ‖ + 72 * M / (1 - ρ.re) := by
      field_simp; ring
    rw [hdist]
    have h1 : 90 * M / ‖1 - ρ‖ ≤ 90 * M * r := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hpole (by positivity)
    have h2 : 72 * M / (1 - ρ.re) ≤ 72 * M * r := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hsig (by positivity)
    linarith [h1, h2]
  -- combine : LHS ≤ 102Q + 54MQ·Z₀ + 108MQ·r + 54MQ + 198M·r
  have hLHS1 : 3 * (12 * M / ‖1 - ρ‖ + 2 * (9 + 8 * ‖ρ‖) + 2 * (Z₀ + 1 / ‖1 - ρ‖) * P + 2 * P
        + 2 * P / (1 - ρ.re)) + 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re))
      ≤ 102 * Q + 54 * (M * Q) * Z₀ + 108 * ((M * Q) * r) + 54 * (M * Q) + 198 * (M * r) := by
    nlinarith [hA, hB', hC, hD, hE, hExtra]
  -- fold 1 : ≤ (102Q + 54MQZ₀ + 162MQ + 198M)·r
  have hfold1 : 102 * Q + 54 * (M * Q) * Z₀ + 108 * ((M * Q) * r) + 54 * (M * Q) + 198 * (M * r)
      ≤ (102 * Q + 54 * (M * Q) * Z₀ + 162 * (M * Q) + 198 * M) * r := by
    nlinarith [mul_nonneg hQ0.le (by linarith : (0 : ℝ) ≤ r - 1),
      mul_nonneg (mul_nonneg hMQnn hZ0) (by linarith : (0 : ℝ) ≤ r - 1),
      mul_nonneg hMQnn (by linarith : (0 : ℝ) ≤ r - 1)]
  -- fold 2 : the coefficient collapses onto `B₂ = Q^{5/2}L₂`
  have hQ52 : Q ^ (5 / 2 : ℝ) = Q * Q * Q ^ (1 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 1 + 1 + 1 / 2 by norm_num, Real.rpow_add hQ0, Real.rpow_add hQ0,
      Real.rpow_one]
  set B₂ : ℝ := Q ^ (5 / 2 : ℝ) * L₂ with hB2def
  have hB2eq : B₂ = Q * Q * B := by rw [hB2def, hBdef, hQ52]; ring
  have hMQQ : M * Q * Q ≤ B₂ := by
    rw [hB2eq]; nlinarith [hMQ, hQ0.le, mul_nonneg hQ0.le hQ0.le]
  have hMQle : M * Q ≤ B₂ := by nlinarith [hMQQ, mul_nonneg hMQnn (by linarith : (0 : ℝ) ≤ Q - 1)]
  have hMle : M ≤ B₂ := by nlinarith [hMQle, mul_nonneg hMnn (by linarith : (0 : ℝ) ≤ Q - 1)]
  have hQle : Q ≤ B₂ := by
    rw [hB2eq]; nlinarith [hBnn, hBpos, hQ0.le, mul_nonneg hQ0.le hQ0.le]
  have hZterm : 54 * (M * Q) * Z₀ ≤ 108 * B₂ := by
    have h1 : 54 * (M * Q) * Z₀ ≤ 54 * (M * Q) * (2 * Q) :=
      mul_le_mul_of_nonneg_left hZ0Q (by positivity)
    nlinarith [hMQQ, h1]
  have hfold2 : 102 * Q + 54 * (M * Q) * Z₀ + 162 * (M * Q) + 198 * M ≤ 570 * B₂ := by
    have hB2nn : (0 : ℝ) ≤ B₂ := by rw [hB2eq]; positivity
    linarith [hZterm, hQle, hMQle, hMle, hB2nn]
  have hfold2r : (102 * Q + 54 * (M * Q) * Z₀ + 162 * (M * Q) + 198 * M) * r ≤ 570 * B₂ * r :=
    mul_le_mul_of_nonneg_right hfold2 hrnn
  -- final identity
  have hL2sq : L₂ ^ (2 : ℝ) = L₂ * L₂ := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have hfinaleq : 570 * B₂ * r = 570 * (Q ^ (5 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀) := by
    rw [hB2def, hrdef, hL2sq]; field_simp
  linarith [hLHS1, hfold1, hfold2r, hfinaleq ▸ le_refl (570 * B₂ * r)]

set_option maxHeartbeats 1600000 in
-- The four-factor monomial collection (`← Real.rpow_add` groups + `ring`) plus the nested
-- `nlinarith` window checks exceed the default budget (as in `dh_master_ray`).
/-- **The Eρ-row cap, TALL.** `Eρ = Cρ·z·(1+log z²)^9·Y^{1/2−σ} ≤ 1/8` on the ray, where the
extraction constant `Cρ` (`= C2Rho q Z₀ ρ`) obeys the TALL bound `Cρ ≤ 570·Q^{5/2}·L₂²/c₀`
(`C2Rho_le_tall`).

This is `row_Eρ_cap` with the two extra `Q`-powers of the tall re-pricing threaded through. They
land in the monomial exponent, `α = 1/2 + 12 + 104(1/2−σ) ⇝ 5/2 + 12 + 104(1/2−σ)`, and the
exponent-balance hypothesis of `ray_pow_bound` (`α ≤ 680wγ`) is unmoved by them: on the window
`σ ≥ 16/17` the `−104(σ−1/2) ≈ −52` term dominates, so `α < 0 < 680wγ` with room to spare — this
is the `b = 680` vs `104`-spent slack the ⟦TAU-EXT⟧ scope doc priced. The payoff is that the
threshold `hg` no longer mentions `Z₀`, so the repulsion constant `c` stays uniform. -/
lemma row_Eρ_cap_tall {Q L₂ c c₀ u w σ Y z Cρ : ℝ}
    (hQ4 : 4 ≤ Q) (hL2 : Real.log Q + 2 ≤ L₂) (hcc : 0 < c) (hc1 : c ≤ 1) (hc0 : 0 < c₀)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hwdef : w = 1 - σ) (hσlo : 16 / 17 ≤ σ) (hσ1 : σ < 1)
    (_hCρnn : 0 ≤ Cρ)
    (hCρ : Cρ ≤ 570 * (Q ^ (5 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀))
    (hz1 : 1 ≤ z) (hzhi : z ≤ 2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
    (hYlo : Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) ≤ Y)
    (huτ : u ≤ c * Q ^ (-(680 * w)) / L₂ ^ (14 : ℝ))
    (hg : 2 * 570 * 248 ^ 9 / c₀ * c ^ (5247 / 1700 : ℝ) ≤ 1 / 8) :
    Cρ * z * (1 + Real.log (z ^ 2)) ^ 9 * Y ^ (1 / 2 - σ) ≤ 1 / 8 := by
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hL2' : (1 : ℝ) ≤ L₂ := by linarith
  have hL0 : (0 : ℝ) < L₂ := by linarith
  have hw0 : 0 < w := by rw [hwdef]; linarith
  have hbaselo : (0 : ℝ) < Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by positivity
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le hbaselo hYlo
  have hzpos : (0 : ℝ) < z := by linarith
  have hpoly := logz_factor_pow9_le hQ4 hL2 hu0 hu1 hz1 hzhi
  have hYexp : (1 : ℝ) / 2 - σ < 0 := by linarith
  have hYb : Y ^ (1 / 2 - σ) ≤ Q ^ (104 * (1 / 2 - σ)) * u ^ (-(14 * (1 / 2 - σ))) := by
    have h1 : Y ^ (1 / 2 - σ) ≤ (Q ^ (104 : ℝ) * u ^ (-(14 : ℝ))) ^ (1 / 2 - σ) :=
      Real.rpow_le_rpow_of_nonpos hbaselo hYlo hYexp.le
    rwa [Real.mul_rpow (Real.rpow_nonneg hQ0.le _) (Real.rpow_nonneg hu0.le _),
      ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hu0.le,
      show -(14 : ℝ) * (1 / 2 - σ) = -(14 * (1 / 2 - σ)) by ring] at h1
  -- monomial collapse via ray_pow_bound (the tall `α` carries two extra `Q`-powers)
  have hγpos : (0 : ℝ) < -(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ)) := by nlinarith [hσlo]
  have hmono := ray_pow_bound (Q := Q) (L₂ := L₂) (c := c) (u := u) (w := w) (b := 680) (k := 14)
    (α := 5 / 2 + 12 + 104 * (1 / 2 - σ))
    (γ := -(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ)))
    (ε := 2 + 9) hQ1 hL2' hcc (by norm_num) (by norm_num) hu0 hγpos huτ
    (by nlinarith [hσlo, mul_pos hw0 hγpos]) (by nlinarith [hσlo])
  have hQg : Q ^ (5 / 2 : ℝ) * Q ^ (12 : ℝ) * Q ^ (104 * (1 / 2 - σ))
      = Q ^ (5 / 2 + 12 + 104 * (1 / 2 - σ)) := by
    rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
  have hug : u ^ (-(3 : ℝ)) * u ^ (-(9 / 100 : ℝ)) * u ^ (-(14 * (1 / 2 - σ)))
      = u ^ (-(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ))) := by
    rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]
  have hLg : L₂ ^ (2 : ℝ) * L₂ ^ (9 : ℝ) = L₂ ^ (2 + 9 : ℝ) := by rw [← Real.rpow_add hL0]
  have hcollect : (570 * (Q ^ (5 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀))
        * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
        * (248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ))
        * (Q ^ (104 * (1 / 2 - σ)) * u ^ (-(14 * (1 / 2 - σ))))
      = 2 * 570 * 248 ^ 9 / c₀
        * (Q ^ (5 / 2 + 12 + 104 * (1 / 2 - σ))
          * u ^ (-(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ)))
          * L₂ ^ (2 + 9 : ℝ)) := by
    rw [← hQg, ← hug, ← hLg]; ring
  -- nonneg facts and the product bound
  have hbnn : (0 : ℝ) ≤ 1 + Real.log (z ^ 2) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ z ^ 2 by nlinarith [hz1]); linarith
  have hpolynn : (0 : ℝ) ≤ (1 + Real.log (z ^ 2)) ^ 9 := pow_nonneg hbnn 9
  have hYsnn : (0 : ℝ) ≤ Y ^ (1 / 2 - σ) := Real.rpow_nonneg hYpos.le _
  have hCbarnn : (0 : ℝ) ≤ 570 * (Q ^ (5 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀) := by positivity
  have hzbarnn : (0 : ℝ) ≤ 2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) := by positivity
  have hPbarnn : (0 : ℝ) ≤ 248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ) := by positivity
  have hprod : Cρ * z * (1 + Real.log (z ^ 2)) ^ 9 * Y ^ (1 / 2 - σ)
      ≤ (570 * (Q ^ (5 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀))
          * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
          * (248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ))
          * (Q ^ (104 * (1 / 2 - σ)) * u ^ (-(14 * (1 / 2 - σ)))) := by
    have h1 : Cρ * z
        ≤ 570 * (Q ^ (5 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀)
          * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) :=
      mul_le_mul hCρ hzhi hzpos.le hCbarnn
    have h2 : Cρ * z * (1 + Real.log (z ^ 2)) ^ 9
        ≤ 570 * (Q ^ (5 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀)
          * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
          * (248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ)) :=
      mul_le_mul h1 hpoly hpolynn (mul_nonneg hCbarnn hzbarnn)
    exact mul_le_mul h2 hYb hYsnn (mul_nonneg (mul_nonneg hCbarnn hzbarnn) hPbarnn)
  have hCnn : (0 : ℝ) ≤ 2 * 570 * 248 ^ 9 / c₀ := by positivity
  -- TAU-SHARP S2: the Eρ row's **own** γ-floor (the forked twin of `TBalR8`'s `row_Eρ_cap`, same
  -- exponent, same floor).  `γ_Eρ(σ) = 14σ − 1009/100` is strictly increasing in `σ`, so its
  -- infimum over the window sits at the CLOSED endpoint `hσlo : 16/17 ≤ σ`, where it equals
  -- `5247/1700` EXACTLY (`14·16/17 − 1009/100 = 22400/1700 − 17153/1700`).  The freeze's decimal
  -- `3.0865` exceeds this by `2.941e−5` and is FALSE at the endpoint — the rational is the only
  -- admissible numeral, and substituting `3.0865` here is the wave's mutation control (it must,
  -- and does, break the build).  `linarith` (not `nlinarith`): linear in `σ`, tight at equality.
  have hcγ : c ^ (-(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ))) ≤ c ^ (5247 / 1700 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hcc hc1 (by linarith [hσlo])
  calc Cρ * z * (1 + Real.log (z ^ 2)) ^ 9 * Y ^ (1 / 2 - σ)
      ≤ (570 * (Q ^ (5 / 2 : ℝ) * L₂ ^ (2 : ℝ)) * (1 / c₀))
          * (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)))
          * (248 ^ 9 * u ^ (-(9 / 100 : ℝ)) * L₂ ^ (9 : ℝ))
          * (Q ^ (104 * (1 / 2 - σ)) * u ^ (-(14 * (1 / 2 - σ)))) := hprod
    _ = 2 * 570 * 248 ^ 9 / c₀
        * (Q ^ (5 / 2 + 12 + 104 * (1 / 2 - σ))
          * u ^ (-(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ)))
          * L₂ ^ (2 + 9 : ℝ)) := hcollect
    _ ≤ 2 * 570 * 248 ^ 9 / c₀
        * c ^ (-(3 : ℝ) + -(9 / 100 : ℝ) + -(14 * (1 / 2 - σ))) :=
        mul_le_mul_of_nonneg_left hmono hCnn
    _ ≤ 2 * 570 * 248 ^ 9 / c₀ * c ^ (5247 / 1700 : ℝ) :=
        mul_le_mul_of_nonneg_left hcγ hCnn
    _ ≤ 1 / 8 := hg

/-- ceil bounds: `x ≤ ⌈x⌉ ≤ 2x` for `x ≥ 1` (verbatim copy of `TBalR8`'s `private`). -/
private lemma ceil_dbl {x : ℝ} (hx : 1 ≤ x) : x ≤ (⌈x⌉₊ : ℝ) ∧ (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  refine ⟨Nat.le_ceil x, ?_⟩
  have h1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  linarith

set_option maxHeartbeats 3200000 in
-- The per-instance assembly threads the 5 row caps + 6 guard discharges through the tall master;
-- the accumulated `rpow`/`nlinarith` elaboration exceeds the default budget.
/-- The per-instance body of `dh_repulsion_tall` (light context: `c` opaque, all `c`-thresholds
as hypotheses). -/
private lemma dh_repulsion_inst_tall {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (_hχ1 : χ ≠ 1) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q)
    {β₀ : ℝ} (hβ0zero : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0)
    (hβ0lo : 1 / 2 < β₀) (hβ0hi : β₀ < 1)
    {ρ : ℂ} (hρzero : DirichletCharacter.LFunction χ ρ = 0) (hρim : ρ.im ≠ 0)
    {H : ℝ} (himρ : |ρ.im| ≤ H) (hσlo : 16 / 17 ≤ ρ.re) (hσ1 : ρ.re < 1) (hord : ρ.re ≤ β₀)
    {c₀ Zρ c : ℝ}
    (hZρ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ H → ‖zetaHol s‖ ≤ Zρ)
    (hc₀pos : 0 < c₀) (hc₀le1 : c₀ ≤ 1) (hZ0nn : 0 ≤ Zρ)
    (hZ0Q : Zρ ≤ 2 * ((q : ℝ) * (|ρ.im| + 2)))
    (hfloor : ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)))
    (hcpos : 0 < c) (hc1 : c ≤ 1) (hc_t1 : c ≤ 1 / 40)
    (hc_t2 : c ≤ (c₀ / 32) ^ (17 / 3 : ℝ))
    (hc_t3 : c ≤ (1 / 805 : ℝ) ^ (50 / 49 : ℝ))
    (hc_t4 : c ≤ (1 / (8 * 1610 * Real.exp 1)) ^ (850 / 133 : ℝ)) (hc_t5 : c ≤ 1 / 2)
    (hc_t6 : c ≤ (1 / (16 * (328 + 48 * 5) * 248 ^ 9)) ^ (1700 / 3547 : ℝ))
    (hc_t7 : c ≤ (c₀ / (16 * 570 * 248 ^ 9)) ^ (1700 / 5247 : ℝ))
    (hc_t8 : c ≤ 1 / (3 * (Real.log 2 + 4 * Real.log (256 * (82 + 12 * 5)))))
    (hc_t9 : c ≤ 1 / 18) (hc_t10 : c ≤ 1 / 576) :
    (1 - β₀) ≥ c * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(680 * (1 - ρ.re)))
      / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ (14 : ℝ) := by
  set Q : ℝ := (q : ℝ) * (|ρ.im| + 2) with hQdef
  set L₂ : ℝ := Real.log Q + 2 with hL₂def
  set u : ℝ := 1 - β₀ with hudef
  set σ : ℝ := ρ.re with hσdef
  set w : ℝ := 1 - σ with hwdef
  set M : ℝ := Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) with hMdef
  have hu0 : 0 < u := by rw [hudef]; linarith only [hβ0hi]
  have hu_half : u ≤ 1 / 2 := by rw [hudef]; linarith only [hβ0lo]
  have hu1 : u ≤ 1 := by linarith only [hu_half]
  have huβ : 1 - β₀ = u := hudef.symm
  have hσlo' : 16 / 17 ≤ σ := hσlo
  have hσ1' : σ < 1 := hσ1
  have hσβ : σ ≤ β₀ := hord
  have hw0 : 0 < w := by rw [hwdef]; linarith only [hσ1']
  have hwle : w ≤ 1 / 17 := by rw [hwdef]; linarith only [hσlo']
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQ4 : 4 ≤ Q := by rw [hQdef]; nlinarith only [hqR, abs_nonneg ρ.im]
  have hQ0 : 0 < Q := by linarith only [hQ4]
  have hQ1 : (1 : ℝ) ≤ Q := by linarith only [hQ4]
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hlogQpos : 0 < Real.log Q := Real.log_pos (by linarith only [hQ4])
  have hL₂ge2 : (2 : ℝ) ≤ L₂ := by rw [hL₂def]; linarith only [hlogQ0]
  have hL₂1 : (1 : ℝ) ≤ L₂ := by linarith only [hL₂ge2]
  have hL₂pos : (0 : ℝ) < L₂ := by linarith only [hL₂ge2]
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hβ0 : 0 ≤ β₀ := by linarith only [hβ0lo]
  -- the β₀ side keeps the UNIT-box packaging with the numeral `5` (`zetaHol_bound_five`):
  -- its `hZ` is only ever read at the REAL point `β₀`, so it need not share the ρ-side constant.
  have hZβ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ 5 :=
    zetaHol_bound_five
  rw [ge_iff_le]
  by_cases htriv : 1 / (40 * L₂) ≤ u
  · -- trivial branch (TAU-SHARP S1: the generalised split takes `c` itself, via `c ≤ 1/40 ≤ 1`)
    have hsplit := tbal_tau_le_split (c := c) hQ1 hw0 hcpos.le (le_trans hc_t1 (by norm_num))
    rw [← hL₂def] at hsplit
    linarith only [hsplit, htriv]
  · -- deep branch
    rw [not_le] at htriv
    by_contra hcon
    rw [not_le] at hcon
    have huτ : u ≤ c * Q ^ (-(680 * w)) / L₂ ^ (14 : ℝ) := le_of_lt hcon
    -- ray facts
    have hQpow_le1 : Q ^ (-(680 * w)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by nlinarith only [hw0])
    have hL14pos : (0 : ℝ) < L₂ ^ (14 : ℝ) := Real.rpow_pos_of_pos hL₂pos _
    have hL14ge1 : (1 : ℝ) ≤ L₂ ^ (14 : ℝ) := Real.one_le_rpow hL₂1 (by norm_num)
    have hL2leL14 : L₂ ≤ L₂ ^ (14 : ℝ) := by
      calc L₂ = L₂ ^ (1 : ℝ) := (Real.rpow_one L₂).symm
        _ ≤ L₂ ^ (14 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL₂1 (by norm_num)
    have huL14c : u * L₂ ^ (14 : ℝ) ≤ c := by
      have h1 := mul_le_mul_of_nonneg_right huτ hL14pos.le
      rw [div_mul_cancel₀ _ hL14pos.ne'] at h1
      nlinarith only [h1, hQpow_le1, hcpos.le]
    have hu_le_c : u ≤ c := by
      nlinarith only [huL14c, mul_nonneg hu0.le (show (0 : ℝ) ≤ L₂ ^ (14 : ℝ) - 1 by linarith)]
    have huL2c : u * L₂ ≤ c :=
      le_trans (by nlinarith only [mul_le_mul_of_nonneg_left hL2leL14 hu0.le]) huL14c
    -- guard thresholds
    have hZray : (5 : ℝ) * u ≤ 1 := by
      have h10 : u ≤ 1 / 576 := le_trans hu_le_c hc_t10
      linarith only [h10]
    have huA : u * (Real.log 2 + 4 * Real.log (256 * (82 + 12 * 5))) ≤ 1 / 3 := by
      set A : ℝ := Real.log 2 + 4 * Real.log (256 * (82 + 12 * 5)) with hAdef
      have hApos : (0 : ℝ) < 3 * A := by
        rw [hAdef]
        have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have h2 : 0 ≤ Real.log (256 * (82 + 12 * 5)) := Real.log_nonneg (by norm_num)
        linarith only [h1, h2]
      have h8 : u ≤ 1 / (3 * A) := le_trans hu_le_c hc_t8
      rw [le_div_iff₀ hApos] at h8
      linarith only [h8]
    have huL2g : u * L₂ ≤ 1 / 18 := le_trans huL2c hc_t9
    have hsqrtg : Real.sqrt u ≤ 1 / 24 := by
      have h10 : u ≤ 1 / 576 := le_trans hu_le_c hc_t10
      calc Real.sqrt u ≤ Real.sqrt (1 / 576) := Real.sqrt_le_sqrt h10
        _ = 1 / 24 := by
            rw [show (1 / 576 : ℝ) = (1 / 24) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    -- scales
    set z : ℕ := ⌈Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))⌉₊ with hzdef
    set Y : ℕ := ⌈Q ^ (104 : ℝ) * u ^ (-(14 : ℝ))⌉₊ with hYdef
    set G : ℝ := 34 + 12 * M + 12 * M * 5 + 36 * M / (1 - β₀) with hGdef
    set N : ℕ := ⌈(256 * G) ^ (4 : ℝ)⌉₊ with hNdef
    have hzarg1 : (1 : ℝ) ≤ Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) := by
      have h1 : (1 : ℝ) ≤ Q ^ (12 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
      have h2 : (1 : ℝ) ≤ u ^ (-(3 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
      nlinarith only [h1, h2]
    have hYarg1 : (1 : ℝ) ≤ Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by
      have h1 : (1 : ℝ) ≤ Q ^ (104 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
      have h2 : (1 : ℝ) ≤ u ^ (-(14 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
      nlinarith only [h1, h2]
    have hGdiv : (0 : ℝ) ≤ 36 * M / (1 - β₀) :=
      div_nonneg (mul_nonneg (by norm_num) hMnn) (by linarith)
    have hG34 : 34 ≤ G := by rw [hGdef]; nlinarith only [hMnn, hGdiv]
    have hNarg1 : (1 : ℝ) ≤ (256 * G) ^ (4 : ℝ) :=
      Real.one_le_rpow (by nlinarith only [hG34]) (by norm_num)
    have hzlo_r : Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) ≤ (z : ℝ) := by
      rw [hzdef]; exact (ceil_dbl hzarg1).1
    have hzhi_r : (z : ℝ) ≤ 2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) := by
      rw [hzdef, mul_assoc]; exact (ceil_dbl hzarg1).2
    have hYlo_r : Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) ≤ (Y : ℝ) := by
      rw [hYdef]; exact (ceil_dbl hYarg1).1
    have hYhi_r : (Y : ℝ) ≤ 2 * Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by
      rw [hYdef, mul_assoc]; exact (ceil_dbl hYarg1).2
    have h4eq : (256 * G) ^ (4 : ℝ) = (256 * G) ^ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hNlo_r : (256 * G) ^ (4 : ℝ) ≤ (N : ℝ) := by rw [hNdef]; exact (ceil_dbl hNarg1).1
    have hNhi_npow : (N : ℝ) ≤ 2 * (256 * G) ^ 4 := by
      rw [← h4eq, hNdef]; exact (ceil_dbl hNarg1).2
    have hQ12ge4 : (4 : ℝ) ≤ Q ^ (12 : ℝ) := by
      calc (4 : ℝ) ≤ Q := hQ4
        _ = Q ^ (1 : ℝ) := (Real.rpow_one Q).symm
        _ ≤ Q ^ (12 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
    have hu3ge1 : (1 : ℝ) ≤ u ^ (-(3 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
    have hz2 : 2 ≤ z := by
      have hge : (2 : ℝ) ≤ Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) := by
        nlinarith only [hQ12ge4, mul_nonneg (Real.rpow_pos_of_pos hQ0 (12 : ℝ)).le
          (show (0 : ℝ) ≤ u ^ (-(3 : ℝ)) - 1 by linarith only [hu3ge1])]
      have : (2 : ℝ) ≤ (z : ℝ) := le_trans hge hzlo_r
      exact_mod_cast this
    have hQ104ge4 : (4 : ℝ) ≤ Q ^ (104 : ℝ) := by
      calc (4 : ℝ) ≤ Q := hQ4
        _ = Q ^ (1 : ℝ) := (Real.rpow_one Q).symm
        _ ≤ Q ^ (104 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
    have hu14ge1 : (1 : ℝ) ≤ u ^ (-(14 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
    have hY4 : 4 ≤ Y := by
      have hge : (4 : ℝ) ≤ Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by
        nlinarith only [hQ104ge4, mul_nonneg (Real.rpow_pos_of_pos hQ0 (104 : ℝ)).le
          (show (0 : ℝ) ≤ u ^ (-(14 : ℝ)) - 1 by linarith only [hu14ge1])]
      have : (4 : ℝ) ≤ (Y : ℝ) := le_trans hge hYlo_r
      exact_mod_cast this
    have h256G1 : (1 : ℝ) ≤ 256 * G := by nlinarith only [hG34]
    have hN4 : 4 ≤ N := by
      have hge : (4 : ℝ) ≤ (256 * G) ^ (4 : ℝ) := by
        calc (4 : ℝ) ≤ 256 * G := by nlinarith only [hG34]
          _ = (256 * G) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (256 * G) ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le h256G1 (by norm_num)
      have : (4 : ℝ) ≤ (N : ℝ) := le_trans hge hNlo_r
      exact_mod_cast this
    -- ===== derived facts =====
    have hqQ : (q : ℝ) ≤ Q := by rw [hQdef]; nlinarith only [hqR, abs_nonneg ρ.im]
    have hsqrtqQ : Real.sqrt (q : ℝ) ≤ Q ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt hqQ
    have hlogqL2 : 1 + Real.log (q : ℝ) ≤ L₂ := by
      rw [hL₂def]
      have hll : Real.log (q : ℝ) ≤ Real.log Q := Real.log_le_log (by positivity) hqQ
      linarith only [hll]
    have hMB : M ≤ Q ^ (1 / 2 : ℝ) * L₂ := by
      rw [hMdef]; exact mul_le_mul hsqrtqQ hlogqL2 (by positivity) (by positivity)
    have hsq1 : (1 : ℝ) ≤ Q ^ (1 / 2 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
    have hB1 : (1 : ℝ) ≤ Q ^ (1 / 2 : ℝ) * L₂ := by nlinarith only [hsq1, hL₂1]
    have hQsqsq : Q ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) = Q := by rw [← Real.rpow_add hQ0]; norm_num
    have hlogQ2 : Real.log Q ≤ 2 * Q ^ (1 / 2 : ℝ) := by
      have h := Real.log_le_rpow_div hQ0.le (show (0 : ℝ) < 1 / 2 by norm_num)
      linarith only [h, show Q ^ (1 / 2 : ℝ) / (1 / 2) = 2 * Q ^ (1 / 2 : ℝ) by ring]
    have hM4Q : M ≤ 4 * Q := by
      have hL2le : L₂ ≤ 4 * Q ^ (1 / 2 : ℝ) := by rw [hL₂def]; linarith only [hlogQ2, hsq1]
      calc M ≤ Q ^ (1 / 2 : ℝ) * L₂ := hMB
        _ ≤ Q ^ (1 / 2 : ℝ) * (4 * Q ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hL2le (by positivity)
        _ = 4 * Q := by
            rw [show Q ^ (1 / 2 : ℝ) * (4 * Q ^ (1 / 2 : ℝ))
              = 4 * (Q ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ)) by ring, hQsqsq]
    have hlnB : Real.log (Q ^ (1 / 2 : ℝ) * L₂) ≤ 3 / 2 * L₂ := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hQ0]
      have hL2log : Real.log L₂ ≤ L₂ := by
        have := Real.log_le_sub_one_of_pos hL₂pos; linarith only [this]
      have hlogQL2 : Real.log Q ≤ L₂ := by rw [hL₂def]; linarith only [hlogQ0]
      linarith only [hL2log, hlogQL2]
    have hLc : (1 : ℝ) ≤ L₂ / c₀ := by
      rw [le_div_iff₀ hc₀pos]; nlinarith only [hL₂ge2, hc₀le1]
    -- ZFR floors
    have hn1re : (1 - ρ).re = w := by rw [Complex.sub_re, Complex.one_re, ← hσdef, ← hwdef]
    have hn1 : w ≤ ‖1 - ρ‖ := by
      have h := Complex.abs_re_le_norm (1 - ρ)
      rw [hn1re, abs_of_pos hw0] at h; exact h
    have hnpos : 0 < ‖1 - ρ‖ := lt_of_lt_of_le hw0 hn1
    have hn2re : (2 - ρ).re = 2 - σ := by rw [Complex.sub_re, Complex.re_ofNat, ← hσdef]
    have hn2 : (1 : ℝ) ≤ ‖2 - ρ‖ := by
      have h := Complex.abs_re_le_norm (2 - ρ)
      rw [hn2re, abs_of_pos (by linarith only [hσ1'])] at h; linarith only [h, hσ1']
    have hwZFR : c₀ / Real.log Q ≤ w := by
      rw [hwdef, hσdef]; linarith only [hfloor]
    have hlogQL2' : Real.log Q ≤ L₂ := by rw [hL₂def]; linarith only [hlogQ0]
    have hinvw : 1 / w ≤ L₂ / c₀ := by
      have h2 : 1 / w ≤ Real.log Q / c₀ := by
        rw [div_le_div_iff₀ hw0 hc₀pos]
        have hwZFR' : c₀ ≤ w * Real.log Q := by
          rw [div_le_iff₀ hlogQpos] at hwZFR; linarith only [hwZFR]
        nlinarith only [hwZFR']
      have h3 : Real.log Q / c₀ ≤ L₂ / c₀ := by gcongr
      linarith only [h2, h3]
    have hn1inv : 1 / ‖1 - ρ‖ ≤ L₂ / c₀ :=
      le_trans (one_div_le_one_div_of_le hw0 hn1) hinvw
    have hsig : 1 / (1 - ρ.re) ≤ L₂ / c₀ := by
      rw [show 1 - ρ.re = w by rw [← hσdef, ← hwdef]]; exact hinvw
    have hρQ : ‖ρ‖ ≤ Q := by
      have h := Complex.norm_le_abs_re_add_abs_im ρ
      rw [abs_of_pos (by linarith only [hσlo] : (0 : ℝ) < ρ.re)] at h
      rw [hQdef]
      nlinarith only [h, hσ1, hqR, abs_nonneg ρ.im]
    have hCρ := C2Rho_le_tall hσlo hσ1 hQ1 hρQ hZ0nn hZ0Q hc₀pos hLc hL₂1 hMB hMnn hB1 hn1inv hsig
      hnpos
    -- ===== 2 z^4 ≤ Y  and  ⌈1/(1-β₀)⌉ ≤ z =====
    have hexp4 : (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) ^ 4 = 16 * Q ^ (48 : ℝ) * u ^ (-(12 : ℝ)) := by
      rw [mul_pow, mul_pow, ← Real.rpow_natCast (Q ^ (12 : ℝ)) 4, ← Real.rpow_mul hQ0.le,
        ← Real.rpow_natCast (u ^ (-(3 : ℝ))) 4, ← Real.rpow_mul hu0.le]
      push_cast; ring_nf
    have hQ56ge : (32 : ℝ) ≤ Q ^ (56 : ℝ) * u ^ (-(2 : ℝ)) := by
      have hQ3 : (64 : ℝ) ≤ Q ^ (56 : ℝ) := by
        have h1 : (4 : ℝ) ^ (3 : ℝ) ≤ Q ^ (3 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hQ4 (by norm_num)
        have h2 : Q ^ (3 : ℝ) ≤ Q ^ (56 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
        rw [show (4 : ℝ) ^ (3 : ℝ) = 64 from by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num] at h1
        linarith only [h1, h2]
      have hu2 : (1 : ℝ) ≤ u ^ (-(2 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by norm_num)
      nlinarith only [hQ3, hu2, Real.rpow_pos_of_pos hQ0 (56 : ℝ)]
    have hfactor : Q ^ (104 : ℝ) * u ^ (-(14 : ℝ))
        = (Q ^ (56 : ℝ) * u ^ (-(2 : ℝ))) * (Q ^ (48 : ℝ) * u ^ (-(12 : ℝ))) := by
      rw [show (Q ^ (56 : ℝ) * u ^ (-(2 : ℝ))) * (Q ^ (48 : ℝ) * u ^ (-(12 : ℝ)))
          = (Q ^ (56 : ℝ) * Q ^ (48 : ℝ)) * (u ^ (-(2 : ℝ)) * u ^ (-(12 : ℝ))) by ring,
        ← Real.rpow_add hQ0, ← Real.rpow_add hu0]; norm_num
    have hY_nat : 2 * z ^ 4 ≤ Y := by
      have hzr4 : (z : ℝ) ^ 4 ≤ (2 * Q ^ (12 : ℝ) * u ^ (-(3 : ℝ))) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hzhi_r 4
      have hQ48pos : (0 : ℝ) ≤ Q ^ (48 : ℝ) * u ^ (-(12 : ℝ)) := by positivity
      have hchain : 2 * (z : ℝ) ^ 4 ≤ (Y : ℝ) := by
        calc 2 * (z : ℝ) ^ 4 ≤ 2 * (16 * Q ^ (48 : ℝ) * u ^ (-(12 : ℝ))) := by
              rw [← hexp4]; linarith only [hzr4]
          _ = 32 * (Q ^ (48 : ℝ) * u ^ (-(12 : ℝ))) := by ring
          _ ≤ (Q ^ (56 : ℝ) * u ^ (-(2 : ℝ))) * (Q ^ (48 : ℝ) * u ^ (-(12 : ℝ))) :=
              mul_le_mul_of_nonneg_right hQ56ge hQ48pos
          _ = Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := hfactor.symm
          _ ≤ (Y : ℝ) := hYlo_r
      have : (2 * z ^ 4 : ℕ) ≤ ((Y : ℕ) : ℝ) := by push_cast; linarith only [hchain]
      exact_mod_cast this
    have hcue : ⌈(1 : ℝ) / (1 - β₀)⌉₊ ≤ z := by
      have h1u : (1 : ℝ) / (1 - β₀) = 1 / u := by rw [huβ]
      have hceil : (⌈(1 : ℝ) / (1 - β₀)⌉₊ : ℝ) ≤ 1 / u + 1 := by
        rw [h1u]; exact (Nat.ceil_lt_add_one (by positivity)).le
      have h2u : 1 / u + 1 ≤ 2 * (1 / u) := by
        have : (1 : ℝ) ≤ 1 / u := by rw [le_div_iff₀ hu0]; linarith only [hu1]
        linarith only [this]
      have hu32 : u ^ (-(3 : ℝ)) * u = u ^ (-(2 : ℝ)) := by
        rw [show (-(3 : ℝ)) = -(2 : ℝ) + -(1 : ℝ) by norm_num, Real.rpow_add hu0]
        rw [show u ^ (-(2 : ℝ)) * u ^ (-(1 : ℝ)) * u
            = u ^ (-(2 : ℝ)) * (u ^ (-(1 : ℝ)) * u) by ring,
          show u ^ (-(1 : ℝ)) * u = 1 by rw [Real.rpow_neg_one, inv_mul_cancel₀ hu0.ne'], mul_one]
      have hu2ge : (2 : ℝ) ≤ Q ^ (12 : ℝ) * u ^ (-(2 : ℝ)) := by
        nlinarith only [hQ12ge4,
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (show -(2 : ℝ) ≤ 0 by norm_num),
          Real.rpow_pos_of_pos hQ0 (12 : ℝ)]
      have hzge : 2 * (1 / u) ≤ Q ^ (12 : ℝ) * u ^ (-(3 : ℝ)) := by
        rw [mul_one_div, div_le_iff₀ hu0, mul_assoc, hu32]; exact hu2ge
      have : (⌈(1 : ℝ) / (1 - β₀)⌉₊ : ℝ) ≤ (z : ℝ) := by
        linarith only [hceil, h2u, hzge, hzlo_r]
      exact_mod_cast this
    -- ===== guards + master =====
    have hGu : G = 34 + 12 * M + 12 * M * 5 + 36 * M / u := by rw [hGdef, huβ]
    have hNpos_r : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hscale := tbal_hscale (Z₀ := 5) hu0 hu1 huβ hMnn hMB hB1 (by norm_num) hL₂1 hlnB hGu
      hNhi_npow hNpos_r huA huL2g hsqrtg
    have hguard := tbal_hguard hG34 hNlo_r hscale
    have hcov := tbal_hcov (Z₀ := 5) (by norm_num) (le_of_lt hβ0lo) hβ0hi huβ hQ4 hM4Q hMnn hz2
      hzlo_r hzhi_r hcue hZray
    have hmaster := dh_master_ray_tall χ hχ hsq hq hβ0zero (le_of_lt hβ0lo) hβ0hi hρzero
      (by linarith only [hσlo] : 1 / 2 ≤ ρ.re) hσ1 himρ hord hZρ hZβ hN4 hscale hguard hz2 hY_nat
      hcov
    rw [← hMdef] at hmaster
    -- ===== row hg's from the c-thresholds =====
    have hcollapse : ∀ X pinv p : ℝ, 0 ≤ X → 0 < p → c ≤ X ^ pinv → pinv * p = 1 → c ^ p ≤ X := by
      intro X pinv p hX hp hcX hpp
      calc c ^ p ≤ (X ^ pinv) ^ p := Real.rpow_le_rpow hcpos.le hcX hp.le
        _ = X ^ (pinv * p) := (Real.rpow_mul hX pinv p).symm
        _ = X := by rw [hpp, Real.rpow_one]
    have hgρ : 4 / c₀ * c ^ (3 / 17 : ℝ) ≤ 1 / 8 := by
      have hp : c ^ (3 / 17 : ℝ) ≤ c₀ / 32 :=
        hcollapse (c₀ / 32) (17 / 3) (3 / 17) (by positivity) (by norm_num) hc_t2 (by norm_num)
      have heq : 4 / c₀ * (c₀ / 32) = 1 / 8 := by field_simp; ring
      nlinarith only [mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 4 / c₀ by positivity), heq]
    have hg1A : 805 * c ^ (49 / 50 : ℝ) ≤ 1 := by
      have hp : c ^ (49 / 50 : ℝ) ≤ 1 / 805 :=
        hcollapse (1 / 805) (50 / 49) (49 / 50) (by norm_num) (by norm_num) hc_t3 (by norm_num)
      nlinarith only [mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 805 by norm_num)]
    have hg2A : 1610 * Real.exp 1 * c ^ (133 / 850 : ℝ) ≤ 1 / 8 := by
      have hp : c ^ (133 / 850 : ℝ) ≤ 1 / (8 * 1610 * Real.exp 1) :=
        hcollapse (1 / (8 * 1610 * Real.exp 1)) (850 / 133) (133 / 850) (by positivity)
          (by norm_num) hc_t4 (by norm_num)
      have hepos : 0 < Real.exp 1 := Real.exp_pos 1
      have heq : 1610 * Real.exp 1 * (1 / (8 * 1610 * Real.exp 1)) = 1 / 8 := by field_simp
      nlinarith only
        [mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 1610 * Real.exp 1 by positivity), heq]
    have hg1x : c ≤ 1 / 2 := hc_t5
    have hgEβ : 2 * (328 + 48 * 5) * 248 ^ 9 * c ^ (3547 / 1700 : ℝ) ≤ 1 / 8 := by
      have hp : c ^ (3547 / 1700 : ℝ) ≤ 1 / (16 * (328 + 48 * 5) * 248 ^ 9) :=
        hcollapse (1 / (16 * (328 + 48 * 5) * 248 ^ 9)) (1700 / 3547) (3547 / 1700)
          (by positivity) (by norm_num)
          hc_t6
          (by norm_num)
      have heq : 2 * (328 + 48 * 5) * 248 ^ 9 * (1 / (16 * (328 + 48 * 5) * 248 ^ 9))
          = 1 / 8 := by
        norm_num
      nlinarith only [mul_le_mul_of_nonneg_left hp
        (show (0 : ℝ) ≤ 2 * (328 + 48 * 5) * 248 ^ 9 by positivity), heq]
    have hgEρ : 2 * 570 * 248 ^ 9 / c₀ * c ^ (5247 / 1700 : ℝ) ≤ 1 / 8 := by
      have hp : c ^ (5247 / 1700 : ℝ) ≤ c₀ / (16 * 570 * 248 ^ 9) :=
        hcollapse (c₀ / (16 * 570 * 248 ^ 9)) (1700 / 5247) (5247 / 1700)
          (by positivity) (by norm_num)
          hc_t7
          (by norm_num)
      have heq : 2 * 570 * 248 ^ 9 / c₀ * (c₀ / (16 * 570 * 248 ^ 9)) = 1 / 8 := by
        field_simp; ring
      nlinarith only [mul_le_mul_of_nonneg_left hp
        (show (0 : ℝ) ≤ 2 * 570 * 248 ^ 9 / c₀ by positivity), heq]
    -- ===== derived shapes + row caps =====
    have hlogL2 : Real.log Q + 2 ≤ L₂ := le_of_eq hL₂def.symm
    have hMB' : M ≤ Real.sqrt Q * L₂ := by rw [Real.sqrt_eq_rpow]; exact hMB
    have hYpos : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (show 0 < Y by omega)
    have hz1r : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show 1 ≤ z by omega)
    have hrow1 : (1 - β₀) * (2 - β₀) * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖) ≤ 1 / 8 :=
      row_rho_main_cap (Q := Q) (L₂ := L₂) (c := c) (c₀ := c₀) (u := 1 - β₀) (w := 1 - ρ.re)
        (σ := ρ.re) (β₀ := β₀) (Y := Y) (n1 := ‖1 - ρ‖) (n2 := ‖2 - ρ‖)
        hQ4 hL₂1 hcpos hc1 hc₀pos hu0 rfl hσlo hσ1 hβ0 hβ0hi hn2 hn1inv hYlo_r hYhi_r huτ hgρ
    have hσ0 : 0 < ρ.re := by linarith only [hσlo]
    have hCρnn : 0 ≤ C2Rho q Zρ ρ := by
      rw [C2Rho, CwRho]
      have h1 : (0 : ℝ) ≤ ‖ρ‖ / ρ.re := div_nonneg (norm_nonneg _) hσ0.le
      positivity
    have hrow2 : C2Rho q Zρ ρ * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9
        * (Y : ℝ) ^ (1 / 2 - ρ.re) ≤ 1 / 8 :=
      row_Eρ_cap_tall (Q := Q) (L₂ := L₂) (c := c) (c₀ := c₀) (u := 1 - β₀) (w := 1 - ρ.re)
        (σ := ρ.re) (Y := Y) (z := (z : ℝ)) (Cρ := C2Rho q Zρ ρ) hQ4 hlogL2 hcpos hc1 hc₀pos hu0
        hu1 rfl hσlo hσ1 hCρnn hCρ hz1r hzhi_r hYlo_r huτ hgEρ
    have hrowA : (Y : ℝ) ^ (β₀ - ρ.re) * ((Y : ℝ) ^ (1 - β₀) - 1) ≤ 1 / 8 :=
      row_A_cap (Q := Q) (L₂ := L₂) (c := c) (u := 1 - β₀) (w := 1 - ρ.re) (σ := ρ.re) (β₀ := β₀)
        (Y := Y) hQ4 hlogL2 hcpos hc1 hu0 hu1 rfl hσlo hσ1 hσβ hβ0hi rfl hYlo_r hYhi_r huτ hg1A hg2A
    have hrow1x : (Y : ℝ) ^ (β₀ - ρ.re - 1) ≤ 1 / 8 :=
      row_1x_cap (Q := Q) (L₂ := L₂) (c := c) (u := 1 - β₀) (w := 1 - ρ.re) (σ := ρ.re) (β₀ := β₀)
        (Y := Y) hQ4 hL₂1 hcpos hg1x hu0 rfl hσlo hσ1 hσβ hβ0hi hYlo_r huτ
    have hrowEβ : (Y : ℝ) ^ (β₀ - ρ.re) * ((136 + 48 * M + 48 * M * 5 + 144 * M / (1 - β₀))
        * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀)) ≤ 1 / 8 :=
      row_Eβ_cap (Q := Q) (L₂ := L₂) (c := c) (u := 1 - β₀) (w := 1 - ρ.re) (σ := ρ.re) (β₀ := β₀)
        (Y := Y) (z := (z : ℝ)) (M := M) (Z₀ := 5) hQ4 hlogL2 hcpos hc1 hu0 hu1 rfl hσlo hσ1 hσβ
        hβ0hi rfl hMnn hMB' (by norm_num) hz1r hzhi_r hYlo_r hYhi_r huτ hgEβ
    -- ===== ROW3 decomposition + contradiction =====
    have hYdiv : (Y : ℝ) ^ (β₀ - ρ.re) / (Y : ℝ) = (Y : ℝ) ^ (β₀ - ρ.re - 1) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one (Y : ℝ), ← Real.rpow_add hYpos,
        show β₀ - ρ.re + -1 = β₀ - ρ.re - 1 by ring]
    have hROW3 : (Y : ℝ) ^ (β₀ - ρ.re) * (((Y : ℝ) ^ (1 - β₀)
          + (136 + 48 * M + 48 * M * 5 + 144 * M / (1 - β₀))
            * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀))
          - (1 - 1 / (Y : ℝ)))
        = (Y : ℝ) ^ (β₀ - ρ.re) * ((Y : ℝ) ^ (1 - β₀) - 1)
          + (Y : ℝ) ^ (β₀ - ρ.re) * ((136 + 48 * M + 48 * M * 5 + 144 * M / (1 - β₀))
            * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀))
          + (Y : ℝ) ^ (β₀ - ρ.re - 1) := by rw [← hYdiv]; ring
    have hYbig : (1 : ℝ) / (Y : ℝ) ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le (by norm_num)
      calc (4 : ℝ) ≤ Q ^ (104 : ℝ) * u ^ (-(14 : ℝ)) := by nlinarith only [hQ104ge4, hu14ge1]
        _ ≤ (Y : ℝ) := hYlo_r
    rw [hROW3] at hmaster
    linarith only [hmaster, hrow1, hrow2, hrowA, hrowEβ, hrow1x, hYbig]

/-! ## §3 — the contract -/

/-- **⟦TAU-EXT-2⟧ — THE DEURING–HEILBRONN REPULSION, OFF THE UNIT BOX.**

`dh_repulsion_ordered` with the height binder `|Im ρ| ≤ 1` **removed entirely**: the contract holds
at every non-real zero of `L(·,χ)` in the window `16/17 ≤ Re ρ < 1`, at that zero's own base
`Q = q(|Im ρ| + 2)`, with `b = 680` and `k = 14` UNCHANGED and a single constant `c` uniform in
everything. In particular it holds on the tall box `|Im ρ| ≤ T` for every `T` — the ⟦TAU-EXT-2⟧
deliverable, in its strongest form.

Why no `T` survives: the chain reads the height only through the `zetaHol` packaging constant and
through `‖ρ‖`, and both may be taken AT the zero — `Zρ = 3 + 2|Im ρ|` (`zetaHol_bound_tall` at
`H = |Im ρ|`, so the height hypothesis is `le_rfl`) and `‖ρ‖ ≤ 1 + |Im ρ|`. Since `q ≥ 2`, both are
bounded by the contract's own base: `Zρ ≤ 2Q` and `‖ρ‖ ≤ Q`. The β₀ side never sees the height at
all and keeps the unit-box numeral `Zβ = 5`.

The ordering hypothesis `ρ.re ≤ β₀` is the named `T-BAL-UNORDERED` deviation, unchanged. -/
theorem dh_repulsion_tall : ∃ b c k : ℝ, 0 < b ∧ 0 < c ∧ 0 ≤ k ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → 2 ≤ q →
      ∀ β₀ : ℝ, DirichletCharacter.LFunction χ (β₀ : ℂ) = 0 → 1 / 2 < β₀ → β₀ < 1 →
      ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.im ≠ 0 →
        16 / 17 ≤ ρ.re → ρ.re < 1 → ρ.re ≤ β₀ →
        (1 - β₀) ≥ c * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(b * (1 - ρ.re)))
          / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ k := by
  obtain ⟨c₀', hc₀'pos, hZFR⟩ := zero_free_region_all
  set c₀ : ℝ := min c₀' 1 with hc₀def
  have hc₀pos : 0 < c₀ := lt_min hc₀'pos one_pos
  have hc₀le1 : c₀ ≤ 1 := min_le_right _ _
  have hc₀lec₀' : c₀ ≤ c₀' := min_le_left _ _
  -- the three `Z₀`-carrying numerals, now `Z₀`-FREE: the β₀ side is pinned at `Zβ = 5`
  -- (`zetaHol_bound_five`) and the ρ side's growth was charged to the `Q`-exponent by
  -- `C2Rho_le_tall`/`row_Eρ_cap_tall`, leaving the bare `570`.
  set KEβ : ℝ := 16 * (328 + 48 * 5) * 248 ^ 9 with hKEβdef
  set KEρ : ℝ := 16 * 570 * 248 ^ 9 with hKEρdef
  set A₀ : ℝ := Real.log 2 + 4 * Real.log (256 * (82 + 12 * 5)) with hA₀def
  have hA₀pos : 0 < A₀ := by
    rw [hA₀def]
    have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : 0 ≤ Real.log (256 * (82 + 12 * 5)) := Real.log_nonneg (by norm_num)
    linarith only [h1, h2]
  -- **THE ARM TABLE** (`log(1/arm)`, `c₀ = 1/126848`; the BINDING arm is the largest).  Every
  -- numeral here is `Z₀`-free, so unlike the R8 twin this tower prices exactly.
  -- REALISED post-TAU-SHARP TS-1 (S1: arm 1 `2^{−250} ⇝ 1/40`; S5(a): `627 ⇝ 248`; S6: `636 ⇝ 570`)
  -- **and TS-2** (S2: arms 4/6/7 carry each row's own γ-floor in place of the uniform `1/8`, so the
  -- exponent `8 ⇝ 1/γ₀`).  Both columns are MEASURED, not projected:
  --                                after TS-1     **after TS-2 (REALISED)**
  --   1. `1/40`                        3.6889          3.6889
  --   2. `(c₀/32)^{17/3}`             86.2267         86.2267  ← **BINDING**
  --   3. `(1/805)^{50/49}`             6.8274          6.8274
  --   4. `(1/(8·1610·e))^{850/133}`   83.7074         66.8716   (γ_A  = 133/850)
  --   5. `1/2`                         0.6931          0.6931
  --   6. `(1/KEβ)^{1700/3547}`       469.8846         28.1507   (γ_Eβ = 3547/1700)
  --   7. `(c₀/KEρ)^{1700/5247}`      563.9186 ←BIND   22.8383   (γ_Eρ = 5247/1700)
  --   8. `1/(3A₀)`                     4.8527          4.8527
  --   9. `1/18`                        2.8904          2.8904
  --  10. `1/576`                       6.3561          6.3561
  -- `log(1/c)` = the MAX = **86.2267** (was 563.9186 after TS-1, 631.5764 landed) — i.e. §D2's
  -- `e^{1264} ⇝ e^{172}`, with no parameter changed.  The binding arm moves from 7 to 2:
  -- `(c₀/32)^{17/3}` is the ρ-main row's threshold, which is NOT a γ-collapse (its exponent
  -- `3/17` is already the row's own), so retiring it is TS-3's business, not this wave's.  The
  -- `1/40` arm stays inert (dominated by arm 10, `log 576 = 6.3561`).  Every projection index below
  -- is hand-built and depth-sensitive, so keep this tower TEN deep and replace numerals in place —
  -- never delete an arm.
  set c : ℝ := min (1 / 40 : ℝ) (min ((c₀ / 32) ^ (17 / 3 : ℝ))
    (min ((1 / 805 : ℝ) ^ (50 / 49 : ℝ)) (min ((1 / (8 * 1610 * Real.exp 1)) ^ (850 / 133 : ℝ))
    (min (1 / 2 : ℝ) (min ((1 / KEβ) ^ (1700 / 3547 : ℝ)) (min ((c₀ / KEρ) ^ (1700 / 5247 : ℝ))
    (min (1 / (3 * A₀)) (min (1 / 18 : ℝ) (1 / 576 : ℝ))))))))) with hcdef
  have hp1 : (0 : ℝ) < 1 / 40 := by norm_num
  have hp2 : (0 : ℝ) < (c₀ / 32) ^ (17 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (div_pos hc₀pos (by norm_num)) _
  have hp3 : (0 : ℝ) < (1 / 805 : ℝ) ^ (50 / 49 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hp4 : (0 : ℝ) < (1 / (8 * 1610 * Real.exp 1)) ^ (850 / 133 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hp6 : (0 : ℝ) < (1 / KEβ) ^ (1700 / 3547 : ℝ) :=
    Real.rpow_pos_of_pos (by rw [hKEβdef]; positivity) _
  have hp7 : (0 : ℝ) < (c₀ / KEρ) ^ (1700 / 5247 : ℝ) :=
    Real.rpow_pos_of_pos (div_pos hc₀pos (by rw [hKEρdef]; positivity)) _
  have hp8 : (0 : ℝ) < 1 / (3 * A₀) := div_pos one_pos (by linarith only [hA₀pos])
  have hcpos : 0 < c := by
    rw [hcdef]
    exact lt_min hp1 (lt_min hp2 (lt_min hp3 (lt_min hp4 (lt_min (by norm_num) (lt_min hp6
      (lt_min hp7 (lt_min hp8 (lt_min (by norm_num) (by norm_num)))))))))
  have hc_t1 : c ≤ 1 / 40 := by rw [hcdef]; exact min_le_left _ _
  have hc_t2 : c ≤ (c₀ / 32) ^ (17 / 3 : ℝ) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hc_t3 : c ≤ (1 / 805 : ℝ) ^ (50 / 49 : ℝ) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc_t4 : c ≤ (1 / (8 * 1610 * Real.exp 1)) ^ (850 / 133 : ℝ) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hc_t5 : c ≤ (1 / 2 : ℝ) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hc_t6 : c ≤ (1 / KEβ) ^ (1700 / 3547 : ℝ) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hc_t7 : c ≤ (c₀ / KEρ) ^ (1700 / 5247 : ℝ) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))))))
  have hc_t8 : c ≤ 1 / (3 * A₀) := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))))
  have hc_t9 : c ≤ 1 / 18 := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _))))))))
  have hc_t10 : c ≤ 1 / 576 := by
    rw [hcdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_right _ _))))))))
  have hc1 : c ≤ 1 := le_trans hc_t5 (by norm_num)
  rw [hKEβdef] at hc_t6
  rw [hKEρdef] at hc_t7
  rw [hA₀def] at hc_t8
  clear_value c c₀
  refine ⟨680, c, 14, by norm_num, hcpos, by norm_num, ?_⟩
  intro q _instNe χ hχ hχ1 hsq hq β₀ hβ0zero hβ0lo hβ0hi ρ hρzero hρim hσlo hσ1 hord
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hfloor : ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
    have h := hZFR q χ hχ hχ1 hρzero (by linarith only [hσlo] : 1 / 2 ≤ ρ.re) (Or.inr hρim)
    have hlogpos : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) :=
      Real.log_pos (by nlinarith only [hqR, abs_nonneg ρ.im])
    have hdiv : c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2))
        ≤ c₀' / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by gcongr
    linarith only [h, hdiv]
  -- the TALL packaging, taken AT the zero's own height
  have hZρ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ |ρ.im| →
      ‖zetaHol s‖ ≤ 3 + 2 * |ρ.im| := zetaHol_bound_tall |ρ.im|
  have hZ0nn : (0 : ℝ) ≤ 3 + 2 * |ρ.im| := by positivity
  have hZ0Q : 3 + 2 * |ρ.im| ≤ 2 * ((q : ℝ) * (|ρ.im| + 2)) := by
    nlinarith only [hqR, abs_nonneg ρ.im]
  exact dh_repulsion_inst_tall (H := |ρ.im|) χ hχ hχ1 hsq hq hβ0zero hβ0lo hβ0hi hρzero hρim
    le_rfl hσlo hσ1 hord hZρ hc₀pos hc₀le1 hZ0nn hZ0Q hfloor hcpos hc1 hc_t1 hc_t2 hc_t3 hc_t4
    hc_t5 hc_t6 hc_t7 hc_t8 hc_t9 hc_t10

/-! ## §4 — the plug: the `β`-supplier at the CAMPAIGN box -/

/-- **THE PLUG — `boxZeros_re_le_of_repulsion` fired at the campaign box.**

`boxZeros_re_le_unit_box` (`Salt/SW/TauExt.lean`) is this statement at `T = 1`, off the landed
`dh_repulsion_ordered`. Here it is at `T = efHeight q + 2 = (log q + 2)⁴ + 2` — the ⟦N0 CLEAR⟧
ruled truncation height, i.e. the box that `efZeroSumM_spend_at_efHeight` actually sums over — off
`dh_repulsion_tall`. **The artillery is COMPLETE for N4:** every zero of `L(·,χ)` in the campaign
box has real part at most the single number `repulsionCeiling b c k (q(T+2)) (1 − β₀)`, and that is
verbatim the `hβ` hypothesis of `efZeroSumM_spend_at_efHeight` (see
`efZeroSumM_spend_at_repulsion`, whose `hrep` this theorem's `dh_repulsion_tall` now discharges).

The three named side hypotheses are carried unchanged and each names a real obligation, not a gap:
`hord` (the `T-BAL-UNORDERED` deviation `Re ρ ≤ β₀`), `hreal` (the zeros ON the real axis — the
exceptional zero `β₀` itself does not satisfy the ceiling and must be split off first, exactly as
HB (4.11) splits off the `−y^{β₀}/β₀` term of `ψ`), and `hceil` (the ceiling exceeds the contract's
window floor `16/17`, so the discarded strip is free). `hN` is the regime statement. -/
theorem boxZeros_re_le_at_efHeight : ∃ b c k : ℝ, 0 < b ∧ 0 < c ∧ 0 ≤ k ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → 2 ≤ q →
      ∀ β₀ : ℝ, DirichletCharacter.LFunction χ (β₀ : ℂ) = 0 → 1 / 2 < β₀ → β₀ < 1 →
      ∀ σ₀ : ℝ,
        (∀ ρ ∈ boxZeros χ σ₀ 1 (efHeight q + 2), ρ.re ≤ β₀) →
        (∀ ρ ∈ boxZeros χ σ₀ 1 (efHeight q + 2), ρ.im = 0 →
          ρ.re ≤ repulsionCeiling b c k ((q : ℝ) * (efHeight q + 4)) (1 - β₀)) →
        16 / 17 ≤ repulsionCeiling b c k ((q : ℝ) * (efHeight q + 4)) (1 - β₀) →
        0 ≤ Real.log (1 / (1 - β₀)) - Real.log (1 / c)
          - k * Real.log (Real.log ((q : ℝ) * (efHeight q + 4)) + 2) →
        ∀ ρ ∈ boxZeros χ σ₀ 1 (efHeight q + 2),
          ρ.re ≤ repulsionCeiling b c k ((q : ℝ) * (efHeight q + 4)) (1 - β₀) := by
  obtain ⟨b, c, k, hb, hc, hk, hDH⟩ := dh_repulsion_tall
  refine ⟨b, c, k, hb, hc, hk, ?_⟩
  intro q _inst χ hχ hχ1 hsq hq β₀ hβ0zero hβ0lo hβ0hi σ₀ hord hreal hceil hN
  have h4 : (q : ℝ) * (efHeight q + 2 + 2) = (q : ℝ) * (efHeight q + 4) := by ring
  have hmain := boxZeros_re_le_of_repulsion (χ := χ) hχ1 (b := b) (c := c) (k := k) (β₀ := β₀)
    (σ₀ := σ₀) (T := efHeight q + 2) hb hc hk hq hβ0hi
    (fun ρ hz him _hle hwin hlt hordρ =>
      hDH q χ hχ hχ1 hsq hq β₀ hβ0zero hβ0lo hβ0hi ρ hz him hwin hlt hordρ)
    hord (by rw [h4]; exact hreal) (by rw [h4]; exact hceil) (by rw [h4]; exact hN)
  intro ρ hρ
  have h := hmain ρ hρ
  rwa [h4] at h

end Salt.SW

end
