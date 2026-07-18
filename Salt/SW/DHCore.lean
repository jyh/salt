/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHExtract
import Salt.SW.DHBal
import Salt.SW.ZetaEM

/-!
# The unmollified extraction crux (`T-BAL` R2/R3) — the swamping-error resolution

Design: the JYH-ratified **T-BAL S₀ synthesis freeze** (`docs/exploration/tbal-s0-freeze.md`,
the 5th design). This module lands the R2 unmollified detector extraction at a real zero `β₀`
and its R3 specialization (the effective-Siegel lower bound `L1_lower_siegel`).

## The swamping-error resolution (the crux the freeze flagged)

The detector `D₀(y) = Σ_{n≤y} dhA χ n · n^{−β₀} · (1−n/y)` is handled by the landed kernel-Abel
identity `kernel_abel_sum`: `D₀ = (1/y)·Σ_{t<y} A(t)`, `A(t) = Σ_{n≤t} dhA χ n · n^{−β₀}`.
The naive per-divisor remainder swamps the budget (`~ y^{1−β₀} log y`). THE RESOLUTION: apply the
landed **symmetric √t Dirichlet hyperbola** (`sum_divisors_eq_hyperbola_symm`) to `A(t)` with
`a_d = χ_ℝ(d)·d^{−β₀}`, `b_e = e^{−β₀}` — since `dhA = χ_ℝ ∗ 1`, this is `A(t)` exactly. Both legs
are confined to `d,e ≤ √t`, so the zero-killed character partial sums `B(m) = Σ_{d≤m} χ_ℝ(d)d^{−β₀}`
(`chiRe_partial_at_zero_le`: `|B(m)| ≤ 6M·m^{−β₀}`) control the two short legs and the corner by
`t^{−β₀}·√t = t^{1/2−β₀} ≤ 1` (β₀ ≥ 1/2). No swamping. The main term `L₁·t^{1−β₀}/(1−β₀)` comes
from the long-leg's `Σ_{d≤√t} χ_ℝ(d)/d → L(1,χ)` via the landed strip bound.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open Complex Finset

noncomputable section

namespace Salt.SW

/-! ## §1 — the power-sum caps (`T(m) = Σ_{e≤m} e^{−β}` two-sided) -/

/-- **Antitone power-sum cap.** For `0 ≤ β < 1` and every `m`,
`Σ_{1≤e≤m} e^{−β} ≤ m^{1−β}/(1−β)`. The integrand `x ↦ x^{−β}` is antitone on `[1,m]`, so the
`e ≥ 2` block is `≤ ∫_1^m x^{−β} = (m^{1−β}−1)/(1−β)` (`AntitoneOn.sum_le_integral`); adding the
`e = 1` term `1` and using `−β/(1−β) ≤ 0` gives the cap. -/
theorem sum_rpow_neg_le {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (m : ℕ) :
    ∑ e ∈ Finset.Icc 1 m, (e : ℝ) ^ (-β) ≤ (m : ℝ) ^ (1 - β) / (1 - β) := by
  have hu : (0 : ℝ) < 1 - β := by linarith
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Finset.Icc_eq_empty (by omega : ¬ 1 ≤ 0), Finset.sum_empty, Nat.cast_zero]
    rw [Real.zero_rpow (by linarith : (1 : ℝ) - β ≠ 0)]
    positivity
  · -- split off the `e = 1` term, bound the `e ≥ 2` block by the integral
    have hins : Finset.Icc 1 m = insert 1 (Finset.Icc 2 m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h1notin : (1 : ℕ) ∉ Finset.Icc 2 m := by simp only [Finset.mem_Icc]; omega
    rw [hins, Finset.sum_insert h1notin, Nat.cast_one, Real.one_rpow]
    -- reindex `Icc 2 m` to `range (m-1)` via `e = i + 2`
    have hmeq : (1 : ℝ) + (((m - 1 : ℕ) : ℝ)) = (m : ℝ) := by
      rw [Nat.cast_sub hm]; push_cast; ring
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-β))
        (Set.Icc (1 : ℝ) (1 + (((m - 1 : ℕ)) : ℝ))) := by
      intro u hu' v hv' huv
      simp only [Set.mem_Icc] at hu' hv'
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hu'.1]) huv (by linarith)
    have hle := hanti.sum_le_integral (x₀ := 1) (a := m - 1)
    rw [hmeq] at hle
    have hreindex : ∑ e ∈ Finset.Icc 2 m, (e : ℝ) ^ (-β)
        = ∑ i ∈ Finset.range (m - 1), (fun x : ℝ => x ^ (-β)) (1 + ((i + 1 : ℕ) : ℝ)) := by
      rw [show Finset.Icc 2 m = Finset.Ico 2 (m + 1) from by
            ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
        Finset.sum_Ico_eq_sum_range, show m + 1 - 2 = m - 1 from by omega]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hb : ((2 + i : ℕ) : ℝ) = 1 + ((i + 1 : ℕ) : ℝ) := by push_cast; ring
      simp only [hb]
    have hint : (∫ x in (1 : ℝ)..(m : ℝ), x ^ (-β)) = ((m : ℝ) ^ (1 - β) - 1) / (1 - β) := by
      rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -β)), Real.one_rpow,
        show -β + 1 = 1 - β from by ring]
    rw [hreindex]
    calc 1 + ∑ i ∈ Finset.range (m - 1), (fun x : ℝ => x ^ (-β)) (1 + ((i + 1 : ℕ) : ℝ))
        ≤ 1 + ∫ x in (1 : ℝ)..(m : ℝ), x ^ (-β) := by linarith [hle]
      _ = 1 + ((m : ℝ) ^ (1 - β) - 1) / (1 - β) := by rw [hint]
      _ ≤ (m : ℝ) ^ (1 - β) / (1 - β) := by
          rw [le_div_iff₀ hu, add_mul, div_mul_cancel₀ _ (by linarith : (1 : ℝ) - β ≠ 0)]
          nlinarith [Real.rpow_nonneg (Nat.cast_nonneg m) (1 - β), h0]

/-! ## §2 — the real Euler–Maclaurin split of `T(m) = Σ_{e≤m} e^{−β}` -/

/-- **The real EM split.** For `1/2 ≤ β < 1` and `m ≥ 1`,
`|T(m) − m^{1−β}/(1−β) − ζ(β).re| ≤ 8(1+β)·m^{−β}`, `T(m) = Σ_{1≤e≤m} e^{−β}`. The real cast of the
landed complex `zeta_partial_em` at the real point `s = β` (`Re` of the complex bound). -/
theorem T_em_real {β : ℝ} (hlo : 1 / 2 ≤ β) (hhi : β < 1) {m : ℕ} (hm : 1 ≤ m) :
    |(∑ e ∈ Finset.Icc 1 m, (e : ℝ) ^ (-β)) - (m : ℝ) ^ (1 - β) / (1 - β)
        - (riemannZeta (β : ℂ)).re|
      ≤ 8 * (1 + β) * (m : ℝ) ^ (-β) := by
  have hβ0 : 0 < β := by linarith
  have hem := zeta_partial_em (s := (β : ℂ)) (by rw [Complex.ofReal_re]; linarith)
    (by rw [Complex.ofReal_re]; exact hhi) (by rw [Complex.ofReal_im]; simp) hm
  have hsumcast : ((∑ e ∈ Finset.Icc 1 m, (e : ℝ) ^ (-β) : ℝ) : ℂ)
      = ∑ a ∈ Finset.Icc 1 m, (a : ℂ) ^ (-(β : ℂ)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (a : ℝ)), Complex.ofReal_neg,
      Complex.ofReal_natCast]
  have hmaincast : (((m : ℝ) ^ (1 - β) / (1 - β) : ℝ) : ℂ)
      = (m : ℂ) ^ (1 - (β : ℂ)) / (1 - (β : ℂ)) := by
    rw [Complex.ofReal_div, Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (m : ℝ)),
      Complex.ofReal_natCast, Complex.ofReal_sub, Complex.ofReal_one]
  have hReS : (∑ a ∈ Finset.Icc 1 m, (a : ℂ) ^ (-(β : ℂ))).re
      = ∑ e ∈ Finset.Icc 1 m, (e : ℝ) ^ (-β) := by rw [← hsumcast, Complex.ofReal_re]
  have hReMain : ((m : ℂ) ^ (1 - (β : ℂ)) / (1 - (β : ℂ))).re = (m : ℝ) ^ (1 - β) / (1 - β) := by
    rw [← hmaincast, Complex.ofReal_re]
  have hnorm : ‖(β : ℂ)‖ = β := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
  have hwre : ((∑ a ∈ Finset.Icc 1 m, (a : ℂ) ^ (-(β : ℂ)))
        - ((m : ℂ) ^ (1 - (β : ℂ)) / (1 - (β : ℂ)) + riemannZeta (β : ℂ))).re
      = (∑ e ∈ Finset.Icc 1 m, (e : ℝ) ^ (-β)) - (m : ℝ) ^ (1 - β) / (1 - β)
          - (riemannZeta (β : ℂ)).re := by
    rw [Complex.sub_re, Complex.add_re, hReS, hReMain]; ring
  calc |(∑ e ∈ Finset.Icc 1 m, (e : ℝ) ^ (-β)) - (m : ℝ) ^ (1 - β) / (1 - β)
          - (riemannZeta (β : ℂ)).re|
      = |((∑ a ∈ Finset.Icc 1 m, (a : ℂ) ^ (-(β : ℂ)))
          - ((m : ℂ) ^ (1 - (β : ℂ)) / (1 - (β : ℂ)) + riemannZeta (β : ℂ))).re| := by rw [hwre]
    _ ≤ ‖(∑ a ∈ Finset.Icc 1 m, (a : ℂ) ^ (-(β : ℂ)))
          - ((m : ℂ) ^ (1 - (β : ℂ)) / (1 - (β : ℂ)) + riemannZeta (β : ℂ))‖ :=
        Complex.abs_re_le_norm _
    _ ≤ 8 * (1 + β) * (m : ℝ) ^ (-β) := by
        have h := hem; rw [hnorm, Complex.ofReal_re] at h; exact h

/-! ## §3 — the `ζ(β₀).re` size bound (the `1/u` dust constant) -/

/-- **`ζ(β).re` bound.** For `1/2 ≤ β < 1`, `|ζ(β).re| ≤ Z₀ + 1/(1−β)` where `Z₀` is the
`zetaHol_bound` compactness constant. `ζ(β) = 1/(β−1) + zetaHol β` (`riemannZeta_eq_add_zetaHol`)
and `‖zetaHol β‖ ≤ Z₀` on the strip. -/
theorem abs_zeta_re_le {Z₀ : ℝ}
    (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {β : ℝ} (hlo : 1 / 2 ≤ β) (hhi : β < 1) :
    |(riemannZeta (β : ℂ)).re| ≤ Z₀ + 1 / (1 - β) := by
  have hne : (β : ℂ) ≠ 1 := by
    intro h; rw [Complex.ext_iff, Complex.ofReal_re, Complex.one_re] at h; linarith [h.1]
  have hsplit : riemannZeta (β : ℂ) = 1 / ((β : ℂ) - 1) + zetaHol (β : ℂ) :=
    riemannZeta_eq_add_zetaHol hne
  have hZb : ‖zetaHol (β : ℂ)‖ ≤ Z₀ := hZ (β : ℂ)
    (by rw [Complex.ofReal_re]; linarith) (by rw [Complex.ofReal_re]; linarith)
    (by rw [Complex.ofReal_im]; simp)
  have hpole : ‖(1 : ℂ) / ((β : ℂ) - 1)‖ = 1 / (1 - β) := by
    rw [norm_div, norm_one]
    congr 1
    rw [show (β : ℂ) - 1 = (((β - 1 : ℝ)) : ℂ) from by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith : β - 1 < 0)]
    ring
  calc |(riemannZeta (β : ℂ)).re|
      ≤ ‖riemannZeta (β : ℂ)‖ := Complex.abs_re_le_norm _
    _ = ‖(1 : ℂ) / ((β : ℂ) - 1) + zetaHol (β : ℂ)‖ := by rw [hsplit]
    _ ≤ ‖(1 : ℂ) / ((β : ℂ) - 1)‖ + ‖zetaHol (β : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 / (1 - β) + Z₀ := by rw [hpole]; linarith [hZb]
    _ = Z₀ + 1 / (1 - β) := by ring

/-! ## §4 — the `√t` / floor per-term estimates (the decay engine) -/

/-- `t ≤ 2·(e·⌊t/e⌋)` for `1 ≤ e ≤ t` (`⌊t/e⌋ ≥ 1`, and `t/e < ⌊t/e⌋+1 ≤ 2⌊t/e⌋`). -/
lemma floor_div_mul_ge {e t : ℕ} (he : 1 ≤ e) (het : e ≤ t) :
    (t : ℝ) ≤ 2 * ((e : ℝ) * ((t / e : ℕ) : ℝ)) := by
  have he0 : 0 < e := he
  have hfloor : 1 ≤ t / e := (Nat.one_le_div_iff he0).mpr het
  have hmod : t < (t / e + 1) * e := by
    have h1 := Nat.div_add_mod t e
    have h2 : t % e < e := Nat.mod_lt t he0
    nlinarith
  have hR : (t : ℝ) < (((t / e : ℕ) : ℝ) + 1) * (e : ℝ) := by exact_mod_cast hmod
  have hfR : (1 : ℝ) ≤ ((t / e : ℕ) : ℝ) := by exact_mod_cast hfloor
  have he0R : (0 : ℝ) ≤ (e : ℝ) := by positivity
  nlinarith [hR, hfR, he0R, mul_nonneg (by linarith : (0 : ℝ) ≤ ((t / e : ℕ) : ℝ) - 1) he0R]

/-- **The per-term decay bound.** For `0 ≤ β ≤ 1` and `1 ≤ e ≤ t`,
`e^{−β}·⌊t/e⌋^{−β} ≤ 2·t^{−β}` (fold to `(e·⌊t/e⌋)^{−β}`, use `e·⌊t/e⌋ ≥ t/2`, then `2^β ≤ 2`). -/
lemma term_rpow_le {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) {e t : ℕ} (he : 1 ≤ e) (het : e ≤ t) :
    (e : ℝ) ^ (-β) * ((t / e : ℕ) : ℝ) ^ (-β) ≤ 2 * (t : ℝ) ^ (-β) := by
  have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (le_trans he het)
  have hfloor : 1 ≤ t / e := (Nat.one_le_div_iff (by omega)).mpr het
  have hf0 : (0 : ℝ) < ((t / e : ℕ) : ℝ) := by exact_mod_cast hfloor
  have hprod : (t : ℝ) / 2 ≤ (e : ℝ) * ((t / e : ℕ) : ℝ) := by
    have := floor_div_mul_ge he het; linarith
  rw [← Real.mul_rpow he0.le hf0.le]
  calc ((e : ℝ) * ((t / e : ℕ) : ℝ)) ^ (-β)
      ≤ ((t : ℝ) / 2) ^ (-β) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hprod (by linarith)
    _ ≤ 2 * (t : ℝ) ^ (-β) := by
        rw [show (t : ℝ) / 2 = (t : ℝ) * (2 : ℝ)⁻¹ from by ring,
          Real.mul_rpow (by positivity) (by positivity)]
        have h2 : ((2 : ℝ)⁻¹) ^ (-β) ≤ 2 := by
          rw [Real.inv_rpow (by norm_num) , Real.rpow_neg (by norm_num), inv_inv]
          calc (2 : ℝ) ^ β ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
            _ = 2 := by norm_num
        have ht0 : (0 : ℝ) ≤ (t : ℝ) ^ (-β) := Real.rpow_nonneg (by positivity) _
        nlinarith [h2, ht0]

/-- `(Nat.sqrt t : ℝ) ≤ Real.sqrt t`. -/
lemma natSqrt_le_sqrt (t : ℕ) : ((Nat.sqrt t : ℕ) : ℝ) ≤ Real.sqrt (t : ℝ) := by
  rw [show ((Nat.sqrt t : ℕ) : ℝ) = Real.sqrt (((Nat.sqrt t : ℝ)) ^ 2) from
    (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  have : Nat.sqrt t ^ 2 ≤ t := Nat.sqrt_le' t
  exact_mod_cast this

/-- **The `√t` collapse.** For `1 ≤ t` and any `β`, `(Nat.sqrt t : ℝ)·t^{−β} ≤ t^{1/2−β}`. -/
lemma natSqrt_mul_rpow_le {β : ℝ} {t : ℕ} (ht : 1 ≤ t) :
    ((Nat.sqrt t : ℕ) : ℝ) * (t : ℝ) ^ (-β) ≤ (t : ℝ) ^ (1 / 2 - β) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hsqrt : ((Nat.sqrt t : ℕ) : ℝ) ≤ (t : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; exact natSqrt_le_sqrt t
  calc ((Nat.sqrt t : ℕ) : ℝ) * (t : ℝ) ^ (-β)
      ≤ (t : ℝ) ^ (1 / 2 : ℝ) * (t : ℝ) ^ (-β) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg ht0.le _)
    _ = (t : ℝ) ^ (1 / 2 - β) := by rw [← Real.rpow_add ht0]; ring_nf

/-- `√t < 2·⌊√t⌋` for `1 ≤ t` (`⌊√t⌋ ≥ 1` and `√t < ⌊√t⌋+1 ≤ 2⌊√t⌋`). -/
lemma sqrt_lt_two_natSqrt {t : ℕ} (ht : 1 ≤ t) :
    Real.sqrt (t : ℝ) < 2 * ((Nat.sqrt t : ℕ) : ℝ) := by
  have hr1 : 1 ≤ Nat.sqrt t := by
    calc 1 = Nat.sqrt 1 := Nat.sqrt_one.symm
      _ ≤ Nat.sqrt t := Nat.sqrt_le_sqrt ht
  have hr1R : (1 : ℝ) ≤ ((Nat.sqrt t : ℕ) : ℝ) := by exact_mod_cast hr1
  have h2 := Nat.lt_succ_sqrt t
  have hcast : (t : ℝ) < (((Nat.sqrt t : ℕ) : ℝ) + 1) ^ 2 := by
    have hh : (t : ℝ) < ((Nat.sqrt t + 1 : ℕ) : ℝ) * ((Nat.sqrt t + 1 : ℕ) : ℝ) := by
      exact_mod_cast h2
    push_cast at hh ⊢; nlinarith [hh]
  have hlt : Real.sqrt (t : ℝ) < ((Nat.sqrt t : ℕ) : ℝ) + 1 := by
    rw [show ((Nat.sqrt t : ℕ) : ℝ) + 1
        = Real.sqrt ((((Nat.sqrt t : ℕ) : ℝ) + 1) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_lt_sqrt (by positivity) hcast
  linarith

/-- **The general `⌊√t⌋`-decay.** For `1 ≤ t` and `−1 ≤ a ≤ 0`,
`⌊√t⌋^a ≤ 2·t^{a/2}` (from `⌊√t⌋ ≥ √t/2` and `2^{−a} ≤ 2`). -/
lemma sqrt_pow_bound {a : ℝ} (ha1 : -1 ≤ a) (ha0 : a ≤ 0) {t : ℕ} (ht : 1 ≤ t) :
    ((Nat.sqrt t : ℕ) : ℝ) ^ a ≤ 2 * (t : ℝ) ^ (a / 2) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr ht0
  have hge : Real.sqrt (t : ℝ) / 2 ≤ ((Nat.sqrt t : ℕ) : ℝ) := by
    have := sqrt_lt_two_natSqrt ht; linarith
  have hst2 : (0 : ℝ) < Real.sqrt (t : ℝ) / 2 := by linarith
  have hsqrt_rpow : Real.sqrt (t : ℝ) ^ a = (t : ℝ) ^ (a / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le]
    congr 1; ring
  have h2a : (2 : ℝ) ^ (-a) ≤ 2 := by
    calc (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := by norm_num
  calc ((Nat.sqrt t : ℕ) : ℝ) ^ a
      ≤ (Real.sqrt (t : ℝ) / 2) ^ a := Real.rpow_le_rpow_of_nonpos hst2 hge ha0
    _ = Real.sqrt (t : ℝ) ^ a * (2 : ℝ) ^ (-a) := by
        rw [Real.div_rpow (Real.sqrt_nonneg _) (by norm_num), Real.rpow_neg (by norm_num),
          div_eq_mul_inv]
    _ = (t : ℝ) ^ (a / 2) * (2 : ℝ) ^ (-a) := by rw [hsqrt_rpow]
    _ ≤ (t : ℝ) ^ (a / 2) * 2 := by
        apply mul_le_mul_of_nonneg_left h2a (Real.rpow_nonneg ht0.le _)
    _ = 2 * (t : ℝ) ^ (a / 2) := by ring

/-- **The tangent-line (concavity) bound.** For `0 ≤ c ≤ 1` and `0 < x ≤ y`,
`y^c − x^c ≤ c·x^{c−1}·(y−x)`. Mean value theorem (`exists_hasDerivAt_eq_slope`) for `z ↦ z^c`
plus `ξ^{c−1} ≤ x^{c−1}` (`ξ ≥ x`, exponent `c−1 ≤ 0`). The floor-error control on the main term. -/
lemma rpow_sub_le_tangent {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y ^ c - x ^ c ≤ c * x ^ (c - 1) * (y - x) := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · simp
  have hcont : ContinuousOn (fun z : ℝ => z ^ c) (Set.Icc x y) :=
    ContinuousOn.rpow_const continuousOn_id (fun z _ => Or.inr hc0)
  have hderiv : ∀ z ∈ Set.Ioo x y, HasDerivAt (fun z : ℝ => z ^ c) (c * z ^ (c - 1)) z := by
    intro z hz
    exact Real.hasDerivAt_rpow_const (Or.inl (lt_of_lt_of_le hx (le_of_lt hz.1)).ne')
  obtain ⟨ξ, hξ, hslope⟩ :=
    exists_hasDerivAt_eq_slope (fun z : ℝ => z ^ c) (fun z => c * z ^ (c - 1)) hlt hcont hderiv
  have hyx : (0 : ℝ) < y - x := by linarith
  have hξx : x ≤ ξ := le_of_lt hξ.1
  have hmono : ξ ^ (c - 1) ≤ x ^ (c - 1) :=
    Real.rpow_le_rpow_of_nonpos hx hξx (by linarith)
  have heq : y ^ c - x ^ c = c * ξ ^ (c - 1) * (y - x) := by
    field_simp at hslope ⊢
    linarith [hslope]
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ hyx.le
  apply mul_le_mul_of_nonneg_left hmono hc0

/-! ## §5 — the `A(t)` symmetric-hyperbola decomposition and the per-`t` bound -/

/-- **The `A(t)` symmetric hyperbola.** `A(t) = Σ_{n≤t} dhA χ n · n^{−β₀}` splits at `√t`:
`A(t) = Σ_{d≤√t} χ_ℝ(d)d^{−β₀}·T(⌊t/d⌋) + Σ_{e≤√t} e^{−β₀}·B(⌊t/e⌋) − B(⌊√t⌋)·T(⌊√t⌋)`,
`T(m) = Σ_{e≤m} e^{−β₀}`, `B(m) = Σ_{d≤m} χ_ℝ(d)d^{−β₀}`. The landed symmetric hyperbola
applied to `a_d = χ_ℝ(d)d^{−β₀}`, `b_e = e^{−β₀}` (using `dhA = χ_ℝ ∗ 1` and
`d^{−β₀}·(n/d)^{−β₀} = n^{−β₀}`). -/
theorem dhAbel_hyperbola {q : ℕ} (χ : DirichletCharacter ℂ q) {β₀ : ℝ} (t : ℕ) :
    ∑ n ∈ Finset.Icc 1 t, dhA χ n * (n : ℝ) ^ (-β₀)
      = (∑ d ∈ Finset.Icc 1 (Nat.sqrt t), (chiRe χ d * (d : ℝ) ^ (-β₀))
            * ∑ e ∈ Finset.Icc 1 (t / d), (e : ℝ) ^ (-β₀))
        + (∑ e ∈ Finset.Icc 1 (Nat.sqrt t), (e : ℝ) ^ (-β₀)
            * ∑ d ∈ Finset.Icc 1 (t / e), chiRe χ d * (d : ℝ) ^ (-β₀))
        - (∑ d ∈ Finset.Icc 1 (Nat.sqrt t), chiRe χ d * (d : ℝ) ^ (-β₀))
          * ∑ e ∈ Finset.Icc 1 (Nat.sqrt t), (e : ℝ) ^ (-β₀) := by
  have hrw : (∑ n ∈ Finset.Icc 1 t, dhA χ n * (n : ℝ) ^ (-β₀))
      = ∑ n ∈ Finset.Icc 1 t, ∑ d ∈ n.divisors,
          (chiRe χ d * (d : ℝ) ^ (-β₀)) * ((n / d : ℕ) : ℝ) ^ (-β₀) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_Icc] at hn
    rw [dhA, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hnd : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    have hsplit : (n : ℝ) ^ (-β₀) = (d : ℝ) ^ (-β₀) * ((n / d : ℕ) : ℝ) ^ (-β₀) := by
      rw [← Real.mul_rpow (by positivity) (by positivity), hnd]
    rw [hsplit]; ring
  rw [hrw]
  exact sum_divisors_eq_hyperbola_symm (fun d => chiRe χ d * (d : ℝ) ^ (-β₀))
    (fun e => (e : ℝ) ^ (-β₀)) t

end Salt.SW

end
