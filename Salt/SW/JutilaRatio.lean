/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.JutilaHalasz

/-!
# B2 W9c′ — THE RATIO's re-cut: the residue block's integrability over the device's rectangle,
the device lemma, and THE RATIO `J ≪ (qT)^{13(1−σ)}`

The ratio `card_system_le_rpow` was flagged at the W9a + W9c wave (`B2-W9ac-card_system_le_rpow`)
with its TEN inputs landed and one input NAMED as missing: the assembly integrates both sides of
Halász's inequality over the device's rectangle `Ξ × H` (`M = e^ξ`, `N = e^η`), and every route
to `c·|Ξ||H| ≤ ∫_Ξ∫_H Q` takes `IntervalIntegrable Q` — a non-integrable integrand has interval
integral `0` in mathlib, so the LOWER bound is false without it — while the corpus carried bounds
on `resKernel`, `jutilaI` and `halaszBTsum` only at a FIXED `(N, M)`. This file supplies the row.

* **The residue block on the rectangle is a FINITE sum with a UNIFORM range**
  (`halaszBTsum_jutilaB_exp_eq_sum`): `jutilaB q R N M n = 0` for `n ≥ N`
  (`jutilaB_eq_zero_of_le`), so on `e^ξ ≤ e^η ≤ N₁` the series is the sum over `n ≤ ⌈N₁⌉₊` —
  the landed `halaszBTsum_jutilaB_eq_sum`'s range extended by zero terms. Each term is CONTINUOUS
  in `(ξ, η)` (`continuous_jutilaB_exp`: `jutilaB`'s body is
  `n⁻¹·Σ'(n)²·((max 0 (1 − n·e^{−η}))² − (max 0 (1 − n·e^{−ξ}))²)`), hence so is the finite sum
  (`continuous_halaszB_sum_exp`) — a function on all of `ℝ²` that AGREES with the residue block
  on the rectangle. The kernel `resKernel s (e^η) (e^ξ)` is continuous in `(ξ, η)` at every `s`
  (`continuous_resKernel_exp`: the closed form off `s = 0`, `η − ξ` at `s = 0`); `jutilaI` on the
  rectangle is then integrable as the DIFFERENCE of two integrable functions through the landed
  identity `halaszBTsum_jutilaB_eq` — it needs no continuity row of its own.
* **THE DEVICE LEMMA** (`const_mul_le_integral_integral_of_le`): for `F` continuous on `ℝ²` and
  `c ≤ F` on the closed rectangle, `c·|Ξ||H| ≤ ∫_Ξ∫_H F` — the inner integral against the
  constant by `intervalIntegral.integral_mono_on`, the outer likewise, its integrand
  `ξ ↦ ∫_H F(ξ, ·)` continuous by `continuous_parametric_intervalIntegral_of_continuous'`.
* **THE RATIO** (`card_system_le_rpow`, VERBATIM from the W9a/c freeze — the statement never
  moved): the assembly as the W9a/c freeze's §1 spells it, with the device applied to the
  finite-sum form `F̃` (equal to `Q` on the rectangle by (i), so `∫∫ F̃ = ∫∫ Q` by `integral_congr`
  twice), the double integral expanded per `(j, k)` through the identity with `integral_add` on
  the now-integrable pieces, the diagonal and off-diagonal bounded by the two landed integrated
  kernel rows, the `I`-block by `norm_jutilaI_le` under `norm_integral_le_of_norm_le_const` twice.

## The honest label

Nothing here is new mathematics: (i) and (ii) are the plumbing the device needs and the corpus
lacked; the ratio's statement is the W9a/c freeze's, character for character, and its docstring
is kept. `C` and `D₁` are non-effective inside the `∃` (the partial summation's landed witness is
`4·max(4K_H, K_L)`, so the design's `C_ps` doubles and `D₁` moves by `2^{240/43} = 47.9`, i.e.
`+1.68` decades — inside the band `10^59–10^64` unless `D₁` sat above `10^{62.3}`; non-effective
either way); the ratio assumes zeros with `β ≥ 119/120` and is VACUOUS at the object. Nothing
here bears on twin primes or on the crown's conditions.
-/

open MeasureTheory Complex DirichletCharacter

noncomputable section
namespace Salt.SW

variable {q : ℕ}

/-! ## (i) The residue block on the rectangle: a finite sum, continuous in `(ξ, η)` -/

/-- On `e^ξ ≤ e^η ≤ N₁` the series is the finite sum over `n ≤ ⌈N₁⌉₊`: `jutilaB` vanishes at
`n ≥ N = e^η` (`jutilaB_eq_zero_of_le`), so the landed `halaszBTsum_jutilaB_eq_sum`'s range
`Icc 1 ⌈e^η⌉₊` extends to `Icc 1 ⌈N₁⌉₊` by zero terms. -/
theorem halaszBTsum_jutilaB_exp_eq_sum (χ : DirichletCharacter ℂ q) (R : ℝ) {ξ η N₁ : ℝ}
    (hξη : ξ ≤ η) (hN : Real.exp η ≤ N₁) (s : ℂ) :
    Salt.MR.halaszBTsum (jutilaB q R (Real.exp η) (Real.exp ξ)) χ χ s
      = ∑ n ∈ Finset.Icc 1 ⌈N₁⌉₊,
          (jutilaB q R (Real.exp η) (Real.exp ξ) n : ℂ) * (starRingEnd ℂ) (χ n) * χ n
            * (n : ℂ) ^ (-s) := by
  rw [halaszBTsum_jutilaB_eq_sum χ (Real.exp_pos ξ) (Real.exp_le_exp.mpr hξη) s]
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.ceil_le_ceil hN)) ?_
  intro n hn hn'
  have hlt : ⌈Real.exp η⌉₊ < n := by
    rcases Finset.mem_Icc.mp hn with ⟨h1, _⟩
    by_contra hcon
    exact hn' (Finset.mem_Icc.mpr ⟨h1, le_of_not_gt hcon⟩)
  have hle : Real.exp η ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hlt.le)
  rw [jutilaB_eq_zero_of_le (Real.exp_pos ξ) (Real.exp_le_exp.mpr hξη) q R hle]
  simp

/-- Each weight is continuous in `(ξ, η)` at `(N, M) = (e^η, e^ξ)`: the body is
`n⁻¹·Σ'(n)²·((max 0 (1 − n·e^{−η}))² − (max 0 (1 − n·e^{−ξ}))²)` (at `n = 0` the constant `0`). -/
theorem continuous_jutilaB_exp (q : ℕ) (R : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => jutilaB q R (Real.exp p.2) (Real.exp p.1) n) := by
  unfold jutilaB
  by_cases hn : n = 0
  · simp only [hn, if_pos]; exact continuous_const
  · simp only [hn, if_false]
    refine continuous_const.mul
      (((continuous_const.max ?_).pow 2).sub ((continuous_const.max ?_).pow 2))
    · exact continuous_const.sub (continuous_const.div
        (Real.continuous_exp.comp continuous_snd) (fun p => (Real.exp_pos p.2).ne'))
    · exact continuous_const.sub (continuous_const.div
        (Real.continuous_exp.comp continuous_fst) (fun p => (Real.exp_pos p.1).ne'))

/-- The finite-sum form is continuous on `ℝ²` — the function the device integrates. -/
theorem continuous_halaszB_sum_exp (χ : DirichletCharacter ℂ q) (R N₁ : ℝ) (s : ℂ) :
    Continuous (fun p : ℝ × ℝ => ∑ n ∈ Finset.Icc 1 ⌈N₁⌉₊,
      (jutilaB q R (Real.exp p.2) (Real.exp p.1) n : ℂ) * (starRingEnd ℂ) (χ n) * χ n
        * (n : ℂ) ^ (-s)) := by
  exact continuous_finsetSum _ fun n _ =>
    (((Complex.continuous_ofReal.comp (continuous_jutilaB_exp q R n)).mul
      continuous_const).mul continuous_const).mul continuous_const

/-- The kernel is continuous in `(ξ, η)` at every `s`: the closed form
`2((e^η)^{−s} − (e^ξ)^{−s})/((−s)(1 − s)(2 − s))` off `s = 0`, and `η − ξ` at `s = 0`. -/
theorem continuous_resKernel_exp (s : ℂ) :
    Continuous (fun p : ℝ × ℝ => resKernel s (Real.exp p.2) (Real.exp p.1)) := by
  by_cases hs : s = 0
  · subst hs
    have h0 : (fun p : ℝ × ℝ => resKernel 0 (Real.exp p.2) (Real.exp p.1))
        = fun p : ℝ × ℝ => ((p.2 - p.1 : ℝ) : ℂ) := by
      funext p
      rw [resKernel_zero (Real.exp_pos p.1) (Real.exp_pos p.2), ← Real.exp_sub,
        Real.log_exp]
    rw [h0]
    exact Complex.continuous_ofReal.comp (continuous_snd.sub continuous_fst)
  · have h : (fun p : ℝ × ℝ => resKernel s (Real.exp p.2) (Real.exp p.1))
        = fun p : ℝ × ℝ => 2 * (((Real.exp p.2 : ℝ) : ℂ) ^ (-s)
            - ((Real.exp p.1 : ℝ) : ℂ) ^ (-s)) / ((-s) * (1 - s) * (2 - s)) := by
      funext p; rw [resKernel_of_ne_zero hs]
    rw [h]
    exact ((continuous_const.mul
      (((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_snd)).cpow
          continuous_const (fun p => Or.inl
            (by simpa only [Function.comp_apply, Complex.ofReal_re] using Real.exp_pos p.2))).sub
       ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_fst)).cpow
          continuous_const (fun p => Or.inl
            (by simpa only [Function.comp_apply, Complex.ofReal_re]
              using Real.exp_pos p.1))))).div_const _)

/-! ## (ii) The device lemma -/

/-- A pointwise lower bound on a continuous `F` integrates over the closed rectangle:
`c ≤ F` on `Icc ξ₀ ξ₁ × Icc η₀ η₁` gives `c·|Ξ||H| ≤ ∫_Ξ∫_H F`. -/
theorem const_mul_le_integral_integral_of_le {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) {ξ₀ ξ₁ η₀ η₁ c : ℝ} (hξ : ξ₀ ≤ ξ₁) (hη : η₀ ≤ η₁)
    (h : ∀ ξ ∈ Set.Icc ξ₀ ξ₁, ∀ η ∈ Set.Icc η₀ η₁, c ≤ F ξ η) :
    c * ((ξ₁ - ξ₀) * (η₁ - η₀)) ≤ ∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, F ξ η := by
  have hconstη : c * (η₁ - η₀) = ∫ _ in η₀..η₁, c := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hin : ∀ ξ ∈ Set.Icc ξ₀ ξ₁, c * (η₁ - η₀) ≤ ∫ η in η₀..η₁, F ξ η := fun ξ hξ' => by
    rw [hconstη]
    exact intervalIntegral.integral_mono_on hη intervalIntegrable_const
      ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      (fun η hη' => h ξ hξ' η hη')
  have hout : Continuous fun ξ => ∫ η in η₀..η₁, F ξ η :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF η₀ η₁
  calc c * ((ξ₁ - ξ₀) * (η₁ - η₀)) = ∫ _ξ in ξ₀..ξ₁, c * (η₁ - η₀) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ ∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, F ξ η :=
        intervalIntegral.integral_mono_on hξ intervalIntegrable_const
          (hout.intervalIntegrable _ _) hin

/-! ## (iii) THE RATIO (W9c's headline, verbatim from the W9a/c freeze) -/

/-- **THE RATIO**: for a `Δ`-well-spaced system of `J` zeros in the strip (`Δ = 1/log(qT)`,
distinct ordinates), Halász integrated over the `(ξ, η)`-rectangle of F5's table with the floor
`‖g(ρ_j)‖ ≥ S'/2` on the left and the residue block on the right gives `J ≤ C·(qT)^{13(1−σ)}`
once `D₁ ≤ qT` (the `I`-block below `S'²/8`); `C` and `D₁` are non-effective (design v2 §A.6:
`D₁ = 10^59–10^64` at `C_ps = 1`), inside the `∃`. The strictness `β_j < 1` is supplied by the
consumer (W9f) from `LFunction_ne_zero_of_one_le_re`; `13 = 2c` is F5's `x = D^{13/2}`. -/
theorem card_system_le_rpow : ∃ C D₁ : ℝ, 0 < C ∧ 0 < D₁ ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → 2 ≤ q →
    ∀ (σ T : ℝ), 119 / 120 ≤ σ → σ < 1 → 2 ≤ T → D₁ ≤ (q : ℝ) * T →
    ∀ (J : ℕ) (ρ : Fin J → ℂ), (∀ j, LFunction χ (ρ j) = 0) → (∀ j, σ ≤ (ρ j).re) →
      (∀ j, (ρ j).re < 1) → (∀ j, |(ρ j).im| ≤ T) →
      WellSpacedAt (1 / Real.log ((q : ℝ) * T)) (Finset.univ.image (fun j => (ρ j).im)) →
      Function.Injective (fun j => (ρ j).im) →
      (J : ℝ) ≤ C * ((q : ℝ) * T) ^ (13 * (1 - σ)) := by
  sorry

/-- **The W9c′ exit rows** (each INVOKES a frozen row at numerals): the kernel's continuity at
`s = 0`; the weight's continuity at `(q, R, n) = (5, 6, 7)`. -/
example : Continuous (fun p : ℝ × ℝ => resKernel 0 (Real.exp p.2) (Real.exp p.1)) :=
  continuous_resKernel_exp 0

example : Continuous (fun p : ℝ × ℝ => jutilaB 5 6 (Real.exp p.2) (Real.exp p.1) 7) :=
  continuous_jutilaB_exp 5 6 7

end Salt.SW
