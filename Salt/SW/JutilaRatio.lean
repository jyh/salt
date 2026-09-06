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

/-- The threshold as a LIMIT. -/
private lemma exists_threshold (K : ℝ) (hK : 0 < K) :
    ∃ D₁ : ℝ, 0 < D₁ ∧ ∀ D : ℝ, D₁ ≤ D →
      K * (D ^ (-(17 / 120) : ℝ) * (1 + Real.log D / 10) ^ 2) ≤ 2 / 10 ^ 4 := by
  have hlim : Filter.Tendsto (fun D : ℝ => 121 * K * D ^ (-(73 / 600) : ℝ))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (y := (73 / 600 : ℝ)) (by norm_num)).const_mul (121 * K)
    simpa using h
  have hev : ∀ᶠ D : ℝ in Filter.atTop, 121 * K * D ^ (-(73 / 600) : ℝ) ≤ 2 / 10 ^ 4 :=
    hlim.eventually_le_const (by norm_num)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max a 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun D hD => ?_⟩
  have hD1 : (1 : ℝ) ≤ D := le_trans (le_max_right _ _) hD
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hD1
  have hcen : (1 : ℝ) ≤ D ^ ((1 / 100 : ℝ)) := Real.one_le_rpow hD1 (by norm_num)
  have hlog : Real.log D ≤ 100 * D ^ ((1 / 100 : ℝ)) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hD0 ((1 : ℝ) / 100))
    rw [Real.log_rpow hD0] at h
    linarith
  have h1 : (1 : ℝ) + Real.log D / 10 ≤ 11 * D ^ ((1 / 100 : ℝ)) := by linarith
  have h0 : (0 : ℝ) ≤ 1 + Real.log D / 10 := by
    have := Real.log_nonneg hD1
    linarith
  have h2 : (1 + Real.log D / 10) ^ 2 ≤ 121 * D ^ ((1 / 50 : ℝ)) := by
    have hsq : (1 + Real.log D / 10) ^ 2 ≤ (11 * D ^ ((1 / 100 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    have hexp : (11 * D ^ ((1 / 100 : ℝ))) ^ 2 = 121 * D ^ ((1 / 50 : ℝ)) := by
      rw [mul_pow, ← Real.rpow_natCast (D ^ ((1 / 100 : ℝ))) 2, ← Real.rpow_mul hD0.le]
      norm_num
    linarith [hexp ▸ hsq]
  have hrp : (0 : ℝ) < D ^ (-(17 / 120) : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hadd : D ^ (-(17 / 120) : ℝ) * D ^ ((1 / 50 : ℝ)) = D ^ (-(73 / 600) : ℝ) := by
    rw [← Real.rpow_add hD0]
    norm_num
  have hcol : D ^ (-(17 / 120) : ℝ) * (121 * D ^ ((1 / 50 : ℝ)))
      = 121 * D ^ (-(73 / 600) : ℝ) := by
    calc D ^ (-(17 / 120) : ℝ) * (121 * D ^ ((1 / 50 : ℝ)))
        = 121 * (D ^ (-(17 / 120) : ℝ) * D ^ ((1 / 50 : ℝ))) := by ring
      _ = 121 * D ^ (-(73 / 600) : ℝ) := by rw [hadd]
  have hchain : D ^ (-(17 / 120) : ℝ) * (1 + Real.log D / 10) ^ 2
      ≤ 121 * D ^ (-(73 / 600) : ℝ) := by
    calc D ^ (-(17 / 120) : ℝ) * (1 + Real.log D / 10) ^ 2
        ≤ D ^ (-(17 / 120) : ℝ) * (121 * D ^ ((1 / 50 : ℝ))) := by
          exact mul_le_mul_of_nonneg_left h2 hrp.le
      _ = 121 * D ^ (-(73 / 600) : ℝ) := hcol
  have := ha D (le_trans (le_max_left _ _) hD)
  nlinarith [mul_le_mul_of_nonneg_left hchain hK.le]

/-- `‖∏_{p ∣ q}(1 − p⁻¹)‖ = φ(q)/q` — the cancellation of `φ(q)/q` between Halász's two sides. -/
private lemma norm_prod_one_sub_inv_le_totient_div (q : ℕ) (hq : 1 ≤ q) :
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)‖ ≤ (Nat.totient q : ℝ) / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hppos : (0 : ℝ) < ∏ p ∈ q.primeFactors, (p : ℝ) :=
    Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hcast : ∏ p ∈ q.primeFactors, (((p - 1 : ℕ)) : ℝ)
      = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) :=
    Finset.prod_congr rfl fun p hp => by
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hkey : (Nat.totient q : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ)
      = (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have h := Nat.totient_mul_prod_primeFactors q
    calc (Nat.totient q : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ)
        = ((Nat.totient q * ∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by push_cast; ring
      _ = ((q * ∏ p ∈ q.primeFactors, (p - 1) : ℕ) : ℝ) := by rw [h]
      _ = (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_prod, hcast]
  have hprodform : ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ))
      = (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) / ∏ p ∈ q.primeFactors, (p : ℝ) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    field_simp
  have heq : (Nat.totient q : ℝ) / q = ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ)) := by
    rw [hprodform, div_eq_div_iff hq0.ne' hppos.ne']
    linarith [hkey]
  rw [heq, Complex.norm_prod]
  refine le_of_eq (Finset.prod_congr rfl fun p hp => ?_)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hrw : (1 - (p : ℂ)⁻¹) = ((1 - 1 / (p : ℝ) : ℝ) : ℂ) := by
    push_cast
    rw [one_div]
  have hnn : (0 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
    linarith
  rw [hrw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]

/-- The double integral of a finite sum of continuous functions. -/
private lemma integral_integral_finsetSum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℂ)
    (hF : ∀ i ∈ s, Continuous (Function.uncurry (F i))) (ξ₀ ξ₁ η₀ η₁ : ℝ) :
    (∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, ∑ i ∈ s, F i ξ η)
      = ∑ i ∈ s, ∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, F i ξ η := by
  have hinner : ∀ ξ : ℝ, (∫ η in η₀..η₁, ∑ i ∈ s, F i ξ η)
      = ∑ i ∈ s, ∫ η in η₀..η₁, F i ξ η := fun ξ =>
    intervalIntegral.integral_finsetSum (fun i hi =>
      (((hF i hi).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _))
  simp only [hinner]
  exact intervalIntegral.integral_finsetSum (fun i hi =>
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (hF i hi) η₀ η₁).intervalIntegrable _ _))

/-- The `.re` moves out of both integrals. -/
private lemma integral_integral_re {F : ℝ → ℝ → ℂ} (hF : Continuous (Function.uncurry F))
    (ξ₀ ξ₁ η₀ η₁ : ℝ) :
    (∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, (F ξ η).re)
      = (∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, F ξ η).re := by
  have hin : ∀ ξ : ℝ, (∫ η in η₀..η₁, (F ξ η).re) = (∫ η in η₀..η₁, F ξ η).re := by
    intro ξ
    have hi : IntervalIntegrable (fun η => F ξ η) volume η₀ η₁ :=
      (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have h := intervalIntegral.intervalIntegral_re hi
    simpa only [RCLike.re_eq_complex_re] using h
  simp only [hin]
  have ho : IntervalIntegrable (fun ξ => ∫ η in η₀..η₁, F ξ η) volume ξ₀ ξ₁ :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hF η₀ η₁).intervalIntegrable _ _
  have h := intervalIntegral.intervalIntegral_re ho
  simpa only [RCLike.re_eq_complex_re] using h

/-- A double integral splits off a comparison function with a uniform remainder bound. -/
private lemma norm_integral_integral_le_of_sub {F G : ℝ → ℝ → ℂ}
    (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G))
    {ξ₀ ξ₁ η₀ η₁ Cb : ℝ} (hξ : ξ₀ ≤ ξ₁) (hη : η₀ ≤ η₁)
    (h : ∀ ξ ∈ Set.uIoc ξ₀ ξ₁, ∀ η ∈ Set.uIoc η₀ η₁, ‖F ξ η - G ξ η‖ ≤ Cb) :
    ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, F ξ η‖
      ≤ ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, G ξ η‖ + Cb * ((ξ₁ - ξ₀) * (η₁ - η₀)) := by
  have hFi : ∀ ξ : ℝ, IntervalIntegrable (fun η => F ξ η) volume η₀ η₁ := fun ξ =>
    (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hGi : ∀ ξ : ℝ, IntervalIntegrable (fun η => G ξ η) volume η₀ η₁ := fun ξ =>
    (hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hFo : Continuous fun ξ => ∫ η in η₀..η₁, F ξ η :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF η₀ η₁
  have hGo : Continuous fun ξ => ∫ η in η₀..η₁, G ξ η :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG η₀ η₁
  have hinner : ∀ ξ ∈ Set.uIoc ξ₀ ξ₁,
      ‖(∫ η in η₀..η₁, F ξ η) - ∫ η in η₀..η₁, G ξ η‖ ≤ Cb * (η₁ - η₀) := by
    intro ξ hξm
    rw [← intervalIntegral.integral_sub (hFi ξ) (hGi ξ)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun η => F ξ η - G ξ η) (C := Cb) (fun η hηm => h ξ hξm η hηm)
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ η₁ - η₀)] at this
  have houter : ‖(∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, F ξ η)
      - ∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, G ξ η‖ ≤ Cb * (η₁ - η₀) * (ξ₁ - ξ₀) := by
    rw [← intervalIntegral.integral_sub (hFo.intervalIntegrable _ _) (hGo.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun ξ => (∫ η in η₀..η₁, F ξ η) - ∫ η in η₀..η₁, G ξ η)
      (C := Cb * (η₁ - η₀)) (fun ξ hξm => hinner ξ hξm)
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ξ₁ - ξ₀)] at this
  have hsplit := norm_sub_norm_le (∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, F ξ η)
    (∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, G ξ η)
  nlinarith [houter, hsplit]

/-- The constant pulls out of a double integral. -/
private lemma integral_integral_const_mul (c : ℂ) (F : ℝ → ℝ → ℂ) (ξ₀ ξ₁ η₀ η₁ : ℝ) :
    (∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, c * F ξ η)
      = c * ∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, F ξ η := by
  simp only [intervalIntegral.integral_const_mul]


/-- `‖∫∫ F‖ ≤ ∫∫ ‖F‖` for a continuous `F`. -/
private lemma norm_ii_le_ii_norm {F : ℝ → ℝ → ℂ}
    (hF : Continuous (Function.uncurry F)) {ξ₀ ξ₁ η₀ η₁ : ℝ} (hξ : ξ₀ ≤ ξ₁) (hη : η₀ ≤ η₁) :
    ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, F ξ η‖ ≤ ∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, ‖F ξ η‖ := by
  have h1 : ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, F ξ η‖
      ≤ ∫ ξ in ξ₀..ξ₁, ‖∫ η in η₀..η₁, F ξ η‖ :=
    intervalIntegral.norm_integral_le_integral_norm hξ
  have hi1 : IntervalIntegrable (fun ξ => ‖∫ η in η₀..η₁, F ξ η‖) volume ξ₀ ξ₁ :=
    (continuous_norm.comp (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hF η₀ η₁)).intervalIntegrable _ _
  have hFn : Continuous (Function.uncurry (fun ξ η => ‖F ξ η‖)) := continuous_norm.comp hF
  have hi2 : IntervalIntegrable (fun ξ => ∫ η in η₀..η₁, ‖F ξ η‖) volume ξ₀ ξ₁ :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hFn η₀ η₁).intervalIntegrable _ _
  have h2 : (∫ ξ in ξ₀..ξ₁, ‖∫ η in η₀..η₁, F ξ η‖)
      ≤ ∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, ‖F ξ η‖ :=
    intervalIntegral.integral_mono_on hξ hi1 hi2
      (fun ξ _ => intervalIntegral.norm_integral_le_integral_norm hη)
  linarith

/-! ## (iii) THE RATIO (W9c's headline, verbatim from the W9a/c freeze) -/

set_option maxHeartbeats 1000000 in
-- the assembly is one declaration with ~90 staged `have`s over the rectangle; the default
-- 200 000 heartbeats are exhausted in the elaboration of its `set` locals alone
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
  classical
  obtain ⟨Cps, hCps, hps⟩ := sum_sq_sum_bvWeight_mul_rpow_le
  obtain ⟨Dt, hDt0, hDt⟩ := exists_threshold (60000 * Cps) (by positivity)
  refine ⟨10 ^ 8 * Cps, max (10 ^ 20) Dt, by positivity,
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro q _ χ hχ hq σ T hσ hσ1 hT hDT J ρ hzero hβ hβ1 hρT hws hinj
  rcases Nat.eq_zero_or_pos J with rfl | hJpos
  · rw [Nat.cast_zero]; positivity
  have hq1 : 1 ≤ q := by omega
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hT1 : (1 : ℝ) ≤ T := by linarith
  set D : ℝ := (q : ℝ) * T with hDdef
  have hD0 : (10 : ℝ) ^ 20 ≤ D := le_trans (le_max_left _ _) hDT
  have hDth : Dt ≤ D := le_trans (le_max_right _ _) hDT
  have hD1 : (1 : ℝ) ≤ D := by linarith only [hD0]
  have hDpos : (0 : ℝ) < D := by linarith only [hD1]
  set L : ℝ := Real.log D with hLdef
  have hL : (46 : ℝ) ≤ L := by
    have h10 : Real.log 10 = Real.log 2 + Real.log 5 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have hbase : (46 : ℝ) ≤ Real.log ((10 : ℝ) ^ 20) := by
      rw [Real.log_pow, h10]
      have h2 := Real.log_two_gt_d9
      have h5 := Real.log_five_gt_d9
      push_cast
      linarith only [h2, h5]
    exact le_trans hbase (Real.log_le_log (by norm_num) hD0)
  have hLpos : (0 : ℝ) < L := by linarith only [hL]
  have hqD : (q : ℝ) ≤ D := by
    have h := mul_nonneg (by linarith only [hq1R] : (0 : ℝ) ≤ (q : ℝ))
      (by linarith only [hT1] : (0 : ℝ) ≤ T - 1)
    rw [hDdef]; linarith only [h]
  set R : ℝ := D ^ ((1 : ℝ) / 10) with hRdef
  set x : ℝ := D ^ ((13 : ℝ) / 2) with hxdef
  have hR1 : (1 : ℝ) ≤ R := Real.one_le_rpow hD1 (by norm_num)
  have hlogR : Real.log R = 1 / 10 * L := Real.log_rpow hDpos _
  have hlogRnn : (0 : ℝ) ≤ Real.log R := by rw [hlogR]; linarith only [hLpos]
  have hx1 : (1 : ℝ) ≤ x := Real.one_le_rpow hD1 (by norm_num)
  have hlogx : Real.log x = 13 / 2 * L := Real.log_rpow hDpos _
  have hD3big : (10 : ℝ) ^ 20 ≤ D ^ (3 : ℝ) := by
    have h : D ^ (1 : ℝ) ≤ D ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num)
    rw [Real.rpow_one] at h; linarith only [h, hD0]
  have hD3pos : (0 : ℝ) < D ^ (3 : ℝ) := by linarith only [hD3big]
  have hhalf : (2 : ℝ) ≤ D ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow, show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith only [hD0])
  have hsplit : D ^ ((7 : ℝ) / 2) = D ^ (3 : ℝ) * D ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add hDpos]; norm_num
  set z₁ : ℕ := ⌊D ^ (3 : ℝ)⌋₊ with hz₁def
  set z₂ : ℕ := ⌊D ^ ((7 : ℝ) / 2)⌋₊ with hz₂def
  have hz₁le : (z₁ : ℝ) ≤ D ^ (3 : ℝ) := Nat.floor_le (by linarith only [hD3pos])
  have hz₁lo : D ^ (3 : ℝ) - 1 ≤ (z₁ : ℝ) := by
    have h := Nat.lt_floor_add_one (D ^ (3 : ℝ)); rw [← hz₁def] at h; linarith only [h]
  have h72pos : (0 : ℝ) < D ^ ((7 : ℝ) / 2) := by
    rw [hsplit]; nlinarith only [hD3pos, hhalf]
  have hz₂le : (z₂ : ℝ) ≤ D ^ ((7 : ℝ) / 2) := Nat.floor_le (by linarith only [h72pos])
  have hz₂lo : D ^ ((7 : ℝ) / 2) - 1 ≤ (z₂ : ℝ) := by
    have h := Nat.lt_floor_add_one (D ^ ((7 : ℝ) / 2)); rw [← hz₂def] at h; linarith only [h]
  have hz₁2 : 2 ≤ z₁ := Nat.le_floor (by push_cast; linarith only [hD3big])
  have hz₁2R : (2 : ℝ) ≤ (z₁ : ℝ) := by exact_mod_cast hz₁2
  have hz₁pos : (0 : ℝ) < (z₁ : ℝ) := by linarith only [hz₁2R]
  have hprodD : D ^ (3 : ℝ) * 2 ≤ D ^ (3 : ℝ) * D ^ ((1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_left hhalf (by linarith only [hD3pos])
  have hz₁lt : z₁ < z₂ := by
    have h : ((z₁ + 1 : ℕ) : ℝ) ≤ D ^ ((7 : ℝ) / 2) := by
      push_cast
      linarith only [hprodD, hsplit, hz₁le, hD3big]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self z₁) (Nat.le_floor h)
  have hz₂2R : (2 : ℝ) ≤ (z₂ : ℝ) := by
    have : (z₁ : ℝ) ≤ (z₂ : ℝ) := by exact_mod_cast hz₁lt.le
    linarith only [this, hz₁2R]
  have hz₂pos : (0 : ℝ) < (z₂ : ℝ) := by linarith only [hz₂2R]
  have hz₂x : (z₂ : ℝ) ≤ x := by
    refine le_trans hz₂le ?_
    rw [hxdef]
    exact Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num)
  set ξ₁ : ℝ := Real.log (z₁ : ℝ) with hξ₁def
  set ξ₀ : ℝ := (1 - 1 / 120) * ξ₁ with hξ₀def
  set η₀ : ℝ := Real.log (2 * x) with hη₀def
  set η₁ : ℝ := η₀ + (13 / 240 : ℝ) * L with hη₁def
  have hη₀eq : η₀ = Real.log 2 + 13 / 2 * L := by
    rw [hη₀def, Real.log_mul (by norm_num) (by linarith only [hx1]), hlogx]
  have hlog2lo : (0.6931 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlog2hi : Real.log 2 ≤ 0.694 := by linarith only [Real.log_two_lt_d9]
  have hξ₁hi : ξ₁ ≤ 3 * L := by
    rw [hξ₁def]
    have h := Real.log_le_log hz₁pos hz₁le
    rwa [Real.log_rpow hDpos] at h
  have hξ₁lo : 3 * L - 0.694 ≤ ξ₁ := by
    have hhalfD : D ^ (3 : ℝ) / 2 ≤ (z₁ : ℝ) := by linarith only [hz₁lo, hD3big]
    have h1 : Real.log (D ^ (3 : ℝ) / 2) ≤ ξ₁ := by
      rw [hξ₁def]; exact Real.log_le_log (by linarith only [hD3big]) hhalfD
    rw [Real.log_div (ne_of_gt hD3pos) (by norm_num), Real.log_rpow hDpos] at h1
    linarith only [h1, hlog2hi]
  have hξ₀lo : (29 / 10 : ℝ) * L ≤ ξ₀ := by rw [hξ₀def]; linarith only [hξ₁lo, hL]
  have hξ₀0 : (0 : ℝ) ≤ ξ₀ := by linarith only [hξ₀lo, hLpos]
  have hξ₀hi : ξ₀ ≤ 3 * L := by rw [hξ₀def]; linarith only [hξ₁hi, hLpos]
  have hξ : ξ₀ ≤ ξ₁ := by rw [hξ₀def]; linarith only [hξ₁lo, hL]
  have hξη₀ : ξ₁ ≤ η₀ := by rw [hη₀eq]; linarith only [hξ₁hi, hlog2lo, hLpos]
  have hη : η₀ ≤ η₁ := by rw [hη₁def]; linarith only [hLpos]
  have hη₀0 : (0 : ℝ) ≤ η₀ := by rw [hη₀eq]; linarith only [hlog2lo, hLpos]
  set N₁ : ℝ := Real.exp η₁ with hN₁def
  have hMlo : ∀ ξ : ℝ, ξ₀ ≤ ξ → (2 : ℝ) ≤ Real.exp ξ := by
    intro ξ hξl
    have h : Real.exp (Real.log 2) ≤ Real.exp ξ :=
      Real.exp_le_exp.mpr (by linarith only [hξl, hξ₀lo, hlog2hi, hL])
    rwa [Real.exp_log (by norm_num)] at h
  have hMz₁ : ∀ ξ : ℝ, ξ ≤ ξ₁ → Real.exp ξ ≤ (z₁ : ℝ) := by
    intro ξ hξr
    have h : Real.exp ξ ≤ Real.exp ξ₁ := Real.exp_le_exp.mpr hξr
    rwa [hξ₁def, Real.exp_log hz₁pos] at h
  have hNlo : ∀ η : ℝ, η₀ ≤ η → 2 * x ≤ Real.exp η := by
    intro η hηl
    have h : Real.exp η₀ ≤ Real.exp η := Real.exp_le_exp.mpr hηl
    rwa [hη₀def, Real.exp_log (by linarith only [hx1])] at h
  have hNhi : ∀ η : ℝ, η ≤ η₁ → Real.exp η ≤ N₁ := fun η hηr => Real.exp_le_exp.mpr hηr
  have hMN : ∀ ξ η : ℝ, ξ ≤ ξ₁ → η₀ ≤ η → Real.exp ξ ≤ Real.exp η := by
    intro ξ η h1 h2
    exact Real.exp_le_exp.mpr (by linarith only [h1, h2, hξη₀])
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  -- ## the coprime harmonic sum
  set Sp : ℝ := ∑ r ∈ rFilter q R, (r : ℝ)⁻¹ with hSpdef
  set Φ : ℝ := (Nat.totient q : ℝ) / (q : ℝ) with hΦdef
  have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith only [hq1R]
  have hΦpos : (0 : ℝ) < Φ := by rw [hΦdef]; exact div_pos hφpos hqpos
  have hΦ1 : Φ ≤ 1 := by
    rw [hΦdef, div_le_one hqpos]
    exact_mod_cast Nat.totient_le q
  have hSpl : 6 / Real.pi ^ 2 * Φ * Real.log R ≤ Sp := by
    have h := sum_sf_coprime_inv_ge q R hq1 hR1
    simp only [one_div] at h
    exact h
  have hpi0 : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hpihi : Real.pi ^ 2 ≤ 99225 / 10000 := by
    nlinarith only [Real.pi_lt_d2, Real.pi_gt_three]
  have hlogq : Real.log (q : ℝ) ≤ L := Real.log_le_log hqpos hqD
  have hlogqnn : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1R
  have hWpos : (0 : ℝ) < 29 / 20 * L + 1 := by linarith only [hLpos]
  have hden : Real.log (q : ℝ) / Real.log 2 + 1 ≤ 29 / 20 * L + 1 := by
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith only [hlog2lo]
    have h : Real.log (q : ℝ) / Real.log 2 ≤ 29 / 20 * L := by
      rw [div_le_iff₀ hl2]
      nlinarith only [hlogq, hlogqnn, hlog2lo, hLpos]
    linarith only [h]
  have hΦlo : 1 / (29 / 20 * L + 1) ≤ Φ := by
    have hnn : (0 : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 :=
      div_nonneg hlogqnn (by linarith only [hlog2lo])
    refine le_trans ?_ (inv_log_le_totient_div hq1)
    exact one_div_le_one_div_of_le (by linarith only [hnn]) hden
  have hpi6 : (6 : ℝ) / (99225 / 10000) ≤ 6 / Real.pi ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) hpi0 hpihi
  have hSp : (4 : ℝ) / 100 ≤ Sp := by
    have hkey : (4 : ℝ) / 100
        ≤ 6 / (99225 / 10000) * (1 / (29 / 20 * L + 1)) * (1 / 10 * L) := by
      have he : (6 : ℝ) / (99225 / 10000) * (1 / (29 / 20 * L + 1)) * (1 / 10 * L)
          = (6 / (99225 / 10000) * (1 / 10 * L)) / (29 / 20 * L + 1) := by
        field_simp
      rw [he, le_div_iff₀ hWpos]
      linarith only [hL]
    have h1 : (6 : ℝ) / (99225 / 10000) * (1 / (29 / 20 * L + 1)) ≤ 6 / Real.pi ^ 2 * Φ :=
      mul_le_mul hpi6 hΦlo (by positivity) (by positivity)
    have h2 : (6 : ℝ) / (99225 / 10000) * (1 / (29 / 20 * L + 1)) * (1 / 10 * L)
        ≤ 6 / Real.pi ^ 2 * Φ * (1 / 10 * L) :=
      mul_le_mul_of_nonneg_right h1 (by linarith only [hLpos])
    rw [hlogR] at hSpl
    linarith only [hkey, h2, hSpl]
  have hSppos : (0 : ℝ) < Sp := by linarith only [hSp]
  -- ## the partial summation
  set Am : ℝ := 4 * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2 * (n : ℝ) ^ (1 - 2 * σ) with hAmdef
  set xp : ℝ := x ^ (2 - 2 * σ) with hxpdef
  have hxp1 : (1 : ℝ) ≤ xp := Real.one_le_rpow hx1 (by linarith)
  have hxpnn : (0 : ℝ) ≤ xp := by linarith only [hxp1]
  have hlz₂ : Real.log (z₂ : ℝ) ≤ 7 / 2 * L := by
    have h := Real.log_le_log hz₂pos hz₂le
    rwa [Real.log_rpow hDpos] at h
  have h72two : (2 : ℝ) ≤ D ^ ((7 : ℝ) / 2) := by
    rw [hsplit]; nlinarith only [hD3big, hhalf, hD3pos]
  have hlz₂lo : 7 / 2 * L - 0.694 ≤ Real.log (z₂ : ℝ) := by
    have hhalfD : D ^ ((7 : ℝ) / 2) / 2 ≤ (z₂ : ℝ) := by linarith only [hz₂lo, h72two]
    have h1 : Real.log (D ^ ((7 : ℝ) / 2) / 2) ≤ Real.log (z₂ : ℝ) :=
      Real.log_le_log (by linarith only [h72two]) hhalfD
    rw [Real.log_div (ne_of_gt h72pos) (by norm_num), Real.log_rpow hDpos] at h1
    linarith only [h1, hlog2hi]
  have hlz₂nn : (0 : ℝ) ≤ Real.log (z₂ : ℝ) := by linarith only [hlz₂lo, hL]
  have hlratio : (48 / 100 : ℝ) * L ≤ Real.log ((z₂ : ℝ) / (z₁ : ℝ)) := by
    rw [Real.log_div (ne_of_gt hz₂pos) (ne_of_gt hz₁pos), ← hξ₁def]
    linarith only [hlz₂lo, hξ₁hi, hL]
  have hBpos : (0 : ℝ) < Real.log ((z₂ : ℝ) / (z₁ : ℝ)) ^ 2 := by
    have h : (0 : ℝ) < Real.log ((z₂ : ℝ) / (z₁ : ℝ)) := by linarith only [hlratio, hLpos]
    positivity
  have hBlo : (2304 / 10000 : ℝ) * L ^ 2 ≤ Real.log ((z₂ : ℝ) / (z₁ : ℝ)) ^ 2 := by
    nlinarith only [hlratio, hLpos]
  have hAmub : Am ≤ 700 * Cps * xp := by
    have hpsb := hps z₁ z₂ hz₁2 hz₁lt x σ hz₂x (by linarith) (by linarith)
    rw [← hxpdef] at hpsb
    have hV : (1 + Real.log x) * xp + Real.log (z₂ : ℝ) ≤ 1003 / 100 * L * xp := by
      have h1 : 1 + Real.log x ≤ 653 / 100 * L := by rw [hlogx]; linarith only [hL]
      nlinarith only [h1, hxp1, hlz₂, hLpos, hxpnn]
    have hVnn : (0 : ℝ) ≤ (1 + Real.log x) * xp + Real.log (z₂ : ℝ) := by
      have h1 : (0 : ℝ) ≤ 1 + Real.log x := by rw [hlogx]; linarith only [hLpos]
      nlinarith only [h1, hxpnn, hlz₂nn]
    have hLxp : (0 : ℝ) ≤ L ^ 2 * xp := by positivity
    have hstep1 : Real.log (z₂ : ℝ) * ((1 + Real.log x) * xp + Real.log (z₂ : ℝ))
        ≤ (7 / 2 * L) * (1003 / 100 * L * xp) :=
      mul_le_mul hlz₂ hV hVnn (by linarith only [hLpos])
    have hstep2 : 175 * xp * ((2304 / 10000 : ℝ) * L ^ 2)
        ≤ 175 * xp * Real.log ((z₂ : ℝ) / (z₁ : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hBlo (by linarith only [hxpnn])
    have hGV : (Real.log (z₂ : ℝ) / Real.log ((z₂ : ℝ) / (z₁ : ℝ)) ^ 2)
        * ((1 + Real.log x) * xp + Real.log (z₂ : ℝ)) ≤ 175 * xp := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hBpos]
      linarith only [hstep1, hstep2, hLxp]
    have h1 : Cps * (Real.log (z₂ : ℝ) / Real.log ((z₂ : ℝ) / (z₁ : ℝ)) ^ 2)
        * ((1 + Real.log x) * xp + Real.log (z₂ : ℝ)) ≤ Cps * (175 * xp) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hGV (le_of_lt hCps)
    rw [hAmdef]
    linarith only [hpsb, h1]
  have hAmnn : (0 : ℝ) ≤ Am := by
    rw [hAmdef]
    have : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2 * (n : ℝ) ^ (1 - 2 * σ) :=
      Finset.sum_nonneg fun n _ => by positivity
    linarith only [this]
  -- ## the unimodular witnesses and the finite-sum form
  have hfl : ∀ j, Sp / 2 ≤ ‖jutilaDetector χ z₁ z₂ R x (ρ j)‖ := fun j =>
    jutilaDetector_floor_half_sum hχ hq hz₁2 hz₁lt hT1 hDdef hD0 hRdef hz₂le le_rfl
      (hzero j) (le_trans hσ (hβ j)) (hβ1 j) (hρT j)
  choose u hu1 hu2 using fun j =>
    Salt.MR.exists_unimodular_mul_eq_norm (jutilaDetector χ z₁ z₂ R x (ρ j))
  set Bt : Fin J → Fin J → ℝ → ℝ → ℂ := fun j k ξ η =>
    ∑ n ∈ Finset.Icc 1 ⌈N₁⌉₊,
      (jutilaB q R (Real.exp η) (Real.exp ξ) n : ℂ) * (starRingEnd ℂ) (χ n) * χ n
        * (n : ℂ) ^ (-((starRingEnd ℂ) (ρ j - σ) + (ρ k - σ))) with hBtdef
  set Kf : Fin J → Fin J → ℝ → ℝ → ℂ := fun j k ξ η =>
    resKernel ((starRingEnd ℂ) (ρ j - σ) + (ρ k - σ)) (Real.exp η) (Real.exp ξ) with hKfdef
  set Fc : ℝ → ℝ → ℂ := fun ξ η => ∑ j, ∑ k, (starRingEnd ℂ) (u j) * u k * Bt j k ξ η with hFcdef
  have hBtc : ∀ j k, Continuous (Function.uncurry (Bt j k)) := fun j k =>
    continuous_halaszB_sum_exp χ R N₁ _
  have hKfc : ∀ j k, Continuous (Function.uncurry (Kf j k)) := fun j k =>
    continuous_resKernel_exp _
  have hFcc : Continuous (Function.uncurry Fc) :=
    continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
      continuous_const.mul (hBtc j k)
  -- ## the pointwise Halász instance
  have hSpnn : (0 : ℝ) ≤ Sp := le_of_lt hSppos
  have hJSnn : (0 : ℝ) ≤ (J : ℝ) * (Sp / 2) :=
    mul_nonneg (Nat.cast_nonneg J) (by linarith only [hSpnn])
  have hJR : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJpos
  have hsqpos : (0 : ℝ) < ((J : ℝ) * Sp / 2) ^ 2 := by
    have : (0 : ℝ) < (J : ℝ) * Sp / 2 := by
      have := mul_pos (by linarith only [hJR] : (0:ℝ) < (J:ℝ)) hSppos
      linarith only [this]
    positivity
  have hcore : ∀ ξ : ℝ, ξ₀ ≤ ξ → ξ ≤ ξ₁ → ∀ η : ℝ, η₀ ≤ η → η ≤ η₁ →
      ∃ A : ℝ, 0 ≤ A ∧ A ≤ Am ∧ ((J : ℝ) * Sp / 2) ^ 2 ≤ A * (Fc ξ η).re := by
    intro ξ hξl hξr η hηl hηr
    have hM2 : (2 : ℝ) ≤ Real.exp ξ := hMlo ξ hξl
    have hM1 : (1 : ℝ) ≤ Real.exp ξ := by linarith only [hM2]
    have hM0 : (0 : ℝ) < Real.exp ξ := Real.exp_pos ξ
    have hMNe : Real.exp ξ ≤ Real.exp η := hMN ξ η hξr hηl
    have hMz : Real.exp ξ ≤ (z₁ : ℝ) := hMz₁ ξ hξr
    have hxNe : 2 * x ≤ Real.exp η := hNlo η hηl
    have hξηle : ξ ≤ η := by linarith only [hξr, hηl, hξη₀]
    have hηN : Real.exp η ≤ N₁ := hNhi η hηr
    refine ⟨∑ n ∈ Finset.Ioc z₁ ⌊x⌋₊,
      ‖jutilaA q z₁ z₂ R x σ n‖ ^ 2 / jutilaB q R (Real.exp η) (Real.exp ξ) n, ?_, ?_, ?_⟩
    · exact Finset.sum_nonneg fun n _ =>
        div_nonneg (sq_nonneg _) (jutilaB_nonneg hM0 hMNe q R n)
    · exact sum_normSq_jutilaA_div_jutilaB_le hz₁2 hx1 hM1 hMNe hMz hxNe hσ0
    · have hhal := sq_sum_norm_jutilaDetector_le χ hz₁2 hx1 hM1 hMNe hMz hxNe hσ0 ρ u hu2
      have hrw : ∀ j k : Fin J,
          Salt.MR.halaszBTsum (jutilaB q R (Real.exp η) (Real.exp ξ)) χ χ
              ((starRingEnd ℂ) (ρ j - σ) + (ρ k - σ)) = Bt j k ξ η := fun j k =>
        halaszBTsum_jutilaB_exp_eq_sum χ R hξηle hηN _
      simp only [hrw] at hhal
      have hsum : (J : ℝ) * (Sp / 2) ≤ ∑ j, ‖jutilaDetector χ z₁ z₂ R x (ρ j)‖ := by
        have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hfl j)
        simpa using h
      have hsq : ((J : ℝ) * (Sp / 2)) ^ 2
          ≤ (∑ j, ‖jutilaDetector χ z₁ z₂ R x (ρ j)‖) ^ 2 := pow_le_pow_left₀ hJSnn hsum 2
      have heq : ((J : ℝ) * Sp / 2) ^ 2 = ((J : ℝ) * (Sp / 2)) ^ 2 := by ring
      rw [heq]
      exact le_trans hsq hhal
  have hAmpos : (0 : ℝ) < Am := by
    obtain ⟨A, hA0, hAM, hle⟩ := hcore ξ₀ le_rfl hξ η₀ le_rfl hη
    rcases eq_or_lt_of_le hA0 with h | h
    · rw [← h, zero_mul] at hle; linarith only [hle, hsqpos]
    · linarith only [h, hAM]
  have hpt : ∀ ξ : ℝ, ξ₀ ≤ ξ → ξ ≤ ξ₁ → ∀ η : ℝ, η₀ ≤ η → η ≤ η₁ →
      ((J : ℝ) * Sp / 2) ^ 2 / Am ≤ (Fc ξ η).re := by
    intro ξ h1 h2 η h3 h4
    obtain ⟨A, hA0, hAM, hle⟩ := hcore ξ h1 h2 η h3 h4
    rw [div_le_iff₀ hAmpos]
    have hQ : (0 : ℝ) < (Fc ξ η).re := by
      by_contra hc
      have hc' : (Fc ξ η).re ≤ 0 := not_lt.mp hc
      have hprod : (0 : ℝ) ≤ A * (-(Fc ξ η).re) := mul_nonneg hA0 (by linarith only [hc'])
      linarith only [hle, hsqpos, hprod]
    have : A * (Fc ξ η).re ≤ Am * (Fc ξ η).re :=
      mul_le_mul_of_nonneg_right hAM (le_of_lt hQ)
    linarith only [hle, this]
  -- ## the device
  have hFrc : Continuous (Function.uncurry (fun ξ η => (Fc ξ η).re)) :=
    Complex.continuous_re.comp hFcc
  have hdev : ((J : ℝ) * Sp / 2) ^ 2 / Am * ((ξ₁ - ξ₀) * (η₁ - η₀))
      ≤ ∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, (Fc ξ η).re :=
    const_mul_le_integral_integral_of_le hFrc hξ hη
      (fun ξ hξm η hηm => hpt ξ hξm.1 hξm.2 η hηm.1 hηm.2)
  -- ## the `I`-block's uniform bound over the rectangle
  set Ib : ℝ := 73 * D * (Real.exp ξ₀) ^ (-(1 / 2) : ℝ) * (R * (1 + Real.log R)) ^ 2 with hIbdef
  have hIbnn : (0 : ℝ) ≤ Ib := by
    rw [hIbdef]
    have h1 : (0 : ℝ) < (Real.exp ξ₀) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_pos_of_pos (Real.exp_pos _) _
    exact mul_nonneg (mul_nonneg (by linarith only [hDpos]) h1.le) (sq_nonneg _)
  have hexpξ₀ : (Real.exp ξ₀) ^ (-(1 / 2) : ℝ) ≤ D ^ (-(29 / 20) : ℝ) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos ξ₀), Real.log_exp,
      Real.rpow_def_of_pos hDpos, ← hLdef]
    exact Real.exp_le_exp.mpr (by linarith only [hξ₀lo])
  have hRsq : (R * (1 + Real.log R)) ^ 2 = D ^ ((1 : ℝ) / 5) * (1 + 1 / 10 * L) ^ 2 := by
    rw [hlogR, mul_pow, hRdef, ← Real.rpow_natCast (D ^ ((1 : ℝ) / 10)) 2,
      ← Real.rpow_mul hDpos.le]
    norm_num
  have hcollapse : D ^ (1 : ℝ) * D ^ (-(29 / 20) : ℝ) * D ^ ((1 : ℝ) / 5)
      = D ^ (-(1 / 4) : ℝ) := by
    rw [← Real.rpow_add hDpos, ← Real.rpow_add hDpos]; norm_num
  have hIbub : Ib ≤ 73 * (D ^ (-(1 / 4) : ℝ) * (1 + 1 / 10 * L) ^ 2) := by
    have hLterm : (0 : ℝ) ≤ D ^ ((1 : ℝ) / 5) * (1 + 1 / 10 * L) ^ 2 := by positivity
    have hstep : D * (Real.exp ξ₀) ^ (-(1 / 2) : ℝ) ≤ D * D ^ (-(29 / 20) : ℝ) :=
      mul_le_mul_of_nonneg_left hexpξ₀ hDpos.le
    have h1 : 73 * (D * (Real.exp ξ₀) ^ (-(1 / 2) : ℝ)) ≤ 73 * (D * D ^ (-(29 / 20) : ℝ)) := by
      linarith only [hstep]
    have h2 := mul_le_mul_of_nonneg_right h1 hLterm
    rw [hIbdef, hRsq]
    calc 73 * D * (Real.exp ξ₀) ^ (-(1 / 2) : ℝ) * (D ^ ((1 : ℝ) / 5) * (1 + 1 / 10 * L) ^ 2)
        = 73 * (D * (Real.exp ξ₀) ^ (-(1 / 2) : ℝ))
            * (D ^ ((1 : ℝ) / 5) * (1 + 1 / 10 * L) ^ 2) := by ring
      _ ≤ 73 * (D * D ^ (-(29 / 20) : ℝ)) * (D ^ ((1 : ℝ) / 5) * (1 + 1 / 10 * L) ^ 2) := h2
      _ = 73 * (D ^ (1 : ℝ) * D ^ (-(29 / 20) : ℝ) * D ^ ((1 : ℝ) / 5)
            * (1 + 1 / 10 * L) ^ 2) := by rw [Real.rpow_one]; ring
      _ = 73 * (D ^ (-(1 / 4) : ℝ) * (1 + 1 / 10 * L) ^ 2) := by rw [hcollapse]
  have hxpow : xp = D ^ (13 * (1 - σ)) := by
    rw [hxpdef, hxdef, ← Real.rpow_mul hDpos.le]; congr 1; ring
  have hxpD : xp ≤ D ^ ((13 : ℝ) / 120) := by
    rw [hxpow]; exact Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
  have hcol2 : D ^ ((13 : ℝ) / 120) * D ^ (-(1 / 4) : ℝ) = D ^ (-(17 / 120) : ℝ) := by
    rw [← Real.rpow_add hDpos]; norm_num
  have hthr : Am * Ib ≤ Sp ^ 2 / 8 := by
    have hthr0 := hDt D hDth
    rw [show Real.log D = L from hLdef.symm, show (1 + L / 10) ^ 2 = (1 + 1 / 10 * L) ^ 2 by ring]
      at hthr0
    have hAmD : Am ≤ 700 * Cps * D ^ ((13 : ℝ) / 120) := by
      have h := mul_le_mul_of_nonneg_left hxpD (by linarith only [hCps] : (0:ℝ) ≤ 700 * Cps)
      linarith only [hAmub, h]
    have hprod : Am * Ib
        ≤ (700 * Cps * D ^ ((13 : ℝ) / 120)) * (73 * (D ^ (-(1 / 4) : ℝ) * (1 + 1/10*L) ^ 2)) :=
      mul_le_mul hAmD hIbub hIbnn (by positivity)
    have heq : (700 * Cps * D ^ ((13 : ℝ) / 120)) * (73 * (D ^ (-(1/4) : ℝ) * (1 + 1/10*L) ^ 2))
        = 51100 * Cps * (D ^ (-(17 / 120) : ℝ) * (1 + 1 / 10 * L) ^ 2) := by
      rw [← hcol2]; ring
    have hnn : (0 : ℝ) ≤ Cps * (D ^ (-(17 / 120) : ℝ) * (1 + 1 / 10 * L) ^ 2) := by positivity
    have hSp2 : (2 : ℝ) / 10 ^ 4 ≤ Sp ^ 2 / 8 := by nlinarith only [hSp]
    linarith only [hprod, heq, hthr0, hnn, hSp2]
  -- ## the rectangle's shape constants
  have hL3 : (0 : ℝ) ≤ L ^ 3 := by positivity
  have hXhi : ξ₁ - ξ₀ ≤ 25 / 1000 * L := by rw [hξ₀def]; linarith only [hξ₁hi]
  have hXlo : 241 / 10000 * L ≤ ξ₁ - ξ₀ := by rw [hξ₀def]; linarith only [hξ₁lo, hL]
  have hXnn : (0 : ℝ) ≤ ξ₁ - ξ₀ := by linarith only [hXlo, hLpos]
  have hHeq : η₁ - η₀ = 13 / 240 * L := by rw [hη₁def]; ring
  have hEta : η₁ - ξ₀ ≤ 367 / 100 * L := by
    rw [hη₁def, hη₀eq]; linarith only [hξ₀lo, hlog2hi, hL]
  have hEta0 : (0 : ℝ) ≤ η₁ - ξ₀ := by
    rw [hη₁def, hη₀eq]; linarith only [hξ₀hi, hlog2lo, hL]
  have hW : 2 / (59 / 60 * (119 / 60)) * ((ξ₁ - ξ₀) * (η₁ - η₀)) * (η₁ - ξ₀)
      + 2 * (2 / (59 / 60 * (119 / 60))) * ((ξ₁ - ξ₀) + (η₁ - η₀)) * (Real.pi ^ 2 / 3 * L ^ 2)
      ≤ 600 * L * ((ξ₁ - ξ₀) * (η₁ - η₀)) := by
    rw [hHeq]
    have hXE : (ξ₁ - ξ₀) * (η₁ - ξ₀) ≤ (25 / 1000 * L) * (367 / 100 * L) :=
      mul_le_mul hXhi hEta hEta0 (by linarith only [hLpos])
    have hT1' : 2 / (59 / 60 * (119 / 60)) * ((ξ₁ - ξ₀) * (13 / 240 * L)) * (η₁ - ξ₀)
        ≤ 6 / 1000 * L ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hXE (le_of_lt hLpos)
      linarith only [h, hL3]
    have hSum : (ξ₁ - ξ₀) + 13 / 240 * L ≤ 791667 / 10000000 * L := by linarith only [hXhi, hLpos]
    have hpi3 : Real.pi ^ 2 / 3 * L ^ 2 ≤ 33075 / 10000 * L ^ 2 := by
      nlinarith only [hpihi, sq_nonneg L]
    have hpi3nn : (0 : ℝ) ≤ Real.pi ^ 2 / 3 * L ^ 2 := by positivity
    have hT2' : 2 * (2 / (59 / 60 * (119 / 60))) * ((ξ₁ - ξ₀) + 13 / 240 * L)
        * (Real.pi ^ 2 / 3 * L ^ 2) ≤ 54 / 100 * L ^ 3 := by
      have h := mul_le_mul hSum hpi3 hpi3nn (by linarith only [hLpos])
      linarith only [h, hL3]
    have hRHS : 78 / 100 * L ^ 3 ≤ 600 * L * ((ξ₁ - ξ₀) * (13 / 240 * L)) := by
      have h := mul_le_mul_of_nonneg_right hXlo (sq_nonneg L)
      linarith only [h, hL3]
    linarith only [hT1', hT2', hRHS, hL3]
  -- ## the residue block's constants
  set Ec : ℂ := ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) with hEcdef
  set Scr : ℝ := ∑ r ∈ rFilter q R, (Nat.totient r : ℝ) / (r : ℝ) ^ 2 with hScrdef
  have hScrnn : (0 : ℝ) ≤ Scr := Finset.sum_nonneg fun r _ => by positivity
  have hScrle : Scr ≤ Sp := sum_rFilter_totient_div_sq_le q R
  have hEScn : ‖Ec * ((Scr : ℝ) : ℂ)‖ ≤ Φ * Sp := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScrnn]
    exact mul_le_mul (norm_prod_one_sub_inv_le_totient_div q hq1) hScrle hScrnn
      (le_of_lt hΦpos)
  have hre : ∀ j k : Fin J, ((starRingEnd ℂ) (ρ j - σ) + (ρ k - σ)).re
      = ((ρ j).re - σ) + ((ρ k).re - σ) := by
    intro j k
    simp only [Complex.add_re, Complex.sub_re, Complex.conj_re, Complex.ofReal_re]
  have himS : ∀ j k : Fin J, ((starRingEnd ℂ) (ρ j - σ) + (ρ k - σ)).im
      = (ρ k).im - (ρ j).im := by
    intro j k
    simp only [Complex.add_im, Complex.sub_im, Complex.conj_im, Complex.ofReal_im]
    ring
  have hs0 : ∀ j k : Fin J, (0 : ℝ) ≤ ((starRingEnd ℂ) (ρ j - σ) + (ρ k - σ)).re := by
    intro j k; rw [hre]; linarith only [hβ j, hβ k]
  have hs1 : ∀ j k : Fin J, ((starRingEnd ℂ) (ρ j - σ) + (ρ k - σ)).re ≤ 1 / 60 := by
    intro j k; rw [hre]; linarith only [hβ1 j, hβ1 k, hσ]
  have hsT : ∀ j k : Fin J, |((starRingEnd ℂ) (ρ j - σ) + (ρ k - σ)).im| ≤ 2 * T := by
    intro j k
    rw [himS, abs_le]
    have h1 := abs_le.mp (hρT j)
    have h2 := abs_le.mp (hρT k)
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  -- ## the per-(j,k) bound
  have hBtbnd : ∀ j k : Fin J,
      ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Bt j k ξ η‖
        ≤ Φ * Sp * ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Kf j k ξ η‖
          + Ib * ((ξ₁ - ξ₀) * (η₁ - η₀)) := by
    intro j k
    have hGc : Continuous (Function.uncurry (fun ξ η => Ec * ((Scr : ℝ) : ℂ) * Kf j k ξ η)) :=
      continuous_const.mul (hKfc j k)
    have hptI : ∀ ξ ∈ Set.uIoc ξ₀ ξ₁, ∀ η ∈ Set.uIoc η₀ η₁,
        ‖Bt j k ξ η - Ec * ((Scr : ℝ) : ℂ) * Kf j k ξ η‖ ≤ Ib := by
      intro ξ hξm η hηm
      rw [Set.uIoc_of_le hξ] at hξm
      rw [Set.uIoc_of_le hη] at hηm
      have hξl : ξ₀ ≤ ξ := le_of_lt hξm.1
      have hξr : ξ ≤ ξ₁ := hξm.2
      have hηl : η₀ ≤ η := le_of_lt hηm.1
      have hηr : η ≤ η₁ := hηm.2
      have hM2 : (2 : ℝ) ≤ Real.exp ξ := hMlo ξ hξl
      have hMNe : Real.exp ξ ≤ Real.exp η := hMN ξ η hξr hηl
      have hξηle : ξ ≤ η := by linarith only [hξr, hηl, hξη₀]
      have hηN : Real.exp η ≤ N₁ := hNhi η hηr
      have h1 : Bt j k ξ η = Salt.MR.halaszBTsum (jutilaB q R (Real.exp η) (Real.exp ξ)) χ χ
          ((starRingEnd ℂ) (ρ j - σ) + (ρ k - σ)) :=
        (halaszBTsum_jutilaB_exp_eq_sum χ R hξηle hηN _).symm
      have h2 : Kf j k ξ η
          = resKernel ((starRingEnd ℂ) (ρ j - σ) + (ρ k - σ)) (Real.exp η) (Real.exp ξ) := rfl
      have hid := halaszBTsum_jutilaB_eq χ hR1 hM2 hMNe (hs0 j k) (hs1 j k)
      have hdiff : Bt j k ξ η - Ec * ((Scr : ℝ) : ℂ) * Kf j k ξ η
          = jutilaI q R (Real.exp η) (Real.exp ξ)
              ((starRingEnd ℂ) (ρ j - σ) + (ρ k - σ)) := by
        rw [h1, h2, hid, hEcdef, hScrdef]; ring
      rw [hdiff]
      have hIb0 := norm_jutilaI_le hq hR1 hM2 hMNe (hs0 j k) (hs1 j k) hT (hsT j k)
      rw [← hDdef] at hIb0
      refine le_trans hIb0 ?_
      have hMon : (Real.exp ξ) ^ (-(1 / 2) : ℝ) ≤ (Real.exp ξ₀) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos ξ₀) (Real.exp_le_exp.mpr hξl) (by norm_num)
      rw [hIbdef]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hMon (by linarith only [hDpos])) (sq_nonneg _)
    have hmain := norm_integral_integral_le_of_sub (hBtc j k) hGc hξ hη hptI
    have hconst : (∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Ec * ((Scr : ℝ) : ℂ) * Kf j k ξ η)
        = (Ec * ((Scr : ℝ) : ℂ)) * ∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Kf j k ξ η :=
      integral_integral_const_mul _ _ _ _ _ _
    rw [hconst, norm_mul] at hmain
    have hb := mul_le_mul_of_nonneg_right hEScn
      (norm_nonneg (∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Kf j k ξ η))
    linarith only [hmain, hb]
  -- ## the diagonal and the off-diagonal
  have hdiagb : ∀ j : Fin J,
      ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Kf j j ξ η‖
        ≤ 2 / (59 / 60 * (119 / 60)) * ((ξ₁ - ξ₀) * (η₁ - η₀)) * (η₁ - ξ₀) := by
    intro j
    have hsr : (starRingEnd ℂ) (ρ j - σ) + (ρ j - σ) = ((2 * ((ρ j).re - σ) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
      ring
    have hK : ∀ ξ η : ℝ, Kf j j ξ η
        = resKernel ((2 * ((ρ j).re - σ) : ℝ) : ℂ) (Real.exp η) (Real.exp ξ) := by
      intro ξ η
      have hz : Kf j j ξ η
          = resKernel ((starRingEnd ℂ) (ρ j - σ) + (ρ j - σ)) (Real.exp η) (Real.exp ξ) := rfl
      rw [hz, hsr]
    have h1 := norm_ii_le_ii_norm (hKfc j j) hξ hη
    have h2 := integral_norm_resKernel_diag_le (s := 2 * ((ρ j).re - σ))
      (by linarith only [hβ j]) (by linarith only [hβ1 j, hσ]) hξ₀0 hξ hη hξη₀
    have h3 : (∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, ‖Kf j j ξ η‖)
        = ∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁,
            ‖resKernel ((2 * ((ρ j).re - σ) : ℝ) : ℂ) (Real.exp η) (Real.exp ξ)‖ := by
      simp only [hK]
    linarith only [h1, h2, h3]
  have hoffb : ∀ j k : Fin J, j ≠ k →
      ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Kf j k ξ η‖
        ≤ 2 * (2 / (59 / 60 * (119 / 60))) * ((ξ₁ - ξ₀) + (η₁ - η₀))
            * (1 / ((ρ k).im - (ρ j).im) ^ 2) := by
    intro j k hjk
    have him : ((starRingEnd ℂ) (ρ j - σ) + (ρ k - σ)).im ≠ 0 := by
      rw [himS]
      intro hc
      exact hjk (hinj (by linarith only [hc] : (ρ j).im = (ρ k).im))
    have h := norm_integral_resKernel_offdiag_le (hs0 j k) (hs1 j k) him hξ₀0 hη₀0 hξ hη
    rw [himS] at h
    calc ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Kf j k ξ η‖
        ≤ 2 * (2 / (59 / 60 * (119 / 60))) * ((ξ₁ - ξ₀) + (η₁ - η₀))
            / ((ρ k).im - (ρ j).im) ^ 2 := h
      _ = 2 * (2 / (59 / 60 * (119 / 60))) * ((ξ₁ - ξ₀) + (η₁ - η₀))
            * (1 / ((ρ k).im - (ρ j).im) ^ 2) := by ring
  -- ## the Schur sum
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hschur : ∀ j : Fin J,
      ∑ k ∈ Finset.univ.erase j, 1 / ((ρ k).im - (ρ j).im) ^ 2 ≤ Real.pi ^ 2 / 3 * L ^ 2 := by
    intro j
    have hΔ : (0 : ℝ) < 1 / L := by positivity
    have hγ : (ρ j).im ∈ Finset.univ.image (fun j => (ρ j).im) :=
      Finset.mem_image_of_mem _ (Finset.mem_univ j)
    have h := sum_inv_sq_sub_le_of_wellSpacedAt hΔ hws hγ
    have himg : (Finset.univ.image (fun k => (ρ k).im)).erase ((ρ j).im)
        = (Finset.univ.erase j).image (fun k => (ρ k).im) :=
      (Finset.image_erase hinj Finset.univ j).symm
    rw [himg, Finset.sum_image (f := fun y : ℝ => 1 / ((ρ j).im - y) ^ 2)
      (fun a _ b _ hab => hinj hab)] at h
    have hLL : Real.pi ^ 2 / 3 / (1 / L) ^ 2 = Real.pi ^ 2 / 3 * L ^ 2 := by field_simp
    rw [hLL] at h
    have hcong : ∑ k ∈ Finset.univ.erase j, 1 / ((ρ j).im - (ρ k).im) ^ 2
        = ∑ k ∈ Finset.univ.erase j, 1 / ((ρ k).im - (ρ j).im) ^ 2 :=
      Finset.sum_congr rfl fun k _ => by ring
    linarith only [h, hcong]
  have hKsum : ∀ j : Fin J, ∑ k, ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Kf j k ξ η‖
      ≤ 2 / (59 / 60 * (119 / 60)) * ((ξ₁ - ξ₀) * (η₁ - η₀)) * (η₁ - ξ₀)
        + 2 * (2 / (59 / 60 * (119 / 60))) * ((ξ₁ - ξ₀) + (η₁ - η₀))
            * (Real.pi ^ 2 / 3 * L ^ 2) := by
    intro j
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun k => ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Kf j k ξ η‖) (Finset.mem_univ j)
    have hcnn : (0 : ℝ) ≤ 2 * (2 / (59 / 60 * (119 / 60))) * ((ξ₁ - ξ₀) + (η₁ - η₀)) := by
      have h1 : (0 : ℝ) ≤ η₁ - η₀ := by rw [hHeq]; linarith only [hLpos]
      have h2 : (0 : ℝ) ≤ ξ₁ - ξ₀ := hXnn
      nlinarith only [h1, h2]
    have hoff : ∑ k ∈ Finset.univ.erase j, ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Kf j k ξ η‖
        ≤ ∑ k ∈ Finset.univ.erase j,
            2 * (2 / (59 / 60 * (119 / 60))) * ((ξ₁ - ξ₀) + (η₁ - η₀))
              * (1 / ((ρ k).im - (ρ j).im) ^ 2) :=
      Finset.sum_le_sum fun k hk => hoffb j k (fun h => (Finset.ne_of_mem_erase hk) h.symm)
    have hpull : ∑ k ∈ Finset.univ.erase j,
        2 * (2 / (59 / 60 * (119 / 60))) * ((ξ₁ - ξ₀) + (η₁ - η₀))
          * (1 / ((ρ k).im - (ρ j).im) ^ 2)
        = 2 * (2 / (59 / 60 * (119 / 60))) * ((ξ₁ - ξ₀) + (η₁ - η₀))
          * ∑ k ∈ Finset.univ.erase j, 1 / ((ρ k).im - (ρ j).im) ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    have hlast := mul_le_mul_of_nonneg_left (hschur j) hcnn
    linarith only [hsplit, hoff, hpull, hlast, hdiagb j]
  -- ## the expansion of the double integral
  have hFc0 : ∀ ξ η : ℝ, Fc ξ η
      = ∑ j, ∑ k, (starRingEnd ℂ) (u j) * u k * Bt j k ξ η := fun _ _ => rfl
  have hFcexp : (∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Fc ξ η)
      = ∑ j, ∑ k, (starRingEnd ℂ) (u j) * u k
          * ∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Bt j k ξ η := by
    simp only [hFc0]
    rw [integral_integral_finsetSum Finset.univ
      (fun j ξ η => ∑ k, (starRingEnd ℂ) (u j) * u k * Bt j k ξ η)
      (fun j _ => continuous_finsetSum _ fun k _ => continuous_const.mul (hBtc j k)) ξ₀ ξ₁ η₀ η₁]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_integral_finsetSum Finset.univ
      (fun k ξ η => (starRingEnd ℂ) (u j) * u k * Bt j k ξ η)
      (fun k _ => continuous_const.mul (hBtc j k)) ξ₀ ξ₁ η₀ η₁]
    exact Finset.sum_congr rfl fun k _ => integral_integral_const_mul _ _ _ _ _ _
  have hnormc : ∀ (j k : Fin J) (Z : ℂ), ‖(starRingEnd ℂ) (u j) * u k * Z‖ = ‖Z‖ := by
    intro j k Z
    rw [norm_mul, norm_mul, RCLike.norm_conj, hu1 j, hu1 k, one_mul, one_mul]
  have hup : (∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, (Fc ξ η).re)
      ≤ ∑ j, ∑ k, ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Bt j k ξ η‖ := by
    rw [integral_integral_re hFcc]
    refine le_trans (Complex.re_le_norm _) ?_
    rw [hFcexp]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => le_of_eq (hnormc j k _))
  have hΦSnn : (0 : ℝ) ≤ Φ * Sp := mul_nonneg (le_of_lt hΦpos) hSpnn
  have hperj : ∀ j : Fin J, ∑ k, ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Bt j k ξ η‖
      ≤ Φ * Sp * (600 * L * ((ξ₁ - ξ₀) * (η₁ - η₀)))
        + (J : ℝ) * (Ib * ((ξ₁ - ξ₀) * (η₁ - η₀))) := by
    intro j
    have h1 : ∑ k, ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Bt j k ξ η‖
        ≤ ∑ _k : Fin J, (Φ * Sp * ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Kf j _k ξ η‖
            + Ib * ((ξ₁ - ξ₀) * (η₁ - η₀))) := Finset.sum_le_sum fun k _ => hBtbnd j k
    have h2 : ∑ _k : Fin J, (Φ * Sp * ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Kf j _k ξ η‖
          + Ib * ((ξ₁ - ξ₀) * (η₁ - η₀)))
        = Φ * Sp * (∑ k, ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Kf j k ξ η‖)
          + (J : ℝ) * (Ib * ((ξ₁ - ξ₀) * (η₁ - η₀))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have h3 : Φ * Sp * (∑ k, ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Kf j k ξ η‖)
        ≤ Φ * Sp * (600 * L * ((ξ₁ - ξ₀) * (η₁ - η₀))) :=
      mul_le_mul_of_nonneg_left (le_trans (hKsum j) hW) hΦSnn
    linarith only [h1, h2, h3]
  have htot : ∑ j, ∑ k, ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, Bt j k ξ η‖
      ≤ (J : ℝ) * (Φ * Sp * (600 * L * ((ξ₁ - ξ₀) * (η₁ - η₀)))
          + (J : ℝ) * (Ib * ((ξ₁ - ξ₀) * (η₁ - η₀)))) := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hperj j)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    linarith only [h]
  -- ## the closing chain
  have hPpos : (0 : ℝ) < (ξ₁ - ξ₀) * (η₁ - η₀) := by
    have h1 : (0 : ℝ) < ξ₁ - ξ₀ := by linarith only [hXlo, hLpos]
    have h2 : (0 : ℝ) < η₁ - η₀ := by rw [hHeq]; linarith only [hLpos]
    exact mul_pos h1 h2
  have h3 : ((J : ℝ) * Sp / 2) ^ 2
      ≤ Am * ((J : ℝ) * (Φ * Sp * (600 * L)) + (J : ℝ) ^ 2 * Ib) := by
    have hchain := le_trans hdev (le_trans hup htot)
    have heq : (J : ℝ) * (Φ * Sp * (600 * L * ((ξ₁ - ξ₀) * (η₁ - η₀)))
          + (J : ℝ) * (Ib * ((ξ₁ - ξ₀) * (η₁ - η₀))))
        = ((J : ℝ) * (Φ * Sp * (600 * L)) + (J : ℝ) ^ 2 * Ib) * ((ξ₁ - ξ₀) * (η₁ - η₀)) := by
      ring
    rw [heq] at hchain
    have hdiv : ((J : ℝ) * Sp / 2) ^ 2 / Am
        ≤ (J : ℝ) * (Φ * Sp * (600 * L)) + (J : ℝ) ^ 2 * Ib :=
      le_of_mul_le_mul_right hchain hPpos
    rw [div_le_iff₀ hAmpos] at hdiv
    linarith only [hdiv]
  have hIth := mul_le_mul_of_nonneg_left hthr (sq_nonneg (J : ℝ))
  have hq2 : (J : ℝ) ^ 2 * Sp ^ 2 / 8 ≤ 600 * Am * (J : ℝ) * Φ * Sp * L := by
    linarith only [h3, hIth]
  have hJSppos : (0 : ℝ) < (J : ℝ) * Sp := mul_pos (by linarith only [hJR]) hSppos
  have h6 : (J : ℝ) * Sp / 8 ≤ 600 * Am * Φ * L := by
    have h : ((J : ℝ) * Sp / 8) * ((J : ℝ) * Sp) ≤ (600 * Am * Φ * L) * ((J : ℝ) * Sp) := by
      linarith only [hq2]
    exact le_of_mul_le_mul_right h hJSppos
  have hSpl2 : 6 * Φ * L ≤ 10 * Real.pi ^ 2 * Sp := by
    have h := mul_le_mul_of_nonneg_left hSpl (by positivity : (0 : ℝ) ≤ 10 * Real.pi ^ 2)
    have he : 10 * Real.pi ^ 2 * (6 / Real.pi ^ 2 * Φ * Real.log R) = 60 * Φ * Real.log R := by
      field_simp
      ring
    rw [he, hlogR] at h
    linarith only [h]
  have hA' : 600 * Am * Φ * L ≤ 1000 * Am * Real.pi ^ 2 * Sp := by
    have h := mul_le_mul_of_nonneg_left hSpl2 (by linarith only [hAmnn] : (0 : ℝ) ≤ 100 * Am)
    linarith only [h]
  have h7 : (J : ℝ) / 8 * Sp ≤ (1000 * Am * Real.pi ^ 2) * Sp := by linarith only [h6, hA']
  have h9 : (J : ℝ) / 8 ≤ 1000 * Am * Real.pi ^ 2 := le_of_mul_le_mul_right h7 hSppos
  have hJfin : (J : ℝ) ≤ 8000 * Real.pi ^ 2 * Am := by linarith only [h9]
  have hpiAm := mul_nonneg (by linarith only [hpihi] : (0 : ℝ) ≤ 99225 / 10000 - Real.pi ^ 2)
    hAmnn
  have hfin2 : (J : ℝ) ≤ 79380 * Am := by linarith only [hJfin, hpiAm]
  have hfin3 : (J : ℝ) ≤ 79380 * (700 * Cps * xp) := by linarith only [hfin2, hAmub]
  rw [hxpow] at hfin3
  have hCY : (0 : ℝ) ≤ Cps * D ^ (13 * (1 - σ)) := by positivity
  linarith only [hfin3, hCY]

/-- **The W9c′ exit rows** (each INVOKES a frozen row at numerals): the kernel's continuity at
`s = 0`; the weight's continuity at `(q, R, n) = (5, 6, 7)`. -/
example : Continuous (fun p : ℝ × ℝ => resKernel 0 (Real.exp p.2) (Real.exp p.1)) :=
  continuous_resKernel_exp 0

example : Continuous (fun p : ℝ × ℝ => jutilaB 5 6 (Real.exp p.2) (Real.exp p.1) 7) :=
  continuous_jutilaB_exp 5 6 7

end Salt.SW
