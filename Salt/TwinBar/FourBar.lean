/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.SliceCS

/-!
# The `k = 4` analytic core — the `β = 1/3` CS-base tuning (`FourBar`)

**This is EXPLORATION, not a frozen blueprint node.** Design context:
`docs/exploration/pilot.md` (probes P-C / Q2bc) and the `M_k` atlas sprint (Q2b).
This file is the exact analogue at `k = 4` of the landed `k = 3` analytic core
`Salt/TwinBar/ThreeBar.lean` — a coordinate-for-coordinate mirror, only the base
tuning changes. It adds NEW work only; it edits no landed file and is wired into
`Salt.TwinBar.All` by the house session. Everything here is sorry-free and
axiom-clean.

## The target: the Maynard–Selberg functional at `k = 4`

Polymath8b (arXiv:1407.4897) eq. (31)–(33), specialised to `k = 4`. `F` is a
continuous weight on the closed `4`-simplex
`R₄ = {(t₁,t₂,t₃,t₄) | tᵢ ≥ 0, t₁+t₂+t₃+t₄ ≤ 1}`. The carriers, in the nested-1D
form mirroring `ThreeBar.lean`'s `k = 3` conventions (`I₃`/`J₁₃…J₃₃` there):

* `I₄ F = ∫∫∫∫_{R₄} F²` — the `L²`-mass (eq. 33).
* `J₁₄ F … J₄₄ F` — the four Selberg peels (eq. 31–32): `J_{m}` is the square of
  the marginal in the `m`-th variable, integrated over the other three, written
  with its marginal variable *innermost* so the per-slice Cauchy–Schwarz applies
  directly.

`M₄ := sup_F (J₁₄ + J₂₄ + J₃₄ + J₄₄)/I₄`. The classical fact (Polymath8b) is the
sharp `M_k ≤ (k/(k−1))·log k`, giving `(4/3)·log 4 ≈ 1.8484 < 2` at `k = 4`: `k = 4`
is still *too small* for the unmodified Maynard sieve to force two primes.

## The retuned CS base (`β = 1/(k−1) = 1/3` at `k = 4`)

The `k = 2` "magic identity" `w₁ + w₂ ≡ 2` is the `β = 1/(k−1)` tuning: writing the
CS base as `β·(slice length)`, the normalisation is `log((β+1)/β)` (`a`-uniform)
and `w_m = β·(slice length) + t_m` has `Σ_m w_m` CONSTANT in `s := Σ tᵢ` iff
`β = 1/(k−1)`, giving normalisation `log k` and constant sum `k/(k−1)`. Hence the
sharp `Σ_m J_m ≤ (k/(k−1))·log k · I_k`.

* `k = 2`: `β = 1`, `log 2`, sum `2` — landed `twin_bar`.
* `k = 3`: `β = 1/2`, `log 3`, sum `3/2` — landed `ThreeBar` (`three_bar`).
* `k = 4`: `β = 1/3`, base `= (slice length)/3`, normalisation `log 4`
  (`logWeight_third`), and the CONSTANT weight-sum
  **`w₁₄ + w₂₄ + w₃₄ + w₄₄ ≡ 4/3`** (`w_sum_four`). Therefore
  `M₄ ≤ (4/3)·log 4 < 2` (`four_thirds_log_four_lt_two`) — the sharp constant, and
  a `k = 4` NO-GO.

## Structure (mirroring the `k = 3` heart)

The analytic content is complete and unconditional: on every slice the retuned CS
gives `(∫ F)² ≤ log 4 · ∫ w_m·F²` (`sliceCS₁₄…sliceCS₄₄`), and the four weights sum
to the constant `4/3` (`w_sum_four`). The `4`-D Fubini/Tonelli assembly of the four
slice bounds into a single scalar `≤ I₄` is the `k = 4` analogue of `ThreeBarAsm`
(the landed `three_bar`); it is scheduled separately (nodes N4-ASM-a/b/c) and is NOT
in this file. The assembly target is stated here as the citable `def FourBar`, and
the no-go `no_quad_weight_of_fourBar` (the exact `k = 4` analogue of
`no_triple_weight_of_tripleBar`) is proved *modulo* `FourBar` — exhibiting that the
`4`-D assembly is the ONLY missing input to `M₄ < 2`.
-/

namespace Salt.TwinBar

open MeasureTheory Set Function intervalIntegral

/-! ## The `k = 4` carriers (nested-1D, mirroring `ThreeBar.lean`) -/

/-- The closed `4`-simplex
`R₄ = {0 ≤ t₁, 0 ≤ t₂, 0 ≤ t₃, 0 ≤ t₄, t₁+t₂+t₃+t₄ ≤ 1}`. -/
def R₄ : Set (ℝ × ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2.1 ∧ 0 ≤ p.2.2.2 ∧ p.1 + p.2.1 + p.2.2.1 + p.2.2.2 ≤ 1}

/-- `I₄ F = ∫∫∫∫_{R₄} F²` in canonical nested order (`t₄` outer, then `t₃`, `t₂`,
`t₁` inner). The `L²`-mass carrier (Polymath8b eq. 33 at `k = 4`). -/
noncomputable def I₄ (F : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₄ in (0:ℝ)..1, ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃),
    ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃ - t₂), (F t₁ t₂ t₃ t₄) ^ 2

/-- `J₁₄ F` — the marginal-in-`t₁` Selberg peel (eq. 31), `t₁` innermost. -/
noncomputable def J₁₄ (F : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₄ in (0:ℝ)..1, ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃),
    (∫ t₁ in (0:ℝ)..(1 - t₄ - t₃ - t₂), F t₁ t₂ t₃ t₄) ^ 2

/-- `J₂₄ F` — the marginal-in-`t₂` Selberg peel, `t₂` innermost. -/
noncomputable def J₂₄ (F : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₄ in (0:ℝ)..1, ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃),
    (∫ t₂ in (0:ℝ)..(1 - t₄ - t₃ - t₁), F t₁ t₂ t₃ t₄) ^ 2

/-- `J₃₄ F` — the marginal-in-`t₃` Selberg peel, `t₃` innermost.

Outer order `(t₁, t₂, t₄)` — `t₁` OUTERMOST, per the N4-ASM gate's correction 1:
the original `(t₄, t₂, t₁)` order left the `t₃` marginal unreachable by either
size-`s` reduce3 order without swapping a marginal (an unbudgeted size-`s`
marginal-continuity lemma); with `t₁` outermost the route is peel-`t₁`-outer →
one plain inner-two swap `(t₄, t₃)` at size `1 − t₁ − t₂` → w3order. The peel
orders are the assembly's one free choice (value-neutral by Tonelli). -/
noncomputable def J₃₄ (F : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂),
    (∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄), F t₁ t₂ t₃ t₄) ^ 2

/-- `J₄₄ F` — the marginal-in-`t₄` Selberg peel, `t₄` innermost. -/
noncomputable def J₄₄ (F : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂),
    (∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), F t₁ t₂ t₃ t₄) ^ 2

/-! ## Nonnegativity of the carriers -/

/-- `0 ≤ I₄ F`. Four nested `integral_nonneg` over correctly-oriented ranges. -/
theorem I₄_nonneg (F : ℝ → ℝ → ℝ → ℝ → ℝ) : 0 ≤ I₄ F := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro t₄ ht₄
  apply intervalIntegral.integral_nonneg (by have := ht₄.2; linarith : (0:ℝ) ≤ 1 - t₄)
  intro t₃ ht₃
  apply intervalIntegral.integral_nonneg (by have := ht₃.2; linarith : (0:ℝ) ≤ 1 - t₄ - t₃)
  intro t₂ ht₂
  apply intervalIntegral.integral_nonneg (by have := ht₂.2; linarith :
    (0:ℝ) ≤ 1 - t₄ - t₃ - t₂)
  intro t₁ _
  positivity

/-- `0 ≤ J₁₄ F`. Outer integrand is a square. -/
theorem J₁₄_nonneg (F : ℝ → ℝ → ℝ → ℝ → ℝ) : 0 ≤ J₁₄ F := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro t₄ ht₄
  apply intervalIntegral.integral_nonneg (by have := ht₄.2; linarith : (0:ℝ) ≤ 1 - t₄)
  intro t₃ ht₃
  apply intervalIntegral.integral_nonneg (by have := ht₃.2; linarith : (0:ℝ) ≤ 1 - t₄ - t₃)
  intro t₂ _; positivity

/-- `0 ≤ J₂₄ F`. -/
theorem J₂₄_nonneg (F : ℝ → ℝ → ℝ → ℝ → ℝ) : 0 ≤ J₂₄ F := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro t₄ ht₄
  apply intervalIntegral.integral_nonneg (by have := ht₄.2; linarith : (0:ℝ) ≤ 1 - t₄)
  intro t₃ ht₃
  apply intervalIntegral.integral_nonneg (by have := ht₃.2; linarith : (0:ℝ) ≤ 1 - t₄ - t₃)
  intro t₁ _; positivity

/-- `0 ≤ J₃₄ F`. -/
theorem J₃₄_nonneg (F : ℝ → ℝ → ℝ → ℝ → ℝ) : 0 ≤ J₃₄ F := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro t₁ ht₁
  apply intervalIntegral.integral_nonneg (by have := ht₁.2; linarith : (0:ℝ) ≤ 1 - t₁)
  intro t₂ ht₂
  apply intervalIntegral.integral_nonneg (by have := ht₂.2; linarith : (0:ℝ) ≤ 1 - t₁ - t₂)
  intro t₄ _; positivity

/-- `0 ≤ J₄₄ F`. -/
theorem J₄₄_nonneg (F : ℝ → ℝ → ℝ → ℝ → ℝ) : 0 ≤ J₄₄ F := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro t₁ ht₁
  apply intervalIntegral.integral_nonneg (by have := ht₁.2; linarith : (0:ℝ) ≤ 1 - t₁)
  intro t₂ ht₂
  apply intervalIntegral.integral_nonneg (by have := ht₂.2; linarith : (0:ℝ) ≤ 1 - t₁ - t₂)
  intro t₃ _; positivity

/-! ## The retuned Cauchy–Schwarz weights (base `= (slice length)/3`, `β = 1/3`) -/

/-- The first weight `w₁₄ (t₁,t₂,t₃,t₄) = (1 − t₂ − t₃ − t₄)/3 + t₁ = (base) + t₁`
with base `(1−t₂−t₃−t₄)/3` a third of the `t₁`-slice length. -/
noncomputable def w₁₄ (t₁ t₂ t₃ t₄ : ℝ) : ℝ := (1 - t₂ - t₃ - t₄) / 3 + t₁

/-- The second weight `w₂₄ (t₁,t₂,t₃,t₄) = (1 − t₁ − t₃ − t₄)/3 + t₂`. -/
noncomputable def w₂₄ (t₁ t₂ t₃ t₄ : ℝ) : ℝ := (1 - t₁ - t₃ - t₄) / 3 + t₂

/-- The third weight `w₃₄ (t₁,t₂,t₃,t₄) = (1 − t₁ − t₂ − t₄)/3 + t₃`. -/
noncomputable def w₃₄ (t₁ t₂ t₃ t₄ : ℝ) : ℝ := (1 - t₁ - t₂ - t₄) / 3 + t₃

/-- The fourth weight `w₄₄ (t₁,t₂,t₃,t₄) = (1 − t₁ − t₂ − t₃)/3 + t₄`. -/
noncomputable def w₄₄ (t₁ t₂ t₃ t₄ : ℝ) : ℝ := (1 - t₁ - t₂ - t₃) / 3 + t₄

/-- **The `k = 4` magic identity.** `w₁₄ + w₂₄ + w₃₄ + w₄₄ ≡ 4/3` pointwise — the
constant weight-sum from the retuned base `β = 1/3`. This is the `k = 4` analogue
of `w_sum_three : … = 3/2`; the constant is `k/(k−1) = 4/3` (the one-line identity
`(4 − 3s)/3 + s = 4/3`, `s := t₁+t₂+t₃+t₄`). -/
theorem w_sum_four (t₁ t₂ t₃ t₄ : ℝ) :
    w₁₄ t₁ t₂ t₃ t₄ + w₂₄ t₁ t₂ t₃ t₄ + w₃₄ t₁ t₂ t₃ t₄ + w₄₄ t₁ t₂ t₃ t₄ = 4 / 3 := by
  unfold w₁₄ w₂₄ w₃₄ w₄₄; ring

/-- `0 ≤ w₁₄` on `R₄`: base `≥ 0` (from `t₂+t₃+t₄ ≤ 1`) and `t₁ ≥ 0`. -/
theorem w₁₄_nonneg {t₁ t₂ t₃ t₄ : ℝ} (h1 : 0 ≤ t₁) (h : t₂ + t₃ + t₄ ≤ 1) :
    0 ≤ w₁₄ t₁ t₂ t₃ t₄ := by
  unfold w₁₄; linarith

/-- `0 ≤ w₂₄` on `R₄`. -/
theorem w₂₄_nonneg {t₁ t₂ t₃ t₄ : ℝ} (h2 : 0 ≤ t₂) (h : t₁ + t₃ + t₄ ≤ 1) :
    0 ≤ w₂₄ t₁ t₂ t₃ t₄ := by
  unfold w₂₄; linarith

/-- `0 ≤ w₃₄` on `R₄`. -/
theorem w₃₄_nonneg {t₁ t₂ t₃ t₄ : ℝ} (h3 : 0 ≤ t₃) (h : t₁ + t₂ + t₄ ≤ 1) :
    0 ≤ w₃₄ t₁ t₂ t₃ t₄ := by
  unfold w₃₄; linarith

/-- `0 ≤ w₄₄` on `R₄`. -/
theorem w₄₄_nonneg {t₁ t₂ t₃ t₄ : ℝ} (h4 : 0 ≤ t₄) (h : t₁ + t₂ + t₃ ≤ 1) :
    0 ≤ w₄₄ t₁ t₂ t₃ t₄ := by
  unfold w₄₄; linarith

/-! ## The retuned normalisation `∫₀^a (a/3 + t)⁻¹ = log 4` -/

/-- **The retuned log-weight integral** (the `k = 4` analogue of `logWeight_half`).
For `a > 0`, `∫₀^a (a/3 + t)⁻¹ dt = log 4`: the shift `t ↦ a/3 + t` lands the range
`a/3 .. 4a/3`, and `∫ x⁻¹` collapses `log((4a/3)/(a/3)) = log 4`. The base `a/3` (a
third of the slice length) is the `β = 1/3` retuning; base `a` would give `log 2`,
base `a/2` would give `log 3`. -/
theorem logWeight_third {a : ℝ} (ha : 0 < a) :
    ∫ t in (0:ℝ)..a, (a / 3 + t)⁻¹ = Real.log 4 := by
  have hshift : (∫ t in (0:ℝ)..a, (fun x : ℝ => x⁻¹) (a / 3 + t))
      = ∫ x in a / 3 + 0..a / 3 + a, (fun x : ℝ => x⁻¹) x :=
    intervalIntegral.integral_comp_add_left (fun x : ℝ => x⁻¹) (a / 3)
  simp only [add_zero] at hshift
  rw [hshift]
  have h43 : a / 3 + a = 4 * (a / 3) := by ring
  rw [h43, integral_inv_of_pos (by linarith : (0:ℝ) < a / 3) (by linarith : (0:ℝ) < 4 * (a / 3)),
    mul_div_assoc, div_self (by linarith : a / 3 ≠ 0), mul_one]

/-! ## The general sharp per-slice Cauchy–Schwarz (base `a/3`) -/

/-- **The sharp per-slice CS.** For continuous `φ` on `[0, a]` (`a ≥ 0`),
`(∫₀^a φ)² ≤ log 4 · ∫₀^a (a/3 + t)·φ(t)² dt`. This is the base-`a/3` retuning of
`log_slice_CS` (`ThreeBar.lean`, base `a/2`, `log 3`): instantiate the sign-agnostic
`interval_CS` with `f := √((a/3+t)⁻¹)`, `g := √(a/3+t)·φ` so `f·g = φ`,
`f² = (a/3+t)⁻¹` (`∫ f² = log 4` by `logWeight_third`), `g² = (a/3+t)·φ²`. The
`a = 0` slice is `0 ≤ 0`. -/
theorem log_slice_CS_third {φ : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hφ : ContinuousOn φ (Set.Icc 0 a)) :
    (∫ t in (0:ℝ)..a, φ t) ^ 2 ≤ Real.log 4 * ∫ t in (0:ℝ)..a, (a / 3 + t) * (φ t) ^ 2 := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · rw [← ha0]; simp
  -- `a > 0`. Positivity of `a/3 + x` on both interval flavours.
  have hpos_uIcc : ∀ x ∈ Set.uIcc (0:ℝ) a, 0 < a / 3 + x := by
    intro x hx; rw [Set.uIcc_of_le hapos.le] at hx; have := hx.1; linarith
  have hpos_uIoc : ∀ x ∈ Set.uIoc (0:ℝ) a, 0 < a / 3 + x := by
    intro x hx; rw [Set.uIoc_of_le hapos.le] at hx; have := hx.1; linarith
  have hφicc : ContinuousOn φ (Set.uIcc 0 a) := by rw [Set.uIcc_of_le hapos.le]; exact hφ
  have hφii : IntervalIntegrable φ volume 0 a := hφicc.intervalIntegrable
  -- Integrability of the reciprocal weight and the weighted square.
  have hinv_ii : IntervalIntegrable (fun x => (a / 3 + x)⁻¹) volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hapos.le]
    exact ContinuousOn.inv₀ (by fun_prop) (fun x hx => by
      have : (0:ℝ) < a / 3 + x := by have := hx.1; linarith
      exact this.ne')
  have hweight_ii : IntervalIntegrable (fun x => (a / 3 + x) * (φ x) ^ 2) volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hapos.le]
    exact (by fun_prop : ContinuousOn (fun x : ℝ => a / 3 + x) (Set.Icc 0 a)).mul (hφ.pow 2)
  -- The three `interval_CS` ingredients via `.congr` from the nice forms.
  have hf2ii : IntervalIntegrable (fun x => Real.sqrt ((a / 3 + x)⁻¹) ^ 2) volume 0 a :=
    hinv_ii.congr (fun x hx => (Real.sq_sqrt (inv_nonneg.mpr (hpos_uIoc x hx).le)).symm)
  have hg2ii : IntervalIntegrable (fun x => (Real.sqrt (a / 3 + x) * φ x) ^ 2) volume 0 a :=
    hweight_ii.congr (by
      intro x hx
      have : (Real.sqrt (a / 3 + x) * φ x) ^ 2 = (a / 3 + x) * (φ x) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (hpos_uIoc x hx).le]
      exact this.symm)
  have hfgii : IntervalIntegrable
      (fun x => Real.sqrt ((a / 3 + x)⁻¹) * (Real.sqrt (a / 3 + x) * φ x)) volume 0 a :=
    hφii.congr (by
      intro x hx
      have hne : Real.sqrt (a / 3 + x) ≠ 0 := (Real.sqrt_pos.mpr (hpos_uIoc x hx)).ne'
      have : Real.sqrt ((a / 3 + x)⁻¹) * (Real.sqrt (a / 3 + x) * φ x) = φ x := by
        rw [Real.sqrt_inv, inv_mul_cancel_left₀ hne]
      exact this.symm)
  -- Value rewrites.
  have hf2val : (∫ x in (0:ℝ)..a, Real.sqrt ((a / 3 + x)⁻¹) ^ 2) = Real.log 4 := by
    rw [intervalIntegral.integral_congr
          (fun x hx => Real.sq_sqrt (inv_nonneg.mpr (hpos_uIcc x hx).le))]
    exact logWeight_third hapos
  have hg2val : (∫ x in (0:ℝ)..a, (Real.sqrt (a / 3 + x) * φ x) ^ 2)
      = ∫ x in (0:ℝ)..a, (a / 3 + x) * (φ x) ^ 2 :=
    intervalIntegral.integral_congr (by
      intro x hx
      have hh : (Real.sqrt (a / 3 + x) * φ x) ^ 2 = (a / 3 + x) * (φ x) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (hpos_uIcc x hx).le]
      exact hh)
  have hfgval : (∫ x in (0:ℝ)..a, Real.sqrt ((a / 3 + x)⁻¹) * (Real.sqrt (a / 3 + x) * φ x))
      = ∫ x in (0:ℝ)..a, φ x :=
    intervalIntegral.integral_congr (by
      intro x hx
      have hne : Real.sqrt (a / 3 + x) ≠ 0 := (Real.sqrt_pos.mpr (hpos_uIcc x hx)).ne'
      have hh : Real.sqrt ((a / 3 + x)⁻¹) * (Real.sqrt (a / 3 + x) * φ x) = φ x := by
        rw [Real.sqrt_inv, inv_mul_cancel_left₀ hne]
      exact hh)
  -- Assemble via `interval_CS`.
  have hCS : (∫ x in (0:ℝ)..a, Real.sqrt ((a / 3 + x)⁻¹) * (Real.sqrt (a / 3 + x) * φ x)) ^ 2
      ≤ (∫ x in (0:ℝ)..a, Real.sqrt ((a / 3 + x)⁻¹) ^ 2)
        * (∫ x in (0:ℝ)..a, (Real.sqrt (a / 3 + x) * φ x) ^ 2) :=
    interval_CS (f := fun t => Real.sqrt ((a / 3 + t)⁻¹))
      (g := fun t => Real.sqrt (a / 3 + t) * φ t) hapos.le hf2ii hg2ii hfgii
  rw [hfgval, hf2val, hg2val] at hCS
  exact hCS

/-! ## The numeric atom `(4/3)·log 4 < 2` (the sub-gate constant) -/

/-- **`(4/3)·log 4 < 2`.** Via `log 4 = 2·log 2` (`Real.log_pow`), the goal is
`log 2 < 3/4`; mathlib's `Real.log_two_lt_d9` (`log 2 < 0.6931471808`) closes it.
This is the `k = 4` no-go direction: the sharp constant `(4/3)·log 4 ≈ 1.8484` is
strictly below the twin gate `2`. Mirrors `three_halves_log_three_lt_two`. -/
theorem four_thirds_log_four_lt_two : (4 / 3 : ℝ) * Real.log 4 < 2 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [h4]
  have h2 := Real.log_two_lt_d9
  linarith

/-! ## The four sharp per-slice bounds (analytic heart)

For a continuous `F` on `R₄`, the marginal-innermost CS on each slice gives the
sharp base-`a/3` bound with normalisation `log 4` and weight `w_m`. These are the
`k = 4` analogues of `sliceCS₁₃`/`sliceCS₂₃`/`sliceCS₃₃`. -/

/-- `t₁`-slice continuity: for fixed `(t₂,t₃,t₄)` in the base `3`-simplex, the slice
`t₁ ↦ F t₁ t₂ t₃ t₄` is `ContinuousOn (Icc 0 (1−t₂−t₃−t₄))`. -/
theorem slice_cont₁₄ {F : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄)
    {t₂ t₃ t₄ : ℝ} (h2 : 0 ≤ t₂) (h3 : 0 ≤ t₃) (h4 : 0 ≤ t₄) :
    ContinuousOn (fun t₁ => F t₁ t₂ t₃ t₄) (Set.Icc 0 (1 - t₂ - t₃ - t₄)) := by
  have hmap : Set.MapsTo (fun t₁ : ℝ => (t₁, t₂, t₃, t₄)) (Set.Icc 0 (1 - t₂ - t₃ - t₄)) R₄ := by
    intro t₁ ht₁; exact ⟨ht₁.1, h2, h3, h4, by linarith [ht₁.2]⟩
  have hcont : Continuous (fun t₁ : ℝ => (t₁, t₂, t₃, t₄)) := by fun_prop
  exact hF.comp hcont.continuousOn hmap

/-- `t₂`-slice continuity: for fixed `(t₁,t₃,t₄)`, `t₂ ↦ F t₁ t₂ t₃ t₄` is
`ContinuousOn (Icc 0 (1−t₁−t₃−t₄))`. -/
theorem slice_cont₂₄ {F : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄)
    {t₁ t₃ t₄ : ℝ} (h1 : 0 ≤ t₁) (h3 : 0 ≤ t₃) (h4 : 0 ≤ t₄) :
    ContinuousOn (fun t₂ => F t₁ t₂ t₃ t₄) (Set.Icc 0 (1 - t₁ - t₃ - t₄)) := by
  have hmap : Set.MapsTo (fun t₂ : ℝ => (t₁, t₂, t₃, t₄)) (Set.Icc 0 (1 - t₁ - t₃ - t₄)) R₄ := by
    intro t₂ ht₂; exact ⟨h1, ht₂.1, h3, h4, by linarith [ht₂.2]⟩
  have hcont : Continuous (fun t₂ : ℝ => (t₁, t₂, t₃, t₄)) := by fun_prop
  exact hF.comp hcont.continuousOn hmap

/-- `t₃`-slice continuity: for fixed `(t₁,t₂,t₄)`, `t₃ ↦ F t₁ t₂ t₃ t₄` is
`ContinuousOn (Icc 0 (1−t₁−t₂−t₄))`. -/
theorem slice_cont₃₄ {F : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄)
    {t₁ t₂ t₄ : ℝ} (h1 : 0 ≤ t₁) (h2 : 0 ≤ t₂) (h4 : 0 ≤ t₄) :
    ContinuousOn (fun t₃ => F t₁ t₂ t₃ t₄) (Set.Icc 0 (1 - t₁ - t₂ - t₄)) := by
  have hmap : Set.MapsTo (fun t₃ : ℝ => (t₁, t₂, t₃, t₄)) (Set.Icc 0 (1 - t₁ - t₂ - t₄)) R₄ := by
    intro t₃ ht₃; exact ⟨h1, h2, ht₃.1, h4, by linarith [ht₃.2]⟩
  have hcont : Continuous (fun t₃ : ℝ => (t₁, t₂, t₃, t₄)) := by fun_prop
  exact hF.comp hcont.continuousOn hmap

/-- `t₄`-slice continuity: for fixed `(t₁,t₂,t₃)`, `t₄ ↦ F t₁ t₂ t₃ t₄` is
`ContinuousOn (Icc 0 (1−t₁−t₂−t₃))`. -/
theorem slice_cont₄₄ {F : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄)
    {t₁ t₂ t₃ : ℝ} (h1 : 0 ≤ t₁) (h2 : 0 ≤ t₂) (h3 : 0 ≤ t₃) :
    ContinuousOn (fun t₄ => F t₁ t₂ t₃ t₄) (Set.Icc 0 (1 - t₁ - t₂ - t₃)) := by
  have hmap : Set.MapsTo (fun t₄ : ℝ => (t₁, t₂, t₃, t₄)) (Set.Icc 0 (1 - t₁ - t₂ - t₃)) R₄ := by
    intro t₄ ht₄; exact ⟨h1, h2, h3, ht₄.1, by linarith [ht₄.2]⟩
  have hcont : Continuous (fun t₄ : ℝ => (t₁, t₂, t₃, t₄)) := by fun_prop
  exact hF.comp hcont.continuousOn hmap

/-- **`t₁` slice bound.** `(∫₀^{1−t₂−t₃−t₄} F)² ≤ log 4 · ∫₀^{1−t₂−t₃−t₄} w₁₄·F²`. -/
theorem sliceCS₁₄ {F : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄)
    {t₂ t₃ t₄ : ℝ} (h2 : 0 ≤ t₂) (h3 : 0 ≤ t₃) (h4 : 0 ≤ t₄) (h : t₂ + t₃ + t₄ ≤ 1) :
    (∫ t₁ in (0:ℝ)..(1 - t₂ - t₃ - t₄), F t₁ t₂ t₃ t₄) ^ 2
      ≤ Real.log 4 * ∫ t₁ in (0:ℝ)..(1 - t₂ - t₃ - t₄), w₁₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
  have hbound := log_slice_CS_third (φ := fun t₁ => F t₁ t₂ t₃ t₄) (a := 1 - t₂ - t₃ - t₄)
    (by linarith) (slice_cont₁₄ hF h2 h3 h4)
  have hrw : (∫ t₁ in (0:ℝ)..(1 - t₂ - t₃ - t₄),
        ((1 - t₂ - t₃ - t₄) / 3 + t₁) * (F t₁ t₂ t₃ t₄) ^ 2)
      = ∫ t₁ in (0:ℝ)..(1 - t₂ - t₃ - t₄), w₁₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := rfl
  rwa [hrw] at hbound

/-- **`t₂` slice bound.** `(∫₀^{1−t₁−t₃−t₄} F)² ≤ log 4 · ∫₀^{1−t₁−t₃−t₄} w₂₄·F²`. -/
theorem sliceCS₂₄ {F : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄)
    {t₁ t₃ t₄ : ℝ} (h1 : 0 ≤ t₁) (h3 : 0 ≤ t₃) (h4 : 0 ≤ t₄) (h : t₁ + t₃ + t₄ ≤ 1) :
    (∫ t₂ in (0:ℝ)..(1 - t₁ - t₃ - t₄), F t₁ t₂ t₃ t₄) ^ 2
      ≤ Real.log 4 * ∫ t₂ in (0:ℝ)..(1 - t₁ - t₃ - t₄), w₂₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
  have hbound := log_slice_CS_third (φ := fun t₂ => F t₁ t₂ t₃ t₄) (a := 1 - t₁ - t₃ - t₄)
    (by linarith) (slice_cont₂₄ hF h1 h3 h4)
  have hrw : (∫ t₂ in (0:ℝ)..(1 - t₁ - t₃ - t₄),
        ((1 - t₁ - t₃ - t₄) / 3 + t₂) * (F t₁ t₂ t₃ t₄) ^ 2)
      = ∫ t₂ in (0:ℝ)..(1 - t₁ - t₃ - t₄), w₂₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := rfl
  rwa [hrw] at hbound

/-- **`t₃` slice bound.** `(∫₀^{1−t₁−t₂−t₄} F)² ≤ log 4 · ∫₀^{1−t₁−t₂−t₄} w₃₄·F²`. -/
theorem sliceCS₃₄ {F : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄)
    {t₁ t₂ t₄ : ℝ} (h1 : 0 ≤ t₁) (h2 : 0 ≤ t₂) (h4 : 0 ≤ t₄) (h : t₁ + t₂ + t₄ ≤ 1) :
    (∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄), F t₁ t₂ t₃ t₄) ^ 2
      ≤ Real.log 4 * ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄), w₃₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
  have hbound := log_slice_CS_third (φ := fun t₃ => F t₁ t₂ t₃ t₄) (a := 1 - t₁ - t₂ - t₄)
    (by linarith) (slice_cont₃₄ hF h1 h2 h4)
  have hrw : (∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄),
        ((1 - t₁ - t₂ - t₄) / 3 + t₃) * (F t₁ t₂ t₃ t₄) ^ 2)
      = ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄), w₃₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := rfl
  rwa [hrw] at hbound

/-- **`t₄` slice bound.** `(∫₀^{1−t₁−t₂−t₃} F)² ≤ log 4 · ∫₀^{1−t₁−t₂−t₃} w₄₄·F²`. -/
theorem sliceCS₄₄ {F : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄)
    {t₁ t₂ t₃ : ℝ} (h1 : 0 ≤ t₁) (h2 : 0 ≤ t₂) (h3 : 0 ≤ t₃) (h : t₁ + t₂ + t₃ ≤ 1) :
    (∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), F t₁ t₂ t₃ t₄) ^ 2
      ≤ Real.log 4 * ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), w₄₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
  have hbound := log_slice_CS_third (φ := fun t₄ => F t₁ t₂ t₃ t₄) (a := 1 - t₁ - t₂ - t₃)
    (by linarith) (slice_cont₄₄ hF h1 h2 h3)
  have hrw : (∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃),
        ((1 - t₁ - t₂ - t₃) / 3 + t₄) * (F t₁ t₂ t₃ t₄) ^ 2)
      = ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), w₄₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := rfl
  rwa [hrw] at hbound

/-! ## The assembly target and the `k = 4` no-go (modulo the `4`-D Fubini assembly)

The analytic content above is complete and sharp: on every slice the retuned CS
gives `(∫ F)² ≤ log 4 · ∫ w_m·F²` (`sliceCS₁₄`/`sliceCS₂₄`/`sliceCS₃₄`/`sliceCS₄₄`),
and the four weights sum to the constant `4/3` (`w_sum_four`). What remains to
conclude `four_bar : J₁₄ + J₂₄ + J₃₄ + J₄₄ ≤ (4/3)·log 4 · I₄` is purely the `k = 4`
Fubini/Tonelli assembly — the same bookkeeping the landed `k = 3` assembly
(`three_bar` in `ThreeBarAsm.lean`) performs, one dimension up (nodes N4-ASM-a/b/c,
NOT in this file). -/

/-- **The `k = 4` bound as a citable target** (`FourBar`). Stated as a `Prop`
(a `def`, mirroring `TripleBar`), NOT proved here: the sharp `M₄ ≤ (4/3)·log 4` for
every continuous weight on `R₄`. The per-slice content (`sliceCS₁₄…sliceCS₄₄`,
`w_sum_four`) is complete; only the `4`-D Fubini assembly is outstanding. -/
def FourBar : Prop :=
  ∀ F : ℝ → ℝ → ℝ → ℝ → ℝ,
    ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄ →
    J₁₄ F + J₂₄ F + J₃₄ F + J₄₄ F ≤ (4 / 3) * Real.log 4 * I₄ F

/-- **The `k = 4` no-go, modulo the bound** (`no_quad_weight_of_fourBar`). GIVEN
`FourBar` (the `4`-D-Fubini assembly of the landed per-slice content), the `k = 4`
twin gate is unsatisfiable: NO continuous weight `F` on `R₄` with positive
`L²`-mass has `2·I₄ F < J₁₄ F + J₂₄ F + J₃₄ F + J₄₄ F`. The proof is the exact
`k = 4` analogue of `no_triple_weight_of_tripleBar` — the sharp constant is
sub-gate, `(4/3)·log 4 < 2` (`four_thirds_log_four_lt_two`), and `0 < I₄ F`. This
exhibits that once the assembly lands, `M₄ < 2`: `k = 4` is provably too small for
the unmodified Maynard sieve to force two primes (the atlas's third delimitation,
matching Polymath8b's `M_k ≤ (k/(k−1))·log k`). -/
theorem no_quad_weight_of_fourBar (h : FourBar) :
    ¬ ∃ F : ℝ → ℝ → ℝ → ℝ → ℝ,
      ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄ ∧
      0 < I₄ F ∧ 2 * I₄ F < J₁₄ F + J₂₄ F + J₃₄ F + J₄₄ F := by
  rintro ⟨F, hF, hI, hlt⟩
  have hbar := h F hF
  nlinarith [hbar, hlt,
    mul_pos (show (0:ℝ) < 2 - (4 / 3) * Real.log 4 by linarith [four_thirds_log_four_lt_two]) hI]

end Salt.TwinBar
