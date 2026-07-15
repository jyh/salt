/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.SliceCS
import Salt.TwinBar.Tonelli

/-!
# Exploration pilot P-C — the delimitation machinery at `k = 3`

**This is EXPLORATION, not a frozen blueprint node.** Design context:
`docs/exploration/pilot.md` (probe P-C) and `docs/writeup/pre-outline.md` §7. The
file adds NEW work only; it edits no landed file and is not wired into
`Salt.TwinBar.All`. Everything here is sorry-free and axiom-clean; any residual
OPEN questions are recorded as prose, never as a `sorry`'d theorem.

## The target (recon, R1): the Maynard–Selberg functional at `k = 3`

Polymath8b (arXiv:1407.4897) eq. (31)–(33), specialised to `k = 3`. `F` is a
continuous weight on the closed `3`-simplex
`R₃ = {(t₁,t₂,t₃) | tᵢ ≥ 0, t₁+t₂+t₃ ≤ 1}`. The carriers, in the nested-1D form
mirroring `Salt/TwinBar/Defs.lean`'s `k = 2` conventions (`I₂`/`J₁`/`J₂` there):

* `I₃ F = ∭_{R₃} F²` — the `L²`-mass (eq. 33).
* `J₁₃ F`, `J₂₃ F`, `J₃₃ F` — the three Selberg peels (eq. 31–32): `J_{m}` is the
  square of the marginal in the `m`-th variable, integrated over the other two.
  Each is written with its marginal variable *innermost* so the per-slice
  Cauchy–Schwarz applies directly.

`M₃ := sup_F (J₁₃ + J₂₃ + J₃₃)/I₃`. The DHL[3,2] gate is `M₃ > 2` (level of
distribution `θ = 1`, EH); crossing it would give two primes in every admissible
`3`-tuple infinitely often. The classical fact (Polymath8b) is `M₃ < 2`: `k = 3`
is *too small* for the Maynard sieve to force two primes — the sharp upper bound
is `M_k ≤ (k/(k−1))·log k`, giving `(3/2)·log 3 ≈ 1.648` at `k = 3`.

## The carrier-shape decision (R1/R3 — load-bearing; frozen here)

The `k = 2` carriers slice the outer variable on `[0,1]` and the inner on
`[0, 1−t₂]`. At `k = 3` the honest nested shape has TWO outer variables (a
`2`-simplex) and one inner:

* `I₃`: `∫_{t₃∈[0,1]} ∫_{t₂∈[0,1−t₃]} ∫_{t₁∈[0,1−t₃−t₂]} F²` (canonical order).
* `J₁₃` (marginal `t₁`): `∫_{t₃}∫_{t₂} (∫_{t₁∈[0,1−t₃−t₂]} F)²`.
* `J₂₃` (marginal `t₂`): `∫_{t₃}∫_{t₁} (∫_{t₂∈[0,1−t₃−t₁]} F)²`.
* `J₃₃` (marginal `t₃`): `∫_{t₁}∫_{t₂} (∫_{t₃∈[0,1−t₁−t₂]} F)²`.

There is a genuine choice of *which of the two outer variables is outermost* in
each `J`; it does not change the value (Tonelli), and each `J` is written in the
order its slicing produces. This is the only ambiguity and it is value-neutral
(R3 clears: no carrier-shape choice changes the constant).

## The key mathematical finding (the retuned CS base)

The `k = 2` no-go is driven by the "magic identity" `w₁ + w₂ ≡ 2`, where
`w_m = (slice length) + t_m` and the per-slice normalisation `∫₀^a (a+t)⁻¹ = log 2`
is `a`-uniform. Writing the CS base as `β·(slice length)`, the normalisation
becomes `log((β+1)/β)` (still `a`-uniform) and the weight `w_m = β·(slice length)
+ t_m` has

  `Σ_{m=1}^k w_m = β·k − (β(k−1) − 1)·s`,  `s := Σ tᵢ`,

which is CONSTANT in `s` **iff `β = 1/(k−1)`**, giving normalisation `log k` and
constant sum `k/(k−1)`. Hence the sharp

  `Σ_m J_m ≤ (k/(k−1))·log k · I_k`  — Polymath8b's bound, re-derived.

* `k = 2`: `β = 1`, base `= slice length`, `log 2`, sum `2` — the landed
  `twin_bar` (`2·log 2`).
* `k = 3`: `β = 1/2`, base `= (slice length)/2`, normalisation `log 3`
  (`logWeight_half`), and the CONSTANT weight-sum **`w₁ + w₂ + w₃ ≡ 3/2`**
  (`w_sum_three`). Therefore `M₃ ≤ (3/2)·log 3 < 2` — the sharp constant, and a
  `k = 3` NO-GO.

So the `k = 2` "magic" is not special to constancy `= 2`; it is the `β = 1/(k−1)`
tuning, and at `k = 3` the constant is `3/2`, sub-`2`. The pilot brief's guessed
`3·log 2 ≈ 2.079` is exactly the WRONG base `β = 1` (the naive pull-back of the
landed `k = 2` weight): valid but `> 2`, hence no no-go. The `(3/2)·log 3` result
requires the retuned base — that extra tuning is what buys the delimitation.

## Route log (R2 first: can we pull back onto the landed `twin_bar`?)

* **Route (b), the pull-back (assessed, REJECTED as insufficient).** Each
  `t₃`-slice of `R₃` is a scaled `2`-simplex; applying the landed `twin_bar` per
  slice and symmetrising over the three slicing directions gives
  `J₁₃ + J₂₃ + J₃₃ ≤ 3·log 2·I₃`. But `twin_bar` bakes in base `β = 1`
  (sum `= 2`), so the pull-back is STUCK at `3·log 2 ≈ 2.079 > 2` — no no-go.
  The sharp constant is unreachable by pull-back; it needs the retuned base
  `β = 1/2`, i.e. a direct port of the CS atom. (Process datum: unlike P-A, here
  the cheap pull-back does not reach the reportable threshold — the extra work of
  the direct port is mathematically necessary, not gold-plating.)
* **Route (a), the direct port (TAKEN).** Reuse the clean `k = 2` atoms
  `interval_CS` (sign-agnostic discriminant CS) and the shift-normalisation, at
  base `(slice length)/2`. The analytic heart — `logWeight_half`, the general
  sharp per-slice CS `log_slice_CS`, the three slice bounds `sliceCS_m3`, the
  constant weight-sum `w_sum_three`, and the numeric `(3/2)·log 3 < 2` — is
  landed below, kernel-checked and axiom-clean.

## Status of the final assembly (`three_bar`) — see the OPEN note at the end

The per-slice sharp bound holds on every slice with constant `3/2`; assembling
`three_bar : J₁₃ + J₂₃ + J₃₃ ≤ (3/2)·log 3 · I₃` from the three slice bounds needs
the `k = 3` analogue of the landed `simplex_swap` (`Salt/TwinBar/Tonelli.lean`) and
`marginal₁_integrableOn` (`Salt/TwinBar/Impossibility.lean`) — a `3`-D
Fubini/Tonelli reconciliation of the three marginal-innermost weighted masses into
a common order. The target is stated as the citable `def TripleBar`, and the no-go
`no_triple_weight_of_tripleBar` (the exact `k = 3` analogue of `no_twin_weight`) is
proved *modulo* `TripleBar` — exhibiting that the `3`-D assembly is the ONLY missing
input to `M₃ < 2`. See the `-- OPEN:` section for the precise remaining step.

## Budget / stopping-rule note (pilot calibration — P-C's primary datum)

Unlike P-A (whose δ-enlargement admitted a cheap change-of-variables *pull-back*
onto the landed `twin_bar`, landing its theorem first-attempt), the sharp `k = 3`
result has NO cheap pull-back: the naive pull-back (base `β = 1`, `twin_bar` per
slice + symmetrise) caps at `3·log 2 ≈ 2.079 > 2` — valid but no no-go. The sharp
`(3/2)·log 3 < 2` requires the retuned base `β = 1/2`, i.e. a direct CS port. That
analytic port is cheap and landed here (this file); its *assembly* into a single
scalar `≤ I₃`, however, is a ~300–500-line `3`-D measure-theory build with no
turnkey mathlib support — a multi-session task, not a pilot probe. Per the pilot's
"give up early, loudly", the assembly was DEFERRED with a precise OPEN note rather
than ground out. Calibration takeaway: a T3 probe at `k = 3` splits cleanly into a
cheap "find the sharp constant" phase (hours) and an expensive "formal Fubini
assembly" phase (a rung of its own) — budget them separately.
-/

namespace Salt.TwinBar

open MeasureTheory Set Function intervalIntegral

/-! ## The `k = 3` carriers (nested-1D, mirroring `Defs.lean`) -/

/-- The closed `3`-simplex `R₃ = {0 ≤ t₁, 0 ≤ t₂, 0 ≤ t₃, t₁+t₂+t₃ ≤ 1}`. -/
def R₃ : Set (ℝ × ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 ≤ 1}

/-- `I₃ F = ∭_{R₃} F²` in canonical nested order (`t₃` outer, `t₂` mid, `t₁`
inner). The `L²`-mass carrier (Polymath8b eq. 33 at `k = 3`). -/
noncomputable def I₃ (F : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₃ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₃), ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), (F t₁ t₂ t₃) ^ 2

/-- `J₁₃ F` — the marginal-in-`t₁` Selberg peel (eq. 31), `t₁` innermost. -/
noncomputable def J₁₃ (F : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₃ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₃), (∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), F t₁ t₂ t₃) ^ 2

/-- `J₂₃ F` — the marginal-in-`t₂` Selberg peel, `t₂` innermost. -/
noncomputable def J₂₃ (F : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₃ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₃), (∫ t₂ in (0:ℝ)..(1 - t₃ - t₁), F t₁ t₂ t₃) ^ 2

/-- `J₃₃ F` — the marginal-in-`t₃` Selberg peel, `t₃` innermost. -/
noncomputable def J₃₃ (F : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁), (∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), F t₁ t₂ t₃) ^ 2

/-! ## Nonnegativity of the carriers -/

/-- `0 ≤ I₃ F`. Three nested `integral_nonneg` over correctly-oriented ranges. -/
theorem I₃_nonneg (F : ℝ → ℝ → ℝ → ℝ) : 0 ≤ I₃ F := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro t₃ ht₃
  apply intervalIntegral.integral_nonneg (by have := ht₃.2; linarith : (0:ℝ) ≤ 1 - t₃)
  intro t₂ ht₂
  apply intervalIntegral.integral_nonneg (by have := ht₂.2; linarith :
    (0:ℝ) ≤ 1 - t₃ - t₂)
  intro t₁ _
  positivity

/-- `0 ≤ J₁₃ F`. Outer integrand is a square. -/
theorem J₁₃_nonneg (F : ℝ → ℝ → ℝ → ℝ) : 0 ≤ J₁₃ F := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro t₃ ht₃
  apply intervalIntegral.integral_nonneg (by have := ht₃.2; linarith : (0:ℝ) ≤ 1 - t₃)
  intro t₂ _; positivity

/-- `0 ≤ J₂₃ F`. -/
theorem J₂₃_nonneg (F : ℝ → ℝ → ℝ → ℝ) : 0 ≤ J₂₃ F := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro t₃ ht₃
  apply intervalIntegral.integral_nonneg (by have := ht₃.2; linarith : (0:ℝ) ≤ 1 - t₃)
  intro t₁ _; positivity

/-- `0 ≤ J₃₃ F`. -/
theorem J₃₃_nonneg (F : ℝ → ℝ → ℝ → ℝ) : 0 ≤ J₃₃ F := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro t₁ ht₁
  apply intervalIntegral.integral_nonneg (by have := ht₁.2; linarith : (0:ℝ) ≤ 1 - t₁)
  intro t₂ _; positivity

/-! ## The retuned Cauchy–Schwarz weights (base `= (slice length)/2`, `β = 1/2`) -/

/-- The first weight `w₁₃ (t₁,t₂,t₃) = (1 − t₂ − t₃)/2 + t₁ = (base) + t₁` with
base `(1−t₂−t₃)/2` half the `t₁`-slice length. -/
noncomputable def w₁₃ (t₁ t₂ t₃ : ℝ) : ℝ := (1 - t₂ - t₃) / 2 + t₁

/-- The second weight `w₂₃ (t₁,t₂,t₃) = (1 − t₁ − t₃)/2 + t₂`. -/
noncomputable def w₂₃ (t₁ t₂ t₃ : ℝ) : ℝ := (1 - t₁ - t₃) / 2 + t₂

/-- The third weight `w₃₃ (t₁,t₂,t₃) = (1 − t₁ − t₂)/2 + t₃`. -/
noncomputable def w₃₃ (t₁ t₂ t₃ : ℝ) : ℝ := (1 - t₁ - t₂) / 2 + t₃

/-- **The `k = 3` magic identity.** `w₁₃ + w₂₃ + w₃₃ ≡ 3/2` pointwise — the
constant weight-sum from the retuned base `β = 1/2`. This is the `k = 3` analogue
of the landed `w₁_add_w₂ : w₁ + w₂ = 2`; the constant is `k/(k−1) = 3/2`. -/
theorem w_sum_three (t₁ t₂ t₃ : ℝ) : w₁₃ t₁ t₂ t₃ + w₂₃ t₁ t₂ t₃ + w₃₃ t₁ t₂ t₃ = 3 / 2 := by
  unfold w₁₃ w₂₃ w₃₃; ring

/-- `0 ≤ w₁₃` on `R₃`: base `≥ 0` (from `t₂+t₃ ≤ 1`) and `t₁ ≥ 0`. -/
theorem w₁₃_nonneg {t₁ t₂ t₃ : ℝ} (h1 : 0 ≤ t₁) (h : t₂ + t₃ ≤ 1) : 0 ≤ w₁₃ t₁ t₂ t₃ := by
  unfold w₁₃; linarith

/-- `0 ≤ w₂₃` on `R₃`. -/
theorem w₂₃_nonneg {t₁ t₂ t₃ : ℝ} (h2 : 0 ≤ t₂) (h : t₁ + t₃ ≤ 1) : 0 ≤ w₂₃ t₁ t₂ t₃ := by
  unfold w₂₃; linarith

/-- `0 ≤ w₃₃` on `R₃`. -/
theorem w₃₃_nonneg {t₁ t₂ t₃ : ℝ} (h3 : 0 ≤ t₃) (h : t₁ + t₂ ≤ 1) : 0 ≤ w₃₃ t₁ t₂ t₃ := by
  unfold w₃₃; linarith

/-! ## The retuned normalisation `∫₀^a (a/2 + t)⁻¹ = log 3` -/

/-- **The retuned log-weight integral** (the `k = 3` analogue of `logWeight`). For
`a > 0`, `∫₀^a (a/2 + t)⁻¹ dt = log 3`: the shift `t ↦ a/2 + t` lands the range
`a/2 .. 3a/2`, and `∫ x⁻¹` collapses `log((3a/2)/(a/2)) = log 3`. The base `a/2`
(half the slice length) is the `β = 1/2` retuning; base `a` would give `log 2`. -/
theorem logWeight_half {a : ℝ} (ha : 0 < a) :
    ∫ t in (0:ℝ)..a, (a / 2 + t)⁻¹ = Real.log 3 := by
  have hshift : (∫ t in (0:ℝ)..a, (fun x : ℝ => x⁻¹) (a / 2 + t))
      = ∫ x in a / 2 + 0..a / 2 + a, (fun x : ℝ => x⁻¹) x :=
    intervalIntegral.integral_comp_add_left (fun x : ℝ => x⁻¹) (a / 2)
  simp only [add_zero] at hshift
  rw [hshift]
  have h32 : a / 2 + a = 3 * (a / 2) := by ring
  rw [h32, integral_inv_of_pos (by linarith : (0:ℝ) < a / 2) (by linarith : (0:ℝ) < 3 * (a / 2)),
    mul_div_assoc, div_self (by linarith : a / 2 ≠ 0), mul_one]

/-! ## The general sharp per-slice Cauchy–Schwarz (base `a/2`) -/

/-- **The sharp per-slice CS.** For continuous `φ` on `[0, a]` (`a ≥ 0`),
`(∫₀^a φ)² ≤ log 3 · ∫₀^a (a/2 + t)·φ(t)² dt`. This is the base-`a/2` retuning of
the landed `sliceCS₁`/`sliceCS₂`: instantiate the sign-agnostic `interval_CS` with
`f := √((a/2+t)⁻¹)`, `g := √(a/2+t)·φ` so `f·g = φ`, `f² = (a/2+t)⁻¹`
(`∫ f² = log 3` by `logWeight_half`), `g² = (a/2+t)·φ²`. The `a = 0` slice is
`0 ≤ 0`. -/
theorem log_slice_CS {φ : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hφ : ContinuousOn φ (Set.Icc 0 a)) :
    (∫ t in (0:ℝ)..a, φ t) ^ 2 ≤ Real.log 3 * ∫ t in (0:ℝ)..a, (a / 2 + t) * (φ t) ^ 2 := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · rw [← ha0]; simp
  -- `a > 0`. Positivity of `a/2 + x` on both interval flavours.
  have hpos_uIcc : ∀ x ∈ Set.uIcc (0:ℝ) a, 0 < a / 2 + x := by
    intro x hx; rw [Set.uIcc_of_le hapos.le] at hx; have := hx.1; linarith
  have hpos_uIoc : ∀ x ∈ Set.uIoc (0:ℝ) a, 0 < a / 2 + x := by
    intro x hx; rw [Set.uIoc_of_le hapos.le] at hx; have := hx.1; linarith
  have hφicc : ContinuousOn φ (Set.uIcc 0 a) := by rw [Set.uIcc_of_le hapos.le]; exact hφ
  have hφii : IntervalIntegrable φ volume 0 a := hφicc.intervalIntegrable
  -- Integrability of the reciprocal weight and the weighted square.
  have hinv_ii : IntervalIntegrable (fun x => (a / 2 + x)⁻¹) volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hapos.le]
    exact ContinuousOn.inv₀ (by fun_prop) (fun x hx => by
      have : (0:ℝ) < a / 2 + x := by have := hx.1; linarith
      exact this.ne')
  have hweight_ii : IntervalIntegrable (fun x => (a / 2 + x) * (φ x) ^ 2) volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hapos.le]
    exact (by fun_prop : ContinuousOn (fun x : ℝ => a / 2 + x) (Set.Icc 0 a)).mul (hφ.pow 2)
  -- The three `interval_CS` ingredients via `.congr` from the nice forms.
  have hf2ii : IntervalIntegrable (fun x => Real.sqrt ((a / 2 + x)⁻¹) ^ 2) volume 0 a :=
    hinv_ii.congr (fun x hx => (Real.sq_sqrt (inv_nonneg.mpr (hpos_uIoc x hx).le)).symm)
  have hg2ii : IntervalIntegrable (fun x => (Real.sqrt (a / 2 + x) * φ x) ^ 2) volume 0 a :=
    hweight_ii.congr (by
      intro x hx
      have : (Real.sqrt (a / 2 + x) * φ x) ^ 2 = (a / 2 + x) * (φ x) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (hpos_uIoc x hx).le]
      exact this.symm)
  have hfgii : IntervalIntegrable
      (fun x => Real.sqrt ((a / 2 + x)⁻¹) * (Real.sqrt (a / 2 + x) * φ x)) volume 0 a :=
    hφii.congr (by
      intro x hx
      have hne : Real.sqrt (a / 2 + x) ≠ 0 := (Real.sqrt_pos.mpr (hpos_uIoc x hx)).ne'
      have : Real.sqrt ((a / 2 + x)⁻¹) * (Real.sqrt (a / 2 + x) * φ x) = φ x := by
        rw [Real.sqrt_inv, inv_mul_cancel_left₀ hne]
      exact this.symm)
  -- Value rewrites.
  have hf2val : (∫ x in (0:ℝ)..a, Real.sqrt ((a / 2 + x)⁻¹) ^ 2) = Real.log 3 := by
    rw [intervalIntegral.integral_congr
          (fun x hx => Real.sq_sqrt (inv_nonneg.mpr (hpos_uIcc x hx).le))]
    exact logWeight_half hapos
  have hg2val : (∫ x in (0:ℝ)..a, (Real.sqrt (a / 2 + x) * φ x) ^ 2)
      = ∫ x in (0:ℝ)..a, (a / 2 + x) * (φ x) ^ 2 :=
    intervalIntegral.integral_congr (by
      intro x hx
      have hh : (Real.sqrt (a / 2 + x) * φ x) ^ 2 = (a / 2 + x) * (φ x) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (hpos_uIcc x hx).le]
      exact hh)
  have hfgval : (∫ x in (0:ℝ)..a, Real.sqrt ((a / 2 + x)⁻¹) * (Real.sqrt (a / 2 + x) * φ x))
      = ∫ x in (0:ℝ)..a, φ x :=
    intervalIntegral.integral_congr (by
      intro x hx
      have hne : Real.sqrt (a / 2 + x) ≠ 0 := (Real.sqrt_pos.mpr (hpos_uIcc x hx)).ne'
      have hh : Real.sqrt ((a / 2 + x)⁻¹) * (Real.sqrt (a / 2 + x) * φ x) = φ x := by
        rw [Real.sqrt_inv, inv_mul_cancel_left₀ hne]
      exact hh)
  -- Assemble via `interval_CS`.
  have hCS : (∫ x in (0:ℝ)..a, Real.sqrt ((a / 2 + x)⁻¹) * (Real.sqrt (a / 2 + x) * φ x)) ^ 2
      ≤ (∫ x in (0:ℝ)..a, Real.sqrt ((a / 2 + x)⁻¹) ^ 2)
        * (∫ x in (0:ℝ)..a, (Real.sqrt (a / 2 + x) * φ x) ^ 2) :=
    interval_CS (f := fun t => Real.sqrt ((a / 2 + t)⁻¹))
      (g := fun t => Real.sqrt (a / 2 + t) * φ t) hapos.le hf2ii hg2ii hfgii
  rw [hfgval, hf2val, hg2val] at hCS
  exact hCS

/-! ## The numeric atom `(3/2)·log 3 < 2` (the sub-gate constant) -/

/-- **`(3/2)·log 3 < 2`.** Equivalent to `log 3 < 4/3`, i.e. `3 < e^{4/3}`. Via
`e^{4/3} = e·e^{1/3} > 2.718·(4/3) = 3.62 > 3` (`exp_one_gt_d9`, `add_one_le_exp`).
This is the `k = 3` no-go direction: the sharp constant is strictly below the twin
gate `2`. -/
theorem three_halves_log_three_lt_two : (3 / 2 : ℝ) * Real.log 3 < 2 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (4 / 3 : ℝ) ≤ Real.exp (1 / 3) := by
    have := Real.add_one_le_exp (1 / 3 : ℝ); linarith
  have hexp : (3 : ℝ) < Real.exp (4 / 3) := by
    have he : Real.exp (4 / 3 : ℝ) = Real.exp 1 * Real.exp (1 / 3) := by
      rw [← Real.exp_add]; norm_num
    rw [he]
    nlinarith [Real.exp_pos (1 / 3 : ℝ), Real.exp_pos (1 : ℝ), h1, h2]
  have hlog : Real.log 3 < 4 / 3 := by
    have h := Real.log_lt_log (by norm_num : (0:ℝ) < 3) hexp
    rwa [Real.log_exp] at h
  linarith

/-! ## The three sharp per-slice bounds (route (a) analytic heart)

For a continuous `F` on `R₃`, the marginal-innermost CS on each slice gives the
sharp base-`a/2` bound with normalisation `log 3` and weight `w_m`. These are the
`k = 3` analogues of the landed `sliceCS₁`/`sliceCS₂`. -/

/-- `t₁`-slice continuity: for fixed `(t₂,t₃)` in the base `2`-simplex, the slice
`t₁ ↦ F t₁ t₂ t₃` is `ContinuousOn (Icc 0 (1−t₂−t₃))`. -/
theorem slice_cont₁ {F : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃)
    {t₂ t₃ : ℝ} (h2 : 0 ≤ t₂) (h3 : 0 ≤ t₃) :
    ContinuousOn (fun t₁ => F t₁ t₂ t₃) (Set.Icc 0 (1 - t₂ - t₃)) := by
  have hmap : Set.MapsTo (fun t₁ : ℝ => (t₁, t₂, t₃)) (Set.Icc 0 (1 - t₂ - t₃)) R₃ := by
    intro t₁ ht₁; exact ⟨ht₁.1, h2, h3, by linarith [ht₁.2]⟩
  have hcont : Continuous (fun t₁ : ℝ => (t₁, t₂, t₃)) := by fun_prop
  exact hF.comp hcont.continuousOn hmap

/-- `t₂`-slice continuity: for fixed `(t₁,t₃)`, `t₂ ↦ F t₁ t₂ t₃` is
`ContinuousOn (Icc 0 (1−t₁−t₃))`. -/
theorem slice_cont₂ {F : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃)
    {t₁ t₃ : ℝ} (h1 : 0 ≤ t₁) (h3 : 0 ≤ t₃) :
    ContinuousOn (fun t₂ => F t₁ t₂ t₃) (Set.Icc 0 (1 - t₁ - t₃)) := by
  have hmap : Set.MapsTo (fun t₂ : ℝ => (t₁, t₂, t₃)) (Set.Icc 0 (1 - t₁ - t₃)) R₃ := by
    intro t₂ ht₂; exact ⟨h1, ht₂.1, h3, by linarith [ht₂.2]⟩
  have hcont : Continuous (fun t₂ : ℝ => (t₁, t₂, t₃)) := by fun_prop
  exact hF.comp hcont.continuousOn hmap

/-- `t₃`-slice continuity: for fixed `(t₁,t₂)`, `t₃ ↦ F t₁ t₂ t₃` is
`ContinuousOn (Icc 0 (1−t₁−t₂))`. -/
theorem slice_cont₃ {F : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃)
    {t₁ t₂ : ℝ} (h1 : 0 ≤ t₁) (h2 : 0 ≤ t₂) :
    ContinuousOn (fun t₃ => F t₁ t₂ t₃) (Set.Icc 0 (1 - t₁ - t₂)) := by
  have hmap : Set.MapsTo (fun t₃ : ℝ => (t₁, t₂, t₃)) (Set.Icc 0 (1 - t₁ - t₂)) R₃ := by
    intro t₃ ht₃; exact ⟨h1, h2, ht₃.1, by linarith [ht₃.2]⟩
  have hcont : Continuous (fun t₃ : ℝ => (t₁, t₂, t₃)) := by fun_prop
  exact hF.comp hcont.continuousOn hmap

/-- **`t₁` slice bound.** `(∫₀^{1−t₂−t₃} F)² ≤ log 3 · ∫₀^{1−t₂−t₃} w₁₃·F²`. -/
theorem sliceCS₁₃ {F : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃)
    {t₂ t₃ : ℝ} (h2 : 0 ≤ t₂) (h3 : 0 ≤ t₃) (h : t₂ + t₃ ≤ 1) :
    (∫ t₁ in (0:ℝ)..(1 - t₂ - t₃), F t₁ t₂ t₃) ^ 2
      ≤ Real.log 3 * ∫ t₁ in (0:ℝ)..(1 - t₂ - t₃), w₁₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 := by
  have hbound := log_slice_CS (φ := fun t₁ => F t₁ t₂ t₃) (a := 1 - t₂ - t₃)
    (by linarith) (slice_cont₁ hF h2 h3)
  -- `(a/2 + t₁) = w₁₃ t₁ t₂ t₃`.
  have hrw : (∫ t₁ in (0:ℝ)..(1 - t₂ - t₃), ((1 - t₂ - t₃) / 2 + t₁) * (F t₁ t₂ t₃) ^ 2)
      = ∫ t₁ in (0:ℝ)..(1 - t₂ - t₃), w₁₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 := rfl
  rwa [hrw] at hbound

/-- **`t₂` slice bound.** `(∫₀^{1−t₁−t₃} F)² ≤ log 3 · ∫₀^{1−t₁−t₃} w₂₃·F²`. -/
theorem sliceCS₂₃ {F : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃)
    {t₁ t₃ : ℝ} (h1 : 0 ≤ t₁) (h3 : 0 ≤ t₃) (h : t₁ + t₃ ≤ 1) :
    (∫ t₂ in (0:ℝ)..(1 - t₁ - t₃), F t₁ t₂ t₃) ^ 2
      ≤ Real.log 3 * ∫ t₂ in (0:ℝ)..(1 - t₁ - t₃), w₂₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 := by
  have hbound := log_slice_CS (φ := fun t₂ => F t₁ t₂ t₃) (a := 1 - t₁ - t₃)
    (by linarith) (slice_cont₂ hF h1 h3)
  have hrw : (∫ t₂ in (0:ℝ)..(1 - t₁ - t₃), ((1 - t₁ - t₃) / 2 + t₂) * (F t₁ t₂ t₃) ^ 2)
      = ∫ t₂ in (0:ℝ)..(1 - t₁ - t₃), w₂₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 := rfl
  rwa [hrw] at hbound

/-- **`t₃` slice bound.** `(∫₀^{1−t₁−t₂} F)² ≤ log 3 · ∫₀^{1−t₁−t₂} w₃₃·F²`. -/
theorem sliceCS₃₃ {F : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃)
    {t₁ t₂ : ℝ} (h1 : 0 ≤ t₁) (h2 : 0 ≤ t₂) (h : t₁ + t₂ ≤ 1) :
    (∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), F t₁ t₂ t₃) ^ 2
      ≤ Real.log 3 * ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), w₃₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 := by
  have hbound := log_slice_CS (φ := fun t₃ => F t₁ t₂ t₃) (a := 1 - t₁ - t₂)
    (by linarith) (slice_cont₃ hF h1 h2)
  have hrw : (∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), ((1 - t₁ - t₂) / 2 + t₃) * (F t₁ t₂ t₃) ^ 2)
      = ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), w₃₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 := rfl
  rwa [hrw] at hbound

/-! ## The assembly target and the precise OPEN obstruction

The analytic content above is complete and sharp: on every slice the retuned CS
gives `(∫ F)² ≤ log 3 · ∫ w_m·F²` (`sliceCS₁₃`/`sliceCS₂₃`/`sliceCS₃₃`), and the
three weights sum to the constant `3/2` (`w_sum_three`). What remains to conclude
`three_bar : J₁₃ + J₂₃ + J₃₃ ≤ (3/2)·log 3 · I₃` is purely the `k = 3`
Fubini/Tonelli assembly — the same bookkeeping the landed `k = 2` proof performs
(`marginal₁_integrableOn` + `simplex_swap`), one dimension up:

1. **Outer integration of each slice bound** (`J_{m,3} ≤ log 3 · W_m`, where
   `W_m := ∭ w_m·F²` with `t_m` innermost): integrate `sliceCS_m3` over the outer
   `2`-simplex with `integral_mono_of_nonneg`, whose dominating side needs the
   `k = 3` marginal-integrability lemma — the `3`-D analogue of the landed private
   `marginal₁_integrableOn`: a `2`-fold-nested marginal of the compact-simplex
   indicator `R₃.indicator (w_m·F²)`, integrable by `Integrable.integral_prod_right`
   applied twice.
2. **The three-way combine** (`W₁ + W₂ + W₃ = (3/2)·I₃`): the three `W_m` sit in
   three different nesting orders (each `t_m` innermost). Reconciling them to a
   common order — equivalently, `W_m = ∫_{R₃} w_m·F² d(vol₃)` for each `m` and
   `I₃ = ∫_{R₃} F²` — is the `3`-D analogue of `simplex_swap`; then
   `Σ W_m = ∫_{R₃}(Σ w_m)F² = (3/2)·∫_{R₃} F² = (3/2)·I₃` by `w_sum_three`
   (`w_m·F² ≥ 0` on `R₃` by `w₁₃_nonneg` etc., so every reorder is Tonelli, not
   signed Fubini).

`-- OPEN (P-C, recorded per the exploration STOP-AND-FLAG rule):` mathlib has no
turnkey "iterated interval-integral over the standard `k`-simplex = region
integral" (`regionBetween` is `2`-D area-under-a-graph only), so both (1) and (2)
must be hand-built as in `Salt/TwinBar/{Impossibility,Tonelli}.lean`. This is a
~300–500-line `3`-D measure-theory port with genuine mathlib-API friction, NOT a
pilot-sized task — see the calibration note in the module docstring. It is
deferred, not attempted, and no step is `sorry`'d. The scalar endgame below shows
this port is the ONLY missing input to the `k = 3` no-go. -/

/-- **The `k = 3` bound as a citable target** (`three_bar`). Stated as a `Prop`
(a `def`, mirroring P-A's `density_bridge_question`), NOT proved here: the sharp
`M₃ ≤ (3/2)·log 3` for every continuous weight on `R₃`. The per-slice content
(`sliceCS₁₃`/`sliceCS₂₃`/`sliceCS₃₃`, `w_sum_three`) is complete; only the `3`-D
Fubini assembly above is outstanding. -/
def TripleBar : Prop :=
  ∀ F : ℝ → ℝ → ℝ → ℝ, ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃ →
    J₁₃ F + J₂₃ F + J₃₃ F ≤ (3 / 2) * Real.log 3 * I₃ F

/-- **The `k = 3` no-go, modulo the bound** (`no_triple_weight_of_tripleBar`).
GIVEN `TripleBar` (the `3`-D-Fubini assembly of the landed per-slice content), the
`k = 3` twin gate is unsatisfiable: NO continuous weight `F` on `R₃` with positive
`L²`-mass has `2·I₃ F < J₁₃ F + J₂₃ F + J₃₃ F`. The proof is the exact `k = 3`
analogue of the landed `no_twin_weight` — the sharp constant is sub-gate,
`(3/2)·log 3 < 2` (`three_halves_log_three_lt_two`), and `0 < I₃ F`. This exhibits
that once the assembly lands, `M₃ < 2`: `k = 3` is provably too small for the
unmodified Maynard sieve to force two primes (the atlas's second delimitation,
matching Polymath8b's `M_k ≤ (k/(k−1))·log k`). -/
theorem no_triple_weight_of_tripleBar (h : TripleBar) :
    ¬ ∃ F : ℝ → ℝ → ℝ → ℝ, ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃ ∧
      0 < I₃ F ∧ 2 * I₃ F < J₁₃ F + J₂₃ F + J₃₃ F := by
  rintro ⟨F, hF, hI, hlt⟩
  have hbar := h F hF
  nlinarith [hbar, hlt,
    mul_pos (show (0:ℝ) < 2 - (3 / 2) * Real.log 3 by linarith [three_halves_log_three_lt_two]) hI]

end Salt.TwinBar
