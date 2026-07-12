/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.Impossibility

/-!
# The twin-bar rung (`twinbar`) — the possibility witness (the squeeze's lower jaw)

Design: `docs/blueprints/twinbar.md`. This module is the POSITIVE complement to the
landed impossibility theorem `twin_bar` (`Salt/TwinBar/Impossibility.lean`,
`J₁ F + J₂ F ≤ 2·log 2·I₂ F`). Together they two-sidedly pin the Maynard–Selberg
variational constant `M₂` for the twin tuple `{0, 2}` (`k = 2`):

  `1.383 ≤ M₂ ≤ 2·log 2 < 2`.

The upper jaw (`twin_bar`) is the certified impossibility: no continuous weight can
push the Selberg functional past `2·log 2`, hence never to the twin gate `2`. The
lower jaw is HERE: an explicit continuous weight `Fw` whose ratio
`(J₁ + J₂) / I₂` certifiably exceeds `1.383`, so the method DOES reach that far.

## The witness

`Fw t₁ t₂ = 1 + (9/7)·(1 − t₁ − t₂)` — a deliberately simple degree-1 polynomial,
near-optimal in its class (the degree-1 optimum is `c = (−2+√34)/3 ≈ 1.27698` with
ratio `≈ 1.38310`; the round value `c = 9/7 ≈ 1.28571` gives ratio
`212464/153615 ≈ 1.383095`, still above `1.383`). Its exact carrier values are the
three headliners below, computed by pedestrian polynomial interval integration:

  `I₂ Fw = 209/196`,   `J₁ Fw = J₂ Fw = 542/735`,   so `J₁ + J₂ = 1084/735`,
  and `(1084/735) / (209/196) = 212464/153615 ≈ 1.3831 > 1383/1000`.

## Honesty contract (read before quoting any theorem)

The true constant is `M₂ = 1/(1 − W(1/e)) ≈ 1.38593` (Polymath8b arXiv:1407.4897,
Cor. 6.3), which is NOT formalized here — `Fw` is a deliberately simple degree-1
polynomial chosen for a clean rational certificate, so the lower jaw we prove is
`1.383`, comfortably below the true `M₂` and far below the `2·log 2 ≈ 1.38629`
upper jaw. As with `twin_bar`, these are per-`F` statements over CONTINUOUS weights;
the density bridge to Polymath8b's `L²`-sup `M₂` (eq. 33) is a possible later
strengthening, not part of the floor. Neither jaw claims "sieves (can/cannot) prove
twin primes": parity-breaking (type-II / bilinear) inputs modify the functional and
lie outside this bound. The squeeze certifies the exact boundary of the UNMODIFIED
Maynard class — the method certifiably achieves `1.383` and certifiably cannot
reach `2`.

## The route (exact polynomial interval integration)

Two reusable FTC atoms — `integral_quartic` (`∫₀^a` of a degree-≤4 polynomial) and
`integral_one_sub_quartic` (`∫₀¹` of a degree-≤4 polynomial in `1 − x`) — reduce
every carrier to a rational endpoint computation. Each concrete integrand is
rewritten to canonical polynomial form via `intervalIntegral.integral_congr`
(`ring` pointwise), then the atom fires and `ring`/`norm_num` closes the arithmetic.
The values are FROZEN: they were hand-derived by Fable and re-verified here by the
Lean integrals, which agree exactly.
-/

namespace Salt.TwinBar

open intervalIntegral MeasureTheory Set

/-- **The possibility witness.** `Fw t₁ t₂ = 1 + (9/7)·(1 − t₁ − t₂)` — a degree-1
polynomial on the simplex, near-optimal in its class for the ratio `(J₁+J₂)/I₂`. -/
noncomputable def Fw (t₁ t₂ : ℝ) : ℝ := 1 + (9 / 7) * (1 - t₁ - t₂)

/-! ## FTC atoms for polynomial interval integrals -/

/-- `∫₀^a (c₀ + c₁·x + c₂·x² + c₃·x³ + c₄·x⁴) dx = c₀·a + c₁·a²/2 + c₂·a³/3
+ c₃·a⁴/4 + c₄·a⁵/5`, by FTC on the explicit antiderivative (works for any `a`, both
orientations, since it goes through `uIcc`). Used for the inner slice integrals. -/
private lemma integral_quartic (c₀ c₁ c₂ c₃ c₄ a : ℝ) :
    (∫ x in (0:ℝ)..a, c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4)
      = c₀ * a + c₁ * a ^ 2 / 2 + c₂ * a ^ 3 / 3 + c₃ * a ^ 4 / 4 + c₄ * a ^ 5 / 5 := by
  have hderiv : ∀ x ∈ uIcc (0:ℝ) a, HasDerivAt
      (fun x => c₀ * x + c₁ * x ^ 2 / 2 + c₂ * x ^ 3 / 3 + c₃ * x ^ 4 / 4 + c₄ * x ^ 5 / 5)
      (c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4) x := by
    intro x _
    have e0 : HasDerivAt (fun x : ℝ => c₀ * x) c₀ x := by
      simpa using (hasDerivAt_id x).const_mul c₀
    have e1 : HasDerivAt (fun x : ℝ => c₁ * x ^ 2 / 2) (c₁ * x) x := by
      have h := ((hasDerivAt_pow 2 x).const_mul c₁).div_const 2
      have heq : c₁ * (↑(2:ℕ) * x ^ (2 - 1)) / 2 = c₁ * x := by push_cast; ring
      rwa [heq] at h
    have e2 : HasDerivAt (fun x : ℝ => c₂ * x ^ 3 / 3) (c₂ * x ^ 2) x := by
      have h := ((hasDerivAt_pow 3 x).const_mul c₂).div_const 3
      have heq : c₂ * (↑(3:ℕ) * x ^ (3 - 1)) / 3 = c₂ * x ^ 2 := by push_cast; ring
      rwa [heq] at h
    have e3 : HasDerivAt (fun x : ℝ => c₃ * x ^ 4 / 4) (c₃ * x ^ 3) x := by
      have h := ((hasDerivAt_pow 4 x).const_mul c₃).div_const 4
      have heq : c₃ * (↑(4:ℕ) * x ^ (4 - 1)) / 4 = c₃ * x ^ 3 := by push_cast; ring
      rwa [heq] at h
    have e4 : HasDerivAt (fun x : ℝ => c₄ * x ^ 5 / 5) (c₄ * x ^ 4) x := by
      have h := ((hasDerivAt_pow 5 x).const_mul c₄).div_const 5
      have heq : c₄ * (↑(5:ℕ) * x ^ (5 - 1)) / 5 = c₄ * x ^ 4 := by push_cast; ring
      rwa [heq] at h
    exact ((((e0.add e1).add e2).add e3).add e4)
  have hint : IntervalIntegrable
      (fun x => c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4) volume 0 a := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- `∫₀¹ (c₀ + c₁(1−x) + c₂(1−x)² + c₃(1−x)³ + c₄(1−x)⁴) dx = c₀ + c₁/2 + c₂/3
+ c₃/4 + c₄/5`, by FTC on the antiderivative in `1 − x`. Used for the outer
integrals, whose integrands are naturally polynomials in `1 − t`. -/
private lemma integral_one_sub_quartic (c₀ c₁ c₂ c₃ c₄ : ℝ) :
    (∫ x in (0:ℝ)..1, c₀ + c₁ * (1 - x) + c₂ * (1 - x) ^ 2 + c₃ * (1 - x) ^ 3
        + c₄ * (1 - x) ^ 4)
      = c₀ + c₁ / 2 + c₂ / 3 + c₃ / 4 + c₄ / 5 := by
  have hderiv : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt
      (fun x => -(c₀ * (1 - x)) - c₁ * (1 - x) ^ 2 / 2 - c₂ * (1 - x) ^ 3 / 3
        - c₃ * (1 - x) ^ 4 / 4 - c₄ * (1 - x) ^ 5 / 5)
      (c₀ + c₁ * (1 - x) + c₂ * (1 - x) ^ 2 + c₃ * (1 - x) ^ 3 + c₄ * (1 - x) ^ 4) x := by
    intro x _
    have hb : HasDerivAt (fun x : ℝ => (1:ℝ) - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1:ℝ)
    have e0 : HasDerivAt (fun x : ℝ => -(c₀ * (1 - x))) c₀ x := by
      have h := (hb.const_mul c₀).neg
      have heq : -(c₀ * -1) = c₀ := by ring
      rwa [heq] at h
    have e1 : HasDerivAt (fun x : ℝ => c₁ * (1 - x) ^ 2 / 2) (-(c₁ * (1 - x))) x := by
      have h := ((hb.pow 2).const_mul c₁).div_const 2
      have heq : c₁ * (↑(2:ℕ) * (1 - x) ^ (2 - 1) * (-1)) / 2 = -(c₁ * (1 - x)) := by
        push_cast; ring
      rwa [heq] at h
    have e2 : HasDerivAt (fun x : ℝ => c₂ * (1 - x) ^ 3 / 3) (-(c₂ * (1 - x) ^ 2)) x := by
      have h := ((hb.pow 3).const_mul c₂).div_const 3
      have heq : c₂ * (↑(3:ℕ) * (1 - x) ^ (3 - 1) * (-1)) / 3 = -(c₂ * (1 - x) ^ 2) := by
        push_cast; ring
      rwa [heq] at h
    have e3 : HasDerivAt (fun x : ℝ => c₃ * (1 - x) ^ 4 / 4) (-(c₃ * (1 - x) ^ 3)) x := by
      have h := ((hb.pow 4).const_mul c₃).div_const 4
      have heq : c₃ * (↑(4:ℕ) * (1 - x) ^ (4 - 1) * (-1)) / 4 = -(c₃ * (1 - x) ^ 3) := by
        push_cast; ring
      rwa [heq] at h
    have e4 : HasDerivAt (fun x : ℝ => c₄ * (1 - x) ^ 5 / 5) (-(c₄ * (1 - x) ^ 4)) x := by
      have h := ((hb.pow 5).const_mul c₄).div_const 5
      have heq : c₄ * (↑(5:ℕ) * (1 - x) ^ (5 - 1) * (-1)) / 5 = -(c₄ * (1 - x) ^ 4) := by
        push_cast; ring
      rwa [heq] at h
    have h := ((((e0.sub e1).sub e2).sub e3).sub e4)
    have heq : c₀ - -(c₁ * (1 - x)) - -(c₂ * (1 - x) ^ 2) - -(c₃ * (1 - x) ^ 3)
        - -(c₄ * (1 - x) ^ 4)
        = c₀ + c₁ * (1 - x) + c₂ * (1 - x) ^ 2 + c₃ * (1 - x) ^ 3 + c₄ * (1 - x) ^ 4 := by ring
    rwa [heq] at h
  have hint : IntervalIntegrable
      (fun x => c₀ + c₁ * (1 - x) + c₂ * (1 - x) ^ 2 + c₃ * (1 - x) ^ 3 + c₄ * (1 - x) ^ 4)
      volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp; ring

/-! ## Inner (slice) integrals -/

/-- The `J₁`/`I₂` inner slice of `Fw`: `∫₀^{1−t₂} Fw dt₁ = (1−t₂) + (9/14)(1−t₂)²`. -/
private theorem inner_J1 (t₂ : ℝ) :
    (∫ t₁ in (0:ℝ)..(1 - t₂), Fw t₁ t₂) = (1 - t₂) + (9 / 14) * (1 - t₂) ^ 2 := by
  have hc : (∫ t₁ in (0:ℝ)..(1 - t₂), Fw t₁ t₂)
      = ∫ t₁ in (0:ℝ)..(1 - t₂),
          (1 + (9 / 7) * (1 - t₂)) + (-(9 / 7)) * t₁ + 0 * t₁ ^ 2 + 0 * t₁ ^ 3 + 0 * t₁ ^ 4 := by
    apply intervalIntegral.integral_congr
    intro t₁ _; unfold Fw; ring
  rw [hc, integral_quartic]; ring

/-- The `I₂` inner slice of `Fw²`: `∫₀^{1−t₂} Fw² dt₁
= (1−t₂) + (9/7)(1−t₂)² + (27/49)(1−t₂)³`. -/
private theorem inner_I2 (t₂ : ℝ) :
    (∫ t₁ in (0:ℝ)..(1 - t₂), (Fw t₁ t₂) ^ 2)
      = (1 - t₂) + (9 / 7) * (1 - t₂) ^ 2 + (27 / 49) * (1 - t₂) ^ 3 := by
  have hc : (∫ t₁ in (0:ℝ)..(1 - t₂), (Fw t₁ t₂) ^ 2)
      = ∫ t₁ in (0:ℝ)..(1 - t₂),
          (1 + (9 / 7) * (1 - t₂)) ^ 2 + (-(18 / 7) * (1 + (9 / 7) * (1 - t₂))) * t₁
            + (81 / 49) * t₁ ^ 2 + 0 * t₁ ^ 3 + 0 * t₁ ^ 4 := by
    apply intervalIntegral.integral_congr
    intro t₁ _; unfold Fw; ring
  rw [hc, integral_quartic]; ring

/-- The `J₂` inner slice of `Fw` (mirror; `Fw` is symmetric in `t₁, t₂`):
`∫₀^{1−t₁} Fw dt₂ = (1−t₁) + (9/14)(1−t₁)²`. -/
private theorem inner_J2 (t₁ : ℝ) :
    (∫ t₂ in (0:ℝ)..(1 - t₁), Fw t₁ t₂) = (1 - t₁) + (9 / 14) * (1 - t₁) ^ 2 := by
  have hc : (∫ t₂ in (0:ℝ)..(1 - t₁), Fw t₁ t₂)
      = ∫ t₂ in (0:ℝ)..(1 - t₁),
          (1 + (9 / 7) * (1 - t₁)) + (-(9 / 7)) * t₂ + 0 * t₂ ^ 2 + 0 * t₂ ^ 3 + 0 * t₂ ^ 4 := by
    apply intervalIntegral.integral_congr
    intro t₂ _; unfold Fw; ring
  rw [hc, integral_quartic]; ring

/-! ## The three frozen carrier values -/

/-- **`I₂ Fw = 209/196`** — the `L²`-mass of the witness. -/
theorem I₂_Fw : I₂ Fw = 209 / 196 := by
  unfold I₂
  have hc : (∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), (Fw t₁ t₂) ^ 2)
      = ∫ t₂ in (0:ℝ)..1,
          (0:ℝ) + 1 * (1 - t₂) + (9 / 7) * (1 - t₂) ^ 2 + (27 / 49) * (1 - t₂) ^ 3
            + 0 * (1 - t₂) ^ 4 := by
    apply intervalIntegral.integral_congr
    intro t₂ _; dsimp only; rw [inner_I2 t₂]; ring
  rw [hc, integral_one_sub_quartic]; norm_num

/-- **`J₁ Fw = 542/735`** — the first Selberg peel of the witness. -/
theorem J₁_Fw : J₁ Fw = 542 / 735 := by
  unfold J₁
  have hc : (∫ t₂ in (0:ℝ)..1, (∫ t₁ in (0:ℝ)..(1 - t₂), Fw t₁ t₂) ^ 2)
      = ∫ t₂ in (0:ℝ)..1,
          (0:ℝ) + 0 * (1 - t₂) + 1 * (1 - t₂) ^ 2 + (9 / 7) * (1 - t₂) ^ 3
            + (81 / 196) * (1 - t₂) ^ 4 := by
    apply intervalIntegral.integral_congr
    intro t₂ _; dsimp only; rw [inner_J1 t₂]; ring
  rw [hc, integral_one_sub_quartic]; norm_num

/-- **`J₂ Fw = 542/735`** — the symmetric Selberg peel (equal to `J₁ Fw` since `Fw`
depends only on `t₁ + t₂`). -/
theorem J₂_Fw : J₂ Fw = 542 / 735 := by
  unfold J₂
  have hc : (∫ t₁ in (0:ℝ)..1, (∫ t₂ in (0:ℝ)..(1 - t₁), Fw t₁ t₂) ^ 2)
      = ∫ t₁ in (0:ℝ)..1,
          (0:ℝ) + 0 * (1 - t₁) + 1 * (1 - t₁) ^ 2 + (9 / 7) * (1 - t₁) ^ 3
            + (81 / 196) * (1 - t₁) ^ 4 := by
    apply intervalIntegral.integral_congr
    intro t₁ _; dsimp only; rw [inner_J2 t₁]; ring
  rw [hc, integral_one_sub_quartic]; norm_num

/-! ## Continuity and the headliners -/

/-- `Fw` is continuous on the simplex (it is a polynomial). -/
theorem Fw_continuousOn : ContinuousOn (Function.uncurry Fw) R₂ := by
  have h : Function.uncurry Fw = fun p : ℝ × ℝ => 1 + (9 / 7) * (1 - p.1 - p.2) := by
    funext p; rfl
  rw [h]; fun_prop

/-- **The possibility headliner (the squeeze's lower jaw).** There is a continuous
weight `F` on the simplex with positive `L²`-mass whose Selberg pair `J₁ + J₂`
exceeds `1.383·I₂`: the witness `Fw` certifies `(J₁ + J₂)/I₂ ≥ 1383/1000`, so the
Maynard–Selberg functional for the twin tuple provably reaches ratio `≥ 1.383`. -/
theorem twin_witness :
    ∃ F : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry F) R₂ ∧
      0 < I₂ F ∧ (1383 / 1000 : ℝ) * I₂ F ≤ J₁ F + J₂ F := by
  refine ⟨Fw, Fw_continuousOn, ?_, ?_⟩
  · rw [I₂_Fw]; norm_num
  · rw [I₂_Fw, J₁_Fw, J₂_Fw]; norm_num

/-- **The two-sided squeeze**, pairing this rung's possibility witness with the
landed impossibility bound `twin_bar`. Interpreted numerically:
`1.383 ≤ M₂ ≤ 2·log 2 < 2` — the Maynard–Selberg method for the twin tuple `{0, 2}`
certifiably achieves ratio `≥ 1.383` (left conjunct, via `Fw`) and certifiably
cannot reach `2` (right conjunct, `twin_bar`, since `2·log 2 < 2`). The true
constant `M₂ = 1/(1 − W(1/e)) ≈ 1.38593` (Polymath8b Cor. 6.3) sits strictly
between the two jaws and is NOT formalized here — `Fw` is a deliberately simple
degree-1 polynomial chosen for a clean rational certificate. -/
theorem M₂_squeeze :
    (∃ F : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry F) R₂ ∧ 0 < I₂ F ∧
        (1383 / 1000 : ℝ) * I₂ F ≤ J₁ F + J₂ F)
      ∧ (∀ F : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry F) R₂ →
        J₁ F + J₂ F ≤ 2 * Real.log 2 * I₂ F) :=
  ⟨twin_witness, fun F hF => twin_bar F hF⟩

end Salt.TwinBar
