/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey
-/
import Mathlib
import Salt.MR.AbsCosFourier
import Salt.MR.A4FMidBridge
import Salt.MR.MRTPropA3

/-!
# A4F H4 — the Y-parametric mid-range theorem, BOTH floors carried

The wave's deliverable: with the `Y`-floor `log Y ≥ (log X)^{2/3}` AND the `u`-floor
`(log X)^{1/16}/2 ≤ |u|` (dropping either reintroduces a falsity of the refuted-Prop genre —
the statement is FALSE at `u = 0`, where every summand vanishes while the demand grows),
and `e ≤ Y` carried EXPLICITLY (mathlib's `Real.log` is even, so the floor alone yields only
`e ≤ |Y|` — the commissioning note that the floor supplies `e ≤ Y` "by construction" is
false in this convention; see the flags record),

`(1 − 2/π)·log(log X/log Y) − C ≤ Σ_{Y<p≤X} (1 − |cos(u·log p/2)|)/p`

for `|u| ≤ (log X)^{20}` — the mid range, closed UNCONDITIONALLY at the sharp constant.

Assembly: H1's exact-series majorization at cutoff `Mcut = max 1 ⌈loglog X⌉` converts the
sifted sum into a Mertens main term at weight `1 − 2/π` (the two-sided Mertens window below),
an exact tail `≤ 2/(π(2Mcut+1))` whose `P`-weighted total is `O(1)`, and `Mcut` harmonic
sums, each two-sidedly controlled by H3's regime lemmas — bounded-height below `T₀`
(absolute), VK-difference above (the margin `(1/log Y)·400·D/cR ≤ 1` holds because
`log Y ≥ e^{(2/3)·loglog X}` beats the polynomial `D ≤ (21·loglog X)^5`, via the crude
exp-beats-poly stone below).  The head weights sum to `Mcut/(2Mcut+1) < 1/2` exactly.

The top-level branch is on `Λ₀ ≤ loglog X` (`Λ₀` explicit in the VK constants): below it the
`X`-range is bounded, the demand is at most `(1−2/π)·Λ₀/3 ≤ Λ₀` (the `Y`-floor caps
`log X/log Y` at `(log X)^{1/3}`), the sifted sum is `≥ 0`, and everything absorbs into `C`;
this branch carries the whole `|u| < 2` regime (and with it the `|t| ∈ [1/2,2)` row of H3's
table), since `|u| ≥ e^{Λ₀/16}/2 > 2` once `loglog X ≥ Λ₀ ≥ 32`.
-/

namespace Salt.MR

open Complex (I)

/-! ## Support stones -/

/-- `(x/7)^7 ≤ exp x` for `x ≥ 0` — the crude exp-beats-poly stone the branch threshold
uses (seven factors of `add_one_le_exp`). -/
lemma div_seven_pow_seven_le_exp {x : ℝ} (hx : 0 ≤ x) : (x / 7) ^ (7 : ℕ) ≤ Real.exp x := by
  have h7 : (0 : ℝ) ≤ x / 7 := by positivity
  have hle : x / 7 ≤ Real.exp (x / 7) := by
    have := Real.add_one_le_exp (x / 7)
    linarith
  calc (x / 7) ^ (7 : ℕ) ≤ (Real.exp (x / 7)) ^ (7 : ℕ) := pow_le_pow_left₀ h7 hle 7
    _ = Real.exp x := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- **The Mertens window.**  `|Σ_{Y<p≤X} 1/p − log(log X/log Y)| ≤ 24` for `e ≤ Y ≤ X`:
the sharp real Mertens-2 at both endpoints through the index identity; each endpoint pays
`12/log ≤ 12`. -/
lemma prime_recip_window_bounds {X Y : ℝ} (heY : Real.exp 1 ≤ Y) (hYX : Y ≤ X) :
    |(∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ)),
        (1 : ℝ) / p) - Real.log (Real.log X / Real.log Y)| ≤ 24 := by
  have heX : Real.exp 1 ≤ X := le_trans heY hYX
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2Y : (2 : ℝ) ≤ Y := le_trans h2e heY
  have h2X : (2 : ℝ) ≤ X := le_trans h2Y hYX
  have hlogY1 : (1 : ℝ) ≤ Real.log Y := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) heY
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) heX
  rw [prime_sum_filter_gt_sub _ (by linarith) hYX]
  have hmX := abs_le.mp (Salt.Mertens.mertens_second_sharp_real (t := X) h2X)
  have hmY := abs_le.mp (Salt.Mertens.mertens_second_sharp_real (t := Y) h2Y)
  have hSX : (∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p)
      = Salt.Mertens.SPartial X := rfl
  have hSY : (∑ p ∈ (Finset.range (⌊Y⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p)
      = Salt.Mertens.SPartial Y := rfl
  rw [hSX, hSY, Real.log_div (by linarith) (by linarith)]
  have h12X : 12 / Real.log X ≤ 12 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h12Y : 12 / Real.log Y ≤ 12 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h12X0 : (0 : ℝ) ≤ 12 / Real.log X := by positivity
  have h12Y0 : (0 : ℝ) ≤ 12 / Real.log Y := by positivity
  rw [abs_le]
  constructor <;> linarith [hmX.1, hmX.2, hmY.1, hmY.2]

/-! ## The deliverable -/

set_option maxHeartbeats 2000000 in
-- one long assembly: three branches, a per-harmonic case split over the VK threshold, and
-- several large `linarith`/`nlinarith` closes over the Mertens/tail/harmonic atoms
/-- **H4 — the Y-parametric mid-range theorem, BOTH floors carried.**  With the `Y`-floor
`(log X)^{2/3} ≤ log Y` and the `u`-floor `(log X)^{1/16}/2 ≤ |u|` (and the range ceiling
`|u| ≤ (log X)^{20}`), `(1 − 2/π)·log(log X/log Y) − C ≤ Σ_{Y<p≤X} (1 − |cos(u·log p/2)|)/p`
with an absolute `C`.  Unconditional; the constant `1 − 2/π` is sharp (the exact series
loses nothing at the head).  Route in the module doc. -/
theorem mrt_mid_range_parametric :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Y u : ℝ), Real.exp 1 ≤ X → Real.exp 1 ≤ Y →
      (Real.log X) ^ ((2 : ℝ) / 3) ≤ Real.log Y →
      (Real.log X) ^ ((1 : ℝ) / 16) / 2 ≤ |u| →
      |u| ≤ (Real.log X) ^ (20 : ℕ) →
        (1 - 2 / Real.pi) * Real.log (Real.log X / Real.log Y) - C
          ≤ ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter
                (fun p : ℕ => Y < (p : ℝ)),
              (1 - |Real.cos (u * Real.log p / 2)|) / (p : ℝ) := by
  obtain ⟨K₂, cR, T₀, hK₂0, hcR0, hcR1, hT₀3, hVK⟩ := harmonic_prime_sum_abs_le_vk
  obtain ⟨B₀, hB₀0, hBH⟩ := harmonic_prime_sum_abs_le_bounded_height (T := T₀) (by linarith)
  set B₁ : ℝ := max B₀ (K₂ + 1) with hB₁
  have hB₁0 : 0 ≤ B₁ := le_trans hB₀0 (le_max_left _ _)
  set Q : ℝ := 400 * 21 ^ (12 : ℕ) / (2 ^ (7 : ℕ) * cR) with hQ
  have hQ0 : 0 < Q := by positivity
  set Λ₀ : ℝ := 32 + Q with hΛ₀
  have hΛ₀32 : (32 : ℝ) ≤ Λ₀ := by rw [hΛ₀]; linarith
  refine ⟨30 + B₁ + Λ₀, by positivity, ?_⟩
  intro X Y u heX heY hYfl hufl huceil
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπpos : 0 < Real.pi := by linarith
  have h2π : 2 / Real.pi < 1 := by rw [div_lt_one hπpos]; linarith
  have h2π0 : 0 < 2 / Real.pi := by positivity
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) heX
  have hlogXpos : 0 < Real.log X := by linarith
  set lam : ℝ := Real.log (Real.log X) with hlam
  have hlam0 : 0 ≤ lam := Real.log_nonneg hlogX1
  -- `1 ≤ log Y` (from `e ≤ Y`; note the floor alone gives only `e ≤ |Y|`, mathlib's `log`
  -- being even — which is why `e ≤ Y` is a separate hypothesis)
  have hlogY1 : (1 : ℝ) ≤ Real.log Y := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) heY
  have hlogYpos : 0 < Real.log Y := by linarith
  -- the demand is capped by `lam/3` (the Y-floor)
  set Δ : ℝ := Real.log (Real.log X / Real.log Y) with hΔ
  have hΔle : Δ ≤ lam / 3 := by
    have hdiv : Real.log X / Real.log Y ≤ (Real.log X) ^ ((1 : ℝ) / 3) := by
      rw [div_le_iff₀ hlogYpos]
      calc Real.log X = (Real.log X) ^ ((1 : ℝ) / 3) * (Real.log X) ^ ((2 : ℝ) / 3) := by
            rw [← Real.rpow_add hlogXpos]; norm_num
        _ ≤ (Real.log X) ^ ((1 : ℝ) / 3) * Real.log Y :=
            mul_le_mul_of_nonneg_left hYfl (by positivity)
    have hpos : 0 < Real.log X / Real.log Y := by positivity
    calc Δ ≤ Real.log ((Real.log X) ^ ((1 : ℝ) / 3)) := Real.log_le_log hpos hdiv
      _ = lam / 3 := by rw [Real.log_rpow hlogXpos, hlam]; ring
  -- the target sum is nonnegative
  have hT0 : 0 ≤ ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter
      (fun p : ℕ => Y < (p : ℝ)), (1 - |Real.cos (u * Real.log p / 2)|) / (p : ℝ) := by
    refine Finset.sum_nonneg fun p _ => ?_
    have := Real.abs_cos_le_one (u * Real.log p / 2)
    exact div_nonneg (by linarith) (Nat.cast_nonneg p)
  have h12 : 0 ≤ 1 - 2 / Real.pi := by linarith
  have h12' : 1 - 2 / Real.pi ≤ 1 := by linarith
  -- ## the small branch: bounded `X`, absorb
  rcases lt_or_ge lam Λ₀ with hsmall | hbig
  · have hΔΛ : Δ ≤ Λ₀ := by linarith [hΔle, hsmall, hlam0]
    have h1 : (1 - 2 / Real.pi) * Δ ≤ Λ₀ := by
      rcases le_or_gt Δ 0 with hΔ0 | hΔ0
      · nlinarith
      · nlinarith
    linarith [hT0, hB₁0]
  -- ## the `Y > X` branch: empty window, nonpositive demand
  rcases lt_or_ge X Y with hXY | hYX
  · have hΔ0 : Δ ≤ 0 := by
      have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) heX
      have hlogle : Real.log X ≤ Real.log Y := Real.log_le_log hXpos hXY.le
      have hratio : Real.log X / Real.log Y ≤ 1 := by rw [div_le_one hlogYpos]; exact hlogle
      exact Real.log_nonpos (by positivity) hratio
    have : (1 - 2 / Real.pi) * Δ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h12 hΔ0
    linarith [hT0, hB₁0, hΛ₀32]
  -- ## the large branch, `Y ≤ X`
  have hlam32 : (32 : ℝ) ≤ lam := le_trans hΛ₀32 hbig
  have hlam1 : (1 : ℝ) ≤ lam := by linarith
  have hlamQ : Q ≤ lam := by linarith [hbig, hΛ₀]
  -- `|u| ≥ 2`
  have hu2 : (2 : ℝ) ≤ |u| := by
    have hexp : Real.exp 2 ≤ (Real.log X) ^ ((1 : ℝ) / 16) := by
      rw [Real.rpow_def_of_pos hlogXpos]
      apply Real.exp_le_exp.mpr
      rw [← hlam]; linarith
    have he2 : (4 : ℝ) < Real.exp 2 := by
      have h1 := Real.exp_one_gt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith
    linarith [hufl, hexp, he2]
  -- the cutoff
  set Mcut : ℕ := max 1 ⌈lam⌉₊ with hMcut
  have hMcut1 : 1 ≤ Mcut := le_max_left _ _
  have hMcutR1 : (1 : ℝ) ≤ (Mcut : ℝ) := by exact_mod_cast hMcut1
  have hMcutge : lam ≤ (Mcut : ℝ) := by
    have h1 : lam ≤ (⌈lam⌉₊ : ℝ) := Nat.le_ceil lam
    have h2 : (⌈lam⌉₊ : ℝ) ≤ (Mcut : ℝ) := by exact_mod_cast le_max_right 1 ⌈lam⌉₊
    linarith
  have hMcutle : (Mcut : ℝ) ≤ lam + 1 := by
    have h1 : (⌈lam⌉₊ : ℝ) < lam + 1 := Nat.ceil_lt_add_one hlam0
    have hcast : (Mcut : ℝ) = max (1 : ℝ) (⌈lam⌉₊ : ℝ) := by rw [hMcut]; push_cast; rfl
    rw [hcast]; exact max_le (by linarith) h1.le
  -- Mertens window
  have hP := prime_recip_window_bounds heY hYX
  -- H1 at each prime, with the harmonic argument aligned to `(m·u)·log p`
  have hH1 : ∀ p : ℕ, |Real.cos (u * Real.log p / 2)|
      ≤ 2 / Real.pi + 4 / Real.pi * ∑ m ∈ Finset.Icc 1 Mcut,
          ((-1 : ℝ) ^ (m + 1) / (4 * (m : ℝ) ^ 2 - 1)) * Real.cos (((m : ℝ) * u) * Real.log p)
        + 2 / (Real.pi * (2 * (Mcut : ℝ) + 1)) := by
    intro p
    have h := (abs_le.mp (abs_cos_partial_fourier_bound (u * Real.log p / 2) Mcut)).2
    have hcongr : ∀ m : ℕ,
        (-1 : ℝ) ^ (m + 1) * Real.cos (2 * (m : ℝ) * (u * Real.log p / 2))
            / (4 * (m : ℝ) ^ 2 - 1)
          = ((-1 : ℝ) ^ (m + 1) / (4 * (m : ℝ) ^ 2 - 1))
              * Real.cos (((m : ℝ) * u) * Real.log p) := by
      intro m
      rw [show 2 * (m : ℝ) * (u * Real.log p / 2) = ((m : ℝ) * u) * Real.log p by ring]
      ring
    simp only [hcongr] at h
    linarith
  -- the per-harmonic bound
  have hSm : ∀ m ∈ Finset.Icc 1 Mcut,
      |∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ)),
          Real.cos (((m : ℝ) * u) * Real.log p) / (p : ℝ)| ≤ B₁ := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmM : m ≤ Mcut := (Finset.mem_Icc.mp hm).2
    have hmR1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have habs_mu : |(m : ℝ) * u| = (m : ℝ) * |u| := by
      rw [abs_mul, abs_of_pos (by linarith)]
    have h2mu : (2 : ℝ) ≤ |(m : ℝ) * u| := by rw [habs_mu]; nlinarith [hu2]
    rcases le_or_gt |(m : ℝ) * u| T₀ with hle | hgt
    · exact le_trans (hBH X Y ((m : ℝ) * u) heY hYX h2mu hle) (le_max_left _ _)
    · have ht3 : (3 : ℝ) ≤ |(m : ℝ) * u| := le_trans hT₀3 hgt.le
      have hexp1lt3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
      have hlogt1 : (1 : ℝ) < Real.log |(m : ℝ) * u| := by
        calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hexp1lt3
          _ ≤ Real.log |(m : ℝ) * u| := Real.log_le_log (by norm_num) ht3
      have htle : |(m : ℝ) * u| ≤ (Mcut : ℝ) * (Real.log X) ^ (20 : ℕ) := by
        rw [habs_mu]
        exact mul_le_mul (by exact_mod_cast hmM) huceil (abs_nonneg u) (Nat.cast_nonneg _)
      have hMcutpos : (0 : ℝ) < (Mcut : ℝ) := by linarith
      have hlogt : Real.log |(m : ℝ) * u| ≤ 21 * lam := by
        calc Real.log |(m : ℝ) * u| ≤ Real.log ((Mcut : ℝ) * (Real.log X) ^ (20 : ℕ)) :=
              Real.log_le_log (by positivity) htle
          _ = Real.log (Mcut : ℝ) + 20 * lam := by
              rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hlam]
              push_cast; ring
          _ ≤ lam + 20 * lam := by
              have := Real.log_le_sub_one_of_pos hMcutpos
              linarith [hMcutle]
          _ = 21 * lam := by ring
      have hlogtpos : 0 < Real.log |(m : ℝ) * u| := by linarith
      have hloglogt : Real.log (Real.log |(m : ℝ) * u|) ≤ 21 * lam := by
        calc Real.log (Real.log |(m : ℝ) * u|) ≤ Real.log (21 * lam) :=
              Real.log_le_log hlogtpos hlogt
          _ ≤ 21 * lam - 1 := Real.log_le_sub_one_of_pos (by positivity)
          _ ≤ 21 * lam := by linarith
      have hloglogt0 : 0 < Real.log (Real.log |(m : ℝ) * u|) := Real.log_pos hlogt1
      set D : ℝ := (Real.log |(m : ℝ) * u|) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log |(m : ℝ) * u|)) ^ (4 : ℕ) with hD
      have hDpos : 0 < D := by
        rw [hD]
        have : (0 : ℝ) < (Real.log |(m : ℝ) * u|) ^ ((3 : ℝ) / 4) :=
          Real.rpow_pos_of_pos hlogtpos _
        positivity
      have hDle : D ≤ (21 * lam) ^ (5 : ℕ) := by
        have h34 : (Real.log |(m : ℝ) * u|) ^ ((3 : ℝ) / 4) ≤ 21 * lam := by
          calc (Real.log |(m : ℝ) * u|) ^ ((3 : ℝ) / 4)
              ≤ (Real.log |(m : ℝ) * u|) ^ ((1 : ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le hlogt1.le (by norm_num)
            _ = Real.log |(m : ℝ) * u| := Real.rpow_one _
            _ ≤ 21 * lam := hlogt
        have h4 : (Real.log (Real.log |(m : ℝ) * u|)) ^ (4 : ℕ) ≤ (21 * lam) ^ (4 : ℕ) :=
          pow_le_pow_left₀ hloglogt0.le hloglogt 4
        rw [hD]
        calc (Real.log |(m : ℝ) * u|) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log |(m : ℝ) * u|)) ^ (4 : ℕ)
            ≤ (21 * lam) * (21 * lam) ^ (4 : ℕ) :=
              mul_le_mul h34 h4 (by positivity) (by positivity)
          _ = (21 * lam) ^ (5 : ℕ) := by ring
      -- `400·(21·lam)^5/cR ≤ exp((2/3)·lam) ≤ (log X)^{2/3} ≤ log Y`
      have hexpge : 400 * (21 * lam) ^ (5 : ℕ) / cR ≤ Real.exp (2 / 3 * lam) := by
        have h7 := div_seven_pow_seven_le_exp (x := 2 / 3 * lam) (by positivity)
        have hlamsq : Q ≤ lam ^ 2 := by nlinarith [hlamQ, hlam1]
        have hkey : 400 * (21 * lam) ^ (5 : ℕ) / cR ≤ (2 / 3 * lam / 7) ^ (7 : ℕ) := by
          rw [div_le_iff₀ hcR0]
          have hQeq : (2 / 21 : ℝ) ^ (7 : ℕ) * cR * Q = 400 * 21 ^ (5 : ℕ) := by
            rw [hQ]; field_simp
          have hlam5 : 0 ≤ lam ^ (5 : ℕ) := by positivity
          have hcoef : (0 : ℝ) ≤ (2 / 21 : ℝ) ^ (7 : ℕ) * cR := by positivity
          calc 400 * (21 * lam) ^ (5 : ℕ) = 400 * 21 ^ (5 : ℕ) * lam ^ (5 : ℕ) := by ring
            _ = (2 / 21 : ℝ) ^ (7 : ℕ) * cR * Q * lam ^ (5 : ℕ) := by rw [hQeq]
            _ ≤ (2 / 21 : ℝ) ^ (7 : ℕ) * cR * lam ^ 2 * lam ^ (5 : ℕ) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlamsq hcoef) hlam5
            _ = (2 / 3 * lam / 7) ^ (7 : ℕ) * cR := by ring
        exact le_trans hkey h7
      have hlogY_ge : Real.exp (2 / 3 * lam) ≤ Real.log Y := by
        have : (Real.log X) ^ ((2 : ℝ) / 3) = Real.exp (2 / 3 * lam) := by
          rw [Real.rpow_def_of_pos hlogXpos, hlam]; ring_nf
        rw [← this]; exact hYfl
      have hDcR : 400 * D / cR ≤ Real.log Y := by
        calc 400 * D / cR ≤ 400 * (21 * lam) ^ (5 : ℕ) / cR := by
              rw [div_le_div_iff_of_pos_right hcR0]
              exact mul_le_mul_of_nonneg_left hDle (by norm_num)
          _ ≤ Real.exp (2 / 3 * lam) := hexpge
          _ ≤ Real.log Y := hlogY_ge
      have hmargin : 1 / Real.log Y * (400 * D / cR) ≤ 1 := by
        have : 1 / Real.log Y * (400 * D / cR) = (400 * D / cR) / Real.log Y := by ring
        rw [this, div_le_one hlogYpos]; exact hDcR
      have hwin : 1 / Real.log Y ≤ cR / D := by
        rw [div_le_div_iff₀ hlogYpos hDpos]
        have h := hDcR
        rw [div_le_iff₀ hcR0] at h
        nlinarith [hDpos, hcR0, hlogYpos]
      have hvk := hVK X Y ((m : ℝ) * u) heY hYX hgt.le hwin
      calc _ ≤ K₂ + 1 / Real.log Y * (400 * D / cR) := hvk
        _ ≤ K₂ + 1 := by linarith
        _ ≤ B₁ := le_max_right _ _
  -- ## assemble
  set W := ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ))
    with hW
  set P : ℝ := ∑ p ∈ W, (1 : ℝ) / p with hPdef
  set tail : ℝ := 2 / (Real.pi * (2 * (Mcut : ℝ) + 1)) with htail
  have htail0 : 0 ≤ tail := by positivity
  -- the harmonic sums and their weighted total
  set S : ℕ → ℝ := fun m => ∑ p ∈ W, Real.cos (((m : ℝ) * u) * Real.log p) / (p : ℝ) with hS
  have hHabs : |∑ m ∈ Finset.Icc 1 Mcut, ((-1 : ℝ) ^ (m + 1) / (4 * (m : ℝ) ^ 2 - 1)) * S m|
      ≤ B₁ * (1 / 2) := by
    calc |∑ m ∈ Finset.Icc 1 Mcut, ((-1 : ℝ) ^ (m + 1) / (4 * (m : ℝ) ^ 2 - 1)) * S m|
        ≤ ∑ m ∈ Finset.Icc 1 Mcut, |((-1 : ℝ) ^ (m + 1) / (4 * (m : ℝ) ^ 2 - 1)) * S m| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 Mcut, (1 : ℝ) / (4 * (m : ℝ) ^ 2 - 1) * B₁ := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hmR1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
          have hden : (0 : ℝ) < 4 * (m : ℝ) ^ 2 - 1 := by nlinarith
          rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hden]
          exact mul_le_mul_of_nonneg_left (hSm m hm) (by positivity)
      _ = (∑ m ∈ Finset.Icc 1 Mcut, (1 : ℝ) / (4 * (m : ℝ) ^ 2 - 1)) * B₁ := by
          rw [Finset.sum_mul]
      _ = (Mcut : ℝ) / (2 * (Mcut : ℝ) + 1) * B₁ := by rw [absCos_weight_partial_sum]
      _ ≤ B₁ * (1 / 2) := by
          have : (Mcut : ℝ) / (2 * (Mcut : ℝ) + 1) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
          nlinarith [hB₁0]
  -- the sifted sum split and the H1 majorization summed over primes
  have hTsplit : ∑ p ∈ W, (1 - |Real.cos (u * Real.log p / 2)|) / (p : ℝ)
      = P - ∑ p ∈ W, |Real.cos (u * Real.log p / 2)| / (p : ℝ) := by
    rw [hPdef, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have hcos_sum : ∑ p ∈ W, |Real.cos (u * Real.log p / 2)| / (p : ℝ)
      ≤ (2 / Real.pi + tail) * P
        + 4 / Real.pi * ∑ m ∈ Finset.Icc 1 Mcut,
            ((-1 : ℝ) ^ (m + 1) / (4 * (m : ℝ) ^ 2 - 1)) * S m := by
    -- per prime: divide H1 by `p` and distribute
    have hper : ∀ p : ℕ, |Real.cos (u * Real.log p / 2)| / (p : ℝ)
        ≤ (2 / Real.pi + tail) * ((1 : ℝ) / p)
            + 4 / Real.pi * ∑ m ∈ Finset.Icc 1 Mcut,
              ((-1 : ℝ) ^ (m + 1) / (4 * (m : ℝ) ^ 2 - 1))
                * (Real.cos (((m : ℝ) * u) * Real.log p) / (p : ℝ)) := by
      intro p
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      have hdivle : |Real.cos (u * Real.log p / 2)| / (p : ℝ)
          ≤ (2 / Real.pi + 4 / Real.pi * ∑ m ∈ Finset.Icc 1 Mcut,
              ((-1 : ℝ) ^ (m + 1) / (4 * (m : ℝ) ^ 2 - 1))
                * Real.cos (((m : ℝ) * u) * Real.log p) + tail) / (p : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (hH1 p) (inv_nonneg.mpr hp0)
      have hAp : (2 / Real.pi + 4 / Real.pi * ∑ m ∈ Finset.Icc 1 Mcut,
              ((-1 : ℝ) ^ (m + 1) / (4 * (m : ℝ) ^ 2 - 1))
                * Real.cos (((m : ℝ) * u) * Real.log p) + tail) / (p : ℝ)
          = (2 / Real.pi + tail) * ((1 : ℝ) / p)
            + 4 / Real.pi * ∑ m ∈ Finset.Icc 1 Mcut,
              ((-1 : ℝ) ^ (m + 1) / (4 * (m : ℝ) ^ 2 - 1))
                * (Real.cos (((m : ℝ) * u) * Real.log p) / (p : ℝ)) := by
        rw [add_div, add_div, mul_div_assoc (4 / Real.pi), Finset.sum_div]
        simp only [mul_div_assoc]
        ring
      rw [hAp] at hdivle
      exact hdivle
    have hsum_eq : ∑ p ∈ W, ((2 / Real.pi + tail) * ((1 : ℝ) / p)
            + 4 / Real.pi * ∑ m ∈ Finset.Icc 1 Mcut,
              ((-1 : ℝ) ^ (m + 1) / (4 * (m : ℝ) ^ 2 - 1))
                * (Real.cos (((m : ℝ) * u) * Real.log p) / (p : ℝ)))
        = (2 / Real.pi + tail) * P
          + 4 / Real.pi * ∑ m ∈ Finset.Icc 1 Mcut,
              ((-1 : ℝ) ^ (m + 1) / (4 * (m : ℝ) ^ 2 - 1)) * S m := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
      simp only [hS, hPdef]
      congr 1
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
    exact le_trans (Finset.sum_le_sum fun p _ => hper p) (le_of_eq hsum_eq)
  -- the tail's weighted total is absolute
  have hPΔ := abs_le.mp hP
  have hPle : P ≤ lam + 24 := by linarith [hPΔ.2, hΔle]
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun p _ => by positivity
  have htailP : tail * P ≤ 6 := by
    have h1 : tail * P ≤ tail * (lam + 24) := mul_le_mul_of_nonneg_left hPle htail0
    have h2 : tail * (lam + 24) ≤ 6 := by
      rw [htail, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hπ3, hMcutge, hlam1]
    linarith
  -- close
  have hHle := (abs_le.mp hHabs).2
  have hH4 : 4 / Real.pi * ∑ m ∈ Finset.Icc 1 Mcut,
      ((-1 : ℝ) ^ (m + 1) / (4 * (m : ℝ) ^ 2 - 1)) * S m ≤ B₁ := by
    have h4π : 4 / Real.pi ≤ 2 := by rw [div_le_iff₀ hπpos]; linarith
    have h4π0 : 0 ≤ 4 / Real.pi := by positivity
    nlinarith [hHle, h4π, h4π0, hB₁0]
  have hmain : (1 - 2 / Real.pi) * P ≥ (1 - 2 / Real.pi) * (Δ - 24) :=
    mul_le_mul_of_nonneg_left (by linarith [hPΔ.1]) h12
  rw [hTsplit]
  nlinarith [hcos_sum, htailP, hH4, hmain, h12, h12', hB₁0, hΛ₀32]

/-! ## The dischargers: the pinned Props are instances of the floor -/

/-- **`MRTShortSegmentSplitting` is DISCHARGED** — its pin `Y = exp((log X)^{2/3+ε})`
satisfies the floor `(log X)^{2/3} ≤ log Y` for every `ε > 0`. -/
theorem mrtShortSegmentSplitting_holds : MRTShortSegmentSplitting := by
  obtain ⟨C, hC0, hmain⟩ := mrt_mid_range_parametric
  refine ⟨C, hC0, ?_⟩
  intro X Y u ε hε heX hY hlo hhi
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) heX
  have hfloor : (Real.log X) ^ ((2 : ℝ) / 3) ≤ Real.log Y := by
    rw [hY, Real.log_exp]
    exact Real.rpow_le_rpow_of_exponent_le hlogX1 (by linarith)
  have heY : Real.exp 1 ≤ Y := by
    rw [hY]; exact Real.exp_le_exp.mpr (Real.one_le_rpow hlogX1 (by linarith))
  exact hmain X Y u heX heY hfloor hlo hhi

/-- **The θ = 3/4 instance** — the mid-range estimate at `Y = exp((log X)^{3/4+ε})`, the
`Y` the θ = 3/4 far-arm assembly feeds to the landed composer. -/
theorem mrt_mid_range_34 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X u ε : ℝ), 0 < ε → Real.exp 1 ≤ X →
      (Real.log X) ^ ((1 : ℝ) / 16) / 2 ≤ |u| → |u| ≤ (Real.log X) ^ (20 : ℕ) →
        (1 - 2 / Real.pi)
            * Real.log (Real.log X / Real.log (Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε))))
          - C
          ≤ ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter
                (fun p : ℕ => Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε)) < (p : ℝ)),
              (1 - |Real.cos (u * Real.log p / 2)|) / (p : ℝ) := by
  obtain ⟨C, hC0, hmain⟩ := mrt_mid_range_parametric
  refine ⟨C, hC0, ?_⟩
  intro X u ε hε heX hlo hhi
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) heX
  have hfloor : (Real.log X) ^ ((2 : ℝ) / 3)
      ≤ Real.log (Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε))) := by
    rw [Real.log_exp]
    exact Real.rpow_le_rpow_of_exponent_le hlogX1 (by linarith)
  have heY : Real.exp 1 ≤ Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε)) :=
    Real.exp_le_exp.mpr (Real.one_le_rpow hlogX1 (by linarith))
  exact hmain X _ u heX heY hfloor hlo hhi

/-! ## The far-arm wiring through the landed Y-parametric composer -/

/-- **The θ = 2/3 far arm, UNCONDITIONAL** — `mrtA4ii_far_of_named_splitting` with its named
hypothesis discharged. -/
theorem mrtA4ii_far_mid_unconditional
    (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t t₁ ε : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hε : 0 < ε) (hXe : Real.exp 1 ≤ X)
    (hlo : (Real.log X) ^ ((1 : ℝ) / 16) / 2 ≤ |t - t₁|)
    (hhi : |t - t₁| ≤ (Real.log X) ^ (20 : ℕ))
    (hmin : pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist t) X) :
    ∃ C : ℝ, 0 ≤ C ∧
      (1 / 2) * ((1 - 2 / Real.pi)
          * Real.log (Real.log X
              / Real.log (Real.exp ((Real.log X) ^ ((2 : ℝ) / 3 + ε)))) - C)
        ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X :=
  mrtA4ii_far_of_named_splitting mrtShortSegmentSplitting_holds f Pseq Qseq 𝒥 X t t₁ ε
    hf hε hXe hlo hhi hmin

/-- **The θ = 3/4 far arm, UNCONDITIONAL** — the 3/4 instance through the landed
`Y`-parametric composer `mrtA4ii_far_of_either_estimate`. -/
theorem mrtA4ii_far_mid34_unconditional
    (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t t₁ ε : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hε : 0 < ε) (hXe : Real.exp 1 ≤ X)
    (hlo : (Real.log X) ^ ((1 : ℝ) / 16) / 2 ≤ |t - t₁|)
    (hhi : |t - t₁| ≤ (Real.log X) ^ (20 : ℕ))
    (hmin : pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist t) X) :
    ∃ C : ℝ, 0 ≤ C ∧
      (1 / 2) * ((1 - 2 / Real.pi)
          * Real.log (Real.log X
              / Real.log (Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε)))) - C)
        ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X := by
  obtain ⟨C, hC0, h34⟩ := mrt_mid_range_34
  refine ⟨C, hC0, ?_⟩
  have hs := h34 X (t - t₁) ε hε hXe hlo hhi
  exact mrtA4ii_far_of_either_estimate f Pseq Qseq 𝒥 X
    (Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε))) t t₁ C hf hmin hs

end Salt.MR
