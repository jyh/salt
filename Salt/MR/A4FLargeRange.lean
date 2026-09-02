/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey
-/
import Mathlib
import Salt.MR.A4FThreshold

/-!
# A4F AU — the large-range reduction (D★): A.4(ii) whole at θ = 3/4, in the source's order

The frozen large-range Prop `MRTLargeRangeEquidistributionFixed` (MRTPropA3.lean) claims a
constant `C` UNIFORM down to the bare floor `(log X)^{2/3} ≤ log Y`.  Its ONE consumer,
`mrtLemmaA4iiFixed34T_of_largeRangeFixed` (A4FThreshold.lean), reads it only at
`Y = exp((log X)^{3/4+ε'})` — and at that `Y` the landed mid-range mechanism carries with no
height cap at all: `harmonic_prime_sum_abs_le_vk` and its supplier `zeta_near_logDeriv_bound`
bound every harmonic `|m·u|` above the VK threshold `T₀`, whatever its size, under the window
hypothesis `1/log Y ≤ cR/D(t)`, `D(t) = (log|t|)^{3/4}(loglog|t|)^4`.  The large range changes
ONE number: the harmonic height is `|m·u| ≤ 2·Mcut·X` (so `log|m·u| ≤ 2·log X`) instead of
`Mcut·(log X)^{20}`; the window hypothesis then reads `400·D/cR ≤ log Y` with
`D ≤ 32·(log X)^{3/4}·(loglog X)^4`, met by the floor `(log X)^{3/4}·(loglog X)^5 ≤ log Y`
once `loglog X ≥ 12800/cR`.

**What lands here (the freeze `2026-09-02-math-AU-Dstar-FREEZE.md`, refuter-passed):**

* `mrt_large_range_parametric` — the port of `mrt_mid_range_parametric` (A4FMidRange.lean)
  regime by regime: the height ceiling `|u| ≤ (log X)^{20}` becomes the range
  `(log X)^{20} < |u| ≤ 2X`; the floor becomes `(log X)^{3/4}·(loglog X)^5 ≤ log Y`; the
  bounded-height regime is EMPTY (every harmonic sits above `T₀` once `loglog X ≥ log T₀`),
  so the `|u| ≥ 2` detour and `harmonic_prime_sum_abs_le_bounded_height` are not needed;
  ONE new stone — rpow monotonicity at exponent `3/4` against a floor at the SAME exponent
  (the mid range's crude `(log t)^{3/4} ≤ (log t)^1` would lose the `(log X)^{1/4}` this
  floor cannot pay).  Uniform `C`; `e ≤ Y` carried (mathlib's `log` is even; and the floor
  vanishes at `X = e`, admitting `Y → 1⁺` where the demand is unbounded — the statement
  WITHOUT `e ≤ Y` is refutable at `X = e, Y = e^δ, u = 2`).
* `MRTLargeRangeEquidistributionFixedEps` (D1) — the large-range Prop in the SOURCE'S
  quantifier order `∀ε ∃C`, floor `(log X)^{3/4+ε}`, `e ≤ Y` carried; produced by
  `mrtLargeRangeEquidistributionFixedEps_holds` from the theorem above through the
  `(x/7)^7 ≤ e^x` stone (threshold `(loglog X)^2 ≥ (7/ε)^7`, `pow` arithmetic only).
* `MRTLemmaA4iiFixed34E` (D2) — `MRTLemmaA4iiFixed34T` with `∀ε` BEFORE `∃C₀`; produced
  UNCONDITIONALLY by `mrtLemmaA4iiFixed34E_holds` — **A.4(ii) whole at θ = 3/4**, high-M +
  mid + large arms all closed, in the source's own order ("for any ε > 0", arXiv:1503.05121
  p.22, the `O(1)` absorbed for `X` large in `ε`).
* The pins `largeRangeFixedEps_of_fixed` and `lemmaA4iiFixed34E_of_fixed34T`: the frozen
  strong forms IMPLY the new ones (never the reverse), so nothing downstream of D1/D2 is
  stronger than what the frozen targets would have given.

**What does NOT land, on purpose (flags record, the S2(iii) shape):** the frozen
`MRTLargeRangeEquidistributionFixed` and the T-form's large arm demand a uniform `C` at a
BARE exponent; every ζ'/ζ route needs `log Y ≥ K·(log t)^θ·(loglog t)^a` with `a > 0`, and
the T-form's own threshold admits `ε ≈ C₀/loglog X`, i.e. `log Y = (log X)^{3/4}·e^{O(1)}`,
where the deficit is `≥ (1−2/π)·4·logloglog X − O(1)` against an allowance `C₀/2`.  NOT
refuted (under RH both hold); STATEMENT-BLOCKED.  The source never claims the uniformity.
The bytes of both frozen statements are untouched; the honest family lands beside them.

Nothing here bears on twin primes: A.4(ii) is one floor inside the E-ladder's A.3 engine.
-/

namespace Salt.MR

/-! ## D1 and D2 — the statements in the source's quantifier order -/

/-- **D1 — the large-range Prop in the source's order.**  For every `ε > 0` a constant
`C = C(ε)` with, for `e ≤ X`, `e ≤ Y`, `(log X)^{20} < |u| ≤ 2X` and the floor
`(log X)^{3/4+ε} ≤ log Y`, `(1 − 2/π)·log(log X/log Y) − C ≤ Σ_{Y<p≤X}(1 − |cos(u·log p/2)|)/p`.
Weaker than the frozen `MRTLargeRangeEquidistributionFixed` in exactly two ways (the floor
exponent `3/4 + ε` vs the bare `2/3`, and `∀ε ∃C` vs `∃C ∀`), see `largeRangeFixedEps_of_fixed`;
`e ≤ Y` is carried because mathlib's `log` is even.  The floor exponent is the landed region's
θ = 3/4 (A.4(ii)'s (A.5) is written at `2/3 + ε` in the source; a `2/3` region moves this one
numeral through the same port).  Statement act: the freeze §4, Fable-tier. -/
def MRTLargeRangeEquidistributionFixedEps : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Y u : ℝ), Real.exp 1 ≤ X → Real.exp 1 ≤ Y →
    |u| ≤ 2 * X → (Real.log X) ^ (20 : ℕ) < |u| →
    (Real.log X) ^ ((3 : ℝ) / 4 + ε) ≤ Real.log Y →
      (1 - 2 / Real.pi) * Real.log (Real.log X / Real.log Y) - C
        ≤ ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ)),
            (1 - |Real.cos (u * Real.log p / 2)|) / (p : ℝ)

/-- **D2 — the threshold producer with `∀ε` BEFORE `∃C₀`.**  `MRTLemmaA4iiFixed34T`'s binders
and hypotheses byte-for-byte, with the `ε` binder and its `0 < ε` moved out in front of the
existential: `C₀ = C₀(ε)`, the source's `≪_ε`.  The threshold `C₀/ε ≤ loglog X` is kept (it is
`X ≥ X₀(ε)` in the corpus's idiom and composes with `far34_threshold_close` unchanged).
Statement act: the freeze §4, Fable-tier. -/
def MRTLemmaA4iiFixed34E : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t t₁ : ℝ),
    (∀ n, ‖f n‖ ≤ 1) → Real.exp 1 ≤ X → |t| ≤ X →
    |t₁| ≤ X → pretDistSq f (costwist t₁) X = mrtM f X →
    ((1 / 8) * Real.log (Real.log X) ≤ mrtM f X
      ∨ (Real.log X) ^ ((1 : ℝ) / 16) / 2 < |t - t₁|) →
    C₀ / ε ≤ Real.log (Real.log X) →
      (1 / 8 - 1 / (4 * Real.pi) - ε) * Real.log (Real.log X)
        ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X

/-! ## The pins: the frozen strong forms imply the new ones -/

/-- **Pin.**  The frozen uniform-`C` Prop at the bare floor `2/3` implies D1: instantiate its
`C` for every `ε` and discharge the bare floor from the higher one by rpow monotonicity.
The reverse is NOT derivable (D1 has no uniformity clause, and no `ε > 0` makes
`3/4 + ε ≤ 2/3`). -/
theorem largeRangeFixedEps_of_fixed (hFix : MRTLargeRangeEquidistributionFixed) :
    MRTLargeRangeEquidistributionFixedEps := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := hFix
  refine ⟨C, hC, ?_⟩
  intro X Y u hXe _heY hu2X hulo hfl
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hXe
  exact h X Y u hXe hu2X hulo
    (le_trans (Real.rpow_le_rpow_of_exponent_le hlogX1 (by linarith)) hfl)

/-- **Pin.**  The uniform-`C₀` T-form implies the E-form: pure instantiation, the
`ε`-independent `C₀` reused.  The reverse would need `sup_ε C₀(ε) < ∞`, which the E-form
does not assert. -/
theorem lemmaA4iiFixed34E_of_fixed34T (hT : MRTLemmaA4iiFixed34T) : MRTLemmaA4iiFixed34E := by
  intro ε hε
  obtain ⟨C₀, h0, h⟩ := hT
  exact ⟨C₀, h0, fun f Pseq Qseq 𝒥 X t t₁ hf hXe htX ht₁X hmin harm hthr =>
    h f Pseq Qseq 𝒥 X t t₁ ε hf hXe htX hε ht₁X hmin harm hthr⟩

/-! ## The port: the Y-parametric LARGE-range theorem, uniform `C` -/

set_option maxHeartbeats 2000000 in
-- one long assembly, the mid-range template's shape: two absorbing branches, a per-harmonic
-- VK bound (the bounded-height regime is empty above the branch threshold), and several
-- large `linarith`/`nlinarith` closes over the Mertens/tail/harmonic atoms
/-- **AU — the Y-parametric large-range theorem, uniform `C`.**  With `e ≤ X`, `e ≤ Y`, the
floor `(log X)^{3/4}·(loglog X)^5 ≤ log Y` and the range `(log X)^{20} < |u| ≤ 2X`,
`(1 − 2/π)·log(log X/log Y) − C ≤ Σ_{Y<p≤X} (1 − |cos(u·log p/2)|)/p` with an absolute `C`.
The port of `mrt_mid_range_parametric` (A4FMidRange.lean): the height of the `m`-th harmonic is
`|m·u| ≤ 2·Mcut·X`, so `log|m·u| ≤ 2·log X` and `D(m·u) ≤ 32·(log X)^{3/4}·(loglog X)^4`
(rpow monotonicity at exponent `3/4` — the one new stone); the VK window
`400·D/cR ≤ (log X)^{3/4}·(loglog X)^5 ≤ log Y` then holds once `loglog X ≥ 12800/cR`, and
every harmonic is above `T₀` once `loglog X ≥ log T₀`, so the bounded-height regime never
occurs.  `e ≤ Y` is load-bearing: the floor vanishes at `X = e`. -/
theorem mrt_large_range_parametric :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Y u : ℝ), Real.exp 1 ≤ X → Real.exp 1 ≤ Y →
      (Real.log X) ^ ((3 : ℝ) / 4) * (Real.log (Real.log X)) ^ (5 : ℕ) ≤ Real.log Y →
      (Real.log X) ^ (20 : ℕ) < |u| → |u| ≤ 2 * X →
        (1 - 2 / Real.pi) * Real.log (Real.log X / Real.log Y) - C
          ≤ ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter
                (fun p : ℕ => Y < (p : ℝ)),
              (1 - |Real.cos (u * Real.log p / 2)|) / (p : ℝ) := by
  obtain ⟨K₂, cR, T₀, hK₂0, hcR0, hcR1, hT₀3, hVK⟩ := harmonic_prime_sum_abs_le_vk
  set B₁ : ℝ := K₂ + 1 with hB₁
  have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; linarith
  set Q' : ℝ := 12800 / cR with hQ'
  have hQ'0 : 0 < Q' := by positivity
  have hlogT₀ : 0 < Real.log T₀ := Real.log_pos (by linarith)
  set Λ₀ : ℝ := 32 + Q' + Real.log T₀ with hΛ₀
  have hΛ₀32 : (32 : ℝ) ≤ Λ₀ := by rw [hΛ₀]; linarith
  refine ⟨30 + B₁ + Λ₀, by positivity, ?_⟩
  intro X Y u heX heY hYfl hufl hu2X
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπpos : 0 < Real.pi := by linarith
  have h2π : 2 / Real.pi < 1 := by rw [div_lt_one hπpos]; linarith
  have h2π0 : 0 < 2 / Real.pi := by positivity
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) heX
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) heX
  have hlogXpos : 0 < Real.log X := by linarith
  set lam : ℝ := Real.log (Real.log X) with hlam
  have hlam0 : 0 ≤ lam := Real.log_nonneg hlogX1
  -- `1 ≤ log Y` (from `e ≤ Y`; the floor alone gives only `e ≤ |Y|`, mathlib's `log` being
  -- even — and the floor VANISHES at `X = e`, so `e ≤ Y` is load-bearing here)
  have hlogY1 : (1 : ℝ) ≤ Real.log Y := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) heY
  have hlogYpos : 0 < Real.log Y := by linarith
  set Δ : ℝ := Real.log (Real.log X / Real.log Y) with hΔ
  -- the demand is capped by `lam` at every `X` (from `1 ≤ log Y` alone)
  have hΔlam : Δ ≤ lam := by
    have hdiv : Real.log X / Real.log Y ≤ Real.log X := by
      rw [div_le_iff₀ hlogYpos]; nlinarith
    have hpos : 0 < Real.log X / Real.log Y := by positivity
    exact Real.log_le_log hpos hdiv
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
  · have hΔΛ : Δ ≤ Λ₀ := by linarith
    have h1 : (1 - 2 / Real.pi) * Δ ≤ Λ₀ := by
      rcases le_or_gt Δ 0 with hΔ0 | hΔ0
      · nlinarith
      · nlinarith
    linarith [hT0, hB₁0]
  -- ## the `Y > X` branch: empty window, nonpositive demand
  rcases lt_or_ge X Y with hXY | hYX
  · have hΔ0 : Δ ≤ 0 := by
      have hlogle : Real.log X ≤ Real.log Y := Real.log_le_log hXpos hXY.le
      have hratio : Real.log X / Real.log Y ≤ 1 := by rw [div_le_one hlogYpos]; exact hlogle
      exact Real.log_nonpos (by positivity) hratio
    have : (1 - 2 / Real.pi) * Δ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h12 hΔ0
    linarith [hT0, hB₁0, hΛ₀32]
  -- ## the large branch, `Y ≤ X`
  have hlam32 : (32 : ℝ) ≤ lam := le_trans hΛ₀32 hbig
  have hlam1 : (1 : ℝ) ≤ lam := by linarith
  have hlamQ : Q' ≤ lam := by linarith [hbig, hΛ₀]
  have hlamT₀ : Real.log T₀ ≤ lam := by linarith [hbig, hΛ₀, hQ'0]
  -- the demand is capped by `lam/4` (the floor, with `lam^5 ≥ 1`)
  have hΔle : Δ ≤ lam / 4 := by
    have hlam5 : (1 : ℝ) ≤ lam ^ (5 : ℕ) := one_le_pow₀ hlam1
    have hdiv : Real.log X / Real.log Y ≤ (Real.log X) ^ ((1 : ℝ) / 4) := by
      rw [div_le_iff₀ hlogYpos]
      calc Real.log X = (Real.log X) ^ ((1 : ℝ) / 4) * (Real.log X) ^ ((3 : ℝ) / 4) := by
            rw [← Real.rpow_add hlogXpos]; norm_num
        _ ≤ (Real.log X) ^ ((1 : ℝ) / 4) * ((Real.log X) ^ ((3 : ℝ) / 4) * lam ^ (5 : ℕ)) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hlogXpos.le _)
            exact le_mul_of_one_le_right (Real.rpow_nonneg hlogXpos.le _) hlam5
        _ ≤ (Real.log X) ^ ((1 : ℝ) / 4) * Real.log Y :=
            mul_le_mul_of_nonneg_left hYfl (Real.rpow_nonneg hlogXpos.le _)
    have hpos : 0 < Real.log X / Real.log Y := by positivity
    calc Δ ≤ Real.log ((Real.log X) ^ ((1 : ℝ) / 4)) := Real.log_le_log hpos hdiv
      _ = lam / 4 := by rw [Real.log_rpow hlogXpos, hlam]; ring
  -- every harmonic is above the VK threshold: `T₀ ≤ log X ≤ (log X)^20 < |u| ≤ |m·u|`
  have hT₀X : T₀ ≤ Real.log X := by
    have h1 : Real.exp (Real.log T₀) ≤ Real.exp lam := Real.exp_le_exp.mpr hlamT₀
    rw [Real.exp_log (by linarith), hlam, Real.exp_log hlogXpos] at h1
    exact h1
  have hlogX20 : Real.log X ≤ (Real.log X) ^ (20 : ℕ) := le_self_pow₀ hlogX1 (by norm_num)
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
  have hMcutpos : (0 : ℝ) < (Mcut : ℝ) := by linarith
  -- three logarithmic stones shared by every harmonic
  have hlogM : Real.log (Mcut : ℝ) ≤ lam := by
    have := Real.log_le_sub_one_of_pos hMcutpos; linarith [hMcutle]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlamX : lam + 1 ≤ Real.log X := by
    have := Real.log_le_sub_one_of_pos hlogXpos; rw [hlam]; linarith
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
  -- the per-harmonic bound: every harmonic is in the VK regime
  have hSm : ∀ m ∈ Finset.Icc 1 Mcut,
      |∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ)),
          Real.cos (((m : ℝ) * u) * Real.log p) / (p : ℝ)| ≤ B₁ := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmM : m ≤ Mcut := (Finset.mem_Icc.mp hm).2
    have hmR1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have habs_mu : |(m : ℝ) * u| = (m : ℝ) * |u| := by
      rw [abs_mul, abs_of_pos (by linarith)]
    -- above the threshold
    have hgt : T₀ < |(m : ℝ) * u| := by
      have h1 : |u| ≤ (m : ℝ) * |u| := le_mul_of_one_le_left (abs_nonneg u) hmR1
      rw [habs_mu]; linarith [hT₀X, hlogX20, hufl]
    have ht3 : (3 : ℝ) ≤ |(m : ℝ) * u| := le_trans hT₀3 hgt.le
    have hexp1lt3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    have hlogt1 : (1 : ℝ) < Real.log |(m : ℝ) * u| := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hexp1lt3
        _ ≤ Real.log |(m : ℝ) * u| := Real.log_le_log (by norm_num) ht3
    -- the height: `|m·u| ≤ Mcut·2X`, so `log|m·u| ≤ 2·log X`
    have htle : |(m : ℝ) * u| ≤ (Mcut : ℝ) * (2 * X) := by
      rw [habs_mu]
      exact mul_le_mul (by exact_mod_cast hmM) hu2X (abs_nonneg u) (Nat.cast_nonneg _)
    have hlogt : Real.log |(m : ℝ) * u| ≤ 2 * Real.log X := by
      calc Real.log |(m : ℝ) * u| ≤ Real.log ((Mcut : ℝ) * (2 * X)) :=
            Real.log_le_log (by linarith) htle
        _ = Real.log (Mcut : ℝ) + (Real.log 2 + Real.log X) := by
            rw [Real.log_mul hMcutpos.ne' (by positivity), Real.log_mul (by norm_num) hXpos.ne']
        _ ≤ 2 * Real.log X := by linarith
    have hlogtpos : 0 < Real.log |(m : ℝ) * u| := by linarith
    have hloglogt : Real.log (Real.log |(m : ℝ) * u|) ≤ 2 * lam := by
      calc Real.log (Real.log |(m : ℝ) * u|) ≤ Real.log (2 * Real.log X) :=
            Real.log_le_log hlogtpos hlogt
        _ = Real.log 2 + lam := by rw [Real.log_mul (by norm_num) hlogXpos.ne', hlam]
        _ ≤ 2 * lam := by linarith
    have hloglogt0 : 0 < Real.log (Real.log |(m : ℝ) * u|) := Real.log_pos hlogt1
    set D : ℝ := (Real.log |(m : ℝ) * u|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |(m : ℝ) * u|)) ^ (4 : ℕ) with hD
    have hDpos : 0 < D := by
      rw [hD]
      have : (0 : ℝ) < (Real.log |(m : ℝ) * u|) ^ ((3 : ℝ) / 4) :=
        Real.rpow_pos_of_pos hlogtpos _
      positivity
    -- THE NEW STONE: rpow monotonicity at exponent `3/4`, against the floor's own exponent
    have hDle : D ≤ 32 * (Real.log X) ^ ((3 : ℝ) / 4) * lam ^ (4 : ℕ) := by
      have h2 : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
        calc (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 : ℝ) ^ ((1 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have h34 : (Real.log |(m : ℝ) * u|) ^ ((3 : ℝ) / 4)
          ≤ 2 * (Real.log X) ^ ((3 : ℝ) / 4) := by
        calc (Real.log |(m : ℝ) * u|) ^ ((3 : ℝ) / 4)
            ≤ (2 * Real.log X) ^ ((3 : ℝ) / 4) :=
              Real.rpow_le_rpow hlogtpos.le hlogt (by norm_num)
          _ = (2 : ℝ) ^ ((3 : ℝ) / 4) * (Real.log X) ^ ((3 : ℝ) / 4) :=
              Real.mul_rpow (by norm_num) hlogXpos.le
          _ ≤ 2 * (Real.log X) ^ ((3 : ℝ) / 4) :=
              mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hlogXpos.le _)
      have h4 : (Real.log (Real.log |(m : ℝ) * u|)) ^ (4 : ℕ) ≤ (2 * lam) ^ (4 : ℕ) :=
        pow_le_pow_left₀ hloglogt0.le hloglogt 4
      rw [hD]
      calc (Real.log |(m : ℝ) * u|) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log |(m : ℝ) * u|)) ^ (4 : ℕ)
          ≤ (2 * (Real.log X) ^ ((3 : ℝ) / 4)) * (2 * lam) ^ (4 : ℕ) :=
            mul_le_mul h34 h4 (pow_nonneg hloglogt0.le 4)
              (mul_nonneg (by norm_num) (Real.rpow_nonneg hlogXpos.le _))
        _ = 32 * (Real.log X) ^ ((3 : ℝ) / 4) * lam ^ (4 : ℕ) := by ring
    -- the window: `400·D/cR ≤ (log X)^{3/4}·lam^5 ≤ log Y` once `lam ≥ 12800/cR`
    have hDcR : 400 * D / cR ≤ Real.log Y := by
      have hA0 : 0 ≤ (Real.log X) ^ ((3 : ℝ) / 4) * lam ^ (4 : ℕ) :=
        mul_nonneg (Real.rpow_nonneg hlogXpos.le _) (pow_nonneg hlam0 4)
      calc 400 * D / cR ≤ 400 * (32 * (Real.log X) ^ ((3 : ℝ) / 4) * lam ^ (4 : ℕ)) / cR := by
            rw [div_le_div_iff_of_pos_right hcR0]
            exact mul_le_mul_of_nonneg_left hDle (by norm_num)
        _ = Q' * ((Real.log X) ^ ((3 : ℝ) / 4) * lam ^ (4 : ℕ)) := by rw [hQ']; ring
        _ ≤ lam * ((Real.log X) ^ ((3 : ℝ) / 4) * lam ^ (4 : ℕ)) :=
            mul_le_mul_of_nonneg_right hlamQ hA0
        _ = (Real.log X) ^ ((3 : ℝ) / 4) * lam ^ (5 : ℕ) := by ring
        _ ≤ Real.log Y := hYfl
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
      _ ≤ B₁ := by linarith [hB₁]
  -- ## assemble (verbatim from the mid range: no height enters below this line)
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

/-! ## The producers: D1 from the theorem, D2 from D1 -/

/-- **D1 is PRODUCED.**  From the uniform-`C` theorem through the `(x/7)^7 ≤ e^x` stone:
above the threshold `(loglog X)^2 ≥ (7/ε)^7` one has `(loglog X)^5 ≤ (log X)^ε`, so D1's floor
`(log X)^{3/4+ε} ≤ log Y` implies the theorem's; below it `loglog X ≤ (7/ε)^7 + 1` and the
demand `≤ loglog X` is absorbed into `C(ε) = C + (7/ε)^7 + 1`.  `pow` arithmetic only. -/
theorem mrtLargeRangeEquidistributionFixedEps_holds : MRTLargeRangeEquidistributionFixedEps := by
  obtain ⟨C, hC0, hmain⟩ := mrt_large_range_parametric
  intro ε hε
  refine ⟨C + (7 / ε) ^ (7 : ℕ) + 1, by positivity, ?_⟩
  intro X Y u heX heY hu2X hulo hfl
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) heX
  have hlogXpos : 0 < Real.log X := by linarith
  set lam : ℝ := Real.log (Real.log X) with hlam
  have hlam0 : 0 ≤ lam := Real.log_nonneg hlogX1
  have hlogY1 : (1 : ℝ) ≤ Real.log Y := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) heY
  have hlogYpos : 0 < Real.log Y := by linarith
  set Δ : ℝ := Real.log (Real.log X / Real.log Y) with hΔ
  have hΔlam : Δ ≤ lam := by
    have hdiv : Real.log X / Real.log Y ≤ Real.log X := by
      rw [div_le_iff₀ hlogYpos]; nlinarith
    have hpos : 0 < Real.log X / Real.log Y := by positivity
    exact Real.log_le_log hpos hdiv
  have hT0 : 0 ≤ ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter
      (fun p : ℕ => Y < (p : ℝ)), (1 - |Real.cos (u * Real.log p / 2)|) / (p : ℝ) := by
    refine Finset.sum_nonneg fun p _ => ?_
    have := Real.abs_cos_le_one (u * Real.log p / 2)
    exact div_nonneg (by linarith) (Nat.cast_nonneg p)
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h12 : 0 ≤ 1 - 2 / Real.pi := by
    have : 2 / Real.pi < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have h12' : 1 - 2 / Real.pi ≤ 1 := by
    have : 0 < 2 / Real.pi := by positivity
    linarith
  have h7ε0 : (0 : ℝ) ≤ (7 / ε) ^ (7 : ℕ) := by positivity
  rcases lt_or_ge (lam ^ (2 : ℕ)) ((7 / ε) ^ (7 : ℕ)) with hsmall | hbig
  · -- below the threshold: absorb
    have hlamle : lam ≤ (7 / ε) ^ (7 : ℕ) + 1 := by
      rcases le_or_gt lam 1 with h1 | h1
      · linarith
      · have : lam ≤ lam ^ (2 : ℕ) := by nlinarith
        linarith
    have h1 : (1 - 2 / Real.pi) * Δ ≤ (7 / ε) ^ (7 : ℕ) + 1 := by
      rcases le_or_gt Δ 0 with hΔ0 | hΔ0
      · nlinarith
      · nlinarith
    linarith [hT0, hC0]
  · -- above the threshold: `lam^5 ≤ (log X)^ε`, so D1's floor implies the theorem's
    have hlam5 : lam ^ (5 : ℕ) ≤ Real.exp (ε * lam) := by
      have h7 := div_seven_pow_seven_le_exp (x := ε * lam) (by positivity)
      have hkey : lam ^ (5 : ℕ) ≤ (ε * lam / 7) ^ (7 : ℕ) := by
        have hεpos : 0 < (ε / 7) ^ (7 : ℕ) := by positivity
        have hprod : (ε / 7) ^ (7 : ℕ) * (7 / ε) ^ (7 : ℕ) = 1 := by
          rw [← mul_pow, div_mul_div_comm, mul_comm ε 7, div_self (by positivity), one_pow]
        have h1 : 1 ≤ (ε / 7) ^ (7 : ℕ) * lam ^ (2 : ℕ) := by
          calc (1 : ℝ) = (ε / 7) ^ (7 : ℕ) * (7 / ε) ^ (7 : ℕ) := hprod.symm
            _ ≤ (ε / 7) ^ (7 : ℕ) * lam ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hbig hεpos.le
        have hlam5nn : 0 ≤ lam ^ (5 : ℕ) := by positivity
        calc lam ^ (5 : ℕ) = 1 * lam ^ (5 : ℕ) := (one_mul _).symm
          _ ≤ ((ε / 7) ^ (7 : ℕ) * lam ^ (2 : ℕ)) * lam ^ (5 : ℕ) :=
              mul_le_mul_of_nonneg_right h1 hlam5nn
          _ = (ε * lam / 7) ^ (7 : ℕ) := by ring
      exact le_trans hkey h7
    have hfloorLL : (Real.log X) ^ ((3 : ℝ) / 4) * lam ^ (5 : ℕ) ≤ Real.log Y := by
      have hexp : Real.exp (ε * lam) = (Real.log X) ^ ε := by
        rw [Real.rpow_def_of_pos hlogXpos, hlam]; ring_nf
      calc (Real.log X) ^ ((3 : ℝ) / 4) * lam ^ (5 : ℕ)
          ≤ (Real.log X) ^ ((3 : ℝ) / 4) * Real.exp (ε * lam) :=
            mul_le_mul_of_nonneg_left hlam5 (Real.rpow_nonneg hlogXpos.le _)
        _ = (Real.log X) ^ ((3 : ℝ) / 4 + ε) := by rw [hexp, ← Real.rpow_add hlogXpos]
        _ ≤ Real.log Y := hfl
    have h := hmain X Y u heX heY hfloorLL hulo hu2X
    linarith [h, h7ε0]

/-- **A.4(ii) WHOLE AT θ = 3/4, UNCONDITIONAL — in the source's quantifier order.**  The
threshold producer in the E-form: the high-M arm through `mrtA4ii_high_M_target34`, the far
arm split at `(log X)^{20}` — the mid range through `mrtA4ii_far34_C`, the large range
through D1 at `ε' = ε/(1 − 2/π)` and the landed composer — both closed by
`far34_threshold_close` with `C₀ = max C₁ C₂(ε')`.  The body of
`mrtLemmaA4iiFixed34T_of_largeRangeFixed` (A4FThreshold.lean) rethreaded: `C₂` is obtained
AFTER `ε`, the bare `2/3` floor line becomes equality at the consumer's `Y`, and `e ≤ Y` is
supplied by `Real.one_le_rpow`. -/
theorem mrtLemmaA4iiFixed34E_holds : MRTLemmaA4iiFixed34E := by
  intro ε hε
  obtain ⟨C₁, hC₁0, hfar⟩ := mrtA4ii_far34_C
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h12 : 0 < 1 - 2 / Real.pi := by
    have : 2 / Real.pi < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hε'pos : 0 < ε / (1 - 2 / Real.pi) := div_pos hε h12
  obtain ⟨C₂, hC₂0, hlarge⟩ :=
    mrtLargeRangeEquidistributionFixedEps_holds (ε / (1 - 2 / Real.pi)) hε'pos
  refine ⟨max C₁ C₂, le_trans hC₁0 (le_max_left _ _), ?_⟩
  intro f Pseq Qseq 𝒥 X t t₁ hf hXe htX ht₁X hmin harm hthr
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hlogX1 : 1 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hXpos]; exact hXe
  rcases harm with hM | hfarhyp
  · exact mrtA4ii_high_M_target34 f Pseq Qseq 𝒥 X t ε hf hXe htX hε hM
  · have hmin' : pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist t) X := by
      rw [hmin]; exact mrtM_le f hXpos.le htX
    have hthr₁ : C₁ / ε ≤ Real.log (Real.log X) :=
      le_trans (div_le_div_of_nonneg_right (le_max_left _ _) hε.le) hthr
    have hthr₂ : C₂ / ε ≤ Real.log (Real.log X) :=
      le_trans (div_le_div_of_nonneg_right (le_max_right _ _) hε.le) hthr
    rcases le_or_gt |t - t₁| ((Real.log X) ^ (20 : ℕ)) with hmid | hlarge_range
    · have h := hfar f Pseq Qseq 𝒥 X t t₁ (ε / (1 - 2 / Real.pi)) hf hε'pos hXe
        hfarhyp.le hmid hmin'
      exact far34_threshold_close hlogX1 hε hthr₁ h
    · have hfloor : (Real.log X) ^ ((3 : ℝ) / 4 + ε / (1 - 2 / Real.pi))
          ≤ Real.log (Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε / (1 - 2 / Real.pi)))) := by
        rw [Real.log_exp]
      have heY : Real.exp 1 ≤ Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε / (1 - 2 / Real.pi))) :=
        Real.exp_le_exp.mpr (Real.one_le_rpow hlogX1 (by linarith))
      have ht := abs_le.mp htX
      have ht₁ := abs_le.mp ht₁X
      have hu2X : |t - t₁| ≤ 2 * X := abs_le.mpr ⟨by linarith, by linarith⟩
      have hb := hlarge X (Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε / (1 - 2 / Real.pi))))
        (t - t₁) hXe heY hu2X hlarge_range hfloor
      have h := mrtA4ii_far_of_either_estimate f Pseq Qseq 𝒥 X
        (Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε / (1 - 2 / Real.pi)))) t t₁ C₂ hf hmin' hb
      exact far34_threshold_close hlogX1 hε hthr₂ h

end Salt.MR
