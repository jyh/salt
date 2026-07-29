/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CapFreeAssembly
import Salt.MR.CofactorSupplier
import Salt.Mertens.Third

/-!
# ⟦F4⟧ — THE SHARP `p | q` DEFICIT AND THE SHARP THRESHOLD FAMILY (`CapFreeSharp`)

`CapFreeAssembly.primeDivSum_le_modulus` prices the `p | q` deficit
`primeDivSum q X = ∑_{p | q, p ≤ X} 1/p` by `q` outright ("Crude on purpose": at most
`q + 1` prime divisors, each `≤ 1/2`).  That crude price rides in-statement as `(1/4)·q`
inside every cap-free threshold, so the assembled floor's hypothesis carries a term
`32·(1/4)·q = 8q` — at the door's own modulus range `q ≤ (log H)^12` an EXPONENTIAL
demand `8·exp(12·loglog H)` on `loglog X`.

**This file replaces `q` by `loglog q`, and nothing else moves.**  Every prime factor of
`q` is `≤ q`, so the deficit is at most the FULL Mertens partial sum at `t = q`, and the
in-kernel sharp Mertens-2 (`Salt.Mertens.mertens_second_sharp_real`:
`|S(t) − (loglog t + M)| ≤ 12/log t` for `t ≥ 2`) prices that.  The threshold's `8q`
becomes `8·loglog q ≤ 8·log(12·loglog H)` — the exponential demand collapses to a
doubly-logarithmic one, and what is left of the `q`-content in the threshold is the
landed `28·log q` (the `(1/8)log q`, the `(1/4)log C` and the `vkMidDebit` halves).

## SIBLING-ADDITIVE

Nothing landed moves.  `primeDivSum_le_modulus` and the whole `capFreeFloor3`-family stay
byte-identical; every statement here is a NEW `_sharp` sibling whose CONCLUSION is
byte-identical to its landed original and whose HYPOTHESIS has the `(1/4)·q` summand
replaced by `(1/4)·mertensCap q`.

⚠ **The weakening is asymptotic, not universal.**  `mertensCap q ≤ q` is FALSE at small
`q` (`mertensCap 1 = mertensCap 2 ≈ 17.2`, the `12/log 2` half): the crude bound is
already tiny there, and the Mertens window's `12/log q` error swamps it.  The crossover
is at `q ≈ 8`, and from there the gap grows without bound — at the door's own range
`q ≤ (log H)^12` the crude `32·(1/4)·q` is `8·exp(12·loglog H)` while the sharp term is
`≤ 8·log(12·loglog H) + 8M + 96/log 2` (`mertensCap_le_of_le`).

## THE `q = 1` CORNER

The sharp bound is stated through `mertensCap`, which reads the Mertens data at
`max 2 q`.  Mertens-2 has no content below `t = 2`, and the corpus's only landed lower
bound on the Meissel–Mertens constant is `SmallStones.mertensM_ge_neg_seventeen`
(`−17 ≤ M`, crude on purpose), which does not settle the sign of `M`.  The `max` costs
nothing: `mertensCap` is evaluated at `q ≥ 2` everywhere the register uses it, and at
`q = 1` the deficit is `0` while `mertensCap 1` is the (nonnegative) `q = 2` value.

## VT-7 (NOT LANDED — the term stays symbolic)

`vkMidDebit q` is carried symbolically in every threshold below, exactly as the landed
originals carry it.  A future VT-7 (the classical 1-line mid bound
`‖L(1+δ+it,χ)‖ ≪ log(q(|t|+2))`, plugged at `VkTwistClose.chi_Llower_341_of_ub`'s `U`
slot) therefore folds into this family by a definitional swap at one name, with no
statement here re-cut.

Source pins: `Salt/MR/CapFreeAssembly.lean` (the landed originals),
`Salt/MR/CofactorSupplier.lean` (the margin/masked stack),
`Salt/Mertens/Third.lean` (`mertens_second_sharp_real`, `SPartial`, `mertensM`),
`docs/blueprints/flags.md` (⟦F4 — the primeDivSum repair⟧, REF-F5's R3).
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — THE STONE: the `p | q` deficit at the sharp Mertens price -/

/-- **THE STONE** (`primeDivSum_le_loglog`).  For every `q ≥ 2` and EVERY `X`,

  `∑_{p | q, p ≤ X} 1/p ≤ loglog q + M + 12/log q`

with `M = Salt.Mertens.mertensM` the Meissel–Mertens constant.

Two moves, no analysis: every prime `p | q` satisfies `p ≤ q` (as `q ≠ 0`), so the index
set of `primeDivSum q X` injects into the index set of `Salt.Mertens.SPartial q`
(`{p ≤ q : p prime}`) whatever `X` is — the bound is `X`-FREE, the only property the
regime lever ever needed from the crude form.  Then the in-kernel sharp real-variable
Mertens-2 `Salt.Mertens.mertens_second_sharp_real` at `t = q ≥ 2` prices that full sum.

Compare `primeDivSum_le_modulus` (the same object, bounded by `q`). -/
theorem primeDivSum_le_loglog {q : ℕ} (hq : 2 ≤ q) (X : ℝ) :
    primeDivSum q X
      ≤ Real.log (Real.log q) + Salt.Mertens.mertensM + 12 / Real.log q := by
  have hq0 : q ≠ 0 := by omega
  have hfl : ⌊((q : ℕ) : ℝ)⌋₊ = q := Nat.floor_natCast q
  -- the index set injects into the full prime range `[0, q]`
  have hsub : (Finset.range (⌊X⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ p ∣ q)
      ⊆ (Finset.range (⌊((q : ℕ) : ℝ)⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [hfl, Finset.mem_filter, Finset.mem_range]
    have hle : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hp.2.2
    exact ⟨by omega, hp.2.1⟩
  have hstep : primeDivSum q X ≤ Salt.Mertens.SPartial ((q : ℕ) : ℝ) := by
    unfold primeDivSum Salt.Mertens.SPartial
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => ?_)
    positivity
  have hq2 : (2 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast hq
  have hmert := (abs_le.mp (Salt.Mertens.mertens_second_sharp_real hq2)).2
  linarith

/-- **THE SHARP `p | q` CAP** (`mertensCap`).  `loglog q + M + 12/log q`, read at
`max 2 q` so that the `q = 1` corner (where Mertens-2 has no content) is covered by the
`q = 2` value.  This is the term that replaces the crude `(q : ℝ)` in every `_sharp`
threshold below. -/
def mertensCap (q : ℕ) : ℝ :=
  Real.log (Real.log ((max 2 q : ℕ) : ℝ)) + Salt.Mertens.mertensM
    + 12 / Real.log ((max 2 q : ℕ) : ℝ)

/-- The stone at `mertensCap`'s own argument. -/
theorem primeDivSum_max_le_mertensCap (q : ℕ) (X : ℝ) :
    primeDivSum (max 2 q) X ≤ mertensCap q :=
  primeDivSum_le_loglog (le_max_left 2 q) X

/-- `mertensCap` is nonnegative — it dominates a sum of nonnegative terms. -/
theorem mertensCap_nonneg (q : ℕ) : 0 ≤ mertensCap q := by
  have h0 : (0 : ℝ) ≤ primeDivSum (max 2 q) 0 := by
    unfold primeDivSum
    exact Finset.sum_nonneg (fun p _ => by positivity)
  linarith [primeDivSum_max_le_mertensCap q 0]

/-- **THE STONE, at the register's own side condition** (`primeDivSum_le_mertensCap`).
`q ≠ 0` — exactly the hypothesis `primeDivSum_le_modulus` carries, and exactly what
`[NeZero q]` supplies. -/
theorem primeDivSum_le_mertensCap {q : ℕ} (hq : q ≠ 0) (X : ℝ) :
    primeDivSum q X ≤ mertensCap q := by
  rcases Nat.lt_or_ge q 2 with hlt | hge
  · -- `q = 1`: the deficit is empty and the cap is the (nonnegative) `q = 2` value
    have hq1 : q = 1 := by omega
    have hzero : primeDivSum q X = 0 := by
      unfold primeDivSum
      refine Finset.sum_eq_zero (fun p hp => ?_)
      rw [Finset.mem_filter] at hp
      obtain ⟨-, hpp, hpd⟩ := hp
      rw [hq1, Nat.dvd_one] at hpd
      subst hpd
      exact absurd hpp Nat.not_prime_one
    rw [hzero]
    exact mertensCap_nonneg q
  · have hmax : max 2 q = q := max_eq_right hge
    have := primeDivSum_max_le_mertensCap q X
    rwa [hmax] at this

/-- **THE MONOTONE MAJORANT** (`mertensCap_le_of_le`).  Over a finite modulus range
`q ≤ Q` with `2 ≤ Q`, `mertensCap q ≤ loglog Q + M + 12/log 2` — the shape the threshold
arithmetic consumes (`12/log 2 ≤ 17.4`).  `mertensCap` itself is not monotone (the
`12/log q` half decreases), which is why the majorant splits the two halves. -/
theorem mertensCap_le_of_le {q Q : ℕ} (hqQ : q ≤ Q) (hQ : 2 ≤ Q) :
    mertensCap q ≤ Real.log (Real.log Q) + Salt.Mertens.mertensM + 12 / Real.log 2 := by
  have hm2 : 2 ≤ max 2 q := le_max_left 2 q
  have hmQ : max 2 q ≤ Q := max_le hQ hqQ
  have hm2R : (2 : ℝ) ≤ ((max 2 q : ℕ) : ℝ) := by exact_mod_cast hm2
  have hmQR : ((max 2 q : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hmQ
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogm : Real.log 2 ≤ Real.log ((max 2 q : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) hm2R
  have hlogmpos : (0 : ℝ) < Real.log ((max 2 q : ℕ) : ℝ) := lt_of_lt_of_le hlog2 hlogm
  have hlogQ : Real.log ((max 2 q : ℕ) : ℝ) ≤ Real.log Q :=
    Real.log_le_log (by linarith) hmQR
  have hll : Real.log (Real.log ((max 2 q : ℕ) : ℝ)) ≤ Real.log (Real.log Q) :=
    Real.log_le_log hlogmpos hlogQ
  have hdiv : 12 / Real.log ((max 2 q : ℕ) : ℝ) ≤ 12 / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) hlog2 hlogm
  rw [mertensCap]
  linarith

/-! ## §2 — THE ARM SIBLING (the one consumption point) -/

/-- **ARM 1, SHARP** (`chi_floor_real_bulk_sharp`).  `CapFreeAssembly.chi_floor_real_bulk`
with its single `primeDivSum_le_modulus` consumption replaced by the stone: the debit
`(1/4)·q` becomes `(1/4)·mertensCap q`.  Everything else — the `k = 2` route, the two box
drifts, the constant `(C₀ + 23/4)/4` — is the landed proof verbatim. -/
theorem chi_floor_real_bulk_sharp :
    ∃ C : ℝ, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (X v : ℝ), q ≠ 0 → χ ^ 2 = 1 →
      Real.exp (Real.exp 1) ≤ X → 1 / 2 ≤ |v| → |v| ≤ 3 * X →
        (1 / 16) * Real.log (Real.log X)
            - (5 / 4) * Real.log (Real.log (Real.log X))
            - (1 / 4) * mertensCap q - C
          ≤ pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨C₀, hC₀⟩ := chi_floor_of_order
  refine ⟨(C₀ + 23 / 4) / 4, ?_⟩
  intro q χ X v hq hχ2 hX hv2 hv3
  obtain ⟨hX8, hlogX, hLL, _⟩ := cff_scale_facts hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hXe : Real.exp 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact le_trans (Real.exp_le_exp.mpr h1) hX
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hkt : (1 : ℝ) ≤ |((2 : ℕ) : ℝ) * v| := by
    rw [hcast, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hmain := hC₀ q χ 2 X v (by norm_num) ⟨1, by norm_num⟩ hχ2 hXe hkt
  rw [hcast] at hmain
  have hsq : ((2 : ℝ)) ^ 2 = 4 := by norm_num
  rw [hsq] at hmain
  have hA := cff_box_loglog (X := X) (v := v) hX hv3
  have hB := cff_box_logloglog (X := X) (v := v) hX hv3
  have hP := primeDivSum_le_mertensCap (q := q) hq X
  -- `CapFreeAssembly.cff_log_two_le_one` is `private`; the same one-liner
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  linarith

/-! ## §3 — THE SHARP THRESHOLD FAMILY (`CapFreeAssembly` §4/§5) -/

/-- **THE ASSEMBLED CAP-FREE FLOOR, SHARP** (`capFreeFloor3_all_chi_sharp`).
`CapFreeAssembly.capFreeFloor3_all_chi` with `(1/4)·q` replaced by `(1/4)·mertensCap q` in
the threshold.  Conclusion byte-identical; hypothesis weaker at every modulus past the
`q ≈ 8` crossover, and by an EXPONENTIAL margin at the door's range (`mertensCap_le_of_le`,
and the module docstring). -/
theorem capFreeFloor3_all_chi_sharp (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + K + 25)
        < Real.log (Real.log X) →
        CapFreeFloor3 (lamChi χ) X := by
  obtain ⟨Kvk, hvk⟩ := capFreeFloor3_lamChi_unconditional
  obtain ⟨Kbulk, hbulk⟩ := chi_floor_real_bulk_sharp
  obtain ⟨Kband, hband⟩ := chi_floor_band_arm Q
  refine ⟨max 0 (max Kvk (max Kbulk Kband)), le_max_left _ _, ?_⟩
  set K : ℝ := max 0 (max Kvk (max Kbulk Kband)) with hKdef
  have hK0 : 0 ≤ K := le_max_left _ _
  have hKvk : Kvk ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKbulk : Kbulk ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hKband : Kband ≤ K :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  intro q _ χ X hq hX hthr
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hmcap : (0 : ℝ) ≤ mertensCap q := mertensCap_nonneg q
  have hC1 : (1 : ℝ) ≤ vkEulerCorr q * vkTwistConst q := by
    nlinarith [one_le_vkEulerCorr q, one_le_vkTwistConst (q := q)]
  have hvkD : (0 : ℝ) ≤ vkDebitConst (vkEulerCorr q * vkTwistConst q) :=
    vkDebitConst_nonneg hC1
  have hvkM : (0 : ℝ) ≤ vkMidDebit q := vkMidDebit_nonneg q
  by_cases hsq : χ ^ 2 = 1
  · intro v hv
    by_cases hband2 : |v| ≤ 1 / 2
    · have h := hband q χ X v hq hX hband2
      linarith
    · have hvbig : 1 / 2 ≤ |v| := le_of_lt (not_le.mp hband2)
      have h := hbulk q χ X v hq0 hsq hX hvbig hv
      linarith
  · refine hvk q χ X hsq hX ?_
    linarith

/-- **The sharp assembled floor at the `X` box** (`capFreeFloor_all_chi_sharp`).
`CapFreeAssembly.capFreeFloor_all_chi`'s sibling. -/
theorem capFreeFloor_all_chi_sharp (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + K + 25)
        < Real.log (Real.log X) →
        CapFreeFloor (lamChi χ) X := by
  obtain ⟨K, hK0, hK⟩ := capFreeFloor3_all_chi_sharp Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ X hq hX hthr
  obtain ⟨hX8, _, _, _⟩ := cff_scale_facts hX
  exact capFreeFloor_of_capFreeFloor3 (by linarith) (hK q χ X hq hX hthr)

/-- **The sharp assembled constant, named** (`cffKSharp`).  `cffK`'s sibling: one
`Classical.choose`, spent here. -/
def cffKSharp (Q : ℕ) : ℝ := Classical.choose (capFreeFloor3_all_chi_sharp Q)

theorem cffKSharp_nonneg (Q : ℕ) : 0 ≤ cffKSharp Q :=
  (Classical.choose_spec (capFreeFloor3_all_chi_sharp Q)).1

/-- The defining property of `cffKSharp` — `capFreeFloor3_all_chi_sharp`'s body at the
chosen constant (`cffK_spec`'s sibling). -/
theorem cffKSharp_spec (Q : ℕ) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + cffKSharp Q + 25)
        < Real.log (Real.log X) →
        CapFreeFloor3 (lamChi χ) X :=
  (Classical.choose_spec (capFreeFloor3_all_chi_sharp Q)).2

/-- **THE SHARP FLOOR AT THE ROW'S OWN DATUM** (`capFreeFloor3_liouChi_all_sharp`).
`CapFreeAssembly.capFreeFloor3_liouChi_all`'s sibling — the shape
`ThmA2Rows.a2Rows_of_capfree3` consumes. -/
theorem capFreeFloor3_liouChi_all_sharp (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + K + 25)
        < Real.log (Real.log X) →
        CapFreeFloor3 (liouChi χ) X := by
  obtain ⟨K, hK0, hK⟩ := capFreeFloor3_all_chi_sharp Q
  exact ⟨K, hK0, fun q _ χ X hq hX hthr =>
    capFreeFloor3_liouChi_of_lamChi χ (hK q χ X hq hX hthr)⟩

/-! ## §4 — THE SHARP ALL-χ FLOOR STACK (`CofactorSupplier` §3) -/

/-- **THE ASSEMBLED χ-FLOOR WITH MARGIN, SHARP** (`capFreeFloor3_margin_all_chi_sharp`).
`CofactorSupplier.capFreeFloor3_margin_all_chi`'s sibling: the same three arms at their
pointwise forms, the same margin `D`, with `(1/4)·q` replaced by `(1/4)·mertensCap q`. -/
theorem capFreeFloor3_margin_all_chi_sharp (Qm : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X D : ℝ), q ≤ Qm →
      Real.exp (Real.exp 1) ≤ X → 0 ≤ D →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + K + 25 + D)
        < Real.log (Real.log X) →
      ∀ v : ℝ, |v| ≤ 3 * X →
        (1 / 32) * Real.log (Real.log X) + 25 + D < pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨Kvk, hvk⟩ := chi_floor_vk_pointwise
  obtain ⟨Kbulk, hbulk⟩ := chi_floor_real_bulk_sharp
  obtain ⟨Kband, hband⟩ := chi_floor_band_arm Qm
  refine ⟨max 0 (max Kvk (max Kbulk Kband)), le_max_left _ _, ?_⟩
  set K : ℝ := max 0 (max Kvk (max Kbulk Kband)) with hKdef
  have hK0 : 0 ≤ K := le_max_left _ _
  have hKvk : Kvk ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKbulk : Kbulk ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hKband : Kband ≤ K :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  intro q _ χ X D hq hX hD0 hthr v hv
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hmcap : (0 : ℝ) ≤ mertensCap q := mertensCap_nonneg q
  have hC1 : (1 : ℝ) ≤ vkEulerCorr q * vkTwistConst q := by
    nlinarith [one_le_vkEulerCorr q, one_le_vkTwistConst (q := q)]
  have hvkD : (0 : ℝ) ≤ vkDebitConst (vkEulerCorr q * vkTwistConst q) :=
    vkDebitConst_nonneg hC1
  have hvkM : (0 : ℝ) ≤ vkMidDebit q := vkMidDebit_nonneg q
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  by_cases hsq : χ ^ 2 = 1
  · by_cases hband2 : |v| ≤ 1 / 2
    · have h := hband q χ X v hq hX hband2
      linarith
    · have hvbig : 1 / 2 ≤ |v| := le_of_lt (not_le.mp hband2)
      have h := hbulk q χ X v hq0 hsq hX hvbig hv
      linarith
  · have hψ : (χ ^ 2 : DirichletCharacter ℂ q) ≠ 1 := hsq
    have hsock : Real.exp (Real.exp 100) ≤ |v| →
        VkTwistUB (vkEulerCorr q * vkTwistConst q) (χ ^ 2) X (2 * v) := by
      intro hbig
      have h2v : Real.exp (Real.exp 100) ≤ |2 * v| := by
        have hle : |v| ≤ |2 * v| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          nlinarith [abs_nonneg v]
        linarith
      exact vkTwistUB_holds (χ ^ 2) hψ hXe h2v
    have h := hvk q χ (vkEulerCorr q * vkTwistConst q) X v hC1 hsq hX hv hsock
    linarith

/-- **THE MASKED FLOOR, SHARP** (`capFreeFloor3_pieceDatum_sharp`).
`CofactorSupplier.capFreeFloor3_pieceDatum`'s sibling. -/
theorem capFreeFloor3_pieceDatum_sharp (Qm : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X D : ℝ), q ≤ Qm →
      Real.exp (Real.exp 1) ≤ X → 0 ≤ D →
      (∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)) ≤ D →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + K + 25 + D)
        < Real.log (Real.log X) →
        CapFreeFloor3 (pieceDatum χ 𝒥 Pseq Qseq) X := by
  obtain ⟨K, hK0, hK⟩ := capFreeFloor3_margin_all_chi_sharp Qm
  refine ⟨K, hK0, ?_⟩
  intro q _ χ Pseq Qseq 𝒥 X D hq hX hD0 hdebit hthr v hv
  have hmargin := hK q χ X D hq hX hD0 hthr v hv
  have hcw : ∀ p : ℕ, p.Prime → ‖costwist v p‖ ≤ 1 :=
    fun p _ => le_of_eq (costwist_norm v p)
  have htr := pretDistSq_pieceDatum_ge χ Pseq Qseq hcw X 𝒥 (w := costwist v)
  rw [pretDistSq_liouChi_eq] at htr
  linarith

end Salt.MR
