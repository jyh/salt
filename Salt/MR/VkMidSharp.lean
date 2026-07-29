/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CapFreeSharp
import Salt.MR.VkTwistClose
import Salt.SW.StripConvergence
import Salt.SW.GrahamWeights

/-!
# ⟦VT-7⟧ — THE LOG-SHAPED MID BRANCH AND THE COMBINED SHARP THRESHOLD (`VkMidSharp`)

`VkTwistClose.chi_Llower_341_height` supplies the 3-4-1's growth slot `U` on the bounded
height window `|t| ≤ T₀` from `ChiLLower.LFunction_norm_le_level`, whose Pólya–Vinogradov
shape is LINEAR in `‖s‖`:

  `U_old = 3·(3 + 2T₀)·q²·(1 + log q)`,  so  `(1/4)·log U_old ≈ (1/4)·log T₀`.

At the VK socket's own height floor `T₀ = exp(exp 100)` that is `(1/4)·e^100 ≈ 6.7·10^42`, and
the assembled threshold carries `32·vkMidDebit q`, i.e. an `X`-free demand `≈ 2.15·10^44` on
`loglog X` — the single largest number anywhere in the cap-free stack.

**This file replaces the LINEAR growth input by the classical LOG-shaped one.**  At the bridge
point `Re s = 1 + 1/log X > 1`,

  `‖L(s, ψ)‖ ≤ 7/2 + log 2 + log q + log(|Im s| + 2)`     (`norm_LFunction_le_logBound`)

for every nonprincipal `ψ mod q`.  The height then enters through `log T₀` instead of `T₀`:

  `U_vt = 7/2 + log 2 + log q + log(2T₀ + 2)`,  so  `(1/4)·log U_vt ≈ (1/4)·100 = 25`

at `T₀ = exp(exp 100)`.  The `32·vkMidDebitSharp q` block is `≈ 905`, and — a second, separate
gain — the `q`-content of the old block (`q²·(1+log q)` inside the logarithm, worth `16·log q`
in the threshold) collapses to `log q` inside a `log`, i.e. to nothing: the threshold's
`q`-coefficient drops from `28·log q` to `12·log q`.

## The route (three landed stones, no new analysis)

1. **The character-sum bound at the LEVEL** (`norm_char_partial_sum_le`): for a nonprincipal
   `ψ mod q` the partial sums `∑_{k<u} ψ(k)` are bounded by `q`, uniformly in `u` — the full
   period sums to `0` (`MulChar.sum_eq_zero_of_ne_one`) and the residual block has `< q` terms
   of norm `≤ 1`.  No Pólya–Vinogradov, no primitivity, no conductor bookkeeping.
2. **The truncation** (`Salt.SW.norm_LFunction_sub_partial_le`, `StripConvergence`:389, gate
   `0 < Re s` — the bridge point is strictly inside): split at `N = ⌈q(|t|+2)⌉`.  The tail is
   `q·(1 + ‖s‖(1 + 1/Re s))·N^{−Re s} ≤ (5 + 2|t|)/(|t| + 2) ≤ 5/2`, an ABSOLUTE constant: the
   `q` in the numerator cancels the `q` in `N`.
3. **The head** `‖∑_{n≤N} ψ(n)n^{−s}‖ ≤ ∑_{n≤N} 1/n ≤ 1 + log N` (`Salt.SW.sum_inv_Icc_le`),
   with `N ≤ 2q(|t|+2)`.

## SIBLING-ADDITIVE

Nothing landed moves.  `chi_Llower_341_height`, `vkMidDebit`, `chi_floor_vk_pointwise`, the
`capFreeFloor3`-family and the `⟦F4⟧` `_sharp` family are all byte-untouched.  §4's `_vt`
family is the SINGLE combined family carrying BOTH improvements — `(1/4)·q ↦
(1/4)·mertensCap q` (F4) and `vkMidDebit q ↦ vkMidDebitSharp q` (VT-7) — with conclusions
byte-identical to the landed originals.

Source pins: `Salt/MR/VkTwistClose.lean` (the mid/VK branches and the debits),
`Salt/MR/CapFreeSharp.lean` (⟦F4⟧, the family this one supersedes),
`Salt/SW/StripConvergence.lean` (the truncation engine),
`docs/blueprints/flags.md` (⟦REF-F5⟧ R3, ⟦COUNCIL 0729 — C4⟧).
-/

noncomputable section

namespace Salt.MR

open Complex DirichletCharacter Salt.SW
open scoped BigOperators

/-! ## §1 — the character-sum bound at the level (`M = q`, no Pólya–Vinogradov) -/

/-- A full period of a character sum, started anywhere, is the sum over `ZMod q`: the map
`k ↦ (c + k : ZMod q)` is a bijection `range q → ZMod q`, and translation is an equivalence. -/
private lemma sum_period_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (c : ℕ) :
    ∑ k ∈ Finset.range q, χ ((c + k : ℕ) : ZMod q) = ∑ a : ZMod q, χ a := by
  have h1 : ∑ k ∈ Finset.range q, χ ((c + k : ℕ) : ZMod q)
      = ∑ a : ZMod q, χ ((c : ZMod q) + a) := by
    refine Finset.sum_nbij' (fun k => (k : ZMod q)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_univ _
    · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro a ha; exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
    · intro a _; exact ZMod.natCast_rightInverse a
    · intro a _; rw [Nat.cast_add]
  rw [h1]
  simpa using Equiv.sum_comp (Equiv.addLeft (c : ZMod q)) (fun a => χ a)

/-- **THE LEVEL-`q` CHARACTER-SUM BOUND.**  For a NONPRINCIPAL `χ mod q` the ordered partial
sums are bounded by `q`, uniformly in `u`.  This is the crude companion of Pólya–Vinogradov
(`Salt.BV.polya_vinogradov`, `√q(1+log q)`, but PRIMITIVE only): a full period sums to `0`, so
only the last incomplete block survives, and it has fewer than `q` terms of norm `≤ 1`.

Crude is exactly right here: the truncation below cuts at `N ≍ q·(|t|+2)`, and the `q` of this
bound cancels the `q` of `N` — see `norm_LFunction_le_logBound`. -/
theorem norm_char_partial_sum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (u : ℕ) : ‖∑ k ∈ Finset.range u, χ ((k : ℕ) : ZMod q)‖ ≤ (q : ℝ) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hzero : ∀ c : ℕ, ∑ k ∈ Finset.range q, χ ((c + k : ℕ) : ZMod q) = 0 := fun c => by
    rw [sum_period_eq χ c]; exact MulChar.sum_eq_zero_of_ne_one hχ
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    rcases lt_or_ge u q with hlt | hge
    · calc ‖∑ k ∈ Finset.range u, χ ((k : ℕ) : ZMod q)‖
          ≤ ∑ k ∈ Finset.range u, ‖χ ((k : ℕ) : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range u, (1 : ℝ) :=
            Finset.sum_le_sum (fun k _ => χ.norm_le_one _)
        _ = (u : ℝ) := by simp
        _ ≤ (q : ℝ) := by exact_mod_cast hlt.le
    · obtain ⟨v, rfl⟩ : ∃ v, u = v + q := ⟨u - q, by omega⟩
      rw [Finset.sum_range_add, hzero v, add_zero]
      exact ih v (by omega)

/-! ## §2 — VT-7's STONE: the log-shaped upper bound at the bridge point -/

/-- **THE VT-7 STONE** (`norm_LFunction_le_logBound`).  For a NONPRINCIPAL `ψ mod q` and any
`s` with `1 < Re s ≤ 2`,

  `‖L(s, ψ)‖ ≤ 7/2 + log 2 + log q + log(|Im s| + 2)`.

This is the classical `‖L(1+δ+it,χ)‖ ≪ log(q(|t|+2))`, with every constant explicit.  Route:
truncate at `N = ⌈q(|t|+2)⌉` through `Salt.SW.norm_LFunction_sub_partial_le` (whose gate
`0 < Re s` the bridge point clears with room).  The head is a harmonic sum, `≤ 1 + log N ≤
1 + log 2 + log q + log(|t|+2)`; the tail is `q·(1+‖s‖(1+1/Re s))·N^{−Re s} ≤ (5+2|t|)/(|t|+2)
≤ 5/2` — the level `q` supplied by `norm_char_partial_sum_le` cancels against `N`'s own `q`,
which is why NO `√q` and NO `(1 + log q)` factor survives.

Compare `ChiLLower.LFunction_norm_le_level` (`q·3(1+‖s‖)·√q·(1+log q)`): the same object, but
LINEAR in the height, which is what forces `VkTwistClose.chi_Llower_341_height`'s `log T₀`
price and hence the `e^{e^100}` block. -/
theorem norm_LFunction_le_logBound {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re ≤ 2) :
    ‖LFunction ψ s‖ ≤ 7 / 2 + Real.log 2 + Real.log q + Real.log (|s.im| + 2) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · exact absurd (ψ.level_one' (by omega)) hψ
    · exact h
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  set y : ℝ := |s.im| with hydef
  have hy0 : (0 : ℝ) ≤ y := abs_nonneg _
  have hprod2 : (2 : ℝ) ≤ (q : ℝ) * (y + 2) := by nlinarith
  set N : ℕ := ⌈(q : ℝ) * (y + 2)⌉₊ with hNdef
  have hNge : (q : ℝ) * (y + 2) ≤ (N : ℝ) := Nat.le_ceil _
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hNR1
  have hs0 : (0 : ℝ) < s.re := by linarith
  -- the truncation
  have htail := norm_LFunction_sub_partial_le ψ hψ hq2 (norm_char_partial_sum_le ψ hψ) hs0 hN1
  -- the head: a harmonic sum
  have hhead : ‖∑ n ∈ Finset.Icc 1 N, ψ ((n : ℕ) : ZMod q) * (n : ℂ) ^ (-s)‖
      ≤ 1 + Real.log N := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun n hn => ?_)) (Salt.SW.sum_inv_Icc_le N)
    rw [Finset.mem_Icc] at hn
    have hn0 : 0 < n := hn.1
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
    rw [norm_mul, norm_natCast_cpow_of_pos hn0]
    have h1 : ‖ψ ((n : ℕ) : ZMod q)‖ ≤ 1 := ψ.norm_le_one _
    have h2 : ((n : ℝ)) ^ (-s).re ≤ ((n : ℝ))⁻¹ := by
      rw [Complex.neg_re, ← Real.rpow_neg_one (n : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    have h3 : (0 : ℝ) ≤ ((n : ℝ)) ^ (-s).re := Real.rpow_nonneg (by linarith) _
    nlinarith [norm_nonneg (ψ ((n : ℕ) : ZMod q))]
  -- the tail is an absolute constant
  have hsnorm : ‖s‖ ≤ 2 + y := by
    have h := norm_le_abs_re_add_abs_im s
    rw [hydef]
    have : |s.re| = s.re := abs_of_nonneg hs0.le
    linarith [h, this.le, this.ge]
  have hinv : 1 / s.re ≤ 1 := by rw [div_le_one hs0]; linarith
  have hinv0 : (0 : ℝ) ≤ 1 / s.re := by positivity
  have hfac : 1 + ‖s‖ * (1 + 1 / s.re) ≤ 5 + 2 * y := by
    nlinarith [norm_nonneg s]
  have hfac0 : (0 : ℝ) ≤ 1 + ‖s‖ * (1 + 1 / s.re) := by positivity
  have hpow : (N : ℝ) ^ (-s.re) ≤ ((q : ℝ) * (y + 2))⁻¹ := by
    have hstep : (N : ℝ) ^ (-s.re) ≤ (N : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNR1 (by linarith)
    rw [Real.rpow_neg_one] at hstep
    have hstep2 : ((N : ℝ))⁻¹ ≤ ((q : ℝ) * (y + 2))⁻¹ :=
      one_div (N : ℝ) ▸ one_div ((q : ℝ) * (y + 2)) ▸
        one_div_le_one_div_of_le (by linarith) hNge
    linarith
  have hpow0 : (0 : ℝ) ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg hNpos.le _
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hkey : (q : ℝ) * (1 + ‖s‖ * (1 + 1 / s.re)) * (N : ℝ) ^ (-s.re) ≤ 5 / 2 := by
    have hstep : (q : ℝ) * (1 + ‖s‖ * (1 + 1 / s.re)) * (N : ℝ) ^ (-s.re)
        ≤ (q : ℝ) * (5 + 2 * y) * ((q : ℝ) * (y + 2))⁻¹ := by
      gcongr
    have heq : (q : ℝ) * (5 + 2 * y) * ((q : ℝ) * (y + 2))⁻¹ = (5 + 2 * y) / (y + 2) := by
      field_simp
    rw [heq] at hstep
    have hfin : (5 + 2 * y) / (y + 2) ≤ 5 / 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < y + 2)]
      linarith
    linarith
  -- `N ≤ 2q(|t|+2)`
  have hlogN : Real.log N ≤ Real.log 2 + Real.log q + Real.log (y + 2) := by
    have hceil : (N : ℝ) < (q : ℝ) * (y + 2) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h1 : (N : ℝ) ≤ 2 * ((q : ℝ) * (y + 2)) := by linarith
    calc Real.log N ≤ Real.log (2 * ((q : ℝ) * (y + 2))) := Real.log_le_log hNpos h1
      _ = Real.log 2 + Real.log q + Real.log (y + 2) := by
          rw [Real.log_mul (by norm_num) (by positivity),
            Real.log_mul (by positivity) (by positivity)]
          ring
  -- assemble
  have hsplit : ‖LFunction ψ s‖
      ≤ ‖LFunction ψ s - ∑ n ∈ Finset.Icc 1 N, ψ ((n : ℕ) : ZMod q) * (n : ℂ) ^ (-s)‖
        + ‖∑ n ∈ Finset.Icc 1 N, ψ ((n : ℕ) : ZMod q) * (n : ℂ) ^ (-s)‖ := by
    have hid : LFunction ψ s
        = (LFunction ψ s - ∑ n ∈ Finset.Icc 1 N, ψ ((n : ℕ) : ZMod q) * (n : ℂ) ^ (-s))
          + ∑ n ∈ Finset.Icc 1 N, ψ ((n : ℕ) : ZMod q) * (n : ℂ) ^ (-s) := by ring
    calc ‖LFunction ψ s‖ = ‖_ + _‖ := by rw [← hid]
      _ ≤ _ := norm_add_le _ _
  linarith

/-! ## §3 — the mid branch, re-supplied -/

/-- **VT-7 — THE MID BRANCH AT THE LOG PRICE** (`chi_Llower_341_height_sharp`).
`VkTwistClose.chi_Llower_341_height`'s sibling with the growth slot `U` taken from the VT-7
stone instead of `ChiLLower.LFunction_norm_le_level`:

  `−[2log4 + (3/4)log(1+log X) + (1/4)log(7/2 + log 2 + log q + log(2T₀+2))]
      ≤ log‖L(1 + 1/log X − it, χ)‖`   for `|t| ≤ T₀`.

The whole VT-7 gain is the position of `T₀`: the landed form pays `(1/4)·log(3(3+2T₀)q²(1+log q))
≈ (1/4)·T₀`, this one pays `(1/4)·log(log T₀ + …) ≈ (1/4)·log log T₀`.  At `T₀ = exp(exp 100)`
that is `6.7·10^42` against `25.2`. -/
theorem chi_Llower_341_height_sharp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ2 : χ ^ 2 ≠ 1) (X t T₀ : ℝ) (hX : Real.exp 1 ≤ X) (_hT₀ : 1 ≤ T₀) (ht : |t| ≤ T₀) :
    -(2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (7 / 2 + Real.log 2 + Real.log q + Real.log (2 * T₀ + 2)))
      ≤ Real.log ‖DirichletCharacter.LFunction χ
          (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hd0 : (0 : ℝ) < 1 / Real.log X := one_div_pos.mpr hlogXpos
  have hd1 : 1 / Real.log X ≤ 1 := by rw [div_le_one hlogXpos]; linarith
  refine chi_Llower_341_of_ub χ X t _ hX ?_
  have hsre : ((((1 + 1 / Real.log X : ℝ) : ℂ)) - ((2 * t : ℝ) : ℂ) * Complex.I).re
      = 1 + 1 / Real.log X := by simp
  have hsim : ((((1 + 1 / Real.log X : ℝ) : ℂ)) - ((2 * t : ℝ) : ℂ) * Complex.I).im
      = -(2 * t) := by simp
  have h := norm_LFunction_le_logBound (χ ^ 2) hχ2
    (s := (((1 + 1 / Real.log X : ℝ) : ℂ)) - ((2 * t : ℝ) : ℂ) * Complex.I)
    (by rw [hsre]; linarith) (by rw [hsre]; linarith)
  refine le_trans h ?_
  have habs : |((((1 + 1 / Real.log X : ℝ) : ℂ)) - ((2 * t : ℝ) : ℂ) * Complex.I).im|
      = 2 * |t| := by
    rw [hsim, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [habs]
  have hmono : Real.log (2 * |t| + 2) ≤ Real.log (2 * T₀ + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

/-! ## §4 — the sharp mid debit, and the combined `_vt` threshold family -/

/-- **THE SHARP `X`-FREE MID-BRANCH DEBIT** (`vkMidDebitSharp`), at the socket's own height
floor `T₀ = exp(exp 100)`.  `VkTwistClose.vkMidDebit`'s twin with the growth slot re-supplied
from the VT-7 stone.

Numerically: `log(2·exp(exp 100) + 2) = log 2 + e^100` to 43 digits, so the inner argument is
`e^100 + O(1) + log q` and its logarithm is `100` to 43 digits.  Hence
`vkMidDebitSharp q ≈ 2log4 + (3/4)log2 + 25 ≈ 28.3` — against `vkMidDebit q ≈ 6.7·10^42.  Note
where `log q` now sits: INSIDE the outer logarithm, so its threshold weight is `0` where the
landed form's `q²` was worth `16·log q`. -/
def vkMidDebitSharp (q : ℕ) : ℝ :=
  2 * Real.log 4 + (3 / 4) * Real.log 2
    + (1 / 4) * Real.log (7 / 2 + Real.log 2 + Real.log q
        + Real.log (2 * Real.exp (Real.exp 100) + 2))

lemma vkMidDebitSharp_nonneg (q : ℕ) [NeZero q] : 0 ≤ vkMidDebitSharp q := by
  have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1R
  have hE : (1 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have : (0 : ℝ) ≤ Real.exp 100 := (Real.exp_pos 100).le
    calc (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr this
  have hT : (0 : ℝ) ≤ Real.log (2 * Real.exp (Real.exp 100) + 2) :=
    Real.log_nonneg (by linarith)
  have harg : (1 : ℝ) ≤ 7 / 2 + Real.log 2 + Real.log q
      + Real.log (2 * Real.exp (Real.exp 100) + 2) := by linarith
  have := Real.log_nonneg harg
  unfold vkMidDebitSharp; linarith

/-- `VkTwistClose.vk_log_one_add_log_le` is `private`; the same three lines. -/
private lemma vt_log_one_add_log_le {X : ℝ} (hX : Real.exp 1 ≤ X) :
    Real.log (1 + Real.log X) ≤ Real.log 2 + Real.log (Real.log X) := by
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  calc Real.log (1 + Real.log X) ≤ Real.log (2 * Real.log X) :=
        Real.log_le_log (by linarith) (by linarith)
    _ = Real.log 2 + Real.log (Real.log X) := Real.log_mul (by norm_num) (by linarith)

/-- `VkTwistClose.vk_log_two_abs_le` is `private`; the same argument. -/
private lemma vt_log_two_abs_le {X v : ℝ} (hX : Real.exp (Real.exp 1) ≤ X) (hv : |v| ≤ 3 * X) :
    Real.log |2 * v| ≤ 2 * Real.log X := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h6e : (6 : ℝ) < Real.exp 2 := by rw [hsq]; nlinarith [Real.exp_one_gt_d9]
  have hmono : Real.exp 2 ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.mpr he2
  have h6X : (6 : ℝ) ≤ X := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hlog6 : Real.log 6 ≤ Real.log X := Real.log_le_log (by norm_num) h6X
  have hlog6pos : (0 : ℝ) < Real.log 6 := Real.log_pos (by norm_num)
  rcases eq_or_lt_of_le (abs_nonneg (2 * v)) with h0 | h0
  · rw [← h0, Real.log_zero]; linarith
  · have habs : |2 * v| ≤ 6 * X := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; linarith
    calc Real.log |2 * v| ≤ Real.log (6 * X) := Real.log_le_log h0 habs
      _ = Real.log 6 + Real.log X := Real.log_mul (by norm_num) (ne_of_gt hXpos)
      _ ≤ 2 * Real.log X := by linarith

/-- **VT-6's POINTWISE FLOOR, SHARP** (`chi_floor_vk_pointwise_sharp`).
`VkTwistClose.chi_floor_vk_pointwise` with the mid branch re-supplied: `vkMidDebit q` becomes
`vkMidDebitSharp q`.  The VK branch is the landed proof verbatim (`vk_debit_le`). -/
theorem chi_floor_vk_pointwise_sharp :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (C X v : ℝ),
      1 ≤ C → χ ^ 2 ≠ 1 → Real.exp (Real.exp 1) ≤ X → |v| ≤ 3 * X →
      (Real.exp (Real.exp 100) ≤ |v| → VkTwistUB C (χ ^ 2) X (2 * v)) →
        (1 / 16) * Real.log (Real.log X) - Real.log (Real.log (Real.log X))
            - (1 / 8) * Real.log q - vkDebitConst C - vkMidDebitSharp q - K
          ≤ pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨K, hK⟩ := chi_floor_low_of_Llower
  refine ⟨K, ?_⟩
  intro q _ χ C X v hC hχ2 hX hv hsock
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hL : Real.exp 1 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hLpos : (0 : ℝ) < Real.log X := by linarith [Real.exp_pos (1 : ℝ)]
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log X) := by
    have := (Real.le_log_iff_exp_le hLpos).mpr hL
    linarith
  have hlll : (0 : ℝ) ≤ Real.log (Real.log (Real.log X)) := Real.log_nonneg hLL1
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1R
  have hDC : (0 : ℝ) ≤ vkDebitConst C := vkDebitConst_nonneg hC
  have hDM : (0 : ℝ) ≤ vkMidDebitSharp q := vkMidDebitSharp_nonneg q
  by_cases hbig : Real.exp (Real.exp 100) ≤ |v|
  · -- the VK branch (landed verbatim)
    have hlow := chi_Llower_341_vk χ C X v hXe (hsock hbig)
    have hfl := hK q χ X v (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (vkProfile C q (2 * v))) hXe hlow
    have hexp := vk_debit_le (C := C) hC (q := q) (X := X) (t := v) hX hbig
      (vt_log_two_abs_le hX hv)
    linarith
  · -- the MID branch, at the VT-7 price
    have hvT : |v| ≤ Real.exp (Real.exp 100) := (not_le.mp hbig).le
    have hT₀ : (1 : ℝ) ≤ Real.exp (Real.exp 100) := by
      have : (0 : ℝ) ≤ Real.exp 100 := (Real.exp_pos 100).le
      calc (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
        _ ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr this
    have hlow := chi_Llower_341_height_sharp χ hχ2 X v (Real.exp (Real.exp 100)) hXe hT₀ hvT
    have hfl := hK q χ X v (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (7 / 2 + Real.log 2 + Real.log q
            + Real.log (2 * Real.exp (Real.exp 100) + 2))) hXe hlow
    have hone := vt_log_one_add_log_le hXe
    have hmid : 2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (7 / 2 + Real.log 2 + Real.log q
            + Real.log (2 * Real.exp (Real.exp 100) + 2))
        ≤ (3 / 4) * Real.log (Real.log X) + vkMidDebitSharp q := by
      unfold vkMidDebitSharp; linarith
    linarith

/-- **VT-6's CLOSE (the `3X` box), SHARP** — `VkTwistClose.capFreeFloor3_lamChi_vk`'s sibling. -/
theorem capFreeFloor3_lamChi_vk_sharp :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (C X : ℝ),
      1 ≤ C → χ ^ 2 ≠ 1 → Real.exp (Real.exp 1) ≤ X →
      (∀ v : ℝ, |v| ≤ 3 * X → Real.exp (Real.exp 100) ≤ |v| → VkTwistUB C (χ ^ 2) X (2 * v)) →
      32 * (Real.log (Real.log (Real.log X)) + (1 / 8) * Real.log q
            + vkDebitConst C + vkMidDebitSharp q + K + 25) < Real.log (Real.log X) →
        CapFreeFloor3 (lamChi χ) X := by
  obtain ⟨K, hK⟩ := chi_floor_vk_pointwise_sharp
  refine ⟨K, ?_⟩
  intro q _ χ C X hC hχ2 hX hsock hthr v hv
  have hfl := hK q χ C X v hC hχ2 hX hv (fun hb => hsock v hv hb)
  have hmar := vk_capfree_threshold (Real.log (Real.log X))
    (Real.log (Real.log (Real.log X))) (Real.log q) (vkDebitConst C) (vkMidDebitSharp q) K hthr
  linarith

/-- **THE VK-TWIST CAPSTONE, SHARP** — `VkTwistLadder.capFreeFloor3_lamChi_unconditional`'s
sibling: the socket is discharged by `vkTwistUB_holds` exactly as in the landed proof. -/
theorem capFreeFloor3_lamChi_unconditional_sharp :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ),
      χ ^ 2 ≠ 1 → Real.exp (Real.exp 1) ≤ X →
      32 * (Real.log (Real.log (Real.log X)) + (1 / 8) * Real.log q
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q + K + 25)
        < Real.log (Real.log X) →
        CapFreeFloor3 (lamChi χ) X := by
  obtain ⟨K, hK⟩ := capFreeFloor3_lamChi_vk_sharp
  refine ⟨K, ?_⟩
  intro q _ χ X hχ2 hX hthr
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  have hC1 : (1 : ℝ) ≤ vkEulerCorr q * vkTwistConst q := by
    nlinarith [one_le_vkEulerCorr q, one_le_vkTwistConst (q := q)]
  refine hK q χ (vkEulerCorr q * vkTwistConst q) X hC1 hχ2 hX (fun v _hv hbig => ?_) hthr
  have h2v : Real.exp (Real.exp 100) ≤ |2 * v| := by
    have : |v| ≤ |2 * v| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg v]
    linarith
  exact vkTwistUB_holds (χ ^ 2) hχ2 hXe h2v

/-! ### The combined family: ⟦F4⟧ + ⟦VT-7⟧ in one threshold

Every statement below is `CapFreeSharp`'s `_sharp` form with `vkMidDebit q` replaced by
`vkMidDebitSharp q` — i.e. the landed `CapFreeAssembly`/`CofactorSupplier` threshold with BOTH
repairs applied.  Conclusions byte-identical to the landed originals throughout. -/

/-- **THE ASSEMBLED CAP-FREE FLOOR, F4 + VT-7** (`capFreeFloor3_all_chi_vt`). -/
theorem capFreeFloor3_all_chi_vt (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q + K + 25)
        < Real.log (Real.log X) →
        CapFreeFloor3 (lamChi χ) X := by
  obtain ⟨Kvk, hvk⟩ := capFreeFloor3_lamChi_unconditional_sharp
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
  have hvkM : (0 : ℝ) ≤ vkMidDebitSharp q := vkMidDebitSharp_nonneg q
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

/-- **The F4 + VT-7 assembled floor at the `X` box** (`capFreeFloor_all_chi_vt`). -/
theorem capFreeFloor_all_chi_vt (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q + K + 25)
        < Real.log (Real.log X) →
        CapFreeFloor (lamChi χ) X := by
  obtain ⟨K, hK0, hK⟩ := capFreeFloor3_all_chi_vt Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ X hq hX hthr
  obtain ⟨hX8, _, _, _⟩ := cff_scale_facts hX
  exact capFreeFloor_of_capFreeFloor3 (by linarith) (hK q χ X hq hX hthr)

/-- **The F4 + VT-7 assembled constant, named** (`cffKVt`). -/
def cffKVt (Q : ℕ) : ℝ := Classical.choose (capFreeFloor3_all_chi_vt Q)

theorem cffKVt_nonneg (Q : ℕ) : 0 ≤ cffKVt Q :=
  (Classical.choose_spec (capFreeFloor3_all_chi_vt Q)).1

/-- The defining property of `cffKVt` (`cffKSharp_spec`'s sibling). -/
theorem cffKVt_spec (Q : ℕ) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q + cffKVt Q + 25)
        < Real.log (Real.log X) →
        CapFreeFloor3 (lamChi χ) X :=
  (Classical.choose_spec (capFreeFloor3_all_chi_vt Q)).2

/-- **THE F4 + VT-7 FLOOR AT THE ROW'S OWN DATUM** (`capFreeFloor3_liouChi_all_vt`). -/
theorem capFreeFloor3_liouChi_all_vt (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q + K + 25)
        < Real.log (Real.log X) →
        CapFreeFloor3 (liouChi χ) X := by
  obtain ⟨K, hK0, hK⟩ := capFreeFloor3_all_chi_vt Q
  exact ⟨K, hK0, fun q _ χ X hq hX hthr =>
    capFreeFloor3_liouChi_of_lamChi χ (hK q χ X hq hX hthr)⟩

/-- **THE ASSEMBLED χ-FLOOR WITH MARGIN, F4 + VT-7** (`capFreeFloor3_margin_all_chi_vt`). -/
theorem capFreeFloor3_margin_all_chi_vt (Qm : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X D : ℝ), q ≤ Qm →
      Real.exp (Real.exp 1) ≤ X → 0 ≤ D →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q + K + 25 + D)
        < Real.log (Real.log X) →
      ∀ v : ℝ, |v| ≤ 3 * X →
        (1 / 32) * Real.log (Real.log X) + 25 + D < pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨Kvk, hvk⟩ := chi_floor_vk_pointwise_sharp
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
  have hvkM : (0 : ℝ) ≤ vkMidDebitSharp q := vkMidDebitSharp_nonneg q
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

/-- **THE MASKED FLOOR, F4 + VT-7** (`capFreeFloor3_pieceDatum_vt`). -/
theorem capFreeFloor3_pieceDatum_vt (Qm : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X D : ℝ), q ≤ Qm →
      Real.exp (Real.exp 1) ≤ X → 0 ≤ D →
      (∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)) ≤ D →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q + K + 25 + D)
        < Real.log (Real.log X) →
        CapFreeFloor3 (pieceDatum χ 𝒥 Pseq Qseq) X := by
  obtain ⟨K, hK0, hK⟩ := capFreeFloor3_margin_all_chi_vt Qm
  refine ⟨K, hK0, ?_⟩
  intro q _ χ Pseq Qseq 𝒥 X D hq hX hD0 hdebit hthr v hv
  have hmargin := hK q χ X D hq hX hD0 hthr v hv
  have hcw : ∀ p : ℕ, p.Prime → ‖costwist v p‖ ≤ 1 :=
    fun p _ => le_of_eq (costwist_norm v p)
  have htr := pretDistSq_pieceDatum_ge χ Pseq Qseq hcw X 𝒥 (w := costwist v)
  rw [pretDistSq_liouChi_eq] at htr
  linarith

end Salt.MR
