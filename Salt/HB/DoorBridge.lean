/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Transfer
import Salt.HB.L2cER
import Salt.TwinBar.TwinDoor

/-!
# THE DOOR BRIDGE — the N11 half of the fulcrum campaign

THE DOOR BRIDGE — the N11 half of the fulcrum campaign: from HB's own carrier
`S1 (Ioc x (2x))` to the Twin Prime Conjecture, via the landed survivor extraction on
`p1PrimeSum`.  This file supplies the DOOR only: it does not bound `S1` from below (that
is Theorem 1, N9, unbuilt); a positive `S1 − ppTail` at arbitrarily large `x` is its
HYPOTHESIS, not its claim.  Nothing here bears on twin primes.

## The two halves

**(i) The door on the landed carrier.**  `twinPrimeConjecture_of_frequently_pos` — if the
Λ-weighted twin carrier `p1PrimeSum x 1` (`Salt.Chen.TwinDeficit`) is positive at
arbitrarily large `x`, the Twin Prime Conjecture follows.  This is pure plumbing on top of
the landed survivor extraction `Salt.TwinBar.twin_survivor_of_pos`, whose survivor sits at
`n ≥ x / 2`; taking `x ≥ 2N` pushes the survivor past `N`.

**(ii) The carrier bridge.**  HB's carrier is `S1 A = Σ_{n ∈ A} Λ(n)·Λ(n+2)` on the dyadic
window `A = Ioc x (2x)`; salt's landed carrier is `p1PrimeSum (2x+2) 1`, a sum over
`twinWindow (2x+2) = Icc (x+1) (2x)` — the SAME Finset (`twinWindow_two_mul_add_two`).  On
that window the two differ in three ways, all handled by
`S1_Ioc_le_p1PrimeSum_add_ppTail`:

* at a genuine twin `n` the HB weight is `Λ(n)·Λ(n+2) = log n · log(n+2)` while the salt
  weight is `Λ(n)·1·1 = log n` — one logarithm apart, paid by the factor
  `log(2x+2) ≥ log(n+2)`;
* at a non-twin `n` the salt weight is `0`, so the whole HB term is thrown into `ppTail`;
* the coprimality cut `keepR 1` is vacuous (`Nat.Coprime 1 _`), so the salt weight is `1`
  at every twin.

`ppTail` collects exactly the non-twin terms.  A term of it is nonzero only when BOTH `n`
and `n+2` are prime powers and at least one is NOT prime — a proper prime power — so
`ppTail_le` prices it by the landed sparsity count `Salt.HB.properPrimePow_count`.

## Scope fence

The composite `twinPrimeConjecture_of_frequently_S1` has as its HYPOTHESIS a lower bound on
`S1 (Ioc x (2x))` that beats the crude tail `4√(2x+2)·log(2x+2)³` at arbitrarily large `x`.
Nothing in this file supplies such a bound, and nothing here is evidence that one exists.
The hypothesis is exactly HB's Theorem 1 territory (node N9, unbuilt); this file is the
plumbing that would consume it.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction
open Salt.Chen

namespace Salt.HB

/-! ## §1 — the door on the landed twin carrier `p1PrimeSum` -/

/-- **The arbitrarily-large-`x` door.**  If the Λ-weighted twin carrier `p1PrimeSum x 1` is
positive at arbitrarily large `x`, the Twin Prime Conjecture follows.  Given `N`, take
`x ≥ 2N` from the hypothesis; the landed survivor extraction
`Salt.TwinBar.twin_survivor_of_pos` delivers a twin `n ≥ x / 2 ≥ N`.

This is a DOOR, not a theorem about twin primes: its hypothesis is never discharged here. -/
theorem twinPrimeConjecture_of_frequently_pos
    (h : ∀ N : ℕ, ∃ x : ℕ, N ≤ x ∧ 0 < p1PrimeSum x 1) : TwinPrimeConjecture := by
  intro N
  obtain ⟨x, hx, hpos⟩ := h (2 * N)
  obtain ⟨n, hlo, hp, hp2⟩ := Salt.TwinBar.twin_survivor_of_pos hpos
  exact ⟨n, by omega, hp, hp2⟩

/-! ## §2 — the window identification -/

/-- **The two windows coincide.**  `twinWindow (2x+2) = Icc (x+1) (2x) = Ioc x (2x)` — the
salt carrier's window at the shifted argument `2x+2` is literally HB's dyadic window. -/
theorem twinWindow_two_mul_add_two (x : ℕ) :
    twinWindow (2 * x + 2) = Finset.Ioc x (2 * x) := by
  ext n
  rw [twinWindow, Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-! ## §3 — the prime-power tail -/

/-- **The prime-power tail.**  The HB terms on `Ioc x (2x)` at which `(n, n+2)` is NOT a twin
pair.  A term is nonzero only when both `n` and `n+2` are prime powers, and then at least one
of them is a PROPER prime power — hence the sparsity bound `ppTail_le`. -/
noncomputable def ppTail (x : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => ¬ (n.Prime ∧ (n + 2).Prime)), Λ n * Λ (n + 2)

/-- The `n`-side proper-prime-power set on the window — literally the set counted by
`properPrimePow_count`. -/
private def ppLeft (x : ℕ) : Finset ℕ :=
  (Finset.Ioc x (2 * x)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)

/-- The `n+2`-side proper-prime-power set on the window. -/
private def ppRight (x : ℕ) : Finset ℕ :=
  (Finset.Ioc x (2 * x)).filter (fun n => IsPrimePow (n + 2) ∧ ¬ (n + 2).Prime)

/-- The union: every window point that can carry a nonzero `ppTail` term. -/
private def ppBad (x : ℕ) : Finset ℕ := ppLeft x ∪ ppRight x

private lemma ppLeft_card_le (x : ℕ) : (ppLeft x).card ≤ Nat.sqrt (2 * x) :=
  properPrimePow_count x

private lemma ppRight_card_le (x : ℕ) : (ppRight x).card ≤ Nat.sqrt (2 * (x + 1)) := by
  refine le_trans ?_ (properPrimePow_count (x + 1))
  refine Finset.card_le_card_of_injOn (fun n => n + 2) ?_ ?_
  · intro n hn
    have hn' : n ∈ ppRight x := Finset.mem_coe.mp hn
    unfold ppRight at hn'
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn'
    obtain ⟨⟨hlo, hhi⟩, hpp⟩ := hn'
    have : n + 2 ∈ (Finset.Ioc (x + 1) (2 * (x + 1))).filter
        (fun m => IsPrimePow m ∧ ¬ m.Prime) := by
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, by omega⟩, hpp⟩
    exact Finset.mem_coe.mpr this
  · intro a _ b _ hab
    have hab' : a + 2 = b + 2 := hab
    omega

private lemma mem_ppBad_Ioc {x n : ℕ} (h : n ∈ ppBad x) : x < n ∧ n ≤ 2 * x := by
  unfold ppBad at h
  rcases Finset.mem_union.mp h with h | h
  · unfold ppLeft at h; rw [Finset.mem_filter, Finset.mem_Ioc] at h; exact h.1
  · unfold ppRight at h; rw [Finset.mem_filter, Finset.mem_Ioc] at h; exact h.1

/-- Every nonzero `ppTail` term sits on `ppBad`. -/
private lemma ppTail_le_ppBad (x : ℕ) :
    ppTail x ≤ ∑ n ∈ ppBad x, Λ n * Λ (n + 2) := by
  classical
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ Λ n * Λ (n + 2) := fun n =>
    mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg
  have hz : ∀ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => ¬ (n.Prime ∧ (n + 2).Prime)),
      n ∉ ((Finset.Ioc x (2 * x)).filter (fun n => ¬ (n.Prime ∧ (n + 2).Prime))).filter
        (fun n => n ∈ ppBad x) → Λ n * Λ (n + 2) = 0 := by
    intro n hn hnot
    by_contra hne
    refine hnot (Finset.mem_filter.mpr ⟨hn, ?_⟩)
    rw [Finset.mem_filter] at hn
    have hL1 : Λ n ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have hL2 : Λ (n + 2) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hpp1 : IsPrimePow n := vonMangoldt_ne_zero_iff.mp hL1
    have hpp2 : IsPrimePow (n + 2) := vonMangoldt_ne_zero_iff.mp hL2
    unfold ppBad
    refine Finset.mem_union.mpr ?_
    by_cases hp1 : n.Prime
    · right
      unfold ppRight
      exact Finset.mem_filter.mpr ⟨hn.1, hpp2, fun h => hn.2 ⟨hp1, h⟩⟩
    · left
      unfold ppLeft
      exact Finset.mem_filter.mpr ⟨hn.1, hpp1, hp1⟩
  calc ppTail x
      = ∑ n ∈ ((Finset.Ioc x (2 * x)).filter (fun n => ¬ (n.Prime ∧ (n + 2).Prime))).filter
            (fun n => n ∈ ppBad x), Λ n * Λ (n + 2) :=
        (Finset.sum_subset (Finset.filter_subset _ _) hz).symm
    _ ≤ ∑ n ∈ ppBad x, Λ n * Λ (n + 2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hnn n)
        intro n hn
        exact (Finset.mem_filter.mp hn).2

/-- **The tail bound.**  `ppTail x ≤ 4·√(2x+2)·log(2x+2)³`.

The constant is CRUDE BY DESIGN: the honest content is a `√y·log³y`-grade tail against a
main term of `x`-grade, so the numeric factor `4` (and the third power of the logarithm)
buys robustness at no cost to the comparison.  What is actually proved: a nonzero term needs
both `n` and `n+2` to be prime powers with at least one proper, the count of such `n` on
`Ioc x (2x)` is `≤ ⌊√(2x)⌋ + ⌊√(2x+2)⌋ ≤ 2√(2x+2)` (`properPrimePow_count`, twice), and each
term is `≤ log(2x+2)²` (`vonMangoldt_le_log`, twice).  The step from
`2√(2x+2)·log(2x+2)²` to `4√(2x+2)·log(2x+2)³` uses `1 ≤ log(2x+2)`, true for `x ≥ 1`;
`x = 0` has an empty window and is handled separately. -/
theorem ppTail_le (x : ℕ) :
    ppTail x ≤ 4 * Real.sqrt (2 * (x : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2) ^ 3 := by
  classical
  rcases Nat.eq_zero_or_pos x with rfl | hx1
  · have h0 : ppTail 0 = 0 := by
      have : (Finset.Ioc 0 (2 * 0) : Finset ℕ) = ∅ := by decide
      rw [ppTail, this]
      simp
    rw [h0]
    have hlog : (0 : ℝ) ≤ Real.log (2 * ((0 : ℕ) : ℝ) + 2) :=
      Real.log_nonneg (by norm_num)
    exact mul_nonneg (by positivity) (pow_nonneg hlog 3)
  · have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have hL1 : (1 : ℝ) ≤ Real.log (2 * (x : ℝ) + 2) := by
      have hexp : Real.exp 1 ≤ 2 * (x : ℝ) + 2 := by
        have := Real.exp_one_lt_d9
        linarith
      have := Real.log_le_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    have hL0 : (0 : ℝ) ≤ Real.log (2 * (x : ℝ) + 2) := le_trans zero_le_one hL1
    have hS : (0 : ℝ) ≤ Real.sqrt (2 * (x : ℝ) + 2) := Real.sqrt_nonneg _
    -- the termwise cap
    have hterm : ∀ n ∈ ppBad x, Λ n * Λ (n + 2) ≤ Real.log (2 * (x : ℝ) + 2) ^ 2 := by
      intro n hn
      obtain ⟨hlo, hhi⟩ := mem_ppBad_Ioc hn
      have hnR : (n : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hhi
      have hA : Λ n ≤ Real.log (2 * (x : ℝ) + 2) := by
        refine le_trans vonMangoldt_le_log ?_
        have hpos : (0 : ℝ) < (n : ℝ) := by
          have : 0 < n := by omega
          exact_mod_cast this
        exact Real.log_le_log hpos (by linarith)
      have hB : Λ (n + 2) ≤ Real.log (2 * (x : ℝ) + 2) := by
        refine le_trans vonMangoldt_le_log ?_
        have hcast : (((n + 2 : ℕ)) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
        rw [hcast]
        exact Real.log_le_log (by positivity) (by linarith)
      calc Λ n * Λ (n + 2) ≤ Real.log (2 * (x : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2) := by
            exact mul_le_mul hA hB vonMangoldt_nonneg hL0
        _ = Real.log (2 * (x : ℝ) + 2) ^ 2 := by ring
    have hsum : ∑ n ∈ ppBad x, Λ n * Λ (n + 2)
        ≤ ((ppBad x).card : ℝ) * Real.log (2 * (x : ℝ) + 2) ^ 2 := by
      have h := Finset.sum_le_card_nsmul (ppBad x) (fun n => Λ n * Λ (n + 2))
        (Real.log (2 * (x : ℝ) + 2) ^ 2) hterm
      simpa [nsmul_eq_mul] using h
    -- the count
    have hcardN : (ppBad x).card ≤ Nat.sqrt (2 * x) + Nat.sqrt (2 * (x + 1)) := by
      unfold ppBad
      exact le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add (ppLeft_card_le x) (ppRight_card_le x))
    have hcardR : ((ppBad x).card : ℝ) ≤ 2 * Real.sqrt (2 * (x : ℝ) + 2) := by
      have h1 : ((Nat.sqrt (2 * x) : ℕ) : ℝ) ≤ Real.sqrt (2 * (x : ℝ) + 2) := by
        refine le_trans Real.nat_sqrt_le_real_sqrt ?_
        refine Real.sqrt_le_sqrt ?_
        push_cast
        linarith
      have h2 : ((Nat.sqrt (2 * (x + 1)) : ℕ) : ℝ) ≤ Real.sqrt (2 * (x : ℝ) + 2) := by
        refine le_trans Real.nat_sqrt_le_real_sqrt ?_
        refine Real.sqrt_le_sqrt ?_
        push_cast
        linarith
      have := (Nat.cast_le (α := ℝ)).mpr hcardN
      push_cast at this
      linarith
    have hmid : ((ppBad x).card : ℝ) * Real.log (2 * (x : ℝ) + 2) ^ 2
        ≤ 4 * Real.sqrt (2 * (x : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2) ^ 3 := by
      have h23 : Real.log (2 * (x : ℝ) + 2) ^ 2 ≤ Real.log (2 * (x : ℝ) + 2) ^ 3 := by
        nlinarith [sq_nonneg (Real.log (2 * (x : ℝ) + 2))]
      have hstep : ((ppBad x).card : ℝ) * Real.log (2 * (x : ℝ) + 2) ^ 2
          ≤ (2 * Real.sqrt (2 * (x : ℝ) + 2)) * Real.log (2 * (x : ℝ) + 2) ^ 2 :=
        mul_le_mul_of_nonneg_right hcardR (sq_nonneg _)
      have hstep2 : (2 * Real.sqrt (2 * (x : ℝ) + 2)) * Real.log (2 * (x : ℝ) + 2) ^ 2
          ≤ 4 * Real.sqrt (2 * (x : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2) ^ 3 := by
        nlinarith [mul_nonneg hS (sq_nonneg (Real.log (2 * (x : ℝ) + 2))),
          mul_le_mul_of_nonneg_left h23 hS]
      linarith
    exact le_trans (ppTail_le_ppBad x) (le_trans hsum hmid)

/-! ## §4 — the carrier bridge -/

/-- **The carrier bridge.**  On the dyadic window `Ioc x (2x)`, HB's own carrier is dominated
by the landed salt carrier at `2x+2`, one logarithm up, plus the prime-power tail:

`S1 (Ioc x (2x)) ≤ log(2x+2) · p1PrimeSum (2x+2) 1 + ppTail x`.

Proof: split `Ioc x (2x)` by the twin predicate.  The non-twin half IS `ppTail`.  On the twin
half `keepR 1 n = 1` (`Nat.Coprime 1 _`) and `p1Ind (n+2) = 1`, so the salt summand is
`Λ n`, while the HB summand is `Λ n · Λ(n+2) ≤ Λ n · log(2x+2)`; the remaining (nonneg)
window terms only help. -/
theorem S1_Ioc_le_p1PrimeSum_add_ppTail (x : ℕ) :
    S1 (Finset.Ioc x (2 * x))
      ≤ Real.log (2 * (x : ℝ) + 2) * p1PrimeSum (2 * x + 2) 1 + ppTail x := by
  classical
  have hxR : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hL0 : (0 : ℝ) ≤ Real.log (2 * (x : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hsplit : S1 (Finset.Ioc x (2 * x))
      = (∑ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => n.Prime ∧ (n + 2).Prime),
            Λ n * Λ (n + 2)) + ppTail x := by
    rw [S1, ppTail]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hcar : Real.log (2 * (x : ℝ) + 2) * p1PrimeSum (2 * x + 2) 1
      = ∑ n ∈ Finset.Ioc x (2 * x),
          Real.log (2 * (x : ℝ) + 2) * (vonMangoldt n * keepR 1 n * p1Ind (n + 2)) := by
    rw [p1PrimeSum, twinWindow_two_mul_add_two, Finset.mul_sum]
  have hmain : (∑ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => n.Prime ∧ (n + 2).Prime),
        Λ n * Λ (n + 2)) ≤ Real.log (2 * (x : ℝ) + 2) * p1PrimeSum (2 * x + 2) 1 := by
    rw [hcar]
    refine le_trans (Finset.sum_le_sum (fun n hn => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => ?_))
    · rw [Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨⟨hlo, hhi⟩, hp, hp2⟩ := hn
      have hk : keepR 1 n = 1 := keepR_eq_one_iff.mpr ⟨hp, Nat.coprime_one_left _⟩
      have hi : p1Ind (n + 2) = 1 := by unfold p1Ind; rw [if_pos hp2]
      rw [hk, hi, mul_one, mul_one]
      have hnR : (n : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hhi
      have hB : Λ (n + 2) ≤ Real.log (2 * (x : ℝ) + 2) := by
        refine le_trans vonMangoldt_le_log ?_
        have hcast : (((n + 2 : ℕ)) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
        rw [hcast]
        refine Real.log_le_log (by positivity) (by linarith)
      calc Λ n * Λ (n + 2) ≤ Λ n * Real.log (2 * (x : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left hB vonMangoldt_nonneg
        _ = Real.log (2 * (x : ℝ) + 2) * vonMangoldt n := mul_comm _ _
    · exact mul_nonneg hL0
        (mul_nonneg (mul_nonneg vonMangoldt_nonneg (keepR_nonneg 1 n)) (p1Ind_nonneg _))
  linarith

/-! ## §5 — the door at HB's carrier -/

/-- **The door at HB's carrier.**  If the prime-power tail is strictly beaten by `S1` on the
window `Ioc x (2x)`, there is a genuine twin pair `n > x`.  From the carrier bridge the
salt carrier `p1PrimeSum (2x+2) 1` is then strictly positive, and the landed survivor
extraction places its twin at `n ≥ (2x+2)/2 = x+1`.

HYPOTHESIS, not claim: nothing here proves `ppTail x < S1 (Ioc x (2x))` at any `x`. -/
theorem twin_of_ppTail_lt_S1 {x : ℕ} (h : ppTail x < S1 (Finset.Ioc x (2 * x))) :
    ∃ n : ℕ, x < n ∧ n.Prime ∧ (n + 2).Prime := by
  have hb := S1_Ioc_le_p1PrimeSum_add_ppTail x
  have hxR : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hLpos : 0 < Real.log (2 * (x : ℝ) + 2) := Real.log_pos (by linarith)
  have hprod : 0 < Real.log (2 * (x : ℝ) + 2) * p1PrimeSum (2 * x + 2) 1 := by linarith
  have hpos : 0 < p1PrimeSum (2 * x + 2) 1 := by
    rcases lt_or_ge 0 (p1PrimeSum (2 * x + 2) 1) with hc | hc
    · exact hc
    · exact absurd hprod (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hLpos.le hc))
  obtain ⟨n, hlo, hp, hp2⟩ := Salt.TwinBar.twin_survivor_of_pos hpos
  exact ⟨n, by omega, hp, hp2⟩

/-- **The composite door.**  If HB's carrier beats the crude tail `4√(2x+2)·log(2x+2)³` at
arbitrarily large `x`, the Twin Prime Conjecture follows.

R4 tripwire: the antecedent is exactly the unbuilt lower bound (HB's Theorem 1, node N9).
This theorem is the plumbing that would consume it, and is no evidence whatever that such a
bound holds.  Nothing here bears on twin primes. -/
theorem twinPrimeConjecture_of_frequently_S1
    (h : ∀ N : ℕ, ∃ x : ℕ, N ≤ x ∧
      4 * Real.sqrt (2 * (x : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2) ^ 3
        < S1 (Finset.Ioc x (2 * x))) : TwinPrimeConjecture := by
  intro N
  obtain ⟨x, hx, hlt⟩ := h N
  obtain ⟨n, hn, hp, hp2⟩ := twin_of_ppTail_lt_S1 (lt_of_le_of_lt (ppTail_le x) hlt)
  exact ⟨n, by omega, hp, hp2⟩

end Salt.HB
