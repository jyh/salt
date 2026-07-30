/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BV.Defs

/-!
# The effective Liouville summatory rate (Q6a node 2 — the `M_μ → M_λ` fold)

Design: `docs/exploration/q6a-design.md` (D3/D6) and the Q6a-GATE amendment
(`docs/exploration/pilot.md`). The parity wall's analytic input is the effective
*summatory* rate `|M_λ(y)| ≤ C·y/(log y)^A`, sourced (per the amendment) from the
LANDED unconditional ψ-PNT `Salt.BV.siegelWalfisz_psiTot` via two bridge nodes:

* **node 1** (`Mmu_rate`, ψ → M_μ): the effective Tauberian bridge, the classical
  "equivalent forms of PNT" argument made effective. This is the one genuinely deep
  step (the μ ↔ ψ equivalence). Here it is packaged as the clean hypothesis `Prop`
  `MmuRate`, and it is now **LANDED**: `Salt.SW.mmuRate_holds : MmuRate`
  (`Salt/SW/MobiusRateClose.lean` — the `1/ζ` smoothed-Perron contour at
  `log T = (log x)^{1/10}` plus the two-point Riesz de-smoothing). No obstruction
  remains here.
* **node 2** (`Mlambda_rate`, M_μ → M_λ): the *hyperbola fold*. This file LANDS it
  unconditionally-in-`M_μ`: from the exact identity `λ = 1_{squares} ∗ μ`, i.e.
  `M_λ(y) = ∑_{d ≤ √y} M_μ(⌊y/d²⌋)` (`Mlambda_eq_sum_Mmu`, unconditional), the rate
  folds (`Mlambda_rate`): split the `d`-sum at `d ≤ y^{1/4}` (there `log(y/d²) ≥
  (log y)/2`, `∑ 1/d²` converges) versus `d > y^{1/4}` (crude `|M_μ| ≤ y/d²`, tail
  `≤ y^{3/4} = o(y/(log y)^A)`).

So the WALL SHIPS UNCONDITIONALLY: the single clean `MmuRate` Prop is discharged by
`Salt.SW.mmuRate_holds`, and `Salt/TwinBar/WallUnconditional.lean` composes the two
through `LambdaSummatory_of_MmuRate` — a massive improvement over the retired λ-BV
route.

## Naming (Q6a-2 reconciliation)

The parallel `ParityWall.lean` executor defines `Mlambda`. This file defines its own
`Mmu`/`Mlambda` locally (real summatory of `μ`/`λ` over `Finset.Icc 1 y`); Q6a-2
reconciles the two.
-/

open ArithmeticFunction
open scoped BigOperators

namespace Salt.TwinBar

/-! ## The summatory functions and the rate Props -/

/-- The Möbius summatory function `M_μ(y) = ∑_{n ≤ y} μ(n)`, real-valued. -/
noncomputable def Mmu (y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 y, ((ArithmeticFunction.moebius n : ℤ) : ℝ)

/-- The Liouville summatory function `M_λ(y) = ∑_{n ≤ y} λ(n)`, real-valued. -/
noncomputable def Mlambda (y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 y, ((ArithmeticFunction.liouville n : ℤ) : ℝ)

/-- **The effective Möbius summatory rate** (node 1's clean interface).
`|M_μ(y)| ≤ C·y/(log y)^A` for every saving `A > 0`, uniformly for `y` large.
This is the effective Tauberian bridge from the ψ-PNT, and it is **LANDED**:
`Salt.SW.mmuRate_holds : MmuRate` (`Salt/SW/MobiusRateClose.lean`).  Nothing here is
conditional any more; the Prop is kept as the clean interface the fold below reads. -/
def MmuRate : Prop :=
  ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ y : ℕ, x₀ ≤ y →
    |Mmu y| ≤ C * y / (Real.log y) ^ A

/-- **The effective Liouville summatory rate** at a fixed saving `A` — the named form
the parity wall consumes (D3's `LambdaSummatory A` shape). -/
def LambdaSummatory (A : ℝ) : Prop :=
  ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ y : ℕ, x₀ ≤ y →
    |Mlambda y| ≤ C * y / (Real.log y) ^ A

/-! ## The square-indicator arithmetic function and `λ = 1_sq ∗ μ` -/

/-- The indicator of perfect squares as an arithmetic function `ℤ` (with the forced
`0 ↦ 0`). Its Dirichlet series is `ζ(2s)`, and `λ = chiSq ∗ μ`. -/
noncomputable def chiSq : ArithmeticFunction ℤ where
  toFun n := if n ≠ 0 ∧ IsSquare n then (1 : ℤ) else 0
  map_zero' := by simp

lemma chiSq_apply {n : ℕ} (hn : n ≠ 0) :
    chiSq n = if IsSquare n then (1 : ℤ) else 0 := by
  change (if n ≠ 0 ∧ IsSquare n then (1 : ℤ) else 0) = _
  simp [hn]

lemma chiSq_zero : chiSq 0 = 0 := rfl

/-- Coprime square extraction over `ℕ`: if `m*n` is a perfect square and `m, n` are
coprime, then `m` is a perfect square. Proved by lifting to `ℤ` and using the
PID coprime-power extraction. -/
lemma isSquare_of_coprime_mul {m n : ℕ} (hcop : Nat.Coprime m n)
    (h : IsSquare (m * n)) : IsSquare m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; exact ⟨0, by simp⟩
  -- lift to ℤ
  have hcopZ : IsCoprime (m : ℤ) (n : ℤ) := hcop.isCoprime
  obtain ⟨c, hc⟩ := h
  have hZ : (m : ℤ) * (n : ℤ) = (c : ℤ) ^ 2 := by
    have : ((m * n : ℕ) : ℤ) = ((c * c : ℕ) : ℤ) := by exact_mod_cast hc
    push_cast at this ⊢; rw [this]; ring
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hcopZ hZ
  -- Associated (d^2) (m : ℤ) → IsSquare (m : ℤ) → IsSquare m
  rw [Int.associated_iff] at hd
  have hmsqZ : IsSquare (m : ℤ) := by
    rcases hd with hd | hd
    · exact ⟨d, by rw [← hd]; ring⟩
    · -- d^2 = -m with m > 0 is impossible
      exfalso
      have hmpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
      have hnn : (0 : ℤ) ≤ (d : ℤ) ^ 2 := sq_nonneg _
      rw [hd] at hnn
      linarith
  exact (Int.isSquare_natCast_iff).mp hmsqZ

/-- `chiSq` is multiplicative. -/
lemma isMultiplicative_chiSq : chiSq.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · change (if (1 : ℕ) ≠ 0 ∧ IsSquare (1 : ℕ) then (1 : ℤ) else 0) = 1
    rw [if_pos ⟨one_ne_zero, ⟨1, by norm_num⟩⟩]
  · intro m n hcop
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    have hm0 : m ≠ 0 := hm.ne'
    have hn0 : n ≠ 0 := hn.ne'
    have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm0 hn0
    rw [chiSq_apply hm0, chiSq_apply hn0, chiSq_apply hmn0]
    by_cases hsm : IsSquare m
    · by_cases hsn : IsSquare n
      · rw [if_pos hsm, if_pos hsn, if_pos (hsm.mul hsn), mul_one]
      · rw [if_pos hsm, if_neg hsn, mul_zero, if_neg]
        intro hcontra
        exact hsn (isSquare_of_coprime_mul hcop.symm (by rwa [mul_comm] at hcontra))
    · rw [if_neg hsm, zero_mul, if_neg]
      intro hcontra
      exact hsm (isSquare_of_coprime_mul hcop hcontra)

/-- `p^k` is a perfect square iff `k` is even (for `p` prime). -/
lemma isSquare_prime_pow_iff {p : ℕ} (hp : p.Prime) (k : ℕ) :
    IsSquare (p ^ k) ↔ Even k := by
  constructor
  · rintro ⟨r, hr⟩
    have hr2 : r ^ 2 = p ^ k := by rw [sq, ← hr]
    have key : k = 2 * r.factorization p := by
      have e : (p ^ k).factorization p = (r ^ 2).factorization p :=
        congrArg (fun m => m.factorization p) hr2.symm
      rw [Nat.factorization_pow_self hp, Nat.factorization_pow] at e
      simpa using e
    exact ⟨r.factorization p, by omega⟩
  · rintro ⟨m, rfl⟩
    exact ⟨p ^ m, by rw [← pow_add]⟩

/-- **The prime-power value of the convolution `chiSq ∗ μ`.** Only `μ(p^{i-j}) ≠ 0`
for `i - j ∈ {0, 1}` survive, giving `[Even i]·1 + [Even (i-1)]·(-1) = (-1)^i`. -/
lemma chiSq_mul_moebius_prime_pow {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (chiSq * ArithmeticFunction.moebius) (p ^ i) = (-1 : ℤ) ^ i := by
  rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => chiSq a * ArithmeticFunction.moebius b),
      Nat.sum_divisors_prime_pow hp]
  -- reduce `p^i / p^j` to `p^(i-j)`
  have hcong : ∀ j ∈ Finset.range (i + 1),
      chiSq (p ^ j) * ArithmeticFunction.moebius (p ^ i / p ^ j)
        = chiSq (p ^ j) * ArithmeticFunction.moebius (p ^ (i - j)) := by
    intro j hj
    rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hp.pos]
  rw [Finset.sum_congr rfl hcong]
  -- `chiSq (p^j) = if Even j then 1 else 0`
  have hchi : ∀ j : ℕ, chiSq (p ^ j) = if Even j then (1 : ℤ) else 0 := by
    intro j
    rw [chiSq_apply (pow_ne_zero j hp.ne_zero)]
    simp only [isSquare_prime_pow_iff hp]
  simp only [hchi]
  rcases i with _ | i'
  · rw [Finset.sum_range_one, Nat.sub_zero, pow_zero, ArithmeticFunction.moebius_apply_one]
    simp
  · rw [Finset.sum_range_succ, Finset.sum_range_succ]
    -- the bulk sum over `range i'` vanishes (`i - j ≥ 2 ⇒ μ = 0`)
    have hzero : ∑ j ∈ Finset.range i',
        (if Even j then (1 : ℤ) else 0) * ArithmeticFunction.moebius (p ^ (i' + 1 - j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' : j < i' := Finset.mem_range.mp hj
      have hmz : ArithmeticFunction.moebius (p ^ (i' + 1 - j)) = 0 := by
        rw [ArithmeticFunction.moebius_apply_prime_pow hp (show i' + 1 - j ≠ 0 by omega),
            if_neg (show ¬ (i' + 1 - j = 1) by omega)]
      rw [hmz, mul_zero]
    rw [hzero, zero_add]
    have he1 : i' + 1 - i' = 1 := by omega
    have he0 : i' + 1 - (i' + 1) = 0 := by omega
    rw [he1, he0, pow_zero, ArithmeticFunction.moebius_apply_one,
        ArithmeticFunction.moebius_apply_prime_pow hp one_ne_zero, if_pos rfl]
    by_cases hev : Even i'
    · have hodd : Odd (i' + 1) := Nat.not_even_iff_odd.mp (fun h => (Nat.even_add_one.mp h) hev)
      rw [if_pos hev, if_neg (fun h => (Nat.even_add_one.mp h) hev), Odd.neg_one_pow hodd]
      ring
    · have heven : Even (i' + 1) := Nat.even_add_one.mpr hev
      rw [if_neg hev, if_pos heven, Even.neg_one_pow heven]
      ring

/-- **The pointwise identity `λ = 1_{squares} ∗ μ`** (as arithmetic functions `ℤ`). -/
lemma liouville_eq_chiSq_mul_moebius :
    (ArithmeticFunction.liouville : ArithmeticFunction ℤ)
      = chiSq * ArithmeticFunction.moebius := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
        ArithmeticFunction.liouville ArithmeticFunction.isMultiplicative_liouville
        (chiSq * ArithmeticFunction.moebius)
        (isMultiplicative_chiSq.mul ArithmeticFunction.isMultiplicative_moebius)]
  intro p i hp
  rw [ArithmeticFunction.liouville_apply (pow_ne_zero i hp.ne_zero),
      ArithmeticFunction.cardFactors_apply_prime_pow hp, chiSq_mul_moebius_prime_pow hp]

/-! ## The summatory hyperbola fold `M_λ(y) = ∑_{d ≤ √y} M_μ(⌊y/d²⌋)` -/

/-- For a perfect square `a`, `(√a)² = a`. -/
lemma natSqrt_sq_of_isSquare {a : ℕ} (h : IsSquare a) : (Nat.sqrt a) ^ 2 = a := by
  obtain ⟨r, rfl⟩ := h
  rw [Nat.sqrt_eq, sq]

/-- **The pointwise identity in `d`-form**: for `1 ≤ n ≤ y`,
`λ(n) = ∑_{d ≤ y, d² ∣ n} μ(n/d²)`. (The ambient `Icc 1 y` captures every `d` with
`d² ∣ n`, since such `d ≤ √n ≤ y`.) -/
lemma liouville_eq_sum_moebius {n y : ℕ} (hn1 : 1 ≤ n) (hny : n ≤ y) :
    (ArithmeticFunction.liouville n : ℤ)
      = ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ^ 2 ∣ n),
          ArithmeticFunction.moebius (n / d ^ 2) := by
  have hn0 : n ≠ 0 := by omega
  have hfun : ArithmeticFunction.liouville n = (chiSq * ArithmeticFunction.moebius) n := by
    rw [liouville_eq_chiSq_mul_moebius]
  rw [hfun, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => chiSq a * ArithmeticFunction.moebius b)]
  -- Move 1: only the square divisors survive
  have hM1 : ∑ a ∈ n.divisors, chiSq a * ArithmeticFunction.moebius (n / a)
      = ∑ a ∈ n.divisors.filter (fun a => IsSquare a), ArithmeticFunction.moebius (n / a) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    have ha0 : a ≠ 0 := by
      rw [Nat.mem_divisors] at ha; rintro rfl; exact ha.2 (Nat.eq_zero_of_zero_dvd ha.1)
    rw [chiSq_apply ha0]
    split_ifs <;> ring
  rw [hM1]
  -- Move 2: reindex the square divisors `a = d²`
  refine Finset.sum_bij' (fun a _ => Nat.sqrt a) (fun d _ => d ^ 2) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors] at ha
    obtain ⟨⟨hadvd, _⟩, hasq⟩ := ha
    have hsq : (Nat.sqrt a) ^ 2 = a := natSqrt_sq_of_isSquare hasq
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · exact absurd (Nat.eq_zero_of_zero_dvd hadvd) hn0
      · exact h
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have : 1 ≤ (Nat.sqrt a) ^ 2 := by rw [hsq]; exact ha1
      nlinarith [Nat.sqrt_le_self a]
    · exact le_trans (Nat.sqrt_le_self a) (le_trans (Nat.le_of_dvd (by omega) hadvd) hny)
    · rw [hsq]; exact hadvd
  · intro d hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, _⟩, hddvd⟩ := hd
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hddvd, hn0⟩, ⟨d, sq d⟩⟩
  · intro a ha
    rw [Finset.mem_filter] at ha
    exact natSqrt_sq_of_isSquare ha.2
  · intro d hd
    exact Nat.sqrt_eq' d
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [natSqrt_sq_of_isSquare ha.2]

/-- **The inner multiples bijection**: `∑_{n ≤ y, d² ∣ n} μ(n/d²) = M_μ(⌊y/d²⌋)` (real). -/
lemma Mmu_inner (y d : ℕ) (hd : 1 ≤ d) :
    ∑ n ∈ (Finset.Icc 1 y).filter (fun n => d ^ 2 ∣ n),
        ((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℝ) = Mmu (y / d ^ 2) := by
  have hd2 : 0 < d ^ 2 := by positivity
  unfold Mmu
  refine Finset.sum_bij' (fun n _ => n / d ^ 2) (fun m _ => d ^ 2 * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hny⟩, hdvd⟩ := hn
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff hd2).mpr (Nat.le_of_dvd (by omega) hdvd),
           Nat.div_le_div_right hny⟩
  · intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hmy⟩ := hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · exact Nat.mul_pos hd2 (by omega)
    · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd2).mp hmy
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _
    exact Nat.mul_div_cancel_left m hd2
  · intro n _
    rfl

/-- **The hyperbola fold identity (unconditional)**: `M_λ(y) = ∑_{d ≤ √y} M_μ(⌊y/d²⌋)`.
This is node 2's exact combinatorial core: `λ = 1_{squares} ∗ μ` summed. -/
lemma Mlambda_eq_sum_Mmu (y : ℕ) :
    Mlambda y = ∑ d ∈ Finset.Icc 1 (Nat.sqrt y), Mmu (y / d ^ 2) := by
  -- expand `M_λ` and substitute the pointwise `d`-form identity (cast to ℝ)
  have hpt : ∀ n ∈ Finset.Icc 1 y, ((ArithmeticFunction.liouville n : ℤ) : ℝ)
      = ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ^ 2 ∣ n),
          ((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℝ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [liouville_eq_sum_moebius hn.1 hn.2, Int.cast_sum]
  unfold Mlambda
  rw [Finset.sum_congr rfl hpt]
  -- inner filter → ite over the ambient `Icc 1 y`
  have hstep1 : ∀ n : ℕ, ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ^ 2 ∣ n),
        ((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℝ)
      = ∑ d ∈ Finset.Icc 1 y,
          (if d ^ 2 ∣ n then ((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℝ) else 0) := by
    intro n; rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun n _ => hstep1 n), Finset.sum_comm]
  -- inner ite → filter over `n`, then collapse via `Mmu_inner`
  have hstep2 : ∀ d ∈ Finset.Icc 1 y,
        ∑ n ∈ Finset.Icc 1 y,
          (if d ^ 2 ∣ n then ((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℝ) else 0)
      = Mmu (y / d ^ 2) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [← Finset.sum_filter]
    exact Mmu_inner y d hd.1
  rw [Finset.sum_congr rfl hstep2]
  -- trim `Icc 1 y` down to `Icc 1 (√y)` (`d > √y ⇒ ⌊y/d²⌋ = 0 ⇒ M_μ = 0`)
  refine (Finset.sum_subset ?_ ?_).symm
  · intro d hd
    rw [Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, le_trans hd.2 (Nat.sqrt_le_self y)⟩
  · intro d hd hd'
    rw [Finset.mem_Icc] at hd
    have hdgt : Nat.sqrt y < d := by
      by_contra h
      exact hd' (Finset.mem_Icc.mpr ⟨hd.1, Nat.not_lt.mp h⟩)
    have hlt : y < d ^ 2 := Nat.sqrt_lt'.mp hdgt
    rw [Nat.div_eq_of_lt hlt]
    simp [Mmu]

/-! ## The analytic rate fold `M_μ-rate ⇒ M_λ-rate` -/

/-- **Crude bound** `|M_μ(y)| ≤ y` (from `|μ(n)| ≤ 1`). -/
lemma Mmu_abs_le (y : ℕ) : |Mmu y| ≤ (y : ℝ) := by
  unfold Mmu
  calc |∑ n ∈ Finset.Icc 1 y, ((ArithmeticFunction.moebius n : ℤ) : ℝ)|
      ≤ ∑ n ∈ Finset.Icc 1 y, |((ArithmeticFunction.moebius n : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 y, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        calc |((ArithmeticFunction.moebius n : ℤ) : ℝ)|
            = ((|ArithmeticFunction.moebius n| : ℤ) : ℝ) := by rw [Int.cast_abs]
          _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          _ = 1 := by norm_num
    _ = (y : ℝ) := by rw [Finset.sum_const, Nat.card_Icc]; simp

/-- `∑_{d ≤ q} 1/d² ≤ 2`. -/
lemma sum_inv_sq_Icc_le (q : ℕ) : ∑ d ∈ Finset.Icc 1 q, ((d : ℝ) ^ 2)⁻¹ ≤ 2 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have hsplit : Finset.Icc 1 q = insert 1 (Finset.Ioc 1 q) := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have h1 : (((1 : ℕ) : ℝ) ^ 2)⁻¹ = 1 := by norm_num
    rw [h1]
    have hsub := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := q) one_ne_zero hq
    rw [Nat.cast_one, inv_one] at hsub
    have hqinv : 0 ≤ (q : ℝ)⁻¹ := by positivity
    linarith

/-- `∑_{q < d ≤ N} 1/d² ≤ 1/q` (telescoping tail). -/
lemma sum_inv_sq_Ioc_le {q N : ℕ} (hq : 1 ≤ q) (hqN : q ≤ N) :
    ∑ d ∈ Finset.Ioc q N, ((d : ℝ) ^ 2)⁻¹ ≤ (q : ℝ)⁻¹ := by
  have hsub := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := q) (n := N) (by omega) hqN
  have : 0 ≤ (N : ℝ)⁻¹ := by positivity
  linarith

/-- **`log √y ≥ (log y)/4` for `y ≥ 16`** (via `Nat.sqrt y ≥ √y/2`). -/
lemma log_natSqrt_ge {y : ℕ} (hy : 16 ≤ y) :
    Real.log y / 4 ≤ Real.log (Nat.sqrt y) := by
  have hy16 : (16 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hsqrt : Real.sqrt y < (Nat.sqrt y : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hsqy : (4 : ℝ) ≤ Real.sqrt y := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt hy16
  have hs_gt : Real.sqrt y - 1 < (Nat.sqrt y : ℝ) := by linarith
  have hhalf : Real.sqrt y / 2 ≤ (Nat.sqrt y : ℝ) := by linarith
  have hspos : (0 : ℝ) < (Nat.sqrt y : ℝ) := by linarith
  have hlog_s : Real.log (Real.sqrt y / 2) ≤ Real.log (Nat.sqrt y) :=
    Real.log_le_log (by positivity) hhalf
  have hlog_div : Real.log (Real.sqrt y / 2) = Real.log y / 2 - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hy0.le]
  have hlog2 : Real.log 2 ≤ Real.log y / 4 := by
    have hle : Real.log 16 ≤ Real.log y := Real.log_le_log (by norm_num) hy16
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at hle
    push_cast at hle
    linarith
  linarith

/-- `K⁴ ≤ y ⇒ K ≤ √√y` (two applications of `Nat.le_sqrt`). -/
lemma le_sqrt_sqrt_of_pow4_le {y K : ℕ} (h : K ^ 4 ≤ y) :
    K ≤ Nat.sqrt (Nat.sqrt y) := by
  rw [Nat.le_sqrt, Nat.le_sqrt]
  calc K * K * (K * K) = K ^ 4 := by ring
    _ ≤ y := h

/-- **The eventual power bound** `(log y)^A + 1)⁴ ≤ y` (from `(log)^A = o(y^{1/8})`). -/
lemma eventually_pow4_le (A : ℝ) :
    ∀ᶠ y : ℕ in Filter.atTop, ((Real.log y) ^ A + 1) ^ 4 ≤ (y : ℝ) := by
  have hlo := isLittleO_log_rpow_rpow_atTop (s := (1 / 8 : ℝ)) A (by norm_num)
  have hreal : ∀ᶠ x : ℝ in Filter.atTop, ((Real.log x) ^ A + 1) ^ 4 ≤ x := by
    filter_upwards [hlo.eventuallyLE, Filter.eventually_ge_atTop (256 : ℝ)] with x hxb hx256
    have hx0 : (0 : ℝ) < x := by linarith
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hlogA_nn : 0 ≤ (Real.log x) ^ A := Real.rpow_nonneg (Real.log_nonneg hx1) A
    have h18_nn : 0 ≤ x ^ (1 / 8 : ℝ) := Real.rpow_nonneg hx0.le _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogA_nn,
        abs_of_nonneg h18_nn] at hxb
    have hu : (2 : ℝ) ≤ x ^ (1 / 8 : ℝ) := by
      have h256 : (256 : ℝ) ^ (1 / 8 : ℝ) = 2 := by
        rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 8,
            ← Real.rpow_mul (by norm_num)]
        norm_num
      calc (2 : ℝ) = (256 : ℝ) ^ (1 / 8 : ℝ) := h256.symm
        _ ≤ x ^ (1 / 8 : ℝ) := Real.rpow_le_rpow (by norm_num) hx256 (by norm_num)
    have hquarter : x ^ (1 / 4 : ℝ) = (x ^ (1 / 8 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast (x ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul hx0.le]; norm_num
    have hsum : (Real.log x) ^ A + 1 ≤ x ^ (1 / 4 : ℝ) := by
      rw [hquarter]; nlinarith [hxb, hu]
    have hx4 : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
      rw [← Real.rpow_natCast (x ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul hx0.le]; norm_num
    calc ((Real.log x) ^ A + 1) ^ 4 ≤ (x ^ (1 / 4 : ℝ)) ^ 4 := by gcongr
      _ = x := hx4
  exact tendsto_natCast_atTop_atTop.eventually hreal

/-- **Node 2 — the effective rate fold.** From the effective Möbius summatory rate
`MmuRate`, the Liouville summatory inherits the same power-log rate:
`|M_λ(y)| ≤ C·y/(log y)^A` for every `A > 0`, uniformly for `y` large.

Proof: from the unconditional identity `M_λ(y) = ∑_{d ≤ √y} M_μ(⌊y/d²⌋)`, split the
`d`-sum at `d ≤ √√y ≈ y^{1/4}`. On the small range `log(⌊y/d²⌋) ≥ log √y ≥ (log y)/4`
and `∑ 1/d² ≤ 2`, giving `≤ 2C·4^A·y/(log y)^A`. On the tail `|M_μ| ≤ ⌊y/d²⌋ ≤ y/d²`
and `∑_{d>√√y} 1/d² ≤ 1/√√y ≤ 1/(log y)^A`, giving `≤ y/(log y)^A`. -/
theorem Mlambda_rate (hMmu : MmuRate) (A : ℝ) (hA : 0 < A) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ y : ℕ, x₀ ≤ y →
      |Mlambda y| ≤ C * y / (Real.log y) ^ A := by
  obtain ⟨C, x₀mu, hCpos, hMmuBound⟩ := hMmu A hA
  have h4A : (0 : ℝ) < (4 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have hC'pos : (0 : ℝ) < 2 * C * (4 : ℝ) ^ A + 1 := by
    have h := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hCpos) h4A
    linarith
  -- build the bound as an eventual statement, then extract the threshold
  have key : ∀ᶠ y : ℕ in Filter.atTop,
      |Mlambda y| ≤ (2 * C * (4 : ℝ) ^ A + 1) * y / (Real.log y) ^ A := by
    filter_upwards [eventually_pow4_le A, Filter.eventually_ge_atTop 16,
        Filter.eventually_ge_atTop (x₀mu ^ 2)] with y hpow4 hy16 hyx0
    have hLpos : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
    have hs1 : 1 ≤ Nat.sqrt y := Nat.le_sqrt.mpr (by nlinarith [hy16])
    have hq_le_s : Nat.sqrt (Nat.sqrt y) ≤ Nat.sqrt y := Nat.sqrt_le_self _
    have hq1 : 1 ≤ Nat.sqrt (Nat.sqrt y) := Nat.le_sqrt.mpr (by nlinarith [hs1])
    have hs_ge_x0 : x₀mu ≤ Nat.sqrt y := by
      rw [Nat.le_sqrt]; calc x₀mu * x₀mu = x₀mu ^ 2 := by ring
        _ ≤ y := hyx0
    have hlogs : Real.log y / 4 ≤ Real.log (Nat.sqrt y) := log_natSqrt_ge hy16
    -- `(log y)^A ≤ √√y`
    have hlogAq : (Real.log y) ^ A ≤ (Nat.sqrt (Nat.sqrt y) : ℝ) := by
      have hLA_le_K : (Real.log y) ^ A ≤ (Nat.ceil ((Real.log y) ^ A) : ℝ) := Nat.le_ceil _
      have hK_le : (Nat.ceil ((Real.log y) ^ A) : ℝ) ≤ (Real.log y) ^ A + 1 :=
        (Nat.ceil_lt_add_one (Real.rpow_nonneg hLpos.le A)).le
      have hK4 : Nat.ceil ((Real.log y) ^ A) ^ 4 ≤ y := by
        have hle : ((Nat.ceil ((Real.log y) ^ A) : ℝ)) ^ 4 ≤ (y : ℝ) :=
          le_trans (by gcongr) hpow4
        exact_mod_cast hle
      calc (Real.log y) ^ A ≤ (Nat.ceil ((Real.log y) ^ A) : ℝ) := hLA_le_K
        _ ≤ (Nat.sqrt (Nat.sqrt y) : ℝ) := by exact_mod_cast le_sqrt_sqrt_of_pow4_le hK4
    -- expand and split the sum
    rw [Mlambda_eq_sum_Mmu]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hdisj : Disjoint (Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)))
        (Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y)) := by
      rw [Finset.disjoint_left]; intro a ha hb
      rw [Finset.mem_Icc] at ha; rw [Finset.mem_Ioc] at hb; omega
    have hIccsplit : Finset.Icc 1 (Nat.sqrt y)
        = Finset.Icc 1 (Nat.sqrt (Nat.sqrt y))
          ∪ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y) := by
      ext a; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
    rw [hIccsplit, Finset.sum_union hdisj]
    -- small range
    have hsmall : ∑ d ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)), |Mmu (y / d ^ 2)|
        ≤ 2 * C * (4 : ℝ) ^ A * y / (Real.log y) ^ A := by
      have key_d : ∀ d ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)),
          |Mmu (y / d ^ 2)| ≤ C * (4 : ℝ) ^ A * y / (Real.log y) ^ A * ((d : ℝ) ^ 2)⁻¹ := by
        intro d hd
        rw [Finset.mem_Icc] at hd
        obtain ⟨hd1, hdq⟩ := hd
        have hd2s : d ^ 2 ≤ Nat.sqrt y :=
          le_trans (Nat.pow_le_pow_left hdq 2) (Nat.sqrt_le' (Nat.sqrt y))
        have hts : Nat.sqrt y ≤ y / d ^ 2 := by
          rw [Nat.le_div_iff_mul_le (show 0 < d ^ 2 by positivity)]
          calc Nat.sqrt y * d ^ 2 ≤ Nat.sqrt y * Nat.sqrt y := by gcongr
            _ ≤ y := Nat.sqrt_le y
        have htx : x₀mu ≤ y / d ^ 2 := le_trans hs_ge_x0 hts
        have hMt := hMmuBound (y / d ^ 2) htx
        have hlogt : Real.log y / 4 ≤ Real.log ((y / d ^ 2 : ℕ) : ℝ) := by
          refine le_trans hlogs ?_
          apply Real.log_le_log (by exact_mod_cast (by omega : 0 < Nat.sqrt y))
          exact_mod_cast hts
        have hL4pos : 0 < Real.log y / 4 := by linarith
        have hrpow : (Real.log y / 4) ^ A ≤ (Real.log ((y / d ^ 2 : ℕ) : ℝ)) ^ A :=
          Real.rpow_le_rpow hL4pos.le hlogt hA.le
        calc |Mmu (y / d ^ 2)|
            ≤ C * ((y / d ^ 2 : ℕ) : ℝ) / (Real.log ((y / d ^ 2 : ℕ) : ℝ)) ^ A := hMt
          _ ≤ C * ((y / d ^ 2 : ℕ) : ℝ) / (Real.log y / 4) ^ A :=
                div_le_div_of_nonneg_left (mul_nonneg hCpos.le (Nat.cast_nonneg _))
                  (Real.rpow_pos_of_pos hL4pos A) hrpow
          _ = C * ((y / d ^ 2 : ℕ) : ℝ) * (4 : ℝ) ^ A / (Real.log y) ^ A := by
                rw [Real.div_rpow hLpos.le (by norm_num), div_div_eq_mul_div]
          _ ≤ C * (4 : ℝ) ^ A * y / (Real.log y) ^ A * ((d : ℝ) ^ 2)⁻¹ := by
                have hcast : ((y / d ^ 2 : ℕ) : ℝ) ≤ (y : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
                  have h := Nat.cast_div_le (m := y) (n := d ^ 2) (α := ℝ)
                  rwa [Nat.cast_pow, div_eq_mul_inv] at h
                have hCoef : (0 : ℝ) ≤ C * (4 : ℝ) ^ A / (Real.log y) ^ A :=
                  div_nonneg (mul_nonneg hCpos.le (Real.rpow_nonneg (by norm_num) A))
                    (Real.rpow_nonneg hLpos.le A)
                calc C * ((y / d ^ 2 : ℕ) : ℝ) * (4 : ℝ) ^ A / (Real.log y) ^ A
                    = (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * ((y / d ^ 2 : ℕ) : ℝ) := by ring
                  _ ≤ (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * ((y : ℝ) * ((d : ℝ) ^ 2)⁻¹) :=
                        mul_le_mul_of_nonneg_left hcast hCoef
                  _ = C * (4 : ℝ) ^ A * y / (Real.log y) ^ A * ((d : ℝ) ^ 2)⁻¹ := by ring
      calc ∑ d ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)), |Mmu (y / d ^ 2)|
          ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)),
              C * (4 : ℝ) ^ A * y / (Real.log y) ^ A * ((d : ℝ) ^ 2)⁻¹ :=
            Finset.sum_le_sum key_d
        _ = (C * (4 : ℝ) ^ A * y / (Real.log y) ^ A) *
              ∑ d ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)), ((d : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
        _ ≤ (C * (4 : ℝ) ^ A * y / (Real.log y) ^ A) * 2 :=
              mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le _)
                (div_nonneg (mul_nonneg (mul_nonneg hCpos.le h4A.le) (Nat.cast_nonneg _))
                  (Real.rpow_nonneg hLpos.le A))
        _ = 2 * C * (4 : ℝ) ^ A * y / (Real.log y) ^ A := by ring
    -- tail range
    have hlarge : ∑ d ∈ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y), |Mmu (y / d ^ 2)|
        ≤ (y : ℝ) / (Real.log y) ^ A := by
      have hbd : ∀ d ∈ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y),
          |Mmu (y / d ^ 2)| ≤ (y : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
        intro d _
        calc |Mmu (y / d ^ 2)| ≤ ((y / d ^ 2 : ℕ) : ℝ) := Mmu_abs_le _
          _ ≤ (y : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
                have h := Nat.cast_div_le (m := y) (n := d ^ 2) (α := ℝ)
                rwa [Nat.cast_pow, div_eq_mul_inv] at h
      calc ∑ d ∈ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y), |Mmu (y / d ^ 2)|
          ≤ ∑ d ∈ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y), (y : ℝ) * ((d : ℝ) ^ 2)⁻¹ :=
            Finset.sum_le_sum hbd
        _ = (y : ℝ) * ∑ d ∈ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y), ((d : ℝ) ^ 2)⁻¹ := by
              rw [Finset.mul_sum]
        _ ≤ (y : ℝ) * (Nat.sqrt (Nat.sqrt y) : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_left (sum_inv_sq_Ioc_le hq1 hq_le_s) (Nat.cast_nonneg _)
        _ ≤ (y : ℝ) / (Real.log y) ^ A := by
              rw [div_eq_mul_inv]
              have hLA : (0 : ℝ) < (Real.log y) ^ A := Real.rpow_pos_of_pos hLpos A
              have hinv : (Nat.sqrt (Nat.sqrt y) : ℝ)⁻¹ ≤ ((Real.log y) ^ A)⁻¹ := by
                gcongr
              exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
    calc ∑ d ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)), |Mmu (y / d ^ 2)|
          + ∑ d ∈ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y), |Mmu (y / d ^ 2)|
        ≤ 2 * C * (4 : ℝ) ^ A * y / (Real.log y) ^ A + (y : ℝ) / (Real.log y) ^ A :=
          add_le_add hsmall hlarge
      _ = (2 * C * (4 : ℝ) ^ A + 1) * y / (Real.log y) ^ A := by ring
  rw [Filter.eventually_atTop] at key
  obtain ⟨N, hN⟩ := key
  exact ⟨2 * C * (4 : ℝ) ^ A + 1, N, hC'pos, hN⟩

/-- **The `LambdaSummatory A` discharge** (D3's shape the wall consumes): the effective
Möbius rate `MmuRate` implies the effective Liouville summatory rate at every `A`. -/
theorem LambdaSummatory_of_MmuRate (hMmu : MmuRate) (A : ℝ) (hA : 0 < A) :
    LambdaSummatory A :=
  Mlambda_rate hMmu A hA

end Salt.TwinBar
