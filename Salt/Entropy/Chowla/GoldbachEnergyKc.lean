/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦ROUTE 1 — THE `Kc` CEILING AT ITS LEAF⟧ (NUMERAL wave)

`S16Uniform`'s flat head pins `ε := 1/500` LITERALLY and then opens
`bigXi_bounded ε _ _`, whose `∃ C, 0 < C ∧ …` exports POSITIVITY ONLY.  The
terminal's first inner rider `Kc ≤ 2^539` is therefore a rider only because the
count constant is opaque at the `∃`, not because it is large: at the pinned `ε`
the corpus already has the count with the constant IN THE STATEMENT
(`bigXi_bounded_500`), and the sole remaining opacity is the `∃ K` of
`hFac2_lcm_sum_le`, whose witness is the closed form `exp(24·ζ(2)) = exp(4π²)`.

This file closes that last gap ADDITIVELY, without touching one landed
declaration and without a full-corpus rebuild:

* `hFac2_lcm_sum_le_exp40` — GB-14b's double sum bounded by the NUMERAL
  `exp 40`.  The proof is `hFac2_lcm_sum_le`'s own body, replayed verbatim
  against the same (private) per-prime machinery via `open private`, with the
  terminal `exp(24·ζ(2)) ≤ exp 40` step supplied by mathlib's
  `hasSum_zeta_two` (`ζ(2) = π²/6`, the `ℕ`-indexed tsum, the `n = 0` term
  being `1/0 = 0`) and `Real.pi_lt_d6`: `24·ζ(2) = 4π² ≤ 4·(3.141593)² < 40`.
* `hFac2_lcm_sum_le_bounded` — the pinned twin of `hFac2_lcm_sum_le`, with the
  ceiling as a conjunct (witness `K := exp 40`, so the ceiling is `le_rfl`).
* `bigXi_bounded_500_explicit40` — `bigXi_bounded_explicit` at
  `C₁ = 2^35`, `K = exp 40`, `ε = 1/500`, i.e. the count with a fully NUMERIC
  constant `32·exp 40·(2^35)²·500^10`.
* `bigXi_bounded_500_ceiling` / `bigXi_bounded_ceiling_of_pin` — the drop-in
  replacement for `bigXi_bounded ε _ _` at the pinned `ε`, carrying
  `C ≤ 2^539` as one extra conjunct.  THIS IS THE COMPOSE PASS'S HOOK.

⟦THE ARITHMETIC, HONEST⟧ `exp 40 ≤ 3^40` (from `Real.exp_one_lt_d9`), so the
exported ceiling is at most `2^5 · 3^40 · 2^70 · 500^10 ≈ 4.5·10^68 = 2^228.2`
— against the asked `2^539` that is ~310 bits of room.  (The sharp figure with
`exp 40 ≈ 2.35·10^17` is `2^221.7`; the `3^40` slack costs 6.5 bits and buys a
one-line `norm_num`.)

No `sorry`, no `native_decide`, no new axioms.
-/
import Mathlib
import Salt.Entropy.Chowla.GoldbachEnergyHsq2
import Salt.Entropy.Chowla.GoldbachEnergyN0

open Finset
open scoped BigOperators Pointwise

open private u2 v2 G2 doubleSum2_eq_prod prod_L2_le_exp G2_nonneg cast_lcm_eq_prod2
  from Salt.Entropy.Chowla.GoldbachEnergyHsq2

-- ⟦BYTE-FAITHFUL REPLAY⟧ every proof body below is the landed proof, copied verbatim so
-- that the twin is auditable against its original line for line; the long lines are the
-- originals' own, and reflowing them would destroy exactly the property that makes the
-- replay checkable.  (Same device as `Salt/Chen/SuperPanelsO.lean`.)
set_option linter.style.longLine false

namespace Salt.Entropy.Chowla

/-! ## §1 — the GB-14b majorant at a NUMERAL -/

/-- **⟦THE LEAF NUMERAL⟧** (`hFac2_lcm_sum_le_exp40`).  GB-14b's doubled
Euler-product majorant with the constant IN THE STATEMENT: the double sum over
odd squarefree `d₁, d₂ ≤ X` of `hFac2 d₁ · hFac2 d₂ / lcm(d₁,d₂)` is at most
`exp 40`, uniformly in `X`.

Body: `hFac2_lcm_sum_le`'s, verbatim (same private per-prime machinery), plus
the single closing step `exp(24·ζ(2)) ≤ exp 40`, i.e. `4π² ≤ 40`. -/
theorem hFac2_lcm_sum_le_exp40 : ∀ (X : ℕ),
    ∑ d₁ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
      ∑ d₂ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
        hFac2 d₁ * hFac2 d₂ / (Nat.lcm d₁ d₂ : ℝ) ≤ Real.exp 40 := by
  classical
  -- ⟦THE ζ(2) STEP⟧ `24·∑' 1/n² = 24·π²/6 = 4π² ≤ 4·(3.141593)² < 40`
  have hzeta : 24 * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 40 := by
    rw [hasSum_zeta_two.tsum_eq]
    have hpi : Real.pi < 3.141593 := Real.pi_lt_d6
    have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith [hpi, hpi0]
  intro X
  set D := (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d) with hDdef
  set P := (Finset.range (X + 1)).filter (fun p => p.Prime ∧ Odd p) with hPdef
  have hP3 : ∀ p ∈ P, 3 ≤ p := by
    intro p hp
    rw [hPdef, Finset.mem_filter] at hp
    exact three_le_of_odd_prime hp.2.1 hp.2.2
  have hpfsub : ∀ d ∈ D, d.primeFactors ⊆ P := by
    intro d hd
    rw [hDdef, Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨hdlt, _, hodd⟩ := hd
    have hd0 : 0 < d := by have := Nat.odd_iff.mp hodd; omega
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hodd_p : Odd p := by
      rcases hpp.eq_two_or_odd' with h | h
      · have := three_le_of_odd_primeFactor hodd hp; omega
      · exact h
    have hple : p ≤ d := Nat.le_of_dvd hd0 hpd
    rw [hPdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpp, hodd_p⟩
  have hInj : Set.InjOn Nat.primeFactors ↑D := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hDdef, Finset.mem_filter] at hx hy
    have hx' := Nat.prod_primeFactors_of_squarefree hx.2.1
    rw [← hx', hxy, Nat.prod_primeFactors_of_squarefree hy.2.1]
  have hterm : ∀ d₁ ∈ D, ∀ d₂ ∈ D,
      hFac2 d₁ * hFac2 d₂ / (Nat.lcm d₁ d₂ : ℝ)
        = G2 d₁.primeFactors d₂.primeFactors := by
    intro d₁ hd₁ d₂ hd₂
    rw [hDdef, Finset.mem_filter] at hd₁ hd₂
    have hsq1 := hd₁.2.1
    have hsq2 := hd₂.2.1
    have e1 : hFac2 d₁ = ∏ p ∈ d₁.primeFactors, u2 p := rfl
    have e2 : hFac2 d₂ = ∏ p ∈ d₂.primeFactors, u2 p := rfl
    have hlcm : (Nat.lcm d₁ d₂ : ℝ)
        = ∏ p ∈ d₁.primeFactors ∪ d₂.primeFactors, (p : ℝ) :=
      cast_lcm_eq_prod2 hsq1 hsq2
    have hvvprod : (∏ p ∈ d₁.primeFactors ∪ d₂.primeFactors, v2 p)
        = 1 / (Nat.lcm d₁ d₂ : ℝ) := by
      simp only [v2, one_div]
      rw [Finset.prod_inv_distrib, ← hlcm]
    rw [e1, e2]
    simp only [G2]
    rw [hvvprod]
    ring
  have hEq : (∑ d₁ ∈ D, ∑ d₂ ∈ D, hFac2 d₁ * hFac2 d₂ / (Nat.lcm d₁ d₂ : ℝ))
      = ∑ d₁ ∈ D, ∑ d₂ ∈ D, G2 d₁.primeFactors d₂.primeFactors :=
    Finset.sum_congr rfl (fun d₁ hd₁ =>
      Finset.sum_congr rfl (fun d₂ hd₂ => hterm d₁ hd₁ d₂ hd₂))
  have hsubP : D.image Nat.primeFactors ⊆ P.powerset := by
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨d, hd, rfl⟩ := hS
    rw [Finset.mem_powerset]
    exact hpfsub d hd
  have hGnn : ∀ S₁ ∈ P.powerset, ∀ S₂ ∈ P.powerset, 0 ≤ G2 S₁ S₂ := by
    intro S₁ hS₁ S₂ hS₂
    exact G2_nonneg (fun p hp => hP3 p (Finset.mem_powerset.mp hS₁ hp))
      (fun p hp => hP3 p (Finset.mem_powerset.mp hS₂ hp))
  have hreindex : (∑ d₁ ∈ D, ∑ d₂ ∈ D,
        hFac2 d₁ * hFac2 d₂ / (Nat.lcm d₁ d₂ : ℝ))
      ≤ ∑ S₁ ∈ P.powerset, ∑ S₂ ∈ P.powerset, G2 S₁ S₂ := by
    rw [hEq]
    have hInner : ∀ d₁ ∈ D, (∑ d₂ ∈ D, G2 d₁.primeFactors d₂.primeFactors)
        = ∑ S₂ ∈ D.image Nat.primeFactors, G2 d₁.primeFactors S₂ :=
      fun d₁ _ => (Finset.sum_image hInj).symm
    rw [Finset.sum_congr rfl hInner]
    have hOuter : (∑ d₁ ∈ D,
          ∑ S₂ ∈ D.image Nat.primeFactors, G2 d₁.primeFactors S₂)
        = ∑ S₁ ∈ D.image Nat.primeFactors,
            ∑ S₂ ∈ D.image Nat.primeFactors, G2 S₁ S₂ :=
      (Finset.sum_image (f := fun S₁ => ∑ S₂ ∈ D.image Nat.primeFactors, G2 S₁ S₂)
        hInj).symm
    rw [hOuter]
    calc (∑ S₁ ∈ D.image Nat.primeFactors,
            ∑ S₂ ∈ D.image Nat.primeFactors, G2 S₁ S₂)
        ≤ ∑ S₁ ∈ D.image Nat.primeFactors,
            ∑ S₂ ∈ P.powerset, G2 S₁ S₂ := by
          apply Finset.sum_le_sum
          intro S₁ hS₁
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubP
          intro S₂ hS₂mem _
          exact hGnn S₁ (hsubP hS₁) S₂ hS₂mem
      _ ≤ ∑ S₁ ∈ P.powerset, ∑ S₂ ∈ P.powerset, G2 S₁ S₂ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubP
          intro S₁ hS₁mem _
          exact Finset.sum_nonneg (fun S₂ hS₂mem => hGnn S₁ hS₁mem S₂ hS₂mem)
  calc (∑ d₁ ∈ D, ∑ d₂ ∈ D, hFac2 d₁ * hFac2 d₂ / (Nat.lcm d₁ d₂ : ℝ))
      ≤ ∑ S₁ ∈ P.powerset, ∑ S₂ ∈ P.powerset, G2 S₁ S₂ := hreindex
    _ = ∏ p ∈ P, (u2 p ^ 2 * v2 p + u2 p * v2 p + (u2 p * v2 p + 1)) :=
        doubleSum2_eq_prod P
    _ ≤ Real.exp (24 * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) := prod_L2_le_exp hP3
    _ ≤ Real.exp 40 := Real.exp_le_exp.mpr hzeta

/-- **The pinned twin of `hFac2_lcm_sum_le`** — the landed statement plus the
ceiling conjunct `K ≤ exp 40`.  ⟦IRON RULE 1⟧ additive: `hFac2_lcm_sum_le` is
untouched. -/
theorem hFac2_lcm_sum_le_bounded :
    ∃ K : ℝ, 0 < K ∧ K ≤ Real.exp 40 ∧ ∀ (X : ℕ),
      ∑ d₁ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
        ∑ d₂ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
          hFac2 d₁ * hFac2 d₂ / (Nat.lcm d₁ d₂ : ℝ) ≤ K :=
  ⟨Real.exp 40, Real.exp_pos _, le_rfl, hFac2_lcm_sum_le_exp40⟩

/-! ## §2 — the count at the pinned `ε`, with a numeric constant -/

/-- `exp 40 ≤ 3^40` — the one-line coarsening that makes the ceiling a
`norm_num` (true value `2.354·10^17` against `1.216·10^19`, 6.5 bits given
away against 310 bits of room). -/
theorem exp_forty_le_pow40 : Real.exp 40 ≤ 3 ^ 40 := by
  have h1 : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h2 : Real.exp 40 = Real.exp 1 ^ (40 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le h1 40

/-- **The `|Ξ_H|` count at `ε = 1/500` with a FULLY NUMERIC constant.**
`bigXi_bounded_explicit` at `C₁ = 2^35` (`hpt_holds_500`) and `K = exp 40`
(`hFac2_lcm_sum_le_exp40`) — no `∃`-witness is read anywhere. -/
theorem bigXi_bounded_500_explicit40 :
    ∀ (H : ℕ) [NeZero H], 2 ≤ H →
      ((bigXi (1 / 500) H).card : ℝ)
        ≤ 32 * Real.exp 40 * ((2 : ℝ) ^ 35) ^ 2 / (((1 : ℚ) / 500 : ℚ) : ℝ) ^ 10 := by
  intro H _ hH2
  exact bigXi_bounded_explicit (1 / 500) (by norm_num) (by push_cast; norm_num)
    ((2 : ℝ) ^ 35) (Real.exp 40) (Real.exp_pos _) hFac2_lcm_sum_le_exp40 hpt_holds_500 H hH2

/-- **⟦THE COMPOSE HOOK⟧** (`bigXi_bounded_500_ceiling`) — `bigXi_bounded`'s
EXACT shape at the pinned `ε = 1/500`, with the terminal's first inner rider
`Kc ≤ 2^539` carried as ONE extra conjunct.

`32·exp 40·(2^35)²·500^10 ≤ 2^5·3^40·2^70·500^10 ≈ 2^228.2 ≤ 2^539`. -/
theorem bigXi_bounded_500_ceiling :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 539 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((bigXi (1 / 500) H).card : ℝ) ≤ C := by
  refine ⟨32 * Real.exp 40 * ((2 : ℝ) ^ 35) ^ 2 / (((1 : ℚ) / 500 : ℚ) : ℝ) ^ 10,
    by positivity, ?_, 2, le_rfl, bigXi_bounded_500_explicit40⟩
  have hcast : (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 := by norm_num
  rw [hcast]
  have h40 := exp_forty_le_pow40
  have hstep : 32 * Real.exp 40 * ((2 : ℝ) ^ 35) ^ 2 / (1 / 500 : ℝ) ^ 10
      ≤ 32 * (3 : ℝ) ^ 40 * ((2 : ℝ) ^ 35) ^ 2 / (1 / 500 : ℝ) ^ 10 := by
    gcongr
  refine le_trans hstep (le_trans ?_
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : 229 ≤ 539)))
  norm_num

/-- The same hook, stated against an opaque `ε` pinned by an equation — the
literal drop-in for the flat head's `obtain … := bigXi_bounded ε hεQpos hε2`
(the head pins `ε := 1/500` at `HloExportFlat` :256 / `S16Uniform` :275). -/
theorem bigXi_bounded_ceiling_of_pin (ε : ℚ) (hε : ε = 1 / 500) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 539 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((bigXi ε H).card : ℝ) ≤ C := by
  subst hε; exact bigXi_bounded_500_ceiling

end Salt.Entropy.Chowla
