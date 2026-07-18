/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.GrahamL2
import Salt.SW.MoebiusLog

/-!
# The `g`-restricted Barban–Vehov decay (DH-COPBV, HB-ENGINE WP2)

Design: the DH-LCM residual flagged in `docs/blueprints/flags.md`. `GrahamL2`'s Selberg
diagonalization `Σ_{d,e≤z} θ_dθ_e/lcm(d,e) = Σ_{g≤z} φ(g)·(innerG z g)²` reduced the L² mean
to the `g`-restricted Barban–Vehov sums `innerG z g = Σ_{d≤z, g∣d} θ_d/d`. The `g = 1` factor
is already sharp (`MoebiusLog.abs_sum_grahamTheta_div_le_inv_log`). This module lands the
combinatorial identity machinery that exposes `innerG z g` as a `g`-coprime copy of the
Barban–Vehov sum, plus the crude pointwise size bound.

## Objects / rungs

* **The reindex stone** `sum_dvd_reindex` — the multiples-of-`k` reindex
  `Σ_{d≤N, k∣d} F d = Σ_{e≤N/k} F(k·e)` (the bijection `e ↦ k·e`).
* **The Möbius-over-gcd expansion stone** `sum_coprime_eq_moebius_multiples` — the classical
  coprimality unfolding `Σ_{d≤N, (d,g)=1} F d = Σ_{k∣g} μ(k)·Σ_{e≤N/k} F(k·e)`, via the
  divisor Möbius identity `Σ_{k∣m} μ(k) = [m=1]`. The genuine combinatorial heart of the
  `g`-restricted analysis (the `(d,g)=1` indicator is `Σ_{k∣gcd(d,g)} μ(k)`).
* **The factorization stone** `innerG_eq_coprime_sum` — `innerG z g` written as a `g`-coprime,
  level-`z/g` copy of the BV value sum: `d = g·d'` with `μ(d)=μ(g)μ(d')` on `(d',g)=1`.
* **The crude pointwise bound** `abs_innerG_le_crude` — `|innerG z g| ≤ (1 + log(z/g))/g`
  (triangle inequality + `|θ_d| ≤ 1` + the multiples reindex). No `1/log z` decay.

## Named residual (flagged, NOT attempted here)

The SHARP pointwise decay `|innerG z g| ≤ C·3^ω(g)/(g·log z)` needs the `g`-coprime Möbius
decay (coprime-Mertens with an Euler-factor constant), which regenerates coprimality under
every elementary expansion — it forces a nested strong induction (on `ω(g)` with an inner
level-telescope for the self-term) or the full Euler-product analytic input. See
`docs/blueprints/flags.md` (DH-COPBV). The Graham *average* `Σ_g φ(g) innerG² ≍ 1/log z` is a
separate node (even the sharp pointwise bound with `3^ω` does not close the `g`-sum).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open Finset

namespace Salt.SW

open ArithmeticFunction

/-! ## The multiples-of-`k` reindex and the divisor Möbius identity -/

/-- **The reindex stone.** For `k ≥ 1`, summing a function over the multiples of `k` in
`[1, N]` is the same as summing the scaled function over `[1, N/k]` (the bijection
`e ↦ k·e`, injective by `k ≥ 1`, hitting exactly the multiples of `k`). -/
theorem sum_dvd_reindex {k N : ℕ} (hk : 1 ≤ k) (F : ℕ → ℝ) :
    ∑ d ∈ (Finset.Icc 1 N).filter (fun d => k ∣ d), F d
      = ∑ e ∈ Finset.Icc 1 (N / k), F (k * e) := by
  have himg : (Finset.Icc 1 N).filter (fun d => k ∣ d)
      = (Finset.Icc 1 (N / k)).image (fun e => k * e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hd1, hdN⟩, hkd⟩
      obtain ⟨e, rfl⟩ := hkd
      refine ⟨e, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos e with rfl | he
        · simp at hd1
        · exact he
      · exact (Nat.le_div_iff_mul_le hk).mpr (by rw [mul_comm]; exact hdN)
    · rintro ⟨e, ⟨he1, heN⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hk he1, ?_⟩, Dvd.intro e rfl⟩
      rw [mul_comm]; exact (Nat.le_div_iff_mul_le hk).mp heN
  rw [himg, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hk hxy

/-- The divisor Möbius identity `Σ_{k∣m} μ(k) = [m=1]` in `ℝ` (from `μ * ζ = 1`). -/
theorem sum_divisors_moebius_real (m : ℕ) :
    ∑ k ∈ m.divisors, (moebius k : ℝ) = if m = 1 then (1 : ℝ) else 0 := by
  have hint : ∑ k ∈ m.divisors, (moebius k : ℤ) = if m = 1 then (1 : ℤ) else 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
        ArithmeticFunction.one_apply]
  have hcast : ∑ k ∈ m.divisors, (moebius k : ℝ)
      = ((∑ k ∈ m.divisors, (moebius k : ℤ) : ℤ) : ℝ) := by push_cast; rfl
  rw [hcast, hint]; split_ifs <;> norm_num

/-! ## The Möbius-over-gcd expansion stone -/

/-- **The Möbius-over-gcd expansion stone.** For `g ≥ 1` and any `F : ℕ → ℝ`, the coprime-to-`g`
restricted sum unfolds over divisors of `g`:
`Σ_{d≤N, (d,g)=1} F d = Σ_{k∣g} μ(k)·Σ_{e≤N/k} F(k·e)`.
The classical coprimality unfolding: `[(d,g)=1] = Σ_{k∣gcd(d,g)} μ(k)`, then reindex the
`k`-divisible inner sums by `d = k·e`. This is the combinatorial heart of the `g`-restricted
Barban–Vehov analysis. -/
theorem sum_coprime_eq_moebius_multiples (g N : ℕ) (hg : 1 ≤ g) (F : ℕ → ℝ) :
    ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d g), F d
      = ∑ k ∈ g.divisors, (moebius k : ℝ) * ∑ e ∈ Finset.Icc 1 (N / k), F (k * e) := by
  have hg0 : g ≠ 0 := by omega
  -- The gcd-divisor identity: divisors of `g` dividing `d` are exactly divisors of `gcd g d`.
  have hset : ∀ d : ℕ, g.divisors.filter (fun k => k ∣ d) = (Nat.gcd g d).divisors := by
    intro d
    ext k
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hgcd0 : Nat.gcd g d ≠ 0 := by
      have : 0 < Nat.gcd g d := Nat.gcd_pos_of_pos_left d (by omega)
      omega
    constructor
    · rintro ⟨⟨hkg, _⟩, hkd⟩; exact ⟨⟨hkg, hkd⟩, hgcd0⟩
    · rintro ⟨⟨hkg, hkd⟩, _⟩; exact ⟨⟨hkg, hg0⟩, hkd⟩
  -- The pointwise Möbius collapse: `Σ_{k∣g} μ(k)·[k∣d]·F d = [(d,g)=1]·F d`.
  have hpt : ∀ d : ℕ, ∑ k ∈ g.divisors, (moebius k : ℝ) * (if k ∣ d then F d else 0)
      = if Nat.Coprime d g then F d else 0 := by
    intro d
    have hrw : ∑ k ∈ g.divisors, (moebius k : ℝ) * (if k ∣ d then F d else 0)
        = F d * ∑ k ∈ g.divisors.filter (fun k => k ∣ d), (moebius k : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      exact Finset.sum_congr rfl (fun k _ => by split_ifs <;> ring)
    rw [hrw, hset d, sum_divisors_moebius_real]
    by_cases hc : Nat.Coprime d g
    · have hg1 : Nat.gcd g d = 1 := by rw [Nat.gcd_comm]; exact hc
      rw [if_pos hg1, if_pos hc, mul_one]
    · have hg1 : ¬ Nat.gcd g d = 1 := by rw [Nat.gcd_comm]; exact hc
      rw [if_neg hg1, if_neg hc, mul_zero]
  -- Assemble: reindex each inner sum, swap, collapse pointwise.
  have hRHS : ∑ k ∈ g.divisors, (moebius k : ℝ) * ∑ e ∈ Finset.Icc 1 (N / k), F (k * e)
      = ∑ d ∈ Finset.Icc 1 N, (if Nat.Coprime d g then F d else 0) := by
    have e1 : ∀ k ∈ g.divisors, (moebius k : ℝ) * ∑ e ∈ Finset.Icc 1 (N / k), F (k * e)
        = ∑ d ∈ Finset.Icc 1 N, (moebius k : ℝ) * (if k ∣ d then F d else 0) := by
      intro k hk
      rw [← sum_dvd_reindex (Nat.pos_of_mem_divisors hk) F, Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun d _ => hpt d)
  rw [Finset.sum_filter, hRHS]

/-! ## The factorization stone and the crude pointwise bound -/

/-- **The factorization stone.** `innerG z g` is a level-`z/g` reindex of the Barban–Vehov
value sum over multiples of `g`: `innerG z g = Σ_{e≤z/g} θ_{g·e}/(g·e)`. The bijection
`d = g·e` (`sum_dvd_reindex` at `k = g`); the `μ`-vanishing off `(e,g)=1` is carried inside
`θ_{g·e} = μ(g·e)·log(z/(g·e))/log z`. -/
theorem innerG_eq_reindex (z g : ℕ) (hg : 1 ≤ g) :
    innerG z g = ∑ e ∈ Finset.Icc 1 (z / g), grahamTheta z (g * e) / ((g * e : ℕ) : ℝ) := by
  unfold innerG
  rw [← Finset.sum_filter]
  exact sum_dvd_reindex hg (fun d => grahamTheta z d / (d : ℝ))

/-- **The crude pointwise bound.** `|innerG z g| ≤ (1 + log(z/g))/g`. Triangle inequality on
the reindex, `|θ_d| ≤ 1`, and the harmonic bound `Σ_{e≤z/g} 1/e ≤ 1 + log(z/g)`. This carries
NO `1/log z` decay — the sharp `g`-coprime cancellation is the named residual (see the module
header / flags DH-COPBV). Useful in the `g`-truncated regimes where `z/g` is bounded. -/
theorem abs_innerG_le_crude {z g : ℕ} (hz : 2 ≤ z) (hg : 1 ≤ g) :
    |innerG z g| ≤ (1 + Real.log (z / g : ℕ)) / (g : ℝ) := by
  rw [innerG_eq_reindex z g hg]
  have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hbound : ∀ e ∈ Finset.Icc 1 (z / g),
      |grahamTheta z (g * e) / ((g * e : ℕ) : ℝ)| ≤ (g : ℝ)⁻¹ * (e : ℝ)⁻¹ := by
    intro e he
    rw [Finset.mem_Icc] at he
    have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he.1
    have hge : ((g * e : ℕ) : ℝ) = (g : ℝ) * (e : ℝ) := by push_cast; ring
    rw [abs_div, Nat.abs_cast, hge]
    calc |grahamTheta z (g * e)| / ((g : ℝ) * (e : ℝ))
        ≤ 1 / ((g : ℝ) * (e : ℝ)) := by gcongr; exact abs_grahamTheta_le_one hz (g * e)
      _ = (g : ℝ)⁻¹ * (e : ℝ)⁻¹ := by rw [one_div, mul_inv]
  calc |∑ e ∈ Finset.Icc 1 (z / g), grahamTheta z (g * e) / ((g * e : ℕ) : ℝ)|
      ≤ ∑ e ∈ Finset.Icc 1 (z / g), |grahamTheta z (g * e) / ((g * e : ℕ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ Finset.Icc 1 (z / g), (g : ℝ)⁻¹ * (e : ℝ)⁻¹ := Finset.sum_le_sum hbound
    _ = (g : ℝ)⁻¹ * ∑ e ∈ Finset.Icc 1 (z / g), (e : ℝ)⁻¹ := by rw [← Finset.mul_sum]
    _ ≤ (g : ℝ)⁻¹ * (1 + Real.log (z / g : ℕ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_Icc_le (z / g)) (by positivity)
    _ = (1 + Real.log (z / g : ℕ)) / (g : ℝ) := by rw [inv_mul_eq_div]

/-- **The coprime factorization stone.** For squarefree `g`, `innerG z g` is `μ(g)/(g·log z)`
times a genuinely `g`-coprime, level-`z/g` copy of the Barban–Vehov numerator:
`innerG z g = (μ(g)/(g·log z))·Σ_{e≤z/g, (e,g)=1} (μ(e)/e)·log(z/(g·e))`.
The non-coprime terms vanish (`μ(g·e)=0`), and on `(e,g)=1` the Möbius multiplicativity gives
`μ(g·e)=μ(g)μ(e)`. This is the exact object on which the SHARP `1/log z` decay operates: its
`g=1` instance is the landed `abs_sum_grahamTheta_div_le_inv_log` (up to the `1/log z` factor);
the general `g` requires the coprime-Mertens Euler-factor decay (the named residual). -/
theorem innerG_eq_coprime_sum {z g : ℕ} (hz : 2 ≤ z) (hg : 1 ≤ g) (hsf : Squarefree g) :
    innerG z g
      = (moebius g : ℝ) / ((g : ℝ) * Real.log z)
        * ∑ e ∈ (Finset.Icc 1 (z / g)).filter (fun e => Nat.Coprime e g),
            (moebius e : ℝ) / (e : ℝ) * Real.log ((z : ℝ) / ((g * e : ℕ) : ℝ)) := by
  have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := ne_of_gt hgpos
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hlogzne : Real.log (z : ℝ) ≠ 0 := ne_of_gt hlogz
  rw [innerG_eq_reindex z g hg]
  -- Restrict the full reindexed sum to coprime `e` (non-coprime terms carry `μ(g·e)=0`).
  have hfull : ∑ e ∈ Finset.Icc 1 (z / g), grahamTheta z (g * e) / ((g * e : ℕ) : ℝ)
      = ∑ e ∈ (Finset.Icc 1 (z / g)).filter (fun e => Nat.Coprime e g),
          grahamTheta z (g * e) / ((g * e : ℕ) : ℝ) := by
    symm
    apply Finset.sum_filter_of_ne
    intro e he hne
    by_contra hcop
    apply hne
    rw [Finset.mem_Icc] at he
    have hle : g * e ≤ z := by
      have h := (Nat.le_div_iff_mul_le hg).mp he.2; rw [mul_comm]; exact h
    rw [grahamTheta_of_le hle]
    have hns : ¬ Squarefree (g * e) := by
      rw [Nat.squarefree_mul_iff]; rintro ⟨hcopge, _, _⟩; exact hcop (Nat.coprime_comm.mp hcopge)
    rw [moebius_eq_zero_of_not_squarefree hns]; simp
  rw [hfull, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Finset.mem_filter, Finset.mem_Icc] at he
  obtain ⟨⟨he1, heM⟩, hcop⟩ := he
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
  have hene : (e : ℝ) ≠ 0 := ne_of_gt hepos
  have hle : g * e ≤ z := by
    have h := (Nat.le_div_iff_mul_le hg).mp heM; rw [mul_comm]; exact h
  have hmuge : (moebius (g * e) : ℝ) = (moebius g : ℝ) * (moebius e : ℝ) := by
    have h := isMultiplicative_moebius.map_mul_of_coprime hcop.symm
    exact_mod_cast h
  have hgeR : ((g * e : ℕ) : ℝ) = (g : ℝ) * (e : ℝ) := by push_cast; ring
  rw [grahamTheta_of_le hle, hmuge, hgeR]
  field_simp

end Salt.SW
