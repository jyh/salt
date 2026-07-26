/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RamWeight
import Salt.MR.USetPins
import Salt.MR.CompactMin
import Salt.Mertens.Third

/-!
# CofactorDist — the co-factor distance page, THE COLLISION LEMMA, the amended pin (U7-C)

The ⟦V5⟧ plan's `U7-C`.  Three stones, in the order they are consumed.

* **§1 (C-1) the block-window Mertens page.**  `RamWeight`'s exit
  (`gxDatum_pretDistSq_costwist`) prices the `∫₀¹ x^ω` damping by the *abstract* window sum
  `Σ_{P ≤ p ≤ Q, p ≤ X} 1/p`.  Here it is evaluated: `blockWindow_mertens_pin` says that at
  the §8.3 endpoints (`P ≥ P₈₃ = exp((log X)^{1−θ})`, `Q ≤ Q₈₃ = exp(log X/loglog X)`) the
  whole damping price is `≤ θ·loglog X + 25`.

  The honest page (`loglog_P83`, `loglog_Q83`): `loglog Q₈₃ = loglog X − logloglog X`,
  `loglog P₈₃ = (1−θ)·loglog X`, so the window mass is
  `θ·loglog X − logloglog X + O(1)` — the `−logloglog X` is a *gain* and is discarded.
  The `+25` is the fully explicit `12/log Q + 12/log P + 1/P` of the sharp real Mertens-2
  (`Salt.Mertens.mertens_second_sharp_real`) plus the `P`-endpoint half-prime; nothing is
  hidden (law #253).

* **§2 (C-2) the amended pin `θ = 1/(32(3e+1))`.**  `W2`'s one-sided distance loss (factor
  `1`, not `2`) makes the balance self-consistent: the Halász grade after the damping is
  `ρ = (1/32 − θ)/e` and the §8.3 balance is `θ = ρ/3`, i.e. `θ(3e+1) = 1/32`.  The twins of
  `USetPins` §6 are re-run at this pin.

  **FINDING (recorded in Lean).**  The ⟦V5⟧ block's quoted door margin `1.707×` is *very
  slightly optimistic*: `500·θ₂₉₃ = 1.70675…`, so `exit_margin_293` is stated at `1.706/500`
  and `exit_margin_293_sharp` records that `1.707/500` genuinely FAILS.  The door
  (`c₀ ≥ 1/500`) is cleared either way — see `exit_beats_c0_293`.

* **§3 (C-3) THE COLLISION LEMMA.**  `dist_one_shift_le_of_two_caps` (`CompactMin`:244) is
  *symmetric*: two caps at the same `S` give `𝔻²(1, shift) ≤ 4S`.  At the live grades
  (`S₁ = (1/16)loglog X` on the row, `S₂ + W = (1/32)loglog X` on the co-factor) the
  symmetric form gives `4·(1/16)loglog X = (1/4)loglog X`, which does **not** beat the
  `(1/4 − o(1))·loglog X` floor of `dist_one_floor_pow`.  So the collision needs the
  ASYMMETRIC twin `dist_one_shift_le_of_two_caps_asym`:
  `𝔻²(1, shift) ≤ (√S₁ + √S₂)²`, and there

    `(√(1/16) + √(1/32))² = (3 + 2√2)/32 = 0.18213… ≤ 0.1822 < 1/4`,

  a margin of `0.0678·loglog X` (`collision_margin`).  That margin is exactly what pays for
  the `o(loglog)` corrections, and those are carried IN-STATEMENT as the named gate
  `collisionGate` (Z-3 of the ⟦V5⟧ plan: the `X₀` tower is never absorbed).

* **§4 (C-4) the ball corollaries.**  `pocket_far_from_ball` / `pocket_ball_shrink`: with the
  pocket center pinned to within `1` of the row center, a ball of radius `R` around one is
  inside the ball of radius `R+1` around the other — the CASE-B radius input of U7-D.
-/

namespace Salt.MR

open Finset
open scoped BigOperators

/-! ## §1 (C-1) — the block-window Mertens page -/

/-- The block window `[P,Q]` truncated at `X`, compared against the two Mertens partial sums
at the endpoints: `Σ_{p ∈ window} 1/p ≤ S(Q) − S(P) + 1/2`.

The `+1/2` is the `P`-endpoint: the window is *closed* at `P`, while `S(P)` already counts
`P` itself, so at most one prime (`p = P`, worth `1/P ≤ 1/2`) is double-subtracted. -/
lemma sum_blockWindowPrimes_le_SPartial (P Q : ℕ) (X : ℝ) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ∑ p ∈ blockWindowPrimes P Q X, (1 : ℝ) / (p : ℝ)
      ≤ Salt.Mertens.SPartial (Q : ℝ) - Salt.Mertens.SPartial (P : ℝ) + 1 / 2 := by
  classical
  set A := (Finset.range (Q + 1)).filter Nat.Prime with hA
  set B := (Finset.range P).filter Nat.Prime with hB
  set C := (Finset.range (P + 1)).filter Nat.Prime with hC
  have hSQ : Salt.Mertens.SPartial (Q : ℝ) = ∑ p ∈ A, (1 : ℝ) / (p : ℝ) := by
    rw [Salt.Mertens.SPartial, Nat.floor_natCast, hA]
  have hSP : Salt.Mertens.SPartial (P : ℝ) = ∑ p ∈ C, (1 : ℝ) / (p : ℝ) := by
    rw [Salt.Mertens.SPartial, Nat.floor_natCast, hC]
  have hBA : B ⊆ A := by
    rw [hA, hB]
    refine Finset.filter_subset_filter _ ?_
    intro m hm
    rw [Finset.mem_range] at hm ⊢
    omega
  have hGsub : blockWindowPrimes P Q X ⊆ A \ B := by
    intro p hp
    simp only [blockWindowPrimes, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨⟨_, hpr⟩, hPle, hQle⟩ := hp
    rw [Finset.mem_sdiff, hA, hB]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpr⟩, ?_⟩
    rw [Finset.mem_filter, Finset.mem_range]
    rintro ⟨h, -⟩
    omega
  have hsd : ∑ p ∈ A \ B, (1 : ℝ) / (p : ℝ) + ∑ p ∈ B, (1 : ℝ) / (p : ℝ)
      = ∑ p ∈ A, (1 : ℝ) / (p : ℝ) := Finset.sum_sdiff hBA
  have hle : ∑ p ∈ blockWindowPrimes P Q X, (1 : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ A \ B, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hGsub (fun p _ _ => by positivity)
  have hCB : ∑ p ∈ C, (1 : ℝ) / (p : ℝ) ≤ 1 / 2 + ∑ p ∈ B, (1 : ℝ) / (p : ℝ) := by
    have hins : C ⊆ insert P B := by
      intro p hp
      rw [hC, Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_insert]
      rcases Nat.lt_or_ge p P with h | h
      · exact Or.inr (by rw [hB, Finset.mem_filter, Finset.mem_range]; exact ⟨h, hp.2⟩)
      · exact Or.inl (by omega)
    have h1 : ∑ p ∈ C, (1 : ℝ) / (p : ℝ) ≤ ∑ p ∈ insert P B, (1 : ℝ) / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hins (fun p _ _ => by positivity)
    have h2 : ∑ p ∈ insert P B, (1 : ℝ) / (p : ℝ) ≤ 1 / 2 + ∑ p ∈ B, (1 : ℝ) / (p : ℝ) := by
      by_cases hPB : P ∈ B
      · rw [Finset.insert_eq_self.mpr hPB]; norm_num
      · rw [Finset.sum_insert hPB]
        have hP2 : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
        have hinv : (1 : ℝ) / (P : ℝ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
        linarith
    linarith
  rw [hSQ, hSP]
  linarith

/-- **C-1 (the abstract window page).**  The block-window mass, evaluated by the sharp real
Mertens-2 at the two endpoints: the Meissel constant cancels and only the `loglog`-difference
plus the two explicit `12/log` errors survive. -/
theorem blockWindow_mertens_abstract (P Q : ℕ) (X : ℝ) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ∑ p ∈ blockWindowPrimes P Q X, (1 : ℝ) / (p : ℝ)
      ≤ Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ))
          + 12 / Real.log (Q : ℝ) + 12 / Real.log (P : ℝ) + 1 / 2 := by
  have hP2 : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hQ2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast le_trans hP hPQ
  have hmP := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hP2)
  have hmQ := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hQ2)
  have hbase := sum_blockWindowPrimes_le_SPartial P Q X hP hPQ
  linarith [hmP.1, hmQ.2]

/-- **C-1 (the `C`-shape).**  Once both endpoints are at least `e` the two Mertens errors are
each `≤ 12`, so the whole window page is the `loglog`-difference plus the explicit `25`. -/
theorem blockWindow_mertens_const (P Q : ℕ) (X : ℝ)
    (hP : Real.exp 1 ≤ (P : ℝ)) (hPQ : P ≤ Q) :
    ∑ p ∈ blockWindowPrimes P Q X, (1 : ℝ) / (p : ℝ)
      ≤ Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25 := by
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hP2R : (2 : ℝ) ≤ (P : ℝ) := le_trans h2e hP
  have hP2 : 2 ≤ P := by exact_mod_cast hP2R
  have hPQR : (P : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hPQ
  have hlogP : (1 : ℝ) ≤ Real.log (P : ℝ) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hP
  have hlogQ : (1 : ℝ) ≤ Real.log (Q : ℝ) := le_trans hlogP
    (Real.log_le_log (by linarith) hPQR)
  have e1 : 12 / Real.log (P : ℝ) ≤ 12 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have e2 : 12 / Real.log (Q : ℝ) ≤ 12 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hbase := blockWindow_mertens_abstract P Q X hP2 hPQ
  linarith

/-- **The honest page, upper endpoint.**  `loglog Q₈₃ = loglog X − logloglog X`. -/
theorem loglog_Q83 (X : ℝ) (hL : 1 < Real.log X) :
    Real.log (Real.log (Q83 X)) = Real.log (Real.log X) - Real.log (Real.log (Real.log X)) := by
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLL0 : (0 : ℝ) < Real.log (Real.log X) := Real.log_pos hL
  rw [Q83, Real.log_exp, Real.log_div (ne_of_gt hL0) (ne_of_gt hLL0)]

/-- **The honest page, lower endpoint.**  `loglog P₈₃ = (1−θ)·loglog X`. -/
theorem loglog_P83 (X θ : ℝ) (hL0 : 0 < Real.log X) :
    Real.log (Real.log (P83 X θ)) = (1 - θ) * Real.log (Real.log X) := by
  rw [P83, Real.log_exp, Real.log_rpow hL0]

/-- **C-1 AT THE PIN — the shape U7-E consumes.**  For a natural window `[P,Q]` sitting
inside the §8.3 window (`P₈₃ ≤ P`, `Q ≤ Q₈₃`), the entire price of the `∫₀¹ x^ω` damping is

  `Σ_{P ≤ p ≤ Q, p ≤ X} 1/p ≤ θ·loglog X + 25`.

The `−logloglog X` of the honest page (`loglog_Q83`) is a gain and is thrown away; the `25` is
the explicit Mertens error (law #253: no `X₀` is hidden — the only gate is the stated
`e ≤ log X`). -/
theorem blockWindow_mertens_pin (P Q : ℕ) (X θ : ℝ) (_hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hX : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X θ ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q) :
    ∑ p ∈ blockWindowPrimes P Q X, (1 : ℝ) / (p : ℝ)
      ≤ θ * Real.log (Real.log X) + 25 := by
  have he1 : (1 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hL1 : (1 : ℝ) < Real.log X := lt_of_lt_of_le he1 hX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log (Real.exp_pos 1) hX; rwa [Real.log_exp] at h
  have hLL0 : (0 : ℝ) < Real.log (Real.log X) := by linarith
  have hLLL0 : (0 : ℝ) ≤ Real.log (Real.log (Real.log X)) := Real.log_nonneg hLL1
  -- the lower endpoint dominates `e`
  have hlogP83 : Real.log (P83 X θ) = (Real.log X) ^ (1 - θ) := by rw [P83, Real.log_exp]
  have hP83one : (1 : ℝ) ≤ (Real.log X) ^ (1 - θ) :=
    Real.one_le_rpow (le_of_lt hL1) (by linarith)
  have hPexp : Real.exp 1 ≤ (P : ℝ) := by
    refine le_trans ?_ hPlow
    rw [P83]
    exact Real.exp_le_exp.mpr hP83one
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hP2R : (2 : ℝ) ≤ (P : ℝ) := le_trans h2e hPexp
  have hPQR : (P : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hPQ
  have hQ2R : (2 : ℝ) ≤ (Q : ℝ) := le_trans hP2R hPQR
  -- the two endpoint comparisons
  have hlogP0 : (0 : ℝ) < Real.log (P83 X θ) := by rw [hlogP83]; linarith
  have hP83pos : (0 : ℝ) < P83 X θ := by rw [P83]; exact Real.exp_pos _
  have hlogPP : Real.log (P83 X θ) ≤ Real.log (P : ℝ) :=
    Real.log_le_log hP83pos hPlow
  have hllP : (1 - θ) * Real.log (Real.log X) ≤ Real.log (Real.log (P : ℝ)) := by
    rw [← loglog_P83 X θ hL0]
    exact Real.log_le_log hlogP0 hlogPP
  have hlogQ0 : (0 : ℝ) < Real.log (Q : ℝ) := by
    have : (1 : ℝ) < (Q : ℝ) := by linarith
    exact Real.log_pos this
  have hlogQQ : Real.log (Q : ℝ) ≤ Real.log (Q83 X) :=
    Real.log_le_log (by linarith) hQhigh
  have hllQ : Real.log (Real.log (Q : ℝ))
      ≤ Real.log (Real.log X) - Real.log (Real.log (Real.log X)) := by
    rw [← loglog_Q83 X hL1]
    exact Real.log_le_log hlogQ0 hlogQQ
  have hbase := blockWindow_mertens_const P Q X hPexp hPQ
  nlinarith [hbase, hllP, hllQ, hLLL0]

/-! ## §2 (C-2) — the amended pin `θ = 1/(32(3e+1))` and its balance twins -/

/-- **THE AMENDED PIN** (⟦V5⟧, JYH-ratified).  `θ₂₉₃ := 1/(32(3e+1)) ≈ 1/292.955`.

It is the self-consistent solution of the `W2` balance: the `∫₀¹ x^ω` damping costs
`θ·loglog X` of distance (factor `1`, not `2`), so the Halász grade after the damping is
`ρ = (1/32 − θ)/e`, and the §8.3 balance pin is `θ = ρ/3` (`USetPins.balance_exponent`).
Eliminating `ρ` gives `θ(3e+1) = 1/32`. -/
noncomputable def theta293 : ℝ := 1 / (32 * (3 * Real.exp 1 + 1))

/-- **The amended exit exponent** `ρ_eff = 3θ₂₉₃` — the `(log X)^{−ρ_eff}` at which BOTH arms
of the U-7 dichotomy exit. -/
noncomputable def rho293 : ℝ := 3 * theta293

theorem theta293_pos : 0 < theta293 := by
  rw [theta293]; positivity

theorem rho293_pos : 0 < rho293 := by
  rw [rho293]; linarith [theta293_pos]

/-- **THE BALANCE IDENTITY at the amended pin.**  `ρ_eff = (1/32 − θ)/e`: the Halász grade
that survives the one-sided damping loss `θ·loglog X`.  Together with `theta293_eq_rho_div_three`
(`θ = ρ/3`, the §8.3 balance) this is the self-consistency
`θ₂₉₃ = (1/32 − θ₂₉₃)/(3e)` that FIXES the pin. -/
theorem balance_exponent_293 : rho293 = (1 / 32 - theta293) / Real.exp 1 := by
  have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  rw [rho293, theta293]
  field_simp
  ring

/-- The §8.3 balance leg at the amended pin: `θ = ρ_eff/3`. -/
theorem theta293_eq_rho_div_three : theta293 = rho293 / 3 := by
  rw [rho293]; ring

/-- The self-consistency in one line: `θ₂₉₃ = (1/32 − θ₂₉₃)/(3e)`. -/
theorem theta293_self_consistent : theta293 = (1 / 32 - theta293) / (3 * Real.exp 1) := by
  have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  rw [theta293]
  field_simp
  ring

/-- **The balance exponent identity** (`USetPins.balance_exponent`'s twin at the amended pin):
the §8.3 main leg `(log X)^{5θ−2ρ}` and remainder leg `(log X)^{−θ}` meet. -/
theorem balance_exponent_293' : 5 * theta293 - 2 * rho293 = -theta293 := by
  rw [rho293]; ring

/-- `θ₂₉₃ < 1/2` — the `P-2` guard (`USetPins.pin_Pii` needs `θ < 1/2`). -/
theorem theta293_lt_half : theta293 < 1 / 2 := by
  rw [theta293, div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.exp_one_gt_d9]

/-- **The door margin — `1.706×`.**  `θ₂₉₃ ≥ 1.706/500`.

FINDING: the ⟦V5⟧ block quotes `1.707×`; the true value is `500·θ₂₉₃ = 1.70675…`, so
`1.707/500` is (barely) FALSE — see `exit_margin_293_sharp`. -/
theorem exit_margin_293 : (1.706 : ℝ) / 500 ≤ theta293 := by
  rw [theta293, div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [Real.exp_one_lt_d9]

/-- **FAILS-protection for the quoted margin** (the recorded finding).  `θ₂₉₃ < 1.707/500`:
the ⟦V5⟧ block's `1.707×` overstates the door margin by `3·10^{-4}`.  The door itself is
untouched (`exit_beats_c0_293`). -/
theorem exit_margin_293_sharp : theta293 < (1.707 : ℝ) / 500 := by
  rw [theta293, div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.exp_one_gt_d9]

/-- `θ₂₉₃ < 1/32` — the co-factor pocket grade `1/32 − θ` is genuinely positive, which is what
makes the collision's `θ`-cancellation an identity rather than a wish. -/
theorem theta293_lt_one_div_32 : theta293 < 1 / 32 := by
  rw [theta293, div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.exp_one_gt_d9]

/-- **The door's floor is cleared**: `c₀ = 1/500 ≤ θ₂₉₃`. -/
theorem c0_le_theta293 : (1 : ℝ) / 500 ≤ theta293 := by
  have h := exit_margin_293; norm_num at h ⊢; linarith

/-- **The `o(1)` still clears the floor.**  Any `ε ≤ 1/1000` leaves `θ₂₉₃ − ε ≥ 1/500`. -/
theorem exit_beats_c0_293 (ε : ℝ) (hε : ε ≤ 1 / 1000) : (1 : ℝ) / 500 ≤ theta293 - ε := by
  have h := exit_margin_293
  have h2 : (1.706 : ℝ) / 500 - 1 / 1000 ≥ 1 / 500 := by norm_num
  linarith

/-- **The price of the amendment, in Lean.**  `θ₂₉₃ = 1/(96e + 32) < 1/(96e) = θ(ρ_B4)`: the
`W2` damping loss genuinely shrinks the §8.3 exit exponent (margin `1.916× → 1.706×`), and the
whole content of the ⟦V5⟧ ρ-amendment is that it *still* clears `c₀ = 1/500`. -/
theorem theta293_lt_theta83_rhoB4 : theta293 < theta83 rhoB4 := by
  rw [theta83_rhoB4, theta293]
  refine div_lt_div_of_pos_left (by norm_num) (by positivity) ?_
  nlinarith [Real.exp_one_gt_d9]

/-- `ρ_eff = 3θ₂₉₃ ≥ 3/293` — the numeral the two U-7 arms share. -/
theorem rho293_ge : (3 : ℝ) / 293 ≤ rho293 := by
  rw [rho293, theta293]
  rw [div_le_iff₀ (by norm_num)]
  rw [show (3 : ℝ) * (1 / (32 * (3 * Real.exp 1 + 1)))
      = 3 / (32 * (3 * Real.exp 1 + 1)) by ring]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [Real.exp_one_lt_d9]

/-- **The loglog absorption at the amended pin** (`loglog_le_rpow` instantiated):
`loglog X ≤ (log X)^{θ₂₉₃}` from the stated threshold. -/
theorem loglog_absorb_293 (X : ℝ) (hX : Real.exp 1 ≤ Real.log X)
    (hgate : 4 / theta293 ^ 2 ≤ (Real.log X) ^ theta293) :
    Real.log (Real.log X) ≤ (Real.log X) ^ theta293 :=
  loglog_le_rpow X theta293 theta293_pos hX hgate

/-- **P-3 at the amended pin**: the §8.3 window `[P₈₃, Q₈₃]` is nonempty at `θ₂₉₃`. -/
theorem pin_P83_le_Q83_293 (X : ℝ) (hX : Real.exp 1 ≤ Real.log X)
    (hgate : 4 / theta293 ^ 2 ≤ (Real.log X) ^ theta293) :
    P83 X theta293 ≤ Q83 X :=
  pin_P83_le_Q83_of_gate X theta293 theta293_pos hX hgate

/-! ## §3 (C-3) — THE COLLISION LEMMA -/

/-- Sub-additivity of `√` (the split that releases the `O(1)` window error from under the
root). -/
private lemma sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have h3 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h3
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-- **THE ASYMMETRIC TWO-CAP TRIANGLE.**  If `f` is within `√S₀` of `n^{it₀}` and within
`√S₁` of `n^{iv}` then the two characters are within `√S₀ + √S₁` of each other:

  `𝔻²(1, n^{i(v−t₀)}; X) ≤ (√S₀ + √S₁)²`.

This is `CompactMin.dist_one_shift_le_of_two_caps` with the two caps *unlinked*.  The
symmetric stone is the `S₀ = S₁ = S` case (`(√S+√S)² = 4S`); on the U-7 row the two caps are
genuinely different grades (`1/16` on the row, `1/32` on the co-factor after the damping
loss), and the `4·max` reading is exactly lossy enough to lose the collision — see the
module header. -/
theorem dist_one_shift_le_of_two_caps_asym {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {t₀ v X S₀ S₁ : ℝ} (h0 : pretDistSq f (costwist t₀) X ≤ S₀)
    (h1 : pretDistSq f (costwist v) X ≤ S₁) :
    pretDistSq (fun _ => 1) (costwist (v - t₀)) X ≤ (Real.sqrt S₀ + Real.sqrt S₁) ^ 2 := by
  have htri := pretDist_triangle (f := costwist t₀) (g := f) (h := costwist v) X
    (norm_costwist_le t₀) hf (norm_costwist_le v)
  have e0 : pretDist (costwist t₀) f X ≤ Real.sqrt S₀ := by
    rw [pretDist_comm]; unfold pretDist; exact Real.sqrt_le_sqrt h0
  have e1 : pretDist f (costwist v) X ≤ Real.sqrt S₁ := by
    unfold pretDist; exact Real.sqrt_le_sqrt h1
  have hnn : 0 ≤ pretDist (costwist t₀) (costwist v) X := Real.sqrt_nonneg _
  have hsq : pretDist (costwist t₀) (costwist v) X ^ 2
      = pretDistSq (costwist t₀) (costwist v) X :=
    Real.sq_sqrt (pretDistSq_nonneg _ _ _ (norm_costwist_le t₀) (norm_costwist_le v))
  have hle : pretDist (costwist t₀) (costwist v) X ≤ Real.sqrt S₀ + Real.sqrt S₁ := by
    linarith
  rw [← pretDistSq_costwist_shift t₀ v X, ← hsq]
  nlinarith [hnn, hle]

/-- **C-3 (the abstract collision).**  Two caps at *different* grades on the SAME 1-bounded
datum force the two frequencies together: if `𝔻²(f, n^{it₀}; X) ≤ S₀`, `𝔻²(f, n^{iv}; X) ≤ S₁`
and the strict gap

  `(√S₀ + √S₁)² < loglog X − (3/4)loglog(4X+3) − 5·logloglog(4X+16) − C`

holds, then `|v − t₀| < 1`.  (The right side is `dist_one_floor_pow`'s uncapped floor,
evaluated at the worst admissible height `|v − t₀| ≤ 4X`: it is `(1/4 − o(1))·loglog X`.)

The gap hypothesis is IN-STATEMENT (law #253 / ⟦V5⟧ Z-3): the honest `X₀` for the pinned
instance is a tower (the floor's `C` already carries `e^{e^{100}}`), and absorbing it into an
"for `X` large enough" would make the exit vacuous. -/
theorem pocket_collision_abstract :
    ∃ C : ℝ, ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) → ∀ X S₀ S₁ t₀ v : ℝ,
      Real.exp 1 ≤ X → |t₀| ≤ X → |v| ≤ 3 * X →
      pretDistSq f (costwist t₀) X ≤ S₀ →
      pretDistSq f (costwist v) X ≤ S₁ →
      (Real.sqrt S₀ + Real.sqrt S₁) ^ 2 < Real.log (Real.log X)
          - (3 / 4) * Real.log (Real.log (4 * X + 3))
          - 5 * Real.log (Real.log (Real.log (4 * X + 16))) - C →
      |v - t₀| < 1 := by
  obtain ⟨C, hC⟩ := dist_one_floor_pow
  refine ⟨C, fun f hf X S₀ S₁ t₀ v hX ht0 hv hcap0 hcap1 hgap => ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have hshift := dist_one_shift_le_of_two_caps_asym hf hcap0 hcap1
  have hfloor := hC X (v - t₀) hX hcon
  have hb0 : (0 : ℝ) ≤ |v - t₀| := abs_nonneg _
  have hb4 : |v - t₀| ≤ 4 * X := by
    obtain ⟨hv1, hv2⟩ := abs_le.mp hv
    obtain ⟨ht1, ht2⟩ := abs_le.mp ht0
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hX2 : (2 : ℝ) ≤ X := by
    have h := Real.add_one_le_exp (1 : ℝ); linarith
  have hmon3 : Real.log (Real.log (|v - t₀| + 3)) ≤ Real.log (Real.log (4 * X + 3)) := by
    have hpos : (0 : ℝ) < Real.log (|v - t₀| + 3) := Real.log_pos (by linarith)
    exact Real.log_le_log hpos (Real.log_le_log (by linarith) (by linarith))
  have hmon16 : Real.log (Real.log (Real.log (|v - t₀| + 16)))
      ≤ Real.log (Real.log (Real.log (4 * X + 16))) := by
    have he16 : Real.exp 1 < |v - t₀| + 16 := by
      have h := Real.exp_one_lt_d9; linarith
    have h1 : (1 : ℝ) < Real.log (|v - t₀| + 16) := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ < Real.log (|v - t₀| + 16) := Real.log_lt_log (Real.exp_pos 1) he16
    have hpos : (0 : ℝ) < Real.log (Real.log (|v - t₀| + 16)) := Real.log_pos h1
    refine Real.log_le_log hpos (Real.log_le_log (by linarith) ?_)
    exact Real.log_le_log (by linarith) (by linarith)
  linarith [hfloor, hshift, hmon3, hmon16, hgap]

/-- **C-3 — THE COLLISION LEMMA (the live form).**  The U-7 CASE-B dichotomy input.

Hypotheses: the row's cap `hMcap` on the UNDAMPED `ellLin`-datum at `t₁`; a POCKET of the
`x`-DAMPED datum (`RamWeight.gxDatum`) at `t₁'`; and `W`, any bound for the block-window mass
`Σ_{P ≤ p ≤ Q, p ≤ X} 1/p` — which by `RamWeight.gxDatum_pretDistSq_costwist` is the *entire*
price of the damping (C-1 evaluates it: `W = θ·loglog X + 25`).

Conclusion: `|t₁' − t₁| < 1` — the pocket cannot run away from the row's center.

Route: the damping loss releases the pocket back onto the undamped datum
(`𝔻²(ellLin g, n^{it₁'}) ≤ S₂ + W`), which is the second cap the asymmetric two-cap triangle
wants; the resulting `𝔻²(1, n^{i(t₁'−t₁)}) ≤ (√S₁ + √(S₂+W))²` collides with
`dist_one_floor_pow` at `|t₁'−t₁| ≥ 1`. -/
theorem pocket_collision :
    ∃ C : ℝ, ∀ g : ℕ → ℂ, (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → ∀ (P Q : ℕ),
      ∀ X x t₁ t₁' S₁ S₂ W : ℝ,
      Real.exp 1 ≤ X → 0 ≤ x → x ≤ 1 → |t₁| ≤ X → |t₁'| ≤ 3 * X →
      pretDistSq (ellLin g) (costwist t₁) X ≤ S₁ →
      pretDistSq (ellLin (gxDatum g P Q x)) (costwist t₁') X ≤ S₂ →
      (∑ p ∈ blockWindowPrimes P Q X, (1 : ℝ) / (p : ℝ)) ≤ W →
      (Real.sqrt S₁ + Real.sqrt (S₂ + W)) ^ 2 < Real.log (Real.log X)
          - (3 / 4) * Real.log (Real.log (4 * X + 3))
          - 5 * Real.log (Real.log (Real.log (4 * X + 16))) - C →
      |t₁' - t₁| < 1 := by
  obtain ⟨C, hC⟩ := pocket_collision_abstract
  refine ⟨C, fun g hg P Q X x t₁ t₁' S₁ S₂ W hX hx0 hx1 ht1 ht1' hMcap hpocket hW hgap => ?_⟩
  have hf : ∀ n : ℕ, ‖ellLin g n‖ ≤ 1 := fun n => ellLin_norm_le_one g hg n
  -- the damping loss releases the pocket onto the undamped datum
  have hloss := gxDatum_pretDistSq_costwist (g := g) (P := P) (Q := Q) (x := x) (X := X)
    (t := t₁') hx0 hx1 hg
  have hcap2 : pretDistSq (ellLin g) (costwist t₁') X ≤ S₂ + W := by linarith
  exact hC (ellLin g) hf X S₁ (S₂ + W) t₁ t₁' hX ht1 ht1' hMcap hcap2 hgap

/-! ### The pinned numerals and the explicit `X₀` gate -/

/-- **THE COLLISION `X₀` GATE** (⟦V5⟧ Z-3, named and never absorbed).  At the pin the
collision's margin is `(1/4 − (3+2√2)/32)·loglog X ≥ 0.0678·loglog X`
(`collision_margin`); the gate says that margin outweighs

* the cross term `2K·√(C_w·loglog X) ≤ 0.8536·√C_w·√loglog X` of the window constant,
* the window constant `C_w` itself (C-1's `25`),
* the floor's height drift `(3/4)(loglog(4X+3) − loglog X)`,
* the floor's `5·logloglog(4X+16)`, and
* the floor's absolute constant `C` (which already carries the `e^{e^{100}}` tower).

Nothing here is `o(1)`-absorbed: this is the honest `X₀` of the U-7 CASE-B arm. -/
def collisionGate (X Cw C : ℝ) : Prop :=
  (0.8536 : ℝ) * Real.sqrt Cw * Real.sqrt (Real.log (Real.log X)) + Cw
      + (3 / 4) * (Real.log (Real.log (4 * X + 3)) - Real.log (Real.log X))
      + 5 * Real.log (Real.log (Real.log (4 * X + 16))) + C
    < (0.0678 : ℝ) * Real.log (Real.log X)

/-- `√2 ≤ 1.41422`. -/
private lemma sqrt_two_le : Real.sqrt 2 ≤ 1.41422 := by
  rw [show (1.41422 : ℝ) = Real.sqrt (1.41422 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- **THE COLLISION MARGIN — the numeral that makes CASE B work.**

`(√(1/16) + √(1/32))² = 3/32 + √2/16 = 0.182138… ≤ 0.1822`, so against the floor's `1/4` the
collision has an absolute margin of `0.0678` per unit of `loglog X`.

(The symmetric stone `dist_one_shift_le_of_two_caps` would give `4·(1/16) = 1/4` here — EXACTLY
the floor, with no margin at all.  This numeral is the whole reason C-3 needs the asymmetric
triangle.) -/
theorem collision_margin : ((1 : ℝ) / 4 + Real.sqrt 2 / 8) ^ 2 + 0.0678 ≤ 1 / 4 := by
  have h2 := sqrt_two_le
  have h2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [h2, h2nn, hsq]

/-- The cross-term coefficient: `2·(1/4 + √2/8) ≤ 0.8536`. -/
theorem collision_cross_le : 2 * ((1 : ℝ) / 4 + Real.sqrt 2 / 8) ≤ 0.8536 := by
  have h2 := sqrt_two_le; linarith

/-- The pinned collision arithmetic, in pure real variables (`sl = √L`, `sc = √C_w`,
`K = 1/4 + √2/8`, `G` the collected `o(loglog)` corrections).  Kept `√`-free so the numeral
work is polynomial. -/
private lemma collision_arith {A L Cw sl sc K G : ℝ}
    (hsl0 : 0 ≤ sl) (hsc0 : 0 ≤ sc)
    (hslsq : sl ^ 2 = L) (hscsq : sc ^ 2 = Cw)
    (hK2 : K ^ 2 + 0.0678 ≤ 1 / 4) (hKcross : 2 * K ≤ 0.8536)
    (hA0 : 0 ≤ A) (hAB : A ≤ K * sl + sc)
    (hgate : 0.8536 * sc * sl + Cw + G < 0.0678 * L) :
    A ^ 2 < 1 / 4 * L - G := by
  have hL0 : (0 : ℝ) ≤ L := by rw [← hslsq]; positivity
  have hprod : (0 : ℝ) ≤ sl * sc := mul_nonneg hsl0 hsc0
  have h1 : A ^ 2 ≤ (K * sl + sc) ^ 2 := by nlinarith [hA0, hAB]
  have h2 : (K * sl + sc) ^ 2 = K ^ 2 * L + 2 * K * (sl * sc) + Cw := by
    have hid : (K * sl + sc) ^ 2 = K ^ 2 * sl ^ 2 + 2 * K * (sl * sc) + sc ^ 2 := by ring
    rw [hid, hslsq, hscsq]
  have h3 : K ^ 2 * L ≤ (1 / 4 - 0.0678) * L := by nlinarith [hK2, hL0]
  have h4 : 2 * K * (sl * sc) ≤ 0.8536 * (sl * sc) := by nlinarith [hKcross, hprod]
  have h5 : sl * sc = sc * sl := mul_comm _ _
  linarith [h1, h2.le, h2.ge, h3, h4, hgate, h5]

/-- **C-3 AT THE PIN — the CASE-B input, with every numeral discharged.**

On the row the cap is at grade `1/16`; the damped co-factor's pocket is at grade `1/32 − θ`;
C-1 prices the damping at `θ·loglog X + C_w`.  The two grades therefore collide at
`(√(1/16) + √(1/32))² · loglog X` — the `θ` cancels EXACTLY (that is what the ⟦V5⟧ pin is
for) — which `collision_margin` puts `0.0678·loglog X` below the floor.  Under the named gate
`collisionGate` (which is where the `X₀` tower lives, Z-3) the pocket center is pinned:

  `|t₁' − t₁| < 1`. -/
theorem pocket_collision_pin :
    ∃ C : ℝ, ∀ g : ℕ → ℂ, (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → ∀ (P Q : ℕ),
      ∀ X x θ Cw t₁ t₁' : ℝ,
      Real.exp 1 ≤ X → 1 ≤ Real.log (Real.log X) →
      0 ≤ x → x ≤ 1 → 0 ≤ θ → θ ≤ 1 / 32 → 0 ≤ Cw →
      |t₁| ≤ X → |t₁'| ≤ 3 * X →
      pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
      pretDistSq (ellLin (gxDatum g P Q x)) (costwist t₁') X
          ≤ (1 / 32 - θ) * Real.log (Real.log X) →
      (∑ p ∈ blockWindowPrimes P Q X, (1 : ℝ) / (p : ℝ))
          ≤ θ * Real.log (Real.log X) + Cw →
      collisionGate X Cw C →
      |t₁' - t₁| < 1 := by
  obtain ⟨C, hC⟩ := pocket_collision
  refine ⟨C, fun g hg P Q X x θ Cw t₁ t₁' hX hLL1 hx0 hx1 _hθ0 hθ32 hCw0 ht1 ht1'
    hMcap hpocket hW hgate => ?_⟩
  unfold collisionGate at hgate
  have hL0 : (0 : ℝ) ≤ Real.log (Real.log X) := by linarith
  have hsl0 : (0 : ℝ) ≤ Real.sqrt (Real.log (Real.log X)) := Real.sqrt_nonneg _
  have hsc0 : (0 : ℝ) ≤ Real.sqrt Cw := Real.sqrt_nonneg _
  have hslsq : Real.sqrt (Real.log (Real.log X)) ^ 2 = Real.log (Real.log X) := Real.sq_sqrt hL0
  have hscsq : Real.sqrt Cw ^ 2 = Cw := Real.sq_sqrt hCw0
  -- the two root evaluations
  have h16 : Real.sqrt ((1 : ℝ) / 16) = 1 / 4 := by
    rw [show ((1 : ℝ) / 16) = (1 / 4) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h32 : Real.sqrt ((1 : ℝ) / 32) = Real.sqrt 2 / 8 := by
    rw [show ((1 : ℝ) / 32) = (Real.sqrt 2 / 8) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num]
    exact Real.sqrt_sq (by positivity)
  have hs1 : Real.sqrt ((1 / 16 : ℝ) * Real.log (Real.log X))
      = 1 / 4 * Real.sqrt (Real.log (Real.log X)) := by
    rw [Real.sqrt_mul (by norm_num), h16]
  have hs2 : Real.sqrt ((1 / 32 : ℝ) * Real.log (Real.log X))
      = Real.sqrt 2 / 8 * Real.sqrt (Real.log (Real.log X)) := by
    rw [Real.sqrt_mul (by norm_num), h32]
  -- the collapse of the two grades: the `θ` cancels EXACTLY (the ⟦V5⟧ pin)
  have hcollapse : (1 / 32 - θ) * Real.log (Real.log X)
        + (θ * Real.log (Real.log X) + Cw)
      = (1 / 32 : ℝ) * Real.log (Real.log X) + Cw := by ring
  have hroot2 : Real.sqrt ((1 / 32 - θ) * Real.log (Real.log X)
        + (θ * Real.log (Real.log X) + Cw))
      ≤ Real.sqrt 2 / 8 * Real.sqrt (Real.log (Real.log X)) + Real.sqrt Cw := by
    rw [hcollapse]
    refine le_trans (sqrt_add_le_add_sqrt
      (by linarith : (0 : ℝ) ≤ (1 / 32 : ℝ) * Real.log (Real.log X)) hCw0) ?_
    rw [hs2]
  have hA0 : (0 : ℝ) ≤ Real.sqrt ((1 / 16 : ℝ) * Real.log (Real.log X))
      + Real.sqrt ((1 / 32 - θ) * Real.log (Real.log X)
        + (θ * Real.log (Real.log X) + Cw)) := by positivity
  have hAB : Real.sqrt ((1 / 16 : ℝ) * Real.log (Real.log X))
        + Real.sqrt ((1 / 32 - θ) * Real.log (Real.log X)
          + (θ * Real.log (Real.log X) + Cw))
      ≤ (1 / 4 + Real.sqrt 2 / 8) * Real.sqrt (Real.log (Real.log X)) + Real.sqrt Cw := by
    rw [hs1]; nlinarith [hroot2]
  -- hand the strict gap to the collision
  refine hC g hg P Q X x t₁ t₁' ((1 / 16 : ℝ) * Real.log (Real.log X))
    ((1 / 32 - θ) * Real.log (Real.log X)) (θ * Real.log (Real.log X) + Cw)
    hX hx0 hx1 ht1 ht1' hMcap hpocket hW ?_
  have hkey := collision_arith (L := Real.log (Real.log X)) (Cw := Cw)
    (sl := Real.sqrt (Real.log (Real.log X))) (sc := Real.sqrt Cw)
    (K := 1 / 4 + Real.sqrt 2 / 8)
    (G := 3 / 4 * (Real.log (Real.log (4 * X + 3)) - Real.log (Real.log X))
        + 5 * Real.log (Real.log (Real.log (4 * X + 16))) + C)
    hsl0 hsc0 hslsq hscsq collision_margin collision_cross_le hA0 hAB (by linarith)
  linarith [hkey]

/-- **THE GATE, SPLIT INTO FIVE STATED THRESHOLDS.**  `collisionGate` holds as soon as each
of its five charges is under `0.0135·loglog X` (five of them fit inside the `0.0678` margin
with room to spare).  This is the form a consumer checks, and it exhibits exactly where the
`X₀` tower comes from: charge (5) is the floor's own constant, which already carries
`log(5 + 2e^{e^{100}}) ≈ e^{100} ≈ 2.7·10^{43}`, so `C ≤ 0.0135·loglog X` alone forces
`loglog X ≳ 2·10^{45}`, i.e. `X ≳ exp exp(2·10^{45})` — the ⟦V5⟧ Z-3 tower, in the open. -/
theorem collisionGate_of_five (X Cw C : ℝ) (hL : 0 < Real.log (Real.log X))
    (h1 : (0.8536 : ℝ) * Real.sqrt Cw * Real.sqrt (Real.log (Real.log X))
      ≤ 0.0135 * Real.log (Real.log X))
    (h2 : Cw ≤ 0.0135 * Real.log (Real.log X))
    (h3 : (3 / 4) * (Real.log (Real.log (4 * X + 3)) - Real.log (Real.log X))
      ≤ 0.0135 * Real.log (Real.log X))
    (h4 : 5 * Real.log (Real.log (Real.log (4 * X + 16)))
      ≤ 0.0135 * Real.log (Real.log X))
    (h5 : C ≤ 0.0135 * Real.log (Real.log X)) :
    collisionGate X Cw C := by
  unfold collisionGate
  linarith

/-- **C-3 COMPOSED WITH C-1 — the single stone U7-D consumes.**  The window mass is no longer
a hypothesis: at the §8.3 endpoints C-1 supplies it (`W = θ·loglog X + 25`), and the `θ`
cancels against the co-factor's `1/32 − θ` grade exactly.  What is left is the row cap, the
pocket, and the named gate. -/
theorem pocket_collision_window :
    ∃ C : ℝ, ∀ g : ℕ → ℂ, (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → ∀ (P Q : ℕ),
      ∀ X x θ t₁ t₁' : ℝ,
      Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 0 < θ → θ ≤ 1 / 32 →
      0 ≤ x → x ≤ 1 →
      P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q →
      |t₁| ≤ X → |t₁'| ≤ 3 * X →
      pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
      pretDistSq (ellLin (gxDatum g P Q x)) (costwist t₁') X
          ≤ (1 / 32 - θ) * Real.log (Real.log X) →
      collisionGate X 25 C →
      |t₁' - t₁| < 1 := by
  obtain ⟨C, hC⟩ := pocket_collision_pin
  refine ⟨C, fun g hg P Q X x θ t₁ t₁' hX hLX hθ0 hθ32 hx0 hx1 hPlow hQhigh hPQ ht1 ht1'
    hMcap hpocket hgate => ?_⟩
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log (Real.exp_pos 1) hLX; rwa [Real.log_exp] at h
  have hW := blockWindow_mertens_pin P Q X θ hθ0 (by linarith) hLX hPlow hQhigh hPQ
  exact hC g hg P Q X x θ 25 t₁ t₁' hX hLL1 hx0 hx1 (le_of_lt hθ0) hθ32 (by norm_num)
    ht1 ht1' hMcap hpocket hW hgate

/-! ## §4 (C-4) — the ball corollaries the U7-D arm consumes -/

/-- **C-4 (the far form).**  Once the collision has pinned the pocket center `t₁'` to within
`1` of the row center `t₁`, everything at distance `≥ R` from `t₁` is at distance `> R − 1`
from `t₁'`.  (Instantiated at `R = seamRad X` this is the CASE-B radius input: the seam ball
around the row center is, up to the harmless `−1`, a seam ball around the pocket.) -/
theorem pocket_far_from_ball {t t₁ t₁' R : ℝ} (hcoll : |t₁' - t₁| < 1) (hfar : R ≤ |t - t₁|) :
    R - 1 < |t - t₁'| := by
  have h := abs_sub_abs_le_abs_sub (t - t₁) (t - t₁')
  have h2 : (t - t₁) - (t - t₁') = t₁' - t₁ := by ring
  rw [h2] at h
  linarith

/-- **C-4 (the near form).**  Dually: a ball of radius `R` around the pocket center sits inside
the ball of radius `R + 1` around the row center — the transfer direction U7-D uses to move a
pocket bound onto the row's own ball. -/
theorem pocket_ball_shrink {t t₁ t₁' R : ℝ} (hcoll : |t₁' - t₁| < 1) (hin : |t - t₁'| ≤ R) :
    |t - t₁| < R + 1 := by
  have h : |t - t₁| ≤ |t - t₁'| + |t₁' - t₁| := by
    rw [show t - t₁ = (t - t₁') + (t₁' - t₁) by ring]
    exact abs_add_le _ _
  linarith

end Salt.MR
