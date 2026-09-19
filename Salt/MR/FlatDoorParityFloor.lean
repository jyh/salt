/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FlatDoorAllGrades
import Mathlib

/-!
# ⟦TIER S — ROAD F: THE `ξ = 0` TERM OF THE `L²` DOOR IS `≥ 1/H²` AT ODD `H`⟧
(`FlatDoorParityFloor`)

`FlatDoorNonVacuity` proved that the flat regimes can be taken with `0 ∈ Ξ_H` at every `H` the
door quantifies over, and said in its own header that this is only HALF of non-vacuity: the term
is in the sum, and nothing there says the term is positive.  This file is the other half.

* THE PARITY FLOOR.  `windowExpSum H n 0` is the integer sum of the `H` Liouville values
  `λ(n+1), …, λ(n+H)` (`crownK6_windowExpSum_zero`); each value is `±1`, so at ODD `H` the sum is
  odd (`crownK6_window_sum_odd`), hence of norm `≥ 1` (`crownK6_one_le_norm_of_odd`); against the
  probability measure `logMeasure R.x R.ω` that gives `1 ≤ ∫ ‖windowExpSum H n 0‖²`
  (`crownK6_integral_floor`).  No condition on `n` is used: the argument `n + i + 1` is never `0`.
* AN ODD `H` IS IN RANGE, FOR EVERY REGIME.  `hJcon` forces `1 ≤ R.J` (an empty drop sum is `0`,
  and `log 2 < 0` is false), the first tower step at least doubles, and `hfit` puts it under
  `R.Hhi`: so `R.Hlo + 1 ≤ R.Hhi` (`crownK6_Hlo_succ_le_Hhi`) and one of `R.Hlo`, `R.Hlo + 1` is
  odd (`crownK6_odd_in_range`).
* THE GRADE FLOOR.  A regime with `0 ∈ Ξ_H` on its range carries the door only at grades
  `ρ ≥ 1/(R.Hlo + 1)²` (`crownK6_grade_floor`), so it does NOT carry the door at every grade
  (`crownK6_not_every_grade`); `crownK6_flat_order_forced` says this of every flat regime above
  `FlatDoorNonVacuity`'s floors, and `crownK6_Wdelta_regime_moves` is the control that the class
  is inhabited — by W-δ's own regime.

WHAT THIS BUYS.  W-δ (`FlatDoorAllGradesW`) has the shape `∀ ρ … ∃ R`.  On the flat family above
the floors the other order, `∃ R ∀ ρ`, is FALSE: the regime has to move with the grade.

⚠ WHAT THIS DOES NOT SAY.  The floor `H₀` is `FlatDoorNonVacuity`'s and is NON-EFFECTIVE, and a
regime lying below it is out of reach: `¬ ∃ R, ∀ ρ > 0, MRTUniformityXiL2 R ρ` over ALL regimes
is NOT proved.  W-δ's truth never depended on any of this — `∃ R ∀ ρ` would IMPLY W-δ.  Even `H`
is untouched (an even number of `±1` values can sum to `0`).  Nothing here bears on twin primes.
-/

noncomputable section

open MeasureTheory
open Salt.Entropy.Chowla
open scoped BigOperators

namespace Salt.MR

/-- **⟦`windowExpSum` AT FREQUENCY `0`⟧** (`crownK6_windowExpSum_zero`) — every phase is `1`, so
the window exponential sum is the integer sum of the window's Liouville values, cast to `ℂ`. -/
theorem crownK6_windowExpSum_zero (H n : ℕ) :
    windowExpSum H n 0 = ((∑ i : Fin H, liouvilleWindow H n i : ℤ) : ℂ) := by
  unfold windowExpSum
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp

/-- **⟦THE PARITY OF A WINDOW SUM⟧** (`crownK6_window_sum_odd`) — each `liouvilleWindow H n i` is
`±1`, hence `≡ 1 (mod 2)`; a sum of an odd number `H` of them is odd. -/
theorem crownK6_window_sum_odd {H : ℕ} (hH : Odd H) (n : ℕ) :
    Odd (∑ i : Fin H, liouvilleWindow H n i) := by
  have hterm : ∀ i : Fin H, liouvilleWindow H n i % 2 = 1 := by
    intro i
    have hmem := liouville_mem_pm_one (m := n + (i : ℕ) + 1) (by omega)
    rw [liouvilleWindow_apply]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h <;> rw [h] <;> norm_num
  have hHZ : ((H : ℕ) : ℤ) % 2 = 1 := Int.odd_iff.mp (by exact_mod_cast hH)
  rw [Int.odd_iff, Finset.sum_int_mod, Finset.sum_congr rfl (fun i _ => hterm i)]
  simpa using hHZ

/-- **⟦AN ODD INTEGER HAS NORM `≥ 1`⟧** (`crownK6_one_le_norm_of_odd`). -/
theorem crownK6_one_le_norm_of_odd {z : ℤ} (hz : Odd z) : (1 : ℝ) ≤ ‖(z : ℂ)‖ := by
  have hz0 : z ≠ 0 := by
    obtain ⟨k, hk⟩ := hz
    omega
  have h1 : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
  rw [Complex.norm_intCast]
  exact_mod_cast h1

/-- **⟦THE PARITY FLOOR ON THE INTEGRAL⟧** (`crownK6_integral_floor`) — at odd `H` the integrand
`‖windowExpSum H n 0‖²` is `≥ 1` at EVERY `n`, and `logMeasure R.x R.ω` is a probability measure
(`isProbabilityMeasure_logMeasure`, from the structure fields `R.hx`, `R.hω`). -/
theorem crownK6_integral_floor (R : ChowlaRegime) {H : ℕ} (hH : Odd H) :
    (1 : ℝ) ≤ ∫ n, ‖windowExpSum H n 0‖ ^ 2 ∂(logMeasure R.x R.ω) := by
  haveI hpm : IsProbabilityMeasure (logMeasure R.x R.ω) :=
    isProbabilityMeasure_logMeasure R.hx R.hω
  have hint : Integrable (fun n => ‖windowExpSum H n 0‖ ^ 2) (logMeasure R.x R.ω) :=
    ProbabilityTheory.integrable_of_finiteSupport _
  have hpt : ∀ n, (1 : ℝ) ≤ ‖windowExpSum H n 0‖ ^ 2 := by
    intro n
    rw [crownK6_windowExpSum_zero]
    have h1 := crownK6_one_le_norm_of_odd (crownK6_window_sum_odd hH n)
    nlinarith [norm_nonneg ((∑ i : Fin H, liouvilleWindow H n i : ℤ) : ℂ)]
  calc (1 : ℝ) = ∫ _n, (1 : ℝ) ∂(logMeasure R.x R.ω) := by simp
    _ ≤ ∫ n, ‖windowExpSum H n 0‖ ^ 2 ∂(logMeasure R.x R.ω) :=
        integral_mono (integrable_const _) hint hpt

/-- **⟦THE TOWER HAS A STEP⟧** (`crownK6_one_le_J`) — `R.hJcon` reads `log 2 < towerDropSum …`,
a sum over `Finset.range R.J`; at `R.J = 0` it would read `log 2 < 0`. -/
theorem crownK6_one_le_J (R : ChowlaRegime) : 1 ≤ R.J := by
  by_contra h
  have hJ : R.J = 0 := by omega
  have h2 := R.hJcon
  rw [hJ] at h2
  unfold towerDropSum at h2
  simp only [Finset.range_zero, Finset.sum_empty] at h2
  exact absurd h2 (not_lt.mpr (Real.log_nonneg (by norm_num)))

/-- **⟦THE RANGE HOLDS TWO CONSECUTIVE INTEGERS⟧** (`crownK6_Hlo_succ_le_Hhi`) — the first tower
step multiplies by `≥ 2` (`tower_mult_ge_two`), the tower's base is `≥ R.Hlo`
(`chowlaTower_ge`), and `chowlaTower_le_Hhi` puts step `1` under `R.Hhi`. -/
theorem crownK6_Hlo_succ_le_Hhi (R : ChowlaRegime) : R.Hlo + 1 ≤ R.Hhi := by
  have h1 : chowlaTower R.C0 R.a R.Hlo 1 ≤ R.Hhi := chowlaTower_le_Hhi R (crownK6_one_le_J R)
  have h0 : R.Hlo ≤ chowlaTower R.C0 R.a R.Hlo 0 := chowlaTower_ge R 0
  have hfloor : 4000000 ≤ chowlaTower R.C0 R.a R.Hlo 0 := le_trans R.hHlo_floor h0
  have hmult := tower_mult_ge_two R.hC0 hfloor
  have hs : chowlaTower R.C0 R.a R.Hlo 1
      = chowlaTower R.C0 R.a R.Hlo 0
        * ⌊(R.C0 : ℝ) * Real.log (chowlaTower R.C0 R.a R.Hlo 0 : ℝ)
            * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo 0 : ℝ)))⌋₊ :=
    chowlaTower_succ R.C0 R.a R.Hlo 0
  have hstep : chowlaTower R.C0 R.a R.Hlo 0 * 2 ≤ chowlaTower R.C0 R.a R.Hlo 1 := by
    rw [hs]
    exact Nat.mul_le_mul_left _ hmult
  have hfl := R.hHlo_floor
  omega

/-- **⟦AN ODD `H` IN RANGE⟧** (`crownK6_odd_in_range`) — one of `R.Hlo`, `R.Hlo + 1` is odd, and
both are in `[R.Hlo, R.Hhi]`.  Holds for EVERY `ChowlaRegime`. -/
theorem crownK6_odd_in_range (R : ChowlaRegime) :
    ∃ H : ℕ, Odd H ∧ R.Hlo ≤ H ∧ H ≤ R.Hlo + 1 ∧ H ≤ R.Hhi := by
  have hsucc := crownK6_Hlo_succ_le_Hhi R
  rcases Nat.even_or_odd R.Hlo with he | ho
  · exact ⟨R.Hlo + 1, he.add_one, Nat.le_succ _, le_rfl, hsucc⟩
  · exact ⟨R.Hlo, ho, le_rfl, Nat.le_succ _, le_trans (Nat.le_succ _) hsucc⟩

/-- **⟦THE GRADE FLOOR AT ONE ODD `H`⟧** (`crownK6_grade_floor_at`) — at an odd `H` in range with
`0 ∈ Ξ_H`, the door's Ξ-sum is `≥` its `ξ = 0` term (every term is non-negative), and that term
is `≥ 1/H²` by `crownK6_integral_floor`.  So a door at grade `ρ` forces `1/H² ≤ ρ`. -/
theorem crownK6_grade_floor_at (R : ChowlaRegime) {H : ℕ} [NeZero H] (hH : Odd H)
    (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi) (h0 : (0 : ZMod H) ∈ bigXi R.eps H) {ρ : ℝ}
    (hdoor : MRTUniformityXiL2 R ρ) : 1 / (H : ℝ) ^ 2 ≤ ρ := by
  have hterm : (1 / (H : ℝ) ^ 2)
      * ∫ n, ‖windowExpSum H n (-(((0 : ZMod H).val : ℕ) : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω) ≤ ρ := by
    refine le_trans ?_ (hdoor H hlo hhi)
    exact Finset.single_le_sum
      (f := fun ξ' : ZMod H => (1 / (H : ℝ) ^ 2)
        * ∫ n, ‖windowExpSum H n (-(ξ'.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure R.x R.ω))
      (fun ξ' _ => mul_nonneg (by positivity) (integral_nonneg (fun n => by positivity))) h0
  simp only [ZMod.val_zero, Nat.cast_zero, neg_zero, zero_div] at hterm
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast NeZero.pos H
  have hH2 : (0 : ℝ) ≤ 1 / (H : ℝ) ^ 2 := by positivity
  calc 1 / (H : ℝ) ^ 2 = (1 / (H : ℝ) ^ 2) * 1 := (mul_one _).symm
    _ ≤ (1 / (H : ℝ) ^ 2) * ∫ n, ‖windowExpSum H n 0‖ ^ 2 ∂(logMeasure R.x R.ω) :=
        mul_le_mul_of_nonneg_left (crownK6_integral_floor R hH) hH2
    _ ≤ ρ := hterm

/-- **⟦THE GRADE FLOOR OF A REGIME⟧** (`crownK6_grade_floor`) — a regime with `0 ∈ Ξ_H` at every
`H ≥ R.Hlo` carries the `L²` door only at grades `ρ ≥ 1/(R.Hlo + 1)²`: the odd `H` of
`crownK6_odd_in_range` is at most `R.Hlo + 1`. -/
theorem crownK6_grade_floor (R : ChowlaRegime)
    (h0 : ∀ (H : ℕ) [NeZero H], R.Hlo ≤ H → (0 : ZMod H) ∈ bigXi R.eps H) {ρ : ℝ}
    (hdoor : MRTUniformityXiL2 R ρ) : 1 / ((R.Hlo : ℝ) + 1) ^ 2 ≤ ρ := by
  obtain ⟨H, hodd, hlo, hle, hhi⟩ := crownK6_odd_in_range R
  haveI : NeZero H := ⟨by have := R.hHlo_floor; omega⟩
  have hfl := crownK6_grade_floor_at R hodd hlo hhi (h0 H hlo) hdoor
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast NeZero.pos H
  have hHle : (H : ℝ) ≤ (R.Hlo : ℝ) + 1 := by exact_mod_cast hle
  refine le_trans ?_ hfl
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ hHpos.le hHle 2

/-- **⟦NO SUCH REGIME CARRIES THE DOOR AT EVERY GRADE⟧** (`crownK6_not_every_grade`) — the door
fails at `ρ := (1/(R.Hlo + 1)²)/2`. -/
theorem crownK6_not_every_grade (R : ChowlaRegime)
    (h0 : ∀ (H : ℕ) [NeZero H], R.Hlo ≤ H → (0 : ZMod H) ∈ bigXi R.eps H) :
    ¬ ∀ ρ : ℝ, 0 < ρ → MRTUniformityXiL2 R ρ := by
  intro hall
  have hpos : (0 : ℝ) < 1 / ((R.Hlo : ℝ) + 1) ^ 2 := by positivity
  have h := crownK6_grade_floor R h0 (hall _ (half_pos hpos))
  linarith

/-- **⟦ON THE FLAT FAMILY THE ORDER `∀ ρ ∃ R` IS FORCED⟧** (`crownK6_flat_order_forced`) — with
`crownNV_above_flat_floor`'s binders VERBATIM: every regime at `ε` whose `Hlo` is the flat design
base of an `A` above the floors has the grade floor `1/(R.Hlo + 1)² ≤ ρ`, and so does NOT carry
the `L²` door at every grade.  W-δ's regime must move with `ρ`. -/
theorem crownK6_flat_order_forced :
    ∃ H₀ : ℕ, ∀ (ε : ℚ), 0 < ε → ε ≤ 1 / 500 → ∀ A : ℝ, 162 ≤ A → (H₀ : ℝ) ≤ A →
      (2 / (ε : ℝ) ^ 2) ^ 2 ≤ A →
      ∀ R : ChowlaRegime, R.eps = ε → R.Hlo = flatDesignBase A →
        (∀ ρ : ℝ, MRTUniformityXiL2 R ρ → 1 / ((R.Hlo : ℝ) + 1) ^ 2 ≤ ρ) ∧
          ¬ ∀ ρ : ℝ, 0 < ρ → MRTUniformityXiL2 R ρ := by
  obtain ⟨H₀, hfloor⟩ := crownNV_above_flat_floor
  refine ⟨H₀, ?_⟩
  intro ε hε0 hε A hA162 hH₀A hTA R hReps hHlo
  have h0 : ∀ (H : ℕ) [NeZero H], R.Hlo ≤ H → (0 : ZMod H) ∈ bigXi R.eps H := by
    intro H _ hH
    rw [hReps]
    exact hfloor ε hε0 hε A hA162 hH₀A hTA H (hHlo ▸ hH)
  exact ⟨fun ρ hd => crownK6_grade_floor R h0 hd, crownK6_not_every_grade R h0⟩

/-- **⟦THE CONTROL: THE CLASS IS INHABITED, AND IT IS W-δ'S OWN REGIME⟧**
(`crownK6_Wdelta_regime_moves`) — `crownNV_Wdelta_nonvacuous_holds`'s regime at grade `ρ`
carries the door at `ρ`, has the grade floor `1/(R.Hlo + 1)² ≤ ρ`, and does NOT carry the door at
every grade.  So `crownK6_grade_floor`'s hypothesis is met by a landed regime (the floor is not a
statement about an empty class), and as `ρ → 0` the design base `R.Hlo` of W-δ's regime must
grow. -/
theorem crownK6_Wdelta_regime_moves :
    ∀ (ε : ℚ), 0 < ε → ε ≤ 1 / 500 → ∀ ρ : ℝ, 0 < ρ → ∀ A₀ : ℝ,
      ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧
        ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
          MRTUniformityXiL2 R ρ ∧ 1 / ((R.Hlo : ℝ) + 1) ^ 2 ≤ ρ ∧
          ¬ ∀ ρ' : ℝ, 0 < ρ' → MRTUniformityXiL2 R ρ' := by
  intro ε hε0 hε ρ hρ A₀
  obtain ⟨A, hA162, hA₀A, R, hReps, hHlo, -, hdoor, h0⟩ :=
    crownNV_Wdelta_nonvacuous_holds ε hε0 hε ρ hρ A₀
  exact ⟨A, hA162, hA₀A, R, hReps, hHlo, hdoor, crownK6_grade_floor R h0 hdoor,
    crownK6_not_every_grade R h0⟩

end Salt.MR
