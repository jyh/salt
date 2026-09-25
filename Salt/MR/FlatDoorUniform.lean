/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FlatDoorEpsRung2
import Salt.MR.FlatDoorAllGrades
import Salt.MR.DoorReceipt
import Mathlib

/-!
# ⟦TIER S — ROAD F, THE REGIME AXIS: THE UNIFORM FLAT DOOR (CANDIDATE U)⟧ (`FlatDoorUniform`)

**HONEST LABEL, FIRST.**  Nothing here bears on twin primes.  Candidate U is the crown's
quantifier (`∃ H₀ ∀ R`) on the FLAT CLASS: it is IMPLIED by the crown (`nextHopU_of_crown`,
landed here) and it is NOT the crown — the crown quantifies over every `ChowlaRegime`, with no
ceiling and no width law.  No rate is exported.

**THE CLASS.**  Rung 2 (`FlatDoorEpsRung2`) proves the `L²` MRT door at the flat family's BUILT
regime, eight forms `∃ R, [exports] ∧ SLOT` composed by seven hops.  The walk of the road-F
freeze of candidate U read, hop by hop, what those hops use about the built regime: the window's
`ε`, the outer-scale CEILING `log x ≤ (31/ε)·Hhi`, and the WIDTH LAW
`50 ≤ loglog Hlo → loglog Hhi ≤ exp(loglog Hlo / 2)` — the three conjuncts of `FlatClassW`.
Every other export is a floor on `Hlo` (paid by `H₀`), the count (a fact about `ε` and `H`), the
arm (dominated by the structure's own `hPHheadroom`), or `Hlo`-exactness (recovered by the
inversion `A := loglog Hlo / 3.2`, `flatDesignBase_of_loglog_eq`).

**THIS FILE IS HALF 1 OF 2.**  It carries the class and the statement of record
(`FlatClassW`, `FlatDoorUniformW`), their two receipts (U gives the landed W-δ; the crown gives
U), the inversion lemmas, the eight U-forms (rung 2's forms with `∃ R` turned into `∀ R`), the
arm bound from the regime's own fields, and the four pass-through hops.  HALF 2 — the
conditional, kswin and v7 hops, the chain, and the theorem `: FlatDoorUniformW` — is OWED: no
proof of `FlatDoorUniformW` exists in this file.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla

namespace Salt.MR

/-! ## §0 — the class, the statement of record, and the four receipts -/

/-- **THE FLAT CLASS at `ε`** — the THREE regime facts the rung-2 DOOR route reads beyond the
floors (the walk of 2026-09-25): the window's `ε`, the outer-scale CEILING (read at the rated
hop's base-scale cap), and the WIDTH LAW (read at the conditional hop, four sites, and at the
terminal hop's width).  Every other export of the head form is a floor (paid by `H₀`), the count
(paid by `bigXi_bounded_ceiling_eps` at `H ≥ H₀`), the cap (spent only on `Hlo`-exactness, which
`A := loglog Hlo / 3.2` recovers), or the arm (dominated by the structure's own `hPHheadroom`).
Nothing here bears on twin primes. -/
def FlatClassW (ε : ℚ) (R : ChowlaRegime) : Prop :=
  R.eps = ε ∧
  Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
  (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
    Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2))

/-- **CANDIDATE U v1.1 — THE UNIFORM FLAT DOOR**: the crown's quantifier shape `∃ H₀ ∀ R`, on
the flat class. -/
def FlatDoorUniformW : Prop :=
  ∀ (ε : ℚ), 0 < ε → ε ≤ 1 / 500 → ∀ ρ : ℝ, 0 < ρ →
    ∃ H₀ : ℕ, ∀ R : ChowlaRegime, FlatClassW ε R → H₀ ≤ R.Hlo →
      MRTUniformityXiL2 R ρ

/-- the charge, as `flatDoorEpsFamilyW_holds` picks it: `c := ⌈1/(500·ε)⌉₊`. -/
theorem charge_exists (ε : ℚ) (hε0 : 0 < ε) :
    ∃ c : ℕ, 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε := by
  have hεQ0 : (0 : ℚ) < 500 * ε := by linarith
  refine ⟨⌈(1 / (500 * ε) : ℚ)⌉₊, ?_, ?_⟩
  · have h : 0 < ⌈(1 / (500 * ε) : ℚ)⌉₊ := Nat.ceil_pos.mpr (div_pos one_pos hεQ0)
    omega
  · have hle : (1 : ℚ) / (500 * ε) ≤ (⌈(1 / (500 * ε) : ℚ)⌉₊ : ℚ) := Nat.le_ceil _
    have hc1 : (1 : ℚ) ≤ (⌈(1 / (500 * ε) : ℚ)⌉₊ : ℚ) := by
      have h : 0 < ⌈(1 / (500 * ε) : ℚ)⌉₊ := Nat.ceil_pos.mpr (div_pos one_pos hεQ0)
      exact_mod_cast h
    rw [div_le_iff₀ hεQ0] at hle
    rw [div_le_iff₀ (by linarith)]
    linarith

/-- `flatDesignBase` is monotone (inline; the landed `flatDesignBase_mono` lives outside this
module's imports). -/
theorem flatDesignBase_mono' {A A' : ℝ} (h : A ≤ A') :
    flatDesignBase A ≤ flatDesignBase A' := by
  unfold flatDesignBase
  exact Nat.ceil_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith)))

/-- the inversion's floor: `H ≤ flatDesignBase (loglog H / 3.2 + 1)` —
`exp(exp(loglog H + 3.2)) = H^(e^3.2) ≥ H`. -/
theorem le_flatDesignBase_of_loglog {H : ℕ} (hH : 2 ≤ H) :
    H ≤ flatDesignBase (Real.log (Real.log (H : ℝ)) / 3.2 + 1) := by
  have hH1 : (1 : ℝ) < (H : ℝ) := by exact_mod_cast (show 1 < H by omega)
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  have hlogpos : 0 < Real.log (H : ℝ) := Real.log_pos hH1
  have h1 : 3.2 * (Real.log (Real.log (H : ℝ)) / 3.2 + 1)
      = Real.log (Real.log (H : ℝ)) + 3.2 := by
    ring
  have h32 : (1 : ℝ) ≤ Real.exp 3.2 := by
    have := Real.add_one_le_exp (3.2 : ℝ); linarith
  have h2 : Real.log (H : ℝ) ≤ Real.log (H : ℝ) * Real.exp 3.2 :=
    le_mul_of_one_le_right hlogpos.le h32
  have h3 : (H : ℝ)
      ≤ Real.exp (Real.exp (3.2 * (Real.log (Real.log (H : ℝ)) / 3.2 + 1))) := by
    rw [h1, Real.exp_add, Real.exp_log hlogpos]
    calc (H : ℝ) = Real.exp (Real.log (H : ℝ)) := (Real.exp_log hH0).symm
      _ ≤ Real.exp (Real.log (H : ℝ) * Real.exp 3.2) := Real.exp_le_exp.mpr h2
  have h4 : (H : ℝ)
      ≤ ((flatDesignBase (Real.log (Real.log (H : ℝ)) / 3.2 + 1) : ℕ) : ℝ) := by
    unfold flatDesignBase
    exact le_trans h3 (Nat.le_ceil _)
  exact_mod_cast h4

/-- **THE ZERO LEVEL** — U gives the landed W-δ: the rung-2 head form at `P := True` builds a
regime whose exports carry EXACTLY the class's two conjuncts (`hRx`, `hRtow`) beside
`R.eps = ε`; the design constant is raised until the built `Hlo = flatDesignBase A` clears `H₀`
(the inversion's floor), and U's door at that regime is W-δ's. -/
theorem nextHopU_zero_level (hU : FlatDoorUniformW) : FlatDoorAllGradesW := by
  intro ε hε0 hε ρ hρ A₀
  obtain ⟨H₀, hH₀⟩ := hU ε hε0 hε ρ hρ
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  obtain ⟨c, hc1, hcε⟩ := charge_exists ε hε0
  have hc0 : 0 < c := hc1
  have hcQ0 : (0 : ℚ) < 500 * (c : ℚ) := by
    have : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
    linarith
  have hLc0 : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast hc1)
  have hεR : (1 : ℝ) / (500 * (c : ℝ)) ≤ (ε : ℝ) := by
    have hq := hcε
    rw [div_le_iff₀ hcQ0] at hq
    have hcR0 : (0 : ℝ) < 500 * (c : ℝ) := by exact_mod_cast hcQ0
    have h1R : (1 : ℝ) ≤ (ε : ℝ) * (500 * (c : ℝ)) := by exact_mod_cast hq
    rw [div_le_iff₀ hcR0]
    linarith
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have hq : ε ≤ (1 : ℚ) / 2 := le_trans hε (by norm_num)
    have h := (Rat.cast_le (K := ℝ)).mpr hq
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have hhead : FlatHeadFormEpsW ε c (fun _ => True) :=
    flat_head_uniform_xceil_epsW ε hε0 hε hc1 hcε (fun _ => True) (fun _ _ _ _ => trivial)
  obtain ⟨K, δ₀, β, Hopq, -, -, -, -, -, -, -, hβ, hbody⟩ := hhead
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a =
      max (max (max A₀ 162) (max (budgetAFlat (ε : ℝ) β) (10 + 2 * Real.log (c : ℝ))))
        (max (Real.log (Real.log ((max 2 H₀ : ℕ) : ℝ)) / 3.2 + 1)
          (Real.log (Real.log ((max 2 Hopq : ℕ) : ℝ)) / 3.2 + 1)) := ⟨_, rfl⟩
  have hA162 : (162 : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hA₀ : A₀ ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hAbud : budgetAFlat (ε : ℝ) β ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hAL : 10 + 2 * Real.log (c : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hAH₀ : Real.log (Real.log ((max 2 H₀ : ℕ) : ℝ)) / 3.2 + 1 ≤ A := by
    rw [hAdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hAHopq : Real.log (Real.log ((max 2 Hopq : ℕ) : ℝ)) / 3.2 + 1 ≤ A := by
    rw [hAdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hA26 : (26 : ℝ) ≤ A := by linarith
  obtain ⟨Hcap, hCapEq, hR⟩ := hbody A hA26 hAbud hAL
  have hHcapW : max Hcap (max arcFloor36 loglogFloor50) ≤ flatWitFloor ε β A Hopq :=
    flatCap_le_flatWitFloor hCapEq.le
  have hg0 : XCeilRiderAt (50 + Real.log (c : ℝ)) ε (fun _ _ : ℕ => 0) := by
    intro Hhi ω _
    simp only [Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (div_nonneg (by norm_num) hεR0.le) (Nat.cast_nonneg _)
  obtain ⟨R, hReps, -, hU1, -, hRx, -, hRtow, hRcap, -⟩ :=
    hR 0 (flatWitFloor ε β A Hopq) (fun _ _ => 0) hg0
  have hHloLe : R.Hlo ≤ flatWitFloor ε β A Hopq := by
    refine le_trans hRcap (max_le ?_ (max_le (Nat.zero_le _) le_rfl))
    exact le_trans (le_max_left _ _) hHcapW
  have hHloEq : R.Hlo = flatWitFloor ε β A Hopq := le_antisymm hHloLe hU1
  have hopq : Hopq ≤ flatDesignBase A :=
    le_trans (le_max_right 2 Hopq)
      (le_trans (le_flatDesignBase_of_loglog (le_max_left 2 Hopq))
        (flatDesignBase_mono' hAHopq))
  have hWit : flatWitFloor ε β A Hopq = flatDesignBase A :=
    flat_witFloor_eq_designBase_L (h := c) hc0 hLc0 le_rfl hA162 hAL hβ hεR hε2 hε0 hcε
      hAbud hopq
  have hHlo : R.Hlo = flatDesignBase A := by rw [hHloEq, hWit]
  have hH₀le : H₀ ≤ R.Hlo := by
    rw [hHlo]
    exact le_trans (le_max_right 2 H₀)
      (le_trans (le_flatDesignBase_of_loglog (le_max_left 2 H₀)) (flatDesignBase_mono' hAH₀))
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHloEq]; exact flatWitFloor_design ε β A Hopq
  exact ⟨A, hA162, hA₀, R, hReps, hHlo, hdes, hH₀ R ⟨hReps, hRx, hRtow⟩ hH₀le⟩

/-- **THE TRUTH RECEIPT** — the crown gives U: at grade `ρ/K` with `K` the count ceiling at
`H ≥ H₀xi`, the crown's L¹ door at every regime above its floor lifts to the L² door at `ρ` by
the landed bridge.  U is never more than the crown says, on the class or off it. -/
theorem nextHopU_of_crown (hC : MRTDoorAllGrades) : FlatDoorUniformW := by
  intro ε hε0 hε ρ hρ
  obtain ⟨c, hc1, hcε⟩ := charge_exists ε hε0
  obtain ⟨K, hK, -, H₀xi, -, hxi⟩ := bigXi_bounded_ceiling_eps ε hε0 hε hc1 hcε
  have hε2 : ε ≤ (1 : ℚ) / 2 := le_trans hε (by norm_num)
  obtain ⟨H₀c, hcrown⟩ := hC (ρ / K) (div_pos hρ hK) ε hε0 hε2
  refine ⟨max H₀c H₀xi, ?_⟩
  intro R hcls hHlo
  obtain ⟨hReps, -, -⟩ := hcls
  have hL1 : MRTUniformityXi R (ρ / K) := hcrown R hReps (le_trans (le_max_left _ _) hHlo)
  have hXi : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      ((bigXi R.eps H).card : ℝ) ≤ K := by
    intro H _ hlo _
    rw [hReps]
    exact hxi H (le_trans (le_trans (le_max_right _ _) hHlo) hlo)
  have h := mrtUniformityXiL2_of_xi R (div_pos hρ hK).le hXi hL1
  have hKρ : K * (ρ / K) = ρ := by field_simp
  rwa [hKρ] at h

/-! ## §1 — the inversion: at `A := loglog H / 3.2` the flat base is `H` -/

/-- the inversion's equality: at `A := loglog H / 3.2` the flat base IS `H`. -/
theorem flatDesignBase_of_loglog_eq {H : ℕ} (hH : 2 ≤ H) :
    flatDesignBase (Real.log (Real.log (H : ℝ)) / 3.2) = H := by
  have hH1 : (1 : ℝ) < (H : ℝ) := by exact_mod_cast (show 1 < H by omega)
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  have hlogpos : 0 < Real.log (H : ℝ) := Real.log_pos hH1
  have h1 : 3.2 * (Real.log (Real.log (H : ℝ)) / 3.2) = Real.log (Real.log (H : ℝ)) := by
    ring
  unfold flatDesignBase
  rw [h1, Real.exp_log hlogpos, Real.exp_log hH0, Nat.ceil_natCast]

/-- the flat design law at the flat base itself (the `flatWitFloor_design` shape on
`flatDesignBase`). -/
theorem flatDesignBase_design (A : ℝ) :
    3.2 * A ≤ Real.log (Real.log ((flatDesignBase A : ℕ) : ℝ)) := by
  have hy0 : 0 < Real.exp (Real.exp (3.2 * A)) := Real.exp_pos _
  have hceil : Real.exp (Real.exp (3.2 * A))
      ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    unfold flatDesignBase
    exact Nat.le_ceil _
  have hlog1 : Real.exp (3.2 * A) ≤ Real.log ((flatDesignBase A : ℕ) : ℝ) := by
    have h := Real.log_le_log hy0 hceil
    rwa [Real.log_exp] at h
  have h := Real.log_le_log (Real.exp_pos _) hlog1
  rwa [Real.log_exp] at h

/-- the `loglogFloor50` floor sits under the flat base once `A ≥ 162` (`50 ≤ 3.2·162 = 518.4`). -/
theorem loglogFloor50_le_flatDesignBase {A : ℝ} (hA : 162 ≤ A) :
    loglogFloor50 ≤ flatDesignBase A := by
  unfold loglogFloor50 flatDesignBase
  exact Nat.ceil_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith)))

/-- the `arcFloor36 = 10^138` floor sits under the flat base once `A ≥ 162`: symbolically,
`10^138 = exp(138·log 10)`, `log 10 ≤ log 16 = 4·log 2 < 2.7726`, so
`138·log 10 < 382.7 < 519.4 ≤ 3.2·A + 1 ≤ exp(3.2·A)`. -/
theorem arcFloor36_le_flatDesignBase {A : ℝ} (hA : 162 ≤ A) :
    arcFloor36 ≤ flatDesignBase A := by
  have hlog10 : Real.log 10 ≤ 4 * Real.log 2 := by
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    rw [← h16]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hlog2 := Real.log_two_lt_d9
  have hexp : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  have hmain : 138 * Real.log 10 ≤ Real.exp (3.2 * A) := by nlinarith
  have hpow : (10 : ℝ) ^ 138 = Real.exp (138 * Real.log 10) := by
    rw [show (138 : ℝ) * Real.log 10 = ((138 : ℕ) : ℝ) * Real.log 10 by norm_num,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hR : ((arcFloor36 : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by
    unfold arcFloor36
    rw [Nat.cast_pow, Nat.cast_ofNat, hpow]
    exact Real.exp_le_exp.mpr hmain
  have hceil : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    unfold flatDesignBase
    exact Nat.le_ceil _
  exact_mod_cast le_trans hR hceil

end Salt.MR
