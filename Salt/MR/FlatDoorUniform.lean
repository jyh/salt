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

**THIS FILE CARRIES BOTH HALVES.**  It carries the class and the statement of record
(`FlatClassW`, `FlatDoorUniformW`), their two receipts (U gives the landed W-δ; the crown gives
U), the inversion lemmas, the eight U-forms (rung 2's forms with `∃ R` turned into `∀ R`), the
arm bound from the regime's own fields (`s15Arm_le_of_regime`), the seven hops, the head at the
trivial payload, the shrink twin, the chain, and the theorem `flatDoorUniformW_holds :
FlatDoorUniformW` (§5).  *(Until half 2 landed this header read "HALF 1 OF 2 … HALF 2 is OWED";
the socket hop's absence from half 1 and its cause are recorded at §4 and
`docs/blueprints/flags.md`,
both dated, and resolved in §5.)*
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

/-! ## §2 — the eight U-forms: rung 2's forms with `∃ R` turned into `∀ R`

Each form is its rung-2 source (`FlatDoorEpsRung2`) with ONE transformation of the regime clause:
the export conjuncts become hypotheses in the same order, the cap conjunct
`R.Hlo ≤ max Hcap …` is dropped, and the floor binders are replaced by the one floor hypothesis
the form's own hop requests.  Constants, the `A`-quantifier, the `Hcap` clause, the rider and the
slot are the source's, token for token. -/

/-- **the head form, uniform** (`FlatHeadFormU`) — `FlatHeadFormEpsW`
(`FlatDoorEpsRung2.lean:4478`) with its `∃ R` tuple turned into `∀ R` + hypotheses; floor
hypothesis `Hcap ≤ R.Hlo`.  RE-CUT (the freeze's second addendum §2): the COUNT, which the head
PROVES from its floor, is a CONCLUSION conjunct beside the slot, not a hypothesis on `R`. -/
def FlatHeadFormU (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧ 0 < δ₀ ∧
      1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 26 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap = max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (R : ChowlaRegime) (g : ℕ → ℕ → ℕ),
            XCeilRiderAt (50 + Real.log (c : ℝ)) ε g → R.eps = ε → Hcap ≤ R.Hlo →
            g R.Hhi R.ω ≤ R.x →
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((bigXi R.eps H).card : ℝ) ≤ K) ∧
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
              P R

/-- **the socket form, uniform** (`FlatSocketFormU`) — `FlatSocketFormEpsW`
(`FlatDoorEpsRung2.lean:4499`) with its `∃ R` tuple turned into `∀ R` + hypotheses; floor
hypothesis `Hcap ≤ R.Hlo`. -/
def FlatSocketFormU (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧ 0 < δ₀ ∧
      1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (R : ChowlaRegime) (g : ℕ → ℕ → ℕ), XCeilRiderAt (50 + Real.log (c : ℝ)) ε g →
            R.eps = ε → Hcap ≤ R.Hlo → g R.Hhi R.ω ≤ R.x →
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) →
              (∀ (a e : ℕ → ℂ) (Bsieve : ℕ → ℝ) (Binsert : ℝ),
                (∀ m, lamCoeff m = a m + e m) →
                (∀ H : ℕ, 0 ≤ Bsieve H) →
                (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
                  NearRatTight (arcDen 12 H) H α →
                    (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                      ≤ Bsieve H * (H : ℝ) ^ 2) →
                (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
                  (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
                    ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                      ∂(logMeasure R.x R.ω)) ≤ Binsert) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  K * (2 * Bsieve H) + 2 * Binsert ≤ δ₀) →
                P R)

/-- **the `L²` door form, uniform** (`FlatDoorL2FormU`) — `FlatDoorL2FormEpsW`
(`FlatDoorEpsRung2.lean:4529`) with its `∃ R` tuple turned into `∀ R` + hypotheses; floor
hypothesis `Hcap ≤ R.Hlo`. -/
def FlatDoorL2FormU (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg : ℝ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧ 0 < δ₀ ∧
      1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧
      (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (R : ChowlaRegime) (g : ℕ → ℕ → ℕ), XCeilRiderAt (50 + Real.log (c : ℝ)) ε g →
            R.eps = ε → Hcap ≤ R.Hlo → g R.Hhi R.ω ≤ R.x →
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) →
              ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
                M4DoorGates_L_gk K Cg R M k δ →
                (∀ H : ℕ, 0 ≤ Braw H) →
                M4SievedDoorSq_L_gk K R M Braw →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                  P R

/-- **the road form, uniform** (`FlatRoadFormU`) — `FlatRoadFormEpsW`
(`FlatDoorEpsRung2.lean:4554`) with its `∃ R` tuple turned into `∀ R` + hypotheses; floor
hypothesis `Hcap ≤ R.Hlo`. -/
def FlatRoadFormU (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg : ℝ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧ 0 < δ₀ ∧
      1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧
      (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (R : ChowlaRegime) (g : ℕ → ℕ → ℕ), XCeilRiderAt (50 + Real.log (c : ℝ)) ε g →
            R.eps = ε → Hcap ≤ R.Hlo → g R.Hhi R.ω ≤ R.x →
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) →
              ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
                M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
                (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
                (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                    ≤ Braw H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                M4ChiSummedFreeRow_L_gk K R M RS →
                  P R

/-- **the capstone form, uniform** (`FlatCapstoneFormU`) — `FlatCapstoneFormEpsW`
(`FlatDoorEpsRung2.lean:4590`) with its `∃ R` tuple turned into `∀ R` + hypotheses; floor
hypothesis `max Hcap (max arcFloor36 loglogFloor50) ≤ R.Hlo`. -/
def FlatCapstoneFormU (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ) : Prop :=
    ∃ (Cg : ℝ) (Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      Kc ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (R : ChowlaRegime) (g : ℕ → ℕ → ℕ), XCeilRiderAt (50 + Real.log (c : ℝ)) ε g →
              R.eps = ε → max Hcap (max arcFloor36 loglogFloor50) ≤ R.Hlo → g R.Hhi R.ω ≤ R.x →
                Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) →
                ∀ (M : ℕ), Mfl ≤ M → K ≤ 170000000 * M →
                  ∃ C' : ℝ, 0 < C' ∧
                    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                        ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                    ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                      -- ⟦A⟧ THE SPINE ARITHMETIC
                      M4DoorGates_L_gk K Cg R M k δ₀ →
                      8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                          (fun H => 2 * rStrWitness H) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                          (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                          5 ≤ Real.log (Real.log (2 * T)) →
                          (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                            ≤ 8 * (0 : ℝ) ^ 2
                              + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                    \ seamBall (((A + s : ℕ)) : ℝ) 0)
                                  ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                      (calP (AdoorL M) (s13GK K M))
                                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                      (mrAlpha (1 / 12)) 2,
                                  ‖spoly (2 * (A + s))
                                    (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                              + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                                  * (Real.log (((A + s : ℕ)) : ℝ))
                                      ^ (-theta293 + epsrf (A + s)))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        P R

/-- **the conditional form, uniform** (`FlatConditionalFormU`) — `FlatConditionalFormEpsW`
(`FlatDoorEpsRung2.lean:4684`) with its `∃ R` tuple turned into `∀ R` + hypotheses; floor
hypothesis `max Hcap (max arcFloor36 loglogFloor50) ≤ R.Hlo` (the source's `R.Hlo = U1floor`
exactness, spent only on floors).  HALF 2 adds ONE hypothesis on `R` after the floor, the ninth-arm
floor `518 + 6·log c ≤ loglog Hlo` that U-ARM (`s15Arm_le_of_regime`) needs for the hop's arm (a
floor the hop needs is a hypothesis on `R`: the freeze's second addendum §2's principle). -/
def FlatConditionalFormU (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ) : Prop :=
    ∃ (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      Kc ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (R : ChowlaRegime) (g : ℕ → ℕ → ℕ), XCeilRiderStrictAt (50 + Real.log (c : ℝ)) ε g →
            R.eps = ε → max Hcap (max arcFloor36 loglogFloor50) ≤ R.Hlo →
            518 + 6 * Real.log (c : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) → g R.Hhi R.ω ≤ R.x →
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) →
              ∀ M : ℕ,
                S15Sel''_L_gk_T K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                 K ≤ 170000000 * M →
                S15CrossingBound_L_gk K R M → P R

/-- **the kswin form, uniform** (`FlatKswinFormU`) — `FlatKswinFormEpsW`
(`FlatDoorEpsRung2.lean:4709`) with its `∃ R` tuple turned into `∀ R` + hypotheses; floor
hypothesis `R.Hlo = flatDesignBase A` (the source's `R.Hlo = flatWitFloor ε β A Hopq`, under the
form's own witness-floor conjunct), with the two design exports also turned into hypotheses.
HALF 2 adds the ninth-arm floor `518 + 6·log c ≤ loglog Hlo` after the floor, as on the
conditional form (the v7 hop pays it at `A(R) ≥ 162 + 2·log c`). -/
def FlatKswinFormU (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ) : Prop :=
    ∃ (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧
        ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
          K ≤ 170000000 * flatDoorM A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          T₀ ≤ Real.exp (Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ) / 2) →
          Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 →
          ∀ (R : ChowlaRegime) (g : ℕ → ℕ → ℕ), XCeilRiderStrictAt (50 + Real.log (c : ℝ)) ε g →
            R.eps = ε → R.Hlo = flatDesignBase A →
            518 + 6 * Real.log (c : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) → g R.Hhi R.ω ≤ R.x →
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) →
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) →
            (S16CofactorSupply_L_gk K Cq R (flatDoorM A) →
              S16BaseScaleCap96_L_gk K R (flatDoorM A) →
                P R))

/-- **the rated (v7) form, uniform** (`V7RatedFormU`) — `V7RatedFormEpsW`
(`FlatDoorEpsRung2.lean:4738`) with its `∃ R` tuple turned into `∀ R` + hypotheses, RE-CUT (the
road-F freeze of candidate U, its second addendum §3): the design constant `A` is INTERNAL to the
v7 hop, which chooses `A := loglog Hlo / 3.2` for the given regime, so the form exports a FLOOR
`Hfl ≤ R.Hlo` in place of `R.Hlo = flatDesignBase A`; the class's ceiling and width law are the
hypotheses on `R`; no rider. -/
def V7RatedFormU (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg Kc δ₀ Ct β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Hfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧ Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧
      (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ R : ChowlaRegime, R.eps = ε → Hfl ≤ R.Hlo →
        Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) →
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) →
        P R


/-! ## §3 — U-ARM: the conditional hop's arm, from the regime's own fields

The conditional hop reads `s15Arm δ₀ ρ' Hhi ω ≤ x` about the built regime.  At an arbitrary
regime it is paid by the HBUDGET majorant `hPHheadroom` at the NINTH-ARM floor
`518 + 6·log c ≤ loglog Hlo` (never `loglogFloor50` alone: at `loglog Hlo = 50` the arm exceeds
the field for small enough `ρ` or `ε`, both of which U admits).  Every exponent stays symbolic. -/

/-- **⟦U-ARM, the grade⟧** — the conditional hop's grade `ρ' = doorRhoOfDelta (s12DeltaSock δ₀ Kc)`
at the pin `1/(838400·c) ≤ δ₀` and the count ceiling `Kc ≤ 2^283·c^20` has
`0 ≤ log(1/ρ') ≤ 226 + 21·log c`: `1/ρ' ≤ max 1 (16·110525·Kc/δ₀) ≤ 1768400·838400·c·Kc`,
`log (1768400·838400) ≤ 41·log 2 < 28.42` (`1768400·838400 = 1482626560000 ≤ 2^41`), and
`log (2^283·c^20) ≤ 197 + 20·log c` (`epsRung2_log_Kb_le`). -/
theorem uArm_log_inv_grade_le {c : ℕ} (hc1 : 1 ≤ c) {δ₀ Kc : ℝ} (hδ₀ : 0 < δ₀)
    (hδpin : (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀) (hKc : 0 < Kc)
    (hKcb : Kc ≤ 2 ^ 283 * (c : ℝ) ^ 20) :
    0 ≤ Real.log (1 / doorRhoOfDelta (s12DeltaSock δ₀ Kc)) ∧
      Real.log (1 / doorRhoOfDelta (s12DeltaSock δ₀ Kc)) ≤ 226 + 21 * Real.log (c : ℝ) := by
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hc0 : (0 : ℝ) < (c : ℝ) := by linarith
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  obtain ⟨Km, hKmdef⟩ : ∃ Km : ℝ, Km = 2 ^ 283 * (c : ℝ) ^ 20 := ⟨_, rfl⟩
  have hKb : Real.log Km ≤ 197 + 20 * Real.log (c : ℝ) := by
    rw [hKmdef]; exact epsRung2_log_Kb_le hc1
  have hKm1 : (1 : ℝ) ≤ Km := by rw [hKmdef]; exact epsRung2_one_le_Kb hc1
  rw [← hKmdef] at hKcb
  clear hKmdef
  have hδs2 : s12DeltaSock δ₀ Kc ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  obtain ⟨ρ', hρdef⟩ : ∃ ρ' : ℝ, ρ' = doorRhoOfDelta (s12DeltaSock δ₀ Kc) := ⟨_, rfl⟩
  rw [← hρdef]
  have hρ0 : 0 < ρ' := by
    rw [hρdef]; exact doorRhoOfDelta_pos (s12DeltaSock_pos hδ₀ hKc).ne'
  have hρ1 : ρ' ≤ 1 := by rw [hρdef]; exact doorRhoOfDelta_le_one _
  have hinvδ : 1 / δ₀ ≤ 838400 * (c : ℝ) := by
    rw [div_le_iff₀ hδ₀]
    rw [div_le_iff₀ (by positivity)] at hδpin
    linarith
  have hB1 : (1 : ℝ) ≤ 1768400 * 838400 * (c : ℝ) * Km := by
    have h1 : (1 : ℝ) ≤ 1768400 * 838400 * (c : ℝ) := by linarith
    exact one_le_mul_of_one_le_of_one_le h1 hKm1
  have hinvρ : 1 / ρ' ≤ 1768400 * 838400 * (c : ℝ) * Km := by
    rw [hρdef, doorRhoOfDelta, hδs2]
    rcases le_total 1 (δ₀ / (16 * Kc) / 110525) with h | h
    · rw [min_eq_left h]; simpa using hB1
    · rw [min_eq_right h, one_div_div]
      have hstep : 110525 / (δ₀ / (16 * Kc)) = 1768400 * (Kc * (1 / δ₀)) := by
        field_simp
        ring
      rw [hstep]
      have h1 : Kc * (1 / δ₀) ≤ Km * (838400 * (c : ℝ)) :=
        mul_le_mul hKcb hinvδ (by positivity) (by linarith)
      have h2 : 1768400 * (Kc * (1 / δ₀)) ≤ 1768400 * (Km * (838400 * (c : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
      linarith
  refine ⟨Real.log_nonneg (by rw [le_div_iff₀ hρ0]; linarith), ?_⟩
  have hnum : (1768400 * 838400 : ℝ) ≤ 2 ^ 41 := by norm_num
  have hlnum : Real.log (1768400 * 838400 : ℝ) ≤ 41 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num) hnum
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  have hlog := Real.log_le_log (by positivity) hinvρ
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity)] at hlog
  have hsum : Real.log (1768400 * 838400) + Real.log (c : ℝ) + Real.log Km
      ≤ 41 * Real.log 2 + Real.log (c : ℝ) + (197 + 20 * Real.log (c : ℝ)) :=
    add_le_add (add_le_add hlnum le_rfl) hKb
  have hnum2 : 41 * Real.log 2 + Real.log (c : ℝ) + (197 + 20 * Real.log (c : ℝ))
      ≤ 226 + 21 * Real.log (c : ℝ) := by linarith
  exact le_trans hlog (le_trans hsum hnum2)

/-- **⟦U-ARM, the exponent comparison⟧** — in the log-log domain, at the ninth-arm floor
`518 + 6·log c ≤ u` and the grade bound `Λ ≤ 226 + 21·log c`, the arm's exponent
`24·log 2 + 12·u + exp(7000·u + 500·Λ + 6600)` (plus `2`) sits under
`exp(exp u − 12 − 2·log c)`.  With `F := 7000·u + 119600 + 10500·log c` the left side is
`≤ 2·exp F ≤ exp (F + 1)`, and `F + 1 ≤ exp u − 12 − 2·log c` because
`10502·log c ≤ 1751·u`, `119613 ≤ 231·u` and `8982·u ≤ u³/6 ≤ exp u` at `u ≥ 518`. -/
theorem uArm_exponent_le {u Λ Lc : ℝ} (hu : 518 + 6 * Lc ≤ u) (hLc : 0 ≤ Lc)
    (hΛ : Λ ≤ 226 + 21 * Lc) :
    24 * Real.log 2 + 12 * u + Real.exp (7000 * u + 500 * Λ + 6600) + 2
      ≤ Real.exp (Real.exp u - 12 - 2 * Lc) := by
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hu0 : 0 ≤ u := by linarith
  have h518u : (518 : ℝ) ≤ u := by linarith
  have hu2 : (518 : ℝ) * 518 ≤ u * u := mul_le_mul h518u h518u (by norm_num) hu0
  have hu3 : 268324 * u ≤ u ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hu2 hu0
    nlinarith [h]
  have hexpu : u ^ 3 / 6 ≤ Real.exp u := by
    have h := Real.pow_div_factorial_le_exp u hu0 3
    norm_num [Nat.factorial] at h
    linarith
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ, F = 7000 * u + 119600 + 10500 * Lc := ⟨_, rfl⟩
  have hEF : 7000 * u + 500 * Λ + 6600 ≤ F := by rw [hFdef]; linarith
  have hFL : F + 1 ≤ Real.exp u - 12 - 2 * Lc := by rw [hFdef]; linarith
  have hsmall : 24 * Real.log 2 + 12 * u + 2 ≤ Real.exp F := by
    have := Real.add_one_le_exp F
    rw [hFdef] at this ⊢
    linarith
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2F : 2 * Real.exp F ≤ Real.exp (F + 1) := by
    rw [Real.exp_add]
    have := mul_le_mul_of_nonneg_left he1 (Real.exp_pos F).le
    linarith
  have hFW : Real.exp (F + 1) ≤ Real.exp (Real.exp u - 12 - 2 * Lc) := Real.exp_le_exp.mpr hFL
  have hEFe : Real.exp (7000 * u + 500 * Λ + 6600) ≤ Real.exp F := Real.exp_le_exp.mpr hEF
  linarith

/-- **⟦U-ARM⟧ the conditional hop's x-floor, from the regime's OWN fields**: the HBUDGET majorant
`hPHheadroom` (`8·(4^⌊ε²·Hhi⌋₊)²·ω ≤ x`) dominates `s15Arm` at every regime whose `Hlo` clears the
ninth-arm floor `518 + 6·log c ≤ loglog Hlo`.  Per unit `ω` every summand of the arm is at most
`2^27·L^12·exp(exp E)` (`L = log Hhi`, `E = 7000·loglog Hhi + 500·log(1/ρ') + 6600`, using
`Hhi ≤ exp(exp E)`, `c ≤ L`, `128·838400·c` from the pin), and
`2^24·L^12·exp(exp E) = exp(24·log 2 + 12·u + exp E) ≤ exp(2N) ≤ 16^N`, `N = ⌊ε²·Hhi⌋₊`, by
`uArm_exponent_le` and `2N ≥ exp(L − 12 − 2·log c) − 2` (from `ε ≥ 1/(500·c)`). -/
theorem s15Arm_le_of_regime {c : ℕ} (hc1 : 1 ≤ c) {δ₀ Kc : ℝ} (hδ₀ : 0 < δ₀)
    (hδpin : (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀) (hKc : 0 < Kc)
    (hKcb : Kc ≤ 2 ^ 283 * (c : ℝ) ^ 20)
    (R : ChowlaRegime) (hε : (1 : ℚ) / (500 * (c : ℚ)) ≤ R.eps)
    (h518 : 518 + 6 * Real.log (c : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi R.ω ≤ R.x := by
  obtain ⟨hΛ0, hΛ⟩ := uArm_log_inv_grade_le hc1 hδ₀ hδpin hKc hKcb
  clear hKcb
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hc0 : (0 : ℝ) < (c : ℝ) := by linarith
  have hLc0 : 0 ≤ Real.log (c : ℝ) := Real.log_nonneg hcR
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  -- ⟦the scales: `L = log Hhi`, `u = log L`⟧
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hHloHhi : (R.Hlo : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast R.hHlohi
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hlogHlo : 0 < Real.log (R.Hlo : ℝ) := Real.log_pos (by linarith)
  have hlogle : Real.log (R.Hlo : ℝ) ≤ Real.log (R.Hhi : ℝ) :=
    Real.log_le_log (by linarith) hHloHhi
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (R.Hhi : ℝ) := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hLdef]; linarith
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = Real.log L := ⟨_, rfl⟩
  have hu518 : 518 + 6 * Real.log (c : ℝ) ≤ u := by
    rw [hudef, hLdef]; exact le_trans h518 (Real.log_le_log hlogHlo hlogle)
  have hLu : Real.exp u = L := by rw [hudef]; exact Real.exp_log hL0
  have hHL : Real.exp L = (R.Hhi : ℝ) := by rw [hLdef]; exact Real.exp_log hHhi0
  have hu0 : 0 ≤ u := by linarith
  have hcL : (c : ℝ) ≤ L := by
    calc (c : ℝ) = Real.exp (Real.log (c : ℝ)) := (Real.exp_log hc0).symm
      _ ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
      _ = L := hLu
  have hL1 : 1 ≤ L := le_trans hcR hcL
  -- ⟦the arm's exponent `E`, `Q = exp(exp E)`, `P = L^12·Q`⟧
  obtain ⟨ρ', hρdef⟩ : ∃ ρ' : ℝ, ρ' = doorRhoOfDelta (s12DeltaSock δ₀ Kc) := ⟨_, rfl⟩
  rw [← hρdef] at hΛ0 hΛ
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = 7000 * u + 500 * Real.log (1 / ρ') + 6600 := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = Real.exp (Real.exp E) := ⟨_, rfl⟩
  have hLE : L ≤ Real.exp E := by
    rw [← hLu]; exact Real.exp_le_exp.mpr (by rw [hEdef]; linarith)
  have hHQ : (R.Hhi : ℝ) ≤ Q := by
    rw [← hHL, hQdef]; exact Real.exp_le_exp.mpr hLE
  have hL12 : (1 : ℝ) ≤ L ^ 12 := one_le_pow₀ hL1
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = L ^ 12 * Q := ⟨_, rfl⟩
  have hQP : Q ≤ P := by rw [hPdef]; exact le_mul_of_one_le_left (by linarith) hL12
  have hHP : (R.Hhi : ℝ) ≤ P := le_trans hHQ hQP
  have hLH : L ≤ (R.Hhi : ℝ) := by rw [← hHL]; linarith [Real.add_one_le_exp L]
  have hcP : (c : ℝ) ≤ P := by linarith
  have hP1 : 1 ≤ P := by linarith
  -- ⟦the headroom field: `8·(4^N)²·ω ≤ x`, `N = ⌊ε²·Hhi⌋₊`⟧
  have hPH := R.hPHheadroom
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ := ⟨_, rfl⟩
  rw [← hN] at hPH
  have hNlt : (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) < (N : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (R.eps ^ 2 * (R.Hhi : ℚ))
    rw [← hN] at h
    have h' := (Rat.cast_lt (K := ℝ)).mpr h
    push_cast at h'
    exact h'
  have hεR : (1 : ℝ) / (500 * (c : ℝ)) ≤ (R.eps : ℝ) := by
    have h : (((1 : ℚ) / (500 * (c : ℚ)) : ℚ) : ℝ) ≤ ((R.eps : ℚ) : ℝ) := Rat.cast_le.mpr hε
    push_cast at h
    exact h
  have h500 : 1 ≤ 500 * (c : ℝ) * (R.eps : ℝ) := by
    rw [div_le_iff₀ (by positivity)] at hεR; linarith
  have h500sq : 1 ≤ 250000 * (c : ℝ) ^ 2 * (R.eps : ℝ) ^ 2 := by
    calc (1 : ℝ) ≤ (500 * (c : ℝ) * (R.eps : ℝ)) ^ 2 := one_le_pow₀ h500
      _ = 250000 * (c : ℝ) ^ 2 * (R.eps : ℝ) ^ 2 := by ring
  -- ⟦`W = exp(L − 12 − 2·log c)` sits under `2·ε²·Hhi`⟧
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = Real.exp (L - 12 - 2 * Real.log (c : ℝ)) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hWdef]; positivity
  have h125 : 125000 * (c : ℝ) ^ 2 ≤ Real.exp (12 + 2 * Real.log (c : ℝ)) := by
    have hc2 : (c : ℝ) ^ 2 = Real.exp (2 * Real.log (c : ℝ)) := by
      rw [show 2 * Real.log (c : ℝ) = ((2 : ℕ) : ℝ) * Real.log (c : ℝ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hc0]
    have h12 : (125000 : ℝ) ≤ Real.exp 12 := by
      have h217 : (125000 : ℝ) ≤ 2 ^ 17 := by norm_num
      have h17 : Real.exp (17 * Real.log 2) = 2 ^ 17 := by
        rw [show (17 : ℝ) * Real.log 2 = ((17 : ℕ) : ℝ) * Real.log 2 by norm_num,
          Real.exp_nat_mul, Real.exp_log two_pos]
      have hle : Real.exp (17 * Real.log 2) ≤ Real.exp 12 :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    rw [Real.exp_add, hc2]
    exact mul_le_mul_of_nonneg_right h12 (by positivity)
  have hWH : W * (125000 * (c : ℝ) ^ 2) ≤ (R.Hhi : ℝ) := by
    calc W * (125000 * (c : ℝ) ^ 2) ≤ W * Real.exp (12 + 2 * Real.log (c : ℝ)) :=
          mul_le_mul_of_nonneg_left h125 hW0
      _ = (R.Hhi : ℝ) := by
          rw [hWdef, ← Real.exp_add, ← hHL]
          congr 1
          ring
  have hepsH : W / 2 ≤ (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) := by
    have h1 : (R.eps : ℝ) ^ 2 * (W * (125000 * (c : ℝ) ^ 2))
        ≤ (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) := mul_le_mul_of_nonneg_left hWH (sq_nonneg _)
    have h2 : W * (1 / 2) ≤ W * (125000 * (c : ℝ) ^ 2 * (R.eps : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hW0
    linarith
  -- ⟦the exponent comparison⟧
  have hexp := uArm_exponent_le hu518 hLc0 hΛ
  rw [hLu, ← hWdef, ← hEdef] at hexp
  have hkey : 24 * Real.log 2 + 12 * u + Real.exp E ≤ 2 * (N : ℝ) := by linarith
  -- ⟦`2^24·P ≤ (4^N)²`⟧
  have hexpP : 16777216 * P = Real.exp (24 * Real.log 2 + 12 * u + Real.exp E) := by
    rw [Real.exp_add, Real.exp_add, hPdef, hQdef, ← hLu]
    rw [show (24 : ℝ) * Real.log 2 = ((24 : ℕ) : ℝ) * Real.log 2 by norm_num,
      Real.exp_nat_mul, Real.exp_log two_pos]
    rw [show (12 : ℝ) * u = ((12 : ℕ) : ℝ) * u by norm_num, Real.exp_nat_mul]
    ring
  have hY : Real.exp (2 * (N : ℝ)) ≤ ((4 ^ N : ℕ) : ℝ) ^ 2 := by
    have he2 : Real.exp 2 ≤ 16 := by
      have h1 := Real.exp_one_lt_d9
      have h : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have h4 : Real.exp 1 ≤ 4 := by linarith
      rw [h]
      calc Real.exp 1 ^ 2 ≤ 4 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le h4 2
        _ = 16 := by norm_num
    have h16 : ((4 ^ N : ℕ) : ℝ) ^ 2 = (16 : ℝ) ^ N := by
      push_cast
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h16, show 2 * (N : ℝ) = (N : ℝ) * 2 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 2).le he2 N
  have h24P : 16777216 * P ≤ ((4 ^ N : ℕ) : ℝ) ^ 2 := by
    rw [hexpP]; exact le_trans (Real.exp_le_exp.mpr hkey) hY
  -- ⟦the goal, in `ℝ`⟧
  rw [← hρdef, ← Nat.cast_le (α := ℝ)]
  unfold s15Arm s13GArm'
  push_cast
  have hω1 : (1 : ℝ) ≤ (R.ω : ℝ) := by
    have h := R.hω
    exact_mod_cast (by omega : 1 ≤ R.ω)
  have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := by linarith
  have hinvδ : 1 / δ₀ ≤ 838400 * (c : ℝ) := by
    rw [div_le_iff₀ hδ₀]
    rw [div_le_iff₀ (by positivity)] at hδpin
    linarith
  have hceil1 : ((⌈128 * (R.ω : ℝ) / δ₀⌉₊ : ℕ) : ℝ)
      ≤ 128 * 838400 * ((R.ω : ℝ) * (c : ℝ)) + 1 := by
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ 128 * (R.ω : ℝ) / δ₀ by positivity)
    have h2 : 128 * (R.ω : ℝ) / δ₀ = 128 * ((R.ω : ℝ) * (1 / δ₀)) := by ring
    have h3 : (R.ω : ℝ) * (1 / δ₀) ≤ (R.ω : ℝ) * (838400 * (c : ℝ)) :=
      mul_le_mul_of_nonneg_left hinvδ hω0
    linarith
  have hgval : gArmDoorRho 0 0 (R.ω : ℝ) ρ' R.Hhi = 16 * ((R.ω : ℝ) * P) := by
    unfold gArmDoorRho arcDen
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← hLdef, ← hudef]
    simp only [mul_zero, add_zero]
    rw [max_eq_right (by positivity)]
    rw [← hEdef, ← hQdef, hPdef]
    ring
  have hωP0 : 0 ≤ (R.ω : ℝ) * P := mul_nonneg hω0 (by linarith)
  have hceil2 : ((⌈gArmDoorRho 0 0 (R.ω : ℝ) ρ' R.Hhi⌉₊ : ℕ) : ℝ)
      ≤ 16 * ((R.ω : ℝ) * P) + 1 := by
    rw [hgval]
    exact (Nat.ceil_lt_add_one (by linarith)).le
  have hωP : (R.ω : ℝ) ≤ (R.ω : ℝ) * P := le_mul_of_one_le_right hω0 hP1
  have hωH : (R.ω : ℝ) * (R.Hhi : ℝ) ≤ (R.ω : ℝ) * P := mul_le_mul_of_nonneg_left hHP hω0
  have hωc : (R.ω : ℝ) * (c : ℝ) ≤ (R.ω : ℝ) * P := mul_le_mul_of_nonneg_left hcP hω0
  have hfin := mul_le_mul_of_nonneg_right h24P hω0
  linarith [hfin, hPH, hceil1, hceil2, hωP, hωH, hωc, hω1]


/-! ## §4 — the pass-through hops on the U-forms: doorL2 · road · capstone

Each body is its rung-2 source's with ONLY the plumbing changed: where the source obtains the built
regime from the previous form and re-exports its tuple, the U-hop introduces the regime and its
hypotheses and applies the previous form at the weaker floor.  Nothing below the plumbing moves.

⛔ **THE SOCKET HOP WAS NOT IN HALF 1, AND WHY WAS A WALK FINDING (dated 2026-09-25; RESOLVED in
§5).**
`flat_socket_generic_epsW` spends the head's COUNT export `∀ H ∈ [Hlo, Hhi], |Ξ_H| ≤ K` twice — as
the
head's own hypothesis and as the arc lemma's `hcount` — at the head's existential `K`.  Half 1's
`FlatHeadFormU` kept the count as a HYPOTHESIS on the regime (the source has it as an export), while
`FlatSocketFormU` has no count (its source exports none), so the hop could not forward it.  The
freeze's second addendum moved the count to the head form's CONCLUSION side — an export the rung-2
head PROVES from a floor belongs there — and the socket hop landed in §5 on the re-cut form.
Recorded in `docs/blueprints/flags.md` with its RESOLVED line; the three hops below never read it.
-/

/-- **the `L²` door hop, uniform** (`flat_doorL2_generic_U`) — `flat_doorL2_generic_epsW`
(`FlatDoorEpsRung2.lean:4978`) on the U-forms: the regime and its six hypotheses are introduced and
passed to the socket form at the same floor `Hcap ≤ R.Hlo`; the slot's proof is the source's. -/
theorem flat_doorL2_generic_U (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatSocketFormU ε c P) :
    FlatDoorL2FormU ε c P := by
  unfold FlatDoorL2FormU
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  obtain ⟨Kb, δ₀, β, Hopq, hε, hKb, hKbb, hδ₀, hc1, hεpin, hδpin, hβ, hsk⟩ :=
    h
  refine ⟨Cg, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hc1, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge hAL
  obtain ⟨Hcap, hCapLe, hexit⟩ := hsk A hA162 hAge hAL
  refine ⟨Hcap, hCapLe, ?_⟩
  intro R g hg hReps hfl hRg hRx hRtow
  have hR := hexit R g hg hReps hfl hRg hRx hRtow
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  have hA : 1 ≤ AdoorL M := one_le_AdoorL hgates.hM
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
    intro H hhi
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  refine hR (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2
      liouvilleC)
    (fun m => lamCoeff m - memSCoeff (calP (AdoorL M) (s13GK K M))
      (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC m)
    Braw (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) (fun m => by ring) hBraw0
    (hsock m4_bandTransport) ?_ ?_
  · intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (AdoorL M) (s13GK K M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · intro H hlo hhi
    rw [l2_budget_line Kb (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * Kb * Braw H ≤ 2 * Kb * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

/-- **the road hop, uniform** (`flat_road_generic_U`) — `flat_road_generic_epsW`
(`FlatDoorEpsRung2.lean:5023`) on the U-forms: the regime and its six hypotheses are introduced and
passed to the `L²` door form at the same floor; the slot's proof is the source's. -/
theorem flat_road_generic_U (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatDoorL2FormU ε c P) :
    FlatRoadFormU ε c P := by
  unfold FlatRoadFormU
  obtain ⟨Cg, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hc1, hεpin, hδpin, hβ, hdoor⟩ :=
    h
  refine ⟨Cg, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hc1, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge hAL
  obtain ⟨Hcap, hCapLe, hmain⟩ := hdoor K A hA162 hAge hAL
  refine ⟨Hcap, hCapLe, ?_⟩
  intro R g hg hReps hfl hRg hRx hRtow
  have hR := hmain R g hg hReps hfl hRg hRx hRtow
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  have harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    nlinarith [h1, harc1]
  have harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 2 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    nlinarith [h1, harc1]
  have hchi : M4ChiSummedBlockMeanSqN_L_gk K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied_L_gk K j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummed_L_gk K (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  have hcov := m4_cover_assembly_blk2_L_gk K hgates hBblk0 hblk2
  refine hR Braw Bceil δ M k hgates hBraw0 ?_ hceil hbudget
  refine m4_sievedDoorSq_of_blk2_L_gk K (ℓ := blockLen)
    (fun H => by have := hBblk0 H; positivity)
    (fun H q _ _ _ _ => one_le_blockLen H q) ?_ ?_ ?_ ?_ hcov
  · intro H q hlo hhi _ _
    have h1 := harc H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hH1 : 1 ≤ H := by
      have : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
      exact_mod_cast this
    exact blockLen_le H q hH1
  · intro H q hlo hhi _ _
    exact blockLen_narrow (R := R) hlo (harc H hlo hhi)
  · intro H q hlo hhi hq _
    exact blockLen_drift (R := R) hlo hq (harc H hlo hhi)
  · intro H hlo hhi
    have h := hdrift H hlo hhi
    have hres0 : (0 : ℝ) ≤ strataResidual H :=
      strataResidual_nonneg (one_le_arcDen_of_regime (R := R) hlo)
    have hB := hBcl0 H
    nlinarith [h]

/-- **the capstone hop, uniform** (`flat_capstone_generic_U`) — `flat_capstone_generic_epsW`
(`FlatDoorEpsRung2.lean:5086`) on the U-forms: the floor hypothesis
`max Hcap' (max arcFloor36 loglogFloor50) ≤ R.Hlo` (with `Hcap' = max Hcap (max arcFloor36
loglogFloor50)`) gives the road form its floor `Hcap ≤ R.Hlo` and the two absorbed floors, as at
the source's `:5113–5116`; the slot's proof is the source's. -/
theorem flat_capstone_generic_U (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatRoadFormU ε c P) (Awin : ℝ) (hband : S16BandLaneCBoundedL_winU Awin) :
    FlatCapstoneFormU ε c P Awin := by
  unfold FlatCapstoneFormU
  obtain ⟨Cg, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hKcb, hδ₀, hc1, hεpin, hδpin, hβ, hroadU⟩ :=
    h
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  refine ⟨Cg, Kc, δ₀, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, s11GradeFloor_one_le _, hCgle,
    hc1, hεpin, hδpin, hKcb,
    (fun A hA162 hAw => flatDoorM_gradeFloor_win hA162 hCband0 (by linarith)),
    hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_L_gk_ceiling_kwide K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge hAL
  obtain ⟨Hcap, hCapLe, hroad⟩ := hroadU K A hA26 hAge hAL
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp R g hg hReps hU1 hRg hRx hRtow
  have hR := hroad R g hg hReps (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hU1)
    hRg hRx hRtow
  intro M hMfloor hKw
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit K M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_L_gk K R M
      (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho_L M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
    have hKcpos : (0 : ℝ) < 16 * Kc := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

/-! ## §5 — HALF 2: the socket hop, the head at the trivial payload, the shrink, the conditional ·
kswin · v7 hops, the chain and `FlatDoorUniformW`

The module header's "HALF 2 … is OWED" and §4's "THE SOCKET HOP IS NOT HERE" describe half 1 and
are superseded by this section.  Two forms were RE-CUT for it (the road-F freeze of candidate U,
its second addendum §2–§3): `FlatHeadFormU`'s count moved to its conclusion side, which is what
lets the socket hop below forward it, and `V7RatedFormU` exports a floor. -/

/-- **the socket hop, uniform** (`flat_socket_generic_U`) — `flat_socket_generic_epsW`
(`FlatDoorEpsRung2.lean:4952`) on the U-forms: the head's floor `Hcap` sits under the socket's
`max Hcap H₀`, the head at the given regime returns the COUNT beside its slot (the re-cut), and the
count is spent, as at the source, as `hcount` of `sum_bigXi_norm_windowExpSum_sq_le_twelve`. -/
theorem flat_socket_generic_U (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatHeadFormU ε c P) :
    FlatSocketFormU ε c P := by
  unfold FlatSocketFormU
  obtain ⟨K, δ₀, β, Hopq, hε, hK, hKb, hδ₀, hc1, hεpin, hδpin, hβ, hhead⟩ :=
    h
  obtain ⟨H₀, hH₀⟩ := sum_bigXi_norm_windowExpSum_sq_le_twelve ε hε
  refine ⟨K, δ₀, β, max Hopq H₀, hε, hK, hKb, hδ₀, hc1, hεpin, hδpin, hβ, ?_⟩
  intro A hA162 hAge hAL
  obtain ⟨Hcap, hCapEq, hhd⟩ := hhead A (by linarith) hAge hAL
  refine ⟨max Hcap H₀, by rw [hCapEq]; omega, ?_⟩
  intro R g hg hReps hfl hRg hRx hRtow
  obtain ⟨hcount, hslot⟩ :=
    hhd R g hg hReps (le_trans (le_max_left _ _) hfl) hRg hRx hRtow
  have harc : H₀ ≤ R.Hlo := le_trans (le_max_right _ _) hfl
  intro a e Bsieve Binsert hsplit hB0 hsock hins hρ
  refine hslot δ₀ hδ₀ le_rfl ?_
  intro H _ hlo hhi
  exact le_trans (hH₀ R hReps harc a e Bsieve K Binsert hsplit hB0 hsock hcount hins
    H hlo hhi) (hρ H hlo hhi)

/-- **the head at the trivial payload, uniform** (`flatHeadFormU_trivial`) — rung 2's head
`flat_head_uniform_xceil_epsW` (`FlatDoorEpsRung2.lean:4783`) WITHOUT the spine: the ε bounds, the
mint against the pin (`hδnum`), the count hook `bigXi_bounded_ceiling_eps`, `β`, and the head's own
floor `Hopq = max (max H₀red H₀D3) H₀xi` (the two spine floors kept, so the `Hcap` equation is the
source's) are the source's; the regime is GIVEN, the count is proved at it from `H₀xi ≤ Hopq ≤ Hcap
≤ R.Hlo` exactly as at the source's `:4869–4877`, and the slot is `trivial`.  No builder, no
entropy decrement, no spine core.  Dropped from the source (served only the spine or the builder):
the circle-method obtain, `hlog4` · `hlog2gt` · `hCnum` · `hCle` · `hεle` · `hεcE` · `hε_half_lt`
· `hε_D3` · `hε_D3C` · `hεQ1` · `hcD3ge` · `hlamA` and `classical`. -/
theorem flatHeadFormU_trivial (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
    {c : ℕ} (hc1 : 1 ≤ c) (hcε : (1 : ℚ) / (500 * (c : ℚ)) ≤ ε) :
    FlatHeadFormU ε c (fun _ => True) := by
  unfold FlatHeadFormU
  obtain ⟨-, -, -, H₀red, -⟩ := hreduce_holds_final_bounded
  obtain ⟨-, -, -, H₀D3, -⟩ := primeWindow_sum_inv_ge_bounded
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  obtain ⟨cD3, hcD3def⟩ : ∃ c : ℝ, c = 1 / 4 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ c : ℝ, c = 1 + 2 * (2 * Real.log 4) := ⟨_, rfl⟩
  have hcD3 : 0 < cD3 := by rw [hcD3def]; norm_num
  have hC : 0 < C := by rw [hCdef]; positivity
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  have hmint : cD3 / (16 * C) * (ε : ℝ) / 4 = (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) := by
    rw [hcD3def, hCdef]
    have hne : (1 : ℝ) + 2 * (2 * Real.log 4) ≠ 0 := by positivity
    field_simp
    ring
  have hcQ : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcQ0 : (0 : ℚ) < 500 * (c : ℚ) := by linarith
  have hqcap : (1 : ℚ) ≤ 500 * (c : ℚ) * ε := by
    rw [div_le_iff₀ hcQ0] at hcε; linarith
  have hcapR : (1 : ℝ) ≤ 500 * (c : ℝ) * (ε : ℝ) := by exact_mod_cast hqcap
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hδnum : (1 : ℝ) / (838400 * (c : ℝ)) ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    rw [hmint, div_le_div_iff₀ (by linarith) (by positivity), hlog4eq]
    linarith
  obtain ⟨K, hK, hKb, H₀xi, -, hxi⟩ := bigXi_bounded_ceiling_eps ε hε0 hε hc1 hcε
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = cD3 * (ε : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hcD3 hεR0) (by positivity)
  obtain ⟨Hopq, hOpqdef⟩ : ∃ n : ℕ, n = max (max H₀red H₀D3) H₀xi := ⟨_, rfl⟩
  refine ⟨K, cD3 / (16 * C) * (ε : ℝ) / 4, β, Hopq, hε0, hK, hKb,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num),
    hc1, hcε, hδnum, hβpos, ?_⟩
  intro A _hA26 _hAge _hAL
  obtain ⟨F, hFdef⟩ : ∃ n : ℕ, n = max Hopq (budgetFloorFlat (ε : ℝ) β A) := ⟨_, rfl⟩
  refine ⟨max (flatDesignFloor A) (max F (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), by rw [hFdef], ?_⟩
  intro R _g _hg hReps hfl _hRg _hRx _hRtow
  refine ⟨?_, fun _ _ _ _ => trivial⟩
  have hFlo : F ≤ R.Hlo := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hfl
  have hxiHlo : H₀xi ≤ R.Hlo := by
    rw [hFdef, hOpqdef] at hFlo
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hFlo
  intro H' _ hlo' _
  rw [hReps]
  exact hxi H' (le_trans hxiHlo hlo')

/-- **the threshold shrink, uniform** (`flatHeadFormU_at_grade`) — `flatHeadFormEpsW_at_grade`
(`FlatDoorAllGrades.lean:89`) on the re-cut head form: the threshold becomes any `ρt` on the pin,
the count is forwarded, and the new slot is `mrtUniformityXiL2_mono`. -/
theorem flatHeadFormU_at_grade {ε : ℚ} {c : ℕ} {Q : ChowlaRegime → Prop}
    (h : FlatHeadFormU ε c Q) {ρt : ℝ} (hρt : 0 < ρt)
    (hpin : (1 : ℝ) / (838400 * (c : ℝ)) ≤ ρt) :
    FlatHeadFormU ε c (fun R => MRTUniformityXiL2 R ρt) := by
  unfold FlatHeadFormU at h ⊢
  obtain ⟨K, δ₀, β, Hopq, hε, hK, hKb, -, hc1, hcε, -, hβ, hbody⟩ := h
  refine ⟨K, ρt, β, Hopq, hε, hK, hKb, hρt, hc1, hcε, hpin, hβ, ?_⟩
  intro A hA hbud hcA
  obtain ⟨Hcap, hHcap, hR⟩ := hbody A hA hbud hcA
  refine ⟨Hcap, hHcap, ?_⟩
  intro R g hg hReps hfl hRg hRx hRtow
  obtain ⟨hcount, -⟩ := hR R g hg hReps hfl hRg hRx hRtow
  exact ⟨hcount, fun ρ _ hle hd => mrtUniformityXiL2_mono hle hd⟩

/-- **the conditional hop, uniform** (`flat_conditional_generic_U`) —
`flat_conditional_generic_epsW` (`FlatDoorEpsRung2.lean:5250`) on the U-forms.  The source asks the
builder for the substituted caller `s15Arm δ₀ ρ + g`; here the regime is GIVEN and its arm
`s15Arm δ₀ ρ Hhi ω ≤ x` comes from U-ARM (`s15Arm_le_of_regime`) at the form's ninth-arm floor
hypothesis.  The capstone form is called at the same regime with the caller's own `g` (its strict
rider weakened to the non-strict one), and the floor hypothesis gives `loglogFloor50 ≤ R.Hlo`; the
body below the fire is the source's `:5297–5356` verbatim. -/
theorem flat_conditional_generic_U (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ)
    (h : FlatCapstoneFormU ε c P Awin) :
    FlatConditionalFormU ε c P Awin := by
  unfold FlatConditionalFormU
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hCg, hε, hKc, hδ₀, hMfl,
    hCgle, hc1, hεpin, hδpin, hKcb, hMflb, hβ, hcapU⟩ :=
    h
  refine ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl,
    hCgle, hc1, hεpin, hδpin, hKcb, hMflb, hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcapK⟩ := hcapU K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge hAL
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapK A hA26 hAge hAL
  refine ⟨Hcap, hCapLe, ?_⟩
  intro R g hg hReps hU h518 hRg hRx hRtow
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦THE CALLER'S RIDER, NON-STRICT⟧ the capstone form takes the non-strict rider
  have hgA : XCeilRiderAt (50 + Real.log (c : ℝ)) ε g := by
    intro Hhi ω hgate
    have h1 := hg Hhi ω hgate
    have h2 : (0 : ℝ) ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := by positivity
    linarith
  -- ⟦THE ARM, FROM THE REGIME'S OWN FIELDS⟧ U-ARM at the ninth-arm floor
  have hεR : (1 : ℚ) / (500 * (c : ℚ)) ≤ R.eps := by rw [hReps]; exact hεpin
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x :=
    s15Arm_le_of_regime hc1 hδ₀ hδpin hKc hKcb R hεR h518
  have hfire := hmain 0 le_rfl R g hgA hReps hU hRg hRx hRtow
  have hfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
  intro M hsel hKw
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor hKw
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the LINEAR anchor
  have harith := s15_doorArithFrameRho_L_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register⟧
  have hgate : S13BandGate'_L_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_L_gk_T K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_gen le_rfl (s13_g2_jfloor_of_MSelect'_L_gk K (by linarith) hS))
    (s13_gate8_L_gk le_rfl (s13_gate8_of_MSelect'_L_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_L_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket_L hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorL_gk_T K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat_T hfl (socketBase_of_socketBaseL hsel.hM hb) hlam50 htow
        hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flat_T hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flat_T hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM (hgate.block H L q j A s hb)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_L_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith

/-- **the kswin hop, uniform** (`flat_kswin_generic_U`) — `flat_kswin_generic_epsW`
(`FlatDoorEpsRung2.lean:5380`) on the U-forms.  The source's PROBE regime (`:5393–5412`), built only
to read `ε ≤ 1/2` off its `heps1`, is DELETED: a `∀ R` form exhibits no regime.  The ONE site that
reads `ε ≤ 1/2` with no regime in scope is the form's first conjunct
(`flat_witFloor_eq_designBase_L`, under `∀ A` and before `∀ R`), so this hop takes it as the
theorem binder `hε2q : ε ≤ 1 / 2` (the structure's own `heps1` bound, NOT a form component; the
assembly pays it from `ε ≤ 1/500`).  The given `R.Hlo = flatDesignBase A` replaces the source's
`R.Hlo = flatWitFloor …` through that conjunct at `hopq`; the design and width facts are the
form's hypotheses; the rest is the source's `:5445–5475`. -/
theorem flat_kswin_generic_U (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ)
    (hε2q : ε ≤ 1 / 2) (h : FlatConditionalFormU ε c P Awin) :
    FlatKswinFormU ε c P Awin := by
  unfold FlatKswinFormU
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hc1, hεpin, hδpin, hKcb, hMflb, hβ, hcondU⟩ :=
    h
  -- ⟦THE CROSSING CONSTANTS, HOISTED ABOVE THE LEVER⟧ — §4's windowed twin
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40,
    hsupplyU⟩ := s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin
  have hc0 : 0 < c := by omega
  have hLc0 : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast hc1)
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have hcQ1 : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hεR : (1 : ℝ) / (500 * (c : ℝ)) ≤ (ε : ℝ) := by
    have hq := hεpin
    rw [div_le_iff₀ (by linarith)] at hq
    have h1R : (1 : ℝ) ≤ (ε : ℝ) * (500 * (c : ℝ)) := by exact_mod_cast hq
    rw [div_le_iff₀ (by linarith)]
    linarith
  refine ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hc1, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  have hsupply := hsupplyU K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA26 hAwin hAge hAL hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge hAL
  have hWitEq : Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A :=
    fun hopq => flat_witFloor_eq_designBase_L (h := c) hc0 hLc0 le_rfl hA26 hAL hβ
      hεR hε2 hε hεpin hAge hopq
  refine ⟨hWitEq, ?_⟩
  intro hx0win hopq hT₀ hKsw R g hg hReps hHlo h518 hRg hRx hRtow _hdes hwin
  have hWit : flatWitFloor ε β A Hopq = flatDesignBase A := hWitEq hopq
  have hfloor : max Hcap (max arcFloor36 loglogFloor50) ≤ R.Hlo := by
    rw [hHlo, ← hWit]; exact flatCap_le_flatWitFloor hCapLe
  have hfire := hbody R g hg hReps hfloor h518 hRg hRx hRtow
  intro hcof hcapsc
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  -- `1/(2^9·c) ≤ 1/(500·c) ≤ ε`, the source's step at the charge: `500 ≤ 512 = 2^9`
  have heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps := by
    rw [hReps]
    have h512 : (500 : ℚ) * (c : ℚ) ≤ 2 ^ 9 * (c : ℚ) := by
      have h9 : (2 : ℚ) ^ 9 = 512 := by norm_num
      rw [h9]; linarith
    have hb : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ 1 / (500 * (c : ℚ)) :=
      one_div_le_one_div_of_le (by linarith) h512
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo, ← hWit]; exact flatWitFloor_log_ge hA26
  -- ⟦THE BRIDGE⟧ the `A`-scoped window becomes §4's regime-scoped one at the flat floor
  have hKswR : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16 := by linarith
  -- the selector's pin `1/(838400·2^12·c²) ≤ δ₀` from `1/(838400·c) ≤ δ₀`: `c ≤ 4096·c²` at
  -- `c ≥ 1` (the binder's type is the lemma's, left to unification)
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win_L hA26 K hKw (h := c) hc0 hLc0 le_rfl hAL
    hδ₀ (le_trans (one_div_le_one_div_of_le (by linarith) (by norm_num; nlinarith)) hδpin)
    hKc (epsRung2_one_le_Kb hc1) hKcb (epsRung2_log_Kb_le hc1)
    hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win heps hlo hwin
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo, ← hWit]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk K (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel hKw
    (hsupply hKqb R (flatDoorM A) hM1 hfl hKswR (by rw [hHlo, ← hWit]; exact hT₀) hblk hcof
      hcapsc)

/-- **the rated hop, uniform** (`flat_v7_generic_U`) — `flat_v7_generic_epsW`
(`FlatDoorEpsRung2.lean:5505`) on the re-cut V7 U-form.  The supplies and the nine arms are the
source's, minted BEFORE the lever (the seven landed arms at `A₀ := 0`, `armVt Kvt`, and
`162 + 2·log c` outermost), into `A*`; the form's floor is `Hfl := flatDesignBase A*`.  For a
given regime above it the design constant is `A := loglog Hlo / 3.2` (the INVERSION): `A* ≤ A`
because `loglog (flatDesignBase A*) ≥ 3.2·A*`, `R.Hlo = flatDesignBase A` by
`flatDesignBase_of_loglog_eq`, `hdes` holds with equality and `hbaseceil` with slack `log 2`, and
every arm reading lifts through `A* ≤ A`.  The kswin form is called at `R` with the zero rider;
the base-scale cap reads the class's ceiling; the rest is the source's `:5580–5648`.  The exported
`Ct` is the rated one at `KlevF A*` (the form asks only `0 < Ct`). -/
theorem flat_v7_generic_U (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : ∀ Awin : ℝ, S16BandLaneCBoundedL_winU Awin → FlatKswinFormU ε c P Awin) :
    V7RatedFormU ε c P := by
  unfold V7RatedFormU
  obtain ⟨Awin, -, hband⟩ := s16_bandLaneWinL_holdsU
  -- ⟦THE cs-FREE, Ks-WINDOWED FLAT TERMINAL⟧ V7Ks §5
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hc1, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ :=
    h Awin hband
  have hc0 : 0 < c := by omega
  have hLc0 : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast hc1)
  -- ⟦THE RATED CO-FACTOR SUPPLY⟧ four Skolem REALS, minted BEFORE the lever
  obtain ⟨Xsk, Y0, Kvt, Cb, _hXsk0, _hY0pin, hKvt0, _hCb0, hcofR⟩ :=
    cofkR_cofactorSupply_L_gk_rated_L c hc0 hLc0 le_rfl
  -- ⟦THE NINE ARMS⟧ the source's seven at `A₀ := 0` (`A'`), `armVt Kvt`, `162 + 2·Lc` outermost
  obtain ⟨A', hA'def⟩ : ∃ a : ℝ, a = max (16 * Real.log (1 / Ks) / 3) (max T₀
      (max (max (max (max 0 162) Awin) (cofkRThr Cq Cb Xsk Y0))
        (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))))) := ⟨_, rfl⟩
  obtain ⟨As, hAsdef⟩ : ∃ a : ℝ, a = max (162 + 2 * Real.log (c : ℝ)) (max (armVt Kvt) A') :=
    ⟨_, rfl⟩
  have hA162bs : 162 + 2 * Real.log (c : ℝ) ≤ As := by rw [hAsdef]; exact le_max_left _ _
  have harmAs : armVt Kvt ≤ As := by
    rw [hAsdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hlift : A' ≤ As := by
    rw [hAsdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hKsAs : 16 * Real.log (1 / Ks) / 3 ≤ As := by
    refine le_trans ?_ hlift; rw [hA'def]; exact le_max_left _ _
  have hT₀As : T₀ ≤ As := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hAwinAs : Awin ≤ As := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (max 0 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hthrAs : cofkRThr Cq Cb Xsk Y0 ≤ As := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_right (max (max 0 162) Awin)
      (cofkRThr Cq Cb Xsk Y0)) (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAgeAs : budgetAFlat (ε : ℝ) β ≤ As := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _)
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hx0As : 4 * (x₀ : ℝ) ≤ As := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hopqAs : ((Hopq : ℕ) : ℝ) ≤ As := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  obtain ⟨Ct, hCt, -⟩ := hmainU (KlevF As)
  refine ⟨Cg, Kc, δ₀, Ct, β, Mfl, Cq, cs, T₀, Kq, Ks, C, flatDesignBase As,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hc1, hεpin, hδpin, hβ, ?_⟩
  intro R hReps hHfl hRx hRtow
  -- ⟦THE INVERSION⟧ `A := loglog Hlo / 3.2`: the flat base IS `Hlo`, and `A* ≤ A`
  have hHlo2 : 2 ≤ R.Hlo := by have := R.hHlo_floor; omega
  have hHlo1R : (1 : ℝ) < (R.Hlo : ℝ) := by exact_mod_cast (show 1 < R.Hlo by omega)
  have hlogHlo : 0 < Real.log (R.Hlo : ℝ) := Real.log_pos hHlo1R
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = Real.log (Real.log (R.Hlo : ℝ)) / 3.2 := ⟨_, rfl⟩
  have hHlo : R.Hlo = flatDesignBase A := by rw [hAdef, flatDesignBase_of_loglog_eq hHlo2]
  have hdeseq : 3.2 * A = Real.log (Real.log (R.Hlo : ℝ)) := by rw [hAdef]; ring
  have hAstar : As ≤ A := by
    have hd := flatDesignBase_design As
    have hB1 : (1 : ℝ) < ((flatDesignBase As : ℕ) : ℝ) := by
      have hy : (1 : ℝ) < Real.exp (Real.exp (3.2 * As)) := by
        have := Real.add_one_le_exp (Real.exp (3.2 * As))
        have := Real.exp_pos (3.2 * As)
        linarith
      refine lt_of_lt_of_le hy ?_
      unfold flatDesignBase
      exact Nat.le_ceil _
    have hBle : ((flatDesignBase As : ℕ) : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast hHfl
    have hl1 := Real.log_le_log (by linarith) hBle
    have hl2 := Real.log_le_log (Real.log_pos hB1) hl1
    linarith
  have hA162b : 162 + 2 * Real.log (c : ℝ) ≤ A := le_trans hA162bs hAstar
  have hAL : 10 + 2 * Real.log (c : ℝ) ≤ A := by linarith
  have harmA : armVt Kvt ≤ A := le_trans harmAs hAstar
  have hKsA : 16 * Real.log (1 / Ks) / 3 ≤ A := le_trans hKsAs hAstar
  have hT₀A : T₀ ≤ A := le_trans hT₀As hAstar
  have hA162 : (162 : ℝ) ≤ A := by linarith
  have hAwinA : Awin ≤ A := le_trans hAwinAs hAstar
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := le_trans hthrAs hAstar
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := le_trans hAgeAs hAstar
  have hx0A : 4 * (x₀ : ℝ) ≤ A := le_trans hx0As hAstar
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := le_trans hopqAs hAstar
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  -- ⟦THE `Ks` WINDOW, AT THE SEVENTH ARM⟧ as in the parent
  have hKswin : Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 := by linarith
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
    have h2 : Real.exp (3.2 * A) / 10 + 1 ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
      Real.add_one_le_exp _
    linarith
  have hopq : Hopq ≤ flatDesignBase A := by
    have h2 : Real.exp (3.2 * A) + 1 ≤ Real.exp (Real.exp (3.2 * A)) := Real.add_one_le_exp _
    have hR : ((Hopq : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by linarith
    have hceil := le_trans hR (Nat.le_ceil (Real.exp (Real.exp (3.2 * A))))
    rw [flatDesignBase]; exact_mod_cast hceil
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨_Ct', -, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hAL hKw
  -- ⟦THE `T₀` ARM⟧ V7-C's discharge, as in the parent
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  -- ⟦THE DESIGN FACTS AT `A(R)`⟧ `hdes` with equality, `hbaseceil` with slack `log 2`
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := hdeseq.le
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    rw [← hdeseq]; linarith
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA162 hbaseceil hdes hRtow
  -- ⟦THE NINTH ARM, FIRST READER⟧ `3.2·(162 + 2·Lc) = 518.4 + 6.4·Lc ≥ 518 + 6·Lc` at `0 ≤ Lc`
  have h518 : (518 : ℝ) + 6 * Real.log (c : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    linarith [hdes, hA162b, hLc0]
  -- ⟦THE EXHIBITED CALLER⟧ `g ≡ 0` meets the strict rider
  have hfire2 := hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKswin R (fun _ _ : ℕ => 0)
    (xceilRiderStrictAt_zero _ ε) hReps hHlo h518 (Nat.zero_le _) hRx hRtow hdes hwin
  -- ⟦THE BASE-SCALE CAP⟧ at `K = KlevF A`, the class's ceiling
  have heps500 : (1 : ℚ) / (500 * (c : ℚ)) ≤ R.eps := by
    rw [hReps]; exact hεpin
  have hxceil : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [hReps]; exact hRx
  -- ⟦THE RATED SUPPLY, WITH THE CUSHION PAID BY THE EIGHTH ARM⟧
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA26
  have hcQ1 : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have heps500R : (1 : ℝ) / (500 * (c : ℝ)) ≤ (R.eps : ℝ) := by
    rw [hReps]
    have hq := hεpin
    rw [div_le_iff₀ (by linarith)] at hq
    have h1R : (1 : ℝ) ≤ (ε : ℝ) * (500 * (c : ℝ)) := by exact_mod_cast hq
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact loglogFloor50_le_flatDesignBase hA162
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hdeseq, Real.exp_log hlogHlo]
  -- ⟦THE NINTH ARM, SECOND READER⟧ `cofkRThr ≤ A`, `2·Lc ≤ A`, `2·A ≤ 3.2·A + 1 ≤ e^(3.2A)`
  have hthrgate : cofkRThr Cq Cb Xsk Y0 + 2 * Real.log (c : ℝ)
      ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    linarith [hthrA, hlo, hexp1, hAL, hA162]
  have hKvtcush : 32 * Kvt
      + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
      ≤ Real.log (R.Hhi : ℝ) / 4 :=
    cofkR_cushion_of_armVt R hKvt0 harmA hlo
  -- ⟦THE NINTH ARM, THIRD READER⟧ `Lc ≤ A ≤ 1.6·A + 1 ≤ e^(1.6·A)`
  have hexp16 : 3.2 * A / 2 + 1 ≤ Real.exp (3.2 * A / 2) := Real.add_one_le_exp _
  have hLt : Real.log (c : ℝ) ≤ Real.exp (3.2 * A / 2) := by linarith
  have hcofsupply : S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) :=
    s16CofactorSupply_L_of_LH hc0
      (hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush)
  exact hfire2 hcofsupply
    (s16BaseScaleCap96_L_of_LH hc0
      (s16_baseScaleCap96_LH_at_klevF_L (h := c) hc0 hLc0 le_rfl
        hA26 hLt (flatDoorM_one_le hA26) heps500 hxceil hwin))

/-- **the chain, uniform** (`flat_chain_U`) — `flat_chain_generic_epsW`
(`FlatDoorEpsRung2.lean:5656`) on the U-forms: the seven U-hops composed.  ONE binder beyond the
source's, `hε2 : ε ≤ 1 / 2`, for the kswin hop's first conjunct (see `flat_kswin_generic_U`). -/
theorem flat_chain_U (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (hε2 : ε ≤ 1 / 2)
    (h : FlatHeadFormU ε c P) : V7RatedFormU ε c P :=
  flat_v7_generic_U ε c P (fun Awin hband => flat_kswin_generic_U ε c P Awin hε2
    (flat_conditional_generic_U ε c P Awin (flat_capstone_generic_U ε c P
      (flat_road_generic_U ε c P (flat_doorL2_generic_U ε c P (flat_socket_generic_U ε c P h)))
      Awin hband)))

/-- **⟦CANDIDATE U — THE UNIFORM FLAT DOOR, PROVED⟧** (`flatDoorUniformW_holds`) — the L² MRT door
with the crown's quantifier `∃ H₀ ∀ R` on the FLAT CLASS, at every grade `ρ > 0` and every
`ε ∈ (0, 1/500]`.  The charge is `crownWd_exists_charge`'s (it depends on `ε` and `ρ`, so the
threshold pin holds at `ρ`); the head at the trivial payload is shrunk to grade `ρ`; the chain's
V7 U-form exports the floor `H₀`.  ⚠ U is IMPLIED by the crown (`nextHopU_of_crown`) and is NOT
the crown: the residual is every regime off the class.  No rate.  Nothing here bears on twin
primes. -/
theorem flatDoorUniformW_holds : FlatDoorUniformW := by
  intro ε hε0 hε ρ hρ
  obtain ⟨c, hc1, hcε, hpin⟩ := crownWd_exists_charge ε hε0 ρ hρ
  have hhead : FlatHeadFormU ε c (fun _ => True) := flatHeadFormU_trivial ε hε0 hε hc1 hcε
  have hV := flat_chain_U ε c (fun R => MRTUniformityXiL2 R ρ) (le_trans hε (by norm_num))
    (flatHeadFormU_at_grade hhead hρ hpin)
  obtain ⟨Cg, Kc, δ₀, Ct, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Hfl,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hall⟩ := hV
  exact ⟨Hfl, fun R hcls hfl => hall R hcls.1 hfl hcls.2.1 hcls.2.2⟩

/-- **W-δ FROM U** (`flatDoorAllGradesW_of_uniform`) — the zero level `nextHopU_zero_level`
FIRED at `flatDoorUniformW_holds`: a second route to the landed `flatDoorAllGradesW_holds`.  It
lands NO new statement. -/
theorem flatDoorAllGradesW_of_uniform : FlatDoorAllGradesW :=
  nextHopU_zero_level flatDoorUniformW_holds

end Salt.MR
