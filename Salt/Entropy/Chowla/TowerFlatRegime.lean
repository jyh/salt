/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# THE FLAT-THRESHOLD REGIME (freeze item F-1)

The flat design (KAPPA-SCOPE; FLAT-REF §3) charges the mutual-information
threshold `κ = H/(A·log H)` at a design CONSTANT `A`, in place of the landed
`κ = H/(log H · logloglog H)`.  Its parameter bundle is `ChowlaRegimeFlat`: the
landed `ChowlaRegime` PLUS the four flat fields

    A : ℝ,  hA : 26 ≤ A,
    hflat  : 3.2·A ≤ loglog H₋        -- THE DESIGN LAW (one field)
    hfitF  : chowlaTowerFlat A a H₋ Jf ≤ H₊
    hJconF : log 2 < towerDropSumFlat A a H₋ Jf

Everything here is ADDITIVE.  The bundle is stated as an EXTENSION of the landed
structure (the option the wave brief names), which is what lets the entire landed
cone — `pH_headroom_at`, `sqrt_le_window_at`, `omega_big_at`, `x_big_at`,
`deficit_le_log_two`, `entropy_residueWindow_ge`, the Concentration/FBridge/
Transport/OuterCombine/WeakUniform chain, every `shellError` consumer — carry
VERBATIM through `R.toChowlaRegime`, exactly as FLAT-REF's F-7 rules.  No landed
declaration is touched.

## What `hflat` buys (the one field that discharges four faces)

* `flatFloor_of_design` — the flat tower's floor hypothesis
  `100·(c + λ) ≤ L` (`TowerFlat`'s `hfl`), FLAT-REF's probe F6;
* `fannes_ceiling_of_design` — the Fannes budget's ceiling `12·A·log 2 ≤ L`
  (probe F3: the width floor DOMINATES the Fannes demand, uniformly in `A`);
* the height-1 budget floor and the A-free width export (probes F7/F11) — the
  latter lives with the width cone, not here.

`c = log (2A)` is `flatC`; `λ = loglog H`; `L = log H`.
-/
import Salt.Entropy.Chowla.Tower
import Salt.Entropy.Chowla.TowerFlat

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ### Section 1 — the design-law discharges (symbolic in `A`) -/

/-- `12·A·log 2 ≤ exp (3·A)` for every `A ≥ 1` — FLAT-REF's probe F3, THE MONEY
    INEQUALITY: the flat width floor `λ₋ ≥ 3·A` implies the Fannes ceiling
    `12·A·log 2 ≤ L₋`, uniformly in `A`, with no numeral. -/
theorem flat_fannes_dominated {A : ℝ} (hA : 1 ≤ A) :
    12 * A * Real.log 2 ≤ Real.exp (3 * A) := by
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h4 : (4 : ℝ) * (3 * A / 4) = 3 * A := by ring
  have hpow : ((1 : ℝ) + 3 * A / 4) ^ 4 ≤ Real.exp (3 * A) := by
    have h1 : (1 : ℝ) + 3 * A / 4 ≤ Real.exp (3 * A / 4) := by
      linarith [Real.add_one_le_exp (3 * A / 4)]
    have hnn : (0 : ℝ) ≤ 1 + 3 * A / 4 := by linarith
    calc ((1 : ℝ) + 3 * A / 4) ^ 4 ≤ (Real.exp (3 * A / 4)) ^ 4 := by gcongr
      _ = Real.exp (4 * (3 * A / 4)) := by rw [← Real.exp_nat_mul]; norm_num
      _ = Real.exp (3 * A) := by rw [h4]
  nlinarith [hpow, hA, hl2, sq_nonneg A, sq_nonneg (A - 1)]

/-- The flat floor `100·(c + λ) ≤ exp λ`, in the pure-real glyphs: at the design
    law `λ ≥ 3.2·A` with `A ≥ 26` the second-order factors of `TowerFlat` are
    `1/100`-small.  (FLAT-REF probe F6, restated at the honest `exp λ = L`.) -/
theorem flat_floor_real {A lam : ℝ} (hA : 26 ≤ A) (hlam : 3.2 * A ≤ lam) :
    100 * (Real.log (2 * A) + lam) ≤ Real.exp lam := by
  have hlam0 : (83 : ℝ) ≤ lam := by linarith
  have hlog2A : Real.log (2 * A) ≤ 2 * A - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have h2A : 2 * A ≤ lam := by linarith
  have hpow : ((1 : ℝ) + lam / 4) ^ 4 ≤ Real.exp lam := by
    have h1 : (1 : ℝ) + lam / 4 ≤ Real.exp (lam / 4) := by
      linarith [Real.add_one_le_exp (lam / 4)]
    have hnn : (0 : ℝ) ≤ 1 + lam / 4 := by linarith
    calc ((1 : ℝ) + lam / 4) ^ 4 ≤ (Real.exp (lam / 4)) ^ 4 := by gcongr
      _ = Real.exp (4 * (lam / 4)) := by rw [← Real.exp_nat_mul]; norm_num
      _ = Real.exp lam := by rw [show (4 : ℝ) * (lam / 4) = lam by ring]
  have hq : (lam / 4) ^ 4 ≤ ((1 : ℝ) + lam / 4) ^ 4 := by
    have h0 : (0 : ℝ) ≤ lam / 4 := by linarith
    gcongr
    linarith
  have hcube : (571787 : ℝ) ≤ lam ^ 3 := by
    have h : ((83 : ℝ)) ^ 3 ≤ lam ^ 3 := by gcongr
    norm_num at h; linarith
  have hlin : 200 * lam ≤ (lam / 4) ^ 4 := by nlinarith [hcube, hlam0]
  linarith

/-- **The flat floor at a base `B`.**  The design law `3.2·A ≤ loglog B` (with
    `A ≥ 26` and the house regime floor) discharges `TowerFlat`'s `hfl`
    hypothesis `100·(c + loglog B) ≤ log B`. -/
theorem flatFloor_of_design {A : ℝ} (hA : 26 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hlam : 3.2 * A ≤ Real.log (Real.log (B : ℝ))) :
    100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ) := by
  have hlogB : (15 : ℝ) ≤ Real.log (B : ℝ) := (tower_log_bounds hB).1
  have hexp : Real.exp (Real.log (Real.log (B : ℝ))) = Real.log (B : ℝ) :=
    Real.exp_log (by linarith)
  have h := flat_floor_real hA hlam
  rw [hexp] at h
  rw [flatC]
  exact h

/-- **The Fannes ceiling at a base `B`.**  The design law gives the flat step's
    budget hypothesis `12·A·log 2 ≤ log B` — the width floor pays the Fannes
    demand (probe F3), with no numeral. -/
theorem fannes_ceiling_of_design {A : ℝ} (hA : 26 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hlam : 3.2 * A ≤ Real.log (Real.log (B : ℝ))) :
    12 * A * Real.log 2 ≤ Real.log (B : ℝ) := by
  have hlogB : (15 : ℝ) ≤ Real.log (B : ℝ) := (tower_log_bounds hB).1
  have hexp : Real.exp (Real.log (Real.log (B : ℝ))) = Real.log (B : ℝ) :=
    Real.exp_log (by linarith)
  have h3 := flat_fannes_dominated (show (1 : ℝ) ≤ A by linarith)
  have hmono : Real.exp (3 * A) ≤ Real.exp (Real.log (Real.log (B : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [hexp] at hmono
  linarith

/-! ### Section 2 — the flat regime bundle -/

/-- **THE FLAT-THRESHOLD REGIME** (freeze F-1).  The landed `ChowlaRegime` plus
    the flat design constant `A`, the design law `3.2·A ≤ loglog H₋`, and the
    flat tower's fit/crossing fields.  `toChowlaRegime` carries every landed
    consumer verbatim. -/
structure ChowlaRegimeFlat extends ChowlaRegime where
  /-- the flat design constant (the threshold is `κ = H/(A·log H)`) -/
  A : ℝ
  /-- the design constant's floor (FLAT-REF F-1) -/
  hA : 26 ≤ A
  /-- **THE DESIGN LAW.**  One field; it discharges the flat tower floor (F6),
      the Fannes ceiling (F3), the height-1 budget floor (F7) and the A-free
      width export (F11). -/
  hflat : 3.2 * A ≤ Real.log (Real.log (Hlo : ℝ))
  /-- the flat tower length -/
  Jf : ℕ
  /-- the flat tower fits below `H₊` -/
  hfitF : chowlaTowerFlat A a Hlo Jf ≤ Hhi
  /-- the flat telescoped decrement crosses `log 2` -/
  hJconF : Real.log 2 < towerDropSumFlat A a Hlo Jf

namespace ChowlaRegimeFlat

variable (R : ChowlaRegimeFlat)

lemma hApos : 0 < R.A := by have := R.hA; linarith

lemma hA1 : 1 ≤ R.A := by have := R.hA; linarith

/-- The flat tower floor at the regime's own base. -/
lemma hfl : 100 * (flatC R.A + Real.log (Real.log (R.Hlo : ℝ))) ≤ Real.log (R.Hlo : ℝ) :=
  flatFloor_of_design R.hA R.hHlo_floor R.hflat

/-- The Fannes ceiling at the regime's own base. -/
lemma hfannes : 12 * R.A * Real.log 2 ≤ Real.log (R.Hlo : ℝ) :=
  fannes_ceiling_of_design R.hA R.hHlo_floor R.hflat

/-- The Fannes ceiling propagates UP to every admissible `H ≥ H₋`. -/
lemma hfannes_at {H : ℕ} (hH : R.Hlo ≤ H) : 12 * R.A * Real.log 2 ≤ Real.log (H : ℝ) := by
  have hlo : 0 < R.Hlo := by have := R.hHlo_floor; omega
  have hmono : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by exact_mod_cast hlo) (by exact_mod_cast hH)
  linarith [R.hfannes]

end ChowlaRegimeFlat

/-! ### Section 3 — the flat tower inside the regime (general stride `a`) -/

/-- The flat tower respects the stride: `a ∣ H_j`. -/
lemma dvd_chowlaTowerFlat (A : ℝ) (a Hlo : ℕ) (j : ℕ) : a ∣ chowlaTowerFlat A a Hlo j := by
  induction j with
  | zero => exact ⟨Hlo, rfl⟩
  | succ n ih => exact ih.mul_right _

/-- The stride rebase: `chowlaTowerFlat A a B = chowlaTowerFlat A 1 (a·B)`, which
    is what carries `TowerFlat`'s `a = 1` master law to the regime's tower. -/
lemma chowlaTowerFlat_rebase (A : ℝ) (a B : ℕ) (j : ℕ) :
    chowlaTowerFlat A a B j = chowlaTowerFlat A 1 (a * B) j := by
  induction j with
  | zero => change a * B = 1 * (a * B); omega
  | succ n ih => rw [chowlaTowerFlat_succ, chowlaTowerFlat_succ, ih]

/-- Every flat tower value is `≥ H₋`. -/
lemma chowlaTowerFlat_ge (R : ChowlaRegimeFlat) (j : ℕ) :
    R.Hlo ≤ chowlaTowerFlat R.A R.a R.Hlo j := by
  induction j with
  | zero =>
    change R.Hlo ≤ R.a * R.Hlo
    calc R.Hlo = 1 * R.Hlo := (one_mul _).symm
      _ ≤ R.a * R.Hlo := by gcongr; exact R.ha
  | succ n ih =>
    have hfloor : 4000000 ≤ chowlaTowerFlat R.A R.a R.Hlo n := le_trans R.hHlo_floor ih
    have hmult := flatMul_ge_two R.hA1 hfloor
    rw [chowlaTowerFlat_succ]
    calc R.Hlo ≤ chowlaTowerFlat R.A R.a R.Hlo n := ih
      _ = chowlaTowerFlat R.A R.a R.Hlo n * 1 := (Nat.mul_one _).symm
      _ ≤ chowlaTowerFlat R.A R.a R.Hlo n
            * ⌊2 * R.A * Real.log (chowlaTowerFlat R.A R.a R.Hlo n : ℝ)⌋₊ := by
          gcongr; omega

lemma chowlaTowerFlat_floor (R : ChowlaRegimeFlat) (j : ℕ) :
    4000000 ≤ chowlaTowerFlat R.A R.a R.Hlo j :=
  le_trans R.hHlo_floor (chowlaTowerFlat_ge R j)

lemma chowlaTowerFlat_le_succ (R : ChowlaRegimeFlat) (j : ℕ) :
    chowlaTowerFlat R.A R.a R.Hlo j ≤ chowlaTowerFlat R.A R.a R.Hlo (j + 1) := by
  have hmult := flatMul_ge_two R.hA1 (chowlaTowerFlat_floor R j)
  rw [chowlaTowerFlat_succ]
  calc chowlaTowerFlat R.A R.a R.Hlo j
      = chowlaTowerFlat R.A R.a R.Hlo j * 1 := (Nat.mul_one _).symm
    _ ≤ chowlaTowerFlat R.A R.a R.Hlo j
          * ⌊2 * R.A * Real.log (chowlaTowerFlat R.A R.a R.Hlo j : ℝ)⌋₊ := by
        gcongr; omega

lemma chowlaTowerFlat_monotone (R : ChowlaRegimeFlat) :
    Monotone (chowlaTowerFlat R.A R.a R.Hlo) :=
  monotone_nat_of_le_succ (chowlaTowerFlat_le_succ R)

/-- Every flat tower value up to `Jf` fits below `H₊` (`hfitF` + monotonicity). -/
lemma chowlaTowerFlat_le_Hhi (R : ChowlaRegimeFlat) {j : ℕ} (hj : j ≤ R.Jf) :
    chowlaTowerFlat R.A R.a R.Hlo j ≤ R.Hhi :=
  le_trans (chowlaTowerFlat_monotone R hj) R.hfitF

/-- The flat design law at every tower level (the flat floor propagates: each
    level's `loglog` only grows). -/
lemma chowlaTowerFlat_design (R : ChowlaRegimeFlat) (j : ℕ) :
    3.2 * R.A ≤ Real.log (Real.log (chowlaTowerFlat R.A R.a R.Hlo j : ℝ)) := by
  have hlo : 0 < R.Hlo := by have := R.hHlo_floor; omega
  have hge : R.Hlo ≤ chowlaTowerFlat R.A R.a R.Hlo j := chowlaTowerFlat_ge R j
  have hlogHlo : (15 : ℝ) ≤ Real.log (R.Hlo : ℝ) := (tower_log_bounds R.hHlo_floor).1
  have hmono : Real.log (R.Hlo : ℝ) ≤ Real.log (chowlaTowerFlat R.A R.a R.Hlo j : ℝ) :=
    Real.log_le_log (by exact_mod_cast hlo) (by exact_mod_cast hge)
  have h2 : Real.log (Real.log (R.Hlo : ℝ))
      ≤ Real.log (Real.log (chowlaTowerFlat R.A R.a R.Hlo j : ℝ)) :=
    Real.log_le_log (by linarith) hmono
  linarith [R.hflat]

end Salt.Entropy.Chowla

