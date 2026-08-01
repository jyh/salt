/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# THE FLAT REGIME BUILDER (freeze F-1; FLAT-REF amendment 2)

`chowlaRegime_exists_param_gen` (`RegimeParam.lean:386`) builds a landed
`ChowlaRegime` over the base `max 4·10⁶ (max H₋₀ (4·⌈1/ε⌉₊⁴))`.  Its flat twin
cannot re-use that base: the flat tower's crossing needs the FLOOR hypothesis
`100·(c + loglog B) ≤ log B` (`TowerFlat`'s `hfl`), which FAILS at `B = 4·10⁶`,
and the flat regime's own design law `3.2·A ≤ loglog H₋` is a genuine new demand
on the base.  FLAT-REF's amendment 2 therefore RE-BASES the builder.  This file
is that re-basing plus the builder itself; everything is ADDITIVE.

## The three floors

* `flatBase A = ⌈exp (200·c + 10000)⌉₊`, `c = flatC A = log (2A)` — the floor at
  which the flat tower's `hfl` holds (FLAT-REF amendment 2, verbatim shape).
  `flat_floor_of_log` is its whole content: `100·(c + log L) ≤ L` as soon as
  `L ≥ 200c + 10000`, by one `log (L/400) ≤ L/400 − 1`.
* `flatDesignBase A = ⌈exp (exp (3.2·A))⌉₊` — the floor at which THE DESIGN LAW
  `3.2·A ≤ loglog B` holds.  It is the flat road's price for `hflat`, and it is
  the ONLY doubly-exponential arm anywhere in the flat cone.
* `flatDesignFloor A = max 4·10⁶ (max (flatBase A) (flatDesignBase A))` — the
  builder's base arm, replacing the landed `4·10⁶`.  MAX-MONOTONE: every
  consequence is stated at an arbitrary `B ≥ flatDesignFloor A`, so enlarging the
  base by any consumer floor (the `max` the builder takes) preserves it.

## The upper endpoint carries BOTH towers

`ChowlaRegimeFlat` extends `ChowlaRegime`, so `H₊` must dominate the LANDED tower
(`hfit`, `hJcon`) as well as the flat one (`hfitF`, `hJconF`).  The builder sets

```
H₊ = max (chowlaTower 2 1 H₋ (towerJmin 2 1 H₋)) (chowlaTowerFlat A 1 H₋ (towerFlatJmin A 1 H₋))
```

— both fits are then `le_max_*`, both crossings are the landed/flat `Jmin`
specs, and the WIDTH EXPORT still closes at the flat shape on BOTH arms: the
flat arm is freeze F-5 (`towerFlat_width_export`) exactly, and the landed arm is
`tower_loglog_le_45` followed by the shape bridge `pow_nine_halves_le_exp_half`
(whose guard `50 ≤ loglog H₋` the design law supplies free, `3.2·26 = 83.2`).
-/
import Salt.Entropy.Chowla.TowerExport
import Salt.Entropy.Chowla.TowerFlatExport

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ### Section 1 — the re-based floor (FLAT-REF amendment 2) -/

/-- **THE RE-BASED FLOOR, in pure real glyphs.**  `100·(c + log L) ≤ L` whenever
    `L ≥ 200·c + 10000` and `c ≥ 0`.  One `log (L/400) ≤ L/400 − 1` plus
    `log 400 ≤ 9·log 2`: the `log L` term costs `L/4 + 524`, the `c` term costs
    `L/2 − 5000`, and `10000` pays the remainder. -/
theorem flat_floor_of_log {c L : ℝ} (hc : 0 ≤ c) (hL : 200 * c + 10000 ≤ L) :
    100 * (c + Real.log L) ≤ L := by
  have hLpos : (0 : ℝ) < L := by linarith
  have h400 : (0 : ℝ) < L / 400 := by positivity
  have hd : Real.log (L / 400) ≤ L / 400 - 1 := Real.log_le_sub_one_of_pos h400
  have hsplit : Real.log (L / 400) = Real.log L - Real.log 400 :=
    Real.log_div (ne_of_gt hLpos) (by norm_num)
  have h512 : Real.log 400 ≤ 9 * Real.log 2 := by
    have h : Real.log 400 ≤ Real.log 512 := Real.log_le_log (by norm_num) (by norm_num)
    rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow] at h
    push_cast at h
    linarith
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

/-- **THE FLAT TOWER'S BASE FLOOR** (FLAT-REF amendment 2) — the least base at
    which `TowerFlat`'s `hfl` is available, `⌈exp (200·flatC A + 10000)⌉₊`. -/
noncomputable def flatBase (A : ℝ) : ℕ := ⌈Real.exp (200 * flatC A + 10000)⌉₊

/-- Above `flatBase A` the log is above the exponent. -/
theorem flatBase_log {A : ℝ} {B : ℕ} (hB : flatBase A ≤ B) :
    200 * flatC A + 10000 ≤ Real.log (B : ℝ) := by
  have hle : Real.exp (200 * flatC A + 10000) ≤ (B : ℝ) := by
    calc Real.exp (200 * flatC A + 10000)
        ≤ (⌈Real.exp (200 * flatC A + 10000)⌉₊ : ℝ) := Nat.le_ceil _
      _ = (flatBase A : ℝ) := by rw [flatBase]
      _ ≤ (B : ℝ) := by exact_mod_cast hB
  have h := Real.log_le_log (Real.exp_pos _) hle
  rwa [Real.log_exp] at h

/-- **THE FLAT TOWER FLOOR AT A RE-BASED BASE** — `TowerFlat`'s `hfl` for every
    `B ≥ flatBase A`.  This is the hypothesis the crossing stones want, now
    available WITHOUT the design law (the landed `4·10⁶` does not supply it). -/
theorem flatBase_floor {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : flatBase A ≤ B) :
    100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ) :=
  flat_floor_of_log (flatC_pos hA).le (flatBase_log hB)

/-- **THE DESIGN-LAW BASE** — the least base at which `3.2·A ≤ loglog B`. -/
noncomputable def flatDesignBase (A : ℝ) : ℕ := ⌈Real.exp (Real.exp (3.2 * A))⌉₊

/-- **THE BUILDER'S BASE ARM** — the landed `4·10⁶` enlarged by the two flat
    floors.  Everything below is stated at an arbitrary `B ≥ flatDesignFloor A`,
    which is the MAX-MONOTONICITY the builder needs: the base it actually uses is
    `max (flatDesignFloor A) (…consumer floors…)`. -/
noncomputable def flatDesignFloor (A : ℝ) : ℕ :=
  max 4000000 (max (flatBase A) (flatDesignBase A))

theorem flatDesignFloor_house (A : ℝ) : 4000000 ≤ flatDesignFloor A := le_max_left _ _

theorem flatBase_le_flatDesignFloor (A : ℝ) : flatBase A ≤ flatDesignFloor A :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem flatDesignBase_le_flatDesignFloor (A : ℝ) : flatDesignBase A ≤ flatDesignFloor A :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-- **THE DESIGN LAW AT ANY RE-BASED BASE** — `3.2·A ≤ loglog B` for every
    `B ≥ flatDesignFloor A`. -/
theorem flatDesignFloor_design {A : ℝ} {B : ℕ} (hB : flatDesignFloor A ≤ B) :
    3.2 * A ≤ Real.log (Real.log (B : ℝ)) := by
  have hdb : flatDesignBase A ≤ B := le_trans (flatDesignBase_le_flatDesignFloor A) hB
  have hle : Real.exp (Real.exp (3.2 * A)) ≤ (B : ℝ) := by
    calc Real.exp (Real.exp (3.2 * A))
        ≤ (⌈Real.exp (Real.exp (3.2 * A))⌉₊ : ℝ) := Nat.le_ceil _
      _ = (flatDesignBase A : ℝ) := by rw [flatDesignBase]
      _ ≤ (B : ℝ) := by exact_mod_cast hdb
  have h1 : Real.exp (3.2 * A) ≤ Real.log (B : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hle
    rwa [Real.log_exp] at h
  have h2 := Real.log_le_log (Real.exp_pos (3.2 * A)) h1
  rwa [Real.log_exp] at h2

/-- **THE MAX-MONOTONICITY LEMMA** (FLAT-REF amendment 2's second half): the
    design law survives the builder's `max` with ANY consumer floor. -/
theorem flatDesignFloor_design_max (A : ℝ) (m : ℕ) :
    3.2 * A ≤ Real.log (Real.log ((max (flatDesignFloor A) m : ℕ) : ℝ)) :=
  flatDesignFloor_design (le_max_left _ _)

/-- The flat tower floor at any re-based base (through `flatBase`). -/
theorem flatDesignFloor_tower_floor {A : ℝ} (hA : 1 ≤ A) {B : ℕ}
    (hB : flatDesignFloor A ≤ B) :
    100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ) :=
  flatBase_floor hA (le_trans (flatBase_le_flatDesignFloor A) hB)

/-! ### Section 2 — the single-exponential envelope -/

/-- `4·10⁶ ≤ e^16`. -/
theorem four_million_le_exp_sixteen : (4000000 : ℝ) ≤ Real.exp 16 := by
  have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h : Real.exp (16 : ℝ) = (Real.exp 1) ^ (16 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have hc : (2.7 : ℝ) ^ (16 : ℕ) ≤ (Real.exp 1) ^ (16 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) he1.le 16
  have hn : (4000000 : ℝ) ≤ (2.7 : ℝ) ^ (16 : ℕ) := by norm_num
  linarith

/-- **THE SINGLE-EXPONENTIAL ENVELOPE.**  Every arm of `flatDesignFloor A` is a
    `⌈exp ·⌉₊`, so the whole floor sits under `⌈exp T⌉₊` for any `T` dominating
    the two exponents.  This is the shape the road's cap comparison reads: the
    flat cap is `⌈e^T⌉₊`-genre with `T` the MAX of `200·log(2A)+10000`,
    `exp (3.2A)` and the height-1 budget exponent — never a tower. -/
theorem flatDesignFloor_le_ceil_exp {A T : ℝ} (hA : 1 ≤ A)
    (hbase : 200 * flatC A + 10000 ≤ T) (hdes : Real.exp (3.2 * A) ≤ T) :
    flatDesignFloor A ≤ ⌈Real.exp T⌉₊ := by
  have hcpos : 0 < flatC A := flatC_pos hA
  have hT : (16 : ℝ) ≤ T := by linarith
  have harm1 : (4000000 : ℕ) ≤ ⌈Real.exp T⌉₊ := by
    have h1 : (4000000 : ℝ) ≤ Real.exp T :=
      le_trans four_million_le_exp_sixteen (Real.exp_le_exp.mpr hT)
    have h2 : (4000000 : ℝ) ≤ (⌈Real.exp T⌉₊ : ℝ) := le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h2
  have harm2 : flatBase A ≤ ⌈Real.exp T⌉₊ :=
    Nat.ceil_le_ceil (Real.exp_le_exp.mpr hbase)
  have harm3 : flatDesignBase A ≤ ⌈Real.exp T⌉₊ :=
    Nat.ceil_le_ceil (Real.exp_le_exp.mpr hdes)
  rw [flatDesignFloor]
  exact max_le harm1 (max_le harm2 harm3)

/-! ### Section 3 — the outer-scale enlargement, flat -/

/-- **The outer-scale enlargement of a FLAT regime** — `regimeEnlargeX'` with the
    four flat fields carried verbatim (none of them mentions `x`). -/
def regimeFlatEnlargeX (R : ChowlaRegimeFlat) {x' : ℕ} (h : R.x ≤ x') : ChowlaRegimeFlat :=
  { regimeEnlargeX' R.toChowlaRegime h with
    A := R.A
    hA := R.hA
    hflat := R.hflat
    Jf := R.Jf
    hfitF := R.hfitF
    hJconF := R.hJconF }

@[simp] lemma regimeFlatEnlargeX_Hlo (R : ChowlaRegimeFlat) {x' : ℕ} (h : R.x ≤ x') :
    (regimeFlatEnlargeX R h).Hlo = R.Hlo := rfl

@[simp] lemma regimeFlatEnlargeX_Hhi (R : ChowlaRegimeFlat) {x' : ℕ} (h : R.x ≤ x') :
    (regimeFlatEnlargeX R h).Hhi = R.Hhi := rfl

@[simp] lemma regimeFlatEnlargeX_eps (R : ChowlaRegimeFlat) {x' : ℕ} (h : R.x ≤ x') :
    (regimeFlatEnlargeX R h).eps = R.eps := rfl

@[simp] lemma regimeFlatEnlargeX_A (R : ChowlaRegimeFlat) {x' : ℕ} (h : R.x ≤ x') :
    (regimeFlatEnlargeX R h).A = R.A := rfl

@[simp] lemma regimeFlatEnlargeX_omega (R : ChowlaRegimeFlat) {x' : ℕ} (h : R.x ≤ x') :
    (regimeFlatEnlargeX R h).ω = R.ω := rfl

@[simp] lemma regimeFlatEnlargeX_x (R : ChowlaRegimeFlat) {x' : ℕ} (h : R.x ≤ x') :
    (regimeFlatEnlargeX R h).x = x' := rfl

/-! ### Section 4 — THE FLAT REGIME BUILDER -/

/-- **THE FLAT REGIME BUILDER** (`chowlaRegimeFlat_exists_param_gen`) — the flat
    twin of `chowlaRegime_exists_param_gen`, re-based per FLAT-REF amendment 2.

    For any design constant `A ≥ 26`, any `ε ∈ (0, 1/2]` and any consumer floor
    `H₋₀`, a `ChowlaRegimeFlat` exists with

    * `R.eps = ε`, `R.A = A`, `H₋₀ ≤ R.Hlo`;
    * THE BASE EQUATION `R.Hlo = max (flatDesignFloor A) (max H₋₀ (4·⌈1/ε⌉₊⁴))`
      — the flat analogue of `HloExport`'s exported `hHlodef`, kept so the road's
      cap conjunct can be re-shaped downstream;
    * THE A-FREE WIDTH EXPORT `loglog H₊ ≤ exp (loglog H₋ / 2)` (freeze F-5),
      UNGUARDED: the `50 ≤ loglog H₋` guard the MR conjunct carries is free here
      (`3.2·A ≥ 83.2`).

    The construction is `RegimeParam.lean:391–459` with three changes: the base
    arm `4·10⁶ ⟶ flatDesignFloor A`; the endpoint `H₊` is the MAX of the landed
    and flat towers at their minimal crossings; and the four flat fields are
    discharged by `flatDesignFloor_design` (the design law), `flatFloor_of_design`
    + `towerFlatJmin_spec` (the flat crossing) and `le_max_right` (the flat fit).
    Everything else — `hcoprime`, `hPNTwindow`, the outer scale — is verbatim. -/
theorem chowlaRegimeFlat_exists_param_gen (A : ℝ) (hA : 26 ≤ A) (eps : ℚ) (heps : 0 < eps)
    (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) := by
  classical
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  -- the scale `m ≥ 1/ε`
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈(1 / eps : ℚ)⌉₊ := ⟨_, rfl⟩
  have hm_ge : (1 / eps : ℚ) ≤ (m : ℚ) := by rw [hmdef]; exact Nat.le_ceil _
  have hem : (1 : ℚ) ≤ eps * (m : ℚ) := by
    have h := mul_le_mul_of_nonneg_left hm_ge (le_of_lt heps)
    rwa [mul_one_div, div_self (ne_of_gt heps)] at h
  have hm1N : 1 ≤ m := by rw [hmdef]; exact Nat.ceil_pos.mpr (div_pos one_pos heps)
  have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm1N
  have hemR : (1 : ℝ) ≤ (eps : ℝ) * (m : ℝ) := by exact_mod_cast hem
  -- ⟦THE RE-BASED BASE⟧
  obtain ⟨Hlo, hHlodef⟩ : ∃ Hlo : ℕ,
      Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * m ^ 4)) := ⟨_, rfl⟩
  have hHloDF : flatDesignFloor A ≤ Hlo := by rw [hHlodef]; exact le_max_left _ _
  have hHlo_floor : 4000000 ≤ Hlo := le_trans (flatDesignFloor_house A) hHloDF
  have hHlo0 : Hlo₀ ≤ Hlo := by
    rw [hHlodef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hHlo4 : 4 * m ^ 4 ≤ Hlo := by
    rw [hHlodef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hHlo4Q : (4 : ℚ) * (m : ℚ) ^ 4 ≤ (Hlo : ℚ) := by exact_mod_cast hHlo4
  have hHlo4R : (4 : ℝ) * (m : ℝ) ^ 4 ≤ (Hlo : ℝ) := by exact_mod_cast hHlo4
  have hHlocap : Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) := by
    rw [hHlodef, hmdef]
  -- ⟦THE DESIGN LAW⟧ and the two floors it and `flatBase` supply
  have hflat : 3.2 * A ≤ Real.log (Real.log (Hlo : ℝ)) := flatDesignFloor_design hHloDF
  have hfl : 100 * (flatC A + Real.log (Real.log (Hlo : ℝ))) ≤ Real.log (Hlo : ℝ) :=
    flatFloor_of_design hA hHlo_floor hflat
  have h50 : (50 : ℝ) ≤ Real.log (Real.log (Hlo : ℝ)) := by linarith
  -- `hcoprime : 1 ≤ ε²·Hlo/2`
  have hcop : ((1 : ℕ) : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) / 2 := by
    have hprod : (1 : ℚ) ≤ (eps * (m : ℚ)) ^ 2 * (m : ℚ) ^ 2 := by
      have h1 : (1 : ℚ) ≤ (eps * (m : ℚ)) ^ 2 := by nlinarith [hem, sq_nonneg (eps * (m : ℚ) - 1)]
      have h2 : (1 : ℚ) ≤ (m : ℚ) ^ 2 := by nlinarith [hm1, sq_nonneg ((m : ℚ) - 1)]
      exact le_trans h1 (le_mul_of_one_le_right (sq_nonneg _) h2)
    have heq : (eps * (m : ℚ)) ^ 2 * (m : ℚ) ^ 2 = eps ^ 2 * (m : ℚ) ^ 4 := by ring
    have h4le : (4 : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) := by
      have hmul : eps ^ 2 * (4 * (m : ℚ) ^ 4) ≤ eps ^ 2 * (Hlo : ℚ) :=
        mul_le_mul_of_nonneg_left hHlo4Q (sq_nonneg eps)
      nlinarith [hmul, hprod, heq]
    rw [Nat.cast_one]; linarith
  -- `hPNTwindow : √Hlo ≤ ε²·Hlo/2`
  have hPNT : Real.sqrt (Hlo : ℝ) ≤ (eps : ℝ) ^ 2 * (Hlo : ℝ) / 2 := by
    have hsqrtHlo : (2 : ℝ) * (m : ℝ) ^ 2 ≤ Real.sqrt (Hlo : ℝ) := by
      have heq : Real.sqrt (4 * (m : ℝ) ^ 4) = 2 * (m : ℝ) ^ 2 := by
        rw [show (4 : ℝ) * (m : ℝ) ^ 4 = (2 * (m : ℝ) ^ 2) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
      calc (2 : ℝ) * (m : ℝ) ^ 2 = Real.sqrt (4 * (m : ℝ) ^ 4) := heq.symm
        _ ≤ Real.sqrt (Hlo : ℝ) := Real.sqrt_le_sqrt hHlo4R
    have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (Hlo : ℝ) := Real.sqrt_nonneg _
    have hHloeq : Real.sqrt (Hlo : ℝ) * Real.sqrt (Hlo : ℝ) = (Hlo : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have h2 : (2 : ℝ) ≤ (eps : ℝ) ^ 2 * Real.sqrt (Hlo : ℝ) := by
      have hstep : (eps : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2) ≤ (eps : ℝ) ^ 2 * Real.sqrt (Hlo : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrtHlo (sq_nonneg _)
      nlinarith [hstep, hemR, sq_nonneg ((eps : ℝ) * (m : ℝ) - 1)]
    have h3 : 2 * Real.sqrt (Hlo : ℝ) ≤ (eps : ℝ) ^ 2 * (Hlo : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right h2 hsqrtnn
      rw [mul_assoc, hHloeq] at hh
      linarith [hh]
    linarith [h3]
  -- ⟦THE TWO TOWERS⟧ at their minimal crossings, and the endpoint that hosts both
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = towerJmin 2 1 Hlo := ⟨_, rfl⟩
  obtain ⟨Jf, hJfdef⟩ : ∃ Jf : ℕ, Jf = towerFlatJmin A 1 Hlo := ⟨_, rfl⟩
  have hJ : Real.log 2 < towerDropSum 2 1 Hlo J := by
    rw [hJdef]; exact towerJmin_spec hHlo_floor
  have hJf : Real.log 2 < towerDropSumFlat A 1 Hlo Jf := by
    rw [hJfdef]; exact towerFlatJmin_spec hA1 hHlo_floor hfl
  obtain ⟨Hhi, hHhidef⟩ : ∃ Hhi : ℕ,
      Hhi = max (chowlaTower 2 1 Hlo J) (chowlaTowerFlat A 1 Hlo Jf) := ⟨_, rfl⟩
  have hfitL : chowlaTower 2 1 Hlo J ≤ Hhi := by rw [hHhidef]; exact le_max_left _ _
  have hfitFl : chowlaTowerFlat A 1 Hlo Jf ≤ Hhi := by rw [hHhidef]; exact le_max_right _ _
  have hHlohi : Hlo ≤ Hhi := le_trans (chowlaTower_base_ge hHlo_floor J) hfitL
  have hHhi_floor : 4000000 ≤ Hhi := le_trans hHlo_floor hHlohi
  -- ⟦THE WIDTH EXPORT⟧ at the flat shape, on both arms of the endpoint
  have hwidth : Real.log (Real.log (Hhi : ℝ))
      ≤ Real.exp (Real.log (Real.log (Hlo : ℝ)) / 2) := by
    rw [hHhidef, hJdef, hJfdef]
    rcases le_total (chowlaTower 2 1 Hlo (towerJmin 2 1 Hlo))
        (chowlaTowerFlat A 1 Hlo (towerFlatJmin A 1 Hlo)) with h | h
    · rw [max_eq_right h]
      exact towerFlat_width_export hA hHlo_floor hflat
    · rw [max_eq_left h]
      exact le_trans (tower_loglog_le_45 hHlo_floor h50) (pow_nine_halves_le_exp_half h50)
  -- the outer scale at this `ε` and endpoint
  obtain ⟨x, ω, hx2, hω2, hωx, hhead, hhead', hPH, homega, hxb⟩ :=
    regime_outer_param eps heps heps1 Hhi (4 ^ ⌊eps ^ 2 * (Hhi : ℚ)⌋₊) hHhi_floor
  refine ⟨{ x := x, ω := ω, a := 1, eps := eps, Hlo := Hlo, Hhi := Hhi, C0 := 2, J := J,
            hx := hx2, hω := hω2, hωx := hωx, ha := le_refl 1, heps := heps, heps1 := heps1,
            hHlo := le_trans (by norm_num) hHlo_floor, hHlohi := hHlohi, hC0 := le_refl 2,
            hHlo_floor := hHlo_floor, hheadroom := hhead, hcoprime := hcop, hfit := hfitL,
            hJcon := hJ, hheadroom' := hhead', hPHheadroom := hPH, hPNTwindow := hPNT,
            hωbig := homega, hxbig := hxb,
            A := A, hA := hA, hflat := hflat, Jf := Jf,
            hfitF := by simpa using hfitFl, hJconF := by simpa using hJf },
    rfl, rfl, hHlo0, hHlocap, hwidth⟩

/-- **THE HEAD-SHAPED FLAT BUILDER** — the builder plus the outer-scale clearance
    `g H₊ ω ≤ x`, by `regimeFlatEnlargeX` (which carries `Hlo`, `Hhi`, `eps`, `A`
    and all four flat fields verbatim, so every exported conjunct survives). -/
theorem chowlaRegimeFlat_exists_param_head (A : ℝ) (hA : 26 ≤ A) (eps : ℚ) (heps : 0 < eps)
    (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ) (g : ℕ → ℕ → ℕ) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      g R.Hhi R.ω ≤ R.x ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) := by
  obtain ⟨R, hReps, hRA, hRHlo, hRcap, hRwid⟩ :=
    chowlaRegimeFlat_exists_param_gen A hA eps heps heps1 Hlo₀
  exact ⟨regimeFlatEnlargeX R (le_max_left R.x (g R.Hhi R.ω)), hReps, hRA, hRHlo,
    le_max_right _ _, hRcap, hRwid⟩

end Salt.Entropy.Chowla

