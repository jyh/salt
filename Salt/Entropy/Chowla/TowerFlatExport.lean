/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# THE A-FREE WIDTH EXPORT of the flat tower (freeze F-5) + THE SHAPE BRIDGE

`TowerFlat.towerFlat_width_le` brackets the flat tower's width by
`(λ₊ + c) ≤ (21/20)·4^A·(λ₋ + c)` — a statement in which the design constant `A`
appears explicitly.  FLAT-REF's ruling F-5 is that the export the MR register
hosts must be stated **A-FREE**: under the design law `3.2·A ≤ λ₋` (with
`26 ≤ A`) the whole right-hand side collapses to `e^{λ₋/2}`, and that is the
shape the register's `half`-capped `λ₊ ≤ 898·e^{λ₋/2}` accommodates and the shape
the MR λ-engine consumes.  Keeping the export A-free is what bounds the blast
radius: the MR cone then changes ONE SHAPE,

    `λ₊ ≤ λ₋ ^ (9/2)`   ⟶   `λ₊ ≤ e^{λ₋/2}`,

instead of acquiring an `A`-dependence at 101 sites.

## What is here

* `flatWidth_coef`, `flatWidth_engine_at`, `flatWidth_engine` — the symbolic
  engine.  `flatWidth_engine_at` is FLAT-REF's probe F11 (the design point
  `λ = 3.2·A`); `flatWidth_engine` extends it to the whole design half-line
  `λ ≥ 3.2·A` by one `1 + x ≤ e^x` step against `flatWidth_coef`.  No numeral for
  `A` appears anywhere: `A` is a free real with `26 ≤ A`.
* `towerFlat_width_export` — **freeze F-5**, the export itself.
* `pow_nine_halves_le_exp_half` — **THE SHAPE BRIDGE** `λ^{9/2} ≤ e^{λ/2}` on the
  guard `λ ≥ 50`.  The landed tower conjunct is therefore STRICTLY STRONGER than
  the flat one, so every flat CARRIER twin is derivable from its landed original
  by one monotone rewrite, and (dually) every flat CONSUMER twin is strictly
  stronger than its landed original.  This is what makes the shape substitution
  additive rather than a re-derivation.
* `flat_lambda_core`, `flat_lambda_core_17` — FLAT-REF's probe F10: the MR
  λ-engine at the flat export shape, at the two coefficients the cone spends
  (`2·10^{-4}` for `S12ConstCompose`, `1.7·10^{-3}` for `S15Compose`).

Everything is ADDITIVE: no landed declaration is touched.
-/
import Salt.Entropy.Chowla.TowerFlatRegime

namespace Salt.Entropy.Chowla

/-! ### Section 1 — the symbolic width engine (no numeral in `A`) -/

/-- `(21/10)·4^A ≤ e^{3.2A/2}` for `A ≥ 26` — the SLOPE half of the engine: it is
    what lets the design half-line `λ ≥ 3.2·A` be walked by a single
    `1 + x ≤ e^x`.  At logs the demand is `log(21/10) + A·log 4 ≤ 1.6·A`, i.e.
    `1.1 ≤ 0.2137·A`, free from `A ≥ 26` by a factor `5`. -/
theorem flatWidth_coef {A : ℝ} (hA : 26 ≤ A) :
    (21 / 10) * (4 : ℝ) ^ A ≤ Real.exp (3.2 * A / 2) := by
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := flat_log_four
  have h2110 : Real.log (21 / 10) ≤ 1.1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 21 / 10 by norm_num)
    linarith
  rw [← Real.log_le_log_iff (by positivity) (Real.exp_pos _), Real.log_exp,
    Real.log_mul (by norm_num) (ne_of_gt h4pos), Real.log_rpow (by norm_num), h4]
  nlinarith [mul_le_mul_of_nonneg_left hl2.le (show (0 : ℝ) ≤ A by linarith)]

/-- **FLAT-REF probe F11** — the engine AT the design point `λ = 3.2·A`:
    `(21/20)·4^A·(3.2A + log 2A) ≤ e^{3.2A/2}` for every `A ≥ 26`.  Proved at
    logs, with `log S ≤ 9·log 2 − 1 + S/512` paying the `log` of the width. -/
theorem flatWidth_engine_at {A : ℝ} (hA : 26 ≤ A) :
    (21 / 20) * ((4 : ℝ) ^ A * (3.2 * A + Real.log (2 * A)))
      ≤ Real.exp (3.2 * A / 2) := by
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := flat_log_four
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have hlog2A : Real.log (2 * A) ≤ 2 * A - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hlog2Anonneg : (0 : ℝ) ≤ Real.log (2 * A) := Real.log_nonneg (by linarith)
  set S : ℝ := 3.2 * A + Real.log (2 * A) with hS
  have hSpos : (0 : ℝ) < S := by rw [hS]; linarith
  have hS5 : S ≤ 5.2 * A := by rw [hS]; linarith
  have hlogS : Real.log S ≤ 9 * Real.log 2 - 1 + S / 512 := by
    have h512 : Real.log (S / 512) ≤ S / 512 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hsplit : Real.log S = Real.log 512 + Real.log (S / 512) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
    have h512v : Real.log 512 = 9 * Real.log 2 := by
      rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    rw [hsplit, h512v]; linarith
  have hLHSpos : (0 : ℝ) < (21 / 20) * ((4 : ℝ) ^ A * S) := by positivity
  rw [← Real.log_le_log_iff hLHSpos (Real.exp_pos _)]
  have hlogL : Real.log ((21 / 20) * ((4 : ℝ) ^ A * S))
      = Real.log (21 / 20) + (A * Real.log 4 + Real.log S) := by
    rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (ne_of_gt h4pos) (ne_of_gt hSpos), Real.log_rpow (by norm_num)]
  have h2120 : Real.log (21 / 20) ≤ 1 / 20 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 21 / 20 by norm_num)
    linarith
  rw [hlogL, Real.log_exp, h4]
  nlinarith [hlogS, hS5, h2120, hl2lo, hl2hi, hA, hSpos]

/-- **THE SYMBOLIC WIDTH ENGINE** — `flatWidth_engine_at` on the whole design
    half-line.  For `A ≥ 26` and any `λ ≥ 3.2·A`,

        `(21/20)·4^A·(log 2A + λ) ≤ e^{λ/2}`.

    The step from the design point is one `1 + x ≤ e^x`: the extra width
    `λ − 3.2A` is charged linearly on the left and pays for itself on the right
    through `flatWidth_coef`. -/
theorem flatWidth_engine {A lam : ℝ} (hA : 26 ≤ A) (hlam : 3.2 * A ≤ lam) :
    (21 / 20) * ((4 : ℝ) ^ A * (Real.log (2 * A) + lam)) ≤ Real.exp (lam / 2) := by
  have hbase := flatWidth_engine_at hA
  have hcoef := flatWidth_coef hA
  have ht : (0 : ℝ) ≤ lam - 3.2 * A := by linarith
  have hEpos : (0 : ℝ) < Real.exp (3.2 * A / 2) := Real.exp_pos _
  have hsplit : Real.exp (lam / 2)
      = Real.exp (3.2 * A / 2) * Real.exp ((lam - 3.2 * A) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hlin : 1 + (lam - 3.2 * A) / 2 ≤ Real.exp ((lam - 3.2 * A) / 2) := by
    linarith [Real.add_one_le_exp ((lam - 3.2 * A) / 2)]
  have hprod : Real.exp (3.2 * A / 2) * (1 + (lam - 3.2 * A) / 2) ≤ Real.exp (lam / 2) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hlin hEpos.le
  have hid : Real.exp (3.2 * A / 2) * (1 + (lam - 3.2 * A) / 2)
      = Real.exp (3.2 * A / 2) + Real.exp (3.2 * A / 2) * ((lam - 3.2 * A) / 2) := by ring
  have hmul : (21 / 20) * (4 : ℝ) ^ A * (lam - 3.2 * A)
      ≤ Real.exp (3.2 * A / 2) * ((lam - 3.2 * A) / 2) := by nlinarith [hcoef, ht]
  have hLHS : (21 / 20) * ((4 : ℝ) ^ A * (Real.log (2 * A) + lam))
      = (21 / 20) * ((4 : ℝ) ^ A * (3.2 * A + Real.log (2 * A)))
        + (21 / 20) * (4 : ℝ) ^ A * (lam - 3.2 * A) := by ring
  rw [hLHS]
  linarith [hprod, hid.le, hid.ge]

/-! ### Section 2 — freeze F-5: the export -/

/-- **THE A-FREE WIDTH EXPORT** (freeze F-5).  Under the design law
    `3.2·A ≤ loglog B` (and `26 ≤ A`, and the house regime floor `4·10⁶ ≤ B`)
    the flat tower's terminal width at its MINIMAL crossing length obeys

        `loglog (chowlaTowerFlat A 1 B (towerFlatJmin A 1 B)) ≤ exp (loglog B / 2)`.

    `A` has left the statement.  This is the shape `S12ConstCompose`'s λ-engine
    consumes (`flat_lambda_core`) and the shape the register's cap+frame face
    hosts with a uniform `~400×` margin — the whole point of stating the export
    A-free rather than at `(21/20)·4^A·(λ₋ + c)`. -/
theorem towerFlat_width_export {A : ℝ} (hA : 26 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hflat : 3.2 * A ≤ Real.log (Real.log (B : ℝ))) :
    Real.log (Real.log (chowlaTowerFlat A 1 B (towerFlatJmin A 1 B) : ℝ))
      ≤ Real.exp (Real.log (Real.log (B : ℝ)) / 2) := by
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hfl := flatFloor_of_design hA hB hflat
  have hwid := towerFlat_width_le hA1 hB hfl
  have hlam0 : towerLamF A B 0 = Real.log (Real.log (B : ℝ)) := towerLamF_zero A B
  have hcpos : 0 < flatC A := flatC_pos hA1
  have hengine := flatWidth_engine hA hflat
  rw [hlam0] at hwid
  have hc : flatC A = Real.log (2 * A) := rfl
  rw [hc] at hwid
  have hgoal : towerLamF A B (towerFlatJmin A 1 B)
      = Real.log (Real.log (chowlaTowerFlat A 1 B (towerFlatJmin A 1 B) : ℝ)) := rfl
  rw [← hgoal]
  rw [hc] at hcpos
  linarith

/-! ### Section 3 — THE SHAPE BRIDGE and the flat λ-engine -/

/-- `9·log λ ≤ λ` for `λ ≥ 50` — the arithmetic behind the shape bridge.  From
    `log (λ/20) ≤ λ/20 − 1` and `log 20 ≤ 5·log 2`. -/
theorem nine_log_le_self {lam : ℝ} (hlam : 50 ≤ lam) : 9 * Real.log lam ≤ lam := by
  have hpos : (0 : ℝ) < lam := by linarith
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h20 : Real.log (lam / 20) ≤ lam / 20 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hsplit : Real.log (lam / 20) = Real.log lam - Real.log 20 :=
    Real.log_div (ne_of_gt hpos) (by norm_num)
  have hlog20 : Real.log 20 ≤ 5 * Real.log 2 := by
    have h : Real.log 20 ≤ Real.log 32 := Real.log_le_log (by norm_num) (by norm_num)
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow] at h
    push_cast at h
    linarith
  linarith

/-- **THE SHAPE BRIDGE** — `λ^{9/2} ≤ e^{λ/2}` on the guard the tower conjunct
    carries (`50 ≤ λ₋`).

    ⟦WHAT IT MEANS FOR THE WAVE⟧  The landed conjunct `λ₊ ≤ λ₋^{9/2}` therefore
    IMPLIES the flat conjunct `λ₊ ≤ e^{λ₋/2}`; the implication is one-way.  So

    * a CARRIER (the conjunct in the payload of an `∃`) has a flat twin that is
      strictly WEAKER — provable from the landed original by one rewrite;
    * a CONSUMER (the conjunct as a hypothesis) has a flat twin that is strictly
      STRONGER — genuine new content, paid for by `flat_lambda_core`.

    That asymmetry is what makes the whole shape substitution additive.  When the
    flat regime builder replaces the landed root, the carriers' proofs are the
    only thing that moves, and they move by deleting this bridge step. -/
theorem pow_nine_halves_le_exp_half {lam : ℝ} (hlam : 50 ≤ lam) :
    lam ^ ((9 : ℝ) / 2) ≤ Real.exp (lam / 2) := by
  have hpos : (0 : ℝ) < lam := by linarith
  have hkey : (9 : ℝ) / 2 * Real.log lam ≤ lam / 2 := by
    linarith [nine_log_le_self hlam]
  calc lam ^ ((9 : ℝ) / 2) = Real.exp ((9 / 2 : ℝ) * Real.log lam) := by
        rw [Real.rpow_def_of_pos hpos]; ring_nf
    _ ≤ Real.exp (lam / 2) := Real.exp_le_exp.mpr hkey

/-- **THE MR λ-ENGINE AT THE FLAT EXPORT SHAPE** (FLAT-REF probe F10), at the
    `500×` coefficient `S12ConstCompose` spends: for `λ ≥ 50`,

        `14·e^{λ/2} + 10^{15} ≤ 2·10^{−4}·e^λ`.

    The landed engine `s12c_lambda_core` is the same statement with `λ^{9/2}` on
    the left; by `pow_nine_halves_le_exp_half` this one is strictly stronger.
    Proof: with `u = e^{λ/2} ≥ e^{25} ≥ 6·10^{10}` one has `e^λ = u²`, so the
    demand is `14u + 10^{15} ≤ 2·10^{−4}·u²` — true with margin `~700` at the
    floor and improving. -/
theorem flat_lambda_core {lam : ℝ} (hlam : 50 ≤ lam) :
    14 * Real.exp (lam / 2) + 1000000000000000 ≤ 0.0002 * Real.exp lam := by
  set u : ℝ := Real.exp (lam / 2) with hu
  have hupos : (0 : ℝ) < u := Real.exp_pos _
  have husq : u * u = Real.exp lam := by
    rw [hu, ← Real.exp_add]; congr 1; ring
  have h25 : Real.exp (25 : ℝ) ≤ u := by
    rw [hu]; exact Real.exp_le_exp.mpr (by linarith)
  have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h25v : (6e10 : ℝ) ≤ Real.exp (25 : ℝ) := by
    have h : Real.exp (25 : ℝ) = (Real.exp 1) ^ (25 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    have hc : (2.7 : ℝ) ^ (25 : ℕ) ≤ (Real.exp 1) ^ (25 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he1.le 25
    have hn : (6e10 : ℝ) ≤ (2.7 : ℝ) ^ (25 : ℕ) := by norm_num
    linarith
  have hulo : (6e10 : ℝ) ≤ u := le_trans h25v h25
  nlinarith [hulo, hupos, husq]

/-- The flat λ-engine at `S15Compose`'s coefficient `1.7·10^{−3}` — a weakening of
    `flat_lambda_core`, since `e^λ > 0`. -/
theorem flat_lambda_core_17 {lam : ℝ} (hlam : 50 ≤ lam) :
    14 * Real.exp (lam / 2) + 1000000000000000 ≤ 0.0017 * Real.exp lam := by
  have h := flat_lambda_core hlam
  have hpos : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  linarith

/-! ### Section 4 — THE SWAP POINT: a flat regime supplies the MR conjunct -/

/-- **THE GUARD IS FREE ON THE FLAT ROAD.**  The MR tower conjunct is guarded by
    `50 ≤ loglog H₋`; the design law gives `loglog H₋ ≥ 3.2·A ≥ 83.2` outright.
    So no consumer of a flat regime ever has to discharge the guard. -/
theorem ChowlaRegimeFlat.loglog_ge_fifty (R : ChowlaRegimeFlat) :
    50 ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
  have h1 := R.hA
  have h2 := R.hflat
  linarith

/-- **THE SWAP POINT** — a flat regime whose upper endpoint is its own flat tower
    at the minimal crossing length SUPPLIES the flat MR conjunct

        `50 ≤ loglog H₋ → loglog H₊ ≤ exp (loglog H₋ / 2)`

    directly from freeze F-5, with no `9/2` law anywhere in the derivation.

    ⟦WHAT THIS IS FOR⟧  The flat carrier twins in `Salt.MR` (`HloExportMRFlat`,
    and the capstone twins) are today rooted, through their landed originals, in
    the landed `9/2` producer plus `pow_nine_halves_le_exp_half`.  THIS theorem is
    the replacement root: when the flat regime builder lands, each carrier's
    `obtain` re-points at a flat producer built on this, the bridge step is
    deleted, and NO STATEMENT MOVES.  That is what the whole shape substitution
    buys. -/
theorem chowlaRegimeFlat_tower_conjunct (R : ChowlaRegimeFlat)
    (hHhi : R.Hhi = chowlaTowerFlat R.A 1 R.Hlo (towerFlatJmin R.A 1 R.Hlo)) :
    50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) := by
  intro _
  rw [hHhi]
  exact towerFlat_width_export R.hA R.hHlo_floor R.hflat

end Salt.Entropy.Chowla
