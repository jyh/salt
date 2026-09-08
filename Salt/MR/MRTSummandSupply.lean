/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MRTThmA2Stmt

/-!
# THE SUMMAND SUPPLY — MRT A.2/A.3's `P₁`-power term, bounded at last

**Why this file exists.**  Every target in the MRT A-ladder is a SUM, and the campaign's
levers move exactly one summand each.  The map (`MRTPropA3.lean`'s A.6 flag, and the
helm's 2026-08-27 design block) reads, at the `def`s:

```
  MRTLemmaA6   C·( exp(−M/2)/(1+|t−t₁|)  +  (log X)^{−1/16} )
  MRTThmA2     C·( exp(−M)·M  +  (log h)^{1/3}/P₁^{1/6−η}  +  1/(log X)^{1/50} )
  MRTPropA3    C·(T/(X/Q₁)+1)·( (log Q₁)^{1/3}/P₁^{1/6−η} + M/exp M + 1/(log X)^{1/50} )
```

* the `M`-decay summand is supplied by the head constant `c` (`θ`-lift, landed);
* the `1/(log X)^{1/50}` summand is supplied by A.5's own constant through `ρ/3`
  (`mrtA5_epsilon_ceiling`, `mrtA5_rho_margin`);
* the `(log X)^{−1/16}` summand is the Halász GRADE, and
  `b4_grade_cannot_reach_a6_from_head` proves this route cannot reach it;
* **the `P₁`-power summand had NO supplier and NO bound at all** — its only two theorems
  were `mrtA3_bracket_nonneg` (it is `≥ 0`) and `mrtA3_first_term_of_Pseq1_zero` (it is `0`
  at the junk value `P₁ = 0`).  Neither is a bound in the parameters a consumer controls.

**This file supplies that summand.**  It converts the two FREE sequence values `Qseq 1` and
`Pseq 1` out of A.3's first bracket term, and `h` out of A.2's, leaving a bound in the
ambient scale — which is what a consumer of either statement can actually discharge.

⛔ **HONEST LABEL, AND IT IS THE POINT OF §3.**  These are BOUNDS, not smallness statements.
`(log X₀)^{1/6}/P₁^{1/6−η}` is `o(1)` only when `P₁` grows with `X₀`, and
**`MRTBands` DOES NOT FORCE THAT** — §3's `mrtBands_A1_vacuous_at_Pseq_one_two` exhibits the
gap in the kernel.  So the supply is stated in the conditional form a consumer reads
(`mrtA3_first_summand_le_of_floor`), with the missing caller condition named rather than
assumed.  ⛔ **That is a fact about the TRANSCRIPTION, not about MRT** — the same class as
this file's sibling record of the dropped word *"increasing"* (`MRTPropA3.lean`'s
`memS_false_of_band_inverted` section).  MRT's intervals are increasing and their `P_{j-1}`
is large; `MRTBands` carries neither, and repairing that is a statement act (iron rule 1).

⛔ Nothing here touches `MRTBands`, `MRTPropA3`, `MRTThmA2` or any landed statement, and
nothing here bears on twin primes.
-/

namespace Salt.MR

/-! ### §1 — the band condition's own consequence: `Q₁` is small on the log scale -/

/-- **A.3's first band condition, read as a bound on `log Q₁`.**  `MRTBands`' first clause
is `Q₁ ≤ exp(√(log X₀))`; taking logs gives `log Q₁ ≤ √(log X₀)`.  The `Q₁ = 0` junk case is
handled explicitly: `Real.log 0 = 0`, and `√(log X₀) ≥ 0`, so the bound survives it.
⭐ **NO SIZE HYPOTHESIS ON `X₀` IS NEEDED HERE** — `Real.sqrt` is nonnegative on every input,
so the junk branch closes without one.  `1 ≤ X₀` enters one step later, at the rpow. -/
theorem mrtBands_log_Qseq_one_le {X₀ η : ℝ} {Pseq Qseq : ℕ → ℕ}
    (hb : MRTBands X₀ η Pseq Qseq) :
    Real.log (Qseq 1 : ℝ) ≤ Real.sqrt (Real.log X₀) := by
  have hs : (0 : ℝ) ≤ Real.sqrt (Real.log X₀) := Real.sqrt_nonneg _
  rcases Nat.eq_zero_or_pos (Qseq 1) with hQ | hQ
  · simp only [hQ, Nat.cast_zero, Real.log_zero]; exact hs
  · have hQR : (0 : ℝ) < (Qseq 1 : ℝ) := by exact_mod_cast hQ
    have h := Real.log_le_log hQR hb.1
    simpa [Real.log_exp] using h

/-- **A.3's first bracket NUMERATOR, bounded in the ambient scale.**
`(log Q₁)^{1/3} ≤ ((log X₀)^{1/2})^{1/3} = (log X₀)^{1/6}` — the band condition's `√` and
the summand's cube root compose to a SIXTH power, which is the exponent a consumer must
beat with `P₁`. -/
theorem mrtBands_log_Qseq_one_rpow_le {X₀ η : ℝ} {Pseq Qseq : ℕ → ℕ}
    (hX₀ : 1 ≤ X₀) (hb : MRTBands X₀ η Pseq Qseq) :
    (Real.log (Qseq 1 : ℝ)) ^ ((1 : ℝ) / 3) ≤ (Real.log X₀) ^ ((1 : ℝ) / 6) := by
  have hlogX₀ : (0 : ℝ) ≤ Real.log X₀ := Real.log_nonneg hX₀
  calc (Real.log (Qseq 1 : ℝ)) ^ ((1 : ℝ) / 3)
      ≤ (Real.sqrt (Real.log X₀)) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (Real.log_natCast_nonneg _)
          (mrtBands_log_Qseq_one_le hb) (by norm_num)
    _ = (Real.log X₀) ^ ((1 : ℝ) / 6) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlogX₀]; norm_num

/-! ### §2 — the supply, at A.3 and at A.2 -/

/-- **THE SUMMAND SUPPLY AT A.3.**  `MRTPropA3`'s first bracket term is bounded by the same
term with `(log Q₁)^{1/3}` replaced by `(log X₀)^{1/6}` — the free sequence value `Qseq 1`
leaves the summand and the ambient scale takes its place. -/
theorem mrtA3_first_summand_le_of_bands {X₀ η : ℝ} {Pseq Qseq : ℕ → ℕ}
    (hX₀ : 1 ≤ X₀) (hb : MRTBands X₀ η Pseq Qseq) :
    (Real.log (Qseq 1 : ℝ)) ^ ((1 : ℝ) / 3) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η)
      ≤ (Real.log X₀) ^ ((1 : ℝ) / 6) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η) := by
  have hden : (0 : ℝ) ≤ ((Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η))⁻¹ :=
    inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  simpa [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right (mrtBands_log_Qseq_one_rpow_le hX₀ hb) hden

/-- **THE SUMMAND SUPPLY AT A.3, AT THE AMBIENT FLOOR.**  With `MRTPropA3Ambient`'s
`2 ≤ Pseq 1` and A.3's own `η < 1/6`, BOTH free sequence values leave the summand:
`(log Q₁)^{1/3}/P₁^{1/6−η} ≤ (log X₀)^{1/6} / 2^{1/6−η}`. -/
theorem mrtA3_first_summand_le_of_bands_ambient {X₀ η : ℝ} {Pseq Qseq : ℕ → ℕ}
    (hX₀ : 1 ≤ X₀) (hη : η < 1 / 6) (hP : 2 ≤ Pseq 1)
    (hb : MRTBands X₀ η Pseq Qseq) :
    (Real.log (Qseq 1 : ℝ)) ^ ((1 : ℝ) / 3) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η)
      ≤ (Real.log X₀) ^ ((1 : ℝ) / 6) / (2 : ℝ) ^ ((1 : ℝ) / 6 - η) := by
  have hlogX₀ : (0 : ℝ) ≤ Real.log X₀ := Real.log_nonneg hX₀
  have hnum : (0 : ℝ) ≤ (Real.log X₀) ^ ((1 : ℝ) / 6) := Real.rpow_nonneg hlogX₀ _
  have he : (0 : ℝ) < (1 : ℝ) / 6 - η := by linarith
  have h2 : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 6 - η) := Real.rpow_pos_of_pos (by norm_num) _
  have hPR : (2 : ℝ) ≤ (Pseq 1 : ℝ) := by exact_mod_cast hP
  have hpow : (2 : ℝ) ^ ((1 : ℝ) / 6 - η) ≤ (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η) :=
    Real.rpow_le_rpow (by norm_num) hPR he.le
  exact (mrtA3_first_summand_le_of_bands hX₀ hb).trans
    (div_le_div_of_nonneg_left hnum h2 hpow)

/-- **THE SUPPLY IN THE FORM A CONSUMER READS.**  Given the caller floor
`(log X₀)^{1/6} ≤ δ · P₁^{1/6−η}`, A.3's first bracket term is `≤ δ`.  ⭐ **This is the
statement that names the missing hypothesis instead of assuming it**: the floor is exactly
the condition `MRTBands` does not supply (§3). -/
theorem mrtA3_first_summand_le_of_floor {X₀ η δ : ℝ} {Pseq Qseq : ℕ → ℕ}
    (hX₀ : 1 ≤ X₀) (hb : MRTBands X₀ η Pseq Qseq)
    (hP : (0 : ℝ) < (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η))
    (hfloor : (Real.log X₀) ^ ((1 : ℝ) / 6) ≤ δ * (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η)) :
    (Real.log (Qseq 1 : ℝ)) ^ ((1 : ℝ) / 3) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η) ≤ δ := by
  refine (mrtA3_first_summand_le_of_bands hX₀ hb).trans ?_
  rw [div_le_iff₀ hP]
  exact hfloor

/-- **THE SUMMAND SUPPLY AT A.2.**  `MRTThmA2`'s middle term carries `(log h)^{1/3}`, and
A.2's own binders give `3 ≤ h` and `h ≤ X` — so the short-interval length leaves the summand
and the ambient `X` takes its place.  ⛔ The exponent is `1/3`, NOT A.3's `1/6`: A.3 gets the
extra square root from the band condition, and A.2's `h` is capped only by `X`. -/
theorem mrtA2_first_summand_le_of_h {X h η : ℝ} {Pseq : ℕ → ℕ}
    (hh : 3 ≤ h) (hhX : h ≤ X) :
    (Real.log h) ^ ((1 : ℝ) / 3) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η)
      ≤ (Real.log X) ^ ((1 : ℝ) / 3) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η) := by
  have hnn : (0 : ℝ) ≤ Real.log h := Real.log_nonneg (by linarith)
  have hlog : Real.log h ≤ Real.log X := Real.log_le_log (by linarith) hhX
  have hnum : (Real.log h) ^ ((1 : ℝ) / 3) ≤ (Real.log X) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hnn hlog (by norm_num)
  have hden : (0 : ℝ) ≤ ((Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η))⁻¹ :=
    inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hnum hden

/-! ### §3 — why the supply is CONDITIONAL: the bands do not force `P₁` to grow -/

/-- **THE (A.1) CLAUSE IS VACUOUS AT `Pseq 1 = 2`, AND THAT IS WHY §2's SUPPLY CARRIES A
CALLER FLOOR.**  `MRTBands`' second clause at `j = 2` reads
`loglog Q₂ / (log P₁ − 1) ≤ η/16`, and it is meant to force `P₁` LARGE.  At `P₁ = 2` the
denominator is `log 2 − 1 < 0` while the numerator is `≥ 0` for every `Q₂ ≥ e`, so the
quotient is `≤ 0` and the clause holds **for every `Q₂` whatsoever**.

⇒ ***A DIVISION CONSTRAINT LOSES ITS DIRECTION WHEN ITS DENOMINATOR CHANGES SIGN, AND THE
CLAUSE THEN CONSTRAINS NOTHING RATHER THAN FAILING.***  A statement-level repair (`e < P_j`,
or the dropped *"increasing"*) is a statement act and is not taken here — the fact is
recorded in the kernel so §2's floor reads as a named gap, not as timidity. -/
theorem mrtBands_A1_vacuous_at_Pseq_one_two {η : ℝ} {Pseq Qseq : ℕ → ℕ}
    (hη : 0 < η) (hP : Pseq 1 = 2) (hQ : Real.exp 1 ≤ (Qseq 2 : ℝ)) :
    Real.log (Real.log (Qseq 2)) / (Real.log (Pseq (2 - 1)) - 1)
      ≤ η / (4 * (2 : ℝ) ^ 2) := by
  have hnum : (0 : ℝ) ≤ Real.log (Real.log (Qseq 2)) := by
    refine Real.log_nonneg ?_
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hQ
  have hden : Real.log (Pseq (2 - 1) : ℝ) - 1 < 0 := by
    have h1 : (2 : ℕ) - 1 = 1 := by norm_num
    rw [h1, hP]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have hle0 : Real.log (Real.log (Qseq 2)) / (Real.log (Pseq (2 - 1) : ℝ) - 1) ≤ 0 := by
    rcases eq_or_lt_of_le hnum with h | h
    · simp [← h]
    · exact (div_neg_of_pos_of_neg h hden).le
  have hrhs : (0 : ℝ) ≤ η / (4 * (2 : ℝ) ^ 2) := div_nonneg hη.le (by norm_num)
  linarith

/-- **THE CONTROL, AND IT IS WHAT MAKES THE VACUITY A FINDING RATHER THAN AN ARTEFACT.**
The clause above is not toothless in general — it is toothless AT `P₁ = 2`.  One prime up, at
`P₁ = 3`, the denominator `log 3 − 1` is POSITIVE (`e < 3`) and at most `1`
(`log 3 ≤ 3 − 1`), so any `Q₂` with `loglog Q₂ ≥ 1` makes the quotient `≥ 1`, while the
bound `η/16 < 1/96` for every admissible `η < 1/6`.  **The clause REFUSES.**

⇒ 🔑 ***A CONTROL IS A MEASUREMENT AND HAS TO BE MEASURED TOO*** — without this name, the
theorem above reads as "the (A.1) clause is weak", which is false; what is true is that its
DENOMINATOR CHANGES SIGN at `P₁ = 2`, and the sign change is the whole content. -/
theorem mrtBands_A1_binds_at_Pseq_one_three {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6)
    {Pseq Qseq : ℕ → ℕ} (hP : Pseq 1 = 3)
    (hQ : 1 ≤ Real.log (Real.log (Qseq 2))) :
    ¬ (Real.log (Real.log (Qseq 2)) / (Real.log (Pseq (2 - 1)) - 1)
        ≤ η / (4 * (2 : ℝ) ^ 2)) := by
  have h1 : (2 : ℕ) - 1 = 1 := by norm_num
  have hlb : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hub : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  intro hle
  rw [h1, hP] at hle
  push_cast at hle
  have hdpos : (0 : ℝ) < Real.log 3 - 1 := by linarith
  rw [div_le_iff₀ hdpos] at hle
  have hcoef : (0 : ℝ) ≤ η / (4 * (2 : ℝ) ^ 2) := div_nonneg hη0.le (by norm_num)
  have hstep : η / (4 * (2 : ℝ) ^ 2) * (Real.log 3 - 1) ≤ η / (4 * (2 : ℝ) ^ 2) * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) hcoef
  have hsmall : η / (4 * (2 : ℝ) ^ 2) < 1 := by linarith
  linarith

end Salt.MR
