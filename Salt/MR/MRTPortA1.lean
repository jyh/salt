/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MRTPort
import Salt.MR.MRTThmA1

/-!
# The MRT port (item 15) — the λ-instantiation chain (nodes D2, D3, D4)

Dispatched from the frozen executor brief
`seat/briefs/2026-08-25-item15-D-WAVE-EXECUTOR-BRIEF-FROZEN.md`, node D2.  The three
statements below are the **door-composition gate v2's own**, copied verbatim from that
brief; they are not the maestro's or this executor's paraphrase.

| node | declaration |
|---|---|
| **D2** | `mrtM_lam_eq_lamCoeff` |
| **D3** | `lamCoeff_mul_coprime` |
| **D4** | `mrtThmA1_at_lamCoeff` |

Together they carry MRT Theorem A.1 (`MRTThmA1`, `MRTThmA1.lean:88`) from its universally
quantified 1-bounded multiplicative datum to the **one** coefficient sequence the port
needs, `lamCoeff` (`M4Window.lean:73`), and reconcile A.1's quality quantity `mrtM` with
the spelling `lam` in which the landed λ-quality supply `mrtM_lam_lower`
(`MRTQualityLam.lean:75`) states its lower bound.

⛔ **SCOPE, stated once for the whole file.**  These three close **named residuals** of
the MRT port.  They do **not** compose to the door.  Two research gaps remain open above
them and are explicitly NOT closed here:

* **GAP α — the major arc.**  The door datum is *phased* (`doorCoeffPhase c α`); A.1
  carries no frequency at all.  Class D.
* **GAP A.1 — the primary itself.**  `MRTThmA1` is a `def … : Prop` with **no producer**;
  the stack beneath it (`MRTThmA1GJ` → `MRTParsevalConstantMatch`) is open.  Class D.

So `mrtThmA1_at_lamCoeff` below is an *implication from* `MRTThmA1 C`, not a theorem of
MRT A.1 at λ.  Nothing here asserts A.1 holds.
-/

namespace Salt.MR

/-! ## D2 — `mrtM` is blind to the `lam` / `lamCoeff` spelling -/

/-- **D2 — `M(lam; X) = M(lamCoeff; X)`.**

`mrtM g X = sInf {m | ∃ t, |t| ≤ X ∧ m = pretDistSq g (costwist t) X}`
(`MRTProp24.lean:175-176`) places `g` in `pretDistSq`'s **left** slot, and
`pretDistSq_lam_eq_lamCoeff` (`MRTPort.lean:255`, node N3) rewrites exactly that slot for
every twist.  The two `sInf` index sets are therefore literally equal: one `Set.ext`, no
analysis and no `sInf` theory.  This is what lets the S5 non-pretentiousness stone (stated
at `lam`) and A.1's right-hand side (stated at `lamCoeff`) meet on one object. -/
theorem mrtM_lam_eq_lamCoeff (X : ℝ) : mrtM lam X = mrtM lamCoeff X := by
  unfold mrtM
  congr 1
  ext m
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, (pretDistSq_lam_eq_lamCoeff (costwist t) X)⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, (pretDistSq_lam_eq_lamCoeff (costwist t) X).symm⟩

/-! ## D3 — the coprime-multiplicativity binder A.1 asks for -/

/-- **D3 — `λ(mn) = λ(m)λ(n)` in the shape `MRTThmA1` consumes.**

`liouvilleC_mul` (`M4Residue.lean:103`) is **unconditional** — complete
multiplicativity, no coprimality and no nonvanishing side conditions — and
`lamCoeff_eq_liouvilleC` (`M4Exit.lean:99`) is `rfl`.  The coprimality binder is therefore
consumed unused (hence `_hmn`), exactly as `mrtCompMultDatum_lamCoeff` consumes its two
`≠ 0` binders (`MRTPort.lean:301`).  Stronger discharges weaker; the binder is kept
because A.1's statement is what fixes the shape. -/
theorem lamCoeff_mul_coprime (m n : ℕ) (_hmn : Nat.Coprime m n) :
    lamCoeff (m * n) = lamCoeff m * lamCoeff n := by
  rw [lamCoeff_eq_liouvilleC]
  exact liouvilleC_mul m n

/-! ## D4 — A.1 instantiated at `lamCoeff` -/

/-- **D4 — MRT Theorem A.1 at the Liouville coefficient sequence.**

One `exact`.  Two of the three data binders are projections of the landed
`mrtCompMultDatum_lamCoeff` (`MRTPort.lean:301`); the third is D3.

⚠️ The middle right-hand term is `(log log h)^2 / (log h)^2` — **squared** denominator.
`MRTThmA1`'s transcription was repaired to the source's form at commit `46b7a5a9`
(`MRTThmA1.lean:94`); a statement written against the older unsquared byte will not
elaborate.

⛔ This is an **implication from** `MRTThmA1 C`.  `MRTThmA1` has no producer in the
corpus, so nothing here asserts A.1 itself. -/
theorem mrtThmA1_at_lamCoeff {C : ℝ} (hA1 : MRTThmA1 C) {X h : ℝ}
    (hh : 10 ≤ h) (hhX : h ≤ X) :
    (1 / X) * (∫ x in X..(2 * X), ‖mrtShortMean lamCoeff h x‖ ^ 2)
      ≤ C * (Real.exp (-(mrtM lamCoeff X))
            + (Real.log (Real.log h)) ^ 2 / Real.log h ^ 2
            + 1 / (Real.log X) ^ ((1 : ℝ) / 50)) :=
  hA1 lamCoeff mrtCompMultDatum_lamCoeff.norm_le_one mrtCompMultDatum_lamCoeff.map_one
    lamCoeff_mul_coprime X h hh hhX

end Salt.MR
