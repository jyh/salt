/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.V7Ks

/-!
# `V7Headline` — ⟦DREAM-SPACE⟧ the `g ≡ 0` instance: `logChowla2_ineffective_v7_headline`

⟦DREAM-SPACE, night 08/14 — branch artifact; consumes nothing until waking review; the V7-D
question in the T2-A brief §5(iv) remains the Captain's⟧

`V7Ks.logChowla2_ineffective_v7_ksarm` carries TWO inner riders (`XCeilRiderStrict ε g` on the
caller's own function, and the `K_vt` cushion).  This file proposes the HEADLINE instance: the
caller's function is EXHIBITED as `g := fun _ _ => 0`, its rider discharged in-file, leaving
**one** inner rider — the `K_vt` cushion.

## What is here

`logChowla2_ineffective_v7_headline` is `…_ksarm` with the inner `∀ g, XCeilRiderStrict ε g → …`
removed and the body taken at `g := fun _ _ : ℕ => 0`.  The statement diff against the parent is
exactly the name and TWO lines:

```
-      (∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
+      (∃ R : ChowlaRegime,
-        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
+        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ 0 ≤ R.x ∧
```

The second is the beta-reduction of `(fun _ _ : ℕ => 0) R.Hhi R.ω ≤ R.x`; every other conjunct,
including the indentation of the block, is byte-faithful to the parent.  The proof passes the
parent's own `hRg` through, so the kernel — not the prose — is what certifies that `0 ≤ R.x` is
the instantiated conjunct and not a substitute.

## The rider's discharge

`XCeilRiderStrict ε (fun _ _ => 0)` unfolds to: on `XCeilGate ε H₊ ω`,
`log 0 + ε²·H₊ ≤ (31/ε)·H₊`.  `Real.log_zero` collapses the first summand to `0`, and the gate's
own third field is `log ω + ε²·H₊ ≤ (31/ε)·H₊` with `log ω ≥ 0` — the ε²·H₊ margin the gate
already carries is the whole payment.  This is the witness pattern already in-body at
`RegisterCompose.lean:245-253` and `XThread.lean:1247`, lifted here to the terminal.

## What this instance does and does not say

⟦THE SURVIVING LIST⟧ outer hypotheses: NOTHING.  Inner, exactly **one** item — the `K_vt`
cushion
`32·Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊ + 32·(2·log (flatDoorM A) + log 4 + 50) ≤ log R.Hhi / 4`.

⟦THE HONEST READING OF `0 ≤ R.x`⟧ at `g ≡ 0` the `g`-conjunct is vacuous: `R.x : ℕ`, so
`0 ≤ R.x` holds of every regime (the structure's own `hx` already gives `2 ≤ R.x`).  That is the
price of exhibiting `g`, and it is the point of the parent's `∀ g` form: the parent promises a
regime whose outer scale clears the CALLER's requested floor `g R.Hhi R.ω`, at any `g` meeting
the rider; the headline promises only the regime, with no floor requested.  The headline is a
SPECIALIZATION of the parent — strictly weaker as a statement, and it is the parent, not this
file, that carries the caller-facing content.  Nothing here is a strengthening of `…_ksarm`.

⟦STILL INEFFECTIVE⟧ A2's word is carried unchanged.  The `K_vt` cushion is the Siegel-genre core
and this file does not touch it; only the caller-side `XCeil` rider, an artefact of the `∀ g`
interface, is gone at the exhibited `g`.

**PURELY ADDITIVE.** `logChowla2_ineffective_v7_ksarm`, `V7E.logChowla2_ineffective_v7`,
`…_v6`, `…_v6_csarm`, `…_v6_T0arm` and every parent are byte-untouched and remain citable.  The
hub import (`Salt/MR/All.lean`) is NOT taken — it is owed to the waking review.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla
open scoped BigOperators

/-! ## §1 — ⟦THE EXHIBITED CALLER⟧ `g ≡ 0` meets the strict rider -/

/-- **⟦DREAM-SPACE, night 08/14 — branch artifact; consumes nothing until waking review⟧**

**⟦THE ZERO CALLER⟧** (`xceilRiderStrict_zero`) — the constant-zero request meets
`XCeilRiderStrict` at every `ε`.  `log 0 = 0` and the gate's own width window carries the
`ε²·H₊` margin; `log ω ≥ 0` closes it.  (The witness pattern of `RegisterCompose.lean:245-253`,
named here so the terminal can cite it.) -/
theorem xceilRiderStrict_zero (ε : ℚ) : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := by
  intro Hhi ω hgate
  obtain ⟨-, -, hωw⟩ := hgate
  simp only [Nat.cast_zero, Real.log_zero]
  linarith [Real.log_natCast_nonneg ω]

/-! ## §2 — ⟦THE PROPOSED HEADLINE⟧ `…_ksarm` at the exhibited `g` -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 3200000 in
/-- **⟦DREAM-SPACE, night 08/14 — branch artifact; consumes nothing until waking review; the
V7-D question in the T2-A brief §5(iv) remains the Captain's⟧**

**⟦THE `g ≡ 0` INSTANCE⟧** (`logChowla2_ineffective_v7_headline`) —
`V7Ks.logChowla2_ineffective_v7_ksarm` with the inner `∀ g, XCeilRiderStrict ε g → …` taken at
`g := fun _ _ => 0`, the rider discharged by `xceilRiderStrict_zero`.

⟦THE SURVIVING LIST⟧ outer hypotheses: NOTHING.  Inner, exactly **one** item:

* the `K_vt` cushion
  `32·Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊ + 32·(2·log (flatDoorM A) + log 4 + 50) ≤ log R.Hhi / 4`.

⟦WHAT MOVED⟧ the caller-side rider is not asked because the caller is EXHIBITED.  The `∃`-prefix
is the parent's, unchanged and in order, including the delivered `Real.exp (-100) ≤ cs`, `3 ≤ T₀`
and `0 < Ks`.

⟦WHAT IT COSTS, NAMED⟧ the `g`-conjunct degenerates: `(fun _ _ => 0) R.Hhi R.ω ≤ R.x` is
`0 ≤ R.x`, true of every `ChowlaRegime` (`R.x : ℕ`).  So this instance carries none of the
parent's caller-facing content; it is a SPECIALIZATION, strictly weaker than `…_ksarm`, and the
parent remains the statement of record for a caller with its own outer-scale request.

⟦STILL INEFFECTIVE⟧ the name is unchanged on purpose: the `K_vt` cushion is untouched.

`logChowla2_ineffective_v7_ksarm`, `logChowla2_ineffective_v7`, `…_v6`, `…_v6_csarm` and
`…_v6_T0arm` are byte-untouched and remain citable. -/
theorem logChowla2_ineffective_v7_headline (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ 0 ≤ R.x ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
            + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
          ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
    a15, a16, a17, a18, a19, a20, a21, a22, hmain⟩ := logChowla2_ineffective_v7_ksarm A₀
  -- ⟦RIDER 1, DISCHARGED AT THE EXHIBITED CALLER⟧ §1
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hdes, hwin, hfire⟩ :=
    hmain (fun _ _ : ℕ => 0) (xceilRiderStrict_zero ε)
  exact ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
    a15, a16, a17, a18, a19, a20, a21, a22,
    R, hReps, hHlo, hRg, hRtow, hdes, hwin, hfire⟩

end Salt.MR

end
