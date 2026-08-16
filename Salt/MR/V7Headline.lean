/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.V7Ks

/-!
# `V7Headline` — ⟦DREAM-SPACE⟧ the `g ≡ 0` instance: `logChowla2_ineffective_v7_ksarm_g0`

⟦DREAM-SPACE, night 08/14 — branch artifact; consumes nothing until waking review; the V7-D
question in the T2-A brief §5(iv) remains the Captain's⟧

`V7Ks.logChowla2_ineffective_v7_ksarm` carries TWO inner riders (`XCeilRiderStrict ε g` on the
caller's own function, and the `K_vt` cushion).  This file states that terminal read at `g ≡ 0`:
the caller's function is EXHIBITED as `g := fun _ _ => 0`, its rider discharged in-file, leaving
**one** inner rider — the `K_vt` cushion.

## What is here

`logChowla2_ineffective_v7_ksarm_g0` is `…_ksarm` with the inner `∀ g, XCeilRiderStrict ε g → …`
removed and the body taken at `g := fun _ _ : ℕ => 0`.  The statement diff against the parent is
exactly the name and TWO lines:

```
-      (∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
+      (∃ R : ChowlaRegime,
-        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
+        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
```

The second line DROPS the `g`-conjunct rather than carrying it: at `g ≡ 0` it beta-reduces to
`0 ≤ R.x`, which holds of every regime (`R.x : ℕ`; the structure's own `hx` already gives
`2 ≤ R.x`), so carrying it would put a conjunct in the statement that says nothing.  That is the
choice `V7E.logChowla2_ineffective_v7_g0` made on `main`, and it is made here for the same
reason.  Every other conjunct, including the indentation of the block, is byte-faithful to the
parent; the proof discards the parent's own `hRg` and passes the rest through unchanged.

## The rider's discharge

`XCeilRiderStrict ε (fun _ _ => 0)` unfolds to: on `XCeilGate ε H₊ ω`,
`log 0 + ε²·H₊ ≤ (31/ε)·H₊`.  `Real.log_zero` collapses the `log 0` summand to `0`, and the
gate's own third field is `log ω + ε²·H₊ ≤ (31/ε)·H₊` with `log ω ≥ 0` — the ε²·H₊ margin the
gate already carries is the whole payment.  This is the witness pattern already in-body at
`RegisterCompose.lean:247-251`, `XThread.lean:1247` and `V7B.lean:1760`, lifted here to the
terminal.

## What this instance does and does not say

⟦THE SURVIVING LIST⟧ outer hypotheses: NOTHING.  Inner, exactly **one** item — the `K_vt`
cushion
`32·Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊ + 32·(2·log (flatDoorM A) + log 4 + 50) ≤ log R.Hhi / 4`.

⟦WHAT `0 ≤ R.x` DOES NOT SAY⟧ at `g ≡ 0` the `g`-conjunct is vacuous: `R.x : ℕ`, so `0 ≤ R.x`
holds of every regime.  That is the price of exhibiting `g`, and it is the point of the parent's
`∀ g` form: the parent promises a regime whose outer scale clears the CALLER's requested floor
`g R.Hhi R.ω`, at any `g` meeting the rider; this instance promises only the regime, with no
floor requested — which is why the degenerate conjunct is dropped from the statement instead of
being displayed as though it carried content.  This instance is a SPECIALIZATION of the parent —
strictly weaker as a statement, and it is the parent, not this file, that carries the
caller-facing content.  Nothing here is a strengthening of `…_ksarm`.

⟦STILL INEFFECTIVE⟧ A2's word is carried unchanged.  The `K_vt` cushion is the Siegel-genre core
and this file does not touch it; only the caller-side `XCeil` rider, an artefact of the `∀ g`
interface, is gone at the exhibited `g`.  And the parent's own relocation is inherited whole: the
ineffective load formerly borne by the `Ks` rider is borne by the DESIGN CONSTANT `A`, through
`…_ksarm`'s seventh `max` arm `16·log(1/Ks)/3`, so this object's ineffectivity sits in `K_vt`
AND in `A` — and `A` indexes the cushion through `KlevF A` and `flatDoorM A`, so the two are
coupled, not independent.

**PURELY ADDITIVE.** `logChowla2_ineffective_v7_ksarm`, `V7E.logChowla2_ineffective_v7`,
`…_v6`, `…_v6_csarm`, `…_v6_T0arm` and every parent are byte-untouched and remain citable.  The
hub import (`Salt/MR/All.lean`) IS taken, with the roll-call stanza and the `#audit_axioms` line.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla
open scoped BigOperators

/-! ## §1 — ⟦THE EXHIBITED CALLER⟧ `g ≡ 0` meets the strict rider -/

/-- **⟦DREAM-SPACE, night 08/14 — branch artifact; consumes nothing until waking review⟧**

**⟦THE ZERO CALLER⟧** (`xceilRiderStrict_zero`) — the constant-zero request meets
`XCeilRiderStrict` at every `ε`.  `log 0 = 0` and the gate's own width window carries the
`ε²·H₊` margin; `log ω ≥ 0` closes it.  (The witness pattern of `RegisterCompose.lean:247-251`,
named here so the terminal can cite it.) -/
theorem xceilRiderStrict_zero (ε : ℚ) : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := by
  intro Hhi ω hgate
  obtain ⟨-, -, hωw⟩ := hgate
  simp only [Nat.cast_zero, Real.log_zero]
  linarith [Real.log_natCast_nonneg ω]

/-! ## §2 — ⟦THE TERMINAL AT THE EXHIBITED CALLER⟧ `…_ksarm` read at `g ≡ 0` -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 3200000 in
-- Same cause as `…_ksarm`: the `∃`-prefix re-elaborates in full when the parent's inner `∀ g`
-- is instantiated at the exhibited caller and the degenerate `g`-conjunct is discarded.
/-- **⟦DREAM-SPACE, night 08/14 — branch artifact; consumes nothing until waking review; the
V7-D question in the T2-A brief §5(iv) remains the Captain's⟧**

**⟦THE `g ≡ 0` INSTANCE⟧** (`logChowla2_ineffective_v7_ksarm_g0`) —
`V7Ks.logChowla2_ineffective_v7_ksarm` with the inner `∀ g, XCeilRiderStrict ε g → …` taken at
`g := fun _ _ => 0`, the rider discharged by `xceilRiderStrict_zero`.

⟦THE SURVIVING LIST⟧ outer hypotheses: NOTHING.  Inner, exactly **one** item:

* the `K_vt` cushion
  `32·Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊ + 32·(2·log (flatDoorM A) + log 4 + 50) ≤ log R.Hhi / 4`.

⟦WHAT MOVED⟧ the caller-side rider is not asked because the caller is EXHIBITED.  The `∃`-prefix
is the parent's, unchanged and in order, including the delivered `Real.exp (-100) ≤ cs`, `3 ≤ T₀`
and `0 < Ks`.

⟦WHAT IT COSTS, NAMED⟧ the `g`-conjunct degenerates: `(fun _ _ => 0) R.Hhi R.ω ≤ R.x` is
`0 ≤ R.x`, true of every `ChowlaRegime` (`R.x : ℕ`), so it is DROPPED from the conclusion rather
than carried.  This instance therefore carries none of the parent's caller-facing content; it is
a SPECIALIZATION, strictly weaker than `…_ksarm`, and the parent remains the statement of record
for a caller with its own outer-scale request.

⟦THE RELATION TO `V7E.logChowla2_ineffective_v7_g0`⟧ `main`'s `_g0` — landed at `82fedba`, after
this file was drafted — is the same instance taken at the `v7` mint rather than at the `ksarm`
rethread.  Its statement is this one with the single line `Real.exp (-100) ≤ Ks →` reinserted
ahead of the `∃ R`; equivalently, this statement is `_g0`'s minus that arrow.  So `_g0` is
DERIVABLE from this object with the same witnesses — introduce the `Ks` hypothesis vacuously
(`fun _ => ·`).  The converse direction is not available here: it would need the floor
`Real.exp (-100) ≤ Ks`, which V7-A traced to an explicit numerical lower bound on Siegel's
ineffective constant at `ε = 1/16`, supplied by neither the corpus nor the literature.  The
derivation is STATED here, not landed — no declaration in this file discharges `_g0`.

⟦STILL INEFFECTIVE⟧ the name is unchanged on purpose: the `K_vt` cushion is untouched, and the
parent's relocation is inherited — `…_ksarm` moved the `Ks` rider's ineffective load into the
DESIGN CONSTANT `A` through the seventh `max` arm `16·log(1/Ks)/3`, so this object's
ineffectivity sits in `K_vt` AND in `A`, which indexes the cushion through `KlevF A` and
`flatDoorM A`.

⟦THE SCOPE, STATED⟧ what the statement does and does not say, in its own bytes:

* the tolerance `ε` is OPAQUE and bounded only from BELOW — all that is exported is
  `1 / 500 ≤ ε` (with the regime's own `ε ≤ 1/2`).  The theorem is at one produced `ε`, not
  at every `ε`, and not at any named value;
* the window is `(x/ω, x]` weighted by `1/n` against `ε · log ω` (`logChowla2Fails`,
  `ChowlaFailure.lean:59-63`) — a windowed partial sum, not the full logarithmic average over
  `n ≤ x` against `log x`;
* the shift is `n + 1` (the `2` counts the factors `λ(n)·λ(n+1)`, not the shift);
* `ineffective`: the design constant `A` is produced by `Classical.choice` through the chain,
  and after the `ksarm` rethread `A` also carries Siegel's ineffective constant through its
  seventh `max` arm, so no numerical scale is extractable;
* nothing here bears on twin primes — the transport wall is untouched at this rung.

`logChowla2_ineffective_v7_ksarm`, `logChowla2_ineffective_v7`, `…_v6`, `…_v6_csarm` and
`…_v6_T0arm` are byte-untouched and remain citable. -/
theorem logChowla2_ineffective_v7_ksarm_g0 (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
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
  -- ⟦RIDER 1, DISCHARGED AT THE EXHIBITED CALLER⟧ §1; the `g`-conjunct is dropped, not carried
  obtain ⟨R, hReps, hHlo, -, hRtow, hdes, hwin, hfire⟩ :=
    hmain (fun _ _ : ℕ => 0) (xceilRiderStrict_zero ε)
  exact ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
    a15, a16, a17, a18, a19, a20, a21, a22,
    R, hReps, hHlo, hRtow, hdes, hwin, hfire⟩

end Salt.MR

end
