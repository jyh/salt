# W-F3 WAVE B v3 — THE CONCENTRATION CONE AT SHIFT h

**Pen:** math, 2026-08-20 16:3x. **v1 and v2 both failed their gates**; every finding is applied
below and every figure re-measured. ⛔ **FRESH GATE NOT YET RUN — nothing dispatches.**
Wave A landed `2095863e`.

## §0 — THE THREE CORRECTIONS THAT DEFINE v3

**C1 — `ε²·h < 2` IS NECESSARY AND NOT SUFFICIENT. The constraint is `ε²·h ≤ 1`.**
v2's *"exactly when"* claimed a false iff: `primeWindow` is a set of **integers**, so the real
interval `(ε²H/2, H/h)` being non-empty does not mean it contains a **prime**. Machine-checked
counterexample, reproduced independently: **`ε = 0.999, H = 1000, h = 2` gives `ε²h = 1.996 < 2`,
73 window primes, and ZERO survivors** — every hypothesis of `outer_combine` holds *including
`hne`*, and `h211_h` is false. Two further failures at `ε²h = 1.96, 1.984`; **zero failures below
`ε²h < 1`.** ✅ **At `ε²·h ≤ 1` the ENTIRE window survives** (40/40, 23/23, 10/10, 73/73), so the
surviving mass equals the `h = 1` mass exactly and **the floor gets EASIER as `h` grows, since
`ε = √(α/h)` must shrink.** ⚠️ *The Mertens continuity argument behind "≤ 1 is enough" is
asymptotic heuristic, NOT machine-checked — the counterexample and the survivor counts are.*
⇒ **Every object from B-2 down carries `hεh : (eps:ℝ)^2 * h ≤ 1`, acquired at `h211_h`.**

**C2 — B-4 IS A FIVE-LINE FIX, NOT A CAMPAIGN. v2's §0.5 was FALSE.**
`hoeffding_residueProj` is generic in its box: `lo`/`hi` are **caller-supplied**, unified from the
`h_bdd` argument. The **sharp** box at `p·h ≥ H` is `[0,0]` — width zero, contributing **0** to the
denominator. **The `h`-blindness v2 called an intrinsic obstruction is an artifact of Wave A's
deliberately loose `fBridgeG_h_abs_le`.** *I promoted a removable artifact to a wall and then
ordered the wave around it.*
🔑 **AND THE AXIS COLLAPSE:** `fBridge_varTerm`, `fBridge_var_le`, `fBridge_var_le_sharp` are
offset-free **only because they hard-code the `h`-blind box.** ***The free/bound split and box
sharpness are ONE axis, not two: B-2/B-3's byte-copies are cheap precisely because they inherit
the looseness C2 removes.*** Sharpening the box and porting cheaply are the same decision.

**C3 — THE `h211` PRODUCER CHAIN IS IN SCOPE. v2 exiled its own object of risk.**
`h211_of_logChowla2Fails` (`ChowlaFailure.lean:120`) **produces** `h211`; that file's own docstring
says it is *"byte-identical to `outer_combine`'s `h211` hypothesis"* and `:173` feeds it in.
**v2 named `h211_h`'s satisfiability as the block's object of risk and then ruled its only producer
out of scope, making C1 unanswerable inside the block.**
⛔ **And upstream is worse than vacuous:** `fBridge_of_singleCorr` (`Prop26.lean:160`) is an
**∃-statement with a strictly positive floor**, consuming `hmert : cM/log H ≤ ∑_{p ∈ primeWindow} 1/p`
over the **full** window, while at shift `h` the mass comes only from **survivors**. At C1's
counterexample those are inconsistent ⇒ **at shift `h` that node is FALSE, not vacuous.** *The
vacuity v2 found downstream is the shadow of an outright falsity one file up.*

## §1 — THE CENSUS, over the TRUE cone

**Cone = `FBridge` · `Decoupled` · `Transport` · `WindowCount` · `MarkovExtract` · `OuterCombine`.**
v2 said four files; `OuterCombine` imports `WindowCount` and `MarkovExtract`, and `WindowCount`
imports `FBridge`, so both sit **strictly inside** the span. *Consequence benign — both are 0
offset-bound — but v2 asserted a scope it never measured.*

**52 declarations · 32 offset-bound · 10 ported by Wave A · 14 unported.**
⛔ **v2 counted 45 and missed the `instance` class entirely** — `neZero_primeWindow`
(`FBridge.lean:52`). *The trap class named in v2's own instrument note, absent from v2's matcher.*

| file | decls | offset-bound |
|---|---|---|
| `FBridge` | 27 | 16 |
| `OuterCombine` | 13 | 11 |
| `Transport` | 4 | 3 |
| `Decoupled` | 2 | 2 |
| `WindowCount` | 2 | **0** |
| `MarkovExtract` | 4 | **0** |

**The 14 unported:** `fBridgeG_sum_over_residues` · `fBridgeG_mean` · `fBridge_concentration_raw`
· `fBridge_concentration` · `fBridge_concentration_sharp` · `fBridge_concentration_decoupled_sharp`
· `fBridgeF_mean` · `fBridge_concentration_decoupled` · `badSet` · `badSet_transport`
· `badSet_transport_at_calibration` · `outer_badMass_eq` · `outer_badMass_le` · `outer_combine`.

## §2 — WAVE SHAPE

- **B-0 (new, from C2) — SHARPEN THE BOX.** `fBridgeG_h_eq_zero_of_le` and a sharp
  `fBridgeG_h_mem_Icc` giving `[0,0]` at `p·h ≥ H`. **~5 lines. Do this FIRST**: it is what makes
  B-4 ordinary, and it is what the three variance lemmas will then need re-porting against.
- **B-1 — `badSet_h`** + its `h = 1` compat (`Nat.mul_one`, not `rfl`). ⚠️ **Byte-identity at `h`
  needs THREE synchronized sites, not one**: `badSet_h`'s predicate, the concentration lemma's
  deviation set, **and `outer_combine`'s own conclusion** (`OuterCombine.lean:363-364`, which
  spells the offset independently). Wave A already fixed the target spelling at `:150`.
- **B-2 + B-3 — the mean and concentration cone (8 objects).** Byte-copies of the `h = 1` scripts;
  **already built once by the v2 refuter at `EXIT=0`.** ONE executor, Class C.
- **B-4 — calibration + outer_combine (5 objects).** Ordinary once B-0 lands.
- **B-5 (new, from C3) — THE PRODUCER CHAIN.** `h211_of_logChowla2Fails` and
  `fBridge_of_singleCorr` at shift `h`, carrying `hεh` and a **truncated-window** Mertens floor
  in place of the full-window `hmert`. ⛔ **This is where `h211_h` becomes satisfiable or does
  not. It is the wave's real question and it is no longer out of scope.**

## §3 — KILL-CHECKS

**M1** — is `ε²·h ≤ 1` sufficient **as stated in Lean**, or does the truncated-window Mertens floor
need to be a hypothesis rather than a consequence? *C1's argument for sufficiency is heuristic.*
**M2** — does sharpening the box (B-0) break the three variance lemmas' `h = 1` proofs? **If the
sharp box costs more than it saves, C2 is wrong and B-4 is a campaign after all.**
**M3** — at shift `h`, is `fBridge_of_singleCorr` repairable, or is its `∃ c > 0` genuinely FALSE
for all `h ≥ 2`? **KILL: if false, W-F3 dies regardless of any constraint.**
**M4** — audit this census: it now knows infixed `_h`, three baked defs, `instance`, and six files.
**What class does it STILL miss?** *Candidates: offset-binding through a def outside the three;
proof-only sensitivity; declarations in files that import the cone but are not consumers.*
