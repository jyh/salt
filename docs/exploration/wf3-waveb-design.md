# W-F3 WAVE B — THE CONCENTRATION HEART AT SHIFT h. DESIGN BLOCK

**Pen:** math, 2026-08-20 15:0x. ⛔ **REFUTER PASS NOT RUN — not dispatchable.**
Wave A landed at `2095863e` (10 declarations, `[3 axioms]`, `Built`). Wave C is gated on this.

## §0 — HOW THIS BLOCK WAS BUILT, because the method is the correction

Three design blocks failed their gates today (λ-BV v1, W-F3 v1, and I contributed to v2/v3's
refutations). **Every failure was an assertion I could have measured and did not.** So this block
opens with the census, and every cost claim below is a measurement with its instrument named.

⛔ **AND THE CENSUS CAUGHT MY OWN FIRST INSTRUMENT.** Surface-syntax test — *does the statement
spell `+ (p`?* — returned **6 of 10 offset-free**. Definition-aware test — *does it spell the
offset **or name a definition that bakes it in*** (`fBridgeG`, `fBridgeF`, `badSet`,
`decoupledMean`) — returns **2 of 9**. ***The surface count was wrong by a factor of three, in the
direction that would have made this wave look cheap.*** A statement can be offset-bound through a
definition it names, and surface syntax cannot see it. *This is the same member-class blindness
that produced every other error today, caught prospectively for once.*

## §1 — THE CENSUS (definition-aware; the operative table)

| object | where | offset status |
|---|---|---|
| `fBridge_varTerm` | `FBridge.lean:198` | ✅ **genuinely offset-free** |
| `fBridge_var_le` | `FBridge.lean:218` | ✅ **genuinely offset-free** |
| `fBridgeG_sum_over_residues` | `FBridge.lean:176` | ⚠️ offset-bound (inline + via def) |
| `fBridgeG_mean` | `FBridge.lean:331` | ⚠️ offset-bound (inline + via def) |
| `fBridge_concentration_decoupled_sharp` | `FBridge.lean:460` | ⚠️ offset-bound — **the heart** |
| `badSet` | `Transport.lean:42` | ⚠️ offset baked into the membership predicate |
| `badSet_transport_at_calibration` | `Transport.lean:128` | ⚠️ offset-bound via def |
| `outer_badMass_eq` / `_le` | `OuterCombine.lean:193` / `:242` | ⚠️ offset-bound via def |
| `outer_combine` | `OuterCombine.lean:342` | ⚠️ offset-bound (its `h211` names `fBridgeF`) |

⇒ **Only `fBridge_varTerm` and `fBridge_var_le` transport for free. Everything else needs an
h-version, and `badSet`/`decoupledMean` are two more offset-baked DEFINITIONS** (Wave A did the
other two, `fBridgeG`/`fBridgeF`).

## §2 — WHAT WAVE A'S EXECUTOR HANDED FORWARD, and it changes the shape

Wave A refused my gate specification and was right: **the `1` in `fBridgeG`'s residue gate is the
window's 1-INDEXING OFFSET, not `h`** (`windowVal H (liouvilleWindow H n) j = λ(n+j+1)`; Tao's
(3.14) indicator carries no `h` — `h` enters only through `x_{2,j+ph}`). **So the gate is
`h`-FREE.** Consequence for this wave, from Wave A's own note: `fBridgeG_h_sum_over_residues` and
`fBridgeG_h_mean` should port **more** cleanly than expected — the residue collapse fires at
`r = -(j+1)` independent of `h`, and `residueProj_fiber_card` is `h`-blind.
⚠️ **The genuinely `h`-sensitive step is DOWNSTREAM of those, in (2.11) restated at shift `h`.**
⛔ *And the tripwire worth carrying: the wrong gate and the right gate COINCIDE AT `h = 1`, so no
`h = 1` compat lemma can separate them. Green, compat-clean, and wrong at `h ≥ 2`.*

## §3 — KILL-CHECKS

**K1 — IS THE CONCENTRATION LEMMA OFFSET-BLIND?** `fBridge_concentration_decoupled_sharp` is
Hoeffding-shaped. **KILL CONDITION: if its proof uses independence or a pairing argument that the
`p·h` offset breaks (e.g. overlapping windows when `p·h ≥ H`), this is not a transport and Wave B
is a new estimate.** *Wave A flagged the boundary case: at `j + p·h ≥ H` every term vanishes, and
for `p·h ≥ H` the correlation is identically 0 — which must be reconciled with `outer_combine`'s
strictly positive lower bound.*

**K2 — DOES `badSet` AT `h` STILL CALIBRATE?** `badSet_transport_at_calibration` is byte-identical
in shape to `badSet` per Transport's own docstring. **Verify that the calibration constant does not
move with `h`; if it does, `outer_badMass_le`'s bound moves and §4's wave shape is wrong.**

**K3 — MEASURE, DO NOT ASSERT, EVERY "IT SHOULD PORT" ABOVE.** Including §2's — that is Wave A's
executor's expectation, not a measurement. **Run the definition-aware test on any object before
pricing it, and state which test you ran.**

**K4 — SCOPE.** Nothing here touches the terminal (Wave C), `MRTUniformityXiH` (open, no producer),
or E7's band boundary (P2's).

## §4 — WAVE SHAPE (conditional on K1–K3)

**B-1** `badSet_h` + `decoupledMean_h` (the two remaining offset-baked definitions) + their
`h = 1` compats — mirror Wave A's technique (`Nat.mul_one`, not `rfl`). **Class C.**
**B-2** `fBridgeG_h_sum_over_residues`, `fBridgeG_h_mean` — expected cheap per §2, **measure first**.
**B-3** `fBridge_concentration_decoupled_sharp` at `h` — **the heart; gated on K1.**
**B-4** `badSet_h_transport_at_calibration`, `outer_badMass_h_eq/_le`, `outer_combine_h`.
⛔ **B-3 is the item that decides whether Wave B is a wave or a campaign. Do not brief B-4 until
B-3's cost is measured.**
