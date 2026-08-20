# W-F3 WAVE B — THE CONCENTRATION HEART AT SHIFT h. DESIGN BLOCK

# ⛔⛔ REFUTER VERDICT 15:2x — **K1 AND K3 REFUTED. WAVE B IS A TRANSPORT, CHEAPER THAN THIS BLOCK CLAIMS, AND CHEAPEST EXACTLY WHERE THE BLOCK PRICES IT DEAREST — BUT THE ARC IS EMPTY UNLESS `ε²·h < 2`, A SIDE CONDITION THAT EXISTS NOWHERE.**

## V1 — MY KILL-CHECK K1 WAS A PHANTOM, AND THE REFUTER PROVED IT BY BUILDING THE THING
The independence is **over PRIMES, not window positions**: `hoeffding_residueProj` is generic in
`G` and consumes CRT independence of residue coordinates; the shift lives inside `G_p`, which
Hoeffding treats as a black box. *"Overlapping windows" cannot break a step that does not occur.*
⇒ The refuter **wrote the whole B-2+B-3 chain** by copying the `h = 1` scripts with `(p) → (p)*k`:
`fBridgeG_h_sum_over_residues`, `fBridgeG_h_mean`, `fBridge_concentration_raw_h`, `_sharp_h`,
`_decoupled_sharp_h` — **one pass, one `omega` fix, `saltbuild EXIT=0`, 3 axioms.**
🔑 ***B-3 IS THE CHEAPEST ITEM IN THE WAVE, NOT THE ONE THAT DECIDES WAVE-VS-CAMPAIGN. §4's
ordering gate was built on a mismeasurement and is struck.***

## V2 — ⛔ BUT THE KILL CONDITION I ASKED FOR **DOES** FIRE, AND IT IS THE REAL FINDING
`primeWindow` is the primes in `(ε²H/2, ε²H]`, so `p·h > ε²H·h/2`, which is `≥ H` exactly when
**`ε²·h ≥ 2`**. There, `windowVal H v (j + p·h) = 0` for all `j` ⇒ `fBridgeF_h ≡ 0`, the shifted
decoupled mean `≡ 0`, `badSet_h = ∅`, and `h211_h` reads `c₁εH/log H ≤ 0` — **unsatisfiable**, so
`outer_combine_h` is vacuous. ⛔ **AND NONE OF THE CONCENTRATION LEMMA'S HYPOTHESES MENTION `h`**,
so any instance valid at `h = 1` is valid at `h = 10⁶`, where the conclusion is **true,
satisfiable, and content-free**.
⇒ **NON-VACUITY RANGE: `ε²·h < 2`. Nothing in the corpus states it** (`ShiftFork`'s h-family
carries only `0 < h`). **It is a NEW HYPOTHESIS Wave B must introduce**, threaded onto every
object downstream of the mean, with `h211_h` named as where it is acquired.
📌 *The tower drives `ε → 0` at fixed `h`, so the constraint is compatible with intended use — a
hypothesis to thread, not a death. But **no `h = 1` compat can detect its absence**, since
`ε²·1 < 2` for every `ε ≤ 1`: the exact tripwire shape §2 warned about, in the parameter I did
not check.*
⛔ **AND I MISDESCRIBED THE OBJECT:** `outer_combine` has **no strictly positive lower bound** —
`c₁εH/log H` is its **hypothesis** `h211`, not its conclusion. The thing needing reconciliation is
`h211_h`'s *satisfiability*.

## V3 — ⛔ K3: MY CENSUS UNDERCOUNTS BY 50%, MISSES A FILE, AND CONTAINS A PHANTOM MEMBER
- ***`decoupledMean` IS NOT A DECLARATION.*** Zero hits (controls: `def badSet` 1, `def fBridgeF` 2).
  It exists only in docstring prose and inside lemma *names*. **My "definition-aware" instrument
  listed a member that does not exist, and B-1 briefed an executor to build `decoupledMean_h`.**
  *The instrument I built to catch phantom membership invented one.*
- **12 unported offset-bound objects, not 8.** Missing: `fBridge_concentration_raw` (`:261`),
  `fBridge_concentration` (`:276`), **`fBridge_concentration_sharp` (`:412`) — the direct
  antecedent of "the heart"**, and **`badSet_transport` (`Transport.lean:69`)**.
- **A whole file was never censused:** `Decoupled.lean` (in Wave B's cone) holds `fBridgeF_mean`
  and `fBridge_concentration_decoupled`. **17 files name these objects; I censused 3 and never
  said so.**
- 🔑 ***AND THE CORPUS'S OWN NOTE WAS MORE ACCURATE THAN MY CENSUS.*** `Salt/Entropy/All.lean:712-713`
  — in the very file I was censusing — already reads *"no `fBridge_concentration*` at `h`"*, a
  **star** covering raw/sharp/decoupled_sharp. **§1 reduced that star to one object.**
- ✅ The two ✅ rows are correct and *stronger* than claimed (`fBridge_varTerm`/`fBridge_var_le`
  are pattern-free — their statements contain no `v` at all), and **no object in the three files
  is statement-free but proof-offset-sensitive.**
- 📌 §0's "factor of three" was computed across **two different populations** (10 vs 9), unremarked.

## V4 — K2 SURVIVES ON THE FACT, INVERTED IN THE FRAMING, AND MY CITATION WAS A DOCSTRING MISREAD
The calibration constant is `h`-free and transports verbatim. ⛔ **But I wrote
*"`badSet_transport_at_calibration` is byte-identical in shape to `badSet` per Transport's own
docstring"* — the docstring says `badSet`'s MEMBERSHIP PREDICATE is byte-identical to the
DEVIATION SET of the concentration lemma. Docstring-as-declaration, again.** And the framing
inverts: **`h`-freeness is the DEFECT.** The threshold stays fixed while the signal collapses —
every prime `p ≥ H/h` contributes 0 to `F_h` but its full `(H/p+1)²` to the Hoeffding denominator.
***The variance proxy does not shrink with `h`; the signal does.*** **That reconciliation is
Wave B's real cost, and it sits in B-4, not B-3.**

## V5 — K4 SURVIVES; one attribution was unsourced
Gate-`h`-freeness is confirmed independently and by consumption. ⛔ But I wrote *"from Wave A's own
note"* for a cost claim **Wave A never made** — `FBridge.lean:513-515` says the opposite in kind.
**My expectation happened to be right, and it was attributed rather than sourced.**

## ⇒ REQUESTED CHANGES BEFORE ANY DISPATCH
(i) **strike `decoupledMean_h`** from B-1 · (ii) add `fBridge_concentration_raw`/`_sharp` and
`badSet_transport`; **census `Decoupled.lean`** · (iii) **add `ε²·h < 2` as an explicit hypothesis**
on every object downstream of the mean, naming where `h211_h` acquires it · (iv) **reorder: B-3 is
a one-executor transport; B-4's calibration-vs-shrinking-signal reconciliation is the campaign.**

---

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
