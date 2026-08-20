# W-F3 WAVE B v2 — THE CONCENTRATION CONE AT SHIFT h

**Pen:** math, 2026-08-20 15:4x. **v1 failed its gate**; all four requested changes are applied
below and the census was re-run from scratch. ⛔ **FRESH GATE NOT YET RUN — nothing dispatches.**
Wave A landed at `2095863e` (10 declarations, `[3 axioms]`, `Built`).

## §0 — WHAT THE v1 GATE ESTABLISHED (kept because the corrections ARE the design)

1. ⛔ **`decoupledMean` IS NOT A DECLARATION** (0 hits; controls `def badSet` 1, `def fBridgeF` 1).
   v1 listed it among the offset-baked *definitions* and briefed an executor to build
   `decoupledMean_h`. **The real baked definitions are exactly three: `fBridgeG`, `fBridgeF`,
   `badSet`** — Wave A ported the first two. *The object is an inline sum; Wave A already states
   it at `h` inside `decoupledMean_h_abs_le_boxSum`.*
2. ⭐ **B-3 IS CHEAP, MEASURED BY CONSTRUCTION.** The Hoeffding independence is over **PRIMES**
   (CRT residue coordinates via `iIndepFun_residueProj`), not window positions; the shift lives
   inside `G_p`, a black box to `hoeffding_residueProj`, which is generic in `G`. The v1 refuter
   **built the whole B-2+B-3 chain** from the `h = 1` scripts with `(p) → (p)*k`: one pass,
   `saltbuild EXIT=0`, 3 axioms. **v1's "B-3 decides wave-vs-campaign" is struck.**
3. ⛔⛔ **THE NON-VACUITY CONSTRAINT, and it is the block's real content.** `primeWindow` is the
   primes in `(ε²H/2, ε²H]`, so `p·h > ε²H·h/2 ≥ H` exactly when **`ε²·h ≥ 2`**. There
   `windowVal H v (j + p·h) = 0` for all `j` ⇒ `fBridgeF_h ≡ 0`, `badSet_h = ∅`, `h211_h`
   unsatisfiable, `outer_combine_h` vacuous. **And no hypothesis of the concentration lemma
   mentions `h`,** so an instance valid at `h = 1` is valid at `h = 10⁶` where the conclusion is
   true and content-free. ⇒ ***`ε²·h < 2` IS A NEW HYPOTHESIS THIS WAVE MUST INTRODUCE. No `h = 1`
   compat can detect its absence (`ε²·1 < 2` for every `ε ≤ 1`).***
4. 📌 **`outer_combine` has no positive lower bound to reconcile** — `c₁εH/log H` is its
   *hypothesis* `h211`. The object at risk is **`h211_h`'s satisfiability**. (v1 said otherwise.)
5. 📌 **The threshold's `h`-freeness is the DEFECT, not the safety.** Every prime `p ≥ H/h`
   contributes **0** to `F_h` and its **full** `(H/p+1)²` to the Hoeffding denominator:
   *the variance proxy does not shrink with `h`; the signal does.* **That is B-4's cost.**

## §1 — THE CENSUS, RE-RUN OVER THE WHOLE CONE (v1 looked at 3 files of 17 and did not say so)

**Cone = `FBridge` · `Decoupled` · `Transport` · `OuterCombine`** (the span from `fBridgeG` to
`outer_combine`). The other 13 files naming these objects are **downstream consumers** —
`Theorem23Shell`, `SpineFinal`, `HloExport*`, `S16Uniform`, … — and belong to **Wave C**, not here.
*Stated as a scope measurement, not an assumption.*

**45 cone declarations · 32 offset-bound · 13 free · 10 already ported by Wave A.**
⛔ **INSTRUMENT NOTE, third correction on this block:** the first recount said **20** unported.
Six of those were **already ported** — Wave A **infixes** `_h` after the head token
(`fBridgeG_abs_le` → `fBridgeG_h_abs_le`) and my check looked for a **suffix**. **True figure: 14.**
*(Control: the corrected rule finds exactly Wave A's 10 h-siblings.)*

| # | unported, offset-bound | site |
|---|---|---|
| 1 | `fBridgeG_sum_over_residues` | `FBridge.lean:176` |
| 2 | `fBridgeG_mean` | `:331` |
| 3 | `fBridge_concentration_raw` | `:261` |
| 4 | `fBridge_concentration` | `:276` |
| 5 | `fBridge_concentration_sharp` | `:412` |
| 6 | `fBridge_concentration_decoupled_sharp` | `:460` |
| 7 | `fBridgeF_mean` | `Decoupled.lean:38` |
| 8 | `fBridge_concentration_decoupled` | `Decoupled.lean:53` |
| 9 | `badSet` (definition) | `Transport.lean:42` |
| 10 | `badSet_transport` | `:69` |
| 11 | `badSet_transport_at_calibration` | `:128` |
| 12 | `outer_badMass_eq` | `OuterCombine.lean:193` |
| 13 | `outer_badMass_le` | `:242` |
| 14 | `outer_combine` | `:342` |

*Rows 3–5, 7, 8, 10 were all absent from v1's table. `Decoupled.lean` was never censused at all.*
📌 **`Salt/Entropy/All.lean:712-713` already carried the accurate list** — *"no `fBridge_concentration*`
at `h`"*, a **star** over raw/sharp/decoupled_sharp. v1 reduced that star to one object. **The
corpus's own note beat my census, in the file I was censusing.**

## §2 — WAVE SHAPE, REORDERED (v1 had it backwards)

- **B-1 — `badSet_h` + its `h = 1` compat.** The one remaining offset-baked *definition*.
  Compat by `Nat.mul_one`, **not `rfl`** (Wave A's measured technique). **Class C, small.**
- **B-2 + B-3 — rows 1–8, the mean and the concentration cone.** ***Byte-copies of the `h = 1`
  scripts; already built once by the refuter.*** **ONE executor, Class C.**
- **B-4 — rows 10–14, the calibration and the outer combine. THE CAMPAIGN.** Here the fixed
  threshold meets the shrinking signal (§0.5), and `h211_h` must assert the same
  `c₁·εH/log H` floor on a strictly smaller object. **Do not brief B-4 as one wave.**
- **⛔ EVERY object from B-2 onward carries `hεh : (eps:ℝ)^2 * h < 2` EXPLICITLY.** It is
  **acquired at `h211_h`**, which is where satisfiability is asserted, and threaded downward.
  *Absent it, every statement below is green, compat-clean and empty.*

## §3 — KILL-CHECKS FOR THE FRESH GATE

**L1** — is `ε²·h < 2` sufficient as well as necessary? §0.3 proves the failure at `ε²h ≥ 2`;
**nobody has shown the surviving prime range `(ε²H/2, H/h)` carries enough mass for `h211_h`.**
**KILL: if it does not, the arc dies inside the constraint too.**
**L2** — does `badSet_h`'s deviation set stay byte-identical to the h-concentration lemma's, as
`Transport.lean:39-41` asserts for `h = 1`? *(v1 misread that docstring; read the bytes.)*
**L3** — B-4's reconciliation: state the inequality `h211_h` needs and whether the shrinking
signal can satisfy it for any `h ≥ 2`. **This is the wave's real question.**
**L4** — audit THIS census as v1's was audited: which member class can the corrected matcher still
not see? *It now knows infixed `_h`, the three real baked defs, and the four cone files. It does
not know: objects offset-bound through a def I have not listed, or proof-only sensitivity.*
