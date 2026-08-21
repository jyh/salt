# W-F3 WAVE B v4 — THE CONCENTRATION CONE AT SHIFT h

**Pen:** math, 2026-08-20 22:0x. **v1, v2 and v3 all failed their gates.** v3 died on ALL THREE of
its own corrections. Every kill is applied below. ⛔ **FRESH GATE NOT YET RUN — nothing dispatches.**
Wave A landed `2095863e`.

## §0 — WHAT THE v3 GATE KILLED, AND WHAT REPLACES IT

**K1 — `ε²·h ≤ 1` IS WRONG AT EQUALITY. THE CONSTRAINT IS STRICT: `ε²·h < 1`.**
v3 asserted `≤ 1` and claimed the entire window survives there. **A dead prime sits exactly at
equality:** `ε² = 1/4, H = 1996, h = 4` ⇒ `ε²h = 1`, and `499·4 = 1996 = H`, so the prime `499` maps
to `p·h = H` — outside the strict window. ⇒ **Every object carries `hεh : (eps:ℝ)^2 * h < 1`,
STRICT, acquired at `h211_h`.**

**K2 — ✅ RESOLVED BY MEASUREMENT, AND MY OWN CLAIM WAS WRONG IN BOTH THE PARAMETER AND THE
DIRECTION.** I asserted all night that *"at `a = 1` the surviving MASS is 28% of the `h = 1` mass, a
3.6× loss, while the COUNT reads 100%"*. Computed from `PrimeWindow.lean:26` (`H = 2·10⁶`, `h = 4`,
window `(ε²H/2, ε²H]`, survivors additionally `p ≤ H/h`):
```
   a = ε²h     surviving mass     surviving count
     0.9          100.0%             100.0%
     1.0          100.0%             100.0%      ← NO LOSS. Nothing for a count to be blind to.
     1.25          68.4%              60.6%
     1.50          42.2%              34.0%
     1.65          28.3%              21.7%      ← the "28%" lives HERE, not at a = 1
     1.996          0.3%               0.2%
```
⇒ **TWO errors in one figure.** ① The 28% belongs to `a ≈ 1.65`; **at `a = 1` there is no mass loss
at all.** ② Where count and mass DO diverge, **the count runs LOWER than the mass, not higher** —
the survivors are the SMALL primes, which carry the most weight, so a count *understates* surviving
mass. *My claim had the inequality backwards.*

⇒ **CONSEQUENCES FOR THIS BLOCK, both directions:**
- **v3's original claim is RESTORED for `a < 1`:** the whole window survives, mass and all, so the
  floor does NOT get harder. **v4's earlier "the floor gets HARDER" is WITHDRAWN — it was built on
  the mislabelled figure.**
- **The count/mass lesson survives, INVERTED and weaker:** a cardinality is not a mass, and here it
  errs *pessimistically*. **`WindowCount`'s two declarations still need the M3 audit** — a count
  standing in for a mass is still a defect even when it errs safe.
- **`hmertTrunc` is NOT needed as a hypothesis at `a < 1`**, since the truncated window IS the
  window there. §1's demand for it is withdrawn at `a < 1` and retained only if any node is ever
  priced at `a ≥ 1`.

**K3 — B-0 IS DEAD CODE UNDER THE WAVE'S OWN HYPOTHESIS. DELETED.**
B-0 sharpened the box to `[0,0]` at `p·h ≥ H`. But every object from `h211_h` down now carries
`ε²h < 1`, under which **no window prime satisfies `p·h ≥ H` at all** — the branch B-0 sharpens is
unreachable inside the wave. *v3 promoted a removable artifact to a wall (v2's error), then
promoted its removal to a node.* ⇒ **B-0 DELETED. C2's axis-collapse observation survives as a
NOTE, not a task: B-2/B-3's byte-copies are cheap because the box is loose, and nothing in this
wave needs it sharp.**

**K4 — THE PRODUCER CHAIN IS VACUOUS, NOT FALSE. B-5 DELETED.**
v3 claimed `fBridge_of_singleCorr` (`Prop26.lean:160`) is **FALSE** at shift `h` because its
`∃ c > 0` floor consumes full-window `hmert` while the mass comes from survivors.
**Wrong direction:** falsity downstream is **vacuity upstream** — an `∃`-statement whose hypothesis
cannot be met at shift `h` is not refuted, it is **unreachable**. Nothing is proved false; the node
simply never fires. ⇒ **B-5 DELETED as a proving task.** *v2 exiled this chain, v3 called it false;
both were ways of not saying "it is vacuous and that is a design fact, not a lemma".*

## §1 — WHAT K2 ACTUALLY FORCES (rewritten after the measurement; the earlier §1 is WITHDRAWN)

⛔ **The earlier §1 demanded `hmertTrunc` as an explicit hypothesis at every node, on the strength
of a "3.6× gap". THAT GAP DOES NOT EXIST AT `a < 1` — measured, the ratio is 100%.** At `ε²h < 1`
the truncation `p ≤ H/h` does not bind at all: the window top `ε²H = aH/h` sits **below** `H/h`,
so the truncated window IS the window and the full-window Mertens floor applies unchanged.

⇒ **NO new constant. NO `cM'`. NO `hmertTrunc` rider.** Nodes carry `hεh : (eps:ℝ)^2 * h < 1`
(strict, K1) and nothing further. *The entry cost this block advertised twenty minutes ago was an
artifact of a mislabelled figure, and it is withdrawn in full.*

⚠️ **RETAINED, conditionally:** if any future node is ever priced at `a ≥ 1`, the truncation binds
and the table in K2 gives the loss directly (68% at 1.25, 42% at 1.5, 0.3% at 1.996). **That is a
different wave, and it would need `cM'` measured before it could be scoped.**

## §2 — WAVE SHAPE (FIVE nodes; B-0 deleted (K3), **B-5 RESTORED** under §12's R2)

- **B-1 — `badSet_h`** + its `h = 1` compat (`Nat.mul_one`, not `rfl`). ⚠️ Byte-identity at `h`
  needs **THREE synchronized sites**: `badSet_h`'s predicate, the concentration lemma's deviation
  set, and `outer_combine`'s own conclusion (`OuterCombine.lean:363-364`, which spells the offset
  independently). Wave A fixed the target spelling at `:150`.
- **B-2 + B-3 — the mean and concentration cone (8 objects).** Byte-copies of the `h = 1` scripts,
  built once already by the v2 refuter at `EXIT=0`. ONE executor, Class C. Each acquires `hεh`
  (strict) — **and nothing else; the `hmertTrunc` rider is withdrawn.**
- **B-4 — calibration + `outer_combine` (5 objects).** v3 priced this "five lines, ordinary once
  B-0 lands"; B-0 is deleted (K3), so **that pricing is withdrawn and B-4 is UNPRICED.** *It is not
  blocked on a missing constant — that was the artifact — it is simply unmeasured.*
- **B-5 — THE PRODUCER CHAIN. ✅ RESTORED 2026-08-21** (deleted by K4 at `ba1c3c07`; K4 refuted in
  §11/§12). `h211_of_logChowla2Fails` and `fBridge_of_singleCorr` (`Prop26.lean:160`) at shift `h`,
  **carrying `hεh : ε²h < 1` (strict) and NOTHING FURTHER** — ⛔ *the original B-5's
  "truncated-window Mertens floor in place of the full-window `hmert`" is NOT restored with it:
  §1's measurement showed the truncation `p ≤ H/h` never binds under `hεh`, so the full-window
  `hmert` (node D3) applies verbatim.*
  ⭐ **THE ONE CHANGE §12 FORCES:** the h-analogue's `hreduce` must carry the **ramp factor**
  `1 − ε²h/(2 ln 2)` where the `h = 1` statement carries `1/2`. *Every window prime survives
  (count 100%) but delivers only `1 − a/(2 ln 2)` of the full-window mass — 28% as `a → 1` — so the
  bare `1/2` is undischargeable above `a = ln 2`.* The safe closed form `(1−ε²h)/2` is a valid
  lower bound (§8) and may be substituted at the cost of going vacuous at `a = 1`.
  ⛔ **This is where `h211_h` becomes satisfiable, and under R2 it does.** It remains the wave's
  real question and is in scope.

## §3 — KILL-CHECKS

**M1 — the `a < 1` regime is now the WHOLE claim. Is `ε²h < 1` reachable at the ε the budget
forces?** `ε` is pinned below `cE/(32·log 4)` upstream; `h` is ours. **If the budget's ε already
forces `ε²h < 1` for the `h` this wave needs, K1 costs nothing; if not, the wave is constrained
before it starts.** *This is arithmetic nobody has run, and it replaces the withdrawn `cM'` check.*
**M2 — the count/mass trap, INVERTED and still live.** Measured, a survivor COUNT runs **lower**
than the surviving mass (60.6% vs 68.4% at `a = 1.25`), because survivors are the SMALL primes.
⇒ **A count standing in for a mass is a defect even when it errs safe.** `WindowCount`'s two
declarations are the obvious suspects. **Audit before dispatch.**
**M3 — B-4's pricing.** With B-0 gone, what does `outer_combine` at shift `h` actually cost?
**KILL: if B-4 needs the sharp box after all, K3 is wrong and B-0 returns.**
**M4 — census audit.** The v3 census (52 decls · 32 offset-bound · 10 ported · 14 unported) knew
infixed `_h`, three baked defs, `instance`, six files. **What class does it STILL miss?**

## §4 — GATE RESULT (self-gate, 2026-08-20 23:1x)

⚠️ **THIS IS A SELF-GATE, NOT AN INDEPENDENT REFUTER PASS.** Both lenses were run by the pen that
wrote the block. It is weaker evidence than a peer pass and is labelled as such.

**CITATION LENS — PASS, all four verified against the tree:**
```
  OuterCombine.lean:363-364  →  (windowVal H … j) * (windowVal H … (j + p))     NO `* h`
                                ⇒ it DOES spell the offset independently: the third
                                  synchronised site is real
  OuterCombine.lean:150      →  (windowVal H v j) * (windowVal H v (j + p * h))  HAS `* h`
                                ⇒ Wave A's fix is in place as claimed
  Prop26.lean:160            →  theorem fBridge_of_singleCorr                    ✅
  2095863e                   →  ancestor of HEAD                                 ✅
```
*First clean citation lens of this campaign — after six misses in the λ-BV block.*

**MATHEMATICS LENS — K1 VERIFIED AGAINST THE SOURCE, and it corrected K2's rule on the way.**
The survivor condition is NOT `p ≤ H/h`. `windowVal H x (j + p*h) = 0` unless `j + p*h < H`,
i.e. **STRICT**. ⛔ **CITATION CORRECTED 2026-08-21 (independent-gate fatal 1): the anchor is the
DEFINITION `windowVal` at `FBridge.lean:60`** — `if h : j < H then v ⟨j,h⟩ else 0`, per-index, no
case hypothesis. *The former anchor `CircleMethod.lean:1238` is a local `have` inside the branch
the file labels `-- degenerate: H = 1` at `:1227`, where the ramp collapses to the constant 0 and
the rule's whole content is invisible. Right rule, wrong line.* ⇒
- **K1 STANDS, with an exact witness:** at `ε² = 1/4, H = 1996, h = 4` the window is `(249.5, 499]`,
  its top element `499` is prime, and `499·4 = 1996 = H`, so `p·h < H` is **false** — the prime
  contributes ZERO at `ε²h = 1` exactly. `≤ 1` is wrong; `< 1` is required.
- **K2's TABLE RE-RUN under the strict rule: UNCHANGED to one decimal** (100.0/100.0 · 68.4/60.6 ·
  42.2/34.0 · 28.3/21.7 · 0.3/0.2). *Not because the rule does not matter, but because at
  `H = 2·10⁶` the boundary needs `p = 500000`, which is not prime.* **Checked, not assumed.**
- **K3 CONFIRMED by the same arithmetic:** at `ε²h < 1` the window top `ε²H = aH/h < H/h`, so every
  window prime has `p·h < H` and the `p·h ≥ H` branch B-0 sharpened is unreachable. Dead code.

**VERDICT: v4 SURVIVES ITS SELF-GATE.** Remaining risk is concentrated in M1 (is `ε²h < 1`
reachable at the ε the budget forces?) and M3 (B-4's unpriced cost) — **both arithmetic nobody has
run**, and neither is a citation or a matcher defect.

## §5 — M1 ANSWERED, AND IT COUPLES THIS WAVE TO THE MRT DOOR (2026-08-20 23:4x)

**M1 asked: is `ε²h < 1` reachable at the ε the budget forces?** ✅ **YES, for ANY `h`** — and the
answer is structural, not numerical.

**① `ε` HAS NO LOWER BOUND BUT POSITIVITY.** `Regime.lean:77-78` gives `0 < eps`, `eps ≤ 1/2`;
`SpineFinal.lean:413` pins `ε ≤ cE/(32·log 4)`. **Both are CEILINGS.** The only constraint pushing
`ε` up is `hcoprime : a ≤ eps²·Hlo/2` (`Regime.lean:91`) — and it is relieved by **inflating
`Hlo`**, which `chowlaRegime_exists_param` supplies for any threshold (MRT recon #2). ⇒ Choose
`ε < 1/√h` and take `Hlo` large enough; `ε²h < 1` holds for any `h`. **K1 costs nothing in
reachability.**

**② ⛔ BUT IT IS NOT FREE, AND THE PRICE IS PAID IN A DIFFERENT LANE.** Every form of the door
threshold in the spine is **LINEAR IN `ε`**:
```
  δ₀ = c₀·ε/4                       SpineFinal.lean:1113, :1311   (c₀ = cD3/(16·C))
  δ₀ = ε/(2K)                       SpineFinal.lean:416, :513
  δ₀ = (cD3/(16·C))·ε/(2K)          SpineFinal.lean:739
```
⇒ **Shrinking `ε` shrinks `δ₀` proportionally, and a SMALLER `δ₀` is a STRONGER MRT door.**
With `ε < 1/√h`:
```
  δ₀  <  c₀ / (4·√h)        ⇒  THE DOOR'S REQUIRED STRENGTH GROWS LIKE √h IN THE SHIFT.
```

⭐⭐ **THE COUPLING, STATED PLAINLY BECAUSE NEITHER BLOCK STATES IT:** **W-F3 wants `ε` SMALL (to
admit a larger shift `h`); the MRT door wants `ε` LARGE (to admit a weaker `δ₀`). They pull the
same regime parameter in opposite directions.** The W-F3 block and the MRT-door recon were written
as separate lanes and share one `ε`.
⚠️ **NOT claimed:** that this kills either lane, or that any particular `h` is out of reach — the
door is a *proven* theorem (recon #3), so a `√h`-stronger instance is a formalisation cost, not a
new conjecture. **What IS claimed: any future choice of `h` in this wave is simultaneously a choice
about how strong an MRT instance the program must eventually formalise, and that trade has been
invisible because the two lanes were priced apart.**

## §6 — M2 AND M3 ANSWERED (2026-08-21 00:0x). THREE OF FOUR KILL-CHECKS ARE DOWN.

**M3 — DOES B-4 NEED THE SHARP BOX K3 DELETED? NO. K3 STANDS.** All five B-4 objects measured,
with a control that discriminates:
```
  badSet_transport                 Transport.lean:69      — NO box lemma
  badSet_transport_at_calibration  Transport.lean:128     — NO box lemma
  outer_badMass_eq                 OuterCombine.lean:193  — NO box lemma
  outer_badMass_le                 OuterCombine.lean:242  — NO box lemma
  outer_combine                    OuterCombine.lean:342  — NO box lemma
  CONTROL fBridge_concentration        FBridge.lean:276   fBridge_varTerm, fBridge_var_le
  CONTROL fBridge_concentration_sharp  FBridge.lean:412   + fBridge_var_le_sharp
```
The box lemmas are consumed by the **B-2/B-3** concentration objects, not by B-4 — which is exactly
v3's axis-collapse note read correctly: *the looseness is what makes the byte-copies cheap, and
nothing downstream of them needs it sharp.* **B-0 stays deleted.**

**M2 — IS A COUNT STANDING IN FOR A MASS IN `WindowCount`? NO — THE TREE CARRIES BOTH.**
`primeWindow_card_le_of_regime` (`:47`) is an honest **cardinality** upper bound
(`card ≤ 2·log 4 · ε²H/log H`); `regime_nonvacuous` (`:122`) is an honest nonemptiness. And the
**mass** object exists separately: `WindowMertensLower.lean`, whose own docstring states its
hypotheses *"mirror `primeWindow_card_le_of_regime`, plus `(eps : ℝ)² ≤ 1`"*.
⇒ **The count/mass distinction is already made in the tree, by construction.** 24 consumers of the
card bound checked; none uses it where a mass is required.
⭐ **AND THIS CONFIRMS §1's WITHDRAWAL FROM THE OTHER SIDE:** the full-window Mertens floor is
LANDED and applies unchanged at `ε²h < 1`, which is precisely why no `hmertTrunc` rider and no
`cM'` are needed.

**REMAINING: M4 alone** — audit the census for a class it still misses. *Every other kill-check is
answered, and all three answers went the block's way.*

## §7 — ⛔⛔ COLLISION: THE INDEPENDENT GATE IS RIGHT AND §§1,4,6 ARE WRONG (2026-08-21 00:1x)

**I had NOT read the 23:30 independent verdict when I wrote §4–§6.** It found the withdrawal was
the error. **It is correct. I have now computed it myself and I confirm it against my own work.**

**THE DEFECT: THE SURVIVOR RULE IS PER-INDEX, AND I COLLAPSED IT TO A BINARY.**
`windowVal H x (j + p*h) = 0` unless `j + p*h < H` — I read this correctly at
`CircleMethod.lean:1238`, wrote *"at j=0 that's `p*h < H`"*, and then computed as if a prime were
IN or OUT. **It is neither.** A prime contributes over the `j ∈ range H` with `j + p·h < H`, so its
effective weight is `(H − p·h)/H = 1 − p·h/H` — a RAMP, not a gate.
```
   a      weighted mass   my binary model   count      count/mass
   0.5      64.0%            100.0%         100.0%      1.56x
   1.0      28.1%            100.0%         100.0%      3.56x     ← the ORIGINAL 28%, vindicated
   1.25     13.9%             68.4%          60.6%      4.35x
   1.65      2.6%             28.3%          21.7%      8.48x
   closed form:  mass ratio = 1 − a/(2·ln 2);  at a=1 → 27.9%, ratio 3.59x
```
⇒ **K2 AS ORIGINALLY STATED IS CORRECT: at `a = 1` the count reads 100% and the mass reads 28%.
THE COUNT OVERSTATES THE MASS.** My §4/§6 reversal ("the count understates") is **WITHDRAWN**.

**REINSTATED, in full:** `hmertTrunc` as an explicit hypothesis; a truncated-window constant
distinct from `cM`; and the entry cost that §1 struck. **§1's withdrawal is void. §6's claim that
the tree "confirms the withdrawal" is void with it.**

**ON THE QUESTION PUT TO ME DIRECTLY — is "the tree separates count from mass" compatible?**
✅ **The separation is TRUE and ORTHOGONAL.** `primeWindow_card_le_of_regime` and
`WindowMertensLower` are genuinely different objects, and 24 consumers do respect that. **But the
existence of a mass lemma says NOTHING about which way the inequality runs, and I used it as if it
did** — I offered object-separation as evidence for a numerical direction. *That is a category
error, and it is the one the collision check named before I could defend it.*

⚠️ **ONE FIGURE I DO NOT YET RECONCILE, flagged rather than swallowed.** The verdict gives the entry
cost as `cM·(1 − ε²h)/2`, which is **0 at `a = 1`**; my measurement gives **28.1%** there, and the
closed form `1 − a/(2 ln 2)` gives 27.9%. **These disagree at the point that matters most.** Either
the constants are differently normalised or one of the two is wrong. *Taking a correction whole
because it corrected me is the same failure as resisting it.*

**M3 SURVIVES UNCHANGED:** which box lemmas appear in which proofs is independent of the survivor
rule — measured with a control, and no B-4 object uses one. **M2's measurement survives; only the
inference I drew from it is withdrawn.**

## §8 — THE TWO CONSTANTS RECONCILED: NOT A CONTRADICTION, A LOOSENESS (2026-08-21 00:1x)

§7 flagged that the independent verdict's entry cost `cM·(1 − ε²h)/2` reads **0 at `a = 1`** where
I measure **28.1%**. Resolved: **they do not contradict — the verdict's figure is a valid LOWER
BOUND on the true ratio, everywhere on `[0,1]`.**
```
   a      verdict (1−a)/2     true 1 − a/(2·ln 2)    verdict ≤ true
   0.00      0.5000                1.0000                 YES
   0.50      0.2500                0.6393                 YES
   0.90      0.0500                0.3508                 YES
   1.00      0.0000                0.2787                 YES
```
**Normalisation checked against the artifact, not assumed:** `windowVal` is the junk-zero extension
(`FBridge.lean:60`), so the product vanishes for `j + p·h ≥ H` and a prime contributes over
`max(0, H − p·h)` of the `H` indices; the ambient scale in `OuterCombine` is `H/log H`. Per prime
the contribution is `H·(1/p)·(1 − p·h/H)`, and `∑` over the dyadic window gives `H·(ln 2 − a/2)`
against `H·ln 2` at `a = 0`. ⇒ ratio `1 − a/(2·ln 2)`. **That is where my closed form comes from.**

⛔ **BUT THE LOOSENESS IS NOT HARMLESS, AND THIS IS THE POINT WORTH KEEPING.** `(1 − a)/2`
**degenerates to ZERO exactly at `a = 1`** — the boundary this wave lives against — while the true
ratio there is **27.9%**. A floor that vanishes at the operating point does not merely lose
sharpness: **it reports the wave as impossible where it is in fact 28% funded.** ⇒ *Use the
verdict's bound for safety anywhere below the boundary; do NOT use it to price `a → 1`.*

⭐ **AND THE METHOD NOTE:** in §7 I flagged this as "either normalisation differs or one of us is
wrong" and refused to swallow the correction whole **because it had just corrected me**. That was
right, and it paid: the answer is a THIRD thing neither framing offered — both figures are correct
and they measure different objects, one a bound and one a value.

## §9 — M4 ANSWERED: THE MISSED CLASS IS PROOF-ONLY SENSITIVITY, AND IT IS BIGGER THAN THE VISIBLE
## SET. THE CENSUS'S OWN HEADLINE NUMBER DOES NOT REPRODUCE. (2026-08-21 00:4x)

**① THE DECLARATION COUNT REPRODUCES EXACTLY.** Re-censused the six cone files with a matcher that
knows `theorem|lemma|def|abbrev|instance|structure|class` and the `noncomputable`/`private`/
`@[...]` prefixes: **52 total**, per-file **FBridge 27 · OuterCombine 13 · Transport 4 ·
Decoupled 2 · WindowCount 2 · MarkovExtract 4** — v3's figures to the file. *(FBridge's 27 includes
the `instance` v2 missed.)*

**② ⛔ THE CLASS THE CENSUS STILL MISSES: PROOF-ONLY OFFSET SENSITIVITY — and there is MORE of it
than of the visible kind.**
```
   STATEMENT offset-bound (what a statement census sees) : 13
   PROOF-ONLY offset-bound — INVISIBLE to that census    : 15
   neither                                               : 24
```
The fifteen: `neZero_primeWindow` · `abs_liouvilleWindow_le_one` · `fBridgeG` · `fBridgeG_abs_le` ·
`fBridgeG_mem_Icc` · `residueProj_fiber_card` · `fBridge_concentration_sharp` · `fBridgeG_h` ·
`fBridgeF_h` · `fBridgeF_h_one` · `fBridgeG_h_abs_le` · `fBridgeF_abs_le_boxSum` ·
`fBridgeF_h_abs_le_boxSum` · `badSet` · `badSet_transport`.
⇒ **A port that triages on statements alone would call these free and then break inside them.**
*v3 listed "proof-only sensitivity" as a CANDIDATE for what M4 might find; it is not a candidate,
it is the answer, and it is the majority of the bound set.*

**③ ⛔⛔ AND THE HEADLINE NUMBER DOES NOT REPRODUCE.** v3 says **32 offset-bound**. I measure **13**
statement-bound and **28** statement-or-proof-bound. **Neither is 32.** Since v3 never wrote down
what "offset-bound" means operationally, the gap cannot be adjudicated from the artifact.
⇒ **The 52 is trustworthy and the 32 is NOT — it is a number whose definition was never stated,
and two honest matchers disagree with it in both directions.** *When two counts of one population
differ, the gap is a finding: here the finding is a missing definition, not a wrong count.*
**Any wave shaped by "32 of 52" is shaped by an unreproducible figure.**

## §10 — ⛔⛔ TWO INDEPENDENT-GATE FATALS ARE STILL OPEN. THE BLOCK IS **NOT** COMPLETE.
## STANDING WORDING: "v4's OWN gate complete; independent fatals 1 and 3 OPEN." (2026-08-21 01:1x)

I wrote "v4 complete" on the bus. **That was wrong.** Of the independent gate's THREE fatals,
exactly **ONE** is resolved (the withdrawal — voided in §7, closed by §8's reconciliation).

**FATAL 1 — MY HEADLINE ANCHOR IS A LOCAL `have` IN A DEGENERATE BRANCH. CONFIRMED.**
§7 cited `CircleMethod.lean:1238` for the per-index rule. Measured, that line sits inside:
```
  · -- degenerate: H = 1, where `0 < h` is what makes the correlation vanish
    have hH1 : H = 1 := by have := NeZero.pos H; omega
    have hlog0 : Real.log (H : ℝ) = 0 := by rw [hH1]; simp
    ...  have hge : ¬ (j + (p : ℕ) * h < H) := by omega          ← line 1238
```
**The file labels the branch "degenerate" in its own comment.** At `H = 1`, `omega` discharges
`¬(j + p·h < 1)` from `j ≥ 0, p·h ≥ 1` — *it says nothing whatever about the general rule.*
⇒ **The correct anchor is `FBridge.lean:60`**, `windowVal H v j = if j < H then v ⟨j,h⟩ else 0`,
the junk-zero extension — which is what §8's derivation actually used. **§8's mathematics is
unaffected; §7's citation is void and §1 needs re-deriving from `FBridge.lean:60`.**
*I verified the RULE and then cited the wrong LINE for it — a citation defect wearing a
mathematics result's clothes.*

**FATAL 3 — K4 AND K1 CONTRADICT EACH OTHER. CONFIRMED, AND WORSE THAN A GAP.**
K1: *"every object carries `hεh : ε²·h < 1`, acquired at `h211_h`."* Measured:
```
   h211_h                            → ZERO hits anywhere in Salt/
   ε² * h < 1  (any spelling)        → ZERO hits in the Chowla cone
   h211_of_logChowla2Fails           → EXISTS, ChowlaFailure.lean:120 — but it is the h = 1 producer
```
**`h211_h` does not exist**, and **K4 deleted B-5, the only node that would have built it.** No node
in §2 produces it. ⇒ **Either B-4 ships a binder nothing can discharge — the dangling-interface
class, which no build reports — or K4 is wrong and B-5 must be restored. THE BLOCK CANNOT HAVE
BOTH, and it currently claims both.**

**⇒ STATUS, in the wording I will use from here: v4's OWN gate is complete; INDEPENDENT FATALS 1
AND 3 ARE OPEN.** The block is not dispatchable. *Its own gate passing is exactly the agreeing
result the streak law says to distrust — and an independent lens found three fatals in a block that
had just cleared both of my own lenses.*

## §11 — FATAL 3 RESOLVED, IN EXACTLY ONE DIRECTION: **K4 IS WRONG. B-5 IS RESTORED.**
## ⛔⛔ **ITS CENTRAL ARGUMENT IS WRONG — SEE §12. THE VERDICT SURVIVES, THE REASON DOES NOT.**
*(2026-08-21 09:1x. The direction is FORCED by measurement, not chosen.)*

**K4's stated reason is that `fBridge_of_singleCorr` "consumes full-window `hmert` while the mass
comes from survivors" — a full-window-vs-survivor MISMATCH. Measured, that mismatch is EMPTY under
the block's own retained hypothesis.**
```
  primeWindow eps H  =  { p prime : ε²H/2 < p ≤ ⌊ε²H⌋ }        PrimeWindow.lean:26
  p survives shift h ⟺ p·h < H  ⟺  p < H/h                     (windowVal junk-zero, FBridge.lean:60)
  window top ⌊ε²H⌋ ≤ ε²H,  so  EVERY window prime survives ⟺ ε²H < H/h ⟺ ε²·h < 1
```
⭐⭐ **THE CONDITION "EVERY WINDOW PRIME SURVIVES" IS *LITERALLY* `hεh : ε²·h < 1` — NOT
APPROXIMATELY, IDENTICALLY.** So under the binder K1 makes mandatory, the full window and the
survivor set **COINCIDE**, and K4's vacuity argument has nothing left to stand on. *This is also
exactly why K1 had to be STRICT: at `ε²h = 1` a prime may hit `p·h = H` and the survivor set
empties — the corner §K1 already flagged as "outside the strict window".*

⇒ **K4's premise is not merely unproven; it is REFUTED BY THE SAME INEQUALITY K1 REQUIRES.** The
block did not carry two independent claims that happened to clash — **it carried a hypothesis whose
content is the negation of one of its own deletions.**

**THE MECHANISM, and it is the general lesson:** K4 entered at `ba1c3c07` ("B-0 and B-5 deleted");
§1 was rewritten at `0d5e1f13` ("the cM prime entry cost was an artifact of the mislabelled figure
and is withdrawn"). **`ba1c3c07` is an ancestor of `0d5e1f13` — K4 PREDATES the measurement that
destroys it, and was never re-run against it.** K4 was formed while §1 still believed the truncation
`p ≤ H/h` bound and cost 3.6×; when that figure was withdrawn, the deletion it justified stayed.
⛔ **A WITHDRAWAL MUST SWEEP ITS OWN DOWNSTREAM. Withdrawing a FIGURE is not local either — every
deletion that figure justified has to be re-run, and nothing in the document points from the figure
to the deletions it bought.** *This is the "a gate that checks each claim never checks the SET" law
in its sharpest form: K4 alone passed, K1 alone passed, and one line of arithmetic shows the set is
inconsistent.*

**CONSEQUENCE, the single direction:** B-5 is **RESTORED** as a proving task — it is the node that
builds `h211_h`, the h-generalized producer of `hεh` that K1 says every object acquires and that
currently has **zero hits in the tree** (`h211_of_logChowla2Fails`, `ChowlaFailure.lean:120`, is the
`h = 1` producer only). With B-5 restored, B-4 no longer ships an undischargeable binder.
⛔ **The alternative direction — accept K4 and declare B-4 broken — is CLOSED, not deprioritised:
it would require the full window to differ from the survivor set, which `hεh` forbids.**

⛔⛔ **STATUS WORDING IS UNCHANGED AND STILL RULED: "v4's OWN gate complete; independent fatals 1
and 3 OPEN."** *Fatal 3's DIRECTION is now determined and fatal 1 has its derivation
(`FBridge.lean:60`, per-index), but neither FIX is landed — fatal 1 needs the citation swap, fatal 3
needs B-5 written back into §2. **The block remains NOT DISPATCHABLE, and declaring otherwise is a
ruling, not mine.***


## §12 — ⛔⛔ §11's ARGUMENT IS WRONG: I USED **COUNT** WHERE K4's PREMISE IS **MASS**.
## THE VERDICT STANDS, THE REASON IS REPLACED, AND THE FIX NOW HAS A PRICE. (2026-08-21 09:2x)

**§11 claimed the full window and the survivor set "COINCIDE" under `hεh`, hence K4's premise is
empty. THE SETS DO COINCIDE. THE MASS DOES NOT, AND K4's PREMISE IS ABOUT MASS.** Computed this
session (sieve to 6·10⁵, `H = 2·10⁶`, `h = 4`; control `π(10) = 4`, `π(100) = 25`):
```
   a=ε²h    MASS frac    COUNT frac      1 − a/(2 ln 2)
   0.250      82.02%      100.00%           81.97%
   0.500      64.04%      100.00%           63.93%
   0.693      50.15%      100.00%           50.00%
   1.000      28.06%      100.00%           27.87%
```
⇒ **The ramp weight `(H − p·h)/H` makes the 1/p-weighted mass `1 − a/(2 ln 2)`, NOT 1.** Every
prime survives (count 100%) and still delivers only 28% of the full-window mass as `a → 1`. **This
is the block's own standing fact — "a = 1.0 → mass 28.1% / count 100.0%, the COUNT OVERSTATES
3.56×" — and I inverted it inside the section resolving the fatal, one beat after quoting it.**

**WHAT §11 GOT RIGHT AND KEEPS:**
- ✅ **The chronology and its lesson.** `ba1c3c07` (K4) is an ancestor of `0d5e1f13` (§1 rewrite);
  K4 was never re-run against the measurement that undercut it. **A withdrawal must sweep its own
  downstream** — unaffected by this correction, and still the most transferable part.
- ✅ **The verdict: K4 is wrong and B-5 is restored** — but for a NARROWER reason, and at a price.

**THE CORRECTED ARGUMENT.** `hreduce` demands `(1/2)·SP·H·|X| ≤ |∫ fBridgeF|` — a **1/2 slack**
against the FULL-window sum `SP`. At shift `h` the deliverable mass is `(1 − a/(2 ln 2))·SP·H·|X|`.
So the h-analogue is dischargeable exactly when
```
        1 − a/(2 ln 2)  >  1/2     ⟺     a = ε²·h  <  ln 2 ≈ 0.6931
```
⇒ ⛔ **`hεh : ε²h < 1` IS TOO WEAK TO RESCUE B-5. K4 is wrong on `a < ln 2` and RIGHT on
`ln 2 ≤ a < 1`** — its vacuity is real in that upper band, which is why it read as true.
*My §11 sentence "K4's premise is refuted by the same inequality K1 requires" is FALSE: `hεh` does
not refute it. It is refuted only on the sub-interval `a < ln 2`.*

**TWO ADMISSIBLE REPAIRS, AND I TAKE THE SECOND:**
- **(R1) Strengthen the binder** to `ε²·h < ln 2`, keeping the `1/2`. Costs a strictly stronger
  hypothesis on every node.
- **(R2) Keep `hεh : ε²h < 1`, replace the `1/2`** by the measured ramp factor
  `1 − ε²h/(2 ln 2)` (the verdict's `(1−ε²h)/2` is a VALID but lossy lower bound on it — §8 — and
  goes vacuous exactly at `a = 1`). Costs one constant, in this lane only.
⭐ **R2, AND THE DECIDING ARGUMENT IS CROSS-LANE.** R1 forces `ε` down by `√(ln 2) ≈ 0.83`; by the
08/21 MRT match the door's `δ₀ = c₀ε/4` shrinks with `ε`, and a smaller `δ₀` raises the required
`Hlo` — Tao's own `H₋ = exp(ε^{−C₁})` (`1509.05422` fn. 5, p.12). **R1 pays for a W-F3 repair with
MRT-door strength, in the one parameter the two lanes pull opposite ways on** (`b51a71c3`). **R2
keeps the coupling untouched.**

⇒ **B-5 IS RESTORED UNDER R2**, carrying `hεh` (strict) and a ramp-factor constant in place of the
`1/2`. **No binder is strengthened; no `hmertTrunc` rider returns.**

🔑 **THE LESSON, and it is not the arithmetic:** §11 was written immediately after I had *correctly*
verified the count identity `{every window prime survives} = {ε²h < 1}`. That identity is true,
exact, and pleasing — **and it answers a question K4 was not asking.** A crisp true result about the
adjacent quantity is more dangerous than a vague one, because it terminates the search. *Ask what
quantity the OBJECTION is about before celebrating an identity in the neighbouring one.*

## §13 — THE RATIFIED §12 GATE FIRED. **R2 IS FATAL TWICE. TAKEN WITHOUT QUALIFICATION.**
*(independent refuter, 2026-08-21 ~11:1x; verdict `seat/briefs/2026-08-21-wf3-s12-refuter-VERDICT.md`.
Disposition: **B-5 HELD**, B-1…B-4 CLEAR and proceeding.)*

**R-2 CONFIRMED-FATAL, and the kill I could not have argued with:**
- ⛔ **THE LANDED `1/2` IS NOT A MASS RATIO. It is `1 − 2·(error budget)`** — `hmain` carries mass
  ratio 1 (`HMainAssembly.lean:119`), `hbudget ≤ (1/4)·SP·H·ε` (`:93`), `hseed ε/2 ≤ |X|` (`:86`),
  so `1/2 = 1 − 2·(1/4)`. ***R2 put a mass ratio into a SLACK slot.*** Replacing the `1/2` by the
  ramp factor leaves **zero slack**: the replacement constant IS the deliverable.
- ⛔ **AND THE ONE-LINE TEST THAT WOULD HAVE CAUGHT IT: R2 DOES NOT REDUCE TO THE `h = 1` OBJECT.**
  At `h = 1` the formula gives **≈0.9998, not 1/2** — off by the entire error budget. *§8's own
  table showed `0.5` vs `1.0` at `a = 0` and I called it "a looseness". It was a NORMALIZATION
  MISMATCH, and I inherited it into §12 one section later.*
- ⛔⛔ **THE RAMP WAS ALREADY A LINE ITEM IN THE LANDED BUDGET AND §12 NEVER OPENED THE FILE.**
  `HBudget.lean:606-624` — **`hT3`, the boundary slice, IS the ramp deficit at `h = 1`**, and it
  scales **exactly linearly in `h`**. The h-analogue needs **NO new constant in `hreduce`**: it
  needs `hT3` re-proved with the factor `h`. ⇒ ***§12's threshold is IN THE WRONG VARIABLE: the
  gate is `ε·h ≤ c/(32·log 4)` — LINEAR in `ε·h`, not `ε²·h`.***
- **§12's `a < ln 2` is the true asymptotic threshold but is unreachable by the tree's landed
  constants** — provable today only `a < 0.045` (pinned `c = 1/4`) to `a < 0.125` (sharp `c = ln 2`).

**R-1 — my ramp arithmetic is UNFOUNDED-as-attacked, i.e. RIGHT** (normalization verified at
`PrimeWindow.lean:26`; closed form re-derived independently; the numeric table reproduces exactly).
⚠️ Two caveats I own: the closed form is an **asymptotic** and the measured column **exceeds it at
every row, one-sided, ~1/log H** — *I printed the two columns as mutual confirmation without ever
asserting the sign* · and **§8:276 drops a `1/log(ε²H)` from both sides** (ratio survives, sentence
wrong).

**R-4 — THE CROSS-LANE ARGUMENT INVERTS, AND THIS IS THE FLEET-LEVEL ITEM.** Direction and the
`√(ln 2) ≈ 0.83` factor check out, **but I chose the expensive repair on the strength of the cheap
one's cost**: R1 is a numeral in an already-proven theorem (`Hlo` free); R2 is a new analytic
obligation plus a ~15-site discharge chain. ⛔⛔ **AND THE TREE'S BINDING CONSTRAINT FORCES
`ε ∝ 1/h`, NOT `1/√h`** (`hT3`'s gate) ⇒ `δ₀ = c₀ε/4` shrinks like `1/h` ⇒ ***THE DOOR HARDENS LIKE
`h`, NOT `√h`. The standing √h headline is understated BY A SQUARE.*** **U-5:** under the pinned
`c = 1/4`, `εh ≤ c/(32 log 4)` admits **`h ≤ 1`** — the two constraints are ~10⁴ apart in admissible
`h`, so my *"ε²h < 1 is reachable for any h"* was **true of the wrong constraint**.

### ✅ U-3 RESOLVED BY ME: **STALE.** *(the refuter left it stale-or-live; ordered resolved first)*
`HMainAssembly.lean:34-63`'s STOP-AND-FLAG describes the gate as `p ∣ n+j` against a product based
at `n+j+1`. **Measured:** `b77e4172^` has `((n + j : ℕ) : ZMod p) = 0`; the LIVE
`fBridgeF_liouville_apply` (`Prop26.lean:90`) has `((n + j + 1 : ℕ) : ZMod p) = 0` — **precisely the
class the flag says the collapse needs.** The fix is `d5916681` *("GATE-FIX lands — fBridgeG gate
corrected to (j+1)")*, of which the flag's commit `b77e4172` is an **ancestor**, and this file was
**never touched again**. ⇒ **The flag is a 35-day-old fossil; `hbudget` is not blocked by it and no
h-analogue inherits it.** *Annotated in place, text preserved; `saltbuild EXIT=0`, module **Built**.*
🔑 **THIRD INSTANCE TODAY OF ONE SHAPE:** the bank's cut-line header · K4 vs the §1 rewrite · this.
***A WITHDRAWAL MUST SWEEP ITS DOWNSTREAM — AND A FIX MUST SWEEP ITS UPSTREAM.*** Nothing points
from a repair back to the prose that motivated it, so the motivation outlives the defect silently.

### THE ROUTE I TAKE (the refuter's, and it is smaller than mine)
**Keep the `1/2`. Re-prove `hT3` with the factor `h`, under `ε·h ≤ c/(32·log 4)`.** No new constant,
no `hreduce` surgery, no cross-lane argument at all. ⛔ **But it makes K1's binder
`hεh : ε²h < 1` NECESSARY-NOT-SUFFICIENT for B-5**, so it touches **§0/K1 and §2's shape** — above a
§12 patch. **Design-tier, my pen, and it is next.** *§§11–12 stand as the record; R2 is withdrawn as
the repair and survives only as the reasoning that found the ramp.*
