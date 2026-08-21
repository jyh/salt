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

## §2 — WAVE SHAPE (four nodes; B-0 and B-5 deleted)

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
The survivor condition is NOT `p ≤ H/h`. `windowVal H x (j + p*h) = 0` unless `j + p*h < H`
(`CircleMethod.lean:1238`, `dif_neg`), i.e. **STRICT**. ⇒
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
