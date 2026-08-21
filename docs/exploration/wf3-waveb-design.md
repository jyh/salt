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

## §1 — THE CONSEQUENCE K2 FORCES ON THE WAVE'S SHAPE

The Mertens floor over the **truncated** window is **not derivable** from the full-window floor —
K2 measures the gap at 3.6×. ⇒ **It must be carried as an explicit HYPOTHESIS with a named
constant, at every node from B-1 down:**
```
  hmertTrunc : cM' / Real.log H ≤ ∑ p ∈ primeWindowTrunc eps H h, (1 : ℝ)/p
```
**`cM'` is NOT `cM`.** Any node that silently reuses the full-window constant is wrong by the
measured factor. ⚠️ **`cM'` IS NOT SUPPLIED BY THIS BLOCK** — its value is a measurement nobody has
made, and pricing it is the wave's entry cost, not its content.

## §2 — WAVE SHAPE (four nodes, B-0 and B-5 deleted)

- **B-1 — `badSet_h`** + its `h = 1` compat (`Nat.mul_one`, not `rfl`). ⚠️ Byte-identity at `h`
  needs **THREE synchronized sites**: `badSet_h`'s predicate, the concentration lemma's deviation
  set, and `outer_combine`'s own conclusion (`OuterCombine.lean:363-364`, which spells the offset
  independently). Wave A fixed the target spelling at `:150`.
- **B-2 + B-3 — the mean and concentration cone (8 objects).** Byte-copies of the `h = 1` scripts,
  built once already by the v2 refuter at `EXIT=0`. ONE executor, Class C. Each acquires `hεh`
  (strict) and `hmertTrunc`.
- **B-4 — calibration + `outer_combine` (5 objects).** ⚠️ **v3 called this "five lines, ordinary
  once B-0 lands". B-0 is deleted, so that pricing is withdrawn** — B-4 is re-priced as UNKNOWN
  until `cM'` exists.

## §3 — KILL-CHECKS

**M1 — `cM'`.** What IS the truncated-window Mertens constant? Until measured, every node below
B-1 is priced on an unknown. **KILL: if `cM'` cannot beat the concentration's requirement, the
wave dies at B-2 and nothing further matters.**
**M2 — is `hmertTrunc` even satisfiable at `ε²h < 1`?** K2 says the mass is 28% at `a = 1`; the
floor needs `cM'/log H`. **These have not been compared.** *This is the question v2 exiled, v3
mislabelled as falsity, and v4 states plainly: it is an arithmetic comparison nobody has run.*
**M3 — the count/mass trap, generalised.** Where ELSE in this cone does a cardinality stand in for
a mass? `WindowCount`'s two declarations are the obvious suspects. **Audit before dispatch.**
**M4 — census audit.** The v3 census (52 decls · 32 offset-bound · 10 ported · 14 unported) knew
infixed `_h`, three baked defs, `instance`, six files. **What class does it STILL miss?**
