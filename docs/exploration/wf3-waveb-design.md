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

**K2 — ⛔⛔ THE FATAL ONE. I MEASURED THE SURVIVOR *COUNT*, AND THE COUNT IS BLIND TO THE LOSS.**
v3's evidence for "`≤ 1` is safe" was survivor counts: 40/40, 23/23, 10/10, 73/73 — **100%
survival**. Re-measured as *mass*, which is what the Mertens floor actually consumes:
```
  at a = 1 :  surviving  ∑ 1/p   =   28%  of the h = 1 mass      ⇒  a 3.6× LOSS
              surviving  COUNT   =  100%
```
**Both numbers are correct and they describe opposite situations.** The window keeps its primes and
loses nearly three quarters of its mass, because `ε = √(α/h)` shrinks the window from the small-`p`
end where `1/p` is large. ⇒ **v3's headline claim — *"the floor gets EASIER as `h` grows"* — is
FALSE and inverted. The floor gets HARDER.**

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
