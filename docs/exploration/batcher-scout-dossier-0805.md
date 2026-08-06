BATCHER-SCOUT DOSSIER — Batcher-banyan formalization pricing
READ-ONLY scout, no repo writes. All probe artifacts in the session scratchpad (paths at the end).

HEADLINE: I did not just price S1 — I proved it. 111 lines, sorry-free, `[propext, Classical.choice, Quot.sound]`, 0.5s over a bare mathlib import. The representation question (item 5) turned out to be the whole ballgame, and it resolves cleanly against both "natural" choices.

════════════════════════════════════════
1. MATHLIB INVENTORY
════════════════════════════════════════

ABSENT — confirmed by grep -ril over the whole `Mathlib/` tree (zero files each):
  sorting networks · bitonic · Batcher · comparator networks · 0-1 principle ·
  banyan / omega network · butterfly · perfect shuffle / riffle
The single "comparator" hit is `Mathlib/Tactic/ITauto.lean:144,149` — an `Ord` instance for `AndKind`, unrelated.

So S3 has **zero** mathlib scaffolding. That is the budget-defining fact.

PRESENT AND LOAD-BEARING:
- `Mathlib/Data/Finset/Sort.lean:198` `Finset.orderEmbOfFin (s) (h : s.card = k) : Fin k ↪o α`, and `:190` `orderIsoOfFin`. This is *exactly* the "n distinct destinations presented sorted" datum, free. It is also the S3 escape hatch (see item 6).
- `Mathlib/Data/List/Sort.lean` — `insertionSort`/`mergeSort`, `Pairwise`, `SortedLT/LE/GT/GE`, `:403 sortedLT_iff_strictMono_get`, `:474 sortedLT_iff_getElem_lt_getElem_of_lt`.
- **Lean core `Init/Data/Nat/Bitwise/Lemmas.lean:700` `Nat.testBit_two_pow_mul_add`** — `testBit (2^i * a + b) j = if j < i then testBit b j else testBit a (j-i)`. This is the entire bit-level facade in one lemma. Also `:128 testBit_div_two_pow`, `:296 testBit_mod_two_pow`, `:738 testBit_mul_two_pow`, `:742 two_pow_add_eq_or_of_lt`, `:764/:768 testBit_shiftLeft/Right`.
- `Mathlib/Data/Nat/Bitwise.lean` — 41 `testBit` sites; `eq_of_testBit_eq`, `:192 lt_of_testBit`, `:243 and_two_pow`.
- BitVec (Lean core): ~11k lines — `Lemmas.lean` 6842, `Bitblast.lean` 2802. `getLsbD_*` for every operation, `:220 eq_of_getLsbD_eq_iff`.
- `Mathlib/Data/BitVec.lean:106` `BitVec.equivFin : BitVec m ≃+* Fin (2^m)`.
- `Batteries/Data/Fin/OfBits.lean` `Fin.ofBits : (Fin n → Bool) → Fin (2^n)`; `Batteries/Data/Nat/Lemmas.lean:169-212` `Nat.ofBits`, `:205 testBit_ofBits`, `:211 ofBits_testBit`.
- `Mathlib/Algebra/BigOperators/Fin.lean:580` `finFunctionFinEquiv : (Fin n → Fin m) ≃ Fin (m^n)`.
- For S3 specifically: `Monotone.map_min` / `Monotone.map_max` (verified present) — the algebraic core of the 0-1 principle. `List.nodup_iff_injective_getElem`, `List.Nodup.map_on`, `List.getElem_zipIdx`, `List.pairwise_iff_getElem` — all verified present, they carry S2's reflection bridge.

════════════════════════════════════════
2 & 5. REPRESENTATION — THE DESIGN RISK, RESOLVED
════════════════════════════════════════

**R1 — stage-indexed permutation family `Fin k → Equiv.Perm (Fin N)`. REJECT, circular.**
The banyan's routing is *data-dependent* (it reads destinations). To present a stage as a `Perm` you must first prove it is a bijection — but injectivity of the stage map is precisely the theorem. You'd be assuming the conclusion in the type. This is the trap that would burn a week.

**R2 — `BitVec k`, route by `getLsbD`. REJECT as carrier.**
Three strikes, one of them fatal:
  (a) The facts S1 actually needs are *order* facts ("same low bits + distinct ⇒ ≥ 2^m apart"; "same high bits ⇒ < 2^m apart"). BitVec's order theory is thin; you route through `toNat` and re-derive div/mod anyway.
  (b) `omega` does not reason about BitVec. S1's endgame is one `omega` call. You'd lose it.
  (c) FATAL: `bv_decide` — the only reason to pick BitVec — **emits an axiom**. Measured: `#print axioms` on a trivial `by bv_decide` goal returns `[propext, Classical.choice, Quot.sound, bvtest._native.bv_decide.ax_1_5]`. Disqualified under salt's iron rule 3 / any no-new-axioms public claim. Worth knowing before someone builds S2 on it.

**R3 — ℕ with div/mod, the "prefix-suffix" line. ✅ WINNER — proven, not argued.**

```lean
def line (m s d : ℕ) : ℕ := 2 ^ m * (d / 2 ^ m) + s % 2 ^ m
```
`m` = number of low bits **still unrouted**, counting *down* k → 0. `m = k` is the input line (`= s`), `m = 0` is the output (`= d`).

That descending index is the single highest-leverage decision in the whole design: it makes ℕ-subtraction vanish. The natural ascending stage index forces `2^(k-1-i)` into every statement and every `omega` call — truncated subtraction poisoning a hundred goals is the classic way this formalization bleeds time. With the descending index, **`k` does not appear in the main theorem at all**.

Two structural findings that changed the estimate:

▸ **S1 needs no induction over stages.** `line m s d` is a *closed form* for the state at every stage boundary, so conflict-freeness is proved once, uniformly in `m`, in a 12-line argument. The stage recursion is a separate 4-line lemma (`step_line : step m (line (m+1) s d) d = line m s d`) that connects the closed form to the operational per-stage hardware reading — it is the bridge to the physical description, not a proof obligation of the theorem. This deletes the predicted time sink (a stage-by-stage induction carrying an invariant).

▸ **The bit-level facade is free.** `Nat.testBit_two_pow_mul_add` gives, in 4 lines:
```lean
theorem testBit_line (m s d j : ℕ) :
    (line m s d).testBit j = if j < m then s.testBit j else d.testBit j
```
plus a 6-line `testBit_step` showing one stage flips exactly bit `m`. So the *public statement* reads as bit-routing ("high bits from the destination, low bits from the source") while the *proof* stays arithmetic. Best of both. Ship this on day 1 — it is what makes the repo legible to a networks person.

RECOMMENDATION: ℕ carrier, div/mod, descending `m`; `testBit` as facade; `Fin`/`BitVec` only in the outer statement wrapper if desired (`BitVec.equivFin` bridges for free). Do **not** use `Fin (2^k)` as the carrier — coercion tax with no compensating benefit.

════════════════════════════════════════
3. DECIDABILITY — ALL MEASURED, NOT ESTIMATED
════════════════════════════════════════

Baseline (`import Mathlib` alone): **3.0s**. All figures below are wall-clock totals.

| certificate | time | verdict |
|---|---|---|
| single config, N=8 and N=16 | ~3.2s (≈0 over baseline) | free |
| **exhaustive all 256 configs, N=8, `decide +kernel`** | **3.2s (0.2s over)** | ✅ ship |
| exhaustive N=8, plain `decide` | 3.9s | works, but +kernel is the default |
| **exhaustive all 65536 configs, N=16, `decide +kernel`** | **6m10s** (sys 3m36s ⇒ GC pressure) | ⚠️ passes, bad CI citizen |
| same via bitmask enumeration (avoiding `sublists`) | **>8m20s, timed out** | ❌ *worse* |
| **pairwise-exhaustive N=16** (all s,s',d,d' × all stages) | **10.9s (8s over)** | ✅ ship |

`by decide` at N=8 and N=16 is realistic with pure kernel reduction, **no `native_decide`**. Why it works: `Nat` add/mul/div/mod/beq/ble are GMP-accelerated in the Lean kernel, so the div/mod representation reduces fast. This is a second, independent reason R3 beats `Fin`/`BitVec` — the danger you named (Nat-vs-Fin reduction blowup) is dodged by staying on `Nat` with kernel-accelerated primitives.

Note the negative result: the "obvious" optimization (enumerate bitmasks instead of materializing `List.sublists`) is *slower*. The 65536 × 5 stages × Nodup work is the floor, not list materialization. Don't spend a day on that.

MITIGATION for N=16: ship the **pairwise** exhaustive (8s) — given sortedness it is logically the full content of the theorem — plus the **configuration**-exhaustive at N=8 (0.2s) plus a handful of named N=16 configs (free). Gate the 6-minute N=16 configuration-exhaustive behind a separate slow target, or drop it.

Salt precedents supporting this: `docs/blueprints/tactics.md:47-56` (`decide +kernel` MANDATORY — plain `decide`/`rfl` stall in the elaborator; 2285× over `norm_num`), `Salt/Tactic/CertEval.lean:222,227` (`maxRecDepth 8000` + `decide +kernel`). maxRecDepth ceilings in the corpus: `Salt/MR/S11Hoist.lean:876` and `Salt/Chen/SuperPanelsE.lean:43` at 100000.

════════════════════════════════════════
4. SALT'S REUSABLE MACHINERY
════════════════════════════════════════

- **`Salt/Tactic/AuditAxioms.lean` (127 lines, `import Lean` only) — copy verbatim.** Provides `#audit_axioms decl…`, a build-*failing* assertion that no declaration depends on anything outside `{propext, Classical.choice, Quot.sound}`. Self-contained, no mathlib dependency, Apache 2.0, same owner, personal lane → no lane-firewall issue. For a public demo whose selling point is "kernel-checked, no native_decide", this is the single highest-value transplant.
- `Salt/Tactic/CertEval.lean` — take the **doctrine** (packed representation + `decide +kernel` + raised `maxRecDepth`), not the code. It is rational-certificate-specific.
- Process transplant: the A/B/C/D pre-classification and "give up early, loudly" budget from `salt/CLAUDE.md`.
- **Nothing else.** I checked: salt's Finset/counting/injectivity helpers are all analytic-number-theory shaped (`Goldbach/`, `SW/`, `MR/`, `Brun/`) — wrong shape. `Salt/Keller/Counterexample.lean` is the Jacobian counterexample, not a large finite `decide` harness; it is not the precedent it looks like from the filename.

════════════════════════════════════════
6. STAGE ESTIMATES AND THE CUT
════════════════════════════════════════

**S1 — the heart. Class B (not C). ~150-200 lines finished. 1-2 days.**
Already proven at 111 lines in this scout pass, sorry-free, axiom-clean. Remaining: naming/docstrings, the operational `step`-iteration lemma, N-boundedness wrappers, and the sharp-hypothesis variant. The div/mod representation is what demotes this from C to B.

**S2 — certificates. Class B. ~120-180 lines. 2-3 days.**
Checker defs 15 ln; `nodupB_iff` 4 ln (proven); `imageAt_nodup_iff` reflection bridge 40-70 ln (all needed mathlib lemmas verified present); "the construction always passes the checker" soundness theorem 40-60 ln on top of S1; certificates ~20 ln.

**S3 — Batcher bitonic + 0-1 principle. Class C. ~800-1200 lines. 2-4 weeks ON ITS OWN.**
Comparator-network infrastructure 100-150 ln; 0-1 principle 150-250 ln; **Batcher's half-cleaner lemma on bitonic 0-1 sequences 300-500 ln** (the classical time sink — cyclic `0^a1^b0^c` / `1^a0^b1^c` case analysis, nothing in mathlib helps); bitonic merge + full sorter by induction on k 200-350 ln; composition 50 ln.
**S3 does not fit a two-week budget alongside S1+S2. Do not attempt it as specified.**

**THE CUT — S3′, the end-to-end theorem in ~1 day instead of ~3 weeks.**
You do not need Batcher's *network* to get an end-to-end switch-fabric theorem — you need the *sorted datum*, and mathlib already supplies it. `Finset.orderEmbOfFin` (`Mathlib/Data/Finset/Sort.lean:198`) gives, for any destination set D with `|D| = n`, a strictly monotone `Fin n ↪o ℕ` enumerating it in order. Feed that to S1 and you get:

> for ANY set of n distinct destinations, presenting them sorted into a concentrated block makes the banyan internally nonblocking — end to end.

That is the theorem a reader cares about. Batcher's network correctness only supplies a hypothesis mathlib can already discharge; deferring it is an honest, clearly-labelled gap ("we assume a sorter; mathlib provides one"), not a hole in the result.

RECOMMENDED ORDERING:
- Week 1: S1 finish + S2. This alone is a complete, publishable artifact.
- Week 2: S3′ composition, the `testBit` facade, README/writeup, `#audit_axioms` CI. Open S3-proper as a "future work" branch.
- **Decide the S3 vs S3′ question on day 1, not day 10.**

════════════════════════════════════════
TOP THREE RISKS
════════════════════════════════════════

**RISK 1 — S3 eats the entire budget. Likelihood HIGH.** 800-1200 lines of class-C work with literally zero mathlib support (0 files match bitonic/comparator/sorting-network/0-1-principle). *Mitigation:* ship S3′ via `orderEmbOfFin`; scope S3-proper post-demo. Commit on day 1.

**RISK 2 — the N=16 certificate becomes a CI anchor. MEASURED, not hypothetical.** 6m10s with heavy GC pressure, and the obvious optimization is worse (>8m20s). *Mitigation:* pairwise-exhaustive at N=16 (8s) + configuration-exhaustive at N=8 (0.2s) + named N=16 configs; slow target for the rest.

**RISK 3 — representation lock-in, discovered late.** Starting from `Fin (2^k)` + `testBit` (the "natural" choice) or `BitVec` + `bv_decide` costs you `omega` on the endgame, adds a coercion tax, forces truncated-subtraction pain via the ascending stage index, and — for BitVec — you find out only after building S2 that `bv_decide` emits `_native.bv_decide.ax_*` and voids the no-new-axioms claim. *Mitigation:* ℕ + div/mod carrier, descending `m`, `testBit` facade shipped day 1. The proof in `ProbeS1.lean` is the reference.

════════════════════════════════════════
ONE MATHEMATICAL CATCH WORTH SHIPPING
════════════════════════════════════════
Concentration is genuinely necessary, and here is the minimal counterexample — worth putting in the repo as an `example`, it is the kind of detail that makes a demo credible. k=2 (N=4), sources {0, 2} (sorted destinations, *not* concentrated), dest 0 = 0, dest 2 = 1. At stage m=1: `line 1 0 0 = 0` and `line 1 2 1 = 0`. Collision, despite strictly increasing destinations.

Relatedly, the proof shows the *sharp* hypothesis is not "concentrated + sorted" but `dest b - dest a ≥ b - a` for `a < b`. Stating the sharp version and deriving the textbook one costs ~5 lines and is a genuine small improvement on the usual presentation.

════════════════════════════════════════
PROBE ARTIFACTS (scratchpad, not in the repo)
════════════════════════════════════════
- `/private/tmp/claude-501/-Users-jyh-projects-claude-salt/ea81b992-0821-4192-8f48-c0dcdcbc14c2/scratchpad/ProbeS1.lean` — **S1 complete, 111 lines, sorry-free, axiom-clean. Lift this into the repo as-is.**
- `.../ProbeFacade.lean` — `testBit_line` + `testBit_step`, the bit-routing facade.
- `.../ProbeA.lean` — the checker + N=8/N=16 single and exhaustive certificates.
- `.../ProbeD.lean` — the pairwise N=16 exhaustive (the 8s mitigation).
- `.../ProbeC.lean`, `.../ProbeG.lean` — the two slow N=16 variants (6m10s / timed out), kept as negative results.
- `.../ProbeH.lean` — S2 reflection bridge skeleton (`nodupB_iff` proven; `imageAt_nodup_iff` left as the one `sorry`, priced at 40-70 lines).
