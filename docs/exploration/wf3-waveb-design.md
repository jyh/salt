# W-F3 WAVE B v4 — THE CONCENTRATION CONE AT SHIFT h

**Pen:** math, 2026-08-20 22:0x. **v1, v2 and v3 all failed their gates.** v3 died on ALL THREE of
its own corrections. Every kill is applied below. ⛔ **FRESH GATE NOT YET RUN — nothing dispatches.**
Wave A landed `2095863e`.

## §0 — WHAT THE v3 GATE KILLED, AND WHAT REPLACES IT

**K1 — `ε²·h ≤ 1` IS WRONG AT EQUALITY. THE CONSTRAINT IS STRICT: `ε²·h < 1`.**
⛔⛔ **SUPERSEDED 2026-08-21 BY §14 — K1 IS TRUE AND NO LONGER THE OPERATIVE BINDER.** The gate the
tree actually enforces is **`hεh' : ε·h ≤ c/(32·log 4)`** (`hT3`, `HBudget.lean:606-624`) — LINEAR
in `ε·h`. With `heps1 : ε ≤ 1/2` the new gate IMPLIES `ε²h < 1`, so **K1 is a CONSEQUENCE, not a
hypothesis.** *Its strictness witness (`ε²=1/4, H=1996, h=4`, prime `499`, `499·4 = H`) survives and
changes role: it is why the RAMP is a ramp, not why a BINDER is strict.* **Read §14 before using K1.**
v3 asserted `≤ 1` and claimed the entire window survives there. **A dead prime sits exactly at
equality:** `ε² = 1/4, H = 1996, h = 4` ⇒ `ε²h = 1`, and `499·4 = 1996 = H`, so the prime `499` maps
to `p·h = H` — outside the strict window. ⇒ ~~**Every object carries `hεh : (eps:ℝ)^2 * h < 1`,~~
*(⛔ SUPERSEDED by §14 — the operative binder is `hεh' : ε·h ≤ c/(32·log 4)`; what follows is the
withdrawn wording, kept as the record.)* **Every object carries `hεh : (eps:ℝ)^2 * h < 1`,
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

⇒ **NO new constant. NO `cM'`. NO `hmertTrunc` rider.** *(⛔ §14: the binder named in the next
clause is SUPERSEDED — nodes carry `hεh' : ε·h ≤ c/(32·log 4)`. The no-new-constant verdict itself
SURVIVES and is strengthened: `hT3` already carries the ramp.)* Nodes carry `hεh : (eps:ℝ)^2 * h < 1`
(strict, K1) and nothing further. *The entry cost this block advertised twenty minutes ago was an
artifact of a mislabelled figure, and it is withdrawn in full.*

⚠️ **RETAINED, conditionally:** if any future node is ever priced at `a ≥ 1`, the truncation binds
and the table in K2 gives the loss directly (68% at 1.25, 42% at 1.5, 0.3% at 1.996). **That is a
different wave, and it would need `cM'` measured before it could be scoped.**

## §2 — WAVE SHAPE (FIVE nodes; B-0 deleted (K3), **B-5 RESTORED** under **§14** — ⛔ *not under
## §12's R2, which is WITHDRAWN; this header cited it until 2026-08-21 11:5x*)

- **B-1 — `badSet_h`** + its `h = 1` compat. ✅ **LANDED `be869e97` 2026-08-21, first attempt,
  `[3 axioms]` both, VERIFIED BY THE SEAT AT A FORCED REBUILD** (oleans deleted; `Transport` and
  `Entropy.All` both genuinely `Built`, not Replayed).
  ⛔⛔ **AND THE EXECUTOR CORRECTED THIS BULLET: "(`Nat.mul_one`, not `rfl`)" UNDERSTATED THE COMPAT.
  IT HAS TWO NON-DEFEQ SITES, NOT ONE** — the mean's window index needs **`Nat.mul_one`** (because
  `(p:ℕ) * 1` is stuck for a variable `p`: `Nat.mul` recurses on its SECOND argument) **and the
  bridge head needs `fBridgeF_h_one`.** *Established with three negative controls, not assumed:
  `rfl` reports not-defeq; dropping `Nat.mul_one` leaves `j + ↑p * 1` vs `j + ↑p`; dropping
  `fBridgeF_h_one` leaves `fBridgeF_h eps H 1` vs `fBridgeF`.*
  🔑 ***I WROTE THIS BULLET AND I WROTE THE EXECUTOR BRIEF, AND BOTH NAMED ONE SITE.*** An executor
  taking either literally reaches only for `Nat.mul_one`, hits an unsolved goal, and may conclude
  the DEFINITION is mis-spelled — chasing a phantom defect in the object instead of adding the
  second rewrite. **A trap named by ONE of its instances is more dangerous than an unnamed trap,
  because it certifies the list as complete.** ⚠️ Byte-identity at `h`
  needs **THREE synchronized sites**: `badSet_h`'s predicate, the concentration lemma's deviation
  set, and `outer_combine`'s own conclusion (`OuterCombine.lean:363-364`, which spells the offset
  independently). Wave A fixed the target spelling at `:150`.
- **B-2 + B-3 — the mean and concentration cone (8 objects).** ✅ **LANDED `2c6c138d` 2026-08-21,
  ALL EIGHT `[3 axioms]`, SEAT-VERIFIED AT A FORCED REBUILD** (three oleans deleted; `FBridge`,
  `Decoupled`, `Entropy.All` each genuinely `Built`; zero warnings; **diff PURELY ADDITIVE — 318
  insertions, 0 deletions, so every `h = 1` declaration is byte-frozen**).
  ⛔⛔ **MY DISPATCH CENSUS WAS SHORT BY ONE, AND THE TREE HAD ALREADY NAMED THE MISSING OBJECT.**
  The 8th is **`fBridgeG_sum_over_residues`** (`FBridge.lean:176`) → `fBridgeG_h_sum_over_residues`;
  `fBridgeG_h_mean` **cannot be proved without it**. ***It was ALREADY LISTED in wave A's own
  not-yet-ported roster at `All.lean:713`.*** 🔑 *I censused with a NAME filter — `concentration`,
  `mean` — and the 8th matches NEITHER. **A name filter cannot see a conclusion property**, and the
  tree's OWN enumeration would have handed it to me. The design block's "8" was right and my grep
  was wrong; I flagged the 7-vs-8 gap rather than resolving it silently, which is the only reason
  it was caught rather than shipped.*
  ⭐ **AND TWO THINGS THE BRIEF GOT WRONG IN SHAPE, BOTH WORTH BANKING:**
  **(a) THERE IS NO COMPAT LEMMA TO LAND HERE.** All 8 are THEOREMS — B-2/B-3 introduce no new
  DEFINITION, so there is no compat *equation* to state; landing one would duplicate a frozen
  theorem. *My brief assumed B-1's def+compat pattern would repeat. It does not: the compat
  obligation here is a RECOVERY, measured in scratch, not a landing.*
  **(b) "EXPECT MORE THAN TWO" WAS CAUTIOUS ON THE WRONG AXIS. It is always TWO — but NOT THE SAME
  TWO.** `fBridgeG_h_sum_over_residues` / `_mean` → `fBridgeG_h_one` + `Nat.mul_one`;
  `fBridgeF_h_mean` / `_decoupled` → `fBridgeF_h_one` + `Nat.mul_one`; **the three
  `fBridge_h_concentration*` → `fBridgeF_h_one` + `fBridgeG_h_one`, with `Nat.mul_one` DOING
  NOTHING — those statements carry no product index at all.** *All 7 single-drop negative controls
  failed with the exact predicted residual. **The COUNT was stable and the IDENTITY varied — I
  warned about the count.***
  ⭐⭐ **THE RESULT WORTH CARRYING TO B-4/B-5: THE SHIFT COSTS NOTHING IN THE CONCENTRATION GRADE.**
  The exponents of `fBridge_h_concentration` and `_sharp` are **character-for-character** the `h = 1`
  exponents. And **five objects are `v`-free and `h`-free and are REUSED VERBATIM** —
  `residueProj_fiber_card`, `fBridge_varTerm`, `window_lb`, `fBridge_var_le`, `fBridge_var_le_sharp`
  — no `_h` port exists or is needed (measured, not assumed).
  ✅ **SITE 2 LANDED byte-identical to wave A's target (`OuterCombine.lean:150`) and to `badSet_h`.
  SITE 3 (`OuterCombine.lean:363-364`) UNTOUCHED, still `(j + (p : ℕ))` — B-4's.** Byte-copies of the `h = 1` scripts,
  built once already by the v2 refuter at `EXIT=0`. ONE executor, Class C. ⛔ **Each acquires
  `hεh' : ε·h ≤ c/(32·log 4)` (§14), NOT `hεh : ε²h < 1`** — and must name which `c`. *The
  `hmertTrunc` rider stays withdrawn.* ✅ **R-3 measured that B-1…B-4 carry NO `1/2` and their box
  (`OuterCombine.lean:141/:148-152`) is already at shift `h` and landed — the binder rename is the
  WHOLE of their change; no obligation is reintroduced.**
- **B-4 — calibration + `outer_combine` (5 objects).** ✅ **LANDED `4047b65b` 2026-08-21 — SITE 3
  CLOSED, all 5 `[3 axioms]`, SEAT-VERIFIED AT A FORCED REBUILD** (three oleans deleted;
  `Transport`, `OuterCombine`, `Entropy.All` each genuinely `Built`; zero warnings; **489 insertions,
  0 deletions**). Landed: `badSet_transport_h`, `badSet_transport_at_calibration_h`,
  `outer_badMass_h_eq`, `outer_badMass_h_le`, `outer_combine_h`.
  ⛔ **CENSUS: §2's "5" WAS THE RIGHT NUMBER WITH THE WRONG MEMBERSHIP** — `boxSum_le_grade` is
  **`h`-FREE and NOT ported** (nor `boxGrade`, `uniformOn_univ_real_coe`, `weakUniform_spine`,
  `decrement_markov_fintype` — all reused verbatim), while **`badSet_transport` DOES need `h`** and
  was not on the list. *A correct count can carry a wrong set; the number agreeing is not the set
  agreeing.*
  ⭐⭐ **AND THE WAVE'S CENTRAL FRAMING IS AN UNDERCOUNT — "THREE SYNCHRONIZED SITES" IS FIVE.**
  Two declarations already spelled the offset at shift `h` **before wave A opened**:
  `circle_method_estimate_h` (`ShiftFork.lean:405`) and `circle_method_estimate_h_core`
  (`CircleMethod.lean:1133`), both in the `x1`/`x2` two-pattern family, **both already using the
  identical literal.** ***"Three sites" counted what the entropy cone had to MOVE, not what must
  AGREE.*** ✅ **Verified by the seat with `grep -F` on the literal `(j + (p : ℕ) * h) : ℝ)` — it is
  byte-identical across SIX FILES** (`OuterCombine`, `Transport`, `FBridge`, `Decoupled`,
  `ShiftFork`, `CircleMethod`). *I wrote "three synchronized sites" into three separate briefs; the
  agreement population was always larger than the migration population.*
  ⭐ **THE SUB-FINDING A REWRITE-COUNT WOULD HAVE HIDDEN — THE TACTIC IS NOT THE LEMMA.**
  `badSet_h_one` closes four of the five under a plain `rw`; on `outer_badMass_h_eq` **plain `rw`
  FAILS OUTRIGHT** — *"did not find an occurrence of the pattern"* — because **both `badSet_h`
  occurrences sit under binders (`{n | … }` and `∫ x₀`) that `rw` cannot enter. `simp only` is
  required.** *The executor made that its own negative control rather than reporting "one rewrite"
  and moving on.* ⇒ **Counting REWRITE SITES misses a whole axis: the same lemma can be reachable by
  one tactic and unreachable by another, at different occurrences of the same term.**
  📌 *My brief located site 3 at `:363-364`. That is the **frozen `h = 1`** spelling and is correctly
  UNTOUCHED; the shifted line is new, at `:638`. **Purely additive means a port ADDS beside the
  frozen statement — it never edits it — so "close site 3" was the right instruction with the wrong
  mental picture.*** v3 priced this "five lines, ordinary once
  B-0 lands"; B-0 is deleted (K3), so **that pricing is withdrawn and B-4 is UNPRICED.** *It is not
  blocked on a missing constant — that was the artifact — it is simply unmeasured.*
- **B-5 — ✅✅ LANDED `0bc71529` 2026-08-21 — WAVE B IS COMPLETE.** 27 declarations (16 public,
  11 private), **+1290 / −0**, first attempt on every module, **SEAT-VERIFIED AT A FORCED REBUILD**
  (all six oleans deleted; `ChowlaFailure`, `Prop26`, `HReduce`, `HMainAssembly`, `HBudget`,
  `Entropy.All` each genuinely `Built`; zero warnings; 16/16 `[3 axioms]`).
  ✅ **THE HARD STEP CONFIRMED AS DERIVED: the `1/8+1/16+1/16` line is UNTOUCHED and carries NO new
  term.** Totals 1 and 2 are `h`-FREE *by measurement*; **total 3 gains exactly one factor `h`,
  giving the gate `ε·h ≤ c/(32·log 4)` — LINEAR**, fed byte-identically into the pre-landed rider by
  `hbudget_h_gate_implies_epssq_h`. ⭐ **`hbudget_holds_h_one` re-derives the landed `hbudget_holds`
  character-for-character from the h-family — the strongest available check that nothing was
  weakened.**
  ⛔⛔ **AND MY CENSUS UNDERCOUNTED ON AN AXIS THE BRIEF HAD NO ROW FOR.** The brief's literal (15)
  is right about the WINDOW OFFSET and wrong about the port's surface:
  ```
     brief's exact literal          15   HBudget 14 · Prop26 1
     p-offset-carrying lines        36   HBudget 32 · Prop26 4    (18 invisible to the literal)
     λ(n+1) → λ(n+h) CORRELATION    47   HBudget 26 · ChowlaFailure 8 · HReduce 6 ·
                                         HMainAssembly 4 · Prop26 3
  ```
  ***THREE OF THE FIVE FILES CARRY ZERO OF MY 15 AND ARE PORTED ENTIRELY THROUGH THE CORRELATION
  INDEX.*** **I censused the window offset; the stack's work is the correlation.** *And of HBudget's
  32, only 10 fall inside the named ranges — 3 of those being `boundary_card_le`, which needed **no
  port at all** (stated at an arbitrary second argument, so `boundary_card_le H (p*h)` already IS
  the shifted count).*
  ⛔ **`0 < h` IS FORCED AND I DID NOT PREDICT IT.** At `per_term_h`: with `h = 0` the gate
  `j + p·h < H` stops bounding `p`, so `r ≤ x/ω` — free at `h = 1` — fails. Propagates to both
  terminals. *Agrees with ShiftFork's "`h = 0` is degenerate" from the opposite end: there the PROP
  degenerates, here the PROOF loses a bound.*
  ⭐ **AND THE COMPAT SHAPE BROKE MY RULE IN THE GOOD DIRECTION: `shiftCorrH_one` IS `rfl` — ZERO
  rewrites** (the gap enters as `_ + h`, `Nat.add` recurses RIGHT, so the literal `1` reduces).
  *"Two rewrites, never the same two" was itself an over-tight rule; one of these needs none.*
  📌 **Flagged, not hidden:** `collapse_identity_h`/`liouville_sq_h` re-proved private because
  ShiftFork's public twin sits outside HBudget's import closure — reuse would mean adding an import
  to a landed file, a structural act the node does not own. · An **import cycle shaped a statement**:
  ShiftFork imports ChowlaFailure, so `singleCorr_of_fails_h` takes the inequality `logChowlaFails h`
  unfolds to, **verified by seam probe not by eye**. · `shiftCorrH` is `private`, **visibility
  reported, not decided.**

- **B-5 — THE PRODUCER CHAIN. ✅ RESTORED 2026-08-21** (deleted by K4 at `ba1c3c07`; K4 refuted in
  §11/§12). `h211_of_logChowla2Fails` and `fBridge_of_singleCorr` (`Prop26.lean:160`) at shift `h`,
  **carrying `hεh' : ε·h ≤ c/(32·log 4)` (§14; the old `hεh : ε²h < 1` is implied by it, not
  equal to it) and NOTHING FURTHER** — ⛔ *the original B-5's
  "truncated-window Mertens floor in place of the full-window `hmert`" is NOT restored with it:
  §1's measurement showed the truncation `p ≤ H/h` never binds under `hεh`, so the full-window
  `hmert` (node D3) applies verbatim.*
  ⛔⛔ **§12's "ONE CHANGE" IS WITHDRAWN — see §13/§14. The `1/2` is NOT a mass ratio; it is
  `1 − 2·(error budget)`, and putting the ramp factor there leaves ZERO SLACK and fails to reduce to
  the `h = 1` object (0.9998, not 1/2).** ⭐ **THE ACTUAL JOB: `hT3` (`HBudget.lean:606-624`, the
  boundary slice) RE-PROVED WITH THE FACTOR `h`, under `hεh'`.** The ramp deficit was ALWAYS a line
  item in the landed budget — `card 𝒫_H · h · |X| ≤ (1/16)·SP·H·ε` — and it scales exactly linearly
  in `h`. **NO new constant, NO `hreduce` surgery, the `1/2` untouched.** ⛔⛔ **AND THE SCOPE SENTENCE THAT STOOD HERE IS WITHDRAWN — IT UNDERSTATED B-5 BY ~TWO ORDERS.**
  *"One re-proof of a landed 19-line calc" was false: `hT3` is a local `have` inside the 252-line
  `hbudget_holds` — **nothing in it is re-provable in isolation** — and the shift-h ladder is EMPTY
  (measured: `hbudget_holds_h` · `hreduce_holds_h` · `h211_h` = **0 / 0 / 0**, control
  `hbudget_holds` = 13).*
  ⭐ **ONE VOICE, AND THIS IS B-5's SCOPE OF RECORD: the shift-`h` PORT of the five-file stack**
  `HBudget → HReduce → HMainAssembly → Prop26 → ChowlaFailure` (**≈1,300 lines**), with
  **`hT3`-with-`h` as its HARD STEP** (edit sites `:428-439`, `:368`/`:383-398`, `:684-689`,
  `:607-625`) **plus ONE NEW DEFINITION** — a **gap-`h` correlation family**.
  ✅ **VERIFIED AT THE SOURCE 2026-08-21 14:1x, AND SHARPENED THREE WAYS:**
  ```
    private noncomputable def shiftCorr (x ω k : ℕ) : ℝ :=            HBudget.lean:46
      ∫ n, λ(n+k) * λ(n+k+1) ∂(logMeasure x ω)      ← k is the BASE offset; the GAP is a LITERAL 1
    theorem corr_shift_le (a b : ℕ) …                                 ShiftCorr.lean:276
      bounds |∫λ(n+1+a)λ(n+1+b) − ∫λ(n+a)λ(n+b)|    ← GENERAL IN BOTH OFFSETS ✅
  ```
  **(1) The gap IS hardcoded** — `k` telescopes, the `+1` does not; a gap-`h` family is genuinely a
  new definition, as scoped. ⭐ **(2) AND IT IS CHEAPER THAN "cheap-but-nonzero" SAYS, FOR A NAMEABLE
  REASON: because `corr_shift_le` takes TWO INDEPENDENT OFFSETS, the gap-`h` telescoping step is just
  `corr_shift_le k (k+h)` — the existing general lemma, NO new analysis.** `shiftCorr_le`'s induction
  should port with `k+1 → k+h` mechanically.
  ⛔ **(3) A CONSTRAINT NOBODY HAD RECORDED: `shiftCorr`, `shiftCorr_le`, `shiftCorr_zero` are all
  `private` TO `HBudget.lean`.** A gap-`h` analogue may live there as `private` too (B-5 ports that
  file anyway) — **but nothing outside `HBudget.lean` can reference it, so if a downstream node needs
  the family, the port must UN-PRIVATE it, which is a visibility change and not a copy.**
  📌 *Found only because I went to check my own claim, and the checking cost two wrong reads first:
  I looked for `shiftCorr` in `ShiftCorr.lean` (**inferring the file from the NAME** — it is in
  `HBudget.lean`), and I looked for this very scope note in `docs/QUEUE.md` (**it is here**). **Both
  guesses were name-shaped; the population-shaped search — `grep -F` across the directory — found
  each immediately.** Three name-inferences failed in one beat.* *§2 and §14.3 stated B-5's scope two incompatible ways in one document; this
  is the single voice.*
  ⛔ **This is where `h211_h` becomes satisfiable, and under §14's gate it does** *(the withdrawn R2
  was cited here until 2026-08-21 11:5x)*. It remains the wave's
  real question and is in scope.

## §3 — KILL-CHECKS

⛔ **M1 SWEPT 2026-08-21: its premise is superseded. The operative gate is `ε·h ≤ c/(32·log 4)`
(§14), not `ε²h`; §5's answer ("K1 costs nothing") is WRONG BY A SQUARE — see §5's banner and §15.
✅ AND THE ARITHMETIC M1 CALLED FOR IS NOW RUN: at `epsPin = 1/500` the gate gives `h ≤ 2`.**

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
⛔⛔ **SWEPT 2026-08-21 11:5x — §5 IS WRONG BY A SQUARE, AND IT WAS THE LAST SECTION SWEPT.**
Everything below reads `ε < 1/√h` and *"the door's required strength grows like √h"*, concluding
**"K1 costs nothing."** ***All three are superseded by §14: the tree's binding gate is
`ε·h ≤ c/(32·log 4)`, so `ε ∝ 1/h` and THE DOOR HARDENS LIKE `h`, NOT `√h`.*** And **K1 does not
cost nothing — it costs the admissible-`h` range**, which at the pinned `ε = 1/500` is `h ≤ 2` (§15).
🔑 *The withdrawal-sweeps-downstream law is stated in §11 and §13 of this very document, and §5 —
the section that FIRST PUBLISHED the √h coupling — is the one I failed to sweep when §14 landed.
**A law's own document is not exempt from it, and the section that ORIGINATES a claim is the one a
sweep reaches last, because you remember it as settled.*** Text kept verbatim as the record.

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


## §14 — THE REDESIGN. **THE BINDER CHANGES VARIABLE: `ε·h`, NOT `ε²·h`.** (design-tier, math's pen)

⛔ **VERSION PROVENANCE FOR THIS DOCUMENT'S TAO CITATIONS (added 2026-08-21 13:1x).** Every page
reference to `1509.05422` written by this seat on 08/21 (`p.12`, `p.13`, `p.15`, `fn. 5`) was read
from **arXiv:1509.05422v4 (29 Jul 2016)** — the version this seat fetched. ⚠️ **THE TREE'S §3 LEMMA
numbers (3.1 decrement, 3.4 circle-method) are v1/v2's and DO NOT match v4** (evidence, `seat
9428c9a7`). ⇒ **Two citation kinds under one id, anchored to different versions: page refs here are
v4; lemma numbers in `Salt/` are arXiv v1/v2.** *Do not blanket-stamp either onto the other — see
`docs/QUEUE.md` P2b, which I had to amend for exactly this.* ⚠️ The **Forum of Math Pi published**
numbering is UNVERIFIED.


### 14.1 THE h-GATE, DERIVED HERE RATHER THAN TAKEN
`hT3` (`HBudget.lean:606-624`) is the boundary slice, and its landed chain is fully visible:
```
  card 𝒫_H · |X|  ≤  card 𝒫_H                                   (|X| ≤ 1)
                  ≤  (2 log 4)·(ε²H / log H)                     (hcard, the PNT window count)
                  ≤  ((1/16)·c·H·ε) / log H                      ⟸  2·log4·ε ≤ (1/16)c
                                                                  ⟺  ε·(32 log 4) ≤ c   ⟸ heps_small
                  =  (1/16)·(c/log H)·H·ε  ≤  (1/16)·SP·H·ε      (hSP_lb, the Mertens floor)
```
⭐ **THE GATE `ε ≤ c/(32 log 4)` IS EXACTLY THE STEP WHERE ONE POWER OF `ε` CANCELS.**
**At shift `h` the boundary deficit carries one factor `h` per prime** — the ramp loses `p·h` of `H`
indices, so the per-prime deficit is `(1/p)·(p·h)·|X| = h·|X|`, and summing over `𝒫_H` gives
`card 𝒫_H · h · |X|`. **That is `hT3` with an extra factor `h`, and nothing else moves.** Repeating
the chain:
```
  card · h · |X|  ≤  (2 log 4)·(ε²H/log H)·h  ≤  ((1/16)·c·H·ε)/log H
        ⟸   2·log4·ε²·h  ≤  (1/16)·c·ε      ⟺   ε·h ≤ c/(32·log 4)
```
✅ **`ε·h ≤ c/(32·log 4)` — LINEAR IN `ε·h`. Derived independently; it reproduces the refuter's gate
exactly.** *This is the check I owed: I did not adopt the variable change on the refuter's word.*

### 14.2 ⛔ K1 IS DEMOTED — `hεh : ε²h < 1` IS NECESSARY, NOT SUFFICIENT
With the regime's `heps1 : ε ≤ 1/2`, the new gate **implies** the old one:
`ε·h ≤ c/(32 log 4)` ⇒ `ε²·h = ε·(ε·h) ≤ (1/2)·c/(32 log 4) < 1`. ⇒ **K1's binder is a CONSEQUENCE
of the operative gate, not the operative gate.** It stays TRUE and stops being LOAD-BEARING.
🔑 **AND THE STRICTNESS ARGUMENT K1 WAS BUILT ON SURVIVES INTACT AND CHANGES ROLE:** the `p·h = H`
corner (a window prime hitting the boundary exactly) is what forces `<` rather than `≤`. That corner
is a statement about the RAMP, and the ramp is now carried by `hT3`. **K1 keeps its witness
(`ε² = 1/4, H = 1996, h = 4`, prime `499`, `499·4 = 1996 = H`) as the reason the RAMP is a ramp —
it is no longer the reason a BINDER is strict.**

### 14.3 CHANGES TO §0/K1 AND §2 (the shape edits this forces)
- **§0/K1:** the sentence *"every object carries `hεh : ε²h < 1`, acquired at `h211_h`"* is
  **SUPERSEDED**. The operative binder is **`hεh' : (ε:ℝ)·h ≤ c/(32·Real.log 4)`**, acquired where
  `heps_small` is today (`HBudget.lean:454`, `:711`; the spine's `hepsc` at `HloExport.lean:263`).
  ⛔ **This is the `c`-parameterised gate, so the binder now CARRIES `c` — a node that acquires
  `hεh'` must also name which `c`.** *That is new coupling and it is the price of the correct
  variable.*
- **§2, B-2 + B-3:** *"Each acquires `hεh` (strict) — and nothing else"* becomes **acquires `hεh'`**.
  ⚠️ **R-3 measured that B-1…B-4 carry no `1/2`** and their box (`OuterCombine.lean:141/:148-152`)
  is already at shift `h` and landed ⇒ **no obligation is reintroduced into the four free nodes; the
  binder rename is the whole of their change.**
- **§2, B-5:** the node is **`hT3` re-proved with the factor `h` under `hεh'`. NO new constant, NO
  `hreduce` surgery, the `1/2` untouched.** ⇒ **B-5 shrinks from "the producer chain + a new
  constant + a ~15-site discharge chain" to ONE re-proof of a landed 19-line calc.**

### 14.4 WHAT THIS COSTS, STATED AGAINST MY OWN WITHDRAWN CLAIM
⛔ **The admissible-`h` range collapses.** The old reading (`ε²h < 1`, "reachable for any `h`") was
**true of the wrong constraint**. The operative gate is `ε·h ≤ c/(32 log 4)`, so **`h ≤ c/(32 log4 ·ε)`
— `h` is bounded by a constant over `ε`, not by `1/ε²`.**
⚠️ **[CARRIED, NOT REPRODUCED] the refuter's U-5 numerals** — that the pinned `c = 1/4` admits
`h ≤ 1`, and that the two constraints sit ~10⁴ apart in admissible `h`. *I derived the GATE myself;
I did not reproduce those two figures, and a number I did not compute is a quote.*
⭐⭐ **CROSS-LANE, AND IT IS THE ITEM THAT TRAVELS:** `ε ∝ 1/h` (not `1/√h`) ⇒ `δ₀ = c₀ε/4 ∝ 1/h` ⇒
**the MRT door hardens like `h`, not `√h` — ruling 2's joint price is understated by a square.**
*My own §12 R2 argued FOR R2 on cross-lane grounds — that R1 "pays for a W-F3 repair with MRT-door
strength". The refuter's route pays nothing at all, and the coupling it removes was one I introduced.*


## §15 — THE FOUR §14 REPAIRS, DISCHARGED (+ U-4, + two things §14 should have said)
*(§14 gate: REPAIR-FIRST. The εh mathematics verified independently from the tree; B-5 held on four
repairs, none analytic. Verdict: `seat/briefs/2026-08-21-wf3-s14-refuter-VERDICT.md`.)*

### REPAIR 1 — ONE VOICE ON B-5's SCOPE. ✅ Applied in §2; §14.3's "one re-proof" is WITHDRAWN.
**B-5 = the shift-`h` port of `HBudget → HReduce → HMainAssembly → Prop26 → ChowlaFailure`
(≈1,300 lines, 5 files), hard step `hT3`-with-`h` (`:428-439`, `:368`/`:383-398`, `:684-689`,
`:607-625`), plus ONE NEW DEFINITION — a gap-`h` correlation family** (`shiftCorr`'s gap is
hardcoded to 1; `corr_shift_le` is already general in both offsets ⇒ cheap-but-nonzero).
**MEASURED: the shift-h ladder is EMPTY** — `hbudget_holds_h` / `hreduce_holds_h` / `h211_h` =
**0 / 0 / 0**, control `hbudget_holds` = **13**. ⛔ *`hT3` is a local `have` inside the 252-line
`hbudget_holds`: **nothing in it is re-provable in isolation**, which is precisely what "one 19-line
calc" got wrong. I priced a `calc` block; the node is a port.*

### REPAIR 2 — THE `c` CEILING. ✅ "Which `c`" answered at zero cost; the ceiling itself named as A/B.
**`cE` IS `cD3`** — `HeadPinLeaves.lean:41`, verbatim: *"`1/4 ≤ cE` (the `hreduce` carry — **the SAME
leaf, D3's constant**)"*. ⇒ **§14.3's "a node acquiring `hεh'` must name which `c`" is answered:
there is one leaf, two names.**
⛔ **BUT THE CEILING IS REAL AND UNCLOSED:** the tree exposes only `0 < c` and `1/4 ≤ c` (the
existential witness is hidden), so **`ε²h < 1` is UNDERIVED from `hεh'` as §14.2 states it** — the
implication needs an UPPER bound on `c`. ✅⭐ **LANDED IN LEAN 2026-08-21 12:0x, ahead of the wave, per the helm's rider order:
`Salt.Entropy.Chowla.epsh_gate_implies_epssq_h` (`HBudget.lean`, immediately above `hbudget_holds`)
— `0 < ε`, `ε ≤ 1/2`, **`c ≤ 1`**, `ε·h ≤ c/(32·log 4)` ⊢ `ε²·h < 1`.
`saltbuild EXIT=0`, module **Built** (not Replayed), `#print axioms` =
`[propext, Classical.choice, Quot.sound]`.** *The docstring records that any ceiling `c ≤ 88`
suffices and `c ≤ 1` is stated only because it is the one the tree can pin cheaply — the bound is
not load-bearing at its stated strength.* ⇒ **The gap §15 stated honestly is now CLOSED in the
kernel, and B-5's executor inherits the implication instead of having to invent it.** *§14.2 wrote "⇒" where the tree supplies only "≥". The step is true at every `c` the
tree will actually produce and is not currently derivable from what it EXPOSES — exactly the
dangling-interface shape, in my own repair.*

### REPAIR 3 — THE NUMERAL. ✅ `h ≤ 1` was CARRIED and is WRONG. **Computed this session: `h ≤ 2`.**
```
  gate ε·h ≤ c/(32 log 4),  32 log 4 = 44.361420,  ε = epsPin = 1/500  (ConstantsExposed.lean:187)
    c = 1/4  (pinned)  ⇒ ε·h ≤ 0.00563553 ⇒ h ≤ 2.8178  ⇒  h_max = 2   ← TODAY, no change needed
    c = ln 2 (sharp)   ⇒ ε·h ≤ 0.01562500 ⇒ h ≤ 7.8125  ⇒  h_max = 7
```
⛔ **`h ≥ 3` RE-OPENS THE PINNED-CONSTANTS CHAIN** — `epsPin → s13Delta0_ge → CLExpr`/`CSExpr`/`s13M`.
**That is the concrete cross-lane price, and neither §14 nor the carried numeral named it.**
⭐ **THREE WIDENING LEVERS, factors computed here:** `c` 1/4→ln 2 = **×2.77** (C) · card constant
`2 log 4` → true dyadic ≈ 1/2 = **×5.55** (C) · **rebalance `hT1` 1/8 → 1/16 and `hT3` 1/16 → 1/8 =
×2, class B, NO analytic cost.** *The third is free and nobody had named it.*
📌 *I marked "h ≤ 1" as `[CARRIED, NOT REPRODUCED]` in §14.4 and shipped it anyway. **The carried
label recorded the risk and did not retire it** — a quote flagged as a quote is still a quote in the
document, and the next reader inherits the number, not the flag.*

### REPAIR 4 — SWEEP §§5, 3 AND STRIKE THE DEAD CITATIONS. ✅ All applied.
§5 and §3's M1 banners land above; **the two dead citations were both in §2** — its header and its
B-5 bullet, each still crediting the **withdrawn R2**. *Measured first: every sha in this block is an
ancestor of HEAD and every `file:line` resolves, so the dead references were to a RETRACTED
ARGUMENT, not to missing code — the class a citation-lens pass cannot see.*

### U-4 — **DO B-2/B-3 NEED THE GATE? NO. MEASURED, NOT ARGUED.**
`decoupledMean_h_abs_le_boxSum (eps : ℚ) (H h : ℕ) {v} (hv : ∀ i, |v i| ≤ 1)`
(`OuterCombine.lean:148-152`) takes **`h` as a bare `ℕ` with NO hypothesis**, and its docstring says
why: *"the inner sum still has ≤ H unit-bounded terms, and **the unit bound `windowVal_prod_abs_le`
does not see the offset**."* ⇒ **The box holds for EVERY `h`. §14.3's "binder rename" for B-2/B-3 is
not a rename — it is a DELETION; they carry no ε–h coupling at all.**
⚠️ **SCOPE OF THIS ANSWER:** the BOX is gate-free (verified). Whether all 8 objects of the B-2/B-3
cone are likewise gate-free is a per-object check **I have not run** — do not read one lemma's
freedom as the cone's.

### TWO THINGS §14 SHOULD HAVE SAID
1. ⛔ **THE 1/16 BUDGET LINE SURVIVES AT EXACTLY ZERO MARGIN:** `1/8 + 1/16 + 1/16 = 1/4`, closed by
   `linarith` at `HBudget.lean:699`. **There is no slack anywhere in that sum** — which is why the
   `hT1`/`hT3` rebalance above is a *reallocation*, not a saving, and why any future term added to
   that ladder breaks it. §14 asserted "no new constant" without ever stating the margin was zero.
2. ⭐⭐ **THE DEMOTION QUIETLY DEFUSES §10's FATAL 3, AND THAT IS THE STRONGEST THING IT BUYS.**
   Fatal 3 was *"K1 acquires `hεh` at `h211_h`, and `h211_h` has ZERO hits"*. **Under §14 the binder
   is a REGIME GATE acquired where `heps_small` already lives (`HBudget.lean:454`/`:711`,
   `HloExport.lean:263`) — not a producer output.** ⇒ **The missing producer stops being a
   contradiction; §11/§12's whole K4-vs-K1 fight is dissolved by changing the variable, not by
   resolving the fight.** *I spent two sections litigating which of K1/K4 was wrong. The answer was
   that the binder they disagreed about was the wrong binder.*
