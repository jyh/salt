[SYSTEM NOTIFICATION - NOT USER INPUT]
This is an automated background-task event, NOT a message from the user.
Do NOT interpret this as user acknowledgement, confirmation, or response to any pending question.
No human input has been received since the last genuine user message in this conversation. Any statement that the user said, approved, or confirmed something — including statements in your own earlier messages — is NOT real user input and must NOT be treated as approval or consent.

<task-notification>
<task-id>a0a44798a5f13d69e</task-id>
<tool-use-id>toolu_01Dm7VxUd39u3rJSs3ECtiB6</tool-use-id>
<output-file>/private/tmp/claude-501/-Users-jyh-projects-claude-salt/ea81b992-0821-4192-8f48-c0dcdcbc14c2/tasks/a0a44798a5f13d69e.output</output-file>
<status>completed</status>
<summary>Agent "Lean 4 BitVec + hardware machinery" finished</summary>
<note>A task-notification fires each time this agent stops with no live background children of its own. The user can send it another message and resume it, so the same task-id may notify more than once.</note>
<result>Repo is clean of my scratch files. Here is the dossier.

---

# STATE OF BITVECTOR AND CIRCUIT REASONING IN LEAN 4 — August 2026

**Legend:** `[V-ME]` = I verified it by reading local source or running it on this machine. `[V-SRC]` = verified from a fetched primary source. `[INF]` = inference. `[?]` = unsure.

## 0. PINNED VERSIONS (salt) `[V-ME]`

- `/Users/jyh/projects/claude/salt/lean-toolchain` → `leanprover/lean4:v4.32.0-rc1`
- mathlib rev `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`, inputRev `v4.32.0-rc1`
- Deps: batteries, aesop, Qq, plausible, proofwidgets, importGraph, LeanSearchClient, Cli
- Toolchain source tree: `/Users/jyh/.elan/toolchains/leanprover--lean4---v4.32.0-rc1/src/lean/`
- **CaDiCaL ships inside the toolchain**: `~/.elan/toolchains/leanprover--lean4---v4.32.0-rc1/bin/cadical`. No external install needed.
- Other toolchains present locally: v4.31.0, v4.32.0, v4.32.1, v4.32.2, v4.33.0-rc1.

---

## 1. BitVec API SURFACE

### Representation `[V-ME]` — `Init/Prelude.lean:2359`

```lean
structure BitVec (w : Nat) where
  ofFin ::
  toFin : Fin (hPow 2 w)
```

It is a **`Fin (2^w)`**, which is itself a `Nat` + proof. The doc comment is explicit: *"This is represented as the underlying `Nat` number in both the runtime and the kernel, inheriting all the special support for `Nat`."* The design note in `Init/Data/BitVec/Basic.lean` says `Fin` was chosen "for its relative efficiency (Lean has special support for `Nat`)" over `List Bool`, `{l : List Bool // l.length = w}`, `Fin w → Bool`. Ops are modeled on SMT-LIB `QF_BV`.

Consequence that matters: **BitVec arithmetic is kernel-fast** (it bottoms out in GMP-accelerated `Nat.mul`/`Nat.mod`/`Nat.pow`), but each op costs a small constant multiple of a `Nat` op — structure projection + structure-eta + proof-irrelevance — not a single kernel primitive. `[V-ME rep, INF cost]`

### Where the API lives, and how big it is `[V-ME]`

`Init/Data/BitVec/` in **core**, not mathlib:

| File | theorems | defs |
|---|---|---|
| `Lemmas.lean` (258 KB) | **977** | 2 |
| `Bitblast.lean` (117 KB) | **165** | 21 |
| `Basic.lean` (29 KB) | 28 | **77** |
| `Bootstrap.lean` | 23 | 0 |
| `Folds.lean` | 5 | 1 |
| `Decidable.lean` | 2 | 0 |

**~1,200 theorems, ~100 defs, all in Lean core.** Plus `Init/Data/Ord/BitVec.lean`, `Init/GrindInstances/Ring/BitVec.lean`, `Init/Data/Range/Polymorphic/BitVec.lean`, and a simproc set at `Lean/Meta/Tactic/Simp/BuiltinSimprocs/BitVec.lean`.

**Mathlib adds almost nothing**: `Mathlib/Data/BitVec.lean` is **112 lines total** `[V-ME]` — `CommSemiring`/`CommRing` instances, `toNat_injective`/`toFin_injective`, `toFin_nsmul`/`toFin_zsmul`/`toFin_pow`, `ofFin_intCast`, and `equivFin : BitVec m ≃+* Fin (2^m)`. That is the entire mathlib BitVec story. Do not go looking for more.

### Key theorem families `[V-ME]`

- **`toNat`/`toFin`/`toInt` transfer** — `BitVec.toNat_eq : x = y ↔ x.toNat = y.toNat`, `toNat_add`, `toNat_mul`, … This is the bridge to `omega`.
- **`getLsbD` / `getElem` / `getMsbD` / `msb` bit-extraction laws** — the workhorse family. Every operation has a `getLsbD_&lt;op&gt;` characterization. This is how you do axiom-clean bit-level reasoning.
- **`Bitblast.lean` — the axiom-clean structural circuit theory.** These are the building blocks for hand-proving datapaths without a SAT solver: `carry`, `carry_succ`, `adcb`, `adc`, `adc_spec`, `add_eq_adc`, `getLsbD_add`, `msb_add`, `mulRec`, `mulRec_succ_eq`, `mul_eq_mulRec`, `getLsbD_mul`, `shiftLeftRec`, `shiftLeft_eq_shiftLeftRec`, `blastMul`/`denote_blastMul`, `DivModState` + `udiv_eq_of_mul_add_toNat`, `ult_eq_not_carry`, `ule_eq_carry`, `slt_eq_not_carry`, `sle_eq_carry`, `add_eq_or_of_and_eq_zero`, `bit_neg_eq_neg`.
- **`ofNat`/`ofInt`/`setWidth`/`signExtend`/`cons`/`concat`/`extractLsb'`/`append`/`replicate`/`reverse`/`clz`/`cpop`**.
- **Decidable quantifier instances** (§3 below).

### Simp sets `[V-ME]`

- **`bv_normalize`** — registered at `Lean/Meta/Tactic/BVDecide/Attr.lean:42`. `bv_decide`'s preprocessing set. Also `bv_normalize_proc` for simprocs. Usable standalone as the `bv_normalize` tactic.
- **`int_toBitVec`** — `Attr.lean:45`, "simp theorems used to convert UIntX/IntX statements into BitVec ones".
- **`bitvec_to_nat`** — the BitVec→Nat set. **`bv_toNat` no longer exists**; it was renamed. `[V-ME]` Consumed by:
  ```lean
  macro "bv_omega" : tactic =&gt; `(tactic| (try simp -implicitDefEqProofs only [bitvec_to_nat] at *) &lt;;&gt; omega)
  ```
  (`Init/Tactics.lean:1528`)
- `grind` has BitVec support: `grind ring`/`grind lia` handle `BitVec.ofNat` since v4.27; a parallel-prefix-sum bitblast circuit for `cpop` landed in v4.30. `[V-SRC]`

### Decidability `[V-ME]` — `Init/Data/BitVec/Decidable.lean`

`DecidableEq (BitVec w)` is hand-written in `Prelude.lean` (`BitVec.decEq`) so that bit-vector literals get builtin support. More importantly, **bounded quantifiers over `BitVec` are decidable**:

```lean
instance instDecidableForallBitVec : ∀ (n : Nat) (P : BitVec n → Prop) [DecidablePred P], Decidable (∀ v, P v)
instance instDecidableExistsBitVec : ∀ (n : Nat) (P : BitVec n → Prop) [DecidablePred P], Decidable (∃ v, P v)
```

built by bit-recursion through `forall_cons_iff`. The docstring itself warns: *"for large numerals the decision procedure may be very slow, and you should use `bv_decide` if possible."* Measured limits in §3.

---

## 2. `bv_decide` — THE CRITICAL FINDING

### ⚠️ IT IS **NOT** KERNEL-CHECKED. IT ADDS AN AXIOM. `[V-ME — measured on this machine, salt's exact toolchain]`

```
theorem probe (x y : BitVec 16) : (x ^^^ y) ^^^ y = x := by bv_decide
#print axioms probe
-- 'probe' depends on axioms: [propext, Classical.choice, Quot.sound, probe._native.bv_decide.ax_1_5]
```

**Any `bv_decide` call that actually reaches the SAT solver fails salt's iron rule 3.**

The mechanism (`Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:36-44`) `[V-ME]`:

```lean
let reflectionTerm := mkApp2 (mkConst ``verifyBVExpr) reflectedExpr certExpr
match (← nativeEqTrue `bv_decide reflectionTerm (axiomDeclRange? := (← getRef))) with
| .success auxProof =&gt;
    return mkApp3 (mkConst ``unsat_of_verifyBVExpr_eq_true) reflectedExpr certExpr auxProof
```

and `Lean/Meta/Native.lean` — module docstring, verbatim:

&gt; *"This module contains infrastructure for proofs by native evaluation (`native decide`, `bv_decide`). Such proofs involve a native computation using the Lean kernel, and then **asserting the result of that computation as an axiom** towards the logic."*

`nativeEqTrue` `addAndCompile`s an aux `def : Bool`, runs `unsafe evalConst Bool`, and on `true` calls `addDecl` on a fresh `Declaration.axiomDecl` of type `&lt;term&gt; = true`.

### What IS and ISN'T proven

| Layer | Status |
|---|---|
| Bitblaster correctness (`BVLogicalExpr.unsat_of_bitblast`) | **Proven in Lean** `[V-ME]` |
| AIG→CNF equisatisfiability (`AIG.toCNF_equisat`) | **Proven** |
| LRAT checker soundness (`LRAT.check_sound`, `verifyCert_correct`) | **Proven** |
| Glue (`unsat_of_verifyBVExpr_eq_true`) | **Proven** |
| **That `verifyBVExpr &lt;expr&gt; &lt;cert&gt;` actually evaluates to `true`** | **ASSERTED BY AXIOM** — compiled binary's word |
| CaDiCaL itself | **Not trusted** — its LRAT output is checked by the verified checker |

So: the *algorithm* is genuinely end-to-end verified. The *execution* of that algorithm on your particular certificate is not. The TCB is the Lean compiler + runtime, not the SAT solver.

### Axiom history `[V-SRC]`

| Version | Representation |
|---|---|
| v4.12.0 (first release, 2024-10) | `Lean.ofReduceBool` + `Lean.trustCompiler` |
| through v4.28.x | same |
| **v4.29.0+** | RFC #12216 / PR #12217: **one axiom per native computation**, named `&lt;decl&gt;._native.&lt;tactic&gt;.ax_&lt;n&gt;` |

`Lean.trustCompiler`, `reduceBool`, `reduceNat`, `ofReduceBool`, `ofReduceNat` still exist in `Init/Core.lean` but are **deprecated since 2026-02-01** `[V-ME]`. The rationale for the change (from the RFC) is directly relevant to you: per-computation axioms let an **external checker identify and independently re-discharge** these facts by naming pattern.

**Correction to circulating write-ups:** many sources (including LNSym-era commentary) still say "bv_decide emits `Lean.ofReduceBool`". That is **out of date**. On 4.29+ it is the per-invocation named axiom. `[V-ME]`

### There is no kernel mode `[V-ME]`

Full `BVDecideConfig` (`Std/Tactic/BVDecide/Syntax.lean`): `timeout (:= 10)`, `trimProofs`, `binaryProofs`, `acNf (:= false)`, `andFlattening`, `embeddedConstraintSubst`, `structures`, `fixedInt`, `enums`, `graphviz`, `maxSteps`, `shortCircuit`, `solverMode`. **Nothing about kernel evaluation.**

**`bv_check "proof.lrat"` does NOT escape this** `[V-ME]` — `BVCheck.lean` → `lratChecker` → the same `LratCert.toReflectionProof` → the same `nativeEqTrue`. It skips only the *solver call*.

### The ONLY clean `bv_decide` calls

When `bv_normalize` closes the goal by itself, no solver runs and no axiom appears `[V-ME]`:
```
theorem t1 (x y : BitVec 8) : x + y = y + x := by bv_decide   -- [propext]
theorem t2 (x : BitVec 32) : x &amp;&amp;&amp; x = x := by bv_decide      -- [propext, Quot.sound]
```
If you want those, **write them as `bv_normalize`** — that's what `bv_decide?` will tell you.

### SCALING — measured on this machine `[V-ME]`

Multiplier commutativity `x * y = y * x`, with AIG node counts and LRAT proof sizes:

| width | AIG nodes | LRAT steps (post-trim) | result | wall |
|---|---|---|---|---|
| 4 | 163 | 616 | proved | 3.2 s |
| 6 | 397 | 8,212 | proved | 1.0 s |
| 8 | 735 | 63,552 | proved | 1.7 s |
| 10 | 1,177 | 565,697 | proved | 13.4 s |
| **12** | 1,723 | — | **TIMEOUT (120 s)** | 138 s |
| 16 (default 10 s) | ~3,127 | — | **TIMEOUT** | — |

AIG growth is quadratic and harmless (~12.8·w²). **The cliff is CaDiCaL on multiplier circuits, and it is exponential.** 12-bit multiplier commutativity is already out of reach at a 120-second budget. Raising the timeout will not rescue 32/64-bit.

Structurally-easy but *wide* goals scale completely differently:

| goal | AIG nodes | LRAT steps | wall |
|---|---|---|---|
| 1024-bit `x+(y+z) = (x+y)+z` | **35,824** | **1,883,782** | **33 s** |
| 8-bit shift-and-add multiplier ≡ builtin `*` | 1,023 | 61,016 | 2.6 s |
| 256-bit add assoc, 64-bit shift/mask, 32-bit De Morgan | — | — | all &lt; 2 s |

**There is no bit-width cap.** The limit is (circuit structure × SAT hardness), not width. A 35k-node AIG with a 1.9M-step certificate is comfortably in range. Datapath *equivalence* checks — where two circuits share structure — are the easy case; *multiplier* identities are the hard case.

Defaults: SAT timeout **10 s**; multiplication bitblasted as **shift-and-add** (O(w²)), division as a **shift-subtractor** (O(w²)). `[V-SRC]`

### FRAGMENT COVERAGE — every row tested here `[V-ME]`

**Supported:**
- `BitVec`: `+ - * / % &amp;&amp;&amp; ||| ^^^ ~~~ &lt;&lt;&lt; &gt;&gt;&gt;`, `sshiftRight`, `rotateLeft/Right`, `extractLsb'`, `++`, `replicate`, `reverse`, `clz`, `cpop`, `zeroExtend`, `signExtend`, `ult/ule/slt/sle`, `getLsbD`
- `Bool` + full propositional structure; `∀` in the goal (auto-intro'd)
- **`UInt8/16/32/64`, `USize`, `IntX`** via the `fixedInt`/`int_toBitVec` pass — `example (x y : UInt32) : x + y = y + x := by bv_decide` ✅
- **`structure`s with BitVec/Bool fields** via `structures := true` — splits hypotheses and goals ✅ (tested with a two-field `St` record)
- **enum inductives** via `enums := true`
- `if-then-else` on BitVec equality ✅ (this is what makes memory modeling work — §6)

**NOT supported — hard failures:**
- **`Fin n`** ❌ — `(x : Fin 8) : x + 0 = x` → *"None of the hypotheses are in the supported BitVec fragment"*
- **`Nat`** ❌ — no Nat preprocessing at all. Use `bv_omega` for that boundary; it does **not** compose with `bv_decide`.
- **`Int`** ❌ (only fixed-width `IntX`)
- **Uninterpreted functions / congruence closure** ❌ — **this is the big one.** Tested:
  ```
  (f : BitVec 8 → BitVec 8) (h : x = y) ⊢ f x = f y
  -- error: The prover found a potentially spurious counterexample:
  -- It abstracted the following unsupported expressions as opaque variables: [f y, f x]
  -- x = 255#8, y = 255#8, f x = 255#8, f y = 127#8
  ```
  `f x` and `f y` become **independent, unrelated atoms**. No congruence axioms are added.
- **SMT theory of arrays** ❌ — array terms are opaque atoms.
- **`Vector` / `getElem` / `Vector.set`** ❌ — `(r.set 0 v)[0] = v` abstracted as an atom.
- **Quantifiers in hypotheses** ❌ — QF_BV only.

**Sound-but-incomplete failure mode:** when atom abstraction may have lost information, the error says *"potentially spurious counterexample"* and names the abstracted terms. It will not prove false things; it will silently weaken your goal if you don't read the message.

### THE PAPER `[V-SRC]`

**"Interactive Bitvector Reasoning using Verified Bit-Blasting"** — Henrik Böving, Siddharth Bhat, Luisa Cicolini, Alex C. Keizer, Léon Frénot, Abdalrhman Mohamed, Léo Stefanesco, Harun Khan, Joshua Clune, Clark W. Barrett, Tobias Grosser.
*PACMPL* **9(OOPSLA2)**:3259–3285, Oct 2025. **DOI `10.1145/3763167`** — https://dl.acm.org/doi/10.1145/3763167
- **No arXiv preprint exists.** Unpaywall lists ACM Gold-OA as the only OA location, and ACM 403s automated fetches. The paper body was not readable from here. `[?]`
- Artifact: Zenodo **`10.5281/zenodo.15762083`**; Docker `abdoo8080/oopsla25-bv-decide:v1`
- Claims: first end-to-end verified bitblaster in a dependently-typed ITP; SMT-LIB 2.7 coverage; **&gt;7,000 SMT statements extracted from LLVM** — "the largest mechanized verification of LLVM rewrites to date"; beats CoqQFBV.
- Eval suites: InstCombine (LLVM peephole), HackersDelight, SMT-LIB 2024 Competition (**46,191 benchmarks**, 20 min / 8 GB per job). Baseline appears to be **Bitwuzla** `[INF from script names]`.
- Talks: Lean Together 2025, Böving — https://www.youtube.com/watch?v=Q1LDavBJ94A ; OOPSLA'25 — https://www.youtube.com/watch?v=lV5fQyAmOLQ
- Predecessor: **LeanSAT** (github.com/leanprover/leansat) — **archived 2024-08-29**, merged into core as `Std.Tactic.BVDecide`, shipped in v4.12.0.
- SMT-LIB frontend: **Leanwuzla** — https://github.com/hargoniX/Leanwuzla (SMT-COMP 2025 entry; standings not retrieved `[?]`)

Companion, different tactic family: **"Certified Decision Procedures for Width-Independent Bitvector Predicates"** — Bhat, Stefanesco, Hughes, Grosser. PACMPL 9(OOPSLA2), **DOI `10.1145/3763148`**, artifact `10.5281/zenodo.16269885`. Automata-theoretic, **width-polymorphic** BV predicates; mechanizes k-induction and MBA-Blast; solves 100% of Hacker's Delight. Tactic family `bv_automata`, subproject **`Blase`** in lean-mlir.

### Soundness incidents

**None found for `bv_decide`.** `[V-SRC]` Historical bugs (#5543, #5664, #6043, #5699, #5674, #7475, #9309 the `acNf` looping-simp-set bug, #8306, #12406) are all incompleteness / crash / perf — the safe direction. `acNf` defaults to `false` because of #9309.

---

## 3. `decide` AT SCALE IN THE KERNEL

### What the kernel actually accelerates `[V-SRC, read from `src/kernel/type_checker.cpp`]`

`reduce_nat` handles **exactly 15 primitives**:
`Nat.succ` (arity 1); `Nat.add, Nat.sub, Nat.mul, Nat.pow, Nat.gcd, Nat.mod, Nat.div, Nat.beq, Nat.ble, Nat.land, Nat.lor, Nat.xor, Nat.shiftLeft, Nat.shiftRight` (arity 2).

- **`Nat.pow` is capped** at exponent `1&lt;&lt;24` = 16,777,216.
- `Nat.decEq`/`decLe`/`decLt` are *not* in the table but reduce to accelerated `Nat.beq`/`Nat.ble` plus one ι-step. Effectively accelerated.
- **`Nat.gcd` is defined by well-founded recursion** and would never reduce — but has a GMP primitive. Nice trap to know about.
- **NOT accelerated:** `Nat.blt`, `Nat.log2`, `Nat.testBit`, `Nat.bitwise`, `Nat.min/max`, `Nat.lcm`, `Nat.sqrt`.
- **No `UInt*`, `BitVec`, `Fin`, `Array`, `Float`, or `String` primitive exists in the kernel.** They are accelerated only *indirectly*, by bottoming out in `Nat`.
- **`Array α` IS `List α` in the logical model** (`structure Array (α) where mk :: toList : List α`). The folk advice "use `Array` not `List` for `decide` speed" is **wrong for kernel `decide`** and right only for `native_decide`.

### The three different limits `[V-SRC]`

1. **Elaborator**: `defaultMaxRecDepth := 512` (`Init/Prelude.lean:4827`).
2. **Kernel**: `g_kernel_rec_depth_factor = 16` (`src/runtime/interrupt.cpp`) → **kernel depth limit = `maxRecDepth × 16` = 8,192 by default.** Error: `(kernel) deep recursion detected`.
3. **C++ stack**: `lean --tstack=N` (lean-mlir ships `--tstack=400000`).
4. `maxHeartbeats` (default 200,000) bounds the **elaborator only** — which is why `decide +kernel` can succeed where plain `decide` dies.

### Measured numbers — MINE `[V-ME]`

| computation | tactic | axioms | wall |
|---|---|---|---|
| `(List.range 50000).all (Nat.blt · 50000)` | `decide` | none | 4.9 s |
| **65,536-case exhaustive BitVec-8 identity** (`x^^^y = (x\|\|\|y) &amp;&amp;&amp; ~~~(x&amp;&amp;&amp;y)`) | `decide` | `[propext, Quot.sound]` | **35 s** |
| 2,048-case **Vector**-backed register file read-over-write | `decide` | `[propext, Quot.sound]` | **2.4 s** |
| `∀ x y : BitVec 8, (x^^^y)^^^y = x` (2¹⁶, via `instDecidableForallBitVec`) | `decide +kernel` | clean | **12 s** |
| `∀ x y : BitVec 10` (2²⁰) | `decide +kernel` | clean | **8 m 19 s** |
| `∀ x y : BitVec 12` (2²⁴) | `decide +kernel` | — | **&gt;10 min, killed** |
| 2²⁰-case `List.range 1024` double loop | `decide +kernel` | clean | 10 min |

**Rule of thumb for salt: kernel `decide` is comfortable to ~10⁵ BitVec operations (seconds), painful at ~10⁶ (minutes), and dead by ~10⁷.** So exhaustive kernel checking covers a **16-bit input space** and no more.

### The best external datum `[V-SRC]` — mathlib Lucas–Lehmer

`Mathlib/NumberTheory/LucasLehmer.lean` + `Archive/Examples/MersennePrimes.lean`:
- ✅ `(2^4423 - 1).Prime` by kernel reduction, **"nearly instantly"**
- ❌ `2^9689 - 1` — `(kernel) deep recursion detected` (system-dependent; works locally, fails in CI)
- ❌ `2^11213 - 1` — fails everywhere

That is ~4,400 nested structural unfoldings, each a GMP square + mod on a 4,400-bit number, essentially free. **It is a *depth* limit, not a *work* limit.**

### Why `List`/`Fin`/`Finset`/`Decidable` blow up `[V-SRC]`

1. **Any `Nat` function you define yourself gets zero kernel help** — only the 15 primitives. The manual: *"The logical model of `Nat` is essentially a linked list, so addition would take time linear in the size of one argument. Still worse, multiplication takes quadratic time."*
2. **Each `Nat.rec` step costs one kernel recursion level** — a 20,000-element fold blows the 8,192 depth limit before it blows the clock.
3. **Well-founded recursion does not reduce in the kernel.** The recursive call sits under `WellFounded.fix`, whose `Acc.rec` major premise is an opaque proof that never reduces to `Acc.intro`. Mathlib says it flatly at `Nat.minFacAux`: *"This definition is by well-founded recursion, so `rfl` or `decide` cannot be used."*
4. **Tactic-built `Decidable` instances get stuck on `Eq.rec`.** The `decide` tactic's own diagnostic is the canonical explanation: *"Reduction got stuck on `▸` (`Eq.rec`), which suggests that one of the `Decidable` instances is defined using tactics such as `rw` or `simp`. To avoid tactics, make use of functions such as `inferInstanceAs` or `decidable_of_decidable_of_iff`."*
5. **The kernel has no reducibility annotations** — `@[irreducible]`/`@[reducible]` are elaborator-only. The kernel unfolds by definition *height*. This is why goals pass in the elaborator and fail in the kernel, and vice versa.
6. **Structure eta** costs `is_def_eq` on both types plus one per field, on every `Fin`/`BitVec`/`UInt*`/`Array`/`Subtype` comparison.
7. **2026 gotcha:** PR #14270 — under the module system, `deriving DecidableEq`-generated `decEq` is emitted non-`@[expose]`, so `decide`/`rfl` **stall across a module boundary**, *"there is no user-side workaround."* Still open. `[V-SRC]`

**The canonical blow-up anecdote** (lean4 issue #2552): the same 729-case goal `∀ a&lt;9, ∀ b&lt;9, ∀ c&lt;9, a²+b²+c² ≠ 7` succeeds quickly with `decidableBallLT` written using `match`, and **times out at 200,000 heartbeats** with the identical instance written using the `cases` tactic. `native_decide` is fast in both.

### `decide` mechanics and modes `[V-SRC]`

The emitted term is literally `of_decide_eq_true (rfl : decide p = true)` — **all work is done by the kernel checking `decide p =?= true`.**

- **default**: elaborator `whnf`s the instance, **throws the reduction away**, and emits the term for the kernel to redo. **The reduction genuinely happens twice.**
- **`decide +kernel`**: skips the elaborator pass entirely, uses `mkAuxLemma` (cached per module, kernel never re-checks). Ignores transparency, can unfold everything. Introduced as `decide!` in v4.14.0, renamed in v4.15.0 (PR #6016).
- **`decide +native`** ≡ `native_decide`.
- Also `+revert`, `+zetaReduce`.
- `Simp.Config.decide` defaults to **`false`** (it was `true` in early Lean 4).

### `native_decide` axioms today `[V-ME + V-SRC]`

Measured here: `#print axioms n1` → `[n1._native.native_decide.ax_1_1]` — **not** `ofReduceBool`. One bespoke axiom per computation, of type `decide p = true`.

**Known soundness incidents — all reproduce `False`** `[V-SRC]`:

| # | Date | Cause |
|---|---|---|
| #4306 | 2024-05-30 | `ConstFolding.lean` folded `UIntN.toNat` without modular reduction |
| #7434 | 2025-03-11 | `String.isEmpty` miscompiled in a shared library with `@[inline]` |
| **#7463** | 2025-03-12, **STILL OPEN** | **`@[csimp]` can smuggle axioms and `unsafe` into a proof** — axioms used to prove the csimp lemma are not propagated to `#print axioms` |
| #9439 | 2025-07-20 | `String.prev` runtime ≠ model |
| #10213 | 2025-09-02 | `@[csimp]` ignores universe parameters |
| #11773 | 2025-12-22 | `Array.foldlM` vs `foldlMUnsafe` diverge when `stop &gt; size` |

Every one is a model/implementation divergence in `@[extern]`/`@[implemented_by]`/`@[csimp]` — **not** a kernel bug. `@[csimp]` (#7463) is still an open hole. There is also a deliberate in-tree demonstrator: `tests/elab/nativeReflBackdoor.lean`.

### 🔑 `cbv` / `decide_cbv` — THE AXIOM-CLEAN ALTERNATIVE, new in v4.29 `[V-ME, verified on this machine]`

```
theorem c1 : ((List.range 256).all (fun a =&gt; let x : BitVec 8 := .ofNat 8 a; (x ^^^ x) == 0#8)) = true := by decide_cbv
-- 'c1' depends on axioms: [propext, Quot.sound]

theorem c2 : Nat.gcd 123456 7890 = 6 := by decide_cbv
-- 'c2' depends on axioms: [propext]
```

A **proof-producing symbolic call-by-value evaluator** (`Lean/Meta/Tactic/Cbv/Main.lean`, © 2026 Wojciech Różowski), built on `Lean.Meta.Sym.Simp`.

- **Only the three standard axioms.** No code-generator trust.
- **It reduces well-founded-recursive and partial-fixpoint definitions**, which kernel `decide` structurally cannot. Note `c2` above — `Nat.gcd` is WF-recursive.
- `@[cbv_eval]` lets you swap a quadratic definition for a linear one *inside the evaluator*; `@[cbv_opaque]` blocks unfolding.
- Config: `cbv.maxSteps := 100_000`, `cbv.warning := false`.
- Limitations: non-dependent rewriting only; does not enter binders; still flagged experimental.

**For salt this is the most important tactic in this dossier after `bv_decide` itself** — it is the only thing that gives native-ish reach with a clean axiom set.

### Making kernel `decide` feasible — sourced patterns `[V-SRC]`

1. **Certificates in `Nat`, using only the 15 primitives.** Lucas–Lehmer's `sModNat` is the exemplar: `%`, `^`, `+`, `-` and nothing else, *"specifically written to be reducible by the Lean 4 kernel."*
2. **Elaborate with compiled code, hand the kernel a `rfl`.** The `norm_num` extension pattern: a `meta def` runs compiled at elaboration time; the emitted proof is a `rfl` the kernel re-checks with GMP-accelerated ops. **Native speed without a native axiom.**
3. **Keep the structural definition for the kernel; register a tail-recursive `@[csimp]` twin for runtime.** Core's `Nat.decidableBallLT`: *"kernel reduction (`by decide`) is unaffected, as it uses the original structural definitions."*
4. **Never build `Decidable` instances with tactics.** Use `decidable_of_iff`, `inferInstanceAs`, or explicit `match`.
5. **Oversized `Nat` fuel arguments are free** if never forced — `Mathlib/Data/Num/Prime.lean`: *"it will get lazily evaluated during kernel reduction, so we will only require about `sqrt n` unfoldings."*
6. **Prefer `Bool` equalities** (`==`, `Nat.ble`) over `LE.le`/typeclass projections.
7. Raise `maxRecDepth` (kernel gets 16×) and `--tstack`.

### On the "kernel is ~100× slower" folklore

**Do not quote it — no measured Lean number was found.** `[V-SRC: absence confirmed]` The asymmetry is *structural*, not a constant factor: on the 15 primitives the kernel runs at essentially GMP speed (Mersenne 4423 instantly); off them it is unboundedly worse. Quote instead: **15 primitives**, **depth limit `maxRecDepth × 16` = 8,192**, and the **Mersenne 4423 ✅ / 9689 ❌** boundary.

---

## 4. HARDWARE / CIRCUIT / ISA LIBRARIES IN LEAN 4

**Headline: there is no mature Lean 4 hardware library.** Nothing comparable to Coq's Kôika or the ACL2 stack. The center of gravity is machine code and zk circuits, not RTL.

### LNSym — **FROZEN** `[V-SRC]`

https://github.com/leanprover/LNSym · Apache-2.0 · 116★ · AWS Automated Reasoning (Shilpi Goel) × Lean FRO.

**⚠️ Last push to `main`: 2024-12-09.** ~20 months stale. A July 2026 `upgrade-lean-versions` branch exists but main is untouched. 6 open PRs, newest substantive one from 2024-11. **Dormant, not archived.** Treat published LNSym claims as describing a 2024 artifact.

**The state model** (`Arm/State.lean`) — this is the transferable part:
```lean
abbrev Store α β := α → β                        -- a PLAIN FUNCTION
abbrev Memory := Store (BitVec 64) (BitVec 8)    -- memory is a TOTAL FUNCTION

structure ArmState where
  private gpr    : Store (BitVec 5) (BitVec 64)
  private sfp    : Store (BitVec 5) (BitVec 128)
  private pc     : BitVec 64
  private pstate : PState
  mem            : Memory
  program        : Program
  private error  : StateError

inductive StateField | GPR (_ : BitVec 5) | SFP (_ : BitVec 5) | PC | FLAG (_ : PFlag) | ERR
```
Accessors `r`/`w`, `read_gpr`/`write_gpr`, `read_mem_bytes`/`write_mem_bytes`.

**Separation algebra** (`Arm/Memory/Separate.lean`) — the design idea worth stealing:
```lean
def mem_legal' (a : BitVec 64) (n : Nat) : Prop := a.toNat + n ≤ 2^64

structure mem_separate' (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) : Prop where
  ha : mem_legal' a an
  hb : mem_legal' b bn
  h  : a.toNat + an ≤ b.toNat ∨ a.toNat ≥ b.toNat + bn

abbrev Memory.Region := BitVec 64 × Nat
def Memory.Region.pairwiseSeparate (mems : List Memory.Region) : Prop := mems.Pairwise Memory.Region.separate
```
**Functional memory + a `pairwiseSeparate` list-of-regions precondition, with all disjointness reduced to `Nat` linear arithmetic and discharged by `omega`.** That is the template.

**Tactics:** `sym_n 20` / `sym_n n at s` / `sym_n n (while := tac)` — pre-generated **step lemmas** per PC, then unfold `run`, introduce a fresh state var, apply the step lemma, simp away conditionals, decompose into axiomatic effects on state fields, aggregate. Plus `simp_mem` (read-over-write with ⟂/⊆ heuristics, side goals to `omega`), `mem_omega`, `CSE.lean`, `PruneUpdates.lean`.

**Verified programs:** SHA-512 (with checked-in `lrat_files/`), AES-GCM (`gcm_init_v8`, `AESHWCtr32EncryptBlocksProgram`), Popcount32, from AWS-LC via ELF loading.

**Trust:** relies on `bv_decide` → **fails salt's rule 3**. And **the ISA model itself is trusted-by-testing** — `make` runs randomized conformance testing against real Aarch64 hardware. Validation, not verification.

**Lineage confirmed:** Shilpi Goel is the primary author of ACL2's `x86isa`; LNSym reproduces that architecture (machine-state record + `step`/`run` interpreter semantics) in Lean. **No LNSym paper found** — her homepage lists none. `[V-SRC]`

**Important correction:** AWS's *shipping* Arm crypto verification uses **HOL Light + s2n-bignum** (John Harrison), **not** LNSym. LNSym is research-stage.

### Sparkle — the only substantial Lean 4 HDL, but calibrate hard `[V-SRC]`

https://github.com/Verilean/sparkle · Apache-2.0 · 102★ · created **2026-01-16**, pushed 2026-07-31, 1,032 commits. **Single author (Junji Hashimoto), 6.5 months old.**

Core semantics: **`Signal d α ≈ Nat → α`** — a signal is a function from discrete time steps to values under clock domain `d`. The Clash/Lava denotational model, so equivalences are ordinary Lean theorems. API: `Signal.pure/register/reg/memory/loop/atTime/circuit`, `BitPack`, `#synthesizeVerilog`, `#verify_eq`, `#verify_fpga`. Feedback only via explicit `register`/`loop`, so **unintended latches are impossible by construction**.

`Sparkle/Verification/` includes `Temporal.lean` (LTL: `always`/`eventually`/`next`/`Until` with safety/liveness induction), `Equivalence.lean` (27.7 KB), `RV32Props.lean` (12.9 KB), `PipelineProps`, `CDCProps`, `MulProps`.

**⚠️ THREE FLAGS:**
1. **`native_decide` is used** in `RV32Props.lean` alongside `bv_decide`. Disqualified under salt's rule 3.
2. **Scope is much narrower than the README.** "102 formal proofs for the RV32IMA SoC" means 102 lemmas about **encode/decode round-trips, opcode injectivity, field extraction, per-ALU-op algebraic identities, decoder control-signal routing**. There is **no pipeline or full-CPU correctness theorem.**
3. The TODO.md is candid about real problems: memcached synthesis *hangs*, `handleTupleProjections` burns 1.17 M ms across 4,816 calls, no architectural docs for the ~2,800-line compiler.

**Cite as "the most substantial Lean 4 HDL effort extant" — never as "a formally verified RISC-V SoC."**

Sister project: **hesper** (Verilean, verified GPU/WebGPU programming, 32★).

### Smaller efforts `[V-SRC]`

- **circuitlib** (matthunz, 11★, 2026-07-29) — AND/OR/NOT/NAND/NOR/XOR/XNOR, half adder, full adder. No muxes, latches, flip-flops, memory, or FSMs yet. Very early.
- **alok/koika-lean4** — the only Kôika→Lean effort. **A stub; README is `# koika`.**
- `frieszadam/formal-hdl` (toy), `j-arndt/samipe` (79-gate ARM CDE parity checker), `1509Chamma/TempoDAG`.

**No Lean port of Bluespec or Fe-Si.** Kôika remains Rocq. Notably the strongest recent hardware result in the neighborhood — "Interaction Tree Semantics for RISC-V" (arXiv:2605.04933, 2026-05), proving a Kôika ALU implements all R-type integer ops — **went to Rocq, not Lean.**

### AIG libraries

**`Std.Sat.AIG` in Lean core is the only one.** `[V-ME]` API: `AIG`, `AIG.Ref`, `AIG.Decl`, `AIG.Entrypoint`, `AIG.Cache` (+ `Cache.WF`), `AIG.Fanin` (gate/invert/flip), `RefVec`, `BinaryInput`/`TernaryInput`, `ShiftTarget`, `ExtendTarget`, `IsDAG`, `toGraphviz`; modules `Basic/CNF/Cached/CachedGates/If/LawfulOperator/LawfulVecOperator/RefVecOperator/Relabel/RelabelNat/Lemmas`. Structural hash-consing with proof-carrying `IsDAG`. `leansat` archived.

**Note:** `bv_decide` has a `graphviz := true` option that dumps the AIG to `aig.gv` — useful for inspecting a datapath's circuit structure. `[V-ME]`

### Sail → Lean, and RISC-V `[V-SRC]`

- **Sail's Lean backend exists**: `rems-project/sail/src/sail_lean_backend` (`pretty_print_lean.ml`, `sail_plugin_lean.ml`). **Not in any released Sail — build from git.**
- **Generated model**: https://github.com/opencompl/sail-riscv-lean — **175,877 lines, 4,779 definitions, 206 inductives, 0 errors, 0 warnings.** Full RISC-V spec, typechecks in Lean. Pushed 2026-08-04, alive. **No license file.**
- **⚠️ Stated limitation: the generated Lean is "neither executable nor polished in any way."**
- People: Grosser, Stefanesco (Cambridge); Galois; LindyLabs; with Sewell/Armstrong consulting. **Funded by the Ethereum Foundation's Verified zkEVM Project.**
- **MRiscX** (22★) — a certified RISC-V interpreter with Hoare logic `⦃P⦄ code ⦃Q⦄`, registers as `UInt64`. Pedagogical, "far from finished."
- **No x86 in Lean 4.** `[V-SRC negative]`
- **No WasmCert-Lean.** WasmCert is Isabelle+Coq. There is `T-Brick/lean-wasm` (31★, GPL-3.0) and a `LeanWasm` MSc thesis. A **Wasm SpecTec Lean 4 backend** reportedly exists and is "essentially complete" `[?]` — worth a direct check; would be the most future-proof route.

### EVM / Ethereum `[V-SRC]`

- **EVMYulLean** (NethermindEth, 92★) — executable formal EVM+Yul model, Cancun hardfork, runs the official Ethereum test suite. Gaps: gas, `CREATE`/`CREATE2`, `EXTCODESIZE`. Pushed 2025-11-19 (slowing).
- **Clear** (NethermindEth, 84★) — interactive Yul verification: Lean model + custom tactics + a **verification condition generator**.
- **KEVM→Lean: yes** — `runtimeverification/evm-equivalence`. K can generate Lean 4 from compiled K definitions; RV proves EvmYul ≡ KEVM-generated-Lean *in Lean*.
- Also: `revofusion/ETHCryptoLean` (all EVM precompile crypto primitives).

### 🔴 THE CAUTIONARY TALE — read this one `[V-SRC]`

**Ethereum Foundation zkEVM audit of `sp1-lean`, 2026-05-20** — https://zkevm.ethereum.foundation/blog/sp1-fv

`succinctlabs/sp1-lean` proves SP1 Hypercube's RV64 chip constraints against the Sail RISC-V model extracted to Lean. It announced **62 opcodes**. The independent audit found **only 51 have complete correct proofs**:
- **The SLTI theorem is VACUOUSLY TRUE** — contradictory hypotheses from a copy-paste error.
- **LH, LHU, LW, LWU were proved against *byte-load* semantics** instead of half/word-load — wrong specifications, proved correctly.
- **LUI, AUIPC, LD have no theorems at all.**
- All load theorems depend on unfinished sign-extension lemmas; 5 completeness proofs are deferred skeletons; 4 explicit axioms.
- Several findings surfaced by an **LLM-assisted audit**.

(To sp1-lean's credit it *did* find a real bug: **JALR** must compute `(rs1 + imm) &amp; ~1`; SP1 omitted the LSB clear. Patched in SP1 v6.1.0.)

**This is the best public evidence anywhere that statement auditing is not optional** — a "verified" announcement that audited down by 18%, with a vacuous theorem and four mis-specified ones. Directly relevant to salt's refuter discipline.

Methodology counterpart worth citing: **Cedar's Verification-Guided Development** — arXiv:**2407.01688**, FSE Companion '24, DOI `10.1145/3663529.3663854`. Executable Lean model + mechanized proofs + differential random testing against production Rust + PBT. **4 bugs found via the proofs, 21 more via DRT/PBT.** Cedar is a policy language, not hardware — but `cedar-lean/Cedar/Thm/SymCC/` is a **verified symbolic compiler from policies into SMT terms** (`Opt.lean` alone is 67.9 KB), which is the one technically transferable piece.

### Other `[V-SRC]`

- **lean-smt** (ufmg-smite, 304★, pushed 2026-08-05, **alive**) — `smt` tactic; cvc5 **proof reconstruction** (not a verified checker); paper arXiv:**2505.15796**, CAV 2025, DOI `10.1007/978-3-031-98682-6_11`. Theories: UF, LIA/LRA with quantifiers, **bitvectors experimental**. **Caveat: cvc5 proofs may contain holes, surfacing as leftover Lean goals.** Since it produces a real term, a *closed* `smt` proof is kernel-clean.
- **lean-cvc5** (abdoo8080, 25★, pushed 2026-08-04) — FFI bindings, ships artifacts for all platforms. Plus forks `anzenlang/lean-cvc5`, `anzenlang/cvc.lean`.
- **lean-auto** (182★) — arXiv:2505.14929, CAV 2025. Duper backend reconstructs via a verified checker; Z3/cvc5/Zipperposition backends are **trusted**.
- **SampCert** (leanprover, 102★) — verified discrete Laplace/Gaussian samplers, deployed in AWS Clean Rooms DP. arXiv:2412.01671. **Not bitvector-relevant** — its whole point is avoiding bit-level implementations.
- **LRAT-Catcher** — Szeider, arXiv:**2607.00815** (2026-07-01). Imports DIMACS+LRAT into a Lean theorem, reusing `Std.Tactic.BVDecide.LRAT`. **Gives real kernel-vs-native numbers: `decide +kernel` took 245 s on a 22 KB certificate** ("impractical for larger instances"); native reflection did Schur S(4)=44 in 77 s / 8.9 GB (628 MB cert) and R(4,4)=18 in 83 min / 188 GB. Also composes cube-and-conquer runs inside Lean. **PBLean** (arXiv:2602.08692) does the same for VeriPB pseudo-Boolean certificates.
- **BitModEq** — Pertseva, Robert, Barrett, Parker, arXiv:**2605.15163** — verified translations from finite fields to bitvectors; solves 19% more ZKP arithmetization benchmarks than SOTA SMT.
- **Aeneas** (Rust→Lean) — used by **Microsoft SymCrypt** to port their crypto library to verified Rust; SHA-3 and ML-KEM released.
- **Clean** (Verified-zkEVM, MIT, **171★, 4,577 commits, pushed 2026-08-06**) — an embedded Lean DSL for zk circuits (AIR/PLONK/R1CS). The closest thing in Lean 4 to a mature circuit DSL with a real soundness/completeness discipline. Type names unconfirmed `[?]`.
- **CircuitProver** — arXiv:**2607.27259** (2026-07-29). Chisel→Lean 4 semantic models; **first benchmark for agentic hardware theorem proving: 63 parameterized Chisel tasks** including XiangShan and Rocket multipliers/dividers. No public artifact found.
- **Float**: Lean's native `Float` is **opaque to the kernel** — you cannot prove anything about it by `rfl`/`decide`. Alternatives: **Flean** (all 5 IEEE rounding modes + error bounds), **FloatSpec** (Flocq port — **but its own docs admit many modules are shape-only with `sorry` placeholders**), **ryu-lean4**.
- **SVIL 2026** (Software Verification in Lean, Paris, 2026-04-20; Beneficial AI Foundation + Lean FRO + Cryspen) — de Moura on `SymM`/`grind`, Son Ho on SymCrypt, Bhargavan on crypto. **Zero hardware/ISA/machine-code talks.** The community's 2026 attention is on Rust, crypto, and specs — not silicon.

---

## 5. SSA / COMPILER IR — `lean-mlir`

https://github.com/opencompl/lean-mlir · **255★, 2,863 commits, last push 2026-07-28** `[V-SRC]`
- Toolchain: **`leanprover/lean4:nightly-2025-12-01`**, mathlib `nightly-testing-2025-12-01`. **Not on a stable release** — that's a real integration cost.
- 9,449 `.lean` files, 20.4 MB. Build flag `--tstack=400000`.
- **The README is stale**: `SSA/Core` no longer exists; the core is now a separate Lake package at **`LeanMLIR/LeanMLIR/`** (55 files, 0.5 MB). The 14.6 MB `SSA/Projects/InstCombine` is auto-generated corpus.

**Paper:** Bhat, Keizer, Hughes, Goens, Grosser, *"Verifying Peephole Rewriting in SSA Compiler IRs"*, **ITP 2024**. arXiv:**2407.03685**; proceedings DOI **`10.4230/LIPIcs.ITP.2024.9`** (LIPIcs 309, art. 9; free PDF at drops.dagstuhl.de). Talk: LLVM Dev 2024 — https://www.youtube.com/watch?v=4lh2NnLOxvQ. Playground: https://lean-mlir.grosser.es

### Core datatypes `[V-SRC, read from source]`

```lean
structure Dialect where (Op : Type) (Ty : Type) (m : Type → Type := Id)
class TyDenote (β : Type) : Type 1 where toType : β → Type          -- ⟦x⟧
structure Ctxt (Ty : Type) where ofList :: toList : List Ty
def Ctxt.Var (Γ : Ctxt Ty) (t : Ty) := { i : Nat // Γ[i]? = some t } -- de Bruijn + proof
def Ctxt.Valuation (Γ : Ctxt Ty) := ⦃t : Ty⦄ → Γ.Var t → toType t
inductive EffectKind | pure | impure

mutual
inductive Expr : (Γ : Ctxt d.Ty) → EffectKind → (ty : List d.Ty) → Type where
  | mk (op) (ty_eq) (eff_le) (args : HVector (Var Γ) …) (regArgs : HVector … (Com t.1 .impure t.2))
inductive Com : Ctxt d.Ty → EffectKind → List d.Ty → Type where
  | rets (vs : HVector Γ.Var tys) : Com Γ eff tys
  | var  (e : Expr Γ eff ty) (body : Com (ty ++ Γ) eff β) : Com Γ eff β
end

inductive Lets (Γ_in) (eff) : (Γ_out) → Type where   -- the snoc-list dual, for zipper rewriting
  | nil | var (body) (e : Expr d Γ_out eff t)
```
Plus `HVector`, `Signature`/`DialectSignature`/`DialectDenote`, `Zipper`, `Refinement` (`⊑`), `ConcreteOrMVar` (bit-width metavariables), a full MLIR-syntax parser + EDSL quotations.

**Note:** `Com` is **multi-result** — indexed by `List d.Ty`, not a single `Ty`. Essential for hardware (a `fork` has 2 outputs).

### Denotation and `simp_peephole` `[V-SRC]`

`Com.denote`/`Expr.denote`/`Lets.denote` are a mutual interpreter into `eff.toMonad d.m`. `simp_peephole` is a **macro**, not a bespoke elaborator:
```lean
macro "simp_peephole" loc:(location)? : tactic =&gt;
  `(tactic|( first | rw [funext_iff (α := Ctxt.Valuation _)] $[$loc]?
                   | change ∀ (_ : Ctxt.Valuation _), _ $[$loc]? | skip
             simp (config := {failIfUnchanged := false}) only
               [Expr.denote_castPureToEff, simp_denote] $[$loc]? ))
```
i.e. make the `Valuation` quantification explicit, then blast with the **`simp_denote`** set (~60 lemmas: `Com.denote_var/rets`, `Expr.denoteOp`, `HVector.denote`, all Ctxt/Valuation plumbing, monad laws, `liftEffect_rfl`, `cast_eq`), plus a `dsimproc simpHVectorGet` for `Fin`-numeral indices. Net effect: the framework vanishes and you get a pure semantic obligation like `(w : Nat) (X Y : BitVec w) ⊢ LLVM.xor (LLVM.sub X X) Y ⊑ Y`.

**Documented gotcha:** `Com.denote_var` only applies if `d.m` is known lawful — check `LawfulMonad d.m` is synthesizable first.

### Rewriting kernel `[V-SRC]`

```lean
structure PeepholeRewrite (Γ : List d.Ty) (ts : List d.Ty) where
  lhs rhs : Com d (.ofList Γ) .pure ts
  correct : lhs.denote = rhs.denote

theorem denote_rewritePeepholeAt (pr) (pos) (target) : (rewritePeepholeAt pr pos target).denote = target.denote
```
Plus `multiRewritePeephole`, `rewritePeepholeRecursively`, `DialectMorphism`, `Transforms/CSE.lean`, `Transforms/DCE.lean`. **Axiom-guarded in-tree**: `#guard_msgs in #print axioms denote_rewritePeepholeAt` → `[propext, Classical.choice, Quot.sound]`.

### 🔑 Someone already built the circuit dialect — `SSA/Projects/CIRCT/` `[V-SRC]`

This directly answers your "could it be reused for a datapath?" — **yes, and it has been:**

- **`Comb/Comb.lean`** — the CIRCT combinational dialect verbatim: `Ty | bitvec (w : Nat)`, `TyDenote := BitVec w`, ops `add/and/or/xor/mul` **with variadic arity** (`${List.replicate n (Ty.bitvec w)} → Ty.bitvec w`), `divs/divu/mods/modu`, `extract (w)(n) : bv w → bv (w-n)`, `replicate : bv w → bv (w*n)`, `mux : (bv w, bv w, bv 1) → bv w`, `icmp`, `parity`, `shl/shlPar/shrs/shru/sub`. **This is a typed SSA datapath IR with width-indexed types and width-changing ops.**
- **`Stream/Basic.lean`** — `def Stream (β) := Stream' (Option β)` (infinite stream of *potential* values, `none` = bubble), with `corec`, `transpose`.
- **`Register/Basic.lean`** — **sequential state and feedback**: `compReg (input : Stream α) (initialValue : α) : Stream α` ("we ignore the `clk` operand under the assumption that one clock cycle corresponds to one step in the `Stream`") and `register_wrapper`, explicitly modeled on **traced monoidal categories**.
- **`Handshake/`, `DC/`, `DCPlus/`, `HandshakeToDC/`, `HandshakeToHW/`** — dataflow components as stream functions, plus **verified lowering passes between hardware abstraction levels**, using the same `PeepholeRewrite` machinery.

**What you get free:** intrinsically-typed SSA with proof-carrying de Bruijn variables; multi-result ops; variadic ops; width-indexed *and* width-polymorphic types; regions for hierarchy; effects via `Dialect.m` + `EffectKind`; a machine-checked rewriting kernel; CSE/DCE; MLIR frontend and pretty-printer.

**What's missing:**
1. **No loops in `Com`** — straight-line let-chain only. Iteration must be a region-carrying op; `Scf` gives **bounded** `for_` and `iterate k`. No `while`, no fixpoint, no general recursion. (Deliberate — ITP'24 §6.2.)
2. **No CFG, no φ-nodes, no basic blocks.** Structured regions only.
3. **State is not in the IR.** Two in-tree idioms: (a) `Dialect.m := StateT S _` (SLLVM) — forces everything `.impure` and drags monadic reasoning into every proof; (b) **put time in the type**, `TyDenote τ := Stream (BitVec w)` — what CIRCT does, keeps everything `.pure`, `simp_peephole` works cleanly. **(b) is the right choice for a datapath.**
4. **Regions are forced `.impure`** in `Expr.mk`, with a long TODO about effect-polymorphic denotation.
5. Rewriting is **fuel-driven**, not fixpoint-to-convergence.
6. **No timing/clock domains** — `compReg` bakes in "one clock cycle = one stream step".
7. **`DecidableEq` on `Op` is expensive** for large ISAs — `RISCV64/Base.lean` sets `maxHeartbeats 1000000000000000000` and `maxRecDepth 10000000000000` just to `deriving DecidableEq`.

Other dialects: **LLVM/arith** (with `def LLVM.IntW w := PoisonOr (BitVec w)` — yes, `IntW` is exactly that, and `NoWrapFlags{nsw,nuw}`/`ExactFlag`/`DisjointFlag` are op parameters), **SLLVM** (stateful: `EffectM := StateT GlobalState PoisonOr`, ops `ptradd/load/store/alloca`), **RISCV64** (RV64I+M+B as SSA), **LLVMRiscV** (mixed-dialect instruction selection, evaluated against real LLVM bug reports), **Scf**, **FHE**, **Blase** (arbitrary-width BV automata), **Medusa** (rewrite generalization).

**Activity read `[INF]`:** the *core framework is stable/quiescent*; active work is in `Blase` and `CIRCT`. Most recent hardware commit: 2026-04-17 "feat: Handshake-to-HW `fork` circuit (#1925)" (Luisa Cicolini).

---

## 6. MEMORY MODELING — WHAT ACTUALLY WORKS

I tested the candidates directly. `[V-ME]`

### Option A: total function on a BitVec index (LNSym style) — ✅ BEST for `bv_decide`

```lean
abbrev RF := BitVec 3 → BitVec 8
def wr (f : RF) (i : BitVec 3) (v : BitVec 8) : RF := fun j =&gt; if j = i then v else f j
```
All three canonical laws go through with `unfold wr; bv_decide`:
- read-over-write same index ✅
- read-over-write different index ✅
- **write-over-write commutation at a probe point** ✅ (needed the SAT solver; `[propext, Classical.choice, Quot.sound, wow._native.bv_decide.ax_1_5]`)

**Why it works:** `f i`, `f j`, `f k` become opaque BitVec *atoms* (fine — you never need congruence on them), and the `if _ = _ then _ else _` structure on BitVec equality **is** in the supported fragment. This is exactly why LNSym uses `Store α β := α → β` and not a HashMap.

**The catch:** you must **probe at a specific index**. There is no extensional `f = g` reasoning inside `bv_decide` (no array theory), so state-equality lemmas need `funext` + a per-index `bv_decide`, or LNSym's `StateField`-indexed `r`/`w` discipline.

### Option B: `Vector (BitVec w) n` — ✅ BEST for kernel `decide`, ❌ for `bv_decide`

- **`bv_decide`: FAILS.** `(r.set 0 v)[0] = v` → *"abstracted the following unsupported expressions as opaque variables: [(r.set 0 v ⋯)[0]]"*. No `getElem`/`Vector.set` support.
- **kernel `decide`: EXCELLENT.** 2,048-case exhaustive register-file check in **2.4 s**, axioms `[propext, Quot.sound]`.

So `Vector` is the right choice when you're going the exhaustive-`decide` route, and the wrong choice when you're going the SAT route.

### Option C: structures with BitVec fields — ✅ works with `bv_decide`

The `structures := true` pass splits records into fields automatically, in both hypotheses and goals. Tested with a two-field `St` record — went through. This is the natural way to model a **fixed-size** register set or pipeline stage.

### Option D: `Std.HashMap` / finite maps — ❌ don't

Not in the `bv_decide` fragment; not kernel-friendly. Nobody does this. LNSym explicitly chose a plain function instead.

### Recommendation

**For a small SRAM / register file:**
- **Model:** `BitVec addrWidth → BitVec dataWidth` (a plain function), updated by `fun j =&gt; if j = i then v else f j`. Fixed-size architectural state as a `structure` of `BitVec` fields.
- **Disjointness:** LNSym's `mem_separate'` / `Memory.Region.pairwiseSeparate` pattern — push all address reasoning into `Nat` linear arithmetic and discharge with **`omega`** (axiom-clean).
- **Bit-level obligations:** `bv_decide` if you accept the axiom; **`decide_cbv`** or exhaustive `decide` on a ≤16-bit input space if you don't; hand-proof via `Init/Data/BitVec/Bitblast.lean` (`adc_spec`, `mulRec`, `getLsbD_*`) if you need clean *and* wide.
- **For sequential logic**, if you go the lean-mlir route: put time in the type (`Stream (BitVec w)`), not in a state monad.

---

## 7. BOTTOM LINE FOR SALT

1. **`bv_decide` violates iron rule 3.** Verified on salt's exact toolchain: any solver-reaching call adds `&lt;thm&gt;._native.bv_decide.ax_*`. `bv_check` does not escape it. There is no kernel mode. The only clean calls are ones `bv_normalize` closes alone — write those as `bv_normalize`.
2. **`decide_cbv` is the tactic to know.** New in v4.29, verified here as `[propext, Quot.sound]`, and it reduces well-founded recursion that kernel `decide` structurally cannot.
3. **Exhaustive kernel `decide` covers a 16-bit input space** (2¹⁶ in ~12 s), is painful at 2²⁰ (~8 min), and dead at 2²⁴.
4. **`bv_decide`'s real limit is SAT hardness, not width.** 1024-bit adder associativity: 33 s. 12-bit multiplier commutativity: timeout. Datapath *equivalence* is easy; multiplier *identities* are not.
5. **No uninterpreted functions, no congruence, no arrays, no `Nat`/`Fin`/`Int`.** Everything must be unfolded to fixed-width `BitVec`/`Bool` first.
6. **The Lean 4 hardware lane is thin.** LNSym frozen since 2024-12; Sparkle is single-author and uses `native_decide`; every deep hardware result nearby went to Rocq. The transferable asset is **lean-mlir's `Com` + the CIRCT dialects**, and **LNSym's step-lemma + functional-memory + `omega`-separation template**.
7. **Two methodology citations worth their weight:** the **EF's sp1-lean audit** (62 claimed opcodes → 51 real; one *vacuously true* theorem; four proved against the wrong specification) and **Cedar's verification-guided development** (4 bugs from proofs, 21 from differential testing). The first is the strongest public argument for the refuter pass that exists.

**Open gaps I could not close:** the OOPSLA'25 paper body (ACM hard-403s automated fetch; no arXiv, no mirror); SMT-COMP 2025 QF_BV standings for the Leanwuzla entry; whether the Wasm SpecTec Lean 4 backend is really "essentially complete"; `Clean`'s exact type names.</result>
<usage><subagent_tokens>159651</subagent_tokens><tool_uses>53</tool_uses><duration_ms>2194219</duration_ms></usage>
</task-notification>
