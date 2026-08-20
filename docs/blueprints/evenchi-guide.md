# The even-χ ground — blueprint guide

**Charter.** The even-character companion to the odd-χ massif: at an even real
primitive Dirichlet character, route the class-number/cyclotomic-unit fulcrum
through the sine product to an **integrality jump**, and land the floor
`L(1,χ) ≥ 2·log φ / √q` as a kernel theorem. This is the E-ladder's even wing;
its conclusion feeds the ladder at **E5** (`even_trace_cosh`).

**Provenance.** Statement ratified by the Captain at the 2026-08-19 council
sitting (Fable seated), amended from the v2 §1 draft by exactly one hypothesis
(`hprim`) on math's own forward-audit evidence. This guide written the same
sitting, per iron rule 5 (blueprint pen is Fable/human-tier). The design record
lives in the seat: `2026-08-17-math-E4a-design-block-v2.md` (the statement's
four type-level decisions) and `2026-08-19-math-evenchi-port-plan.md` (the
module split and its measured cone). Source of truth for the mathematics until
the port completes: the custody brief
`2026-08-18-math-E4a-probe1-unit-route.lean` (seat-tracked, 174 top-level
declarations, axiom-clean).

⚠️ `scripts/blueprint_lint.py` audits only the Brun guide; docs↔code checks for
this ground are **manual**, as for explicit12.

## The statement of record (iron rule 1 applies from here)

```lean
theorem exists_int_add_inv_sin_prod {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q)
    (hprim : χ.IsPrimitive)
    (heven : χ (-1) = 1)
    (hsum : ∑ a : ZMod q, χ a = 0)
    (e : ℕ → ℤ) (he : ∀ a, (e a : ℝ) = -χ a) :
    ∃ T : ℤ, (∏ a ∈ Finset.Ioo 0 q, (2 * Real.sin (Real.pi * a / q)) ^ (e a))
           + (∏ a ∈ Finset.Ioo 0 q, (2 * Real.sin (Real.pi * a / q)) ^ (e a))⁻¹ = T
```

Do not alter this statement to make a proof go through (iron rule 1). The four
type-level decisions (χ over ℝ; `hsum` in `Finset.univ` form; ℤ-exponents via
`(e, he)` as zpow; `hprim` present because the proved route is primitive-bound
through the Fourier identity and `gaussSum_normSq_of_primitive`) are ratified
design, recorded with their reasons in the v2 block.

**Why the integrality jump matters** (the ground's one-sentence why): over ℝ,
`2·cosh y > 2` is compatible with `2 + ε` for every ε; integrality turns `> 2`
into `≥ 3` — a gap, not an epsilon — and that gap is the floor's whole source.

## Node catalog — the port (dependency order, from the measured plan)

| # | node / module (`Salt/MR/…`) | content | ~decls | class | status |
|---|---|---|---|---|---|
| 1 | `EvenChiCosh` | the cosh/golden apparatus (the integrality jump) | 11 | B | ✅ in tree, audited, EXIT=0 |
| 2 | `EvenChiSine` | the `2 sin` ↔ `‖1−ζ^a‖` bridge | 14 | B | ✅ in tree, audited, EXIT=0 |
| 3a | `EvenChiAlgebra` | generic algebra beneath η: fibre swaps, the descent spine, associates, primitive-root exponents | **23** | B | ✅ in tree, audited, EXIT=0 |
| 3b/5/9 | `EvenChiEta` (one unit) | the `𝓞_K` layer → η → the ruled statement → **the ground** | **35** | B/C | ✅ **in tree, audited, EXIT=0 — `e4a_L1_lower_even [3 axioms]` and `exists_int_add_inv_sin_prod [3 axioms]` are IN THE CORPUS.** 35 not 29: five declarations are reached by TYPECLASS INSTANCE RESOLUTION and are invisible to any textual cone, plus one their own closure pulled in. |
| 4 | `EvenChiSign` | the ℤ sign map (`E4aChiBridge`) + fibre swap | **17** | B | ✅ in tree, audited, EXIT=0 |
| 5 | *(merged)* | culmination + η-norm | — | B | ✅ **MERGED INTO ROW 3b/5/9** — it is not a separate deliverable; the `𝓞_K` chain is indivisible. |
| 6 | `EvenChiTau` | τ real + magnitude at even real primitive χ | **7** | B | ✅ in tree, audited, EXIT=0 |
| 7 | `EvenChiRingBridge` | ℝ→ℂ transport (`ringHomComp`; helm-ruled ℝ-up) | **13** | B | ✅ in tree, audited, EXIT=0 |
| 8 | `EvenChiMiddle` | E3's Fourier identity → the real sine product; the crux `e4a_norm_add_inv_int` | **14** | B | ✅ in tree, audited, EXIT=0 |
| 9 | *(merged)* | E5a join + the floor + **the ground** `L(1,χ) ≥ 2·log φ/√q` | — | B | ✅ **MERGED INTO ROW 3b/5/9** — there is no `EvenChiFloor.lean`; the ground landed inside `EvenChiEta`. |
| 10 | `EvenChiControls` | the four mutation controls + `e4a_gaussSum_odd_re_zero` — the corpus's own non-vacuity witnesses | ~12 | B | ⬜ **APPROVED 21:0x (helm), at math's argument** |

**⚖️ PORT-RULE AMENDMENT (helm, 2026-08-19 21:0x, at math's argument):** negative controls
and non-vacuity witnesses **PORT** — only superseded routes and dead ends stay in custody. The
original §2 classed mutation controls as droppable scaffolding; **that classification was
wrong: a mutation control is not scaffolding, it is the evidence that a hypothesis is
load-bearing**, and the corpus should carry it. They land LABELLED, with a module docstring
naming what each refutes, so no reader mistakes a control for a theorem about the mathematics.
⇒ **Row 10 below.**

Port rules (from the plan, binding): root every module in `Salt/MR/All.lean`
(the track aggregate — executor-open; `saltworks/SaltWorks.lean` is maestro-only
and not involved) · **a module is done when the corpus's instruments SEE it** —
`#audit_axioms` lines in `All.lean` for every declaration, membership in the
default build graph, zero warnings introduced · the measured cone (122) is a
**lower bound** — the port keeps typeclass instances whatever the textual cone
says · development scaffolding (~25–30 decls: mutation controls, odd-companion
lemmas, superseded routes) is **dropped from the port, not deleted** — it stays
in the custody brief as the negative-control and refutation record.

## Frontier

- **Open:** modules 3, 5–9 of the port (№4 landed 16:2x; №3 re-measured at ~29
  algebraic declarations, NOT the bulk — 74 of the 103 remaining have no
  `K`/`𝓞_K` in their cone). Honest cost from the plan: not a single sitting,
  though the 16:2x re-measure shrinks it.
- **Consumer:** E5 (`even_trace_cosh`) consumes the spine once №9 lands.
- **No open class-C/D mathematics remains on this ground** — the mathematics is
  proved in custody; what remains is porting under the membership disciplines
  above.

## History (one line each)

E4a spine discharged in custody 08-18→19 (92→174 decls, every landing
first-or-second attempt) · piece (2) τ-real proved by helm executor 08-19
07:47, grafted 10:17 · the join `e4a_middle_re_join` 08-19 11:0x · statement
ratified with `hprim` 08-19 ~11:5x · ground landed in custody
(`L(1,χ) ≥ 2 log φ/√q`, 3 axioms) 08-19 14:2x · modules 1–2 in tree the same
afternoon.
