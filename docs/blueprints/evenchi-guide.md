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
    (hsum  : ∑ a : ZMod q, χ a = 0)
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
| 3 | `EvenChiCyclotomic` | the cyclotomic-unit machinery (fibres, mirror swap, units index, assembly) | **~29** | B/C | ⬜ — **RE-MEASURED 16:2x: NOT the bulk. 74 of the 103 remaining declarations have NO `K`/`𝓞_K` anywhere in their cone; only ~29 touch the algebraic layer.** |
| 4 | `EvenChiSign` | the ℤ sign map (`E4aChiBridge`) + fibre swap | **17** | B | ✅ in tree, audited, EXIT=0 |
| 5 | `EvenChiEta` | culmination + η-norm | ~20 | B | ⬜ |
| 6 | `EvenChiTau` | τ real + magnitude at even real primitive χ | 9 | B | ⬜ |
| 7 | `EvenChiRingBridge` | ℝ→ℂ transport (`ringHomComp`; helm-ruled ℝ-up) | 17 | B | ⬜ |
| 8 | `EvenChiStatement` | index transport + discharge + **the statement of record** | ~13 | B | ⬜ |
| 9 | `EvenChiFloor` | middle-closed + E5a join + nonvanishing + **the ground** `L(1,χ) ≥ 2·log φ/√q` | ~15 | B | ⬜ the objective |

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

- **Open:** modules 3–9 of the port (the bulk is №3's ~70 cyclotomic
  declarations). Honest cost from the plan: not a single sitting.
- **Consumer:** E5 (`even_trace_cosh`) consumes the spine once №9 lands.
- **No open class-C/D mathematics remains on this ground** — the mathematics is
  proved in custody; what remains is porting under the membership disciplines
  above.

## History (one line each)

E4a spine discharged in custody 08-18→19 (93→174 decls, every landing
first-or-second attempt) · piece (2) τ-real proved by helm executor 08-19
07:47, grafted 10:17 · the join `e4a_middle_re_join` 08-19 11:0x · statement
ratified with `hprim` 08-19 ~11:5x · ground landed in custody
(`L(1,χ) ≥ 2 log φ/√q`, 3 axioms) 08-19 14:2x · modules 1–2 in tree the same
afternoon.
