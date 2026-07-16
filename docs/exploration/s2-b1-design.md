# S2-B1 DESIGN FREEZE — the weight no-go atlas (WeightNoGo)

**Status: FROZEN (house, 2026-07-17 ~03:25) — PENDING GATE.**
Recon: S2-B1-RECON adjudicated PLACEABLE (ledger). House source
verification pre-freeze: the `p1PrimeSum` grep (every occurrence is
def / nonneg / split / the LARGE side of `p1RazorValue ≤ p1PrimeSum`
— no operating-point lower bound exists in the corpus; the only `0 <`
fact is the toy-point `p1_carrier_inhabited` at x=35, disclaimed by
TwinDeficit.lean:91), the heavy vanishing triple
(TwinDeficit.lean:200/207/214), the split (:175), the y-capped
decorations (WeightTrivia.lean:133/278/286).

## The theorem

The three landed decorations (`omegaLe y`, `sqStrip y`, `tripleT y`)
all read only prime-factor structure **at or below y**. A window
prime and a heavy semiprime (p·q, y < p,q) are therefore
decoration-identical — both read (0,0,0). Consequence: the
**impostor** — same four carrier-row values, all P₂ mass poured into
E2, twin mass zero — satisfies every constraint the corpus certifies.
So no certificate Φ reading the row values can lower-bound the twin
mass by anything positive. That absence-of-a-p₁-row IS the theorem.

## Frozen Lean statements

### File 1 — `Salt/Chen/WeightNoGo.lean` (imports: `Salt.Chen.TwinDeficit` ONLY)

The constraint predicate — FROZEN VERBATIM (the recon's seven-row
audit, spelled as twelve clauses; parametric in the row-bound
constants so the certificate may be granted every cap):

```lean
/-- The corpus-certified constraint set on the six observables
    (a₁, a₂, a₃, s, p₁, e₂). See the enumeration table in
    docs/exploration/s2-b1-design.md — the gate checked it complete. -/
def Feasible (A₁lo A₁hi A₂hi A₃hi Shi : ℝ)
    (a₁ a₂ a₃ s p₁ e₂ : ℝ) : Prop :=
  A₁lo ≤ a₁ ∧ a₁ ≤ A₁hi ∧
  0 ≤ a₂ ∧ a₂ ≤ A₂hi ∧
  0 ≤ a₃ ∧ a₃ ≤ A₃hi ∧
  0 ≤ s ∧ s ≤ Shi ∧
  0 ≤ p₁ ∧ 0 ≤ e₂ ∧
  p₁ + e₂ ≤ a₁ ∧
  a₁ - a₂ / 2 - a₃ / 2 - s / 2 ≤ p₁ + e₂
```

Design notes (binding): the mass cap `p₁ + e₂ ≤ a₁` is INCLUDED —
this is the GAP-U erratum's trivial bound (`p2Ind ≤ 1` term-by-term),
granted to the certificate on purpose: the no-go survives it by
construction. The razor VALUE floor (`XW/200 ≤ razor LHS`) is NOT a
clause — it is derivable from clauses 1/4/6/8 at the certified
constants (that derivation is the landed `p2RazorLHS_ge_of_certs`).

```lean
/-- The impostor: same rows, twin mass zeroed, all P₂ mass in E2. -/
theorem impostor_feasible {A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂ : ℝ}
    (h : Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂) :
    Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s 0 (p₁ + e₂)

/-- THE FLAGSHIP. Any certificate reading only the four carrier-row
    values, valid over the corpus-certified feasible set, certifies
    NOTHING: its guaranteed twin mass is ≤ 0.  Note the quantifier
    order: Φ is bound AFTER the row-bound constants, so Φ may encode
    every certified constant freely — the theorem still kills it. -/
theorem no_readable_certificate {A₁lo A₁hi A₂hi A₃hi Shi : ℝ}
    (Φ : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hΦ : ∀ a₁ a₂ a₃ s p₁ e₂,
      Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂ →
      Φ a₁ a₂ a₃ s ≤ p₁) :
    ∀ a₁ a₂ a₃ s p₁ e₂,
      Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂ →
      Φ a₁ a₂ a₃ s ≤ 0
```

Proof route (frozen): apply `hΦ` at the impostor; `impostor_feasible`
supplies the hypothesis; the conclusion reads `Φ … ≤ 0` because the
impostor's p₁-slot is literally `0`. Expected ≤ 10 lines total.

The III.3″ schematic witness — FROZEN, hand-checked at freeze
(all twelve clauses; razor floor hit at EQUALITY — the worst case):

```lean
example : Feasible 1 (21/20) 1 1 1
    1 (199/300) (199/300) (199/300) 0 (1/200) := by
  norm_num [Feasible]
```

Hand-check: 1 ≤ 1 ≤ 21/20 ✓; 0 ≤ 199/300 ≤ 1 (×3) ✓; 0 ≤ 0,
0 ≤ 1/200 ✓; mass cap 0 + 1/200 ≤ 1 ✓; razor
1 − 3·(199/300)/2 = 1 − 199/200 = 1/200 ≤ 0 + 1/200 ✓ (equality).
A twin-void configuration sits exactly ON the certified razor floor.

### File 1, continued — the realization and the affine corollary

```lean
/-- N0 — the corpus realizes Feasible: the LANDED sums at the
    operating parameters satisfy every clause, with the same
    hypothesis package as p2RazorLHS_ge_of_certs (mirror it
    verbatim), A₁hi instantiated reflexively (a₁ ≤ a₁), and the
    mass-cap clause via the NEW small lemma
    p2PrimeSum ≤ A1primeSum (p2Ind ≤ 1 pointwise) + the split. -/
theorem corpus_feasible … :
    Feasible mainA1 (A1primeSum x P) mainA2 mainA3 stripBd
      (A1primeSum x P) (omegaPrimeSum x P y) (triplePrimeSum x P y)
      (stripPrimeSum x P y) (p1PrimeSum x P) (e2PrimeSum x z P)
```

(Exact hypothesis spelling is the executor's to mirror from
`p2RazorLHS_ge_of_certs` at TwinDeficit.lean:431 — statement content
above is frozen; hypothesis names/order are not. If a cap clause
needs a different reflexive instantiation, widen the PARAMETER, never
the clause.)

```lean
/-- N1 — the affine family reads exactly the four rows. -/
noncomputable def readableAffineWeight (c₀ c₁ c₂ c₃ : ℝ) (y m : ℕ) : ℝ :=
  c₀ + c₁ * (omegaLe y m : ℝ) + c₂ * tripleT y m + c₃ * (sqStrip y m : ℝ)

theorem affine_carrier_identity … :
    (∑ Λ·keep·readableAffineWeight c₀ c₁ c₂ c₃ y)   -- spelled at the
      = c₀ * A1primeSum x P + c₁ * omegaPrimeSum x P y   -- landed carrier
      + c₂ * triplePrimeSum x P y + c₃ * stripPrimeSum x P y

/-- Corollary: the registered class — arbitrary real coefficients —
    certifies nothing (instantiate no_readable_certificate at the
    affine Φ). -/
theorem no_affine_certificate …
```

The carrier sum in `affine_carrier_identity` is spelled over the SAME
index set and weight (`Λ·keep`) as `A1primeSum` (Assembly.lean:143) —
pure `Finset.sum_add_distrib` + `mul_sum`. `chenWeightA α` must be a
definitional instance (`c₀=1, c₁=c₂=c₃=−α`) — state that as a `rfl`
or `simp` lemma, `readableAffineWeight_chenWeightA`.

### File 2 — `Salt/Chen/WeightEscape.lean` (imports: `Salt.Chen.TwinDeficit`)

```lean
/-- N3 — the FULL decoration algebra is blind, pointwise. -/
noncomputable def readableWeight (f : ℝ → ℝ → ℝ → ℝ) (y m : ℕ) : ℝ :=
  f (omegaLe y m : ℝ) (tripleT y m) (sqStrip y m : ℝ)

theorem readableWeight_heavy (f) {y p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hyp : y < p) (hyq : y < q) :
    readableWeight f y (p * q) = f 0 0 0
theorem readableWeight_window_prime (f) {y p : ℕ} (hp : p.Prime)
    (hyp : y < p) : readableWeight f y p = f 0 0 0
-- The two point-types every readable weight cannot separate.
theorem readableWeight_blind (f) … :
    readableWeight f y (p * q) = readableWeight f y p'
```

Heavy side: reuse the landed vanishing triple. Prime side: NEW small
lemmas (`omegaLe`/`sqStrip` at a prime > y vanish since
`primeFactors p = {p}` filtered by `≤ y` is empty; `tripleT` at a
prime is 0 since a prime is not a 3-almost-prime) — B-grade, derive
in-file.

```lean
/-- N4 — the escape: the MULTIPLICITY count above y separates. -/
def bigOmegaGt (y m : ℕ) : ℕ :=
  ∑ p ∈ m.primeFactors.filter (fun p => y < p), m.factorization p

theorem bigOmegaGt_prime {y p : ℕ} (hp : p.Prime) (hyp : y < p) :
    bigOmegaGt y p = 1
theorem bigOmegaGt_heavy {y p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hyp : y < p) (hyq : y < q) : bigOmegaGt y (p * q) = 2
-- NOTE: p = q allowed — the heavy-square corner is COVERED by the
-- multiplicity count (factorization p² p = 2). See the case table.
```

Docstring (frozen content, prose): `bigOmegaGt` is the minimal
decoration the impostor cannot survive (it reads 1 at the window
prime, 2 at every heavy E2 point) — and the carrier row it would
need, a LOWER bound on the heavy-semiprime mass, is exactly GAP-E
(the B2 census's named missing theorem; parity-sensitive). The
escape is the name of where twin progress must come from, not a
route. NO claim beyond the two equalities is stated in Lean.

## The constraint enumeration (execution clause 3 — case-space at freeze)

THE COMPLETE LIST of corpus facts about the six observables, each
dispatched. The gate's charge #1 is to check this table COMPLETE
(grep every lemma mentioning p1PrimeSum / e2PrimeSum / p2PrimeSum /
A1primeSum / omegaPrimeSum / triplePrimeSum / stripPrimeSum /
p2RazorLHS / p1RazorValue and verify it lands in a row below).

| Corpus fact | Disposition |
|---|---|
| `p2PrimeSum_split` (p₂ = p₁ + e₂) | ABSORBED — p₂ eliminated; clauses 11/12 written in p₁+e₂ |
| `razor_reduction` (razor LHS ≤ p₂) | clause 12 |
| `hA1` row (mainA1 ≤ a₁) | clause 1 |
| `hA2`/`hA3`/`hstrip` rows (upper) | clauses 4/6/8 |
| carrier nonnegativity (each sum ≥ 0) | clauses 3/5/7/9/10 |
| `p2Ind ≤ 1` mass cap (the erratum bound) | clause 11 (granted!) |
| a₁ upper cap (a1up — NOT landed; parked option (c)) | clause 2, PARAMETRIC; realization reflexive |
| `p2RazorLHS_ge_of_certs` (XW/200 ≤ razor) | DERIVABLE from 1/4/6/8 at certified constants — excluded |
| `deficit_floor_of_certs` | DERIVABLE (rows + hE) — excluded |
| `p1_razor_reduction` / `p1RazorValue_eq` | clause-12 rearrangements — excluded |
| `hE` error bundle | instantiation data inside the constants — excluded |
| toy-point inhabitations (x=35: p₁ > 0, e₂ > 0) | EXCLUDED WITH REASON: toy parameters, not the operating point (TwinDeficit.lean:91 disclaims); gate confirms no op-point p₁ lower bound exists |
| heavy vanishing triple / chenWeight pointwise | pointwise, not constraints on the six reals — feed N3, not Feasible |

Impostor closure, clause-by-clause (frozen check): clauses 1–8
untouched (a-values fixed); 9 becomes 0 ≤ 0; 10 becomes 0 ≤ p₁+e₂
(sum of 9,10); 11 becomes 0+(p₁+e₂) ≤ a₁ (was clause 11); 12's RHS
is the unchanged sum. No clause detects the move.

The N4 case table (m-shapes of the E2-above-y mass + the target):

| m-shape | omegaLe/sqStrip/tripleT | DISTINCT count >y | MULTIPLICITY count >y |
|---|---|---|---|
| window prime p (> y) | (0,0,0) | 1 | **1** |
| heavy pq, p ≠ q | (0,0,0) | 2 | **2** |
| heavy p² | (0,0,0) | 1 — **FAILS to separate** | **2** |

⇒ the distinct-count variant is REJECTED at freeze; `bigOmegaGt`
(multiplicity) is the frozen escape. (The enumeration catching the
p² corner before dispatch is clause 3 doing its job.)

## III.3″ slot witnesses (both frozen as landing requirements)

1. **Schematic** (in-file `example`, hand-checked above): the
   twin-void point ON the razor floor — parameters (1, 21/20, 1, 1,
   1), values (1, 199/300, 199/300, 199/300, 0, 1/200), clause 12 at
   equality.
2. **Operating-point** (= N0 `corpus_feasible`): the landed sums
   satisfy Feasible under the certified package; combined with the
   landed `deficit_floor_of_certs`, the impostor's E2 mass lives in
   the band [XW/200, XW·a1up] ≈ [0.005·XW, 1.0216·XW] — the
   erratum's ~200× inflation, used correctly (VALUE level, not mass
   level).

## Nodes & dispatch

| Node | Class | File | Content | Est. |
|---|---|---|---|---|
| N2 (flagship) | **C** | WeightNoGo.lean | Feasible + impostor_feasible + no_readable_certificate + the schematic witness | 120k |
| N0 | B | WeightNoGo.lean | corpus_feasible (+ the small p2PrimeSum ≤ A1primeSum lemma) | 60k |
| N1 | B | WeightNoGo.lean | readableAffineWeight + affine_carrier_identity + no_affine_certificate + the chenWeightA instance | 60k |
| N3 | B | WeightEscape.lean | readableWeight + heavy/prime pointwise + readableWeight_blind | 70k |
| N4 | B | WeightEscape.lean | bigOmegaGt + the two separation equalities + the GAP-E docstring | 80k |

EXEC-1 (Opus): N2 → N0 → N1 sequentially (one file, ~240k).
EXEC-2 (Opus): N3 → N4 sequentially (one file, ~150k).
Both dispatch ONLY on gate GO. No `.All` imports. Ceremony per
landing. Zeno tripwire armed per clause 2: any node terminating
with a new one-more-supplier residual on the same chain twice → HALT.

## Honesty / R4 (binding on all docstrings and the report)

The theorem covers every certificate readable from the y-CAPPED
decoration data — candidates (a), (b), (c) — fully. It says NOTHING
about decorations reading above y; that region is open and is
exactly the parity barrier / GAP-E. Every Lean conclusion is an
upper cap (Φ ≤ 0) or an equality of readings; no twin-prime-adjacent
existence claim appears anywhere (R4 clear). The honest headline:
"no y-capped decoration certificate certifies P₁; the minimal escape
is the above-y factor count, whose carrier is GAP-E."

## Gate charge (adversarial, Opus, BEFORE any executor)

1. **Enumeration completeness**: run the grep sweep; every corpus
   fact on the six observables lands in the table (included /
   derivable / excluded-with-reason) — any missed constraint that
   the impostor VIOLATES kills the design.
2. **Closure audit**: re-derive impostor_feasible clause-by-clause
   independently; check the quantifier-order claim (Φ after
   constants) actually yields the strength asserted.
3. **Vacuity probes**: the schematic witness arithmetic; whether
   corpus_feasible's hypothesis package is satisfiable at the
   certified constants (the GAP-U failure mode — check the
   INSTANTIATED clauses are not mutually contradictory).
4. **The trap re-run**: confirm the design never compares e2lo
   against a1up at the MASS level (the erratum's vacuity); the
   deficit reading must stay at the razor VALUE.
5. **The escape's honesty**: the p² corner handling; that
   bigOmegaGt_heavy at p = q is genuinely covered by the stated
   p*q form (it is: take q = p); that the GAP-E tie cites the B2
   census's terminal statement precisely.

*Frozen by the house session 2026-07-17. The statements above are
frozen content; executors may adjust names/hypothesis-spelling only
where the text explicitly says so. Statement changes: house/human
only (iron rule 1).*

## GATE VERDICT (2026-07-17 ~04:30): GO-WITH-AMENDMENTS — applied here

S2-B1-GATE (Opus, ≈ 139k / 11 tools): NO TEAR — all five charges
PASS on substance; the impostor violates no unconditional corpus
constraint. Three amendments, applied as APPENDMENTS (the frozen
body above is unchanged, per the transparent-amendment protocol):

- **A1 (enumeration completeness).** The pre-freeze grep was
  Salt/Chen/-scoped; the gate's repo-wide sweep found
  Salt/TwinBar/TwinDoor.lean carries three p1PrimeSum facts. NEW
  DISPOSITION ROW for the constraint table:
  `twinTypeII_eventually_pos` (:231), `twin_survivor_of_pos`
  (:204), the `TwinTypeII` def (:184), the :192 toy re-export →
  EXCLUDED WITH REASON: all gated on `TwinTypeII`, a class-D
  premise that implies TwinPrimeConjecture itself — not a corpus
  certificate; the impostor lives in a world where TwinTypeII
  fails and violates nothing. The substantive claim (NO
  unconditional operating-point p₁ lower bound anywhere in Salt/)
  is CONFIRMED repo-wide by the gate.
- **A2 (N4 route, binding on EXEC-2).** Prove bigOmegaGt_heavy
  UNIFORMLY: heavy_semiprime_factors (TwinDeficit.lean:190) → the
  filter keeps ALL of primeFactors → cardFactors_eq_sum_pf
  (WeightTrivia.lean:320) → cardFactors_mul +
  cardFactors_apply_prime. NO p = q case split (the frozen
  statement is unchanged; p = q is covered by instantiation).
- **A3 (N1 hint, binding on EXEC-1).** readableAffineWeight_chenWeightA
  is a ring-closed lemma, NOT rfl (sub vs +neg are not defeq).
- **W-mirror ruling (gate charge 1):** Feasible and the flagship
  are abstract over six reals — the W-carriers are covered by
  instantiation; NO separate Feasible needed. corpus_feasible_W is
  OPTIONAL post-landing, not a node.

EXEC-1 (N2 → N0 → N1, WeightNoGo.lean) and EXEC-2 (N3 → N4,
WeightEscape.lean) DISPATCHED on this verdict.
