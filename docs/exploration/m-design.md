# THREAD M — the minimal parity-breaking input / separation-game master

**Frozen at adjudication by M-GATE (2026-07-16).**  Verdict: **GO-WITH-BLOCK**.
Design recon: pilot.md 2026-07-18 ~23:40 (M-R0 ADJUDICATED).  This file is the
frozen statement block + node briefs the M-wave executors build against.  It
supersedes the M-R0 recon on every point where the two disagree (four binding
BLOCKS below).

**This is EXPLORATION, not a frozen blueprint node.**  M-thread files add NEW
work only (a new `Salt/TwinBar/Separation.lean` + wiring), edit no landed file,
are sorry-free / axiom-clean.  Every OPEN mathematical gap is prose or a named
`Prop`, never a `sorry`'d theorem.

---

## 0. The gate's verdict in one paragraph

The M-thread ships a genuine, non-vacuous, **organizing** theorem: a single
tolerant separation lemma (`wall_of_indistinguishable`) that RE-DERIVES two of
the three landed walls — W3 (`no_readable_certificate`) and W2 (`parity_wall`)
— as literal instances, probe-verified end-to-end by the gate against the built
oleans (both instances compile with NO extra hypotheses; the content lives in
the landed decoy objects `impostor_feasible`, `sieveAgree_pair`,
`siftedSum_sPlus`, all axiom-clean).  It does **not** produce new twin-prime
progress: the only proven implication to twins is the ALREADY-LANDED door
`twinB_min_implies_twins`, whose premise `TwinB_min` is class-D open.  The
M-thread is a UNIFICATION/atlas result, and must be framed as exactly that.

The gate's probe: `wall_of_indistinguishable` (tolerant, 3-line proof) applied
with `cap = siftedSum`, decoy `= sPlus x` yields **exactly** `parity_wall`'s
`Φ (sMinus x) ≤ 2 + 2·B`; applied with `B = 0`, decoy `= the impostor`, cap `=
the p₁-slot` yields **exactly** `no_readable_certificate`'s `Φ … ≤ 0`.  Compiled
clean, EXIT 0.

---

## 1. THE FOUR BINDING BLOCKS (corrections to the M-R0 recon — non-negotiable)

**BLOCK 1 (charge 2 — the master is TOLERANT, not equality).**  `SieveAgree`
(ParityWall.lean:414) is a 5-clause relation — three exact equalities
(`prodPrimes`, `nu`, `totalMass`) **plus a shared remainder budget `B`** on both
sieves — and the W2 certificate is controlled only to within `2·B`
(`|Φ s − Φ t| ≤ 2·B`).  The equality-shaped master the recon probe-compiled
(`R u = R w → m w ≤ 0 → valid Φ → Φ (R u) ≤ 0`) covers **only the `B = 0`
corner** (W3).  The frozen master is the tolerant form in §2.  The equality form
survives only as a named `B = 0` corollary used for W3's packaging.  The parity
content of W2 lives precisely in the budget `B` and the `λ ↦ −λ` involution — do
not state a master that cannot see it.

**BLOCK 2 (charge 3 — δ₀ is a per-instance parameter, not one number).**  The
three "critical strengths" are three DIFFERENT numbers in different roles:
W3's `1/200` (the razor's certified margin `XW/200`, `deficit_floor_of_certs`),
W1's `1/log 2 − 1 ≈ 0.4427` (the ε-enlargement threshold,
`no_twin_weight_enlarged`), and W2's `LambdaSummatory` rate `A > 2` (a whole
family, no single δ₀).  `δ₀` is a per-instance *role* ("the strength above which
the decoy breaks"), NOT a shared quantity.  **No Lean statement may assert the
three are equal or "commensurable as one parameter."**  `walls_are_dual` (§2.4)
is parametric per instance; the shared-role reading is PROSE.

**BLOCK 3 (charge 4 — the 0.614 "price tie" is definitional, → prose).**
`δ₀·(wall value) = (1/log 2 − 1)·(2·log 2) = 2 − 2·log 2 ≈ 0.614` is the
ε-enlargement threshold equation `2·(1+δ₀)·log 2 = 2` rearranged — a ring-trivial
identity the gate closed with `field_simp` alone.  It is INTERNAL to W1 (both
sides are W1 quantities); it does NOT tie W1 to W2/W3.  It may appear as a single
decorative `example` (norm_num/field_simp) for color, and as a prose remark ("the
enlargement radius and the value gap are the same W1 number in two units"); it is
**never load-bearing and never framed as a cross-wall coincidence.**

**BLOCK 4 (charge 1 structural — W1 is NOT an indistinguishability instance;
downgrade the headline).**  W1 (`no_twin_weight`) is a Cauchy–Schwarz *ceiling*
(`J₁+J₂ ≤ 2·log 2·I₂`, and `2·log 2 < 2`), structurally NOT an "R u = R w"
separation — it does not instantiate `wall_of_indistinguishable`.  W1 is the
`decoy_survives_below_radius` leg (the enlarged wing survives for δ < δ₀).  So
"THE THREE WALLS ARE ONE LP GAME" overstates.  The honest headline:
**two indistinguishability walls (W2, W3) share the tolerant master; W1 is the
threshold/enlargement leg; the door is the input-breaks-wall leg.**  Three
logically-distinct lemmas with a shared narrative — say so.

---

## 2. The frozen statement block

New file `Salt/TwinBar/Separation.lean`, `namespace Salt.TwinBar.Sep`,
`open Salt.Chen Salt.TwinBar`.  All statements below are gate-verified to compile
(the two instance derivations were probe-built end-to-end against the landed
oleans).

### 2.1  M1 — the master (TOLERANT) + the equality corollary

```lean
/-- **The tolerant separation master.**  `agree` bakes in the budget `B`
(equality is the `B = 0` corner).  If a decoy `w` is reading-indistinguishable
from a target `u` at budget `B`, the certificate `Φ` is `2·B`-tolerant under
`agree`, and `Φ` is valid at the decoy (`Φ w ≤ cap w`), then the certificate at
the target is capped by the decoy's ceiling plus the tolerance: `Φ u ≤ cap w +
2·B`.  Three-line proof — trivial as pure logic; ALL content is in the instances'
landed `agree`/`cap` witnesses. -/
theorem wall_of_indistinguishable
    {C : Type*} (agree : C → C → Prop) (Φ cap : C → ℝ) (B : ℝ) (u w : C)
    (hagree : agree u w)
    (htol : ∀ a b, agree a b → |Φ a - Φ b| ≤ 2 * B)
    (hvalid : Φ w ≤ cap w) :
    Φ u ≤ cap w + 2 * B
-- proof: `have h := htol u w hagree; rcases abs_le.mp h with ⟨h1, _⟩; linarith`
```

The `B = 0` corollary (the shape W3 uses — `Φ` factors through a reading `read`,
the decoy's ceiling is `≤ 0`):

```lean
/-- The equality corner of the master: `Φ` reads only `read`, `read u = read w`,
the decoy's ceiling is `≤ 0`  ⟹  `Φ (read u) ≤ 0`. -/
theorem wall_of_indistinguishable_eq
    {C R : Type*} (read : C → R) (Ψ : R → ℝ) (cap : C → ℝ) (u w : C)
    (hread : read u = read w) (hvalid : Ψ (read w) ≤ cap w) (hcap : cap w ≤ 0) :
    Ψ (read u) ≤ 0
```

### 2.2  M2 — the W3 instance (re-derives `no_readable_certificate`)

The deliverable is the SAME statement as the landed `no_readable_certificate`,
proved **as an application of the master** (demonstrating instancehood).  Gate
probe compiled this exactly:

```lean
/-- W3 as an instance of the master (`B = 0`, decoy = the impostor, cap = the
p₁-slot).  Byte-identical conclusion to `Salt.Chen.no_readable_certificate`. -/
theorem no_readable_certificate_via_master {A₁lo A₁hi A₂hi A₃hi Shi : ℝ}
    (Φ : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hΦ : ∀ a₁ a₂ a₃ s p₁ e₂,
      Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂ → Φ a₁ a₂ a₃ s ≤ p₁) :
    ∀ a₁ a₂ a₃ s p₁ e₂,
      Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂ → Φ a₁ a₂ a₃ s ≤ 0
-- Config = ℝ⁶; agree u w := (first four coords equal); cap = the p₁ slot;
-- decoy w = (a₁,a₂,a₃,s,0,p₁+e₂) via `Salt.Chen.impostor_feasible`; B = 0.
```

### 2.3  M3 — the W2 instance (re-derives `parity_wall`)

Same statement as the landed `parity_wall`, proved as an application of the
master.  Gate probe compiled this exactly:

```lean
/-- W2 as an instance of the master (cap = `siftedSum`, decoy = `sPlus x`,
target = `sMinus x`, budget = `B`).  Byte-identical conclusion to
`Salt.TwinBar.parity_wall`. -/
theorem parity_wall_via_master (x : ℕ) (hx : 2 ≤ x) (D : ℕ) (B : ℝ)
    (hplus : Salt.Chen.rosserRemainder (sPlus x) (D : ℝ) ≤ B)
    (hminus : Salt.Chen.rosserRemainder (sMinus x) (D : ℝ) ≤ B)
    (Φ : BoundingSieve → ℝ)
    (htol : ∀ s t, SieveAgree s t D B → |Φ s - Φ t| ≤ 2 * B)
    (hcert : ∀ s, Φ s ≤ s.siftedSum) :
    Φ (sMinus x) ≤ 2 + 2 * B
-- hagree : SieveAgree (sMinus x) (sPlus x) D B := ⟨rfl, rfl, rfl, hminus, hplus⟩
-- cap = fun s => s.siftedSum;  rw [siftedSum_sPlus x hx];  linarith.
```

### 2.4  M4 — `walls_are_dual` (the honest organizing statement)

A `structure` capturing the shared separation shape, with **per-instance**
radius (BLOCK 2 — no shared δ₀), plus the observation that each indistinguishable
wall follows from M1.  This is ORGANIZATIONAL: it proves nothing beyond
M1+instances.

```lean
/-- The shape shared by the two indistinguishability walls (W2, W3).  `radius`
is per-instance (BLOCK 2).  `wall` is derivable from `wall_of_indistinguishable`
for any inhabitant — the structure just records the data. -/
structure IndistWall where
  C : Type
  agree : C → C → Prop
  Φcap  : (C → ℝ) → Prop          -- the admissible certificate class (valid + tolerant at B)
  radius : ℝ                       -- this wall's own δ₀ (1/200 for W3; the A>2 family for W2)
  -- fields witnessing a decoy indistinguishable from a target with sub-radius mass
```

The frozen `walls_are_dual` is the pair of instances (`W2inst`, `W3inst`) + a
lemma `each_indist_wall_from_master : ∀ (w : IndistWall) …, <the wall conclusion>
follows from wall_of_indistinguishable`.  **`walls_are_dual` MUST NOT contain any
equation between the three radii.**  W1 is NOT an `IndistWall` instance (BLOCK 4).

### 2.5  M5 — the door leg + the decoy leg + the R4 open board

Both re-export LANDED, axiom-clean theorems as the two remaining master legs:

```lean
/-- `input_breaks_wall` (W2): the LANDED door.  An input to `TwinB_min` at
distributional strength walks through the wall to twins. -/
theorem input_breaks_wall : TwinB_min → TwinPrimeConjecture :=
  twinB_min_implies_twins                       -- Salt.TwinBar.TwinDoor, class B, LANDED

/-- `decoy_survives_below_radius` (W1): the LANDED enlarged wing survives (the
no-go persists) strictly below the enlargement radius δ₀ = 1/log 2 − 1. -/
theorem decoy_survives_below_radius {δ : ℝ} (hδ : 0 < δ)
    (hthr : (1 + δ) * Real.log 2 < 1) : ¬ ∃ F, … :=
  no_twin_weight_enlarged hδ hthr               -- Salt.TwinBar.Enlarged, LANDED
```

The **R4 open board** — class-D, STATED-NOT-ATTEMPTED as named `Prop`s or prose,
NEVER `sorry`'d (these are the ONLY routes to actual twin progress; all open):
- `TwinB_min` (= `TwinTypeII`) — the door's premise (flagship Challenge 2).
- **GAP-E** — the below-`y` decoration's escape carrier (`bigOmegaGt`'s missing
  lower bound on heavy-semiprime mass; `TwinDeficit.hE2lo`-shaped).  Parity-hard.
- **TwinLambda** — fixed-shift Chowla `Σ λ(n)λ(n+2) = o(x)` + the λ→Λ transfer.

---

## 3. Node briefs (estimates sanity-checked by the gate)

The gate has already probe-built M1, M2, M3 end-to-end (they compile clean).  The
executor work is transcription + wiring, so the recon's "~300k for M1+M2+M3" is
GENEROUS.  Revised:

| Node | Content | Class | Est. (gate-revised) | Risk |
|---|---|---|---|---|
| **M1** | tolerant master + `_eq` corollary (§2.1) | A | ~40k (gate-drafted) | none — 3-line proofs |
| **M2** | W3 instance `_via_master` (§2.2) | A/B | ~60k | none — probe compiled |
| **M3** | W2 instance `_via_master` (§2.3) | A/B | ~60k | none — probe compiled |
| **M4** | `IndistWall` + 2 instances + `each_…_from_master` (§2.4) | B | ~120k | the structure ergonomics; keep it a plain data record |
| **M5** | door + decoy re-exports + R4 board (§2.5) | A | ~60k | none — re-exports of landed thms |

**Wave plan:** M1 → {M2 ∥ M3} → M4 → M5.  M1 is a hard prerequisite (M2/M3
apply it).  M2/M3 are independent (parallel).  M4 consumes M2/M3.  M5 is
independent of M2–M4 (pure re-export) and may run any time after M1.  Total
gate-revised ≈ 340k (vs the recon's ~300k for M1+M2+M3 alone — the recon
over-budgeted the trivial glue and under-scoped M4/M5).

**Ceremony (every node):** wire into `Salt/TwinBar/All.lean`; add each new
keystone BY NAME to the `#audit_axioms` block; `lake build` exit 0 with all
`✓ [3 axioms]`; longLine + unusedVariables linters are enforced by `lake build`
(underscore unused hyps).

---

## 4. The R4 frame (the too-good-to-be-true tripwire — ARMED)

The M-thread's failure mode is **restatement dressed as a theorem**.  The gate's
probe cleared the load-bearing half (M2/M3 genuinely RE-DERIVE, not restate).
The remaining discipline, binding on executors:

1. **No new twin-prime existence claim anywhere in M1–M4.**  The master and both
   instances conclude `Φ … ≤ (small)` — negative/ceiling statements only.  The
   ONLY twin implication is M5's `input_breaks_wall`, which is the LANDED door
   with a class-D open premise.  If any M-node's conclusion asserts twins (or
   `p1PrimeSum > 0`, or a positive twin lower bound) UNCONDITIONALLY, it is a
   definitional alarm — STOP and flag.
2. **The master is trivial-as-logic; the value is organizational.**  Docstrings
   must say so.  Do not claim M1 is "the theorem"; the theorems are the landed
   instances it re-derives.
3. **No radius equation (BLOCK 2), no cross-wall price coincidence (BLOCK 3).**
   The number 0.614 is a W1-internal definitional identity; the three δ₀'s are
   three different numbers.
4. **W1 is not an indistinguishability instance (BLOCK 4).**  If an executor
   tries to force `no_twin_weight` through `wall_of_indistinguishable`, that is a
   category error — W1 is the CS-ceiling/enlargement leg (M5's decoy).
5. **Anti-vacuity:** each instance must be inhabited by its landed witness
   (`impostor_feasible` for W3; `sieveAgree_pair` + `siftedSum_sPlus` for W2;
   the landed `phiLowerR` certificate class for the tolerant W2 hypothesis).  A
   master with no inhabited instance is vacuous — the gate confirmed all three
   witnesses are landed and axiom-clean.

---

## 5. Gate provenance

Probes run (all against the built `.lake/build/lib/lean/Salt/…` oleans):
- `MProbe.lean` — the tolerant master + the W2 and W3 re-derivations, END-TO-END,
  EXIT 0.  This is the charge-1/charge-2 load-bearing check.
- `MAudit.lean` — `#print axioms` on all 11 landed objects the design leans on:
  every one `[propext, Classical.choice, Quot.sound]`.  Plus the price-tie
  identity closed by `field_simp` (charge 4 = definitional).

Charges settled: (1) W3 re-derives exactly, no extra hypotheses — PASS.
(2) master must be tolerant — RE-CUT applied (BLOCK 1), tolerant form verified.
(3) δ₀ not commensurable — PROSE only (BLOCK 2).  (4) price tie numerology —
PROSE only (BLOCK 3).  (5) honest asymmetry — only W2's door implies twins;
concrete inputs class-D (§2.5 R4 board).
