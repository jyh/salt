# N7 ASSEMBLY GATE — the design block that reopens the flagship proving front

**Date:** 2026-08-11 (morning council). **Seat:** maestro (Fable, ritual-checked this sitting).
**Authority:** the Captain's word at council 8/11 ("please fire", item 1) discharging ruling
f-ii; QUEUE debt (a) (saltworks `docs/QUEUE.md:935`, registered 1f4a313 08/08 20:39).
**Inputs:** `docs/exploration/n7-prep-dossier-0806.md` (+ ADDENDA A–D; row 10 pin repaired by
math at `91f0c88` this morning) · `${SEAT_DIR}/briefs/2026-08-10-next-rung-re-recon.json` (the 7/07
scoping doc is dead as a planning instrument; RESULTS/CAMPAIGNS/roadmap are the registers).
**Road wiring:** Road 3 (`docs/exploration/roadmap.md:18-22`) — N7 is "the remaining HB chain"
row: Lemma 5 → hEngine → **CONVERGENCE: TPC ∨ NoSiegelZeros with no hypothesis** (the CROWN,
`docs/CAMPAIGNS.md:43`).

---

## 0. THE HEADLINE — the supply side is FINISHED; what remains is N7's own assembly

Every pin below was re-verified against the working tree at read time, 8/11 09:5x (grep -F -e
form; the dossier's numbers are amended here where they moved). Three things changed since the
dossier froze on 8/06, all in the good direction:

1. **W3 LANDED** — `Salt/Weil/EstermannGlobal.lean`: `norm_kloosterman_estermann` (`:318`,
   arbitrary `k`, explicit 2-adic factor `√(2^{v₂ k})`, the D3 exit shape) and
   **`norm_kloosterman_estermann_road` (`:343`)** — whose own docstring says "N7 quotes this as
   Estermann (7.1)". Gap row 1's `[DESIGN]` is spent.
2. **W4-a LANDED and gap row 8 IS CLOSED** — `Salt/HB/RealPrimStructure.lean` (809 ln, commit
   `eb14498`, 08/06 10:28): `structure_of_isPrimitive` (`:737`) gives `q = 2^a·m`,
   **`a ∈ {0,2,3}`**, `m` squarefree odd — i.e. `v₂(q) ≤ 3` is a THEOREM for every real
   primitive character. The dossier's FINDING #1 critical path (the 2-adic constant) is clear:
   `factorization_two_roadModulus_le` (`RoadModulus.lean:107`) + `a ∈ {0,2,3}` collapse
   `2^{v₂(D)/2} ≤ 2^{3/2}` on road moduli, every link kernel-side.
3. **The p.217 two-forms bound went UNCONDITIONAL** — `sum_two_forms_le_gcd_of_isPrimitive`
   (`RealPrimStructure.lean:763`): primitivity alone, no split hypothesis. Gap row 6's
   "hypothesis-carrying until W4-a lands" is retired; nothing downstream needs to carry `hW4a`.

**⛔ REGISTER CORRECTION, recorded where a successor will look:** QUEUE debt (b) — "the W4-a
DESIGN CAMPAIGN … mathlib has the tools, not the theorem" — was registered 08/08 20:39
(`1f4a313`), **58 hours after the theorem landed** (`eb14498`, 08/06 10:28, 799 ln vs the
1,300–2,600 priced). The debt was opened stale: a register asserted world-state instead of
measuring it (the same defect class as this morning's mortality-law sweep). Debt (b) is
**DISCHARGED BY EVENTS**; the QUEUE is amended in the same push as this block.

Consequence: **N7 owes no supplier waves.** All eleven gap rows of the dossier's §5 are
supplied or closed. What remains is the assembly itself — §7, §5, §6 of HB 1983 — and that is
what this gate opens.

## 1. THE SUPPLY TABLE — re-verified pins, 8/11 (quote these names, not the dossier's)

| HB input | Lean name | Site (8/11) |
|---|---|---|
| (7.1) Estermann, arbitrary `k` | `norm_kloosterman_estermann` / `…_road` | `Salt/Weil/EstermannGlobal.lean:318/:343` |
| 2-part of the road modulus | `factorization_two_kloosterman_modulus` · `two_pow_factorization_dvd_of_odd_cofactors` | `Salt/Weil/GcdBranch.lean:347/:355` |
| `D = lcm(α₂,q)`, `q ∣ k`, `v₂(D)` | `roadModulus_eq_lcm` :62 · `dvd_roadModulus` :65 · **`dvd_roadModulus_mul`** :72 (row 10; renamed from `dvd_roadLevel` at `588f3b4`) · `factorization_two_roadModulus(_le)` :93/:107 | `Salt/Weil/RoadModulus.lean` |
| `v₂(q) ≤ 3` (W4-a) | `structure_of_isPrimitive` :737 · `exists_split_of_isPrimitive(_enumerated)` :699/:779 | `Salt/HB/RealPrimStructure.lean` |
| (7.2) sawtooth expansion | `sawtooth_fourier_expansion` (kernel, row 2) | `Salt/Weil/Sawtooth.lean` |
| (7.3) majorant expansion | `sawtoothMajorant_fourier_expansion` :166 · `hasSum_majorantCoeff` :142 | `Salt/Weil/MajorantExpansion.lean` |
| (7.4) coefficient decay + L¹ | `norm_majorantCoeff_le_sq` :970 · `tsum_norm_majorantCoeff_le(_log)` :1434/:1444 | `Salt/Weil/Sawtooth.lean` |
| (7.7a) orthogonality mod `k` | `Salt.BV.sum_e_eq` | `Salt/BV/Completion.lean:76` |
| (7.7b) congruence completion | `norm_congrExpSum_le` :1227 (+ `_le_length` :1119, `_le_dist` :1187) | `Salt/Weil/Sawtooth.lean` |
| (7.7d)+(7.8) gcd sums | `sum_sqrt_gcd_div_le` :178 (+ `_log_two_mul` :214) · `sum_sqrt_gcd_dyadic_le` :287 · **`…_of_dvd` :363** (the `k₀ ∣ k` shape (7.8) consumes) | `Salt/Weil/GcdDivisorSum.lean` |
| phase-sum kit ((7.6) service) | `minTerm` :271 · `geom_phase_bound` :298 | `Salt/MR/MinorArcVaughan.lean` |
| p.217 two-forms (§6 regime c) | `sum_two_forms_le_gcd_of_isPrimitive` | `Salt/HB/RealPrimStructure.lean:763` |
| p.216 class vanishing (§6 regime b) | `sum_class_eq_zero_of_isPrimitive` | `Salt/HB/RealPrimitive.lean:415` (moved from `Salt/Weil/`) |
| Λ* positivity (Lemma 1) | `LamStar_nonneg` :359 · `vonMangoldt_le_LamTilde` :368 | `Salt/HB/TwistChain.lean` |
| Lemma 5's constants as kernel objects | `hbG` :81 · `hbKappa` :342-348 (κ print-certified, ADDENDUM D.3) | `Salt/HB/Lemma7Kappa.lean` |

Roll-call closure verified: `Salt/Weil/All.lean:30-34` carries EstermannGlobal, GcdDivisorSum,
MajorantExpansion, RoadModulus; `Salt/HB/All.lean:7-8` carries RealPrimitive, RealPrimStructure.

## 2. THE WAVE PLAN — three waves, not one (dossier rec 5 binds)

N7 = HB Lemma 5, total estimate 9,000–18,000 ln, class C. It does NOT open as one wave.

### WAVE A — §7: Lemma 10 (OPENS NOW; this is the gate)
**Content:** state and prove Lemma 10 ((7.5)–(7.8) + the `K = 2 + k^{1/4}` balance) from the
supply table. Estimate 1,500–3,000 ln; class profile B with C-clusters at the (7.7) junction
and the final balance. **Entry: math seat pulls at will — its context is pre-loaded (its own
pre-flight `91f0c88`).**

Statement-design constraints, each AT its site (all from the source sweep — do not relearn):
- The Lean statement carries **`d(k)³(log 2k)³` literally, never `k^ε`** (freeze rule,
  confirmed correct for Lemma 10 at ADDENDUM A.2: `log(Kk) ≍ log k` at the printed `K`).
- The **intermediate (7.8) carries ONE log**, not three (`(log 2k)¹` — re-derived A.2); the
  cube arrives only at the p.223 assembly (truncation log × dyadic log). Stating (7.8) at
  `(log 2k)³` would be provable-but-blunt; state the sharp intermediate.
- The `d(k)²` intermediate and the **explicit spend of `(C,k₀) = 1`** (a hypothesis of
  Lemma 10 consumed via `k₀ ∣ k`) are steps the notes omit — plan them (A.2).
- The `(log Kk)³ ≤ 2.39·(log 2k)³` conversion is one explicit-constant line and is Wave A's.
- The `d(k)³` divisor bookkeeping (`d(k)·d(k₀)·d(·) ≤ d(k)³`, gap row 4's open half) is
  elementary and Wave A's own; `sum_sqrt_gcd_dyadic_le_of_dvd` already carries the `k₀ ∣ k`
  gcd average.
- **First mechanical act before any proof: the ~20-line `I₀ ⊆ (E,2E] ↦ Finset.Ioc` off-by-one
  scratch check** owed since 8/06 (FINDING #3 / A.3 leaves it explicitly unproved). If it
  fails, STOP and flag — the W5 re-price rests on it.
- The `j = e` vacuity constraint (`weil-trio-audit-0806.md` §2) is untouched and owed here.
- 2-adic constant: quote `norm_kloosterman_estermann_road`, discharge its `v₂(D)` factor via
  `factorization_two_roadModulus_le` + `structure_of_isPrimitive`'s `a ∈ {0,2,3}` — the
  numeric collapse `2^{v₂(D)/2} ≤ 2^{3/2}` is now class A/B, all links named above.

### WAVE B — §5: Lemmas 9 + 11, (5.1)–(5.19) (opens on Wave A's seal)
CRT gymnastics + the four-congruence collapse to (5.11) + the (5.17) application of Lemma 10.
Estimate 3,000–6,000 ln. Application-site constraints: the substitution table of dossier §2
(n ↦ `w₂`, `k ↦ Dδ₁w₁`, the O(1) `T`/`T/w₂` split); the `q ∣ k` discharge is
`dvd_roadModulus_mul` (class A, the mispricing already recorded at row 10); the corrected
p.214 exponents (`S₁ ≪ x^{1/2}`, HB's printed 1/4 is his erratum — established twice over).

### WAVE C — §6: the leading-term evaluation (SCOUT FIRST, then two waves split at (6.12))
The expensive part (4,000–9,000 ln, class C throughout) and NOT Lemma 10. Before pricing:
a read-only Opus scout wave over pp.215–221 against the corpus reusables — dispatch it in
parallel with Wave A, it blocks nothing. Known structure for the scout: three regimes
((a) main term via Lemma 11; (b) killed by `sum_class_eq_zero_of_isPrimitive`; (c) killed by
`sum_two_forms_le_gcd_of_isPrimitive` — both now unconditional); window edge `x ≥ q^{250}`
spent at (6.11); the scariest sub-block is **two GENERIC product-differentiation formulae**
(B.3) — point the executor at them first; reusables: `Salt/HB/Lemma7Prod.lean`
(`hbEulerLog`/`hbEulerProd`/`hbLogF`), `TwistedMertens.lean:136`
(`logDeriv_LFunction_eq_LSeries`). Statement trap that would produce a FALSE lemma: the `C_i`
are `≪ 1` uniformly in `q,t,σ` **but not in `α`** (B.2) — moot at the twin instance
(`α₁ = α₂ = 4` fixed) but it must be stated, never assumed.

**Exit of the three waves:** HB Lemma 5 in the kernel, stated against `hbG`/`hbKappa`
(constants print-certified, D.3), error `O(x·L⁴z^{−1}d^{−1}4^{ω(d)})` — the (6.15)/Lemma-5
`x`-factor reconciliation of ADDENDUM D is a formalizer trap, already resolved: the `x` is the
`t`-integration length. Lemma 5 feeds the Lemma 3–10 assembly of Road 3 toward hEngine.

## 3. LAWS RIDING (every wave, every executor brief)

Build/audit only through `../saltbuild.sh`, run BARE, judge "EXIT=N" from the text. Axiom check
per landing: at most `[propext, Classical.choice, Quot.sound]`. `grep -F` always; `-e` for
alternation (`\|` under `-F` is a literal — this block's own pin sweep hit that mine today).
Roll-call row in the SAME commit as the file. Statement-read ≠ kernel-checked: every pin above
is bytes-say-so until an executor's build replays it. No stubs; give up loudly at ~3 attempts
with a flags.md entry. Shared tree: pathspec-only commits. Blueprint statements are not altered
to make proofs go through (iron rule 1) — Lemma 5/10 statement changes come back to this desk.

## 4. GATE CRITERIA + ASSIGNMENT

The gate is OPEN when this block is pushed and the QUEUE debt row points here. Wave A is
**assigned to the math seat on pull** (proposed, not imposed — its 09:16 measurement asked for
exactly this gate; its pre-flight is the freshest context in the fleet). Wave C's scout may be
dispatched by math or this desk at either's seam; Opus tier, read-only. Wave B waits on A's
seal. First landing of Wave A = Lemma 10's statement compiling against the supply table with
the off-by-one check discharged; its seal = the full (7.5)–(7.8) chain, saltbuild EXIT=0,
axioms clean, guide/flags updated in the same commit.

**[AMENDED 8/11 10:2x, at math's question from inside the wave — the criterion above collided
with iron rule 2 (no `sorry` on `main`), and the repair is a MECHANISM, not a relaxation:
(i) the "statement compiling" check is discharged in `Scratch.lean` — the house's own
uncommitted elaboration space (CLAUDE.md build commands) — with `sorry` allowed THERE ONLY;
receipt = the elaboration output quoted in flags/bus; the scratch is never committed.
(ii) every COMMIT stays sorry-free: build bottom-up so each landing is a proved piece
(compiler's L2 shape, tested last night, re-verified at the bytes this morning — sub-lemmas
land proved, the top statement lands WITH its proof).
(iii) NO track branch: the checkout is cross-seat with no lock, and a branch switch would
move the tree under three other seats. Iron rule 2 stands unamended.]**

**This block supersedes nothing in the dossier except its pins** — the dossier remains the
reference for the mathematics; this gate is the executable form of its recommendations.
