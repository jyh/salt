# COUNCIL 0731 — the morning after the assembly campaign

*Sealed state at convening: `15ddb44` (build 9629 exit-0, axioms standard
everywhere). In the kernel: `logChowla2_conditional_sharp` — log-averaged
two-point Chowla at a witnessed scale, conditional on exactly two named
objects: `S15Sel'` (the 11-line selection register) and `S15CrossingBound`
(B4). The full ledger: flags.md, the 7/30 evening arc (~31 commits).*

---

## C1 — THE WIDTH GIANT: the B4 crossing-bound design block

**The wall (all kernel-certified).** Every regime the spine can build has
λ₊ ≥ λ₋³ (`probe_regime_width_forced` — hJcon *is* the entropy budget;
the tower is a theorem, not a builder choice). The cap bundle's `budget`
field (the thinBundle tail `S^{2·loglog S/log 𝒫₂}` at S ≈ X_d) allows
λ₊ ≤ λ₋ + 7.1448. Deficit ~5000× at the kindest exponent. This blocks
exactly one object: the B4 crossing bound's only landed supply route.

**The two known routes and their two different walls:**
- *B4 raw at εr = 0*: dead at the seam-row constant — a hard 4320×
  shortfall, certified by counter-witness (`probe_rem_shortfall_at_zero`);
  closing it means beating MR's own published 720 by 4320× (sharpest
  landed variant: 520). Class D.
- *B4 through the cap bundle at εr = θ₂₉₃−1/500*: everything supplied
  (37/37 fields) EXCEPT `budget`, which carries the width law above.

**The design question for this council:** does a THIRD route exist — a
crossing-bound supply that never routes through `budget`? The unexplored
space: (i) the ~70 corpus declarations carrying the crossing shape
(STOP-SCOUT's census — each has a tail; nobody has classified their
walls); (ii) a per-block budget re-derivation with S pinned to the
H-scale rather than X_d (the tail exponent then reads loglog H/log 𝒫₂ —
the width law's LHS drops from ½e^{λ₊} to λ₊); (iii) the
`USetGradedBalance`/`USetBalance` raw producers (ε-free main leg already
landed at `(log X)^{5θ−2ρ}`; only the 2E remainder leg needs pricing);
(iv) an εr-split *inside* B4 (the seam leg at εr = 0 where 4320× is the
wall, the absorption leg at εr > 0 where the x-scale pays — can the
crossing bound decompose?).

**RECOMMENDATION:** authorize ⟦B4-SUPPLY⟧, a full design block in the
house genre — scoper wave over (i)–(iv) with kernel probes, adversarial
refuter pass on the winning route, council v2 before any executor. This
is the campaign's central remaining mathematics; it deserves the same
treatment the two knots got.

## C2 — THE REGISTER WITNESS: expose the opaque constants

`S15Sel'`'s full ∃(R,M) witness stopped honestly at the opaque
`Cg/δ₀/Ct/x₀/Mfl` the capstone produces existentially. But the corpus
already knows these constants are EFFECTIVE (ConstantsExposed: δ₀ =
2.293·10⁻¹⁶⁸ exact, Cg ≤ 2·10¹², all nine spine constants) — the bounds
simply are not *threaded through the capstone's prefix*.

**RECOMMENDATION:** authorize ⟦SEL-WITNESS⟧, established conjunct-carry
genre (the HLO-EXPORT precedent, third use): thread the effective bounds
into the const twin's ∃-block, then land the ∃(R,M) witness page — the
conditional becomes non-vacuous *with a kernel witness*, not just
anchor-cap evidence. Executor-tier, no design risk identified.

## C3 — RATIFICATIONS: eleven rulings, three errata

Under the push-forward grant, banked in flags with evidence, now for
ratification: (1) route-(b) fuse composition; (2) the forced Hlo carry;
(3) Aexp := 3; (4) the shared s13BandM0 pin; (5) the block-floor gate
line; (6) the mu_cap deletion [+ the "zero readers" erratum — field yes,
constraint no]; (7) rawcap' as road [superseded by 8]; (8) THE CONST
ROAD at Cp = 0, εr freed positive; (9) Rbd_grade/Cq_gate as supplier
hypotheses; (10) no-All.lean-race protocol; (11) the fifteen-item
conditional fire. Errata: the level1-not-p2 slot call; the ruling-6
phrasing; the fourth clock offense (law hardened: `date` before ANY
time narration, including memory blocks).

## C4 — THE NAME

The statement stands at HEAD-SCOUT's honest shape
(`LogChowla2WitnessedScale`): *there is an explicit ε > 0 such that for
every prescribed window floor and outer-scale demand there is a scale
pair (x, ω) at which |Σ_{x/ω<n≤x} λ(n)λ(n+1)/n| ≤ ε·log ω.* The fences:
ε is chosen-and-opaque (the ∀ε-upgrade is a separately priceable wave);
x is lower-bounded only (witnessed scales, not a limit); the content is
fixed-factor cancellation at the witnessed scale. **The name is the
Captain's alone.** (Nothing is announced regardless until the summit
seal: audit + leanchecker + the statement-honesty pass + your word.)

## C5 — THE HUMAN ARC (facts only)

- **mathlib PR #42116**: CONFLICTING (the bot asks for a master merge —
  mechanical, in hand this morning). Beneath it, a reviewer questions
  inclusion vs. the formal-conjectures version (length, docstrings);
  you have one reply in. Your call on the response; I hold facts.
- **arXiv endorsements**: Loeffler (sent 7/29) and Buzzard (sent 7/30)
  both pending. Approval re-surface scheduled ~8/4 if quiet.
- **Flagship #2** (the campaign paper) queues behind the capstone.
