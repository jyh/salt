# Q1 DESIGN FREEZE — chen_goldbach (Chen-2, full in-sprint) — PRE-GATE

*2026-07-15, Fable freeze off the Q1-INV declaration-level inventory
(the exploration ledger ~14:50). JYH-ratified scope: full in-sprint
(29a9a68). An adversarial gate runs on THIS document before any wave
dispatches. The reuse coefficient is a registered deliverable: every
node's actuals are recorded against the inventory estimates.*

## D0 — the frozen target

```lean
theorem chen_goldbach :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, N = p + q ∧ p.Prime ∧ IsP2 2 q
```

Additive form (no ℕ-subtraction), explicit threshold (house bundle
style), `IsP2 2` unchanged (`WeightTrivia.lean:270`; the survivor
arrives at `IsP2 (opZ N)` and relaxes via `isP2_mono`, Assembly:375).
The alternatives (subtraction / ∀ᶠ / exceptional-set forms) are
recorded in the inventory; corollaries may restate, the primary is
frozen as above. NOTE the quantifier inversion vs the twin
`Set.Infinite`: per-N existence, NO infinitude wrapper (re-derive iii).

## D1 — the reuse contract (what is NOT rewritten)

The 2A backbone imports unchanged — the numeric certificate cluster
(CbarCert/SuperPanels*/SuperClose), the Rosser value cascade
(fchain ≥ 9779/10000, Fchain_switch_le = 243/100, chen_ledger_line),
the mass ledger, the linear-sieve/Buchstab engine, the bilinear/window
BV engine (residues are FREE parameters: set r d := N % d), LogToolkit,
BetaSW (`prime_indicator_coprime_SW`:582 instantiates at s := N), the
abstract A₂ engine, GlueNormalized + RazorClose (generic in X_W and
the three mains). **The singular-series invariance is the load-bearing
reuse fact**: 𝔖_N enters only through W (sifted primes exclude q ∣ N),
X_W = totalMass·W is common to A₁/A₂/A₃ and cancels in the normalized
bracket; nuChen = 1/φ(d) is residue-blind; c̄ = ∫_{1/8}^{1/3}
log(2−3t)/(t(1−t)) dt is N-free. NO numeric re-certification. Any wave
executor who finds themselves editing a 2A file has left the design —
STOP AND FLAG.

## D2 — the three re-derive interfaces (frozen shapes)

1. **G-DENS (B).** `P_N = ∏_{w' ≤ q < z, q ∤ N} q` (prodPrimes is
   consumed opaquely — confirmed); the reduced-residue re-threading
   (`coprime_sub_two` TwinA1:221 → `Coprime d N` from `Coprime P_N N`;
   consumers: apDisc_le TwinA1:242, crt_class_coprime TwinA1W:208,
   rosserRemainderW_le_split TwinA1W:457, rosserRemainderW2_le_split
   TwinA2W:426, divisor_cases BVSum:184); the W-ratio residual: primes
   q ∣ N in [z, y) leave ≤ ω(N)·N^{−1/8} = o(1/log z), absorbed by
   the window_prod slack (constants 25/38 per log z — bump if needed,
   flag the bump).
2. **G-RES (B).** `∃ a < Q, Coprime Q a ∧ Coprime Q (N − a) ∧
   ∀ q ∈ Q.primeFactors, a % q ∉ {0, N % q}` — CRT over the FIXED
   opQ; nonvacuity q ≥ 3 ⟹ ≥ q−2 free classes (q ∣ N ⟹ q−1); q = 2
   with N even ⟹ both forbidden classes are 0, a odd works. Feeds the
   hQa2 slot of chen_of_hypotheses_W (Assembly:720) via crtClassG.
3. **G-ASM's ∀N wrapper (A/B).** opQ = Qval opEps, opEps = 2/10⁸
   FIXED ⟹ opQ ≤ log N for N ≥ e^{opQ}, absorbed into N₀. Per-N razor
   instantiation at x := N (z = N^{1/8}, y = N^{1/3}), positivity →
   survivor n prime in [N/2, N−2], N − n the P₂; p := n, q := N − n.

## D3 — the waves (file-disjoint nodes; new sibling files only)

| Wave | Node | Scope (anchors in the inventory ledger entry) | Class | Est |
|---|---|---|---|---|
| W0 | G-IMPORT | Salt/Goldbach/ skeleton + backbone import check + **CONFIRM the live spine** (ChenTheorem ← FinA3c/FinLed3 ← Headline4 ← Assembly; no superseded twin capstone feeds it) | A | 60k |
| W1 | G-DENS | re-derive (i) | B | 250k |
| W1 | G-RES | re-derive (ii) | B | 150k |
| W1 | G-WEIGHT | window_two_thirds_lt mirror at N−n | A | 80k |
| W2 | G-A1 | goldA1Sieve(/W) + goldBVSum (divisor_cases mirror) | B/C | 330k |
| W2 | G-A2 | goldA2SieveW + aggregation | B | 280k |
| W2 | **G-SW** ⚠ | goldSwitch{Sieve,W,Blocks,BV}: **the {q∣N} unit seam** (switch_dvd_coprime_two SwitchBV:88, nonunit_forces_fst_dvd AggCE:75) — the finite exceptional-modulus split in the switched remainder, x^{o(1)} scale. THE RISK NODE. | C | 350k |
| W3 | G-COUNT | goldTripleCount/WeightedCount/CountFinal/CountW/CountAtOp*/CountClose | B | 380k |
| W3 | G-BAND | goldPairBijection/Band*/PDiag/SwitchDyadic/Pricing/Strip/W2/Agg*/BlockPricing | B | 380k |
| W4 | G-OP | goldHeadlineW2 op-facts (opP_N, opA_N, a12_h* bundles) | B/C | 330k |
| W4 | G-ASM | goldAssembly (positivity/survivor/factors_ge_z + the ∀N wrapper) + goldFinA3/FinLed/Headline4 + the terminal chen_goldbach | C | 380k |

Critical path: G-DENS → (G-A1 ∥ G-SW) → (G-COUNT ∥ G-BAND) → G-OP →
G-ASM. Total est. ≈2.9M (→ ~2.2M at rfl-transfer productivity: the
W/maxDepth transfers are rfl — switchSieveW_W_eq SwitchW:179,
blockSwitchSieve_W_eq SwitchBlocks:254). All executors Opus; every
node ceremonied individually; actuals vs estimates recorded per node
(THE MEASUREMENT).

## D4 — the gate mandate (adversarial, BEFORE any wave)

1. **Stress the X_W cancellation claim** (D1's load-bearing fact): is
   the singular series REALLY confined to W — check the A₃/switch
   carrier's totalMass and the count bridge (tripleSum_le_cbar_final
   CountFinal:555) for any hidden 𝔖_N; if A₃'s normalization differs,
   the whole no-recertification verdict falls.
2. Stress the G-SW seam scoping: is the exceptional-modulus split
   really x^{o(1)}-bounded within the landed remainder budgets (read
   the SwitchBV/AggCE bodies at proof level, not signature level —
   the inventory read them at signature level only).
3. The hWy closure uncertainty: confirm rho − 3/8 = O(1/log z)
   arithmetic at the op point tolerates the Goldbach W-ratio residual
   (GlueFinal/HeadlineW layer).
4. The frozen statement: any vacuity/threshold trap in `∃ N₀ ∀ N ≥ N₀
   Even N → …` against the landed bundle forms (the Even-inside-
   the-quantifier shape).
5. The W0 spine confirmation obligation stands regardless of verdict.

## D5 — disciplines

Iron rules apply per node (no sorry, no native_decide, 3-axiom audit,
ceremony per landing, All.lean wired by the house). Statement
weakening = report exactly (the Q6a-2 pattern); silent strengthening
forbidden. Estimate overruns ≥ 2× on any node → STOP, the house
re-cuts. The reuse coefficient table (est vs actual per node) is
appended to the ledger at each ceremony.
