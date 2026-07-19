# FULCRUM HUNT — CONSUMERS/GLUE AUDIT (Pass 1)
Auditor: consumers/glue. All claims GROUNDED (file:line) unless marked MEMORY.
Date: 2026-07-18 night. Scope: what stands BETWEEN the landed pieces and the full
conditional `InfinitelyManySiegelZeros → TwinPrimeConjecture`, and what shape F must
take to cross it.

## 0. The formal target (the flagship statement shape — LANDED as a def)

- `InfinitelyManySiegelZeros` — Salt/TwinBar/SiegelTwin.lean:85-88:
  `∀ c > 0, ∃ (q>1) (χ quadratic primitive mod q, χ≠1) (β), L(β,χ)=0 ∧
  1 − c/log q < β ∧ β < 1`. ∀c∃ order (the ∃∀ mis-freeze `BadHyp` is refuted,
  `badHyp_false` SiegelTwin.lean:153). First-power coupling.
- `HeathBrownStatement := InfinitelyManySiegelZeros → TwinPrimeConjecture`
  — SiegelTwin.lean:92-93. Dichotomy equivalence `heathBrown_iff_dichotomy`
  (TwinPrimeConjecture ∨ NoSiegelZeros) at :136-147.
- The HB-ENGINE re-freeze pins the campaign target: "Target statement:
  `InfinitelyManySiegelZeros → TwinPrimeConjecture` = the landed HeathBrownStatement,
  exactly — the first-power hypothesis is what the paper needs, no squared-log
  strengthening, and the mis-aimed SiegelSequence bridge is bypassed"
  — docs/exploration/s3-hb3-design.md:876-880.

## 1. "H-glue" disambiguation (the grep target)

The docs' "H-glue" is the CHEN assembly glue (docs/blueprints/chen.md:461-470:
discharge map for `chen_of_hypotheses`'s H). It LANDED: `chen_headline :
{p | p.Prime ∧ IsP2 2 (p+2)}.Infinite` — Salt/Chen/ChenTheorem.lean:32,
sorry-free, axioms audited (docstring :24-26). Relevance to the fulcrum: (a) the
H-glue's `∀X ∃ operating point` plumbing (Chen/Assembly.lean:425-440 →
`Set.infinite_of_forall_exists_gt`) is EXACTLY the WP7 windowed-door shape HB needs;
(b) chen_headline is the corpus's proof-of-life that signed-resolution reading
escapes the parity wall (TwinDoor.lean:40-44).

## 2. The demand chain, link by link (what each consumes of the Siegel input)

### L1 — hypothesis intake, HB (1.11)+(1.13)
s3-hb3-design.md:814-817: `1−β₀ ≤ (3 log q)^{-1}`, `η := {(1−β₀)L}^{-1} ≥ 3`;
window (1.13) `q^250 ≤ x ≤ q^500` (Cor 1 at q^300). Consumes: QUALITY first-power
(NOT squared-log); one real zero of one quadratic primitive χ mod q per window;
χ real primitive ⟹ q cube-free (design :810-812) is derived, not assumed.

### L2 — Corollary-2 door (WP7, UNBUILT)
s3-hb3-design.md:818-821: "target Corollary 2's shape (∃ effective C^(1):
η ≥ C^(1) infinitely often ⟹ infinitely many twin representations), consumed
through twin_survivor_of_pos, replacing twinB_min_implies_twins." WP7 spec at
:867-871: "the twin door re-point (windowed positivity via twin_survivor_of_pos +
a NEW arbitrarily-large-x door lemma; retire the TwinTypeII target)."
Consumes: QUANTITY — unboundedly many moduli q at the FIXED quality η ≥ C^{(1)}
(each window [q^250,q^500] yields ≥1 twin ≥ x/2; q→∞ gives infinitude).
- `twin_survivor_of_pos` LANDED (TwinBar/TwinDoor.lean:204-223): 0 < p1PrimeSum x 1
  → twin pair ≥ x/2. Consumes NO Siegel input.
- `twinB_min_implies_twins` (TwinDoor.lean:270) consumes `TwinTypeII`
  (TwinDoor.lean:182-184): an ALL-x, EVERY-saving asymptotic. HB's supply is
  WINDOWED — this door is RETIRED for the HB route (design :821, :870).
- UNBUILT glue: (i) the B-class arbitrarily-large-x door lemma
  `(∀n, ∃x ≥ n, 0 < p1PrimeSum x 1) → TwinPrimeConjecture`; (ii) the CARRIER BRIDGE
  from HB's S⁽³⁾ (Λ̃/Λ* weighted, Salt/HB/StarStep/StarWindow) to `p1PrimeSum`
  (or re-derived survivor extraction on HB's own carrier).

### L3 — WP2: the L-machinery (where the zero does its real work)
- Lemma 3 (pretense sum) + Lemma 7 (L′/L): s3-hb3-design.md:850-853. Consumes
  QUALITY as log η: `Σ_{χ(p)=1} p^{-1}log p ≪ L(log η)^{-1/4}` — THE PARITY BREAK
  (the zero forces χ(p) = −1 for almost all small p); `L′/L(1,χ) = ηL + O(·)`;
  `κS₁ → 𝔖C(α)(ηL)^{-2}` — max named η-power A = 2 (sigma_window_budget_analysis.md
  C1/C2, :49-74).
- Repulsion `dh_repulsion_ordered` (contract in PROSE, DHRepulsion.lean:266-275,
  explicitly "not `sorry`" :254): diagonal Deuring–Heilbronn — β₀ repels the OTHER
  zeros of the SAME L(s,χ); window 16/17 ≤ ρ.re < 1, |ρ.im| ≤ 1, ordering
  ρ.re ≤ β₀ (T-BAL-UNORDERED, grounded harmless: sigma analysis §3). Witnesses
  b=40..680-grade, k=9..14, c=2^{-26..-250} — orders below literature b≈2; the
  σ-window budget verdict TOLERATES for every WP2 consumer
  (sigma_window_budget_analysis.md §5) with conditions: s = log x/log q ≥ 250,
  q₀ ≈ 20 folded into C^{(1)}, no EF application at x < q^34, T-BAL-BUDGET audit
  before the consuming node. STATUS: T-BAL-R8c IN FLIGHT (pilot.md tail, 20:50 PT);
  engine + 3/5 rows banked (TBalR8.lean), residual = Eβ/Eρ rows + 6 guards +
  assembly + contract.
- Crude zero-density node (UNBUILT): tolerance 3D < 250, any (qT)^{O(1)(1−σ)},
  band up to 16/17 (design :898-902; sigma C3). Consumes non-exceptional zeros only.
- Sharp-EF rebuild (UNBUILT, catch #47, design :891-897): ψ(y,χ) with ENUMERATED
  truncated zero sum — the landed stack is smoothed ψ₁ with zeros assumed away
  (hzf architecture). Range demand: y ∈ [q^250, q^500] only.
- Effectivity: the whole WP2 route avoids Siegel's theorem (Jutila p.47 quote,
  design :947-950) — C^{(1)} stays effective.

### L4 — WP1: the twist chain (landed surface + one undesigned node)
Landed (Salt/HB/All.lean:32-64 audit list): Λ̃/Λ* defs + Lemma 1 (TwistChain),
S-transfers (Transfer/TransferFull — parametric `hb_lemma2` with a PretenseSum
SLOT), star step + honest window (StarStep/StarWindow:
`S2_sub_S3_honestWindow`, `hstar_window`; the P-coprimality resolution
excPrimorial StarWindow.lean:70-75 — support (n(n+2), q·P)=1 with
P = ∏_{p<z, χ_ℝ(p)≠−1} p). Consumes the CHARACTER (sighted weights), not yet the
zero's quality; the PretenseSum slot is filled by WP2's Lemma 3 — the WP1↔WP2 seam.
RESIDUAL: HB-L2c (v-fibration + ShiuCore consumption) — UNDESIGNED, C+
(pilot.md:7395, panel queued :8944); its resisting sum Σ_m τ(vm+2) is EXACTLY
ShiuCore's object (pilot.md:7098-7103), and ShiuCore is CLOSED (MEMORY:
gold-window; SHIU-W5 composition, pilot.md:7176-7179).

### L5 — WP3/WP4/WP5/WP6 (the engine's middle — mostly Siegel-free tools)
- WP3 sieve: Iwaniec Rosser dim 4, D = z³ = q^{1/3} (design :829-835) — import-vs-
  Selberg-re-derivation decision OPEN. Landed adjacent: the pair/mixed sieve counting
  surface `hb_lemma8` family (HB/PairInstance.lean:414, PairSieveMixed, MixedCount —
  audited HB/All.lean:37-48).
- WP4 Kloosterman completion: Weil toolkit BANKED (norm_kloosterman_le_two_sqrt
  Weil/Descent.lean:206; composite/prime-power assembly Composite.lean:107-190,
  CompositeTail.lean:65-224; Incomplete.lean). Deltas owed: gcd factor
  (k,u,v)^{1/2}, cube-free assembly, Lemma 10's congruence-conditioned interval
  completion (design :806-813). Estermann d(k)√k over-satisfied by Weil.
- WP5 THE CORE (Lemmas 9,11, §5 congruence elimination): UNSTARTED, ~1.5-3M,
  THE POLE (design :859-862). Elementary, no Siegel consumption — consumes WP4.
- WP6 leading terms: QuadCharSum LANDED (HB/QuadCharSum.lean; audit :65-70);
  Euler products F,G + (L′/L)² log-differentiation + A_i(d) UNBUILT (:863-866).
  Consumes the zero via L′/L(1,χ) = ηL (the η-dependence of the main term).

## 3. The residual gap (exact, tonight → full conditional)

(a) WP2 endgame: T-BAL-R8c (in flight) → dh_repulsion_ordered; then crude density,
    sharp-EF rebuild, Lemma 3/7 assembly, T-BAL-BUDGET grade audit (design
    :1256-1257 — Λ ~6 orders below Benli, re-audit log-η budget vs k=9).
(b) WP1: HB-L2c design+land (ShiuCore now available).
(c) WP3: the dimension-4 lower-sieve consequence (design decision open).
(d) WP4: three deltas (gcd, cube-free, interval completion).
(e) WP5: the entire core (~1.5-3M) — the largest unstarted block.
(f) WP6: everything except QuadCharSum.
(g) WP7: Theorem 1 → Corollary 2 assembly + the carrier bridge + the B-class
    arbitrarily-large-x door lemma.
Campaign price ~7-13M (design :912, :873) minus tonight's WP2 progress.

## 4. The shape F must take (the glue layer's verdict)

The chain consumes EXACTLY: infinitely many moduli q carrying a real zero of a real
primitive quadratic χ mod q at the FIXED first-power quality η ≥ C^{(1)}, C^{(1)}
the machine's own effective constant. So the weakest sufficient form visible from
the consumer side is
  F(C) := ∀ Q, ∃ q > Q, ∃ χ quadratic primitive mod q (χ≠1), ∃ β real:
          L(β,χ) = 0 ∧ β < 1 ∧ (1−β)·log q ≤ 1/C
consumed at C = C^{(1)}. IMSZ ⟹ F(C) for every C (fix C; run the ∀c∃ witnesses at
c = 1/(nC): each has (1−β)log q > 0 so shrinking c forces infinitely many distinct
(q,χ,β)); F(C^{(1)}) does NOT imply IMSZ — a genuine weakening (quality pinned, no
quality → 0 demanded).
CONSTRAINTS the designers must respect:
1. FIRST-POWER floor is binding: any coupling weaker than (1−β) ≲ 1/log q (e.g.
   1/√log q) breaks (1.11)/window entry — (1−β)·log x ≤ 500·(1−β)·log q must stay
   O(1) on the window.
2. QUANTITY cannot drop below "infinitely many q": one window = one twin pair;
   infinitude of twins needs unboundedly many windows. (Finite prefix q < q₀ free.)
3. The ∃ε₀-first order (`∃ε₀ ∀Q ∃q ... quality ε₀`) is NOT known sufficient:
   ε₀ might exceed 1/C^{(1)}. Until WP2's witnesses freeze C^{(1)}, F is stated
   parametrically (F(C) with C consumed from the machine) or keeps the ∀-quality
   binder on a countable quality sequence.
4. F must stay CHARACTER-SIGHTED (a statement about zeros of L(·,χ)). The TwinBar
   walls kill every tolerant route: `no_parity_beating_certificate_unconditional`
   (TwinBar/WallUnconditional.lean:44-52, unconditional) and the enlarged
   second-moment bar J₁+J₂ ≤ 2log2·I₂ with 2log2 < 2
   (Enlarged.lean:160, Impossibility.lean:161). Non-contradiction triple:
   SiegelTwin.lean:29-48 (blindness vs sight; MmuRate ζ-governed stays true;
   zero_free_region_all deliberately carves out χ²=1 ∧ Im ρ=0 — the region does
   not exclude the Siegel zero). Any F formulated as a SieveAgree-tolerant sieve
   lower bound is provably dead on arrival.
5. Do NOT state F in SiegelSequence's squared-log form ((1−β)(log q)² < c,
   SiegelCorr.lean:54-57) — strictly stronger than needed, a corpus artifact of the
   dispatcher box (SiegelCorr.lean:25-31); the engine bypasses it (design :876-880).
6. The repulsion consumed is ORDERED (ρ.re ≤ β₀): F's zero should be the maximal
   real zero — WLOG-able inside the proof; benign per sigma analysis §3.

## 5. Substitute/supplement artillery at the glue layer (inventory)

- `chen_headline` (Chen/ChenTheorem.lean:32, UNCONDITIONAL): assembly-plumbing
  template + parity-wall escape proof-of-life. Cannot substitute for the twin door
  (P₂ ≠ prime).
- `twin_almost_prime` (BrunLower/TwinInstance.lean:771): Ω(n(n+2)) ≤ 20 i.o.,
  unconditional — lower-bound sieve exists, but tolerant-grade (no parity break).
- `bounded_gaps_unconditional` (SW/Gate.lean:376) + the Maynard chain
  (Maynard/Complete.lean:1472 etc.): the Maynard door is parity-limited to bounded
  gaps at ANY level — never twins (design :739-741). Not a route for F.
- BV/dispersion stack (Salt/BV/): level ½ exactly, no Kloosterman socket
  (typeII_disc_le closes via large sieve — design :738-740); WP5 must build its own.
- `siegel_correlation_strong` (R3b) + TwistedSieve (R3c partials): off the engine
  path (squared-log input; R3c's (a3) is the registered death, design :442-497);
  useful only as honesty guards.
- HB-R3a dead-end and HB-R4-as-tool-absence are RE-ATTRIBUTED (design :726-756):
  the Weil tool is IN HAND; the missing object is the ENGINE (WP1-7), i.e. the gap
  is construction work, not a known impossibility.

## 6. Answer to THE KEY QUESTION (one paragraph)

Between tonight's landed surface and `HeathBrownStatement` stands: the WP2 endgame
(repulsion contract R8c in flight, then density + sharp-EF + Lemmas 3/7 — the only
links that consume the zero's QUALITY, all at first power with log-η grade), the
WP1 seam HB-L2c (undesigned but its key theorem ShiuCore is closed), the untouched
WP5 congruence core and WP6 leading terms (Siegel-free construction, the bulk of
the remaining ~5-9M), and the thin WP7 glue (Theorem 1 → Cor 2 → the windowed door:
carrier bridge + a B-class arbitrarily-large-x lemma consuming twin_survivor_of_pos
— the ONLY link that consumes the zero's QUANTITY, namely infinitely many moduli at
one fixed effective quality). Hence F's shape: infinitely many real primitive
quadratic characters whose L-function has a real zero within 1/(C^{(1)}·log q) of 1,
with C^{(1)} the machine's own effective constant — first-power, fixed-quality,
infinite-quantity, character-sighted; strictly weaker than the landed
InfinitelyManySiegelZeros, whose ∀-quality binder the chain never uses beyond one
strength.
