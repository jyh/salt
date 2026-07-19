# PASS 2 — E2: SIEVE ARTILLERY vs ¬F (the supply map)

E2 enumerator, 2026-07-19. All claims GROUNDED (file:line) unless marked MEMORY.
¬F := ¬FulcrumQualityMin C⋆ = ∃ Q₀, ∀ q > Q₀, ∀ primitive quadratic χ ≠ 1 mod q,
∀ ρ: LFunction χ ρ = 0 → ‖1−ρ‖·(C⋆·log q) > 1
(negation of `FulcrumQualityMin`, Salt/Fulcrum/Basic.lean:61-64).
NO Lean written this pass; analysis only.

## §0 — ¬F's three supply forms (the inputs the artillery could eat)

**Form A (kernel-composable TODAY, zero new Lean).**
¬F(C⋆) ∧ 0 < C⋆ ⟹ ¬InfinitelyManySiegelZeros ⟹ NoSiegelZeros.
Route: contrapositive of `imsz_gives_fulcrum_witnesses`
(Salt/Fulcrum/Gadget.lean:128-131 — IMSZ → ∀C>0 ∀Q ∃ fulcrum witness; instantiate
C := C⋆), then `noSiegelZeros_iff_not_infinitely` (Salt/TwinBar/SiegelTwin.lean:129-131).
Pass 1's negation brief (fulcrum-pass1.md:73) listed the compactness gadget as the
missing bridge for this direction — the gadget has since LANDED
(`siegel_zeros_isolated_below`, Gadget.lean:93-96), so ¬F ⟹ NoSiegelZeros is now a
pure propositional composition of kernel-checked pieces. CAVEAT (honest shape): the
`∃c` in `NoSiegelZeros` (SiegelTwin.lean:76-80) obtained this way is a BARE
existential — the below-Q₀ radii come from the cheap-ball continuity route
(Gadget.lean:49-66), no rate.

**Form B (pinned-constant, meta-level).** For q > Q₀ every real zero obeys
β < 1 − 1/(C⋆·log q) — the SPECIFIC machine constant 1/C⋆ (first-power log quality).
In HB normalization η := ((1−β)·log q)⁻¹: ¬F pins η < C⋆ for ALL q > Q₀.
Effectivity structure: everything downstream is effective RELATIVE TO (Q₀, c(Q₀)) —
¬F's own Q₀ is itself a bare existential; c(Q₀) (the below-Q₀ isolation radius) is
finite-check effective in principle (MEMORY — classical: finitely many χ, each
L(1,χ) ≠ 0 numerically verifiable) but the landed Lean proof extracts no number.

**Form C (full-region tiling, meta-level).** ¬F's ball covers exactly the carve-out
of the landed effective ZFR: `zero_free_region_all` (Salt/SW/ZeroFreeReal.lean:605)
handles (χ² ≠ 1 ∨ Im ρ ≠ 0); ¬F handles (χ² = 1 ∧ Im ρ = 0) beyond Q₀. Together:
classical-shape effective zero-free region near s = 1 for ALL primitive χ mod
q > Q₀. This tiling is the corpus's own structure (`fulcrum_zero_real` consumes the
disjunction explicitly, Fulcrum/Basic.lean:93-103).

---

## §1 — THE BV CHAIN: demand vs supply

**The exact SW-grade demand.** `bounded_gaps_of_siegelWalfisz`
(Salt/BV/AbelCore.lean:757-760) demands `hSW : SiegelWalfisz`
(Salt/BV/Defs.lean:35-38): ψ-form, ∀ A C > 0, ∃ K ≥ 0, uniformly over **ALL** moduli
q ≤ (log x)^C (not just quadratic conductors), all coprime residues:
|ψ(x;q,a) − x/φ(q)| ≤ K·x/(log x)^A. Level: `psi_BV_of_siegelWalfisz'`
(Salt/BV/DispersionClose.lean:439-443) turns this into dispersion-BV at the haircut
level √x/(log x)^B; `hasLevel_half_of_siegelWalfisz` (AbelCore.lean:753) feeds
Maynard.

**The demand is ALREADY DISCHARGED.** `siegelWalfisz_holds` (Salt/SW/Gate.lean:150)
and `bounded_gaps_unconditional` (Gate.lean:376-379) are landed, sorry-free. So ¬F
changes NO truth value anywhere in the chain. Kernel-visible gain of ¬F here: ZERO
(`SiegelWalfisz` is a bare-∃K Prop and is already a theorem).

**The single ineffectivity point, located.** The landed discharge routes through
`siegel_theorem` (Salt/SW/SiegelClose.lean:841-844 — ineffective C(ε), the
Goldfeld-dichotomy exceptional branch fixes an unlocatable (χ₁, β₁)), consumed at
exactly one call site: `psi1AP_main_bound`, Salt/SW/Fold.lean:167 (ε = 1/(4C));
Cₛ enters `c5 := min (min cc ct) Cₛ` (Fold.lean:170) and flows into x₀ and K.

**What ¬F-effective-SW delivers (META).** Under Form B, in SW's range
q ≤ (log x)^C the exceptional term is x^β ≤ x·exp(−log x/(C⋆·C·log log x)) —
super-polylog saving, strictly stronger than EVERY demanded exponent A. So ¬F
replaces `siegel_theorem`'s role wholesale for q > Q₀ (below Q₀: c(Q₀)). Scope-diff
check (catch #224): SW quantifies over all characters; ¬F covers only real zeros of
primitive quadratic χ — but that is precisely the ZFR carve-out (Form C tiles it),
and imprimitive moduli reduce to primitive inducers inside the landed fold
(Fold.lean:154 `psi1_transfer`). No gap. **Deliverable: the BV chain eats
EFFECTIVITY ONLY** — K(A,C), the haircut B, and the Maynard thresholds become
effective-in-(Q₀, c(Q₀)). The headline gap constant C was already effective (tuple
diameter); the current ineffectivity is invisible in the headline statement.

---

## §2 — SALT/CHEN: the keystones' demand

**Status.** `chen_headline` (Salt/Chen/ChenTheorem.lean:32-33) is UNCONDITIONAL and
landed: infinitely many p prime with p+2 prime or a product of two primes
(`IsP2`, Salt/Chen/WeightTrivia.lean:270-271).

**The keystones' exact level/quality demand (grounded call sites).**
- `psi_BV_of_siegelWalfisz' Salt.SW.siegelWalfisz_holds 11` — polylog saving A = 11
  at haircut level √x/(log x)^B: Salt/Chen/BVSum.lean:328, HeadlineW2.lean:819 and
  :893, TwinA1W.lean:637, TwinA2W.lean:721.
- `siegelWalfisz_psiTot ... (A = 1)` — PNT-grade: Salt/Chen/TripleCount.lean:67.
- `Salt.SW.siegelWalfisz_holds A C` generic: Salt/Chen/BetaSW.lean:217.
- Windowed bilinear BV terminals: `general_BV_cutoff_sqrtD`
  (Chen/SqrtDFold.lean:818, √D structural level) and
  `general_BV_cutoff_unconditional` (Chen/WindowSmallChi.lean:458), packaged at
  Chen/WindowedBVStatement.lean:110/:163.
So Chen's whole distributional demand = polylog-saving BV at level ≤ 1/2-minus-
haircut — ALREADY supplied by the unconditional gate.

**What ¬F buys Chen (META only).** Same as §1: effectivity of every constant that
currently inherits Cₛ — in particular the operating-point threshold `op_floors`
(Chen/TheHeadline.lean:55, ∃ x₁ ...) and the error bundle ≤ 1/200 ledger
(FinLed3 `hL_bundle`, cited in ChenTheorem.lean:17-19) become effective-in-(Q₀,c(Q₀)).
**No level upgrade**: ¬F's zero-free ball improves the SAVING side (already
saturated); the LEVEL 1/2 barrier is large-sieve/dispersion-limited, and ¬F supplies
nothing against it. The P₂ → prime step is the parity wall; ¬F supplies nothing
against it either (§4, §5) — and cuts the one landed anti-parity mechanism (the HB
engine's fuel).

---

## §3 — twin_almost_prime: what would ¬F IMPROVE? Nothing.

`twin_almost_prime` (Salt/BrunLower/TwinInstance.lean:771): {n | Ω(n(n+2)) ≤ 20}
infinite, unconditional. Input profile (TwinInstance.lean:20-40): both-sided Brun
sieve `brun_lower` at (b,λ,A) = (2, 1/4, 2) + windowed Mertens (PM1/PM2). It
consumes NO character, NO L-function, NO AP-distribution input — Brun's remainder is
trivial per-modulus counting. **¬F has no entry point into this artifact**: the 20
comes from the level exponent 10.3 and z^{21} sizing (TwinInstance.lean:33-38),
sieve-combinatorial, zero-insensitive.

Sharper honest point: the corpus has already superseded the headline number —
`chen_headline` gives Ω(p·(p+2)) ≤ 3 infinitely often (trivial corollary: Ω(p) = 1,
IsP2 ⟹ Ω(p+2) ≤ 2; MEMORY-free arithmetic, statement-level observation, not landed
as a named theorem). The residual step Ω ≤ 3 → twins is exactly parity; under ¬F it
stays parity-blocked. Deliverable of ¬F on this target: NONE (kernel), NONE (meta,
beyond §2's effectivity of Chen's constants).

---

## §4 — SALT/TWINBAR: what stays EXCLUDED (the dead M₂ door), precisely

**The door, grounded.** `twin_bar` (Salt/TwinBar/Impossibility.lean:173-174): for
EVERY F continuous on the simplex R₂, J₁F + J₂F ≤ 2·log 2·I₂F; the numeric atom
`two_log_two_lt_two` (:161); `twin_gate_fails` (:262-264): for EVERY level
θ ∈ (0, 1], θ·(J₁F + J₂F) ≤ 2·I₂F; `no_twin_weight` (:276-278): no continuous F
with 0 < I₂F crosses the strict twin gate 2·I₂F < J₁F + J₂F.

**The exclusion, stated exactly.** The k = 2 Maynard/Selberg second-moment route to
twins — "produce F and a level θ with θ·(J₁+J₂) > 2·I₂" — is closed
UNCONDITIONALLY, for EVERY θ ≤ 1, including θ = 1 (full Elliott–Halberstam grade).
The hypotheses of `twin_bar`/`twin_gate_fails` contain NO distributional input
whatsoever (only continuity of F); therefore NO consequence of ¬F — however
effective, at whatever level up to θ = 1 — can enter these statements, and the
fulcrum/¬F must NOT be spent attempting to resurrect this door. The θ-quantifier
already prices the best conceivable ¬F-fed level improvement and rejects it:
M₂ ≤ 2·log 2 < 2 is final.

Fossil/scope check (catch #239/#224): the exclusion is exactly the M₂-functional
shape — it does NOT exclude k ≥ 3 Maynard (bounded gaps, landed), Chen-weight
routes, or the HB engine; those are priced separately (§2, §5).

**The complementary kill (the other landed twin door).** ¬F(C⋆) definitionally
empties the HB engine's fuel tank: F_min was DESIGNED as the engine's weakest fuel
(Fulcrum/Basic.lean:19-24, W1 ledger :30-32 — the engine consumes one strength
η ≥ C⁽¹⁾, C⋆ fixes it). Via Form A, ¬F proves `NoSiegelZeros`, so the landed
dichotomy `heathBrown_iff_dichotomy` (SiegelTwin.lean:136-147; `HeathBrownDichotomy`
:97-98 = TwinPrimeConjecture ∨ NoSiegelZeros) is satisfied on the RIGHT horn — under
¬F the entire HB-statement machinery yields ZERO twin information. Likewise
`SiegelSequence` (SiegelCorr.lean:54, squared-log quality) is false under ¬F
(it implies IMSZ, `siegelSequence_implies_infinitely` SiegelCorr.lean:64), starving
`siegel_correlation_dichotomy` (:184). Net: BOTH landed twin doors (M₂ second-moment;
HB engine) are closed/starved under ¬F — that residue is exactly D1's gap Z.

---

## §5 — SALT/HB WP1 TRANSFER: the unconditional half vs the hres slot

**Pass-1 finding, re-grounded.** fulcrum_audit_wp1.md:8-16: the entire landed WP1
chain consumes NO Siegel input — conditional only on χ² = 1 (arbitrary real χ; not
even primitivity), support windows, and parametric slots. Under ¬F every landed WP1
theorem still runs, for every real χ, including all q > Q₀.

**What the unconditional half delivers against ¬F-fed inputs.**
`S1_le_S2` (Salt/HB/Transfer.lean:189-193): S1(A) = Σ_{n∈A} Λ(n)Λ(n+2) ≤
S2(χ,A) = Σ Λ̃χ(n)Λ̃χ(n+2) (Transfer.lean:176-180) for EVERY quadratic χ — an
unconditional UPPER-bound transfer on the twin sum. Under ¬F-fed effective-SW
(Form C), Λ̃χ is a μ²χ-weighted divisor sum whose twisted sums become effectively
evaluable — so the surviving ¬F-compatible WP1 output is an effective per-χ UPPER
bound on the twin von-Mangoldt sum. This is seam-input material (D2), not a twin
producer (upper bounds don't make twins).

**The hres slot: demand vs supply (the requested trace).**
- DEMAND. `hb_lemma2` (Salt/HB/TransferFull.lean:204-214) leaves ONE input, `hres`:
  overshootMajorant χ A ≤ Cmain·(x/z₀) + Cmain·(x/log x)·exp(Aexp·z₀)·PretenseSum χ N
  + junk, where PretenseSum χ N = Σ_{p ≤ N, χ(p)=1} log p / p
  (TransferFull.lean:183-185). The route beats the S1 main term only when
  PretenseSum is SMALL — o(log x · exp(−A·z₀))-grade (audit:169-175: "the pretense
  is the TRUE consumable, not the zero"); the zero was HB's manufacturing device
  for it, at first-power quality η ≥ C⁽¹⁾ i.o. (audit:176-180).
- SUPPLY under ¬F: OPPOSITE SIGN. (i) GROUNDED: the zero-route supplier is
  definitionally cut off — ¬F pins η < C⋆ for all q > Q₀ (Form B), i.e. the exact
  quality the slot's manufacturer needs never occurs beyond Q₀. (ii) MEMORY
  (E1's charge to ground): ¬F ⟹ effective L(1,χ) lower bounds ⟹ χ does NOT
  pretend — classically Σ_{p≤N, χ(p)=1} log p/p = ½·log N + O_eff(1)-grade in the
  HB window (log N ≍ log q), so PretenseSum is provably LARGE. Under (ii) the hres
  demand is not merely unsupplied but UNSATISFIABLE for q > Q₀ (the RHS with large
  PretenseSum exceeds x-scale — vacuous). The twin-producing half of WP1 is dead
  under ¬F; only the S1 ≤ S2 upper-bound half survives.
- Adjacent slot check: the S⁽²⁾→S⁽³⁾ star-step residual (StarStep.lean:319-333) is
  fully discharged per audit:101 — no second slot hides there.

---

## §6 — E2 BOTTOM LINE

Against the sieve artillery, ¬F is a ZERO-TRUTH-VALUE event: every consumer in the
inventory (BV/bounded gaps, Chen, twin_almost_prime) is already unconditional, and
the two twin doors are respectively unconditionally dead (M₂) and definitionally
starved (HB engine). ¬F's entire purchase here is (a) NoSiegelZeros as a landed-
composable corollary (Form A), and (b) METAMATHEMATICAL effectivization — the single
ineffective constant Cₛ (siegel_theorem → Fold.lean:167) replaced by
effective-in-(Q₀, c(Q₀)) data, propagating to SW's K(A,C), BV's haircut, Maynard's
thresholds, and Chen's operating point. The only genuinely NEW ¬F-compatible object
WP1 offers is the effective per-χ twin-sum UPPER bound (S1 ≤ S2 + effective S2
evaluation) — a seam candidate input, not a twin producer. Twins need what neither
horn's sieve output supplies: that is D1's Z.
