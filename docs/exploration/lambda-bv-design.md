# λ-BV — THE DESIGN BLOCK (P1, commissioned 2026-08-20)

# ⛔⛔⛔ REFUTER VERDICT 2026-08-20 13:2x — **THIS BLOCK FAILED ITS GATE. BOTH CENTRAL CLAIMS ARE REFUTED. NO WAVE IS DISPATCHABLE FROM IT.**

Two adversarial refuters ran (mathematics · citation-integrity). **Both central claims fell, with
machine-checked counterexamples at `saltbuild EXIT=0`.** The block is kept in full below because
the refutation is the deliverable; every claim it makes is now annotated with what it actually
survives as. **The verify-posture law worked exactly as intended: this cost two refuters and it
stopped waves aimed at already-landed work, at an open problem, and at the wrong object.**

## R1 — §1's DISCRIMINATOR TESTS THE WRONG FIELD. **Support shape is irrelevant.**
The identity in §1 is fine — *and it is already landed verbatim*, `Salt/TwinBar/ParityWall.lean:309`
`lambda_mult_sum`. **But the dichotomy fails three ways against the corpus's own live sieves:**
- **It returns REGIME A on the flagship BV consumer.** `Salt/Chen/TwinA1.lean:121` has
  `support = Icc(x/2+2, x)` — an interval — with `weights = Λ(m−2)`. K1 would say "no BV"; the
  object is the Λ-mass in the class `n ≡ −2 (mod d)`, which is *precisely what BV exists for*.
- **It is not invariant under a change of variable.** `Salt/Goldbach/A1.lean:51` mirrors that
  sieve with `n ↦ N−n` and gets the OPPOSITE verdict. *A test that flips on a cosmetic
  reparameterisation is not a discriminator.*
- **It is not exhaustive, and the missing case is the twin case.** `Salt/Brun/Sieve.lean:85` has
  `support = image (n ↦ n(n+2))` — neither interval nor affine. Its `d = 1` term is
  `Σ_{n≤N} λ(n)λ(n+2)`, **the two-point Chowla conjecture — OPEN**; and `d = 1` is squarefree and
  lies in `divisors prodPrimes` for *every* sieve, so it cannot be dropped. ⇒ **There is a THIRD
  regime, priced neither free nor BV-class but OPEN, and this block gives no answer for it.**

✅ **THE CORRECTED DISCRIMINATOR, from the refuter and adopted:** ***is `n ↦ λ(n)·w(n)` a linear
combination of COMPLETELY MULTIPLICATIVE functions?*** Constants and λ qualify; `Λ(m−2)`, prime
indicators and `aCount` do not. **Support shape does not enter.**

## R2 — §2's μ-COLLAPSE IS A CONFLATION. **Struck.**
Exactly the fault I named to the refuter as my own weakest paragraph. `λ(d)` occurs **nowhere** in
`multSum`, `rem`, or `rosserRemainder` — `d` appears only inside the predicate `d ∣ n`. The twist
is `λ(n)` **on the sifted variable**, which is not squarefree. Squarefreeness of the *index* cannot
act on the *summand*. Machine-checked at `saltbuild EXIT=0`: `λ(4) = 1`, `μ(4) = 0`, and the two
twists already differ at `d = 1`. **§2 survives only as `|λ(d)| = 1` on the index set — true,
free without squarefreeness, and worth nothing. It is not a collapse candidate. K2 cannot fire in
either direction and is struck.**

## R3 — THE REGIME-A BRANCH IS **ALREADY BUILT**, and §3 called it "specified, unbuilt"
`mmuRate_holds` (`Salt/SW/MobiusRateClose.lean:1059`, no hypotheses) · `Mlambda_rate`
(`Salt/TwinBar/LambdaRate.lean:451`) · `rosserRemainder_sPlus_le` (`Salt/TwinBar/Wall.lean:356`),
composed into **`parity_wall_unconditional`** (`Salt/TwinBar/WallUnconditional.lean:31`).
⇒ **A regime-A verdict does not produce a two-node bridge; it produces NOTHING TO BUILD.**
⛔ **And `Salt/MR/LambdaRateTwisted.lean:131` records this exact stale "unbuilt" claim having been
STRUCK ONCE ALREADY. This block re-imported a struck claim** — the failure mode is not that I
guessed wrong, it is that I did not grep the tree for objects a design doc told me did not exist.
🔑 **And the sharp point: those landed objects prove the parity WALL — the OBSTRUCTION — not the
parity-pinned survivor.** The cheap half of this campaign is not cheap; it is done, and it points
the other way.

## R4 — THREE HYPOTHESES THE BLOCK NEEDS AND NEVER STATED
a **level cap** (`Q` is a free widening knob with only `hQ : 1 ≤ Q`; `|M_λ(⌊x/d⌋)|` is worthless
once `x/d = O(1)` — needs `Q·D ≤ x^{1−δ}`) · **`ν = 1/d`** (Chen/Goldbach carry `nuChen = 1/φ(d)`,
where `⌊x/d⌋ − x/φ(d)` is main-term sized, not a crumb) · and **§0's decomposition is NOT a sieve
decomposition** — `λ·w` is signed and `BoundingSieve.weights_nonneg` forbids it; the corpus does
it correctly as `weights := 1 ± liouville n` (`ParityWall.lean:139/152`).

## R5 — SCOPING GAP, noted by the refuter outside its lens
`1_{Ω odd} = (1−λ)/2` pins Ω **odd**, not Ω **= 1**. A parity-pinned survivor still admits
`Ω ∈ {1,3,5,…}` up to the dimension bound. §6 disclaims the survivor, so this is a scoping note —
but any wave list would inherit it.

---

**Pen:** math. **Status:** drafted 08/20 12:4x, **refuter pass NOT yet run — no wave may be
dispatched until it is** (verify-posture law). ⛔ **PROVENANCE CORRECTED 08/20 13:1x — the sha this block was commissioned with, `d0d9097`, IS NOT ON THE HISTORY.** It `cat-file`s clean from the local store and prints a perfect message, and `merge-base --is-ancestor` says NO — a pre-flip orphan. `5340c7ff` is the ancestor carrying the identical blob (`6a94047d`). *This seat's own fourth-direction law — a stale reference that RESOLVES — and I quoted the sha out of the queue without running the one test that catches it.* **Door consumed:** `brun_lower_ell1`
(`Salt/Chen/BrunEll1.lean:191`, **`5340c7ff`**). **Objective:** the road toward the parity-pinned
survivor, `Ω(n)` odd.

⛔ **SCOPE FENCE, standing beside E7 and binding on every wave below.** `l1LowerEffective_goldenGate`
is a **POINT** floor at `s = 1`. It does **not** discharge `K_vt`, whose live ineffectivity is
`siegelBandB`'s EVT **band** minimum. If any wave here reaches K_vt territory, that is **P2's**
boundary, not P1's, and the wave stops and reports.

---

## §0 — THE OBJECTS, exactly as the corpus states them

From `Mathlib/NumberTheory/SelbergSieve.lean` (`multSum`, `rem`) and **from salt's own `Salt/Chen/LinearSieve.lean:307` (`rosserRemainder` — NOT a mathlib object; this block filed all three under one mathlib heading and two of them belong there)**:

```
multSum d      = Σ_{n ∈ s.support}  [d ∣ n] · s.weights n
rem d          = multSum d − s.nu d · s.totalMass
rosserRemainder s bound = Σ_{d ∈ divisors s.prodPrimes, d < bound} |rem d|
```

and `s.prodPrimes_squarefree : Squarefree s.prodPrimes`.

`brun_lower_ell1` leaves exactly one slot open:

```
X·W·(1 − 2λ^{2b}e^{2λ}/(1−λ²e^{2+2λ}))   [⚠️ the door's docstring writes `W(z)`; `Salt.BrunLower.W` takes NO `z` — an executor grepping for a z-parameterised `W` finds nothing] − rosserRemainder s (Q·D)  ≤  s.siftedSum
```

Its own docstring is explicit that the slot is the deliverable: *"the value of this exit is the
SLOT, not the numerics … it is the only one of the two exits that a `λ`-twisted BV rider or a
parity-pinned survivor could enter. Those riders are named, not consumed."*

**The parity pin is a weight identity, not a new sieve:**
`1_{Ω(n) odd}(n) = (1 − λ(n))/2`. So a parity-pinned sieve is the ordinary sieve on `w`, minus
the **λ-twisted** sieve on `λ·w`, halved. The campaign is therefore entirely about one object:

```
multSum_λ d  =  Σ_{n ∈ support, d ∣ n} λ(n) · w(n)
```

---

## §1 — THE DISCRIMINATOR ⛔⛔ **RUN THIS BEFORE ANY WAVE. IT CAN RETIRE THE CAMPAIGN AS NAMED.**

**The remainder is indexed by DIVISIBILITY (`d ∣ n`), not by a residue class.** Whether that is
free or expensive depends entirely on the support:

**REGIME A — `support` is an interval (and `w` factors through `n`).**
Total multiplicativity: `n = d·m`, `λ(n) = λ(d)·λ(m)`, so

```
Σ_{n ≤ x, d ∣ n} λ(n)  =  λ(d) · M_λ(⌊x/d⌋)
```

**pointwise, with no equidistribution anywhere.** The analytic input collapses to the effective
summatory rate `|M_λ(y)| ≤ C·y/(log y)^A`. ⇒ **In regime A there is NO BV in this campaign and
the name "λ-BV" is a misnomer.**

🔑 **This is not my conjecture — it is a RECORDED AMENDMENT in this repo.** *(It is recorded in a DESIGN DOCUMENT, not in the kernel: nothing about it is machine-checked, and §3 marks its two bridge nodes "specified, unbuilt". In a repo where "landed" means IN THE KERNEL, calling it landed was the same category slip K5 exists to catch, one register up.)*
`docs/exploration/q6a-design.md` §D3 carries *"GATE AMENDMENT: no λ-BV — the summatory rate
suffices; the wall is UNCONDITIONAL"*, retires its `LambdaLevel` Prop **for exactly this reason**,
and sources the rate from `siegelWalfisz_psiTot` **paired with `siegelWalfisz_holds`** through two named bridge nodes *(this sentence said "the LANDED `siegelWalfisz_psiTot`" bare — the sibling surface of the very defect §3 and K5 record; fixed at one surface, left standing at the other)*:
(i) ψ→M_μ (Tauberian, at the power-log rate), (ii) M_μ→M_λ (`λ = μ ∗ 1_squares`, the hyperbola
fold, rate-preserving). Those two nodes are already specified and were promoted to critical path.

**REGIME B — `support` is affine/shifted** (the twin and Chen settings: `n ↦ N − n`, or shifted
primes). Writing `n = N − m`, the condition `d ∣ n` becomes `m ≡ N (mod d)` — a **nonzero**
residue class. Total multiplicativity gives nothing. The required input is genuinely

```
Σ_{d ≤ D} max_a | Σ_{n ≤ x, n ≡ a (d)} λ(n) |  ≤  C·x/(log x)^A
```

**and THAT is the λ-BV rider.** Here the campaign is BV-class and currently unpriced.

⇒ ***K1 (below) is the whole question. A regime-A answer makes this a two-node bridge; a
regime-B answer makes it a campaign. Nothing may be dispatched until it is settled.***

---

## §2 — THE SECOND COLLAPSE CANDIDATE: on the sieve's own divisors, λ **IS** μ

`rosserRemainder` sums over `d ∈ divisors s.prodPrimes`. Since `prodPrimes` is squarefree, every
such `d` is squarefree — and mathlib states exactly that as
`SelbergSieve.squarefree_of_dvd_prodPrimes` (`SelbergSieve.lean:114`), so the step is a citation,
not an argument. On squarefree `d`, `liouville d = μ d` — ⚠️ **but NOT as a citable declaration: it exists only as a `have` inside `moebius_sq_mul_lamR`'s proof body (`SignLiouville.lean:82`). The consumable forms are `moebius_sq_mul_lamR` and `gGen_lamR_eq_moebius`; a K2 wave wanting the bare identity re-derives it in one line.** The corpus holds it as
(`Salt/HB/SignLiouville.lean`, and `gGen_lamR_eq_moebius : gGen lamR = μ` states the collapse
`μ²·λ = μ` in the form the sign-chain uses).

⇒ **The λ-twist, restricted to the sieve's divisor set, is the Möbius twist.** Whether that
buys anything is K2 — but it means the campaign may be reaching for machinery the corpus already
has under a different name. *This is the "check what the corpus already holds before pricing"
step; it cost one lemma-read and could cost a wave.*

---

## §3 — INVENTORY: what is already landed and consumable

| object | where | state |
|---|---|---|
| `brun_lower_ell1` — the ℓ¹ exit, `rosserRemainder` slot open | `Salt/Chen/BrunEll1.lean:191` | ✅ landed `5340c7ff` |
| `lamR`, `isSignFunction_lamR` — λ as a real completely-multiplicative sign function | `Salt/HB/SignLiouville.lean` | ✅ in tree |
| `gGen_lamR_eq_moebius` — `μ²λ = μ`, the squarefree collapse | same | ✅ in tree |
| `LamTildeGen_lamR_eq_vonMangoldt` — `Λ̃_λ = Λ` **on the nose** | same | ✅ audited |
| `overshootExactGen_lamR = 0` — λ is the zero-overshoot sign function | same | ✅ audited |
| `siegelWalfisz_psiTot` — the rate's source | `Salt/BV/Defs.lean:76` | ✅ available, **but it carries `(hSW : SiegelWalfisz)`** — supplied by `siegelWalfisz_holds` (`Salt/SW/Gate.lean:150`, no hypotheses of its own). *Cite it as the pair, never as a bare landing.* |
| q6a §D3's two bridge nodes (ψ→M_μ, M_μ→M_λ) | `docs/exploration/q6a-design.md` | 📐 specified, unbuilt |
| `l1LowerEffective_goldenGate` — effective **point** floor | `Salt/MR/EvenChiDescent.lean` | ✅ landed 08/20, FENCED |

⚠️ **MEMBERSHIP DEFECT FOUND WHILE TAKING THIS INVENTORY, reported not repaired** (the Estermann
executor is live in `Salt/HB/` and I will not race it): `SignLiouville.lean` is rooted at
`Salt/HB/All.lean:20`, but **5 of its 9 declarations sit in no `#audit_axioms` block** — `lamR_prime`,
`isSignFunction_lamR`, `moebius_sq_mul_lamR`, `gGen_lamR_eq_moebius`, **and `lamR` itself**.
⛔ **THIS BLOCK FIRST SAID "4 of 9", WHICH IS NEITHER COUNT: it omitted `lamR`, a
`noncomputable def` — the exact declaration class named in this seat's own matcher-trap warning,
missed again in the paragraph reporting a matcher failure.**
⛔⛔ **AND THE CHARACTERISATION WAS INVERTED IN BOTH HALVES — the corrected version is worse and
narrower.** (a) `#audit_axioms` collects **transitive** dependencies, so
`gGen_lamR_eq_moebius`, `moebius_sq_mul_lamR`, `lamR_prime` and `lamR` are all axiom-covered
through the four audited theorems that consume them. The "arithmetic heart" was never uncovered.
(b) `IsSignFunction` is a `structure` taken as an **explicit hypothesis**, *not* a typeclass —
`isSignFunction_lamR` is not an instance, and **nothing in Lean consumes it**: outside its own
module it appears only in design-doc prose. ⇒ **The real defect is ONE declaration, and it is
that the λ-instantiation of the sign chain is a certificate with ZERO consumers.** *Its docstring also still says "not yet in the `Salt.HB.All` manifest" — stale, and stale
in the safe direction, which is why nobody caught it: a claim about ANOTHER file is outside any
self-check's subject.*

---

## §4 — KILL-CHECKS, shipped with the block (the house pattern the E4a block set)

**A refuter pass gates wave 1. These are what it must run.**

**K1 — THE REGIME DISCRIMINATOR.** Determine, for the intended parity-pinned survivor, whether
`support` is an interval (regime A) or affine/shifted (regime B). **KILL CONDITION: if regime A,
the campaign as commissioned is misnamed and waves 2+ must be re-scoped to q6a's two bridge
nodes — no BV theorem is needed.** *State the support explicitly as a Lean term before answering;
"the twin setting" is not an answer, the `s.support` field is.*

**K2 — THE μ-COLLAPSE.** On `d ∈ divisors prodPrimes` every `d` is squarefree, so `λ(d) = μ(d)`.
Test whether `multSum_λ`'s remainder therefore reduces to an object the corpus already bounds.
**KILL CONDITION: if it reduces, the wave is a rewrite, not a campaign.**

**K3 — NON-VACUITY, and it must FAIL the mutant, not merely fail to prove it.** Exhibit a witness
that the parity-pinned survivor set is nonempty in the intended regime. *A mutation control is
valid only if it makes the mutated statement FALSE — "unreachable by this route" is not a control.
This is the E4a house rule (`e4a_gaussSum_mutant_is_false`), and it is why `EvenChiControls`
exists in tree.*

**K4 — THE POINT/BAND FENCE.** No wave may state or imply a band floor. If a wave's statement
would need `siegelBandB`'s EVT minimum, it stops and reports: that is P2.

**K5 — INTERFACE SUPPLY, checked FORWARD.** *(This check fired on THIS BLOCK while it was being
written: I wrote "`siegelWalfisz_psiTot` — landed" and it carries `(hSW : SiegelWalfisz)`. The
Prop is discharged, so the claim survives — but it survives as a PAIR, and I had written it bare.)*
 `brun_lower_ell1` carries **TEN** hypotheses —
`hQ`, `hb`, `hlam`, `h12`, `hLam`, `hz`, `htotalMass`, `hzprimes`, `hkappa`, `hMert`. (Its
docstring names nine as *"`brun_lower`'s own"*; `hQ : 1 ≤ Q` is the tenth, the level-widening
knob this exit adds. **Nine is the right count for a different question than the one a wave
asks** — a wave must supply all ten.) For each, name **where the wave supplies it**, before
proving anything. *The kernel checks theorems, not that
they compose: nine dangling interfaces were found in one file in one day on the last campaign,
none catchable by a build.*

**K6 — ⛔ THE NAME IS NOT RETIRED, IT IS OCCUPIED. THIS KILL-CHECK WAS FOUNDED ON A FALSE
PREMISE AND IS REWRITTEN.** The block first claimed `LambdaLevel` was a retired Prop and warned
against rebuilding it. **`Salt.Maynard.LambdaLevel` IS LANDED AND LOAD-BEARING** —
`Salt/Maynard/GehVaughan.lean:60`, with `LambdaLevelU` at `:404` and
`lambdaLevel_of_lambdaLevelU`; **43 occurrences across 5 Maynard modules.** It is the **von
Mangoldt** level: `∑_{q ≤ x^θ/(log x)^B} seqDiscrepancy vonMangoldt x q ≤ C·x/(log x)^A`.
⇒ **TWO consequences, and the second is the valuable one:**
(i) a wave writing a new `LambdaLevel` walks into a namespace collision with a live declaration;
(ii) ***that landed Prop is the CLOSEST structural template the corpus holds for the regime-B
rider*** — §5 named the far-away `bounded_gaps_of_siegelWalfisz` and never mentioned the near one.
**If K1 returns regime B, start from `Salt.Maynard.LambdaLevel`'s shape, not from the BV rung.**
*(q6a retired ITS OWN λ-BV design, which is a different object from this landed Prop. The block
read "retired" and never grepped the tree for the name — an absence assumed from a design doc.)*

## §5 — WAVE DECOMPOSITION (conditional on K1; **not dispatchable yet**)

**If regime A:** two executor nodes, both already specified in q6a §D3 —
W-A1 the ψ→M_μ Tauberian bridge; W-A2 the M_μ→M_λ hyperbola fold. Then W-A3, the rem-bound
`|rem d| ≤ (integer crumb) + |M_λ(⌊x/d⌋)|` summed over `d ∣ P(z)`, `d < Q·D`, feeding
`rosserRemainder` directly. **Class B/C, not a campaign.**

**If regime B:** the wave list is genuinely unpriced and the block must be re-opened with the
dispersion apparatus stated. The corpus's BV rung (`bounded_gaps_of_siegelWalfisz`) is the
structural template but λ is not the prime indicator, and the level-1/4 trap recorded on that
rung applies. **Do not estimate this until K1 returns B.**

---

## §6 — WHAT THIS BLOCK DOES NOT CLAIM

It does not claim the parity-pinned survivor. It does not price regime B. It does not touch
K_vt. It supplies: the door's open slot restated over the exact mathlib objects, the two collapse
candidates that could retire the campaign before it is funded, the landed inventory, and six
kill-checks the refuter pass must run first.
