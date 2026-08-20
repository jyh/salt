# λ-BV — THE DESIGN BLOCK (P1, commissioned 2026-08-20)

**Pen:** math. **Status:** drafted 08/20 12:4x, **refuter pass NOT yet run — no wave may be
dispatched until it is** (verify-posture law). **Door consumed:** `brun_lower_ell1`
(`Salt/Chen/BrunEll1.lean:191`, d0d9097). **Objective:** the road toward the parity-pinned
survivor, `Ω(n)` odd.

⛔ **SCOPE FENCE, standing beside E7 and binding on every wave below.** `l1LowerEffective_goldenGate`
is a **POINT** floor at `s = 1`. It does **not** discharge `K_vt`, whose live ineffectivity is
`siegelBandB`'s EVT **band** minimum. If any wave here reaches K_vt territory, that is **P2's**
boundary, not P1's, and the wave stops and reports.

---

## §0 — THE OBJECTS, exactly as the corpus states them

From `Mathlib/NumberTheory/SelbergSieve.lean`:

```
multSum d      = Σ_{n ∈ s.support}  [d ∣ n] · s.weights n
rem d          = multSum d − s.nu d · s.totalMass
rosserRemainder s bound = Σ_{d ∈ divisors s.prodPrimes, d < bound} |rem d|
```

and `s.prodPrimes_squarefree : Squarefree s.prodPrimes`.

`brun_lower_ell1` leaves exactly one slot open:

```
X·W(z)·(1 − 2λ^{2b}e^{2λ}/(1−λ²e^{2+2λ})) − rosserRemainder s (Q·D)  ≤  s.siftedSum
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

🔑 **This is not a conjecture — it is a LANDED AMENDMENT in this repo.**
`docs/exploration/q6a-design.md` §D3 carries *"GATE AMENDMENT: no λ-BV — the summatory rate
suffices; the wall is UNCONDITIONAL"*, retires its `LambdaLevel` Prop **for exactly this reason**,
and sources the rate from the **landed** `siegelWalfisz_psiTot` through two named bridge nodes:
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
not an argument. On squarefree `d`, `liouville d = μ d` — this is already in the corpus
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
| `brun_lower_ell1` — the ℓ¹ exit, `rosserRemainder` slot open | `Salt/Chen/BrunEll1.lean:191` | ✅ landed d0d9097 |
| `lamR`, `isSignFunction_lamR` — λ as a real completely-multiplicative sign function | `Salt/HB/SignLiouville.lean` | ✅ in tree |
| `gGen_lamR_eq_moebius` — `μ²λ = μ`, the squarefree collapse | same | ✅ in tree |
| `LamTildeGen_lamR_eq_vonMangoldt` — `Λ̃_λ = Λ` **on the nose** | same | ✅ audited |
| `overshootExactGen_lamR = 0` — λ is the zero-overshoot sign function | same | ✅ audited |
| `siegelWalfisz_psiTot` — the rate's source | `Salt/BV/Defs.lean:76` | ✅ available, **but it carries `(hSW : SiegelWalfisz)`** — supplied by `siegelWalfisz_holds` (`Salt/SW/Gate.lean:150`, no hypotheses of its own). *Cite it as the pair, never as a bare landing.* |
| q6a §D3's two bridge nodes (ψ→M_μ, M_μ→M_λ) | `docs/exploration/q6a-design.md` | 📐 specified, unbuilt |
| `l1LowerEffective_goldenGate` — effective **point** floor | `Salt/MR/EvenChiDescent.lean` | ✅ landed 08/20, FENCED |

⚠️ **MEMBERSHIP DEFECT FOUND WHILE TAKING THIS INVENTORY, reported not repaired** (the Estermann
executor is live in `Salt/HB/` and I will not race it): `SignLiouville.lean` is rooted at
`Salt/HB/All.lean:20`, but **4 of its 9 declarations sit in no `#audit_axioms` block** —
`lamR_prime`, `isSignFunction_lamR`, `moebius_sq_mul_lamR`, `gGen_lamR_eq_moebius`. That includes
the instance the whole generic chain is instantiated at and the module's own stated "arithmetic
heart". *Its docstring also still says "not yet in the `Salt.HB.All` manifest" — stale, and stale
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

**K6 — THE NAME IS NOT THE MEASUREMENT.** `docs/exploration/q6a-design.md` already RETIRED a
Prop named `LambdaLevel` that looks exactly like what this campaign is called. Before writing any
new named Prop, check it is not the retired one wearing a new label.

---

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
