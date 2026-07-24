# MR-GATE grounding map #3 — THE SOURCES: where the region enters the log-Chowla chain
### (the λ-non-pretentiousness trace + the MR-theorem-side port map)

Workflow: wf_63b55005 (pilot.md:8671–8690, JYH-approved 2026-07-18 16:55 PT).
Labels: **[G]** = GROUNDED (file:line read this session), **[M]** = MEMORY (untrusted,
verify-on-staging). MR is the longest-parked campaign — every [M] below is a
mandatory staging-check before any node freeze.

---

## 0. VERDICT (one paragraph)

**[G]** The zero-free region does NOT enter the Matomäki–Radziwiłł theorem's
*application* in Tao's chain. It enters at exactly one gate-load-bearing place:
**the λ-instantiation of the non-pretentiousness hypothesis (1.6) of Tao's
Theorem 1.3** — Tao: "Using the prime number theorem in arithmetic progressions
with Vinogradov-Korobov error term (see [19, §9.5]), it is not difficult to
establish (1.8) when g is the Liouville function" (chowla.txt:272–278). That
hypothesis is `D(λ, χ·n^{it}; x)² ≥ A` for all χ of period ≤ A and **|t| ≤ Ax**
(chowla.txt:210–215) — and the Option-C RED arithmetic
(s3-a3-design.md:1076–1100) is precisely the coefficient test for THIS D²:
width `(log t)^{−θ}` ⟹ `D² ≥ (1−θ)·loglog x`, divergent iff θ < 1. Our landed
power region has θ = 3/4 — the gate is arithmetic-satisfiable. A **second,
distinct** potential entry lives INSIDE the MR theorem's own proof (extreme-|t|
prime-polynomial decay) — **[M]**, unverifiable from staged sources (the MR/MRT
papers are NOT staged), flagged below. The claim "the classical MR proof needs
only elementary-Halász inputs for λ" is **NOT verified** and [M] says it is
false for the full |t|-range — but with the power region landed, both entry
points are served by the same theorem.

---

## 1. STAGED SOURCES INVENTORY

Scratchpad = `/private/tmp/claude-501/-Users-jyh-projects-claude-salt/c6ff6bbc-2921-406a-a6be-c3774806f5ff/scratchpad/`.

| file | identity | role | staged? |
|---|---|---|---|
| `chowla.txt` (+`chowla.pdf`, `chowla_pages/`) | **Tao, "The logarithmically averaged Chowla and Elliott conjectures for two-point correlations"** = arXiv:1509.05422 [G head + refs 1520–1560] | THE primary source; the spine's paper | YES |
| `montgomery3.txt` / `montgomery3.pdf` (scratchpad AND repo root `/Users/jyh/projects/claude/salt/montgomery3.pdf`, both 2,284,571 B = same file) | **Montgomery–Vaughan, Multiplicative Number Theory III (draft)** [G ToC head] | Ch. 23.5 = **Halász** (Thm 23.15 `T:HalaszThm`, montgomery3.txt:3538 [G]); Ch. 24 = VMVT + VK region (already served the Vk campaign) | YES — **montgomery3.pdf IS relevant: it is the staged Halász source** |
| `psu597.txt`, `psu_dedup.txt` | Vaughan PSU Math 597 Ch. 24 (VMVT/VK) [G head] | region side, consumed by VMVT | YES |
| `ford.txt`, `survey.txt` | Ford, zero-free regions (2 versions; survey.txt = arXiv:1910.08205v5) [G heads] | region side, consumed | YES |
| `crit.txt` | Yang arXiv:2301.03165 explicit ζ bounds [G head] | region side | YES |
| **arXiv:1501.04585** — Matomäki–Radziwiłł, *Multiplicative functions in short intervals* (Annals 2016) | cited as **[16]** in chowla.txt:1527 [G] | THE MR theorem | **NO — NOT STAGED** |
| **arXiv:1503.05121** — Matomäki–Radziwiłł–Tao, *An averaged form of Chowla's conjecture* | cited as **[17]** in chowla.txt:1529 [G]; the door's own docstrings cite it (MRTDoor.lean:9) [G] | the theorem the door quotes (Lemma 2.2, Thm 2.3, **Thm A.1**) | **NO — NOT STAGED** |
| Montgomery, *Ten Lectures*, §9.5 | cited as **[19]** in chowla.txt (refs) [G] | Tao's cited source for the λ-(1.8) discharge | NO (MNT-III ≠ Ten Lectures; equivalent content = §4 chain below) |
| Soundararajan, *The Matomäki–Radziwiłł theorem* lecture notes, arXiv:2105.11689 | — | **[M]** modern self-contained proof; candidate alternate porting target | NO |

**STAGE-FIRST (mandatory before node freeze): 1501.04585 and 1503.05121.**
No `mr*.txt`/`tao*.txt` exist in the scratchpad; `bodies.txt`/`montgomery3.txt`
Matomäki hits are bibliographic only [G grep].

---

## 2. WHAT THE CORPUS ALREADY HOLDS (all [G], file:line)

**The Entropy spine (COMPLETE, sorry-free):**
- `Salt/Entropy/Chowla/SpineFinal.lean:260` — `log_chowla_two_final`: the
  terminal surface, Tao's model form `a=1, b=0, h=1, g₁=g₂=λ`
  (docstring :237–245). Conditional **ONLY** on `MRTUniformity R δ` for any
  `0 < δ ≤ δ₀` (with `δ₀ = ε/(2K)`, docstring :251), plus the explicit
  entropy-decrement AM–GM residual `t, g` + budget `hbudget1`
  (docstring :254–258 — "Tao's Lemma-3.x quantitative close"). Every other
  input proven from mathlib, axioms `[propext, Classical.choice, Quot.sound]`.
- `Salt/Entropy/Chowla/MRTDoor.lean:48` — `MRTUniformity` (the `∀α`-OUTSIDE
  door = Tao Prop 2.4, p. 12); `:109` — `MRTUniformityXi` (the Ξ_H-restricted
  Tao-faithful weakening; fires only at `α = −ξ/H`, Tao p. 24); `:116`
  full ⟹ Xi. **Quantifier trap (docstrings :43–47, :98–102): the sup-INSIDE
  form is Tao's (4.1), OPEN — any port statement must keep `∀α`/`∀ξ` outside
  the integral.**
- `Salt/Entropy/Chowla/CircleMethod.lean:37–46` — `expSum` (Tao (3.17) at
  `c_p = 1`: `S_H(α) = Σ_{p∈𝒫_H} (1/p)e(αp)`), `bigXi` = `{ξ : |S_H(−ξ/H)| ≥
  ε²/log H}` (Lemma 3.4 at a=1), `bigXi_bounded` (card ≤ K, Lemma 3.5).
- Regime floor: `H ≥ 4,000,000` (`SpineFinal.lean:298`, via `R.hHlo_floor`).

**The region side (the MR gate's key opened 2026-07-18):**
- `Salt/Vk/GrowthPow.lean:1044` — `zeta_zero_free_region_pow`
  (**UNCONDITIONAL**, commit 65d361d "THE MR GATE OPENS"): every ζ-zero with
  `|Im ρ| ≥ T₀` has `Re ρ ≤ 1 − c/((log|Im ρ|)^{3/4}·(loglog|Im ρ|)³)`,
  `c = 10⁻⁹`, `T₀ = exp(exp(8·log(20000K)+1100))+t₀+3` (flags.md VK-7 block
  ~:9670–9700). θ = **3/4** exactly, `(loglog)³` correction, power 3.
- `Salt/SW/` — the classical L(s,χ) zero-theory: `zero_free_region`
  (`ZeroFree.lean:387`), `zero_free_region_real`, Siegel
  (`SiegelFinal.lean:440`), `ThreeFourOne.lean`, contour machinery
  (`ContourShift.lean`, `ZetaEM.lean`), and **`zeta_lower_shallow`**
  (`ZetaLowerShallow.lean:1–35`): `σ ≥ 1 − c₄/log⁹(|t|+2) ⟹ ‖ζ(σ+it)‖ ≥
  c/log⁷(|t|+2)` — the landed **region→lower-bound bridge TEMPLATE**
  (anchor via 3-4-1 + Cauchy derivative + horizontal transport). NOTE: its
  shallow shape (log-power 7) FAILS the gate coefficient test (7 > 1); the
  route, not the constants, is what ports.
- `Salt/Vmvt/` — VMVT complete (`linnik_lemma`, `vmvt_base`, …, audited in
  `All.lean`); `Salt/Vk/` ladder + emission all sorry-free ([G] no sorry hits).
- Exp-sum infrastructure: `Salt/ExpSum/` (vdC, Kusmin, ζ-blocks),
  `Salt/LS/Vaughan.lean` (Vaughan identity), `Salt/Mertens/`.

**NOT held anywhere in Lean [G grep]: Halász's theorem, any Dirichlet-polynomial
mean-value/large-value estimate in MR's frame, any L(s,χ) power region, any
statement of the MR/MRT theorems themselves (the door is a `def`, not a proof).**

---

## 3. THE HONEST CHAIN (Tao 1509.05422, model form — all [G] unless marked)

```
log-Chowla-2 (Thm 1.2)  ⟸  Cor 1.5  ⟸  Thm 1.3          [chowla.txt:81,230,204]
   spine formalizes the model instance; SpineFinal consumes ONLY Prop 2.4:

Prop 2.4 (chowla.txt:622):  sup_α  Σ_{x/ω<n≤x} (1/n)|(1/H)Σ_{j≤H} g₁(n+j)e(jα)|
                             = o_{H*→∞}(log ω)     — sup OUTSIDE the sum. [G]
   Proof [G, chowla.txt:623–640]: fix α; apply [17, Lemma 2.2 + Thm 2.3] with
   W := log⁵H,  requiring  W ≪ min(A, (log X)^{1/125}),
   per dyadic X ∈ [x/2ω, 2x],  X ≥ x/2ω ≥ (log x)/2 ≥ (log A)/2;
   average over dyadic X → the log-measure form.

λ-case simplification [G, chowla.txt:743–750]:  c_p = 1  ⟹  Prop 2.4 is needed
   only at "MAJOR ARC" α, and [17, Lemma 2.2 + Thm 2.3] can be replaced by the
   SIMPLER [17, Theorem A.1].   ◀◀ the minimal-port pivot

Hypothesis (1.6) of Thm 1.3 [G, chowla.txt:208–215]:
   Σ_{p≤x} (1 − Re g₁(p)χ(p)p^{−it})/p ≥ A
   for ALL χ of period ≤ A and ALL |t| ≤ A·x.
   ⚠ Option-C freeze says "heights t ≍ x^A" — the GROUNDED text says |t| ≤ Ax.
   The coefficient arithmetic is identical (loglog(Ax) = loglog x + o(1);
   even loglog(x^A) = loglog x + log A). Record the discrepancy; use |t| ≤ Ax.

λ-discharge of (1.6) [G, chowla.txt:272–278]: "PNT in APs with
   Vinogradov-Korobov error term (see [19, §9.5])" — i.e. THE REGION ENTERS
   HERE, and only here, in Tao's own chain.
```

Tao's Props 2.1/2.2 (Halász-based reductions to unit-magnitude/completely
multiplicative g, chowla.txt:378–475 [G]) are **NOT needed** for the λ model
form — λ is already completely multiplicative of modulus 1. The Halász
inequality cited there ([24]/[10, Cor 1]) is needed only for the general-g
Theorem 1.3, i.e. Route F's *faithful* scope, not the gate.

---

## 4. WHERE THE ZERO-FREE REGION ACTUALLY ENTERS — the D² trace

**Entry point 1 — the gate's own need (GROUNDED, load-bearing).**
The λ-instantiation of (1.6). The pretentious distance at the worst pattern:
```
D(λ, χ·n^{it}; x)² = Σ_{p≤x} (1 + Re χ(p)p^{−it})/p
                   = loglog x + Re log L(1 + 1/log x + it, χ) + O_A(1)
```
(Mertens + Euler-log; prime-power p^k, k≥2 terms are O(1)). The region enters
as the **lower bound on the L-factor at height t, |t| ≤ Ax**:
- Option-C frozen arithmetic [G, s3-a3-design.md:1076–1100]: region width
  `(log t)^{−θ}` ⟹ `log|ζ(1+it)| ≥ −θ·loglog t` ⟹ `D² ≥ (1−θ)·loglog x` —
  **diverges for ANY θ < 1**; Littlewood has coefficient EXACTLY 1
  (width `loglog t/log t` ⟹ `log|ζ| ≥ −loglog t + logloglog t`) ⟹
  `D² ≥ logloglog x + O(1)` — bounded — **RED**. No cutoff re-parametrization
  escapes (invariant under P₋/P₊ choices).
- With OUR landed shape θ = 3/4, `(loglog)³`:
  `log|ζ(1+σ'+it)| ≥ −(3/4)·loglog t − 3·logloglog t − log(1/c′)`  (σ' ≥ 0)
  ⟹ `D² ≥ (1/4)·loglog x − 3·logloglog x − O_A(1) → ∞`.  **Coefficient 1/4.**
  (If the bridge only achieves the 3-4-1-anchor grade, see N1: θ_eff = 13/16,
  coefficient 3/16 — still diverges. Both budgets recorded in §6.)

**Entry point 2 — inside MR [16] itself ([M], VERIFY ON STAGING).**
[M]: the MR proof's Parseval/large-value frame needs pointwise decay of prime
Dirichlet polynomials `Σ_{P<p≤Q} p^{−1−it}` for |t| up to X-grade, and at
extreme |t| uses VK-region-grade estimates. The prompt's parenthetical "the
classical MR proof needs only elementary-Halász inputs for λ" is therefore
**NOT CONFIRMED**: no staged source decides it (1501.04585 unstaged), and [M]
leans FALSE for the full |t| ≤ X/h mean-square range. **Consequence either
way: none for feasibility** — `zeta_zero_free_region_pow` + bridge N1 serves
this entry too (T₀ is an absolute constant, eventually ≪ any X-grade range).
But the NODE COUNT of the MR-core port depends on it — C2 checklist item.

**Entry point 3 — the entropy/circle part: NONE.** Landed sorry-free ([G] §2).

**Character aspect:** (1.6) quantifies over χ of period ≤ A with A a
**constant** (depending on ε only). So: no Siegel-zero exposure (constants may
depend on A nonconstructively; at t = 0 non-principal χ gives
`Σ_{χ(p)=1} 2/p ~ loglog x` divergence; real-χ t=0 needs only `L(1,χ) ≠ 0`).
The t-aspect for L(s,χ), q ≤ A, DOES need a power-shape region — our Vk
machinery is ζ-only — gap node N2 below.

---

## 5. THE PORT-SHAPED CHAIN (nodes; class guesses; both routes)

**Gate target:** discharge the door consumed at `SpineFinal.lean:263`.
Currently that is the FULL `MRTUniformity` (∀α). The Xi-rewire (spine consuming
`MRTUniformityXi` instead) is grounding-map-#1 scope; both routes below are
stated against their natural door.

### Route M — minimal-for-the-gate (Tao's own λ shortcut; needs the Xi door)
- **M1 XI-MAJOR (C):** structure of `bigXi`: every ξ ∈ Ξ_H has `−ξ/H` in a
  major arc `|α − a/q| ≤ 1/(qH')`, `q ≤ Q(ε)`. Mechanism: contrapositive
  Vinogradov minor-arc bound for the PRIME window sum `S_H(α)` (threshold
  `ε²/log H` [G CircleMethod.lean:41]). Corpus: `LS/Vaughan.lean` (Vaughan
  identity) + `ExpSum/` vdC. Exponents TBD from Tao pp. 24–25 on staging.
  ⚠ verify first whether Tao's Lemma 3.4/3.5 as formalized already implies
  the arc structure, or Tao's §4 uses it silently.
- **M2 MRT-A1 (C/D until staged):** port **[17, Theorem A.1]** at g = λ,
  rational/major-arc α only [G that it suffices: chowla.txt:743–750; statement
  shape [M]: modulated short-interval averages over [X, 2X] for λ at α = a/q,
  reduced through characters mod q + partial summation in `n^{it}` to MR
  short-interval averages of λ·χ-twists]. Constraint budget from Tao's Prop
  2.4 proof [G]: W = log⁵H ≤ min(A, (log X)^{1/125}); worst X ≍ (log x)/2.
  - **CORRECTION (DOOR-SCOPE / SEAM-SCOPE 2026-07-24)** to the [M]-graded shape
    guess above: the additive-twist mechanism is NOT "partial summation in
    `n^{it}`". MRT's actual mechanism is (i) Dirichlet approximation of α,
    (ii) integration by parts over the SUB-WINDOW length (MRT eq. 4.2), and
    (iii) a residue-class split closed by character orthogonality (eq. 4.4).
    The character half of the old guess was right — reduction through
    characters mod q to MR short-interval averages of λ·χ-twists is correct;
    only the "partial summation in `n^{it}`" clause is wrong and is retired.
- **M3 MR-CORE (the big port; node freeze DEFERRED until 1501.04585 staged):**
  the MR [16] theorem at λχ-twists. Expected internal skeleton [M]:
  (a) Parseval: short-interval variance ⟶ `∫ |F(1+it)|² dt` over
      |t| ≤ X/h-grade, F the Dirichlet polynomial on [X, 2X];
  (b) the Ramaré-identity / typical-factorization decomposition over prime
      ranges [P_j, Q_j] (small-prime multiplicativity; smooth-number
      complement priced by sieve bounds);
  (c) Dirichlet-polynomial mean value + Halász–Montgomery large-value
      estimates (corpus: `LS/` large-sieve frame is adjacent scaffolding);
  (d) pointwise prime-polynomial decay: moderate |t| via Halász-grade
      pretentious bounds (staged source: MNT-III §23.5, Thm 23.15
      [G montgomery3.txt:3538] — ⚠ that statement is the QUALITATIVE
      equivalence; the port needs the QUANTITATIVE Halász decay — check
      MNT-III's surrounding sections on staging, else Tenenbaum III.4 [M]);
      extreme |t| via the power region (= entry point 2, [M]).
- **M4 NONPRET — the λ-(1.6) discharge (the region trace, all new nodes):**
  - **N1 POW-LOWER (C):** `∀ σ ∈ [1, 2], t ≥ T₀: ‖ζ(σ+it)‖ ≥
    c′/((log t)^{θeff}(loglog t)^{3})`-grade with **θ_eff < 1**. From
    `zeta_zero_free_region_pow` via the `zeta_lower_shallow` route
    ([G] template: 3-4-1 anchor at σ₀ = 1+η(t) + Cauchy derivative +
    horizontal transport). Anchor arithmetic (explicit): η = c·L^{−3/4}ℓ^{−3}
    (L = log t, ℓ = loglog t):
    `|ζ(1+η+it)| ≥ (η³/(8C₁L))^{1/4} = (c³/8C₁)^{1/4}·L^{−13/16}·ℓ^{−9/4}`
    ⟹ θ_eff = **13/16** with NO transport needed if the D²-bookkeeping (N5)
    is run at σ = 1+η(t) instead of 1+1/log x — a design choice: moving the
    evaluation point costs `Σ_{p≤x}(p^{−1−1/log x} − p^{−1−η})/p`-grade
    ⚠ PRICE THIS FIRST at the worst pattern t ≍ Ax (the smallest-index-term
    rule): naive bound η·Σ_{p≤x}(log p)/p ≈ η·log x = c·(log x)^{1/4}ℓ^{−3}
    DIVERGES — the naive move is DEAD; either transport ζ down to
    σ = 1+1/log x inside the region (Landau `ζ′/ζ ≪ log t/η` route, θ_eff
    = 3/4 + o(1)) or restructure the distance sum. THIS is the designers'
    first real fork; both feasible on paper, neither free.
  - **N2 L-CHI-POW (C, sized mid):** the same power-shape lower bound for
    `L(1+σ'+it, χ)`, χ mod q ≤ A **fixed**, t-aspect. Gap: Vk ladder is
    ζ-only; the χ-twist splits blocks into ≤ q APs with constant χ-values
    (same Weyl phases), growth `‖L‖ ≪ q·log t`; SW holds the classical
    L-bracket (`ThreeFourOne`, `zero_free_region` [G]). Assessment, not
    grounded: replicate `PowRegion` at the L-level on landed scaffolding.
  - **N3 T0-FILL (B):** the pre-flagged hole [G pilot.md:8678–8681,
    "T₀ = exp(exp 100) range hole vs the classical-region union"]: for
    3 ≤ |t| ≤ T₀ (T₀ absolute), compactness + non-vanishing on Re s = 1
    (`riemannZeta_ne_zero_of_one_le_re` [M mathlib name] and the L-function
    1-line non-vanishing from mathlib's PNT-in-APs work [M]); nonconstructive
    inf suffices — constants may depend on A.
  - **N4 SMALL-T (B):** |t| ≤ 3: ζ-pole regime helps (t → 0 gives
    D² ≈ 2·loglog x); non-principal χ at t ≈ 0 via `L(1,χ) ≠ 0` [M mathlib];
    seams to price FIRST: t ≈ 1/log x, t ≈ 3, t ≈ T₀.
  - **N5 D2-BOOK (B/C):** `Σ_{p≤x} Re χ(p)p^{−1−it} = Re log L(1+1/log x+it,
    χ) + O(1)`: Euler-log (k ≥ 2 powers O(1)) + Mertens truncation (tail
    p > x at σ = 1+1/log x is O(1)). Corpus scaffolding: `Salt/Mertens/`,
    `SW/EulerBridge`, `SW/MoebiusLog` (names [G]; content-fit unverified).
  - **N6 NONPRET-ASM (B):** ∀A ∃x₀ ∀x ≥ x₀: (1.6) at level A:
    `D² ≥ (1−θ_eff)loglog x − 3·logloglog x − C_A ≥ A`. ⚠ ∃-order coupling
    with the spine's regime builder (`chowlaRegime_exists_param` picks x
    after ε) — map-#1 scope, flag only.

### Route F — faithful-MR (discharges the FULL ∀α door as currently consumed)
- **F1 = M3 + the full [17, Lemma 2.2 + Thm 2.3]:** adds the minor-arc half
  (bilinear Type-II sums from small-prime multiplicativity; Turán–Kubilius /
  Ramaré identity [M]) and the α-uniformity glue. No M1 needed (no bigXi
  structure), no Xi-rewire needed. Strictly larger analytic surface than
  Route M; strictly smaller wiring delta against the landed spine.
- M4 (N1–N6) is needed by BOTH routes — the non-pretentiousness hypothesis is
  consumed by Thm 2.3 and Thm A.1 alike.

**Shared glue (both routes):** the dyadic-X-average → log-measure bridge
(Tao's averaging step in Prop 2.4's proof [G chowla.txt:633–640] vs our
`logMeasure R.x R.ω` integral) — bookkeeping-C, and the o(1)→(δ, H-window)
quantifier translation: the door needs `∫ ≤ δ·H` for ALL H ∈ [R.Hlo, R.Hhi]
of the ONE witnessed regime, any δ ≤ δ₀ — so the port must be quantitative in
H (rate δ(H) → 0) so the builder can be re-run at large Hlo. (Interface
details = map #1.)

---

## 6. EXPONENT LEDGER (everything explicit, one place)

| quantity | value | status |
|---|---|---|
| region log-power θ | **3/4** exactly | [G] GrowthPow.lean:1044 |
| region loglog-correction power | **3** | [G] ibid. |
| region constant c | 10⁻⁹ | [G] flags.md VK-7 block |
| region threshold T₀ | exp(exp(8·log(20000K)+1100))+t₀+3 ("exp(exp ~100)"-grade) | [G] flags + pilot.md:8679 |
| D² coefficient (region-grade bridge) | 1 − 3/4 = **1/4**, minus 3·logloglog x | derived, §4 |
| D² coefficient (3-4-1-anchor-only bridge) | 1 − 13/16 = **3/16**, ℓ-power 9/4 | derived, §5 N1 |
| Littlewood coefficient (RED) | exactly 1 ⟹ D² ≈ logloglog x, bounded-grade | [G] s3-a3-design.md:1076 |
| (1.6) heights | **\|t\| ≤ A·x** (not x^A — memory discrepancy, flagged) | [G] chowla.txt:214 |
| (1.6) character periods | ≤ A (constant) | [G] chowla.txt:213 |
| Tao's W | **log⁵ H** | [G] chowla.txt:624 |
| W-constraint | W ≪ min(A, **(log X)^{1/125}**) | [G] chowla.txt:625 |
| composite H-cap | H ≤ exp((log X)^{1/625}); worst X ≍ (log x)/2 ⟹ H ≤ exp((loglog x)^{1/625}) | derived |
| X-range in Prop 2.4 proof | x/2ω ≤ X ≤ 2x; X ≥ (log x)/2 ≥ (log A)/2 | [G] chowla.txt:632–636 |
| scale ordering | x ≥ n ≥ x/ω ≥ log x ≥ log A ≫ H* | [G] chowla.txt:597 |
| bigXi threshold | ε²/log H | [G] CircleMethod.lean:41 |
| spectrum bound | card(Ξ_H) ≤ K (Lemma 3.5 = `bigXi_bounded`) | [G] |
| door threshold | δ₀ = ε/(2K) | [G] SpineFinal.lean:251 (docstring) |
| regime H-floor | H ≥ 4·10⁶ | [G] SpineFinal.lean:298 |
| MR quantitative error exponents (e.g. the remembered 1/50) | — | **[M] DO NOT USE; stage 1501.04585** |

---

## 7. STAGING ASKS + C2-CHECKLIST FEED

1. **STAGE arXiv:1501.04585 + arXiv:1503.05121** (mandatory). Optional:
   Soundararajan arXiv:2105.11689 as an alternate self-contained MR-core
   porting target [M].
2. On staging 1503.05121: transcribe **Theorem A.1's exact statement**
   (the λ/major-arc minimal surface) and Lemma 2.2 + Thm 2.3's hypothesis
   constants (provenance of 1/125; the W-smoothness form; the α-uniformity
   quantifier positions — must match `∀α`-outside).
3. On staging 1501.04585: settle **entry point 2** (does the MR proof invoke
   the VK region / where; which |t|-range) — decides M3's node count and
   kills-or-confirms the "elementary-Halász-only" claim.
4. Verify mathlib names: `riemannZeta_ne_zero_of_one_le_re`; the
   Dirichlet-L 1-line non-vanishing; `L(1,χ) ≠ 0` [all M].
5. Quantitative-Halász sourcing: MNT-III §23.5 holds the qualitative
   Thm 23.15 [G]; locate the quantitative decay form in MNT-III or stage
   Tenenbaum III.4 [M].
6. The Xi-rewire decision (Route M needs it; Route F doesn't) — couples to
   grounding map #1; **catch #224 scope-diff item: Route M narrows the
   consumed door from `MRTUniformity` to `MRTUniformityXi` — that is a
   freeze-to-freeze scope change and must appear on the diff checklist.**
7. The N1 fork (transport-vs-restructure; the dead naive move is priced in
   §5) — designers must price the evaluation-point seam FIRST at t ≍ Ax.
8. The Ax-vs-x^A heights discrepancy (Option-C memory vs grounded chowla.txt)
   — harmless to the arithmetic, but the freeze must cite the grounded form.
