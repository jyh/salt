# PASS 2 — E3 FRESH ARTILLERY: the 2026 corpus priced against ¬F

E3 enumerator, 2026-07-19. NO Lean written. Every claim labeled GROUNDED (file:line)
or MEMORY. ¬F throughout means the negation of `FulcrumQualityMin C⋆`
(GROUNDED Salt/Fulcrum/Basic.lean:61-64):

```
¬F(C⋆) ≡ ∃ Q₀, ∀ q > Q₀ [NeZero q], ∀ primitive quadratic χ ≠ 1 mod q,
          ∀ ρ, LFunction χ ρ = 0 → ‖1-ρ‖·(C⋆·log q) > 1
```

— a uniform fixed-quality COMPLEX zero-free ball at s=1, radius 1/(C⋆·log q), for the
whole family above Q₀. (Negation shape verified against the def: the ∃-witness tuple
(q, NeZero, χ, ρ) with Q < q dies wholesale, leaving the ∀-form above.)

Calibration constant: C⋆ ≥ 2/c₀ with c₀ = 1/126848, i.e. C⋆ ≈ 253696 ≈ 2^18.
GROUNDED-as-doc: Basic.lean:166-169 (hcal residual, "c₀ = 1/126848, risk R6 numeral
extraction owed") + ZeroFreeReal.lean:600-604 (docstring "c₀ = min(1/50456,1/126848)
= 1/126848"; the theorem itself is ∃-shaped — the numeral is design-grade, NOT
kernel-extracted).

---

## D1 — THE SHARPEST: ¬F(C⋆) ⟹ ¬IMSZ, by a LANDED contrapositive

`imsz_gives_fulcrum_witnesses` (GROUNDED Gadget.lean:128-131) is exactly
`InfinitelyManySiegelZeros → ∀ C > 0, FulcrumQualityMin C` (unfolded form, defeq per
its docstring Gadget.lean:23-25). Instantiate at C := C⋆ (0 < C⋆), contrapose:

**¬F(C⋆) ⟹ ¬InfinitelyManySiegelZeros.**

Unfolding ¬IMSZ (def GROUNDED TwinBar/SiegelTwin.lean:85-88, ∀c∃-order):
∃ c > 0, ∀ q > 1 [NeZero q], ∀ primitive quadratic χ ≠ 1, ∀ real β:
LFunction χ β = 0 → β < 1 → β ≤ 1 − c/log q.

This is the **uniform effective no-Siegel-zero standoff for ALL q** — below Q₀ the
gadget arm inside the landed proof (`siegel_zeros_isolated_below`, Gadget.lean:93-96,
consumed at :133), above Q₀ the ¬F ball. Direct constant trace: c = min(c_iso(Q₀), 1/C⋆)
(below Q₀: β ≤ 1−c_iso ≤ 1−c/log q since log q > 1 for q ≥ 3; q = 1, 2 vacuous — mod 1, 2
carry only trivial characters, GROUNDED-as-prose Basic.lean:46-47; above Q₀: β < 1 forced
by `LFunction_ne_zero_of_one_le_re` — same use GROUNDED Basic.lean:159-162 — so
1−β = ‖1−β‖ > 1/(C⋆ log q)).
New Lean needed: ONE contrapositive + de-Morgan unfold — A/B-class. Nothing else; the
gadget is already inside the landed theorem.

**Effectivity**: c is explicit in (Q₀, C⋆) EXCEPT c_iso(Q₀): the cheap-ball ε per
character (Gadget.lean:54-56, `ContinuousAt.eventually_ne` — nonconstructive) minimized
over the finitely many χ of modulus ≤ Q₀. Structure: ONE fixed nonconstructive finite
minimum, not an ε-indexed ineffective family. (In principle each L(1,χ), q ≤ Q₀, is a
computable nonzero number — a decidable per-q certification is plausible future work:
MEMORY, ungrounded.)

## D2 — The three-zone composite: the classical NO-EXCEPTIONAL-ZERO region

¬F(C⋆) + `zero_free_region_all` (GROUNDED ZeroFreeReal.lean:605-608: c₀-region for
(χ²≠1 ∨ Im ρ≠0), Re ρ ≥ 1/2, radius c₀/log(q(|Im ρ|+2))) + gadget ⟹

∃ c₁ > 0, ∀ q [NeZero q], ∀ primitive quadratic χ ≠ 1 mod q, ∀ ρ:
LFunction χ ρ = 0 → 1/2 ≤ Re ρ → **Re ρ ≤ 1 − c₁/log(q(|Im ρ|+2))**.

Case check (done this pass, honest): Im ρ ≠ 0 → ZFR arm (any q). Im ρ = 0, q ≤ Q₀ →
gadget arm (real form suffices — no complex-ball need below Q₀ for THIS shape).
Im ρ = 0, q > Q₀ → ¬F arm; conversion 1−β > 1/(C⋆ log q) ≥ c₁/log(2q) holds for
c₁ ≤ 1/C⋆ since log(2q) ≥ log q. Take c₁ = min(c₀, 1/C⋆, c_iso(Q₀)).
This is the FULL classical zero-free region with the Siegel carve-out (S3e territory,
ZeroFreeReal.lean:603) CLOSED — the exact analytic input for effective PNT-in-APs.
New Lean: B-class glue. Effectivity: as D1 (single nonconstructive c_iso).

## D3 — The complex ball at 1 for ALL q (the brief's composite, scope-corrected)

CATCH #224 SCOPE-DIFF: the landed gadget is REAL-zero-only (β : ℝ binder,
Gadget.lean:94-96). The brief's "¬F + gadget = zero-free ball at 1 for ALL q" needs,
below Q₀, the COMPLEX ball — NOT landed, but the landed proof route already yields it:
`isolation_char`'s `eventually_ne` ball is over nhds (1 : ℂ) (Gadget.lean:54-56) and is
restricted to ℝ only in the statement. One new A/B-class node (complex re-statement +
finite min) gives:

∃ c₂ > 0, ∀ q ≥ 3 [NeZero q], ∀ primitive quadratic χ ≠ 1, ∀ ρ:
‖1 − ρ‖ ≤ c₂/log q → LFunction χ ρ ≠ 0.

(above Q₀: c₂ ≤ 1/C⋆ from ¬F directly; below: c₂ ≤ (min_q ε_q)·log 3.)
This is the precise composite statement; prefer D1/D2 as deliverable surfaces (landed
routes), keep D3 as the one-cheap-node upgrade.

## D4 — Hygiene: ¬F's marginal content is EXACTLY the real zeros

At calibrated C⋆ ≥ 2/c₀ the complex part of ¬F's ball is ALREADY unconditional — that
is `fulcrum_zero_real`'s content (GROUNDED Basic.lean:93-103: any ball witness is real,
via the ZFR disjunction; ball radius < 1/2 forces |Im ρ|+2 < 3 ≤ q). So above Q₀,
¬F adds nothing about complex zeros beyond zero_free_region_all. Any Pass-2 claim
crediting ¬F with complex-zero exclusions at calibrated C⋆ DOUBLE-COUNTS the landed
ZFR. All pricing below uses only the real-zero standoff.

## D5 — dh_repulsion_ordered (T-BAL R8) under ¬F: window does NOT empty; conclusion SUBSUMED

Landed contract (GROUNDED TBalR8.lean:1752-1759): b = 680, k = 14, c an explicit
min-tower with c ≤ 2^(−250) (hc_t1, TBalR8.lean:1796; witnesses supplied at :1836);
hypotheses: primitive quadratic χ, q ≥ 2, real zero β₀ ∈ (1/2, 1), complex zero ρ with
Im ρ ≠ 0, |Im ρ| ≤ 1, 16/17 ≤ Re ρ < 1, Re ρ ≤ β₀; conclusion
1−β₀ ≥ c·(q(|Im ρ|+2))^(−680(1−Re ρ))/(log(q(|Im ρ|+2))+2)^14.

(a) **The β₀ window does NOT empty under ¬F** — the brief's "or does it?" resolves NO.
Survivors: q > Q₀: β₀ ∈ (1/2, 1 − 1/(C⋆ log q)]; q ≤ Q₀: β₀ ∈ (1/2, 1 − c_iso(Q₀)].
Only the deep band (1 − 1/(C⋆ log q), 1) empties. The theorem never becomes vacuous.
(b) **Subsumption above Q₀**: the rpow factor ≤ 1 (base ≥ 4, exponent ≤ 0) and the
denominator ≥ 1, so the conclusion RHS ≤ c ≤ 2^(−250), and more precisely
RHS ≤ 2^(−250)/(log q)^14. ¬F's direct floor is 1/(C⋆ log q). RHS ≤ floor for ALL
q ≥ 3 whenever C⋆ ≤ 2^(250)·(log 3)^13 — and calibrated C⋆ ≈ 2^18 ≪ 2^250. So for
q > Q₀ **every instance of the repulsion conclusion is strictly weaker than what ¬F
already gives**: dh_repulsion_ordered is INEFFECTIVE (fully subsumed) on the ¬F side
above Q₀. (c) Below Q₀: both give constants; c_iso nonconstructive vs c ≤ 2^(−250)
explicit — INCOMPARABLE, no domination claim. (d) Verdict: T-BAL R8 is F-side
artillery (repelling zeros NEAR a deep β₀ that F supplies); it cannot amplify ¬F
(its grade (log)^(−14) sits below the (log)^(−1) floor).

## D6 — ¬F ⟹ effective `siegel_theorem`: the SW arc's single ineffective step falls

The landed SW chain's only flagged ineffectivity is Siegel (GROUNDED All.lean:118
"Siegel's intrinsic ineffective constant"; the ineffective choice: Siegel.lean:220-224
exceptional-branch dichotomy; consumer slot: Fold.lean:167 `siegel_theorem ε`).
Statement (GROUNDED SiegelClose.lean:841-844): ∀ε>0 ∃C>0, primitive quadratic real
zeros obey β ≤ 1 − C/q^ε.
Under ¬F, D1's standoff β ≤ 1 − c₁/log q implies this with **effective**
C(ε) = c₁·inf_{q≥3}(q^ε/log q) > 0 (inf attained, explicit in ε and c₁) — for large q,
1/log q ≫ q^(−ε), so the ¬F standoff strictly dominates Siegel's window. Consequence:
an effective-K variant of `Salt.BV.SiegelWalfisz` (def GROUNDED BV/Defs.lean:35-38)
through the landed Gate chain (`siegelWalfisz_holds`, Gate.lean:150), with K explicit
in (A, C, Q₀, C⋆) modulo the single c_iso(Q₀) input. This is C-class re-tracing work
(the claim is the OBSTRUCTION is removed, not that constants are traced today).
Consumers: the BV chain (`bounded_gaps_of_siegelWalfisz` — MEMORY project_bv) and the
explicit12 flagship, where ineffective Siegel constants are the classical plague on
explicit gap bounds (MEMORY-tier framing).
CATCH #239 FOSSIL noted: BV/Defs.lean:31-33 still says SW is "absent from every Lean
artifact as of 2026-07" — falsified by Gate.lean:150.

## D7 — The χ-twist question (Vk chain × ¬F): NO direct combination; the four needs

`zeta_zero_free_region_pow` (GROUNDED GrowthPow.lean:1044-1047: ζ-zeros of height
≥ T₀ obey Re ρ ≤ 1 − c/((log|Im ρ|)^(3/4)(loglog|Im ρ|)^3)) and `zeta_lower_all_t`
(GROUNDED ZetaLowerAllT.lean:273-277: c''/((log(|t|+3))^(3/4)(loglog(|t|+16))^4) ≤
‖ζ(1+d'+it)‖, d' ∈ [0,1], pole point excluded) are ζ-ONLY, t-aspect statements; ¬F is
a q-aspect fixed-quality statement at s=1. Disjoint aspects — they compose only through
a NOT-YET-EXISTING VK-for-L chain. What that chain needs (enumerated, all MEMORY-tier
classical routes except where noted):
 (i) L front end — analog of GrowthPow's `zeta_sub_dirichlet_bound` with χ-twisted
     partial sums; nonprincipal tails cheap by Pólya–Vinogradov; q-uniformity forces
     length ≍ (q(|t|+2))².
 (ii) twisted block dispatch — χ constant on residue classes mod q, so the sub-Weyl
     blocks split into ≤ q classes: cost factor q. Pow-grade survives in the t-aspect
     with q-growing thresholds T₀(q) (e.g. log T₀ ≍ q^ε); family-uniform POW-IN-q is
     NOT reachable. HONEST-SHAPE LAW: never claim (log q)^(3/4)-grade in q — ¬F's
     quality is the FIXED constant 1/C⋆ and cannot be amplified.
 (iii) the 3-4-1 emission's third leg: for quadratic χ, χ² = χ₀ and L(s,χ₀) =
     ζ(s)·∏_{p|q}(1−p^(−s)); on Re s ≥ 1 each factor ≥ 1−1/p, product ≥ ∏_{p|q}(1−1/p)
     ≫ 1/loglog q (Mertens — MEMORY). **So `zeta_lower_all_t` IS the artillery for the
     twisted 3-4-1's χ₀ leg, at an honest (loglog q)^(−1) cost** — the precise sense in
     which the fresh all-t bound serves the family. Its ¬(d'=0 ∧ t=0) carve-out is
     harmless (the 3-4-1 evaluates at d' > 0).
 (iv) the t ≈ 0 hole: for real χ the 3-4-1 degenerates at t → 0 (the Landau/Siegel
     obstruction — MEMORY). ¬F plugs EXACTLY this hole and nothing else: the ball
     ‖1−ρ‖ ≤ 1/(C⋆ log q) is the unique corpus coverage there.
Resulting family region under ¬F + future VK-L: THREE-ZONE — ball at 1 (¬F),
1/log(q(|t|+2))-grade for all t (zero_free_region_all + D2), pow-grade for
|t| ≥ T₀(q) (VK-L). D-class campaign; the zones are complementary, not redundant.

## D8 — ¬F ⟹ HeathBrownStatement, vacuously

`HeathBrownStatement ≡ IMSZ → TwinPrimeConjecture` (def GROUNDED SiegelTwin.lean:92-93).
D1 gives ¬IMSZ, so the HB-ENGINE campaign target (DHRepulsion.lean:331-333 honesty
block; MEMORY project — HB-ENGINE registered future campaign) is TRUE-BUT-INERT on the
¬F side: the engine can never fire. Dichotomy bookkeeping made exact: F-side = the HB
engine manufactures twins; ¬F-side = effectivity harvest (D1/D2/D6), NOT a known route
to TPC. No known classical route derives twins from ¬F — the honest death map.

## D9 — The spine and λ-nonpret: dichotomy-INVARIANT; do not oversell ¬F

`lambda_nonpret_of_bridge` (GROUNDED NonPret.lean:114-123) is the ζ-only (χ=1) leg,
conditional only on the Euler-bridge residual — untouched by ¬F. The spine terminal
`log_chowla_two_final` (GROUNDED SpineFinal.lean:416-428) is gated on `MRTUniformity`
(def GROUNDED MRTDoor.lean:48-50, exponential-sum L¹ door) + the AM-GM residual —
no Dirichlet-character family input at growing modulus. The S5 split form fixes Q
BEFORE x₀ (GROUNDED NonPret.lean:120: ∀ Q ≥ 1, ∃ x₀ C, …), so future χ-legs need only
FIXED-q L-lower bounds: compact-min per character (pattern GROUNDED
ZetaLowerAllT.lean:44-47) + a fixed-q VK-L twist (class-splitting cost q = O_Q(1) —
cheap instance of D7(ii)). **¬F is NOT needed anywhere on the spine.** ¬F buys only
the uniform-in-q (q growing with x) nonpret that a QUANTITATIVE Chowla/twin-count
would demand — real but distant. HONEST-SHAPE: no ¬F-to-spine claim.

## D10 — ShiuCore/strip stack: invariant substrate + the one missing cash-out node

`ShiuCore` (def GROUNDED ShiuBlocks.lean:292-297; landed as `sum_tau_in_ap_le`,
ShiuS5b.lean:628) has NO zero-theoretic input — dichotomy-invariant, serves both
branches unchanged (consumers: `shiu_for_blocks_of_core` ShiuBlocks.lean:312, the
Maynard/GehShiuWire blocks). Under ¬F it remains the AP-divisor workhorse for any
effective sieve re-run (pairs with D6's effective SW).
THE MISSING NODE that would let ¬F feed L(1)-grade consumers (χ-legs of nonpret at
growing q, class-number-grade bounds): the classical converse cash-out
"no real zero in (1−δ, 1) ⟹ L(1,χ) ≫ δ" — the corpus holds only the OTHER direction
(`LFunction_one_re_le_mvt_sharp`: (L(1,χ)).re ≤ (1−β₀)·25e(1+log f)², cited
DHRepulsion.lean:317-319). The positivity substrate it needs is LANDED (dhA = 1∗χ
nonnegativity + detector floor, DHRepulsion.lean:36-41, M2 landed per :256-257).
New C-class node; classical route MEMORY-tier. With it: ¬F ⟹ L(1,χ) ≫ 1/(C⋆ log q)
uniformly for q > Q₀.

---

## Constants ledger (one table)

| piece | constant | status |
|---|---|---|
| ¬F ball | 1/(C⋆ log q), C⋆ ≈ 253696 = 2/c₀ | explicit given calibration; numeral extraction owed (Basic.lean:169) |
| ZFR | c₀ = 1/126848 | ∃-shaped; numeral in docstring only (ZeroFreeReal.lean:604) |
| gadget below Q₀ | c_iso(Q₀) | nonconstructive (eventually_ne), finite min |
| repulsion | b=680, k=14, c ≤ 2^(−250) | fully explicit min-tower (TBalR8.lean:1776-1796) |
| zeta_lower_all_t | c'' | ∃-shaped; compact-min nonconstructive arm (ZetaLowerAllT.lean:44) |
| siegel_theorem | C(ε) ineffective | becomes effective under ¬F: C(ε)=c₁·inf_q(q^ε/log q) |

## Catches

- #224 scope-diffs: gadget = REAL zeros only (D3); repulsion hypotheses 16/17-window +
  ordering + |Im ρ| ≤ 1 (D5 compares conclusions only inside scope); ¬F marginal
  content = real zeros at calibrated C⋆ (D4).
- #239 fossil: BV/Defs.lean:31-33 "absent from every Lean artifact as of 2026-07" —
  stale since Gate.lean:150 landed.
