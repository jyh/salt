# PASS-3 T2 — S3 Q-RANGE KILL-CHECK: **KILLED** (2026-07-19)

QUESTION (fulcrum-pass2.md:69): does a rate-version 2-point log-Chowla demand character
information at growing moduli (where ¬F's polylog floors matter), or do unconditional
q^{-1/2} floors suffice for every demand the landed spine + a rate upgrade could make?

VERDICT: **S3 DIES — same-day, both kill modes fire.** The demand conductor range is
triple-log in x; ¬F's floors have marginal content only at polylog-in-x moduli. The gap
is two iterated exponentials and cannot be crossed by any rate upgrade of this
architecture.

## Leg 1 — STRUCTURAL (the predicted kill mode, fulcrum-pass2.md:91): the landed spine is q-free

- `ChowlaRegime` (Salt/Entropy/Chowla/Regime.lean:56-96) has fields x, ω, a, eps, Hlo,
  Hhi, C0, J — **no modulus field exists**. GROUNDED.
- The sole residual door of `log_chowla_two_final` (SpineFinal.lean:416-427) is
  `MRTUniformity R δ` (MRTDoor.lean:48-50): an `e(αj)`-twisted window exponential sum,
  ∀α real — **no characters, no moduli**. GROUNDED.
- The S5 split form (Salt/MR/NonPret.lean:104-123) is `pretDistSq lam (costwist t) x` —
  the q=1 twist family n^{it} only; bound `(1/4)loglog x − 4·logloglog(|t|+16) − C`,
  heights |t| ≤ Q·x. GROUNDED.

No growing-q demand exists anywhere in the landed structure. S3's "feed χ-legs of a
quantitative spine" has no consumer.

## Leg 2 — ARITHMETIC (the ceiling for ANY rate upgrade of this architecture)

**(a) Demand size = conductor range = the same parameter A.** Tao Thm 1.3
(chowla.txt:206-230) and its reduction Thm 2.3 + hypothesis (2.3) (chowla.txt:552-611):
non-pretentiousness distance ≥ A demanded for all χ of **period ≤ A**, |t| ≤ Ax.
GROUNDED. A rate version quantifies ε(x)→0 via A(x)→∞; the conductor range grows only
as the demand size grows.

**(b) Satisfiability cap: A ≤ 2·loglog x + O(1).** For g₁ = λ and χ₀ mod 1, t = 0:
𝔻(λ,1;x)² = Σ_{p≤x} 2/p = 2loglog x + O(1) (Mertens; MEMORY, elementary). Hypothesis
(2.3) with larger A is unsatisfiable — the theorem goes vacuous. Sharper: the landed
q=1 supply floor is (1/4)loglog x − o (NonPret.lean:114-118 + ZetaLowerAllT.lean:270-273,
GROUNDED), so the *usable* A is ≤ (1/4)loglog x. Either constant kills.

**(c) Where the proof consults characters: W := log⁵H.** Prop 2.4's proof
(chowla.txt:622-640, GROUNDED): "Applying [17, Lemma 2.2, Theorem 2.3] (with W := log⁵H,
noting that this is much less than A or (log X)^{1/125})". Characters enter ONLY here
(and only at major-arc α, chowla.txt:748). Hierarchy (chowla.txt:~590): 1/ε ≪ H₋ ≪ H ≪
H₊ ≪ A. So the operative conductor range of the entire architecture is

  **q ≤ log⁵H₊ ≤ log⁵A ≤ (log(2loglog x))⁵ ≈ (logloglog x)⁵ — triple-log moduli.**

**(d) Supply comparison at triple-log moduli.** In 𝔻(λ, χn^{it}; x)² = loglog x +
log|L(1+1/log x+it, χ)| + O(1) (standard Euler-product split; the q=1 instance is the
repo's own bridge stone, NonPret.lean:114-118):
- Unconditional effective L(1,χ) ≫ q^{-1/2} (Landau/class-number; MEMORY): additive loss
  (1/2)log q ≤ (5/2)·log₄x. Complex-χ / t-away regime: unconditional zero-free-region
  floors, log₃-grade loss (the landed q=1 VK shape already pays the dominant
  −(3/4)loglog(|t|+3), q-independent).
- ¬F floor L(1,χ) ≫ 1/(C⋆ log q) (the S3 ledger claim, fulcrum-pass2.md:55): loss
  loglog q + log C⋆ = log₅x-grade.
- **¬F's marginal content: ≤ (5/2)·log₄x, against a demand-supply slack of Ω(log₂x).**
  Three iterated-exponential orders below relevance.

**(e) The crossing is impossible.** ¬F beats q^{-1/2} materially only when (1/2)log q ≍
loglog x, i.e. q ≍ (log x)² — polylog moduli. Reaching that conductor range needs
A ≥ q ≥ (log x)² ≫ 2loglog x = the satisfiability ceiling from (b). Decoupling demand
size B from range Q doesn't help: the hypothesis is consumed only through Prop 2.4's
W = log⁵H ≤ log⁵A slot — conductors above it are idle strength (vacuous supply, not
demand).

## Checklist (standing rules)

- Catch #224 conductor-vs-modulus: "period ≤ A" is modulus; ¬F floors are per-conductor;
  induced-character correction at these ranges is O(loglog q) = log₄x-grade — immaterial,
  same verdict. Real-zeros-only scope: ¬F's improvement targets exactly the real-χ/t≈0
  Siegel regime, where q^{-1/2} already overserves by two exponentials — the scope
  restriction makes S3 weaker, not stronger.
- H-B C⁽³⁾ vacuity benchmark: a "¬F ⟹ rate-Chowla" composite would improve the rate
  through a log₅x-grade term in a correction already four logs deep — fails any benchmark
  trivially. No composite is claimable.
- Honest-shape law: S3 was never a twin route; it is now not even a lottery ticket.
- Odds update: <1% twins → 0; "~15% a ¬F-conditional quantitative-Chowla node worth
  landing" → ~0 (the conditional node's content is a log₅x-vs-log₄x refinement); the
  ~50% same-day-death estimate was indeed generous to survival.

## Scope note (honesty)

The kill is relative to the entropy-decrement architecture (the landed spine + Tao
arXiv:1509.05422v1), exactly as the brief specifies. A hypothetical power-saving 2-point Chowla
demanding polylog-x conductors would be a different architecture and a NEW supply
question — it is not S3, which was defined (fulcrum-pass2.md:55) as feeding χ-legs of
THIS quantitative spine.

## Banked wall-theorem candidate

**TRIPLE-LOG CONDUCTOR CEILING.** In the entropy-decrement architecture, any rate-version
2-point log-Chowla consumes character information only at moduli q ≤ log⁵H₊ ≤
(log(2loglog x))⁵, because the non-pretentiousness demand size and the conductor range
are the same parameter A, capped at 2loglog x by χ₀-satisfiability. At that range
unconditional effective q^{-1/2} floors overserve every possible demand by two iterated
exponentials. Corollary: the landed spine's q-free shape (`ChowlaRegime` without a
modulus field) is the CORRECT shape, not a simplification — and Siegel-zero character
supply has zero marginal content for this spine, permanently.
