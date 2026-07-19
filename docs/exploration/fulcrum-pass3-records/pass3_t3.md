# T3 — THE S1 EXCHANGE-RATE CONJECTURE (kill-check, Pass 3)

Status: KC2 run 2026-07-19. KC1 (pair-sieve half character-free) was ALREADY DISCHARGED
in S1's favor — inherited, not re-run (per brief; per-file audit, fulcrum-pass2.md:51).
Verdict: **KILLED as a twin route; wall-theorem candidate BANKED** (the ~20–25% payoff).
Honest-shape law: S1 is a priced lottery ticket throughout; nothing below is a twin route.

## 0. The engine's currency (grounding)

- `LamTilde χ n = ∑_{d|n} μ(d)²·χ_ℝ(d)·log(n/d)` — GROUNDED TwistChain.lean:98-99.
  The engine consumes f ONLY at squarefree d (the μ² factor), i.e. only prime values
  of f matter; `chiRe` enters pointwise with `|χ_ℝ| ≤ 1` (TwistChain.lean:49) and
  `χ_ℝ(aᵏ) = χ_ℝ(a)ᵏ` from `hsq : χ² = 1` (TwistChain.lean:55-59).
- Transfer lower half `S1 ≤ S2`: GROUNDED Transfer.lean:189-192; hypotheses are
  `hsq : χ² = 1` only — pointwise, hence re-typable to any f with f² = 1 (the
  KC1-discharged B-class re-typing).
- The demand: `hb_lemma2` (GROUNDED TransferFull.lean:204-214) squeezes
  `S2 − S1 ≤ C·(x/z₀) + C·(x/log x)·e^{A·z₀}·PretenseSum(χ,N) + junk`, with
  `PretenseSum(χ,N) = ∑_{p≤N, χ(p)=+1} log p / p` (GROUNDED TransferFull.lean:183-185).
  For the squeeze to beat the main term the engine needs **pret(f,N) = O(1)** (indeed
  ≤ δ·e^{−Az₀}-grade). Mertens (classical): `∑_{p≤N} log p/p = log N + O(1)`, so
  pret ranges over [0, log N + O(1)].
- Evaluation half: QuadCharSum.lean — Jacobi sums, `quadraticChar_sum_mul_shift = −1`,
  two-forms bound ≤ 2, complete sums over `ZMod`/finite fields (HB p.217 keystone).
  GROUNDED (file read this session). This technology is **character-rigid**.

## 1. The conjecture, stated

For f real multiplicative, f² = 1 (WLOG determined by ε: Primes → {±1}), define in the
engine's own currency:
- **pretense** `pret(f,N) := ∑_{p≤N, f(p)=+1} log p/p` (TransferFull.lean:183-185 with
  χ_ℝ ↦ f). pret = 0 ⟺ f = λ on primes ≤ N. Quality `pretQ := 1 − pret/log N ∈ [o(1),1]`.
- **evaluability** `eval(f,N)`: existence of an asymptotic `S2(f,A_N) = M(f,N)(1+o(1))`,
  M > 0 explicit, by corpus technology — (E-per) complete-sum/periodicity
  (QuadCharSum-grade, period D ≤ N^{o(1)}) or (E-aut) automorphic.

**EXCHANGE-RATE CONJECTURE (wall candidate).** Under ¬F_eff, no f has both:
`pretQ(f,N) · evalQ(f,N) = o(1)`. Refined two-lemma form:
- **(A — neutrality, unconditional)** `0 ≤ S2(f,A) − S1(A) ≤ EngineBound(pret(f,N))`
  — the transfer exchanges the twin sum for the twisted sum at a rate priced EXACTLY
  by pret(f,N). At pret = O(1), evaluating S2(f) IS evaluating S1.
- **(B — starvation, ¬F_eff)** any f evaluable by (E-per) with period D in the engine
  regime N ≥ D^{C} has the **staircase rate**
  `pret(f,N) = (m_f/φ(D))·log N·(1+o(1)) + O_eff(1)`, `m_f = #{a mod D : f(a)=+1}`,
  and m_f = 0 forces f = λ-mod-finite (→ horn A). (E-aut) is starved UNCONDITIONALLY
  by Hoffstein–Lockhart (no GL(2) Siegel zeros) — MEMORY-staged, FLAGGED, not chased.

## 2. The three poles

**(a) f = λ — TAUTOLOGICAL. CONFIRMED.** pret(λ,N) = 0 (λ(p) = −1 ∀p: the +1-filter at
TransferFull.lean:184 is empty — perfect pretense). But for squarefree d with k prime
factors, λ(d) = (−1)^k = μ(d), so μ(d)²λ(d) = μ(d) and (TwistChain.lean:98-99, verbatim
substitution) `Λ̃_λ = μ∗log = Λ` (classical Möbius–von Mangoldt identity). Hence
S2(λ,A) ≡ S1(A): Transfer.lean:189-192 reads S1 ≤ S1; hb_lemma2's squeeze reads 0 ≤ slot.
Evaluating S2(λ) is VERBATIM the twin problem — and the k=2 kernel witness prices this
corner as parity-hard (twin_bar Impossibility.lean:173, twin_gate_fails :262 —
GROUNDED-inherited, fulcrum-pass2.md:41). Corner: (pretQ = 1, evalQ = 0).

**(b) f = real χ under ¬F — STARVED. CONFIRMED.** evalQ = 1: QuadCharSum.lean is the
p.217 keystone; the full HB evaluation stack is character technology. But ¬F is the
anti-supply: the Siegel zero is the ONLY mechanism by which a real character achieves
pret(χ,N) = o(log N) in the engine regime N = q^{O(1)} (HB works at x ≍ q^{250}-grade —
MEMORY for the exponent; C⁽¹⁾ constants p.223 GROUNDED-inherited via E4). Under ¬F_eff:
pret(χ,N) ≥ (1/2 − o(1))·log N for N ≥ q^{C} (effective PNT for L(s,χ) with no
exceptional zero — MEMORY-classical; this is ledger item A1, fulcrum-pass2.md:25).
Demand is O(1); supply is ≍ log N. Starved by a factor log N.
Corner: (pretQ ≤ 1/2 + o(1) — fatally short, evalQ = 1).

**(c) f = χ₀ (trivial) — WRONGLY TRIVIAL. CONFIRMED.** pret(χ₀,N) = ∑_{p≤N,p∤q} log p/p
= log N + O(1) − O(∑_{p|q} log p/p) = log N + O(1): MAXIMAL pretense-failure (pretQ = o(1)).
Λ̃_{χ₀}(n) = ∑_{d|n,(d,q)=1} μ²(d)log(n/d) is a pure divisor-type object; S2(χ₀) is a
shifted convolution of (μ²·1_{(·,q)=1})∗log — evaluable at divisor-correlation grade,
main term ≫ x·log²x-scale, and S2(χ₀) > 0 already from the d = 1 term (log n) at every
composite n: positivity carries ZERO prime information. Meanwhile hb_lemma2's RHS with
PretenseSum = log N + O(1) is ≍ C·x·e^{Az₀} — the squeeze is vacuous. This pole is the
in-house instance of the H-B C⁽³⁾ vacuity lesson (p.196, standing-rule benchmark):
evaluable positivity without transfer-back is free and worthless.
Corner: (pretQ = o(1), evalQ = 1-but-informationless).

## 3. The interior hunt (the kill)

**Prong 1 — periodic class, staircase exhaustion.** Widest corpus-evaluable class beyond
characters: f with D-periodic prime values (Selberg–Delange: F(s) = ∏_χ L(s,χ)^{c_χ},
c_χ = φ(D)^{-1}∑_a f(a)χ̄(a)). Then pret(f,N) = ∑_{f(a)=+1} ∑_{p≡a,p≤N} log p/p, and in
the engine regime N ≥ D^{C} under ¬F_eff each reduced class carries (log N)/φ(D)
effectively. CATCH #224 (C⋆-regime) honored: unconditional PNT-AP covers only
N ≥ exp(D^ε) — the WRONG regime; the per-class equidistribution at N = D^{O(1)} is
exactly no-Siegel-zero strength, so this prong is ¬F-conditional, as priced.
Conductor-vs-modulus (catch #224): starvation applies to the primitive inducing
character; induced-vs-primitive pretense differs by O(∑_{p|D} log p/p) = o(log N) —
absorbed. So: pret ≤ δ with φ(D) ≪ log N forces m_f = 0, i.e. f(a) = −1 on ALL classes
⟹ f = λ on p ∤ D ⟹ pole (a) up to finitely many Euler factors. Interior EMPTY here:
pretense is quantized in steps of (log N)/φ(D), each ≫ demand.

**Prong 2 — the crack, found and closed (this sharpens the wall).** Devil's advocate:
take φ(D) ≥ log N and m_f = 1 (f = −1 except on one class a₀ mod D). Then
pret(f,N) ≈ (log N)/φ(D) = O(1) — MEETS the demand while f ≠ λ! Starvation does NOT
kill this f. What kills it is NEUTRALITY: μ²f(d) = μ(d)·(−1)^{j(d)} with j(d) = #{p|d :
p ≡ a₀ (D)}, so Λ̃_f − Λ is supported on n having a prime factor ≡ a₀ (D) — an event of
prime log-weight ∑_{p≡a₀,p≤N} log p/p = O(1) — and hb_lemma2's own squeeze (horn A,
re-typed) gives S2(f) = S1 + O(small)·x. Its Dirichlet series is ζ(s)^{−1}·(tiny twist):
λ-pretentious, the anti-ζ direction — the entropy spine's λ-side, non-transporting
(chowla.txt:196-200, GROUNDED-inherited). Any evaluation of S2(f) with positive main
term would hand back S1 ≥ M − o(x·scale) = twins directly: evaluability of THIS f is
identically the twin problem. Complete sums mod D are useless anyway at D ≥ N^{Ω(1)}
window scales. The crack closes by horn A, not horn B — hence the wall needs BOTH lemmas,
and with both it covers ALL of ℱ, not just characters.

**Prong 3 — beyond periodicity.** (E-aut): ±1-valued multiplicative with automorphic
structure ≈ dihedral ≈ character again; and Hoffstein–Lockhart makes GL(2) ¬F a THEOREM
— automorphic surrogates are starved unconditionally. FLAG per brief; MEMORY-staged; do
not chase. Anything else: a new evaluation mechanism for ∑ Λ̃_f(n)Λ̃_f(n+2) at small
pretense is a lower-bound-oriented bilinear estimate in the (n,n+2) configuration with
no character oracle — that is verbatim the demand specification Z (fulcrum-pass2.md:41-43;
Z is a demand spec, not an impossibility theorem). S1 adds no route; it RELABELS Z.

## 4. What an interior f would need (for the record)

(i) pret(f,N) = O(1) — so f = λ on a set of prime log-density 1 − o(1); (ii) an
S2(f)-evaluation NOT factoring through S1 — impossible for (E-per) by Prongs 1–2 and for
(E-aut) by HL; (iii) hence a parity-breaking bilinear mechanism: Z's front door, not S1's.

## 5. The banked wall candidate + vacuity benchmark

**WALL (exchange rate).** For f real multiplicative, f² = 1: (A) unconditionally,
0 ≤ S2(f,A) − S1(A) ≤ EngineBound(pret(f,N)) — the trade's exact rate; (B) under ¬F_eff,
every (E-per)-evaluable f obeys the staircase pret = (m_f/φ(D))·log N + O_eff(1), whose
only demand-meeting points are λ-mod-finite (→ tautology) or φ(D) ≥ log N (→ neutrality);
(E-aut) is HL-starved unconditionally. Corollary: pretQ·evalQ = o(1) over the corpus's
entire evaluation cone.
Benchmark (p.196, binding): the wall is NOT a dichotomy-composite twin claim (no twin
content asserted — honest-shape law); its content is falsifiable — exhibit any f with
pret = O(1) and an S2-evaluation not routing through S1 and it dies — and it prices a
class STRICTLY wider than characters (all prime-periodic f + the large-φ(D) crack).
Non-vacuous against C⁽³⁾: it asserts a quantitative rate at every f, not a disjunction.

**Lean shape (for the wall series, NOT this pass — no Lean-writing):**
W1 pointwise re-typing of Transfer/TransferFull to f (B-class; KC1 basis);
W2 the λ-pole lemma `Λ̃_λ = Λ` (A/B: μ∗log = Λ + μ²λ = μ);
W3 neutrality `|S2(f) − S1| ≤ EngineBound(pret f N)` as the formal rate (C);
W4 prose horn B (¬F_eff staircase + HL flag + catch-#224 regime notes).

## 6. Checklist (standing rules)

- Kill-check RECORDED before any design spend: this file. ✔
- Honest-shape law: no twin route asserted. ✔
- C⁽³⁾ vacuity benchmark addressed (§5). ✔
- Catch #224: real-zeros-only (f²=1 real world — in scope), conductor-vs-modulus
  (absorbed, §3), C⋆-regime (prong 1 is ¬F-conditional, regime-honest). ✔
- Catch #239 fossils: no stale citations used; the FALSE "grep EMPTY" cite replaced by
  the per-file audit version throughout. ✔
- GROUNDED/MEMORY labels: on every load-bearing claim. ✔
