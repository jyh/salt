# The twin-bar rung — `M₂ ≤ 2·log 2 < 2` (`twinbar`)

**STATUS: RUNG COMPLETE (2026-07-12, single sitting, every node
first-attempt).** The three frozen headliners are LANDED byte-faithful in
`Salt/TwinBar/Impossibility.lean`: **`twin_bar`** (J₁+J₂ ≤ 2log2·I₂),
**`twin_gate_fails`** (θ-form, all θ ≤ 1), **`no_twin_weight`** (the ¬∃
headline) — the first machine-checked negative result about a sieve
method, the exact dual of the landed `M5_cert`. Axiom-clean, 0 sorry,
9 project headliners lint-audited. Chain as designed: `logWeight` (T2) →
`interval_CS`/`sliceCS` (T3, the signed-safe discriminant CS — mathlib
lacked it) → `simplex_swap` (T4, STRONGER than frozen: no sign condition;
first 2-D integration in the corpus) → the assembly (T5+T6; the
integrability plumbing dissolved via `integral_mono_of_nonneg` +
Fubini-marginals — no Tietze, no PB-floor anywhere). T7 rational tie
remains the designed follow-on.

*Fable, 2026-07-12. Ratified by the user as the flagship: NEW-mathematics
artifact — the first machine-checked negative result about a sieve method.
Design recon: the session's design memo (Polymath8b arXiv:1407.4897,
Lemma 6.1 + Cor. 6.4 — NOT Maynard 1311.4600, which lacks the upper
bound). Track branch `twinbar`. The statement chain hand-verified by
Fable; the lean adversarial check PASSED 2026-07-12 (against the
extracted Polymath8b PDF: carriers faithful to eq. 31–33 at k = 2, chain
re-derived, the w's = exactly Cor 6.4's `1/(G_i·log 2)`, gate polarity
the literal negation of `M5_cert`/`theta_ratio_cert`, all hooks present
in the pin; ONE correction folded — T3's signed-weights route; scope
remarks added).*

## What this rung IS (the honesty contract — read before any prose claim)

**Claim:** for the twin tuple `{0, 2}` (k = 2), the Maynard–Selberg
variational gate `θ·(J₁+J₂) > 2·I₂` is unsatisfiable by ANY continuous
weight at ANY level of distribution `θ ≤ 1` — because
`J₁(F) + J₂(F) ≤ 2·log 2·I₂(F)` and `2·log 2 < 2`.

**What it does NOT claim:** that "sieves cannot prove twin primes."
Parity-breaking inputs (bilinear/type-II information à la
Friedlander–Iwaniec, Chen's switching) modify the functional; this bound
does not apply to modified functionals. The theorem certifies the exact
boundary of the UNMODIFIED Maynard class: no better `F`, no better
equidistribution level, can cross it. This scoping goes in every
docstring verbatim-in-spirit.

**Scope remarks (verify pass, 2026-07-12):** (a) the Lean theorems are
per-F bounds over CONTINUOUS F; Polymath8b's `M₂` (eq. 33) is an L²-sup
— the standard density bridge upgrades our bound to the sup; state the
artifact as "over continuous weights" and put the density remark in the
docstring rather than claiming the L²-sup formally (a possible later
strengthening, NOT the floor). (b) H2 covers θ = 1 — a SUPERSET of
Theorem 3.8's `ϑ < 1` range; stronger, and not an assertion that ϑ = 1
is an admissible EH level (EH[1] is false). (c) `Poly`-class membership
is true in spirit (polynomials are continuous); the machine connection
is T7 (excluded).

**The duality:** this is the negative dual of the landed `M5_cert`
(`2·Ical Fstar < Σ Jcal m Fstar`, k = 5) and `theta_ratio_cert`. Same
framework, both directions machine-checked: what the method can do
(gaps ≤ 12, ≤ C mod SW) and what it cannot (twins, ever).

## Doctrine

Iron rules per `CLAUDE.md`. Namespace `Salt.TwinBar`, files
`Salt/TwinBar/*.lean`, aggregate `All.lean` wired into `Salt.lean` at
first commit, `#audit_axioms` block from the start. Constants explicit.
The `lintegral`-first lever (below) is the standing recommendation for
every integrability-adjacent node. NEW-to-corpus machinery: 2-D
integration (the corpus has only 1-D `intervalIntegral` — every 2-D step
is greenfield; mathlib hooks verified present in the design memo).

## Carriers (Fable-frozen; nested-1D formulation matching corpus idioms)

```lean
def I₂ (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), (F t₁ t₂) ^ 2
def J₁ (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₂ in (0:ℝ)..1, (∫ t₁ in (0:ℝ)..(1 - t₂), F t₁ t₂) ^ 2
def J₂ (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₁ in (0:ℝ)..1, (∫ t₂ in (0:ℝ)..(1 - t₁), F t₁ t₂) ^ 2
def R₂ : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
```
(These match Polymath8b eq. (31)–(33) at k = 2; the inner integral is the
`contractAt` peel, consistent with the landed `Jcal`. Regularity
hypothesis for all theorems: `ContinuousOn (Function.uncurry F) R₂` —
the honest sweet spot: contains every sieve weight incl. all `Poly`,
makes all integrability side-conditions derivable. F outside R₂ never
enters any carrier: hypotheses about support are NOT needed — verify
this claim per-node, it holds because every integration range is inside
the slice.)

## The frozen headliners

```lean
-- H1, the mathematical keystone
theorem twin_bar (F : ℝ → ℝ → ℝ) (hF : ContinuousOn (Function.uncurry F) R₂) :
    J₁ F + J₂ F ≤ 2 * Real.log 2 * I₂ F

-- H2, the θ-parameterized gate failure (the landed theta_ratio_cert dialect)
theorem twin_gate_fails (F : ℝ → ℝ → ℝ) (hF : ContinuousOn (Function.uncurry F) R₂)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    θ * (J₁ F + J₂ F) ≤ 2 * I₂ F

-- H3, the headline impossibility (¬∃ — the dual of M5_cert's existence)
theorem no_twin_weight :
    ¬ ∃ F : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry F) R₂ ∧
      0 < I₂ F ∧ 2 * I₂ F < J₁ F + J₂ F
```
(H2 needs `0 ≤ J₁+J₂` (squares) and `0 ≤ I₂` — prove as N1 trivia. H3
from H1 + `2 log 2 < 2`. The strict `<` in `2·I₂ < J₁+J₂` with the
`0 < I₂` guard is the exact k=2 analogue of the landed `M5_cert` shape.)

## The proof chain (Polymath8b Lemma 6.1 at k = 2; hand-verified)

Weights `w₁ (t₁,t₂) := 1 − t₂ + t₁`, `w₂ := 1 − t₁ + t₂`; on R₂ both lie
in `[0, 2]` and **`w₁ + w₂ ≡ 2`** (the magic). Per t₂-slice with
`a := 1 − t₂ ≥ 0`:
(i) `∫₀^a dt₁/(a + t₁) = log 2` (a > 0; the `a` cancels — uniformity);
(ii) CS: `(∫₀^a F)² ≤ (∫₀^a 1/w₁)·(∫₀^a w₁F²) = log 2·∫₀^a w₁F²`
(a = 0 slice trivially 0 ≤ 0);
(iii) integrate in t₂: `J₁ ≤ log 2·∬_{R₂} w₁F²`;
(iv) symmetric for J₂ + ONE Tonelli swap to land both on the same
iterated order — THE novel-to-corpus 2-D step;
(v) `w₁+w₂ = 2` ⇒ `J₁+J₂ ≤ log 2·∬ 2F² = 2 log 2·I₂`;
(vi) `log 2 < 1` (`Real.log_lt_sub_one_of_pos`-route or `log_two_lt_d9`).

## Node catalog

| id | content | class | status |
|---|---|---|---|
| T1 ✅ | Carriers + trivia: `0 ≤ I₂/J₁/J₂` (squares); slice integrability from `ContinuousOn` (compact slices ⇒ bounded ⇒ intervalIntegrable); the `Function.uncurry`/slice-continuity plumbing | B–C | ⬜ |
| T2 ✅ | `logWeight : 0 < a → ∫ t in (0:ℝ)..a, (a + t)⁻¹ = Real.log 2` (via `integral_inv`/`integral_one_div` + shift; `log (2a) − log a = log 2`) | A–B | ⬜ |
| T3 ✅ | `sliceCS : (∫₀^a F·)² ≤ Real.log 2 · ∫₀^a w₁·F²` per slice. ⚠️ ROUTE (verify pass): the L² inner-product CS (`abs_inner_le_norm`/`inner_mul_le_norm_mul_norm`) is PRIMARY — sign-agnostic, and the Maynard weights are SIGNED (`Fstar` has negative coefficients), so `integral_mul_le_Lp_mul_Lq_of_nonneg` does NOT apply raw (nonneg hypotheses; usable only after `(∫F)² ≤ (∫|F|)²`, and it returns the un-squared form). a = 0 slice trivial. | B–C | ⬜ |
| T4 | the simplex order-swap — LANDED STRONGER than frozen: `simplex_swap (G)(hG : ContinuousOn …) : iterated(t₂-outer) = iterated(t₁-outer)` — NO nonnegativity needed (Fable dropped the inert hypothesis): the executor assessed both routes and chose Bochner–Fubini (`integral_prod_symm`/`integral_prod` through the single 2-D indicator integral; `ContinuousOn.integrableOn_compact'` on the compact R₂ + `integrable_indicator_iff`), which needs only integrability — the `lintegral` lever was the costlier route (ofReal/toReal round-trip). First 2-D integration in the corpus. `Salt/TwinBar/Tonelli.lean` | **C** (low end) | ✅ |
| T5 ✅ | `combine : J₁+J₂ ≤ 2·log 2·I₂` (pointwise `w₁+w₂ = 2`, `integral_add`, mono) | A–B | ⬜ |
| T6 ✅ | H1/H2/H3 assembly + `two_log_two_lt_two` | A–B | ⬜ |
| T7 | *(follow-on rung, NOT this one)* the rational tie: `∬_{R₂} eval (sq p) = (simplexInt p : ℝ)` at n = 2 ⇒ the `Poly`-class corollary (mathlib has NO multivariate Dirichlet-integral lemma — ~6–8 h greenfield; EXCLUDED from the floor) | C | ⬜ (excluded) |

## PB-floors
- The rung is DONE at T6 (H1+H2+H3). Floor estimate 11–15 h.
- De-risk fallback if T2 fights (it removes ONLY T2 — T4's Tonelli
  remains either way): the log-free weight `G_i = (1−t_{≠i})⁻¹` gives
  `J₁+J₂ ≤ 2·I₂` NON-strict — which still refutes the STRICT gate
  `2·I₂ < J₁+J₂` at EVERY θ ≤ 1 including 1 (verify pass: `≤` negates
  `<`; the only loss is the strict margin and the quotable 2·log 2).
  Land it as the floor + flag; the strict bound remains the target.
- T7 is a follow-on; do not let it creep in.

## Statement-design decisions reserved to Fable
Any change to H1/H2/H3 shapes; the regularity class (continuity is
frozen; L² generalization is a possible LATER strengthening, never a
requirement); all prose scoping claims (the honesty contract above).
