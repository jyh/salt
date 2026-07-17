# s3-a3-design — the log-Chowla spine, wave 3 (A-R3 W3)

Frozen by the A3-W3R recon, adjudicated by the house 2026-07-19.
Paper: Tao, arXiv 1509.05422 (page-image fidelity; the cached PDF +
`chowla_pages/` in the session scratchpad). Model instantiation
throughout: `a = 1, b = 0, h = 1, c_p = 1` (the Liouville case).

## Page-fidelity transcriptions

**(3.15)** — p. 22 (bottom):

    | E (1/P_H) ∑_{y ∈ ℤ/P_Hℤ} F(X_H, y) |  ≫  ε · H/log H

**(3.16)** — p. 23 (top; after the `g_{i,ε²} → g_i` replacement at
cost `O(ε² H/log H)`):

    | E ∑_{p∈𝒫_H} (c_p/p) ∑_{j : j, j+ph ∈ [1,H]} 1_{j ≡ pb (a)}
        · g₁(a n + j) · g₂(a n + j + ph) |  ≫  ε · H/log H

(`n` = the log-uniform random integer; `E` over `n`.)

**Lemma 3.4 (circle method estimate)** — p. 23, defs pp. 23–24:
`S_H(α) := ∑_{p∈𝒫_H} (c_p/p) e(αp)` (3.17); `Ξ_H` := the `ξ ∈ ℤ/Hℤ`
with `|S_H(−(b+h)η/a − hξ/H)| ≥ ε²/log H` for some `η ∈ ℤ/aℤ`; then
for `|x_{i,j}| ≤ 1`:

    ∑_{p∈𝒫_H} (c_p/p) ∑_{j : j,j+ph∈[1,H]} 1_{j≡pb (a)} x_{1,j} x_{2,j+ph}
      ≪_{a,h}  (H/log H) · ( ε² + ∑_{ξ∈Ξ_H} (1/H) |∑_{j=1}^H x_{1,j} e(−jξ/H)| )   (3.18)

Proof substrate (p. 24): `G_i(ξ) := (1/H) ∑_j x_{i,j} e(−jξ/H)`,
Fourier inversion, and Plancherel/Cauchy–Schwarz
`∑_ξ |G_1(ξ)||G_2(ξ + (H/a)η)| ≪ 1`.

**Model collapse check** (`a=1,b=0,h=1,c_p=1`): the (3.18) LHS is
exactly the RHS of `fBridgeF_mean` — W3-b bounds precisely the object
W3-a produces. The seam is tight.

## Landed at adjudication (house ceremony, no executor)

- `Salt/Entropy/Chowla/Decoupled.lean` — **W3-a-1** `fBridgeF_mean`,
  **W3-a-2** `fBridge_concentration_decoupled` (the recon's validity
  probes WERE full proofs; class A each).
- `Salt/Entropy/Chowla/CircleMethod.lean` — **W3-b-defs**: `expSum`
  (3.17), `bigXi` (Ξ_H at `a=1`), `dft_is_fourier_coeff` (the
  carrier bridge, = `ZMod.dft_apply`).

## The frozen W3-b-main statement — RE-FROZEN v2 (2026-07-19)

**⛔ THE v1 FREEZE WAS FALSE** (W3-b-main executor STOP-AND-FLAG,
zero proof attempts wasted). Counterexample family: `eps = 1/k`,
`H = 5k²` (so ε²H = 5, 𝒫_H = {3,5}), `x1 = x2 ≡ 1`: LHS = Θ(H) but
RHS = Θ(H/log H); LHS/RHS = Θ(log H) unbounded — violated at k = 10
for C = 1, at k = 10⁶⁰ for C = 100. ROOT CAUSE: the v1 vacuity
guard (uniform C over ALL (eps,H)) over-corrected into falsity —
Tao's Lemma 3.4 is regime-gated: his p. 22 uses the PNT bound
`|𝒫_H| ≪ ε²H/log H` ("as ε is small and H is large"), which fails
when ε²H is bounded. The catch genre: ANTI-VACUITY OVERCORRECTION
(the dual trap to the per-H vacuity trap — recorded for the method
paper).

**v2 (house re-freeze): externalize Tao's PNT input as an explicit
hypothesis** — LHS/RHS byte-identical to v1, one hypothesis added,
quantifier discipline unchanged:

```lean
theorem circle_method_estimate :
    ∃ C C₀ : ℝ, 0 < C ∧ 0 < C₀ ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 x2 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) → (∀ i, |x2 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) *
          ∑ j ∈ Finset.range H,
            (windowVal H x1 j : ℝ) * (windowVal H x2 (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ)) *
            ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi eps H, (1 / (H : ℝ)) *
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖) := by
  sorry -- lands in CircleMethod.lean via W3-b-main-v2
```

**VACUITY GUARD (v2 form):** `eps, H, x1, x2` stay INSIDE the ∃;
the new hypothesis is satisfiable non-trivially (PNT: for any fixed
eps, all large H — the WITNESS obligation is node **W3-c-pnt**,
which must also produce the anti-vacuity instance; until it lands,
v2's non-vacuity rests on Tao p. 22, flagged not proven).

**v2 LANDED 2026-07-19 (byte-identical, C = 2, C₀ = 1 pinned).
v3 RE-FREEZE RATIFIED (house, same day): the executor's
consumer-seam flag is accepted — the existential C₀ is opaque, so
W3-c-pnt's specific constant (2·log 4) cannot fire the hypothesis
through the ∃. v3 form: `∀ C₀ > 0, ∃ C > 0, ∀ eps H x1 x2, hyp(C₀)
→ concl(C)` with C = 1 + 2·C₀ (the executor's own proof supports
it mechanically). Strictly stronger; quantifier discipline
preserved (eps/H/x1/x2 inside, C uniform). The consumer then
instantiates C₀ := 2·log 4 directly.**

**The proof device (transcribed at page fidelity by the flag
report):** periodize x_i with period H — the wraparound error is
O(Σ_p (1/p)·p) = O(|𝒫_H|) ≤ C₀ε²H/log H by the NEW HYPOTHESIS
(the truncated-vs-cyclic seam is a non-issue once the hypothesis
exists); Fourier-expand; minor arcs (ξ ∉ Ξ_H): |S_H| < ε²/log H by
the bigXi filter + `dft_l1_bound` (M = 1); major arcs (ξ ∈ Ξ_H):
bound G₂ crudely by O(1) (box: ‖𝓕‖ ≤ H) and |S_H| ≤ Σ_p 1/p ≤
card·2/(ε²H) ≤ 2C₀/log H via `window_lb` (p > ε²H/2) + the
hypothesis.

## Carrier inventory (`Mathlib/Analysis/Fourier/ZMod.lean`)

`ZMod.dft : (ZMod N → E) ≃ₗ[ℂ] (ZMod N → E)` (scoped `𝓕`);
`dft_apply`, `dft_apply_zero`, `dft_dft` (inversion:
`𝓕(𝓕Φ) = fun j => (N:ℂ) • Φ (−j)`), `invDFT_apply`,
`dft_const_smul/-mul`, `dft_comp_neg`, `dft_comp_unitMul`;
`ZMod.stdAddChar` with `stdAddChar_apply` = `exp(2πi·/N)`; character
orthogonality IS exported (the recon's inline-only finding was
wrong): `AddChar.sum_mulShift` + `ZMod.isPrimitive_stdAddChar`
(found by the W3-b-parseval executor). `dft_eq_fourier` bridges to
the continuous FT.

**⚠ CARRIER GAP (CLOSED 2026-07-19):** mathlib has NO
Parseval/Plancherel for `ZMod.dft` — node **W3-b-parseval** LANDED
it in `CircleMethod.lean`: `dft_parseval`
(`∑_ξ ‖𝓕Φ ξ‖² = N · ∑_j ‖Φ j‖²`, factor N on the time side, pinned
by a delta-function smoke test) + `dft_l1_bound`
(`∑_ξ ‖𝓕Φ ξ‖·‖𝓕Ψ (ξ+t)‖ ≤ N²M²`, the CS corollary Lemma 3.4's
proof cites; shift in the SECOND factor). Both upstreamable.

## House rulings (adjudication 2026-07-19)

1. **The `≪_{a,h}` constant**: the existential-`C` freeze is ACCEPTED
   for the sprint (the model `a=h=1` constant is absolute; the
   vacuity guard makes it honest). The explicit-constant doctrine
   option (pin a numeral during proof) is OPPORTUNISTIC for the
   executor — if the proof yields a clean numeral, pin it; do not
   spend attempts hunting one.
2. **W3-a-3 (the outer (3.15)→(3.16) combine): DEFERRED to a house
   design block.** New doors identified by the recon: (i) the
   Chowla-failure hypothesis (2.11) as an explicit input; (ii) the
   good-`x` selector (union bound: decrement (3.13) +
   `weakUniform_spine` + `fBridge_concentration_decoupled` over the
   outer `logMeasure`); (iii) outer-expectation Fubini plumbing that
   does not exist in the landed API. NOT executor-safe as
   "elementary"; do not dispatch without a frozen design.
3. **Node cuts**: W3-a-1/2 + W3-b-defs landed at adjudication (house);
   W3-b-parseval (C, ~15–25k) dispatches next; W3-b-main (C, ~25–40k,
   may sub-split reduce-to-Fourier / Ξ_H-split) queues behind it.

## Kill-check record

Elaboration: all frozen statements elaborate against the landed API
(`ProbeW3.lean`, sorry-skeletons, zero errors). Validity: W3-a-1/2
PROVEN (`ProbeW3_validate.lean`). Falsity/degeneracy: zero-window
instance collapses both sides to 0; W3-b small-`H` consistent
(`H=1`: Lean's `log 1 = 0` zeroes both sides); the per-`H` vacuity
trap identified and dodged (see the guard above). Deprecation note:
use `integral_finsetSum` (not `integral_finset_sum`).

## W3-a-3 — the outer combine (HOUSE DESIGN BLOCK, 2026-07-19)

Page-fidelity source: p. 22 (read in-house). The chain from (2.11)
to (3.15):

1. Lemma 3.3 concentration (PRODUCT world, uniform y) — landed as
   `fBridge_concentration_decoupled`.
2. Lemma 3.2 transport: the deviation event E_bad ⊂ ZMod P_H has
   exp-small UNIFORM measure ⟹ log|E_bad| ≤ log P_H − g′ + log 2;
   `weakUniform_spine` then bounds its CONDITIONAL measure (given
   liouvilleWindow = x₀) by (t + corr + log 2)/g′ where t = the
   per-x₀ entropy deficiency. "Good x" = x₀ with small t.
3. Markov selection of good x₀ — landed as `decrement_markov` (t ≤
   (κ + defect)/θ for logMeasure-most x₀; κ from the decrement at
   the tower-selected H, defect funded by (3.9) =
   `entropy_residueWindow_ge`).
4. Deterministic box |F| ≪ H/log H on the bad set — needs
   `fBridgeG_abs_le` (H/p + 1) summed via **W3-c-pnt** (the SECOND
   consumer of that node: Σ_p (H/p+1) ≤ H·Σ1/p + |𝒫_H| ≪ H/log H).
5. Fubini + take E over logMeasure; (2.11-model) as the DOOR input:
   `|∫ fBridgeF eps H (liouvilleWindow H n) ((n : ZMod (PH eps H)))
   ∂(logMeasure x ω)| ≥ c·ε·H/log H` ⟹ (3.15-model), then
   `fBridgeF_mean` rewrites the y-mean as the two-point correlation.

**⚠ THE MARGIN CHECK (house, confirmed at design level): the
honest-exponent pinch is REAL.** The transport (step 2) needs the
deficiency budget t ≪ g′. Our landed exponent is g′ ≈ ε⁶H/(8·log²H)
(the PNT-free prime count in W2-b), one log below Tao's ε⁷H/log H.
The tower telescope selects H against budgets whose tower-sum
diverges: Σ 1/(n log n) diverges (landed,
`not_summable_one_div_nat_log`) but **Σ 1/(n log² n) CONVERGES** —
a two-log budget is NOT fundable by widening the tower. Tao's
one-log grade sits exactly on the divergence boundary; ours is
across it. REMEDY (mandatory prerequisite): **node W2-b′ — the
single-spot Chebyshev swap** in FBridge.lean's prime-count step,
pre-identified by the W2-b executor as a local upgrade, restoring
g′ to the ε⁷H/log H grade. Without W2-b′, W3-a-3c is UNPROVABLE as
designed — do not dispatch 3c before b′ lands.

**Node cuts:**
| node | content | class | prereq |
|---|---|---|---|
| W2-b′ | the Chebyshev swap: fBridge_concentration at Tao-grade exponent ε⁷H/log H | B | none (local to FBridge) |
| W3-a-3a | bad-set transport: Hoeffding card bound + weakUniform_spine compose, per-x₀ | B | W2-b′ |
| W3-a-3b | good-x₀ selection | A (≈ decrement_markov applied) | none |
| W3-a-3c | the outer Fubini assembly → (3.15/3.16-model), (2.11) as hypothesis | C | ALL of: W2-b′, 3a, 3b, W3-c-pnt, the v2 circle method |

**Doors (explicit hypotheses, believed-true, no new axioms):**
(2.11-model) — discharged later by W3-e from the log-Chowla-failure
assumption (the contradiction hypothesis; it is SUPPOSED to be
false); the MR Prop 2.4 door is downstream of this block (feeds
W3-e, not W3-a-3).

## The MRT door — FROZEN (MRT-DOOR-R0, adjudicated 2026-07-19)

**THE HEADLINE: this is a THEOREM-door.** Tao Prop 2.4 (p. 12) is
PROVEN from [17] = Matomäki–Radziwiłł–Tao, arXiv:1503.05121 ("An
averaged form of Chowla's conjecture") — the strongest honesty
class. The OPEN object is (4.1) (§4, p. 26): the sup-INSIDE-the-
integral variant, "not currently covered by the existing
literature" (Tao), the sole k=3 obstacle.

**Frozen door** (elaboration-checked; lands in MRTDoor.lean):
`windowExpSum H n α := ∑ i : Fin H, (liouvilleWindow H n i : ℂ) ·
exp(2πiα(i+1))` and
`MRTUniformity (R : ChowlaRegime) (δ : ℝ) : Prop := ∀ H, R.Hlo ≤ H
→ H ≤ R.Hhi → ∀ α : ℝ, ∫ n, ‖windowExpSum H n α‖ ∂(logMeasure R.x
R.ω) ≤ δ · H`.

**⚠ NON-NEGOTIABLE INVARIANT (kernel cannot police it):** the
`∀ α` stays OUTSIDE the integral. Moving it inside (`∫ ⨆ α ...`)
elaborates identically but silently swaps the proven Prop 2.4 for
the OPEN (4.1). Any future edit to this def must preserve the
quantifier position; the docstring carries this warning verbatim.

**Anti-vacuity:** trivially true iff δ ≥ 1 (unit-modulus box);
teeth live in the consumer smallness `K·δ < c₀·ε` (a regime-style
inequality at W3-e-glue). δ is DATA (∃-inside is vacuous,
∀-inside is false — both probed).

**Seam (probe-PROVEN sorry-free):** hdoor + hXi (|Ξ_H| ≤ K, Lemma
3.5 = W3-c/d) + hsmall (K·δ < c₀·ε) + hlower (the (3.16)∘circle-
method mass ≥ c₀·ε) ⟹ False. The door fires once, at α = −ξ/H.

**Node cuts:** W3-e-door (A, the defs) + W3-e-seam (B,
contradiction_of_mrtDoor — probe-proven) — both landing now via
the resumed recon agent; W3-e-glue (C) waits on W3-c/d constants
(c₀, K) + the (2.11) reduction.

## The additive-energy escape — FROZEN (W3-cd-R0, adjudicated 2026-07-19)

**RENAME RULING (house): the escape nodes are W3-AE-c / W3-AE-d**
(the recon flagged the collision with W3-c-pnt; renamed throughout).

**Transcriptions at page fidelity:** Lemma 3.5 (`|Ξ_H| ≪_{a,h,ε} 1`,
p. 24) + footnote 4 verbatim (the Ben Green quadruple-sum escape) +
the consuming passage. **🚩 PAPER TYPO CAUGHT:** p. 25's Markov line
reads `ε²/H`; the Ξ_H definition and the L⁴ bound require
`ε²/log H`. Our landed `bigXi` already carries the correct
threshold — recorded so no executor "fixes" the carrier to match
the paper. (Catch-against-the-paper #3 this sprint.)

**The chain (S1–S7, provenance per step in the recon report):**
L⁴ = additive energy (Parseval) → triangle → window lower bound
(2/N)⁴ → **the sieve count E[𝒫_H] ≪ N³/log⁴N** (binary-Goldbach
upper sieve, r(n) ≪ (N/log²N)·𝔖(n), Σ𝔖² ≪ N; order TIGHT) →
1/(ε²log⁴H) → Markov at 4th power → |Ξ_H| ≤ ~16·C_d·ε⁻¹⁶,
H-independent. Green–Tao restriction [11] fully bypassed.

**Frozen statements (elaboration-checked; probe at
scratchpad/W3cd_freeze_probe.lean):** W3-AE-d =
`Finset.addEnergy (primeWindow eps H) (primeWindow eps H) ≤
C·H³/log⁴H` (∃C ∃H₀ ∀H ≥ H₀ — the regime is MANDATORY: the crude
E ≤ |𝒫|⁴ ~ ε⁸H⁴ fails against H³/log⁴H; single-prime falsity probe
run); W3-AE-c = the unconditional L⁴/Markov inequality
`|Ξ_H|·(ε²/logH)⁴ ≤ H·(2/ε²H)⁴·E[𝒫_H]`; Lemma_3_5 assembly =
`|Ξ_H| ≤ C(ε)` (B-grade compose). Helpers: W3-AE-bridge (expSum =
dft of the 1/p-weighted window; needs p < H), W3-AE-l4 (the L⁴
Parseval extension of the landed L² dft_sum_mul_conj), W3-AE-markov.

**Carriers:** mathlib `Finset.addEnergy` + `card_sq_le_card_mul_
addEnergy` (ℕ-safe); ⚠ `addEnergy_eq_sum_sq` needs [Fintype] — sum
over a finite carrier instead. Brun track: `congCount_bound`
(generic), `Salt.SelbergPort.selberg_bound_simple`,
`Salt.BrunLower.brun_upper`, `sum_inv_prime_window_le`; the twin-
hard-wired lemmas need re-instantiation for the additive constraint.

**Node cuts:** W3-AE-d (C, 60–90k, the Brun re-instantiation —
generous STOP-AND-FLAG), W3-AE-c cluster (l4 + bridge + markov +
the C-grade combine, one executor), Lemma_3_5 assembly (B, after
both). MRT door lands separately (W3-e-door/seam, from the
MRT-DOOR-R0 freeze above).

## W3-AE-d — SIEVE-PARAMETRIC LANDING + the flagged design block
(adjudicated 2026-07-19)

The executor's STEP-0 verdict: Route A (the full binary-Goldbach
sieve) is a REBUILD, not an instantiation — correctly flagged, not
ground. LANDED (QuadrupleCount.lean, 9108 green): repCount +
addEnergy_eq_sum_repCount_sq (ℕ-safe Σr(n)² identity) +
addEnergy_le_of_r_bound (the isolation) + **W3_AE_d_of_sieve** —
the frozen conclusion from exactly TWO named sieve hypotheses:
`hpt` (r(n) ≤ rbound H n — the Goldbach upper sieve) and `hsq`
(Σ (rbound)² ≤ C·H³/log⁴H — the squared main term × Σ𝔖² ≪ N).

**THE FLAGGED DESIGN BLOCK (deferred; research-grade):** a new
BoundingSieve instance with n-DEPENDENT nu (the twin rho's +2 is
hard-wired; no parameter substitution possible), its three field
proofs (new degenerate case at p ∣ n), the m(n−m) support
injectivity, the main-term extraction (a MertensWindow analogue
for the n-dependent density), and — with NO analogue anywhere in
the track — the singular-series second moment Σ_{n~2N} 𝔖(n)² ≪ N.
Estimated: a twin-sieve-build-sized multi-node block PLUS the
second-moment sub-block. Route B is provably one log short (max-r
crude bound reaches only log³; log⁴ REQUIRED for |Ξ_H| = O(1)).

**WAVE-3 ZENO HALT (house ruling, III.3‴):** wave 3 closes
HYPOTHESIS-PARAMETRICALLY with exactly TWO residuals: (1) the
sieve pair (hpt, hsq) above; (2) the (2.11) reduction (W3-e-glue's
door input). Both named, both scoped, both believed-true (Tao
p. 25 / MRT). The remaining wave nodes (the Lemma-3.5 assembly,
the Theorem-2.3 shell) compose everything landed against these
two residuals.

## GB-SIEVE-R0 — the rebuild PRICED (adjudicated 2026-07-20)

**Verdict: in-window feasible, ~16 nodes, raw ~1.0M / expected
2.0–2.5M loaded (range 1.6–3.2M).** Cheaper than the W3-AE-d
scoping because: (1) MertensWindow + CongruenceCounting + the
Selberg/brun_upper engines reuse VERBATIM (the priciest assets,
cost zero); (2) upper-bound-only DELETES the twin build's whole
endgame/discharge half; (3) **hsq is class-B, not C**: we need a
MAJORANT, not the true Σ𝔖² ≪ N — euler_tail_L + prod_one_add_le +
Σ1/p² < ∞ carry it, both former class-C gaps (sharp 𝒫+𝒫 count,
exact constant) are OFF the critical path; (4) the twin Brun sieve
is ALREADY dimension-2 (ρ(p) = 2), so M2/M3 param-substitute — the
only genuinely new structure is ρₙ(p) = 1 at p ∣ n, which IS the
singular series. The two former HIGH blockers evaporate
(identity-map sifting kills non-injectivity; no infinitude
needed). goldA1Sieve's shifted-support plumbing is a live template
(wrong dimension, right scaffolding).

**Node DAG** (see the recon report in the session tasks for the
full table): hpt track GB-1..10 (poles: GB-5 the n-even dim-2
instance ~110k, GB-6 the 𝔖(n) split ~110k, GB-7 main term ~100k);
hsq track GB-11..15 fully parallel (pole: GB-14 the Euler-product
majorant ~100k); GB-0 = the Fable design/freeze node (~60k).
Critical path ≈ 420k. Stop-and-flag risks: GB-5, GB-14.

**DECISION: with JYH** (in-window go vs deferral).

## GB-0 — THE REBUILD DESIGN FREEZE (house, 2026-07-20, JYH GO)

**The parity split (resolves n-even).** Window primes are odd
(> ε²H/2 ≥ 3 in-regime), so odd n has repCount = 0 (odd+odd=even):
hpt is TRIVIAL for odd n. FREEZE:
`rbound H n := if Even n then C₁·((eps:ℝ)²·H/(Real.log H)²)·sTrunc n else 0`
— hpt splits into the parity-triviality branch + the sieve branch
(even n only, where ν_n(2) = 1/2 < 1 is safe).

**The majorant series (resolves h at p = 2).** ODD squarefree
divisors only:
`h (d) := ∏_{p ∈ d.primeFactors} (1/((p:ℝ) − 2))` (odd d ⟹ p ≥ 3
⟹ p − 2 ≥ 1 > 0);
`sTrunc n := ∑_{d ∈ n.divisors, Squarefree d ∧ Odd d} h d`
— UNTRUNCATED (divisors of n are finite; the hsq Fubini converges
because h(p) ~ 1/p gives Σ_{d₁,d₂} h·h/[d₁,d₂] < ∞ per
euler_tail_L, and the +1 error carries (Σ_{d ≤ 2N} h)² ~ log² —
negligible). No D-level needed in hsq; the sieve's own `level`
handles hpt's truncation.

**The local density (GB-1/2).** ρₙ(d) = #roots of m(n−m) ≡ 0 mod d
(d squarefree): ρₙ(p) = 1 if p ∣ n (m ≡ 0 ≡ n coincide), else 2;
at p = 2, n even: ρ = 1. ν_n = ρₙ/d; all ν_n(p) < 1 given n even.

**The instance (GB-5).** mathlib BoundingSieve/SelbergSieve:
support = Finset.Icc 1 n with the IDENTITY map (sift m by
d ∣ m(n−m) — no injectivity issue), weights ≡ 1, totalMass = n,
nu = ν_n, level = the twin template's choice (mirror M3's z; the
log² emerges from G(z) ≥ c₀·log²z exactly as in the twin dim-2
main term). goldA1Sieve (Goldbach/A1.lean) is the plumbing
template; the twin Sieve.lean/M2/M3 are the mathematical template.

**Interfaces (frozen).** GB tracks must produce EXACTLY
QuadrupleCount.lean's `hpt`/`hsq` shapes at the rbound above; the
composition target is `bigXi_bounded_of_sieve` (L35-ASM, in
flight) → `contradiction_of_mrtDoor`. Constants stay symbolic
(C₁, c₀, K) — pin opportunistically, never hunt.

**Wave 1 (dispatched):** GB-M2 executor = GB-1..4 chained
(GoldbachEnergyM2.lean); GB-HSQ executor = GB-11+14 (the defs +
the Euler majorant, GoldbachEnergyHsq.lean). Wave 2 on their
landing: GB-5/6 (Sieve), then GB-7..10 (Hpt assembly), GB-12/13/15.
