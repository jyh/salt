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

**The instance (GB-5). [AMENDED at landing — the executor caught a
design-mechanics error in the original freeze: mathlib's multSum
tests d ∣ (support element) with NO sift-function hook, and
m ↦ m(n−m) is symmetric, so identity-map + weights ≡ 1 would
UNDER-count. Faithful realization:]** support = (Icc 1 n).image
(m ↦ m(n−m)), weights v = the fibre multiplicity
#{m ∈ [1,n] : m(n−m) = v}, totalMass = n — multSum d then counts
#{m : d ∣ m(n−m)} EXACTLY and siftedSum over-counts ordered reps
(what repCount ≤ siftedSum needs).
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

## W3-F — the (2.4)→(2.11) producer chain FROZEN (W3-F-R0,
adjudicated 2026-07-20)

**h211 IS Tao (2.11) verbatim** at the model + normalized measure;
the producer is §2's (2.4)→(2.6)→(2.11), pp. 12–16 (NOT pp. 19–21
— the recon corrected the house's page pointer). **The §2 collapse
is PARTIAL:** the g_{ε²} truncation dies (λ's alphabet is {±1};
entropy_liouvilleWindow_le already bounds H ≤ H·log2 — we also
dodge Tao's O(ε²H/logH) truncation error) and the pretentious
dichotomy is NOT on this path (it feeds Prop 2.4 = the MRT door,
downstream); but **Prop 2.6 (the multiplicativity p-average:
1_{...}g₁g₂(n) = c_p·(...)(pn), then affine pn ↦ n+j at cost 1/p,
sum over j ≤ H and p ∈ 𝒫_H) survives as THE class-C node.**

**Frozen statements** (probe ProbeW3F.lean, elaborates; seam
byte-verified through outer_combine): `logChowla2Fails eps x ω`
(anti-vacuity probed both directions); Stmt 1
`singleCorr_of_fails` (A: ÷Z via harmonic_window_bounds, ε/2
margin); Stmt 2 `fBridge_of_singleCorr` (C: Prop 2.6; sub-split 2a
per-(p,j) reduction via the LANDED dilation_error_div — explicit
error 2Mr/q²/Z, better than Tao's o(1) — + D2, and 2b sum + D3 +
error control; needs hωbig regime hypothesis, weaker than hhead);
Stmt 3 `h211_of_logChowla2Fails` (A glue; its (c₁, h211) pair IS
outer_combine's parameter pair).

**New nodes cut:** **D2** (A): port liouville_apply_mul/
liouville_int_prime from Salt/TwinBar into the spine. **🚩 D3
(B/C, NEW LOAD-BEARING GAP): primeWindow_sum_inv_ge — the Mertens
LOWER bound Σ_{p∈𝒫_H} 1/p ≥ c/log H** (needs a dyadic Chebyshev
lower count π(N)−π(N/2) ≫ N/log N; only the UPPER direction exists
anywhere in the tree). Tao's "by the prime number theorem" hides
it; the H/logH grade of h211 is born here. **Offset note:** the
failure Prop uses λ(n)λ(n+1); liouvilleWindow starts at λ(n+1) —
one translation, absorbed in Stmt 2's j-sum.

## Night-shift adjudications (house, 2026-07-20, JYH asleep)

**GB-6 2^ω flag → RESOLUTION (c), the coprime restriction (house
re-freeze).** The landed comparison route costs sCorr n =
2^{ω_odd(n)}·sTrunc n (breaks hsq: Σ4^ω(n) ~ N·log³N). The fix: on
ℓ COPRIME to n, g_n(ℓ) = gTwin(ℓ) EXACTLY (all p ∤ n); the d·m
factorization (d ∣ rad_odd(n), (m,n) = 1) gives
Σ_{ℓ≤z} gTwin ≤ sTrunc2(n)·Σ_{(m,n)=1} gTwin(m) where
**hFac2 d := ∏_{p∣d} 2/((p:ℝ)−2), sTrunc2 n := Σ_{d∣n,sqfree,odd}
hFac2 d = ∏_{p∣n,odd}(1 + 2/(p−2))** — polylog-grade AND
square-sum-fundable (h₂(p) ~ 2/p still gives 1 + O(1/p²) local
factors in the lcm double sum). New nodes: **GB-6c** (the
coprime-restricted denominator bound c₀log²z/sTrunc2 n ≤
selbergBoundingSum — reuses the landed mainTermSum engine +
gTwin multiplicativity; GB-6's Parts 1/2/4 remain valid
infrastructure) + **GB-14b** (hFac2_lcm_sum_le — mechanical re-run
of GB-14's route). rbound RE-FROZEN: sTrunc → sTrunc2.

**THE lcm-SPLIT TRICK (house, kills GB-1213's Mertens flag):** in
the hsq Fubini count, pairs with lcm(d₁,d₂) > 2ε²H contribute ZERO
(no multiples in (0, 2ε²H]); pairs with lcm ≤ 2ε²H have
count ≤ 2ε²H/lcm + 1 ≤ 2·(2ε²H)/lcm. So the +1 term folds into a
factor 2 on the main term — NO Σ1/p Mertens upper needed, no
polylog chase. Sent to the in-flight GB-1213 executor.

**STMT2 Zeno residual:** hreduce (the 2b main-term extraction) is
blocked on a missing carrier — shift invariance for CORRELATION
INTEGRALS against logMeasure (harmonic_shift_l1_le covers window
LAWS only). New node **SHIFT-CORR** (B): |∫ f(n+1) ∂logMeasure −
∫ f(n) ∂logMeasure| ≤ C/Z-form for |f| ≤ 1 (TV/endpoint-mass
argument on the Dirac sum). Then **HREDUCE** (C, all carriers
present): the 2b assembly (fBridgeF_liouville_apply +
perPair_dilation + liouville_mul/prime + SHIFT-CORR + the
error-below-half arithmetic at hωbig : log ω ≥ cM/ε). hmert is
ALREADY discharged by D3's primeWindow_sum_inv_ge.

**GB-7 CATCH + RE-FREEZE #2 (night, 2026-07-20): THE PARITY SPLIT
IS DROPPED.** The ungated hpt at the `if Even n` rbound is FALSE
(eval counterexample: eps = 1, H = 3, 𝒫 = {2,3}, n = 5 odd has
repCount = 2 > 0 = rbound — small-H windows may contain 2; the
GB-0 absorption analysis covered only the even branch). RE-FREEZE:
`rbound H n := C₁·((eps:ℝ)²·H/(log H)²)·sTrunc2 n` for ALL n (no
if). Consequences: (i) hpt becomes true+ungated — odd-large-H is
trivial (all-odd window ⟹ repCount = 0 ≤ rbound ≥ 0), small-H
absorbs into C₁(ε) for BOTH parities (rbound never 0), even-large-H
is the landed sieve core; (ii) hsq re-runs FREE — sum_sTruncW_sq_le
already bounds the FULL sumset (the if was discarding odd terms);
the no-if variant is strictly easier. GB-15 = the terminal
assembly: hsq_holds_gen' (no-if, mechanical) + the hpt final
(the z = ⌊H^(1/10)⌋ rpow seam per the M5Assembly templates + the
small-H absorption + the composition) + the |Ξ_H| hookup through
W3_AE_d_of_sieve → bigXi_bounded_of_sieve.

**W3-F-G-R0 ADJUDICATED (night, 2026-07-20): G1 DISSOLVES, G2 IS
ELEMENTARY, hωbig STRENGTHENED.** (1) G1 is a NON-GAP: reorder
collapse-BEFORE-dilate — on the residue class p ∣ n+j+1 the
identity λ(pN)λ(pN+p) = λ(N)λ(N+1) applies exactly (needs only
λ(p)² = 1, NO primality; core proven in the recon probe, ~8
lines); dilation_error_div then receives the pre-collapsed f. No
strided-shift carrier needed; corr_shift_le is not on this path.
(2) G2 = ONE new elementary carrier, the two-scale edge lemma
(sibling of edge_sum_le at a scale JUMP): the dilated window
(x/pω, x/p] vs the base (x/ω, x] differ by two strips of harmonic
mass ≈ log p each — per-pair error (2·log p)/(p·Z), summed
2H·log(ε²H)·SP/Z. Tao's Lemma 2.5 (transcribed verbatim in the
recon) bundles the reindex + this swap into one o(1) — elementary,
NO entropy/pretentious input (the flags' contrary note was a
misread). (3) ⚠ REGIME CORRECTION: the hωbig obligation was
UNDER-BUDGETED (Z ≥ 8/ε covered only the dilation defect and
missed the swap error, which is Z-controlled and does NOT vanish
in x). STRENGTHENED FORM (house amendment; the obligation is
design-doc-only, no landed statement touched): **hωbig: log ω ≥
(8/ε)·log(ε²H) + 1** — compatible with Tao's hierarchy (H ≪ ω).
For the morning brief. NODES: W3-F-G1 (B, perPair_collapse),
W3-F-G2 (C, dilated_window_stability), W3-F-A (C, hmain_assembly
→ hreduce_close's hbudget ∧ hmain). G1+G2 dispatch as one
executor; W3-F-A on their landing.

**hωbig STRENGTHENING RATIFIED BY JYH (2026-07-20 ~05:00: "I
ratify the strengthened hωbig").** The form log ω ≥
(8/ε)·log(ε²H) + 1 is now the frozen obligation.

## W3-e-final — THE TERMINAL GLUE (house freeze, 2026-07-20)

The single theorem closing the conditional chain:
`log_chowla_two_conditional (R : ChowlaRegime) {δ c₁ ...}
(hdoor : MRTUniformity R δ) (htower : the budget block)
(hfail : logChowla2Fails R.eps R.x R.ω) : False`.

**The composition order (all landed unless marked):**
1. hfail → singleCorr_of_fails → hseed (needs hlog2 : 2 ≤ log R.ω
   ← regime).
2. hseed + hmert (← primeWindow_sum_inv_ge, D3) + hreduce (←
   hreduce_close ∘ W3-F-A's hmain+hbudget — **W3-F-A pending**) →
   fBridge_of_singleCorr → hprop26 → h211_of_logChowla2Fails →
   (c₁, h211).
3. hcirc ← circle_method_estimate (2·log4) + the hcard chain
   (sqrt_le_window_at + primeWindow_card_le_of_regime).
4. hXi ← bigXi_bounded (destructure; H ≥ H₀ ← the tower's
   H-selection).
5. hdoor + hbudget1/2 + steps 2–4 → log_chowla_two_shell → False.

**The H-threshold fold:** the tower-selected H must satisfy ALL
floors simultaneously: bigXi_bounded's H₀, hpt's H₁(ε) (internal,
already absorbed), 3 ≤ H, log H ≥ 1, 4 ≤ ε²H, the hωbig-linked
forms. Strategy: ONE combined floor H* := max of the finitely many
∃-extracted thresholds; the ChowlaRegime's Hlo must be enlargeable
to H* — RegimeInst PATCH-4 if the current witness's Hlo = 4·10⁶
falls below any extracted threshold (they are ∃-opaque: the patch
takes H* as data and re-witnesses with Hlo := max(4·10⁶, H*) —
the tower construction is Hlo-parametric, verify in
Tower.lean/RegimeInst.lean).

**The budget block (htower):** hbudget1/2 (the shell's numeric
closures — the tower drives ERROR + Kδ below the c₁ε margins),
ht/hg/hgle/hI (decrement budgets ← entropy_decrement at the
selected H), hωbig (RATIFIED strengthened form ← the regime's
ω-vs-H hierarchy — CHECK RegimeInst's ω = 2 witness: the
strengthened hωbig needs log ω LARGE — ⚠ ω = 2 gives log ω ≈ 0.69
— THE WITNESS MUST BE RE-BUILT with ω ≫ exp((8/ε)·log(ε²Hhi))-
grade... the regime's hcoprime/hheadroom couple ω to x; verify
the tower still witnesses — this is PATCH-4's real content and
MAY be the last hard node; if the tower cannot fund the
strengthened hωbig at the needed H the Zeno halt lands the
conditional shell with htower explicit).

**Nodes:** W3-F-A (C, on G12) → W3E-PATCH4 (B/C, the regime
re-witness incl. the ω-hierarchy check) → W3E-FINAL (B/C, the
composition above). Then log-Chowla-2 rests on: MRTUniformity
(theorem-door) + htower-if-Zeno.

**W3-F-A + THE GATE CATCH (night, 2026-07-20): the fBridgeF gate
is OFF BY ONE — a W2-b transcription slip, load-bearing only now.**
The landed gate `(j : ZMod p) = −r` (0-indexed j) pairs with the
1-indexed window values λ(n+j+1); Tao (3.14) has gate index =
product index (house-verified against FBridge.lean:89 + pg-22).
Every count-based consumer (boxes, means, Hoeffding, the decoupled
chain) is residue-independent — hence ten nodes of silence; the
multiplicativity collapse is the FIRST alignment-sensitive
consumer, and W3-F-A proved no r-choice can reconcile (the
executor's p=2 witness). The G-R0 "G1 dissolves" adjudication
implicitly assumed the aligned gate. **HOUSE RULING (Fable-tier
statement correction, ground truth = the page image): fix the
gate to `((j+1 : ℕ) : ZMod p) = −r` in fBridgeG; repair the
unfolding consumers (fBridgeG_mean's fiber count — residue-
independent, mechanical; fBridgeF_liouville_apply → gate
p ∣ n+j+1, EXACTLY perPair_collapse's class — the blocker
dissolves at the root); full-build re-verification of the entire
Chowla cone; all downstream STATEMENTS unchanged in shape
(fBridgeF_mean's RHS, the concentration forms, the shell).**
Node GATE-FIX (B/C). W3-F-A itself LANDED sound: hreduce_holds
(hseed + hbudget ⟹ the frozen hreduce — hmain proven FREE via
reverse-triangle; the node's whole content collapsed onto ONE
residual hbudget, dischargeable post-GATE-FIX via the G12 chain).

**HBUDGET STEP-0: THE RATIFIED hωbig IS INSUFFICIENT — CORRECTED
FORM PROVISIONALLY ADOPTED (night, 2026-07-20; ⚠ MORNING
RE-RATIFICATION ITEM FOR JYH).** The 8/ε calibration allocated the
ENTIRE (1/4)·SP·H·ε budget to the swap term's 2L coefficient
alone — zero room for the collapse total, the landed +6, the
shift, or the boundary (verified two ways against
DilationStability's landed constants). CORRECTED (tight, adopted):
**hωbig: log ω ≥ (16/ε)·log(ε²H) + 64/ε + 1** (clean alternative:
(64/ε)·log(ε²H) + 1). Slice allocation: Z-controlled ≤ 1/8,
shift ≤ 1/16 (hxbig, x-only), boundary ≤ 1/16 (heps tied to D3's
c: eps ≤ c/(32·log 4)). The full regime block + budget table are
in the HBUDGET STEP-0 report (session tasks) and become
W3E-FINAL/PATCH-4 obligations: **PATCH-4's ω-floor is now
ω ≥ (ε²H)^(16/ε)·e^(64/ε)** (maintaining ω ≤ x — the tower's
hierarchy check sharpens accordingly). HBUDGET-2 (the turnkey
proof per the closed table) dispatched.

**hωbig CORRECTED FORM RE-RATIFIED BY JYH (2026-07-20 morning:
"Yes, I reratify hwbig").** log ω ≥ (16/ε)·log(ε²H) + 64/ε + 1 is
now the frozen obligation; the provisional adoption is confirmed.

## W4-MAJOR-R0 — VERDICT RED: the door deletion is OFF
(adjudicated 2026-07-20 morning; the HOUSE'S OWN hypothesis killed)

**The house's category error, named:** "major-arc" constrains the
FREQUENCY α; it does nothing to the SHORT-WINDOW structure of the
λ-sum. The fatal facts: (1) **ξ = 0 ∈ Ξ_H always** (S_H(0) ≈
log 2 ≫ ε²/logH), and its door instance is the bare
E|Σ_{j≤H} λ(n+j)| = o(H) over windows H ≪ log x — the
Matomäki–Radziwiłł SHORT-INTERVAL theorem itself; (2) Tao's
"simpler [17, Thm A.1]" is STILL an MR theorem — the remark
simplifies the citation, not the strength; (3) SW/zero-density
have zero content below x^{7/12}; (4) the corpus has NO Weyl/
Vinogradov machinery (and the spine doesn't use any — Lemma 3.5's
L⁴ route bounds |Ξ_H| without locating frequencies); (5) the L²
escape is circular (its off-diagonal IS the Chowla correlation).
**Door-deletion ≡ formalizing MR (arXiv:1503.05121) — a D-grade
multi-month program, the natural flagship of a FUTURE campaign,
not this window.** Cost of the wrong hypothesis: 119k (the recon).
Cost it prevented: the 1.5–3M wrong-GREEN campaign.

**SALVAGE (ruled, queued as node DOOR-MIN, AFTER W3E-FINAL lands
— no race with the in-flight composition):** the Tao-faithful
WEAKENED door `MRTUniformityXi` (the finitely many Ξ_H
frequencies instead of ∀α — Tao's own proof fires it exactly
there; +0 ≤ δ side hypothesis). Landed ADDITIVELY (new def + the
trivial implication MRTUniformity → Xi + the Xi-form final
surface); no landed statement edited. It shrinks the door's
formal surface honestly and future-proofs the MR campaign.

## M-BOUNDARY — THE DEEP PLAY (house design block, 2026-07-20,
JYH: "I love it, let's go for it, together")

The question: what, precisely, separates the proven crack
(log-Chowla-2) from the twin conjecture? Two probes, each with
kernel-checked deliverables.

**PROBE 1 — THE LOG-LOCALIZATION MAP.** Audit the landed spine
for every logMeasure-SPECIFIC property consumed. The house's
candidate inventory: (a) the dilation covariance (Lemma 2.5's
1/q change of variables, carried by dilation_error_div) — the
load-bearing log-specific step: the density 1/n is scaling-
covariant (1/(qm) = (1/q)·(1/m)); the UNIFORM measure fails this
constitutively; (b) harmonic_window_bounds (Z ≈ log ω — the
normalization that turns ε·log ω into ε); (c) everything else
(integral_logMeasure_eq etc.) is weight-GENERIC — verify.
**Crown deliverable (MB-2): the dilation-covariance UNIQUENESS
lemma** — a weight w : ℕ → ℝ≥0 satisfying the q-dilation
covariance for all q is proportional to 1/n (the multiplicative
functional equation) — i.e. a kernel-checked theorem that
**logarithmic averaging is FORCED by dilation covariance**: the
first formal explanation of WHY the log is there. Nobody has
this.

**PROBE 2 — THE Λ-TRANSPORT BREAK-POINT AUDIT.** Attempt-map the
spine with Λ-grade weights in place of λ; formalize each break as
a precise statement. The house's candidate break-points: (a) THE
COLLAPSE ENGINE — λ(pN)λ(pN+p) = λ(N)λ(N+1) needs complete
multiplicativity + unit modulus; Λ is supported on prime powers —
the identity fails constitutively. Deliverable (MB-3): the
CHARACTERIZATION lemma — the class of f admitting a p-collapse
identity IS the completely multiplicative unit-modulus class — a
wall-statement connecting to the landed parity-wall family;
(b) the entropy alphabet ({±1}^H → H·log2 ceiling — the
decrement's fuel; Λ unbounded breaks the Fannes/box machinery);
(c) the F-bridge box (|λ| ≤ 1 load-bearing). **Best-case output:
a NEW DOOR — the minimal hypothesis on a weight system making the
entropy argument run (the "transport door") — possibly weaker or
incomparable to TwinB_min. Honest-case output: new named
obstruction theorems (publishable walls).**

**Nodes:** MB-1 (recon: the spine-wide logMeasure/|λ|≤1/
multiplicativity dependency sweep — the certificate data; B/C) →
MB-2 (the uniqueness lemma; B) ∥ MB-3 (the characterization; B) →
MB-4 (house synthesis: the boundary map document + any door
freeze; Fable). MB-1 dispatches now.

## GEH-REV-R0 — ADJUDICATED (2026-07-20): re-price FLAT at
0.75–1.2M; all four obligations remain DEBT; the WindowPNT lead

**The honest headline: the window's marquee landings are
ORTHOGONAL to this door** — Weil/Kloosterman/Chowla feed additive
correlations, not multiplicative AP-discrepancies; only the SW arc
helps (SmallQTypeII's small-q half now discharges from the PROVEN
siegelWalfisz_holds). Composition shift: SmallQ −150k, PpLevel
+150k (the floors made the mathlib gap precise: the composite
k-th-power root count incl. the (ZMod 2^e)ˣ 2-torsion corner
mathlib entirely lacks). No obligation is research-open; the door
does NOT reclassify.

**The DAG (3 parallel tracks + glue):** A: N-REPLUMB (FABLE-TIER
— the pieceObligationU_of_multiblock combinator demands global
balance x ≤ 4NᵢMᵢ that vP3's low dyadic blocks provably violate;
the re-cut to a local-scale variant is an interface change,
reserved; the house designs it next) → N-HDOM + N-TYPEI-MID.
B: N-SMALLQ (C, 150–250k — the CRT/Möbius reduction onto
siegelWalfisz_holds; reindex landed). C: N-PP-ROOT (C→Fable,
250–400k, THE critical path) → N-PP-ASSEMBLY. D: N-WIN glue.

**🚩 THE LEAD (dispatched as WINPNT): WindowPNT may be
DISCHARGEABLE** — it was stated as an interface "because mathlib
has no PNT"; that premise is STALE (the corpus has PNT-with-rate
through the SW gate: Salt.Chen.lambda_mass_lower etc.). If the
rate covers the 64N window, ONE OF THE DOOR'S TWO GENUINE ANALYTIC
INPUTS IS DELETED — the door becomes GEH_min + obligations, full
stop. Verify-then-discharge, ~50–150k.

## MB-1 — ADJUDICATED (2026-07-20): THE BOUNDARY MAP

**The headline: the crack runs on DILATION INVARIANCE, twice.**
The sweep (37 keystone files, classified by actual consumption not
mention): **the log enters at exactly TWO load-bearing places** —
(a) the dilation covariance 1/(qm) = (1/q)(1/m) (Dilation →
DilationStability/Prop26) and (b) the harmonic normalizer value
Z ≈ log ω (LogMeasure → ChowlaFailure/HBudget); a third
normalizer-floor use is weight-generic. **Complete multiplicativity
enters at ONE mechanism** — the collapse identity — and the
SURPRISE: it consumes λ(p)² = 1, NEVER the sign λ(p) = −1
(liouville_prime has zero proof-term uses!) — the collapse works
for ANY real completely-multiplicative ±1 function (real Dirichlet
characters, λ·χ, ...). And the recon's reframing: **the collapse
IS pair-correlation dilation-invariance** — the ±1-sign analogue
of (a). So the two "different" mechanisms are ONE principle in two
guises. **The unit-box**: the {±1}^H → H·log2 ceiling is the
decrement's fuel (the load-bearing log 2 threshold in Diverge/
SpineClose); the |λ| ≤ 1 boxing elsewhere is hypothesis-generic.
**The sieve side (~21 files incl. all GoldbachEnergy*) is FULLY
weight- and box-generic.**

**What separates log-Chowla from twins, stated by the map:** not
"λ-ness" — the crack needs (i) dilation-covariant weighting (the
log, forced — see MB-2), (ii) a bounded ±1-grade alphabet (entropy
fuel), (iii) pair-correlation dilation-invariance (the CM±1
class). Λ fails (ii) and (iii) constitutively; any twin-transport
door must state what replaces them.

**MB-2/MB-3 adjudication:** mb2_exact (the crown: w(qn) = w(n)/q
⟹ w = w(1)/n — "the log is FORCED"; class A, probe-PROVEN; the
approximate form is an honest NON-uniqueness — bounded
multiplicative oscillation survives, noted as a remark) +
mb3_forward (real-CM±1 ⟹ collapse; A, probe-proven) + the
candidate biconditional FROZEN AS AN OPEN WALL (the converse
likely false/hard — collapse constrains only pair-correlations)
+ THE NUMERIC HUNT (search ±1 sequences with dilation-invariant
pair-correlation, not CM — a counterexample IS the publishable
wall). Node MB-23 dispatches (all four pieces, one executor).
MB-4 (house synthesis: the boundary-map document) after.

## N-SMALLQ STOP-AND-FLAG — SmallQTypeII IS FALSE AS FROZEN
(house ruling, 2026-07-20)

The sprint-2 freeze dropped the polynomial-scale condition every
textbook Type-II estimate carries: with V = M = polylog(x) the
typeIIData block collapses to pure Λ (only divisor > M of
n ∈ (M, 2M] is n itself — numerically verified), and the Λ-in-AP
discrepancy at mod 3 grows like 0.3·√M (prime-race Ω-behavior)
while the budget shrinks — ∃K ∀x refuted. ROOT CAUSE: SW saves
powers of log(SCALE); polylog scale gives log log x. **RULING
(exploration-track def, house tier): amend SmallQTypeII with the
scale guard** — the inner ∀-block gains the hypothesis
`(x:ℝ)^(1/3) ≤ (V x : ℝ)` (the form every real caller satisfies:
V = cbrt x; M = 2^a·x^(1/3)-grade) — making the Prop true and
SW-provable; re-thread swAt_typeIIData + its GehDecomp/GehMulti
call sites. THE GIFT (kills the flagged hard seam): the CRT/
solvability machinery is UNNECESSARY — gcd(a,q) = 1 forces
gcd(m,q) = 1 (else the per-cofactor discrepancy VANISHES), so the
reindex is a clean m⁻¹-bijection at the same modulus. Node
**GEH-FIX** (B/C: the amendment + re-thread + repair) dispatches;
**SMALLQ-2** (the SW proof at the fixed def, using the gift + the
landed spine: typeIIData_residue_reindex, the seqDiscrepancy
calculus, siegelWalfisz_holds, the summation budgets) follows.
Catch genre: LATENT FREEZE FALSITY, surfaced at first proof
contact — two sprints after the freeze.

## THE GOLD WINDOW — christened (JYH, 2026-07-20: "yes I love
'Gold Window'!")

The current campaign's official name: **Sprint 3 / the Gold
Window** — the boundary experiment, played at full throttle
through the 78-hour quota window ("go for the gold"). The ledger's
`play <thread>:` commit prefix denotes this campaign. THE
TAXONOMY (canonical, for all reports and future campaigns):
**node** (one executor dispatch) < **wave** (a batch under one
freeze) < **rung/track** (a ladder toward one theorem) <
**campaign** (a registered phase with its own design docs, arc,
and closing report — e.g. the Chen arc, Sprint 2, the Gold
Window; future: MR, HB-ENGINE, the transport door) < **the siege**
(the project entire).

## N-REPLUMB — THE ANCHORED MULTIBLOCK RE-CUT (Fable design block,
## the Gold Window, 2026-07-20; supersedes halt #2's combinator)

**The defect (halt #2, probe-verified):** `pieceObligationU_of_
multiblock` demands every block balanced at the GLOBAL scale
(`x ≤ 4·Nᵢ·Mᵢ`); `vP3` lives on `n ∈ (x^{2/3}, x]`, so its dyadic
block-pairs have products spanning `[x^{2/3}, x]` — `hwin ∧
hdecomp` jointly unsatisfiable (witness: `vP3(pq) ≠ 0` at
`pq ≤ x/4`). GEH_min itself is faithful to P8b (two-sided CoeffAt
boxes, balance NM ≍ x) and MUST NOT be weakened.

**The re-cut: per-block ANCHORS + two regimes.** New combinator
`pieceObligationU_of_anchored_multiblock` (new file
Salt/Maynard/GehAnchor.lean). Each block carries its own anchor
`s i x := 2 * N i x * M i x`; GEH_min's `∀x` is instantiated AT
THE ANCHOR per block. Consequences:
- **The balance hypothesis DELETES** — `N·M ≤ s = 2NM ≤ 4NM`
  holds definitionally at the anchor. No `hwin`-vs-`hdecomp`
  conflict can recur.
- **hanch** (replaces hwin): scales relative to OWN anchor —
  `(s i x)^ε ≤ N i x ≤ (s i x)^{1-ε}` (same for M), `s i x ≤ x`.
  Satisfied by cbrt-scale blocks with ε ≈ 1/4 above an x-threshold.
- **The proof splits blocks at the anchor floor** `s ≥ x/(log x)^F`,
  `F := 2A + p + 4` chosen per-A inside the proof (the hypothesis
  stays A-free):
  1. **Deep anchors (s ≥ floor):** GEH at x := s. The modulus-range
     deficit `s^θ < x^θ` is POLYLOG-thin and the outer haircut
     absorbs it — `⌊x^θ/log^{B_out} x⌋ ≤ ⌊s^θ/log^B s⌋` with
     `B_out := B + θF + 1` (THE ABSORPTION LEMMA, self-contained
     real inequality; the same trick the old combinator used for
     block COUNT, now applied to modulus range).
  2. **Shallow anchors (s < floor):** support ⊆ [1, 2s] ⊆
     [1, 2x/log^F]; per-q trivial class-mass bound. Needs the
     per-class estimate `Σ_{n≤y, n≡a(q)} |dconv block| ≤
     (y/q + 1)·Sp(x)·log^{pc} x` — derivable from CoeffAt boxes +
     ONE new analytic input: **N-TAU-SPIKE** (below). Σ over
     q ≤ x^θ: the (y/q)-part gives x·polylog/log^F ✓ (F eats it);
     the +1-part gives x^θ·Sp(x)·polylog ✓ provided
     Sp(x) ≤ x^{(1-θ)/2} eventually — x^{1/4000} beats polylog.

**THE TWO EXECUTOR TRAPS (house-caught, MUST be in every brief):**
- **The anchor-shift re-index k-bump.** GEH at x := s evaluates
  families at index s, but our blocks are pinned at outer x. The
  combinator passes CONSTANT families `α' _ := α i x`. CoeffAt
  then demands `|α i x n| ≤ τ^k·log^k s` with s ≤ x — the WRONG
  direction for the log factor. Fix: invoke GEH at exponent k+1;
  above the floor `log x ≤ 2·log s`, so `log^k x ≤ log^{k+1} s`
  once `log s ≥ 2^k` (x-threshold, folded into the corner
  constant). SWAtData shifts in the RIGHT direction (1/log^A x ≤
  1/log^A s) — no bump needed there.
- **The corner regime.** x below the k-dependent threshold: crude
  universal bound, same pattern as the landed x=2 corner.

**N-TAU-SPIKE (new node, class B/C, ~150k, NO dependencies):**
`∀ ε > 0, ∃ C, ∀ n ≥ 1, (n.divisors.card : ℝ) ≤ C * n^ε` — the
elementary divisor bound via the prime-split `τ(n)/n^ε =
∏(e_p+1)/p^{εe_p}`: primes ≥ 2^{1/ε} contribute ≤ 1, the finitely
many below contribute a bounded constant. Corpus check done: only
`card_divisors_le_two_sqrt` (√n — too weak) and the squarefree
2^ω form exist. Consumed at ε := (1-θ)/4 = 1/16000.

**Satisfiability for vP3 (the point of it all):** the double-dyadic
family (muBlock a) × (tiiBlock b) — anti-diagonal pairs, count
≤ D·log² x (p = 2); each pair's anchor is its own box product;
hanch holds since both sides live in [cbrt x, x^{2/3}]-scales;
hdecomp is hdecomp_dyadic refined to the double slicing. NO block
is asked to be globally balanced. **Downstream re-freezes:**
N-HDOM := anchored combinator @ the vP3 double-dyadic family
(discharges hdom); N-TYPEI-MID := same for vP1/vP2 mid-halves.
Dispatch order: N-TAU-SPIKE ∥ GehAnchor(combinator) → N-HDOM →
N-TYPEI-MID.

### N-REPLUMB AMENDMENT 1 (house SELF-CATCH, same session, before
### any dispatch)

**The shallow regime as frozen above is WRONG.** Kill-check
re-derivation: the crude class-mass bound `(z/q + 1)·Sp(x)` summed
over a long modulus range gives `Σ_q (z/q)·Sp ≈ z·Sp·log` — and
`Sp = x^{c/loglog x}` (the true τ-spike scale) BEATS every log
power, so shallow blocks with `s ∈ (x^θ, x/log^F)` yield
`x^{1+o(1)}/log^F ≫ x/log^A`. N-TAU-SPIKE is necessary (the
+1/tail parts) but NOT sufficient: the (z/q)-part needs the max
class to track the AVERAGE (polylog) with the spike appearing
only additively — i.e., a **Shiu-shaped class-moment bound**
`Σ_{n≤z, n≡a(q)} |block coeffs| ≤ (z/q)·C·log^{pc} x + Sp x`
(Shiu 1980 / Wolke-type; coprimality + range conditions; C-class,
a real analytic theorem). The registration's 150–250k for the
re-plumb hid this debt.

**The corrected freeze:** `pieceObligationU_of_anchored_multiblock`
takes the Shiu-shaped bound as an explicit per-block HYPOTHESIS
(`hshiu`), discharges the deep regime fully (that half is
verified: GEH-at-anchor + absorption lemma + k-bump), and routes
every shallow block through `hshiu`. New named node **N-SHIU**
(C, ~250–400k, or a restructure making sub-scale coefficients
log-bounded — the Λ-style route — to be decided by its own recon
N-SHIU-R0 BEFORE commitment). N-HDOM's price re-opens
accordingly. Dispatch order revised: N-TAU-SPIKE ∥ GehAnchor
(deep regime + hshiu interface) → N-SHIU-R0 → N-HDOM.

## MR-FORMALIZATION — REGISTERED + GATED (MR-R0 adjudicated,
## 2026-07-20 night)

**The door, grounded:** MRTUniformity (MRTDoor.lean:48) = the
log-averaged, Fourier-uniform (∀α OUTSIDE the L¹ integral) MR-type
bound for λ windows at fixed δ₀ = ε/(2K), in the DEEP H = x^{o(1)}
regime (tower headroom). This is MRT-2015's central estimate
specialized to λ — essentially the full machinery; λ saves little.

**Price: central 12–16M (band 8–25M+) — LARGER than HB-ENGINE;
multi-rung.** Corpus map: landed = large-sieve stack, classical
dVP zero-free region, smoothed Perron/contour, λ long-sum rates,
Mertens. Absent = Halász–Montgomery (POLE 1, 2–5M), vertical-line
L² mean value, Saffari–Vaughan bridge, Turán–Kubilius, and — the
campaign-killer risk — **Vinogradov–Korobov (POLE 2): the standard
MR proof invokes VK; the corpus has ONLY classical dVP; VK has
never been formalized in any proof assistant (+4–8M or
infeasible-as-one-campaign if strictly required).**

**GATE (blocking, Fable-tier): the POLE-2 memo** — at fixed δ₀ +
log-averaging + tower headroom, does classical dVP suffice for
the large-t Dirichlet-polynomial bound (slower rate acceptable),
or is VK strictly required? GO at ~12–16M vs re-scope hangs on
this memo. House writes it before any dispatch.

**Registered structure (post-gate):** the CHEAPER honest target is
**MRTUniformityXi** (MRTDoor.lean:109 — major-arc ξ/H frequencies
only; the Xi seam contradiction_of_mrtDoorXi ALREADY SHIPS) —
drops the minor-arc Kátai/BSZ package (~2M) at the cost of a
Fable spine-rewire (couples naturally with SPINE-BUDGET, same
surface). First milestone: the **ξ=0 untwisted log-averaged
cheap-MR for λ** (Tao Suppl. 6 route: Turán–Kubilius + Plancherel
+ Halász-type + ZFR + Mertens — avoids large-values/duality) — a
historic standalone. Registered openers (post-gate): MR-C
(Turán–Kubilius, B/C, self-contained), MR-A (vertical-line L²
from analytic_LS via gallagher_pointwise, C).

## THE POLE-2 MEMO (house, 2026-07-17 ~3pm; grounded by MR-P2G):
## MR IS VK-GATED — classical dVP does NOT suffice

The grounded chain (Tao Suppl. 6 Thm 7, 6 fetch passes; MRT
1503.05121 cross-check): the zero-free region enters at EXACTLY
ONE step — bounding −ζ′/ζ(1 + 1/log Q + it) = o((log|t|)^{0.98})
— but it is consumed UNIFORMLY AT HEIGHTS |t| UP TO ≍ X
(polynomial in the scale: the door's additive window H ⟹
T ≈ x/H, and H is fixed-large while x is tower-sized). At those
heights classical dVP delivers only O(log|t|) — SHORT BY A FULL
POWER OF LOG. The pretentious form makes it vivid:
D(λ, n^{it}; x)² = loglog x + log|ζ(1+it)| + O(1); under dVP at
|t| ≍ x^A this is ≥ O(1) — no divergence, and NOT even a
guaranteed fixed-fraction cancellation, so the fixed-δ₀ slack
does NOT rescue dVP: the Plancherel step needs |μ̂(ξ)| ≤ 1 − δ₀
uniformly over the polynomial-height support, and dVP leaves
"λ pretends to be n^{it} at some polynomial height" unexcluded.
Both grounded sources spend VK on exactly this object; MRT's
fixed 1/700-power saving is VK-coupled. (Loud residual: the
tail-range dispatch [exp((log X)^{0.99}), X] was not verbatim-
recovered; and any intermediate region σ > 1 − c/(log|t|)^θ,
θ < 0.98, would also suffice — VK's 2/3 is sufficient, not
necessary.)

**VERDICT: the MR campaign stays GATED, now with the gate
resolved AGAINST the cheap branch.** Two registered
continuations, both requiring a dedicated design session:
1. **MR-VK** — build Vinogradov–Korobov (or ANY intermediate
   power-region θ < 0.98; never formalized in any assistant;
   +4–8M ⟹ campaign ~16–24M). Historic, priced, honest.
2. **MR-RESHAPE (D-grade)** — re-design the door/spine
   consumption so the internal frequency support is capped below
   polynomial heights (the Xi seam is the natural candidate home,
   BUT whether the ξ/H major-arc restriction propagates into the
   internal Plancherel range is exactly the open design question
   — unresolved, do not assume).
HB-ENGINE remains the active road. MR-C (Turán–Kubilius) and
MR-A (vertical-line L²) stay registered as unconditionally
useful infrastructure either way.

## VK-R0 ADJUDICATED (2026-07-17 ~5:45pm): RE-SCOPE — THE
## CHUDAKOV MYTH KILLED (catch #52); the exponent is QUANTIZED

**CATCH #52 (recon-kills-house-hypothesis, exactly as tasked):**
"Chudakov θ≈3/4 via van der Corput, no VMVT" is a MYTH. Grounded
(Ford 1910.08205 Table 1 + Yang 2301.03165): Chudakov 1938 used
VINOGRADOV'S METHOD; the van der Corput/Weyl route PROVABLY tops
out at Littlewood (1−σ ≪ loglog t/log t = θ 1−o(1)) — the 2^k
loss per differencing step forces λ=1; only Vinogradov's
polynomial-in-k loss buys λ>1 (θ = 1/λ: VK λ=3/2→2/3, Chudakov
λ=4/3→3/4). **θ is quantized: {1, ≤3/4} — nothing in (3/4, 1);
Littlewood FAILS the θ<0.98 gate** (loglog ≪ (log)^{0.02}).
Every power region requires VMVT — unformalized in ANY assistant
(grounded search). Honest price to clear the gate: **~10–18M**
(4–6× the 2–3.5M prior), pole = the D-tier VMVT slice (6–12M,
widest error bars; needs additive-comb/p-adic infra mathlib
lacks at 0%). Corpus back-half: 3 structural locks (fixed-disk
geometry, the hardcoded dVP balance, poly-only growth) — a
rebuild-on-scaffolding, not a plug-in (the HB-ENGINE
radius-resolved work is the right starter shape). PNT+ has
portable analytic scaffolding, 0% exp-sum core.

**The recon's staged option (registered as the house
recommendation): F1+F2 (~3.5–5.5M) → THE LITTLEWOOD REGION as a
first-in-any-prover CHECKPOINT** (vdC A/B processes + k-th
derivative test + Littlewood balance; pole-free; every lemma
upstreamable exp-sum infrastructure) — banks historic value
regardless, de-risks the pipeline end-to-end, then VMVT gets its
own dedicated recon + GO/NO-GO. Pole-free first nodes frozen by
the recon: VK-N1 (Weyl–vdC A-process inequality), VK-N2 (the
second-derivative test via Poisson), VK-N3 (the parametrized
growth→region back-half, de-locking zero_free_extraction).
**Registered option C (D-grade design question): can the
cheap-MR chain be RE-PARAMETRIZED to consume Littlewood's
loglog saving** (the 0.98 came from Tao's P₋ cutoff choice —
whether a loglog-scaled cutoff closes is unexamined by any
source; the house examines before VMVT is priced as
load-bearing). **PARKED pending JYH: (A) staged Littlewood
(~3.5–5.5M, recommended) / (B) full VMVT commit (~10–18M) /
(C) stand down.**

## PP3-DESIGN — the k ≥ 3 prime-power tail (Fable design block,
## 2026-07-17 evening; discharges N-PP-FOLD's named residual)

**Why it's genuinely hard at θ = 3999/4000:** classical BV
treatments wave the k ≥ 3 tail through because their moduli stop
at x^{1/2} — x^{θ+1/3} ≤ x^{5/6} is harmless there. At GEH-grade
θ ≈ 1, ANY per-q additive x^{1/3} breaks (Σ_q = x^{θ+1/3} ≫ x).
The class/root structure must run deep into k — but the naive
per-factor root bound gcd(k, φ(p^e)) ≤ k gives N_k ≤ 2k·k^{ω(q)},
and Σ_q k^{ω(q)} ≈ Q·(log Q)^{k−1} grows in k. THE RESOLUTION:
the k-regimes cross at **k*(x) := ⌈√(log x / loglog x)⌉** —
below k*, the (log Q)^{k−1} growth loses to x^θ's headroom
(e^{√(log x·loglog x)} = x^{o(1)} ≤ x^{(1−θ)/2} eventually);
above k*, the TOTAL prime-power mass x^{1/k} ≤ x^{1/k*} =
e^{√(log x·loglog x)} is itself x^{o(1)}, so the crude
(no-class-structure) bound closes: Σ_q Q·x^{o(1)} ≤ x^{θ+o(1)}
≤ x/log^A eventually. All x-thresholds fold into the constant
via the corner pattern.

**The three frozen nodes:**
- **PP3-NK** (C, ~150–250k): the general-k root count
  N_k(a,q) ≤ 2k·k^{ω(q)} for unit a — the general-k CRT fold
  (PpRootCrt's named residual: crt_sq_step's structure
  generalizes; per-factor inputs LANDED: card_pow_eq_le_gcd
  gives gcd(k,φ(p^e)) ≤ k odd-side; PpRootTwo's general form
  gives gcd(k,2)·gcd(k,2^{e−2}) ≤ 2k two-side; the parity-aware
  product mirrors sqBound).
- **PP3-SUMS** (C, ~150–250k): the k-uniform divisor-power sums
  Σ_{q≤Q} k^{ω(q)} ≤ Q·(C₀·log(Q+1))^{k−1}·C₁^k and the harmonic
  variant Σ k^{ω(q)}/q ≤ (C₀·log(Q+1))^k·C₁^k — the GehPp2
  pattern (sum_two_pow_omega_le) generalized with EXPLICIT
  k-tracking (the e^{O(k)} must be explicit; induction over
  primes ≤ Q via the Euler-product majorant ∏(1 + k/(p−1))).
- **PP3-ASSEMBLY** (C, ~200–300k): the three-regime split (k=2
  landed sharp; 3 ≤ k ≤ k* via NK+SUMS; k > k* crude via
  π(x^{1/k}) ≤ x^{1/k*}) + the eventual-x threshold folding →
  discharge pp3Term's seqDiscrepancy sum → with the landed
  pp2 bound, N-PP-ASSEMBLY closes PpLevel (3999/4000).
Dispatch: NK ∥ SUMS now; ASSEMBLY after both.

## MERT-3b — THE γ-INTEGRAL FREEZE (house design block; the
## D-risk DISSOLVES on inspection)

The worked chain (house, verified by substitution): with ε = s−1,
(s−1)∫₂^∞ loglog t·t^{−s}dt  =[t = e^u]=  ε∫_{log 2}^∞ log u·
e^{−εu}du  =[v = εu]=  ∫_{ε·log 2}^∞ log v·e^{−v}dv − log ε·
∫_{ε·log 2}^∞ e^{−v}dv  →  (−γ) − log ε·1. Two sub-lemmas:
- **3b-α (the γ-integral):** ∫₀^∞ e^{−v}·log v dv = −γ. Proof:
  differentiate Real.Gamma_eq_integral under the integral at
  s = 1 (mathlib's parametric-integral machinery; dominator
  (t^{−δ}+t^{δ})|log t|e^{−t}) ⟹ HasDerivAt Γ (∫e^{−t}log t) 1;
  equate with the LANDED hasDerivAt_Gamma_one (−γ) by
  derivative uniqueness. C-class — NOT the feared D; the mathlib
  TODO (Gauss's digamma rep) is not needed, only this single
  value.
- **3b-β (the asymptotic):** the two-piece split above with
  explicit tails (|∫₀^{ε·log2}| ≤ ε·log 2·(1+|log(ε log 2)|) → 0;
  the e^{−v}-mass below ε·log 2 → 0). Dominated convergence or
  explicit bounds — executor's choice.
One node MERT-3b lands both. Then 3c (equate MERT-3a's ζ-side
with 3b through MERT-1's Abel form) → 4 → 5.

## OPTION-C RESOLVED: RED — Littlewood CANNOT clear the MR gate,
## by coefficient arithmetic (house analysis, no recon needed)

The pretentious-distance form is scale-free and settles it:
D(λ, n^{it}; x)² = loglog x + log|ζ(1+it)| + O(1), and the gate
needs D² → ∞ (fixed-δ₀ grade: D² ≥ K) at heights t ≍ x^A. A
zero-free region of width (log t)^{−θ} gives log|ζ(1+it)| ≥
−θ·loglog t, so D² ≥ (1−θ)·loglog x — diverges for ANY θ < 1.
Littlewood's region has COEFFICIENT EXACTLY 1 (width
loglog t/log t ⟹ log|ζ| ≥ −loglog t + logloglog t), so D² ≥
logloglog x + O(1) — bounded. No re-parametrization of Tao's
P₋/P₊ cutoffs escapes this: the coefficient arithmetic is
invariant under cutoff choices (both loglog terms shift
together). CONSEQUENCES: (1) the MR gate = any power region
θ < 1 strictly — and by VK-R0's quantization (θ ∈ {1, ≤3/4},
nothing between) that means VINOGRADOV MACHINERY, full stop;
(2) the VMVT decision at the Littlewood checkpoint is now a
clean GO/NO-GO with no cheap third option; (3) the Littlewood
checkpoint's value is unchanged (historic first + infrastructure)
but it is NOT a route to MR. Register updated.

## VMVT-R0 ADJUDICATED (2026-07-17): GO — STAGED AND GATED;
## catch #58 (the fixed-k hope is provably dead)

**CATCH #58 (recon-kills-house-hypothesis):** the fixed-small-k
simplification does NOT exist — GROUNDED via the dyadic
optimization in the growth step (Vaughan PSU Ch. 24, Cor. 24.16):
the optimal depth r* ∝ (1−σ)^{−1/2}, degree k = 100r* → ∞; a
fixed k truncates the maximization and degrades the growth
exponent to α = 1 = Littlewood only. The VK-R0 quantization gap
(3/4, 1) IS this phenomenon — there is no "a little Vinogradov."
Consolation: crude Linnik–Karatsuba η suffices (η(k,r) =
½k²(1−1/k)^r, NOT Wooley/BDG), and θ = 2/3 costs the same as any
worse θ — target it directly.

**The campaign structure (accepted):** WP-A (the VMVT core:
J_k + Newton base case + LINNIK'S LEMMA + the k-uniform p-adic
induction; 2.5–4.5M, the pole; the torus-Parseval vs
combinatorial-count FORK is the widest error bar — Fable design
call at the fork point) / WP-B (the k-dim Weyl chain, 2–4M,
joins onto the Littlewood A-process) / WP-C (growth→region
re-parametrization of the SW seam, 1.3–2.3M, shares the
Littlewood back-half). Total 6.3–11.8M, central ~8.5M —
CONFIRMS the prior. Reclassification that matters: LARGE-C
PORTING, not D-open (the math is 70-years-settled; Vaughan's
Ch. 24 is the porting target, decoded in the scratchpad:
psu_dedup.txt + ford_zeros.txt).

**THE GATE (accepted; executes JYH's "full VMVT" ratification as
staged spend):** the first ~2M buys (a) the Littlewood checkpoint
close-out (the shared spine is real: the A-process feeds WP-B,
the back-half seam feeds WP-C) + (b) the VMVT-FOUNDATION PROBE =
VMVT-N1 (J_k + Lemma 24.1, DISPATCHED) → N2 (the k!·x^k base
case via mathlib Newton/Vieta) → **N3 = LINNIK'S LEMMA (the gate
node: its outcome converts 6–13M into a tight ~6–9M commit or an
early honest re-scope)**. WP-A runs parallel to Littlewood (no
contention — different machinery).

## SHIU-G ADJUDICATED (accepted): N-SHIU-CORE = A RUNG (~440–660k,
## 11 nodes, 4 waves) — the honest re-price above the 250–400k prior

GROUNDED via Wright arXiv:2508.17217 (reproduces Shiu 1980's full
class-partition proof; the 1980 original paywalled, bibliographic-
confirmed). The τ-case skeleton re-derived in our z-normalization,
exponents verified at α = 1/8000: the greedy smooth-prefix
decomposition n = c·d (c ≤ w = z^{α/40}); classes I/II/III/IV_r;
the CAPPED-prime-powers trick killing every √z spike; Rankin at
graded λ_r = ½log r; the φ(q)-saving manufactured ONLY in the
rough-cofactor sieve count. THE POLE: S1 = rough_count_in_ap_le
(frozen statement delivered) via the LANDED selberg_bound_simple
+ the φ-saving harmonic lemma. Supplier-map addendum (collected
by the house): Rankin.lean's rankin_bound EXISTS (squarefree
Euler form — different shape than S3a's smooth-sum Rankin, so
S3a still builds, but rFac machinery helps); GehPp2's τ-swap +
sum_card_divisors_div_le + PhiSum's totient sums all confirm the
recon's consumption list. Waves: W1 = {S1(a+b+c), S2, S3a} →
W2 = {S3b, S4-II} → W3 = {S4-I/III/IV} → W4 = S5 =
sum_tau_in_ap_le : ShiuCore. Fable pre-flight items honored: S2's
definitional API frozen per the recon's spec; S3b's exponent
arithmetic gets adversarial review at its dispatch. W1 DISPATCHED
(3 grouped executors).

## VMVT-R2 DESIGN NOTE (house, day 2): the Hölder gap is an
## IMPORT — mathlib's Finset.inner_le_Lp_mul_Lq (MeanInequalities)
## is general finite-sum Hölder; on N4's rcount signature frame it
## IS Hölder-on-counts. R2's remaining structure: (a) the P(m) =
## ∏_{i<j}(m_i − m_j) pigeonhole (|P| ≤ x^{k(k−1)/2-grade} bounds
## its prime divisors > y by ½k²(k−1)-grade < the CHEB-supplied
## ½k(k²−1) primes ⟹ some selected p has the coordinates
## k-distinct mod p — catch #66's corrected count is exactly what
## makes this close); (b) the truly-degenerate (few distinct
## INTEGER values) count bounded via the choose-and-assign crude
## form where sufficient, else the Hölder re-symmetrization per
## the source's S₁/S₂ split. VMVT-R2 dispatched with the source +
## this note; STOP-AND-FLAG discipline on the S₂ regime.

## SHIU-G2 ADJUDICATED: catch #76's fix is THE TUNED SHIFT —
## δ = 1 − r·log r/(4 log z) (Shiu's own Lemma 4)

The grounded mechanism (Wright §§6–8, verbatim displays): the
r-decay is manufactured on the LARGE SMOOTH PREFIX c-sum, NOT
the d-side — Rankin with the tuned shift turns W^{δ−1} into
exp(−(1/10)·r·log r) = r^{−r/10}, factorial-scale, beating the
pointwise A₅^r term-by-term in the r-sum (Σ (A₅/r^{1/10})^r =
O(1)). Catch #76's route failed ONLY because it Rankin'd at a
FIXED shift (no r-decay). Class III kills by SMOOTH-NUMBER
SPARSITY (the c > W, y₀-smooth prefix is x^{−ε}-sparse — zero
τ(d) paid). For f = τ (bounded at primes) the J-split and ε-loss
of Wright's generalization are UNNECESSARY — pure Shiu suffices.
NEW STONES: NEW-1 the tuned graded Rankin (small C — the shift
choice on the landed smooth-Euler bound + the correction
telescope); NEW-2 the dyadic smooth-prefix tail (B). Then
S4-III/IV assemble on S4-I's landed infrastructure per the
grounded 6-step route. The 1/(j−1)! prime-product count is
explicitly NOT the route (recommended against). SHIU-W3b
DISPATCHED (NEW-1 + NEW-2 + the corrected assemblies).

**SHIU-W3b PARTIAL LANDING (2026-07-17): the STONES are in;
the assemblies FLAGGED.** `Salt/Maynard/ShiuTuned.lean` (sorry-free,
axioms clean, in `All.lean`): **NEW-1 `sum_tau_smooth_gt_tuned_le`**
(the tuned graded Rankin at δ=1−r·log r/(4 log z), factor-2 tight
Euler + `e^t−1≤t·e^t` correction telescope + Mertens-1; RHS =
`exp(−(1/8)r log r + r^{1/4}(log r/2+C₀))·exp(2Σ_{p≤z}1/p+Ce)`) and
**NEW-2 `sum_smooth_gt_tuned_le`** (the unweighted 1/c tail via 1≤τ;
`u^{−u}` de Bruijn grade for free, r·log r=u·log u). The design's
NEW-2 "extra factorial log" worry DISSOLVED — the u^{−u} structure IS
NEW-1's r^{−r/8} at v=y₀. S4-III/IV assemblies FLAGGED (see
flags.md "SHIU-W3b"): two clusters remain — (1) the r-sum
convergence (geometric-vs-factorial; clean route documented,
~80–120 ln, C), (2) the r-binning of the COMBINED shiuClassIIIIV
(ShiuDecomp has no III/IV split predicate; ~200 ln each on the S4-I
template, composition-only, no new math). All ingredients now
exist; dispatch as a fresh executor.

## VMVT-R3 DESIGN (house, night watch): the block change of
## variables — the residue/quotient split

The obstruction (Step.lean's flag): the whole-tuple Ncount/sig
frame has no block decomposition. THE DESIGN: don't decompose
the frame — decompose the COUNTING MAP. For the transversal box
at prime p: each designated coordinate m_i (i < k) splits
UNIQUELY as m_i = ρ_i + p^k·μ_i (ρ_i = m_i mod p^k ∈ ZMod-lift,
μ_i the quotient, 0 ≤ μ_i ≤ x/p^k); each rest coordinate stays
whole. THE COUNTING FACTORIZATION (an injection, not a
bijection — upper bounds suffice):
Ncount 0 (transBox x e p) ≤ Σ_{(rest data)} #{(ρ, μ) : the
graded congruences pin ρ ∈ LinnikSol p k h(rest); μ free in the
box} ≤ (the rest-count) × k!·p^{k(k−1)/2} × (x/p^k + 1)^k
— via THREE lemmas:
- R3-a (the split injection): the map m ↦ (designated residues,
  designated quotients, rest) is injective; the transversality
  (distinct mod p) transfers to ρ (distinctness descends mod p);
  the power-sum system at precision p^j (j ≤ k) DEPENDS ONLY ON
  ρ (μ contributes multiples of p^k ≥ p^j) — the graded system
  h(rest) := (the targets minus the rest's power sums) mod p^j
  is well-defined from the rest alone. [The piFinset injection +
  ZMod.castHom arithmetic; the Linnik.lean encoding patterns.]
- R3-b (the fibre bound): for FIXED rest and h: the ρ-count ≤
  linnik_lemma's k!·p^{k(k−1)/2} (the LinnikSol membership is
  R3-a's conclusion); the μ-count ≤ (x/p^k + 1)^k trivially.
- R3-c (the rest-count): Σ over rest-tuples of 1 — the rest
  ranges in the box: ≤ x^{(r−1)k}... NO — the honest form: the
  rest is UNCONSTRAINED in the fibre bound (the constraints
  moved into h(rest)) — the rest-sum is the FULL box count
  x^{k(r−1)}?? That loses the J-structure. THE CORRECT
  BOOKKEEPING (the source's): the rest carries ITS OWN pair
  structure — the transBox counts PAIRS (m, n) with the joint
  system; the split applies to BOTH sides; for fixed (ρ_m, ρ_n,
  μ-boxes) the REST PAIR satisfies the SHIFTED system (shift =
  the designated blocks' contribution) ⟹ the rest-pair count ≤
  JkShift ≤ Jk (24.1e!) at (r−1)k variables and scale... the
  rest lives in (0, x] — but the IH is at x/p: THE DILATION: the
  designated μ's range in (0, x/p^k]-boxes and the ρ-classes
  fix the arithmetic — the source dilates by writing the
  designated m_i = ρ_i + p^k μ_i with the μ-box A' of size
  x/p^k, and applies the IH to THE REST at the ORIGINAAL scale
  via... [re-read the source's step at dispatch; the safe
  frozen form: Ncount(transBox p) ≤ k!·p^{k(k−1)/2}·(x/p^k+1)^k
  · Jk k (k(r−1)) (Icc 1 x) — with the p-power savings carried
  by the ρ/μ split and the IH consumed at the SAME scale x but
  FEWER variables (the exponent arithmetic: vmvtExp_succ was
  verified against exactly this shape: x^k·p^{k(k−1)/2}·
  p^{−k·k}-ish·J(x, k(r−1)) — CHECK the resume map's accounting:
  "Linnik m-freedom x^k + Hölder p^{2rk−2k} + Linnik residues
  p^{k(k−1)/2} + IH at x/p" — the IH at x/p comes from μ-box
  dilation of the REST?? — RESOLVE AT DISPATCH against
  psu_dedup.txt; freeze R3-a/b as stated (they are source-
  independent) and let R3-c follow the source verbatim.]
DISPATCH: R3-a + R3-b now (source-independent); R3-c with the
source open.

## VMVT R3-c FREEZE (house, night watch 2, post-catch-#78): the
## Hölder-over-residues step goes through the INTEGRAL side

Catch #78 proved the combinatorial frame cannot reach the source
bound: the p^{k(k−1)/2} savings + x→x/p scale drop emerge ONLY
inside the single-residue-class restriction, entangled with the
Hölder step. RESOLUTION: the landed Fourier machinery
(`integral_setGen_mul_conj` is fully general in D, E) carries the
Hölder step on integrals, exactly as the S₂ branch did. Source:
PSU 24.5 (psu_dedup.txt ll. 363–457). New file
`Salt/Vmvt/Transversal3.lean`. THE SIX RUNGS:

- **c-1 (system translation)** `powerSumEq_sub_const`:
  `PowerSumEq k b m n ↔ PowerSumEq k b (·−a) (·−a)` — binomial
  triangular: Σ(m−a)^j = Σ_{i≤j} C(j,i)(−a)^{j−i}Σm^i, the i=0
  term b·(−a)^j equal on both sides; prove one direction ∀a, get
  iff via a ↦ −a. (Also its ShiftEq analogue if convenient.)
- **c-2 (block factorization over an injective e)**: for the
  per-coordinate character `gcoord` (HolderTwo), and a filter
  touching ONLY the designated block:
  `setGen(transBox x e p) = Gdesig(α) · f(α)^(kr−k)` and
  `setGen(mixBox x e p a) = Gdesig(α) · g_a(α)^(kr−k)`, where
  `Gdesig = Σ_{desig k-tuples ∈ Ioc(0,x]^k, distinct mod p} ∏ gcoord`,
  `f = genFun k (Ioc 0 x)`, `g_a = genFun` over the residue-a
  subset `(Ioc 0 x).filter (· ≡ a mod p)`, and
  `mixBox x e p a := (solBox).filter (blockDistinctMod e p ∧
  ∀ q ∉ Set.range e, (m q − a) ≡ 0 mod p)`. Route: reindex the
  piFinset sum via `Fin (kr) ≃ range-e ⊕ complement`
  (mirror `sum_prod_filter_eq`'s collapsed-sum pattern).
- **c-3 (pointwise power-mean + swap)**: `f = Σ_{a<p} g_a`
  (residue fiberwise partition of Ioc(0,x]); pointwise
  `‖f‖^{2b} ≤ (Σ_a ‖g_a‖)^{2b} ≤ p^{2b−1}·Σ_a ‖g_a‖^{2b}`
  (power-mean/Jensen; mathlib `Finset.pow_sum_div_card_le_sum_pow`
  — MEMORY, verify; hand fallback ~30 ln). Multiply by ‖Gdesig‖²,
  integrate, swap ∫/Σ (finite sum, integrable: all finite trig
  polys, the `integrable_gterm`/fun_prop pattern):
  `I(p) ≤ p^{2b−1} Σ_a ∫‖Gdesig‖²‖g_a‖^{2b}`, b := kr−k.
- **c-4 (mixed Parseval)**: `∫‖Gdesig‖²‖g_a‖^{2b} =
  Ncount k (kr) 0 (mixBox a) (mixBox a)` via c-2 +
  `integral_setGen_mul_conj` (B = C = mixBox).
- **c-5 (the fibration — the meat, ~250 ln)**:
  `Ncount 0 (mixBox a) (mixBox a) ≤ x^k · k!·p^{k(k−1)/2} ·
  Jk k (k(r−1)) (Icc 1 (x/p+1))` under `x < p^k`:
  (i) bijection `mixBox ≃ desigMod × uboxProd` (rest = p·u + a,
  ubox an explicit Ioc of card ≤ x/p+1; recovery linear);
  (ii) fibrate the pair count over designated pairs (md, nd);
  (iii) by c-1 translate by a: the inner system is
  `p^j·Σv^j − p^j·Σu^j = D_j(md,nd)` with
  `D_j = Σ(md−a)^j − Σ(nd−a)^j` ⟹ inner count = 0 unless
  `∀j, p^j ∣ D_j` (the graded set B(p,a)), else
  `= Ncount k (k(r−1)) ℓ uboxProd uboxProd`, `ℓ j = D_j/p^j`;
  (iv) `Ncount_shift_le` + `Ncount_zero_eq_Jk` + `Jk_image_add`
  → inner ≤ `Jk k (k(r−1)) (Icc 1 (x/p+1))`;
  (v) `card B(p,a) ≤ x^k·k!·p^{k(k−1)/2}`: md free (box count);
  nd−a in an **Ioc-generalized desigFibre** (R3-b′, ~90 ln:
  re-run `desigFibre_card_le` over `Ioc lo (lo+len)` with
  `μ_q = ((ñ_q − lo).toNat)/p^k`; at `x < p^k` the μ-box is a
  point, factor `(len/p^k+1)^k = 1`); the LinnikSol targets
  `h_j := (D-pinned c_{j+1} : ZMod (p^k))`, castHom-compatible.
- **c-6 (assembly)** — THE FROZEN TARGET:
  `theorem transBox_Ncount_le {k r : ℕ} (x p : ℕ)
    (e : Fin k → Fin (k*r)) (he : Function.Injective e)
    (hp : p.Prime) (hkp : k < p) (hk : 0 < k) (hr : 1 ≤ r)
    (hpx : x < p^k) :
    Ncount k (k*r) 0 (transBox x e p) (transBox x e p)
      ≤ p^(2*(k*r) − 2*k) * (x^k * k.factorial * p^(k*(k−1)/2))
        * Jk k (k*(r−1)) (Finset.Icc 1 (x/p + 1))`
  via chaining c-3/c-4/c-5 with the a-sum bounded by p × the
  uniform c-5 bound (NO max — Σ_a ≤ p·uniform, dodging ∫-max).
  (r = 1: rest empty, f^0 = 1 — handle or flag; the consumer
  R4-S₁ always has r ≥ 2.)
Matches the R4 accounting "m-freedom x^k + Hölder p^{2rk−2k} +
Linnik p^{k(k−1)/2} + IH at x/p". Est ~700 ln. Zeno: stone 1 =
c-1+c-2+c-3+c-4 (I(p) ≤ p^{2b}·mixCount uniform); stone 2 = c-5;
close = c-6.

## LITT-REGION RE-PRICING (house, night watch 2): convexity
## cannot give the loglog region — the conversion is THREE nodes

Design finding (recorded before any freeze; full design deferred
to a dedicated block, same treatment as T-BAL). The landed
`zeta_growth_strip` (ZetaApprox) is CONVEXITY-grade:
‖ζ(σ+it)‖ ≤ 10·t^{1−σ}(1+log t). The Landau-method arithmetic:
with circles of radius r near 1+it, the growth input gives
log M ≈ r·log t + loglog t, and the resulting zero-free width
r/log M saturates at ≈ 1/log t for EVERY choice of r (optimum
r ≈ loglog t/log t gives width 1/(2 log t)). So the convexity
bound can only reproduce the landed c₃/log t region
(`zeta_zero_free_region`) — Littlewood's loglog/log upgrade
PROVABLY needs the Weyl-strip subconvexity input near σ = 1,
i.e. the vdC-k phase saving. The landed phase machinery
(`zeta_partial_growth`, `zeta_dyadic_assembly`) is
window-CONDITIONED (each dyadic block needs the k-dependent
sandwich on t/(2π)·(k−1)!/(2N+k)^k) — the un-conditioned strip
bound is exactly the flagged LITT-COVER residual. THE HONEST
CHAIN (re-priced):
- **LITT-COVER** (C): the k-per-window coverage assembly — for
  every dyadic N ≤ t choose k(N) so the sandwich holds; output
  an UNCONDITIONED phase-sum bound on (N₀, t]-grade windows.
- **LITT-STRIP** (C): partial summation → the Weyl strip bound
  ζ(σ+it) ≪ (log t)·t^{b·2^{−k}} for σ ≥ 1 − a·2^{−k}-grade,
  k free (the per-k family; Titchmarsh 5.13 shape).
- **LITT-LANDAU** (C/D, the crux): re-run the SW 3-4-1/Davenport
  chain (`ZetaZeroFree.lean` machinery) with the per-k strip
  family via Borel–Carathéodory, optimize k ≈ loglog t →
  σ ≥ 1 − c·loglog t/(log t) — THE HISTORIC CHECKPOINT. Whether
  the landed fixed-strip 3-4-1 assembly parametrizes cleanly or
  needs a fresh log-derivative chain is THE design question for
  the dedicated block.

## VMVT-R5b FREEZE (house, post-R4): the vmvtC0 re-grade + the
## medium-x trivial branch + THE SUMMIT INDUCTION

R4's stone-2 flag is correct: the fixed C₀ = k⁶·k!·2^{k²}·3 is
exp-grade too small for the trivial branch to reach the
pigeonhole threshold. The source's D(k,r) = exp(Crk²log k) with
C FREE is the designed absorber (PSU 24.5 lines 290–311: "if
x ≤ exp(C max(k,r) log k) ... the trivial estimate gives the
Theorem"). AUTHORIZED STATEMENT CHANGE (Fable): redefine

  vmvtC0 (k : ℕ) : ℝ := (k : ℝ) ^ (8 * k ^ 2)

(vmvtConst = C₀^r and VmvtBound keep their FORM; vmvtExp/
vmvtEta/vmvtExp_succ UNTOUCHED — the exponent is the
load-bearing content, the constant is free per the source and
the file's own docstring). Threshold: Xmed k r := k ^ (8 * max
k r) (ℕ-power). THE ARITHMETIC (all margins checked):

- Bridge: k ≥ 2 → k⁶·k!·2^{k²}·3 ≤ k^{8k²} (k! ≤ k^k, 2^{k²} ≤
  k^{k²}, 3 ≤ k², exponents 6+k+k²+2 ≤ 8k² ⟸ k ≥ 2). Every
  landed proof that consumed the old value (mul_pred_pow_le_
  vmvtC0, vmvt_base, the degen branch, StepFull's
  transBox_le_const fold) re-closes THROUGH the bridge — patch
  mechanically, do not re-derive.
- Trivial branch (vmvt_trivial_branch): x ≤ Xmed k r →
  VmvtBound k r x. JkI ≤ (x^{kr})² = x^{2kr} crude; deficit
  2kr − E = ½k(k+1) − η with (i) ≤ k² (η ≥ 0), (ii) ≤ kr via
  Bernoulli (1−1/k)^r ≥ 1 − r/k (mathlib one_add_mul_le_pow at
  x := −1/k) → η ≥ ½k² − ½kr. Then x^{deficit} ≤
  k^{8·max(k,r)·min(k²,kr)} ≤ k^{8rk²} = C₀^r (max·min ≤ rk²
  by the r ≤ k / r > k case split).
- Prime supply at x > Xmed: y = vmvtScale ≥ x^{1/k} ≥
  k^{8·max(k,r)/k} ≥ k⁸; primes_in_Ioc_ge (c = 1/8; RECON its
  own thresholds) gives #(y,2y] ≥ y/(8 log y) ≥ ½k³ + 1-grade
  at y ≥ k⁸ (k^5 ≥ 32·ln k·-grade, k=2: 32 ≥ 22.2 ✓) ⟹ hpig
  k·k·(k−1) < 2·#P. hreg k² + 4E ≤ y: E ≤ 2rk + η ≤ 2rk + ½k²,
  exponential y beats linear ✓.
- hrange b ≤ E: PROVABLE ∀ r ≥ 1, k ≥ 2 (equality at r=1):
  discrete induction, f(r+1) − f(r) = k − η(k,r)/k ≥ k/2 ≥ 0
  with f(1) = 0. Side lemma, ~20 ln.
- THE INDUCTION (vmvt, the summit): induct on r ≥ 1 for fixed
  k ≥ 2, ∀x. Base: vmvt_base through the bridge. Step: given
  IH ∀x' (VmvtBound k r x'), for x at r+1: x ≤ Xmed k (r+1) →
  trivial branch; x > Xmed → discharge the landed
  vmvt_step_transversal_large's hypotheses (hpig/hreg/hrange/
  scale facts per above) and apply it with the IH. Target:
  `theorem vmvt (k r x : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r)
  (hx : 1 ≤ x) : VmvtBound k r x`.
Est ~400–500 ln incl. patches. Zeno: stone 1 = re-grade +
bridge + all patches green; stone 2 = trivial branch; ██ stone
3 = vmvt — THE VINOGRADOV MEAN VALUE THEOREM ██.

## VMVT-SUMMIT-2 FREEZE (house, post-R5b flag / catch #102):
## the effective prime supply + the final bridge

R5b's flag: primes_in_Ioc_ge only PROVES y/(8 log y) for y ≥
y₀ = max(⌈e^{6K}⌉, 1280000), K a bare PNT existential — the
threshold is k-independent and non-explicit, so no fixed-power
trivial branch bridges it. LESSON (catch #102, now standing):
freeze margins must be checked against the LEMMA'S PROVEN
RANGE, never the inequality's truth. THE REPAIR — two stones:

**Stone A (VMVT-PRIME, class C): the effective interval count.**
New Salt/Vmvt/PrimeEff.lean. Target shape:
  `theorem primes_in_Ioc_eff : ∃ y₁ : ℕ, y₁ ≤ 2^24 ∧
   ∀ y : ℕ, y₁ ≤ y →
   (y : ℝ) / (8 * Real.log y) ≤
   (((Finset.Ioc y (2*y)).filter Nat.Prime).card : ℝ)`
(∃-form deliberately: the executor proves it at WHATEVER
explicit y₁ the argument honestly yields, ≤ 2^24; smaller is
fine, do not chase.) Route: the Erdős/Bertrand central-binomial
argument, whose machinery mathlib ALREADY CARRIES
(Mathlib.NumberTheory.Bertrand: centralBinom bounds; primorial
bounds in Mathlib.NumberTheory.Primorial) — RECON FIRST what
exists (Nat.centralBinom_le_..., Nat.primorial_le_4_pow /
primorial_lt_..., the Bertrand proof's decomposition of
C(2y,y) into prime-power factors). The count extraction:
∏_{y<p≤2y} p divides C(2y,y); each such p ≤ 2y ⟹
∏ ≤ (2y)^{count}; lower-bound ∏ from C(2y,y) ≥ 4^y/(2y+1)
divided by the ≤-√(2y)-powers block ((2y)^{√(2y)}) and the
≤-2y/3 primorial block (4^{2y/3}) ⟹ (2y)^{count} ≥
4^{y/3}/((2y+1)(2y)^{√(2y)}) ⟹ count ≥ (y·log 4/3 −
√(2y)·log(2y) − log(2y+1))/log(2y). Then count ≥ y/(8 log y)
⟸ y(log4)/3 − √(2y)log(2y) − log(2y+1) ≥ y·log(2y)/(8 log y)
— CARE: log(2y)/log y ≤ 1 + 1/log y ≤ 1.1-grade at y ≥ 2^10,
so RHS ≤ 0.1375·y·... honest check at y = 2^20: LHS ≈
0.462·1.05M − 1448·14.6 − 14.6 ≈ 485k − 21.1k ≈ 464k; RHS =
1.05M·14.6/(8·13.9) ≈ 137.6k ✓ factor 3.4 margin; at y = 2^14:
LHS ≈ 7568 − 181·10.4 − 10.4 ≈ 5674; RHS = 16384·10.4/(8·9.7)
≈ 2196 ✓ factor 2.6; at y = 2^12: LHS ≈ 1892 − 90.5·9.0 − 9 ≈
1069; RHS = 4096·9.0/(8·8.3) ≈ 555 ✓ factor 1.9. y₁ = 2^12 =
4096 has margin; freeze y₁ target ≤ 2^14 with 2^24 as the
formal cap. (If mathlib's primorial/centralBinom forms force
lossier constants, y₁ grows — anything ≤ 2^24 closes stone B.)
**Stone A2**: `exists_transversal_prime_set'` — re-run the
landed exists_transversal_prime_set (Step.lean) with the
effective supply: Y'(k) := max(y₁, 64·(k²·(k−1)+1)², 2) —
now EXPLICIT with Y'(k) ≤ max(2^24, 64·(k³+1)²) ≤ 2^24·k⁶-crude.
Do NOT edit the landed one; a new primed decl beside it.

**Stone B: the bridge + THE SUMMIT.** Second authorized
re-grade (same source justification, C free): vmvtC0 :=
k^{24·k²}, Xmed := k^{24·max k r}. Bridge arithmetic
(house-checked): (a) old k^{8k²} ≤ k^{24k²} — the R5b bridge
composes (patch old_c0_le's consumers by transitivity, or
re-point the bridge constant — executor's choice, mechanical);
(b) the trivial branch re-runs verbatim at 24 (the deficit
chain max·min ≤ rk² is exponent-uniform); (c) THE NEW BRIDGE
CHECK (the R5b gap, now closing): need Xmed ≥ Y'(k)^k-grade,
i.e. k^{24·max(k,r)} ≥ (2^24·k⁶)^k = 2^{24k}·k^{6k}:
k^{24k} = k^{6k}·k^{18k} and k^{18k} ≥ 2^{24k} ⟺ k^{18} ≥
2^{24} ⟺ 18·log₂k ≥ 24 ⟺ k ≥ 2^{4/3} ≈ 2.52 — **FAILS at
k = 2!** k=2: Xmed = 2^{48} vs Y'(2)^2 ≤ (2^24·64)² = 2^{60}.
RESOLUTION for k = 2: Y'(2) = max(y₁, 64·(4·1+1)², 2) =
max(y₁, 1600) = y₁ (y₁ ≥ 4096) — the k⁶-crude bound is lossy
at k=2; use Y'(2) = y₁ ≤ 2^{14} (the stone-A target, NOT the
2^{24} cap): Y'(2)² ≤ 2^{28} vs Xmed = 2^{48} ✓✓. GENERAL
honest form: Xmed ≥ (max(y₁, 64(k³+1)²))^k with y₁ ≤ 2^{14}:
(i) y₁-arm: k^{24k} ≥ 2^{14k} ⟺ k^{24} ≥ 2^{14} ✓ k ≥ 2
(2^{24} ≥ 2^{14}); (ii) polynomial arm: k^{24k} ≥ (256k⁶)^k ⟺
k^{18} ≥ 256 = 2^8 ✓ k ≥ 2 (2^{18}). BOTH ARMS CLEAR at
y₁ ≤ 2^{14}. [CORRECTED post-refuter 05:00: the "2^{24} cap is
dead" conclusion here was WRONG — an artifact of the lossy
product bound Y' ≤ 2^{24}·k⁶. Under the honest max-form arms,
the y₁-arm at cap 2^{24} needs k^{24} ≥ 2^{24}, which holds
for ALL k ≥ 2 (equality at k=2; non-strict suffices — the
split supplies strict x > Xmed, so y^k ≥ x > Xmed ≥ Y'^k gives
y > Y' strictly). ⟹ stone A targets y₁ ≤ 2^{14} (margin
factor 2.6 at the corner; the real inequality holds from
y ≈ 1200) but ANY y₁ ≤ 2^{24} still closes stone B — do NOT
stop-and-flag on overshooting 2^{14}.] Then the
induction assembles exactly as the R5b freeze specified
(trivial ∨ large by x vs Xmed; the large branch's y ≥ Y'(k)
from x > Xmed ⟹ y ≥ x^{1/k}-grade ≥ Xmed^{1/k} =
k^{24·max/k} ≥ both arms per the same two-arm check). Target:
`theorem vmvt (k r x : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r)
(hx : 1 ≤ x) : VmvtBound k r x` ██ THE SUMMIT ██.
Est: A ~350 ln, A2 ~80, B ~250 (mostly re-runs). Zeno: A → A2
→ B-regrade → ██ vmvt ██.

## LITT-COVER FREEZE (house, 04:10 gate honored): the per-k
## window discharge of the block sandwich

The consumer chain (LITT-COVER → LITT-STRIP → LITT-LANDAU, see
the RE-PRICING section). This node: discharge `zeta_block_bound`'s
sandwich hypothesis (ZetaBlock.lean:367 — λ := t/(2π)·(k−1)!·
(2N+k)^{−k} ∈ [N^{−3+8/2^k}, N^{−1}]) from clean WINDOW
inequalities in (t, N) alone. THE HONEST MARGIN FINDING (house,
checked): the naive window t ∈ [N^{k−2}, N^{k−1}] FAILS the
upper edge for k ≥ 8 — λ ≤ N^{−1} at t = N^{k−1} forces
(k−1)! ≤ 2π·2^k, false from k = 8 (5040 > 1608). The factorial
must be absorbed by an N-floor, NOT window-edge constants (which
would break the k↔k+1 overlap). THE FREEZE:

- Target (AMENDED post-verify 04:23 — the original bullet was
  stale vs the section's own later findings; a 3-refuter pass
  confirmed every margin, 0 refutations, and flagged the
  staleness): `theorem zeta_block_window (k : ℕ) (hk : 4 ≤ k) :
  ∃ C N₀ : ℝ, 1 ≤ C ∧ ∀ (t : ℝ) (N : ℕ), N₀ ≤ N →
  (N:ℝ)^(k−2:ℝ)/((k−2).factorial) ≤ t →
  t ≤ (N:ℝ)^(k−1:ℝ)/((k−1).factorial) →
  ‖Σ_{n ∈ Ioc N (2N)} eR (phi t n)‖ ≤ C·N^{1−1/(2^k−2)}`
  with N₀ := (k.factorial : ℝ)^6 — NOT (k!)³, which fails this
  section's own absorption chain at k=4 (117.6 < 508.9); do not
  tune N₀ below (k!)^6 without re-running the k-sweep. k = 3 is
  EXCLUDED here (stone 2's seam). Verified gifts for the
  executor: the upper edge needs NO N-floor (λ ≤ N^{−1}/(2π·2^k)
  by edge construction); k=4's exponent step 1−8/2⁴ = 1/2 is
  exact EQUALITY — use non-strict rpow monotonicity; the
  factorial absorption has a clean non-inductive route
  (k!)³/(k−2)! = (k!)²·k(k−1) ≥ 3·4^k ≥ 7·3^k ≥ 2π·3^k via
  k! ≥ 2^{k−1} (replace 2π by 7 to dodge pi estimates).
- Upper edge: λ ≤ t·(k−1)!/(2π·(2N)^k) ≤ [t ≤ N^{k−1}/(k−1)!]
  ≤ N^{−1}/(2π·2^k) ≤ N^{−1} ✓ (the factorial cancels by
  CONSTRUCTION of the edge; 2π·2^k ≥ 1).
- Lower edge: λ ≥ t·(k−1)!/(2π·(2N+k)^k) ≥ t/(2π·(3N)^k)
  (k ≤ N₀ ≤ N kills the +k; (k−1)! ≥ 1) ≥ N^{k−2}/(2π·3^k·N^k)
  = N^{−2}/(2π·3^k) ≥ N^{−3+8/2^k} ⟸ N^{1−8/2^k} ≥ 2π·3^k ⟸
  [k ≥ 3 → 1−8/2^k ≥ 0 at k=3 exactly 0 — CARE: at k=3 the
  exponent is 0, need 1 ≥ 2π·27 FALSE!] — k = 3 needs its own
  margin: at k=3, 8/2³ = 1, lower sandwich is λ ≥ N^{−2}, and
  λ ≥ N^{−2}/(2π·27) MISSES by the constant. RESOLUTION: run
  the k=3 window as t ∈ [c₃·N, N²/2] with the DerivTest
  (vdC_third_derivative) directly, or start the ladder at k=4
  and cover the k=3 regime by vdC_second_derivative
  (VdCorput2's C'=8, its own window t ≈ N²-grade — RECON which
  landed second/third-derivative form spans t ∈ [N^{1+δ}, N²];
  the executor picks the seam and records it). For k ≥ 4:
  1 − 8/2^k ≥ 1/2, so N^{1/2} ≥ 2π·3^k ⟸ N ≥ (2π·3^k)² —
  absorbed by N₀ = (k!)³ for k ≥ 4 ((k!)^{3/2} ≥ 2π·3^k ⟸
  k ≥ 4: 24^{1.5}=117 ≥ 6.28·81=509 FALSE at k=4! → take
  N₀ := (k.factorial)^6: 24³ = 13824 ≥ 509 ✓ k=4; k=5:
  120³ ≫ 1527 ✓; grows factorially vs exponentially ✓).
  FREEZE N₀ := (k.factorial : ℝ)^6.
- Window overlap (for LITT-STRIP's gluing, prove as a side
  lemma): windows k and k+1 overlap in t for N ≥ N₀:
  N^{k−1}/k! ≥ N^{k−1}·[need ≥ (k+1)-window lower = N^{k−1}] —
  window k+1 lower edge is N^{(k+1)−2} = N^{k−1} vs window k
  upper N^{k−1}/(k−1)!: OVERLAP FAILS by the factorial!
  RESOLUTION (design decision): make the window LOWER edge also
  factorial-shifted: window k := {N^{k−2}/(k−2)! ≤ t ≤
  N^{k−1}/(k−1)!}. Lower-edge margin re-check: λ ≥
  t/(2π(3N)^k) ≥ N^{k−2}/((k−2)!·2π·3^k·N^k) — the (k−2)! now
  hurts the lower margin: need N^{1−8/2^k} ≥ 2π·3^k·(k−2)! —
  still factorial-vs-N₀ = (k!)^6: (k!)^{6(1/2)} = (k!)^3 ≥
  2π·3^k·(k−2)! ✓ trivially k ≥ 4. Adjacent windows now MEET
  exactly (k-upper = N^{k−1}/(k−1)! = (k+1)-lower). ✓
- Consumers downstream (NOT this node): LITT-STRIP glues over
  k with partial summation; the k=3 seam per above.
Est ~300–450 ln, class C, one new file Salt/ExpSum/Window.lean.
Zeno: stone 1 = the k ≥ 4 window theorem; stone 2 = the k=3
seam + the overlap lemma.
