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
