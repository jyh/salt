# Rung 4a — explicit gaps ≤ 12 (Fable design, 2026-07-10)

Target track: `explicit12`. Replace the crude logarithmic tensor weights
(which forced `k₀ ~ exp(7·10⁶/c)` and "some C") with Maynard's genuine
polynomial weights at `k = 5`, certifying `M₅ > 2` in exact rational
arithmetic, and prove the iconic explicit bound. This doc is the wave-1
design per the wave protocol (`docs/MODEL_POLICY.md`); waves 2+ get their
cards at the next Fable pre-flight, after wave 1 lands.

## 1. The target statement (frozen shape; Fable-tier decision)

```lean
/-- PNT-quality prime supply in the (N, 64N] window: for every ε there is a
threshold past which Δπ ≥ (63−ε)·N/log N.  A trivial consequence of PNT;
stated as an interface (like `HasLevel`) because mathlib has no PNT — the
PrimeNumberTheoremAnd project can discharge it the day we take the dep. -/
def WindowPNT : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
    (63 - ε) * (N : ℝ) / Real.log N
      ≤ (Nat.primeCounting (64 * N) : ℝ) - (Nat.primeCounting N : ℝ)

/-- The full Elliott–Halberstam conjecture: every level θ < 1. -/
def EHall : Prop := ∀ θ : ℝ, 0 < θ → θ < 1 → EH θ

theorem gaps_le_twelve (hPNT : WindowPNT) (hEH : EHall) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-12 : ℤ) 12
```

**Why `WindowPNT` is unavoidable (worked at design time — do not re-litigate
at Opus tier).** The endgame needs `Σ_m S₂ > S₁` with
`Σ S₂/S₁ ≈ (Δπ·log N/(63N)) · (log R/log N) · M₅`, `R = N^{θ/2}`. The
certified slack is `δ★ = M₅ − 2 ~ 10⁻³`. Chebyshev-type bounds give
`Δπ·logN/N ≥ a·63` only for a *fixed* `a < 1` (classically `a ≈ 0.92`),
inflating the threshold to `M > 2/(a·θ) ≥ 2.17 > M₅` — the method dies.
Enlarging the window `K₀` does not help (the loss tends to `a`, not `1`).
Only `Δπ ~ 63N/logN` (PNT) makes the loss `o(1)`. Every route to an
explicit small constant needs this; the interface makes it honest and
dischargeable. (The landed `BoundedGapsFromEH` escaped this because
crude weights let `M → ∞`, absorbing any fixed Chebyshev loss.)

**Why `EHall`, not `EH (1/2)`.** `M₅ ≈ 2.001`, so the level must satisfy
`θ > 2/M₅ ≈ 0.9995`. Under `EH (1/2)` the threshold is `M > 4`, needing
`k = 105` (Maynard) and gaps ≤ 600 — that variant ("Option A") reuses every
pillar below with a bigger certificate and tuple; deferred as a follow-on.

## 2. The five design insights (the load-bearing decisions)

1. **No measure theory.** `I₅(F)` and `J₅⁽ᵐ⁾(F)` are *defined* as rational
   numbers via the Dirichlet formula
   `∫_{Δ} ∏tᵢ^{cᵢ}·(1−Σt)^d dt = (∏cᵢ!)·d!/(k+d+Σcᵢ)!` — the mean-value
   lemmas (P3) connect sieve sums directly to these rationals. `M₅ > 2` is
   then pure `norm_num` on `ℚ`. No integrals, no interval arithmetic.
2. **Polynomial ⟹ one-dimensional moments.** `y_F(r) = F(t(r))`,
   `tᵢ = log rᵢ/log R`, with `F` polynomial = finite sum of tensor
   monomials. All quadratic forms are bilinear in `y`, and budget powers
   `(1−Σt)^b` expand binomially — so *every* k-dim sum reduces to products
   of one-dim moment sums `Σ μ²(r)/φ(r)·(log r/log R)^a` (the P1 atom).
   The k-fold simplex induction stays inside this class.
3. **Fixed-k license, δ★ budget discipline.** `k = 5` is a numeral: all
   combinatorial constants are `O(1)` and may be crude. BUT the endgame
   slack is `δ★ ~ 10⁻³` *relative*, so every error term must carry an
   explicit constant and an explicit `N`-threshold (the landed
   eventually-engine pattern). The error budget sheet (§5) allocates
   `δ★/8` per consumer. No un-budgeted losses; no crude factors of 2 in
   main terms (the landed `S1_upper`'s `2·main` is unusable here —
   sharp mains throughout, errors only in error terms).
4. **`D` decoupled from `k`.** The primorial cutoff must be a free
   parameter `D` (with `W' = primorial D`), chosen LAST against the
   budget sheet — `D₀ 5 = 125` is far too small (collision/coprimality
   tails `~C/D` vs `δ★/8`). All new statements take `(D, W')` as
   parameters with `(H 5).sup < D`; the landed generic-`W` spine survives,
   the hardwired-`W k` layer gets a mechanical generalization sweep (C3).
5. **The tuple is free.** `H 5 = {7,11,13,17,19}` (first 5 primes > 5,
   landed def) has diameter exactly **12** — the optimal admissible
   5-tuple width. No tuple machinery changes; only concrete evaluation
   lemmas (`hSeq 5` values via `Nat.count`/`Nat.nth_count`).

## 3. Reuse map (from the Maynard track)

**Survives as-is (weight-free, generic or nearly):** the S₂
diagonalization (`s2_diag_lam_restricted`, free `W`), `lemma53` (general
`y`, needs `(W', D)` re-parameterization), the counting layer
(`congCountTuple_approx ±2`, `cong_solvable`, collision-zero, CRT,
`s2PrimeCount_*`), the pigeonhole (`sum_S2m_eq`,
`exists_window_two_primes` — sharpen gap bound from `D₀` to `diam H`),
`compat_pair_fiber_le`, EH consumption shape (`eh_error_pow` at level θ),
`eventually_poly_beats_polylog`, Abel machinery (Brun M6), `exists_nu0`
(re-run CRT at `W'`).

**Replaced (tensor-specific):** everything in
Transfer/TransferSharp/TensorA1/HMain/HOmit/HA11/OvershootCheb/
S2Tensor*/RatioCore/S2MainLower*/VAbs-as-used — the entire crude-weight
evaluation pipeline. Its *proof patterns* (sum-level averaging, erasure,
g↔φ transfer `∏(p−1)/(p−2) = 1+O(1/D)`, box relaxation) are the templates
for P3's corrections.

**Audit needed (C3):** which spine files hardwire `W k`/`D₀ k` in
statements vs take free `W`.

## 4. Pillars

- **P0 — parameter pack** (wave 1, card C3): `k := 5`; free `D`,
  `W' := primorial D`; `hSeq 5` evaluation + `diam = 12`; statement stubs
  (`WindowPNT`, `EHall`); spine audit.
- **P1 — one-dim moment atom** (wave 1, card C2): for `a : ℕ`, `W'`:
  `Σ_{r<z, sqf, (r,W')=1} μ²(r)/φ(r)·(log r)^a
   = (φW'/W')·(log z)^{a+1}/(a+1) + O_{W'}((1+log z)^a)`, explicit
  constant. Plus the `1/g`-weight corollary via the sum-level
  `∏(p−1)/(p−2)` transfer (landed `Ag_le_A1_mul` pattern).
- **P2 — rational I/J calculus + certificate** (wave 1, card C1): the
  `ℚ`-valued pairings and the certified `F★` with
  `2·I₅(F★) < Σ_m J₅⁽ᵐ⁾(F★)`.
- **P3 — the simplex mean value** (wave 2; C-keystone, sketch below):
  for budget-polynomial `G`, the constrained sum
  `Σ_{r ∈ 𝒟} ∏μ²(rᵢ)/φ(rᵢ)·G(t(r)) = X^5·(∫G)·(1 + O(1/log R) + O(C_G/D))`,
  `X = (φW'/W')·log R`, `∫G` the P2-rational. **Sketch:** (i) uncoupled
  version first (drop pairwise-coprimality): the sum factors; induct on
  coordinates peeling the last — the inner sum is a one-dim *budget*
  moment `Σ_{r<Z'} μ²/φ·t^c·((log Z'−log r)/log R)^b`, binomially reduced
  to P1 moments, producing a budget power again (closes the induction,
  rational bookkeeping); (ii) the pairwise-coprimality coupling: sum-level
  inclusion–exclusion over shared primes `p > D` — `(5 choose 2)` pairs,
  each shared-prime term contracts two coordinates and is bounded by
  `Σ_{p>D} 1/(p−1)²`-tails (landed euler-tail pattern) — a
  `1 + O(C_G·25/D)` multiplicative correction. Both `F²` (S₁/I-side) and
  `(F⁽ᵐ⁾)²` (S₂/J-side, after lemma53 turns the contraction into a
  one-dim budget moment = `X·F⁽ᵐ⁾(t(u))·(1+err)`) are instances.
- **P4 — sharp sieve evaluation** (wave 3): S₁ two-sided
  `= (63N/W')·X^5·I₅(F)·(1+o(1)) + O(R²·polylog)`; per-m S₂ lower
  `≥ (Δπ/φW')·X^6·J₅⁽ᵐ⁾(F)·(1−o(1)) − errEH` via the landed counting
  layer + P3 + the collision machinery re-run with polynomial weights
  (bilinear over monomials; fixed-k crudeness fine, budget-tracked).
- **P5 — endgame** (wave 3/4): θ := 1 − δ★/16, `R = ⌊N^{θ/2}⌋`,
  EH consumption at level θ (mechanical `eh_error_pow` variant), the
  master inequality with the §5 budget, `D`-selection, pigeonhole with
  the sharpened `|q−p| ≤ diam(H 5) = 12`.

## 5. Error budget sheet (each consumer ≤ δ★/8 relative; δ★ from C1)

| # | Consumer | Form | Discharge |
|---|---|---|---|
| 1 | level loss `2/θ − 2` | `δ★/8` | choose `θ = 1 − δ★/16` |
| 2 | `WindowPNT` ε | `δ★/8` | instantiate interface |
| 3 | coprimality/collision `D`-tails | `C(F)·25/D` | choose `D` explicit |
| 4 | P3 mean-value `O(1/log R)` | `C(F,W')/log R` | `N`-threshold |
| 5 | lemma53 contraction error | `C·log R/D`-scale rel. `X` | `D` + threshold |
| 6 | EH-consumption error | `(1+log R)^{12}N/(log N)^{14}`-type | `N`-threshold |
| 7 | S₁ truncation `R²·polylog` | `o(N/log N)` | `N`-threshold |
| 8 | g↔φ transfers | `1+O(1/D)` | `D` |

## 6. Wave-1 cards (Opus, all three independent — run in parallel)

### Card C1 — the rational certificate (P2). New file `Salt/Twelve/Certificate.lean`
**Statements (semantics frozen; representation has latitude):** with
exponent vectors `α β : Fin 5 → ℕ` and `Nat.factorial`:
- `DInt (c : Fin 5 → ℕ) (d : ℕ) : ℚ := (∏ i, (c i)!) * d! / (5 + d + ∑ i, c i)!`
- `F` as a finite formal `ℚ`-combination of monomials (list/Finsupp — pick
  what `norm_num`/`decide` handles best);
- `Ical F : ℚ := Σ_{α,β} c_α·c_β·DInt (α+β) 0`;
- `Jcal m F : ℚ := Σ_{α,β} c_α·c_β/((α m +1)·(β m +1)) ·
    (∏_{i≠m}(αᵢ+βᵢ)!)·(α m + β m + 2)! / (6 + ∑(αᵢ+βᵢ))!`
  (this is `DInt` on 4 variables with budget power `α_m+β_m+2`; the `6+Σ`
  exponent is `4 + (budget) + Σ_{i≠m}` — verify the identity, it is the
  crux);
- **`M5_cert : 2 * Ical F★ < ∑ m, Jcal m F★`** for an explicit `F★`.

**Route:** (1) implement the `ℚ` defs; (2) OFF-LINE (python/scratch):
optimize the generalized eigenproblem over the symmetric basis
`{1, P₁, P₂, P₁², P₁P₂, P₁³, P₃, ...}` (expanded to monomials), degree ≤ 3–4
— literature says the optimum is `M₅ ≈ 2.001`; (3) round the optimal
coefficients to small rationals, re-evaluate EXACTLY in `ℚ`, keep
`> 2 + δ★` with `δ★ ≥ 5·10⁻⁴` if achievable (report the certified δ★ —
it drives the whole budget sheet); (4) certify in Lean by
`norm_num [Nat.factorial]`/`decide` (mind kernel-reduction blowup:
precompute factorials or use `Nat.factorial` simp lemmas).
**Traps:** the `(α_m+1)(β_m+1)` divisor and the `+2` budget exponent;
signed coefficients (F★ will have them — keep exact ℚ, no floats in Lean);
`decide` on large ℚ arithmetic can be slow — prefer `norm_num`.
**Verifier brief:** (a) re-derive `DInt` against the Dirichlet formula at
two hand-checkable instances (e.g. `∫1 = 1/5!`, `∫t₁ = 1/6!·1!`); (b)
re-derive the `Jcal` identity independently; (c) check `M5_cert` is about
the DEFINED `Ical/Jcal` (no lateral redefinition); (d) recompute the ℚ
inequality outside Lean.
**PORT-BLOCKER floor:** none permitted — this node is self-contained ℚ
arithmetic; if the search can't beat 2, report the best value found (that
is information, not failure).

### Card C2 — the moment atom (P1). New file `Salt/Twelve/MomentAtom.lean`
**Statement (frozen up to the explicit constant):**
```lean
theorem moment_atom (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W') (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℕ, 2 ≤ z →
      |(∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
          (Real.log r) ^ a / (Nat.totient r : ℝ))
        - (Nat.totient W' / W' : ℝ) * (Real.log z) ^ (a + 1) / (a + 1)|
      ≤ C * (1 + Real.log z) ^ a
```
plus corollary `moment_atom_g` (same with `gMult r` in the denominator,
main term scaled by `∏_{p>D}`-transfer `1+O(1/D)` — or absorb into `C`).
`C` explicit in `(W', a)` — constants discipline; `∃ C` acceptable ONLY if
`C` is uniform in `z` (it is bound before `z` above — keep that order).
**Route:** (1) `a = 0` base, TWO-SIDED: suggested identity
`r/φ(r) = Σ_{d∣r} μ²(d)/φ(d)` (squarefree `r`), giving
`μ²(r)/φ(r) = (μ²(r)/r)·Σ_{d∣r}μ²(d)/φ(d)`; swap sums; inner sums are
squarefree-coprime harmonic sums `Σ μ²(e)/e` — evaluate to density·log
with `O(1)` via mathlib harmonic bounds + Mertens assets
(`Salt/Maynard/Mertens.lean`) — the Brun-M3 technique; the convergent
`d`-sum `Σ μ²(d)/(dφ(d)) = ∏(1+1/(p(p−1)))` reassembles the `φW'/W'`
density. Latitude: any route hitting the stated shape. (2) the Abel lift
`a → a+1`: partial summation (Brun M6 assets) of `(log r)^a` against the
`a = 0` counting function — generic lemma, prove once by induction on `a`.
**Traps:** the coprimality-to-`W'` restriction must thread through the
divisor swap (`d ∣ r ⟹ (d, W') = 1` ✓ automatic); two-sidedness (we need
BOTH directions — the S₂ side needs the lower bound); `log 0/log 1`
boundary terms in Abel.
**Verifier brief:** (a) the main-term density is `φW'/W'` and NOT
`6/π²`-polluted (the classic error — check the reassembly); (b) `C` is
bound before `z`; (c) two-sided; (d) spot-check numerically
(`W' = 2, z = 10³`) outside Lean.
**PORT-BLOCKER floor:** the `a = 0` two-sided base only; the Abel lift
must land.

### Card C3 — parameter pack + spine audit (P0). File `Salt/Twelve/Params.lean` + report
(i) Defs: `WindowPNT`, `EHall` (as §1, verbatim); nothing else stated.
(ii) Evaluate the tuple: `hSeq 5 ⟨i,_⟩` equals `7,11,13,17,19` (route:
`firstIdxAboveK 5 = Nat.count Nat.Prime 6 = 3` by `decide`-able count;
`Nat.nth Nat.Prime (3+i)` via `Nat.nth_count` at each prime); corollary
`(H 5).max − (H 5).min = 12`-shaped facts (whatever form the pigeonhole
sharpening needs: `∀ i j, hSeq 5 i − hSeq 5 j ≤ 12` in ℤ).
(iii) AUDIT (report, no code): for each spine file (KSieve, Diagonal,
S2DiagLam/Restricted, CongCount, Compat, CrossCollision, CollisionQuant,
S2Decomp, S2Eh, S1Bound, CongSolvable, Tuple, Endgame counting layer):
does it take `W` free or hardwire `W k`/`D₀ k` in STATEMENTS? Output a
table {free | mechanical-generalization | tensor-specific-skip} with the
list of lemmas to re-parameterize over `(D, W' = primorial D)`. Also:
confirm the landed S₁ diagonalization identity (Diagonal.lean) is exact
and general-`y`. (iv) `exists_nu0` genericity check for `W'`.
**Verifier brief:** spot-check 3 random audit rows against the actual
signatures; check `hSeq` values by independent computation.
**PORT-BLOCKER floor:** none (A/B-tier throughout); Sonnet-suitable
except the audit judgment calls.

## 7. Deferred to the next Fable pre-flight
P3 cards (the simplex induction — written after C1/C2 land, since the
statement shapes depend on the certified `F★`'s degree and C2's exact
error form); P4/P5 cards; the Option-A (`EH(1/2) → 600`) fork decision;
the `WindowPNT`-discharge dependency decision (PrimeNumberTheoremAnd).

## 8. Known traps (track-wide)
Monomial weights are divisor-MONOTONE (not antitone like `fWt`) — no
antitone-based landed lemma applies to them without re-proof; `F★` has
signed coefficients — absolute-value bounds must be taken per-monomial
(bilinear expansion), never on `F` itself; the S₂ contraction for
polynomial `y` lives on a 4-dim simplex slice (budget `1 − Σ_{i≠m}tᵢ`) —
off-by-one in budget exponents is the likeliest silent error (verify
against `Jcal`'s `+2`); all mains sharp, all crudeness in errors.

---

## C1 off-line result (2026-07-10, Opus) — CERTIFIED F★

Symmetric-polynomial optimization on the 5-simplex (exact ℚ, cross-checked two
ways: symmetric-basis eigenproblem AND full 56-monomial expansion; Dirichlet
sanity `vol Δ₅ = 1/120`, `∫t₁ = 1/720` both pass). Float optimum M₅ ≈ 2.00289
(matches Maynard); sparse integer certificate:

**F★ = 7·1 − 19·m₁ + 28·m₂ + 30·m₁₁ − 15·m₃ − 21·m₂₁ − 19·m₁₁₁**

(monomial symmetric functions on 5 vars: m₁=Σtᵢ, m₂=Σtᵢ², m₁₁=Σ_{i<j}tᵢtⱼ,
m₃=Σtᵢ³, m₂₁=Σ_{i≠j}tᵢ²tⱼ, m₁₁₁=Σ_{i<j<l}tᵢtⱼtₗ). Degree 3, 56 monomials.

- **I(F★) = 1597/399168**
- **Σ_m J⁽ᵐ⁾(F★) = 191881/23950080**
- **M₅ = 191881/95820 = 2.0025151… > 2** ✓
- **δ★ = 241/95820 ≈ 2.515·10⁻³** — the certified relative slack (drives §5).
- Lean reduces to: `2·I < J ⟺ 2·1597/399168 < 191881/23950080
  ⟺ 191640 < 191881` (common denom 23950080). Trivial ℕ inequality after
  evaluation.

Level requirement: θ > 2/M₅ = 191640/191881 ≈ 0.99874, so `EHall` suffices
(pick θ = 1 − δ★/4). Budget-sheet consumers each ≤ δ★/8 ≈ 3.1·10⁻⁴.
Scripts: scratchpad `m5_opt.py`, `m5_verify.py`.

---

## Wave 1 status (2026-07-10) + P3 pre-flight readiness

**Landed on `explicit12`** (axiom-clean throughout):
- C1 `Certificate.lean` — `M5_cert : 2·Ical F★ < Σ Jcal`, `M₅ = 191881/95820 > 2`.
- C3 `Params.lean` — `WindowPNT`/`EHall`, `hSeq 5 = {7,11,13,17,19}`,
  `hSeq_diam_le_twelve`, spine audit (diagonalization core is FREE-W; the
  `(D,W')`-sweep is confined to the counting/prime-side interface).
- C2 `MomentAtom.lean` — `moment_atom` (two-sided, `C` uniform in `a`, exact
  `1/(a+1)` main constant), conditional on `PhiUpperAtom`.
- `PhiUpper.lean` — the hard core of `phiAtom_upper` (the Euler-product
  radical-fiber identity `∑'_{rad n=r}1/n = 1/φ(r)` + reduction to one tail).

**FABLE-QUEUE: (empty)** — no design/impossibility/statement issues arose.

**Opus follow-on leaf (scheduled with wave-2 execution, NOT Fable):**
`phiAtom_upper` tail bound `∑_{v powerful}(1+log v)/v < ∞` (reindex n=u·v
squarefree×powerful; needs a `Nat` powerful/squarefree-part decomposition,
~200 lines). Discharges `PhiUpperAtom` → `moment_atom` unconditional. Required
for the rung's eventual unconditionality; carried as a hypothesis meanwhile
(like `WindowPNT`/`EHall`). Deferred (leaf, non-blocking, possible mathlib gap
— don't grind speculatively).

**P3 pre-flight is now UNBLOCKED** — the two inputs the design deferred P3's
cards for are known: (i) C1 fixed `F★` = **degree 3** (simplex sums top out at
degree-3 monomials, budget powers ≤ `2·3+2 = 8`); (ii) C2 fixed the moment
error form = **`C·(1+log z)^a` with `C` uniform in `a`** (so the P3 induction
carries a single `(1+log R)^{deg}`-type error, no `a`-growth). Next Fable wave:
write the P3 cards (the simplex mean-value keystone, §4-P3 sketch), reconcile
the C3 audit's `(D,W')`-sweep list into a concrete node list, and decide the
`moment_atom_g` (gMult) statement shape now that `F★`'s degree is fixed.
