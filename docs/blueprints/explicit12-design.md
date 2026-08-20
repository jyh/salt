⚓ **TRACK CLOSED — THIS IS A HISTORICAL RECORD, NOT A WORK SOURCE.**
The frontier list below is empty/closed by its own declaration. Live routing:
`docs/QUEUE.md`. Reopening this track is a Fable/human-tier decision (iron rule 5).
This banner is the routing fix of 2026-08-18, landed 2026-08-20 at the Captain's
commissioning ruling; nothing below it was altered.

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

---

# Wave 2 design (Fable pre-flight, 2026-07-10): P3.a/b/e + the spine sweep

Pre-flight run: FABLE-QUEUE empty; design-debt review of wave-1 scaffolding
PASSED (`PhiUpperAtom` matches the documented blocker; C1's `JD` verified
against the contraction semantics — `(αₘ+1)(βₘ+1)` divisor, budget power
`αₘ+βₘ+2`, `6+Σ` denominator — so P3 ties to the certified rationals).

## The P3 design cruxes (worked at Fable tier — binding on execution)

**Crux 1 — FORBIDDEN ROUTE: per-u modulus folding.** In the J-side, `aₘ`
must be coprime to `W'·∏uᵢ`. Folding this into a moment-atom application at
modulus `W'' = W'·∏uᵢ` is a fragility-#1-shaped trap: the atom's constant
`C(W'')` grows like `Σ_{p|∏u} log p/p ~ log R/D` and is unbounded over `u`.
**Binding design:** every moment-atom/budget-moment application is at the
FIXED modulus `W'`; ALL coprimality coupling (pairwise `u`-coprimality, and
`aₘ ⊥ ∏u`) is handled by Möbius/marked-prime expansion `[gcd=1] = Σ_{s|gcd}μ(s)`
at SUM level: each marked prime `p > D` costs `O(1/p)` (weight transfer)
times `O(1/p)` (hit probability), summing to `O(1/D)` total via
`Σ_{p>D} 1/(p−1)(p−2)`-tails (landed euler-tail pattern).

**Crux 2 — g-weights via sandwich.** The J-side outer weights are
`μ²(uᵢ)/g(uᵢ)`. Per-prime `(1−1/p)(1+1/(p−2)) = 1 + 1/(p(p−2))`, so the
g-moment main term is the φ-moment times a singular factor
`𝔖_{W'} ∈ [1, 1 + 8/D]` (all `p ∤ W'` are `> D`). Prove as a two-sided
sandwich `moment_φ ≤ moment_g ≤ (1+8/D)·moment_φ` via ONE marked-prime
application (`1/g(r) = 1/φ(r)·∏_{p|r}(1+1/(p−2))`, expand, mark). Never
compute 𝔖 exactly.

**Crux 3 — the budget-moment reduction.** All multi-dim work reduces to:
`Σ_{r<z} μ²(r)/φ(r)·(log r/log R)^c·((log z − log r)/log R)^b` = binomial
expansion → `moment_atom` at `a = c+j` → collect with the beta identity
`Σ_j (b choose j)(−1)^j/(c+j+1) = c!·b!/(c+b+1)!` → main
`X·B(c,b)·(log z/log R)^{c+b+1}` with `X = (φW'/W')·log R`, error
`≤ C_atom(W')·4^{b+c}` ABSOLUTE (relative `O(1/log R)`). Degrees are tiny:
`F★` deg 3 ⟹ `c ≤ 6`, `b ≤ 8`.

**Crux 4 — decouple analysis from combinatorics.** `mv_I`/`mv_J` (wave 3)
conclude against a recursively-defined `simplexInt : BPoly → ℚ` (the peel
order's own Dirichlet bookkeeping); separate `norm_num` nodes tie
`simplexInt (F★²) = 1597/399168`-value and
`Σ_m simplexInt ((F★⁽ᵐ⁾)²) = 191881/23950080`-value to C1's `Ical/Jcal`.
The analysis never touches ℚ-arithmetic; the arithmetic never touches sums.

**Hypothesis pattern:** g-lemmas and D-corrections take
`(hD : ∀ p, p.Prime → ¬ p ∣ W' → D ≤ p)` (satisfied by `W' = primorial D`);
`PhiUpperAtom W'` rides along as a hypothesis (discharged later by the
deferred tail leaf, for the single final `W'`).

## Wave-2 cards (4, independent, parallel; W2-1/2/3 need no spine changes)

**STATUS — wave 2 LANDED on `explicit12` (2026-07-10), all axiom-clean
`[propext, Classical.choice, Quot.sound]`:**
- W2-1 ✅ `a7c3926` — `beta_sum` + `budget_moment` (φ-version, frozen main term).
  `budget_moment_g` → FABLE-QUEUE (composite marked sum).
- W2-2 ✅ `6eeae61` — `marked_prime_phi`. `marked_prime_g` → FABLE-QUEUE (dead
  end, unneeded; g-sandwich routes through `marked_prime_phi`).
- W2-3 ✅ `b460815` — `BudgetPoly` symbolic ℚ layer; general-`F` ties
  `simplexInt (sq (ofPoly F)) = Ical F` and `… (contractAt m F) = Jcal m F`.
- W2-4 ✅ `c7ee1f9` — `(D,W')` spine sweep, purely additive `*_W` layer;
  capstone `bounded_gaps_from_eh_complete` unchanged + full build green.
- leaf ✅ `4e1b9a8` — `phiAtom_upper` analytic core (`powerful_sum_bounded`);
  `phiUpperAtom_holds` discharges `PhiUpperAtom` modulo `hReindex` → FABLE-QUEUE.
All wired into `Salt/Twelve/All.lean`. Next: wave-3 Fable pre-flight
(`mv_I`/`mv_J`); the φ-version `budget_moment` is the critical-path atom.

### W2-1 (P3.a) `Salt/Twelve/BudgetMoment.lean` — Opus
`beta_sum : ∀ c b, Σ_{j≤b} (b.choose j : ℚ)·(−1)^j/(c+j+1) = c!·b!/(c+b+1)!`
(ℚ; induction on `b` or `decide` per instance for `c+b ≤ 14`; general proof
preferred). Then `budget_moment` (statement frozen up to the constant):
for `W'` sqf pos, `PhiUpperAtom W'`, `c b : ℕ`, `z R : ℕ`, `2 ≤ z ≤ R`,
`1 ≤ log R`:
`|Σ_{r<z, sqf, (r,W')=1} (log r/log R)^c·((log z − log r)/log R)^b/φ(r)
  − (φW'/W')·log R·(c!·b!/(c+b+1)!)·(log z/log R)^{c+b+1}|
  ≤ C_atom(W')·4^{b+c}` — from `moment_atom` + `beta_sum` (route: Crux 3).
Then `budget_moment_g` (both inequalities of the sandwich, Crux 2, using
W2-2's marked lemma; hypothesis `hD`). Verifier: beta identity at (c,b) =
(0,0),(1,2) by hand; the error is ABSOLUTE not `·log z`; g-sandwich is
two-sided. PORT-BLOCKER floor: none (B-tier assembly on landed atoms).

### W2-2 (P3.b) `Salt/Twelve/MarkedPrime.lean` — Sonnet-suitable
`marked_prime_phi : p prime, p ∤ W', Σ_{r<z, sqf, (r,W')=1, p∣r}
(log r)^a/φ(r) ≤ (1/(p−1))·c_up(W')·(log z)^{a+1}` (reindex `r = p·s`,
crude `(log r)^a ≤ (log z)^a`, landed lossy upper bounds suffice — any O(1)
constant); `marked_prime_g` (same, `1/(p−2)`). Optionally the tail-sum
corollary `Σ_{p>D, p prime} (1/(p−1))·(1/(p−2)-ish) ≤ 4/D` — check landed
`euler_tail_L`-adjacent forms first (may exist). PORT-BLOCKER floor: none.

### W2-3 (P3.e) `Salt/Twelve/BudgetPoly.lean` — Opus
The symbolic ℚ layer. Representation latitude (suggest
`BPoly n := List ((Fin n → ℕ) × ℕ × ℚ)`: t-exponents, budget exponent,
coeff). REQUIRED interface: `eval` (over ℝ, `t : Fin n → ℝ`, budget
`1 − Σt`); `ofPoly : Poly → BPoly 5` (C1's `Poly`, budget exp 0);
`contractAt m : Poly → BPoly 4` (the `∫dtₘ`: per monomial, divide by
`αₘ+1`, budget exponent `αₘ+1`, drop coord `m`); `mul/sq`;
`simplexInt : BPoly n → ℚ` per monomial `= (∏cᵢ!)·d!/(n+d+Σc)!`. TIES
(norm_num, the wave's deliverable): `simplexInt (sq (ofPoly Fstar))
= Ical Fstar` and `∀ m, simplexInt (sq (contractAt m Fstar)) = Jcal m Fstar`
(semantic identity — should be provable for general `F` by `Finset` algebra,
or per-`Fstar` by `norm_num`; either accepted, general preferred).
Verifier: `contractAt` semantics vs `JD` (the `(αₘ+1)(βₘ+1)`/budget `+2`
bookkeeping); `simplexInt` vs `DInt` at two instances. PORT-BLOCKER floor:
the general-`F` tie may be PB'd to the `Fstar`-instance ties.

### W2-4 (sweep) `(D, W')`-generalization — Opus, mechanical per C3 audit
Files/lemmas per the audit table (CongCount, CongSolvable, Compat's two,
S2Decomp defs+3, S2Eh defs+7, S1Bound's 4 dropping `hW : W' = W k`,
CollisionQuant's 7 `D₀`-lemmas, Tuple: parameterized `exists_nu0`/
`hSeq_le_D₀`-analogs at `W'' = primorial D`, `(H 5).sup < D`). **Fable
authorization (statement-tier): generalize IN PLACE** — widen `W k → (W' : ℕ)`
+ explicit hypotheses (squarefree, primorial-primes-`> D`, `hν₀`-shape),
PROVIDED the full `lake build` stays green with every downstream
Maynard/Brun theorem building unchanged (instantiation must be trivially
recoverable). Anything whose proof genuinely uses `W k`-specific facts:
flag in the report, do not force. Verifier: full build + spot 3 downstream
users unchanged + axiom audit on 3 generalized lemmas. PORT-BLOCKER floor:
per-lemma flags.

## Wave 3 (carded at next pre-flight; sketches binding)
`mv_I` (5-dim, weights `μ²/φ`, integrand `F★²`): drop pairwise coprimality
via marked primes (25 pairs × `O(1/D)`), then peel coordinates with
`budget_moment`, concluding at `X^5·simplexInt(F★²)·(1+E)`,
`|E| ≤ c(F,W')(1/log R + 1/D)`. `mv_J` (4+2-dim, outer `μ²/g` via sandwich,
inner two independent `budget_moment`s at fixed `W'` with Möbius
`aₘ ⊥ ∏u` marking): `X^6·Σ_m simplexInt((F★⁽ᵐ⁾)²)·(1+E)`. Bridge to
`Qdiag_m` via the (W',D)-generalized `lemma53` = wave-4 work with P4.

---

# Wave-3 cards (Fable pre-flight, 2026-07-10)

**STATUS — wave 3 LANDED on `explicit12` (2026-07-10), all axiom-clean
`[propext, Classical.choice, Quot.sound]`, every statement verbatim-frozen:**
- W3-0 ✅ `97bd32d` — `W3Prep`: `marked_sqf_phi`, `eval_mul/sq`, `log_natCap_slip`.
- W3-1 ✅ `d620dda` — `MvMoment`: `decBox` + `mv_monomial` (general-`n` workhorse;
  `DInt'_succ` telescope).
- W3-2 ✅ `3f2f098` — `BudgetMomentG`: `marked_sqf_g` + `budget_moment_g` +
  `box_g_pos` (drained the `budget_moment_g` FABLE-QUEUE item; `1/g(s)` prefactor
  exact via `gMult` multiplicativity).
- W3-3 ✅ `06d3643` — `MvMomentG`: `mv_monomial_g` (top-level g↔φ comparison,
  general `n`; reusable `product_gap_bound`).
- W3-4 ✅ `6091663` — `MvI`: **`mv_I`** (keystone I), general over `F`.
- W3-5 ✅ `f45a63f` — `MvJ` pt1: `yF` + `inner_contract`.
- W3-6 ✅ `570be28` — `MvJ` pt2: **`mv_J`** (keystone II), full 4-part assembly
  (`mv_J_main` + single/double sum-swaps), nothing hypothesized.
All wired into `Salt/Twelve/All.lean`. At `F★`, via the W2-3 ties, `mv_I` gives
`X⁵·Ical F★` and `mv_J` gives `X⁶·Jcal m F★` (`Σ_m Jcal m F★ = 191881/23950080`).
Design allowances used: three `set_option maxHeartbeats` (documented; resource
limits, not axioms); `mv_I` handled the coprimality-drop sign per-monomial
(equivalent to the `F²≥0` framing). Next: wave-4 Fable pre-flight (spine
bridges, `WindowPNT`/`EHall`, endgame).

Statements below are FROZEN (iron rule 1). Everything else — proof-internal
definitions, helper lemmas, exact constants inside `∃ c` — is executor
latitude. Throughout `X` abbreviates `(W'.totient : ℝ) / W' * Real.log R`
(spelled out in every frozen statement; `X` is NOT a Lean def — executors may
`set` it locally).

All frozen statements were ELABORATION-CHECKED verbatim (2026-07-10,
adversarial pass): they compile as written inside `namespace Salt.Twelve`
PROVIDED the file adds `open Salt.Maynard` (for `kSieveIndex`, `gMult`) —
every wave-3 module needs that open (or full qualification). The
constant/dimension chain, the g-side swap machinery, and the D=3 tail
constants were independently re-derived and numerically re-tested (J-side
miniature: main `X³/20` + `(1+X)²` error shape confirmed; all tail bounds
hold at the frozen minimum `D = 3` with ≥4× slack).

## Architecture revision (supersedes the sketch's 2-node plan)

Hand-deriving the peel revealed a better decomposition than "mv_I and mv_J
directly": a single general-`n` induction workhorse does all the peeling for
BOTH keystones.

1. **`mv_monomial`** (n-dim, φ-weights, decoupled box, cap `z ≤ R`): peel the
   FIRST coordinate at ℕ-cap `z' = (z−1)/r₀ + 1`, apply the induction
   hypothesis at `z'`, then `budget_moment` at `(c,b) = (e₀, n+d+Σ'e)`. The β
   coefficients telescope EXACTLY into the Dirichlet constant:
   `DInt'ₙ(e',d) · e₀!·M!/(e₀+M+1)! = DInt'ₙ₊₁(e,d)` with `M = n+d+Σ'e`
   (hand-verified; the `M!` cancels — `d!` is carried through unchanged). Base
   `n = 1` IS `budget_moment` (up to the `Fin 1` tuple iso). Errors propagate
   as absolute-times-`(1+X)`-powers: `≤ c·(1+X)^{n−1}`.
2. `mv_I` = pairwise-coprimality drop (marked, `O(1/D)`) + monomial expansion
   of `sq (ofPoly F)` + `mv_monomial` at `n = 5, z = R`. The pair count is
   `C(5,2) = 10` (the sketch's "25" was a loose cross-keystone count).
3. `mv_J` = per-`r` inner contraction (`inner_contract`, 1-dim peel +
   marked `u ⊥ ∏r` correction with an r-DEPENDENT error budget), squared,
   then the 4-dim g-weighted outer sum via `mv_monomial_g`.
4. All g-weighted control routes through the powerset-swap: per-term
   `1/g ≤ C/φ` is FALSE (W2-2's finding), but
   `1/g(r) = (1/φ(r))·Σ_{u∣r} h(u)` with `h(u) = ∏_{p∣u} 1/(p−2)` (exact for
   squarefree `r`), and after swapping the `u`-sum out, `marked_sqf_phi` at
   `lcm(s,u)` + the `(p−1)(p−2)`-tail give uniform bounds. The `1/g(s)`
   prefactor in `marked_sqf_g` is EXACT:
   `(1/φ(s))·∏_{p∣s}(p−1)/(p−2) = 1/g(s)`.

**Numeric verification (2026-07-10, `mv_smoke.py` + scaling fit):** k=2 model
of `mv_monomial`/`mv_I` at `W' = 210`, `R = 10⁴…10⁶`: the residual
`S − X²·∫F²` fits `0.382·X + 0.603` across all five R values to 4 decimals —
error is exactly `O((1+X)^{n−1})`, main-term constant and X-power confirmed.
Pairwise-coprimality drop measured 0.5% (`≤ O(1/D)` predicted). Convergence to
the asymptote is `1/X`-slow — inherent; the rung's endgame is an `∀ᶠ`
statement, so no explicit `N₀` is chased.

## Frozen definitions

```lean
/-- The DECOUPLED box: like `kSieveIndex` but WITHOUT pairwise coprimality,
and with cap `z` decoupled from the weight normalization `R`. Proof-internal
to wave 3 but frozen because it appears in `mv_monomial`'s statement. -/
def decBox (n z W' : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range z).filter
    (fun r => (∀ i, Squarefree (r i)) ∧ (∀ i, (r i).Coprime W') ∧ ∏ i, r i < z)

/-- The explicit12 sieve weight: `F` evaluated at `t(s)`, supported on the
sieve box. Matches the `y`-slot of the spine's `lemma53_tight` contraction. -/
noncomputable def yF (R W' : ℕ) (F : Poly) (s : Fin 5 → ℕ) : ℝ :=
  if s ∈ kSieveIndex 5 R W'
  then eval (ofPoly F) (fun i => Real.log (s i) / Real.log R) else 0
```

## Card W3-0 (prep) `Salt/Twelve/W3Prep.lean` — Sonnet, class B

Four independent leaves; everything downstream imports this file.

```lean
theorem marked_sqf_phi (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W') (a : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ s z : ℕ, 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter
          (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
          (Real.log r) ^ a / (Nat.totient r : ℝ))
        ≤ (1 / (Nat.totient s : ℝ)) * c * (Real.log z) ^ (a + 1)

theorem eval_mul {n : ℕ} (p q : BPoly n) (t : Fin n → ℝ) :
    eval (mul p q) t = eval p t * eval q t

theorem eval_sq {n : ℕ} (p : BPoly n) (t : Fin n → ℝ) :
    eval (sq p) t = eval p t ^ 2
```
plus a floor-slip helper (exact form = executor latitude, the NEED is frozen):
for `1 ≤ r < z`, `|Real.log ((z−1)/r + 1 : ℕ) − (Real.log z − Real.log r)|
≤ Real.log 2` (ℕ-division cap vs real budget).

Route for `marked_sqf_phi`: the landed `marked_prime_phi` route verbatim with
composite squarefree `s` — `r` squarefree ∧ `s ∣ r` ⇒ `Coprime s (r/s)` (else
`p² ∣ r`), so `φ(r) = φ(s)·φ(r/s)` (`Nat.Coprime.totient_mul`), inject
`r ↦ r/s` into the unmarked sum, finish with `phiAtom_upper_lossy`.
**`c` is quantified BEFORE `s`** — uniformity in `s` is load-bearing (the
g-side tail sums over `s`). No `PhiUpperAtom` hypothesis (the lossy upper
suffices, as in W2-2). Note `s` need not be assumed squarefree/coprime: when
it isn't, the LHS sum is empty and the bound is trivial. `eval_mul`: List
`flatMap`/`map` sum algebra + `(1−Σt)^{d₁+d₂} = (…)^{d₁}·(…)^{d₂}` +
`pow_add`; `eval_sq := eval_mul p p`. Verifier: `marked_sqf_phi` at `s = p`
prime must recover `marked_prime_phi`'s strength; `c` outside `∀ s`; empty-`s`
edge (`s = 0` excluded by `0 < s`; `s` with a small prime factor → empty sum).
PB floor: none (B-tier on landed atoms).

## Card W3-1 (workhorse) `Salt/Twelve/MvMoment.lean` — Opus, class C

`decBox` (frozen above) and THE keystone:

```lean
theorem mv_monomial (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (n : ℕ) (e : Fin n → ℕ) (d : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ z R : ℕ, 2 ≤ z → z ≤ R → 1 ≤ Real.log R →
      |(∑ r ∈ decBox n z W',
            (∏ i, (Real.log (r i) / Real.log R) ^ e i)
              * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
              / ∏ i, (Nat.totient (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ n
            * ((DInt' e d : ℚ) : ℝ)
            * (Real.log z / Real.log R) ^ (n + d + ∑ i, e i)|
      ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (n - 1)
```

Route: induction on `n` (generalizing `e`, `d`, and — crucially — `z`; the
constant `c` is per-`(n,e,d)`, obtained BEFORE `z`, `R`).
- Base `n = 1`: `decBox 1 z` ≅ `budget_moment`'s filtered range (single-coord
  tuple iso via `Fin.cons`/`piFinset` singleton); `DInt' e d` at `n = 1` is
  `e₀!·d!/(1+d+e₀)!` — exactly `budget_moment`'s β. (`n = 0` is trivially
  `0 ≤ c`: the empty tuple gives LHS = main.)
- Step: split `r = Fin.cons r₀ r'` (`Finset.sum` over `piFinset` splits as
  `sum_comm`/`sum_sigma`); for fixed `r₀` the inner tuple ranges over
  `decBox n z' W'` with ℕ-cap `z' = (z−1)/r₀ + 1` (check: `r₀·P < z ↔ P < z'`
  for `r₀ ≥ 1`); `2 ≤ z'` holds since `r₀ ≤ z−1`. Apply IH at `z'`; convert
  `log z'` to `log z − log r₀` by the floor-slip helper (each slip is an
  additive `O(1)` in a `[0,1]`-power, contributing absolute error
  `≤ c·(1+X)^{n−1}` after the `r₀`-sum). Then `budget_moment` at
  `(c,b) = (e₀, n+d+Σᵢ'eᵢ)` for the `r₀`-sum. Telescope check the executor
  must reproduce: with `M = n+d+Σ'e`,
  `DInt'ₙ(e',d)·(e₀!·M!/(e₀+M+1)!) = DInt'ₙ₊₁(e,d)` — concretely
  `(∏'eᵢ!·d!/M!)·(e₀!·M!/(e₀+M+1)!) = ∏eᵢ!·d!/(n+1+d+Σe)!` (only `M!`
  cancels; `d!` is preserved end-to-end).
- Error bookkeeping: prior-level error × (a=0 moment of the new coordinate
  `≤ c(1+X)`) + new absolute (`Catom·4^…` + slip terms) × `(1+X)^{n−1}`.

Traps: (i) `z'`-threshold — IH needs `2 ≤ z'`, true only for `r₀ ≤ z−1`,
which `Finset.range z` + squarefree (`r₀ ≥ 1`) gives; do NOT let `r₀ = 0`
terms in (squarefree filter kills them). (ii) The budget numerator after
peeling is `log z − log r₀ − Σ' log rᵢ'` — the IH's `z'`-budget
`log z' − Σ'` differs by the slip; bound `|(A+δ)^d − A^d| ≤ d·|δ|·(1+|δ|)^{d−1}`
with `A ∈ [0,1]`. (iii) All weights are ≥ 0 on the box (needed for crude
upper bounds): `r < z ⇒ log r ≤ log z`... the BUDGET numerator uses
`∏ r < z`, NOT per-coordinate. (iv) `budget_moment`'s `∀ z` quantifier is
consumed at the DYNAMIC `z'` — this is why its constants-before-`z` shape
matters; do not re-obtain constants per `r₀`. Verifier: `n = 1` reduction to
`budget_moment` literally; the telescope identity at `(n,e,d) = (1,(2,·),3)`
by hand; error shape has NO `log z` factor. PB floor: if the `piFinset`
split fights, land `n = 5` concretely (5 hand-peels) — acceptable but flag.

## Card W3-2 (g-engine) `Salt/Twelve/BudgetMomentG.lean` — Opus, class C

Drains FABLE-QUEUE item 1. Both lemmas are powerset-swap machinery.

```lean
theorem marked_sqf_g (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W') (a : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D s z : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter
          (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
          (Real.log r) ^ a / (gMult r : ℝ))
        ≤ (1 / (gMult s : ℝ)) * c * (Real.log z) ^ (a + 1)

theorem budget_moment_g (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (c b : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ D z R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      2 ≤ z → z ≤ R → 1 ≤ Real.log R →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
          (Real.log r / Real.log R) ^ c
            * ((Real.log z - Real.log r) / Real.log R) ^ b
            / (Nat.totient r : ℝ))
        ≤ (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
            (Real.log r / Real.log R) ^ c
              * ((Real.log z - Real.log r) / Real.log R) ^ b
              / (gMult r : ℝ)) ∧
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
          (Real.log r / Real.log R) ^ c
            * ((Real.log z - Real.log r) / Real.log R) ^ b
            / (gMult r : ℝ))
        ≤ (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
            (Real.log r / Real.log R) ^ c
              * ((Real.log z - Real.log r) / Real.log R) ^ b
              / (Nat.totient r : ℝ))
          + Cg / D * Real.log R
```

Route (hand-verified, incl. numerically): for squarefree `r` with all prime
factors `> D ≥ 3`: `1/g(r) = (1/φ(r))·∏_{p∣r}(1 + 1/(p−2))
= (1/φ(r))·Σ_{u ∣ r} h(u)`, `h(u) = ∏_{p∣u} 1/(p−2)` (finite divisor sum —
NO tsum). Swap `Σ_r Σ_{u∣r} → Σ_u Σ_{r: u∣r}` (`Finset.sum_sigma`-style over
pairs, `u` ranges over `Finset.range z` filtered squarefree). Then:
- `marked_sqf_g`: the marked sum at `s` becomes
  `Σ_u h(u)·[marked_sqf_phi at lcm(s,u)]`; use
  `φ(lcm(s,u)) = φ(s)·∏_{p∣u, p∤s}(p−1)` and split `u = u₁·u₂`
  (`u₁ ∣ s`, `u₂ ⊥ s`): the `u₁`-factor resummed is EXACTLY
  `∏_{p∣s}(1+1/(p−2)) = φ(s)/g(s)`, the `u₂`-factor is
  `≤ ∏_{D<p<z}(1 + 1/((p−1)(p−2))) ≤ exp(2/D) ≤ 2`. Net prefactor
  `(1/φ(s))·(φ(s)/g(s))·2·c = (2c)/g(s)`. **This is the exactness the whole
  g-side rests on — verify the `u₁`-resummation identity by hand.**
- `budget_moment_g` lower: termwise, `g(r) ≤ φ(r)` (each `p−2 ≤ p−1`) and
  `gMult r > 0` on the box (all `p > D ≥ 3`), weights ≥ 0.
  Upper: difference `= Σ_{u≠1} h(u)·(u-marked φ-sum with weights ≤ 1)`
  `≤ Σ_{u≠1} h(u)·(1/φ(u))·c·log z ≤ (exp(2/D) − 1)·c·log R ≤ (4/D)·c·log R`
  (using `e^x − 1 ≤ 2x` on `x = 2/D ≤ 2/3`). Numerics (2026-07-10):
  `Σ_{p>D} 1/((p−1)(p−2))` = 0.037 at D=10 vs 2/D = 0.2 — slack ×5.

Traps: (i) `gMult 0 = 1` (empty product over `primeFactors 0 = ∅`) — the
`Squarefree r` filter kills `r = 0`, but NEVER bound `1/gMult` without being
inside the filter. (ii) The per-term transfer `1/g ≤ C/φ` is FALSE — any
route that bounds `∏(1+1/(p−2))` pointwise by a constant is wrong
(`ω(r)` is unbounded); only the post-swap `(p−1)(p−2)` tail converges.
(iii) `h` is multiplicative on coprime divisors of a squarefree number —
build the divisor-sum identity via `Nat.sum_divisors`/`Finset.prod_add`-style
expansion (`∏(1+xₚ) = Σ_{S⊆primes} ∏xₚ`), finite products only — no
`ArithmeticFunction`/tsum. (iv) EVEN-`s` KNIFE EDGE (adversarial pass):
`gMult s = 0` exactly when `2 ∣ s`, so for even `s` the frozen RHS of
`marked_sqf_g` is `0` — the statement stays true because `hD` + `3 ≤ D`
force `2 ∣ W'` (contrapositive: `¬2∣W' → D < 2`), so `2 ∣ s ⇒` the LHS
filter is empty. Open the proof with the explicit early case
"if ¬(Squarefree s ∧ s.Coprime W' ∧ ∀ p ∣ s, prime → D < p) then LHS = 0
≤ RHS". (v) Land a reusable helper `box_g_pos : Squarefree r → r.Coprime W'
→ (3 ≤ D) → hD → 0 < gMult r` (pivot: `2 ∣ W'` ⇒ `2 ∤ r`) — it is the
load-bearing fact for the sandwich's LOWER half (a `g(r) = 0` term would
flip that inequality under Lean's `x/0 = 0`) and is reused by W3-3/W3-6.
Verifier: the `u₁`-resummation (`φ(s)/g(s)` exactness); `Cg` uniform in
`D, z, R`; lower bound needs NO `hUpper`. PB floor: none — this is the
designed drain of the queue item; if the swap machinery fights, flag rather
than weaken the `1/g(s)` prefactor.

## Card W3-3 (g-workhorse) `Salt/Twelve/MvMomentG.lean` — Opus, class C

```lean
theorem mv_monomial_g (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (n : ℕ) (e : Fin n → ℕ) (d : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D z R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      2 ≤ z → z ≤ R → 1 ≤ Real.log R →
      |(∑ r ∈ decBox n z W',
            (∏ i, (Real.log (r i) / Real.log R) ^ e i)
              * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
              / ∏ i, (gMult (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ n
            * ((DInt' e d : ℚ) : ℝ)
            * (Real.log z / Real.log R) ^ (n + d + ∑ i, e i)|
      ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (n - 1)
          * (1 + Real.log R / D)
```

Same induction as `mv_monomial` (mirror the file), with each peel's
`budget_moment` application replaced by `budget_moment` + the
`budget_moment_g` sandwich: the g-peel's main term is the φ-peel's main term
plus an absolute `O(Cg·log R/D)`, which propagates through remaining levels
exactly like the other absolute errors (× `(1+X)`-powers — note the g-side
crude a=0 bound needs `marked_sqf_g` at `s = 1`). MAIN TERM IS THE φ-MAIN
TERM — the `∏(1+1/(p(p−2)))` singular-series deviation lives in the error
(that's what the `log R/D` factor is for). Traps: same as W3-1 plus:
the crude per-coordinate upper moments must ALSO use g-weights (via
`marked_sqf_g` `s = 1`), not a pointwise `1/g ≤ 1/φ`-style lie (the
inequality goes the WRONG way). Verifier: main term literally identical to
`mv_monomial`'s; the `log R/D` factor present. Numeric caveat (adversarial
pass): at FIXED `W'` the g/φ ratio converges to the singular constant
`∏_{p∤W'}(1+1/(p(p−2))) ≈ 1.038` at `W' = 210` — NOT to 1; that offset IS
the `log R/D` error term doing its job, not a bug. PB floor: `n = 4`
concrete (mv_J's only consumption) — acceptable, flag.

## Card W3-4 (keystone I) `Salt/Twelve/MvI.lean` — Opus, class C

```lean
theorem mv_I (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (F : Poly) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → 1 ≤ Real.log R →
      |(∑ r ∈ kSieveIndex 5 R W',
            eval (ofPoly F) (fun i => Real.log (r i) / Real.log R) ^ 2
              / ∏ i, (Nat.totient (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ 5
            * ((simplexInt (sq (ofPoly F)) : ℚ) : ℝ)|
      ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 5
          * (1 / Real.log R + 1 / D)
```

Route: (1) `eval_sq` + `sq (ofPoly F)` is a `BPoly 5` with ALL budget
exponents 0 (`ofPoly` sets 0, `mul` adds) — so the integrand is a plain
`List`-sum of t-monomials; exchange `Finset.sum`/`List.sum`. (2) Enlarge
`kSieveIndex 5 R W' ⊆ decBox 5 R W'` (same `range R`, same `∏ < R`, pairwise
coprimality dropped): the DIFFERENCE is a sum over tuples where some pair
`(i,j)` shares a prime `p` (necessarily `p ∤ W'`, so `p > D`); bound each
monomial's contribution on the difference set by: weights `≤ 1` termwise
(`t ∈ [0,1]` on the box), unmark 3 coordinates (a=0 moment,
`≤ c(1+X)` each), mark coordinates `i,j` at `p` (`marked_sqf_phi` at
`s = p`, a = 0: `≤ c·log R/(p−1)` each), sum `Σ_{p>D} 1/(p−1)² ≤ 2/D`, times
10 pairs. NOTE the difference-set sum is SIGNED-FREE: `F(t)² ≥ 0`, so
`0 ≤ Σ_dec − Σ_ksieve ≤ (marked bound)` — no absolute values needed on the
drop. (3) `mv_monomial` at `n = 5`, `z = R` per monomial (the budget factor
at `z = R` with `d = 0` is `1`; `(log R/log R)^{5+Σe} = 1` — no boundary
slip at `z = R`), then `simplexInt (sq (ofPoly F)) = Σ q·DInt' α 0` is
literally the definition. Traps: (i) the monomial-level constants `c(α)`
are per-monomial — collect the finite max/sum over the `sq`-list (3136
entries for F★ — do NOT unfold the list; work with `List.sum` abstractly).
(ii) `(1+X)⁴ ≤ (1+X)⁵/Real.log R · (W'/φW')`-style absorptions need
`X ≥ φW'/W'` (from `1 ≤ log R`) — keep the `(1+X)⁵` frozen error form, it
absorbs both `mv_monomial`'s `(1+X)⁴` (via `/log R`) and the drop (via
`/D`). Verifier: `t ∈ [0,1]` and budget ≥ 0 on the box; the drop's sign
argument; consistency `simplexInt (sq (ofPoly Fstar)) = Ical Fstar` (landed
tie) — so `mv_I` at `F★` concludes `X⁵·(1597/399168)·(1+E)`. PB floor: none.

## Card W3-5 (inner contraction) `Salt/Twelve/MvJ.lean` — Opus, class C

`yF` (frozen above) and:

```lean
theorem inner_contract (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (F : Poly) (m : Fin 5) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → 1 ≤ Real.log R →
      ∀ r ∈ kSieveIndex 5 R W', r m = 1 →
      |(∑ u ∈ Finset.range R,
            yF R W' F (Function.update r m u) / (Nat.totient u : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R)
            * eval (contractAt m F)
                (fun i => Real.log (r (m.succAbove i)) / Real.log R)|
      ≤ c * (1 + ((W'.totient : ℝ) / W' * Real.log R)
              * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)))
```

Route: unfold `yF`; `Function.update r m u ∈ kSieveIndex 5 R W'` iff `u` is
squarefree, `u ⊥ W'`, `u ⊥ rᵢ (i ≠ m)`, and `u·∏_{i≠m} rᵢ < R` (use
`r ∈ kSieveIndex`, `r m = 1`; note `∏ᵢ rᵢ = ∏_{i≠m} rᵢ`). So the inner sum
is a 1-dim budget-moment at ℕ-cap `z_r = (R−1)/∏ᵢrᵢ + 1` with the EXTRA
constraint `u ⊥ ∏r`: (a) drop it — the dropped terms are marked sums,
`Σ_{p ∣ ∏r} marked_sqf_phi(s=p)` — this is the r-dependent error budget in
the frozen bound (do NOT try to bound it r-uniformly; the caller swaps it);
(b) the unconstrained sum: expand `eval (ofPoly F)(update-t)` per monomial
`(α, q)`: the `tₘ`-power is `(log u/log R)^{α m}`, the others are constants
in `u`; apply `budget_moment` at `(c,b) = (α m, 0)` and cap `z_r`; the main
term reassembles as `X · eval (contractAt m F) t'` — `contractAt`'s
`q/(αₘ+1)` coefficient and `(1−Σ't)^{αₘ+1}` budget exponent are EXACTLY the
peel's `β = αₘ!·0!/(αₘ+1)! = 1/(αₘ+1)` and `(log z_r/log R)^{αₘ+1}` up to
the floor slip `log z_r = log R − log ∏r + O(log 2)` (slip → absolute `O(1)`
error via the `[0,1]`-power Lipschitz bound; `Fin.removeNth m t = t ∘
m.succAbove` aligns the coordinates). Traps: (i) `u = 1` IS in the sum
(`t_m = 0` term, legit); `u = 0` killed by squarefree-in-box. (ii) the
`(1−Σ't)` in `eval (contractAt m F)` uses the FOUR remaining coordinates —
`Σ_{i : Fin 4} log (r (m.succAbove i))/log R = log ∏ᵢrᵢ / log R` since
`r m = 1`. (iii) `eval` bounded on the box: `t' ∈ [0,1]⁴`, `1−Σ't' ∈ [0,1]`
— needed for the caller's square-expansion; state it as a companion lemma
`inner_main_bound : |eval (contractAt m F) t'| ≤ (constant from F)` if
useful (executor latitude). Verifier: the error's r-dependence is EXACTLY
`Σ_{p ∣ ∏r} 1/(p−1)` (one marked power, not two); `contractAt` coefficient
vs the β of `budget_moment` at `b = 0`. PB floor: none.

## Card W3-6 (keystone J) — append to `Salt/Twelve/MvJ.lean` — Opus, class C+

```lean
theorem mv_J (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (F : Poly) (m : Fin 5) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → 1 ≤ Real.log R →
      |(∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
            (∑ u ∈ Finset.range R,
                yF R W' F (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
              / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ 6
            * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
      ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 6
          * (1 / Real.log R + 1 / D)
```

Route (the assembly; consumes W3-1g/2/3/5): (1) substitute
`inner = X·eval(contractAt m F)(t') + err_r` (W3-5) and expand the square:
`inner² = X²·eval(…)² + 2X·eval(…)·err_r + err_r²`, with
`|eval(…)| ≤ c_F` on the box. (2) The MAIN part
`Σ_r X²·eval(sq (contractAt m F))(t')/∏g` (via `eval_sq`): the outer tuples
`(r_i)_{i≠m}` under `r ∈ kSieveIndex, r_m = 1` form the 4-dim
pairwise-coprime box; drop pairwise coprimality (6 pairs; g-weighted marked
bounds via `marked_sqf_g` at `s = p`, tail `Σ 1/((p−2)·(p−2))`-shaped
`≤ c/D`... note BOTH markings are now `1/(p−2)`) to land in `decBox 4 R W'`
(reindex `Fin 5`-tuples-with-`r m = 1` ↔ `Fin 4`-tuples via
`m.succAbove`/`Fin.insertNth m 1` — `∏_{i≠m} rᵢ = ∏ (4-tuple)`, budget
matches); apply `mv_monomial_g` at `n = 4, z = R` per monomial of
`sq (contractAt m F)` (budget exponents are NONZERO here — `d` up to
`2(deg_m F + 1)` — this is why `mv_monomial_g` carries general `d`);
reassemble `X²·X⁴·simplexInt (sq (contractAt m F))`. (3) The CROSS part:
`Σ_r 2X·c_F·err_r/∏g ≤ 2X·c_F·Σ_r [c(1 + X·Σ_{p∣∏r}1/(p−1))]/∏g`; the
`Σ_p`-part SWAPS: `Σ_r (Σ_{p∣∏r}1/(p−1))/∏g(rᵢ) = Σ_{p>D} (1/(p−1))·
Σ_{r: p∣∏r} 1/∏g ≤ Σ_{p>D} (1/(p−1))·4·(1/(p−2))·(g-moment)³ᵘᵐ…` — four
choices of the marked coordinate, `marked_sqf_g(s=p)` on it, crude g-moments
(`marked_sqf_g` `s=1`) on the rest: net `≤ c·(1+X)³·Σ_{p>D}1/((p−1)(p−2))
≤ c·(1+X)³·(2/D)`; total cross ≤ `c·X·(1+X)⁴/D`-shaped — inside the frozen
budget. (4) `err_r²` similarly with TWO swapped primes (or crudely one prime
+ `Σ_{p∣∏r}1/(p−1) ≤ 1` for `D ≥ 3`... careful: that sum is NOT ≤ 1
uniformly — use the double swap). (5) Collect into the frozen
`(1+X)⁶(1/log R + 1/D)`.

Traps: (i) the outer box after `r m = 1`-restriction: `kSieveIndex`
membership of the 5-tuple ⇔ the 4-tuple's `decBox`-style membership PLUS
pairwise coprimality — write the `Fin.insertNth`-bijection lemma FIRST and
test it on a `#eval`-free example. (ii) `∏ i ∈ univ.erase m, gMult (r i)`
vs `∏ i : Fin 4, gMult (4-tuple i)` — same product via the bijection
(`gMult (r m) = gMult 1 = 1` if you prefer full products). (iii) The cross
term's sign: `err_r` is NOT signed — use `|inner² − X²eval²| ≤
2X|eval||err| + err²`. (iv) Never bound `Σ_{p∣∏r} 1/(p−1)` uniformly in `r`
(it grows like `ω(∏r)/D` — the swap is mandatory). Verifier: the X-power
(2 inner + 4 outer = 6); `simplexInt (sq (contractAt m Fstar)) = Jcal m
Fstar` (landed tie) — so `mv_J` at `F★` concludes `X⁶·(Jcal m F★)·(1+E)`,
`Σ_m Jcal m F★ = 191881/23950080`; the swap in steps (3)/(4). PB floor:
if the full assembly exceeds budget, land the main part (2) as
`mv_J_main` with hypotheses packaging (3)/(4)'s bounds, and flag — but the
swap lemmas themselves must NOT be hypothesized away.

## Dependency DAG and dispatch plan

```
W3-0 (Sonnet) ──┬─→ W3-1 (Opus) ──┬─→ W3-4 mv_I (Opus)
                │                  └─→ W3-3 (Opus) ─→ W3-6 mv_J (Opus)
                ├─→ W3-2 (Opus) ───→ W3-3
                └─→ W3-5 (Opus) ───→ W3-6
```

Round 1: W3-0 alone (small, everything imports it). Round 2: W3-1, W3-2,
W3-5 in parallel. Round 3: W3-3, W3-4 in parallel. Round 4: W3-6.
Verify+commit each node before dependents dispatch (import race discipline,
as wave 2). Wire new files into `Salt/Twelve/All.lean` at reconciliation.
Escalation tripwires per MODEL_POLICY (3 serious attempts → FABLE-QUEUE).

After wave 3, the remaining explicit12 work (wave 4, needs the next Fable
pre-flight): the `Qdiag_m`/`S1` bridges via the `(D,W')`-generalized spine
(`lemma53` at free `W'`, `S1_upperW`/`S2mW_lower` consumption), the window
PNT/EH plumbing (`WindowPNT`/`EHall` → the prime-side counts), and the
endgame assembly `gaps_le_twelve`.

---

# Wave-4 cards (Fable pre-flight, 2026-07-10)

**STATUS — wave 4 COMPLETE on `explicit12` (2026-07-10), all axiom-clean
`[propext, Classical.choice, Quot.sound]`:**
- W4-0 ✅ `085f496` — `PhiUpperReindex`: `phiUpperAtom_final : ∀ B≠0,
  PhiUpperAtom B` UNCONDITIONAL (closed the `hReindex` residual).
- W4-1 ✅ `a6dd715` — `RelEngines`: `marked_sqf_phi_rel`/`marked_sqf_g_rel`/
  `g_gap_rel` (constant-free, vs `phiAtomSum`).
- W4-2 ✅ `6086f68`+`ba5c526` — `MvSplit`: `inner_contract_rel`, `mv_I_split`,
  `mv_J_split` (split errors; `1/D` relativized, `∃A` before `W'`).
- W4-3 ✅ `380b9e7` — `Lemma53W`: `euler_tail_LW` + `lemma53_tightW` (free
  `(W',D)`, `|y|≤B`).
- W4-4 ✅ `02be093` — `FstarNorm`: `Fstar1` (`|yF|≤1`), `M5_cert1`,
  `primorial_hDlt`.
- W4-5 ✅ `abf457c` — `QdiagBridge`: `qdiag_bridge` (the S2 bridge).
All wired into `Salt/Twelve/All.lean`. TWO Opus-inline design corrections
(both endgame-verified, `κ⁻¹≤5√D`): the `mv_J_split`/`qdiag_bridge` `1/D`
buckets became MIXED-power `(1+X+PAS)⁶` (`db82524`), and `qdiag_bridge` gained
a second `κ⁻²·Y⁶/D²` term for the `δ²` self-term (`c9db92b`). Both were
pre-flight bucket under-specs the execution caught. FABLE-QUEUE now holds only
`marked_prime_g` (dead-end record). Next: wave-5 pre-flight (S1 non-tensor
collision, sharp S1, WindowPNT/EHall plumbing, `gaps_le_twelve`).

Statements below are FROZEN (iron rule 1); routes/traps are executor guidance.
`X` abbreviates `(W'.totient : ℝ)/W' * Real.log R`; `PAS z W'` abbreviates
`Salt.Maynard.phiAtomSum z W'` (a landed def, NOT new notation in Lean).

## Pre-flight findings (three interface maps + endgame analysis; binding)

1. **The ∃-opacity trap and its resolution (THE structural decision).** The
   wave-3 keystones quantify `∃c` AFTER `W'`. At the endgame `W' = primorial D`
   is LINKED to `D`, so the residual error `c(W')/D` is an opaque real that can
   never be beaten against the certified slack `δ★ = M₅ − 2 = 241/95820`.
   Uniformizing `c` over `W'` is NOT viable via absolute atom constants: the
   landed `phiAtom_upper_lossy` constant is `4(φ(B)+1)` (grows like `B`), the
   true `copHarmonic` constant analysis needs Mertens-type facts we do not
   have. **Resolution — relativize:** all `1/D`-side errors are re-stated
   against the CONCRETE quantity `PAS R W'` (no constants at all): e.g. the
   marked bound `≤ (1/φ(s))·(log z)^a·PAS z W'` is EXACT by the landed reindex
   proof. `1/D`-side coefficients become ABSOLUTE (pair counts, `2/D` tails,
   `Qabs`-powers), quantified `∃A` BEFORE `W'`. At the endgame, at fixed
   `(W', D★)`: `PAS R W'/X → 1` inside the `∀ᶠ` (per-`W'` atom bounds, opacity
   harmless there), and `∃D★ > A·M₅/δ★` is pure Archimedes on a single real.
   The `1/log R`-side keeps per-`W'` opaque constants (they die in `∀ᶠ` at
   fixed `W'`).
2. **`hReindex` is CRITICAL-PATH now**: `gaps_le_twelve (WindowPNT) (EHall)`
   cannot carry `PhiUpperAtom` — the per-`B` discharge (W4-0) is required at
   the instantiated `W' = primorial D★`.
3. **θ arithmetic (verified, `norm_num`-ready):** the pigeonhole needs
   `(θ/2)·M₅ > 1`. At `θ★ = 1999/2000`: `191881·1999·1000 > 95820·2000²`
   equivalently `(1999/4000)·M₅ = 1.000757 > 1`, margin `7.6×10⁻⁴`. (`θ=99/100`
   FAILS — the rung genuinely needs level `> 2/M₅ ≈ 0.99875`.) EH is consumed
   at level `θ₊ = 3999/4000 > θ★` so `W'·R² ≤ N^{θ₊}` holds eventually at
   `R = ⌊N^{θ★/2}⌋` with `W'` fixed.
4. **`D₀ 5 = 125 < 300 = 12·5²`**: every `D₀ k`-pinned lemma is VACUOUS at
   k=5. All bridges must run on the free-`D` `*W` spine with `12k² ≤ D`
   (i.e. `D ≥ 300`; the endgame's Archimedean `D★` also obeys this).
5. **The tensor obstruction is S1-only.** `S1_upperW` (landed, free `(W',D)`)
   has the diagonalized main `2·((K₀−1)N/W')·Σ_r y²/∏φ` whose inner sum IS
   `mv_I`'s LHS — but its collision step (`compat_le_two_ysideW` /
   `collision_lower_orderW`) requires tensor `y = ⟦𝒟⟧·∏f₀` with `f₀`
   divisor-MONOTONE. `yF`'s monomials are tensors but INCREASING — the
   monotone hypothesis fails. **The general-`y` (or per-monomial-bilinear)
   collision bound is the single open analytic design item — wave-5
   pre-flight work (Fable must read `collision_lower_orderW`'s proof), NOT
   carded here.** Also the crude factor 2 must go (sharp assembly, wave 5).
6. **The S2 side aligns exactly.** `s2_diag_lam_restricted` (already free-`W`)
   gives `Qdiag_mW k R W' m y = Σ_{u: uₘ=1} (∏ᵢ g(uᵢ))·V(u)²` with
   `V = lamPhiContractM`; `∏g·V² = yM²/∏_{i≠m}g` (`μ²=1`); `lemma53W` (W4-3)
   bridges `yM ↔ Inn := Σ_u y(update)/φ(u)` pointwise with the EXPLICIT
   W'-free constant `B·lemma53Const·k·log R/D`; `mv_J` evaluates `Σ Inn²/∏g`.
   The `|V|`-bound needed for `|yM² − Inn²|` falls out of the landed
   `inner_contract` + `lemma53W` — no tensor `VAbs` needed.
7. **Normalization:** `S1`, `S2m`, `Qdiag`, `mv_I`, `mv_J` are all degree-2
   homogeneous in `y`, so the pigeonhole is scale-invariant. Freeze
   `Fstar1 := Fstar` with every coefficient divided by
   `Qabs := Σ|coeffs Fstar|` (exact ℚ scaling): then `|yF R W' Fstar1| ≤ 1`
   on the box, ALL landed `|y| ≤ 1` machinery applies verbatim, and
   `M5_cert` transports (both sides scale by `Qabs⁻²`).
8. **Consumption anchors (from the endgame map):** the pigeonhole spine
   (`sum_S2m_eq`, `exists_window_two_primes`, `bounded_gap_of_S2_gt_S1`,
   `bounded_gaps_reduces`, `S1_lt_sum_S2m`) is k/y-generic but `W k`-pinned —
   wave 5 re-issues it at `W'` (mechanical sum-swaps) with the diam-12 variant
   via `hSeq_diam_le_twelve`. `S2mW_lower` (landed, free `W'`) needs its
   `herr` assembled from `s2PrimeCountW_approx'` + EH at `θ₊` (wave 5).
   `deltaPi_lower_of` takes the abstract prime supply — feed `WindowPNT`
   (`63−ε`, replacing Chebyshev's `c=1`). `eventually_poly_beats_polylog` is
   θ-agnostic and reused. `S1_upperW`'s error exponent is `(4k+2)` (not
   `2k+2`).

## Card W4-0 `Salt/Twelve/PhiUpperReindex.lean` — Opus, class C
**Discharge `hReindex`** (new file; do NOT edit the landed `PhiUpper.lean`):
```lean
theorem reindex_tail_le (B : ℕ) (hB : B ≠ 0) : ∀ x : ℕ, 2 ≤ x →
    (∑ r ∈ Salt.Maynard.sqfCop x B, radFiberTail r x B)
      ≤ ∑' v : ℕ, powerfulWeight v

theorem phiUpperAtom_final (B : ℕ) (hB : B ≠ 0) : Salt.Twelve.PhiUpperAtom B
```
(`phiUpperAtom_final := phiUpperAtom_holds B hB (reindex_tail_le B hB)`.)
Route (designed; ~430 lines of `tsum` bookkeeping, all in ℝ with
nonneg/summable — no ENNReal): (i) `radFiberTail r x B` = the tsum of the
fiber `{n | rad n = r, n ≠ 0, x ≤ n}` of `n⁻¹` (from `radFiber_inv_hasSum`
minus the finite head via `HasSum.sub`; note `n ⊥ B` is AUTOMATIC on the
fiber since `rad n = r ⊥ B`). (ii) Sum over `r ∈ sqfCop x B` = tsum over the
disjoint union `{n | rad n < x ≤ n, sqf-rad, ⊥B}` (finite sum of tsums,
nonneg). (iii) Reindex by `n ↦ (powPart n, sqfPart n)` where
`sqfPart n = ∏_{e_p = 1} p`, `powPart n = ∏_{e_p ≥ 2} p^{e_p}` (via
`Nat.factorization`; facts: `n = sqfPart·powPart`, coprime, `sqfPart`
squarefree, `powPart` powerful (`IsPowerful`), `rad n = sqfPart·rad powPart`).
The map is INJECTIVE on the union (`n` recovers as the product). (iv) Group
by `v = powPart n`: the fiber over `v` has `u = sqfPart n` ranging in the
window `x/v ≤ u·(rad v stuff)`: precisely `u·v ≥ x` and `u·rad v·... < x`
— derive the window `x/v ≤ u < x/rad v` from `rad n = u·rad v < x ≤ n = u·v`.
(v) Per-`v` harmonic window: `Σ_{a ≤ u < b} 1/u ≤ 1 + log(b/a)` via the
telescope `1/u ≤ log u − log(u−1)` for `u ≥ 2` (from
`Real.add_one_le_exp (−1/u)`), giving `≤ 1 + log(v/rad v) ≤ 1 + log v`.
(vi) Total `≤ Σ'_v powerfulWeight v` (`tsum_le_tsum`, nonneg). Traps:
`v = 1` (fiber = squarefree `n = u`, window `x ≤ u < x` EMPTY — handle
`rad v = v = 1` separately); `u = 1`-edges; summability side-goals (dominate
by the landed `powerfulWeight_tsum_le` and full-fiber sums). PB floor: NONE —
this is critical-path; if the tsum regroup fights, escalate to FABLE-QUEUE
with the exact broken step rather than weakening.

## Card W4-1 `Salt/Twelve/RelEngines.lean` — Sonnet, class B
Constant-FREE relative forms (each SIMPLER than its landed analog — same
reindex/swap bodies, stopping BEFORE any atom-constant step):
```lean
theorem marked_sqf_phi_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (a : ℕ) (s z : ℕ) (hs : 0 < s) (hz : 2 ≤ z) :
    (∑ r ∈ (Finset.range z).filter
        (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ a / (Nat.totient r : ℝ))
      ≤ (1 / (Nat.totient s : ℝ)) * (Real.log z) ^ a
          * Salt.Maynard.phiAtomSum z W'

theorem marked_sqf_g_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (a : ℕ) (D s z : ℕ) (hD : 3 ≤ D)
    (hDp : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) (hs : 0 < s) (hz : 2 ≤ z) :
    (∑ r ∈ (Finset.range z).filter
        (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ a / (gMult r : ℝ))
      ≤ (1 / (gMult s : ℝ)) * 2 * (Real.log z) ^ a
          * Salt.Maynard.phiAtomSum z W'

theorem g_gap_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (c b : ℕ) (D z R : ℕ) (hD : 3 ≤ D)
    (hDp : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p)
    (hz : 2 ≤ z) (hzR : z ≤ R) (hlR : 1 ≤ Real.log R) :
    (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
        (Real.log r / Real.log R) ^ c
          * ((Real.log z - Real.log r) / Real.log R) ^ b / (gMult r : ℝ))
      ≤ (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
          (Real.log r / Real.log R) ^ c
            * ((Real.log z - Real.log r) / Real.log R) ^ b
            / (Nat.totient r : ℝ))
        + (4 / (D : ℝ)) * Salt.Maynard.phiAtomSum z W'
```
No `∃` anywhere — every coefficient is literal (`1`, `2`, `4/D`). Routes:
`marked_sqf_phi_rel` = W3-0's reindex `r = s·t` + extend, STOPPING at
`phiAtomSum` (do not invoke `phiAtom_upper_lossy`). `marked_sqf_g_rel` =
W3-2's `r = s·b` multiplicativity + divisor swap + `exp(2/D) ≤ 2`, with the
residual `b`-sum bounded by `marked_sqf_phi_rel`-shaped sums (the `2` is the
tail factor). `g_gap_rel` = W3-2's upper-half swap with weights `≤ 1` and
`e^x−1 ≤ 2x`, landing `(4/D)·PAS`. Traps: the even-`s`/`box_g_pos` cases as
in W3-2 (reuse `box_g_pos`); weights `∈ [0,1]` on the box needs `z ≤ R`.
PB floor: none (these are sub-proofs of landed theorems).

## Card W4-2 `Salt/Twelve/MvSplit.lean` — Opus, class C
The split-error keystone re-statements (quantifier order is THE point:
`A` before `W'`):
```lean
theorem mv_I_split (F : Poly) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ kSieveIndex 5 R W',
              eval (ofPoly F) (fun i => Real.log (r i) / Real.log R) ^ 2
                / ∏ i, (Nat.totient (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 5
              * ((simplexInt (sq (ofPoly F)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 5 / Real.log R
          + A * (1 + Salt.Maynard.phiAtomSum R W') ^ 5 / D

theorem mv_J_split (F : Poly) (m : Fin 5) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
              (∑ u ∈ Finset.range R,
                  yF R W' F (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
                / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 6
              * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 6 / Real.log R
          + A * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ 6 / D
```
**CORRECTION (2026-07-10, wave-4-fix Fable pass — mv_J_split `1/D` bucket
reshaped to MIXED-power `(1 + X + PAS)^6`).** The original `(1+PAS)^6` bucket
was PROVABLY too tight: `mv_J`'s main term `X²·∑Ev²/∏g` has an outer `X²`
prefactor (from `Inn = X·Ev + δ`), so its coprimality-drop `1/D` error is
`X²·A_m·(1+PAS)⁴/D` — fitting `(1+PAS)⁶` needs `X ≤ C(1+PAS)`, a Mertens-type
sharp lower bound the repo lacks (the W4-2 execution hit exactly this wall).
The fix: `(1+X+PAS)⁶` dominates BOTH the main-drop `X²(1+PAS)⁴` (via
`X² ≤ (1+X)²`, TRIVIAL — no cross-bound) AND the square-expansion `(1+PAS)⁶`
(finding: `|Inn| ≤ cF·PAS`, the `Pr`-weighted parts swap to `~PAS⁶/D`). It
still closes the endgame with NO extra κ: at fixed `(W',D★)`, `R→∞`,
`(1+X+PAS)⁶ ≈ 64·X⁶` (both `X`, `PAS ~ κ log R`), so the term is `≈ A·X⁶/D★`,
relative error `→ 64A/(D★·J) < δ★` (Archimedes; NO κ factor). `X = κ log R`
is explicit, so `(1+X+PAS)` is consumption-safe. The REJECTED `κ⁻²` reshape
was fatal (`κ⁻²/D ≈ 25`, no decay). `mv_I_split` is UNAFFECTED (no inner
contraction, no `X²`; its `(1+PAS)⁵/D` is already landed & correct).

`A` may depend on `F` (and `m`) ONLY. THIRD frozen deliverable (adversarial
pass, binding — the landed `inner_contract`'s constant `cic` is W'-opaque
and leaks into mv_J's `1/D` side through the MQ/MQ2 collision moments, so
it can NOT be black-boxed):
```lean
theorem inner_contract_rel (F : Poly) (m : Fin 5) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
      ∀ r ∈ kSieveIndex 5 R W', r m = 1 →
      |(∑ u ∈ Finset.range R,
            yF R W' F (Function.update r m u) / (Nat.totient u : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R)
            * eval (contractAt m F)
                (fun i => Real.log (r (m.succAbove i)) / Real.log R)|
      ≤ c + A * Salt.Maynard.phiAtomSum R W'
              * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1))
```
(the landed `inner_contract` shape with the SPLIT error: the `Pr(r)`-weighted
part carries `A·PAS` with `A` F-only; the `r`-uniform part keeps opaque `c`.
Proof = the landed `inner_contract` with ONLY the `u ⊥ ∏r`-drop step routed
through `marked_sqf_phi_rel`; everything else black-boxes.)
Route: replay the landed `mv_I`/`mv_J` proofs (they are on disk — READ them)
with every `1/D`-producing step routed through W4-1's relative engines
instead of the constant-bearing W3 lemmas: (mv_I) the stage-2 pairwise
drop's marked²·unmarked³ products become `(PAS)²·(PAS)³`-bounded with the
absolute tail `Σ_{p>D}1/(p−1)² ≤ 2/D` — the landed covering uses 20 ORDERED
pairs, so `A = 40·(monomial ℓ¹-data of sq(ofPoly F))`-shaped; (mv_J) the
g-sandwich gaps (`g_gap_rel`), the outer pairwise drop (`marked_sqf_g_rel`),
the `u ⊥ ∏r` swaps via `inner_contract_rel` + `marked_sqf_phi_rel` /
`marked_sqf_g_rel`, each with absolute coefficients; the `1/log R`-side
(budget_moment/mv_monomial(±g) machinery, floor slips, X-power absorptions)
keeps landed per-`W'` constants inside `∃c`. Crude moments on the `1/D` side
MUST be `PAS`-relative (`marked_*_rel` at `s = 1`), never `c(W')·(1+X)`.
Traps: (i) `inner_contract` is NOT `1/log R`-only — its `X·Pr(r)` error part
feeds the `1/D` side (MQ/MQ2); use `inner_contract_rel` there. In the
square-expansion use `(a+b)² ≤ 2a² + 2b²` on `δ ≤ c + A·PAS·Pr` — NO mixed
`c·A·Pr` term may survive multiplication into the `1/D` side (a pure
`c(W')/D` coefficient is consumption-poison; mixed `c(W')/(D·log R)` terms
are fine — they vanish at fixed `(W',D)`); (ii) `mv_monomial_g`'s error
factor `(1+X)^{n−1}(1+log R/D)` MIXES the sides: its `log R/D` part must be
re-derived relatively (the g-gap accumulation with `g_gap_rel`, coefficient
`4·n`-shaped absolute × `(1+PAS)`-powers) — a genuinely new sub-proof;
(iii) `(1+PAS)` vs `(1+X)`: on the `1/D` side always dominate crude sums by
`PAS`-powers (PAS ≥ the a=0 crude moment ≥ 1 for `z ≥ 2` since `r=1 ∈` box).
PB floor: `mv_I_split` + `inner_contract_rel` are the must-haves; if the
mv_J double-swap assembly resists, land those two + flag `mv_J_split` to
FABLE-QUEUE with the exact broken step. Do NOT land a `mv_J_split` whose
`1/D` coefficient carries ANY opaque W'-dependent factor — that artifact is
unconsumable (worse than nothing, it would mask the gap).

## Card W4-3 `Salt/Maynard/Lemma53W.lean` — Opus, class B/C
The free-`(W',D)`, `|y| ≤ B` contraction (mechanical sweep per the
lemma53 interface map; the heart — `yM`, `lamPhiContractM`,
`lamPhiContractM_collapse`, `sigmaMuKpin`, `s2_diag_lam_restricted` — is
ALREADY free-`W`):
```lean
theorem euler_tail_LW (M : ℕ) (L : ℝ) (D : ℕ) (hL : 1 ≤ L)
    (hD : 4 * L ≤ (D : ℝ)) :
    ∑ t ∈ ((Finset.range M).filter
        (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1,
      L ^ t.primeFactors.card * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2
      ≤ 4 * L / (D : ℝ)

theorem lemma53_tightW (k R W' D : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (B : ℝ) (hB0 : 0 ≤ B) (hyB : ∀ s, |y s| ≤ B)
    (hysupp : ∀ s, s ∉ kSieveIndex k R W' → y s = 0)
    (r : Fin k → ℕ) (hrm : r m = 1) (hR : 2 ≤ R)
    (hrsupp : r ∈ kSieveIndex k R W')
    (hW' : Squarefree W') (hDlt : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p)
    (hk : 1 ≤ k) (hDk : 12 * k ^ 2 ≤ D) :
    |yM k R W' m y r
        - ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
      ≤ B * (lemma53Const * (k : ℝ)) * Real.log R / (D : ℝ)
```
Recipe (from the map; verbatim ports keeping old names intact, new `*W`):
`euler_tail_LW` = `euler_tail_L` with `D₀ k → D` (its `k` occurs ONLY via
`D₀ k` — drop the binder); then `phiSq_tail_tightW`, `phiSq_dvd_ne_tightW`,
`phiSq_dvd_tightW`, `tailCoordSetW`, `tail_factor_le'W`, `gProd_boundW`,
`stepB_identityW` (pure `W k → W'`, no `D`), `abs_mainSum_le_tightW` (+`B`:
`hy1` enters ONLY at the `|y(update)|/φ ≤ B/φ` step → `B·rankinC·logR`),
`htail_tightW` (+`B` at its one `|y a|` step → `B·4·exp4·rankinC·k·logR/D`),
assembly `lemma53_tightW` (`|G−1|·|S| + |PT|` with the `B` factor threaded;
`hfinal`'s `nlinarith` gets `hB0`). Use `D_lt_of_prime_dvd_coordW` (STRICT
`D < p`, collision convention) everywhere `D₀_lt_of_prime_dvd_coord` was
used; `3 ≤ p` comes from `D < p`, `4 ≤ D`. NO primorial/parity facts are
used anywhere in the chain (verified). Traps: `rankinC`/`lemma53Const` are
landed and W-free — do NOT redefine; `hkD : k ≤ D` inside `htail_tight`
follows from `12k² ≤ D` by `nlinarith`. PB floor: none (two independent
precedents: `c7ee1f9`, `*_K`).

## Card W4-4 `Salt/Twelve/FstarNorm.lean` — Sonnet, class B
Normalization + instantiation helpers:
```lean
def Qabs (F : Poly) : ℚ := (F.map (fun m => |m.2|)).sum

noncomputable def Fstar1 : Poly := Fstar.map (fun m => (m.1, m.2 / Qabs Fstar))

theorem M5_cert1 : 2 * Ical Fstar1 < ∑ m : Fin 5, Jcal m Fstar1

theorem yF_Fstar1_abs_le_one (R W' : ℕ) (s : Fin 5 → ℕ) :
    |yF R W' Fstar1 s| ≤ 1

theorem primorial_hDlt (D : ℕ) :
    ∀ p : ℕ, p.Prime → ¬p ∣ primorial D → D < p
```
Routes: `M5_cert1` by the scaling identities `Ical (scale q F) = q²·Ical F`,
`Jcal m (scale q F) = q²·Jcal m F` (List.map algebra over the landed defs;
`Qabs Fstar > 0` by `norm_num`-evaluation or positivity of the coefficient
list) + the landed `M5_cert`; do NOT re-run the 3136-monomial `norm_num`.
`yF_Fstar1_abs_le_one`: off-box `= 0`; on-box `|eval (ofPoly F) t| ≤
Σ|coeffs|` (monomials `∈ [0,1]` — `t ∈ [0,1]⁵` on `kSieveIndex` needs
`log rᵢ ≤ log R`, from `rᵢ < R`), and `Σ|coeffs Fstar1| = 1` by
construction. `primorial_hDlt`: `p ∤ primorial D` + `p ≤ D` would force
`p ∣ primorial D` (the product of primes `≤ D`) — contradiction; use
mathlib's `primorial`/`Nat.prod` facts or the repo's `W_squarefree`-adjacent
lemmas (`Tuple.lean`). Check first whether an equivalent exists in
`Tuple.lean` (the W2-4 report mentions primorial discharge helpers) — reuse,
don't duplicate. PB floor: none.

## Card W4-5 `Salt/Twelve/QdiagBridge.lean` — Opus, class C+
The S2 bridge (consumes W4-2, W4-3, W4-4; the deepest card):
```lean
theorem qdiag_bridge (F : Poly) (m : Fin 5) (hQ : Qabs F ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 300 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 2 ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 5 R W' m (yF R W' F)
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 6
              * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 6 / Real.log R
          + A * ((W' : ℝ) / W'.totient)
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ 6 / D
          + A * ((W' : ℝ) / W'.totient) ^ 2
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ 6 / D ^ 2
```
**TWO-TERM bucket `κ⁻¹·Y⁶/D + κ⁻²·Y⁶/D²` (wave-4-fix-2 2026-07-10, Opus
inline — endgame-verified).** The W4-5 execution caught a SECOND shape defect
the original single-`κ⁻¹` bucket missed: the square difference
`yM² − Inn² = 2·Inn·δ + δ²` (`δ = yM − Inn`, `|δ| ≤ ε = lemma53Const·5·logR/D`)
has a SELF-term `Σδ²/∏g ≤ ε²·Σ1/∏g ≤ κ⁻²·X²·PAS⁴/D² ≤ κ⁻²·Y⁶/D²` — genuinely
`κ⁻²/D²` (two `D`'s from `ε²`), NOT the rejected `κ⁻²/D`. It is ENDGAME-SAFE
(`κ⁻²/D² ≤ 25/D → 0` via `κ⁻¹ ≤ 5√D`, subdominant to the `κ⁻¹/D` term's
`5/√D`; numerically confirmed both → 0). The complete `1/D` accounting is
now: (a) cross `2·Inn·δ` → `κ⁻¹·Y⁶/D`; (b) self `δ²` → `κ⁻²·Y⁶/D²`; (c)
consumed `mv_J_split` → `κ⁻¹·Y⁶/D`. Provable from the landed pieces
(`qdiag_eq_yMsq_sum`, `yM_sub_inn_le`, `absInn_le_pas`, `qdiag_bridge_of`,
`2d4b522`) + the crude 4-dim g-moment `Σ_{u:uₘ=1}1/∏_{i≠m}g ≤ (2·PAS)⁴`. The
mixed `(1+X+PAS)⁶` (below) is still needed in BOTH terms (the `X²`/`X`-powers
from `Inn`/`ε`). This card covers BOTH of qdiag_bridge's older `1/D`
sources: (a) the `lemma53W` contraction error `logR/D` summed against
`Σ_u|Inn|/∏g ≲ X·(1+PAS)⁴`, `= logR·X·(1+PAS)⁴/D = κ⁻¹·X²·(1+PAS)⁴/D ≤
κ⁻¹·(1+X+PAS)⁶/D`; and (b) the consumed `mv_J_split` error `(1+X+PAS)⁶/D ≤
κ⁻¹·(1+X+PAS)⁶/D` (κ⁻¹ ≥ 1). The `(1+PAS)⁶` bucket was too tight for BOTH
(same `X²` wall as mv_J_split). ONE κ⁻¹ (from the contraction's `logR = X/κ`)
is unavoidable; it is affordable (κ⁻¹/D → 0, see below). NOTE the two 1/D
sources are NOT summed with distinct exponents — `(1+X+PAS)⁶` dominates each,
so a single term suffices.
NOTE: `A` here is F-only ONLY BECAUSE mv_J_split/inner_contract_rel carry
F-only `A`s (the adversarial pass traced `cic`-leakage; the
`inner_contract_rel` deliverable in W4-2 is what makes this card's claim
true — W4-5 must consume it, never the landed `inner_contract`, on any
`1/D` path). It is CONSUMABLE because κ⁻¹ is a CONCRETE computable
of `W'` (not opaque) and (RESOLVED at this pre-flight, numerically verified
with ≥30× slack): the elementary bound
`(primorial D : ℝ)/(primorial D).totient ≤ 5·Real.sqrt D` holds via
`∏_{p≤D} p/(p−1) ≤ exp(Σ_{p≤D} 1/(p−1))` and — the key elementary step —
`Σ_{p≤D} 1/(p−1) ≤ 1 + (1 + log D)/2` (the primes ≤ D other than 2 are
distinct odds ≥ 3, so the j-th contributes ≤ 1/(2j); NO Mertens needed).
So the endgame's error is `A·5√D/D = 5A/√D → 0`, Archimedes closes. The
`primorial_ratio_le` lemma lands in wave 5 (`5·√D` frozen there).
Route: (1) `Qdiag_mW 5 R W' m y = Σ_{u: uₘ=1} (∏ᵢ g(uᵢ))·V(u)²` by
`s2_diag_lam_restricted` at `W'` (free-W, landed; `V = lamPhiContractM`);
`∏g·V² = yM²/∏_{i≠m}g(uᵢ)` (`μ² = 1` on the box, `g(1) = 1`).
(2) `|yM(u) − Inn(u)| ≤ lemma53Const·k·logR/D` pointwise by `lemma53_tightW`
at `B = 1` (from `hQ` via W4-4's `|yF| ≤ Qabs F ≤ 1` on the box; support
from `yF`'s `if`). (3) `|yM² − Inn²| ≤ |yM−Inn|·(2|Inn| + |yM−Inn|)` with
`|Inn(u)| ≤ X·c_F + (landed inner_contract error)`. (4) Sum over `u`: crude
g-moments via `marked_sqf_g_rel (s=1)` powers — every crude sum
`PAS`-relative, never `c(W')`-weighted. (5) `Σ_u Inn(u)²/∏_{i≠m}g =
mv_J_split`'s LHS — conclude, collecting the `1/logR`-side into `c` and the
`1/D`-side into `A·κ⁻¹·(1+PAS)⁶/D`. Traps: `V` vanishes off `uₘ = 1`
(`lamPhiContractM`'s filter); `12·5² = 300 ≤ D` is the binding constant
(hence `300 ≤ D`); the `u`-box is `kSieveIndex 5 R W'` filtered `uₘ = 1` —
EXACTLY `mv_J`'s outer box, no reindex needed; keep the κ⁻¹ EXPLICIT — do
NOT absorb it into `A` (that would smuggle the W'-dependence back into the
opaque constant and kill the endgame). PB floor: land steps (1)–(3) + the
statement with (4)–(5) hypothesized, flag loudly.

## Dependency DAG and dispatch plan (wave 4)

```
W4-0 (Opus) ──────────────→ (endgame, wave 5)
W4-1 (Sonnet) ─→ W4-2 (Opus) ─→ W4-5 (Opus)
W4-3 (Opus) ──────────────────→ W4-5
W4-4 (Sonnet) ────────────────→ (wave 5; W4-5 may use yF_Fstar1_abs_le_one)
```
Round 1: W4-0, W4-1, W4-3, W4-4 in parallel (independent files). Round 2:
W4-2. Round 3: W4-5. Verify+commit per node; wire into `All.lean` at
reconciliation. Escalation per MODEL_POLICY.

---

# Wave-5 cards (Fable pre-flight, 2026-07-10) — THE ENDGAME

Statements FROZEN (iron rule 1). Abbrev: `X = (φW'/W')·log R`,
`PAS = phiAtomSum R W'`, `Y = 1+X+PAS`, `κ⁻¹ = W'/φW'`, `M₅ = (Σ Jcal m F★)/Ical F★
= 191881/95820`, `θ★ = 1999/2000`, `θ₊ = 3999/4000`, `K₀ = 64` (window `(N,64N]`).

## Pre-flight findings (three deep-reads of the PROOF internals; binding)

**FEASIBILITY: the rung closes, with ONE genuine remaining node (Node B below).**
Nothing is impossible; the S1 collision bound is TRUE for `yF` (it is Maynard's
real weight), it just needs a new estimate.

1. **The endgame ratio is a pure rational (derived term-by-term).** With the
   SHARP S1 (`mv_I`, factor-2 KILLED) and `qdiag_bridge`:
   `Σ_m S2m / S1 = (Δπ·log R)/(63·N)·M₅` — EVERY `φW'`, `W'`, `log N` cancels
   (`(W'/φW')·X = log R`; `X⁶/X⁵ = X`; the `63 = K₀−1` window count cancels the
   `63` of `WindowPNT`). With `Δπ ≥ (63−ε)N/log N` and `log R/log N → θ★/2`:
   `→ ((63−ε)/63)·(θ★/2)·M₅ → (θ★/2)·M₅ = 383570119/383280000 = 1.00076 > 1`.
   Maynard's `M_k > 4` is REPLACED by `(θ★/2)·M₅ > 1 ⟺ M₅ > 2/θ★ ≈ 2.0013`
   (certified `M₅ = 2.00252`; `θ = 99/100` FAILS — the rung genuinely needs
   `θ > 2/M₅`). `norm_num` target: `1999·191881·1000 > 95820·2000²`.
   The landed `win_core` constant tower (`126=2·63`, `1/16`, `504=4·126`,
   `2916`, `k→∞` dominance) is ENTIRELY DISCARDED.
2. **The interface to hit is `S1_lt_sum_S2m`** (`Endgame.lean:315`, free `y`,
   slots `δ`/`cval`/`errEH`) — `win_core'` produces its `hnum`. The prime-supply
   plug is `deltaPi_lower_of` (`Final.lean:174`), which takes `WindowPNT`'s
   `63−ε` directly in place of Chebyshev `c=1` (`ChebyshevInterval.lean:144`,
   which is FATAL here: `2/(a·θ) ≥ 2.17 > M₅` for any fixed `a<1`).
3. **Prime-side plumbing (clusters 1–3): all mechanical, B/A.** Confirmed:
   (i) `Salt.Twelve` reuses `Salt.Maynard.hSeq 5` — no tuple mismatch;
   (ii) `W'·R² ≤ N^{θ₊}` at fixed `W'` reduces to `W' ≤ N^{1/4000}` (eventual);
   (iii) the λ-bound `lam_abs_le_sharp_uniform` is free-`W`/free-`y` under just
   `|y| ≤ 1` → ports to `yF Fstar1` via the landed `yF_Fstar1_abs_le_one`;
   (iv) `herr` vanishes against the main with a `(log N)²` margin;
   (v) the pigeonhole spine needs NO squarefree hypothesis — pure
   `S2m→S2mW`, `W k→W'` + a ~10-line `hSeq_diam_le_twelve` swap for `Icc(-12,12)`.
4. **THE ONE OPEN NODE — S1 non-tensor collision (Node B).** The landed collision
   bound's `hfmono` (divisor-DECREASING) is load-bearing for DIRECTION: it is the
   sole source of the `(p−1)⁻²` Euler-tail decay. `yF`'s monomials are divisor-
   INCREASING, so the landed route fails, `|y|≤1` fails, per-monomial fails,
   Cauchy–Schwarz gives a true-but-divergent bound. The tensor dependency bottoms
   out in ONE atom (`inner_abs_le`, `CollisionQuant.lean:1107`). Node B discharges
   it via a Lipschitz-smoothness argument — a C/D node needing its OWN design pass.
5. **ZERO-SLACK on the SHARP constant** (margin `7.6×10⁻⁴`): the factor-2 MUST be
   killed (crude-2 S1 ⟹ ratio `0.50 < 1`, fatal). All errors VANISH (in `N`,
   `D★`, or budgeted `ε`), so the margin absorbs them; but no FIXED loss is
   allowed — the sharp S1 main constant must be EXACTLY `(K₀−1)·N/W'·X⁵·Ical`.

## Error budget (term-by-term, from the win_core deep-read) — the ordering strategy
Both mains `~ N·(log N)⁵` at fixed `(W'=primorial D★, D★)`, `N→∞`. Total allowable
relative loss `< 7.6×10⁻⁴`; per-consumer budget `δ★/8 ≈ 3.1×10⁻⁴`.
1. Pick `ε` (WindowPNT, term i) and `θ★=1999/2000` (level, term 0) so
   `((63−ε)/63)(θ★/2)M₅ > 1 + margin/2`. `ε` is a budgeted constant (not a limit).
2. Pick `D★` (Archimedes) so the `/D` terms — `mv_I_split` `A(1+PAS)⁵/D`,
   `qdiag` `κ⁻¹Y⁶/D` + `κ⁻²Y⁶/D²`, all F-only `A` — sum `< margin/4`, using
   `primorial_ratio_le : κ⁻¹ ≤ 5√D` (`κ⁻¹/D → 5/√D`, `κ⁻²/D² → 25/D`).
3. Fix `W' = primorial D★`. Take `N→∞`: the `1/log R` errors (`mv_I_split`,
   `qdiag` opaque `c`), the `herr` `C/(log N)⁷` (term iv), the S1 truncation
   `Cs·R²·polylog = N^{−1/2000}·polylog` (term v, via `eventually_poly_beats_polylog`),
   and the `Δπ` shift `12·log N/(63N)` (term vi) each `→ 0` below the remaining budget.
4. Discharge Node B (sharp collision, term vii), assemble `hnum`, call the
   `W'`-reissued `S1_lt_sum_S2m`, close `S1 < Σ S2m`, pigeonhole → gap `≤ 12`.

## Cards — the MECHANICAL/FEASIBLE layer (Opus-executable from the deep-read reports)

### W5-1 `Salt/Maynard/CollisionQuantW.lean` (Node A: S1 collision SPLIT) — Opus, B
Refactor so the collision assembly is `y`-generic modulo an atom. Define
```lean
def S1InnerBound (k R W' : ℕ) (y : (Fin k → ℕ) → ℝ) : Prop :=
  ∀ s : ℕ, Squarefree s → ∀ (assignment data α as in inner_abs_le),
    |∑ u ∈ kSieveIndex k R W', (∏ i, (Nat.totient (u i):ℝ))
        * yhat … u * yhat … u|
      ≤ (3:ℝ)^s.primeFactors.card
          * (∏ p ∈ s.primeFactors, ((p:ℝ)-1)⁻¹^2)
          * ∑ r ∈ kSieveIndex k R W', (y r)^2 / ∏ i, (Nat.totient (r i):ℝ)
```
(the EXACT conclusion of `inner_abs_le`, `CollisionQuant.lean:1114–1123` — READ
it and transcribe verbatim). Then land `collision_lower_orderW_of` : the current
`collision_lower_orderW` (`:2310`) with `hf01`/`hfmono`/`hy` REPLACED by
`(hInner : S1InnerBound k R W' y)` and `hy0` (off-support). Body UNCHANGED except
the one call at `:2423` becomes `hInner …`. Propagate the swap up:
`crossCollisionControlled_holds_of`, `compat_le_two_yside_of`, `S1_le_of`,
`S1_upper_of` (each drops the tensor hyps, takes `S1InnerBound`). Verify: the old
`collision_lower_orderW` still builds (keep it; the `_of` versions are parallel).
PB floor: none — pure signature refactor, the assembly is already `y`-generic.

### W5-2 `Salt/Maynard/EHLevelTheta.lean` (Cluster 1: EH at θ★) — Opus, B (one C)
Level-θ₊ / range-`N^{θ★/2}` twins of the pinned literals. Land:
`lod_error_pow_theta` (`lod_error_pow` with `(1/2:ℝ)→(3999/4000:ℝ)`);
`EH_range_theta` (`R=⌊N^{1999/4000}⌋`, `R²≤N^{3998/4000}`, `W'·(log N)^{B'}≤N^{1/4000}`,
`1/4000+3998/4000=3999/4000`); `R_sq_le_theta`, `logR_upper_theta`
(`≤(1999/4000)log N`), **`logR_lower_theta`** (the ONE fiddly node: the floor-slack
exponent split — landed `1/5=1/6+1/30` becomes `1999/4000 = ρ + rest` with `2·x^ρ
≤ x^{θ★/2}`; choose `ρ` and thread its output constant), `R_ge_two_theta`,
`R_le_N'_theta`. `eventually_poly_beats_polylog` is θ-agnostic (reuse). Traps: the
`logR_lower_theta` output constant ripples into every `analyticFrontier`/`win_core`
threshold — pick it once and thread. PB floor: none (literal swaps + one split).

### W5-3 `Salt/Maynard/S2CompatEHW.lean` (Cluster 2: herr at W'/yF/θ★) — Opus, B (one B/C)
Free-`W'` mirrors: `abs_S2mW_sub_compatMainW_le` (mirror `S2CompatEH.lean:84`),
`abs_S2mW_sub_compatMainW_le_disc_R_uniform` (mirror `FrontierDischarge.lean:224`,
reuse free-`W` `lam_abs_le_sharp_uniform` + landed `s2PrimeCountW_approx'`),
**`compat_pair_fiber_leW`** (mirror `S2FiberCount.lean:411` — the free-`W'` CRT
`(3k)^{ω(q)}`-multiplicity fiber count, the ONE intricate atom),
`S2mW_ge_compatMain_theta_uniform` (mirror `:289`/`LevelConsume.lean:326`,
consuming `lod_error_pow_theta` at level θ₊). `S2mW_lower` itself is already free
and needs no change. λ-bound discharge via `yF_Fstar1_abs_le_one`. PB floor:
`compat_pair_fiber_leW` may need care (CRT bookkeeping); flag if it fights.

### W5-4 `Salt/Twelve/PrimorialRatio.lean` — Sonnet, B
```lean
theorem primorial_ratio_le (D : ℕ) (hD : 2 ≤ D) :
    (primorial D : ℝ) / (primorial D).totient ≤ 5 * Real.sqrt D
```
Route (elementary, NO Mertens; numerically ≥30× slack): `primorial D/φ =
∏_{p≤D} p/(p−1) ≤ exp(Σ_{p≤D} 1/(p−1))`, and `Σ_{p≤D} 1/(p−1) ≤ 1 + (1+log D)/2`
(the primes `≤ D` other than `2` are distinct odds `≥ 3`, so the `j`-th smallest
prime `p_j ≥ 2j+1`, giving `1/(p_j−1) ≤ 1/(2j)`; `Σ 1/(2j) ≤ (1+log(π(D)))/2 ≤
(1+log D)/2`). Then `exp(1+(1+log D)/2) = e^{3/2}·√D ≤ 5√D` (`e^{3/2}=4.48`). Traps:
the `p_j ≥ 2j+1` injection into odds (careful with `p=2`); mathlib `primorial`
= `∏ p ∈ (range(n+1)).filter Nat.Prime`. PB floor: none.

### W5-5 `Salt/Twelve/Pigeonhole12.lean` (Cluster 3) — Opus, A/B
Free-`W'` + diam-12 pigeonhole. `sum_S2mW_eq`, `exists_window_two_primesW`,
`bounded_gap_of_S2_gt_S1_twelve`, `bounded_gaps_reduces_twelve` — the four spine
lemmas (`Endgame.lean:254/268/292/349`) with `S2m→S2mW`, `W k→W'`, and the
`:303–306` bullet swapped: `hSeq_le_D₀ k` → `Salt.Twelve.hSeq_diam_le_twelve j i`,
interval `Icc(-(D₀ k),D₀ k)` → `Icc(-12,12)`, output `C = D₀ k₀` → `12`. All
`y`/`W'`-generic (no squarefree needed). Frozen conclusion of the last:
```lean
theorem bounded_gaps_reduces_twelve (W' : ℕ)
    (hwin : ∀ N : ℕ, ∃ (N' R ν₀ : ℕ) (y : (Fin 5 → ℕ) → ℝ), N ≤ N' ∧
      S1 5 64 N' R W' ν₀ y < ∑ m : Fin 5, S2mW 5 64 N' R ν₀ W' m y) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-12 : ℤ) 12
```
PB floor: none.

### W5-6 `Salt/Twelve/WinCore.lean` (the ratio assembly + `gaps_le_twelve`) — Opus, C
The capstone assembly. Depends on ALL of W5-1..W5-5, `mv_I_split`, `qdiag_bridge`,
`M5_cert1`, `FstarNorm`, and Node B (via the W5-1 `S1InnerBound` discharged for
`yF Fstar1`). Structure: (1) `deltaPiW_lower` — feed `WindowPNT` into
`deltaPi_lower_of` (`c := 63−ε`, shift `≤ 12`). (2) `sharp_S1_upper` — `S1 ≤
(63N/W')·X⁵·Ical + [errors]` from `mv_I_split` + W5-1 (collision, needs Node B)
+ S1 truncation. (3) `sharp_S2m_lower` — `S2mW ≥ (Δπ/φW')·X⁶·Jcal_m − [errors]`
from `S2mW_lower` (W5-3 `herr`) + `qdiag_bridge`. (4) `win_core'` — assemble
`hnum : S1 < Σ_m (…)` via the ratio `(θ★/2)M₅ > 1` (`norm_num` on
`1999·191881·1000 > 95820·2000²`) with all errors budgeted `∀ᶠ N`; call
`S1_lt_sum_S2mW`. (5) `analyticFrontierW` — the `∀ N ∃ N'≥N` largeness (mirror
`analyticFrontier_lod`, the `∀ᶠ` stack + `eventually_poly_beats_polylog`, at θ★).
(6) `gaps_le_twelve (hPNT : WindowPNT) (hEH : EHall)` — `bounded_gaps_reduces_twelve
(primorial D★) (analyticFrontierW …)` at the Archimedean `D★`. This is the
FROZEN capstone (`gaps_le_twelve` at the top of this doc). Traps: the Archimedean
`D★` choice (from `primorial_ratio_le` + the `/D` error budget) — a concrete
`∃D★`; the `∀ᶠ N` threshold assembly is the bulk. PB floor: land `win_core'`
(the ratio) + the assembly with `analyticFrontierW`'s `∀ᶠ` conjuncts as
hypotheses if the largeness stack fights; flag.

# Node C — THE CLOSURE (Fable design pass 2, 2026-07-11) — termwise + marked moments

**STATUS: THE RUNG IS CLOSED (2026-07-11).** The frozen top-of-doc target is
LANDED under its frozen name, UNCONDITIONAL beyond `WindowPNT`/`EHall`:
**`gaps_le_twelve (hPNT : WindowPNT) (hEH : EHall)`**,
`Salt/Twelve/GapsUncond.lean` (`eb42624` + rename), axiom-clean
`[propext, Classical.choice, Quot.sound]`, bare-`lake build`-checked.
Chain: NC-1 (`a0ce27e`, `collision_yF_M`), NC-2 (`4594f54`, `s2_inner_yF`,
`(p−2)⁻²`), NC-3 (`4648af1`, now `gaps_le_twelve_of_frontierM`), R1a
(`4868be9`, `JcalPos`), R2a (`9c54938`, `FrontierM` — parameterized per the
pinned-Dfin correction `51221c8`), R1b (`fbde659`, `QdiagFloor`), R2b+R2c
(`eb42624`, `GapsUncond`: `winSlackM_ev` + capstone; `deltaPi` upper via
mathlib Chebyshev; the qdiag error folded additively into `win_ratio_core`'s
free `eps` — the `/2`-floor form would have blown the certificate margin).
Historical residual notes below are CLOSED; kept for the record. Original
review-era text: Live
residuals (flags.md 2026-07-11 + Fable review): R1 — the `hQd` comparison,
discharged POINTWISE at `(primorial Dfin, Dfin)` via the now-public
`s2_inner_termwise` (NO statement surgery on the frozen `hQd`; per-m
positivity LANDED: `Jcal_Fstar1_eq`/`Jcal_Fstar1_pos`,
`Salt/Twelve/JcalPos.lean`; R1b LANDED: `qdiag_floor` (`Qdiag ≥ X⁶·J₁/2`,
`∃Dthr` built from `qdiag_bridge`'s `A`), `qdiag_cmp` (the hQd payload,
`CF = 720000/J₁` a closed numeral), `s2_collision_floor` (the pointwise S2
collision closure, RHS = `s2_collision_yF_C`'s) — `Salt/Twelve/QdiagFloor.lean`,
quantifier order `∃CF ∃Dthr ∀W'D ∃R₀ ∀R` frozen); R2 — the frontier slack,
PARAMETERIZED per the
pinned-Dfin correction (flags 2026-07-11: the slack constants are ∃-opaque, so
the Archimedes `D` is chosen existentially AFTER the constants — no numeral
resize suffices). R2a LANDED: `WinFrontierMW (D)`/`WinSlackM D C₀ N'`/
`winFrontierMW_of (300 ≤ D)` + defeq bridge `winFrontierM_of_W`
(`Salt/Twelve/FrontierM.lean`) — conjuncts 1–6 discharged at any `D ≥ 300`,
only conjunct 7 (`hslackEv`) remains. R2b = discharge `∀ᶠ N', WinSlackM D C₀
N'` at the existential `D`; R2c = the ~30-line assembly picking
`D ≥ max(Dthr, 300)` from R1b's constants → unconditional `gaps_le_twelve`.

**SUPERSEDES Node B's crude-domination route** (whose S1 form was proven a
mirage by NB-1 — the domination overshoots to `M` and the abs/signed forms
don't align — and whose S2 form is spectral, NB-3). The correct closure needs
NO smoothness/Lipschitz and NO domination: it is a TERMWISE absolute bound
(valid purely from `|y| ≤ 1`), a contamination partition (the landed
`hcompl`/`hpart` structure), and MARKED componentwise moments (our landed
`marked_sqf_phi_rel`/`marked_sqf_g_rel` machinery) — with all constants
absorbed by an ABSTRACT Archimedean `Dfin` (never computed; `primorial Dfin`
appears only symbolically).

## The two discharges (hand-derived, term-by-term; numerically checked)

**S1 (unconditional in R).** For `|y| ≤ 1` supported on the box, the per-(s,α)
inner form satisfies, TERMWISE: `|term_u| = ∏φ(u)·|y(u∨σ)||y(u∨τ)|/(∏φ(u∨σ)·
∏φ(u∨τ)) ≤ 1/(∏φ(u)·Wσ(u)·Wτ(u))` (`φ(u∨σ) = φ(u)·Wσ`, `totient_lcm_split` —
PUBLIC). Partition `u` by the contamination set `Q = {p ∣ s : p ∣ u at its
fst- or snd-slot}` (a prime dividing `u` at any OTHER coordinate makes the
join pairwise-non-coprime ⟹ `u∨σ ∉ kSieveIndex` ⟹ `yF(u∨σ) = 0` — term
VANISHES; and `u` pairwise-coprime means each `p` divides at most one
coordinate, so fst-XOR-snd): `Wσ·Wτ ≥ ∏_{p∉Q}(p−1)²·∏_{p∈Q}(p−1)` (the
contaminated prime loses its power on ONE side only). The `Q`-marked crude
moment: `Σ_{u: p|u@slot(p) ∀p∈Q} 1/∏φ(u) ≤ ∏_{p∈Q}(p−1)⁻¹·M` (componentwise
reindex `u_i = p·u'_i`, `φ(p·u') = (p−1)φ(u')`, image ⊆ box — EXACTLY the
`marked_sqf_phi_rel` reindex, on the 5-dim box). Net per `Q`:
`∏_{p|s}(p−1)⁻²·M`; `Σ_Q ≤ Σ_{T⊆pf(s)} 2^{|T|} = 3^{ω(s)}`. TOTAL:
`3^ω·∏(p−1)⁻²·M`. NO CS, NO smoothness, NO threshold.

**S2 (∀ᶠ R at fixed (W',D)).** Same skeleton with `g` for `φ` and the
CONTRACTION `V = lamPhiContractM`: `|term_u| = ∏g(u)·|V(u∨σ)||V(u∨τ)| ≤
(PAS+ε)²/(∏g(u)·Gσ·Gτ)` where `|V(w)| = |yM(w)|/∏g(w) ≤ (|Inn(w)|+ε)/∏g(w) ≤
(PAS+ε)/∏g(w)` via `lemma53_tightW` (B=1) + `absInn_le_pas` (both LANDED);
`ε = lemma53Const·5·logR/D`; joins violating pairwise coprimality or `wₘ≠1`
give `V = 0`. Contamination partition + `g`-marked moments
(`∏_{p∈Q}(p−2)⁻¹·Mg₄`, `Mg₄ ≤ (2·PAS)⁴` = the landed `gmoment4_le`,
`uₘ=1`-box): TOTAL `≤ 3^ω·∏(p−2)⁻²·(PAS+ε)²·(2PAS)⁴` — the atom keeps the
g-weighted `(p−2)⁻²` (the `(p−2)⁻²≤4(p−1)⁻²` conversion costs `4^ω`, unabsorbable
by any F-only CF; it is deferred to the collision assembly's euler tail, where it
costs a single factor 4: `48 = 4·Cs`). Convert to the atom's
`Qdiag_gv`-RHS via the landed `qdiag_bridge`: at fixed `(W',D)` with the
`D`-largeness hypotheses (below), `Qdiag_gv ≥ X⁶·J/2` for `R ≥ R₀(W')` and
`PAS⁶ ≤ C·X⁶` — net `(PAS+ε)²(2PAS)⁴ ≤ CF·Qdiag_gv`, `CF` F-only (the ratio
`→ 2⁶·2/J(F)`; W'-dependent approach absorbed in `R₀`). Requires (as
hypotheses, dischargeable at `primorial Dfin` for all large `Dfin`):
`hκ : (W':ℝ)/W'.totient ≤ 5·√D` (from `primorial_ratio_le`) and D-largeness
vs the (F-only, obtained-before-W') `qdiag_bridge` constant and `lemma53Const`
(`ε ≤ PAS` etc.) — executor latitude on the exact form, FROZEN REQUIREMENT:
every hypothesis must hold at `W' = primorial D` for ALL sufficiently large
`D` (Archimedes-compatible; no opaque-W'-linked-to-D constants).

**Endgame constants (verified numerically, scale-invariant; the landed
`yside_ge_cM` has `c = 60·Ical` but NC-3 re-bases on `mv_I_split` — the ratio
`(1/120)/Ical` governs):** S1 collision
constant `~ 12k²·Qabs²/(120·Ical(Fstar)) ≈ 9.4×10⁸` ⟹ `D ≥ 10¹³`; S2
`~ 48k²·2⁶·Qabs²/J(Fstar) ≈ 1.4×10¹³` ⟹ `D ≥ 7×10¹⁶`. **`Dfin ~ 10¹⁸`
covers both** — an ∃-witness, never computed (`primorial Dfin` symbolic);
`κ⁻¹ ≤ 5√Dfin`, `12k² ≤ Dfin` all hold. The ratio closes at ANY total
collision loss `< 7.5×10⁻⁴` and the `Dfin` choice makes it arbitrarily small.
The pigeonhole/frontier machinery is W'-generic, so instantiating at
`primorial Dfin` (instead of WinCore's numeral `Dstar`) is a re-thread, not
new analysis.

## Card NC-1 `Salt/Twelve/InnerS1.lean` — the S1 discharge — Opus, C
```lean
def S1InnerBoundM (k R W' : ℕ) (y : (Fin k → ℕ) → ℝ) (B : ℝ) : Prop :=
  -- the LHS |I(s,α)[y]| VERBATIM from S1InnerBound (CollisionQuantW.lean),
  -- with RHS  3 ^ s.primeFactors.card * (∏ p ∈ s.primeFactors, ((p:ℝ)-1)⁻¹^2) * B
  ∀ {s : ℕ}, Squarefree s → ∀ (α : (p : ℕ) → p ∈ s.primeFactors → Fin k × Fin k),
    α ∈ assignments k s → |/- I(s,α)[y] -/| ≤ 3 ^ s.primeFactors.card
      * (∏ p ∈ s.primeFactors, (((p:ℝ)-1)⁻¹)^2) * B

theorem s1_inner_bounded (k R W' : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ r, |y r| ≤ 1) (hy0 : ∀ r, r ∉ kSieveIndex k R W' → y r = 0) :
    S1InnerBoundM k R W' y
      (∑ r ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (r i) : ℝ))

theorem collision_lower_orderW_ofM (k R W' D : ℕ) (y : (Fin k → ℕ) → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hy0 : ∀ r, r ∉ kSieveIndex k R W' → y r = 0)
    (hInner : S1InnerBoundM k R W' y B)
    (hDlt : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) (hk : 1 ≤ k)
    (hDk : 12 * k ^ 2 ≤ D) :
    |s1CollisionForm k R W' y| ≤ 12 * (k:ℝ)^2 / D * B
```
Route: `s1_inner_bounded` = the termwise+partition proof above (the crux
proof of the closure; the partition/marked-reindex Finset work mirrors the
landed `hcompl`/`hpart`/`erase`-injection structure with the weight steps
REPLACED by `|y| ≤ 1` and the componentwise marked reindex — all on PUBLIC
machinery: `totient_lcm_split`, `lcm_split`, `assignments`, `slotProd`,
`mem_kSieveIndex_iff`). `collision_lower_orderW_ofM` = the `y`-generic
assembly of `collision_lower_orderW_of` with the RHS constant `B` threading
through the euler tail unchanged (NB-1's flagged "constant-B copy" — the
assembly is public+`y`-generic per NB-1's read). Corollary at `y = yF R W' F`,
`hQ : Qabs F ≤ 1` (via landed `yF_abs_le_Qabs`): `collision_yF_M :
|s1CollisionForm 5 R W' (yF R W' F)| ≤ 300/D · M`. Traps: the third-coordinate
contamination ⟹ join ∉ box ⟹ `y(join) = 0` (handle explicitly); a prime
divides `u` at ≤1 coordinate (pairwise-coprime box); the marked reindex needs
`p ∤ u'` (from squarefree `p·u'`). The TWO real proofs: `box_marked_moment`
(the 5-dim Q-marked moment, ~120 lines) and the contamination partition
(~150 lines mirroring `inner_abs_le`'s fiberwise `hpart` structure). PB floor:
if the partition balloons past ~500 lines, land `box_marked_moment` +
`S1InnerBoundM`+assembly and flag the partition step precisely.

## Card NC-2 `Salt/Twelve/InnerS2.lean` — the S2 discharge — Opus, C+
```lean
def S2InnerBoundQC (k R W' : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) (CF : ℝ) : Prop :=
  -- LHS verbatim from S2InnerBoundQ (S2Collision.lean:795); RHS gains the CF slot:
  ∀ {s : ℕ}, Squarefree s → ∀ α ∈ assignments k s,
    |/- S2 inner form -/| ≤ 3 ^ s.primeFactors.card
      * (∏ p ∈ s.primeFactors, (((p:ℝ)-2)⁻¹)^2) * CF * Qdiag_gv k R W' m y

theorem s2_inner_yF (F : Poly) (m : Fin 5) (hQ : Qabs F ≤ 1) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' → PhiUpperAtom W' →
      300 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ((W':ℝ)/W'.totient ≤ 5 * Real.sqrt D) →
      /- + D-largeness hyps vs the F-only qdiag_bridge/lemma53 constants;
         executor latitude, FROZEN REQUIREMENT: each must hold at
         W' = primorial D for all sufficiently large D -/
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        S2InnerBoundQC 5 R W' m (yF R W' F) CF

theorem s2_collision_le_QdiagW_C (k R W' D : ℕ) (m : Fin k) (y) (CF : ℝ)
    (hCF : 0 ≤ CF) (hInner : S2InnerBoundQC k R W' m y CF) (hyps…) :
    |s2CollisionForm k R W' m y| ≤ 48 * CF * (k:ℝ)^2 / D * Qdiag_gv k R W' m y
```
(`s2_collision_le_QdiagW_C` = the CF-slotted mirror of NB-3's landed
`s2_collision_le_QdiagW` — CF multiplies through the euler tail.) Route for
`s2_inner_yF`: the S2 termwise+partition proof above. Key landed inputs:
`lemma53_tightW` (B=1) for `|yM(w)| ≤ |Inn(w)| + ε` at each NONVANISHING join
`w` (needs `w ∈ kSieveIndex`, `wₘ=1` — the vanishing cases `V=0` handled
first); `absInn_le_pas` for `|Inn| ≤ PAS`; a MARKED generalization of `gmoment4_le`
(the landed one is the Q=∅ case only): `box_marked_gmoment` — `Σ_{u: uₘ=1,
p|u@slot ∀p∈Q} 1/∏_{i≠m}g(uᵢ) ≤ ∏_{p∈Q}(p−2)⁻¹·(2·PAS)⁴` (compose
`gmoment4_le`'s box→product structure with per-prime `marked_sqf_g_rel`
reindexes at the α-dependent slots — an explicit deliverable, ~100 lines); `qdiag_eq_yMsq_sum` for `Qdiag_gv = Σ yM²/∏g`; `qdiag_bridge` for
`Qdiag_gv ≥ X⁶J/2` at `R ≥ R₀` (obtain its `A` BEFORE `W'`); the atom
`3^ω`-budget absorbs the side-choice factors (the `(p−2)→(p−1)` conversion is NOT taken in the atom — see the TOTAL note above).
Traps: the `(PAS+ε)² ≤ 4PAS²` step needs `ε ≤ PAS` — from `hκ` + D-largeness
(`c₀κ⁻¹/D ≤ 1`); the `Mg₄` box is `uₘ=1` (4 free coords); σₘ≠1 ⟹ V=0.
PB floor: if the `Qdiag ≥ X⁶J/2` eventual-comparison fights, take it as an
explicit `∀ᶠ`-hypothesis and flag — but its proof is a direct read of
`qdiag_bridge` + `theta_ratio`-style positivity.

## Card NC-3 `Salt/Twelve/GapsFinal.lean` — the assembly — Opus, C+
The final node: `gaps_le_twelve (hPNT : WindowPNT) (hEH : EHall)` UNCONDITIONAL
(the FROZEN top-of-doc target). Structure: (1) obtain ALL constants BEFORE
choosing the modulus: `qdiag_bridge`'s `A` (F-only), NC-2's `CF`,
`lemma53Const`, and the `mv_I_split` `A`-constants (F-only, `∃A` BEFORE `W'`).
⚠️ BLOCKER FIX (adversarial pass): do NOT route the S1 conversion through the
landed `yside_ge_cM` — its `hD0` hypothesis carries the W'-OPAQUE `mvIErr`
(`~φ(W')` via the atom witness), unsatisfiable at `W' = primorial Dfin` for
EVERY `Dfin`. Instead base BOTH moments on the wave-4 relativized
**`mv_I_split`** (whose `1/D` bucket has F-only `A`): `M`-side at `onePoly`
(`M ≤ X⁵/120 + A₁(1+X+PAS)⁵/D + c_M(W')(1+X)⁵/logR`; `Ical onePoly = 1/120`,
`Qabs onePoly = 1`) and `yside`-side at `Fstar1`
(`yside ≥ X⁵·Ical − A_F(1+X+PAS)⁵/D − c(W')(1+X)⁵/logR`). At fixed `(W',D)`,
`R→∞`: the `1/logR` parts die, `(1+X+PAS)⁵ ~ 32X⁵`, so
`M/yside → (1/120 + 32A₁/D)/(Ical − 32A_F/D)` — F-ONLY, Archimedes-compatible.
The landed `yside_ge_cM` is NOT consumed by NC-3 (it remains a landed lemma;
its `mvIErr`-conditioned form is documented as unusable at primorial moduli). (2) **Archimedes:** `∃ Dfin` with: `12k² ≤
Dfin`, every NC-2 D-largeness hypothesis, NB-2's `hD0`, and the TOTAL
collision losses `[300/(c·Dfin)]·(S1) + [48·CF·25/Dfin]·(S2) + (qdiag κ-terms)
< the win_ratio margin-share` — each term explicit-or-F-only over `1/Dfin` or
`1/√Dfin`. (3) `W' := primorial Dfin`; discharge `Squarefree`/`hDlt`
(`primorial_hDlt`)/`hκ` (`primorial_ratio_le`)/`hν₀` (`exists_nu0W`)/
`PhiUpperAtom` (`phiUpperAtom_final`)/`hIcal` (`Ical_Fstar1_pos`). (4)
Re-thread the WinCore chain AT THE ABSTRACT `(Dfin, primorial Dfin)`. The
Dstar-numeral pins to mirror: `gaps_le_twelve_of_inner`, `WinFrontier`'s
`(1+12·5²/Dstar)` factor, `hSeq_lt_Dstar`, the `win_core'` instantiation.
GOOD NEWS: `win_ratio_core` ALREADY takes `eps` as a free real
(`hepsle : eps ≤ 1/100000`) — reuse directly with the assembled abstract eps
(no cert re-derivation). `sharp_S1_upperW`'s pattern runs with
`collision_yF_M` + the `mv_I_split`-based conversion (step 1) giving the
`(1 + [F-only]/Dfin)` factor; `S2mW_ge_compatMain_theta_uniform`,
`qdiag_bridge`, `winFrontier_of`'s conjunct-structure,
`bounded_gaps_reduces_twelve` are all W'-generic or re-instantiable. (5) Discharge the `WinSlack`/`hslackEv` quantitative
threading (W5-7 residual (a)): all vanishing errors below the margin at the
chosen constants — the `∀ᶠ N` stack. (6) `gaps_le_twelve := …` — matching the
frozen target EXACTLY. Traps: quantifier ORDER is everything — constants
before `Dfin`, `Dfin` before `W'`, thresholds inside `∀ᶠ N`; do NOT reuse the
`Dstar`-pinned `WinFrontier`/`gaps_le_twelve_of_inner` directly (mirror at the
abstract modulus); the `win_ratio` margin analysis needs the certified
`theta_ratio_cert_sharp` with the abstract-eps version. PB floor: land (1)–(3)
+ the S1-side re-thread + `gaps_le_twelve` with the S2/slack pieces as
explicit hypotheses if the full (4)–(5) balloons — then ONE follow-up
discharges them; flag precisely.

## Node C dependency DAG
```
NC-1 (S1 discharge) ──┐
NC-2 (S2 discharge) ──┼→ NC-3 GapsFinal → gaps_le_twelve (hPNT) (hEH)  — THE END
   (landed: yside_ge_cM, collision chains, qdiag_bridge, WinCore, frontier)
```
Round 1: NC-1, NC-2 parallel. Round 2: NC-3.

---

## Node B — CARDED (Fable design pass, 2026-07-11) — the CRUDE-domination route
**(SUPERSEDED by Node C above — the S1 crude-domination was proven a mirage by
NB-1's execution; kept as history. NB-2's `yside_ge_cM` and NB-3's landed
S2 infrastructure remain LIVE inputs to Node C.)**

**RESOLVED: the collision estimate needs NO Lipschitz smoothness.** The design
exploration (full read of `inner_abs_le`) found the crude route (b′): `yF` is
BOUNDED (`|yF R W' Fstar1 r| ≤ 1`, landed `yF_Fstar1_abs_le_one`), so
`|yF r| ≤ ONE r` where `ONE r := if r ∈ kSieveIndex 5 R W' then 1 else 0` is the
CONSTANT tensor (`f₀ ≡ 1`, a legal divisor-DECREASING tensor: `1 ≤ 1`). The
`μ`-sign-strip inside `inner_abs_le` makes the inner form MONOTONE in `|y|`
pointwise, so `inner_abs_le` applied to `ONE` bounds the `yF` form:
`|s1CollisionForm (yF)| ≤ 12k²/D · M`, `M := ∑_r 1/∏φ(rᵢ)` (the crude moment =
`yside` of `ONE`). Then `M ≤ (1/c)·yside` (`c = 120·Ical(Fstar1) = 120·1597/399168
≈ 0.480`) converts it to `≤ 12k²/(cD)·yside`. NUMERICS (verified): the collision
constant becomes `12·25/(c·Dstar) ≈ 2.08×10⁻⁵` (vs the tensor `10⁻⁵`); the ratio
`(θ★/2)M₅/(1+2.08×10⁻⁵) = 1.000736 > 1` — closes with margin `7.36×10⁻⁴` to
spare (bumping `Dstar` restores it fully). NO Lipschitz, NO new erasure, NO
`euler_tailW_log`. The erase-case residual worry was a MISDIAGNOSIS (the
`log/log R` normalization makes the erase shift uniform) — but the crude route
sidesteps it entirely anyway.

### NB-1 `Salt/Twelve/CollisionYF.lean` — `collision_yF_le` (S1 side) — Opus, B/C
```lean
def ONEw (R W' : ℕ) : (Fin 5 → ℕ) → ℝ := fun r => if r ∈ kSieveIndex 5 R W' then 1 else 0

theorem collision_yF_le (R W' D : ℕ) (F : Poly) (hQ : Qabs F ≤ 1)
    (hW' : Squarefree W') (hDlt : ∀ p, p.Prime → ¬p ∣ W' → D < p)
    (hDk : 12 * 5 ^ 2 ≤ D) :
    |s1CollisionForm 5 R W' (yF R W' F)|
      ≤ (12 * (5:ℝ)^2 / D) * ∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ)
```
Route (the domination is on the ABS-majorant `s1AbsCollisionForm`, NOT the signed
form — the `lam` weights carry `μ` signs so `s1AbsCollisionForm ONE ≠
s1CollisionForm ONE`): (i) **`collision_abs_ONE_le : s1AbsCollisionForm 5 R W' (ONEw)
≤ 12k²/D·M`** — this is what `inner_abs_le` at `f₀ ≡ 1` (`hf0 : 0 ≤ 1`, `hfmono :
1 ≤ 1`) + the `collision_lower_orderW` ASSEMBLY prove, since `inner_abs_le` and
the assembly go through the ABS forms (`∑_u ∏φ·|ŷ||ŷ|`). Extract an abs-conclusion
`collision_lower_orderW_of_abs : S1InnerBound … → s1AbsCollisionForm … ≤ 12k²/D·yside`
from the existing proof (its body already bounds the abs-majorant; the signed
`|s1CollisionForm|` is a downstream corollary via `s1CollisionForm_le_abs`).
`yside[ONE] = M`. (ii) **`|s1CollisionForm (yF F)| ≤ s1AbsCollisionForm (yF F) ≤
s1AbsCollisionForm ONEw`** — `s1CollisionForm_le_abs` (`|·| ≤` majorant) +
`s1AbsCollisionForm_mono` (`|y₁ r| ≤ |y₂ r| ∀r ⇒ s1AbsCollisionForm y₁ ≤
s1AbsCollisionForm y₂`, since `|lam y d| = ∏dᵢ·|wSum y d|` is monotone in `|y|`
via `|wSum y d| ≤ ∑|y_r|/∏φ`), and `|yF r| ≤ ONEw r` (`yF_abs_le_Qabs` + `hQ`;
off-box both 0). Chain (i)+(ii): `≤ 12k²/D·M`. Land `s1AbsCollisionForm_mono`,
`s1CollisionForm_le_abs`, `lam_abs_mono` (`|y₁|≤|y₂| ⇒ |lam y₁ d| ≤ |lam y₂ d|`).
PB floor: if extracting the abs-conclusion from `collision_lower_orderW_of` fights,
prove `collision_abs_ONE_le` directly by re-running the assembly (it's `y`-generic
and its inequalities are all on abs forms).

### NB-2 `Salt/Twelve/CollisionYF.lean` — `yside_ge_cM` — Opus, B/C
```lean
theorem yside_ge_cM (F : Poly) : ∃ c : ℝ, 0 < c ∧ ∀ W' D : ℕ, Squarefree W' →
    0 < W' → PhiUpperAtom W' → 3 ≤ D → (∀ p, p.Prime → ¬p ∣ W' → D < p) →
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
      c * (∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i):ℝ))
        ≤ ∑ r ∈ kSieveIndex 5 R W', (yF R W' F r)^2 / ∏ i, (Nat.totient (r i):ℝ)
```
Route: `yside = X⁵·Ical F ± mv_I err` (landed `mv_I`); `M = X⁵·simplexInt(1)
± err = X⁵/120 ± err` (`mv_I` at `F ≡ 1`, `simplexInt(sq(ofPoly 1)) = DInt'(0,0)
= 1/120`); ratio `→ 120·Ical F`. `c = 100·Ical F` (after absorbing `o(1)`);
`Ical_Fstar1_pos` (landed `WinCore.lean:127`). NEEDS `PhiUpperAtom` — discharge
it via the landed `phiUpperAtom_final` (W4-0, UNCONDITIONAL) so `yside_ge_cM` is
hypothesis-free at `Fstar1`. PB floor: none.

### NB-3 `Salt/Twelve/CollisionYF.lean` — S2 twin `collision_yF_le_S2` — Opus, C
The S2-side analog: `s2_collision_le_QdiagW` (`S2Collision.lean:808`, `y`-generic
modulo `S2InnerBoundQ`) — discharge `S2InnerBoundQ (yF)` by the SAME ONE-tensor
domination (`s2_inner_bound_N`'s `fTilde`-antitone step replaced by the `f₀≡1`
instance), giving `|Qdiag_mW − s2CompatFormM| ≤ (c₂k²/D)·M ≤ (c₂k²/(cD))·yside`.
This connects `S2mW_lower`'s compat bound to `qdiag_bridge`'s `Qdiag` (the
`hslackEv` residual (b) from W5-7). Traps: audit `s2_collision_le_QdiagW`'s exact
hyp shape; the `S2InnerBoundQ` Prop atom. PB floor: if the S2 split needs its own
`_of` refactor (like W5-1 did for S1), land that first.

### NB-4 `Salt/Twelve/GapsFinal.lean` — assemble UNCONDITIONAL `gaps_le_twelve` — Opus, C
Consumes NB-1/2/3 + the landed `gaps_le_twelve_of_inner`/`winFrontier_of`. (a)
Discharge `hInner`: `collision_yF_le` + `yside_ge_cM` give the S1 collision bound;
feed the sharp S1 (revise `sharp_S1_upperW` → factor `(1 + 12k²/(cD))`, an
INLINE endgame-verified constant change to `WinCore.lean` — ratio re-verified
`1.000736 > 1`). (b) Discharge `hslackEv` (W5-7's residual): NB-3 closes the S2
collision, then the vanishing-error threading (mechanical, per W5-7's flag)
closes `WinSlack`. (c) `winFrontier_holds := winFrontier_of hslackEv`. (d)
`gaps_le_twelve := gaps_le_twelve_of_inner hPNT hEH hInner winFrontier_holds` —
matching the FROZEN top-of-doc target `gaps_le_twelve (hPNT) (hEH) : ∀N ∃p q,
… ∈ Icc(-12,12)`. NB-4 is where the two atoms + slack land the unconditional
theorem. INLINE-authorized constant changes to `WinCore.lean` (the `300/Dstar →
12k²/(cD)` in `WinFrontier`/`sharp_S1_upperW`/`win_ratio_core`, all endgame-
verified: ratio `1.000736 > 1`, margin `7.36×10⁻⁴`) — bump `Dstar` if any
re-cert is tight. PB floor: land `hInner`-discharge (a) cleanly (that alone
removes the S1 collision hypothesis); if the S2/slack (b) fights, the result is
`gaps_le_twelve` conditional on ONLY the S2 collision — still a milestone; flag.

### Node B dependency DAG
```
NB-1 collision_yF_le ─┐
NB-2 yside_ge_cM ─────┼→ NB-4 GapsFinal (hInner discharge + assembly) → gaps_le_twelve
NB-3 S2 twin ─────────┘   (+ hslackEv discharge via NB-3 + vanishing errors)
```
Round 1: NB-1, NB-2, NB-3 parallel. Round 2: NB-4. This is the FINISH.

---

### Historical note (the Lipschitz route, superseded by the crude route above)

**SCOPE CORRECTION (W5-7 execution, 2026-07-10): the non-tensor collision
estimate is needed on BOTH sieve sides — it is ONE technique, TWO atoms.** The
wave-5 design under-scoped the S2 side as an "audit"; the W5-7 discharge showed
it is a full atom of the same shape as the S1 one:
- **S1 side — `S1InnerBound k R W' (yF R W' Fstar1)`** (Node A `collision_lower_orderW_of`,
  W5-1): the sharp S1 factor-2 kill.
- **S2 side — `S2InnerBoundQ`-for-`yF` / `s2_collision_le_QdiagW`** (`S2Collision.lean:795/808`):
  the `s2CompatFormM ↔ Qdiag_mW` passage (`Qdiag − s2CompatForm = s2CollisionForm`,
  needed to connect `S2mW_lower`'s compat-pairs bound to `qdiag_bridge`'s sharp
  `X⁶·Jcal`). Its landed discharge `s2_inner_bound_N` uses `fTilde`-antitonicity
  (tensor) — unusable for `yF`, exactly like Node A.
Both discharge via the SAME Lipschitz-smoothness restricted-diagonal contraction
(below). The S2 split (`s2_collision_le_Qdiag` + abstract `S2InnerBoundQ`) already
exists `y`-generic, so the S2 atom is a drop-in once the technique is designed.
Downstream, the quantitative slack `hslackEv` (W5-7's `winFrontier_of` residual
(a): thread the vanishing errors below `win_ratio_core`'s ~4.4×10⁻³ main-gap) is
MECHANICAL but BLOCKED on the S2 atom (its `errEH` carries the S2 collision) —
lands once both atoms do.

**The estimate (`S1InnerBound k R W' (yF R W' Fstar1)` and its S2 twin) — for the
divisor-INCREASING polynomial weight.** This is the last genuine mathematical
content of the rung (Maynard's singular-series smoothness / ε-enlargement
estimate). The landed monotone-tensor machinery
(`inner_abs_le`/`yhat_side_le`/`erase_branch`) is
UNUSABLE (wrong monotonicity direction). Design substrate for the dedicated pass:

- **The target.** For squarefree collision modulus `σ` (primes `> D`), the
  restricted double-sieve sum must contract by `∏_{p|σ}(p−1)⁻²` (TWO powers — both
  sieve variables `d,e` divisible by `p`) to feed `euler_tailW`'s convergent tail.
  For DECREASING `f₀≤1` this is `yhat_side_le` (`y(lcm) ≤ y(u)` + `φ(lcm)=∏(p−1)φ`).
- **The obstruction, precisely.** For INCREASING `yF`, `y(lcm) ≥ y(u)`, so the
  bound is backwards. BUT `yF_v = eval F(log v/log R)` is LIPSCHITZ in log-space:
  `|eval F(t+δ) − eval F(t)| ≤ L(F)·‖δ‖`, `L(F)` computable from `F`'s formal
  partial derivatives (`Qabs` of `∂F`). The shift from the σ-primes is
  `δ = log(σ-part)/log R`. KEY REGIME FACT: at fixed `D★`, `R→∞`, the dominant
  collision terms have `σ = O(1)` primes near `D★`, so `δ = log D★/log R → 0` —
  the contraction is `(p−1)⁻²·(1 + O(L·log p/log R))`, recovering the decay up to
  a VANISHING Lipschitz correction. The `(p−1)⁻²` survives; the correction is a
  new `1/log R`-side error term.
- **The open design questions (for the dedicated pass):** (a) does the `(p−1)⁻²`
  survive cleanly for ALL σ (incl. large-modulus σ where `δ = O(1)`), or does the
  large-modulus tail need a separate crude bound (weighted by the tiny
  `∏(p−1)⁻²`)? — the C-vs-D fork; (b) the exact form of the Lipschitz constant
  `L(F)` and whether `Fstar1`'s degree-≤3 / 56-monomial structure gives a clean
  bound; (c) does the argument need the full double-sieve Cauchy–Schwarz structure
  or a direct per-`σ` reindex? Recommend: a Fable design pass reads `inner_abs_le`
  in FULL, hand-derives the Lipschitz contraction with the small-modulus tail
  case split, and freezes `S1InnerBound`'s discharge as its own card set — THEN
  Opus executes. This is the highest-uncertainty node in the rung; do NOT rush it.
- **Fallback if Node B proves intractable:** the rung's `gaps_le_twelve` would
  remain conditional on `S1InnerBound (yF Fstar1)` as an explicit hypothesis (a
  narrow, TRUE, `∀ᶠ`-shaped analytic input — like `WindowPNT`/`EHall` already
  are), landing `gaps_le_twelve (hPNT) (hEH) (hInner)` — still a major result
  (explicit bounded gaps modulo one standard sieve estimate), with Node B as a
  documented PORT-BLOCKER. But the recommended path is to CLOSE it.

## Wave-5 dependency DAG
```
W5-4 primorial_ratio (Sonnet) ─┐
W5-2 EHtheta (Opus) ─┐         │
W5-3 herr (Opus) ────┼→ W5-6 win_core/gaps_le_twelve (Opus) ← W5-5 pigeonhole
W5-1 collision-split ┘   ↑
Node B (sub-wave) ───────┘  (discharges S1InnerBound for W5-1's collision bound)
```
Round 1: W5-1, W5-2, W5-3, W5-4, W5-5 in parallel (independent). Node B: its own
Fable design pass, then execution. Round 2: W5-6 (after Round 1 + Node B).
`s2_collision_le_QdiagW` audit (the `S2InnerBoundQ` compat↔full-form passage)
folds into W5-3 if needed.
