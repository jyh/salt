# S3-HB-R3 DESIGN — the ladder verdicts + the R3b freeze

**Status: FROZEN (house, 2026-07-18 ~02:10) — R3b PENDING GATE.**
Provenance: S3-HB3-R0 (the full-climb recon, ledger ~02:00 — the
authoritative annex; its §1/§4 ARE the R3a/R4 deliverables below).

## The ladder verdicts (adopted from the recon, house-ratified)

- **HB-R3a (the dispatcher box upgrade): DEAD-END, documented —
  DO NOT BUILD.** The √log x geometry is the de la Vallée Poussin
  optimum welded at three coupled points (the saving, the
  zero-free width c₀ = 1/126848, the truncation balance); a
  polynomial box degrades the saving to x²·e^{−c₀/θ} ≈ x²·1
  (c₀ five orders too small). Deeper: ψ₁ is parity-blind — the
  non-exceptional zeros contribute a constant fraction of x² at
  polynomial height; no contour statement isolates the exceptional
  zero without an arithmetic parity-break, which is the SIEVE's
  job. The recon's §1 is the negative-result record.
- **HB-R4 (beyond-level-½ error control): THE PREDICTED DEATH
  RUNG.** Heath-Brown needs level x^{1/2+δ}; the corpus's entire
  cancellation stack (char_LS Q²+13N, the bilinear shells, the
  dispersion BV) stops at level ½ exactly, Kloosterman/Weil is
  absent entirely, and the literature confirms HB requires
  nontrivial Kloosterman bounds. This is the SAME wall the corpus
  hits in Chen (TransposedBV), Maynard (GehTail), and the twin
  door — now confirmed as the Heath-Brown death rung. The wall-doc
  is the recon's §4.
- **HB-R3c (the χ-twisted sieve weight): the boundary-entry rung**
  — stratum-0 re-instantiation + the τ-weighted remainder are
  C-tier (~0.6–1.0M to a partial landing); node (a) (the signed
  twisted main term ↔ the L(1,χ) lower bound) is the D-locus and
  the likely death point. QUEUED behind R3b; dispatched only with
  budget to spare, in full knowledge of the expected death (a
  registered success under Amendment 3's acceptance rule).
- **HB-R5 (assembly): gated behind R4 — unreachable this sprint.**

## The R3b freeze — the correlation STATEMENT (SiegelCorrStrong)

The recon's wave-1 recommendation, adopted verbatim: refute the
silence branch by forcing the hypothesis's zero INTO the
dispatcher's box, then re-run the dispatcher's exceptional-case
template directly — no dichotomy, one conclusion.

File: Salt/TwinBar/SiegelCorrStrong.lean (imports
Salt.TwinBar.SiegelCorr + Salt.SW.ShiftVariants + what the case-iii
template needs; NO .All).

```lean
/-- The strong window: the correlation window PLUS the box-entry
    floor s = √log x ≥ 0.27/a (a = the dispatcher's c₄'-grade
    constant — the executor reads the landed value and pins the
    numeric floor accordingly; the recon's arithmetic at
    a ≈ 9.85e−7: s ≥ 2.74e5, x ≥ exp(7.5e10)). -/
def CorrWindowStrong (q : ℕ) (β x : ℝ) : Prop := ...

/-- THE CORRELATION STATEMENT (HB-R3b): under SiegelSequence, for
    every sufficiently small strength there are exceptional data
    such that at EVERY strong-window scale,
      ‖ψ₁(x,χ) + x^{β₁+1}/(β₁(β₁+1))‖ ≤ K₄·x²·e^{−c₄√log x}
    AND the residue ≥ x²/3 — ψ₁ is DEFINITIVELY large negative:
    the primes correlate with χ, no silence branch. -/
theorem siegel_correlation_strong (hSeq : SiegelSequence) : ...
```

Binding notes (recon-verified): the non-emptiness arithmetic
(c ≤ 2.6e−12 grade; the ∀c∃ order preserved; the numeric check
IN the design record: floor exp(7.5e10) ≤ cap exp(1.57e11·(log q)²)
✓); the β₁-into-box lemma (1−β₁ ≤ 0.4055/s² ≤ 3a/(2s) at the
strong floor); the case-iii template re-run
(psi1_contour_shift_exceptional + landau_one_exceptional_at +
E_shape_bound + residue_lower — all landed). Est. 300–450k,
6–10 nodes, ONE executor after the gate.

## Gate charge (S3-HB3B-GATE)

1. Independently REDO the recon's non-emptiness and box-entry
   arithmetic at the LANDED dispatcher constants (read c₄'/a from
   CharDispatch.lean's proof — the recon read a ≈ 9.85e−7;
   verify) — the HB2 self-refutation precedent makes this the
   kill-check.
2. Trace the case-iii template (CharDispatch L435–532): every
   hypothesis it consumes must be derivable in the strong window
   from SiegelSequence's data (the hzfexc zero-freeness, the box
   membership, T = e^{√log x} constraints) — list each with its
   source.
3. Elaboration probes: the strong-window def + the headline
   statement against the landed SiegelCorr/ShiftVariants.
4. Quantifier order (∃c₄K₄ outermost; ∀c-with-a-ceiling — the
   "sufficiently small strength" shape must not invert).
5. R4: the conclusion stays conditional-correlation (NOT twins);
   the docstring carries the R4/R5 gating and the death-map
   pointers.

---

## GATE VERDICT — S3-HB3B-GATE (2026-07-16)

**VERDICT: GO-WITH-BLOCK.** The R3b construction is STRUCTURALLY SOUND
(force the Siegel zero into the dispatcher's box; re-run the case-iii
template; drop the silence disjunct). Non-emptiness holds end-to-end and
every case-iii hypothesis is derivable in the strong window. BUT the
freeze's schematic window is under-parametrized, and the binding note's
instruction to "pin the numeric floor" from the landed `a` is **UNSOUND**
(the HB2 failure mode is latent in the recon's own numbers). The frozen
block below replaces the schematic def/statement with the honest,
`c₄`-parametrized versions — both elaborated clean against the landed
layer. Build the block AS WRITTEN; do not pin numerals for the box floor.

### Charge 1 — arithmetic REDONE at the landed constants

The dispatcher's constant chain (CharDispatch L336–395), traced verbatim:
`c₀` from `zero_free_region_all` (witness `1/126848`, ZeroFreeReal L392),
`c₃` from `zeta_zero_free_region` (witness `min (1/75712) (ε₀·log 2)`,
ZetaZeroFree L239 — **`ε₀` is OPAQUE**, from `zeta_zero_free_strip`),
`c₀' = min (min c₀ c₃) (1/3750)`, `a = c₀'/8`, `c₄ = a/2` (so **`a = 2c₄`**).
Box left edge (L450): `σ₀ − w = 1 − 3a/(2s)`, `s = √log x`. So **box entry
is `1 − β₁ ≤ 3a/(2s) = 3c₄/s`** (machine-checked, Algebra probe).

*Recon's `a ≈ 9.85e−7` reproduced* — but only IF `c₀' = c₀`, i.e. IF
`c₃ ≥ c₀`. Since `1/75712 ≈ 1.32e−5 > c₀ ≈ 7.88e−6` but `ε₀·log 2` is
opaque, **`c₀'`, hence `a`, is NOT a provable literal to any consumer**
(both `c₀` and `c₃` are existentially hidden). The recon's `2.6e−12` is the
*crossover* ceiling (δ = 9a²/(4log(3/2)) = 5.39e−12, s = 0.27/a = 2.74e5,
c ≤ (log2)²·δ = 2.59e−12) — all reproduced — but it is loose by ~25000×:
the honest floor-based ceiling is **`c ≤ 0.134·c₄ ≈ 6.6e−8`**.

**KILL-CHECK RESULT (the HB2 precedent): the recon's PINNED window
self-refutes.** Its floor `exp((0.27/a)²)` vs cap `exp(1.57e11·(log q)²)`
has a **0.47 % margin at q = 2** (floor 7.508e10 ≤ cap 7.543e10). If the
true `a` is merely **0.7×** the assumed value — which `c₃ = min(…,ε₀log2)`
permits, `ε₀` being unknown — the floor jumps to 1.53e11 > cap: **window
EMPTY, theorem vacuous.** A pinned-numeric window is therefore forbidden.
The frozen block parametrizes the box floor by the exposed `c₄`; its
floor-point non-emptiness margin `30Q² − 4(Q+2) = 3.64 > 0` is
**`c₄`-independent** (holds for any `c₄ > 0`). Non-emptiness SURVIVES.

### Charge 2 — case-iii template: every hypothesis sourced

`psi1_contour_shift_exceptional` (ShiftVariants L230–236) + the surrounding
assembly (CharDispatch L436–532) consume, in the strong window (sources):

| hypothesis | source in strong window |
|---|---|
| `χ`, `NeZero q`, `hf : 2 ≤ f`, `hχ` primitive | SiegelSequence data (`q>1 ⟹ q≥2`) |
| `hx : 3 ≤ x` | `corrWindow_box.1` (from CorrWindow floor) |
| `hT : 2 ≤ T`, `T = exp(√log x)` | `s ≥ 1` ⟹ `exp s ≥ e ≥ 2` |
| `hw : 0 < w` | `w = a/(2s) > 0` |
| **box entry `σ₀ − w ≤ β₁`** | **CorrWindowStrong clause `1−β₁ ≤ 3c₄/s`** (the ONE new input) |
| `hβ1_ge : 1 − 3w ≤ β₁` (L472) | = box entry (`σ₀−w = 1−3w`) |
| `hβ90 : 9/10 ≤ β₁` (L464) | box entry + `hσ₀w` (`9/10 ≤ σ₀−w`) |
| `hβwin` Landau window (L475) | `hβ1_ge` + `hlog4q_le` arithmetic (verbatim) |
| `hsimple` order = 1 (L481) | `landau_one_exceptional_at` @ `hβwin` |
| `σ₀''`, `hσ''w/1/βsep/lo/dec` (L484–494) | `hβ1_ge` + `hw_bound` (verbatim) |
| `hzfexc` (L496–526) | `dispatch_zero_re_le` + `landau_one_exceptional_at` (verbatim) |
| final `hE` collapse (L529–532) | `E_shape_bound` @ `hσ''lo/dec`, `hB0/Bs` (verbatim) |

**Conclusion:** the ONLY ingredient the dispatcher got "for free" from its
`by_cases hbox` that the strong statement must SUPPLY is box entry
`σ₀ − w ≤ β₁`; it comes from the added window clause. Everything L454–532 is
a verbatim re-run with `β₁` = the Siegel zero. No orphan hypothesis. Because
`psi1_char_bound`'s clean disjunct is a bound (not "hbox false"), it cannot
be refuted as a black box — the executor must re-derive the case-iii block
(copy L336–532, or factor a `…_forced_exceptional` lemma threading `c₄`);
either lands the STATEMENT. No RE-CUT needed.

### Charge 3 — elaboration probes: PASS (frozen statements below)

`CorrWindowStrong` + `siegel_correlation_strong` (with the non-emptiness
witness conjunct) elaborate clean against `Salt.TwinBar.SiegelCorr` +
`Salt.SW.ShiftVariants` (only the expected `sorry` warning). The box-entry
reduction `1−β ≤ 3c₄/s ⟹ 1 − 3(2c₄)/(2s) ≤ β` is kernel-checked.

### Charge 4 — quantifier order: HONEST, no inversion

`∃ c₄ K₄` OUTERMOST (universal dispatcher constants) `∧ ∀ c > 0, ∃ (q,χ,β₁)`
(for every strength, exceptional data EXIST — the honest ∀∃, never ∃∀)
`∧ ∀ x, CorrWindowStrong c₄ q β₁ x → concl`. The "sufficiently small
strength" is the **witness-absorbing** shape (matches
`siegel_correlation_dichotomy`, SiegelCorr L197–201): invoke `hSeq` at
`min c (c₄/10)`; the delivered `(1−β₁)(log q)² < min c (c₄/10) ≤ c` still
gives the stated `< c`. No external ceiling on `c`; no ∃∀ inversion. The
`CorrWindowStrong`-hypothesis being non-vacuous is guarded IN-KERNEL by the
witness conjunct (no `badHyp_false` trap).

### Charge 5 — R4 framing: conditional-correlation only

Conclusion is `SiegelSequence → (x in strong window → ψ₁ ≈ −residue,
residue ≥ x²/3)`. NO twin claim; `SiegelSequence` is a (strictly-stronger-
than-textbook, squared-log) HYPOTHESIS. Docstring MUST carry: the R4 death
rung (beyond-½ error control — the confirmed wall; §HB-R4 above), R5 gated
behind R4 (unreachable), the R3a dead-end and R3c likely-death pointers,
and the SiegelCorr honesty block (strictly-stronger input; one-way bridge;
no branch smuggled — the domain restriction to the box-entry band is
EXPLICIT in `CorrWindowStrong`, not a selection).

---

## THE FROZEN BLOCK (verbatim-ready — build AS WRITTEN)

File: `Salt/TwinBar/SiegelCorrStrong.lean` (imports `Salt.TwinBar.SiegelCorr`
+ `Salt.SW.ShiftVariants`; NO `.All`).

```lean
/-- **The strong window.** `CorrWindow` (floor `x ≥ exp(16(log q+2)²)` +
    residue cap `(1−β)log x ≤ log(3/2)`) PLUS the box-entry clause
    `1 − β ≤ 3·c₄/√log x`. The last encodes the dispatcher's box membership
    `σ₀ − w ≤ β` exactly: `σ₀ − w = 1 − 3a/(2s)`, `a = 2c₄`, `s = √log x`,
    so `3a/(2s) = 3c₄/s`. `c₄` is the EXPOSED dispatcher constant (never a
    pinned numeral — `a` is opaque behind two existentials; pinning it is
    the HB2 self-refutation, see gate Charge 1). -/
def CorrWindowStrong (c₄ : ℝ) (q : ℕ) (β x : ℝ) : Prop :=
  CorrWindow q β x ∧ (1 - β) ≤ 3 * c₄ / Real.sqrt (Real.log x)

/-- **THE CORRELATION STATEMENT (HB-R3b).** Under `SiegelSequence`: there are
    universal dispatcher constants `c₄, K₄ > 0` such that for every strength
    `c` there exist exceptional data `(q, χ, β₁)` with `(1−β₁)(log q)² < c`,
    for which (i) the strong window is INHABITED at the floor scale
    `x₀ = exp(16(log q+2)²)` — the in-kernel anti-vacuity guard — and (ii) at
    EVERY strong-window scale `x`, `ψ₁(x,χ)` is DEFINITIVELY large-negative:
    `‖ψ₁ + x^{β₁+1}/(β₁(β₁+1))‖ ≤ K₄ x² e^{−c₄√log x}` while the residue is
    `≥ x²/3`. No silence disjunct — the domain restriction to the box-entry
    band (the `CorrWindowStrong` clause) is what forces the correlation.

    NOT a twin claim. `SiegelSequence` is a (squared-log, strictly-stronger-
    than-textbook) HYPOTHESIS; this rung selects the correlation branch only
    on the box-entry band. Death map: R3a (box upgrade) DEAD-END; R4
    (beyond-level-½ / Kloosterman) THE PREDICTED DEATH RUNG; R5 (assembly)
    gated behind R4, unreachable; R3c (χ-twisted sieve) the boundary-entry
    rung with its own likely death. See `docs/exploration/s3-hb3-design.md`
    and the `SiegelCorr` honesty block (one-way bridge; no branch smuggled). -/
theorem siegel_correlation_strong (hSeq : SiegelSequence) :
    ∃ c₄ K₄ : ℝ, 0 < c₄ ∧ 0 < K₄ ∧
      ∀ c : ℝ, 0 < c → ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q) (β₁ : ℝ),
        1 < q ∧ χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
        LFunction χ (β₁ : ℂ) = 0 ∧ (1 - β₁) * (Real.log q) ^ 2 < c ∧ β₁ < 1 ∧
        CorrWindowStrong c₄ q β₁ (Real.exp (16 * (Real.log (q : ℝ) + 2) ^ 2)) ∧
        ∀ x : ℝ, CorrWindowStrong c₄ q β₁ x →
          x ^ 2 / 3 ≤ ‖(x : ℂ) ^ ((β₁ : ℂ) + 1) / ((β₁ : ℂ) * ((β₁ : ℂ) + 1))‖ ∧
          ‖psi1Chi x χ + (x : ℂ) ^ ((β₁ : ℂ) + 1) / ((β₁ : ℂ) * ((β₁ : ℂ) + 1))‖
              ≤ K₄ * x ^ 2 * Real.exp (-(c₄ * Real.sqrt (Real.log x))) := by
  sorry
```

**Binding implementation notes (gate-verified):**
1. `c₄, K₄` come from re-deriving the dispatcher head (obtain `c₀`,`c₃`; set
   `c₀'`,`a = c₀'/8`, `c₄ = a/2`; `E_shape_bound` for `K₄`) — the strong
   proof re-runs CharDispatch L336–532, NOT a black-box `psi1_char_bound`
   call (its clean disjunct is unrefutable externally).
2. Invoke `hSeq` at **`min c (c₄/10)`**. Non-emptiness of the witness
   conjunct at `x₀ = exp(16(log q+2)²)` then holds with `c₄`-INDEPENDENT
   box-entry margin (`30(log q)² ≥ 4(log q+2)` for `q ≥ 2`, i.e.
   `30Q² − 4Q − 8 ≥ 0` at `Q ≥ log 2`) and residue-cap margin from
   `c₄ ≤ 1/60000` (provable: `a ≤ 1/30000`). Box entry at `x₀`:
   `δ < c₄/(10Q²) ≤ 3c₄/(4(Q+2))`. Residue at `x₀`:
   `δ·16(Q+2)² ≤ log(3/2)` from `c₄ ≤ 0.253 Q²/(Q+2)²`.
3. `residue ≥ x²/3` clause: `residue_lower h90 hβ1 hwin` (`h90` from box
   entry + `hσ₀w`; `hwin = CorrWindowStrong.1`). Box constraint
   `log(q(T+4)) ≤ 2√log x`: `corrWindow_box`.
4. Box-entry discharge: `1−β₁ ≤ 3c₄/s` ⟹ `σ₀ − w ≤ β₁` via `a = 2c₄`,
   `3(2c₄)/(2s) = 3c₄/s` (kernel-checked).

**Est.** unchanged (300–450k, 6–10 nodes); ONE executor after this gate.

---

# HB-R3c DESIGN FREEZE — the χ-twisted sieve weight (house, 2026-07-18)

**Status: FROZEN (house). R3c is the DELIBERATE BOUNDARY-ENTRY rung —
dispatched in full knowledge of the expected death at node (a3), a
registered success either way under Amendment 3.** Provenance: HB3-R0 §3
(the substrate survey, pilot ~02:00), R3b landed (siegel_correlation_strong,
pilot ~05:20), this pass's proof-level re-verification + one clean
elaboration probe against the landed layer, + Tao's exposition of
Heath-Brown 1983 (the (a3) adjudication, WebFetch 2026-07-18).

Target file: `Salt/TwinBar/TwistedSieve.lean` (imports `Salt.Chen.LinearSieve`
for the `BoundingSieve`/`TruncSieve` API + `Salt.TwinBar.SiegelCorrStrong` for
`psi1Chi`/`SiegelSequence`/the R3b correlation; NO `.All`).

## §0 — THE SUBSTRATE VERDICT (recon §3, re-confirmed at PROOF level)

`BoundingSieve` (mathlib, `#print`-verified this pass) carries exactly:
`support : Finset ℕ`, `prodPrimes : ℕ` (`+ prodPrimes_squarefree`),
`weights : ℕ → ℝ` (`+ weights_nonneg`), `totalMass : ℝ`,
`nu : ArithmeticFunction ℝ` (`+ nu_mult`, `+ nu_pos_of_prime`,
`+ nu_lt_one_of_prime`). Derived (all `#print`-verified):
`siftedSum = Σ_{d ∈ support, P⊥d} weights d`;
`mainSum muPlus = Σ_{d ∣ P} muPlus(d)·ν(d)`;
`errSum muPlus = Σ_{d ∣ P} |muPlus(d)|·|rem(d)|`;
`rem d = multSum d − ν(d)·totalMass`.

**Re-instantiation is INADMISSIBLE — confirmed, four ways.** The twist
`λ_χ = (χ_ℝ ∗ 1)` violates: (1) `weights_nonneg` (the character-signed sift is
signed); (2) `nu_pos_of_prime` AND `nu_lt_one_of_prime` (any ν built to carry
the χ-sign is signed / can exceed 1 — the positivity that the corpus's
`nuChen = 1/φ` gets ANALYTICALLY is here COMBINATORIAL, the recon's headline);
(3) `abs_lam_le_one` (`LinearSieve.lean:144`) — `|λ_χ(d)| ≤ τ(d)`, NOT `≤ 1`;
(4) `TruncSieve.isLowerMoebius` — λ_χ is not a Möbius truncation `μ·[P]`, so
the whole `linear_sieve_lower` (`LinearSieve.lean:349`) closure is unavailable.

**THE REUSE SEAM (this pass's sharpening of the recon).** `mainSum`/`errSum`
are `(ℕ → ℝ) → ℝ`, i.e. **WEIGHT-GENERIC**. So the twisted main/error sums are
NOT new bookkeeping — they are the abstract combinators AT the signed weight,
on any LANDED `BoundingSieve s` (the twin/Chen carriers reuse verbatim):
`twistedMainSum s χ := s.mainSum (lamChi χ)`,
`twistedErrSum s χ := s.errSum (lamChi χ)` (both elaborate clean, this pass).
**The obstruction is therefore NOT the stratum-0 bookkeeping (free) but the
two DOWNSTREAM consumers**: `errSum_lam_le` (`LinearSieve.lean:313`, consumes
`abs_lam_le_one`) → node (b) re-derive with `τ(d)` for `1`; and
`linear_sieve_lower` (consumes `abs_lam_le_one` + `isLowerMoebius`) → node (c)
re-derive for the signed weight. This re-scopes "stratum-0 re-instantiation"
DOWN from a full mirror to two lemma re-derivations. C-tier stands.

## §1 — THE TWISTED WEIGHT AS A LEAN OBJECT (FROZEN VERBATIM — probe-clean)

```lean
/-- The real quadratic-character value `χ_ℝ(n) = Re χ(n) ∈ {−1,0,1}` (χ real,
    `χ² = 1`). Real-valued so the sieve weight lives in `ℝ` (the abstract
    `mainSum`/`errSum` are `ℝ`-valued). -/
noncomputable def chiRe {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  (χ (n : ZMod q)).re

/-- **The χ-twisted sieve weight** `λ_χ(d) = (χ_ℝ ∗ 1)(d) = Σ_{e∣d} χ_ℝ(e)`.
    Multiplicative (χ_ℝ ∗ 1 is a convolution of multiplicative functions),
    SIGNED, and τ-bounded — `|λ_χ(d)| ≤ τ(d)`, NEVER `≤ 1`. This is the object
    that CANNOT be a `BoundingSieve.weights` (signed) nor a `TruncSieve.lam`
    (`|·| ≤ 1` fails); it lives OUTSIDE both structures. -/
noncomputable def lamChi {q : ℕ} (χ : DirichletCharacter ℂ q) (d : ℕ) : ℝ :=
  ∑ e ∈ d.divisors, chiRe χ e

/-- **The twisted main sum** `M_χ(s) = Σ_{d ∣ P} λ_χ(d)·ν(d)` — the abstract
    `mainSum` AT the signed weight (weight-generic reuse; no new bookkeeping). -/
noncomputable def twistedMainSum {q : ℕ}
    (s : BoundingSieve) (χ : DirichletCharacter ℂ q) : ℝ :=
  s.mainSum (lamChi χ)

/-- **The twisted error sum** `E_χ(s) = Σ_{d ∣ P} |λ_χ(d)|·|rem(d)|` — the
    abstract `errSum` AT the signed weight (the τ-weighted remainder, node b). -/
noncomputable def twistedErrSum {q : ℕ}
    (s : BoundingSieve) (χ : DirichletCharacter ℂ q) : ℝ :=
  s.errSum (lamChi χ)
```

**Node R3c-1 (the defs + multiplicativity).** Class **B**. Also frozen for this
node: `lamChi_mult : (fun d => lamChi χ d).IsMultiplicative`-shape (χ_ℝ mult ×
`1` mult, via mathlib `ArithmeticFunction.IsMultiplicative.mul`/convolution) —
the load-bearing input to (a1). Est. 60–100k.

## §2 — NODE (b): THE τ-WEIGHTED REMAINDER (C-tier, FROZEN)

```lean
/-- **(b.1)** `|λ_χ(d)| ≤ τ(d)`. `|Σ_{e∣d} χ_ℝ(e)| ≤ Σ_{e∣d} |χ_ℝ(e)| ≤
    Σ_{e∣d} 1 = τ(d)` (triangle + `|Re χ| ≤ ‖χ‖ ≤ 1`). The signed-weight
    replacement for `abs_lam_le_one`. -/
lemma abs_lamChi_le_tau {q : ℕ} (χ : DirichletCharacter ℂ q) (d : ℕ) :
    |lamChi χ d| ≤ (d.divisors.card : ℝ)

/-- **(b.2)** `E_χ(s) ≤ Σ_{d∣P, d<bound} τ(d)·|rem(d)|` — the τ-weighted Rosser
    remainder, the signed analogue of `errSum_lam_le` (`LinearSieve.lean:313`),
    `τ(d)` replacing the `1`. λ_χ is supported on ALL of `divisors P` (unlike
    the Rosser truncation), so the support hypothesis is only the level cap. -/
lemma twistedErrSum_le_tauRemainder {q : ℕ}
    (s : BoundingSieve) (χ : DirichletCharacter ℂ q) {bound : ℝ}
    (hsupp : ∀ d, d ∣ s.prodPrimes → (d : ℝ) < bound) :
    twistedErrSum s χ ≤ ∑ d ∈ s.prodPrimes.divisors,
      if (d : ℝ) < bound then (d.divisors.card : ℝ) * |s.rem d| else 0
```

(b.1) is class **B** (pure triangle inequality on a divisor sum). (b.2) is class
**B/C** (a mirror of `errSum_lam_le`, replacing the `S.abs_lam_le_one d` call by
`abs_lamChi_le_tau χ d`, and dropping the Rosser-support restriction since λ_χ
is full-support). **The genuinely C-tier sub-item is NOT frozen as a required
node**: the *analytic* control `Σ_{d<D} τ(d)·|rem(d)| = o(main)` at the sieve
level `D`. That is a τ-weighted Bombieri–Vinogradov statement; the corpus's
`char_LS` (Q²+13N) covers τ-weighted sums to level ½ (recon §3), so **(b) lands
to level ½ as C-tier** and this rung STOPS there for the error side — pushing the
error past ½ is exactly R4 (the Kloosterman wall, the documented death rung). The
freeze records level ½ as the (b) ceiling and does NOT budget beyond-½ error
control (unreachable this sprint). Est. 150–250k for (b.1)+(b.2)+the level-½
packaging.

## §3 — NODE (c): THE ASSEMBLY ALGEBRA (SCHEMATIC + gate charges)

The signed-weight analogue of `linear_sieve_lower`: from the twisted main lower
bound (a3) and the τ-remainder (b), a lower bound on the χ-detected sifted count.
Schematic shape:

```lean
-- SCHEMATIC. The signed linear-sieve lower assembly. NOT reusable from
-- `linear_sieve_lower` (that consumes `isLowerMoebius` + `abs_lam_le_one`,
-- both false for λ_χ); RE-DERIVED off the Buchstab/`siftedSum_ge_*` identity
-- with the signed weight inserted directly.
theorem twisted_sieve_lower {q : ℕ} (s : BoundingSieve) (χ : DirichletCharacter ℂ q)
    {bound mainBound : ℝ}
    (htm : 0 ≤ s.totalMass)
    (hmain : mainBound ≤ twistedMainSum s χ)        -- from (a3)
    (herr  : twistedErrSum s χ ≤ …) :               -- from (b)
    s.totalMass * mainBound - (τ-remainder) ≤ (χ-detected sifted count) := …
```

**Gate charge (c):** the *sign-flow* audit. `linear_sieve_lower`'s lower bound
rides on `siftedSum_ge_mainSum_errSum_of_lowerMoebius` (the Möbius-truncation
sign lemma). λ_χ has NO single peel-sign — its lower-sieve validity comes from
`(χ_ℝ ∗ 1) ≥ 0` on prime powers being FALSE in general; the correct route is the
**Selberg-diagonalized / fundamental-lemma** framing where λ_χ enters as a
DENSITY twist `ν → ν·(1+χ)`, not as a truncation sign. The executor MUST decide
placement (density-twist vs weight-twist) at node (c) design time — this is
flagged as a gate sub-charge, NOT frozen, because it interacts with whether the
main term is `Σλ_χ ν` (weight) or a twisted-ν sieve. **Class C, gated behind (a).
Likely never reached this sprint (a3 dies first).**

## §4 — NODE (a): THE D-LOCUS, FROZEN AS A LADDER

### (a1) — the Euler-product identity (FROZEN VERBATIM — probe-clean)

```lean
/-- **(a1)** Since `P` is squarefree, `d ∣ P` ranges over squarefree `d`, and
    `λ_χ(d)·ν(d)` is multiplicative, so the twisted main sum FACTORS:
    `Σ_{d∣P} λ_χ(d)·ν(d) = ∏_{p∣P} (1 + λ_χ(p)·ν(p)) = ∏_{p∣P} (1 + (1+χ_ℝ(p))·ν(p))`
    (using `λ_χ(p) = χ_ℝ(1)+χ_ℝ(p) = 1 + χ_ℝ(p)` at a prime). -/
lemma twistedMainSum_euler {q : ℕ} (s : BoundingSieve) (χ : DirichletCharacter ℂ q) :
    twistedMainSum s χ
      = ∏ p ∈ s.prodPrimes.primeFactors, (1 + (1 + chiRe χ p) * s.nu p)
```

Class **C** (mathlib route: `ArithmeticFunction.IsMultiplicative.map_prod` /
`Nat.sum_divisors_eq_prod_..` over `Squarefree`; `s.nu_mult` + `lamChi_mult`).
**THE STRUCTURAL WITNESS (load-bearing for (a3)):** the local factor is
`(1 + (1+χ_ℝ(p))·ν(p))`, so **when `χ(p) = −1` the factor is exactly `1`** and
**when `χ(p) = +1` it is `(1 + 2ν(p))`**. Hence
`twistedMainSum s χ = ∏_{p∣P, χ(p)=1}(1 + 2ν(p))` — a product over the SPARSE
`{χ = +1}` primes. This IS the mechanism the Siegel zero exploits AND the source
of the (a3) difficulty (below). Est. 150–250k.

### (a2) — the L(1,χ)-singular-series identification (SCHEMATIC)

The finite product `∏_{p∣P, p<z}(1+(1+χ_ℝ(p))ν(p))` ↔ the infinite
`∏_p(1−χ(p)/p)^{-1} = L(1,χ)` times the ordinary twin singular series, as
`z → ∞`. Requires a twisted-Mertens tail estimate (finite-to-infinite passage).
Class **C/D** — the tail is the analytic seam; NOT the death, but non-trivial.

### (a3) — THE LOWER BOUND (the D-locus) — ADJUDICATED, BOTH READINGS FROZEN

```lean
-- SCHEMATIC — THE D-LOCUS, the expected death.
theorem twistedMainSum_lower {q : ℕ} [NeZero q]
    (s : BoundingSieve) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hχ1 : χ ≠ 1) (hz : … sieve range …) :
    ∃ cLow : ℝ, 0 < cLow ∧ cLow * (LFunction χ 1).re ≤ twistedMainSum s χ := …
```

**THE ADJUDICATION (Tao's HB-1983 exposition, WebFetch, decisive).**

- **Reading A (the "L(1,χ) lower bound" reading — CORRECT, per Tao).** HB's
  argument REQUIRES `L(1,χ) ≫ q^{−O(1)}` (Tao's (8)); it is the constant factor
  multiplying the main asymptotic of the twisted Dirichlet sum
  (`Σ_{n≤x}(1∗χ)(n)/n^β = x^{1−β}/(1−β)·L(1,χ) + O(…)`, Tao's (9)); **without the
  lower bound the main term COLLAPSES and the twin lower bound is not positive.**
  The direction is genuinely the LOWER bound — a positive floor on L(1,χ).

- **Reading B (the "smallness is the friend" reading — REFUTED, per Tao).** The
  task's hypothesis (SiegelClose's landed UPPER bound
  `(L(1,χ)).re ≤ (1−β)·25e(1+log f)²`, `SiegelClose.lean:461`, i.e. L(1,χ) SMALL
  under the zero) does **NOT** invert to help the main term. Tao is explicit: the
  smallness enters only INDIRECTLY, via **Lemma 5** (`Σ_{p: χ(p)≠−1} 1/p = o(1)`
  — the zero forces `χ(p) = −1` for a density-1 set of small primes), which acts
  on the sieve *density* through the `(1−χ(p)/p) = (1+1/p)` factors (raising the
  density, beating parity). The main-term POSITIVITY still needs the lower bound.
  **So the frozen (a3) is the LOWER bound; SiegelClose's upper bound must NOT be
  smuggled in with a flipped sign** (a gate kill-check, §5).

- **THE COMBINED VERDICT (this pass).** The D-locus is CONFIRMED at (a3) but
  RE-PRECISED. It is **not** that `L(1,χ) ≫ q^{−O(1)}` is unprovable — the corpus
  has landed a Goldfeld-type EFFECTIVE lower bound `siegel_L_one_lower_near`
  (`SiegelClose.lean:582`), and Dirichlet's `L(1,χ) ≫ q^{−1/2}` is effective and
  suffices for `q^{−O(1)}`. **The genuine D-difficulty is the CONJUNCTION** of:
  (i) `siegel_L_one_lower_near` requires a DISTINCT target character
  (`hdist : χ₁ ≠ χ`, the Goldfeld/Deuring–Heilbronn mechanism) — but HB's χ IS the
  exceptional character itself, so the landed lemma does **not** apply to the
  self-same χ, and the self-character lower bound is Dirichlet's √q floor, which
  is where the finite-product-to-L(1,χ) bridge (a2) must land its constant; AND
  (ii) the lower bound is only LOAD-BEARING if the τ-error (b) is dominated by
  the main term, and at the `{χ=+1}`-sparse product of (a1) the main term is
  itself `q^{−O(1)}`-small, so the domination margin re-collides with the
  beyond-½ / Kloosterman wall (R4). **Net: (a3) is D — expected death — with the
  death re-attributed away from "L(1,χ) is ineffective" (it is NOT, largely
  landed) toward "the sparse twisted main term cannot be shown to dominate the
  τ-error without R4-grade distribution."** This is the honest map; the executor
  budgets (a1)+(b)+(a2)-tail and DECLARES (a3) at the collision, per Amendment 3.

**Outcome classes for (a3):** (O1) full lower bound lands off Dirichlet's √q
floor + an (a2) tail small enough that the sparse product still dominates — the
SUCCESS branch (unlikely; would be a genuine advance); (O2) the lower bound is
proved but VACUOUS at the sieve level (τ-error not dominated) — the EXPECTED
death, registered as an obstruction note pinning the R4 collision; (O3) the (a2)
tail itself prices D — recorded as a distinct sub-obstruction. All three are
registered successes under Amendment 3's acceptance rule.

## §5 — CASE SPACE (III.3‴), WITNESSES, WAVE PLAN, GATE CHARGE

### III.3‴ — the R3c case space (successor to III.3′ = R3a, III.3″ = R3b)

| case | condition | disposition |
|---|---|---|
| III.3‴.a | defs + (b.1)+(b.2)+(a1) land; (a2) tail C | PARTIAL LANDING (the registered target; ~0.6–1.0M) |
| III.3‴.b | (a3) O1 (lower bound dominates) | SUCCESS branch — escalate to house (genuine advance) |
| III.3‴.c | (a3) O2 (lower bound vacuous at level) | EXPECTED DEATH — R4-collision obstruction note |
| III.3‴.d | (a2) tail prices D | sub-obstruction, distinct from (a3) |
| III.3‴.e | (b) analytic control fails below level ½ | REGRESSION — should not occur (char_LS covers τ to ½); if it does, flag |

### III.3″-style numeric witnesses (decidable, for the gate's arithmetic redo)

- **χ mod 3** (quadratic, χ(1)=1, χ(2)=−1, χ(0)=0): λ_χ table —
  `λ_χ(1)=1`, `λ_χ(2)=1+(−1)=0`, `λ_χ(3)=1+0=1`, `λ_χ(6)=1−1+0+0=0`.
  τ-bound check: `|λ_χ(6)|=0 ≤ τ(6)=4` ✓ (the bound is LOOSE — the twist
  cancels; the looseness IS the parity signal).
- **χ mod 5** (quadratic, χ:(1,2,3,4)↦(1,−1,−1,1)): local factors for `P=2·3·7`
  — `p=2: χ(2)=−1 ⟹ factor 1`; `p=3: χ(3)=−1 ⟹ factor 1`; `p=7: χ(7)=χ(2)=−1
  ⟹ factor 1`. Twisted main sum `= 1` (all local factors collapse) — the
  extreme sparse-product witness for (a1)/(a3): under full χ=−1 correlation the
  twisted main term is `∏_{χ=1}(…) = (empty) = 1`, and `L(1,χ)` small ⟹ the
  `cLow·L(1,χ)` floor is TINY — the (a3) collision made concrete.
- **The `(1+χ(p))` collapse** is `decide`-checkable per prime; the gate redoes it.

### Wave / node plan (~0.6–1.0M, matching the recon's cliff datum)

| node | content | class | est. |
|---|---|---|---|
| R3c-1 | `chiRe`/`lamChi`/`twistedMainSum`/`twistedErrSum` + `lamChi_mult` | B | 60–100k |
| R3c-b | `abs_lamChi_le_tau` + `twistedErrSum_le_tauRemainder` + level-½ packaging | B/C | 150–250k |
| R3c-a1 | `twistedMainSum_euler` (the sparse-product factorization) | C | 150–250k |
| R3c-a2 | L(1,χ) identification (finite→infinite tail) | C/D | 150–300k |
| R3c-a3 | THE LOWER BOUND — the D-locus, expected death | D | declare at collision |
| R3c-c | signed assembly (`twisted_sieve_lower`) — gated behind (a3) | C | (unreached) |

Dispatch: R3c-1 → R3c-b ∥ R3c-a1 (independent) → R3c-a2 → R3c-a3 (declare).
ONE executor after the gate; the partial landing (1+b+a1[+a2 tail]) is the
registered deliverable, (a3) the honest death.

### GATE CHARGE — S3-HB3C-GATE (the standing kill-check discipline)

Per the `swat_vacuous` / HB2 / HB3b precedents (the audit is bidirectional —
recon-refutes-gate AND gate-refutes-recon have both fired this sprint):

1. **The arithmetic REDO.** Independently recompute the χ mod 3 / χ mod 5 λ_χ
   tables and the `(1+χ(p))` local-factor collapse (`decide`-shaped); confirm the
   τ-bound is the loose signal it should be, not a masked error.
2. **The elaboration probes.** Re-run the §1 defs + the (b)/(a1)/(a3) statement
   shapes against the LANDED layer (this pass's probe is clean; the gate re-does
   at the actual `Salt.Chen.LinearSieve` + `SiegelClose` names, and CONFIRMS the
   weight-generic reuse `twistedMainSum = s.mainSum (lamChi χ)` holds at the real
   API — the §0 seam is the load-bearing structural claim).
3. **The quantifier audit.** (a3)'s `∃ cLow > 0` must be OUTERMOST and NOT
   collapse: the standing kill-check is **is `twistedMainSum_lower` VACUOUS?** —
   `cLow = 0` makes it trivially true (the `swat_vacuous` trap). Force `cLow > 0`
   in-statement AND verify `cLow` may legitimately be `q^{−O(1)}` (from
   Dirichlet's √q floor via a2) WITHOUT the R3b `∀`-strength order inverting. If
   the honest `cLow` is provably positive but the CONCLUSION is vacuous at the
   sieve level (τ-error undominated), that is outcome O2 (the death), and the gate
   records it as the R4-collision — NOT as a landed theorem.
4. **The direction kill-check.** Verify (against Tao) that (a3) is the LOWER
   bound and that SiegelClose's UPPER bound `LFunction_one_re_le_mvt_sharp` is
   **not** smuggled in with a flipped sign as if smallness helped the main term
   (Reading B is refuted; the Lean statement must not encode it).
5. **R4 framing.** (b) STOPS at level ½; the docstrings carry the R4 death-rung
   pointer (beyond-½ / Kloosterman, the documented wall) and the R3c-as-boundary-
   entry framing (no twin claim; the partial landing + the (a3) obstruction note
   are the deliverable; the SiegelSequence honesty block from R3b applies — the
   twist inherits the strictly-stronger, one-way, no-branch-smuggled discipline).

**Est.** partial landing 0.6–1.0M / 6 nodes; ONE executor after this gate;
(a3) declared at the collision per Amendment 3.

---

## GATE VERDICT — S3-HB3C-GATE (2026-07-16)

**VERDICT: GO-WITH-BLOCK.** The R3c architecture is STRUCTURALLY SOUND and the
death map is HONEST: the "reuse seam" (twisted main/err sums = the mathlib
`BoundingSieve.mainSum`/`errSum` combinators AT the signed weight `lamChi χ`)
elaborates at the REAL API (probe-confirmed); the substrate inadmissibility is
correct; the direction (a3 = LOWER bound) is honest and SiegelClose's UPPER bound
is not sign-flip-smuggled; `siegel_L_one_lower_near`'s distinct-target shape is
characterized accurately; Charge-1 arithmetic re-checks in-kernel. BUT the standing
kill-check fires on TWO frozen statements — **build with BLOCK-1/2/3 applied, not
verbatim.** One is a hypothesis omission that makes a REQUIRED node's frozen
statement FALSE (a1); the other is the `swat_vacuous` trap latent in the (a3)
schematic (proven vacuous in-kernel). Both fixes are surgical (no re-cut of the
wave plan, node set, or estimates), hence GO-WITH-BLOCK not RE-CUT.

Adjudication probes (kept in scratch, reproduced by the gate):
`ProbeR3c.lean` (the design's own frozen-def probe — re-run, clean: 4 expected
`sorry`s only) and the gate's `ProbeGate.lean` (Charge-1 `decide` arithmetic +
the in-kernel (a3) vacuity witness).

### Charge 1 — arithmetic REDONE (in-kernel, `decide`-confirmed)

`quadraticChar (ZMod 3)`: `1↦1, 2↦−1, 0↦0`; `quadraticChar (ZMod 5)`:
`1↦1, 2↦−1, 3↦−1, 4↦1`; `(7 : ZMod 5) = 2` — all `by decide` (ProbeGate).
Hence, redone independently:
- **χ mod 3:** `λ_χ(1)=1`, `λ_χ(2)=1+(−1)=0`, `λ_χ(3)=1+0=1`, `λ_χ(6)=1−1+0+0=0`;
  `τ(6)=4`, `|λ_χ(6)|=0 ≤ 4` ✓ (loose — the twist cancels; the looseness IS the
  parity signal, NOT a masked error). Matches the design table (L513–516).
- **χ mod 5, `P=2·3·7`:** `χ(2)=χ(3)=χ(7 mod 5=2)=−1` ⟹ every local factor
  `1+(1+χ_ℝ(p))ν(p) = 1+0·ν(p) = 1`; twisted main sum `= 1` (empty `{χ=+1}`
  product). Matches L517–522. **The `(1+χ(p))` collapse** verified: `χ(p)=−1 ⟹`
  factor `1`; `χ(p)=+1 ⟹` factor `1+2ν(p)`. RESULT: no arithmetic defect.

### Charge 2 — elaboration probes: PASS at the LANDED API

`BoundingSieve` is a **mathlib** structure (confirmed — `Salt/BrunLower/Defs.lean:49`
comment "mathlib's `BoundingSieve.nu`"; opened, not salt-defined). `mainSum`/`errSum`
are `BoundingSieve` members of type `(ℕ → ℝ) → ℝ` (weight-generic; used as
`s.mainSum S.lam` throughout `LinearSieve.lean`). Therefore the §0 load-bearing
seam holds AT the real API: `twistedMainSum s χ := s.mainSum (lamChi χ)` and
`twistedErrSum s χ := s.errSum (lamChi χ)` elaborate with `lamChi χ : ℕ → ℝ`
(ProbeR3c, clean). All §1 defs and the (b.1)/(b.2)/(a1)/(a3) statement SHAPES
type-check. `errSum` unfolds to `Σ_{d∈divisors P} |w d|·|rem d|`
(`LinearSieve.lean:316`), so (b.2)'s RHS index (`s.prodPrimes.divisors`) and abs
structure match; (b.1)+(b.2) are termwise-sound as frozen (and correctly carry NO
reality hypothesis — see BLOCK-1 for why (b) is right where (a1) is wrong).

### Charge 3 — quantifier / vacuity: **BLOCK-2** (the swat_vacuous trap fires on a3)

The frozen (a3) conclusion (L449),
`∃ cLow : ℝ, 0 < cLow ∧ cLow * (LFunction χ 1).re ≤ twistedMainSum s χ`,
is **VACUOUS**: the gate proved IN-KERNEL (`ProbeGate.lean`, no `sorry`) that it
follows from `0 < twistedMainSum s χ` ALONE, with NO information about the actual
size relationship (case `L≤0`: take `cLow=1`; case `L>0`: take `cLow=M/(2L)`, giving
`cLow·L = M/2 < M`). Since the twisted main term IS positive generically (via a1,
each factor `≥ 1`), a proof of the frozen (a3) would be a trivial swat and would
let outcome **O2/O3 masquerade as O1** — exactly what the standing charge forbids.
The design's own Charge-3 mitigation ("force `cLow > 0`") is **INSUFFICIENT** —
forcing `0 < cLow` does not remove the vacuity (the in-kernel witness has
`0 < cLow`). **BLOCK-2:** if (a3) is committed as a Lean statement at all, `cLow`
must be pinned to a `q`-explicit floor (e.g. `∃ A > 0, (q:ℝ)^(−A) ≤ cLow ∧ …`, the
Dirichlet √q / Goldfeld floor that (a2) must land), so that "O1" is defined against
a NON-vacuous statement. Otherwise keep (a3) **prose-only** ("declare at the
collision" per Amendment 3) and record the R4-collision obstruction note WITHOUT a
Lean theorem. No `∀`-strength inversion is introduced by R3c's own statements
(the R3b `∀c∃` lives behind the imported correlation, not in §1–§4).

### Charge 4 — direction kill-check: HONEST

`LFunction_one_re_le_mvt_sharp` (`SiegelClose.lean:458–461`) is the UPPER bound
`(LFunction χ 1).re ≤ (1−β)·25e·(1+log f)²` — matches the design's L461 citation.
The frozen (a3) uses `cLow·(LFunction χ 1).re ≤ twistedMainSum` — the LOWER
direction. `siegel_L_one_lower_near` (`SiegelClose.lean:582–590`) carries the zero
on `χ₁` (`hz₁`), the lower bound on the DISTINCT target `χ`, and the distinctness
hypothesis `hdist : ∀ (h : q₁ = q), (h ▸ χ₁) ≠ χ` (L586). So the freeze's
characterization — "the landed effective lower bound requires a distinct target and
does NOT apply to the self-same exceptional χ" — is ACCURATE; Reading B is correctly
refuted; the upper bound is not smuggled with a flipped sign.

### Charge 5 — R4 framing: HONEST

(b) STOPS at level ½ (the char_LS τ-coverage ceiling); the beyond-½ push is R4
(the Kloosterman wall). No twin claim; the deliverable is the partial landing +
the (a3) obstruction note; the SiegelSequence honesty block is inherited. The
executor MUST carry these pointers into the actual `.lean` docstrings (the design
prose is correct; verify it survives into code).

### BLOCK-1 — (a1) `twistedMainSum_euler` (and `lamChi_mult`) are MISSING `χ² = 1` — FALSE as frozen

The frozen (a1) (L421) quantifies over ALL `χ : DirichletCharacter ℂ q` with NO
constraint. But `chiRe χ = Re ∘ χ` is multiplicative ONLY when `χ` is real; for
complex `χ`, `Re(zw) ≠ Re(z)·Re(w)`, so `lamChi χ = χ_ℝ ∗ 1` is NOT multiplicative
and the Euler factorization `Σ_{d∣P} λ_χ(d)ν(d) = ∏_p (1+(1+χ_ℝ(p))ν(p))` FAILS.
**Concrete counterexample** (order-4 `χ` mod 5, `χ(2)=i`, a legal instance of the
frozen quantifier): `χ(3)=χ(2³)=−i`, so `χ_ℝ(2)=χ_ℝ(3)=0`, `χ_ℝ(6)=Re χ(1)=1`;
then `λ_χ(2)=1+0=1`, `λ_χ(3)=1+0=1`, but `λ_χ(6)=χ_ℝ(1)+χ_ℝ(2)+χ_ℝ(3)+χ_ℝ(6)
=1+0+0+1=2 ≠ 1 = λ_χ(2)·λ_χ(3)` — non-multiplicative, and `twistedMainSum` at
`P=2·3` misses the product by `ν(2)ν(3) > 0`. (For a QUADRATIC `χ`, `χ_ℝ = χ ∈
{−1,0,1}` is completely multiplicative and (a1) is exactly right — that is why the
FIX is precise.) **BLOCK-1:** add `(hsq : χ ^ 2 = 1)` to `twistedMainSum_euler`
AND to `lamChi_mult`. This is ALWAYS available downstream (the SiegelSequence χ is
quadratic), does not change the node's B/C tier or estimates, and is the reason (b)
is stated correctly without it: `|λ_χ(d)| ≤ τ(d)` (b.1) needs only `|Re χ(e)| ≤ 1`,
which holds for any χ — the reality hypothesis is a MULTIPLICATIVITY requirement,
not a boundedness one. Adding it blanket-everywhere would be wrong; add it to
(a1)+`lamChi_mult` ONLY.

### BLOCK-3 — `lamChi_mult`'s `.IsMultiplicative` shape does not typecheck on a bare `ℕ → ℝ`

The frozen node-R3c-1 shape `(fun d => lamChi χ d).IsMultiplicative` (L346)
references `ArithmeticFunction.IsMultiplicative`, a projection on `ArithmeticFunction`,
not on a plain function. **BLOCK-3:** the executor picks the multiplicativity vehicle
— either state it as `∀ m n, Nat.Coprime m n → lamChi χ (m*n) = lamChi χ m * lamChi χ n`
(the directly-usable form for the (a1) factorization), or wrap `lamChi χ` in an
`ArithmeticFunction`. Either is class-B and inherits the R3c-1 budget.

### Node (c) sign-flow sub-charge: DEFERRAL ACCEPTED

`linear_sieve_lower` (`LinearSieve.lean:349`) rides on
`Salt.BrunLower.siftedSum_ge_mainSum_errSum_of_lowerMoebius` via `S.isLowerMoebius`
(a Möbius-truncation SIGN lemma) + `abs_lam_le_one` — both FALSE for `λ_χ`
(`λ_χ` is neither a Möbius truncation nor `|·| ≤ 1`). The design flags this correctly:
node (c) is NOT a mechanical mirror, is gated behind (a3) (which dies first), is
SCHEMATIC (placeholders, not frozen), and the density-twist-vs-weight-twist decision
is deferred to (c) design time. The gate accepts the deferral: DO NOT commit the
schematic `twisted_sieve_lower` via the `…_lowerMoebius` route (it does not apply);
(c) is unreached this sprint.

### THE WAVE-1 EXECUTOR CUT (on GO)

ONE executor (subagent named `R3c-1`, model opus), single file
`Salt/TwinBar/TwistedSieve.lean` (imports `Salt.Chen.LinearSieve` +
`Salt.TwinBar.SiegelCorrStrong`; NO `.All`). Node order:

1. **R3c-1** (wave-1 cut, the foundation): `chiRe`, `lamChi`, `twistedMainSum`,
   `twistedErrSum` VERBATIM (probe-clean) + `lamChi_mult` **with `(hsq : χ^2 = 1)`
   [BLOCK-1] as a coprime-product equation [BLOCK-3]**. Class B, 60–100k.
2. **R3c-b ∥ R3c-a1** (independent, after R3c-1): (b.1) `abs_lamChi_le_tau`
   (verbatim, no reality hyp) + (b.2) `twistedErrSum_le_tauRemainder` (verbatim) +
   the level-½ packaging that STOPS at ½; and (a1) `twistedMainSum_euler` **with
   `(hsq : χ^2 = 1)` added [BLOCK-1]**. Classes B / B-C.
3. **R3c-a2** (tail): the L(1,χ) finite→infinite identification (C/D).
4. **R3c-a3** (declare, per Amendment 3): DO NOT commit a vacuous Lean statement
   [BLOCK-2]; if committed, pin `cLow ≥ q^{−O(1)}`; else record the R4-collision
   obstruction note in prose. (c) unreached.

The registered deliverable is the partial landing (R3c-1 + b + a1 [+ a2 tail]);
(a3) is the honest death. Docstrings carry the R4 death-rung pointer and the
no-twin-claim / SiegelSequence-honesty framing [Charge 5].

## HB-R4-R0 — THE REVIVAL HEARING (2026-07-20, post-Weil):
VERDICT RED, RE-ATTRIBUTED

The death certificate's stated cause ("Kloosterman/Weil is absent
entirely") is NOW FALSE — the genuine 2√p Weil bound landed via
Stepanov descent this window. The rung stays RED for the CORRECTED
reason: the certificate mis-diagnosed which absence was fatal. The
missing object is the ENGINE, not the tool — the bridge
**SiegelSequence ⟹ TwinTypeII** (= Heath-Brown's paper): the
Vaughan-twist decomposition → the dispersion reduction → the
incomplete-Kloosterman completion → the composite τ(c)√c assembly
(parked) → the singular-series reassembly. Five links; the first
four unbuilt; a Chen/BV-scale multi-month track. No landed
dispersion frame has a Kloosterman socket (typeII_disc_le closes
via the large sieve; the Maynard door is parity-limited to
bounded gaps at ANY level — never twins).

**THE NARROWING (the hearing's gift):** the sorry-free twin door
`twinB_min_implies_twins : TwinTypeII → TwinPrimeConjecture`
means R5 = "prove SiegelSequence ⟹ TwinTypeII", FULL STOP — the
death map never noticed. **THE LIGHTNESS FINDING:** HB is
genuinely lighter than Zhang — one-variable Weil (IN HAND), not
Deligne; single-layer dispersion; the Siegel zero supplies the
parity break free. The corpus has HB's tool where it could never
have had Zhang's. **THE FIRST NODE for whoever opens the track:**
re-point BV/Completion.lean's Fourier-cutoff machinery (currently
Dirichlet-aimed) at the Kloosterman complete sums — a bounded
port. STATUS: **HB-ENGINE = a NAMED FUTURE CAMPAIGN** (peer of
the MR formalization), not a this-window play. Distinction from
W4-MAJOR's RED: a SCALE verdict, not a category error — opening
a track, not flipping a switch.

## HB-ENGINE — REGISTERED AS A FUTURE CAMPAIGN (JYH, 2026-07-20)

Target: **SiegelSequence ⟹ TwinTypeII** (the twin door then gives
TwinPrimeConjecture — Heath-Brown 1983, formal-first). Pricing
(the HB-R4-R0 hearing + house link table): five links — the
completion port (~0.2–0.3M), the composite Weil assembly
(~0.3–0.5M), the tailored Vaughan/HB decomposition (~0.8–1.5M),
THE DISPERSION CORE (~1.5–3M, pole #1), the reassembly (~1–2M,
pole #2, the Chen-5.3× genre) — raw ~4–7M, realistic **8–14M**,
2–5 focused days at Gold-Window intensity. Discounts banked: the
periphery landed (R1/R2/R3b/R3c bookkeeping, the sorry-free twin
door, the FULL Weil toolkit, the completion infra); the method's
current first-attempt rate. Risk: the dispersion core's structure
(the hearing's flagged reconstruction uncertainty) — the
campaign's opening recon must verify HB-1983's skeleton
section-by-section before the freeze.

**HB-FOUND (the down payment, THIS window — dispatched):** links
3+4 as independent bounded nodes: HB-F-COMP (re-point
BV/Completion's Fourier-cutoff at the Kloosterman complete sums —
the incomplete-sum bound) + HB-F-TAU (the composite τ(c)√c
assembly: the odd-prime-power crude bound + the factorization
iteration over Nat.factorization — ALSO completes summit one's
parked polish).

## HB-ENGINE RE-FREEZE (Fable, 2026-07-20 evening) — THE PAPER
## READ AT SOURCE; the five-link registration RE-CUT to seven
## grounded work packages

House read the actual PDF (Proc. LMS (3) 47 (1983) 193–224, all
32 pages; JYH supplied). Every claim below is GROUNDED at the
source. HB-R0's Tao-mediated recon was right about the hypothesis
shapes and WRONG (because Tao streamlined) about the exponential-
sum machinery.

### THE PIVOTAL ANSWERS (HB-R0 low-confidence list resolved)

1. **Kloosterman: YES, incomplete AND complete — our banked links
   are ON-TARGET.** §1 p.196: "bounds for the Kloosterman sum
   will be needed." §7 (7.1): the tool is **ESTERMANN's elementary
   bound** S(k;u,v) ≪ d(k)·k^{1/2}·(k,u,v)^{1/2} — complete sums
   at COMPOSITE modulus, the exact τ(c)√c shape of our landed
   norm_kloosterman_le_tau_sqrt, NOT Weil (weaker than Weil; our
   Weil-grade per-prime input over-satisfies it). And Lemma 10
   (§7) is precisely an INCOMPLETE-sum estimate: Σ'_{n∈I}ψ(f(n))
   over subintervals with congruence conditions, completed via
   the sawtooth Fourier expansion (7.2)–(7.4) into complete
   S(k;s,Cm) — the same completion genre as our BV fourierCutoff
   / HB-F-COMP. Tao's r^{3/4} remark replaced Estermann; the
   original uses d(k)√k. **Links (a)+(b) banked-and-central, not
   sunk.** Remaining deltas: (i) the gcd factor (k,u,v)^{1/2}
   (our τ√c is unit-a only); (ii) CUBE-FREE moduli (χ real
   primitive ⟹ q cube-free, p.212) — corpus has k=1 sharp (Weil)
   + k=2 sharp (even prime-power); cube-free assembly is a modest
   CompositeFull extension; (iii) Lemma 10's congruence-
   conditioned interval variant of the completion.
2. **Hypothesis (1.11): FIRST-POWER confirmed at source** —
   1−β₀ ≤ (3 log q)^{-1}, η := {(1−β₀)L}^{-1} ≥ 3. Matches
   InfinitelyManySiegelZeros, NOT SiegelSequence (squared-log).
   Window (1.13): q^250 ≤ x ≤ q^500 (Corollary 1 at q^300).
   WINDOWED, so the TwinTypeII re-point stands: target Corollary
   2's shape (∃ effective C^(1): η ≥ C^(1) infinitely often ⟹
   infinitely many twin representations), consumed through
   twin_survivor_of_pos, replacing twinB_min_implies_twins.
3. **Zero-density IS needed — HB-R0's kill-question (i) answer
   was WRONG.** (4.9) uses Jutila's N(σ,T,χ) ≪ (qT)^{(5/2)(1−σ)}
   (σ ≥ 4/5) AND the Deuring–Heilbronn repulsion r₀ ≫ L^{-1}log η
   (Jutila Thm 2) — both in Lemmas 3 & 7 (§4). Corpus check
   needed: the SW stack has the explicit formula ψ(y,χ) (landed);
   Jutila-grade density + D-H repulsion are NOT believed landed.
   This is the campaign's biggest unpriced analytic debt.
4. **The sieve is IWANIEC's ROSSER SIEVE, DIMENSION 4** (λ_d^±,
   D = z³ = q^{1/3}, the S-set/P(δ) structure, S₁′−S₁ ≪
   exp(−z₀/4)S₁ from [Iwaniec, Rosser's sieve, Thm 4]) — (2.2),
   Lemma 6. Tao streamlined this away; the registration never
   mentioned it. Import honestly or re-derive the needed
   fundamental-lemma consequence over our Selberg machinery —
   a design decision for the campaign opener.
5. **The quadratic character sum** Σ_t χ(ut+u′)χ(vt+v′) ≪
   (q, uv′−vu′) (p.217, "straightforward. We shall omit it") is
   real and UNBANKED — B-class node.
6. **No Cauchy–Schwarz dispersion anywhere** — confirmed at
   source. The §§5–6 core is congruence elimination
   (5.4)–(5.17): the two-variable lattice count reduced to
   v₂w₂ ≡ C (mod Dδ₁w₁) via CRT consistency (5.13), then counted
   by sawtooth ψ → Lemma 10. Intricate but ELEMENTARY.

### The seven grounded work packages (replacing the five links)

- **WP1 — the twist chain** (Lemmas 1, 2, 4; §§2–3): Λ̃ = μ²χ∗log,
  Λ* with the ∑* star condition, S⁽⁰⁾→S⁽³⁾ transfer; elementary
  convolution identities + crude bounds. ~0.5–1M.
- **WP2 — the pretense sum + L-machinery** (Lemmas 3, 7; §4):
  Σ_{χ(p)=1} p^{-1}log p ≪ L(log η)^{-1/4}; L′/L(1,χ) = ηL +
  O(L(log η)^{-1/4}); κS₁ → 𝔖C(α)(ηL)^{-2}. NEEDS Jutila density
  (4.9) + Deuring–Heilbronn + the landed explicit-formula stack.
  ~1.5–3M (the density theorem dominates; recon the corpus first).
- **WP3 — the Rosser sieve import** (dimension 4, λ±, Lemma 6 +
  the [10, Thm 4] consequence). ~1–2M or a Selberg re-derivation.
- **WP4 — the Kloosterman completion** (Lemma 10, §7): banked
  HB-F-COMP/HB-F-TAU + the three deltas above. ~0.3–0.7M.
- **WP5 — THE CORE congruence reduction** (Lemmas 9, 11, §5):
  the Λ* Mellin expansion, dyadic S(δ₁,δ₂;V₁,V₂), the
  (5.4)–(5.17) elimination to a single congruence + ψ-counting.
  ~1.5–3M. THE POLE.
- **WP6 — the leading terms** (§6): the a_i,b_i character
  averaging (incl. the unbanked quadratic character sum), the
  Euler products F(u,v)/G(u,v), the log-differentiation to
  (L′/L)² + additive functions A_i(d). ~1–2M.
- **WP7 — assembly + the windowed door** (§§2, 8): Lemma 5 →
  S⁽³⁾ → Theorem 1 → Corollary 2; the twin door re-point
  (windowed positivity via twin_survivor_of_pos + a new
  arbitrarily-large-x door lemma; retire the TwinTypeII target).
  ~0.5–1M.

**Revised campaign price: 6.5–12.5M** (recon band confirmed,
now with grounded structure). Biggest swing: WP2's density
theorem (if a corpus recon finds usable zero-density
infrastructure, −1M). Target statement: `InfinitelyManySiegelZeros
→ TwinPrimeConjecture` = the landed HeathBrownStatement, exactly
— the first-power hypothesis is what the paper needs, no
squared-log strengthening, and the mis-aimed SiegelSequence
bridge is bypassed. **First executable nodes (freezable now):
HB-1 = WP1's Λ̃/Λ*/f(n) definitions + Lemma 1 (B-class, ~150k);
HB-2 = the quadratic character sum (B, ~100–150k); HB-3 = WP2's
corpus recon for density/repulsion (recon, ~100k).** Campaign
opening awaits JYH's go.

### WP2 AMENDMENT (HB-3 adjudicated, 2026-07-20 late evening)

HB-3's corpus recon re-prices WP2 at **2.4–4.3M, center ~3M**
(the old band's UPPER edge), MEDIUM confidence, with a corrected
composition:
- **CATCH #47 (executor-catches-designer):** the house belief
  "the explicit-formula stack is landed" was WRONG. What is
  landed is the SMOOTHED Riesz mean ψ₁ with zeros ASSUMED AWAY
  (hzf-hypothesis architecture) — HB needs the sharp ψ(y,χ) with
  the ENUMERATED truncated zero sum Σ_{|ρ|≤T} y^ρ/ρ. The rebuild
  (+~0.8M) reuses Perron/kernel_residue/contour calculus but
  flips the architecture. Under-budgeted in the re-freeze.
- **The density discount is REAL (−1M):** the entire large-sieve
  input stack is landed (char_LS/analytic_LS/bdh/gallagher/
  parseval) and the TOLERANCE ARITHMETIC gives ~33× slack — the
  tail needs only 3D < c_win ≈ 250, so ANY crude polynomial
  density (qT)^{O(1)(1−σ)} works; no Jutila reproduction.
- **Deuring–Heilbronn is THE POLE** (C→D risk, 0.6–1.2M+):
  genuinely absent, indispensable (a zero-free region gives NO
  η-decay — the log η repulsion is what manufactures η^{-A});
  best route = partial-fraction/positivity (footholds landed:
  any-radius LFunction_partialFraction, page_positivity, 3-4-1).
- Ingredient prices: L′/L+Prachar 0.3–0.5M; repulsion 0.6–1.2M⚠;
  crude density 0.5–0.9M; EF rebuild 0.6–1.0M; Lemma 3/7
  assembly 0.4–0.7M.

**Campaign total re-centered: ~7–13M** (WP2 at upper band).
**Dispatched on adjudication: HB-WP2-1** (the Prachar
radius-resolved zero count near s=1, B–C ~0.2M — prerequisite to
THREE downstream items, buildable on the landed Jensen count) and
**HB-WP2-2-SPIKE** (the repulsion feasibility spike: isolate β₀
in the any-radius partial fraction, attempt the log η gain on a
bounded range; its verdict decides WP2 ≈ 2.5M vs >4M — the
campaign's true go/no-go).

### WP2 SOURCE REFERENCES (grounded 2026-07-20 night; house read)

**Jutila, "On Linnik's constant", Math. Scand. 41 (1977) 45–62 —
HB's [11], BOTH consumed theorems. OPEN ACCESS:**
PDF https://www.mscand.dk/article/download/11701/9717
(DOI 10.7146/math.scand.a-11701). NOT to be confused with
Jutila's OTHER 1977 paper (Acta Arith. 32, "Zero-density
estimates for L-functions" — sharper A₁=2 density via
Halász–Montgomery; we do not need it).

- **Theorem 1** (p.46): N(α,T,q) ≪_ε (qT)^{(2+ε)(1−α)} for
  4/5 ≤ α ≤ 1 (summed over χ mod q — implies the per-character
  form; HB quotes the safer 5/2). Proof via Selberg
  pseudocharacters + Halász; per HB-3's tolerance (~33× slack)
  we may instead land ANY crude polynomial density from the
  landed large sieve.
- **Theorem 2** (p.47, THE REPULSION, exact statement): χ₁ real
  non-principal mod q, β₁ = 1−δ₁ real zero of L(s,χ₁); χ any
  character mod q, ρ = 1−δ+iτ a zero of L(s,χ), δ < 1/6,
  β ≤ β₁; D = q(|τ|+1) ≥ D₀(ε). Then
  **δ₁ ≥ (1−6δ)·D^{−(2+ε)δ/(1−6δ)}/(8 log D)**. (1.10)
  INVERSION to HB's form: δ₁ tiny ⟹ for τ bounded,
  δ ≥ c·log(1/(δ₁ log D))/log D ≈ c·(log η)/L — exactly
  r₀ ≫ L⁻¹ log η. The formalization may target (1.10)'s shape
  directly (a LOWER bound on δ₁ given another zero — possibly
  friendlier to Lean than the min-over-zeros form).
- **BONUS (effectivity):** "We do not appeal to Siegel's theorem,
  so that everything can be made explicit" (p.47) — matches HB's
  effective C^(1) in Corollary 2; the repulsion route keeps the
  campaign's final theorem effective.
- Jutila's own Thm 2 proof is NEW (not Turán power-sum; via the
  Graham/Halász lemma apparatus) — §§ later in the paper; house
  reads the proof section IF the in-flight spike returns
  YELLOW/RED (the D-posture siege prep). Local copy:
  scratchpad/jutila_linnik.pdf (session) — re-curl the URL above
  in future sessions.
