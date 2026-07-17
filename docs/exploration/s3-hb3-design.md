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
