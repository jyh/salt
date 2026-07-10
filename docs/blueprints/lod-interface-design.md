# Rung 4b — level-of-distribution interface (Fable design, 2026-07-09)

Goal: make the capstone **Bombieri–Vinogradov-consumable**. Our
`bounded_gaps_from_eh_complete` consumes `EH (1/2)` (full modulus range
`x^{1/2}`). Actual BV controls only `x^{1/2}/(log x)^B`. This rung adds
the BV-shaped hypothesis and re-threads the one consumer, so that the
day BV is formalized (Rung 5), unconditional bounded gaps is an
instantiation. Additive only — iron rule 1: the landed `EH`,
`BoundedGapsFromEH`, `bounded_gaps_from_eh_complete`, and all proof
files are untouched.

## The statement (the Fable-tier decision — do not alter)

```lean
/-- The primes have level of distribution `θ` in the
Bombieri–Vinogradov sense: for every log-power saving `A` there is a
log-power haircut `B = B(A)` on the modulus range that achieves it.
`B` is existentially quantified AFTER `A` — this is BV's exact shape;
a fixed-`B` or `∀B` variant would be strictly stronger than BV and
unusable by Rung 5. `EH θ` is the `B = 0` special case. -/
def HasLevel (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ (B C : ℝ), 0 ≤ B ∧ ∀ x : ℕ, 2 ≤ x →
    (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / (Real.log x) ^ B⌋₊,
        maxDiscrepancy x q)
      ≤ C * (x : ℝ) / (Real.log x) ^ A
```

Rationale, fixed by design: (i) same `maxDiscrepancy`/`Finset.Icc 1 ⌊·⌋₊`
idiom as the landed `EH` — no new counting definitions; (ii) `∀A ∃B C`
ordering is load-bearing (see above); (iii) `0 ≤ B` so `(log x)^B` is
monotone-friendly; (iv) for `x ≥ 2`, `log x > 0`, so `B = 0` makes the
range coincide with `EH`'s — `EH θ → HasLevel θ` is immediate.

## Why the sieve absorbs the haircut

The only place the modulus range enters is `eh_error_pow`'s
range-extension step: our compat moduli satisfy `q = W·∏lcm < W·R²` with
`R = ⌊N^{1/5}⌋`, i.e. `q ≪ N^{2/5}`, while the shrunk range is
`x^{1/2}/(log x)^B ≥ N^{1/2}/(log 65N)^B` for `x ∈ {N+hₘ, 64N+hₘ}`.
Since `N^{2/5} ≪ N^{1/2}/(log N)^B` for every fixed `B`, the inclusion
`W·R² ≤ ⌊x^{1/2}/(log x)^B⌋₊` holds past an explicit `N`-threshold.
Nothing else in the proof sees the range.

## Nodes

| id | statement | class | notes |
|---|---|---|---|
| L1 | `HasLevel` def; `EH_hasLevel : EH θ → HasLevel θ`; `HasLevel_antitone` (θ-antitone, mirroring `EH_antitone`) | A | new file `Salt/Maynard/Level.lean` |
| L2 | `lod_error_pow` — the `eh_error_pow` analog under `HasLevel (1/2)`: same conclusion `Σ_{q<⌊√N⌋+1 → shrunk range, sqf} (3k)^ω·maxDisc ≤ C·N/(log N)^B'`, with the Cauchy–Schwarz structure of `eh_error_pow` intact; ONLY the second factor's modulus range shrinks | B/C | the one real node; copy `EHConsume.lean`'s proof, thread the haircut |
| L3 | `S2m_ge_compatMain_lod` — the `S2m_ge_compatMain_eh_uniform` analog: identical conclusion, hypothesis `HasLevel (1/2)`, range condition now `W·R² ≤ ⌊√N/(log N)^B⌋₊` (or fold the threshold into `N₀`) | B | copy `S2CompatEHFinal.lean`/`FrontierDischarge.lean` chain |
| L4 | `bounded_gaps_from_level : HasLevel (1/2) → ∃ C, ∀ N, ∃ p q, …` (same conclusion shape as `BoundedGapsFromEH`'s body); corollary `bounded_gaps_from_eh' := bounded_gaps_from_level ∘ EH_hasLevel` as a consistency check | B | copy `Complete.lean`'s endgame wiring |

## Execution constraints (from the six-fragility record)

1. **R-uniformity discipline** (the FrontierDischarge lesson): in L2/L3,
   obtain `(B, C)` from `HasLevel` ONCE at the fixed exponent
   (`eh_error_pow` uses `A' = 9k² + 2B'` internally) BEFORE quantifying
   over `R`/`N`. The `B` haircut then enters the `N`-threshold only.
2. **Explicit thresholds**: the new range condition is an `N`-largeness
   fact; state it as a hypothesis conjunct exactly like the landed
   `W k * R ^ 2 ≤ ⌊(N:ℝ)^(1/2:ℝ)⌋₊` and discharge it in L4's
   `∀ᶠ N'` block (template: `compatFrontier_holds` / Part G of
   `Complete.lean`) via `N^{2/5}·(log)^B ≤ N^{1/2}` eventually —
   `eventually_poly_beats_polylog` (FrontierDischarge.lean) is exactly
   this engine.
3. **Additive only**: new files `Level.lean` (L1) and `LevelConsume.lean`
   (L2–L4), imported from `All.lean`. No edits to landed proof files.
4. Verify per node: build clean, adversarial check on the quantifier
   shape of anything touching `HasLevel`, `#print axioms` =
   `[propext, Classical.choice, Quot.sound]`.

## Acceptance

`#check @bounded_gaps_from_level` shows
`HasLevel (1/2) → ∃ C : ℕ, ∀ N, ∃ p q, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧
q.Prime ∧ (q:ℤ)−(p:ℤ) ∈ Set.Icc (−C) C`, axiom-clean, with
`bounded_gaps_from_eh'` recovering the EH corollary. Estimated one Opus
session (L2 is the bulk).

---

## DONE (2026-07-09)

Rung 4b landed on `main`, axiom-clean `[propext, Classical.choice, Quot.sound]`:
- `Salt/Maynard/Level.lean`: `HasLevel`, `EH_hasLevel`, `HasLevel_antitone` (L1).
- `Salt/Maynard/LevelConsume.lean`: `lod_error_pow` (L2), `EH_range_lod` +
  `range_haircut_mono` + `S2m_ge_compatMain_lod_uniform` (L3),
  `analyticFrontier_lod` + `bounded_gaps_from_level_final` +
  **`bounded_gaps_from_level : HasLevel (1/2) → ∃ C, ∀ N, ∃ p q, …`** +
  **`bounded_gaps_from_eh' : BoundedGapsFromEH`** (L4, the consistency check).

Acceptance met: `#check @bounded_gaps_from_level` is `HasLevel (1/2) → …` and
`#check @bounded_gaps_from_eh'` is `BoundedGapsFromEH`. The theorem is now
BV-consumable: proving BV (Rung 5) makes unconditional bounded gaps a one-line
instantiation `bounded_gaps_from_level (bv_hasLevel …)`.

One design allowance used (L3, "fold the threshold into `N₀`"): the haircut map
`y ↦ y^{1/2}/(log y)^{B'}` is non-monotone near `y=2`, so `S2m_..._lod_uniform`
folds a `⌈exp(2B')⌉₊` threshold into its `N₀` (helper `range_haircut_mono`,
monotone once `2B' ≤ log N`). No blueprint statement altered; the interface
signature matches spec exactly.
