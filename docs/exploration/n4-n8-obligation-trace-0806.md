# N4/N8 OBLIGATION TRACE — does the repulsion ceiling have a consumer that needs `log(1/c)` SHARP?

**Read-only architecture trace, 2026-08-06. Opus executor. No Lean written, no build run, no
commit. Every load-bearing claim carries a `file:line` and is marked USE or PROSE.**

---

## 1. THE VERDICT

# **(B) — TS-3 IS DEFERRED (as a `log(1/c)` wave).**

**There IS a committed consumer, and the repulsion ceiling IS non-substitutable for it — but the
consumer's demand is quantitative in `b`, not in `log(1/c)`: driving `log(1/c)` from the landed
`631.58` all the way to `0` moves the consumer's own threshold by 0.27 %, while `b : 680 → 210`
moves it by a factor of 10.5.**

The one sentence that decides it: the committed obligation is
`hσ'r : √(log η)/(2L) ≤ r0/2` (`Salt/HB/Lemma7L.lean:240`, USE — a binder in the type of a landed
theorem), and feeding it the landed ceiling
`r0 = (log(1/u) − log(1/c) − k·log(log Q+2))/(b·log Q)` (`Salt/SW/TauExt.lean:177-178`, USE) gives
the threshold `log η − b·√(log η) ≥ log(1/c) + (k−1)·log L + O(1)` — in which `log(1/c)` is an
**additive term of order 10²** set against a **`b²`-scaled quantity of order 4.6 × 10⁵**.

**A (B) here is not "the artillery was wasted."** The trace found something the TS-0 refuter pass
did not: a *second*, genuinely load-bearing repulsion obligation that `efZfrCeil` provably cannot
discharge (§4). The finding is that the lever on it is `b` and `k`, and **not** `c`.

---

## 2. WHAT N4 AND N8 ARE ON THE ROAD — COMMITTED, and quoted

**N4 (= N4b, HB 1983 Lemma 7 at the multiplicative mandate) is COMMITTED, not sketched.** It has
a frozen design document with a wave table, and four of its five waves are landed sorry-free Lean.

- The freeze: `docs/exploration/n4b-design-0805.md:1-5` —
  > "# N4b DESIGN FREEZE v3 — HB Lemma 7 at the multiplicative mandate … v1 REFUTED (4 refuters
  > …); v2 folds every repair. Status: FROZEN pending the delta pass"

  with a named wave table (`:117-152` W0–W4) and a v3 DELTA (`:178-181`) that
  > "**GOVERNS**. Wave briefs quote v3."

- Its waves have LANDED as kernel-checked Lean, not prose. `git log -- Salt/HB/`:
  `f56ddf4` "N4B-SYMSPLIT — the W2C sharpening lands (848 ln, 13 decls)",
  `a607c61` / `127de71` "N4B-W4.5(defs+hsing)" / "N4B-W4.5(hrear+capstone+All.lean) — (4.4)
  PROVED … `hb_L2_at_split_point_concrete`: (L2) with both sieve binders discharged",
  and W1 at `f94cedb` (recorded at `n4b-design-0805.md:368`, "D10. W1 LANDED (f94cedb)").
  Landed artefacts: `Salt/HB/Lemma7L.lean` (W1), `Salt/HB/Lemma7EF.lean` (W2), `Salt/HB/Lemma7F.lean`
  (W3), `Salt/HB/Lemma7.lean` + `Lemma7Prod.lean` + `Lemma7Kappa.lean` (W4/W4.5).

**N8 is NOT a node with a stated deliverable anywhere I could find.** It appears exactly twice
outside `flags.md`: once in a road ordering sketch —
`docs/exploration/fleet-meeting-0803-brief.md:42` (PROSE) —
> "N5 → N8 → N9 (Thm 1) → N10 (Cor 2) → N11 (door …)"

— and once in the prose sentence this trace was dispatched to test,
`Salt/HB/PretenseSumProof.lean:105` (PROSE, inside a `/-- … -/` block):
> "N4/N8's assembly discharges them once, from the F-side context, exactly as
> `boxZeros_re_le_at_efHeight` requires."

There is **no N8 design freeze, no N8 wave table, no N8 deliverable statement, and no N8 Lean.**
So the sentence that names the intended wiring names one committed node (N4b) and one placeholder
(N8). ⇒ The intended assembly is committed **only through N4b**, and what N4b actually demands is
§4 below.

---

## 3. THE LEAVES CONFIRMED DEAD — the Range-A / efHeight branch

Re-verified by name (line numbers current at HEAD, 2026-08-06):

| leaf | site | consumers |
|---|---|---|
| `dh_repulsion_tall` | `Salt/SW/TBalTall.lean:2090` | `TauExt`/`TBalTall` internals + `Lemma7EF.lean:709` |
| `boxZeros_re_le_at_efHeight` | `Salt/SW/TBalTall.lean:2231` | **NONE.** `Salt/SW/All.lean:346` is the roll-call; `TwistedMertens.lean:116`, `PretenseSumProof.lean:105`/`:309` are all inside `/-- … -/` — **PROSE** |
| `boxZeros_re_le_unit_box` | `Salt/SW/TauExt.lean:340` | **NONE.** `Salt/SW/All.lean:342` roll-call; the two `Salt/HB/` hits are PROSE |
| `efZeroSumM_spend_at_repulsion` | `Salt/SW/TauExt.lean:306` | **NONE.** `Salt/SW/All.lean:341` roll-call only |
| `exists_repulsion_ceiling_of_ne` | `Salt/HB/Lemma7EF.lean:696` | applied at `:774` only — USE, one hop |
| `psiDefect_norm_le_rangeA` | `Salt/HB/Lemma7EF.lean:748` | **NONE.** `Salt/HB/All.lean:212` roll-call only |
| `one_sub_ceiling_le_dist_one` | `Salt/HB/PretenseSumProof.lean:312` | **NONE.** `Salt/HB/All.lean:179` roll-call only; `:73`, `:338`, `:377`, `TwistedMertens.lean:115`, `:792` are all PROSE |

And the end-to-end (4.12) theorem closes **without** any of it. `Salt/HB/Lemma7EF.lean:2317-2320`
(docstring of `logChiSum_tendsto_zfr`, PROSE but describing a machine-checked type):
> "The ONLY remaining binders are the freeze's own named ones: `hZFR` …, `hreal′` …, and the
> design's numeric `hgap`. **`hN+`, `hord` and the `q^{250} ≤ X` edge do NOT appear — they are
> Range-A's, and Range B needs neither.**"

Verified at the type: `logChiSum_tendsto_zfr_hundred` (`Salt/HB/Lemma7EF.lean:3136-3149`, USE)
has hypotheses `hZFR` and `hreal` only, both against `efZfrCeil` (`:1953`), and concludes
`≤ 100/√(log X)`. **The Range-A/efHeight repulsion branch is dead on the landed bytes.**

*(The open item is recorded, not owed: `flags.md:20762-20768` — the two-window assembly
"`psiDefect_norm_le_rangeA` `:748`, `logChiSum_composite_of_ceiling` `:1128`" exists in halves but
"**no assembly composes them**".)*

---

## 4. THE SUBSTITUTABILITY FINDING — the obligation `efZfrCeil` genuinely CANNOT discharge

**The repulsion contract's live consumer is not the EF ledger. It is HB's Lemma-3 machinery, and
it is live in the types of four landed theorems.** All four carry the same triple of binders:

```
(hr0   : 0 < r0)
(hσ'r  : √ell / Lp ≤ r0 / 2)                 ← THE SIZE DEMAND
(hSinvC: Sinv ≤ Cs * (Lp^2 / ell))           ← the (4.1) error-sum pricing
…  ((∀ ρ ∈ Z.erase β₀, r0 ≤ ‖ρ - 1‖) → …)    ← hfloor, in the conclusion
```

USE sites, all sorry-free and all `Lp = 2L`, `ell = log η`:

- `hb_L1_one_sided` — **N4b W1's deliverable, (L1)** — `Salt/HB/Lemma7L.lean:231`, binders at
  `:236` (`hSinvC`) and `:240` (`hσ'r : Real.sqrt (Real.log η) / (2 * L) ≤ r0 / 2`).
- `hb_chiOne_kill_at_window` — **N4b W3's (4.7)** — `Salt/HB/Lemma7F.lean:713`, binders at
  `:717` and `:721`.
- `pretenseSum_unconditional_absorbed` — `Salt/HB/Lemma3Uncond.lean:117`.
- `hb_lemma3_unconditional_absorbed` — `Salt/HB/Lemma3Uncond.lean:213`, binders at `:218`, `:222`.

**Why `efZfrCeil` cannot supply this.** `efZfrCeil q c₀ u = 1 − c₀/log(q(T₀(u)+3))`
(`Salt/HB/Lemma7EF.lean:1953-1954`, USE). The distance-to-1 floor it yields is
`r0 = c₀/log Q ≤ c₀/L`. Substituting into `hσ'r` demands

```
    √(log η) / (2L)  ≤  c₀ / (2L)     ⟺     √(log η) ≤ c₀ ,     c₀ = 1/126848
```

which is false for every `η > 1`. **The classical ZFR floor is bounded; the obligation needs a
floor that GROWS with `η`.** That is precisely the Deuring–Heilbronn content, and it is exactly
what `one_sub_ceiling_le_dist_one` (`Salt/HB/PretenseSumProof.lean:312-316`, USE) delivers:

```
    (log(1/u) − log(1/c) − k·log(log Q + 2)) / (b·log Q)  ≤  ‖ρ − 1‖ ,   u = 1 − β₀ = (ηL)^{-1}
```

whose numerator is `log η + log L − O(1)`. **This is the answer to the dispatched question:
the repulsion ceiling discharges `hσ'r`, an `η`-growing distance floor, and `efZfrCeil` provably
cannot.** Weakening `σ' = 1 + a/L` to fit a ZFR-sized `r0` forces `a ≤ c₀/2`, and
`hbCoreRate_at_operating_point` (`Salt/HB/TwistedMertens.lean:664-667`, USE) then returns
`2 + Rrem + 2(L/a) + …` — a rate of size `≍ L/c₀`, i.e. HB's Lemma 3 becomes vacuous. The
repulsion input is load-bearing, not decorative.

**Caveat, stated as dispatched:** `dh_repulsion_tall` excludes real zeros (`ρ.im ≠ 0`), so it
cannot cover the real zeros of `Z.erase β₀`. Neither can `zero_free_region_all` for a real `χ`
(side condition `χ² ≠ 1 ∨ Im ρ ≠ 0`; recorded at `n4b-design-0805.md:243-245`). **That residual
is `hreal′`, and it is owed by neither ceiling** — TS-3 does not touch it either way.

---

## 5. THE SHARPNESS FINDING — the consumer needs `b` small, NOT `log(1/c)` small

Compose the supply (§4) into the demand `hσ'r` at the unit-scale box (`Z ⊂ ball(2, 3/2)` from
`LFunction_partialFraction_remainder_diff`, so `log Q = L + O(1)`):

```
    log η + log L − log(1/c) − k·log(log Q + 2)  ≥  b · √(log η)
```

Solving `ℓ − b√ℓ ≥ log(1/c) + (k−1)·log L + O(1)` at the landed and proposed parameter sets
(`c₀ = 1/126848` at `ZeroFreeReal.lean:604`; the arm table at
`tau-sharp-ts1-ts2-briefs-0806.md:128-147`):

| state | `b` | `log(1/c)` | `k` | threshold `log η ≥` (L = 250) | (L = 10⁴) |
|---|---|---|---|---|---|
| **LANDED** | 680 | 631.58 | 14 | **463 806** | 463 901 |
| post TS-1+TS-2 (tonight) | 680 | 86.23 | 14 | 462 716 | 462 812 |
| **landed, `log(1/c)` set to 0** | 680 | — | 14 | **462 544** | 462 639 |
| TS-3 target (K2-corrected) | 210.12 | 51.67 | 1 | **44 254** | 44 254 |
| TS-3 target, `log(1/c)` set to 0 | 210.12 | — | 1 | 44 150 | 44 150 |

**Read the table:** an *infinitely sharp* `c` is worth **0.27 %** of the consumer's threshold at
the landed parameters and **0.23 %** at TS-3's. `b : 680 → 210` is worth **10.5×**. `k : 14 → 1`
is worth the `L`-dependence (the `(k−1)·log L` term — visible as the L=250 vs L=10⁴ column
collapsing at `k = 1`), which is a *structural* gain, not a size gain.

**Second, independent confirmation from the delivered constant.** `invSq_sum_split_le`
(`Salt/HB/TwistedMertens.lean:597-606`, USE) prices `Sinv ≤ C(1/r0² + log(f+2)/r0) + 16J`. At
`r0 ≍ ℓ/(bL)` this is `Cs ≍ C·b` — and `Cs` is exactly what appears in the delivered rate,
`K₁ = 1604 + 2m + 8·Cs` (`Salt/HB/Lemma7L.lean:249-251`, USE). So **`b` enters the delivered
constant linearly and `log(1/c)` does not enter it at all** — `log(1/c)` only shifts the
threshold at which `hσ'r` becomes satisfiable.

**The door is verified indifferent, exactly as pre-flagged.** `FulcrumQualityMin C`
(`Salt/Fulcrum/Basic.lean:61-64`, USE) is `‖1−ρ‖·(C·log q) ≤ 1`, i.e. literally `η ≥ C`; and
`imsz_gives_fulcrum_witnesses` (`Salt/Fulcrum/Gadget.lean:128-131`, USE) opens
`∀ C : ℝ, 0 < C → ∀ Q : ℕ, ∃ …`, supplying it **for every constant `C > 0`** (the proof takes
`c := min (c_iso·log 2) (1/C)`, `:124`). **A threshold `η ≥ e^{463806}` is therefore as free at
the door as `η ≥ e^{44254}`.** Consumed at `Salt/Fulcrum/Dichotomy.lean:86` (USE). The door is
gated on `q`-freeness, never on size.

⇒ **No consumer needs `log(1/c)` small. One consumer needs it FINITE and `q`-free — which it
already is.** That is decision-rule branch **(B)**.

---

## 6. WHAT WOULD HAVE MADE IT (A), AND WHAT TO SALVAGE

Stated so the deferral is not read as "the road needs nothing here":

1. **`k : 14 → 1` is the only TS-3 move with a structural (not size) payoff.** It removes the
   `(k−1)·log L` term above, making the `hσ'r` threshold `q`-free — the one property the door
   requires. But `k = 1` is the floor, not `0`: the freeze itself says so
   (`tau-sharp-scout-dossier-0805.md:242`, "**THE FLOOR OF k: k = 1 EXACTLY (§4). Not 0**"), and at
   `k = 1` the `+1·log(log Q+2)` and the `−log L` from `log(ηL)` cancel to `O(1)`, so this
   obligation *does* become `q`-free at `k = 1`. **This contradicts nothing in TS-0's K3**, which
   was analysing a *different* obligation (the Range-A EF ledger's `10³M³N` prefactor,
   `Lemma7EF.lean:2626-2632`) — the one §3 shows is dead.
2. **If TS-3 is re-scoped as a `b`-wave (S3 alone: `a : 104 → 51`), it clears the (A) bar on the
   `b` axis** — 10.5× on the threshold, ~3× on the delivered `Cs`. That is a different wave with a
   different justification, and it should be priced against K2's corrected `b`-floor of **664.66**
   (`tau-sharp-refuter-0806.md:225-241`), not the freeze's 589.33.
3. **TS-1 and TS-2 (firing tonight) already collect 82 % of the entire `log(1/c)` prize**
   (631.58 → 86.23), for ~140 lines instead of 600–900. Whatever the residual `86 → 52` is worth,
   it is 0.05 % of the consumer's threshold.

---

## 7. WHAT I COULD NOT DETERMINE

Stated plainly; each of these is a real gap in this trace, not a hedge.

1. **No Lean anywhere instantiates `r0` at the repulsion value.** `one_sub_ceiling_le_dist_one`
   (`PretenseSumProof.lean:312`) and `hσ'r` (`Lemma7L.lean:240`) have never been composed — the
   connection is asserted only in docstrings (`TwistedMertens.lean:114-118`,
   `PretenseSumProof.lean:303-310`, both PROSE). **My §5 arithmetic is my own hand derivation from
   the two landed statements, not a kernel-checked composition.** If the eventual composition
   needs a different `Q` (e.g. the tall box rather than `ball(2,3/2)`), the `log Q/L` factor moves
   and the numbers in the §5 table shift — the *ratio* between the `c`-lever and the `b`-lever
   would not, since it is `b²`-vs-additive, but I did not prove that robustly at every base.
2. **I could not tell whether the road's endgame is sensitive to the SIZE of `K₁ = 1604+2m+8Cs`.**
   It flows into `hsmall` (`Lemma7Kappa.lean:958`, a hard `≤ 1` side condition) and thence to
   N9/N10, but the `z`-window feasibility that decides it is not written anywhere I found. If it
   *is* sensitive, that is a second argument for a `b`-wave — and still not for a `c`-wave.
3. **I could not determine whether the two-window Range-A assembly (`flags.md:20762-20768`) is
   still wanted.** Range B closes (4.12) end-to-end at `K = 100`; whether the road ever needs the
   Range-A power saving on `[X, Y₁]` for a *different* consumer is a design question, not a byte
   question. If someone revives it, `psiDefect_norm_le_rangeA` becomes live and this trace's §3
   would need re-running — but §5's sharpness arithmetic would be unaffected.
4. **`hreal′` (real zeros of `Z.erase β₀`) is owed by neither ceiling** and I did not price it.
   It is a named binder in the landed statements, exactly as `hN+` and `hsep` are.
5. **I did not verify TS-3's line estimate (600–900).** I took it from K2
   (`tau-sharp-refuter-0806.md:243-252`) at face value.
