# THE A4 BRIDGE — design freeze v1 (2026-07-30, the BRIDGE-SCOPE dossier consumed)

*The port's last stone: the y-aspect-vs-t-aspect crossing that discharges
`m4_second_road`'s socket (item 11) from A3's ordinate supply.  Inputs:
the BRIDGE-SCOPE dossier (banked in flags 2026-07-30 00:49), the CLOSE-WAVE
STOP, port-freeze-0729.md (which never priced this stone — the freeze-gap
finding), second-road-freeze-0729.md D-5/D-8(iii) (which flagged the hole).
Status: v1 → overnight refuter pass → the morning council.  JYH has NOT
seen this freeze; nothing here is ratified.  The night executes only the
fork-neutral tail, and only on refuter confirmation.*

## 0. The re-diagnosis (what changed since the STOP)

The A4 STOP cited `M4DoorRow`'s two walls.  Both are DOWN at HEAD
(⟦WALL 1⟧ `hwinBand` deleted by the 7/28 counter-wave; ⟦WALL 2⟧ the
length gate is the landed graded split's own partition boundary).  The
real blocker of the per-χ route is the F5/F4 `q`-LINEAR gate pair
(`M4MeanSq.lean:626-630` at coefficient 32; `M4T0Discharge` at
coefficient 700) — precisely the route the port replaces.  So A4 is not
a stalled composition; it is the port's one unpriced stone, and its
design is the q=1 crossing χ-summed with the ordinate side fed by the
port instead of by `capFreeFloor3`.

## 1. THE RULED ROUTE — R1, the pointwise lift of the q=1 crossing

The crossing layer (`Lemma14*`, `Seam*`, `Parseval*`, `ThmA2*`) is
χ-BLIND (verbatim grep: zero χ) and MONOTONE in the row datum; the
saving-earning coupling lives entirely on the ordinate side, where A3
already put it.  So the lift is the landed three-move pattern
(exemplars: `m4_chiSummedShiftBlock_of_freeRow`,
`lemma12_meansq_all_chi`): free the constant per χ, instantiate at the
character's own datum, split the affine RHS and pay `φ(q)` where the
ledger says.  R2 (per-χ + F4) is DEAD as priced (F4 repairs half of one
of the two gates; the coefficient-700 gate has no repair).  R3 (a fresh
Σ_χ Parseval page) is REJECTED (coupling at a χ-blind monotone step buys
nothing).

**The target:** `m4_second_road_rs_ceiling` — the socket's inhabitant
must come in at `RSan H ≲ 2.5·10⁻¹⁰⁵/(loglog H)²` against the trivial
`4·arcDen 12 H = 4(log H)^{12}`.  No power of `arcDen`, no `q`: the
whole content of the second road.

## 2. The delta (D1–D5) and the wave plan

| # | statement | supplier ruling | ln | class | when |
|---|---|---|---|---|---|
| D1 | Σ_χ twin of `thm_a2_spine`/`thm_a2'_of_rows` — SLOT FORM: `hrowsΣ`, `hT0bandΣ` as free hypotheses, conclusion the Σ_χ window mean square | the three-move wrapper; four χ-free summands pick up `φ(q)` | 250–450 | B | **NIGHT** (fork-neutral, on refuter confirm) |
| D4 | socket wiring: `M4ChiSummedFreeRow` at the door datum (`chiFreeRowSq` byte-identical to `m4_door_meansq_carried`'s conclusion), the three base antecedents, the graded split at `doorRowFloor M`, the φ(q)-ledger arithmetic page | fixed by landed statements | 400–700 | B/C | **NIGHT** (fork-neutral, on refuter confirm) |
| D2 | Σ_χ row family (the `hrowsΣ` slot) | **per-leg, ruled below (§3)** | 1200–2200 | C | morning, post-council |
| D3 | Σ_χ T₀-band (the `hT0bandΣ` slot) | `lambdaChiSummatory_holds_gated` → the MemS J=2 four-fold decomposition (CS cost 4) → the O6 perturbation (**LANDED**: `MobiusChiRamare.lean`, μ·g_r = μ ∗ w_r + the hyperbola identity + the Rankin tail) → the `∀k ∀t` partial-sum form of `m4_hT0band_at_door`'s `hpiece` | 700–1400 | C | morning, post-council |
| D5 | *(contingent: only if D2 routes through the MR rows)* Σ_χ twin of `lemma12_meansq_mr_windowed{,_end}` — NOT a wrapper over `lemma12_meansq_all_chi` (global `hcoef` vs `SeamCoefW`; 3 rows vs 4; prefactor 3 vs 4) | — | 500–900 | B/C | only if forced |

Total (D1–D4): ~2.5–4.7k ln, class C overall.  All statements write
against the POINTWISE `HalaszPrimesChi C c q T` (the SLOT-WAVE landed at
ce24d31; K5 moot).

## 3. THE K3 RULING — each annulus leg's supplier, named BEFORE execution

The #1 shape risk: A3 delivers `Σ_χ ∫_A` only over
`A = (Ann ∖ ball) ∩ 𝒰`.  The complement legs must NOT route through the
per-χ `capFreeFloor3_liouChi_all` (the coefficient-28 gate returns).
The ruling, leg by leg:

* **`(Ann ∖ ball) ∩ 𝒰`** ← A3 as landed: `usetChi_window_meansq_gated`
  (the five named residue groups), extended along `usetChi_integral_to_branches`
  to the annulus form the rows demand.
* **the 𝒰-complement (typical) leg** ← the port's OWN χ-lifted 𝒰-ladder
  (`USetChi`/`USetChiTS`, the P-6 stones) — the χ-twin of the q=1
  `uset_TS_branch_meanvalue` → `hU_exit_of_branches` discrete→integral
  path.  NOT `capFreeFloor3`.  ⟦REFUTER CHECK R-A4-1: byte-verify the
  χ-lifted ladder actually covers this leg — that `exists_Tset_or_mem_Uset`'s
  χ-analogue partitions the annulus, and nothing in the chain imports the
  per-χ floor.⟧
* **the ball leg** ← the pointwise lift of the q=1 ball decay: the `8S²`
  absolute term is φ(q)-debited into the g-arm (K4).  The carried
  per-frequency sup `‖spolyA a t m‖ ≤ S·m` (`M4DoorRow.lean` ⟦THE
  T₀-BAND, NAMED⟧) is priced by D3's supplier at the same `(k,t)`-form —
  one datum, two consumers.  ⟦REFUTER CHECK R-A4-2: confirm D3's
  `∀k ∀t` form instantiates BOTH `hpiece` and the ball-leg sup, or price
  them separately.⟧
* **the far tail** ← `far_tail_crude` verbatim (χ-blind); the φ(q) fold
  is absorbed by `h ≥ 2^{M·Adoor M}` (free, as are summands 2 and 4).

## 4. THE K1 ARITHMETIC PAGE — the φ(q) leak and the g-arm bump

Summand 3 (`188133·(log X)^{−1/500}`) at Σ_χ becomes
`φ(q)·188133·(log X)^{−1/500}`.  Against the ceiling, in logs:
`loglog X ≳ 500·(12·loglog H + 254) ≈ 6000·loglog H + 1.3·10⁵`, vs the
current g-arm `144·loglog H + ~2·10³` — a ~42× coefficient bump on a
consumer-chosen knob.  The precedent for repaying φ(q) with log-X powers
is landed (`phi_debit_level_repin`: `φ(q)·(log X)^{−212} ≤ (log X)^{−200}`
at `q ≤ (log X)^{12}`).  **The claim to verify, not assume: the bump is
F5-NEUTRAL and gate-neutral** — g raises `x`, not `H`; the ruled 2³⁶
anchor and the spine conjunct (`loglog Hhi ≤ (loglog Hlo)⁵`) read only
`H`; the socket's third antecedent `x ≤ 16ω·arcDen·A` is suppliable at
any `x` (the ladder's `A` scales with `x`); and a LARGER `loglog X` only
eases every `… < loglog X` threshold.  ⟦REFUTER CHECK R-A4-3: walk all
11 gates of `m4_second_road` + the socket's three antecedents + the
tower cap at the bumped g; derive, don't affirm.⟧

## 5. The D3 range fit (checked at scoping, refuter to re-derive)

`LambdaChiSummatory`'s `q ≤ (log y)^{11}` at the x-scale base contains
`arcDen 12 H = (log H)^{12}` (y rides the x-ladder, `log y ≫ log H`);
`|t| ≤ ⌊√y⌋` contains `seamT0 X = (log X)^{1/45}` with room to spare.
The four-fold decomposition (`1_𝒮·λ` = a signed sum of four completely
multiplicative 1-bounded functions) costs CS 4, never `4^J`.  The
𝒮-block restriction is the O6 perturbation, whose carrier page is landed.
⟦REFUTER CHECK R-A4-4: the `hpiece` slot's demand is `∀ k ∈ [X_d, N]`,
`∀ |t| ≤ seamT0 X`, a bound `S₀·k` — verify `LambdaChiSummatory`'s rate
shape delivers `S₀ ≤ 2(C₁e^{−M₀/2e} + 4(log X)^{−1/2+1/1000})` at every
such `(k,t)` through the CS-4 fold and the O6 tail, including the small-k
corner `k` near `X_d`.⟧

## 6. The fork-neutrality claim (gates the night tail)

D1 and D4 commit to NOTHING in §3–§5: D1's slots are stated at the
Σ_χ shapes the crossing itself forces (the χ-sum of `thm_a2_spine`'s two
ordinate binders), and D4's wiring is fixed by landed statements
(`chiFreeRowSq` = the door conclusion, byte-identical).  Whatever
supplier wins any fork, these bytes stand.  ⟦REFUTER CHECK R-A4-5:
byte-check the claim — write the two Σ_χ slot shapes from
`ThmA2Spine.lean:394`'s actual binders and confirm no fork leaks into
them (in particular that the `hrows` T-quantification `∀ T, X/h ≤ T →
2T ≤ X` survives the χ-sum unchanged, and that the socket's graded split
does not force a supplier choice).⟧

## 7. What the morning council decides

1. Ratify R1 and the §3 leg-supplier rulings (or re-fork).
2. Ratify the K1 g-arm bump (~42×) as the honest φ(q) price.
3. D3's route as ruled (LambdaChiSummatory → four-fold → O6), or the
   alternative (a direct χ-twisted Perron re-run at the T₀-band — NOT
   recommended: a new analytic page where a landed rate suffices).
4. The D5 contingency trigger.
5. Fire A4-W2 (D2) and A4-W3 (D3), then A4-W4: the assembly —
   `m4_socket_discharged` shipped HONESTLY (the socket inhabited at the
   ceiling's grade, gates in-statement), then THE S11 COMPOSE under the
   ratified summit protocol.

*The refuter pass (REF-A4: R-A4-1..5) runs overnight; verdicts bank in
flags before the council.  — Sancho, 2026-07-30, the night watch.*
