# THE INTERFACE DESIGN BLOCK — the four scope reports, verbatim (2026-07-31 evening)
# Preserved from the workflow output for the freeze + refuter pass.



---

# ══════════ S1 ══════════

**VERDICT — THE TOWER IS ONE TERM, AND IT IS NOT THE `logloglog`.** The entire height-3 demand comes from a single summand of ONE of `budget_facts`' five conclusions: the `κ = H/(log H·logloglog H)` half of fact (iv) (`BudgetCore.lean:143-145`). In the ratio `κ/gcap` the `H` and the `log H` cancel **exactly** (kernel: P1), leaving `36·log 4/(ε⁶·logloglog H)` — so `logloglog H` alone must absorb a constant of size `10^19–10^31`. The other four facts (and the `log 2` half of (iv)) go through `hcore` (`BudgetCore.lean:192-197`) and need only **height 1**: `log H ≥ 2.2·10^31`, which sits INSIDE the register's ceiling `logloglog H ≤ 6.24` with ~190 orders of room (kernel: P7). `budgetX` is NOT the culprit: fact (iv) *as frozen* already forces `logloglog H ≥ 576·log4/(ε⁶β²)` (kernel: P2, exact, no slack) — `budgetX` overcharges by exactly 4×. Sharpening constants is dead: the sharpest conceivable re-derivation of the whole g/β chain, at `cD3 = 1` and every slice share 1, still demands `logloglog H ≥ 3·10^16` under the S2 ε-cap (P5) and `≥ 4·10^7` even at the absolute `ε = 1/2` (P6). **Charging in the double log does not close it either** (`log(1/(ε⁶β²)) ≈ 43.7 > 6.24`, 7× over). Only charging in the SINGLE log closes it — and that requires `g` to gain a full `log H`, i.e. a **Bennett/Bernstein tail replacing the Hoeffding range-square** in `FBridge`.

Probes: `/private/tmp/claude-501/-Users-jyh-projects-claude-salt/ea81b992-0821-4192-8f48-c0dcdcbc14c2/scratchpad/iface/s1-budget/Probe.lean` — 9 theorems, `lake env lean` green, `import Mathlib` only, no `sorry`/`native_decide`. (Repo untouched; scratch copy removed.)

---

## THE CHAIN, BYTE BY BYTE

**The demand's two halves** (`Salt/Entropy/Chowla/BudgetCore.lean:138-146`):
- `κ := H/(log H · logloglog H)` — produced by `entropy_decrement` (`Decrement.lean:49-56`), consumed at `SpineFinal.lean:632` and threaded into fact (iv) at `SpineFinal.lean:576-579, 626`.
- `gcap := ε⁶H/(18·(2·log 4)·log H) − log 2` — the concentration exponent, born at `Transport.lean:82` as `E = δ²·log H/(2·C₀·ε²H·(2/ε²+1)²)` and specialized at `Transport.lean:128-146` to `δ := ε²H/log H`, giving `ε⁶H/(18·C₀·log H)`; `C₀ = 2·log 4` from `circle_method_estimate` (`CircleMethod.lean:574,586`, witness `C = 1+2C₀`).

**The cancellation (P1, kernel):** `(H/(L·L3)) / (ε⁶H/(18·(2·log4)·L)) = 36·log 4/(ε⁶·L3)` — identically, for all `H, L, L3, ε > 0`. Both sides are `(H/log H) × scalar`. This is the crux: the demand is not "H large", it is a **pure constant inequality on `logloglog H`**.

**Which fact needs the tower.** `budget_facts` uses `hLLL` (the height-3 transfer) in exactly one place: `hA_demand` (`BudgetCore.lean:199-207`). `D_ii` (:209), `D_iv` (:223), `D_v` (:236) all route through `hcore` (:192-197), which needs only `4·c ≤ log H` — a **single** exponential. Delete/replace the `κ` summand and `budgetFloor` collapses from `⌈exp(exp(exp X))⌉₊` to `⌈exp(4X)⌉₊`.

**P2 (kernel, the decisive reduction).** From fact (iv) verbatim — `(H/(L·L3) + log 2)/gcap ≤ (β/4)²` with `0 < gcap` — one derives `576·log 4/(ε⁶β²) ≤ L3`. No `budgetX`, no `budgetFloor`, no proof internals. **The frozen contract IS the demand.** Catch #100 applies to the maestro's own framing: "weaken `budget_facts`' demand on H" is not available while conclusions (iv) stand; you must change the *conclusion*, i.e. the shape of `κ` or of `gcap`.

**The 4× of `budgetX`.** `budgetX` charges `2304·log4/(ε⁶β²)` (`BudgetCore.lean:199`) vs the forced `576·log4/(ε⁶β²)`. The 4 = 2 (`gcap ≥ F/2`, :~250) × 2 (the `κ`/`log 2` split, :~262). Recoverable, worthless: `10^31 → 2.5·10^30`.

---

## (1) WHERE THE `logloglog` IS BORN — INTRINSIC, but IRRELEVANT

Three candidate births; I checked all three at the bytes.

- **Tower step size** (`Tower.lean:87-90`): `H_{j+1} = H_j·⌊C₀·log H_j·logloglog H_j⌋₊`. Downstream of the threshold, not upstream: it exists to satisfy `hkey : ε²log4/m ≤ 1/(4·lg·L3)` (`Tower.lean:192`), i.e. the multiplier must beat the threshold.
- **Tao's shift/Fannes loss** — **NOT the source.** `budget_real` (`Step.lean:330-333`) proves the honest Fannes budget is `(3/2)·H·log2/(log H)² + log 2`, and *inflates* it to `H/(4·log H·logloglog H)`. The Fannes side permits any `φ(H) ≲ log H/4.16`; it is nowhere near binding.
- **The drop-sum divergence** (`Regime.lean:46-49, 98`) — **THIS is the birthplace.** With threshold `H/(log H·φ)`, `tower_step` (`Tower.lean:210-250`) yields drop `1/(2 log H_j·φ_j)` and forces multiplier `m ≳ C₀·log H_j·φ_j`. Writing `L = log H`, `u = log L`, the telescoped sum is `≈ ∫ du/(2·u·φ(u))`. `φ = logloglog H = log u` gives `(1/2)·logloglog u` — divergent, barely. `φ = loglog H = u` gives `∫du/(2u²)` — **convergent**, total `≈ 1/(2u₀) ≪ log 2`, so `hJcon` becomes unsatisfiable. (Derivation mine, not kernel-probed; the two ingredients — the step law and the summand — are at the cited lines.)

**Verdict (1): INTRINSIC to the entropy-decrement method as implemented, and not fixable by growing `φ`.** `φ` must sit on the `∫du/(u·φ)` divergence borderline. The admissible family is `lll H · llll H · lllll H · …`, each factor buying only `log`/`loglog` of the demand: stacking every iterated log gains ≈ `45 × 3.8 × 1.3 ≈ 220`, against a gap of `10^19`. Dead.

**But this does not matter.** The `logloglog` would be harmless if `κ/gcap` retained *any* `H`-decay. It is the exact cancellation (P1), not the triple log, that puts the constant at height 3.

---

## (2) `ε⁶` AND `β²` — WHERE THEY ENTER, AND AT WHAT HEIGHT

**`ε⁶` — all of it from the concentration side, and it is a Hoeffding artifact in one factor.** `Transport.lean:82`: `E = δ²·log H/(2·C₀·ε²H·(2/ε²+1)²)`. Decomposition at `δ = ε²H/log H`:
- `δ² → ε⁴`,
- `÷ |P_H| ≤ C₀ε²H/log H → ×ε^{-2}` (PNT-sharp; `fBridge_var_le_sharp`, `FBridge.lean:375-386`),
- `÷ R² = (H/p+1)² ≤ (2/ε²+1)² → ×ε⁴`.
Net `ε⁶`. **`R` is a RANGE, not a variance**: `fBridge_varTerm` (`FBridge.lean:198-206`) literally computes the Hoeffding half-width `((hi−lo)/2)² = (H/p+1)²`. The file's "sharp" refers only to the *cardinality* upgrade (`FBridge.lean:372-374`), never the tail.

**`β²` — the mass-slice bookkeeping.** `β := cD3·ε/(144·log 4)` (`SpineFinal.lean:621`). It is **not the door grade** — that is `c₀ = cD3/(16C)`, `δ₀ = c₀ε/(2K)` (`ConstantsExposed.lean:26-33`). `β` occurs ONLY as `budgetFloor`'s second argument and inside `hbudget1_witness`. It is `(S4 mass slice)/(2·boxGrade)`: `2·boxGrade·bracket ≤ (cD3/16)(εH/log H)` with `boxGrade = 2·log4·(2+ε²)·(H/log H)` (`OuterCombine.lean:42-43`), and `(2+ε²) ≤ 9/4` gives the 144. `β` enters squared because `bracket_close` (`BudgetCore.lean:83-113`) is an **AM–GM square root**: `2√(κ/g) + 2log2/g ≤ β`.

**Combination:** `ε⁶β² = cD3²ε⁸/(20736·log4²)` — the "ε⁻⁸ law" (`spine-budget-freeze.md:61`, labeled DERIVED-not-registered). And `ε` is itself capped by `cD3/(16C)` (`SpineFinal.lean` ε-arms; `C = 1+4·log4 = 6.545`), so the demand scales as **`cD3^{-10}`**. With the landed witness `cD3 = 1/4` (`WindowMertensLower.lean:62`, `refine ⟨1/4, …⟩`) and `ε` pinned to `1/500` (`ConstantsExposed.lean:187`): forced demand `≥ 10^30` (P3c, kernel).

**Could it be charged at a different height?** Answer to the brief's own hypothesis: **NO for the double log.** Charging `1/(ε⁶β²)` in `loglog H` means `loglog H ≥ 10^19`, i.e. `logloglog H ≥ 43.7` — 7× the register's 6.24. Even the *sharpest* version (P6, `4·10^7`) charged in `loglog H` gives `logloglog H ≥ 17.5`, still over. The register's window in the double log is `loglog H ≤ 513` (= `exp 6.24`). **Only the single log has room**: `log H ≤ e^{513} ≈ 10^{223}`, versus a height-1 demand of `2.2·10^{31}` (P7).

---

## (3) THE MINIMAL HONEST DEMAND OF THE SAME PROOF SHAPE

| stage | constant | source | recoverable |
|---|---|---|---|
| `budgetX` as written | `2304·log4/(ε⁶β²)` | `BudgetCore.lean:199` | — |
| **forced by frozen fact (iv)** | **`576·log4/(ε⁶β²)`** | **P2, kernel** | 4× |
| AM–GM-sharp bracket `(β/4)²→((β−2log2/g)/2)²` | `144·log4/(ε⁶β²)` | **P4, kernel** (contract change) | 4× |
| Hoeffding `(2+ε²)² ≥ 4` instead of `≤ 9` | ×`4/9` | `Transport.lean:141-146` | 2.25× |
| all four mass slices → S4 | `β` ×4 | `SpineFinal.lean:~665-700` | 16× |
| `cD3 = 1/4 → 1` | ×`cD3^{-10}` | `WindowMertensLower.lean:62` | `10^6` |

Composite sharpest form: `L3 ≥ 4096·log4³·(2+ε²)⁴/(θ²·cD3²·ε⁸)`.

Kernel-probed at candidate floors:
- **P5**: with `cD3 = 1`, `θ = 1`, `ε ≤ cD3/(4C) ≤ 1/26` (the S2 coupling `C·ε² ≤ slice`) → `logloglog H ≥ 3·10^16`.
- **P6**: drop the S2 coupling entirely, run at the absolute `ε = 1/2` (`ChowlaRegime.heps1`, `Regime.lean:78`) → `logloglog H ≥ 4·10^7`.
- **P3a**: from the *frozen* contract, `ε = 1/2` and `β = 1` (β's true frame value is `≈ 6·10^{-6}`) → `≥ 51000`.
- **P3b**: to reach `logloglog H ≤ 6.24` at `ε = 1/2` the contract needs `β ≥ 90`. `β ≤ cD3/(288·log4) < 10^{-3}`.

**Answer (3): `4·10^7` is the floor of this shape. Every constant on the table is worth ≤ `10^9` combined; the gap is `10^7` after all of them.** No re-derivation with today's sharper constants reaches 6.24.

---

## (4) `β = cD3·ε/(144·log 4)` — PLUMBING, AND ALREADY NEARLY MAXIMAL

**The flags entry's pre-analysis is wrong on this point** (`flags.md:18658-18659`, "beta (IS the door grade, small by design)"). `β` is the bracket budget, not the door grade. Grep of `144 * Real.log 4` returns only `budgetFloor` call sites and `SpineFinal.lean:621`.

Can the budget run at its own larger `β`? **No, and the reason is structural, not plumbing.** `β` is pinned by the mass ledger: the total correlation mass is `c₁·εH/log H` with `c₁ = cD3/4` (exact: `(1/2)·Σ_p 1/p ·H·|X|` with `Σ ≥ cD3/log H` and seed `|X| ≥ ε/2`, `HBudget.lean:705`), and the four errors (S1 door, S2 circle-method `ε²`, S3 good-event `δ`, S4 bracket) must fit under it. `β` = S4's share ÷ `2·boxGrade`. The only enlargements are the slice share (≤ 4×) and `(2+ε²) → 2` (≤ 1.125×) — a combined ≤ 20× in `β²`, already counted above. Decoupling `β` from the door is free (they were never coupled) and buys **nothing**.

One genuine, uncounted slack: `δ` is *calibrated* to `ε²H/log H` (`Transport.lean:128`) but is only *required* to be ≤ its slice `(cD3/16)·εH/log H`. At the ε-cap the headroom is exactly `C = 6.545`, and `g ∝ δ²`, so raising `δ` to its slice buys `C² ≈ 43×`. Real, small, class B–C.

---

## (5) REPAIR DIRECTIONS, WITH HONEST PRICES

**D1 — BENNETT/BERNSTEIN TAIL FOR THE F-BRIDGE. [D-tier. THE ONLY DIRECTION THAT CHANGES THE HEIGHT.]**
Replace `hoeffding_residueProj` (`Concentration.lean:218`) / `fBridge_varTerm` (`FBridge.lean:198`) — which charge the full range `(H/p+1)²` — by a Bennett bound using the true variance. The `residueProj` components across distinct window primes are CRT-independent, so the hypothesis is in place. Mechanism: at `δ = ρεH/log H` the deviation is deep in the Poisson regime (`Rδ/(Nσ²) ∼ ε³H`), where the Bennett exponent is `≈ (δ/R)·log(Rδ/Nσ²) ≈ (ρε³H/(2log H))·log H = ρε³H/2` — **the `log H` cancels**, so `g` gains a full `log H` and `κ/g ∝ 1/(log H·logloglog H)`. The demand moves to the SINGLE log, where the register has `10^{223}` of room. Price: a Bennett/Bernstein inequality for independent bounded variables — not in mathlib (`Mathlib/Probability/Moments/` has `SubGaussian` only); salt's own Hoeffding kernel would need a sibling. Then `Transport.lean`, `FBridge.lean`, `BudgetCore.lean`, `SpineFinal.lean`'s witness all re-derive. **UNVERIFIED — my heuristic, flagged as such; the exponent computation is the thing a refuter must kill first.** (Honest hazard: the variance bound must be uniform over the adversarial Liouville pattern `v`; the worst-case pattern gives `σ_p² ≈ H²/p³`, a factor `p ≈ ε²H/2` below `R²` — enough to enter the Poisson regime, which is where the `log H` cancellation lives.)

**D2 — DECOUPLE `κ` FROM `H/log H`. [D-tier, the tower scoper's face.]** The cancellation is exact because `κ` and `gcap` are both `(H/log H) × scalar`. Anything that gives `κ` a smaller `H`-order kills the tower. Blocked from the entropy side by the drop-sum divergence (question 1). Only live if the MI budget is consumed at a *different* scale from the mass — i.e. the `S16BaseScaleCap` decoupling named in `flags.md:18667-18669`.

**D3 — RAISE `δ` TO ITS SLICE. [B/C-tier.]** `Transport.lean:128`'s calibration `δ := ε²H/log H` is a choice; the constraint is `δ ≤ (cD3/16)·εH/log H`. Buys `C² ≈ 43×` in `g`. Moves `10^{31} → 2·10^{29}`. Cheap, correct, cosmetic.

**D4 — RECOVER THE 4× AND THE BRACKET 4×. [B-tier.]** `budgetX`'s 2304 → the forced 576 (P2); then the contract's `(β/4)²` → `((β−2log2/g)/2)²` (P4, kernel-proved here, drop-in for `bracket_close`). Total 16×. Requires re-freezing `budget_facts` conclusion (iv) — a blueprint statement change, Fable/human tier. Moves `10^{31} → 6·10^{29}`.

**D5 — SHARPEN `cD3`. [C-tier, highest leverage per unit work among the numeral moves.]** The demand is `∝ cD3^{-10}`. `primeWindow_sum_inv_ge` witnesses `1/4` (`WindowMertensLower.lean:62`) against a true value `≈ log 2 ≈ 0.693` (its own docstring, `:30`). `1/4 → 0.693` is `10^{4.4}`. Requires a real Mertens-window improvement, not bookkeeping. Moves `10^{31} → 4·10^{26}`. **Still `10^{26}` short.**

**IMPOSSIBLE AT THIS DESIGN:** D3+D4+D5 together, plus every constant in the table at its theoretical optimum, plus `ε` at the absolute `1/2` in violation of its own S2 cap, bottoms out at `logloglog H ≥ 4·10^7` (P6, kernel) against the register's `6.24`. **Any repair that leaves `κ` at order `H/log H` and `g` at order `ε^k H/log H` fails by at least `10^7`, for every `k` and every constant.** The shape that must move is the `log H` in `g`'s denominator — D1 — or the `H`-coupling of the register's cap — D2.

---

# ══════════ S2 ══════════

VERDICT: **THE TOWER LAW IS NOT THE WALL — AND IT IS NOT INTRINSIC.** The cubic/quartic `λ₊ ≥ λ₋^{3.74}` is an artifact of ONE choice (the multiplier `⌊C₀·log H·logloglog H⌋` in `chowlaTower`); the landed `step_ineq_3_11` is parametric in `k` and its multiplier is free down to `k = 2` (kernel: `probe_shallow_step`). A `k = 2` tower gives an ADDITIVE window that fits the register's 7.1448 budget with room. But the redesign buys nothing, because the DESIGN-INDEPENDENT floor is `λ₊ − λ₋ ≥ 0.9·logloglog H₋` (kernel: `probe_window_floor`) — a lower bound on the window proportional to the very quantity S1's floor drives to `≥ 270270` (kernel: `probe_budgetX_floor`). Composing: **every regime the spine can build, at the shallowest tower that exists, has `λ₊ − λ₋ ≥ 243243` against the register's `≤ 7.1448` — deficit 34043×** (kernel: `probe_the_one_line`). Q3's reading is REFUTED both ways (below). Probes: `/private/tmp/claude-501/-Users-jyh-projects-claude-salt/ea81b992-0821-4192-8f48-c0dcdcbc14c2/scratchpad/iface/s2tower/{P1,P2,P3,P4,P5}.lean` — 12 theorems, all `[propext, Classical.choice, Quot.sound]`.

---

## (1) THE FORCING, RE-VERIFIED AT THE BYTES

| object | file:line | fact |
|---|---|---|
| `chowlaTower` | `Salt/Entropy/Chowla/Regime.lean:39-45` | `H₀ = a·H₋`, `H_{j+1} = H_j·⌊C₀·log H_j·logloglog H_j⌋₊` |
| `towerDropSum` | `Regime.lean:47-51` | `Σ_{j<J} 1/(2·log H_j·logloglog H_j)` |
| `hfit` | `Regime.lean:94` | `chowlaTower C0 a Hlo J ≤ Hhi` — bounds `H₊` from BELOW |
| `hJcon` | `Regime.lean:98` | `log 2 < towerDropSum C0 a Hlo J` |
| crossing law, lower | `TowerExport.lean:502` | `(1−1/20)·½·(w_J−w₀) ≤ S_J` |
| crossing law, upper | `TowerExport.lean:539` | `S_J ≤ (1+1/20)·½·(w_J−w₀)`, `w = log v`, `v = logloglog H` |
| companion | `TowerExport.lean:673` | `tower_loglog_ge : λ₋³ ≤ λ₊` |
| export | `TowerExport.lean:617` | `tower_loglog_le : λ₊ ≤ λ₋⁵` (9/2 twin at `:770-800`) |

The forcing re-derives exactly: `log 2 < S_J ≤ (21/40)(w_J−w₀)` ⟹ `w_J−w₀ > (40/21)·log 2 = 1.320280` ⟹ `v_J/v₀ > e^{1.32028} = 3.74366` ⟹ **`λ₊ ≥ λ₋^{3.7436}`**. WIDTH-SCOPE's `probe_regime_width_forced` (`scratchpad/width/probe_width.lean:9`) re-runs green; its `K = 3` spends the budget against `log 3 < 6/5`, a weakening.

**HONEST MINIMAL EXPONENT: 3.7436** — kernel-probed as `3.74` (`P1.lean:32 probe_tower_exponent_374`; `P1.lean:76 probe_no_cubic_regime` shows NO `ChowlaRegime` has `λ₊ < λ₋^{3.74}`). The bracket is `[3.7436, 4.4077]` (upper = `exp(89/60)`, the `tower_loglog_le` budget line `(40/19)log2 + 7/300`); the continuum value is **4** (`∫dL/(2L·logL·loglogL) = ½·Δ log logloglog H`). So: landed `3` — weakening; `3.74` — the theorem; `4` — the truth; `4.41/4.5/5` — the exported upper laws. **The `λ₋³` in every register docstring is 0.74 of an exponent softer than reality.**

## (2) WHAT THE TOWER IS FOR — AND THE J-TRADEOFF IS REAL

The pigeonhole (`Endpoints.lean:98-128`, consumed at `Decrement.lean:49`) needs exactly three things: `e(H₀) ≤ log 2`, `e(H_J) ≥ 0`, `log 2 < towerDropSum`. **Nothing in it mentions `J` or depth.** The depth is entirely an artifact of the exchange rate between drop and growth.

The decisive reduction, at the bytes: `step_ineq_3_11` (`Salt/Entropy/Chowla/Step.lean:696-706`) is
```
e(kH) ≤ e(H) − I/H + (ε²·log 4)/k + 1/(4·log H·logloglog H)
```
for **every** `k ≥ 1`. Its ONLY `k`-dependence is the error `ε²log4/k`. `tower_step_of` (`Tower.lean:152`) then imposes `hmL : C₀·L·v − 1 < m` — **that hypothesis is a choice, not a necessity**: the arithmetic only needs `k ≥ 4·log 4·ε²·L·v`, which at `ε ≤ 1/2` happens to be `≥ 1.386·L·v`, so the landed multiplier is minimal *given* `ε ≤ 1/2` — and only then.

- KERNEL (`P2.lean:27 probe_shallow_step`): at `k = 2`, under `ε²·log 4 ≤ 1/(2·log H·logloglog H)`, the drop is the SAME `1/(2·log H·logloglog H)` the landed step delivers. No modification of `step_ineq_3_11`.
- KERNEL (`P2.lean:78 probe_shallow_exchange`): a `k=2` step advances `u = loglog H` by `≤ log2/L` while paying the same summand — so drop-per-unit-window is `1/(2·log2·v)` instead of the landed `1/(2·u·v)`: **a factor `u/log 2 ≈ 400` more decrement per unit of window travel at `λ₋ = 277`.**
- KERNEL (`P2.lean:98,111`): at the landed witness `λ₋ = 277.2589`, a window of width **5.9** clears `log 2` — against the register's 7.1448, 17% of room. (Landed tower at the same base: `λ₊ ≥ λ₋^{3.74} = 5.6·10⁹`.)

**WHAT `J` COSTS DOWNSTREAM: NOTHING.** Census of `R.J` readers: `Tower.lean:130,210,247,252-263`, `Endpoints.lean:100-122` — the spine only. In the register it appears exactly twice, both as a verbatim carry in a structure copy (`RegimeParam.lean:509`, `Salt/MR/RegimeHead.lean:112`). No error accumulates per level either: every error in `step_ineq_3_11` is per-step and already absorbed inside the summand (`hheadroom'`, `hPHheadroom` are `H`-uniform, `J`-free — `Regime.lean:103,116`). **The J-riders the question asks about do not exist. A `1.6·10^{123}`-level tower costs the register zero bytes.**

## (3) THE JOINT SHAPE — Q3's READING IS WRONG IN BOTH DIRECTIONS

**(a) `λ₋³ ≤ log log 𝒫₂` at `K = 32M` is NOT a compatibility certificate.** `s16_recut_cap_demand_met` (`Salt/MR/S16Budget.lean:730`) is kernel-true, but the same file's `:660-670` states the companion: the `M`-window gives `K ≤ 0.55·λ₋ − 41 = 111.5` at that witness, while the cap needs `K ≥ 1.443·λ₋³ − 413 = 3.075·10⁷`. `Mfl` and `S16BaseScaleCap_gk` are jointly unsatisfiable at every `K`. So the tower face is NOT "already certified compatible at shallow λ₋".

**(b) But an ADDITIVE tower DOES dissolve that particular collision** — at the landed witness only: `λ₊ = λ₋ + 0.9·log λ₋ = 282.3` ⟹ cap demands `K ≥ 1.443·282.3 − 413 < 0`, M-window allows `K ≤ 111.5`. Joint solution `K ∈ [0,111]`. The general form: `1.443·λ₊ ≤ 0.55·λ₋ + 372` with `λ₊ ≥ λ₋` forces `λ₋ ≤ 417`. So the additive tower buys a *real* register-side dissolution — up to `λ₋ ≈ 417` (S16 face) and `λ₋ ≈ 1690` (the 7.1448 width face).

**(c) And it is then killed by S1's floor, on the SAME line.** Two independent kills:

*Kill 1 — the ε-axis (the shallow road's own price).* The `k=2` step needs `ε² ≲ 1/(2·log4·log H·logloglog H)`, i.e. `ε ≲ e^{−λ₋/2}` (at `λ₋ = 277`, `ε ≤ e^{−139}`). `budgetX` (`BudgetCore.lean:21`) carries `1/ε⁶`, and its β is `cD3·ε/(144·log 4)` (`HloExport.lean:433,464`; `SpineFinal.lean:604`), making it `ε^{−8}`. KERNEL (`P3.lean:19 probe_shallow_budget_kill`): no `(λ,ε,β)` satisfies both, at **every** `λ ≥ 1` — the `ε^{−6}` alone suffices, `β` never used. KERNEL (`P3.lean:67 probe_shallow_budget_price`): the induced `budgetX ≥ 24000·e^{3λ}`, so the floor then demands `λ ≥ exp(24000·e^{3λ})`. **No fixed point, by an exponential, at every λ.**

*Kill 2 — the design-independent one (this is the giant).* Forget `ε`. Any tower has multiplier `≥ 2` per level (`step_ineq_3_11` needs the `k`-fold block structure; `k=1` is a no-op in the telescope), and every level pays at most the landed summand `1/(2 L_j v_j)`. KERNEL (`P4.lean:49 probe_window_floor`): then
> **`λ₊ − λ₋ ≥ (15/8)·(log 2)²·logloglog H₋ = 0.90085 · logloglog H₋`**

stated on abstract sequences — it holds for EVERY tower design, not just `chowlaTower`. (The absolute variant, allowing the maximal per-level drop `1/(L v)`: `≥ 0.4504·logloglog H₋`.) Against the register's window `W`: `logloglog H₋ ≤ W/0.9 = 7.94` (`P4.lean:99 probe_v_ceiling`). And KERNEL (`P5.lean:12 probe_budgetX_floor`): `budgetX ≥ 270270` at EVERY `0 < ε ≤ 1/2` (the regime's own `heps1`, `Regime.lean:78`) and every `β > 0` — `1/ε⁶ ≥ 64` alone, `4158·65 = 270270` exactly. Composition, KERNEL (`P5.lean probe_the_one_line`): **`λ₊ − λ₋ ≥ 243243`.**

**THE ONE LINE:** the tower converts the register's window budget into a ceiling on `logloglog H`; the budget floor is a floor on the same `logloglog H`. `7.94` vs `270270` — **34043×**, definitional. At the fired `ε = 1/500`: `budgetX ≥ 6.5·10¹⁹`, window floor `5.9·10¹⁹`, deficit `8.2·10¹⁸×`.

**Structural note (analysis, NOT kernel — flagged):** `budget_facts` fact 4 (`BudgetCore.lean:138`, the `(β/4)²` line) has numerator `H/(log H·logloglog H)` — *literally the headline threshold* — over the D3 energy `ε⁶H/(36 log4·log H)`. So the floor's real content is `g ≥ 576·log4/(ε⁶β²)` where `g` is the headline's THIRD FACTOR; and the tower floor is `λ₊−λ₋ ≥ 0.45·g`. **The third factor cancels**: `λ₊ − λ₋ ≥ 259/(ε⁶β²)`, a window floor mentioning only `ε` and `β`. Weakening or strengthening the headline's `logloglog H` moves both sides identically. This is why no reshaping of the threshold (the obvious next idea) can help — verify before spending on it.

## (4) THE MINIMAL TOWER — THE BUILDER DOES NOT OVERSHOOT

`chowlaRegime_exists_param_gen` (`RegimeParam.lean:386`) returns `R.Hhi = chowlaTower 2 1 R.Hlo (Jof R.Hlo)` — an EQUATION; at `Jof = towerJmin` (`TowerExport.lean:729 chowlaRegime_exists_param_tower`) `H₊` is *exactly* the minimal crossing tower value. There is no builder slack to recover. And `λ₊ = λ₋³` exactly is impossible: `3 < 3.7436` (kernel, `P1.lean:76`). The only slack is in the EXPORTED upper law: landed `K = 5` and the `9/2` twin against an honest `4.4077`. Re-cutting `9/2 → 4.42` is a 30-line arithmetic twin (`three_halves_lt_log_nine_halves` pattern, `TowerExport.lean:786`) worth 1.8% of exponent — **worthless against a 34043× deficit. Do not fly it.**

## (5) DIRECTIONS, WITH CLASS AND HONEST PRICE

1. **THE SHALLOW TOWER (`k = 2`), as a construction — SOUND, class C, ~800–1200 ln, and it BUYS NOTHING ALONE.** New recursion + a `towerDropSum₂` potential `u = loglog H` (easier than the landed `w = log v`: `P2.lean:78` is the whole per-step law), new builder, re-point `hJcon`. Dissolves the 7.1448 width collision at `λ₋ ≤ 1690` and the S16 `K`-collision at `λ₋ ≤ 417`. **Priced only as a package with (2) or (3); alone it dies at the ε-price (`P3`).**
2. **BREAK THE ε-COUPLING (split the residue-window ε from the budget's ε).** The tower's ε is the `𝒫_H` window parameter; the budget's is the same `R.eps` field (`HloExport.lean:464`). A two-ε regime is the only way the shallow road survives Kill 1. Note (favourable, analysis-tier): the Mertens input `cD3/log H ≤ Σ_{p∈𝒫_H} 1/p` (`HloExport.lean:248`) is a DYADIC window sum ≈ `log2/log(ε²H)` — first-order **ε-independent**, so shrinking ε does not obviously kill the D3 leg. **Class D. Does not touch Kill 2.**
3. **RE-DERIVE `budgetX`'s `ε^{-6}` / the fact-4 ratio line.** The single highest-value object in the campaign under my face: it is what stands between an additive tower and the register's window, and it is the ONLY surviving wall after (1). But `budgetX` is a Captain-tier freeze ("enlargeable, never shrinkable"), and Kill 2 shows even `budgetX`'s DEFINITIONAL minimum `270270` (forced by `ε ≤ 1/2` alone) overshoots the register's `7.94` by 34043×. **So the re-derivation must beat 270270 → 7.94, i.e. kill the `1/ε⁶` factor entirely, not shrink it. Class D, and the target is a shape not a constant.**
4. **Sharpen the exported `K` (5 → 9/2 → 4.42).** Class A/B, ~30 ln. **DO NOT FLY** (1.8% of exponent).
5. **IMPOSSIBLE AT THIS DESIGN — name it as such.** Any road that keeps (i) `step_ineq_3_11`'s `ε²·log4/k` error shape, (ii) the `log 2` entropy ceiling, and (iii) `budgetFloor` in the `H₋` floor, has `λ₊ − λ₋ ≥ 243243` as a THEOREM (`P5.lean probe_the_one_line`). No tower redesign, no `C₀`, no `a`, no `J`, no multiplier schedule, no exponent re-export touches it. The register must supply a window of `≥ 243243` in `loglog H`, or one of (i)/(ii)/(iii) must go.

**CARRIED, NOT KERNEL (check before consuming):** the `7.1448 = log(1280·log2/0.7)` width ceiling is LAMBDA-RECON prose (`flags.md:17972-17982`, docstring at `Salt/MR/S15Compose.lean:60,795`) — my floor law `P4.lean:49` is stated parametrically in `W`, so any register width plugs in. The `K ≤ 0.55·λ₋ − 41` M-window line is prose (`S16Budget.lean:667`), and that file itself marks the `Mfl` read `⟦NOT KERNEL-CERTIFIED⟧` (opaque band constant `C`).

---

# ══════════ S3 ══════════

**VERDICT.** The register's honest maximal `λ₋` at symbolic `M` is **`λ₋ ≤ 20048`** (register alone; binding face = `anchor` × `half` × tower) and **`λ₋ ≤ 13381`** once the carried base-scale cap is included (binding face = `S16BaseScaleCap_gk` + the sharp socket floor + the frame's `A_gate_logK`). The maestro's pre-analysis is CONFIRMED to 3 digits (~2e4 / λ₋²≲1.8e8 → 1.79038e8). The frame ceiling **DOES scale with `log₂M`**: `K ≤ 1.7896·10⁸·(Nat.log 2 M + 1)`, kernel-green; the corpus's `K ≤ 1.7·10⁸` (94 sites) is that bound's `M=1` pin. Consequently the flags entry's "register permits logloglog H ≤ 6.24" (from `s16_audit_hcap_wall`'s `λ₋≥492`) is an **under-read by 3.3 in the triple log** — honest is 9.906 / 9.502. Verdict on the gap: UNCHANGED (6.5e19 vs ~9.9). **But the ceiling is not structural**: it is ONE definition, `Adoor M := 2^36·(Nat.log 2 M + 1)` (`DoorFrame.lean:84`). Re-cut it to grow polynomially in `M` and the cubic collision dies for every `λ₋ ≥ 50` — kernel-probed. At this design "raise the ceiling to `λ₋ ~ 50·e^45`" is NOT impossible; it costs one definition + one wide numeral re-cut.

---

## 1. The faces, at symbolic `(λ₋, λ₊, L = Nat.log 2 M, K)`

`λ₋ = log log R.Hlo`, `λ₊ = log log R.Hhi`, `Adoor M = 2^36·(L+1)` (`Salt/MR/DoorFrame.lean:84`, cast at `:96`), `doorRowFloor M = M·Adoor M` (`Salt/MR/M4DoorRow.lean:462`), `s13GK K M = 3072·2^K·M` (`Salt/MR/GLever.lean:59`).

The register is `S15Sel''_gk` (`Salt/MR/S15Compose.lean:2564`), the live one on the final object (`Salt/MR/S16Budget.lean:619`).

| face | file:line | exact inequality | what it caps | probe |
|---|---|---|---|---|
| **anchor** | `S15Compose.lean:2585`, frame form `M4ArithRho.lean:195` | `14λ₊ + log(1/ρ) + 33 ≤ 3.9e9·(L+1)` | `λ₊ ≤ 2.78571e8·(L+1)` — **SHARPEST register λ₊-cap** | `faceA_anchor` ✅ |
| **lvl** | `S15Compose.lean:2591` | `26 + 14λ₊ + ⅓·loglog Q₁ + log(1/ρ) ≤ (1/12)·Adoor M·log2` | `λ₊ ≤ 2.83530e8·(L+1)` (1.8% slacker) | `faceB_lvl` ✅ |
| **gRows** | `S15Compose.lean:2573` | `242·λ₊ ≤ Adoor M` | `λ₊ ≤ 2.83965e8·(L+1)` | `faceC_gRows` ✅ |
| **gP1** | `S15Compose.lean:2588` | `29 + log Ct + 14λ₊ ≤ Adoor M·log2 + log ρ` | `λ₊ ≤ 3.40234e9·(L+1)` (12× slack) | `faceD_gP1` ✅ |
| **half/winFit** | `S15Compose.lean:2580`; law at `S14Compose.lean:123,309,346` | `0.7·M·Adoor M + 3log(1/ρ) ≤ (log H₋)/2` | **the ONLY M-upper**: `L+1 ≤ λ₋/log2 − 35` | `faceE_half` ✅ |
| **cap+frame** | `S16Budget.lean:467` + `S13CapGrid.lean:201` + `SeamCalibrationK.lean:173` | `e^{λ₊} = log H₊ ≤ log𝒫₂/12 = 2^K(L+1)M·2^46·log2` | `λ₊ ≤ 1.241e8·(L+1)` — **2.25× sharper than anchor** | `faceF0_size`, `faceF_cap` ✅ |
| **blk** | `S15Compose.lean:2577`, def `S13FramesA.lean:1129` | `14427+64+8(L+1)+400(A·G·M)² + 1 + 18λ₊ ≤ 4⌊ε²H₊⌋` | K-upper `K ≲ e^{λ₊}/(2log2) ≳ 3.7e21` — **NOT the binder**, ~13 orders looser than the frame | analytic |
| **rho / bfloor / mfloor / x0M** | `:2583/:2571/:2569/:2575` | `−log ρ ≤ 1e14`; `24Cg/δ₀ ≤ M`; `Mfl(=2) ≤ M`; `x₀ ≤ 2^{doorRowFloor M}` | no λ-content | — |

**Structure in one line:** every λ₊-cap is `λ₊ ≤ c·Adoor M` (`c` = 1/246.7, 1/242.4, 1/242, 1/20.2, and 1/554 for the cap chain); the single M-upper is `log₂(M·Adoor M) ≤ 1.4427·λ₋ − const`.

## 2. The frame ceiling DOES scale (the brief's explicit question)

`A_gate_logK` (`Salt/MR/SeamCalibrationK.lean:173`) at the door+lever instance (`Salt/MR/DoorFrame.lean:352`, `DoorFrameH1.lean:520`) closes as
```
16·((L+3)log2 + (2L+52+K)log2)  ≤  (1/24)·(68719476736·(L+1)·log2 − 1)
```
i.e. `(48L + 880 + 16K)·log2 ≤ (1/24)(2^36(L+1)log2 − 1)` — the RHS carries the `(L+1)` **inside `Adoor`**, the LHS does not. Kernel:
- `p1a_Agate_scaled`: **passes** at `K ≤ 1.789e8·(L+1)` ✅
- `p1b_Agate_sharp`: **fails** at `K = 1.79e8·(L+1)` ✅ (so 1.7896e8 is sharp to 4 digits)
- `p1c_calFrameK_satisfiable_door_gk_scaled`: the **full `CalFrameK` inhabitant**, byte-for-byte `calFrameK_satisfiable_door_gk` with only `hK` weakened to `K ≤ 178900000 * (Nat.log 2 M + 1)` — **GREEN** ✅

So `K ≤ 170000000` is a *selection numeral read at `M = 1`*, not a structural ceiling. This is why `s16_audit_hcap_wall` (`S16Budget.lean:1015`, `492 ≤ λ ⇒ (K+413)log2 < λ³` for `K ≤ 1.7e8`) is true as stated but must not be read as the register's ceiling.

## 3. The joint ceiling, kernel-probed

`joint1_anchor` ✅ — `50 ≤ λ₋`, `L+1 ≤ λ₋/log2`, anchor, `λ₋³ ≤ λ₊` ⇒ **`λ₋ ≤ 20048`**
`joint1_sharp` ✅ — at `λ₋ = 20100` the anchor face already gives `λ₊ < λ₋³`. Not a lazy under-read.
`joint2_cap` ✅ — with the cap chain instead of the anchor ⇒ **`λ₋ ≤ 13381`**

**The composite, against the corpus's own objects** — `P3.s3_ceiling_joint`, GREEN:
```
S15Sel''_gk K … R M  +  S16BaseScaleCap_gk K R M  +  (K ≤ 1.789e8·(log₂M+1))
  +  loglogFloor50 ≤ R.Hlo  +  50 ≤ λ₋  +  λ₋³ ≤ λ₊
⟹  λ₋ ≤ 13381
```
It routes through the corpus's real machinery: `s13_MSelect'_of_halfWindow_gk` → `s14_window_floor_of_winFit` → `s14_socketBase_witness` → `s13CapGrid_Lambda_sharp` (the SHARP floor `½·log H ≤ loglog X_d`, catch #100 honored — NOT the arm's `7000λ₊`) → `s16_logP2` → `half`. Axioms of every landed input: `[propext, Classical.choice, Quot.sound]` (AX.lean).

In triple-log terms: register alone `logloglog H₋ ≤ log 20048 = 9.906`; with the carried cap `≤ log 13381 = 9.502`. Against `budgetX`'s `6.5e19`. The working point sits at `λ₋ = 277.2589` (`S15Witness.lean:824`, `s15WitFloor2 = ⌈e^{2^400}⌉` at `:787`) — **72× below the register's own ceiling**, so the register is *not* what pins the working point.

## 4. Statements vs selection lines

**FROZEN STATEMENTS (expensive):**
- `CalFrameK.A_gate_logK` — `SeamCalibrationK.lean:173`, the port of MR condition (2). The *inequality* is frozen; its side-condition numeral is not.
- The sharp socket floor `√H ≤ log A` ⇒ `½·log H ≤ loglog X_d` — `S13MSelect2.lean:182,240`; `S13CapGrid.lean:201`. Rooted in the **regime's** `hPHheadroom` (`Salt/Entropy/Chowla/Regime.lean:116`) + `SocketBase`'s x-scale (`M4Assembly.lean:431-434`). Spine-side, not register-side. NOT re-cuttable here.
- The window law `2^{doorRowFloor M} ≤ H` — `SocketBase` fields `doorRowFloor M ≤ j`, `2^j ≤ A` (`M4Assembly.lean:432-433`), `s14_logH_ge_of_socket` (`S14Compose.lean:123`). Content: `log₂ Q₁ ≤ 0.714·log H₋` where `Q₁ = P₁^M = 2^{M·Adoor M}` — the door's level-1 modulus must fit under the H-window. Structural.
- The anchor's SHAPE — `DoorArithFrameRho.anchor` (`M4ArithRho.lean:195`), supplied by `doorGrade_summand2_priced_rho` (`M4ArithRho.lean:282`), which prices `1787702400·a2Level1 M·e^{14λ}` ≤ ρ/8 with `a2Level1 M = (log Q₁)^{1/3}/P₁^{1/12}`. The `3.9e9·(L+1)` **is** `Adoor M·log2/12` rounded down — so it moves *automatically* with `Adoor`, and the proof is symbolic in `Adoor M` except through `Adoor_cast`.

**SELECTION-REGISTER LINES (cheap):**
- All 12 fields of `S15Sel''_gk` (`S15Compose.lean:2564-2594`) — demands on the witness `M`, each with a named supplier. At any `λ₋ ≤ 2e4` only `anchor` and `half` are within 10× of binding.
- `S16BaseScaleCap_gk` (`S16Budget.lean:467`) — **carried, underived**, at `/24` with a stated 1.5× margin over what `s16_budget_num` spends. Cheapest of all.
- `K ≤ 170000000` — 94 sites, kernel-proved re-cuttable (P1c).

**DEFINITIONS = the real knobs:** `Adoor` (`DoorFrame.lean:84`), `doorRowFloor` (`M4DoorRow.lean:462`), `s13GK` (`GLever.lean:59`), `s13BlockExp_gk` (`S13FramesA.lean:1129`).

## 5. Directions, with honest prices

**D1 — `Adoor M := 2^36·M` (the knob).** `half` then reads `0.7·2^36·M² ≤ e^{λ₋}/2` ⇒ `M ≤ e^{λ₋/2}/310300`; the anchor's RHS becomes `∝ M`, so `λ₊ ≤ 2.786e8·M ≥ 696·e^{λ₋/2}`. Kernel: `P2.shape_probe_Adoor_linear` ✅ — `λ₋³ ≤ 2.786e8·M` for **every `λ₋ ≥ 50`**. The collision disappears. What breaks: `A_gate_logK` gets strictly easier (RHS grows like `M`, LHS like `log M + K`; the K-ceiling becomes `≈1.79e8·M`); `blk`'s `400(A·G·M)²` grows to `M⁶` but is priced against `H₊ = e^{e^{λ₊}}` — an entire exponential of room; `gRows/lvl/gP1/x0M` all get easier. **Price:** re-derive 4 arithmetic lemmas — `Adoor_cast` (13 sites), `calE_door_two` (38), `log_calE_door_two(_gk)` (16), `log_four_M_door` (10). `Adoor_ge` / `Adoor_ge_old` / `one_le_Adoor` (97 sites) **survive unchanged** because `Adoor` only grows. **Class B, wide.**

**D2 — free the level-1 anchor `A` entirely (maximal).** `A` is bounded only by the window law `M·A ≤ 0.714·e^{λ₋}`; at the register's own `M`-floor (`Mfl = 2`, `S11HoistGrade.lean:327`) that permits `A ≤ e^{λ₋}/2.8`, hence `λ₊ ≤ A/246.7 ≤ e^{λ₋}/691`. Kernel: `P4.shape_probe_freeA` ✅ (`λ₋³ ≤ e^{λ₋}/1000` for all `λ₋ ≥ 200`; crossover is `λ₋ ≈ 24`, moving only like `+log M`). **Then the register imposes NO `λ₋` ceiling at all — including the budget's `e^{6.5e19}`.** **Class C** (`Adoor` becomes a parameter threaded through ~3188 symbolic sites; most are `∀`-abstract already).

**D3 — re-cut the carried cap `/24 → /16`** (`S16Budget.lean:467`; the margin is stated as 1.5×). Moves 13381 → ~16389. **Class A. Does not change genre.**

**D4 — re-cut `K ≤ 1.7e8 → 1.789e8·(log₂M+1)`.** Moves the cap-face reading from 492 to 13381. Either 94 mechanical edits, or one new M-LOWER register line `klev : (K:ℝ) ≤ 1.789e8·(log₂M+1)` beside `gRows`. **Class B, wide.** Kernel-green at the frame (P1c). *Needed anyway* if D1/D2 is taken.

**D5 — IMPOSSIBLE AT THIS DESIGN:** closing anything by numerals. `λ₋ ≤ (4.019e8)^{1/(p−1)}` where `p` is the tower exponent (`P4.tower_p2` ✅: `p=2 ⇒ λ₋ ≤ 4.019e8`; `p=3 ⇒ 2.0e4`; `p→1 ⇒ unbounded`). Reaching `e^{6.5e19}` needs a shape, not a constant.

## 6. The `λ₋ ~ 50·e^{45} = 1.75e21` question (S1's double-log world)

With D1 in place, at `λ₋ = 1.75e21` the demand is `λ₊ ≥ λ₋³ = 5.36e63`:
- **cap+frame (binder):** needs `A ≥ 554·λ₊ = 2.97e66` ⇒ `M ≥ 4.3e55`, `K ≈ 7.7e63` — inside the scaled ceiling `K ≤ 1.79e8·M`. **SURVIVES.**
- **anchor:** needs `A ≥ 246.7·λ₊ = 1.32e66` — slacker by 2.25×. **SURVIVES, verbatim.**
- **half:** `doorRowFloor = 2^36 M² ≈ 1.3e122`, `log₂ = 405 ≤ 1.4427·1.75e21`. **SURVIVES with 21 orders of room.**
- **blk / lvl / gRows / gP1 / x0M / bfloor / mfloor / rho:** all get easier. **SURVIVE verbatim, class none.**
- **Needs re-derivation:** only the four `Adoor` arithmetic bridges (class A–B) + the `K`-ceiling re-cut (class B, wide).
- **Untouched by any register move:** `Hcap`'s `budgetFloor` height-3 tower and `H₀red = H₀D3` (Siegel) — the other two walls, spine-side and not mine.

## 7. Probe files (read-only, uncommitted)

All under `/private/tmp/claude-501/-Users-jyh-projects-claude-salt/ea81b992-0821-4192-8f48-c0dcdcbc14c2/scratchpad/iface/s3-ceiling/`:
`P1.lean` (frame-ceiling scaling, incl. the full `CalFrameK` re-inhabitation), `P2.lean` (7 face probes + 2 joints + sharpness + the `Adoor`-linear shape probe), `P3.lean` (`s3_ceiling_joint`, the composite against corpus objects), `P4.lean` (tower-exponent dependence + free-`A`), `AX.lean` (axiom audit — all `[propext, Classical.choice, Quot.sound]`). **Every one compiles green.**

---

# ══════════ S4 ══════════

**VERDICT — S4/INTERFACE.** The cap's H-coupling is *not* in the cap bundle: of the 37 cap-gate fields exactly **one** reads the regime's H (`q_arcDen`), and it is supplied verbatim from `SocketBase`'s own modulus ledger at zero cost. The entire coupling lives in **one antecedent line** — `SocketBase`'s x-scale field `R.x ≤ 16·ω·arcDen 12 H·A` — read against **one regime field**, `hPHheadroom`. The register's cap `S16BaseScaleCap_gk` is the **only x-CEILING in the whole chain** (every `ChowlaRegime` x-constraint is a one-sided floor — that is exactly why `regimeEnlargeX` is sound), and it collides with the spine's x-floors **monotonically, without the tower**: `budgetFloor ≤ R.Hlo ≤ R.Hhi` alone closes it. Kernel-certified: `exp(budgetX ε β) + 2 ≤ (K+414)·log 2`, i.e. **K ≥ 1.44·e^{budgetX}** — one full exponential worse than the flags' "1.5e31", which turns out to be precisely the price *after* the decoupling, not before it. The decoupling buys **exactly one exponential** (Λ ≥ e^{λ₊} → Λ ≥ λ₊) and the residual demand is still 1.5e31 against a frame ceiling of 1.7e8. The decoupling is a D-tier re-proof of `entropy_residueWindow_ge`'s error term, not plumbing — but it is **not** information-theoretically forced, and I name where the exponential actually enters: the factor `ω` in `8·P_H²·ω/x`.

Probes: `/private/tmp/claude-501/-Users-jyh-projects-claude-salt/ea81b992-0821-4192-8f48-c0dcdcbc14c2/scratchpad/iface/s4/ProbeS4.lean` — 7 theorems, all `[propext, Classical.choice, Quot.sound]`, no repo edits.

---

## 1. THE INTERFACE MAP — every regime field the register/cap chain reads

`ChowlaRegime` is `Salt/Entropy/Chowla/Regime.lean:57-143` (27 fields). Reads inside `Salt/MR/` (the sieve register), excluding `RegimeHead.lean`'s pass-through enlargement:

| field | Regime.lean | couples | where read (Salt/MR) | direction |
|---|---|---|---|---|
| `hPHheadroom` `8·(4^⌊ε²H₊⌋)²·ω ≤ x` | :116 | **H₊ ↔ x/ω** | `S13MSelect2.lean:112` (`s13_socketBase_xscale`), `:518`, `:634`; `S13FramesA.lean:1039`, `:1528`; `DoorDischarge.lean:113`; `DoorFloor1500.lean:160` | **x-FLOOR, exponential in H₊** |
| `hheadroom` `Hhi ≤ x/ω` | :86 | H₊ ↔ x/ω | `S14Compose.lean:315` (inside the socket witness), `M4Close.lean:485/731/911/994`, `M4BridgeCover.lean:373`, `HloExportMR.lean:144/354/530/672`, `M4DoorL2.lean:160/623/697/855` | x-FLOOR, linear in H₊ |
| `hheadroom'` `8H₊(log H₊)² ≤ x/ω` | :103 | H₊ ↔ x/ω | `M4SecondRoad.lean:535`, `:1185` | x-FLOOR, poly in H₊ |
| `hHlo_floor` `4·10⁶ ≤ Hlo` | :80 | H₋ | ~81 sites (`S13CapFloor`, `S14Compose:112/235/353/514`, …) | H₋ floor |
| `hHlohi` `Hlo ≤ Hhi` | :70 | H₋ ↔ H₊ | ~54 sites | window |
| `hPNTwindow` `√H₋ ≤ ε²H₋/2` | :127 | H₋ ↔ ε | `S13MSelect2.lean:165` (`s13_socketBase_mFloor`), `S13FramesA.lean:343` | H₋/ε |
| `hωbig` `log ω ≥ (16/ε)log(ε²H₊)+64/ε+1` | :133 | H₊ ↔ ω | `S13FramesA.lean:367` (`s13_logOmega_ge`) | ω-FLOOR, poly in H₊ |
| `hx`,`hω`,`hωx`,`heps`,`heps1` | :68,69,71,73,74 | x, ω, ε | ubiquitous | bookkeeping |

**Never read by the register at all** (kernel-checked by exhaustive grep): `hfit` (:93), `hJcon` (:97), `hcoprime` (:90), `hC0` (:79), `hxbig` (:141), `ha`, `hHlo`. ⚡ **The tower is invisible to the sieve side.** `hJcon`/`hfit` — where the maestro's "λ₊ ≥ λ₋³" originates — are consumed only inside `Salt/Entropy/Chowla/`. The register sees the H-window solely through its two endpoints.

**The non-regime x-floors the register itself imposes** (the "arm/g-lever" reads):
- `s13GArm_gk K M δ Hhi ω = 2ω(Hhi+2) + 8ω + 4ω·s13BlockFloor_gk K M + ⌈128ω/δ⌉₊` (`S13FramesA.lean:1316`), consumed via the witness conjunct `g R.Hhi R.ω ≤ R.x` (`S15Witness.lean:1865`). `s13BlockFloor_gk = 2^{s13BlockExp_gk}` with `s13BlockExp_gk K M = 14427 + (64+8(log₂M+1)) + 400·(Adoor M·s13GK K M·M)²` (`S13FramesA.lean:1129`) — **double-exponential in K**, linear in H₊.
- `s13GK K M = 3072·2^K·M` (`GLever.lean:59`); `Adoor M = 2^36(log₂M+1)` (`DoorFrame.lean:84`).

**And the one x-CEILING:** `S16BaseScaleCap_gk` (`S16Budget.lean:467`) — `∀ H L q j A s, SocketBase R M H L q j A s → loglog(A+s) ≤ log 𝒫₂/24`. Carried, never discharged (`S16Budget.lean:93`, `:787`).

**Why the base is x-scale at all** (the supply side, named): `doorLadder_ge_x_div_four_omega` (`M4SecondRoad.lean:449`) — every cover rung is ≥ ⌊x/(4ω)⌋, the window's own lower endpoint. That is the physical content of `SocketBase`'s x-scale field.

**Kernel probe (B):** `probe_cap_is_x_ceiling` — the cap instantiated at the landed inhabitation witness `s14_socketBase_witness` (`S14Compose.lean:311`, tuple `H=L=Hhi, q=1, j=doorRowFloor M, A=2·R.x, s=0`) yields literally `loglog(2·R.x) ≤ log 𝒫₂/24`. The family is non-vacuous on the real chain (`S14Compose.lean:400-402` forces `2^{doorRowFloor M} ≤ R.Hlo` from `MSelect'.winFit`), so this is a genuine ceiling, not a vacuity.

---

## 2. THE DECOUPLING QUESTION

**(a) Which spine lemma consumes `hPHheadroom`, at what strength?** Exactly one, through `pH_headroom_at` (`Regime.lean:161`): `deficit_le_log_two` (`BudgetDeficit.lean:46-69`). Its whole use is `u := 8·P_H²·ω/x ≤ 1`, so that `log(1+u) ≤ log 2` in `entropy_residueWindow_ge` (`ResidueUniform.lean:536-539`). Consumed at **one** H per spine run: `SpineFinal.lean:641`, inside `hbudget1_witness` (`SpineFinal.lean:592`, hypothesis `hhi : H ≤ R.Hhi`) — the pigeonhole's H, *not* every tower level. (The per-level telescope reads `hheadroom'` only: `Step.lean:454`.)

Second consumer, spine-side: `regime_W_headroom_of_floor` (`DoorDischarge.lean:42`) — Tao's W-constraint `(log H₊)^625 ≤ log(x/2ω)`. **Polynomial** in `log H₊`; funded by `hPHheadroom` with astronomic slack. Nothing else in the corpus needs an exponential-in-H₊ x-floor.

**(b) Is the floor forced by the spine, or plumbing?** The honest answer is *neither cleanly*:

- **Information-theoretically forced part.** `deficit_le_log_two` asserts `log P_H − H[Y_H] ≤ log 2`, and `H[Y_H] ≤ log(#atoms of logMeasure x ω) ≤ log x`. So the *consumed conclusion itself* forces `log x ≥ log P_H − log 2 ≍ ε²H₊`. **This part is not removable** — it is what "the residue mod P_H carries ≈ log P_H bits" means.
- **But it constrains `x`, not `x/ω`.** The socket floor reads `x/ω`, not `x`: `A ≥ (x/ω)/(16·(log H)^12)` (`s13_socketBase_xscale`, `S13MSelect2.lean:107`). The field as stated puts `P_H²` below the window's **lower endpoint** `x/ω`; the necessity above puts `P_H` below its **upper endpoint** `x`. ⚡ **The gap is exactly the factor `ω`, and `ω` is exactly one exponential of λ₊.**

**Kernel probes (D, E) — the two floors, sharp and irreducible:**
- `probe_xscale_log`: `4·⌊ε²H₊⌋·log 2 ≤ log 2 + 12·loglog H₊ + log(2·R.x)`. So `log X_d ≥ 2.77·ε²H₊`, hence `Λ := loglog X_d ≥ log H₊ + log(2.77ε²) = e^{λ₊} + O(1)`. (Catch #100: this is the SHARP floor. The landed lemma `s13CapGrid_Lambda_sharp`, `S13CapGrid.lean:201`, gives only `Λ ≥ ½·log H`, i.e. `e^{λ₊}/2` — a factor 2, worth `log 2` on the λ₊ ceiling. `All.lean:6402` already states the sharp form; the flags' "`e^{λ₊}/2`" is the weaker one. Either way the collision is insensitive.)
- `probe_irreducible_floor`: from `hheadroom` **alone**, `R.Hhi ≤ 16·arcDen 12 H·A`. So even with `hPHheadroom` deleted entirely, `log X_d ≥ log H₊ − 12·loglog H₊ − log 16`, hence `Λ ≥ λ₊ − o(1)`. **The decoupling ceiling is exactly one exponential and no more**, and `hheadroom : Hhi ≤ x/ω` (the shift must fit under the window's floor) is not negotiable.

**(c) Could the cap bundle be stated at an H-independent scale? The C2 exposure law's deeper form.** `regimeEnlargeX` (`RegimeHead.lean:104`) is sound because *every* x-constraint is a floor (`RegimeHead.lean:33-37`, `RegimeParam.lean:497`). So the builder may push `x` up freely — but that is the wrong direction: the register needs `x` **small**, and there is no mechanism to push it down. The spine needs `x` from **below** only (`hx`, `hωx`, `hheadroom`, `hheadroom'`, `hPHheadroom`, `hxbig`); it needs nothing of `x` from above. So the cap *could* in principle be met by choosing `x` at its floor — and its floor is `max(8P_H²ω, ω·H₊, s13GArm)`, which is `e^{Θ(ε²H₊)}`. **The builder's freedom in `x` is already exhausted downward.** Note also `RegimeHead.lean:56-64`: enlargement is *not* transportable across the door payload (`logChowla2Fails R.eps R.x R.ω` mentions `R.x` on both sides), so even the upward freedom is not free at S11.

---

## 3. THE PIGEONHOLE FACE

**Re-verified — `∃H` has no index control, at the statement.** `entropy_decrement` (`Decrement.lean:49-55`): `∃ H, R.Hlo ≤ H ∧ H ≤ R.Hhi ∧ R.a ∣ H ∧ I[…] ≤ H/(log H·logloglog H)`. Six consumers, all `obtain ⟨H, hlo, hhi, _hdvd, hMI⟩` (`SpineFinal.lean:462/558/794/921/1061/1417`, `HloExport.lean:454/589`, `TowerDischarge.lean:117`) — the divisibility conjunct is discarded at every one.

**But it is not dead at *source*.** `decrement_exists_of_tower` (`Endpoints.lean:98`) obtains `⟨j, hjJ, hb⟩` and packages the witness as **`chowlaTower R.C0 R.a R.Hlo j`** (`Endpoints.lean:126-129`). The index exists in the proof term and is thrown away in the statement. An index-carrying restatement is a mechanical **class A/B** re-derivation.

**Two facts that matter more than the index:**
1. `chowlaTower (C0 a Hlo : ℕ) : ℕ → ℕ` (`Regime.lean:38`) reads **neither `x` nor `ω`**. The candidate H-set is a fixed J-element set determined by `(C0, a, Hlo)` before `x` is chosen. So index control would buy: `H ≤ chowlaTower C0 a Hlo (J−1)` instead of `H ≤ Hhi`.
2. ⚡ **It buys nothing anyway**, because the harmful coupling does not read the pigeonhole's H. `hPHheadroom` is stated at the **majorant over `Hhi`** (`Regime.lean:116`, and the majorant form is deliberate — `Regime.lean:104-116`: `P_H` is not monotone in H, so the endpoint form does not compose). The socket floor therefore reads `⌊ε²·Hhi⌋`, never the selected H. Splitting the family at the pigeonhole's H leaves the floor untouched.

**THE 37-FIELD CENSUS.** `S13CapGatePerBlock_gk` (`S13FramesB.lean:1996-2110`), 37 fields:
`logX_eight H83_two QTann kappa30Q q_logX T0_Tann floor1 floor2 floor3 floor4 logqT_L P_low Q2_reg Q_pos Q_high P_le_Q budget Hj B3 BT kappa30 BT10 WL gate Rbd_nonneg Rbd_grade Cq_gate Rbd_socket epsr_nonneg abs8640 EP2_gate q_arcDen phi_row p2_row tail_row Q_hundred band_product`.

**Exactly one mentions `Hreg`: `q_arcDen` (`S13FramesB.lean:2092`), `q ≤ arcDen 12 Hreg`.** The `budget` field (`:2043`) reads `Nd = X_d`, `q`, `Tann`, `M`, `K` — **no H at all**. ⚡ **The maestro's "the budget field is the only H₊-reader among the 37" is wrong on both halves**: the budget reads no H, and `q_arcDen` (the sole H-reader) reads the socket's own H, not H₊.

**Kernel probe (A):** `probe_capgate_Hreg_only` — `arcDen 12 Hreg ≤ arcDen 12 Hreg'` transports the *whole bundle* from `Hreg` to `Hreg'` by `{ hg with q_arcDen := le_trans hg.q_arcDen hmono }`. That is a machine certificate that H enters the bundle through one field only.

**Consequence for the split question.** The split is already in place and free: `q_arcDen` is discharged verbatim from `SocketBase`'s own `(q:ℝ) ≤ arcDen 12 H` (`M4Assembly.lean:431`, conjunct 5). The ∀-H family is H-parametric in name only; the poison is the *scale* of `X_d` fixed by the antecedent's x-scale field, and no re-quantification touches it.

---

## 4. THE WALL, IN NUMBERS (kernel probes C, F)

`probe_cap_forces_logHhi`: cap + landed floor at the witness ⟹ **`log H₊ ≤ log 𝒫₂/12`**.
`probe_wall_core`: + `budgetFloor ε β ≤ R.Hlo` (via `budget_tower`, `BudgetCore.lean:54`) ⟹ **`exp(exp(budgetX ε β)) ≤ log 𝒫₂/12`**.
`probe_calE_le` + `probe_wall_K_demand` (at the register's own `M = 2^355`): **`exp(budgetX ε β) + 2 ≤ (K + 414)·log 2`**.

With `log 𝒫₂ = 4·Adoor M·s13GK K M·log 2 = 1.043·2^{K+413}·log 2` (exact at `M = 2^355`; the corpus's own lower twin is `s16_recut_calE_ge`, `S16Budget.lean:698`):

| K | λ₊ ceiling = `(K+413)log2 − 2.81` | logloglog H₊ ceiling |
|---|---|---|
| 0 | 283.5 | 5.647 |
| 3.2·10⁷ (§6 re-pin) | 2.218·10⁷ | 16.92 |
| 1.7·10⁸ (frame ceiling) | 1.178·10⁸ | **18.58** |

Budget demand: `logloglog H ≥ budgetX(1/500, cD3·ε/(144 log 4)) = 1.036·10³¹` (`BudgetCore.lean:21`; `S16Budget.lean:897` reads the same numeral). **The gap at my face is 1.04·10³¹ vs 18.58 in the triple log** (the flags' "≤ 6.24" is the anchor face, `S15Witness.lean:48`, not this one).

**Two corrections to the banked pre-analysis, both kernel-backed:**
1. **The demand on K is `1.44·e^{budgetX}`, not `1.5·10³¹`.** `1.5e31 = budgetX/log 2` is the demand one gets from `λ₊ ≤ (K+413)log2` **only if the socket floor is `Λ ≥ λ₊`** — i.e. *after* the full decoupling. At the design as it stands the floor is `Λ ≥ e^{λ₊}` and the demand is `(K+414)log 2 ≥ e^{budgetX}` (probe F). The flags' number is the post-repair price; the pre-repair price is one exponential worse. Symmetrically, `S16Budget.lean:1013`'s "`budgetFloor` forces `λ₋ ≥ e^{e^{1.04·10³¹}}`" is one exponential too *many*: `budget_tower` gives `logloglog H ≥ budgetX`, i.e. `λ₋ ≥ e^{1.04·10³¹}`.
2. **The tower is not load-bearing at this face.** `s16_audit_hcap_wall` (`S16Budget.lean:1016`) routes through `λ₋³ ≤ (K+413)log 2`. `probe_wall_core` needs only `Hlo ≤ Hhi` and `log` monotone. The maestro's "both cubic collisions trace to ONE root [the tower]" is false for S16BaseScaleCap: this collision is a **monotone** one, and it survives the deletion of `hJcon` entirely (which the register never reads).

**One caveat I did not close** (flagging, not hiding): at a *moving* `M` the cap ceiling is `≈ 354.8·Adoor M·M·2^K`, and `half` (`S15Witness.lean:48`) lets `M ≲ log H₋`. Working that through gives `λ₊ ≤ λ₋ + K·log 2 + 5.5` — so with `M` free the collision reduces to the tower after all (`K ≳ 1.44·λ₋³`), still dead at `λ₋ ≥ e^{1.036·10³¹}`. The register's `M = 2^355` pin is itself downstream of the anchor's λ₋-ceiling: `λ₋^{4.5} ≤ 2.7857·10⁸·(log₂M+1)` with `log₂M ≤ 1.4427·λ₋` gives `λ₋^{3.5} ≤ 4.03·10⁸`, i.e. **λ₋ ≤ 288** (the corpus's 277.7, `S15Witness.lean:761-767`); under the spine's own `λ₊ ≥ λ₋³` the same line gives `λ₋ ≤ 2.0·10⁴` — which is the maestro's "~1e4-genre", independently confirmed on a second route. That ceiling belongs to the anchor scoper's face; I did not audit `gP1`/`lvl`/`Mfl` at a moving M.

---

## 5. DIRECTIONS, WITH HONEST PRICES

**I-1 · Re-cut `entropy_residueWindow_ge`'s error from `8·P_H²·ω/x` to a form not read at the window's floor. [D-tier, spine-side]** This is the only change that moves my face's shape. The error is an ℓ¹/total-variation union bound over `P_H` residue classes evaluated at the window's *lower* endpoint `x/ω`; the logarithmic measure puts only a `1/log ω` fraction of its mass there. Payoff: `x/ω` freed from `P_H²`, socket floor drops `Λ ≥ e^{λ₊} → Λ ≥ λ₊` (probe E is the exact stopping point — `hheadroom` alone still gives `λ₊`). **Price:** a genuine re-proof of `ResidueUniform.lean:536` plus a re-derivation of `hPHheadroom` and its 7 register reads. **Residual after success: `K ≥ 1.5·10³¹` vs the frame's `1.7·10⁸` — 23 orders short.** So I-1 is necessary-but-nowhere-near-sufficient. Recommend: do not fire on its own.

**I-2 · Raise `log 𝒫₂`. [dead at this design]** The ceiling is `log 𝒫₂/24 = 0.0301·2^{K+413}` — exponential in K, so it *looks* like the free knob. It is not: `K ≤ 1.7·10⁸` is spent at `A_gate_logK` inside `calFrameK_satisfiable_door_gk` (`DoorFrameH1.lean:511-520` names it), which is linear in `Adoor M ∝ log₂M`; and `M` is capped by `half` at `log₂M ≲ 1.4427·λ₋`. So the K-ceiling grows only *linearly in λ₋* while the demand grows like `e^{budgetX}`. **Impossible at this design.**

**I-3 · Restate the family at a scale variable independent of H. [impossible at this design — named]** The socket base is the door ladder's rung and the ladder tiles `(x/ω, x]` (`M4SecondRoad.lean:449`). Any sieve run for the spine must run *on the spine's own window*, whose lower endpoint the spine bounds from below. There is no scale variable to introduce: `X_d`'s floor is `x/ω`, `x/ω`'s floor is a regime field, and the regime has no x-ceiling to trade against. The only structural freedom — `regimeEnlargeX` — points the wrong way.

**I-4 · Index-carrying `entropy_decrement`. [A/B-tier, and worthless here]** Mechanically available from `Endpoints.lean:126-129`. Buys `H = chowlaTower C0 a Hlo j` for some `j < J`. Does **not** help: `hPHheadroom` is stated at the `Hhi`-majorant by necessity (`Regime.lean:104-116`), so the socket floor never reads the selected H. Only worth doing if some *other* face needs the tower index.

**I-5 · Split the ∀-H family. [free, and worthless here]** Already effectively done: 1 H-reader of 37, discharged verbatim from the antecedent (probe A certifies the count). No gain available.

**I-6 · Weaken `hPHheadroom`'s constant (`u ≤ 1 → u ≤ U`). [A-tier, worthless]** The bracket in `hbudget1_witness` (`SpineFinal.lean:645-655`) tolerates a deficit `D ≲ β²·g ≈ ε⁸H/log H`, so `x` may be shrunk by at most `e^{O(ε⁸H₊/log H₊)}` — a lower-order correction to `log x ≍ ε²H₊`. `Λ = loglog x` is unchanged to `O(1)`. Any *constant* relaxation is invisible; only the **shape** (I-1) matters.

**Where I would put the design council's attention, from this face:** the collision at S16BaseScaleCap is monotone, tower-free, and one exponential deeper than banked. It is not repairable on the register side at any K or M. Of the three shapes the flags name, only "the budget's `logloglog` demand" (spine-side, `budgetX`) can move this face by more than one exponential — I-1 buys exactly one exponential and leaves 23 orders.