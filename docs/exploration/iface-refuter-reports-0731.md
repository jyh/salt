# THE INTERFACE REFUTER PASS — R1/R2/R3 verbatim (2026-07-31 night)


---

# ══════ R1 ══════

**VERDICT — CLAIM 1's operative half is REFUTED; CLAIM 2's branch (a) is DEAD but at a face neither claim names; branch (b) closes EVERY register face and dies at the ε-coupling; CLAIM 3 is REFUTED (the cap face closes at K = 0 at both branches, with margin). Post-D1 there is NO working point at either branch — but the residual is not the cap: it is (a) the 6.4517 width law and (b) the tower/budget ε-coupling. Two new faces the freeze omits (the b-floor and the x₀ rider) move the honest working point from λ₋ ≈ 72–110 to λ₋ ≈ 449.**

Probes: `/private/tmp/claude-501/-Users-jyh-projects-claude-salt/ea81b992-0821-4192-8f48-c0dcdcbc14c2/scratchpad/ifref/r1-joint/R1.lean` — 17 theorems, `lake env lean` green, all `[propext, Classical.choice, Quot.sound]`, repo untouched.

## 1. What D1 delivers — CONFIRMED, and the number is right

`budget_facts`' four height-1 facts route through `hcore` (`BudgetCore.lean:192-197`); the largest is D_iv's `c = 2304·log2·log4/(β²ε⁶)` (`:223-235`), needing `4c ≤ log H`. At `ε = 1/500`, `β = cD3·ε/(144·log4) = 2.5047e-6` (`SpineFinal.lean:621`, `cD3 = 1/4` `WindowMertensLower.lean:62`):

- **`p1_demand_ge` + `p1b_lambda_floor`**: `log H₋ ≥ 2^104 = 2.2057e31` ⟹ **λ₋ ≥ 72.17**.
- **`p1c_budgetX_route`**: via `4·budgetX` (`BudgetCore.lean:21`, the shape S1 says `budgetFloor` collapses to) `4X = 4.1434e31` ⟹ λ₋ ≥ 72.80.

S1's "2.2·10³¹-genre, height 1" is exact. λ₋ is a **logarithm** of the demand, so this is robust: a demand of 10⁵⁰ still gives λ₋ = 115. That half of CLAIM 1 stands.

## 2. But the register's OWN floors dominate — two faces the freeze never walks

| face | source | forces |
|---|---|---|
| budget (post-D1) | `BudgetCore.lean:223` | λ₋ ≥ 72.17 |
| **x₀ rider** | `S15Sel''_gk.x0M` (`S15Compose.lean:2575`) + the chain's pinned `x₀ ≥ exp(exp 100)` (`S15Witness.lean:~795`, `mmu1Chi_rate_of_pinned`) | **λ₋ ≥ 100.9** (`p9_x0_rider_lambda`: ≥ 100) |
| **b-floor** | `S15Sel''_gk.bfloor` + the road's own `24·Cg/δ₀ = 1.68·10¹⁸¹ = 2^602.02` (`ConstantsExposed.lean:410`, docstring `:67`) + `half` | **λ₋ ≥ 448.98** (`p4_bfloor_lambda`: ≥ 448) |

So the honest post-D1 working point is **λ₋ = 448.98, M = 2^602.02, L+1 = 603** — not "λ₋ ≈ 72–110". CLAIM 1's numerals name only the weakest of the three floors. (Silver lining, and it is real: post-D1 λ₋ is *free to be chosen* at 449, which is exactly where the landed witness's 248-bit b-floor gap — `S15Witness.lean:780` — closes to zero. Pre-D1 that was impossible because λ₋ was pinned at `e^{1.04e31}`.)

Freeze numeral slip inside CLAIM 2, kernel-checked: "at L+1 ≈ 155 [with] λ₋ ≈ 110" — `half` at L+1 = 155 forces **λ₋ ≥ 136.5** (`p8_L155_needs_lambda_136`); at λ₋ = 110 `half` allows only L+1 ≤ 116. Harmless for the anchor, wrong as stated.

## 3. The width law is 6.4517, not 7.1448 — the freeze's own figure, off by exactly log 2

`S15Sel''_gk.half` (`S15Compose.lean:2580-2581`) reads `0.7·doorRowFloor M + 3·log(1/ρ) ≤ (log H₋)/2` — **with the /2**. The budget ghost (`S15Compose.lean:794`, `flags.md:17978`) is `log H₊ ≤ 1280·log2·doorRowFloor M`. Composing (`p2_width_from_half`, certified at the clean `10·log2 = 6.9315`; the sharp value is `log(1280·log2/1.4) = 6.4517`):

**λ₊ ≤ λ₋ + 6.4517.** `p2b_width_gap_is_log_two` certifies `log(1280·log2/0.7) = log(1280·log2/1.4) + log 2` — the flags'/freeze's 7.1448 dropped the `/2`. Status of the law itself: the `×1280` ghost is LAMBDA-RECON **prose**, not a landed field (`flags.md:17978` says so outright) — but it is the price of supplying the one carried binder `S15CrossingBound` (`S15Compose.lean:~800`) through its only known route.

## 4. Branch (a) — landed tower — DEAD, at two faces, neither of them CLAIM 3's

At λ₋ = 448.98 the landed tower gives λ₊ = λ₋^3.7436 = **8.489·10⁹** (cube: 9.05·10⁷).

- **Width face (the kill)**: `p3_branch_a_kill` — even the *weakest* landed law `λ₋³ ≤ λ₊` (`TowerExport.lean:673`) contradicts `λ₊ ≤ λ₋ + 6.94` at every λ₋ ≥ 50. `p3b_branch_a_deficit`: window demand ≥ 9·10⁷ vs budget 6.45 — **deficit 1.3·10⁶× at the honest exponent**. Not repairable by any constant: saving it needs `e^{8.5e9}` of re-pricing, i.e. a shape change in the crossing-bound supply. D1 does not touch this face at all.
- **Anchor face (second, independent kill)**: `p4b_anchor_caps_lambda` — `anchor` + `half` + the compose's only exported λ₊-handle `λ₊ ≤ λ₋^{9/2}` cap **λ₋ ≤ 288**, against the b-floor's 448.98. The honest sharpest export (4.4077, S2 §1) gives only λ₋ ≤ 334.6; the working point needs an export exponent ≤ **4.244**, which is inside the [3.7436, 4.4077] bracket-gap but is not provable from the landed budget line. So branch (a) cannot even host the road's own `bfloor`.
- Everything else at branch (a) **passes**: anchor RHS 2.35e12 vs LHS 1.19e11; gRows 4.14e13 vs 2.05e12; lvl 2.39e12 vs 1.19e11; cap needs K ≥ 1.226·10¹⁰ vs frame ceiling 1.079·10¹¹ (`p5b_branch_a_cap_K`).

## 5. CLAIM 3 — REFUTED (a category error, both branches)

CLAIM 3 compares the socket floor `Λ ≥ e^{λ₊}` against `K ≤ 1.79e8·(L+1) ≈ 2e10` **as numbers**. But K enters the ceiling as `2^K`: `log 𝒫₂ = 4·Adoor M·s13GK K M·log 2` (`S16Budget.lean:104-112` `s16_logP2`, `:698` `s16_recut_calE_ge`), and the face `log H₊ ≤ log 𝒫₂/12` (S4 `probe_cap_forces_logHhi`, = `s13CapGrid_Lambda_sharp` `S13CapGrid.lean:201` composed with `S16BaseScaleCap_gk` `S16Budget.lean:467`, the `/24`). The demand is therefore

**K ≥ 1.4427·λ₊ − (48 + log₂M + log₂(3(L+1)) − 3.6)**, not `K ≈ e^{λ₊}`.

- **`p5_cap_ceiling_at_working_point`**: at M = 2^602, L+1 = 603, **K = 0** the ceiling is λ₊ ≤ 455.19. Branch (b) asks 454.85 → **closes at K = 0**, margin 0.35 in λ₊ (1.4× in log H₊); K = 1 gives 1.04. Freeze says "STILL DEAD BY ~23 ORDERS" — refuted.
- Branch (a) closes too at K = 1.23e10 ≤ 1.08e11 (`p5b`).

The cap/S4 face is **not** the residual mountain post-D1. (S4's own "1.44·e^{budgetX}" was correct *pre*-D1 only because λ₊ ≥ λ₋ ≥ e^{budgetX} then.)

## 6. Branch (b) — k = 2 shallow — closes every register face, then dies at the ε-coupling

Working point λ₋ = 448.98, λ₊ = 454.85 (k=2's own width `2(log2)²·log λ₋` = 5.868; design-independent floor 5.501), M = 2^602.02, K ∈ [0, 1.08e11]:

| face | demand | budget | margin |
|---|---|---|---|
| budget (post-D1) | λ₋ ≥ 72.17 | λ₋ = 448.98 | 163 orders in log H₋ |
| width (`half` + ghost) | 5.868 | 6.4517 | **0.58 (1.79×)** — the tight one |
| cap/S16BaseScaleCap, K=0 | λ₊ 454.85 | 455.19 | 0.35 (K-free upward) |
| anchor | 6.4e3 | 2.352e12 | 3.7e8× |
| gRows | 1.10e5 | Adoor M = 4.14e13 | 3.8e8× |
| lvl | ~6.7e3 | 2.394e12 | 3.6e8× |
| gP1 | ~6.4e3 | 2.872e13 | 4e9× |
| blk | 2^2530 | 4⌊ε²H₊⌋ ≈ 2^{3.6e197} | free |
| x0M | x₀ ≥ e^{e^{100}} | 2^{doorRowFloor} = e^{e^{448.26}} | 348 double-log units |
| half / bfloor | pinned at equality (this is what fixes λ₋) | — | 0 |
| hM, mfloor, rho | free (`rho`: anchor tightens −log ρ ≤ 2.35e12 vs the field's 1e14) | — | — |

Joint λ₋ window for branch (b): **[448.98, 823.9]** with the k=2 construction's own width, **[448.98, 1289.1]** at the design-independent floor (`p7_window_fits` certifies λ₋ ≤ 1024 fits; `p7b_floor_at_bfloor_point` certifies the floor ≥ 5.49 at λ₋ ≥ 449). NONEMPTY. If the b-floor is separately repaired (the known ~350-bit `hMδ`/δ₀ wall), λ₋ drops to 100.9 and the width margin widens to 2.2 (9×).

**THE KILL** — S2's Kill 1, re-run post-D1 and still fatal:
- `p6_eps_kill`: the k=2 step needs `ε²·log4 ≤ 1/(2·log H·logloglog H)` (S2 `P2.lean:27 probe_shallow_step`, verbatim), i.e. `ε ≲ e^{−λ/2}`; `β ≤ ε/798`; the post-D1 height-1 demand is `e^λ ≥ 4·2304·log2·log4/(β²ε⁶)`. **Contradictory at every λ ≥ 50** — and my antecedent is *weaker* than the real one (I drop the `logloglog` factor), so the kill is a fortiori. The divergence is `e^{3λ}`, not a numeral.
- `p6b_eps_kill_beta_only` — **the knife-edge, and the decisive fact for R2**: even if D1 removes *every* ε from `g` (the whole ε⁶), `β ∝ ε` alone leaves total ε-power 2 and the fixed point still fails, at every λ, by the constant `1.57·10¹⁰`. Threshold: the post-D1 demand must carry total ε-power **< 2** for the shallow tower to have any fixed point. Since `β = cD3·ε/(144·log4)` is pinned by the mass ledger (S1 §4, seed `|X| ≥ ε/2`), branch (b) requires the **two-ε split** (S2 direction 2, class D) — not a Bennett ε-power improvement.

## 7. The honest post-D1 residual, priced

1. **Branch (a) price**: kill the width law outright (re-supply `S15CrossingBound` off the `budget` route — WIDTH-SCOPE priced its three known directions DEAD-or-2×) **plus** a λ₊-export at exponent ≤ 4.244 (landed 4.5, honest-achievable 4.4077) **or** a b-floor repair to release λ₋ ≤ 288. Three shape changes.
2. **Branch (b) price**: the two-ε split (D-tier, spine-side: split `R.eps` into the 𝒫_H-window ε and the budget ε — `HloExport.lean:464` is the single field) **plus** the k=2 tower construction (~800–1200 ln, class C). Then every face above closes with the margins tabled, the b-floor's 248-bit gap closes for free, and the residual is the width margin 0.58 and the cap margin 0.35 — both real but positive, both K-/M-tunable.
3. **D1 alone closes nothing.** It converts the wall from "a 10³¹ constant in the triple log" into "a shallow-tower ε-coupling + a 6.45 width law" — a genuinely different and much smaller residual, but a residual.

Status flags: the ×1280 ghost (§3) is prose, not kernel; `S16BaseScaleCap_gk` is carried, never discharged (`S16Budget.lean:93, 787`); `b_floor_cert` is landed (`ConstantsExposed.lean:410`); the frame ceiling `K ≤ 1.7896e8·(L+1)` is S3's kernel probe, consumed here as given.

---

# ══════ R2 ══════

**VERDICT: D1 IS REFUTED. The Bennett re-proof cannot gain a `log H` — it cannot gain one at ANY admissible threshold — and the best conceivable gain (two ε-powers, `ε⁶→ε⁴`) leaves the height-3 demand at `logloglog H ≥ 4.9·10²¹` against the register's 9.906. The freeze's B/D1 line, CLAIM 1 and CLAIM 2's premise all fall with it. The variance is NOT smaller: the bridge variable is genuinely range-spread.**

Probes: `/private/tmp/claude-501/-Users-jyh-projects-claude-salt/ea81b992-0821-4192-8f48-c0dcdcbc14c2/scratchpad/ifref/R2/{P1,P2,P3}.lean` — 26 theorems, `lake env lean` green, no `sorry`/`native_decide`, every named result `[propext, Classical.choice, Quot.sound]`.

## (1) THE TRUE VARIANCE — the kill

The bridge variable is `X_p = fBridgeG eps H v p (residueProj p ω)` (`FBridge.lean:88-92`), `ω` uniform on `ZMod P_H`, CRT-independent across `p` (`Concentration.lean:218`). `G_p(v)(r) = ∑_{j<H, gate} v_j·v_{j+p}` — the gate is rewritten by FBridge's own proof (`FBridge.lean:180-184`, `hset`) to `(j : ZMod p) = -r-1`, i.e. `G_p` sums the CONSECUTIVE PRODUCTS along the arithmetic chain `{j ≡ c (p)} ∩ [0,H)`, of length `m ≈ H/p`.

**Those products are freely prescribable per chain, and the chains are disjoint.** Setting `v` constant along even-indexed chains and alternating along odd-indexed chains makes every product `+1` resp. `−1`, so `G_p(r) = ±(m−1)`:
- kernel (`P1.lean:39-43`, `decide`): at `p=5, H=100` the five class values are `19, −19, 19, −19, 19`; `vadv` is `±1`-valued (`P1.lean:33`, an admissible `hv : ∀ i, |v i| ≤ 1` pattern).
- `σ² = 19² − (19/5)² = 346.56` vs the Hoeffding half-width `(H/p+1)² = 441` (`fBridge_varTerm`, `FBridge.lean:198-206`): **78.6 % of the range-square** (`P1.lean:46,53`). General form `(m−1)²(1−1/p²)` → `(m+1)²` as `m→∞`; kernel: `≥ (m+1)²/2` for `m ≥ 11, p ≥ 2` (`P1.lean:62`).

⟹ **any uniform-in-`v` variance bound below the range-square is FALSE.** For the worst-case admissible pattern Bennett *is* Hoeffding, gain `O(1)`.

The most that survives is the **first-moment (averaging) floor**, which is a *lower* bound on what a uniform-in-`v` proof must carry: `E_v[∑_r G_p(r)²] = H−p` and `E_v[(∑_r G_p(r))²] = H−p` (only the diagonal survives) ⟹ `E_v[σ_p²] = (H−p)(p−1)/p² ≈ H/p`, so **some** admissible pattern forces `∑_p σ_p² ≥ N·(H/p−1)`-genre simultaneously over all window primes. Kernel brute force of both identities at `H=8, p=3` (`P3.lean:27,33`, `2^8` patterns, `= 1280 = 256·(8−3)`), consequence `10/9` (`P3.lean:39`). Window floor: `σ_p² ≥ 1/(4ε²)` (`P3.lean:46`).

**S1's `σ_p² ≈ H²/p³` (scope report (5), "honest hazard") is the whole error.** On the window (`ε²H/2 < p ≤ ε²H`, `PrimeWindow.lean:26`) `H²/p³ ≤ 8/(ε⁶H)`, i.e. it is below the honest floor by the factor `ε⁴H/32` — kernel (`P3.lean:66`). `log(ε⁴H/32) ≍ log H`: S1 bought its `log H` cancellation with exactly that missing factor.

**Corpus supply: NONE.** `grep -i variance Salt/Entropy/` returns only "invariance". The corpus has the first moment (`fBridgeG_mean`, `FBridge.lean:337`) and the box bound (`fBridgeG_abs_le`, `FBridge.lean:160`) and nothing else on `G_p`. The `MeanSq` pages are `Salt/MR/*` (M4 rows/door, a different object).

## (2) MATHLIB — nothing, and the sibling must be built

`grep -rl "Bennett|Bernstein" Mathlib/Probability/` → **empty**. Bernstein hits are polynomials (`Analysis/SpecialFunctions/Bernstein.lean`, `RingTheory/Polynomial/Bernstein.lean`). The landed chain is `hasSubgaussianMGF_of_mem_Icc` (`Mathlib/Probability/Moments/SubGaussian.lean:860`, Hoeffding's lemma) → `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` (`:780`), consumed at `Concentration.lean:167-176`. `Moments/Variance.lean` has Chebyshev only. Est for a from-scratch `HasBennettMGF` sibling: the mgf lemma `E e^{tX} ≤ exp(σ²(e^{tb}−1−tb)/b²)` needs the monotonicity of `(e^u−1−u)/u²` (not in mathlib — the risky step, C/D, ~100-150 ln), the independent-sum product (~150-250 ln), the Chernoff optimisation at `t = b⁻¹log(1+bδ/V)` (~100-150 ln). **≈ 500-900 ln, class C** (mathlib's SubGaussian.lean is 945 ln for the Hoeffding analogue).

## (3) THE HONEST GAIN — no `log H`, at most `ε²`

Kernel, `P2.lean`:
- `bennett_h_le` (`:14`): `h(u) = (1+u)log(1+u) − u ≤ u²` ⟹ `bennett_le_gaussian` (`:25`): **the Bennett exponent `(V/R²)h(Rδ/V) ≤ δ²/V` for every `V,R,δ`.** No variance-based tail (Bennett, Bernstein, Freedman, Bousquet) beats the Gaussian exponent at the true variance sum. (Conservative: the sharp constant is `δ²/2V`, so this is generous to D1 by 2×.)
- `bennett_ceiling` (`:43`): with `V ≥ N/(4ε²)` (P3 floor) and `N ≥ ε²H/(8 log H)` (corpus: `primeWindow_sum_inv_ge`, `cD3 = 1/4`, `WindowMertensLower.lean`, times `p ≤ ε²H`), at `δ = ε²H/log H` (`Transport.lean:128`): **`g ≤ 32·ε⁴H/log H`.** The `log H` survives. So `ε⁶ → ε⁴` in `g` (`ε⁻⁸ → ε⁻⁶` in the demand) and **nothing else**.
- `poisson_regime_absent` (`:100`): S1's mechanism dies at the argument itself — `Rδ/V ≤ 32(2+ε²) ≤ 72`, a pure constant. S1 claims `Rδ/(Nσ²) ∼ ε³H`. `log(1+72) < 4.3`, not `log H`.
- `poisson_log_bounded_at_max_delta` (`:134`): **the "raise δ" rebuttal is dead too** — at the maximal admissible `δ ≤ (cD3/16)εH/log H` (S1 (4)'s slice), `Rδ/V ≤ 4/ε + 2ε ≤ 2001` at `ε = 1/500` (`:172`), Poisson log `< 7.7`, against `log H ≥ 2.2·10³¹`.
- `log_cancellation_impossible` (`:187`): if `g ≥ ε⁴H` (the freeze's "gains a full `log H`"), then `log H ≤ 32`. The budget's own height-1 demand is `log H ≥ 2.2·10³¹` (S1 P7). **Incompatible by 30 orders.**
- `height3_invariant` (`:71`): frozen fact (iv) (`BudgetCore.lean:138-145`) with `gcap ≤ c·ε⁴H/log H` still forces `logloglog H ≥ 16/(c ε⁴β²)`. **The κ/gcap cancellation is untouched by the ε-power; budgetFloor stays `⌈exp exp exp X⌉`.**
- Numerals at the fired point (`ε = 1/500`, `β = cD3ε/(144 log4) = ε/(576 log4) ≤ ε/798.5`, `SpineFinal.lean:621`): landed demand `≥ 1.9·10³⁰` (`:178`, matches S1 P3c); **post-D1 best case `≥ 4.9·10²¹`** (`:174`); gain `4·10⁸`; deficit vs S3's honest `9.906` ceiling **`≥ 4.9·10²⁰`** (`:182`).

**CLAIM 1 is REFUTED**: `λ₋ ≈ 72–110` presumes `budgetFloor` collapsing to height 1, which presumes the `κ`-summand's death, which presumes the `log H` cancellation. Post-D1 `λ₋ = loglog H ≥ e^{4.9·10²¹}` vs the register's `λ₋ ≤ 20048` (S3). CLAIM 2's branch choice and CLAIM 3's `λ₋ ≈ 73` working point are moot — they are downstream of a premise that does not hold.

## (4) HONEST EST AND BLAST RADIUS

If flown anyway: (a) `HasBennettMGF` + Finset sum + Chernoff, 500-900 ln, class C, riskiest step the `(e^u−1−u)/u²` monotonicity; (b) **the variance INPUT — no est, because the needed statement is false**: uniform in `v` it must be `σ_p² ≲ R²/p`, contradicted by `P1` at ratio 0.786; restricted to Liouville windows it is a 4-point-correlation equidistribution statement across residue classes, strictly stronger than the two-point cancellation the spine is trying to prove — class D/open, plausibly false. Even granted, the payoff is `ε²`.

Blast radius (re-derive on any change to the tail): `FBridge.lean` `fBridge_varTerm:198`, `fBridge_var_le:217`, `fBridge_var_le_sharp:375`, `fBridge_concentration_raw:262`, `fBridge_concentration:274`, `fBridge_concentration_sharp:405`, `fBridge_concentration_decoupled_sharp:459`; `Concentration.lean:167,196,218` (a Bennett sibling of all three); `Decoupled.lean:53`; `Transport.lean:69` `badSet_transport` + `:128` `badSet_transport_at_calibration` (the `ε⁶/18C₀` calibration line `:141`); `OuterCombine.lean:238`; `SpineFinal.lean:630` `gcap`; and `BudgetCore.lean:138-145` fact (iv) + `:21` `budgetX` are **statement-tier** (Captain's fence, per the freeze's §D). ~2,000 ln touched, 4 frozen statements re-opened, for a `4·10⁸` gain against a `10²¹` gap.

**RECOMMENDATION TO THE FREEZE**: strike D1 from §B. The height-3 wall is not the Hoeffding range-square; it is the identity `κ ≍ gcap ≍ H/log H`, and the variance floor `σ_p² ≥ 1/(4ε²)` proves *no* concentration re-proof can move `gcap` off `H/log H`. What must move is `κ`'s `H`-order (D2) or the register's `H`-coupling — not the tail.

---

# ══════ R3 ══════

**VERDICT — CLAIM 3 IS REFUTED AT THE KERNEL. The S4/S3 face does not exist post-D1: it needs NO repair, no Adoor re-cut, no ω-route, no cap reprice. CLAIM 3's "K ≈ 4e33, DEAD BY 23 ORDERS" is a one-exponential LEVEL ERROR — it compares `Λ = loglog X_d` against `(K+414)·log 2`, which is the ceiling on `λ₊`, not on `Λ`. The cap's actual right side is `log 𝒫₂/24 = 0.0301·2^{K+413}` — EXPONENTIAL in `K + log₂M`. The honest demand at CLAIM 3's own branch-(b) point is `K = 0`; at the freeze's CLAIM-1 point `K = 1` (K = 2 at S4's sharp floor); at branch (a) `K = 6.8e7 ≤ 1.7e8`, INSIDE the corpus's landed pin. Fifteen probes green, `[propext, Classical.choice, Quot.sound]` only.**

Probes: `/private/tmp/claude-501/-Users-jyh-projects-claude-salt/ea81b992-0821-4192-8f48-c0dcdcbc14c2/scratchpad/ifref/r3/R3.lean` (15 theorems + axiom block, `lake env lean` green, repo untouched).

## 1. THE REDUCTION, AT THE BYTES (catch #100 applied to the freeze)

The cap is `S16BaseScaleCap_gk` (`Salt/MR/S16Budget.lean:467`): `loglog(A+s) ≤ log 𝒫₂ / 24`, and `log 𝒫₂ = 4·(Adoor M · s13GK K M)·log 2` (`s16_logP2`, `S16Budget.lean:108`). At `M = 2^L` this is `12288·(L+1)·2^{36+K+L}·log 2` (kernel: `r3_logP2_ge`). Composing with the landed socket floor `Λ ≥ ½·log H` (`s13CapGrid_Lambda_sharp`, `S13CapGrid.lean:201`, `log H₊ = e^{λ₊}`):

> **the cap's ceiling on `λ₊` is `(49 + K + log₂M)·log 2 + log(log₂M+1) − 2.85`** — kernel: `r3_cap_fit`. LINEAR in `K`; each unit of `K` buys `log 2 = 0.693` of `λ₊`.

`(K+414)·log 2` is `log(log 𝒫₂/12)` — S4's §4 table states it correctly *as a ceiling on `λ₊`*. CLAIM 3 fed `Λ = e^{λ₊}/2` into it instead of `λ₊`. That is the entire 23 orders. The corpus's own `s16_recut_cap_demand_met` (`S16Budget.lean:730`) already certifies this shape: `λ₋³ ≤ loglog 𝒫₂ = (K+413)log 2` at `K = 3.2·10^7` — the cap face closing at a **cubic** `λ₊` with a nine-digit `K`, in the kernel since before the freeze.

Kernel isolation of the error (`r3_level_error`): at `K = 0` and the freeze's own `M`-genre (`log₂M+1 = 105`), the cap admits `Λ = e^{106}/2 ≈ 7.9·10^{45}`; CLAIM 3's reading admits `287`. Factor `2.7·10^{43}`, same face, same `K`.

## 2. THE POST-D1 WORKING POINT, KERNEL-CERTIFIED

| point | λ₋ | λ₊ | M | K the cap needs | vs landed pin `1.7e8` | probe |
|---|---|---|---|---|---|---|
| CLAIM 3's own branch (b) | ~73 | 77 | 2^62 | **0** | ✓ | `r3_branchB_lam77_K0` |
| branch (b) @ CLAIM-1 point | 110 | 114.3 | 2^114 | **1** (landed floor) | ✓ | `r3_branchB_freeze_point` |
| ″, at S4's SHARP floor `Λ ≥ e^{λ₊}` | 110 | 114.3 | 2^114 | **2** | ✓ | `r3_branchB_sharp_floor` |
| branch (b) @ landed witness `λ₋ = 400·log2` | 277.26 | 282.4 | 2^355 | **0** | ✓ | `r3_branchB_landed_witness` |
| branch (a), sharp tower exp 3.7436 | 110 | ≤4.7e7 | 2^114 | **6.8e7** | ✓ (2.5× room) | `r3_towerA_lower`, `r3_branchA_landedK` |
| branch (a), S2 bracket TOP 4.4077 | 110 | ≤1.6e9 | 2^114 | **2.4e9** | ✗ → needs S3's D4 (`1.789e8·115 = 2.06e10` ✓, 8.6×) | `r3_towerA_upper`, `r3_branchA_bracketTop` |

The frame gate is not in the way at branch (a): `r3_frame_ok_at_branchA` is the corpus's **own** `CalFrameK` inhabitant `calFrameK_satisfiable_door_gk 68000000 (2^114)` (`DoorFrame.lean:352`), side condition `K ≤ 1.7e8`, no re-cut. And `half` hosts that `M`: `r3_half_ok_at_110` certifies `0.7·doorRowFloor(2^114) + 3·43 ≤ e^{110}/2`. The cap's RHS is monotone in `M` (`Adoor`, `s13GK` both nondecreasing), so `M = 2^L` probes are honest lower bounds for any admissible `M ≥ 2^L`.

**CLAIM 3's numbers, recomputed:** `e^{77}/2 = 1.379e33` (freeze: 1.5e33 — fine); "`K ≈ 4e33`" = `e^{77}/log 2` (the freeze dropped the /2) — **void**, wrong reduction; "`1.79e8·(L+1) ≈ 2e10` at `L+1 ≈ 105`" ✓ (1.88e10); `λ₋ = log(4·10^{31}) = 72.77` ✓. Everything is arithmetically self-consistent *given* the wrong inequality.

## 3. THE ROUTES

**(1) THE ADOOR RE-CUT — UNNECESSARY, and the asymptotic worry is void twice over.**
(a) The face closes at the LANDED `Adoor M = 2^36(log₂M+1)` (`DoorFrame.lean:84`), table above. (b) The worry's own arithmetic inverts once the demand is right: `A_gate_logK`'s door instance is `(48L + 880 + 16K)log 2 ≤ (1/24)(Adoor M·log 2 − 1)` (`SeamCalibrationK.lean:173`, instance named at `DoorFrameH1.lean:511-520`), so with `Adoor ~ M^c` the gate gives `K_max ≈ Adoor M/384 ~ M^c` and `winFit/half` gives `M^{1+c} ≲ e^{λ₋}`, hence `λ₊_max ≈ 0.693·K_max ~ e^{cλ₋/(1+c)}` — **exponential in λ₋** — against a demand of `λ₊ = λ₋+4` (b) or `λ₋^{3.74}` (a), i.e. *polynomial*. At `c = 1, λ₋ = 110`: `K_max ~ 7.7e23` vs demand `6.4e7`. The "short by construction" reading came from demanding `e^{λ₊}` where `1.4427·λ₊` is what is owed. (c) Reconciling S3: S3's "the cubic collision dies for every `λ₋ ≥ 50`" was aimed at reaching `λ₋ ~ 1.75e21` (S1's double-log world = the PRE-D1 demand). Post-D1 the demand is `λ₋ ∈ [73, 278]`, and S3's own joint already certifies the LANDED register to `λ₋ ≤ 13381` with the cap / `≤ 20048` without. **S3's D1 and D2 become dead weight post-D1. Only S3's D4 (`K ≤ 1.789e8·(log₂M+1)`, kernel-green at its P1c) is live, and only for branch (a) at the bracket top.**

**(2) THE ω ROUTE (S4's I-1) — DO NOT FIRE.** Priced honestly: `hPHheadroom`'s `8·(4^⌊ε²H₊⌋)²·ω ≤ x` (`Regime.lean:116`) has exactly one consumer, `deficit_le_log_two` (`BudgetDeficit.lean:46`), and only through `u := 8·P_H²ω/x ≤ 1` feeding `entropy_residueWindow_ge` (`ResidueUniform.lean:536`). The information-theoretic core (`log x ≥ log P_H − log 2`) is irreducible and, with `hheadroom : Hhi ≤ x/ω` alone, already yields `Λ ≥ λ₊ − o(1)` (S4's `probe_irreducible_floor`) — so the repair's entire yield is `Λ: e^{λ₊} → λ₊`, **exactly one exponential**. Post-D1 that exponential is worth **two units of K** at the working point (K = 2 → K = 0), on a parameter that is free up to `1.7e8` landed / `2.06e10` scaled. A D-tier spine re-proof (re-derive `ResidueUniform.lean:536` + `hPHheadroom` + its 7 register reads) for 2 units of a free integer. Genuinely an over-ask in the statement — and genuinely not worth repairing.

**(3) THE PER-BLOCK CAP REPRICE — MOOT.** The cap's right side *already* grows like `2^K·M·(log₂M+1)`, i.e. exponentially in the register's own free parameter; there is nothing to reprice to make it "grow with `e^{λ₊}`". The constant (`/24`, vs the mandate's `5/48`, vs S3's D3 `/16`) is worth `log 2.5 = 0.92` in `λ₊` ≈ 1.3 units of `K`. Class A, worthless, do not fly.

**(4) FOURTH ROUTE — WHAT THE RESIDUAL ACTUALLY IS ON THIS FACE (two items, neither a mountain).**

*(i) THE CAP'S DISCHARGE, not its satisfaction.* `S16BaseScaleCap_gk` is CARRIED and never discharged — it is on the terminal's survivor list (`S16Budget.lean:93`) and stands as an antecedent of `logChowla2_witnessed_scale_final'` (`S16Budget.lean:787`). Post-D1 the obligation is to *prove* `loglog(A+s) ≤ log 𝒫₂/24`, i.e. to bound `Λ` from ABOVE. That is available: the builder's `x` is already at its floor — `RegimeParam.lean:339` returns `x = K·ω` with `K = 8H₊³ + 8P² + Ce` — so `log x ≈ 2·log4·ε²H₊` and `Λ ≈ e^{λ₊} + log(2.77ε²) = e^{λ₊} − 11.4`, within `O(1)` of the floor the probes are priced against; the only other x-inflator, the register's arm `s13GArm_gk`/`s13BlockExp_gk` (`S13FramesA.lean:1316`, `:1129`), contributes `Λ ≈ 400` at `K = 0` and `≈ 9.4·10^7` at `K = 6.8e7` — both far under. **Class C plumbing (monotone upper-bound chain on objects the floor already uses), not D-tier.**

*(ii) WHAT PINS `λ₋` POST-D1 IS NOT THE BUDGET — it is the M-LOWER ledger against `half`, and post-D1 that is FREE.* The budget only imposes a FLOOR (`λ₋ ≥ 72.8`). The register's `x0M` line, at the chain's own effective `x₀ ≥ 2^{1.55·10^44}` (`flags.md:18313`, X0MFL-TRACE — CARRIED, I did not re-derive it), forces **`λ₋ ≥ 101`** (kernel: `r3_x0_forces_lambda`), and the Mfl overflow (honest `Mfl ≥ 2^158`, `S16Budget.lean:672`) forces **`λ₋ ≥ 134`** (kernel: `r3_Mfl_forces_lambda`). Both were walls only because the budget's tower pinned `λ₋` from ABOVE; D1 deletes that ceiling, so both become free — and both *help* my face (larger `log₂M` = more cap ceiling). ⟹ **the freeze's post-D1 working point `λ₋ ≈ 73` is not admissible** (at `λ₋ = 73`, `half` permits `doorRowFloor ≤ 3.6e31` against `x₀`'s `1.55e44` demand — short by 12 orders). R1's joint should be re-run at `λ₋ ≥ 101`, and the natural point is the LANDED witness `λ₋ = 400·log 2 = 277.2589` (`S15Witness.lean:787`), where I certify branch (b) at `K = 0`. The one genuinely irreducible residue here is the Siegel-ineffective `x₀` itself — research-tier, untouched by anything on this face.

## 4. RECOMMENDATION

1. **Delete CLAIM 3 from the freeze** and replace it with the cap-face law `λ₊ ≤ (49 + K + log₂M)·log 2 + log(log₂M+1) − 2.85` (`r3_cap_fit`). S4's report is not at fault — its §4 table and its "23 orders" are correct **pre-D1** statements (`λ₊ ≥ λ₋ ≥ e^{budgetX}`); the freeze imported them across D1, where they evaporate. On this face **D1 alone closes the S4/S3 collision**, exactly as S4's own §5 predicted ("only the budget's `logloglog` demand can move this face").
2. **Branch (a) vs (b): my face does not discriminate — both close, and branch (a) is the cheaper one HERE** (nothing needed at the sharp exponent 3.7436; S3's D4 K-re-cut only if the builder's actual `λ₊` sits near the bracket top 4.4077). The `k = 2` tower (S2, class C, 800–1200 ln) buys my face **nothing**. The branch must be decided on faces 1+2 — specifically against the register's `7.1448` width law, where branch (a)'s `λ₊ − λ₋ = 4.3·10^7` is fatal and branch (b)'s `4.23` fits; note S2 flags that `7.1448` as LAMBDA-RECON prose (`flags.md:17972-17982`, `S15Compose.lean:60,795`), **not kernel** — verify it before it decides a 1000-line build.
3. **Fire nothing on R3's face.** The next real items in my scope are the cap's discharge (class C) and, for the register generally, the two carried M-lower riders (Mfl overflow — already banked; `x₀` — Siegel, research-tier).