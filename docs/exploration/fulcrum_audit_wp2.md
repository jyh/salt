# FULCRUM AUDIT — WP2 (THE REPULSION): what the DH engine demands of the zero, and what it delivers
Auditor: WP2 subagent, 2026-07-18. All claims GROUNDED (file:line) unless marked MEMORY.
Scope: the T-BAL landed chain in `Salt/SW/` + freeze `docs/exploration/tbal-s0-freeze.md`
+ consumers per `docs/exploration/s3-hb3-design.md` + `docs/exploration/sigma_window_budget_analysis.md`.

## 0. The contract (what the engine promises)

GROUNDED DHRepulsion.lean:262–275 (prose contract, 16/17 window ratified 2026-07-18
contingent on the σ-budget analysis; ordering `ρ.re ≤ β₀` = T-BAL-UNORDERED):

    dh_repulsion_ordered: ∃ b c k (witnesses b=680, c=2^{−250}, k=14, freeze:9/AM.1):
    χ real primitive mod q ≥ 2, L(β₀)=0, 1/2 < β₀ < 1;  L(ρ)=0, ρ.im ≠ 0, |ρ.im| ≤ 1,
    16/17 ≤ ρ.re < 1, ρ.re ≤ β₀  ⟹  1−β₀ ≥ c·(q(|Im ρ|+2))^{−b(1−ρ.re)}/(log(qT)+2)^k

LANDED state (flags.md:11039–11207 + grep): `dh_master_ray` (TBalR8.lean:98), ALL 5 row
caps + `ray_pow_bound` engine (TBalR8.lean:268–955), guard discharges `tbal_hscale/
tbal_hguard/tbal_hcov` (TBalR8.lean:959–1305), `dh_balance` (TBalR7.lean:100), `H_lower`
(CrushH.lean:65), `L1_lower_siegel` (DHCore.lean:808), extractions (DHExtractW.lean:1163,
TBalCompose.lean:489), `zfr_harvest` (DHBal.lean:62), `selberg_opt_eq` (SelOpt.lean:440),
`tail_shift_to_beta0` (SelWeight.lean:381). The ONLY unlanded producer piece: the R8c
final assembly (trivial split + by_contra inversion into the contract ∃-shape) —
dispatched per flags/git (cf2f0c0), no `theorem dh_repulsion_ordered` in Lean yet.
**[STALE — corrected 2026-08-02 by HB-CENSUS: this line was written at cf2f0c0,
one commit before the landing. `dh_repulsion_ordered` LANDED at f1b92ca
(2026-07-18, TBalR8.lean:1752, 3 axioms, audit-registered All.lean:305). The
§3 T-BAL-BUDGET demand-side audit below remains the lane's one genuine open
item, gated on the consuming node.]**

## 1. WHAT THE REPULSION SIDE DEMANDS OF THE ZERO (link by link)

### 1a. Of the REAL zero β₀ (the Siegel zero itself)
- `dh_master_ray` (TBalR8.lean:98–104): `L(β₀)=0`, `1/2 ≤ β₀ < 1`. NOTHING else — no
  rate, no 1−β₀ smallness hypothesis on the zero itself. The deep-regime guards
  (`hscale : N^{1−β₀} ≤ e`, `hguard`, `hcov`) are SCALE choices discharged on the
  contradiction ray by tbal_hscale/hguard/hcov (TBalR8.lean:959–1305); in the trivial
  branch `u ≥ 1/(40L₂)` the contract is immediate (`tbal_tau_le_split`, TBalR8.lean:44).
- `L1_lower_siegel` (DHCore.lean:808–816): consumes the SAME zero at the Siegel scale
  `N=⌊e^{1/u}⌋` to deliver `L(1,χ).re ≥ 0.27(1−β₀)(2−β₀)` — PV-grade, single-χ,
  effective. This is where the β₀ zero is cashed; quality consumed = vanishing only.
- `dh_extraction_upper_W` (DHExtractW.lean:1163–1175): consumes the VANISHING
  `L(β₀)=0` for pole-cancellation (freeze:12 — "every 1/(1−s) completed to
  L(s,χ)=0; exactly ONE u^{−1} dust survives at β₀" = the `144M/(1−β₀)` term in C₂).
- **FOSSIL CHECK (catch-#224 genre, CONFIRMED against corpus catch #239,
  flags.md:11095–11097):** the β₀-range `1−1/(4(1+log q)) ≤ β` named in the task brief
  belongs to the OLD M4 inverter `dh_repulsion_of_LFunction_one_lower`
  (DHBalance.lean:196–201) / `LFunction_one_re_le_mvt_sharp` (SiegelClose.lean:458–461).
  The live R8 route does NOT consume it — R8 inverts by contradiction on the ray; "M4
  plays NO role" (flags.md:11097). The engine's true β₀-range demand is `1/2 < β₀ < 1`.

### 1b. Of the COMPLEX zero ρ (the repelled zero)
- `dh_master_ray`: `L(ρ)=0`, `1/2 ≤ ρ.re < 1`, `|ρ.im| ≤ 1`, `ρ.re ≤ β₀`. Note:
  `ρ.im ≠ 0` is NOT needed by the master — it enters only via `zfr_harvest`.
- **The 16/17 window** is consumed ONLY by the §5 on-ray row caps (row_1x_cap:406,
  row_A_cap:446, row_rho_main_cap:598, row_Eβ_cap:737, row_Eρ_cap:863 — each takes
  `hσlo : 16/17 ≤ σ`): the b=680/k=14 exponent law needs the net Q-power
  `104w − 680w(1−14w) ≤ 0` ⟺ `w ≤ 576/9520 ≈ 0.06050` (σ ≥ 0.93950) and the L₂-power
  `1 − 14(1−14w) ≤ 0` ⟺ `w ≤ 13/196 ≈ 0.06633` (TBalR8.lean:262–265 docstring + :307,
  :311). Frozen `w ≤ 1/17 ≈ 0.05882` — thin visible slack (σ could drop to ≈0.9395 at
  the SAME witnesses). The deeper generator is the ledger: W=14 is "the UNIQUE integer
  with η_E = η_A at every σ, forced by E-grade G=13 ⟹ W ≥ 13·17/16" (freeze AMENDMENT
  1, tbal-s0-freeze.md:36–38); widening below ~0.9395 requires raising b (weakening
  every delivered exponent) or a better E-grade (T-BAL-SIGMA-SLIVER, class D).
- **The |Im ρ| ≤ 1 restriction**'s true home: the `hZ` box hypothesis
  `∀ s, 1/2 ≤ Re s ≤ 1 → |Im s| ≤ 1 → ‖zetaHol s‖ ≤ Z₀` threaded through
  `dh_extraction_upper_rho` (TBalCompose.lean:493, applied AT ρ: :515) and the whole
  crush chain. Extending to |γ| ≤ T₀ = a taller zetaHol box + re-ledger; NOT demanded
  by any consumer (both contracts use |γ| ≤ 1; T = |γ|+2 ≤ 3, budget analysis §2 C1).
- **The ZFR consumption** (`zfr_harvest`, DHBal.lean:62–69): `ρ.im ≠ 0`, `9/10 ≤ ρ.re`
  (implied by 16/17 — budget C6) harvest `zero_free_region_all` (ZeroFreeReal.lean:605,
  c₀ = 1/126848, ∃-form in Lean) into `1/‖1−ρ‖ ≤ log(qT)/c₀`, `‖2−ρ‖ ≥ 1`. Quality
  consumed: a POLYLOG-grade zero-free region only, and it lands in the CONSTANT: the
  row-cap gate is `4/c₀·c^{3/17} ≤ 1/8` (row_rho_main_cap:605) = 2^{17+2−44.1} ≈
  2^{−25} vs 2^{−3} — ~22 binary orders of slack. The ZFR is nowhere near binding.
- **The ordering `ρ.re ≤ β₀`** (T-BAL-UNORDERED): consumed by `tail_shift_to_beta0`
  (SelWeight.lean:381, the exact termwise R1 shift). Grounded harmless downstream:
  ordering is automatic once η ≳ 1.4e5 via the landed ZFR, and for bounded η it matches
  Jutila Thm 2's own `β ≤ β₁`, which is what HB consumes (budget analysis §3;
  s3-hb3-design.md:940).

### 1c. Supply-side binding margin (inside the engine)
Per freeze AMENDMENT 1 (tbal-s0-freeze.md:40–48): after the W=14 retune the δ rows are
DELETED; the thinnest at-τ row is the E(β₀)-amp at q=3: 10^{−5.7} vs the 1/8 budget
(4.75 decades spare), all rows monotone-decaying on the ray; ledger law = rows capped on
the ray u < τ ONLY. The binding corner is q=3 (crush coverage margin 1.76x at the honest
u*-corner). So the engine's internal binding constraint is the q=3 E(β₀)-amplification
margin — an arithmetic margin, not a zero-quality demand.

## 2. WHAT REPULSION DELIVERS DOWNSTREAM (the WP2 consumers)

Inverted contract, per-zero: at scale x = Q^s the damping `x^{−(1−ρ.re)} ≤
η^{−s/680}·polylog` where η := ((1−β₀)L)^{−1} (budget analysis §1). Consumers
(s3-hb3-design.md, WP2 = Lemmas 3 & 7 chain, :850–853):
- **Lemma 3 (pretense sum)** `Σ_{χ(p)=1} p^{−1}log p ≪ L(log η)^{−1/4}` and
  **Lemma 7** `L′/L(1,χ) = ηL + O(L(log η)^{−1/4})`: consume the repulsion as
  `r₀ ≫ L^{−1}log η` (:824, :903–905 — "a zero-free region gives NO η-decay; the log η
  repulsion is what manufactures η^{−A}"), at the x-window `q^250 ≤ x ≤ q^500` (:817),
  under hypothesis (1.11): `1−β₀ ≤ (3log q)^{−1}`, η ≥ 3 — FIRST-power (:814–816).
  Multiplicity: only polynomially many near-1 zeros, supplied by the LANDED
  `LFunction_zero_count_near_one` (ZeroCountNearOne.lean:98–102, C = 7200, r < 1/2,
  with multiplicity, window-agnostic).
- **κS₁ → 𝔖C(α)(ηL)^{−2}** (:852): the worst named relative budget, A = 2.
- **Below the window**: [4/5, 16/17) is covered by the PLANNED crude density node
  `N(σ,T,χ) ≪ (qT)^{D(1−σ)}`, D ≤ 83 tolerated (3D < 250, :898–902); the narrowing
  extends its band from 9/10 to 16/17 at a quantified q^{6.9} margin cost, q^{9.82}
  retained (budget C3). NOT yet landed — consumer-side condition 3 of the verdict.
  The sliver [9/10,16/17) itself: trivial 1/17-strip dominates (budget §1: at b=680
  the repulsion's content zone is ≤ 1/1360-wide, deep inside [16/17,1); anchor q=20,
  s=250: sliver 1.06e−10 vs budget 2.93).
- **Also unlanded on the consumer path** (WP2 AMENDMENT, s3-hb3-design.md:886–910):
  the sharp ψ(y,χ) explicit formula with ENUMERATED zero sum (CATCH #47 — the landed
  stack is smoothed-ψ₁ with zeros assumed away); L′/L+Prachar assembly; Lemma 3/7 glue.

## 3. THE KEY QUESTION — zero-quality per stage, and the binding constraint

| Stage | Zero-quality consumed | Binding? |
|---|---|---|
| dh_master_ray + extractions | vanishing only; β₀ > 1/2; σ ≥ 1/2; |γ| ≤ 1 | no |
| row caps (window law) | 16/17 ≤ σ (true law σ ≥ 0.9395) | supply-side shaper |
| zfr_harvest | polylog ZFR at c₀ = 1/126848 | no (2^{−25} vs 2^{−3}) |
| ledger at-τ rows | none (arithmetic) | q=3 E-amp 10^{−5.7} vs 1/8 |
| Lemma 3/7 (consumers) | η ≥ 3 first-power on β₀; per-zero η^{−s/680} | — |
| κS₁ main term | η^{−A}, A = 2 worst | **THE OPEN AUDIT** |

**The demand-side binding constraint is the witness grade b = 680 vs the η^{−A}
budget** (T-BAL-BUDGET, registered: tbal-s0-freeze.md:18 condition 4;
sigma_window_budget_analysis.md §3; s3-hb3-design.md:1256–1257 MEMORY-grade pointer).
The witnesses deliver per-zero η^{−s/680} = η^{−0.368} at s=250 (η^{−0.735} at the
window top s=500). The budget analysis asserts this is "sufficient for every polylog(η)
and η^{≤2} need" (its §3) — but a naive per-zero comparison for UNBOUNDED η
(η ≤ 25e·√q(1+log q)²/(0.1L) ceiling, budget C2) gives η^{−0.368} ≥ q^{−0.184}polylog
against a needed η^{−2} ≥ q^{−1}polylog: the per-zero exponent alone does NOT
majorize A=2, so sufficiency rests on the composition (count × strip × x-tuning), and
the freeze itself mandates the witness-grade audit BEFORE the consuming node. Honest
verdict: **unresolved, registered, and it is the fulcrum-relevant constraint** — a
fulcrum weakening that degrades b (or the log η grade) eats directly into it, while the
literature grade (Jutila Thm 2, b ≈ 2+ε, s3-hb3-design.md:937–944) has ~2 orders of
exponent headroom (s/2 vs s/680).

**Effectivity** is preserved end-to-end: L1_lower_siegel/H_lower are PV-grade single-χ
(no Siegel ineffectivity); Jutila's route "does not appeal to Siegel's theorem"
(s3-hb3-design.md:947–950) matching HB's effective C^(1); c₀ is existential in Lean but
effective in principle (1/126848 docstring-grade, freeze:13). The fulcrum hypothesis F
therefore needs to supply only: infinitely many real primitive χ with a real zero at
FIRST-power quality 1−β₀ ≤ (3 log q)^{−1} (η ≥ 3) — the engine itself asks nothing of
the zero beyond β₀ > 1/2 + existence; every stronger demand lives on the consumer side.

## 4. Slack summary (where a weaker F could still ride this chain)

1. β₀-quality: engine needs β₀ > 1/2 only; the η ≥ 3 (first-power) grade is consumed
   by Lemma 3/7's η-manufacture, and everything below η ≈ 1.4e5 additionally needs the
   ordered form's Jutila-style `β ≤ β₁` framing (benign). A fulcrum with weaker η-growth
   (e.g. η → ∞ along a subsequence, any rate) still feeds the engine; the consumers'
   (log η)^{−1/4} and η^{−2} budgets are where the rate is spent.
2. σ-window: 16/17 → ~0.9395 free at the same witnesses; below that costs b.
3. |γ| ≤ 1: a zetaHol-box constant away from |γ| ≤ T₀; no consumer wants it.
4. ZFR: ~22 binary orders of slack in c₀.
5. Quantity: one β₀ + one ρ per (q, χ) instance; multiplicity handled by the landed
   Prachar count. No density input to the ENGINE at all (density is consumer-side).

## 5. Open items blocking the composed engine (for the fulcrum statement)

- R8c final assembly (producer, dispatched, mechanical per flags.md:11182).
- T-BAL-BUDGET witness-grade audit (demand-side, REGISTERED-OPEN — the real risk).
- Crude density node covering σ ∈ [4/5, 16/17) (consumer, priced ~0.5–0.9M, :909).
- EF rebuild: sharp ψ(y,χ) with enumerated zeros (consumer, CATCH #47, ~0.6–1.0M).
- WP2 executes at s ≥ 250 and q₀ ≈ 20 (budget verdict conditions 1–2, free under
  InfinitelyManySiegelZeros).
