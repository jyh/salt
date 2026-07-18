# σ-WINDOW BUDGET ANALYSIS — dh_repulsion 9/10 → 16/17 narrowing
Analyst draft (wf_b116a106). Ledger: `sigma_window_ledger.py` (same dir, ALL PASS).
Every file:line below re-read this session (GROUNDED unless marked MEMORY).

## 0. The question and the two contracts

- OLD prose contract (GROUNDED DHRepulsion.lean:262–269): `dh_repulsion` covers
  complex zeros ρ with `9/10 ≤ ρ.re < 1`, `|ρ.im| ≤ 1`, giving
  `1−β₀ ≥ c·(q(|γ|+2))^{−b(1−ρ.re)}/polylog^k` — constants FREE (∃ b c k).
- NEW frozen target (GROUNDED tbal-s0-freeze.md:14): `dh_repulsion_ordered`,
  window `16/17 ≤ ρ.re < 1` (plus `ρ.re ≤ β₀`), witnesses `b:=680, k:=14, c:=2^{−250}`.
- Ratification gate (GROUNDED tbal-s0-freeze.md:18): "no landed Lean consumer,
  grep-confirmed; consumer = WP2". Independently re-confirmed this session:
  `grep -rn dh_repulsion Salt/` shows no landed theorem CONSUMES the 9/10 window
  (details §4); the consumers are the PLANNED WP2 shapes (s3-hb3-design.md).
- Charter (GROUNDED pilot.md:8069–8079): JYH approved "contingent on the budget
  analysis"; key structural check = does the trivial 1/17-strip on [9/10,16/17)
  dominate every consumer's needed savings.

## 1. THE CORE STRUCTURAL RESULT (consumer-independent, witness-grounded)

The narrowed band was VACUOUS-IN-USE even under the old contract. With the frozen
witnesses, the repulsion inequality (inverted) gives a zero ρ the floor

    1 − ρ.re ≥ [log η + log L − 14·log L₂ − 250·log 2] / (680·log Q),
    η := 1/((1−β₀)·L),  Q := q(|γ|+2) ≤ 3q.

This floor exceeds the trivial strip 1/17 only when `log η > (680/17)·log Q`,
i.e. **η > Q^40**. But η is capped by the effective Siegel/class-number ceiling
`η ≤ C′·q^{1/2}·polylog` (from `LFunction_one_re_le_mvt_sharp`,
DHBalance.lean:187–201, inverted against L(1,χ) ≫ q^{−1/2}): exponent 1/2 vs 40 —
**a factor-80 gap**. So for EVERY zero with ρ.re < 16/17 and every feasible η,
the trivial strip `x^{−(1−ρ.re)} ≤ x^{−1/17}` is the STRONGER bound; the
repulsion's entire content zone is `1−ρ.re ≲ (log η)/(680·L) ≤ 1/1360·(1+o(1))`,
deep inside [16/17, 1). Removing [9/10, 16/17) removes only territory where the
theorem was already dominated by the strip. Per-zero at the consumer's window
bottom x = q^250: strip = q^{−250/17} = q^{−14.71}; worst-case repulsion-grade =
η^{−250/680} ≥ q^{−0.184}·polylog — the strip is 80× stronger in the q-exponent.

Caveat honestly recorded: with a LITERATURE-grade witness b ≈ 2+ε (Jutila Thm 2,
design s3-hb3-design.md:937–944), the content zone (log η)/(2L) can reach ≈ 1/4
> 1/17 at maximal η — a sharper future theorem COULD carry content in the sliver.
The freeze's residual `T-BAL-SIGMA-SLIVER` (tbal-s0-freeze.md:18) already
registers this recoverable-via-class-D note. For THIS ratification the consumers
consume OUR b=680 theorem, for which the sliver is provably content-free.

## 2. Consumer-by-consumer (each with one concrete numeric anchor)

### C1 — WP2 Lemma 3 (pretense sum) + Lemma 7 (L′/L) — the log-η chain
GROUNDED s3-hb3-design.md:850–853: needs `Σ_{χ(p)=1} p^{-1}log p ≪ L(log η)^{−1/4}`
and `L′/L(1,χ) = ηL + O(L(log η)^{−1/4})`; s3-hb3-design.md:815–817: hypothesis
(1.11) η ≥ 3, x-window `q^250 ≤ x ≤ q^500`; :824, :903–905: the repulsion consumed
is `r₀ ≫ L^{−1}log η` ("the log η repulsion is what manufactures η^{-A}").
Zone split at scale y ∈ [q^250, q^500]:
- [16/17, 1): narrowed theorem applies → per-zero `y^{−(1−β)} ≤ η^{−s/680}·polylog`
  (s = log y/log q ≥ 250) → η-power decay, over-delivering the (log η)^{−1/4} need.
  Counts: `LFunction_zero_count_near_one` (ZeroCountNearOne.lean:15–39, radius-
  resolved, C = 7200, r < 1/2 — window-agnostic) — polylog multiplier.
- [9/10, 16/17) SLIVER: trivial strip. Total ≤ slab·T^{D/17}·q^{−(s−D)/17} with the
  design's own crude-density tolerance D ≤ 83 (3D < 250, s3-hb3-design.md:898–902)
  and T ≤ 3 (|γ| ≤ 1 in both contracts). **Anchor q = 20, s = 250, η = 3:
  sliver = 1.06e−10 vs Lemma-3 budget L(log η)^{−1/4} = 2.93 — margin 2.8e10.**
  At q = 10^6: 3.4e−56 vs 13.5. TOLERATES.

### C2 — WP2 κS₁ → 𝔖C(α)(ηL)^{−2} (the η^{-A} manufacture, worst A = 2)
GROUNDED s3-hb3-design.md:852. Relative budget (ηL)^{−2} with the pessimistic
ceiling η ≤ (25e/0.1)·√q·(1+log q)²/L. Sliver/budget ratio is monotone
decreasing in q; **crossover in q ∈ (16, 20)** (ratio 1.32 at q=16, 0.25 at
q=20, 1.0e−6 at q=100, 7.5e−40 at q=10^6). The q ≤ 16 corner is VACUOUS for
this consumer: `InfinitelyManySiegelZeros` supplies unboundedly many moduli, and
HB Corollary 2's effective C^(1)/q₀ (s3-hb3-design.md:818–821, 947–950) absorbs
any finite prefix — the WP2 proofs may fix q₀ = 20 freely. Headroom: the strip
covers ANY η^{−A} consumer with A ≤ 19 asymptotically ((s−D)/17 = 9.8 > A/2);
HB's max named A = 2, a 9.8× exponent margin. TOLERATES.

### C3 — WP2 crude zero-density node (the tail below the repulsion window)
GROUNDED s3-hb3-design.md:898–902, 1064–1066. The narrowing EXPANDS the density
band from [4/5, 9/10) to [4/5, 16/17) — this is the one place the change has a
real (quantified) cost. Crude large-sieve densities `(qT)^{D(1−σ)}` are valid on
the whole band (16/17 < 1; [9/10,16/17) ⊂ [4/5,1)). Band-top contribution
`q^{−(s−D)(1−σ)}` at s = 250, D = 83: **old top (σ=9/10) q^{−16.70} → new top
(σ=16/17) q^{−9.82} — a q^{6.88} margin loss, with q^{9.82} of power-saving
retained** (the ~33× tolerance claim survives; still crushes every η-power
budget per C2). TOLERATES, with the margin-loss number recorded.

### C4 — VMVT / VK chain — FALSE ALARM CONFIRMED
`grep -rn "repulsion|9/10|16/17" Salt/Vmvt/ Salt/Vk/` → EMPTY. The VMVT→VK→MR
chain (pilot.md:7707–7732) is the ζ Vinogradov–Korobov pipeline — it neither
consumes dh_repulsion nor any σ-window of it. Named in the gate text
(tbal-s0-freeze.md:18) only as a re-check item. NOT A CONSUMER.

### C5 — N-HDOM — FALSE ALARM CONFIRMED
GROUNDED pilot.md:5382, 6456, 7364: N-HDOM is the Maynard-side Shiu-block
domination node (`hdom` in GEH_min = ShiuCore + N-HDOM). No repulsion or
σ-window reference anywhere in its docs. NOT A CONSUMER.

### C6 — zfr_harvest (T-BAL's own K1 rung) — landed, tolerates trivially
GROUNDED DHBal.lean:62–69: takes `hlo : 9/10 ≤ ρ.re` as HYPOTHESIS (an
ingredient, not a consumer). Under the narrowed contract R8 calls it at
16/17 ≤ ρ.re, and 16/17 = 0.9412 > 0.9 — implied by `linarith`. TOLERATES.

### C7 — dh_repulsion_of_LFunction_one_lower (M4) + dh_repulsion_partial — unaffected
GROUNDED DHBalance.lean:196–201, DHClose.lean:154–162: both windows are on the
REAL zero β (`1 − 1/(4(1+log q)) ≤ β`); neither mentions ρ.re. The M4 threshold
interacts with the trivial split u ≥ 1/(40L₂) (tbal-s0-freeze.md:9), not with σ.
UNAFFECTED.

## 3. The additional deltas observed (flagged, not part of this verdict)

- **Ordering hypothesis `ρ.re ≤ β₀`** (frozen target, tbal-s0-freeze.md:14; kept
  as T-BAL-UNORDERED per :11). Bonus arithmetic: for complex zeros the landed
  `zero_free_region_all` (c₀ = 1/126848, DHBal.lean:55,70) gives
  `1−ρ.re ≥ c₀/log(3q)`, so the ordering holds AUTOMATICALLY once
  η ≥ log(3q)/(c₀L) ≈ 1.4e5 (anchors: 1.47e5 at q=10³, 1.37e5 at q=10⁶) —
  absorbable into HB's effective C^(1). For bounded η the ordered form matches
  Jutila Thm 2's own `β ≤ β₁` (design :940), which is what HB consumes. Benign,
  tracked separately.
- **T-BAL-BUDGET** (pilot.md:7777–7779, s3-hb3-design.md:1256–1257): the
  witness-GRADE audit (Λ orders below Benli; log-η budget vs b=680/k=14) is a
  separate open register item, orthogonal to the window question. The η-exponent
  the witnesses deliver at s=250 is s/b = 0.368 — sufficient for every polylog(η)
  and η^{≤2} need above, but that audit should still run before the consuming node.

## 4. Landed-consumer sweep (re-verification of the freeze's grep claim)

`grep -rn dh_repulsion Salt/` — every hit is the repulsion chain itself
(DHRepulsion/DHContour/DHClose/DHBalance/DHMollified/DHMain/DHBal/MoebiusLog/
MoebiusRateSharp docstrings + All.lean exports). The only landed theorems with a
9/10 σ-hypothesis in the SW L-function corpus: `zfr_harvest` (C6 — implied by
16/17) and the Siegel–Walfisz contour stack (ShiftAssembly.lean:57–60,
ShiftTrivChar.lean:60–65, MobiusRateClose.lean:215, CharDispatch.lean:320,
EstermannInterface.lean:139) — all pre-dating and independent of dh_repulsion
(they bound contours/Landau-zero dichotomies, consume zero_free_region, never
dh_repulsion). Goldbach/Chen/Brun/Maynard 9/10-hits are unrelated numerics.

## 5. Verdict

**TOLERATES.** The fixed 1/17-strip is polynomially (x^{−1/17}-grade) strong
where every consumer needs at most η-power/log-grade savings, and with the
frozen b = 680 the repulsion inequality was ALREADY weaker than the trivial
strip everywhere below 16/17 (content zone ≤ 1/1360-wide vs strip 1/17) — the
narrowing costs nothing against the frozen design. Quantified residual costs:
the density band-top margin drops q^{−16.70} → q^{−9.82} (C3), and the A=2
relative budget requires q ≥ 17-ish (C2) — both inside the consumers' own
regimes. No consumer needs repulsion inside [9/10, 16/17).

Conditions attached (all already registered or absorbable):
1. WP2 executes at the design's x-window s ≥ 250 (s3-hb3-design.md:817); any
   future lemma applying the explicit formula at x < q^34 (where s/17 < 2)
   re-opens the sliver check.
2. WP2's proofs fix q₀ ≈ 20 (or fold into effective C^(1)) — free under
   InfinitelyManySiegelZeros.
3. The crude density node must cover σ up to 16/17 (band extension; standard
   for large-sieve densities, ~q^{6.9} margin cost quantified in C3).
4. T-BAL-BUDGET witness-grade audit still runs before the consuming node
   (separate, already-registered item).
5. If dh_repulsion is ever re-proved at literature grade b ≈ 2, re-audit the
   sliver (content zone then ≈ 1/4 > 1/17) — the registered T-BAL-SIGMA-SLIVER
   residual.
