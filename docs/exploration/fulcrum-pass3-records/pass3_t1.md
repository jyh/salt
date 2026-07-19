# PASS-3 T1 — THE DEFLATION AUDIT (KC(b) walk)

**Question.** Does C1 (effective uniform SW under ¬F) deflate because the landed
consumers only need per-q effective SW? **Answer: NO — deflation KILLED, C1 HOLDS.**

## 1. The consumption walk (every SW use in the landed chain, classified)

| # | Site (GROUNDED) | What is consumed | Classification |
|---|---|---|---|
| W1 | `Salt/BV/Defs.lean:35-38` | The Prop: ONE `K` for ALL `q ≤ (log x)^C` | uniform-in-q by statement |
| W2 | `Salt/SW/Gate.lean:376` → `AbelCore.lean:757` → `PsiToPi.lean:144` → `DispersionClose.lean:443` | full Prop threaded to `psi_BV_of_siegelWalfisz'` (∀A form) | pass-through |
| W3 | `Dispersion.lean:778` `psi_BV_of_siegelWalfisz (_hSW ...)` | `_hSW` UNUSED — SW enters ONLY via the `hlargeY` slot | localizes the audit |
| W4 | `DispersionClose.lean:181-182` (`largeY_bound`) | extracts ONE `K` from `psiChi_le_of_siegelWalfisz_absorbed` at saving `4A+19`, cutoff `C_sw = 2(A+6)` | **uniform-in-q** |
| W5 | `DispersionClose.lean:268-276` (`hSWloc`) | that single `K` asserted for ALL conductors `2 ≤ f ≤ (log x)^{A+6}`, ALL non-principal χ mod f | **uniform-in-q** (unbounded family, grows with x) |
| W6 | `Dispersion.lean:425-479` (`smallEnergy_le`) | sums the per-χ bound over `#T ≤ (log x)^C` conductors × `φ(f)` primitive χ each; count argument needs the conductor-uniform `K`; the (potential) exceptional χ is NOT separated | **uniform-in-q, NOT summable** (see §2) |
| W7 | `SWChar.lean:100` (`psiChi_le_of_siegelWalfisz`) | one `hSW A C` call → `K` used at every `(f,a)`, `f ≤ (log x)^C` | uniform-in-q |
| W8 | `Defs.lean:79` (`siegelWalfisz_psiTot`, q=1) → `Chen/TripleCount.lean:67`, `TwinBar/LambdaRate.lean:15-57` | q=1 instance only | **per-q** — effective PNT serves these WITHOUT C1 (the only genuine per-q consumers) |
| W9 | `Goldbach/A1.lean:328`, `A1W.lean:371`, `Op.lean:217` | `psi_BV_...' 11` — BV at FIXED saving A=11 | uniform-in-q (11 > 2, see §2) |
| W10 | `Maynard/LevelConsume.lean:39` (`lod_error_pow`) | `hLoD (9k² + 2B)`; at :339 `B = 2k+4`; k = k₀ with `hk3072 : 3072 ≤ k₀` (:614) and `k₀ ≥ ⌈e³⁰⁰⌉` (:616-621) | **the demanded BV saving: A ≥ 9·3072² = 84,934,656; in fact A ≥ 9e⁶⁰⁰** |

## 2. The kill arithmetic (against MNT Thm 24.22's explicit E₁)

The deflation route would re-plumb W4-W6 by MNT 24.22/24.25 (GROUNDED
montgomery3.txt:7504-7537): ψ(y,χ) = E₀x − E₁·y^{β₁}/β₁ + O(y·exp(−log y/(c₁log f +
(log y)^{2/5}(log log y)^{1/5}))), **c₁ effective** (effectivity remark GROUNDED
montgomery3.txt:7576-7614: "c₁ is effective... x₀(A) is not"). Non-exceptional part: for
f ≤ (log y)^{A+6} the error is ≪ y·exp(−c(log y)^{3/5-ε}) — beats every log power,
effective. Fine. Exceptional part: at most one exceptional χ₁ of conductor f₁ in the
range (Page uniqueness, GROUNDED montgomery3.txt:7329, 21688-21710); its slot in
smallEnergy_le (weight 1/φ(f₁), `Dispersion.lean:430`) receives y^{β₁}/β₁.

Effective repulsion (MEMORY, classical Landau/h(−d)≥1): 1−β₁ ≫_eff f₁^{−1/2}(log f₁)^{−2}.
Write f₁ ≍ (log y)^θ. Then (1−β₁)·log y ≫ (log y)^{1−θ/2}/(log log y)²:
- θ < 2: y^{β₁} ≤ y·exp(−c(log y)^{δ}) — effectively negligible. Covered.
- θ ≥ 2: exp factor → 1; the term is y·(log y)^{−θ+o(1)} (the φ(f₁)-weight is the only
  saving). The slot needs ≤ K·y/(log y)^{2A+7} (`DispersionClose.lean:269`).
  **Uncovered band: θ ∈ [2, 2A+7) — NONEMPTY FOR EVERY A > 0** (even A→0⁺ leaves [2,7)).

So the effective-explicit-E₁ re-plumb caps the unconditional effective BV saving at
A < 2−ε (the classical effective-BV cap, MEMORY). Landed demand (W10): A ≥ 8.5×10⁷
(numerically: 9·3072² = 84,934,656; with k₀ ≥ e³⁰⁰, A ≥ 9e⁶⁰⁰). Even the fixed
Goldbach consumption (W9) sits at 11 > 2. Gap: 7+ orders of magnitude in the exponent
at the conservative bound. The criterion "summable-over-exceptional-moduli" FAILS at
every consumption site W4-W7, W9, W10.

## 3. What a "deflation" would actually require

Carrying the E₁ term in the approximant (Linnik-style: dispDisc against
x/φ(q) − χ₁(a)y^{β₁}/(φ(q)β₁)) is NOT a deflation of the landed consumers: it rewrites
`dispDisc` (`Dispersion.lean:153`) and forces the Maynard main-term calc
(`LevelConsume.lean` L2-L4b) to absorb a χ₁-twisted secondary term — a redesign whose
viability is exactly the H-B/Siegel-zero dichotomy (the ¬F horn itself), not
"already-effective per-q SW". Honest-shape law: not presentable as an existing route.

## 4. Verdict + partial record (the "which parts" clause)

- **DEFLATION KILLED; C1 HOLDS** as the ¬F flagship cash-out. The landed BV chain's SW
  consumption is genuinely uniform-in-q and non-summable over exceptional moduli at
  every demanded saving.
- Genuinely per-q (already effective without C1, record for the floor): the ψ-PNT
  consumers only — `Chen/TripleCount.lean:67`, `TwinBar/LambdaRate.lean` (q=1 instance
  W8). No BV-grade consumer deflates.
- Banked wall-theorem candidate: **the θ∈[2, 2A+7) exceptional-conductor wall** (§2) —
  the Siegel wall enters the landed chain at conductor exponent exactly 2, and the
  Maynard demand sits at ≥ 9·3072². (D3 re-ratification: program valuation on C1 stands.)

Labels: file:line cites above GROUNDED (read this session); MNT cites GROUNDED at the
listed txt lines; Landau repulsion + the effective-BV-cap-at-2 folklore MEMORY.
