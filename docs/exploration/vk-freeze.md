# VMVT-VK FREEZE (synthesis output, 2026-07-18 07:20 PT)

Chosen angle: minimal-power | dispatch_ready: True

## Open risks

- R3 (box-averaging measure stone) is the heaviest Lean work: folding real boxes into torusMeasure (restrict Ioc 0 1) with mod-1 disjointness in one coordinate; failure mode is measure-bookkeeping blowup, not mathematics — Zeno partial acceptable, surfaces early by dispatch order
- R4 orbit algebra: alternating-sign vkCoef and the binomial tail bound (steps in [s/2, 3s/2] under W2c) verified numerically but fiddly in Lean
- R8 mathlib audit open on the Euler-product lower bound |1/zeta(s)| <= zeta(Re s) for Re s > 1 (upper side landed via zeta_real_upper); budgeted fallback: hand Dirichlet-series argument off Zc machinery, +80 lines
- final constants are existential and astronomically lazy: new region beats landed c3/log only for log t > ~1e37 and VK rungs fire only for log t > ~1.5e26; the MR gate must consume the width SHAPE (theta = 3/4 < 1) — if any consumer needs dominance at accessible heights, min with the landed region in the consumer
- hW1's P+Y restatement threads through R1/R2/R5 statement shapes; drift between the freeze forms and the committed refuter script would silently un-verify the window arithmetic — keep them in lockstep

## Grafts

- [korobov verdict-2 -> R8] negative-gamma conjugation shim: zeta_growth_pow covers t >= t0 > 0 only, zeros carry either Im sign; one transport helper via mathlib riemannZeta_conj (absent from minpow's own verdicts)
- [korobov verdict-2 -> R10] eK/eR unification: vdC_second_derivative is stated in the private Kusmin character eK, consume via the eR_eq_eK switch (grounded Salt/ExpSum/DerivTest.lean:43, pattern inside zeta_block_kusmin)
- [korobov verdict-2 -> R8] center-floor sigma-side upper bound is LANDED: zeta_real_upper (Salt/SW/ZetaLowerShallow.lean:57, |zeta(sigma)| <= 1+1/(sigma-1)) — shrinks R8's mathlib-audit surface to the Euler-product lower step only, Moebius fallback +80 lines
- [korobov verdict-2 verify-posture -> process] commit the checkable refuter artifact: scripts/vk_minpow_check.py lands in the first Vk commit, updated for the applied repairs (W2b=1/6, hW1 radius P+Y)

## Executor notes

Judge re-grounded every disputed citation in the repo (grep) and reran the load-bearing arithmetic (ledger at k=19/100/5623414; W2b spread; firing boundary 1.48e26; trivial-only end 1.1e20; Lq(1e30)=1820, width 7.85e-12) — all pass. Both minpow verdict repair sets are APPLIED in the freeze; do not re-derive from the original candidate text. Dispatch order: R1,R2,R7,R10 independent starts; design stones R3 then R4 first among C-rungs so a stall surfaces early; R3/R7/R10 are independently valuable Zeno partials (R7 = LITT-LANDAU, R10 = LITT-COVER stone-3). First Vk commit MUST include scripts/vk_minpow_check.py (currently scratchpad-only), updated for W2b=1/6 and hW1 radius P+Y. hW1 is restated at radius P+Y — keep R1/R2/R5 statements consistent with it and derive the (1+Y/P)^{k+1} <= 2 slack from hD in R5. R6/R8: K, t0, T0 are existential — witness decimals are comments, never hypotheses. R7's elided existential-conjunct risk is RETIRED (both refuters read ZetaPartialFractions.lean:171-183 in full: all c-relative, affine transfer legitimate) but do the pre-read as an impl sanity check. R8 needs the [G] negative-gamma conjugation shim (riemannZeta_conj) — growth is stated for t >= t0 > 0 only. R10 consumes vdC_second_derivative through the eR_eq_eK switch (DerivTest.lean:43 pattern). Executor dispatches per house policy: model opus, node-name subagent_type.

## THE FREEZE

# VK-MINPOW freeze v2 (SYNTHESIS-JUDGED) — lazy power region from vmvt
Winner: minimal-power. Repairs from both its verdicts APPLIED; grafts from korobov marked [G].
TARGET (main, new Salt/Vk/ZeroFreePow.lean):
```lean
theorem zeta_zero_free_region_pow :
    ∃ c T₀ : ℝ, 0 < c ∧ 3 ≤ T₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 → T₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - c / ((Real.log |ρ.im|) ^ ((3:ℝ)/4) * (Real.log (Real.log |ρ.im|)) ^ (3:ℕ))
```
θ = 3/4 < 1 — MR gate satisfied. Design-grade witnesses c ~ 1e-8, T₀ ~ 1e30 are COMMENTS on the ∃, not frozen (branch-(c) tiles are ∃-form; see R6 repair). New theorem; landed zeta_zero_free_region untouched (consumers min existentials).

MID TARGETS:
```lean
def vkTheta (t : ℝ) : ℝ :=
  (1/1000) / ((Real.log t) ^ ((3:ℝ)/4) * (Real.log (Real.log t)) ^ (2:ℕ))

theorem zeta_growth_pow : ∃ K t₀ : ℝ, 1 ≤ K ∧ 3 ≤ t₀ ∧ ∀ σ t : ℝ, t₀ ≤ t →
    1 - vkTheta t ≤ σ → σ ≤ 3 → ‖riemannZeta (↑σ + ↑t*Complex.I)‖ ≤ K * Real.log t

theorem vk_block_core {k r N₀ P P' Y : ℕ} {t ρbl : ℝ} (hk : 19 ≤ k)
    (hr : r = ⌈(k:ℝ) * Real.log (4*(k:ℝ)^2)⌉₊) (hρ : ρbl = 1/(16*(k:ℝ)*r))
    (hP' : P' ≤ P) (hY : Y = ⌈(P:ℝ)^((1:ℝ)/2)⌉₊)
    (hD : 8*((k:ℝ)*Real.log (16*k) + 24*(k:ℝ)^2*r*Real.log k) ≤ Real.log P)
    (hW1 : t * (((P+Y:ℕ):ℝ)/N₀)^(k+1) ≤ ((N₀:ℝ))⁻¹)   -- REPAIR: radius P+Y
    (hW2 : ∃ js ∈ Finset.Icc 2 (k-1), VkSpaced t N₀ P Y js ρbl k) :
    ‖∑ n ∈ Finset.Ioc (N₀:ℤ) (N₀+P'), eR (phi t n)‖ ≤ 8 * (P:ℝ)^(1-ρbl)
-- VkSpaced := P^{−js−ρ}/(4k) ≤ t/(2πN₀^{js+1})  (W2a separation)
--   ∧ t·Y/(2πN₀^{js+1}) ≤ 1/6  (W2b, REPAIRED 1/4→1/6: orbit spread (3/2)(1/6)=1/4
--     matches R3's length-1/4 window; deep-anchor W2b margin e^{-1e25}-grade, free)
--   ∧ 4k²Y ≤ N₀  (W2c linearity)
```

ROUTE (short blocks + lazy exit, NOT the MV3 bilinear machine). One k per t: k(t)=max(19,⌈L^{1/4}⌉), L:=log t; r=⌈k·log4k²⌉, b=kr, ρ=1/(16kr). Fixed-k barrier forces k→∞; α=1/4 balances D-floor vs trivial floor: θ=3/4.

RUNGS (10; new Salt/Vk/; NO class D — R3/R4 are the design stones, C):
R1 VK-TAYLOR (B, ~120): phi_taylor_block: |phi t (N₀+m) − phi t N₀ − Σ_{j∈Icc 1 k} vkCoef t N₀ j·m^j| ≤ 2(t/2π)((P+Y)/N₀)^{k+1} for m ≤ P+Y < N₀; vkCoef t N₀ j := −(t/2π)(−1)^{j−1}/(j·N₀^j). Via landed logD/logD_hasDerivAt (Salt/ExpSum/ZetaBlock.lean:141/:148) + mathlib taylor_mean_remainder_lagrange. Factor ≥ 2(k+1) Lagrange slack; under (W1) block phase error ≤ (P+Y)/N₀ ≤ 1.
R2 VK-SHIFT (B, ~90): eR_lipschitz ‖eR x − eR y‖ ≤ 2π|x−y|; block reduction to pure polynomial sum + 2π(P+Y)·R_taylor; shift identity |S| ≤ |S_y| + 2Y.
R3 VK-BOX-AVG (C, ~220, measure stone): vk_box_disjoint_avg: α(y)∈ℝ^{Deg k}, y=1..Y, j*-coords pairwise 2δ-separated mod 1 inside a length-1/4 window ⟹ (1/Y)Σ_y‖genFun k (Ioc 0 P) (α y)‖^{2b} ≤ 2^{2b−1}[(Π_jδ_j⁻¹)/Y·Jk k b (Ioc 0 P) + Slack^{2b}], Slack = 2πPΣ_jδ_jP^j. integral_norm_pow_eq_Jk (Salt/Vmvt/Fourier.lean:259) RIGHT-to-LEFT + genFun 1-periodicity (integer powers) folds boxes into torusMeasure; HolderTwo idioms scaffold.
R4 VK-POINTWISE (C, ~260, THE stone): vk_block_core. R2 shift-average (Jensen) → orbit β_j(y) = Σ_{i≥j} C(i,j)·vkCoef_i·y^{i−j}; j*-step s = t/(2πN₀^{j*+1}) ∈ [4δ_{j*}, 1/(6Y)], δ_j := P^{−j−ρ}/(16k); (W2c) ⟹ steps ∈ [s/2, 3s/2] ⟹ boxes disjoint → R3 → vmvt (Salt/Vmvt/Summit2.lean:151) + Jk_mono (P'≤P). LEDGER (Σ=1/2, judge-reverified k=19/100/5623414): 2bρ=1/8 | kρ=1/(16r) | η≤1/8 by r-choice | log_P((16k)^k·k^{24k²r})≤1/8 by hD. (2Y)^{2b} ≤ P^{(1−ρ)2b}.
R5 VK-SCALE (B/C, ~140): ⌈N/P⌉ blocks of R4 ⟹ ‖Σ_{(N,2N]} eR(phi t n)‖ ≤ 10·N·P^{−ρ}; window-select: j := log N, r₀ := ⌈L/j⌉, β := (r₀+1)/(k+1) (edge-slack form), P := ⌈N^{1−β}⌉, j* := r₀+2 ⟹ hD∧hW1∧hW2 hold, j_cut := 96L^{3/4}(logL)². (hW1: t((P+Y)/N)^{k+1} ≤ N^{−1}, the (1+Y/P)^{k+1} ≤ 2 degradation derivable from hD since √P ≫ k.)
R6 VK-GROWTH (C, ~300): zeta_growth_pow via zetaApprox/norm_zeta_sub_approx_le (Salt/ExpSum/ZetaApprox.lean:471/:542) at N = ⌈t²⌉. ROUTING BY j-COMPARISON (REPAIR — not by L-threshold): (a) j ≤ j_cut trivial (Θ·j_cut = 0.096); (b) j_cut < j ≤ L/10: R5 + Abel σ-shift via norm_sum_smul_antitone_le (Salt/SW/DHTrunc.lean:301); (c) j > L/10: landed zeta_block_bound (ZetaBlock.lean:367) / zeta_block_window(+meet,three) (Window.lean:53/201/218) / zeta_block_kusmin (ZetaGrowth.lean:278) tiles; R10 seam. Trivial-only regime ends ~1.1e20 (judge-verified); scales j∈(j_cut,2L] route to (c) there. VK fires for L > ~1.5e26 (judge-verified), required for ∀t. CONSTANT HYGIENE (REPAIR): branch-(c) tiles are '∃ C, 1 ≤ C'-form ⟹ K, t₀ EXISTENTIAL (finite k ≤ 12 range, max of constants); design values K=30, t₀=1e8 are comments. Approx err t·N^{−σ} ≤ 2e^{−L(1−2Θ)}, pole O(1).
R7 VK-LANDAU-SCALED (B/C, ~180): entire_norm_logDeriv_sub_sum_scaled BY AFFINE SCALING of entire_norm_logDeriv_sub_sum' (Salt/SW/ZetaPartialFractions.lean:171), G := F∘(c + λ·), λ ∈ (0,1]: cost (120/λ)·log(4M₀). ∃-conjuncts (:175-183) read IN FULL by both refuters: all c-relative, transfer under precomposition — pre-read risk RETIRED; keep as impl sanity check only.
R8 VK-ZETA-DISC (B/C, ~200): disc at c = 1+Θ/2+iγ, λ = 6Θ/7 (sphere 3Θ/2 dips exactly to 1−Θ); F := Zc/(c−1) (Zc at ZetaPartialFractions.lean:45). Center floor via |1/ζ| ≤ ζ(σ) ≤ 1+1/(σ−1) — [G] σ-side upper bound LANDED: zeta_real_upper (Salt/SW/ZetaLowerShallow.lean:57); only the Euler-product lower step needs mathlib audit (riemannZeta_eulerProduct; Moebius fallback +80). Pull zero in via mem_zeros_of_factorization_gen (Salt/SW/ZetaZeroFree.lean:56); wrappers off neg_logDeriv_zeta_split (ZetaPartialFractions.lean:98) + neg_re_logDeriv_le (Salt/SW/BCBound.lean:399 — REPAIRED loc). log(4M₀') ≤ 7logL for L ≥ L₀(K) (L₀ existential per R6). [G] NEG-GAMMA SHIM: growth is t ≥ t₀ > 0 but zeros have either Im sign — one conjugation-transport helper via mathlib riemannZeta_conj.
R9 VK-341 (B/C, ~220): assembly at Lq := L^{3/4}(logL)³: three_four_one_logDeriv (Salt/SW/ThreeFourOne.lean:180) + neg_logDeriv_zeta_le (ZetaPole.lean:189) + zero_free_extraction (Salt/SW/ZeroFree.lean:142, generic Lq) with C_chain := 5e6, dd := 1e-7 (C·dd = 1/2 EXACT) ⟹ 1−β ≥ dd/(7Lq). Conversion deriv-LSeries→ζ via LFunction_modOne_eq pattern (ZetaZeroFree.lean:273-283); term_re_nonneg / neg_logDeriv_LSeries_eq (ZeroFree.lean:129/:32). Ball: Θ/2 + dd/(7Lq) ≤ 0.986Θ. T₀ gate absorbs |γ|≤1 strip.
R10 VK-STRIP-PATCH (B, ~150): t ∈ [N, 27πN] (≤7 blocks) via vdC_second_derivative (Salt/ExpSum/VdCorput2.lean:140 — REPAIRED loc) / vdC_2nd_ZR (Salt/ExpSum/DerivTest.lean:63 — REPAIRED loc): N^{−1/2}-grade saving ≫ Θ. [G] the vdC2 engine is in eK character: consume via the eR_eq_eK switch (DerivTest.lean:43 pattern, as inside zeta_block_kusmin).

TRAP k^{24k²r} RESOLVED: enters only via hD P-floor (log_P(D) ≤ 1/8), not a saving-eater; 3.8× margin at j_cut, asymptote 4.

ANCHORS (judge-recomputed): A1 t=1e8: all ~53 scales trivial, Σ ≤ 54.2. A2 t=1e30: trivial-only; REGION live: Lq=1820 (REPAIRED), σ−1=5.5e-11 ≤ 0.486Θ, width dd/(7Lq)=7.85e-12 (REPAIRED; < landed 1.9e-7 here — gate consumes the SHAPE θ=3/4, crossover L~1e37). A3 t=e^{1e27}: k=5623414, r=1.83e8, ρ=6.09e-17, VK j-range [6.6e25, 1e26] nonempty, all W-hyps hold with e^{1e25}-grade margins, ρ·logP beats 2Θj by 4.1e9.

VERIFY-POSTURE [G]: commit the refuter as scripts/vk_minpow_check.py (currently scratchpad-only) in the first Vk commit, updated for W2b=1/6 and hW1 radius P+Y.

ORDER: R1,R2,R7,R10 independent starts; R3←R2; R4←R1,R3+vmvt; R5←R4; R6←R5,R10; R8←R6,R7; R9←R8. Design stones R3/R4 FIRST among C-rungs so a stall surfaces early. Zeno partials: R3 (first vmvt consumer), R7 (serves LITT-LANDAU), R10 (LITT-COVER stone-3) independently valuable.

RESIDUALS consumed: LITT-LANDAU (R7), LITT-COVER stone-3 (R10); none left blocking.
