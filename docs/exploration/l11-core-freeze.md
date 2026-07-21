# L11-CORE freeze — the Perron rep of the pairwise prime sum + LEFT shift

*Maestro design block, 2026-07-21 morning council (JYH nod). Status:
DESIGNED, awaiting refuter pass. Source: MR 1501.04585v4.pdf pp.17–18 (Lemma
11's proof, READ DIRECTLY this session — the sketch below is transcription,
not memory). Target: close `halasz_primes_pow` (S8 [P3]/L11) at the frozen
header shape of `Salt/MR/HalaszPrimes.lean` (BINDING). The four sub-stones
(primes_dual_iff, zeta_near_strip_growth, prime_contour_decay,
primePoly_wellspaced_l2) are LANDED; this freeze is the R1-core.*

## MR'S ACTUAL PROOF (p.17–18, the load-bearing devices)

After duality (landed `primes_dual_iff`), MR bound the **log-weighted** dual
`Σ_{P≤p≤2P} log p·|Σ_t η_t p^{it}|²`, open the square, and dominate the
prime window by a smooth cutoff f (=1 on [1,2], compact support), extended
over ALL prime powers:
`≤ Σ_{t,t'} |η_t η_{t'}|·|Σ_{p^k} log p·p^{ki(t-t')}·f(p^k/P)|`.
Then per pair, u := t−t' (well-spaced ⟹ |u| ≥ 1 off-diagonal):

- **(15)** `Σ_n Λ(n) n^{iu} f(n/P) = −(1/2πi)∫_{(2)} f̃(s)·(ζ'/ζ)(s−iu)·P^s ds`
  (f̃ = Mellin transform; rapid decay f̃(x+iy) ≪_{A,B} (1+|y|)^{-B}).
- Truncate at |Im s| = T (negligible by kernel decay), **shift left** to
  σ = 1 − c/(log T)^{2/3+ε} staying in the zero-free region, crossing the
  SINGLE pole of ζ'/ζ(s−iu) at s = 1+iu (residue term f̃(1+iu)·P^{1+iu}/(1+iu)).
- Price the shifted line by **Ivić (1.52)**:
  `ζ'/ζ(σ+it) = Σ_{|t−γ|<1} 1/(σ+it−ρ) + O(log(|t|+2)) ≪ (log T)^{1+2/3+ε}`
  (O(log T) local zeros, each ≫ (log T)^{-2/3-ε} from the contour).
- Result per pair: `f̃(1+iu)·P^{1+iu}/(1+iu) + O(P·exp(−log P/(log T)^{2/3+ε})·(log T)²)`.
- Sum over pairs with |η_t η_{t'}| ≤ |η_t|²+|η_{t'}|²: the POLE ROW sums to
  O(P)·Σ|η|² because `Σ_{t∈𝒯} |f̃(1−i(t−t'))| = O(1)` (rapid decay ×
  well-spacing); the error row gives |𝒯|·P·exp(·)·(log T)²·Σ|η|². Divide by
  log p ≥ log P.

## THE TWO HOUSE RULINGS (statement layer — surfaced at council 2026-07-21)

1. **The coefficient-1 exp NEEDS NO AMENDMENT.** Landed region
   (`zeta_zero_free_region_pow`, Vk/GrowthPow.lean:1044): zeros with
   |γ| ≥ T₀ have β ≤ 1 − c/((log|γ|)^{3/4}·**(loglog|γ|)³**). The frozen
   decay's **(loglog T)⁴** is one full loglog power WEAKER — the ε-slack
   slot, exactly MR's (log T)^{2/3+ε} device at θ=3/4. Contour at depth
   (c/2)/D₃ gives decay exp(−(c/2)·log P/D₃) ≤ exp(−log P/D₄) once
   (c/2)·loglog T ≥ 1, i.e. T ≥ exp(exp(2/c)) — absorbed into the ∃ T₀.
   (Notation: D₃(T) = (log T)^{3/4}(loglog T)³, D₄ = (log T)^{3/4}(loglog T)⁴.)
   Likewise the edge price: local-Landau gives ‖ζ'/ζ‖ ≪ (log T)·D₃-grade on
   the shifted line; ×∫|f̃| = O(1) ⟹ error P·exp(−(c/2)logP/D₃)·(log T)^{7/4}
   ·(loglog)³ ≤ P·exp(−log P/D₄)·(log T)² for T ≥ T₀ ((loglog)³ ≤ (log T)^{1/4}).
   The frozen (log T)² SURVIVES.
2. **AMENDMENT L11-T (RATIFIED by JYH at the council, 2026-07-21 10:33):** the
   corpus kernel is the hat/ramp kernel (quadratic Mellin decay), not MR's
   C^∞ f (super-polynomial decay). The truncation tail is then honest
   P·log P/T-grade, negligible against the frozen RHS only under a largeness
   relation. ADD the hypothesis **`P ≤ T^10`** (equivalently any fixed power;
   10 is generous) to `halasz_primes_pow`. Consumption-safe: §8.3 runs at
   P ≤ X, T ≥ X^{5/6}-grade ⟹ P ≤ T^{6/5} ≪ T^10. With P ≤ T^10:
   tail ≪ P·log P/T = P·exp(−log T + loglog P) ≪ P·exp(−log P/D₄(T))·(log T)²
   since log P/D₄ ≤ 10·log T/D₄(T) = 10(log T)^{1/4}/(loglog T)⁴ ≪ log T. ✓
   The ∃ C c T₀ packaging (house pattern, scope-diff (6)) is NOT an
   amendment — it is the sanctioned existential-constant posture.

## THE STONE LADDER (single writer, `Salt/MR/HalaszPrimesCore.lean`, ~1.6–2.2k ln)

- **W-KER** [B/C, 250] `primeWindow_kernel`: the two-sided ramp window w from
  two `hatK` instances (plateau ⊇ [P, 2P], support ⊆ [P/2, 3P], 0 ≤ w ≤ 1),
  with its EXACT contour representation from `hat_contour_rep` (two
  applications, linearity) — the corpus replacement for MR's f. Mellin kernel
  = difference of hat kernels; decay quadratic in Im s (kernel-decay remark,
  montgomery3.txt:3530 pattern, already consumed by PerronTrunc).
- **W-DOM** [B, 150] `window_dominates`: Σ_{P≤p≤2P} log p·|Σ_t η_t p^{it}|²
  ≤ Σ_n Λ(n)·w(n)·|Σ_t η_t n^{it}|²-shaped domination (nonneg termwise;
  Λ(p) = log p; w ≥ 1 on the window) + the k≥2 prime-power discard:
  prime-power count in [P/2, 3P] ≪ √P·log P, contribution
  |𝒯|·√P·(log P)-grade·Σ|η|², absorbed: √P·log P ≤ P·exp(−log P/D₄)·(log T)²
  for T ≥ T₀ (D₄ ≥ 3 suffices — corner ledger).
- **REP** [C, 300] `lambda_window_rep`: the per-u representation —
  `Σ_n Λ(n) n^{iu} w(n) = (1/2πi)∫_{Re s = c} (−ζ'/ζ)(s−iu)·W(s) ds`, c = 1 + 1/log P,
  W = the window's Mellin kernel; via `neg_logDeriv_LSeries_eq_LSeries_twist`
  (SW) + hat_contour_rep's integrability apparatus. (The twist n^{iu}
  re-indexes the series: LSeries Λ at s−iu.)
- **TRUNC** [C, 250] `rep_truncated`: cut at |Im s| = T' := 5T; tail ≤
  c'·P·log P/T-grade via the quadratic kernel decay + ‖ζ'/ζ(c+·)‖ ≤
  1/(c−1)-grade = log P-grade on the c-line. (This stone consumes Amendment
  L11-T's headroom; carries the honest tail in-statement.)
- **ZFREE-RECT** [B/C, 300] `rect_zero_free`: the closed rectangle
  [σ₀, c]×[−T', T'] SHIFTED by iu is ζ-zero-free, σ₀ := 1 − (c_vk/2)/D₃(5T):
  heights |Im| ≥ T₀^pow by the region (monotone D₃ at the max height 5T —
  `vkTheta_anti` pattern); heights |Im| ≤ T₀^pow by the COMPACTNESS stone:
  ζ ≠ 0 on the compact segment {Re = 1}×[−T₀^pow, T₀^pow] (pole at 1 exempt:
  (s−1)ζ(s) nonvanishing there) ⟹ ∃ δ₀ > 0 zero-free margin
  [1−δ₀, 1]×[−T₀^pow, T₀^pow] (continuity/isolated-zeros; mathlib
  analyticity of ζ); then T ≥ T₁ ⟹ (c_vk/2)/D₃(5T) ≤ δ₀. ∃-packaged.
- **EDGE** [C, 400] `shifted_edge_price`: on the left edge + horizontals,
  ‖ζ'/ζ(s−iu)‖ ≤ C_E·(log(5T))·D₃(5T)/c_vk + C₀ — the LEFT-strip Landau
  bound: rides `near_norm_logDeriv_Zc_le` (ZetaPowLower:301 disc core) with
  hdist = (c_vk/2)/D₃(5T) from ZFREE-RECT, on discs centered on the shifted
  spine (the :641 hdist-construction TEMPLATE, re-run at the left spine);
  moderate heights by the compact max-bound C₀ (∃); the pole vicinity
  |s−iu−1| ≥ (c_vk/2)/D₃ priced 1/dist-grade (same D₃-budget). The
  (log·D₃)-grade TOTAL is the (log T)²-budget's input (ruling 1).
- **RES** [B/C, 200] `pole_residue_term`: the rectangle identity with the one
  interior pole s = 1+iu (residue of −ζ'/ζ = +1): PerronTrunc's finite-
  rectangle + residue pattern (perron_trunc's 2πi·indicator device);
  main term = W(1+iu), with ‖W(1+iu)‖ ≪ P/(1+|u|²)-grade (quadratic kernel
  decay — this replaces MR's f̃(1+iu)/(1+iu), and the EXTRA decay only helps).
- **POLE-ROW** [B/C, 200] `pole_row_sum`: Σ_{t∈𝒯} ‖W(1+i(t−t'))‖ ≤ c_W·P
  per fixed t' (well-spacing: the j-th nearest neighbor at distance ≥ j ⟹
  Σ_j P/(1+j²) — the SAME summation shape as `wellspaced_l2`'s spacing
  arithmetic). Gives the diagonal-grade P·Σ|η|² pole contribution.
- **ASM** [C, 400] `halasz_primes_pow`: assemble — per-pair estimate
  (RES + TRUNC + EDGE ∘ ZFREE-RECT decay: P^{σ₀} = P·exp(−(c_vk/2)·log P/D₃(5T)));
  |η_t η_{t'}| ≤ |η_t|²+|η_{t'}|²; POLE-ROW for the P-term; the error row
  ×|𝒯|; the D₃(5T)→D₄(T) absorption (ruling 1: log 5T ≤ 2 log T, constants
  into ∃C); divide by log P (log p ≥ log P on the window); close the frozen
  header shape + `P ≤ T^10` (Amendment L11-T) + ∃ C c T₀ packaging.

## CORNER LEDGER (worst-corner incl. asymptotic — #253)

- **u = 0 (diagonal):** never enters the pairwise machinery — the diagonal
  is the landed `primePoly_wellspaced_l2`/window-count side; the off-diagonal
  route only consumes |u| ≥ 1 (well-spacing). The ASM stone must split
  diagonal/off-diagonal BEFORE invoking REP. ✓
- **|u| large (up to 2T):** heights in the shifted rectangle reach 5T =
  T' + 2T at worst; every D₃-evaluation in the freeze is at 5T with
  monotonicity (`vkTheta_anti` pattern) — NEVER at |u| or T alone (the #253
  conflation corner: an executor evaluating the region at height T while u
  pushes the argument to 3T is a BUG the freeze forbids by construction).
- **T moderate (T < T₁ from ZFREE-RECT):** absorbed by the ∃ T₀ in the
  frozen statement (T₀ := max(T₁, exp(exp(2/c_vk)), the (loglog)³≤(logT)^{1/4}
  threshold, the √P-absorption threshold)). The freeze's T₀ is the MAX of
  four named thresholds — the executor lists all four in the docstring.
- **P small (P < 100, say):** the window may hold O(1) primes;
  √P-absorption needs D₄(T₀) ≥ 3 ✓ and the ≪-constant absorbs; the frozen
  statement's `2 ≤ P` side condition suffices (verify at ASM).
- **P ≫ T^10:** EXCLUDED by Amendment L11-T (the truncation tail would
  genuinely leak — this is the honest boundary, not a technical cowardice;
  MR's C^∞ kernel is the alternative price, a D-tier analytic build).
- **the c-line (Re = 1 + 1/log P) integrability:** ζ'/ζ bounded by
  1/(c−1) = log P-grade there; the kernel is L¹ on the line (quadratic
  decay) — REP's integral converges absolutely. ✓

## INVENTORY (verified present this session)

`zeta_zero_free_region_pow` Vk/GrowthPow.lean:1044 ((loglog)³ — the slack
source); `vkTheta`/`vkTheta_anti` Vk/PowRegion.lean:35/40;
`near_norm_logDeriv_Zc_le` MR/ZetaPowLower.lean:301 (disc core, hdist
hypothesis) + the :641 hdist-construction template + `zeta_near_logDeriv_bound`
:779 (RIGHT strip — the pattern, NOT the tool: L11-CORE needs the LEFT spine);
`perron_trunc` MR/PerronTrunc.lean:389 (rectangle+residue pattern);
`hat_contour_rep` (HalaszKernel, K2'); `neg_logDeriv_LSeries_eq_LSeries_twist`
(SW); `primes_dual_iff`/`zeta_near_strip_growth`/`prime_contour_decay_frozen`/
`primePoly_wellspaced_l2` MR/HalaszPrimes.lean (landed L11 stones);
`wellspaced_l2` MR/LargeValues.lean (spacing arithmetic pattern for POLE-ROW).

## TRAPS

The ℂ-module-diamond convert trap (rewrite-the-value); implicit-μ metavar
(annotate volume); maxHeartbeats-needs-comment; log-of-arithmetic linarith
law; goal-changing show→change; copy-summands-verbatim; binder-ascription
retype; interval vs Finset boundary conventions (MR's closed-≤ vs half-open —
the RAMARE-DPOLY catch, pilot 2026-07-20).

## EXECUTOR BOILERPLATE

Model: opus MANDATORY. You write ONLY Salt/MR/HalaszPrimesCore.lean. NO-GIT
(#244). The `halasz_primes_pow` conclusion shape = HalaszPrimes.lean header
+ Amendment L11-T's `P ≤ T^10` + ∃ C c T₀ packaging — FROZEN (iron rule 1).
Helpers yours; harder-than-C helper → STOP, flags.md. 3 attempts per stone →
flags → next. Gate: lake build + #print axioms ⊆ [propext, Classical.choice,
Quot.sound]. Growing quantities in-statement (#253). Zeno partials = success.

## REFUTER QUESTIONS (kill-checks)

R-1: The pole-row device — does the QUADRATIC kernel decay really give
Σ_t ‖W(1+i(t−t'))‖ ≪ P uniformly (check the nearest-neighbor count at
well-spacing exactly 1, and W's actual size at |u| ≤ 1... which never occurs
off-diagonal — verify)? R-2: ZFREE-RECT's compactness stone — is the
mathlib apparatus (ζ analytic off 1, nonvanishing on Re = 1) actually
sufficient for the ∃δ₀ margin, or is there a hidden dependence on zero-
counting near Re = 1 at moderate height? R-3: the D₃(5T) bookkeeping — run
the FULL height budget (T' = 5T; ζ-argument heights ≤ T' + 2T = 7T?? —
CHECK: s ∈ rectangle has |Im s| ≤ 5T, argument s−iu has |Im| ≤ 5T + 2T = 7T
— if 7T, every 5T in this freeze inflates to 7T; verify and repair
consistently — this is a DELIBERATE refuter trap left in: find the correct
uniform height). R-4: the truncation-tail arithmetic under P ≤ T^10 —
re-derive P·logP/T ≤ P·exp(−logP/D₄)(logT)² honestly, all corners (P tiny,
P = T^10 exactly). R-5: EDGE's horizontal edges — the horizontals sweep
σ ∈ [σ₀, c] at heights ±5T; is the Landau/disc-core price valid THERE (the
:641 template is spine-based — do the horizontal discs stay inside the
region)? R-6: the log p vs Λ division direction at ASM (≥ log P needs the
window's LEFT endpoint — P/2-supported ramp mass must NOT enter the
log p ≥ log P step; check W-DOM's discard covers the ramp zones).
