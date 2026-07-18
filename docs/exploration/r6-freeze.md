# R6 FREEZE (survived 0/2, conf 0.85; 2026-07-18 13:30 PT)

## THE FREEZE

# R6 FREEZE — dh_extraction_upper_W via EXACT template reduction (no third convolution)

TARGET (new file Salt/SW/DHExtractW.lean, register in All.lean):
theorem dh_extraction_upper_W {q}[NeZero q] (χ) (hχ:IsPrimitive)(hsq:χ²=1)(hq:2≤q){β₀:ℝ}
 (hzero: LFunction χ β₀ = 0)(hlo:1/2≤β₀)(hhi:β₀<1){Z₀}(hZ: box-bound ‖zetaHol‖≤Z₀)
 {z Y : ℕ}(hz:1≤z)(hY: 2*z^4 ≤ Y) :
 |∑_{n∈Icc 1 Y} dhCoeffW χ (selWeight χ z) n · n^{−β₀} · dhKernR(n/Y)
   − L₁ · selMainTerm χ z · Y^{1−β₀}/((1−β₀)(2−β₀))|
 ≤ C₂ · z · (1+log(z²))⁹ · Y^{1/2−β₀},
 C₂ := 4·C_w = 136+48M+48M·Z₀+144M/(1−β₀), M=√q(1+log q), L₁=(LFunction χ 1).re.
Plus ≤-corollary (drop abs) for R7; selberg_opt_eq rewrites selMainTerm=1/H(z) downstream.

THE WALL-BREAKER (kills both prongs): the (†) bijection (dhA_mul_eq_sum) composed with
the Möbius coprimality unfold reduces the per-m inner sum EXACTLY (identity, no estimate)
to the LANDED m=1 template at rescaled real scales:
  Σ_{n≤Y,m∣n} dhA(n)n^{−β₀}(1−n/Y) = Σ_{g∣m}Σ_{k∣m/g} χℝ(g)χℝ(k)μ(k)·(mk)^{−β₀}·D₀(Y/(mk)),
  D₀(x) := Σ_{s≤⌊x⌋} dhA(s)s^{−β₀}(1−s/x).
(a) no third convolution ever materializes — only the 2-fold χℝ∗1 template at 3^{ω(m)}
scales; (b) sign cancellation preserved — the signed gcW collection is applied to the
EXACT main terms (identity), triangle inequality ONLY on the residual.

MAIN-TERM DIAGONALIZATION (numerically certified 1.8e-16, off-diagonal battery, q=3):
per-m main = L₁Y^{1−β₀}/((1−β₀)(2−β₀))·(1/m)Σ_{g,k}χℝ(gk)μ(k)/k, and for sf m
  Σ_{g∣m}χℝ(g)Σ_{k∣m/g}μ(k)χℝ(k)/k = selHmul χ m  (F=χ∗(μχ/id) mult., F(p)=1+χ(p)−χ(p)/p=selH p),
so per-m factor = selHmul(m)/m = selNu χ m — EXACTLY the ν the selMainTerm form wants:
  Σ_{m≤Y} gcW(selWeight χ z) m · selNu χ m = selMainTerm χ z  (=1/H(z) by selberg_opt_eq),
valid since gcW supported on sf m=lcm(d,e)≤z²≤Y. Certified EXACT at z∈{6,10,20}, q=3.

RUNGS (8, no D-class, ~970 ln):
R6-1 [B ~60] kernel_abel_sum_real + rpow_sub_le_tangent_upper: real-scale kernel-Abel
 D₀(x)=(1/x)[Σ_{t≤T−1}A(t)+(x−T)A(T)], T=⌊x⌋ (from sum_mul_index_eq); MVT upper tangent
 x^c−(x−1)^c ≤ c·x^{c−1}, c∈[1,2] (mirror of rpow_sub_le_tangent, catch #168 route).
R6-2 [B ~110] dhAbel_inner_abs_le: TWO-SIDED |A(t)−L₁t^{1−β₀}/(1−β₀)| ≤ C_w·t^{1/2−β₀} —
 re-assembly of DHCore hLeg1/hLeg2/hCorner (all already abs-form haves); SAME C_w.
R6-3 [C ~150] unmoll_extraction_abs_real: real x≥2:
 |D₀(x) − L₁x^{1−β₀}/((1−β₀)(2−β₀))| ≤ C₂x^{1/2−β₀}. Honest anatomy 3C_w+7M/u
 (2C_w cap-leg + C_w boundary + 7M/u Riemann sandwich via R6-1; L₁≤1+6M≤7M from strip@1,r=1);
 C₂=4C_w covers with slack. Uses sum_rpow_neg_le, sum_rpow_le_integral.
R6-4 [C ~150] dhA_kernel_reduction: THE EXACT REDUCTION (boxed identity above), stated on
 (Icc 1 Y).filter(m∣·) to match the regroup. Route: n=mt reindex + (†)dhA_mul_eq_sum +
 coprime Möbius unfold (inner_coprime_eq mechanism) + t=ks reindex (sum_dvd_reindex) +
 Nat.div_div_eq_div_mul + chiRe_mul. CERTIFIED 1.4e-16 (m≤30, Y=500, β₀=0.7).
R6-5 [C ~120] selHmul_collection: sf m: Σ_{g∣m}χℝ(g)Σ_{k∣m/g}μ(k)χℝ(k)/k = selHmul χ m.
 Route: (g,k)↦(a=gk,k) sigma reindex (selCore_collapse idiom) + χ(g)χ(k)=χ(a) +
 DIVPROD (sum_divisors_prod_primeFactors) at f(p)=−1/p giving Σ_{k∣a}μ(k)/k=∏(1−1/p),
 then DIVPROD at f(p)=χℝ(p)(1−1/p): ∏(1+χ(p)−χ(p)/p)=selHmul. CERTIFIED 1.8e-16.
R6-6 [B ~100] support+moment: selWeight sf-z-supported [A, if-guard]; gcW_selWeight_
 eq_zero_of_gt_sq (z²<m→0, lcm≤de≤z²); abs_gcW_le_pow3 (|λ|≤1 sf-supported ⟹ |gcW λ m|≤3^ω,
 mirror abs_grahamGc_le, pair count=3^ω certified); sum_abs_gcW_pow3_div_sqrt_le:
 Σ_{m≤Y}|gcW|3^ω m^{−1/2} ≤ z(1+log z²)⁹ via m^{−1/2}≤z/m on m≤z² + tau6W_le k=9.
R6-7 [B ~100] sum_gcW_selNu_eq_selMainTerm (z²≤Y): gcW_eq unfold + per-(d,e) collapse at
 m=lcm(d,e) (sum_ite_eq', dhWeightSqW_eq_sum_gcW mechanism reversed). CERTIFIED (=1/H).
R6-8 [C ~180] assembly: dhExtractionW_regroup (f=n^{−β₀}dhKernR(n/Y); kernel exact on range
 via dhKernR_eq) → R6-4 per m → R6-3 at x=Y/(mk) (guard: mk≤m²≤z⁴, 2z⁴≤Y ⟹ x≥2) →
 (mk)^{−β₀}(Y/(mk))^{1−β₀}=Y^{1−β₀}/(mk) → R6-5 ⟹ per-m main = selNu(m)·L₁Y^{1−β₀}/(u(2−β₀))
 → R6-7 collects SIGNED main EXACTLY → triangle on residual ONLY:
 Σ_m|gcW|Σ_{g,k}(mk)^{−β₀}C₂(Y/(mk))^{1/2−β₀} = C₂Y^{1/2−β₀}Σ_m|gcW|Σ_{g,k}(mk)^{−1/2}
 ≤ C₂Y^{1/2−β₀}Σ_m|gcW|3^ω m^{−1/2} ≤ C₂·z·(1+log z²)⁹·Y^{1/2−β₀} (R6-6).

FULL ERROR CHAIN, constants: template C₂=4C_w=136+48M+48MZ₀+144M/(1−β₀) [the ONE u⁻¹ dust];
collection factor z(1+log z²)⁹ [u-content: z=Q¹²u⁻² ⟹ total u⁻³ vs budget's z⁴(1+1/u)=u⁻⁹];
amped into the master as 2x^{β₀−σ}E(β₀): q=3 corner 10^{−11.12} ≤ 1/8 (10.2 orders, BEATS
the ledger's budgeted −8.86); q=10⁶: 10^{−188.9} ≤ 1/8 (188 orders; looser than the budgeted
shape −270 but the binding test is vs 1/8). Guard 2z⁴≤x structural for all q (104lnQ+11ln(1/u)
vs ln2+48lnQ+8ln(1/u)). VERDICT: CLOSES at frozen z=Q¹²u⁻²; no z-retune, no smoothed cutoff.
Numeric certs: scratchpad r6_verify.py (this session), sections (a)-(e) all pass.

## Smallest-index ledger

- m=1,g=k=1 (SMALLEST index, priced FIRST): |gcW(1)|=selWeight(z,1)²=1; term = full template error C₂Y^{1/2−β₀}; amped 2C₂x^{1/2−σ}: q=3 → 10^{−41.0}, q=10⁶ → 10^{−293}; share of collected bound 10^{−30.0} / 10^{−104.4}
- TOTAL collected error amped (headline): q=3 → 10^{−11.12} vs 1/8=10^{−0.90} — margin 10.2 orders, BEATS ledger's budgeted E(β₀)-amp −8.86 by 2.3; q=10⁶ → 10^{−188.9} vs 1/8 — margin 188 orders (mine looser than the budgeted shape −270 there; binding test is 1/8, passes)
- Deepest scale, LARGEST index mk=z⁴ (m=z², k=m): x₀ = Y/z⁴; template guard x₀ ≥ 2 from hY: q=3 x₀=10^{50.1}, q=10⁶ x₀=10^{361.3}; structural for all q
- Real-scale wrapper + Riemann-sandwich dust at deepest scale: (L₁/u)x₀^{−β₀} vs C₂x₀^{1/2−β₀} = 10^{−26.4} (q=3), 10^{−182} (q=10⁶) — absorbed in C₂'s +7M/u
- u⁻¹ census: exactly ONE u⁻¹ in C₂ (144M/(1−β₀), honest 115M/u); z-factor carries u⁻² inside z=Q¹²u⁻²; total error grade u⁻³ ≤ budget's z⁴(1+1/u) = u⁻⁹ grade
- β₀=1/2 corner (no-decay index): Y^{1/2−β₀}=1; statement holds verbatim; master folding at β₀<σ is R8's existing trivial-split branch (unchanged from landed R2 posture)
- Moment floor m=1: |gcW(1)|·3⁰·1 = 1 ≤ z(1+log z²)⁹; small-z sanity z=6: S=19.6 ≤ 5.36e6 (r6_verify.py (e))
- k^{−1/2}≤1 crudeness at k=m=z²: loses factor √k ≤ z — absorbed inside the 10.2-order margin
- Kernel seam: (1−n/Y)₊ = 1−n/Y exact on n≤Y (dhKernR_eq) — zero cost at every index

## THE BINDING REPAIRS (frame refuter, fold ALL in)

- R6-2: do NOT cite 'hLeg2/hCorner' — they are proof-local haves inside dhAbel_inner_le (DHCore.lean:608, :638), not exported lemmas. Copy the two blocks (~55 ln) into the new two-sided proof; every ingredient they use is exported (chiRe_partial_at_zero_le, term_rpow_le, sqrt_pow_bound, natSqrt_mul_rpow_le, sum_rpow_neg_le). The freeze wording 'already abs-form haves' is accurate about form but an executor reading it as citable will stall
- R6-6: consume the LANDED abs_gcW_le (SelWeight.lean:171, exact statement |gcW lam m| <= 3^omega(m) for sf-supported |lam|<=1) instead of re-proving the planned abs_gcW_le_pow3; hypotheses discharge via selweight_abs_le_one (SelOpt.lean:536) and the selWeight if-guard (SelWeight.lean:341). Strike that helper from the new_helpers list
- R6-4: add the one un-landed micro-lemma explicitly to the rung plan — either the divisor-level coprime Moebius unfold Sum_{d|t,(d,kappa)=1} chiRe d = Sum_{k|kappa, k|t} mu(k) chiRe(k) dhA(t/k) (mechanism: hset/hpt from CoprimeBV.lean:103-119 + the k*e divisor reindex), or the swap-first route (generalize inner_cop_swap DHBal2.lean:167 to a t-dependent weight, then apply the Icc-level sum_coprime_eq_moebius_multiples CoprimeBV.lean:98 which is generic in F). Fits the C ~150 budget either way
- R6-4 statement: state the reduction for ALL m>=1, not sf-only — my extended battery certifies it off-squarefree (m=4..45, three beta0 values, ragged Y, <=9e-16), and (dagger) dhA_mul_eq_sum needs no squarefree hypothesis; an sf side-condition would only complicate the R6-8 splice against dhExtractionW_regroup's unrestricted m in Icc 1 Y
- R6-1/R6-3: thread Nat.floor_div_nat (real-floor of nat quotient = nat division) for the D0(Y/(mk)) <-> Icc 1 (Y/(m*k)) bridge; state D0 at real x with T = Nat.floor x so the R6-8 splice needs no side bridge
- New file Salt/SW/DHExtractW.lean: import Salt.SW.SelOpt explicitly (catch #178 — not transitively available), plus DHClose2, DHBal2, DHExtract, DHRepulsion, Sharp; register in All.lean with the #audit_axioms gate
- Risk-list cleanup: the tau6W k=9 fallback is unnecessary — tau6W_le (Sharp.lean:248) is generic in k and tau6W (:156) is exactly the sf-filtered Sum k^omega/d shape; k=9 applies directly at L=z^2 giving (1+log z^2)^9 with no friction and no (1+2lnz)^3 loss
