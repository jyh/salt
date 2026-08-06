# ONE-WALL-SCOUT — morning-design dossier

Read-only pass, salt @ `main` (`fb44672`). Every claim below is file:line. Numerics recomputed from the corpus's own literals; discrepancies with the 8/5 flags are flagged loudly.

---

## 0. HEADLINE (three findings that re-price tomorrow's block)

**F1 — Mask (b) is not a wall at all. It is already covered by a landed theorem.**
`Salt/SW/ZetaLowerShallow.lean:323` `zeta_lower_shallow` carries **no upper bound on σ and no upper bound on |t|** — only `2 ≤ |t|` and `1 − c₄/log(|t|+2)⁹ ≤ σ`. `Salt/MR/ZetaLowerAllT.lean:44`'s compact-min box is `Re ∈ [1,2]`, `3 ≤ |t| ≤ T₁` — every point satisfies both hypotheses. `ε₀ := c/log(T₁+2)⁷` discharges it outright. **~15 lines, class A/B, zero new analysis.** The 3-4-1 route's `2 ≤ |t|` gate — which is exactly why it cannot serve mask (a) — is *satisfied* on mask (b). The two masks were mis-fused.

**F2 — `zeta_pow_lower_far`'s `2 ≤ |t|` is a false gate.**
`Salt/MR/ZetaPowLower.lean:198` `zeta_horiz_lower` uses `ht : 2 ≤ |t|` at **exactly one place** — inside `hzne1`, to derive `(v:ℂ)+(t:ℂ)*I ≠ 1`, i.e. it only needs `t ≠ 0` (the closing tactic is `rw [him] at ht; norm_num at ht` with `him : t = 0`). `zeta_pow_lower_far` (`:247`) uses `ht` only to call `zeta_horiz_lower`. **So `d'/32 ≤ ‖ζ((1+d')+it)‖` holds for every `t ≠ 0`** — the argument is pure Dirichlet series (`zeta_dirichlet_re_le` `:104`, valid for `u > 1`, any `t`) plus the `Re = 2` anchor plus the real-axis pole bound. Nothing in it knows about height. This is a free ~60-line generalisation and it **cuts the shared stone's constant by 715 nats** (see §3).

**F3 — the flags' `δ₀ ~ e^{−14000}` is wrong by a factor ~25 in the exponent.**
The 8/5 ZETA-INV-SHALLOW entry prices "`Σ_ρ ½·log(20/(a−β)²) ≈ 18.7` per zero against a **Jensen zero-count ~757**". But `757 = 120·log(4·M₀ζ(1))` is the *Borel–Carathéodory constant*, not the zero count. The Jensen count is `log(4M₀)/log(7/6) ≈ 41` (`entire_zero_count_le`, `Salt/SW/ZetaPartialFractions.lean:134`, ratio `7/4 : 3/2 = 7/6`) — **smaller by the factor `120·log(7/6) = 18.5`**. Re-run at the old `c₃ = 10⁻⁷`: `log(1/δ₀) ≈ 1522`, not `1.4e4`. Re-run at EPSILON-SHARP's `c₃ = 1/75712` **and** with F2's anchor: **`log(1/δ₀) ≈ 485`**. The route is an order of magnitude cheaper than banked.

---

## 1. THE MASK SITES AT THE BYTES

### (a) `Zc_patch_lower` — `Salt/SW/ZetaInvShallow.lean:53`

```
lemma Zc_patch_lower {a c₃ : ℝ} (ha : 1/2 ≤ a) (ha1 : a ≤ 1) (hc₃ : 0 < c₃)
    (hcompat : 1 - a < c₃ / Real.log 4)
    (Hzfr : ∀ {ρ}, riemannZeta ρ = 0 → 1/2 ≤ ρ.re → ρ.re ≤ 1 - c₃/Real.log (|ρ.im|+2)) :
    ∃ δ > 0, ∀ z : ℂ, a ≤ z.re → z.re ≤ 3 → |z.im| ≤ 2 → δ ≤ ‖Zc z‖
```
Discharge: `R` closed (`:65`) ∩ `closedBall 0 5` (`:70`) ⇒ compact (`:77`); `Zc ≠ 0` on `R` (`:85`, via `riemannZeta_ne_zero_of_one_le_re` above the line and `Hzfr` below); **`hRcompact.exists_isMinOn` at `:105`** — the leaf. `δ := ‖Zc z₀‖`, opaque.

Single Lean call site: `zeta_inv_shallow` `:151`, where `δ` sits under division in `C := max (1/c) (max (4/(δ·log2⁷)) (4/log2⁷))` (`:154`).

**§5 of `Salt/SW/EpsilonZero.lean` (8/5) already abolished two thirds:**
- `Zc_lower_near_pole` `:366` — `1/2 ≤ Re z ∧ ‖z−1‖ ≤ 1/5 ⇒ ‖Zc z‖ ≥ 7/25`;
- `Zc_lower_of_two_le_re` `:394` — `Re z ≥ 2 ⇒ ‖Zc z‖ ≥ 1/4`;
- `Zc_patch_lower_of_band` `:414` / `Zc_patch_lower_bounded_of_band` `:429` — hypothesis-taking twins, floor `min δ₁ (1/4)` on the whole rectangle given the band input
  ```
  hband : ∀ z, a ≤ z.re → z.re ≤ 2 → |z.im| ≤ 2 → 1/5 ≤ ‖z-1‖ → δ₁ ≤ ‖Zc z‖
  ```
  Note: **no `Hzfr`, no `hcompat`** — the twin is `c₃`-independent. This is the exact socket the new stone plugs into.

**What the residual band actually needs.** Box `{a ≤ Re ≤ 2, |Im| ≤ 2, ‖z−1‖ ≥ 1/5}`. Grade: any `δ₁ > 0` explicit. Height range: `|t₀| ≤ 2`. The width sliver `1 − a`: derived *inside* `zeta_inv_shallow` at `:127`/`:137` as
`c₄ := min c₄₀ (min (log2⁹/2) (c₃·log2⁹/(2·log 4)))`, `a := 1 − c₄/log2⁹`, so `1 − a ≤ c₃/(2 log 4)` **structurally, for any `c₃ > 0`**.
At the corpus's own numbers the `min` is won by `c₄₀ = b⁴ = 77760⁻⁴` from `zeta_lower_shallow` (b = 1/(8·36·270)), giving **`1 − a ≈ 7.4e−19`** — three orders *below* the `c₃` arm's `4.76e−6`. Design consequence: state the stone parametrically in `η := 1 − a` and quote both.

### (b) `zeta_lower_compact_mid` — `Salt/MR/ZetaLowerAllT.lean:44`

```
theorem zeta_lower_compact_mid {T₁} (hT₁ : 3 ≤ T₁) :
    ∃ ε₀ > 0, ∀ d' t, 0 ≤ d' → d' ≤ 1 → 3 ≤ |t| → |t| ≤ T₁ →
      ε₀ ≤ ‖riemannZeta ((1+d' : ℝ) + t*I)‖
```
Box `B = {Re ∈ [1,2]} × {3 ≤ |Im| ≤ T₁}` (`:47`), closed `:55`, `⊆ closedBall 0 (2+T₁)` `:61`, compact `:68`; nonvanishing from `riemannZeta_ne_zero_of_one_le_re` alone (`:85` — no height threshold, no zero-free region); **`exists_isMinOn` at `:83`**. `ε₀` may depend on `T₁` arbitrarily (docstring `:43`; design-grade `≈ e^{−1251}` per `:184` and `mr-freeze.md:13`).
**→ served by F1.**

### (b′) `zeta_lower_small_t` — `Salt/MR/ZetaLowerAllT.lean:103` — THE FOURTH MASK

```
theorem zeta_lower_small_t :
    ∃ δ > 0, ∀ d' t, 0 ≤ d' → d' ≤ 1 → |t| ≤ 3 → ¬(d' = 0 ∧ t = 0) →
      δ ≤ ‖riemannZeta ((1+d' : ℝ) + t*I)‖
```
Same genre: `P = {Re ∈ [1,2], |Im| ≤ 3}`, **`exists_isMinOn` on `‖Zc‖` at `:140`**, then `‖ζ‖ ≥ δ/4` off `‖s−1‖ ≤ 4`. The brief names three masks; this is a fourth, and it is **load-bearing outside `ZetaLowerAllT`**: `Salt/MR/SiegelArm.lean:235` consumes it for the S-2b principal-character band floor (`δ/q`, docstring `:53`/`:68`).
Grade needed: any explicit `δ`; box `Re ∈ [1,2]`, `|Im| ≤ 3`; **σ ≥ 1 exactly**, so `η = 0` and the separation is the full `c₃/log(|γ|+2)` — *easier* than mask (a).

### Bonus mask (same box, ceiling side)
`zeta_upper_band` — `Salt/MR/SiegelArm.lean:392`, `exists_isMaxOn` at `:397`, `Z := max ‖Zc z₀‖ 1`. **Free kill**: bandBox `= {Re∈[1,2], |Im|≤1}` sits inside `‖z − 2‖ ≤ √2 ≤ 7/4`, so `Zc_sphere_bound_sharp` (`EpsilonZero.lean:477`) at `t₀ = 0, a = 1, b = 2` gives `‖Zc‖ ≤ 1 + 5·(11/4)·(15/4) = 52.6`, i.e. **`Z = 53`**, ~12 lines.

### Corpus census of the same leaf (for completeness)
| site | what | status |
|---|---|---|
| `SW/ZetaZeroFree.lean:203` | `ε₀` = infDist to zeros on `Re=1`, `|t|≤1` | **abolished** by `zeta_zero_free_strip_sharp` (`EpsilonZero.lean:708`, `2·10⁻⁵`) |
| `SW/ZetaInvShallow.lean:105` | mask (a) | 2/3 abolished; band open |
| `MR/ZetaLowerAllT.lean:83` | mask (b) | **F1** |
| `MR/ZetaLowerAllT.lean:140` | mask (b′) | new stone |
| `MR/SiegelArm.lean:166` | `LFunction_band_lower`, χ≠1 | **genuinely ineffective** (Siegel; `:161` docstring says so) — not this wall |
| `MR/SiegelArm.lean:397` | `zeta_upper_band` | free kill above |
| `MR/HalaszPrimesCore.lean:589` | `zeta_zero_free_strip_height {M}` (`:570`), infDist on `|t| ≤ M` | same genre as `ZetaZeroFree:203`, height-parametric; not yet re-based on the sharp strip |
| `MR/CompactMin.lean:127` | `isCompact_Icc` min, different genre | out of scope |

---

## 2. THE BC / JENSEN MACHINERY — WHAT EXISTS **FOR ζ**

The answer to "does a ζ version of `LFunction_norm_logDeriv_sub_sum'` exist?" is **yes, two of them, and they are the exact tools.**

| lemma | file:line | shape |
|---|---|---|
| `LFunction_norm_logDeriv_sub_sum'` | `SW/MaxModulus.lean:89` | Dirichlet `L`; radius `3/2`, numeric on `‖s−c‖ ≤ 23/20`, `120·log(4M₀)` |
| **`entire_norm_logDeriv_sub_sum'`** | `SW/ZetaPartialFractions.lean:171` | **the ζ one**: arbitrary entire `F`, `‖F c‖ ≥ 1/4`, sphere bounds on `7/4` and `3/2` ⇒ same conclusion. Blaschke max-modulus at radius `8/5` carried over verbatim |
| `entire_norm_logDeriv_sub_sum_scaled` | `Vk/Landau.lean:35` | the `λ`-scaled twin: radii `7λ/4, 3λ/2, 23λ/20`, numeric `(120/λ)·log(4M₀)` |
| `entire_zero_count_le` | `SW/ZetaPartialFractions.lean:134` | Jensen: `∑ᶠ divisor F (closedBall c r) ≤ log(4M)/log(R/r)` |

ζ-side suppliers, all landed and explicit:
- `Zc` entire, `Zc 1 = 1`, `Zc_eq_of_ne`, `Zc_differentiable`; `Zc_eq_series` `:814`; `Zc_growth` `:851`; `norm_R_le` `:524`.
- `Zc_center_lower` `:114` — `‖Zc(2+it₀)‖ ≥ 1/4` (the `hFc` slot, free).
- `zeta_norm_ge` `:108` — `Re s ≥ 2 ⇒ ‖ζ‖ ≥ 1/4`.
- `M0zeta` `:867` `= 1+5(19/4+|t₀|)(15/4+|t₀|)`; `Zc_sphere_bound` `:895` (radius `≤ 7/4`).
- **sharp**: `Zc_sphere_bound_sharp` `EpsilonZero.lean:477`, `Zc_sphere_bound_height_one` `:524` (`≤ 66` at `|t₀|≤1`), `Zc_sphere_bound_height_two` `:535` (`≤ 96` at `|t₀|≤2`) — factor ≈2 off `M0zeta`.
- Assembled ζ consumers already riding this: `zeta_neg_re_logDeriv_le` `ZetaPartialFractions.lean:942`; `zeta_neg_re_logDeriv_le_keep_of_growth` / `_le_of_growth` `EpsilonZero.lean:553/625` (hypothesis-taking, `120·log(4M)` **un-collapsed** — the right genre to imitate); `ShiftTrivChar.lean:208`.

**Segment-integration / transport devices (all landed):**
- `hasDerivAt_log_norm_horiz` — `MR/ChiLLower.lean:87` — `d/dv log‖F(v+c)‖ = Re(logDeriv F)`, `F` arbitrary. (ζ-specialised copy: `MR/ZetaPowLower.lean:144`.)
- **`norm_Zc_lower_of_shallow_ball`** — `MR/ZetaInvShallow.lean:225` — **the template**: Landau ball on `G = Zc/Zc(c)`, zero set forced EMPTY, then `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` transports `log‖Zc‖` horizontally at cost `≤ 1` (`:305`). Everything in the new stone except the non-empty zero set is here already.
- `near_norm_logDeriv_Zc_le` — `MR/ZetaPowLower.lean:301` — **the zero-count block** (`:334–390`): from the exported factorization it recovers `∑_{ρ∈Z} m_ρ ≤ log(4M₀)/log(7/6)` via `analyticOrderAt_eq_of_factorization` + divisor locality + `entire_zero_count_le`. Directly liftable.
- `zeta_near_bridge` — `MR/ZetaPowLower.lean:843` — FTC over a horizontal segment with continuity-of-`logDeriv` integrability, ζ version.
- `norm_logDeriv_le_of_ball_dist` — `SW/ShiftVariants.lean:45` — the L-side distance form.
- Ceilings: `TauExt.lean:121` `zetaHol_norm_le` (`≤ 3+2|Im s|` on `1/2 ≤ Re ≤ 1`), `:152` `zetaHol_bound_tall`, `:162` `zetaHol_bound_five`. **Not usable here** — `zetaHol` is the *completed/regularised* object of the DH lane; the pole patch needs `Zc`, whose ceiling is `Zc_sphere_bound_sharp`. Record as a non-lead.

**The one export gap.** `entire_norm_logDeriv_sub_sum'` returns six conjuncts (`:175–183`) and **the zero count is not among them** — it is computed internally in the L-twin (`MaxModulus.lean:276`) but never exported. The new wave must either widen the export (breaks the `⟨Z,m,h,-,-,-,-,hnum⟩` destructuring at 8 call sites — **don't**) or land a standalone recovery lemma. `near_norm_logDeriv_Zc_le`'s `:334–390` block is exactly that proof; extract it.

---

## 3. THE SHARED STONE

### 3.1 Why the naive route fails and the exact one works

`near_norm_logDeriv_Zc_le` bounds the zero sum *uniformly*: `‖∑ m_ρ/(s−ρ)‖ ≤ (∑m_ρ)/w`. Over a segment of length `ℓ` that costs `ℓ·N/w`. Here `w = σ−β ≈ 3e−6`, `N ≈ 39`, `ℓ ≈ 1` ⇒ `1.3·10⁷`. **Catastrophic.** The stone must integrate each zero term *exactly*:

`∫_σ^{u₁} Re 1/((u+it₀)−ρ) du = ½·log( ((u₁−β)²+g²) / ((σ−β)²+g²) )`, `g = t₀−γ`

which is `≈ log(1/(σ−β)) ≈ 12.7` per unit multiplicity, i.e. `10⁶` times cheaper. **This is the whole content of the new stone.** Everything else is already on disk.

### 3.2 Statement shape (hypothesis-taking, the corpus's `_of_band`/`_of_growth` genre)

```
/-- THE LOW-HEIGHT `Zc` FLOOR. -/
theorem Zc_band_lower_of_sep {η d₀ T M sep δ₀ : ℝ}
    (hT : 0 ≤ T) (hM : 1 ≤ M) (hη : 0 ≤ η)
    (hsphere : ∀ t₀ z, |t₀| ≤ T → ‖z - (2 + t₀*I)‖ ≤ 7/4 → ‖Zc z‖ ≤ M)   -- Zc_sphere_bound_sharp
    (hsep : ∀ ρ, riemannZeta ρ = 0 → 1/2 ≤ ρ.re → |ρ.im| ≤ T + 3/2 →
              ρ.re ≤ 1 - η - sep)                                        -- zeta_zero_free_region_sharp
    (hsep0 : 0 < sep) (hd₀ : 0 < d₀) (hd₀1 : d₀ ≤ 1/2)
    (hδ₀ : Real.log δ₀ ≤ Real.log (d₀/160) - (120*Real.log (4*M))*(d₀+η)
             - (Real.log (4*M)/Real.log (7/6)) * (1/2 * Real.log (((1/2+d₀)^2+9/4)/sep^2))) :
    ∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 1 + d₀ → |z.im| ≤ T → 1/5 ≤ ‖z - 1‖ → δ₀ ≤ ‖Zc z‖
```
plus a numeral instantiation `Zc_band_lower` at `T = 2, η = c₃/(2 log 4), M = 96` and a second at `T = 3, η = 0, M = 133`.

### 3.3 The route (five steps, all templated)

1. **Anchor** at `u₁ := 1 + d₀`, same height `t₀ = z.im`. On the band, `‖z−1‖ ≥ 1/5` and `Re z ≤ 1+d₀ ≤ 3/2` force `|t₀| ≥ √(1/25 − d₀²) ≥ 1/5 − d₀`. **F2's generalised `zeta_pow_lower_far`** (needs only `t₀ ≠ 0`) gives `‖ζ(u₁+it₀)‖ ≥ d₀/32`, hence `‖Zc(u₁+it₀)‖ ≥ (1/5)(d₀/32) = d₀/160`.
   *Without F2 this step must anchor at `Re = 2` with `Zc_center_lower` (`‖Zc‖ ≥ 1/4`) and the segment length jumps from `d₀+η ≈ 1.4e−3` to `1+η`, costing **+715 nats**.*
2. **Landau ball** `entire_norm_logDeriv_sub_sum'` at `F = Zc`, `c = 2+it₀`: `hFc` = `Zc_center_lower`, spheres = `Zc_sphere_bound_sharp`. The whole segment `[1−η, 1+d₀]+it₀` sits in `‖s−c‖ ≤ 1+η < 23/20` ✓ (the geometry closes with room: `1.0000000000000007 < 1.15`).
3. **Count** `∑_{ρ∈Z} m_ρ ≤ log(4M)/log(7/6)` — lift `ZetaPowLower.lean:334–390`.
4. **Separation** every `ρ ∈ Z` has `‖ρ−c‖ < 3/2` ⇒ `1/2 < Re ρ < 7/2` and `|Im ρ| < T+3/2`; `Re ρ < 1` (`riemannZeta_ne_zero_of_one_le_re`); `zeta_zero_free_region_sharp` (`EpsilonZero.lean:833`) ⇒ `Re ρ ≤ 1 − (1/75712)/log(|Im ρ|+2)`. Hence `Re z − Re ρ ≥ sep > 0`, so `Zc ≠ 0` on the segment and each `u − β > 0`.
5. **Transport** `Φ(u) := log‖Zc(u+it₀)‖ − ∑_ρ m_ρ·½·log((u−β_ρ)²+g_ρ²)` has `Φ'(u) = Re(logDeriv Zc − ∑ m_ρ/(s−ρ))`, so `|Φ'| ≤ K := 120·log(4M)`; MVT (`ZetaInvShallow.lean:305`'s device) gives `|Φ(σ)−Φ(u₁)| ≤ K·(u₁−σ)`; exponentiate.

### 3.4 The constant — the table

`sep = (1/75712)/log(T+3.5+2) − η`; `K = 120 log 4M`; `N = log(4M)/log(7/6)`; `d₀ := 1/K` (the optimum of `log(160/d₀) + K d₀`).

| box | `M` | `η` | `sep` | `K` | `N` | **`−log δ₀` (F2 split anchor)** | `−log δ₀` (anchor at `Re=2`) |
|---|---|---|---|---|---|---|---|
| `T=2`, corpus `c₄` | 96 | 7.4e−19 | 7.75e−6 | 714 | 38.6 | **485** | 1199 |
| `T=2`, `c₃`-arm worst case | 96 | 4.76e−6 | 2.98e−6 | 714 | 38.6 | **522** | 1236 |
| `T=3` (mask b′), `η=0` | 133 | 0 | 7.06e−6 | 753 | 40.7 | **514** | 1268 |
| `T=2` with `M0zeta` (unsharp) | 195 | 7.4e−19 | 7.75e−6 | 799 | 43.2 | 541 | 1341 |

**Recommended pin: `δ₀ := exp(−530)` for `T = 2`, `exp(−560)` for `T = 3`** (≈10% headroom over the worst arm).

Where the EPSILON-SHARP separation buys: `sep` enters as `N·log(1/sep)`, i.e. `132×` in `c₃` = `−N·log 132 = −188 nats`. Real but sub-dominant. **The dominant terms are now `N·log(1/sep) ≈ 470` and, if F2 is skipped, `K ≈ 714`.** Further levers, in order of return:
1. **F2 (the anchor split)** — 715 nats, ~60 lines. Do it.
2. The `120` in `entire_norm_logDeriv_sub_sum'` — EPSILON-SHARP's own §"NOT DONE (3)" already names it as "where the next factor of two lives". Worth ~1 nat here after F2 (it only multiplies `d₀+η`), but worth ~357 without F2. **After F2 it is no longer the lever** — re-price it.
3. `M` (sharp sphere bound) — 57 nats via `N`. Already landed; just use `_height_two`, not `M0zeta`.
4. A `|γ| ≤ 3.5` extension of `zeta_zero_free_strip_sharp` (the branch-2 3-4-1 re-run at `log 5.5` instead of `log 3`) would roughly double `sep` ⇒ −27 nats. **Not worth a wave.**

### 3.5 Per-mask consumption

- **(a)** `Zc_band_lower` at `T=2`, `η := c₄/log2⁹` → feeds `hband` of `Zc_patch_lower_bounded_of_band` (`EpsilonZero.lean:429`, note the `1/5 ≤ ‖z−1‖` hypothesis is exactly what the stone assumes) → floor `min δ₀ (1/4)` on the whole `Zc_patch_lower` rectangle → `zeta_inv_shallow_explicit` with `C = max(1/c, 4/(δ₀ log2⁷), 4/log2⁷)` fully explicit. **Caveat:** the explicit `a` requires re-deriving `zeta_inv_shallow` off `zeta_zero_free_region_sharp_bounded` (`:929`) rather than the opaque `zeta_zero_free_region` at `ZetaInvShallow.lean:120`. That is a re-run of `:116–234` with two `obtain`s changed, not a new proof.
- **(b)** does **not** consume the stone. `zeta_lower_compact_mid_explicit` off `zeta_lower_shallow` (F1).
- **(b′)** `Zc_band_lower` at `T=3, η=0`, plus `Zc_lower_near_pole` for `‖z−1‖ ≤ 1/5` and `Zc_lower_of_two_le_re` for `Re ≥ 2` → `zeta_lower_small_t_explicit` with `δ = min δ₀ (7/25) / 4`. Also de-opaques `SiegelArm.lean:235`.
- Both feed `zeta_lower_all_t_of_pow` (`ZetaLowerAllT.lean:185`), whose `c'' = min c' (min ε₀ δ)` then becomes explicit modulo `zeta_pow_lower`'s own `c'`. Downstream consumer: `MR/NonPret.lean:124`.

### 3.6 Effectivity twins owed (the EPSPIN genre, no new analysis)

- `zeta_log_bound_explicit` — `ZetaLogBound.lean:126` already writes `refine ⟨36, …⟩`; a 3-line de-existentialisation.
- `zeta_lower_shallow_of_logBound (C₁) (hC₁ : 1 ≤ C₁) (hlog : …)` — refactor `ZetaLowerShallow.lean:323` into the hypothesis-taking genre; then `c₄ = b⁴`, `c = b³/(4C₁)` with `b = 1/(8C₁P)`, `P = 6C₁+54` are literals. At `C₁ = 36`: `b = 1/77760`, **`c₄ = 2.735e−20`, `c = 1.477e−17`**. Both the landed existential form and the explicit one become one-liners. *(This is also what pins `η ≈ 7.4e−19` in the table.)*

---

## 4. WAVE DECOMPOSITION (tomorrow's block)

Additive only; nothing landed is altered. Suggested home: a new `Salt/SW/ZetaBandFloor.lean` (SW, so both SW and MR consumers can import) + a small `Salt/MR/` closing file.

| # | node | statement | class | ln | deps |
|---|---|---|---|---|---|
| **W0-a** | `MID-FILL` | `zeta_lower_compact_mid_explicit` off `zeta_lower_shallow` — **F1** | A/B | 25 | none — **dispatch first, it is free** |
| **W0-b** | `EFFECTIVE-SHALLOW` | `zeta_log_bound_explicit`; `zeta_lower_shallow_of_logBound`; `zeta_lower_shallow_bounded` (`c ≥ 1.4e−17`, `c₄ ≥ 2.7e−20`) | B | 120 | refactor of `:323` body, verbatim with `C₁` a binder |
| **W0-c** | `BAND-CEILING` | `zeta_upper_band` explicit, `Z = 53`, off `Zc_sphere_bound_sharp` | A | 20 | none |
| **W1** | `FAR-UNGATE` | `zeta_horiz_lower'`, `zeta_pow_lower_far'` at `(ht : t ≠ 0)`; old two as corollaries — **F2** | B | 70 | bodies verbatim, one `hzne1` line changed |
| **W2** | `LANDAU-COUNT` | `entire_factorization_count_le` — from the six exported invariants of `entire_norm_logDeriv_sub_sum'`, recover `∑_{ρ∈Z} (m ρ:ℝ) ≤ log(4M₀)/log(7/6)` | B | 90 | lift `ZetaPowLower.lean:334–390`; **do not widen the existing export** |
| **W3** | `PER-ZERO-INT` | `hasDerivAt (fun u:ℝ => ½ log((u−β)²+g²)) ((u−β)/((u−β)²+g²))`; `Re (1/((u+it₀)−ρ)) = (u−β)/((u−β)²+g²)`; the `Φ` MVT lemma | C | 170 | `Complex.inv_re`; MVT device from `ZetaInvShallow.lean:305` |
| **W4** | `BAND-FLOOR` | `Zc_band_lower_of_sep` + the two numeral instances (`T=2`, `T=3`) + `zeta_band_sep` (separation off `zeta_zero_free_region_sharp`) | C | 200 | W1–W3 |
| **W5** | `THE THREE CLOSERS` | `Zc_patch_lower_explicit` (via `:429`); `zeta_inv_shallow_explicit`; `zeta_lower_small_t_explicit`; `zeta_lower_all_t_explicit` | B | 150 | W0-a, W4 |

Total ≈ **845 lines**, one class-C core (W3+W4 ≈ 370). W0-a/b/c and W1/W2 are mutually independent — **fire five executors in parallel**; W3 gates W4 gates W5.

---

## 5. REFUTER CHECKS TO ASSIGN BEFORE W4 DISPATCHES

1. **Circularity.** `zeta_zero_free_region_sharp` must not depend on any of the four masks. EPSILON-ZERO ran a 4829-constant transitive closure walk for its own leaf; re-run it for `Zc_band_lower` against `{Zc_patch_lower, zeta_lower_compact_mid, zeta_lower_small_t, zeta_zero_free_strip, IsCompact.exists_isMinOn, Metric.infDist}`. Note the *new* risk W0-b introduces: `zeta_lower_shallow` → `zeta_log_bound`, and `zeta_inv_shallow`'s `c₄` is `min`'d against `c₄₀` from `zeta_lower_shallow` — check the stone does not close a loop through `zeta_inv_shallow`.
2. **F2's `ht` audit.** Verify at the bytes that `ht` occurs in `zeta_horiz_lower`'s body *only* in the `hzne1` block, and in `zeta_pow_lower_far`'s body *only* at the `zeta_horiz_lower` application. (My read says yes; a refuter should re-read `:198–290` line by line, because the whole 715-nat saving hangs on it.)
3. **Geometry.** `2 − a ≤ 23/20` must hold with room. At `η ≤ 4.8e−6` it is `1.0000048 < 1.15` ✓ — but if a future consumer widens the patch to `Re ≥ 1/2` this **breaks**, and the stone would need the scaled Landau core. State the `η ≤ 1/10` hypothesis explicitly.
4. **The band's height floor.** F2's anchor needs `t₀ ≠ 0`; the derivation `|t₀| ≥ 1/5 − d₀` uses `‖z−1‖ ≥ 1/5` **and** `Re z ≤ 1+d₀`. Mask (b′)'s box has `Re` up to 2 — the `Re ∈ [1+d₀, 2]` slab must be handled separately (it is: `‖Zc‖ ≥ ‖z−1‖·(Re z−1)/32 ≥ d₀²/32` for `t₀ ≠ 0`, and `Zc(σ) = (σ−1)ζ(σ) ≥ σ−1` on the real axis since `ζ(σ) ≥ 1`). Make sure the case split is exhaustive at `t₀ = 0`.
5. **Downstream budget.** CMU-HUNT §3/§4(b) (`docs/exploration/cmu-hunt-0802.md`) ratified BAND-WINDOW with `A₀ := 36 000` against a traced ceiling `log Cband ≈ 22 661` (tolerance `0.64·A₀ − 4.2`). The δ-leaf enters `zeta_inv_shallow`'s `C` as `log(4/δ₀) ≈ 530`, and `C` feeds row 2 of `C_mu`. **Budget it before `A₀` is frozen**: at face value `A₀ = 36 000` still clears (`23 036` vs `22 661 + ~530`), but the margin drops from ~375 to a few hundred nats and the multiplier through row 2's "shallow gate spends `9·A_pow`, squared" is not obviously 1. Have a refuter price the exact hop `δ₀ → C → C₂ → Cband` before W5 lands.

---

## 6. ONE-LINE VERDICT

The wall is real but it is **one box, not three**, and it is **~485 nats deep, not 14 000**. Mask (b) falls to a landed theorem for free; masks (a) and (b′) fall to a single `Zc` floor built from four devices already on disk (`entire_norm_logDeriv_sub_sum'`, `entire_zero_count_le`, the `ZetaPowLower` count block, the `ZetaInvShallow` MVT transport), with one genuinely new idea — **integrate the per-zero terms exactly instead of bounding them uniformly** — and one free ungating (`zeta_pow_lower_far` at `t ≠ 0`) that pays for the dominant term.
