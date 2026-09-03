# WAVE C SCOUT — HB 1983 §6 (pp.215–221) against the corpus

**Date:** 2026-09-03. **Seat:** salt, Opus, READ-ONLY (no Lean, no build, no state-changing git).
**Commission:** `docs/exploration/n7-assembly-gate-0811.md` §2, "WAVE C — §6: the leading-term
evaluation (SCOUT FIRST, then two waves split at (6.12))" — ordered 08/11 "in parallel with Wave A,
it blocks nothing"; never ran; the 09/04 council prices Wave C from this dossier.
**Sources read:** `docs/sources/hb1983-notes.md` §6 (`:684-802`), §5 (`:522-683`), §2b–2f
(`:216-323`), §8 (`:895-915`), §9 (`:934-968`), §10 (`:969-988`); `n7-prep-dossier-0806.md`
ADDENDA B (`:447-525`) and D (`:562-677`).

**⚠️ EPISTEMIC TIERS, kept apart on every row.** **[KERNEL]** — a declaration exists at the cited
`file:line` on this tree (bytes-say-so; no build was run, per the read-only order). **[DESIGN]** —
priced in a freeze/gate only. **[HB-NOTES]** — transcribed from the paper. **[SCOUT]** — derived
this sitting. Absence rule (QUEUE row 19i): "not found under N arms, arms listed" — unless a
sibling control in the same convention IS found, in which case ABSENT, siblings named.

---

## §0 — HEADLINE

§6 turns (5.19)'s dyadic bilinear sum into Lemma 5's evaluation, and it needs three things the
corpus does not have and two it does: it needs (i) a **definitional layer** — the linear forms
`l_i(n) = α_i n + β_i`, the measure `A(w₁,w₂)`, the two-variable Euler products `F(u,v)`/`G(u,v)`,
the Dirichlet series `S(d;t)`/`S′(d_i;t,σ)` — none of which exists in `Salt/` under any arm
(sibling control: `roadModulus`, `Salt/Weil/RoadModulus.lean:62`, IS the §5 modulus in the same
convention, so this is ABSENT, not merely unfound); (ii) **two generic product-differentiation
formulae** (dossier B.3), of which mathlib supplies the first almost outright —
`logDeriv_tprod_eq_tsum`, `.lake/packages/mathlib/Mathlib/Analysis/Calculus/LogDerivUniformlyOn.lean:24`
— and the second, the **mixed second derivative of an infinite product, not at all** (no
`deriv_tprod`, no `HasDerivAt.tprod`, no Leibniz rule for `iteratedDeriv` of a `Finset.prod`; arms
listed in §3); and (iii) an **additive-arithmetic-function predicate** for `A(d), A′(d), A₁, A₂, A₃`
— mathlib has `IsMultiplicative` (`…/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:418`) and
**no `IsAdditive` at all** (ABSENT, sibling named). What the corpus DOES supply is exactly the two
regime-killers, both unconditional and both sharper than HB: `sum_class_eq_zero_of_isPrimitive`
(`Salt/HB/RealPrimitive.lean:415`) kills regime (b) at constant zero, and
`sum_two_forms_le_gcd_of_isPrimitive` (`Salt/HB/RealPrimStructure.lean:763`) kills regime (c) at
constant **one** where HB writes `≪`, with the Δ-fold descent (W4-c′) already landed beside it at
`Salt/HB/RealPrimitive.lean:129`; and it supplies `κ` and `G(d)` as print-certified kernel objects
(`Salt/HB/Lemma7Kappa.lean:348`/`:86`) so §6's exit has a target rather than a definition to invent.
Price: **Wave C-1 (regimes, through (6.11)) 1,450–3,150 ln, class B with two C-clusters; Wave C-2
(the main term, (6.12)–(6.16) and the σ→1 limit) 4,000–7,900 ln, class C throughout; total
5,450–11,050 ln** — above the 08/06 dossier's 4,000–9,000, and the excess is the two missing
stones plus the definitional layer, itemised in §6.

---

## §1 — THE EQUATION LEDGER, (6.1)–(6.16)

All "states" entries are **[HB-NOTES]** at the cited `hb1983-notes.md` line. Class per salt's
CLAUDE.md table. "ln" = executor line estimate for that row alone.

| Eq | States (HB-NOTES) | Consumes | Corpus supply / gap | Class | ln |
|---|---|---|---|---|---|
| **(6.1)** `:691` | regime-(a) coprimality `(w_i,α)=(w₁,δ₂)=(w₂,δ₁)=(w₁,w₂)=1` | Lemma 11's (5.19) `Σ*`, (5.6) | GAP — a coprimality bundle; `Nat.Coprime` only | A | 40–80 |
| **(6.2)** `:693-696` | summand `K^{−1}(w₁w₂)^{−1}A`, `K = δ₁δ₂qΔ^{−1}`, `A(w₁,w₂) = mes{t ∈ [x,2x] : R_i ≤ l_i(t)/(δ_iw_i) ≤ 2R_i}` | the forms `l_i`, Lebesgue measure on ℝ | GAP — **no `l_i(n) = α_i n + β_i` object in `Salt/`** (arms: `roadForm`, `linear form`, `α₁`, `alpha1`, `RoadPair`, `roadPair`; sibling `roadModulus` FOUND ⇒ ABSENT). Measure: mathlib `MeasureTheory.volume` on `Set.Icc` | B | 200–350 |
| **(6.3)(6.4)** `:698-703` | the `a_i` count: `t₂ ≡ γt₁ (mod q/Δ)`; `a₂ ≡ ca₁+b (mod q/Δ)`; count `= ∏_{p∣q/Δ}(p−2) = qΔ^{−1}M`, `M = ∏_{p∣q/Δ,p∤α}(1−2/p)` | q **cube-free**, (1.9) ⟹ `(α_i,q/Δ)=1`, `(Δ,q/Δ)=1` | GAP for the CRT count; `Δ = (α₂,q)`, `D = α₂qΔ^{−1} = Nat.lcm α₂ q` is **[KERNEL]** `Salt/Weil/RoadModulus.lean:62` (`roadModulus_eq_lcm`) | C | 300–600 |
| **(6.5)(6.6)** `:709-713` | regime (b): `Σ_{d∣q/Δ}μ(d)Σχ(b₂)` over a class mod `dΔ`; **vanishes unless `dΔ = q`**; (6.6) is `O(1)` | **χ primitive** | ✅ **[KERNEL]** `sum_class_eq_zero_of_isPrimitive`, `Salt/HB/RealPrimitive.lean:415` — see §2(b) | B | 200–400 |
| **(6.7)(6.8)** `:716-726` | regime (c): `|Σ| = |Σ_{t=1}^{q/Δ} χ(Δγ₁t+β₁)χ(Δγ₂t+β₂)| ≪ Δ^{−1}(q,Δα^{−1}(α₁β₂−α₂β₁)) ≪ 1` | χ **real** primitive; **(1.6)** `α₁β₂−α₂β₁ ≠ 0` | ✅ **[KERNEL]** `sum_two_forms_le_gcd_of_isPrimitive` `Salt/HB/RealPrimStructure.lean:763` **at constant 1** + the Δ-descent `sum_range_eq_nsmul_of_dvd_of_periodic` `Salt/HB/RealPrimitive.lean:129` — see §2(c) | B | 250–450 |
| **(6.9)** `:728-735` | `S(δ₁,δ₂;V₁,V₂) = Σ_{R_i,S_i}M(δ₁δ₂)^{−1}F(R_i,S_i) + O(xL⁴(qδ₁δ₂)^{−1}) + O(δ₁δ₂q^{13/2}x^{15/16+2ε})` | (6.2)+(6.6)+(6.8) and (5.19)'s error | GAP — the assembly; the three inputs are rows above | C | 300–600 |
| **(6.10)** `:734` | `Σ_{w∈I,(w,f)=1}χ(w) = Σ_{g∣f}μ(g)Σ_{w∈I,g∣w}χ(w) ≪ q·d(f)`, **PV-free** (`|Σχ| ≤ q` over any interval) | Möbius coprimality expansion; trivial complete-sum bound | ✅ better than needed: **[KERNEL]** `Salt.BV.polya_vinogradov` `Salt/BV/PolyaVinogradov.lean:234` gives `‖Σ_{m<t}χ(m)‖ ≤ √f(1+log f)`. **[SCOUT]** it is over `Finset.range t`, so an arbitrary interval costs one differencing step (~20 ln). GAP: the μ-expansion itself | B | 150–300 |
| **(6.11)** `:737-742` | `≪ x^{1+ε}q^{−1} + x^{15/16+3ε}q^{14} ≪ x^{1+ε}q^{−1}` **since `δ₁δ₂ ≤ q⁴d²` and `x ≥ q^250`** — the LOWER window edge | (6.9) fed into Lemma 9; `d ≤ q^{1/3}` | GAP — pure real-exponent arithmetic. Notes record ~10 powers of `q` of slack (`:744-746`) | B | 200–400 |
| **(6.12)** `:751-753` | `S(d;t) = Σ_{d_i,r_i, r_i ≤ l_i(t)} S(d₁,r₁)S(d₂,r₂)`; `S(d_i,r_i) = χ(r_i)(r_id_i)^{−1}log(l_i(t)/r_i)M(r_i)Σ_{h_i∣(d_i,r_i)}h_iΣ_{j_i∣h_i}μ(j_i)/j_i`; `M(r) = Σ_{m∣Q,m²≤r}μ(m)` | `Σ_{R_i}A(w₁,w₂) = mes{t : l_i(t)/(δ_iw_i) ≥ V_i}`; `Q = ∏_{p<z,χ(p)=−1}p` | GAP — **the split point.** `μ` is mathlib `ArithmeticFunction.moebius`; the nested divisor sums are Finset work | C | 300–500 |
| **(6.13)(6.14)** `:755-757` | the collapsed `S(d;t)` with `(d₁,r₁)(d₂,r₂)` and the four coprimality side conditions | (6.12) + the `h_i`/`j_i` collapse | GAP; elementary but bulky | B | 250–400 |
| **(6.15)** `:762` | replacement `M(r) → N(r)` (`N(r)=0` iff `p²∣r` for some `χ(p)=−1`), error `≪ L⁴z^{−1}d^{−1}4^{ω(d)}` — **Lemma 5's stated error** | the `Q`-squarefree structure | GAP. `ω(d)` is **[KERNEL]**-adjacent: `ArithmeticFunction.cardDistinctFactors`, used at `Salt/Brun/M5Assembly.lean:82`, `Salt/SW/DHBal.lean:458` | C | 400–800 |
| **(6.16)** `:765-766` | extension of the `r_i`-sum to ∞ via `S′(d_i;t,σ)`, `σ > 1`, `S′(d;t) = d^{−1}lim_{σ→1}Σ_{d=d₁d₂}S′(d_i;t,σ)`; tail by partial summation + (6.10) again, total `≪ q d x^{ε−1/4}` | (6.10); Abel summation | GAP. Abel summation exists in mathlib (`Finset.sum_Ioc_by_parts`-family); the Dirichlet-series objects do not | C | 400–800 |
| **F/G** `:770-772` | `f(u,v) = l₁^u l₂^v F(u,v)G(u,v)`; `F` an infinite Euler product over `p∤α` split by `χ(p)=±1`; `G` a **finite** product over `p ∣ d` | Euler-product factorisation of `S(d_i,l_i,σ)` | GAP — see §3. Idiom precedents **[KERNEL]**: `Salt/HB/Lemma7Kappa.lean:339-340` (`tprod` + `Multipliable` witness `:329`), `Salt/HB/Lemma7Prod.lean:169-232` (ordered partial products where `∏'` is wrong) | C | 500–1,000 |
| **log-diff** `:774-777` | `F_u/F = F_v/F = L′(σ,χ)/L(σ,χ) + C₁`; `F_{uv} = F((L′/L)² + 2C₁(L′/L) + C₂)`; `G_u = G_v = G·A₁(d)`; `G_{uv} = G(A₂+A₁²)`; `C_i ≪ 1` in `q,t,σ` **but not in `α`**; `A₁(p) ≪ log p`, `A₂(p) ≪ (log p)²` | **the two B.3 formulae** | GAP — the two stones, §3. Reusable **[KERNEL]**: `logDeriv_LFunction_eq` `Salt/SW/EulerBridge.lean:145` and `norm_logDeriv_LFunction_sub_primitive_le` `:245` are exactly the "`L′/L` + bounded finite-prime correction" shape | C | 800–1,600 |
| **(6.17-eq)** `:790-791` | `Σ_{d=d₁d₂}S(d_i,l_i,σ) = F(0,0)G(0,0){(L′/L)² + A₁(d)² + A₃(d) + L²C₃ + LC₄(L′/L)}` | the four log-diff identities | GAP — the assembly display (HB does not number it) | C | 300–600 |
| **σ→1 / exit** `:793-795` | `MF(0,0) → κx^{−1}`, `G(0,0) → G(d)`; **Lemma 5 follows on integrating over `t`**, the `t`-integral of `A₃` again additive | continuity in σ; additivity | ✅ targets **[KERNEL]**: `hbKappa` `Salt/HB/Lemma7Kappa.lean:348`, `hbG` `:86`. GAP: the limit itself, and additivity (no `IsAdditive` — §0) | C | 400–800 |

**Consumer of the exit, for the statement shape [KERNEL]:** `Salt/HB/RosserDim4Instance.lean:558`
already names what N8 owes — *"(i) **Lemma 5** — the evaluation `S(d) = κ(G(d)/d){(L′/L)² + A²(d) +
A′(d) + C₀} + O(xL⁴z^{−1}d^{−1}4^{ω(d)})`"*. Wave C's exit statement should be written to that
consumer, not invented.

---

## §2 — THE THREE REGIMES

The split is by whether `S_i ≤ R_i` (the dyadic `w`-scale vs the dyadic `v`-scale of (5.2)).

### (a) `S_i ≤ R_i` for both `i` (pp.215–216) — the MAIN TERM, and the only one that survives
Enters at (6.1)/(6.2), where Lemma 11's (5.19) applies verbatim. What it **still owes**, all GAP:
the forms `l_i` and the measure `A(w₁,w₂)` (6.2); the `a_i`-count `∏_{p∣q/Δ}(p−2) = qΔ^{−1}M`
(6.3)/(6.4) — a CRT count spending q cube-free and (1.9); the character sum `F(R_i,S_i) =
Σ_{w_i}χ(w₁w₂)(w₁w₂)^{−1}A(w₁,w₂)`; then everything from (6.12) on. It is regime (a) that becomes
Wave C-2 in full.

### (b) `S₁ ≤ R₁`, `S₂ > R₂` (p.216) — KILLED by primitivity, unconditionally
HB Möbius-expands `(b₂+b″, q/Δ) = 1` into `Σ_{d∣q/Δ}μ(d)Σχ(b₂)` with the inner sum over a class
**mod `dΔ`**, and *"since χ is primitive, this last sum vanishes unless `dΔ = q`"*. The killer,
**[KERNEL]**, `Salt/HB/RealPrimitive.lean:415`, verbatim:

```
theorem sum_class_eq_zero_of_isPrimitive {R : Type*} [CommRing R] [IsDomain R] {q : ℕ}
    [NeZero q] {χ : DirichletCharacter R q} (hprim : χ.IsPrimitive) {f : ℕ} (hf : f ∣ q)
    (hfq : f ≠ q) (c : ZMod f) :
    ∑ b ∈ Finset.univ.filter (fun b : ZMod q => ZMod.castHom hf (ZMod f) b = c), χ b = 0
```

Its own docstring says *"N7 quotes this as: the p.216 vanishing of a primitive character over a
congruence class to a proper divisor of the modulus"* (`:413-414`), and *"for an arbitrary residue
`c` — **no coprimality hypothesis on `c`**"* (`:406`). **What remains for the executor:** identify
`f := dΔ`, prove `dΔ ∣ q` and `dΔ ≠ q` for the surviving `d`, and run the μ-expansion — the sum
over `d` collapses to the single term `dΔ = q`, giving (6.6) `= O(1)`. Class B, 200–400 ln.

### (c) `S_i > R_i` for both `i` (p.217) — KILLED by the two-forms bound, unconditionally and SHARPER
HB reduces to `|Σ_{t=1}^{q/Δ} χ(Δγ₁t+β₁)χ(Δγ₂t+β₂)|`, quotes (proof omitted as straightforward)
`Σ_{t=1}^{q}χ(ut+u′)χ(vt+v′) ≪ (q,uv′−vu′)`, and concludes `≪ Δ^{−1}(q,Δα^{−1}(α₁β₂−α₂β₁)) ≪ 1`
**using (1.6)**. Two **[KERNEL]** pieces, both present:

```
theorem sum_two_forms_le_gcd_of_isPrimitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℤ q)
    (hprim : χ.IsPrimitive) (u u' v v' : ZMod q) :
    |∑ t : ZMod q, χ (u * t + u') * χ (v * t + v')|
      ≤ (Nat.gcd q (u * v' - v * u').val : ℤ)                 -- RealPrimStructure.lean:763
```
```
theorem sum_range_eq_nsmul_of_dvd_of_periodic (f : ℕ → M) {q Δ : ℕ} (hΔ : Δ ∣ q)
    (hper : ∀ t, f (t + q / Δ) = f t) :
    ∑ t ∈ range q, f t = Δ • ∑ t ∈ range (q / Δ), f t        -- RealPrimitive.lean:129
```

The first is at **constant 1**, strictly sharper than HB's `≪` (its docstring: *"nothing is assumed
about the shape of `q` or of `χ` beyond primitivity"*, `:759-760`). The second is W4-c′, the Δ-fold
periodicity descent that ADDENDUM B.1 predicted would be load-bearing and it is: §6 needs the sum
over `t ≤ q/Δ`, not over `t ≤ q`. **[SCOUT] the periodicity hypothesis discharges cleanly**:
shifting `t` by `q/Δ` shifts `Δγ_i t` by `γ_i q ≡ 0 (mod q)`, so `f` is `q/Δ`-periodic — one
`ZMod` computation, class A. **What remains:** that discharge, the `ℤ`→`ℂ` composition (the
docstring names the route: `MulChar.ringHomComp (Int.castRingHom ℂ)`, `:761`), and the numeric
collapse `Δ^{−1}(q, Δα^{−1}(α₁β₂−α₂β₁)) ≪ 1` off (1.6)+(1.7). Class B, 250–450 ln.

---

## §3 — THE TWO GENERIC PRODUCT-DIFFERENTIATION FORMULAE (dossier B.3) — POINT THE EXECUTOR HERE FIRST

The dossier's B.3 (`n7-prep-dossier-0806.md:494-503`) reduces §6's frightening
"two-variable logarithmic differentiation of an Euler product" to two statements **about products**,
not about this Euler product:

```
STONE 1:   ∂/∂u   ∏_m a^{(m)}(u,v) = {∏_m a^{(m)}}·{Σ_m a_u^{(m)}/a^{(m)}}
STONE 2:   ∂²/∂u∂v ∏_m a^{(m)}(u,v)
             = {∏ a^{(m)}}·{(∂_u ∏ a)(∂_v ∏ a) + Σ_m (a_uv^{(m)}/a^{(m)} − a_u^{(m)}a_v^{(m)}/(a^{(m)})²)}
```

### The house idiom these must be stated in
The corpus holds **two** infinite-product idioms and they are not interchangeable — a Wave C
statement must pick deliberately:

- **`tprod` + a genuine `Multipliable` witness** — used where the product converges absolutely.
  `Salt/HB/Lemma7Kappa.lean:339-340`: `noncomputable def hbKappaTail … := ∏' p :
  Salt.TwinBar.PrimesGt2, hbWfac χ α (p : ℕ)`, backed at `:329-332` by `theorem
  hbWfac_multipliable … := Real.multipliable_of_summable_log (fun p => hbWfac_pos …)
  (hbWfac_log_summable χ α)`, whose docstring says *"so `hbKappaTail` is the honest convergent
  product, never mathlib's junk default"* (`:327-328`). The summability chain is a `|log factor| ≤
  8/p²` majorant (`abs_log_hbSfac_le` `:185`, `summable_eight_div_sq` `:268`), and there is a
  reusable generic tail lemma at `:223` (`tsum_tail_inv_sq_le`).
- **Ordered partial products, `exp ∘ limUnder`** — used where `∏'` is *mathematically wrong*.
  `Salt/HB/Lemma7Prod.lean:22-26` verbatim: *"`F` is **not** a `tprod`. Mathlib's `Multipliable` is
  unconditional (net) convergence, which for this product is equivalent to the absolute convergence
  of `∑_{p ≥ z} |χ(p)|/p` — and that series **diverges** … so `∏'` is the mathematically wrong
  object here and no amount of Lean effort would produce it."* The replacement:
  `hbEulerLog` (`:169`), `hbEulerProd` (`:173`), `hbLogF := limUnder Filter.atTop …` (`:201`),
  `hbF := Real.exp (hbLogF …)` (`:205`), with `tendsto_hbEulerProd_hbF` (`:222`) paying the debt.

**🔱 FORK, Fable/helm tier — which idiom `F(u,v)` takes.** Arm 1: `tprod`, on the ground that at
`u=v=0, σ>1` the factors are `1 + O(p^{−σ})` with `σ > 1`, so `∑|log factor|` converges and
`Multipliable` is honest — but this **fails at σ = 1**, exactly where the limit is taken. Arm 2:
the `Lemma7Prod` ordered idiom, which survives σ→1 but has **no derivative theory at all** (see the
gap below: `hbF` is `exp ∘ limUnder` and nothing in the corpus differentiates it). Both arms are
recorded; this scout does not choose.
**[SCOUT] a third reading that may dissolve the fork, offered as evidence not as a decision:** the
σ→1 limit is taken of `M·F(0,0)`, and factor-by-factor `F(0,0)·L(σ,χ)^{−2}` is *absolutely*
convergent — at `χ(p)=1` the factor `(1−p^{−2σ})/(1−p^{−σ})²·(1−p^{−σ})² = 1−p^{−2σ}`, at
`χ(p)=−1` the factor `(1−2p^{−σ})·(1+p^{−σ})² = 1 − 3p^{−2σ} − 2p^{−3σ}`, at `p∣α` the factor
`(1−χ(p)/p)²`, at `p∣q` the factor `1`. **That is `hbSfac`/`hbWfac` on the nose**
(`Salt/HB/Lemma7Kappa.lean:132-140`: `χ_ℝ(p)=1 ↦ 1−1/p²`, `χ_ℝ(p)=−1 ↦ (1−2/p)(1+1/p)²`, `else ↦ 1`;
`hbWfac = 1` on `p ∣ α`), so **`hbKappaTail` IS the σ→1 limit of `F(0,0)/L(σ,χ)²` restricted to
`p ∤ α`, factor for factor** — which independently re-derives ADDENDUM B.4's "`κ` is defined by that
limit" and confirms D.1's partition from the §6 side. Consequence: state `F` **relative to
`L(σ,χ)²`**, and the `tprod` arm survives the limit. ⚠️ This also fixes `M`: HB's `M =
∏_{p∣q/Δ,p∤α}(1−2/p)` vs `hbKappa`'s `∏_{p ∈ q.primeFactors.filter (¬ p ∣ α)}(1−2/p)` agree exactly
**when every prime of `Δ` divides `α`** — true at the twin instance (`Δ = (α₁,q)` and `α = (α₁,α₂) =
α₁` when `α₁ = α₂`), not stated in general. State the hypothesis; do not assume it.

### What mathlib actually has (searched this sitting; every path absolute under `.lake/packages/mathlib/`)
- ✅ **STONE 1 is essentially in mathlib**, for ℂ: `Mathlib/Analysis/Calculus/LogDerivUniformlyOn.lean:24`
  ```
  theorem logDeriv_tprod_eq_tsum {ι} {s : Set ℂ} (hs : IsOpen s) {x : ℂ} (hx : x ∈ s)
      {f : ι → ℂ → ℂ} (hf : ∀ i, f i x ≠ 0) (hd : ∀ i, DifferentiableOn ℂ (f i) s)
      (hm : Summable fun i ↦ logDeriv (f i) x) (htend : MultipliableLocallyUniformlyOn f s)
      (hnez : ∏' i, f i x ≠ 0) : logDeriv (∏' i, f i ·) x = ∑' i, logDeriv (f i) x
  ```
  Hypothesis suppliers: `Summable.multipliableLocallyUniformlyOn_one_add`
  (`Mathlib/Analysis/Normed/Module/MultipliableUniformlyOn.lean:137`) or
  `Complex.multipliableUniformlyOn_of_clog` (`:72`); `tprod_one_add_ne_zero_of_summable`
  (`Mathlib/Analysis/SpecialFunctions/Log/Summable.lean:216`). Finite case:
  `logDeriv_prod` (`Mathlib/Analysis/Calculus/LogDeriv.lean:73`), already used in-corpus at
  `Salt/SW/PartialFractions.lean:80` and `Salt/SW/BCBound.lean:128`. ⇒ **Stone 1 is a wiring job,
  not a construction: ~200–400 ln, class B.**
- ⛔ **STONE 2 is ABSENT from mathlib and from the corpus.** Arms searched by name and by shape:
  `deriv_tprod`, `hasDerivAt_tprod`, `HasDerivAt.tprod`, `hasFDerivAt_tprod`,
  `Multipliable.hasDerivAt`, `differentiable_tprod`, `DifferentiableAt.tprod`, `deriv2`,
  `deriv_deriv_prod`, `iteratedDeriv_prod`, plus a cross-product regex `(deriv|Differentiab|FDeriv)`
  × `(tprod|TProd)` in both orders — **zero hits**. Sibling control **IS** found in the same
  convention: `deriv_finsetProd` (`Mathlib/Analysis/Calculus/Deriv/Mul.lean:459`),
  `HasDerivAt.finsetProd` (`:417`), `fderiv_finsetProd` (`Mathlib/Analysis/Calculus/FDeriv/Mul.lean:631`),
  and the binary Leibniz rule `iteratedDeriv_mul`
  (`Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean:423`) — so this is **ABSENT**, not unfound.
  There is also **no two-variable partial-derivative API** (no `partialDeriv`/`deriv_fst`/`deriv_snd`);
  mixed partials go through `fderiv` on a product space plus `IsSymmSndFDerivAt`
  (`Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:91`). ⇒ **Stone 2 is a build: 600–1,200 ln,
  class C**, and it is the single largest unbuilt object in Wave C.
- ⛔ **Nothing in mathlib differentiates an Euler product.** `Mathlib/NumberTheory/EulerProduct/`
  carries only log/exp identities (`ExpLog.lean:39`, `DirichletLSeries.lean:137/152/160`);
  `logDeriv_LFunction` does not exist in mathlib — mathlib only proves *continuity* of
  `-deriv (LFunction χ) s / LFunction χ s` (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:369/389`).
  **The corpus is ahead of mathlib here** — `Salt/SW/EulerBridge.lean:145`
  `theorem logDeriv_LFunction_eq` decomposes `logDeriv (LFunction χ) s` as
  `logDeriv (LFunction χ.primitiveCharacter) s + ∑ p ∈ q.primeFactors, logDeriv (eulerFactor …) s`,
  and `:245` `norm_logDeriv_LFunction_sub_primitive_le` bounds the correction by `log q`.
  **[SCOUT]** that is structurally HB's `F_u/F = L′/L + C₁` with `C₁` the finite-prime deficit —
  the closest existing template, though HB's `C₁` must be `≪ 1` (not `≪ log q`), because his
  deficit is over `p ∣ α` plus a `p^{−2σ}`-sized tail, not over `p ∣ q`.
- Also present and useful: `logDeriv_tendsto` (`…/Analysis/Complex/LocallyUniformLimit.lean:201`),
  `TendstoLocallyUniformlyOn.deriv` (`:153`), `hasDerivAt_tsum` (`…/Calculus/SmoothSeries.lean:134`),
  `deriv_tsum` (`:180`); worked models `…/ModularForms/DedekindEta.lean:89` and
  `…/Trigonometric/Cotangent.lean:150-197` (the best end-to-end template in mathlib).

---

## §4 — THE `(6.12)` SPLIT

**Wave C-1 = everything BEFORE (6.12): the regime analysis and the error assembly.**
Rows (6.1) through (6.11). Content: the definitional layer for the forms and the measure; the CRT
`a_i`-count producing `M`; regime (b) killed at `sum_class_eq_zero_of_isPrimitive`; regime (c)
killed at `sum_two_forms_le_gcd_of_isPrimitive` after the Δ-descent; the (6.9) assembly; (6.10)'s
PV-free interval bound and its μ-expansion; (6.11)'s window-edge arithmetic spending `x ≥ q^250`.
Exit: (6.9)/(6.11) with the main term expressed as `M∫_x^{2x}S(d;t)dt` and every error absorbed.
**Nothing analytic. No Euler product. No σ. It can land before Stone 2 exists.**

**Wave C-2 = everything FROM (6.12) on: the main-term evaluation.**
Rows (6.12)–(6.16), the F/G factorisation, the log-differentiation display, the assembly display,
the σ→1 limit, and the `t`-integration into Lemma 5. **Stones 1 and 2 are Wave C-2's opening nodes.**

### ⚠️ THE `C_i`-IN-`α` TRAP — placed at its exact display
It belongs at **`hb1983-notes.md:774-777`**, the display *"Logarithmic differentiation gives
`F_u(0,0)/F(0,0) = F_v(0,0)/F(0,0) = L′(σ,χ)/L(σ,χ) + C₁` …"* — i.e. the **first** display in which
any `C_i` appears, node **C2-06** of §6's table. HB's exact words (`:781-783`, corrected 08/06 from
p.220): *"`C_i` denotes a continuous function of `σ` (`σ ≥ 1`), depending on `i`, `q`, `χ`, `t` and
`α`, but not on `d`, for which `C_i ≪ 1` uniformly in `q`, `t`, and `σ`, **but not necessarily in
`α`**."* **A Lean statement asserting `C_i ≪ 1` uniformly in `α` would be FALSE.** The Lean shape:
`C₁` is a function of `(σ, q, χ, t, α)` with the bound quantified as
`∀ α, ∃ K, ∀ q χ t σ, ‖C₁ …‖ ≤ K` — the `∃ K` **inside** the `∀ α`, never outside. Moot at the twin
instance (`α₁ = α₂ = 4`, so `α = 4` is a literal), but it must be **stated**, never assumed. Two
facts HB separates and both matter: *independent of `d`* (the argument uses it — `d` is the
summation variable) and *not uniform in `α`* (survived only because `α` is fixed).

---

## §5 — THE `(6.15)` / LEMMA-5 `x`-FACTOR RECONCILIATION: **CONFIRMED at the notes**

ADDENDUM D (`n7-prep-dossier-0806.md:596-602`) says the apparent missing `x` is a formalizer trap
already resolved: Lemma 5's error is `O(x·L⁴z^{−1}d^{−1}4^{ω(d)})` while (6.15) is
`S(d;t) − S′(d;t) ≪ L⁴z^{−1}d^{−1}4^{ω(d)}` with no `x`, and the reconciliation is that (6.15) lives
at the `S(d;t)` level while Lemma 5 is reached through `M∫_x^{2x}S(d;t)dt`, so the `x` is the length
of the `t`-integration range. **Checked at the notes and CONFIRMED, not corrected**, on three
independent lines: (i) `:749` — *"the main terms contribute `M ∫_x^{2x} S(d;t) dt`"*; (ii) `:762`
states (6.15) without `x` and calls it *"Lemma 5's stated error term"*; (iii) `:794` — *"**Lemma 5
follows on integrating over t**"*. The §8 ledger carries both forms consistently (`:909` for (6.15),
`:216-222` for Lemma 5). **Executor consequence:** the `x` must be *produced* by the integration
step, not carried through (6.15); a Wave C-2 statement of (6.15) that already has an `x` in it is
wrong by a factor of `x`. Recorded because the ADDENDUM's own warning applies to Wave C's own
statement-writer.

---

## §6 — THE WAVE TABLE

Order is executor order. "consumes" cites rows of §1 and kernel pins.

### WAVE C-1 — before (6.12): the regimes (class B overall; 1,450–3,150 ln)

| # | Node | Statement shape | Consumes | Class | ln |
|---|---|---|---|---|---|
| C1-01 | the forms | `def hbForm (α β : ℤ) (n : ℝ) : ℝ := α*n + β` + (1.3)–(1.9) as a structure | — | A | 80–150 |
| C1-02 | the measure `A` | `A w₁ w₂ = volume {t ∈ Icc x (2x) | R_i ≤ l_i t/(δ_i w_i) ≤ 2R_i}`, finiteness | C1-01, `MeasureTheory.volume` | B | 200–350 |
| C1-03 | (6.1) coprimality bundle | the five conditions as one `Prop` | (5.6) | A | 40–80 |
| C1-04 | regime (b) | `Σ_{d∣q/Δ}μ(d)·Σ_{class mod dΔ}χ = (the dΔ=q term)` | **`sum_class_eq_zero_of_isPrimitive` `RealPrimitive.lean:415`** | B | 200–400 |
| C1-05 | regime (c) periodicity | `f(t + q/Δ) = f t` for `f t = χ(Δγ₁t+β₁)χ(Δγ₂t+β₂)` | ZMod arithmetic | A | 60–120 |
| C1-06 | regime (c) exit | `|Σ_{t<q/Δ} …| ≤ Δ^{−1}(q, …) ≤ 1` | **`sum_two_forms_le_gcd_of_isPrimitive` `RealPrimStructure.lean:763`** + `sum_range_eq_nsmul_of_dvd_of_periodic` `:129` + (1.6) | B | 250–450 |
| C1-07 | (6.3)/(6.4) the `a_i` count | `#{a₁} = ∏_{p∣q/Δ}(p−2) = qΔ^{−1}M`; `M` as a `Finset.prod` | q cube-free, (1.9), `roadModulus_eq_lcm` `RoadModulus.lean:62` | **C** | 300–600 |
| C1-08 | (6.10) interval char sum | `‖Σ_{w∈I}χ(w)‖ ≤ q` and the μ-coprimality expansion `≪ q·d(f)` | `Salt.BV.polya_vinogradov` `PolyaVinogradov.lean:234` (sharper) + differencing | B | 150–300 |
| C1-09 | (6.9) assembly | the three-term display | C1-02/04/06/07/08 | **C** | 300–600 |
| C1-10 | (6.11) window edge | `x^{1+ε}q^{−1} + x^{15/16+3ε}q^{14} ≪ x^{1+ε}q^{−1}` under `δ₁δ₂ ≤ q⁴d²`, `x ≥ q^250` | C1-09, real rpow arithmetic | B | 200–400 |

### WAVE C-2 — from (6.12): the main term (class C throughout; 4,000–7,900 ln)
**The two stones come FIRST**, per the gate's order and B.3's re-pricing.

| # | Node | Statement shape | Consumes | Class | ln |
|---|---|---|---|---|---|
| **C2-01** | **STONE 1** | `logDeriv (fun u => ∏' m, a m u) u₀ = ∑' m, logDeriv (a m) u₀` in the house idiom | mathlib `logDeriv_tprod_eq_tsum` `LogDerivUniformlyOn.lean:24` + `…MultipliableUniformlyOn.lean:137` + `Log/Summable.lean:216` | B | 200–400 |
| **C2-02** | **STONE 2** | the mixed second derivative of `∏' m, a m (u,v)` — the B.3 display | **ABSENT everywhere**; built from `fderiv_finsetProd` `FDeriv/Mul.lean:631` + `TendstoLocallyUniformlyOn.deriv` `LocallyUniformLimit.lean:153` + `IsSymmSndFDerivAt` `FDeriv/Symmetric.lean:91` | **C** | 600–1,200 |
| C2-03 | `F(u,v)`, `G(u,v)` as objects | `F` relative to `L(σ,χ)²` (§3 fork); `G` a `Finset.prod` over `d.primeFactors` | `Lemma7Kappa.lean:339/329` idiom or `Lemma7Prod.lean:169-232` idiom | **C** | 500–1,000 |
| C2-04 | (6.12)/(6.13)/(6.14) | `S(d;t)`, `S(d_i,r_i)`, `M(r)`, the four coprimality conditions | `ArithmeticFunction.moebius`, Finset divisor sums | **C** | 300–500 |
| C2-05 | (6.15) `M(r) → N(r)` | error `≪ L⁴z^{−1}d^{−1}4^{ω(d)}`, **no `x`** (§5) | C2-04, `cardDistinctFactors` | **C** | 400–800 |
| C2-06 | (6.16) + the log-diff display | the `σ>1` extension, tail `≪ qdx^{ε−1/4}`; `F_u/F = L′/L + C₁`, `F_{uv}`, `G_u`, `G_{uv}` — **the `C_i`-in-`α` trap is STATED HERE (§4)** | C2-01, C2-02, C2-03; `logDeriv_LFunction_eq` `EulerBridge.lean:145` as template | **C** | 1,200–2,400 |
| C2-07 | additivity of `A₁, A₂, A₃` | an additive-arithmetic-function predicate + `A₁(p) ≪ log p`, `A₂(p) ≪ (log p)²`, `A₃(p) ≪ (L+|L′/L|)log p` | **no mathlib `IsAdditive`** (sibling `IsMultiplicative` `ArithmeticFunction/Defs.lean:418`) ⇒ define it | B | 300–600 |
| C2-08 | the assembly display `:790` | `Σ_{d=d₁d₂}S(d_i,l_i,σ) = FG{(L′/L)² + A₁² + A₃ + L²C₃ + LC₄(L′/L)}` | C2-06, C2-07 | **C** | 300–600 |
| C2-09 | σ→1 | `M·F(0,0) → κx^{−1}` (target `hbKappa` `Lemma7Kappa.lean:348`), `G(0,0) → G(d)` (target `hbG` `:86`) | C2-03, C2-08; §3's `hbSfac` identification | **C** | 400–800 |
| C2-10 | the `t`-integration + Lemma 5 | `S(d) = κ(G(d)/d){(L′/L)² + A²(d) + A′(d) + C₀} + O(xL⁴z^{−1}d^{−1}4^{ω(d)})`, written to the consumer at `RosserDim4Instance.lean:558` | C2-05, C2-09, C2-07 (the `t`-integral of `A₃` is again additive) | **C** | 400–800 |

**Totals.** C-1 1,450–3,150 · C-2 4,000–7,900 · **Wave C 5,450–11,050 ln.** The 08/06 dossier
priced §6 at 4,000–9,000; this scout is ~25–35% higher at both ends, and the difference is
itemisable: Stone 2 (600–1,200, absent from mathlib and unknown on 08/06), the definitional layer
C1-01/C1-02/C2-03 (780–1,500, ABSENT under the sibling control), and C2-07's missing `IsAdditive`
(300–600). Calibration for the range: HB's Lemma 7 (§4, one lemma) cost ~6,200 ln in this corpus
across `Lemma7{,Prod,F,EF,Kappa}.lean`; §6 is a comparable but wider block.

---

## §7 — WHAT I COULD NOT DETERMINE

1. **Which infinite-product idiom `F(u,v)` must take** — `tprod`+`Multipliable`
   (`Lemma7Kappa.lean:339`) vs the ordered `exp∘limUnder` (`Lemma7Prod.lean:201-205`). Recorded as a
   **fork with both arms** in §3, with a third reading (state `F` relative to `L(σ,χ)²`) that may
   dissolve it. **A statement choice is Fable/helm tier; this scout did not choose.**
2. **Whether HB's `≪ 1` for `C₁` survives at the twin instance with an explicit constant.**
   The freeze rule wants literal constants, not `≪`. HB's `C₁` depends on `α` and on the tail
   `∑_p p^{−2σ}`; a numeral is plausible but I did not derive one.
3. **Whether `M(r)`'s `Q = ∏_{p<z, χ(p)=−1} p` is finite-product-representable in Lean without a
   decidable `χ(p) = −1`.** `hbSfac` (`Lemma7Kappa.lean:132`) does exactly this branch with
   `Salt.TwinBar.chiRe`, so the pattern exists; whether it composes under a `Finset.filter` at
   `Q`'s scale I could not check without elaborating.
4. **The size of the (6.16) tail step.** HB compresses partial summation + a Möbius/character
   manipulation + (6.10) into one sentence (`:765-766`); 400–800 ln is the table's widest guess.
5. **Whether Wave C-1's `A(w₁,w₂)` measure argument needs `MeasurableSet` side conditions that
   mathlib does not hand over for the four-inequality region.** Not searched to conclusion.
6. **⚠️ A NOTATION HAZARD THE `§10` CENSUS DOES NOT CARRY, found this sitting.** `hb1983-notes.md:969-988`
   catalogues eleven meanings of `S`, four families of `A`, and the `κ/G/F/M` collisions — but it
   **does not list `K`**, which is `K = δ₁δ₂qΔ^{−1}` at (6.2) (`:695`) and `K = 2 + k^{1/4}` in §7
   (`:853`). Wave C-1 and Wave A therefore use the same letter for different objects at the same
   time. Recorded here rather than fixed: the notes are a source file and this scout is read-only.
7. **Whether Wave A's seal changes any of this.** Wave A has landed (7.5) and the `d(k)³`
   bookkeeping only (`Salt/HB/Lemma10.lean`, 168 ln, `9e7cbbac`/`2b535e93`/`7d8a8a3f`); §6 consumes
   Lemma 10 only through §5's (5.19), so Wave C-1 is independent of Wave A's remaining rungs.
   I did not verify that (5.19) as Wave B will state it matches (6.2)'s summand shape.
8. **Every pin above is bytes-say-so.** No `lake build` was run (read-only order). Statement-read ≠
   kernel-checked: an executor's build replays them.
