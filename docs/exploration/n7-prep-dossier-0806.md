# N7-PREP DOSSIER — what Lemma 10 consumes, what WEIL-TRIO supplies, and the gap

**Date:** 2026-08-06 (morning). **Seat:** salt MATHEMATICS. **Method:** three parallel
read-only Opus scouts (consumption / supply / corpus+gap), zero Lean — the fleet's third-OOM
standing order pauses BUILDS until 20:00; this dossier is analysis only.

**⚠️ EPISTEMIC POSTURE — BINDING ON EVERY ROW BELOW.** Three tiers are kept strictly apart and
never blurred:

- **[KERNEL]** — a declaration exists at the cited `file:line` **and is committed**. Note this
  still means *the bytes say X*, **not** *X kernel-checks*: no `lake build` was run. Settle after
  20:00.
- **[IN FLIGHT]** — present in the working tree, **uncommitted** (another seat's live work).
- **[DESIGN]** — priced/planned in a freeze doc only.
- **[HB-NOTES]** — transcribed from the paper, not formalized. **All of §5, §6, §7 is this.**
  ⬆️ **UPGRADED SAME DAY:** §5, §6, §7 and Lemma 5's statement have since been **verified against
  the paper itself** (ADDENDA A–D). They remain un-formalized, but they are no longer
  *unverified transcription* — with the single exception of `κ`'s four-product formula (ADDENDUM D).

---

## 0. THE HEADLINE

1. **Lemma 10 consumes exactly ONE thing from outside HB: Estermann (7.1).** Everything else in
   §7 is elementary and either proved there or elementary-but-untranscribed. The paper says so
   itself (`hb1983-notes.md:788`: "Cited: Estermann [6] (7.1) only").
2. **WEIL-TRIO does NOT deliver (7.1) verbatim.** Post-v2 D3 it delivers a strictly weaker pair,
   and the weakness is a `2^{v₂(k)/2}` factor that is **unbounded at general `k`**. It collapses
   to a constant only on road moduli — and that collapse depends on **W4-a**, which D2/D3 do not
   name as a dependency. **This is the single most important finding in this dossier.**
3. **Two supply rows are cheaper than priced**, both because the corpus already holds the tool.
   The `Salt/MR/` sawtooth and phase-sum kit was missed by the WEIL-TRIO dossier entirely.
4. **N7 is very large**: order **9,000–18,000 ln**, and §6 — not Lemma 10 — is the bulk of it.
   Lemma 10 is the famous part; §6 is the expensive part. *(ADDENDUM B re-prices §6's scariest
   sub-block downward: the two-variable Euler-product differentiation is two GENERIC product
   formulae, provable once and reused — the range stands, but the shape is friendlier.)*
5. **⬆️ ADDED AFTER THE SOURCE SWEEP (ADDENDA A–D).** This dossier was built from a transcription.
   All five blocks it depends on have since been read at the paper. **HB was corrected twice; our
   own transcription was corrected three times; two blocks were clean.** The two defects that
   would actually have cost a wave were **ours** — the dropped `w₂` index in (5.14), which is
   Lemma 10's own summation variable, and the dropped *"not necessarily in `α`"* on the `C_i`,
   which would have made a Lean statement **false**. Read the addenda before pricing N7; §§1–4
   below are the pre-sweep text and the addenda amend them where they differ.

---

## 1. THE CONSUMPTION SIDE — §7 walked equation by equation

Source: `docs/sources/hb1983-notes.md:754-793`. All **[HB-NOTES]**.

| Eq | Shape (as transcribed) | Consumes | Proved in §7? |
|---|---|---|---|
| **(7.1)** `:758` | `S(k;u,v) = Σ_{n=1,(n,k)=1}^{k} e((un+vn̄)/k) ≪ d(k)·k^{1/2}·(k,u,v)^{1/2}` | a **complete Kloosterman bound at arbitrary modulus and arbitrary `u,v`** — no unit hypothesis; the gcd factor is load-bearing | **NO — quoted from Estermann [6]** (`:853`). "the paper's only algebra-geometry-grade ingredient, and it enters as a black box" (`:760-761`) |
| **(7.2)** `:765` | `ψ(θ) = −Σ_{0<\|m\|≤K} e(mθ)/(2πim) + O(Min(1/(K‖θ‖),1))` | classical sawtooth Fourier truncation (Vinogradov/Vaaler genre) | **NO** — asserted, never derived; HB's reference list has no source. Treat as an external input to supply |
| **(7.3)** `:766` | `Min(1/(K‖θ‖),1) = Σ_m a_m e(mθ)`, **`K ≥ 2`** | Fourier expansion of the majorant | NO — same status. **`K ≥ 2` is why the final choice is `K = 2 + k^{1/4}`, not `k^{1/4}`** |
| **(7.4)** `:767` | `a_m ≪ Min((log K)/K, K/m²)` | coefficient decay; makes the `m ≥ Kk^{1/2}` tail summable | NO — elementary, untranscribed |
| **(7.5)** `:769` | `S_m ≪ E` | counting only (`I ⊆ (E,2E]`) | **YES**, trivially |
| **(7.6)** `:770-772` | `S_m ≪ (1 + m\|T\|E^{−1}k^{−1})·\|Σ′_{n∈I₀} e(Cmn̄/k)\|` | Abel/partial summation against `e(mT/(nk))`, total variation `≍ m\|T\|/(Ek)` | **YES**. This is the step that lets ONE statement cover both `f(n) = (T−Cn̄)/k` and `(T/n−Cn̄)/k` |
| **(7.7)** `:774-779` | `Σ′_{n∈I₀} g(n) ≪ d(k)k^{−1/2}q^{3/2}{E(k₀,Cm)^{1/2} + Σ_{s≤k₀}k₀(k₀,s)^{1/2}s^{−1}}`, and `Σ_{s≤k₀}(k₀,s)^{1/2}s^{−1} ≪ d(k₀)log(2k₀)` | **FOUR things** — see below | partly |
| **(7.8)** `:780` | `Σ_{M<m≤2M}\|S_m\| ≪ (1+M\|T\|E^{−1}k^{−1})d(k)³(log 2k)³q^{3/2}M{E+k}k^{−1/2}` | (7.7) summed dyadically + divisor bookkeeping `d(k)d(k₀)d(·) ≤ d(k)³` + the gcd average `Σ_{M<m≤2M}(k₀,Cm)^{1/2} ≪ Md(k)log 2k` | **YES** from (7.7) |

**(7.7) unpacked — it is the junction, and it consumes four distinct inputs:**
(a) additive-character orthogonality mod `k` (the `n ≡ r` detector);
(b) the **congruence-restricted linear completion** `Σ_{n∈I₀, q∣n−b} e(−sn/k) ≪ Min(E, ‖sq/k‖^{−1})`
— stated inline, **not derived**;
(c) **(7.1)** at modulus `k`, arguments `(s, Cm)`;
(d) the **gcd-weighted divisor sum** `Σ_{s≤k₀}(k₀,s)^{1/2}s^{−1} ≪ d(k₀)log(2k₀)` — elementary,
untranscribed.
**`q ∣ k` is consumed here, not decorative**: `k₀ = k/q` is the modulus the `s`-sum runs over.

**The final balance** (`:782-786`) and `K = 2 + k^{1/4}` were re-derived symbolically by the
consumption scout and are consistent.

### THE COMPLETE DEDUPLICATED INPUT LIST (this is what supply must match)

1. Estermann (7.1) — arbitrary `k`, arbitrary `u,v`, gcd factor intact.
2. The sawtooth kit (7.2)+(7.3)+(7.4).
3. The congruence-restricted completion (7.7b).
4. The gcd-weighted divisor sum (7.7d) + divisor bookkeeping for (7.8).
   **[the two sums KERNEL 2026-08-08, `Salt/Weil/GcdDivisorSum.lean`; the `d(k)³`
   bookkeeping still open — see gap list row 4 and `flags.md`]**
5. Additive-character orthogonality mod `k` (7.7a).

---

## 2. THE CONSUMPTION SITE — how §5 fires Lemma 10

The ψ's arise from **(5.17)** (`:594`). "Applying Lemma 10" is `:605-609`. The substitution table:

| Lemma 10 slot | §5 value | cite |
|---|---|---|
| summation variable `n` | **`w₂`** | (5.17)'s `w̄₂`; (5.19) `:634-636` |
| `k` | `Dδ₁w₁ = α₂qΔ^{−1}δ₁w₁` | `:605`, `:579` |
| `E` | `S₂`, so `I ⊆ (S₂, 2S₂]` | `:605`, (5.2) `:551-553` |
| `T` | `T₁` or `T₂` of (5.15)/(5.16) after an O(1) split into `T`- and `T/w₂`-shaped pieces; `T ≪ x/δ₂` | `:605-606` |
| `C` | the (5.11) constant, `(C, Dδ₁w₁) = 1` | `:579-584` |
| `b` | `b₂` | `:557`, `:634-636` |
| `q ∣ k` | `q ∣ D` since `Δ = (α₂,q) ∣ α₂` ⟹ `D = (α₂/Δ)·q` | **INFERRED — HB does not spell it out. N7 owes this discharge.** |

(5.19) then feeds §6, whose error rides into (6.9)'s `O(δ₁δ₂q^{13/2}x^{15/16+2ε})` and (6.11)'s
`x^{15/16+3ε}q^{14}`, absorbed by the window edge `x ≥ q^{250}`.

### ⛔ THREE TRANSCRIPTION DEFECTS N7 MUST FIX BEFORE WIRING

1. ~~**(5.14) as transcribed (`:588`) DROPS the `w₂` summation** — recover the double-sum form
   from the source.~~
   ✅ **CLOSED at the source, p.213 (`8e906ed`-successor).** HB prints the **`i`-indexed**
   subscript `Σ_{S_i < w_i ≤ 2S_i, w_i ≡ b_i (mod q)}` — a double sum over both `w₁` and `w₂`,
   matching (5.19). The transcription had collapsed it to `w₁` alone. **The dropped index was
   exactly Lemma 10's summation variable** (`n ↦ w₂`), so this one would have bitten N7 hardest.
   Unlike the `:611` pair, **this defect was ours, not HB's.** Fixed in `hb1983-notes.md:588`
   with a `[corrected 2026-08-06, from the source p.213]` block.
2. ~~**The `:611` erratum residual** — needs HB p.214 at the bytes; N7 owns it.~~
   ✅ **CLOSED at the source, same day (`b25d8aa`).** p.214 read directly: HB **prints**
   `S₁ ≪ x^{1/4}`, so the notes were faithful and **the typo is the paper's**; his own next
   display forces `1/2` three times over. The `S₂ ≪ x^{1/4}` proviso is **the same typo again**
   and is what emptied the regime — at `x^{1/2}` the regime `S₁S₂ ∈ (x^{15/16}, x]` is non-empty,
   and term-by-term the `S₂` proviso **is not needed at all**. N7 owes only the corrected
   exponents. See `docs/sources/hb1983-notes.md` at the `[corrected 2026-08-06]` block.
3. **`(log Kk)³` vs `(log 2k)³`.** The freeze rules Lean statements carry `d(k)³(log 2k)³`
   literally (`weil-trio-design-0806.md:90-93`), but the notes' pre-final display carries
   `(log Kk)³`. Bounded conversion: `sup_{k≥2} log(Kk)/log(2k) = 1.3366` (at `k=2`; limit `5/4`),
   so `(log Kk)³ ≤ 2.39·(log 2k)³`. One explicit-constant line — but it is a line, and it is N7's.

---

## 3. THE SUPPLY SIDE — WEIL-TRIO's exit interface, post-v2

v1 §3 (`weil-trio-design-0806.md:55-60`) promises five rows. **The v2 DELTA block governs**, and
it changes the interface materially.

### ⛔ FINDING #1 — W3 DOES NOT DELIVER (7.1). THE GAP IS UNBOUNDED AT GENERAL `k`.

D3 (`:115-119`) restates W3's exit as the **achieved pair**, not (7.1) verbatim:

```
  W3 exit :  ‖S(a,b;k)‖ ≤ 2^{v₂(k)/2} · d(k) · k^{1/2} · (k,a,b)^{1/2}     [arbitrary k,a,b]
  HB (7.1):  ‖S(k;u,v)‖ ≪              d(k) · k^{1/2} · (k,u,v)^{1/2}
```

Three differences; **only one is a loss**, and it is a real one:

- **`2^{v₂(k)/2}` is extra**, a consequence of D2 deleting W2 (the 2-adic stationary phase): the
  2-part is served by the crude placeholder `norm_kloosterman_two_pow` (`CompositeTail.lean:73`,
  `‖S‖ ≤ 2^κ`), which sits `2^{κ/2}` above the target `√(2^κ)`. **At general `k` this factor is
  unbounded — up to `√k` — so the W3 exit is a genuinely weaker theorem than (7.1).**
- `θ = 0` on the odd part: matches (7.1) exactly. This is what D1's budget bought.
- The implied constant is **explicit and equal to 1** — sharper than HB's `≪` in that respect.

**So N7 receives a TWO-ROW supply where it expected one**: the W3 inequality, plus
`two_pow_factorization_dvd_of_odd_cofactors` (`GcdBranch.lean:355`) to move `2^{v₂(k)}` into `D`.

**🔴 AND THERE IS AN UNNAMED DEPENDENCY.** The numeric collapse to a constant on road moduli is
**not a landed lemma and is not implied by W1-d alone.** W1-d
(`factorization_two_kloosterman_modulus`, `GcdBranch.lean:347`) gives `v₂(k) = v₂(D)` with
`D = α₂qΔ^{−1}`. For the twin instance `α₁ = α₂ = 4` this is `v₂(D) = max(2, v₂(q))`, which is
bounded **only because `v₂(q) ≤ 3` — and that is the structure lemma, W4-a**. Therefore:

> **W4-a is on the critical path for the 2-adic CONSTANT, not merely for the p.217 lift.**
> D2/D3 do not say so. D4 *decoupled* W4-a and re-priced it at 1,300–2,600 ln.

Note also D2's own inequality `v₂(k) ≤ v₂(α₂)+3` (`:99-100`) is loose/garbled — it would give
`≤ 5` at `α₂ = 4`; the correct bound is `max(2, v₂(q)) ≤ 3`, conditional on W4-a.
**RECOMMENDATION: state this in W3's brief and in §3's exit table.**

> ## ✅ **[RECOMMENDATION DISCHARGED 2026-08-08 night — IT IS NOW PROVED, NOT STATED (`ac29358`)]**
>
> `Salt/Weil/RoadModulus.lean` carries both halves, general in `α₂`:
> ```lean
> factorization_two_roadModulus    : v₂(D) = max (v₂ α₂) (v₂ q)
> factorization_two_roadModulus_le : v₂ q ≤ 3 → v₂(D) ≤ max (v₂ α₂) 3
> ```
> **This paragraph's arithmetic is confirmed in the kernel and its two claims are separated:**
> at `α₂ = 4` (`v₂ = 2`) the first row gives exactly this paragraph's `v₂(D) = max(2, v₂ q)`,
> and the second gives `≤ max(2,3) = 3` — ***so D2's `≤ 5` is confirmed LOOSE by a factor of two
> in the exponent, and "the correct bound" is no longer a recommendation but a theorem.***
>
> 🔑 The route is that `D = α₂qΔ^{−1}` **is `Nat.lcm α₂ q`** (`roadModulus_eq_lcm`, `rfl`), and
> `v₂` of an lcm is the max of the `v₂`s (`Nat.factorization_lcm`).
>
> ⚠️ **SCOPE, so this is not over-read.** These rows are about `D` alone. The step from `D` to
> `k = D·δ₁·w₁` is W1-d's (`factorization_two_kloosterman_modulus`, needs `δ₁, w₁` odd), and is
> **not** re-proved here. **W4-a itself — the `v₂(q) ≤ 3` hypothesis — remains OPEN (row 8);
> nothing above proves it, and `hw4a` is exactly where it enters.**

### The other deltas, and what each does to N7

- **D1 (θ ≤ 1/50)** — independently reproduced by arithmetic: `θ_max = 1/2 − 120/X` at `x ≥ q^X`;
  at `X = 250`, `θ ≤ 1/50` exactly; the ε-budget `≤ 1/800` reproduces too. **Effect on N7: none
  in shape.** W1-c landed at `θ = 0` on the odd part, so N7 gets HB's grade with the budget
  unspent. The **binding** consequence is stylistic-but-mandatory: Lean statements carry
  `d(k)³(log 2k)³` **literally, never `k^ε`**.
- **D2 (W2 deleted)** — N7 **gains a row** (W1-d) and must carry W1-d and W3 **as a pair**. The
  mandated pre-flight guard passed at the source PDF.
- **D4 (W4 re-cut)** — three real changes: the `2^{ω(q)}` absorption worry **dissolves** (there is
  no ω-factor; W4-c's constant is **one**, sharper than HB); N7 receives a
  **hypothesis-carrying** theorem until W4-a lands; and N7 **gains W4-c′**, which it genuinely
  needs, because p.217 is consumed at length `q/Δ`, not `q` (`hb1983-notes.md:681`) — W4-c′ is
  exactly the `Δ^{−1}` producing HB's `Σ ≪ Δ^{−1}(q,·)` at `:687`.
- **D5** — §3 **gains a sixth row**: the congruence-restricted completion (7.7b) [W5]. And the
  ownership seam is ruled: **Lemma 10 and (7.5)–(7.8) are N7's; WEIL-TRIO delivers supplies only.**

---

## 4. THE CORPUS INVENTORY — what N7 can quote today

### 4a. Kloosterman [KERNEL unless marked]
`kloosterman` (`Kloosterman.lean:49`, modulus need not be prime) · `norm_kloosterman_le_modulus`
(`CompositeTail.lean:65`) · `norm_kloosterman_two_pow` (`:73`, the crude 2-part) ·
`norm_kloosterman_le_two_sqrt(')` (`Descent.lean:206/:222`, Weil, `2√p`) ·
`norm_kloosterman_prime_pow_even` (`PrimePower.lean:228`) · `norm_kloosterman_prime_pow_ge_two`
(`CompositeFull.lean:230`) · `norm_kloosterman_prime_pow_odd` (`:299`, crude, `√p` above sharp) ·
`kloosterman_zero_right` (`:309`) · `norm_kloosterman_le_tau_sqrt` (`:384`, **needs
`Squarefree c` AND `IsUnit a`**) · `kloosterman_mul_of_coprime` (`Composite.lean:107`, twisted
multiplicativity) · `norm_kloosterman_le_mul_of_coprime(_unit)` (`Composite.lean:190` /
`CompositeTail.lean:224`) · `norm_incomplete_kloosterman_le` (`Incomplete.lean:181`, **prime
modulus only**).

**W1 rows — `GcdBranch.lean`, committed at `d1a5668`:** `kloosterman_descent` (`:132`,
loss-neutral gcd descent) · `kloosterman_eq_sum_crit` (`:197`, unit-free localisation) ·
`kloosterman_zero_right_prime_pow` (`:274`) · `norm_kloosterman_zero_right_prime_pow` (`:295`) ·
**`factorization_two_kloosterman_modulus` (`:347`, W1-d — the row N7 quotes)** ·
`two_pow_factorization_dvd_of_odd_cofactors` (`:355`).

> ### ✅ FINDING #2 — RAISED AND ALREADY RESOLVED, IN FLIGHT, BY THE WEIL-TRIO SEAT.
> The scout found `GcdBranch.lean` committed at `d1a5668` but **absent from HEAD's roll-call** —
> `git show HEAD:Salt/Weil/All.lean | grep GcdBranch` → empty at that moment. Since
> `lakefile.toml` has `defaultTargets = ["Salt"]` and `Salt.lean:14` imports `Salt.Weil.All`, a
> clean build would never have reached the file: six W1 declarations, W1-d among them, would have
> been committed-but-unbuilt.
> **This seat re-checked before publishing and it is now FIXED**: commit **`4a58e51`**
> (WEIL-TRIO-W1(c), the sharp Salié stone) landed *while these scouts were running* and carries
> the `All.lean` roll-call row — `git show HEAD:Salt/Weil/All.lean | grep -c GcdBranch` → **2**.
> **No action owed.** Recorded only because the window was real, and because it is the generic
> hazard of this shared tree: a file can be committed and out of the build closure at the same
> time. Roll-call rows belong in the SAME commit as the file.

**W1-c — `Estermann.lean`, [KERNEL as of `4a58e51`]** (the scouts saw it untracked; it was
committed mid-run — re-checked by this seat): `norm_quadExpSum` (`:167`, `√p`, proved from scratch
— **no `gaussSum`**) · `norm_kloosterman_prime_pow_odd_sharp` (**`:268`**) ·
`norm_kloosterman_prime_pow_unit_sharp` (**`:459`**) · **`norm_kloosterman_prime_pow_gcd`
(`:498`) — the W1 exit**, `‖S(A,B;p^e)‖ ≤ 2√(p^e)·√(gcd(p^e, gcd A B))`, odd `p`, **no
`IsUnit`**, constant 2.
> **[corrected 2026-08-06, by the statement audit]** These three cites originally read `:265`,
> `:456`, `:495` — each exactly **3 low**, because the scouts read the file while it was still
> uncommitted and 3 lines shorter between `:167` and `:265`. (`norm_quadExpSum :167` was
> unaffected and is correct.) The committed numbers are `:268` / `:459` / `:498`, matching
> `weil-trio-design-0806.md` §D8. Recorded rather than silently patched: it is a worked example
> of this dossier's own warning that a snapshot of another seat's in-flight tree ages fast.

### 4b. Character sums
[KERNEL]: `quadraticChar_sum_two_forms_bound` (`QuadCharSum.lean:143`, `≤ 2`) ·
`quadraticChar_sum_two_forms_trivial` (`:123`) · `legendre_sum_two_forms_bound(_trivial)`
(`:281`/`:298`).
[IN FLIGHT]: `quadraticChar_sum_two_forms_eq` (`:200`) · `..._bound_one` / `legendre_..._bound_one`
(`:253`/`:290`, **constant ONE**, W4-c0) · `chi4_/chi8_/chi8'_sum_two_forms_le_gcd`
(`RealPrimitive.lean:71/80/88`, by `decide`) · `HasTwoFormGcdBound(.mul)` (`:151`/`:189`, CRT
engine, **no `2^ω` residue**) · `hasTwoFormGcdBound_jacobiChar` (`:328`) ·
**`sum_two_forms_le_gcd_of_split` (`:381`) — the p.217 exit, with the `e·m` split as a
HYPOTHESIS** · **`sum_class_eq_zero_of_isPrimitive` (`:413`) — the p.216 exit (W4-d)** ·
`sum_range_eq_nsmul_of_dvd_of_periodic` (`:127`, W4-c′).

### 4c. Λ* / Lemma 1 — **already supplied** [KERNEL]
`Salt.HB.LamStar_nonneg` (`TwistChain.lean:359`, Lemma 1(a)) and
`Salt.HB.vonMangoldt_le_LamTilde` (`:367`, Lemma 1(b)), both in the committed roll-call
(`Salt/HB/All.lean:87-88`). **The road table's "N7 also needs Λ* positivity from Lemma 1" is
already discharged.**

> ### ⛔ FINDING #3 — THE `Salt/MR/` SAWTOOTH KIT EXISTS AND THE WEIL-TRIO DOSSIER MISSED IT.
> Both the dossier (`n6-scout-dossier-0805.md:410-413`) and D5 (`:153-155`) record **"nothing
> serving"** for the sawtooth rows and the congruence-restricted completion. That is too
> pessimistic. Landed and audited:
> `Salt.MR.geom_phase_bound` (`MinorArcVaughan.lean:298`) — `‖Σ_{M₁<m≤M₂} e(θm)‖ ≤ minTerm (M₂−M₁)
> (dist₁ θ 0)`, Montgomery p.40 eq.(2), with `minTerm` (`:271`) carrying the `1/‖0‖ = ∞` case
> honestly; `dist₁` (`Salt/LS/Dist.lean:29`) is exactly HB §7's `‖·‖`;
> `two_mul_dist₁_le_abs_sin` (`:136`, Jordan); `Salt.MR.tendsto_sum_sin_div_nat`
> (`Sawtooth.lean:358`) — **the exact sawtooth Fourier series**; `abs_sum_sin_le` (`:329`);
> `abs_sum_mul_le_of_bounded` (`:65`, Abel); `hurwitzZeta_apply_zero` (`:579`); and the
> `Salt.BV` completion kit (`Completion.lean:76/134/141/191/237`) with its `2 + log H` L¹ mass.
> **(7.7b) reindexes as `n = b + qm` ⟹ `e(−sb/k)·Σ_m e((−sq/k)m)`, which IS `geom_phase_bound` at
> `θ = −sq/k`** — a reindex plus `dist₁` bookkeeping, plausibly class A/B, **not** the class-C
> `Salt/Weil/Sawtooth.lean` block W5 was priced at.
> **UNVERIFIED**: nobody has checked that `I₀ ⊆ (E,2E]` maps onto a `Finset.Ioc M₁ M₂` without an
> off-by-one. A ~20-line scratch file settles it — **after 20:00**.

### 4d. mathlib census (read from `.lake/packages/mathlib`)
- **Kloosterman sums: ABSENT.** `grep -rl Kloosterman Mathlib` → nothing. The whole `Salt/Weil/`
  tree is corpus-original.
- `gaussSum_sq`: **PRESENT**, `NumberTheory/GaussSum.lean:179`. ⚠️ the freeze cites `:178`
  (`weil-trio-design-0806.md:88`) — **off by one**. And it is moot: `Estermann.lean:167` proves
  `√p` from scratch and says so, so D1's "the one non-elementary input… mathlib supplies it" is
  **no longer the route actually taken**.
- `jacobiSym`, `quadraticChar`, `DirichletCharacter` primitivity/conductor: **PRESENT** and in use.

---

## 5. THE GAP LIST

| # | N7 needs | Supplier | Status |
|---|---|---|---|
| 1 | Estermann (7.1), arbitrary `k,u,v` | W3 + W1-d pair | W1-c/W1-d **[KERNEL, `4a58e51`/`d1a5668`]**, W3 **[DESIGN]** — and see FINDING #1: the pair is weaker than (7.1) at general `k`, bounded only via **W4-a** |
| 2 | sawtooth (7.2)+(7.3)+(7.4) | W5 | **ROW COMPLETE 2026-08-09 12:1x.** (7.2) `sawtooth_fourier_expansion` **[KERNEL]**; (7.4) BOTH arms `norm_majorantCoeff_le` / `…_le_sq` **[KERNEL]**, plus the `L¹` row `tsum_norm_majorantCoeff_le` **[KERNEL]**. ✅ **(7.3) ASSEMBLED at the Captain's click ("assemble (7.3)", 12:0x)** — `sawtoothMajorant_fourier_expansion` + `hasSum_majorantCoeff` (`Salt/Weil/MajorantExpansion.lean`, `e2307cc`, axioms clean ×7 rows, saltbuild EXIT=0 9722 jobs, warnings 190→190, first attempt). No residue. History: was Captain-held one-click since 8/8 16:06 |
| 3 | congruence-restricted completion (7.7b) | W5 (D5's sixth row) | **STALE — [KERNEL], verified 2026-08-08**: `norm_congrExpSum_le` (`Salt/Weil/Sawtooth.lean`, with `…_le_length` and `…_le_dist`), landed **and** carried in `Salt/Weil/All.lean`'s audit roll-call. Was: **[DESIGN] — re-price**; the re-price happened and the row was never updated |
| 4 | gcd-weighted divisor sum (7.7d) + `d(k)³` bookkeeping | W5 depot #2 | **the two sums are [KERNEL] 2026-08-08** — `Salt/Weil/GcdDivisorSum.lean`: `sum_sqrt_gcd_div_le` ((7.7) 2nd line) and `sum_sqrt_gcd_dyadic_le` (the (7.8) intermediate), explicit constants, `[3 axioms]`. The `d(k)³` **bookkeeping** is still open. Was: supplier **nobody**, *[GENUINELY OPEN] — elementary, unpriced, N7's own*; the "elementary" pricing held |
| 5 | additive-character orthogonality mod `k` (7.7a) | corpus | **CONFIRMED PRESENT 2026-08-08, exact form named** — `Salt.BV.sum_e_eq` (`Salt/BV/Completion.lean:76`, "P1 — additive orthogonality"): `∑_{h<H} e(h·r/H) = if (H:ℤ) ∣ r then H else 0`, which is (7.7a)'s detector at `H := k`, `r := n − r`. Already load-bearing: the W5 depot's sixth exit row `norm_congrExpSum_le` is built on it. **The gate was vacuous** |
| 6 | p.217 real-primitive two-forms, composite `q` | W4-c + W4-c′ | **[IN FLIGHT]** `RealPrimitive.lean:381`, **split as a hypothesis** until W4-a lands |
| 7 | p.216 `Σχ(b₂)` vanishing | W4-d | **[IN FLIGHT]** `RealPrimitive.lean:413` |
| 8 | `q = 2^a m`, `a ∈ {0,2,3}` structure | W4-a | **[DESIGN]**, 1,300–2,600 ln — **and on the critical path for FINDING #1** |
| 9 | Λ* positivity (Lemma 1) | corpus | **✅ [KERNEL]** `TwistChain.lean:359/:367` |
| 10 | `q ∣ k` discharge (`q ∣ D`) | W5 depot #3 | **[KERNEL] 2026-08-08** — `Salt/Weil/RoadModulus.lean`: `dvd_roadModulus`, ~~`dvd_roadLevel`~~ **`dvd_roadModulus_mul`** (RENAMED at `588f3b4`, 08-08 20:55, the "three names tightened" pass; the old name CEASES TO EXIST — corrected here 08-11 during N7 pre-flight), hypothesis-free. **The row was MISPRICED**: with `Δ = (α₂,q)`, HB's `D = α₂qΔ^{−1}` **is** `Nat.lcm α₂ q` (`roadModulus_eq_lcm` is `rfl`), so the discharge is `Nat.dvd_lcm_right`. Was: supplier **nobody**, *[GENUINELY OPEN] — HB leaves it implicit; N7 owes it*; the honest class is `A` |
| 11 | (5.14) double-sum recovery; the `:611` residual; `(log Kk)³→(log 2k)³` | the source notes | **ALL THREE CLOSED — verified 2026-08-08, and this row was STALE FROM THE DAY IT WAS WRITTEN.** (i) the (5.14) `w₂` double sum: *"now closed at the source"*, `hb1983-notes.md` correction block dated 2026-08-06 — it was ours, not HB's; (ii) the `:611` residual: **RECLASSIFIED, not merely fixed** — it is *"an ERRATUM IN THE PUBLISHED PAPER, not a transcription error"* (HB prints `x^{1/4}`; three independent terms of his own next display each force `θ = 1/2`, re-derived here); (iii) `(log Kk)³→(log 2k)³`: corrected 2026-08-06 and **independently re-derived 2026-08-08** while landing the (7.8) fold. Was: supplier **nobody**, *[GENUINELY OPEN] — §2's three transcription defects* |

---

## 6. SCALE — ESTIMATE, NOT A PRICED BRIEF

Calibrated against the corpus's nearest analogue: HB Lemma 7 (§4, ~3.5 journal pages, comparable
Euler-product/L-function density) came to **6,489 ln** across `Salt/HB/Lemma7*.lean`.

| Block | Content | Estimate |
|---|---|---|
| §5 (Lemmas 9, 11; (5.1)–(5.19)) | CRT gymnastics, the four-congruence collapse to (5.11) | 3,000–6,000 ln |
| **§6 ((6.1)–(6.16), pp.215–221)** | **the leading-term evaluation — almost NO Kloosterman content** | **4,000–9,000 ln, class C throughout** |
| §7 beyond WEIL-TRIO's supplies | (7.5)–(7.8) assembly, the `K` balance | 1,500–3,000 ln |
| **N7 total** | | **9,000–18,000 ln** |

**§6 is the expensive part, and it is not Lemma 10.** It splits `S(δ₁,δ₂;V₁,V₂)` into three
regimes: (a) `S_i ≤ R_i` both — the main term, Lemma 11, consuming (1.9) + `q` cube-free;
(b) `S₁ ≤ R₁ < S₂` — killed by **primitivity** (→ W4-d, in flight); (c) `S_i > R_i` both — killed
by the **real-primitive two-forms bound** (→ W4-c, in flight, under the W4-a hypothesis). Then
(6.9)–(6.11) assemble with the window edge `x ≥ q^{250}`, and (6.12)–(6.16) + pp.218–221 are the
hard block: `S(d;t)` rearrangement, `M(r)→N(r)` (whose error **is Lemma 5's stated error**), the
Dirichlet-series tail, `f(u,v) = l₁^u l₂^v F(u,v)G(u,v)` as an **Euler product**, **two-variable
logarithmic differentiation** at `(0,0)` yielding `L′/L`, and the `σ→1` limit.
Reusable patterns already in the corpus: `Salt/HB/Lemma7Prod.lean`'s ordered-partial-product
construction (`hbEulerLog`/`hbEulerProd`/`hbLogF` — chosen precisely because `Multipliable` fails
for conditionally convergent Euler products) and `TwistedMertens.lean:136`
(`logDeriv_LFunction_eq_LSeries`).

---

## 7. WHAT THIS DOSSIER RECOMMENDS

1. **Amend §3's exit table and W3's brief** to state the `2^{v₂(k)/2}` gap and that **W4-a is on
   the critical path for the 2-adic constant**, not only for the p.217 lift. Fix D2's
   `v₂(k) ≤ v₂(α₂)+3` to `max(2, v₂(q)) ≤ 3`.
2. **Re-price W5 downward** against `Salt/MR/{Sawtooth,MinorArcVaughan}.lean` and `Salt/BV/
   Completion.lean` before writing a fresh class-C block — after a ~20-line off-by-one check.
3. ~~WEIL-TRIO seat: commit the `All.lean` roll-call row~~ — **already done at `4a58e51`, mid-run.**
   Standing lesson only: **a roll-call row belongs in the same commit as the file it names**, or a
   declaration is committed and outside the build closure at once.
4. **Settle the `:611` residual at HB p.214** — one look; it is N7's gate on (5.19).
5. **Do not open N7 as one wave.** At 9,000–18,000 ln it wants the §5 / §6 / §7 split, with §6
   further split at (6.12), and §6's Euler-product block scouted on its own before pricing.
6. Correct the freeze's `gaussSum_sq` line cite (`:178` → `:179`) and drop the "mathlib supplies
   the non-elementary input" framing — `Estermann.lean` proves it from scratch.

**NOT VERIFIED IN THIS DOSSIER** (stated so nobody reads past it): no Lean was run, so every
"[KERNEL]" row is *bytes-say-so*, not kernel-checked; the §6 line estimate is an analogy to
Lemma 7, not a priced brief; FINDING #3's reduction of (7.7b) to `geom_phase_bound` is a shape
match, not a proof.

---

# ADDENDUM A (2026-08-06) — §7 VERIFIED AGAINST THE SOURCE, pp.221–223

**Why:** §1 of this dossier mapped §7 from `hb1983-notes.md`, a *transcription*. Hours later the
same transcription's §5 was found to sit on **two errata in one printed sentence** of the paper
(`b25d8aa`). The block N7 must formalize therefore deserved a direct read. The PDF is staged at
`~/Downloads/Proceedings of London Math Soc - September 1983 - Heath-Brown - Prime Twins and
Siegel Zeros.pdf`. Read-only, no Lean.

## A.1 — WHAT VERIFIED CLEAN ✅

`(7.1)`, `(7.2)`, `(7.3)` (with its `K ≥ 2`), `(7.4)`, `(7.5)`, `(7.6)` and `(7.7)` all match
`hb1983-notes.md` as transcribed. Also confirmed at the source:

- **§7 cites exactly one external result.** "This will then be tackled using **Estermann's bound
  [6]** for the Kloosterman sum" — and the reference list gives **[6] T. Estermann, 'On
  Kloosterman's sum', *Mathematika* 8 (1961) 83–86**, exactly as this dossier recorded. The
  "only one thing from outside HB" headline is confirmed **at the paper**, not just at the notes.
- **`K = 2 + k^{1/4}`** is the printed choice ("We choose `K = 2 + k^{1/4}`, and Lemma 10
  follows"), and the `K ≥ 2` of (7.3) is what forces the `2 +`.
- **(7.6)'s `I₀` is "a certain subinterval of `I`"** — a genuine interval, not an arbitrary set.
  This matters for §4 FINDING #3 (see A.3).
- The final display on p.223 carries **`d³(k)(log Kk)³`**, confirming the `(log Kk)³` vs
  `(log 2k)³` conversion this dossier flagged as owed by N7.

## A.2 — 🟡 THE NOTES OMIT AN INTERMEDIATE STEP, AND IT IS THE ONE THAT INTRODUCES `k₀`

Between (7.7) and (7.8) the paper has a line the notes do not carry:

> "On comparing estimates, we see that (7.6) yields
> `S_m ≪ (1+m|T|E^{−1}k^{−1})·d(k)²·q^{3/2}·(log 2k₀)·{E(k₀,m)^{1/2} + k₀}·k^{−1/2}`
> **since `(C,k₀) = 1`**."

Two things N7 needs that are invisible in the notes: the `d(k)²` intermediate (it becomes `d(k)³`
only after the `Σ_{M<m≤2M}(k₀,m)^{1/2} ≪ M·d(k₀)` step), and the **explicit use of `(C,k₀) = 1`**,
which is a *hypothesis of Lemma 10* (`(C,k) = 1`) being spent here via `k₀ ∣ k`. Add both to the
formalization plan.

**⚠️ AND ONE EXPONENT I COULD NOT SETTLE FROM THE PAGE IMAGE — ✅ NOW SETTLED, BY DERIVATION.**
The notes transcribed (7.8) with `(log 2k)³`; **it is `(log 2k)` to the FIRST power.** Rather than
squint at the rendering I re-derived it from the intermediate step recovered above: summing
`S_m ≪ (1+m|T|E^{−1}k^{−1})d(k)²q^{3/2}(log 2k₀){E(k₀,m)^{1/2}+k₀}k^{−1/2}` over `M < m ≤ 2M` with
`Σ(k₀,m)^{1/2} ≪ M·d(k₀)` gives
`(1+M|T|E^{−1}k^{−1})·d(k)²·q^{3/2}·(log 2k₀)·k^{−1/2}·M{E·d(k₀)+k₀}`; folding `d(k₀) ≤ d(k)`
(valid since `k₀ ∣ k`) produces **`d(k)³`** and `{E+k}` — and **exactly one log survives**. The
cube arrives only at p.223, where the (7.2)–(7.4) truncation contributes `log K` and the dyadic
`m`-summation another, giving `d³(k)(log Kk)³`.
**CONSEQUENCE FOR THE FREEZE — reassuring.** Its rule that Lean statements carry `d(k)³(log 2k)³`
literally is **correct for Lemma 10** (p.223's `(log Kk)³` with `K = 2 + k^{1/4}`, so
`log(Kk) ≍ log k`); only the *intermediate* (7.8) was over-stated in our notes, and stating (7.8)
at `(log 2k)³` would be provable-but-blunt, **not false**. Fixed in the notes at the (7.8) block.

## A.3 — ⭐ THE SOURCE STRENGTHENS FINDING #3 (the W5 re-price), AND NAMES ITS EDGE CASE

The completion step reads, at the paper:

> `Σ'_{n∈I₀} g(n) = (1/k) Σ_{s=1}^{k} S(k;s,Cm) · Σ_{n∈I₀, q∣n−b} e(−sn/k)`,
> with `Σ_{n∈I₀, q∣n−b} e(−sn/k) ≪ Min(E, ‖sq/k‖^{−1})`.

Since `k = q·k₀`, the phase is `sq/k = s/k₀`. So **the `E` branch of that `Min` is exactly the
case `‖s/k₀‖ = 0`, i.e. `k₀ ∣ s`** — which is why HB's next line splits off `E(k₀,Cm)^{1/2}` from
the `s`-sum. That is precisely the junk-value edge the statement audit worried about
(`weil-trio-audit-0806.md` §3, the `1/‖0‖ = ∞` case), and **the corpus already handles it in the
right shape**: `Salt.MR.minTerm` (`MinorArcVaughan.lean:271`) is
`if t = 0 then Y else min Y (1/(2t))`, carrying the vanishing-distance case honestly rather than
by a junk value, and `Salt.MR.geom_phase_bound` (`:298`) delivers exactly
`‖Σ_{M₁<m≤M₂} e(θm)‖ ≤ minTerm (M₂−M₁) (dist₁ θ 0)`.

Combined with A.1's confirmation that `I₀` is a genuine **subinterval**, the reindex `n = b + qm`
maps it onto a `Finset.Ioc` cleanly. **This raises confidence in the W5 re-price from "shape
match" to "shape match with the edge case named and already served"** — but it is still not a
proof, and the off-by-one check remains owed (queued for after 20:00).

## A.4 — WHAT THIS ADDENDUM DOES NOT CHANGE

The consumption map (§1), the supply map (§3), the gap list (§5) and the scale estimate (§6)
stand as written. The `j = e` vacuity constraint of `weil-trio-audit-0806.md` §2 is untouched and
still owed by N7.

---

# ADDENDUM B (2026-08-06) — §6 VERIFIED AGAINST THE SOURCE, pp.215–221

**Why:** §6 is the bulk of N7 by this dossier's own estimate (4,000–9,000 ln, class C) and had
**never been read at the source** — only through `hb1983-notes.md`. After the source produced two
HB errata and one of ours in §5/§7, that gap was the largest remaining. Read-only, no Lean.

## B.1 — VERIFIED CLEAN, and three of them settle open questions ✅

- **p.217 — HB EXPLICITLY OMITS THE TWO-FORMS PROOF.** Verbatim: *"However, for a real,
  primitive, character `χ (mod q)`, one has `Σ_{t=1}^{q} χ(ut+u')χ(vt+v') ≪ (q, uv'−vu')`.
  **(The proof of this is straightforward. We shall omit it.)**"* This confirms at the source what
  the road table asserted — the second character-sum input is stated without proof and must be
  supplied. **WEIL-TRIO's W4-c has now landed it at constant ONE, which is strictly sharper than
  HB's `≪`.**
- **⭐ THE `Δ^{−1}` IS REAL, AND W4-c′ IS NECESSARY — confirmed at the source.** This dossier §3
  predicted that "p.217 is consumed at length `q/Δ`, not `q`". p.217 shows exactly that: the sum
  HB actually needs is `|Σ_{t=1}^{q/Δ} χ(Δγ₁t+β₁)χ(Δγ₂t+β₂)|`, and he concludes
  `Σ ≪ Δ^{−1}(q, Δγ₁β₂ − Δγ₂β₁) ≪ Δ^{−1}(q, Δα^{−1}(α₁β₂−α₂β₁)) ≪ 1`. **The prediction was
  right**, and D4's addition of W4-c′ (the Δ-fold periodicity descent) is load-bearing, not
  optional. Note the final `≪ 1` also spends **(1.6)** (`α₁β₂ − α₂β₁ ≠ 0`), exactly as the freeze's
  supply table records.
- **p.216 — regime (b) is killed by primitivity.** *"b₂ runs over a congruence class (mod dΔ).
  Since χ is primitive, this last sum vanishes unless `dΔ = q`."* Matches W4-d's landed
  `sum_class_eq_zero_of_isPrimitive` (proper divisor ⟹ the class sum vanishes).
- **p.218 — the window edge is `x ≥ q^{250}`**, spent exactly where the notes say: the (6.9) error
  terms contribute `≪ x^{1+ε}q^{−1} + x^{15/16+3ε}q^{14} ≪ x^{1+ε}q^{−1}` (6.11) *"since
  `δ₁δ₂ ≤ q⁴d²` and `x ≥ q^{250}`"*.
- **p.219 — (6.15) `S(d;t) − S'(d;t) ≪ L⁴z^{−1}d^{−1}4^{ω(d)}` IS Lemma 5's stated error**, as the
  notes record. The `M(r) → N(r)` replacement is where it arises.
- **p.218 — (6.10) is PV-free**, as recorded: `Σ_{w∈I,(w,f)=1} χ(w) = Σ_{g∣f} μ(g)Σ_{w∈I, g∣w} χ(w)
  ≪ q·d(f)`, *"since `|Σχ(w)| ≤ q` when `w` runs over any interval"* — the trivial complete-sum
  bound, no Pólya–Vinogradov needed.

## B.2 — ⚠️ ONE TRANSCRIPTION DEFECT, AND IT WOULD PRODUCE AN UNPROVABLE LEMMA

`hb1983-notes.md:776` had the `C_i` bounded *"`≪ 1` uniformly in q, t, σ"*. **HB's p.220 continues:
"but not necessarily in `α`."** The full sentence is:

> *"`C_i` denotes a continuous function of `σ` (`σ ≥ 1`), depending on `i, q, χ, t` and `α`, but not
> on `d`, for which `C_i ≪ 1` uniformly in `q`, `t`, and `σ`, **but not necessarily in `α`**."*

**A Lean statement asserting `C_i ≪ 1` uniformly in `α` would be FALSE**, so an executor working
from the notes alone could spend a wave on an unprovable lemma. This is the sp1-lean failure mode
one level upstream — in a *transcription* rather than a statement. **Moot for twin primes**, where
`α₁ = α₂ = 4` is fixed, but it must be *stated*, not silently relied on. HB separates two facts and
both matter: "independent of `d`" (which the argument uses, `d` being the summation variable) and
"not uniform in `α`" (which it survives only because `α` is fixed). Fixed in the notes with a
`[corrected 2026-08-06, from the source p.220]` block.

## B.3 — §6 RE-PRICED, AND IT IS BETTER NEWS THAN §6 SOUNDED

The phrase "two-variable logarithmic differentiation of an Euler product" was doing a lot of
frightening work in this dossier's §6 estimate. At the source (p.220) the differentiation rests on
**exactly two formulae**, and both are *generic statements about products*, not about this Euler
product:

```
    ∂/∂u  ∏_m a^{(m)}(u,v) = {∏_m a^{(m)}}·{Σ_m a_u^{(m)}/a^{(m)}}
    ∂²/∂u∂v ∏_m a^{(m)}(u,v) = {∏ a^{(m)}}·{(∂_u ∏ a)(∂_v ∏ a) + Σ_m (a_uv^{(m)}/a^{(m)} − a_u^{(m)}a_v^{(m)}/(a^{(m)})²)}
```

So the hard analytic core is **one reusable lemma pair proved once**, then applied to `F(u,v)` and
`G(u,v)` whose factors are explicit finite rational expressions in `p^{−σ−u}`, `p^{−σ−v}`,
`p^{−2σ−u−v}`. That is materially cheaper than "differentiate an Euler product in two variables"
implies, and the corpus already has the ordered-partial-product machinery
(`Salt/HB/Lemma7Prod.lean`) for the convergence side.
**I am NOT revising the 4,000–9,000 ln estimate downward on this alone** — the three regime splits,
(6.12)–(6.16), the `M(r)→N(r)` replacement and the `σ→1` limit are all still there — but the single
scariest sub-block is smaller than it looked, and a §6 executor should be pointed at these two
formulae first.

## B.4 — WHERE `κ` COMES FROM (for the N5/N6 consumer wiring)

p.221, last line of §6: *"On taking `σ → 1` we have `MF(0,0) → κx^{−1}`, `G(0,0) → G(d)`. Lemma 5
now follows on integrating over `t`, since the integral of `A₃(d)` is also an additive function of
`d`."* So `κ` is **defined by that limit**, not by an independent formula — worth knowing for
anyone reconciling `Salt/HB/Lemma7Kappa.lean`'s `hbKappa` against the paper.

---

# ADDENDUM C (2026-08-06) — §5's OPENING VERIFIED, pp.210–211: **CLEAN**

Read-only, no Lean. Continues the source-verification sweep (§7 = ADDENDUM A, §6 = ADDENDUM B).

**RESULT: no defects.** Every item in `hb1983-notes.md`'s §5 opening matches the paper:

- the `Λ*` μ-sieve expansion and its truncation at `m < q`, with error
  `O(d(n)(log n)·#{m : m²∣n, m ≥ q})` — matches p.210;
- the truncation error in `S(d)`, `≪ Σ_{m≥q} x^{1+ε}m^{−2} ≪ x^{1+ε}q^{−1}` — matches p.210;
- **Lemma 9** (`d ∣ P`; the double `dV_i/V_i` integral over `S(m₁²d₁j₁, m₂²d₂j₂; V₁,V₂)` with
  `O(x^{1+ε}q^{−1})`) — matches p.211 term for term;
- **(5.1)** `(δ_i,q) = (δ_i,α) = (δ₁,δ₂) = 1` — matches;
- **(5.3)** `Σ_{R_i,S_i} Σ_{a_i,b_i=1}^{q} χ(b₁b₂)S` with `(q, a_ib_i) = 1`, and the definition of
  `S` as the four-condition lattice count — matches.

**⭐ AND (5.2) IS VERBATIM AT THE SOURCE**, which independently re-confirms the p.214 erratum:

> *"Since `x ≪ l_i ≪ x` we may assume that `R_i ≥ V_i`, `S_i ≫ 1`, `x ≪ δ_i R_i S_i ≪ x`."* (5.2)

From this alone, `S₁ ≤ R₁` gives `S₁² ≤ R₁S₁ ≍ x/δ₁ ≤ x`, hence **`S₁ ≪ x^{1/2}`** — the exponent
HB's p.214 prints as `x^{1/4}`. So the erratum is now established **twice over and independently**:
once from HB's own substituted display (ADDENDUM A / `b25d8aa`), once from (5.2) read directly.

**Scope note.** Lemma 5's *statement* lives in §2 (pp.197–204), not here; §5 opens with "we show how
the proof of Lemma 5 may be made to depend on the estimation of some simpler sums". Verifying the
statement itself remains the last unchecked block, and it is the one N7 must render in Lean.

**Running tally after four blocks** (§5-opening, §5-body, §6, §7): the source has corrected **HB
twice** (both the `:611` exponent pair) and corrected **our transcription three times** (the dropped
`w₂` index in (5.14); the dropped "not necessarily in `α`" on the `C_i`; the over-stated log power
in (7.8)). **We remain the less reliable party.** This block breaks the streak of "every block
yields a defect" — reported as prominently as the defects were.

---

# ADDENDUM D (2026-08-06) — LEMMA 5's STATEMENT VERIFIED, p.199: **CLEAN**

The last unverified block, and the most expensive place for a defect: this is the theorem N7 must
render in Lean. Read-only, no Lean.

**RESULT: `hb1983-notes.md:216-240` matches the source.** Verified item by item:

- **Hypotheses `d ∣ P`, `(d,α) = 1`, `d, z ≤ q^{1/3}`** — match. The `q^{1/3}` bound is carried,
  and it is not decorative: p.199 takes `z ≤ q^{1/3}`, `D = q^{1/3}` so the errors contribute
  `≪ xL⁴z^{−1}Σ_{d≤D}d^{−1}4^{ω(d)} ≪ xL⁸z^{−1}` (2.3).
- **Conclusion** `S(d) = κ(G(d)/d){(L′(1,χ)/L(1,χ))² + A²(d) + A′(d) + C₀} + O(xL⁴z^{−1}d^{−1}4^{ω(d)})`
  — matches.
- **`G(d) = 2^{ω(d)}∏_{p∣d}(2p−1)/(p+1)`** — matches, and independently confirms
  `Salt/HB/Lemma7Kappa.lean:86`'s `hbG`, which the W4.5 flag cites as "HB p.199's `G(d)`".
- **`A(p) ≪ log p`, `A′(p) ≪ B log p` with `B = L + |L′(1,χ)/L(1,χ)|`, `C₀` independent of `d`,
  `C₀ ≪ BL`** — all match.
- **`G(p) ≤ 4` and the dimension-4 sieve** — p.200 states *"As `G(p) ≤ 4` we need a sieve of
  dimension 4 here"*, confirming `hbG_le_four` and the N5 gate check's CHECK 3 at the source.
- **The `β ≥ 3` sieving-limit fact** — p.199: *"To obtain the bound `δ ≤ q` we need the fact that
  the sieving limit satisfies `β ≥ 3` for the case of dimension 4."* Confirms the N5 gate check's
  CHECK 1 (that `β ≥ 3` is spent only on support bookkeeping) at the source.

**⭐ ONE RECONCILIATION WORTH RECORDING.** Lemma 5's error is `O(x·L⁴z^{−1}d^{−1}4^{ω(d)})` while
(6.15) is `S(d;t) − S′(d;t) ≪ L⁴z^{−1}d^{−1}4^{ω(d)}` — **no `x`**. These are consistent, not a
discrepancy: (6.15) lives at the `S(d;t)` level and Lemma 5 is reached through
`M∫_x^{2x} S(d;t)dt`, so the `x` is the length of the `t`-integration range. A formalizer comparing
the two statements side by side would otherwise see a missing factor and go looking for a defect
that is not there.

**⚠️ ONE HONEST LIMIT — `κ` WAS NOT VERIFIED TO BYTE PRECISION.** `κ`'s four-product formula is a
dense single line of small type and my page rendering is not sharp enough to certify each factor's
subscript (`p ∣ q, p∤α` / `p ∣ α` / `p∤α, χ(p)=1` / `p∤α, χ(p)=−1`) and exponent individually. The
**structure** matches the notes — four products, in that order, with those factor shapes — and
nothing above depends on `κ`'s internals. But `Salt/HB/Lemma7Kappa.lean:348`'s `hbKappa` **does**,
and W4.5 built it from Lemma 5. **Recommend one careful re-read of p.199's `κ` against `hbKappa`
by whoever owns `Lemma7Kappa`** — it is a five-minute check against a definition already in the
kernel, and it is the one place in this sweep where I am reporting "structure matches" rather than
"verified".

**FINAL TALLY FOR THE SOURCE-VERIFICATION SWEEP** (Lemma 5 statement, §5-opening, §5-body, §6, §7):
**HB corrected twice** (the `S₁`/`S₂` exponent pair at p.214, one erratum in two places);
**our transcription corrected three times** (the dropped `w₂` index in (5.14); the dropped "not
necessarily in `α`" on the `C_i`; the over-stated log power in (7.8)). Two blocks clean.
**We were the less reliable party, by half again.**

## ADDENDUM D.1 — `κ`'s LEAN RENDERING CROSS-CHECKED (what I *could* settle)

I cannot certify `κ` against the print, but I can check our **two internal records against each
other**, and I can attack the definition's branch structure. Both done:

**(i) `hbKappa` and the notes agree exactly.** `Salt/HB/Lemma7Kappa.lean:348` *(corrected — I
first wrote `:346`, which is the docstring's κ display, not the `def`; the maestro caught it in
D.3)* carries κ's
four-product form in its docstring verbatim as `hb1983-notes.md:225-226` has it, and the Lean body
matches that docstring term for term:
`x * L1^2 * ∏_{p ∈ q.primeFactors, p ∤ α}(1 − 2/p) * ∏_{p ∈ α.primeFactors}(1 − χ_ℝ(p)/p)^2 *
hbKappaTail`, with `hbKappaTail = ∏'_{p > 2} hbWfac χ α p` documented as HB's two infinite products.

**(ii) THE PARTITION IS CORRECT — I attacked it and it held.** HB's two tail products run over
`p ∤ α` split by `χ(p) = ±1`; primes with `χ(p) = 0` (i.e. `p ∣ q`) belong to the **first, finite**
product instead. So the tail factor must return `1` on them or those primes are **counted twice**.
`hbSfac` (`:132`) is a three-way split — `χ_ℝ(p) = 1 ↦ (1−1/p²)`, `χ_ℝ(p) = −1 ↦ (1−2/p)(1+1/p)²`,
**`else ↦ 1`** — so the `χ(p) = 0` primes contribute exactly `1`, and `hbWfac` (`:139`) returns `1`
on `p ∣ α`. **No double-counting; both `p ∣ α` and `χ(p) = 0` are handled, and the `else ↦ 1` is
load-bearing rather than a junk default** (the file says as much at `:34`).

**⚠️ WHAT THIS DOES AND DOES NOT BUY.** It rules out an *internal* inconsistency and the obvious
partition bug. It does **not** verify `κ` against p.199 — and because `hbKappa` reproduces the
notes exactly, **any mis-transcription in the notes is inherited by the kernel definition
verbatim**. So the risk is not eliminated, it is **localised to a single line of small type**, and
one careful read of p.199 by anyone with a cleaner copy discharges it for both records at once.
That is a sharper ask than "someone check κ", and it is the last open item from this sweep.

### D.2 — the PDF text-layer route: **tried, and it cannot settle `κ`**

Recorded as a negative result so nobody repeats it. The staged PDF *does* carry a text layer
(`pdftotext -layout`, p.199 extracts ~3.3 KB), and it is **useful for prose but destroys displayed
mathematics** — this is a scan with weak formula OCR.

**What it DOES confirm** (independently of my page-image read, which is worth having):
`"LEMMA 5. Let d\P, (d,oc) = 1, and d,z ^ qil3"` → the hypotheses `d ∣ P`, `(d,α) = 1`,
**`d, z ≤ q^{1/3}`**; `"A(p) « log p, >4'(p) « £ log p (B = L + …)"` → the additive bounds;
`"Co is independent of d and satisfies Co « BL"` → verbatim; `"We take z ^ ql/3, D = q1'3"` → the
(2.3) parameter choice.

**What it does NOT recover: `κ`'s factors.** The display degrades to fragments. The *subscripts*
partially survive and are **consistent with the notes' four-product split** — `P[q\ / Plot`
(= `∏_{p∣q, p∤α}`), `Pi*` (= `∏_{p∣α}`), `x<p)'=` and `X(P?=-I` (= the `χ(p)=1` and `χ(p)=−1`
products) — which is weak corroboration of the *structure* only. **Every factor
(`1−2/p`, `(1−χ(p)/p)²`, `1−1/p²`, `(1−2/p)(1+1/p)²`) and every exponent is lost.**

**So the `κ` ask stands unchanged and cannot be closed by tooling available here**: it needs a
cleaner copy or human eyes on one line of p.199. Both cheap routes — page image and text layer —
are now exhausted and documented.

## ADDENDUM D.3 (2026-08-06, maestro) — κ VERIFIED AT THE PRINT; THE SWEEP'S LAST GAP CLOSES

The maestro's own page-image read of the staged PDF (p.199 = PDF page 7) resolved the display
at full resolution: every subscript and every exponent of κ's four products is individually
legible. Against `hbKappa` (`Salt/HB/Lemma7Kappa.lean:348`):

1. `∏_{p|q, p∤α}(1−2/p)` — stacked subscript `p|q` over `p∤α`, exactly as rendered. **VERIFIED.**
2. `∏_{p|α}(1−χ(p)/p)²` — square OUTSIDE the parenthesis. **VERIFIED.**
3. `∏_{p∤α, χ(p)=1}(1−1/p²)` — square on `p` inside, no outer exponent. **VERIFIED.**
4. `∏_{p∤α, χ(p)=−1}(1−2/p)(1+1/p)²` — square on the `(1+1/p)` factor only. **VERIFIED.**

Prefactor `xL(1,χ)²` matches `x * L1^2`. With D.1's internal cross-check (rendering vs. notes),
`hbKappa` is now certified against the source. The five-block sweep carries **zero** remaining
"structure matches" rows — everything is "verified".

Line-number reconciliation (the evidence seat's 11:52 flag): `hbKappa` is at **:348**
(`hbKappaTail` at :339); the 11:51 post's `:346` was the stale number.

Method note for the record: ADDENDUM D.2's negative on the text layer stands — this read used
the page image, which at full page resolution IS sharp enough for the subscripts. The earlier
"not sharp enough" verdict was a property of the earlier render, not of the scan.
