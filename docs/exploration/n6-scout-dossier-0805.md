# N6-SCOUT — THE MORNING-DESIGN DOSSIER
## "the Weil-delta trio" off the banked Weil bank
### READ-ONLY scout, salt @ main (working tree untouched). 2026-08-05.

---

## 0. HEADLINE (five findings, in order of design impact)

1. **The p.217 bound is ALREADY LANDED at the prime case — and it landed in the
   CORRECTED form, not the dropped-`v` form.** `Salt.HB.quadraticChar_sum_two_forms_bound`
   (`/Users/jyh/projects/claude/salt/Salt/HB/QuadCharSum.lean:137`) proves
   `|∑ t, χ(a·t+b)·χ(c·t+d)| ≤ 2` under `a*d − b*c ≠ 0` — i.e. exactly
   `Σ_t χ(ut+u′)χ(vt+v′)` with determinant `uv′ − vu′`. The HB-STAGE erratum
   (`fulcrum_audit_source.md:185`, item 1) is a **document defect only**; the kernel
   never carried the bad form. N6 should quote the Lean statement, not the audit doc.
2. **Delta (ii) of the recorded trio is MIS-SCOPED, and it is the expensive kind of
   mis-scope.** The recorded delta says the Kloosterman modulus is cube-free (so
   only `k=1,2` prime-power cases are needed). At the bytes, Lemma 10 is applied with
   modulus `k = D·δ₁·w₁` where `w₁` is a **free summation variable** over a dyadic
   interval (`hb1983-notes.md:605-606`). `k` is an arbitrary integer. Cube-freeness is
   a fact about `q`, the *character* modulus, consumed in the §5/§6 CRT gymnastics
   (`hb1983-notes.md:566-567`, `:646-647`) — a different object entirely. **N6 needs
   Estermann at an arbitrary modulus**, all odd exponents and the 2-adic branch included.
3. **The gcd factor `(k,u,v)^{1/2}` is not a refinement — it carries the whole `s`-sum.**
   The completion at (7.7) (`hb1983-notes.md:762-763`) produces `S(k; s, Cm)` summed over
   `1 ≤ s ≤ k₀`, i.e. over **non-units**, and the surviving term is literally
   `Σ_s k₀(k₀,s)^{1/2}s^{-1} ≪ d(k₀)log 2k₀`. Every composite bound in the bank
   (`norm_kloosterman_le_tau_sqrt`, `norm_kloosterman_prime_pow_*`) carries `IsUnit a`.
   There is **no non-unit branch in the bank at all** except the trivial `≤ c`.
4. **"q cube-free" is literally false at `q = 8`** (χ₈ is real primitive mod 8 = 2³).
   The house already ruled the right replacement, in a doc nobody has cited since:
   `fulcrum-pass1.md:57` — *"Conductor shape consumed at (α_i, q/Δ)=1 steps via (1.9)
   — land as the structural lemma (a ∈ {0,2,3}), NOT cube-freeness."* That ruling is
   correct (`v₂(q) ∈ {0,2,3}`, odd part squarefree) and should govern N6/N7.
5. **The p.216 `Σχ(b₂)` vanishing is NOT landed anywhere**, and the composite lift of
   p.217 is NOT landed. Both need a real-primitive-χ structure theorem that
   **mathlib does not have** (χ₄/χ₈/χ₈′ exist in `LegendreSymbol/ZModChar.lean`;
   there is no fundamental-discriminant classification — grep for
   `FundamentalDiscriminant` over `Mathlib/` returns nothing).

---

## 1. THE WEIL BANK — MAP

**5,687 ln confirmed exactly**: `wc -l Salt/Weil/*.lean` = 5687 total, 23 files,
187 top-level declarations, 60 names audited at 3 axioms via
`#audit_axioms` in `/Users/jyh/projects/claude/salt/Salt/Weil/All.lean:36-96`.
Wired into the root at `Salt.lean:14`. Sorry-free (grep clean).

### 1a. The INTERFACE layer — what N6/N7 may quote today

The object (`Salt/Weil/Kloosterman.lean:49`):
```
noncomputable def kloosterman (a b : ZMod p) : ℂ :=
  ∑ t : (ZMod p)ˣ, ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p))
```
Note `[NeZero p]` only — the name says `p` but the modulus is a **general natural**.
Good: no re-definition needed for composite work.

| # | Export | Exact statement (abridged to hypotheses + conclusion) | File:line |
|---|---|---|---|
| K1 | `norm_kloosterman_le` | `‖S(a,b;c)‖ ≤ #(ZMod c)ˣ` | Kloosterman.lean:54 |
| K2 | `norm_kloosterman_le_sub_one` | prime `p`: `‖S‖ ≤ p−1` | Kloosterman.lean:61 |
| K3 | `kloosterman_comm` | `S(a,b) = S(b,a)` | Kloosterman.lean:68 |
| K4 | `kloosterman_conj` / `kloosterman_im` | `S` is real | Kloosterman.lean:79 / :97 |
| K5 | `kloosterman_reindex_units` | `S(a·c, b·c⁻¹) = S(a,b)`, `c` a unit | Kloosterman.lean:103 |
| **W** | **`norm_kloosterman_le_two_sqrt`** | `[Fact p.Prime] (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) : ‖S(a,b;p)‖ ≤ 2√p` — **THE WEIL BOUND**, registry row `docs/RESULTS.md:173` | Descent.lean:206 |
| W′ | `norm_kloosterman_le_two_sqrt'` | same, `p = 2` folded in | Descent.lean:222 |
| P1 | `norm_kloosterman_prime_unit` | any prime `p`, `IsUnit a`, **any `b` incl. 0**: `‖S‖ ≤ 2√p` | CompositeFull.lean:351 |
| P2 | `kloosterman_zero_right` | `IsUnit a ⟹ S(a,0;p) = −1` (Ramanujan) | CompositeFull.lean:309 |
| P3 | `norm_kloosterman_prime_pow_even` | odd `p`, `m ≥ 1`, `IsUnit a`: `‖S(a,b;p^{2m})‖ ≤ 2p^m` | PrimePower.lean:228 |
| P4 | **`norm_kloosterman_prime_pow_ge_two`** | odd `p`, `k ≤ 2j`, `j+1 ≤ k`, `IsUnit a`: `‖S(a,b;p^k)‖ ≤ 2·p^j` | CompositeFull.lean:230 |
| P5 | `norm_kloosterman_prime_pow_odd` | odd `p`, `m ≥ 1`, `IsUnit a`: `‖S(a,b;p^{2m+1})‖ ≤ 2p^{m+1}` — **crude, √p above sharp** | CompositeFull.lean:299 |
| P6 | `norm_kloosterman_two_pow` | `‖S(a,b;2^k)‖ ≤ 2^k` — **trivial placeholder**, docstring says so | CompositeTail.lean:73 |
| P7 | `norm_kloosterman_le_modulus` | `‖S(a,b;c)‖ ≤ c` | CompositeTail.lean:65 |
| C1 | `kloosterman_mul_of_coprime` | CRT factorization with explicit twists `l₁,l₂` | Composite.lean:107 |
| C2 | `norm_kloosterman_mul_of_coprime` | `∃ a₁b₁a₂b₂, ‖S(a,b)‖ = ‖S(a₁,b₁)‖·‖S(a₂,b₂)‖` | Composite.lean:178 |
| C3 | `norm_kloosterman_le_mul_of_coprime` | **unit-free** product bound from uniform per-factor bounds | Composite.lean:190 |
| C4 | `exists_split_stdAddChar_unit` | the CRT split constants `l₁,l₂` are **units** | CompositeTail.lean:94 |
| C5 | `norm_kloosterman_le_mul_of_coprime_unit` | unit-threaded product bound | CompositeTail.lean:224 |
| **T** | **`norm_kloosterman_le_tau_sqrt`** | `(hc : Squarefree c) (ha : IsUnit a) : ‖S(a,b;c)‖ ≤ τ(c)·√c` | CompositeFull.lean:384 |
| **I** | **`norm_incomplete_kloosterman_le`** | prime `p`, `b ≠ 0`, `Z ≤ p`: `‖∑_{t unit, val t ≤ Z} ψ(at+bt⁻¹)‖ ≤ 2√p(2+log p)` — HB-F-COMP | Incomplete.lean:181 |

The `T` docstring records its own gap verbatim (CompositeFull.lean:373-383):
> *"For a general (non-squarefree) modulus the composite bound is the product of the
> per-prime-power estimates `2·p^{⌈k/2⌉}` … which the sharp `τ(c)√c` needs the odd-`k`
> Gauss-sum `√p` to recover (**the recorded honest gap**; here `k = 1` throughout, so no gap)."*

### 1b. The ENGINE layer (not interface — do not re-open)

Stepanov ladder producing `W`: `weil_stepanov` (WeilStepanov.lean:77) → `PointCount`,
`StepanovCore/Solve/Stepanov`, `ArtinSchreier`, `Orbits`, `LocalFactor`, `LFunction`,
`Moments`, `MomentOrbit`, `MomentEigen`, `NewtonBridge`, `CurveBridge`, `MultiExtract`,
`Descent`. ~4,000 of the 5,687 ln. N6 consumes `W`/`W′` as a black box.

### 1c. Adjacent supply outside `Salt/Weil/`

- `Salt.HB.quadraticChar_sum_*` — `Salt/HB/QuadCharSum.lean` (244 ln, landed
  `09c2522`, 2026-07-17; audited `Salt/HB/All.lean:98-100`).
- `Salt.BV.fourierCutoff` + `fourierCutoff_indicator` + `norm_fourierCutoff_le` +
  `sum_norm_fourierCutoff_le` + `sum_e_eq` — `Salt/BV/Completion.lean:134/141/191/237/76`.
  This is the **sharp-cutoff** completion kit (indicator ↔ frequencies). It is *not*
  the sawtooth kit HB's §7 needs (see §2, delta iii).
- `Salt.BV.polya_vinogradov` — `Salt/BV/PolyaVinogradov.lean`, used ~8 places in `Salt/SW/`.
  Note HB deliberately avoids Pólya–Vinogradov at (6.10) (`hb1983-notes.md:679-681`).

---

## 2. WHAT "THE WEIL-DELTA TRIO" IS, AT THE BYTES

**Provenance of the phrase.** `council-0804.md:30` ("N6 (the Weil-delta trio off the
banked 5,687-ln Weil bank)") points back to the HB-ENGINE re-freeze,
`docs/exploration/s3-hb3-design.md:808-813`, which names exactly three "Remaining
deltas", re-quoted as "Deltas owed" at `docs/exploration/fulcrum_audit_glue.md:104-106`:

> *"Remaining deltas: (i) the gcd factor (k,u,v)^{1/2} (our τ√c is unit-a only);
> (ii) CUBE-FREE moduli (χ real primitive ⟹ q cube-free, p.212) — corpus has k=1 sharp
> (Weil) + k=2 sharp (even prime-power); cube-free assembly is a modest CompositeFull
> extension; (iii) Lemma 10's congruence-conditioned interval variant of the completion."*

**Scope caution.** The N6 crosswalk row (`docs/sources/hb1983-notes.md:861`) prices N6 as
**two** character-sum inputs — Estermann (7.1) at p.221, *and* the p.217 real-primitive
bound — noting *"the second is stated without proof in HB and must be supplied."*
So: the trio all sits under input 1; input 2 is a fourth item. **The Fable block must rule
the scope explicitly**; this dossier treats N6 = trio + p.217 lift.

---

### DELTA (i) — the gcd factor `(k,u,v)^{1/2}`

**What HB demands.** (7.1), p.221 (`hb1983-notes.md:742`):
```
S(k; u,v) = Σ_{n=1,(n,k)=1}^{k} e((un + v n̄)/k) ≪ d(k)·k^{1/2}·(k,u,v)^{1/2}
```
Estermann 1961 [6]; HB's **only** algebraic-geometry-grade input, elementary and effective.

**Where consumed.** §7's completion, (7.7) `hb1983-notes.md:760-763`. The inner sum is
completed by additive characters mod `k`, producing `S(k; s, Cm)` **for every residue
`s`**, and the term that survives is
```
Σ_{1 ≤ s ≤ k₀} k₀(k₀,s)^{1/2} s^{-1} ≪ d(k₀) log(2k₀).
```
`s` ranges over non-units; `m` ranges `1..Kk^{1/2}` so `Cm` is not a unit either
(`(C,k)=1` per Lemma 10's hypothesis, `hb1983-notes.md:596`, but `m` is free).

**Which bank export serves it.** Nothing, on the non-unit branch. `T`
(CompositeFull.lean:384) and every `P`-row require `IsUnit a`. `kloosterman_comm`
(Kloosterman.lean:68) lets the unit hypothesis sit in *either* slot — so the branch is
needed only when **both** `s` and `Cm` are non-units mod some prime power, which halves
the work but does not remove it.

**Interface gap, exactly.**
- Missing: the descent identity `p ∣ a ∧ p ∣ b ⟹ S(a,b;p^k) = p·S(a/p, b/p; p^{k-2})`
  (the standard `k ≥ 2` gcd reduction) — nowhere in the bank.
- Missing: the `(a,b,c)`-indexed composite assembly. `C3` (Composite.lean:190) is
  **unit-free** but takes uniform per-factor bounds `M₁,M₂` quantified over *all*
  `a₁,b₁`, which loses gcd tracking. `C1`+`C4` together give the explicit projected
  arguments with **unit** twists `l₁,l₂` — so `gcd(a₁,b₁,c₁) = gcd((CRT a).1,(CRT b).1,c₁)`
  is recoverable. The machinery is present; the gcd-tracking wrapper is not.

---

### DELTA (ii) — "cube-free moduli" — **MIS-SCOPED (see finding 2)**

**What the delta record claims.** That the Kloosterman modulus is cube-free, so `k=1`
(Weil) + `k=2` (even prime-power) suffice and "cube-free assembly is a modest
CompositeFull extension" (`s3-hb3-design.md:809-812`).

**What the source says.** Lemma 10 is applied (p.214, `hb1983-notes.md:605-606`) with
```
k = D·δ₁·w₁,   D = α₂ q Δ^{-1}   (5.12),   E = S₂,
```
summed over `S₁ < w₁ ≤ 2S₁, w₁ ≡ b₁ (mod q)` — see (5.14), `hb1983-notes.md:588`.
`w₁` is a free integer variable. **`k` is arbitrary**: `8 ∣ k`, `27 ∣ k`, etc. all occur.

**Where cube-freeness is *actually* consumed** (and it is `q`, not `k`):
- (5.5), p.212 (`hb1983-notes.md:566-567`) — verbatim: *"since χ is real and primitive,
  q can have no cube factors. Thus (1.8) and (1.9) yield (α₁,q) = (α₂,q)."*
- p.216 regime (a) (`hb1983-notes.md:646-647`) — to get `(α_i, q/Δ) = 1` and `(Δ, q/Δ) = 1`.

Both are **N7** congruence steps (crosswalk `hb1983-notes.md:862`), not Kloosterman steps.

**And the claim is false as stated.** χ₈ is a real primitive character mod `8 = 2³`
(mathlib: `Mathlib/NumberTheory/LegendreSymbol/ZModChar.lean:129`). The house already
ruled the correct replacement — `fulcrum-pass1.md:57`:
> *"Conductor shape consumed at (α_i, q/Δ)=1 steps via (1.9) — land as the structural
> lemma (a ∈ {0,2,3}), NOT cube-freeness."*

i.e. **χ real primitive mod q ⟹ q = 2^a·m with a ∈ {0,2,3} and m odd squarefree.**
That is the object N6/N7 should build. It also *implies* what HB's (5.5) step needs at
odd `p` and forces the `a=3` case to be handled separately (where HB's own sentence
does not hold).

**Interface gap, exactly.** Delta (ii) splits in two:
- **(ii-a) [N6]** the per-prime-power bound at **arbitrary** exponent, both parities,
  `p = 2` included, no `IsUnit`. Bank state: `P4` gives `2p^j` for odd `p`, `IsUnit a`,
  `k ≤ 2j`, `j+1 ≤ k`; `P5` is `√p` above sharp on odd exponents; `P6` is the trivial
  `2^k` at `p = 2` (a **full square root** below sharp, docstring: "the consumers absorb
  the `2^{O(1)}` loss" — an assumption that must now be re-checked, since `v₂(k)` is
  unbounded here).
- **(ii-b) [N7, flag only]** the `q = 2^a m, a ∈ {0,2,3}` structure lemma.

---

### DELTA (iii) — Lemma 10's congruence-conditioned interval completion

**What HB demands.** Lemma 10, p.213-214 (`hb1983-notes.md:596-603`): for `(C,k)=1`,
`q ∣ k`, `(q,b)=1`, `n̄` the inverse mod `k`, `I ⊆ (E,2E]`, any real `T`,
```
Σ′_{n ∈ I} ψ(f(n)) ≪ (1 + |T|E^{-1}k^{-1})(E + k) q^{3/2} k^{ε-1/4},
f(n) = (T − Cn̄)/k  or  (T/n − Cn̄)/k,   Σ′ imposing (n,k)=1 AND n ≡ b (mod q).
```
`ψ(θ) = θ − [θ] − ½` (the sawtooth), not `ψ(y,χ)` — see the notation hazard sheet
`hb1983-notes.md:903`.

**The §7 route** (`hb1983-notes.md:747-770`): the sawtooth Fourier expansion
```
ψ(θ) = −Σ_{0<|m|≤K} e(mθ)/(2πim) + O(Min(1/(K‖θ‖),1))     (7.2)
Min(1/(K‖θ‖),1) = Σ_m a_m e(mθ), K ≥ 2                     (7.3)
a_m ≪ Min((log K)/K, K/m²)                                 (7.4)
```
then `S_m = Σ′_{n∈I} e(mf(n))`, partial summation (7.6), completion by additive
characters mod `k` with `q ∣ n−b` detected via
`Σ_{n∈I₀, q∣n−b} e(−sn/k) ≪ Min(E, ‖sq/k‖^{-1})`, then (7.1) ⟹ (7.7)/(7.8), then
`K = 2 + k^{1/4}`.

**Which bank export serves it.** `I` = `norm_incomplete_kloosterman_le`
(Incomplete.lean:181) is the closest object and it is the **wrong genre in three ways**:
prime modulus only (`[Fact p.Prime]`); interval is `[1,Z]` on `val t` with `Z ≤ p`, not a
subinterval of `(E,2E]`; **no congruence condition** `n ≡ b (mod q)`; and it completes an
*indicator*, not a *sawtooth*.

**Interface gap, exactly.**
- The `Salt.BV` completion kit (`Completion.lean:134/141/191/237`) supplies the
  indicator↔frequency expansion and the `2 + log H` L¹ mass. It is reusable for the
  `q ∣ n−b` detection but **not** for (7.2)–(7.4).
- (7.2)–(7.4) — the sawtooth expansion with the `Min(1/(K‖θ‖),1)` majorant and
  `a_m ≪ Min(log K/K, K/m²)` — is **absent from the corpus**. Grep for
  `sawtooth`/`Int.fract` returns only `Salt/ExpSum/ZetaApprox.lean` (a `Int.fract`-in-integral
  form for ζ, unrelated).
- **Seam recommendation:** the crosswalk assigns Lemma 10 itself to **N7**
  (`hb1983-notes.md:862`: "Lemmas 9, 10, 11"). N6 should deliver the *supply*
  (complete-sum bound + sawtooth kit + congruence-restricted completion identity);
  N7 assembles (7.5)–(7.8). Otherwise N6 and N7 collide on Lemma 10.

---

### INPUT 2 (the crosswalk's second character-sum input) — p.217, the real-primitive bound

**The corrected form** (`hb1983-notes.md:667-669`; correction record `:927-930`;
`fulcrum_audit_source.md:185` item 1) — for χ real primitive mod q:
```
Σ_{t=1}^{q} χ(ut + u′) χ(vt + v′) ≪ (q, uv′ − vu′).
```
The recorded form at `fulcrum_audit_source.md:95` drops the `v` in the second factor;
with `v` dropped the RHS `(q, uv′−vu′)` does not match its own arguments.

**Where consumed.** §6, regime (c) `S_i > R_i` for both `i`, p.217
(`hb1983-notes.md:661-672`). After the `t_i ≡ γ_i t (mod q/Δ)` parametrization the object is
`|Σ_{t=1}^{q/Δ} χ(Δγ₁t + β₁)χ(Δγ₂t + β₂)|`, and the bound gives
`Σ ≪ Δ^{-1}(q, Δα^{-1}(α₁β₂ − α₂β₁)) ≪ 1` **using (1.6)** `α₁β₂ − α₂β₁ ≠ 0`
(`hb1983-notes.md:44`). Regime (c) then contributes `≪ xL⁴(qδ₁δ₂)^{-1}`.

**What is landed** — `Salt/HB/QuadCharSum.lean`, all three audited at 3 axioms
(`Salt/HB/All.lean:98-100`):

| Export | Statement | Line |
|---|---|---|
| `quadraticChar_sum_mul_shift` | `ringChar F ≠ 2`, `e ≠ 0`: `∑ t : F, χ(t)·χ(t+e) = −1` (QCS-1, via mathlib `jacobiSum_nontrivial_inv`) | :62 |
| `quadraticChar_sum_linear` | `a ≠ 0`: `∑ t, χ(a t + b) = 0` | :104 |
| **`quadraticChar_sum_two_forms_bound`** | `ringChar F ≠ 2`, `a*d − b*c ≠ 0`: `\|∑ t : F, χ(a t + b)·χ(c t + d)\| ≤ 2` | **:137** |
| `quadraticChar_sum_two_forms_trivial` | unconditional: `≤ Fintype.card F` | :117 |
| `legendre_sum_two_forms_bound` / `_trivial` / `legendre_sum_mul_shift` | the `ZMod p` specializations | :202 / :210 / :195 |

**The dictionary is exact**: `(a,b,c,d) = (u,u′,v,v′)`, `a*d − b*c = u v′ − u′ v`.
**The landed form is the corrected form.** The trivial companion is exactly the
`(q, det) = q` branch.

**Two document defects to fix inside N6** (no math impact):
- `Salt/HB/QuadCharSum.lean:13-14` and `:44` cite *"The fourth power moment of the
  Riemann zeta-function (Proc. LMS 1981)"*. Wrong paper. The bound is
  **Prime Twins and Siegel Zeros, Proc. LMS (3) 47 (1983) 193-224, p.217**
  (the file's own title line is right; the body and References are wrong).
- `docs/exploration/fulcrum_audit_source.md:95` still carries the dropped-`v` form
  inline; only the `:185` footer corrects it.

**The gap: composite lift.** Landed = the **prime** case (`ZMod p` / finite field, odd char).
Owed = arbitrary `q` carrying a real primitive χ. The CRT route
(`q = 2^a m, a∈{0,2,3}, m odd squarefree`) factors the sum into per-prime pieces, each
`≤ 2` (QCS-2) or `≤ p` (trivial branch, when `p ∣ det`), giving
```
|Σ| ≤ 2^{ω(q)} · (q, uv′ − vu′).
```
⟦INFERENCE — my derivation, refuter-grade⟧ **HB's `≪` is therefore not absolute**: it
hides `2^{ω(q)} ≤ d(q) ≪ q^ε`. Downstream this multiplies the regime-(c) error
`xL⁴(qδ₁δ₂)^{-1}` by `d(q)`, which (6.11)'s `≪ x^{1+ε}q^{-1}` absorption tolerates
(`hb1983-notes.md:683-688`) — but the Lean statement must **carry the factor explicitly**,
not inherit HB's `≪`.

---

## 3. THE REAL-PRIMITIVE-χ INPUTS — LANDED ANYWHERE?

| Input | Source cite | Landed? | Where / what's missing |
|---|---|---|---|
| p.217 two-forms bound, **prime case** | `hb1983-notes.md:667-669` | **YES** | `QuadCharSum.lean:137` (+ trivial `:117`), corrected form |
| p.217, **composite q** | same | **NO** | needs CRT lift + the `q = 2^a m` structure lemma + the `2^a` cases from χ₄/χ₈/χ₈′ |
| **p.216 `Σχ(b₂)` vanishing** ("vanishes unless `dΔ = q` since χ primitive") | `hb1983-notes.md:654-658`; cross-cut law `:873`; hazard `fulcrum_audit_source.md:179-180` | **NO** | nothing in the corpus. Consumed in §6 regime (b) (`S₁≤R₁, S₂>R₂`), killing that whole regime to `O(1)`; needs `∑_{b ≡ · (mod f)} χ(b) = 0` for `f` a proper divisor of the conductor — i.e. a primitivity/orthogonality lemma over congruence classes. mathlib has `DirichletCharacter/Orthogonality.lean` and `IsPrimitive`; the class-restricted vanishing is not there. |
| **q cube-free** (consumed at (5.5) p.212 and p.216) | `hb1983-notes.md:566-567`, `:646-647`, `:871-872` | **NO** | grep for cube-free over `Salt/` returns only unrelated `hcube` cube-root hypotheses in `Salt/Goldbach/*`, `Salt/SW/SiegelClose.lean`. Prior house ruling: land as `a ∈ {0,2,3}` (`fulcrum-pass1.md:57`), **not** cube-freeness — and note the raw statement is false at `q = 8`. |
| the structure theorem "χ real primitive mod q ⟹ q = 2^a m, a∈{0,2,3}, m odd squarefree" | derived from the above | **NO — and not in mathlib** | mathlib has `χ₄`/`χ₈`/`χ₈′` + `IsQuadratic` (`Mathlib/NumberTheory/LegendreSymbol/ZModChar.lean:53/129/168`), `DirichletCharacter.IsPrimitive`, `conductor`; **no** fundamental-discriminant classification (`grep -rln FundamentalDiscriminant Mathlib/` → empty). **This is the single most expensive unbuilt object in N6's tray.** |
| (1.6) `α₁β₂ − α₂β₁ ≠ 0`, consumed at p.217 | `hb1983-notes.md:44`, `:876` | n/a | a hypothesis to carry, not a theorem to prove; matches `quadraticChar_sum_two_forms_bound`'s `a*d − b*c ≠ 0` **exactly** |

---

## 4. THE N6 WAVE-DECOMPOSITION RECOMMENDATION

Files: new `Salt/Weil/Estermann.lean`, `Salt/Weil/GcdBranch.lean`,
`Salt/Weil/Sawtooth.lean`; extend `Salt/HB/QuadCharSum.lean` in place; new
`Salt/HB/RealPrimitive.lean`. Import order: `Weil/*` before `HB/QuadCharSum`.
Track branch per `CLAUDE.md`; `#print axioms` gate at every wave exit.

### W0 — THE BUDGET LEDGER (read-only, **must fire first**, no Lean)

The pre-proof ruling that can delete half of W1 and all of W2.

**Question.** How much Kloosterman loss does the chain (7.7) → (7.8) → Lemma 10 →
(5.19) → (6.11) tolerate?

⟦INFERENCE — my arithmetic, hand it to a refuter⟧ Replacing
`d(k)k^{1/2}(k,u,v)^{1/2}` by `d(k)k^{1/2+θ}(k,u,v)^{1/2}` turns `k^{-1/2}` in (7.7) into
`k^{-1/2+θ}`; re-balancing `K` in `{EK^{-1} + (1+K|T|E^{-1}k^{-1})q^{3/2}(E+k)k^{-1/2+θ}}`
gives Lemma 10 at `k^{ε−(1/4−θ/2)}` instead of `k^{ε−1/4}`. Our worst-case `θ` from the
landed `P5` (odd exponents `≥ 3`, loss `∏ p_i^{1/2} ≤ k^{1/6}`) is `θ = 1/6`, giving
`k^{ε−1/6}`, and (5.19)'s error exponent drifts from `x^{15/16+ε}` toward roughly
`x^{23/24+ε}`. **HB's own remark at p.214 (`hb1983-notes.md:625-626`) is decisive**:
*"the error term in (5.19) can be improved. However, all that is necessary for our
purposes is to have an exponent for x that is less than 1."* Plus the ~`q^{10}` visible
slack at the lower window edge (`hb1983-notes.md:690-692`: true need `x ≫ q^{240+O(ε)}`,
we have `x ≥ q^{250}`).
**But `P6` (the 2-adic `2^k` placeholder) is a full square root, `θ = 1/2` on the 2-part,
and `v₂(k)` is unbounded — that one is NOT absorbable and W2 is mandatory.**

Deliverable: a ruling on (a) is `P5`'s crude odd bound enough (⟹ delete the Gauss-sum
stone from W1); (b) confirm W2's necessity; (c) the tolerated `2^{ω(q)}`/`d(q)` grade in
the p.217 lift. Cost ~0.15–0.3M, read-only, one refuter.

### W1 — THE LOCAL BOUND (odd `p`, all exponents, **no `IsUnit`**)

| Stone | Statement | Class | Notes |
|---|---|---|---|
| W1-a | `p ∣ a → p ∣ b → k ≥ 2 → S(a,b;p^k) = p · S(a/p, b/p; p^{k-2})` (the gcd descent) | **B** | pure reindex/orthogonality; unlocks the whole non-unit branch |
| W1-b | `b = 0` non-unit fibres: `S(a,0;p^k)` (Ramanujan) — extend `kloosterman_zero_right` (CompositeFull.lean:309) off the prime case | **B** | |
| W1-c | `‖S(a,b;p^k)‖ ≤ (k+1)·p^{k/2}·(p^k,a,b)^{1/2}`, odd `p`, arbitrary `a,b` | **B** (given W0(a) = "crude OK") / **C** (if sharp odd exponent needed: Salié/Gauss-sum evaluation) | assembles W1-a/b over `P1`,`P3`,`P4`,`P5` |

Est. 600–1,400 ln. File `Salt/Weil/GcdBranch.lean` + `Salt/Weil/Estermann.lean`.

### W2 — THE 2-ADIC BRANCH (mandatory per W0(b))

`‖S(a,b;2^k)‖ ≤ C·2^{k/2}·(2^k,a,b)^{1/2}` replacing the trivial `P6`
(CompositeTail.lean:73). Class **C** (the `p=2` stationary phase is the classical hard
local case; `p ≠ 2` is hypothesised in `P3`/`P4`/`P5` for exactly this reason).
Est. 400–800 ln. Escalation candidate — if W2 stalls, the fallback is a W0-style
re-audit asking whether `v₂(k)` can be *bounded* upstream (it enters via `w₁`, so
probably not — flag loudly).

### W3 — THE GLOBAL ASSEMBLY (Estermann at arbitrary `k`)

`‖S(a,b;k)‖ ≤ d(k)·√k·(k,a,b)^{1/2}` for arbitrary `k`, arbitrary `a,b`.
Route: `Nat.recOnPosPrimePosCoprime` (the pattern already used at
CompositeFull.lean:387-390) over `C1`+`C4` (explicit **unit** CRT twists, so gcds are
preserved) with W1-c/W2 as the per-factor input, `d` and `√·` multiplicative.
Class **B**. Est. 250–450 ln. *This is the row the crosswalk calls "Estermann (7.1)".*

### W4 — THE p.217 COMPOSITE LIFT

| Stone | Statement | Class | Notes |
|---|---|---|---|
| W4-a | χ real primitive mod q ⟹ `q = 2^a·m`, `a ∈ {0,2,3}`, `m` odd squarefree, χ = CRT product | **C** | **not in mathlib**; the wave's cost centre; the `fulcrum-pass1.md:57` ruling names this shape |
| W4-b | the `2^a` cases: `a ∈ {0,2,3}`, bound `|Σ_{t mod 2^a} χ(ut+u′)χ(vt+v′)| ≤ 8` | **A** | finite check off `χ₄`/`χ₈`/`χ₈′` (`ZModChar.lean:53/129/168`) |
| W4-c | `\|Σ_{t=1}^{q} χ(ut+u′)χ(vt+v′)\| ≤ 2^{ω(q)}·(q, uv′−vu′)` | **B** | CRT product of `quadraticChar_sum_two_forms_bound` (:137) and `_trivial` (:117); **carry the `2^{ω(q)}` explicitly** |
| W4-d | the p.216 `Σχ(b₂)` vanishing over a congruence class mod `dΔ` with `dΔ ≠ q` | **B–C** | off `DirichletCharacter/Orthogonality.lean` + `IsPrimitive`; **flag**: this is a §6 regime-(b) input, arguably N7's — rule the seam |
| W4-e | doc fixes: `QuadCharSum.lean:13-14,:44` citation; `fulcrum_audit_source.md:95` inline form | **A** | zero risk, do it in wave 1 |

Est. 700–1,500 ln. Files: `Salt/HB/RealPrimitive.lean` (new) + `QuadCharSum.lean` (extend).

### W5 — THE SAWTOOTH KIT (delta iii's supply half)

(7.2)–(7.4): `ψ(θ) = −Σ_{0<|m|≤K} e(mθ)/(2πim) + O(Min(1/(K‖θ‖),1))`, the majorant's
Fourier coefficients `a_m ≪ Min((log K)/K, K/m²)`, and the congruence-restricted
completion `Σ_{n∈I₀, q∣n−b} e(−sn/k) ≪ Min(E, ‖sq/k‖^{-1})`.
Class **C**. Est. 500–1,000 ln, file `Salt/Weil/Sawtooth.lean`. Reuses
`Salt/BV/Completion.lean:76` (`sum_e_eq`) and the `dist₁` apparatus at
`Completion.lean:191`. **Does not** include (7.5)–(7.8) or Lemma 10 — those are N7.

### Dependency order and price

```
W0 (ruling)  →  W1 ∥ W2 ∥ W4 ∥ W5  →  W3 (needs W1+W2)  →  N7
```
`W4` and `W5` are independent of `W1/W2/W3` and can run in parallel writer slots
(**not** on the same `All.lean` — catch #104's shared-write hazard,
`docs/blueprints/flags.md:19005`).
**Honest total: ~2,500–5,200 ln**, dominated by W4-a (unbuilt structure theorem) and
W2 (`p=2` local). Two class-C escalation candidates: W2 and W4-a.

### Supply table — N6's exit interface for N7

| N7 will quote | N6 delivers | Serving today |
|---|---|---|
| (7.1) Estermann, arbitrary `k`, arbitrary `a,b` | W3 | `T` (squarefree+unit only) |
| (7.2)–(7.4) sawtooth | W5 | nothing |
| p.217 real-primitive two-forms, composite `q` | W4-c | `QuadCharSum.lean:137` (prime only) |
| p.216 `Σχ(b₂)` vanishing | W4-d (seam: could be N7) | nothing |
| `q = 2^a m`, `a ∈ {0,2,3}` | W4-a | nothing |
| (1.6) `α₁β₂ − α₂β₁ ≠ 0` | carried as a hypothesis | matches `:137`'s `a*d−b*c ≠ 0` |

---

## 5. REFUTER TARGETS FOR THE FABLE BLOCK

1. **W0's slack arithmetic** (§4, W0) — my `θ = 1/6 ⟹ x^{23/24}` chain is an inference,
   not a source claim. If it fails, W1-c goes class C.
2. **The `2^{ω(q)}` in W4-c** — is it truly absorbable at (6.9)/(6.11)
   (`hb1983-notes.md:676-688`), or does it need `Δ`-uniformity that HB's `≪ 1` hides?
3. **The `k` cube-free misread (finding 2)** — verify independently that `w₁` is free
   and `k = Dδ₁w₁` is unrestricted (5.14, `hb1983-notes.md:588`; the application,
   `hb1983-notes.md:605`). If I am wrong, W1/W2/W3 shrink dramatically.
4. **The W2 necessity** — can `v₂(k)` be bounded upstream? If yes, `P6` survives and
   W2 dies.
5. **The N6/N7 seam at Lemma 10** — the crosswalk puts Lemma 10 in N7
   (`hb1983-notes.md:862`) but delta (iii) puts its completion in N6. One owner, ruled.
6. **Naming collision** — `docs/exploration/n4b-design-0805.md:171` and `:309` use "N6"
   for *HB's §6 leading terms* (a Lemma-5/N7 object), not for the road's node N6.
   Two different N6s in live design docs. Also `N6.1/N6.2/N6.3` are **Brun** and
   **Maynard** node ids (`docs/blueprints/brun.md:123-125`,
   `docs/blueprints/maynard.md:214-216`). Pick a distinct tag before dispatching
   executors (`feedback_agent_naming` uses the node name as `subagent_type`).

---

## 6. FILE INDEX (absolute paths)

```
/Users/jyh/projects/claude/salt/Salt/Weil/                      (5,687 ln, 23 files, 60 audited)
  Kloosterman.lean:49,54,61,68,79,97,103        the object + trivial bounds + symmetries
  Descent.lean:194,206,222                      THE WEIL BOUND 2√p
  WeilStepanov.lean:77                          the Stepanov exit
  PrimePower.lean:228                           odd p, even exponent, unit a
  CompositeFull.lean:230,299,309,351,365,384    prime-power ge_two / odd / Ramanujan / τ√c
  Composite.lean:66,107,178,190                 CRT factorization (unit-free product bound)
  CompositeTail.lean:65,73,94,139,224           trivial/2-adic + unit-threaded CRT
  Incomplete.lean:181                           HB-F-COMP incomplete bound (prime only)
  MultiExtract.lean:37,209,228                  power-sum extraction
  All.lean:36-96                                the #audit_axioms roll
/Users/jyh/projects/claude/salt/Salt/HB/QuadCharSum.lean:62,104,117,137,195,202,210
/Users/jyh/projects/claude/salt/Salt/HB/All.lean:6,98-100
/Users/jyh/projects/claude/salt/Salt/BV/Completion.lean:76,134,141,191,237,291
/Users/jyh/projects/claude/salt/docs/sources/hb1983-notes.md:522-777 (§§5-7), :848-880 (crosswalk), :883-903 (notation hazards), :907-971 (checks + the D–H gap)
/Users/jyh/projects/claude/salt/docs/exploration/fulcrum_audit_source.md:89-101, :171-185
/Users/jyh/projects/claude/salt/docs/exploration/s3-hb3-design.md:795-813   ← the trio's origin
/Users/jyh/projects/claude/salt/docs/exploration/fulcrum_audit_glue.md:102-110
/Users/jyh/projects/claude/salt/docs/exploration/fulcrum-pass1.md:57        ← the a∈{0,2,3} ruling
/Users/jyh/projects/claude/salt/docs/exploration/fleet-meeting-0803-brief.md:40-43
/Users/jyh/projects/claude/salt/docs/exploration/council-0804.md:30
/Users/jyh/projects/claude/salt/docs/RESULTS.md:173
```

No writes, no commits, no edits made. Working tree as found
(`M claude.sh`, `?? docs/exploration/personal-time-record-0728.md`).
