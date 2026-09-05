# Jutila 1977 — research notes (the companion staging extract)

**Node:** JUTILA-STAGE (source extraction, no Lean). **Source:** M. Jutila, *On Linnik's
constant*, Math. Scand. **41** (1977), 45–62 (received 26 Nov 1976; Dept. of Mathematics,
University of Turku). Open access, DOI 10.7146/math.scand.a-11701 (resolves to
`https://journals.msp.org/mscand/article/view/1943`); PDF galley
`https://journals.msp.org/mscand/article/download/1943/1942/1974`. (The earlier
`mscand.dk/article/download/11701/9717` link is HTTP 404 since at least 2026-09-04; the DOI is the
durable pointer, the galley the direct one — both verified live 2026-09-05, `application/pdf`.)
**The PDF is NOT in this repo and must never enter it** (copyright). These are my own notes:
definitions, theorem statements with formulas transcribed faithfully, constants, and
proof-shape summaries. No prose passages are reproduced beyond the single effectivity
sentence in §2.4, quoted because the campaign's effectivity claim rests on it.

This is Heath-Brown 1983's **[11]**, the source of BOTH theorems HB consumes. It is the
reference behind the landed `dh_repulsion_ordered` (TBalR8.lean:1752) and the repulsion-side
reference for the fulcrum campaign (N0–N12). Companion to the HB staging extract.

**Reading conditions.** The scan carries **no text layer** (`pdftotext` returns 0 bytes), so
every formula below was read from the page images, with the delicate glyphs re-rendered at
600 dpi and re-read individually: Theorem 1′ (1.9), Theorem 2 (1.10), Theorem 3, the
effectivity sentence, Lemma 5's hypothesis, (2.8), and §6's (6.2) + the Y/R choices.
Anything I could not resolve is marked **⚠ FLAG**; there is one such item (§4, note c).

**Do not confuse** this with Jutila's *other* 1977 paper (Acta Arith. **32**, "Zero-density
estimates for L-functions", the sharper A₁ = 2 density via Halász–Montgomery). Not needed here.

---

## 0. THE HEADLINE RESULTS AND THE FIRST CORRECTION

### 0.1 ⚠ **L ≤ 550 IS NOT THIS PAPER'S RESULT — THIS PAPER PROVES L ≤ 80.**

The staging brief (and any reader carrying "Jutila 1977 = L ≤ 550") has the wrong number.
The paper's own account, p.45:

- Linnik: `p(q,a) ≪ q^L` for `(a,q) = 1` — (1.1), Linnik [11],[12].
- Turán [20] and Knapowski [10] proved Linnik's two theorems by **Turán's power-sum method**;
  the present author, in [7] and [8] (Ann. Acad. Sci. Fenn. 1969 / 1970), **carried out the
  calculations with the result L ≤ 550**. That is prior work, by the power-sum route.
- **THIS paper: Theorem 3 (p.47): Linnik's constant `L ≤ 80`.** Obtained from Theorem 1′ +
  Theorem 2 via §7's Turán-kernel computation at `k = 19` (`4k + 4 = 80`).

So `550` is the number this paper *supersedes*. Anywhere the repo says "Jutila 1977, L ≤ 550",
the correct reading is "Jutila [7],[8] 1969/70, L ≤ 550, by Turán power sums — improved to
**L ≤ 80** in Jutila 1977 by the pseudocharacter route".

### 0.2 The four numbered results

| Result | p. | Statement |
|---|---|---|
| **Theorem 1** | 46 | For `4/5 ≤ α ≤ 1`, `T ≥ 1`:  (1.7) `N(α,T,q) ≪_ε (qT)^{(2+ε)(1−α)}`,  (1.8) `N*(α,T,Q) ≪_ε (Q²T)^{(2+ε)(1−α)}`. |
| **Theorem 1′** | 47 | For all `λ > 0` and `D` sufficiently large:  (1.9) `N(λ) ≤ 10·e^{11λ}`. |
| **Theorem 2** | 47 | (the Deuring–Heilbronn repulsion) — see §2.1 below, (1.10). |
| **Theorem 3** | 47 | Linnik's constant `L ≤ 80`. |

Notation for Theorem 1 (p.46): `R(α,T) = {σ + it : α ≤ σ ≤ 1, |t| ≤ T}`;
`N(α,T,χ)` = number of zeros of `L(s,χ)` in `R(α,T)`; `N(α,T,q) = Σ_{χ mod q} N(α,T,χ)`
(so (1.7) is already summed over χ, and implies the per-character form);
`N*(α,T,Q) = Σ_{q ≤ Q} Σ*_{χ mod q} N(α,T,χ)` (asterisk = primitive characters only).

Notation for Theorem 1′ (p.47): `τ` any real number, `D = q(|τ| + 1)`, and **`N(λ)` counts
L-functions (mod q), not zeros** — the number of `L(s,χ)`, `χ` mod `q`, having **at least one**
zero in the rectangle `1 − λ/log D ≤ σ ≤ 1`, `|t − τ| ≤ 1`. Theorem 1′ is called "a weak form
of (1.7)" and is what §7 actually uses.

---

## 1. THE PSEUDOCHARACTER APPARATUS (§1, §2)

### 1.1 The definition (p.45, (1.2))

For a **square-free** number `r` and a multiplicative arithmetic function `f`, the *pseudocharacter*
`f_r` is the periodic multiplicative function

    (1.2)   f_r(n) = f((r, n)) .

Abbreviation used throughout (p.47): `f_r f_{r'}(n) = f_r(n) f_{r'}(n)`; and `Σ'` denotes a sum
over **square-free numbers coprime with q**.

### 1.2 The two choices of `f` — and which theorem each serves

| choice | `f(n)` | whose | used for |
|---|---|---|---|
| Selberg's | `μ(n)φ(n)` | Selberg [19], *Remarks on sieves* | Theorem 1 (density); it is the `f` of Lemma 3 and of Lemma 6's `ψ(n) = μ(n)φ(n)` |
| Jutila's | `μ(n)·2^{−ω(n)}·n` | this paper, p.45 + Lemma 10 (p.55) | **Theorem 2** (the repulsion) |

`ω(n)` = number of distinct prime factors. The paper attributes the whole idea to Selberg [19]:
a pseudocharacter is inserted into the Dirichlet polynomial and the zeros are detected by an
identity (Lemma 1); **averaging over `r` saves a logarithm** in the zero-density estimate (p.45),
which is what makes the Linnik-type density theorem work near `σ = 1` where the usual Dirichlet
polynomial method gives only trivial results.

### 1.3 Lemma 1 — the detection identity (p.48)

Let

    (2.1)   M(s, χ, f_r) = Σ_{d=1}^∞ ξ_d χ(d) f_r(d) d^{−s} · ∏_{p | r/(r,d)} { 1 + (f(p) − 1) χ(p) p^{−s} } ,

with `ξ_d = O(1)`. Then for `Re s > 1`

    (2.2)   L(s, χ) · M(s, χ, f_r) = Σ_{n=1}^∞ ( Σ_{d|n} ξ_d ) χ(n) f_r(n) n^{−s} .

Proof shape: `r` square-free and `f` multiplicative give `f_r(nd) = f_r(d) f_t(n)` with
`t = r/(r,d)`; feed that into the Euler product of the generating function of `χ(n) f_r(n)`.
(Lemmas 1–3 are stated as partial generalizations of Lemmas 2–4 of Motohashi [17].)

### 1.4 Lemmas 2, 3 — the `h(d; r, r')` coefficients (pp.48–49)

Lemma 2 defines `h(d; r, r')` by

    ∏_{p | rr', p ∤ (r,r')} (1 + (f(p) − 1) p^{−s}) · ∏_{p | (r,r')} (1 + (f²(p) − 1) p^{−s})
        = Σ_{d=1}^∞ h(d; r, r') d^{−s} ,

and then `f_r f_{r'}(n) = Σ_{d|n} h(d; r, r')`. (Proof: `Σ_n f_r f_{r'}(n) n^{−s} = ζ(s)·Σ_d h(d;r,r')d^{−s}`.)

Lemma 3 — the two facts actually used, **for `f(n) = μ(n)φ(n)`**:

    Σ_d h(d; r, r') d^{−1} = δ_{r,r'} · φ(r)      (δ = Kronecker delta)
    Σ_d |h(d; r, r')| ≤ ∏_{p|r} (p + 1) · ∏_{p|r'} (p + 1) .

The **orthogonality** in the first line (only `r = r'` survives) is the mechanism that makes the
`r`-average collapse to a single log in §3.

### 1.5 Lemmas 4, 5 — the Barban–Vehov / Graham input and the `r`-average (p.49)

Barban–Vehov [1] problem: minimize `S = Σ_{n ≤ x} (Σ_{d|n} λ_d)²` subject to

    (2.5)   λ_d = μ(d)  for 1 ≤ d < z₁,   λ_d = 0  for d > z₂        (1 < z₁ < z₂),
    (2.6)   λ_d = μ(d)·log(z₂/d)/log(z₂/z₁)   for z₁ ≤ d ≤ z₂ ;

their result was `(2.7) S ≪ x/log(z₂/z₁)`. Motohashi [16] gave a fuller proof. **Lemma 4** is
S. Graham's [5] sharpening to an asymptotic formula with an error term:

    S = x/log(z₂/z₁) + O(x/log²(z₂/z₁))                     for x ≥ z₂ ,
    S = x·log(x/z₁)/log²(z₂/z₁) + O(x/log²(z₂/z₁))          for z₁ < x < z₂ .

Jutila states (p.46) that Graham's theorem is "very useful in calculating the constants implied
by the symbols ≪_ε" — i.e. **Lemma 4 is the explicit-constants engine of the density side**.

**Lemma 5** (the `r`-average): for `log R ≥ (log q)^{1/2}` and `R → ∞`,

    Σ'_{r ≤ R} r^{−1} = 6π^{−2} · ∏_{p|q} (1 + p^{−1})^{−1} · log R · (1 + o(1)) .

(Proof: the generating function `Σ'_r r^{−s} = ζ(s)/ζ(2s) · ∏_{p|q}(1 + p^{−s})^{−1}`.)
This is the source of the `6/π²` in Lemma 6's (2.10). The exponent `1/2` in `(log q)^{1/2}` was
re-read at 600 dpi and matches the same glyph in (2.8).

---

## 2. THEOREM 2 — THE REPULSION SIDE (§5, §6)

### 2.1 The statement (p.47), transcribed

> **Theorem 2.** Let `χ₁` be a real non-principal character (mod `q`), `β₁ = 1 − δ₁` a real zero
> of `L(s, χ₁)`, `χ` a character (mod `q`), and `ρ = β + iτ = 1 − δ + iτ` a zero of `L(s, χ)`
> with `δ < 1/6`, `β ≤ β₁`. Suppose that `D = q(|τ| + 1)` is sufficiently large, that is,
> `D ≥ D₀(ε)`. Then

    (1.10)   δ₁  ≥  (1 − 6δ) · D^{−(2+ε)δ/(1−6δ)} / 8 log D .

Scope points that matter downstream:

- **`χ` is ANY character mod `q`** — including `χ = χ₀` and `χ = χ₁`. The diagonal is *inside*
  the statement, not excluded (see §2.3 — this answers a question left open in our own docs).
- No primitivity is assumed of either character.
- `τ` is unrestricted; the τ-dependence is entirely inside `D = q(|τ|+1)`.
- `δ < 1/6` ⟺ `β > 5/6`.
- The proof (Lemma 10) additionally runs under `3/4 < β₁ < 1`; §6 opens by noting one may
  suppose `δ₁ ≪ 1/log D` (otherwise nothing to prove).
- `D₀(ε)` is **not computed** in the paper.

### 2.2 The proof apparatus — ⚠ **NOT** Graham/Halász, and **NOT** Turán power-sums

**This corrects our recorded reading** (see §5c). Theorem 2's proof lives in §5 (Lemmas 9–12,
pp.54–58) and §6 (pp.58–59), and its apparatus is:

**(i) The `1∗χ₁` detector (p.54–55).** Set `a_n = Σ_{d|n} χ₁(d)`. Then
`a_n = ∏_{p^α ‖ n} (1 + χ₁(p) + … + χ₁(p^α)) ≥ 0`; and for **square-free** `n`,
`a_n = 0` if some `p | n` has `χ₁(p) = −1`, and otherwise `a_n = 2^{ω(n)}`.
This is exactly the elementary non-negative detector the house named DH-1.

**(ii) Lemma 9 (p.55) — the factorization.** For `χ` a Dirichlet character, `f` multiplicative,
`r, r'` square-free with `χ₁(p) = 1` for every `p | rr'`, and `Re s > 1`,

    G_{r,r'}(s, χ) = Σ_{n=1}^∞ μ²(n) a_n χ(n) f_r f_{r'}(n) n^{−s}

satisfies

    (5.1)   G_{r,r'}(s, χ) = L(s, χ) · L(s, χχ₁) · P_{r,r'}(s, χ) · Q(s, χ) ,

with the explicit finite/Euler factors

    P_{r,r'}(s,χ) = ∏_{p|rr', p∤(r,r')} (1 + 2χ(p) f(p) p^{−s}) · ∏_{p|(r,r')} (1 + 2χ(p) f²(p) p^{−s})
                        · ∏_{p|rr'} (1 + 2χ(p) p^{−s})^{−1} ,
    Q(s,χ) = ∏_{χ₁(p)=1} (1 − χ(p) p^{−s})² (1 + 2χ(p) p^{−s}) · ∏_{χ₁(p)=−1} (1 − χ²(p) p^{−2s}) .

So the detector is the **product** `L(s,χ)·L(s,χχ₁)` carrying a pseudocharacter mollifier —
the "product/mollifier route" in our design vocabulary, with `Q` absolutely convergent for
`Re s > 1/2` (this is what lets the contour go to `Re s = 1/2 + ε`).

**(iii) Lemma 10 (pp.55–56) — the asymptotic at the Siegel scale.** Choose
`f(n) = μ(n)·2^{−ω(n)}·n` in Lemma 9, assume `L(β₁, χ₁) = 0` with `3/4 < β₁ < 1`, and put

    T = Σ'_{n=1}^∞ a_n e^{−n/Y} n^{−β₁} ( Σ'_{r ≤ R} a_r f_r(n) r^{−1} )² ,   S = Σ'_{r≤R} a_r r^{−1} .

Then

    (5.2)   T = (φ(q)/q) · Q(1, χ₀) · L(1, χ₁) · Γ(δ₁) · Y^{δ₁} · S + O_ε( R q^{1/4} Y^{1/2−β₁+ε} ) .

Proof shape: Mellin (`2πi T = Σ'_{r,r'≤R} (rr')^{−1} a_r a_{r'} ∫_{Re s=1} G_{r,r'}(s+β₁, χ₀) Γ(s) Y^s ds`),
then shift to `Re(s + β₁) = 1/2 + ε`; **the zero `s = β₁` of `L(s,χ₁)` cancels the pole of `Γ(s)`
at `s = 0`**, and the pole of `L(s,χ₀)` at `s = 1` gives the main term. The `Γ(δ₁)Y^{δ₁}` factor
is the entire mechanism: `Γ(δ₁) ~ 1/δ₁`, so a *small* `δ₁` makes the main term *large*, and the
contradiction with an upper bound for `T` forces `δ₁` up. Two identities carry the diagonal
collapse: `P_{r,r'}(1, χ₀) = 0` for `r ≠ r'`, and `P_{r,r}(1, χ₀) = r a_r^{−1}`.

**(iv) Lemma 11 (pp.56–57) — the floor for `S`.**

    S ≥ (φ(q)/q) · Q(1, χ₀) · L(1, χ₁) · δ₁^{−1} + O_ε( R^{−1/2+ε} q^{1/4+ε} ) ,

via `F(s) = L(s,χ₁) L(s,χ₀) Q(s,χ₀)`, a Perron integral to `a = δ₁ + 1/log(qR)`, then a shift to
`Re(s+β₁) = 1/2 + ε` estimated by **Hölder's inequality and mean fourth power estimates**.

**(v) Lemma 12 (pp.57–58) — the dichotomy.** With `L(ρ,χ) = 0`, `ρ = β + iτ`, `3/4 < β < β₁`,
`D = q(|τ|+1)`:

- if `χ ≠ χ₀, χ₁`:   (5.3) `T ≥ S²(1 + Y^{(1+ε)(β−β₁)}) + O_ε(R D^{1/2} Y^{1/2−β₁+ε})`;
- if `χ = χ₀` or `χ₁`: **either** (5.4) `T ≥ S²(1 + ½ Y^{(1+ε)(β−β₁)}) + O_ε(R D^{1/2} Y^{1/2−β₁+ε})`,
  **or** (5.5) `δ₁ ≥ ½ Y^{β−1} |Γ(1−ρ)|^{−1} { 1 + O_ε(R^{−1/2+ε} q^{1/4+ε}) }`.

Proof shape: form `T_χ = Σ μ²(n) a_n χ(n) e^{−n/Y} n^{−ρ} (Σ'_{r≤R} a_r f_r(n) r^{−1})²`; for
`χ ≠ χ₀,χ₁` the integrand is regular between `Re s = 1` and `Re(s+β) = 1/2 + ε`, giving
`(5.6) T_χ ≪ R D^{1/2} Y^{1/2−β+ε}`; the `n = 1` term of `T_χ` is `α₁ = S²`, so the tail must
absorb `S²`, and comparing with `T = Σ|α_n| e^{−n/Y} n^{−β₁}` gives (5.3). **The extra `n = 1`
term is the repelled zero's own signature** — this is where `L(ρ,χ) = 0` is spent.

**(vi) §6 (pp.58–59) — the extraction.** Compare Lemma 10 and Lemma 12. For `χ ≠ χ₀, χ₁`:
combine (5.2) and (5.3), cancel, substitute Lemma 11 for `S`, obtaining

    (6.1)   Y^{δ₁} − 1  ≥  Y^{−(1+ε)δ} + O(δ₁) + O_ε(R D^{1/2} Y^{−1/2+ε}) + O_ε(R^{−1/2+ε} D^{1/4+ε}) .

Then **the parameter choice**

    Y = D^{2/(1−6δ) + ε₁} ,        R = D^{(1+2δ)/(2−12δ) + ε₂} ,

with `ε₁, ε₂` small in terms of `ε` so the `O_ε(…)` terms in (6.1) are of lower order than
`Y^{−(1+ε)δ}`. This yields

    (6.2)   δ₁ ≥ (1 − ε) Y^{−(1+ε)δ} / K(Y, δ₁) ,
    (6.3)   K(Y, δ₁) = δ₁^{−1}(Y^{δ₁} − 1) = e^α log Y ,   α ∈ (0, δ₁ log Y) .

One may suppose `δ₁ log Y < 1/2` (else Theorem 2 is clear), so `α < 1/2`, and (1.10) follows.
**Consistency check (mine):** `Y^{−(1+ε)δ} = D^{−(2+ε′)δ/(1−6δ)}` and
`(1−ε)/(e^{1/2}·2/(1−6δ)) ≈ 0.30(1−6δ) ≥ (1−6δ)/8`, so the printed `8 log D` is the honest
rounding of the constant. The `2/(1−6δ)` in `Y` is the sole source of `(2+ε)/(1−6δ)` in (1.10).

**Where Graham/Halász/Turán actually live** (the correction in §5c):
`Lemma 4` (Graham) and `Lemma 7` (Halász, in the modified form with the `η_j` retained) are §2
lemmas and are used in **§3, the proof of Theorem 1** — *not* in §§5–6. Turán's method appears
only in **§7**, as the kernel `K(w) = e^{kw}(e^w − e^{−w})/2w` of Turán [20], for converting the
two theorems into `L ≤ 80`. Theorem 2's proof uses **none of the three**.

### 2.3 THE DIAGONAL — answered from the source

Our WP2 design left this open (s3-hb3-design.md:1014–1031: *"how his Thm 2 statement still
covers the diagonal at log η quality must be read from his §§5–6"*). **Answer:**

- The diagonal `χ ∈ {χ₀, χ₁}` is handled explicitly and costs **a factor 2**, nothing more.
  In branch (5.4) the only change from (5.3) is `Y^{(1+ε)(β−β₁)} → ½Y^{(1+ε)(β−β₁)}`; §6, p.59:
  the argument is as above and "the resulting lower bound for `δ₁` is half of that in (6.2)".
- The reason the regular-integrand argument fails on the diagonal is named: `L(s,χ)L(s,χχ₁)` is
  **not regular at `s = 1`** when `χ ∈ {χ₀, χ₁}`, so instead of (5.6) one gets
  `T_χ = (φ(q)/q) Q(1,χ₀) L(1,χ₁) Γ(1−ρ) Y^{1−ρ} S + O_ε(R D^{1/2} Y^{1/2−β+ε})`, and the split
  is on whether `A = |S² − (φ(q)/q)Q(1,χ₀)|L(1,χ₁)||Γ(1−ρ)|Y^{1−β}| ≥ ½S²` (⟹ (5.4)) or
  `< ½S²` (⟹ (5.9) `S = θ(φ(q)/q)Q(1,χ₀)L(1,χ₁)|Γ(1−ρ)|Y^{1−β}`, `2/3 ≤ θ ≤ 2`, which against
  Lemma 11 gives (5.5)).
- Branch (5.5) is closed with the auxiliary estimate

      (6.4)   |1 − ρ| ≥ 0.28 / log q ,

  trivial for `χ = χ₀`, and otherwise from Lemma 12 of Miech [13] (`ρ` real) or Lemma 3b of
  Jutila [7] (`ρ` non-real). Since `|Γ(1−ρ)|^{−1} ≍ |1−ρ|` for small `|1−ρ|`, (5.5) + (6.4)
  give `δ₁ ≳ 0.14 Y^{β−1}/log q` — same shape, no quality loss.

**Consequence for us:** the diagonal fork does **not** degrade the repulsion quality in the
source; our own diagonal-only contract is therefore not a weakening relative to Jutila on the
character axis (it is the case HB consumes), and Jutila's own route to it is the product
detector `L(s,χ)L(s,χχ₁)` + explicit pole bookkeeping — the same shape the house recorded from
Benli–Goel–Twiss–Zaman (s3-hb3-design.md:1036–1046).

### 2.4 The effectivity remark — exact location and wording

**Page 47**, in the paragraph immediately following the statement of Theorem 3 (i.e. after
`L ≤ 80`, before the acknowledgements). The claim, quoted:

> "We do not appeal to Siegel's theorem, so that everything can be made explicit."

The same paragraph continues that it would not be too difficult to compute a constant `L₀` with
`p(q,a) ≤ q^{L₀}` for all `q ≥ 2` and `(a,q) = 1`.

There is a **second, more operational effectivity statement on p.61** (end of §7): treating the
Siegel-zero case, Jutila separates `δ₁ ≥ q^{−ε}` from `(q^{1/4}log q)^{−1} ≪ δ₁ < q^{−ε}`, notes
that the latter possibility could be avoided by appealing to Siegel's theorem, and states that
this is not necessary — so all estimations are in principle effective. Note that the effectivity
is *in principle*: `D₀(ε)` in Theorem 2 and the `≪_ε` constants in Theorem 1 are never computed
in this paper. **This is exactly the gap our machine-checked contract closes** (§5a).

---

## 3. THE DENSITY SIDE (§2–§4)

### 3.1 The prior estimates being improved (p.46)

| | estimate | source |
|---|---|---|
| (1.3) | `N(α,T,q) ≪_ε (qT³)^{(1+ε)(1−α)}` | Selberg's method [15] |
| (1.4) | `N*(α,T,Q) ≪_ε (Q⁵T³)^{(1+ε)(1−α)}` | Selberg's method [15] |
| (1.5) | `N(α,T,q) ≪_ε (q²T³)^{(1+ε)(1−α)}`, `4/5 ≤ α ≤ 1` | Motohashi [17] |
| (1.6) | `N*(α,T,Q) ≪_ε (Q⁴T³)^{(1+ε)(1−α)}`, `4/5 ≤ α ≤ 1` | Motohashi [17] |
| (1.7)/(1.8) | `(qT)^{(2+ε)(1−α)}` / `(Q²T)^{(2+ε)(1−α)}` | **Theorem 1** |

Density-hypothesis language: Theorem 1 "extend[s] the density hypothesis to the interval
`[4/5, 1]`". Density theorems of type (1.3)/(1.4) are credited to Fogels [3] and Gallagher [4].
Huxley's remark (p.54): the same method gives `N*(α,T,Q) ≪_ε (Q³T²)^{(1+ε)(1−α)}` for α near 1.
Jutila notes (p.46) that Theorem 1 was proved in the unpublished [9], and that Huxley's
communication of Graham's theorem [5] is what made the explicit constants (and hence the new
proof of Linnik's second theorem) available.

### 3.2 The proof shape of Theorem 1 (§3, pp.51–53)

1. **Well-spaced systems.** `D = qT`, `Δ = 1/log D`; split `R(α,T)` into `α ≤ σ ≤ 1`,
   `max(−T, kΔ) ≤ t ≤ min(T, (k+1)Δ)`, pick one zero per L-function per box, and separate even
   from odd `k` to get two Δ-well-spaced systems. `J` = cardinality of the larger. **Lemma 8**
   (Linnik's density lemma, Prachar [18, p.331]: the number of zeros of `L(s,χ)` in
   `α ≤ σ ≤ 1`, `|t − T| ≤ (1−α)/2` is `≪ (1−α)log(q(T+1)) + 1`) reduces (1.7) to a bound for `J`.
2. **Lemma 6 (p.50) — the detected Dirichlet polynomial.** With `f = ψ = μφ`, `ξ_d = λ_d` the
   Barban–Vehov/Graham weights (2.5)/(2.6), `a(n) = Σ_{d|n} λ_d`, parameters satisfying
   `(log q)^{1/2} ≤ log R ≪ log(qT)` and `(2.8) X^α ≥ ((qT)^{1/2} R z₂)^{1+ε}`, and
   `x = X log²(qT)`, the mollified polynomial `g(s,χ) = Σ_{z₁ < n ≤ x} a(n) χ(n) e^{−n/X} n^{−s}
   Σ'_{r≤R} r^{−1} ψ_r(n)` satisfies at any zero `ρ ∈ R(α,T)`

       (2.10)   |g(ρ, χ)| ≥ (1 − ε)(φ(q)/q)(6/π²) log R .

   Mechanism: multiply (2.2) by `r^{−1}`, sum over `r`, Mellin-transform (Prachar [18, p.380,
   Satz 3.2]); `a₁ = 1`, `a_n = 0` for `2 ≤ n ≤ z₁`; the contour term is `≪_ε 1` by (2.8), and the
   surviving main term is Lemma 5's `6π^{−2}∏(1+p^{−1})^{−1} log R`. **This is the "averaging over
   r saves a logarithm" step.**
3. **The explicit parameter choice (p.52):** `R = D^ε`, `z₁ = D^{1/2+7ε}`, `z₂ = D^{1/2+8ε}`,
   `X = D^{1+12ε}`, giving `(3.2) |g(ρ,χ)| ≫_ε (φ(q)/q) log D`.
4. **Lemma 7 (p.51) — Halász's inequality, modified form.** For `f(s,χ) = Σ_{n≤N} a_n χ(n)n^{−s}`,

       ( Σ_{j=1}^J |f(s_j, χ_j)| )²  ≤  Σ_{n≤N} |a_n|² b_n^{−1} · Σ_{j,k=1}^J η̄_j η_k B(s̄_j + s_k, χ̄_j χ_k) ,

   with `η_j` certain complex numbers of modulus 1, `b_n > 0` whenever `a_n ≠ 0`, and
   `B(s,χ) = Σ b_n χ(n) n^{−s}` absolutely convergent at all the pairs. This is Montgomery
   [14, Lemma 1.6] with **the `η_j` retained rather than eliminated by absolute values** — the
   feature Huxley's variant (3.7) exploits for the primitive-character estimate (1.8).
5. **The integrating device (the "new feature").** Take `b_n = n^{−1}(Σ'_{r≤R} r^{−1}ψ_r(n))²
   (e^{−n/N} − e^{−n/M})` with `M = e^ξ`, `N = e^η` **variable**, `ξ ∈ [(1−ε)log z₁, log z₁]`,
   `η ∈ [log x, (1+ε)log x]`, and integrate the Halász inequality in `ξ` and `η`. Lemma 4 supplies
   the `Σ|a(n)|²` evaluation; Lemma 2 expands `B(s,χ)`; the `I_d(s,χ)` contour integrals are
   negligible (`≪_ε J²x^{2−2α}D^{−5ε}R² ≪_ε J²` after Lemma 3), and the residues, summed over `d`
   by Lemma 3 (only `r = r'` survives), contribute `≪_ε J(φ(q)/q)x^{2−2α}log²D`. The result is
   `(φ(q)/q)²J²log²D ≪_ε (φ(q)/q) J x^{2−2α} log²D + J²`, which gives (1.7).
   *(Without the ξ,η-integration the Halász argument does not close — this device is the paper's
   stated novelty on the density side, p.46.)*
6. **(1.8):** Huxley's variant `(3.7)`, with `C(m, χ_j) = Σ_{r≤R, (r,q_j)=1} μ²(r) ψ_r(m) r^{−1}`
   depending only on the *modulus* of `χ_j`, and `|η_j| = q_j/φ(q_j)`; by primitivity `χ̄_jχ_k` is
   principal only when `χ_j = χ_k`.

### 3.3 Theorem 1′ (§4, p.54) — the explicit near-1 count

The estimate (1.9) needs proof only for `λ` below a certain constant (larger `λ` follows from
(1.7)). Restrict to non-principal characters; repeat §3 with two simplifications: **the
integrating device is unnecessary** (take `b_n` as in (3.3) with `M = z₁`, `N = x`), and the
constants are made explicit by Lemmas 4 and 5. With `z_i = D^{a_i}` (`i = 1,2`), `R = D^b`,
`X = D^c` subject to

    ½ + a₂ + b − c < 0 ,    ½ − a₁ + 2b < 0 ,

the conclusion is, for `D` sufficiently large,

    J ≤ (π²/6) · (c − a₁)² / (b(a₂ − a₁)) · e^{2cλ} .

**The choice `a₁ = 5/2, a₂ = 4, c = 11/2, b = 1 − ε` gives (1.9).** *(Check, mine:
`(c−a₁)² = 9`, `b(a₂−a₁) = 1.5(1−ε)`, so the prefactor is `(π²/6)·6 = π² ≈ 9.87 ≤ 10`, and
`e^{2cλ} = e^{11λ}`; the two constraints read `−ε < 0` and `−2ε < 0`. Self-consistent.)*

### 3.4 §7 — how the two theorems become `L ≤ 80` (pp.59–61)

Turán's kernel [20]: `K(w) = e^{kw}(e^w − e^{−w})/2w`, `K₁(w) = K(2w log q)`,
`R(n) = (1/2πi)∫_{Re w = 2} K₁²(w) n^{−w} dw`, with `R(n) = 0` for `1 ≤ n ≤ q^{4k−4}` and for
`n ≥ q^{4k+4}`, and `R(n) ≪ 1/log q` in between; and the explicit formula

    (7.1)   Σ_{q^{4k−4} < n < q^{4k+4}, n ≡ a (q)} Λ(n) R(n) n^{−1}
              = (1/φ(q)) { 1 − Σ_χ χ̄(a) Σ_{ρ_χ} K₁²(ρ_χ) } + O(q^{−2}) ,

with the decay `(7.2) |K₁²(w)| ≤ e^{−(4k−4)λ} min{1, (4(λ²+τ²))^{−1}}` for `w = (−λ + iτ)/log q`.
If `{…}` in (7.1) exceeds a positive constant then `p(q,a) ≤ q^{4k+4}`.

- **No Siegel zero.** The zero-free region used is `(7.3) σ ≥ 1 − 1/(15 log q)`, `|t| ≤ q^ε`,
  from **Miech [13]** — *"Miech had the constant 20 instead of 15"*; the widening to 15 uses
  Miech's argument together with **Burgess's [2] character-sum estimate** for L-functions.
  Zero-counting in the boxes `(7.4) 1 − λ/log q ≤ σ ≤ 1, |t| ≤ 1/log q` and
  `(7.5) 1 − λ/log q ≤ σ ≤ 1, v/log q ≤ t ≤ (v+1)/log q, |v| ≤ q^ε log q` uses **Lemma 3b of
  Jutila [7]**: for a single `L` (mod q), `≤ 3` zeros in (7.4) for `λ ≤ 2` and `≤ e^λ` for
  `λ ≥ 2`; `≤ 2` zeros in (7.5) for `λ ≤ 1` and `≤ e^λ` for `λ ≥ 2`. Then by (7.2) and
  **Theorem 1′** the `R₀`-contribution to (7.1) is at most

      30e^{−(4k−15)/15} + 330∫_{1/15}^{2} e^{−(4k−15)λ}dλ + 10e^{−(4k−16)2} + 120∫_{2}^{∞} e^{−(4k−16)λ}dλ
        < (30 + 330/(4k−15)) e^{−(4k−15)/15} + (10 + 120/(4k−16)) e^{−2(4k−16)} ,

  and the `R_v` with `1 ≤ |v| ≤ q^ε log q` contribute at most

      (π²/12) { (20 + 220/(4k−15)) e^{−(4k−15)/15} + (10 + 120/(4k−16)) e^{−(4k−16)} } .

  Total `< 1` at **`k = 19`**, whence `p(q,a) ≤ q^{4·19+4} = q^{80}`.
- **Siegel zero present** (`β₁ > 1 − 1/(15 log q)`): **by Theorem 2** the wider region
  `(7.6) σ ≥ 1 − 0.3/log q`, `|t| ≤ q^ε` is free of the other zeros; the term `1 − |K₁²(β₁−1)|`
  then dominates the sum over non-exceptional zeros, and the estimation is *less* delicate.

---

## 4. CONSTANTS CENSUS (page-cited)

| constant / parameter | value | where |
|---|---|---|
| `L ≤ 550` (**prior work**, Turán power sums) | 550 | p.45 (Jutila [7],[8]) |
| **`L ≤ 80`** (this paper) | 80 = `4k+4`, `k = 19` | p.47 Thm 3; p.61 §7 |
| Theorem 1 exponent | `(2+ε)(1−α)`, valid `4/5 ≤ α ≤ 1`, `T ≥ 1` | p.46 (1.7)/(1.8) |
| Theorem 1 primitive form | `(Q²T)^{(2+ε)(1−α)}` | p.46 (1.8) |
| Huxley refinement near α=1 | `(Q³T²)^{(1+ε)(1−α)}` | p.54 |
| **Theorem 1′** | `N(λ) ≤ 10·e^{11λ}` | p.47 (1.9) |
| Thm 1′ parameters | `a₁ = 5/2`, `a₂ = 4`, `c = 11/2`, `b = 1 − ε` | p.54 §4 |
| Thm 1′ prefactor | `(π²/6)(c−a₁)²/(b(a₂−a₁))·e^{2cλ}` | p.54 |
| **Theorem 2** | `δ₁ ≥ (1−6δ)·D^{−(2+ε)δ/(1−6δ)}/(8 log D)` | p.47 (1.10) |
| Thm 2 hypotheses | `δ < 1/6`, `β ≤ β₁`, `D = q(|τ|+1) ≥ D₀(ε)`; `3/4 < β₁ < 1` in §5 | p.47, p.56 |
| §6 parameter choice | `Y = D^{2/(1−6δ)+ε₁}`, `R = D^{(1+2δ)/(2−12δ)+ε₂}` | p.59 |
| §6 kernel | `K(Y,δ₁) = δ₁^{−1}(Y^{δ₁}−1) = e^α log Y`, `α ∈ (0, δ₁ log Y)`, wlog `α < 1/2` | p.59 (6.3) |
| the diagonal fallback | `|1 − ρ| ≥ 0.28/log q` | p.59 (6.4) |
| the `r`-average constant | `6/π² · ∏_{p|q}(1+p^{−1})^{−1}` | p.49 Lemma 5 |
| Lemma 5 / (2.8) range condition | `(log q)^{1/2} ≤ log R ≪ log(qT)` | pp.49–50 |
| Lemma 6 detector floor | `|g(ρ,χ)| ≥ (1−ε)(φ(q)/q)(6/π²)log R` | p.50 (2.10) |
| §3 parameters | `R = D^ε`, `z₁ = D^{1/2+7ε}`, `z₂ = D^{1/2+8ε}`, `X = D^{1+12ε}`, `D = qT` | p.52 |
| Lemma 3 divisor bound | `Σ_d |h(d;r,r')| ≤ ∏_{p|r}(p+1)∏_{p|r'}(p+1)` | p.49 |
| convexity input | `L(s,χ) ≪_ε E(χ)/|s−1| + (q(|t|+1))^{(1−σ)/2+ε}`, `0 ≤ σ ≤ 1`, `E(χ₀)=φ(q)/q`, else 0 | p.48 |
| zero-free region used in §7 | `σ ≥ 1 − 1/(15 log q)`, `|t| ≤ q^ε` (Miech had 20; Burgess widens to 15) | p.60 (7.3) |
| Siegel-case region | `σ ≥ 1 − 0.3/log q`, `|t| ≤ q^ε` | p.61 (7.6) |
| §7 box zero counts | `≤ 3` (λ≤2) / `≤ e^λ` (λ≥2) in (7.4); `≤ 2` (λ≤1) / `≤ e^λ` (λ≥2) in (7.5) | p.60 |
| §7 Siegel case split | `δ₁ ≥ q^{−ε}` vs `(q^{1/4}log q)^{−1} ≪ δ₁ < q^{−ε}` | p.61 |
| Lemma 12 branch factors | `½` in (5.4); `θ ∈ [2/3, 2]` in (5.9) | pp.57–58 |
| Lemma 10 error | `O_ε(R q^{1/4} Y^{1/2−β₁+ε})` | p.56 (5.2) |
| Lemma 11 error | `O_ε(R^{−1/2+ε} q^{1/4+ε})` | p.56 |

Notes.
(a) `D₀(ε)` (Theorem 2) and every `≪_ε` constant in Theorem 1 are **never computed**. The
paper's effectivity claim is "in principle" — no numerical `L₀` is produced.
(b) `10` in (1.9) is `π²` rounded up; `8` in (1.10) is a rounding of `≈ 1/0.30`. Both are
generous roundings, so both are safe to quote as printed.
(c) **⚠ FLAG.** The only glyph I could not resolve with full confidence at 600 dpi is the
superscript in `(log q)^{1/2}` (Lemma 5 and (2.8)). The rendering matches the `(qT)^{1/2}`
glyph one line below it in (2.8), so `1/2` is my reading; if a future consumer depends on
this exponent (it is a range condition, not a rate), re-verify. Nothing downstream in these
notes depends on it.

---

## 5. THE CROSSWALK

### 5a. `dh_repulsion_ordered` ↔ Jutila Theorem 2

**Which Jutila object we realize.** `dh_repulsion_ordered` (`Salt/SW/TBalR8.lean:1752`,
landed 2026-07-18 at `f1b92ca`, axiom-clean, registered `Salt/SW/All.lean:305`) realizes
**(1.10) restricted to Jutila's diagonal case `χ = χ₁`** (both zeros belonging to the same real
character), with the δ-dependent exponent `(2+ε)/(1−6δ)` replaced by the **uniform constant
`b = 680`** on a narrower window, and the single `log D` replaced by `(log Q + 2)^{14}`. The
file's own docstring calls it "the reversed-Jutila repulsion contract" (TBalR8.lean:11–16).

| axis | Jutila Thm 2 (1.10) | ours (`dh_repulsion_ordered`) | who is stronger |
|---|---|---|---|
| conclusion | `δ₁ ≥ (1−6δ)D^{−(2+ε)δ/(1−6δ)}/(8 log D)` | `1−β₀ ≥ c·Q^{−b(1−Re ρ)}/(log Q+2)^k` | same shape |
| scale variable | `D = q(|τ|+1)` | `Q = q(|Im ρ|+2)` | ours `+2` (avoids `log ≤ 0`) |
| exponent constant | `(2+ε)/(1−6δ)`; at `δ = 1/17` this is `34/11 ≈ 3.09` | `b = 680` | **Jutila, by ≈ 220×** |
| numerator constant | `1−6δ ≥ 11/17 ≈ 0.647` at `δ = 1/17` | `c = 2^{−250} ≈ 5.5·10^{−76}` | Jutila (a constant, not a rate) |
| log power | `1` (`8 log D`) | `k = 14` | Jutila |
| window | `δ < 1/6` ⟺ `σ > 5/6 ≈ 0.833` | `16/17 ≤ σ`, i.e. `δ ≤ 1/17 ≈ 0.0588` | **Jutila** (ours ≈ 0.94 floor) |
| τ-range | any real `τ` | `ρ.im ≠ 0`, `|Im ρ| ≤ 1` | **Jutila** |
| characters | `χ₁` real non-principal; `ρ` from **any** `χ` mod `q` | one real primitive `χ` (`χ² = 1`, `χ ≠ 1`), **both zeros of the same `L(·,χ)`** | Jutila (ours = his diagonal case, which is what HB consumes) |
| primitivity | not required | `χ.IsPrimitive` required | Jutila |
| real zero | `β₁ = 1 − δ₁`, `3/4 < β₁ < 1` in §5 | `1/2 < β₀ < 1` | ours |
| ordering | `β ≤ β₁` | `ρ.re ≤ β₀` | identical (this is the `T-BAL-UNORDERED` item; see wp2 audit §1b) |
| threshold | `D ≥ D₀(ε)`, **`D₀` never computed** | none — the contract is unconditional in `q ≥ 2` | **ours, and this is the point** |
| status | prose, 1977 | Lean 4, kernel-checked, 3 axioms | **ours** |

**Where our witnesses sit relative to his.** Strictly inside, and much more expensive:
our operating window `σ ∈ [16/17, 1)` is a sub-interval of his `σ ∈ (5/6, 1)`; our
`|Im ρ| ≤ 1` is a sub-case of his τ-uniform statement; our character hypothesis is his
diagonal branch only. Against that, we pay `b = 680` where he pays `≈ 3.09`, `k = 14`
where he pays `1`, and `c = 2^{−250}` where he pays `0.647`. The compensation is
categorical rather than numerical: his `D₀(ε)` is an uncomputed ineffective threshold, and
ours does not exist. The `b = 680` grade was already ruled absorbable by the 7/19 T4 ledger
(fleet-meeting-0803-brief.md:35–39: zero-dependent factors cancel exactly in the main term;
the true charge clears by ≈ 3500 orders at the engine threshold); the residual is the
bounded arithmetic audit **T-BAL-BUDGET / N0**, not a redesign.

**One structural echo worth recording.** Jutila's Theorem-2 proof and our DH-1..4 design were
arrived at independently and share the detector: his `a_n = Σ_{d|n} χ₁(d)` (p.54) *is* the
house's `1∗χ₁`, his mollifier is the pseudocharacter `f(n) = μ(n)2^{−ω(n)}n`, and his main term
`Γ(δ₁)Y^{δ₁}` at the Siegel scale is the same "small `δ₁` ⟹ large main term" inversion our
`H_lower`/`L1_lower_siegel` chain runs. The route diverges at the mollifier: he squares an
`r`-averaged pseudocharacter sum; we use the Selberg-weight machinery (`selWeight`, `SelOpt`).

### 5b. The fulcrum campaign's repulsion consumer chain

⚠ **Naming note:** the tasking named "the L2/L5 links". The recorded consumption ledger
(`docs/exploration/fulcrum-pass3-records/pass3_t4.md:38–50`) has no L5 repulsion link, and L2
is not a direct consumer. The actual chain is **L3-ii → (L2 multiplies) → L7**:

- **L3-ii — the only direct consumer.** HB Lemma 3 (pp.206–207) consumes the D–H repulsion as
  `r₀ ≫ L^{−1} log η`, `η := ((1−β₀)L)^{−1}`, quality **LOG-only**, and the ledger names
  Jutila Thm 2 as its source and `dh_repulsion_ordered` as "exactly this artillery, in-house,
  log-shape". Constants absorbable; **shape not** — log-order is what D–H-type methods give,
  which Jutila's (1.10) confirms at the source (the `Y^{δ₁}`/`K(Y,δ₁)` inversion cannot produce
  a polynomial-in-η rate). Lean slot: `Salt.HB.PretenseSum` (`TransferFull.lean:183`), road node
  **N3**.
- **L2** — HB Lemma 2 (pp.201–203), the `e^{Az₀}` amplification: consumes no repulsion directly;
  it *multiplies* L3's rate. Absorbable at exponent-constant grade.
- **L7** — HB Lemma 7 (pp.207–210), `L′/L(1,χ) = ηL + O(L(log η)^{−·})`: fed by L3, its own
  zero-sum errors already polynomial in η, so it adds no independent wall. Road node **N4**.
- **L5/K** — HB Lemma 5 / §§5–7 Kloosterman (pp.210–223): audited to consume **no η at all**.
  If "L5" was meant literally, the answer is that it has no repulsion link.
- **Density side.** Jutila Theorem 1 is HB's other consumed theorem; on our road it is node
  **N2, the crude zero-density estimate** `N(σ,T,χ) ≪ (qT)^{D(1−σ)}` with `D ≤ 83` tolerated
  (`3D < 250`) — i.e. we may be ~40× cruder than Jutila's `2+ε` and still clear the window
  `q^{250} ≤ x ≤ q^{500}`. Jutila's own §3 route (pseudocharacter + Graham + Halász +
  the ξ,η-integration) is therefore **not** something we need to reproduce.
- **Theorem 1′ has a landed analogue already.** `N(λ) ≤ 10e^{11λ}` counts L-functions with a
  zero within `λ/log D` of `σ = 1`; our `LFunction_zero_count_near_one`
  (`Salt/SW/ZeroCountNearOne.lean:98–102`, `C = 7200`, zeros **with multiplicity** in
  `closedBall 1 r` for `0 < r < 1/2`, bound `C(1 + r·log(q+2))`) is the per-character
  radius-resolved count, which is the object HB's L3-iii ("Prachar disc count `≪ 1 + rL`")
  actually consumes. Jutila's Theorem 1′ is the *summed-over-χ, exponential-in-λ* form and is
  not needed by our road as currently priced — worth knowing before anyone stages it as a node.

### 5c. ⚠ CONTRADICTIONS WITH OUR RECORDED READING (`s3-hb3-design.md:921–956`)

Three items. One is a real error, one is a scope slip, one is a gap.

1. **⚠⚠ WRONG — the Theorem-2 proof apparatus.** s3-hb3-design.md:951–953 records:
   *"Jutila's own Thm 2 proof is NEW (not Turán power-sum; via the Graham/Halász lemma
   apparatus)"*. The "not Turán power-sum" half is **correct**. The "via the Graham/Halász
   lemma apparatus" half is **wrong**: Lemma 4 (Graham) and Lemma 7 (Halász) are §2 lemmas
   consumed in **§3, the proof of Theorem 1**. Theorem 2's proof (§5 Lemmas 9–12 + §6) uses
   none of them. Its apparatus is: the `1∗χ₁` detector `a_n`, the pseudocharacter mollifier
   `f = μ·2^{−ω}·n`, the factorization `G_{r,r'} = L(s,χ)L(s,χχ₁)P_{r,r'}Q` (5.1), Mellin +
   contour shift to `Re s = 1/2 + ε` with the `Γ`-pole cancelled by the zero `β₁`, Hölder +
   mean-fourth-power for Lemma 11, and the `n = 1`-term dichotomy of Lemma 12.
   **Consequence for the design record:** the note at s3:951–956 ("house reads the proof section
   IF the in-flight spike returns YELLOW/RED") pointed a future reader at the wrong sections.
   Anyone re-deriving the repulsion from Jutila should read **§5–§6, not §2–§3**. Turán *does*
   appear in the paper, but only in §7 (the kernel `K(w)`), on the road from the two theorems to
   `L ≤ 80` — so "not Turán power-sum" is right about Theorem 2 and would be wrong as a
   statement about the paper as a whole.
2. **⚠ SCOPE SLIP — `L ≤ 550`.** The staging tasking (and the sense in which the paper is
   sometimes cited here) attaches `550` to this paper. `550` is Jutila [7],[8] (1969/70),
   superseded here by `L ≤ 80` (Theorem 3, p.47). See §0.1.
3. **GAP (not an error) — Theorem 1′ was never recorded.** s3-hb3-design.md:931–950 records
   Theorems 1 and 2 but not Theorem 1′ (1.9), which is the form §7 actually consumes, and which
   is the near-1 zero-*count* whose in-house analogue we already have (§5b). Worth adding to any
   future WP2 node table.

**Verified as CORRECT in our record** (no change needed): the (1.10) formula transcription,
character-by-character, including the `(1−6δ)` numerator, the `(2+ε)δ/(1−6δ)` exponent and the
`8 log D` denominator (s3:941); the `4/5 ≤ α ≤ 1` range and `(qT)^{(2+ε)(1−α)}` shape of
Theorem 1 (s3:931–933); the page assignment of the effectivity remark to **p.47** (s3:947–950)
and its wording; and the "not Turán power-sum" reading of Theorem 2 (s3:951).
Also confirmed: the inversion note at s3:942–946 — (1.10) is a **lower bound on `δ₁` given
another zero**, and its friendliness to Lean is exactly what the landed contract exploits.

---

## 6. REFERENCE LIST (as printed, pp.61–62) — for provenance tracing

[1] Barban–Vehov, Trudy Moskov. Mat. Obsc. 18 (1968) 83–90 (transl. 91–99) ·
[2] Burgess, *On character sums and L-series II*, Proc. LMS 13 (1963) 524–536 ·
[3] Fogels, Acta Arith. 11 (1965) 67–96 · [4] Gallagher, Invent. Math. 11 (1970) 329–339 ·
[5] **S. Graham, *An asymptotic estimate related to Selberg's sieve*, to appear** ·
[6] Huxley–Jutila, *Large values of Dirichlet polynomials IV*, Acta Arith. 33 (1977) 89–104 ·
[7] **Jutila, *On two theorems of Linnik…*, Ann. Acad. Sci. Fenn. AI 458 (1969), 32 pp.** ·
[8] **Jutila, *A new estimate for Linnik's constant*, Ann. Acad. Sci. Fenn. AI 471 (1970), 8 pp.** ·
[9] **Jutila, *On Linnik's density theorem*, unpublished** · [10] Knapowski, Publ. Math. Debrecen 9 (1962) 168–178 ·
[11],[12] Linnik, Mat. Sb. 15 (1944) 139–178 and 347–368 · [13] **Miech, *A number-theoretic constant*, Acta Arith. 15 (1969) 119–137** ·
[14] Montgomery, *Topics in multiplicative number theory*, LNM 227 (1971) ·
[15] Montgomery–Selberg, *Linnik's theorem*, unpublished · [16] Motohashi, Publ. RIMS 222 (1974) 9–50 (in Japanese) ·
[17] **Motohashi, *On the zero-density theorem of Linnik*, to appear** · [18] Prachar, *Primzahlverteilung*, Springer 1957 ·
[19] **Selberg, *Remarks on sieves*, Proc. 1972 Number Theory Conf., Boulder, 205–216** ·
[20] **Turán, *On a density theorem of Yu. V. Linnik*, Magyar Tud. Akad. Mat. Kutató Int. Közl. 6 (1961) 165–179**.

Bolded = load-bearing for the two theorems we consume. Note that three of them ([5], [9], [17])
were **unpublished or forthcoming** at the time; [15] never appeared. Any future attempt to
reconstruct Theorem 1's constants from the literature must go through Graham [5] — which
appeared as *An asymptotic estimate related to Selberg's sieve*, J. Number Theory 10 (1978)
83–94 (**MEMORY**, not read this session; verify before citing).
