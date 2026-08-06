# TAU-SHARP — WAVE TS-0, THE REFUTER PASS

**Date:** 2026-08-06 morning. **Freeze under attack:**
`docs/exploration/tau-sharp-scout-dossier-0805.md`.
**Method:** four parallel read-only Opus refuters, one per kill-check, verdict
vocabulary CONFIRMED-FATAL / CONFIRMED-REPAIRABLE / UNFOUNDED, house rule
"a refutation is only worth reporting if it names the byte or the arithmetic".
**Executor seat** (mathematics), per the verify-posture law (catch #98).

| kill-check | subject | overall |
|---|---|---|
| K1 | `htriv` in the deep branch; S1's scope | **REPAIR-THEN-FIRE** |
| K2 | the shortfall-∝-w conversion at all `w` | **REPAIR-THEN-FIRE** |
| K3 | the consumer's Range-A ledger / the door | **HOLD** |
| K4 | the γ-floors and the arm arithmetic | **REPAIR-THEN-FIRE** |

**EXECUTION RULING (this seat, execution layer only):** TS-1 and TS-2 **FIRE
with the K1 + K4 repairs applied**. TS-3 and the §6 design ruling **HOLD** —
K3 is a statement-layer kill and belongs to the design seat / JYH, not to an
executor. Nothing below changes a blueprint statement.

---

## 0. THE ONE FINDING THAT OUTRANKS THE REST

**The freeze's central law is off by one power of `L`, and the word ABSOLUTE
does not survive.** Found INDEPENDENTLY by K1, K2 and K3 (three separate
derivations, plus the conductor's own before any refuter reported) — so this
is not one refuter's opinion.

The freeze (§0(ii), §4, §3's consumer read, §6's design ruling) asserts

> the L-power of the regime binder is `(1+ξ)(k − 1)`, hence **k = 1 makes the
> threshold ABSOLUTE — `η ≤ c^{1+ξ}`, no L at all — for any ξ**,

and claims §D2's own numerals confirm it "exactly: 26 = 2·(14−1)".

Derive it instead from §D2's *literally stated* `hN+`
(`n4b-design-0805.md:207`): `log(1/(1−β₀)) ≥ (1+ξ)·(log(1/c) + k·log(log Q+2))`.
With the road's own `η := ((1−β₀)·log q)^{−1}` (`n4b-design-0805.md:52`) and the
freeze's own approximation `log(log Q + 2) ≈ log L` (freeze:296-300):

```
    log η  ≥  (1+ξ)·log(1/c)  +  [ (1+ξ)k − 1 ]·log L
```

The lone `−log L` comes from the `η ↔ (1−β₀)` conversion and is **never
doubled** by the margin; the margin multiplies the block `log(1/c) + k·log L`.
The freeze subtracts `(1+ξ)·log L` where only ONE `log L` exists. The two laws
agree only at `ξ = 0` — and they diverge exactly where the headline lives:

| | freeze's law `(1+ξ)(k−1)` | honest law `(1+ξ)k − 1` |
|---|---|---|
| k = 14, ξ = 1 | 26 | **27** |
| k = 1, ξ = 1 | 0 — "ABSOLUTE" | **1** — `η ≳ c^{−2}·L` |

§D2's own two numerals are **mutually inconsistent**, and the freeze adopted the
reading that makes its door claim true: `:214`'s `e^{1264+26 log L}` carries the
DOUBLED `log(1/c)` (an ξ=1 shape) but the `(k−1)` L-power of `:218`'s ledger form
`(e^{632}·L^{13}/η)^θ` (an ξ=0 shape). The "26 = 2·13" match is a coincidence of
that fusion. The constant is right (1264 ≈ 2·631.58); the exponent is not.

**What survives:** the `k : 14 → 1` SCOPE is still a real and large win — the
L-power falls from 27 to ξ. **What does not:** "ABSOLUTE … for any ξ", and with
it §6's design ruling as worded. ξ cannot be sent to 0 for free, because the
road's own `θ = s·ξ/((1+ξ)·b)` is proportional to ξ.

**REPAIR (design-layer, NOT taken by this seat):** bank the law as
`(1+ξ)k − 1`; state the k=1 threshold as `η ≤ c^{1+ξ}·L^{−ξ}`, absolute only in
the ξ→0 limit; correct `n4b-design-0805.md:214` to `e^{1263+27·log L}`; and record
that `:218` is the ξ=0 form whose θ is not `:207`'s θ — the two lines are
different regimes and must not be quoted together.

---

## 1. K1 — `htriv`, and S1's real scope

**The guard claim: UNFOUNDED (the freeze is right).**
The split is `by_cases htriv : 1 / (40 * L₂) ≤ u` at `TBalTall.lean:1725`; the
deep bullet opens at `:1734` and `rw [not_le] at htriv` (`:1735`) gives exactly
`htriv : u < 1/(40·L₂)`. The deep branch is one contiguous tactic block
`:1735–2062` with no `clear`/`clear_value`, so htriv is live at `:1769` and at
every later use of the ray. Twin identical at `TBalR8.lean:1420/:1430`.
The kill-check's premise ("needs `L₂² ≥ 40/18`") was a **mis-derivation by the
conductor**: from `u < 1/(40 L₂)` and `L₂ > 0`, multiply by `L₂` — `u·L₂ < 1/40
< 1/18`. No `L₂²` occurs anywhere, and no lower bound on `L₂` is needed (though
`hL₂ge2 : 2 ≤ L₂` is in scope at `TBalTall:1715` / `TBalR8:1414` regardless).

**Consumer enumeration.** `hc_t9` is used at exactly two sites —
`TBalTall:1769`, `TBalR8:1463` — both `le_trans huL2c hc_t9`, both inside the
deep bullet. `huL2g` at exactly two — `TBalTall:1964`, `TBalR8:1651-1652` —
both feeding `tbal_hscale`, whose hypothesis is literally `u·L₂ ≤ 1/18`
(`TBalR8:1003`), discharged by the stronger `1/40`. **So `hc_t9 : c ≤ 1/18` is
genuinely redundant today in BOTH assemblies.**
*Caveat worth banking:* the 1/18 arm was never binding — the same min already
carries `1/576` (log 576 = 6.36 > log 18 = 2.89) — so deleting `hc_t9` buys
**0.00** in log(1/c) while paying the full min-tower re-index cost. Do not spend
on it.

**S1's c-hypothesis: the freeze is right.** `tbal_tau_le_split` takes NO
hypothesis on `c` — the literal `2^{−250}` is hard-wired in the STATEMENT
(`TBalR8:45`). Its proof uses the literal exactly three times: `hclt1 : 2^{−250}
≤ 1` (`:51-52`), `hcpos` (`:50`, used at `:77`), and `hstep` (`:71-77`) which
needs only `40·c·Q^{−680w} ≤ 8192` given `hL13` (`:58-63`). Honest hypothesis
set: `(hc0 : 0 ≤ c) (hc1 : c ≤ 1)`. The freeze's "c ≤ 204.8 suffices" is
byte-accurate, and `hc1 : c ≤ 1` is already derived independently of the deleted
arm (`le_trans hc_t5 …`, `TBalTall:2157` / `TBalR8:1834`), so S1 orphans nothing.
Nothing outside the deep branch consumes the smallness of `c`: after
`clear_value c` the witness is existential (`TBalTall:2162` / `TBalR8:1836`) and
every downstream consumer takes `c` abstractly with only `0 < c` and `hN`, which
is **monotone-easier as c grows**. Enlarging `c` is safe in every direction.

### ⛔ THE KILL — S1's EDIT LIST OMITS THE ENTIRE TWIN

Freeze §2.4 says `hc_t1` is "consumed at EXACTLY ONE site: the trivial branch,
`TBalTall.lean:1730-1733`". **FALSE at the bytes.** There is a second, identical
site at **`TBalR8.lean:1425-1428`** (`exact mul_le_mul_of_nonneg_right hc_t1
hbase_nn` at `:1427`), inside `dh_repulsion_inst` (`TBalR8:1373`), the body of
the **LANDED `dh_repulsion_ordered`** (`TBalR8:1752`) — which is consumed
downstream at `TauExt.lean:353` (`boxZeros_re_le_unit_box`) and audited in
`Salt/SW/All.lean:313`.

S1's edit list names only `TBalTall:1684, :2109, :2124` and the `:1730-1733`
block. **An executor following S1 literally restates `tbal_tau_le_split` and
leaves `TBalR8:1422` applied at the old arity: `lake build` fails and a landed
theorem with live consumers goes red.**

**S2 REPEATS THE SAME OMISSION.** Four of the five row caps are shared verbatim
by both assemblies — `row_rho_main_cap`, `row_A_cap`, `row_1x_cap`,
`row_Eβ_cap` are applied at `TBalR8:1709, :1723, :1726, :1730` AND at
`TBalTall:2021, :2035, :2038, :2042`; only the Eρ row is forked
(`row_Eρ_cap` vs `row_Eρ_cap_tall`, `TBalTall:1570`). S2 restates the `hg` of
exactly these shared caps and then says "the assembly needs only new `pinv`
numerals" — *singular*. It is **two** assemblies: TBalR8's hg-block `:1660-1707`
with its **11-fold** min at `:1776-1833`, and TBalTall's `:1973-2014` /
**10-fold** min at `:2105-2156`. §5 is internally inconsistent about this: S3
does price the twin (freeze:338); S1 and S2 do not.
Note further: TBalR8's KEβ/KEρ arms carry the **free variable `Z₀`**
(`TBalR8:1387-1388`), so the freeze's §3 arm table — computed at the tall
numerals (`Z₀ ⇝ 5`, `636`) — **does not price the TBalR8 tower at all**.

**S1 RE-PRICED.** Class A: accurate (every edit is numeral/projection
bookkeeping; every miscount is a kernel type error, so no soundness exposure).
"No statement outside TBalR8/TBalTall": accurate. "~15 ln": **off by ~8×**.
Deleting the head of a 10-fold and an 11-fold nested `min` shifts every
hand-built projection chain below it (`hc_t2` is two deep, `hc_t10` is nine
deep). Ledger: TBalTall ≈ 52 changed lines, TBalR8 ≈ 71 — **≈ 123 lines, 2 files,
5 declarations** (`tbal_tau_le_split`, `dh_repulsion_inst`,
`dh_repulsion_ordered`, `dh_repulsion_inst_tall`, `dh_repulsion_tall`).

**THE PREFERRED REPAIR (adopted for TS-1): do NOT delete the head arm.**
Replace the head numeral `2^(-(250:ℝ))` by `1/40` in both towers
(`TBalTall:2105`, `TBalR8:1776`), replace `hp1` by `by norm_num`
(`TBalTall:2109`, `TBalR8:1780`), and restate `tbal_tau_le_split` once,
generalised in `c` (and `b`, `k`):

```lean
lemma tbal_tau_le_split {Q b w c k : ℝ} (hQ : 1 ≤ Q) (hb : 0 < b) (hw : 0 < w)
    (hc0 : 0 ≤ c) (hc : c ≤ 1/40) (hk : 1 ≤ k) :
    c * Q ^ (-(b*w)) / (Real.log Q + 2) ^ k ≤ 1 / (40 * (Real.log Q + 2))
```

This (a) keeps every `le_trans (min_le_right _ _) …` chain **index-stable** —
the whole point; (b) leaves the arm inert in log(1/c) (`log 40 = 3.69`, dominated
by the surviving `1/576` arm at 6.36), so the **full 173.29 is still realised**;
(c) is already S4-shaped, so TS-3 never re-touches this lemma. **≈ 20 lines.**

---

## 2. K2 — the shortfall-∝-w conversion

**THE MECHANISM SURVIVES; THE NUMERALS DO NOT.**

`ray_pow_bound` (`TBalR8:368-372`) is
`… (hα : α ≤ 680*w*γ) (hε : ε ≤ 14*γ) : Q^α · u^γ · L₂^ε ≤ c^γ` — **`b = 680`
and `k = 14` are HARDCODED numerals in the statement**, not parameters; the proof
needs exactly `Q^(α − 680wγ) ≤ 1` (`:386`) and `L₂^(ε − 14γ) ≤ 1` (`:388`).

For the ρ-main row the shortfall `ε − kγ = m·w` at k=1 really is ∝ w, so after
`L₂^{mw} ≤ C^{mw}·Q^{δ'mw}` the hα demand is `w·(a + δ'm − bγ) ≤ 0`, which
**divides by w > 0**: `a + δ'm ≤ b(1 − m·w₀)`, worst at `w₀ = 1/17`, w-free, and
needs no ZFR floor. **Legitimate uniformly on `(c₀/log Q, 1/17]`** — K2 CONFIRMS
the freeze here. The extra constant is bounded (`C^{mw} ≤ C^{m w₀}`) and costs
`(m w₀/(1 − m w₀))·log C = 2.4·log C` on the ρ-main arm.

**⛔ THE NUMERALS FAIL.** At the freeze's own S3+S4 target `(a,m,b) = (51,12,174)`:
`b(1 − m w₀) = 174·(5/17) = 51.176`, so `δ' ≤ 0.0147` — while §4:279 and §5:350
name **`δ' = 1/2`**. `51 + 12·(1/2) = 57 > 51.176`: **hα FAILS.** Feasible:
`δ'=1/2 ⇒ b ≥ 193.80`; `δ'=1 ⇒ b ≥ 214.20`. §3's table row
"`+ S4 (k → 1) | 51.74 | 174 | 1`" is **nowhere on the feasible curve**: with the
freeze's own conversion constant `(1/δ'+2)`, the best admissible point gives
`log(1/c) = 57.81` at `b = 214.20` (binding arm **Eβ**, not the ZFR row); forced
to `b = 174` it gives `77.11`. K2's arm model reproduces the freeze's §3 table
exactly at every k=14 row (86.23 / 55.71 / 51.74), so the divergence is in S4's
pricing, not the calibration.

### ⛔ NEW WALL W4 — a δ' ceiling the freeze never names

S4 move (iii) converts the WHOLE `L₂^{10}/L₂^{11}` to `Q^{10δ'}/Q^{11δ'}` — which
adds exactly the **constant Q-power** that catch R8b-B (`flags.md:11253-11256`)
forbids. Exact rows (`TBalR8:791-794` Eβ; `TBalTall:1599-1602` Eρ-tall):
`α = (1/2 or 5/2) + 12 + a(1/2−σ)`, so the w-free part is
`(1/2 or 5/2) + g − a/2 + εδ'` while RHS `= b·w·γ → 0` as `w → 0+`. Hence a
ceiling **independent of b**:

```
    δ' ≤ (a/2 − g − 5/2)/11   (Eρ)        δ' ≤ (a/2 − g − 1/2)/10   (Eβ)
```

At the LANDED `a = 104` these are `3.409 / 3.950` — comfortable, so the freeze's
"α_Eρ ≤ −31.4, the Q-exponent is free" defence **DOES close** (both endpoints
verified: worst margin −32.008 at w→0+; at w = 1/17, lhs = −26.5 vs rhs = 123.5).
**BUT S3 (a: 104 → 51) collapses the ceiling to `δ' ≤ 1.000` (Eρ) / `1.300` (Eβ)**,
and at `δ' = 1` the Eρ w-free part is **exactly zero** (saved only by `w > 0`) —
a knife edge that any future re-cut of `g = 12` or of the tall `+2`
(`TBalTall:1565`) breaks.

**S3 AND S4 ARE ANTI-SYNERGISTIC**, not merely co-dependent as §6 says: S3 cuts
`γ_Eβ` from 2.0865 to 1.1141, **tripling** the per-unit cost of the conversion.
The freeze prices the conversion only against Eρ at m=14 (`11·log4/3.0865 =
4.94`); post-S3 the Eβ cost is `10·log4/1.1141 = 12.44`, and at `δ' = 1/2` the Eβ
arm becomes **60.4 and BINDING** — overturning §6's "the BINDING arm is the ZFR
residue row".

### ⛔ THE b-FLOOR NAMES THE WRONG ROW (§2.6 correction)

§2.6 claims `b` is fixed by the ρ-main row alone, `b ≥ a/(1 − m·w₀) = 589.33`,
landed slack `680/589.33 = 1.154`. But **`row_A_cap`'s `ray_pow_bound` call
(`TBalR8:534-540`) carries `δ_A = 1/50` INSIDE γ**: `α = 104(β₀−σ)`,
`γ = 49/50 − 14(β₀−σ)`, and at the admissible corner `u → 0+` the hα at `:538`
becomes `104 ≤ 680(49/50 − 14w)`, i.e.

```
    b ≥ a/(1 − δ_A − m·w₀) = 104/0.156470 = 664.66
```

Numerically at `w = 1/17, u → 0`: lhs 6.1176 vs rhs 6.2588 — a **2.3% margin**,
versus the ρ-main row's 15.4%. **True landed slack is 680/664.66 = 1.023, not
1.154**, and the post-S3 b-floor is 186.05 (k=14) / 214.20 (k=1 at δ'=1), never
173.4. Consequence: §2.6/§3's "b: 680 → 174 multiplies θ by 3.9" is wrong — the
multiplier is `680/210.12 = 3.24` and **θ = 0.595, not 0.72**.

### S4 RE-PRICED — class C, 600–900 ln jointly with S3

Missing breakage site: `row_A_cap`'s `hulogY` guard (`TBalR8:499-510`) calls
`ray_pow_bound` at `(α,γ,ε) = (0, 49/50, 1)`; at k=1 hε reads `1 ≤ 49/50` —
FALSE — and the shortfall `1/50 = δ_A` is a **constant**, not ∝ w. Repairable
(a second piece-split inside the same lemma) but **not on S4's four-move list**.
Surface: `680` at 63 sites, `(14 : ℝ)` at 101, `104` at 126, across
`dh_repulsion_inst` (378 ln) + `dh_repulsion_inst_tall` (405 ln); `row_A_cap`
alone is 148 ln and needs two piece-splits, two new `hg` thresholds, two new
c-arms.

**MANDATORY PREP STEP (K2's repair, banked for TS-3):** parametrize
`ray_pow_bound` over `(b, k)` with `0 < b`, `0 ≤ k`, replacing the 680/14
numerals in its STATEMENT, and re-thread the existing proofs at `k = 14, b = 680`
— a pure refactor whose exit test is "both contracts build unchanged". Then
S3+S4 move witnesses only, not statements.

Other K2 repairs for the design seat: replace S4's conversion lemma
`L₂ ≤ (1/δ'+2)Q^{δ'}` with the sharp `Real.log Q + 2 ≤ C(δ')·Q^{δ'}`,
`C(δ') = sup_{Q≥4}(log Q+2)/Q^{δ'}` (`= 0.9725` at `δ'=0.9`, attained at Q=4) —
worth **5.8** on log(1/c) for two lines; recommended operating point
`δ' = 0.9, b ≥ 210.12, log(1/c) = 51.67, θ = 0.595`; restate §6's deliverable as
`(b, c, k) = (~210, e^{−52}, 1)`.

---

## 3. K3 — the consumer's Range-A ledger. **HOLD.**

**(a) The L-power: NEITHER of the offered readings.** See §0. From
`repulsionCeiling` (`TauExt.lean:177-178`) alone the L-power is `(k−1)`, with **no
ξ in it** — ξ is a consumer-side margin, absent from TauExt entirely. Applying
§D2's margin multiplies the block `log(1/c) + k·log L`, not the lone `−log L`.
Honest law: `(1+ξ)k − 1`.
K3 adds a correction the freeze missed: the residual `k·[log(log Q+2) − log L]`
is **not o(1)** at the landed window — at `L = 250` and the consumer's real base
`Q = q(T₀(u)+3)`, `log Q = 316.3` and `log(log Q+2) = 5.763` vs `log L = 5.521`,
so the residual is **+3.4** in the binder at k=14 (+0.24 at k=1). The freeze
prices it at the **RETIRED** height `efHeight q = (log q+2)^4` (`TauExt:315`)
rather than the design's landed `T₀(u) = (log(qu)+2)^6`
(`n4b-design-0805.md:202`, `Lemma7EF.lean:794`).

**(b) §D2's numerals: 1264 confirmed verbatim (`:214`), 26 WRONG.** Detailed in
§0 above.

**(c) ⛔ CONFIRMED-FATAL — a k-INDEPENDENT L-POWER SURVIVES.** Two independent
sources, both byte-grounded.

1. **The margin.** By (a), at k=1 the binder is `η ≳ c^{−(1+ξ)}·L^{ξ}`. ξ = 0 is
   not available — the freeze's own `θ = s·ξ/((1+ξ)·b)` vanishes at ξ=0, so the
   consumer gets no saving at all. At §D2's own ξ=1 the surviving power is `L^1`.
2. **The ledger's polylog prefactor, read at the LANDED consumer.**
   `efEnvelope_le_ledger_sharp` (`Lemma7EF.lean:2624-2632`) prices the Range-A
   erased-spend row as `10^3·M^3·N·u^{bceil−1}`, `M = log(qu)+2`,
   `N = log q + 11·log M`, against the consumer's target grade `(m+255)/log u`
   (`:2907-2908`) inside the byte-fixed window `250·log q ≤ log u` (`:2844`).
   That forces `𝒩 ≥ (b/250)·(5·log L + 29)` — a demand that **grows like log L**
   and is **entirely k-independent**. Hence
   `log η ≥ log(1/c) + [(k−1) + 5b/s]·log L + O(1)`.
   At the freeze's own TS-3 target `(k=1, b=174, log(1/c)=52)`: required `log η`
   = 102.2 at L=250, 104.5 at L=10⁴, 120.0 at L=10⁶, 168.1 at L=10¹² — i.e.
   `η ≳ e^{~100}·L^{~3}`, **q-GROWING**.

**THE DOOR.** `FulcrumQualityMin C` (`Salt/Fulcrum/Basic.lean:61-64`) is
`‖1−ρ‖·(C·log q) ≤ 1` with `C` a FIXED real, and `imsz_gives_fulcrum_witnesses`
(`Salt/Fulcrum/Gadget.lean:128-131`) supplies it for any **constant** `C > 0`. A
binder `η ≳ L^{~3}` is not expressible as `FulcrumQualityMin C` for any `C`, so
`not_fulcrum_implies_noSiegelZeros` (`Dichotomy.lean:82`) never fires.
**§6's design ruling is false as worded, and TS-3's stated deliverable cannot be
produced by moving `k`. The lever is `b/s`, not `k`** — the surviving power is
`Θ(b/s)`, which S3's `b: 680 → 174` improves 3.9×, and only a Jutila-grade
`b ≈ 3.09` would drive it near zero. Even then it is positive: **ABSOLUTE is
unreachable in this skeleton by ANY (b, c, k).**

**(d) "no consumer exists yet": FALSE at the bytes.** Four kernel-landed
consumers, three in the road's own file — `Lemma7EF.lean:661`
(`re_le_repulsionCeiling_of_ne`), `:696` (`exists_repulsion_ceiling_of_ne`, which
`obtain`s `dh_repulsion_tall` at `:709`), `:748` (`psiDefect_norm_le_rangeA`) —
plus `TBalTall.lean:2199` (`boxZeros_re_le_at_efHeight`). The freeze also names
the **wrong prefactor** as the risk: `efZeroSumM_spend_at_repulsion`'s
`4110·(log q+2)^5` (`TauExt:320`) is the count-form route **retired by design D4**
(`n4b-design-0805.md:236-238`); the operative prefactor is `10^3·M^3·N`
(`Lemma7EF.lean:2632`).
*(Reconciles with this seat's own grep: `dh_repulsion_tall` has no consumer in
`Salt/SW/`; the consumers are in `Salt/HB/`.)*

### K3's two unassigned kills that bear on the WAVE PLAN

- **THE STONE TABLE MEASURES THE WRONG QUANTITY FOR THE DOOR.**
  `imsz_gives_fulcrum_witnesses` delivers `FulcrumQualityMin C` for **every**
  constant `C > 0`, so the door is indifferent to the SIZE of `log(1/c)` —
  `e^{631.6}` is as acceptable as `e^{52}`, provided it is a constant. The
  door's gate is purely the **L-power**. Therefore S1, S2, S5, S6, S8 and most
  of S3 — i.e. **all of TS-1 and all of TS-2** — buy the N11 door **exactly
  nothing**. They buy explicit-constant hygiene and (through `b`) the θ ledger.
- **TS-3's PREMISE IS UNVERIFIED.** The landed end-to-end consumer
  `logChiSum_tendsto_zfr_hundred` (`Lemma7EF.lean:3136-3149`) closes HB's (4.12)
  tail at `K = 100` using the CLASSICAL ZFR ceiling `efZfrCeil` at every `u`, and
  `logChiSum_tendsto_zfr`'s docstring says in the open that "`hN+`, `hord` and the
  `q^{250} ≤ X` edge do NOT appear — they are Range-A's". **On the landed bytes
  the repulsion contract is currently not load-bearing for Lemma 7's tail at
  all.** Before ~300 Lean lines go into TS-3, the road must state which consumer
  obligation the repulsion ceiling discharges that `efZfrCeil` cannot. (It cannot
  discharge `hreal′`: `dh_repulsion_tall` excludes real zeros by hypothesis,
  `ρ.im ≠ 0`.)

---

## 4. K4 — the γ-floors and the arm arithmetic

**⛔ TWO OF THE THREE γ-FLOOR NUMERALS ARE INADMISSIBLE — the freeze rounded the
WRONG WAY.** (Independently reproduced by this seat before K4 reported.)

| row | exact γ(σ) | infimum (at σ = 16/17) | freeze claims | admissible? |
|---|---|---|---|---|
| Eρ (`TBalTall:1644`) | `14σ − 1009/100` | **5247/1700 = 3.0864705…** | 3.0865 | **NO** (−2.941e−5) |
| Eβ (`TBalR8:816`) | `14σ − 1109/100` | **3547/1700 = 2.0864705…** | 2.0865 | **NO** (−2.941e−5) |
| A (`TBalR8:542`) | `49/50 − 14(w−u)` | **133/850 = 0.1564705…** | 0.15647 | yes (+5.9e−7) |

Each γ is a function of σ **alone** for Eρ/Eβ (no w, u, m, L₂ dependence — w
enters only via `ray_pow_bound`'s hα), strictly increasing in σ, so the infimum
sits at the closed left endpoint `hσlo : 16/17 ≤ σ`. **With `γ₀ = 3.0865` the
side goal is FALSE at σ = 16/17 and no `nlinarith` will close it — an executor
handed 3.0865 burns its budget on an unprovable goal.**
For the A row the infimum is the corner `(w,u) → (1/17, 0+)`, **not attained**
(u > 0 strictly), so 0.15647 is provable — but on a 5.9e−7 margin.

**REPAIR (adopted for TS-2): use exact rationals — `5247/1700`, `3547/1700`,
`133/850`** — and close the side goals with `linarith [hσlo]` (tight-but-true,
equality at the endpoint), **not** `nlinarith`. Corrected arms:
`log(KEρ/c₀)/(5247/1700) = 25.5784`; `log(KEβ)/(3547/1700) = 32.1515` — note this
also corrects the freeze's stated **32.16 → 32.15**.

**SIGN CONVENTION: UNFOUNDED — no inversion.** mathlib's
`Real.rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
x^y ≤ x^z` is applied with `x = c`, `hcc`, `hc1`, and the side goal in the FLOOR
direction (`1/8 ≤ γ_row`). Substituting `γ₀` keeps the direction and the shape
(`γ₀ ≤ γ_row`); since `γ₀ > 1/8` the resulting `hg` is a **weaker** demand on `c`
— exactly the intended gain. Downstream the arm is `c ≤ (1/(8K))^{1/γ₀}` via
`hcollapse`, which needs only `pinv·p = 1`.

**UNIFORMITY TRAP: UNFOUNDED — no trap.** `hσlo` is a top-level hypothesis of all
three row lemmas (`TBalTall:1572`, `TBalR8:739`, `TBalR8:448`), and each collapse
site already discharges its side goal with the window in hand. The window is
**already load-bearing** at these exact lines for `hγpos` and for
`ray_pow_bound`'s hα/hε. Nothing new enters scope.

**ARM ARITHMETIC: UNFOUNDED — all ten arms reproduce.** `c₀ = 1/126848` confirmed
(`ZeroFreeReal.lean:392/:605`; `TBalTall:2090` takes `min c₀' 1`),
`log(1/c₀) = 11.7507`. As `log(1/arm)`: `2^{−250}` 173.2868 · `(c₀/32)^{17/3}`
**86.2267** · `(1/805)^{50/49}` 6.8274 · `(1/(8·1610·e))^8` 83.7074 · `1/2`
0.6931 · `(1/KEβ)^8` 536.6658 · `(c₀/KEρ)^8` **631.5764** · `1/(3A₀)` 4.8527 ·
`1/18` 2.8904 · `1/576` 6.3561. **Headline (i) is byte-exact.**
Minor: §0(i)'s "then six arms ≤ 6.9" miscounts — the min has exactly TEN arms, of
which **five** are ≤ 6.9.

---

## 5. WHAT THIS SEAT IS FIRING, AND WHY

**TS-1 and TS-2 FIRE**, with these binding amendments:

1. **Both towers, always.** Every S1/S2 edit is mirrored in `dh_repulsion_inst` /
   `dh_repulsion_ordered` (`TBalR8:1373, :1660-1707, :1752-1848`, 11-fold min at
   `:1776-1833`) as well as the tall twin. This is the difference between a green
   build and a landed theorem going red.
2. **S1 by numeral replacement, not arm deletion** (`2^(-250)` → `1/40`), keeping
   every min-projection chain index-stable. ~20 ln instead of ~123.
3. **γ-floors as exact rationals** `5247/1700`, `3547/1700`, `133/850`.
4. **The shared `c`-min block is `TBalR8:1776-1833` AND `TBalTall:2105-2156`** —
   this, not TBalTall alone, is what forces TS-1 strictly before TS-2 (the
   writer-slot law).

**Honest statement of what TS-1 + TS-2 deliver, post-K3:** `log(1/c)` from
**631.58 → 86.23** (binding arm becomes the ZFR residue row `(c₀/32)^{17/3}`,
which no stone in TS-1/TS-2 touches), i.e. §D2's `e^{1264}` → `e^{172}`, with **no
parameter changed and no statement outside the two files**. That is
explicit-constant hygiene and it moves the `hN+ ∧ hηq` non-emptiness floor — it
does **not** buy the N11 door, which K3 shows is gated on the L-power and not on
the size of the constant. Recorded here so no one later reads TS-2's landing as
door progress.

**Note on S5's second half.** The sharp `neg_log_le_rpow` (`u^{−δ}/(e·δ)`) is
local and free (627 → ≈248). The **δ re-tune 1/100 → 1/50 is a different animal**:
it changes the `u`-exponent at every consumer of `logz_factor_pow9_le`, hence
every γ-floor and every window `nlinarith`, and — because the binding arm after
S2 is the ZFR row at 86.23 — it **moves no delivered number**. Its value is banked
for TS-3 only. TS-1 attempts it second, with a stop-rule.

**TS-3 and §6's design ruling: HOLD, escalated.** K3's fatal finding and K2's
wall W4 / b-floor correction are statement-layer. They go to the design seat and
to JYH; this seat does not rule on them.
