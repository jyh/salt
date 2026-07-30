# THE A4 BRIDGE — design freeze v1 (2026-07-30, the BRIDGE-SCOPE dossier consumed)

*The port's last stone: the y-aspect-vs-t-aspect crossing that discharges
`m4_second_road`'s socket (item 11) from A3's ordinate supply.  Inputs:
the BRIDGE-SCOPE dossier (banked in flags 2026-07-30 00:49), the CLOSE-WAVE
STOP, port-freeze-0729.md (which never priced this stone — the freeze-gap
finding), second-road-freeze-0729.md D-5/D-8(iii) (which flagged the hole).
Status: v1 → overnight refuter pass → the morning council.  JYH has NOT
seen this freeze; nothing here is ratified.  The night executes only the
fork-neutral tail, and only on refuter confirmation.*

## 0. The re-diagnosis (what changed since the STOP)

The A4 STOP cited `M4DoorRow`'s two walls.  Both are DOWN at HEAD
(⟦WALL 1⟧ `hwinBand` deleted by the 7/28 counter-wave; ⟦WALL 2⟧ the
length gate is the landed graded split's own partition boundary).  The
real blocker of the per-χ route is the F5/F4 `q`-LINEAR gate pair
(`M4MeanSq.lean:626-630` at coefficient 32; `M4T0Discharge` at
coefficient 700) — precisely the route the port replaces.  So A4 is not
a stalled composition; it is the port's one unpriced stone, and its
design is the q=1 crossing χ-summed with the ordinate side fed by the
port instead of by `capFreeFloor3`.

## 1. THE RULED ROUTE — R1, the pointwise lift of the q=1 crossing

The crossing layer (`Lemma14*`, `Seam*`, `Parseval*`, `ThmA2*`) is
χ-BLIND (verbatim grep: zero χ) and MONOTONE in the row datum; the
saving-earning coupling lives entirely on the ordinate side, where A3
already put it.  So the lift is the landed three-move pattern
(exemplars: `m4_chiSummedShiftBlock_of_freeRow`,
`lemma12_meansq_all_chi`): free the constant per χ, instantiate at the
character's own datum, split the affine RHS and pay `φ(q)` where the
ledger says.  R2 (per-χ + F4) is DEAD as priced (F4 repairs half of one
of the two gates; the coefficient-700 gate has no repair).  R3 (a fresh
Σ_χ Parseval page) is REJECTED (coupling at a χ-blind monotone step buys
nothing).

**The target:** `m4_second_road_rs_ceiling` — the socket's inhabitant
must come in at `RSan H ≲ 2.5·10⁻¹⁰⁵/(loglog H)²` against the trivial
`4·arcDen 12 H = 4(log H)^{12}`.  No power of `arcDen`, no `q`: the
whole content of the second road.

## 2. The delta (D1–D5) and the wave plan

| # | statement | supplier ruling | ln | class | when |
|---|---|---|---|---|---|
| D1 | Σ_χ twin of `thm_a2_spine`/`thm_a2'_of_rows` — SLOT FORM: `hrowsΣ`, `hT0bandΣ` as free hypotheses, conclusion the Σ_χ window mean square | the three-move wrapper; four χ-free summands pick up `φ(q)` | 250–450 | B | **NIGHT** (fork-neutral, on refuter confirm) |
| D4 | socket wiring: `M4ChiSummedFreeRow` at the door datum (`chiFreeRowSq` byte-identical to `m4_door_meansq_carried`'s conclusion), the three base antecedents, the graded split at `doorRowFloor M`, the φ(q)-ledger arithmetic page | fixed by landed statements | 400–700 | B/C | **NIGHT** (fork-neutral, on refuter confirm) |
| D2 | Σ_χ row family (the `hrowsΣ` slot) | **per-leg, ruled below (§3)** | 1200–2200 | C | morning, post-council |
| D3 | Σ_χ T₀-band (the `hT0bandΣ` slot) | `lambdaChiSummatory_holds_gated` → the MemS J=2 four-fold decomposition (CS cost 4) → the O6 perturbation (**LANDED**: `MobiusChiRamare.lean`, μ·g_r = μ ∗ w_r + the hyperbola identity + the Rankin tail) → the `∀k ∀t` partial-sum form of `m4_hT0band_at_door`'s `hpiece` | 700–1400 | C | morning, post-council |
| D5 | *(contingent: only if D2 routes through the MR rows)* Σ_χ twin of `lemma12_meansq_mr_windowed{,_end}` — NOT a wrapper over `lemma12_meansq_all_chi` (global `hcoef` vs `SeamCoefW`; 3 rows vs 4; prefactor 3 vs 4) | — | 500–900 | B/C | only if forced |

Total (D1–D4): ~2.5–4.7k ln, class C overall.  All statements write
against the POINTWISE `HalaszPrimesChi C c q T` (the SLOT-WAVE landed at
ce24d31; K5 moot).

## 3. THE K3 RULING — each annulus leg's supplier, named BEFORE execution

The #1 shape risk: A3 delivers `Σ_χ ∫_A` only over
`A = (Ann ∖ ball) ∩ 𝒰`.  The complement legs must NOT route through the
per-χ `capFreeFloor3_liouChi_all` (the coefficient-28 gate returns).
The ruling, leg by leg:

* **`(Ann ∖ ball) ∩ 𝒰`** ← A3 as landed: `usetChi_window_meansq_gated`
  (the five named residue groups), extended along `usetChi_integral_to_branches`
  to the annulus form the rows demand.
* **the 𝒰-complement (typical) leg** ← the port's OWN χ-lifted 𝒰-ladder
  (`USetChi`/`USetChiTS`, the P-6 stones) — the χ-twin of the q=1
  `uset_TS_branch_meanvalue` → `hU_exit_of_branches` discrete→integral
  path.  NOT `capFreeFloor3`.  ⟦REFUTER CHECK R-A4-1: byte-verify the
  χ-lifted ladder actually covers this leg — that `exists_Tset_or_mem_Uset`'s
  χ-analogue partitions the annulus, and nothing in the chain imports the
  per-χ floor.⟧
* **the ball leg** ← the pointwise lift of the q=1 ball decay: the `8S²`
  absolute term is φ(q)-debited into the g-arm (K4).  The carried
  per-frequency sup `‖spolyA a t m‖ ≤ S·m` (`M4DoorRow.lean` ⟦THE
  T₀-BAND, NAMED⟧) is priced by D3's supplier at the same `(k,t)`-form —
  one datum, two consumers.  ⟦REFUTER CHECK R-A4-2: confirm D3's
  `∀k ∀t` form instantiates BOTH `hpiece` and the ball-leg sup, or price
  them separately.⟧
* **the far tail** ← `far_tail_crude` verbatim (χ-blind); the φ(q) fold
  is absorbed by `h ≥ 2^{M·Adoor M}` (free, as are summands 2 and 4).

## 4. THE K1 ARITHMETIC PAGE — the φ(q) leak and the g-arm bump

Summand 3 (`188133·(log X)^{−1/500}`) at Σ_χ becomes
`φ(q)·188133·(log X)^{−1/500}`.  Against the ceiling, in logs:
`loglog X ≳ 500·(12·loglog H + 254) ≈ 6000·loglog H + 1.3·10⁵`, vs the
current g-arm `144·loglog H + ~2·10³` — a ~42× coefficient bump on a
consumer-chosen knob.  The precedent for repaying φ(q) with log-X powers
is landed (`phi_debit_level_repin`: `φ(q)·(log X)^{−212} ≤ (log X)^{−200}`
at `q ≤ (log X)^{12}`).  **The claim to verify, not assume: the bump is
F5-NEUTRAL and gate-neutral** — g raises `x`, not `H`; the ruled 2³⁶
anchor and the spine conjunct (`loglog Hhi ≤ (loglog Hlo)⁵`) read only
`H`; the socket's third antecedent `x ≤ 16ω·arcDen·A` is suppliable at
any `x` (the ladder's `A` scales with `x`); and a LARGER `loglog X` only
eases every `… < loglog X` threshold.  ⟦REFUTER CHECK R-A4-3: walk all
11 gates of `m4_second_road` + the socket's three antecedents + the
tower cap at the bumped g; derive, don't affirm.⟧

## 5. The D3 range fit (checked at scoping, refuter to re-derive)

`LambdaChiSummatory`'s `q ≤ (log y)^{11}` at the x-scale base contains
`arcDen 12 H = (log H)^{12}` (y rides the x-ladder, `log y ≫ log H`);
`|t| ≤ ⌊√y⌋` contains `seamT0 X = (log X)^{1/45}` with room to spare.
The four-fold decomposition (`1_𝒮·λ` = a signed sum of four completely
multiplicative 1-bounded functions) costs CS 4, never `4^J`.  The
𝒮-block restriction is the O6 perturbation, whose carrier page is landed.
⟦REFUTER CHECK R-A4-4: the `hpiece` slot's demand is `∀ k ∈ [X_d, N]`,
`∀ |t| ≤ seamT0 X`, a bound `S₀·k` — verify `LambdaChiSummatory`'s rate
shape delivers `S₀ ≤ 2(C₁e^{−M₀/2e} + 4(log X)^{−1/2+1/1000})` at every
such `(k,t)` through the CS-4 fold and the O6 tail, including the small-k
corner `k` near `X_d`.⟧

## 6. The fork-neutrality claim (gates the night tail)

D1 and D4 commit to NOTHING in §3–§5: D1's slots are stated at the
Σ_χ shapes the crossing itself forces (the χ-sum of `thm_a2_spine`'s two
ordinate binders), and D4's wiring is fixed by landed statements
(`chiFreeRowSq` = the door conclusion, byte-identical).  Whatever
supplier wins any fork, these bytes stand.  ⟦REFUTER CHECK R-A4-5:
byte-check the claim — write the two Σ_χ slot shapes from
`ThmA2Spine.lean:394`'s actual binders and confirm no fork leaks into
them (in particular that the `hrows` T-quantification `∀ T, X/h ≤ T →
2T ≤ X` survives the χ-sum unchanged, and that the socket's graded split
does not force a supplier choice).⟧

## 7. What the morning council decides

1. Ratify R1 and the §3 leg-supplier rulings (or re-fork).
2. Ratify the K1 g-arm bump (~42×) as the honest φ(q) price.
3. D3's route as ruled (LambdaChiSummatory → four-fold → O6), or the
   alternative (a direct χ-twisted Perron re-run at the T₀-band — NOT
   recommended: a new analytic page where a landed rate suffices).
4. The D5 contingency trigger.
5. Fire A4-W2 (D2) and A4-W3 (D3), then A4-W4: the assembly —
   `m4_socket_discharged` shipped HONESTLY (the socket inhabited at the
   ceiling's grade, gates in-statement), then THE S11 COMPOSE under the
   ratified summit protocol.

*The refuter pass (REF-A4: R-A4-1..5) runs overnight; verdicts bank in
flags before the council.  — Sancho, 2026-07-30, the night watch.*

---

# v2 ADDENDUM (2026-07-30 01:10, REF-A4-SHAPE folded; v1 above kept as the record)

The refuter pass amended the freeze before any executor consumed it —
the law working.  Three corrections, all adopted:

## A1 — THE SLOT SHAPE (v1 §6 was the wrong one of two inequivalent forms)

`thm_a2_spine`'s `Mrow` is a single scalar uniform over the `T`-family,
so the pointwise lift forces **indexed families**
`Mrow B₀ : DirichletCharacter ℂ q → ℝ` with the χ-sum on the CONSTANTS:

```
hrowsΣ   : ∀ χ, ∀ T, X/h ≤ T → 2T ≤ X → TannGate X (2T) → 5 ≤ loglog (2T) →
             X/h/T * ∫_{seamAnn X (2T)} ‖spoly N (a χ) t‖² ≤ Mrow χ
hT0bandΣ : ∀ χ, ∫_{-seamT0 X}^{seamT0 X} ‖dpolyA (a χ) (seamS0 N X) t‖² ≤ B₀ χ
  ⟹  ∑_χ (window mean square at a χ) ≤ (affine in ∑_χ Mrow χ, ∑_χ B₀ χ,
       with φ(q) on the χ-free summands)
```

with the datum a generic χ-indexed family (not pinned to `chiBarCoeff`
or `doorChiCoeff`; they agree up to one `mul_comm`).  This SUBSUMES the
sum-inside form (`Mrow χ := MrowΣ`) — fork-neutral, night-fireable.  The
`sup_T ∑_χ` vs `∑_χ sup_T` exchange costs a φ(q) on the ROW summand that
the g-arm absorbs (`loglog X ≳ 3.7e3·loglog H + 7.4e4` on top of K1's) —
council arithmetic.

## A2 — D4 RESCOPED to the wiring half

Kernel-confirmed clean: `chiFreeRowSq` is DEFEQ to
`m4_door_meansq_carried`'s conclusion; the graded split forces no
supplier choice; `m4_chiSummedFreeRow_trivial` carries `j < j₀`.  D4
fires that wiring only.  The φ(q)-ledger page is COUNCIL work with the
SIX-debit enumeration: summands 2 (tightens ⟦gate 8⟧ ≈12× — `P₁/M`-side,
NOT g-absorbable), 3 (g-arm, K1), the ball `8S²` (K4), `hgP1`, `hgRows`,
and the A1 row exchange.  The page's content is the CLASSIFICATION:
g-arm-absorbable (`X`-side) vs gate-8-tightening (`P₁/M`-side).

## A3′ — THE §3 LEG CENSUS CORRECTED (v1's was refuted)

| leg | v2 supplier | status |
|---|---|---|
| ball | pointwise lift of `ball_leg_of_sup` (`8S²`, φ(q)-debited) | as v1 |
| `(Ann∖ball) ∩ ⋂_χ 𝒰_χ` | A3 (`usetChi_window_meansq_gated`) — **v1 misfiled this machinery under the complement leg** | landed, BUT carries ⟦THE Rbd HOLE⟧ |
| the 𝒯-leg (the complement) | **NO χ-LIFT EXISTS** (q=1 apparatus 4061+2161 ln, zero χ); the Σ_χ Lemma-12 half IS landed (`lemma12_meansq_all_chi`) | **missing: 1.5–3k ln, C** |
| the partition itself | no ordinate-level χ-analogue of `exists_Tset_or_mem_Uset`; `UsetChi` is FIBREWISE, so one `A` works only at `A ⊆ ⋂_χ 𝒰_χ`, complement `⋃_χ 𝒯tot_χ` mixes genres | **missing: 150–300 ln, B — a DESIGN FORK** (⋂ vs per-χ `A_χ` vs graded pair-partition) |

⟦THE Rbd HOLE⟧ — the deepest new item: the ruled leg's `Rbd` slot
(character-uniform, graded) has as its only landed supplier the
`pocket_collision_window` chain fed by `capFreeFloor3_liouChi_all` — the
`(1/4)q` gate returns INSIDE the safe leg.  A Σ_χ collision/pocket stone:
~600–1200 ln, class C, and a genuine design question (the pretentious
floor is per-χ by nature; character-uniformity is not a composition).
Machine-verified clean elsewhere: the gated ladder's proof term (4864
constants) touches zero capFree/pocket constants.

## THE RE-PRICE

A4 honest total: **~4.8–9.2k ln** (v1's 2.5–4.7k roughly doubled by the
census gap).  The council's deep items, in order: (1) the partition
fork; (2) the Rbd design; (3) the six-debit classification page; (4)
D3's route (REF-A4-MATH pending at this writing).

## THE NIGHT TAIL (fired under A1+A2)

D1 at the indexed-family shape + D4's wiring half — one executor,
additive only, fork-neutral under the refuter's own verdict.

---

# v2.1 ADDENDUM (2026-07-30 01:13, REF-A4-MATH folded)

## The corrected arithmetic (supersedes §4 and the v2 re-price)

* **The arm:** `loglog X ≥ 7000·loglog H + 1.25·10⁵` (clean form; exact:
  `6000λ + 1000·log(1+12λ) + 124,815`).  v1's `6000λ + 1.3e5` FAILED for
  every λ ≥ 33.2 — the log term was dropped.  The "42× bump" framing is
  retired: the old `144λ + 2e3` baseline priced the DEAD F4/F5 route; the
  honest ledger is **+6000λ flat on a 1.24e5 baseline**.
* **The g-arm's full written form:**
  `g H ω := max x₀ (16·ω·(log H)^12 · exp(exp(7000·loglog H + 1.25e5)))`
  — the socket-antecedent division AND the ineffective `∃x₀` both ride
  inside g (legal: g takes ω; x₀ is a constant of a fixed Prop).
* **The M₀ window (NEW, was unclosable unstated):** summand 1 + the ball
  `8S²` force `M₀ ∈ [32.62λ + 670 + 0.06·loglog X, 2.7128·loglog X − 7.54]`
  (upper cap = `hErr`).  Non-empty under the arm; MUST be stated in the
  D-wave.
* **⟦THE 12× ANCHOR LINE — COUNCIL ITEM #1⟧:** summand 2's φ(q)
  absorption needs `Adoor M ≥ 207.75λ` vs gate 8's `17.31λ` — exactly
  12× on THE ONE BINDING H-UPPER.  `log₂M+1: 207 → ~2484`,
  `M: 1.9e62 → ~1e747`.  Knock-ons derived free; M is bound after `∃R`;
  but this is an anchor movement and goes to JYH.
* **F5/gate-neutrality: CONFIRMED by derivation** (regimeEnlargeX' moves
  x alone; all 11 gates x-neutral or eased).  The freeze's cleanest claim.
* **The θ₂₉₃ lever, recorded not spent:** re-cutting D1's pooling at
  1/293 instead of 1/500 buys 1.71× on the whole arm, at zero ε-room.

## D3 re-priced (supersedes the v2 table row)

The rate and the four-fold ARE landed (cost exactly 4).  But O6 sits at
(μ, single window); D3 owes: the λ-transposition (200–350, B), the
union-mask twin for 𝒥 = {1,2} (300–500, B/C), the mass page (150–250,
B), the Rankin-tail page (300–500, C).  **D3 honest: ≈1.65–3.0k ln.**
Fit CONFIRMED at the small-k corner; hpiece is a summatory (no Abel).

## R-A4-2 resolved (v1 §3 bullet 3 corrected both ways)

The T₀-band sup is DERIVED from hpiece by landed bytes (`m4_t0datum_sup`)
— not a second consumer.  The REAL ball-leg sup is a different shape
(disjoint t-range, `S·m/(1+|t−t₁|)` renormalization, the centre t₁) —
**a new leg: the χ-lift of `ball_sup_of_center` at `pieceDatum`,
≈400–700 ln, class C** (hCenter at t₁ ≠ 0 is a genuine nonzero-centre
Halász instance).

## THE CUMULATIVE RE-PRICE (v2.1 final)

**A4 ≈ 6.2–11.6k ln.**  The council slate, final order: (1) the 12×
anchor ask; (2) the partition fork; (3) the Rbd design; (4) the
corrected six-debit page (the arm + the M₀ window); (5) D3's owed pages
+ the ball-sup leg; (6) the θ₂₉₃ lever.  The night tail (D1+D4)
untouched by every finding — in flight at this writing.

---

# v2.2 NOTE (2026-07-30 01:46 PDT, C3-SCOPE folded)

⟦THE Rbd HOLE⟧ of v2's A3′ table DISSOLVES: the pocket chain fires
VACUOUSLY at the landed door road (the floor is per-datum, never
per-ordinate — M4MeanSq.lean:451); the landed F4+VT-7 sibling
`capFreeFloor3_pieceDatum_vt` supplies the socket at 43× headroom under
the v2.1 arm; the value `2^J·Rbar0` is character-uniform by
construction (ZERO φ(q) — A3's binder is pointwise in (χ,t)).  The
stone re-prices ~0.28–0.71k class B (was 0.6–1.2k C); A4 total
**5.9–11.1k**.  C3 decouples from C2 and from the ball leg (t₁ free).
One erratum absorbed: F5 killed the floor's ROW consumer, never the
CO-FACTOR consumer (the "category error" line of v2.1's source verdict
corrected in flags).  The surviving council ruling: the third opaque
constant `cffKVt` in the g-arm (grant ⟹ wiring; deny ⟹ an unscoped
majorant page).  New micro-item: `mertensM ≤ 3` (~30 ln, A).

---

# v2.3 NOTE (2026-07-30 01:51 PDT, C2-SCOPE folded — THE FORK COLLAPSES)

Design (i) KILLED at q=3 (margin 5.2e103; the off-diagonal mixed
term's only supplier is the hybrid MVT at Θ(q) diagonal mass; not
g-arm repairable).  (ii) = (iii) at the set level — adopt (ii)'s
content in the pair spelling `𝔄 : Set (DirichletCharacter ℂ q × ℝ)`.
**⟦THE THRESHOLD WALL⟧ (new, load-bearing): A3/UsetChi lifts the FLAT
δ-partition; every landed row reaching hrows lives on the GRADED one
(SeamGraded.UsetG); the bridge `UsetG ⊆ Uset` is false by 3.5·M ≈
1e62 — the port lifted the superseded route.  THE FORCED REPAIR: A3
re-lifted at the graded threshold, fibrewise from the first line
(~1.02-1.64k C: UsetGChi, the pair Lemma-8 ramQChi_graded_count
[PROBE FIRST], graded thinness/bundle, the fibrewise branches) —
mandatory under any design, so the per-χ form is FREE.**  The 𝒯-leg
census item re-priced 1.5-3k C → 0.2-0.45k B (TLeg is datum-generic;
only the χ-factorization page is owed).  D2 to be re-derived downward
(double-count).  One refuter check owed at execution (K-5: graded
gates vs the socket's four (q,T) gates).  **A4 total, combined with
v2.2: ≈5.5-10.3k ln.  ZERO design forks remain in the port.**
