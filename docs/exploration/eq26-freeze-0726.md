# eq-(26) bridge freeze — the h₂-average → X-average arc (2026-07-26)

**STATUS: GATED on JYH (GATE-1 below) — do not dispatch.** Refuter pass
deferred until GATE-1 ratifies execution (verify-posture law satisfied:
no executor consumes this before then). Source: EQ26-SCOPE (read-only; MR
`1501.04585v4` pp. 6, 7, 13, 15, 29, 30 ALL RENDERED via Read pages — never
pdftotext, the banked defect generator; the landed Sec9Glue/JFactor/
KernelCarry corpus).

## The statement, byte-verified (p. 30)

At Q₁ ≤ h ≤ h₂ = X/(log X)^{1/5}, "Using Lemma 4 together with Lemma 5", for
any X ≤ x ≤ 2X:

**(26)** (1/h₂)Σ_{x≤n≤x+h₂, n∈𝒮} f(n) = (1/X)Σ_{X≤n≤2X, n∈𝒮} f(n) +
O((log X)^{−1/20+o(1)})

Exponent exact: −1/20 + o(1) IN the exponent. Both windows CLOSED; both sums
carry n ∈ 𝒮. Used in BOTH branches at p. 30: h ≤ h₂ (the only bridge from
Step 1's h₂-average to Theorem 3's X-average — LOAD-BEARING) and h > h₂
(retired for us: door h ≍ log X ≪ h₂, `door_h_le_hTwo` Sec9Glue :370).
mr_extract :292–297 agrees byte-for-byte. The reconstructed proof (MR give
none): Lemma 5 on each window → alternating 2^J rows → Lemma 4 at f := g_𝒥·f,
y := h₂ (the EXACT lower endpoint of Lemma 4's range — saturated) → triangle
× 2^J ≪ (log X)^{o(1)}. Four side-checks pass (g_𝒥·f multiplicative and
1-bounded; windows match with no re-indexing; squaring gives (log X)^{−1/10}
absorbed by 1/(log X)^{1/50} — lossless).

**Source looseness (new find):** 𝒮 is defined on p. 6 only for X ≤ n ≤ 2X,
but (26)'s short window reaches 3X; MR use n ∈ 𝒮 there anyway. Any port
modeling 𝒮 as a Finset ⊆ Icc X (2X) silently truncates. The corpus is safe
(`MemS` is a predicate on all n, Sec9Glue :118) — keep it that way.

## The verdict on V9's "likely cheaper post-KernelCarry"

**REFUTED for (26) proper**: its complete input list — lemma5 (landed,
Sec9Glue :275, at arbitrary Finset — strictly more general than the print),
Lemma 4 (external hypothesis), the 2^J triangle, one rpow computation — has
EMPTY intersection with what KernelCarry/SeamNumber supply. Costs today what
it cost a week ago: 565–1000 ln, all A/B, zero C.

**CONFIRMED for the consumer (E26-6, the Theorem-3 composition)** — and that
is what V9 likely meant: pre-kernel, the pinned-Tcut far-band defect
4h₁(1+log 3X) was irreducible and Theorem 3 was NOT CLOSABLE AT ALL; the
kernel exit's Egap → 0 makes E26-6 a stone instead of a wall.

**The kill-check that makes the bridge irreducible**: could the kernel retire
(26) by taking h₂ := X? REFUSED twice — the landed binder demands
h₂ ≤ X(log X)^{−1/5} (KernelCarry :940/:1156), and the source's own
arithmetic requires it (the slab/Taylor main term T₀²·(x/X)(h₂/X) needs the
(log X)^{−1/5} factor to produce Lemma 14's grade; dyadic chaining fails at
every step for the same reason). **The h₂ → X step is exactly where the
Halász/GS pretentious input must enter — Lemma 4 is irreducible on this arc.**

## What the landed glue already assumes: NOTHING

`sec9_split`/`sec9_four_term` are pure Finset/ℝ inequalities — no h₂, no
bridge binder. `sec9_eq28_exit` (:517) swallows (26) whole inside hthm3f/
hthm3one (:521/:524) — the X-average comparand is already installed there,
invisible and unpriced. This freeze builds a SUPPLY for those binders from
outside; iron rules 1 and 5 both clean, no landed line edited.

## The stone ladder (ids E26-* — avoids both the Sec9Glue "S9-*" and the
s9-freeze "M4-*" collisions). New file Salt/MR/Eq26Bridge.lean, additive only.

| id | shape | class | ln |
|---|---|---|---|
| E26-0 | the ℝ mirror (GATE STONE): gJR/blockAvoidR + the lemma5R suite; `prod_one_sub_eq_alt_sum` is already CommRing-generic (JFactor :113) so the instance is free; add gJR_ofReal | B | 220–360 |
| E26-1 | `lemma5_budget_diff`: the difference-shaped 2^J budget (c₁Σ_{N₁} − c₂Σ_{N₂}; the landed lemma5_budget is ONE sum/ONE Finset — a naming trap, not the lemma) | B | 60–110 |
| E26-2 | hTwo arithmetic: hTwo_pos, hTwo_le_self, **hTwo_eq_mul_rpow_neg** (the KernelCarry-binder adapter — same number, NOT syntactically equal) | A | 40–80 |
| E26-3 | **eq26** — the binder proposal below; uniform in J, error EXPLICIT: 2^J·C/(log X)^{1/20} (the o(1) recovered by 2^J ≪ (log X)^{o(1)}, p. 28; explicitness-only strengthening, iron rule 1 clean) | B | 120–220 |
| E26-3′ | the K-ladder pin J = 2: error 4C/(log X)^{1/20} — the o(1) EVAPORATES | A | 25–50 |
| E26-4 | (optional, honesty) gJR·f multiplicative + 1-bounded — makes the 2^J instantiation demonstrably legitimate | B/C | 130–260 |
| E26-5 | window bridge: closed Icc⌈·⌉₊⌊·⌋₊ ↔ shortSum's half-open filter ↔ the s0-clip (containment is an OBLIGATION); defect ≤ 1/h per average = MR's own O(1/h), already carried by sec9_four_term's R | B | 100–180 |
| E26-6 | the Theorem-3 composition: (a+b)² ≤ 2a²+2b², integrate, absorb. Consumes `lemma14_shortInterval_meansq_kernel` (:1153) — THE ONLY STONE THAT DOES. ⚠ its real blocker is Prop-1 supply (hMsup + the mid-range integral), NOT (26): carry Step 1 as an explicit hypothesis in the frozen KernelCarry shape; prefer the single-instance `lemma14_contour_of_Msup_at` (SeamLemma14 :451) | C | 250–450 |
| E26-7 | (adjacent, OUT of this freeze — GATE-2) eq (27): Chebyshev at δ/100 producing hthm3f/hthm3one with the exceptional-set count | C | 200–400 |

Bands: (26) proper (E26-0..3′+5) **565–1000, all A/B**; +E26-4: 695–1260;
+E26-6: 945–1710; full arc +E26-7: 1145–2110 — inside s8-freeze's own
declared fallback price ("separate real-Thm-3 port (+1.5k, C)", SCOPE-DIFF
(1)/D4).

**The difference-vs-single-h note: polarity INVERTED here vs the S9 freeze's
stone-4 note.** MR's Step 1 is NATIVELY the h-vs-h₂ difference — the landed
KernelCarry shape is a FIT for this arc, not a mismatch. The single-h V(x)
note applies only to MRT p. 21/thm_A2′ (a different paper's consumer). The
hMsup fires-once-at-Tann note DOES transfer to E26-6.

## The eq26 binder (primary form — reuses the landed Lemma4Comparison
verbatim, byte-fit to rendered p. 13, ZERO consumers today)

```lean
theorem eq26 (Pseq Qseq : ℕ → ℕ) (J : ℕ) (f : ℕ → ℝ) {X C x : ℝ}
    (hX : Real.exp 1 ≤ X) (hx1 : X ≤ x) (hx2 : x ≤ 2 * X)
    (hL4 : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset,
      Lemma4Comparison (fun n => gJR 𝒥 Pseq Qseq n * f n) X C) :
    |(1 / hTwo X) * ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + hTwo X⌋₊).filter (MemS Pseq Qseq J), f n
      - (1 / X) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter (MemS Pseq Qseq J), f n|
      ≤ 2 ^ J * (C / Real.log X ^ ((1 : ℝ) / 20))
```

The SAME C on every row is MR's absolute constant (p. 13) — the uniformity in
f is what the 2^J triangle spends. Windows are Lemma 4's own (closed) so E26-3
needs no convention bridge; all conversion work isolated in E26-5. Secondary
(class-quantified) form noted; recommendation: ship primary + land E26-4.
Carried, never scoped: Lemma 4 (Halász + GS [12, 7.1/Thm 4/Cor 3] — a separate
arc; Sec9Glue :347–359 already says so), hsieve, eq (27).

## JYH GATES

- **GATE-1 (whether to execute at all):** the consumption chain eq26 →
  Theorem 3 → hthm3f/hthm3one → sec9_eq28_exit → **nothing**. Sec9Glue has
  zero Lean consumers; Lemma4Comparison has zero consumers; the door road
  retires MR Theorem 3 on BOTH arms (s8-freeze SCOPE-DIFF (1)/D4; the S9
  ladder's M4-1). Eq-(26) is currently OFF the log-Chowla critical path — it
  is on the PAPER's path iff MR Theorem 1 is wanted as a stated,
  machine-checked result (it is the source's headline theorem, and it is what
  makes Sec9Glue a theorem rather than an implication). The 565–1000 price
  makes "yes, for completeness" cheap — but it should be an answer, not a
  default.
- **GATE-2:** if GATE-1 = yes, eq (27) (E26-7) is unowned/unpriced and
  sec9_eq28_exit cannot discharge without it — same wave or the arc stops one
  stone short.
- **GATE-3 (informational, already open):** hsieve unowned (flags :11989).

## Traps (the scoper's twelve, condensed)

ℂ/ℝ split at the Lemma-5↔Lemma-4 seam (E26-0 is the gate stone);
lemma5_budget is NOT the budget (26) needs; hTwo vs X·(log X)^{−1/5} not
syntactic; THREE window conventions (pick closed real-endpoint, isolate in
E26-5); lemma5_MR/_middle are TRAPS not assets (ℕ-instances — the generic
lemma5 composes; do not send an executor at lemma5_MR); 𝒮 as predicate never
Finset (the 3X reach); J is a VARIABLE in the source and a PIN (Jb = 2) in
the corpus — state uniform, derive pinned, never hard-code 4 in the general
statement nor carry o(1) into the pinned one; eq28_clears_of_M is uniform in
Jb while calFrameK_satisfiable is where Jb = 2 lives; the s0-clip containment
is an obligation; Lemma4Comparison is dead code today (header amendment rides
with the landing wave, not before); E26-6's blocker is Prop 1 not (26);
rendered pages only.

## ⟦AMENDMENT A⟧ — the refuter repairs (folded before wave 1; verdicts:
BINDER-REF REPAIR-THEN-FIRE, IRRED-REF REPAIR-THEN-FIRE)

**SURVIVED (UNFOUNDED ×5):** the binder byte-fit (windows/normalizations/C-
uniformity/index range all exact; the strengthening legitimate both ways —
explicit conclusion AND weaker hypothesis); the derivation closes (Σ|·| of
the difference — E26-1's shape is precisely the composer); the J-pin (no
consumer needs J → ∞; sec9_eq28_exit uniform in J); the irreducibility
(CONFIRMED harder than claimed: every kernel exit is L²-in-x, (26) is
pointwise-in-x — no L² bound reaches it; the low-frequency band |t| ≤ T₀ is
exactly the pretentious band only Lemma 4 handles); the E26-0 pricing
(conservative — see the cast-route note below).

**REPAIRS (all folded into the rows above by this amendment):**
- **E26-5 SPLIT.** The "defect ≤ 1/h = sec9_four_term's R" equation was
  FALSE (R is the cardinality-normalization defect OUTSIDE the mean square;
  the E26-5 defect is the shortSum↔closed-Icc conversion INSIDE E26-6's).
  Now: **E26-5a** — pointwise bridges |(1/hⱼ)shortSum a s0 x hⱼ −
  (1/hⱼ)Σ_{Icc ⌈x⌉₊ ⌊x+hⱼ⌋₊, MemS}| ≤ 1/hⱼ at s0 := (Icc ⌈X⌉₊ ⌊4X⌋₊).filter
  MemS (both clip directions automatic; KernelCarry's hrange met; the short
  window reaches < 3X < 4X). **E26-5b** — the explicit record that
  sec9_four_term's R is a DIFFERENT object. **E26-6 gains the binder
  hh1lo : 400/δ ≤ h₁** (post-Chebyshev placement, the cheaper form; the door
  road h ≍ log X discharges it at any fixed δ). No landed lemma supplies any
  h₁ lower bound — the binder must be in the row (catch #253: at h₁ = 1 the
  squared bridge defect is Θ(1) against a vanishing target).
- **E26-6 REWRITTEN** (three incompatible instructions resolved): E26-6
  carries Step 1 as an explicit hypothesis IN THE :1153 SHAPE and therefore
  consumes no landed lemma; the "prefer lemma14_contour_of_Msup_at" note is
  DELETED (category error — that is the uSlab CONTOUR form at N = 1, whose
  conversion resurrects the irreducible Perron defect the kernel bought
  off); the fires-once-at-Tann note does NOT transfer (the ∀T family is
  consumed at N dyadic levels). E26-6 also budgets: a public
  shortSum_measurable' re-proof (~15 ln — the landed one is PRIVATE at
  Lemma14 :563; the only public integrability export covers only the
  two-scale difference, not ‖(1/h₁)S₁ − c‖²; do NOT de-private the landed
  line), and the SECOND ℂ↔ℝ crossing at the KernelCarry side (+~60–100).
- **E26-7 RESTATED** (GATE-2 was necessary, not sufficient): the honest
  deliverable is the exceptional-set form — ∃ E, (measure bound) ∧
  ∀ x ∈ [X,2X] \ E, hthm3f ∧ hthm3one — with the UNION of the f- and
  f≡1-exceptional sets and the non-vacuity count. The f ≡ 1 instance is a
  SECOND full chain: its Lemma-4 rows are free (E26-3 is uniform in f) but
  its Step-1 supply is a second CARRIED hypothesis (priced into wave 2).
  Micro-gap closed: the Finset.sum_const/card bridge for hthm3one (2 ln,
  now in E26-7's scope).
- **NEW E26-8 [A/B, 150–250] — the A(h) instantiation (★ the corner):** the
  pinned A = 65536 makes P₁ an absolute constant, so Theorem 3's error
  (log h)^{1/3}/P₁^{1/6−η} → ∞ on the door road — TRUE BUT VACUOUS at the
  pin. Repair: A := ⌈(δ/8)·log₂ h⌉, M := ⌈8/δ⌉ ⟹ P₁ ≈ h^{δ/8},
  Q₁ = 2^{MA} ≈ h — meets [P₁,Q₁] ⊆ [1,h] and MR p. 31's shape; the
  CalFrameK gates survive (A_gate_logK's LHS ~ log A vs RHS ~ A·log2/24;
  G_gateK/A_floor h-free). Note: this h-dependent inhabitant is for the
  Theorem-3 SUPPLY side; the eq-(28) demand side stays scale-invariant.
- **Executor permissions/nits:** E26-0 via the CAST ROUTE is permitted and
  preferred (gJR + gJR_ofReal + Complex.ofReal_inj transport of the landed
  lemma5 — ~80–140 ln; the full re-proof suite only if the cast resists;
  gJR_mul etc. only in E26-4); write ALL filters eta-expanded
  (.filter (fun n => MemS ...)) to match the landed syntactic forms; the
  dyadic-chaining sentence in the kill-check reads "fails at the single
  final (log X)^{1/5} step to X" (chaining below hTwo X is admissible);
  "Four side-checks" reads three; the Jb = 2 pin is TIGHT (G_gateK holds
  with EQUALITY at the pinned frame — raising Jb requires re-pinning G) and
  the write-up says "an 𝒮 of MR's shape at Jb = 2", never "MR's 𝒮".

**WAVE PLAN:** wave 1 (NOW) = E26-0 (cast route), E26-1, E26-2, E26-3, E26-3′,
E26-4, E26-5a/5b — the elementary core, all A/B, ~500–900. Wave 2 (after
wave 1 + the design-block verdicts) = E26-6 (amended), E26-7 (exceptional-set
form), E26-8.
