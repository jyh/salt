# WEIL-TRIO DESIGN FREEZE v1 — Estermann + the real-primitive lifts
### 2026-08-06, Fable (Sancho). STATUS: frozen pending the refuter
### pass (§4). Governing dossier: n6-scout-dossier-0805.md — this
### freeze RATIFIES its §4 plan and rules its open seams.
### NODE TAG: **WEIL-TRIO** (the dossier's §5.6 collision finding:
### "N6" is overloaded — never use it in dispatches).

## 0. Rulings (resolving the dossier's open questions)

1. **The plan is adopted as-priced**: W0 → (W1 ∥ W2 ∥ W4 ∥ W5) → W3.
   Files and estimates per the dossier §4, verbatim.
2. **W4-d (the p.216 Σχ(b₂) vanishing) stays in WEIL-TRIO**, last
   stone of W4 — the machinery is character theory (Orthogonality +
   IsPrimitive), which is W4's toolbox, not N7's congruence
   gymnastics. N7 consumes it by name.
3. **The scout's corrections are LAW for every brief**: the
   Kloosterman modulus k = D·δ₁·w₁ is ARBITRARY (the cube-free
   delta-ii mis-scope is dead); "q cube-free" is replaced everywhere
   by the structure lemma q = 2^a·m, a ∈ {0,2,3}, m odd squarefree
   (the fulcrum-pass1.md:57 ruling; raw cube-freeness is FALSE at
   q = 8); the p.217 prime case is LANDED at QuadCharSum.lean:137 in
   the corrected form — quote the Lean, never the audit doc.
4. **W4-c carries 2^{ω(q)} explicitly** — HB's ≪ hides d(q); our
   statement does not (the dossier's refuter target #2 checks the
   absorption at (6.11) BEFORE W4-c's brief is cut).
5. **W2 fallback pre-ruled**: if the 2-adic stationary phase stalls
   at 3 attempts, do NOT grind — flag with the achieved constant and
   the road takes C·2^{k/2}·(...)^{1/2} at whatever C landed, or the
   v₂-bounded question escalates to a Fable block. An explicit weak
   2-adic bound (e.g. C = 4) still beats the trivial P6 by the full
   square root that matters.
6. **W4-e (the doc fixes) fires immediately, no refuter needed** —
   class A, zero risk: the QuadCharSum citation correction (wrong
   paper named at :13-14/:44) + the fulcrum_audit_source.md:95
   inline form.

## 1. Fire conditions

- W0 (the budget ledger, read-only, one refuter-grade agent) fires
  NOW alongside the §4 refuter pass — it is itself a refuter task.
- W1/W2/W4/W5 executor briefs are cut only after W0's ruling and the
  §4 verdicts land; W3 after W1+W2.
- Seat: math-acct (the math seat), after its TAU-SHARP queue completes —
  or maestro-dispatched Opus executors if math-acct is saturated.

## 2. Iron rules riders (beyond salt/CLAUDE.md's standing set)

- Estermann statements at ARBITRARY a, b — no IsUnit hypothesis
  anywhere in an exit-interface statement (interior lemmas may).
- The gcd factor (k,a,b)^{1/2} in every exit statement; never absorb
  it into a constant.
- Statement audit per the sp1-lean kill-list: no vacuous hypothesis
  pairs, width/normalization stated, every promised theorem present.

## 3. Exit interface (what N7 quotes — the dossier's supply table)

(7.1) at arbitrary k/a/b [W3]; the sawtooth kit (7.2)–(7.4) [W5];
p.217 composite [W4-c]; p.216 vanishing [W4-d]; the structure lemma
[W4-a]. Each lands with #audit_axioms and a one-line "N7 quotes
this as ..." docstring.

## 4. The refuter pass (fires now, with W0)

Six kill-checks, verbatim from the dossier §5: (1) the W0 slack
arithmetic (θ = 1/6 ⟹ x^{23/24} — re-derive independently); (2) the
2^{ω(q)} absorption at (6.9)/(6.11) incl. Δ-uniformity; (3) the
k-arbitrary misread check (verify w₁ free at (5.14)/the p.214
application — if the scout is wrong, W1/W2/W3 shrink); (4) W2
necessity (can v₂(k) be bounded upstream?); (5) the W4-d seam
(confirm ruling #2 doesn't strand an N7 dependency); (6) statement-
level audit of §3's exit interface against hb1983-notes' exact
forms (the sp1-lean genre).

---

# v2 DELTA (8/6, post-refutation — 3× REPAIR-THEN-FIRE). v2 GOVERNS.

## D1. THE W0 RULING (R1's independent ledger — my θ=1/6 claim was 8× over)
The true budget at x ≥ q^{250} is **θ ≤ 1/50** (leverage: 31.25
q-powers per unit θ; closed form θ_max = 1/2 − 120/X at x ≥ q^X;
validated by reproducing HB's own 15/16 at θ=1/4). The "q^10 slack"
argument was a category error (x-exponent vs q-powers) — mine, in
the freeze. CONSEQUENCES:
- **W1-c is the SHARP Salié stone, class C** (crude P5 is 8× over
  budget). Grade: ‖S(a,b;p^e)‖ ≤ c_e·p^{e/2}·(p^e,a,b)^{1/2}, odd p,
  arbitrary a,b, ∏c_{e_p} ≤ d(k). The one non-elementary input is
  |quadratic Gauss sum| = √p — **mathlib supplies it:
  gaussSum_sq, Mathlib/NumberTheory/GaussSum.lean:178**. Non-unit
  a free via W1-a's loss-neutral descent.
- **The ε-budget is 1/800** (catch #253 genre): Lean statements
  carry d(k)³(log 2k)³ LITERALLY, never k^ε (the ∀ε∃C shape loses
  the ordering the chain needs); (6.11) holds only for q ≥ q₀
  (absorbed by Theorem 1's error at bounded q — say so).
- HB's p.214 "exponent < 1 suffices" does NOT license degrading
  15/16: the window (1.13) is a blueprint statement (iron rule 1).

## D2. W2 DELETED — with the adjudication (R1 vs R3, maestro-ruled)
R1: the standing (1.5) normalization 2∣α makes every l_i(n) odd ⟹
δ₁, w₁ odd ⟹ v₂(k) = v₂(α₂qΔ^{−1}) ≤ v₂(α₂)+3 (≤ 3 for twin
forms). R3 countered "q odd ⟹ no constraint on w₁" — but R3's OWN
census lists **(w₁,α) = 1 at (5.6)**, and 2∣α then forces w₁ odd
regardless of q's parity; (5.1)'s support kills (δ₁,α) ≠ 1
likewise. ADJUDICATED: **W2 dies unconditionally.** The landed P6
covers the bounded 2-part at constant 2^{κ₀/2} ≈ 2.83.
- Guard (verify posture): **W1's brief carries a pre-flight** —
  byte-check (5.6)/(5.1) at the source PDF pp.212-214 that the
  coprimality-to-α constraints really govern every w₁/δ₁ reaching
  Lemma 10. If the pre-flight fails, STOP and flag; W2 revives.
- NEW bookkeeping stone W1-d (class A/B, ~40-80 ln): the v₂(k)
  discharge lemma N7 quotes (k = α₂qΔ^{−1}δ₁w₁, δ₁w₁ odd ⟹ v₂
  bound).
- Dependency graph: **W0✓(ruled here) → (W1 ∥ W4 ∥ W5) → W3**, W3
  gated on W1 alone.

## D3. W3's EXIT RESTATED (the achieved pair, not (7.1) verbatim)
`‖S(a,b;k)‖ ≤ 2^{v₂(k)/2}·d(k)·k^{1/2}·(k,a,b)^{1/2}`, arbitrary
k,a,b — the 2-part factor EXPLICIT (≤ 2^{3/2} on road moduli via
W1-d), θ = 0 on the odd part. Docstring carries the N7 rider:
"Lemma 10 then reads k^{ε−1/4}-grade, (5.19) at x^{15/16+ε}".

## D4. W4 RE-CUT (R2: the ω-factor is NOT THERE; the sharp constant is 1)
- **W4-c0** (~10 ln): expose the landed proof's hval as
  `quadraticChar_sum_two_forms_eq` (Σ = 0 ∨ Σ = −χ(a)χ(c)) +
  `_bound_one : |Σ| ≤ 1` — the :137 ≤ 2 stays for compatibility.
- **W4-b SHARPENED to gcd form**: |Σ_{t mod 2^a}| ≤ (2^a, det) for
  a ∈ {2,3}, χ₄/χ₈/χ₈′ — still class A, still decide (≤ 4096
  cases; the refuter RAN it exhaustively — it holds, with Σ = 0 at
  unit det).
- **W4-c FINAL: |Σ_{t mod q}| ≤ (q, uv′−vu′) — constant ONE**,
  sharper than HB's own ≪. Ruling 4's 2^{ω(q)} is amended: there
  is no ω-factor to carry.
- **W4-c′** (class B, ~40 ln): the Δ-fold periodicity descent
  (Σ_{t<q} = Δ·Σ_{t<q/Δ} under q/Δ-periodicity) — R3-U3's unowned
  step, now owned here.
- **W4-a DECOUPLED and re-priced**: 1,300–2,600 ln, a FIVE-STONE
  sub-wave (mathlib is barer than the dossier said: no Kronecker
  symbol, no CRT character decomposition, χ₄/χ₈/χ₈′ primitivity
  UNPROVEN — docstring prose only). W4-c takes the structure as a
  HYPOTHESIS so it lands independently; W4-a supplies the discharge.
  Named shorteners for the brief: factorsThrough_iff_ker_unitsMap
  (DirichletCharacter/Basic.lean:150), ZMod.unitsMap_surjective,
  and **Salt/Maynard/PpRootCrt.lean:88-110 — the CRT units engine
  ALREADY IN THE CORPUS (the fifth VK-forgetting) + the 2^ω
  bookkeeping at :73-87.**
- **VALUE RING RULED (R2-U3)**: the two-forms exits are ℤ-valued
  (MulChar F ℤ, matching the landed QuadCharSum); the
  MulChar.ringHomComp bridge to ℂ is the consumer's one-liner,
  noted in each docstring.
- W4-e: struck (landed at 7a1a6a1 before the pass — R1-U3/R2-U4).

## D5. W5 + THE EXIT INTERFACE REPAIRS (R3)
- §3 gains the SIXTH row: the congruence-restricted completion
  `Σ_{n∈I₀, q∣n−b} e(−sn/k) ≪ Min(E, ‖sq/k‖^{−1})` [W5] — the
  missing theorem N7 cannot assemble (7.7) without.
- W5 exits split degenerate cases (the ‖θ‖ = 0 arm; a₀ vs a_m) —
  no junk-value traps.
- **The Lemma-10 ownership seam RULED EXPLICITLY** (R3-U1: my §4
  silently swapped the dossier's kill-check 5): Lemma 10 +
  (7.5)–(7.8) belong to N7; WEIL-TRIO delivers supplies only.

## D6. ERRATA BANKED
- **hb1983-notes.md:611 is WRONG** (S₁ ≪ x^{1/4} should be x^{1/2}
  from (5.2); as written the non-trivial regime is empty). Fix the
  notes; R1's ledger used the correct form and reproduces HB :609.
- **🔴 A GENUINE HOLE IN HB (5.5) AT v₂(q)=3, GENERAL FORM PAIRS**:
  (1.8)+(1.9) do NOT give (α₁,q) = (α₂,q) when v₂(α₁) ≠ v₂(α₂)
  (admissible counterexample: 4n+1, 8n+3). MOOT FOR TWIN PRIMES
  (α₁ = α₂ = 4 ⟹ trivially equal) — the road carries α₁ = α₂ as a
  named hypothesis; the general-pair hole is recorded as an
  HB-erratum-grade finding (N7-scoped, worth a remark in any
  writeup).

## D7. Fire order (v2): W1 (w/ pre-flight) ∥ W4(b,c0,c′,d) now;
## W5 next slot; W3 after W1; W4-a as its own sub-wave behind them.
## ALL briefs: builds via /Users/jyh/projects/claude/saltbuild.sh.
