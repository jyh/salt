# Pass 2 / E4 — DEAD ROUTES: what "no Siegel zeros" is known to buy, and where each route died

Date: 2026-07-19. Mission: price ¬F against the literature's "no-Siegel ⟹ ?" corpus.
¬F := ¬(FulcrumQualityMin C⋆) = ∃Q₀, every primitive quadratic χ mod q > Q₀ has
L(·,χ) zero-free in the ball ‖1−ρ‖ ≤ 1/(C⋆·log q)  (Salt/Fulcrum/Basic.lean:61, live grep today).

Labels: **GROUNDED** = file:line or page:eq read THIS pass. **MEMORY** = model recall, unverified.
Sources actually read: H-B 1983 PDF pp. 193–198, 221–224 (~/Downloads); docs/sources/montgomery3.txt
(MNT III chs. 24, 28); docs/sources/chowla.txt (Tao, log-averaged 2-point Chowla/Elliott).

---

## 0. The shape of ¬F (scope-diffs first — catch #224)

- ¬F is a COMPLEX ball, primitive-quadratic-only, at ONE constant C⋆, with a bare-∃ Q₀.
- Ball→real-segment: for C⋆ dominating 2/c₀ of the classical region, any in-ball zero is real
  (GROUNDED Salt/Fulcrum/Basic.lean:93 `fulcrum_zero_real`, :167–170 `fulcrum_zero_real_zfr`).
  So at engine-scale C⋆, ¬F ⟺ "no real zero β > 1 − 1/(C⋆ log q), q > Q₀" — honest classical no-Siegel at quality C⋆.
- Quality translation (H-B's η): a real zero of quality η = [(1−β₀)log q]⁻¹ > C⋆ lies in the ball, so
  **¬F ⟹ η ≤ C⋆ for every real zero of every primitive quadratic χ, q > Q₀.** This is exactly
  H-B's "second case: η is bounded" (GROUNDED H-B p.223 §8) with A = C⋆.
- Scope-diff (a): H-B's (1.11) zone is η ≥ 3. If C⋆ < 3, ¬F does not even exclude (1.11)-zeros.
  All consumers below want η ≤ some bound — the DIRECTION is right for any C⋆ (bounds get weaker, never break).
- Scope-diff (b): MNT III Ex. 28.4.3.1 (GROUNDED montgomery3.txt:20088) hypothesizes no exceptional zero
  for characters of conductor DIVIDING q; ¬F speaks of primitives mod q. Bridged by induced-character
  zero identity (Euler factors at p|q nonvanish for σ>0) + the q ≤ Q₀ audit. MEMORY-tier bridge, routine.
- Q₀ is a bare ∃: as stated, ¬F cannot even NAME the finite exceptional set. Every "effective" row below
  is effective-for-q>Q₀; global effectivity needs a Q₀ witness + per-character finite audit (possible in
  principle: fixed χ has L(1,χ) ≠ 0 effectively — MEMORY, classical).

---

## 1. Route: effective Linnik / effective Siegel–Walfisz under no-Siegel (the classical cash-out)

**What the literature actually says (GROUNDED):**
- MNT III Thm 28.20 (Gallagher), montgomery3.txt:23113–23124: if no exceptional zero β₁ with
  1−β₁ < 1/(κ log q) (κ ≥ κ₀), then for q^{6c} ≤ x:
  ϑ(x;q,a) = x/φ(q)·(1 + O(exp(−log x/(κ log q)) + log²x/(q log²q))) — EFFECTIVE.
  ¬F feeds it with κ = max(κ₀, C⋆) for all q > Q₀ (larger κ = weaker hypothesis = still effective).
  κ₀ = 3·max(c, c₁, c₀e, 1, c₀e^{3c}) (GROUNDED montgomery3.txt:22945–22948, eq. 28.91).
- MNT III Ex. 28.4.3.1, montgomery3.txt:20088–20100: no exceptional zero (conductor | q) ⟹
  ψ(x;q,a) = x/φ(q)(1+O(exp(−(log x)^{1/2}·…))) for q ≤ exp(log x/(c₂ log log x)) —
  effective SW in an EXPONENTIALLY wider q-range than Siegel–Walfisz's q ≤ (log x)^C.
- MNT III (24.18)/(24.19), montgomery3.txt:7426–7438: no exceptional zero ⟹ effective L′/L, log L, 1/L
  bounds in the Korobov–Vinogradov region; and eq. (24.25) at :7560: the SOLE ineffective term of
  ψ(x,χ) is x^{β₁}β₁⁻¹E₁(χ) — ¬F deletes it for q > Q₀. The VSiegel corollaries (:7574, :7586) are
  where Siegel's ineffective theorem currently enters; ¬F replaces that step.
- Linnik Thm 28.21 p(q,a) ≤ q^A, montgomery3.txt:23128–23140: proof splits on exceptional zero;
  no-zero case runs on the log-free density Thm 28.14 alone; zero case runs on Deuring–Heilbronn
  repulsion Cor 28.15 (GROUNDED :21746–21756). ¬F keeps only the first case (q > Q₀) — effective A.
- MEMORY (LOUD): numerical constants — unconditional Linnik A = 5.18 (Xylouris 2011), 5.5 (H-B 1992);
  "no Siegel zeros ⟹ smaller A" claims exist in H-B 1992 (recalled ~4.5, LOW confidence); GRH gives 2+ε.
  The Deuring–Heilbronn PARADOX (grounded in structure, Cor 28.15): the zero-case often gives BETTER
  exponents — ¬F's gift is effectivity, not strength.

**Twin-relevant statement following: NONE.** Everything above is a single-prime / Type-I statement
(ψ(x;q,a), least prime). DEAD END for twins at the parity barrier (§4): feeding effective SW into every
landed consumer reproduces already-landed unconditional theorems with (invisible-in-kernel) effective
constants. BV's level 1/2 is large-sieve-limited, not Siegel-limited (MEMORY, standard), so no gap-size
improvement either.

**In-repo consumers:** `SiegelWalfisz` (Salt/BV/Defs.lean:35) is a bare-∃-K Prop and is ALREADY a
theorem (`siegelWalfisz_holds`, SW gate arc) — ¬F adds literally nothing in-kernel. It would matter only
for an explicit-constants SW/Linnik restatement (unlanded).

---

## 2. Route: H-B 1983's OWN no-zero branch (the source of record)

Paper structure (GROUNDED, pp. 193–196, 223):
- (1.10)–(1.11) p.194: classical ZFR with effective C⁽⁰⁾, sole exception χ real, t = 0; Siegel zero
  = real zero with 1−β₀ ≤ (3 log q)⁻¹; quality η = [(1−β₀)log q]⁻¹ ≥ 3; η ≪ q.
- Thm 1 + Cor 1 (p.195): zeros horn: given (q,χ,β₀), twin asymptotic 𝔖C(α)x(log x)⁻² + O(x(log x)⁻²(log log η)⁻¹)
  uniformly for q^{250} ≤ x ≤ q^{500} (window tied to q!). EFFECTIVE implied constants.
- Cor 2 (p.195): if η ≥ C⁽¹⁾ for infinitely many triples ⟹ infinitely many twin representations.
  C⁽¹⁾ = exp exp{2A(𝔖C(α))⁻¹} EXPLICIT-EFFECTIVE (GROUNDED p.223). [F-horn: our F_min feeds this iff
  C⋆ ≥ C⁽¹⁾ — the HB-ENGINE constants gap.]
- **Thm 2 (pp.195–196): the dichotomy.** Ineffective C⁽²⁾: either (i) every admissible form pair
  represents simultaneous primes infinitely often, or (ii) ∀q ∀χ: L(σ+it,χ) ≠ 0 for
  σ ≥ 1 − C⁽²⁾/log(q(|t|+2)).
- **Proof of Thm 2 (GROUNDED p.223 §8), the exact ineffectivity locus:** case η → ∞ on a sequence ⟹
  take C⁽²⁾ = 1, horn (i) holds by Cor 2; case η ≤ A globally ⟹ take C⁽²⁾ = Min(A⁻¹, C⁽⁰⁾).
  The ineffectivity of C⁽²⁾ IS the excluded middle on F. **On the no-zero horn the paper's ENTIRE yield
  is: the (1.10) region loses its real-character exception — C⁽²⁾ = Min(A⁻¹, C⁽⁰⁾). No twin statement.**
- **The framing sentence (GROUNDED p.196):** "the present paper shows that any future work on twin primes
  can assume that Siegel zeros do not exist." — the no-zero horn's yield is a HYPOTHESIS LICENSE, not a theorem.
  (Analogy given: Heilbronn's h(√−d) → ∞ under GRH-false.)
- **The C⁽³⁾ vacuity proposition (GROUNDED p.196):** "there exists a constant C⁽³⁾ with the property that
  to prove the number of prime twins to be infinite, it suffices to find a pair p, p+2 with p > C⁽³⁾."
  This is H-B's own warning that ineffective dichotomies can be logically near-vacuous — the benchmark
  every ¬F-claim in our ledger must beat (honest-shape law).
- Also GROUNDED p.196: no Goldbach analogue of Thm 2 expected (representations 2n = p+p′ only in sparse
  q-dependent ranges); prime-gaps remark C⁽⁴⁾ is again a ZEROS-horn yield (η ≥ C⁽⁴⁾ ⟹ small gaps in q-windows).
- Engine mechanics for §4's classification (GROUNDED p.196, §2 pp.197–198, §7 p.221): "if η is large, then
  most primes p have χ(p) = −1, whence μ²(n)χ(n) behaves very similarly to μ(n)"; Λ̃(n) = Σ_{d|n} μ²(d)χ(d)log(n/d)
  turns the twin sum into Σ d(n)d(n+1)-type, closed by Estermann's Kloosterman bound (7.1).
  The exceptional character = a Möbius surrogate = THE parity-breaking oracle; the bilinear (Kloosterman)
  input sees divisor correlations, not primes, without the surrogate.

**¬F applied to Thm 2:** ¬F at C⋆ ⟹ η ≤ C⋆ for q > Q₀; q ≤ Q₀ is a finite character set whose real
zeros sit below 1 by L(1,χ) ≠ 0 (compactness — ineffective as stated, per-character-effective in principle).
So ¬F ⟹ horn (ii) with C⁽²⁾ = Min(C⋆⁻¹, C⁽⁰⁾, small-q term): a uniform fixed-quality ZFR for ALL
Dirichlet L-functions. That IS ¬F's strongest classical consequence — and it is a statement about
L-functions, with zero twin content on its own.

---

## 3. Route: Chen's theorem with effective SW

- In-repo: `chen_headline : {p | p.Prime ∧ IsP2 2 (p+2)}.Infinite` LANDED unconditional
  (GROUNDED Salt/Chen/ChenTheorem.lean:32), fed by the landed SW gate. ¬F adds nothing in-kernel
  (bare-∃ constants). An explicit-constants Chen (effective x₀, effective density ≫ x/log²x) becomes
  writable under ¬F + Q₀ witness — MEMORY: no such explicit Chen is landed anywhere in the literature
  without a Siegel-zero caveat (explicit BV variants, e.g. Akbary–Hambrook, carry exceptional-modulus
  terms; LOW confidence on the exact reference — FLAG).
- **What stays parity-blocked: P₂ → prime.** Chen's weighted sieve consumes only AP-remainder (Type-I/BV)
  information; by §4 the sieve axioms cannot separate Ω = 1 from Ω = 2. No effectivization changes this;
  even full EH doesn't (MEMORY, standard: EH improves levels, not parity).
- DEAD END: ¬F-effectivized Chen is the same theorem with better bookkeeping.

---

## 4. The parity barrier — formal content, and the audit of OUR landed tools

**Formal content:**
- GROUNDED chowla.txt:124–131 (Tao): estimates of λ-correlation type "are well known to be subject to the
  parity problem obstruction (see e.g. [9, Chapter 16]), and thus cannot be resolved purely by existing
  sieve-theoretic techniques that rely solely on 'linear' estimates for the Liouville function. We avoid
  the parity obstacle here by using a new 'bilinear' estimate..." ([9, Ch.16] = Friedlander–Iwaniec,
  Opera de Cribro ch. 16 — Tao's pointer; the chapter itself: MEMORY.)
- GROUNDED chowla.txt:160–162 (footnote): "Bilinear estimates have been used to get around the parity
  obstacle in previous works, most notably in the Friedlander-Iwaniec result [8] on primes of the form a²+b⁴."
- MEMORY (classical formal statement): Selberg 1949 examples / Bombieri's asymptotic sieve — from Type-I
  axioms alone (|A_d| = g(d)X + r_d, remainders controlled in ℓ¹) the sifted count is invariant under
  weights that flip the parity of Ω; hence no lower-bound sieve reaches Ω = 1; P₂ is the exact ceiling.
- GROUNDED chowla.txt:196–200 (Tao's own limitation): his parity-break "rel[ies] in an essential fashion on
  multiplicativity at small primes" and the arguments "do not appear to have any bearing as yet on twin
  prime-type sums such as (1.2)" (the θ(n)θ(n+2) sum). λ-side parity-breaking does NOT transport to Λ.

**Classification of the landed corpus (live greps today):**
SIEVE-ONLY (Type-I-fed, parity-capped):
- Brun upper bound track (Salt/Brun/) — upper bounds; parity-immune but twin-lower-bound-empty.
- `twin_almost_prime : {n | Ω(n(n+2)) ≤ 20}.Infinite` (Salt/BrunLower/TwinInstance.lean:16,771) —
  lower-bound almost-prime sieve; parity caps any refinement strictly above "both prime".
- `chen_headline` (Salt/Chen/ChenTheorem.lean:32) — capped at P₂ (the parity-exact ceiling).
- BV+Maynard chain: `bounded_gaps_of_siegelWalfisz` (Salt/BV/AbelCore.lean:757),
  `bounded_gaps_unconditional` (Salt/SW/Gate.lean:376) — parity does NOT block bounded gaps, but blocks
  gap-2; ¬F leaves the gap constant untouched (level 1/2 is large-sieve-limited).
- `twin_bar : J₁F + J₂F ≤ 2·log 2·I₂F` with `two_log_two_lt_two` (Salt/TwinBar/Impossibility.lean:173,161)
  — OUR OWN kernel-checked parity-adjacent obstruction: the k = 2 Maynard functional cannot certify twins
  even at level θ = 1 (M₂ = 2log2 < 2). This is the formal in-house witness of where the ¬F-fed Maynard
  route dies.
PARITY-BREAKING INPUTS (bilinear / L-function / oracle-fed):
- HB-ENGINE (Salt/HB/, campaign in flight; Kloosterman inputs banked Salt/Weil/) — the parity-breaker is
  the exceptional character as Möbius surrogate (GROUNDED H-B p.196) + Estermann/Kloosterman bilinear
  (GROUNDED p.221 eq. 7.1). **Lives entirely on the F horn: ¬F is the hypothesis that deletes its oracle.**
- `log_chowla_two_final` (Salt/Entropy/Chowla/SpineFinal.lean:416, THE CITATION THEOREM) — Tao's bilinear
  entropy-decrement parity-break, λ-side only; residual hypotheses are `MRTUniformity R δ` + entropy-budget
  inequalities (GROUNDED :416–428) — NONE is Siegel-sensitive; ¬F discharges nothing here, and by Tao's own
  statement the conclusion has no bearing on Λ(n)Λ(n+2).

**Where each ¬F-fed route hits the wall, exactly:**
1. ¬F → eff. SW/Linnik → BV → Maynard: dies at k = 2 — `twin_bar` (2log2 < 2); bounded gaps survive
   unchanged (already landed unconditionally).
2. ¬F → eff. SW → Chen weighted sieve: dies at P₂ → prime (Type-I axioms; Selberg parity examples).
3. ¬F → eff. ZFR → binary Λ-correlations: no route exists — ZFRs bound linear averages ψ(x;q,a);
   Λ(n)Λ(n+2) is not a linear functional of AP-counts; circle-method minor arcs eat binary problems
   (MEMORY, classical).
4. ¬F → L(1,χ) ≫ 1/log q → effective class numbers h(−d) ≫ √d/log d (MEMORY: classical Hecke/
   class-number-formula equivalence) — REAL cash, the famous ¬F cash-out (effective Gauss problem) —
   but consumer-free in Salt (no class-number module) and twin-irrelevant.

**Central verdict:** ¬F carries NO parity-breaking input. It deletes the only unconditional-family
parity oracle (the exceptional character) and pays back effectivity; every effectivity consumer is
sieve-side, hence parity-capped. All twin content of the dichotomy lives on the F horn.

---

## 5. Known "no-Siegel ⟹ twins-adjacent" conditionals — the null result (ALL MEMORY, FLAGGED LOUD)

After a deliberate sweep: **I know of NO published result of the form "no Siegel zeros ⟹ (twins /
twin-adjacent lower bound)". The traffic is one-way, onto the zeros horn:**
- H-B 1983 (GROUNDED, the source): zeros ⟹ twin asymptotics in q-windows.
- MEMORY: Friedlander–Iwaniec (exceptional characters ⟹ primes in short intervals / illusory-sieve
  yields); Tao–Teräväinen 2021 (Siegel zeros ⟹ Hardy–Littlewood–Chowla correlations in ranges);
  Chinis (Siegel zeros ⟹ log-Chowla-type cancellation). All F-horn.
- MEMORY: the ¬F direction's entire known yield: effective Linnik/SW/PNT-AP (§1), effective class
  numbers/Gauss (§4.4), effective Tatuzawa-window cleanups, deletion of the DH case in zero-density
  arguments, cleaned explicit-BV variants. NOT ONE twin-adjacent statement among them.
- Structural reason (composite of GROUNDED pieces): the no-zero horn only upgrades LINEAR (single-prime)
  statements from ineffective to effective; twin-type statements need bilinear/parity-breaking input
  (chowla.txt:124–131, H-B p.196 mechanics), which ¬F removes rather than supplies.
- The one honest near-exception: H-B p.196's license — ¬F simplifies HYPOTHESES of future twin work
  (may assume no Siegel zeros). A license is not a theorem; per the C⁽³⁾ proposition (p.196) it must
  not be dressed as one.

**In-repo logical consequence (GROUNDED):** ¬F ⟹ ¬InfinitelyManySiegelZeros by contrapositive of
`imsz_implies_fulcrum_of_gadget` (Salt/Fulcrum/Basic.lean:193, given the landed gadget interface
`SiegelModulusUnbounded`, Basic.lean:73; witnesses via Gadget.lean:93,128). So the ¬F horn also
formally starves the HB-ENGINE's feeder hypothesis — the F-horn machine is not merely unhelped by ¬F,
it is refuted at C⋆ by it.

---

## Fossil check (catch #239)
All Lean names/lines re-grepped live 2026-07-19; H-B cites from today's PDF read (pp. 193–198, 221–224);
montgomery3.txt/chowla.txt line numbers from today's greps. `C⋆` is a design-name (parametric C in-repo),
not a defined Lean constant — do not cite it as one.
