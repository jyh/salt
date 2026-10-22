# Errata to the submitted manuscript (2026-10-22)

This manuscript (`main.tex` beside this file; submitted to Forum of Mathematics, Pi on 2026-08-18; Zenodo
10.5281/zenodo.23106948) says more than its Lean proves in the places listed below. No Lean statement is wrong.
Each place is corrected by the statement shown, which names the declaration it paraphrases (salt `4844dbc6`).
Since submission, a later declaration (`logChowla2_v7_rated`, 2026-08-30) proves the window bound of Theorem
thm:spine with no hypothesis, at one opaque margin; see C1. A revised manuscript is in preparation. The
manuscript itself is kept as submitted.

## A claim dated after submission: the 7/8 claim (2026-10-22)

OpenAI's preprints dated 2026-09-30 and 2026-10-01 (published with Lean sources at `github.com/openai/math`
from 2026-10-06) claim that no Dirichlet L-function has a zero with real part above 7/8, for every modulus and every character, and that
there are no Siegel zeros. The Lean proof of the 7/8 claim was kernel-checked on our machine, 2026-10-22, from
OpenAI's pinned source (`openai/math` 1581d4cbdd69): the full environment of 561,427 declarations replayed by
`leanchecker --fresh`, and the theorem depends on the three standard axioms only (`#print axioms`). The statement
was matched by elaboration, not by OpenAI's comparator; OpenAI's 23 patches to third-party packages were applied
as their build applies them, and their content was not read (mathlib is not patched); and this checks their Lean
proof, not the preprint's argument. The steps of that run are written down, with two additions, as
`scripts/replay_openai_seven_eighths.sh`, which has not itself been run end to end yet. This repository does not
import that proof. It restates the 7/8 statement over its own mathlib as `DirichletSevenEighths` and proves that
it implies `NoSiegelZeros` (`noSiegelZeros_of_sevenEighths`, in `Salt/TwinBar/SevenEighthsClaim.lean`). Whether
OpenAI's mathlib (`d13f23b7`) and this repository's define the L-function identically has not been checked yet, so
OpenAI's theorem does not discharge `DirichletSevenEighths` here.
If the 7/8 claim is true of the L-function as mathlib defines it, the fulcrum
hypothesis F(C) is false at every C > 0, including the C⋆ of the manuscript: a witness of modulus q with
C log q > 8 has a zero ρ with |1 − ρ| < 1/8, so Re ρ > 7/8, which the claim excludes, since the
character is nontrivial. The dichotomy TPC ∨ NoSiegelZeros is then decided
through its NoSiegelZeros side and says nothing about twin primes; the manuscript's twin horn, "Siegel zeros
produce infinitely many twin primes", is an implication whose hypothesis would be false, so it would hold vacuously; and the reality
theorem at C ≥ 253696 and the Deuring–Heilbronn repulsion contract hold vacuously. The deductions about F(C) and the vacuous horns are
short and are not formalized here; the step to `NoSiegelZeros` is. The claim makes no Lean statement the manuscript cites false.
The manuscript's framing of F(C) as a live hypothesis is what the claim, if it holds, overtakes.

## The five corrected statements (what the Lean proves)

**C1, log-Chowla.** `log_chowla_two_door_only` (Salt/Entropy/Chowla/SpineFinal.lean:981) proves: there are δ₀ > 0
and one regime R (one x, one ω, one ε) such that, if `MRTUniformity R δ` holds for some 0 < δ ≤ δ₀, then
|Σ_{x/ω < n ≤ x} λ(n)λ(n+1)/n| ≤ ε·log ω (that inequality is `¬ logChowla2Fails`, ChowlaFailure.lean:59).
`log_chowla_two_budget_head` (SpineFinal.lean:750) gives, at one fixed ε, such a regime above every floor on
`R.Hlo`, under the weaker hypothesis `MRTUniformityXi` (`mrtUniformity_implies_xi`, MRTDoor.lean:120). Neither
states the logarithmic two-point Chowla statement (the limit as x → ∞, which is Tao's theorem), and the hypothesis
is assumed at the constructed regime, not proved.
**Added 2026-10-21:** a later declaration, `logChowla2_v7_rated`
(Salt/MR/V7Rated.lean:973, landed 2026-08-30, in MR/All.lean's `#audit_axioms` list, no `sorry`), proves the same
window inequality **with no hypothesis**: for every floor `A₀`, at an opaque ε ≥ 1/500 (which the statement lets
depend on `A₀`) and a regime above `A₀`. It is still a
single-scale bound and does not state the limit. So the short form below is exact for `log_chowla_two_door_only`
and the 08-18 manuscript's Theorem thm:spine; a sentence about **the corpus's** Chowla result now reads "a
single-scale bound on the two-point logarithmic Chowla sum, proved with no hypothesis at one opaque margin
(2026-08-30); the limit statement is not formalized".
*Short form:* "a single-scale bound on the two-point logarithmic Chowla sum, at one constructed regime, assuming a
Matomäki–Radziwiłł–Tao-type uniformity hypothesis at that regime".

**C2, minimality.** `FulcrumQualityMin C` (Salt/Fulcrum/Basic.lean:61) is a definition. No Lean declaration states
that it is minimal, weakest, or the weakest hypothesis for any engine. "Weakest" describes how it was found.
*Short form:* "the fulcrum hypothesis F(C)", with no superlative.

**C3, strengthened / effective.** `fulcrum_dichotomy` (Salt/Fulcrum/Dichotomy.lean:102) assumes `hC : 0 < C` and
`hEngine : FulcrumQualityMin C → TwinPrimeConjecture` and concludes `HeathBrownDichotomy`, i.e. TPC ∨
NoSiegelZeros (SiegelTwin.lean:97). Infinitely many Siegel zeros give F(C) for every C > 0
(`imsz_gives_fulcrum_witnesses`, Gadget.lean:128), so the hypothesis implies Heath-Brown's statement, which is
equivalent to the conclusion (`heathBrown_iff_dichotomy`, SiegelTwin.lean:136; the composition is not itself a named
lemma). The theorem is not stronger than Heath-Brown's; it says an engine that starts from F(C) would suffice. The
¬F horn, `not_fulcrum_implies_noSiegelZeros` (Dichotomy.lean:82), is unconditional (given `0 < C`), and its constant
is a bare existential reached by contradiction; no numeral is extracted (its docstring, Dichotomy.lean:79–81:
"effective-in-(Q, c(Q)) only in principle, no extracted numeral").
*Short form:* "a conditional form of Heath-Brown's dichotomy, with the engine as a named hypothesis; the ¬F horn is
unconditional, its constant not computed".

**C4, rate / census.** `neutrality_rate` (Salt/HB/SignRate.lean:53) proves S₁ ≤ S₂(f) for every sign function f
(`S1_le_S2Gen`, SignChain.lean:511) and returns its own hypothesis `hbudget` as the upper bound, through the ring
identity `S2Gen_sub_S1_eq` (SignChain.lean:519). For a general sign function no upper bound on S₂ − S₁ is proved
(the generic master `hb_l2c_masterGen` exists only in a comment, SignRate.lean:66–78). For real characters,
`hb_l2c_master_unconditional` (Salt/HB/L2cMasterUncond.lean:85) bounds S₂ − S₁ unconditionally, in the range
100¹⁶ ≤ z, Lwin(x)⁸ ≤ z, z³ ≤ x, by a row that does
not involve the pretense sum, plus a row proportional to `PretenseSum χ`, plus an error row; so no Lean statement
makes the price "exactly a pretense sum". At f = λ the difference is zero (`S2Gen_lamR_eq_S1`,
SignLiouville.lean:97; λ's pretense sum is zero, `PretenseSumGen_lamR_eq_zero`, :109). The census
(Salt/Parity/Instances.lean) applies `parityInv_of_closed` (Salt/Parity/Z.lean:117), which holds for every true
proposition, to ten theorems; it carries no information about them (Instances.lean:25–28).
*Short form:* "the transfer inequality S₁ ≤ S₂(f)"; the census is not cited as a result.

**C5, VMVT.** `vmvt` (Salt/Vmvt/Summit2.lean:151) proves `VmvtBound k r x` (Vmvt/MeanValue.lean:172):
J_k(x, kr) ≤ k^{24k²r} · x^{2rk − k(k+1)/2 + η}, η = ½k²(1 − 1/k)^r, for k ≥ 2, r ≥ 1, x ≥ 1. That is the classical
Vinogradov mean value bound (Vaughan's notes, Thm 24.5), with an explicit constant, not the main conjecture proved by Bourgain–Demeter–Guth and
by Wooley. *Short form:* "the classical Vinogradov mean value bound".

## The entries

Line numbers are `main.tex`'s; page numbers are the submitted PDF's where known. Each entry quotes the sentence
as submitted and the sentence that corrects it, both as TeX source.

**F1. :157–158, abstract, p. 1 [C2].** The sentence:
```text
the zero's reality is derived rather than assumed, and the fulcrum is proved minimal for the engine that consumes it.
```

Corrected:
```text
the zero's reality is derived rather than assumed.
```

**F2. :159–160, abstract, p. 1 [C4].** The sentence:
```text
Around it we prove kernel-checked zero-free regions for $\zeta$, a Deuring--Heilbronn repulsion contract, an
exchange-rate neutrality theorem pricing transfer-based routes to twins, and the parity gap as a mathematical object.
```

Corrected:
```text
Around it we prove kernel-checked zero-free regions for $\zeta$, a Deuring--Heilbronn repulsion contract, the
transfer inequality $S_1 \le S_2(f)$ for every real sign function $f$, and the parity gap as a mathematical object.
```

**F3. :198–201, overview, pp. 1–2 [C2].** The sentence:
```text
Siegel zeros produce infinitely many twin primes; the fulcrum is proved minimal for the engine that consumes it,
with the zero's reality \emph{derived} rather than assumed.
```

Corrected:
```text
Siegel zeros produce infinitely many twin primes, with the zero's reality \emph{derived} rather than assumed.
```

**F4. :211–213, overview, p. 2 [C4].** The sentence:
```text
the \emph{exchange-rate wall}, a neutrality theorem over arbitrary real sign functions that prices every
transfer-based route to twins;
```

Corrected:
```text
the \emph{exchange-rate wall}: the transfer inequality $S_1 \le S_2(f)$ over arbitrary real sign functions, with
equality at $f = \lambda$, and for real Dirichlet characters, in a stated range, an unconditional upper bound on
$S_2 - S_1$;
```

**F5. :215–217, overview, p. 2 [C4].** The sentence:
```text
a predicate $Z$ with a kernel-checked theorem that no twin-sufficient, parity-invariant completion exists,
together with a census placing ten headline theorems of the corpus inside the parity-invariant cone.
```

Corrected:
```text
a predicate $Z$ with a kernel-checked theorem that no twin-sufficient, parity-invariant completion exists.
```

**F6. :217–220, overview, p. 2 [C1].** The sentence:
```text
As a byproduct, the logarithmic two-point Chowla statement---a theorem of Tao---is machine-checked conditionally
on a single named uniformity hypothesis.
```

Corrected:
```text
As a byproduct, at one constructed regime the two-point logarithmic Chowla sum over one window is bounded by
$\varepsilon\log\omega$, assuming a Matom\"aki--Radziwi\l\l--Tao-type uniformity hypothesis at that regime. This
is a single-scale bound, not Tao's theorem, which is the limit statement. (A later declaration removes the
hypothesis at one opaque margin; see the erratum's C1.)
```

**F7. :248–250, p. 2 [C2].** The sentence:
```text
The fixed point of that process is the weakest twin-producing Siegel hypothesis in the surveyed record
(Definition~\ref{def:fulcrum});
```

Corrected:
```text
The fixed point of that process is the hypothesis $F(C)$ (Definition~\ref{def:fulcrum}); no Lean statement asserts
that it is the weakest;
```

**F8. :263, the roadmap [C2].** The sentence:
```text
the minimized hypothesis, the kernel-checked dichotomy it induces,
```

Corrected:
```text
the hypothesis $F(C)$, the kernel-checked dichotomy it induces,
```

**F9. :446–458, Remark rem:vmvtdate, p. 5 [C5].** The sentence:
```text
For this theorem the as-of dating requires more than the survey's default as-of form---a dated adversary
citation: the \texttt{lean-lang.org} evaluation board records its Vinogradov-mean-value problem---stated there in
full main-conjecture form---as solved on 2026-08-16 by a third-party submission (an automated system), verified
by the board's own same-statement comparator (kernel-accepted, axioms within the standard three), with the
solution source private and its publication announced for 2026-08-31. No public artifact proves the theorem as of
2026-08-17, but a kernel-grade, dated counter-attestation exists and its artifact is expected to be public before
review of this paper completes. We therefore attach no priority weight to Theorem~\ref{thm:vmvt}: it appears here
as the input that Theorem~\ref{thm:pow} consumes,
```

Corrected:
```text
Theorem~\ref{thm:vmvt} is the classical Vinogradov mean value bound (Vaughan's notes, Thm 24.5), with an explicit
constant and exponent $2kr - k(k+1)/2 + \eta$, $\eta = \tfrac12 k^2(1-1/k)^r$; it is not the main conjecture of
Bourgain--Demeter--Guth and Wooley. The \texttt{lean-lang.org} evaluation board records its Vinogradov-mean-value
problem, stated there in main-conjecture form, as solved on 2026-08-16 by a third-party submission whose source was
private as of 2026-08-17. The two exponents agree at $s = k$, and for every $s = kr$ with $r \ge 2$ the main
conjecture's is strictly smaller, so a public proof of it would supersede the exponent of Theorem~\ref{thm:vmvt}. We
therefore attach no priority weight to Theorem~\ref{thm:vmvt}: it appears here as the input that
Theorem~\ref{thm:pow} consumes,
```

**F10. :524–527, p. 6 [C2].** The sentence:
```text
this is the weakest shape for which the engine of \S\ref{sec:keystone} can run, and the demand audit certifies
that \emph{this} engine leaves nothing weaker on the table.
```

Corrected:
```text
this is the shape the engine of \S\ref{sec:keystone} consumes; the demand audit found nothing weaker that it could
consume, and no Lean statement asserts minimality (Appendix~A).
```

**F11. :597–600, p. 6 [C3].** The sentence:
```text
The second horn is thus the Heath-Brown dichotomy, machine-checked and strengthened: strengthened because the
hypothesis feeding its twin horn is the minimized fulcrum rather than the 1983 hypothesis, and because the
$\lnot F$ horn is unconditional and effective.
```

Corrected:
```text
The second horn is thus a conditional form of the Heath-Brown dichotomy, machine-checked, with the engine as a
named hypothesis. It is not stronger than Heath-Brown's statement: infinitely many Siegel zeros give $F(C)$ for
every $C > 0$, so the engine hypothesis implies Heath-Brown's. The $\lnot F$ horn is unconditional (for $C > 0$);
its constant is a bare existential reached by contradiction, and no numeral is extracted.
```

**F12. :689–691, p. 8 [C4].** The sentence:
```text
The wall states: this exchange is \emph{never free, and its price is exactly a pretense sum}---and it says so for
arbitrary real sign functions, a class strictly wider than Dirichlet characters.
```

Corrected:
```text
What is proved: for every sign function $f$ (Definition~\ref{def:sign}; the class carries no modulus and contains no
Dirichlet character of modulus $> 1$), the exchange never lowers the sum ($S_1 \le S_2(f)$); for real Dirichlet
characters, in the range of Theorem~\ref{thm:master}, $S_2 - S_1$ is bounded above unconditionally by a row free of
the pretense sum, a row proportional to $\mathrm{PS}_\chi$, and an error row; and at $f = \lambda$ the exchange is
free ($S_2(\lambda) = S_1$). No Lean statement makes the price exactly a pretense sum.
```

**F13. :722–725, p. 8 [C4].** The sentence:
```text
Read together: any route that would extract twins from a transfer must pay in pretense, the currency
$\mathrm{PS}_f$; the one sign function with $\mathrm{PS} = 0$ is the one at which the transfer returns exactly the
twin sum it was fed.
```

Corrected:
```text
Read together: no transfer lowers the twin sum, and $\lambda$, whose pretense sum is zero, is a sign function at
which the transfer returns exactly the twin sum it was fed. An upper bound on the price is proved for real
characters (in a stated range) and, trivially, at $f = \lambda$; for a general sign function none is proved.
```

**F14. :802–818, Proposition prop:census [C4].** The sentence:
```text
\begin{proposition}[The census]\label{prop:census} Ten headline theorems of the corpus lie inside the
parity-invariant cone: the transfer's unconditional leg $S_1 \le S_2$; [… the ten listed …] and Chen's second
theorem (every sufficiently large even $N$ is $p + q$ with $p$ prime and $q$ a $P_2$). [the \leanname line] \end{proposition}
```

Corrected (a remark, not a proposition):
```text
\begin{remark}[The closure schema]\label{rem:closure} The schema \leaninline{parityInv\_of\_closed} applies to ten
headline theorems of the corpus: [the same ten]. The schema makes any proved statement that does not mention a
completion parity-invariant, as a constant predicate, so this carries no arithmetic information about them.
\leanname{Salt/Parity/Instances.lean (ten declarations, one per theorem)} \end{remark}
```

**F15. :821–825, p. 9 [C4].** The sentence:
```text
The three results triangulate the frontier exactly: the corpus's censused headline theorems live inside the cone
(Proposition~\ref{prop:census}); the twin prime conjecture is equivalent to a demand $Z$ (Theorem~\ref{thm:ziff});
and that demand cannot be met inside the cone (Theorem~\ref{thm:gap}).
```

Corrected:
```text
Two results locate the frontier: the twin prime conjecture is equivalent to a demand $Z$
(Theorem~\ref{thm:ziff}), and that demand cannot be met inside the cone (Theorem~\ref{thm:gap}).
```

**F16. :835–838 [C1].** The sentence:
```text
Independently of the Siegel-zero tracks, the corpus carries a full formalization of the entropy-decrement route to
the logarithmic two-point Chowla statement, proved by Tao~\cite{TaoChowla}; the content here is the
machine-checked reduction, not the truth of the statement.
```

Corrected:
```text
Independently of the Siegel-zero tracks, the corpus formalizes the entropy-decrement argument of
Tao~\cite{TaoChowla} at one finite scale: at one constructed regime it bounds the two-point logarithmic Chowla sum
over one window, assuming a Matom\"aki--Radziwi\l\l--Tao-type uniformity hypothesis there. It does not formalize
Tao's theorem, which is the limit statement. (A later declaration removes the hypothesis at one opaque margin; see
the erratum's C1.)
```

**F17. :845–851, Theorem thm:spine, p. 10 [C1].** The sentence:
```text
There exist $\delta_0 > 0$ and a regime $R$ such that a single hypothesis ---the Matom\"aki--Radziwi\l\l--Tao
uniformity door $\mathrm{MRTUniformity}\,R\,\delta$ at any $0 < \delta \le \delta_0$--- implies the logarithmic
two-point Chowla statement at $R$. A $\forall$-quantified head version places the regime floor above any
prescribed threshold.
```

Corrected:
```text
There exist $\delta_0 > 0$ and a regime $R$ (fixing, among other data, a scale $x$, a window $\omega$, a margin
$\varepsilon$ and a range $[H_-, H_+]$ of window lengths) such that, if $\mathrm{MRTUniformity}\,R\,\delta$ holds for
some $0 < \delta \le \delta_0$, then $\bigl|\sum_{x/\omega < n \le x} \lambda(n)\lambda(n+1)/n\bigr| \le
\varepsilon\log\omega$. A head version, at one fixed $\varepsilon$ and under the weaker hypothesis
$\mathrm{MRTUniformityXi}$, gives such a regime above any prescribed floor.
```

**F18. :331–335, p. 3 [C4]**. The sentence:
```text
Non-vacuity is proved by witness: the fulcrum's zero-reality is derived from our own zero-free region
(Theorem~\ref{thm:fulcrumreal}); the parity census instantiates its cone with ten corpus theorems; classical
corollaries are re-derived from our statements, which a misstated premise would break.
```

Corrected:
```text
Non-vacuity is proved by witness: the fulcrum's zero-reality is derived from our own zero-free region
(Theorem~\ref{thm:fulcrumreal}); classical corollaries are re-derived from our statements, which a misstated premise
would break.
```

**F19. :588–590, p. 6 [C3]**. The sentence:
```text
i.e.\ some single effective constant pushes every real zero of every primitive quadratic character---all moduli, no
exceptions---away from $s = 1$ at the scale $1/\log q$.
```

Corrected:
```text
i.e.\ some single constant pushes every real zero of every primitive quadratic character---all moduli, no
exceptions---away from $s = 1$ at the scale $1/\log q$ (an existential constant; where it is produced below, no
numeral is extracted).
```

**F20. :725–728, p. 8 [C4]**. The sentence:
```text
The wall is falsifiable---exhibit a sign function with bounded pretense sum and an $S_2$-evaluation that does not
route through $S_1$---and it is stated over the full sign-function cone precisely so that its scope is a theorem
rather than an impression.
```

Corrected:
```text
The lower inequality $S_1 \le S_2(f)$ is a theorem over the full sign-function cone. The pricing is not: inside the
cone an upper bound on $S_2(f) - S_1$ is proved only at $f = \lambda$, and the unconditional bound of
Theorem~\ref{thm:master} is stated for real Dirichlet characters, not for sign functions.
```

**F21. :856–863, p. 10 [C1]**. The sentence:
```text
Here the logarithmic two-point Chowla statement at scale $x$ is the standard one, \[ \frac{1}{\log x} \sum_{n \le x}
\frac{\lambda(n)\,\lambda(n+1)}{n} \;\longrightarrow\; 0, \] rendered in the corpus as the failure of a quantified
$\varepsilon$-deviation over the regime's windows.
```

Corrected:
```text
The logarithmic two-point Chowla statement is the limit \[ \frac{1}{\log x} \sum_{n \le x}
\frac{\lambda(n)\,\lambda(n+1)}{n} \;\longrightarrow\; 0; \] the corpus does not state it. Theorem~\ref{thm:spine},
under its hypothesis, bounds one regime's window: $\bigl|\sum_{x/\omega<n\le x}\lambda(n)\lambda(n+1)/n\bigr| \le
\varepsilon\log\omega$.
```

**F22. :876–880, p. 10 [C1]**. The sentence:
```text
The door is the exact target of the corpus's staged Matom\"aki--Radziwi\l\l\ program \cite{MR2016} (whose first
stones, including the closure of a long-flagged Euler-oscillation bridge, landed the same day); the conjecture's
entire residual is thus one named seam between two formalized campaigns.
```

Corrected:
```text
The door is the target of the corpus's staged Matom\"aki--Radziwi\l\l\ program \cite{MR2016} (whose first stones,
including the closure of a long-flagged Euler-oscillation bridge, landed the same day). Between
Theorem~\ref{thm:spine} as stated and Tao's theorem stand two things: the uniformity hypothesis at the regime, and
the passage from one window at one margin $\varepsilon$ to the limit, which no declaration states. A later
declaration, \leaninline{Salt.MR.logChowla2\_v7\_rated} (2026-08-30), removes the first: it proves such a window
bound, at one opaque $\varepsilon \ge 1/500$ and at regimes above any floor, with no hypothesis. The second remains.
```

**F23. :1437, Appendix A [C4]**. The sentence:
```text
\textbf{Proposition~\ref{prop:census}} (the census).
```

Corrected:
```text
\textbf{Remark~\ref{rem:closure}} (the closure schema).
```

**F24. :445 and :259–261, the remark's title and its pointer [C5]** (follows F9). The sentence:
```text
\begin{remark}[A dated qualification]\label{rem:vmvtdate}

(The Vinogradov mean value theorem that feeds the latter carries its own dated qualification, stated at
Remark~\ref{rem:vmvtdate}.)
```

Corrected:
```text
\begin{remark}[The classical bound]\label{rem:vmvtdate}

(The Vinogradov mean value bound that feeds the latter is the classical one; see Remark~\ref{rem:vmvtdate}.)
```

**F25. :733–734, p. 8 [C4]**. The sentence:
```text
that the deletion is sound is itself part of the formal content: the character was never necessary.
```

Corrected:
```text
that the deletion is sound is itself part of the formal content: for the inequality $S_1 \le S_2(f)$ the character
was never necessary. No upper bound on $S_2(f) - S_1$ is proved for a sign function other than $\lambda$.
```

**F26. :1450–1451, Appendix A [C4]**. The sentence:
```text
so the census is one lemma about where a closed proposition sits, instantiated ten times.
```

Corrected:
```text
so the ten are one lemma about closed propositions, instantiated ten times, and carry no arithmetic information.
```

**F27. :863–866, p. 10 [C1]**. The sentence:
```text
The door is the Matom\"aki--Radziwi\l\l--Tao uniformity property restricted to the bounded large-spectrum
frequency set $\Xi_H$ (of size $\le K$, independent of $H$):
```

Corrected:
```text
The head version's hypothesis, $\mathrm{MRTUniformityXi}$, is the Matom\"aki--Radziwi\l\l--Tao uniformity property
restricted to the bounded large-spectrum frequency set $\Xi_H$ (of size $\le K$, independent of $H$);
Theorem~\ref{thm:spine} itself assumes the unrestricted $\mathrm{MRTUniformity}$, which implies it. The restricted
form reads:
```


(The manuscript's own Appendix A, :1155–1157, already says *"no declaration in the corpus asserts the minimality
claimed for it in §sec:fulcrum"*; F1, F3, F7, F8 and F10 are where the body contradicts it.)
