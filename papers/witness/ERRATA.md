# Errata to the published manuscript (2026-10-25)

This manuscript (`main.tex` beside this file; *The Pearl and the Toll*, published on Zenodo 2026-09-24 as
10.5281/zenodo.22942698, sources 10.5281/zenodo.21828638) says more than its Lean proves in the places listed below.
No Lean statement is wrong. Each place is corrected by the statement shown, which names the declaration it
paraphrases. The manuscript itself is kept as published. Line numbers are `main.tex`'s.

## The entries

**W1. :571–574, §sec:toll, "What the toll means"**. The sentence:
```text
There is no slack to find: the entire price of crossing $\log 2$ at design constant $A$ is $4^{A}$ in
doubly-logarithmic width, and both directions of that sentence are theorems.
```

Corrected:
```text
There is little slack to find: the price of crossing $\log 2$ at design constant $A$ lies between $4^{(20/21)A}$
and $\frac{21}{20}\,4^{A}$ in doubly-logarithmic width, and both bounds are theorems.
```

(The two bounds are `towerFlat_width_ge` and `towerFlat_width_le` (`Salt/Entropy/Chowla/TowerFlat.lean`), the
paper's Theorems thm:tollge and thm:tollle; no declaration states the price as exactly $4^{A}$. The manuscript's own
bracket, eq:bracket at :490–493, says so.)

(The same claim in short at :579–580, *"On the flat road the toll is a factor $4^{A}$ on the width"*: read it as the
bracket above.)

**W2. :97–100, abstract**. The sentence:
```text
Every theorem in this paper is verified by the Lean~4 kernel over \textsf{mathlib}, with axiom base exactly
$\{\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}\}$; nothing rests on informal argument.
```

Corrected:
```text
Every theorem in this paper names a Lean~4 declaration that the kernel checks over \textsf{mathlib}, with the axiom
base Appendix~\ref{app:index} states for each. Where a theorem's wording says more than its declaration (the entries
here), the declaration is what is proved.
```

(The flagship's F28 corrects the same sentence, `papers/flagship/ERRATA.md`. Measured 2026-10-25: all 17 theorem,
proposition, corollary, lemma and definition environments of this manuscript name a declaration. The axiom column of
Appendix A is not re-measured here.)

**W3. :271–275, introduction**. The sentence:
```text
The hypotheses sort in \S\ref{sec:pearl-hyp}: the eight riders are six ceilings on constants the theorem itself
produces and two windows of Siegel genre, and it is the Siegel pair that survives every removal \S\ref{sec:limit}
performs.
```

Corrected:
```text
The hypotheses sort in \S\ref{sec:pearl-hyp}: the eight riders are six ceilings on constants the theorem itself
produces and two windows of Siegel genre. \S\ref{sec:limit} removes the two windows first; what survives every
removal is Siegel's ineffective constant, carried by the rider $e^{-100} \le K_s$ and the cushion.
```

(`logChowla2_ineffective_v6` (`Salt/MR/RegisterCompose.lean:345`), the end of §sec:limit's chain, has neither window
among its hypotheses: they are `x₀ ≤ e^{e^{3.2A}/10}` and `H_opq ≤ ⌈e^{e^{3.2A}}⌉`, and its statement binds no `x₀` or
`H_opq`. The manuscript's own §sec:limit, :1278, opens the chain with "Step 1: the Siegel pair, by the limit", and
:295–297 names the surviving pair as `K_s` and the cushion.)

**W4. :119–126, abstract**. The sentence:
```text
The second theorem, the \emph{pearl}, is conditional and we name its conditionality at the statement: at every design
constant $A$ above an explicit floor there is a Chowla regime whose window base is pinned at
$\lceil e^{e^{3.2A}}\rceil$, and for that regime the logarithmically averaged two-point Chowla correlation does not
fail at the witnessed scale, on a list of hypotheses given in full in \S\ref{sec:pearl}: one analytic constant of the
band lane, eight numeric riders on constants the theorem itself produces, and two carried predicates.
```

Corrected:
```text
The second theorem, the \emph{pearl}, is conditional and we name its conditionality at the statement: for every
floor $A_0 \ge 162$ there are a design constant $A \ge A_0$ and a Chowla regime whose window base is pinned at
$\lceil e^{e^{3.2A}}\rceil$, and for that regime the logarithmically averaged two-point Chowla correlation does not
fail at the witnessed scale, on a list of hypotheses given in full in \S\ref{sec:pearl}: one analytic constant of the
band lane, eight numeric riders on constants the theorem itself produces, and two carried predicates.
```

(`logChowla2_witnessed_scale_flat_L_v2` (`Salt/MR/S16FlatFinal.lean:136`), Theorem thm:pearl, takes `A₀` with
`162 ≤ A₀` and produces one `A` with `A₀ ≤ A`; the manuscript's own :1201–1202 says "the theorem produces, for every
`A₀`, some `A ≥ A₀`". The hoisted form of §sec:limit, `logChowla2_witnessed_scale_flat_L_v2_uniform`
(`Salt/MR/S16Uniform.lean:891`), does hold at every `A` with `162 ≤ A` and `budgetAFlat ε β ≤ A`, but
`budgetAFlat ε β = 2304·log 4/(ε⁶β²)` is computed from constants the theorem produces, and only `0 < β` is known of
`β`, so that floor is not explicit.)

(Copies, measured 2026-10-25: the same claim stands in `pi-overview-draft.md` beside this file, a draft, and in the
description of the Zenodo record 10.5281/zenodo.22942698, which reproduces the abstract. W2's sentence stands in both
too. This file corrects them; the record's metadata is left as published.)

**W5. :1437–1439, "The five riders, by nature", the $K_{\mathrm{vt}}$ item**. The sentence:
```text
This is the single point at which Siegel's ineffective constant enters, and the cushion is therefore carried by
name, with the trace behind it rather than a bound.
```

Corrected:
```text
This is the one leg of the cushion that is not effective in $q$: the minimum is the extreme-value theorem's, which
is where a Siegel-type ineffectivity would enter, and the cushion is therefore carried by name, with the trace
behind it rather than a bound.
```

(The declaration, `Salt.MR.LFunction_band_lower` (`Salt/MR/SiegelArm.lean:161`), uses no Siegel input. Its docstring
says the minimum "is NOT effective in `q`: that, and only that, is where Siegel's ineffective constant would enter".
Siegel's theorem itself enters the corollary elsewhere: `xiCarveWidth_of_siegel` (`Salt/MR/PortClose.lean:76`)
obtains `siegel_real_carve` (`Salt/MR/PortAssembly.lean:1180`), which obtains `Salt.SW.siegel_theorem`. The
sentence holds only inside its own paragraph. Found by math's reach census, salt #525.)
