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
