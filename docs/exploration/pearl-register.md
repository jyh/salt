# THE PEARL REGISTER

*The pearl doctrine (fleet council, 2026-07-27, JYH-ratified): "effectivity
is a jewel, never a blocker... we will take a line from our friend Ahab and
track it, within reason." This register tracks every point where
ineffectivity enters the main chain — each entry is a pearl we may one day
dive for, never a debt that stalls the road. The kernel does not care;
we do, aesthetically, and this is where that care lives.*

## P-1 — the even-χ band constant (ENTERED 2026-07-28, council C3)

**Where:** `LFunction_band_lower` (Salt/MR/SiegelArm.lean:161) — the EVT
compact-minimum on bandBox [1,2]×[−1,1] producing the per-χ constant B_χ;
lifted to the finite max B(W) over {χ mod q : q ≤ W} by
`chi_Llower_band_uniform` (the C3 stones); consumed by the regime g-arm
through `log_chowla_two_budget_head_g` (landed f8be05e).

**What it buys:** the entire even-χ/Siegel-corner quality floor — the
campaign's last analytic residual — with no Siegel completion, no
class-number formula, no CNF port. The Siegel-zero dichotomy is absorbed
into the regime choice: x is taken large enough relative to Hhi that even
a Siegel-zero character's floor clears, without ever knowing how large
"large enough" is effectively.

**The confinement (why this pearl is small):** the ineffective set is
exactly {real even primitive χ}. The odd-real lane keeps the fully
effective π·q^{−5/2} floor (L1_lower_odd, Sawtooth.lean); non-real and
principal lanes are unconditional with explicit constants. One constant,
one file, one arm.

**The dive (if we ever go):** any even-χ `L1LowerEffective` production —
the Siegel-completion ε-form (SiegelFinal.lean:324, two named gaps), the
class-number route, or a CNF/FE port — re-effectivizes B(W) and this
entry closes. The interface stays open at the register as
paper-completeness; nothing in the machine-checked chain waits on it.

**Axiom posture:** unchanged — [propext, Classical.choice, Quot.sound];
Classical.choice was already load-bearing (gJoin's arms, mathlib's
character fintype). The pearl is *quantitative* ineffectivity, not an
axiom.
