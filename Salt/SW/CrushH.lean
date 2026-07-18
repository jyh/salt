/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.CrushC
import Salt.SW.CrushE

/-!
# T-BAL R5h — `H_lower` (the crush glue; R5 COMPLETE)

The freeze:11 R5 row in the amended (δ = 0) form: `H(z) ≥ L₁/((1−β₀)(2−β₀))`. Pure composition of
the landed crush stones:

* R5c `selHSum_ge_dhA_div_sum` (CrushC) — `Σ_{n≤z} dhA(n)/n ≤ H(z)`;
* R5e `dhAbel_inner_ge` (CrushE) — the free-cut lower Abel bound with the explicit error
  `crushErr` at the cut `crushCut β₀ z ~ √(z/(1−β₀))`;
* R5f `crush_coverage` + R3 `L1_lower_siegel` (Crush/DHCore) — the coverage collapse
  `z^{−u}·crushErr ≤ L₁/(2−β₀)`;
* the R5h algebra `H_lower_of_parts` (Crush).

Guard-gated like `L1_lower_siegel`: the deep-regime guards (`hN`/`hscale`/`hguard` at the Siegel
scale `N = ⌊e^{1/u}⌋`) and the coverage guard `hcov` (at the ledger's `z = ⌈Q¹²u^{−3}⌉` the
crushed error is ≤ `0.27u` with margin 114x at the q=3 u*-corner at Z₀ = 100, growing in q and
into the deep ray — `scripts/tbal_ledgers/r5_crush_ledger.py`) are discharged downstream by R8's
ledger arithmetic.
-/

namespace Salt.SW

/-- **The crush cut** `D = ⌊√(z·min(⌈1/(1−β₀)⌉, z))⌋ ~ √(z/(1−β₀))` — R5e's free hyperbola cut.
The `min _ z` cap keeps `D ≤ z` for every `z ≥ 2` (small `z` degrades to the symmetric cut). -/
noncomputable def crushCut (β₀ : ℝ) (z : ℕ) : ℕ :=
  Nat.sqrt (z * min ⌈(1 : ℝ) / (1 - β₀)⌉₊ z)

/-- **The crush error** — R5e's explicit error at the cut `crushCut β₀ z`:
`34D·z^{−β₀} + 12M·z^{1−β₀}/((1−β₀)D) + 12M·z^{1−β₀}/D + 6M(Z₀+1/(1−β₀))·D^{−β₀}`,
`M = √q(1+log q)`. Every term crushes (÷ `z^{1−β₀}`) to ONE clean power of `(1−β₀)` at the ledger
scale — the half-power gain over the symmetric `√z` cut that makes coverage close. -/
noncomputable def crushErr (q : ℕ) (Z₀ β₀ : ℝ) (z : ℕ) : ℝ :=
  34 * (crushCut β₀ z : ℝ) * (z : ℝ) ^ (-β₀)
    + 12 * (Real.sqrt q * (1 + Real.log q)) * (z : ℝ) ^ (1 - β₀)
        / ((1 - β₀) * (crushCut β₀ z : ℝ))
    + 12 * (Real.sqrt q * (1 + Real.log q)) * (z : ℝ) ^ (1 - β₀) / (crushCut β₀ z : ℝ)
    + 6 * (Real.sqrt q * (1 + Real.log q)) * (Z₀ + 1 / (1 - β₀)) * (crushCut β₀ z : ℝ) ^ (-β₀)

/-- R5e (`dhAbel_inner_ge`) restated through `crushErr` (definitional repackaging). -/
lemma dhAbel_inner_ge_err [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β₀ : ℝ}
    (hzero : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0) (hlo : 1 / 2 ≤ β₀) (hhi : β₀ < 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {z : ℕ} (hz : 2 ≤ z) :
    (DirichletCharacter.LFunction χ 1).re * (z : ℝ) ^ (1 - β₀) / (1 - β₀) - crushErr q Z₀ β₀ z
      ≤ ∑ n ∈ Finset.Icc 1 z, dhA χ n * (n : ℝ) ^ (-β₀) := by
  have h := dhAbel_inner_ge χ hχ hsq hq hzero hlo hhi hZ hz
  simpa only [crushErr, crushCut] using h

/-- **T-BAL R5h — `H_lower` (R5 COMPLETE).** The freeze:11 amended (δ = 0) Selberg-mean lower
bound: for a real primitive `χ` at a real zero `β₀`, under the deep-regime guards (the
`L1_lower_siegel` scale `N` and the coverage guard at `z`),
`L(1,χ).re/((1−β₀)(2−β₀)) ≤ H(z) = selHSum χ z`.
This is the exact reciprocal partner of R4's `selberg_opt_eq` (`V(λ^opt) = 1/H(z)`), turning the
R6 main term `L₁·V·x^{1−β₀}/(u(2−β₀))` into `≤ (1+o(1))·x^{1−β₀}` — the crush chain
`H ≥ Σ_{n≤z} dhA(n)/n ≥ z^{−u}·A(z) ≥ z^{−u}(L₁z^{1−β₀}/u − crushErr) ≥ L₁/(u(2−β₀))`. -/
theorem H_lower [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β₀ : ℝ}
    (hzero : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0) (hlo : 1 / 2 ≤ β₀) (hhi : β₀ < 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {N : ℕ} (hN : 4 ≤ N) (hscale : (N : ℝ) ^ (1 - β₀) ≤ Real.exp 1)
    (hguard : 2 * (34 + 12 * (Real.sqrt q * (1 + Real.log q))
        + 12 * (Real.sqrt q * (1 + Real.log q)) * Z₀
        + 36 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀)) * (N : ℝ) ^ (1 / 2 - β₀) ≤ 1 / 64)
    {z : ℕ} (hz : 2 ≤ z)
    (hcov : crushErr q Z₀ β₀ z ≤ 27 / 100 * ((1 - β₀) * (z : ℝ) ^ (1 - β₀))) :
    (DirichletCharacter.LFunction χ 1).re / ((1 - β₀) * (2 - β₀)) ≤ selHSum χ z := by
  have hL1 : 27 / 100 * ((1 - β₀) * (2 - β₀)) ≤ (DirichletCharacter.LFunction χ 1).re :=
    L1_lower_siegel χ hχ hsq hq hzero hlo hhi hZ hN hscale hguard
  exact H_lower_of_parts χ hsq (by omega) (by linarith) hhi
    (selHSum_ge_dhA_div_sum χ hsq z)
    (dhAbel_inner_ge_err χ hχ hsq hq hzero hlo hhi hZ hz)
    (crush_coverage χ (by omega) hhi hcov hL1)

end Salt.SW
