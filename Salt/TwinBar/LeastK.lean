/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.Impossibility
import Salt.TwinBar.ThreeBarAsm
import Salt.TwinBar.FourBarAsm
import Salt.Twelve.Certificate

/-!
# Sprint Q2c — the delimitation capstone: the least-k theorem

**Exploration sprint work item** (`docs/exploration/preregistration.md`, amendment
**A1** 2026-07-15; pilot ledger Q2bc-recon ~11:20). This file is PACKAGING only: it
gathers the four already-landed keystones under uniform, paper-facing names and
assembles the sprint headline. It adds NO new mathematics — every proof below is a
one-line re-export of a landed theorem. Sorry-free, `native_decide`-free, axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## The A1-ratified statement (read the carrier asymmetry BEFORE quoting)

> **In the unmodified Maynard–Selberg class, the least `k` with `M_k > 2` is `5`.**

This is landed in the **honest asymmetric form** deliberately — the two halves live in
DIFFERENT carriers and are NOT bridged into a single object:

* **The `k ∈ {2, 3, 4} no-gos** are *real-integral / continuous-`F`* statements. For each
  such `k`, NO continuous weight `F` on the `k`-simplex with positive `L²`-mass crosses the
  gate `2·I_k F < Σ_m J_m F`, because the Selberg pair is capped by
  `Σ_m J_m F ≤ c_k · I_k F` with `c_k = (k/(k−1))·log k < 2` (`twin_bar`/`three_bar`/
  `four_bar`). These delimit the CONTINUOUS-weight class.
* **The `k = 5` achievement** is the *exact rational (`ℚ`) bilinear certificate* `M5_cert`:
  the explicit degree-3 symmetric polynomial witness `F★` satisfies `2·I(F★) < Σ_m J(F★)`
  in exact Dirichlet arithmetic, i.e. `M₅ = 191881/95820 ≈ 2.00251 > 2`.

**The single-object bracket is registered debt.** Reconciling the two carriers — a
Dirichlet real-integral bridge that would place the `k = 5` witness in the same
real-integral functional as the no-gos (and the `2 < M₅ ≤ (5/4)·log 5` upper bracket) —
does NOT exist in the corpus and is recorded as debt (A1 point 3), NOT sprint work. What is
proved here is exactly the asymmetric pair: continuous no-gos below `5`, `ℚ` witness `> 2`
at `5`.

## The numeric atlas (the `c_k` capping constants and `M₅`)

| `k` | carrier      | cap `c_k = (k/(k−1))·log k` | value    | vs `2` | landed keystone |
|-----|--------------|-----------------------------|----------|--------|-----------------|
| `2` | continuous-`F` | `2·log 2`                 | `≈1.386` | `< 2`  | `no_twin_weight`   |
| `3` | continuous-`F` | `(3/2)·log 3`             | `≈1.648` | `< 2`  | `no_triple_weight` |
| `4` | continuous-`F` | `(4/3)·log 4`             | `≈1.848` | `< 2`  | `no_quad_weight`   |
| `5` | exact `ℚ`      | `M₅ = 191881/95820`       | `≈2.00251` | `> 2` | `M5_cert`          |

The `k = 5` slack is `δ★ = 241/95820 ≈ 2.515·10⁻³` (`191640 < 191881`).

## Companion notes (per A1)

* **`H₁ ≤ 12` at BV-level distribution.** The `k = 5` certificate is what powers the landed
  explicit bounded-gaps result: `Salt.Twelve.gaps_le_twelve_of_hasLevel`
  (`Salt/Twelve/GapsOfLevel.lean`) — `WindowPNT → HasLevel (3999/4000) → ∀ N, ∃ p q > N`
  prime with `|q − p| ≤ 12`. This is the honest gap companion; it is a *pointer*, not
  restated here.
* **The `≤ 6` optimality is OPEN.** Pushing the diameter to `H₁ ≤ 6` would need the
  enlarged-`k`/GEH `M > 4` floor, whose sharp half is Tao's open problem (rung-∞); the DHL
  bridge is unlanded. Recorded as an open note (A1 point 1), not claimed.
-/

namespace Salt.TwinBar

open Function Salt.Twelve

/-! ## The three continuous-weight no-gos (`k = 2, 3, 4`), uniform names -/

/-- **`k = 2` closed.** No continuous weight `F` on the `2`-simplex `R₂` with positive
`L²`-mass crosses the twin gate `2·I₂ F < J₁ F + J₂ F`: the Selberg pair is capped by
`c₂ = 2·log 2 ≈ 1.386 < 2` (`twin_bar`). Continuous-`F` carrier. Re-export of the landed
`no_twin_weight`. -/
theorem maynard_closed_at_two :
    ¬ ∃ F : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry F) R₂ ∧
      0 < I₂ F ∧ 2 * I₂ F < J₁ F + J₂ F :=
  no_twin_weight

/-- **`k = 3` closed.** No continuous weight `F` on the `3`-simplex `R₃` with positive
`L²`-mass crosses the gate `2·I₃ F < J₁₃ F + J₂₃ F + J₃₃ F`: the Selberg triple is capped by
`c₃ = (3/2)·log 3 ≈ 1.648 < 2` (`three_bar`). Continuous-`F` carrier. Re-export of the
landed `no_triple_weight`. -/
theorem maynard_closed_at_three :
    ¬ ∃ F : ℝ → ℝ → ℝ → ℝ, ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃ ∧
      0 < I₃ F ∧ 2 * I₃ F < J₁₃ F + J₂₃ F + J₃₃ F :=
  no_triple_weight

/-- **`k = 4` closed.** No continuous weight `F` on the `4`-simplex `R₄` with positive
`L²`-mass crosses the gate `2·I₄ F < J₁₄ F + J₂₄ F + J₃₄ F + J₄₄ F`: the Selberg quadruple is
capped by `c₄ = (4/3)·log 4 ≈ 1.848 < 2` (`four_bar`). Continuous-`F` carrier. Re-export of
the landed `no_quad_weight`. -/
theorem maynard_closed_at_four :
    ¬ ∃ F : ℝ → ℝ → ℝ → ℝ → ℝ,
      ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄ ∧
      0 < I₄ F ∧ 2 * I₄ F < J₁₄ F + J₂₄ F + J₃₄ F + J₄₄ F :=
  no_quad_weight

/-! ## The `k = 5` achievement (exact `ℚ` certificate), in the `M₅ > 2` form -/

/-- **`k = 5` open.** The exact rational Maynard functional at the explicit degree-3 witness
`F★` exceeds the twin threshold: `M₅ = (Σ_m J⁽ᵐ⁾(F★)) / I(F★) > 2`, with certified value
`191881/95820 ≈ 2.00251` and slack `δ★ = 241/95820 ≈ 2.515·10⁻³`. The exact-`ℚ` carrier
(distinct from the continuous-`F` no-gos above). Derived from the landed product-form
certificate `M5_cert` (`2·I(F★) < Σ_m J⁽ᵐ⁾(F★)`). -/
theorem maynard_open_at_five : 2 < (∑ m : Fin 5, Jcal m Fstar) / Ical Fstar := by
  rw [lt_div_iff₀ (by rw [I_Fstar]; norm_num : (0 : ℚ) < Ical Fstar)]
  exact M5_cert

/-! ## The headline: the least-k theorem -/

/-- **The least-k theorem (sprint headline).** *In the unmodified Maynard–Selberg class,
the least `k` with `M_k > 2` is `5`.* Concretely: for each `k ∈ {2, 3, 4}` NO continuous
weight crosses the twin gate (`maynard_closed_at_{two,three,four}`), while the explicit
rational witness `F★` DOES cross it at `k = 5` (`maynard_open_at_five`, `M₅ ≈ 2.00251 > 2`).

**Carrier asymmetry — READ THIS before quoting (per A1).** The statement is deliberately
NOT a single-object claim. The three no-gos delimit the *continuous-weight* class over the
real simplices (each capped by `c_k = (k/(k−1))·log k < 2`). The `k = 5` achievement is the
*exact rational certificate* in `ℚ` bilinear Dirichlet arithmetic. The two halves live in
different carriers; the single-object bracket that would unify them (a Dirichlet
real-integral bridge, plus the `2 < M₅ ≤ (5/4)·log 5` upper bracket) is **registered debt**,
not part of this theorem. What is certified is exactly the honest asymmetric pair. See the
module docstring for the numeric atlas and the `H₁ ≤ 12` / `≤ 6`-open companions. -/
theorem least_k_theorem :
    (¬ ∃ F : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry F) R₂ ∧
        0 < I₂ F ∧ 2 * I₂ F < J₁ F + J₂ F)
    ∧ (¬ ∃ F : ℝ → ℝ → ℝ → ℝ, ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃ ∧
        0 < I₃ F ∧ 2 * I₃ F < J₁₃ F + J₂₃ F + J₃₃ F)
    ∧ (¬ ∃ F : ℝ → ℝ → ℝ → ℝ → ℝ,
        ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄ ∧
        0 < I₄ F ∧ 2 * I₄ F < J₁₄ F + J₂₄ F + J₃₄ F + J₄₄ F)
    ∧ 2 < (∑ m : Fin 5, Jcal m Fstar) / Ical Fstar :=
  ⟨maynard_closed_at_two, maynard_closed_at_three, maynard_closed_at_four,
    maynard_open_at_five⟩

end Salt.TwinBar
