/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.SignChain

/-!
# The neutrality rate against the generic sign-function chain (WALL-3, wave 3, node SignRate)

The exchange-rate wall's rate node.  Against the generic transfer chain of
`Salt.HB.SignChain` we record two objects:

* `EngineBound` — the frozen three-row engine budget: a `P`-independent floor
  `Cmain·x/z₀`, the pretense row `Cmain·(x/log x)·exp(5·z₀)·P`, and the junk row
  `Cmain·exp(2·z₀)·(x/z^{1/8} + x^{9/10})·L³`, with the scales `z0`/`Lwin` as landed
  in `Salt.HB.L2cCore`.
* `neutrality_rate` — the budget-conditional rate: given a budget hypothesis on the
  exact overshoot sum, `S⁽²⁾_f − S⁽¹⁾` sits in `[0, EngineBound]` on the window.

**Amendment J2 (content honesty).**  The *unconditional* content of `neutrality_rate`
is exactly `S1_le_S2Gen` — the left conjunct `0 ≤ S⁽²⁾_f − S⁽¹⁾`.  The *rate* content
(the upper bound) is `hbudget`-conditional, pending the character master
`hb_l2c_master` and its generic mirror.  No `o(1)`/staircase/cone claim is a Lean
statement here (that stays W4 prose, W5 law).

**Amendment J1 (discharge target).**  The absolute discharge shape `hb_l2c_masterGen`
is **comment-frozen** at the foot of this file as a docstring block — never a
declaration, never a `sorry` — and carries no proof attempt (D-shaped; scope diff #2).

Single-writer file; it touches no landed file and is not yet in the `Salt.HB.All`
manifest.  It builds standalone via `Salt.HB.SignChain`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace Salt.HB

/-- Frozen engine-bound shape (l2c-freeze.md:27-33): `Aexp = 5` pinned, junk in rpow form,
    scales `z0`/`Lwin` landed at LC:54-57.  NOT a function of `P` alone: `P`-independent floor. -/
noncomputable def EngineBound (Cmain : ℝ) (z x : ℕ) (P : ℝ) : ℝ :=
  Cmain * ((x : ℝ) / z0 z x)
    + Cmain * ((x : ℝ) / Real.log x) * Real.exp (5 * z0 z x) * P
    + Cmain * Real.exp (2 * z0 z x)
        * ((x : ℝ) / (z : ℝ) ^ ((1 : ℝ) / 8) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3

/-- **W3 RATIFIED FORM — the neutrality rate**, budget-conditional (provable now given W1).

    Amendment J2: the *unconditional* content is exactly the left conjunct
    `0 ≤ S⁽²⁾_f − S⁽¹⁾`, i.e. `S1_le_S2Gen`; the *rate* (upper) bound is `hbudget`-conditional,
    pending the character master (`hb_l2c_masterGen`, comment-frozen below). -/
theorem neutrality_rate (f : ℕ → ℝ) (hf : IsSignFunction f) (z x : ℕ) (Cmain : ℝ)
    (hbudget : ∑ n ∈ l2cWindowGen f z x, overshootExactGen f n
        ≤ EngineBound Cmain z x (PretenseSumGen f (2 * x + 2))) :
    0 ≤ S2Gen f (l2cWindowGen f z x) - S1 (l2cWindowGen f z x) ∧
      S2Gen f (l2cWindowGen f z x) - S1 (l2cWindowGen f z x)
        ≤ EngineBound Cmain z x (PretenseSumGen f (2 * x + 2)) := by
  refine ⟨sub_nonneg.mpr (S1_le_S2Gen hf _), ?_⟩
  rw [S2Gen_sub_S1_eq]
  exact hbudget

/-
W3 DISCHARGE TARGET — FROZEN TARGET, DO NOT PROVE (Amendment J1, comment-frozen; NOT a
Lean declaration, NOT a `sorry`).  D-shaped today (scope diff #2): the absolute `∃ Cmain`
discharge shape, frozen against the as-yet-unlanded character master `hb_l2c_master`
(no `L2cMaster.lean`, no `All.lean` L2c line).  A mandatory catch-#224 `EngineBound`
freeze-to-freeze re-diff is required before any attempt.  Authoritative text =
DES-W §W3 verbatim; Amendment J3: the `∃ Cmain` binder sits OUTSIDE `∀ f ∀ z ∀ x`
(moving it inside the context is `Cmain`-monotonically vacuous = forbidden).

theorem hb_l2c_masterGen :
    ∃ Cmain : ℝ, 0 < Cmain ∧
      ∀ (f : ℕ → ℝ), IsSignFunction f → ∀ z x : ℕ,
        100 ^ 16 ≤ z → Lwin x ^ 8 ≤ (z : ℝ) → (z : ℝ) ^ 3 ≤ (x : ℝ) →
        S2Gen f (l2cWindowGen f z x) - S1 (l2cWindowGen f z x) ≤
          EngineBound Cmain z x (PretenseSumGen f (2 * x + 2))
-/

end Salt.HB
