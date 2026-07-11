/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Tactic.AuditAxioms

/-!
# `eventually_budget` — the `∀ᶠ` threshold-stack assembler (tactic ledger T2)

Analytic assemblies in this project repeatedly discharge a *budget* goal of the
shape

```
∀ᶠ N in atTop, (piece₁ N + piece₂ N + … + pieceₙ N)  </≤  margin
```

from a stack of per-piece eventual bounds `hᵢ : ∀ᶠ N in atTop, pieceᵢ N ≤ εᵢ`
plus one numeral tail `Σᵢ εᵢ </≤ margin`.  Doing this by hand is ~100+ lines of
`max`-threshold plumbing per assembly (`GapsUncond.winSlackM_ev`'s "7 vanishing
pieces", `WinFrontierDischarge`'s W5-7 threshold stack, `WindowPNTDischarge`'s
extraction).  This module packages the pattern.

## Layer 1 — the combinator library (`Salt.Tactic` namespace)

* `eventually_finset_sum_le` / `eventually_sum_lt_of_pieces` — the
  `Finset`-indexed versions, for budgets that are literally a `∑ i ∈ s, f i N`
  (e.g. the `∑ m : Fin 5` moment sums).  Built on mathlib's
  `Filter.eventually_all_finset` + `Finset.sum_le_sum`.
* `eventually_add_le` / `eventually_lt_of_eventually_le_const` /
  `eventually_le_of_eventually_le_const` — the binary `+`-tree building blocks
  the macro folds over.
* `eventually_le_of_tendsto_zero` — a thin `Tendsto f atTop (𝓝 0) → ∀ᶠ, |f| ≤ ε`
  convenience (mathlib has the pieces `Filter.Tendsto.abs` +
  `Filter.Tendsto.eventually_le_const` but not the composite).

### Re-exports of existing mathlib lemmas (aliases, not duplicates)

* `eventually_ge_of_tendsto_gt` **is** `Filter.Tendsto.eventually_const_le`
  (`hv : b < c`, `Tendsto f _ (𝓝 c)` ⊢ `∀ᶠ, b ≤ f`).  Kept as a named,
  discoverable alias matching the consumers' vocabulary.
* `exists_forall_ge_of_eventually` **is** `Filter.eventually_atTop.mp` — the
  `∀ᶠ ↦ ∃ N₀, ∀ N ≥ N₀` beta-reducer.

## Layer 2 — the `eventually_budget` tactic

```
eventually_budget [h₁, h₂, …, hₙ]
```

for a goal `∀ᶠ N in atTop, (piece₁ N + … + pieceₙ N) </≤ margin`.  It left-folds
the hypotheses with `eventually_add_le` and discharges the eventual layer,
leaving exactly the residual numeral goal `((ε₁ + ε₂) + …) </≤ margin` for
`norm_num` (or the caller).  Handles both `<` and `≤` goals (it tries the strict
tail first, then the non-strict).

**Contract (positional):** list the hypotheses left-to-right in the same order
the pieces appear in the goal's `+`-tree.  Lean left-associates `a + b + c`, so
the fold `((h₁ ⊕ h₂) ⊕ h₃)` lines up with the goal `(p₁ + p₂) + p₃`
automatically.  Each `hᵢ`'s piece must be *syntactically* the goal's piece
(defeq that `refine` can see) — in practice the `hᵢ` are produced *from* the goal
subterms, so this holds; a stray cast mismatch (`↑1` vs `1`) will make the
`refine` miss.

### 3-line usage note for the V3.1 executor

1. Budget is a flat `+`-tree → `eventually_budget [h₁,…,hₙ]; norm_num` (pieces in
   goal order); budget is a `∑ i ∈ s, …` → `exact eventually_sum_lt_of_pieces s
   hpieces hnum`.
2. Get each `hᵢ` from a limit with `eventually_le_of_tendsto_zero h hε` (⇒ `|·| ≤
   ε`) or `eventually_ge_of_tendsto_gt h hlt` (⇒ `b ≤ ·`); need an explicit
   `∃ N₀, ∀ N ≥ N₀` instead → `exists_forall_ge_of_eventually`.
3. The macro leaves the numeral goal `Σεᵢ </≤ margin`; close it yourself
   (`norm_num`/`linarith`) — it is deliberately not auto-discharged.
-/

open Filter Topology

namespace Salt.Tactic

/-! ## Layer 1 — `Finset`-indexed combinators -/

/-- **Finset-indexed eventual-sum combinator.**  If each summand is eventually
`≤ εᵢ`, the sum is eventually `≤ Σᵢ εᵢ`.  (`Filter.eventually_all_finset` bundles
the finitely many thresholds; `Finset.sum_le_sum` does the pointwise step.) -/
theorem eventually_finset_sum_le {ι} (s : Finset ι) {f : ι → ℕ → ℝ} {ε : ι → ℝ}
    (h : ∀ i ∈ s, ∀ᶠ N in atTop, f i N ≤ ε i) :
    ∀ᶠ N in atTop, ∑ i ∈ s, f i N ≤ ∑ i ∈ s, ε i := by
  filter_upwards [(Filter.eventually_all_finset s).mpr h] with N hN
  exact Finset.sum_le_sum hN

/-- **Finset budget closer.**  Compose `eventually_finset_sum_le` with a strict
numeral tail `Σᵢ εᵢ < margin` to land the eventual strict budget bound. -/
theorem eventually_sum_lt_of_pieces {ι} (s : Finset ι) {f : ι → ℕ → ℝ} {ε : ι → ℝ}
    {margin : ℝ} (h : ∀ i ∈ s, ∀ᶠ N in atTop, f i N ≤ ε i)
    (hlt : ∑ i ∈ s, ε i < margin) :
    ∀ᶠ N in atTop, ∑ i ∈ s, f i N < margin := by
  filter_upwards [eventually_finset_sum_le s h] with N hN
  exact lt_of_le_of_lt hN hlt

/-! ## Layer 1 — `Tendsto`-to-eventual extractors -/

/-- **From a null limit to an eventual absolute bound.**  If `f → 0` then
eventually `|f N| ≤ ε` for any `ε > 0`.  Thin composite of `Filter.Tendsto.abs`
(giving `|f| → |0| = 0`) and `Filter.Tendsto.eventually_le_const`. -/
theorem eventually_le_of_tendsto_zero {f : ℕ → ℝ}
    (h : Tendsto f atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, |f N| ≤ ε := by
  have habs : Tendsto (fun N => |f N|) atTop (𝓝 0) := by simpa using h.abs
  exact habs.eventually_le_const hε

/-- **From a limit above `b` to an eventual lower bound.**  If `f → c` and
`b < c` then eventually `b ≤ f N`.

This is a discoverable alias of mathlib's `Filter.Tendsto.eventually_const_le`
(prefer that name when writing new mathlib-facing code). -/
theorem eventually_ge_of_tendsto_gt {f : ℕ → ℝ} {c b : ℝ}
    (h : Tendsto f atTop (𝓝 c)) (hb : b < c) :
    ∀ᶠ N in atTop, b ≤ f N :=
  h.eventually_const_le hb

/-- **Threshold beta-reducer.**  Turn an `∀ᶠ N in atTop` fact into an explicit
`∃ N₀, ∀ N ≥ N₀`.  Alias of `Filter.eventually_atTop.mp`. -/
theorem exists_forall_ge_of_eventually {p : ℕ → Prop}
    (h : ∀ᶠ N in atTop, p N) : ∃ N₀, ∀ N, N₀ ≤ N → p N :=
  Filter.eventually_atTop.mp h

/-! ## Layer 2 — `+`-tree building blocks -/

/-- Pointwise-add two eventual `≤` facts.  The macro left-folds this over the
supplied hypothesis list. -/
theorem eventually_add_le {f g : ℕ → ℝ} {a b : ℝ}
    (hf : ∀ᶠ N in atTop, f N ≤ a) (hg : ∀ᶠ N in atTop, g N ≤ b) :
    ∀ᶠ N in atTop, f N + g N ≤ a + b := by
  filter_upwards [hf, hg] with N hfN hgN; exact add_le_add hfN hgN

/-- Strict tail: an eventual `≤ s` fact plus `s < m` gives an eventual `< m`. -/
theorem eventually_lt_of_eventually_le_const {g : ℕ → ℝ} {s m : ℝ}
    (h : ∀ᶠ N in atTop, g N ≤ s) (hlt : s < m) :
    ∀ᶠ N in atTop, g N < m := by
  filter_upwards [h] with N hN; exact lt_of_le_of_lt hN hlt

/-- Non-strict tail: an eventual `≤ s` fact plus `s ≤ m` gives an eventual `≤ m`. -/
theorem eventually_le_of_eventually_le_const {g : ℕ → ℝ} {s m : ℝ}
    (h : ∀ᶠ N in atTop, g N ≤ s) (hle : s ≤ m) :
    ∀ᶠ N in atTop, g N ≤ m := by
  filter_upwards [h] with N hN; exact le_trans hN hle

/-! ## Layer 2 — the macro -/

open Lean in
/-- Left-fold a nonempty array of eventual `≤` facts with `eventually_add_le`,
producing a single `∀ᶠ N, (p₁ N + … + pₖ N) ≤ (ε₁ + … + εₖ)`. -/
private def foldEvAdd (hs : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  let mut acc := hs[0]!
  for h in hs[1:] do
    acc ← `(Salt.Tactic.eventually_add_le $acc $h)
  return acc

/-- `eventually_budget [h₁, …, hₙ]` — discharge a goal
`∀ᶠ N in atTop, (p₁ N + … + pₙ N) </≤ margin` from positional per-piece bounds
`hᵢ : ∀ᶠ N in atTop, pᵢ N ≤ εᵢ`, leaving the numeral residual
`(ε₁ + … + εₙ) </≤ margin`.  See the module docstring for the contract. -/
macro "eventually_budget" "[" hs:term,* "]" : tactic => do
  let elems := hs.getElems
  if elems.isEmpty then
    Lean.Macro.throwError "eventually_budget: need at least one hypothesis"
  let fold ← foldEvAdd elems
  `(tactic|
    first
    | refine Salt.Tactic.eventually_lt_of_eventually_le_const $fold ?_
    | refine Salt.Tactic.eventually_le_of_eventually_le_const $fold ?_)

end Salt.Tactic

/-! ## Self-tests (kernel-checked at build time)

A shared eventual per-piece bound, then the macro on a 3-piece `+`-tree (strict),
a single piece, a `≤`-goal (exercising the non-strict tail), and the `Finset`
combinator.  The `#audit_axioms` block dogfoods T5 and pins every landed lemma to
the whitelisted axiom set. -/

section Tests
open Filter Topology Salt.Tactic

/-- `1/(N+c) ≤ 1/100` eventually, for `c ≥ 0`. -/
private theorem toy_piece (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ N : ℕ in atTop, (1:ℝ)/((N:ℝ)+c) ≤ 1/100 := by
  filter_upwards [eventually_ge_atTop 100] with N hN
  have hNr : (100:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

-- macro: 3-piece `+`-tree, strict goal
example : ∀ᶠ N : ℕ in atTop,
    (1:ℝ)/((N:ℝ)+1) + 1/((N:ℝ)+2) + 1/((N:ℝ)+3) < 1/10 := by
  eventually_budget [toy_piece 1 (by norm_num), toy_piece 2 (by norm_num),
    toy_piece 3 (by norm_num)]
  norm_num

-- macro: single piece
example : ∀ᶠ N : ℕ in atTop, (1:ℝ)/((N:ℝ)+1) < 1/10 := by
  eventually_budget [toy_piece 1 (by norm_num)]
  norm_num

-- macro: `≤`-goal exercises the non-strict tail
example : ∀ᶠ N : ℕ in atTop,
    (1:ℝ)/((N:ℝ)+1) + 1/((N:ℝ)+2) ≤ 1/10 := by
  eventually_budget [toy_piece 1 (by norm_num), toy_piece 2 (by norm_num)]
  norm_num

-- Finset combinator (`eventually_sum_lt_of_pieces`)
example : ∀ᶠ N : ℕ in atTop,
    ∑ i : Fin 3, (1:ℝ)/((N:ℝ) + (i:ℕ) + 1) < 1/10 := by
  refine eventually_sum_lt_of_pieces Finset.univ (ε := fun _ => 1/100)
    (fun i _ => ?_) (by norm_num [Fin.sum_univ_three])
  filter_upwards [eventually_ge_atTop 100] with N hN
  have hNr : (100:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hinn : (0:ℝ) ≤ (i:ℕ) := by positivity
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

-- extractor smoke test
example {f : ℕ → ℝ} (h : Tendsto f atTop (𝓝 5)) :
    ∀ᶠ N in atTop, (3:ℝ) ≤ f N :=
  eventually_ge_of_tendsto_gt h (by norm_num)

#audit_axioms Salt.Tactic.eventually_finset_sum_le Salt.Tactic.eventually_sum_lt_of_pieces
  Salt.Tactic.eventually_le_of_tendsto_zero Salt.Tactic.eventually_ge_of_tendsto_gt
  Salt.Tactic.exists_forall_ge_of_eventually Salt.Tactic.eventually_add_le
  Salt.Tactic.eventually_lt_of_eventually_le_const Salt.Tactic.eventually_le_of_eventually_le_const

end Tests
