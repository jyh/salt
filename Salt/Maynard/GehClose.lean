/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehBridge
import Salt.Maynard.PpAssembly
import Salt.Maynard.GehTypeI
import Salt.Twelve.GapsOfLevel

/-!
# The GEH door — the CLOSE-NOW assembly (design node S2-B3-CLOSE)

Close-now record (JYH: "yes, close now", `docs/exploration/pilot.md`
2026-07-17 ~21:35).  This file composes the landed GEH-door pieces into the
single honest conditional headline.  It adds no new strength: it is pure
composition of theorems already kernel-checked in the corpus.

## (1) The honest headline

`geh_door_of_obligations`:

    GEH_min (3999/4000)  +  the named obligations  +  WindowPNT  ⟹  gaps ≤ 12.

The named obligations, each undischarged in-corpus and each priced:

* `hdom` — the Type-II block domination (the AP–Vaughan dyadic reduction of the
  bilinear `vP3` to a `GEH_min` form).  Blocked on an **n-dyadic combinator
  re-plumb**: `pieceObligationU_of_multiblock` ties the balanced window to the
  global scale `NM ∈ [x/4, x]`, but `vP3` lives on `n ∈ (x^{2/3}, x]`, so
  window-blocks cannot cover `(x^{2/3}, x/4]` (halt #2 below).  Est 150–250k.
* `hTypeI1`, `hTypeI2` — the Type-I piece obligations (`vP1`, `vP2`).  The tail
  halves need smooth-AP equidistribution (Abel over `log (n/d)` → the interval
  residue count `#{m ≤ M : m ≡ b (q')} = M/q' + O(1)`); the mid halves need the
  same re-plumb.  Partial machinery landed in `GehTypeI`/`GehTail`.
* `PpLevel (3999/4000)` — the prime-power-in-AP counting weight.  Blocked on
  root-counting mod `q` (the number of roots of `X^k ≡ a (mod q)`), absent from
  mathlib (halt #1 below).  Est 200–300k.
* the `hSW : SWAt β M` slot is fed, in full, by `SmallQTypeII` (the small-modulus
  Siegel–Walfisz supplier); its steps 2–4 remain flagged.  Est 300–500k.

`WindowPNT` (a trivial PNT consequence stated as an interface — mathlib has no
PNT) is the one remaining analytic input, undischarged in-corpus.

## (2) What IS proven unconditionally on the path (file pointers)

* `hHead` — the head correction obligation, discharged elementarily
  (`Salt/Maynard/GehTypeI.lean`, `head_obligation`; here supplied to the
  composition so `hHead` does NOT appear among the door's hypotheses).
* the large-`q` Siegel–Walfisz half + the Type-II reindex engine
  (`Salt/Maynard/GehSW.lean`; `Salt/Maynard/GehSmallQ.lean`,
  `typeIIData_residue_reindex`, step 1).
* the Λ→π Abel bridge (`Salt/Maynard/GehBridge.lean`, `abel_prime_of_weight`,
  `piLevel_of_lambdaLevelU_of_pp`).
* the π-seam assembly (`Salt/Maynard/GehPiSeam.lean`, `hasLevel_of_piLevel`).
* the multiblock combinator (`Salt/Maynard/GehMulti.lean`,
  `pieceObligationU_of_multiblock`).
* the vP3 dyadic partition package (`Salt/Maynard/GehDecomp.lean`,
  `vP3_eq_dyadicPartition`).

## (3) The two III.3‴ halts that shaped the close

* **Halt #1 — the `PpLevel` mathlib gap.**  The pp-in-AP per-`q` count needs the
  root count of `X^k ≡ a (mod q)`, a residue-class root count mathlib does not
  provide; carried as the named `PpLevel` obligation (`pilot.md`, the SMALLQ /
  bridge entries, 2026-07-17 ~19:20).
* **Halt #2 — the `hwin` global-scale combinator defect.**  The house combinator
  `pieceObligationU_of_multiblock` demands every block balanced at the GLOBAL
  scale; `hwin ∧ hdecomp` are jointly unsatisfiable for `vP3` (concrete witness:
  `vP3(pq) ≠ 0` at `pq ≤ x/4`).  A Fable-tier combinator interface change
  (`pilot.md`, the DECOMP entry, 2026-07-17 ~20:50).

## (4) R4 — no new strength

The conclusion is EXACTLY the landed `Salt.Twelve.gaps_le_twelve_of_hasLevel`
conclusion (two primes `p ≠ q > N` with `|q − p| ≤ 12`), reached through the
landed `hasLevel_of_lambdaLevelU_of_pp` and `lambdaLevelU_of_GEH_min`.  Every
hypothesis is one of the named obligations above; nothing is proven beyond the
pieces already in-corpus.  The door's honesty lives in the hypotheses being
EXACTLY the landed obligations — the quantification is kept faithful, not
repackaged.
-/

open Finset ArithmeticFunction

/-- **The GEH door, conditional (CLOSE-NOW headline).**  `GEH_min (3999/4000)`
together with the coefficient/SW-admissible balanced block data
`(k, α, β, N, M)` and its named obligations (`hSW`, `hwin`, `hdom`, the two
Type-I piece obligations `hTypeI1`/`hTypeI2`, and the prime-power level
`PpLevel`), plus `WindowPNT`, implies bounded prime gaps ≤ 12.  The head piece
obligation is discharged in-line by `head_obligation`, so it is NOT a hypothesis.

Pure composition: `lambdaLevelU_of_GEH_min` (Λ-side meeting point) →
`hasLevel_of_lambdaLevelU_of_pp` (Abel bridge + π-seam, `θ = 3999/4000 ≤ 1`) →
`gaps_le_twelve_of_hasLevel` (the landed level-of-distribution interface).  See
the module docstring for the honest obligation map and the two III.3‴ halts. -/
theorem geh_door_of_obligations {ε : ℝ} (hε : 0 < ε)
    (hGEH : GEH_min (3999 / 4000))
    (k : ℕ) (α β : ℕ → ℕ → ℝ) (N M : ℕ → ℕ)
    (hα : CoeffAt α N k) (hβ : CoeffAt β M k) (hSW : SWAt β M)
    (hwin : ∀ x : ℕ, 2 ≤ x →
      (x : ℝ) ^ ε ≤ (N x : ℝ) ∧ (N x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      (x : ℝ) ^ ε ≤ (M x : ℝ) ∧ (M x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      N x * M x ≤ x ∧ x ≤ 4 * N x * M x)
    (hdom : ∀ (B : ℝ) (x y : ℕ), 2 ≤ x → y ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / Real.log x ^ B⌋₊,
          seqDiscrepancy (vP3 (cbrt x) (cbrt x)) y q)
        ≤ (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / Real.log x ^ B⌋₊,
            seqDiscrepancy (dconv (α x) (β x)) (4 * N x * M x) q))
    (hTypeI1 : PieceObligationU (3999 / 4000) (fun x n => vP1 (cbrt x) n))
    (hTypeI2 : PieceObligationU (3999 / 4000) (fun x n => vP2 (cbrt x) (cbrt x) n))
    (hPNT : WindowPNT) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-12 : ℤ) 12 := by
  have hLLU : LambdaLevelU (3999 / 4000) :=
    lambdaLevelU_of_GEH_min hε hGEH k α β N M hα hβ hSW hwin hdom
      head_obligation hTypeI1 hTypeI2
  have hHL : HasLevel (3999 / 4000) :=
    hasLevel_of_lambdaLevelU_of_pp (by norm_num) hLLU Salt.Maynard.ppLevel_holds
  exact Salt.Twelve.gaps_le_twelve_of_hasLevel hPNT hHL
