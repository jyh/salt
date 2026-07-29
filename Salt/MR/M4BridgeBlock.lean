/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4BridgePhase
import Salt.MR.M4BridgeCover

/-!
# ⟦F3⟧ — THE BLOCKED DRIFT (`M4BridgeBlock`)

Wave ③ of the second-road freeze v2 (`docs/exploration/second-road-freeze-0729.md`),
verified by ⟦ARC-SCOPE⟧'s Q2 (flags, 2026-07-29 ~03:00).

## What this file removes

`M4BridgePhase`'s landed drift line prices the phase `e(αn)` over the **whole** door window:

```
‖absWindowSum a H n (β+θ)‖ ≤ (1 + 2π·arcDen 12 H / q) · subWindowSup a H n β
```

(`norm_absWindowSum_le_drift`, `:291`).  The factor `1 + 2π·arcDen/q` is the *flattening of
the phase across a length-`H` window*, and at `q = 1` it is `(log H)^{12}`-scale; squared into
the socket it is the `F3` factor of the four-factor wall (⟦DRIFT-SCOPE⟧: `F3 = (2π·arcDen/q)²`,
`M4BridgePhase:403`).

Blocked at the drift's **own length** `ℓ ≈ qH/arcDen` the per-block drift is `≤ 1 + 2π` — an
absolute constant, no `arcDen`, no `q` — and the block count `N = ⌈H/ℓ⌉` enters only through
Cauchy–Schwarz over the blocks, as `N`.  Composed with a per-block supply normalised at `ℓ²`
the assembled price is

```
(1 + 2π)² · N · (Bblk · N · ℓ²)  =  (1 + 2π)² · Bblk · (N·ℓ)²  ≤  4·(1 + 2π)² · Bblk · H²
```

— `N²ℓ² ≍ H²`, so the blocking is **loss-free up to the absolute factor `4`** (exactly `H²`
when `ℓ ∣ H`; `numBlocks H ℓ · ℓ ≤ H + ℓ ≤ 2H` is the honest bookkeeping, `numBlocks_mul_le`).

⟦F3 IS WORTHLESS STANDALONE⟧ (D1-SCOPE, now law): the drift price is an identity over the
legal `q`-range, so removing `F3` buys nothing until `F2`'s two `q`'s die as well.  Nothing
here claims otherwise — this file supplies one factor of a composition wave ④ owns.

## ⟦THE ③×④ INTERFACE — the socket's contract⟧

The deliverable wave ④ consumes is `M4SievedDoorSqBlk R M ℓ Bblk`:

```
∫ (∑_{m < N} (subWindowSup a ℓ (n + m·ℓ) (b/q))²) dμ  ≤  Bblk H · N · ℓ²
      where  N := numBlocks H (ℓ H q) = H / ℓ + 1  (≥ ⌈H/ℓ⌉),  a := doorSievedCoeff M
```

read under the admissibility binders `1 ≤ ℓ H q`, `ℓ H q ≤ H` and
`H ≤ arcDen 12 H · ℓ H q`.  The socket theorem `m4_sievedDoorSq_of_blk` turns it into
`M4Close.M4SievedDoorSq R M Braw` at

```
4·(1 + 2π)² · Bblk H  ≤  Braw H
```

**with no `q` and no `arcDen` anywhere in the price** — the `q` lives ONLY in the legal range
of `ℓ`, through the fourth (theorem-level, not socket-level) obligation

```
⟦THE DRIFT BINDER⟧   arcDen 12 H · ℓ H q  ≤  q · H .
```

⟦THE `q`-DEPENDENCE OF `ℓ` IS FORCED — a co-design finding⟧  The freeze brief listed the two
socket binders as `H ≤ arcDen 12 H · ℓ` and `ℓ ≤ H`, with the drift binder
`ℓ ≤ qH/arcDen` from step 1.  A `q`-**uniform** `ℓ` cannot satisfy both: `NearRatTight` may
hand out `q = 1`, where the drift binder reads `arcDen·ℓ ≤ H` and, against
`H ≤ arcDen·ℓ`, forces `arcDen 12 H · ℓ = H` exactly — no natural number does that for
generic `H`.  So `ℓ : ℕ → ℕ → ℕ` takes **both** `H` and `q`, and the intended witness is
`ℓ H q ≈ q·H/arcDen 12 H`, at which both binders hold with room `q`.  (④ owns the witness;
the four `hℓ*` hypotheses of `m4_sievedDoorSq_of_blk` are exactly its obligation, and none of
them is used anywhere else — the socket itself never sees `ℓ`'s construction.)

⟦K-FREEDOM⟧  The sup over sub-window lengths stays *inside* `subWindowSup` at cap `ℓ`; no
statement in this file carries a `K`, and the block count `numBlocks H ℓ` depends on `H` and
`ℓ` alone.  The partial last block is absorbed by the block-sup — `subWindowSup a ℓ base β`
dominates every length `≤ ℓ` (`subWindowSup_mono_length`), so `M4BridgeIntegral`'s overhang
ledger is not needed and is not cited.

## Contents

* §1 THE BLOCK GEOMETRY — `numBlocks`, `blockCut`, the chunking identity `sum_Ioc_chunk`.
* §2 THE BLOCKED DRIFT — `abs_mul_window_le_of_arcDen_block` (the block-length twin of
  `M4Abel.abs_mul_window_le_of_arcDen`), `norm_absWindowSum_le_drift_blocked` and its squared
  Cauchy–Schwarz form.
* §3 THE BLOCKED SOCKET — `blockSupSq`, `M4SievedDoorSqBlk`, `m4_sievedDoorSq_of_blk`, and the
  inhabitation witness.
* §4 THE COVERING SIDE — `M4BlockMeanSqBlk` and `m4_cover_assembly_blk`, at
  `M4BridgeCover.integral_door_cover_le_clean`'s free nonnegative `g`.
* §5 THE SHIFTED-BASE BRIDGE — the blocked bases `n + m·ℓ` inside the ladder block's own
  doubled interval (④'s χ-side reads the shift family there).

## Conventions

* One log scale: `arcDen 12 H` only, never evaluated (`arcDen_nonneg` is the only fact used).
* The drift constant is symbolic: `(1 + 2π)²`, never a numeral.
* Nothing landed is restated: `M4Abel`'s drift kill, `M4BridgePhase`'s `subWindowSup` family
  and `M4BridgeCover`'s cover assembly are all consumed verbatim.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.ExpSum
open Salt.Entropy.Chowla

/-! ## §1 — THE BLOCK GEOMETRY

A window of length `H` is cut into blocks of length `ℓ`, the last one short.  The cut points
are `n + min H (m·ℓ)`, so the family is monotone, starts at `n` and stops at `n + H` — the
truncation is what makes the last block partial rather than overhanging. -/

/-- **THE BLOCK COUNT.**  `H / ℓ + 1` — one more than the number of *full* blocks, hence at
least `⌈H/ℓ⌉`, and never zero.  The `+1` (rather than the exact ceiling) is deliberate: it
makes both directions of the bookkeeping one-line, and it costs only the empty last block when
`ℓ ∣ H`. -/
def numBlocks (H ℓ : ℕ) : ℕ := H / ℓ + 1

/-- The blocks cover the window: `H ≤ N·ℓ`. -/
theorem le_numBlocks_mul (H : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) : H ≤ numBlocks H ℓ * ℓ := by
  have hm : H % ℓ < ℓ := Nat.mod_lt _ hℓ
  calc H = H / ℓ * ℓ + H % ℓ := (Nat.div_add_mod' H ℓ).symm
    _ ≤ H / ℓ * ℓ + ℓ := Nat.add_le_add_left hm.le _
    _ = numBlocks H ℓ * ℓ := by rw [numBlocks, Nat.add_mul, one_mul]

/-- The blocks do not overshoot by more than one: `N·ℓ ≤ H + ℓ`.  With `ℓ ≤ H` this is the
`N·ℓ ≤ 2H` that makes the blocking loss-free up to the absolute factor `4`. -/
theorem numBlocks_mul_le (H ℓ : ℕ) : numBlocks H ℓ * ℓ ≤ H + ℓ := by
  have h : H / ℓ * ℓ ≤ H := Nat.div_mul_le_self H ℓ
  calc numBlocks H ℓ * ℓ = H / ℓ * ℓ + ℓ := by rw [numBlocks, Nat.add_mul, one_mul]
    _ ≤ H + ℓ := Nat.add_le_add_right h ℓ

/-- Every block base stays inside the window: `m < N` gives `m·ℓ ≤ H`.  This is what makes the
cut points `n + min H (m·ℓ)` read as the plain shifts `n + m·ℓ` (`blockCut_eq_of_lt`). -/
theorem mul_le_of_lt_numBlocks {H ℓ m : ℕ} (hm : m < numBlocks H ℓ) : m * ℓ ≤ H := by
  have h1 : m ≤ H / ℓ := Nat.lt_succ_iff.mp hm
  calc m * ℓ ≤ H / ℓ * ℓ := Nat.mul_le_mul_right ℓ h1
    _ ≤ H := Nat.div_mul_le_self H ℓ

/-- **THE CUT POINTS.**  `blockCut n H ℓ m = n + min H (m·ℓ)`: the `m`-th boundary of the
window `(n, n+H]`, truncated at the top so that the family is constant at `n + H` beyond the
last block. -/
def blockCut (n H ℓ m : ℕ) : ℕ := n + min H (m * ℓ)

@[simp] theorem blockCut_zero (n H ℓ : ℕ) : blockCut n H ℓ 0 = n := by simp [blockCut]

/-- Below the block count the truncation is inactive: the cut point is the plain shift. -/
theorem blockCut_eq_of_lt {n H ℓ m : ℕ} (hm : m < numBlocks H ℓ) :
    blockCut n H ℓ m = n + m * ℓ := by
  have h := mul_le_of_lt_numBlocks hm
  simp [blockCut, Nat.min_eq_right h]

/-- At the block count the family has reached the top of the window. -/
theorem blockCut_numBlocks {H ℓ : ℕ} (hℓ : 0 < ℓ) (n : ℕ) :
    blockCut n H ℓ (numBlocks H ℓ) = n + H := by
  have h := le_numBlocks_mul H hℓ
  simp [blockCut, Nat.min_eq_left h]

theorem blockCut_mono (n H ℓ : ℕ) : Monotone (blockCut n H ℓ) := by
  intro i j hij
  have h : i * ℓ ≤ j * ℓ := Nat.mul_le_mul_right ℓ hij
  simp only [blockCut]
  omega

/-- Each block is at most `ℓ` long — including the last, truncated one. -/
theorem blockCut_succ_sub_le (n H ℓ m : ℕ) :
    blockCut n H ℓ (m + 1) - blockCut n H ℓ m ≤ ℓ := by
  have h : (m + 1) * ℓ = m * ℓ + ℓ := by ring
  simp only [blockCut]
  omega

/-- Consecutive `Ioc`-sums glue.  (`Finset.sum_Ioc_consecutive` is not in mathlib; the union
form `Finset.Ioc_union_Ioc_eq_Ioc` plus disjointness is.) -/
private theorem sum_Ioc_consec {N : Type*} [AddCommMonoid N] (f : ℕ → N) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    ((∑ i ∈ Finset.Ioc a b, f i) + ∑ i ∈ Finset.Ioc b c, f i) = ∑ i ∈ Finset.Ioc a c, f i := by
  rw [← Finset.sum_union, Finset.Ioc_union_Ioc_eq_Ioc hab hbc]
  refine Finset.disjoint_left.mpr ?_
  intro x hx hx'
  simp only [Finset.mem_Ioc] at hx hx'
  omega

/-- **THE CHUNKING IDENTITY.**  A sum over `Ioc (c 0) (c N)` is the sum of its `N` consecutive
blocks, for any monotone family of cut points.  Stated at a general `c` so that the truncation
convention lives only in `blockCut`. -/
theorem sum_Ioc_chunk {N : Type*} [AddCommMonoid N] (f : ℕ → N) {c : ℕ → ℕ}
    (hc : Monotone c) (K : ℕ) :
    ∑ m ∈ Finset.range K, ∑ i ∈ Finset.Ioc (c m) (c (m + 1)), f i
      = ∑ i ∈ Finset.Ioc (c 0) (c K), f i := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih,
        sum_Ioc_consec f (hc (Nat.zero_le K)) (hc (Nat.le_succ K))]

/-! ## §2 — THE BLOCKED DRIFT

`M4Abel`'s drift kill, applied on each block instead of once on the window.  The only new
arithmetic is the block-length twin of `M4Abel.abs_mul_window_le_of_arcDen`. -/

/-- **THE SUP ABSORBS THE PARTIAL BLOCK.**  `subWindowSup` is monotone in its cap, so the
block object at cap `ℓ` already dominates every shorter block — in particular the truncated
last one.  ⟦K-FREEDOM⟧ this is why no overhang machinery is needed anywhere below. -/
theorem subWindowSup_mono_length (a : ℕ → ℂ) {L ℓ : ℕ} (h : L ≤ ℓ) (n : ℕ) (β : ℝ) :
    subWindowSup a L n β ≤ subWindowSup a ℓ n β :=
  subWindowSup_le (fun _K hK => le_subWindowSup a ℓ n β (le_trans hK h))

/-- **THE BLOCK-LENGTH DRIFT BOUND** — the twin of `M4Abel.abs_mul_window_le_of_arcDen`
(`M4Abel:238`) read at the *block* length rather than the window length.

At the tight major-arc radius `|θ| ≤ arcDen/(qH)`, a block of length `≤ ℓ` with
`arcDen·ℓ ≤ q·H` drifts by at most `1` — the phase turns through `O(1)` radians on the block,
which is exactly the statement that `ℓ` is the drift's own length. -/
theorem abs_mul_window_le_of_arcDen_block {B₅ : ℝ} {H q ℓ : ℕ} (hq : 0 < q) (hH : 0 < H)
    {θ : ℝ} (hθ : |θ| ≤ arcDen B₅ H / ((q : ℝ) * (H : ℝ)))
    (hadm : arcDen B₅ H * (ℓ : ℝ) ≤ (q : ℝ) * (H : ℝ)) :
    |θ| * (ℓ : ℝ) ≤ 1 := by
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqH : (0 : ℝ) < (q : ℝ) * (H : ℝ) := mul_pos hqR hHR
  have hℓ0 : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
  have h1 : |θ| * (ℓ : ℝ) ≤ arcDen B₅ H / ((q : ℝ) * (H : ℝ)) * (ℓ : ℝ) :=
    mul_le_mul_of_nonneg_right hθ hℓ0
  have h2 : arcDen B₅ H / ((q : ℝ) * (H : ℝ)) * (ℓ : ℝ) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hqH]
    exact hadm
  linarith

/-- **THE ONE-BLOCK DRIFT KILL.**  On a block `(A, B]` of length `≤ ℓ` inside the window, the
phase `e(θ·)` costs the ABSOLUTE factor `1 + 2π` over the block's own sub-window sup.

This is `M4Abel.norm_phase_sum_Ioc_drift` at `M := A`, `N := B`, with the uniform partial-sum
bound taken at cap `ℓ` (so every prefix of the block, including the truncated last one, is
already inside the sup — ⟦K-FREEDOM⟧). -/
theorem norm_block_phase_sum_le {ℓ A B : ℕ} (hAB : A ≤ B) (hlen : B - A ≤ ℓ) {θ : ℝ}
    (hdrift : |θ| * (ℓ : ℝ) ≤ 1) (a : ℕ → ℂ) (β : ℝ) :
    ‖∑ j ∈ Finset.Ioc A B, eR (θ * (j : ℝ)) * phaseCoeff a β j‖
      ≤ (1 + 2 * Real.pi) * subWindowSup a ℓ A β := by
  have hpart : ∀ K, A ≤ K → K ≤ B →
      ‖∑ j ∈ Finset.Ioc A K, phaseCoeff a β j‖ ≤ subWindowSup a ℓ A β := by
    intro K h1 h2
    rw [sum_Ioc_phaseCoeff_eq_sub a β h1]
    exact le_subWindowSup a ℓ A β (by omega)
  refine le_trans (norm_phase_sum_Ioc_drift hAB θ hpart) ?_
  refine mul_le_mul_of_nonneg_right ?_ (subWindowSup_nonneg a ℓ A β)
  have hlenR : ((B - A : ℕ) : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hlen
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hstep : |θ| * ((B - A : ℕ) : ℝ) ≤ |θ| * (ℓ : ℝ) :=
    mul_le_mul_of_nonneg_left hlenR (abs_nonneg θ)
  nlinarith

/-- **THE BLOCKED DRIFT COMPOSITION** — ⟦F3⟧'s payload.

`‖absWindowSum a H n (β+θ)‖ ≤ (1 + 2π)·∑_{m<N} subWindowSup a ℓ (n + m·ℓ) β`.

Compare `M4BridgePhase.norm_absWindowSum_le_drift` (`:291`), whose single-block reading pays
`1 + 2π·arcDen/q` against ONE sup of cap `H`.  Here the price is the absolute `1 + 2π` and the
`arcDen/q` has migrated into the block COUNT — where (after Cauchy–Schwarz and the per-block
normalisation `ℓ²`) it cancels against `ℓ` exactly: `N²ℓ² ≍ H²`. -/
theorem norm_absWindowSum_le_drift_blocked {B₅ : ℝ} {H q n ℓ : ℕ} (hq : 0 < q) (hH : 0 < H)
    (hℓ : 0 < ℓ) {β θ : ℝ} (hθ : |θ| ≤ arcDen B₅ H / ((q : ℝ) * (H : ℝ)))
    (hadm : arcDen B₅ H * (ℓ : ℝ) ≤ (q : ℝ) * (H : ℝ)) (a : ℕ → ℂ) :
    ‖absWindowSum a H n (β + θ)‖
      ≤ (1 + 2 * Real.pi)
          * ∑ m ∈ Finset.range (numBlocks H ℓ), subWindowSup a ℓ (n + m * ℓ) β := by
  have hdrift := abs_mul_window_le_of_arcDen_block (B₅ := B₅) (ℓ := ℓ) hq hH hθ hadm
  -- ⟦the window, cut into blocks⟧
  have hchunk : absWindowSum a H n (β + θ)
      = ∑ m ∈ Finset.range (numBlocks H ℓ),
          ∑ j ∈ Finset.Ioc (blockCut n H ℓ m) (blockCut n H ℓ (m + 1)),
            eR (θ * (j : ℝ)) * phaseCoeff a β j := by
    rw [absWindowSum_add_eq_phase_sum,
      sum_Ioc_chunk (fun j => eR (θ * (j : ℝ)) * phaseCoeff a β j) (blockCut_mono n H ℓ)
        (numBlocks H ℓ), blockCut_zero, blockCut_numBlocks hℓ]
  rw [hchunk]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  have hmlt := Finset.mem_range.mp hm
  have hbase : blockCut n H ℓ m = n + m * ℓ := blockCut_eq_of_lt hmlt
  have hle : blockCut n H ℓ m ≤ blockCut n H ℓ (m + 1) := blockCut_mono n H ℓ (Nat.le_succ m)
  have h := norm_block_phase_sum_le (ℓ := ℓ) hle (blockCut_succ_sub_le n H ℓ m) hdrift a β
  rw [hbase] at h
  rw [hbase]
  exact h

/-- **THE SQUARED FORM** — the blocked drift after Cauchy–Schwarz over the blocks.

`(∑_{m<N} S_m)² ≤ N·∑_{m<N} S_m²` (`sq_sum_le_card_mul_sum_sq`), so the door's *mean square*
reads the blocked supply with ONE factor `N` outside.  Composed with a per-block supply at
`Bblk·N·ℓ²` the two `N`'s and the `ℓ²` reassemble `(N·ℓ)² ≍ H²`. -/
theorem norm_absWindowSum_sq_le_drift_blocked {B₅ : ℝ} {H q n ℓ : ℕ} (hq : 0 < q) (hH : 0 < H)
    (hℓ : 0 < ℓ) {β θ : ℝ} (hθ : |θ| ≤ arcDen B₅ H / ((q : ℝ) * (H : ℝ)))
    (hadm : arcDen B₅ H * (ℓ : ℝ) ≤ (q : ℝ) * (H : ℝ)) (a : ℕ → ℂ) :
    ‖absWindowSum a H n (β + θ)‖ ^ 2
      ≤ (1 + 2 * Real.pi) ^ 2 * (numBlocks H ℓ : ℝ)
          * ∑ m ∈ Finset.range (numBlocks H ℓ), (subWindowSup a ℓ (n + m * ℓ) β) ^ 2 := by
  have hlin := norm_absWindowSum_le_drift_blocked (B₅ := B₅) (n := n) (β := β) (θ := θ)
    hq hH hℓ hθ hadm a
  have hS0 : (0 : ℝ) ≤ ∑ m ∈ Finset.range (numBlocks H ℓ), subWindowSup a ℓ (n + m * ℓ) β :=
    Finset.sum_nonneg fun m _ => subWindowSup_nonneg a ℓ (n + m * ℓ) β
  have hpi : (0 : ℝ) ≤ 1 + 2 * Real.pi := by positivity
  have hsq : ‖absWindowSum a H n (β + θ)‖ ^ 2
      ≤ (1 + 2 * Real.pi) ^ 2
          * (∑ m ∈ Finset.range (numBlocks H ℓ), subWindowSup a ℓ (n + m * ℓ) β) ^ 2 := by
    have hnn := norm_nonneg (absWindowSum a H n (β + θ))
    nlinarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (numBlocks H ℓ))
    (f := fun m => subWindowSup a ℓ (n + m * ℓ) β)
  rw [Finset.card_range] at hcs
  nlinarith [Finset.sum_nonneg (f := fun m => (subWindowSup a ℓ (n + m * ℓ) β) ^ 2)
    (s := Finset.range (numBlocks H ℓ)) (fun m _ => sq_nonneg _), sq_nonneg (1 + 2 * Real.pi)]

/-! ## §3 — THE BLOCKED SOCKET

`M4Close.M4SievedDoorSq`, discharged from the blocked supply.  The socket's integrand is the
BLOCK SUM of squared sub-window sups at the blocked bases; everything else in the statement is
`M4BridgePhase.M4SievedDoorSqSup`'s. -/

/-- **THE BLOCKED INTEGRAND** — `∑_{m<N} (sup over lengths ≤ ℓ at base n + m·ℓ)²`.  This is
the object wave ④'s χ-summed free-base row supplies, one blocked base at a time. -/
def blockSupSq (a : ℕ → ℂ) (H ℓ n : ℕ) (β : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (numBlocks H ℓ), (subWindowSup a ℓ (n + m * ℓ) β) ^ 2

theorem blockSupSq_nonneg (a : ℕ → ℂ) (H ℓ n : ℕ) (β : ℝ) : 0 ≤ blockSupSq a H ℓ n β :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The trivial bound at a `1`-bounded coefficient sequence: every block sup is `≤ ℓ`. -/
theorem blockSupSq_le_of_norm_le_one {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (H ℓ n : ℕ) (β : ℝ) :
    blockSupSq a H ℓ n β ≤ (numBlocks H ℓ : ℝ) * (ℓ : ℝ) ^ 2 := by
  have hterm : ∀ m ∈ Finset.range (numBlocks H ℓ),
      (subWindowSup a ℓ (n + m * ℓ) β) ^ 2 ≤ (ℓ : ℝ) ^ 2 := by
    intro m _
    have h := subWindowSup_le_of_norm_le_one ha ℓ (n + m * ℓ) β
    have h0 := subWindowSup_nonneg a ℓ (n + m * ℓ) β
    nlinarith
  calc blockSupSq a H ℓ n β ≤ ∑ _m ∈ Finset.range (numBlocks H ℓ), (ℓ : ℝ) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = (numBlocks H ℓ : ℝ) * (ℓ : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **THE BLOCKED SOCKET** — ⟦THE ③×④ INTERFACE⟧, stated once.

`M4BridgePhase.M4SievedDoorSqSup`'s statement with three changes, and only these three:

* the integrand is the BLOCK SUM `blockSupSq` at cap `ℓ H q` and bases `n + m·ℓ H q`, not the
  single sup at cap `H`;
* the right-hand side is `Bblk H · N · ℓ²` — "block count × per-block grade × block length²" —
  instead of `Braw H · q² · H²`.  ⟦NO `q²`⟧ the blocked price carries no residue-class factor
  at all: the class machinery is wave ④'s, and lives in `Bblk`;
* three admissibility binders on `ℓ` are premises, so a supplier need only produce the bound
  at legal block lengths.

⟦THE `N²ℓ² = H²` CONTRACT⟧  `m4_sievedDoorSq_of_blk` composes this with the blocked drift's
own factor `(1 + 2π)²·N`, giving `(1 + 2π)²·Bblk H·(N·ℓ)²`; since `N·ℓ ≤ H + ℓ ≤ 2H` the
assembled price is `4·(1 + 2π)²·Bblk H·H²` (and exactly `(1+2π)²·Bblk H·H²` when `ℓ ∣ H`).
That identity is the whole reason the blocking is free.

The band transport is carried as the same premise, so the ⟦A2-5⟧ binder stays visible and is
never unfolded. -/
def M4SievedDoorSqBlk (R : ChowlaRegime) (M : ℕ) (ℓ : ℕ → ℕ → ℕ) (Bblk : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
      (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q → ℓ H q ≤ H →
      (H : ℝ) ≤ arcDen 12 H * (ℓ H q : ℝ) →
        (∫ n, blockSupSq (doorSievedCoeff M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
            ∂(logMeasure R.x R.ω))
          ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2

/-- **THE BLOCKED SOCKET THEOREM** — ⟦F3⟧'s exit, the sibling of
`M4BridgePhase.m4_sievedDoorSq_of_sup` (`:434`).

`M4Close.M4SievedDoorSq R M Braw` from the blocked supply at the composed price
`4·(1 + 2π)²·Bblk H ≤ Braw H`.  ⟦THE DRIFT FACTOR IS ABSOLUTE⟧ — no `arcDen`, no `q`.  The
`q` survives only inside the block-length obligations `hℓcnt`/`hℓdrift`, which pin `ℓ H q`
into the interval `H/arcDen ≤ ℓ H q ≤ q·H/arcDen` (nonempty for every `q ≥ 1`); wave ④ owns
the witness. -/
theorem m4_sievedDoorSq_of_blk {R : ChowlaRegime} {M : ℕ} {ℓ : ℕ → ℕ → ℕ} {Bblk Braw : ℕ → ℝ}
    (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hℓ1 : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q)
    (hℓH : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → ℓ H q ≤ H)
    (hℓcnt : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (H : ℝ) ≤ arcDen 12 H * (ℓ H q : ℝ))
    (hℓdrift : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      arcDen 12 H * (ℓ H q : ℝ) ≤ (q : ℝ) * (H : ℝ))
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * (1 + 2 * Real.pi) ^ 2 * Bblk H ≤ Braw H)
    (hblk : M4SievedDoorSqBlk R M ℓ Bblk) : M4SievedDoorSq R M Braw := by
  intro htr H _ hlo hhi α hα
  have hH : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  obtain ⟨b, q, hq, hqQ, hd⟩ := hα
  have hℓ1' := hℓ1 H q hlo hhi hq hqQ
  have hℓH' := hℓH H q hlo hhi hq hqQ
  have hℓcnt' := hℓcnt H q hlo hhi hq hqQ
  have hℓdrift' := hℓdrift H q hlo hhi hq hqQ
  have hℓ0 : 0 < ℓ H q := hℓ1'
  set c := doorSievedCoeff M with hc
  set β : ℝ := (b : ℝ) / (q : ℝ) with hβ
  set L := ℓ H q with hL
  set N := numBlocks H L with hN
  -- ⟦the pointwise blocked drift, squared⟧
  have hpt : ∀ n : ℕ, ‖absWindowSum c H n α‖ ^ 2
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β := by
    intro n
    have h := norm_absWindowSum_sq_le_drift_blocked (B₅ := 12) (H := H) (q := q) (n := n)
      (ℓ := L) hq hH hℓ0 (β := β) (θ := α - β) hd hℓdrift' c
    have he : β + (α - β) = α := by ring
    rw [he] at h
    exact h
  -- ⟦the integral, and the grade⟧
  have hmono : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ ∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_mono hpt
  have hconst : (∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β
        ∂(logMeasure R.x R.ω))
      = (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * ∫ n, blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_const_mul _ _
  have hsupply := hblk htr H hlo hhi b q hq hqQ hℓ1' hℓH' hℓcnt'
  have hfac0 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) := by positivity
  have hstep : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := by
    rw [hconst] at hmono
    exact le_trans hmono (mul_le_mul_of_nonneg_left hsupply hfac0)
  -- ⟦`N²ℓ² ≤ 4H²`: the blocking is loss-free up to the absolute factor `4`⟧
  have hNL : N * L ≤ 2 * H := by
    have h1 : N * L ≤ H + L := by rw [hN]; exact numBlocks_mul_le H L
    omega
  have hNLR : (N : ℝ) * (L : ℝ) ≤ 2 * (H : ℝ) := by
    have : ((N * L : ℕ) : ℝ) ≤ ((2 * H : ℕ) : ℝ) := by exact_mod_cast hNL
    push_cast at this
    linarith
  have hNL0 : (0 : ℝ) ≤ (N : ℝ) * (L : ℝ) := by positivity
  have hsq : ((N : ℝ) * (L : ℝ)) ^ 2 ≤ 4 * (H : ℝ) ^ 2 := by nlinarith
  have hB := hB0 H
  have hpi2 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 := sq_nonneg _
  have hfin : (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
      ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by
    calc (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
        = (1 + 2 * Real.pi) ^ 2 * Bblk H * (((N : ℝ) * (L : ℝ)) ^ 2) := by ring
      _ ≤ (1 + 2 * Real.pi) ^ 2 * Bblk H * (4 * (H : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hpi2 hB)
      _ = 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by ring
  have hgr := hgrade H hlo hhi
  calc (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := hstep
    _ ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := hfin
    _ ≤ Braw H * (H : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hgr (sq_nonneg _)

/-- **THE BLOCKED SOCKET IS INHABITED** (the anti-vacuity duty, mirroring
`M4Close.m4_sievedDoorSq_trivial` and `M4BridgePhase.m4_sievedDoorSqSup_trivial`).

At the trivial grade `Bblk ≡ 1` each block sup is `≤ ℓ`, so the block sum is `≤ N·ℓ²` — the
socket's right-hand side ON THE NOSE.  So the blocked socket's hypothesis list is satisfiable
and ALL of its content is the grade. -/
theorem m4_sievedDoorSqBlk_trivial (R : ChowlaRegime) (M : ℕ) (ℓ : ℕ → ℕ → ℕ) :
    M4SievedDoorSqBlk R M ℓ (fun _ => 1) := by
  intro _ H _ _ _ b q _ _ _ _ _
  refine integral_logMeasure_le_of_le R.hx R.hω (fun n => ?_)
  have h := blockSupSq_le_of_norm_le_one (a := doorSievedCoeff M)
    (norm_doorSievedCoeff_le_one M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
  linarith [h]

/-! ## §4 — THE COVERING SIDE

`M4BridgeCover.integral_door_cover_le_clean` is stated at a **free nonnegative `g`**, so the
blocked integrand needs no new covering lemma — only the repackage, exactly as
`M4Join.m4_cover_assembly_sup` did for the unblocked sup. -/

/-- **THE PER-LADDER-BLOCK BLOCKED MEAN SQUARE.**  `M4Join.M4BlockMeanSqSup` at the blocked
integrand: the door ladder's block `(X_{i+1}, X_i]` against "block count × grade × ℓ² × block
bottom".

Two block notions meet here and must not be confused: the DOOR ladder's blocks (index `i < k`,
the harmonic cover of `(x/ω, x]`) and the DRIFT blocks (index `m < N`, the cut of the window
`(n, n+H]`).  They are independent; §5 records how the drift blocks sit inside the door
block's own doubled interval. -/
def M4BlockMeanSqBlk (R : ChowlaRegime) (M k : ℕ) (ℓ : ℕ → ℕ → ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
    1 ≤ ℓ H q → ℓ H q ≤ H → (H : ℝ) ≤ arcDen 12 H * (ℓ H q : ℝ) →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          blockSupSq (doorSievedCoeff M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
        ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2
            * (doorLadder R.x H (i + 1) : ℝ)

/-- **`m4_cover_assembly_blk` — THE BLOCKED ROUTE'S COVERING SIDE.**  The same
`integral_door_cover_le_clean`, the same door-gate bundle, the same absolute factor `3`.

Nothing about the covering argument depends on what the nonnegative integrand *is*, which is
precisely why `M4BridgeCover` §3 could state it at a free `g`. -/
theorem m4_cover_assembly_blk {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {ℓ : ℕ → ℕ → ℕ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqBlk R M k ℓ Bblk) :
    M4SievedDoorSqBlk R M ℓ (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ h1 h2 h3
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2 := by
    have := hB0 H; positivity
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => blockSupSq (doorSievedCoeff M) H (ℓ H q) n ((b : ℝ) / (q : ℝ)))
    (P := Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount
    (fun n => blockSupSq_nonneg _ _ _ _ _) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ h1 h2 h3)
  refine le_trans hmain (le_of_eq ?_)
  ring

/-- **THE BLOCKED BLOCK HYPOTHESIS IS INHABITED** (anti-vacuity, mirroring
`M4Join.m4_blockMeanSqSup_trivial`).  At `Bblk ≡ 1` each block sum is `≤ N·ℓ²` and the door
block's cardinality is `≤ X_{i+1}`. -/
theorem m4_blockMeanSqBlk_trivial (R : ChowlaRegime) (M k : ℕ) (ℓ : ℕ → ℕ → ℕ) :
    M4BlockMeanSqBlk R M k ℓ (fun _ => 1) := by
  intro H _ hhi b q _ _ _ _ _ i _
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hterm : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      blockSupSq (doorSievedCoeff M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
        ≤ (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2 := fun n _ =>
    blockSupSq_le_of_norm_le_one (norm_doorSievedCoeff_le_one M) H (ℓ H q) n _
  have hcard : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      blockSupSq (doorSievedCoeff M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
      ≤ ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
        * ((numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2) := by
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          blockSupSq (doorSievedCoeff M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
        ≤ ∑ _n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            ((numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2) := Finset.sum_le_sum hterm
      _ = ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
            * ((numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
      ≤ (doorLadder R.x H (i + 1) : ℝ) := by
    rw [Nat.card_Ioc]
    have hfit := doorLadder_fit R.x H i
    have hn : doorLadder R.x H i - doorLadder R.x H (i + 1) ≤ doorLadder R.x H (i + 1) := by
      omega
    exact_mod_cast hn
  have hpos := doorLadder_pos hxH (i + 1)
  have hQ : (0 : ℝ) ≤ (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2 := by positivity
  nlinarith

/-! ## §5 — THE SHIFTED-BASE BRIDGE

The drift blocks live at bases `n + m·ℓ` with `n` in a door-ladder block.  Wave ④'s χ-side
reads the free-base shift family at those bases, so it needs to know they stay inside the
engine's dyadic interval — they do, by the ladder's own fit, with no new gate.

Documented, not over-built: ④ owns the χ-side. -/

/-- **THE BLOCKED BASES SIT IN THE LADDER BLOCK'S DYADIC INTERVAL.**  For `n` in the door
block `(X_{i+1}, X_i]` and a drift block index `m < N`, the base `n + m·ℓ` lies in
`Icc X_{i+1} (2·X_{i+1})` — the same containment `M4Door.doorLadder_block_subset` gives the
unshifted window, because `m·ℓ ≤ H` and the ladder's fit is `X_i + H ≤ 2·X_{i+1}`. -/
theorem blockBase_mem_doorLadder_block {x H ℓ i m n : ℕ}
    (hn : n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i))
    (hm : m < numBlocks H ℓ) :
    n + m * ℓ ∈ Finset.Icc (doorLadder x H (i + 1)) (2 * doorLadder x H (i + 1)) := by
  rw [Finset.mem_Ioc] at hn
  rw [Finset.mem_Icc]
  have hmℓ := mul_le_of_lt_numBlocks hm
  have hfit := doorLadder_fit x H i
  omega

/-- **THE FACTOR-2 RULE AT THE BLOCKED BASES.**  `n + m·ℓ ≤ 2n`: the shift never doubles the
base, because `m·ℓ ≤ H ≤ X_{i+1} < n` (`doorLadder_floor`).  This is the shape a free-base row
consumer reads when it needs the shifted base to stay in the same dyadic scale. -/
theorem blockBase_le_two_mul {x H ℓ i m n : ℕ} (hxH : H + 1 ≤ x)
    (hn : n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i))
    (hm : m < numBlocks H ℓ) :
    (n + m * ℓ : ℝ) ≤ 2 * (n : ℝ) := by
  rw [Finset.mem_Ioc] at hn
  have hmℓ := mul_le_of_lt_numBlocks hm
  have hfloor := doorLadder_floor hxH (i + 1)
  have hnat : n + m * ℓ ≤ 2 * n := by omega
  have : ((n + m * ℓ : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast hnat
  push_cast at this
  linarith

end Salt.MR
