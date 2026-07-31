/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ClassPrice

/-!
# `M4WaveClosed` — THE FINAL COMPOSE (`m4_wave_closed`)

The M4 wave's last flight.  `M4Join` closed the wave at a six-item register whose last open
item was the row input; `M4ClassPrice` pre-composed steps 3–5 of the compose and pinned the
interface (⟦U2⟧, the forced order).  This file performs the join and states the wave's closed
theorem with ⟦THE FINAL REGISTER⟧ enumerated once, in classes.

## ⟦WHAT CHANGED IN THE COMPOSE⟧ — the mean-square re-cut of the class assembly

`M4ClassPrice`'s `m4_blockMeanSqSupQ_of_classPrice` assembles the block predicate from a
**pointwise** class price: a bound `‖∑_{m ∈ windowClass K n q r} 1_𝒮λ(m)‖ ≤ B H` holding at
EVERY door index `n` of the block and every sub-window length `K ≤ H`.  That lemma is true
and its arithmetic is exact, but its hypothesis is **not what a mean-square supplier can
deliver**, and at the strength the pricing needs (`B H ≈ H·(log H)^{−15}`, since the block
grade is `B H ²/H²` and must clear `m4Saving H = (log H)^{−30}`) it asserts cancellation in
*every* short interval of the block — strictly stronger than anything the MRT method proves,
which is a mean square over the block.  Taking the maximum over the block before squaring
throws the method away.

§2 lands the assembly in the shape the method actually produces: the class datum enters as a
**block mean square** (`M4ClassBlockMeanSq`), the split's `q` is paid ONCE inside the square
by Chebyshev (`sq_sum_le_card_mul_sum_sq`), and the resulting `q²` lands in exactly the same
`q`-graded slot of `M4BridgePhase.M4SievedDoorSqSup` that `M4ClassPrice` §4 opened.  The
composed grade is identical (`q²·B_cl`); only the input's shape changed, from `sup_n` to
`∑_n`.

## ⟦THE LAYERS⟧

* **§1 — `classSup`** — the class sum's sub-window sup, the single carrier the assembly
  reads.  `subWindowSup ≤ ∑_{r<q} classSup_r` is `M4ClassPrice` §1's split at every length
  (the rational phase is a unimodular constant on each class, so no phase survives — ⟦U2⟧).
* **§2 — the assembly** (`m4_blockMeanSqSupQ_of_classMeanSq`) and its socket exit
  (`m4_sievedDoorSq_of_classMeanSq`), the `q`-graded route of `M4ClassPrice` §7 steps 3–5
  entered at the mean-square datum.  Anti-vacuity: `m4_classBlockMeanSq_trivial`.
* **§3 — the χ-reduction** (`m4_classMeanSq_of_chiMeanSq`).  The character expansion, taken
  INSIDE the mean square: `‖class‖ ≤ (1/φ(q))∑_χ‖twisted‖` pointwise
  (`M4BridgeResidue.norm_sum_residueClassOn_liou_le`), then the square of the average is
  under the average of the squares (Chebyshev again), then the `n`-sum and the χ-average
  commute and `M4Close.inv_totient_sum_le` cancels the `1/φ(q)` exactly.  **Loss: none.**
  This covers the classes coprime to `q`; the non-coprime half is the named residue (below).
* **§4 — the pricing** (⟦U1⟧): the five raw summands of the capstone's conclusion
  (`M4Close.m4RawMS`) priced into one grade with the FIRST summand read through
  `M4ClassPrice.m4_decay_summand_eq` — the decay-retaining route, never
  `m4_quality_summand_le`.
* **§5 — `m4_wave_closed`** and its collision form, with ⟦THE FINAL REGISTER⟧.
* **§6 — the row bridge** (`m4_chiBlock_fixed_of_chiRow`).  The χ-uniform datum of §3, taken
  back one more layer: from the capstone's own currency (`ThmA2.thm_a2'_of_rows`' mean square
  at the block scale, un-phased) to the block sum of squared sieved-twisted window sums, via
  B-4's ladder lemma and `M4Join`'s exchange.  It lands the FIXED window length `K = H`; the
  sup over `K ≤ H` is the named residue (below).

## ⟦THE FINAL REGISTER⟧ — the S11 spine's consumption list

`m4_wave_closed`'s hypotheses, in the three classes the spine must dispatch:

**(a) REGIME/SCALE — thresholds the spine's `g`-arm absorbs** (all `X`-free or `Hhi`-only;
`M4Quality.m4JointThr` is the single joint inequality of this class):
1. `M4DoorGates Cg R M k δ` — M4-8's door-glue bundle; witness `M4Door.doorCount_gates` at
   `k := doorCount R.ω`.
2. `hdrift` — the drift price against the split's `q²`, `q`-graded:
   `(1 + 2π·arcDen 12 H/q)²·(q²·(3·B_cl H)) ≤ Braw H` on the window range.  Absolute:
   `M4BridgePhase.qgraded_drift_price_le` reads it as `(1+2π)²·arcDen 12 H²·(3·B_cl H)`.
3. `hdel` — `√(Braw H) ≤ mrtDeliveredGrade (C/2) H`, the budget line, via ⟦U3⟧
   (`m4_gradeGate_direct`; the `15 − 11/4` exponent gap is NOT spent).
4. `hrest` — the door's own two grades against the other half of the budget.

**(b) DATA** — `0 ≤ B_cl H`, `0 ≤ Braw H`; and `0 ≤ C`.

**(c) THE ONE ANALYTIC ITEM** — `M4ClassBlockMeanSq R M k B_cl`: the per-class block mean
square of the door's sieved `λ` at the arc's modulus.  §3 reduces its coprime half, with no
loss, to the χ-uniform block mean square `M4ChiBlockMeanSq` — i.e. to the mean square of the
SIEVED, χ-TWISTED short sums over the block, which is the M4/MRT capstone's own currency.

⟦THE RESIDUE, named⟧ THREE items keep (c) from being discharged from the landed capstone
(`M4MeanSq.m4_meansq_per_chi_gen`) today.  §6 lands everything between the capstone's own
currency and `M4ChiBlockMeanSq` EXCEPT the first of them; all three are statement questions
upstream of this file, not proof-engineering ones:

* **R1 — the maximal step** (§6's own boundary).  `m4_chiBlock_fixed_of_chiRow` delivers the
  block mean square at the FIXED window length `K = H`; `M4ChiBlockMeanSq` needs it with the
  sup over `K ≤ H` inside (`doorChiSup`), because `M4BridgePhase`'s drift produces a
  sub-window sup.  Going from one to the other is a maximal inequality over the partial sums
  of a short window — the standard dyadic route costs `(log H)²`, which the budget absorbs
  (the exponent gap is `15 − 11/4` against `arcDen`'s `(log H)^{12}`), but it is a page, not
  a rewrite.  The lossy alternative (`sup² ≤ ∑_{K≤H}`) costs a factor `H` and is fatal.
* **R2 — the non-coprime half** — for `d₀ = (r,q) > 1` the class is transported by ONE
  dilation (`M4ClassPrice.norm_sum_windowClass_memS_dilate`, an EQUALITY) to a coprime class
  of the DILATED window at base `n/d₀`; in mean-square form that transport re-indexes the
  block `n ↦ n/d₀` (`d₀`-to-one) onto an interval that is not a `doorLadder` block — this is
  `M4Join`'s ⟦THE CLASS PRICING⟧ obstruction in its surviving, mean-square form, and
  `M4ClassPrice` §5's endpoint drop is its first half.
* **R3 — the capstone's row datum** — `m4_meansq_per_chi_gen` still pins its co-factor slot
  to `ellLin (liouChi χ)` (the b-slot cut, registered open at the closing wave's ceremony)
  and still demands `∀ n, a n ≠ 0 → 1 ≤ blockOmega P P n`, i.e. a datum supported on
  multiples of the single block prime `P`.  The door's sieved `1_𝒮λχ̄` is neither.  The
  supply side's own last stone (`CaseAWide.m4_supplier_complete`) is already stated at the
  door's own co-factor datum `doorCofactor0`, so the b-slot half is a re-statement away
  (`ThmA2Rows.a2Rows_of_capfree3` and `FrameWitness.a2Frame3_witness` are both already
  `b`-generic); the `blockOmega` half is the block decomposition and is a design question.
  §6's `M4ChiRowMeanSq` is the exact shape the capstone must be brought to.

## ⟦THE TRAPS RESPECTED⟧

* the four log scales — this file writes `log H` only through `arcDen 12 H` (never
  evaluated) and `log X` only in §4's pricing page; the two never meet in one statement;
* the un-phased datum throughout — every carrier below is `doorSievedCoeff M` BARE; the
  rational phase is removed by `M4ClassPrice` §1 before the class sums are formed (⟦U2⟧);
* `liouvilleC`/`liouChi` only — never `lam`/`lamChi`;
* the enlarged-cap rule is MOOT here — no dilation is taken in this file, so no arc datum is
  transported and `arcDen·(H+d₀)/H` is never incurred;
* strict gates — `0 < q`, `R.Hlo ≤ H ≤ R.Hhi`, `0 < H` (from `R.hHlo_floor`) are carried;
* half-open — every window is `Finset.Ioc n (n+K)`, every block `Finset.Ioc X_{i+1} X_i`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — `classSup`: THE CLASS SUM'S SUB-WINDOW SUP

`M4BridgePhase.subWindowSup` is the sup of the *phased* window sums over sub-window lengths.
At a rational frequency the phase is a unimodular constant on each class (`M4ClassPrice` §1),
so the sup splits into `q` **phase-free** class sups.  This is the carrier the mean-square
assembly reads, and it is the un-phased datum's own object — no frequency appears in it. -/

/-- **THE CLASS SUP** `classSup a H n q r` — `sup_{K ≤ H} ‖∑_{m ≡ r (q), n < m ≤ n+K} a m‖`.
The sup is over LENGTHS (`Finset.Icc 0 H`), exactly as `subWindowSup`'s is. -/
def classSup (a : ℕ → ℂ) (H n q r : ℕ) : ℝ :=
  (Finset.Icc 0 H).sup' ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le H⟩⟩
    (fun K => ‖∑ m ∈ windowClass K n q r, a m‖)

/-- Every sub-window length is under the sup. -/
theorem le_classSup (a : ℕ → ℂ) (H n q r : ℕ) {K : ℕ} (hK : K ≤ H) :
    ‖∑ m ∈ windowClass K n q r, a m‖ ≤ classSup a H n q r :=
  Finset.le_sup' (f := fun K => ‖∑ m ∈ windowClass K n q r, a m‖)
    (Finset.mem_Icc.mpr ⟨Nat.zero_le K, hK⟩)

/-- The sup of norms is nonnegative (it dominates the empty window's `0`). -/
theorem classSup_nonneg (a : ℕ → ℂ) (H n q r : ℕ) : 0 ≤ classSup a H n q r :=
  le_trans (norm_nonneg _) (le_classSup a H n q r (Nat.zero_le H))

/-- A bound uniform over the sub-window lengths bounds the sup. -/
theorem classSup_le {a : ℕ → ℂ} {H n q r : ℕ} {B : ℝ}
    (hB : ∀ K, K ≤ H → ‖∑ m ∈ windowClass K n q r, a m‖ ≤ B) : classSup a H n q r ≤ B :=
  Finset.sup'_le _ _ (fun K hK => hB K (Finset.mem_Icc.mp hK).2)

/-- The trivial per-class bound: a class of a window of length `K` carries at most `K` terms
of modulus `≤ 1`.  (No `1/q` saving is claimed — the honest ceiling is `H`.) -/
theorem norm_sum_windowClass_le_of_norm_le_one {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1)
    (K n q r : ℕ) : ‖∑ m ∈ windowClass K n q r, a m‖ ≤ (K : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 (fun m _ => ha m)) ?_
  rw [nsmul_eq_mul, mul_one]
  have hcard : (windowClass K n q r).card ≤ K := by
    have h := Finset.card_le_card (windowClass_subset K n q r)
    rwa [Nat.card_Ioc, Nat.add_sub_cancel_left] at h
  exact_mod_cast hcard

theorem classSup_le_of_norm_le_one {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (H n q r : ℕ) :
    classSup a H n q r ≤ (H : ℝ) :=
  classSup_le fun K hK =>
    le_trans (norm_sum_windowClass_le_of_norm_le_one ha K n q r) (by exact_mod_cast hK)

/-- **THE SPLIT, AT EVERY SUB-WINDOW LENGTH.**  `M4ClassPrice.norm_absWindowSum_rat_le_class_sums`
applied inside `subWindowSup`'s sup-elimination: the sub-window sup at the rational `b/q` is
under the sum of the `q` class sups.  The rational phase leaves no trace (⟦U2⟧). -/
theorem subWindowSup_le_sum_classSup (a : ℕ → ℂ) (H n : ℕ) {q : ℕ} (hq : 0 < q) (b : ℤ) :
    subWindowSup a H n ((b : ℝ) / (q : ℝ))
      ≤ ∑ r ∈ Finset.range q, classSup a H n q r :=
  subWindowSup_le fun K hK =>
    le_trans (norm_absWindowSum_rat_le_class_sums a K n hq b)
      (Finset.sum_le_sum fun r _ => le_classSup a H n q r hK)

/-! ## §2 — THE ASSEMBLY, IN MEAN-SQUARE FORM

The class datum enters as a block mean square, one class at a time.  The split's `q` is paid
once inside the square (Chebyshev), the `q` classes are summed, and the resulting `q²` is
exactly `M4BridgePhase.M4SievedDoorSqSup`'s `q`-graded slot — the same `q` as the drift
witness's, by `M4ClassPrice` §4's identity. -/

/-- **THE ANALYTIC ITEM** (`M4ClassBlockMeanSq`) — the per-class block mean square of the
door's sieved `λ`, at the arc's own modulus range.  This is what the M4 wave's supply side
must deliver, and it is the mean-square shape: the sum over the block's door indices of the
squared class sup, NOT a maximum over the block. -/
def M4ClassBlockMeanSq (R : ChowlaRegime) (M k : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ r, r < q →
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff M) H n q r) ^ 2
        ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE ANTI-VACUITY WITNESS** (the house's duty, mirroring
`M4Join.m4_blockMeanSqSup_trivial`).  At the trivial grade `B_cl ≡ 1` every class sup is
`≤ H` and the block's cardinality is `≤ X_{i+1}` (`M4Door.doorLadder_fit`), so the predicate
holds outright.  Its hypothesis list is therefore not satisfiable-by-nobody: ALL of its
content is the grade. -/
theorem m4_classBlockMeanSq_trivial (R : ChowlaRegime) (M k : ℕ) :
    M4ClassBlockMeanSq R M k (fun _ => 1) := by
  intro H _ hhi q _ _ i _ r _
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hterm : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (classSup (doorSievedCoeff M) H n q r) ^ 2 ≤ (H : ℝ) ^ 2 := by
    intro n _
    have h := classSup_le_of_norm_le_one (norm_doorSievedCoeff_le_one M) H n q r
    have h0 := classSup_nonneg (doorSievedCoeff M) H n q r
    nlinarith
  have hsum : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (classSup (doorSievedCoeff M) H n q r) ^ 2
      ≤ ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
        * (H : ℝ) ^ 2 := by
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff M) H n q r) ^ 2
        ≤ ∑ _n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i), (H : ℝ) ^ 2 :=
          Finset.sum_le_sum hterm
      _ = ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
            * (H : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
      ≤ (doorLadder R.x H (i + 1) : ℝ) := by
    rw [Nat.card_Ioc]
    have hfit := doorLadder_fit R.x H i
    have hn : doorLadder R.x H i - doorLadder R.x H (i + 1) ≤ doorLadder R.x H (i + 1) := by
      omega
    exact_mod_cast hn
  have hpos := doorLadder_pos hxH (i + 1)
  nlinarith

/-- **THE ASSEMBLY** (`m4_blockMeanSqSupQ_of_classMeanSq`).  The `q`-graded block predicate
from the per-class block mean square.

The arithmetic, once: pointwise in the door index `n`,

```
   (subWindowSup)²  ≤  (∑_{r<q} classSup_r)²  ≤  q·∑_{r<q} classSup_r²
```

(the split of §1, then Chebyshev at `#(range q) = q`); summing over the block and applying
the per-class datum `q` times gives `q²·B_cl H·H²·X_{i+1}`, which is
`M4ClassPrice.M4BlockMeanSqSupQ`'s right-hand side verbatim.

Compare `M4ClassPrice.m4_blockMeanSqSupQ_of_classPrice`: identical output grade, but its
input is the pointwise class price (a bound at every `n` of the block).  Here the block sum
is the input — the shape a mean-square supplier produces. -/
theorem m4_blockMeanSqSupQ_of_classMeanSq {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hcl : M4ClassBlockMeanSq R M k Bcl) : M4BlockMeanSqSupQ R M k Bcl := by
  intro H hlo hhi b q hq hqQ i hik
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  -- ⟦pointwise: the split, then Chebyshev⟧
  have hpt : ∀ n : ℕ,
      (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (q : ℝ) * ∑ r ∈ Finset.range q, (classSup (doorSievedCoeff M) H n q r) ^ 2 := by
    intro n
    have hsplit := subWindowSup_le_sum_classSup (doorSievedCoeff M) H n hq b
    have h0 := subWindowSup_nonneg (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))
    have hsq : (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (∑ r ∈ Finset.range q, classSup (doorSievedCoeff M) H n q r) ^ 2 := by
      nlinarith
    refine hsq.trans ?_
    have hcheb := sq_sum_le_card_mul_sum_sq
      (s := Finset.range q) (f := fun r => classSup (doorSievedCoeff M) H n q r)
    rwa [Finset.card_range] at hcheb
  -- ⟦the block sum⟧
  have hstep1 : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (q : ℝ) * ∑ r ∈ Finset.range q, (classSup (doorSievedCoeff M) H n q r) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (q : ℝ) * ∑ r ∈ Finset.range q, (classSup (doorSievedCoeff M) H n q r) ^ 2
      = (q : ℝ) * ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff M) H n q r) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  have hper : ∑ r ∈ Finset.range q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff M) H n q r) ^ 2
      ≤ (q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) := by
    calc ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff M) H n q r) ^ 2
        ≤ ∑ _r ∈ Finset.range q,
            (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) :=
          Finset.sum_le_sum fun r hr =>
            hcl H hlo hhi q hq hqQ i hik r (Finset.mem_range.mp hr)
      _ = (q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ (q : ℝ) * ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff M) H n q r) ^ 2 := by rw [← hswap]; exact hstep1
    _ ≤ (q : ℝ) * ((q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ))) :=
        mul_le_mul_of_nonneg_left hper hq0
    _ = Bcl H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by ring

/-- **THE SOCKET EXIT** (`m4_sievedDoorSq_of_classMeanSq`) — `M4ClassPrice` §7's steps 3–5,
entered at the mean-square datum:

3. `m4_blockMeanSqSupQ_of_classMeanSq` (§2) assembles `M4BlockMeanSqSupQ`;
4. `M4ClassPrice.m4_cover_assembly_supQ` covers, at the absolute factor `3`;
5. `M4BridgePhase.m4_sievedDoorSq_of_sup` discharges `M4Close.M4SievedDoorSq`, the split's
   `q²` meeting the drift's `1/q²` exactly.

This is `M4ClassPrice.m4_sievedDoorSq_of_classPrice` with its input re-cut, and nothing
else. -/
theorem m4_sievedDoorSq_of_classMeanSq {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {Bcl Braw : ℕ → ℝ}
    (hgates : M4DoorGates Cg R M k δ) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hdrift : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
        ≤ Braw H)
    (hcl : M4ClassBlockMeanSq R M k Bcl) :
    M4SievedDoorSq R M Braw :=
  m4_sievedDoorSq_of_sup hdrift
    (m4_cover_assembly_supQ hgates hBcl0 (m4_blockMeanSqSupQ_of_classMeanSq hcl))

/-! ## §3 — THE χ-REDUCTION, INSIDE THE MEAN SQUARE

`M4Close.inv_totient_sum_le` cancels the `1/φ(q)` against a bound holding uniformly over `χ`.
The mean-square version needs one more step — the square of the χ-average is under the
χ-average of the squares — and then the `n`-sum and the χ-average commute freely.  The result
is loss-free: a χ-uniform BLOCK mean square gives the per-class block mean square at the same
grade. -/

/-- **THE SQUARE OF THE AVERAGE, UNDER THE AVERAGE OF THE SQUARES** (over the character
group).  Chebyshev at `#{χ mod q} = φ(q)` (`M4Close.card_dirichletCharacter_eq_totient`). -/
theorem sq_inv_totient_sum_le_sum_sq {q : ℕ} [NeZero q] (F : DirichletCharacter ℂ q → ℝ) :
    ((q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, F χ) ^ 2
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (F χ) ^ 2 := by
  have hφ : (0 : ℝ) < (q.totient : ℝ) := totient_cast_pos q
  have hcard : ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) = (q.totient : ℝ) := by
    rw [Finset.card_univ]
    exact_mod_cast card_dirichletCharacter_eq_totient q
  have hcheb := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (DirichletCharacter ℂ q))) (f := F)
  rw [hcard] at hcheb
  have hstep : ((q.totient : ℝ)⁻¹) ^ 2 * (∑ χ : DirichletCharacter ℂ q, F χ) ^ 2
      ≤ ((q.totient : ℝ)⁻¹) ^ 2
          * ((q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, (F χ) ^ 2) :=
    mul_le_mul_of_nonneg_left hcheb (by positivity)
  have hlhs : ((q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, F χ) ^ 2
      = ((q.totient : ℝ)⁻¹) ^ 2 * (∑ χ : DirichletCharacter ℂ q, F χ) ^ 2 := by ring
  have hrhs : ((q.totient : ℝ)⁻¹) ^ 2
        * ((q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, (F χ) ^ 2)
      = (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (F χ) ^ 2 := by
    field_simp
  rw [hlhs, ← hrhs]
  exact hstep

/-- **THE DOOR'S SIEVED WINDOW**, named once: `{n < m ≤ n+K : m ∈ 𝒮}` at the door's own
K-family.  `M4ClassPrice.sievedWindow` at `p := MemS (calP …) (calQK …) 2`. -/
def doorSievedWindow (M K n : ℕ) : Finset ℕ :=
  sievedWindow (MemS (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2) K n

/-- **THE χ-TWISTED SUP** `doorChiSup χ M H n` — `sup_{K ≤ H} ‖∑_{m ∈ 𝒮, n < m ≤ n+K} λ(m)χ̄(m)‖`.
The datum is `liouChi χ` (the ⟦lam collision⟧: the sum runs over integers). -/
def doorChiSup {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) : ℝ :=
  (Finset.Icc 0 H).sup' ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le H⟩⟩
    (fun K => ‖∑ m ∈ doorSievedWindow M K n, liouChi χ m‖)

theorem le_doorChiSup {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) {K : ℕ} (hK : K ≤ H) :
    ‖∑ m ∈ doorSievedWindow M K n, liouChi χ m‖ ≤ doorChiSup χ M H n :=
  Finset.le_sup' (f := fun K => ‖∑ m ∈ doorSievedWindow M K n, liouChi χ m‖)
    (Finset.mem_Icc.mpr ⟨Nat.zero_le K, hK⟩)

theorem doorChiSup_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) :
    0 ≤ doorChiSup χ M H n :=
  le_trans (norm_nonneg _) (le_doorChiSup χ M H n (Nat.zero_le H))

/-- **THE χ-UNIFORM BLOCK MEAN SQUARE** — the shape the M4/MRT capstone natively produces
(per character, over one ladder block), with the sub-window sup inside. -/
def M4ChiBlockMeanSq (R : ChowlaRegime) (M k : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (doorChiSup χ M H n) ^ 2
        ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE POINTWISE HALF** (`classSup_le_inv_totient_sum_doorChiSup`).  For a class coprime
to `q`, the class sup is under the χ-average of the twisted sups.  Route, at each length `K`:
`M4ClassPrice.sum_windowClass_memSCoeff` (the two filters commute) then
`M4BridgeResidue.norm_sum_residueClassOn_liou_le` (the decomposition, `χ(r)` unimodular). -/
theorem classSup_le_inv_totient_sum_doorChiSup {q : ℕ} [NeZero q] {r : ℕ}
    (hcop : Nat.Coprime q r) (M H n : ℕ) :
    classSup (doorSievedCoeff M) H n q r
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup χ M H n := by
  refine classSup_le fun K hK => ?_
  have hfilt : ∑ m ∈ windowClass K n q r, doorSievedCoeff M m
      = ∑ m ∈ residueClassOn q r (doorSievedWindow M K n), liouvilleC m := by
    simpa only [doorSievedCoeff, doorSievedWindow] using
      sum_windowClass_memSCoeff (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) 2 liouvilleC K n q r
  rw [hfilt]
  refine le_trans (norm_sum_residueClassOn_liou_le hcop (doorSievedWindow M K n)) ?_
  have hφ : (0 : ℝ) < (q.totient : ℝ) := totient_cast_pos q
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum fun χ _ => le_doorChiSup χ M H n hK

/-- **THE χ-REDUCTION** (`m4_classMeanSq_of_chiMeanSq`) — the coprime half of
`M4ClassBlockMeanSq`, from `M4ChiBlockMeanSq`, at the SAME grade.  **No loss at all**: the
`1/φ(q)` of the decomposition cancels against the character count exactly
(`M4Close.inv_totient_sum_le`), and the only inequality spent is the square-of-average step,
which the χ-uniformity of the input makes free. -/
theorem m4_classMeanSq_of_chiMeanSq {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hchi : M4ChiBlockMeanSq R M k Bcl) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ r, r < q → Nat.Coprime q r →
        ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff M) H n q r) ^ 2
          ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by
  intro H hlo hhi q hq hqQ i hik r _ hcop
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦pointwise: the χ-average, squared⟧
  have hpt : ∀ n : ℕ, (classSup (doorSievedCoeff M) H n q r) ^ 2
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup χ M H n) ^ 2 := by
    intro n
    have hle := classSup_le_inv_totient_sum_doorChiSup hcop M H n
    have h0 := classSup_nonneg (doorSievedCoeff M) H n q r
    have hsq : (classSup (doorSievedCoeff M) H n q r) ^ 2
        ≤ ((q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup χ M H n) ^ 2 := by
      nlinarith
    exact hsq.trans (sq_inv_totient_sum_le_sum_sq (fun χ => doorChiSup χ M H n))
  -- ⟦the block sum, then the χ-average and the `n`-sum commute⟧
  have hstep1 : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (classSup (doorSievedCoeff M) H n q r) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup χ M H n) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup χ M H n) ^ 2
      = (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (doorChiSup χ M H n) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hswap] at hstep1
  refine hstep1.trans ?_
  exact inv_totient_sum_le (fun χ => hchi H hlo hhi q hq hqQ i hik χ)

/-! ## §4 — THE PRICING PAGE (⟦U1⟧, the decay-retaining route)

`M4Close.m4RawMS` is the capstone's five-summand right-hand side.  Priced into one grade with
the FIRST summand read through `M4ClassPrice.m4_decay_summand_eq` — an EQUALITY, retaining
the honest `(log X)^{1/45 − 7/(30e)}` decay.

⚠ NEVER `M4Close.m4_quality_summand_le` on the first summand: its gate `g1` demands
`8448·C₁'² ≤ 1/5`, unsatisfiable at `C₁' = cfbC₁ X C₁ ≥ 1` (`M4ClassPrice`'s header). -/

/-- **THE FIVE SUMMANDS, PRICED** (`m4_rawMS_priced_decay`).  `M4Close.m4_rawMS_le` with its
first gate replaced by the decay-retaining one: the raw mean square at the band's own
constants `C₁' = cfbC₁ X C₁`, `M₀ = cfbM0 K q X` is below `G` as soon as each of the five
displayed gates reads against `G/5`.  The row never chooses a numeral. -/
theorem m4_rawMS_priced_decay {X C₁ K h G : ℝ} {q M : ℕ} (hX : 0 < Real.log X)
    (g1 : m4DecayGrade K q X C₁ ≤ G / 5)
    (g2 : 1787702400 * a2Level1 M ≤ G / 5)
    (g3 : 188133 * (Real.log X) ^ (-(1 : ℝ) / 500) ≤ G / 5)
    (g4 : 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) ≤ G / 5)
    (g5 : 6315000 / h ≤ G / 5) :
    m4RawMS (cfbC₁ X C₁) (cfbM0 K q X) M X h ≤ G := by
  have hdec : 8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * cfbM0 K q X)
      = m4DecayGrade K q X C₁ := m4_decay_summand_eq hX
  unfold m4RawMS
  rw [hdec]
  linarith

/-- **THE DECAY GRADE'S OWN CEILING** — the `X`-factor is `≤ 1` past `log X ≥ 1`
(`M4ClassPrice.m4DecayGrade_factor_le_one`, whose exponent is STRICTLY negative), so the
grade is under its own debit factor.  This is the form the regime's `g`-arm reads: the whole
`X`-dependence of the first summand is one factor that decays. -/
theorem m4DecayGrade_le_debit {X C₁ K : ℝ} {q : ℕ} (hX : 1 ≤ Real.log X) :
    m4DecayGrade K q X C₁
      ≤ 8448 * (C₁ + 1) ^ 2
          * Real.exp ((1 / Real.exp 1)
              * (23 / 16 * Real.log (Real.log (Real.log X)) + 3 / 4 * Real.log (q : ℝ)
                  + 1 / 4 * (q : ℝ) + K)) := by
  have hfac := m4DecayGrade_factor_le_one (X := X) hX
  have h0 : (0 : ℝ) ≤ 8448 * (C₁ + 1) ^ 2
      * Real.exp ((1 / Real.exp 1)
          * (23 / 16 * Real.log (Real.log (Real.log X)) + 3 / 4 * Real.log (q : ℝ)
              + 1 / 4 * (q : ℝ) + K)) := by positivity
  unfold m4DecayGrade
  nlinarith [Real.rpow_nonneg (le_trans zero_le_one hX)
    ((1 : ℝ) / 45 - 7 / (30 * Real.exp 1))]

/-! ## §5 — ⟦THE CLOSE⟧

`M4Close.m4_door_contradiction_of_live` carries three sockets: the door gates, the grade gate
and `M4SievedDoorSq`.  §2 discharges the third from the class mean square, ⟦U3⟧
(`M4ClassPrice.m4_gradeGate_direct`) the second without spending the exponent gap, and the
first is M4-8's own witness.  Composing them is the M4 wave, end to end. -/

/-- **`m4_wave_closed` — THE M4 WAVE'S CLOSED THEOREM.**

For every `C ≥ 0` and every floor / outer-scale demand there is a regime `R` at which
log-Chowla-2 does not fail, conditional on exactly ⟦THE FINAL REGISTER⟧ (the module header's
three classes) and on nothing else:

**(a) REGIME/SCALE** — `M4DoorGates Cg R M k δ` (witness `M4Door.doorCount_gates`);
`hdrift` (the `q`-graded drift price, absolute by `M4BridgePhase.qgraded_drift_price_le`);
`hdel` (`√(Braw H) ≤ mrtDeliveredGrade (C/2) H` — ⟦U3⟧, the exponent gap unspent);
`hrest` (the door's own two grades against the other half).

**(b) DATA** — `0 ≤ B_cl H`, `0 ≤ Braw H`, `0 ≤ C`.

**(c) THE ANALYTIC ITEM** — `M4ClassBlockMeanSq R M k B_cl`, the per-class block mean square
of the door's sieved `λ`.  §3 reduces its coprime half, LOSSLESSLY, to `M4ChiBlockMeanSq` —
the χ-uniform block mean square, i.e. the M4/MRT capstone's own currency.  The non-coprime
half and the capstone's row-datum binders are the module header's ⟦THE RESIDUE⟧.

Nothing else: the arc, the budget head, the collision, the sieve insert, the harmonic cover,
the `log ω` absorption, the `L²→L¹` descent, the residue split, the phase removal, the class
assembly and the grade gate are all landed and consumed. -/
theorem m4_wave_closed :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ClassBlockMeanSq R M k Bcl →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hcl => ?_⟩
  exact hR δ Braw M k hgates hBraw0 (m4_gradeGate_direct hdel hrest)
    (m4_sievedDoorSq_of_classMeanSq hgates hBcl0 hdrift hcl)

/-- **The close's collision form** (`m4_wave_closed_False`).  Same register; with the failure
branch assumed at the exit's regime the chain closes to `False`. -/
theorem m4_wave_closed_False :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ClassBlockMeanSq R M k Bcl →
              logChowla2Fails R.eps R.x R.ω → False := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_False_of_live
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hcl => ?_⟩
  exact hR δ Braw M k hgates hBraw0 (m4_gradeGate_direct hdel hrest)
    (m4_sievedDoorSq_of_classMeanSq hgates hBcl0 hdrift hcl)

/-- **THE CLOSE AT THE χ-UNIFORM DATUM** (`m4_wave_closed_of_chi`) — the same theorem with
class (c) read one layer further down, at the character-twisted block mean square.  The
`hnoncop` slot is the module header's ⟦THE RESIDUE⟧, first item: the non-coprime classes,
whose transport is `M4ClassPrice.norm_sum_windowClass_memS_dilate` (an EQUALITY) followed by
the same character expansion at the reduced modulus, and whose mean-square form re-indexes
the block `n ↦ n/d₀`.  It is carried here, not assumed away. -/
theorem m4_wave_closed_of_chi :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ChiBlockMeanSq R M k Bcl →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff M) H n q r) ^ 2
                  ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hchi hnoncop => ?_⟩
  refine hR δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest ?_
  intro H hlo hhi q hq hqQ i hik r hr
  by_cases hcop : Nat.Coprime q r
  · exact m4_classMeanSq_of_chiMeanSq hchi H hlo hhi q hq hqQ i hik r hr hcop
  · exact hnoncop H hlo hhi q hq hqQ i hik r hr hcop

/-! ### ⟦THE SPLIT TWINS⟧ (second-road freeze v2, wave ①)

The family's contract is `M4Exit` §7.  The class machinery is untouched: the class assembly,
the `q`-graded drift price, the χ-average and the non-coprime slot are all consumed verbatim.
Only `hdel` and `hrest` re-cut against the head's constant `δ₀`, and the `C_MRT` binder
leaves.

⟦NOTE THE `q²`⟧ these two registers hard-wire the class modulus in their drift conjunct
(`(1 + 2π·arcDen/q)²·(q²·(3·B_cl))`) and weave `B_cl` into three conjuncts — which is exactly
why D-1 ratified `M4Join.m4_wave_exit_sup_split` as the second road's target register and not
these.  They are landed here so the class road keeps its split sibling. -/

/-- **THE M4 WAVE'S CLOSED THEOREM, SPLIT** (`m4_wave_closed_split`) — the twin of
`m4_wave_closed` (:525).

⟦THE FINAL REGISTER, split form⟧ — the landed one with `0 ≤ C` deleted and the two grade
lines re-cut: `hdel` becomes `√(Braw H) ≤ δ₀/2` and `hrest` becomes
`δ/4 + 4·2^k/x ≤ δ₀/2`.  `M4DoorGates`, the `q`-graded drift line, `0 ≤ B_cl`, `0 ≤ Braw`
and `M4ClassBlockMeanSq` are all byte-unchanged, and so is the conclusion. -/
theorem m4_wave_closed_split :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.sqrt (Braw H) ≤ δ₀ / 2) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 2) →
            M4ClassBlockMeanSq R M k Bcl →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_split
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hcl => ?_⟩
  exact hR δ Braw M k hgates hBraw0 (m4_gradeGate_direct_split hdel hrest)
    (m4_sievedDoorSq_of_classMeanSq hgates hBcl0 hdrift hcl)

/-- **THE CLOSE AT THE χ-UNIFORM DATUM, SPLIT** (`m4_wave_closed_of_chi_split`) — the twin of
`m4_wave_closed_of_chi` (:583): `m4_wave_closed_split` with class (c) read one layer further
down, at the character-twisted block mean square, and the non-coprime slot carried
unchanged. -/
theorem m4_wave_closed_of_chi_split :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.sqrt (Braw H) ≤ δ₀ / 2) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 2) →
            M4ChiBlockMeanSq R M k Bcl →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff M) H n q r) ^ 2
                  ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_split
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hchi hnoncop => ?_⟩
  refine hR δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest ?_
  intro H hlo hhi q hq hqQ i hik r hr
  by_cases hcop : Nat.Coprime q r
  · exact m4_classMeanSq_of_chiMeanSq hchi H hlo hhi q hq hqQ i hik r hr hcop
  · exact hnoncop H hlo hhi q hq hqQ i hik r hr hcop

/-! ## §6 — THE ROW BRIDGE: the capstone's currency into the block

`M4ChiBlockMeanSq` (§3) is one layer above the capstone.  This section lands that layer at
the FIXED window length, so that exactly one named gap (⟦R1⟧, the maximal step) separates the
M4 wave's analytic item from `ThmA2.thm_a2'_of_rows`' own conclusion.

The route is `M4Join` §3's, at the frequency `0` instead of a tight-major `α` — which is what
⟦U2⟧'s forced order delivers (the drift, the split and the expansion all REMOVE the phase, so
the capstone is instantiated un-phased).  `M4ClassPrice.doorCoeffPhase_zero` is the whole
bridge between the two spellings. -/

/-- **THE SIEVED, χ-TWISTED DATUM** `doorChiCoeff χ M = 1_𝒮·λχ̄` at the door's own K-family.
The ⟦lam collision⟧: `liouChi`, never `lamChi` — the sum runs over integers. -/
def doorChiCoeff {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) : ℕ → ℂ :=
  memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 (liouChi χ)

/-- The indicator-restricted window sum IS the sum over the sieved window. -/
theorem absWindowSum_doorChiCoeff_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) :
    absWindowSum (doorChiCoeff χ M) H n 0 = ∑ m ∈ doorSievedWindow M H n, liouChi χ m := by
  rw [absWindowSum_zero, doorSievedWindow, sievedWindow, Finset.sum_filter]
  rfl

/-- **THE ROW INPUT, PER CHARACTER** (`M4ChiRowMeanSq`) — the mean square of the door's
sieved, χ-twisted, UN-PHASED datum on one ladder block, in `ThmA2.thm_a2'_of_rows`' own
currency (`1/X·∫_X^{2X}‖(1/H)·shortSum a (seamS0 N X) y H‖²` at `X = X_{i+1}`, `N = 2X_{i+1}`,
`h = H`).

The instantiation is forced, not chosen — the two pins `X_d = X` and `N = 2X_d` are exactly
`M4MeanSq.m4_meansq_per_chi_gen`'s, and the window length is the door's own `H`.  This is
`M4ClassPrice.M4RowMeanSqUnphased` at the χ-twisted datum: the same block, the same seam
index set, the same currency, with `liouvilleC` replaced by `liouChi χ` under the sieve. -/
def M4ChiRowMeanSq (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
      1 / (doorLadder R.x H (i + 1) : ℝ)
          * (∫ y in (doorLadder R.x H (i + 1) : ℝ)..(2 * (doorLadder R.x H (i + 1) : ℝ)),
              ‖((1 / (H : ℝ) : ℝ) : ℂ)
                  * shortSum (doorChiCoeff χ M)
                      (seamS0 (2 * doorLadder R.x H (i + 1))
                        (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
        ≤ MS H

/-- **THE ROW BRIDGE** (`m4_chiBlock_fixed_of_chiRow`).  The per-character row mean square
becomes the block sum of squared sieved-twisted window sums, at the grade `2·MS`:

* B-4's `M4BridgeIntegral.sum_Ioc_absWindowSum_sq_div_le_ladder` at the frequency `0` (both
  its fits are `le_rfl` and `M4Door.doorLadder_fit` — ⟦THE ENDPOINT LEDGER⟧: no boundary
  loss at all), with the coverage datum free at the block's own seam index set;
* `M4Join.sum_Ioc_le_two_mul_of_harmonic`, the harmonic→flat exchange, at the ladder's
  factor `2` and nothing else.

This is `M4ChiBlockMeanSq`'s body with `doorChiSup` replaced by the FIXED length `K = H`.
⟦R1⟧ — the maximal step from here to the sup — is the module header's first residue. -/
theorem m4_chiBlock_fixed_of_chiRow {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℝ}
    (hrow : M4ChiRowMeanSq R M k MS) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
        ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            ‖∑ m ∈ doorSievedWindow M H n, liouChi χ m‖ ^ 2
          ≤ 2 * MS H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by
  intro H hlo hhi q hq hqQ i hik χ
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hfit := doorLadder_fit R.x H i
  -- ⟦the coverage datum is free at the block's own seam index set⟧
  have hcov : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      ∀ m ∈ Finset.Ioc n (n + H), m ∉ seamS0 (2 * doorLadder R.x H (i + 1))
          (doorLadder R.x H (i + 1) : ℝ) → doorChiCoeff χ M m = 0 :=
    hcov_of_seamS0 (doorChiCoeff χ M) (A := doorLadder R.x H (i + 1))
      (B := doorLadder R.x H i) (N := 2 * doorLadder R.x H (i + 1)) (H := H) le_rfl
      (by omega)
  -- ⟦the row datum, read at the removed phase⟧
  have hMS0 : 1 / ((doorLadder R.x H (i + 1) : ℕ) : ℝ)
      * (∫ y in ((doorLadder R.x H (i + 1) : ℕ) : ℝ)..(2
            * ((doorLadder R.x H (i + 1) : ℕ) : ℝ)),
          ‖((1 / (H : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff χ M) 0)
                  (seamS0 (2 * doorLadder R.x H (i + 1))
                    (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
      ≤ MS H := by
    rw [doorCoeffPhase_zero]
    exact hrow H hlo hhi q hq hqQ i hik χ
  -- ⟦B-4: the harmonic-weighted block bound⟧
  have hladder := sum_Ioc_absWindowSum_sq_div_le_ladder (doorChiCoeff χ M)
    (seamS0 (2 * doorLadder R.x H (i + 1)) (doorLadder R.x H (i + 1) : ℝ)) 0
    (x := R.x) (H := H) (i := i) (MS := MS H) hH0 hxH hcov hMS0
  -- ⟦the exchange⟧
  have hflat := sum_Ioc_le_two_mul_of_harmonic (x := R.x) (H := H) (i := i)
    (f := fun n => ‖absWindowSum (doorChiCoeff χ M) H n 0‖ ^ 2)
    (V := (H : ℝ) ^ 2 * MS H) hxH (fun n _ => by positivity) hladder
  simp only [absWindowSum_doorChiCoeff_zero] at hflat
  have heq : 2 * ((H : ℝ) ^ 2 * MS H) * (doorLadder R.x H (i + 1) : ℝ)
      = 2 * MS H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by ring
  rw [heq] at hflat
  exact hflat

/-- **⟦R1⟧, STATED** (`M4ChiMaximalStep`).  The one inequality between §6's fixed-length
block bound and §3's input: the sub-window sup's block mean square against the fixed-length
one, at a grade factor `Cmax`.  A dyadic decomposition of the partial sums gives
`Cmax ≈ (log H)²`, which the exponent gap absorbs; the trivial route
`sup² ≤ ∑_{K ≤ H}` gives `Cmax = H + 1` and is fatal.  Named here so the S11 spine's
consumption list carries it explicitly rather than by implication. -/
def M4ChiMaximalStep (R : ChowlaRegime) (M k : ℕ) (Cmax : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (doorChiSup χ M H n) ^ 2
        ≤ Cmax H
          * ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
              ‖∑ m ∈ doorSievedWindow M H n, liouChi χ m‖ ^ 2

/-- **THE χ-DATUM, ASSEMBLED** (`m4_chiBlockMeanSq_of_row`).  §6's bridge composed with
⟦R1⟧: the wave's analytic item at the grade `Cmax H·2·MS H`, from the capstone's own
currency.  Every step between `ThmA2.thm_a2'_of_rows` and `M4ChiBlockMeanSq` is now either
landed or one of the three named residues. -/
theorem m4_chiBlockMeanSq_of_row {R : ChowlaRegime} {M k : ℕ} {MS Cmax : ℕ → ℝ}
    (hCmax0 : ∀ H : ℕ, 0 ≤ Cmax H) (hmax : M4ChiMaximalStep R M k Cmax)
    (hrow : M4ChiRowMeanSq R M k MS) :
    M4ChiBlockMeanSq R M k (fun H => Cmax H * (2 * MS H)) := by
  intro H hlo hhi q hq hqQ i hik χ
  refine le_trans (hmax H hlo hhi q hq hqQ i hik χ) ?_
  have hb := m4_chiBlock_fixed_of_chiRow hrow H hlo hhi q hq hqQ i hik χ
  have hle := mul_le_mul_of_nonneg_left hb (hCmax0 H)
  refine le_trans hle (le_of_eq ?_)
  ring

/-- **THE CLOSE AT THE CAPSTONE'S OWN CURRENCY** (`m4_wave_closed_of_row`) — `m4_wave_closed`
with class (c) read all the way down to `M4ChiRowMeanSq`, the per-character block mean square
in `ThmA2.thm_a2'_of_rows`' currency.

⟦THE S11 CONSUMPTION LIST, final form⟧ — the hypotheses below, and nothing else:

* **(a) regime/scale** — `M4DoorGates` (witness `M4Door.doorCount_gates`), the `q`-graded
  drift price, the budget line `√Braw ≤ mrtDeliveredGrade (C/2)` (⟦U3⟧), the door's own two
  grades;
* **(b) data** — the three nonnegativity slots and `0 ≤ C`;
* **(c) the analytic residue, in THREE named pieces** —
  ⟦R1⟧ `M4ChiMaximalStep` (the sub-window sup against the fixed length),
  ⟦R2⟧ `hnoncop` (the non-coprime classes, whose transport is one loss-free dilation),
  ⟦R3⟧ `M4ChiRowMeanSq` (the capstone at the door's sieved, χ-twisted, un-phased datum).

Every other link of the M4/S9 chain — the arc, the budget head, the collision, the sieve
insert, the residue split, the phase removal, the character expansion, the class assembly,
the harmonic cover, the `log ω` absorption, the `L²→L¹` descent, the block exchange and the
grade gate — is landed and consumed. -/
theorem m4_wave_closed_of_row :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw MS Cmax : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ MS H) → (∀ H : ℕ, 0 ≤ Cmax H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * (Cmax H * (2 * MS H)))) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ChiMaximalStep R M k Cmax →
            M4ChiRowMeanSq R M k MS →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff M) H n q r) ^ 2
                  ≤ (Cmax H * (2 * MS H)) * (H : ℝ) ^ 2
                      * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_chi
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw MS Cmax M k hgates hMS0 hCmax0 hBraw0 hdrift hdel
    hrest hmax hrow hnoncop => ?_⟩
  refine hR δ Braw (fun H => Cmax H * (2 * MS H)) M k hgates
    (fun H => by have := hMS0 H; have := hCmax0 H; positivity) hBraw0 hdrift hdel hrest
    (m4_chiBlockMeanSq_of_row hCmax0 hmax hrow) hnoncop

/-! ## §GK — the G-lever twin

The additive `_gk` family at `G := s13GK K M` (`GLever`): each declaration is its landed
sibling with `(K : ℕ)` inserted as the FIRST binder and every literal `3072 * M` rewritten to
`s13GK K M`.

⟦THE FORCED α-RENAMINGS⟧ three landed statements already bind a variable named `K` — the
SUB-WINDOW LENGTH (`doorSievedWindow`, `doorChiSup`, `le_doorChiSup`) and the band constant
`K : ℝ` (`m4_rawMS_priced_decay`).  The lever's binder takes that name by the kdesign's
uniform convention, so those landed binders are α-renamed (`Kw` for the window length, `Kb`
for the band constant).  The statements are alpha-equivalent; nothing else moves.

The class machinery of §1 (`classSup`, `subWindowSup_le_sum_classSup`,
`sq_inv_totient_sum_le_sum_sq`, `classSup_le_of_norm_le_one`) is datum-abstract and is
re-instantiated at the lever's datum, never twinned. -/

/-- **THE ANALYTIC ITEM AT THE LEVER** — `M4ClassBlockMeanSq` (:198). -/
def M4ClassBlockMeanSq_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ r, r < q →
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
        ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE ANTI-VACUITY WITNESS AT THE LEVER** — `m4_classBlockMeanSq_trivial` (:210). -/
theorem m4_classBlockMeanSq_trivial_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) :
    M4ClassBlockMeanSq_gk K R M k (fun _ => 1) := by
  intro H _ hhi q _ _ i _ r _
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hterm : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2 ≤ (H : ℝ) ^ 2 := by
    intro n _
    have h := classSup_le_of_norm_le_one (norm_doorSievedCoeff_le_one_gk K M) H n q r
    have h0 := classSup_nonneg (doorSievedCoeff_gk K M) H n q r
    nlinarith
  have hsum : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
      ≤ ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
        * (H : ℝ) ^ 2 := by
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
        ≤ ∑ _n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i), (H : ℝ) ^ 2 :=
          Finset.sum_le_sum hterm
      _ = ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
            * (H : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
      ≤ (doorLadder R.x H (i + 1) : ℝ) := by
    rw [Nat.card_Ioc]
    have hfit := doorLadder_fit R.x H i
    have hn : doorLadder R.x H i - doorLadder R.x H (i + 1) ≤ doorLadder R.x H (i + 1) := by
      omega
    exact_mod_cast hn
  have hpos := doorLadder_pos hxH (i + 1)
  nlinarith

/-- **THE ASSEMBLY AT THE LEVER** — `m4_blockMeanSqSupQ_of_classMeanSq` (:256). -/
theorem m4_blockMeanSqSupQ_of_classMeanSq_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ}
    {Bcl : ℕ → ℝ}
    (hcl : M4ClassBlockMeanSq_gk K R M k Bcl) : M4BlockMeanSqSupQ_gk K R M k Bcl := by
  intro H hlo hhi b q hq hqQ i hik
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  -- ⟦pointwise: the split, then Chebyshev⟧
  have hpt : ∀ n : ℕ,
      (subWindowSup (doorSievedCoeff_gk K M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (q : ℝ) * ∑ r ∈ Finset.range q,
            (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2 := by
    intro n
    have hsplit := subWindowSup_le_sum_classSup (doorSievedCoeff_gk K M) H n hq b
    have h0 := subWindowSup_nonneg (doorSievedCoeff_gk K M) H n ((b : ℝ) / (q : ℝ))
    have hsq : (subWindowSup (doorSievedCoeff_gk K M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (∑ r ∈ Finset.range q, classSup (doorSievedCoeff_gk K M) H n q r) ^ 2 := by
      nlinarith
    refine hsq.trans ?_
    have hcheb := sq_sum_le_card_mul_sum_sq
      (s := Finset.range q) (f := fun r => classSup (doorSievedCoeff_gk K M) H n q r)
    rwa [Finset.card_range] at hcheb
  -- ⟦the block sum⟧
  have hstep1 : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (subWindowSup (doorSievedCoeff_gk K M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (q : ℝ) * ∑ r ∈ Finset.range q,
            (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (q : ℝ) * ∑ r ∈ Finset.range q, (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
      = (q : ℝ) * ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  have hper : ∑ r ∈ Finset.range q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
      ≤ (q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) := by
    calc ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
        ≤ ∑ _r ∈ Finset.range q,
            (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) :=
          Finset.sum_le_sum fun r hr =>
            hcl H hlo hhi q hq hqQ i hik r (Finset.mem_range.mp hr)
      _ = (q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (subWindowSup (doorSievedCoeff_gk K M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ (q : ℝ) * ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2 := by rw [← hswap]; exact hstep1
    _ ≤ (q : ℝ) * ((q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ))) :=
        mul_le_mul_of_nonneg_left hper hq0
    _ = Bcl H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by ring

/-- **THE SOCKET EXIT AT THE LEVER** — `m4_sievedDoorSq_of_classMeanSq` (:318). -/
theorem m4_sievedDoorSq_of_classMeanSq_gk (K : ℕ) {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ}
    {δ : ℝ} {Bcl Braw : ℕ → ℝ}
    (hgates : M4DoorGates_gk K Cg R M k δ) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hdrift : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
        ≤ Braw H)
    (hcl : M4ClassBlockMeanSq_gk K R M k Bcl) :
    M4SievedDoorSq_gk K R M Braw :=
  m4_sievedDoorSq_of_sup_gk K hdrift
    (m4_cover_assembly_supQ_gk K hgates hBcl0 (m4_blockMeanSqSupQ_of_classMeanSq_gk K hcl))

/-- **THE DOOR'S SIEVED WINDOW AT THE LEVER** — `doorSievedWindow` (:364), with the
sub-window binder α-renamed `K ↦ Kw`.  THE SIEVE SET GENUINELY MOVES: `𝒫`, `𝒬` grow with the
lever, so this is a different `Finset`. -/
def doorSievedWindow_gk (K M Kw n : ℕ) : Finset ℕ :=
  sievedWindow (MemS (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) 2) Kw n

/-- **THE χ-TWISTED SUP AT THE LEVER** — `doorChiSup` (:369). -/
def doorChiSup_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) : ℝ :=
  (Finset.Icc 0 H).sup' ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le H⟩⟩
    (fun Kw => ‖∑ m ∈ doorSievedWindow_gk K M Kw n, liouChi χ m‖)

theorem le_doorChiSup_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) {Kw : ℕ}
    (hK : Kw ≤ H) :
    ‖∑ m ∈ doorSievedWindow_gk K M Kw n, liouChi χ m‖ ≤ doorChiSup_gk K χ M H n :=
  Finset.le_sup' (f := fun Kw => ‖∑ m ∈ doorSievedWindow_gk K M Kw n, liouChi χ m‖)
    (Finset.mem_Icc.mpr ⟨Nat.zero_le Kw, hK⟩)

theorem doorChiSup_nonneg_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) :
    0 ≤ doorChiSup_gk K χ M H n :=
  le_trans (norm_nonneg _) (le_doorChiSup_gk K χ M H n (Nat.zero_le H))

/-- **THE χ-UNIFORM BLOCK MEAN SQUARE AT THE LEVER** — `M4ChiBlockMeanSq` (:384). -/
def M4ChiBlockMeanSq_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (doorChiSup_gk K χ M H n) ^ 2
        ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE POINTWISE HALF AT THE LEVER** — `classSup_le_inv_totient_sum_doorChiSup`
(:395). -/
theorem classSup_le_inv_totient_sum_doorChiSup_gk (K : ℕ) {q : ℕ} [NeZero q] {r : ℕ}
    (hcop : Nat.Coprime q r) (M H n : ℕ) :
    classSup (doorSievedCoeff_gk K M) H n q r
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup_gk K χ M H n := by
  refine classSup_le fun Kw hKw => ?_
  have hfilt : ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_gk K M m
      = ∑ m ∈ residueClassOn q r (doorSievedWindow_gk K M Kw n), liouvilleC m := by
    simpa only [doorSievedCoeff_gk, doorSievedWindow_gk] using
      sum_windowClass_memSCoeff (calP (Adoor M) (s13GK K M))
        (calQK (Adoor M) (s13GK K M) M) 2 liouvilleC Kw n q r
  rw [hfilt]
  refine le_trans (norm_sum_residueClassOn_liou_le hcop (doorSievedWindow_gk K M Kw n)) ?_
  have hφ : (0 : ℝ) < (q.totient : ℝ) := totient_cast_pos q
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum fun χ _ => le_doorChiSup_gk K χ M H n hKw

/-- **THE χ-REDUCTION AT THE LEVER** — `m4_classMeanSq_of_chiMeanSq` (:416). -/
theorem m4_classMeanSq_of_chiMeanSq_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hchi : M4ChiBlockMeanSq_gk K R M k Bcl) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ r, r < q → Nat.Coprime q r →
        ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
          ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by
  intro H hlo hhi q hq hqQ i hik r _ hcop
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦pointwise: the χ-average, squared⟧
  have hpt : ∀ n : ℕ, (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_gk K χ M H n) ^ 2 := by
    intro n
    have hle := classSup_le_inv_totient_sum_doorChiSup_gk K hcop M H n
    have h0 := classSup_nonneg (doorSievedCoeff_gk K M) H n q r
    have hsq : (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
        ≤ ((q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup_gk K χ M H n) ^ 2 := by
      nlinarith
    exact hsq.trans (sq_inv_totient_sum_le_sum_sq (fun χ => doorChiSup_gk K χ M H n))
  -- ⟦the block sum, then the χ-average and the `n`-sum commute⟧
  have hstep1 : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_gk K χ M H n) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_gk K χ M H n) ^ 2
      = (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (doorChiSup_gk K χ M H n) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hswap] at hstep1
  refine hstep1.trans ?_
  exact inv_totient_sum_le (fun χ => hchi H hlo hhi q hq hqQ i hik χ)

/-- **THE FIVE SUMMANDS, PRICED, AT THE LEVER** — `m4_rawMS_priced_decay` (:464), with the
band-constant binder α-renamed `K ↦ Kb`. -/
theorem m4_rawMS_priced_decay_gk (K : ℕ) {X C₁ Kb h G : ℝ} {q M : ℕ} (hX : 0 < Real.log X)
    (g1 : m4DecayGrade Kb q X C₁ ≤ G / 5)
    (g2 : 1787702400 * a2Level1 M ≤ G / 5)
    (g3 : 188133 * (Real.log X) ^ (-(1 : ℝ) / 500) ≤ G / 5)
    (g4 : 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) ≤ G / 5)
    (g5 : 6315000 / h ≤ G / 5) :
    m4RawMS_gk K (cfbC₁ X C₁) (cfbM0 Kb q X) M X h ≤ G := by
  have hdec : 8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * cfbM0 Kb q X)
      = m4DecayGrade Kb q X C₁ := m4_decay_summand_eq hX
  unfold m4RawMS_gk
  rw [hdec]
  linarith

/-- **THE M4 WAVE'S CLOSED THEOREM AT THE LEVER** — `m4_wave_closed` (:525). -/
theorem m4_wave_closed_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ClassBlockMeanSq_gk K R M k Bcl →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_gk K
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hcl => ?_⟩
  exact hR δ Braw M k hgates hBraw0 (m4_gradeGate_direct hdel hrest)
    (m4_sievedDoorSq_of_classMeanSq_gk K hgates hBcl0 hdrift hcl)

/-- **The close's collision form at the lever** — `m4_wave_closed_False` (:552). -/
theorem m4_wave_closed_False_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ClassBlockMeanSq_gk K R M k Bcl →
              logChowla2Fails R.eps R.x R.ω → False := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_False_of_live_gk K
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hcl => ?_⟩
  exact hR δ Braw M k hgates hBraw0 (m4_gradeGate_direct hdel hrest)
    (m4_sievedDoorSq_of_classMeanSq_gk K hgates hBcl0 hdrift hcl)

/-- **THE CLOSE AT THE χ-UNIFORM DATUM, AT THE LEVER** — `m4_wave_closed_of_chi` (:583). -/
theorem m4_wave_closed_of_chi_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ChiBlockMeanSq_gk K R M k Bcl →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
                  ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_gk K
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hchi hnoncop => ?_⟩
  refine hR δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest ?_
  intro H hlo hhi q hq hqQ i hik r hr
  by_cases hcop : Nat.Coprime q r
  · exact m4_classMeanSq_of_chiMeanSq_gk K hchi H hlo hhi q hq hqQ i hik r hr hcop
  · exact hnoncop H hlo hhi q hq hqQ i hik r hr hcop

/-- **THE M4 WAVE'S CLOSED THEOREM, SPLIT, AT THE LEVER** — `m4_wave_closed_split`
(:635). -/
theorem m4_wave_closed_split_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.sqrt (Braw H) ≤ δ₀ / 2) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 2) →
            M4ClassBlockMeanSq_gk K R M k Bcl →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_split_gk K
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hcl => ?_⟩
  exact hR δ Braw M k hgates hBraw0 (m4_gradeGate_direct_split hdel hrest)
    (m4_sievedDoorSq_of_classMeanSq_gk K hgates hBcl0 hdrift hcl)

/-- **THE CLOSE AT THE χ-UNIFORM DATUM, SPLIT, AT THE LEVER** — `m4_wave_closed_of_chi_split`
(:663). -/
theorem m4_wave_closed_of_chi_split_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.sqrt (Braw H) ≤ δ₀ / 2) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 2) →
            M4ChiBlockMeanSq_gk K R M k Bcl →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
                  ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_split_gk K
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hchi hnoncop => ?_⟩
  refine hR δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest ?_
  intro H hlo hhi q hq hqQ i hik r hr
  by_cases hcop : Nat.Coprime q r
  · exact m4_classMeanSq_of_chiMeanSq_gk K hchi H hlo hhi q hq hqQ i hik r hr hcop
  · exact hnoncop H hlo hhi q hq hqQ i hik r hr hcop

/-- **THE SIEVED, χ-TWISTED DATUM AT THE LEVER** — `doorChiCoeff` (:708). -/
def doorChiCoeff_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) : ℕ → ℂ :=
  memSCoeff (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) 2 (liouChi χ)

/-- The indicator-restricted window sum IS the sum over the levered sieved window —
`absWindowSum_doorChiCoeff_zero` (:712). -/
theorem absWindowSum_doorChiCoeff_zero_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M H n : ℕ) :
    absWindowSum (doorChiCoeff_gk K χ M) H n 0
      = ∑ m ∈ doorSievedWindow_gk K M H n, liouChi χ m := by
  rw [absWindowSum_zero, doorSievedWindow_gk, sievedWindow, Finset.sum_filter]
  rfl

/-- **THE ROW INPUT, PER CHARACTER, AT THE LEVER** — `M4ChiRowMeanSq` (:726). -/
def M4ChiRowMeanSq_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
      1 / (doorLadder R.x H (i + 1) : ℝ)
          * (∫ y in (doorLadder R.x H (i + 1) : ℝ)..(2 * (doorLadder R.x H (i + 1) : ℝ)),
              ‖((1 / (H : ℝ) : ℝ) : ℂ)
                  * shortSum (doorChiCoeff_gk K χ M)
                      (seamS0 (2 * doorLadder R.x H (i + 1))
                        (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
        ≤ MS H

/-- **THE ROW BRIDGE AT THE LEVER** — `m4_chiBlock_fixed_of_chiRow` (:748). -/
theorem m4_chiBlock_fixed_of_chiRow_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℝ}
    (hrow : M4ChiRowMeanSq_gk K R M k MS) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
        ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            ‖∑ m ∈ doorSievedWindow_gk K M H n, liouChi χ m‖ ^ 2
          ≤ 2 * MS H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by
  intro H hlo hhi q hq hqQ i hik χ
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hfit := doorLadder_fit R.x H i
  -- ⟦the coverage datum is free at the block's own seam index set⟧
  have hcov : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      ∀ m ∈ Finset.Ioc n (n + H), m ∉ seamS0 (2 * doorLadder R.x H (i + 1))
          (doorLadder R.x H (i + 1) : ℝ) → doorChiCoeff_gk K χ M m = 0 :=
    hcov_of_seamS0 (doorChiCoeff_gk K χ M) (A := doorLadder R.x H (i + 1))
      (B := doorLadder R.x H i) (N := 2 * doorLadder R.x H (i + 1)) (H := H) le_rfl
      (by omega)
  -- ⟦the row datum, read at the removed phase⟧
  have hMS0 : 1 / ((doorLadder R.x H (i + 1) : ℕ) : ℝ)
      * (∫ y in ((doorLadder R.x H (i + 1) : ℕ) : ℝ)..(2
            * ((doorLadder R.x H (i + 1) : ℕ) : ℝ)),
          ‖((1 / (H : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff_gk K χ M) 0)
                  (seamS0 (2 * doorLadder R.x H (i + 1))
                    (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
      ≤ MS H := by
    rw [doorCoeffPhase_zero]
    exact hrow H hlo hhi q hq hqQ i hik χ
  -- ⟦B-4: the harmonic-weighted block bound⟧
  have hladder := sum_Ioc_absWindowSum_sq_div_le_ladder (doorChiCoeff_gk K χ M)
    (seamS0 (2 * doorLadder R.x H (i + 1)) (doorLadder R.x H (i + 1) : ℝ)) 0
    (x := R.x) (H := H) (i := i) (MS := MS H) hH0 hxH hcov hMS0
  -- ⟦the exchange⟧
  have hflat := sum_Ioc_le_two_mul_of_harmonic (x := R.x) (H := H) (i := i)
    (f := fun n => ‖absWindowSum (doorChiCoeff_gk K χ M) H n 0‖ ^ 2)
    (V := (H : ℝ) ^ 2 * MS H) hxH (fun n _ => by positivity) hladder
  simp only [absWindowSum_doorChiCoeff_zero_gk] at hflat
  have heq : 2 * ((H : ℝ) ^ 2 * MS H) * (doorLadder R.x H (i + 1) : ℝ)
      = 2 * MS H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by ring
  rw [heq] at hflat
  exact hflat

/-- **⟦R1⟧ AT THE LEVER** — `M4ChiMaximalStep` (:797). -/
def M4ChiMaximalStep_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (Cmax : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (doorChiSup_gk K χ M H n) ^ 2
        ≤ Cmax H
          * ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
              ‖∑ m ∈ doorSievedWindow_gk K M H n, liouChi χ m‖ ^ 2

/-- **THE χ-DATUM, ASSEMBLED, AT THE LEVER** — `m4_chiBlockMeanSq_of_row` (:810). -/
theorem m4_chiBlockMeanSq_of_row_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {MS Cmax : ℕ → ℝ}
    (hCmax0 : ∀ H : ℕ, 0 ≤ Cmax H) (hmax : M4ChiMaximalStep_gk K R M k Cmax)
    (hrow : M4ChiRowMeanSq_gk K R M k MS) :
    M4ChiBlockMeanSq_gk K R M k (fun H => Cmax H * (2 * MS H)) := by
  intro H hlo hhi q hq hqQ i hik χ
  refine le_trans (hmax H hlo hhi q hq hqQ i hik χ) ?_
  have hb := m4_chiBlock_fixed_of_chiRow_gk K hrow H hlo hhi q hq hqQ i hik χ
  have hle := mul_le_mul_of_nonneg_left hb (hCmax0 H)
  refine le_trans hle (le_of_eq ?_)
  ring

/-- **THE CLOSE AT THE CAPSTONE'S OWN CURRENCY, AT THE LEVER** — `m4_wave_closed_of_row`
(:840). -/
theorem m4_wave_closed_of_row_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw MS Cmax : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ MS H) → (∀ H : ℕ, 0 ≤ Cmax H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * (Cmax H * (2 * MS H)))) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ChiMaximalStep_gk K R M k Cmax →
            M4ChiRowMeanSq_gk K R M k MS →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
                  ≤ (Cmax H * (2 * MS H)) * (H : ℝ) ^ 2
                      * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_chi_gk K
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw MS Cmax M k hgates hMS0 hCmax0 hBraw0 hdrift hdel
    hrest hmax hrow hnoncop => ?_⟩
  refine hR δ Braw (fun H => Cmax H * (2 * MS H)) M k hgates
    (fun H => by have := hMS0 H; have := hCmax0 H; positivity) hBraw0 hdrift hdel hrest
    (m4_chiBlockMeanSq_of_row_gk K hCmax0 hmax hrow) hnoncop

-- #audit (temporary)

end Salt.MR

end
