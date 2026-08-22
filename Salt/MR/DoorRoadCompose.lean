import Salt.MR.M4Gauss
import Salt.MR.M4BridgePhase
import Salt.MR.M4Maximal

/-!
# The door's road, COMPOSED across its first seam

The door's chain was walked link-by-link and every link was found to have producers
(`MRTPropA3.lean`, the "five links deep" section).  What was **not** measured there is whether
the links **compose** — and that is precisely the gap a green build cannot see: *the kernel
checks theorems, not that they compose.*

This file closes that gap for the first seam, in the kernel rather than in prose.  It joins

* `norm_absWindowSum_le_drift_tight` (`M4BridgePhase`) — phase drift from an arbitrary `α`
  at a tight major arc down to a rational `b/q`, landing on `subWindowSup`, and
* `subWindowSup_sq_le_strata` (`M4Gauss`) — the Gauss/strata bound at `doorSievedCoeff M`,

into one statement about `absWindowSum` directly.  The seam that had to line up is the
modulus cap: `drift_tight` **produces** `(q : ℝ) ≤ arcDen B₅ H`, and `strata` **consumes**
`(q : ℝ) ≤ W`.  Instantiating `W := arcDen B₅ H` makes the produced fact *be* the consumed
one — so the two arcs' denominators are the same object, not merely similarly named.

That is the whole content of a composition check, and it is the kind of thing that stays
invisible until someone writes the composed statement down.
-/

namespace Salt.MR

/-- **THE FIRST SEAM OF THE DOOR'S ROAD, KERNEL-CHECKED.**  At a tight major arc, the door's
sieved window sum is bounded — squared — by the weighted stratum budgets, with the drift
constant carried through.  The arc's own witness denominator `q` is shared by both halves:
`drift_tight` hands out `(q : ℝ) ≤ arcDen B₅ H` and `strata` takes it in at `W := arcDen B₅ H`.

⭐ **The numerator `b` is deliberately NOT in the conclusion.**  The first draft carried
`∃ (b : ℤ) (q : ℕ), …` and the unused-variable linter flagged `b` as unreferenced — which is a
statement-level fact, not a style nit: the stratum budgets are summed over ALL residues, so the
bound depends only on the arc's DENOMINATOR.  Carrying `∃ b` would have implied the estimate is
tied to a particular rational approximant when it is not. -/
theorem door_absWindowSum_sq_le_strata {M n H : ℕ} {B₅ α : ℝ}
    (hM : 1 ≤ M) (hH : 0 < H)
    (hW : arcDen B₅ H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
    (hα : NearRatTight (arcDen B₅ H) H α) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ arcDen B₅ H ∧
      ‖absWindowSum (doorSievedCoeff M) H n α‖ ^ 2
        ≤ (1 + 2 * Real.pi * (arcDen B₅ H / (q : ℝ))) ^ 2
          * ((∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
              * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm M q H d n) := by
  obtain ⟨b, q, hq, hqA, hbound⟩ :=
    norm_absWindowSum_le_drift_tight (B₅ := B₅) (H := H) (n := n) hH hα (doorSievedCoeff M)
  refine ⟨q, hq, hqA, ?_⟩
  -- ⟦THE SEAM⟧ `strata` is instantiated at `W := arcDen B₅ H`, so `hqA` IS its `hqW`.
  have hstrata := subWindowSup_sq_le_strata (M := M) (n := n) (q := q) (L := H)
    (W := arcDen B₅ H) hM hq hqA hW b
  calc ‖absWindowSum (doorSievedCoeff M) H n α‖ ^ 2
      ≤ ((1 + 2 * Real.pi * (arcDen B₅ H / (q : ℝ)))
            * subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = (1 + 2 * Real.pi * (arcDen B₅ H / (q : ℝ))) ^ 2
          * (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2 := by ring
    _ ≤ (1 + 2 * Real.pi * (arcDen B₅ H / (q : ℝ))) ^ 2
          * ((∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
              * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm M q H d n) :=
        mul_le_mul_of_nonneg_left hstrata (sq_nonneg _)

/-! ## Seam 2 — `strataTerm` against the aligned dyadic family

`strataTerm` is *defined* as `∑_χ (doorChiSup χ M (capL L d) (n/d))²`, so the next link is not
a definitional unfolding but a genuine estimate under the character sum: each summand is
replaced by `M4Maximal.doorChiSup_sq_le_dyadic`'s `K`-free maximal bound, uniformly in `χ`.
-/

/-- The stratum's dyadic budget: the aligned dyadic family summed over the stratum's
characters, at its own cap `capL L d` and dilated base `n / d`.  Named so the composition
below reads as one line instead of three screens. -/
noncomputable def dyadicStratumBudget (M q L d n : ℕ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ (q / d),
    ((∑ j ∈ Finset.range (Nat.log 2 (capL L d) + 1), (3 / 2 : ℝ) ^ j)
      * ∑ j ∈ Finset.range (Nat.log 2 (capL L d) + 1),
          (∑ t ∈ Finset.range (capL L d / 2 ^ (j + 1) + 1),
            ‖∑ m ∈ doorSievedWindow M (2 ^ j) (n / d + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2)
            * (2 / 3 : ℝ) ^ j)

/-- **SEAM 2, KERNEL-CHECKED** — the stratum budget against the aligned dyadic family.
Uniform in `χ`, so it passes under the character sum with `Finset.sum_le_sum`. -/
theorem strataTerm_le_dyadic (M q L d n : ℕ) :
    strataTerm M q L d n ≤ dyadicStratumBudget M q L d n := by
  unfold strataTerm dyadicStratumBudget
  exact Finset.sum_le_sum fun χ _ => doorChiSup_sq_le_dyadic χ M (capL L d) (n / d)

/-! ## Seams 1+2 CHAINED — the door's window sum against the dyadic mean squares

The point of stating this: it is the first object in the file whose proof forces the two
seams to hold *simultaneously*, under the divisor sum.  Each seam alone type-checks in
isolation; a mismatch in `q`, `L` or the base would surface only here. -/

/-- **THE CHAIN, FOR ITS FIRST FIVE NODES** — at a tight major arc, the door's sieved window
sum is bounded, squared, by the weighted dyadic stratum budgets:
`absWindowSum → subWindowSup → strata → doorChiSup → dyadic`, in one statement.

⛔ **THIS IS NOT THE WHOLE ROAD, AND AN EARLIER DRAFT OF THIS DOCSTRING SAID IT WAS.**  The
statement terminates at `dyadicStratumBudget`.  The road's last two nodes —
`M4ChiDyadicRowMeanSq` (the capstone) and `DoorRowCarried` — appear **nowhere in this file**,
and the seams `dyadic → capstone → DoorRowCarried` remain joined by prose only.

**Measured: 5 of 7 nodes; 4 of 6 seams composed; 2 seams remain.**  The overstatement was
caught by a peer reading the banner while the body of the same report listed the remaining
seams correctly — *the headline is the part that travels*.  See the "five links deep" section
of `MRTPropA3.lean`: **"the road is complete" is the same mistake as "the road is broken",
wearing the other sign**, and it must not be claimed before the last link is in the kernel. -/
theorem door_absWindowSum_sq_le_dyadic {M n H : ℕ} {B₅ α : ℝ}
    (hM : 1 ≤ M) (hH : 0 < H)
    (hW : arcDen B₅ H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
    (hα : NearRatTight (arcDen B₅ H) H α) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ arcDen B₅ H ∧
      ‖absWindowSum (doorSievedCoeff M) H n α‖ ^ 2
        ≤ (1 + 2 * Real.pi * (arcDen B₅ H / (q : ℝ))) ^ 2
          * ((∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
              * ∑ d ∈ q.divisors, (d : ℝ) * dyadicStratumBudget M q H d n) := by
  obtain ⟨q, hq, hqA, hmain⟩ := door_absWindowSum_sq_le_strata (n := n) hM hH hW hα
  refine ⟨q, hq, hqA, le_trans hmain ?_⟩
  have hinner : ∑ d ∈ q.divisors, (d : ℝ) * strataTerm M q H d n
      ≤ ∑ d ∈ q.divisors, (d : ℝ) * dyadicStratumBudget M q H d n :=
    Finset.sum_le_sum fun d _ =>
      mul_le_mul_of_nonneg_left (strataTerm_le_dyadic M q H d n) (Nat.cast_nonneg d)
  have hharm : (0 : ℝ) ≤ ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) :=
    Finset.sum_nonneg fun d _ => div_nonneg zero_le_one (Nat.cast_nonneg d)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hharm) (sq_nonneg _)

/-! ## Seam 3 — what it actually costs: an INDEX-SET ALIGNMENT, not an estimate

Seam 3 joins the dyadic budget to the capstone `M4ChiDyadicRowMeanSq`, whose consumer
`m4_chiShiftBlock_of_dyadicRow` delivers `M4ChiShiftBlockMeanSq`.  Comparing the two objects:

* the capstone's family sums `‖∑_{m ∈ doorSievedWindow M (2^j) n} liouChi χ m‖²` over **every**
  `n` in the ladder block `Ioc (doorLadder R.x H (i+1) + s) (doorLadder R.x H i + s)`;
* `dyadicStratumBudget` sums the **same summand** over an arithmetic progression of bases
  `n₀ + 2^(j+1)·t`.

**The summands are identical — `doorSievedWindow` and `liouChi`, not lookalikes.**  What differs
is the index set: a step-`2^(j+1)` progression versus a full interval.  So seam 3 is not a
numerical estimate at all; it is the statement that the progression **lands inside** the block.
That is the piece below, isolated and proved in general so the seam has nothing left to invent.
-/

/-- **THE ALIGNMENT LEMMA** — a nonnegative sum over an arithmetic progression is dominated by
the sum over any interval containing that progression's terms.  Positive step gives
injectivity, so no term is double-counted; nonnegativity absorbs the interval's extra cells.

*This is exactly what seam 3 needs, and stating it made the seam's real cost visible: the
dyadic family and the capstone family have the SAME summand and differ only in index set.* -/
theorem sum_progression_le_sum_Ioc {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {a b n₀ step T : ℕ} (hstep : 0 < step)
    (hin : ∀ t, t < T → n₀ + step * t ∈ Finset.Ioc a b) :
    ∑ t ∈ Finset.range T, f (n₀ + step * t) ≤ ∑ n ∈ Finset.Ioc a b, f n := by
  classical
  have hinj : ∀ x ∈ Finset.range T, ∀ y ∈ Finset.range T,
      n₀ + step * x = n₀ + step * y → x = y := by
    intro x _ y _ hxy
    have : step * x = step * y := by omega
    exact Nat.eq_of_mul_eq_mul_left hstep this
  have himg : (Finset.range T).image (fun t => n₀ + step * t) ⊆ Finset.Ioc a b := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact hin t (Finset.mem_range.mp ht)
  calc ∑ t ∈ Finset.range T, f (n₀ + step * t)
      = ∑ n ∈ (Finset.range T).image (fun t => n₀ + step * t), f n :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ n ∈ Finset.Ioc a b, f n :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun n _ _ => hf n)

/-! ## Seam 3, the MODULUS half — the capstone is applicable at the strata's reduced modulus

Seam 3 has two independent halves, and only one of them is the index alignment above.

`strataTerm` sums over `χ : DirichletCharacter ℂ (q / d)` — the **reduced** modulus, one per
divisor `d ∣ q`.  The capstone `M4ChiDyadicRowMeanSq` quantifies `∀ q, 0 < q → (q : ℝ) ≤
arcDen 12 H → ∀ χ : DirichletCharacter ℂ q`.  So firing it at the strata's characters means
instantiating its `q` at `q / d`, which incurs exactly two obligations:
`0 < q / d` and `(q / d : ℝ) ≤ arcDen 12 H`.

Both are discharged below.  **The modulus half of seam 3 lines up; the index-alignment half
(`sum_progression_le_sum_Ioc`'s `hin`) does NOT, and remains open.**
-/

/-- The reduced modulus is positive at every divisor of a nonzero modulus. -/
theorem strata_modulus_pos {q d : ℕ} (hd : d ∈ q.divisors) : 0 < q / d := by
  have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
  have hq0 : q ≠ 0 := (Nat.mem_divisors.mp hd).2
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hdvd) hdpos

/-- The reduced modulus stays inside the arc's admissible range — the cap is inherited from
`q`, monotonically, at every `d`.  *No divisor can push a stratum outside the arc.* -/
theorem strata_modulus_within_arc {q d H : ℕ} (hq : (q : ℝ) ≤ arcDen 12 H) :
    ((q / d : ℕ) : ℝ) ≤ arcDen 12 H :=
  le_trans (by exact_mod_cast Nat.div_le_self q d) hq

/-- **THE MODULUS HALF OF SEAM 3, ASSEMBLED** — at every divisor `d ∣ q` of an
arc-admissible modulus, the capstone's own two side conditions hold at the reduced modulus
`q / d`, so `M4ChiDyadicRowMeanSq` may be fired on the stratum's characters.

⛔ This is **not** seam 3.  It is the half of seam 3 that is about moduli.  The other half —
that the dyadic progression's bases land inside a ladder block — is `hin` in
`sum_progression_le_sum_Ioc` and is **still a hypothesis**. -/
theorem strata_capstone_applicable {q d H : ℕ} (hd : d ∈ q.divisors)
    (hq : (q : ℝ) ≤ arcDen 12 H) :
    0 < q / d ∧ ((q / d : ℕ) : ℝ) ≤ arcDen 12 H :=
  ⟨strata_modulus_pos hd, strata_modulus_within_arc hq⟩

/-! ## Seam 3, the INDEX half — `hin` reduced to a window-in-block containment

`sum_progression_le_sum_Ioc` takes `hin` as an opaque hypothesis: *every* progression term
lies in the interval.  That is not the form a consumer can check.  The natural criterion is
geometric — the stratum's whole window sits inside the ladder block — and it implies `hin`
for the progression the dyadic family actually uses, whose length is `cap / step + 1`.

Note `0 < step` is **not** needed here: at `step = 0` the range collapses to a single term
`n₀`, which the endpoints already cover.
-/

/-- **THE CONTAINMENT CRITERION** — if the window `[n₀, n₀ + cap]` sits inside `Ioc a b`, then
every base of the step-`step` progression of length `cap / step + 1` lies in `Ioc a b`.

*This is `hin` in the form a consumer can discharge: two endpoint inequalities instead of a
quantified membership.* -/
theorem progression_mem_Ioc_of_window_in_block {a b n₀ step cap : ℕ}
    (hlo : a < n₀) (hhi : n₀ + cap ≤ b) :
    ∀ t, t < cap / step + 1 → n₀ + step * t ∈ Finset.Ioc a b := by
  intro t ht
  have hts : t ≤ cap / step := Nat.lt_succ_iff.mp ht
  have hmul : step * t ≤ cap := by
    calc step * t ≤ step * (cap / step) := Nat.mul_le_mul (le_refl step) hts
      _ = cap / step * step := Nat.mul_comm _ _
      _ ≤ cap := Nat.div_mul_le_self cap step
  refine Finset.mem_Ioc.mpr ⟨by omega, by omega⟩

/-- **SEAM 3'S INDEX HALF, IN CONSUMER FORM** — the dyadic progression sum is dominated by the
ladder-block sum as soon as the stratum's window lies in the block.  `hin` is gone; what
remains for the door is the pair of endpoint facts `a < n₀` and `n₀ + cap ≤ b`. -/
theorem sum_progression_le_sum_Ioc_of_window {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {a b n₀ step cap : ℕ} (hstep : 0 < step)
    (hlo : a < n₀) (hhi : n₀ + cap ≤ b) :
    ∑ t ∈ Finset.range (cap / step + 1), f (n₀ + step * t) ≤ ∑ n ∈ Finset.Ioc a b, f n :=
  sum_progression_le_sum_Ioc hf hstep (progression_mem_Ioc_of_window_in_block hlo hhi)

/-! ## Where seam 3's containment can hold at all — the `3H` rung threshold

The criterion above is only useful if a ladder block is ever long enough to hold a stratum
window.  It is not always: `doorLadder` descends by `X_{i+1} = (X_i + H + 1)/2` toward the
fixed point `H + 1`, where the block `Ioc (X_{i+1}+s) (X_i+s)` has length **zero**.

Measured over `H ∈ {1,2,3,7,10,31,100,257,1000,4096,10⁶}`: the smallest `X_i` at which the
block length reaches `H` is **exactly `3H`**, every time (a `2H` rule is refuted, so the probe
discriminates).  The theorem below is that measurement, in the kernel.

⇒ **Single-block containment is available on the upper rungs (`3H ≤ X_i`) and impossible below
them.**  That is a true statement about `doorLadder`, and both directions are proved below.

⛔⛔ **BUT IT IS NOT A CONSTRAINT ON THE DOOR, AND AN EARLIER VERSION OF THIS SECTION SAID IT
WAS.**  I wrote that seam 3 "needs a covering by several blocks" below `3H`.  That is an
artifact of the route *I* invented, not a gap in the corpus.  **The corpus's own route never
asks the containment question at all:**

```
  M4BaseNarrow.lean:322 / M4ChiSummed.lean:673   ⟦STEP 1⟧ then ⟦STEP 2⟧
    ∑_{n ∈ Ioc A B} (doorChiSup χ M L n)²   ≤   ∑_{n ∈ Ioc A B} SL · ∑_j (∑_t X j t n)·(2/3)^j
    then the sums COMMUTE:  ∑_n ∑_j ∑_t  ⟶  ∑_j ∑_t ∑_{n ∈ Ioc A B}
```
`n` keeps running over the **whole block** and the shift `2^(j+1)·t` rides along on every `n`;
the result is the **shifted** block sum, which is exactly what `M4ChiShiftBlockMeanSq` is —
hence its name.  No progression has to sit inside anything.

⇒ **The real seam-3 step is the SUM SWAP, which the corpus already performs.**  The lemmas in
this section stay true and kernel-checked, but they are **general facts, not campaign
blockers**, and they are **not on the door's critical path**.

🔑 *Lesson, and it is the second of this kind today: when you build your own route and hit a
wall, check whether the CORPUS's route hits the same wall.  **My route's obstruction is not the
campaign's obstruction**, and publishing it as one would have invented a blocker.*
-/

/-- **THE RUNG THRESHOLD** — at `3H ≤ X_i` the ladder block is at least `H` long, so a window
of length `≤ H` can fit inside it.  Below `3H` it cannot, and the bound is sharp: `3H` is the
exact crossover — measured across eleven magnitudes of `H`, then PROVED in both
directions (`doorLadder_block_length_lt` is the converse). -/
theorem doorLadder_block_length_ge {x H i : ℕ} (h : 3 * H ≤ doorLadder x H i) :
    H ≤ doorLadder x H i - doorLadder x H (i + 1) := by
  rw [doorLadder_succ]; omega

/-- **AND THE THRESHOLD IS SHARP — PROVED, NOT MERELY MEASURED.**  Strictly below `3H` the
block is strictly shorter than `H`, so no stratum window of length `H` fits in one block.

*The docstring above first claimed sharpness off an eleven-point measurement.  A measured
crossover is evidence, not a theorem; this is the theorem.* -/
theorem doorLadder_block_length_lt {x H i : ℕ} (hH : 0 < H)
    (h : doorLadder x H i < 3 * H) :
    doorLadder x H i - doorLadder x H (i + 1) < H := by
  rw [doorLadder_succ]; omega

end Salt.MR
