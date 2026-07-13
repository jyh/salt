/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.StepBound2
import Salt.Chen.Hyp4

/-!
# C1c⁷ — the Stieltjes summation-by-parts core of the BJS (34)–(38) `hstep'` comparison

This file supplies the **discrete integration-by-parts machinery** that BJS's partial
summation (their (34)–(38)) runs on: the recognition of the peel weight `ν(p)·V(p)` as a
telescoping increment of the descending `V`-measure, the resulting Stieltjes tail-mass
identities, the algebraic decomposition of `StepBound2.StepHyp`'s left side into that
Stieltjes form, and the parametric ε-ledger collect that fixes the τ-recursion direction.

## What the peel sum IS (the design that C1c⁶ made statable)

`StepHyp σ ε τ` demands, for every sieve `s'`, cutoff `z`, side, level `D'`, depth `n`:

  `Σ_{p ∈ window} ν(p)·fseqBound' σ ε τ (sieveBelow s' p) p (3−side) (⌈D'/p⌉) n`
      `≤ fseqBound' σ ε τ s' z side D' (n+1)`.

Unfolding `fseqBound'` and `W_sieveBelow` (`W (sieveBelow s' p) = Vbelow s' p = V(p)`), the
left side is the **Riemann–Stieltjes sum**

  `Σ_{p ∈ window} ν(p)·V(p)·g(p)`,   `g(p) = fₙ(σ p ⌈D'/p⌉) + ε·τₙ·e²·h(σ p ⌈D'/p⌉)`

against the *descending* density `V(p) = ∏_{q < p}(1−ν q)`.  The key algebraic fact
(`Lemma11.prod_telescope`) is that the increments telescope:

  `ν(pᵢ)·V(pᵢ) = V(pᵢ) − V(pᵢ₊₁)`   (the next prime up),

so the partial masses `Σ_{p ≥ t} ν(p)·V(p) = V(t) − W` are the Stieltjes measure of the
descending `V`.  This file proves those masses in general (`telescope_lt`, `telescope_ge`)
and in the two concrete peel windows (`telescope_window_upper` = `1 − V(D^{1/3})`,
`telescope_window_lower` = `1 − W`), decomposes `StepHyp`'s left side into the Stieltjes
form (`stepHyp_lhs_eq`), records the crude one-sided Stieltjes bound (`stieltjes_sum_le_of_le`),
and closes the ε-ledger collect parametrically (`ledger_collect`).

## The τ-direction resolution (worked out; `ledger_collect`)

`StepHyp σ ε τ` fixes `τ` and demands the inequality for *every* `n`.  Writing the two-part
Stieltjes comparison as `f`-part `≤ W·(fₙ₊₁ + c_f·h)` and `h`-part `≤ W·(c_h·h)` at the parent
operating point (the `(35)–(38)` split with error coefficients `c_f, c_h`), the collect
`f-part + ε·τₙ·e²·(h-part) ≤ W·(fₙ₊₁ + ε·τₙ₊₁·e²·h)` closes **iff**

  `c_f + ε·e²·c_h·τₙ ≤ ε·e²·τₙ₊₁`,   i.e.   `τₙ₊₁ ≥ c_f/(ε e²) + c_h·τₙ`,

which is exactly BJS's `τₙ₊₁ = a·rⁿ + β·τₙ`-recursion **in the ≥ direction** (`a = c_f/(εe²)`,
`β = c_h`).  Crucially this per-`n` inequality closes *regardless of whether `β = c_h < 1`*:
`β < 1` bites only at the τ-**sum** close (`htau : Στ ≤ Cᵢ`, `Lemma11.tau_sum_le_of_recursion`),
which is already parametric per the C0 ledger (the C1c⁵ κ₃ = 1 finding).  So the honest state
is: `StepHyp` follows from the two sharp Stieltjes comparisons plus a τ satisfying `hτrec`
(this direction), and the numeric contraction is deferred to `htau` exactly as before.

## FLOOR reached (honest; precise flag in `docs/blueprints/flags.md`)

**Floor C+ (the reusable Stieltjes summation-by-parts core), NOT the full `hstep'`.**  The one
piece this file does **not** discharge is the *sharp* discrete→integral comparison — the change
of variables `t = log D'/log p ↦ σ p ⌈D'/p⌉ = t − 1`, the pushforward of the descending
`V`-measure onto Lebesgue-against-`(1+ε)/log`-density via hypothesis (4)
(`Hyp4.vratio_window_le`), and the monotone-piece comparison of the Stieltjes sum to the exact
`fseq`-recursion integral (`RosserChain` (16)/(17)).  That step produces the sharp `c_f, c_h`
of the ledger above; it is genuine multi-hundred-line real analysis (BJS §2.4, several pages),
sized by two prior executors as "its own session", and is NOT attempted here — no `sorry`, no
crude bound masquerading as the sharp one.  What *is* landed is every piece surrounding it:
the telescoping/Stieltjes measure structure (general and in situ), the `StepHyp` left-side
decomposition, and the ε/τ ledger collect.  The named remaining hypothesis is the sharp
comparison; `ledger_collect` shows precisely how it composes to `StepHyp`.
-/

open Finset

namespace Salt.Chen

/-! ## Part A — the Stieltjes telescoping core (general `Finset ℕ`)

`Lemma11.prod_telescope` gives the *total* increment mass `Σ_{p∈S} a(p)·∏_{q<p}(1−a q) =
1 − ∏_S(1−a)`.  Here we split it at a threshold `t`: the low part telescopes to `1 − V(t)`
and the tail part to `V(t) − W` — the descending-`V` Stieltjes measure of `[t, ∞)`. -/

/-- Nested `< t` then `< p` filter collapses to `< p` when `p ≤ t` (`q < p ≤ t ⟹ q < t`). -/
lemma filter_lt_filter_lt {S : Finset ℕ} {p t : ℕ} (hpt : p ≤ t) :
    (S.filter (· < t)).filter (· < p) = S.filter (· < p) := by
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hq, _⟩, hqp⟩; exact ⟨hq, hqp⟩
  · rintro ⟨hq, hqp⟩; exact ⟨⟨hq, by omega⟩, hqp⟩

/-- **Low telescoping.**  Summing the increments over `{p ∈ S : p < t}` telescopes to
`1 − V(t)`, `V(t) = ∏_{q ∈ S, q < t}(1 − a q)`.  (The increments there use the *full*-`S`
partial products `∏_{q ∈ S, q < p}`, which for `p < t` equal the `{· < t}`-restricted ones.) -/
theorem telescope_lt (S : Finset ℕ) (a : ℕ → ℝ) (t : ℕ) :
    ∑ p ∈ S.filter (· < t), a p * ∏ q ∈ S.filter (· < p), (1 - a q)
      = 1 - ∏ q ∈ S.filter (· < t), (1 - a q) := by
  rw [← prod_telescope (S.filter (· < t)) a]
  apply Finset.sum_congr rfl
  intro p hp
  have hpt : p < t := (Finset.mem_filter.mp hp).2
  rw [filter_lt_filter_lt (le_of_lt hpt)]

/-- **Tail telescoping (the descending-`V` Stieltjes mass).**  Summing the increments over
`{p ∈ S : t ≤ p}` gives `V(t) − W` — the mass the descending `V`-measure assigns to `[t, ∞)`.
This is the discrete integration-by-parts kernel of BJS's partial summation. -/
theorem telescope_ge (S : Finset ℕ) (a : ℕ → ℝ) (t : ℕ) :
    ∑ p ∈ S.filter (t ≤ ·), a p * ∏ q ∈ S.filter (· < p), (1 - a q)
      = (∏ q ∈ S.filter (· < t), (1 - a q)) - ∏ p ∈ S, (1 - a p) := by
  have hfull := prod_telescope S a
  have hlow := telescope_lt S a t
  have hnot : S.filter (fun p => ¬ p < t) = S.filter (t ≤ ·) := by
    ext q; simp only [Finset.mem_filter, not_lt]
  have hsplit : ∑ p ∈ S, a p * ∏ q ∈ S.filter (· < p), (1 - a q)
      = (∑ p ∈ S.filter (· < t), a p * ∏ q ∈ S.filter (· < p), (1 - a q))
        + ∑ p ∈ S.filter (t ≤ ·), a p * ∏ q ∈ S.filter (· < p), (1 - a q) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (· < t)
      (fun p => a p * ∏ q ∈ S.filter (· < p), (1 - a q)), hnot]
  linarith [hfull, hlow, hsplit]

/-! ## Part B — the crude one-sided Stieltjes bound (reusable)

`Σ_{p∈S} incr(p)·g(p) ≤ M·(1 − ∏_S(1−a))` when `g ≤ M` and the increments are nonnegative.
The crude majorant `M·mass` that the sharp comparison must *beat* — recorded because the
`h`-part slack ledger uses it as the trivial fallback, and because it is the honest witness
that no *uniform* crude bound can discharge `StepHyp` (the mass `1 − ∏` has no uniform ratio
to the target `W·fₙ₊₁`; see the flag). -/
theorem stieltjes_sum_le_of_le {S : Finset ℕ} {a g : ℕ → ℝ} {M : ℝ}
    (ha0 : ∀ p ∈ S, 0 ≤ a p) (ha1 : ∀ p ∈ S, a p ≤ 1)
    (hgM : ∀ p ∈ S, g p ≤ M) :
    ∑ p ∈ S, (a p * ∏ q ∈ S.filter (· < p), (1 - a q)) * g p
      ≤ M * (1 - ∏ p ∈ S, (1 - a p)) := by
  have hincr : ∀ p ∈ S, 0 ≤ a p * ∏ q ∈ S.filter (· < p), (1 - a q) := by
    intro p hp
    refine mul_nonneg (ha0 p hp) (Finset.prod_nonneg (fun q hq => ?_))
    have hqS : q ∈ S := (Finset.mem_filter.mp hq).1
    linarith [ha1 q hqS]
  calc ∑ p ∈ S, (a p * ∏ q ∈ S.filter (· < p), (1 - a q)) * g p
      ≤ ∑ p ∈ S, (a p * ∏ q ∈ S.filter (· < p), (1 - a q)) * M :=
        Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hgM p hp) (hincr p hp))
    _ = (∑ p ∈ S, a p * ∏ q ∈ S.filter (· < p), (1 - a q)) * M := by rw [← Finset.sum_mul]
    _ = (1 - ∏ p ∈ S, (1 - a p)) * M := by rw [prod_telescope]
    _ = M * (1 - ∏ p ∈ S, (1 - a p)) := by ring

/-! ## Part C — `StepHyp`'s left side is the Stieltjes sum `Σ ν(p)·V(p)·g(p)`

`stepHyp_lhs_eq` unfolds `fseqBound' … (sieveBelow s' p) p …` and `W_sieveBelow`
(`W (sieveBelow s' p) = Vbelow s' p`) to exhibit the peel sum as the descending-`V` Stieltjes
sum.  `telescope_window_{upper,lower}` then give the total Stieltjes mass in each concrete
window (`1 − V(D^{1/3})` on the odd/upper side, `1 − W` on the even/lower side). -/

/-- **The `StepHyp` left-side decomposition.**  The peel sum equals the Stieltjes sum
`Σ_{p ∈ window} (ν(p)·V(p))·g(p)` with `V(p) = Vbelow s' p` and
`g(p) = fₙ(σ p ⌈D'/p⌉) + ε·τₙ·e²·h(σ p ⌈D'/p⌉)`. -/
theorem stepHyp_lhs_eq (σ : ℕ → ℕ → ℝ) (ε : ℝ) (tau : ℕ → ℝ)
    (s' : BoundingSieve) (side' D' n : ℕ) :
    (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
        s'.nu p * fseqBound' σ ε tau (sieveBelow s' p) p (3 - side') (cdiv D' p) n)
      = ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
          (s'.nu p * Vbelow s' p)
            * (fseq n (σ p (cdiv D' p))
                + ε * tau n * Real.exp 2 * hBJS (σ p (cdiv D' p))) := by
  apply Finset.sum_congr rfl
  intro p _
  simp only [fseqBound', W_sieveBelow]
  ring

/-- **Total Stieltjes mass, odd/upper window** (`window = {p : p³ < D'}`):
`Σ ν(p)·V(p) = 1 − V(D^{1/3})`.  The `q < p` primes of a window prime `p` are themselves in
the window (`q³ < p³ < D'`), so the increments telescope over the window. -/
theorem telescope_window_upper (s' : BoundingSieve) (D' : ℕ) :
    ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D'), s'.nu p * Vbelow s' p
      = 1 - Vlow s' D' := by
  have hwin : ∀ p ∈ s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D'),
      (s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D')).filter (· < p)
        = s'.prodPrimes.primeFactors.filter (· < p) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq, _⟩, hqp⟩; exact ⟨hq, hqp⟩
    · rintro ⟨hq, hqp⟩
      refine ⟨⟨hq, ?_⟩, hqp⟩
      have : q ^ 3 < p ^ 3 := Nat.pow_lt_pow_left hqp (by norm_num)
      omega
  have hV : ∀ p ∈ s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D'),
      s'.nu p * Vbelow s' p
        = s'.nu p
          * ∏ q ∈ (s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D')).filter (· < p),
              (1 - s'.nu q) := by
    intro p hp
    congr 1
    simp only [Vbelow, belowPrimes]
    rw [hwin p hp]
  calc ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D'), s'.nu p * Vbelow s' p
      = ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D'),
          s'.nu p
            * ∏ q ∈ (s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D')).filter (· < p),
                (1 - s'.nu q) := Finset.sum_congr rfl hV
    _ = 1 - ∏ p ∈ s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D'), (1 - s'.nu p) :=
        prod_telescope _ s'.nu
    _ = 1 - Vlow s' D' := by rw [Vlow]

/-- **Total Stieltjes mass, even/lower window** (`window = all sifting primes`):
`Σ ν(p)·V(p) = 1 − W`.  Direct `prod_telescope` on the full prime factors. -/
theorem telescope_window_lower (s' : BoundingSieve) :
    ∑ p ∈ s'.prodPrimes.primeFactors, s'.nu p * Vbelow s' p
      = 1 - Salt.BrunLower.W s' := by
  have hV : ∀ p ∈ s'.prodPrimes.primeFactors,
      s'.nu p * Vbelow s' p
        = s'.nu p * ∏ q ∈ s'.prodPrimes.primeFactors.filter (· < p), (1 - s'.nu q) := by
    intro p _; simp only [Vbelow, belowPrimes]
  calc ∑ p ∈ s'.prodPrimes.primeFactors, s'.nu p * Vbelow s' p
      = ∑ p ∈ s'.prodPrimes.primeFactors,
          s'.nu p * ∏ q ∈ s'.prodPrimes.primeFactors.filter (· < p), (1 - s'.nu q) :=
        Finset.sum_congr rfl hV
    _ = 1 - ∏ p ∈ s'.prodPrimes.primeFactors, (1 - s'.nu p) := prod_telescope _ s'.nu
    _ = 1 - Salt.BrunLower.W s' := by rw [Salt.BrunLower.W]

/-! ## Part D — the ε-ledger collect (the τ-direction, parametric)

The purely-algebraic collect that turns the two sharp Stieltjes comparisons (`f`-part and
`h`-part, at abstract error coefficients `c_f, c_h`) into one `StepHyp` instance, under the
τ-recursion in the direction `c_f + ε·e²·c_h·τₙ ≤ ε·e²·τₙ₊₁`.  This is the machine-checked
τ-direction resolution: the per-`n` inequality closes for *any* `c_h` (no `β < 1` needed here;
the contraction is a τ-sum property, deferred to `htau`). -/

/-- **The ε-ledger collect (BJS (35)–(38) closure, abstract).**  With the `f`-part Stieltjes
sum `Ff ≤ W·(f₁ + c_f·hz)` and the `h`-part `Fh ≤ W·(c_h·hz)` (`hz = h` at the parent point),
and the τ-recursion `c_f + ε·e²·c_h·τₙ ≤ ε·e²·τₙ₊₁`, the assembled bound
`Ff + ε·τₙ·e²·Fh ≤ W·(f₁ + ε·τₙ₊₁·e²·hz)` holds. -/
theorem ledger_collect {W Ff Fh f1 hz cf ch ε e2 τn τn1 : ℝ}
    (hW : 0 ≤ W) (hε : 0 ≤ ε) (he2 : 0 ≤ e2) (hhz : 0 ≤ hz) (hτn : 0 ≤ τn)
    (hFf : Ff ≤ W * (f1 + cf * hz))
    (hFh : Fh ≤ W * (ch * hz))
    (hτrec : cf + ε * e2 * ch * τn ≤ ε * e2 * τn1) :
    Ff + ε * τn * e2 * Fh ≤ W * (f1 + ε * τn1 * e2 * hz) := by
  have hcoef : 0 ≤ ε * τn * e2 := by positivity
  have hFh' : ε * τn * e2 * Fh ≤ ε * τn * e2 * (W * (ch * hz)) :=
    mul_le_mul_of_nonneg_left hFh hcoef
  -- W·hz·(cf + ε·e²·ch·τn) ≤ W·hz·(ε·e²·τn1)
  have hmass : 0 ≤ W * hz := mul_nonneg hW hhz
  have hcollect : W * hz * (cf + ε * e2 * ch * τn) ≤ W * hz * (ε * e2 * τn1) :=
    mul_le_mul_of_nonneg_left hτrec hmass
  nlinarith [hFf, hFh', hcollect, hW, hhz, hcoef]

/-! ## Part E — `StepHyp` from the two sharp Stieltjes comparisons (the isolated remainder)

The full reduction: everything *except* the sharp discrete→integral comparison is discharged.
The two named hypotheses `hf`/`hh` are the genuine remaining analytic content — the `f`-part
and `h`-part Stieltjes-sum comparisons with explicit uniform error coefficients `c_f, c_h`
(BJS's (35)–(38) split) — stated in the *primitive* Stieltjes form (no `fseqBound'` wrapper, no
`ε`/`τ` mixing), which is what a future change-of-variables discharge produces directly.
`stepHyp_lhs_eq` reshapes `StepHyp`'s left side, the sum splits into `f`- and `h`-parts, and
`ledger_collect` closes under the τ-recursion `hτrec`.  This is the exact statement of what
remains: **`StepHyp` ⇐ (sharp `f`-comparison) ∧ (sharp `h`-comparison) ∧ (τ in ≥-direction).** -/

/-- **`StepHyp` from the sharp Stieltjes comparisons.**  Given the `f`-part comparison `hf`
(`Σ ν(p)V(p)·fₙ(σ_p) ≤ W·(fₙ₊₁(σ_z) + c_f·h(σ_z))`), the `h`-part comparison `hh`
(`Σ ν(p)V(p)·h(σ_p) ≤ W·(c_h·h(σ_z))`), and the τ-recursion `hτrec` in the closing direction
`c_f(n) + ε·e²·c_h(n)·τₙ ≤ ε·e²·τₙ₊₁`, the per-step comparison `StepHyp σ ε τ` holds.  The
only inputs left open are the two sharp comparisons (the change-of-variables real analysis). -/
theorem stepHyp_of_comparisons (σ : ℕ → ℕ → ℝ) (ε : ℝ) (tau : ℕ → ℝ) (cf ch : ℕ → ℝ)
    (hε : 0 ≤ ε) (hτ0 : ∀ n, 0 ≤ tau n)
    (hτrec : ∀ n, cf n + ε * Real.exp 2 * ch n * tau n ≤ ε * Real.exp 2 * tau (n + 1))
    (hf : ∀ (s' : BoundingSieve) (z side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * Vbelow s' p * fseq n (σ p (cdiv D' p)))
          ≤ Salt.BrunLower.W s' * (fseq (n + 1) (σ z D') + cf n * hBJS (σ z D')))
    (hh : ∀ (s' : BoundingSieve) (z side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * Vbelow s' p * hBJS (σ p (cdiv D' p)))
          ≤ Salt.BrunLower.W s' * (ch n * hBJS (σ z D'))) :
    StepHyp σ ε tau := by
  intro s' z side' D' n hside hD hn hz
  rw [stepHyp_lhs_eq σ ε tau s' side' D' n]
  simp only [fseqBound']
  have hsplit :
      (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
          s'.nu p * Vbelow s' p
            * (fseq n (σ p (cdiv D' p))
                + ε * tau n * Real.exp 2 * hBJS (σ p (cdiv D' p))))
        = (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
              s'.nu p * Vbelow s' p * fseq n (σ p (cdiv D' p)))
          + ε * tau n * Real.exp 2
            * ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
                s'.nu p * Vbelow s' p * hBJS (σ p (cdiv D' p)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit]
  exact ledger_collect (Salt.BrunLower.W_pos s').le hε (Real.exp_pos 2).le (hBJS_pos _).le
    (hτ0 n) (hf s' z side' D' n hside hD hn hz) (hh s' z side' D' n hside hD hn hz) (hτrec n)

end Salt.Chen
