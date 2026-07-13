/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.Tail
import Salt.Chen.SwitchConstant

/-!
# C1b′ — the Rosser-chain value certification (interface + achievable core)

Design: `docs/blueprints/chen.md`, the C1b′ row.  The C5 assembly (`Assembly.lean`) needs, at the
frozen operating point, numeric bounds on the truncated Rosser chains of C1a (`RosserChain.lean`):

* a **lower** value `fchain (maxDepth s) (logRatio z D) ≥ (rational)` at `s ≈ 4` (consumed by
  `TwinA1.twin_A1_lower`, the `fchain`-term of BJS Theorem 6 (6)); and
* **upper** values `Fchain (Nf p) (logRatio z (cdiv Dtot p)) ≤ supF` on the A₂ grid
  `s_p ∈ [4/3, 3]` (consumed by `TwinA2.A2grid_le_envelope`).

This file supplies the value-certification **interface** in exactly those consumption shapes
(`fchain_lower_of_evenSum_le`, `Fchain_upper_of_oddSum_le`, and the structural
`one_le_Fchain`/`fchain_le_one`/monotonicity), the **genuine sharp leading per-level bound**
(`fseq_two_le_sq`, in the `fseq_two_window` one-integration style — the template for the sharp
per-level route), the **sharp truncation-tail closeness** (`fchain_trunc_close`, reusing C1b's
`fseq_tail_le`), and the **ledger numeric core** (`chen_ledger_line`, C4a).

## The honest arithmetic (computed pre-dispatch; the certification PLAN)

`fchain N s = 1 − Σ_{n even, n ≤ N} fseq n s`; `Fchain N s = 1 + Σ_{n odd, n ≤ N} fseq n s`.
At the A₁ operating window `s ∈ [39/10, 4]` (support: `fseq 2 4 = 0`, so the even sum starts at
`n = 4`), the TRUE values are

| s    | fchain (=f)  | even-sum   |
|------|--------------|------------|
| 3.90 | 0.972475     | 0.027525   |
| 3.96 | ≈ 0.9757     | ≈ 0.0243   |
| 4.00 | 0.978354     | 0.021646   |

with per-even-level values `f₄(4)=8.8e−3, f₆(4)=6.0e−3, f₈(4)=3.3e−3, …` decaying at the
asymptotic per-two-level ratio `f_{n+2}(4)/f_n(4) → 0.5224` (per-level `≈ 0.723`).  On the A₂ grid
`Fchain(4/3)=2.6723` (the sup), `Fchain(3/2)=2.3748`, `Fchain(3)=1.1874`.

**What the C0 ledger needs (the target constants).**  The margin `M = log 3 − ½log 6 − ½c̄ ≈
0.0212` closes only through `2·log 3 − log 6 − c̄ > 0` (`chen_ledger_line`), which requires the
truncated values to reach their asymptotic form to within the S1/S2 cert budgets: the A₁ lower
value must satisfy `fchain ≥ f(4) − 4.3·10⁻⁴ ≈ 0.9779` (S1: `δ_f ≤ 0.112 %` rel, so
even-sum `≤ ≈ 0.0221`), and the A₂ grid sup `supF ≤ ≈ 2.68` (S2: `δ_F ≤ 0.466 %` rel).  These are
essentially the exact values.

**Why the landed machinery cannot reach them (the certification wall).**  C1b's per-level bound
`fseq_le : fseq (n+1) s ≤ 2e²·(99/100)ⁿ·hbar s` carries the certified ratio `ρ = 99/100`, whose
geometric multiplier `1/(1−ρ) = 100` swamps the small per-level constant `2e²·hbar(3.9) ≈ 0.20`:
the even-sum bound it yields at `s = 3.9`, summed over *all* `n ≤ 2048`, is `≈ 10 > 1`, so it gives
**no** positive lower bound on `fchain` at any feasible depth.  Concretely the `fseq_le` tail
`Σ_{n>K} ≈ 20·(99/100)^K` first drops below `5·10⁻³` only near `K ≈ 700` — so the crude tail never
"takes over" at a small depth, and the sharp per-level route must run essentially the whole way.
The genuinely sharp value needs the **decaying** per-level constants `cₙ` (BJS Table 2 / node
C1cσ) — a `≈ 25`-level cascade of one-integration bounds in the `fseq_two_window` style plus the
sharp tail — which is a compute-heavy C+ keystone left as the C1cσ debt (see
`docs/blueprints/flags.md`, this node's entry, for the achieved-vs-needed numbers).

**What is certified here.**  The interface (exact C5 shapes), the sharp leading term
`fseq 2 s ≤ (4−s)²/(s(s−1)) ≤ 1/1000` on `[39/10, 4]` (⇒ `fchain 2 s ≥ 999/1000` — the *depth-2*
value; `fchain` is antitone in depth, so this is the truncation at `N = 2`, not the operating
depth), the tail closeness `fchain N s ∈ [fchain 2048 s − 4.3·10⁻⁴, fchain 2048 s]` for `N ≥ 2048`
(reducing the ∞-depth value to the depth-2048 value), and the ledger numeric core.  The remaining
sharp head (even levels `4 ≤ n ≲ 2048` at the operating point) is the isolated C1cσ debt.
-/

open Finset

namespace Salt.Chen

/-! ## Part A — structural value facts (bounds, depth-monotonicity) -/

/-- `fchain N s ≤ 1` (the even correction is a sum of nonnegative iterates). -/
theorem fchain_le_one (N : ℕ) (s : ℝ) : fchain N s ≤ 1 := by
  unfold fchain
  have : (0 : ℝ) ≤ ∑ n ∈ (Finset.range (N + 1)).filter (fun n => Even n), fseq n s :=
    Finset.sum_nonneg (fun n _ => fseq_nonneg n s)
  linarith

/-- `1 ≤ Fchain N s` (the odd part `Σ fₙ ≥ 0`).  The A₂ grid keeps `Fchain + slack ≥ 0`
(`TwinA2.one_le_Fchain` is the same fact; re-proved here to keep C1b′ independent of C2b). -/
theorem one_le_Fchain (N : ℕ) (s : ℝ) : 1 ≤ Fchain N s := by
  unfold Fchain
  have : (0 : ℝ) ≤ ∑ n ∈ (Finset.range (N + 1)).filter (fun n => Odd n), fseq n s :=
    Finset.sum_nonneg (fun n _ => fseq_nonneg n s)
  linarith

/-- **`fchain` is antitone in the truncation depth.**  Deeper truncation subtracts more nonnegative
even iterates, so `fchain M s ≤ fchain N s` for `N ≤ M`.  (Consequence: a lower bound proved at a
small depth does NOT transfer to the operating depth — the operating-depth lower value is
smaller.) -/
theorem fchain_antitone_depth {N M : ℕ} (h : N ≤ M) (s : ℝ) : fchain M s ≤ fchain N s := by
  unfold fchain
  have hsub : (Finset.range (N + 1)).filter (fun n => Even n)
      ⊆ (Finset.range (M + 1)).filter (fun n => Even n) :=
    Finset.filter_subset_filter _ (Finset.range_mono (by omega))
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => fseq_nonneg n s)
  linarith

/-- **`Fchain` is monotone in the truncation depth.**  Deeper truncation adds more nonnegative odd
iterates, so `Fchain N s ≤ Fchain M s` for `N ≤ M`. -/
theorem Fchain_mono_depth {N M : ℕ} (h : N ≤ M) (s : ℝ) : Fchain N s ≤ Fchain M s := by
  unfold Fchain
  have hsub : (Finset.range (N + 1)).filter (fun n => Odd n)
      ⊆ (Finset.range (M + 1)).filter (fun n => Odd n) :=
    Finset.filter_subset_filter _ (Finset.range_mono (by omega))
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => fseq_nonneg n s)
  linarith

/-! ## Part B — the value-certification interface (exact C5 consumption shapes)

The A₁ site consumes a **lower** bound on `fchain (maxDepth s) (logRatio z D)`; the A₂ site consumes
**upper** bounds on `Fchain (Nf p) (logRatio z (cdiv Dtot p))`.  Both reduce, by definition, to a
bound on the corresponding parity partial sum — the isolated numeric debt.  These reductions pin the
interface so a caller (C5) can plug the certified constants once the sharp head is discharged. -/

/-- **The A₁ lower-value reduction.**  Any upper bound `B` on the even partial sum gives the lower
value `1 − B ≤ fchain N s`.  Instantiated at `N = maxDepth s`, `s = logRatio z D ≈ 4`, this is the
`fchain`-term C5 needs; `B` is the sharp even-head debt (C1cσ). -/
theorem fchain_lower_of_evenSum_le {N : ℕ} {s B : ℝ}
    (h : ∑ n ∈ (Finset.range (N + 1)).filter (fun n => Even n), fseq n s ≤ B) :
    1 - B ≤ fchain N s := by
  unfold fchain; linarith

/-- **The A₂ upper-value reduction.**  Any upper bound `B` on the odd partial sum gives the upper
value `Fchain N s ≤ 1 + B`.  Instantiated on the grid `s_p ∈ [4/3, 3]`, this is the `supF` the
envelope `A2grid_le_envelope` consumes; `B` is the sharp odd-head debt (C1cσ). -/
theorem Fchain_upper_of_oddSum_le {N : ℕ} {s B : ℝ}
    (h : ∑ n ∈ (Finset.range (N + 1)).filter (fun n => Odd n), fseq n s ≤ B) :
    Fchain N s ≤ 1 + B := by
  unfold Fchain; linarith

/-! ## Part C — the genuine sharp leading per-level bound (`fseq_two_window` template)

`fseq 2` is the leading even iterate; at `s ≈ 4` it dominates the head.  Here is its certified
rational majorant by ONE integration (the `fseq_two_window` closed form + `log x ≤ x − 1`) — the
exact shape each of the `≈ 25` sharp levels of the C1cσ route takes. -/

/-- `f₂(4) = 0` (support edge: `fseq 2` is supported on `[2,4]`, its numerator vanishing at `4`). -/
theorem fseq_two_eq_zero_at_four : fseq 2 4 = 0 := by
  rw [fseq_two_window (by norm_num) (by norm_num)]
  rw [show (4 : ℝ) - 1 = 3 by norm_num]
  ring

/-- **The sharp `f₂` majorant.**  `f₂(s) ≤ (4−s)²/(s(s−1))` on `[2,4]`, from the closed form
`f₂(s) = ((s−4) + 3·log(3/(s−1)))/s` and `log(3/(s−1)) ≤ (4−s)/(s−1)` (`log x ≤ x − 1`).  This is
the one-integration certified per-level bound in the `fseq_two_window` style. -/
theorem fseq_two_le_sq {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    fseq 2 s ≤ (4 - s) ^ 2 / (s * (s - 1)) := by
  rw [fseq_two_window hs2 hs4]
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have hlog : Real.log (3 / (s - 1)) ≤ 3 / (s - 1) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hnum : s - 3 * Real.log (s - 1) + 3 * Real.log 3 - 4
      = (s - 4) + 3 * Real.log (3 / (s - 1)) := by
    rw [Real.log_div (by norm_num) (ne_of_gt hs1)]; ring
  rw [hnum]
  have key : (s - 4) + 3 * Real.log (3 / (s - 1)) ≤ (4 - s) ^ 2 / (s - 1) := by
    have h1 : 3 * Real.log (3 / (s - 1)) ≤ 3 * (3 / (s - 1) - 1) := by linarith
    have h2 : (s - 4) + 3 * (3 / (s - 1) - 1) = (4 - s) ^ 2 / (s - 1) := by
      field_simp; ring
    linarith
  have hfin : (4 - s) ^ 2 / (s - 1) / s = (4 - s) ^ 2 / (s * (s - 1)) := by
    rw [div_div]; ring_nf
  calc (s - 4 + 3 * Real.log (3 / (s - 1))) / s
      ≤ (4 - s) ^ 2 / (s - 1) / s := by gcongr
    _ = (4 - s) ^ 2 / (s * (s - 1)) := hfin

/-- **The `f₂` bound at the A₁ operating window `[39/10, 4]`.**  `f₂(s) ≤ 1/1000`
(true max `≈ 4.4·10⁻⁴` at `s = 39/10`). -/
theorem fseq_two_le_op {s : ℝ} (hs : 39 / 10 ≤ s) (hs4 : s ≤ 4) : fseq 2 s ≤ 1 / 1000 := by
  refine (fseq_two_le_sq (by linarith) hs4).trans ?_
  have hs0 : (0 : ℝ) < s := by linarith
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (4 - s), hs, hs4, mul_pos hs0 hs1]

/-! ## Part D — the depth-2 certified value (genuine, but at the depth-2 truncation)

`fchain` at truncation depth `N = 2` subtracts only `f₂`; combined with the sharp `f₂` bound this
gives a fully certified numeric lower value.  NB the depth: `fchain` is antitone in `N`
(`fchain_antitone_depth`), so this is the value at `N = 2`, an *upper* anchor for the operating
depth, not a lower bound there — the operating-depth lower value (subtracting `f₄, f₆, …` too) is
smaller and is the isolated C1cσ debt. -/

/-- `fchain 2 s = 1 − f₂(s)` (the even filter of `range 3` is `{0, 2}`, and `f₀ = 0`). -/
theorem fchain_two_eq (s : ℝ) : fchain 2 s = 1 - fseq 2 s := by
  unfold fchain
  have hfilt : (Finset.range 3).filter (fun n => Even n) = {0, 2} := by decide
  rw [hfilt, Finset.sum_pair (by norm_num), fseq_zero]
  ring

/-- **The depth-2 certified lower value.**  `fchain 2 s ≥ 999/1000` on `[39/10, 4]`.  Genuine and
sorry-free; see the section note on the depth caveat. -/
theorem fchain_two_lower {s : ℝ} (hs : 39 / 10 ≤ s) (hs4 : s ≤ 4) : 999 / 1000 ≤ fchain 2 s := by
  rw [fchain_two_eq]
  have := fseq_two_le_op hs hs4
  linarith

/-! ## Part E — the sharp truncation-tail closeness (reuses C1b `fseq_tail_le`)

At any depth `N ≥ 2048`, `fchain N s` agrees with the depth-2048 value to within the S1 cert budget
`4.3·10⁻⁴` (the even tail past 2048), for every operating point `s ≥ 4/3`.  This is the SHARP tail
half of the certification: it reduces the ∞-depth value to the depth-2048 value.  (The remaining
sharp head — even levels `≤ 2048` — is the C1cσ debt.) -/

/-- **`fchain` truncation closeness.**  For `N ≥ 2048` and `s ≥ 4/3`,
`fchain 2048 s − 4.3·10⁻⁴ ≤ fchain N s ≤ fchain 2048 s`.  The upper side is depth-antitonicity; the
lower side is the even tail `Σ_{2048 < n ≤ N, n even} fₙ(s) ≤ 43/100000` (`fseq_tail_le`). -/
theorem fchain_trunc_close {N : ℕ} (hN : 2048 ≤ N) {s : ℝ} (hs : 4 / 3 ≤ s) :
    fchain 2048 s - 43 / 100000 ≤ fchain N s ∧ fchain N s ≤ fchain 2048 s := by
  refine ⟨?_, fchain_antitone_depth hN s⟩
  set t := (Finset.range (N + 1)).filter (fun n => Even n) with ht
  set u := (Finset.range 2049).filter (fun n => Even n) with hu
  have hsub : u ⊆ t := Finset.filter_subset_filter _ (Finset.range_mono (by omega))
  have hdiff : fchain 2048 s - fchain N s = ∑ n ∈ t \ u, fseq n s := by
    rw [Finset.sum_sdiff_eq_sub hsub]; simp only [fchain, ht, hu]; ring
  have hsubIoc : t \ u ⊆ Finset.Ioc 2048 N := by
    intro n hn
    rw [Finset.mem_sdiff] at hn
    obtain ⟨hnt, hnu⟩ := hn
    rw [ht, Finset.mem_filter, Finset.mem_range] at hnt
    rw [hu, Finset.mem_filter, Finset.mem_range] at hnu
    obtain ⟨hnN, hEven⟩ := hnt
    rw [Finset.mem_Ioc]
    refine ⟨?_, by omega⟩
    rcases Nat.lt_or_ge n 2049 with h | h
    · exact absurd ⟨h, hEven⟩ hnu
    · omega
  have hbound : ∑ n ∈ t \ u, fseq n s ≤ 43 / 100000 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubIoc (fun n _ _ => fseq_nonneg n s))
      (fseq_tail_le 2048 N (le_refl 2048) s hs)
  linarith [hdiff, hbound]

/-! ## Part F — the ledger numeric core (C4a), and the value-certification verdict

The C5 assembly's numeric closure (`Assembly.chen_positivity`'s `hledger`) reduces, at the carrier
normalisation `Π₂x/(4 log z)`, to the single log line `2·log 3 − log 6 − c̄ > 0` (with
`c̄ ≤ 0.363084`).  This is CLOSED (landed in C4a, `two_log_three_sub_log_six_sub_cbar_pos`).

**The value-certification verdict for the ledger.**  The line closes *given* the truncated values
map to their asymptotic form: the A₁ lower value `fchain → f(4)` supplies the `2·log 3` term, and
the A₂ grid `Fchain → F` the `log 6` term, both within the S1/S2 cert budgets.  The **mappings** are
the
interface pinned in Parts B–E; the **sharp constants** (`fchain ≥ 0.9779`, `supF ≤ 2.68`) are the
isolated C1cσ debt.  So the ledger's numeric core is closed, and the value certification is complete
modulo the sharp head — quantified in `docs/blueprints/flags.md`. -/

/-- **The ledger numeric core** (C4a, re-exposed in the value-certification context).
`0 < 2·log 3 − log 6 − 0.363084` — the only switch-constant fact the C5 ledger consumes, and the
target the certified A₁/A₂ values must reach (asymptotically `2·log 3` and `log 6`). -/
theorem chen_ledger_line : (0 : ℝ) < 2 * Real.log 3 - Real.log 6 - 0.363084 :=
  two_log_three_sub_log_six_sub_cbar_pos

end Salt.Chen
