/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CharFold

/-!
# KMT port, wave P-2, stage S4: the hybrid large sieve for characters (KMT Lemma 6.2)

Freeze: `docs/exploration/port-freeze-0729.md` (wave P-2); refuter verdict R-P3.

## The statement

For `s ⊆ [1, N]` and any coefficients `a : ℕ → ℂ`,

`∑_{χ mod q} ∫_{-T}^{T} ‖∑_{n∈s} aₙ·χ(n)·n^{it}‖² dt`
`  ≤ (2·φ(q)·T + 7·φ(q)·N/q) · ∑_{n∈s, (n,q)=1} ‖aₙ‖²`.

Both constants are *derived*, not assumed:

* the `2·φ(q)·T` is the diagonal, exactly (`2T` per class from the two half-ranges of the
  symmetric window, `φ(q)` classes after the Plancherel fold);
* the `7·φ(q)·N/q` is the off-diagonal.  The refuter's audit priced it at `4π ≤ 13` from
  a separation `δ = q/(2N)`; the landed AP gap lemma `log_gap_ge_of_modEq` is sharp at
  `δ = q/N`, which halves the exponent's cost to `2π ≤ 7` — **so the sharp form is
  delivered.**

## The three moving parts

1. **The fold** (`sum_chi_meanSq_fold`, S3): the character sum collapses to `φ(q)` times a
   sum over the *unit residue classes* mod `q` — all `χ`, no primitivity filter.
2. **The AP gap** (`log_gap_ge_of_modEq`, S1): within one residue class the log-frequencies
   are `q/N`-separated, not merely `1/N`.
3. **The Finset MVT** (`dpolyS_l2_mvt_final`, S2): the mean-value theorem run *on the class*,
   paying `2π/δ = 2πN/q`.

R-P3's warning is what forces this order: running the MVT on `Icc 1 N` and only then
splitting by class loses the factor `q` outright (each class would pay `2πN`, and `φ(q)`
classes would pay `φ(q)·2πN` — a factor `q` above the target).  The `φ(q)/q` in the final
constant is the *safe* saving (dropping it costs only a `logloglog`); the `1/q` bought by
the per-class separation is **not** droppable.

## The `t`-sign convention

`dpolyChi` is written at `n^{+it}`, matching KMT's Lemma 6.2.  The corpus's large-value
callers use `P(1−it)`; `dpolyS_meanSq_reflect` (`Salt/MR/MVHilbertFinset.lean`) shows the
mean square over the symmetric window `[-T, T]` is invariant under `t ↦ −t`, so the two
conventions agree here at no cost.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory intervalIntegral

/-- **S4, the per-class estimate.**  On a single residue class mod `q` inside `[1, N]` the
log-frequencies are `q/N`-separated (S1), so the Finset mean-value theorem (S2) pays
`2π·N/q ≤ 7·N/q` instead of `2π·N`. -/
lemma classSet_meanSq_le {N : ℕ} (q : ℕ) (hq : 0 < q) (hN : 0 < N) (s : Finset ℕ)
    (hs : s ⊆ Finset.Icc 1 N) (a : ℕ → ℂ) (T : ℝ) (b : ZMod q) :
    (∫ t in (-T)..T, ‖dpolyS (classSet q s b) a t‖ ^ 2)
      ≤ (2 * T + 7 * (N : ℝ) / q) * ∑ n ∈ classSet q s b, ‖a n‖ ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hδ : (0 : ℝ) < (q : ℝ) / N := by positivity
  have hmem : ∀ n ∈ classSet q s b, n ∈ Finset.Icc 1 N := fun n hn => hs (classSet_subset hn)
  have hs1 : ∀ n ∈ classSet q s b, 1 ≤ n := fun n hn => (Finset.mem_Icc.1 (hmem n hn)).1
  have hgap : ∀ i ∈ classSet q s b, ∀ j ∈ classSet q s b, i ≠ j →
      (q : ℝ) / N ≤ |Real.log i - Real.log j| := by
    intro i hi j hj hij
    have hci : (i : ZMod q) = b := (mem_classSet.1 hi).2
    have hcj : (j : ZMod q) = b := (mem_classSet.1 hj).2
    have hcong : i ≡ j [MOD q] :=
      (ZMod.natCast_eq_natCast_iff i j q).1 (by rw [hci, hcj])
    exact log_gap_ge_of_modEq hq (hmem i hi) (hmem j hj) hij hcong
  have hmain := dpolyS_l2_mvt_final (classSet q s b) hs1 a T hδ hgap
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_
    (Finset.sum_nonneg fun n _ => by positivity))
  -- `2π/(q/N) = 2πN/q ≤ 7N/q`
  have hrewrite : 2 * Real.pi / ((q : ℝ) / N) = 2 * Real.pi * (N : ℝ) / q :=
    div_div_eq_mul_div _ _ _
  have hnum : 2 * Real.pi * (N : ℝ) ≤ 7 * (N : ℝ) := by
    nlinarith [Real.pi_lt_d2, hNr.le]
  have hstep : 2 * Real.pi * (N : ℝ) / q ≤ 7 * (N : ℝ) / q :=
    div_le_div_of_nonneg_right hnum hqr.le
  rw [hrewrite]
  linarith [hstep]

/-- The unit-class mass equals the coprime-restricted mass:
`∑_{b unit} ∑_{n∈s, n≡b} ‖aₙ‖² = ∑_{n∈s, (n,q)=1} ‖aₙ‖²`. -/
lemma sum_unitClass_mass (q : ℕ) [NeZero q] (s : Finset ℕ) (a : ℕ → ℂ) :
    (∑ b : ZMod q, (if IsUnit b then ∑ n ∈ classSet q s b, ‖a n‖ ^ 2 else 0))
      = ∑ n ∈ s.filter (fun n => Nat.Coprime n q), ‖a n‖ ^ 2 := by
  have hfib := Finset.sum_fiberwise (s.filter (fun n => Nat.Coprime n q))
    (fun n : ℕ => (n : ZMod q)) (fun n : ℕ => ‖a n‖ ^ 2)
  rw [← hfib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hset : ∀ n : ℕ,
      n ∈ (s.filter (fun n => Nat.Coprime n q)).filter (fun n : ℕ => (n : ZMod q) = b)
        ↔ (n ∈ s ∧ (n : ZMod q) = b) ∧ Nat.Coprime n q := by
    intro n
    rw [Finset.mem_filter, Finset.mem_filter]
    tauto
  by_cases hb : IsUnit b
  · rw [if_pos hb]
    refine Finset.sum_congr (Finset.ext fun n => ?_) (fun n _ => rfl)
    rw [mem_classSet, hset n]
    constructor
    · intro h; exact ⟨h, (ZMod.isUnit_iff_coprime n q).1 (h.2 ▸ hb)⟩
    · intro h; exact h.1
  · rw [if_neg hb]
    refine (Finset.sum_eq_zero fun n hn => ?_).symm
    exfalso
    obtain ⟨⟨_, hcast⟩, hcop⟩ := (hset n).1 hn
    exact hb (hcast ▸ (ZMod.isUnit_iff_coprime n q).2 hcop)

/-- **S4 — THE HYBRID LARGE SIEVE FOR CHARACTERS (KMT Lemma 6.2).**  For `s ⊆ [1, N]`,

`∑_{χ mod q} ∫_{-T}^{T} ‖∑_{n∈s} aₙ·χ(n)·n^{it}‖² dt`
`  ≤ (2·φ(q)·T + 7·φ(q)·N/q) · ∑_{n∈s, (n,q)=1} ‖aₙ‖²`.

The sum is over **all** `φ(q)` Dirichlet characters mod `q` (principal and imprimitive
included), the window is symmetric, and the right-hand mass is restricted to the coprime
part (the sharp form: non-coprime `n` contribute nothing, since `χ(n) = 0`).

Constants: `2` on the `φ(q)T` diagonal is exact; `7` on the `φ(q)N/q` off-diagonal is
`2π` rounded up, delivered by the sharp AP gap `δ = q/N`. -/
theorem hybrid_char_mvt {N : ℕ} (q : ℕ) [NeZero q] (s : Finset ℕ)
    (hs : s ⊆ Finset.Icc 1 N) (a : ℕ → ℂ) (T : ℝ) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T, ‖dpolyChi q s a χ t‖ ^ 2)
      ≤ (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
          * ∑ n ∈ s.filter (fun n => Nat.Coprime n q), ‖a n‖ ^ 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hφnn : (0 : ℝ) ≤ (q.totient : ℝ) := by positivity
  rcases s.eq_empty_or_nonempty with hemp | hne
  · subst hemp
    simp [dpolyChi]
  -- `s` nonempty forces `N ≥ 1`
  obtain ⟨n₀, hn₀⟩ := hne
  have hN : 0 < N := by
    have := Finset.mem_Icc.1 (hs hn₀)
    omega
  set P := ∑ n ∈ s.filter (fun n => Nat.Coprime n q), ‖a n‖ ^ 2 with hPdef
  -- the fold, then the per-class estimate, then the mass identity
  rw [sum_chi_meanSq_fold q s a T]
  have hclass : ∀ b : ZMod q,
      (if IsUnit b then ∫ t in (-T)..T, ‖dpolyS (classSet q s b) a t‖ ^ 2 else 0)
        ≤ (if IsUnit b then (2 * T + 7 * (N : ℝ) / q) * ∑ n ∈ classSet q s b, ‖a n‖ ^ 2
            else 0) := by
    intro b
    by_cases hb : IsUnit b
    · rw [if_pos hb, if_pos hb]
      exact classSet_meanSq_le q hq hN s hs a T b
    · rw [if_neg hb, if_neg hb]
  have hsum : (∑ b : ZMod q,
        (if IsUnit b then ∫ t in (-T)..T, ‖dpolyS (classSet q s b) a t‖ ^ 2 else 0))
      ≤ (2 * T + 7 * (N : ℝ) / q) * P := by
    refine (Finset.sum_le_sum fun b _ => hclass b).trans ?_
    have hpull : (∑ b : ZMod q,
          (if IsUnit b then (2 * T + 7 * (N : ℝ) / q) * ∑ n ∈ classSet q s b, ‖a n‖ ^ 2
            else 0))
        = (2 * T + 7 * (N : ℝ) / q)
            * ∑ b : ZMod q, (if IsUnit b then ∑ n ∈ classSet q s b, ‖a n‖ ^ 2 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> ring
    rw [hpull, sum_unitClass_mass q s a, ← hPdef]
  calc (q.totient : ℝ) * ∑ b : ZMod q,
          (if IsUnit b then ∫ t in (-T)..T, ‖dpolyS (classSet q s b) a t‖ ^ 2 else 0)
      ≤ (q.totient : ℝ) * ((2 * T + 7 * (N : ℝ) / q) * P) :=
        mul_le_mul_of_nonneg_left hsum hφnn
    _ = (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q) * P := by ring

/-- **The full-mass form.**  Same bound with the right-hand side taken over all of `s`
(a valid weakening: the discarded terms are nonnegative).  Needs `0 ≤ T` so the constant
is nonnegative. -/
theorem hybrid_char_mvt_full {N : ℕ} (q : ℕ) [NeZero q] (s : Finset ℕ)
    (hs : s ⊆ Finset.Icc 1 N) (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T, ‖dpolyChi q s a χ t‖ ^ 2)
      ≤ (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
          * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hφnn : (0 : ℝ) ≤ (q.totient : ℝ) := by positivity
  have hCnn : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q := by
    have h1 : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T := by positivity
    have h2 : (0 : ℝ) ≤ 7 * (q.totient : ℝ) * (N : ℝ) / q := by positivity
    linarith
  refine (hybrid_char_mvt q s hs a T).trans (mul_le_mul_of_nonneg_left ?_ hCnn)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun n _ _ => by positivity)

end Salt.MR
