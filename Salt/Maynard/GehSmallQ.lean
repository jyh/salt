/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehSW
import Salt.SW.Gate
import Salt.LS.TypeSums

/-!
# The small-modulus Type-II Siegel–Walfisz supplier (node S2-B3-SMALLQ)

Design: `docs/exploration/pilot.md`; the small-`q` half of `SmallQTypeII M V 3`
(`Salt/Maynard/GehSW.lean`), the last C-tier core of the GEH door.  For
`q ≤ (log x)^{A+1}` the trivial bound (`seqDiscrepancy_interval_le`) provably
fails — it gives `~ M·log x`, not `~ M/(log x)^A` — so genuine Siegel–Walfisz
cancellation is mandatory.

## The route (plan-step-1 … 4)

For a residue predicate `P` (either `n % q = a` or `Coprime n q`, both `∧`-ed with
the block and the `r`-coprimality twist) the class/mean sums are all instances of

  `Σ_{n ∈ Icc 1 x, P n} typeIIData V n`.

* **Step 1 — REINDEX (landed here, `typeIIData_residue_reindex`).**  Unfolding
  `typeIIData V n = Σ_{c ∣ n, c > V} Λ c` and substituting `n = m·c` groups the
  double sum with the divisor `c` INNER and its cofactor `m` OUTER:

    `Σ_{n, P n} typeIIData V n = Σ_{m ≤ x} Σ_{c : c>V, m·c≤x, P(m·c)} Λ c`.

  The inner sum is `Λ` over a `c`-interval, which — once `P` is a congruence
  `m·c ≡ a (q)` — is a `ψ`-in-AP window `psiAP U q' b − psiAP L q' b`, exactly the
  shape `siegelWalfisz_holds` (`Salt/SW/Gate.lean`) bounds.

* **Step 2 — SW FEED + REASSEMBLY (residual).**  Reduce `m·c ≡ a (q)` to
  `c ≡ b (q')`, `q' = q/gcd(m,q)` (solvable iff `gcd(m,q) ∣ a`; else the class is
  empty), feed `siegelWalfisz_holds` (with `C := A+1`, valid since `q' ≤ q ≤
  (log x)^{A+1}`) at both endpoints, and check the `Σ_m (M/m)/φ(q')` main terms
  reassemble into the coprime mean of `typeIIData` — leaving `Σ_m` per-`m` SW
  errors, summed via `Σ_{m ≤ 2M/V} 1/m ≪ log` at saving `A' = A+2`.

* **Step 3 — the `r`-twist is NOT a wall.**  `Coprime(m·c) r ↔ Coprime m r ∧
  Coprime c r`; the `Coprime c r` factor does not force SW at modulus `qr`
  (unbounded in `r`).  Because `Λ` is supported on prime powers, `Coprime c r`
  only DELETES the prime powers of the `ω(r)` primes dividing `r`, a sparse
  correction `≤ 2·ω(r)·log(2M)` per `m` (at most one power of each `p` in a
  ratio-`2` window).  Summed over `m ≤ 2M/V` this is `≤ (2M/V)·2ω(r)·log(2M)`,
  absorbed by the RHS budget `τ(qr)^3·M/(log x)^A` since `τ(qr)^3 ≥ 2^{3ω(r)} ≥
  ω(r)` and the `1/V = x^{-1/3}`-grade decay kills the polylog.  The `j = 3`
  divisor budget is exactly `τ(q)` (gcd classes) · `τ(r)` (twist) · one spare.

* **Step 4 — assemble `SmallQTypeII M V 3`** from the two-sided discrepancy.

## Status of this node — FLAG (contained, non-halting)

Step 1 is **landed sorry-free** below.  Steps 2–4 (the `psiAP`-window
identification, the `gcd(m,q)` solvability split, the double SW feed with main-term
reassembly, the prime-power `r`-correction, and the `Σ_m` estimate) are a large
C/D-tier estimate NOT completed in this pass; `SmallQTypeII M V 3` therefore
remains the explicit hypothesis of `swAt_typeIIData` (`Salt/Maynard/GehSW.lean`),
exactly as its docstring already declares.

The residual is entirely INSIDE the dispatch's enumerated case space (M-vs-V
regimes × gcd solvability × `r`-twist multiplicativity × `psiAP` endpoints × `q'=1`
× tiny `x`).  Per III.3‴ it is a contained floor, NOT a chain-halting residual
outside the space: there is no mathematical obstruction — the `r`-twist is
resolved above by prime-power sparsity — only formalization volume.
-/

open Finset ArithmeticFunction

namespace Salt.Maynard

/-- **Divisor double-counting reindex** over `Icc 1 x`.  Swaps `Σ_{n} Σ_{d ∣ n}`
into `Σ_{d} Σ_{m : d·m ≤ x}` via `n = d·m`: `sum_comm'` to reorder, then the
per-`d` bijection `n ↔ n/d` (`sum_nbij'`).  The real-valued `Icc 1 x` analogue of
`Salt.LS.reindex_core` (which is `private`/`ℂ`/`Ioc V x`). -/
private theorem divisor_reindex_icc {x : ℕ} (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, F n d)
      = ∑ d ∈ Finset.Icc 1 x,
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => d * m ≤ x), F (d * m) d := by
  have hcomm : (∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, F n d)
      = ∑ d ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (d ∣ ·), F n d := by
    apply Finset.sum_comm'
    intro n d
    constructor
    · intro h
      obtain ⟨hn, hd⟩ := h
      rw [Nat.mem_divisors] at hd
      rw [Finset.mem_Icc] at hn
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
      have hdx : d ≤ x := le_trans (Nat.le_of_dvd (by omega) hd.1) hn.2
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hn, hd.1⟩,
        Finset.mem_Icc.mpr ⟨hdpos, hdx⟩⟩
    · intro h
      obtain ⟨hnf, _hd⟩ := h
      rw [Finset.mem_filter] at hnf
      obtain ⟨hn, hdvd⟩ := hnf
      rw [Finset.mem_Icc] at hn
      exact ⟨Finset.mem_Icc.mpr hn, Nat.mem_divisors.mpr ⟨hdvd, by omega⟩⟩
  rw [hcomm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hd1 : 0 < d := (Finset.mem_Icc.mp hd).1
  refine Finset.sum_nbij' (fun n => n / d) (fun m => d * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hnx⟩, hdvd⟩ := hn
    have hdn : d * (n / d) = n := Nat.mul_div_cancel' hdvd
    exact ⟨⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd1,
      le_trans (Nat.div_le_self n d) hnx⟩, by rw [hdn]; exact hnx⟩
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    obtain ⟨⟨hm1, _hmx⟩, hx⟩ := hm
    have hpos : 0 < d * m := Nat.mul_pos hd1 (by omega)
    exact ⟨⟨by omega, hx⟩, dvd_mul_right d m⟩
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _
    exact Nat.mul_div_cancel_left m hd1
  · intro n hn
    simp only [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]

/-- **Step 1 — the Type-II residue reindex.**  For any residue predicate `P`,
`Σ_{n ∈ Icc 1 x, P n} typeIIData V n = Σ_{m ≤ x} Σ_{c : c>V, m·c≤x, P(m·c)} Λ c`.
Unfold `typeIIData` by its cofactor (`Nat.sum_div_divisors`), fold `P` and the
`V < c` threshold into the summand, apply `divisor_reindex_icc`, then repackage the
inner filter.  The inner `Λ`-over-interval is the `ψ`-in-AP window the SW gate
feeds. -/
theorem typeIIData_residue_reindex (V x : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ n ∈ (Finset.Icc 1 x).filter P, Salt.LS.typeIIData V n)
      = ∑ m ∈ Finset.Icc 1 x,
          ∑ c ∈ (Finset.Icc 1 x).filter (fun c => V < c ∧ m * c ≤ x ∧ P (m * c)),
            Λ c := by
  have hLHS : (∑ n ∈ (Finset.Icc 1 x).filter P, Salt.LS.typeIIData V n)
      = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors,
          (if P n then (if V < n / d then Λ (n / d) else 0) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases hP : P n
    · rw [if_pos hP, Salt.LS.typeIIData, Finset.sum_filter,
        ← Nat.sum_div_divisors n (fun c => if V < c then Λ c else 0)]
      exact Finset.sum_congr rfl (fun d _ => (if_pos hP).symm)
    · rw [if_neg hP]
      exact (Finset.sum_eq_zero (fun d _ => by rw [if_neg hP])).symm
  rw [hLHS, divisor_reindex_icc]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hd1 : 0 < d := (Finset.mem_Icc.mp hd).1
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Nat.mul_div_cancel_left c hd1]
  by_cases h1 : d * c ≤ x <;> by_cases h2 : P (d * c) <;> by_cases h3 : V < c <;>
    simp [h1, h2, h3]

end Salt.Maynard
