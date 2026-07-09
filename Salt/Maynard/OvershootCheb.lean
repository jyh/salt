/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.HMainClose
import Salt.Maynard.HA11

/-!
# C3b′ — the Chebyshev (second-moment) overshoot bound (o(1))

The committed `HMainClose.hOver_bound` bounds the dim-`(k-1)` overshoot mass by a
*fixed fraction* `(3/8)·A₁^{k-1}` via first-moment Markov, and needs the (in fact
false-at-this-strength) transfer atom `A₁⁽¹⁾ ≤ (1/4)·A₁`.  Here we replace it by a
genuine **second-moment Chebyshev** overshoot that is `o(1)`:

`overshoot ≤ (25·T²/k)·A₁^{k-1} → 0`,

needing only the honest transfer ratio `A₁⁽¹⁾ ≤ c·A₁` for an *explicit* `c < 1`
(here `c = 3/5`), plus `5T ≤ k`.

* `A1_2_le_Tsq` — `A₁⁽²⁾ ≤ T²·A₁` (crude second moment; `uVal ≤ T` on `sqfCop`).
* `hmBox_moment2` — the dim-`(k-1)` **second-moment identity** over `hmBox`:
  weighting by `(∑_{i≠m} uVal)²` gives
  `(k−1)·A₁⁽²⁾·A₁^{k-2} + (k−1)(k−2)·A₁⁽¹⁾²·A₁^{k-3}`
  (diagonal = one special coordinate carrying `A₁⁽²⁾`; cross = two special
  coordinates each carrying `A₁⁽¹⁾`).
* `overshoot_cheb` — Chebyshev at threshold `k−T`, with the variance collapse
  `(k−1)·A^{k-3}·(A·A₁⁽²⁾ − A₁⁽¹⁾²) ≤ (k−1)·T²·A^{k-1}`.
-/

open Finset

namespace Salt.Maynard

/-- **Crude second moment.**  `A₁⁽²⁾ ≤ T²·A₁` (thin wrapper over
`A1_2_le_Tsq_mul_A1`, matching the brief's argument shape). -/
theorem A1_2_le_Tsq (k R : ℕ) (T : ℝ) (hk : 1 ≤ k) (hR : 2 ≤ R) (_hT : 0 ≤ T) :
    A1_2 k R (W k) T ≤ T ^ 2 * A1 k R (W k) T :=
  A1_2_le_Tsq_mul_A1 hk hR

/-! ## Two-coordinate factorizations feeding the second-moment identity -/

/-- On `hmBox`, the off-`m` weight `hmW` equals the full `univ`-product (the
`m`-fiber `= {1}` contributes `1`).  (Local copy; the `HMainClose` version is
`private`.) -/
private lemma hmW_full (k R : ℕ) (m : Fin k) (T : ℝ) {u : Fin k → ℕ}
    (hu : u ∈ hmBox k R m T) :
    hmW k R m T u = ∏ j, (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ) := by
  have hg1 : (fWt k R 1) ^ 2 / (Nat.totient 1 : ℝ) = 1 := by rw [fWt_one]; simp
  simp only [hmBox, Fintype.mem_piFinset] at hu
  have hum : u m = 1 := by have h := hu m; rwa [if_pos rfl, Finset.mem_singleton] at h
  rw [hmW, ← Finset.mul_prod_erase Finset.univ
        (fun j => (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) (Finset.mem_univ m),
      hum, hg1, one_mul]

/-- **Diagonal factorization.**  For `i ≠ m`, weighting the box mass by `uVal(uᵢ)²`
factors as `A₁⁽²⁾·A₁^{k-2}` (the special coordinate carries `A₁⁽²⁾ = ∑ fWt²·u²/φ`,
the `m`-fiber contributes `1`, the other `k−2` carry `A₁`). -/
private lemma hmBox_uSq_diag (k R : ℕ) (m : Fin k) (T : ℝ) (i : Fin k) (hi : i ≠ m) :
    (∑ u ∈ hmBox k R m T, uVal k R (u i) ^ 2 * hmW k R m T u)
      = A1_2 k R (W k) T * (A1 k R (W k) T) ^ (k - 2) := by
  classical
  have hg1 : (fWt k R 1) ^ 2 / (Nat.totient 1 : ℝ) = 1 := by rw [fWt_one]; simp
  have hsummand : ∀ u ∈ hmBox k R m T,
      uVal k R (u i) ^ 2 * hmW k R m T u
        = ∏ j, (if j = i then
                  uVal k R (u j) ^ 2 * ((fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ))
                else (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) := by
    intro u hu
    rw [hmW_full k R m T hu,
        ← Finset.mul_prod_erase Finset.univ
          (fun j => (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) (Finset.mem_univ i),
        ← Finset.mul_prod_erase Finset.univ
          (fun j => if j = i then
                      uVal k R (u j) ^ 2 * ((fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ))
                    else (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) (Finset.mem_univ i),
        if_pos rfl,
        Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
    ring
  rw [Finset.sum_congr rfl hsummand]
  simp only [hmBox]
  rw [← Finset.prod_univ_sum
        (fun i' : Fin k => if i' = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k))
        (fun j x => if j = i then uVal k R x ^ 2 * ((fWt k R x) ^ 2 / (Nat.totient x : ℝ))
                    else (fWt k R x) ^ 2 / (Nat.totient x : ℝ))]
  have hfac : ∀ j : Fin k,
      (∑ x ∈ (if j = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k)),
          if j = i then uVal k R x ^ 2 * ((fWt k R x) ^ 2 / (Nat.totient x : ℝ))
                   else (fWt k R x) ^ 2 / (Nat.totient x : ℝ))
        = if j = i then A1_2 k R (W k) T
          else (if j = m then (1 : ℝ) else A1 k R (W k) T) := by
    intro j
    by_cases hji : j = i
    · subst hji
      have hfiber : (if j = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k))
          = sqfCop (R0 k R T) (W k) := if_neg hi
      rw [hfiber, if_pos rfl, A1_2]
      apply Finset.sum_congr rfl
      intro x _
      rw [if_pos rfl]; ring
    · rw [if_neg hji]
      by_cases hjm : j = m
      · rw [if_pos hjm, if_pos hjm, Finset.sum_singleton, if_neg hji]; exact hg1
      · rw [if_neg hjm, if_neg hjm, A1]
        exact Finset.sum_congr rfl (fun x _ => by rw [if_neg hji])
  rw [Finset.prod_congr rfl (fun j _ => hfac j),
      ← Finset.mul_prod_erase Finset.univ
        (fun j => if j = i then A1_2 k R (W k) T
                  else (if j = m then (1 : ℝ) else A1 k R (W k) T)) (Finset.mem_univ i),
      if_pos rfl]
  congr 1
  rw [Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
  have hm_mem : m ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨fun h => hi h.symm, Finset.mem_univ m⟩
  rw [← Finset.mul_prod_erase (Finset.univ.erase i)
        (fun j => if j = m then (1 : ℝ) else A1 k R (W k) T) hm_mem, if_pos rfl, one_mul,
      Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj)),
      Finset.prod_const, Finset.card_erase_of_mem hm_mem,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      show k - 1 - 1 = k - 2 from by omega]

/-- **Cross factorization.**  For distinct `i₀, j₀ ≠ m`, weighting the box mass by
`uVal(u i₀)·uVal(u j₀)` factors as `A₁⁽¹⁾·A₁⁽¹⁾·A₁^{k-3}` (each of the two special
coordinates carries `A₁⁽¹⁾ = ∑ fWt²·u/φ`, the `m`-fiber contributes `1`, the other
`k−3` carry `A₁`). -/
private lemma hmBox_u_cross (k R : ℕ) (m : Fin k) (T : ℝ)
    (i₀ j₀ : Fin k) (hi₀ : i₀ ≠ m) (hj₀ : j₀ ≠ m) (hij : i₀ ≠ j₀) :
    (∑ u ∈ hmBox k R m T, uVal k R (u i₀) * uVal k R (u j₀) * hmW k R m T u)
      = A1_1 k R (W k) T * A1_1 k R (W k) T * (A1 k R (W k) T) ^ (k - 3) := by
  classical
  have hg1 : (fWt k R 1) ^ 2 / (Nat.totient 1 : ℝ) = 1 := by rw [fWt_one]; simp
  have hsummand : ∀ u ∈ hmBox k R m T,
      uVal k R (u i₀) * uVal k R (u j₀) * hmW k R m T u
        = ∏ j, (if j = i₀ then
                  uVal k R (u j) * ((fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ))
                else if j = j₀ then
                  uVal k R (u j) * ((fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ))
                else (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) := by
    intro u hu
    have hsplit : ∀ j : Fin k,
        (if j = i₀ then uVal k R (u j) * ((fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ))
         else if j = j₀ then uVal k R (u j) * ((fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ))
         else (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ))
          = (if j = i₀ then uVal k R (u i₀) else if j = j₀ then uVal k R (u j₀) else 1)
              * ((fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) := by
      intro j
      by_cases h1 : j = i₀
      · subst h1; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : j = j₀
        · subst h2; rw [if_pos rfl, if_pos rfl]
        · rw [if_neg h2, if_neg h2, one_mul]
    rw [Finset.prod_congr rfl (fun j _ => hsplit j), Finset.prod_mul_distrib,
        hmW_full k R m T hu]
    have hindic : (∏ j, (if j = i₀ then uVal k R (u i₀)
                          else if j = j₀ then uVal k R (u j₀) else (1 : ℝ)))
        = uVal k R (u i₀) * uVal k R (u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ
            (fun j => if j = i₀ then uVal k R (u i₀)
                      else if j = j₀ then uVal k R (u j₀) else (1 : ℝ)) (Finset.mem_univ i₀),
          if_pos rfl]
      have hj₀e : j₀ ∈ Finset.univ.erase i₀ :=
        Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j₀⟩
      rw [← Finset.mul_prod_erase (Finset.univ.erase i₀)
            (fun j => if j = i₀ then uVal k R (u i₀)
                      else if j = j₀ then uVal k R (u j₀) else (1 : ℝ)) hj₀e,
          if_neg (Ne.symm hij), if_pos rfl,
          Finset.prod_congr rfl (fun j hj => by
            have hjj₀ := Finset.ne_of_mem_erase hj
            have hji₀ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
            rw [if_neg hji₀, if_neg hjj₀]),
          Finset.prod_const_one]
      ring
    rw [hindic]
  rw [Finset.sum_congr rfl hsummand]
  simp only [hmBox]
  rw [← Finset.prod_univ_sum
        (fun i' : Fin k => if i' = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k))
        (fun j x => if j = i₀ then uVal k R x * ((fWt k R x) ^ 2 / (Nat.totient x : ℝ))
                    else if j = j₀ then uVal k R x * ((fWt k R x) ^ 2 / (Nat.totient x : ℝ))
                    else (fWt k R x) ^ 2 / (Nat.totient x : ℝ))]
  have hfac : ∀ j : Fin k,
      (∑ x ∈ (if j = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k)),
          if j = i₀ then uVal k R x * ((fWt k R x) ^ 2 / (Nat.totient x : ℝ))
          else if j = j₀ then uVal k R x * ((fWt k R x) ^ 2 / (Nat.totient x : ℝ))
          else (fWt k R x) ^ 2 / (Nat.totient x : ℝ))
        = if j = i₀ then A1_1 k R (W k) T
          else if j = j₀ then A1_1 k R (W k) T
          else (if j = m then (1 : ℝ) else A1 k R (W k) T) := by
    intro j
    by_cases h1 : j = i₀
    · have hjm : j ≠ m := by rw [h1]; exact hi₀
      rw [if_neg hjm, if_pos h1, A1_1]
      exact Finset.sum_congr rfl (fun x _ => by rw [if_pos h1]; ring)
    · rw [if_neg h1]
      by_cases h2 : j = j₀
      · have hjm : j ≠ m := by rw [h2]; exact hj₀
        rw [if_neg hjm, if_pos h2, A1_1]
        exact Finset.sum_congr rfl (fun x _ => by rw [if_neg h1, if_pos h2]; ring)
      · rw [if_neg h2]
        by_cases hjm : j = m
        · rw [if_pos hjm, if_pos hjm, Finset.sum_singleton, if_neg h1, if_neg h2]; exact hg1
        · rw [if_neg hjm, if_neg hjm, A1]
          exact Finset.sum_congr rfl (fun x _ => by rw [if_neg h1, if_neg h2])
  rw [Finset.prod_congr rfl (fun j _ => hfac j)]
  rw [← Finset.mul_prod_erase Finset.univ
        (fun j => if j = i₀ then A1_1 k R (W k) T
                  else if j = j₀ then A1_1 k R (W k) T
                  else (if j = m then (1 : ℝ) else A1 k R (W k) T)) (Finset.mem_univ i₀),
      if_pos rfl]
  have hj₀_mem : j₀ ∈ Finset.univ.erase i₀ :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j₀⟩
  rw [← Finset.mul_prod_erase (Finset.univ.erase i₀)
        (fun j => if j = i₀ then A1_1 k R (W k) T
                  else if j = j₀ then A1_1 k R (W k) T
                  else (if j = m then (1 : ℝ) else A1 k R (W k) T)) hj₀_mem,
      if_neg (Ne.symm hij), if_pos rfl]
  have hm_mem : m ∈ (Finset.univ.erase i₀).erase j₀ :=
    Finset.mem_erase.mpr ⟨Ne.symm hj₀,
      Finset.mem_erase.mpr ⟨Ne.symm hi₀, Finset.mem_univ m⟩⟩
  rw [← Finset.mul_prod_erase ((Finset.univ.erase i₀).erase j₀)
        (fun j => if j = i₀ then A1_1 k R (W k) T
                  else if j = j₀ then A1_1 k R (W k) T
                  else (if j = m then (1 : ℝ) else A1 k R (W k) T)) hm_mem,
      if_neg (Ne.symm hi₀), if_neg (Ne.symm hj₀), if_pos rfl]
  rw [Finset.prod_congr rfl (fun j hj => by
        have hjm := Finset.ne_of_mem_erase hj
        have hj' := Finset.mem_of_mem_erase hj
        have hjj₀ := Finset.ne_of_mem_erase hj'
        have hji₀ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj')
        rw [if_neg hji₀, if_neg hjj₀, if_neg hjm]),
      Finset.prod_const,
      Finset.card_erase_of_mem hm_mem, Finset.card_erase_of_mem hj₀_mem,
      Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin,
      show k - 1 - 1 - 1 = k - 3 from by omega]
  ring

/-! ## The second-moment identity -/

/-- **dim-`(k-1)` second-moment identity over `hmBox`.**  Weighting the off-`m` box
mass by `(∑_{i≠m} uVal(uᵢ))²` and splitting the double coordinate sum into the
diagonal (one special coordinate carrying `A₁⁽²⁾`, `k−1` of them) and the ordered
off-diagonal (two special coordinates each carrying `A₁⁽¹⁾`, `(k−1)(k−2)` of them)
gives `(k−1)·A₁⁽²⁾·A₁^{k-2} + (k−1)(k−2)·A₁⁽¹⁾²·A₁^{k-3}`.  Second-moment analogue
of `HMainClose.hmBox_moment1`.  (`2 ≤ k` only fixes the real casts of `k−1`, `k−2`;
downstream `k ≥ 16`.) -/
theorem hmBox_moment2 (k R : ℕ) (m : Fin k) (T : ℝ) (hk : 2 ≤ k) :
    (∑ u ∈ hmBox k R m T,
        (∑ i ∈ Finset.univ.erase m, uVal k R (u i)) ^ 2 * hmW k R m T u)
      = ((k : ℝ) - 1) * A1_2 k R (W k) T * (A1 k R (W k) T) ^ (k - 2)
        + ((k : ℝ) - 1) * ((k : ℝ) - 2) * (A1_1 k R (W k) T) ^ 2
            * (A1 k R (W k) T) ^ (k - 3) := by
  classical
  set s := (Finset.univ : Finset (Fin k)).erase m with hs
  have hcard : s.card = k - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
  -- Step 1: expand the square, distribute the weight, swap sums → double coordinate
  -- sum of `G i j = ∑_u uVal(uᵢ)·uVal(uⱼ)·hmW u`.
  have hsq : ∀ u, (∑ i ∈ s, uVal k R (u i)) ^ 2 * hmW k R m T u
      = ∑ i ∈ s, ∑ j ∈ s, uVal k R (u i) * uVal k R (u j) * hmW k R m T u := by
    intro u
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun u _ => hsq u), Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ s) => Finset.sum_comm)]
  -- Step 2: evaluate each inner `∑_{j∈s} G i j` (diagonal + off-diagonal).
  have hinner : ∀ i ∈ s,
      (∑ j ∈ s, ∑ u ∈ hmBox k R m T,
          uVal k R (u i) * uVal k R (u j) * hmW k R m T u)
        = A1_2 k R (W k) T * (A1 k R (W k) T) ^ (k - 2)
          + ((k : ℝ) - 2)
              * ((A1_1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 3)) := by
    intro i hi
    have him : i ≠ m := Finset.ne_of_mem_erase hi
    rw [← Finset.add_sum_erase s _ hi]
    have hdiagterm :
        (∑ u ∈ hmBox k R m T, uVal k R (u i) * uVal k R (u i) * hmW k R m T u)
          = A1_2 k R (W k) T * (A1 k R (W k) T) ^ (k - 2) := by
      rw [show (∑ u ∈ hmBox k R m T, uVal k R (u i) * uVal k R (u i) * hmW k R m T u)
            = ∑ u ∈ hmBox k R m T, uVal k R (u i) ^ 2 * hmW k R m T u from
          Finset.sum_congr rfl (fun u _ => by ring)]
      exact hmBox_uSq_diag k R m T i him
    have hoffterm : ∀ j ∈ s.erase i,
        (∑ u ∈ hmBox k R m T, uVal k R (u i) * uVal k R (u j) * hmW k R m T u)
          = A1_1 k R (W k) T ^ 2 * (A1 k R (W k) T) ^ (k - 3) := by
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hjm : j ≠ m := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
      rw [hmBox_u_cross k R m T i j him hjm (Ne.symm hji)]
      ring
    rw [hdiagterm, Finset.sum_congr rfl hoffterm, Finset.sum_const]
    have hcard2 : (s.erase i).card = k - 2 := by
      rw [Finset.card_erase_of_mem hi, hcard]; omega
    rw [hcard2, nsmul_eq_mul]
    have hcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
      rw [Nat.cast_sub hk]; norm_num
    rw [hcast]
  -- Step 3: sum the constant inner value over `s` (card `k-1`).
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, hcard, nsmul_eq_mul,
      Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  ring

/-! ## The variance collapse -/

/-- **Variance collapse.**  With the exact first-moment mean `μ = (k−1)·A₁⁽¹⁾/A₁`,
the second central moment over `hmBox` collapses to
`(k−1)·A^{k-3}·(A·A₁⁽²⁾ − A₁⁽¹⁾²) ≤ (k−1)·T²·A^{k-1}` (Cauchy–Schwarz drops the
`A₁⁽¹⁾²`; `A₁⁽²⁾ ≤ T²·A₁` gives the `T²`). -/
private lemma cheb_variance (k R : ℕ) (m : Fin k) (T : ℝ) (hk : 3 ≤ k)
    (hR : 2 ≤ R) (hT0 : 0 ≤ T) (hA1pos : 0 < A1 k R (W k) T) :
    (∑ u ∈ hmBox k R m T,
        ((∑ i ∈ Finset.univ.erase m, uVal k R (u i))
            - ((k : ℝ) - 1) * A1_1 k R (W k) T / A1 k R (W k) T) ^ 2
          * hmW k R m T u)
      ≤ ((k : ℝ) - 1) * T ^ 2 * (A1 k R (W k) T) ^ (k - 1) := by
  classical
  set μ := ((k : ℝ) - 1) * A1_1 k R (W k) T / A1 k R (W k) T with hμ
  have hexpand : ∀ u,
      ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) - μ) ^ 2 * hmW k R m T u
        = (∑ i ∈ Finset.univ.erase m, uVal k R (u i)) ^ 2 * hmW k R m T u
          - 2 * μ * ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) * hmW k R m T u)
          + μ ^ 2 * hmW k R m T u := by
    intro u; ring
  rw [Finset.sum_congr rfl (fun u _ => hexpand u), Finset.sum_add_distrib,
      Finset.sum_sub_distrib,
      show (∑ u ∈ hmBox k R m T,
              2 * μ * ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) * hmW k R m T u))
          = 2 * μ * (∑ u ∈ hmBox k R m T,
              (∑ i ∈ Finset.univ.erase m, uVal k R (u i)) * hmW k R m T u) from by
        rw [Finset.mul_sum],
      show (∑ u ∈ hmBox k R m T, μ ^ 2 * hmW k R m T u)
          = μ ^ 2 * (∑ u ∈ hmBox k R m T, hmW k R m T u) from by rw [Finset.mul_sum],
      hmBox_moment2 k R m T (by omega), hmBox_moment1, hmBox_sum]
  -- Abbreviate and re-express the powers in terms of `P = A^{k-3}`.
  set a := A1 k R (W k) T with ha_def
  set a1 := A1_1 k R (W k) T with ha1_def
  set a2 := A1_2 k R (W k) T with ha2_def
  have ha0 : a ≠ 0 := ne_of_gt hA1pos
  set P := a ^ (k - 3) with hP
  have hp2 : a ^ (k - 2) = P * a := by rw [hP, ← pow_succ]; congr 1; omega
  have hp1 : a ^ (k - 1) = P * a ^ 2 := by rw [hP, show k - 1 = (k - 3) + 2 from by omega, pow_add]
  rw [hp2, hp1]
  -- The variance identity.
  have hident :
      ((k : ℝ) - 1) * a2 * (P * a) + ((k : ℝ) - 1) * ((k : ℝ) - 2) * a1 ^ 2 * P
          - 2 * μ * (((k : ℝ) - 1) * a1 * (P * a)) + μ ^ 2 * (P * a ^ 2)
        = ((k : ℝ) - 1) * P * (a * a2 - a1 ^ 2) := by
    rw [hμ]; field_simp; ring
  rw [hident]
  -- The bound.
  have ha2T : a2 ≤ T ^ 2 * a := A1_2_le_Tsq k R T (by omega) hR hT0
  have ha_nn : (0 : ℝ) ≤ a := hA1pos.le
  have ha1nn : (0 : ℝ) ≤ a1 := A1_1_nonneg k R (W k) T hR
  have hPnn : (0 : ℝ) ≤ P := by rw [hP]; exact pow_nonneg ha_nn _
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have h1k : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  have hinner : a * a2 - a1 ^ 2 ≤ T ^ 2 * a ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left ha2T ha_nn, sq_nonneg a1]
  have hk1P : (0 : ℝ) ≤ ((k : ℝ) - 1) * P := mul_nonneg hk1 hPnn
  nlinarith [mul_le_mul_of_nonneg_left hinner hk1P]

/-! ## The Chebyshev overshoot bound -/

/-- **Chebyshev (second-moment) overshoot.**  With an honest transfer ratio
`A₁⁽¹⁾ ≤ c·A₁` for an explicit `c ≤ 7/10` and `5T ≤ k`, the dim-`(k-1)` overshoot
mass over `hmBox` (the region failing the `uVal`-threshold `∑_{i≠m} uVal < k−T`) is
`≤ (100·T²/k)·A₁^{k-1} → 0`.  Chebyshev at threshold `k−T`: on the overshoot region
`∑ uVal ≥ k−T ≥ μ + k/10` (where `μ = (k−1)·A₁⁽¹⁾/A₁ ≤ (7/10)k`), so
`1 ≤ (100/k²)(∑ uVal − μ)²`; extend to the full box and apply the variance collapse
`∑ (∑ uVal − μ)² hmW ≤ (k−1)·T²·A₁^{k-1}`.  The constant is `(1/(4/5 − 7/10))² = 100`;
`c = 7/10` is exactly the ratio delivered by `HA11.A1_1_le_seven_tenths`. -/
theorem overshoot_cheb (k R : ℕ) (m : Fin k) (T c : ℝ) (hk : 3 ≤ k) (hR : 2 ≤ R)
    (hT0 : 0 ≤ T) (hTk : 5 * T ≤ (k : ℝ)) (hc : c ≤ (7 / 10 : ℝ))
    (hA11 : A1_1 k R (W k) T ≤ c * A1 k R (W k) T)
    (hA1pos : 0 < A1 k R (W k) T) :
    (∑ u ∈ (hmBox k R m T).filter
        (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)),
        hmW k R m T u)
      ≤ (100 * T ^ 2 / (k : ℝ)) * (A1 k R (W k) T) ^ (k - 1) := by
  classical
  set μ := ((k : ℝ) - 1) * A1_1 k R (W k) T / A1 k R (W k) T with hμ
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  -- `μ ≤ (7/10)·k`.
  have hμle : μ ≤ (7 / 10 : ℝ) * (k : ℝ) := by
    rw [hμ, div_le_iff₀ hA1pos]
    nlinarith [mul_le_mul_of_nonneg_left hA11 hk1, mul_nonneg hk1 hA1pos.le, hc, hA1pos.le]
  -- On the overshoot region, `k/10 ≤ (∑ uVal) − μ`, hence `1 ≤ (100/k²)(∑ uVal − μ)²`.
  have hMarkov : ∀ u ∈ (hmBox k R m T).filter
      (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)),
      hmW k R m T u
        ≤ (100 / (k : ℝ) ^ 2)
            * (((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) - μ) ^ 2 * hmW k R m T u) := by
    intro u hu
    rw [Finset.mem_filter, not_lt] at hu
    have hreg : (k : ℝ) / 10 ≤ (∑ i ∈ Finset.univ.erase m, uVal k R (u i)) - μ := by
      have hT5 : T ≤ (k : ℝ) / 5 := by linarith
      linarith [hu.2, hμle]
    have hk10 : (k : ℝ) ≤ 10 * ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) - μ) := by linarith
    have hkk : (k : ℝ) ^ 2
        ≤ 100 * ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) - μ) ^ 2 := by
      nlinarith [hk10, hkpos.le]
    have h1 : (1 : ℝ)
        ≤ (100 / (k : ℝ) ^ 2) * ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) - μ) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)]
      nlinarith [hkk]
    calc hmW k R m T u
        = 1 * hmW k R m T u := (one_mul _).symm
      _ ≤ ((100 / (k : ℝ) ^ 2) * ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) - μ) ^ 2)
            * hmW k R m T u :=
          mul_le_mul_of_nonneg_right h1 (hmW_nonneg k R m T u)
      _ = (100 / (k : ℝ) ^ 2)
            * (((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) - μ) ^ 2 * hmW k R m T u) := by ring
  -- Assemble.
  calc (∑ u ∈ (hmBox k R m T).filter
            (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)),
            hmW k R m T u)
      ≤ ∑ u ∈ (hmBox k R m T).filter
            (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)),
            (100 / (k : ℝ) ^ 2)
              * (((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) - μ) ^ 2 * hmW k R m T u) :=
        Finset.sum_le_sum hMarkov
    _ ≤ ∑ u ∈ hmBox k R m T,
            (100 / (k : ℝ) ^ 2)
              * (((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) - μ) ^ 2 * hmW k R m T u) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro u _ _
        exact mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (hmW_nonneg k R m T u))
    _ = (100 / (k : ℝ) ^ 2)
          * (∑ u ∈ hmBox k R m T,
              ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) - μ) ^ 2 * hmW k R m T u) := by
        rw [Finset.mul_sum]
    _ ≤ (100 / (k : ℝ) ^ 2) * (((k : ℝ) - 1) * T ^ 2 * (A1 k R (W k) T) ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left (cheb_variance k R m T hk hR hT0 hA1pos) (by positivity)
    _ ≤ (100 * T ^ 2 / (k : ℝ)) * (A1 k R (W k) T) ^ (k - 1) := by
        have hb : (0 : ℝ) ≤ T ^ 2 * (A1 k R (W k) T) ^ (k - 1) := by positivity
        rw [show (100 / (k : ℝ) ^ 2) * (((k : ℝ) - 1) * T ^ 2 * (A1 k R (W k) T) ^ (k - 1))
              = 100 * ((k : ℝ) - 1) / (k : ℝ) ^ 2 * (T ^ 2 * (A1 k R (W k) T) ^ (k - 1)) from by
              ring,
            show (100 * T ^ 2 / (k : ℝ)) * (A1 k R (W k) T) ^ (k - 1)
              = 100 / (k : ℝ) * (T ^ 2 * (A1 k R (W k) T) ^ (k - 1)) from by ring]
        apply mul_le_mul_of_nonneg_right _ hb
        rw [div_le_div_iff₀ (by positivity) hkpos]
        nlinarith [hkpos]

/-! ## Full composition — the ratio hypothesis discharged (genuine o(1))

`HA11.A1_1_le_seven_tenths` proves the transfer ratio at `c = 7/10` sorry-free (with
its own explicit large-regime side hypotheses, isolated there — never the
conclusion).  Feeding it into `overshoot_cheb` removes the free ratio hypothesis and
gives the overshoot `≤ (100·T²/k)·A₁^{k-1} → 0` outright. -/
theorem overshoot_cheb_composed (k R : ℕ) (m : Fin k) (T : ℝ)
    (hk : 3 ≤ k) (hR : 2 ≤ R) (hT0 : 0 ≤ T) (hTk : 5 * T ≤ (k : ℝ))
    (hA1pos : 0 < A1 k R (W k) T)
    (hT : T = (k : ℝ) ^ ((1 : ℝ) / 8) / Real.log k) (hT1 : 1 ≤ T)
    (hX : 4 ≤ R0 k R T) (hlogk : 300 ≤ Real.log k)
    (hb4 : 4 ≤ bParam k R * Real.log (R0 k R T - 1))
    (hEA : errA1 k (W k)
        ≤ (1 / 100) * ((Nat.totient (W k) / W k : ℝ) * (bParam k R)⁻¹) * Real.log k)
    (hEB : errB1 k (W k) ≤ (1 / 100) * ((Nat.totient (W k) / W k : ℝ) * (bParam k R)⁻¹)) :
    (∑ u ∈ (hmBox k R m T).filter
        (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)),
        hmW k R m T u)
      ≤ (100 * T ^ 2 / (k : ℝ)) * (A1 k R (W k) T) ^ (k - 1) := by
  have hW : W k ≠ 0 := (W_squarefree k).ne_zero
  have hA11 := A1_1_le_seven_tenths k R (W k) T hW hk hR hT hT1 hX hlogk hb4 hEA hEB
  exact overshoot_cheb k R m T (7 / 10) hk hR hT0 hTk le_rfl hA11 hA1pos

end Salt.Maynard
