/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Compat
import Salt.Brun.CongruenceCounting

/-!
# Per-tuple congruence count (blueprint N4.1)

For the Maynard sieve's cross-term analysis we need the count of `n` in a
dyadic-type window `(N, K₀N]` subject to the fixed `W`-trick congruence
`n ≡ ν₀ (mod W k)` and, for every coordinate `i`, the divisibility
`lcm(dᵢ, eᵢ) ∣ n + hSeq k i`.

* `congCountTuple` — the counting function.
* `congCountTuple_collision` — if two coordinates share a common prime
  factor (both coprime to `W k`), the count is exactly `0`: the shared
  prime would divide both `n + hSeq k i` and `n + hSeq k j`, impossible
  for `i ≠ j` by `not_common_prime_cross`.
* `congCountTuple_approx` — in the compatible case (pairwise-coprime moduli,
  solvable system) the count is `((K₀-1)N)/M ± 2 ≤ ((K₀-1)N)/M ± 2^(k+1)`
  with `M = W k * ∏ᵢ lcm(dᵢ,eᵢ)`. The `k+1` congruences are folded by CRT
  into a single residue class mod `M`, whose count in the interval is read
  off from the Brun congruence-counting bound at the two endpoints.

The error constant is deliberately generous (`2^(k+1)`): the caller
(N4.3/N5.1) only needs `O_k(1)`.
-/

namespace Salt.Maynard

open Finset

/-! ## A CRT fold: pairwise-coprime moduli combine `ModEq` over a product -/

/-- If `a ≡ b` modulo each of a family of pairwise-coprime moduli indexed
by a `Finset`, then `a ≡ b` modulo their product. -/
lemma modEq_prod_of_pairwise_coprime {ι : Type*} {a b : ℕ}
    (m : ι → ℕ) :
    ∀ (s : Finset ι),
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (m i) (m j)) →
      (∀ i ∈ s, a ≡ b [MOD m i]) →
      a ≡ b [MOD ∏ i ∈ s, m i] := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => intro _ _; simpa using (Nat.modEq_one : a ≡ b [MOD 1])
  | insert x s hx ih =>
    intro hcop h
    rw [Finset.prod_insert hx]
    have hxmod : a ≡ b [MOD m x] := h x (Finset.mem_insert_self x s)
    have hrest : a ≡ b [MOD ∏ i ∈ s, m i] := by
      refine ih (fun i hi j hj hij => ?_) (fun i hi => h i (Finset.mem_insert_of_mem hi))
      exact hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hcopr : Nat.Coprime (m x) (∏ i ∈ s, m i) := by
      apply Nat.Coprime.prod_right
      intro j hj
      exact hcop x (Finset.mem_insert_self x s) j (Finset.mem_insert_of_mem hj)
        (by rintro rfl; exact hx hj)
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcopr).mp ⟨hxmod, hrest⟩

/-! ## The counting function -/

/-- The count of `n ∈ (N, K₀N]` with `n ≡ ν₀ (mod W k)` and
`lcm(dᵢ,eᵢ) ∣ n + hSeq k i` for every `i`. -/
noncomputable def congCountTuple (k K₀ N : ℕ) (ν₀ : ℕ) (d e : Fin k → ℕ) : ℕ :=
  ((Finset.Ioc N (K₀ * N)).filter
    (fun n => n % W k = ν₀ % W k ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (n + hSeq k i))).card

/-! ## Collision case -/

/-- **N4.1 (collision).** If two distinct coordinates `i ≠ j` have
`gcd(dᵢ, eⱼ) > 1` while `dᵢ` and `eⱼ` are each coprime to `W k`, then no
`n` can satisfy the system, so the count is `0`. -/
theorem congCountTuple_collision (k K₀ N ν₀ : ℕ) (d e : Fin k → ℕ)
    (hd : ∀ i, Nat.Coprime (d i) (W k)) (_he : ∀ i, Nat.Coprime (e i) (W k))
    {i j : Fin k} (hij : i ≠ j) (hcol : ¬ Nat.Coprime (d i) (e j)) :
    congCountTuple k K₀ N ν₀ d e = 0 := by
  unfold congCountTuple
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _hn
  rintro ⟨_hnW, hdvd⟩
  -- a prime `p` dividing `gcd(d i, e j)`
  obtain ⟨p, hp, hpdi, hpej⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcol
  have hpNat : p.Prime := hp
  -- `p` must exceed `D₀ k`, since `d i` is coprime to `W k`
  have hpD : D₀ k < p := D₀_lt_of_prime_dvd_coprime (hd i) hpNat hpdi
  -- `p ∣ n + hSeq k i` via `p ∣ d i ∣ lcm(dᵢ,eᵢ) ∣ n + hSeq k i`
  have h1 : p ∣ (n + hSeq k i) :=
    (dvd_trans hpdi (Nat.dvd_lcm_left (d i) (e i))).trans (hdvd i)
  -- `p ∣ n + hSeq k j` via `p ∣ e j ∣ lcm(dⱼ,eⱼ) ∣ n + hSeq k j`
  have h2 : p ∣ (n + hSeq k j) :=
    (dvd_trans hpej (Nat.dvd_lcm_right (d j) (e j))).trans (hdvd j)
  exact not_common_prime_cross hij hpNat hpD h1 h2

/-! ## Compatible case -/

/-- **N4.1 (approx).** In the compatible case — the `k+1` moduli `W k` and
`lcm(dᵢ,eᵢ)` are positive and pairwise coprime, and the combined system is
solvable — the count is `((K₀-1)N)/M ± 2^(k+1)` with
`M = W k * ∏ᵢ lcm(dᵢ,eᵢ)`. (We actually prove the sharper `±2`; the
`2^(k+1)` slack in the statement matches the caller's `O_k(1)` need.)

Hypotheses (chosen for provability + sufficiency for N4.3/N5.1):
* `hK₀ : 1 ≤ K₀` — the window `(N, K₀N]` has positive multiplicative width;
* `hlcmpos i` — each combined coordinate modulus is positive;
* `hcopW i` — `W k` is coprime to each `lcm(dᵢ,eᵢ)`;
* `hcoplcm i j` — the coordinate moduli are pairwise coprime;
* `hsol` — there is a residue `c` solving the whole system. -/
theorem congCountTuple_approx (k K₀ N ν₀ : ℕ) (d e : Fin k → ℕ)
    (hK₀ : 1 ≤ K₀)
    (hlcmpos : ∀ i, 0 < Nat.lcm (d i) (e i))
    (hcopW : ∀ i, Nat.Coprime (W k) (Nat.lcm (d i) (e i)))
    (hcoplcm : ∀ i j, i ≠ j → Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j)))
    (hsol : ∃ c : ℕ, c % W k = ν₀ % W k ∧
      ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i)) :
    |(congCountTuple k K₀ N ν₀ d e : ℝ)
       - ((K₀ - 1) * N : ℝ) / (W k * ∏ i, Nat.lcm (d i) (e i) : ℕ)|
      ≤ 2 ^ (k + 1) := by
  set M : ℕ := W k * ∏ i, Nat.lcm (d i) (e i) with hMdef
  obtain ⟨c, hcW, hclcm⟩ := hsol
  -- `M > 0`
  have hWpos : 0 < W k := Nat.pos_of_ne_zero (W_squarefree k).ne_zero
  have hprodpos : 0 < ∏ i, Nat.lcm (d i) (e i) := Finset.prod_pos (fun i _ => hlcmpos i)
  have hMpos : 0 < M := by rw [hMdef]; exact Nat.mul_pos hWpos hprodpos
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
  -- `W k` coprime to the product of coordinate moduli
  have hcopWprod : Nat.Coprime (W k) (∏ i, Nat.lcm (d i) (e i)) :=
    Nat.Coprime.prod_right (fun i _ => hcopW i)
  -- The heart: the filter predicate is equivalent to a single residue mod `M`.
  have hPiff : ∀ n : ℕ,
      (n % W k = ν₀ % W k ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (n + hSeq k i))
        ↔ n ≡ c [MOD M] := by
    intro n
    constructor
    · rintro ⟨hnW, hnlcm⟩
      have h1 : n ≡ c [MOD W k] := hnW.trans hcW.symm
      have h2 : ∀ i ∈ (Finset.univ : Finset (Fin k)),
          n ≡ c [MOD Nat.lcm (d i) (e i)] := by
        intro i _
        have hn0 : n + hSeq k i ≡ 0 [MOD Nat.lcm (d i) (e i)] :=
          Nat.modEq_zero_iff_dvd.mpr (hnlcm i)
        have hc0 : c + hSeq k i ≡ 0 [MOD Nat.lcm (d i) (e i)] :=
          Nat.modEq_zero_iff_dvd.mpr (hclcm i)
        exact Nat.ModEq.add_right_cancel' (hSeq k i) (hn0.trans hc0.symm)
      have h2prod : n ≡ c [MOD ∏ i, Nat.lcm (d i) (e i)] :=
        modEq_prod_of_pairwise_coprime _ Finset.univ
          (fun i _ j _ hij => hcoplcm i j hij) h2
      rw [hMdef]
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcopWprod).mp ⟨h1, h2prod⟩
    · intro hn
      have hWdvd : W k ∣ M := by rw [hMdef]; exact dvd_mul_right (W k) _
      have h1 : n ≡ c [MOD W k] := hn.of_dvd hWdvd
      refine ⟨(h1 : n % W k = c % W k).trans hcW, fun i => ?_⟩
      have hlcmdvdM : Nat.lcm (d i) (e i) ∣ M := by
        rw [hMdef]
        exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans (dvd_mul_left _ (W k))
      have hi : n ≡ c [MOD Nat.lcm (d i) (e i)] := hn.of_dvd hlcmdvdM
      have hc0 : c + hSeq k i ≡ 0 [MOD Nat.lcm (d i) (e i)] :=
        Nat.modEq_zero_iff_dvd.mpr (hclcm i)
      exact Nat.modEq_zero_iff_dvd.mp ((hi.add_right (hSeq k i)).trans hc0)
  -- Reduce the tuple count to a single-residue count.
  have hfilter : ∀ n : ℕ,
      (n % W k = ν₀ % W k ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (n + hSeq k i))
        ↔ n % M ∈ ({c % M} : Finset ℕ) := by
    intro n
    rw [Finset.mem_singleton]
    exact hPiff n
  have hCT : congCountTuple k K₀ N ν₀ d e
      = ((Finset.Ioc N (K₀ * N)).filter
          (fun n => n % M ∈ ({c % M} : Finset ℕ))).card := by
    unfold congCountTuple
    congr 1
    exact Finset.filter_congr (fun n _ => hfilter n)
  -- Interval decomposition: `Icc 1 (K₀N) = Icc 1 N ⊔ Ioc N (K₀N)`.
  have hNle : N ≤ K₀ * N := Nat.le_mul_of_pos_left N hK₀
  have hsplit : Finset.Icc 1 (K₀ * N) = Finset.Icc 1 N ∪ Finset.Ioc N (K₀ * N) := by
    ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Ioc N (K₀ * N)) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    simp only [Finset.mem_Icc] at hx; simp only [Finset.mem_Ioc] at hx'; omega
  have hadd : congCount M ({c % M}) (K₀ * N)
      = ((Finset.Ioc N (K₀ * N)).filter
          (fun n => n % M ∈ ({c % M} : Finset ℕ))).card
        + congCount M ({c % M}) N := by
    unfold congCount
    rw [hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint
        (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    omega
  -- Hence `congCountTuple = congCount(K₀N) - congCount(N)` over `ℝ`.
  have hcteq : (congCountTuple k K₀ N ν₀ d e : ℝ)
      = (congCount M ({c % M}) (K₀ * N) : ℝ) - (congCount M ({c % M}) N : ℝ) := by
    rw [hCT]
    have hcast : (congCount M ({c % M}) (K₀ * N) : ℝ)
        = (((Finset.Ioc N (K₀ * N)).filter
              (fun n => n % M ∈ ({c % M} : Finset ℕ))).card : ℝ)
          + (congCount M ({c % M}) N : ℝ) := by exact_mod_cast hadd
    linarith
  -- The singleton residue set meets `range M` in exactly one point.
  have hcardR : ((({c % M} : Finset ℕ) ∩ Finset.range M).card : ℝ) = 1 := by
    have hmem : c % M ∈ Finset.range M := Finset.mem_range.mpr (Nat.mod_lt _ hMpos)
    rw [Finset.singleton_inter_of_mem hmem, Finset.card_singleton]; norm_num
  -- The Brun bound at both endpoints.
  have hb1 := congCount_bound M ({c % M}) hMpos (K₀ * N)
  have hb2 := congCount_bound M ({c % M}) hMpos N
  rw [hcardR] at hb1 hb2
  set X : ℝ := (congCount M ({c % M}) (K₀ * N) : ℝ) - ↑(K₀ * N) * 1 / ↑M with hXdef
  set Y : ℝ := (congCount M ({c % M}) N : ℝ) - ↑N * 1 / ↑M with hYdef
  -- Triangle inequality gives the `± 2` bound.
  have hbound : |X - Y| ≤ 2 :=
    calc |X - Y| ≤ |X - 0| + |0 - Y| := abs_sub_le X 0 Y
      _ = |X| + |Y| := by rw [sub_zero, zero_sub, abs_neg]
      _ ≤ 1 + 1 := add_le_add hb1 hb2
      _ = 2 := by norm_num
  -- Identify the target discrepancy with `X - Y`.
  have hgoaleq : (congCountTuple k K₀ N ν₀ d e : ℝ) - ((K₀ - 1) * N : ℝ) / ↑M
      = X - Y := by
    rw [hcteq, hXdef, hYdef]
    push_cast
    field_simp
    ring
  rw [hgoaleq]
  -- Finally `2 ≤ 2^(k+1)`.
  have h2pow : (2 : ℝ) ≤ 2 ^ (k + 1) := by
    exact_mod_cast Nat.le_self_pow (Nat.succ_ne_zero k) 2
  exact hbound.trans h2pow

end Salt.Maynard
