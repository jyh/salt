/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehSmallQ
import Salt.Maynard.GehDecomp

/-!
# Closing the small-modulus Type-II obligation (node SMALLQ-2)

Design: `docs/exploration/s3-a3-design.md` (the N-SMALLQ ruling + THE GIFT).  The
small-`q` Type-II Siegel–Walfisz floor `SmallQTypeII M V 3`
(`Salt/Maynard/GehSW.lean`), at the AMENDED definition carrying the
polynomial-scale guard `x^{1/3} ≤ V x`, is discharged from
`Salt.SW.siegelWalfisz_holds`.

## THE GIFT (kills the CRT machinery)

The residue-class reindex of the Type-II block replaces `n` by `n = m·c` with `c`
the large divisor and `m` its cofactor.  In the class `n ≡ a (mod q)` with
`gcd(a,q)=1`, the cofactor `m` is FORCED coprime to `q`:

* **`smallQ_class_vanish`** — if `gcd(a,q)=1` but `¬ gcd(m,q)=1`, then NO `c`
  satisfies `(m·c) % q = a`.  So `gcd(m,q) > 1` cofactors contribute zero; the
  CRT solvability split is unnecessary.
* **`smallQ_class_reindex`** — for `gcd(m,q)=1`, the class `(m·c) % q = a % q`
  is the single reduced class `c % q = b` with `b = m⁻¹ a (mod q)` (again a
  reduced residue).  So the inner `c`-sum is a clean `ψ`-in-AP window at a shifted
  residue — exactly the shape `siegelWalfisz_holds` bounds.

Both are proven here, sorry-free, via the `ZMod q` unit calculus.
-/

open Finset ArithmeticFunction

namespace Salt.Maynard

/-- **THE GIFT, part 1 — class vanishing.**  Let `a` be a reduced residue mod `q`
(`Nat.Coprime a q`).  If the cofactor `m` is *not* coprime to `q` then the product
`m·c` never lands in the class `a`: `(m * c) % q ≠ a`.  Consequently, in the
Type-II residue reindex, every `gcd(m,q) > 1` cofactor contributes zero to the
`n ≡ a (q)` class sum — the CRT solvability machinery of the original plan is
unnecessary. -/
theorem smallQ_class_vanish {q a m : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q)
    (hm : ¬ Nat.Coprime m q) (c : ℕ) : (m * c) % q ≠ a := by
  haveI : NeZero q := ⟨hq.ne'⟩
  intro h
  have hau : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hmc : (m : ZMod q) * (c : ZMod q) = (a : ZMod q) := by
    rw [← Nat.cast_mul, ← ZMod.natCast_mod (m * c) q, h]
  have hunit : IsUnit ((m : ZMod q) * (c : ZMod q)) := by rw [hmc]; exact hau
  exact hm ((ZMod.isUnit_iff_coprime m q).mp (isUnit_of_mul_isUnit_left hunit))

/-- **THE GIFT, part 2 — class reindex.**  Let `a` be a reduced residue mod `q`
and let the cofactor `m` be coprime to `q`.  Then the class `(m·c) % q = a % q`
is the SINGLE reduced class `c % q = b`, where `b = m⁻¹ a (mod q)` is again a
reduced residue (`b < q`, `Nat.Coprime b q`).  So the inner `c`-sum over the
`n ≡ a (q)` residues reindexes as a clean `ψ`-in-AP window at the shifted residue
`b` — no CRT solvability split, no modulus change: the reduction is the
`m⁻¹`-bijection at the SAME modulus `q`. -/
theorem smallQ_class_reindex {q a m : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q)
    (hmq : Nat.Coprime m q) :
    ∃ b : ℕ, b < q ∧ Nat.Coprime b q ∧
      ∀ c : ℕ, ((m * c) % q = a % q ↔ c % q = b) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hmu : IsUnit (m : ZMod q) := (ZMod.isUnit_iff_coprime m q).mpr hmq
  have hau : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  set u : ZMod q := (m : ZMod q) with hu
  set bz : ZMod q := u⁻¹ * (a : ZMod q) with hbz
  have hbval : ((bz.val : ℕ) : ZMod q) = bz := by rw [ZMod.natCast_val, ZMod.cast_id]
  have huinv : IsUnit u⁻¹ :=
    ⟨⟨u⁻¹, u, ZMod.inv_mul_of_unit u hmu, ZMod.mul_inv_of_unit u hmu⟩, rfl⟩
  refine ⟨bz.val, ZMod.val_lt bz, ?_, ?_⟩
  · have hbu : IsUnit bz := by rw [hbz]; exact huinv.mul hau
    rw [← ZMod.isUnit_iff_coprime, hbval]; exact hbu
  · intro c
    constructor
    · intro h
      have hz : (m : ZMod q) * (c : ZMod q) = (a : ZMod q) := by
        rw [← Nat.cast_mul]; exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
      have hcz : (c : ZMod q) = bz := by
        rw [hbz, ← hz, ← hu, ← mul_assoc, ZMod.inv_mul_of_unit u hmu, one_mul]
      have hcast : ((c : ℕ) : ZMod q) = ((bz.val : ℕ) : ZMod q) := by rw [hcz, hbval]
      have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
      rwa [Nat.ModEq, Nat.mod_eq_of_lt (ZMod.val_lt bz)] at hmod
    · intro h
      have hcz : (c : ZMod q) = bz := by
        rw [← ZMod.natCast_mod c q, h, hbval]
      have hz : (m : ZMod q) * (c : ZMod q) = (a : ZMod q) := by
        rw [hcz, hbz, ← hu, ← mul_assoc, ZMod.mul_inv_of_unit u hmu, one_mul]
      rw [← Nat.cast_mul] at hz
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hz

/-! ## Reduction to per-cofactor discrepancies -/

/-- The `m`-cofactor slice of the `r`-twisted Type-II block weight.  Under the
divisor reindex `n = m·c` the divisor `c = n/m` (with `c > V x`) contributes
`Λ(n/m)` when `n` lies in the block `Ioc (M x) (2 M x)` and is coprime to `r`.
Summing over `m ∈ Icc 1 x` recovers the block weight
(`smallQ_block_eq_sum_cofactor`), so `seqDiscrepancy_sum_le` splits the block
discrepancy into per-cofactor pieces. -/
noncomputable def smallQCofactor (M V : ℕ → ℕ) (r x m n : ℕ) : ℝ :=
  if m ∣ n ∧ V x < n / m ∧ n ∈ Finset.Ioc (M x) (2 * M x) ∧ Nat.Coprime n r then
    Λ (n / m) else 0

/-- **The pointwise cofactor decomposition.**  For `n ∈ Icc 1 x`, the `r`-twisted
Type-II block weight equals the sum of its cofactor slices over `m ∈ Icc 1 x`.
Divisor double-counting: the divisors `m ∣ n` are exactly `Icc 1 x ∩ {m ∣ n}`
(as `n ≤ x`), and `∑_{m ∣ n} Λ(n/m) [V x < n/m] = ∑_{c ∣ n} Λ c [V x < c]` by the
`c ↦ n/c` divisor bijection (`Nat.sum_div_divisors`). -/
theorem smallQ_block_eq_sum_cofactor (M V : ℕ → ℕ) (r x n : ℕ)
    (hn : n ∈ Finset.Icc 1 x) :
    (if Nat.Coprime n r then
        (if n ∈ Finset.Ioc (M x) (2 * M x) then Salt.LS.typeIIData (V x) n else 0) else 0)
      = ∑ m ∈ Finset.Icc 1 x, smallQCofactor M V r x m n := by
  rw [Finset.mem_Icc] at hn
  obtain ⟨hn1, hnx⟩ := hn
  by_cases hcop : Nat.Coprime n r
  · by_cases hIoc : n ∈ Finset.Ioc (M x) (2 * M x)
    · have hRHS : ∑ m ∈ Finset.Icc 1 x, smallQCofactor M V r x m n
          = ∑ m ∈ (Finset.Icc 1 x).filter (fun m => m ∣ n ∧ V x < n / m), Λ (n / m) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        unfold smallQCofactor
        by_cases hc : m ∣ n ∧ V x < n / m
        · rw [if_pos ⟨hc.1, hc.2, hIoc, hcop⟩, if_pos hc]
        · rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩), if_neg hc]
      have hfilter : (Finset.Icc 1 x).filter (fun m => m ∣ n ∧ V x < n / m)
          = n.divisors.filter (fun m => V x < n / m) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨_, _⟩, hmdvd, hlt⟩
          exact ⟨⟨hmdvd, by omega⟩, hlt⟩
        · rintro ⟨⟨hmdvd, _⟩, hlt⟩
          have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos hmdvd (by omega)
          have hmn : m ≤ n := Nat.le_of_dvd (by omega) hmdvd
          exact ⟨⟨hm1, by omega⟩, hmdvd, hlt⟩
      rw [if_pos hcop, if_pos hIoc, hRHS, hfilter, Salt.LS.typeIIData, Finset.sum_filter,
        ← Nat.sum_div_divisors n (fun c => if V x < c then Λ c else 0), ← Finset.sum_filter]
    · rw [if_pos hcop, if_neg hIoc]
      refine (Finset.sum_eq_zero (fun m _ => ?_)).symm
      unfold smallQCofactor
      rw [if_neg]; rintro ⟨_, _, h, _⟩; exact hIoc h
  · rw [if_neg hcop]
    refine (Finset.sum_eq_zero (fun m _ => ?_)).symm
    unfold smallQCofactor
    rw [if_neg]; rintro ⟨_, _, _, h⟩; exact hcop h

/-- **The per-cofactor reduction.**  The `r`-twisted Type-II block discrepancy is
bounded by the sum over cofactors `m ∈ Icc 1 x` of the per-cofactor
discrepancies, via `seqDiscrepancy_sum_le` on the pointwise decomposition.  Each
`m`-term is a `Λ`-in-AP window discrepancy that `siegelWalfisz_holds` bounds —
after the two gift lemmas identify its residue class (`smallQ_class_vanish`,
`smallQ_class_reindex`). -/
theorem seqDiscrepancy_block_le_sum_cofactor (M V : ℕ → ℕ) (r x q : ℕ) :
    seqDiscrepancy (fun n => if Nat.Coprime n r then
        (if n ∈ Finset.Ioc (M x) (2 * M x) then Salt.LS.typeIIData (V x) n else 0)
        else 0) x q
      ≤ ∑ m ∈ Finset.Icc 1 x, seqDiscrepancy (smallQCofactor M V r x m) x q := by
  rw [seqDiscrepancy_congr_Icc q
    (fun n hn => smallQ_block_eq_sum_cofactor M V r x n hn)]
  exact seqDiscrepancy_sum_le (Finset.Icc 1 x) (fun m n => smallQCofactor M V r x m n) x q

end Salt.Maynard
