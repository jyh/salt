/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.StepanovSolve
import Salt.Weil.PointCount
import Mathlib

/-!
# Weil track, Theorem 7 assembly: the Weil–Stepanov point-count bound (W-T7)

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder), following Harcos §5,
Theorem 7. This is the summit of the Stepanov face. It composes the one-sided Stepanov
count bound (`stepanov_one_sided_card_le`) for the two loci `N₀ ∪ N₁` and `N₀ ∪ N₋₁`
(characters `a = ±1`) with the elementary point-count identity `pointCount = q + ∑ χ(f)`
(`pointCount_sub_card`) and the counting glue (`pointCount_abs_sub_le`) to obtain the
`O_m(√q)` deviation bound
`|pointCount f − q| ≤ 8·(deg f)·(⌊√q⌋ + 1)` for `y² = f(x)`.

Parameter choice (Harcos, uniform-`D` variant): `ℓ := ⌊√q⌋ + 1`, `B := (q − m)/2`,
`J := ℓ/2 + 2m + 1`. Under `q ≥ 16 m²` the dimension count (`hcount`) fires and the
rounded division by `ℓ` collapses to the stated `√q`-shape. The constant `8` is not
load-bearing: the descent (Cor 3) consumes any explicit `C·m·√q`.

* `hcount_arith` / `final_arith`: the two `ℤ`-arithmetic facts (dimension count and the
  post-division bound) isolated from the counting glue.
* `weil_stepanov`: Theorem 7 itself.
-/

namespace Salt.Weil

open Polynomial Finset
open scoped BigOperators

variable {F : Type*} [Field F]

/-- **The dimension-count inequality** (Harcos p. 12) at the chosen parameters, over `ℤ`.
With `ℓ = s + 1`, `s = ⌊√q⌋` (`s·s ≤ q`), `4m ≤ s` (from `16m² ≤ q`), `B ≈ (q−m)/2`
(`q ≤ 2B + m + 1`) and `J ≈ ℓ/2 + 2m` (`2J` two-sided), the count `ℓ·D < 2·J·B` holds. -/
theorem hcount_arith {s m q B J : ℤ}
    (hs0 : 0 ≤ s) (hm : 1 ≤ m) (hB0 : 0 ≤ B)
    (hsq : s * s ≤ q) (h4m : 4 * m ≤ s) (hBhi : q ≤ 2 * B + m + 1)
    (hJlo : (s + 1) + 4 * m + 1 ≤ 2 * J) (hJhi : 2 * J ≤ (s + 1) + 4 * m + 2) :
    (s + 1) * (B + s * (m - 1) + J) < 2 * (J * B) := by
  have hm0 : (0:ℤ) ≤ m := by linarith
  have hm1 : (0:ℤ) ≤ m - 1 := by linarith
  have h4ms : (0:ℤ) ≤ s - 4 * m := by linarith
  have hJk : (0:ℤ) ≤ 2 * J - (s + 1) - 4 * m - 1 := by linarith
  nlinarith [mul_nonneg h4ms hm0, mul_nonneg h4ms hs0, mul_nonneg h4ms hm1,
    mul_nonneg hB0 hJk, mul_nonneg hs0 hm1, mul_nonneg hs0 hm0,
    mul_nonneg hs0 hs0, mul_nonneg hB0 hm1, mul_nonneg hB0 hm0,
    mul_nonneg (by linarith : (0:ℤ) ≤ q - s * s) hm0, mul_nonneg hm1 hs0]

/-- **The post-division bound** (Harcos (13) → Theorem 7), over `ℤ`. Twice the one-sided
degree bound `R = ℓm + B + em + (J−1)q` is `≤ ℓq + 8mℓ²`, so `2⌊R/ℓ⌋ − q ≤ 8mℓ`. Uses
`q < ℓ²`, `2B + m ≤ q`, `2e + 1 = q` (q odd) and `2(J−1) ≤ ℓ + 4m`. -/
theorem final_arith {m q lu B J e : ℤ}
    (hm : 1 ≤ m) (hl : 1 ≤ lu) (he0 : 0 ≤ e) (hJ1 : 1 ≤ J)
    (hqu : q < lu * lu) (hBlo : 2 * B + m ≤ q) (he : 2 * e + 1 = q)
    (hJhi : 2 * (J - 1) ≤ lu + 4 * m) :
    2 * (lu * m + B + e * m + (J - 1) * q) ≤ lu * q + 8 * m * (lu * lu) := by
  have hm0 : (0:ℤ) ≤ m := by linarith
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ lu * lu - q) hm0,
    mul_nonneg (by linarith : (0:ℤ) ≤ lu - 1) hm0,
    mul_le_mul_of_nonneg_left hBlo (by linarith : (0:ℤ) ≤ lu),
    mul_nonneg he0 hm0]

/-! ### Theorem 7 — the Weil–Stepanov point count for `y² = f(x)` -/

/-- **Theorem 7 (Weil–Stepanov).** For `q = #F` odd, `f` a non-square (in the algebraic
closure) with `f(0) ≠ 0`, `deg f ≥ 1` and `q ≥ 16·(deg f)²`, the hyperelliptic point count
`N = #{(x, y) : y² = f(x)}` deviates from `q` by `O_m(√q)`:
`|N − q| ≤ 8·(deg f)·(⌊√q⌋ + 1)`. Assembled from the two one-sided Stepanov bounds
(`stepanov_one_sided_card_le` at `a = ±1`), the fibre identity `N = q + ∑ₓ χ(f(x))`
(`pointCount_sub_card`) and the counting glue (`pointCount_abs_sub_le`). -/
theorem weil_stepanov [Fintype F] (f : F[X])
    (hqodd : Odd (Fintype.card F)) (hm : 1 ≤ f.natDegree) (hf0 : f.coeff 0 ≠ 0)
    (hns : ¬ ∃ g : (AlgebraicClosure F)[X],
      f.map (algebraMap F (AlgebraicClosure F)) = g ^ 2)
    (hq : 16 * f.natDegree ^ 2 ≤ Fintype.card F) :
    |(pointCount f : ℤ) - Fintype.card F|
      ≤ 8 * f.natDegree * (Nat.sqrt (Fintype.card F) + 1) := by
  classical
  have hF : ringChar F ≠ 2 := by
    intro h; have := FiniteField.even_card_of_char_two h
    rcases hqodd with ⟨k, hk⟩; omega
  have hf : f ≠ 0 := fun h => hf0 (by rw [h, coeff_zero])
  have hqm : Fintype.card F % 2 = 1 := Nat.odd_iff.mp hqodd
  set s := Nat.sqrt (Fintype.card F) with hs_def
  set ℓ := s + 1 with hℓ_def
  set e := (Fintype.card F - 1) / 2 with he_def
  set B := (Fintype.card F - f.natDegree) / 2 with hB_def
  set J := ℓ / 2 + 2 * f.natDegree + 1 with hJ_def
  set R := ℓ * f.natDegree + (B + e * f.natDegree + (J - 1) * Fintype.card F) with hR_def
  set Bp := R / ℓ with hBp_def
  -- parameter facts (ℕ)
  have hmq : f.natDegree + 2 ≤ Fintype.card F := by nlinarith [hq, hm]
  have hsq : s * s ≤ Fintype.card F := by rw [hs_def]; exact Nat.sqrt_le _
  have h4m : 4 * f.natDegree ≤ s := by
    rw [hs_def]; exact Nat.le_sqrt.mpr (by nlinarith [hq])
  have hℓq : ℓ ≤ Fintype.card F := by
    rw [hℓ_def, hs_def]
    have := Nat.sqrt_lt_self (show 1 < Fintype.card F by omega); omega
  have hqlt : Fintype.card F < ℓ * ℓ := by
    rw [hℓ_def, hs_def]; exact Nat.lt_succ_sqrt _
  have hℓpos : 0 < ℓ := by omega
  have hB1 : 1 ≤ B := by rw [hB_def]; omega
  have hB : B ≤ (Fintype.card F - f.natDegree) / 2 := hB_def.le
  have hBhi : Fintype.card F ≤ 2 * B + f.natDegree + 1 := by rw [hB_def]; omega
  have hBlo : 2 * B + f.natDegree ≤ Fintype.card F := by rw [hB_def]; omega
  have hJlo : s + 1 + 4 * f.natDegree + 1 ≤ 2 * J := by rw [hJ_def, hℓ_def]; omega
  have hJhi : 2 * J ≤ s + 1 + 4 * f.natDegree + 2 := by rw [hJ_def, hℓ_def]; omega
  have hJ1 : 1 ≤ J := by rw [hJ_def]; omega
  -- the dimension count (ℕ)
  have hcount : ℓ * (B + (ℓ - 1) * (f.natDegree - 1) + J) < 2 * (J * B) := by
    rw [hℓ_def, Nat.add_sub_cancel]
    zify [hm]
    exact hcount_arith (s := (s:ℤ)) (m := (f.natDegree:ℤ)) (q := (Fintype.card F:ℤ))
      (B := (B:ℤ)) (J := (J:ℤ)) (by positivity) (by exact_mod_cast hm) (by positivity)
      (by exact_mod_cast hsq) (by exact_mod_cast h4m) (by exact_mod_cast hBhi)
      (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
  -- the character sum and the partition
  have hsum : ∑ x : F, quadraticChar F (f.eval x)
      = ((univ.filter (fun x : F => quadraticChar F (f.eval x) = 1)).card : ℤ)
        - (univ.filter (fun x : F => quadraticChar F (f.eval x) = -1)).card := by
    rw [← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => by
      rcases quadraticChar_isQuadratic F (f.eval x) with h | h | h <;> simp [h])
  have hpart : ((univ.filter (fun x : F => quadraticChar F (f.eval x) = 0)).card : ℤ)
        + (univ.filter (fun x : F => quadraticChar F (f.eval x) = 1)).card
        + (univ.filter (fun x : F => quadraticChar F (f.eval x) = -1)).card
        = Fintype.card F := by
    have hone : (Fintype.card F : ℤ) = ∑ _x : F, (1:ℤ) := by simp [Finset.card_univ]
    rw [hone, ← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_boole,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => by
      rcases quadraticChar_isQuadratic F (f.eval x) with h | h | h <;> simp [h])
  -- the two one-sided bounds
  have onesided : ∀ (a : F) (c : ℤ), (c = 1 ∨ c = -1) → ((c : F) = a) →
      (univ.filter (fun x : F => quadraticChar F (f.eval x) = 0)).card
        + (univ.filter (fun x : F => quadraticChar F (f.eval x) = c)).card ≤ Bp := by
    intro a c hc hca
    have hdisj : Disjoint (univ.filter (fun x : F => quadraticChar F (f.eval x) = 0))
        (univ.filter (fun x : F => quadraticChar F (f.eval x) = c)) := by
      rw [Finset.disjoint_left]; intro x hx0 hxc
      have h0 := (Finset.mem_filter.mp hx0).2
      have hcc := (Finset.mem_filter.mp hxc).2
      rw [h0] at hcc
      rcases hc with h | h <;> · rw [h] at hcc; exact absurd hcc (by norm_num)
    have hT : ∀ x ∈ (univ.filter (fun x : F => quadraticChar F (f.eval x) = 0))
          ∪ (univ.filter (fun x : F => quadraticChar F (f.eval x) = c)),
        f.eval x = 0 ∨ (f.eval x) ^ ((Fintype.card F - 1) / 2) = a := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx0 | hxc
      · exact Or.inl (quadraticChar_eq_zero_iff.mp (Finset.mem_filter.mp hx0).2)
      · right
        have hcx : quadraticChar F (f.eval x) = c := (Finset.mem_filter.mp hxc).2
        have hpow := quadraticChar_eq_pow_of_char_ne_two' hF (f.eval x)
        rw [hcx] at hpow
        rw [show (Fintype.card F - 1) / 2 = Fintype.card F / 2 from by omega, ← hpow, hca]
    have hstep : ℓ * ((univ.filter (fun x : F => quadraticChar F (f.eval x) = 0))
          ∪ (univ.filter (fun x : F => quadraticChar F (f.eval x) = c))).card ≤ R :=
      stepanov_one_sided_card_le (ℓ := ℓ) (J := J) (B := B) f hf hm a hB1 hℓq hqodd hf0 hB
        hns hcount _ hT
    rw [Finset.card_union_of_disjoint hdisj] at hstep
    rw [hBp_def]
    exact (Nat.le_div_iff_mul_le hℓpos).mpr (by rw [Nat.mul_comm]; exact hstep)
  have hb1 := onesided (1:F) (1:ℤ) (Or.inl rfl) (by norm_num)
  have hbm := onesided (-1:F) (-1:ℤ) (Or.inr rfl) (by norm_num)
  -- the point-count deviation
  have hpc : (pointCount f : ℤ) - Fintype.card F
      = ((univ.filter (fun x : F => quadraticChar F (f.eval x) = 1)).card : ℤ)
        - (univ.filter (fun x : F => quadraticChar F (f.eval x) = -1)).card := by
    rw [pointCount_sub_card f hF, hsum]; ring
  -- discharge `2·⌊R/ℓ⌋ − q ≤ 8·m·ℓ`
  -- make the nested `set` parameters opaque so the final `nlinarith` does not
  -- unfold them (avoids a `whnf` heartbeat blow-up).
  clear_value Bp R J B e ℓ s
  have hℓs : (ℓ : ℤ) = (s : ℤ) + 1 := by rw [hℓ_def]; push_cast; ring
  have hdiv : (Bp : ℤ) * ℓ ≤ R := by rw [hBp_def]; exact_mod_cast Nat.div_mul_le_self R ℓ
  have h2R : 2 * (R : ℤ) ≤ (ℓ:ℤ) * (Fintype.card F : ℤ)
      + 8 * (f.natDegree : ℤ) * ((ℓ:ℤ) * ℓ) := by
    have hfin := final_arith (m := (f.natDegree:ℤ)) (q := (Fintype.card F:ℤ)) (lu := (ℓ:ℤ))
      (B := (B:ℤ)) (J := (J:ℤ)) (e := (e:ℤ))
      (by exact_mod_cast hm) (by exact_mod_cast (show 1 ≤ ℓ from by omega)) (by positivity)
      (by exact_mod_cast hJ1) (by exact_mod_cast hqlt) (by exact_mod_cast hBlo)
      (by exact_mod_cast (show 2 * e + 1 = Fintype.card F from by rw [he_def]; omega))
      (by exact_mod_cast (show 2 * (J - 1) ≤ ℓ + 4 * f.natDegree from by
        rw [hJ_def, hℓ_def]; omega))
    rw [hR_def]; push_cast [Nat.cast_sub hJ1]; nlinarith [hfin]
  have hfinal : 2 * (Bp:ℤ) - (Fintype.card F : ℤ) ≤ 8 * (f.natDegree : ℤ) * ℓ := by
    refine le_of_mul_le_mul_left ?_ (show (0:ℤ) < ℓ by exact_mod_cast hℓpos)
    have e1 : (ℓ:ℤ) * (2 * (Bp:ℤ) - (Fintype.card F : ℤ))
        = 2 * ((Bp:ℤ) * ℓ) - (ℓ:ℤ) * (Fintype.card F : ℤ) := by ring
    have e2 : (ℓ:ℤ) * (8 * (f.natDegree : ℤ) * ℓ)
        = 8 * (f.natDegree : ℤ) * ((ℓ:ℤ) * ℓ) := by ring
    rw [e1, e2]; linarith [hdiv, h2R]
  rw [hℓs] at hfinal
  have hb1' : ((univ.filter (fun x : F => quadraticChar F (f.eval x) = 0)).card : ℤ)
      + (univ.filter (fun x : F => quadraticChar F (f.eval x) = 1)).card ≤ (Bp : ℤ) := by
    exact_mod_cast hb1
  have hbm' : ((univ.filter (fun x : F => quadraticChar F (f.eval x) = 0)).card : ℤ)
      + (univ.filter (fun x : F => quadraticChar F (f.eval x) = -1)).card ≤ (Bp : ℤ) := by
    exact_mod_cast hbm
  have habs := pointCount_abs_sub_le (B := (Bp:ℤ)) hpart (Int.natCast_nonneg _) hb1' hbm'
  rw [hpc]
  exact le_trans habs hfinal

end Salt.Weil
