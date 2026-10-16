/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.MaynardK.Miller
import SaltC1.MaynardK.Keys54

/-!
# C1 · A2d (a) — the certificate's series tables are the coefficients of `GM 13 ^ 54`, `GM 13 ^ 53`

`p54T_eq`: on every key of weight `≤ 46`, `p54T` holds `[x^C] GM 13 ^ 54`; `p53T_eq`: on weight
`≤ 48`, `p53T` holds `[x^C] GM 13 ^ 53`. The route (the brief's E3-2 (a)): `g46_ok` + `fact_ok` say
`gT46` holds `[x^A] GM 13` (`gT_eq`, `checkG` is `gN`'s defining equation); `rec54_ok` says `p54T`
satisfies the Miller recurrence at every key of weight `≤ 46` (`rec_of_check`, the certificate's
`boxL` read as `tuplesLE`); `p54_zero` is the constant term; and `eq_coeff_pow_of_rec` (the
uniqueness of `Miller`) closes. No table is reduced: every fact enters through a committed
certificate theorem. Nothing here bears on twin primes.
-/

open Finset
open scoped Nat

namespace SaltC1.MaynardK

open Salt.MaynardK SaltC1.Cert54

attribute [local irreducible] p54T p53T gT46 gT48 factT

/-- `Finsupp.equivFunOnFinite.symm`, the exponent of a tuple. -/
local notation "eF" => Finsupp.equivFunOnFinite.symm

lemma constantCoeff_GM (M : ℕ) : MvPowerSeries.constantCoeff (GM M) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_GM]
  simp [weight]

lemma enc_zero {M : ℕ} : enc (0 : Fin M → ℕ) = 0 := by
  simp [enc]

/-! ## (i) `checkG` is `gN`'s equation -/

/-- A table passing `checkG` on `keysW 13 w` (`w ≤ 101`) holds `[x^A] GM 13` there. -/
lemma gT_eq (t : BST) (w : ℕ) (hw : w ≤ 101) (hg : checkAllL (checkG t) (keysW 13 w) = true)
    (A : Fin 13 → ℕ) (hA : weight A ≤ w) :
    ((t.findB (enc A) : ℤ) : ℚ) = MvPowerSeries.coeff (eF A) (GM 13) := by
  have h := (List.all_eq_true.mp hg) (List.ofFn A) (mem_keysW.mpr hA)
  unfold checkG at h
  rw [beq_iff_eq, encKey_zero_ofFn, wt_ofFn,
    facProd_ofFn_eq A (fun m => by have := two_mul_le_weight A m; omega),
    factT_eq _ (by omega)] at h
  rw [coeff_GM]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  have hP : (∏ m, (((A m)! : ℕ) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun m _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [eq_div_iff hP]
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  exact hq

/-! ## The recurrence, read from `checkRecGen` -/

/-- `checkRecGen` at `List.ofFn C` is the Miller recurrence over `boxM C`. -/
lemma rec_of_check (p g : BST) (k w : ℕ)
    (h : checkAllL (checkRecGen p g k) (keysW 13 w) = true) (C : Fin 13 → ℕ) (hC : weight C ≤ w) :
    (weight C : ℚ) * ((p.findB (enc C) : ℤ) : ℚ)
      = ∑ A ∈ boxM C, if A = 0 then 0 else
          ((k : ℚ) * (weight A : ℚ) - (weight (C - A) : ℚ)) * ((g.findB (enc A) : ℤ) : ℚ) *
            ((p.findB (enc (C - A)) : ℤ) : ℚ) := by
  have hc := (List.all_eq_true.mp h) (List.ofFn C) (mem_keysW.mpr hC)
  unfold checkRecGen at hc
  set G : List ℕ → ℤ := fun a => if allZero a = true then 0 else
    (((k * wt a : ℕ) : ℤ) - ((wt (subL (List.ofFn C) a) : ℕ) : ℤ)) * g.findB (encKey 0 a) *
      p.findB (encKey 0 (subL (List.ofFn C) a)) with hG
  rw [foldl_add_of _ G (fun acc a => by
      rw [hG]
      cases hz : allZero a <;> simp only [hz] <;> simp)] at hc
  rw [zero_add, beq_iff_eq, boxL_ofFn, List.map_map, sum_tuplesLE, wt_ofFn, encKey_zero_ofFn] at hc
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hc
  push_cast at hq
  rw [← hq]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [hG, Function.comp_apply, allZero_ofFn, wt_ofFn, subL_ofFn, encKey_zero_ofFn]
  split_ifs <;> push_cast <;> ring

/-! ## (a) The two series tables -/

/-- **`p54T` is `[x^·] GM 13 ^ 54` on the keys of weight `≤ 46`.** -/
theorem p54T_eq (C : Fin 13 → ℕ) (hC : weight C ≤ 46) :
    ((p54T.findB (enc C) : ℤ) : ℚ) = MvPowerSeries.coeff (eF C) (GM 13 ^ 54) :=
  eq_coeff_pow_of_rec (GM 13) (constantCoeff_GM 13) 54 46
    (fun C => ((p54T.findB (enc C) : ℤ) : ℚ)) (fun A => ((gT46.findB (enc A) : ℤ) : ℚ))
    (by simp only [enc_zero, p54_zero, Int.cast_one])
    (fun A hA => gT_eq gT46 46 (by norm_num) g46_ok A hA)
    (fun C hC => by exact_mod_cast rec_of_check p54T gT46 54 46 rec54_ok C hC) C hC

/-- **`p53T` is `[x^·] GM 13 ^ 53` on the keys of weight `≤ 48`.** -/
theorem p53T_eq (C : Fin 13 → ℕ) (hC : weight C ≤ 48) :
    ((p53T.findB (enc C) : ℤ) : ℚ) = MvPowerSeries.coeff (eF C) (GM 13 ^ 53) :=
  eq_coeff_pow_of_rec (GM 13) (constantCoeff_GM 13) 53 48
    (fun C => ((p53T.findB (enc C) : ℤ) : ℚ)) (fun A => ((gT48.findB (enc A) : ℤ) : ℚ))
    (by simp only [enc_zero, p53_zero, Int.cast_one])
    (fun A hA => gT_eq gT48 48 (by norm_num) g48_ok A hA)
    (fun C hC => by exact_mod_cast rec_of_check p53T gT48 53 48 rec53_ok C hC) C hC

/-- `p54T_eq` with the certificate's list key (`List.ofFn C`, A3 of math's freeze). -/
theorem p54T_eq' (C : Fin 13 → ℕ) (hC : weight C ≤ 46) :
    ((p54T.findB (encKey 0 (List.ofFn C)) : ℤ) : ℚ)
      = MvPowerSeries.coeff (eF C) (GM 13 ^ 54) := by
  rw [encKey_zero_ofFn]
  exact p54T_eq C hC

/-- `p53T_eq` with the certificate's list key. -/
theorem p53T_eq' (C : Fin 13 → ℕ) (hC : weight C ≤ 48) :
    ((p53T.findB (encKey 0 (List.ofFn C)) : ℤ) : ℚ)
      = MvPowerSeries.coeff (eF C) (GM 13 ^ 53) := by
  rw [encKey_zero_ofFn]
  exact p53T_eq C hC

end SaltC1.MaynardK
