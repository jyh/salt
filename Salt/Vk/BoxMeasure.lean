/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.BoxAvg
import Salt.Vmvt.HolderTwo

/-!
# VMVT-VK rung R3-measure — the disjoint-box → `Jk` measure fold (`VK-BOX-AVG`)

This is the heart of R3: folding a family of `Y` disjoint coordinate boxes in the torus
`[0,1]^{Deg k}` into `torusMeasure` and comparing the pointwise `2b`-moment of `genFun`
at the box centers with the mean value `Jk` (via `integral_norm_pow_eq_Jk`, RIGHT-to-LEFT).

Two theorems:

* `vk_box_disjoint_avg` — the **abstract fold**: given `Y` pairwise-disjoint measurable
  boxes, each of `torusMeasure`-mass `≥ ∏_j δ_j`, with `genFun` at the center `c y`
  dominated on the box up to a uniform Slack `S`, the summed center-moments obey
  `∑_y ‖genFun(c y)‖^{2b} ≤ 2^{2b−1}((∏δ)⁻¹·Jk + Y·S^{2b})`.  The measure-theoretic core:
  disjoint-union integral additivity (`integral_iUnion_fintype`), set-integral monotonicity
  into the full torus (`setIntegral_le_integral`), the const-lower bound
  (`setIntegral_ge_of_const_le_real`), and the convexity `add_pow_le`.

* `vk_box_disjoint_avg_of_centers` — the **from-centers form**: the clipped-box construction
  `vkBox` folds the mod-1 bookkeeping into an elementary per-coordinate clipping bound.  The
  inner half of each coordinate interval always survives clipping to `(0,1]`, so each box
  keeps mass `≥ ∏δ` (exactly the lower bound the fold needs — no torus translation invariance
  is required).  Disjointness comes from the `j₀`-coordinate separation alone (clipped boxes
  are subsets of the unclipped, separated ones).  Variation is the landed
  `genFun_box_variation`.

Also lands `genFun_add_int` — `genFun`'s 1-periodicity in each coordinate (the polynomial
phase gains an integer, absorbed by `eR(ℤ) = 1`), the tool R4 uses to reduce orbit centers
into `[0,1)^k` before boxing.
-/

namespace Salt.Vk

open Finset Real MeasureTheory Salt.ExpSum Salt.Vmvt
open scoped BigOperators

/-! ## `genFun` 1-periodicity -/

/-- `eR (m : ℝ) = 1` for integer `m`. -/
lemma eR_intCast (m : ℤ) : eR ((m : ℝ)) = 1 := by
  rw [Salt.ExpSum.eR]
  have h : (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ))
      = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [h]; exact_mod_cast Complex.exp_int_mul_two_pi_mul_I m

/-- **genFun 1-periodicity.**  Shifting each coordinate by an integer leaves `genFun`
unchanged (the polynomial phase gains an integer, absorbed by `eR(ℤ)=1`). -/
lemma genFun_add_int (k : ℕ) (A : Finset ℤ) (α : Deg k → ℝ) (z : Deg k → ℤ) :
    genFun k A (fun j => α j + (z j : ℝ)) = genFun k A α := by
  rw [genFun_eq_eR_sum, genFun_eq_eR_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hsplit : ∑ j : Deg k, (α j + (z j : ℝ)) * (n : ℝ) ^ (j : ℕ)
      = (∑ j : Deg k, α j * (n : ℝ) ^ (j : ℕ))
        + ((∑ j : Deg k, z j * n ^ (j : ℕ) : ℤ) : ℝ) := by
    push_cast
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsplit, eR_add, eR_intCast, mul_one]

/-! ## The abstract disjoint-box fold -/

/-- **R3-measure: the disjoint-box → `Jk` measure fold.**  Given `Y` pairwise-disjoint
measurable boxes in the torus, each of `torusMeasure`-mass at least `∏_j δ_j > 0`, with
`genFun` at the box center `c y` dominated by its value on the box up to a uniform Slack
`S`, the summed `2b`-moments at the centers are controlled by the mean value
`Jk k b (Ioc 0 P)` (via `integral_norm_pow_eq_Jk`, RIGHT-to-LEFT). -/
theorem vk_box_disjoint_avg (k b P Y : ℕ)
    (c : Fin Y → (Deg k → ℝ)) (δ : Deg k → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (box : Fin Y → Set (Deg k → ℝ))
    (hmeas : ∀ y, MeasurableSet (box y))
    (hdisj : Pairwise (Function.onFun Disjoint box))
    (hδpos : 0 < ∏ j : Deg k, δ j)
    (hlow : ∀ y, (∏ j : Deg k, δ j) ≤ (torusMeasure k).real (box y))
    (hvar : ∀ y, ∀ α ∈ box y,
       ‖genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) (c y)‖
         ≤ ‖genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) α‖ + S) :
    ∑ y : Fin Y, ‖genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) (c y)‖ ^ (2 * b)
      ≤ 2 ^ (2 * b - 1) * ((∏ j : Deg k, δ j)⁻¹ * (Jk k b (Finset.Ioc (0 : ℤ) (P : ℤ)) : ℝ)
          + (Y : ℝ) * S ^ (2 * b)) := by
  classical
  set A : Finset ℤ := Finset.Ioc (0 : ℤ) (P : ℤ) with hA
  set F : (Deg k → ℝ) → ℝ := fun α => ‖genFun k A α‖ ^ (2 * b) with hFdef
  set D : ℝ := ∏ j : Deg k, δ j with hDdef
  set τ : Measure (Deg k → ℝ) := torusMeasure k with hτ
  have hFint : Integrable F τ := integrable_norm_genFun_pow k P (2 * b)
  have hFnn : ∀ α, 0 ≤ F α := fun α => by rw [hFdef]; positivity
  set I : Fin Y → ℝ := fun y => ∫ α in box y, F α ∂τ with hIdef
  have hI_nn : ∀ y, 0 ≤ I y := by
    intro y; rw [hIdef]
    exact setIntegral_nonneg (hmeas y) (fun α _ => hFnn α)
  -- the per-box pointwise-to-integral bound
  have hpery : ∀ y, F (c y) ≤ 2 ^ (2 * b - 1) * (D⁻¹ * I y + S ^ (2 * b)) := by
    intro y
    set μy : ℝ := τ.real (box y) with hμy
    have hμy_pos : 0 < μy := lt_of_lt_of_le hδpos (hlow y)
    have hle : ∀ α ∈ box y, F (c y) ≤ 2 ^ (2 * b - 1) * (F α + S ^ (2 * b)) := by
      intro α hα
      have h1 := hvar y α hα
      have h2 : F (c y) ≤ (‖genFun k A α‖ + S) ^ (2 * b) := by
        rw [hFdef]; exact pow_le_pow_left₀ (norm_nonneg _) h1 (2 * b)
      have h3 : (‖genFun k A α‖ + S) ^ (2 * b)
          ≤ 2 ^ (2 * b - 1) * (‖genFun k A α‖ ^ (2 * b) + S ^ (2 * b)) :=
        add_pow_le (norm_nonneg _) hS (2 * b)
      calc F (c y) ≤ (‖genFun k A α‖ + S) ^ (2 * b) := h2
        _ ≤ 2 ^ (2 * b - 1) * (‖genFun k A α‖ ^ (2 * b) + S ^ (2 * b)) := h3
        _ = 2 ^ (2 * b - 1) * (F α + S ^ (2 * b)) := by rw [hFdef]
    have hfint_on : IntegrableOn (fun α => 2 ^ (2 * b - 1) * (F α + S ^ (2 * b))) (box y) τ :=
      Integrable.integrableOn
        ((hFint.add (integrable_const (S ^ (2 * b)))).const_mul (2 ^ (2 * b - 1)))
    have hcl := setIntegral_ge_of_const_le_real (μ := τ) (s := box y)
      (f := fun α => 2 ^ (2 * b - 1) * (F α + S ^ (2 * b)))
      (hmeas y) (measure_ne_top τ (box y)) hle hfint_on
    have hInt_split : ∫ α in box y, 2 ^ (2 * b - 1) * (F α + S ^ (2 * b)) ∂τ
        = 2 ^ (2 * b - 1) * (I y + μy * S ^ (2 * b)) := by
      rw [integral_const_mul]
      congr 1
      rw [integral_add hFint.integrableOn (integrable_const _).integrableOn, hIdef]
      congr 1
      rw [setIntegral_const, smul_eq_mul]
    rw [hInt_split] at hcl
    have hDmu : (1 : ℝ) ≤ D⁻¹ * μy := by
      rw [inv_mul_eq_div]; exact (one_le_div hδpos).mpr (hlow y)
    have hkey : F (c y) * μy ≤ (2 ^ (2 * b - 1) * (D⁻¹ * I y + S ^ (2 * b))) * μy := by
      have hexp : (2 : ℝ) ^ (2 * b - 1) * (D⁻¹ * I y + S ^ (2 * b)) * μy
          = 2 ^ (2 * b - 1) * (D⁻¹ * I y * μy + μy * S ^ (2 * b)) := by ring
      rw [hexp]
      refine le_trans hcl ?_
      have hImul : I y ≤ D⁻¹ * I y * μy := by nlinarith [hI_nn y, hDmu]
      have h2pos : (0 : ℝ) ≤ 2 ^ (2 * b - 1) := by positivity
      nlinarith [hImul, h2pos, mul_nonneg (le_of_lt hμy_pos) (pow_nonneg hS (2 * b))]
    exact le_of_mul_le_mul_right hkey hμy_pos
  -- fold the box integrals into Jk
  have hfold : ∑ y : Fin Y, I y ≤ (Jk k b A : ℝ) := by
    have hunion : ∑ y : Fin Y, I y = ∫ α in ⋃ y, box y, F α ∂τ := by
      rw [hIdef]
      exact (integral_iUnion_fintype hmeas hdisj (fun y => hFint.integrableOn)).symm
    rw [hunion]
    calc ∫ α in ⋃ y, box y, F α ∂τ ≤ ∫ α, F α ∂τ :=
          setIntegral_le_integral hFint (Filter.Eventually.of_forall hFnn)
      _ = (Jk k b A : ℝ) := by rw [hFdef, hτ, hA]; exact integral_norm_pow_eq_Jk k b A
  calc ∑ y : Fin Y, F (c y)
      ≤ ∑ y : Fin Y, 2 ^ (2 * b - 1) * (D⁻¹ * I y + S ^ (2 * b)) :=
        Finset.sum_le_sum (fun y _ => hpery y)
    _ = 2 ^ (2 * b - 1) * (D⁻¹ * (∑ y : Fin Y, I y) + (Y : ℝ) * S ^ (2 * b)) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
    _ ≤ 2 ^ (2 * b - 1) * (D⁻¹ * (Jk k b A : ℝ) + (Y : ℝ) * S ^ (2 * b)) := by
        have h2nn : (0 : ℝ) ≤ 2 ^ (2 * b - 1) := by positivity
        have hDinv_nn : (0 : ℝ) ≤ D⁻¹ := by positivity
        apply mul_le_mul_of_nonneg_left _ h2nn
        have hmul : D⁻¹ * (∑ y : Fin Y, I y) ≤ D⁻¹ * (Jk k b A : ℝ) :=
          mul_le_mul_of_nonneg_left hfold hDinv_nn
        linarith

/-! ## The clipped coordinate box and its construction from centers -/

/-- `unitMeasure (Ioc a b) = b − a` for `0 ≤ a ≤ b ≤ 1`. -/
lemma unitMeasure_Ioc_toReal {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (unitMeasure (Set.Ioc a b)).toReal = b - a := by
  have hsub : Set.Ioc a b ⊆ Set.Ioc (0 : ℝ) 1 := Set.Ioc_subset_Ioc ha hb
  rw [unitMeasure, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left hsub, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith)]

/-- The clipped coordinate box around center `c`, half-widths `δ`, sitting in the torus. -/
noncomputable def vkBox (k : ℕ) (c δ : Deg k → ℝ) : Set (Deg k → ℝ) :=
  Set.univ.pi (fun j => Set.Ioc (max 0 (c j - δ j)) (min 1 (c j + δ j)))

lemma vkBox_measurable (k : ℕ) (c δ : Deg k → ℝ) : MeasurableSet (vkBox k c δ) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

/-- Each clipped coordinate interval has width `≥ δ j` (the inner half survives clipping). -/
lemma clip_width_ge {c δ : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ ≤ min 1 (c + δ) - max 0 (c - δ) := by
  rcases le_total (c + δ) 1 with h1 | h1 <;> rcases le_total 0 (c - δ) with h2 | h2 <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h1, h2] <;> linarith

/-- **The box measure lower bound.**  `∏_j δ_j ≤ torusMeasure(vkBox c δ)` when the center
lies in `[0,1]^k` and `0 ≤ δ_j ≤ 1`. -/
lemma vkBox_measureReal_ge (k : ℕ) (c δ : Deg k → ℝ)
    (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1) :
    (∏ j : Deg k, δ j) ≤ (torusMeasure k).real (vkBox k c δ) := by
  have hmeq : (torusMeasure k).real (vkBox k c δ)
      = ∏ j : Deg k, (min 1 (c j + δ j) - max 0 (c j - δ j)) := by
    rw [MeasureTheory.measureReal_def, vkBox, torusMeasure, Measure.pi_pi, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    have ha : (0 : ℝ) ≤ max 0 (c j - δ j) := le_max_left _ _
    have hb : min 1 (c j + δ j) ≤ 1 := min_le_left _ _
    have hab : max 0 (c j - δ j) ≤ min 1 (c j + δ j) :=
      max_le (le_min (by norm_num) (by linarith [(hc j).1, hδ0 j]))
        (le_min (by linarith [(hc j).2, hδ0 j]) (by linarith [hδ0 j]))
    exact unitMeasure_Ioc_toReal ha hab hb
  rw [hmeq]
  refine Finset.prod_le_prod (fun j _ => hδ0 j) (fun j _ => ?_)
  exact clip_width_ge (hc j).1 (hc j).2 (hδ0 j) (hδ1 j)

/-- **Box disjointness from `j₀`-separation.**  If the centers' `j₀`-coordinates are
`2δ_{j₀}`-separated, the clipped boxes are disjoint (already disjoint in the `j₀` slot,
before clipping). -/
lemma vkBox_disjoint {k : ℕ} {c c' δ : Deg k → ℝ} (j₀ : Deg k)
    (hsep : 2 * δ j₀ ≤ |c j₀ - c' j₀|) :
    Disjoint (vkBox k c δ) (vkBox k c' δ) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have hxj := (Set.mem_univ_pi.mp hx) j₀
  have hxj' := (Set.mem_univ_pi.mp hx') j₀
  rw [Set.mem_Ioc] at hxj hxj'
  have hlo : c j₀ - δ j₀ < x j₀ := lt_of_le_of_lt (le_max_right _ _) hxj.1
  have hhi : x j₀ ≤ c j₀ + δ j₀ := le_trans hxj.2 (min_le_right _ _)
  have hlo' : c' j₀ - δ j₀ < x j₀ := lt_of_le_of_lt (le_max_right _ _) hxj'.1
  have hhi' : x j₀ ≤ c' j₀ + δ j₀ := le_trans hxj'.2 (min_le_right _ _)
  rcases abs_cases (c j₀ - c' j₀) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hsep <;> linarith

/-- **R3-measure (from centers).**  Combining `vk_box_disjoint_avg` with the clipped-box
construction: centers in `[0,1]^k` whose `j₀`-coordinates are `2δ_{j₀}`-separated satisfy
the box-average bound with the `genFun_box_variation` Slack. -/
theorem vk_box_disjoint_avg_of_centers (k b P Y : ℕ) (c : Fin Y → Deg k → ℝ)
    (δ : Deg k → ℝ) (j₀ : Deg k)
    (hc : ∀ y j, 0 ≤ c y j ∧ c y j ≤ 1)
    (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hδpos : 0 < ∏ j : Deg k, δ j)
    (hsep : ∀ y y' : Fin Y, y ≠ y' → 2 * δ j₀ ≤ |c y j₀ - c y' j₀|) :
    ∑ y : Fin Y, ‖genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) (c y)‖ ^ (2 * b)
      ≤ 2 ^ (2 * b - 1) * ((∏ j : Deg k, δ j)⁻¹ * (Jk k b (Finset.Ioc (0 : ℤ) (P : ℤ)) : ℝ)
          + (Y : ℝ) * (2 * π * ((P : ℝ) * ∑ j : Deg k, δ j * (P : ℝ) ^ (j : ℕ))) ^ (2 * b)) := by
  set S : ℝ := 2 * π * ((P : ℝ) * ∑ j : Deg k, δ j * (P : ℝ) ^ (j : ℕ)) with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    refine mul_nonneg (by positivity) (mul_nonneg (by positivity) ?_)
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hδ0 j) (by positivity))
  refine vk_box_disjoint_avg k b P Y c δ S hSnn
    (fun y => vkBox k (c y) δ) (fun y => vkBox_measurable k (c y) δ) ?_ hδpos
    (fun y => vkBox_measureReal_ge k (c y) δ (hc y) hδ0 hδ1) ?_
  · intro y y' hyy'
    exact vkBox_disjoint j₀ (hsep y y' hyy')
  · intro y α hα
    have hin : ∀ j, |c y j - α j| ≤ δ j := by
      intro j
      have hαj := (Set.mem_univ_pi.mp hα) j
      rw [Set.mem_Ioc] at hαj
      have hlo : c y j - δ j < α j := lt_of_le_of_lt (le_max_right _ _) hαj.1
      have hhi : α j ≤ c y j + δ j := le_trans hαj.2 (min_le_right _ _)
      rw [abs_le]; constructor <;> linarith
    have hvar := genFun_box_variation k P (c y) α δ hin hδ0
    calc ‖genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) (c y)‖
        = ‖genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) α
            + (genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) (c y)
              - genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) α)‖ := by rw [add_sub_cancel]
      _ ≤ ‖genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) α‖
            + ‖genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) (c y)
              - genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) α‖ := norm_add_le _ _
      _ ≤ ‖genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) α‖ + S := by
          rw [hSdef]; linarith [hvar]

end Salt.Vk
