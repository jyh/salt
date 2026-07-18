/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Fourier

/-!
# The honest `γ = 2` fractional `S₂` bound (VMVT R2-3, the `S₂`-dominant closure)

This file discharges the analytic residual `(R1)+(R2)` flagged by `VMVT-FOURIER`
(`docs/blueprints/flags.md`): the factorization of the pair-collapse generating
function plus the self-improving Hölder step, in its **honest `γ = 2`, `θ = 2/(kr)`
shape**.  The end product is

  `Ncount(pairEqBox x e ab) ≤ x² · J_k(x, kr)^{1 − 2/(kr)}`   (`pairEq_Ncount_le_frac`)

for any off-diagonal pair with `e ab.1 ≠ e ab.2` (catch #74: the injectivity of the
designated coordinates is REQUIRED — without it `pairEqBox = solBox` and the count is
`J_k`, so the bound is false).  The house has re-verified that this `x²`-carrying,
`θ = 2/(kr)` form closes R4 in the `S₂`-dominant branch for `r ≥ (k+1)/2`; it does
**not** fit `PairEqFracBound` (whose `Cc` is `x`-free), so it stands as its own named
theorem that R4 consumes directly.

## The two rungs

* **Part A — the factorization (the stone).**  `setGen(pairEqBox) = G₂ · F^{kr−2}`
  where `F = genFun k (0,x]` and `G₂ = ∑_{n∈(0,x]} gcoord(n)²` is the "doubled"
  generating function (`‖G₂‖ ≤ x`).  Derived from a subtype-free combinatorial
  identity (`sum_prod_filter_eq`): pinning the two tied coordinates via a doubled
  indicator and collapsing with `Finset.sum_prod_piFinset` — no `Fin (kr)`-complement
  gymnastics.

* **Part B — the Hölder + moments (the node).**  `∫ |G₂|²|F|^{2kr−4}` bounded by
  `(∫|G₂|^{kr})^{2/kr}·(∫|F|^{2kr})^{1−2/kr}` via `ENNReal.lintegral_mul_norm_pow_le`
  (the `p+q=1` Hölder), the crude `∫|G₂|^{kr} ≤ x^{kr}` moment, and the landed keystone
  `∫|F|^{2kr} = J_k(x, kr)`.  The `ENNReal ↔ ℝ` transfer is the expected friction.
-/

namespace Salt.Vmvt

open Finset MeasureTheory
open scoped ComplexConjugate
open Salt.ExpSum

/-! ## Part A — the combinatorial factorization -/

/-- The per-coordinate character block `∏_j e(α_j · v^j)` — the summand of `genFun`,
and the atom into which each `setGen` signature-character factors. -/
noncomputable def gcoord (k : ℕ) (α : Deg k → ℝ) (v : ℤ) : ℂ :=
  ∏ j : Deg k, eR (α j * (v : ℝ) ^ (j : ℕ))

/-- `genFun` is the sum of the coordinate blocks. -/
theorem genFun_eq_sum_gcoord (k : ℕ) (A : Finset ℤ) (α : Deg k → ℝ) :
    genFun k A α = ∑ v ∈ A, gcoord k α v := rfl

/-- Each block has unit modulus (product of unit-modulus characters). -/
theorem norm_gcoord (k : ℕ) (α : Deg k → ℝ) (v : ℤ) : ‖gcoord k α v‖ = 1 := by
  rw [gcoord, norm_prod]; simp [norm_eR]

/-- The `setGen` signature character factors over coordinates:
`∏_j e(α_j · s_j(m)) = ∏_q gcoord(m q)`. -/
theorem setGen_summand_eq_prod (k b : ℕ) (m : Fin b → ℤ) (α : Deg k → ℝ) :
    (∏ j : Deg k, eR (α j * (sig k b m j : ℝ))) = ∏ q : Fin b, gcoord k α (m q) := by
  have hj : ∀ j : Deg k, eR (α j * (sig k b m j : ℝ))
      = ∏ q : Fin b, eR (α j * (m q : ℝ) ^ (j : ℕ)) := by
    intro j
    simp only [sig]
    push_cast
    rw [Finset.mul_sum, eR_sum]
  rw [Finset.prod_congr rfl (fun j _ => hj j), Finset.prod_comm]
  rfl

/-- **The subtype-free pair-collapse identity.**  For a coefficient function `g` and a
pair of distinct coordinates `s ≠ t`, summing `∏_q g(m q)` over the tuples in `A^b` with
`m s = m t` factors as `(∑_n g(n)²) · (∑_v g(v))^{b−2}`.  Proof: pin the tied value with
a doubled indicator, then collapse the free product with `Finset.sum_prod_piFinset`. -/
theorem sum_prod_filter_eq {R : Type*} [CommSemiring R] {b : ℕ} (A : Finset ℤ)
    (g : ℤ → R) {s t : Fin b} (hst : s ≠ t) :
    ∑ m ∈ (Fintype.piFinset fun _ : Fin b => A).filter (fun m => m s = m t),
        ∏ q, g (m q)
      = (∑ n ∈ A, g n ^ 2) * (∑ v ∈ A, g v) ^ (b - 2) := by
  classical
  set P : Finset (Fin b → ℤ) := Fintype.piFinset fun _ : Fin b => A with hP
  -- the doubly-pinned integrand
  set h : ℤ → Fin b → ℤ → R := fun n q v =>
      g v * (if q = s then (if v = n then 1 else 0) else 1)
          * (if q = t then (if v = n then 1 else 0) else 1) with hh
  -- per-coordinate collapsed sums
  have hval_s : ∀ n ∈ A, (∑ v ∈ A, h n s v) = g n := by
    intro n hn
    have hpt : ∀ v, h n s v = if v = n then g v else 0 := by
      intro v
      by_cases hv : v = n <;> simp [hh, hst, hv]
    rw [Finset.sum_congr rfl (fun v _ => hpt v), Finset.sum_ite_eq' A n g, if_pos hn]
  have hval_t : ∀ n ∈ A, (∑ v ∈ A, h n t v) = g n := by
    intro n hn
    have hpt : ∀ v, h n t v = if v = n then g v else 0 := by
      intro v
      by_cases hv : v = n <;> simp [hh, Ne.symm hst, hv]
    rw [Finset.sum_congr rfl (fun v _ => hpt v), Finset.sum_ite_eq' A n g, if_pos hn]
  have hval_o : ∀ n, ∀ q, q ≠ s → q ≠ t → (∑ v ∈ A, h n q v) = ∑ v ∈ A, g v := by
    intro n q hqs hqt
    simp only [hh, if_neg hqs, if_neg hqt, mul_one]
  -- per-`n` product collapse: ∏_q (∑_v h n q v) = g n ^ 2 * (∑ g)^(b-2)
  have perN : ∀ n ∈ A, (∑ m ∈ P, ∏ q, h n q (m q))
      = g n ^ 2 * (∑ v ∈ A, g v) ^ (b - 2) := by
    intro n hn
    rw [hP, Finset.sum_prod_piFinset]
    have hsub : ({s, t} : Finset (Fin b)) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.prod_sdiff hsub]
    have hpair : (∏ q ∈ ({s, t} : Finset (Fin b)), ∑ v ∈ A, h n q v) = g n ^ 2 := by
      rw [Finset.prod_pair hst, hval_s n hn, hval_t n hn, ← pow_two]
    have hcard : (Finset.univ \ ({s, t} : Finset (Fin b))).card = b - 2 := by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin,
        Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr hst),
        Finset.card_singleton]
    have hother : (∏ q ∈ Finset.univ \ ({s, t} : Finset (Fin b)), ∑ v ∈ A, h n q v)
        = (∑ v ∈ A, g v) ^ (b - 2) := by
      have hstep : (∏ q ∈ Finset.univ \ ({s, t} : Finset (Fin b)), ∑ v ∈ A, h n q v)
          = ∏ q ∈ Finset.univ \ ({s, t} : Finset (Fin b)), ∑ v ∈ A, g v := by
        refine Finset.prod_congr rfl (fun q hq => ?_)
        rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hq
        exact hval_o n q (fun hqs => hq.2 (Or.inl hqs)) (fun hqt => hq.2 (Or.inr hqt))
      rw [hstep, Finset.prod_const, hcard]
    rw [hpair, hother, mul_comm]
  -- the doubled-indicator key: (if m s = m t then ∏ g else 0) = ∑_n ∏_q h n q (m q)
  have hkey : ∀ m ∈ P, (if m s = m t then ∏ q, g (m q) else 0)
      = ∑ n ∈ A, ∏ q, h n q (m q) := by
    intro m hm
    have hmsA : m s ∈ A := Fintype.mem_piFinset.mp hm s
    have hexpand : ∀ n, (∏ q, h n q (m q))
        = (∏ q, g (m q)) * ((if m s = n then 1 else 0) * (if m t = n then 1 else 0)) := by
      intro n
      simp only [hh]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_ite_eq' Finset.univ s (fun q => if m q = n then (1 : R) else 0),
        Finset.prod_ite_eq' Finset.univ t (fun q => if m q = n then (1 : R) else 0),
        if_pos (Finset.mem_univ s), if_pos (Finset.mem_univ t), mul_assoc]
    rw [Finset.sum_congr rfl (fun n _ => hexpand n), ← Finset.mul_sum]
    have hinner : (∑ n ∈ A, (if m s = n then (1 : R) else 0) * (if m t = n then 1 else 0))
        = if m s = m t then 1 else 0 := by
      have : ∀ n, (if m s = n then (1 : R) else 0) * (if m t = n then 1 else 0)
          = if m s = n then (if m t = n then 1 else 0) else 0 := by
        intro n; rw [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_congr rfl (fun n _ => this n),
        Finset.sum_ite_eq A (m s) (fun n => if m t = n then (1 : R) else 0), if_pos hmsA]
      by_cases hmt : m s = m t
      · rw [if_pos hmt, if_pos hmt.symm]
      · rw [if_neg hmt, if_neg (fun h => hmt h.symm)]
    rw [hinner, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_filter, Finset.sum_congr rfl hkey, Finset.sum_comm,
    Finset.sum_congr rfl perN, ← Finset.sum_mul]

/-- The "doubled" generating function `G₂(α) = ∑_{n∈(0,x]} gcoord(n)²` — the tied-pair
factor of the pair-collapse generating function. -/
noncomputable def G2 (k x : ℕ) (α : Deg k → ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (0 : ℤ) (x : ℤ), gcoord k α n ^ 2

/-- The integer interval `(0, x]` has exactly `x` elements. -/
theorem card_Ioc_zero (x : ℕ) : (Finset.Ioc (0 : ℤ) (x : ℤ)).card = x := by
  rw [Int.card_Ioc, sub_zero, Int.toNat_natCast]

/-- **The crude `G₂`-bound.**  `‖G₂(α)‖ ≤ x`: a sum of `x` unit-modulus squares. -/
theorem norm_G2_le (k x : ℕ) (α : Deg k → ℝ) : ‖G2 k x α‖ ≤ (x : ℝ) := by
  rw [G2]
  calc ‖∑ n ∈ Finset.Ioc (0 : ℤ) (x : ℤ), gcoord k α n ^ 2‖
      ≤ ∑ n ∈ Finset.Ioc (0 : ℤ) (x : ℤ), ‖gcoord k α n ^ 2‖ := norm_sum_le _ _
    _ = ∑ _n ∈ Finset.Ioc (0 : ℤ) (x : ℤ), (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [norm_pow, norm_gcoord, one_pow]
    _ = ((Finset.Ioc (0 : ℤ) (x : ℤ)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (x : ℝ) := by rw [card_Ioc_zero]

/-- **The factorization (the stone).**  For a pair with distinct designated coordinates
(`e ab.1 ≠ e ab.2`), the pair-collapse generating function factors:
`setGen(pairEqBox) = G₂ · F^{kr−2}` with `F = genFun k (0,x]`. -/
theorem setGen_pairEqBox_factor {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * r))
    (ab : Fin k × Fin k) (he : e ab.1 ≠ e ab.2) (α : Deg k → ℝ) :
    setGen k (k * r) (pairEqBox x e ab) α
      = G2 k x α * (genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α) ^ (k * r - 2) := by
  rw [setGen,
    Finset.sum_congr rfl (fun m _ => setGen_summand_eq_prod k (k * r) m α),
    pairEqBox, solBox,
    sum_prod_filter_eq (Finset.Ioc (0 : ℤ) (x : ℤ)) (gcoord k α) he,
    G2, genFun_eq_sum_gcoord]

/-! ## Part B — continuity, integrability, and the Hölder step -/

@[fun_prop]
theorem continuous_gcoord (k : ℕ) (v : ℤ) :
    Continuous (fun α : Deg k → ℝ => gcoord k α v) := by unfold gcoord; fun_prop

theorem continuous_genFun (k : ℕ) (A : Finset ℤ) :
    Continuous (fun α : Deg k → ℝ => genFun k A α) := by unfold genFun; fun_prop

theorem continuous_G2 (k x : ℕ) :
    Continuous (fun α : Deg k → ℝ => G2 k x α) := by unfold G2; fun_prop

/-- Bounded continuous real functions are torus-integrable (probability measure). -/
theorem integrable_cont_bdd {k : ℕ} {φ : (Deg k → ℝ) → ℝ} (hφ : Continuous φ)
    {C : ℝ} (hbd : ∀ α, ‖φ α‖ ≤ C) : Integrable φ (torusMeasure k) :=
  ⟨hφ.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := C) (Filter.Eventually.of_forall hbd)⟩

theorem integrable_norm_G2_pow (k x n : ℕ) :
    Integrable (fun α => ‖G2 k x α‖ ^ n) (torusMeasure k) := by
  refine integrable_cont_bdd ((continuous_G2 k x).norm.pow n) (C := (x : ℝ) ^ n) (fun α => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_G2_le k x α) n

theorem integrable_norm_genFun_pow (k x n : ℕ) :
    Integrable (fun α => ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ n) (torusMeasure k) := by
  refine integrable_cont_bdd ((continuous_genFun k _).norm.pow n) (C := (x : ℝ) ^ n) (fun α => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ n
  calc ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ≤ ((Finset.Ioc (0 : ℤ) (x : ℤ)).card : ℝ) :=
        norm_genFun_le _ _ _
    _ = (x : ℝ) := by rw [card_Ioc_zero]

theorem integrable_G2_mul_genFun (k x b : ℕ) :
    Integrable (fun α => ‖G2 k x α‖ ^ 2
        * ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * (b - 2))) (torusMeasure k) := by
  refine integrable_cont_bdd
    (((continuous_G2 k x).norm.pow 2).mul ((continuous_genFun k _).norm.pow (2 * (b - 2))))
    (C := (x : ℝ) ^ 2 * (x : ℝ) ^ (2 * (b - 2))) (fun α => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_G2_le k x α) 2) ?_
    (by positivity) (by positivity)
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ (2 * (b - 2))
  calc ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ≤ ((Finset.Ioc (0 : ℤ) (x : ℤ)).card : ℝ) :=
        norm_genFun_le _ _ _
    _ = (x : ℝ) := by rw [card_Ioc_zero]

/-- **The Hölder step (the node).**
`∫ |G₂|²|F|^{2(kr−2)} ≤ (∫|G₂|^{kr})^{2/kr}·(∫|F|^{2kr})^{1−2/kr}`, the `p + q = 1` Hölder
(`ENNReal.lintegral_mul_norm_pow_le`) with `p = 2/kr`, `q = 1 − 2/kr`, via the `ℝ≥0∞ ↔ ℝ`
transfer. -/
theorem holder_step (k x b : ℕ) (hb : 2 ≤ b) :
    (∫ α, ‖G2 k x α‖ ^ 2
        * ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * (b - 2)) ∂(torusMeasure k))
      ≤ (∫ α, ‖G2 k x α‖ ^ b ∂(torusMeasure k)) ^ ((2 : ℝ) / b)
        * (∫ α, ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * b) ∂(torusMeasure k))
            ^ (1 - (2 : ℝ) / b) := by
  have hbpos : 0 < b := by omega
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbR
  have hp0 : (0 : ℝ) ≤ 2 / (b : ℝ) := by positivity
  have hq0 : (0 : ℝ) ≤ 1 - 2 / (b : ℝ) := by
    rw [sub_nonneg, div_le_one hbR]; exact_mod_cast hb
  have hpq : 2 / (b : ℝ) + (1 - 2 / (b : ℝ)) = 1 := by ring
  -- real rpow arithmetic on the pointwise exponents
  have hpowG : ∀ c : ℝ, 0 ≤ c → (c ^ b) ^ ((2 : ℝ) / b) = c ^ 2 := by
    intro c hc
    have he : (b : ℝ) * (2 / b) = 2 := by field_simp
    rw [← Real.rpow_natCast c b, ← Real.rpow_mul hc, he,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpowF : ∀ c : ℝ, 0 ≤ c → (c ^ (2 * b)) ^ (1 - (2 : ℝ) / b) = c ^ (2 * (b - 2)) := by
    intro c hc
    have he : ((2 * b : ℕ) : ℝ) * (1 - 2 / (b : ℝ)) = ((2 * (b - 2) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hb]
      field_simp
    rw [← Real.rpow_natCast c (2 * b), ← Real.rpow_mul hc, he, Real.rpow_natCast]
  -- measurability of the ENNReal functions
  set μ := torusMeasure k with hμ
  have hfEm : AEMeasurable (fun α => ENNReal.ofReal (‖G2 k x α‖ ^ b)) μ :=
    ((continuous_G2 k x).norm.pow b).measurable.ennreal_ofReal.aemeasurable
  have hgEm : AEMeasurable
      (fun α => ENNReal.ofReal (‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * b))) μ :=
    ((continuous_genFun k _).norm.pow (2 * b)).measurable.ennreal_ofReal.aemeasurable
  have H := ENNReal.lintegral_mul_norm_pow_le hfEm hgEm hp0 hq0 hpq
  -- pointwise identity for the LHS integrand
  have hptL : ∀ α, (ENNReal.ofReal (‖G2 k x α‖ ^ b)) ^ ((2 : ℝ) / b)
        * (ENNReal.ofReal (‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * b)))
            ^ (1 - (2 : ℝ) / b)
      = ENNReal.ofReal (‖G2 k x α‖ ^ 2
          * ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * (b - 2))) := by
    intro α
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0,
      ← ENNReal.ofReal_mul (by positivity),
      hpowG _ (norm_nonneg _), hpowF _ (norm_nonneg _)]
  -- nonnegativity and the three lintegral transfers
  have hnnG : (0 : (Deg k → ℝ) → ℝ) ≤ᵐ[μ] fun α => ‖G2 k x α‖ ^ b :=
    Filter.Eventually.of_forall (fun α => pow_nonneg (norm_nonneg _) b)
  have hnnF : (0 : (Deg k → ℝ) → ℝ) ≤ᵐ[μ]
      fun α => ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * b) :=
    Filter.Eventually.of_forall (fun α => pow_nonneg (norm_nonneg _) (2 * b))
  have hnnGF : (0 : (Deg k → ℝ) → ℝ) ≤ᵐ[μ] fun α => ‖G2 k x α‖ ^ 2
      * ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * (b - 2)) :=
    Filter.Eventually.of_forall (fun α =>
      mul_nonneg (pow_nonneg (norm_nonneg _) 2) (pow_nonneg (norm_nonneg _) (2 * (b - 2))))
  have hIG0 : (0 : ℝ) ≤ ∫ α, ‖G2 k x α‖ ^ b ∂μ :=
    integral_nonneg (fun α => pow_nonneg (norm_nonneg _) b)
  have hIF0 : (0 : ℝ) ≤ ∫ α, ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * b) ∂μ :=
    integral_nonneg (fun α => pow_nonneg (norm_nonneg _) (2 * b))
  have hIntG : ∫⁻ α, ENNReal.ofReal (‖G2 k x α‖ ^ b) ∂μ
      = ENNReal.ofReal (∫ α, ‖G2 k x α‖ ^ b ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_norm_G2_pow k x b) hnnG).symm
  have hIntF : ∫⁻ α, ENNReal.ofReal (‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * b)) ∂μ
      = ENNReal.ofReal (∫ α, ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * b) ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_norm_genFun_pow k x (2 * b)) hnnF).symm
  have hIntGF : ∫⁻ α, ENNReal.ofReal (‖G2 k x α‖ ^ 2
        * ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * (b - 2))) ∂μ
      = ENNReal.ofReal (∫ α, ‖G2 k x α‖ ^ 2
          * ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * (b - 2)) ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_G2_mul_genFun k x b) hnnGF).symm
  -- rewrite H into `ofReal ≤ ofReal` and strip
  simp_rw [hptL] at H
  rw [hIntGF, hIntG, hIntF,
    ENNReal.ofReal_rpow_of_nonneg hIG0 hp0,
    ENNReal.ofReal_rpow_of_nonneg hIF0 hq0,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hIG0 _)] at H
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.rpow_nonneg hIG0 _) (Real.rpow_nonneg hIF0 _))).mp H

/-! ## Part C — the assembled `γ = 2` bound (the R4 plug-in) -/

/-- **The honest `γ = 2` fractional `S₂` bound.**  For an off-diagonal pair with distinct
designated coordinates,
`Ncount(pairEqBox) ≤ x² · J_k(x, kr)^{1 − 2/(kr)}`.
This is the `θ = 2/(kr)`, `Cc = 1`, `x²`-carrying shape re-verified by the house to close R4
in the `S₂`-dominant branch (`r ≥ (k+1)/2`).  It does **not** fit `PairEqFracBound` (`Cc`
`x`-free); R4 consumes this directly. -/
theorem pairEq_Ncount_le_frac {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * r))
    (ab : Fin k × Fin k) (he : e ab.1 ≠ e ab.2) (hb : 2 ≤ k * r) :
    (Ncount k (k * r) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ)
      ≤ (x : ℝ) ^ 2 * (JkI k (k * r) x : ℝ) ^ (1 - 2 / (k * r : ℝ)) := by
  have hbpos : 0 < k * r := by omega
  have hbR : (0 : ℝ) < ((k * r : ℕ) : ℝ) := by exact_mod_cast hbpos
  have hbne : ((k * r : ℕ) : ℝ) ≠ 0 := ne_of_gt hbR
  -- Ncount = ∫ ‖setGen‖² = ∫ ‖G₂‖²‖F‖^{2(kr-2)}
  have hNc : (Ncount k (k * r) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ)
      = ∫ α, ‖G2 k x α‖ ^ 2
          * ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * (k * r - 2)) ∂(torusMeasure k) := by
    rw [pairEqBox_Ncount_eq_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun α => ?_))
    change ‖setGen k (k * r) (pairEqBox x e ab) α‖ ^ 2
        = ‖G2 k x α‖ ^ 2 * ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * (k * r - 2))
    rw [setGen_pairEqBox_factor x e ab he α, norm_mul, norm_pow, mul_pow, ← pow_mul,
      mul_comm (k * r - 2) 2]
  rw [hNc]
  refine (holder_step k x (k * r) hb).trans ?_
  -- the crude G-moment and the keystone F-moment
  have hGmom : (∫ α, ‖G2 k x α‖ ^ (k * r) ∂(torusMeasure k)) ≤ (x : ℝ) ^ (k * r) := by
    calc ∫ α, ‖G2 k x α‖ ^ (k * r) ∂(torusMeasure k)
        ≤ ∫ _α, (x : ℝ) ^ (k * r) ∂(torusMeasure k) :=
          integral_mono (integrable_norm_G2_pow k x (k * r)) (integrable_const _)
            (fun α => pow_le_pow_left₀ (norm_nonneg _) (norm_G2_le k x α) (k * r))
      _ = (x : ℝ) ^ (k * r) := by simp
  have hFmom : (∫ α, ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * (k * r)) ∂(torusMeasure k))
      = (JkI k (k * r) x : ℝ) := integral_norm_pow_eq_Jk k (k * r) (Finset.Ioc (0 : ℤ) (x : ℤ))
  have hp0 : (0 : ℝ) ≤ 2 / ((k * r : ℕ) : ℝ) := by positivity
  have hIG0 : (0 : ℝ) ≤ ∫ α, ‖G2 k x α‖ ^ (k * r) ∂(torusMeasure k) :=
    integral_nonneg (fun α => pow_nonneg (norm_nonneg _) (k * r))
  have hx2 : ((x : ℝ) ^ (k * r)) ^ (2 / ((k * r : ℕ) : ℝ)) = (x : ℝ) ^ 2 := by
    have he2 : ((k * r : ℕ) : ℝ) * (2 / ((k * r : ℕ) : ℝ)) = 2 := by field_simp
    rw [← Real.rpow_natCast (x : ℝ) (k * r), ← Real.rpow_mul (by positivity), he2,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc (∫ α, ‖G2 k x α‖ ^ (k * r) ∂(torusMeasure k)) ^ (2 / ((k * r : ℕ) : ℝ))
          * (∫ α, ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * (k * r)) ∂(torusMeasure k))
            ^ (1 - 2 / ((k * r : ℕ) : ℝ))
      ≤ ((x : ℝ) ^ (k * r)) ^ (2 / ((k * r : ℕ) : ℝ))
          * (JkI k (k * r) x : ℝ) ^ (1 - 2 / ((k * r : ℕ) : ℝ)) := by
        rw [hFmom]
        exact mul_le_mul (Real.rpow_le_rpow hIG0 hGmom hp0) (le_refl _)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) (k * r)) _)
    _ = (x : ℝ) ^ 2 * (JkI k (k * r) x : ℝ) ^ (1 - 2 / (k * r : ℝ)) := by
        rw [hx2, Nat.cast_mul]

end Salt.Vmvt
