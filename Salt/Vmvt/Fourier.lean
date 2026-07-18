/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Holder
import Salt.ExpSum.Basic

/-!
# The minimal torus module — the α-domain counting identity and the Hölder step (VMVT R2-3)

This file supplies the single **analytic** ingredient that the combinatorial `rcount`
frame provably cannot: it moves between the `h`-domain (signatures) and the `α`-domain
(exponential sums) via genuine torus integration.  This is exactly the Parseval step
that `Shifted.lean` was deliberately built to avoid (see `Holder.lean`'s header and the
`flags.md` VMVT tail: "the whole `Vmvt` frame must be extended with torus integration +
Parseval").

## The generating function and the counting identity (the keystone)

For `A : Finset ℤ` and a torus point `α : Deg k → ℝ`, the generating function is
`F(α) = ∑_{n ∈ A} ∏_j e(α_j · n^j)` (`genFun`), with `e(x) = eR x = exp(2πi x)` reused
from `Salt.ExpSum`.  Expanding `|F|^{2b} = F^b · conj(F)^b` into a double sum over
`2b`-tuples and integrating over the torus `[0,1]^k` collapses each coordinate by the
**1-D orthogonality** `∫₀¹ e(t·h) dt = [h = 0]`, giving the mean value:

  `∫_{[0,1]^k} |F(α)|^{2b} dα = J_k(A, b)`   (`integral_norm_pow_eq_Jk`).

More generally, for any finite set `D` of `b`-tuples,
`∫ ‖F_D(α)‖² dα = N(D, D, 0) = Ncount k b 0 D D`  (`integral_setGen_normSq`), where
`F_D(α) = ∑_{m ∈ D} ∏_j e(α_j · s_j(m))` sums the signature characters.  This is the
general **α-domain ⇆ h-domain bridge**; the two named consumers are its diagonal
(`A^b`, giving `J_k`) and the pair-collapse box (`pairEqBox`, feeding the Hölder step).

## Representation

The torus is `[0,1]^k` realised as `Measure.pi (fun _ : Deg k => unitMeasure)` with
`unitMeasure = volume.restrict (0,1]` a probability measure.  The k-fold product of the
1-D orthogonalities is `MeasureTheory.integral_fintype_prod_eq_prod` (Fubini for a finite
product of single-coordinate factors); the finite sum ⇆ integral swap is
`integral_finsetSum` (**not** the deprecated `integral_finset_sum`).
-/

namespace Salt.Vmvt

open Finset MeasureTheory
open scoped ComplexConjugate
open Salt.ExpSum

/-! ## Part A — the torus measure and the additive character -/

/-- The unit-interval probability measure on `ℝ`: Lebesgue restricted to `(0, 1]`. -/
noncomputable def unitMeasure : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)

instance : IsProbabilityMeasure unitMeasure := by
  constructor
  rw [unitMeasure, Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num

/-- The `k`-fold torus (product) measure on `[0,1]^k`, indexed by degrees `Deg k`. -/
noncomputable def torusMeasure (k : ℕ) : Measure (Deg k → ℝ) :=
  Measure.pi (fun _ : Deg k => unitMeasure)

instance (k : ℕ) : IsProbabilityMeasure (torusMeasure k) := by
  rw [torusMeasure]; infer_instance

/-- `eR` is continuous (registered for `fun_prop`/`continuity`). -/
@[continuity, fun_prop]
theorem continuous_eR : Continuous eR := by
  unfold Salt.ExpSum.eR; fun_prop

/-- `e(0) = 1`. -/
theorem eR_zero : eR (0 : ℝ) = 1 := by
  unfold Salt.ExpSum.eR; simp

/-- The character turns finite sums into products: `e(∑ f) = ∏ e(f)`. -/
theorem eR_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    eR (∑ i ∈ s, f i) = ∏ i ∈ s, eR (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [eR_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, eR_add, ih]

/-! ## Part B — the 1-D orthogonality -/

/-- **The 1-D orthogonality of the character.**  `∫₀¹ e(t·h) dt = [h = 0]` for `h : ℤ`:
the exponential integrates to `(e(h) − 1)/(2πih) = 0` when `h ≠ 0` (as `e(h) = 1` for
integer `h`), and to `1` when `h = 0`.  This is the atom the k-fold torus integral
factors into. -/
theorem integral_eR_unit (h : ℤ) :
    ∫ t, eR (t * (h : ℝ)) ∂unitMeasure = if h = 0 then 1 else 0 := by
  have hbridge : ∫ t, eR (t * (h : ℝ)) ∂unitMeasure
      = ∫ t in (0 : ℝ)..1, eR (t * (h : ℝ)) := by
    rw [unitMeasure]; exact (intervalIntegral.integral_of_le (by norm_num)).symm
  rw [hbridge]
  by_cases hh : h = 0
  · subst hh
    simp only [Int.cast_zero, mul_zero, eR_zero, if_true]
    simp
  · rw [if_neg hh]
    set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) with hc
    have hcne : c ≠ 0 := by
      rw [hc]
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      have hhc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
      simp only [mul_ne_zero_iff]
      exact ⟨⟨⟨by norm_num, hpi⟩, hI⟩, hhc⟩
    have hrw : (fun t : ℝ => eR (t * (h : ℝ)))
        = fun t : ℝ => Complex.exp (c * (t : ℂ)) := by
      funext t; rw [Salt.ExpSum.eR, hc]; push_cast; ring_nf
    rw [hrw, integral_exp_mul_complex hcne]
    have hexp : Complex.exp (c * (1 : ℝ)) = 1 := by
      rw [hc]
      have : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (h : ℂ) * ((1 : ℝ) : ℂ)
          = (h : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
      rw [this]; exact_mod_cast Complex.exp_int_mul_two_pi_mul_I h
    rw [hexp]
    simp

/-! ## Part C — the per-signature-difference term and its torus integral -/

/-- The single term `g_Δ(α) = ∏_j e(α_j · Δ_j)` attached to a signature difference `Δ`.
Its torus integral is the k-fold product of 1-D orthogonalities. -/
noncomputable def gterm (k : ℕ) (Δ : Deg k → ℤ) (α : Deg k → ℝ) : ℂ :=
  ∏ j : Deg k, eR (α j * (Δ j : ℝ))

/-- `‖g_Δ(α)‖ = 1` pointwise (product of unit-modulus characters). -/
theorem norm_gterm (k : ℕ) (Δ : Deg k → ℤ) (α : Deg k → ℝ) :
    ‖gterm k Δ α‖ = 1 := by
  rw [gterm, norm_prod]
  simp [norm_eR]

/-- `g_Δ` is continuous. -/
@[continuity, fun_prop]
theorem continuous_gterm (k : ℕ) (Δ : Deg k → ℤ) : Continuous (gterm k Δ) := by
  unfold gterm; fun_prop

/-- `g_Δ` is torus-integrable (bounded by `1` on a probability measure). -/
theorem integrable_gterm (k : ℕ) (Δ : Deg k → ℤ) :
    Integrable (gterm k Δ) (torusMeasure k) :=
  ⟨(continuous_gterm k Δ).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := 1)
      (Filter.Eventually.of_forall (fun α => le_of_eq (norm_gterm k Δ α)))⟩

/-- **The k-fold orthogonality.**  `∫_{[0,1]^k} g_Δ(α) dα = ∏_j [Δ_j = 0]`, by Fubini
over the product measure and the 1-D orthogonality on each coordinate. -/
theorem integral_gterm (k : ℕ) (Δ : Deg k → ℤ) :
    ∫ α, gterm k Δ α ∂(torusMeasure k)
      = ∏ j : Deg k, (if Δ j = 0 then (1 : ℂ) else 0) := by
  simp only [gterm, torusMeasure]
  rw [MeasureTheory.integral_fintype_prod_eq_prod
        (fun (j : Deg k) (a : ℝ) => eR (a * (Δ j : ℝ)))]
  exact Finset.prod_congr rfl (fun j _ => integral_eR_unit (Δ j))

/-- A product of `[· = 0]` indicators is the indicator of the conjunction. -/
theorem prod_ite_eq_forall (k : ℕ) (Δ : Deg k → ℤ) :
    ∏ j : Deg k, (if Δ j = 0 then (1 : ℂ) else 0) = if (∀ j, Δ j = 0) then 1 else 0 := by
  by_cases h : ∀ j, Δ j = 0
  · rw [if_pos h]; exact Finset.prod_eq_one (fun j _ => if_pos (h j))
  · rw [if_neg h]; obtain ⟨j, hj⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

/-! ## Part D — the set generating function and the counting identity -/

/-- The **set generating function** `F_D(α) = ∑_{m ∈ D} ∏_j e(α_j · s_j(m))` attaching a
signature character to each tuple `m ∈ D`. -/
noncomputable def setGen (k b : ℕ) (D : Finset (Fin b → ℤ)) (α : Deg k → ℝ) : ℂ :=
  ∑ m ∈ D, ∏ j : Deg k, eR (α j * (sig k b m j : ℝ))

/-- The **generating function** `F(α) = ∑_{n ∈ A} ∏_j e(α_j · n^j)` over an integer set. -/
noncomputable def genFun (k : ℕ) (A : Finset ℤ) (α : Deg k → ℝ) : ℂ :=
  ∑ n ∈ A, ∏ j : Deg k, eR (α j * (n : ℝ) ^ (j : ℕ))

/-- Expanding the product `F_D · conj F_E` into a double sum of signature-difference
terms. -/
theorem setGen_mul_conj_eq_sum (k b : ℕ) (D E : Finset (Fin b → ℤ)) (α : Deg k → ℝ) :
    setGen k b D α * conj (setGen k b E α)
      = ∑ p ∈ D ×ˢ E, gterm k (fun j => sig k b p.1 j - sig k b p.2 j) α := by
  have hpair : ∀ (m n : Fin b → ℤ),
      (∏ j : Deg k, eR (α j * (sig k b m j : ℝ)))
          * conj (∏ j : Deg k, eR (α j * (sig k b n j : ℝ)))
        = gterm k (fun j => sig k b m j - sig k b n j) α := by
    intro m n
    rw [map_prod, ← Finset.prod_mul_distrib, gterm]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [conj_eR, ← eR_add]
    congr 1
    push_cast; ring
  rw [setGen, setGen, map_sum, Finset.sum_mul_sum, Finset.sum_product]
  exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => hpair m n))

/-- **The counting identity (bilinear form).**  `∫ F_D(α)·conj F_E(α) dα = N(D, E, 0)`:
the torus integral of the signature-character correlation counts the pairs with equal
power sums.  This is the α-domain ⇆ h-domain bridge in full. -/
theorem integral_setGen_mul_conj (k b : ℕ) (D E : Finset (Fin b → ℤ)) :
    ∫ α, setGen k b D α * conj (setGen k b E α) ∂(torusMeasure k)
      = (Ncount k b 0 D E : ℂ) := by
  have hiff : ∀ p : (Fin b → ℤ) × (Fin b → ℤ),
      (∀ j, sig k b p.1 j - sig k b p.2 j = 0) ↔ PowerSumEq k b p.1 p.2 := by
    intro p
    rw [powerSumEq_iff_sig, funext_iff]
    exact forall_congr' (fun j => sub_eq_zero)
  have hpse : ∀ m n : Fin b → ℤ,
      PowerSumEq k b m n ↔ PowerSumShiftEq k b (0 : ℕ → ℤ) m n := by
    intro m n
    constructor
    · intro h j hj; rw [h j hj]; simp
    · intro h j hj; have := h j hj; simpa using this
  calc ∫ α, setGen k b D α * conj (setGen k b E α) ∂(torusMeasure k)
      = ∫ α, ∑ p ∈ D ×ˢ E, gterm k (fun j => sig k b p.1 j - sig k b p.2 j) α
          ∂(torusMeasure k) :=
        integral_congr_ae (Filter.Eventually.of_forall
          (fun α => setGen_mul_conj_eq_sum k b D E α))
    _ = ∑ p ∈ D ×ˢ E, ∫ α, gterm k (fun j => sig k b p.1 j - sig k b p.2 j) α
          ∂(torusMeasure k) :=
        integral_finsetSum (D ×ˢ E) (fun p _ => integrable_gterm k _)
    _ = ∑ p ∈ D ×ˢ E, (if PowerSumEq k b p.1 p.2 then (1 : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [integral_gterm, prod_ite_eq_forall]
        exact if_congr (hiff p) rfl rfl
    _ = (((D ×ˢ E).filter (fun p => PowerSumEq k b p.1 p.2)).card : ℂ) := by
        rw [Finset.sum_boole]
    _ = (Ncount k b 0 D E : ℂ) := by
        norm_cast
        unfold Ncount solSetN
        exact congrArg Finset.card (Finset.filter_congr (fun p _ => hpse p.1 p.2))

/-- **The counting identity (diagonal norm form).**  `∫ ‖F_D(α)‖² dα = N(D) = Ncount D`. -/
theorem integral_setGen_normSq (k b : ℕ) (D : Finset (Fin b → ℤ)) :
    ∫ α, ‖setGen k b D α‖ ^ 2 ∂(torusMeasure k) = (Ncount k b 0 D D : ℝ) := by
  have hptc : ∀ α, setGen k b D α * conj (setGen k b D α)
      = ((‖setGen k b D α‖ ^ 2 : ℝ) : ℂ) := by
    intro α; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 : ∫ α, setGen k b D α * conj (setGen k b D α) ∂(torusMeasure k)
      = ∫ α, ((‖setGen k b D α‖ ^ 2 : ℝ) : ℂ) ∂(torusMeasure k) :=
    integral_congr_ae (Filter.Eventually.of_forall hptc)
  have h2 : ∫ α, ((‖setGen k b D α‖ ^ 2 : ℝ) : ℂ) ∂(torusMeasure k)
      = ((∫ α, ‖setGen k b D α‖ ^ 2 ∂(torusMeasure k) : ℝ) : ℂ) :=
    integral_complex_ofReal
  have h3 := integral_setGen_mul_conj k b D D
  rw [h1, h2] at h3
  exact_mod_cast h3

/-! ## Part E — the two named consumers -/

/-- `F(α)^b` is the set generating function over the box `A^b`. -/
theorem genFun_pow_eq_setGen (k b : ℕ) (A : Finset ℤ) (α : Deg k → ℝ) :
    (genFun k A α) ^ b = setGen k b (Fintype.piFinset fun _ : Fin b => A) α := by
  rw [genFun, Finset.sum_pow', setGen]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp only [sig]
  push_cast
  rw [Finset.mul_sum, eR_sum]

/-- **The keystone counting identity.**  `∫_{[0,1]^k} |F(α)|^{2b} dα = J_k(A, b)`. -/
theorem integral_norm_pow_eq_Jk (k b : ℕ) (A : Finset ℤ) :
    ∫ α, ‖genFun k A α‖ ^ (2 * b) ∂(torusMeasure k) = (Jk k b A : ℝ) := by
  have hpt : ∀ α, ‖genFun k A α‖ ^ (2 * b)
      = ‖setGen k b (Fintype.piFinset fun _ : Fin b => A) α‖ ^ 2 := by
    intro α
    rw [← genFun_pow_eq_setGen, norm_pow, ← pow_mul, mul_comm b 2]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_setGen_normSq]
  exact_mod_cast Ncount_zero_eq_Jk k b A

/-- **The pairEq integral identity.**  The pair-collapse count is the second moment of the
pair-collapse box's generating function: `Ncount(D_{a=b}) = ∫ ‖F_{D_{a=b}}(α)‖² dα`.  This
is the α-domain object on which Vaughan's self-improving Hölder step acts. -/
theorem pairEqBox_Ncount_eq_integral {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * r))
    (ab : Fin k × Fin k) :
    (Ncount k (k * r) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ)
      = ∫ α, ‖setGen k (k * r) (pairEqBox x e ab) α‖ ^ 2 ∂(torusMeasure k) :=
  (integral_setGen_normSq k (k * r) (pairEqBox x e ab)).symm

/-! ## Part F — pointwise generating-function bounds (Hölder scaffolding)

The α-domain Hölder step (Vaughan Thm 24.5, `S₂ ≥ S₁` sub-case) acts on the pairEq integral
above via the factorization `F_{D_{a=b}} = G · F^{kr-2}` with `G(α) = ∑_v ∏_j e(2α_j v^j)`
the doubled generating function.  The pointwise bound `‖G‖ ≤ |A|` is the crude `G`-moment
input; the finish (factorization + integral Hölder) is flagged — see `docs/blueprints/flags.md`
(node `VMVT-FOURIER`) and the file-final note. -/

/-- `‖F_D(α)‖ ≤ |D|`: the set generating function is a sum of `|D|` unit-modulus terms. -/
theorem norm_setGen_le (k b : ℕ) (D : Finset (Fin b → ℤ)) (α : Deg k → ℝ) :
    ‖setGen k b D α‖ ≤ (D.card : ℝ) := by
  calc ‖setGen k b D α‖
      = ‖∑ m ∈ D, ∏ j : Deg k, eR (α j * (sig k b m j : ℝ))‖ := by rw [setGen]
    _ ≤ ∑ m ∈ D, ‖∏ j : Deg k, eR (α j * (sig k b m j : ℝ))‖ := norm_sum_le _ _
    _ = ∑ _m ∈ D, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun m _ => ?_); rw [norm_prod]; simp [norm_eR]
    _ = (D.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- `‖F(α)‖ ≤ |A|`: the generating function is a sum of `|A|` unit-modulus terms. -/
theorem norm_genFun_le (k : ℕ) (A : Finset ℤ) (α : Deg k → ℝ) :
    ‖genFun k A α‖ ≤ (A.card : ℝ) := by
  calc ‖genFun k A α‖
      = ‖∑ n ∈ A, ∏ j : Deg k, eR (α j * (n : ℝ) ^ (j : ℕ))‖ := by rw [genFun]
    _ ≤ ∑ n ∈ A, ‖∏ j : Deg k, eR (α j * (n : ℝ) ^ (j : ℕ))‖ := norm_sum_le _ _
    _ = ∑ _n ∈ A, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun n _ => ?_); rw [norm_prod]; simp [norm_eR]
    _ = (A.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end Salt.Vmvt
