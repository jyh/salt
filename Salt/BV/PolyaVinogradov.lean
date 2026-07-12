/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.GaussSum
import Salt.LS.Dist

/-!
# V2.PV — the Pólya–Vinogradov inequality

Design: `docs/blueprints/bv.md`, node `V2.PV`. For a *primitive* Dirichlet
character `χ` mod `f` (with `f ≥ 2`, hence `χ ≠ 1`), the partial character sums
`∑_{m < t} χ(m)` are bounded, **uniformly in `t`**, by `√f · (1 + log f)`.

Route (classical, adapted to the landed Gauss-sum toolkit `Salt/LS/GaussSum.lean`):

1. **Gauss-sum inversion** (`dirichlet_inversion'`): expand each `χ(m)` as
   `τ⁻¹ · ∑_a χ⁻¹(a) · ψ(m·a)` with `ψ = ZMod.stdAddChar`, `τ = gaussSum χ⁻¹ ψ`,
   and swap the `m`/`a` sums:
   `∑_{m<t} χ(m) = τ⁻¹ · ∑_a χ⁻¹(a) · ∑_{m<t} ψ(m·a)`.
2. **Geometric sums** (`geom_e_bound`): `∑_{m<t} ψ(m·a) = ∑_{m<t} (ψ a)^m` is a
   geometric series in `ψ a = e(a.val/f)`, bounded by `1/(2·dist₁(a.val/f, 0))`
   via the chord estimate `‖e θ − 1‖ ≥ 4·dist₁(θ, 0)` (`chord`, from
   `‖exp(ix)−1‖ = 2|sin(x/2)|` and Jordan's inequality `2/π·|x| ≤ |sin x|`).
   The `a = 0` term drops (`χ⁻¹(0) = 0` since `0` is a non-unit).
3. **Harmonic sum** (`dist_lb` + `term_le` + `sum_H_le`): `dist₁(k/f,0) ≥
   k(f−k)/f²`, so the `a`-sum is `≤ f·H_{f−1} ≤ f·(1 + log f)` via
   `harmonic_le_one_add_log`.
4. **Assemble** using `‖τ⁻¹‖ = 1/√f` (`gaussSum_normSq` at `χ⁻¹`).

This is (to our knowledge) the first machine-checked Pólya–Vinogradov in any
library.
-/

namespace Salt.BV

open scoped BigOperators
open Salt.LS

/-! ### The chord estimate `‖e θ − 1‖ ≥ 4·dist₁(θ, 0)` -/

/-- **Chord bound.** `‖e θ − 1‖ = 2|sin(πθ)| ≥ 4·dist₁(θ, 0)`, uniformly in `θ`
(Jordan's inequality after reducing `θ` mod `1`). -/
private lemma chord (θ : ℝ) : 4 * dist₁ θ 0 ≤ ‖e θ - 1‖ := by
  have hdd : dist₁ θ 0 = |θ - (round θ : ℝ)| := by
    unfold dist₁; simp only [sub_zero]
  have hnorm : ‖e θ - 1‖ = 2 * |Real.sin (Real.pi * θ)| := by
    have he : e θ = Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) := by
      unfold e; congr 1; push_cast; ring
    rw [he, Complex.norm_exp_I_mul_ofReal_sub_one,
        show (2 * Real.pi * θ) / 2 = Real.pi * θ from by ring,
        Real.norm_eq_abs, abs_mul, abs_two]
  have hsin_eq :
      |Real.sin (Real.pi * (θ - (round θ : ℝ)))| = |Real.sin (Real.pi * θ)| := by
    rw [show Real.pi * (θ - (round θ : ℝ)) = Real.pi * θ - (round θ : ℝ) * Real.pi from by ring,
        Real.sin_sub_int_mul_pi, abs_mul, abs_zpow]
    simp
  have hsin : 2 * dist₁ θ 0 ≤ |Real.sin (Real.pi * θ)| := by
    rw [hdd, ← hsin_eq]
    have hle : |Real.pi * (θ - (round θ : ℝ))| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      have hh : |θ - (round θ : ℝ)| ≤ 1 / 2 := by rw [← hdd]; exact dist₁_le_half θ 0
      nlinarith [Real.pi_pos, hh]
    have hj := Real.mul_abs_le_abs_sin hle
    have hcompute :
        2 / Real.pi * |Real.pi * (θ - (round θ : ℝ))| = 2 * |θ - (round θ : ℝ)| := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp
    rw [hcompute] at hj
    exact hj
  rw [hnorm]; linarith [hsin]

/-! ### The geometric-sum bound -/

/-- **Geometric bound.** For `dist₁ θ 0 > 0` (so `e θ ≠ 1`), the geometric partial
sum is bounded uniformly in the length `t`:
`‖∑_{m<t} (e θ)^m‖ ≤ 1/(2·dist₁(θ, 0))`. -/
private lemma geom_e_bound (θ : ℝ) (t : ℕ) (hd : 0 < dist₁ θ 0) :
    ‖∑ m ∈ Finset.range t, (e θ) ^ m‖ ≤ 1 / (2 * dist₁ θ 0) := by
  have hchord : 4 * dist₁ θ 0 ≤ ‖e θ - 1‖ := chord θ
  have hpos : 0 < ‖e θ - 1‖ := lt_of_lt_of_le (by linarith) hchord
  have hzne : e θ ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hpos; exact lt_irrefl 0 hpos
  have hnum : ‖(e θ) ^ t - 1‖ ≤ 2 := by
    calc ‖(e θ) ^ t - 1‖ ≤ ‖(e θ) ^ t‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num
  have hdpos2 : (0 : ℝ) < 2 * dist₁ θ 0 := by linarith
  rw [geom_sum_eq hzne t, norm_div, div_le_iff₀ hpos]
  calc ‖(e θ) ^ t - 1‖ ≤ 2 := hnum
    _ = 1 / (2 * dist₁ θ 0) * (4 * dist₁ θ 0) := by
        rw [eq_comm, div_mul_eq_mul_div, one_mul, div_eq_iff hdpos2.ne']; ring
    _ ≤ 1 / (2 * dist₁ θ 0) * ‖e θ - 1‖ := by
        apply mul_le_mul_of_nonneg_left hchord
        exact le_of_lt (one_div_pos.mpr hdpos2)

/-! ### The `dist₁` lower bound and the harmonic sum -/

/-- **Denominator-sharp lower bound.** For `0 < k < f`,
`dist₁(k/f, 0) ≥ k(f−k)/f²`. Proof: every integer `n` has
`|k/f − n| ≥ k(f−k)/f²` (case split on `n ≤ 0` vs `n ≥ 1`); instantiate at
`n = round(k/f)`. -/
private lemma dist_lb (f k : ℕ) (hk : 0 < k) (hkf : k < f) :
    (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 ≤ dist₁ ((k : ℝ) / (f : ℝ)) 0 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkfR : (k : ℝ) < f := by exact_mod_cast hkf
  have hf0 : (0 : ℝ) < f := by linarith
  have hfne : (f : ℝ) ≠ 0 := hf0.ne'
  have hkfpos : (0 : ℝ) < (k : ℝ) / (f : ℝ) := div_pos hkR hf0
  have key : ∀ n : ℤ,
      (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 ≤ |(k : ℝ) / (f : ℝ) - (n : ℝ)| := by
    intro n
    have h1 : (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 ≤ (k : ℝ) / (f : ℝ) := by
      rw [div_le_div_iff₀ (pow_pos hf0 2) hf0]
      nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) hf0.le]
    have h2 : (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 ≤ ((f : ℝ) - k) / (f : ℝ) := by
      rw [div_le_div_iff₀ (pow_pos hf0 2) hf0]
      nlinarith [mul_nonneg (sq_nonneg ((f : ℝ) - k)) hf0.le]
    rcases le_or_gt (n : ℝ) 0 with hn | hn
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnZ
      have hkf1 : (k : ℝ) / (f : ℝ) < 1 := by rw [div_lt_one hf0]; exact hkfR
      rw [abs_of_nonpos (by linarith)]
      have hfk_eq : ((f : ℝ) - k) / (f : ℝ) = 1 - (k : ℝ) / (f : ℝ) := by field_simp
      linarith
  have hdd : dist₁ ((k : ℝ) / (f : ℝ)) 0
      = |(k : ℝ) / (f : ℝ) - (round ((k : ℝ) / (f : ℝ)) : ℝ)| := by
    unfold dist₁; simp only [sub_zero]
  rw [hdd]
  exact key (round ((k : ℝ) / (f : ℝ)))

/-- `dist₁(k/f, 0) > 0` for `0 < k < f`. -/
private lemma dist_pos (f k : ℕ) (hk : 0 < k) (hkf : k < f) :
    0 < dist₁ ((k : ℝ) / (f : ℝ)) 0 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkfR : (k : ℝ) < f := by exact_mod_cast hkf
  have hfkR : (0 : ℝ) < (f : ℝ) - k := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hBpos : (0 : ℝ) < (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 :=
    div_pos (mul_pos hkR hfkR) (pow_pos hf0 2)
  exact lt_of_lt_of_le hBpos (dist_lb f k hk hkf)

/-- **Per-term harmonic bound.** `1/(2·dist₁(k/f,0)) ≤ (f/2)·(1/k + 1/(f−k))`. -/
private lemma term_le (f k : ℕ) (hk : 0 < k) (hkf : k < f) :
    1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0)
      ≤ ((f : ℝ) / 2) * (1 / (k : ℝ) + 1 / ((f : ℝ) - k)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkfR : (k : ℝ) < f := by exact_mod_cast hkf
  have hfkR : (0 : ℝ) < (f : ℝ) - k := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hlb := dist_lb f k hk hkf
  have hBpos : (0 : ℝ) < (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 :=
    div_pos (mul_pos hkR hfkR) (pow_pos hf0 2)
  have step1 : 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0)
      ≤ 1 / (2 * ((k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2)) := by
    apply one_div_le_one_div_of_le
    · linarith
    · linarith
  have step2 : 1 / (2 * ((k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2))
      = ((f : ℝ) / 2) * (1 / (k : ℝ) + 1 / ((f : ℝ) - k)) := by
    rw [eq_comm]
    field_simp
    ring
  rw [step2] at step1
  exact step1

/-- **The harmonic sum.** `∑_{k<f, k≠0} 1/(2·dist₁(k/f,0)) ≤ f·(1 + log f)`. -/
private lemma sum_H_le (f : ℕ) (hf : 2 ≤ f) :
    ∑ k ∈ Finset.range f,
        (if k = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0))
      ≤ (f : ℝ) * (1 + Real.log f) := by
  -- the two inner harmonic sums are each `≤ 1 + log f`
  have hEq : ((harmonic (f - 1) : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 (f - 1), (1 : ℝ) / k := by
    rw [harmonic_eq_sum_Icc]; push_cast
    apply Finset.sum_congr rfl; intro k _; rw [one_div]
  have hA : ∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / k ≤ 1 + Real.log f := by
    have hIco : Finset.Ico 1 f = Finset.Icc 1 (f - 1) := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIco, ← hEq]
    calc ((harmonic (f - 1) : ℚ) : ℝ) ≤ 1 + Real.log ((f - 1 : ℕ) : ℝ) :=
          harmonic_le_one_add_log (f - 1)
      _ ≤ 1 + Real.log f := by
          have h01 : (0 : ℝ) < ((f - 1 : ℕ) : ℝ) := by
            have : 0 < f - 1 := by omega
            exact_mod_cast this
          have hle : ((f - 1 : ℕ) : ℝ) ≤ (f : ℝ) := by exact_mod_cast Nat.sub_le f 1
          have := Real.log_le_log h01 hle
          linarith
  have hBA : ∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / ((f : ℝ) - k)
      = ∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / k := by
    apply Finset.sum_nbij' (fun k => f - k) (fun k => f - k)
    · intro k hk; rw [Finset.mem_Ico] at hk ⊢; omega
    · intro k hk; rw [Finset.mem_Ico] at hk ⊢; omega
    · intro k hk; rw [Finset.mem_Ico] at hk; omega
    · intro k hk; rw [Finset.mem_Ico] at hk; omega
    · intro k hk; rw [Finset.mem_Ico] at hk; rw [Nat.cast_sub hk.2.le]
  have hB : ∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / ((f : ℝ) - k) ≤ 1 + Real.log f := by
    rw [hBA]; exact hA
  -- convert the guarded `range` sum to a sum over `Ico 1 f`
  have hconv : ∀ k : ℕ,
      (if k = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0))
        = (if k ≠ 0 then 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0) else 0) := by
    intro k; by_cases h : k = 0 <;> simp [h]
  have hrange :
      ∑ k ∈ Finset.range f,
          (if k = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0))
        = ∑ k ∈ Finset.Ico 1 f, 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0) := by
    rw [Finset.sum_congr rfl (fun k _ => hconv k), ← Finset.sum_filter]
    congr 1
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hrange]
  calc ∑ k ∈ Finset.Ico 1 f, 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0)
      ≤ ∑ k ∈ Finset.Ico 1 f, ((f : ℝ) / 2) * (1 / (k : ℝ) + 1 / ((f : ℝ) - k)) := by
        apply Finset.sum_le_sum; intro k hk
        rw [Finset.mem_Ico] at hk
        exact term_le f k hk.1 hk.2
    _ = ((f : ℝ) / 2)
        * ((∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / k)
            + (∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / ((f : ℝ) - k))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ ((f : ℝ) / 2) * (2 * (1 + Real.log f)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hA, hB]
    _ = (f : ℝ) * (1 + Real.log f) := by ring

/-! ### The theorem -/

/-- **Pólya–Vinogradov (primitive characters).** For a primitive Dirichlet
character `χ` mod `f` with `2 ≤ f` (hence `χ ≠ 1`), the partial character sums
are bounded, uniformly in `t`, by `√f · (1 + log f)`. -/
theorem polya_vinogradov {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (t : ℕ) :
    ‖∑ m ∈ Finset.range t, χ (m : ZMod f)‖ ≤ Real.sqrt f * (1 + Real.log f) := by
  haveI : Fact (1 < f) := ⟨hf⟩
  set ψ : AddChar (ZMod f) ℂ := ZMod.stdAddChar with hψ
  have hχ' : χ⁻¹.IsPrimitive := isPrimitive_inv χ hχ
  have hf0 : (0 : ℝ) < f := by
    have : 0 < f := by omega
    exact_mod_cast this
  -- Step 1: Gauss-sum inversion + sum swap.
  have hA : ∑ m ∈ Finset.range t, χ (m : ZMod f)
      = (gaussSum χ⁻¹ ψ)⁻¹
        * ∑ a : ZMod f, χ⁻¹ a * (∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a)) := by
    have expand : ∀ m : ℕ, χ (m : ZMod f)
        = (gaussSum χ⁻¹ ψ)⁻¹ * ∑ a : ZMod f, χ⁻¹ a * ψ ((m : ZMod f) * a) := by
      intro m
      rw [hψ]
      exact dirichlet_inversion' χ hχ (m : ZMod f)
    rw [Finset.sum_congr rfl (fun m _ => expand m), ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
  -- Step 2: `‖τ‖ = √f`.
  have hτnorm : ‖gaussSum χ⁻¹ ψ‖ = Real.sqrt f := by
    rw [hψ, ← Real.sqrt_sq (norm_nonneg _), gaussSum_normSq χ⁻¹ hχ']
  -- Step 3: per-term bound `‖χ⁻¹ a‖ · ‖geom a‖ ≤ H a`.
  have hterm : ∀ a : ZMod f,
      ‖χ⁻¹ a‖ * ‖∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a)‖
        ≤ (if a.val = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((a.val : ℝ) / (f : ℝ)) 0)) := by
    intro a
    by_cases ha : a.val = 0
    · rw [if_pos ha]
      have ha0 : a = 0 := (ZMod.val_eq_zero a).mp ha
      have hz : χ⁻¹ a = 0 := ha0 ▸ MulChar.map_nonunit χ⁻¹ not_isUnit_zero
      simp [hz]
    · rw [if_neg ha]
      have hval_pos : 0 < a.val := Nat.pos_of_ne_zero ha
      have hval_lt : a.val < f := ZMod.val_lt a
      have hnorm_le : ‖χ⁻¹ a‖ ≤ 1 := χ⁻¹.norm_le_one a
      have hGeq : (∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a))
          = ∑ m ∈ Finset.range t, (e ((a.val : ℝ) / (f : ℝ))) ^ m := by
        apply Finset.sum_congr rfl; intro m _
        rw [show ((m : ZMod f) * a) = m • a from by rw [nsmul_eq_mul],
            AddChar.map_nsmul_eq_pow, hψ, stdAddChar_eq_e]
      rw [hGeq]
      have hdpos : 0 < dist₁ ((a.val : ℝ) / (f : ℝ)) 0 := dist_pos f a.val hval_pos hval_lt
      have hgeom : ‖∑ m ∈ Finset.range t, (e ((a.val : ℝ) / (f : ℝ))) ^ m‖
          ≤ 1 / (2 * dist₁ ((a.val : ℝ) / (f : ℝ)) 0) :=
        geom_e_bound ((a.val : ℝ) / (f : ℝ)) t hdpos
      calc ‖χ⁻¹ a‖ * ‖∑ m ∈ Finset.range t, (e ((a.val : ℝ) / (f : ℝ))) ^ m‖
          ≤ 1 * (1 / (2 * dist₁ ((a.val : ℝ) / (f : ℝ)) 0)) :=
            mul_le_mul hnorm_le hgeom (norm_nonneg _) (by norm_num)
        _ = 1 / (2 * dist₁ ((a.val : ℝ) / (f : ℝ)) 0) := one_mul _
  -- Step 4: bound the inner `a`-sum by `f·(1 + log f)`.
  have hinner :
      ‖∑ a : ZMod f, χ⁻¹ a * (∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a))‖
        ≤ (f : ℝ) * (1 + Real.log f) := by
    calc ‖∑ a : ZMod f, χ⁻¹ a * (∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a))‖
        ≤ ∑ a : ZMod f, ‖χ⁻¹ a * (∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a))‖ :=
          norm_sum_le _ _
      _ = ∑ a : ZMod f, ‖χ⁻¹ a‖ * ‖∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a)‖ := by
          simp_rw [norm_mul]
      _ ≤ ∑ a : ZMod f,
            (if a.val = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((a.val : ℝ) / (f : ℝ)) 0)) := by
          apply Finset.sum_le_sum; intro a _; exact hterm a
      _ = ∑ k ∈ Finset.range f,
            (if k = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0)) := by
          apply Finset.sum_nbij' (fun a : ZMod f => a.val) (fun k : ℕ => (k : ZMod f))
          · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
          · intro k _; exact Finset.mem_univ _
          · intro a _; exact ZMod.natCast_zmod_val a
          · intro k hk; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hk)
          · intro a _; rfl
      _ ≤ (f : ℝ) * (1 + Real.log f) := sum_H_le f hf
  -- Step 5: assemble.
  have hspos : 0 < Real.sqrt f := Real.sqrt_pos.mpr hf0
  have hs : Real.sqrt f * Real.sqrt f = f := Real.mul_self_sqrt hf0.le
  have hsinv : (Real.sqrt f)⁻¹ * (f : ℝ) = Real.sqrt f := by
    rw [inv_mul_eq_div, div_eq_iff hspos.ne']; exact hs.symm
  rw [hA, norm_mul, norm_inv, hτnorm]
  calc (Real.sqrt f)⁻¹
        * ‖∑ a : ZMod f, χ⁻¹ a * (∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a))‖
      ≤ (Real.sqrt f)⁻¹ * ((f : ℝ) * (1 + Real.log f)) := by
        apply mul_le_mul_of_nonneg_left hinner
        exact le_of_lt (inv_pos.mpr hspos)
    _ = Real.sqrt f * (1 + Real.log f) := by
        rw [← mul_assoc, hsinv]

/-- **Prefix-max form** (consumed by V2a). Since the Pólya–Vinogradov bound is
uniform in the prefix length `t`, the maximum of `‖∑_{m<t} χ(m)‖` over all
`t ≤ T` obeys the same bound. -/
theorem polya_vinogradov_sup' {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (T : ℕ) :
    (Finset.range (T + 1)).sup' Finset.nonempty_range_add_one
        (fun t => ‖∑ m ∈ Finset.range t, χ (m : ZMod f)‖)
      ≤ Real.sqrt f * (1 + Real.log f) := by
  rw [Finset.sup'_le_iff]
  intro t _
  exact polya_vinogradov χ hχ hf t

end Salt.BV
