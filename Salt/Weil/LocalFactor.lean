/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.Kloosterman

/-!
# Weil track, the α/β local-factor layer (W0.2)

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder). This is the eigenvalue
bookkeeping the Weil descent (W5) and the moment layer (W2) consume. Following Harcos §3:
for a Kloosterman value `S : ℝ` and a prime `p`, the local factor `1 + S·T + p·T²` factors
as `(1 − αT)(1 − βT)`, so the reciprocal roots `α, β ∈ ℂ` are the roots of `z² + S·z + p`,
i.e. `α + β = −S` and `α·β = p` (Vieta).

* **The root pair** (`exists_localRootPair`, `localRootPair`, `localAlpha`, `localBeta`):
  existence via a complex square root of the discriminant, then `Classical.choose` for a
  concrete pair. `localRootPair_add`/`localRootPair_mul` are the two Vieta relations.

* **The power sums** (`localPowerSum S p n = αⁿ + βⁿ`): base cases `P₀ = 2`, `P₁ = −S`, and
  the **Newton recurrence** `Pₙ₊₂ = −S·Pₙ₊₁ − p·Pₙ` — pure `ring` algebra from Vieta. This
  recurrence is the atom the extraction consumes; no power series are needed.

* **Reality** (`localPowerSum_conj`, `localPowerSum_im`): the pair is conjugation-invariant
  (real quadratic), so every `Pₙ` is real.

* **Modulus extraction** (`abs_le_sqrt_of_powerSum_bound`, W5.2's core): if `‖αⁿ + βⁿ‖ ≤ C·√pⁿ`
  for all large `n` and `α·β = p`, then `‖α‖ = ‖β‖ = √p`. A geometric-domination argument:
  a strictly larger root would make the power sums grow like `‖α‖ⁿ`, beating any `C·√pⁿ`.
-/

namespace Salt.Weil

open ComplexConjugate Filter

/-! ### The root pair -/

open Polynomial in
/-- Every complex number has a complex square root (ℂ is algebraically closed): a root of
`X² − C w`. -/
private theorem exists_complexSqrt (w : ℂ) : ∃ z : ℂ, z ^ 2 = w := by
  have hdeg : 0 < (X ^ 2 - C w).degree := by
    rw [degree_X_pow_sub_C (by norm_num) w]; norm_num
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  refine ⟨z, ?_⟩
  have hz' : (X ^ 2 - C w).eval z = 0 := hz
  rw [eval_sub, eval_pow, eval_X, eval_C] at hz'
  exact sub_eq_zero.mp hz'

/-- **The local root pair exists.** For `S : ℝ` and `p : ℕ`, there is a pair `(α, β)` of
complex numbers with `α + β = −S` and `α·β = p` — the reciprocal roots of the local factor
`1 + S·T + p·T²`, equivalently the roots of `z² + S·z + p`. Built from the quadratic formula
`α, β = (−S ± √(S² − 4p))/2` over ℂ. -/
theorem exists_localRootPair (S : ℝ) (p : ℕ) :
    ∃ q : ℂ × ℂ, q.1 + q.2 = -(S : ℂ) ∧ q.1 * q.2 = (p : ℂ) := by
  obtain ⟨d, hd⟩ := exists_complexSqrt ((S : ℂ) ^ 2 - 4 * (p : ℂ))
  exact ⟨((-(S : ℂ) + d) / 2, (-(S : ℂ) - d) / 2), by ring, by linear_combination (-1 / 4 : ℂ) * hd⟩

/-- The chosen local root pair `(α, β)`. -/
noncomputable def localRootPair (S : ℝ) (p : ℕ) : ℂ × ℂ := (exists_localRootPair S p).choose

/-- The first local root `α`. -/
noncomputable def localAlpha (S : ℝ) (p : ℕ) : ℂ := (localRootPair S p).1

/-- The second local root `β`. -/
noncomputable def localBeta (S : ℝ) (p : ℕ) : ℂ := (localRootPair S p).2

/-- **Vieta, sum.** `α + β = −S`. -/
theorem localRootPair_add (S : ℝ) (p : ℕ) :
    localAlpha S p + localBeta S p = -(S : ℂ) :=
  (exists_localRootPair S p).choose_spec.1

/-- **Vieta, product.** `α·β = p`. -/
theorem localRootPair_mul (S : ℝ) (p : ℕ) :
    localAlpha S p * localBeta S p = (p : ℂ) :=
  (exists_localRootPair S p).choose_spec.2

/-! ### The power sums and the Newton recurrence -/

/-- The **local power sum** `Pₙ = αⁿ + βⁿ`, the `n`-th symmetric power of the local roots. -/
noncomputable def localPowerSum (S : ℝ) (p n : ℕ) : ℂ :=
  localAlpha S p ^ n + localBeta S p ^ n

/-- Base case: `P₀ = 2`. -/
theorem localPowerSum_zero (S : ℝ) (p : ℕ) : localPowerSum S p 0 = 2 := by
  rw [localPowerSum, pow_zero, pow_zero]; norm_num

/-- Base case: `P₁ = −S`. -/
theorem localPowerSum_one (S : ℝ) (p : ℕ) : localPowerSum S p 1 = -(S : ℂ) := by
  rw [localPowerSum, pow_one, pow_one]; exact localRootPair_add S p

/-- **Newton recurrence.** `Pₙ₊₂ = −S·Pₙ₊₁ − p·Pₙ`. Pure `ring` algebra from the two Vieta
relations: `αⁿ⁺²+βⁿ⁺² = (α+β)(αⁿ⁺¹+βⁿ⁺¹) − (α·β)(αⁿ+βⁿ)`. This is the atom the descent
consumes — the whole `‖·‖`-extraction rides on this three-term linear recurrence. -/
theorem localPowerSum_rec (S : ℝ) (p n : ℕ) :
    localPowerSum S p (n + 2) =
      -(S : ℂ) * localPowerSum S p (n + 1) - (p : ℂ) * localPowerSum S p n := by
  have hs := localRootPair_add S p
  have hp := localRootPair_mul S p
  simp only [localPowerSum]
  rw [← hs, ← hp]
  ring

/-! ### Reality -/

/-- **Reality (conjugation form).** `conj Pₙ = Pₙ`. The pair `{α, β}` is invariant under
complex conjugation — it is the root set of the real quadratic `z² + S·z + p` — so either both
roots are real or they are a conjugate pair; in both cases `αⁿ + βⁿ` is fixed by `conj`. -/
theorem localPowerSum_conj (S : ℝ) (p n : ℕ) :
    conj (localPowerSum S p n) = localPowerSum S p n := by
  simp only [localPowerSum, map_add, map_pow]
  set α := localAlpha S p with hα_def
  set β := localBeta S p with hβ_def
  have hs : α + β = -(S : ℂ) := localRootPair_add S p
  have hp : α * β = (p : ℂ) := localRootPair_mul S p
  have hcs : conj α + conj β = α + β := by
    rw [← map_add, hs, map_neg, Complex.conj_ofReal]
  have hcp : conj α * conj β = α * β := by
    rw [← map_mul, hp, Complex.conj_natCast]
  have hfac : (conj α - α) * (conj α - β) = 0 := by
    linear_combination (conj α) * hcs - hcp
  rcases mul_eq_zero.mp hfac with h | h
  · have hα' : conj α = α := sub_eq_zero.mp h
    have hβ' : conj β = β := by
      have h2 := hcs; rw [hα'] at h2; exact add_left_cancel h2
    rw [hα', hβ']
  · have hα' : conj α = β := sub_eq_zero.mp h
    have hβ' : conj β = α := by
      have h2 := hcs; rw [hα', add_comm α β] at h2; exact add_left_cancel h2
    rw [hα', hβ']; ring

/-- **Reality (imaginary-part form).** `Pₙ` has zero imaginary part. -/
theorem localPowerSum_im (S : ℝ) (p n : ℕ) : (localPowerSum S p n).im = 0 :=
  Complex.conj_eq_iff_im.mp (localPowerSum_conj S p n)

/-! ### Modulus extraction (W5.2's core) -/

/-- **Modulus extraction.** If the power sums `αⁿ + βⁿ` are dominated by `C·√pⁿ` for all large
`n`, and `α·β = p > 0`, then both roots sit exactly on the circle `‖α‖ = ‖β‖ = √p`. This is the
analytic heart of the Weil bound descent: a strictly larger root, say `‖α‖ > √p`, would force
`‖β‖ = p/‖α‖ < √p`, so `‖αⁿ + βⁿ‖ ≥ ‖α‖ⁿ − ‖β‖ⁿ` would grow like `(‖α‖/√p)ⁿ · √pⁿ` with the
ratio `> 1` — eventually beating any `C·√pⁿ`, contradiction. Hence `‖α‖ ≤ √p`, and symmetrically
`‖β‖ ≤ √p`; with `‖α‖·‖β‖ = p = (√p)²` both are forced to equality. -/
theorem abs_le_sqrt_of_powerSum_bound {α β : ℂ} {p : ℕ} {C : ℝ} {N₀ : ℕ} (hp : 0 < p)
    (hbound : ∀ n : ℕ, N₀ ≤ n → ‖α ^ n + β ^ n‖ ≤ C * Real.sqrt p ^ n)
    (hprod : α * β = (p : ℂ)) :
    ‖α‖ = Real.sqrt p ∧ ‖β‖ = Real.sqrt p := by
  set s := Real.sqrt p with hs_def
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hpR
  have hs_sq : s * s = (p : ℝ) := Real.mul_self_sqrt hpR.le
  have hnorm_prod : ‖α‖ * ‖β‖ = (p : ℝ) := by
    rw [← norm_mul, hprod, Complex.norm_natCast]
  -- Core one-sided bound: whichever root we call `x`, its modulus is `≤ √p`.
  have key : ∀ x y : ℂ, x * y = (p : ℂ) →
      (∀ n : ℕ, N₀ ≤ n → ‖x ^ n + y ^ n‖ ≤ C * s ^ n) → ‖x‖ ≤ s := by
    intro x y hxy hb
    by_contra hcon
    have hlt : s < ‖x‖ := not_le.mp hcon  -- `s < ‖x‖`
    have hxnorm_prod : ‖x‖ * ‖y‖ = (p : ℝ) := by
      rw [← norm_mul, hxy, Complex.norm_natCast]
    have hx_pos : 0 < ‖x‖ := lt_trans hs_pos hlt
    have hy_pos : 0 < ‖y‖ := by nlinarith [hxnorm_prod, hpR, hx_pos, norm_nonneg y]
    have hy_lt : ‖y‖ < s := by
      have h1 : s * ‖y‖ < ‖x‖ * ‖y‖ := mul_lt_mul_of_pos_right hlt hy_pos
      rw [hxnorm_prod, ← hs_sq] at h1
      exact lt_of_mul_lt_mul_left h1 hs_pos.le
    set r₁ := ‖x‖ / s with hr1_def
    set r₂ := ‖y‖ / s with hr2_def
    have hr1_gt : 1 < r₁ := by rw [hr1_def, lt_div_iff₀ hs_pos, one_mul]; exact hlt
    have hr2_nonneg : 0 ≤ r₂ := div_nonneg (norm_nonneg y) hs_pos.le
    have hr2_lt : r₂ < 1 := by rw [hr2_def, div_lt_one hs_pos]; exact hy_lt
    -- The dominated bound, rescaled: `r₁ⁿ − r₂ⁿ ≤ C` for all `n ≥ N₀`.
    have hdiv : ∀ n : ℕ, N₀ ≤ n → r₁ ^ n - r₂ ^ n ≤ C := by
      intro n hn
      have hrev : ‖x‖ ^ n - ‖y‖ ^ n ≤ ‖x ^ n + y ^ n‖ := by
        have h := norm_sub_norm_le (x ^ n) (-(y ^ n))
        simpa [norm_pow, norm_neg, sub_neg_eq_add] using h
      have hsn_pos : 0 < s ^ n := pow_pos hs_pos n
      rw [hr1_def, hr2_def, div_pow, div_pow, div_sub_div_same, div_le_iff₀ hsn_pos]
      exact hrev.trans (hb n hn)
    -- But `r₁ⁿ − r₂ⁿ → ∞` since `r₁ > 1` and `r₂ⁿ → 0`, contradicting the uniform bound `C`.
    have htend : Tendsto (fun n => r₁ ^ n - r₂ ^ n) atTop atTop := by
      have h1 : Tendsto (fun n => r₁ ^ n) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt hr1_gt
      have h2 : Tendsto (fun n => r₂ ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hr2_nonneg hr2_lt
      simpa [sub_eq_add_neg] using h1.atTop_add h2.neg
    obtain ⟨n, hgt, hge⟩ :=
      ((htend.eventually_gt_atTop C).and (eventually_ge_atTop N₀)).exists
    exact absurd (hdiv n hge) (not_le.mpr hgt)
  have hα_le : ‖α‖ ≤ s := key α β hprod hbound
  have hβ_le : ‖β‖ ≤ s := key β α (by rw [mul_comm]; exact hprod)
    (fun n hn => by rw [add_comm]; exact hbound n hn)
  refine ⟨le_antisymm hα_le ?_, le_antisymm hβ_le ?_⟩
  · nlinarith [hnorm_prod, hs_sq, mul_le_mul_of_nonneg_left hβ_le (norm_nonneg α), hs_pos]
  · nlinarith [hnorm_prod, hs_sq, mul_le_mul_of_nonneg_right hα_le (norm_nonneg β), hs_pos]

end Salt.Weil
