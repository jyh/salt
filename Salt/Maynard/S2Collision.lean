/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.CollisionQuant
import Salt.Maynard.S2DiagLam
import Salt.Maynard.S2DiagRestricted
import Salt.Maynard.DiagonalS2

/-!
# S2-COLLISION — the `∏φ(lcm)` analog of N4.4's `collision_lower_order`

C4's S₂ main term uses the FULL `dₘ = eₘ = 1`-restricted S₂ diagonal
`Qdiag_m = ∑_{dₘ=eₘ=1} lam·lam/∏φ(lcm)`, but the actual count-weighted `S₂^(m)`
counts only COMPATIBLE (non-collision) pairs.  The difference is the
`m`-restricted S₂ **collision form**

  `s2CollisionForm = ∑_{dₘ=eₘ=1, colliding} lam·lam/∏φ(lcm)`,

and this file bounds it — genuinely SIGNED, via the Möbius/`euler_tail`
structure — by `(Cs k²/D₀)·(nonneg S₂ diagonal yside)`.  It is the exact
`∏φ(lcm)` analog of `collision_lower_order` (`CollisionQuant.lean`, for `∏lcm`).

## Route (mirrors N4.4)

* Structural (reused/ported verbatim, summand-agnostic): the Möbius expansion
  of the collision indicator over collision moduli `t ∣ cRad`
  (`compat_moebius_expansion_M`), the prime-to-slot assignment expansion
  (`inner_collision_expand_M`), and the `R`-free `euler_tail`.
* The genuinely new piece: the **S₂ constrained inner evaluation**
  `inner_exact_S2` — the `(σ,τ)`-forced double `lam·lam/∏φ(lcm)` sum
  diagonalises (via `s2_diag_lam`'s `stepA` + `prod_totient_gcd_expand`) to
  `∑_u (∏ g(uᵢ))·Vₘ(u∨σ)·Vₘ(u∨τ)`, where `Vₘ = lamPhiContractM` is the
  `m`-restricted contraction of `S2DiagRestricted.lean`.  This does NOT
  collapse to a single diagonal term (the `d/φ` weight prevents it — the
  S₂-vs-S₁ asymmetry), which is exactly why the per-assignment absolute
  bound is the wall (`S2InnerControlled`, see below).

## Status

`inner_exact_S2` (identity) and the whole structural assembly land sorry-free.
The per-assignment ABSOLUTE bound — the `∏φ(lcm)` analog of N4.4's
`inner_abs_le`, whose S₁ proof crucially used the single-term collapse of the
forced sum — is isolated as the precise `Prop` `S2InnerControlled` (strictly
narrower than the collision bound) and the collision bound is assembled ON TOP
of it (`s2_collision_lower_order`).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-- The explicit S₂ collision constant. -/
noncomputable def Cs : ℝ := 12

/-- Indicator-product helper over a general `Finset` (local copy; `private`
in the S₁ file). -/
private theorem prod_ite_one_z {ι : Type*} (s : Finset ι) (P : ι → Prop)
    [DecidablePred P] :
    (∏ x ∈ s, if P x then (1 : ℝ) else 0) = if ∀ x ∈ s, P x then 1 else 0 := by
  by_cases h : ∀ x ∈ s, P x
  · rw [if_pos h]
    exact Finset.prod_eq_one fun x hx => if_pos (h x hx)
  · rw [if_neg h]
    obtain ⟨x, hx⟩ := not_forall.mp h
    obtain ⟨hxs, hPx⟩ := Classical.not_imp.mp hx
    exact Finset.prod_eq_zero hxs (if_neg hPx)

/-- Move the innermost of three nested sums to the front (local copy; `private`
in the S₁ file). -/
private theorem sum_move3S {α β γ δ : Type*} [AddCommMonoid δ]
    (A : Finset α) (B : Finset β) (C : Finset γ) (F : α → β → γ → δ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c)
      = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, F a b c := by
  rw [← Finset.sum_product']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  exact Finset.sum_product' A B (fun a b => F a b c)

/-! ## The S₂ diagonal summand and the three `m`-restricted quadratic forms -/

/-- The S₂ diagonal summand for a pair `(d,e)`:
`lam d · lam e / ∏ᵢ φ(lcm(dᵢ,eᵢ))`. -/
noncomputable def s2Summand (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) (d e : Fin k → ℕ) : ℝ :=
  lam k R W y d * lam k R W y e / ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)

/-- The full `dₘ = eₘ = 1`-restricted S₂ diagonal form (`= Qdiag_m`). -/
noncomputable def s2FullFormM (k R W : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ (kSieveIndex k R W).filter (fun d => d m = 1),
    ∑ e ∈ (kSieveIndex k R W).filter (fun e => e m = 1), s2Summand k R W y d e

/-- The collision part of the `m`-restricted S₂ diagonal form. -/
noncomputable def s2CollisionForm (k R W : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ (kSieveIndex k R W).filter (fun d => d m = 1),
    ∑ e ∈ (kSieveIndex k R W).filter (fun e => e m = 1),
      if IsCollisionPair d e then s2Summand k R W y d e else 0

/-- The compatible (non-collision) part of the `m`-restricted S₂ diagonal form. -/
noncomputable def s2CompatFormM (k R W : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ (kSieveIndex k R W).filter (fun d => d m = 1),
    ∑ e ∈ (kSieveIndex k R W).filter (fun e => e m = 1),
      if IsCollisionPair d e then 0 else s2Summand k R W y d e

/-! ## The exact decomposition -/

/-- **Exact decomposition.** The full `m`-restricted S₂ diagonal form splits,
pair by pair, into its collision part and its compatible part. Unconditional. -/
theorem s2_full_split_M (k R W : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) :
    s2CollisionForm k R W m y + s2CompatFormM k R W m y = s2FullFormM k R W m y := by
  unfold s2CollisionForm s2CompatFormM s2FullFormM
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro d _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro e _
  split_ifs <;> ring

/-- **The reduction C4 wants (unconditional).** The compatible (count-weighted)
S₂ main term equals the full `m`-restricted S₂ diagonal minus the collision
correction: `s2CompatFormM = s2FullFormM − s2CollisionForm`. -/
theorem s2_compat_eq_M (k R W : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) :
    s2CompatFormM k R W m y = s2FullFormM k R W m y - s2CollisionForm k R W m y := by
  have h := s2_full_split_M k R W m y
  linarith

/-! ## The S₂ constrained inner evaluation (the genuinely new derivation) -/

/-- **`inner_exact_S2`, the S₂ constrained diagonalisation.** The `(σ,τ)`-forced
`dₘ = eₘ = 1`-restricted double `lam·lam/∏φ(lcm)` sum diagonalises exactly to a
signed `u`-sum of `g`-weighted `Vₘ`-contractions.  Unlike the S₁ `inner_exact`,
the forced side does **not** collapse to a single term — it stays the
`m`-restricted contraction `Vₘ = lamPhiContractM` (the `d/φ` weight; the
S₂-vs-S₁ asymmetry).  Proof mirrors `inner_exact`/`s2_diag_lam` `stepA`:
per-pair `lam·lam/∏φ(lcm) = (lam/∏φ(d))(lam/∏φ(e))·∏φ(gcd)`, then
`∏φ(gcd) = ∑_u [u∣d ∧ u∣e] ∏g(uᵢ)` (`prod_totient_gcd_expand`), factor the
`u`-sum out, and read the two forced sides off as `Vₘ(u∨σ)`, `Vₘ(u∨τ)`. -/
theorem inner_exact_S2 (k R W : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (σ τ : Fin k → ℕ) :
    ∑ d ∈ ((kSieveIndex k R W).filter (fun d => d m = 1)).filter
        (fun d => ∀ i, σ i ∣ d i),
      ∑ e ∈ ((kSieveIndex k R W).filter (fun e => e m = 1)).filter
          (fun e => ∀ i, τ i ∣ e i),
        s2Summand k R W y d e
      = ∑ u ∈ kSieveIndex k R W, (∏ i, (gMult (u i) : ℝ))
          * lamPhiContractM k R W m y (fun i => Nat.lcm (u i) (σ i))
          * lamPhiContractM k R W m y (fun i => Nat.lcm (u i) (τ i)) := by
  classical
  set 𝒮 := (kSieveIndex k R W).filter (fun d => d m = 1) with h𝒮
  have hmem : ∀ {d : Fin k → ℕ}, d ∈ 𝒮 → d ∈ kSieveIndex k R W := by
    intro d hd; exact (Finset.mem_filter.mp hd).1
  -- per-pair algebra: `lam·lam/∏φ(lcm) = (lam/∏φ(d))(lam/∏φ(e))·∏φ(gcd)`.
  have halg : ∀ d ∈ kSieveIndex k R W, ∀ e ∈ kSieveIndex k R W,
      s2Summand k R W y d e
        = (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ))
            * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
            * ∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ) := by
    intro d hd e he
    unfold s2Summand
    have hdsq : ∀ i, Squarefree (d i) := fun i => ((mem_kSieveIndex_iff d).mp hd).1 i
    have hesq : ∀ i, Squarefree (e i) := fun i => ((mem_kSieveIndex_iff e).mp he).1 i
    have hφd : (∏ i, (Nat.totient (d i) : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro i _
      exact_mod_cast (Nat.totient_pos.mpr (kSieveIndex_coord_pos hd i)).ne'
    have hφe : (∏ i, (Nat.totient (e i) : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro i _
      exact_mod_cast (Nat.totient_pos.mpr (kSieveIndex_coord_pos he i)).ne'
    have hφlcm : (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro i _
      have : 0 < Nat.totient (Nat.lcm (d i) (e i)) := Nat.totient_pos.mpr
        (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (kSieveIndex_coord_pos hd i).ne'
          (kSieveIndex_coord_pos he i).ne'))
      exact_mod_cast this.ne'
    have hkey : (∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))
          * (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))
        = (∏ i, (Nat.totient (d i) : ℝ)) * (∏ i, (Nat.totient (e i) : ℝ)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      exact totient_gcd_mul_totient_lcm (hdsq i) (hesq i)
    rw [div_eq_iff hφlcm]
    rw [show (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ))
            * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
            * (∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))
            * (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))
          = (lam k R W y d * lam k R W y e)
            / ((∏ i, (Nat.totient (d i) : ℝ)) * (∏ i, (Nat.totient (e i) : ℝ)))
            * ((∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))
              * (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))) from by ring]
    rw [hkey, div_mul_cancel₀ _ (mul_ne_zero hφd hφe)]
  calc ∑ d ∈ 𝒮.filter (fun d => ∀ i, σ i ∣ d i),
        ∑ e ∈ 𝒮.filter (fun e => ∀ i, τ i ∣ e i), s2Summand k R W y d e
      = ∑ d ∈ 𝒮, ∑ e ∈ 𝒮, ∑ u ∈ kSieveIndex k R W,
          (∏ i, (gMult (u i) : ℝ))
            * ((if ∀ i, Nat.lcm (u i) (σ i) ∣ d i then (1:ℝ) else 0)
                * (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ)))
            * ((if ∀ i, Nat.lcm (u i) (τ i) ∣ e i then (1:ℝ) else 0)
                * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro d hd
        by_cases hσd : ∀ i, σ i ∣ d i
        · rw [if_pos hσd, Finset.sum_filter]
          apply Finset.sum_congr rfl; intro e he
          by_cases hτe : ∀ i, τ i ∣ e i
          · rw [if_pos hτe, halg d (hmem hd) e (hmem he),
              prod_totient_gcd_expand (hmem hd), Finset.mul_sum]
            apply Finset.sum_congr rfl; intro u _
            by_cases hud : ∀ i, u i ∣ d i
            · by_cases hue : ∀ i, u i ∣ e i
              · rw [if_pos (fun i => ⟨hud i, hue i⟩),
                  if_pos (fun i => Nat.lcm_dvd (hud i) (hσd i)),
                  if_pos (fun i => Nat.lcm_dvd (hue i) (hτe i))]
                ring
              · obtain ⟨i₀, hi₀⟩ := not_forall.mp hue
                rw [if_neg (fun h => hi₀ (h i₀).2),
                  if_neg (fun h : ∀ i, Nat.lcm (u i) (τ i) ∣ e i =>
                    hi₀ ((Nat.dvd_lcm_left _ _).trans (h i₀)))]
                ring
            · obtain ⟨i₀, hi₀⟩ := not_forall.mp hud
              rw [if_neg (fun h => hi₀ (h i₀).1),
                if_neg (fun h : ∀ i, Nat.lcm (u i) (σ i) ∣ d i =>
                  hi₀ ((Nat.dvd_lcm_left _ _).trans (h i₀)))]
              ring
          · rw [if_neg hτe]
            symm; apply Finset.sum_eq_zero; intro u _
            obtain ⟨i₀, hi₀⟩ := not_forall.mp hτe
            rw [if_neg (fun h : ∀ i, Nat.lcm (u i) (τ i) ∣ e i =>
              hi₀ ((Nat.dvd_lcm_right _ _).trans (h i₀)))]
            ring
        · rw [if_neg hσd]
          symm; apply Finset.sum_eq_zero; intro e _
          apply Finset.sum_eq_zero; intro u _
          obtain ⟨i₀, hi₀⟩ := not_forall.mp hσd
          rw [if_neg (fun h : ∀ i, Nat.lcm (u i) (σ i) ∣ d i =>
            hi₀ ((Nat.dvd_lcm_right _ _).trans (h i₀)))]
          ring
    _ = ∑ u ∈ kSieveIndex k R W, (∏ i, (gMult (u i) : ℝ))
          * (∑ d ∈ 𝒮,
              (if ∀ i, Nat.lcm (u i) (σ i) ∣ d i then (1:ℝ) else 0)
                * (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ)))
          * (∑ e ∈ 𝒮,
              (if ∀ i, Nat.lcm (u i) (τ i) ∣ e i then (1:ℝ) else 0)
                * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))) := by
        rw [sum_move3S]
        apply Finset.sum_congr rfl; intro u _
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _
        ring
    _ = ∑ u ∈ kSieveIndex k R W, (∏ i, (gMult (u i) : ℝ))
          * lamPhiContractM k R W m y (fun i => Nat.lcm (u i) (σ i))
          * lamPhiContractM k R W m y (fun i => Nat.lcm (u i) (τ i)) := by
        apply Finset.sum_congr rfl; intro u _
        congr 1
        · congr 1
          rw [lamPhiContractM, ← h𝒮]
          apply Finset.sum_congr rfl; intro d _
          split_ifs <;> ring
        · rw [lamPhiContractM, ← h𝒮]
          apply Finset.sum_congr rfl; intro e _
          split_ifs <;> ring

/-! ## Structural machinery (`m`-restricted ports of the N4.4 collision lemmas) -/

/-- **`m`-restricted Möbius collision expansion.** The compatible form expands
exactly over collision moduli with signed Möbius weights.  Port of
`compat_moebius_expansion` with the `dₘ = eₘ = 1` filters threaded through
(the per-pair Möbius identity is index-agnostic). -/
theorem compat_moebius_expansion_M (k R W : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) :
    s2CompatFormM k R W m y
      = ∑ t ∈ collisionModuli k R, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ (kSieveIndex k R W).filter (fun d => d m = 1),
              ∑ e ∈ (kSieveIndex k R W).filter (fun e => e m = 1),
                (if t ∣ cRad d e then s2Summand k R W y d e else 0) := by
  unfold s2CompatFormM
  set 𝒮 := (kSieveIndex k R W).filter (fun d => d m = 1) with h𝒮
  have hmem : ∀ {d : Fin k → ℕ}, d ∈ 𝒮 → d ∈ kSieveIndex k R W := by
    intro d hd; exact (Finset.mem_filter.mp hd).1
  have hpt : ∀ d ∈ 𝒮, ∀ e ∈ 𝒮,
      (if IsCollisionPair d e then 0 else s2Summand k R W y d e)
        = ∑ t ∈ collisionModuli k R, ((μ t : ℤ) : ℝ)
            * (if t ∣ cRad d e then s2Summand k R W y d e else 0) := by
    intro d hd e he
    have hd' := hmem hd
    have he' := hmem he
    have hmoeb : (∑ t ∈ collisionModuli k R,
        if t ∣ cRad d e then ((μ t : ℤ) : ℝ) else 0)
        = if cRad d e = 1 then 1 else 0 := by
      rw [← sum_divisors_moebius_eq (cRad d e), collisionModuli]
      exact (sum_divisors_eq_sum_range (cRad_pos hd' he').ne' (cRad_le hd' he')
        (fun t => ((μ t : ℤ) : ℝ))).symm
    calc (if IsCollisionPair d e then 0 else s2Summand k R W y d e)
        = (if cRad d e = 1 then 1 else 0) * s2Summand k R W y d e := by
          by_cases hc : IsCollisionPair d e
          · rw [if_pos hc,
              if_neg (fun h1 => ((cRad_eq_one_iff hd' he').mp h1) hc), zero_mul]
          · rw [if_neg hc, if_pos ((cRad_eq_one_iff hd' he').mpr hc), one_mul]
      _ = (∑ t ∈ collisionModuli k R,
            if t ∣ cRad d e then ((μ t : ℤ) : ℝ) else 0)
            * s2Summand k R W y d e := by rw [hmoeb]
      _ = ∑ t ∈ collisionModuli k R, ((μ t : ℤ) : ℝ)
            * (if t ∣ cRad d e then s2Summand k R W y d e else 0) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro u _
          split_ifs <;> ring
  calc ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
        (if IsCollisionPair d e then 0 else s2Summand k R W y d e)
      = ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
          ∑ t ∈ collisionModuli k R, ((μ t : ℤ) : ℝ)
            * (if t ∣ cRad d e then s2Summand k R W y d e else 0) := by
        apply Finset.sum_congr rfl; intro d hd
        apply Finset.sum_congr rfl; intro e he
        exact hpt d hd e he
    _ = ∑ t ∈ collisionModuli k R, ∑ d ∈ 𝒮,
          ∑ e ∈ 𝒮, ((μ t : ℤ) : ℝ)
            * (if t ∣ cRad d e then s2Summand k R W y d e else 0) :=
        sum_move3S _ _ _ _
    _ = ∑ t ∈ collisionModuli k R, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
              (if t ∣ cRad d e then s2Summand k R W y d e else 0) := by
        apply Finset.sum_congr rfl; intro t _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.mul_sum]

/-- **`m`-restricted `inner_collision_expand`.** For squarefree `t`, the
`t ∣ cRad`-guarded restricted double sum expands exactly over prime-to-slot
assignments.  Port of `inner_collision_expand`; the slot machinery
(`slotProd_dvd_iff`, `collision_indicator`) is index-agnostic. -/
theorem inner_collision_expand_M (k R W : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    {t : ℕ} (ht : Squarefree t) :
    (∑ d ∈ (kSieveIndex k R W).filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R W).filter (fun e => e m = 1),
        if t ∣ cRad d e then s2Summand k R W y d e else 0)
      = ∑ α ∈ assignments k t,
          ∑ d ∈ ((kSieveIndex k R W).filter (fun d => d m = 1)).filter
              (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
            ∑ e ∈ ((kSieveIndex k R W).filter (fun e => e m = 1)).filter
              (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
              s2Summand k R W y d e := by
  classical
  set 𝒮 := (kSieveIndex k R W).filter (fun d => d m = 1) with h𝒮
  have hmem : ∀ {d : Fin k → ℕ}, d ∈ 𝒮 → d ∈ kSieveIndex k R W := by
    intro d hd; exact (Finset.mem_filter.mp hd).1
  have hind : ∀ d ∈ 𝒮, ∀ e ∈ 𝒮,
      (if t ∣ cRad d e then (1 : ℝ) else 0)
        = ∑ α ∈ assignments k t,
            (if ∀ i, slotProd t α Prod.fst i ∣ d i then (1 : ℝ) else 0)
              * (if ∀ i, slotProd t α Prod.snd i ∣ e i then (1 : ℝ) else 0) := by
    intro d hd e he
    have hd' := hmem hd
    have he' := hmem he
    calc (if t ∣ cRad d e then (1 : ℝ) else 0)
        = if ∀ p ∈ t.primeFactors, p ∣ cRad d e then (1 : ℝ) else 0 := by
          congr 1
          rw [eq_iff_iff]
          exact squarefree_dvd_iff_primes ht
      _ = ∏ p ∈ t.primeFactors, (if p ∣ cRad d e then (1 : ℝ) else 0) :=
          (prod_ite_one_z _ _).symm
      _ = ∏ p ∈ t.primeFactors, ∑ ij ∈ (Finset.univ : Finset (Fin k)).offDiag,
            (if p ∣ d ij.1 ∧ p ∣ e ij.2 then (1 : ℝ) else 0) := by
          apply Finset.prod_congr rfl; intro p hp
          exact collision_indicator hd' he' (Nat.prime_of_mem_primeFactors hp)
      _ = ∑ α ∈ assignments k t, ∏ q ∈ t.primeFactors.attach,
            (if (q : ℕ) ∣ d ((α q.1 q.2).1) ∧ (q : ℕ) ∣ e ((α q.1 q.2).2)
              then (1 : ℝ) else 0) := by
          rw [assignments]
          exact Finset.prod_sum _ _ _
      _ = ∑ α ∈ assignments k t,
            (if ∀ i, slotProd t α Prod.fst i ∣ d i then (1 : ℝ) else 0)
              * (if ∀ i, slotProd t α Prod.snd i ∣ e i then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro α _
          have hsplit : ∀ q ∈ t.primeFactors.attach,
              (if (q : ℕ) ∣ d ((α q.1 q.2).1) ∧ (q : ℕ) ∣ e ((α q.1 q.2).2)
                then (1 : ℝ) else 0)
              = (if (q : ℕ) ∣ d ((α q.1 q.2).1) then (1 : ℝ) else 0)
                  * (if (q : ℕ) ∣ e ((α q.1 q.2).2) then (1 : ℝ) else 0) := by
            intro q _
            by_cases h1 : (q : ℕ) ∣ d ((α q.1 q.2).1) <;>
              by_cases h2 : (q : ℕ) ∣ e ((α q.1 q.2).2) <;> simp [h1, h2]
          rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib,
            prod_ite_one_z, prod_ite_one_z]
          have h1 : (∀ q ∈ t.primeFactors.attach, (q : ℕ) ∣ d ((α q.1 q.2).1))
              ↔ ∀ i, slotProd t α Prod.fst i ∣ d i := by
            constructor
            · intro h
              apply (slotProd_dvd_iff ht α Prod.fst d).mpr
              intro q
              exact h q (Finset.mem_attach _ q)
            · intro h q _
              exact (slotProd_dvd_iff ht α Prod.fst d).mp h q
          have h2 : (∀ q ∈ t.primeFactors.attach, (q : ℕ) ∣ e ((α q.1 q.2).2))
              ↔ ∀ i, slotProd t α Prod.snd i ∣ e i := by
            constructor
            · intro h
              apply (slotProd_dvd_iff ht α Prod.snd e).mpr
              intro q
              exact h q (Finset.mem_attach _ q)
            · intro h q _
              exact (slotProd_dvd_iff ht α Prod.snd e).mp h q
          congr 1
          · congr 1; rw [eq_iff_iff]; exact h1
          · congr 1; rw [eq_iff_iff]; exact h2
  calc (∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
        if t ∣ cRad d e then s2Summand k R W y d e else 0)
      = ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
          ∑ α ∈ assignments k t,
            (if ∀ i, slotProd t α Prod.fst i ∣ d i then (1 : ℝ) else 0)
              * (if ∀ i, slotProd t α Prod.snd i ∣ e i then (1 : ℝ) else 0)
              * s2Summand k R W y d e := by
        apply Finset.sum_congr rfl; intro d hd
        apply Finset.sum_congr rfl; intro e he
        have hstep : (if t ∣ cRad d e then s2Summand k R W y d e else 0)
            = (if t ∣ cRad d e then (1 : ℝ) else 0) * s2Summand k R W y d e := by
          split_ifs <;> ring
        rw [hstep, hind d hd e he, Finset.sum_mul]
    _ = ∑ α ∈ assignments k t, ∑ d ∈ 𝒮,
          ∑ e ∈ 𝒮,
            (if ∀ i, slotProd t α Prod.fst i ∣ d i then (1 : ℝ) else 0)
              * (if ∀ i, slotProd t α Prod.snd i ∣ e i then (1 : ℝ) else 0)
              * s2Summand k R W y d e :=
        sum_move3S _ _ _ _
    _ = ∑ α ∈ assignments k t,
          ∑ d ∈ 𝒮.filter (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
            ∑ e ∈ 𝒮.filter (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
              s2Summand k R W y d e := by
        apply Finset.sum_congr rfl; intro α _
        symm
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.sum_filter]
        by_cases h1 : ∀ i, slotProd t α Prod.fst i ∣ d i
        · rw [if_pos h1]
          apply Finset.sum_congr rfl; intro e _
          by_cases h2 : ∀ i, slotProd t α Prod.snd i ∣ e i
          · rw [if_pos h2, if_pos h1, if_pos h2]; ring
          · rw [if_neg h2, if_neg h2]; ring
        · rw [if_neg h1]
          symm
          apply Finset.sum_eq_zero; intro e _
          rw [if_neg h1]; ring

/-- Collision moduli with a small prime factor contribute nothing to the
`m`-restricted guarded sum (every prime of a `cRad` exceeds `D₀ k`). -/
theorem inner_collision_zero_M (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    {t p : ℕ} (hp : p.Prime) (hpt : p ∣ t) (hpD : p ≤ D₀ k) :
    (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
        if t ∣ cRad d e then s2Summand k R (W k) y d e else 0) = 0 := by
  apply Finset.sum_eq_zero; intro d hd
  apply Finset.sum_eq_zero; intro e he
  have hd' := (Finset.mem_filter.mp hd).1
  rw [if_neg]
  intro hdvd
  have hpc : p ∣ cRad d e := hpt.trans hdvd
  obtain ⟨ij, _, h1, _⟩ := (prime_dvd_cRad_iff hp).mp hpc
  exact absurd (D₀_lt_of_prime_dvd_coord hd' hp h1) (not_lt.mpr hpD)

/-! ## The PORT-BLOCKER: the S₂ per-assignment absolute bound -/

/-- **PORT-BLOCKER (the S₂ inner absolute bound).** The `∏φ(lcm)` analog of
N4.4's `inner_abs_le`.  For a squarefree modulus `s` and any prime-to-slot
assignment `α`, the signed `u`-sum produced by `inner_exact_S2` at
`(σ,τ) = (slotProd fst, slotProd snd)` is bounded by
`3^{ω(s)}·∏_{p∣s}(p−1)⁻²·yside_g` — the per-prime `(p−1)⁻²`, `R`-free bound,
with the `m`-restricted `g`-weighted y-side `∑_{r:rₘ=1} y(r)²/∏g(rᵢ)`.

This is strictly narrower than the collision bound `s2_collision_lower_order`
(which is assembled on top of it via the Möbius/`euler_tail` structure).  The
S₁ proof (`inner_abs_le`) crucially used that the forced side collapses to the
**single** term `T_forced(v) = ∏μ(vᵢ)·y(v)/∏φ(vᵢ)`, so the φ-splitting +
prime-erasure injection applied to one `ŷ`-value.  Here the forced side is the
non-collapsing contraction `Vₘ(v) = lamPhiContractM v` (a full signed `d`-sum,
the S₂-vs-S₁ asymmetry), so that erasure argument does not port directly; the
required estimate is left as this precise `Prop`. -/
def S2InnerControlled (k R W : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) : Prop :=
  ∀ {s : ℕ}, Squarefree s → ∀ α ∈ assignments k s,
    |∑ u ∈ kSieveIndex k R W, (∏ i, (gMult (u i) : ℝ))
        * lamPhiContractM k R W m y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
        * lamPhiContractM k R W m y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))|
      ≤ 3 ^ s.primeFactors.card
          * (∏ p ∈ s.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
          * ∑ r ∈ (kSieveIndex k R W).filter (fun r => r m = 1),
              (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ)

/-! ## Assembly: the quantitative S₂ collision bound (on top of the PORT-BLOCKER) -/

/-- **The `∏φ(lcm)` analog of `collision_lower_order`.** Assembled on top of the
narrow `S2InnerControlled` atom: the `m`-restricted S₂ collision form is
controlled — genuinely SIGNED, via the Möbius expansion over collision moduli
and the `R`-free `euler_tail` (NOT a per-term `|lam·lam|` bound) — by
`(Cs·k²/D₀)·yside_g` with the explicit `Cs = 12` and the nonneg `g`-weighted
y-side `∑_{r:rₘ=1} y(r)²/∏g(rᵢ)`. -/
theorem s2_collision_lower_order (k R W' : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (f₀ : ℕ → ℝ)
    (_hf01 : ∀ n, 0 ≤ f₀ n ∧ f₀ n ≤ 1)
    (_hfmono : ∀ d m : ℕ, d ∣ m → 0 < d → f₀ m ≤ f₀ d)
    (hy : ∀ r, y r = if r ∈ kSieveIndex k R W' then ∏ i, f₀ (r i) else 0)
    (hW : W' = W k) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k)
    (hInner : S2InnerControlled k R W' m y) :
    |s2CollisionForm k R W' m y|
      ≤ (Cs * (k : ℝ) ^ 2 / (D₀ k : ℝ))
          * ∑ r ∈ (kSieveIndex k R W').filter (fun r => r m = 1),
              (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ) := by
  classical
  subst hW
  rw [show (Cs : ℝ) = 12 from rfl]
  set 𝒮 := (kSieveIndex k R (W k)).filter (fun d => d m = 1) with h𝒮
  -- the nonneg g-weighted y-side
  have hyside : 0 ≤ ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ) := by
    apply Finset.sum_nonneg; intro r _
    exact div_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _)
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
  have hDposN : 0 < D₀ k := by omega
  have hDpos : (0 : ℝ) < (D₀ k : ℝ) := by exact_mod_cast hDposN
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · subst hR0
    have hempty : kSieveIndex k 0 (W k) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro r hr
      exact absurd ((mem_kSieveIndex_iff r).mp hr).2.2.2 (Nat.not_lt_zero _)
    have hcoll0 : s2CollisionForm k 0 (W k) m y = 0 := by
      unfold s2CollisionForm
      rw [hempty]; simp
    rw [hcoll0, abs_zero]
    have hrhs : 0 ≤ 12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)
        * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ) := by positivity
    exact hrhs
  -- main case: `R ≥ 1`
  have h1mem : (1 : ℕ) ∈ collisionModuli k R := by
    rw [collisionModuli, Finset.mem_range]
    have := Nat.one_le_pow k R hRpos
    omega
  have hcompat := compat_moebius_expansion_M k R (W k) m y
  have herase := Finset.add_sum_erase (collisionModuli k R)
    (fun t => ((μ t : ℤ) : ℝ)
      * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
          (if t ∣ cRad d e then s2Summand k R (W k) y d e else 0)) h1mem
  have hG1 : (∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
      (if (1 : ℕ) ∣ cRad d e then s2Summand k R (W k) y d e else 0))
      = s2FullFormM k R (W k) m y := by
    unfold s2FullFormM
    rw [← h𝒮]
    apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro e _
    rw [if_pos (one_dvd _)]
  have hμ1 : ((μ 1 : ℤ) : ℝ) = 1 := by
    rw [ArithmeticFunction.moebius_apply_one]; norm_num
  -- `s2CollisionForm = − ∑_{t≠1} μ(t)·G_t`
  have hkey : s2CollisionForm k R (W k) m y
      = - ∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
              (if t ∣ cRad d e then s2Summand k R (W k) y d e else 0) := by
    have hcompat_eq := s2_compat_eq_M k R (W k) m y
    simp only [hμ1, one_mul, hG1] at herase
    -- herase : full + Σ_erase = Σ_CM ; hcompat : compat = Σ_CM
    have e1 : s2CompatFormM k R (W k) m y
        = s2FullFormM k R (W k) m y
          + ∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
              * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
                  (if t ∣ cRad d e then s2Summand k R (W k) y d e else 0) := by
      rw [hcompat, ← h𝒮, ← herase]
    rw [hcompat_eq] at e1
    linarith
  -- per-modulus bound
  have hbound : ∀ t ∈ (collisionModuli k R).erase 1,
      |((μ t : ℤ) : ℝ)
        * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
            (if t ∣ cRad d e then s2Summand k R (W k) y d e else 0)|
      ≤ (if Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p then
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
            * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ)
        else 0) := by
    intro t _
    by_cases hgood : Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p
    · rw [if_pos hgood]
      obtain ⟨hsq, _⟩ := hgood
      have hcard : (assignments k t).card
          = (k * k - k) ^ t.primeFactors.card := by
        rw [assignments, Finset.card_pi, Finset.prod_const,
          Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
      have hinvsq_nonneg : 0 ≤ ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 :=
        Finset.prod_nonneg fun p _ => sq_nonneg _
      have hGabs : |∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
          (if t ∣ cRad d e then s2Summand k R (W k) y d e else 0)|
          ≤ ((assignments k t).card : ℝ)
              * ((3 : ℝ) ^ t.primeFactors.card
                * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ)) := by
        have hICE := inner_collision_expand_M k R (W k) m y hsq
        rw [← h𝒮] at hICE
        rw [hICE]
        calc |∑ α ∈ assignments k t,
              ∑ d ∈ 𝒮.filter (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
                ∑ e ∈ 𝒮.filter (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
                  s2Summand k R (W k) y d e|
            ≤ ∑ α ∈ assignments k t,
                |∑ d ∈ 𝒮.filter (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
                  ∑ e ∈ 𝒮.filter (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
                    s2Summand k R (W k) y d e| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _α ∈ assignments k t,
                ((3 : ℝ) ^ t.primeFactors.card
                  * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                  * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ)) := by
              apply Finset.sum_le_sum
              intro α hα
              have hIE := inner_exact_S2 k R (W k) m y
                (slotProd t α Prod.fst) (slotProd t α Prod.snd)
              rw [← h𝒮] at hIE
              rw [hIE]
              exact hInner hsq α hα
          _ = ((assignments k t).card : ℝ)
                * ((3 : ℝ) ^ t.primeFactors.card
                  * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                  * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hcast : ((assignments k t).card : ℝ) * (3 : ℝ) ^ t.primeFactors.card
          ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card := by
        rw [hcard]
        push_cast
        rw [← mul_pow]
        apply pow_le_pow_left₀
        · positivity
        · have hle : ((k * k - k : ℕ) : ℝ) ≤ (k : ℝ) * (k : ℝ) := by
            have h1 : (k * k - k : ℕ) ≤ k * k := Nat.sub_le _ _
            calc ((k * k - k : ℕ) : ℝ) ≤ ((k * k : ℕ) : ℝ) := by exact_mod_cast h1
              _ = (k : ℝ) * (k : ℝ) := by push_cast; ring
          nlinarith
      calc |((μ t : ℤ) : ℝ)
            * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
                (if t ∣ cRad d e then s2Summand k R (W k) y d e else 0)|
          ≤ |∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
              (if t ∣ cRad d e then s2Summand k R (W k) y d e else 0)| := by
            rw [abs_mul]
            have h1 := abs_moebius_real_le_one t
            have h2 := abs_nonneg (∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
                (if t ∣ cRad d e then s2Summand k R (W k) y d e else 0))
            nlinarith
        _ ≤ ((assignments k t).card : ℝ)
              * ((3 : ℝ) ^ t.primeFactors.card
                * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ)) := hGabs
        _ ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
              * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
              * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ) := by
            have hrest : 0 ≤ (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ) :=
              mul_nonneg hinvsq_nonneg hyside
            calc ((assignments k t).card : ℝ)
                  * ((3 : ℝ) ^ t.primeFactors.card
                    * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                    * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ))
                = (((assignments k t).card : ℝ) * (3 : ℝ) ^ t.primeFactors.card)
                    * ((∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                      * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ)) := by ring
              _ ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
                    * ((∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                      * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ)) :=
                  mul_le_mul_of_nonneg_right hcast hrest
              _ = (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
                    * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                    * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ) := by ring
    · rw [if_neg hgood]
      by_cases hsq : Squarefree t
      · have hsmall : ∃ p ∈ t.primeFactors, ¬ D₀ k < p := by
          by_contra hall
          push Not at hall
          exact hgood ⟨hsq, hall⟩
        obtain ⟨p, hp, hple⟩ := hsmall
        have hzero := inner_collision_zero_M k R m y
          (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp) (not_lt.mp hple)
        rw [← h𝒮] at hzero
        rw [hzero, mul_zero, abs_zero]
      · have hμ0 : ((μ t : ℤ) : ℝ) = 0 := by
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; norm_num
        rw [hμ0, zero_mul, abs_zero]
  -- assemble via the Euler tail
  have htail := euler_tail k (R ^ k + 1) hk hD
  calc |s2CollisionForm k R (W k) m y|
      = |∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
              (if t ∣ cRad d e then s2Summand k R (W k) y d e else 0)| := by
        rw [hkey, abs_neg]
    _ ≤ ∑ t ∈ (collisionModuli k R).erase 1,
          |((μ t : ℤ) : ℝ)
            * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
                (if t ∣ cRad d e then s2Summand k R (W k) y d e else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ (collisionModuli k R).erase 1,
          (if Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p then
            (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
              * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
              * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ)
          else 0) :=
        Finset.sum_le_sum hbound
    _ = ∑ t ∈ (((collisionModuli k R).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p)).erase 1),
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
            * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ) := by
        rw [← Finset.sum_filter, Finset.filter_erase]
    _ = (∑ t ∈ (((collisionModuli k R).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p)).erase 1),
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
          * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ) := by
        rw [Finset.sum_mul]
    _ ≤ 12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)
          * ∑ r ∈ 𝒮, (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ) :=
        mul_le_mul_of_nonneg_right htail hyside

/-- **C4 corollary.** The compatible (count-weighted) S₂ main term dominates the
full `m`-restricted S₂ diagonal minus the controlled collision correction:
`s2CompatFormM ≥ s2FullFormM − (Cs·k²/D₀)·yside_g`.  Immediate from
`s2_compat_eq_M` and `s2_collision_lower_order` (`compat = full − collision`
and `collision ≤ |collision| ≤ (Cs·k²/D₀)·yside_g`). -/
theorem s2Compat_ge_full_sub (k R W' : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (f₀ : ℕ → ℝ)
    (hf01 : ∀ n, 0 ≤ f₀ n ∧ f₀ n ≤ 1)
    (hfmono : ∀ d m : ℕ, d ∣ m → 0 < d → f₀ m ≤ f₀ d)
    (hy : ∀ r, y r = if r ∈ kSieveIndex k R W' then ∏ i, f₀ (r i) else 0)
    (hW : W' = W k) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k)
    (hInner : S2InnerControlled k R W' m y) :
    s2CompatFormM k R W' m y
      ≥ s2FullFormM k R W' m y
        - (Cs * (k : ℝ) ^ 2 / (D₀ k : ℝ))
            * ∑ r ∈ (kSieveIndex k R W').filter (fun r => r m = 1),
                (y r) ^ 2 / ∏ i, (gMult (r i) : ℝ) := by
  have hcompat := s2_compat_eq_M k R W' m y
  have hcoll := s2_collision_lower_order k R W' m y f₀ hf01 hfmono hy hW hk hD hInner
  have hle := le_abs_self (s2CollisionForm k R W' m y)
  rw [hcompat]
  linarith

end Salt.Maynard
