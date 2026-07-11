/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S2Collision
import Salt.Twelve.QdiagBridge

/-!
# Card NB-3 — the S₂-side collision twin `collision_yF_le_S2`

Design: `docs/blueprints/explicit12-design.md`, card NB-3.  The S₂-side analog of
NB-1's `collision_yF_le`.  It connects `S2mW_lower`'s compat-pairs bound to
`qdiag_bridge`'s sharp `Qdiag`, by bounding the S₂ collision residual
`Qdiag_mW − s2CompatFormM = s2CollisionForm` (the exact identity — see below).

## The identity making the LHS the collision form

`Qdiag_mW` (`S2Eh.lean`) is *definitionally* the `dₘ=eₘ=1`-restricted S₂
diagonal `s2FullFormM` (`S2Collision.lean`): both are
`∑_{dₘ=eₘ=1} lam·lam/∏φ(lcm)`.  And `s2CompatFormM = s2FullFormM − s2CollisionForm`
(`s2_compat_eq_M`).  Hence

  `Qdiag_mW − s2CompatFormM = s2FullFormM − s2CompatFormM = s2CollisionForm`,

so the deliverable's LHS is exactly `|s2CollisionForm|`, and the natural RHS is
the S₂ diagonal itself — `Qdiag_gv = s2FullFormM = Qdiag_mW` (`s2FullFormM_eq_Qdiag`).
The bound is therefore **`Qdiag`-relative**, not `M`-relative; NB-4 converts it
via `qdiag_bridge` (which already evaluates `Qdiag_mW ≈ X⁶·Jcal`).

## Route

The landed collision bound `s2_collision_le_Qdiag` (`S2Collision.lean:808`) is
pinned to `W' = W k` and `D₀ k` (via `subst hW` + `euler_tail`), and carries a
vestigial tensor hypothesis `(f₀, hy, …)` that its proof never uses.  Every
*structural* piece it relies on — `compat_moebius_expansion_M`,
`inner_collision_expand_M`, `inner_exact_S2`, `s2_diag_lam_restricted` — is
already free-`W`.  So the free-`(D,W')` mirror `s2_collision_le_QdiagW` below is
the landed proof with three swaps: (i) drop `subst hW` (keep `W'`), (ii) replace
the `W k`-pinned zero lemma `inner_collision_zero_M` by the free-`(D,W')`
`inner_collision_zero_MW`, (iii) replace `euler_tail` by the free-`D`
`euler_tailW`.  Both stay conditional on the abstract atom `S2InnerBoundQ` — the
`(p−1)⁻²`/`Qdiag_gv` per-assignment inner bound, exactly as the landed one is.

## Status of the `S2InnerBoundQ (yF)` discharge

`S2InnerBoundQ` bounds a **signed, non-collapsing** quadratic form in `y`
(`∑_u ∏g·V(u∨σ)·V(u∨τ)`, `V = lamPhiContractM y`) by `const·Qdiag_gv[y]` (also
quadratic in `y`).  Unlike the S₁ side (`S1InnerBound`), whose forced sum
collapses to a single term and is therefore monotone in `|y|`, the S₂ form does
NOT collapse (the documented `PORT-BLOCKER` in `S2Collision.lean`), so the naive
"monotone in `|y|`" domination by `ONE` is unavailable — the genuine discharge is
a weighted Cauchy–Schwarz shift bound `∑_u ∏g·V(u∨σ)² ≤ ∏_{p|σ}(…)·Qdiag_gv`,
the rung's open analytic question (design §"open design questions (c)").  This
node therefore lands the full free-`(D,W')` infrastructure and isolates
`S2InnerBoundQ (yF R W' F)` as the single remaining hypothesis (mirroring the
codebase's conditional-atom architecture: `S1InnerBound`, `S2InnerControlled`,
`PhiUpperAtom`, `WindowPNT`, `EHall`).  See `flags.md` FABLE-QUEUE.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Twelve

open Salt.Maynard

/-- **Free-`(D,W')` S₂ collision-zero lemma.**  The `m`-restricted analog of
`inner_collision_zeroW` (S₁, free-`(D,W')`): a collision modulus `t` with a prime
factor `p ≤ D` forces the constrained `s2Summand` double sum to vanish, because
every coordinate of a sieve tuple in `kSieveIndex k R W'` is `>D` on its prime
factors (via `D_lt_of_prime_dvd_coordW`).  This is the one free-`(D,W')`
replacement for the `W k`-pinned `inner_collision_zero_M`; the other structural
pieces of the S₂ collision assembly are already free-`W`. -/
theorem inner_collision_zero_MW (k R W' D : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p)
    {t p : ℕ} (hp : p.Prime) (hpt : p ∣ t) (hpD : p ≤ D) :
    (∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
        if t ∣ cRad d e then s2Summand k R W' y d e else 0) = 0 := by
  apply Finset.sum_eq_zero; intro d hd
  apply Finset.sum_eq_zero; intro e he
  have hd' := (Finset.mem_filter.mp hd).1
  rw [if_neg]
  intro hdvd
  have hpc : p ∣ cRad d e := hpt.trans hdvd
  obtain ⟨ij, _, h1, _⟩ := (prime_dvd_cRad_iff hp).mp hpc
  exact absurd (D_lt_of_prime_dvd_coordW hDlt hd' hp h1) (not_lt.mpr hpD)

/-- **Free-`(D,W')` S₂ collision bound (conditional on `S2InnerBoundQ`).**  The
mirror of the landed `s2_collision_le_Qdiag` (`S2Collision.lean:808`) with `W k → W'`
and `D₀ k → D`: the `m`-restricted S₂ collision form is controlled by the S₂
diagonal `Qdiag_gv` up to `Cs·k²/D`.  The proof is the landed one with the three
swaps documented in the module header (no `subst hW`; `inner_collision_zero_MW`;
`euler_tailW`); the vestigial tensor hypotheses `(f₀, hy, …)` are dropped. -/
theorem s2_collision_le_QdiagW (k R W' D : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hk : 1 ≤ k) (hDk : 12 * k ^ 2 ≤ D)
    (hInner : S2InnerBoundQ k R W' m y) :
    |s2CollisionForm k R W' m y|
      ≤ (Cs * (k : ℝ) ^ 2 / (D : ℝ)) * Qdiag_gv k R W' m y := by
  classical
  rw [show (Cs : ℝ) = 12 from rfl]
  set 𝒮 := (kSieveIndex k R W').filter (fun d => d m = 1) with h𝒮
  have hyside : 0 ≤ Qdiag_gv k R W' m y := Qdiag_gv_nonneg k R W' m y
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
  have hDposN : 0 < D := by omega
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDposN
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · subst hR0
    have hempty : kSieveIndex k 0 W' = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro r hr
      exact absurd ((mem_kSieveIndex_iff r).mp hr).2.2.2 (Nat.not_lt_zero _)
    have hcoll0 : s2CollisionForm k 0 W' m y = 0 := by
      unfold s2CollisionForm
      rw [hempty]; simp
    rw [hcoll0, abs_zero]
    have hrhs : 0 ≤ 12 * (k : ℝ) ^ 2 / (D : ℝ) * Qdiag_gv k 0 W' m y := by
      have := Qdiag_gv_nonneg k 0 W' m y; positivity
    exact hrhs
  have h1mem : (1 : ℕ) ∈ collisionModuli k R := by
    rw [collisionModuli, Finset.mem_range]
    have := Nat.one_le_pow k R hRpos
    omega
  have hcompat := compat_moebius_expansion_M k R W' m y
  have herase := Finset.add_sum_erase (collisionModuli k R)
    (fun t => ((μ t : ℤ) : ℝ)
      * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
          (if t ∣ cRad d e then s2Summand k R W' y d e else 0)) h1mem
  have hG1 : (∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
      (if (1 : ℕ) ∣ cRad d e then s2Summand k R W' y d e else 0))
      = s2FullFormM k R W' m y := by
    unfold s2FullFormM
    rw [← h𝒮]
    apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro e _
    rw [if_pos (one_dvd _)]
  have hμ1 : ((μ 1 : ℤ) : ℝ) = 1 := by
    rw [ArithmeticFunction.moebius_apply_one]; norm_num
  have hkey : s2CollisionForm k R W' m y
      = - ∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
              (if t ∣ cRad d e then s2Summand k R W' y d e else 0) := by
    have hcompat_eq := s2_compat_eq_M k R W' m y
    simp only [hμ1, one_mul, hG1] at herase
    have e1 : s2CompatFormM k R W' m y
        = s2FullFormM k R W' m y
          + ∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
              * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
                  (if t ∣ cRad d e then s2Summand k R W' y d e else 0) := by
      rw [hcompat, ← h𝒮, ← herase]
    rw [hcompat_eq] at e1
    linarith
  have hbound : ∀ t ∈ (collisionModuli k R).erase 1,
      |((μ t : ℤ) : ℝ)
        * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
            (if t ∣ cRad d e then s2Summand k R W' y d e else 0)|
      ≤ (if Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p then
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
            * Qdiag_gv k R W' m y
        else 0) := by
    intro t _
    by_cases hgood : Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p
    · rw [if_pos hgood]
      obtain ⟨hsq, _⟩ := hgood
      have hcard : (assignments k t).card
          = (k * k - k) ^ t.primeFactors.card := by
        rw [assignments, Finset.card_pi, Finset.prod_const,
          Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
      have hinvsq_nonneg : 0 ≤ ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 :=
        Finset.prod_nonneg fun p _ => sq_nonneg _
      have hGabs : |∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
          (if t ∣ cRad d e then s2Summand k R W' y d e else 0)|
          ≤ ((assignments k t).card : ℝ)
              * ((3 : ℝ) ^ t.primeFactors.card
                * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * Qdiag_gv k R W' m y) := by
        have hICE := inner_collision_expand_M k R W' m y hsq
        rw [← h𝒮] at hICE
        rw [hICE]
        calc |∑ α ∈ assignments k t,
              ∑ d ∈ 𝒮.filter (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
                ∑ e ∈ 𝒮.filter (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
                  s2Summand k R W' y d e|
            ≤ ∑ α ∈ assignments k t,
                |∑ d ∈ 𝒮.filter (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
                  ∑ e ∈ 𝒮.filter (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
                    s2Summand k R W' y d e| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _α ∈ assignments k t,
                ((3 : ℝ) ^ t.primeFactors.card
                  * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                  * Qdiag_gv k R W' m y) := by
              apply Finset.sum_le_sum
              intro α hα
              have hIE := inner_exact_S2 k R W' m y
                (slotProd t α Prod.fst) (slotProd t α Prod.snd)
              rw [← h𝒮] at hIE
              rw [hIE]
              exact hInner hsq α hα
          _ = ((assignments k t).card : ℝ)
                * ((3 : ℝ) ^ t.primeFactors.card
                  * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                  * Qdiag_gv k R W' m y) := by
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
                (if t ∣ cRad d e then s2Summand k R W' y d e else 0)|
          ≤ |∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
              (if t ∣ cRad d e then s2Summand k R W' y d e else 0)| := by
            rw [abs_mul]
            have h1 := abs_moebius_real_le_one t
            have h2 := abs_nonneg (∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
                (if t ∣ cRad d e then s2Summand k R W' y d e else 0))
            nlinarith
        _ ≤ ((assignments k t).card : ℝ)
              * ((3 : ℝ) ^ t.primeFactors.card
                * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * Qdiag_gv k R W' m y) := hGabs
        _ ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
              * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
              * Qdiag_gv k R W' m y := by
            have hrest : 0 ≤ (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * Qdiag_gv k R W' m y :=
              mul_nonneg hinvsq_nonneg hyside
            calc ((assignments k t).card : ℝ)
                  * ((3 : ℝ) ^ t.primeFactors.card
                    * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                    * Qdiag_gv k R W' m y)
                = (((assignments k t).card : ℝ) * (3 : ℝ) ^ t.primeFactors.card)
                    * ((∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                      * Qdiag_gv k R W' m y) := by ring
              _ ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
                    * ((∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                      * Qdiag_gv k R W' m y) :=
                  mul_le_mul_of_nonneg_right hcast hrest
              _ = (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
                    * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                    * Qdiag_gv k R W' m y := by ring
    · rw [if_neg hgood]
      by_cases hsq : Squarefree t
      · have hsmall : ∃ p ∈ t.primeFactors, ¬ D < p := by
          by_contra hall
          push Not at hall
          exact hgood ⟨hsq, hall⟩
        obtain ⟨p, hp, hple⟩ := hsmall
        have hzero := inner_collision_zero_MW k R W' D m y hDlt
          (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp) (not_lt.mp hple)
        rw [← h𝒮] at hzero
        rw [hzero, mul_zero, abs_zero]
      · have hμ0 : ((μ t : ℤ) : ℝ) = 0 := by
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; norm_num
        rw [hμ0, zero_mul, abs_zero]
  have htail := euler_tailW k (R ^ k + 1) D hk hDk
  calc |s2CollisionForm k R W' m y|
      = |∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
              (if t ∣ cRad d e then s2Summand k R W' y d e else 0)| := by
        rw [hkey, abs_neg]
    _ ≤ ∑ t ∈ (collisionModuli k R).erase 1,
          |((μ t : ℤ) : ℝ)
            * ∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
                (if t ∣ cRad d e then s2Summand k R W' y d e else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ (collisionModuli k R).erase 1,
          (if Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p then
            (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
              * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
              * Qdiag_gv k R W' m y
          else 0) :=
        Finset.sum_le_sum hbound
    _ = ∑ t ∈ (((collisionModuli k R).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1),
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
            * Qdiag_gv k R W' m y := by
        rw [← Finset.sum_filter, Finset.filter_erase]
    _ = (∑ t ∈ (((collisionModuli k R).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1),
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
          * Qdiag_gv k R W' m y := by
        rw [Finset.sum_mul]
    _ ≤ 12 * (k : ℝ) ^ 2 / (D : ℝ) * Qdiag_gv k R W' m y :=
        mul_le_mul_of_nonneg_right htail hyside

/-- `Qdiag_mW` is definitionally the `dₘ=eₘ=1`-restricted S₂ diagonal
`s2FullFormM`: both unfold to `∑_{dₘ=eₘ=1} lam·lam/∏φ(lcm)`. -/
theorem Qdiag_mW_eq_s2FullFormM (k R W' : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) :
    Qdiag_mW k R W' m y = s2FullFormM k R W' m y := by
  rfl

/-- **Card NB-3 — the S₂-side collision twin (conditional on `S2InnerBoundQ (yF)`).**
The S₂ analog of NB-1's `collision_yF_le`.  The gap between the sharp S₂ diagonal
`Qdiag_mW` (`= X⁶·Jcal` via `qdiag_bridge`) and the count-weighted compatible
form `s2CompatFormM` is exactly the collision form `s2CollisionForm`
(`Qdiag_mW − s2CompatFormM = s2CollisionForm`), bounded by `Cs·k²/D` times the S₂
diagonal itself.  This is the `Qdiag`-relative form (NB-4 converts via
`qdiag_bridge`, not `yside_ge_cM`; see the module header).

The discharge of `S2InnerBoundQ (yF R W' F)` — the signed non-collapsing S₂ inner
bound, the rung's open Cauchy–Schwarz shift estimate — remains a hypothesis (see
`flags.md` FABLE-QUEUE); the full free-`(D,W')` collision infrastructure is landed
above unconditionally. -/
theorem collision_yF_le_S2 (R W' D : ℕ) (F : Poly) (m : Fin 5) (_hQ : Qabs F ≤ 1)
    (_hW' : Squarefree W') (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p)
    (hDk : 12 * 5 ^ 2 ≤ D)
    (hInner : S2InnerBoundQ 5 R W' m (yF R W' F)) :
    |Qdiag_mW 5 R W' m (yF R W' F) - s2CompatFormM 5 R W' m (yF R W' F)|
      ≤ (Cs * (5 : ℝ) ^ 2 / (D : ℝ)) * Qdiag_mW 5 R W' m (yF R W' F) := by
  have hfull : Qdiag_mW 5 R W' m (yF R W' F) = s2FullFormM 5 R W' m (yF R W' F) :=
    Qdiag_mW_eq_s2FullFormM 5 R W' m (yF R W' F)
  have hgv : s2FullFormM 5 R W' m (yF R W' F) = Qdiag_gv 5 R W' m (yF R W' F) :=
    s2FullFormM_eq_Qdiag 5 R W' m (yF R W' F)
  have hcompat : s2CompatFormM 5 R W' m (yF R W' F)
      = s2FullFormM 5 R W' m (yF R W' F) - s2CollisionForm 5 R W' m (yF R W' F) :=
    s2_compat_eq_M 5 R W' m (yF R W' F)
  have hcoll := s2_collision_le_QdiagW 5 R W' D m (yF R W' F) hDlt (by norm_num) hDk hInner
  -- LHS: Qdiag_mW − s2CompatFormM = s2CollisionForm ; RHS: Qdiag_mW = Qdiag_gv
  have hdiff : Qdiag_mW 5 R W' m (yF R W' F) - s2CompatFormM 5 R W' m (yF R W' F)
      = s2CollisionForm 5 R W' m (yF R W' F) := by rw [hcompat, hfull]; ring
  have hQeq : Qdiag_mW 5 R W' m (yF R W' F) = Qdiag_gv 5 R W' m (yF R W' F) := hfull.trans hgv
  rw [hdiff, hQeq]
  -- reconcile the numeral cast `((5:ℕ):ℝ) = (5:ℝ)`
  have hc : (Cs * (5 : ℝ) ^ 2 / (D : ℝ)) = (Cs * ((5 : ℕ) : ℝ) ^ 2 / (D : ℝ)) := by
    norm_num
  rw [hc]
  exact hcoll

end Salt.Twelve
