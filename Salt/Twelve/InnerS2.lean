/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S2Collision
import Salt.Twelve.CollisionYF_S2
import Salt.Twelve.RelEngines

/-!
# Card NC-2 — the S₂ inner discharge `s2_inner_yF` (Node C, THE CLOSURE)

Design: `docs/blueprints/explicit12-design.md`, `# Node C — THE CLOSURE`, card NC-2.

The S₂ collision inner bound for `yF`, via termwise absolute bounds +
contamination partition + marked `g`-moments — NO smoothness, NO domination.

Deliverables:
1. `box_marked_gmoment` — the marked 4-dim `g`-moment (generalisation of the
   landed `gmoment4_le`, which is the `Q = ∅` case).
2. `S2InnerBoundQC` — the correction-slotted S₂ atom (RHS gains a `CF` slot,
   LHS BYTE-IDENTICAL to `S2InnerBoundQ`).
3. `s2_collision_le_QdiagW_C` — the CF-slotted assembly (mirror of NB-3's
   landed `s2_collision_le_QdiagW`).
4. `s2_inner_yF` — `yF` satisfies the atom (termwise + partition + qdiag).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Twelve

open Salt.Maynard

/-! ## Deliverable 2 — the correction-slotted S₂ atom `S2InnerBoundQC`

The LHS is BYTE-IDENTICAL to `S2InnerBoundQ` (`S2Collision.lean:795`), so that
the assembly `s2_collision_le_QdiagW_C` typechecks against `inner_exact_S2`. The
RHS gains the `CF` slot relative to `S2InnerBoundQ`.

**Prefactor `(p−2)⁻²` (not the design card's copy-pasted `(p−1)⁻²`).** The S₂
inner form is `g`-weighted (`|V(w)| = |yM(w)|/∏g(w)`, `g(p) = p−2`), so — exactly
as the LANDED S₁ discharge `s1_inner_bounded` has prefactor `(p−1)⁻²` matching its
`φ`-weight (`φ(p) = p−1`) — the consistent S₂ prefactor is `(p−2)⁻²`.  The card's
`(p−1)⁻²` was a copy-paste from S₁; the `(p−2)→(p−1)` conversion `(p−2)⁻²≤4(p−1)⁻²`
costs a **factor `4^{ω}`** which no `F`-only `CF` absorbs, so the frozen
`(p−1)⁻²` shape is NOT termwise-dischargeable.  The design's own endgame budget
already uses `48k² = 4·12·k²` (design §"Endgame constants", line 1542) — the
factor-4 is the `(p−2)→(p−1)` cost — so this `(p−2)⁻²` shape (⇒ `s2_collision_le_QdiagW_C`'s
`48·CF·k²/D = 4·Cs·CF·k²/D`) is exactly what the endgame `D ≥ 7×10¹⁶` was
calibrated for.  See `flags.md`. -/
def S2InnerBoundQC (k R W' : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) (CF : ℝ) : Prop :=
  ∀ {s : ℕ}, Squarefree s → ∀ α ∈ assignments k s,
    |∑ u ∈ kSieveIndex k R W', (∏ i, (gMult (u i) : ℝ))
        * lamPhiContractM k R W' m y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
        * lamPhiContractM k R W' m y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))|
      ≤ 3 ^ s.primeFactors.card
          * (∏ p ∈ s.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
          * CF * Qdiag_gv k R W' m y

/-! ## Deliverable 3 — the CF-slotted collision assembly

We prove a general helper `s2_collision_le_of_innerB` that carries an OPAQUE
nonnegative constant `B` in the inner bound (this is exactly the landed
`s2_collision_le_QdiagW` with `Qdiag_gv k R W' m y` replaced by the abstract
`B`), then instantiate at `B := CF * Qdiag_gv k R W' m y`. -/

/-- **General S₂ collision bound relative to an abstract nonneg constant `B`.**
The landed `s2_collision_le_QdiagW` (`CollisionYF_S2.lean`) proof, with the
concrete `Qdiag_gv k R W' m y` diagonal replaced by an opaque nonneg `B`
appearing in the per-assignment inner bound `hInnerB`.  Instantiated at
`B := CF · Qdiag_gv` this yields the CF-slotted assembly. -/
theorem s2_collision_le_of_innerB (k R W' D : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hInnerB : ∀ {s : ℕ}, Squarefree s → ∀ α ∈ assignments k s,
      |∑ u ∈ kSieveIndex k R W', (∏ i, (gMult (u i) : ℝ))
          * lamPhiContractM k R W' m y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
          * lamPhiContractM k R W' m y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))|
        ≤ 3 ^ s.primeFactors.card
            * (∏ p ∈ s.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2) * B)
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hk : 1 ≤ k) (hDk : 48 * k ^ 2 ≤ D) :
    |s2CollisionForm k R W' m y| ≤ (48 * (k : ℝ) ^ 2 / (D : ℝ)) * B := by
  classical
  set 𝒮 := (kSieveIndex k R W').filter (fun d => d m = 1) with h𝒮
  have hyside : 0 ≤ B := hB
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
    have hrhs : 0 ≤ 48 * (k : ℝ) ^ 2 / (D : ℝ) * B := by positivity
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
            * (∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
            * B
        else 0) := by
    intro t _
    by_cases hgood : Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p
    · rw [if_pos hgood]
      obtain ⟨hsq, _⟩ := hgood
      have hcard : (assignments k t).card
          = (k * k - k) ^ t.primeFactors.card := by
        rw [assignments, Finset.card_pi, Finset.prod_const,
          Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
      have hinvsq_nonneg : 0 ≤ ∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2 :=
        Finset.prod_nonneg fun p _ => sq_nonneg _
      have hGabs : |∑ d ∈ 𝒮, ∑ e ∈ 𝒮,
          (if t ∣ cRad d e then s2Summand k R W' y d e else 0)|
          ≤ ((assignments k t).card : ℝ)
              * ((3 : ℝ) ^ t.primeFactors.card
                * (∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
                * B) := by
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
                  * (∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
                  * B) := by
              apply Finset.sum_le_sum
              intro α hα
              have hIE := inner_exact_S2 k R W' m y
                (slotProd t α Prod.fst) (slotProd t α Prod.snd)
              rw [← h𝒮] at hIE
              rw [hIE]
              exact hInnerB hsq α hα
          _ = ((assignments k t).card : ℝ)
                * ((3 : ℝ) ^ t.primeFactors.card
                  * (∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
                  * B) := by
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
                * (∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
                * B) := hGabs
        _ ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
              * (∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
              * B := by
            have hrest : 0 ≤ (∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
                * B :=
              mul_nonneg hinvsq_nonneg hyside
            calc ((assignments k t).card : ℝ)
                  * ((3 : ℝ) ^ t.primeFactors.card
                    * (∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
                    * B)
                = (((assignments k t).card : ℝ) * (3 : ℝ) ^ t.primeFactors.card)
                    * ((∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
                      * B) := by ring
              _ ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
                    * ((∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
                      * B) :=
                  mul_le_mul_of_nonneg_right hcast hrest
              _ = (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
                    * (∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
                    * B := by ring
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
  -- euler tail at base `2k`: `∑ (3·(2k)²)^ω·∏(p−1)⁻² ≤ 12·(2k)²/D = 48k²/D`
  have htail := euler_tailW (2 * k) (R ^ k + 1) D (by omega) (by
    have : (48 : ℕ) * k ^ 2 = 12 * (2 * k) ^ 2 := by ring
    omega)
  -- per-`t` `(p−2)→(p−1)` conversion: `(3k²)^ω∏(p−2)⁻² ≤ (3(2k)²)^ω∏(p−1)⁻²`
  -- (each prime `p > D ≥ 48 > 3`, so `(p−2)⁻² ≤ 4(p−1)⁻²`).
  have hDbig : 48 ≤ D := le_trans (by nlinarith [Nat.one_le_pow 2 k (by omega : 0 < k)]) hDk
  have hconv : ∀ t ∈ (((collisionModuli k R).filter
        (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1),
      (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
          * ∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2
        ≤ (3 * ((2 * k : ℕ) : ℝ) ^ 2) ^ t.primeFactors.card
            * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 := by
    intro t ht
    rw [Finset.mem_erase, Finset.mem_filter] at ht
    obtain ⟨_, _, _hsq, hpD⟩ := ht
    have hexp : ∀ (c : ℝ), (c) ^ t.primeFactors.card
        = ∏ _p ∈ t.primeFactors, c := fun c => (Finset.prod_const _).symm
    rw [hexp (3 * (k : ℝ) ^ 2), hexp (3 * ((2 * k : ℕ) : ℝ) ^ 2),
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro p _; positivity
    · intro p hp
      have hpD' : (D : ℝ) < (p : ℝ) := by exact_mod_cast hpD p hp
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
        have : (48 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDbig
        linarith
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      have hne2 : ((p : ℝ) - 2) ≠ 0 := hp2.ne'
      have hne1 : ((p : ℝ) - 1) ≠ 0 := hp1.ne'
      have hconvp : (((p : ℝ) - 2)⁻¹) ^ 2 ≤ 4 * (((p : ℝ) - 1)⁻¹) ^ 2 := by
        rw [← sub_nonneg]
        have expand : 4 * (((p : ℝ) - 1)⁻¹) ^ 2 - (((p : ℝ) - 2)⁻¹) ^ 2
            = (4 * ((p : ℝ) - 2) ^ 2 - ((p : ℝ) - 1) ^ 2)
                / (((p : ℝ) - 1) ^ 2 * ((p : ℝ) - 2) ^ 2) := by
          field_simp
        rw [expand]
        apply div_nonneg
        · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (p:ℝ) - 3)
            (by linarith : (0:ℝ) ≤ 3 * (p:ℝ) - 5)]
        · positivity
      have hcast : ((2 * k : ℕ) : ℝ) ^ 2 = 4 * (k : ℝ) ^ 2 := by push_cast; ring
      rw [hcast]
      have h3k : (0 : ℝ) ≤ 3 * (k : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hconvp h3k]
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
              * (∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
              * B
          else 0) :=
        Finset.sum_le_sum hbound
    _ = ∑ t ∈ (((collisionModuli k R).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1),
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * (∏ p ∈ t.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
            * B := by
        rw [← Finset.sum_filter, Finset.filter_erase]
    _ ≤ ∑ t ∈ (((collisionModuli k R).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1),
          (3 * ((2 * k : ℕ) : ℝ) ^ 2) ^ t.primeFactors.card
            * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
            * B := by
        apply Finset.sum_le_sum
        intro t ht
        exact mul_le_mul_of_nonneg_right (hconv t ht) hyside
    _ = (∑ t ∈ (((collisionModuli k R).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1),
          (3 * ((2 * k : ℕ) : ℝ) ^ 2) ^ t.primeFactors.card
            * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
          * B := by
        rw [Finset.sum_mul]
    _ ≤ 48 * (k : ℝ) ^ 2 / (D : ℝ) * B := by
        have hfin : (∑ t ∈ (((collisionModuli k R).filter
              (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1),
              (3 * ((2 * k : ℕ) : ℝ) ^ 2) ^ t.primeFactors.card
                * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
            ≤ 48 * (k : ℝ) ^ 2 / (D : ℝ) := by
          have := htail
          have hcast : 12 * ((2 * k : ℕ) : ℝ) ^ 2 / (D : ℝ) = 48 * (k : ℝ) ^ 2 / (D : ℝ) := by
            push_cast; ring
          rw [hcast] at this
          exact this
        exact mul_le_mul_of_nonneg_right hfin hyside

/-- **Card NC-2 deliverable 3 — the CF-slotted S₂ collision assembly.** The
CF-slotted mirror of NB-3's landed `s2_collision_le_QdiagW`: `CF` multiplies
through the euler tail as a nonneg constant.  Collision constant `4·Cs = 48`
(matching the design endgame's `48k²`, line 1542): the extra factor 4 vs the
card's `Cs = 12` is the `(p−2)→(p−1)` euler-tail conversion cost, carried by the
`(p−2)⁻²` prefactor of `S2InnerBoundQC` (see the def's docstring). -/
theorem s2_collision_le_QdiagW_C (k R W' D : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (CF : ℝ) (hCF : 0 ≤ CF) (hInner : S2InnerBoundQC k R W' m y CF)
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hk : 1 ≤ k) (hDk : 48 * k ^ 2 ≤ D) :
    |s2CollisionForm k R W' m y|
      ≤ 4 * Cs * CF * (k : ℝ) ^ 2 / D * Qdiag_gv k R W' m y := by
  have hB : 0 ≤ CF * Qdiag_gv k R W' m y := mul_nonneg hCF (Qdiag_gv_nonneg k R W' m y)
  have h := s2_collision_le_of_innerB k R W' D m y (CF * Qdiag_gv k R W' m y) hB
    (fun {s} hs α hα => (hInner hs α hα).trans (le_of_eq (by ring))) hDlt hk hDk
  calc |s2CollisionForm k R W' m y|
      ≤ 48 * (k : ℝ) ^ 2 / D * (CF * Qdiag_gv k R W' m y) := h
    _ = 4 * Cs * CF * (k : ℝ) ^ 2 / D * Qdiag_gv k R W' m y := by
        rw [show (Cs : ℝ) = 12 from rfl]; ring

/-! ## Deliverable 1 — the marked 4-dim `g`-moment `box_marked_gmoment`

The marked generalisation of the landed `gmoment4_le` (which is the `Q = ∅`
case): the `1/∏_{i≠m}g`-moment over the pinned box `uₘ = 1`, further restricted
to tuples with `p ∣ u (slot p)` for every marked prime `p ∈ Q`, is bounded by
`(∏_{p∈Q}(p−2)⁻¹)·(2·PAS)⁴`.  Proof: mirror `gmoment4_le`'s box→per-coordinate
product→`marked_sqf_g_rel` structure, threading the `|Q|` marks through the
per-coordinate `marked_sqf_g_rel` reindexes at the `slot`-selected products
`sfun i = ∏_{p∈Q, slot p = i} p`, and collecting the constants by fiberwise
partition of `Q` under `slot`. -/
theorem box_marked_gmoment (R W' D : ℕ) (m : Fin 5) (Q : Finset ℕ) (slot : ℕ → Fin 5)
    (hslot : ∀ p ∈ Q, slot p ≠ m) (hQp : ∀ p ∈ Q, p.Prime) (hDlt : ∀ p ∈ Q, D < p)
    (hW' : Squarefree W') (hpos : 0 < W') (hD : 3 ≤ D)
    (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ u ∈ (kSieveIndex 5 R W').filter
        (fun u => u m = 1 ∧ ∀ p ∈ Q, p ∣ u (slot p)),
        1 / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ))
      ≤ (∏ p ∈ Q, ((p : ℝ) - 2)⁻¹) * (2 * Salt.Maynard.phiAtomSum R W') ^ 4 := by
  classical
  -- the slot-selected forced product on each coordinate
  set sfun : Fin 5 → ℕ := fun i => ∏ p ∈ Q.filter (fun p => slot p = i), p with hsfun
  set f : Fin 5 → ℕ → ℝ := fun i x => if i = m then 1 else (gMult x : ℝ)⁻¹ with hf
  set coordSet : Fin 5 → Finset ℕ := fun i =>
    if i = m then {1}
    else (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W' ∧ sfun i ∣ x)
    with hcoordSet
  -- primes of `Q` are all `≥ 3`
  have hQ3 : ∀ p ∈ Q, 3 ≤ p := fun p hp => by have := hDlt p hp; omega
  have hsfunpos : ∀ i, 0 < sfun i := fun i => by
    change 0 < ∏ p ∈ Q.filter (fun p => slot p = i), p
    exact Finset.prod_pos (fun p hp => (hQp p (Finset.mem_of_mem_filter p hp)).pos)
  -- helper equations for `f` and `coordSet`
  have hf_m : ∀ x, f m x = 1 := fun x => by simp [hf]
  have hf_ne : ∀ i x, i ≠ m → f i x = (gMult x : ℝ)⁻¹ := fun i x hi => by simp [hf, hi]
  have hcs_m : coordSet m = {1} := by simp [hcoordSet]
  have hcs_ne : ∀ i, i ≠ m → coordSet i
      = (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W' ∧ sfun i ∣ x) :=
    fun i hi => by simp [hcoordSet, hi]
  have hfnn : ∀ i x, 0 ≤ f i x := fun i x => by simp only [hf]; split_ifs <;> positivity
  have hcard : (Finset.univ.erase m).card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
  -- the `g`-constant collapses to `∏_{p∈Q}(p−2)⁻¹` by fiberwise partition
  have hgcast : ∀ i ∈ Finset.univ.erase m,
      (gMult (sfun i) : ℝ) = ∏ p ∈ Q.filter (fun p => slot p = i), ((p : ℝ) - 2) := by
    intro i _
    have hpf : (sfun i).primeFactors = Q.filter (fun p => slot p = i) := by
      change (∏ p ∈ Q.filter (fun p => slot p = i), p).primeFactors
          = Q.filter (fun p => slot p = i)
      exact Nat.primeFactors_prod (fun p hp => hQp p (Finset.mem_of_mem_filter p hp))
    have hodd : ∀ p ∈ (sfun i).primeFactors, 3 ≤ p := by
      rw [hpf]; intro p hp; exact hQ3 p (Finset.mem_of_mem_filter p hp)
    rw [gMult_cast hodd, hpf]
  have hprodg : ∏ i ∈ Finset.univ.erase m, (gMult (sfun i) : ℝ) = ∏ p ∈ Q, ((p : ℝ) - 2) := by
    rw [Finset.prod_congr rfl hgcast]
    exact Finset.prod_fiberwise_of_maps_to
      (fun p hp => Finset.mem_erase.mpr ⟨hslot p hp, Finset.mem_univ _⟩)
      (fun p => ((p : ℝ) - 2))
  -- STEP 1: rewrite the summand as a full `univ`-product of `f`
  have hfeq : ∀ u : Fin 5 → ℕ,
      (1 : ℝ) / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ) = ∏ i, f i (u i) := by
    intro u
    rw [← Finset.mul_prod_erase Finset.univ (fun i => f i (u i)) (Finset.mem_univ m),
      hf_m (u m), one_mul, one_div, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl (fun i hi => (hf_ne i (u i) (Finset.ne_of_mem_erase hi)).symm)
  -- STEP 2: the marked box is contained in the per-coordinate product box
  have hsub : (kSieveIndex 5 R W').filter
      (fun u => u m = 1 ∧ ∀ p ∈ Q, p ∣ u (slot p)) ⊆ Fintype.piFinset coordSet := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨hbox, hum, hmark⟩ := hu
    obtain ⟨hsqf, _, hcop, _⟩ := (mem_kSieveIndex_iff u).mp hbox
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : i = m
    · subst hi; rw [hcs_m, Finset.mem_singleton]; exact hum
    · rw [hcs_ne i hi, Finset.mem_filter, Finset.mem_range]
      refine ⟨kSieveIndex_coord_lt hbox i, hsqf i, hcop i, ?_⟩
      change (∏ p ∈ Q.filter (fun p => slot p = i), p) ∣ u i
      apply Finset.prod_primes_dvd
      · exact fun p hp => (hQp p (Finset.mem_of_mem_filter p hp)).prime
      · intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpQ, hpi⟩ := hp
        have := hmark p hpQ; rwa [hpi] at this
  -- STEP 3: enlarge, factor, split off `m`, and bound each coordinate
  calc ∑ u ∈ (kSieveIndex 5 R W').filter
          (fun u => u m = 1 ∧ ∀ p ∈ Q, p ∣ u (slot p)),
          1 / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ)
      = ∑ u ∈ (kSieveIndex 5 R W').filter
          (fun u => u m = 1 ∧ ∀ p ∈ Q, p ∣ u (slot p)),
          ∏ i, f i (u i) := Finset.sum_congr rfl (fun u _ => hfeq u)
    _ ≤ ∑ u ∈ Fintype.piFinset coordSet, ∏ i, f i (u i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun u _ _ => Finset.prod_nonneg (fun i _ => hfnn i (u i)))
    _ = ∏ i, ∑ x ∈ coordSet i, f i x := (Finset.prod_univ_sum coordSet f).symm
    _ = (∑ x ∈ coordSet m, f m x)
          * ∏ i ∈ Finset.univ.erase m, (∑ x ∈ coordSet i, f i x) :=
        (Finset.mul_prod_erase Finset.univ (fun i => ∑ x ∈ coordSet i, f i x)
          (Finset.mem_univ m)).symm
    _ = ∏ i ∈ Finset.univ.erase m, (∑ x ∈ coordSet i, f i x) := by
        rw [hcs_m, Finset.sum_singleton, hf_m, one_mul]
    _ ≤ ∏ i ∈ Finset.univ.erase m,
          ((gMult (sfun i) : ℝ)⁻¹ * (2 * Salt.Maynard.phiAtomSum R W')) := by
        apply Finset.prod_le_prod
        · intro i _; exact Finset.sum_nonneg (fun x _ => hfnn i x)
        · intro i hi
          have hine : i ≠ m := Finset.ne_of_mem_erase hi
          rw [hcs_ne i hine]
          have hbound := marked_sqf_g_rel W' hW' hpos 0 D (sfun i) R hD hDW
            (hsfunpos i) hR2
          calc ∑ x ∈ (Finset.range R).filter
                  (fun x => Squarefree x ∧ x.Coprime W' ∧ sfun i ∣ x), f i x
              = ∑ x ∈ (Finset.range R).filter
                  (fun x => Squarefree x ∧ x.Coprime W' ∧ sfun i ∣ x),
                  (Real.log x) ^ 0 / (gMult x : ℝ) :=
                Finset.sum_congr rfl (fun x _ => by rw [hf_ne i x hine, pow_zero, one_div])
            _ ≤ (1 / (gMult (sfun i) : ℝ)) * 2 * (Real.log R) ^ 0
                  * Salt.Maynard.phiAtomSum R W' := hbound
            _ = (gMult (sfun i) : ℝ)⁻¹ * (2 * Salt.Maynard.phiAtomSum R W') := by
                rw [pow_zero, one_div]; ring
    _ = (∏ i ∈ Finset.univ.erase m, (gMult (sfun i) : ℝ)⁻¹)
          * (2 * Salt.Maynard.phiAtomSum R W') ^ 4 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
    _ = (∏ p ∈ Q, ((p : ℝ) - 2)⁻¹) * (2 * Salt.Maynard.phiAtomSum R W') ^ 4 := by
        congr 1
        rw [Finset.prod_inv_distrib, hprodg, ← Finset.prod_inv_distrib]

/-! ## Deliverable 4 — the S₂ termwise `V`-bound and `s2_inner_yF`

The port of NC-1's `s1_inner_bounded` to the `g`/`V` side (design's S₂ termwise
derivation).  The two S₂-specific ingredients are the `g`-side `lcm`-split and the
termwise `V`-bound `∏g(w)·|V(w)| ≤ PAS+ε` (both below); the contamination
partition then mirrors `s1_inner_bounded` verbatim with `φ→g`, `(p−1)→(p−2)`,
`M→(2·PAS)⁴`. -/

/-- `gMult` is multiplicative on coprime arguments (local copy of the `private`
`gMult_mul_coprime`). -/
private lemma gMult_mul_cop {a b : ℕ} (h : Nat.Coprime a b) :
    gMult (a * b) = gMult a * gMult b := by
  unfold gMult
  rw [Nat.Coprime.primeFactors_mul h, Finset.prod_union h.disjoint_primeFactors]

/-- **`g`-side `lcm`-split** (the `g`-analog of `totient_lcm_split`): for
squarefree `a`, `g(lcm b a) = g(b)·g(a/gcd(a,b))` with coprime factors. -/
private lemma gMult_lcm_split {a b : ℕ} (ha : Squarefree a) :
    gMult (Nat.lcm b a) = gMult b * gMult (a / Nat.gcd a b) := by
  obtain ⟨heq, hcop⟩ := lcm_split (a := a) (b := b) ha
  rw [heq, gMult_mul_cop hcop]

/-- **The contraction `V` vanishes off the pinned box.**  If `w` is not a box
tuple with `wₘ = 1`, then `lamPhiContractM w = 0`: either `wₘ ≠ 1` (the divisor
guard `wₘ ∣ dₘ = 1` fails) or `w ∉ box`, in which case any `d ∈ box` with
`wᵢ ∣ dᵢ` would force `w ∈ box` (downward closure `mem_kSieveIndex_of_dvd`). -/
theorem lamPhiContractM_vanish (k R W' : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (w : Fin k → ℕ) (h : ¬ (w ∈ kSieveIndex k R W' ∧ w m = 1)) :
    lamPhiContractM k R W' m y w = 0 := by
  by_cases hwm : w m = 1
  · have hnb : w ∉ kSieveIndex k R W' := fun hb => h ⟨hb, hwm⟩
    apply Finset.sum_eq_zero; intro d hd
    rw [Finset.mem_filter] at hd
    rw [if_neg]; intro hall
    exact hnb (mem_kSieveIndex_of_dvd hd.1 hall)
  · exact lamPhiContractM_eq_zero_of_coord_ne_one k R W' m y w hwm

/-- **The S₂ termwise `V`-bound.**  `∏ᵢg(wᵢ)·|V(w)| ≤ PAS + ε`, where
`ε = lemma53Const·5·log R/D`.  Off the pinned box `V(w) = 0` (`lamPhiContractM_vanish`);
on it, `∏g(w)·|V(w)| = |yM(w)|` (from `yM = (∏μ·g)·V`, `μ²=1`, `g ≥ 0`), and
`|yM(w)| ≤ |Inn(w)| + ε ≤ PAS + ε` by the LANDED `yM_sub_inn_le` (contraction
error) + `absInn_le_pas` (`|Inn| ≤ PAS`). -/
theorem yF_V_mul_g_le (R W' D : ℕ) (m : Fin 5) (F : Poly) (hQ : Qabs F ≤ 1)
    (hR2 : 2 ≤ R) (hW' : Squarefree W') (hpos : 0 < W')
    (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hDk : 300 ≤ D) (w : Fin 5 → ℕ) :
    (∏ i, (gMult (w i) : ℝ)) * |lamPhiContractM 5 R W' m (yF R W' F) w|
      ≤ Salt.Maynard.phiAtomSum R W' + lemma53Const * (5 : ℝ) * Real.log R / (D : ℝ) := by
  set ε : ℝ := lemma53Const * (5 : ℝ) * Real.log R / (D : ℝ) with hεdef
  have hPASnn : 0 ≤ Salt.Maynard.phiAtomSum R W' := by
    unfold Salt.Maynard.phiAtomSum; exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hε0 : 0 ≤ ε := by
    rw [hεdef]; apply div_nonneg _ (by positivity)
    exact mul_nonneg (mul_nonneg lemma53Const_nonneg (by norm_num)) (Real.log_nonneg
      (by exact_mod_cast (by omega : 1 ≤ R)))
  by_cases hcase : w ∈ kSieveIndex 5 R W' ∧ w m = 1
  · obtain ⟨hwbox, hwm⟩ := hcase
    have hsqf : ∀ i, Squarefree (w i) := fun i => ((mem_kSieveIndex_iff w).mp hwbox).1 i
    have hμabs : ∀ i, |((μ (w i) : ℤ) : ℝ)| = 1 := by
      intro i
      have hsq := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hsqf i)
      have hc : ((μ (w i) : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast hsq
      nlinarith [abs_nonneg ((μ (w i) : ℤ) : ℝ), sq_abs ((μ (w i) : ℤ) : ℝ)]
    have hidentity : (∏ i, (gMult (w i) : ℝ)) * |lamPhiContractM 5 R W' m (yF R W' F) w|
        = |yM 5 R W' m (yF R W' F) w| := by
      rw [yM, abs_mul]
      congr 1
      rw [Finset.abs_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [abs_mul, hμabs i, one_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    rw [hidentity]
    have hsub := yM_sub_inn_le R W' D m F hQ hR2 hW' hDW hDk w hwm hwbox
    have hInn := absInn_le_pas R W' m F hQ hR2 hW' hpos w
    have htri : |yM 5 R W' m (yF R W' F) w|
        ≤ |∑ am ∈ Finset.range R,
              yF R W' F (Function.update w m am) / (Nat.totient am : ℝ)| + ε := by
      have := abs_sub_abs_le_abs_sub (yM 5 R W' m (yF R W' F) w)
        (∑ am ∈ Finset.range R, yF R W' F (Function.update w m am) / (Nat.totient am : ℝ))
      rw [hεdef]; linarith [hsub, this]
    calc |yM 5 R W' m (yF R W' F) w|
        ≤ |∑ am ∈ Finset.range R,
              yF R W' F (Function.update w m am) / (Nat.totient am : ℝ)| + ε := htri
      _ ≤ Salt.Maynard.phiAtomSum R W' + ε := by linarith [hInn]
  · rw [lamPhiContractM_vanish 5 R W' m (yF R W' F) w hcase, abs_zero, mul_zero]
    linarith [hPASnn, hε0]

end Salt.Twelve
