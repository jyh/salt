/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RamareMR
import Salt.MR.RamareP2End
import Salt.MR.SmallStones

/-!
# `M4P2MR` — the `p²` mass at `ramP2domMR`, WITHOUT `hwin`

⟦THE WALL⟧'s `p²` stone, split out of `M4ErrRewire` §1 verbatim (names, statements and
proofs unchanged) so that it sits UPSTREAM of the seam-row chain: `M4ErrRewire` reaches the
door datum through `M4Sieve`, whose own cone passes through `CapFreeArm3`, and ⟦WALL 1⟧'s
repair needs this stone at the row — i.e. strictly before `CapFreeArm3`.  Its only inputs are
MR's own coefficient domain (`RamareMR`) and the unconditional term bound
(`SmallStones.ramP2_term_norm_le`), so the split costs nothing.

  `Σ_{n≤N} ‖ramP2coeffMR N X P Q a b c n‖²/n² ≤ 16·log₂(2X)/(X·P)`

with the window read off the INDEX SET (`ramHonMR`) instead of off a joint-support
hypothesis.  `M4ErrRewire` imports this file and its §2/§3 are unchanged.
-/

noncomputable section

namespace Salt.MR

open Finset
open scoped BigOperators

/-! ## §1 — THE `p²` MASS AT `ramP2domMR`, WITHOUT `hwin` -/

/-- **THE WINDOW IS IN THE INDEX SET.**  Every pair of `ramP2domMR N X P Q` satisfies
`X ≤ p·m ≤ 2X` — this is `ramHonMR`'s own filter, and it is what replaces `hwin`. -/
theorem mem_ramP2domMR_window {N X P Q : ℕ} {σ : Σ _ : ℕ, ℕ}
    (hσ : σ ∈ ramP2domMR N X P Q) :
    (X : ℝ) ≤ (σ.1 : ℝ) * (σ.2 : ℝ) ∧ (σ.1 : ℝ) * (σ.2 : ℝ) ≤ 2 * (X : ℝ) := by
  classical
  rw [ramP2domMR, Finset.mem_sigma] at hσ
  obtain ⟨-, h2⟩ := hσ
  rw [Finset.mem_filter, ramHonMR, Finset.mem_filter] at h2
  exact ⟨h2.1.2.1, h2.1.2.2⟩

/-- The first coordinate of a `ramP2domMR` pair is a prime in `[P,Q]`. -/
theorem mem_ramP2domMR_prime {N X P Q : ℕ} {σ : Σ _ : ℕ, ℕ}
    (hσ : σ ∈ ramP2domMR N X P Q) : σ.1.Prime := by
  classical
  rw [ramP2domMR, Finset.mem_sigma] at hσ
  exact (Finset.mem_filter.mp hσ.1).2

/-- **THE FIBRE OF `ramP2domMR` OVER `n` INJECTS INTO `n`'s PRIME DIVISORS.**  A pair `(p,m)`
with `pm = n` is determined by `p`, and `p` is a prime divisor of `n`.  (`SeamCalibrationK`'s
`fiber_card_le_omega` at MR's own domain; that one is `private`.) -/
theorem ramP2domMR_fiber_card_le_omega {N X P Q n : ℕ} (hn : n ≠ 0) :
    ((ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)).card ≤ n.primeFactors.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun σ => σ.1) ?_ ?_
  · intro σ hσ
    obtain ⟨hdom, heq⟩ := Finset.mem_filter.mp hσ
    exact Nat.mem_primeFactors.mpr ⟨mem_ramP2domMR_prime hdom, ⟨σ.2, heq.symm⟩, hn⟩
  · intro σ hσ τ hτ heq
    obtain ⟨hdom, hσn⟩ := Finset.mem_filter.mp hσ
    obtain ⟨-, hτn⟩ := Finset.mem_filter.mp hτ
    have hp : σ.1.Prime := mem_ramP2domMR_prime hdom
    have heq' : σ.1 = τ.1 := heq
    have hmul : σ.1 * σ.2 = σ.1 * τ.2 := by rw [hσn, heq', hτn]
    exact Sigma.ext heq' (heq_of_eq (Nat.eq_of_mul_eq_mul_left hp.pos hmul))

/-- **`ω(n) ≤ log₂ n`**, from `2^{ω(n)} ≤ ∏_{p ∣ n} p ≤ n` (`SeamCalibrationK`'s
`omega_mul_log_two_le`, which is `private` there). -/
private lemma omegaMR_mul_log_two_le {n : ℕ} (hn : 1 ≤ n) :
    (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
  have hpow : 2 ^ n.primeFactors.card ≤ n :=
    le_trans (Finset.pow_card_le_prod _ _ _
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le))
      (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n))
  have hR : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by exact_mod_cast hpow
  have h1 : Real.log ((2 : ℝ) ^ n.primeFactors.card) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) hR
  rwa [Real.log_pow] at h1

/-- **THE MAXIMUM OF `‖coeff_n‖/n`, WITHOUT `hwin`** (`ramP2coeffMR_norm_div_le`).  The
max-half of `SeamCalibrationK.ramP2coeff_norm_div_le`, with its `by_cases hmem` replaced by
the FIBRE-EMPTINESS split: off the fibre the coefficient is a sum over `∅`, and on it the
window is read from `ramHonMR` membership rather than from a joint-support hypothesis. -/
theorem ramP2coeffMR_norm_div_le {N X P Q : ℕ} (hX : 1 ≤ X) {n : ℕ} (hn : 1 ≤ n)
    {a b c : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ‖ramP2coeffMR N X P Q a b c n‖ / (n : ℝ)
      ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) := by
  classical
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (X : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hB0 : (0 : ℝ) ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) := by positivity
  -- the unconditional fibre bound: every term has norm `≤ 2`
  have hstep : ‖ramP2coeffMR N X P Q a b c n‖
      ≤ 2 * (((ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)).card : ℝ) := by
    rw [ramP2coeffMR]
    refine (norm_sum_le _ _).trans ?_
    have h := Finset.sum_le_sum (f := fun σ : Σ _ : ℕ, ℕ =>
        ‖(ramareWeight P Q σ.1 σ.2 : ℂ) * a (σ.1 * σ.2)
          - b σ.2 * c σ.1 * ((blockOmega P Q σ.2 : ℂ) + 1)⁻¹‖)
      (g := fun _ : Σ _ : ℕ, ℕ => (2 : ℝ))
      (s := (ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n))
      (fun σ _ => ramP2_term_norm_le ha hb hc σ.1 σ.2)
    rw [Finset.sum_const, nsmul_eq_mul] at h
    linarith
  rcases Finset.eq_empty_or_nonempty
      ((ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)) with hempty | ⟨σ, hσ⟩
  · -- ⟦THE FIBRE IS EMPTY⟧ the coefficient is a sum over `∅`
    have hz : ramP2coeffMR N X P Q a b c n = 0 := by
      rw [ramP2coeffMR, hempty, Finset.sum_empty]
    rw [hz, norm_zero, zero_div]
    exact hB0
  · -- ⟦THE FIBRE IS INHABITED⟧ the window comes from the index set
    obtain ⟨hdom, hfib⟩ := Finset.mem_filter.mp hσ
    obtain ⟨hlo, hhi⟩ := mem_ramP2domMR_window hdom
    have hcast : ((σ.1 * σ.2 : ℕ) : ℝ) = (σ.1 : ℝ) * (σ.2 : ℝ) := by push_cast; ring
    have hnlo : (X : ℝ) ≤ (n : ℝ) := by rw [← hfib, hcast]; exact hlo
    have hnhi : (n : ℝ) ≤ 2 * (X : ℝ) := by rw [← hfib, hcast]; exact hhi
    have hcard : (((ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)).card : ℝ)
        ≤ (n.primeFactors.card : ℝ) := by
      exact_mod_cast ramP2domMR_fiber_card_le_omega (N := N) (X := X) (P := P) (Q := Q)
        (by omega)
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have homega : (n.primeFactors.card : ℝ) ≤ Real.logb 2 (2 * (X : ℝ)) := by
      rw [Real.logb, le_div_iff₀ hl2]
      refine le_trans (omegaMR_mul_log_two_le hn) ?_
      exact Real.log_le_log hn0 hnhi
    rw [div_le_iff₀ hn0]
    calc ‖ramP2coeffMR N X P Q a b c n‖
        ≤ 2 * (((ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)).card : ℝ) := hstep
      _ ≤ 2 * Real.logb 2 (2 * (X : ℝ)) := by linarith
      _ = 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) * (X : ℝ) := by field_simp
      _ ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hnlo hB0

/-- **The `p²` cofactor count** (`SmallStones.card_ramP2_cofactors_le`, re-derived — the
original is `private`).  The cofactors `m` with `p ∣ m` and `X ≤ pm ≤ 2X` inject into
`[1, 2X/p²]` via `m ↦ m/p`. -/
private lemma cardMR_ramP2_cofactors_le (N X p : ℕ) (hp : 0 < p) :
    ((((ramHonMR N X p).filter (fun m => p ∣ m)).card : ℕ) : ℝ)
      ≤ 2 * (X : ℝ) / (p : ℝ) ^ 2 := by
  classical
  have hcard : ((ramHonMR N X p).filter (fun m => p ∣ m)).card
      ≤ (Finset.Icc 1 (2 * X / (p * p))).card := by
    refine Finset.card_le_card_of_injOn (fun m => m / p) ?_ ?_
    · intro m hm
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hm
      obtain ⟨hmem, hdvd⟩ := hm
      rw [ramHonMR, Finset.mem_filter, Finset.mem_Icc] at hmem
      obtain ⟨⟨hm1, _hmN⟩, _hlo, hhi⟩ := hmem
      have hpm : p * m ≤ 2 * X := by
        have : ((p * m : ℕ) : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      obtain ⟨k, hk⟩ := hdvd
      have hk0 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, Nat.mul_zero] at hk; omega
        · exact h0
      have hkdiv : m / p = k := by rw [hk]; exact Nat.mul_div_cancel_left k hp
      have hkle : k ≤ 2 * X / (p * p) := by
        rw [Nat.le_div_iff_mul_le (by positivity)]
        calc k * (p * p) = p * (p * k) := by ring
          _ = p * m := by rw [hk]
          _ ≤ 2 * X := hpm
      simp only [Finset.coe_Icc, Set.mem_Icc, hkdiv]
      exact ⟨hk0, hkle⟩
    · intro m₁ hm₁ m₂ hm₂ heq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hm₁ hm₂
      have h1 : m₁ / p * p = m₁ := Nat.div_mul_cancel hm₁.2
      have h2 : m₂ / p * p = m₂ := Nat.div_mul_cancel hm₂.2
      have h3 : m₁ / p = m₂ / p := heq
      rw [← h1, ← h2, h3]
  have hIcc : (Finset.Icc 1 (2 * X / (p * p))).card = 2 * X / (p * p) := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  rw [hIcc] at hcard
  have hstep : (((2 * X / (p * p) : ℕ)) : ℝ) ≤ ((2 * X : ℕ) : ℝ) / ((p * p : ℕ) : ℝ) :=
    Nat.cast_div_le
  have hcast : ((2 * X : ℕ) : ℝ) / ((p * p : ℕ) : ℝ) = 2 * (X : ℝ) / (p : ℝ) ^ 2 := by
    push_cast; ring
  have hleft : (((ramHonMR N X p).filter (fun m => p ∣ m)).card : ℝ)
      ≤ (((2 * X / (p * p) : ℕ)) : ℝ) := by exact_mod_cast hcard
  rw [hcast] at hstep
  linarith

/-- The inner (`p`-fixed) row of the `p²` domain sum: `∑_m 2/(pm) ≤ 4/p²`
(`SmallStones.ramP2_inner_row_le`, re-derived — the original is `private`). -/
private lemma ramP2MR_inner_row_le (N X p : ℕ) (hX : 1 ≤ X) (hp : 0 < p) :
    ∑ m ∈ (ramHonMR N X p).filter (fun m => p ∣ m), 2 / ((p * m : ℕ) : ℝ)
      ≤ 4 / (p : ℝ) ^ 2 := by
  classical
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hterm : ∀ m ∈ (ramHonMR N X p).filter (fun m => p ∣ m),
      2 / ((p * m : ℕ) : ℝ) ≤ 2 / (X : ℝ) := by
    intro m hm
    rw [Finset.mem_filter, ramHonMR, Finset.mem_filter] at hm
    obtain ⟨⟨-, hlo, -⟩, -⟩ := hm
    have hcast : ((p * m : ℕ) : ℝ) = (p : ℝ) * (m : ℝ) := by push_cast; ring
    rw [hcast]
    exact div_le_div_of_nonneg_left (by norm_num) hX0 hlo
  have hbound := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hbound
  refine hbound.trans ?_
  have hc := cardMR_ramP2_cofactors_le N X p hp
  have hmul : (((ramHonMR N X p).filter (fun m => p ∣ m)).card : ℝ) * (2 / (X : ℝ))
      ≤ (2 * (X : ℝ) / (p : ℝ) ^ 2) * (2 / (X : ℝ)) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  refine hmul.trans ?_
  rw [div_mul_div_comm]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  ring_nf
  nlinarith [sq_nonneg ((p : ℝ)), hX0.le, hp0.le]

/-- **The whole `p²` domain sum** `∑_{σ ∈ ramP2domMR} 2/(σ.1σ.2) ≤ 8/P`
(`SmallStones.ramP2_dom_sum_le`, re-derived — the original is `private`). -/
theorem ramP2domMR_sum_le (N X P Q : ℕ) (hX : 1 ≤ X) (hP : 1 ≤ P) :
    ∑ σ ∈ ramP2domMR N X P Q, 2 / ((σ.1 * σ.2 : ℕ) : ℝ) ≤ 8 / (P : ℝ) := by
  classical
  rw [ramP2domMR, Finset.sum_sigma]
  have hrow : ∀ p ∈ (Finset.Icc P Q).filter Nat.Prime,
      ∑ m ∈ (ramHonMR N X p).filter (fun m => p ∣ m), 2 / ((p * m : ℕ) : ℝ)
        ≤ 4 / (p : ℝ) ^ 2 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ramP2MR_inner_row_le N X p hX hp.2.pos
  refine (Finset.sum_le_sum hrow).trans ?_
  have hsub : ∑ p ∈ (Finset.Icc P Q).filter Nat.Prime, 4 / (p : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc P Q, 4 / (n : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => by positivity)
  refine hsub.trans ?_
  have heq : ∑ n ∈ Finset.Icc P Q, 4 / (n : ℝ) ^ 2
      = 4 * ∑ n ∈ Finset.Icc P Q, 1 / (n : ℝ) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [heq]
  have htail := sum_inv_sq_tail_le hP Q
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  calc 4 * ∑ n ∈ Finset.Icc P Q, 1 / (n : ℝ) ^ 2 ≤ 4 * (2 / (P : ℝ)) := by linarith
    _ = 8 / (P : ℝ) := by ring

/-- **`Σ_n ‖coeff_n‖/n ≤ 8/P`** — the Σ-half of the direct route, i.e.
`SmallStones.ramP2mass_le`'s own ledger stopped one step before its lossy
`Σf² ≤ (Σf)²`.  `hwin`-free by construction. -/
theorem ramP2coeffMR_sum_div_le (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ / (n : ℝ) ≤ 8 / (P : ℝ) := by
  classical
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hNR : 2 * (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmaps : ∀ σ ∈ ramP2domMR N X P Q, σ.1 * σ.2 ∈ Finset.Icc 1 N := by
    intro σ hσ
    obtain ⟨hlo, hhi⟩ := mem_ramP2domMR_window hσ
    rw [Finset.mem_Icc]
    constructor
    · have h : (1 : ℝ) ≤ ((σ.1 * σ.2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
    · have h : ((σ.1 * σ.2 : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; linarith
      exact_mod_cast h
  have hpt : ∀ n ∈ Finset.Icc 1 N,
      ‖ramP2coeffMR N X P Q a b c n‖ / (n : ℝ)
        ≤ ∑ σ ∈ (ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n),
            2 / ((σ.1 * σ.2 : ℕ) : ℝ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have heq : (∑ σ ∈ (ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n),
          2 / ((σ.1 * σ.2 : ℕ) : ℝ))
        = (∑ _σ ∈ (ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n), (2 : ℝ))
            / (n : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun σ hσ => ?_)
      rw [Finset.mem_filter] at hσ
      rw [hσ.2]
    rw [heq, div_le_div_iff_of_pos_right hn0, ramP2coeffMR]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun σ _ => ?_))
    exact ramP2_term_norm_le ha hb hc σ.1 σ.2
  have hfiber : (∑ n ∈ Finset.Icc 1 N,
        ∑ σ ∈ (ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n),
          2 / ((σ.1 * σ.2 : ℕ) : ℝ))
      = ∑ σ ∈ ramP2domMR N X P Q, 2 / ((σ.1 * σ.2 : ℕ) : ℝ) :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  refine le_trans ?_ (ramP2domMR_sum_le N X P Q hX hP)
  rw [← hfiber]
  exact Finset.sum_le_sum hpt

/-- **⟦THE `p²`-MASS STONE⟧** (`ramP2massMR_direct`).  `SeamCalibrationK.ramP2mass_direct`'s
grade at MR's own domain, with **NO `hwin` anywhere**:

  `Σ_{n≤N} ‖ramP2coeffMR N X P Q a b c n‖²/n² ≤ 16·log₂(2X)/(X·P)`.

`Σ f² ≤ (max f)(Σ f)` with `max f ≤ 2·log₂(2X)/X` (`ramP2coeffMR_norm_div_le`, the window
read off `ramHonMR`) and `Σ f ≤ 8/P` (`ramP2coeffMR_sum_div_le`).  The only hypotheses are
the three `1`-bounds and the scale floors — in particular the coefficient sequence `a` is
UNCONSTRAINED, so this stone is blind to the capstone's datum. -/
theorem ramP2massMR_direct (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 16 * Real.logb 2 (2 * (X : ℝ)) / ((X : ℝ) * (P : ℝ)) := by
  classical
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (X : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hB0 : (0 : ℝ) ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) := by positivity
  have hsq : ∀ n ∈ Finset.Icc 1 N,
      ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ)
            * (‖ramP2coeffMR N X P Q a b c n‖ / (n : ℝ)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hmax := ramP2coeffMR_norm_div_le (N := N) (X := X) (P := P) (Q := Q) hX hn.1 ha hb hc
    have hnn : (0 : ℝ) ≤ ‖ramP2coeffMR N X P Q a b c n‖ / (n : ℝ) := by positivity
    calc ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
        = (‖ramP2coeffMR N X P Q a b c n‖ / (n : ℝ))
            * (‖ramP2coeffMR N X P Q a b c n‖ / (n : ℝ)) := by
          rw [← div_pow]; ring
      _ ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ)
            * (‖ramP2coeffMR N X P Q a b c n‖ / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hmax hnn
  refine (Finset.sum_le_sum hsq).trans ?_
  rw [← Finset.mul_sum]
  have hrow := ramP2coeffMR_sum_div_le N X P Q hX hN hP a b c ha hb hc
  calc 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ)
        * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ / (n : ℝ)
      ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) * (8 / (P : ℝ)) :=
        mul_le_mul_of_nonneg_left hrow hB0
    _ = 16 * Real.logb 2 (2 * (X : ℝ)) / ((X : ℝ) * (P : ℝ)) := by
        field_simp
        ring

/-! ## §2 — ⟦THE ENDPOINT WALL⟧: THE FUSED `p²` MASS

`RamareP2End`'s fused family (`ramP2domEndMR`, inner filter `p ∣ m ∨ p·m = X`) priced by §1's
own two-half route.  The design line, verified against the bytes:

* the **max** half is FREE — the fibre injection into `n.primeFactors` never read `p ∣ m`, so
  `ramP2coeffEndMR_norm_div_le` is `ramP2coeffMR_norm_div_le` with the domain renamed and the
  conclusion `2·log₂(2X)/X` UNCHANGED;
* the **Σ** half gains exactly `2·ω(X)/X`: the `∨`-filter splits by subset-sum (⟦AMENDMENT
  8⟧ — over-counting the `p² ∣ X` overlap is a legal upper bound), and the endpoint half is a
  SINGLETON per prime `p ∣ X` (`p·m = X` determines `m`), so its whole domain injects into
  `X.primeFactors` and each of its terms is exactly `2/X`.  With `ω(X) ≤ log₂ X ≤ log₂(2X)`
  the Σ half is `8/P + 2·log₂(2X)/X`.

The product is the fused stone

  `Σ_{n≤N} ‖ramP2coeffEndMR n‖²/n² ≤ 16·log₂(2X)/(X·P) + 4·(log₂(2X))²/X²`,

i.e. `ramP2massMR_direct` plus the endpoint mass `M_end = 4·(log₂(2X))²/X²`. -/

/-- The fused domain carries MR's window in its INDEX SET, exactly as the landed one. -/
theorem mem_ramP2domEndMR_window {N X P Q : ℕ} {σ : Σ _ : ℕ, ℕ}
    (hσ : σ ∈ ramP2domEndMR N X P Q) :
    (X : ℝ) ≤ (σ.1 : ℝ) * (σ.2 : ℝ) ∧ (σ.1 : ℝ) * (σ.2 : ℝ) ≤ 2 * (X : ℝ) := by
  classical
  rw [ramP2domEndMR, Finset.mem_sigma] at hσ
  obtain ⟨-, h2⟩ := hσ
  rw [Finset.mem_filter, ramHonMR, Finset.mem_filter] at h2
  exact ⟨h2.1.2.1, h2.1.2.2⟩

/-- The first coordinate of a `ramP2domEndMR` pair is a prime in `[P,Q]`. -/
theorem mem_ramP2domEndMR_prime {N X P Q : ℕ} {σ : Σ _ : ℕ, ℕ}
    (hσ : σ ∈ ramP2domEndMR N X P Q) : σ.1.Prime := by
  classical
  rw [ramP2domEndMR, Finset.mem_sigma] at hσ
  exact (Finset.mem_filter.mp hσ.1).2

/-- **THE FIBRE BOUND IS UNMOVED.**  `ramP2domMR_fiber_card_le_omega`'s injection `(p,m) ↦ p`
never used `p ∣ m` — only that `p` is prime and `pm = n` — so it transplants verbatim to the
fused domain. -/
theorem ramP2domEndMR_fiber_card_le_omega {N X P Q n : ℕ} (hn : n ≠ 0) :
    ((ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)).card ≤ n.primeFactors.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun σ => σ.1) ?_ ?_
  · intro σ hσ
    obtain ⟨hdom, heq⟩ := Finset.mem_filter.mp hσ
    exact Nat.mem_primeFactors.mpr ⟨mem_ramP2domEndMR_prime hdom, ⟨σ.2, heq.symm⟩, hn⟩
  · intro σ hσ τ hτ heq
    obtain ⟨hdom, hσn⟩ := Finset.mem_filter.mp hσ
    obtain ⟨-, hτn⟩ := Finset.mem_filter.mp hτ
    have hp : σ.1.Prime := mem_ramP2domEndMR_prime hdom
    have heq' : σ.1 = τ.1 := heq
    have hmul : σ.1 * σ.2 = σ.1 * τ.2 := by rw [hσn, heq', hτn]
    exact Sigma.ext heq' (heq_of_eq (Nat.eq_of_mul_eq_mul_left hp.pos hmul))

/-- **THE MAX HALF, UNCHANGED** (`ramP2coeffEndMR_norm_div_le`).  `ramP2coeffMR_norm_div_le`
at the fused domain: same fibre-emptiness split, same window read off `ramHonMR`, same
conclusion `2·log₂(2X)/X`. -/
theorem ramP2coeffEndMR_norm_div_le {N X P Q : ℕ} (hX : 1 ≤ X) {n : ℕ} (hn : 1 ≤ n)
    {a b c : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ‖ramP2coeffEndMR N X P Q a b c n‖ / (n : ℝ)
      ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) := by
  classical
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (X : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hB0 : (0 : ℝ) ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) := by positivity
  have hstep : ‖ramP2coeffEndMR N X P Q a b c n‖
      ≤ 2 * (((ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)).card : ℝ) := by
    rw [ramP2coeffEndMR]
    refine (norm_sum_le _ _).trans ?_
    have h := Finset.sum_le_sum (f := fun σ : Σ _ : ℕ, ℕ =>
        ‖(ramareWeight P Q σ.1 σ.2 : ℂ) * a (σ.1 * σ.2)
          - b σ.2 * c σ.1 * ((blockOmega P Q σ.2 : ℂ) + 1)⁻¹‖)
      (g := fun _ : Σ _ : ℕ, ℕ => (2 : ℝ))
      (s := (ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n))
      (fun σ _ => ramP2_term_norm_le ha hb hc σ.1 σ.2)
    rw [Finset.sum_const, nsmul_eq_mul] at h
    linarith
  rcases Finset.eq_empty_or_nonempty
      ((ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)) with hempty | ⟨σ, hσ⟩
  · have hz : ramP2coeffEndMR N X P Q a b c n = 0 := by
      rw [ramP2coeffEndMR, hempty, Finset.sum_empty]
    rw [hz, norm_zero, zero_div]
    exact hB0
  · obtain ⟨hdom, hfib⟩ := Finset.mem_filter.mp hσ
    obtain ⟨hlo, hhi⟩ := mem_ramP2domEndMR_window hdom
    have hcast : ((σ.1 * σ.2 : ℕ) : ℝ) = (σ.1 : ℝ) * (σ.2 : ℝ) := by push_cast; ring
    have hnlo : (X : ℝ) ≤ (n : ℝ) := by rw [← hfib, hcast]; exact hlo
    have hnhi : (n : ℝ) ≤ 2 * (X : ℝ) := by rw [← hfib, hcast]; exact hhi
    have hcard : (((ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)).card : ℝ)
        ≤ (n.primeFactors.card : ℝ) := by
      exact_mod_cast ramP2domEndMR_fiber_card_le_omega (N := N) (X := X) (P := P) (Q := Q)
        (by omega)
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have homega : (n.primeFactors.card : ℝ) ≤ Real.logb 2 (2 * (X : ℝ)) := by
      rw [Real.logb, le_div_iff₀ hl2]
      refine le_trans (omegaMR_mul_log_two_le hn) ?_
      exact Real.log_le_log hn0 hnhi
    rw [div_le_iff₀ hn0]
    calc ‖ramP2coeffEndMR N X P Q a b c n‖
        ≤ 2 * (((ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)).card : ℝ) := hstep
      _ ≤ 2 * Real.logb 2 (2 * (X : ℝ)) := by linarith
      _ = 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) * (X : ℝ) := by field_simp
      _ ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hnlo hB0

/-- **THE ENDPOINT DOMAIN INJECTS INTO `X.primeFactors`.**  A pair `(p,m)` with `p·m = X` is
determined by `p`, and `p` is then a prime divisor of `X` — so the endpoint half of the fused
domain has at most `ω(X)` points, whatever the band. -/
private lemma ramP2endMR_card_le (N X P Q : ℕ) (hX : 1 ≤ X) :
    (((Finset.Icc P Q).filter Nat.Prime).sigma
        (fun p => (ramHonMR N X p).filter (fun m => p * m = X))).card
      ≤ X.primeFactors.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun σ => σ.1) ?_ ?_
  · intro σ hσ
    obtain ⟨h1, h2⟩ := Finset.mem_sigma.mp hσ
    exact Nat.mem_primeFactors.mpr ⟨(Finset.mem_filter.mp h1).2,
      ⟨σ.2, ((Finset.mem_filter.mp h2).2).symm⟩, by omega⟩
  · intro σ hσ τ hτ heq
    obtain ⟨hσ1, hσ2⟩ := Finset.mem_sigma.mp hσ
    obtain ⟨-, hτ2⟩ := Finset.mem_sigma.mp hτ
    have hp : σ.1.Prime := (Finset.mem_filter.mp hσ1).2
    have hσX : σ.1 * σ.2 = X := (Finset.mem_filter.mp hσ2).2
    have hτX : τ.1 * τ.2 = X := (Finset.mem_filter.mp hτ2).2
    have heq' : σ.1 = τ.1 := heq
    have hmul : σ.1 * σ.2 = σ.1 * τ.2 := by rw [hσX, heq', hτX]
    exact Sigma.ext heq' (heq_of_eq (Nat.eq_of_mul_eq_mul_left hp.pos hmul))

/-- **THE Σ HALF, FUSED** (`ramP2domEndMR_sum_le`).  The `∨`-filter splits by subset-sum, the
`p ∣ m` half is §1's `8/P` verbatim, and the endpoint half is `2·ω(X)/X ≤ 2·log₂(2X)/X`. -/
theorem ramP2domEndMR_sum_le (N X P Q : ℕ) (hX : 1 ≤ X) (hP : 1 ≤ P) :
    ∑ σ ∈ ramP2domEndMR N X P Q, 2 / ((σ.1 * σ.2 : ℕ) : ℝ)
      ≤ 8 / (P : ℝ) + 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) := by
  classical
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  rw [ramP2domEndMR, Finset.sum_sigma]
  -- ⟦AMENDMENT 8⟧ the `∨`-filter splits by subset-sum; the overlap is over-counted, legally
  have hrow : ∀ p ∈ (Finset.Icc P Q).filter Nat.Prime,
      (∑ m ∈ (ramHonMR N X p).filter (fun m => p ∣ m ∨ p * m = X), 2 / ((p * m : ℕ) : ℝ))
        ≤ (∑ m ∈ (ramHonMR N X p).filter (fun m => p ∣ m), 2 / ((p * m : ℕ) : ℝ))
          + ∑ m ∈ (ramHonMR N X p).filter (fun m => p * m = X), 2 / ((p * m : ℕ) : ℝ) := by
    intro p _
    rw [Finset.filter_or]
    have hui := Finset.sum_union_inter
      (s₁ := (ramHonMR N X p).filter (fun m => p ∣ m))
      (s₂ := (ramHonMR N X p).filter (fun m => p * m = X))
      (f := fun m => 2 / ((p * m : ℕ) : ℝ))
    have hinter : (0 : ℝ) ≤ ∑ m ∈ ((ramHonMR N X p).filter (fun m => p ∣ m))
        ∩ ((ramHonMR N X p).filter (fun m => p * m = X)), 2 / ((p * m : ℕ) : ℝ) :=
      Finset.sum_nonneg (fun m _ => by positivity)
    linarith
  refine (Finset.sum_le_sum hrow).trans ?_
  rw [Finset.sum_add_distrib]
  have hA : (∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
      ∑ m ∈ (ramHonMR N X p).filter (fun m => p ∣ m), 2 / ((p * m : ℕ) : ℝ))
      ≤ 8 / (P : ℝ) := by
    have h := ramP2domMR_sum_le N X P Q hX hP
    rwa [ramP2domMR, Finset.sum_sigma] at h
  -- ⟦THE ENDPOINT HALF⟧ every term is exactly `2/X`, and the domain injects into `X.primeFactors`
  have hval : ∀ p ∈ (Finset.Icc P Q).filter Nat.Prime,
      (∑ m ∈ (ramHonMR N X p).filter (fun m => p * m = X), 2 / ((p * m : ℕ) : ℝ))
        = ((((ramHonMR N X p).filter (fun m => p * m = X)).card : ℕ) : ℝ) * (2 / (X : ℝ)) := by
    intro p _
    have hterm : ∀ m ∈ (ramHonMR N X p).filter (fun m => p * m = X),
        2 / ((p * m : ℕ) : ℝ) = 2 / (X : ℝ) := by
      intro m hm
      rw [(Finset.mem_filter.mp hm).2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_mul]
  have hcards : (∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
        ((((ramHonMR N X p).filter (fun m => p * m = X)).card : ℕ) : ℝ))
      ≤ (X.primeFactors.card : ℝ) := by
    have hc := ramP2endMR_card_le N X P Q hX
    rw [Finset.card_sigma] at hc
    exact_mod_cast hc
  have homega : (X.primeFactors.card : ℝ) ≤ Real.logb 2 (2 * (X : ℝ)) := by
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.logb, le_div_iff₀ hl2]
    exact le_trans (omegaMR_mul_log_two_le hX) (Real.log_le_log hX0 (by linarith))
  have hstep : (∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
        ((((ramHonMR N X p).filter (fun m => p * m = X)).card : ℕ) : ℝ)) * (2 / (X : ℝ))
      ≤ Real.logb 2 (2 * (X : ℝ)) * (2 / (X : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_trans hcards homega) (by positivity)
  have hid : Real.logb 2 (2 * (X : ℝ)) * (2 / (X : ℝ))
      = 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) := by ring
  linarith [hid.le, hid.ge]

/-- **`Σ_n ‖coeff_n‖/n ≤ 8/P + 2·log₂(2X)/X`** — the fused Σ half at the coefficient. -/
theorem ramP2coeffEndMR_sum_div_le (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffEndMR N X P Q a b c n‖ / (n : ℝ)
      ≤ 8 / (P : ℝ) + 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) := by
  classical
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hNR : 2 * (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmaps : ∀ σ ∈ ramP2domEndMR N X P Q, σ.1 * σ.2 ∈ Finset.Icc 1 N := by
    intro σ hσ
    obtain ⟨hlo, hhi⟩ := mem_ramP2domEndMR_window hσ
    rw [Finset.mem_Icc]
    constructor
    · have h : (1 : ℝ) ≤ ((σ.1 * σ.2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
    · have h : ((σ.1 * σ.2 : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; linarith
      exact_mod_cast h
  have hpt : ∀ n ∈ Finset.Icc 1 N,
      ‖ramP2coeffEndMR N X P Q a b c n‖ / (n : ℝ)
        ≤ ∑ σ ∈ (ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n),
            2 / ((σ.1 * σ.2 : ℕ) : ℝ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have heq : (∑ σ ∈ (ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n),
          2 / ((σ.1 * σ.2 : ℕ) : ℝ))
        = (∑ _σ ∈ (ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n), (2 : ℝ))
            / (n : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun σ hσ => ?_)
      rw [Finset.mem_filter] at hσ
      rw [hσ.2]
    rw [heq, div_le_div_iff_of_pos_right hn0, ramP2coeffEndMR]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun σ _ => ?_))
    exact ramP2_term_norm_le ha hb hc σ.1 σ.2
  have hfiber : (∑ n ∈ Finset.Icc 1 N,
        ∑ σ ∈ (ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n),
          2 / ((σ.1 * σ.2 : ℕ) : ℝ))
      = ∑ σ ∈ ramP2domEndMR N X P Q, 2 / ((σ.1 * σ.2 : ℕ) : ℝ) :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  refine le_trans ?_ (ramP2domEndMR_sum_le N X P Q hX hP)
  rw [← hfiber]
  exact Finset.sum_le_sum hpt

/-- **⟦THE FUSED `p²`-MASS STONE⟧** (`ramP2massEndMR_direct`).  `ramP2massMR_direct`'s grade
at the FUSED domain — the landed grade plus the endpoint mass:

  `Σ_{n≤N} ‖ramP2coeffEndMR n‖²/n² ≤ 16·log₂(2X)/(X·P) + 4·(log₂(2X))²/X²`.

`Σ f² ≤ (max f)(Σ f)` with `max f ≤ 2·log₂(2X)/X` (unmoved) and
`Σ f ≤ 8/P + 2·log₂(2X)/X`.  Datum-blind: `a` is unconstrained beyond its `1`-bound. -/
theorem ramP2massEndMR_direct (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 16 * Real.logb 2 (2 * (X : ℝ)) / ((X : ℝ) * (P : ℝ))
        + 4 * (Real.logb 2 (2 * (X : ℝ))) ^ 2 / (X : ℝ) ^ 2 := by
  classical
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (X : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hB0 : (0 : ℝ) ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ) := by positivity
  have hsq : ∀ n ∈ Finset.Icc 1 N,
      ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ)
            * (‖ramP2coeffEndMR N X P Q a b c n‖ / (n : ℝ)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hmax := ramP2coeffEndMR_norm_div_le (N := N) (X := X) (P := P) (Q := Q) hX hn.1
      ha hb hc
    have hnn : (0 : ℝ) ≤ ‖ramP2coeffEndMR N X P Q a b c n‖ / (n : ℝ) := by positivity
    calc ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
        = (‖ramP2coeffEndMR N X P Q a b c n‖ / (n : ℝ))
            * (‖ramP2coeffEndMR N X P Q a b c n‖ / (n : ℝ)) := by
          rw [← div_pow]; ring
      _ ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ)
            * (‖ramP2coeffEndMR N X P Q a b c n‖ / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hmax hnn
  refine (Finset.sum_le_sum hsq).trans ?_
  rw [← Finset.mul_sum]
  have hrow := ramP2coeffEndMR_sum_div_le N X P Q hX hN hP a b c ha hb hc
  calc 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ)
        * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffEndMR N X P Q a b c n‖ / (n : ℝ)
      ≤ 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ)
          * (8 / (P : ℝ) + 2 * Real.logb 2 (2 * (X : ℝ)) / (X : ℝ)) :=
        mul_le_mul_of_nonneg_left hrow hB0
    _ = 16 * Real.logb 2 (2 * (X : ℝ)) / ((X : ℝ) * (P : ℝ))
          + 4 * (Real.logb 2 (2 * (X : ℝ))) ^ 2 / (X : ℝ) ^ 2 := by
        field_simp
        ring

/-! ## §3 — ⟦THE DIRECT `L²` PRICING⟧: the `p²` row WITHOUT the Hölder split

§1's grade `16·log₂(2X)/(X·P)` is a Hölder product `Σf² ≤ (max f)(Σ f)`, and its whole
`X`-dependence is the *sup* half's crudest possible bound, `ω(n) ≤ log₂ n`.  The direct
route never forms the sup.  Write

  `r(n) := #{p ∈ [P,Q] prime : p² ∣ n}`   (`ramP2fibreMR`),

so that `‖coeff_n‖ ≤ 2·r(n)` (the fibre injects into that set — `p ∣ m` and `pm = n` give
`p² ∣ n`, and `p` determines the pair) and the coefficient VANISHES off `[X, 2X]`.  Then

  `Σ_{n ≤ N} ‖c_n‖²/n²  ≤  (4/X²)·Σ_{n ≤ 2X} r(n)²`,

and `r(n)² = Σ_{p,q} [p²∣n][q²∣n]` swaps into a divisibility count:

* the DIAGONAL `Σ_p #{n ≤ 2X : p² ∣ n} = Σ_p ⌊2X/p²⌋ ≤ 2X·Σ_{p ≥ P} p^{-2} ≤ 2X·(2/P)`;
* the OFF-DIAGONAL — for `p ≠ q` prime, `p² ∣ n ∧ q² ∣ n ↔ (pq)² ∣ n` (the squares are
  coprime), so the count is EXACTLY `⌊2X/(pq)²⌋` (`Nat.Ioc_filter_dvd_card_eq_div` — no
  `+1`), and `Σ_{p≠q} ≤ 2X·(2/P)²`.

The product is `16/(X·P) + 32/(X·P²)`: **the numerator is `X`-FREE**.  At `4 ≤ P` the
off-diagonal is at most half the diagonal and the whole row is `24/(X·P)`; at `2 ≤ P` it is
`32/(X·P)`.  (The `24` is sharp for this route at `P = 4` and FAILS at `P ≤ 3` — hence the
`4 ≤ P` binder, free at every consumer since `P₁ ≥ 64`.)  §1's Hölder route stays landed
beside this one; nothing above it moves. -/

/-- **THE `p²` FIBRE SET** (`ramP2fibreMR`): the band primes whose SQUARE divides `n`.  This
is the object the direct `L²` route counts, in place of `n.primeFactors`. -/
def ramP2fibreMR (P Q n : ℕ) : Finset ℕ :=
  ((Finset.Icc P Q).filter Nat.Prime).filter (fun p => p ^ 2 ∣ n)

/-- **THE FIBRE INJECTS INTO `ramP2fibreMR`.**  A pair `(p,m) ∈ ramP2domMR` over `n` carries
`p ∣ m` from the domain's inner filter, so `n = p·m` is divisible by `p²`; and the pair is
determined by `p` (as in `ramP2domMR_fiber_card_le_omega`). -/
theorem ramP2domMR_fiber_card_le_p2 {N X P Q n : ℕ} :
    ((ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)).card
      ≤ (ramP2fibreMR P Q n).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun σ => σ.1) ?_ ?_
  · intro σ hσ
    obtain ⟨hdom, heq⟩ := Finset.mem_filter.mp hσ
    have hdom' := hdom
    rw [ramP2domMR, Finset.mem_sigma] at hdom'
    obtain ⟨hp, hm⟩ := hdom'
    obtain ⟨-, hdvd⟩ := Finset.mem_filter.mp hm
    obtain ⟨k, hk⟩ := hdvd
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hp, ⟨k, ?_⟩⟩)
    rw [← heq, hk]
    ring
  · intro σ hσ τ hτ heqp
    obtain ⟨hdom, hσn⟩ := Finset.mem_filter.mp hσ
    obtain ⟨-, hτn⟩ := Finset.mem_filter.mp hτ
    have hp : σ.1.Prime := mem_ramP2domMR_prime hdom
    have heq' : σ.1 = τ.1 := heqp
    have hmul : σ.1 * σ.2 = σ.1 * τ.2 := by rw [hσn, heq', hτn]
    exact Sigma.ext heq' (heq_of_eq (Nat.eq_of_mul_eq_mul_left hp.pos hmul))

/-- **THE DIVISIBILITY COUNT** (`card_dvd_Icc_le`): `#{n ∈ [1,Y] : d ∣ n} = ⌊Y/d⌋ ≤ Y/d`,
EXACTLY — `Finset.Icc 1 Y = Finset.Ioc 0 Y` and `Nat.Ioc_filter_dvd_card_eq_div`.  There is
no `+1`: the interval starts at `1`, not at `0`. -/
private lemma card_dvd_Icc_le (Y d : ℕ) :
    ((((Finset.Icc 1 Y).filter (fun n => d ∣ n)).card : ℕ) : ℝ) ≤ (Y : ℝ) / (d : ℝ) := by
  have hIcc : Finset.Icc 1 Y = Finset.Ioc 0 Y := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
  exact_mod_cast Nat.cast_div_le

/-- **THE OFF-DIAGONAL IS EXACT.**  For distinct primes `p, q`, `p² ∣ n ∧ q² ∣ n ↔ (pq)² ∣ n`
— the two squares are coprime, so the joint count is the single count at the product. -/
private lemma filter_p2_q2_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (Y : ℕ) :
    (Finset.Icc 1 Y).filter (fun n => p ^ 2 ∣ n ∧ q ^ 2 ∣ n)
      = (Finset.Icc 1 Y).filter (fun n => (p * q) ^ 2 ∣ n) := by
  classical
  have hcop : Nat.Coprime (p ^ 2) (q ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hne)
  refine Finset.filter_congr (fun n _ => ?_)
  constructor
  · rintro ⟨h1, h2⟩
    have : p ^ 2 * q ^ 2 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2
    simpa [mul_pow] using this
  · intro h
    rw [mul_pow] at h
    exact ⟨dvd_trans (Dvd.intro _ rfl) h, dvd_trans (Dvd.intro_left _ rfl) h⟩

/-- **⟦THE `L²` FIBRE COUNT⟧** (`sum_sq_ramP2fibreMR_le`):

  `Σ_{n ≤ Y} r(n)² ≤ Y·(2/P)·(1 + 2/P)` ,

the diagonal `Y·(2/P)` plus the exact off-diagonal `Y·(2/P)²`.  `r(n)²` is expanded as the
double sum over the band, the `n`-sum is swapped inside, and each inner count is
`card_dvd_Icc_le` (at `p²` on the diagonal, at `(pq)²` off it). -/
private lemma sum_sq_ramP2fibreMR_le (Y P Q : ℕ) (hP : 1 ≤ P) :
    ∑ n ∈ Finset.Icc 1 Y, ((ramP2fibreMR P Q n).card : ℝ) ^ 2
      ≤ (Y : ℝ) * (2 / (P : ℝ)) * (1 + 2 / (P : ℝ)) := by
  classical
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hY0 : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg _
  set B : Finset ℕ := (Finset.Icc P Q).filter Nat.Prime with hB
  -- the band's own `Σ p^{-2} ≤ 2/P`
  have hband : ∑ p ∈ B, 1 / (p : ℝ) ^ 2 ≤ 2 / (P : ℝ) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => by positivity)) ?_
    exact sum_inv_sq_tail_le hP Q
  have hband0 : (0 : ℝ) ≤ ∑ p ∈ B, 1 / (p : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun p _ => by positivity)
  -- `r(n)²` as a double sum over the band
  have hsq : ∀ n : ℕ, ((ramP2fibreMR P Q n).card : ℝ) ^ 2
      = ∑ p ∈ B, ∑ q ∈ B, (if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0) := by
    intro n
    have hc : ((ramP2fibreMR P Q n).card : ℝ)
        = ∑ p ∈ B, (if p ^ 2 ∣ n then (1 : ℝ) else 0) := by
      rw [ramP2fibreMR, hB]
      exact Finset.natCast_card_filter _ _
    rw [hc, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    by_cases h1 : p ^ 2 ∣ n <;> by_cases h2 : q ^ 2 ∣ n <;> simp [h1, h2]
  -- swap the `n`-sum inside
  have hswap : ∑ n ∈ Finset.Icc 1 Y, ((ramP2fibreMR P Q n).card : ℝ) ^ 2
      = ∑ p ∈ B, ∑ q ∈ B, ∑ n ∈ Finset.Icc 1 Y,
          (if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0) := by
    rw [Finset.sum_congr rfl (fun n (_ : n ∈ Finset.Icc 1 Y) => hsq n), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
  -- each inner sum is a divisibility count
  have hcnt : ∀ p q : ℕ, (∑ n ∈ Finset.Icc 1 Y,
        (if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0))
      = ((((Finset.Icc 1 Y).filter (fun n => p ^ 2 ∣ n ∧ q ^ 2 ∣ n)).card : ℕ) : ℝ) :=
    fun p q => (Finset.natCast_card_filter _ _).symm
  -- the row at a fixed `p`: the diagonal plus the off-diagonal
  have hrow : ∀ p ∈ B, (∑ q ∈ B, ∑ n ∈ Finset.Icc 1 Y,
        (if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0))
      ≤ (Y : ℝ) * (1 / (p : ℝ) ^ 2) * (1 + 2 / (P : ℝ)) := by
    intro p hpB
    have hp : p.Prime := (Finset.mem_filter.mp hpB).2
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hdiag : (∑ n ∈ Finset.Icc 1 Y,
          (if p ^ 2 ∣ n ∧ p ^ 2 ∣ n then (1 : ℝ) else 0))
        ≤ (Y : ℝ) * (1 / (p : ℝ) ^ 2) := by
      rw [hcnt p p]
      have hfe : (Finset.Icc 1 Y).filter (fun n => p ^ 2 ∣ n ∧ p ^ 2 ∣ n)
          = (Finset.Icc 1 Y).filter (fun n => p ^ 2 ∣ n) :=
        Finset.filter_congr (fun n _ => by tauto)
      rw [hfe]
      refine le_trans (card_dvd_Icc_le Y (p ^ 2)) (le_of_eq ?_)
      push_cast
      ring
    have hoff : ∀ q ∈ B.erase p, (∑ n ∈ Finset.Icc 1 Y,
          (if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0))
        ≤ (Y : ℝ) * (1 / (p : ℝ) ^ 2) * (1 / (q : ℝ) ^ 2) := by
      intro q hq
      have hqne : q ≠ p := Finset.ne_of_mem_erase hq
      have hqB : q ∈ B := Finset.mem_of_mem_erase hq
      have hqp : q.Prime := (Finset.mem_filter.mp hqB).2
      have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqp.pos
      rw [hcnt p q, filter_p2_q2_eq hp hqp (Ne.symm hqne) Y]
      refine le_trans (card_dvd_Icc_le Y ((p * q) ^ 2)) (le_of_eq ?_)
      push_cast
      field_simp
    have hsum_off : (∑ q ∈ B.erase p, ∑ n ∈ Finset.Icc 1 Y,
          (if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0))
        ≤ (Y : ℝ) * (1 / (p : ℝ) ^ 2) * (2 / (P : ℝ)) := by
      refine le_trans (Finset.sum_le_sum hoff) ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun n _ _ => by positivity)) hband
    rw [← Finset.add_sum_erase B _ hpB]
    have hid : (Y : ℝ) * (1 / (p : ℝ) ^ 2) * (1 + 2 / (P : ℝ))
        = (Y : ℝ) * (1 / (p : ℝ) ^ 2) + (Y : ℝ) * (1 / (p : ℝ) ^ 2) * (2 / (P : ℝ)) := by
      ring
    rw [hid]
    linarith
  rw [hswap]
  refine le_trans (Finset.sum_le_sum hrow) ?_
  have hfac : (∑ p ∈ B, (Y : ℝ) * (1 / (p : ℝ) ^ 2) * (1 + 2 / (P : ℝ)))
      = (Y : ℝ) * (1 + 2 / (P : ℝ)) * ∑ p ∈ B, 1 / (p : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [hfac]
  have hmul : (Y : ℝ) * (1 + 2 / (P : ℝ)) * ∑ p ∈ B, 1 / (p : ℝ) ^ 2
      ≤ (Y : ℝ) * (1 + 2 / (P : ℝ)) * (2 / (P : ℝ)) :=
    mul_le_mul_of_nonneg_left hband (by positivity)
  linarith [hmul]

/-- **THE PRICED FIBRE SUM** (`sum_fibre_sq_price`): §3's counting lemma at `Y = 2X`, with
the `4/X²` weight already applied —

  `Σ_{n ≤ 2X} 4·r(n)²/X² ≤ 16/(X·P) + 32/(X·P²)` .

Both the strict and the fused stone reduce to this one inequality. -/
private lemma sum_fibre_sq_price (X P Q : ℕ) (hX : 1 ≤ X) (hP : 1 ≤ P) :
    (∑ n ∈ Finset.Icc 1 (2 * X), 4 * ((ramP2fibreMR P Q n).card : ℝ) ^ 2 / (X : ℝ) ^ 2)
      ≤ 16 / ((X : ℝ) * (P : ℝ)) + 32 / ((X : ℝ) * (P : ℝ) ^ 2) := by
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hfib := sum_sq_ramP2fibreMR_le (2 * X) P Q hP
  have hpull : (∑ n ∈ Finset.Icc 1 (2 * X),
        4 * ((ramP2fibreMR P Q n).card : ℝ) ^ 2 / (X : ℝ) ^ 2)
      = 4 / (X : ℝ) ^ 2 * ∑ n ∈ Finset.Icc 1 (2 * X),
          ((ramP2fibreMR P Q n).card : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [hpull]
  have hstep : 4 / (X : ℝ) ^ 2 * ∑ n ∈ Finset.Icc 1 (2 * X),
        ((ramP2fibreMR P Q n).card : ℝ) ^ 2
      ≤ 4 / (X : ℝ) ^ 2 * (((2 * X : ℕ) : ℝ) * (2 / (P : ℝ)) * (1 + 2 / (P : ℝ))) :=
    mul_le_mul_of_nonneg_left hfib (by positivity)
  refine hstep.trans (le_of_eq ?_)
  push_cast
  field_simp
  ring

/-- The `p²` coefficient VANISHES above the window: the fibre's own membership forces
`pm ≤ 2X`. -/
private lemma ramP2coeffMR_eq_zero_of_gt {N X P Q : ℕ} {n : ℕ} (hn : 2 * X < n)
    (a b c : ℕ → ℂ) : ramP2coeffMR N X P Q a b c n = 0 := by
  classical
  have hemp : (ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro σ hσ
    obtain ⟨hdom, heq⟩ := Finset.mem_filter.mp hσ
    obtain ⟨-, hhi⟩ := mem_ramP2domMR_window hdom
    have hcast : ((σ.1 * σ.2 : ℕ) : ℝ) = (σ.1 : ℝ) * (σ.2 : ℝ) := by push_cast; ring
    have hle : ((n : ℕ) : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by
      rw [← heq, hcast]; push_cast; exact hhi
    have : n ≤ 2 * X := by exact_mod_cast hle
    omega
  rw [ramP2coeffMR, hemp, Finset.sum_empty]

/-- **⟦THE `p²`-MASS STONE, DIRECT `L²`⟧** (`ramP2massMR_L2`).  The two-term raw form:

  `Σ_{n ≤ N} ‖ramP2coeffMR n‖²/n² ≤ 16/(X·P) + 32/(X·P²)` .

`X`-FREE numerators — the `log₂(2X)` of `ramP2massMR_direct` was the Hölder sup-half's
artifact and is gone.  Datum-blind exactly as the landed stone: `a` is unconstrained
beyond its `1`-bound. -/
theorem ramP2massMR_L2 (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 16 / ((X : ℝ) * (P : ℝ)) + 32 / ((X : ℝ) * (P : ℝ) ^ 2) := by
  classical
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  -- ⟦STEP 1⟧ the sum truncates at `2X`
  have hsub : Finset.Icc 1 (2 * X) ⊆ Finset.Icc 1 N := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    omega
  have htrunc : (∑ n ∈ Finset.Icc 1 (2 * X),
        ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
      = ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 := by
    refine Finset.sum_subset hsub (fun n hn hnot => ?_)
    rw [Finset.mem_Icc] at hn
    have hgt : 2 * X < n := by
      by_contra hcon
      exact hnot (Finset.mem_Icc.mpr ⟨hn.1, by omega⟩)
    rw [ramP2coeffMR_eq_zero_of_gt hgt a b c, norm_zero]
    simp
  -- ⟦STEP 2⟧ the pointwise `L²` bound by the fibre count
  have hpt : ∀ n ∈ Finset.Icc 1 (2 * X),
      ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ 4 * ((ramP2fibreMR P Q n).card : ℝ) ^ 2 / (X : ℝ) ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have hstep : ‖ramP2coeffMR N X P Q a b c n‖
        ≤ 2 * (((ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)).card : ℝ) := by
      rw [ramP2coeffMR]
      refine (norm_sum_le _ _).trans ?_
      have h := Finset.sum_le_sum (f := fun σ : Σ _ : ℕ, ℕ =>
          ‖(ramareWeight P Q σ.1 σ.2 : ℂ) * a (σ.1 * σ.2)
            - b σ.2 * c σ.1 * ((blockOmega P Q σ.2 : ℂ) + 1)⁻¹‖)
        (g := fun _ : Σ _ : ℕ, ℕ => (2 : ℝ))
        (s := (ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n))
        (fun σ _ => ramP2_term_norm_le ha hb hc σ.1 σ.2)
      rw [Finset.sum_const, nsmul_eq_mul] at h
      linarith
    rcases Finset.eq_empty_or_nonempty
        ((ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)) with hempty | ⟨σ, hσ⟩
    · have hz : ramP2coeffMR N X P Q a b c n = 0 := by
        rw [ramP2coeffMR, hempty, Finset.sum_empty]
      rw [hz, norm_zero]
      have h0 : (0 : ℝ) ≤ 4 * ((ramP2fibreMR P Q n).card : ℝ) ^ 2 / (X : ℝ) ^ 2 := by
        positivity
      simpa using h0
    · obtain ⟨hdom, hfib⟩ := Finset.mem_filter.mp hσ
      obtain ⟨hlo, -⟩ := mem_ramP2domMR_window hdom
      have hcast : ((σ.1 * σ.2 : ℕ) : ℝ) = (σ.1 : ℝ) * (σ.2 : ℝ) := by push_cast; ring
      have hnlo : (X : ℝ) ≤ (n : ℝ) := by rw [← hfib, hcast]; exact hlo
      have hcard : ((((ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)).card : ℕ) : ℝ)
          ≤ ((ramP2fibreMR P Q n).card : ℝ) := by
        exact_mod_cast ramP2domMR_fiber_card_le_p2 (N := N) (X := X) (P := P) (Q := Q) (n := n)
      have hnorm : ‖ramP2coeffMR N X P Q a b c n‖ ≤ 2 * ((ramP2fibreMR P Q n).card : ℝ) := by
        linarith
      have hnn : (0 : ℝ) ≤ ‖ramP2coeffMR N X P Q a b c n‖ := norm_nonneg _
      have hnum : ‖ramP2coeffMR N X P Q a b c n‖ ^ 2
          ≤ 4 * ((ramP2fibreMR P Q n).card : ℝ) ^ 2 := by nlinarith
      have hden : (X : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
      calc ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
          ≤ 4 * ((ramP2fibreMR P Q n).card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
            gcongr
        _ ≤ 4 * ((ramP2fibreMR P Q n).card : ℝ) ^ 2 / (X : ℝ) ^ 2 := by
            gcongr
  -- ⟦STEP 3⟧ the fibre count
  rw [← htrunc]
  exact le_trans (Finset.sum_le_sum hpt) (sum_fibre_sq_price X P Q hX hP)

/-- **⟦THE `p²`-MASS STONE, `24/(X·P)`⟧** (`ramP2massMR_L2_direct`) — the R1 grade, at the
`4 ≤ P` floor (free everywhere downstream: `calP_door_one_ge` gives `P₁ ≥ 64`):

  `Σ_{n ≤ N} ‖ramP2coeffMR n‖²/n² ≤ 24/(X·P)` ,

**`X`-FREE**.  At `4 ≤ P` the off-diagonal `32/(X·P²)` is at most half the diagonal
`16/(X·P)`; the constant BREAKS at `P ≤ 3` (at `P = 3` the true value is `80/3 > 24`). -/
theorem ramP2massMR_L2_direct (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hP : 4 ≤ P)
    (a b c : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 24 / ((X : ℝ) * (P : ℝ)) := by
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hP4 : (4 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < (P : ℝ) := by linarith
  refine (ramP2massMR_L2 N X P Q hX hN (by omega) a b c ha hb hc).trans ?_
  have hoff : 32 / ((X : ℝ) * (P : ℝ) ^ 2) ≤ 8 / ((X : ℝ) * (P : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hX0.le hP0.le) (by linarith : (0 : ℝ) ≤ (P : ℝ) - 4)]
  have hid : 16 / ((X : ℝ) * (P : ℝ)) + 8 / ((X : ℝ) * (P : ℝ))
      = 24 / ((X : ℝ) * (P : ℝ)) := by ring
  linarith

/-- **THE `2 ≤ P` FORM** (`ramP2massMR_L2_direct32`): the same stone at the weaker floor,
constant `32`.  Kept beside the `24`-form so the `4 ≤ P` binder is never load-bearing for
mere existence of an `X`-free grade. -/
theorem ramP2massMR_L2_direct32 (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hP : 2 ≤ P)
    (a b c : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 32 / ((X : ℝ) * (P : ℝ)) := by
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hP2 : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < (P : ℝ) := by linarith
  refine (ramP2massMR_L2 N X P Q hX hN (by omega) a b c ha hb hc).trans ?_
  have hoff : 32 / ((X : ℝ) * (P : ℝ) ^ 2) ≤ 16 / ((X : ℝ) * (P : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hX0.le hP0.le) (by linarith : (0 : ℝ) ≤ (P : ℝ) - 2)]
  have hid : 16 / ((X : ℝ) * (P : ℝ)) + 16 / ((X : ℝ) * (P : ℝ))
      = 32 / ((X : ℝ) * (P : ℝ)) := by ring
  linarith

/-! ## §4 — ⟦THE ENDPOINT TWIN, DIRECT `L²`⟧

The fused family at §3's route.  The fused fibre over `n ≠ X` is §3's fibre VERBATIM (a
pair with `p·m = X` forces `n = X`, so off `X` the `∨`-filter's second disjunct is empty),
and at `n = X` the fused fibre still injects into `X.primeFactors`
(`ramP2domEndMR_fiber_card_le_omega` — the injection never read `p ∣ m`).  So the whole
endpoint cost is ONE term:

  `Σ ‖ramP2coeffEndMR n‖²/n² ≤ 16/(X·P) + 32/(X·P²) + 4·(log₂(2X))²/X²`,

i.e. the direct grade plus `M4ErrRewire.endMass`-genre mass, BYTE-IDENTICAL to the landed
fused stone's endpoint half (`4·(log₂(2X))²/X²`).  At `4 ≤ P` this is
`24/(X·P) + 4·(log₂(2X))²/X²`, and the row's `1.5×` slot absorbs the second summand exactly
when `(log₂(2X))²·P ≤ 3X` — the ⟦NEW ABSORPTION GATE⟧, `M4RowMR.logbsq_two_mul_P_le`. -/

/-- Off the endpoint `n ≠ X`, the fused fibre IS the landed one. -/
private lemma ramP2domEndMR_fiber_subset {N X P Q n : ℕ} (hn : n ≠ X) :
    (ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)
      ⊆ (ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n) := by
  classical
  intro σ hσ
  obtain ⟨hdom, heq⟩ := Finset.mem_filter.mp hσ
  rw [ramP2domEndMR, Finset.mem_sigma] at hdom
  obtain ⟨hp, hm⟩ := hdom
  obtain ⟨hmem, hor⟩ := Finset.mem_filter.mp hm
  have hdvd : σ.1 ∣ σ.2 := by
    rcases hor with h | h
    · exact h
    · exact absurd (by rw [← heq, h] : n = X) hn
  refine Finset.mem_filter.mpr ⟨?_, heq⟩
  rw [ramP2domMR, Finset.mem_sigma]
  exact ⟨hp, Finset.mem_filter.mpr ⟨hmem, hdvd⟩⟩

/-- The fused `p²` coefficient vanishes above the window. -/
private lemma ramP2coeffEndMR_eq_zero_of_gt {N X P Q : ℕ} {n : ℕ} (hn : 2 * X < n)
    (a b c : ℕ → ℂ) : ramP2coeffEndMR N X P Q a b c n = 0 := by
  classical
  have hemp : (ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro σ hσ
    obtain ⟨hdom, heq⟩ := Finset.mem_filter.mp hσ
    obtain ⟨-, hhi⟩ := mem_ramP2domEndMR_window hdom
    have hcast : ((σ.1 * σ.2 : ℕ) : ℝ) = (σ.1 : ℝ) * (σ.2 : ℝ) := by push_cast; ring
    have hle : ((n : ℕ) : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by
      rw [← heq, hcast]; push_cast; exact hhi
    have : n ≤ 2 * X := by exact_mod_cast hle
    omega
  rw [ramP2coeffEndMR, hemp, Finset.sum_empty]

/-- **⟦THE FUSED `p²`-MASS STONE, DIRECT `L²`⟧** (`ramP2massEndMR_L2`).  The raw form:

  `Σ_{n ≤ N} ‖ramP2coeffEndMR n‖²/n² ≤ 16/(X·P) + 32/(X·P²) + 4·(log₂(2X))²/X²` . -/
theorem ramP2massEndMR_L2 (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 16 / ((X : ℝ) * (P : ℝ)) + 32 / ((X : ℝ) * (P : ℝ) ^ 2)
        + 4 * (Real.logb 2 (2 * (X : ℝ))) ^ 2 / (X : ℝ) ^ 2 := by
  classical
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (X : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  -- the universal term bound, at the fused domain
  have hstep : ∀ n : ℕ, ‖ramP2coeffEndMR N X P Q a b c n‖
      ≤ 2 * (((ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)).card : ℝ) := by
    intro n
    rw [ramP2coeffEndMR]
    refine (norm_sum_le _ _).trans ?_
    have h := Finset.sum_le_sum (f := fun σ : Σ _ : ℕ, ℕ =>
        ‖(ramareWeight P Q σ.1 σ.2 : ℂ) * a (σ.1 * σ.2)
          - b σ.2 * c σ.1 * ((blockOmega P Q σ.2 : ℂ) + 1)⁻¹‖)
      (g := fun _ : Σ _ : ℕ, ℕ => (2 : ℝ))
      (s := (ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n))
      (fun σ _ => ramP2_term_norm_le ha hb hc σ.1 σ.2)
    rw [Finset.sum_const, nsmul_eq_mul] at h
    linarith
  -- ⟦STEP 1⟧ truncate at `2X`
  have hsub : Finset.Icc 1 (2 * X) ⊆ Finset.Icc 1 N := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    omega
  have htrunc : (∑ n ∈ Finset.Icc 1 (2 * X),
        ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
      = ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 := by
    refine Finset.sum_subset hsub (fun n hn hnot => ?_)
    rw [Finset.mem_Icc] at hn
    have hgt : 2 * X < n := by
      by_contra hcon
      exact hnot (Finset.mem_Icc.mpr ⟨hn.1, by omega⟩)
    rw [ramP2coeffEndMR_eq_zero_of_gt hgt a b c, norm_zero]
    simp
  -- ⟦STEP 2⟧ peel the endpoint `n = X`
  have hXmem : X ∈ Finset.Icc 1 (2 * X) := by
    rw [Finset.mem_Icc]
    omega
  have hpeel := Finset.add_sum_erase (Finset.Icc 1 (2 * X))
    (fun n => ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2) hXmem
  -- the endpoint term: the fused fibre still injects into `X.primeFactors`
  have hend : ‖ramP2coeffEndMR N X P Q a b c X‖ ^ 2 / (X : ℝ) ^ 2
      ≤ 4 * (Real.logb 2 (2 * (X : ℝ))) ^ 2 / (X : ℝ) ^ 2 := by
    have hcard : ((((ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = X)).card : ℕ) : ℝ)
        ≤ (X.primeFactors.card : ℝ) := by
      exact_mod_cast ramP2domEndMR_fiber_card_le_omega (N := N) (X := X) (P := P) (Q := Q)
        (by omega)
    have homega : (X.primeFactors.card : ℝ) ≤ Real.logb 2 (2 * (X : ℝ)) := by
      have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      rw [Real.logb, le_div_iff₀ hl2]
      exact le_trans (omegaMR_mul_log_two_le hX) (Real.log_le_log hX0 (by linarith))
    have hnorm : ‖ramP2coeffEndMR N X P Q a b c X‖ ≤ 2 * Real.logb 2 (2 * (X : ℝ)) := by
      have := hstep X
      linarith
    have hnn : (0 : ℝ) ≤ ‖ramP2coeffEndMR N X P Q a b c X‖ := norm_nonneg _
    have hnum : ‖ramP2coeffEndMR N X P Q a b c X‖ ^ 2
        ≤ 4 * (Real.logb 2 (2 * (X : ℝ))) ^ 2 := by nlinarith
    gcongr
  -- the off-endpoint terms: §3's fibre, verbatim
  have hoff : ∀ n ∈ (Finset.Icc 1 (2 * X)).erase X,
      ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ 4 * ((ramP2fibreMR P Q n).card : ℝ) ^ 2 / (X : ℝ) ^ 2 := by
    intro n hn
    have hne : n ≠ X := Finset.ne_of_mem_erase hn
    have hmem : n ∈ Finset.Icc 1 (2 * X) := Finset.mem_of_mem_erase hn
    rw [Finset.mem_Icc] at hmem
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hmem.1
    -- the fused fibre sits inside the landed one
    have hcardsub : (((ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)).card : ℝ)
        ≤ ((ramP2fibreMR P Q n).card : ℝ) := by
      have h1 := Finset.card_le_card (ramP2domEndMR_fiber_subset (N := N) (X := X) (P := P)
        (Q := Q) (n := n) hne)
      have h2 := ramP2domMR_fiber_card_le_p2 (N := N) (X := X) (P := P) (Q := Q) (n := n)
      exact_mod_cast le_trans h1 h2
    rcases Finset.eq_empty_or_nonempty
        ((ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n)) with hempty | ⟨σ, hσ⟩
    · have hz : ramP2coeffEndMR N X P Q a b c n = 0 := by
        rw [ramP2coeffEndMR, hempty, Finset.sum_empty]
      rw [hz, norm_zero]
      have h0 : (0 : ℝ) ≤ 4 * ((ramP2fibreMR P Q n).card : ℝ) ^ 2 / (X : ℝ) ^ 2 := by
        positivity
      simpa using h0
    · obtain ⟨hdom, hfib⟩ := Finset.mem_filter.mp hσ
      obtain ⟨hlo, -⟩ := mem_ramP2domEndMR_window hdom
      have hcast : ((σ.1 * σ.2 : ℕ) : ℝ) = (σ.1 : ℝ) * (σ.2 : ℝ) := by push_cast; ring
      have hnlo : (X : ℝ) ≤ (n : ℝ) := by rw [← hfib, hcast]; exact hlo
      have hnorm : ‖ramP2coeffEndMR N X P Q a b c n‖
          ≤ 2 * ((ramP2fibreMR P Q n).card : ℝ) := by
        have := hstep n
        linarith
      have hnn : (0 : ℝ) ≤ ‖ramP2coeffEndMR N X P Q a b c n‖ := norm_nonneg _
      have hnum : ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2
          ≤ 4 * ((ramP2fibreMR P Q n).card : ℝ) ^ 2 := by nlinarith
      have hden : (X : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
      calc ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
          ≤ 4 * ((ramP2fibreMR P Q n).card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by gcongr
        _ ≤ 4 * ((ramP2fibreMR P Q n).card : ℝ) ^ 2 / (X : ℝ) ^ 2 := by
            gcongr
  -- ⟦STEP 3⟧ assemble
  rw [← htrunc, ← hpeel]
  have hoffsum : (∑ n ∈ (Finset.Icc 1 (2 * X)).erase X,
        ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ 16 / ((X : ℝ) * (P : ℝ)) + 32 / ((X : ℝ) * (P : ℝ) ^ 2) := by
    refine le_trans (Finset.sum_le_sum hoff) ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun n _ _ => by positivity)) ?_
    exact sum_fibre_sq_price X P Q hX hP
  linarith

/-- **⟦THE FUSED `p²`-MASS STONE, `24/(X·P)`⟧** (`ramP2massEndMR_L2_direct`) — the R1 grade
of the FUSED row, at the `4 ≤ P` floor:

  `Σ_{n ≤ N} ‖ramP2coeffEndMR n‖²/n² ≤ 24/(X·P) + 4·(log₂(2X))²/X²` .

The endpoint summand is BYTE-IDENTICAL to `ramP2massEndMR_direct`'s; only the main grade
moves (`16·log₂(2X)/(X·P) → 24/(X·P)`).  The row's `1.5×` slot (`four_rows_le_end`) absorbs
it exactly when `(log₂(2X))²·P ≤ 3X`. -/
theorem ramP2massEndMR_L2_direct (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hP : 4 ≤ P)
    (a b c : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 24 / ((X : ℝ) * (P : ℝ))
        + 4 * (Real.logb 2 (2 * (X : ℝ))) ^ 2 / (X : ℝ) ^ 2 := by
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hP4 : (4 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < (P : ℝ) := by linarith
  refine (ramP2massEndMR_L2 N X P Q hX hN (by omega) a b c ha hb hc).trans ?_
  have hmain : 16 / ((X : ℝ) * (P : ℝ)) + 32 / ((X : ℝ) * (P : ℝ) ^ 2)
      ≤ 24 / ((X : ℝ) * (P : ℝ)) := by
    have hoff : 32 / ((X : ℝ) * (P : ℝ) ^ 2) ≤ 8 / ((X : ℝ) * (P : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hX0.le hP0.le) (by linarith : (0 : ℝ) ≤ (P : ℝ) - 4)]
    have hid : 16 / ((X : ℝ) * (P : ℝ)) + 8 / ((X : ℝ) * (P : ℝ))
        = 24 / ((X : ℝ) * (P : ℝ)) := by ring
    linarith
  linarith

end Salt.MR

end
