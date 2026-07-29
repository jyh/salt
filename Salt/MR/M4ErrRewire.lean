/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SeamRowWindowed
import Salt.MR.SmallStones
import Salt.MR.M4Sieve

/-!
# `M4ErrRewire` — ⟦THE WALL⟧'s `p²` stone and the `hwin`-free `E` row

Design: `docs/exploration/m4-residue-design-0728.md`, Part W (v2's `W1` verdict supersedes
v1's text).  Flags: "THE JOIN lands as an honest prefix", ⟦THE WALL⟧.

**THE WALL.**  `FrameWitness.err_at_witness` reaches `A2Frame3.err` through
`USetResiduals.E_priced_row_scale`, whose `p²`-mass slot is
`SeamCalibrationK.ramP2mass_direct` — and *that* stone reads the JOINT-SUPPORT binder

  `hwin : ∀ p m, p prime → P ≤ p → p ≤ Q → c p · b m ≠ 0 → X_d ≤ pm ≤ 2X_d`.

`M4Seam.m4_row_cf_block_eq_zero` is the kernel witness that `hwin` alone collapses the
capstone's datum: at `m = 1` it forces `c P = 0` at every block prime below the window.  The
window LAW is therefore uninhabitable by the door's `P`-exact sieved `λχ̄`, and no
relativization of `hwin` helps (`SeamRowWindowed` §1: relativizing a joint-support claim is
vacuous).

**THE REWIRE.**  `RamareMR` already retired `hwin` on the *identity* side by moving the
cofactor range to MR's own `ramHonMR N X p = {m : X ≤ pm ≤ 2X}` — the window lives IN THE
INDEX SET.  `SeamRowWindowed.ramErr_moment_split_mr_windowed` decomposes the SAME `ramErr`
object with neither `hwin` nor the unrestricted `hcoef`, at the relativized pair `SeamCoefW`.
What was missing is the ONE stone below: the sharp `p²` mass at `ramP2domMR`, i.e.
`ramP2mass_direct`'s `16·log₂(2X)/(X·P)` grade with the window read off the index set instead
of off `hwin`.  §1 lands it; §2 assembles the `hwin`-free `E` row at the split's prefactor
`4`; §3 records the door datum's inhabitation of the surviving binder set.

## §1's two halves (`ramP2mass_direct`'s own route, `Σf² ≤ (max f)(Σ f)`)

* the **max** half `‖coeff_n‖/n ≤ 2·log₂(2X)/X`: off the fibre the coefficient is `0`, and on
  it the window comes from `ramHonMR` membership (`mem_ramP2domMR_window`), so `X ≤ n ≤ 2X`;
  the fibre has `≤ ω(n) ≤ log₂(2X)` points and each term has norm `≤ 2`
  (`SmallStones.ramP2_term_norm_le` — the unconditional bound, no `hwin`);
* the **Σ** half `Σ_n ‖coeff_n‖/n ≤ 8/P`: `SmallStones.ramP2mass_le`'s own ledger, stopped
  one step before its lossy `Σf² ≤ (Σf)²`.

The product is `16·log₂(2X)/(X·P)` — `ramP2mass_direct`'s grade verbatim, with `hwin` gone.

Three of `SmallStones`' helpers on the `Σ` side (`card_ramP2_cofactors_le`,
`ramP2_inner_row_le`, `ramP2_dom_sum_le`) are `private` there, so they are re-derived here
verbatim; this is `SeamCalibrationK`'s own precedent for `TypicalPrice`'s privates.

## §2's grade arithmetic (the refuter's page)

The windowed split pays `4` where `USetResiduals.ramErr_moment_split` pays `3`, and the two
seam rows collapse to `RamareMR.seam_rows_grade`'s `520·(T/X+1)/H` instead of the unwindowed
`720·(T/X+1)/H`.  Against `A2Frame3.err`'s standing right-hand side:

  `4·520 = 2080  ≤  2160 = 3·720`,

so the seam half fits with `80·(T/X+1)/H` to spare, and the `p²` half fits at the cost of a
`4/3` inflation of the `EP2` slot (`FrameWitness.witEP2`) — which is what the frame's four
`witEP2` sites now carry.  Nothing in `A2Frame3` moves.
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

/-! ## §2 — THE `hwin`-FREE `E` ROW -/

/-- **THE WINDOWED `E` ROW** (`E_priced_mr`).  `USetResiduals.E_priced`'s twin through
`SeamRowWindowed.ramErr_moment_split_mr_windowed`:

  `∫_{−T}^{T} ‖ramErr‖² ≤ 4·(520·(T/X_d + 1)/H + (2T+20N)·16·log₂(2X_d)/(X_d·P))`.

Three changes against `E_priced`, all in the honest direction:

* `hcoef` (unsatisfiable at the S8 datum, `ThmA2Spine.seam_coef_contract_absurd`) becomes
  the relativized `SeamCoefW`;
* **`hwin` is GONE** — MR's cofactor range carries the window, and the `p²` mass is priced by
  §1's `ramP2massMR_direct`;
* the Cauchy–Schwarz prefactor is the four-row split's `4` in place of the three-row `3`, and
  MR's SECOND seam window is paid explicitly inside `RamareMR.seam_rows_grade`'s `520`. -/
theorem E_priced_mr (H : ℝ) (hH : 2 ≤ H) (N Xd P Q : ℕ) (hXd : 1 ≤ Xd) (hN : 2 * Xd ≤ N)
    (hN2 : (N : ℝ) ≤ 2 * (Xd : ℝ)) (hHX : H ≤ (Xd : ℝ)) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoefW : SeamCoefW Xd P Q a b c)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (Xd : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (Xd : ℝ))
    -- ⟦R3a — THE TAIL IS PRICED, NOT PINNED⟧ `homega` (the single-`P` support pin,
    -- unsatisfiable at the door's band datum) is replaced by the coprime-tail MASS
    (Mtail : ℝ)
    (hMtail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramErr H N Xd P Q a b c t‖ ^ 2)
      ≤ 4 * (520 * (T / (Xd : ℝ) + 1) / H
          + (2 * T + 20 * (N : ℝ))
              * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))
          + (2 * T + 20 * (N : ℝ)) * Mtail) := by
  have hsplit := ramErr_moment_split_mr_windowed H hH N Xd P Q hXd hN hP a b c hcoefW
    hasupp T hT
  have h1 := ramSeamLoPoly_moment H hH N Xd P Q hXd hN hP b c hb hc T hT
  have h2 := ramSeamUpPoly_moment H hH N Xd P Q hXd hP b c hb hc T hT
  have h3 := ramP2corrMR_moment N Xd P Q hXd hN a b c T
  have h4 := ramCopTail_moment N P Q a T
  have hgrade := seam_rows_grade H hH N Xd hXd hN2 hHX T hT
  have hmass := ramP2massMR_direct N Xd P Q hXd hN hP a b c ha hb hc
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hfac : (0 : ℝ) ≤ 2 * T + 20 * (N : ℝ) := by linarith
  have hp2 : (∫ t in (-T)..T, ‖ramP2corrMR N Xd P Q a b c t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ))
          * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))) :=
    h3.trans (mul_le_mul_of_nonneg_left hmass hfac)
  have htail : (∫ t in (-T)..T, ‖ramCopTail N P Q a t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * Mtail :=
    h4.trans (mul_le_mul_of_nonneg_left hMtail hfac)
  linarith

/-- **THE WINDOWED `E` ROW AT THE ROW SCALE** (`E_priced_mr_row_scale`).
`USetResiduals.E_priced_row_scale`'s move, verbatim: the row's `T/X` grade is read at the
REAL scale `X`, the seam row at the DYADIC scale `X_d`, and the two meet under `X ≤ X_d`
(⟦V4⟧'s law — stated separately so the mismatch is visible). -/
theorem E_priced_mr_row_scale (H : ℝ) (hH : 2 ≤ H) (N Xd P Q : ℕ) (hXd : 1 ≤ Xd)
    (hN : 2 * Xd ≤ N) (hN2 : (N : ℝ) ≤ 2 * (Xd : ℝ)) (hHX : H ≤ (Xd : ℝ)) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ) (hcoefW : SeamCoefW Xd P Q a b c)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (Xd : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (Xd : ℝ))
    (Mtail : ℝ)
    (hMtail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail)
    (T X : ℝ) (hT : 0 ≤ T) (hX0 : 0 < X) (hXdX : X ≤ (Xd : ℝ)) :
    (∫ t in (-T)..T, ‖ramErr H N Xd P Q a b c t‖ ^ 2)
      ≤ 4 * (520 * (T / X + 1) / H
          + (2 * T + 20 * (N : ℝ))
              * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))
          + (2 * T + 20 * (N : ℝ)) * Mtail) := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hscale : T / (Xd : ℝ) ≤ T / X := div_le_div_of_nonneg_left hT hX0 hXdX
  have hrow : 520 * (T / (Xd : ℝ) + 1) / H ≤ 520 * (T / X + 1) / H := by
    have h1 : 520 * (T / (Xd : ℝ) + 1) ≤ 520 * (T / X + 1) := by linarith
    rw [div_le_div_iff_of_pos_right hH0]
    exact h1
  refine (E_priced_mr H hH N Xd P Q hXd hN hN2 hHX hP a b c hcoefW ha hb hc hasupp Mtail
    hMtail T hT).trans ?_
  linarith

/-- **THE GRADE FIT** (`err_grade_fit`).  The arithmetic behind the rewire, isolated so that
the refuter's page is a Lean object: the windowed row's `4·(520·g + E′)` sits under
`A2Frame3.err`'s standing `3·(720·g + E)` as soon as the `EP2` slot carries the `4/3`
inflation `4·E′ ≤ 3·E`.  The seam half is `4·520 = 2080 ≤ 2160 = 3·720`, with
`80·g/H` to spare. -/
theorem err_grade_fit {g H Ep Ep' : ℝ} (hg : 0 ≤ g) (hH : 0 < H)
    (hE : 4 * Ep' ≤ 3 * Ep) :
    4 * (520 * g / H + Ep') ≤ 3 * (720 * g / H + Ep) := by
  have hgH : 0 ≤ g / H := div_nonneg hg hH.le
  have h1 : 4 * (520 * g / H) ≤ 3 * (720 * g / H) := by
    have : 520 * g / H = 520 * (g / H) := by ring
    rw [this]
    have h2 : 720 * g / H = 720 * (g / H) := by ring
    rw [h2]
    linarith
  linarith

/-! ## §3 — THE DOOR DATUM INHABITS THE SURVIVING BINDER SET

⟦THE WALL⟧'s second half.  With `hwin` gone the err chain's coefficient demand is exactly

  `SeamCoefW X_d P P a b cf`  +  `‖a‖, ‖b‖, ‖cf‖ ≤ 1`  +  `hasupp`  +  `hsupp`,

and the design's factorization of the door's sieved `λχ̄` window datum meets it — at EVERY
cofactor `m`, INCLUDING `P ∣ m` and including `m = 1` (the point at which the old `hwin`
collapsed the datum, `M4Seam.m4_row_cf_block_eq_zero`).  The reason is complete
multiplicativity: `λ` factors with NO coprimality (`M4Residue.liouvilleC_mul`) and `χ̄` is a
`MulChar`, so the sieve indicator and the phase are the only non-multiplicative pieces — and
both are absorbed into the COFACTOR slot, where the phase reads at the dilated frequency
`αP` and the indicator at the shifted argument `P·m`.

**THE RESIDUE THIS SECTION EXPOSES.**  `CapFreeArm3.A2Frame3.err` pins the cofactor slot to
`ellLin g` (the completely multiplicative extension of the row's own `g`), and the row leg
needs it there.  `doorCofactor` below is NOT of that shape — it carries `1_𝒮(P·)` and the
phase.  So the surviving obstruction to instantiating the capstone at the door datum is the
frame's `b`-SLOT PIN, not the window law: `A2Frame3.err`'s `ellLin g` must become a free
`1`-bounded `b` before `m4_meansq_per_chi_gen`'s err-side binders can be re-stated at it.
That statement lives in `CapFreeArm3`, outside this wave's authorization. -/

/-- The unimodular door phase (`M4Window.norm_exp_phase`, which is `private` there). -/
private lemma normMR_exp_phase (β : ℝ) (k : ℕ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * ((k : ℕ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * ((k : ℕ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- **`λχ̄` IS COMPLETELY MULTIPLICATIVE.**  `liouvilleC_mul` (no coprimality) and `χ`'s
`MulChar` law, composed through the conjugation ring hom. -/
theorem liouChi_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (m n : ℕ) :
    liouChi χ (m * n) = liouChi χ m * liouChi χ n := by
  unfold liouChi
  rw [liouvilleC_mul]
  have hcast : ((m * n : ℕ) : ZMod q) = (m : ZMod q) * (n : ZMod q) := by push_cast; ring
  rw [hcast, map_mul, map_mul]
  ring

/-- **THE DOOR'S WINDOW DATUM** at frequency `α`: the sieved `λχ̄`, phased.  This is the
coefficient sequence `M4Door`/`M4BridgePhase` hand the mean-square obligation. -/
noncomputable def doorDatum {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J : ℕ) (α : ℝ) : ℕ → ℂ :=
  fun n => memSCoeff Pseq Qseq J (liouChi χ) n
    * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((n : ℕ) : ℂ))

/-- **THE DOOR'S COFACTOR SLOT AT THE BLOCK PIN `P`**: the sieve indicator read at `P·m`,
the cofactor's own `λχ̄`, and the phase at the DILATED frequency `αP`. -/
noncomputable def doorCofactor {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J P : ℕ) (α : ℝ) : ℕ → ℂ :=
  fun m => (if MemS Pseq Qseq J (P * m) then (1 : ℂ) else 0) * liouChi χ m
    * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((α * (P : ℝ) : ℝ) : ℂ) * ((m : ℕ) : ℂ))

/-- **THE DOOR DATUM FACTORIZES — AT EVERY `m`.**  `a(P·m) = b(m)·cf(P)` with
`cf = λχ̄` and `b = doorCofactor`, with NO coprimality, NO window restriction, and no
exception at `m = 1`. -/
theorem doorDatum_factorizes {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J P : ℕ) (α : ℝ) (m : ℕ) :
    doorDatum χ Pseq Qseq J α (P * m)
      = doorCofactor χ Pseq Qseq J P α m * liouChi χ P := by
  have hphase : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (((P * m : ℕ)) : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((α * (P : ℝ) : ℝ) : ℂ)
          * ((m : ℕ) : ℂ)) := by
    congr 1
    push_cast
    ring
  simp only [doorDatum, doorCofactor, memSCoeff]
  rw [hphase]
  split_ifs with hS
  · rw [liouChi_mul]; ring
  · ring

/-- `doorCofactor` is `1`-bounded. -/
theorem norm_doorCofactor_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J P : ℕ) (α : ℝ) (m : ℕ) : ‖doorCofactor χ Pseq Qseq J P α m‖ ≤ 1 := by
  rw [doorCofactor, norm_mul, norm_mul, normMR_exp_phase, mul_one]
  have hχ := norm_liouChi_le_one χ m
  split_ifs with hS
  · rw [norm_one, one_mul]; exact hχ
  · rw [norm_zero, zero_mul]; norm_num

/-- `doorDatum` is `1`-bounded. -/
theorem norm_doorDatum_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J : ℕ) (α : ℝ) (n : ℕ) : ‖doorDatum χ Pseq Qseq J α n‖ ≤ 1 := by
  rw [doorDatum, norm_mul, normMR_exp_phase, mul_one]
  exact norm_memSCoeff_le_one (norm_liouChi_le_one χ) Pseq Qseq J n

/-- **THE DOOR DATUM SATISFIES THE RELATIVIZED PAIR LAW** at the block pin `P = Q`, at any
dyadic scale `X_d` — the window antecedents are simply not used, because the factorization
is unconditional. -/
theorem doorDatum_seamCoefW {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J P Xd : ℕ) (α : ℝ) :
    SeamCoefW Xd P P (doorDatum χ Pseq Qseq J α) (doorCofactor χ Pseq Qseq J P α)
      (liouChi χ) := by
  intro p m _ hPp hpP _ _ _
  have hpe : p = P := le_antisymm hpP hPp
  subst hpe
  exact doorDatum_factorizes χ Pseq Qseq J p α m

/-- **⟦THE INHABITATION⟧** (`doorDatum_inhabits_err_binders`).  The whole coefficient side of
the rewired err chain — the three `1`-bounds and the relativized pair law — at the door's own
sieved, phased `λχ̄` datum.  Nothing here is conditional: no scale gate, no window, no
coprimality.  Compare `M4Seam.m4_row_cf_block_eq_zero`, which shows the PRE-rewire binder set
(with `hwin`) forces `cf P = 0` and so admits no such datum at all. -/
theorem doorDatum_inhabits_err_binders {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Pseq Qseq : ℕ → ℕ) (J P Xd : ℕ) (α : ℝ) :
    (∀ n, ‖doorDatum χ Pseq Qseq J α n‖ ≤ 1)
      ∧ (∀ m, ‖doorCofactor χ Pseq Qseq J P α m‖ ≤ 1)
      ∧ (∀ p, ‖liouChi χ p‖ ≤ 1)
      ∧ SeamCoefW Xd P P (doorDatum χ Pseq Qseq J α) (doorCofactor χ Pseq Qseq J P α)
          (liouChi χ) :=
  ⟨norm_doorDatum_le_one χ Pseq Qseq J α,
   norm_doorCofactor_le_one χ Pseq Qseq J P α,
   norm_liouChi_le_one χ,
   doorDatum_seamCoefW χ Pseq Qseq J P Xd α⟩

end Salt.MR
