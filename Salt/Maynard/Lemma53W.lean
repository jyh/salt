/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.Lemma53Tight

/-!
# Lemma 5.3 contraction — free-`(W', D)`, `|y| ≤ B` generalization (explicit12 W4-3)

This is a mechanical sweep of the tight `lemma53` contraction machinery
(`Salt/Maynard/Lemma53Tight.lean`, `Salt/Maynard/Lemma53.lean`,
`Salt/Maynard/EulerTailL.lean`) to a free modulus `W'` and free cutoff `D`
(replacing the pinned `W k` / `D₀ k`), with the `|y| ≤ 1` hypothesis widened to
`|y| ≤ B` for an arbitrary `B ≥ 0` (the whole error bound scales by `B`).

The heart (`yM`, `lamPhiContractM`, `lamPhiContractM_collapse`, `sigmaMuKpin`,
`s2_diag_lam_restricted`) is already free-`W` and reused unchanged.  The pinned
STEPS are the strict-prime fact (`D_lt_of_prime_dvd_coordW`, collision
convention `D < p`) and the Euler tail (`euler_tail_LW`).

The landed `*` lemmas are left byte-identical; these are PARALLEL `*W` names.
The private helpers of the landed modules (`inv_sq_tele`, `prod_one_add_le`,
`moebius_sq_one'`, `g_factor_prod'`, `gr_ratio_mem'`, `inv_sq_tele53`,
`one_sub_sum_le_prod_one_sub`, `abs_prod_one_sub_le`) are NOT accessible across
the module boundary, so — exactly as `Lemma53Tight.lean` re-declares its own
`moebius_sq_one'`/`g_factor_prod'`/… — we re-declare local private copies here.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-! ## Local private copies of the landed private helpers

These are byte-identical copies of the same-named `private` lemmas in
`EulerTailL.lean`/`Lemma53Tight.lean`/`Lemma53.lean`.  `private` declarations
are not accessible across module boundaries in Lean 4, so — following the
established precedent of `Lemma53Tight.lean` re-declaring its own copies — we
re-declare them locally.  They are `W`/`D`-free (pure real analysis). -/

/-- Telescoping tail bound (local copy of `EulerTailL.inv_sq_tele`). -/
private theorem inv_sq_tele (a : ℕ) (ha : 2 ≤ a) :
    ∀ b : ℕ, a ≤ b →
      (∑ n ∈ Finset.Icc (a + 1) b, (((n : ℝ) - 1)⁻¹) ^ 2)
        ≤ ((a : ℝ) - 1)⁻¹ - ((b : ℝ) - 1)⁻¹ := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp
  | succ b hab ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast le_trans ha hab
      have hstep : (((b + 1 : ℕ) : ℝ) - 1)⁻¹ ^ 2
          ≤ ((b : ℝ) - 1)⁻¹ - (((b + 1 : ℕ) : ℝ) - 1)⁻¹ := by
        push_cast
        have h1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
        have h2 : (0 : ℝ) < (b : ℝ) := by linarith
        rw [show ((b : ℝ) + 1 - 1) = (b : ℝ) by ring, ← sub_nonneg]
        have hexp : ((b : ℝ) - 1)⁻¹ - (b : ℝ)⁻¹ - ((b : ℝ)⁻¹) ^ 2
            = (((b : ℝ)) ^ 2 * ((b : ℝ) - 1))⁻¹ := by
          field_simp
          ring
        rw [hexp]
        have hposm : (0 : ℝ) < ((b : ℝ)) ^ 2 * ((b : ℝ) - 1) := by nlinarith
        exact inv_nonneg.mpr hposm.le
      linarith [ih]

/-- Product-versus-sum bound (local copy of `EulerTailL.prod_one_add_le`). -/
private theorem prod_one_add_le {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ x ∈ s, 0 ≤ a x) (hs : ∑ x ∈ s, a x ≤ 1 / 2) :
    ∏ x ∈ s, (1 + a x) ≤ 1 + 2 * ∑ x ∈ s, a x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx]
      have hax : 0 ≤ a x := ha x (Finset.mem_insert_self x s)
      have has : ∀ z ∈ s, 0 ≤ a z := fun z hz =>
        ha z (Finset.mem_insert_of_mem hz)
      have hsum_nonneg : 0 ≤ ∑ z ∈ s, a z := Finset.sum_nonneg has
      have hss : ∑ z ∈ s, a z ≤ 1 / 2 := by
        rw [Finset.sum_insert hx] at hs
        linarith
      have hih := ih has hss
      have hprod_nonneg : (0 : ℝ) ≤ ∏ z ∈ s, (1 + a z) :=
        Finset.prod_nonneg fun z hz => by linarith [has z hz]
      nlinarith [hih, hax, hss, hsum_nonneg]

/-- `μ(n)² = 1` for squarefree `n` (local copy of `Lemma53Tight.moebius_sq_one'`). -/
private theorem moebius_sq_one' {n : ℕ} (hn : Squarefree n) :
    ((μ n : ℤ) : ℝ) ^ 2 = 1 := by
  have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hn
  have hc : ((μ n : ℤ) : ℝ) ^ 2 = (((μ n) ^ 2 : ℤ) : ℝ) := by push_cast; ring
  rw [hc, h]; norm_num

/-- Per-coordinate factorization (local copy of `Lemma53Tight.g_factor_prod'`). -/
private theorem g_factor_prod' {r : ℕ} (hr : Squarefree r)
    (hodd : ∀ p ∈ r.primeFactors, 3 ≤ p) :
    (gMult r : ℝ) * (r : ℝ) / (Nat.totient r : ℝ) ^ 2
      = ∏ p ∈ r.primeFactors, (1 - (((p : ℝ) - 1)⁻¹) ^ 2) := by
  have hrprod : (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
  rw [gMult_cast hodd, hrprod, totient_squarefree_cast hr,
    ← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `g(ρ)·ρ/φ(ρ)² ∈ [0,1]` (local copy of `Lemma53Tight.gr_ratio_mem'`). -/
private theorem gr_ratio_mem' {ρ : ℕ} (hρ : Squarefree ρ)
    (hodd : ∀ p ∈ ρ.primeFactors, 3 ≤ p) :
    0 ≤ (gMult ρ : ℝ) * (ρ : ℝ) / (Nat.totient ρ : ℝ) ^ 2
      ∧ (gMult ρ : ℝ) * (ρ : ℝ) / (Nat.totient ρ : ℝ) ^ 2 ≤ 1 := by
  rw [g_factor_prod' hρ hodd]
  refine ⟨Finset.prod_nonneg (fun p hp => ?_),
    Finset.prod_le_one (fun p hp => ?_) (fun p hp => ?_)⟩
  · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
    have h0 : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    have h1 : ((p : ℝ) - 1)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; linarith
    nlinarith [h0, h1]
  · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
    have h0 : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    have h1 : ((p : ℝ) - 1)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; linarith
    nlinarith [h0, h1]
  · nlinarith [sq_nonneg (((p : ℝ) - 1)⁻¹)]

/-- Telescoping tail bound (local copy of `Lemma53.inv_sq_tele53`). -/
private theorem inv_sq_tele53 (a : ℕ) (ha : 2 ≤ a) :
    ∀ b : ℕ, a ≤ b →
      (∑ n ∈ Finset.Icc (a + 1) b, (((n : ℝ) - 1)⁻¹) ^ 2)
        ≤ ((a : ℝ) - 1)⁻¹ - ((b : ℝ) - 1)⁻¹ := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp
  | succ b hab ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast le_trans ha hab
      have hstep : (((b + 1 : ℕ) : ℝ) - 1)⁻¹ ^ 2
          ≤ ((b : ℝ) - 1)⁻¹ - (((b + 1 : ℕ) : ℝ) - 1)⁻¹ := by
        push_cast
        have h1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
        rw [show ((b : ℝ) + 1 - 1) = (b : ℝ) by ring, ← sub_nonneg]
        have hexp : ((b : ℝ) - 1)⁻¹ - (b : ℝ)⁻¹ - ((b : ℝ)⁻¹) ^ 2
            = (((b : ℝ)) ^ 2 * ((b : ℝ) - 1))⁻¹ := by
          field_simp
          ring
        rw [hexp]
        have hposm : (0 : ℝ) < ((b : ℝ)) ^ 2 * ((b : ℝ) - 1) := by nlinarith
        exact inv_nonneg.mpr hposm.le
      linarith [ih]

/-- Weierstrass lower bound (local copy of `Lemma53.one_sub_sum_le_prod_one_sub`). -/
private theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ p ∈ s, 0 ≤ x p) (hx1 : ∀ p ∈ s, x p ≤ 1) :
    1 - ∑ p ∈ s, x p ≤ ∏ p ∈ s, (1 - x p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hxa0 : 0 ≤ x a := hx0 a (Finset.mem_insert_self a s)
      have hxa1 : x a ≤ 1 := hx1 a (Finset.mem_insert_self a s)
      have hx0' : ∀ p ∈ s, 0 ≤ x p := fun p hp => hx0 p (Finset.mem_insert_of_mem hp)
      have hx1' : ∀ p ∈ s, x p ≤ 1 := fun p hp => hx1 p (Finset.mem_insert_of_mem hp)
      have hih := ih hx0' hx1'
      have hpn : 0 ≤ ∏ p ∈ s, (1 - x p) :=
        Finset.prod_nonneg fun p hp => by linarith [hx1' p hp]
      have hsn : 0 ≤ ∑ p ∈ s, x p := Finset.sum_nonneg hx0'
      nlinarith [hih, hxa0, hxa1, hpn, hsn,
        mul_le_mul_of_nonneg_left hih (by linarith : (0 : ℝ) ≤ 1 - x a)]

/-- `|∏(1 − xₚ) − 1| ≤ ∑ xₚ` (local copy of `Lemma53.abs_prod_one_sub_le`). -/
private theorem abs_prod_one_sub_le {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ p ∈ s, 0 ≤ x p) (hx1 : ∀ p ∈ s, x p ≤ 1) :
    |(∏ p ∈ s, (1 - x p)) - 1| ≤ ∑ p ∈ s, x p := by
  have hle : ∏ p ∈ s, (1 - x p) ≤ 1 :=
    Finset.prod_le_one (fun p hp => by linarith [hx1 p hp])
      (fun p hp => by linarith [hx0 p hp])
  have hge := one_sub_sum_le_prod_one_sub s x hx0 hx1
  rw [abs_of_nonpos (by linarith)]
  linarith

/-! ## `euler_tail_LW` — the free-`D` `L`-weighted Euler tail

Port of `EulerTailL.euler_tail_L` with the `k` binder dropped and `D₀ k → D`
(the landed `k` occurs ONLY through `D₀ k`). -/

/-- **`euler_tail_LW`.** Free-`D` form of `euler_tail_L`. -/
theorem euler_tail_LW (M : ℕ) (L : ℝ) (D : ℕ) (hL : 1 ≤ L)
    (hD : 4 * L ≤ (D : ℝ)) :
    ∑ t ∈ ((Finset.range M).filter
        (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1,
      L ^ t.primeFactors.card * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2
      ≤ 4 * L / (D : ℝ) := by
  classical
  have hD4 : 4 ≤ D := by
    have h4 : (4 : ℝ) ≤ (D : ℝ) := le_trans (by linarith) hD
    exact_mod_cast h4
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have : 0 < D := by omega
    exact_mod_cast this
  have hLpos : 0 < L := by linarith
  set a : ℕ → ℝ := fun p => L * (((p : ℝ) - 1)⁻¹) ^ 2 with haDef
  have ha_nonneg : ∀ p, 0 ≤ a p := fun p => by positivity
  set SF := ((Finset.range M).filter
      (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1 with hSF
  set PP := (Finset.range M).filter (fun p => p.Prime ∧ D < p) with hPP
  have hterm : ∀ t ∈ SF,
      L ^ t.primeFactors.card
          * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2
        = ∏ p ∈ t.primeFactors, a p := by
    intro t _
    rw [haDef, Finset.prod_mul_distrib, Finset.prod_const]
  have hinj : Set.InjOn Nat.primeFactors ↑SF := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hSF, Finset.mem_erase, Finset.mem_filter] at hx hy
    have hx' := Nat.prod_primeFactors_of_squarefree hx.2.2.1
    rw [← hx', hxy, Nat.prod_primeFactors_of_squarefree hy.2.2.1]
  have hsub : SF.image Nat.primeFactors ⊆ PP.powerset.erase ∅ := by
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨t, ht, rfl⟩ := hS
    rw [hSF, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨hne1, htM, hsq, hbig⟩ := ht
    rw [Finset.mem_erase, Finset.mem_powerset]
    constructor
    · have ht2 : 1 < t := by
        rcases Nat.lt_or_ge t 2 with h | h
        · interval_cases t
          · exact absurd hsq not_squarefree_zero
          · exact absurd rfl hne1
        · omega
      have : t.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr ht2
      exact Finset.nonempty_iff_ne_empty.mp this
    · intro p hp
      rw [hPP, Finset.mem_filter, Finset.mem_range]
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ t := Nat.dvd_of_mem_primeFactors hp
      have ht0 : 0 < t := Nat.pos_of_ne_zero hsq.ne_zero
      exact ⟨lt_of_le_of_lt (Nat.le_of_dvd ht0 hpd) htM, hpp, hbig p hp⟩
  have hprodadd : ∏ p ∈ PP, (1 + a p)
      = ∑ S ∈ PP.powerset, ∏ p ∈ S, a p := by
    have h := Finset.prod_add (fun p => a p) (fun _ => (1 : ℝ)) PP
    simp only [Finset.prod_const_one, mul_one] at h
    rw [← h]
    exact Finset.prod_congr rfl fun p _ => by ring
  have hsplit : ∑ S ∈ PP.powerset.erase ∅, ∏ p ∈ S, a p
      = (∏ p ∈ PP, (1 + a p)) - 1 := by
    have h := Finset.sum_erase_add PP.powerset (fun S => ∏ p ∈ S, a p)
      (Finset.empty_mem_powerset PP)
    rw [Finset.prod_empty] at h
    rw [hprodadd]
    linarith
  have htailsum : ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2 ≤ 2 / (D : ℝ) := by
    have hPPsub : PP ⊆ Finset.Icc (D + 1) M := by
      intro p hp
      rw [hPP, Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_Icc]
      omega
    have hmono : ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2
        ≤ ∑ n ∈ Finset.Icc (D + 1) M, (((n : ℝ) - 1)⁻¹) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hPPsub fun n _ _ => by positivity
    rcases Nat.lt_or_ge M D with hM | hM
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty] at hmono
      exact le_trans hmono (by positivity)
    · have htele := inv_sq_tele D (by omega) M hM
      have hMinv : 0 ≤ ((M : ℝ) - 1)⁻¹ := by
        have hM2 : (2 : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast (by omega : 2 ≤ M)
        rw [inv_nonneg]
        linarith
      have hfrac : ((D : ℝ) - 1)⁻¹ ≤ 2 / (D : ℝ) := by
        have h1 : (0 : ℝ) < (D : ℝ) - 1 := by
          have : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD4
          linarith
        rw [inv_eq_one_div, div_le_div_iff₀ h1 hDpos]
        have : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD4
        linarith
      linarith
  have hasum : ∑ p ∈ PP, a p ≤ 1 / 2 := by
    have h1 : ∑ p ∈ PP, a p = L * ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2 := by
      simp only [haDef, Finset.mul_sum]
    rw [h1]
    have h2 : L * ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2 ≤ L * (2 / (D : ℝ)) :=
      mul_le_mul_of_nonneg_left htailsum hLpos.le
    have h3 : L * (2 / (D : ℝ)) ≤ 1 / 2 := by
      have heq : L * (2 / (D : ℝ)) = 2 * L / (D : ℝ) := by ring
      rw [heq, div_le_div_iff₀ hDpos (by norm_num : (0 : ℝ) < 2)]
      linarith
    linarith
  calc ∑ t ∈ SF, L ^ t.primeFactors.card
          * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2
      = ∑ t ∈ SF, ∏ p ∈ t.primeFactors, a p := Finset.sum_congr rfl hterm
    _ = ∑ S ∈ SF.image Nat.primeFactors, ∏ p ∈ S, a p := by
        have himg : ∑ S ∈ SF.image Nat.primeFactors, ∏ p ∈ S, a p
            = ∑ t ∈ SF, ∏ p ∈ t.primeFactors, a p := Finset.sum_image hinj
        rw [himg]
    _ ≤ ∑ S ∈ PP.powerset.erase ∅, ∏ p ∈ S, a p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun S _ _ =>
          Finset.prod_nonneg fun p _ => ha_nonneg p
    _ = (∏ p ∈ PP, (1 + a p)) - 1 := hsplit
    _ ≤ (1 + 2 * ∑ p ∈ PP, a p) - 1 := by
        have := prod_one_add_le PP a (fun p _ => ha_nonneg p) hasum
        linarith
    _ = 2 * ∑ p ∈ PP, a p := by ring
    _ ≤ 2 * (L * (2 / (D : ℝ))) := by
        have h1 : ∑ p ∈ PP, a p = L * ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2 := by
          simp only [haDef, Finset.mul_sum]
        rw [h1]
        have h2 := mul_le_mul_of_nonneg_left htailsum hLpos.le
        linarith
    _ = 4 * L / (D : ℝ) := by
        field_simp
        ring

/-! ## Tight `μ²/φ²` tail bounds via `euler_tail_LW` -/

/-- **`phiSq_tail_tightW`.** Free-`D` form of `phiSq_tail_tight`. -/
theorem phiSq_tail_tightW (M D : ℕ) (hD : 4 ≤ D) :
    ∑ c ∈ ((Finset.range M).filter
        (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D < p)).erase 1,
      ((μ c : ℤ) : ℝ) ^ 2 / (Nat.totient c : ℝ) ^ 2
      ≤ 4 / (D : ℝ) := by
  have hDR : 4 * (1 : ℝ) ≤ (D : ℝ) := by
    have : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  have heuler := euler_tail_LW M 1 D le_rfl hDR
  rw [show (4 : ℝ) * 1 / (D : ℝ) = 4 / (D : ℝ) by ring] at heuler
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun c hc => ?_))) heuler
  rw [Finset.mem_erase, Finset.mem_filter] at hc
  obtain ⟨-, -, hcsq, -⟩ := hc
  have hrhs : (∏ p ∈ c.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2) = ((Nat.totient c : ℝ) ^ 2)⁻¹ := by
    rw [Finset.prod_pow, Finset.prod_inv_distrib, ← totient_squarefree_cast hcsq, inv_pow]
  rw [one_pow, one_mul, hrhs, moebius_sq_one' hcsq, one_div]

/-- **`phiSq_dvd_ne_tightW`.** Free-`D` form of `phiSq_dvd_ne_tight`. -/
theorem phiSq_dvd_ne_tightW (R D : ℕ) (hD : 4 ≤ D)
    (ρ : ℕ) (_hρsq : Squarefree ρ) :
    ∑ x ∈ (Finset.range R).filter
        (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D < p) ∧ ρ ∣ x ∧ x ≠ ρ),
      1 / (Nat.totient x : ℝ) ^ 2
      ≤ (1 / (Nat.totient ρ : ℝ) ^ 2) * (4 / (D : ℝ)) := by
  classical
  set S := (Finset.range R).filter
      (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D < p) ∧ ρ ∣ x ∧ x ≠ ρ) with hSdef
  set T := ((Finset.range R).filter
      (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D < p)).erase 1 with hTdef
  have hxmem : ∀ x ∈ S, ρ ∣ x ∧ Squarefree x ∧ x < R
      ∧ (∀ p ∈ x.primeFactors, D < p) ∧ x ≠ ρ := by
    intro x hx
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hx
    exact ⟨hx.2.2.2.1, hx.2.1, hx.1, hx.2.2.1, hx.2.2.2.2⟩
  have hφfac : ∀ x ∈ S, (Nat.totient x : ℝ) = (Nat.totient ρ : ℝ) * (Nat.totient (x / ρ) : ℝ) := by
    intro x hx
    obtain ⟨hdvd, hxsq, _, _, _⟩ := hxmem x hx
    have hxeq : ρ * (x / ρ) = x := Nat.mul_div_cancel' hdvd
    have hcop : Nat.Coprime ρ (x / ρ) := by
      have hx' : Squarefree (ρ * (x / ρ)) := by rw [hxeq]; exact hxsq
      exact (Nat.squarefree_mul_iff.mp hx').1
    have hh := Nat.totient_mul hcop
    rw [hxeq] at hh
    rw [hh]; push_cast; ring
  have hinj : Set.InjOn (fun x => x / ρ) ↑S := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    obtain ⟨hdx, _⟩ := hxmem x hx
    obtain ⟨hdy, _⟩ := hxmem y hy
    have e1 : ρ * (x / ρ) = x := Nat.mul_div_cancel' hdx
    have e2 : ρ * (y / ρ) = y := Nat.mul_div_cancel' hdy
    simp only at hxy
    rw [← e1, ← e2, hxy]
  have himg : S.image (fun x => x / ρ) ⊆ T := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    obtain ⟨hdvd, hxsq, hxR, hxp, hxne⟩ := hxmem x hx
    have hxeq : ρ * (x / ρ) = x := Nat.mul_div_cancel' hdvd
    have hcdvd : (x / ρ) ∣ x := ⟨ρ, by rw [mul_comm]; exact hxeq.symm⟩
    rw [hTdef, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, lt_of_le_of_lt (Nat.div_le_self x ρ) hxR,
      hxsq.squarefree_of_dvd hcdvd, ?_⟩
    · intro h1
      exact hxne (by rw [← hxeq, h1, mul_one])
    · intro p hp
      exact hxp p (Nat.primeFactors_mono hcdvd hxsq.ne_zero hp)
  calc ∑ x ∈ S, 1 / (Nat.totient x : ℝ) ^ 2
      = ∑ x ∈ S, (1 / (Nat.totient ρ : ℝ) ^ 2) * (1 / (Nat.totient (x / ρ) : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [hφfac x hx, mul_pow]
        simp only [one_div, mul_inv]
    _ = (1 / (Nat.totient ρ : ℝ) ^ 2) * ∑ x ∈ S, 1 / (Nat.totient (x / ρ) : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ = (1 / (Nat.totient ρ : ℝ) ^ 2)
          * ∑ c ∈ S.image (fun x => x / ρ), 1 / (Nat.totient c : ℝ) ^ 2 := by
        rw [Finset.sum_image hinj]
    _ ≤ (1 / (Nat.totient ρ : ℝ) ^ 2) * ∑ c ∈ T, 1 / (Nat.totient c : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg himg (fun c _ _ => by positivity)
    _ = (1 / (Nat.totient ρ : ℝ) ^ 2) * ∑ c ∈ T, ((μ c : ℤ) : ℝ) ^ 2 / (Nat.totient c : ℝ) ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl (fun c hc => ?_)
        rw [hTdef, Finset.mem_erase, Finset.mem_filter] at hc
        rw [moebius_sq_one' hc.2.2.1]
    _ ≤ (1 / (Nat.totient ρ : ℝ) ^ 2) * (4 / (D : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hTdef]
        exact phiSq_tail_tightW R D hD

/-- **`phiSq_dvd_tightW`.** Free-`D` form of `phiSq_dvd_tight`. -/
theorem phiSq_dvd_tightW (R D : ℕ) (hD : 4 ≤ D)
    (ρ : ℕ) (hρsq : Squarefree ρ) (hρp : ∀ p ∈ ρ.primeFactors, D < p) (hρR : ρ < R) :
    ∑ x ∈ (Finset.range R).filter
        (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D < p) ∧ ρ ∣ x),
      1 / (Nat.totient x : ℝ) ^ 2
      ≤ (1 / (Nat.totient ρ : ℝ) ^ 2) * (1 + 4 / (D : ℝ)) := by
  classical
  set Bset := (Finset.range R).filter
      (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D < p) ∧ ρ ∣ x) with hBdef
  have hρmem : ρ ∈ Bset := by
    rw [hBdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨hρR, hρsq, hρp, dvd_refl ρ⟩
  have hsplit : ∑ x ∈ Bset, 1 / (Nat.totient x : ℝ) ^ 2
      = 1 / (Nat.totient ρ : ℝ) ^ 2 + ∑ x ∈ Bset.erase ρ, 1 / (Nat.totient x : ℝ) ^ 2 :=
    (Finset.add_sum_erase Bset (fun x => 1 / (Nat.totient x : ℝ) ^ 2) hρmem).symm
  have hBerase : Bset.erase ρ = (Finset.range R).filter
      (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D < p) ∧ ρ ∣ x ∧ x ≠ ρ) := by
    rw [hBdef]
    ext x
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    tauto
  have htail := phiSq_dvd_ne_tightW R D hD ρ hρsq
  rw [← hBerase] at htail
  have hexp : (1 / (Nat.totient ρ : ℝ) ^ 2) * (1 + 4 / (D : ℝ))
      = 1 / (Nat.totient ρ : ℝ) ^ 2 + (1 / (Nat.totient ρ : ℝ) ^ 2) * (4 / (D : ℝ)) := by
    ring
  rw [hsplit, hexp]
  linarith [htail]

/-! ## The multi-index tail `htail_tightW` (LINEAR constant, `B`-scaled) -/

/-- The per-coordinate index set for the `j`-deviating tail, free `D` form of
`tailCoordSet`. -/
noncomputable def tailCoordSetW (k R D : ℕ) (r : Fin k → ℕ) (j i : Fin k) : Finset ℕ :=
  (Finset.range R).filter
    (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D < p) ∧ r i ∣ x ∧ (i = j → x ≠ r j))

/-- **`tail_factor_le'W`.** Free-`(W',D)` form of `tail_factor_le'`. -/
theorem tail_factor_le'W (k R W' D : ℕ)
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p)
    (j : Fin k) (r : Fin k → ℕ)
    (H : Fin k → ℕ → ℝ) (hH : ∀ i x, 0 ≤ H i x) :
    ∑ a ∈ (kSieveIndex k R W').filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
        ∏ i, H i (a i)
      ≤ ∏ i, ∑ x ∈ tailCoordSetW k R D r j i, H i x := by
  classical
  rw [Finset.prod_univ_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨haK, hguard, hdev⟩ := ha
    have hK := (mem_kSieveIndex_iff a).mp haK
    rw [Fintype.mem_piFinset]
    intro i
    simp only [tailCoordSetW, Finset.mem_filter, Finset.mem_range]
    refine ⟨kSieveIndex_coord_lt haK i, hK.1 i, ?_, hguard i, ?_⟩
    · intro p hp
      exact D_lt_of_prime_dvd_coordW hDlt haK (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
    · intro hij; subst hij; exact hdev
  · intro a _ _
    exact Finset.prod_nonneg (fun i _ => hH i (a i))

/-- **`htail_tightW`.** Free-`(W',D)`, `|y| ≤ B` form of `htail_tight`.  The
concrete error constant is `B·(4·exp 4·rankinC·k)·log R/D`. -/
theorem htail_tightW (k R W' D : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (B : ℝ) (hB0 : 0 ≤ B) (hyB : ∀ s, |y s| ≤ B)
    (_hysupp : ∀ s, s ∉ kSieveIndex k R W' → y s = 0)
    (r : Fin k → ℕ) (hrm : r m = 1) (hR : 2 ≤ R) (hrsupp : r ∈ kSieveIndex k R W')
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p)
    (hk : 1 ≤ k) (hDk : 12 * k ^ 2 ≤ D) :
    |(∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
        * (∑ a ∈ ((kSieveIndex k R W').filter (fun a => ∀ i, r i ∣ a i)) \
              ((kSieveIndex k R W').filter
                (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
            (y a / ∏ i, (Nat.totient (a i) : ℝ))
              * ∏ i ∈ Finset.univ.erase m,
                  (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))))|
      ≤ B * (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D : ℝ) := by
  classical
  obtain ⟨hsq, hcop, hcopW, hprodR⟩ := (mem_kSieveIndex_iff r).mp hrsupp
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (by omega)
  have hD12 : 12 ≤ D := by omega
  have hD4 : 4 ≤ D := by omega
  have hkD : k ≤ D := by nlinarith [hDk]
  have hD0 : 0 < D := by omega
  have hD0R : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD0
  have hD0ne : (D : ℝ) ≠ 0 := hD0R.ne'
  have hkD0R : (k : ℝ) ≤ (D : ℝ) := by exact_mod_cast hkD
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hC₁0 : (0 : ℝ) ≤ rankinC := rankinC_nonneg
  have hexp4 : (0 : ℝ) ≤ Real.exp 4 := (Real.exp_pos 4).le
  have hodd : ∀ i, ∀ p ∈ (r i).primeFactors, 3 ≤ p := by
    intro i p hp
    have := D_lt_of_prime_dvd_coordW hDlt hrsupp (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
    omega
  have hrp : ∀ i, ∀ p ∈ (r i).primeFactors, D < p := fun i p hp =>
    D_lt_of_prime_dvd_coordW hDlt hrsupp (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  have hRankin : ∑ q ∈ (Finset.range R).filter Squarefree, 1 / (Nat.totient q : ℝ)
      ≤ rankinC * Real.log R := rankinC_bound R hR
  set H : Fin k → ℕ → ℝ := fun i x =>
    if i = m then 1 / (Nat.totient x : ℝ) else (r i : ℝ) / (Nat.totient x : ℝ) ^ 2 with hHdef
  have hHnn : ∀ i x, 0 ≤ H i x := by
    intro i x; simp only [hHdef]; split_ifs <;> positivity
  set P : ℝ := ∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ) with hPdef
  set INNER : (Fin k → ℕ) → ℝ := fun a =>
    (y a / ∏ i, (Nat.totient (a i) : ℝ))
      * ∏ i ∈ Finset.univ.erase m,
          (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))) with hINNERdef
  set FG := (kSieveIndex k R W').filter (fun a => ∀ i, r i ∣ a i) with hFGdef
  set Df := (kSieveIndex k R W').filter
      (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i) with hDfdef
  -- per-`a` pointwise bound `|INNER a| ≤ B · ∏ᵢ Hᵢ(aᵢ)`
  have hbound : ∀ a ∈ kSieveIndex k R W', |INNER a| ≤ B * ∏ i, H i (a i) := by
    intro a haK
    have hφa : ∀ i, (0 : ℝ) < (Nat.totient (a i) : ℝ) := fun i => by
      exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos haK i)
    have hΦsplit : (∏ i, (Nat.totient (a i) : ℝ))
        = (Nat.totient (a m) : ℝ) * ∏ i ∈ Finset.univ.erase m, (Nat.totient (a i) : ℝ) :=
      (Finset.mul_prod_erase Finset.univ (fun i => (Nat.totient (a i) : ℝ))
        (Finset.mem_univ m)).symm
    have hprodH : (∏ i, H i (a i))
        = (1 / (Nat.totient (a m) : ℝ))
          * ∏ i ∈ Finset.univ.erase m, ((r i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => H i (a i)) (Finset.mem_univ m)]
      congr 1
      · simp only [hHdef]; rw [if_true]
      · exact Finset.prod_congr rfl (fun i hi => by
          simp only [hHdef]; rw [if_neg (Finset.ne_of_mem_erase hi)])
    rw [hprodH]
    simp only [hINNERdef]
    rw [abs_mul, abs_div, abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hφa i).le)),
      Finset.abs_prod]
    have hstep2 : ∀ i ∈ Finset.univ.erase m,
        |((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))|
          ≤ (r i : ℝ) / (Nat.totient (a i) : ℝ) := by
      intro i _
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r i : ℝ) / (Nat.totient (a i) : ℝ))]
      have h1 := abs_moebius_real_le_one (a i)
      have h2 : (0 : ℝ) ≤ (r i : ℝ) / (Nat.totient (a i) : ℝ) := by positivity
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - |((μ (a i) : ℤ) : ℝ)|) h2]
    calc |y a| / (∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                |((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))|
        ≤ B / (∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m, ((r i : ℝ) / (Nat.totient (a i) : ℝ)) := by
          apply mul_le_mul
          · rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right (hyB a) (by positivity)
          · exact Finset.prod_le_prod (fun i _ => abs_nonneg _) hstep2
          · exact Finset.prod_nonneg (fun i _ => abs_nonneg _)
          · exact div_nonneg hB0 (by positivity)
      _ = B * ((1 / (Nat.totient (a m) : ℝ))
            * ∏ i ∈ Finset.univ.erase m, ((r i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2)) := by
          rw [hΦsplit, Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_pow]
          have hPFne : (∏ i ∈ Finset.univ.erase m, (Nat.totient (a i) : ℝ)) ≠ 0 :=
            (Finset.prod_pos (fun i _ => hφa i)).ne'
          have hφamne : (Nat.totient (a m) : ℝ) ≠ 0 := (hφa m).ne'
          field_simp
  -- per-`j` product bound (all `R`-free except the single `log R`)
  have hjbound : ∀ j ∈ Finset.univ.erase m,
      |P| * ∑ a ∈ (kSieveIndex k R W').filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
              ∏ i, H i (a i)
        ≤ rankinC * Real.log R * (4 / (D : ℝ)) * Real.exp 4 := by
    intro j hj
    have hfact := tail_factor_le'W k R W' D hDlt j r H hHnn
    set U : Fin k → ℝ := fun i =>
      (r i : ℝ) * (if i = j then (1 / (Nat.totient (r i) : ℝ) ^ 2) * (4 / (D : ℝ))
        else (1 / (Nat.totient (r i) : ℝ) ^ 2) * (1 + 4 / (D : ℝ))) with hUdef
    have hUbound : ∀ i ∈ Finset.univ.erase m, (∑ x ∈ tailCoordSetW k R D r j i, H i x) ≤ U i := by
      intro i hi
      have him : i ≠ m := Finset.ne_of_mem_erase hi
      have hHi : ∀ x, H i x = (r i : ℝ) / (Nat.totient x : ℝ) ^ 2 := by
        intro x; simp only [hHdef]; rw [if_neg him]
      rw [Finset.sum_congr rfl (fun x _ => hHi x)]
      rw [show (∑ x ∈ tailCoordSetW k R D r j i, (r i : ℝ) / (Nat.totient x : ℝ) ^ 2)
            = (r i : ℝ) * ∑ x ∈ tailCoordSetW k R D r j i, 1 / (Nat.totient x : ℝ) ^ 2 from by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by rw [mul_one_div])]
      simp only [hUdef]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      by_cases hij : i = j
      · rw [if_pos hij]
        have hset : tailCoordSetW k R D r j i = (Finset.range R).filter
            (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D < p) ∧ r i ∣ x ∧ x ≠ r i) := by
          simp only [tailCoordSetW]; apply Finset.filter_congr; intro x _; simp [hij]
        rw [hset]
        exact phiSq_dvd_ne_tightW R D hD4 (r i) (hsq i)
      · rw [if_neg hij]
        have hset : tailCoordSetW k R D r j i = (Finset.range R).filter
            (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D < p) ∧ r i ∣ x) := by
          simp only [tailCoordSetW]; apply Finset.filter_congr; intro x _; simp [hij]
        rw [hset]
        exact phiSq_dvd_tightW R D hD4 (r i) (hsq i) (hrp i) (kSieveIndex_coord_lt hrsupp i)
    have hmfac : (∑ x ∈ tailCoordSetW k R D r j m, H m x) ≤ rankinC * Real.log R := by
      have hHm : ∀ x, H m x = 1 / (Nat.totient x : ℝ) := by
        intro x; simp only [hHdef]; rw [if_true]
      rw [Finset.sum_congr rfl (fun x _ => hHm x)]
      refine le_trans
        (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => by positivity)) hRankin
      intro x hx
      simp only [tailCoordSetW, Finset.mem_filter, Finset.mem_range] at hx
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hx.1, hx.2.1⟩
    have hPabs : |P| ≤ ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ) := by
      rw [hPdef]
      calc |∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)|
          = ∏ i, |((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)| := Finset.abs_prod _ _
        _ ≤ ∏ i, (gMult (r i) : ℝ) := by
            refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (gMult (r i) : ℝ))]
            calc |((μ (r i) : ℤ) : ℝ)| * (gMult (r i) : ℝ)
                ≤ 1 * (gMult (r i) : ℝ) := by
                  apply mul_le_mul_of_nonneg_right (abs_moebius_real_le_one _) (by positivity)
              _ = (gMult (r i) : ℝ) := one_mul _
        _ = ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ) := by
            rw [← Finset.mul_prod_erase Finset.univ (fun i => (gMult (r i) : ℝ))
              (Finset.mem_univ m), hrm]
            simp [gMult, Nat.primeFactors_one]
    have hprodU : (∏ i, ∑ x ∈ tailCoordSetW k R D r j i, H i x)
        ≤ (∑ x ∈ tailCoordSetW k R D r j m, H m x) * ∏ i ∈ Finset.univ.erase m, U i := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => ∑ x ∈ tailCoordSetW k R D r j i, H i x)
        (Finset.mem_univ m)]
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun x _ => hHnn m x))
      exact Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun x _ => hHnn i x)) hUbound
    have hjfac : (gMult (r j) : ℝ) * U j ≤ 4 / (D : ℝ) := by
      simp only [hUdef]; rw [if_true]
      rw [show (gMult (r j) : ℝ) * ((r j : ℝ)
              * ((1 / (Nat.totient (r j) : ℝ) ^ 2) * (4 / (D : ℝ))))
            = ((gMult (r j) : ℝ) * (r j : ℝ) / (Nat.totient (r j) : ℝ) ^ 2)
              * (4 / (D : ℝ)) from by ring]
      calc ((gMult (r j) : ℝ) * (r j : ℝ) / (Nat.totient (r j) : ℝ) ^ 2)
              * (4 / (D : ℝ))
          ≤ 1 * (4 / (D : ℝ)) :=
            mul_le_mul_of_nonneg_right (gr_ratio_mem' (hsq j) (hodd j)).2 (by positivity)
        _ = 4 / (D : ℝ) := one_mul _
    have hrestfac : ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i)
        ≤ Real.exp 4 := by
      have hcard : ((Finset.univ.erase m).erase j).card ≤ k := by
        calc ((Finset.univ.erase m).erase j).card
            ≤ (Finset.univ : Finset (Fin k)).card :=
              Finset.card_le_card ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
          _ = k := by rw [Finset.card_univ, Fintype.card_fin]
      have hfac_le : (1 : ℝ) + 4 / (D : ℝ) ≤ Real.exp (4 / (D : ℝ)) := by
        have h := Real.add_one_le_exp (4 / (D : ℝ)); linarith
      have hcard_le : (((Finset.univ.erase m).erase j).card : ℝ) * (4 / (D : ℝ)) ≤ 4 := by
        have h1 : (((Finset.univ.erase m).erase j).card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcard
        calc (((Finset.univ.erase m).erase j).card : ℝ) * (4 / (D : ℝ))
            ≤ (k : ℝ) * (4 / (D : ℝ)) := by gcongr
          _ ≤ (D : ℝ) * (4 / (D : ℝ)) := by gcongr
          _ = 4 := by field_simp
      calc ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i)
          ≤ ∏ _i ∈ (Finset.univ.erase m).erase j, (1 + 4 / (D : ℝ)) := by
            refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
            · have hijne : i ≠ j := Finset.ne_of_mem_erase hi
              simp only [hUdef]; rw [if_neg hijne]; positivity
            · have hijne : i ≠ j := Finset.ne_of_mem_erase hi
              simp only [hUdef]; rw [if_neg hijne]
              rw [show (gMult (r i) : ℝ) * ((r i : ℝ)
                    * ((1 / (Nat.totient (r i) : ℝ) ^ 2) * (1 + 4 / (D : ℝ))))
                    = ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2)
                      * (1 + 4 / (D : ℝ)) from by ring]
              have hge := (gr_ratio_mem' (hsq i) (hodd i)).2
              nlinarith [hge, (by positivity : (0:ℝ) ≤ 1 + 4 / (D : ℝ))]
        _ = (1 + 4 / (D : ℝ)) ^ ((Finset.univ.erase m).erase j).card := by
            rw [Finset.prod_const]
        _ ≤ (Real.exp (4 / (D : ℝ))) ^ ((Finset.univ.erase m).erase j).card :=
            pow_le_pow_left₀ (by positivity) hfac_le _
        _ = Real.exp ((((Finset.univ.erase m).erase j).card : ℝ) * (4 / (D : ℝ))) :=
            (Real.exp_nat_mul (4 / (D : ℝ)) _).symm
        _ ≤ Real.exp 4 := Real.exp_le_exp.mpr hcard_le
    have hrestnn : (0 : ℝ) ≤ ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i) := by
      refine Finset.prod_nonneg (fun i hi => ?_)
      have hijne : i ≠ j := Finset.ne_of_mem_erase hi
      simp only [hUdef]; rw [if_neg hijne]; positivity
    calc |P| * ∑ a ∈ (kSieveIndex k R W').filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
              ∏ i, H i (a i)
        ≤ |P| * ∏ i, ∑ x ∈ tailCoordSetW k R D r j i, H i x :=
          mul_le_mul_of_nonneg_left hfact (abs_nonneg _)
      _ ≤ |P| * ((∑ x ∈ tailCoordSetW k R D r j m, H m x) * ∏ i ∈ Finset.univ.erase m, U i) :=
          mul_le_mul_of_nonneg_left hprodU (abs_nonneg _)
      _ = (∑ x ∈ tailCoordSetW k R D r j m, H m x) * (|P| * ∏ i ∈ Finset.univ.erase m, U i) := by
          ring
      _ ≤ (rankinC * Real.log R) * ((4 / (D : ℝ)) * Real.exp 4) := by
          refine mul_le_mul hmfac ?_ ?_ (mul_nonneg hC₁0 hlogR)
          · calc |P| * ∏ i ∈ Finset.univ.erase m, U i
                ≤ (∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
                    * ∏ i ∈ Finset.univ.erase m, U i := by
                  refine mul_le_mul_of_nonneg_right hPabs (Finset.prod_nonneg (fun i _ => ?_))
                  simp only [hUdef]; split_ifs <;> positivity
              _ = ∏ i ∈ Finset.univ.erase m, ((gMult (r i) : ℝ) * U i) :=
                  (Finset.prod_mul_distrib).symm
              _ = ((gMult (r j) : ℝ) * U j)
                    * ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i) :=
                  (Finset.mul_prod_erase (Finset.univ.erase m)
                    (fun i => (gMult (r i) : ℝ) * U i) hj).symm
              _ ≤ (4 / (D : ℝ)) * Real.exp 4 :=
                  mul_le_mul hjfac hrestfac hrestnn (by positivity)
          · exact mul_nonneg (abs_nonneg _)
              (Finset.prod_nonneg (fun i _ => by simp only [hUdef]; split_ifs <;> positivity))
      _ = rankinC * Real.log R * (4 / (D : ℝ)) * Real.exp 4 := by ring
  -- the `B`-free core estimate
  have hmid : |P| * ∑ a ∈ FG \ Df, ∏ i, H i (a i)
      ≤ (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D : ℝ) := by
    calc |P| * ∑ a ∈ FG \ Df, ∏ i, H i (a i)
        ≤ |P| * ∑ j ∈ Finset.univ.erase m,
            ∑ a ∈ (kSieveIndex k R W').filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
              ∏ i, H i (a i) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have hunion : ∀ a ∈ FG \ Df, (∏ i, H i (a i))
              ≤ ∑ j ∈ Finset.univ.erase m, (if a j ≠ r j then ∏ i, H i (a i) else 0) := by
            intro a ha
            rw [Finset.mem_sdiff] at ha
            obtain ⟨haFG, haDf⟩ := ha
            rw [hFGdef, Finset.mem_filter] at haFG
            obtain ⟨j, hjmem, hjne⟩ : ∃ j ∈ Finset.univ.erase m, a j ≠ r j := by
              by_contra hcon
              apply haDf
              rw [hDfdef, Finset.mem_filter]
              refine ⟨haFG.1, haFG.2, fun i hi => ?_⟩
              by_contra hne
              exact hcon ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hne⟩
            calc (∏ i, H i (a i)) = if a j ≠ r j then ∏ i, H i (a i) else 0 := by rw [if_pos hjne]
              _ ≤ ∑ j ∈ Finset.univ.erase m, (if a j ≠ r j then ∏ i, H i (a i) else 0) := by
                  refine Finset.single_le_sum
                    (f := fun j => if a j ≠ r j then ∏ i, H i (a i) else 0) (fun j _ => ?_) hjmem
                  split_ifs
                  · exact Finset.prod_nonneg (fun i _ => hHnn i (a i))
                  · exact le_refl 0
          calc ∑ a ∈ FG \ Df, ∏ i, H i (a i)
              ≤ ∑ a ∈ FG \ Df, ∑ j ∈ Finset.univ.erase m,
                  (if a j ≠ r j then ∏ i, H i (a i) else 0) := Finset.sum_le_sum hunion
            _ = ∑ j ∈ Finset.univ.erase m, ∑ a ∈ FG \ Df,
                  (if a j ≠ r j then ∏ i, H i (a i) else 0) := Finset.sum_comm
            _ ≤ ∑ j ∈ Finset.univ.erase m,
                  ∑ a ∈ (kSieveIndex k R W').filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
                    ∏ i, H i (a i) := by
                refine Finset.sum_le_sum (fun j _ => ?_)
                rw [← Finset.sum_filter]
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_
                  (fun a _ _ => Finset.prod_nonneg (fun i _ => hHnn i (a i)))
                intro a ha
                rw [Finset.mem_filter, Finset.mem_sdiff, hFGdef, Finset.mem_filter] at ha
                rw [Finset.mem_filter]
                exact ⟨ha.1.1.1, ha.1.1.2, ha.2⟩
      _ = ∑ j ∈ Finset.univ.erase m,
            |P| * ∑ a ∈ (kSieveIndex k R W').filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
              ∏ i, H i (a i) := Finset.mul_sum _ _ _
      _ ≤ ∑ _j ∈ Finset.univ.erase m, rankinC * Real.log R * (4 / (D : ℝ)) * Real.exp 4 :=
          Finset.sum_le_sum hjbound
      _ = ((Finset.univ.erase m).card : ℝ)
            * (rankinC * Real.log R * (4 / (D : ℝ)) * Real.exp 4) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D : ℝ) := by
          have hcardle : ((Finset.univ.erase m).card : ℝ) ≤ (k : ℝ) := by
            have : (Finset.univ.erase m).card ≤ k := by
              calc (Finset.univ.erase m).card ≤ (Finset.univ : Finset (Fin k)).card :=
                    Finset.card_le_card (Finset.erase_subset _ _)
                _ = k := by rw [Finset.card_univ, Fintype.card_fin]
            exact_mod_cast this
          have hXnn : (0 : ℝ) ≤ rankinC * Real.log R * (4 / (D : ℝ)) * Real.exp 4 :=
            mul_nonneg (mul_nonneg (mul_nonneg hC₁0 hlogR) (by positivity)) hexp4
          have heq : (k : ℝ) * (rankinC * Real.log R * (4 / (D : ℝ)) * Real.exp 4)
              = (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D : ℝ) := by
            field_simp
          exact le_trans (mul_le_mul_of_nonneg_right hcardle hXnn) (le_of_eq heq)
  -- assemble, threading the `B` factor
  rw [abs_mul]
  calc |P| * |∑ a ∈ FG \ Df, INNER a|
      ≤ |P| * ∑ a ∈ FG \ Df, |INNER a| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ ≤ |P| * ∑ a ∈ FG \ Df, (B * ∏ i, H i (a i)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a ha => ?_)) (abs_nonneg _)
        rw [Finset.mem_sdiff, hFGdef, Finset.mem_filter] at ha
        exact hbound a ha.1.1
    _ = B * (|P| * ∑ a ∈ FG \ Df, ∏ i, H i (a i)) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ B * ((4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D : ℝ)) :=
        mul_le_mul_of_nonneg_left hmid hB0
    _ = B * (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D : ℝ) := by ring

/-! ## The main-sum size bound and the Lemma 5.3 assembly -/

/-- **`abs_mainSum_le_tightW`.** Free-`W'`, `|y| ≤ B` form of
`abs_mainSum_le_tight`: `|∑ y/φ| ≤ B·rankinC·log R`. -/
theorem abs_mainSum_le_tightW (k R W' : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (B : ℝ) (hB0 : 0 ≤ B) (hyB : ∀ s, |y s| ≤ B)
    (hysupp : ∀ s, s ∉ kSieveIndex k R W' → y s = 0)
    (r : Fin k → ℕ) (hR : 2 ≤ R) :
    |∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
      ≤ B * (rankinC * Real.log R) := by
  classical
  have hRankin := rankinC_bound R hR
  have hterm : ∀ am ∈ Finset.range R,
      |y (Function.update r m am) / (Nat.totient am : ℝ)|
        ≤ if Squarefree am then B * (1 / (Nat.totient am : ℝ)) else 0 := by
    intro am _
    by_cases hsf : Squarefree am
    · have hampos : 0 < am := Nat.pos_of_ne_zero hsf.ne_zero
      have hφpos : (0 : ℝ) < (Nat.totient am : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hampos
      rw [if_pos hsf, abs_div, abs_of_nonneg hφpos.le, mul_one_div]
      gcongr
      exact hyB _
    · rw [if_neg hsf]
      have hnotmem : Function.update r m am ∉ kSieveIndex k R W' := fun hmem =>
        hsf (by
          have := ((mem_kSieveIndex_iff _).mp hmem).1 m
          rwa [Function.update_self] at this)
      rw [hysupp _ hnotmem, zero_div, abs_zero]
  calc |∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
      ≤ ∑ am ∈ Finset.range R, |y (Function.update r m am) / (Nat.totient am : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ am ∈ Finset.range R, (if Squarefree am then B * (1 / (Nat.totient am : ℝ)) else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ am ∈ (Finset.range R).filter Squarefree, B * (1 / (Nat.totient am : ℝ)) :=
        (Finset.sum_filter _ _).symm
    _ = B * ∑ am ∈ (Finset.range R).filter Squarefree, 1 / (Nat.totient am : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ B * (rankinC * Real.log R) := mul_le_mul_of_nonneg_left hRankin hB0

/-- **`stepB_identityW`.** Free-`W'` form of `stepB_identity` (pure `W k → W'`,
no `D₀`). -/
theorem stepB_identityW (k R W' : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hysupp : ∀ s, s ∉ kSieveIndex k R W' → y s = 0)
    (r : Fin k → ℕ) (hrsupp : r ∈ kSieveIndex k R W') (hrm : r m = 1) :
    (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
      * (∑ a ∈ (kSieveIndex k R W').filter
            (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i),
          (y a / ∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))))
      = (∏ i ∈ Finset.univ.erase m,
          ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2))
        * (∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)) := by
  classical
  obtain ⟨hsq, hcop, hcopW, hprodR⟩ := (mem_kSieveIndex_iff r).mp hrsupp
  set INNER : (Fin k → ℕ) → ℝ := fun a =>
    (y a / ∏ i, (Nat.totient (a i) : ℝ))
      * ∏ i ∈ Finset.univ.erase m,
          (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))) with hINNER
  set 𝒟f := (kSieveIndex k R W').filter
      (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i) with h𝒟f
  have hauto : ∀ am : ℕ, (∀ i, r i ∣ Function.update r m am i)
      ∧ ∀ i, i ≠ m → Function.update r m am i = r i := by
    intro am
    refine ⟨fun i => ?_, fun i hi => Function.update_of_ne hi _ _⟩
    rcases eq_or_ne i m with rfl | hne
    · rw [Function.update_self, hrm]; exact one_dvd _
    · rw [Function.update_of_ne hne]
  have hmemf : ∀ am : ℕ, Function.update r m am ∈ 𝒟f
      ↔ Function.update r m am ∈ kSieveIndex k R W' := by
    intro am
    rw [h𝒟f, Finset.mem_filter]
    exact ⟨fun h => h.1, fun h => ⟨h, hauto am⟩⟩
  have hupd : ∀ a ∈ 𝒟f, a = Function.update r m (a m) := by
    intro a ha
    rw [h𝒟f, Finset.mem_filter] at ha
    funext i
    rcases eq_or_ne i m with rfl | hne
    · rw [Function.update_self]
    · rw [Function.update_of_ne hne, ha.2.2 i hne]
  have hinj : Set.InjOn (fun a : Fin k → ℕ => a m) ↑𝒟f := by
    intro a ha b hb hab
    rw [hupd a ha, hupd b hb]
    simp only at hab
    rw [hab]
  have hsubR : 𝒟f.image (fun a => a m) ⊆ Finset.range R := by
    intro am ham
    rw [Finset.mem_image] at ham
    obtain ⟨a, ha, rfl⟩ := ham
    rw [h𝒟f, Finset.mem_filter] at ha
    rw [Finset.mem_range]
    exact kSieveIndex_coord_lt ha.1 m
  have hzero : ∀ am ∈ Finset.range R, am ∉ 𝒟f.image (fun a => a m) →
      INNER (Function.update r m am) = 0 := by
    intro am _ ham
    have hnotf : Function.update r m am ∉ 𝒟f := by
      intro hmem
      exact ham (Finset.mem_image.mpr ⟨_, hmem, Function.update_self _ _ _⟩)
    have hnot𝒟 : Function.update r m am ∉ kSieveIndex k R W' :=
      fun h => hnotf ((hmemf am).mpr h)
    rw [hINNER]
    simp only
    rw [hysupp _ hnot𝒟, zero_div, zero_mul]
  have hreindex : (∑ a ∈ 𝒟f, INNER a)
      = ∑ am ∈ Finset.range R, INNER (Function.update r m am) := by
    rw [← Finset.sum_subset hsubR hzero, Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun a ha => by rw [← hupd a ha])
  have halg : ∀ am : ℕ,
      (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)) * INNER (Function.update r m am)
        = (∏ i ∈ Finset.univ.erase m,
            ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2))
          * (y (Function.update r m am) / (Nat.totient am : ℝ)) := by
    intro am
    rw [hINNER]
    simp only
    have hφprod : (∏ i, (Nat.totient (Function.update r m am i) : ℝ))
        = (Nat.totient am : ℝ) * ∏ i ∈ Finset.univ.erase m, (Nat.totient (r i) : ℝ) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i => (Nat.totient (Function.update r m am i) : ℝ)) (Finset.mem_univ m),
        Function.update_self]
      congr 1
      exact Finset.prod_congr rfl (fun i hi => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
    have hmuprod : (∏ i ∈ Finset.univ.erase m,
          (((μ (Function.update r m am i) : ℤ) : ℝ)
            * ((r i : ℝ) / (Nat.totient (Function.update r m am i) : ℝ))))
        = ∏ i ∈ Finset.univ.erase m,
            (((μ (r i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (r i) : ℝ))) :=
      Finset.prod_congr rfl (fun i hi => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
    have hPprod : (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
        = ∏ i ∈ Finset.univ.erase m, (((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i => ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)) (Finset.mem_univ m)]
      rw [hrm]
      simp [gMult, Nat.primeFactors_one]
    have hcombine : (∏ i ∈ Finset.univ.erase m, (((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)))
          * (∏ i ∈ Finset.univ.erase m,
              (((μ (r i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (r i) : ℝ))))
          / (∏ i ∈ Finset.univ.erase m, (Nat.totient (r i) : ℝ))
        = ∏ i ∈ Finset.univ.erase m,
            ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have hmu2 := moebius_sq_one' (hsq i)
      have h1 : (((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
            * (((μ (r i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (r i) : ℝ)))
            / (Nat.totient (r i) : ℝ)
          = ((μ (r i) : ℤ) : ℝ) ^ 2
            * ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2) := by ring
      rw [h1, hmu2, one_mul]
    rw [hφprod, hmuprod, hPprod, ← hcombine]
    ring
  calc (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
        * (∑ a ∈ 𝒟f, INNER a)
      = ∑ am ∈ Finset.range R,
          (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)) * INNER (Function.update r m am) := by
        rw [hreindex, Finset.mul_sum]
    _ = ∑ am ∈ Finset.range R,
          (∏ i ∈ Finset.univ.erase m,
              ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2))
            * (y (Function.update r m am) / (Nat.totient am : ℝ)) :=
        Finset.sum_congr rfl (fun am _ => halg am)
    _ = (∏ i ∈ Finset.univ.erase m,
          ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2))
        * (∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)) := by
        rw [Finset.mul_sum]

/-- **`gProd_boundW`.** Free-`(W',D)` form of `gProd_bound`. -/
theorem gProd_boundW (k R W' D : ℕ) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D)
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p)
    (r : Fin k → ℕ) (hrsupp : r ∈ kSieveIndex k R W') (m : Fin k) :
    |(∏ i ∈ Finset.univ.erase m,
        ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2)) - 1|
      ≤ (2 : ℝ) / (D : ℝ) := by
  classical
  obtain ⟨hsq, hcop, hcopW, hprodR⟩ := (mem_kSieveIndex_iff r).mp hrsupp
  have hD12 : 12 ≤ D := by
    have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have : 0 < D := by omega
    exact_mod_cast this
  have hodd : ∀ i, ∀ p ∈ (r i).primeFactors, 3 ≤ p := by
    intro i p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ r i := Nat.dvd_of_mem_primeFactors hp
    have hD0p : D < p := D_lt_of_prime_dvd_coordW hDlt hrsupp hpp hpd
    omega
  set S : Finset ℕ :=
    (Finset.univ.erase m).biUnion (fun i => (r i).primeFactors) with hS
  have hdisj : (↑(Finset.univ.erase m) : Set (Fin k)).PairwiseDisjoint
      (fun i => (r i).primeFactors) := by
    intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hpi hpj
    have hp1 : p ∣ 1 :=
      hcop i j hij ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpi)
        (Nat.dvd_of_mem_primeFactors hpj)
    exact (Nat.prime_of_mem_primeFactors hpi).one_lt.ne' (Nat.dvd_one.mp hp1)
  have hprodeq : (∏ i ∈ Finset.univ.erase m,
        ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2))
      = ∏ p ∈ S, (1 - (((p : ℝ) - 1)⁻¹) ^ 2) := by
    rw [hS, Finset.prod_biUnion hdisj]
    exact Finset.prod_congr rfl (fun i _ => g_factor_prod' (hsq i) (hodd i))
  have hSmem : ∀ p ∈ S, p.Prime ∧ D < p ∧ p ≤ R := by
    intro p hp
    rw [hS, Finset.mem_biUnion] at hp
    obtain ⟨i, _, hpi⟩ := hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpi
    have hpd : p ∣ r i := Nat.dvd_of_mem_primeFactors hpi
    refine ⟨hpp, D_lt_of_prime_dvd_coordW hDlt hrsupp hpp hpd, ?_⟩
    have hle : p ≤ r i := Nat.le_of_dvd (kSieveIndex_coord_pos hrsupp i) hpd
    have hlt : r i < R := kSieveIndex_coord_lt hrsupp i
    omega
  rw [hprodeq]
  refine le_trans (abs_prod_one_sub_le S (fun p => (((p : ℝ) - 1)⁻¹) ^ 2)
    (fun p _ => by positivity) ?_) ?_
  · intro p hp
    obtain ⟨hpp, hpD, -⟩ := hSmem p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (12 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_le_of_lt (by exact_mod_cast hD12) hpD
      linarith
    have h0 : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    have : ((p : ℝ) - 1)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right; linarith
    nlinarith [this, h0]
  · have hsub : S ⊆ Finset.Icc (D + 1) R := by
      intro p hp
      obtain ⟨-, hpD, hpR⟩ := hSmem p hp
      rw [Finset.mem_Icc]; omega
    have hmono : ∑ p ∈ S, (((p : ℝ) - 1)⁻¹) ^ 2
        ≤ ∑ n ∈ Finset.Icc (D + 1) R, (((n : ℝ) - 1)⁻¹) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    have hfrac : ((D : ℝ) - 1)⁻¹ ≤ 2 / (D : ℝ) := by
      have h1 : (0 : ℝ) < (D : ℝ) - 1 := by
        have : (12 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD12
        linarith
      rw [inv_eq_one_div, div_le_div_iff₀ h1 hDpos]
      have : (12 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD12
      linarith
    rcases Nat.lt_or_ge R D with hR' | hR'
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty] at hmono
      linarith [hmono, (by positivity : (0 : ℝ) ≤ 2 / (D : ℝ))]
    · have htele := inv_sq_tele53 D (by omega) R hR'
      have hRinv : (0 : ℝ) ≤ ((R : ℝ) - 1)⁻¹ := by
        have hR2 : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 2 ≤ R)
        rw [inv_nonneg]; linarith
      linarith [hmono, htele, hfrac]

/-- **`lemma53_tightW`** (the frozen deliverable).  Free-`(W',D)`, `|y| ≤ B`
form of `lemma53_tight`: `|yM − contraction| ≤ B·lemma53Const·k·log R/D`. -/
theorem lemma53_tightW (k R W' D : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (B : ℝ) (hB0 : 0 ≤ B) (hyB : ∀ s, |y s| ≤ B)
    (hysupp : ∀ s, s ∉ kSieveIndex k R W' → y s = 0)
    (r : Fin k → ℕ) (hrm : r m = 1) (hR : 2 ≤ R)
    (hrsupp : r ∈ kSieveIndex k R W')
    (hW' : Squarefree W') (hDlt : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p)
    (hk : 1 ≤ k) (hDk : 12 * k ^ 2 ≤ D) :
    |yM k R W' m y r
        - ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
      ≤ B * (lemma53Const * (k : ℝ)) * Real.log R / (D : ℝ) := by
  classical
  -- `hW'` (squarefree `W'`) is carried for the downstream S2 bridge (W4-5); the
  -- contraction proper needs only `hDlt`.  Referenced here to keep it in scope.
  have _hWsq : Squarefree W' := hW'
  have hSb := abs_mainSum_le_tightW k R W' m y B hB0 hyB hysupp r hR
  have hTb := htail_tightW k R W' D m y B hB0 hyB hysupp r hrm hR hrsupp hDlt hk hDk
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hD0R : (0 : ℝ) < (D : ℝ) := by
    have : 0 < D := by have : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (by omega); omega
    exact_mod_cast this
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hC₁0 : (0 : ℝ) ≤ rankinC := rankinC_nonneg
  have hexp4 : (0 : ℝ) ≤ Real.exp 4 := (Real.exp_pos 4).le
  have hsub : (kSieveIndex k R W').filter
        (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)
      ⊆ (kSieveIndex k R W').filter (fun a => ∀ i, r i ∣ a i) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2.1⟩
  have hlpc : lamPhiContractM k R W' m y r
      = (∑ a ∈ (kSieveIndex k R W').filter
            (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i),
          (y a / ∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))))
        + (∑ a ∈ ((kSieveIndex k R W').filter (fun a => ∀ i, r i ∣ a i)) \
              ((kSieveIndex k R W').filter
                (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
            (y a / ∏ i, (Nat.totient (a i) : ℝ))
              * ∏ i ∈ Finset.univ.erase m,
                  (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ)))) := by
    rw [lamPhiContractM_collapse k R W' m y r hrm, ← Finset.sum_filter, add_comm]
    exact (Finset.sum_sdiff hsub).symm
  have hdiff : yM k R W' m y r
        - ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)
      = ((∏ i ∈ Finset.univ.erase m,
            ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2)) - 1)
          * (∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ))
        + (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
          * (∑ a ∈ ((kSieveIndex k R W').filter (fun a => ∀ i, r i ∣ a i)) \
                ((kSieveIndex k R W').filter
                  (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
              (y a / ∏ i, (Nat.totient (a i) : ℝ))
                * ∏ i ∈ Finset.univ.erase m,
                    (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ)))) := by
    rw [show yM k R W' m y r
          = (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
            * lamPhiContractM k R W' m y r from rfl,
      hlpc, mul_add, stepB_identityW k R W' m y hysupp r hrsupp hrm]
    ring
  rw [hdiff]
  set G := ∏ i ∈ Finset.univ.erase m,
    ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2) with hGdef
  set S := ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ) with hSdef
  set PT := (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
      * (∑ a ∈ ((kSieveIndex k R W').filter (fun a => ∀ i, r i ∣ a i)) \
            ((kSieveIndex k R W').filter
              (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
          (y a / ∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ)))) with hPTdef
  have hG : |G - 1| ≤ 2 / (D : ℝ) := gProd_boundW k R W' D hk hDk hDlt r hrsupp m
  have e2 : |G - 1| * |S| ≤ (2 / (D : ℝ)) * (B * (rankinC * Real.log R)) :=
    mul_le_mul hG hSb (abs_nonneg _) (by positivity)
  have hfinal : (2 / (D : ℝ)) * (B * (rankinC * Real.log R))
        + B * (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D : ℝ)
      ≤ B * (lemma53Const * (k : ℝ)) * Real.log R / (D : ℝ) := by
    have hnum : 2 * (B * (rankinC * Real.log R))
          + B * (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R
        ≤ B * (lemma53Const * (k : ℝ)) * Real.log R := by
      rw [lemma53Const]
      nlinarith [hC₁0, hlogR, hexp4, hkR, hB0,
        mul_nonneg (mul_nonneg (mul_nonneg hB0 hC₁0) hlogR)
          (show (0 : ℝ) ≤ (k : ℝ) - 1 by linarith [hkR]),
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hB0 hexp4) hC₁0) hlogR)
          (show (0 : ℝ) ≤ (k : ℝ) - 1 by linarith [hkR])]
    have hLHSeq : (2 / (D : ℝ)) * (B * (rankinC * Real.log R))
          + B * (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D : ℝ)
        = (2 * (B * (rankinC * Real.log R))
            + B * (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R) / (D : ℝ) := by
      field_simp
    rw [hLHSeq]
    gcongr
  calc |(G - 1) * S + PT|
      ≤ |(G - 1) * S| + |PT| := abs_add_le _ _
    _ = |G - 1| * |S| + |PT| := by rw [abs_mul]
    _ ≤ (2 / (D : ℝ)) * (B * (rankinC * Real.log R))
          + B * (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D : ℝ) :=
        add_le_add e2 hTb
    _ ≤ B * (lemma53Const * (k : ℝ)) * Real.log R / (D : ℝ) := hfinal

end Salt.Maynard
