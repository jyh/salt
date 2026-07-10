/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.CollisionQuant
import Salt.Maynard.TensorA1
import Salt.Maynard.Transfer
import Salt.Maynard.GFunction
import Salt.Maynard.Lemma53
import Salt.Maynard.HOmit

/-!
# Node C (S2 inner bound) — `euler_tail_L` and `Gdiag_le`

Two mechanical pieces of the S2 inner-bound design
(`docs/blueprints/s2-inner-design.md`, Node C parts 1 and 3):

* `euler_tail_L` — the Euler-product tail of `CollisionQuant.euler_tail`
  generalized to an arbitrary per-prime amplification `L ≥ 1`: over squarefree
  moduli `t > 1` with all prime factors `> D₀ k`,
  `∑ L^{ω(t)} ∏_{p ∣ t} (p−1)⁻² ≤ 4L/D₀ k`, valid whenever `4L ≤ D₀ k`.
  (The original `euler_tail` is the case `L = 3k²` with the weaker constant.)

* `Gdiag_le` — the diagonal `G`-sum
  `Gdiag = ∑_{u ∈ 𝒟, uₘ = 1} ∏_{i ≠ m} fTilde(uᵢ)²/g(uᵢ)` is at most
  `2·A₁^{k−1}`. Route: box relaxation `Gdiag ≤ A_g^{k−1}` with
  `A_g = ∑_{r ∈ sqfCop(R₀,W)} fWt(r)²/g(r)`, then the sum-level `φ/g`
  comparison `A_g ≤ A₁·(1 + 8/D₀)` (expand `∏(p−1)/(p−2) = ∑_{d ∣ r} h(d)`
  with `h(d) = ∏_{p ∣ d} (p−2)⁻¹`, swap sums, reindex the `d ∣ r` fibre by
  `r = d·c`, and control the `d > 1` tail by `euler_tail_L` at `L = 2`),
  and finally `(1 + 8/D₀)^{k−1} ≤ 2` since `16(k−1) ≤ 12k² ≤ D₀`.
-/

open Finset

namespace Salt.Maynard

/-! ## `euler_tail_L` — the `L`-weighted Euler tail -/

/-- Telescoping tail bound:
`∑_{a < n ≤ b} (n−1)⁻² ≤ (a−1)⁻¹ − (b−1)⁻¹` for `2 ≤ a ≤ b`. -/
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

/-- Product-versus-sum: if the `aₓ ≥ 0` sum to at most `1/2`, then
`∏(1 + aₓ) ≤ 1 + 2∑aₓ`. Elementary induction — no logs, no `exp`. -/
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

/-- **Node C.1 — `euler_tail_L`.** The Euler-product tail over squarefree
moduli with all prime factors `> D₀ k`, with an arbitrary per-prime
amplification `L ≥ 1`: the total (excluding the trivial modulus `1`) is at
most `4L/D₀ k`, valid whenever `4L ≤ D₀ k`. `M` is an arbitrary finite range
cap. Generalizes `euler_tail` (which is the case `L = 3k²`). -/
theorem euler_tail_L (k M : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hD : 4 * L ≤ (D₀ k : ℝ)) :
    ∑ t ∈ ((Finset.range M).filter
        (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p)).erase 1,
      L ^ t.primeFactors.card
        * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2
      ≤ 4 * L / (D₀ k : ℝ) := by
  classical
  have hD4 : 4 ≤ D₀ k := by
    have h4 : (4 : ℝ) ≤ (D₀ k : ℝ) := le_trans (by linarith) hD
    exact_mod_cast h4
  have hDpos : (0 : ℝ) < (D₀ k : ℝ) := by
    have : 0 < D₀ k := by omega
    exact_mod_cast this
  have hLpos : 0 < L := by linarith
  set a : ℕ → ℝ := fun p => L * (((p : ℝ) - 1)⁻¹) ^ 2 with haDef
  have ha_nonneg : ∀ p, 0 ≤ a p := fun p => by positivity
  set SF := ((Finset.range M).filter
      (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p)).erase 1 with hSF
  set PP := (Finset.range M).filter (fun p => p.Prime ∧ D₀ k < p) with hPP
  -- Step 1: each term is `∏_{p ∣ t} a p`.
  have hterm : ∀ t ∈ SF,
      L ^ t.primeFactors.card
          * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2
        = ∏ p ∈ t.primeFactors, a p := by
    intro t _
    rw [haDef, Finset.prod_mul_distrib, Finset.prod_const]
  -- Step 2: `primeFactors` injects `SF` into `PP.powerset.erase ∅`.
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
    · -- `t.primeFactors ≠ ∅` since `t ≠ 1` and `t` squarefree (so `t ≥ 2`).
      have ht2 : 1 < t := by
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
  -- Step 3: the powerset sum is the Euler product minus 1.
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
  -- Step 4: the prime sum is at most `L · 2/D₀ ≤ 1/2`.
  have htailsum : ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2 ≤ 2 / (D₀ k : ℝ) := by
    have hPPsub : PP ⊆ Finset.Icc (D₀ k + 1) M := by
      intro p hp
      rw [hPP, Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_Icc]
      omega
    have hmono : ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2
        ≤ ∑ n ∈ Finset.Icc (D₀ k + 1) M, (((n : ℝ) - 1)⁻¹) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hPPsub fun n _ _ => by positivity
    rcases Nat.lt_or_ge M (D₀ k) with hM | hM
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty] at hmono
      exact le_trans hmono (by positivity)
    · have htele := inv_sq_tele (D₀ k) (by omega) M hM
      have hMinv : 0 ≤ ((M : ℝ) - 1)⁻¹ := by
        have hM2 : (2 : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast (by omega : 2 ≤ M)
        rw [inv_nonneg]
        linarith
      have hfrac : ((D₀ k : ℝ) - 1)⁻¹ ≤ 2 / (D₀ k : ℝ) := by
        have h1 : (0 : ℝ) < (D₀ k : ℝ) - 1 := by
          have : (4 : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast hD4
          linarith
        rw [inv_eq_one_div, div_le_div_iff₀ h1 hDpos]
        have : (4 : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast hD4
        linarith
      linarith
  have hasum : ∑ p ∈ PP, a p ≤ 1 / 2 := by
    have h1 : ∑ p ∈ PP, a p = L * ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2 := by
      simp only [haDef, Finset.mul_sum]
    rw [h1]
    have h2 : L * ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2 ≤ L * (2 / (D₀ k : ℝ)) :=
      mul_le_mul_of_nonneg_left htailsum hLpos.le
    have h3 : L * (2 / (D₀ k : ℝ)) ≤ 1 / 2 := by
      have heq : L * (2 / (D₀ k : ℝ)) = 2 * L / (D₀ k : ℝ) := by ring
      rw [heq, div_le_div_iff₀ hDpos (by norm_num : (0 : ℝ) < 2)]
      linarith
    linarith
  -- Assemble.
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
    _ ≤ 2 * (L * (2 / (D₀ k : ℝ))) := by
        have h1 : ∑ p ∈ PP, a p = L * ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2 := by
          simp only [haDef, Finset.mul_sum]
        rw [h1]
        have h2 := mul_le_mul_of_nonneg_left htailsum hLpos.le
        linarith
    _ = 4 * L / (D₀ k : ℝ) := by
        field_simp
        ring

/-! ## The `h`-expansion `∏_{p ∣ r} (p−1)/(p−2) = ∑_{d ∣ r} ∏_{p ∣ d} (p−2)⁻¹` -/

/-- For squarefree `r`, the divisors of `r` are exactly the products of
subsets of its prime factors. -/
private lemma divisors_eq_powerset_image {r : ℕ} (hr : Squarefree r) :
    r.divisors = r.primeFactors.powerset.image (fun S => ∏ p ∈ S, p) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hdvd, -⟩
    exact ⟨d.primeFactors, Nat.primeFactors_mono hdvd hr.ne_zero,
      Nat.prod_primeFactors_of_squarefree (hr.squarefree_of_dvd hdvd)⟩
  · rintro ⟨S, hS, rfl⟩
    refine ⟨?_, hr.ne_zero⟩
    calc ∏ p ∈ S, p ∣ ∏ p ∈ r.primeFactors, p :=
          Finset.prod_dvd_prod_of_subset _ _ _ hS
      _ = r := Nat.prod_primeFactors_of_squarefree hr

/-- Divisor sums over a squarefree `r` are powerset sums over its prime
factors. -/
private lemma sum_divisors_eq_sum_powerset {r : ℕ} (hr : Squarefree r)
    (f : ℕ → ℝ) :
    ∑ d ∈ r.divisors, f d
      = ∑ S ∈ r.primeFactors.powerset, f (∏ p ∈ S, p) := by
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p)
      ↑r.primeFactors.powerset := by
    intro X hX Y hY hXY
    rw [Finset.mem_coe, Finset.mem_powerset] at hX hY
    have hXp : ∀ p ∈ X, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactors (hX hp)
    have hYp : ∀ p ∈ Y, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactors (hY hp)
    calc X = (∏ p ∈ X, p).primeFactors := (Nat.primeFactors_prod hXp).symm
      _ = (∏ p ∈ Y, p).primeFactors := congrArg Nat.primeFactors hXY
      _ = Y := Nat.primeFactors_prod hYp
  rw [divisors_eq_powerset_image hr, Finset.sum_image hinj]

/-- **The `h`-expansion.** For squarefree `r` with all prime factors `≥ 3`,
`1/g(r) = (∑_{d ∣ r} ∏_{p ∣ d} (p−2)⁻¹) / φ(r)` — the Möbius-style expansion
of `∏(p−1)/(p−2)` into the divisor sum of `h(d) = ∏_{p ∣ d} (p−2)⁻¹`. -/
private lemma inv_gMult_expand {r : ℕ} (hrsq : Squarefree r)
    (hp3 : ∀ p ∈ r.primeFactors, 3 ≤ p) :
    ((gMult r : ℝ))⁻¹
      = (∑ d ∈ r.divisors, ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * ((Nat.totient r : ℝ))⁻¹ := by
  classical
  -- divisor sum → powerset sum
  have hsum : (∑ d ∈ r.divisors, ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
      = ∑ S ∈ r.primeFactors.powerset, ∏ p ∈ S, ((p : ℝ) - 2)⁻¹ := by
    rw [sum_divisors_eq_sum_powerset hrsq]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.mem_powerset] at hS
    rw [Nat.primeFactors_prod
      (fun p hp => Nat.prime_of_mem_primeFactors (hS hp))]
  -- powerset sum → Euler product
  have hpow : (∑ S ∈ r.primeFactors.powerset, ∏ p ∈ S, ((p : ℝ) - 2)⁻¹)
      = ∏ p ∈ r.primeFactors, (1 + ((p : ℝ) - 2)⁻¹) := by
    have h := Finset.prod_add (fun p : ℕ => ((p : ℝ) - 2)⁻¹)
      (fun _ => (1 : ℝ)) r.primeFactors
    simp only [Finset.prod_const_one, mul_one] at h
    rw [← h]
    exact Finset.prod_congr rfl fun p _ => by ring
  rw [hsum, hpow, gMult_cast hp3, totient_squarefree_cast hrsq,
    ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3 p hp
  have h2 : ((p : ℝ) - 2) ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
  have h1 : ((p : ℝ) - 1) ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
  field_simp
  ring

/-! ## The divisor-fibre reindex on `sqfCop` -/

/-- **Divisor-fibre reindex** (generalizes `sqfCop_dvd_reindex` from prime `p`
to arbitrary `d > 0`). Reindexing `r = d·b` over the `d`-divisible part of
`sqfCop`, using `φ(d·b) = φ(d)·φ(b)` (squarefree `⇒ d ⊥ b`) and the
antitonicity of the weight `g`. -/
theorem sqfCop_dvd_reindex_gen (k R : ℕ) (T : ℝ) (d : ℕ) (hd : 0 < d)
    (g : ℕ → ℝ) (hg_nonneg : ∀ n, 0 ≤ g n)
    (hg_anti : ∀ a b : ℕ, 0 < b → a ∣ b → g b ≤ g a) :
    (∑ r ∈ sqfCop (R0 k R T) (W k),
        if d ∣ r then g r / (Nat.totient r : ℝ) else 0)
      ≤ (Nat.totient d : ℝ)⁻¹
          * ∑ r ∈ sqfCop (R0 k R T) (W k), g r / (Nat.totient r : ℝ) := by
  classical
  set S := sqfCop (R0 k R T) (W k) with hSdef
  set filt := S.filter (fun r => d ∣ r) with hfilt
  have hφd : (0 : ℝ) < (Nat.totient d : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hd
  have hmem : ∀ r ∈ filt,
      r < R0 k R T ∧ Squarefree r ∧ Nat.Coprime r (W k) ∧ d ∣ r := by
    intro r hr
    rw [hfilt, Finset.mem_filter] at hr
    obtain ⟨hrS, hdr⟩ := hr
    rw [hSdef, sqfCop, Finset.mem_filter, Finset.mem_range] at hrS
    exact ⟨hrS.1, hrS.2.1, hrS.2.2, hdr⟩
  have hLHS : (∑ r ∈ S, if d ∣ r then g r / (Nat.totient r : ℝ) else 0)
      = ∑ r ∈ filt, g r / (Nat.totient r : ℝ) := (Finset.sum_filter _ _).symm
  rw [hLHS]
  have hb_mem : ∀ r ∈ filt, r / d ∈ S := by
    intro r hr
    obtain ⟨hrlt, hsqf, hcw, hdr⟩ := hmem r hr
    have hbdvd : (r / d) ∣ r :=
      ⟨d, by rw [mul_comm]; exact (Nat.mul_div_cancel' hdr).symm⟩
    rw [hSdef, sqfCop, Finset.mem_filter, Finset.mem_range]
    exact ⟨lt_of_le_of_lt (Nat.div_le_self r d) hrlt,
      Squarefree.squarefree_of_dvd hbdvd hsqf,
      Nat.Coprime.coprime_dvd_left hbdvd hcw⟩
  have hterm : ∀ r ∈ filt,
      g r / (Nat.totient r : ℝ)
        ≤ (Nat.totient d : ℝ)⁻¹
            * (g (r / d) / (Nat.totient (r / d) : ℝ)) := by
    intro r hr
    obtain ⟨hrlt, hsqf, hcw, hdr⟩ := hmem r hr
    set b := r / d with hbdef
    have hrdb : r = d * b := (Nat.mul_div_cancel' hdr).symm
    have hrpos : 0 < r := Nat.pos_of_ne_zero hsqf.ne_zero
    have hbpos : 0 < b := by
      rcases Nat.eq_zero_or_pos b with hb0 | hb0
      · rw [hb0, mul_zero] at hrdb; omega
      · exact hb0
    have hbdvd : b ∣ r :=
      ⟨d, by rw [mul_comm]; exact (Nat.mul_div_cancel' hdr).symm⟩
    have hcop_db : Nat.Coprime d b :=
      Nat.coprime_of_squarefree_mul (by rw [← hrdb]; exact hsqf)
    have hφr : (Nat.totient r : ℝ)
        = (Nat.totient d : ℝ) * (Nat.totient b : ℝ) := by
      have h1 : Nat.totient r = Nat.totient d * Nat.totient b := by
        rw [hrdb, Nat.totient_mul hcop_db]
      rw [h1, Nat.cast_mul]
    have hφb : (0 : ℝ) < (Nat.totient b : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hbpos
    have hgle : g r ≤ g b := hg_anti b r hrpos hbdvd
    rw [hφr, div_le_iff₀ (mul_pos hφd hφb)]
    have hrewrite : (Nat.totient d : ℝ)⁻¹ * (g b / (Nat.totient b : ℝ))
        * ((Nat.totient d : ℝ) * (Nat.totient b : ℝ)) = g b := by
      field_simp
    rw [hrewrite]
    exact hgle
  calc (∑ r ∈ filt, g r / (Nat.totient r : ℝ))
      ≤ ∑ r ∈ filt, (Nat.totient d : ℝ)⁻¹
          * (g (r / d) / (Nat.totient (r / d) : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (Nat.totient d : ℝ)⁻¹
          * ∑ r ∈ filt, g (r / d) / (Nat.totient (r / d) : ℝ) := by
        rw [Finset.mul_sum]
    _ = (Nat.totient d : ℝ)⁻¹
          * ∑ b ∈ filt.image (fun r => r / d),
              g b / (Nat.totient b : ℝ) := by
        congr 1
        have hinj : Set.InjOn (fun r => r / d) (filt : Set ℕ) := by
          intro x hx y hy hxy
          simp only [Finset.mem_coe] at hx hy
          obtain ⟨_, _, _, hdx⟩ := hmem x hx
          obtain ⟨_, _, _, hdy⟩ := hmem y hy
          have e1 : d * (x / d) = x := Nat.mul_div_cancel' hdx
          have e2 : d * (y / d) = y := Nat.mul_div_cancel' hdy
          have hxy' : x / d = y / d := hxy
          rw [← e1, ← e2, hxy']
        rw [Finset.sum_image hinj]
    _ ≤ (Nat.totient d : ℝ)⁻¹
          * ∑ b ∈ S, g b / (Nat.totient b : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hφd.le)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro b hb
          rw [Finset.mem_image] at hb
          obtain ⟨r, hr, rfl⟩ := hb
          exact hb_mem r hr
        · intro b hbS _
          have hbpos : 0 < b := by
            rw [hSdef, sqfCop, Finset.mem_filter] at hbS
            exact Nat.pos_of_ne_zero hbS.2.1.ne_zero
          have hφb : (0 : ℝ) < (Nat.totient b : ℝ) := by
            exact_mod_cast Nat.totient_pos.mpr hbpos
          exact div_nonneg (hg_nonneg b) hφb.le

/-! ## `A_g` and the sum-level `φ/g` comparison -/

/-- `A_g = ∑_{r < R₀ sqfree, (r,W)=1} fWt(r)² / g(r)` — the `g`-weighted
analogue of `A₁`. -/
noncomputable def Ag (k R : ℕ) (T : ℝ) : ℝ :=
  ∑ r ∈ sqfCop (R0 k R T) (W k), (fWt k R r) ^ 2 / (gMult r : ℝ)

lemma Ag_nonneg (k R : ℕ) (T : ℝ) : 0 ≤ Ag k R T :=
  Finset.sum_nonneg fun _ _ =>
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- **Node C.3, sum level.** `A_g ≤ A₁·(1 + 8/D₀)`: expand
`1/g(r) = (∑_{d ∣ r} h(d))/φ(r)`, swap sums, reindex the `d ∣ r` fibre by
`r = d·c` (giving `≤ A₁/φ(d)` per `d`), and bound the `d > 1` tail
`∑ h(d)/φ(d) ≤ ∑ 2^{ω(d)} ∏ (p−1)⁻² ≤ 8/D₀` by `euler_tail_L` at `L = 2`. -/
theorem Ag_le_A1_mul (k R : ℕ) (T : ℝ) (hk : 1 ≤ k) (hR : 2 ≤ R)
    (hD : 12 * k ^ 2 ≤ D₀ k) :
    Ag k R T ≤ A1 k R (W k) T * (1 + 8 / (D₀ k : ℝ)) := by
  classical
  have hD12 : 12 ≤ D₀ k := le_trans (by nlinarith) hD
  have hDpos : (0 : ℝ) < (D₀ k : ℝ) := by
    exact_mod_cast (by omega : 0 < D₀ k)
  have hA1nn : 0 ≤ A1 k R (W k) T := A1_nonneg k R (W k) T
  -- Degenerate case: empty index range.
  rcases Nat.eq_zero_or_pos (R0 k R T) with hR₀0 | hR₀pos
  · have hempty : sqfCop (R0 k R T) (W k) = ∅ := by
      rw [hR₀0, sqfCop, Finset.range_zero, Finset.filter_empty]
    have hAg0 : Ag k R T = 0 := by rw [Ag, hempty, Finset.sum_empty]
    have hA10 : A1 k R (W k) T = 0 := by rw [A1, hempty, Finset.sum_empty]
    rw [hAg0, hA10, zero_mul]
  -- Notation.
  set S := sqfCop (R0 k R T) (W k) with hSdef
  have hmemS : ∀ r ∈ S, r < R0 k R T ∧ Squarefree r ∧ Nat.Coprime r (W k) := by
    intro r hr
    rw [hSdef, sqfCop, Finset.mem_filter, Finset.mem_range] at hr
    exact ⟨hr.1, hr.2.1, hr.2.2⟩
  have hA1S : A1 k R (W k) T
      = ∑ r ∈ S, (fWt k R r) ^ 2 / (Nat.totient r : ℝ) := rfl
  -- Step 1: per-`r` expansion into a guarded divisor sum over the range.
  have hexp : ∀ r ∈ S, (fWt k R r) ^ 2 / (gMult r : ℝ)
      = ∑ t ∈ Finset.range (R0 k R T + 1),
          if t ∣ r then
            (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
              * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ))
          else 0 := by
    intro r hr
    obtain ⟨hrlt, hrsq, hrcop⟩ := hmemS r hr
    have hp3r : ∀ p ∈ r.primeFactors, 3 ≤ p := by
      intro p hp
      have := D₀_lt_of_prime_dvd_coprime hrcop
        (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
      omega
    calc (fWt k R r) ^ 2 / (gMult r : ℝ)
        = (fWt k R r) ^ 2 * ((gMult r : ℝ))⁻¹ := div_eq_mul_inv _ _
      _ = (∑ d ∈ r.divisors, ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ)) := by
          rw [inv_gMult_expand hrsq hp3r, div_eq_mul_inv]
          ring
      _ = ∑ d ∈ r.divisors,
            (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ)) := by
          rw [Finset.sum_mul]
      _ = _ := sum_divisors_eq_sum_range hrsq.ne_zero (by omega) _
  -- Step 2: swap the two sums.
  have hswap : Ag k R T
      = ∑ t ∈ Finset.range (R0 k R T + 1), ∑ r ∈ S,
          if t ∣ r then
            (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
              * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ))
          else 0 := by
    rw [Ag, ← hSdef, Finset.sum_congr rfl hexp, Finset.sum_comm]
  -- Step 3: split off the `t = 1` term (which equals `A₁`).
  have h1mem : 1 ∈ Finset.range (R0 k R T + 1) := by
    rw [Finset.mem_range]; omega
  have hsplit := Finset.sum_erase_add (Finset.range (R0 k R T + 1))
    (fun t => ∑ r ∈ S,
      if t ∣ r then
        (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
          * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ))
      else 0) h1mem
  have hone : (∑ r ∈ S,
      if 1 ∣ r then
        (∏ p ∈ (1 : ℕ).primeFactors, ((p : ℝ) - 2)⁻¹)
          * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ))
      else 0) = A1 k R (W k) T := by
    rw [hA1S]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [if_pos (one_dvd r), Nat.primeFactors_one, Finset.prod_empty, one_mul]
  -- Step 4: the `t ≠ 1` tail is supported on nice moduli.
  have hvanish : ∀ t ∈ (Finset.range (R0 k R T + 1)).erase 1,
      (∑ r ∈ S,
        if t ∣ r then
          (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ))
        else 0) ≠ 0 →
      (Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p) := by
    intro t _ hne
    by_contra hnot
    apply hne
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [if_neg]
    intro htr
    obtain ⟨-, hrsq, hrcop⟩ := hmemS r hr
    exact hnot ⟨hrsq.squarefree_of_dvd htr, fun p hp =>
      D₀_lt_of_prime_dvd_coprime (Nat.Coprime.coprime_dvd_left htr hrcop)
        (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)⟩
  have hrestrict : (∑ t ∈ (Finset.range (R0 k R T + 1)).erase 1, ∑ r ∈ S,
        if t ∣ r then
          (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ))
        else 0)
      = ∑ t ∈ ((Finset.range (R0 k R T + 1)).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p)).erase 1,
        ∑ r ∈ S,
          if t ∣ r then
            (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
              * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ))
          else 0 := by
    rw [← Finset.filter_erase, Finset.sum_filter_of_ne hvanish]
  -- Step 5: bound each nice tail term by `h(t)/φ(t) · A₁`.
  set Tamb := ((Finset.range (R0 k R T + 1)).filter
      (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p)).erase 1
    with hTamb
  have hTmem : ∀ t ∈ Tamb, t ≠ 1 ∧ Squarefree t
      ∧ (∀ p ∈ t.primeFactors, D₀ k < p) := by
    intro t ht
    rw [hTamb, Finset.mem_erase, Finset.mem_filter] at ht
    exact ⟨ht.1, ht.2.2.1, ht.2.2.2⟩
  have hterm_le : ∀ t ∈ Tamb,
      (∑ r ∈ S,
        if t ∣ r then
          (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ))
        else 0)
      ≤ ((∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
          * (Nat.totient t : ℝ)⁻¹) * A1 k R (W k) T := by
    intro t ht
    obtain ⟨-, htsq, htbig⟩ := hTmem t ht
    have htpos : 0 < t := Nat.pos_of_ne_zero htsq.ne_zero
    have hHnn : 0 ≤ ∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹ := by
      refine Finset.prod_nonneg fun p hp => ?_
      have : (12 : ℝ) < (p : ℝ) := by
        have := htbig p hp; have := hD12; exact_mod_cast (by omega : 12 < p)
      have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      positivity
    have hpull : (∑ r ∈ S,
        if t ∣ r then
          (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ))
        else 0)
        = (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ∑ r ∈ S,
              if t ∣ r then (fWt k R r) ^ 2 / (Nat.totient r : ℝ) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [mul_ite, mul_zero]
    rw [hpull, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hHnn
    have hreidx := sqfCop_dvd_reindex_gen k R T t htpos
      (fun n => (fWt k R n) ^ 2) (fun n => sq_nonneg _) (fWt_sq_anti k R hR)
    rw [hA1S]
    exact hreidx
  -- Step 6: the nice tail weights are dominated by the `L = 2` Euler tail.
  have hweight : ∀ t ∈ Tamb,
      (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹) * (Nat.totient t : ℝ)⁻¹
        ≤ (2 : ℝ) ^ t.primeFactors.card
            * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 := by
    intro t ht
    obtain ⟨-, htsq, htbig⟩ := hTmem t ht
    have hφ : ((Nat.totient t : ℝ))⁻¹
        = ∏ p ∈ t.primeFactors, ((p : ℝ) - 1)⁻¹ := by
      rw [totient_squarefree_cast htsq, ← Finset.prod_inv_distrib]
    rw [hφ, ← Finset.prod_mul_distrib]
    have hRHS : (2 : ℝ) ^ t.primeFactors.card
        * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2
        = ∏ p ∈ t.primeFactors, (2 * (((p : ℝ) - 1)⁻¹) ^ 2) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    rw [hRHS]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have hp12 : 12 < p := by have := htbig p hp; omega
      have h2 : (0 : ℝ) < (p : ℝ) - 2 := by
        have : (12 : ℝ) < (p : ℝ) := by exact_mod_cast hp12
        linarith
      have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    · have hp12 : 12 < p := by have := htbig p hp; omega
      have hp' : (12 : ℝ) < (p : ℝ) := by exact_mod_cast hp12
      have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hkey : ((p : ℝ) - 2)⁻¹ ≤ 2 * ((p : ℝ) - 1)⁻¹ := by
        have hdiv : (1 : ℝ) / ((p : ℝ) - 2) ≤ 2 / ((p : ℝ) - 1) := by
          rw [div_le_div_iff₀ h2 h1]
          linarith
        calc ((p : ℝ) - 2)⁻¹ = 1 / ((p : ℝ) - 2) := (inv_eq_one_div _)
          _ ≤ 2 / ((p : ℝ) - 1) := hdiv
          _ = 2 * ((p : ℝ) - 1)⁻¹ := by rw [div_eq_mul_inv]
      calc ((p : ℝ) - 2)⁻¹ * ((p : ℝ) - 1)⁻¹
          ≤ (2 * ((p : ℝ) - 1)⁻¹) * ((p : ℝ) - 1)⁻¹ :=
            mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr h1.le)
        _ = 2 * (((p : ℝ) - 1)⁻¹) ^ 2 := by ring
  -- Step 7: assemble the tail bound via `euler_tail_L` at `L = 2`.
  have htail : (∑ t ∈ Tamb, ∑ r ∈ S,
        if t ∣ r then
          (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ))
        else 0)
      ≤ (8 / (D₀ k : ℝ)) * A1 k R (W k) T := by
    calc (∑ t ∈ Tamb, ∑ r ∈ S,
          if t ∣ r then
            (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
              * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ))
          else 0)
        ≤ ∑ t ∈ Tamb,
            ((∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (Nat.totient t : ℝ)⁻¹) * A1 k R (W k) T :=
          Finset.sum_le_sum hterm_le
      _ = (∑ t ∈ Tamb,
            (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (Nat.totient t : ℝ)⁻¹) * A1 k R (W k) T := by
          rw [Finset.sum_mul]
      _ ≤ (8 / (D₀ k : ℝ)) * A1 k R (W k) T := by
          refine mul_le_mul_of_nonneg_right ?_ hA1nn
          have hsum_le : (∑ t ∈ Tamb,
              (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
                * (Nat.totient t : ℝ)⁻¹)
              ≤ ∑ t ∈ Tamb, (2 : ℝ) ^ t.primeFactors.card
                  * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 :=
            Finset.sum_le_sum hweight
          have heuler := euler_tail_L k (R0 k R T + 1) 2 (by norm_num)
            (by
              have : (8 : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast (by omega : 8 ≤ D₀ k)
              linarith)
          rw [hTamb]
          calc (∑ t ∈ ((Finset.range (R0 k R T + 1)).filter
                (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p)).erase 1,
                (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
                  * (Nat.totient t : ℝ)⁻¹)
              ≤ ∑ t ∈ ((Finset.range (R0 k R T + 1)).filter
                (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p)).erase 1,
                (2 : ℝ) ^ t.primeFactors.card
                  * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 := by
                rw [← hTamb]; exact hsum_le
            _ ≤ 4 * 2 / (D₀ k : ℝ) := heuler
            _ = 8 / (D₀ k : ℝ) := by norm_num
  -- Conclude.
  have hAg_split : Ag k R T
      = (∑ t ∈ Tamb, ∑ r ∈ S,
          if t ∣ r then
            (∏ p ∈ t.primeFactors, ((p : ℝ) - 2)⁻¹)
              * ((fWt k R r) ^ 2 / (Nat.totient r : ℝ))
          else 0) + A1 k R (W k) T := by
    rw [hswap, ← hsplit, hone, hrestrict, hTamb]
  rw [hAg_split]
  have := htail
  nlinarith [hA1nn, hDpos]

/-! ## `Gdiag` and the box relaxation -/

/-- `G`-diag: the diagonal `G`-sum of the S2 inner-bound design,
`∑_{u ∈ 𝒟, uₘ = 1} ∏_{i ≠ m} fTilde(uᵢ)²/g(uᵢ)`. -/
noncomputable def Gdiag (k R : ℕ) (T : ℝ) (m : Fin k) : ℝ :=
  ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
    ∏ i ∈ Finset.univ.erase m,
      (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ)

/-- **Box relaxation.** `Gdiag ≤ A_g^{k−1}`: the `fTilde` cutoff confines the
nonzero terms to the box `∏_{i ≠ m} sqfCop(R₀,W) × {1}`, whose full
(nonnegative) sum factors as `A_g^{k−1}`. -/
theorem Gdiag_le_Ag_pow (k R : ℕ) (T : ℝ) (m : Fin k) :
    Gdiag k R T m ≤ (Ag k R T) ^ (k - 1) := by
  classical
  set S₀ := sqfCop (R0 k R T) (W k) with hS₀
  set f : Fin k → ℕ → ℝ := fun i r =>
    if i = m then 1 else (fTilde k R T r) ^ 2 / (gMult r : ℝ) with hf
  set t : Fin k → Finset ℕ := fun i => if i = m then {1} else S₀ with ht
  -- The `erase m` product is the full product of the `f i`.
  have hF : ∀ u : Fin k → ℕ,
      (∏ i, f i (u i))
        = ∏ i ∈ Finset.univ.erase m,
            (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ) := by
    intro u
    rw [← Finset.mul_prod_erase Finset.univ (fun i => f i (u i))
      (Finset.mem_univ m)]
    have h1 : f m (u m) = 1 := by rw [hf]; simp
    rw [h1, one_mul]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i ≠ m := (Finset.mem_erase.mp hi).1
    rw [hf]; simp [hne]
  have hf_nonneg : ∀ (i : Fin k) (r : ℕ), 0 ≤ f i r := by
    intro i r
    rw [hf]
    by_cases h : i = m
    · simp [h]
    · simp only [h, if_false]
      exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hF_nonneg : ∀ u : Fin k → ℕ, 0 ≤ ∏ i, f i (u i) :=
    fun u => Finset.prod_nonneg fun i _ => hf_nonneg i (u i)
  -- Restrict to the guarded subset (all off-`m` coordinates in the box).
  have hGdiag : Gdiag k R T m
      = ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          ∏ i, f i (u i) := by
    rw [Gdiag]
    exact Finset.sum_congr rfl fun u _ => (hF u).symm
  have hguard : ∀ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
      (∏ i, f i (u i)) ≠ 0 → (∀ i ∈ Finset.univ.erase m, u i ∈ S₀) := by
    intro u _ hne
    by_contra hnot
    apply hne
    push Not at hnot
    obtain ⟨i₀, hi₀mem, hi₀⟩ := hnot
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
    have hne' : i₀ ≠ m := (Finset.mem_erase.mp hi₀mem).1
    rw [hf]
    simp only [hne', if_false]
    rw [fTilde, ← hS₀, if_neg hi₀]
    norm_num
  have hrestrict : (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
        ∏ i, f i (u i))
      = ∑ u ∈ ((kSieveIndex k R (W k)).filter (fun u => u m = 1)).filter
          (fun u => ∀ i ∈ Finset.univ.erase m, u i ∈ S₀),
          ∏ i, f i (u i) :=
    (Finset.sum_filter_of_ne hguard).symm
  -- Guarded subset ⊆ box.
  have hsub : ((kSieveIndex k R (W k)).filter (fun u => u m = 1)).filter
      (fun u => ∀ i ∈ Finset.univ.erase m, u i ∈ S₀)
      ⊆ Fintype.piFinset t := by
    intro u hu
    rw [Finset.mem_filter, Finset.mem_filter] at hu
    obtain ⟨⟨-, hum⟩, hbox⟩ := hu
    rw [Fintype.mem_piFinset]
    intro i
    by_cases h : i = m
    · subst h
      simp only [ht, if_pos rfl, Finset.mem_singleton]
      exact hum
    · simp only [ht, if_neg h]
      exact hbox i (Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩)
  -- The box sum factors into `A_g^{k−1}`.
  have hbox_eq : (∑ u ∈ Fintype.piFinset t, ∏ i, f i (u i))
      = (Ag k R T) ^ (k - 1) := by
    rw [← Finset.prod_univ_sum]
    have hcoord : ∀ i : Fin k,
        (∑ j ∈ t i, f i j) = if i = m then 1 else Ag k R T := by
      intro i
      by_cases h : i = m
      · subst h
        simp [ht, hf]
      · simp only [ht, hf, h, if_false]
        rw [show Ag k R T
            = ∑ r ∈ S₀, (fWt k R r) ^ 2 / (gMult r : ℝ) from rfl]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [show fTilde k R T r = if r ∈ S₀ then fWt k R r else 0 from rfl,
          if_pos hr]
    rw [Finset.prod_congr rfl fun i _ => hcoord i]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m), if_pos rfl,
      one_mul]
    have hconst : ∀ i ∈ Finset.univ.erase m,
        (if i = m then (1 : ℝ) else Ag k R T) = Ag k R T := by
      intro i hi
      rw [if_neg (Finset.mem_erase.mp hi).1]
    rw [Finset.prod_congr rfl hconst, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ,
      Fintype.card_fin]
  -- Assemble.
  calc Gdiag k R T m
      = ∑ u ∈ ((kSieveIndex k R (W k)).filter (fun u => u m = 1)).filter
          (fun u => ∀ i ∈ Finset.univ.erase m, u i ∈ S₀),
          ∏ i, f i (u i) := by rw [hGdiag, hrestrict]
    _ ≤ ∑ u ∈ Fintype.piFinset t, ∏ i, f i (u i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ => hF_nonneg u
    _ = (Ag k R T) ^ (k - 1) := hbox_eq

/-- `(1+a)^n ≤ 1 + 2na` for `0 ≤ a` with `2na ≤ 1` (elementary induction). -/
private lemma one_add_pow_le {a : ℝ} (ha : 0 ≤ a) :
    ∀ n : ℕ, 2 * (n : ℝ) * a ≤ 1 → (1 + a) ^ n ≤ 1 + 2 * (n : ℝ) * a := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ i ih =>
      intro h
      have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
      rw [hcast] at h ⊢
      have hia : 2 * (i : ℝ) * a ≤ 1 := by nlinarith
      have hih := ih hia
      have h1a : (0 : ℝ) ≤ 1 + a := by linarith
      have h2ia : 2 * (i : ℝ) * a * a ≤ 1 * a :=
        mul_le_mul_of_nonneg_right hia ha
      calc (1 + a) ^ (i + 1) = (1 + a) ^ i * (1 + a) := by rw [pow_succ]
        _ ≤ (1 + 2 * (i : ℝ) * a) * (1 + a) :=
            mul_le_mul_of_nonneg_right hih h1a
        _ = 1 + 2 * (i : ℝ) * a + a + 2 * (i : ℝ) * a * a := by ring
        _ ≤ 1 + 2 * ((i : ℝ) + 1) * a := by nlinarith

/-- **Node C.3 — `Gdiag_le`.** The diagonal `G`-sum is at most `2·A₁^{k−1}`:
box relaxation to `A_g^{k−1}`, the sum-level comparison
`A_g ≤ A₁·(1 + 8/D₀)`, and `(1 + 8/D₀)^{k−1} ≤ 2` since
`16(k−1) ≤ 12k² ≤ D₀`. -/
theorem Gdiag_le (k R : ℕ) (T : ℝ) (m : Fin k) (hR : 2 ≤ R)
    (hD : 12 * k ^ 2 ≤ D₀ k) :
    Gdiag k R T m ≤ 2 * (A1 k R (W k) T) ^ (k - 1) := by
  have hk : 1 ≤ k := m.pos
  have hD12 : 12 ≤ D₀ k := le_trans (by nlinarith) hD
  have hDpos : (0 : ℝ) < (D₀ k : ℝ) := by
    exact_mod_cast (by omega : 0 < D₀ k)
  have ha : (0 : ℝ) ≤ 8 / (D₀ k : ℝ) := by positivity
  have hAgnn : 0 ≤ Ag k R T := Ag_nonneg k R T
  have hA1nn : 0 ≤ A1 k R (W k) T := A1_nonneg k R (W k) T
  have h16 : 2 * ((k - 1 : ℕ) : ℝ) * (8 / (D₀ k : ℝ)) ≤ 1 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : ((j + 1) - 1 : ℕ) = j := by omega
    rw [hj]
    have hnat : 16 * j ≤ D₀ (j + 1) :=
      le_trans (by nlinarith : 16 * j ≤ 12 * (j + 1) ^ 2) hD
    have hcast : (16 : ℝ) * (j : ℝ) ≤ (D₀ (j + 1) : ℝ) := by
      exact_mod_cast hnat
    have heq : 2 * (j : ℝ) * (8 / (D₀ (j + 1) : ℝ))
        = 16 * (j : ℝ) / (D₀ (j + 1) : ℝ) := by ring
    rw [heq, div_le_one hDpos]
    exact hcast
  have h5 : (1 + 8 / (D₀ k : ℝ)) ^ (k - 1) ≤ 2 := by
    have := one_add_pow_le ha (k - 1) h16
    linarith
  calc Gdiag k R T m
      ≤ (Ag k R T) ^ (k - 1) := Gdiag_le_Ag_pow k R T m
    _ ≤ (A1 k R (W k) T * (1 + 8 / (D₀ k : ℝ))) ^ (k - 1) :=
        pow_le_pow_left₀ hAgnn (Ag_le_A1_mul k R T hk hR hD) _
    _ = (A1 k R (W k) T) ^ (k - 1) * (1 + 8 / (D₀ k : ℝ)) ^ (k - 1) :=
        mul_pow _ _ _
    _ ≤ (A1 k R (W k) T) ^ (k - 1) * 2 :=
        mul_le_mul_of_nonneg_left h5 (pow_nonneg hA1nn _)
    _ = 2 * (A1 k R (W k) T) ^ (k - 1) := mul_comm _ _

end Salt.Maynard
