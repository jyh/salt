/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.PairSieveMixed

/-!
# HB 1983 §3, Lemma 8′ — the mixed residue count (WP1 / R2, the atomic residual)

This file discharges the single residual left open by `Salt.HB.hb_lemma8′`
(`Salt.HB.PairSieveMixed`): the **mixed cofactor-sift residue count**.  For a
squarefree modulus `d` the number of residues `r < d·d₁·d₂` obeying the AP-pair
conditions `d₁ ∣ r`, `d₂ ∣ (r+2)` together with the mixed cofactor condition
`d ∣ (r/d₁)·((r+2)/d₂)` is the mixed local product

  `ρ_mix(d) = ∏_{p ∣ d, p prime} (if p ∣ 2 d₁ d₂ then 1 else 2)`.

Unlike the `z`-rough twin case (`Salt.HB.card_apResidues`, count `ρ(d)`), here
`d` may share prime factors with `d₁ d₂`; at such a prime the honest local count
drops from `2` to `1` (one cofactor factor is forced nonzero), which is exactly
the mixed density `ν(p) = 1/p`.

## Route

The AP-pair conditions pin `r ≡ c (mod d₁ d₂)` for a fixed class `c` with
`d₁ ∣ c`, `d₂ ∣ (c+2)`; writing `r = c + t·d₁d₂` (`t < d`) turns the cofactor
condition into `d ∣ K(t)` for the fixed quadratic `K(t) = (a₁ + t d₂)(a₂ + t d₁)`
with `a₁ = c/d₁`, `a₂ = (c+2)/d₂` (so `a₁ d₁ = c`, `a₂ d₂ = c+2`, hence
`a₂ d₂ = a₁ d₁ + 2`).  The count `#{t < d : d ∣ K(t)}` is multiplicative over the
squarefree `d` (CRT), and the per-prime value is `1` at `p ∣ 2 d₁ d₂`, `2`
otherwise — a four-case root count in the field `ZMod p`.

Feeding the resulting `|rem d| ≤ 2 ρ_mix(d) ≤ 2^{ω(d)+1}` through the landed
`Salt.HB.congCount_Ioc_bound` and the crude `Σ 3^ω` machinery yields the concrete
`E = 2 z⁸` bound and closes `Salt.HB.hb_lemma8'` unconditionally.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.omega

namespace Salt.HB

/-! ## §1 — the fixed quadratic `K` and its residue-count `rhoK` -/

/-- The fixed mixed quadratic `K(t) = (a₁ + t d₂)(a₂ + t d₁)` (subtraction-free,
so `d ∣ K t` is a clean `[MOD d]` congruence). -/
def Kpoly (a₁ a₂ d₁ d₂ t : ℕ) : ℕ := (a₁ + t * d₂) * (a₂ + t * d₁)

/-- The mixed residue count `#{t < d : d ∣ K(t)}`. -/
def rhoK (a₁ a₂ d₁ d₂ d : ℕ) : ℕ :=
  ((Finset.range d).filter (fun t => d ∣ Kpoly a₁ a₂ d₁ d₂ t)).card

section RhoK
variable (a₁ a₂ d₁ d₂ : ℕ)

/-- `d ∣ K t` depends only on `t (mod q)` when `q = d` — the local periodicity
used by CRT. -/
lemma dvd_Kpoly_mod (q t : ℕ) :
    q ∣ Kpoly a₁ a₂ d₁ d₂ t ↔ q ∣ Kpoly a₁ a₂ d₁ d₂ (t % q) := by
  have hmod : t % q ≡ t [MOD q] := Nat.mod_modEq t q
  have hK : Kpoly a₁ a₂ d₁ d₂ (t % q) ≡ Kpoly a₁ a₂ d₁ d₂ t [MOD q] :=
    Nat.ModEq.mul ((hmod.mul_right d₂).add_left a₁) ((hmod.mul_right d₁).add_left a₂)
  constructor
  · intro h; exact Nat.modEq_zero_iff_dvd.mp (hK.trans (Nat.modEq_zero_iff_dvd.mpr h))
  · intro h; exact Nat.modEq_zero_iff_dvd.mp (hK.symm.trans (Nat.modEq_zero_iff_dvd.mpr h))

/-- `rhoK … 1 = 1`. -/
lemma rhoK_one : rhoK a₁ a₂ d₁ d₂ 1 = 1 := by
  unfold rhoK
  rw [Finset.filter_true_of_mem (fun t _ => one_dvd _), Finset.card_range]

/-- **CRT multiplicativity.**  `rhoK` is multiplicative over coprime moduli:
residues mod `a*b` correspond via CRT to pairs of residues mod `a` and mod `b`. -/
theorem rhoK_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hcop : a.Coprime b) :
    rhoK a₁ a₂ d₁ d₂ (a * b) = rhoK a₁ a₂ d₁ d₂ a * rhoK a₁ a₂ d₁ d₂ b := by
  unfold rhoK
  rw [← Finset.card_product]
  apply Finset.card_bij (fun t _ => (t % a, t % b))
  · -- maps into the product of filters
    intro t ht
    rw [mem_filter, mem_range] at ht
    obtain ⟨htlt, htdvd⟩ := ht
    rw [Finset.mem_product, mem_filter, mem_range, mem_filter, mem_range]
    have hda : a ∣ Kpoly a₁ a₂ d₁ d₂ t := dvd_trans (dvd_mul_right a b) htdvd
    have hdb : b ∣ Kpoly a₁ a₂ d₁ d₂ t := dvd_trans (dvd_mul_left b a) htdvd
    exact ⟨⟨Nat.mod_lt t ha.bot_lt, (dvd_Kpoly_mod a₁ a₂ d₁ d₂ a t).mp hda⟩,
           ⟨Nat.mod_lt t hb.bot_lt, (dvd_Kpoly_mod a₁ a₂ d₁ d₂ b t).mp hdb⟩⟩
  · -- injective
    intro t1 h1 t2 h2 heq
    rw [mem_filter, mem_range] at h1 h2
    simp only [Prod.mk.injEq] at heq
    have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨heq.1, heq.2⟩
    exact (Nat.mod_eq_of_lt h1.1) ▸ (Nat.mod_eq_of_lt h2.1) ▸ this
  · -- surjective
    rintro ⟨u, v⟩ huv
    rw [Finset.mem_product, mem_filter, mem_range, mem_filter, mem_range] at huv
    obtain ⟨⟨hult, hudvd⟩, ⟨hvlt, hvdvd⟩⟩ := huv
    obtain ⟨k, hku, hkv⟩ := Nat.chineseRemainder hcop u v
    set r := k % (a * b) with hr_def
    have hrx : r ≡ k [MOD a] := by
      rw [Nat.ModEq, hr_def, Nat.mod_mod_of_dvd _ (dvd_mul_right a b)]
    have hry : r ≡ k [MOD b] := by
      rw [Nat.ModEq, hr_def, Nat.mod_mod_of_dvd _ (dvd_mul_left b a)]
    have hrxx : r ≡ u [MOD a] := hrx.trans hku
    have hryy : r ≡ v [MOD b] := hry.trans hkv
    have hfx : r % a = u := by
      have h : r % a = u % a := hrxx; rwa [Nat.mod_eq_of_lt hult] at h
    have hfy : r % b = v := by
      have h : r % b = v % b := hryy; rwa [Nat.mod_eq_of_lt hvlt] at h
    refine ⟨r, ?_, Prod.ext hfx hfy⟩
    rw [mem_filter, mem_range]
    refine ⟨Nat.mod_lt k (Nat.pos_of_ne_zero (mul_ne_zero ha hb)), ?_⟩
    -- a*b ∣ K r  from a ∣ K r and b ∣ K r
    have hda : a ∣ Kpoly a₁ a₂ d₁ d₂ r := by
      rw [dvd_Kpoly_mod a₁ a₂ d₁ d₂ a r, hfx]; exact hudvd
    have hdb : b ∣ Kpoly a₁ a₂ d₁ d₂ r := by
      rw [dvd_Kpoly_mod a₁ a₂ d₁ d₂ b r, hfy]; exact hvdvd
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hda hdb

/-- **Product over prime factors.**  For squarefree `d`, `rhoK … d` factors as the
product of the per-prime counts. -/
lemma rhoK_prod_primeFactors :
    ∀ d : ℕ, Squarefree d →
      rhoK a₁ a₂ d₁ d₂ d = ∏ p ∈ d.primeFactors, rhoK a₁ a₂ d₁ d₂ p := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases eq_or_ne d 1 with rfl | hd1
    · rw [rhoK_one, Nat.primeFactors_one, Finset.prod_empty]
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
      obtain ⟨d', rfl⟩ := hpd
      have hcop : p.Coprime d' := (Nat.squarefree_mul_iff.mp hd).1
      have hd'sq : Squarefree d' := (Nat.squarefree_mul_iff.mp hd).2.2
      have hd'ne0 : d' ≠ 0 := hd'sq.ne_zero
      have hd'lt : d' < p * d' := by
        nlinarith [hp.two_le, Nat.pos_of_ne_zero hd'ne0]
      have hind := ih d' hd'lt hd'sq
      rw [rhoK_mul_of_coprime a₁ a₂ d₁ d₂ hp.ne_zero hd'ne0 hcop,
        Nat.primeFactors_mul hp.ne_zero hd'ne0,
        Finset.prod_union hcop.disjoint_primeFactors, hp.primeFactors, Finset.prod_singleton,
        hind]

/-! ## §2 — the per-prime value `rhoK p = if p ∣ 2 d₁ d₂ then 1 else 2` -/

/-- Bridge to the field: for `d > 0`, `rhoK` is the number of `ZMod d` roots of
the cast quadratic. -/
lemma rhoK_eq_zmod {d : ℕ} [NeZero d] :
    rhoK a₁ a₂ d₁ d₂ d
      = (univ.filter (fun u : ZMod d =>
          ((a₁ : ZMod d) + u * (d₂ : ZMod d)) * ((a₂ : ZMod d) + u * (d₁ : ZMod d)) = 0)).card := by
  unfold rhoK
  rw [← Finset.card_image_of_injective _ (ZMod.val_injective d)]
  congr 1
  ext t
  simp only [mem_filter, mem_range, Finset.mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨htlt, hdvd⟩
    refine ⟨(t : ZMod d), ?_, ?_⟩
    · have hz : ((Kpoly a₁ a₂ d₁ d₂ t : ℕ) : ZMod d) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      rw [Kpoly] at hz; push_cast at hz; exact hz
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt htlt]
  · rintro ⟨u, hpred, hval⟩
    refine ⟨hval ▸ ZMod.val_lt u, ?_⟩
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Kpoly]; push_cast
    rw [← hval, ZMod.natCast_zmod_val]
    exact hpred

/-- In a field `ZMod p`, a linear equation `β + u·γ = 0` with `γ ≠ 0` has exactly
one root. -/
lemma card_linear_root {p : ℕ} [Fact p.Prime] (β γ : ZMod p) (hγ : γ ≠ 0) :
    (univ.filter (fun u : ZMod p => β + u * γ = 0)).card = 1 := by
  have hset : (univ.filter (fun u : ZMod p => β + u * γ = 0)) = {-(β * γ⁻¹)} := by
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h
      have hu : u * γ = -β := by linear_combination h
      have h2 : u * γ * γ⁻¹ = -β * γ⁻¹ := by rw [hu]
      rw [mul_assoc, mul_inv_cancel₀ hγ, mul_one, neg_mul] at h2
      exact h2
    · intro h
      subst h
      rw [neg_mul, mul_assoc, inv_mul_cancel₀ hγ, mul_one, add_neg_cancel]
  rw [hset, Finset.card_singleton]

/-- `(2 : ZMod p) ≠ 0` for an odd prime `p`. -/
lemma two_ne_zero_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro hcontra
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hcontra
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    ((ZMod.natCast_eq_zero_iff 2 p).mp h2))

/-- **The per-prime mixed count.**  For the fixed quadratic with `a₂ d₂ = a₁ d₁ + 2`
(`d₁, d₂` odd coprime), the number of roots mod a prime `p` is `1` when
`p ∣ 2 d₁ d₂` (a shared or even prime — one cofactor factor is forced nonzero),
and `2` otherwise (two distinct honest twin roots). -/
lemma rhoK_prime {p : ℕ} (hp : p.Prime)
    (hrel : a₂ * d₂ = a₁ * d₁ + 2) (ho1 : Odd d₁) (ho2 : Odd d₂)
    (hcop12 : Nat.Coprime d₁ d₂) :
    rhoK a₁ a₂ d₁ d₂ p = if p ∣ 2 * (d₁ * d₂) then 1 else 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [rhoK_eq_zmod a₁ a₂ d₁ d₂]
  have hrelZ : (a₂ : ZMod p) * (d₂ : ZMod p) = (a₁ : ZMod p) * (d₁ : ZMod p) + 2 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) hrel
    push_cast at h; exact h
  set α₁ := (a₁ : ZMod p) with hα1def
  set α₂ := (a₂ : ZMod p) with hα2def
  set δ₁ := (d₁ : ZMod p) with hδ1def
  set δ₂ := (d₂ : ZMod p) with hδ2def
  -- split the product equation into the two linear factors
  have hsplit : (univ.filter (fun u : ZMod p => (α₁ + u * δ₂) * (α₂ + u * δ₁) = 0))
      = (univ.filter (fun u : ZMod p => α₁ + u * δ₂ = 0))
        ∪ (univ.filter (fun u : ZMod p => α₂ + u * δ₁ = 0)) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro u _
    simp only [mul_eq_zero]
  by_cases hpd1 : p ∣ d₁
  · -- p ∣ d₁ : one cofactor factor (α₂ + u δ₁) is constant α₂ ≠ 0
    rw [if_pos ((hpd1.mul_right d₂).mul_left 2)]
    have hpne2 : p ≠ 2 := by
      rintro rfl; obtain ⟨k, hk⟩ := ho1; obtain ⟨m, hm⟩ := hpd1; omega
    have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp hpne2
    have hpd2 : ¬ p ∣ d₂ := by
      intro h; have hg := Nat.dvd_gcd hpd1 h
      rw [hcop12.gcd_eq_one] at hg; exact hp.one_lt.ne' (Nat.dvd_one.mp hg)
    have hδ1 : δ₁ = 0 := (ZMod.natCast_eq_zero_iff d₁ p).mpr hpd1
    have hδ2 : δ₂ ≠ 0 := fun h => hpd2 ((ZMod.natCast_eq_zero_iff d₂ p).mp h)
    have hα2 : α₂ ≠ 0 := by
      intro h
      have hh : α₂ * δ₂ = 2 := by rw [hrelZ, hδ1, mul_zero, zero_add]
      rw [h, zero_mul] at hh; exact h2ne hh.symm
    have hB : (univ.filter (fun u : ZMod p => α₂ + u * δ₁ = 0)) = ∅ := by
      apply Finset.filter_false_of_mem; intro u _
      rw [hδ1, mul_zero, add_zero]; exact hα2
    rw [hsplit, hB, Finset.union_empty]
    exact card_linear_root α₁ δ₂ hδ2
  · by_cases hpd2 : p ∣ d₂
    · -- p ∣ d₂ : the other cofactor factor (α₁ + u δ₂) is constant α₁ ≠ 0
      rw [if_pos ((hpd2.mul_left d₁).mul_left 2)]
      have hpne2 : p ≠ 2 := by
        rintro rfl; obtain ⟨k, hk⟩ := ho2; obtain ⟨m, hm⟩ := hpd2; omega
      have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp hpne2
      have hδ2 : δ₂ = 0 := (ZMod.natCast_eq_zero_iff d₂ p).mpr hpd2
      have hδ1 : δ₁ ≠ 0 := fun h => hpd1 ((ZMod.natCast_eq_zero_iff d₁ p).mp h)
      have hα1 : α₁ ≠ 0 := by
        intro h
        have hh : (0 : ZMod p) = α₁ * δ₁ + 2 := by rw [← hrelZ, hδ2, mul_zero]
        rw [h, zero_mul, zero_add] at hh; exact h2ne hh.symm
      have hA : (univ.filter (fun u : ZMod p => α₁ + u * δ₂ = 0)) = ∅ := by
        apply Finset.filter_false_of_mem; intro u _
        rw [hδ2, mul_zero, add_zero]; exact hα1
      rw [hsplit, hA, Finset.empty_union]
      exact card_linear_root α₂ δ₁ hδ1
    · -- p ∤ d₁, p ∤ d₂
      have hδ1 : δ₁ ≠ 0 := fun h => hpd1 ((ZMod.natCast_eq_zero_iff d₁ p).mp h)
      have hδ2 : δ₂ ≠ 0 := fun h => hpd2 ((ZMod.natCast_eq_zero_iff d₂ p).mp h)
      by_cases hp2 : p = 2
      · -- p = 2 : the two factors coincide (α₁ = α₂, δ₁ = δ₂ = 1)
        have hmem : p ∣ 2 * (d₁ * d₂) := by rw [hp2]; exact dvd_mul_right 2 (d₁ * d₂)
        rw [if_pos hmem]
        have h20 : (2 : ZMod p) = 0 := by
          have e1 : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by norm_cast
          have e2 : ((2 : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) :=
            congrArg (fun n : ℕ => (n : ZMod p)) hp2.symm
          rw [e1, e2, ZMod.natCast_self p]
        have hδ1one : δ₁ = 1 := by
          obtain ⟨k, hk⟩ := ho1
          change (d₁ : ZMod p) = 1
          rw [hk]; push_cast; linear_combination (k : ZMod p) * h20
        have hδ2one : δ₂ = 1 := by
          obtain ⟨k, hk⟩ := ho2
          change (d₂ : ZMod p) = 1
          rw [hk]; push_cast; linear_combination (k : ZMod p) * h20
        have hαeq : α₂ = α₁ := by
          rw [hδ1one, hδ2one, mul_one, mul_one] at hrelZ
          rw [hrelZ, h20, add_zero]
        have hAB : (univ.filter (fun u : ZMod p => α₂ + u * δ₁ = 0))
            = (univ.filter (fun u : ZMod p => α₁ + u * δ₂ = 0)) := by
          ext u; simp only [mem_filter, mem_univ, true_and]
          rw [hαeq, hδ1one, hδ2one]
        rw [hsplit, hAB, Finset.union_self]
        exact card_linear_root α₁ δ₂ hδ2
      · -- p ≠ 2, p ∤ d₁ d₂ : two distinct honest roots
        have hnotmem : ¬ p ∣ 2 * (d₁ * d₂) := by
          intro h
          rw [Nat.Prime.dvd_mul hp, Nat.Prime.dvd_mul hp] at h
          rcases h with h2 | h1 | h2'
          · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
          · exact hpd1 h1
          · exact hpd2 h2'
        rw [if_neg hnotmem]
        have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp hp2
        have hdisj : Disjoint (univ.filter (fun u : ZMod p => α₁ + u * δ₂ = 0))
            (univ.filter (fun u : ZMod p => α₂ + u * δ₁ = 0)) := by
          rw [Finset.disjoint_left]
          intro u huA huB
          rw [mem_filter] at huA huB
          have h20 : (2 : ZMod p) = 0 := by
            linear_combination δ₂ * huB.2 - δ₁ * huA.2 - hrelZ
          exact h2ne h20
        rw [hsplit, Finset.card_union_of_disjoint hdisj,
          card_linear_root α₁ δ₂ hδ2, card_linear_root α₂ δ₁ hδ1]

end RhoK

/-! ## §3 — the mixed residue set and its count `card_mixResidues` -/

/-- The mixed cofactor-sift residue set mod `d·d₁·d₂`: AP-pair conditions plus the
mixed cofactor condition `d ∣ (r/d₁)·((r+2)/d₂)`. -/
def mixResSet (d d₁ d₂ : ℕ) : Finset ℕ :=
  (Finset.range (d * d₁ * d₂)).filter
    (fun r => d₁ ∣ r ∧ d₂ ∣ (r + 2) ∧ d ∣ (r / d₁) * ((r + 2) / d₂))

/-- **The mixed residue count.**  For `d` squarefree, `d₁ d₂` odd coprime positive,
the number of mixed cofactor-sift residues mod `d·d₁·d₂` is the mixed local product
`∏_{p ∣ d} (if p ∣ 2 d₁ d₂ then 1 else 2)`. -/
lemma card_mixResidues {d d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hsq : Squarefree d) (ho1 : Odd d₁) (ho2 : Odd d₂) (hcop12 : Nat.Coprime d₁ d₂) :
    (mixResSet d d₁ d₂).card
      = ∏ p ∈ d.primeFactors, (if p ∣ 2 * (d₁ * d₂) then 1 else 2) := by
  set E := d₁ * d₂ with hEdef
  have hEpos : 0 < E := Nat.mul_pos hd₁ hd₂
  -- the fixed AP class `c` (mod E) and its cofactor witnesses `a₁, a₂`
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop12 0 (2 * d₂ - 2)
  set c := k % E with hcdef
  have hcE : c < E := Nat.mod_lt k hEpos
  have hcd1 : d₁ ∣ c := by
    have hck : c ≡ k [MOD d₁] := by
      rw [Nat.ModEq, hcdef, Nat.mod_mod_of_dvd _ (dvd_mul_right d₁ d₂)]
    exact Nat.modEq_zero_iff_dvd.mp (hck.trans hk1)
  have hcd2 : d₂ ∣ (c + 2) := by
    have hck : c ≡ k [MOD d₂] := by
      rw [Nat.ModEq, hcdef, Nat.mod_mod_of_dvd _ (dvd_mul_left d₂ d₁)]
    have hc2 : c + 2 ≡ (2 * d₂ - 2) + 2 [MOD d₂] := (hck.trans hk2).add_right 2
    rw [show (2 * d₂ - 2) + 2 = 2 * d₂ by omega] at hc2
    exact Nat.modEq_zero_iff_dvd.mp (hc2.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left d₂ 2)))
  -- uniqueness: any AP-pair residue reduces mod E to `c`
  have huniq : ∀ r, d₁ ∣ r → d₂ ∣ (r + 2) → r % E = c := by
    intro r hr1 hr2
    have hm1 : r ≡ c [MOD d₁] :=
      (Nat.modEq_zero_iff_dvd.mpr hr1).trans (Nat.modEq_zero_iff_dvd.mpr hcd1).symm
    have hm2 : r ≡ c [MOD d₂] := by
      have h := (Nat.modEq_zero_iff_dvd.mpr hr2).trans (Nat.modEq_zero_iff_dvd.mpr hcd2).symm
      exact Nat.ModEq.add_right_cancel' 2 h
    have hmE : r ≡ c [MOD E] := (Nat.modEq_and_modEq_iff_modEq_mul hcop12).mp ⟨hm1, hm2⟩
    have : r % E = c % E := hmE
    rwa [Nat.mod_eq_of_lt hcE] at this
  obtain ⟨a₁, ha₁⟩ := hcd1
  obtain ⟨a₂, ha₂⟩ := hcd2
  have hrel : a₂ * d₂ = a₁ * d₁ + 2 := by
    rw [mul_comm a₂ d₂, ← ha₂, mul_comm a₁ d₁, ← ha₁]
  -- the bijection `t ↦ c + E t` between the `rhoK` root set and `mixResSet`
  have hbij : (mixResSet d d₁ d₂).card = rhoK a₁ a₂ d₁ d₂ d := by
    unfold mixResSet rhoK
    symm
    apply Finset.card_bij (fun t _ => c + E * t)
    · -- maps into
      intro t ht
      rw [mem_filter, mem_range] at ht
      obtain ⟨htd, htK⟩ := ht
      rw [mem_filter, mem_range]
      refine ⟨?_, ?_, ?_, ?_⟩
      · calc c + E * t < E + E * t := by omega
          _ = E * (t + 1) := by ring
          _ ≤ E * d := Nat.mul_le_mul_left E htd
          _ = d * d₁ * d₂ := by rw [hEdef]; ring
      · rw [ha₁]; exact Dvd.dvd.add ⟨a₁, rfl⟩ ⟨d₂ * t, by rw [hEdef]; ring⟩
      · rw [show c + E * t + 2 = (c + 2) + E * t by ring, ha₂]
        exact Dvd.dvd.add ⟨a₂, rfl⟩ ⟨d₁ * t, by rw [hEdef]; ring⟩
      · have hr1 : (c + E * t) / d₁ = a₁ + t * d₂ := by
          rw [ha₁, hEdef, show d₁ * a₁ + d₁ * d₂ * t = d₁ * (a₁ + t * d₂) by ring,
            Nat.mul_div_cancel_left _ hd₁]
        have hr2 : ((c + E * t) + 2) / d₂ = a₂ + t * d₁ := by
          rw [show c + E * t + 2 = (c + 2) + E * t by ring, ha₂, hEdef,
            show d₂ * a₂ + d₁ * d₂ * t = d₂ * (a₂ + t * d₁) by ring, Nat.mul_div_cancel_left _ hd₂]
        rw [hr1, hr2]; exact htK
    · -- injective
      intro t1 _ t2 _ heq
      exact Nat.eq_of_mul_eq_mul_left hEpos (by omega)
    · -- surjective
      intro r hr
      rw [mem_filter, mem_range] at hr
      obtain ⟨hrD, hr1, hr2, hrcof⟩ := hr
      have hrEc : r % E = c := huniq r hr1 hr2
      set t := r / E with htdef
      have hrval : E * t + c = r := by rw [← hrEc]; exact Nat.div_add_mod r E
      refine ⟨t, ?_, ?_⟩
      · rw [mem_filter, mem_range]
        refine ⟨?_, ?_⟩
        · rw [htdef, Nat.div_lt_iff_lt_mul hEpos]
          calc r < d * d₁ * d₂ := hrD
            _ = d * E := by rw [hEdef]; ring
        · have hr1div : r / d₁ = a₁ + t * d₂ := by
            have hrfact : r = d₁ * (a₁ + t * d₂) := by rw [← hrval, ha₁, hEdef]; ring
            rw [hrfact, Nat.mul_div_cancel_left _ hd₁]
          have hr2div : (r + 2) / d₂ = a₂ + t * d₁ := by
            have hrfact : r + 2 = d₂ * (a₂ + t * d₁) := by
              rw [← hrval, show E * t + c + 2 = E * t + (c + 2) by ring, ha₂, hEdef]; ring
            rw [hrfact, Nat.mul_div_cancel_left _ hd₂]
          have : (r / d₁) * ((r + 2) / d₂) = Kpoly a₁ a₂ d₁ d₂ t := by
            rw [hr1div, hr2div, Kpoly]
          rwa [this] at hrcof
      · omega
  rw [hbij, rhoK_prod_primeFactors a₁ a₂ d₁ d₂ d hsq]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [rhoK_prime a₁ a₂ d₁ d₂ hpp hrel ho1 ho2 hcop12]

/-! ## §4 — the rem bound, the error sum, and the unconditional Lemma 8′ -/

/-- **The mixed cofactor predicate is `D`-periodic.**  Although `n/d₁` is not
periodic, under the AP-pair conditions the cofactor product's residue mod `d`
is, so the whole AP-pair-plus-cofactor predicate holds iff `n % (d d₁ d₂)` lies
in `mixResSet`. -/
lemma mix_pred_iff_mod {d d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hDpos : 0 < d * d₁ * d₂) (n : ℕ) :
    (d₁ ∣ n ∧ d₂ ∣ (n + 2) ∧ d ∣ (n / d₁) * ((n + 2) / d₂))
      ↔ n % (d * d₁ * d₂) ∈ mixResSet d d₁ d₂ := by
  set D := d * d₁ * d₂ with hDdef
  set r := n % D with hrdef
  have hd1D : d₁ ∣ D := ⟨d * d₂, by rw [hDdef]; ring⟩
  have hd2D : d₂ ∣ D := ⟨d * d₁, by rw [hDdef]; ring⟩
  have hrn : r ≡ n [MOD D] := Nat.mod_modEq n D
  have hr1 : r ≡ n [MOD d₁] := hrn.of_dvd hd1D
  have hr2 : r ≡ n [MOD d₂] := hrn.of_dvd hd2D
  have dvd_congr : ∀ {kk a b : ℕ}, a ≡ b [MOD kk] → (kk ∣ a ↔ kk ∣ b) := by
    intro kk a b h
    exact ⟨fun hka => Nat.modEq_zero_iff_dvd.mp (h.symm.trans (Nat.modEq_zero_iff_dvd.mpr hka)),
           fun hkb => Nat.modEq_zero_iff_dvd.mp (h.trans (Nat.modEq_zero_iff_dvd.mpr hkb))⟩
  -- the cofactor congruence, under all four divisibilities
  have hcof : d₁ ∣ n → d₂ ∣ (n + 2) → d₁ ∣ r → d₂ ∣ (r + 2) →
      ((n / d₁) * ((n + 2) / d₂) ≡ (r / d₁) * ((r + 2) / d₂) [MOD d]) := by
    intro _ _ hAr hBr
    set q := n / D with hqdef
    have hnq : D * q + r = n := Nat.div_add_mod n D
    obtain ⟨B1, hB1⟩ := hAr
    obtain ⟨C1, hC1⟩ := hBr
    have hndiv1 : n / d₁ = d * d₂ * q + B1 := by
      have hnf : n = d₁ * (d * d₂ * q + B1) := by rw [← hnq, hB1, hDdef]; ring
      rw [hnf, Nat.mul_div_cancel_left _ hd₁]
    have hrdiv1 : r / d₁ = B1 := by rw [hB1, Nat.mul_div_cancel_left _ hd₁]
    have hcong1 : n / d₁ ≡ r / d₁ [MOD d] := by
      rw [hndiv1, hrdiv1]
      calc d * d₂ * q + B1
          ≡ 0 + B1 [MOD d] := (Nat.modEq_zero_iff_dvd.mpr ⟨d₂ * q, by ring⟩).add_right B1
        _ = B1 := Nat.zero_add B1
    have hndiv2 : (n + 2) / d₂ = d * d₁ * q + C1 := by
      have hnf : n + 2 = d₂ * (d * d₁ * q + C1) := by
        rw [← hnq, show D * q + r + 2 = D * q + (r + 2) by ring, hC1, hDdef]; ring
      rw [hnf, Nat.mul_div_cancel_left _ hd₂]
    have hrdiv2 : (r + 2) / d₂ = C1 := by rw [hC1, Nat.mul_div_cancel_left _ hd₂]
    have hcong2 : (n + 2) / d₂ ≡ (r + 2) / d₂ [MOD d] := by
      rw [hndiv2, hrdiv2]
      calc d * d₁ * q + C1
          ≡ 0 + C1 [MOD d] := (Nat.modEq_zero_iff_dvd.mpr ⟨d₁ * q, by ring⟩).add_right C1
        _ = C1 := Nat.zero_add C1
    exact hcong1.mul hcong2
  rw [mixResSet, Finset.mem_filter, Finset.mem_range, and_iff_right (Nat.mod_lt n hDpos)]
  constructor
  · rintro ⟨hA, hB, hC⟩
    have hAr : d₁ ∣ r := (dvd_congr hr1).mpr hA
    have hBr : d₂ ∣ (r + 2) := (dvd_congr (hr2.add_right 2)).mpr hB
    exact ⟨hAr, hBr, (dvd_congr (hcof hA hB hAr hBr)).mp hC⟩
  · rintro ⟨hAr, hBr, hCr⟩
    have hA : d₁ ∣ n := (dvd_congr hr1).mp hAr
    have hB : d₂ ∣ (n + 2) := (dvd_congr (hr2.add_right 2)).mp hBr
    exact ⟨hA, hB, (dvd_congr (hcof hA hB hAr hBr)).mpr hCr⟩

/-- **The mixed AP-pair remainder bound.**  For `d` squarefree, `d₁ d₂` odd coprime
positive, the mixed Selberg remainder is controlled by the mixed local count:
`|rem d| ≤ 2 · #mixResSet(d)`. -/
lemma mixPairSieve_rem_abs_le {x d₁ d₂ Z : ℕ} (hZ1 : 1 ≤ Z) {d : ℕ}
    (hd : 0 < d) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hsq : Squarefree d)
    (ho1 : Odd d₁) (ho2 : Odd d₂) (hcop12 : Nat.Coprime d₁ d₂) :
    |(mixPairSieve x d₁ d₂ Z hZ1).rem d| ≤ 2 * ((mixResSet d d₁ d₂).card : ℝ) := by
  have hDpos : 0 < d * d₁ * d₂ := by positivity
  set D := d * d₁ * d₂ with hDdef
  -- the mixed local density equals the residue count over `d`
  have hprod : ((mixResSet d d₁ d₂).card : ℝ)
      = ∏ p ∈ d.primeFactors, (if p ∣ 2 * (d₁ * d₂) then (1 : ℝ) else 2) := by
    rw [card_mixResidues hd₁ hd₂ hsq ho1 ho2 hcop12, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p _; split_ifs <;> norm_num
  have hnuMix : nuMix (2 * (d₁ * d₂)) d = ((mixResSet d d₁ d₂).card : ℝ) / d := by
    rw [nuMix_apply, hprod]
  have hcount : (mixPairSieve x d₁ d₂ Z hZ1).multSum d
      = (((Finset.Ioc x (2 * x)).filter (fun n => n % D ∈ mixResSet d d₁ d₂)).card : ℝ) := by
    rw [mixPairSieve_multSum hcop12]
    congr 2
    rw [baseSet, Finset.filter_filter]
    apply Finset.filter_congr
    intro n _
    rw [← mix_pred_iff_mod hd₁ hd₂ hDpos n]
    tauto
  have hinter : mixResSet d d₁ d₂ ∩ Finset.range D = mixResSet d d₁ d₂ :=
    Finset.inter_eq_left.mpr (Finset.filter_subset _ _)
  have hcard : (mixResSet d d₁ d₂ ∩ Finset.range D).card = (mixResSet d d₁ d₂).card := by
    rw [hinter]
  rw [BoundingSieve.rem, hcount, mixPairSieve_nu, mixPairSieve_totalMass, hnuMix]
  have hbound := congCount_Ioc_bound D (mixResSet d d₁ d₂) hDpos x (2 * x) (by omega)
  rw [hcard] at hbound
  have hmain : ((mixResSet d d₁ d₂).card : ℝ) / d * ((x : ℝ) / (d₁ * d₂))
      = ((2 * x : ℕ) - (x : ℕ) : ℝ) * ((mixResSet d d₁ d₂).card : ℝ) / D := by
    have hxx : (((2 * x : ℕ) : ℝ) - (x : ℕ)) = (x : ℝ) := by push_cast; ring
    rw [hxx, hDdef]
    push_cast
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have hd10 : (d₁ : ℝ) ≠ 0 := by positivity
    have hd20 : (d₂ : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hmain]
  exact hbound

/-- **The mixed Selberg error sum bound.**  For `d₁ d₂` a positive odd coprime pair
(no roughness), the `3^ω`-weighted mixed remainder over the truncated divisors of
`primorial Z` is `O(Z⁸)`: `|rem d| ≤ 2 ρ_mix(d) ≤ 2^{ω(d)+1}` gives the same crude
polynomial bound as the twin case. -/
lemma mixPairSieve_errSum_le {x d₁ d₂ Z : ℕ} (hZ1 : 1 ≤ Z) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (ho1 : Odd d₁) (ho2 : Odd d₂) (hcop12 : Nat.Coprime d₁ d₂) :
    (∑ d ∈ (mixPairSieve x d₁ d₂ Z hZ1).prodPrimes.divisors,
        if (d : ℝ) ≤ (mixPairSieve x d₁ d₂ Z hZ1).level then
          (3 : ℝ) ^ ω d * |(mixPairSieve x d₁ d₂ Z hZ1).rem d| else 0)
      ≤ 2 * (Z : ℝ) ^ 8 := by
  simp only [mixPairSieve_prodPrimes, mixPairSieve_level]
  have hterm : ∀ d ∈ (primorial Z).divisors,
      (if (d : ℝ) ≤ (Z : ℝ) ^ 2 then (3 : ℝ) ^ ω d * |(mixPairSieve x d₁ d₂ Z hZ1).rem d| else 0)
        ≤ (if (d : ℝ) ≤ (Z : ℝ) ^ 2 then 2 * (d : ℝ) ^ 3 else 0) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, _⟩ := hd
    split_ifs with hg
    · have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd
        (Nat.pos_of_ne_zero (Salt.M5Assembly.primorial_squarefree Z).ne_zero)
      have hsq : Squarefree d := (Salt.M5Assembly.primorial_squarefree Z).squarefree_of_dvd hdvd
      have hrem := mixPairSieve_rem_abs_le (x := x) hZ1 hd0 hd₁ hd₂ hsq ho1 ho2 hcop12
      have hωb : ω d = omega d := (Salt.M5Assembly.omega_eq_cardDistinctFactors d).symm
      have hcardN : (mixResSet d d₁ d₂).card ≤ 2 ^ omega d := by
        rw [card_mixResidues hd₁ hd₂ hsq ho1 ho2 hcop12]
        calc ∏ p ∈ d.primeFactors, (if p ∣ 2 * (d₁ * d₂) then 1 else 2)
            ≤ ∏ _p ∈ d.primeFactors, 2 :=
              Finset.prod_le_prod' (fun p _ => by split_ifs <;> norm_num)
          _ = 2 ^ omega d := by unfold omega; rw [Finset.prod_const]
      have hcardR : ((mixResSet d d₁ d₂).card : ℝ) ≤ (2 : ℝ) ^ ω d := by
        rw [hωb]; exact_mod_cast hcardN
      have h6 : (6 : ℝ) ^ ω d ≤ (d : ℝ) ^ 3 := by
        rw [hωb]; exact_mod_cast six_pow_omega_le_d_cubed hsq
      calc (3 : ℝ) ^ ω d * |(mixPairSieve x d₁ d₂ Z hZ1).rem d|
          ≤ (3 : ℝ) ^ ω d * (2 * ((mixResSet d d₁ d₂).card : ℝ)) :=
            mul_le_mul_of_nonneg_left hrem (by positivity)
        _ ≤ (3 : ℝ) ^ ω d * (2 * (2 : ℝ) ^ ω d) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hcardR (by norm_num)
        _ = 2 * (6 : ℝ) ^ ω d := by
            rw [show (3 : ℝ) ^ ω d * (2 * (2 : ℝ) ^ ω d)
                = 2 * ((3 : ℝ) ^ ω d * (2 : ℝ) ^ ω d) from by ring, ← mul_pow]
            norm_num
        _ ≤ 2 * (d : ℝ) ^ 3 := by linarith
    · exact le_refl _
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hstep : ∀ d ∈ (primorial Z).divisors,
      (if (d : ℝ) ≤ (Z : ℝ) ^ 2 then 2 * (d : ℝ) ^ 3 else 0)
        ≤ (if (d : ℝ) ≤ (Z : ℝ) ^ 2 then 2 * ((Z : ℝ) ^ 2) ^ 3 else 0) := by
    intro d _
    split_ifs with hg
    · have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      gcongr
    · exact le_refl _
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.sum_filter, Finset.sum_const]
  have hFsub : (primorial Z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (Z : ℝ) ^ 2)
      ⊆ Finset.Icc 1 (Z ^ 2) := by
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hg⟩ := hd
    rw [Finset.mem_Icc]
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd
      (Nat.pos_of_ne_zero (Salt.M5Assembly.primorial_squarefree Z).ne_zero)
    refine ⟨hd0, ?_⟩
    have hle : (d : ℝ) ≤ ((Z ^ 2 : ℕ) : ℝ) := by push_cast; exact hg
    exact_mod_cast hle
  have hcard : ((primorial Z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (Z : ℝ) ^ 2)).card
      ≤ Z ^ 2 := by
    calc ((primorial Z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (Z : ℝ) ^ 2)).card
        ≤ (Finset.Icc 1 (Z ^ 2)).card := Finset.card_le_card hFsub
      _ = Z ^ 2 := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  rw [nsmul_eq_mul]
  calc (((primorial Z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (Z : ℝ) ^ 2)).card : ℝ)
        * (2 * ((Z : ℝ) ^ 2) ^ 3)
      ≤ ((Z ^ 2 : ℕ) : ℝ) * (2 * ((Z : ℝ) ^ 2) ^ 3) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
    _ = 2 * (Z : ℝ) ^ 8 := by push_cast; ring

/-- **HB 1983, Lemma 8′ (mixed / cofactor case, UNCONDITIONAL).**  For `Z ≥ 100`,
`d₁, d₂` a positive odd coprime pair (no roughness assumption), the honest
cofactor-sifted count over the AP window obeys

  `S′(d₁,d₂;Z) ≤ 64·(d₁d₂/φ(d₁d₂))²·(x/(d₁d₂))/(log Z)² + 2 Z⁸`.

This discharges the atomic residual of `Salt.HB.hb_lemma8'`, fully supplying
HB's (3.3). -/
theorem hb_lemma8'_unconditional {x d₁ d₂ Z : ℕ} (hZ : 100 ≤ Z) (hZ1 : 1 ≤ Z)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (ho1 : Odd d₁) (ho2 : Odd d₂) (hcop12 : Nat.Coprime d₁ d₂) :
    (((baseSet x d₁ d₂).filter
        (fun n => Nat.Coprime (primorial Z) ((n / d₁) * ((n + 2) / d₂)))).card : ℝ)
      ≤ 64 * ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂))) ^ 2 * ((x : ℝ) / (d₁ * d₂))
          / (Real.log Z) ^ 2 + 2 * (Z : ℝ) ^ 8 :=
  hb_lemma8' hZ hZ1 hd₁ hd₂ ho1 ho2 hcop12
    (mixPairSieve_errSum_le hZ1 hd₁ hd₂ ho1 ho2 hcop12)

end Salt.HB
