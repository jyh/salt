/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The additive-energy escape: L⁴/Parseval/Markov large-spectrum chain (W3-AE-c)

Tao 1509.05422 Lemma 3.5 (restriction theorem for the primes), footnote-4
additive-energy escape.  The large-spectrum set `Ξ_H` (frequencies where the
prime exponential sum `S_H(−ξ/H)` exceeds `ε²/log H`) is controlled by the
additive energy of the prime window:
`|Ξ_H| · (ε²/log H)⁴ ≤ H · (2/(ε²H))⁴ · E[𝒫_H]`.

The chain lands as four pieces:

1. `expSum_eq_dft_windowPhi` (bridge): `S_H(−ξ/H) = 𝓕Φ ξ` for the `1/p`-weighted
   window indicator `Φ = windowPhi`.  Needs `p < H` (`hwin`) so the primes embed
   injectively into `ℤ/Hℤ`.
2. `card_bigXi_mul_thresh_le` (Markov at the 4th power): the threshold count of
   `Ξ_H` is bounded by the ℓ⁴ Fourier mass.
3. `dft_windowPhi_l4_le` (the L⁴ heart): the Parseval extension of the landed
   L² `dft_parseval` — `∑_ξ ‖𝓕Φ ξ‖⁴ ≤ H · (2/(ε²H))⁴ · E[𝒫_H]`.  Routes through
   the convolution theorem `𝓕(Φ⋆Φ) = (𝓕Φ)²` and the additive energy of the
   window image in `ℤ/Hℤ`.  The no-wrap hypothesis `hwrap` (`p+q < H`) is
   load-bearing: mod-`H` equality of prime sums equals integer equality only
   when the sums stay below `H`.
4. `large_spectrum_energy` (the combine): pieces 2 ∘ 1 ∘ 3.
-/
import Salt.Entropy.Chowla.CircleMethod
import Mathlib

open scoped BigOperators Combinatorics.Additive

namespace Salt.Entropy.Chowla

/-- **The `1/p`-weighted window indicator** `Φ : ℤ/Hℤ → ℂ`.  On the residue `j`
whose lift `j.val` is a window prime, `Φ j = 1/j.val`; elsewhere `0`.  Engineered
so that `𝓕Φ ξ = S_H(−ξ/H)` (see `expSum_eq_dft_windowPhi`). -/
noncomputable def windowPhi (eps : ℚ) (H : ℕ) (j : ZMod H) : ℂ :=
  if (j.val ∈ primeWindow eps H) then (1 / (j.val : ℂ)) else 0

/-- The pointwise bound `‖Φ j‖ ≤ 2/(ε²H)` (from the window lower bound
`p > ε²H/2`). -/
lemma windowPhi_norm_le (eps : ℚ) (H : ℕ) [NeZero H] (heps : 0 < eps) (j : ZMod H) :
    ‖windowPhi eps H j‖ ≤ 2 / ((eps : ℝ) ^ 2 * (H : ℝ)) := by
  have heps2 : (0 : ℝ) < (eps : ℝ) ^ 2 := by positivity
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne H)
  have hMpos : (0 : ℝ) < (eps : ℝ) ^ 2 * (H : ℝ) := mul_pos heps2 hHpos
  unfold windowPhi
  split_ifs with h
  · rw [norm_div, norm_one, Complex.norm_natCast]
    have hprime := (mem_primeWindow.mp h).2.1
    have hpos : (0 : ℝ) < (j.val : ℝ) := by exact_mod_cast hprime.pos
    have hlb : (eps : ℝ) ^ 2 * (H : ℝ) / 2 < (j.val : ℝ) := by
      have hq := (mem_primeWindow.mp h).2.2
      have hcast : ((eps ^ 2 * (H : ℚ) / 2 : ℚ) : ℝ) < ((j.val : ℚ) : ℝ) := by
        exact_mod_cast hq
      push_cast at hcast
      linarith
    rw [div_le_div_iff₀ hpos hMpos]
    nlinarith [hlb]
  · rw [norm_zero]
    positivity

/-- **W3-AE-bridge** (piece 1): the prime exponential sum `S_H(−ξ/H)` is the
finite Fourier transform of the `1/p`-weighted window indicator.  The hypothesis
`hwin : ∀ p ∈ 𝒫_H, p < H` makes `p ↦ (p : ℤ/Hℤ)` injective (the `ZMod.val`
round-trip). -/
theorem expSum_eq_dft_windowPhi (eps : ℚ) (H : ℕ) [NeZero H]
    (hwin : ∀ p ∈ primeWindow eps H, p < H) (ξ : ZMod H) :
    expSum eps H (-(ξ.val : ℝ) / (H : ℝ)) = ZMod.dft (windowPhi eps H) ξ := by
  classical
  -- LHS: expand `expSum` and convert `exp` → `stdAddChar`, subtype → Finset sum
  have hL : expSum eps H (-(ξ.val : ℝ) / (H : ℝ))
      = ∑ p ∈ primeWindow eps H,
          (1 / ((p : ℕ) : ℂ)) * ZMod.stdAddChar (-((((p : ℕ)) : ZMod H) * ξ)) := by
    unfold expSum
    rw [← Finset.sum_coe_sort (primeWindow eps H)
        (fun p => (1 / ((p : ℕ) : ℂ)) * ZMod.stdAddChar (-((((p : ℕ)) : ZMod H) * ξ)))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have hd : ZMod.stdAddChar (-((((p : ℕ)) : ZMod H) * ξ))
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            ((-(ξ.val : ℝ) / (H : ℝ)) : ℂ) * ((p : ℕ) : ℂ)) := by
      have hrw : -((((p : ℕ)) : ZMod H) * ξ) = ((-(((p : ℕ)) * ξ.val : ℕ) : ℤ) : ZMod H) := by
        push_cast [ZMod.natCast_zmod_val]; ring
      rw [hrw, ZMod.stdAddChar_coe]; push_cast; ring_nf
    rw [hd]; push_cast; ring
  -- RHS: `𝓕Φ ξ = ∑_j sc(−jξ) Φ j`; restrict to the window image then reindex
  have hinj : Set.InjOn (Nat.cast : ℕ → ZMod H) (primeWindow eps H) := by
    intro p hp q hq hpq
    have : (p : ZMod H).val = (q : ZMod H).val := by rw [hpq]
    rwa [ZMod.val_natCast_of_lt (hwin p hp), ZMod.val_natCast_of_lt (hwin q hq)] at this
  have hR : ZMod.dft (windowPhi eps H) ξ
      = ∑ p ∈ primeWindow eps H,
          (1 / ((p : ℕ) : ℂ)) * ZMod.stdAddChar (-((((p : ℕ)) : ZMod H) * ξ)) := by
    rw [ZMod.dft_apply]
    rw [← Finset.sum_subset
        (Finset.subset_univ ((primeWindow eps H).image (Nat.cast : ℕ → ZMod H)))
        (fun j _ hjS => ?_)]
    · rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hpv : ((p : ZMod H)).val = p := ZMod.val_natCast_of_lt (hwin p hp)
      have hΦ : windowPhi eps H (p : ZMod H) = 1 / ((p : ℕ) : ℂ) := by
        unfold windowPhi; rw [if_pos (by rw [hpv]; exact hp), hpv]
      rw [hΦ, smul_eq_mul, mul_comm]
    · -- `j` outside the window image ⇒ `Φ j = 0`
      have hΦ0 : windowPhi eps H j = 0 := by
        unfold windowPhi
        rw [if_neg]
        intro hjv
        exact hjS (Finset.mem_image.mpr ⟨j.val, hjv, ZMod.natCast_zmod_val j⟩)
      rw [hΦ0, smul_zero]
  rw [hL, hR]

/-- **W3-AE-markov** (piece 2): the threshold count of `Ξ_H` is bounded by the
ℓ⁴ Fourier mass.  Chebyshev/Markov at the 4th power: each `ξ ∈ Ξ_H` contributes
`≥ (ε²/log H)⁴`, and the count sits inside the full `ℤ/Hℤ` sum of nonneg terms. -/
theorem card_bigXi_mul_thresh_le (eps : ℚ) (H : ℕ) [NeZero H] :
    ((bigXi eps H).card : ℝ) * ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) ^ 4
      ≤ ∑ ξ : ZMod H, ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 4 := by
  have hHge1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne H)
  have hthr_nn : (0 : ℝ) ≤ (eps : ℝ) ^ 2 / Real.log (H : ℝ) :=
    div_nonneg (by positivity) (Real.log_nonneg hHge1)
  calc ((bigXi eps H).card : ℝ) * ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) ^ 4
      = ∑ _ξ ∈ bigXi eps H, ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) ^ 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ ξ ∈ bigXi eps H, ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 4 := by
        refine Finset.sum_le_sum (fun ξ hξ => ?_)
        have hmem : (eps : ℝ) ^ 2 / Real.log (H : ℝ)
            ≤ ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ := by
          simpa only [bigXi, Finset.mem_filter, Finset.mem_univ, true_and] using hξ
        exact pow_le_pow_left₀ hthr_nn hmem 4
    _ ≤ ∑ ξ : ZMod H, ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun ξ _ _ => by positivity)

/-! ### Piece 3: the L⁴ heart -/

/-- **The convolution theorem** for the unnormalized `ZMod.dft`: the transform of
the self-convolution `Φ⋆Φ` is the square of the transform.  (Unnormalized, so no
`H` factor appears.) -/
private lemma dft_conv_sq {H : ℕ} [NeZero H] (Φ : ZMod H → ℂ) (ξ : ZMod H) :
    ZMod.dft (fun m => ∑ j : ZMod H, Φ j * Φ (m - j)) ξ = (ZMod.dft Φ ξ) ^ 2 := by
  have hRHS : (ZMod.dft Φ ξ) ^ 2
      = ∑ j : ZMod H, ∑ k : ZMod H,
          ZMod.stdAddChar (-((j + k) * ξ)) * (Φ j * Φ k) := by
    rw [sq, ZMod.dft_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [smul_eq_mul, smul_eq_mul,
      show -((j + k) * ξ) = -(j * ξ) + -(k * ξ) by ring, ZMod.stdAddChar.map_add_eq_mul]
    ring
  have hLHS : ZMod.dft (fun m => ∑ j : ZMod H, Φ j * Φ (m - j)) ξ
      = ∑ j : ZMod H, ∑ k : ZMod H,
          ZMod.stdAddChar (-((j + k) * ξ)) * (Φ j * Φ k) := by
    rw [ZMod.dft_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Equiv.sum_comp (Equiv.addLeft j)
        (fun m => ZMod.stdAddChar (-(m * ξ)) * (Φ j * Φ (m - j)))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Equiv.coe_addLeft, add_sub_cancel_left]
  rw [hLHS, hRHS]

/-- **W3-AE-l4** (piece 3, the heart): the L⁴ bound.  `∑_ξ ‖𝓕Φ ξ‖⁴` is bounded by
`H · (2/(ε²H))⁴ · E[𝒫_H]`.  Route: `‖𝓕Φ‖⁴ = ‖(𝓕Φ)²‖² = ‖𝓕(Φ⋆Φ)‖²`, apply the
landed L² Parseval to the self-convolution, then bound the ℓ² mass of the
convolution by the additive energy of the window image in `ℤ/Hℤ`, transferred to
the ℕ-energy of `𝒫_H` via the no-wrap hypothesis `hwrap`. -/
theorem dft_windowPhi_l4_le (eps : ℚ) (H : ℕ) [NeZero H] (heps : 0 < eps)
    (hwin : ∀ p ∈ primeWindow eps H, p < H)
    (hwrap : ∀ p ∈ primeWindow eps H, ∀ q ∈ primeWindow eps H, p + q < H) :
    ∑ ξ : ZMod H, ‖ZMod.dft (windowPhi eps H) ξ‖ ^ 4
      ≤ (H : ℝ) * (2 / ((eps : ℝ) ^ 2 * (H : ℝ))) ^ 4
        * (Finset.addEnergy (primeWindow eps H) (primeWindow eps H) : ℝ) := by
  classical
  set M : ℝ := 2 / ((eps : ℝ) ^ 2 * (H : ℝ)) with hMdef
  set supp : Finset (ZMod H) := (primeWindow eps H).image (Nat.cast : ℕ → ZMod H) with hsuppdef
  have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hMnn : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  have hΦM : ∀ j, ‖windowPhi eps H j‖ ≤ M := by
    intro j; rw [hMdef]; exact windowPhi_norm_le eps H heps j
  -- window-image facts
  have hsuppval : ∀ j ∈ supp, j.val ∈ primeWindow eps H := by
    intro j hj
    rw [hsuppdef, Finset.mem_image] at hj
    obtain ⟨p, hp, rfl⟩ := hj
    rwa [ZMod.val_natCast_of_lt (hwin p hp)]
  have hsupp0 : ∀ j, j ∉ supp → windowPhi eps H j = 0 := by
    intro j hj
    unfold windowPhi
    rw [if_neg]
    intro hjv
    exact hj (by rw [hsuppdef]; exact Finset.mem_image.mpr ⟨j.val, hjv, ZMod.natCast_zmod_val j⟩)
  have hvaladd : ∀ a ∈ supp, ∀ b ∈ supp, (a + b).val = a.val + b.val := by
    intro a ha b hb
    have hlt : a.val + b.val < H := hwrap a.val (hsuppval a ha) b.val (hsuppval b hb)
    have hab : a + b = ((a.val + b.val : ℕ) : ZMod H) := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [hab, ZMod.val_natCast_of_lt hlt]
  -- pointwise convolution bound: ‖(Φ⋆Φ) m‖ ≤ M² · #fiber
  have hΨle : ∀ m : ZMod H,
      ‖∑ j : ZMod H, windowPhi eps H j * windowPhi eps H (m - j)‖
        ≤ M ^ 2 * ((supp.filter (fun j => m - j ∈ supp)).card : ℝ) := by
    intro m
    calc ‖∑ j : ZMod H, windowPhi eps H j * windowPhi eps H (m - j)‖
        ≤ ∑ j : ZMod H, ‖windowPhi eps H j * windowPhi eps H (m - j)‖ := norm_sum_le _ _
      _ = ∑ j : ZMod H, ‖windowPhi eps H j‖ * ‖windowPhi eps H (m - j)‖ := by
          refine Finset.sum_congr rfl (fun j _ => ?_); rw [norm_mul]
      _ ≤ ∑ _j : ZMod H, (if (_j ∈ supp ∧ m - _j ∈ supp) then M ^ 2 else 0) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          split_ifs with h
          · rw [sq]; exact mul_le_mul (hΦM j) (hΦM (m - j)) (norm_nonneg _) hMnn
          · rcases not_and_or.mp h with hA | hB
            · rw [hsupp0 j hA]; simp
            · rw [hsupp0 (m - j) hB]; simp
      _ = M ^ 2 * ((supp.filter (fun j => m - j ∈ supp)).card : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            show (Finset.univ.filter (fun j : ZMod H => j ∈ supp ∧ m - j ∈ supp))
                = supp.filter (fun j => m - j ∈ supp) from by
              ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]]
          ring
  -- fiber count = additive-energy fiber
  have hfibcard : ∀ m : ZMod H,
      (supp.filter (fun j => m - j ∈ supp)).card
        = (Finset.filter (fun xy : ZMod H × ZMod H => xy.1 + xy.2 = m) (supp ×ˢ supp)).card := by
    intro m
    refine Finset.card_nbij' (fun j => (j, m - j)) (fun xy => xy.1) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter] at hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hj.1, hj.2⟩, by ring⟩
    · intro xy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hxy
      simp only [Finset.mem_coe, Finset.mem_filter]
      refine ⟨hxy.1.1, ?_⟩
      have hxe : m - xy.1 = xy.2 := by rw [← hxy.2]; ring
      rw [hxe]; exact hxy.1.2
    · intro j _; rfl
    · intro xy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hxy
      have hxe : m - xy.1 = xy.2 := by rw [← hxy.2]; ring
      simp only [hxe, Prod.mk.eta]
  -- ∑_m #fiber² = E[supp]
  have hEsum : ∑ m : ZMod H, ((supp.filter (fun j => m - j ∈ supp)).card : ℝ) ^ 2
      = (Finset.addEnergy supp supp : ℝ) := by
    rw [Finset.addEnergy_eq_sum_sq]
    push_cast
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hfibcard m]
  -- E[supp] ≤ E[𝒫_H] (no wrap ⇒ mod-H equality is integer equality)
  have hEnergyLe : (Finset.addEnergy supp supp : ℝ)
      ≤ (Finset.addEnergy (primeWindow eps H) (primeWindow eps H) : ℝ) := by
    have hnat : Finset.addEnergy supp supp
        ≤ Finset.addEnergy (primeWindow eps H) (primeWindow eps H) := by
      refine Finset.card_le_card_of_injOn
        (fun x => ((x.1.1.val, x.1.2.val), (x.2.1.val, x.2.2.val))) ?_ ?_
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hx ⊢
        obtain ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hsum⟩ := hx
        refine ⟨⟨⟨hsuppval _ ha1, hsuppval _ ha2⟩, hsuppval _ hb1, hsuppval _ hb2⟩, ?_⟩
        have := congrArg ZMod.val hsum
        rwa [hvaladd _ ha1 _ hb1, hvaladd _ ha2 _ hb2] at this
      · intro x _ y _ hxy
        simp only [Prod.mk.injEq] at hxy
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hxy
        have i := ZMod.val_injective H
        exact Prod.ext (Prod.ext (i h1) (i h2)) (Prod.ext (i h3) (i h4))
    exact_mod_cast hnat
  -- assemble via Parseval
  have h4to2 : ∑ ξ : ZMod H, ‖ZMod.dft (windowPhi eps H) ξ‖ ^ 4
      = ∑ ξ : ZMod H, ‖ZMod.dft (fun m => ∑ j : ZMod H,
            windowPhi eps H j * windowPhi eps H (m - j)) ξ‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [dft_conv_sq (windowPhi eps H) ξ, norm_pow]; ring
  rw [h4to2, dft_parseval, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hHnn
  calc ∑ m : ZMod H, ‖∑ j : ZMod H, windowPhi eps H j * windowPhi eps H (m - j)‖ ^ 2
      ≤ ∑ m : ZMod H, (M ^ 2 * ((supp.filter (fun j => m - j ∈ supp)).card : ℝ)) ^ 2 := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        exact pow_le_pow_left₀ (norm_nonneg _) (hΨle m) 2
    _ = M ^ 4 * ∑ m : ZMod H, ((supp.filter (fun j => m - j ∈ supp)).card : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)
    _ = M ^ 4 * (Finset.addEnergy supp supp : ℝ) := by rw [hEsum]
    _ ≤ M ^ 4 * (Finset.addEnergy (primeWindow eps H) (primeWindow eps H) : ℝ) :=
        mul_le_mul_of_nonneg_left hEnergyLe (by positivity)

/-- **W3-AE-c** (piece 4, the combine): the large-spectrum additive-energy
inequality.  Pieces `card_bigXi_mul_thresh_le` (Markov) ∘ `expSum_eq_dft_windowPhi`
(bridge) ∘ `dft_windowPhi_l4_le` (L⁴).  The regime hypotheses `hwin` (`p < H`) and
`hwrap` (`p+q < H`) are load-bearing for the ℤ/Hℤ Fourier route and become
regime-discharge obligations for the Lemma 3.5 assembly. -/
theorem large_spectrum_energy (eps : ℚ) (H : ℕ) [NeZero H] (heps : 0 < eps)
    (hwin : ∀ p ∈ primeWindow eps H, p < H)
    (hwrap : ∀ p ∈ primeWindow eps H, ∀ q ∈ primeWindow eps H, p + q < H) :
    ((bigXi eps H).card : ℝ) * ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) ^ 4
      ≤ (H : ℝ) * (2 / ((eps : ℝ) ^ 2 * (H : ℝ))) ^ 4
        * (Finset.addEnergy (primeWindow eps H) (primeWindow eps H) : ℝ) := by
  have hbridge : ∑ ξ : ZMod H, ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 4
      = ∑ ξ : ZMod H, ‖ZMod.dft (windowPhi eps H) ξ‖ ^ 4 := by
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [expSum_eq_dft_windowPhi eps H hwin ξ]
  calc ((bigXi eps H).card : ℝ) * ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) ^ 4
      ≤ ∑ ξ : ZMod H, ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 4 :=
        card_bigXi_mul_thresh_le eps H
    _ = ∑ ξ : ZMod H, ‖ZMod.dft (windowPhi eps H) ξ‖ ^ 4 := hbridge
    _ ≤ (H : ℝ) * (2 / ((eps : ℝ) ^ 2 * (H : ℝ))) ^ 4
          * (Finset.addEnergy (primeWindow eps H) (primeWindow eps H) : ℝ) :=
        dft_windowPhi_l4_le eps H heps hwin hwrap

end Salt.Entropy.Chowla
