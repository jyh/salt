/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# B2 W9d — `Δ`-well-spaced ordinates and the Schur sum (a Mathlib-only LEAF)

The one predicate and the one inequality the (ξ,η) device's off-diagonal needs (design v2
§A.4, W9c): for a finite set `𝒯 ⊆ ℝ` whose distinct points are at least `Δ` apart,

    Σ_{γ' ∈ 𝒯, γ' ≠ γ} 1/(γ − γ')² ≤ (π²/3)/Δ²        for every `γ ∈ 𝒯`.

The route is the injection `γ' ↦ ±⌊|γ' − γ|/Δ⌋ ∈ ℤ ∖ {0}` — injective on each side of `γ`
because two points of `𝒯` in one half-open interval of length `Δ` would be `< Δ` apart — with
`|γ' − γ| ≥ |m|Δ` for the image `m`, so the sum is at most `2·Σ_{m ≥ 1} 1/(mΔ)² = 2ζ(2)/Δ²`
(`hasSum_zeta_two`). The lattice `{0, Δ, 2Δ, …}` at its centre reaches `3.2799` (401 points)
and `3.2889` (4001 points) against `π²/3 = 3.2899`: the constant is tight.

At `Δ = 1` the predicate is `Salt.MR.WellSpaced` (`Salt/MR/LargeValues.lean:48`) VERBATIM — the
landed predicate is the non-strict `1 ≤ |t − r|`, token-identical — but that file's closure is
eleven Salt modules and nothing in W9 consumes `WellSpaced`, so the tie is this sentence and not
a row: this file imports Mathlib only, and W9c (`JutilaHalasz.lean`) and W9e
(`DensityLogfree.lean`) import it as a leaf.

## The honest label

Nothing here bears on twin primes: the Schur sum is one input of W9c's ratio; the crown's
conditions are unchanged.
-/

namespace Salt.SW

/-- `Δ`-well-spaced: distinct points of `𝒯` are at least `Δ` apart. -/
def WellSpacedAt (Δ : ℝ) (𝒯 : Finset ℝ) : Prop := ∀ t ∈ 𝒯, ∀ r ∈ 𝒯, t ≠ r → Δ ≤ |t - r|

/-- **The one-sided Schur bound.** For a finite set `S` of reals that are all `≥ Δ` and
pairwise at least `Δ` apart, `Σ_{x ∈ S} 1/x² ≤ ζ(2)/Δ² = (π²/6)/Δ²`: index `x` by
`n(x) := ⌊x/Δ⌋ ≥ 1`, which is injective on `S` (two points with one index lie in a
half-open interval of length `Δ`, so they are `< Δ` apart), and `n(x)·Δ ≤ x`. -/
private lemma sum_inv_sq_le_of_spaced {Δ : ℝ} (hΔ : 0 < Δ) (S : Finset ℝ)
    (hlow : ∀ x ∈ S, Δ ≤ x) (hsp : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Δ ≤ |x - y|) :
    ∑ x ∈ S, 1 / x ^ 2 ≤ Real.pi ^ 2 / 6 / Δ ^ 2 := by
  classical
  have key : ∀ x ∈ S, 1 ≤ (⌊x / Δ⌋).toNat ∧ (((⌊x / Δ⌋).toNat : ℝ)) * Δ ≤ x ∧
      x < (((⌊x / Δ⌋).toNat : ℝ)) * Δ + Δ := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x / Δ := (le_div_iff₀ hΔ).mpr (by simpa using hlow x hx)
    have hf1 : (1 : ℤ) ≤ ⌊x / Δ⌋ := Int.le_floor.mpr (by exact_mod_cast hx1)
    have hcast : (((⌊x / Δ⌋).toNat : ℕ) : ℝ) = ((⌊x / Δ⌋ : ℤ) : ℝ) := by
      have hz : ((⌊x / Δ⌋).toNat : ℤ) = ⌊x / Δ⌋ := Int.toNat_of_nonneg (by omega)
      exact_mod_cast hz
    refine ⟨by omega, ?_, ?_⟩
    · rw [hcast]
      exact (le_div_iff₀ hΔ).mp (Int.floor_le (x / Δ))
    · have hlt := (div_lt_iff₀ hΔ).mp (Int.lt_floor_add_one (x / Δ))
      rw [hcast]
      linarith
  have hinj : Set.InjOn (fun x => (⌊x / Δ⌋).toNat) (S : Set ℝ) := by
    intro x hx y hy hxy
    have hxS : x ∈ S := Finset.mem_coe.mp hx
    have hyS : y ∈ S := Finset.mem_coe.mp hy
    by_contra hne
    obtain ⟨-, hx1, hx2⟩ := key x hxS
    obtain ⟨-, hy1, hy2⟩ := key y hyS
    have hxy' : (⌊x / Δ⌋).toNat = (⌊y / Δ⌋).toNat := hxy
    have hc : (((⌊x / Δ⌋).toNat : ℕ) : ℝ) = (((⌊y / Δ⌋).toNat : ℕ) : ℝ) := by
      exact_mod_cast hxy'
    rw [hc] at hx1 hx2
    have habs : |x - y| < Δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    exact absurd (hsp x hxS y hyS hne) (not_le.mpr habs)
  have hstep : ∀ x ∈ S, 1 / x ^ 2 ≤ 1 / (((⌊x / Δ⌋).toNat : ℝ) * Δ) ^ 2 := by
    intro x hx
    obtain ⟨hn1, hle, -⟩ := key x hx
    have hn0 : 0 < (⌊x / Δ⌋).toNat := by omega
    have hnpos : (0 : ℝ) < ((⌊x / Δ⌋).toNat : ℝ) := by exact_mod_cast hn0
    have hpos : (0 : ℝ) < ((⌊x / Δ⌋).toNat : ℝ) * Δ := mul_pos hnpos hΔ
    exact one_div_le_one_div_of_le (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hle 2)
  calc ∑ x ∈ S, 1 / x ^ 2
      ≤ ∑ x ∈ S, 1 / (((⌊x / Δ⌋).toNat : ℝ) * Δ) ^ 2 := Finset.sum_le_sum hstep
    _ = ∑ n ∈ S.image (fun x => (⌊x / Δ⌋).toNat), 1 / ((n : ℝ) * Δ) ^ 2 :=
        (Finset.sum_image (f := fun n : ℕ => 1 / ((n : ℝ) * Δ) ^ 2) hinj).symm
    _ = (∑ n ∈ S.image (fun x => (⌊x / Δ⌋).toNat), 1 / (n : ℝ) ^ 2) / Δ ^ 2 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun n _ => by rw [mul_pow, ← div_div]
    _ ≤ Real.pi ^ 2 / 6 / Δ ^ 2 :=
        div_le_div_of_nonneg_right
          (sum_le_hasSum _ (fun n _ => by positivity) hasSum_zeta_two) (by positivity)

/-- **The Schur sum of a `Δ`-spaced system**: `Σ_{γ' ≠ γ} 1/(γ − γ')² ≤ (π²/3)/Δ²`. -/
theorem sum_inv_sq_sub_le_of_wellSpacedAt {Δ : ℝ} (hΔ : 0 < Δ) {𝒯 : Finset ℝ}
    (h : WellSpacedAt Δ 𝒯) {γ : ℝ} (hγ : γ ∈ 𝒯) :
    ∑ γ' ∈ 𝒯.erase γ, 1 / (γ - γ') ^ 2 ≤ Real.pi ^ 2 / 3 / Δ ^ 2 := by
  classical
  have hHi : ∑ x ∈ 𝒯.erase γ with γ < x, 1 / (γ - x) ^ 2 ≤ Real.pi ^ 2 / 6 / Δ ^ 2 := by
    have hinj : Set.InjOn (fun x => x - γ) ((𝒯.erase γ).filter (fun x => γ < x) : Set ℝ) := by
      intro a _ b _ hab
      have : a - γ = b - γ := hab
      linarith
    have hlow : ∀ z ∈ ((𝒯.erase γ).filter (fun x => γ < x)).image (fun x => x - γ), Δ ≤ z := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hxf, hlt⟩ := Finset.mem_filter.mp hx
      have hxT : x ∈ 𝒯 := (Finset.mem_erase.mp hxf).2
      have hgap := h γ hγ x hxT (ne_of_lt hlt)
      have hneg : γ - x < 0 := by linarith
      rwa [abs_of_neg hneg, neg_sub] at hgap
    have hsp : ∀ z ∈ ((𝒯.erase γ).filter (fun x => γ < x)).image (fun x => x - γ),
        ∀ w ∈ ((𝒯.erase γ).filter (fun x => γ < x)).image (fun x => x - γ),
          z ≠ w → Δ ≤ |z - w| := by
      intro z hz w hw hzw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
      have hxT : x ∈ 𝒯 := (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2
      have hyT : y ∈ 𝒯 := (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).2
      have hne : x ≠ y := fun hxy => hzw (by rw [hxy])
      have hrw : x - γ - (y - γ) = x - y := by ring
      rw [hrw]
      exact h x hxT y hyT hne
    calc ∑ x ∈ 𝒯.erase γ with γ < x, 1 / (γ - x) ^ 2
        = ∑ x ∈ 𝒯.erase γ with γ < x, 1 / (x - γ) ^ 2 :=
          Finset.sum_congr rfl fun x _ => by ring
      _ = ∑ z ∈ ((𝒯.erase γ).filter (fun x => γ < x)).image (fun x => x - γ), 1 / z ^ 2 :=
          (Finset.sum_image (f := fun z : ℝ => 1 / z ^ 2) hinj).symm
      _ ≤ Real.pi ^ 2 / 6 / Δ ^ 2 := sum_inv_sq_le_of_spaced hΔ _ hlow hsp
  have hLo : ∑ x ∈ 𝒯.erase γ with ¬ γ < x, 1 / (γ - x) ^ 2 ≤ Real.pi ^ 2 / 6 / Δ ^ 2 := by
    have hinj : Set.InjOn (fun x => γ - x) ((𝒯.erase γ).filter (fun x => ¬ γ < x) : Set ℝ) := by
      intro a _ b _ hab
      have : γ - a = γ - b := hab
      linarith
    have hlow : ∀ z ∈ ((𝒯.erase γ).filter (fun x => ¬ γ < x)).image (fun x => γ - x), Δ ≤ z := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hxf, hnlt⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxne, hxT⟩ := Finset.mem_erase.mp hxf
      have hlt : x < γ := lt_of_le_of_ne (not_lt.mp hnlt) hxne
      have hgap := h γ hγ x hxT (ne_of_gt hlt)
      have hpos : 0 < γ - x := by linarith
      rwa [abs_of_pos hpos] at hgap
    have hsp : ∀ z ∈ ((𝒯.erase γ).filter (fun x => ¬ γ < x)).image (fun x => γ - x),
        ∀ w ∈ ((𝒯.erase γ).filter (fun x => ¬ γ < x)).image (fun x => γ - x),
          z ≠ w → Δ ≤ |z - w| := by
      intro z hz w hw hzw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
      have hxT : x ∈ 𝒯 := (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2
      have hyT : y ∈ 𝒯 := (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).2
      have hne : y ≠ x := fun hxy => hzw (by rw [hxy])
      have hrw : γ - x - (γ - y) = y - x := by ring
      rw [hrw]
      exact h y hyT x hxT hne
    calc ∑ x ∈ 𝒯.erase γ with ¬ γ < x, 1 / (γ - x) ^ 2
        = ∑ z ∈ ((𝒯.erase γ).filter (fun x => ¬ γ < x)).image (fun x => γ - x), 1 / z ^ 2 :=
          (Finset.sum_image (f := fun z : ℝ => 1 / z ^ 2) hinj).symm
      _ ≤ Real.pi ^ 2 / 6 / Δ ^ 2 := sum_inv_sq_le_of_spaced hΔ _ hlow hsp
  have hsplit := Finset.sum_filter_add_sum_filter_not (𝒯.erase γ) (fun x => γ < x)
    (fun x => 1 / (γ - x) ^ 2)
  have harith : Real.pi ^ 2 / 3 / Δ ^ 2 = Real.pi ^ 2 / 6 / Δ ^ 2 + Real.pi ^ 2 / 6 / Δ ^ 2 := by
    ring
  rw [← hsplit, harith]
  exact add_le_add hHi hLo

/-- **The W9d exit row**: the lattice `{0, 1, 2}` at `Δ = 1`, centre `1` — `1 + 1 ≤ π²/3`,
INVOKING the row with a point on EACH side of the centre (the injection's negative branch
exercised; the `WellSpacedAt` side condition discharged by cases). -/
example : ∑ γ' ∈ ({0, 1, 2} : Finset ℝ).erase 1, 1 / ((1 : ℝ) - γ') ^ 2
    ≤ Real.pi ^ 2 / 3 / (1 : ℝ) ^ 2 :=
  sum_inv_sq_sub_le_of_wellSpacedAt one_pos (by
    intro t ht r hr hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht hr
    rcases ht with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> norm_num at hne <;>
      norm_num [abs_neg, abs_of_nonneg, abs_of_nonpos]) (by simp)

end Salt.SW
