/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.HB.PairSieve
import Salt.Brun.M2
import Salt.Brun.CongruenceCounting
import Salt.Brun.M5Assembly

/-!
# HB 1983 §3, Lemma 8 — the concrete AP-pair Selberg instance (WP1 / R1)

This file discharges residual **R1** of `Salt.HB.PairSieve`: it constructs the
concrete `SelbergSieve` whose `siftedSum` is the honest two-dimensional twin
count `S(d₁,d₂;z)` and feeds it into the landed conditional headline
`Salt.HB.pairSieve_lemma8`, turning it into a working Lemma 8.

## The instance

For `x d₁ d₂ z : ℕ` with `d₁, d₂` odd, squarefree, coprime, and `z`-rough (all
prime factors `> z`), the base set is the AP-pair residue window

  `A = { n ∈ (x, 2x] : d₁ ∣ n, d₂ ∣ (n+2) }`,

and we sift the values `n(n+2)` by the odd primes `≤ z` (packaged as the
primorial `P = primorial z`, which also carries `2`, matching HB's condition
that the cofactors be free of primes `< z`).  Since `d₁ d₂` is `z`-rough it is
coprime to `P`, so `Coprime P (n(n+2))` is exactly "both cofactors
`n/d₁, (n+2)/d₂` are `z`-rough" — the honest `S(d₁,d₂;z)`.

The local density is the twin `ν(p) = ρ(p)/p = 2/p` for odd `p` (reusing the
Brun-track `Salt.TwinSieve.nu`), the total mass is `x/(d₁ d₂)` (the AP class
count in a length-`x` window), and the level is `z²`.

## What is proven here (sorry-free)

* `Salt.HB.card_apResidues` — the CRT cardinality: the AP-pair + twin residues
  mod `d·d₁·d₂` number exactly `ρ(d)` (mirrors `rho_mul_of_coprime`).
* `Salt.HB.hbPairSieve` — the `SelbergSieve` instance.
* `Salt.HB.hbPairSieve_siftedSum` — `siftedSum = S(d₁,d₂;z)` as an explicit
  `Finset.card`.
* `Salt.HB.hbPairSieve_rem_abs_le` — `|rem d| ≤ 2·ρ(d)` for `d ∣ P` (the AP-pair
  remainder, via the interval CRT count).
* `Salt.HB.hb_lemma8` — the assembled Lemma 8:
  `S(d₁,d₂;z) ≤ 64·(x/(d₁ d₂))/(log z)² + E`.

## Residual (out of scope, noted)

* **R2 (the `φ(d₁d₂)` sharpening).**  We take `d₁ d₂` `z`-rough so every sifted
  prime carries the full twin density `2/p`; the coprimality-restricted
  refinement (`φ(d₁d₂)/(d₁d₂)`) is R2 of `Salt.HB.PairSieve`, untouched here.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.omega

namespace Salt.HB

/-! ## The AP-pair base set and its sifting map -/

/-- The AP-pair window `A = { n ∈ (x, 2x] : d₁ ∣ n, d₂ ∣ (n+2) }`. -/
def baseSet (x d₁ d₂ : ℕ) : Finset ℕ :=
  (Finset.Ioc x (2 * x)).filter (fun n => d₁ ∣ n ∧ d₂ ∣ (n + 2))

/-! ## The `SelbergSieve` instance -/

/-- The AP-pair twin `BoundingSieve`: sifts the values `n(n+2)` for `n ∈ A`
by the primes dividing `primorial z`, with twin density `ν = ρ/·` and total
mass `x/(d₁ d₂)`. -/
noncomputable def hbBoundingSieve (x d₁ d₂ z : ℕ) : BoundingSieve where
  support := (baseSet x d₁ d₂).image (fun n => n * (n + 2))
  prodPrimes := primorial z
  prodPrimes_squarefree := Salt.M5Assembly.primorial_squarefree z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (x : ℝ) / (d₁ * d₂)
  nu := Salt.TwinSieve.nu
  nu_mult := Salt.TwinSieve.nu_mult
  nu_pos_of_prime := fun p hp _ => Salt.TwinSieve.nu_pos_of_prime p hp
  nu_lt_one_of_prime := fun p hp _ => Salt.TwinSieve.nu_lt_one_of_prime p hp

/-- The AP-pair twin `SelbergSieve`, with level `z²`. -/
noncomputable def hbPairSieve (x d₁ d₂ z : ℕ) (hz : 1 ≤ z) : SelbergSieve where
  toBoundingSieve := hbBoundingSieve x d₁ d₂ z
  level := (z : ℝ) ^ 2
  one_le_level := by
    have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    nlinarith

variable {x d₁ d₂ z : ℕ} {hz : 1 ≤ z}

@[simp] lemma hbPairSieve_prodPrimes : (hbPairSieve x d₁ d₂ z hz).prodPrimes = primorial z := rfl
@[simp] lemma hbPairSieve_totalMass :
    (hbPairSieve x d₁ d₂ z hz).totalMass = (x : ℝ) / (d₁ * d₂) := rfl
@[simp] lemma hbPairSieve_level : (hbPairSieve x d₁ d₂ z hz).level = (z : ℝ) ^ 2 := rfl
@[simp] lemma hbPairSieve_nu : (hbPairSieve x d₁ d₂ z hz).nu = Salt.TwinSieve.nu := rfl

/-- `multSum d` counts `n ∈ A` with `d ∣ n(n+2)` (the sifting variable). -/
lemma hbPairSieve_multSum (d : ℕ) :
    (hbPairSieve x d₁ d₂ z hz).multSum d
      = (((baseSet x d₁ d₂).filter (fun n => d ∣ n * (n + 2))).card : ℝ) := by
  change (∑ m ∈ (baseSet x d₁ d₂).image (fun n => n * (n + 2)),
      if d ∣ m then (1 : ℝ) else 0) = _
  rw [Finset.sum_image (fun a _ b _ h => Salt.TwinSieve.twinProd_injective h),
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- `siftedSum` counts `n ∈ A` with `n(n+2)` coprime to `primorial z` — the
honest `S(d₁,d₂;z)`. -/
lemma hbPairSieve_siftedSum :
    (hbPairSieve x d₁ d₂ z hz).siftedSum
      = (((baseSet x d₁ d₂).filter
          (fun n => Nat.Coprime (primorial z) (n * (n + 2)))).card : ℝ) := by
  rw [BoundingSieve.siftedSum]
  change (∑ m ∈ (baseSet x d₁ d₂).image (fun n => n * (n + 2)),
      if Nat.Coprime (primorial z) m then (1 : ℝ) else 0) = _
  rw [Finset.sum_image (fun a _ b _ h => Salt.TwinSieve.twinProd_injective h),
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ## The CRT cardinality of the AP-pair + twin residues -/

/-- The residue set mod `D = d·d₁·d₂` cut out by the AP-pair conditions
`d₁ ∣ r`, `d₂ ∣ (r+2)` together with the twin condition `d ∣ r(r+2)`. -/
def apResSet (d d₁ d₂ : ℕ) : Finset ℕ :=
  (Finset.range (d * d₁ * d₂)).filter (fun r => d₁ ∣ r ∧ d₂ ∣ (r + 2) ∧ d ∣ r * (r + 2))

lemma apResSet_subset_range (d d₁ d₂ : ℕ) :
    apResSet d d₁ d₂ ⊆ Finset.range (d * d₁ * d₂) := Finset.filter_subset _ _

/-- **The CRT count.**  For `d, d₁, d₂` pairwise coprime and positive, the
residues `r < d·d₁·d₂` obeying the AP-pair conditions `d₁ ∣ r`, `d₂ ∣ (r+2)`
and the twin condition `d ∣ r(r+2)` number exactly `ρ(d)`.  Each AP condition
pins one residue (mod `d₁`, mod `d₂`), and the twin condition contributes the
`ρ(d)` solutions mod `d`; CRT (mirroring `rho_mul_of_coprime`) multiplies them. -/
lemma card_apResidues (d d₁ d₂ : ℕ) (hd : 0 < d) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hcop1 : Nat.Coprime d d₁) (hcop2 : Nat.Coprime d d₂) (hcop12 : Nat.Coprime d₁ d₂) :
    (apResSet d d₁ d₂).card = rho d := by
  rw [apResSet]
  haveI : NeZero d := ⟨hd.ne'⟩
  have hcopD : Nat.Coprime d (d₁ * d₂) := Nat.Coprime.mul_right hcop1 hcop2
  rw [← Rnat_card d]
  apply Finset.card_bij (fun r _ => r % d)
  · -- maps into `Rnat d`
    intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    exact (dvd_iff_mem_Rnat d r).mp hr.2.2.2
  · -- injective
    intro r1 h1 r2 h2 heq
    rw [Finset.mem_filter, Finset.mem_range] at h1 h2
    obtain ⟨hlt1, hd1r1, hd2r1, _⟩ := h1
    obtain ⟨hlt2, hd1r2, hd2r2, _⟩ := h2
    have hmd : r1 ≡ r2 [MOD d] := heq
    have hmd1 : r1 ≡ r2 [MOD d₁] :=
      (Nat.modEq_zero_iff_dvd.mpr hd1r1).trans (Nat.modEq_zero_iff_dvd.mpr hd1r2).symm
    have hmd2' : r1 + 2 ≡ r2 + 2 [MOD d₂] :=
      (Nat.modEq_zero_iff_dvd.mpr hd2r1).trans (Nat.modEq_zero_iff_dvd.mpr hd2r2).symm
    have hmd2 : r1 ≡ r2 [MOD d₂] := Nat.ModEq.add_right_cancel' 2 hmd2'
    have h12 : r1 ≡ r2 [MOD d₁ * d₂] := (Nat.modEq_and_modEq_iff_modEq_mul hcop12).mp ⟨hmd1, hmd2⟩
    have hD : r1 ≡ r2 [MOD d * (d₁ * d₂)] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcopD).mp ⟨hmd, h12⟩
    have hEq : r1 % (d * d₁ * d₂) = r2 % (d * d₁ * d₂) := by
      have hassoc : d * d₁ * d₂ = d * (d₁ * d₂) := by ring
      rw [hassoc]; exact hD
    rwa [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hEq
  · -- surjective
    intro s' hs'
    have hs'lt : s' < d := Rnat_lt hs'
    have hds' : d ∣ s' * (s' + 2) := (mem_Rnat_iff s' hs'lt).mp hs'
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop12 0 (2 * d₂ - 2)
    obtain ⟨w, hw_d, hw_12⟩ := Nat.chineseRemainder hcopD s' k
    set D := d * d₁ * d₂ with hD_def
    have hDpos : 0 < D := by rw [hD_def]; positivity
    have hdD : d ∣ D := ⟨d₁ * d₂, by rw [hD_def]; ring⟩
    have h12D : (d₁ * d₂) ∣ D := ⟨d, by rw [hD_def]; ring⟩
    set r := w % D with hr_def
    have hr_d : r ≡ w [MOD d] := by rw [Nat.ModEq, hr_def]; exact Nat.mod_mod_of_dvd w hdD
    have hr_12 : r ≡ w [MOD d₁ * d₂] := by rw [Nat.ModEq, hr_def]; exact Nat.mod_mod_of_dvd w h12D
    have hr_s' : r ≡ s' [MOD d] := hr_d.trans hw_d
    have hrk12 : r ≡ k [MOD d₁ * d₂] := hr_12.trans hw_12
    have hr_d1 : r ≡ k [MOD d₁] := hrk12.of_mul_right d₂
    have hr_d2 : r ≡ k [MOD d₂] := hrk12.of_mul_left d₁
    have hd1r : d₁ ∣ r := Nat.modEq_zero_iff_dvd.mp (hr_d1.trans hk1)
    have hd2r : d₂ ∣ (r + 2) := by
      have h1 : r ≡ 2 * d₂ - 2 [MOD d₂] := hr_d2.trans hk2
      have h2 : r + 2 ≡ (2 * d₂ - 2) + 2 [MOD d₂] := h1.add_right 2
      have h3 : (2 * d₂ - 2) + 2 = 2 * d₂ := by omega
      rw [h3] at h2
      exact Nat.modEq_zero_iff_dvd.mp (h2.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left d₂ 2)))
    have hdr : d ∣ r * (r + 2) := by
      have hc : r * (r + 2) ≡ s' * (s' + 2) [MOD d] := hr_s'.mul (hr_s'.add_right 2)
      exact Nat.modEq_zero_iff_dvd.mp (hc.trans (Nat.modEq_zero_iff_dvd.mpr hds'))
    refine ⟨r, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt w hDpos, hd1r, hd2r, hdr⟩
    · have : r % d = s' % d := hr_s'
      rwa [Nat.mod_eq_of_lt hs'lt] at this

/-! ## The interval count (CRT density over `(x, 2x]`) -/

/-- Splitting a `congCount` over `Icc 1 y` into the `Icc 1 x` part and the
`Ioc x y` part (`x ≤ y`). -/
lemma congCount_Ioc_eq (D : ℕ) (S : Finset ℕ) (x y : ℕ) (hxy : x ≤ y) :
    ((Finset.Ioc x y).filter (fun n => n % D ∈ S)).card + congCount D S x = congCount D S y := by
  unfold congCount
  have hsplit : Finset.Icc 1 y = Finset.Icc 1 x ∪ Finset.Ioc x y := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 x) (Finset.Ioc x y) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_Ioc] at hn'
    omega
  rw [hsplit, Finset.filter_union,
    Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  omega

/-- The count over `(x, y]` of `n` with `n % D ∈ S` differs from the density
prediction by at most twice the block count (two `congCount_bound` errors). -/
lemma congCount_Ioc_bound (D : ℕ) (S : Finset ℕ) (hD : 0 < D) (x y : ℕ) (hxy : x ≤ y) :
    |(((Finset.Ioc x y).filter (fun n => n % D ∈ S)).card : ℝ)
        - ((y : ℝ) - x) * (S ∩ Finset.range D).card / D|
      ≤ 2 * (S ∩ Finset.range D).card := by
  set k : ℝ := ((S ∩ Finset.range D).card : ℝ) with hk
  have hAeq : (((Finset.Ioc x y).filter (fun n => n % D ∈ S)).card : ℝ)
      = (congCount D S y : ℝ) - (congCount D S x : ℝ) := by
    have := congCount_Ioc_eq D S x y hxy
    have hcast : (((Finset.Ioc x y).filter (fun n => n % D ∈ S)).card : ℝ)
        + (congCount D S x : ℝ) = (congCount D S y : ℝ) := by exact_mod_cast this
    linarith
  have hy := congCount_bound D S hD y
  have hx := congCount_bound D S hD x
  rw [← hk] at hy hx
  have hexp : ((y : ℝ) - x) * k / D = (y : ℝ) * k / D - (x : ℝ) * k / D := by
    rw [sub_mul, sub_div]
  rw [hAeq, hexp, abs_le]
  rw [abs_le] at hy hx
  constructor <;> linarith [hy.1, hy.2, hx.1, hx.2]

/-! ## The AP-pair remainder bound -/

/-- The AP-pair predicate is `D`-periodic: `n` obeys it iff `n % D` lies in the
residue set `apResSet`. -/
lemma ap_pred_iff_mod (d d₁ d₂ : ℕ) (hDpos : 0 < d * d₁ * d₂) (n : ℕ) :
    (d₁ ∣ n ∧ d₂ ∣ (n + 2) ∧ d ∣ n * (n + 2))
      ↔ n % (d * d₁ * d₂) ∈ apResSet d d₁ d₂ := by
  set D := d * d₁ * d₂ with hDdef
  have hd1D : d₁ ∣ D := ⟨d * d₂, by rw [hDdef]; ring⟩
  have hd2D : d₂ ∣ D := ⟨d * d₁, by rw [hDdef]; ring⟩
  have hdD : d ∣ D := ⟨d₁ * d₂, by rw [hDdef]; ring⟩
  have hrn : n % D ≡ n [MOD D] := Nat.mod_modEq n D
  have hr1 : n % D ≡ n [MOD d₁] := hrn.of_dvd hd1D
  have hr2 : n % D ≡ n [MOD d₂] := hrn.of_dvd hd2D
  have hrd : n % D ≡ n [MOD d] := hrn.of_dvd hdD
  have dvd_congr : ∀ {kk a b : ℕ}, a ≡ b [MOD kk] → (kk ∣ a ↔ kk ∣ b) := by
    intro kk a b h
    constructor
    · exact fun hka => Nat.modEq_zero_iff_dvd.mp (h.symm.trans (Nat.modEq_zero_iff_dvd.mpr hka))
    · exact fun hkb => Nat.modEq_zero_iff_dvd.mp (h.trans (Nat.modEq_zero_iff_dvd.mpr hkb))
  rw [apResSet, Finset.mem_filter, Finset.mem_range, and_iff_right (Nat.mod_lt n hDpos)]
  exact and_congr (dvd_congr hr1).symm
    (and_congr (dvd_congr (hr2.add_right 2)).symm (dvd_congr (hrd.mul (hrd.add_right 2))).symm)

/-- **The AP-pair remainder bound.**  For `d ∣ primorial z` (hence `z`-smooth,
so coprime to the `z`-rough `d₁ d₂`) with `d₁, d₂ > 0`, the sieve remainder is
`ρ(d)`-controlled: `|rem d| ≤ 2·ρ(d)`. -/
lemma hbPairSieve_rem_abs_le (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hcop1 : Nat.Coprime d d₁) (hcop2 : Nat.Coprime d d₂) (hcop12 : Nat.Coprime d₁ d₂)
    (hd : 0 < d) :
    |(hbPairSieve x d₁ d₂ z hz).rem d| ≤ 2 * (rho d : ℝ) := by
  have hDpos : 0 < d * d₁ * d₂ := by positivity
  set D := d * d₁ * d₂ with hDdef
  -- multSum d = count over the AP window of the twin condition
  have hcount : (hbPairSieve x d₁ d₂ z hz).multSum d
      = (((Finset.Ioc x (2 * x)).filter (fun n => n % D ∈ apResSet d d₁ d₂)).card : ℝ) := by
    rw [hbPairSieve_multSum]
    congr 2
    rw [baseSet, Finset.filter_filter]
    apply Finset.filter_congr
    intro n _
    rw [← ap_pred_iff_mod d d₁ d₂ hDpos n]
    tauto
  -- the block count is ρ d
  have hinter : apResSet d d₁ d₂ ∩ Finset.range D = apResSet d d₁ d₂ :=
    Finset.inter_eq_left.mpr (apResSet_subset_range d d₁ d₂)
  have hcard : (apResSet d d₁ d₂ ∩ Finset.range D).card = rho d := by
    rw [hinter, card_apResidues d d₁ d₂ hd hd₁ hd₂ hcop1 hcop2 hcop12]
  -- rem = multSum − ν(d)·totalMass, and ν(d)·totalMass is the density prediction
  rw [BoundingSieve.rem, hcount, hbPairSieve_nu, hbPairSieve_totalMass, Salt.TwinSieve.nu_apply]
  have hbound := congCount_Ioc_bound D (apResSet d d₁ d₂) hDpos x (2 * x) (by omega)
  rw [hcard] at hbound
  -- match the density term ν(d)·totalMass = ρ(d)/d · x/(d₁d₂) = ((2x−x)·ρ(d))/D
  have hmain : (rho d : ℝ) / d * ((x : ℝ) / (d₁ * d₂))
      = ((2 * x : ℕ) - (x : ℕ) : ℝ) * (rho d : ℝ) / D := by
    have hxx : (((2 * x : ℕ) : ℝ) - (x : ℕ)) = (x : ℝ) := by push_cast; ring
    rw [hxx, hDdef]
    push_cast
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have hd10 : (d₁ : ℝ) ≠ 0 := by positivity
    have hd20 : (d₂ : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hmain]
  exact hbound

/-! ## The Selberg error sum -/

/-- A `z`-smooth divisor of the primorial is coprime to any `z`-rough modulus. -/
lemma coprime_of_smooth_rough {d e w : ℕ} (hd : d ∣ primorial w)
    (hrough : ∀ p, p.Prime → p ∣ e → w < p) : Nat.Coprime d e := by
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpd : p ∣ d := hpg.trans (Nat.gcd_dvd_left d e)
  have hpe : p ∣ e := hpg.trans (Nat.gcd_dvd_right d e)
  have hple : p ≤ w := hp.dvd_primorial_iff.mp (hpd.trans hd)
  have hpgt : w < p := hrough p hp hpe
  omega

/-- **The Selberg error sum bound.**  For `d₁ d₂` a `z`-rough coprime pair, the
`3^ω`-weighted Selberg error over the truncated divisors of `primorial z` is
`O(z⁸)`: each `d ∣ P` is `z`-smooth (hence coprime to `d₁ d₂`), giving
`|rem d| ≤ 2 ρ(d)`, so `3^ω(d)|rem d| ≤ 2·6^ω(d) ≤ 2 d³`, and there are `≤ z²`
divisors `≤ z²`, each `≤ 2 (z²)³`. -/
lemma hbPairSieve_errSum_le (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hcop12 : Nat.Coprime d₁ d₂) (hrough : ∀ p, p.Prime → p ∣ d₁ * d₂ → z < p) :
    (∑ d ∈ (hbPairSieve x d₁ d₂ z hz).prodPrimes.divisors,
        if (d : ℝ) ≤ (hbPairSieve x d₁ d₂ z hz).level then
          (3 : ℝ) ^ ω d * |(hbPairSieve x d₁ d₂ z hz).rem d| else 0)
      ≤ 2 * (z : ℝ) ^ 8 := by
  simp only [hbPairSieve_prodPrimes, hbPairSieve_level]
  -- termwise: 3^ω(d)|rem d| ≤ 2 d³ under the guard
  have hterm : ∀ d ∈ (primorial z).divisors,
      (if (d : ℝ) ≤ (z : ℝ) ^ 2 then (3 : ℝ) ^ ω d * |(hbPairSieve x d₁ d₂ z hz).rem d| else 0)
        ≤ (if (d : ℝ) ≤ (z : ℝ) ^ 2 then 2 * (d : ℝ) ^ 3 else 0) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, _⟩ := hd
    split_ifs with hg
    · have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd
        (Nat.pos_of_ne_zero (Salt.M5Assembly.primorial_squarefree z).ne_zero)
      have hsq : Squarefree d := (Salt.M5Assembly.primorial_squarefree z).squarefree_of_dvd hdvd
      have hcopP : Nat.Coprime d (d₁ * d₂) := coprime_of_smooth_rough hdvd hrough
      have hcop1 : Nat.Coprime d d₁ := hcopP.coprime_dvd_right (dvd_mul_right d₁ d₂)
      have hcop2 : Nat.Coprime d d₂ := hcopP.coprime_dvd_right (dvd_mul_left d₂ d₁)
      have hrem := hbPairSieve_rem_abs_le (x := x) (z := z) (hz := hz)
        hd₁ hd₂ hcop1 hcop2 hcop12 hd0
      have hωb : ω d = omega d := (Salt.M5Assembly.omega_eq_cardDistinctFactors d).symm
      have hrho : (rho d : ℝ) ≤ (2 : ℝ) ^ ω d := by
        rw [hωb]; exact_mod_cast rho_squarefree_le d hsq
      have h6 : (6 : ℝ) ^ ω d ≤ (d : ℝ) ^ 3 := by
        rw [hωb]; exact_mod_cast six_pow_omega_le_d_cubed hsq
      calc (3 : ℝ) ^ ω d * |(hbPairSieve x d₁ d₂ z hz).rem d|
          ≤ (3 : ℝ) ^ ω d * (2 * (rho d : ℝ)) :=
            mul_le_mul_of_nonneg_left hrem (by positivity)
        _ ≤ (3 : ℝ) ^ ω d * (2 * (2 : ℝ) ^ ω d) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hrho (by norm_num)
        _ = 2 * (6 : ℝ) ^ ω d := by
            rw [show (3 : ℝ) ^ ω d * (2 * (2 : ℝ) ^ ω d)
                = 2 * ((3 : ℝ) ^ ω d * (2 : ℝ) ^ ω d) from by ring, ← mul_pow]
            norm_num
        _ ≤ 2 * (d : ℝ) ^ 3 := by linarith
    · exact le_refl _
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- collapse each `d³` under the guard to the max `(z²)³`
  have hstep : ∀ d ∈ (primorial z).divisors,
      (if (d : ℝ) ≤ (z : ℝ) ^ 2 then 2 * (d : ℝ) ^ 3 else 0)
        ≤ (if (d : ℝ) ≤ (z : ℝ) ^ 2 then 2 * ((z : ℝ) ^ 2) ^ 3 else 0) := by
    intro d _
    split_ifs with hg
    · have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      gcongr
    · exact le_refl _
  refine le_trans (Finset.sum_le_sum hstep) ?_
  -- the guarded constant sum is `(#divisors ≤ z²)·(z²)³ ≤ z²·2(z²)³ = 2 z⁸`
  rw [← Finset.sum_filter, Finset.sum_const]
  have hFsub : (primorial z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (z : ℝ) ^ 2)
      ⊆ Finset.Icc 1 (z ^ 2) := by
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hg⟩ := hd
    rw [Finset.mem_Icc]
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd
      (Nat.pos_of_ne_zero (Salt.M5Assembly.primorial_squarefree z).ne_zero)
    refine ⟨hd0, ?_⟩
    have hle : (d : ℝ) ≤ ((z ^ 2 : ℕ) : ℝ) := by push_cast; exact hg
    exact_mod_cast hle
  have hcard : ((primorial z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (z : ℝ) ^ 2)).card
      ≤ z ^ 2 := by
    calc ((primorial z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (z : ℝ) ^ 2)).card
        ≤ (Finset.Icc 1 (z ^ 2)).card := Finset.card_le_card hFsub
      _ = z ^ 2 := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  rw [nsmul_eq_mul]
  calc (((primorial z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ (z : ℝ) ^ 2)).card : ℝ)
        * (2 * ((z : ℝ) ^ 2) ^ 3)
      ≤ ((z ^ 2 : ℕ) : ℝ) * (2 * ((z : ℝ) ^ 2) ^ 3) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
    _ = 2 * (z : ℝ) ^ 8 := by push_cast; ring

/-! ## The assembled Lemma 8 -/

/-- **HB 1983, Lemma 8 (twin case, concrete AP-pair instance).**  For `z ≥ 100`,
`d₁, d₂` a positive coprime `z`-rough pair (`z`-roughness forces both odd, since
`z ≥ 100 > 2`), the honest two-dimensional twin count over the AP window
`(x, 2x]` obeys

  `S(d₁,d₂;z) ≤ 64·(x/(d₁ d₂))/(log z)² + 2 z⁸`,

where `S(d₁,d₂;z) = #{ n ∈ (x,2x] : d₁ ∣ n, d₂ ∣ (n+2), (n(n+2), P(z)) = 1 }`.
This is `Salt.HB.pairSieve_lemma8` read at the Stone-1 instance built here;
the `z⁸` error is the crude honest Selberg remainder (R2 sharpens the main
constant, not this instance). -/
theorem hb_lemma8 (hz : 100 ≤ z) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hcop12 : Nat.Coprime d₁ d₂) (hrough : ∀ p, p.Prime → p ∣ d₁ * d₂ → z < p) :
    (((baseSet x d₁ d₂).filter
        (fun n => Nat.Coprime (primorial z) (n * (n + 2)))).card : ℝ)
      ≤ 64 * ((x : ℝ) / (d₁ * d₂)) / (Real.log z) ^ 2 + 2 * (z : ℝ) ^ 8 := by
  have hz1 : 1 ≤ z := by omega
  have hnu : ∀ p, p.Prime → p ∣ (hbPairSieve x d₁ d₂ z hz1).prodPrimes → p ≠ 2 →
      (hbPairSieve x d₁ d₂ z hz1).nu p = 2 / (p : ℝ) := by
    intro p hp _ hp2
    rw [hbPairSieve_nu, Salt.TwinSieve.nu_apply, rho_odd_prime hp hp2]
    norm_num
  have hcontains : ∀ ℓ, Odd ℓ → Squarefree ℓ → ℓ < z →
      ℓ ∣ (hbPairSieve x d₁ d₂ z hz1).prodPrimes := by
    intro ℓ _ hℓsq hℓz
    rw [hbPairSieve_prodPrimes]
    exact (Squarefree.dvd_primorial hℓsq).trans (primorial_dvd_primorial (le_of_lt hℓz))
  have key := Salt.HB.pairSieve_lemma8 (hbPairSieve x d₁ d₂ z hz1) z
    (M := (x : ℝ) / (d₁ * d₂)) (E := 2 * (z : ℝ) ^ 8) hz
    (by rw [hbPairSieve_level]) hcontains hnu (by positivity)
    (le_of_eq hbPairSieve_totalMass)
    (hbPairSieve_errSum_le (x := x) (z := z) (hz := hz1) hd₁ hd₂ hcop12 hrough)
  rwa [hbPairSieve_siftedSum] at key

end Salt.HB
