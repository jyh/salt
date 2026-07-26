/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetThin
import Salt.MR.HalaszPrimesCore
import Salt.Mertens.Third

/-!
# USetThinTL — the `𝒯_L` branch of `hU` (U-8)

MR v4 §8.3, p.29: after the well-spaced discretisation `𝒯` of `𝒰` and the split at the
level `δ'` of the prime block polynomial `Q_{j,H}`, the branch `𝒯_L` where `Q_{j,H}` is
LARGE is killed by four steps:

1. **`|𝒯_L|` is small and `T`-free** — Lemma 8 (`large_value_count`) at the level
   `V = (log X)^{100}` gives `|𝒯_L| ≤ exp((log X)^{θ+o(1)})`; the `T`-freeness is MR's
   Step 0 (`T ≤ X`, everything above rides the trivial mean-value theorem).
2. **Lemma 11** (`halasz_primes_pow`) bounds `Σ_{t∈𝒯_L} ‖Q_{j,H}(1+it)‖²` with the
   Vinogradov–Korobov decay `exp(−c·log P/((log T)^{3/4}(loglog T)⁴))` multiplying `|𝒯_L|`.
3. **The kill**: the decay beats the count — `(1/4 − θ)` against `θ` in the exponent.
4. **The prime-window gain** `Σ_{p ∈ block} 1/p ≍ 1/v` (MR p.29: "the extra logarithm the
   whole apparatus exists to save"), via sharp Mertens-2.

## The stones

* U-8a `ramQ_eq_dpoly` / `ramQ_eq_halaszSum` — the two adapters.  `ramQ` is a `σ = 1`
  Dirichlet polynomial, hence a `dpoly` at the **negated** ordinate (CATCH #B: Lemma 8's
  `dpoly` is `P(1−it)`, so the counted set is `−𝒯`); it is *also*, with no sign flip, the
  `Σ_p p^{−it}·a_p` shape of Lemma 11 at `a_p = c_p/p`.
  `ramQbase` is the block's dyadic base: every block prime lies in `[base, 2·base]`
  (`e^{1/H} ≤ 2` at `H ≥ 2` — the `⌊H log p⌋ = j` fiber is a ratio-`≤2` window).
* U-8b `ramQ_large_count` / `ramQ_large_count_Tfree` — Lemma 8 on `𝒯_L`.
  **THE X₀ LAW (law #253).**  `large_value_count`'s `hκ30 : 30 ≤ log T / log base` is a
  growing-quantity gate: at the §8.3 pin `base ≈ exp((log X)^{1−θ})` and `T ≈ X` it forces
  `log X ≥ 30^{3/ρ} ≈ 10^{385}`.  It is carried **in-statement, verbatim**, at every rung
  of this file and never absorbed; the consumer inherits the resulting `X₀`.
* U-8c `tL_sumsq_ramQ` — Lemma 11 on `𝒯_L`.  Its three gates discharge at the pin:
  `P ≤ T^10` is *free from `hκ30`* (`log base ≤ log T/30 ≤ 10 log T`), `WellSpaced 𝒯_L`
  comes from `𝒯_L ⊆ 𝒯`, and `S ⊆ [P,2P]` is the block geometry above.
* U-8d `ramQblock_inv_sum_le` — the prime-window gain `Σ_{p∈block} 1/p ≤ 27·H/j = 27/v`.
* U-8e `tL_kill` / `tL_ramQ_sumsq_killed` / `tL_main_sumsq` — the kill arithmetic and the
  exit.  The kill gate is stated as the explicit `X₀` hypothesis
  `420·L·L^{3/4}·(log L)^5 ≤ c·W²` (`L ≥ log T`, `W = log base`); at the pin
  `W = L^{1−θ}` it reads `420 (log L)^5 ≤ c·L^{1/4−2θ}`, satisfiable exactly when
  `θ < 1/8` — the honest margin at `θ = ρ/3`, `ρ = 1/(32e)`, is the exponent ratio
  `(1/4 − θ)/θ ≈ 64`.

Nothing here is `𝒰`-specific: `𝒯_L` is defined against an arbitrary well-spaced `𝒯`, so
the file composes with U-3's discretisation without re-pinning any set.

Source pins (D5): MR arXiv v4 (`1501.04585v4`) pp. 19 (the blocks), 29 (the `𝒯_L` page).
-/

namespace Salt.MR

open Finset Complex MeasureTheory
open scoped BigOperators

/-! ## U-8a — the block geometry and the two adapters -/

/-- Membership in the Ramaré prime block, unpacked. -/
lemma mem_ramQblock {H : ℝ} {P Q j p : ℕ} (hp : p ∈ ramQblock H P Q j) :
    P ≤ p ∧ p ≤ Q ∧ p.Prime ∧ Real.exp ((j : ℝ) / H) ≤ (p : ℝ) ∧
      (p : ℝ) < Real.exp (((j : ℝ) + 1) / H) := by
  rw [ramQblock, Finset.mem_filter, Finset.mem_Icc] at hp
  exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2.1, hp.2.2.2⟩

/-- **The block's dyadic base** `max P ⌈e^{j/H}⌉`: a natural number at or below every block
prime, at least half of every block prime, and of logarithm at least the block height
`v = j/H`. -/
noncomputable def ramQbase (H : ℝ) (P j : ℕ) : ℕ := max P ⌈Real.exp ((j : ℝ) / H)⌉₊

/-- The base is at most every block prime. -/
lemma ramQbase_le_of_mem {H : ℝ} {P Q j p : ℕ} (hp : p ∈ ramQblock H P Q j) :
    ramQbase H P j ≤ p := by
  obtain ⟨hP, _, _, hlow, _⟩ := mem_ramQblock hp
  exact max_le hP (Nat.ceil_le.mpr hlow)

/-- The block height `e^{j/H}` is at most the base. -/
lemma exp_le_ramQbase (H : ℝ) (P j : ℕ) :
    Real.exp ((j : ℝ) / H) ≤ (ramQbase H P j : ℝ) := by
  refine le_trans (Nat.le_ceil _) ?_
  exact_mod_cast Nat.cast_le.mpr (le_max_right P ⌈Real.exp ((j : ℝ) / H)⌉₊)

/-- `e^{1/H} ≤ 2` at `H ≥ 2` — the reason the `⌊H log p⌋ = j` fiber is a ratio-`≤2`
window (MR p.19). -/
lemma exp_inv_le_two {H : ℝ} (hH : 2 ≤ H) : Real.exp (1 / H) ≤ 2 := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hhalf : 1 / H ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hH0 (by norm_num : (0:ℝ) < 2)]; linarith
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos : 0 < Real.exp (1 / 2) := Real.exp_pos _
  have h2 : Real.exp (1 / 2) ≤ 2 := by nlinarith
  exact le_trans (Real.exp_le_exp.mpr hhalf) h2

/-- Every block prime is at most twice the base (the ratio-`≤2` window). -/
lemma ramQblock_le_two_base {H : ℝ} (hH : 2 ≤ H) {P Q j p : ℕ}
    (hp : p ∈ ramQblock H P Q j) : p ≤ 2 * ramQbase H P j := by
  obtain ⟨_, _, _, _, hup⟩ := mem_ramQblock hp
  have hH0 : (0 : ℝ) < H := by linarith
  have hsplit : Real.exp (((j : ℝ) + 1) / H)
      = Real.exp ((j : ℝ) / H) * Real.exp (1 / H) := by
    rw [← Real.exp_add]; congr 1; field_simp
  have hbase := exp_le_ramQbase H P j
  have hexp2 := exp_inv_le_two hH
  have hep : 0 < Real.exp ((j : ℝ) / H) := Real.exp_pos _
  have hlt : (p : ℝ) < 2 * (ramQbase H P j : ℝ) := by
    rw [hsplit] at hup
    nlinarith
  have hnat : p < 2 * ramQbase H P j := by exact_mod_cast hlt
  omega

/-- Block members are prime. -/
lemma ramQblock_prime {H : ℝ} {P Q j p : ℕ} (hp : p ∈ ramQblock H P Q j) : p.Prime :=
  (mem_ramQblock hp).2.2.1

/-- **The Lemma-8 coefficient source of the Ramaré block**: `c` restricted to
`ramQblock H P Q j` (the `σ = 1` numerator; `dpoly` carries `ramQsrc n / n`). -/
noncomputable def ramQsrc (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ ramQblock H P Q j then c n else 0

/-- `ramQsrc` vanishes off the block. -/
lemma ramQsrc_eq_zero {H : ℝ} {P Q j n : ℕ} {c : ℕ → ℂ}
    (hn : n ∉ ramQblock H P Q j) : ramQsrc H P Q j c n = 0 := by
  rw [ramQsrc, if_neg hn]

/-- The block prime polynomial is the `σ = 1` polynomial of its own restricted
coefficients (mirror of `primeBlockPoly_eq_spoly`, `Salt.MR.USetThin`). -/
lemma ramQ_eq_spoly (H : ℝ) (P Q N j : ℕ) (c : ℕ → ℂ)
    (hN : ∀ p ∈ ramQblock H P Q j, p ≤ N) (t : ℝ) :
    ramQ H P Q j c t = spoly N (ramQsrc H P Q j c) t := by
  unfold ramQ spoly
  have h1 : ∑ p ∈ ramQblock H P Q j, c p / (p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
      = ∑ p ∈ ramQblock H P Q j,
          ramQsrc H P Q j c p / (p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [ramQsrc, if_pos hp]
  rw [h1]
  refine Finset.sum_subset (fun p hp => ?_) (fun n _ hnot => ?_)
  · exact Finset.mem_Icc.mpr ⟨(ramQblock_prime hp).pos, hN p hp⟩
  · rw [ramQsrc_eq_zero hnot, zero_div]

/-- **U-8a, the `−𝒯` sign bridge (CATCH #B).**  `ramQ H P Q j c t = dpoly N (src/n) (−t)`:
Lemma 8's `dpoly` is `P(1−it)`, so a caller with `|Q_{j,H}(1+it)|` large hands Lemma 8 the
NEGATED ordinate set. -/
lemma ramQ_eq_dpoly (H : ℝ) (P Q N j : ℕ) (c : ℕ → ℂ)
    (hN : ∀ p ∈ ramQblock H P Q j, p ≤ N) (t : ℝ) :
    ramQ H P Q j c t = dpoly N (fun n => ramQsrc H P Q j c n / (n : ℂ)) (-t) := by
  rw [ramQ_eq_spoly H P Q N j c hN t, spoly_eq_dpoly]

/-- **U-8a, the Lemma-11 shape (no sign flip).**  `ramQ H P Q j c t = Σ_p p^{−it}·(c_p/p)`
— exactly the integrand of `halasz_primes_pow` at `a_p = c_p/p`. -/
lemma ramQ_eq_halaszSum (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    ramQ H P Q j c t
      = ∑ p ∈ ramQblock H P Q j, (p : ℂ) ^ (-(t : ℂ) * Complex.I) * (c p / (p : ℂ)) := by
  unfold ramQ
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hppos := (ramQblock_prime hp).pos
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : p ≠ 0)
  have h1 : (p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
      = (p : ℂ) * (p : ℂ) ^ ((t : ℂ) * Complex.I) := by
    rw [Complex.cpow_add _ _ hp0, Complex.cpow_one]
  have h2 : (p : ℂ) ^ (-(t : ℂ) * Complex.I) = ((p : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ := by
    rw [neg_mul, Complex.cpow_neg]
  have h3 : (p : ℂ) ^ ((t : ℂ) * Complex.I) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h0, _⟩; exact hp0 h0
  rw [h1, h2]
  field_simp

/-! ## U-8b — the large-value count of `𝒯_L` (Lemma 8)

**THE X₀ LAW (law #253).**  `hκ30 : 30 ≤ log T / log base` is carried in-statement at every
rung below.  At the §8.3 pin (`base ≈ exp((log X)^{1−θ})`, `T ≍ X`) it says
`(log X)^θ ≥ 30`, i.e. `log X ≥ 30^{1/θ} = 30^{3/ρ} ≈ 10^{385}` — the dominant threshold of
the whole seam row.  It is never absorbed into a constant. -/

/-- **`𝒯_L`** (MR p.29): the ordinates of a well-spaced `𝒯` at which the prime block
polynomial `Q_{j,H}(1+it)` EXCEEDS the split level `δ'`.  (MR splits at
`δ' = (log X)^{−100}`; the level is a parameter here.) -/
noncomputable def tLset (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (δ' : ℝ) (𝒯 : Finset ℝ) :
    Finset ℝ :=
  𝒯.filter (fun t => δ' < ‖ramQ H P Q j c t‖)

/-- `𝒯_L ⊆ 𝒯`. -/
lemma tLset_subset (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (δ' : ℝ) (𝒯 : Finset ℝ) :
    tLset H P Q j c δ' 𝒯 ⊆ 𝒯 := Finset.filter_subset _ _

/-- Membership in `𝒯_L`, unpacked. -/
lemma mem_tLset {H : ℝ} {P Q j : ℕ} {c : ℕ → ℂ} {δ' : ℝ} {𝒯 : Finset ℝ} {t : ℝ}
    (ht : t ∈ tLset H P Q j c δ' 𝒯) : t ∈ 𝒯 ∧ δ' < ‖ramQ H P Q j c t‖ := by
  rw [tLset, Finset.mem_filter] at ht
  exact ht

/-- `𝒯_L` inherits well-spacing. -/
lemma tLset_wellSpaced {H : ℝ} {P Q j : ℕ} {c : ℕ → ℂ} {δ' : ℝ} {𝒯 : Finset ℝ}
    (hws : WellSpaced 𝒯) : WellSpaced (tLset H P Q j c δ' 𝒯) :=
  wellSpaced_of_subset (tLset_subset H P Q j c δ' 𝒯) hws

/-- **U-8b (the raw count).**  Lemma 8 (`large_value_count`) applied to the Ramaré prime
block through the `−𝒯` sign bridge: a well-spaced `𝒮 ⊆ [−T,T]` on which
`‖Q_{j,H}(1+it)‖ ≥ V⁻¹` is counted at the block's own dyadic base.  Gates carried verbatim
from Lemma 8, `hκ30` included (the X₀ law). -/
theorem ramQ_large_count {H : ℝ} (hH : 2 ≤ H) (P Q j : ℕ) (c : ℕ → ℂ)
    (hc1 : ∀ n : ℕ, ‖c n‖ ≤ 1) (T V : ℝ)
    (hB3 : 3 ≤ ramQbase H P j) (hT : 1 < T) (hBT : (ramQbase H P j : ℝ) ≤ T) (hV : 1 ≤ V)
    (hκ30 : 30 ≤ Real.log T / Real.log (ramQbase H P j))
    (hLL5 : 5 ≤ Real.log (Real.log T))
    (𝒮 : Finset ℝ) (hws : WellSpaced 𝒮) (hsub : ∀ t ∈ 𝒮, t ∈ Set.Icc (-T) T)
    (hlb : ∀ t ∈ 𝒮, V⁻¹ ≤ ‖ramQ H P Q j c t‖) :
    (𝒮.card : ℝ)
      ≤ 840 * T ^ (2 * Real.log V / Real.log (ramQbase H P j)) * V ^ 2
          * Real.exp (2 * (Real.log T / Real.log (ramQbase H P j))
              * Real.log (Real.log T)) := by
  classical
  set B := ramQbase H P j with hBdef
  set src : ℕ → ℂ := fun n => ramQsrc H P Q j c n / (n : ℂ) with hsrcdef
  have hN : ∀ p ∈ ramQblock H P Q j, p ≤ 2 * B := fun p hp => ramQblock_le_two_base hH hp
  -- the negated ordinate set (CATCH #B)
  have hcard : (𝒮.image (fun t => -t)).card = 𝒮.card :=
    Finset.card_image_of_injective _ neg_injective
  have hws' : WellSpaced (𝒮.image (fun t => -t)) := by
    intro s hs r hr hne
    rw [Finset.mem_image] at hs hr
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨u, hu, rfl⟩ := hr
    have htu : t ≠ u := fun h => hne (by rw [h])
    have h := hws t ht u hu htu
    rwa [show -t - -u = -(t - u) by ring, abs_neg]
  have hsub' : ∀ s ∈ 𝒮.image (fun t => -t), s ∈ Set.Icc (-T) T := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have h := Set.mem_Icc.mp (hsub t ht)
    exact Set.mem_Icc.mpr ⟨by linarith [h.2], by linarith [h.1]⟩
  -- the Lemma-8 coefficient gates
  have hsupp : ∀ m, src m ≠ 0 → m.Prime ∧ B ≤ m := by
    intro m hm
    by_cases hmem : m ∈ ramQblock H P Q j
    · exact ⟨ramQblock_prime hmem, ramQbase_le_of_mem hmem⟩
    · exact absurd (by simp only [hsrcdef, ramQsrc_eq_zero hmem, zero_div]) hm
  have hcoeff : ∀ m, src m ≠ 0 → ‖src m‖ ≤ (m : ℝ)⁻¹ := by
    intro m hm
    obtain ⟨hpr, _⟩ := hsupp m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hpr.pos
    by_cases hmem : m ∈ ramQblock H P Q j
    · simp only [hsrcdef, ramQsrc, if_pos hmem, norm_div, Complex.norm_natCast]
      rw [inv_eq_one_div]
      gcongr
      exact hc1 m
    · exact absurd (by simp only [hsrcdef, ramQsrc_eq_zero hmem, zero_div]) hm
  have hlb' : ∀ s ∈ 𝒮.image (fun t => -t), V⁻¹ ≤ ‖dpoly (2 * B) src s‖ := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [← ramQ_eq_dpoly H P Q (2 * B) j c hN t]
    exact hlb t ht
  have h := large_value_count B src T V hB3 hT hBT hV hκ30 hLL5
    (𝒮.image (fun t => -t)) hws' hsub' hsupp hcoeff hlb'
  rwa [hcard] at h

/-- **U-8b, the `T`-free shape (MR Step 0).**  With `log T ≤ L` (`T ≤ X`, the range above
which the trivial mean-value theorem takes over) the Lemma-8 count loses all `T`-dependence:
`|𝒮| ≤ 840·V²·exp(2(L/log base)(log V + log L))`.  At the pin
`base ≈ exp(L^{1−θ})`, `V = L^{100}` this is `exp(L^{θ+o(1)})`. -/
theorem ramQ_large_count_Tfree {H : ℝ} (hH : 2 ≤ H) (P Q j : ℕ) (c : ℕ → ℂ)
    (hc1 : ∀ n : ℕ, ‖c n‖ ≤ 1) (T V L : ℝ)
    (hB3 : 3 ≤ ramQbase H P j) (hT : 1 < T) (hBT : (ramQbase H P j : ℝ) ≤ T) (hV : 1 ≤ V)
    (hκ30 : 30 ≤ Real.log T / Real.log (ramQbase H P j))
    (hLL5 : 5 ≤ Real.log (Real.log T)) (hTL : Real.log T ≤ L)
    (𝒮 : Finset ℝ) (hws : WellSpaced 𝒮) (hsub : ∀ t ∈ 𝒮, t ∈ Set.Icc (-T) T)
    (hlb : ∀ t ∈ 𝒮, V⁻¹ ≤ ‖ramQ H P Q j c t‖) :
    (𝒮.card : ℝ)
      ≤ 840 * V ^ 2 * Real.exp (2 * (L / Real.log (ramQbase H P j))
          * (Real.log V + Real.log L)) := by
  have hraw := ramQ_large_count hH P Q j c hc1 T V hB3 hT hBT hV hκ30 hLL5 𝒮 hws hsub hlb
  set W := Real.log (ramQbase H P j) with hWdef
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT0 : 0 < Real.log T := Real.log_pos hT
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log T) := by linarith
  have hW0 : 0 < W := by
    rw [hWdef]
    refine Real.log_pos ?_
    have : (3 : ℝ) ≤ (ramQbase H P j : ℝ) := by exact_mod_cast hB3
    linarith
  have hlogV0 : 0 ≤ Real.log V := Real.log_nonneg hV
  have hL0 : 0 < L := by linarith
  have hlogL : Real.log (Real.log T) ≤ Real.log L := Real.log_le_log hlogT0 hTL
  -- the `T`-power leg
  have hpow : T ^ (2 * Real.log V / W) = Real.exp (2 * Real.log V / W * Real.log T) := by
    rw [Real.rpow_def_of_pos hT0]; ring_nf
  have hleg1 : T ^ (2 * Real.log V / W) ≤ Real.exp (2 * (L / W) * Real.log V) := by
    rw [hpow]
    refine Real.exp_le_exp.mpr ?_
    have hc : (0 : ℝ) ≤ 2 * Real.log V / W := by positivity
    calc 2 * Real.log V / W * Real.log T
        ≤ 2 * Real.log V / W * L := mul_le_mul_of_nonneg_left hTL hc
      _ = 2 * (L / W) * Real.log V := by ring
  -- the `exp` leg
  have hleg2 : Real.exp (2 * (Real.log T / W) * Real.log (Real.log T))
      ≤ Real.exp (2 * (L / W) * Real.log L) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : Real.log T / W ≤ L / W := by gcongr
    have h2 : (0 : ℝ) ≤ Real.log T / W := by positivity
    nlinarith
  have hV0 : (0 : ℝ) < V := by linarith
  calc (𝒮.card : ℝ)
      ≤ 840 * T ^ (2 * Real.log V / W) * V ^ 2
          * Real.exp (2 * (Real.log T / W) * Real.log (Real.log T)) := hraw
    _ ≤ 840 * Real.exp (2 * (L / W) * Real.log V) * V ^ 2
          * Real.exp (2 * (L / W) * Real.log L) := by
        gcongr
    _ = 840 * V ^ 2 * Real.exp (2 * (L / W) * (Real.log V + Real.log L)) := by
        rw [show 2 * (L / W) * (Real.log V + Real.log L)
              = 2 * (L / W) * Real.log V + 2 * (L / W) * Real.log L from by ring,
          Real.exp_add]
        ring

/-! ## U-8c — Lemma 11 on `𝒯_L` (`halasz_primes_pow`, frozen header)

The three gates of the frozen header discharge at the §8.3 pin:
`WellSpaced` and `⊆ [−T,T]` descend from `𝒯` to `𝒯_L`; `S ⊆ [P,2P]` is the block geometry
(`ramQbase`); and `P ≤ T^10` is **free from the X₀ gate `hκ30`** — see
`ramQbase_le_pow_ten`. -/

/-- **The `P ≤ T^10` gate is free at the pin.**  Lemma 8's X₀ gate `30 ≤ log T/log base`
already forces `log base ≤ log T/30`, hence `base ≤ T^{1/30} ≤ T^{10}` — the third gate of
`halasz_primes_pow` costs nothing. -/
lemma ramQbase_le_pow_ten {H : ℝ} {P j : ℕ} {T : ℝ} (hT : 1 < T) (hB3 : 3 ≤ ramQbase H P j)
    (hκ30 : 30 ≤ Real.log T / Real.log (ramQbase H P j)) :
    (ramQbase H P j : ℝ) ≤ T ^ 10 := by
  have hB1 : (1 : ℝ) < (ramQbase H P j : ℝ) := by
    have : (3 : ℝ) ≤ (ramQbase H P j : ℝ) := by exact_mod_cast hB3
    linarith
  have hW0 : 0 < Real.log (ramQbase H P j) := Real.log_pos hB1
  have hlogT0 : 0 < Real.log T := Real.log_pos hT
  have h30 : 30 * Real.log (ramQbase H P j) ≤ Real.log T := by
    rw [le_div_iff₀ hW0] at hκ30; linarith
  have hlog : Real.log (ramQbase H P j) ≤ Real.log (T ^ 10) := by
    rw [Real.log_pow]; push_cast; linarith
  exact (Real.log_le_log_iff (by linarith) (by positivity)).mp hlog

/-- **U-8c — MR Lemma 11 on the Ramaré block.**  `halasz_primes_pow` instantiated at
`S = ramQblock H P Q j`, `a_p = c_p/p`, `P = ramQbase H P j`: for any well-spaced
`𝒮 ⊆ [−T,T]`,

`Σ_{t∈𝒮} ‖Q_{j,H}(1+it)‖² ≤ C·(B + |𝒮|·B·exp(−c·log B/((log T)^{3/4}(loglog T)⁴))·(log T)²)`
`  /log B · Σ_{p∈block}‖c_p/p‖²`,

with `C, c, T₀` the frozen existentials of Lemma 11. -/
theorem tL_sumsq_ramQ :
    ∃ C c T₀ : ℝ, 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧
      ∀ (H : ℝ), 2 ≤ H → ∀ (P Q j : ℕ) (cf : ℕ → ℂ) (T : ℝ), T₀ ≤ T →
      2 ≤ (ramQbase H P j : ℝ) → (ramQbase H P j : ℝ) ≤ T ^ 10 →
      ∀ 𝒮 : Finset ℝ, WellSpaced 𝒮 → (∀ t ∈ 𝒮, t ∈ Set.Icc (-T) T) →
        ∑ t ∈ 𝒮, ‖ramQ H P Q j cf t‖ ^ 2
          ≤ C * ((ramQbase H P j : ℝ) + (𝒮.card : ℝ) * (ramQbase H P j : ℝ)
                  * Real.exp (-c * Real.log (ramQbase H P j)
                      / ((Real.log T) ^ ((3 : ℝ) / 4)
                          * (Real.log (Real.log T)) ^ (4 : ℕ)))
                  * (Real.log T) ^ 2)
              / Real.log (ramQbase H P j)
              * ∑ p ∈ ramQblock H P Q j, ‖cf p / (p : ℂ)‖ ^ 2 := by
  obtain ⟨C, c, T₀, hC, hc, hT₀, hmain⟩ := halasz_primes_pow
  refine ⟨C, c, T₀, hC, hc, hT₀, ?_⟩
  intro H hH P Q j cf T hT hB2 hBT10 𝒮 hws hsub
  have hS : ∀ n ∈ ramQblock H P Q j,
      n.Prime ∧ (ramQbase H P j : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (ramQbase H P j : ℝ) := by
    intro n hn
    refine ⟨ramQblock_prime hn, ?_, ?_⟩
    · exact_mod_cast ramQbase_le_of_mem hn
    · have := ramQblock_le_two_base hH hn
      have hcast : (n : ℝ) ≤ ((2 * ramQbase H P j : ℕ) : ℝ) := by exact_mod_cast this
      rwa [Nat.cast_mul, Nat.cast_ofNat] at hcast
  have h := hmain T (ramQbase H P j : ℝ) hT hB2 hBT10 𝒮 hws hsub (ramQblock H P Q j) hS
    (fun p => cf p / (p : ℂ))
  have hcongr : ∑ t ∈ 𝒮, ‖ramQ H P Q j cf t‖ ^ 2
      = ∑ t ∈ 𝒮, ‖∑ p ∈ ramQblock H P Q j,
          (p : ℂ) ^ (-(t : ℂ) * Complex.I) * (cf p / (p : ℂ))‖ ^ 2 :=
    Finset.sum_congr rfl (fun t _ => by rw [ramQ_eq_halaszSum])
  rw [hcongr]
  exact h

/-! ## U-8d — the prime-window gain `Σ_{p ∈ block} 1/p ≍ 1/v`

MR p.29: "the extra logarithm the whole apparatus exists to save".  The block is the
`⌊H log p⌋ = j` fiber, i.e. the primes of `[e^{v}, e^{v+1/H})` at height `v = j/H`; sharp
Mertens-2 prices its reciprocal sum by `1/v` (the width gain `1/(Hv)` is swamped by
Mertens' own `12/log t` error, which is itself of the target size `1/v` — so `1/v`, not
`1/(Hv)`, is the honest grade). -/

/-- Every block prime is `≤ ⌊e^{(j+1)/H}⌋`, i.e. the block sits inside Mertens' window. -/
lemma ramQblock_subset_upper {H : ℝ} {P Q j : ℕ} :
    ramQblock H P Q j
      ⊆ (Finset.range (⌊Real.exp (((j : ℝ) + 1) / H)⌋₊ + 1)).filter Nat.Prime := by
  intro p hp
  obtain ⟨_, _, hpr, _, hup⟩ := mem_ramQblock hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hpr⟩
  have : p ≤ ⌊Real.exp (((j : ℝ) + 1) / H)⌋₊ := Nat.le_floor (le_of_lt hup)
  omega

/-- **U-8d — the prime-window gain.**  `Σ_{p ∈ block} 1/p ≤ 27·H/j = 27/v` at the block
height `v = j/H ≥ 1`. -/
theorem ramQblock_inv_sum_le {H : ℝ} (hH : 2 ≤ H) {P Q j : ℕ} (hj : H ≤ (j : ℝ)) :
    ∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p ≤ 27 * H / (j : ℝ) := by
  classical
  have hH0 : (0 : ℝ) < H := by linarith
  have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
  set v : ℝ := (j : ℝ) / H with hvdef
  have hv1 : 1 ≤ v := (one_le_div hH0).mpr hj
  set L₀ : ℝ := Real.exp v with hL₀def
  set U₀ : ℝ := Real.exp (((j : ℝ) + 1) / H) with hU₀def
  have hvU : v ≤ ((j : ℝ) + 1) / H := by
    rw [hvdef]; gcongr; linarith
  have hLU : L₀ ≤ U₀ := Real.exp_le_exp.mpr hvU
  have hL2 : 2 ≤ L₀ := by
    have h1 : Real.exp 1 ≤ L₀ := Real.exp_le_exp.mpr hv1
    have h2 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    linarith
  have hU2 : 2 ≤ U₀ := le_trans hL2 hLU
  have hL₀pos : (0 : ℝ) < L₀ := by linarith
  -- the two Mertens windows
  set A : Finset ℕ := (Finset.range (⌊U₀⌋₊ + 1)).filter Nat.Prime with hAdef
  set B : Finset ℕ := (Finset.range (⌊L₀⌋₊ + 1)).filter Nat.Prime with hBdef
  have hBA : B ⊆ A := by
    have hfl : ⌊L₀⌋₊ ≤ ⌊U₀⌋₊ := Nat.floor_mono hLU
    intro p hp
    rw [hBdef, Finset.mem_filter, Finset.mem_range] at hp
    rw [hAdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2⟩
  have hblockA : ramQblock H P Q j ⊆ A := ramQblock_subset_upper
  have hnn : ∀ p ∈ A, (0 : ℝ) ≤ 1 / p := fun p _ => by positivity
  -- split the block along `B`
  have hsplit : ∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p
      = ∑ p ∈ (ramQblock H P Q j).filter (fun p => p ∈ B), (1 : ℝ) / p
        + ∑ p ∈ (ramQblock H P Q j).filter (fun p => p ∉ B), (1 : ℝ) / p :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- the boundary prime: `block ∩ B ⊆ {⌊L₀⌋}`
  have hbnd : (ramQblock H P Q j).filter (fun p => p ∈ B) ⊆ {⌊L₀⌋₊} := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨_, _, _, hlow, _⟩ := mem_ramQblock hp.1
    have hpB := Finset.mem_filter.mp hp.2
    have hple : p ≤ ⌊L₀⌋₊ := by
      have := Finset.mem_range.mp hpB.1
      omega
    have hpge : ⌊L₀⌋₊ ≤ p := by
      have h1 : ((⌊L₀⌋₊ : ℕ) : ℝ) ≤ (p : ℝ) :=
        le_trans (Nat.floor_le (le_of_lt hL₀pos)) hlow
      exact_mod_cast h1
    have : p = ⌊L₀⌋₊ := le_antisymm hple hpge
    simp [this]
  have hbndsum : ∑ p ∈ (ramQblock H P Q j).filter (fun p => p ∈ B), (1 : ℝ) / p
      ≤ 1 / (⌊L₀⌋₊ : ℝ) := by
    have h : ∑ p ∈ (ramQblock H P Q j).filter (fun p => p ∈ B), (1 : ℝ) / p
        ≤ ∑ p ∈ ({⌊L₀⌋₊} : Finset ℕ), (1 : ℝ) / p :=
      Finset.sum_le_sum_of_subset_of_nonneg hbnd (fun p _ _ => by positivity)
    simpa using h
  -- the bulk: `block \ B ⊆ A \ B`
  have hbulk : ∑ p ∈ (ramQblock H P Q j).filter (fun p => p ∉ B), (1 : ℝ) / p
      ≤ Salt.Mertens.SPartial U₀ - Salt.Mertens.SPartial L₀ := by
    have hsub : (ramQblock H P Q j).filter (fun p => p ∉ B) ⊆ A \ B := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_sdiff.mpr ⟨hblockA hp.1, hp.2⟩
    have h1 : ∑ p ∈ (ramQblock H P Q j).filter (fun p => p ∉ B), (1 : ℝ) / p
        ≤ ∑ p ∈ A \ B, (1 : ℝ) / p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    have h2 : ∑ p ∈ A \ B, (1 : ℝ) / p = ∑ p ∈ A, (1 : ℝ) / p - ∑ p ∈ B, (1 : ℝ) / p :=
      Finset.sum_sdiff_eq_sub hBA
    rw [Salt.Mertens.SPartial, Salt.Mertens.SPartial, ← hAdef, ← hBdef, ← h2]
    exact h1
  -- Mertens-2 at the two endpoints
  have hmU := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hU2)
  have hmL := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hL2)
  have hlogU : Real.log U₀ = ((j : ℝ) + 1) / H := Real.log_exp _
  have hlogL : Real.log L₀ = v := Real.log_exp _
  have hvpos : (0 : ℝ) < v := by linarith
  -- the loglog difference is `log((j+1)/j) ≤ 1/j`
  have hlldiff : Real.log (Real.log U₀) - Real.log (Real.log L₀) ≤ 1 / (j : ℝ) := by
    rw [hlogU, hlogL, hvdef]
    have hq : Real.log (((j : ℝ) + 1) / H) - Real.log ((j : ℝ) / H)
        = Real.log (((j : ℝ) + 1) / (j : ℝ)) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      congr 1
      field_simp
    rw [hq]
    have := Real.log_le_sub_one_of_pos (x := ((j : ℝ) + 1) / (j : ℝ)) (by positivity)
    have hjne : (j : ℝ) ≠ 0 := ne_of_gt hjpos
    have hcalc : ((j : ℝ) + 1) / (j : ℝ) - 1 = 1 / (j : ℝ) := by
      have h1 : ((j : ℝ) + 1 - (j : ℝ)) / (j : ℝ)
          = ((j : ℝ) + 1) / (j : ℝ) - (j : ℝ) / (j : ℝ) := sub_div _ _ _
      rw [div_self hjne] at h1
      rw [← h1]
      norm_num
    linarith
  -- the two Mertens errors and the boundary term, all of size `H/j`
  have herrU : 12 / Real.log U₀ ≤ 12 * H / (j : ℝ) := by
    rw [hlogU, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hjpos]
    nlinarith
  have herrL : 12 / Real.log L₀ ≤ 12 * H / (j : ℝ) := by
    rw [hlogL, hvdef, div_div_eq_mul_div]
  have hfloor : 1 / (⌊L₀⌋₊ : ℝ) ≤ 2 * H / (j : ℝ) := by
    have hfl : L₀ - 1 < (⌊L₀⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one L₀
      linarith
    have hflpos : (0 : ℝ) < (⌊L₀⌋₊ : ℝ) := by linarith
    have hhalf : L₀ / 2 ≤ (⌊L₀⌋₊ : ℝ) := by linarith
    have hstep : 1 / (⌊L₀⌋₊ : ℝ) ≤ 2 / L₀ := by
      rw [div_le_div_iff₀ hflpos hL₀pos]; linarith
    have hexp : v ≤ Real.exp v := by
      have := Real.add_one_le_exp v; linarith
    have hinv : 2 / L₀ ≤ 2 / v := by
      rw [div_le_div_iff₀ hL₀pos hvpos, hL₀def]; nlinarith
    have hvform : 2 / v = 2 * H / (j : ℝ) := by rw [hvdef]; field_simp
    linarith
  have hHj : 1 / (j : ℝ) ≤ H / (j : ℝ) := by
    rw [div_le_div_iff₀ hjpos hjpos]; nlinarith
  rw [hsplit]
  have hfin : 12 * H / (j : ℝ) + 12 * H / (j : ℝ) + 2 * H / (j : ℝ) + H / (j : ℝ)
      = 27 * H / (j : ℝ) := by
    field_simp
    ring
  linarith

/-! ## U-8e — the kill arithmetic

The Vinogradov–Korobov decay of Lemma 11 against the Lemma-8 count.  At the pin
`W = log base ≈ L^{1−θ}`, `V = L^{100}`, `log T ≤ L`:

* the count contributes `exp(202·L^θ·log L)` (plus `840·V²·(log T)²`, all `L^{O(1)}`);
* the decay contributes `exp(−c·L^{1−θ}/(L^{3/4}(log L)⁴)) = exp(−c·L^{1/4−θ}/(log L)⁴)`.

The kill is `θ < 1/4 − θ`, i.e. `θ < 1/8`; at `θ = ρ/3 = 1/(96e) ≈ 0.0038` the exponent
ratio `(1/4 − θ)/θ ≈ 64` is the honest margin.  The `X₀` gate below is the explicit
in-statement form of "`L` large enough" (law #253) — it is exactly
`420·(log L)^5 ≤ c·L^{1/4−2θ}` at the pin. -/

/-- **U-8e (the kill).**  `840·V²·exp(2(L/W)(log V + log L)) · exp(−c·W/D) · (log T)² ≤ 1`,
where `D = (log T)^{3/4}(loglog T)⁴`, under the explicit `X₀` gate
`420·L·L^{3/4}·(log L)^5 ≤ c·W²`. -/
lemma tL_kill {L W V T cc : ℝ} (hcc : 0 < cc) (hL : Real.exp 1 ≤ L)
    (hW0 : 0 < W) (hWL : W ≤ L) (hV : 1 ≤ V)
    (hlogV : Real.log V ≤ 100 * Real.log L)
    (hT1 : 1 ≤ Real.log T) (hTL : Real.log T ≤ L) (hllT : 1 ≤ Real.log (Real.log T))
    (hgate : 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cc * W ^ 2) :
    840 * V ^ 2 * Real.exp (2 * (L / W) * (Real.log V + Real.log L))
        * Real.exp (-cc * W / ((Real.log T) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log T)) ^ (4 : ℕ)))
        * (Real.log T) ^ 2 ≤ 1 := by
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (Real.exp_pos 1) hL
  have hlogL1 : 1 ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at h
  have hV0 : (0 : ℝ) < V := by linarith
  have hlogT0 : (0 : ℝ) < Real.log T := by linarith
  have hllT0 : (0 : ℝ) ≤ Real.log (Real.log T) := by linarith
  have hLW1 : 1 ≤ L / W := (one_le_div hW0).mpr hWL
  -- `D ≤ L^{3/4}·(log L)^4`
  set D : ℝ := (Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ) with hDdef
  set D' : ℝ := L ^ ((3 : ℝ) / 4) * (Real.log L) ^ (4 : ℕ) with hD'def
  have hDpos : 0 < D := by
    rw [hDdef]
    exact mul_pos (Real.rpow_pos_of_pos hlogT0 _) (pow_pos (by linarith) 4)
  have hD'pos : 0 < D' := by
    rw [hD'def]
    exact mul_pos (Real.rpow_pos_of_pos hLpos _) (pow_pos (by linarith) 4)
  have hDD' : D ≤ D' := by
    rw [hDdef, hD'def]
    have h1 : (Real.log T) ^ ((3 : ℝ) / 4) ≤ L ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (le_of_lt hlogT0) hTL (by norm_num)
    have h2 : (Real.log (Real.log T)) ^ (4 : ℕ) ≤ (Real.log L) ^ (4 : ℕ) := by
      have hle : Real.log (Real.log T) ≤ Real.log L := Real.log_le_log hlogT0 hTL
      exact pow_le_pow_left₀ hllT0 hle 4
    have h3 : (0 : ℝ) ≤ (Real.log (Real.log T)) ^ (4 : ℕ) := by positivity
    nlinarith [Real.rpow_pos_of_pos hlogT0 ((3 : ℝ) / 4)]
  -- the gate turns into the decay lower bound
  have hKlb : 420 * (L / W) * Real.log L ≤ cc * W / D' := by
    rw [le_div_iff₀ hD'pos]
    have hXW : 420 * (L / W) * Real.log L * D' * W
        = 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 := by
      rw [hD'def]; field_simp
    have h2 : 420 * (L / W) * Real.log L * D' * W ≤ cc * W * W := by
      rw [hXW]; nlinarith
    exact le_of_mul_le_mul_right h2 hW0
  have hdecay : Real.exp (-cc * W / D) ≤ Real.exp (-(420 * (L / W) * Real.log L)) := by
    refine Real.exp_le_exp.mpr ?_
    have hmono : cc * W / D' ≤ cc * W / D := by
      apply div_le_div_of_nonneg_left (by positivity) hDpos hDD'
    have hneg : -cc * W / D = -(cc * W / D) := by ring
    rw [hneg]
    linarith
  -- the three polynomial factors
  have h840 : (840 : ℝ) ≤ Real.exp 7 := by
    have h1 : Real.exp (((7 : ℕ) : ℝ) * 1) = Real.exp 1 ^ (7 : ℕ) := Real.exp_nat_mul 1 7
    have h2 : Real.exp 7 = Real.exp 1 ^ (7 : ℕ) := by rw [← h1]; norm_num
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    rw [h2]
    calc (840 : ℝ) ≤ 2.7 ^ (7 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (7 : ℕ) := pow_le_pow_left₀ (by norm_num) he 7
  have hVsq : V ^ 2 ≤ Real.exp (200 * Real.log L) := by
    have h1 : Real.exp (2 * Real.log V) = V ^ 2 := by
      rw [show (2 : ℝ) * Real.log V = Real.log V + Real.log V from by ring, Real.exp_add,
        Real.exp_log hV0]
      ring
    rw [← h1]
    exact Real.exp_le_exp.mpr (by linarith)
  have hTsq : (Real.log T) ^ 2 ≤ Real.exp (2 * Real.log L) := by
    have h1 : Real.exp (2 * Real.log L) = L ^ 2 := by
      rw [show (2 : ℝ) * Real.log L = Real.log L + Real.log L from by ring, Real.exp_add,
        Real.exp_log hLpos]
      ring
    rw [h1]
    nlinarith
  -- the exponent comparison
  have hexpA : 2 * (L / W) * (Real.log V + Real.log L) ≤ 202 * (L / W) * Real.log L := by
    have hLW0 : (0 : ℝ) ≤ L / W := by linarith
    nlinarith
  have hsum : 7 + 200 * Real.log L + 2 * (L / W) * (Real.log V + Real.log L)
      + 2 * Real.log L - 420 * (L / W) * Real.log L ≤ 0 := by
    have h1 : (1 : ℝ) ≤ (L / W) * Real.log L := by nlinarith
    nlinarith
  calc 840 * V ^ 2 * Real.exp (2 * (L / W) * (Real.log V + Real.log L))
        * Real.exp (-cc * W / D) * (Real.log T) ^ 2
      ≤ Real.exp 7 * Real.exp (200 * Real.log L)
          * Real.exp (2 * (L / W) * (Real.log V + Real.log L))
          * Real.exp (-(420 * (L / W) * Real.log L)) * Real.exp (2 * Real.log L) := by
        gcongr
    _ = Real.exp (7 + 200 * Real.log L + 2 * (L / W) * (Real.log V + Real.log L)
          + -(420 * (L / W) * Real.log L) + 2 * Real.log L) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-- **U-8e (the `Q`-side, killed).**  Lemma 11 on `𝒯_L` with the Lemma-8 count fed into the
Vinogradov–Korobov decay: the `|𝒯_L|` term dies, leaving

`Σ_{t∈𝒯_L} ‖Q_{j,H}(1+it)‖² ≤ 2C·(Σ_{p∈block} 1/p)/log base`

— the `P/log P` shape of MR Lemma 11 with the prime-window gain already exposed.  Every
growing-quantity gate (`hκ30`, `hLL5`, the kill gate) is in-statement (law #253). -/
theorem tL_ramQ_sumsq_killed :
    ∃ C c T₀ : ℝ, 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧
      ∀ (H : ℝ), 2 ≤ H → ∀ (P Q j : ℕ) (cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (T V L δ' : ℝ) (𝒯 : Finset ℝ), WellSpaced 𝒯 →
      (∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) → T₀ ≤ T → 1 < T →
      3 ≤ ramQbase H P j → (ramQbase H P j : ℝ) ≤ T →
      30 ≤ Real.log T / Real.log (ramQbase H P j) →
      5 ≤ Real.log (Real.log T) → 1 ≤ V → V⁻¹ ≤ δ' →
      Real.log T ≤ L → 1 ≤ Real.log T → Real.exp 1 ≤ L →
      Real.log (ramQbase H P j) ≤ L → Real.log V ≤ 100 * Real.log L →
      420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ c * (Real.log (ramQbase H P j)) ^ 2 →
        ∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramQ H P Q j cf t‖ ^ 2
          ≤ 2 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
              / Real.log (ramQbase H P j) := by
  obtain ⟨C, c, T₀, hC, hc, hT₀, hmain⟩ := tL_sumsq_ramQ
  refine ⟨C, c, T₀, hC, hc, hT₀, ?_⟩
  intro H hH P Q j cf hcf1 T V L δ' 𝒯 hws hsub hT₀T hT hB3 hBT hκ30 hLL5 hV1 hVδ hTL
    hlogT1 hLe hWL hlogV hgate
  have hB0 : (0 : ℝ) < (ramQbase H P j : ℝ) := by
    have : (3 : ℝ) ≤ (ramQbase H P j : ℝ) := by exact_mod_cast hB3
    linarith
  have hB1 : (1 : ℝ) < (ramQbase H P j : ℝ) := by
    have : (3 : ℝ) ≤ (ramQbase H P j : ℝ) := by exact_mod_cast hB3
    linarith
  have hW0 : 0 < Real.log (ramQbase H P j) := Real.log_pos hB1
  have hws' : WellSpaced (tLset H P Q j cf δ' 𝒯) := tLset_wellSpaced hws
  have hsub' : ∀ t ∈ tLset H P Q j cf δ' 𝒯, t ∈ Set.Icc (-T) T :=
    fun t ht => hsub t (tLset_subset H P Q j cf δ' 𝒯 ht)
  have hlb : ∀ t ∈ tLset H P Q j cf δ' 𝒯, V⁻¹ ≤ ‖ramQ H P Q j cf t‖ :=
    fun t ht => le_of_lt (lt_of_le_of_lt hVδ (mem_tLset ht).2)
  have hcount := ramQ_large_count_Tfree hH P Q j cf hcf1 T V L hB3 hT hBT hV1 hκ30 hLL5
    hTL (tLset H P Q j cf δ' 𝒯) hws' hsub' hlb
  have hB2 : (2 : ℝ) ≤ (ramQbase H P j : ℝ) := by
    have : (3 : ℝ) ≤ (ramQbase H P j : ℝ) := by exact_mod_cast hB3
    linarith
  have hhal := hmain H hH P Q j cf T hT₀T hB2 (ramQbase_le_pow_ten hT hB3 hκ30)
    (tLset H P Q j cf δ' 𝒯) hws' hsub'
  -- the kill: the count times the decay times `(log T)²` is at most `1`
  have hkill := tL_kill hc hLe hW0 hWL hV1 hlogV hlogT1 hTL (by linarith) hgate
  set E : ℝ := Real.exp (-c * Real.log (ramQbase H P j)
      / ((Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ))) with hEdef
  have hE0 : (0 : ℝ) ≤ E := (Real.exp_pos _).le
  have hlogT2 : (0 : ℝ) ≤ (Real.log T) ^ 2 := sq_nonneg _
  have hcardE : ((tLset H P Q j cf δ' 𝒯).card : ℝ) * E * (Real.log T) ^ 2 ≤ 1 := by
    calc ((tLset H P Q j cf δ' 𝒯).card : ℝ) * E * (Real.log T) ^ 2
        ≤ (840 * V ^ 2 * Real.exp (2 * (L / Real.log (ramQbase H P j))
            * (Real.log V + Real.log L))) * E * (Real.log T) ^ 2 := by gcongr
      _ ≤ 1 := hkill
  -- the bracket collapses to `2·base`
  have hbracket : (ramQbase H P j : ℝ)
      + ((tLset H P Q j cf δ' 𝒯).card : ℝ) * (ramQbase H P j : ℝ) * E * (Real.log T) ^ 2
      ≤ 2 * (ramQbase H P j : ℝ) := by
    have hre : ((tLset H P Q j cf δ' 𝒯).card : ℝ) * (ramQbase H P j : ℝ) * E
          * (Real.log T) ^ 2
        = (ramQbase H P j : ℝ)
            * (((tLset H P Q j cf δ' 𝒯).card : ℝ) * E * (Real.log T) ^ 2) := by ring
    rw [hre]
    nlinarith
  -- the coefficient sum: `base · Σ‖c_p/p‖² ≤ Σ 1/p` (the prime-window gain's carrier)
  have hAnn : (0 : ℝ) ≤ ∑ p ∈ ramQblock H P Q j, ‖cf p / (p : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hA : (ramQbase H P j : ℝ) * (∑ p ∈ ramQblock H P Q j, ‖cf p / (p : ℂ)‖ ^ 2)
      ≤ ∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p := by
    have hterm : ∀ p ∈ ramQblock H P Q j,
        ‖cf p / (p : ℂ)‖ ^ 2 ≤ (1 / (ramQbase H P j : ℝ)) * (1 / (p : ℝ)) := by
      intro p hp
      have hpr := ramQblock_prime hp
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpr.pos
      have hBp : (ramQbase H P j : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast ramQbase_le_of_mem hp
      have hnorm : ‖cf p / (p : ℂ)‖ ≤ 1 / (p : ℝ) := by
        rw [norm_div, Complex.norm_natCast, inv_eq_one_div] at *
        gcongr
        exact hcf1 p
      have hnn : (0 : ℝ) ≤ ‖cf p / (p : ℂ)‖ := norm_nonneg _
      have hsq : ‖cf p / (p : ℂ)‖ ^ 2 ≤ (1 / (p : ℝ)) ^ 2 := by nlinarith
      have hfin : (1 / (p : ℝ)) ^ 2 ≤ (1 / (ramQbase H P j : ℝ)) * (1 / (p : ℝ)) := by
        have h1 : (1 / (p : ℝ)) ^ 2 = 1 / ((p : ℝ) * (p : ℝ)) := by ring
        have h2 : (1 / (ramQbase H P j : ℝ)) * (1 / (p : ℝ))
            = 1 / ((ramQbase H P j : ℝ) * (p : ℝ)) := by ring
        rw [h1, h2]
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
      linarith
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    calc (ramQbase H P j : ℝ) * (∑ p ∈ ramQblock H P Q j, ‖cf p / (p : ℂ)‖ ^ 2)
        ≤ (ramQbase H P j : ℝ)
            * ((1 / (ramQbase H P j : ℝ)) * ∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p) := by
          exact mul_le_mul_of_nonneg_left hsum (le_of_lt hB0)
      _ = ∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p := by
          field_simp
  -- assemble
  calc ∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramQ H P Q j cf t‖ ^ 2
      ≤ C * ((ramQbase H P j : ℝ) + ((tLset H P Q j cf δ' 𝒯).card : ℝ)
            * (ramQbase H P j : ℝ) * E * (Real.log T) ^ 2)
          / Real.log (ramQbase H P j)
          * ∑ p ∈ ramQblock H P Q j, ‖cf p / (p : ℂ)‖ ^ 2 := hhal
    _ ≤ C * (2 * (ramQbase H P j : ℝ)) / Real.log (ramQbase H P j)
          * ∑ p ∈ ramQblock H P Q j, ‖cf p / (p : ℂ)‖ ^ 2 := by
        gcongr
    _ = 2 * C * ((ramQbase H P j : ℝ)
          * ∑ p ∈ ramQblock H P Q j, ‖cf p / (p : ℂ)‖ ^ 2)
          / Real.log (ramQbase H P j) := by ring
    _ ≤ 2 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
          / Real.log (ramQbase H P j) := by
        gcongr

/-- **U-8 — THE EXIT.**  The `𝒯_L` branch of §8.3's `hU`, assembled: with the pointwise
co-factor bound `‖R_{j,H}(1+it)‖ ≤ Rbd` on `𝒯_L` (MR Lemma 3+5, the `U-7` supply — carried
as a hypothesis here, it is not a `𝒰`-property),

`Σ_{t∈𝒯_L} ‖Q_{j,H}·R_{j,H}‖² ≤ 54·C·Rbd²·(H/j)² = 54·C·Rbd²/v²`

at the block height `v = j/H`: the Lemma-11 mass `1/log base` and the prime-window gain
`Σ_{p∈block}1/p ≍ 1/v` each contribute one factor `1/v` — MR p.29's "extra logarithm". -/
theorem tL_main_sumsq :
    ∃ C c T₀ : ℝ, 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧
      ∀ (H : ℝ), 2 ≤ H → ∀ (P Q j N X : ℕ) (cf bb : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      H ≤ (j : ℝ) →
      ∀ (T V L δ' Rbd : ℝ) (𝒯 : Finset ℝ), WellSpaced 𝒯 →
      (∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) → T₀ ≤ T → 1 < T →
      3 ≤ ramQbase H P j → (ramQbase H P j : ℝ) ≤ T →
      30 ≤ Real.log T / Real.log (ramQbase H P j) →
      5 ≤ Real.log (Real.log T) → 1 ≤ V → V⁻¹ ≤ δ' →
      Real.log T ≤ L → 1 ≤ Real.log T → Real.exp 1 ≤ L →
      Real.log (ramQbase H P j) ≤ L → Real.log V ≤ 100 * Real.log L →
      420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ c * (Real.log (ramQbase H P j)) ^ 2 →
      0 ≤ Rbd → (∀ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramR H N X P Q j bb t‖ ≤ Rbd) →
        ∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N X P Q bb cf j t‖ ^ 2
          ≤ 54 * C * Rbd ^ 2 * (H / (j : ℝ)) ^ 2 := by
  obtain ⟨C, c, T₀, hC, hc, hT₀, hmain⟩ := tL_ramQ_sumsq_killed
  refine ⟨C, c, T₀, hC, hc, hT₀, ?_⟩
  intro H hH P Q j N X cf bb hcf1 hHj T V L δ' Rbd 𝒯 hws hsub hT₀T hT hB3 hBT hκ30 hLL5
    hV1 hVδ hTL hlogT1 hLe hWL hlogV hgate hRbd hR
  have hQ := hmain H hH P Q j cf hcf1 T V L δ' 𝒯 hws hsub hT₀T hT hB3 hBT hκ30 hLL5 hV1
    hVδ hTL hlogT1 hLe hWL hlogV hgate
  have hB1 : (1 : ℝ) < (ramQbase H P j : ℝ) := by
    have : (3 : ℝ) ≤ (ramQbase H P j : ℝ) := by exact_mod_cast hB3
    linarith
  have hW0 : 0 < Real.log (ramQbase H P j) := Real.log_pos hB1
  have hH0 : (0 : ℝ) < H := by linarith
  have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
  -- `log base ≥ v = j/H`
  have hWv : (j : ℝ) / H ≤ Real.log (ramQbase H P j) := by
    have h1 := Real.log_le_log (Real.exp_pos ((j : ℝ) / H)) (exp_le_ramQbase H P j)
    rwa [Real.log_exp] at h1
  have hvpos : (0 : ℝ) < (j : ℝ) / H := by positivity
  -- the pointwise `R` factor
  have hsplit : ∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N X P Q bb cf j t‖ ^ 2
      ≤ Rbd ^ 2 * ∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramQ H P Q j cf t‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun t ht => ?_)
    have hnorm : ‖ramMain H N X P Q bb cf j t‖ ^ 2
        = ‖ramQ H P Q j cf t‖ ^ 2 * ‖ramR H N X P Q j bb t‖ ^ 2 := by
      rw [ramMain, norm_mul, mul_pow]
    rw [hnorm]
    have h1 : ‖ramR H N X P Q j bb t‖ ^ 2 ≤ Rbd ^ 2 := by
      have := hR t ht
      nlinarith [norm_nonneg (ramR H N X P Q j bb t)]
    have h2 : (0 : ℝ) ≤ ‖ramQ H P Q j cf t‖ ^ 2 := sq_nonneg _
    nlinarith
  -- the prime-window gain and `1/log base ≤ H/j`
  have hgain := ramQblock_inv_sum_le (H := H) hH (P := P) (Q := Q) (j := j) hHj
  have hnn : (0 : ℝ) ≤ ∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p :=
    Finset.sum_nonneg (fun p _ => by positivity)
  have hinvW : 1 / Real.log (ramQbase H P j) ≤ H / (j : ℝ) := by
    have h1 : 1 / Real.log (ramQbase H P j) ≤ 1 / ((j : ℝ) / H) :=
      one_div_le_one_div_of_le hvpos hWv
    have h2 : 1 / ((j : ℝ) / H) = H / (j : ℝ) := by field_simp
    linarith
  have hstep : 2 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
        / Real.log (ramQbase H P j)
      ≤ 54 * C * (H / (j : ℝ)) ^ 2 := by
    have hform : 2 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
          / Real.log (ramQbase H P j)
        = 2 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
            * (1 / Real.log (ramQbase H P j)) := by ring
    rw [hform]
    have h1 : 2 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
          * (1 / Real.log (ramQbase H P j))
        ≤ 2 * C * (27 * H / (j : ℝ)) * (H / (j : ℝ)) := by
      have hCnn : (0 : ℝ) ≤ 2 * C := by linarith
      have hA : 2 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
          ≤ 2 * C * (27 * H / (j : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hgain hCnn
      have hB : (0 : ℝ) ≤ 2 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p) := by positivity
      have hinv0 : (0 : ℝ) ≤ 1 / Real.log (ramQbase H P j) := by positivity
      nlinarith
    have h2 : 2 * C * (27 * H / (j : ℝ)) * (H / (j : ℝ))
        = 54 * C * (H / (j : ℝ)) ^ 2 := by ring
    linarith
  calc ∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N X P Q bb cf j t‖ ^ 2
      ≤ Rbd ^ 2 * ∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramQ H P Q j cf t‖ ^ 2 := hsplit
    _ ≤ Rbd ^ 2 * (2 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
          / Real.log (ramQbase H P j)) := by
        exact mul_le_mul_of_nonneg_left hQ (by positivity)
    _ ≤ Rbd ^ 2 * (54 * C * (H / (j : ℝ)) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = 54 * C * Rbd ^ 2 * (H / (j : ℝ)) ^ 2 := by ring

end Salt.MR
