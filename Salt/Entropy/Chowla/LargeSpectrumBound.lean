/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# Lemma 3.5 assembly: the sieve-parametric large-spectrum bound (L35-ASM)

Tao 1509.05422 Lemma 3.5, footnote-4 additive-energy escape.  Compose the landed
L⁴/Parseval/Markov large-spectrum chain (`large_spectrum_energy`, W3-AE-c) with
the sieve-parametric additive-energy escape (`W3_AE_d_of_sieve`, W3-AE-d) into the
sieve-parametric `|Ξ_H| ≤ C(ε)` bound: the number of large-spectrum frequencies
is bounded by an `H`-independent constant `C(ε) = 16 · C_d · ε⁻¹⁶`.

Route:

1. `W3_AE_d_of_sieve` turns the two named sieve hypotheses (`hpt`, the r(n) upper
   sieve; `hsq`, the singular-series second moment) into
   `E[𝒫_H] ≤ C_d · H³ / log⁴H` for `H ≥ H₀`.
2. The regime hypothesis `heps2 : ε² < 1/2` discharges the Fourier-embedding
   obligations `hwin` (`p < H`) and `hwrap` (`p+q < H`) of the L⁴ chain: window
   membership gives `p ≤ ⌊ε²H⌋₊ ≤ ε²H`, so `p ≤ ε²H < H` and `p+q ≤ 2ε²H < H`.
3. `large_spectrum_energy` then reads `|Ξ_H|·(ε²/log H)⁴ ≤ H·(2/(ε²H))⁴·E[𝒫_H]`.
   Substituting the sieve bound the `log⁴H` cancel and the `H` powers collapse:
   `|Ξ_H|·ε⁸/log⁴H ≤ 16 C_d ε⁻⁸/log⁴H`, hence `|Ξ_H| ≤ 16 C_d ε⁻¹⁶`.

SEAM: the conclusion `((bigXi eps H).card : ℝ) ≤ C` is verbatim the `hXi`
hypothesis of `contradiction_of_mrtDoor` (MRTDoor.lean) at `eps := R.eps`,
`K := C`; the door composes by feeding `hbound H hH` (a `ChowlaRegime`'s
`heps1 : eps ≤ 1/2` supplies `heps2` via `eps² ≤ 1/4 < 1/2`).

ERRATUM (2026-08-23 helm, the council-demoted repair; item-18 version axis): "footnote 4"
matches NO arXiv version of 1509.05422 — v1 has exactly two footnotes; the additive-energy
escape is fn. 7 in v2 and fn. 9 in v3/v4 (v2's OWN fn. 4 is the model-case remark). The prose
above is kept verbatim; the OBJECT (the additive-energy escape) is the citation, not the number.
-/
import Salt.Entropy.Chowla.LargeSpectrum
import Salt.Entropy.Chowla.QuadrupleCount

namespace Salt.Entropy.Chowla

open scoped BigOperators Pointwise Combinatorics.Additive

/-- **L35-ASM** (the Lemma-3.5 assembly): the sieve-parametric large-spectrum
bound.  From the two named sieve hypotheses `hpt`/`hsq` (fed to `W3_AE_d_of_sieve`)
and the regime bound `heps2 : ε² < 1/2`, the large-spectrum count `|Ξ_H|` is
bounded by the `H`-independent constant `C(ε) = 16 · C_d · ε⁻¹⁶`.  This composes
the L⁴ chain `large_spectrum_energy` with the additive-energy escape; the
`log⁴H` factors cancel and the `H`-powers collapse. -/
theorem bigXi_bounded_of_sieve (eps : ℚ) (heps : 0 < eps) (heps2 : (eps : ℝ) ^ 2 < 1 / 2)
    (rbound : ℕ → ℕ → ℝ)
    (hpt : ∀ H n,
      (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ) ≤ rbound H n)
    (hsq : ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      ∑ n ∈ primeWindow eps H + primeWindow eps H, (rbound H n) ^ 2
        ≤ C * (H : ℝ) ^ 3 / (Real.log H) ^ 4) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((bigXi eps H).card : ℝ) ≤ C := by
  -- Step 1: the additive-energy escape.
  obtain ⟨Cd, hCd, H₀, hH₀, hE⟩ := W3_AE_d_of_sieve eps rbound hpt hsq
  have heQ : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have heps2Q : eps ^ 2 < 1 / 2 := by
    have h : ((eps ^ 2 : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by push_cast; linarith [heps2]
    exact_mod_cast h
  -- The pure algebra of the cancellation, in abstract variables (no `↑eps` folding).
  have algebra : ∀ X e L Hr E : ℝ, 0 < e → 0 < L → 0 < Hr → 0 ≤ X →
      X * (e ^ 2 / L) ^ 4 ≤ Hr * (2 / (e ^ 2 * Hr)) ^ 4 * E →
      E ≤ Cd * Hr ^ 3 / L ^ 4 →
      X ≤ 16 * Cd / e ^ 16 := by
    intro X e L Hr E he hL hHr hX h1 h2
    have hne : e ≠ 0 := ne_of_gt he
    have hLne : L ≠ 0 := ne_of_gt hL
    have hHrne : Hr ≠ 0 := ne_of_gt hHr
    have hcoef : (0 : ℝ) ≤ Hr * (2 / (e ^ 2 * Hr)) ^ 4 := by positivity
    have h3 : X * (e ^ 2 / L) ^ 4 ≤ Hr * (2 / (e ^ 2 * Hr)) ^ 4 * (Cd * Hr ^ 3 / L ^ 4) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 hcoef)
    have hmul : (0 : ℝ) < L ^ 4 * e ^ 8 := by positivity
    have h4 := mul_le_mul_of_nonneg_right h3 (le_of_lt hmul)
    have hL4 : X * (e ^ 2 / L) ^ 4 * (L ^ 4 * e ^ 8) = X * e ^ 16 := by field_simp
    have hR4 : Hr * (2 / (e ^ 2 * Hr)) ^ 4 * (Cd * Hr ^ 3 / L ^ 4) * (L ^ 4 * e ^ 8)
        = 16 * Cd := by field_simp; norm_num
    rw [hL4, hR4] at h4
    rw [le_div_iff₀ (show (0 : ℝ) < e ^ 16 by positivity)]
    exact h4
  refine ⟨16 * Cd / (eps : ℝ) ^ 16,
    div_pos (mul_pos (by norm_num) hCd) (pow_pos heQ 16), H₀, hH₀, ?_⟩
  intro H hNe hH
  haveI := hNe
  have hH2 : 2 ≤ H := le_trans hH₀ hH
  have hHpos : 0 < H := by omega
  have hHQ : (0 : ℚ) < (H : ℚ) := by exact_mod_cast hHpos
  have hHR1 : (1 : ℝ) < (H : ℝ) := by exact_mod_cast (show 1 < H by omega)
  -- Discharge the Fourier-embedding obligations from `ε² < 1/2`.
  have hxnn : (0 : ℚ) ≤ eps ^ 2 * (H : ℚ) := by positivity
  have hfloor : (⌊eps ^ 2 * (H : ℚ)⌋₊ : ℚ) ≤ eps ^ 2 * (H : ℚ) := Nat.floor_le hxnn
  have hwin : ∀ p ∈ primeWindow eps H, p < H := by
    intro p hp
    rw [mem_primeWindow] at hp
    have hpq : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) := le_trans (by exact_mod_cast hp.1) hfloor
    have : (p : ℚ) < (H : ℚ) := by nlinarith [hpq, heps2Q, hHQ]
    exact_mod_cast this
  have hwrap : ∀ p ∈ primeWindow eps H, ∀ q ∈ primeWindow eps H, p + q < H := by
    intro p hp q hq
    rw [mem_primeWindow] at hp hq
    have hpp : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) := le_trans (by exact_mod_cast hp.1) hfloor
    have hqq : (q : ℚ) ≤ eps ^ 2 * (H : ℚ) := le_trans (by exact_mod_cast hq.1) hfloor
    have : ((p + q : ℕ) : ℚ) < (H : ℚ) := by push_cast; nlinarith [hpp, hqq, heps2Q, hHQ]
    exact_mod_cast this
  -- Step 3: feed the L⁴ chain and the escape into the algebra.
  exact algebra ((bigXi eps H).card : ℝ) (eps : ℝ) (Real.log (H : ℝ)) (H : ℝ)
    (Finset.addEnergy (primeWindow eps H) (primeWindow eps H) : ℝ)
    heQ (Real.log_pos hHR1) (by exact_mod_cast hHpos) (Nat.cast_nonneg _)
    (large_spectrum_energy eps H heps hwin hwrap) (hE H hH)

end Salt.Entropy.Chowla
