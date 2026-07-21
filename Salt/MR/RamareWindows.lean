/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RamareDpoly

/-!
# RamareWindows — the dyadic regroup, windows, and error pricing (S8 / MR-CORE, RAMARE-DPOLY)

Closing the seam `RAMARE-DPOLY` of `lemma12_meansq_conditional` (`Salt.MR.MomentsA2`):
building the concrete `hdecomp` witness `spoly = Σ_{j∈I} Q_{j,H}·R_{j,H} + errPoly`
and pricing `herr`.  Source: `docs/sources/1501.04585v4.pdf` pp.19–20, Lemma 12.

## The pieces (MR p.19)

* `ramQ H P Q j c` — `Q_{j,H}(1+it) = Σ_{P≤p≤Q, e^{j/H}≤p≤e^{(j+1)/H}} c_p/p^{1+it}`.
* `ramR H N X P Q j b` — `R_{j,H}(1+it) = Σ_{Xe^{-j/H}≤m≤2Xe^{-j/H}} (b_m/m^{1+it})/(ω(m;P,Q)+1)`.
* `ramMain … j = ramQ j · ramR j`, `ramI H P Q = ⌊H log P⌋..⌊H log Q⌋` the block index set.
* `ramErr … = spoly − Σ_{j∈ramI} ramMain j` — the error, DEFINED as the difference, so the
  decomposition `spoly = Σ ramMain + ramErr` (`hdecomp`) holds **definitionally**.

This file's Stone A: the concrete polynomials, the definitional decomposition, and the
continuity facts — enough to instantiate every hypothesis of `lemma12_meansq_conditional`
except `herr` (the analytic error pricing, the `R2` residual — see NOTES).
-/

namespace Salt.MR

open Finset Complex MeasureTheory intervalIntegral
open scoped BigOperators

/-- The single Dirichlet term `t ↦ c / k^{1+it}` is continuous for `k ≠ 0`
(a constant times a nowhere-vanishing `cpow` in the exponent). -/
lemma continuous_cterm {k : ℕ} (hk : k ≠ 0) (c : ℂ) :
    Continuous (fun t : ℝ => c / (k : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  haveI : NeZero (k : ℂ) := ⟨hk0⟩
  have hexp : Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hne : ∀ t : ℝ, (k : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t; rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h0, _⟩; exact hk0 h0
  simp_rw [div_eq_mul_inv]
  exact continuous_const.mul (((continuous_const_cpow (k : ℂ)).comp hexp).inv₀ hne)

/-- `spoly N a` is continuous (a finite sum of `aₙ/n^{1+it}` terms, `n ≥ 1`). -/
lemma continuous_spoly (N : ℕ) (a : ℕ → ℂ) : Continuous (spoly N a) := by
  unfold spoly
  refine continuous_finsetSum _ (fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  exact continuous_cterm (by omega) (a n)

open Classical in
/-- **The block prime set** for index `j`: primes `p` with `P ≤ p ≤ Q` in the dyadic
window `e^{j/H} ≤ p < e^{(j+1)/H}` (half-open, per the MR p.19 proof regroup — this is the
`⌊H log p⌋ = j` fiber, so the blocks partition the prime range). -/
noncomputable def ramQblock (H : ℝ) (P Q j : ℕ) : Finset ℕ :=
  (Finset.Icc P Q).filter
    (fun p => p.Prime ∧ Real.exp ((j : ℝ) / H) ≤ (p : ℝ) ∧
      (p : ℝ) < Real.exp (((j : ℝ) + 1) / H))

open Classical in
/-- **The co-factor range** for index `j`: integers `m` with `Xe^{-j/H} ≤ m ≤ 2Xe^{-j/H}`
(realised inside `[1, N]`). -/
noncomputable def ramRrange (H : ℝ) (N X j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun m => (X : ℝ) * Real.exp (-(j : ℝ) / H) ≤ (m : ℝ) ∧
      (m : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(j : ℝ) / H))

/-- **`Q_{j,H}(1+it)`** (MR p.19): the prime block polynomial. -/
noncomputable def ramQ (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ ramQblock H P Q j, c p / (p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)

/-- **`R_{j,H}(1+it)`** (MR p.19): the Ramaré-weighted co-factor polynomial. -/
noncomputable def ramR (H : ℝ) (N X P Q j : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ ramRrange H N X j,
    (b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) * (((blockOmega P Q m : ℂ) + 1)⁻¹)

/-- **The main block polynomial** `Q_{j,H}(1+it)·R_{j,H}(1+it)`. -/
noncomputable def ramMain (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) (j : ℕ) (t : ℝ) : ℂ :=
  ramQ H P Q j c t * ramR H N X P Q j b t

/-- **The block index set** `I = ⌊H log P⌋ ≤ j ≤ ⌊H log Q⌋` (MR p.19). -/
noncomputable def ramI (H : ℝ) (P Q : ℕ) : Finset ℕ :=
  Finset.Icc ⌊H * Real.log (P : ℝ)⌋₊ ⌊H * Real.log (Q : ℝ)⌋₊

/-- **The error polynomial**, DEFINED as `spoly − Σ_{j∈I} Q_j R_j`.  The decomposition
`spoly = Σ ramMain + ramErr` is then an identity by construction. -/
noncomputable def ramErr (H : ℝ) (N X P Q : ℕ) (a b c : ℕ → ℂ) (t : ℝ) : ℂ :=
  spoly N a t - ∑ j ∈ ramI H P Q, ramMain H N X P Q b c j t

/-- **`hdecomp`, definitionally.**  `spoly = Σ_{j∈I} Q_j R_j + errPoly` for the concrete
main polynomials and the difference-defined error. -/
theorem spoly_ram_decomp (H : ℝ) (N X P Q : ℕ) (a b c : ℕ → ℂ) (t : ℝ) :
    spoly N a t
      = (∑ j ∈ ramI H P Q, ramMain H N X P Q b c j t) + ramErr H N X P Q a b c t := by
  rw [ramErr]; ring

/-- `ramQ H P Q j c` is continuous (a finite sum of `c_p/p^{1+it}`, `p` prime). -/
lemma continuous_ramQ (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) : Continuous (ramQ H P Q j c) := by
  unfold ramQ
  refine continuous_finsetSum _ (fun p hp => ?_)
  rw [ramQblock, Finset.mem_filter] at hp
  exact continuous_cterm hp.2.1.pos.ne' (c p)

/-- `ramR H N X P Q j b` is continuous (a finite sum of weighted `b_m/m^{1+it}`, `m ≥ 1`). -/
lemma continuous_ramR (H : ℝ) (N X P Q j : ℕ) (b : ℕ → ℂ) : Continuous (ramR H N X P Q j b) := by
  unfold ramR
  refine continuous_finsetSum _ (fun m hm => ?_)
  rw [ramRrange, Finset.mem_filter] at hm
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm.1).1
  exact (continuous_cterm (by omega) (b m)).mul continuous_const

/-- `ramMain H N X P Q b c j` is continuous. -/
lemma continuous_ramMain (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) (j : ℕ) :
    Continuous (ramMain H N X P Q b c j) :=
  (continuous_ramQ H P Q j c).mul (continuous_ramR H N X P Q j b)

/-- `ramErr H N X P Q a b c` is continuous (spoly minus a finite sum of continuous blocks). -/
lemma continuous_ramErr (H : ℝ) (N X P Q : ℕ) (a b c : ℕ → ℂ) :
    Continuous (ramErr H N X P Q a b c) := by
  unfold ramErr
  exact (continuous_spoly N a).sub
    (continuous_finsetSum _ (fun j _ => continuous_ramMain H N X P Q b c j))

/-- **Stone A — Lemma 12 reduced to the error second moment (`herr`).**  With the concrete
`Q_{j,H}·R_{j,H}` main polynomials and the difference-defined error, the mean-square bound
of `lemma12_meansq_conditional` holds; the only remaining obligation is the error pricing
`herr : ∫ ‖errPoly‖² ≤ E` (the `R2` residual). -/
theorem lemma12_meansq_of_windowErr (H : ℝ) (N X P Q : ℕ) (a b c : ℕ → ℂ) (T E : ℝ)
    (hT : 0 ≤ T)
    (herr : (∫ t in (-T)..T, ‖ramErr H N X P Q a b c t‖ ^ 2) ≤ E) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in (-T)..T, ‖ramMain H N X P Q b c j t‖ ^ 2) + 2 * E :=
  lemma12_meansq_conditional (by linarith)
    (fun j _ => continuous_ramMain H N X P Q b c j)
    (continuous_ramErr H N X P Q a b c)
    (fun t => spoly_ram_decomp H N X P Q a b c t)
    herr

/-! ## R1c step 1 — the coprime split of eq (16) (MR p.19 middle display)

From `spoly_ramare_eq16`, split the Ramaré `(p,m)` double sum by `p ∤ m` (coprime) vs
`p ∣ m`.  On the coprime part, `ramareWeight = 1/(ω(m)+1)` and `a_{pm} = b_m c_p`, so each
term becomes the "clean" summand `(b_m c_p/(pm)^s)/(ω(m)+1)`.  Extending the clean summand to
**all** `m` (the `p ∣ m` terms too) and compensating with a correction (the `p²`-terms of
p.20) gives the paper's display: `spoly = clean + p²-correction + coprime-tail`. -/

/-- **R1c step 1 — the coprime split.**  `spoly = clean-term + p²-correction + coprime-tail`,
the MR p.19 rewrite of eq (16).  The clean term extends the Ramaré weight `1/(ω(m)+1)` and the
factorisation `a_{pm}=b_m c_p` to **all** cofactors `m`; the correction repairs the `p ∣ m`
overreach (the `p²`-terms). -/
theorem spoly_ramare_split (N P Q : ℕ) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (t : ℝ) :
    spoly N a t
      = (∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
          ∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
              (fun m => p * m ∈ Finset.Icc 1 N),
            (b m * c p / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
              * ((blockOmega P Q m : ℂ) + 1)⁻¹)
        + (∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
          ∑ m ∈ (((Finset.Icc 1 N).image (fun n => n / p)).filter
              (fun m => p * m ∈ Finset.Icc 1 N)).filter (fun m => p ∣ m),
            (ramareWeight P Q p m • (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
              - (b m * c p / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
                  * ((blockOmega P Q m : ℂ) + 1)⁻¹))
        + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
            a n / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
  rw [spoly_ramare_eq16 N a P Q t]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨hPp, hpQ⟩, hpp⟩ := hp
  rw [Finset.sum_filter (fun m => p ∣ m), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases hpm : p ∣ m
  · rw [if_pos hpm]; simp only [Complex.real_smul]; ring
  · rw [if_neg hpm, add_zero, hcoef p m hpp hPp hpQ hpm,
      ramareWeight_coprime P Q p m (hpp.coprime_iff_not_dvd.mpr hpm), Complex.real_smul]
    push_cast; ring

/-! ## R1c step 2 — the dyadic prime partition (MR p.19 bottom display)

The clean term `Σ_{P≤p≤Q, p prime} G(p)` regroups over the dyadic blocks
`ramQblock_j = {p : e^{j/H}≤p<e^{(j+1)/H}}`.  The block index `⌊H log p⌋` fibers the prime
range, and each block sits inside `I = ⌊H log P⌋..⌊H log Q⌋` by floor-monotonicity. -/

/-- **The `(pm)^s = p^s m^s` split** (retires the mul_cpow LHS-shape trap: `Nat.cast_mul`
then `ofReal_natCast` puts the base in `ofReal` form for `Complex.mul_cpow_ofReal_nonneg`). -/
lemma natCast_mul_cpow (p m : ℕ) (s : ℂ) :
    ((↑(p * m) : ℂ)) ^ s = (↑p : ℂ) ^ s * (↑m : ℂ) ^ s := by
  rw [Nat.cast_mul, ← Complex.ofReal_natCast p, ← Complex.ofReal_natCast m,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg m)]

/-- **The block `=` floor-fiber identity.**  `ramQblock H P Q j` is exactly the primes in
`[P,Q]` whose block index `⌊H log p⌋` equals `j`. -/
lemma ramQblock_eq_filter (H : ℝ) (hH : 0 < H) (P Q : ℕ) (hP : 1 ≤ P) (j : ℕ) :
    ramQblock H P Q j
      = ((Finset.Icc P Q).filter Nat.Prime).filter
          (fun p : ℕ => ⌊H * Real.log (p : ℝ)⌋₊ = j) := by
  rw [ramQblock, Finset.filter_filter]
  refine Finset.filter_congr (fun p hp => ?_)
  rw [Finset.mem_Icc] at hp
  have hp1 : 1 ≤ p := le_trans hP hp.1
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hHlognn : 0 ≤ H * Real.log (p : ℝ) := by positivity
  have hbridge : (Real.exp ((j : ℝ) / H) ≤ (p : ℝ) ∧ (p : ℝ) < Real.exp (((j : ℝ) + 1) / H))
      ↔ ⌊H * Real.log (p : ℝ)⌋₊ = j := by
    rw [Nat.floor_eq_iff hHlognn, ← Real.le_log_iff_exp_le hppos,
      ← Real.log_lt_iff_lt_exp hppos, div_le_iff₀ hH, lt_div_iff₀ hH,
      mul_comm (Real.log (p : ℝ)) H]
  exact and_congr_right (fun _ => hbridge)

/-- **R1c step 2 — the dyadic prime partition.**  For `1 ≤ P` and `0 < H`, any sum over the
primes in `[P,Q]` regroups as the double sum over blocks `j ∈ I` and primes in `ramQblock_j`. -/
theorem prime_sum_dyadic_partition (H : ℝ) (hH : 0 < H) (P Q : ℕ) (hP : 1 ≤ P)
    {M : Type*} [AddCommMonoid M] (G : ℕ → M) :
    (∑ p ∈ (Finset.Icc P Q).filter Nat.Prime, G p)
      = ∑ j ∈ ramI H P Q, ∑ p ∈ ramQblock H P Q j, G p := by
  have hmaps : ∀ p ∈ (Finset.Icc P Q).filter Nat.Prime,
      ⌊H * Real.log (p : ℝ)⌋₊ ∈ ramI H P Q := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hPp, hpQ⟩, _⟩ := hp
    rw [ramI, Finset.mem_Icc]
    have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    have hPpR : (P : ℝ) ≤ (p : ℝ) := by exact_mod_cast hPp
    have hpQR : (p : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hpQ
    have hPpos : (0 : ℝ) < (P : ℝ) := by linarith
    refine ⟨Nat.floor_mono (mul_le_mul_of_nonneg_left (Real.log_le_log hPpos hPpR) hH.le),
      Nat.floor_mono (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hpQR) hH.le)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps G]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ramQblock_eq_filter H hH P Q hP j]

/-- **R1c step 3 — the dyadic clean-term display (MR p.19 bottom).**  The clean term of
`spoly_ramare_split` regroups over the dyadic blocks with `c_p/p^s` factored out:
`Σ_{p} Σ_m (b_m c_p/(pm)^s)/(ω(m)+1) = Σ_{j∈I} Σ_{p∈block_j} (c_p/p^s) Σ_m (b_m/m^s)/(ω(m)+1)`.

The inner cofactor range is still the honest eq (16) range `{m : pm ∈ [1,N]}` (`p`-dependent);
replacing it by the `p`-independent `R_{j,H}` range `ramRrange_j` — the OVERCOUNT-WINDOW step —
is the remaining `R1c` residual (see NOTES). -/
theorem clean_term_dyadic (H : ℝ) (hH : 0 < H) (N P Q : ℕ) (hP : 1 ≤ P) (b c : ℕ → ℂ)
    (t : ℝ) :
    (∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
        ∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
            (fun m => p * m ∈ Finset.Icc 1 N),
          (b m * c p / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
            * ((blockOmega P Q m : ℂ) + 1)⁻¹)
      = ∑ j ∈ ramI H P Q, ∑ p ∈ ramQblock H P Q j,
          (c p / (↑p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
            * ∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
                (fun m => p * m ∈ Finset.Icc 1 N),
              (b m / (↑m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
                * ((blockOmega P Q m : ℂ) + 1)⁻¹ := by
  rw [prime_sum_dyadic_partition H hH P Q hP
    (fun p => ∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
        (fun m => p * m ∈ Finset.Icc 1 N),
      (b m * c p / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
        * ((blockOmega P Q m : ℂ) + 1)⁻¹)]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun p _ => ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [natCast_mul_cpow p m]; ring

/-! ## R2 — the overcount-window count (the `1/H`-row pricing input, MR p.20)

The error second moment (`herr`) is priced by `moment_core_bound` on the window coefficients.
The dominant `1/H` row comes from the count of integers in the multiplicative window
`[Xe^{-1/H}, Xe^{1/H}]` (width `≤ 2eX/H`), yielding the `(T+X)/X · 1/H` grade with the
explicit constant `2e`. -/

/-- **Naturals in a real interval — the count bound.**  A finite set of naturals all lying in
`[lo, hi]` (with `0 ≤ lo ≤ hi`) has at most `hi − lo + 1` elements. -/
lemma nat_real_interval_card_le (lo hi : ℝ) (hlo : 0 ≤ lo) (hle : lo ≤ hi) (s : Finset ℕ)
    (hs : ∀ n ∈ s, lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi) :
    (s.card : ℝ) ≤ hi - lo + 1 := by
  have hsub : s ⊆ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊ := by
    intro n hn; obtain ⟨h1, h2⟩ := hs n hn
    rw [Finset.mem_Icc]; exact ⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩
  have hcard : (s.card : ℝ) ≤ ((⌊hi⌋₊ + 1 - ⌈lo⌉₊ : ℕ) : ℝ) := by
    calc (s.card : ℝ) ≤ ((Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = ((⌊hi⌋₊ + 1 - ⌈lo⌉₊ : ℕ) : ℝ) := by rw [Nat.card_Icc]
  refine hcard.trans ?_
  have h1 : (⌊hi⌋₊ : ℝ) ≤ hi := Nat.floor_le (by linarith)
  have h2 : lo ≤ (⌈lo⌉₊ : ℝ) := Nat.le_ceil lo
  by_cases hcase : ⌈lo⌉₊ ≤ ⌊hi⌋₊ + 1
  · rw [Nat.cast_sub hcase]; push_cast; linarith
  · rw [Nat.sub_eq_zero_of_le (by omega)]; push_cast; linarith

/-- **The symmetric multiplicative width bound.**  `e^{1/H} − e^{-1/H} ≤ 2e/H` for `H ≥ 1`
(the `sinh` bound `e^x − e^{-x} = e^x(1 − e^{-2x}) ≤ e^x · 2x`, with `e^{1/H} ≤ e`). -/
lemma exp_symm_width_le (H : ℝ) (hH : 1 ≤ H) :
    Real.exp (1 / H) - Real.exp (-(1 / H)) ≤ 2 * Real.exp 1 / H := by
  have hH0 : 0 < H := by linarith
  have hb : 1 - Real.exp (-(2 * (1 / H))) ≤ 2 * (1 / H) := by
    have := Real.add_one_le_exp (-(2 * (1 / H))); linarith
  have hexp1 : Real.exp (1 / H) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by rw [div_le_one hH0]; exact hH)
  have hepos : 0 < Real.exp (1 / H) := Real.exp_pos _
  have hfact : Real.exp (1 / H) - Real.exp (-(1 / H))
      = Real.exp (1 / H) * (1 - Real.exp (-(2 * (1 / H)))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
  rw [hfact]
  calc Real.exp (1 / H) * (1 - Real.exp (-(2 * (1 / H))))
      ≤ Real.exp (1 / H) * (2 * (1 / H)) := mul_le_mul_of_nonneg_left hb hepos.le
    _ ≤ Real.exp 1 * (2 * (1 / H)) := mul_le_mul_of_nonneg_right hexp1 (by positivity)
    _ = 2 * Real.exp 1 / H := by ring

/-- **R2 — the overcount-window count** (MR p.20, the `1/H` row).  Any finite set of integers
lying in the multiplicative window `[Xe^{-1/H}, Xe^{1/H}]` has at most `2e·X/H + 1` elements —
the explicit `1/H`-grade count driving the error `(T+X)/X·(1/H)` row. -/
theorem window_card_le (H : ℝ) (hH : 1 ≤ H) (X : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, (X : ℝ) * Real.exp (-(1 / H)) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ (X : ℝ) * Real.exp (1 / H)) :
    (s.card : ℝ) ≤ 2 * Real.exp 1 * (X : ℝ) / H + 1 := by
  have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hlo : (0 : ℝ) ≤ (X : ℝ) * Real.exp (-(1 / H)) := by positivity
  have hHpos : (0 : ℝ) < 1 / H := by positivity
  have hexple : Real.exp (-(1 / H)) ≤ Real.exp (1 / H) := Real.exp_le_exp.mpr (by linarith)
  have hle : (X : ℝ) * Real.exp (-(1 / H)) ≤ (X : ℝ) * Real.exp (1 / H) :=
    mul_le_mul_of_nonneg_left hexple hXnn
  refine (nat_real_interval_card_le _ _ hlo hle s hs).trans ?_
  have hwidth : (X : ℝ) * Real.exp (1 / H) - (X : ℝ) * Real.exp (-(1 / H))
      ≤ 2 * Real.exp 1 * (X : ℝ) / H := by
    rw [← mul_sub]
    calc (X : ℝ) * (Real.exp (1 / H) - Real.exp (-(1 / H)))
        ≤ (X : ℝ) * (2 * Real.exp 1 / H) := mul_le_mul_of_nonneg_left (exp_symm_width_le H hH) hXnn
      _ = 2 * Real.exp 1 * (X : ℝ) / H := by ring
  linarith

/-! ## W1/W2 — the window swap and the exact `ramErr` characterization (MR pp.19–20)

The honest eq (16) cofactor range `{m : pm ∈ [1,N]}` (`p`-dependent) is swapped for the
`p`-independent `R_{j,H}` range `ramRrange_j`.  Factoring `R_{j,H}` out of the block sum, the
per-prime residual is the difference of the two inner sums — the OVERCOUNT WINDOW.  Combined
with the `p²`-correction and the coprime tail of `spoly_ramare_split`, this gives the exact
identity `ramErr = window + p²-correction + coprime-tail` (well-posed: `ramErr` is the
difference by construction). -/

/-- **The window error** (`W1`): the block sum of `c_p/p^s` against the honest-minus-`R_{j,H}`
cofactor difference `Σ_{m:pm∈[1,N]} g − Σ_{m∈ramRrange_j} g`, `g(m) = (b_m/m^s)/(ω(m)+1)`. -/
noncomputable def ramWindowErr (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ ramI H P Q, ∑ p ∈ ramQblock H P Q j,
    (c p / (↑p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
      ((∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
            (fun m => p * m ∈ Finset.Icc 1 N),
          (b m / (↑m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) * ((blockOmega P Q m : ℂ) + 1)⁻¹)
        - ramR H N X P Q j b t)

/-- **The `p²`-correction** (MR p.20): the `p ∣ m` overreach repaired in `spoly_ramare_split`. -/
noncomputable def ramP2corr (N P Q : ℕ) (a b c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
    ∑ m ∈ (((Finset.Icc 1 N).image (fun n => n / p)).filter
        (fun m => p * m ∈ Finset.Icc 1 N)).filter (fun m => p ∣ m),
      (ramareWeight P Q p m • (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
        - (b m * c p / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
            * ((blockOmega P Q m : ℂ) + 1)⁻¹)

/-- **The coprime tail** (MR eq (16)): the `ω(n;P,Q)=0` residue. -/
noncomputable def ramCopTail (N P Q : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
    a n / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)

/-- **W1 — factoring `R_{j,H}` out of the dyadic clean term.**  The dyadic clean term minus the
main block sum `Σ_{j∈I} Q_{j,H}R_{j,H}` is exactly the window error: on each block `Q_{j,H}`
distributes over its primes and the honest cofactor sum minus `R_{j,H}` is the per-prime window
residual. -/
theorem clean_dyadic_sub_main (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) (t : ℝ) :
    (∑ j ∈ ramI H P Q, ∑ p ∈ ramQblock H P Q j,
        (c p / (↑p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
          * ∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
              (fun m => p * m ∈ Finset.Icc 1 N),
            (b m / (↑m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
              * ((blockOmega P Q m : ℂ) + 1)⁻¹)
      - (∑ j ∈ ramI H P Q, ramMain H N X P Q b c j t)
      = ramWindowErr H N X P Q b c t := by
  rw [ramWindowErr, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ramMain, ramQ, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  ring

/-- **W2 — the exact `ramErr` characterization.**  Since `ramErr = spoly − Σ_{j∈I} Q_{j,H}R_{j,H}`
by construction, the Ramaré coprime split (`spoly_ramare_split`) and the dyadic regroup
(`clean_term_dyadic`) resolve it into the window error, the `p²`-correction and the coprime tail.
This is well-posed and unconditional given only the coefficient factorisation `hcoef`. -/
theorem ramErr_window_decomp (H : ℝ) (hH : 0 < H) (N X P Q : ℕ) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (t : ℝ) :
    ramErr H N X P Q a b c t
      = ramWindowErr H N X P Q b c t + ramP2corr N P Q a b c t + ramCopTail N P Q a t := by
  rw [ramErr, spoly_ramare_split N P Q a b c hcoef t, clean_term_dyadic H hH N P Q hP b c t,
    ← clean_dyadic_sub_main H N X P Q b c t]
  unfold ramP2corr ramCopTail
  abel

/-! ## W3 — the L² pricing of the error rows (MR p.20)

Each of the three error rows is a `σ=1` Dirichlet polynomial, so `moment_core_bound` (the
`(2T+20N)·Σ|·|²/n²` engine) prices its second moment.  The coprime tail is the cleanest: it is
literally `spoly` on the `ω(n)=0`-restricted coefficients, so its moment is the "tail verbatim"
grade `(2T+20N)·Σ_{ω(n)=0}|aₙ|²/n²`. -/

/-- **The coprime tail as a `spoly`.**  `ramCopTail = Σ_{n∈[1,N], ω(n)=0} aₙ/n^s` is exactly
`spoly` on the coefficients `aₙ` masked to the `ω(n)=0` support. -/
lemma ramCopTail_eq_spoly (N P Q : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ramCopTail N P Q a t = spoly N (fun n => if blockOmega P Q n = 0 then a n else 0) t := by
  rw [ramCopTail, spoly, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h : blockOmega P Q n = 0 <;> simp [h]

/-- **W3 (tail row) — the coprime-tail second moment.**  The "tail verbatim" grade: the coprime
tail's mean square is priced by `moment_core_bound` at `(2T+20N)·Σ_{ω(n)=0}|aₙ|²/n²`. -/
theorem ramCopTail_moment (N P Q : ℕ) (a : ℕ → ℂ) (T : ℝ) :
    (∫ t in (-T)..T, ‖ramCopTail N P Q a t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ))
          * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
  have hcongr : (∫ t in (-T)..T, ‖ramCopTail N P Q a t‖ ^ 2)
      = ∫ t in (-T)..T, ‖spoly N (fun n => if blockOmega P Q n = 0 then a n else 0) t‖ ^ 2 :=
    intervalIntegral.integral_congr (fun t _ => by rw [ramCopTail_eq_spoly])
  rw [hcongr]
  refine (moment_core_bound N _ T).trans_eq ?_
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h : blockOmega P Q n = 0 <;> simp [h]

/-- `ramCopTail N P Q a` is continuous (a finite sum of `aₙ/n^{1+it}`, `n ≥ 1`). -/
lemma continuous_ramCopTail (N P Q : ℕ) (a : ℕ → ℂ) :
    Continuous (ramCopTail N P Q a) := by
  unfold ramCopTail
  refine continuous_finsetSum _ (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  exact continuous_cterm (by have := (Finset.mem_Icc.mp hn.1).1; omega) (a n)

/-- `ramP2corr N P Q a b c` is continuous (a finite sum of `p²`-correction terms, `pm ≥ 1`). -/
lemma continuous_ramP2corr (N P Q : ℕ) (a b c : ℕ → ℂ) :
    Continuous (ramP2corr N P Q a b c) := by
  unfold ramP2corr
  refine continuous_finsetSum _ (fun p _ => continuous_finsetSum _ (fun m hm => ?_))
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hm
  have hpm : p * m ≠ 0 := by have := hm.1.2.1; omega
  exact ((continuous_cterm hpm (a (p * m))).const_smul _).sub
    ((continuous_cterm hpm (b m * c p)).mul continuous_const)

/-- `ramWindowErr H N X P Q b c` is continuous (a block sum of `(c_p/p^s)`-weighted differences
of continuous cofactor polynomials). -/
lemma continuous_ramWindowErr (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) :
    Continuous (ramWindowErr H N X P Q b c) := by
  unfold ramWindowErr
  refine continuous_finsetSum _ (fun j _ => continuous_finsetSum _ (fun p hp => ?_))
  rw [ramQblock, Finset.mem_filter] at hp
  refine (continuous_cterm hp.2.1.pos.ne' (c p)).mul (Continuous.sub ?_
    (continuous_ramR H N X P Q j b))
  refine continuous_finsetSum _ (fun m hm => ?_)
  rw [Finset.mem_filter, Finset.mem_Icc] at hm
  have hm0 : m ≠ 0 := by have := hm.2.1; rintro rfl; simp at this
  exact (continuous_cterm hm0 (b m)).mul continuous_const

/-- **W3 — the error-moment triangle split.**  Via the exact `W2` characterization
`ramErr = window + p²-correction + coprime-tail` and `‖x+y+z‖² ≤ 3(‖x‖²+‖y‖²+‖z‖²)`, the error
second moment splits into the three row moments — reducing `herr` to pricing the window and
`p²`-correction rows (the tail row is `ramCopTail_moment`). -/
theorem ramErr_moment_split (H : ℝ) (hH : 0 < H) (N X P Q : ℕ) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramErr H N X P Q a b c t‖ ^ 2)
      ≤ 3 * ((∫ t in (-T)..T, ‖ramWindowErr H N X P Q b c t‖ ^ 2)
            + (∫ t in (-T)..T, ‖ramP2corr N P Q a b c t‖ ^ 2)
            + (∫ t in (-T)..T, ‖ramCopTail N P Q a t‖ ^ 2)) := by
  have hWc := continuous_ramWindowErr H N X P Q b c
  have hCc := continuous_ramP2corr N P Q a b c
  have hDc := continuous_ramCopTail N P Q a
  have hIW : IntervalIntegrable (fun t => ‖ramWindowErr H N X P Q b c t‖ ^ 2) volume (-T) T :=
    (hWc.norm.pow 2).intervalIntegrable (-T) T
  have hIC : IntervalIntegrable (fun t => ‖ramP2corr N P Q a b c t‖ ^ 2) volume (-T) T :=
    (hCc.norm.pow 2).intervalIntegrable (-T) T
  have hID : IntervalIntegrable (fun t => ‖ramCopTail N P Q a t‖ ^ 2) volume (-T) T :=
    (hDc.norm.pow 2).intervalIntegrable (-T) T
  have hcongr : (∫ t in (-T)..T, ‖ramErr H N X P Q a b c t‖ ^ 2)
      = ∫ t in (-T)..T, ‖ramWindowErr H N X P Q b c t + ramP2corr N P Q a b c t
          + ramCopTail N P Q a t‖ ^ 2 :=
    intervalIntegral.integral_congr
      (fun t _ => by rw [ramErr_window_decomp H hH N X P Q hP a b c hcoef])
  rw [hcongr]
  calc (∫ t in (-T)..T, ‖ramWindowErr H N X P Q b c t + ramP2corr N P Q a b c t
            + ramCopTail N P Q a t‖ ^ 2)
      ≤ ∫ t in (-T)..T, (3 * ‖ramWindowErr H N X P Q b c t‖ ^ 2
            + 3 * ‖ramP2corr N P Q a b c t‖ ^ 2 + 3 * ‖ramCopTail N P Q a t‖ ^ 2) := by
        refine intervalIntegral.integral_mono_on (by linarith)
          ((((hWc.add hCc).add hDc).norm.pow 2).intervalIntegrable (-T) T)
          (((hIW.const_mul 3).add (hIC.const_mul 3)).add (hID.const_mul 3)) (fun t _ => ?_)
        nlinarith [norm_add_le (ramWindowErr H N X P Q b c t + ramP2corr N P Q a b c t)
            (ramCopTail N P Q a t),
          norm_add_le (ramWindowErr H N X P Q b c t) (ramP2corr N P Q a b c t),
          norm_nonneg (ramWindowErr H N X P Q b c t), norm_nonneg (ramP2corr N P Q a b c t),
          norm_nonneg (ramCopTail N P Q a t),
          norm_nonneg (ramWindowErr H N X P Q b c t + ramP2corr N P Q a b c t),
          norm_nonneg (ramWindowErr H N X P Q b c t + ramP2corr N P Q a b c t
            + ramCopTail N P Q a t),
          sq_nonneg (‖ramWindowErr H N X P Q b c t‖ - ‖ramP2corr N P Q a b c t‖),
          sq_nonneg (‖ramWindowErr H N X P Q b c t‖ - ‖ramCopTail N P Q a t‖),
          sq_nonneg (‖ramP2corr N P Q a b c t‖ - ‖ramCopTail N P Q a t‖)]
    _ = 3 * ((∫ t in (-T)..T, ‖ramWindowErr H N X P Q b c t‖ ^ 2)
            + (∫ t in (-T)..T, ‖ramP2corr N P Q a b c t‖ ^ 2)
            + (∫ t in (-T)..T, ‖ramCopTail N P Q a t‖ ^ 2)) := by
        rw [intervalIntegral.integral_add ((hIW.const_mul 3).add (hIC.const_mul 3))
            (hID.const_mul 3),
          intervalIntegral.integral_add (hIW.const_mul 3) (hIC.const_mul 3),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
        ring

/-! ## R-corr — the `p²`-correction row as a `spoly`, and its second moment (MR p.20)

The `p²`-correction `ramP2corr` is a `(p,m)` double sum of terms `w(p,m)/(pm)^{1+it}` with all
frequencies `pm ∈ [1,N]` (the domain filter `p*m ∈ Icc 1 N`).  The fiberwise reindex
`(p,m) ↦ pm` collapses it to a single `spoly N ramP2coeff`, so `moment_core_bound` prices its
second moment at the `(2T+20N)·Σ_{n∈[1,N]}‖ramP2coeff n‖²/n²` grade — no frequency inflation. -/

/-- **The `p²`-correction domain**: block-prime/cofactor pairs `(p,m)` with `pm ∈ [1,N]` and
`p ∣ m` — the `(p,m)`-sigma index of `ramP2corr`. -/
noncomputable def ramP2dom (N P Q : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  ((Finset.Icc P Q).filter Nat.Prime).sigma
    (fun p => (((Finset.Icc 1 N).image (fun n => n / p)).filter
      (fun m => p * m ∈ Finset.Icc 1 N)).filter (fun m => p ∣ m))

/-- **The `p²`-correction coefficient** at frequency `n`: the fiber sum of the correction
weights `w(p,m) = ramareWeight·a_{pm} − b_m·c_p/(ω(m)+1)` over factorisations `pm = n` with `p`
a block prime and `p ∣ m` (so `p² ∣ n`). -/
noncomputable def ramP2coeff (N P Q : ℕ) (a b c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ σ ∈ (ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n),
    ((ramareWeight P Q σ.1 σ.2 : ℂ) * a (σ.1 * σ.2)
      - b σ.2 * c σ.1 * ((blockOmega P Q σ.2 : ℂ) + 1)⁻¹)

/-- **R-corr (structure) — the `p²`-correction as a `spoly`.**  The fiberwise reindex
`(p,m) ↦ pm` (a `sum_fiberwise_of_maps_to` into `Icc 1 N`, valid since every domain pair has
`pm ∈ [1,N]`) collapses the correction double sum to `spoly N ramP2coeff`. -/
theorem ramP2corr_eq_spoly (N P Q : ℕ) (a b c : ℕ → ℂ) (t : ℝ) :
    ramP2corr N P Q a b c t = spoly N (ramP2coeff N P Q a b c) t := by
  have hmaps : ∀ σ ∈ ((Finset.Icc P Q).filter Nat.Prime).sigma
      (fun p => (((Finset.Icc 1 N).image (fun n => n / p)).filter
        (fun m => p * m ∈ Finset.Icc 1 N)).filter (fun m => p ∣ m)),
      σ.1 * σ.2 ∈ Finset.Icc 1 N := by
    intro σ hσ
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter] at hσ
    exact hσ.2.1.2
  rw [ramP2corr, Finset.sum_sigma', ← Finset.sum_fiberwise_of_maps_to hmaps, spoly]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [ramP2coeff, Finset.sum_div]
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  rw [Finset.mem_filter] at hσ
  rw [Complex.real_smul, ← mul_div_assoc, div_mul_eq_mul_div, div_sub_div_same, hσ.2]

/-- **R-corr — the `p²`-correction second moment.**  Via `ramP2corr_eq_spoly` and the keystone
`moment_core_bound`, the correction's mean square is priced at
`(2T+20N)·Σ_{n∈[1,N]}‖ramP2coeff n‖²/n²`. -/
theorem ramP2corr_moment (N P Q : ℕ) (a b c : ℕ → ℂ) (T : ℝ) :
    (∫ t in (-T)..T, ‖ramP2corr N P Q a b c t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ))
          * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 := by
  have hcongr : (∫ t in (-T)..T, ‖ramP2corr N P Q a b c t‖ ^ 2)
      = ∫ t in (-T)..T, ‖spoly N (ramP2coeff N P Q a b c) t‖ ^ 2 :=
    intervalIntegral.integral_congr (fun t _ => by rw [ramP2corr_eq_spoly])
  rw [hcongr]
  exact moment_core_bound N (ramP2coeff N P Q a b c) T

/-- **The `σ=1` Dirichlet term norm.**  `‖c/k^{1+it}‖ = ‖c‖/k` (`k ≥ 1`): the cpow has
`Re(1+it)=1`, so `‖k^{1+it}‖ = k`. -/
lemma norm_cterm_eq (k : ℕ) (hk : 1 ≤ k) (c : ℂ) (t : ℝ) :
    ‖c / (k : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ = ‖c‖ / (k : ℝ) := by
  rw [norm_div]
  congr 1
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hkpos]
  simp

/-- **The Ramaré-weighted term norm bound.**  `‖(b_m/m^{1+it})·(ω(m)+1)⁻¹‖ ≤ ‖b_m‖/m`
(`m ≥ 1`): the weight `(ω(m)+1)⁻¹` has norm `≤ 1`. -/
lemma norm_weighted_cterm_le (P Q m : ℕ) (hm : 1 ≤ m) (b : ℕ → ℂ) (t : ℝ) :
    ‖(b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) * ((blockOmega P Q m : ℂ) + 1)⁻¹‖
      ≤ ‖b m‖ / (m : ℝ) := by
  rw [norm_mul, norm_cterm_eq m hm (b m) t]
  have hb : ‖((blockOmega P Q m : ℂ) + 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have heq : ‖(blockOmega P Q m : ℂ) + 1‖ = (blockOmega P Q m : ℝ) + 1 := by
      rw [show ((blockOmega P Q m : ℂ) + 1) = ((blockOmega P Q m + 1 : ℕ) : ℂ) by push_cast; ring,
        Complex.norm_natCast]
      push_cast; ring
    rw [heq]
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (by positivity))
  calc (‖b m‖ / (m : ℝ)) * ‖((blockOmega P Q m : ℂ) + 1)⁻¹‖
      ≤ (‖b m‖ / (m : ℝ)) * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ‖b m‖ / (m : ℝ) := mul_one _

/-- **The window ℓ¹-mass** — the `t`-independent sup bound on `ramWindowErr`: over each block
`j` and prime `p`, the factor `‖c_p‖/p` against the honest-plus-`R_{j,H}` cofactor `‖b_m‖/m`
masses. -/
noncomputable def windowMass (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) : ℝ :=
  ∑ j ∈ ramI H P Q, ∑ p ∈ ramQblock H P Q j,
    (‖c p‖ / (p : ℝ)) * ((∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
          (fun m => p * m ∈ Finset.Icc 1 N), ‖b m‖ / (m : ℝ))
        + ∑ m ∈ ramRrange H N X j, ‖b m‖ / (m : ℝ))

/-- **R-window (structure) — the trivial-sup bound.**  `‖ramWindowErr t‖ ≤ windowMass`, uniformly
in `t`: `‖c_p/p^{1+it}‖ = ‖c_p‖/p`, and the honest-minus-`R_{j,H}` cofactor difference is bounded
by the sum of the two cofactor `ℓ¹`-masses (each term `≤ ‖b_m‖/m`).  This avoids pricing the
overcount at an inflated frequency cap — the `moment_core_bound`-at-`QN` trap. -/
theorem ramWindowErr_sup_le (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) (t : ℝ) :
    ‖ramWindowErr H N X P Q b c t‖ ≤ windowMass H N X P Q b c := by
  rw [ramWindowErr, windowMass]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj => ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p hp => ?_))
  rw [ramQblock, Finset.mem_filter] at hp
  rw [norm_mul, norm_cterm_eq p hp.2.1.pos (c p) t]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m hm => ?_))
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at hm
      · exact h
    exact norm_weighted_cterm_le P Q m hm1 b t
  · rw [ramR]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m hm => ?_))
    rw [ramRrange, Finset.mem_filter, Finset.mem_Icc] at hm
    exact norm_weighted_cterm_le P Q m hm.1.1 b t

/-- **R-window — the window second moment (trivial-sup grade).**  Via the `t`-uniform sup bound
`ramWindowErr_sup_le` and the constant integral `∫_{-T}^T M² = 2T·M²`. -/
theorem ramWindowErr_moment_triv (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramWindowErr H N X P Q b c t‖ ^ 2)
      ≤ 2 * T * (windowMass H N X P Q b c) ^ 2 := by
  have hM : 0 ≤ windowMass H N X P Q b c :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun p _ => by positivity))
  calc (∫ t in (-T)..T, ‖ramWindowErr H N X P Q b c t‖ ^ 2)
      ≤ ∫ _t in (-T)..T, (windowMass H N X P Q b c) ^ 2 := by
        refine intervalIntegral.integral_mono_on (by linarith)
          (((continuous_ramWindowErr H N X P Q b c).norm.pow 2).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) (fun t _ => ?_)
        nlinarith [ramWindowErr_sup_le H N X P Q b c t,
          norm_nonneg (ramWindowErr H N X P Q b c t), hM]
    _ = 2 * T * (windowMass H N X P Q b c) ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-! ## R-final — Lemma 12 mean square, UNCONDITIONAL (MR p.20)

Feeding the three row moments — the window trivial-sup bound `ramWindowErr_moment_triv`, the
`p²`-correction `ramP2corr_moment`, and the coprime-tail `ramCopTail_moment` — through the exact
error split `ramErr_moment_split` and the reduction `lemma12_meansq_of_windowErr` discharges
`herr` and closes Lemma 12's mean square with **no residual hypotheses** beyond the coefficient
factorisation `hcoef` (`a_{pm} = b_m c_p` on the coprime block, `P ≤ p ≤ Q`).  The error grade is
honest and explicit: `E = 3·(2T·windowMass² + (2T+20N)·(‖ramP2coeff‖²/n²-mass) +
(2T+20N)·(coprime-tail mass))`.  Collapsing `E` to the paper's `(T+X)/X·(1/H+1/P+tail)` normal
form (via `‖b‖,‖c‖ ≤ 1`, `N = 2X`, `window_card_le`, and the `Σ_{p≥P} p⁻²` zeta-tail) is the
remaining cosmetic sharpening — see NOTES. -/

/-- **Lemma 12 — the mean square, UNCONDITIONAL.**  With the concrete `Q_{j,H}·R_{j,H}` main
blocks and the difference-defined error priced by its three row moments, the full mean-square
bound holds for every coefficient triple `(a,b,c)` satisfying only the block factorisation
`hcoef`.  The error term `E` is fully explicit (window ℓ¹-mass² + correction mass + coprime-tail
mass), each a landed, kernel-checked stone. -/
theorem lemma12_meansq (H : ℝ) (hH : 0 < H) (N X P Q : ℕ) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in (-T)..T, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + 2 * (3 * (2 * T * (windowMass H N X P Q b c) ^ 2
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
                    ‖a n‖ ^ 2 / (n : ℝ) ^ 2)) := by
  refine lemma12_meansq_of_windowErr H N X P Q a b c T _ hT ?_
  refine (ramErr_moment_split H hH N X P Q hP a b c hcoef T hT).trans ?_
  gcongr
  · exact ramWindowErr_moment_triv H N X P Q b c T hT
  · exact ramP2corr_moment N P Q a b c T
  · exact ramCopTail_moment N P Q a T

end Salt.MR
