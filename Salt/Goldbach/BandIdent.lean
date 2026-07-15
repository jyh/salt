/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.WindowSW
import Salt.Goldbach.Band

/-!
# G-BANDIDENT — the Goldbach band identifications at the reflected carriers (wave W3a)

Design: `docs/exploration/pilot.md` (the `~16:30` G-BAND re-cut, the Opt-A adjudication, and the
`~16:35` G-WINDOWSW landed interface).  This file is the band analogue of `Salt/Goldbach/WindowSW`:
where WindowSW identifies the *window-in-carrier* main box, this file identifies the two BAND
RECTANGLES — the `α_low` piece (`p₂ ≤ Nf < p₃`, ordering automatic) and the SYMMETRIC piece
(`max(y,Nf) < p₂, p₃ ≤ M`, unordered double count) — and lands the band close the diagonal
aggregate (G-PDIAG) consumes.

## Reuse census (measured against the twin `Salt/Chen/BandSplit|BandClose|BandIdent`)

* `sum_symm_ordered_split` (BandSplit) — carrier-generic, INSTANTIATED verbatim (no mirror).
* `goldWindowDisc_le_annulus_sum` (WindowSW) — generic in `α, β`, REUSED verbatim for the telescope.
* `blockAlphaLow`, `blockAlphaSym`, `norm_blockAlphaLow_le_one`, `norm_blockAlphaSym_le_one`,
  `lowPairPred`, `symPairPred`, `bandP1Set`, `bandLargeSet` (Chen) — carrier-agnostic PUBLIC defs,
  REUSED (with the ambient `Ne`).
* The private twin summand/pairTerm/uniqueness lemmas hit the PRIVATE WALL (fourth occurrence) and
  are RESTATED locally.
* The pair bijections + cutoff identifications are `goldTripleSet`-tied and RE-DERIVED here, at the
  GENERAL cutoffs `(Tlo, Thi]` (the twin's hard-wired `(x/2+1, x]` generalized, per WindowSW), with
  the window supplied by an `hPwin`; the residue slot is a FREE `R₀` (G-PDIAG takes `crtClassG`).

## Per-annulus vs window-free census (the byte-lock for G-SW2 / G-PDIAG)

* PER-ANNULUS (carry the `k`/cutoff index — the window enters): `goldLowRect_windowDisc_eq`,
  `goldSymRect_windowDisc_eq` (general `(Tlo,Thi]`); `goldLowRect_eq`, `goldSymRect_eq` (the annulus
  instances at `(goldCut Ne k, goldCut Ne (k+1)]`); the annulus-sum bounds `goldBandLowDisc_le_*`,
  `goldBandSymRectDisc_le_*`.
* WINDOW-FREE (no `k` — the full window `2 ≤ prod3 ≤ Ne/2` is built into `goldTripleSet`):
  `goldBandCard_split`, `goldSymCard_two_mul`, `goldBandDiagCount_le`, `goldBandDiscW_eq_three`, and
  the count/honest-disc defs.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset ArithmeticFunction

namespace Salt.Goldbach

open Salt.Chen

/-! ## Part 0 — the oriented-factorization uniqueness kernel (private-wall restatement) -/

/-- Re-proof of the private twin `prime_pair_unique_ident` / WindowSW `gold_prime_pair_unique`: the
oriented `m ↦ {p₁, p₂}` factorization at `y` is unique.  The injectivity kernel of both band
rectangle bijections. -/
private lemma gold_pair_unique_bi {y p₁ p₂ p₁' p₂' : ℕ}
    (h1 : p₁.Prime) (h1' : p₁'.Prime) (h2' : p₂'.Prime)
    (hp1 : p₁ ≤ y) (hp2' : y < p₂')
    (heq : p₁ * p₂ = p₁' * p₂') : p₁ = p₁' ∧ p₂ = p₂' := by
  have hdvd : p₁ ∣ p₁' * p₂' := heq ▸ dvd_mul_right p₁ p₂
  rcases (Nat.Prime.dvd_mul h1).mp hdvd with hd | hd
  · have heqp : p₁ = p₁' := (Nat.prime_dvd_prime_iff_eq h1 h1').mp hd
    refine ⟨heqp, ?_⟩
    rw [heqp] at heq
    exact Nat.eq_of_mul_eq_mul_left h1'.pos heq
  · have heqp : p₁ = p₂' := (Nat.prime_dvd_prime_iff_eq h1 h2').mp hd
    omega

/-! ## Part A — the low rectangle (`p₂ ≤ Nf`, ordering automatic) -/

open Classical in
/-- Restatement of the private twin `summand_eq_low`: the `apDiscBilinCutoff` summand at the low
coefficient is the `lowPairPred` `0/1` indicator (carrier-agnostic — reuses `blockAlphaLow`). -/
private lemma gold_summand_low (z y : ℕ) (ε₀ : ℝ) (j Nf a b : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (q : ℕ × ℕ) :
    (if P (q.1 * q.2) then
        restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b q.1 * blockPrimeInd Nf q.2 else (0 : ℂ))
      = (if lowPairPred z y ε₀ j Nf a b P q then (1 : ℂ) else 0) := by
  classical
  unfold lowPairPred restrictAlpha blockAlphaLow blockPrimeInd
  by_cases hP : P (q.1 * q.2)
  · by_cases hbox : a ≤ q.1 ∧ q.1 < b
    · by_cases hf : (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧ p₂ ≤ Nf ∧
          p₁ * p₂ = q.1 ∧ blockIdx z ε₀ p₁ = j)
      · by_cases hn : Nf < q.2 ∧ q.2.Prime
        · rw [if_pos hP, if_pos hbox, if_pos hf, if_pos hn, if_pos ⟨hP, hbox, hf, hn⟩, mul_one]
        · rw [if_pos hP, if_pos hbox, if_pos hf, if_neg hn, mul_zero,
            if_neg (fun h => hn h.2.2.2)]
      · rw [if_pos hP, if_pos hbox, if_neg hf, zero_mul, if_neg (fun h => hf h.2.2.1)]
    · rw [if_pos hP, if_neg hbox, zero_mul, if_neg (fun h => hbox h.2.1)]
  · rw [if_neg hP, if_neg (fun h => hP h.1)]

open Classical in
/-- Restatement of the private twin `pairTerm_eq_low`: the low double sum counts the `lowPairPred`
pairs. -/
private lemma gold_pairTerm_low (z y : ℕ) (ε₀ : ℝ) (j Nf a b X M : ℕ) (P : ℕ → Prop)
    [DecidablePred P] :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 M,
        if P (m * n) then
          restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b m * blockPrimeInd Nf n else (0 : ℂ))
      = (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
            (fun q => lowPairPred z y ε₀ j Nf a b P q)).card : ℂ) := by
  classical
  rw [← Finset.sum_product']
  rw [Finset.sum_congr rfl (fun q _ => gold_summand_low z y ε₀ j Nf a b P q)]
  rw [Finset.sum_boole]

open Classical in
/-- **`goldLowBox_pair_card` — the low-rectangle pair bijection over `goldTripleSet` (ordering
AUTOMATIC).**  The `goldTripleSet` analogue of the twin `lowBox_pair_card`: the `p₂ ≤ Nf` cap is
baked into `blockAlphaLow`, so the ordering `p₂ ≤ Nf < p₃` needs NO `hord` (surjectivity derives
`p₂ ≤ q.2` from `p₂ ≤ Nf < q.2`).  The BOTTOM-half window is supplied by `hPwin`
(`P v → 2 ≤ v ∧ v ≤ Ne/2`), the box is `Icc 1 Ne` (via `Nat.div_le_self`). -/
theorem goldLowBox_pair_card {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M a b X : ℕ}
    (P : ℕ → Prop) [DecidablePred P]
    (hbX : b ≤ X + 1)
    (hPwin : ∀ v : ℕ, P v → 2 ≤ v ∧ v ≤ Ne / 2) :
    (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter (fun q => lowPairPred z y ε₀ j Nf a b P q)).card)
      = (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ P (prod3 t) ∧
          Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧ t.2.1 ≤ Nf)).card) := by
  classical
  symm
  apply Finset.card_bij (fun t _ => (t.1 * t.2.1, t.2.2))
  · intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htri, hblk, hP, hNlt, hMle, hab_lo, hab_hi, hp2N⟩ := ht
    rw [goldTripleSet, Finset.mem_filter] at htri
    obtain ⟨_, hzp1, hp1y, hyp2, _hp2p3, hp1prime, hp2prime, hp3prime, _hwlo, _hwhi⟩ := htri
    have hm1 : 1 ≤ t.1 * t.2.1 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hp1prime.pos.ne' hp2prime.pos.ne')
    have hmX : t.1 * t.2.1 ≤ X := by omega
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨hm1, hmX⟩, ⟨hp3prime.pos, hMle⟩⟩,
      hP, ⟨hab_lo, hab_hi⟩,
      ⟨t.1, t.2.1, hp1prime, hp2prime, hzp1, hp1y, hyp2, hp2N, rfl, hblk⟩, ⟨hNlt, hp3prime⟩⟩
  · intro t ht t' ht' heq
    rw [Finset.mem_filter] at ht ht'
    have htri := ht.1
    have htri' := ht'.1
    rw [goldTripleSet, Finset.mem_filter] at htri htri'
    obtain ⟨_, _, hp1y, _, _, hp1prime, _, _, _, _⟩ := htri
    obtain ⟨_, _, _, hyp2', _, hp1prime', hp2prime', _, _, _⟩ := htri'
    rw [Prod.mk.injEq] at heq
    obtain ⟨hmeq, hneq⟩ := heq
    obtain ⟨he1, he2⟩ := gold_pair_unique_bi hp1prime hp1prime' hp2prime' hp1y hyp2' hmeq
    exact Prod.ext_iff.mpr ⟨he1, Prod.ext_iff.mpr ⟨he2, hneq⟩⟩
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
    obtain ⟨⟨⟨hq1lo, _hq1hi⟩, hq2lo, hq2hi⟩, hpp⟩ := hq
    obtain ⟨hP, ⟨ha_lo, ha_hi⟩, ⟨p₁, p₂, hp1prime, hp2prime, hzp1, hp1y, hyp2, hp2N, hprod, hblk⟩,
      ⟨hNq2, hq2prime⟩⟩ := hpp
    have hord3 : p₂ ≤ q.2 := by omega
    obtain ⟨hwlo, hwhi⟩ := hPwin (q.1 * q.2) hP
    have hprod3 : prod3 (p₁, p₂, q.2) = q.1 * q.2 := by
      change p₁ * p₂ * q.2 = q.1 * q.2; rw [hprod]
    have hq1N : q.1 ≤ Ne := le_trans (le_trans (Nat.le_mul_of_pos_right q.1 (by omega)) hwhi)
      (Nat.div_le_self Ne 2)
    have hq2N : q.2 ≤ Ne := le_trans (le_trans (Nat.le_mul_of_pos_left q.2 (by omega)) hwhi)
      (Nat.div_le_self Ne 2)
    have hp1le : p₁ ≤ q.1 := by rw [← hprod]; exact Nat.le_mul_of_pos_right p₁ hp2prime.pos
    have hp2le : p₂ ≤ q.1 := by rw [← hprod]; exact Nat.le_mul_of_pos_left p₂ hp1prime.pos
    refine ⟨(p₁, p₂, q.2), ?_, Prod.ext_iff.mpr ⟨hprod, rfl⟩⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hblk, ?_, hNq2, hq2hi, ?_, ?_, hp2N⟩
    · rw [goldTripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
      refine ⟨⟨⟨hp1prime.pos, le_trans hp1le hq1N⟩, ⟨hp2prime.pos, le_trans hp2le hq1N⟩,
          ⟨hq2prime.pos, hq2N⟩⟩,
        hzp1, hp1y, hyp2, hord3, hp1prime, hp2prime, hq2prime, ?_, ?_⟩
      · rw [hprod3]; exact hwlo
      · rw [hprod3]; exact hwhi
    · rw [hprod3]; exact hP
    · change a ≤ p₁ * p₂
      rw [hprod]; exact ha_lo
    · change p₁ * p₂ < b
      rw [hprod]; exact ha_hi

open Classical in
/-- **`gold_cutoffDiff_low` — the general-cutoff low difference is the annulus low-pair count.**
The low mirror of WindowSW's `gold_cutoffDiff_eq_pairCard`: subtracting the `T = Tlo` cutoff from
the `T = Thi` cutoff folds the annulus `Tlo < m·n ≤ Thi` into the class predicate, and
`gold_pairTerm_low` counts the survivors. -/
private lemma gold_cutoffDiff_low (z y : ℕ) (ε₀ : ℝ) (j Nf a b X M : ℕ)
    (P : ℕ → Prop) [DecidablePred P] (Tlo Thi : ℕ) (hT : Tlo ≤ Thi) :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
        if P (m * n) then
          restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b m * blockPrimeInd Nf n else (0 : ℂ))
      - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
        if P (m * n) then
          restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b m * blockPrimeInd Nf n else (0 : ℂ))
      = (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
          (fun q => lowPairPred z y ε₀ j Nf a b
            (fun v => Tlo < v ∧ v ≤ Thi ∧ P v) q)).card : ℂ) := by
  classical
  rw [← gold_pairTerm_low z y ε₀ j Nf a b X M (fun v => Tlo < v ∧ v ≤ Thi ∧ P v),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hP : P (m * n)
  · by_cases hx : m * n ≤ Thi
    · by_cases hlo : m * n ≤ Tlo
      · have hnw : ¬ (Tlo < m * n ∧ m * n ≤ Thi ∧ P (m * n)) := fun ⟨hw, _, _⟩ => by omega
        rw [if_pos hx, if_pos hlo, sub_self, if_neg hnw]
      · rw [if_pos hx, if_neg hlo, sub_zero, if_pos hP,
          if_pos (show Tlo < m * n ∧ m * n ≤ Thi ∧ P (m * n) from ⟨by omega, hx, hP⟩)]
    · have hlo : ¬ m * n ≤ Tlo := by omega
      have hnw : ¬ (Tlo < m * n ∧ m * n ≤ Thi ∧ P (m * n)) := fun ⟨_, hw, _⟩ => by omega
      rw [if_neg hx, if_neg hlo, sub_self, if_neg hnw]
  · have hnw : ¬ (Tlo < m * n ∧ m * n ≤ Thi ∧ P (m * n)) := fun ⟨_, _, hp⟩ => hP hp
    simp only [if_neg hP, if_neg hnw, ite_self, sub_self]

open Classical in
/-- **`goldLowRect_windowDisc_eq` — the low identification at a FREE residue and GENERAL cutoffs.**
The `α_low` mirror of WindowSW's `goldBlockBox_windowDisc_eq_res`: on the ordering-cleared low box
(`p₂ ≤ Nf < p₃`, automatic) the difference of the two one-sided cutoff carriers at `(Tlo, Thi]`
equals the `goldTripleSet` low-count difference restricted to `Tlo < prod3 ≤ Thi`.  NO coprimality,
NO `hord` (the cap `p₂ ≤ Nf` is in `blockAlphaLow`).  The residue slot `R₀` is FREE — G-PDIAG takes
`R₀ := crtClassG Q d N a`.  Instantiate at the annulus `(goldCut Ne k, goldCut Ne (k+1)]`. -/
theorem goldLowRect_windowDisc_eq {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M a b X d R₀ : ℕ}
    (hbX : b ≤ X + 1) (Tlo Thi : ℕ) (hTlo : 1 ≤ Tlo) (hThi : Thi ≤ Ne / 2) (hT : Tlo ≤ Thi) :
    apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b) (blockPrimeInd Nf) X M R₀ d
        Thi
      - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b) (blockPrimeInd Nf) X M R₀
          d Tlo
      = (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            (Tlo < prod3 t ∧ prod3 t ≤ Thi ∧
              ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) ∧
            Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧ t.2.1 ≤ Nf)).card : ℂ)
        - (1 / (d.totient : ℂ)) *
          (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            (Tlo < prod3 t ∧ prod3 t ≤ Thi ∧
              IsUnit ((prod3 t : ℕ) : ZMod d)) ∧
            Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧
              t.2.1 ≤ Nf)).card : ℂ) := by
  classical
  have hPwinR : ∀ v : ℕ, (Tlo < v ∧ v ≤ Thi ∧
      ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) → 2 ≤ v ∧ v ≤ Ne / 2 :=
    fun v hv => ⟨by omega, le_trans hv.2.1 hThi⟩
  have hPwinU : ∀ v : ℕ, (Tlo < v ∧ v ≤ Thi ∧
      IsUnit ((v : ℕ) : ZMod d)) → 2 ≤ v ∧ v ≤ Ne / 2 :=
    fun v hv => ⟨by omega, le_trans hv.2.1 hThi⟩
  have hRes :
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b m * blockPrimeInd Nf n else 0)
        - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b m * blockPrimeInd Nf n else 0)
        = (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            (Tlo < prod3 t ∧ prod3 t ≤ Thi ∧
              ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) ∧
            Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧
              t.2.1 ≤ Nf)).card : ℂ) := by
    rw [gold_cutoffDiff_low z y ε₀ j Nf a b X M
      (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) Tlo Thi hT]
    exact_mod_cast goldLowBox_pair_card
      (fun v => Tlo < v ∧ v ≤ Thi ∧ ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) hbX hPwinR
  have hUnit :
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
          if IsUnit ((m * n : ℕ) : ZMod d) then
            restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b m * blockPrimeInd Nf n else 0)
        - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
          if IsUnit ((m * n : ℕ) : ZMod d) then
            restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b m * blockPrimeInd Nf n else 0)
        = (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            (Tlo < prod3 t ∧ prod3 t ≤ Thi ∧
              IsUnit ((prod3 t : ℕ) : ZMod d)) ∧
            Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧
              t.2.1 ≤ Nf)).card : ℂ) := by
    rw [gold_cutoffDiff_low z y ε₀ j Nf a b X M
      (fun v => IsUnit ((v : ℕ) : ZMod d)) Tlo Thi hT]
    exact_mod_cast goldLowBox_pair_card
      (fun v => Tlo < v ∧ v ≤ Thi ∧ IsUnit ((v : ℕ) : ZMod d)) hbX hPwinU
  have hexpx : apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b)
        (blockPrimeInd Nf) X M R₀ d Thi
      = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b m * blockPrimeInd Nf n else 0)
        - (1 / (d.totient : ℂ)) *
          (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
            if IsUnit ((m * n : ℕ) : ZMod d) then
              restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b m * blockPrimeInd Nf n else 0) :=
    rfl
  have hexplo : apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b)
        (blockPrimeInd Nf) X M R₀ d Tlo
      = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b m * blockPrimeInd Nf n else 0)
        - (1 / (d.totient : ℂ)) *
          (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
            if IsUnit ((m * n : ℕ) : ZMod d) then
              restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b m * blockPrimeInd Nf n else 0) :=
    rfl
  rw [hexpx, hexplo]
  rw [show ∀ (r1 u1 r2 u2 : ℂ),
      (r1 - (1 / (d.totient : ℂ)) * u1) - (r2 - (1 / (d.totient : ℂ)) * u2)
        = (r1 - r2) - (1 / (d.totient : ℂ)) * (u1 - u2) from fun r1 u1 r2 u2 => by ring]
  rw [hRes, hUnit]

/-! ## Part A′ — the low count, honest disc, annulus instance, carrier, and annulus-sum bound -/

open Classical in
/-- **`goldLowCard`** — the FULL-window `α_low` count over `goldTripleSet`: block-`j` triples with
`p₂ ≤ Nf < p₃ ≤ M`, `a ≤ p₁p₂ < b`, and class `C` (the window `2 ≤ prod3 ≤ Ne/2` is built into
`goldTripleSet`, so it carries NO explicit annulus). -/
noncomputable def goldLowCard (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M a b : ℕ) (C : ℕ → Prop) : ℝ :=
  (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ C (prod3 t) ∧
      Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧ t.2.1 ≤ Nf)).card : ℝ)

open Classical in
/-- **`goldBandLowDisc`** — the `α_low` honest discrepancy (`res − ν·unit`) at the free residue
`R₀`.  BV-priced downstream (`goldBandLowDisc_le_annulus_sum`). -/
noncomputable def goldBandLowDisc (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M a b d R₀ : ℕ) : ℝ :=
  goldLowCard Ne z y ε₀ j Nf M a b (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d))
    - nuChen d * goldLowCard Ne z y ε₀ j Nf M a b (fun v => IsUnit ((v : ℕ) : ZMod d))

open Classical in
/-- **`goldLowRect_eq` — the `α_low` identification at the dyadic annulus (byte-lock for G-SW2).**
The `goldLowRect_windowDisc_eq` instance at the factor-2 endpoints
`(goldCut Ne k, goldCut Ne (k+1)]`; each annulus is factor-2 (`goldCut_succ_le_two_mul`), so G-SW2
may price it by `box_disc_three_way`. -/
theorem goldLowRect_eq {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M a b X d R₀ : ℕ}
    (hNe : 2 ≤ Ne) (hbX : b ≤ X + 1) (k : ℕ) :
    apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b) (blockPrimeInd Nf) X M R₀ d
        (goldCut Ne (k + 1))
      - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b) (blockPrimeInd Nf) X M R₀
          d (goldCut Ne k)
      = (((goldTripleSet Ne z y).filter (fun (t : ℕ × ℕ × ℕ) => blockIdx z ε₀ t.1 = j ∧
            (goldCut Ne k < prod3 t ∧ prod3 t ≤ goldCut Ne (k + 1) ∧
              ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) ∧
            Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧
              t.2.1 ≤ Nf)).card : ℂ)
        - (1 / (d.totient : ℂ)) *
          (((goldTripleSet Ne z y).filter (fun (t : ℕ × ℕ × ℕ) => blockIdx z ε₀ t.1 = j ∧
            (goldCut Ne k < prod3 t ∧ prod3 t ≤ goldCut Ne (k + 1) ∧
              IsUnit ((prod3 t : ℕ) : ZMod d)) ∧
            Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧
              t.2.1 ≤ Nf)).card : ℂ) :=
  goldLowRect_windowDisc_eq hbX (goldCut Ne k) (goldCut Ne (k + 1))
    (one_le_goldCut hNe k) (goldCut_le_half Ne (k + 1)) (goldCut_mono Ne (Nat.le_succ k))

open Classical in
/-- **`goldBandLowDisc_eq_carrier` — the full-window `α_low` identification.**  The `α_low` honest
disc IS the cutoff-carrier difference at the whole window `(1, Ne/2]` (`goldLowRect_windowDisc_eq`
at `Tlo = 1`, `Thi = Ne/2`), the window `1 < prod3 ≤ Ne/2` redundant on `goldTripleSet`. -/
theorem goldBandLowDisc_eq_carrier {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M a b X d R₀ : ℕ}
    (hNe : 2 ≤ Ne) (hbX : b ≤ X + 1) :
    ((goldBandLowDisc Ne z y ε₀ j Nf M a b d R₀ : ℝ) : ℂ)
      = apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b) (blockPrimeInd Nf) X M R₀
          d (Ne / 2)
        - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b) (blockPrimeInd Nf) X M
            R₀ d 1 := by
  classical
  have hhalf : (1 : ℕ) ≤ Ne / 2 := by omega
  have hredR : ((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        (1 < prod3 t ∧ prod3 t ≤ Ne / 2 ∧
          ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) ∧
        Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧ t.2.1 ≤ Nf)).card
      = ((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) ∧
        Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧ t.2.1 ≤ Nf)).card := by
    apply congrArg
    apply Finset.filter_congr
    intro t ht
    rw [goldTripleSet, Finset.mem_filter] at ht
    obtain ⟨_, _, _, _, _, _, _, _, hwlo, hwhi⟩ := ht
    constructor
    · rintro ⟨h1, ⟨_, _, hr⟩, hrest⟩; exact ⟨h1, hr, hrest⟩
    · rintro ⟨h1, hr, hrest⟩; exact ⟨h1, ⟨by omega, hwhi, hr⟩, hrest⟩
  have hredU : ((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        (1 < prod3 t ∧ prod3 t ≤ Ne / 2 ∧ IsUnit ((prod3 t : ℕ) : ZMod d)) ∧
        Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧ t.2.1 ≤ Nf)).card
      = ((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        IsUnit ((prod3 t : ℕ) : ZMod d) ∧
        Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧ t.2.1 ≤ Nf)).card := by
    apply congrArg
    apply Finset.filter_congr
    intro t ht
    rw [goldTripleSet, Finset.mem_filter] at ht
    obtain ⟨_, _, _, _, _, _, _, _, hwlo, hwhi⟩ := ht
    constructor
    · rintro ⟨h1, ⟨_, _, hr⟩, hrest⟩; exact ⟨h1, hr, hrest⟩
    · rintro ⟨h1, hr, hrest⟩; exact ⟨h1, ⟨by omega, hwhi, hr⟩, hrest⟩
  rw [goldLowRect_windowDisc_eq (X := X) hbX 1 (Ne / 2) (le_refl 1) (le_refl (Ne / 2)) hhalf,
    goldBandLowDisc, goldLowCard, goldLowCard, nuChen_apply, hredR, hredU]
  push_cast
  ring_nf

/-- **`goldBandLowDisc_le_annulus_sum` — the consumable `α_low` price (byte-lock for G-SW2).**  The
`Dset`-sum of `α_low` honest discrepancies is bounded by the `(annulus × Dset)` double sum of the
per-annulus carrier differences (`goldBandLowDisc_eq_carrier` anchors each `|·|` to the full-window
difference; the generic `goldWindowDisc_le_annulus_sum` telescopes it). -/
theorem goldBandLowDisc_le_annulus_sum {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M a b X : ℕ}
    (r : ℕ → ℕ) (Dset : Finset ℕ)
    (hNe : 2 ≤ Ne) (hbX : b ≤ X + 1) :
    (∑ d ∈ Dset, |goldBandLowDisc Ne z y ε₀ j Nf M a b d (r d)|)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 Ne + 1), ∑ d ∈ Dset,
          ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b) (blockPrimeInd Nf) X M
                (r d) d (goldCut Ne (k + 1))
            - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b) (blockPrimeInd Nf)
                X M (r d) d (goldCut Ne k)‖ := by
  have hstep : ∀ d ∈ Dset, |goldBandLowDisc Ne z y ε₀ j Nf M a b d (r d)|
      = ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b) (blockPrimeInd Nf) X M
            (r d) d (goldCut Ne (Nat.log 2 Ne + 1))
          - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b) (blockPrimeInd Nf) X M
              (r d) d (goldCut Ne 0)‖ := by
    intro d _
    rw [goldCut_top hNe, goldCut_zero hNe,
      ← goldBandLowDisc_eq_carrier (X := X) (R₀ := r d) hNe hbX,
      Complex.norm_real, Real.norm_eq_abs]
  rw [Finset.sum_congr rfl hstep]
  exact goldWindowDisc_le_annulus_sum Ne (restrictAlpha (blockAlphaLow z y ε₀ j Nf) a b)
    (blockPrimeInd Nf) X M r Dset (Nat.log 2 Ne)

/-! ## Part B — the band close: counts, the crude diagonal, the symmetry split, the three pieces -/

/-- The class×window pair weight on `(p₁, p, q)`: the product `p₁·p·q` meets class `C` and lies in
the window `(lo, hi]`.  Symmetric in `p, q` (`goldCwin_comm`) — the reason the symmetric part's
weight `∑_{p₁} [goldCwin]` is symmetric (drives `sum_symm_ordered_split`). -/
def goldCwin (lo hi : ℕ) (C : ℕ → Prop) (p₁ p q : ℕ) : Prop :=
  C (p₁ * p * q) ∧ lo < p₁ * p * q ∧ p₁ * p * q ≤ hi

lemma goldCwin_comm (lo hi : ℕ) (C : ℕ → Prop) (p₁ a b : ℕ) :
    goldCwin lo hi C p₁ a b = goldCwin lo hi C p₁ b a := by
  unfold goldCwin; rw [mul_right_comm p₁ a b]

open Classical in
/-- **`goldBandCard`** — the band-box count over `goldTripleSet` at class `C`: block-`j` triples
with `Nf < p₃ ≤ M`, `a ≤ p₁p₂ < b` (the window `2 ≤ prod3 ≤ Ne/2` is `goldTripleSet`'s).  Equals
`goldBlockBoxResCount`/`…UnitCount` at the residue/unit class. -/
noncomputable def goldBandCard (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M a b : ℕ) (C : ℕ → Prop) : ℝ :=
  (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ C (prod3 t) ∧
      Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℝ)

open Classical in
/-- **`goldSymCard`** — the symmetric-part count at class `C`: block-`j` triples with `p₂ > Nf`,
`Nf < p₃ ≤ M` (the ordered `(p₂, p₃)`-sum, `m`-range redundant — `goldBandCard_split`). -/
noncomputable def goldSymCard (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M : ℕ) (C : ℕ → Prop) : ℝ :=
  (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ C (prod3 t) ∧
      Nf < t.2.1 ∧ Nf < t.2.2 ∧ t.2.2 ≤ M)).card : ℝ)

open Classical in
/-- **`goldSymRectCount`** — the UNORDERED rectangle count at class `C` and window `(lo, hi]`:
`∑_{p₁} ∑_{(p,q) ∈ S×S} [goldCwin]`, `S = bandLargeSet Ne y Nf M`.  The `½`-image of the symmetric
part (`goldSymCard_two_mul`); BV-priced downstream. -/
noncomputable def goldSymRectCount (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M lo hi : ℕ) (C : ℕ → Prop) : ℝ :=
  ∑ p₁ ∈ bandP1Set Ne z y ε₀ j, ∑ q ∈ bandLargeSet Ne y Nf M ×ˢ bandLargeSet Ne y Nf M,
    (if goldCwin lo hi C p₁ q.1 q.2 then (1 : ℝ) else 0)

open Classical in
/-- **`goldDiagSum`** — the diagonal count at class `C` and window `(lo, hi]`:
`∑_{p₁} ∑_{p ∈ S} [goldCwin p p]` (the `p₂ = p₃` triples).  The other `½`-image; crude. -/
noncomputable def goldDiagSum (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M lo hi : ℕ) (C : ℕ → Prop) : ℝ :=
  ∑ p₁ ∈ bandP1Set Ne z y ε₀ j, ∑ p ∈ bandLargeSet Ne y Nf M,
    (if goldCwin lo hi C p₁ p p then (1 : ℝ) else 0)

open Classical in
/-- **`goldBandDiagCount`** — the `p₂ = p₃` band triples over `goldTripleSet` (the diagonal of the
symmetry split; crude-bounded by `goldBandDiagCount_le`). -/
noncomputable def goldBandDiagCount (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M : ℕ) : ℝ :=
  (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ t.2.1 = t.2.2 ∧
     Nf < t.2.2 ∧ t.2.2 ≤ M)).card : ℝ)

/-! ### The crude diagonal count bound (window-free) -/

open Classical in
/-- **`goldBandDiagCount_le_pairCard` — the diagonal injection.**  Each diagonal band triple
`(p₁, p, p)` is recovered from its projection `(p₁, p₃)`, so `#diag ≤ #(Icc 1 y × Ioc Nf M)`. -/
theorem goldBandDiagCount_le_pairCard (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M : ℕ) :
    goldBandDiagCount Ne z y ε₀ j Nf M ≤ ((Finset.Icc 1 y ×ˢ Finset.Ioc Nf M).card : ℝ) := by
  classical
  unfold goldBandDiagCount
  rw [Nat.cast_le]
  apply Finset.card_le_card_of_injOn (fun t => (t.1, t.2.2))
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter] at ht
    obtain ⟨htri, _hblk, _hdiag, hN, hM⟩ := ht
    rw [goldTripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc] at htri
    obtain ⟨⟨⟨h1lo, _⟩, _, _⟩, _hz, hp1y, _⟩ := htri
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_Ioc]
    exact ⟨⟨h1lo, hp1y⟩, hN, hM⟩
  · intro t ht t' ht' heq
    rw [Finset.mem_coe, Finset.mem_filter] at ht ht'
    obtain ⟨_, _, hdiag, _, _⟩ := ht
    obtain ⟨_, _, hdiag', _, _⟩ := ht'
    rw [Prod.mk.injEq] at heq
    obtain ⟨h1, h3⟩ := heq
    have h2 : t.2.1 = t'.2.1 := by rw [hdiag, h3, ← hdiag']
    exact Prod.ext h1 (Prod.ext h2 h3)

/-- **`goldBandDiagCount_le` — the explicit crude form.**  `#diag ≤ y·(M − Nf)` per box. -/
theorem goldBandDiagCount_le (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M : ℕ) :
    goldBandDiagCount Ne z y ε₀ j Nf M ≤ (y : ℝ) * ((M - Nf : ℕ) : ℝ) := by
  refine (goldBandDiagCount_le_pairCard Ne z y ε₀ j Nf M).trans ?_
  rw [Finset.card_product, Nat.card_Icc, Nat.card_Ioc, show y + 1 - 1 = y from by omega,
    Nat.cast_mul]

/-! ### The symmetry split (instantiates the generic `sum_symm_ordered_split`) -/

open Classical in
/-- **The symmetric-part reindex.**  `goldSymCard` reindexes to the ordered `p₁`-then-`(p₂ ≤ p₃)`
double sum over `bandP1Set × (bandLargeSet)²` filtered by `goldCwin 1 (Ne/2)` (the window
`1 < prod3 ≤ Ne/2` is defeq `goldTripleSet`'s `2 ≤ prod3 ≤ Ne/2`).  Mirrors the twin
`symCard_eq_sum` at the bottom-half window. -/
lemma goldSymCard_eq_sum (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M : ℕ) (C : ℕ → Prop) :
    goldSymCard Ne z y ε₀ j Nf M C
      = ∑ p₁ ∈ bandP1Set Ne z y ε₀ j,
          ∑ q ∈ (bandLargeSet Ne y Nf M ×ˢ bandLargeSet Ne y Nf M).filter (fun q => q.1 ≤ q.2),
            (if goldCwin 1 (Ne / 2) C p₁ q.1 q.2 then (1 : ℝ) else 0) := by
  classical
  unfold goldSymCard
  have hset : (goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ C (prod3 t) ∧
        Nf < t.2.1 ∧ Nf < t.2.2 ∧ t.2.2 ≤ M)
      = (bandP1Set Ne z y ε₀ j ×ˢ
          (bandLargeSet Ne y Nf M ×ˢ bandLargeSet Ne y Nf M).filter (fun q => q.1 ≤ q.2)).filter
          (fun w => goldCwin 1 (Ne / 2) C w.1 w.2.1 w.2.2) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_product, bandP1Set, bandLargeSet, goldTripleSet,
      goldCwin, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hp1i, hp2i, hp3i⟩, hz1, h1y, hy2, h23, hpr1, hpr2, hpr3, hwlo, hwhi⟩,
        hblk, hC, hN2, hN3, h3M⟩
      refine ⟨⟨⟨⟨hp1i.1, hp1i.2⟩, hpr1, hz1, h1y, hblk⟩,
        ⟨⟨⟨hp2i.1, hp2i.2⟩, hpr2, ?_, ?_⟩, ⟨⟨hp3i.1, hp3i.2⟩, hpr3, ?_, h3M⟩⟩, h23⟩,
        hC, hwlo, hwhi⟩
      · exact max_lt hy2 hN2
      · exact le_trans h23 h3M
      · exact max_lt (lt_of_lt_of_le hy2 h23) hN3
    · rintro ⟨⟨⟨⟨hp1i1, hp1i2⟩, hpr1, hz1, h1y, hblk⟩,
        ⟨⟨⟨hp2i1, hp2i2⟩, hpr2, h2max, h2M⟩, ⟨⟨hp3i1, hp3i2⟩, hpr3, h3max, h3M⟩⟩, h23⟩,
        hC, hwlo, hwhi⟩
      exact ⟨⟨⟨⟨hp1i1, hp1i2⟩, ⟨hp2i1, hp2i2⟩, ⟨hp3i1, hp3i2⟩⟩,
        hz1, h1y, lt_of_le_of_lt (le_max_left _ _) h2max, h23, hpr1, hpr2, hpr3, hwlo, hwhi⟩,
        hblk, hC, lt_of_le_of_lt (le_max_right _ _) h2max, lt_of_le_of_lt (le_max_right _ _) h3max,
        h3M⟩
  rw [hset, ← Finset.sum_boole, Finset.sum_product]

open Classical in
/-- **`goldSymCard_two_mul` — the `½`-symmetry split (FULL — consumes `sum_symm_ordered_split`).**
Twice the symmetric part equals the unordered rectangle plus the diagonal:
`2·goldSymCard = goldSymRectCount 1 (Ne/2) + goldDiagSum 1 (Ne/2)`.  Per `p₁` the weight
`w p q = [goldCwin p₁ p q]` is symmetric (`goldCwin_comm`), so the generic `sum_symm_ordered_split`
applies; summing over `p₁ ∈ bandP1Set`. -/
theorem goldSymCard_two_mul (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M : ℕ) (C : ℕ → Prop) :
    2 * goldSymCard Ne z y ε₀ j Nf M C
      = goldSymRectCount Ne z y ε₀ j Nf M 1 (Ne / 2) C
        + goldDiagSum Ne z y ε₀ j Nf M 1 (Ne / 2) C := by
  classical
  rw [goldSymCard_eq_sum, Finset.mul_sum, goldSymRectCount, goldDiagSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p₁ _ => ?_)
  have hsymm : ∀ a b : ℕ, (if goldCwin 1 (Ne / 2) C p₁ a b then (1 : ℝ) else 0)
      = (if goldCwin 1 (Ne / 2) C p₁ b a then (1 : ℝ) else 0) := by
    intro a b; rw [goldCwin_comm 1 (Ne / 2) C p₁ a b]
  have h := sum_symm_ordered_split (bandLargeSet Ne y Nf M)
    (fun a b => if goldCwin 1 (Ne / 2) C p₁ a b then (1 : ℝ) else 0) hsymm
  simpa using h

/-! ### The three-piece cover + the honest-disc decomposition -/

/-- `goldBlockBoxResCount` is `goldBandCard` at the residue class. -/
lemma goldBandCard_eq_ResCount (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M a b d R₀ : ℕ) :
    goldBlockBoxResCount Ne z y ε₀ j Nf M a b d R₀
      = goldBandCard Ne z y ε₀ j Nf M a b
          (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) := by
  unfold goldBlockBoxResCount goldBandCard
  rw [Nat.cast_inj]
  apply congrArg Finset.card
  ext t
  simp only [Finset.mem_filter]

/-- `goldBlockBoxUnitCount` is `goldBandCard` at the unit class. -/
lemma goldBandCard_eq_UnitCount (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M a b d : ℕ) :
    goldBlockBoxUnitCount Ne z y ε₀ j Nf M a b d
      = goldBandCard Ne z y ε₀ j Nf M a b (fun v => IsUnit ((v : ℕ) : ZMod d)) := by
  unfold goldBlockBoxUnitCount goldBandCard
  rw [Nat.cast_inj]
  apply congrArg Finset.card
  ext t
  simp only [Finset.mem_filter]

open Classical in
/-- **`goldBandCard_split` — the three-piece cover (FULL).**  For `1 ≤ z`, `a ≤ z·Nf+1`, and
`Ne/2 + 1 ≤ b`, the band-box count partitions into the symmetric part (`p₂ > Nf`) and the `α_low`
part (`p₂ ≤ Nf`): `goldBandCard = goldSymCard + goldLowCard`.  In the symmetric part the `m`-range
`[a, b)` is redundant (`p₁ ≥ z`, `p₂ ≥ Nf+1` force `p₁p₂ ≥ z·Nf+1 ≥ a`, and `p₁p₂ ≤ prod3 ≤ Ne/2 <
b`).  Mirrors the twin `bandCard_split` at the bottom-half window. -/
theorem goldBandCard_split (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M a b : ℕ) (C : ℕ → Prop)
    (hz : 1 ≤ z) (ha : a ≤ z * Nf + 1) (hb : Ne / 2 + 1 ≤ b) :
    goldBandCard Ne z y ε₀ j Nf M a b C
      = goldSymCard Ne z y ε₀ j Nf M C + goldLowCard Ne z y ε₀ j Nf M a b C := by
  classical
  unfold goldBandCard goldSymCard goldLowCard
  rw [← Nat.cast_add, Nat.cast_inj,
    ← Finset.card_filter_add_card_filter_not
        (s := (goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ C (prod3 t) ∧
          Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b))
        (p := fun t => Nf < t.2.1)]
  congr 1
  · rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
    rw [goldTripleSet, Finset.mem_filter] at ht
    obtain ⟨_, hz1, _h1y, _hy2, h23, _hpr1, _hpr2, _hpr3, _hwlo, hwhi⟩ := ht
    have hp3pos : 1 ≤ t.2.2 := by omega
    constructor
    · rintro ⟨⟨hblk, hC, hN3, h3M, _ham, _hmb⟩, hN2⟩
      exact ⟨hblk, hC, hN2, hN3, h3M⟩
    · rintro ⟨hblk, hC, hN2, hN3, h3M⟩
      have hmul : z * Nf + z ≤ t.1 * t.2.1 := by
        have h1 : z * (Nf + 1) ≤ t.1 * t.2.1 := Nat.mul_le_mul hz1 (by omega)
        rwa [Nat.mul_add, Nat.mul_one] at h1
      have hle : t.1 * t.2.1 ≤ prod3 t := by
        rw [prod3]; exact Nat.le_mul_of_pos_right _ hp3pos
      exact ⟨⟨hblk, hC, hN3, h3M, by omega, by omega⟩, hN2⟩
  · rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr (fun t _ => ?_))
    constructor
    · rintro ⟨⟨hblk, hC, hN3, h3M, ham, hmb⟩, hnN2⟩
      exact ⟨hblk, hC, hN3, h3M, ham, hmb, by omega⟩
    · rintro ⟨hblk, hC, hN3, h3M, ham, hmb, h2N⟩
      exact ⟨⟨hblk, hC, hN3, h3M, ham, hmb⟩, by omega⟩

open Classical in
/-- The symmetric UNORDERED rectangle honest discrepancy (`res − ν·unit`) at the free residue `R₀`
and the full window `(1, Ne/2]`. -/
noncomputable def goldBandSymRectDisc (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M d R₀ : ℕ) : ℝ :=
  goldSymRectCount Ne z y ε₀ j Nf M 1 (Ne / 2)
      (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d))
    - nuChen d * goldSymRectCount Ne z y ε₀ j Nf M 1 (Ne / 2)
        (fun v => IsUnit ((v : ℕ) : ZMod d))

open Classical in
/-- The diagonal honest discrepancy (`res − ν·unit`, `p₂ = p₃`) at the free residue `R₀`. -/
noncomputable def goldBandDiagDisc (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M d R₀ : ℕ) : ℝ :=
  goldDiagSum Ne z y ε₀ j Nf M 1 (Ne / 2)
      (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d))
    - nuChen d * goldDiagSum Ne z y ε₀ j Nf M 1 (Ne / 2)
        (fun v => IsUnit ((v : ℕ) : ZMod d))

/-- `goldSymCard = ½·(rectangle + diagonal)` (halving `goldSymCard_two_mul`). -/
lemma goldSymCard_eq_half (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M : ℕ) (C : ℕ → Prop) :
    goldSymCard Ne z y ε₀ j Nf M C
      = (goldSymRectCount Ne z y ε₀ j Nf M 1 (Ne / 2) C
          + goldDiagSum Ne z y ε₀ j Nf M 1 (Ne / 2) C) / 2 := by
  have := goldSymCard_two_mul Ne z y ε₀ j Nf M C; linarith

open Classical in
/-- **`goldBandDiscW_eq_three` — the band honest disc decomposes into three pieces (FULL).**  For
`1 ≤ z`, the band sub-box honest discrepancy at `a = min(z·Nf+1, Ne/2+1)`, `b = Ne/2+1` is
`½·symRect + ½·diag + low` (`goldBandCard_split` + `goldSymCard_two_mul`, `ν`-linearly).  The
count-level decomposition G-PDIAG's diagonal aggregate consumes. -/
theorem goldBandDiscW_eq_three (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M d R₀ : ℕ) (hz : 1 ≤ z) :
    goldBlockBoxHonestDisc Ne z y ε₀ j Nf M (min (z * Nf + 1) (Ne / 2 + 1)) (Ne / 2 + 1) d R₀
      = (1 / 2) * goldBandSymRectDisc Ne z y ε₀ j Nf M d R₀
        + (1 / 2) * goldBandDiagDisc Ne z y ε₀ j Nf M d R₀
        + goldBandLowDisc Ne z y ε₀ j Nf M (min (z * Nf + 1) (Ne / 2 + 1)) (Ne / 2 + 1) d R₀ := by
  have ha : min (z * Nf + 1) (Ne / 2 + 1) ≤ z * Nf + 1 := min_le_left _ _
  have hb : Ne / 2 + 1 ≤ Ne / 2 + 1 := le_refl _
  unfold goldBlockBoxHonestDisc
  rw [goldBandCard_eq_ResCount, goldBandCard_eq_UnitCount,
    goldBandCard_split Ne z y ε₀ j Nf M (min (z * Nf + 1) (Ne / 2 + 1)) (Ne / 2 + 1)
      (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) hz ha hb,
    goldBandCard_split Ne z y ε₀ j Nf M (min (z * Nf + 1) (Ne / 2 + 1)) (Ne / 2 + 1)
      (fun v => IsUnit ((v : ℕ) : ZMod d)) hz ha hb,
    goldSymCard_eq_half Ne z y ε₀ j Nf M (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)),
    goldSymCard_eq_half Ne z y ε₀ j Nf M (fun v => IsUnit ((v : ℕ) : ZMod d))]
  unfold goldBandSymRectDisc goldBandDiagDisc goldBandLowDisc
  ring

/-! ## Part C — the symmetric rectangle identification (`max(y,Nf) < p₂,p₃ ≤ M`, unordered) -/

open Classical in
/-- Restatement of the private twin `summand_eq_sym`: the `apDiscBilinCutoff` summand at the
symmetric coefficient is the `symPairPred` `0/1` indicator (carrier-agnostic — reuses
`blockAlphaSym`). -/
private lemma gold_summand_sym (z y : ℕ) (ε₀ : ℝ) (j Nf M : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (q : ℕ × ℕ) :
    (if P (q.1 * q.2) then
        blockAlphaSym z y ε₀ j Nf M q.1 * blockPrimeInd (max y Nf) q.2 else (0 : ℂ))
      = (if symPairPred z y ε₀ j Nf M P q then (1 : ℂ) else 0) := by
  classical
  unfold symPairPred blockAlphaSym blockPrimeInd
  by_cases hP : P (q.1 * q.2)
  · by_cases hf : (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ max y Nf < p₂ ∧ p₂ ≤ M ∧
        p₁ * p₂ = q.1 ∧ blockIdx z ε₀ p₁ = j)
    · by_cases hn : max y Nf < q.2 ∧ q.2.Prime
      · rw [if_pos hP, if_pos hf, if_pos hn, if_pos ⟨hP, hf, hn⟩, mul_one]
      · rw [if_pos hP, if_pos hf, if_neg hn, mul_zero, if_neg (fun h => hn h.2.2)]
    · rw [if_pos hP, if_neg hf, zero_mul, if_neg (fun h => hf h.2.1)]
  · rw [if_neg hP, if_neg (fun h => hP h.1)]

open Classical in
/-- Restatement of the private twin `pairTerm_eq_sym`: the symmetric double sum counts the
`symPairPred` pairs. -/
private lemma gold_pairTerm_sym (z y : ℕ) (ε₀ : ℝ) (j Nf M X : ℕ) (P : ℕ → Prop)
    [DecidablePred P] :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 M,
        if P (m * n) then
          blockAlphaSym z y ε₀ j Nf M m * blockPrimeInd (max y Nf) n else (0 : ℂ))
      = (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
            (fun q => symPairPred z y ε₀ j Nf M P q)).card : ℂ) := by
  classical
  rw [← Finset.sum_product']
  rw [Finset.sum_congr rfl (fun q _ => gold_summand_sym z y ε₀ j Nf M P q)]
  rw [Finset.sum_boole]

open Classical in
/-- **`goldSymRectCount_eq_card`** — the symmetric rectangle count as a product-filter cardinality
(the `goldSymRectCount` double sum is the card of the filtered `bandP1Set × (bandLargeSet)²`). -/
theorem goldSymRectCount_eq_card (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M lo hi : ℕ) (C : ℕ → Prop) :
    goldSymRectCount Ne z y ε₀ j Nf M lo hi C
      = (((bandP1Set Ne z y ε₀ j ×ˢ (bandLargeSet Ne y Nf M ×ˢ bandLargeSet Ne y Nf M)).filter
          (fun w => goldCwin lo hi C w.1 w.2.1 w.2.2)).card : ℝ) := by
  classical
  unfold goldSymRectCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p₁ _ => ?_)
  refine Finset.sum_congr rfl (fun pq _ => ?_)
  by_cases h : goldCwin lo hi C p₁ pq.1 pq.2 <;> simp [h]

open Classical in
/-- **`goldSymBox_pair_card` — the symmetric-rectangle pair bijection over `goldTripleSet`
(UNORDERED).**  The windowed `symPairPred` pairs `(m, n)` biject with the block-`j` unordered
triples `(p₁, (p, q))` (`p, q ∈ S = (max(y,Nf), M]`) via `(p₁, (p, q)) ↦ (p₁·p, q)`; injectivity is
oriented-factorization uniqueness (`p₁ ≤ y < p`).  The window `(Tlo, Thi]` supplies the box bounds
via `hThiX : Thi ≤ X`, `hThiNe : Thi ≤ Ne`. -/
theorem goldSymBox_pair_card {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M X : ℕ} (C : ℕ → Prop)
    (Tlo Thi : ℕ) (hThiX : Thi ≤ X) (hThiNe : Thi ≤ Ne) :
    (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
        (fun q => symPairPred z y ε₀ j Nf M (fun v => Tlo < v ∧ v ≤ Thi ∧ C v) q)).card)
      = (((bandP1Set Ne z y ε₀ j ×ˢ (bandLargeSet Ne y Nf M ×ˢ bandLargeSet Ne y Nf M)).filter
          (fun w => goldCwin Tlo Thi C w.1 w.2.1 w.2.2)).card) := by
  classical
  symm
  apply Finset.card_bij (fun w _ => (w.1 * w.2.1, w.2.2))
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_product, bandP1Set, bandLargeSet, Finset.mem_Icc,
      goldCwin] at hw
    obtain ⟨⟨⟨⟨hp1lo, hp1hi⟩, hp1prime, hzp1, hp1y, hblk⟩,
             ⟨⟨hplo, _hphi⟩, hpprime, hpmax, hpM⟩,
             ⟨hqlo, _hqhi⟩, hqprime, hqmax, hqM⟩,
            hC, hwlo, hwhi⟩ := hw
    have hmle : w.1 * w.2.1 ≤ Thi := le_trans (Nat.le_mul_of_pos_right (w.1 * w.2.1) hqlo) hwhi
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨Nat.mul_pos hp1lo hplo, le_trans hmle hThiX⟩, ⟨hqlo, hqM⟩⟩,
      ⟨hwlo, hwhi, hC⟩,
      ⟨w.1, w.2.1, hp1prime, hpprime, hzp1, hp1y, hpmax, hpM, rfl, hblk⟩, hqmax, hqprime⟩
  · intro w hw w' hw' heq
    simp only [Finset.mem_filter, Finset.mem_product, bandP1Set, bandLargeSet, Finset.mem_Icc,
      goldCwin] at hw hw'
    obtain ⟨⟨⟨_, hp1prime, _, hp1y, _⟩, ⟨_, hpprime, hpmax, _⟩, _⟩, _⟩ := hw
    obtain ⟨⟨⟨_, hp1prime', _, _, _⟩, ⟨_, hpprime', hpmax', _⟩, _⟩, _⟩ := hw'
    rw [Prod.mk.injEq] at heq
    obtain ⟨hmeq, hqeq⟩ := heq
    have hyp : y < w'.2.1 := lt_of_le_of_lt (le_max_left y Nf) hpmax'
    obtain ⟨he1, he2⟩ := gold_pair_unique_bi hp1prime hp1prime' hpprime' hp1y hyp hmeq
    exact Prod.ext_iff.mpr ⟨he1, Prod.ext_iff.mpr ⟨he2, hqeq⟩⟩
  · intro qp hqp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hqp
    obtain ⟨⟨⟨_hqp1lo, _hqp1hi⟩, hqp2lo, hqp2hi⟩, hpp⟩ := hqp
    obtain ⟨⟨hwlo0, hwhi0, hC0⟩,
      ⟨p₁, p₂, hp1prime, hp2prime, hzp1, hp1y, hp2max, hp2M, hprod, hblk⟩,
      hnmax, hnprime⟩ := hpp
    have hqp1pos : 0 < qp.1 := by
      rcases Nat.eq_zero_or_pos qp.1 with h | h
      · rw [h, zero_mul] at hwlo0; omega
      · exact h
    have hqp2pos : 0 < qp.2 := hqp2lo
    have hprodeq : p₁ * p₂ * qp.2 = qp.1 * qp.2 := by rw [hprod]
    have hqp1N : qp.1 ≤ Ne :=
      le_trans (le_trans (Nat.le_mul_of_pos_right qp.1 hqp2pos) hwhi0) hThiNe
    have hqp2N : qp.2 ≤ Ne :=
      le_trans (le_trans (Nat.le_mul_of_pos_left qp.2 hqp1pos) hwhi0) hThiNe
    have hp1le : p₁ ≤ qp.1 := by rw [← hprod]; exact Nat.le_mul_of_pos_right p₁ hp2prime.pos
    have hp2le : p₂ ≤ qp.1 := by rw [← hprod]; exact Nat.le_mul_of_pos_left p₂ hp1prime.pos
    refine ⟨(p₁, p₂, qp.2), ?_, Prod.ext_iff.mpr ⟨hprod, rfl⟩⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · rw [bandP1Set, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hp1prime.pos, le_trans hp1le hqp1N⟩, hp1prime, hzp1, hp1y, hblk⟩
      · rw [Finset.mem_product]
        refine ⟨?_, ?_⟩
        · rw [bandLargeSet, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hp2prime.pos, le_trans hp2le hqp1N⟩, hp2prime, hp2max, hp2M⟩
        · rw [bandLargeSet, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hnprime.pos, hqp2N⟩, hnprime, hnmax, hqp2hi⟩
    · rw [goldCwin]
      exact ⟨by rw [hprodeq]; exact hC0, by rw [hprodeq]; exact hwlo0, by rw [hprodeq]; exact hwhi0⟩

open Classical in
/-- **`gold_cutoffDiff_sym` — the general-cutoff symmetric difference is the windowed pair count.**
The symmetric mirror of `gold_cutoffDiff_low`: the `(Tlo, Thi]` cutoff difference folds the annulus
into the class predicate; `gold_pairTerm_sym` counts the survivors. -/
private lemma gold_cutoffDiff_sym (z y : ℕ) (ε₀ : ℝ) (j Nf M X : ℕ)
    (P : ℕ → Prop) [DecidablePred P] (Tlo Thi : ℕ) (hT : Tlo ≤ Thi) :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
        if P (m * n) then
          blockAlphaSym z y ε₀ j Nf M m * blockPrimeInd (max y Nf) n else (0 : ℂ))
      - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
        if P (m * n) then
          blockAlphaSym z y ε₀ j Nf M m * blockPrimeInd (max y Nf) n else (0 : ℂ))
      = (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
          (fun q => symPairPred z y ε₀ j Nf M
            (fun v => Tlo < v ∧ v ≤ Thi ∧ P v) q)).card : ℂ) := by
  classical
  rw [← gold_pairTerm_sym z y ε₀ j Nf M X (fun v => Tlo < v ∧ v ≤ Thi ∧ P v),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hP : P (m * n)
  · by_cases hx : m * n ≤ Thi
    · by_cases hlo : m * n ≤ Tlo
      · have hnw : ¬ (Tlo < m * n ∧ m * n ≤ Thi ∧ P (m * n)) := fun ⟨hw, _, _⟩ => by omega
        rw [if_pos hx, if_pos hlo, sub_self, if_neg hnw]
      · rw [if_pos hx, if_neg hlo, sub_zero, if_pos hP,
          if_pos (show Tlo < m * n ∧ m * n ≤ Thi ∧ P (m * n) from ⟨by omega, hx, hP⟩)]
    · have hlo : ¬ m * n ≤ Tlo := by omega
      have hnw : ¬ (Tlo < m * n ∧ m * n ≤ Thi ∧ P (m * n)) := fun ⟨_, hw, _⟩ => by omega
      rw [if_neg hx, if_neg hlo, sub_self, if_neg hnw]
  · have hnw : ¬ (Tlo < m * n ∧ m * n ≤ Thi ∧ P (m * n)) := fun ⟨_, _, hp⟩ => hP hp
    simp only [if_neg hP, if_neg hnw, ite_self, sub_self]

open Classical in
/-- **`goldSymRect_windowDisc_eq` — the symmetric identification at a FREE residue and GENERAL
cutoffs.**  The unordered rectangle's honest disc IS the cutoff-carrier difference at `(Tlo, Thi]`,
at the coefficient `blockAlphaSym j Nf M` with `β = blockPrimeInd (max y Nf)` over the `β`-range.
NO ordering (the point of the unordered double count).  Produces `goldSymRectCount` at `(Tlo, Thi]`
directly.  Requires `Thi ≤ X`, `Thi ≤ Ne` (the box/ambient bounds). -/
theorem goldSymRect_windowDisc_eq {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M X d R₀ : ℕ}
    (Tlo Thi : ℕ) (hT : Tlo ≤ Thi) (hThiX : Thi ≤ X) (hThiNe : Thi ≤ Ne) :
    apDiscBilinCutoff (blockAlphaSym z y ε₀ j Nf M) (blockPrimeInd (max y Nf)) X M R₀ d Thi
      - apDiscBilinCutoff (blockAlphaSym z y ε₀ j Nf M) (blockPrimeInd (max y Nf)) X M R₀ d Tlo
      = ((goldSymRectCount Ne z y ε₀ j Nf M Tlo Thi
            (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) : ℝ) : ℂ)
        - (1 / (d.totient : ℂ)) *
          ((goldSymRectCount Ne z y ε₀ j Nf M Tlo Thi
            (fun v => IsUnit ((v : ℕ) : ZMod d)) : ℝ) : ℂ) := by
  classical
  have hRes :
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            blockAlphaSym z y ε₀ j Nf M m * blockPrimeInd (max y Nf) n else 0)
        - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            blockAlphaSym z y ε₀ j Nf M m * blockPrimeInd (max y Nf) n else 0)
        = ((goldSymRectCount Ne z y ε₀ j Nf M Tlo Thi
            (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) : ℝ) : ℂ) := by
    rw [gold_cutoffDiff_sym z y ε₀ j Nf M X
      (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) Tlo Thi hT,
      goldSymBox_pair_card (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) Tlo Thi hThiX hThiNe,
      goldSymRectCount_eq_card]
    norm_cast
  have hUnit :
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
          if IsUnit ((m * n : ℕ) : ZMod d) then
            blockAlphaSym z y ε₀ j Nf M m * blockPrimeInd (max y Nf) n else 0)
        - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
          if IsUnit ((m * n : ℕ) : ZMod d) then
            blockAlphaSym z y ε₀ j Nf M m * blockPrimeInd (max y Nf) n else 0)
        = ((goldSymRectCount Ne z y ε₀ j Nf M Tlo Thi
            (fun v => IsUnit ((v : ℕ) : ZMod d)) : ℝ) : ℂ) := by
    rw [gold_cutoffDiff_sym z y ε₀ j Nf M X (fun v => IsUnit ((v : ℕ) : ZMod d)) Tlo Thi hT,
      goldSymBox_pair_card (fun v => IsUnit ((v : ℕ) : ZMod d)) Tlo Thi hThiX hThiNe,
      goldSymRectCount_eq_card]
    norm_cast
  have hexpx : apDiscBilinCutoff (blockAlphaSym z y ε₀ j Nf M) (blockPrimeInd (max y Nf)) X M R₀ d
        Thi
      = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            blockAlphaSym z y ε₀ j Nf M m * blockPrimeInd (max y Nf) n else 0)
        - (1 / (d.totient : ℂ)) *
          (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
            if IsUnit ((m * n : ℕ) : ZMod d) then
              blockAlphaSym z y ε₀ j Nf M m * blockPrimeInd (max y Nf) n else 0) :=
    rfl
  have hexplo : apDiscBilinCutoff (blockAlphaSym z y ε₀ j Nf M) (blockPrimeInd (max y Nf)) X M R₀ d
        Tlo
      = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            blockAlphaSym z y ε₀ j Nf M m * blockPrimeInd (max y Nf) n else 0)
        - (1 / (d.totient : ℂ)) *
          (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
            if IsUnit ((m * n : ℕ) : ZMod d) then
              blockAlphaSym z y ε₀ j Nf M m * blockPrimeInd (max y Nf) n else 0) :=
    rfl
  rw [hexpx, hexplo]
  rw [show ∀ (r1 u1 r2 u2 : ℂ),
      (r1 - (1 / (d.totient : ℂ)) * u1) - (r2 - (1 / (d.totient : ℂ)) * u2)
        = (r1 - r2) - (1 / (d.totient : ℂ)) * (u1 - u2) from fun r1 u1 r2 u2 => by ring]
  rw [hRes, hUnit]

open Classical in
/-- **`goldSymRect_eq` — the symmetric identification at the dyadic annulus (byte-lock for G-SW2).**
The `goldSymRect_windowDisc_eq` instance at `(goldCut Ne k, goldCut Ne (k+1)]`; the box bound
`hNeX : Ne/2 ≤ X` covers every annulus (`goldCut ≤ Ne/2`). -/
theorem goldSymRect_eq {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M X d R₀ : ℕ} (hNeX : Ne / 2 ≤ X) (k : ℕ) :
    apDiscBilinCutoff (blockAlphaSym z y ε₀ j Nf M) (blockPrimeInd (max y Nf)) X M R₀ d
        (goldCut Ne (k + 1))
      - apDiscBilinCutoff (blockAlphaSym z y ε₀ j Nf M) (blockPrimeInd (max y Nf)) X M R₀ d
          (goldCut Ne k)
      = ((goldSymRectCount Ne z y ε₀ j Nf M (goldCut Ne k) (goldCut Ne (k + 1))
            (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) : ℝ) : ℂ)
        - (1 / (d.totient : ℂ)) *
          ((goldSymRectCount Ne z y ε₀ j Nf M (goldCut Ne k) (goldCut Ne (k + 1))
            (fun v => IsUnit ((v : ℕ) : ZMod d)) : ℝ) : ℂ) :=
  goldSymRect_windowDisc_eq (goldCut Ne k) (goldCut Ne (k + 1)) (goldCut_mono Ne (Nat.le_succ k))
    (le_trans (goldCut_le_half Ne (k + 1)) hNeX)
    (le_trans (goldCut_le_half Ne (k + 1)) (Nat.div_le_self Ne 2))

open Classical in
/-- **`goldBandSymRectDisc_eq_carrier` — the full-window symmetric identification.**  The symmetric
honest disc IS the cutoff-carrier difference at the whole window `(1, Ne/2]`
(`goldSymRect_windowDisc_eq` at `Tlo = 1`, `Thi = Ne/2`). -/
theorem goldBandSymRectDisc_eq_carrier {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M X d R₀ : ℕ}
    (hNe : 2 ≤ Ne) (hNeX : Ne / 2 ≤ X) :
    ((goldBandSymRectDisc Ne z y ε₀ j Nf M d R₀ : ℝ) : ℂ)
      = apDiscBilinCutoff (blockAlphaSym z y ε₀ j Nf M) (blockPrimeInd (max y Nf)) X M R₀ d (Ne / 2)
        - apDiscBilinCutoff (blockAlphaSym z y ε₀ j Nf M) (blockPrimeInd (max y Nf)) X M R₀ d
            1 := by
  have hhalf : (1 : ℕ) ≤ Ne / 2 := by omega
  rw [goldSymRect_windowDisc_eq (X := X) 1 (Ne / 2) hhalf hNeX (Nat.div_le_self Ne 2),
    goldBandSymRectDisc, nuChen_apply]
  push_cast
  ring

/-- **`goldBandSymRectDisc_le_annulus_sum` — the consumable symmetric price (byte-lock for G-SW2).**
The `Dset`-sum of symmetric honest discrepancies is bounded by the `(annulus × Dset)` double sum of
the per-annulus carrier differences (`goldBandSymRectDisc_eq_carrier` + the generic telescope). -/
theorem goldBandSymRectDisc_le_annulus_sum {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M X : ℕ}
    (r : ℕ → ℕ) (Dset : Finset ℕ)
    (hNe : 2 ≤ Ne) (hNeX : Ne / 2 ≤ X) :
    (∑ d ∈ Dset, |goldBandSymRectDisc Ne z y ε₀ j Nf M d (r d)|)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 Ne + 1), ∑ d ∈ Dset,
          ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j Nf M) (blockPrimeInd (max y Nf)) X M
                (r d) d (goldCut Ne (k + 1))
            - apDiscBilinCutoff (blockAlphaSym z y ε₀ j Nf M) (blockPrimeInd (max y Nf)) X M
                (r d) d (goldCut Ne k)‖ := by
  have hstep : ∀ d ∈ Dset, |goldBandSymRectDisc Ne z y ε₀ j Nf M d (r d)|
      = ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j Nf M) (blockPrimeInd (max y Nf)) X M
            (r d) d (goldCut Ne (Nat.log 2 Ne + 1))
          - apDiscBilinCutoff (blockAlphaSym z y ε₀ j Nf M) (blockPrimeInd (max y Nf)) X M
              (r d) d (goldCut Ne 0)‖ := by
    intro d _
    rw [goldCut_top hNe, goldCut_zero hNe,
      ← goldBandSymRectDisc_eq_carrier (X := X) (R₀ := r d) hNe hNeX,
      Complex.norm_real, Real.norm_eq_abs]
  rw [Finset.sum_congr rfl hstep]
  exact goldWindowDisc_le_annulus_sum Ne (blockAlphaSym z y ε₀ j Nf M)
    (blockPrimeInd (max y Nf)) X M r Dset (Nat.log 2 Ne)

/-! ## Composition sanity — the named deliverables elaborate

The band identifications (`goldLowRect_eq`, `goldSymRect_eq`) feed G-SW2's `box_disc_three_way`
pricing per annulus; the band close (`goldBandCard_split`, `goldSymCard_two_mul`,
`goldBandDiagCount_le`, `goldBandDiscW_eq_three`) feeds G-PDIAG's diagonal aggregate, whose residue
leg consumes `Band.gold_diag_residue_crumb` at the reflected class `crtClassG`. -/

section CompositionSanity

#check @Salt.Goldbach.goldLowRect_eq
#check @Salt.Goldbach.goldSymRect_eq
#check @Salt.Goldbach.goldBandCard_split
#check @Salt.Goldbach.goldSymCard_two_mul
#check @Salt.Goldbach.goldBandDiagCount_le
#check @Salt.Goldbach.goldBandDiscW_eq_three
#check @Salt.Goldbach.goldBandLowDisc_le_annulus_sum
#check @Salt.Goldbach.goldBandSymRectDisc_le_annulus_sum
#check @Salt.Chen.sum_symm_ordered_split
#check @Salt.Goldbach.gold_diag_residue_crumb

end CompositionSanity

end Salt.Goldbach
