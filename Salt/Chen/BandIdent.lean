/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.BandClose

/-!
# BND3 — the band rectangle identifications (the switch line's last combinatorial node)

Design: `docs/blueprints/flags.md`, the `2026-07-14 BND2 … the identifications = BND3` entry and
the `★ CATCH #57 ★` + FABLE ADJUDICATION paragraphs (the frozen three-piece design).  This file
discharges the two HONEST RESIDUALS `BandClose.Plo_discharge` names — turning the two BV-priced
band rectangles (`bandLowDisc`, `bandSymRectDisc`) into `apDiscBilinCutoff` T-differences, the
objects `WindowClose.general_BV_cutoff_final` prices.

The pattern mirrors `WindowSW.blockBox_windowDisc_eq` (the window-in-carrier identification), but
with the ordering supplied by the SPLIT structure rather than the corner `hord`:

## 1. The low rectangle (FLOOR A — ordering automatic)

`blockAlphaLow z y ε₀ j N` is the `0/1` indicator of `m = p₁p₂` with `p₁` in block `j` and
`y < p₂ ≤ N` (the oriented factorization `p₁ ≤ y < p₂` pins `(p₁, p₂)` by unique factorization; the
`p₂ ≤ N` cap is an intrinsic property of the pair).  `lowRect_eq_apDiscBilinCutoff`:
`bandLowDisc` = the `apDiscBilinCutoff` T-difference at `(restrictAlpha (blockAlphaLow …) a b,
blockPrimeInd N)` — the ordering `p₂ ≤ N < p₃` is AUTOMATIC (no `hord`), the `m`-range `[zN+1, x+1)`
carried by `restrictAlpha` (per BND2's finding that the threshold genuinely cuts on the low region).

## 2. The symmetric rectangle (FLOOR B — the unordered double count)

`blockAlphaSym z y ε₀ j N M` is the indicator of `m = p₁p₂` with `p₁` in block `j` and
`max(y, N) < p₂ ≤ M`.  `symRect_eq_apDiscBilinCutoff`: `bandSymRectDisc` (the UNORDERED
both-in-range double count minus its `ν`-main) = the `apDiscBilinCutoff` T-difference at
`(blockAlphaSym, blockPrimeInd (max y N))` over the `β`-range `(max(y, N), M]`.  NO ordering
(the point of the unordered rectangle); no `m`-range restriction (the symmetric region makes it
redundant, `BandClose.bandCard_split`).

## 3. The composed `Plo_discharge_priced` (FULL)

`BandClose.Plo_discharge` with `Psym`/`Plow` instantiated at `general_BV_cutoff_final`-priceable
forms: the `∑_d` of the two identifications' one-sided norms (the per-box price shape of
`WindowClose.hHD_of_generalBV_window`), assembled through the per-`(k, d)` cutoff triangle.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part 0 — the oriented-factorization uniqueness kernel (re-proof) -/

/-- Re-proof of `PairBijection.prime_pair_unique` (private there): the oriented `m ↦ {p₁, p₂}`
factorization at `y` is unique.  The injectivity kernel of both band rectangle bijections. -/
private lemma prime_pair_unique_ident {y p₁ p₂ p₁' p₂' : ℕ}
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

/-! ## Part A — the low rectangle (`p₂ ≤ N`, ordering automatic) -/

open Classical in
/-- **The low-band semiprime indicator** `blockAlphaLow j N m = [m = p₁·p₂, p₁ in block j,
z ≤ p₁ ≤ y < p₂ ≤ N]` — `blockAlpha` with the `p₂ ≤ N` cap added (the α_low part, `p₂ ≤ N < p₃`).
Still `0/1` (unique factorization pins `(p₁, p₂)`). -/
noncomputable def blockAlphaLow (z y : ℕ) (ε₀ : ℝ) (j N m : ℕ) : ℂ :=
  if (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧ p₂ ≤ N ∧ p₁ * p₂ = m
      ∧ blockIdx z ε₀ p₁ = j) then 1 else 0

/-- **`‖blockAlphaLow‖ ≤ 1`.**  The `0/1`-valued `hα` input for `general_BV_cutoff_final`. -/
theorem norm_blockAlphaLow_le_one (z y : ℕ) (ε₀ : ℝ) (j N m : ℕ) :
    ‖blockAlphaLow z y ε₀ j N m‖ ≤ 1 := by
  unfold blockAlphaLow
  split_ifs <;> simp

/-- The `(m, n)`-pair predicate for the low rectangle: `m` carries `blockAlphaLow`-weight `1`
(the oriented semiprime with `p₂ ≤ N`), `n` is a `(N, M]`-prime, `m ∈ [a, b)`, and `P(m·n)`. -/
def lowPairPred (z y : ℕ) (ε₀ : ℝ) (j N a b : ℕ) (P : ℕ → Prop) (q : ℕ × ℕ) : Prop :=
  P (q.1 * q.2) ∧ (a ≤ q.1 ∧ q.1 < b) ∧
    (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧ p₂ ≤ N ∧ p₁ * p₂ = q.1 ∧
      blockIdx z ε₀ p₁ = j) ∧ (N < q.2 ∧ q.2.Prime)

open Classical in
/-- The `apDiscBilinCutoff` summand for the low rectangle is the `lowPairPred` `0/1` indicator. -/
private lemma summand_eq_low (z y : ℕ) (ε₀ : ℝ) (j N a b : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (q : ℕ × ℕ) :
    (if P (q.1 * q.2) then
        restrictAlpha (blockAlphaLow z y ε₀ j N) a b q.1 * blockPrimeInd N q.2 else (0 : ℂ))
      = (if lowPairPred z y ε₀ j N a b P q then (1 : ℂ) else 0) := by
  classical
  unfold lowPairPred restrictAlpha blockAlphaLow blockPrimeInd
  by_cases hP : P (q.1 * q.2)
  · by_cases hbox : a ≤ q.1 ∧ q.1 < b
    · by_cases hf : (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧ p₂ ≤ N ∧
          p₁ * p₂ = q.1 ∧ blockIdx z ε₀ p₁ = j)
      · by_cases hn : N < q.2 ∧ q.2.Prime
        · rw [if_pos hP, if_pos hbox, if_pos hf, if_pos hn, if_pos ⟨hP, hbox, hf, hn⟩, mul_one]
        · rw [if_pos hP, if_pos hbox, if_pos hf, if_neg hn, mul_zero,
            if_neg (fun h => hn h.2.2.2)]
      · rw [if_pos hP, if_pos hbox, if_neg hf, zero_mul, if_neg (fun h => hf h.2.2.1)]
    · rw [if_pos hP, if_neg hbox, zero_mul, if_neg (fun h => hbox h.2.1)]
  · rw [if_neg hP, if_neg (fun h => hP h.1)]

open Classical in
/-- The low-rectangle double sum counts the `lowPairPred` pairs. -/
private lemma pairTerm_eq_low (z y : ℕ) (ε₀ : ℝ) (j N a b X M : ℕ) (P : ℕ → Prop)
    [DecidablePred P] :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 M,
        if P (m * n) then
          restrictAlpha (blockAlphaLow z y ε₀ j N) a b m * blockPrimeInd N n else (0 : ℂ))
      = (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
            (fun q => lowPairPred z y ε₀ j N a b P q)).card : ℂ) := by
  classical
  rw [← Finset.sum_product']
  rw [Finset.sum_congr rfl (fun q _ => summand_eq_low z y ε₀ j N a b P q)]
  rw [Finset.sum_boole]

open Classical in
/-- **`lowBox_pair_card` — the low-rectangle pair bijection (ordering AUTOMATIC).**  The analogue of
`WindowSW.blockBox_windowed_pair_card` with the `p₂ ≤ N` cap baked into the coefficient
(`blockAlphaLow`), so the ordering `p₂ ≤ N < p₃` needs NO `hord`: the surjectivity branch derives
`p₂ ≤ p₃` directly from `p₂ ≤ N < q.2`.  The window comes from `hPwin` (the cutoff). -/
theorem lowBox_pair_card {x z y : ℕ} {ε₀ : ℝ} {j N M a b X : ℕ}
    (P : ℕ → Prop) [DecidablePred P]
    (hbX : b ≤ X + 1)
    (hPwin : ∀ v : ℕ, P v → x / 2 + 2 ≤ v ∧ v ≤ x) :
    (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter (fun q => lowPairPred z y ε₀ j N a b P q)).card)
      = (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ P (prod3 t) ∧
          N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧ t.2.1 ≤ N)).card) := by
  classical
  symm
  apply Finset.card_bij (fun t _ => (t.1 * t.2.1, t.2.2))
  · intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htri, hblk, hP, hNlt, hMle, hab_lo, hab_hi, hp2N⟩ := ht
    rw [tripleSet, Finset.mem_filter] at htri
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
    rw [tripleSet, Finset.mem_filter] at htri htri'
    obtain ⟨_, _, hp1y, _, _, hp1prime, _, _, _, _⟩ := htri
    obtain ⟨_, _, _, hyp2', _, hp1prime', hp2prime', _, _, _⟩ := htri'
    rw [Prod.mk.injEq] at heq
    obtain ⟨hmeq, hneq⟩ := heq
    obtain ⟨he1, he2⟩ := prime_pair_unique_ident hp1prime hp1prime' hp2prime' hp1y hyp2' hmeq
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
    have hq1x : q.1 ≤ x := le_trans (Nat.le_mul_of_pos_right q.1 (by omega)) hwhi
    have hq2x : q.2 ≤ x := le_trans (Nat.le_mul_of_pos_left q.2 (by omega)) hwhi
    have hp1le : p₁ ≤ q.1 := by rw [← hprod]; exact Nat.le_mul_of_pos_right p₁ hp2prime.pos
    have hp2le : p₂ ≤ q.1 := by rw [← hprod]; exact Nat.le_mul_of_pos_left p₂ hp1prime.pos
    refine ⟨(p₁, p₂, q.2), ?_, Prod.ext_iff.mpr ⟨hprod, rfl⟩⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hblk, ?_, hNq2, hq2hi, ?_, ?_, hp2N⟩
    · rw [tripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
      refine ⟨⟨⟨hp1prime.pos, le_trans hp1le hq1x⟩, ⟨hp2prime.pos, le_trans hp2le hq1x⟩,
          ⟨hq2prime.pos, hq2x⟩⟩,
        hzp1, hp1y, hyp2, hord3, hp1prime, hp2prime, hq2prime, ?_, ?_⟩
      · rw [hprod3]; exact hwlo
      · rw [hprod3]; exact hwhi
    · rw [hprod3]; exact hP
    · change a ≤ p₁ * p₂
      rw [hprod]; exact ha_lo
    · change p₁ * p₂ < b
      rw [hprod]; exact ha_hi

open Classical in
/-- The low-rectangle cutoff difference equals the windowed `lowPairPred` pair count. -/
private lemma cutoffDiff_eq_pairCard_low (x z y : ℕ) (ε₀ : ℝ) (j N a b X M : ℕ)
    (P : ℕ → Prop) [DecidablePred P] (hxlo : x / 2 + 1 ≤ x) :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
        if P (m * n) then
          restrictAlpha (blockAlphaLow z y ε₀ j N) a b m * blockPrimeInd N n else (0 : ℂ))
      - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
        if P (m * n) then
          restrictAlpha (blockAlphaLow z y ε₀ j N) a b m * blockPrimeInd N n else (0 : ℂ))
      = (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
          (fun q => lowPairPred z y ε₀ j N a b
            (fun v => x / 2 + 2 ≤ v ∧ v ≤ x ∧ P v) q)).card : ℂ) := by
  classical
  rw [← pairTerm_eq_low z y ε₀ j N a b X M (fun v => x / 2 + 2 ≤ v ∧ v ≤ x ∧ P v),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hP : P (m * n)
  · by_cases hx : m * n ≤ x
    · by_cases hlo : m * n ≤ x / 2 + 1
      · have hnw : ¬ (x / 2 + 2 ≤ m * n ∧ m * n ≤ x ∧ P (m * n)) := fun ⟨hw, _, _⟩ => by omega
        rw [if_pos hx, if_pos hlo, sub_self, if_neg hnw]
      · rw [if_pos hx, if_neg hlo, sub_zero, if_pos hP,
          if_pos (show x / 2 + 2 ≤ m * n ∧ m * n ≤ x ∧ P (m * n) from ⟨by omega, hx, hP⟩)]
    · have hlo : ¬ m * n ≤ x / 2 + 1 := by omega
      have hnw : ¬ (x / 2 + 2 ≤ m * n ∧ m * n ≤ x ∧ P (m * n)) := fun ⟨_, hw, _⟩ => by omega
      rw [if_neg hx, if_neg hlo, sub_self, if_neg hnw]
  · have hnw : ¬ (x / 2 + 2 ≤ m * n ∧ m * n ≤ x ∧ P (m * n)) := fun ⟨_, _, hp⟩ => hP hp
    simp only [if_neg hP, if_neg hnw, ite_self, sub_self]

open Classical in
/-- **`lowRect_eq_apDiscBilinCutoff` — the low-band identification (FLOOR A, FULL).**  The α_low
rectangle's honest discrepancy IS the difference of the two one-sided cutoff carriers at `T = x` and
`T = x/2+1`, at the decided coefficient `restrictAlpha (blockAlphaLow j N) a b` (the `m`-range
`[a, b)` carried explicitly, the threshold cuts on the low region) with `β = blockPrimeInd N`.  NO
`hord`: the ordering `p₂ ≤ N < p₃` is automatic (`lowBox_pair_card`).  Mirrors
`WindowSW.blockBox_windowDisc_eq`, corner- and `hord`-free. -/
theorem lowRect_eq_apDiscBilinCutoff {x z y : ℕ} {ε₀ : ℝ} {j N M a b X d R₀ : ℕ}
    (hbX : b ≤ X + 1) (hxlo : x / 2 + 1 ≤ x) :
    apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j N) a b) (blockPrimeInd N) X M R₀ d x
      - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j N) a b) (blockPrimeInd N) X M R₀ d
          (x / 2 + 1)
      = ((lowCard x z y ε₀ j N M a b (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) : ℝ) : ℂ)
        - (1 / (d.totient : ℂ)) *
          ((lowCard x z y ε₀ j N M a b (fun v => IsUnit ((v : ℕ) : ZMod d)) : ℝ) : ℂ) := by
  classical
  -- window redundancy: on `tripleSet` the folded window `x/2+2 ≤ prod3 ≤ x` is automatic.
  have hredRes : ((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        (x / 2 + 2 ≤ prod3 t ∧ prod3 t ≤ x ∧ ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) ∧
        N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧ t.2.1 ≤ N)).card
      = ((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) ∧
        N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧ t.2.1 ≤ N)).card := by
    apply congrArg
    apply Finset.filter_congr
    intro t ht
    rw [tripleSet, Finset.mem_filter] at ht
    obtain ⟨_, _, _, _, _, _, _, _, hwlo, hwhi⟩ := ht
    constructor
    · rintro ⟨h1, ⟨_, _, hr⟩, hrest⟩; exact ⟨h1, hr, hrest⟩
    · rintro ⟨h1, hr, hrest⟩; exact ⟨h1, ⟨hwlo, hwhi, hr⟩, hrest⟩
  have hredUnit : ((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        (x / 2 + 2 ≤ prod3 t ∧ prod3 t ≤ x ∧ IsUnit ((prod3 t : ℕ) : ZMod d)) ∧
        N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧ t.2.1 ≤ N)).card
      = ((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        IsUnit ((prod3 t : ℕ) : ZMod d) ∧
        N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b ∧ t.2.1 ≤ N)).card := by
    apply congrArg
    apply Finset.filter_congr
    intro t ht
    rw [tripleSet, Finset.mem_filter] at ht
    obtain ⟨_, _, _, _, _, _, _, _, hwlo, hwhi⟩ := ht
    constructor
    · rintro ⟨h1, ⟨_, _, hr⟩, hrest⟩; exact ⟨h1, hr, hrest⟩
    · rintro ⟨h1, hr, hrest⟩; exact ⟨h1, ⟨hwlo, hwhi, hr⟩, hrest⟩
  have hcardRes := (lowBox_pair_card
    (fun v => x / 2 + 2 ≤ v ∧ v ≤ x ∧ ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d))
    (M := M) hbX (fun v hv => ⟨hv.1, hv.2.1⟩)).trans hredRes
  have hcardUnit := (lowBox_pair_card
    (fun v => x / 2 + 2 ≤ v ∧ v ≤ x ∧ IsUnit ((v : ℕ) : ZMod d))
    (M := M) hbX (fun v hv => ⟨hv.1, hv.2.1⟩)).trans hredUnit
  have hRes :
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlphaLow z y ε₀ j N) a b m * blockPrimeInd N n else 0)
        - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlphaLow z y ε₀ j N) a b m * blockPrimeInd N n else 0)
        = ((lowCard x z y ε₀ j N M a b
            (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) : ℝ) : ℂ) := by
    rw [cutoffDiff_eq_pairCard_low x z y ε₀ j N a b X M
      (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) hxlo, hcardRes]
    simp only [lowCard]
    norm_cast
  have hUnit :
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
          if IsUnit ((m * n : ℕ) : ZMod d) then
            restrictAlpha (blockAlphaLow z y ε₀ j N) a b m * blockPrimeInd N n else 0)
        - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
          if IsUnit ((m * n : ℕ) : ZMod d) then
            restrictAlpha (blockAlphaLow z y ε₀ j N) a b m * blockPrimeInd N n else 0)
        = ((lowCard x z y ε₀ j N M a b
            (fun v => IsUnit ((v : ℕ) : ZMod d)) : ℝ) : ℂ) := by
    rw [cutoffDiff_eq_pairCard_low x z y ε₀ j N a b X M
      (fun v => IsUnit ((v : ℕ) : ZMod d)) hxlo, hcardUnit]
    simp only [lowCard]
    norm_cast
  have hexpx : apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j N) a b)
        (blockPrimeInd N) X M R₀ d x
      = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlphaLow z y ε₀ j N) a b m * blockPrimeInd N n else 0)
        - (1 / (d.totient : ℂ)) *
          (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
            if IsUnit ((m * n : ℕ) : ZMod d) then
              restrictAlpha (blockAlphaLow z y ε₀ j N) a b m * blockPrimeInd N n else 0) :=
    rfl
  have hexplo : apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j N) a b)
        (blockPrimeInd N) X M R₀ d (x / 2 + 1)
      = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlphaLow z y ε₀ j N) a b m * blockPrimeInd N n else 0)
        - (1 / (d.totient : ℂ)) *
          (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
            if IsUnit ((m * n : ℕ) : ZMod d) then
              restrictAlpha (blockAlphaLow z y ε₀ j N) a b m * blockPrimeInd N n else 0) :=
    rfl
  rw [hexpx, hexplo]
  rw [show ∀ (r1 u1 r2 u2 : ℂ),
      (r1 - (1 / (d.totient : ℂ)) * u1) - (r2 - (1 / (d.totient : ℂ)) * u2)
        = (r1 - r2) - (1 / (d.totient : ℂ)) * (u1 - u2) from fun r1 u1 r2 u2 => by ring]
  rw [hRes, hUnit]

/-- **`norm_lowRect_eq` — the low identification, norm form (the `Plo_discharge` atom).**  The
`‖T-difference‖` at the low coefficient EQUALS `|bandLowDisc|` — the object `Plo_discharge`'s `hLow`
accumulates.  Immediate from `lowRect_eq_apDiscBilinCutoff` via `Complex.norm_real`. -/
theorem norm_lowRect_eq {x z y : ℕ} {ε₀ : ℝ} {j N M a b X d : ℕ}
    (hbX : b ≤ X + 1) (hxlo : x / 2 + 1 ≤ x) :
    ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j N) a b) (blockPrimeInd N) X M 2 d x
      - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j N) a b) (blockPrimeInd N) X M 2 d
          (x / 2 + 1)‖
      = |bandLowDisc x z y ε₀ j N M a b d| := by
  rw [lowRect_eq_apDiscBilinCutoff hbX hxlo, bandLowDisc, nuChen_apply]
  rw [show ((lowCard x z y ε₀ j N M a b (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d)) : ℝ) : ℂ)
        - (1 / (d.totient : ℂ)) *
          ((lowCard x z y ε₀ j N M a b (fun v => IsUnit ((v : ℕ) : ZMod d)) : ℝ) : ℂ)
      = ((lowCard x z y ε₀ j N M a b (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))
          - 1 / (d.totient : ℝ) *
            lowCard x z y ε₀ j N M a b (fun v => IsUnit ((v : ℕ) : ZMod d)) : ℝ) : ℂ) by
        push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-! ## Part B — the symmetric rectangle (`max(y, N) < p₂ ≤ M`, unordered double count) -/

open Classical in
/-- **The symmetric-band semiprime indicator** `blockAlphaSym j N M m = [m = p₁·p₂, p₁ in block j,
z ≤ p₁ ≤ y < max(y, N) < p₂ ≤ M]` — `blockAlpha` with the large prime lifted to the SYMMETRIC range
`(max(y, N), M]`.  Still `0/1` (the split point `y` orients `(p₁, p₂)`). -/
noncomputable def blockAlphaSym (z y : ℕ) (ε₀ : ℝ) (j N M m : ℕ) : ℂ :=
  if (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ max y N < p₂ ∧ p₂ ≤ M ∧ p₁ * p₂ = m
      ∧ blockIdx z ε₀ p₁ = j) then 1 else 0

/-- **`‖blockAlphaSym‖ ≤ 1`.** -/
theorem norm_blockAlphaSym_le_one (z y : ℕ) (ε₀ : ℝ) (j N M m : ℕ) :
    ‖blockAlphaSym z y ε₀ j N M m‖ ≤ 1 := by
  unfold blockAlphaSym
  split_ifs <;> simp

/-- The `(m, n)`-pair predicate for the symmetric rectangle: `m` carries `blockAlphaSym`-weight `1`,
`n` is a `(max(y, N), ∞)`-prime, and `P(m·n)` — NO `m`-range (the symmetric region is redundant). -/
def symPairPred (z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (P : ℕ → Prop) (q : ℕ × ℕ) : Prop :=
  P (q.1 * q.2) ∧
    (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ max y N < p₂ ∧ p₂ ≤ M ∧
      p₁ * p₂ = q.1 ∧ blockIdx z ε₀ p₁ = j) ∧ (max y N < q.2 ∧ q.2.Prime)

open Classical in
/-- The `apDiscBilinCutoff` summand for the symmetric rectangle is the `symPairPred` indicator. -/
private lemma summand_eq_sym (z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (q : ℕ × ℕ) :
    (if P (q.1 * q.2) then
        blockAlphaSym z y ε₀ j N M q.1 * blockPrimeInd (max y N) q.2 else (0 : ℂ))
      = (if symPairPred z y ε₀ j N M P q then (1 : ℂ) else 0) := by
  classical
  unfold symPairPred blockAlphaSym blockPrimeInd
  by_cases hP : P (q.1 * q.2)
  · by_cases hf : (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ max y N < p₂ ∧ p₂ ≤ M ∧
        p₁ * p₂ = q.1 ∧ blockIdx z ε₀ p₁ = j)
    · by_cases hn : max y N < q.2 ∧ q.2.Prime
      · rw [if_pos hP, if_pos hf, if_pos hn, if_pos ⟨hP, hf, hn⟩, mul_one]
      · rw [if_pos hP, if_pos hf, if_neg hn, mul_zero, if_neg (fun h => hn h.2.2)]
    · rw [if_pos hP, if_neg hf, zero_mul, if_neg (fun h => hf h.2.1)]
  · rw [if_neg hP, if_neg (fun h => hP h.1)]

open Classical in
/-- The symmetric-rectangle double sum counts the `symPairPred` pairs. -/
private lemma pairTerm_eq_sym (z y : ℕ) (ε₀ : ℝ) (j N M X : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 M,
        if P (m * n) then
          blockAlphaSym z y ε₀ j N M m * blockPrimeInd (max y N) n else (0 : ℂ))
      = (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
            (fun q => symPairPred z y ε₀ j N M P q)).card : ℂ) := by
  classical
  rw [← Finset.sum_product']
  rw [Finset.sum_congr rfl (fun q _ => summand_eq_sym z y ε₀ j N M P q)]
  rw [Finset.sum_boole]

open Classical in
/-- **`symRectCount_eq_card` — the symmetric rectangle count as a product-filter cardinality.**  The
`BandClose.symRectCount` double sum `∑_{p₁} ∑_{(p,q)∈S×S} [cwin]` is the cardinality of the filtered
product `bandP1Set × (S × S)`. -/
theorem symRectCount_eq_card (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (P : ℕ → Prop) :
    symRectCount x z y ε₀ j N M P
      = (((bandP1Set x z y ε₀ j ×ˢ (bandLargeSet x y N M ×ˢ bandLargeSet x y N M)).filter
          (fun w => cwin x P w.1 w.2.1 w.2.2)).card : ℝ) := by
  classical
  unfold symRectCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p₁ _ => ?_)
  refine Finset.sum_congr rfl (fun pq _ => ?_)
  by_cases h : cwin x P p₁ pq.1 pq.2 <;> simp [h]

open Classical in
/-- **`symBox_pair_card` — the symmetric-rectangle pair bijection (UNORDERED).**  The windowed
`symPairPred` pairs `(m, n)` are in bijection with the block-`j` unordered triples `(p₁, (p, q))`
(`p₁` in block `j`, `p, q ∈ S = (max(y,N), M]`) via `(p₁, (p, q)) ↦ (p₁·p, q)`.  Injectivity is the
oriented-factorization uniqueness (`p₁ ≤ y < p`); NO ordering constraint between `p` and `q` (the
point of the symmetric rectangle).  The window folded into `P` supplies the `cwin` window. -/
theorem symBox_pair_card {x z y : ℕ} {ε₀ : ℝ} {j N M X : ℕ}
    (C : ℕ → Prop) (hxX : x ≤ X) :
    (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
        (fun q => symPairPred z y ε₀ j N M (fun v => x / 2 + 2 ≤ v ∧ v ≤ x ∧ C v) q)).card)
      = (((bandP1Set x z y ε₀ j ×ˢ (bandLargeSet x y N M ×ˢ bandLargeSet x y N M)).filter
          (fun w => cwin x C w.1 w.2.1 w.2.2)).card) := by
  classical
  symm
  apply Finset.card_bij (fun w _ => (w.1 * w.2.1, w.2.2))
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_product, bandP1Set, bandLargeSet, Finset.mem_Icc,
      cwin] at hw
    obtain ⟨⟨⟨⟨hp1lo, hp1hi⟩, hp1prime, hzp1, hp1y, hblk⟩,
             ⟨⟨hplo, _hphi⟩, hpprime, hpmax, hpM⟩,
             ⟨hqlo, _hqhi⟩, hqprime, hqmax, hqM⟩,
            hC, hwlo, hwhi⟩ := hw
    have hmle : w.1 * w.2.1 ≤ x := le_trans (Nat.le_mul_of_pos_right (w.1 * w.2.1) hqlo) hwhi
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨Nat.mul_pos hp1lo hplo, le_trans hmle hxX⟩, ⟨hqlo, hqM⟩⟩,
      ⟨hwlo, hwhi, hC⟩,
      ⟨w.1, w.2.1, hp1prime, hpprime, hzp1, hp1y, hpmax, hpM, rfl, hblk⟩, hqmax, hqprime⟩
  · intro w hw w' hw' heq
    simp only [Finset.mem_filter, Finset.mem_product, bandP1Set, bandLargeSet, Finset.mem_Icc,
      cwin] at hw hw'
    obtain ⟨⟨⟨_, hp1prime, _, hp1y, _⟩, ⟨_, hpprime, hpmax, _⟩, _⟩, _⟩ := hw
    obtain ⟨⟨⟨_, hp1prime', _, _, _⟩, ⟨_, hpprime', hpmax', _⟩, _⟩, _⟩ := hw'
    rw [Prod.mk.injEq] at heq
    obtain ⟨hmeq, hqeq⟩ := heq
    have hyp : y < w'.2.1 := lt_of_le_of_lt (le_max_left y N) hpmax'
    obtain ⟨he1, he2⟩ := prime_pair_unique_ident hp1prime hp1prime' hpprime' hp1y hyp hmeq
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
    have hqp1x : qp.1 ≤ x := le_trans (Nat.le_mul_of_pos_right qp.1 hqp2pos) hwhi0
    have hqp2x : qp.2 ≤ x := le_trans (Nat.le_mul_of_pos_left qp.2 hqp1pos) hwhi0
    have hp1le : p₁ ≤ qp.1 := by rw [← hprod]; exact Nat.le_mul_of_pos_right p₁ hp2prime.pos
    have hp2le : p₂ ≤ qp.1 := by rw [← hprod]; exact Nat.le_mul_of_pos_left p₂ hp1prime.pos
    refine ⟨(p₁, p₂, qp.2), ?_, Prod.ext_iff.mpr ⟨hprod, rfl⟩⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · rw [bandP1Set, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hp1prime.pos, le_trans hp1le hqp1x⟩, hp1prime, hzp1, hp1y, hblk⟩
      · rw [Finset.mem_product]
        refine ⟨?_, ?_⟩
        · rw [bandLargeSet, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hp2prime.pos, le_trans hp2le hqp1x⟩, hp2prime, hp2max, hp2M⟩
        · rw [bandLargeSet, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hnprime.pos, hqp2x⟩, hnprime, hnmax, hqp2hi⟩
    · rw [cwin]
      exact ⟨by rw [hprodeq]; exact hC0, by rw [hprodeq]; exact hwlo0, by rw [hprodeq]; exact hwhi0⟩

open Classical in
/-- The symmetric-rectangle cutoff difference equals the windowed `symPairPred` pair count. -/
private lemma cutoffDiff_eq_pairCard_sym (x z y : ℕ) (ε₀ : ℝ) (j N M X : ℕ)
    (P : ℕ → Prop) [DecidablePred P] (hxlo : x / 2 + 1 ≤ x) :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
        if P (m * n) then
          blockAlphaSym z y ε₀ j N M m * blockPrimeInd (max y N) n else (0 : ℂ))
      - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
        if P (m * n) then
          blockAlphaSym z y ε₀ j N M m * blockPrimeInd (max y N) n else (0 : ℂ))
      = (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
          (fun q => symPairPred z y ε₀ j N M
            (fun v => x / 2 + 2 ≤ v ∧ v ≤ x ∧ P v) q)).card : ℂ) := by
  classical
  rw [← pairTerm_eq_sym z y ε₀ j N M X (fun v => x / 2 + 2 ≤ v ∧ v ≤ x ∧ P v),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hP : P (m * n)
  · by_cases hx : m * n ≤ x
    · by_cases hlo : m * n ≤ x / 2 + 1
      · have hnw : ¬ (x / 2 + 2 ≤ m * n ∧ m * n ≤ x ∧ P (m * n)) := fun ⟨hw, _, _⟩ => by omega
        rw [if_pos hx, if_pos hlo, sub_self, if_neg hnw]
      · rw [if_pos hx, if_neg hlo, sub_zero, if_pos hP,
          if_pos (show x / 2 + 2 ≤ m * n ∧ m * n ≤ x ∧ P (m * n) from ⟨by omega, hx, hP⟩)]
    · have hlo : ¬ m * n ≤ x / 2 + 1 := by omega
      have hnw : ¬ (x / 2 + 2 ≤ m * n ∧ m * n ≤ x ∧ P (m * n)) := fun ⟨_, hw, _⟩ => by omega
      rw [if_neg hx, if_neg hlo, sub_self, if_neg hnw]
  · have hnw : ¬ (x / 2 + 2 ≤ m * n ∧ m * n ≤ x ∧ P (m * n)) := fun ⟨_, _, hp⟩ => hP hp
    simp only [if_neg hP, if_neg hnw, ite_self, sub_self]

open Classical in
/-- **`symRect_eq_apDiscBilinCutoff` — the symmetric-band identification (FLOOR B, FULL).**  The
symmetric rectangle's honest discrepancy IS the difference of the two one-sided cutoff carriers at
`T = x` and `T = x/2+1`, at the coefficient `blockAlphaSym j N M` with `β = blockPrimeInd (max y N)`
over `(max(y, N), M]`.  NO `m`-range restriction and NO ordering constraint (the unordered double
count, `symBox_pair_card`).  The `β`-block's raised lower end `max(y, N)` keeps the dyadic
hypothesis `M ≤ 2·max(y, N)` (since `M ≤ 2N ≤ 2·max(y, N)`) — threaded honestly downstream. -/
theorem symRect_eq_apDiscBilinCutoff {x z y : ℕ} {ε₀ : ℝ} {j N M X d R₀ : ℕ}
    (hxX : x ≤ X) (hxlo : x / 2 + 1 ≤ x) :
    apDiscBilinCutoff (blockAlphaSym z y ε₀ j N M) (blockPrimeInd (max y N)) X M R₀ d x
      - apDiscBilinCutoff (blockAlphaSym z y ε₀ j N M) (blockPrimeInd (max y N)) X M R₀ d
          (x / 2 + 1)
      = ((symRectCount x z y ε₀ j N M (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) : ℝ) : ℂ)
        - (1 / (d.totient : ℂ)) *
          ((symRectCount x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod d)) : ℝ) : ℂ) := by
  classical
  have hRes :
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            blockAlphaSym z y ε₀ j N M m * blockPrimeInd (max y N) n else 0)
        - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            blockAlphaSym z y ε₀ j N M m * blockPrimeInd (max y N) n else 0)
        = ((symRectCount x z y ε₀ j N M
            (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) : ℝ) : ℂ) := by
    rw [cutoffDiff_eq_pairCard_sym x z y ε₀ j N M X
      (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) hxlo,
      symBox_pair_card (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) hxX,
      symRectCount_eq_card]
    norm_cast
  have hUnit :
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
          if IsUnit ((m * n : ℕ) : ZMod d) then
            blockAlphaSym z y ε₀ j N M m * blockPrimeInd (max y N) n else 0)
        - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
          if IsUnit ((m * n : ℕ) : ZMod d) then
            blockAlphaSym z y ε₀ j N M m * blockPrimeInd (max y N) n else 0)
        = ((symRectCount x z y ε₀ j N M
            (fun v => IsUnit ((v : ℕ) : ZMod d)) : ℝ) : ℂ) := by
    rw [cutoffDiff_eq_pairCard_sym x z y ε₀ j N M X (fun v => IsUnit ((v : ℕ) : ZMod d)) hxlo,
      symBox_pair_card (fun v => IsUnit ((v : ℕ) : ZMod d)) hxX, symRectCount_eq_card]
    norm_cast
  have hexpx : apDiscBilinCutoff (blockAlphaSym z y ε₀ j N M) (blockPrimeInd (max y N)) X M R₀ d x
      = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            blockAlphaSym z y ε₀ j N M m * blockPrimeInd (max y N) n else 0)
        - (1 / (d.totient : ℂ)) *
          (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
            if IsUnit ((m * n : ℕ) : ZMod d) then
              blockAlphaSym z y ε₀ j N M m * blockPrimeInd (max y N) n else 0) :=
    rfl
  have hexplo : apDiscBilinCutoff (blockAlphaSym z y ε₀ j N M) (blockPrimeInd (max y N)) X M R₀ d
        (x / 2 + 1)
      = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            blockAlphaSym z y ε₀ j N M m * blockPrimeInd (max y N) n else 0)
        - (1 / (d.totient : ℂ)) *
          (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
            if IsUnit ((m * n : ℕ) : ZMod d) then
              blockAlphaSym z y ε₀ j N M m * blockPrimeInd (max y N) n else 0) :=
    rfl
  rw [hexpx, hexplo]
  rw [show ∀ (r1 u1 r2 u2 : ℂ),
      (r1 - (1 / (d.totient : ℂ)) * u1) - (r2 - (1 / (d.totient : ℂ)) * u2)
        = (r1 - r2) - (1 / (d.totient : ℂ)) * (u1 - u2) from fun r1 u1 r2 u2 => by ring]
  rw [hRes, hUnit]

/-- **`norm_symRect_eq` — the symmetric identification, norm form (the `Plo_discharge` atom).**  The
`‖T-difference‖` at the symmetric coefficient EQUALS `|bandSymRectDisc|`. -/
theorem norm_symRect_eq {x z y : ℕ} {ε₀ : ℝ} {j N M X d : ℕ} (hxX : x ≤ X) (hxlo : x / 2 + 1 ≤ x) :
    ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j N M) (blockPrimeInd (max y N)) X M 2 d x
      - apDiscBilinCutoff (blockAlphaSym z y ε₀ j N M) (blockPrimeInd (max y N)) X M 2 d
          (x / 2 + 1)‖
      = |bandSymRectDisc x z y ε₀ j N M d| := by
  rw [symRect_eq_apDiscBilinCutoff hxX hxlo, bandSymRectDisc, nuChen_apply]
  rw [show ((symRectCount x z y ε₀ j N M
          (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d)) : ℝ) : ℂ)
        - (1 / (d.totient : ℂ)) *
          ((symRectCount x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod d)) : ℝ) : ℂ)
      = ((symRectCount x z y ε₀ j N M (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))
          - 1 / (d.totient : ℝ) *
            symRectCount x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod d)) : ℝ) : ℂ) by
        push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-! ## Part C — the composed `Plo_discharge_priced` (FULL, item 3) -/

open Classical in
/-- **`Plo_discharge_priced` (FULL) — `BandClose.Plo_discharge` at priceable rectangle forms.**
`Plo_discharge`'s named residuals `Psym`, `Plow` are here instantiated at the
`general_BV_cutoff_final`-priceable one-sided norms: for each piece the two BV-carrier prices at the
cutoffs `T = x` and `T = x/2+1` (the price shape of `WindowClose.hHD_of_generalBV_window`).  The
per-`(k, d)` cutoff-difference triangle (`norm_symRect_eq`/`norm_lowRect_eq` + `norm_sub_le`)
converts the two-sided price into the honest `|bandSymRectDisc|`/`|bandLowDisc|` budgets that
`Plo_discharge` consumes.  The output is the band slot of `PieceDecomp.hBlock_of_window_prices`:
½·(the symmetric price) + (the α_low price) + the crude diagonal. -/
theorem Plo_discharge_priced (x z y : ℕ) (ε₀ : ℝ) (Ps : ℕ) (bound : ℝ) (j X : ℕ)
    (Psym_hi Psym_lo Plow_hi Plow_lo : ℝ)
    (hz : 1 ≤ z) (hxX : x ≤ X) (hxlo : x / 2 + 1 ≤ x)
    (hSymHi : (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
            (blockPrimeInd (max y (pieceN k))) X (pieceM k) 2 d x‖ else 0) ≤ Psym_hi)
    (hSymLo : (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
            (blockPrimeInd (max y (pieceN k))) X (pieceM k) 2 d (x / 2 + 1)‖ else 0) ≤ Psym_lo)
    (hLowHi : (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
            (min (z * pieceN k + 1) (x + 1)) (x + 1)) (blockPrimeInd (pieceN k)) X (pieceM k)
            2 d x‖ else 0) ≤ Plow_hi)
    (hLowLo : (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
            (min (z * pieceN k + 1) (x + 1)) (x + 1)) (blockPrimeInd (pieceN k)) X (pieceM k)
            2 d (x / 2 + 1)‖ else 0) ≤ Plow_lo) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k)
             (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
      ≤ (1 / 2) * (Psym_hi + Psym_lo) + (Plow_hi + Plow_lo)
        + (1 / 2) * ((Nat.divisors Ps).card : ℝ)
            * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
                (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ) := by
  classical
  set R := Finset.range (Nat.log 2 x + 1) with hR
  -- The symmetric budget: the per-`(k, d)` cutoff-difference triangle summed.
  have hSym : (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |bandSymRectDisc x z y ε₀ j (pieceN k) (pieceM k) d| else 0)
      ≤ Psym_hi + Psym_lo := by
    have hterm : ∀ (k d : ℕ),
        (if (d : ℝ) < bound then |bandSymRectDisc x z y ε₀ j (pieceN k) (pieceM k) d| else 0)
          ≤ (if (d : ℝ) < bound then
                ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                  (blockPrimeInd (max y (pieceN k))) X (pieceM k) 2 d x‖ else 0)
            + (if (d : ℝ) < bound then
                ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                  (blockPrimeInd (max y (pieceN k))) X (pieceM k) 2 d (x / 2 + 1)‖ else 0) := by
      intro k d
      by_cases hd : (d : ℝ) < bound
      · simp only [if_pos hd]
        rw [← norm_symRect_eq (X := X) (d := d) hxX hxlo]
        exact norm_sub_le _ _
      · simp only [if_neg hd]; norm_num
    refine le_trans (Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun d _ => hterm k d))) ?_
    have hsplit : (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
          ((if (d : ℝ) < bound then
                ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                  (blockPrimeInd (max y (pieceN k))) X (pieceM k) 2 d x‖ else 0)
            + (if (d : ℝ) < bound then
                ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                  (blockPrimeInd (max y (pieceN k))) X (pieceM k) 2 d (x / 2 + 1)‖ else 0)))
        = (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
              if (d : ℝ) < bound then
                ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                  (blockPrimeInd (max y (pieceN k))) X (pieceM k) 2 d x‖ else 0)
          + (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
              if (d : ℝ) < bound then
                ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                  (blockPrimeInd (max y (pieceN k))) X (pieceM k) 2 d (x / 2 + 1)‖ else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_add_distrib)
    rw [hsplit]
    exact add_le_add hSymHi hSymLo
  -- The α_low budget: the same triangle at the low coefficient.
  have hLow : (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |bandLowDisc x z y ε₀ j (pieceN k) (pieceM k)
          (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
      ≤ Plow_hi + Plow_lo := by
    have hterm : ∀ (k d : ℕ),
        (if (d : ℝ) < bound then |bandLowDisc x z y ε₀ j (pieceN k) (pieceM k)
            (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
          ≤ (if (d : ℝ) < bound then
                ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1)) (blockPrimeInd (pieceN k))
                  X (pieceM k) 2 d x‖ else 0)
            + (if (d : ℝ) < bound then
                ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1)) (blockPrimeInd (pieceN k))
                  X (pieceM k) 2 d (x / 2 + 1)‖ else 0) := by
      intro k d
      by_cases hd : (d : ℝ) < bound
      · simp only [if_pos hd]
        rw [← norm_lowRect_eq (X := X) (d := d) (by omega : x + 1 ≤ X + 1) hxlo]
        exact norm_sub_le _ _
      · simp only [if_neg hd]; norm_num
    refine le_trans (Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun d _ => hterm k d))) ?_
    have hsplit : (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
          ((if (d : ℝ) < bound then
                ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1)) (blockPrimeInd (pieceN k))
                  X (pieceM k) 2 d x‖ else 0)
            + (if (d : ℝ) < bound then
                ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1)) (blockPrimeInd (pieceN k))
                  X (pieceM k) 2 d (x / 2 + 1)‖ else 0)))
        = (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
              if (d : ℝ) < bound then
                ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1)) (blockPrimeInd (pieceN k))
                  X (pieceM k) 2 d x‖ else 0)
          + (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
              if (d : ℝ) < bound then
                ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1)) (blockPrimeInd (pieceN k))
                  X (pieceM k) 2 d (x / 2 + 1)‖ else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_add_distrib)
    rw [hsplit]
    exact add_le_add hLowHi hLowLo
  exact Plo_discharge x z y ε₀ Ps bound j (Psym_hi + Psym_lo) (Plow_hi + Plow_lo) hz hSym hLow

/-! ## Composition sanity — the end-to-end chain elaborates

The two identifications turn `Plo_discharge`'s named residuals into `general_BV_cutoff_final`-priced
`apDiscBilinCutoff` T-differences; `Plo_discharge_priced` composes them into the band slot
`Plo` of `PieceDecomp.hBlock_of_window_prices`. -/

section CompositionSanity

#check @Salt.Chen.blockAlphaLow
#check @Salt.Chen.blockAlphaSym
#check @Salt.Chen.lowRect_eq_apDiscBilinCutoff
#check @Salt.Chen.symRect_eq_apDiscBilinCutoff
#check @Salt.Chen.norm_lowRect_eq
#check @Salt.Chen.norm_symRect_eq
#check @Salt.Chen.Plo_discharge_priced
#check @Salt.Chen.Plo_discharge
#check @Salt.Chen.general_BV_cutoff_final
#check @Salt.Chen.hBlock_of_window_prices

end CompositionSanity

end Salt.Chen
