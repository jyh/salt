/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.SwitchBV
import Salt.Chen.PDiag

/-!
# G-WINDOWSW — the annulus-sliced window identification (wave W3a, Opt-A)

Design: `docs/exploration/pilot.md` (the `~17:30 G-WINDOWSW-recon` NO_GO on the single-cutoff
premise + the Fable Opt-A adjudication).  The twin's window-in-carrier identification
`Salt.Chen.blockBox_windowDisc_eq_res` (`WindowSW:565`) hard-wires the TOP-half window
`x/2+2 ≤ prod ≤ x` as a *factor-2* difference of the two one-sided cutoffs `T = x`, `T = x/2+1`;
the boundary reduction `MediumFloor.box_disc_three_way` cancels those two cutoffs off the
`dyadicBoundary` (≤ 3 pieces, needing `T₂ ≤ 2·T₁`).  Goldbach's `goldTripleSet` uses the
BOTTOM-half window `2 ≤ prod ≤ N/2`, spanning ~21 dyadic scales — a monolithic cutoff pays the
FULL box `X·M` and fails the `≤ 3`-pieces lemma.

**Opt-A — the outer dyadic annulus sum.**  Slice the window `[2, N/2]` into the factor-2 annuli
`(goldCut N k, goldCut N (k+1)]`, `goldCut N k = min (2^k) (N/2)`.  Per annulus the twin's
difference form reuses (RE-DERIVED here over `goldTripleSet` at GENERAL cutoffs, because the
annulus `(2^k, 2^{k+1}]` is off-by-one from the twin's `(x/2+1, x]` — the ±1 boundary is worked
honestly).  Each annulus IS factor-2 (`goldCut_succ_le_two_mul`), so `dyadicBoundary_card_le_three`
applies per annulus; the `O(log N)` annuli cost ONE log, absorbed downstream by consuming the BV
backbone at saving `A+1` (SW supplies every `A`).  The full window discrepancy telescopes into the
annulus sum (`goldWindowDisc_le_annulus_sum`) — the consumable interface for G-SW2's
`hNum_at_opW` mirror.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]`).
-/

open Finset
open scoped BigOperators

namespace Salt.Goldbach

open Salt.Chen

/-! ## Part A — the generic pair-counting re-proofs (carrier-agnostic; `WindowSW` privates) -/

/-- Re-proof of `WindowSW.prime_pair_unique_win` (private there): the oriented `m ↦ {p₁,p₂}`
factorization at `y` is unique. -/
private lemma gold_prime_pair_unique {y p₁ p₂ p₁' p₂' : ℕ}
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

open Classical in
/-- Re-proof of `WindowSW.summand_eq_win` (private there): the `apDiscBilin` summand is the
`pairPred` `0/1` indicator.  Carrier-agnostic — depends only on the block coefficients. -/
private lemma gold_summand_eq (z y : ℕ) (ε₀ : ℝ) (j N a b : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (q : ℕ × ℕ) :
    (if P (q.1 * q.2) then
        restrictAlpha (blockAlpha z y ε₀ j) a b q.1 * blockPrimeInd N q.2 else (0 : ℂ))
      = (if pairPred z y ε₀ j N a b P q then (1 : ℂ) else 0) := by
  classical
  unfold pairPred restrictAlpha blockAlpha blockPrimeInd
  by_cases hP : P (q.1 * q.2)
  · by_cases hbox : a ≤ q.1 ∧ q.1 < b
    · by_cases hf : (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧
          p₁ * p₂ = q.1 ∧ blockIdx z ε₀ p₁ = j)
      · by_cases hn : N < q.2 ∧ q.2.Prime
        · rw [if_pos hP, if_pos hbox, if_pos hf, if_pos hn, if_pos ⟨hP, hbox, hf, hn⟩, mul_one]
        · rw [if_pos hP, if_pos hbox, if_pos hf, if_neg hn, mul_zero,
            if_neg (fun h => hn h.2.2.2)]
      · rw [if_pos hP, if_pos hbox, if_neg hf, zero_mul, if_neg (fun h => hf h.2.2.1)]
    · rw [if_pos hP, if_neg hbox, zero_mul, if_neg (fun h => hbox h.2.1)]
  · rw [if_neg hP, if_neg (fun h => hP h.1)]

open Classical in
/-- Re-proof of `WindowSW.pairTerm_eq_win` (private there): the `apDiscBilin` double sum counts
the `pairPred` pairs. -/
private lemma gold_pairTerm_eq (z y : ℕ) (ε₀ : ℝ) (j N a b X M : ℕ) (P : ℕ → Prop)
    [DecidablePred P] :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 M,
        if P (m * n) then
          restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd N n else (0 : ℂ))
      = (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
            (fun q => pairPred z y ε₀ j N a b P q)).card : ℂ) := by
  classical
  rw [← Finset.sum_product']
  rw [Finset.sum_congr rfl (fun q _ => gold_summand_eq z y ε₀ j N a b P q)]
  rw [Finset.sum_boole]

/-! ## Part B — the dyadic window annulus family (`goldCut`) -/

/-- **The window cutoff sequence.**  `goldCut N k = min (2^k) (N/2)` — the upper endpoint of the
`k`-th dyadic window annulus `(goldCut N k, goldCut N (k+1)]`, saturating at the window top `N/2`.
The annuli partition `[2, N/2]` and each is factor-2 (`goldCut_succ_le_two_mul`). -/
def goldCut (N k : ℕ) : ℕ := min (2 ^ k) (N / 2)

/-- The cutoff never exceeds the window top `N/2`. -/
lemma goldCut_le_half (N k : ℕ) : goldCut N k ≤ N / 2 := min_le_right _ _

/-- The cutoff never exceeds `N` (the `goldTripleSet` carrier bound). -/
lemma goldCut_le_self (N k : ℕ) : goldCut N k ≤ N :=
  le_trans (goldCut_le_half N k) (Nat.div_le_self N 2)

/-- For `N ≥ 2` every cutoff is at least `1` (the window lower guard `prod ≥ 2`). -/
lemma one_le_goldCut {N : ℕ} (hN : 2 ≤ N) (k : ℕ) : 1 ≤ goldCut N k := by
  have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  unfold goldCut; omega

/-- `goldCut N 0 = 1` (for `N ≥ 2`) — the telescoping base (the `T = 1` carrier vanishes). -/
lemma goldCut_zero {N : ℕ} (hN : 2 ≤ N) : goldCut N 0 = 1 := by
  unfold goldCut; rw [pow_zero]; omega

/-- **The factor-2 property** — the box_disc_three_way `hT : T₂ ≤ 2·T₁` slot per annulus. -/
lemma goldCut_succ_le_two_mul (N k : ℕ) : goldCut N (k + 1) ≤ 2 * goldCut N k := by
  have h : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  unfold goldCut; omega

/-- The cutoff is monotone in `k`. -/
lemma goldCut_mono (N : ℕ) : Monotone (goldCut N) := by
  intro k k' hk
  unfold goldCut
  exact min_le_min (Nat.pow_le_pow_right (by norm_num) hk) (le_refl _)

/-- **The window-top saturation.**  At `k = ⌊log₂ N⌋ + 1` the cutoff reaches the window top `N/2`
(`2^{k} > N ≥ N/2`) — the telescoping ceiling. -/
lemma goldCut_top {N : ℕ} (_hN : 2 ≤ N) : goldCut N (Nat.log 2 N + 1) = N / 2 := by
  have hlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hhalf : N / 2 ≤ N := Nat.div_le_self N 2
  unfold goldCut; omega

/-! ## Part C — the corner-free pair bijection over `goldTripleSet` -/

open Classical in
/-- **`goldBlockBox_windowed_pair_card` — the corner-free pair bijection (`goldTripleSet`).**  The
mirror of `Salt.Chen.blockBox_windowed_pair_card` at the BOTTOM-half window: the window is carried
by the class predicate `hPwin` (`2 ≤ v ∧ v ≤ Ne/2`, supplied by the cutoff) rather than by the
twin's `x/2+2 ≤ v ≤ x`, and the carrier is `Icc 1 Ne` (the `goldTripleSet` box).  Injectivity is
`gold_prime_pair_unique`; surjectivity reconstructs the triple, deriving `p₂ ≤ p₃` from `hord`
(`p₂·z ≤ p₁p₂ = m < b ≤ z·Nf+1`) and the window from `hPwin`.  `Nf` is the block prime floor
(`blockPrimeInd Nf`), independent of the even number `Ne`. -/
theorem goldBlockBox_windowed_pair_card {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M a b X : ℕ}
    (P : ℕ → Prop) [DecidablePred P]
    (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * Nf + 1)
    (hPwin : ∀ v : ℕ, P v → 2 ≤ v ∧ v ≤ Ne / 2) :
    (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter (fun q => pairPred z y ε₀ j Nf a b P q)).card)
      = (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ P (prod3 t) ∧
          Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card) := by
  classical
  symm
  apply Finset.card_bij (fun t _ => (t.1 * t.2.1, t.2.2))
  · intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htri, hblk, hP, hNlt, hMle, hab_lo, hab_hi⟩ := ht
    rw [goldTripleSet, Finset.mem_filter] at htri
    obtain ⟨_, hzp1, hp1y, hyp2, _hp2p3, hp1prime, hp2prime, hp3prime, _hwlo, _hwhi⟩ := htri
    have hm1 : 1 ≤ t.1 * t.2.1 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hp1prime.pos.ne' hp2prime.pos.ne')
    have hmX : t.1 * t.2.1 ≤ X := by omega
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨hm1, hmX⟩, ⟨hp3prime.pos, hMle⟩⟩,
      hP, ⟨hab_lo, hab_hi⟩,
      ⟨t.1, t.2.1, hp1prime, hp2prime, hzp1, hp1y, hyp2, rfl, hblk⟩, ⟨hNlt, hp3prime⟩⟩
  · intro t ht t' ht' heq
    rw [Finset.mem_filter] at ht ht'
    have htri := ht.1
    have htri' := ht'.1
    rw [goldTripleSet, Finset.mem_filter] at htri htri'
    obtain ⟨_, _, hp1y, _, _, hp1prime, _, _, _, _⟩ := htri
    obtain ⟨_, _, _, hyp2', _, hp1prime', hp2prime', _, _, _⟩ := htri'
    rw [Prod.mk.injEq] at heq
    obtain ⟨hmeq, hneq⟩ := heq
    obtain ⟨he1, he2⟩ := gold_prime_pair_unique hp1prime hp1prime' hp2prime' hp1y hyp2' hmeq
    exact Prod.ext_iff.mpr ⟨he1, Prod.ext_iff.mpr ⟨he2, hneq⟩⟩
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
    obtain ⟨⟨⟨hq1lo, _hq1hi⟩, hq2lo, hq2hi⟩, hpp⟩ := hq
    obtain ⟨hP, ⟨ha_lo, ha_hi⟩, ⟨p₁, p₂, hp1prime, hp2prime, hzp1, hp1y, hyp2, hprod, hblk⟩,
      ⟨hNq2, hq2prime⟩⟩ := hpp
    have hp2z : p₂ * z ≤ p₁ * p₂ := by
      have h : p₂ * z ≤ p₂ * p₁ := Nat.mul_le_mul_left p₂ hzp1
      rwa [mul_comm p₂ p₁] at h
    have hp2N : p₂ ≤ Nf := by
      have h1 : p₂ * z ≤ b - 1 := by rw [hprod] at hp2z; omega
      have h2 : z * p₂ ≤ z * Nf := by rw [mul_comm z p₂]; omega
      exact Nat.le_of_mul_le_mul_left h2 (by omega)
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
    refine ⟨?_, hblk, ?_, hNq2, hq2hi, ?_, ?_⟩
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

/-! ## Part D — the general-cutoff difference is the windowed pair count -/

open Classical in
/-- **`gold_cutoffDiff_eq_pairCard` — the general-cutoff difference is the annulus pair count.**
Subtracting the `T = Tlo` cutoff term from the `T = Thi` cutoff term leaves the annulus
`Tlo < m·n ≤ Thi` folded into the class predicate; `gold_pairTerm_eq` counts the surviving pairs.
The general cutoffs `(Tlo, Thi]` replace the twin's hard-wired `(x/2+1, x]` — the ±1 boundary is
the strict `Tlo < v` (the twin's `x/2+2 ≤ v = (x/2+1)+1 ≤ v`). -/
private lemma gold_cutoffDiff_eq_pairCard (z y : ℕ) (ε₀ : ℝ) (j Nf M a b X : ℕ)
    (P : ℕ → Prop) [DecidablePred P] (Tlo Thi : ℕ) (hT : Tlo ≤ Thi) :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
        if P (m * n) then
          restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd Nf n else (0 : ℂ))
      - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
        if P (m * n) then
          restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd Nf n else (0 : ℂ))
      = (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
          (fun q => pairPred z y ε₀ j Nf a b
            (fun v => Tlo < v ∧ v ≤ Thi ∧ P v) q)).card : ℂ) := by
  classical
  rw [← gold_pairTerm_eq z y ε₀ j Nf a b X M (fun v => Tlo < v ∧ v ≤ Thi ∧ P v),
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

/-! ## Part E — the window-in-carrier identification at general cutoffs -/

open Classical in
/-- **`goldBlockBox_windowDisc_eq_res` — the window identification at a FREE residue and GENERAL
cutoffs.**  The mirror of `Salt.Chen.blockBox_windowDisc_eq_res` over the `goldTripleSet` carrier
at arbitrary window endpoints `(Tlo, Thi]` (with `1 ≤ Tlo`, `Thi ≤ Ne/2`, `Tlo ≤ Thi`).  On an
ordering-cleared box (`hord`) the difference of the two one-sided cutoff carriers equals the raw
`goldTripleSet` class-count difference restricted to `Tlo < prod3 ≤ Thi`.  NO coprimality is
required (the residue never enters the bijection); the window `Tlo < prod3 ≤ Thi` is a GENUINE
filter (not redundant, unlike the twin's built-in window).  Instantiated at the dyadic annulus
`(Tlo, goldCut Ne (k+1)]` (`..._annulus`) and at the full window `(1, N/2]`
(`..._full`).  The W-mirror (G-SW2) takes `d := Q·d'`, `R₀ := crtClassG Q d' N a`. -/
theorem goldBlockBox_windowDisc_eq_res {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M a b X d R₀ : ℕ}
    (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * Nf + 1)
    (Tlo Thi : ℕ) (hTlo : 1 ≤ Tlo) (hThi : Thi ≤ Ne / 2) (hT : Tlo ≤ Thi) :
    apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd Nf) X M R₀ d Thi
      - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd Nf) X M R₀ d Tlo
      = (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            (Tlo < prod3 t ∧ prod3 t ≤ Thi ∧
              ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) ∧
            Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℂ)
        - (1 / (d.totient : ℂ)) *
          (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            (Tlo < prod3 t ∧ prod3 t ≤ Thi ∧
              IsUnit ((prod3 t : ℕ) : ZMod d)) ∧
            Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℂ) := by
  classical
  have hPwinR : ∀ v : ℕ, (Tlo < v ∧ v ≤ Thi ∧
      ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) → 2 ≤ v ∧ v ≤ Ne / 2 := by
    intro v hv
    exact ⟨by omega, le_trans hv.2.1 hThi⟩
  have hPwinU : ∀ v : ℕ, (Tlo < v ∧ v ≤ Thi ∧
      IsUnit ((v : ℕ) : ZMod d)) → 2 ≤ v ∧ v ≤ Ne / 2 := by
    intro v hv
    exact ⟨by omega, le_trans hv.2.1 hThi⟩
  -- the residue / unit cutoff differences equal the window-restricted `goldTripleSet` counts.
  have hRes :
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd Nf n else 0)
        - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd Nf n else 0)
        = (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            (Tlo < prod3 t ∧ prod3 t ≤ Thi ∧
              ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) ∧
            Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℂ) := by
    rw [gold_cutoffDiff_eq_pairCard z y ε₀ j Nf M a b X
      (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) (Tlo) (Thi) hT]
    exact_mod_cast goldBlockBox_windowed_pair_card
      (fun v => Tlo < v ∧ v ≤ Thi ∧
        ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) hz hbX hord hPwinR
  have hUnit :
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
          if IsUnit ((m * n : ℕ) : ZMod d) then
            restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd Nf n else 0)
        - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
          if IsUnit ((m * n : ℕ) : ZMod d) then
            restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd Nf n else 0)
        = (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            (Tlo < prod3 t ∧ prod3 t ≤ Thi ∧
              IsUnit ((prod3 t : ℕ) : ZMod d)) ∧
            Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℂ) := by
    rw [gold_cutoffDiff_eq_pairCard z y ε₀ j Nf M a b X
      (fun v => IsUnit ((v : ℕ) : ZMod d)) (Tlo) (Thi) hT]
    exact_mod_cast goldBlockBox_windowed_pair_card
      (fun v => Tlo < v ∧ v ≤ Thi ∧
        IsUnit ((v : ℕ) : ZMod d)) hz hbX hord hPwinU
  -- unfold the two carriers (definitional), rearrange, and substitute.
  have hexpx : apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
        (blockPrimeInd Nf) X M R₀ d (Thi)
      = (∑ m ∈ Finset.Icc 1 X,
          ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd Nf n else 0)
        - (1 / (d.totient : ℂ)) *
          (∑ m ∈ Finset.Icc 1 X,
            ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Thi),
            if IsUnit ((m * n : ℕ) : ZMod d) then
              restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd Nf n else 0) :=
    rfl
  have hexplo : apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
        (blockPrimeInd Nf) X M R₀ d (Tlo)
      = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd Nf n else 0)
        - (1 / (d.totient : ℂ)) *
          (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ Tlo),
            if IsUnit ((m * n : ℕ) : ZMod d) then
              restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd Nf n else 0) :=
    rfl
  rw [hexpx, hexplo]
  rw [show ∀ (r1 u1 r2 u2 : ℂ),
      (r1 - (1 / (d.totient : ℂ)) * u1) - (r2 - (1 / (d.totient : ℂ)) * u2)
        = (r1 - r2) - (1 / (d.totient : ℂ)) * (u1 - u2) from fun r1 u1 r2 u2 => by ring]
  rw [hRes, hUnit]

/-! ## Part F — the annulus instance, the outer telescoping sum, and the consumable form -/

open Classical in
/-- **`goldBlockBox_windowDisc_eq_res_annulus` — the dyadic-annulus instance.**  The general
identification at the factor-2 endpoints `Tlo = goldCut Ne k`, `Thi = goldCut Ne (k+1)`.  Each
annulus satisfies `dyadicBoundary_card_le_three`'s `hT` (`goldCut_succ_le_two_mul`), so G-SW2 may
price it by `box_disc_three_way`; `hNe : 2 ≤ Ne` supplies `1 ≤ goldCut Ne k`. -/
theorem goldBlockBox_windowDisc_eq_res_annulus {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M a b X d R₀ : ℕ}
    (hNe : 2 ≤ Ne) (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * Nf + 1) (k : ℕ) :
    apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd Nf) X M R₀ d
        (goldCut Ne (k + 1))
      - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd Nf) X M R₀ d
          (goldCut Ne k)
      = (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            (goldCut Ne k < prod3 t ∧ prod3 t ≤ goldCut Ne (k + 1) ∧
              ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) ∧
            Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℂ)
        - (1 / (d.totient : ℂ)) *
          (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            (goldCut Ne k < prod3 t ∧ prod3 t ≤ goldCut Ne (k + 1) ∧
              IsUnit ((prod3 t : ℕ) : ZMod d)) ∧
            Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℂ) :=
  goldBlockBox_windowDisc_eq_res hz hbX hord (goldCut Ne k) (goldCut Ne (k + 1))
    (one_le_goldCut hNe k) (goldCut_le_half Ne (k + 1)) (goldCut_mono Ne (Nat.le_succ k))

/-- **`goldWindowDisc_le_annulus_sum` — the outer telescoping sum (the O(log N) interface).**  Per
`d ∈ Dset` the full-window carrier difference at `(goldCut Ne 0, goldCut Ne (K+1)]` telescopes into
the `K+1` annulus differences (`Finset.sum_range_sub`); the triangle inequality and a sum swap
bound the `Dset`-sum of full-window discrepancies by the `Σ_k Σ_d` of annulus discrepancies.  At
`K = ⌊log₂ Ne⌋` the outer endpoints ARE the whole window `(1, Ne/2]` (via `goldCut_top`,
`goldCut_zero`).  Each inner `∑_d ‖annulus_k‖` is priced by G-SW2 via `box_disc_three_way`, so the
interface carries EXACTLY one extra `log` — consumed by taking the BV backbone at `A+1`. -/
theorem goldWindowDisc_le_annulus_sum (Ne : ℕ) (α β : ℕ → ℂ) (X M : ℕ)
    (r : ℕ → ℕ) (Dset : Finset ℕ) (K : ℕ) :
    (∑ d ∈ Dset, ‖apDiscBilinCutoff α β X M (r d) d (goldCut Ne (K + 1))
        - apDiscBilinCutoff α β X M (r d) d (goldCut Ne 0)‖)
      ≤ ∑ k ∈ Finset.range (K + 1), ∑ d ∈ Dset,
          ‖apDiscBilinCutoff α β X M (r d) d (goldCut Ne (k + 1))
            - apDiscBilinCutoff α β X M (r d) d (goldCut Ne k)‖ := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro d _
  rw [(Finset.sum_range_sub
    (fun k => apDiscBilinCutoff α β X M (r d) d (goldCut Ne k)) (K + 1)).symm]
  exact norm_sum_le _ _

/-! ## Part G — the count-level box honest disc and the consumable reassembly (Φ_k glue) -/

open Classical in
/-- **`goldBlockBoxResCount`** — block-`j` `goldTripleSet` triples with `prod3 ≡ R₀ (mod d)`,
`Nf < p₃ ≤ M`, `a ≤ p₁p₂ < b` (NO explicit window — the `[2, Ne/2]` window is `goldTripleSet`'s). -/
noncomputable def goldBlockBoxResCount (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M a b d R₀ : ℕ) : ℝ :=
  (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
      ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) ∧
      Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℝ)

open Classical in
/-- **`goldBlockBoxUnitCount`** — the same box with `prod3` a UNIT mod `d`. -/
noncomputable def goldBlockBoxUnitCount (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M a b d : ℕ) : ℝ :=
  (((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
      IsUnit ((prod3 t : ℕ) : ZMod d) ∧
      Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℝ)

/-- **`goldBlockBoxHonestDisc`** — the box's honest residue-class discrepancy against the coprime
main term (`goldTripleSet` mirror of `Salt.Chen.blockBoxHonestDisc`). -/
noncomputable def goldBlockBoxHonestDisc (Ne z y : ℕ) (ε₀ : ℝ) (j Nf M a b d R₀ : ℕ) : ℝ :=
  goldBlockBoxResCount Ne z y ε₀ j Nf M a b d R₀
    - nuChen d * goldBlockBoxUnitCount Ne z y ε₀ j Nf M a b d

open Classical in
/-- **`goldBlockBoxHonestDisc_eq_carrier` — the full-window identification.**  The box honest disc
IS the difference of the two one-sided cutoff carriers at the whole window `(1, Ne/2]`
(`goldBlockBox_windowDisc_eq_res` at `Tlo = 1`, `Thi = Ne/2`), the window `1 < prod3 ≤ Ne/2` being
redundant on `goldTripleSet` (`2 ≤ prod3 ≤ Ne/2` built in).  This is the count-level anchor the
outer sum consumes. -/
theorem goldBlockBoxHonestDisc_eq_carrier {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M a b X d R₀ : ℕ}
    (hNe : 2 ≤ Ne) (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * Nf + 1) :
    ((goldBlockBoxHonestDisc Ne z y ε₀ j Nf M a b d R₀ : ℝ) : ℂ)
      = apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd Nf) X M R₀ d
          (Ne / 2)
        - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd Nf) X M R₀ d
            1 := by
  classical
  have hhalf : (1 : ℕ) ≤ Ne / 2 := by omega
  have hredR : ((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        (1 < prod3 t ∧ prod3 t ≤ Ne / 2 ∧
          ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) ∧
        Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card
      = ((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) ∧
        Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card := by
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
        Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card
      = ((goldTripleSet Ne z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        IsUnit ((prod3 t : ℕ) : ZMod d) ∧
        Nf < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card := by
    apply congrArg
    apply Finset.filter_congr
    intro t ht
    rw [goldTripleSet, Finset.mem_filter] at ht
    obtain ⟨_, _, _, _, _, _, _, _, hwlo, hwhi⟩ := ht
    constructor
    · rintro ⟨h1, ⟨_, _, hr⟩, hrest⟩; exact ⟨h1, hr, hrest⟩
    · rintro ⟨h1, hr, hrest⟩; exact ⟨h1, ⟨by omega, hwhi, hr⟩, hrest⟩
  rw [goldBlockBox_windowDisc_eq_res hz hbX hord 1 (Ne / 2) (le_refl 1) (le_refl (Ne / 2)) hhalf,
    goldBlockBoxHonestDisc, goldBlockBoxResCount, goldBlockBoxUnitCount, nuChen_apply, hredR, hredU]
  push_cast
  ring

/-- **`goldBoxHonestDisc_le_annulus_sum` — the consumable form (the byte-lock for G-SW2).**  The
`Dset`-sum of box honest discrepancies is bounded by the `(annulus × Dset)` double sum of the
per-annulus carrier differences: `goldBlockBoxHonestDisc_eq_carrier` anchors each `|·|` to the
full-window carrier difference at `(1, Ne/2] = (goldCut Ne 0, goldCut Ne (⌊log₂ Ne⌋+1)]`, which
`goldWindowDisc_le_annulus_sum` telescopes.  This is the exact `hHD_of_box_discW` slot G-SW2's
`hNum_at_opW` mirror composes with `box_disc_three_way` — with the extra `Σ_{k ≤ log₂ Ne}` (the
one log Opt-A pays) made explicit. -/
theorem goldBoxHonestDisc_le_annulus_sum {Ne z y : ℕ} {ε₀ : ℝ} {j Nf M a b X : ℕ}
    (r : ℕ → ℕ) (Dset : Finset ℕ)
    (hNe : 2 ≤ Ne) (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * Nf + 1) :
    (∑ d ∈ Dset, |goldBlockBoxHonestDisc Ne z y ε₀ j Nf M a b d (r d)|)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 Ne + 1), ∑ d ∈ Dset,
          ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd Nf) X M
                (r d) d (goldCut Ne (k + 1))
            - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd Nf) X M
                (r d) d (goldCut Ne k)‖ := by
  have hstep : ∀ d ∈ Dset, |goldBlockBoxHonestDisc Ne z y ε₀ j Nf M a b d (r d)|
      = ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd Nf) X M
            (r d) d (goldCut Ne (Nat.log 2 Ne + 1))
          - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd Nf) X M
              (r d) d (goldCut Ne 0)‖ := by
    intro d _
    rw [goldCut_top hNe, goldCut_zero hNe,
      ← goldBlockBoxHonestDisc_eq_carrier (X := X) (R₀ := r d) hNe hz hbX hord,
      Complex.norm_real, Real.norm_eq_abs]
  rw [Finset.sum_congr rfl hstep]
  exact goldWindowDisc_le_annulus_sum Ne (restrictAlpha (blockAlpha z y ε₀ j) a b)
    (blockPrimeInd Nf) X M r Dset (Nat.log 2 Ne)

end Salt.Goldbach
