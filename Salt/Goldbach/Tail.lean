/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.OpPlumb
import Salt.Goldbach.Op

/-!
# G-TAIL — the LIVE-LOW crude harmonic tail (Goldbach terminal, part I)

The corrected design (pilot ledger ~07:30): the LIVE-LOW tail — the annuli where the wide window
`√(X·M)/L^18` falls below the operating conductor, so `gold_box_rows_wide`'s `hDwide` cannot be met
— closes NOT on any smooth-divisor estimate but on the CRUDE HARMONIC BOUND.  For a single fixed
modulus the one-sided windowed AP discrepancy carrier is bounded by elementary residue-class
counting; summed over the `QImage` moduli up to the conductor it is a harmonic sum that lands well
inside the `htail` budget at the tower margins.

This file lands:

* **`gold_box_disc_trivial`** (item 1) — the per-modulus trivial bound
  `‖apDiscBilinCutoff α β X Y R d T‖ ≤ 2·X·Y/d + 2·Y` for `‖α‖,‖β‖ ≤ 1`, `R` coprime to `d ≥ 1`.
  The residue count uses that `R` a unit forces the contributing `n` coprime to `d`, so each fixed
  `n`-fibre is a single residue class mod `d` (≤ `X/d+1` values); the unit main term cancels the
  `1/φ(d)` weight against the period bound on coprime `m`-counts.  Additive constant `C = 0`.

The `QImage` harmonic sum (item 2) and the terminal instantiation (item 3) are in `Tail2.lean`.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 0. Elementary interval counting helpers -/

/-- Numbers in `[1, X]` in a single residue class mod `d` number at most `X/d + 1`
(the map `m ↦ m / d` is injective on a fixed residue class). -/
private lemma card_Icc_filter_mod_le {X d : ℕ} (c : ℕ) :
    ((Finset.Icc 1 X).filter (fun m => m % d = c)).card ≤ X / d + 1 := by
  classical
  have h : ((Finset.Icc 1 X).filter (fun m => m % d = c)).card
      ≤ (Finset.range (X / d + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun m => m / d)
    · intro m hm
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
      simp only [Finset.mem_coe, Finset.mem_range]
      have : m / d ≤ X / d := Nat.div_le_div_right hm.1.2
      omega
    · intro m₁ hm₁ m₂ hm₂ heq
      rw [Finset.mem_coe, Finset.mem_filter] at hm₁ hm₂
      have hqe : m₁ / d = m₂ / d := heq
      have h1 := Nat.div_add_mod m₁ d
      have h2 := Nat.div_add_mod m₂ d
      rw [hqe, hm₁.2] at h1
      rw [hm₂.2] at h2
      exact h1.symm.trans h2
  rwa [Finset.card_range] at h

/-- Numbers in `[1, X]` coprime to `d` number at most `(X/d + 1)·φ(d)` (map `m ↦ (m/d, m%d)`
into `range (X/d+1) ×ˢ {residues coprime to d}`). -/
private lemma card_Icc_filter_coprime_le {X d : ℕ} (hd : 0 < d) :
    ((Finset.Icc 1 X).filter (fun m => Nat.Coprime m d)).card ≤ (X / d + 1) * d.totient := by
  classical
  have hcop : ((Finset.range d).filter (fun c => Nat.Coprime c d)).card = d.totient := by
    have hcongr : (Finset.range d).filter (fun c => Nat.Coprime c d)
        = (Finset.range d).filter (fun a => Nat.Coprime d a) := by
      apply Finset.filter_congr; intro c _; rw [Nat.coprime_comm]
    rw [hcongr]; exact (Nat.totient_eq_card_coprime d).symm
  have htarget : (Finset.range (X / d + 1) ×ˢ
      (Finset.range d).filter (fun c => Nat.Coprime c d)).card = (X / d + 1) * d.totient := by
    rw [Finset.card_product, Finset.card_range, hcop]
  rw [← htarget]
  apply Finset.card_le_card_of_injOn (fun m => (m / d, m % d))
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · have : m / d ≤ X / d := Nat.div_le_div_right hm.1.2; omega
    · exact Nat.mod_lt _ hd
    · have hg : Nat.gcd (m % d) d = Nat.gcd m d := by rw [← Nat.gcd_rec, Nat.gcd_comm]
      exact hg.trans hm.2
  · intro m₁ hm₁ m₂ hm₂ heq
    have hqe : m₁ / d = m₂ / d := congrArg Prod.fst heq
    have hre : m₁ % d = m₂ % d := congrArg Prod.snd heq
    have h1 := Nat.div_add_mod m₁ d
    have h2 := Nat.div_add_mod m₂ d
    rw [hqe, hre] at h1
    exact h1.symm.trans h2

/-! ## 1. The two windowed carrier legs -/

/-- The residue-class leg: with `R` coprime to `d`, only `n` coprime to `d` contribute, and each
fixed-`n` fibre lies in a single residue class mod `d` — so the count is `≤ Y·(X/d + 1)`. -/
private lemma norm_res_sum_le {α β : ℕ → ℂ} {X Y R d T : ℕ}
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) (hcop : Nat.Coprime R d) :
    ‖∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
        (if ((m * n : ℕ) : ZMod d) = (R : ZMod d) then α m * β n else 0)‖
      ≤ (Y : ℝ) * ((X : ℝ) / d + 1) := by
  classical
  have hbound : ∀ m n : ℕ,
      ‖(if ((m * n : ℕ) : ZMod d) = (R : ZMod d) then α m * β n else 0)‖
        ≤ (if ((m * n : ℕ) : ZMod d) = (R : ZMod d) then (1 : ℝ) else 0) := by
    intro m n
    by_cases h : ((m * n : ℕ) : ZMod d) = (R : ZMod d)
    · rw [if_pos h, if_pos h, norm_mul]
      nlinarith [hα m, hβ n, norm_nonneg (α m), norm_nonneg (β n)]
    · rw [if_neg h, if_neg h, norm_zero]
  calc ‖∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
          (if ((m * n : ℕ) : ZMod d) = (R : ZMod d) then α m * β n else 0)‖
      ≤ ∑ m ∈ Finset.Icc 1 X, ‖∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
            (if ((m * n : ℕ) : ZMod d) = (R : ZMod d) then α m * β n else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
            (if ((m * n : ℕ) : ZMod d) = (R : ZMod d) then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun m _ => le_trans (norm_sum_le _ _)
          (Finset.sum_le_sum (fun n _ => hbound m n)))
    _ ≤ ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
            (if ((m * n : ℕ) : ZMod d) = (R : ZMod d) then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun m _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun n _ _ => by positivity))
    _ = ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 X,
            (if ((m * n : ℕ) : ZMod d) = (R : ZMod d) then (1 : ℝ) else 0) := Finset.sum_comm
    _ ≤ ∑ _n ∈ Finset.Icc 1 Y, ((X : ℝ) / d + 1) := Finset.sum_le_sum (fun n _ => ?_)
    _ = (Y : ℝ) * ((X : ℝ) / d + 1) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  -- fixed-`n` fibre bound
  rw [Finset.sum_boole]
  by_cases hne : ((Finset.Icc 1 X).filter
      (fun m => ((m * n : ℕ) : ZMod d) = (R : ZMod d))).Nonempty
  · obtain ⟨m₀, hm₀⟩ := hne
    rw [Finset.mem_filter] at hm₀
    have hRunit : IsUnit ((R : ZMod d)) := by rw [ZMod.isUnit_iff_coprime]; exact hcop
    have hnunit : IsUnit ((n : ZMod d)) := by
      have hu : IsUnit ((m₀ : ZMod d) * (n : ZMod d)) := by
        rw [← Nat.cast_mul, hm₀.2]; exact hRunit
      exact ((Commute.all _ _).isUnit_mul_iff.mp hu).2
    have hsub : (Finset.Icc 1 X).filter
          (fun m => ((m * n : ℕ) : ZMod d) = (R : ZMod d))
        ⊆ (Finset.Icc 1 X).filter (fun m => m % d = m₀ % d) := by
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      refine ⟨hm.1, ?_⟩
      have hmm : (m : ZMod d) * (n : ZMod d) = (m₀ : ZMod d) * (n : ZMod d) := by
        rw [← Nat.cast_mul, ← Nat.cast_mul, hm.2, hm₀.2]
      have heqm : (m : ZMod d) = (m₀ : ZMod d) := (hnunit.mul_left_inj).mp hmm
      rwa [ZMod.natCast_eq_natCast_iff'] at heqm
    calc (((Finset.Icc 1 X).filter
            (fun m => ((m * n : ℕ) : ZMod d) = (R : ZMod d))).card : ℝ)
        ≤ (((Finset.Icc 1 X).filter (fun m => m % d = m₀ % d)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((X / d + 1 : ℕ) : ℝ) := by exact_mod_cast card_Icc_filter_mod_le (m₀ % d)
      _ ≤ (X : ℝ) / d + 1 := by
          have hcd : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / d := Nat.cast_div_le
          push_cast; linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty, Nat.cast_zero]; positivity

open Classical in
/-- The unit main-term leg: the fibre over each `n` lies in `{m coprime to d}`, whose count is
`≤ (X/d + 1)·φ(d)`; the `1/φ(d)` weight later cancels the `φ(d)`. -/
private lemma norm_unit_sum_le {α β : ℕ → ℂ} {X Y d T : ℕ}
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) (hd : 0 < d) :
    ‖∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
        (if IsUnit ((m * n : ℕ) : ZMod d) then α m * β n else 0)‖
      ≤ (Y : ℝ) * (((X : ℝ) / d + 1) * d.totient) := by
  classical
  have hbound : ∀ m n : ℕ,
      ‖(if IsUnit ((m * n : ℕ) : ZMod d) then α m * β n else 0)‖
        ≤ (if IsUnit ((m * n : ℕ) : ZMod d) then (1 : ℝ) else 0) := by
    intro m n
    by_cases h : IsUnit ((m * n : ℕ) : ZMod d)
    · rw [if_pos h, if_pos h, norm_mul]
      nlinarith [hα m, hβ n, norm_nonneg (α m), norm_nonneg (β n)]
    · rw [if_neg h, if_neg h, norm_zero]
  calc ‖∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
          (if IsUnit ((m * n : ℕ) : ZMod d) then α m * β n else 0)‖
      ≤ ∑ m ∈ Finset.Icc 1 X, ‖∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
            (if IsUnit ((m * n : ℕ) : ZMod d) then α m * β n else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
            (if IsUnit ((m * n : ℕ) : ZMod d) then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun m _ => le_trans (norm_sum_le _ _)
          (Finset.sum_le_sum (fun n _ => hbound m n)))
    _ ≤ ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
            (if IsUnit ((m * n : ℕ) : ZMod d) then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun m _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun n _ _ => by positivity))
    _ = ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 X,
            (if IsUnit ((m * n : ℕ) : ZMod d) then (1 : ℝ) else 0) := Finset.sum_comm
    _ ≤ ∑ _n ∈ Finset.Icc 1 Y, ((X : ℝ) / d + 1) * d.totient :=
        Finset.sum_le_sum (fun n _ => ?_)
    _ = (Y : ℝ) * (((X : ℝ) / d + 1) * d.totient) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  -- fixed-`n` fibre bound
  rw [Finset.sum_boole]
  have hsub : (Finset.Icc 1 X).filter (fun m => IsUnit ((m * n : ℕ) : ZMod d))
      ⊆ (Finset.Icc 1 X).filter (fun m => Nat.Coprime m d) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    refine ⟨hm.1, ?_⟩
    have hc : Nat.Coprime (m * n) d := (ZMod.isUnit_iff_coprime (m * n) d).mp hm.2
    exact (Nat.coprime_mul_iff_left.mp hc).1
  calc (((Finset.Icc 1 X).filter (fun m => IsUnit ((m * n : ℕ) : ZMod d))).card : ℝ)
      ≤ (((Finset.Icc 1 X).filter (fun m => Nat.Coprime m d)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (((X / d + 1) * d.totient : ℕ) : ℝ) := by exact_mod_cast card_Icc_filter_coprime_le hd
    _ ≤ ((X : ℝ) / d + 1) * d.totient := by
        have hcd : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / d := Nat.cast_div_le
        have hφ : (0 : ℝ) ≤ (d.totient : ℝ) := by positivity
        push_cast; nlinarith [hcd, hφ]

/-! ## 2. The per-modulus trivial discrepancy bound (item 1) -/

set_option maxHeartbeats 800000 in
-- The `apDiscBilinCutoff` unfold plus the two carrier-leg bounds and the `φ(d)`-cancelling
-- `field_simp`/`ring` close elaborate a long ℂ/ℝ norm chain; headroom above the default.
/-- **`gold_box_disc_trivial` (item 1).**  The crude per-modulus bound on the one-sided windowed AP
discrepancy carrier: for bounded coefficients `‖α‖, ‖β‖ ≤ 1`, modulus `d ≥ 1`, and residue `R`
coprime to `d`,
`‖apDiscBilinCutoff α β X Y R d T‖ ≤ 2·X·Y/d + 2·Y` (additive constant `C = 0`).  The residue leg
(`norm_res_sum_le`) and the `1/φ(d)`-weighted unit leg (`norm_unit_sum_le`, with the `φ(d)`
cancelled) each contribute `Y·(X/d + 1)`; the cutoff `T` is discarded (fewer terms). -/
theorem gold_box_disc_trivial {α β : ℕ → ℂ} {X Y R d T : ℕ}
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1)
    (hd : 1 ≤ d) (hcop : Nat.Coprime R d) :
    ‖apDiscBilinCutoff α β X Y R d T‖ ≤ 2 * ((X : ℝ) * Y / d) + 2 * Y := by
  have hd0 : 0 < d := hd
  have hφpos : (0 : ℝ) < (d.totient : ℝ) := by
    have := Nat.totient_pos.mpr hd0; exact_mod_cast this
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hφne : (d.totient : ℝ) ≠ 0 := ne_of_gt hφpos
  rw [apDiscBilinCutoff]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_mul, show ‖(1 / (d.totient : ℂ))‖ = 1 / (d.totient : ℝ) from by
    rw [norm_div, norm_one, RCLike.norm_natCast]]
  have hS1 := norm_res_sum_le (X := X) (Y := Y) (R := R) (d := d) (T := T) hα hβ hcop
  have hS2 := norm_unit_sum_le (X := X) (Y := Y) (d := d) (T := T) hα hβ hd0
  refine le_trans (add_le_add hS1 (mul_le_mul_of_nonneg_left hS2
    (show (0 : ℝ) ≤ 1 / (d.totient : ℝ) by positivity))) (le_of_eq ?_)
  field_simp
  ring

/-! ## 3. The `QImage` harmonic tail sum (item 2) -/

/-- `∑_{d ∈ [1, M]} 1/d = H_M`, the harmonic number, bridging `Finset.Icc` to `harmonic`. -/
private lemma sum_Icc_one_div_eq_harmonic (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 M, (1 / (d : ℝ))) = (harmonic M : ℝ) := by
  induction M with
  | zero => simp [harmonic_zero]
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), harmonic_succ, ih]
      push_cast
      ring

set_option maxHeartbeats 400000 in
-- The image reindex, the `1/d` harmonic close, and the interval-membership discharge elaborate a
-- long divisor/floor chain; headroom above the default.
/-- **`gold_box_tail_le` (item 2).**  The `QImage` harmonic tail: summing the item-1 trivial bound
`2·X·Y/m + 2·Y` over the moduli `m = Q·d` (`d ∣ Ps`, `d < bound`) lands at
`2·X·Y/Q·(1 + log bound) + 2·Y·bound`.  The `X·Y/m` legs contribute `(2·X·Y/Q)·∑_d 1/d`, and the
divisors below `bound` are DISTINCT integers in `[1, bound]`, so `∑_d 1/d ≤ H_{⌊bound⌋} ≤ 1 + log
bound`; the additive `2·Y` legs contribute `2·Y·#QImage ≤ 2·Y·bound`.  At op (`X·Y ≤ N^{1−2ε}`,
`bound ≈ N^{1/2}`) both terms sit well inside the `htail` budget at the tower margins. -/
theorem gold_box_tail_le (X Y Q Ps : ℕ) (bound : ℝ) (hQ : 1 ≤ Q) (hb : 1 ≤ bound) :
    (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
        (2 * ((X : ℝ) * Y / m) + 2 * Y))
      ≤ 2 * (X : ℝ) * Y / Q * (1 + Real.log bound) + 2 * Y * bound := by
  classical
  set S := (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound) with hSdef
  have hb0 : (0 : ℝ) ≤ bound := le_trans zero_le_one hb
  have hsub : S ⊆ Finset.Icc 1 ⌊bound⌋₊ := by
    intro d hd
    rw [hSdef, Finset.mem_filter] at hd
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_floor (le_of_lt hd.2)⟩
  -- reindex the image sum to the divisor sum
  rw [Finset.sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left (by omega) hxy)]
  rw [Finset.sum_add_distrib]
  -- part A: the harmonic legs
  have hAeq : (∑ d ∈ S, 2 * ((X : ℝ) * Y / ((Q * d : ℕ) : ℝ)))
      = (2 * (X : ℝ) * Y / Q) * (∑ d ∈ S, (1 / (d : ℝ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    push_cast; ring
  have hharm : (∑ d ∈ S, (1 / (d : ℝ))) ≤ 1 + Real.log bound := by
    calc (∑ d ∈ S, (1 / (d : ℝ)))
        ≤ ∑ d ∈ Finset.Icc 1 ⌊bound⌋₊, (1 / (d : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      _ = (harmonic ⌊bound⌋₊ : ℝ) := sum_Icc_one_div_eq_harmonic _
      _ ≤ 1 + Real.log bound := harmonic_floor_le_one_add_log bound hb
  have hApos : (0 : ℝ) ≤ 2 * (X : ℝ) * Y / Q := by positivity
  have hA : (∑ d ∈ S, 2 * ((X : ℝ) * Y / ((Q * d : ℕ) : ℝ)))
      ≤ 2 * (X : ℝ) * Y / Q * (1 + Real.log bound) := by
    rw [hAeq]; exact mul_le_mul_of_nonneg_left hharm hApos
  -- part B: the additive legs
  have hcardS : (S.card : ℝ) ≤ bound := by
    calc (S.card : ℝ) ≤ ((Finset.Icc 1 ⌊bound⌋₊).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = (⌊bound⌋₊ : ℝ) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
      _ ≤ bound := Nat.floor_le hb0
  have hB : (∑ _d ∈ S, (2 * (Y : ℝ))) ≤ 2 * Y * bound := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hY0 : (0 : ℝ) ≤ 2 * (Y : ℝ) := by positivity
    calc (S.card : ℝ) * (2 * Y) ≤ bound * (2 * Y) := mul_le_mul_of_nonneg_right hcardS hY0
      _ = 2 * Y * bound := by ring
  exact add_le_add hA hB

end Salt.Goldbach
