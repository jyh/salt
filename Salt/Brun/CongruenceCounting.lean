/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# Counting congruence classes in an interval (helper for blueprint N2.4)

A general-purpose lemma: for a set of residues `S` modulo `d`, the count of
`n ∈ Icc 1 N` with `n % d ∈ S` differs from the "expected" value `N * |S| / d`
by at most `|S|`. Proved via a block decomposition (each length-`d` block of
consecutive integers hits every residue exactly once) plus a base case for
the leftover partial block.
-/

open Finset

variable (d : ℕ) (S : Finset ℕ)

/-- Any `d` consecutive naturals hit every residue mod `d` exactly once. -/
lemma block_mod_bij (N d : ℕ) (hd : 0 < d) :
    ((Finset.Ico (N + 1) (N + 1 + d)).image (· % d)) = Finset.range d := by
  have hinj : Set.InjOn (· % d) (Finset.Ico (N + 1) (N + 1 + d) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    simp only at hab
    rcases le_total a b with h | h
    · have hdvd : d ∣ (b - a) := (Nat.modEq_iff_dvd' h).mp hab
      have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
    · have hdvd : d ∣ (a - b) := (Nat.modEq_iff_dvd' h).mp hab.symm
      have : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
  have hcard : ((Finset.Ico (N + 1) (N + 1 + d)).image (· % d)).card = d := by
    rw [Finset.card_image_of_injOn hinj, Nat.card_Ico]
    omega
  have hsub : ((Finset.Ico (N + 1) (N + 1 + d)).image (· % d)) ⊆ Finset.range d := by
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨n, _, rfl⟩ := hr
    simp [Nat.mod_lt _ hd]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])

/-- Count of `n ∈ [1,N]` with `n % d ∈ S`. -/
def congCount (N : ℕ) : ℕ := ((Finset.Icc 1 N).filter (fun n => n % d ∈ S)).card

lemma block_count (hd : 0 < d) (N : ℕ) :
    ((Finset.Ico (N + 1) (N + 1 + d)).filter (fun n => n % d ∈ S)).card
      = (S ∩ Finset.range d).card := by
  apply Finset.card_bij (fun n _ => n % d)
  · intro n hn
    simp only [Finset.mem_filter] at hn
    simp only [Finset.mem_inter, Finset.mem_range]
    exact ⟨hn.2, Nat.mod_lt _ hd⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha hb
    rcases le_total a b with h | h
    · have hdvd : d ∣ (b - a) := (Nat.modEq_iff_dvd' h).mp hab
      have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
    · have hdvd : d ∣ (a - b) := (Nat.modEq_iff_dvd' h).mp hab.symm
      have : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
  · intro r hr
    simp only [Finset.mem_inter, Finset.mem_range] at hr
    have hex : r ∈ (Finset.Ico (N + 1) (N + 1 + d)).image (· % d) := by
      rw [block_mod_bij N d hd]; simp [hr.2]
    simp only [Finset.mem_image] at hex
    obtain ⟨n, hn, hnr⟩ := hex
    exact ⟨n, by simp only [Finset.mem_filter]; exact ⟨hn, hnr ▸ hr.1⟩, hnr⟩

lemma congCount_step (hd : 0 < d) (N : ℕ) :
    congCount d S (N + d) = congCount d S N + (S ∩ Finset.range d).card := by
  unfold congCount
  have hsplit : Finset.Icc 1 (N + d) = Finset.Icc 1 N ∪ Finset.Ico (N + 1) (N + 1 + d) := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Ico (N + 1) (N + 1 + d)) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_Ico] at hn'
    omega
  rw [hsplit, Finset.filter_union,
    Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  rw [block_count d S hd N]

lemma congCount_telescoping (hd : 0 < d) (q s : ℕ) :
    congCount d S (q * d + s) = q * (S ∩ Finset.range d).card + congCount d S s := by
  induction q with
  | zero => simp
  | succ q ih =>
    have heq : (q + 1) * d + s = (q * d + s) + d := by ring
    rw [heq, congCount_step d S hd (q * d + s), ih]
    ring

lemma congCount_base_bound (_hd : 0 < d) (s : ℕ) (hs : s < d) :
    (congCount d S s : ℝ) ≤ (S ∩ Finset.range d).card := by
  unfold congCount
  have hsub : (Finset.Icc 1 s).filter (fun n => n % d ∈ S) ⊆ S ∩ Finset.range d := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    simp only [Finset.mem_inter, Finset.mem_range]
    have : n % d = n := Nat.mod_eq_of_lt (by omega)
    rw [this] at hn
    exact ⟨hn.2, by omega⟩
  exact_mod_cast Finset.card_le_card hsub

/-- Pure real-arithmetic core of the bound, isolated from the `Finset`/`Nat` bookkeeping. -/
lemma congCount_pure_bound (d k q s gs : ℝ) (hd : 0 < d) (hs0 : 0 ≤ s) (hsd : s < d)
    (hk0 : 0 ≤ k) (hgs0 : 0 ≤ gs) (hgsk : gs ≤ k) :
    |(q * k + gs) - (q * d + s) * k / d| ≤ k := by
  have expand : (q * k + gs) - (q * d + s) * k / d = gs - s * k / d := by
    field_simp; ring
  rw [expand, abs_le]
  constructor
  · nlinarith [div_le_iff₀ hd |>.mpr (show s * k ≤ k * d by nlinarith)]
  · have : 0 ≤ s * k / d := by positivity
    linarith

/-- N2.4 (general form): for any residue set `S` mod `d`, the count of
`n ∈ Icc 1 N` with `n % d ∈ S` differs from `N * |S ∩ range d| / d` by at most
`|S ∩ range d|`. -/
theorem congCount_bound (hd : 0 < d) (N : ℕ) :
    |(congCount d S N : ℝ) - N * (S ∩ Finset.range d).card / d| ≤ (S ∩ Finset.range d).card := by
  have hNqs : N = (N / d) * d + N % d := by rw [Nat.div_add_mod']
  have hslt : N % d < d := Nat.mod_lt _ hd
  have hgeq : congCount d S N = (N / d) * (S ∩ Finset.range d).card + congCount d S (N % d) := by
    conv_lhs => rw [hNqs]
    exact congCount_telescoping d S hd (N / d) (N % d)
  have hgbound : (congCount d S (N % d) : ℝ) ≤ (S ∩ Finset.range d).card :=
    congCount_base_bound d S hd _ hslt
  have h1 : (congCount d S N : ℝ)
      = (N / d : ℕ) * (S ∩ Finset.range d).card + congCount d S (N % d) := by
    exact_mod_cast hgeq
  have h2 : (N : ℝ) = (N / d : ℕ) * (d : ℝ) + (N % d : ℕ) := by exact_mod_cast hNqs
  rw [h1, h2]
  exact congCount_pure_bound d (S ∩ Finset.range d).card ((N / d : ℕ) : ℝ) ((N % d : ℕ) : ℝ)
    (congCount d S (N % d)) (by exact_mod_cast hd) (Nat.cast_nonneg _) (by exact_mod_cast hslt)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hgbound
