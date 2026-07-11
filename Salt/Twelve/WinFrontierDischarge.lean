/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.WinCore

/-!
# W5-7 — discharging the `WinFrontier` largeness bundle

Design: `docs/blueprints/explicit12-design.md`, wave-5 card W5-6/W5-7 and the
"Error budget" section; the W5-7 flag in `docs/blueprints/flags.md`.

`gaps_le_twelve_of_inner` (`Salt/Twelve/WinCore.lean`) is conditional on the
`WinFrontier (primorial Dstar)` hypothesis `hFrontier` — the `∀ᶠ N` largeness
bundle `WindowPNT → EHall → ∀ N, ∃ N' ≥ N, [9 analytic conjuncts]`.  This file
lands the discharge as a mirror of `Salt.Maynard.analyticFrontier_lod` at level
`θ★`.

The canonical wave-5 witnesses:

* `R := ⌊N'^{1999/4000}⌋₊`  (the `θ★/2` window exponent);
* `ν₀ := (exists_nu0W 5 (primorial Dstar) …).choose`  (CRT residue base);
* `δ := (63 − 1/100)·N'/log N' − 19`  (`WindowPNT` prime supply, `hSeq ≤ 19`);
* `cval m := Qdiag_mW 5 R (primorial Dstar) m (yF R (primorial Dstar) Fstar1)`
  (the full S₂ diagonal — conjunct 5 is then `le_refl`, conjunct 3 is the
  sum-of-squares nonnegativity via `qdiag_eq_yMsq_sum`);
* `errEH m :=`  the `S2mW_ge_compatMain_theta_uniform` residual `C₀·…` folded
  with the collision difference `Δπ/φW'·(Qdiag − s2CompatForm)` so conjunct 6
  is an exact consequence of `S2mW_ge_compatMain_theta_uniform`.

Conjuncts 1–6 and the `∀ᶠ` threshold assembly are discharged concretely from
the landed lemmas.  The assembled ratio-slack (conjunct 7, `WinSlack`) is the
`win_ratio_core` + error-budget content; it is carried here as the explicit
`∀ᶠ`-hypothesis of `winFrontier_of` (its full discharge — threading
`mv_I_split`/`qdiag_bridge` mains below `win_ratio_core`'s certified margin — is
FABLE-QUEUE'd; see the W5-7 flag).
-/

namespace Salt.Twelve

open Salt.Maynard
open Finset Filter

/-! ## Local helpers -/

private lemma prod_primes_sqf {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hap : a.Prime := hs a (Finset.mem_insert_self a s)
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hap (hsp p hp)).mpr (by rintro rfl; exact ha hp)
    rw [Nat.squarefree_mul_iff]
    exact ⟨hcop, hap.squarefree, ih hsp⟩

private lemma primorial_sqf (D : ℕ) : Squarefree (primorial D) := by
  unfold primorial
  exact prod_primes_sqf (fun p hp => (Finset.mem_filter.mp hp).2)

private lemma primorial_pos' (D : ℕ) : 0 < primorial D := by
  unfold primorial
  exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)

private lemma hSeq_lt_Dstar' (i : Fin 5) : hSeq 5 i < Dstar := by
  unfold Dstar
  fin_cases i <;>
    simp only [hSeq_five_zero, hSeq_five_one, hSeq_five_two, hSeq_five_three,
      hSeq_five_four] <;>
    norm_num

private lemma hSeq_le_nineteen (i : Fin 5) : hSeq 5 i ≤ 19 := by
  fin_cases i <;>
    simp only [hSeq_five_zero, hSeq_five_one, hSeq_five_two, hSeq_five_three,
      hSeq_five_four] <;>
    norm_num

/-- Non-collision pairs have pairwise-coprime lcm coordinates (free `W'`; the
private `lcmPairwiseCoprimeW` of `S2CompatEHW.lean` reproved for `Fin 5`). -/
private lemma lcm_pairwise_coprime_of_noncollision {R W' : ℕ} {d e : Fin 5 → ℕ}
    (hd : d ∈ kSieveIndex 5 R W') (he : e ∈ kSieveIndex 5 R W')
    (hcompat : ¬ IsCollisionPair d e) {i j : Fin 5} (hij : i ≠ j) :
    Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j)) := by
  obtain ⟨-, hdcop, -, -⟩ := (mem_kSieveIndex_iff d).mp hd
  obtain ⟨-, hecop, -, -⟩ := (mem_kSieveIndex_iff e).mp he
  have hnc : ∀ a b : Fin 5, a ≠ b → Nat.Coprime (d a) (e b) := by
    intro a b hab
    by_contra h
    exact hcompat ⟨a, b, hab, h⟩
  apply Nat.coprime_of_dvd
  intro p hp hpi hpj
  have hi : p ∣ d i ∨ p ∣ e i := (Nat.Prime.dvd_mul hp).mp (hpi.trans (Nat.lcm_dvd_mul _ _))
  have hj : p ∣ d j ∨ p ∣ e j := (Nat.Prime.dvd_mul hp).mp (hpj.trans (Nat.lcm_dvd_mul _ _))
  rcases hi with hdi | hei <;> rcases hj with hdj | hej
  · exact absurd (hdcop i j hij) (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hdi, hdj⟩)
  · exact absurd (hnc i j hij) (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hdi, hej⟩)
  · exact absurd (hnc j i hij.symm) (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hdj, hei⟩)
  · exact absurd (hecop i j hij) (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hei, hej⟩)

/-! ## The assembled ratio-slack (conjunct 7 of `WinFrontier`) -/

/-- The assembled ratio-slack inequality (conjunct 7 of `WinFrontier`) at the
canonical wave-5 witnesses.  Parametrized by the `S2mW_ge_compatMain_theta_uniform`
residual constant `C₀` (so `winFrontier_of` can instantiate it after obtaining
the real `C₀`).  Carried as the `∀ᶠ`-hypothesis of `winFrontier_of`; its
discharge (`win_ratio_core` + the vanishing `mv_I_split`/`qdiag_bridge`/`herr`
error budget) is FABLE-QUEUE'd — see the W5-7 flag. -/
def WinSlack (C₀ : ℝ) (N' : ℕ) : Prop :=
  ((64 - 1) * (N' : ℝ) / (primorial Dstar))
      * ((1 + 12 * (5 : ℝ) ^ 2 / Dstar)
          * ∑ r ∈ kSieveIndex 5 (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial Dstar),
              (yF (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial Dstar) Fstar1 r) ^ 2
                / ∏ i, (Nat.totient (r i) : ℝ))
    + 2 ^ (5 + 1)
        * (∑ d ∈ kSieveIndex 5 (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial Dstar),
            |lam 5 (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial Dstar)
              (yF (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial Dstar) Fstar1) d|) ^ 2
    < (∑ m : Fin 5,
          ((63 - 1 / 100) * (N' : ℝ) / Real.log N' - 19)
              / (Nat.totient (primorial Dstar) : ℝ)
            * Qdiag_mW 5 (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial Dstar) m
                (yF (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial Dstar) Fstar1))
      - ∑ m : Fin 5,
          (deltaPi 5 64 N' m / (Nat.totient (primorial Dstar) : ℝ)
              * (Qdiag_mW 5 (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial Dstar) m
                    (yF (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial Dstar) Fstar1)
                - s2CompatFormM 5 (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial Dstar) m
                    (yF (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial Dstar) Fstar1))
            + C₀ * (1 + Real.log (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ)) ^ (2 * 5 + 2)
                * (N' : ℝ) / (Real.log N') ^ (2 * 5 + 4))

/-! ## `winFrontier_of` — the discharge modulo the slack hypothesis -/

/-- **W5-7 (modulo the FABLE-QUEUE'd slack).**  The `WinFrontier` largeness
bundle for `W' = primorial Dstar`, discharging conjuncts 1–6 and the `∀ᶠ`
threshold assembly concretely from the landed lemmas, and reducing conjunct 7 to
the explicit `∀ᶠ`-slack hypothesis `hslackEv` (the `win_ratio_core` +
error-budget content). -/
theorem winFrontier_of
    (hslackEv : ∀ C₀ : ℝ, 0 ≤ C₀ → ∀ᶠ N' : ℕ in atTop, WinSlack C₀ N') :
    WinFrontier (primorial Dstar) := by
  intro hPNT hEH N
  classical
  -- modulus facts
  have hW'sqf : Squarefree (primorial Dstar) := primorial_sqf Dstar
  have hW'pos : 0 < primorial Dstar := primorial_pos' Dstar
  have hW'ne : (primorial Dstar) ≠ 0 := hW'pos.ne'
  have hφW'pos : (0 : ℝ) < (Nat.totient (primorial Dstar) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hW'pos
  have hDle : ∀ p : ℕ, p.Prime → ¬ p ∣ primorial Dstar → Dstar ≤ p :=
    fun p hp hnd => le_of_lt (primorial_hDlt Dstar p hp hnd)
  have hSeqlt : ∀ i : Fin 5, hSeq 5 i < Dstar := hSeq_lt_Dstar'
  -- HasLevel θ₊ from EHall
  have hLoD : HasLevel (3999 / 4000) :=
    EH_hasLevel (EHall_hasEH hEH (by norm_num) (by norm_num))
  -- CRT residue base
  obtain ⟨ν₀, hν₀⟩ := exists_nu0W 5 (primorial Dstar) hW'ne
  -- the θ₊-level coupled-EH lemma (constants obtained before choosing N')
  obtain ⟨C₀, B', N₀eh, hC₀0, hB'0, hS2fun⟩ :=
    S2mW_ge_compatMain_theta_uniform 5 64 (primorial Dstar) Dstar (by norm_num)
      (by norm_num) hW'sqf hDle hSeqlt hLoD
  -- EH range threshold
  obtain ⟨Nr, hNrfun⟩ := EH_range_theta (primorial Dstar) hW'pos B' hB'0
  -- WindowPNT threshold (ε = 1/100)
  obtain ⟨Nc, hNc⟩ := eventually_atTop.mp (hPNT (1 / 100) (by norm_num))
  -- eventually `0 ≤ δ`
  have hδev : ∀ᶠ N' : ℕ in atTop,
      (19 : ℝ) ≤ (63 - 1 / 100) * (N' : ℝ) / Real.log N' := by
    have hev := eventually_poly_beats_polylog 1 1 1 (by norm_num)
    have hevN := tendsto_natCast_atTop_atTop.eventually hev
    filter_upwards [hevN, eventually_ge_atTop 2] with N' hN' hN2
    have hlogpos : 0 < Real.log N' := Real.log_pos (by exact_mod_cast (by omega : 1 < N'))
    simp only [pow_one, Real.rpow_one, one_mul] at hN'
    rw [le_div_iff₀ hlogpos]
    linarith [hN', hlogpos]
  -- combine every eventually fact
  have hcombined := (hslackEv C₀ hC₀0).and
    (hδev.and (eventually_ge_atTop (max (max Nr N₀eh) (max Nc 8))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hcombined
  set N' := max N₀ N with hN'def
  have hNleN' : N ≤ N' := le_max_right _ _
  have hN'geN₀ : N₀ ≤ N' := le_max_left _ _
  obtain ⟨hslack, hδ0', hgeThr⟩ := hN₀ N' hN'geN₀
  -- unpack thresholds
  have hNr' : Nr ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hgeThr
  have hN₀eh' : N₀eh ≤ N' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hgeThr
  have hNc' : Nc ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hgeThr
  have h8' : 8 ≤ N' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hgeThr
  have hN'8r : (8 : ℝ) ≤ (N' : ℝ) := by exact_mod_cast h8'
  have hN'pos : 0 < N' := by omega
  have hlogN'pos : 0 < Real.log N' := Real.log_pos (by exact_mod_cast (by omega : 1 < N'))
  -- R and its facts
  set R := ⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ with hRdef
  have hR2 : 2 ≤ R := R_ge_two_theta N' hN'8r
  have hRleN' : R ≤ N' := R_le_N'_theta N' (by omega)
  have hrange : primorial Dstar * R ^ 2
      ≤ ⌊(N' : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log N') ^ B'⌋₊ := by
    rw [hRdef]; exact hNrfun N' hNr'
  have hyabs : ∀ r, |yF R (primorial Dstar) Fstar1 r| ≤ 1 :=
    fun r => yF_Fstar1_abs_le_one R (primorial Dstar) r
  -- δ, cval, errEH
  set δ : ℝ := (63 - 1 / 100) * (N' : ℝ) / Real.log N' - 19 with hδdef
  set cval : Fin 5 → ℝ :=
    fun m => Qdiag_mW 5 R (primorial Dstar) m (yF R (primorial Dstar) Fstar1) with hcvaldef
  set errEH : Fin 5 → ℝ :=
    fun m => deltaPi 5 64 N' m / (Nat.totient (primorial Dstar) : ℝ)
          * (Qdiag_mW 5 R (primorial Dstar) m (yF R (primorial Dstar) Fstar1)
            - s2CompatFormM 5 R (primorial Dstar) m (yF R (primorial Dstar) Fstar1))
        + C₀ * (1 + Real.log R) ^ (2 * 5 + 2) * (N' : ℝ) / (Real.log N') ^ (2 * 5 + 4)
    with herrdef
  refine ⟨N', R, ν₀, δ, errEH, cval, hNleN', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- conjunct 1 : CRT collision-solvability
    intro d hd e he hcompat
    obtain ⟨hdsq, -, hdcopW, -⟩ := (mem_kSieveIndex_iff d).mp hd
    obtain ⟨hesq, -, hecopW, -⟩ := (mem_kSieveIndex_iff e).mp he
    exact cong_solvableW 5 (primorial Dstar) d e ν₀ hW'pos
      (fun i => Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hdsq i).ne_zero (hesq i).ne_zero))
      (fun i => ((hdcopW i).symm.mul_right (hecopW i).symm).coprime_dvd_right
        (Nat.lcm_dvd_mul (d i) (e i)))
      (fun i j hij => lcm_pairwise_coprime_of_noncollision hd he hcompat hij)
  · -- conjunct 2 : `0 < φ W'`
    exact hφW'pos
  · -- conjunct 3 : `0 ≤ cval m`
    intro m
    simp only [hcvaldef]
    rw [qdiag_eq_yMsq_sum]
    exact Finset.sum_nonneg
      (fun u _ => div_nonneg (sq_nonneg _)
        (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)))
  · -- conjunct 4a : `0 ≤ δ`
    rw [hδdef]; linarith [hδ0']
  · -- conjunct 4b : `δ ≤ Δπ`
    intro m
    have hd := deltaPi_lower_of 5 (63 - 1 / 100) Nc hNc m N' hNc'
    have hhs : (hSeq 5 m : ℝ) ≤ 19 := by exact_mod_cast hSeq_le_nineteen m
    rw [hδdef]; linarith [hd, hhs]
  · -- conjunct 5 : `cval m ≤ Qdiag`
    intro m; exact le_refl _
  · -- conjunct 6 : the `S2ᵂ` lower bound
    intro m
    have hS2 := hS2fun R ν₀ (yF R (primorial Dstar) Fstar1) hR2 hyabs hν₀ N'
      hN₀eh' hRleN' hrange m
    simp only [herrdef]
    have hid : deltaPi 5 64 N' m / (Nat.totient (primorial Dstar) : ℝ)
          * Qdiag_mW 5 R (primorial Dstar) m (yF R (primorial Dstar) Fstar1)
        - (deltaPi 5 64 N' m / (Nat.totient (primorial Dstar) : ℝ)
              * (Qdiag_mW 5 R (primorial Dstar) m (yF R (primorial Dstar) Fstar1)
                - s2CompatFormM 5 R (primorial Dstar) m (yF R (primorial Dstar) Fstar1))
            + C₀ * (1 + Real.log R) ^ (2 * 5 + 2) * (N' : ℝ) / (Real.log N') ^ (2 * 5 + 4))
      = deltaPi 5 64 N' m / (Nat.totient (primorial Dstar) : ℝ)
            * s2CompatFormM 5 R (primorial Dstar) m (yF R (primorial Dstar) Fstar1)
          - C₀ * (1 + Real.log R) ^ (2 * 5 + 2) * (N' : ℝ) / (Real.log N') ^ (2 * 5 + 4) := by
      ring
    rw [hid]; linarith [hS2]
  · -- conjunct 7 : the assembled ratio-slack (FABLE-QUEUE'd)
    exact hslack

end Salt.Twelve
