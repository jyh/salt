/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.GapsFinal

/-!
# R2a — discharging the `WinFrontierM` largeness bundle (conjuncts 1–6)

Design: `docs/blueprints/explicit12-design.md`, card NC-3 and the W5-7 flag in
`docs/blueprints/flags.md`.

`gaps_le_twelve_of_frontierM` (`Salt/Twelve/GapsFinal.lean`) is conditional on the
`WinFrontierM` hypothesis `hFrontier` — the `∀ᶠ N` largeness bundle
`WindowPNT → EHall → ∀ N, ∃ N' ≥ N, [analytic conjuncts]` at the modulus
`primorial Dfin`, with the *M-based* S₁ slack (conjunct 7).  This file lands the
discharge as a verbatim mirror of `winFrontier_of`
(`Salt/Twelve/WinFrontierDischarge.lean`).

**Parameterization.**  The Archimedean cutoff must be chosen *existentially*
after the `qdiag_bridge` / `mv_I_split` constants are obtained (they are
∃-opaque reals — no fixed numeral `D` can be proven `≥` an opaque threshold).
So the frontier bundle is stated at an abstract parameter `D` (`WinFrontierMW`),
and the pinned-numeral `WinFrontierM` of `GapsFinal` is recovered from
`WinFrontierMW Dfin` by defeq (`winFrontierM_of_W`).  Conjuncts 1–6 and the
`∀ᶠ` threshold assembly are identical to `winFrontier_of` (they never mention
the S₁ collision); the only numeral fact used is `hSeq i < D`, which follows
from `300 ≤ D` (`hSeq` maxes at `19`).  Conjunct 7 is reduced to the explicit
`∀ᶠ`-slack hypothesis `hslackEv`, now in the M-form (`yside + 12·5²/D · M`
rather than `(1 + 12·5²/Dstar)·yside`).

The canonical wave-5 witnesses (unchanged from `winFrontier_of`):

* `R := ⌊N'^{1999/4000}⌋₊`  (the `θ★/2` window exponent);
* `ν₀ := (exists_nu0W 5 (primorial D) …).choose`  (CRT residue base);
* `δ := (63 − 1/100)·N'/log N' − 19`  (`WindowPNT` prime supply, `hSeq ≤ 19`);
* `cval m := Qdiag_mW 5 R (primorial D) m (yF R (primorial D) Fstar1)`;
* `errEH m :=`  the `S2mW_ge_compatMain_theta_uniform` residual `C₀·…` folded
  with the collision difference `Δπ/φW'·(Qdiag − s2CompatForm)`.

The landed lemmas are all `W'`-generic, so this re-applies them at `primorial D`.
-/

namespace Salt.Twelve

open Salt.Maynard
open Finset Filter

/-! ## Local helpers (modulus-generic; re-proved from `WinFrontierDischarge`) -/

/-- Non-collision pairs have pairwise-coprime lcm coordinates (free `W'`;
mirror of `WinFrontierDischarge`'s private helper of the same shape). -/
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

private lemma hSeq_le_nineteen (i : Fin 5) : hSeq 5 i ≤ 19 := by
  fin_cases i <;>
    simp only [hSeq_five_zero, hSeq_five_one, hSeq_five_two, hSeq_five_three,
      hSeq_five_four] <;>
    norm_num

/-! ## The abstract frontier `WinFrontierMW` (parameterized by `D`)

Byte-mirror of `GapsFinal`'s `WinFrontierM` with every `primorial Dfin` replaced
by `primorial D` and the slack's `12 * (5:ℝ)^2 / Dfin` by `12 * (5:ℝ)^2 / D`.
At `D := Dfin` this is definitionally `WinFrontierM` (`winFrontierM_of_W`). -/
def WinFrontierMW (D : ℕ) : Prop :=
  WindowPNT → EHall → ∀ N : ℕ,
    ∃ (N' R ν₀ : ℕ) (δ : ℝ) (errEH cval : Fin 5 → ℝ), N ≤ N' ∧
    (∀ d ∈ kSieveIndex 5 R (primorial D), ∀ e ∈ kSieveIndex 5 R (primorial D),
      ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % (primorial D) = ν₀ % (primorial D) ∧
        ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq 5 i)) ∧
    0 < (Nat.totient (primorial D) : ℝ) ∧ (∀ m : Fin 5, 0 ≤ cval m) ∧ 0 ≤ δ ∧
    (∀ m : Fin 5, δ ≤ deltaPi 5 64 N' m) ∧
    (∀ m : Fin 5,
      cval m ≤ Qdiag_mW 5 R (primorial D) m (yF R (primorial D) Fstar1)) ∧
    (∀ m : Fin 5,
      deltaPi 5 64 N' m / (Nat.totient (primorial D) : ℝ)
          * Qdiag_mW 5 R (primorial D) m (yF R (primorial D) Fstar1) - errEH m
        ≤ S2mW 5 64 N' R ν₀ (primorial D) m (yF R (primorial D) Fstar1)) ∧
    (((64 - 1) * N' / (primorial D) : ℝ)
          * ((∑ r ∈ kSieveIndex 5 R (primorial D),
                  (yF R (primorial D) Fstar1 r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
              + 12 * (5 : ℝ) ^ 2 / D
                  * ∑ r ∈ kSieveIndex 5 R (primorial D),
                      1 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (5 + 1)
            * (∑ d ∈ kSieveIndex 5 R (primorial D),
                |lam 5 R (primorial D) (yF R (primorial D) Fstar1) d|) ^ 2
        < (∑ m : Fin 5,
              δ / (Nat.totient (primorial D) : ℝ) * cval m) - ∑ m : Fin 5, errEH m)

/-! ## The assembled ratio-slack (conjunct 7 of `WinFrontierMW`, M-form) -/

/-- The assembled M-based ratio-slack inequality (conjunct 7 of `WinFrontierMW`)
at the canonical wave-5 witnesses and modulus `primorial D`.  Mirror of
`WinFrontierDischarge`'s `WinSlack`, but the S₁ main factor carries the raw
M-form `yside + 12·5²/D · M` (instead of `(1 + 12·5²/Dstar)·yside`).
Parametrized by the cutoff `D` and the `S2mW_ge_compatMain_theta_uniform`
residual constant `C₀`.  Carried as the `∀ᶠ`-hypothesis of `winFrontierMW_of`;
its discharge is FABLE-QUEUE'd — see the NC-3 / W5-7 flag. -/
def WinSlackM (D : ℕ) (C₀ : ℝ) (N' : ℕ) : Prop :=
  ((64 - 1) * (N' : ℝ) / (primorial D))
      * ((∑ r ∈ kSieveIndex 5 (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial D),
              (yF (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial D) Fstar1 r) ^ 2
                / ∏ i, (Nat.totient (r i) : ℝ))
          + 12 * (5 : ℝ) ^ 2 / D
              * ∑ r ∈ kSieveIndex 5 (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial D),
                  1 / ∏ i, (Nat.totient (r i) : ℝ))
    + 2 ^ (5 + 1)
        * (∑ d ∈ kSieveIndex 5 (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial D),
            |lam 5 (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial D)
              (yF (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial D) Fstar1) d|) ^ 2
    < (∑ m : Fin 5,
          ((63 - 1 / 100) * (N' : ℝ) / Real.log N' - 19)
              / (Nat.totient (primorial D) : ℝ)
            * Qdiag_mW 5 (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial D) m
                (yF (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial D) Fstar1))
      - ∑ m : Fin 5,
          (deltaPi 5 64 N' m / (Nat.totient (primorial D) : ℝ)
              * (Qdiag_mW 5 (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial D) m
                    (yF (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial D) Fstar1)
                - s2CompatFormM 5 (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial D) m
                    (yF (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) (primorial D) Fstar1))
            + C₀ * (1 + Real.log (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ)) ^ (2 * 5 + 2)
                * (N' : ℝ) / (Real.log N') ^ (2 * 5 + 4))

/-! ## `winFrontierMW_of` — the discharge modulo the M-based slack hypothesis -/

/-- **R2a (modulo the FABLE-QUEUE'd slack).**  The `WinFrontierMW D` largeness
bundle for `W' = primorial D` (any cutoff `D ≥ 300`), discharging conjuncts 1–6
and the `∀ᶠ` threshold assembly concretely from the landed lemmas, and reducing
conjunct 7 to the explicit `∀ᶠ`-slack hypothesis `hslackEv` (the M-based
`win_ratio_core` + error-budget content).  The only use of `300 ≤ D` is to
supply `hSeq i < D` (`hSeq` maxes at `19`); everything else is `W'`-generic. -/
theorem winFrontierMW_of (D : ℕ) (hD : 300 ≤ D)
    (hslackEv : ∀ C₀ : ℝ, 0 ≤ C₀ → ∀ᶠ N' : ℕ in atTop, WinSlackM D C₀ N') :
    WinFrontierMW D := by
  intro hPNT hEH N
  classical
  -- modulus facts
  have hW'sqf : Squarefree (primorial D) := primorial_sqf' D
  have hW'pos : 0 < primorial D := primorial_pos'' D
  have hW'ne : (primorial D) ≠ 0 := hW'pos.ne'
  have hφW'pos : (0 : ℝ) < (Nat.totient (primorial D) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hW'pos
  have hDle : ∀ p : ℕ, p.Prime → ¬ p ∣ primorial D → D ≤ p :=
    fun p hp hnd => le_of_lt (primorial_hDlt D p hp hnd)
  have hSeqlt : ∀ i : Fin 5, hSeq 5 i < D := fun i => by
    have := hSeq_le_nineteen i; omega
  -- HasLevel θ₊ from EHall
  have hLoD : HasLevel (3999 / 4000) :=
    EH_hasLevel (EHall_hasEH hEH (by norm_num) (by norm_num))
  -- CRT residue base
  obtain ⟨ν₀, hν₀⟩ := exists_nu0W 5 (primorial D) hW'ne
  -- the θ₊-level coupled-EH lemma (constants obtained before choosing N')
  obtain ⟨C₀, B', N₀eh, hC₀0, hB'0, hS2fun⟩ :=
    S2mW_ge_compatMain_theta_uniform 5 64 (primorial D) D (by norm_num)
      (by norm_num) hW'sqf hDle hSeqlt hLoD
  -- EH range threshold
  obtain ⟨Nr, hNrfun⟩ := EH_range_theta (primorial D) hW'pos B' hB'0
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
  have hrange : primorial D * R ^ 2
      ≤ ⌊(N' : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log N') ^ B'⌋₊ := by
    rw [hRdef]; exact hNrfun N' hNr'
  have hyabs : ∀ r, |yF R (primorial D) Fstar1 r| ≤ 1 :=
    fun r => yF_Fstar1_abs_le_one R (primorial D) r
  -- δ, cval, errEH
  set δ : ℝ := (63 - 1 / 100) * (N' : ℝ) / Real.log N' - 19 with hδdef
  set cval : Fin 5 → ℝ :=
    fun m => Qdiag_mW 5 R (primorial D) m (yF R (primorial D) Fstar1) with hcvaldef
  set errEH : Fin 5 → ℝ :=
    fun m => deltaPi 5 64 N' m / (Nat.totient (primorial D) : ℝ)
          * (Qdiag_mW 5 R (primorial D) m (yF R (primorial D) Fstar1)
            - s2CompatFormM 5 R (primorial D) m (yF R (primorial D) Fstar1))
        + C₀ * (1 + Real.log R) ^ (2 * 5 + 2) * (N' : ℝ) / (Real.log N') ^ (2 * 5 + 4)
    with herrdef
  refine ⟨N', R, ν₀, δ, errEH, cval, hNleN', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- conjunct 1 : CRT collision-solvability
    intro d hd e he hcompat
    obtain ⟨hdsq, -, hdcopW, -⟩ := (mem_kSieveIndex_iff d).mp hd
    obtain ⟨hesq, -, hecopW, -⟩ := (mem_kSieveIndex_iff e).mp he
    exact cong_solvableW 5 (primorial D) d e ν₀ hW'pos
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
    have hS2 := hS2fun R ν₀ (yF R (primorial D) Fstar1) hR2 hyabs hν₀ N'
      hN₀eh' hRleN' hrange m
    simp only [herrdef]
    have hid : deltaPi 5 64 N' m / (Nat.totient (primorial D) : ℝ)
          * Qdiag_mW 5 R (primorial D) m (yF R (primorial D) Fstar1)
        - (deltaPi 5 64 N' m / (Nat.totient (primorial D) : ℝ)
              * (Qdiag_mW 5 R (primorial D) m (yF R (primorial D) Fstar1)
                - s2CompatFormM 5 R (primorial D) m (yF R (primorial D) Fstar1))
            + C₀ * (1 + Real.log R) ^ (2 * 5 + 2) * (N' : ℝ) / (Real.log N') ^ (2 * 5 + 4))
      = deltaPi 5 64 N' m / (Nat.totient (primorial D) : ℝ)
            * s2CompatFormM 5 R (primorial D) m (yF R (primorial D) Fstar1)
          - C₀ * (1 + Real.log R) ^ (2 * 5 + 2) * (N' : ℝ) / (Real.log N') ^ (2 * 5 + 4) := by
      ring
    rw [hid]; linarith [hS2]
  · -- conjunct 7 : the assembled M-based ratio-slack (FABLE-QUEUE'd)
    exact hslack

/-! ## Compatibility bridge to the pinned-numeral `WinFrontierM` -/

/-- `WinFrontierMW Dfin` is definitionally `GapsFinal`'s pinned `WinFrontierM`
(the byte-mirror substitutes `D := Dfin`).  This bridges the parameterized
frontier back to the capstone's hypothesis shape. -/
theorem winFrontierM_of_W (h : WinFrontierMW Dfin) : WinFrontierM := h

end Salt.Twelve
