/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.GapsFinal
import Salt.MaynardK.S2Half
import Salt.MaynardK.LevelRange
import Salt.MaynardK.F1

/-!
# C1 · B4.5d — the frontier at `k = 105`, level `1/2`

`WinSlackM105`, `WinFrontierMW105` and `winFrontierMW105_of`: mirror of `FrontierM` +
`GapsOfLevel.winFrontierMW_of_hasLevel` with ρ = 9999/40000,
ε = 1/1000, h_max ≤ 743, cutoff 744, weight `F1`). `yFg_F1_abs_le_one`: `|F1| ≤ 1` on the sieve
index.
Generic in the tuple (`TupleChoice`): the `105`-entries are assumed `≤ 743` (`hle`), nothing else.
Ported by an Opus executor from a frozen brief (2026-10-11).
-/

namespace Salt.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Salt.Maynard Salt.Twelve Salt.MaynardK
open Finset Filter

/-! ## Local helpers -/

omit [Salt.Maynard.TupleChoice] in
/-- Non-collision pairs have pairwise-coprime lcm coordinates (k-generic mirror). -/
lemma lcm_pairwise_coprime_of_noncollision_k {k R W' : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W')
    (hcompat : ¬ IsCollisionPair d e) {i j : Fin k} (hij : i ≠ j) :
    Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j)) := by
  obtain ⟨-, hdcop, -, -⟩ := (mem_kSieveIndex_iff d).mp hd
  obtain ⟨-, hecop, -, -⟩ := (mem_kSieveIndex_iff e).mp he
  have hnc : ∀ a b : Fin k, a ≠ b → Nat.Coprime (d a) (e b) := by
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

omit [Salt.Maynard.TupleChoice] in
/-- `|yFg R W' F1| ≤ 1` everywhere (the `hy1` of the k = 105 chain, from `eval_F1_abs_le_one`). -/
theorem yFg_F1_abs_le_one (R W' : ℕ) (s : Fin 105 → ℕ) :
    |yFg R W' F1 s| ≤ 1 := by
  unfold yFg
  split_ifs with hs
  · have hs0lt : s 0 < R := kSieveIndex_coord_lt hs 0
    have hs0pos : 0 < s 0 := kSieveIndex_coord_pos hs 0
    have hR2 : 2 ≤ R := by omega
    have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast hR2.trans_lt' (by norm_num)
    have hLpos : 0 < Real.log R := Real.log_pos hR1
    apply eval_F1_abs_le_one
    · intro i
      have hsipos : 0 < s i := kSieveIndex_coord_pos hs i
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hsipos)) hLpos.le
    · obtain ⟨-, -, -, hprod⟩ := (mem_kSieveIndex_iff s).mp hs
      have hne : ∀ i ∈ (Finset.univ : Finset (Fin 105)), ((s i : ℕ) : ℝ) ≠ 0 := by
        intro i _
        have hsipos : 0 < s i := kSieveIndex_coord_pos hs i
        exact_mod_cast hsipos.ne'
      have hprodpos : (0 : ℝ) < ∏ i, ((s i : ℕ) : ℝ) :=
        Finset.prod_pos (fun i _ => by exact_mod_cast kSieveIndex_coord_pos hs i)
      have hprodle : ∏ i, ((s i : ℕ) : ℝ) ≤ (R : ℝ) := by
        rw [← Nat.cast_prod]; exact_mod_cast hprod.le
      rw [← Finset.sum_div, ← Real.log_prod hne, div_le_one hLpos]
      exact Real.log_le_log hprodpos hprodle
  · simp

/-! ## The k = 105 frontier `WinFrontierMW105` (parameterized by `D`) -/

/-- Mirror of `WinFrontierMWL` (the level-route bundle) at k = 105, weight `F1`, with
`HasLevel (1/2)` carried as the second premise. -/
def WinFrontierMW105 (D : ℕ) : Prop :=
  WindowPNT → HasLevel (1 / 2) → ∀ N : ℕ,
    ∃ (N' R ν₀ : ℕ) (δ : ℝ) (errEH cval : Fin 105 → ℝ), N ≤ N' ∧
    (∀ d ∈ kSieveIndex 105 R (primorial D), ∀ e ∈ kSieveIndex 105 R (primorial D),
      ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % (primorial D) = ν₀ % (primorial D) ∧
        ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq 105 i)) ∧
    0 < (Nat.totient (primorial D) : ℝ) ∧ (∀ m : Fin 105, 0 ≤ cval m) ∧ 0 ≤ δ ∧
    (∀ m : Fin 105, δ ≤ deltaPi 105 64 N' m) ∧
    (∀ m : Fin 105,
      cval m ≤ Qdiag_mW 105 R (primorial D) m (yFg R (primorial D) F1)) ∧
    (∀ m : Fin 105,
      deltaPi 105 64 N' m / (Nat.totient (primorial D) : ℝ)
          * Qdiag_mW 105 R (primorial D) m (yFg R (primorial D) F1) - errEH m
        ≤ S2mW 105 64 N' R ν₀ (primorial D) m (yFg R (primorial D) F1)) ∧
    (((64 - 1) * N' / (primorial D) : ℝ)
          * ((∑ r ∈ kSieveIndex 105 R (primorial D),
                  (yFg R (primorial D) F1 r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
              + 12 * (105 : ℝ) ^ 2 / D
                  * ∑ r ∈ kSieveIndex 105 R (primorial D),
                      1 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (105 + 1)
            * (∑ d ∈ kSieveIndex 105 R (primorial D),
                |lam 105 R (primorial D) (yFg R (primorial D) F1) d|) ^ 2
        < (∑ m : Fin 105,
              δ / (Nat.totient (primorial D) : ℝ) * cval m) - ∑ m : Fin 105, errEH m)

/-- The assembled M-based ratio-slack at k = 105 (conjunct 7 of `WinFrontierMW105`) at the
canonical witnesses `R = ⌊N'^{9999/40000}⌋`, `δ = (63 − 1/1000)·N'/log N' − 743`, weight `F1`. -/
def WinSlackM105 (D : ℕ) (C₀ : ℝ) (N' : ℕ) : Prop :=
  ((64 - 1) * (N' : ℝ) / (primorial D))
      * ((∑ r ∈ kSieveIndex 105 (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊) (primorial D),
              (yFg (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊) (primorial D) F1 r) ^ 2
                / ∏ i, (Nat.totient (r i) : ℝ))
          + 12 * (105 : ℝ) ^ 2 / D
              * ∑ r ∈ kSieveIndex 105 (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊) (primorial D),
                  1 / ∏ i, (Nat.totient (r i) : ℝ))
    + 2 ^ (105 + 1)
        * (∑ d ∈ kSieveIndex 105 (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊) (primorial D),
            |lam 105 (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊) (primorial D)
              (yFg (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊) (primorial D) F1) d|) ^ 2
    < (∑ m : Fin 105,
          ((63 - 1 / 1000) * (N' : ℝ) / Real.log N' - 743)
              / (Nat.totient (primorial D) : ℝ)
            * Qdiag_mW 105 (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊) (primorial D) m
                (yFg (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊) (primorial D) F1))
      - ∑ m : Fin 105,
          (deltaPi 105 64 N' m / (Nat.totient (primorial D) : ℝ)
              * (Qdiag_mW 105 (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊) (primorial D) m
                    (yFg (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊) (primorial D) F1)
                - s2CompatFormM 105 (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊) (primorial D) m
                    (yFg (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊) (primorial D) F1))
            + C₀ * (1 + Real.log (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ)) ^ (2 * 105 + 2)
                * (N' : ℝ) / (Real.log N') ^ (2 * 105 + 4))

/-! ## `winFrontierMW105_of` — the discharge modulo the slack hypothesis (LEVEL route) -/

theorem winFrontierMW105_of (D : ℕ) (hD : 744 ≤ D) (hle : ∀ i : Fin 105, hSeq 105 i ≤ 743)
    (hslackEv : ∀ C₀ : ℝ, 0 ≤ C₀ → ∀ᶠ N' : ℕ in atTop, WinSlackM105 D C₀ N') :
    WinFrontierMW105 D := by
  intro hPNT hLoD N
  classical
  -- modulus facts
  have hW'sqf : Squarefree (primorial D) := primorial_sqf' D
  have hW'pos : 0 < primorial D := primorial_pos'' D
  have hW'ne : (primorial D) ≠ 0 := hW'pos.ne'
  have hφW'pos : (0 : ℝ) < (Nat.totient (primorial D) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hW'pos
  have hDle : ∀ p : ℕ, p.Prime → ¬ p ∣ primorial D → D ≤ p :=
    fun p hp hnd => le_of_lt (primorial_hDlt D p hp hnd)
  have hSeqlt : ∀ i : Fin 105, hSeq 105 i < D := fun i => lt_of_le_of_lt (hle i) hD
  -- CRT residue base
  obtain ⟨ν₀, hν₀⟩ := exists_nu0W 105 (primorial D) hW'ne
  -- the level-1/2 S₂ lemma (constants obtained before choosing N')
  obtain ⟨C₀, B', N₀eh, hC₀0, hB'0, hS2fun⟩ :=
    S2mW_ge_compatMain_half_uniform 105 64 (primorial D) D (by norm_num)
      (by norm_num) hW'sqf hDle hSeqlt hLoD
  -- level range threshold
  obtain ⟨Nr, hNrfun⟩ := level_range_half (primorial D) hW'pos B' hB'0
  -- WindowPNT threshold (ε = 1/1000)
  obtain ⟨Nc, hNc⟩ := eventually_atTop.mp (hPNT (1 / 1000) (by norm_num))
  -- eventually `0 ≤ δ`
  have hδev : ∀ᶠ N' : ℕ in atTop,
      (743 : ℝ) ≤ (63 - 1 / 1000) * (N' : ℝ) / Real.log N' := by
    have hev := eventually_poly_beats_polylog 1 1 743 (by norm_num)
    have hevN := tendsto_natCast_atTop_atTop.eventually hev
    filter_upwards [hevN, eventually_ge_atTop 2] with N' hN' hN2
    have hlogpos : 0 < Real.log N' := Real.log_pos (by exact_mod_cast (by omega : 1 < N'))
    simp only [pow_one, Real.rpow_one] at hN'
    rw [le_div_iff₀ hlogpos]
    nlinarith [hN', hlogpos]
  -- combine every eventually fact
  have hcombined := (hslackEv C₀ hC₀0).and
    (hδev.and (eventually_ge_atTop (max (max Nr N₀eh) (max Nc 32))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hcombined
  set N' := max N₀ N with hN'def
  have hNleN' : N ≤ N' := le_max_right _ _
  have hN'geN₀ : N₀ ≤ N' := le_max_left _ _
  obtain ⟨hslack, hδ0', hgeThr⟩ := hN₀ N' hN'geN₀
  -- unpack thresholds
  have hNr' : Nr ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hgeThr
  have hN₀eh' : N₀eh ≤ N' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hgeThr
  have hNc' : Nc ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hgeThr
  have h32' : 32 ≤ N' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hgeThr
  have hN'32r : (32 : ℝ) ≤ (N' : ℝ) := by exact_mod_cast h32'
  -- R and its facts
  set R := ⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊ with hRdef
  have hR2 : 2 ≤ R := R_ge_two_rho N' hN'32r
  have hRleN' : R ≤ N' := R_le_N'_rho N' (by omega)
  have hrange : primorial D * R ^ 2
      ≤ ⌊(N' : ℝ) ^ (1 / 2 : ℝ) / (Real.log N') ^ B'⌋₊ := by
    rw [hRdef]; exact hNrfun N' hNr'
  have hyabs : ∀ r, |yFg R (primorial D) F1 r| ≤ 1 :=
    fun r => yFg_F1_abs_le_one R (primorial D) r
  -- δ, cval, errEH (the level residual atomised as `Eres`)
  set δ : ℝ := (63 - 1 / 1000) * (N' : ℝ) / Real.log N' - 743 with hδdef
  set cval : Fin 105 → ℝ :=
    fun m => Qdiag_mW 105 R (primorial D) m (yFg R (primorial D) F1) with hcvaldef
  set Eres : ℝ := C₀ * (1 + Real.log R) ^ (2 * 105 + 2) * (N' : ℝ)
      / (Real.log N') ^ (2 * 105 + 4) with hEresdef
  set errEH : Fin 105 → ℝ :=
    fun m => deltaPi 105 64 N' m / (Nat.totient (primorial D) : ℝ)
          * (Qdiag_mW 105 R (primorial D) m (yFg R (primorial D) F1)
            - s2CompatFormM 105 R (primorial D) m (yFg R (primorial D) F1))
        + Eres
    with herrdef
  refine ⟨N', R, ν₀, δ, errEH, cval, hNleN', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- conjunct 1 : CRT collision-solvability
    intro d hd e he hcompat
    obtain ⟨hdsq, -, hdcopW, -⟩ := (mem_kSieveIndex_iff d).mp hd
    obtain ⟨hesq, -, hecopW, -⟩ := (mem_kSieveIndex_iff e).mp he
    exact cong_solvableW 105 (primorial D) d e ν₀ hW'pos
      (fun i => Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hdsq i).ne_zero (hesq i).ne_zero))
      (fun i => ((hdcopW i).symm.mul_right (hecopW i).symm).coprime_dvd_right
        (Nat.lcm_dvd_mul (d i) (e i)))
      (fun i j hij => lcm_pairwise_coprime_of_noncollision_k hd he hcompat hij)
  · -- conjunct 2 : `0 < φ W'`
    exact hφW'pos
  · -- conjunct 3 : `0 ≤ cval m` (diagonal form, k-generic)
    intro m
    change 0 ≤ Qdiag_mW 105 R (primorial D) m (yFg R (primorial D) F1)
    rw [Qdiag_mW, s2_diag_lam_restricted]
    exact Finset.sum_nonneg
      (fun u _ => mul_nonneg (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
        (sq_nonneg _))
  · -- conjunct 4a : `0 ≤ δ`
    rw [hδdef]; linarith [hδ0']
  · -- conjunct 4b : `δ ≤ Δπ`
    intro m
    have hd := deltaPi_lower_of 105 (63 - 1 / 1000) Nc hNc m N' hNc'
    have hhs : (hSeq 105 m : ℝ) ≤ 743 := by exact_mod_cast hle m
    rw [hδdef]; linarith [hd, hhs]
  · -- conjunct 5 : `cval m ≤ Qdiag`
    intro m; exact le_refl _
  · -- conjunct 6 : the `S2ᵂ` lower bound
    intro m
    have hS2 := hS2fun R ν₀ (yFg R (primorial D) F1) hR2 hyabs hν₀ N'
      hN₀eh' hRleN' hrange m
    rw [← hEresdef] at hS2
    change deltaPi 105 64 N' m / (Nat.totient (primorial D) : ℝ)
          * Qdiag_mW 105 R (primorial D) m (yFg R (primorial D) F1)
        - (deltaPi 105 64 N' m / (Nat.totient (primorial D) : ℝ)
              * (Qdiag_mW 105 R (primorial D) m (yFg R (primorial D) F1)
                - s2CompatFormM 105 R (primorial D) m (yFg R (primorial D) F1))
            + Eres)
        ≤ S2mW 105 64 N' R ν₀ (primorial D) m (yFg R (primorial D) F1)
    generalize deltaPi 105 64 N' m / (Nat.totient (primorial D) : ℝ) = a at hS2 ⊢
    generalize Qdiag_mW 105 R (primorial D) m (yFg R (primorial D) F1) = Q at hS2 ⊢
    generalize s2CompatFormM 105 R (primorial D) m (yFg R (primorial D) F1) = Sc at hS2 ⊢
    generalize S2mW 105 64 N' R ν₀ (primorial D) m (yFg R (primorial D) F1) = S2 at hS2 ⊢
    generalize Eres = E at hS2 ⊢
    have hid : a * Q - (a * (Q - Sc) + E) = a * Sc - E := by ring
    rw [hid]; linarith [hS2]
  · -- conjunct 7 : the assembled ratio-slack (B4.5c)
    exact hslack

end Salt.MaynardK

