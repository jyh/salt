/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DensityLogfree
import Salt.SW.JutilaHalasz
import Salt.SW.JutilaRatio
import Salt.SW.ZeroCountNearOne

/-!
# B2 W9f — the strip, the below-threshold supplier, the `σ = 1` line and the glue:
THE LOG-FREE ZERO-DENSITY THEOREM `N(σ, T, χ) ≤ C·(qT)^{D(1−σ)}`

The last block of Arm B part B2 (design v2 §0, §0.f; K-W9-8). Three inputs are already on
`main`: the boxes at the scale `Δ = 1/log D` with W1's constant threaded (W9e,
`zeroCountM_le_box_bound_mul` — the count is at most `C₁(7/4 + 3λ/2)` times the number of
non-empty boxes, even plus odd, `λ = (1 − σ) log D`), the `Δ`-well-spacing of each parity's
representatives (W9e, `wellSpacedAt_parity_reps`), and THE RATIO for a `Δ`-well-spaced system of
zeros in the strip `119/120 ≤ σ ≤ β < 1` (W9c, `card_system_le_rpow`: `J ≤ C·(qT)^{13(1−σ)}`
once `D₁ ≤ qT`, `C` and `D₁` non-effective inside the `∃`). This file assembles them.

* **The `σ ≥ 1` line** (`zeroCountM_eq_zero_of_one_le`): no zero of `L(·, χ)` has `Re ≥ 1`
  (`LFunction_ne_zero_of_one_le_re` at `χ ≠ 1`, which primitivity at `q ≥ 2` supplies), so the
  closed box `σ ≤ Re ≤ 1` is empty and the count is `0`.
* **Below the threshold** (`zeroCountM_le_const_of_le`): for `qT ≤ D₀` the `σ`-free crude count
  `zeroCountM_le` (`≤ 137(2T + 3)log(q(T + 3))`) is at most the CONSTANT
  `137(2D₀ + 3)·log(D₀(D₀ + 3))` (`T ≤ D₀/2`, `q ≤ D₀/2` at `q, T ≥ 2`).
* **The glue's monotonicity** (`rpow_mul_le_rpow_of_le_150`): `(qT)^{14(1−σ)} ≤ (qT)^{150(1−σ)}`
  at `qT ≥ 1`, `σ ≤ 1` — `rpow` is monotone in the exponent above base `1`.
* **THE STRIP** (`zeroCountM_density_logfree_strip`, the literal `14 = 2c + 1`): on
  `119/120 ≤ σ ≤ 1`, `T ≥ 2`, the count is `≤ C·(qT)^{14(1−σ)}`. At `σ = 1` it is `0`. For
  `qT ≥ D₀ := max(10²⁰, D₁)` and `σ < 1`: each parity's representatives form a `Δ`-well-spaced
  system of `J` zeros with distinct ordinates (a box's representative carries the box's index:
  `⌊γ log D⌋ = k`), so the ratio bounds each parity's non-empty boxes by `C_r·(qT)^{13(1−σ)}`,
  and `N ≤ C₁(7/4 + 3λ/2)·2·C_r·(qT)^{13(1−σ)} ≤ (7/2)·C₁·C_r·(qT)^{14(1−σ)}` since
  `7/4 + 3λ/2 ≤ (7/4)e^{λ}` and `e^{λ} = (qT)^{1−σ}`. Below `D₀` the constant supplier applies
  against `(qT)^{14(1−σ)} ≥ 1`. `C := max(137(2D₀ + 3)log(D₀(D₀ + 3)), (7/2)C₁C_r)`.
* **THE TARGET** (`zeroCountM_density_logfree`, design v2 §0 VERBATIM — B3's `ellL` row consumes
  it as `∃ C D`): on `4/5 ≤ σ ≤ 1` with `D := 150`: the low half `zeroCountM_density_logfree_low`
  (`1378·(qT)^{150(1−σ)}` on `4/5 ≤ σ ≤ 119/120`) and the strip lifted by the glue's monotonicity
  on `119/120 ≤ σ ≤ 1`; `C := max 1378 C_strip`.

## The honest label

Landing this file lands **B2 WHOLE** — the log-free density theorem is one of the crown's six
conditions (Arm B v2 §0), and it is stated as the design froze it: `∃ C D` with `D ≤ 150` and a
`C` that is NON-EFFECTIVE (through S10's `∃ K` and W1's `∃ C`, and a threshold
`D₁ = 10^59–10^64` at `C_ps = 1`); the strip's `14` is a literal the proof supplies. The
`σ ≤ 1` binder that W9e's count rows carry is CONSUMED here on `[119/120, 1]`; the strip's
`119/120 ≤ σ` is the floor rows' (a zero with `β ≥ 119/120` is assumed there and none is known,
so the ratio is vacuous at the object while the strip and the target are NOT — below `D₀` and
at `σ = 1` they are the crude count and the non-vanishing). Nothing here bears on twin primes or
on the crown's conditions beyond stating B2's own.

## The measured receipts (design v2 §A.6/§A.7 as corrected at the passes; `h2c-desk/w9f_sweep.py`)

`7/4 + 3λ/2 ≤ (7/4)e^{λ}` with equality at `λ = 0` (the gap `0.034` at `λ = 0.1`, `0.243`
at `λ = 0.384 = log(10²⁰)/120`, the strip's largest `λ` at `10²⁰`). The glue at `qT = 4`,
`σ = 1/2`: `4^{7} = 16384 ≤ 4^{75}`. The constant supplier at `D₀ = 10²⁰`:
`137·(2·10²⁰ + 3)·log(10⁴⁰) = 2.52·10²⁴`, against the crude count's own value at
`(q, T) = (2, 5·10¹⁹)`: `137·(10²⁰ + 3)·log(10²⁰ + 6) = 6.31·10²³` (ratio `0.25`).

## The executor's note (the import)

THE RATIO `card_system_le_rpow` landed in `Salt/SW/JutilaRatio.lean` (the W9c′ re-cut), not
in `JutilaHalasz.lean` where the design placed it, so this file imports `Salt.SW.JutilaRatio`
(which imports `JutilaHalasz`) beside the two count files. No statement of the block moved.
-/

open MeasureTheory Complex DirichletCharacter

noncomputable section
namespace Salt.SW

variable {q : ℕ}

/-! ## (i) The `σ ≥ 1` line -/

/-- No zero of `L(·, χ)` has `Re ≥ 1` (`LFunction_ne_zero_of_one_le_re` at `χ ≠ 1`, from
primitivity at `q ≥ 2`), so the closed box `σ ≤ Re ≤ 1`, `|Im| ≤ T` is empty at `σ ≥ 1` and
the count is `0`. -/
theorem zeroCountM_eq_zero_of_one_le [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) {σ T : ℝ} (hσ : 1 ≤ σ) : zeroCountM χ σ T = 0 := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  unfold zeroCountM
  have hemp : boxZeros χ σ 1 T = ∅ := Finset.eq_empty_of_forall_notMem fun ρ hρ => by
    obtain ⟨h0, hσρ, -, -⟩ := (mem_boxZeros hχ1).mp hρ
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by linarith : (1:ℝ) ≤ ρ.re) h0
  rw [hemp]; simp [efMultTotal]

/-! ## (ii) Below the threshold -/

/-- Below the threshold `D₀` the `σ`-free crude count (`zeroCountM_le`,
`≤ 137(2T + 3)log(q(T + 3))`) is at most a CONSTANT in `q` and `T`: `T ≤ D₀/2` and `q ≤ D₀/2`
from `qT ≤ D₀` at `q, T ≥ 2`. -/
theorem zeroCountM_le_const_of_le [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) {σ T : ℝ} (hσ : 1 / 2 ≤ σ) (hT : 2 ≤ T) {D₀ : ℝ} (hD : (q : ℝ) * T ≤ D₀) :
    zeroCountM χ σ T ≤ 137 * (2 * D₀ + 3) * Real.log (D₀ * (D₀ + 3)) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hcrude := zeroCountM_le χ hχ hq hσ (by linarith : (0:ℝ) ≤ T)
  have hD0 : (4 : ℝ) ≤ D₀ := by nlinarith
  have hT' : T ≤ D₀ := by nlinarith
  have hq' : (q : ℝ) ≤ D₀ := by nlinarith
  have hprod : (q : ℝ) * (T + 3) ≤ D₀ * (D₀ + 3) :=
    mul_le_mul hq' (by linarith) (by linarith) (by linarith)
  have hlog : Real.log ((q : ℝ) * (T + 3)) ≤ Real.log (D₀ * (D₀ + 3)) :=
    Real.log_le_log (by nlinarith) hprod
  have hlognn : (0:ℝ) ≤ Real.log ((q : ℝ) * (T + 3)) := Real.log_nonneg (by nlinarith)
  nlinarith [hcrude, hlog, hlognn, hT']

/-! ## (iii) The glue's monotonicity -/

/-- `rpow` is monotone in the exponent above base `1`: `14(1 − σ) ≤ 150(1 − σ)` at `σ ≤ 1`. -/
theorem rpow_mul_le_rpow_of_le_150 {Q σ : ℝ} (hQ : 1 ≤ Q) (hσ : σ ≤ 1) :
    Q ^ (14 * (1 - σ)) ≤ Q ^ (150 * (1 - σ)) := by
  exact Real.rpow_le_rpow_of_exponent_le hQ (by nlinarith)

/-! ## (iv) THE STRIP (the literal `14`) -/

/-- **The per-parity system, staged** (the strip's one non-bookkeeping step): a Finset `S` of box
indices whose boxes are all NON-EMPTY, with the representatives' ordinates `Δ`-well-spaced, is
counted by THE RATIO — the representatives are zeros in the strip (`mem_boxZeros`), their `Re` is
`< 1` by the non-vanishing, their ordinates are distinct because the box index is a function of
`Im` alone, and `WellSpacedAt` is ANTITONE in its Finset (so the inclusion suffices). -/
private lemma card_le_of_boxRep_system {C_r D₁ : ℝ}
    (hratio : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → 2 ≤ q →
      ∀ (σ T : ℝ), 119 / 120 ≤ σ → σ < 1 → 2 ≤ T → D₁ ≤ (q : ℝ) * T →
      ∀ (J : ℕ) (ρ : Fin J → ℂ), (∀ j, LFunction χ (ρ j) = 0) → (∀ j, σ ≤ (ρ j).re) →
        (∀ j, (ρ j).re < 1) → (∀ j, |(ρ j).im| ≤ T) →
        WellSpacedAt (1 / Real.log ((q : ℝ) * T)) (Finset.univ.image (fun j => (ρ j).im)) →
        Function.Injective (fun j => (ρ j).im) →
        (J : ℝ) ≤ C_r * ((q : ℝ) * T) ^ (13 * (1 - σ)))
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    {σ T : ℝ} (hσ : 119 / 120 ≤ σ) (hlt : σ < 1) (hT : 2 ≤ T) (hD₁ : D₁ ≤ (q : ℝ) * T)
    (S : Finset ℤ) (hSmem : ∀ k ∈ S, (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty)
    (hws0 : WellSpacedAt (1 / Real.log ((q : ℝ) * T))
      (S.image (fun k => (boxRep χ σ T ((q : ℝ) * T) k).im))) :
    (S.card : ℝ) ≤ C_r * ((q : ℝ) * T) ^ (13 * (1 - σ)) := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin S.card → ℂ,
      ∀ j, ρ j = boxRep χ σ T ((q : ℝ) * T) (S.equivFin.symm j).1 := ⟨_, fun _ => rfl⟩
  have hfib : ∀ j : Fin S.card,
      ρ j ∈ boxFibre χ σ T ((q : ℝ) * T) (S.equivFin.symm j).1 := by
    intro j
    rw [hρ j]
    exact boxRep_mem (hSmem _ (S.equivFin.symm j).2)
  have hbox : ∀ j : Fin S.card, ρ j ∈ boxZeros χ σ 1 T ∧
      boxIndex ((q : ℝ) * T) (ρ j) = (S.equivFin.symm j).1 :=
    fun j => Finset.mem_filter.mp (hfib j)
  have hz : ∀ j : Fin S.card, LFunction χ (ρ j) = 0 ∧ σ ≤ (ρ j).re ∧ (ρ j).re ≤ 1 ∧
      |(ρ j).im| ≤ T := fun j => (mem_boxZeros hχ1).mp (hbox j).1
  have hzero : ∀ j, LFunction χ (ρ j) = 0 := fun j => (hz j).1
  have hre1 : ∀ j, (ρ j).re < 1 := fun j =>
    lt_of_le_of_ne (hz j).2.2.1 fun h =>
      LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) h.ge (hzero j)
  have hsub : Finset.univ.image (fun j => (ρ j).im)
      ⊆ S.image (fun k => (boxRep χ σ T ((q : ℝ) * T) k).im) := by
    refine Finset.image_subset_iff.mpr fun j _ => ?_
    rw [hρ j]
    exact Finset.mem_image_of_mem _ (S.equivFin.symm j).2
  have hws : WellSpacedAt (1 / Real.log ((q : ℝ) * T))
      (Finset.univ.image (fun j => (ρ j).im)) :=
    fun t ht r hr hne => hws0 t (hsub ht) r (hsub hr) hne
  have hinj : Function.Injective (fun j : Fin S.card => (ρ j).im) := by
    intro j j' h
    have h' : (ρ j).im = (ρ j').im := h
    have h1 : boxIndex ((q : ℝ) * T) (ρ j) = boxIndex ((q : ℝ) * T) (ρ j') := by
      unfold boxIndex
      rw [h']
    have h2 : (S.equivFin.symm j).1 = (S.equivFin.symm j').1 := by
      rw [← (hbox j).2, ← (hbox j').2]
      exact h1
    exact S.equivFin.symm.injective (Subtype.ext h2)
  exact hratio q χ hχ hq σ T hσ hlt hT hD₁ S.card ρ hzero (fun j => (hz j).2.1) hre1
    (fun j => (hz j).2.2.2) hws hinj

/-- **THE STRIP**: on `119/120 ≤ σ ≤ 1`, `T ≥ 2`, `N(σ, T, χ) ≤ C·(qT)^{14(1−σ)}` — the boxes
(W9e) with each parity's `Δ`-well-spaced representatives counted by THE RATIO (W9c) above the
threshold, the crude count below it, the non-vanishing at `σ = 1`; `14 = 2c + 1` at F5's
`x = D^{13/2}`. `C` is non-effective (W1's and S10's `∃`-constants and the threshold `D₁`). -/
theorem zeroCountM_density_logfree_strip :
    ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → 2 ≤ q →
      ∀ (σ T : ℝ), 119 / 120 ≤ σ → σ ≤ 1 → 2 ≤ T →
        zeroCountM χ σ T ≤ C * ((q : ℝ) * T) ^ (14 * (1 - σ)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := LFunction_zero_count_near_one_at_height
  obtain ⟨C_r, D₁, hCr0, hD₁0, hratio⟩ := card_system_le_rpow
  set D₀ : ℝ := max (10 ^ 20) D₁ with hD₀def
  have h10 : (10 : ℝ) ^ 20 ≤ D₀ := le_max_left _ _
  have hD₁D₀ : D₁ ≤ D₀ := le_max_right _ _
  have hD₀1 : (1 : ℝ) < D₀ * (D₀ + 3) := by nlinarith
  have hK₀ : (0 : ℝ) < 137 * (2 * D₀ + 3) * Real.log (D₀ * (D₀ + 3)) :=
    mul_pos (by nlinarith) (Real.log_pos hD₀1)
  refine ⟨max (137 * (2 * D₀ + 3) * Real.log (D₀ * (D₀ + 3))) (7 / 2 * C₁ * C_r),
    lt_max_of_lt_left hK₀, ?_⟩
  intro q _ χ hχ hq σ T hσ hσ1 hT
  have hCmax : (0 : ℝ) <
      max (137 * (2 * D₀ + 3) * Real.log (D₀ * (D₀ + 3))) (7 / 2 * C₁ * C_r) :=
    lt_max_of_lt_left hK₀
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQ4 : (4 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hQ1 : (1 : ℝ) ≤ (q : ℝ) * T := by linarith
  have hQ0 : (0 : ℝ) < (q : ℝ) * T := by linarith
  have hQlt : (1 : ℝ) < (q : ℝ) * T := by linarith
  have hpow1 : (1 : ℝ) ≤ ((q : ℝ) * T) ^ (14 * (1 - σ)) :=
    Real.one_le_rpow hQ1 (by linarith)
  have hpow0 : (0 : ℝ) ≤ ((q : ℝ) * T) ^ (14 * (1 - σ)) := by linarith
  by_cases hD : (q : ℝ) * T ≤ D₀
  · have hbelow := zeroCountM_le_const_of_le hχ hq (by linarith : (1 : ℝ) / 2 ≤ σ) hT hD
    calc zeroCountM χ σ T
        ≤ 137 * (2 * D₀ + 3) * Real.log (D₀ * (D₀ + 3)) := hbelow
      _ ≤ max (137 * (2 * D₀ + 3) * Real.log (D₀ * (D₀ + 3))) (7 / 2 * C₁ * C_r) :=
          le_max_left _ _
      _ ≤ max (137 * (2 * D₀ + 3) * Real.log (D₀ * (D₀ + 3))) (7 / 2 * C₁ * C_r)
            * ((q : ℝ) * T) ^ (14 * (1 - σ)) := le_mul_of_one_le_right hCmax.le hpow1
  · have hD' : D₀ < (q : ℝ) * T := not_le.mp hD
    have h10' : (10 : ℝ) ^ 20 ≤ (q : ℝ) * T := le_trans h10 hD'.le
    have hD₁' : D₁ ≤ (q : ℝ) * T := le_trans hD₁D₀ hD'.le
    rcases hσ1.lt_or_eq with hlt | heq
    · have hcount := zeroCountM_le_box_bound_mul hχ hq hσ hσ1 hT h10' hC₁0 hC₁
      have hJ0 := card_le_of_boxRep_system hratio hχ hq hσ hlt hT hD₁'
        ((Finset.Icc (-⌈T * Real.log ((q : ℝ) * T)⌉ - 1)
            (⌈T * Real.log ((q : ℝ) * T)⌉ + 1)).filter
          (fun k => k % 2 = 0 ∧ (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty))
        (fun _ hk => (Finset.mem_filter.mp hk).2.2)
        (wellSpacedAt_parity_reps (χ := χ) (σ := σ) (T := T) hQlt 0)
      have hJ1 := card_le_of_boxRep_system hratio hχ hq hσ hlt hT hD₁'
        ((Finset.Icc (-⌈T * Real.log ((q : ℝ) * T)⌉ - 1)
            (⌈T * Real.log ((q : ℝ) * T)⌉ + 1)).filter
          (fun k => k % 2 = 1 ∧ (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty))
        (fun _ hk => (Finset.mem_filter.mp hk).2.2)
        (wellSpacedAt_parity_reps (χ := χ) (σ := σ) (T := T) hQlt 1)
      have hL : (0 : ℝ) < Real.log ((q : ℝ) * T) := Real.log_pos hQlt
      set lam : ℝ := (1 - σ) * Real.log ((q : ℝ) * T) with hlamdef
      have hlam0 : (0 : ℝ) ≤ lam := mul_nonneg (by linarith) hL.le
      have hfac : 7 / 4 + 3 / 2 * lam ≤ 7 / 4 * Real.exp lam := by
        have hexp := Real.add_one_le_exp lam
        linarith
      have hexpeq : Real.exp lam = ((q : ℝ) * T) ^ (1 - σ) := by
        rw [Real.rpow_def_of_pos hQ0]
        congr 1
        rw [hlamdef]
        ring
      have hpowmul : ((q : ℝ) * T) ^ (13 * (1 - σ)) * ((q : ℝ) * T) ^ (1 - σ)
          = ((q : ℝ) * T) ^ (14 * (1 - σ)) := by
        rw [← Real.rpow_add hQ0]
        congr 1
        ring
      refine le_trans hcount ?_
      rw [Nat.cast_add]
      refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left hfac hC₁0.le)
        (add_le_add hJ0 hJ1) (by positivity) (mul_nonneg hC₁0.le (by positivity))) ?_
      have hval : C₁ * (7 / 4 * Real.exp lam)
            * (C_r * ((q : ℝ) * T) ^ (13 * (1 - σ))
              + C_r * ((q : ℝ) * T) ^ (13 * (1 - σ)))
          = 7 / 2 * C₁ * C_r * ((q : ℝ) * T) ^ (14 * (1 - σ)) := by
        rw [hexpeq, ← hpowmul]
        ring
      rw [hval]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hpow0
    · rw [zeroCountM_eq_zero_of_one_le hχ hq heq.ge]
      exact mul_nonneg hCmax.le hpow0

/-! ## (v) THE TARGET (design v2 §0, verbatim) -/

/-- **THE LOG-FREE ZERO-DENSITY THEOREM** — B2's deliverable, as the design froze it: on
`4/5 ≤ σ ≤ 1`, `T ≥ 2`, `N(σ, T, χ) ≤ C·(qT)^{D(1−σ)}` with `D ≤ 150`; the low half
(`zeroCountM_density_logfree_low`, `1378·(qT)^{150(1−σ)}` on `σ ≤ 119/120`) and the strip lifted
to the exponent `150` by the glue's monotonicity; `C := max 1378 C_strip`, `D := 150`. -/
theorem zeroCountM_density_logfree :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ D ≤ 150 ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → 2 ≤ q →
      ∀ (σ T : ℝ), 4 / 5 ≤ σ → σ ≤ 1 → 2 ≤ T →
        zeroCountM χ σ T ≤ C * ((q : ℝ) * T) ^ (D * (1 - σ)) := by
  obtain ⟨C_s, hCs, hstrip⟩ := zeroCountM_density_logfree_strip
  refine ⟨max 1378 C_s, 150, lt_max_of_lt_left (by norm_num), by norm_num, le_rfl, ?_⟩
  intro q _ χ hχ hq σ T hσ hσ1 hT
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQ4 : (4 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hQ1 : (1 : ℝ) ≤ (q : ℝ) * T := by linarith
  have hpow0 : (0 : ℝ) ≤ ((q : ℝ) * T) ^ (150 * (1 - σ)) :=
    Real.rpow_nonneg (by linarith) _
  rcases le_or_gt σ (119 / 120) with h | h
  · exact le_trans (zeroCountM_density_logfree_low χ hχ hq σ T hσ h hT)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0)
  · calc zeroCountM χ σ T
        ≤ C_s * ((q : ℝ) * T) ^ (14 * (1 - σ)) := hstrip q χ hχ hq σ T h.le hσ1 hT
      _ ≤ C_s * ((q : ℝ) * T) ^ (150 * (1 - σ)) :=
          mul_le_mul_of_nonneg_left (rpow_mul_le_rpow_of_le_150 hQ1 hσ1) hCs.le
      _ ≤ max 1378 C_s * ((q : ℝ) * T) ^ (150 * (1 - σ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpow0

/-- **The W9f exit rows** (each INVOKES a frozen row at numerals): the glue at `qT = 4`,
`σ = 1/2` (`4^{7} ≤ 4^{75}`); the `σ = 1` line at a primitive character mod `5`, `T = 2`. -/
example : (4 : ℝ) ^ (14 * (1 - (1 / 2 : ℝ))) ≤ (4 : ℝ) ^ (150 * (1 - (1 / 2 : ℝ))) :=
  rpow_mul_le_rpow_of_le_150 (by norm_num) (by norm_num)

example (χ : DirichletCharacter ℂ 5) (hχ : χ.IsPrimitive) : zeroCountM χ 1 2 = 0 :=
  zeroCountM_eq_zero_of_one_le hχ (by norm_num) le_rfl

end Salt.SW
