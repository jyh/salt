/-
# The classical theorem `Σ_{d} μ(d)/d = 0` — decay of the weighted Möbius partial sums

This module lands `mwWeighted_tendsto_zero : Tendsto mwWeighted atTop (𝓝 0)`,
i.e. `Σ_{d≤n} μ(d)/d → 0`, the gate of the sharp Barban–Vehov cancellation (DH-MAIN rung 1d).

Route (the Abelian direction, no Tauberian):
* Phase 1 (limit exists): mathlib's Abel-summation limit
  `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`
  applied to `c = μ`, `f = (·)⁻¹`, fed by the unweighted PNT rate `mmuRate_holds`, gives
  `Tendsto mwWeighted atTop (𝓝 L)` for a fixed `L`.
* The Abel identity `(★)`: mathlib's `LSeries_eq_mul_integral` applied to `μ(·)/·` yields
  `1/ζ(1+ε) = ε ∫_{t>1} Mw(⌊t⌋) t^{-(1+ε)} dt`.
* `1/ζ(1+ε) → 0` as `ε → 0⁺` from `riemannZeta_residue_one`.
* A Tannery/Abelian-mean lemma gives the mean `ε ∫ Mw(⌊t⌋) t^{-1-ε}` tends to `L`.
* Uniqueness of limits forces `L = 0`.
-/
import Mathlib
import Salt.SW.DHMain
import Salt.SW.MobiusRateClose

open MeasureTheory Filter Topology

namespace Salt.SW

open Salt.TwinBar (Mmu MmuRate)

/-! ## Banked real-analysis input: borderline integrability of `1/(t (log t)²)` -/

section Integrability
open Set

/-- The borderline "Bertrand" integrability: `1/(t (log t)²)` is integrable on `(2, ∞)`. -/
theorem integrableOn_inv_mul_log_sq_Ioi :
    IntegrableOn (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹) (Set.Ioi (2:ℝ)) := by
  set g : ℝ → ℝ := fun x => -(Real.log x)⁻¹ with hg_def
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcont : ContinuousWithinAt g (Ici (2:ℝ)) 2 := by
    have : ContinuousAt g 2 :=
      ((Real.continuousAt_log (by norm_num : (2:ℝ) ≠ 0)).inv₀ (ne_of_gt hlog2)).neg
    exact this.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (2:ℝ), HasDerivAt g ((x * (Real.log x) ^ 2)⁻¹) x := by
    intro x hx
    have hx2 : (2:ℝ) < x := hx
    have hx0 : x ≠ 0 := by positivity
    have hlogpos : (0:ℝ) < Real.log x := Real.log_pos (by linarith)
    have hlog0 : Real.log x ≠ 0 := ne_of_gt hlogpos
    have h2 : HasDerivAt (fun x => (Real.log x)⁻¹) (-x⁻¹ / (Real.log x) ^ 2) x :=
      (Real.hasDerivAt_log hx0).inv hlog0
    have h3 : HasDerivAt g (-(-x⁻¹ / (Real.log x) ^ 2)) x := h2.neg
    convert h3 using 1
    field_simp
  have g'pos : ∀ x ∈ Ioi (2:ℝ), (0:ℝ) ≤ (x * (Real.log x) ^ 2)⁻¹ := by
    intro x hx
    have hx2 : (2:ℝ) < x := hx
    have hlogpos : (0:ℝ) < Real.log x := Real.log_pos (by linarith)
    positivity
  have hg : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) :=
      Real.tendsto_log_atTop.inv_tendsto_atTop
    simpa [hg_def, neg_zero] using h1.neg
  exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv g'pos hg

/-- The `atTop` filter form of `integrableOn_inv_mul_log_sq_Ioi`. -/
theorem integrableAtFilter_inv_mul_log_sq :
    IntegrableAtFilter (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹) atTop :=
  ⟨Set.Ioi 2, Ioi_mem_atTop 2, integrableOn_inv_mul_log_sq_Ioi⟩

/-- Tannery / Abelian-mean: if `φ` is measurable, globally bounded by `B`, and `φ(t) → L` as
`t → ∞`, then the normalized moment `ε ∫_{t>1} φ(t) t^{-1-ε} dt → L` as `ε → 0⁺`. -/
theorem tannery_abel_mean {φ : ℝ → ℝ} {B L : ℝ}
    (hmeas : Measurable φ) (hB : ∀ t, |φ t| ≤ B)
    (hlim : Tendsto φ atTop (𝓝 L)) :
    Tendsto (fun ε : ℝ => ε * ∫ t in Set.Ioi (1:ℝ), φ t * t ^ (-1 - ε))
      (𝓝[>] (0:ℝ)) (𝓝 L) := by
  set M : ℝ := B + |L| with hM
  have hφLbound : ∀ t, |φ t - L| ≤ M := by
    intro t
    have h : |φ t - L| ≤ |φ t| + |L| := by
      have h2 := abs_add_le (φ t) (-L)
      rw [abs_neg] at h2
      simpa [sub_eq_add_neg] using h2
    calc |φ t - L| ≤ |φ t| + |L| := h
      _ ≤ B + |L| := by linarith [hB t]
      _ = M := hM.symm
  rw [Metric.tendsto_nhds]
  intro δ' hδ'
  set δ : ℝ := δ' / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hev : ∀ᶠ t in atTop, dist (φ t) L < δ := (Metric.tendsto_nhds.mp hlim) δ hδpos
  rw [eventually_atTop] at hev
  obtain ⟨T₀, hT₀⟩ := hev
  set T : ℝ := max T₀ 1 with hTdef
  have hT1 : (1:ℝ) ≤ T := le_max_right _ _
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hTne : T ≠ 0 := ne_of_gt hTpos
  have hTδ : ∀ t, t ∈ Set.Ioi T → |φ t - L| ≤ δ := by
    intro t ht
    have htT₀ : T₀ ≤ t := le_of_lt (lt_of_le_of_lt (le_max_left _ _) ht)
    have hd := hT₀ t htT₀
    rw [Real.dist_eq] at hd
    exact hd.le
  have hTrpow : Tendsto (fun ε : ℝ => T ^ (-ε)) (𝓝[>](0:ℝ)) (𝓝 1) := by
    have hcont : Tendsto (fun ε : ℝ => T ^ (-ε)) (𝓝 (0:ℝ)) (𝓝 1) := by
      have h := ((Real.continuous_const_rpow hTne).comp continuous_neg).tendsto (0:ℝ)
      simpa [Function.comp_def] using h
    exact hcont.mono_left nhdsWithin_le_nhds
  have htend : Tendsto (fun ε : ℝ => M * (1 - T ^ (-ε)) + δ) (𝓝[>](0:ℝ)) (𝓝 δ) := by
    have h0 := Tendsto.add_const δ ((Tendsto.const_sub 1 hTrpow).const_mul M)
    simpa using h0
  have hbnd : ∀ (μ : Measure ℝ), ∀ᵐ t ∂μ, ‖φ t - L‖ ≤ M :=
    fun μ => ae_of_all μ (fun t => by rw [Real.norm_eq_abs]; exact hφLbound t)
  have hbd : ∀ ε : ℝ, 0 < ε →
      dist (ε * ∫ t in Set.Ioi (1:ℝ), φ t * t ^ (-1 - ε)) L ≤ M * (1 - T ^ (-ε)) + δ := by
    intro ε hε
    have hεne : ε ≠ 0 := ne_of_gt hε
    rw [Real.dist_eq]
    set r := -1 - ε with hrdef
    have hr : r < -1 := by rw [hrdef]; linarith
    have hr1 : r + 1 = -ε := by rw [hrdef]; ring
    have hint1 : IntegrableOn (fun t => t ^ r) (Set.Ioi (1:ℝ)) :=
      integrableOn_Ioi_rpow_of_lt hr one_pos
    have hintT : IntegrableOn (fun t => t ^ r) (Set.Ioi T) :=
      integrableOn_Ioi_rpow_of_lt hr hTpos
    have hintOc : IntegrableOn (fun t => t ^ r) (Set.Ioc (1:ℝ) T) :=
      hint1.mono_set Set.Ioc_subset_Ioi_self
    have hval1 : ∫ t in Set.Ioi (1:ℝ), t ^ r = 1 / ε := by
      rw [integral_Ioi_rpow_of_lt hr one_pos, Real.one_rpow, hr1]; field_simp
    have hvalT : ∫ t in Set.Ioi T, t ^ r = T ^ (-ε) / ε := by
      rw [integral_Ioi_rpow_of_lt hr hTpos, hr1]; field_simp
    have hεIoiT : ε * ∫ t in Set.Ioi T, t ^ r = T ^ (-ε) := by
      rw [hvalT]; field_simp
    have hIocval : ∫ t in Set.Ioc (1:ℝ) T, t ^ r
        = (∫ t in Set.Ioi (1:ℝ), t ^ r) - ∫ t in Set.Ioi T, t ^ r := by
      have hu : ∫ t in Set.Ioi (1:ℝ), t ^ r
          = (∫ t in Set.Ioc (1:ℝ) T, t ^ r) + ∫ t in Set.Ioi T, t ^ r := by
        rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hintOc hintT,
            Ioc_union_Ioi_eq_Ioi hT1]
      linarith
    have hεIoc : ε * ∫ t in Set.Ioc (1:ℝ) T, t ^ r = 1 - T ^ (-ε) := by
      rw [hIocval, hval1, hvalT]; field_simp
    have haesmφ' : AEStronglyMeasurable φ (volume.restrict (Set.Ioi (1:ℝ))) :=
      hmeas.aestronglyMeasurable
    have haesmψ : ∀ (s : Set ℝ),
        AEStronglyMeasurable (fun t => φ t - L) (volume.restrict s) :=
      fun s => (hmeas.sub measurable_const).aestronglyMeasurable
    have hψint1 : IntegrableOn (fun t => (φ t - L) * t ^ r) (Set.Ioi (1:ℝ)) :=
      hint1.bdd_mul (haesmψ _) (hbnd _)
    have hψintT : IntegrableOn (fun t => (φ t - L) * t ^ r) (Set.Ioi T) :=
      hintT.bdd_mul (haesmψ _) (hbnd _)
    have hψintOc : IntegrableOn (fun t => (φ t - L) * t ^ r) (Set.Ioc (1:ℝ) T) :=
      hintOc.bdd_mul (haesmψ _) (hbnd _)
    have hφint : IntegrableOn (fun t => φ t * t ^ r) (Set.Ioi (1:ℝ)) :=
      hint1.bdd_mul haesmφ'
        (ae_of_all _ (fun t => by rw [Real.norm_eq_abs]; exact hB t))
    have hLint : IntegrableOn (fun t => L * t ^ r) (Set.Ioi (1:ℝ)) := hint1.const_mul L
    have hkey : ε * (∫ t in Set.Ioi (1:ℝ), φ t * t ^ r) - L
        = ε * ∫ t in Set.Ioi (1:ℝ), (φ t - L) * t ^ r := by
      have hsplit : ∫ t in Set.Ioi (1:ℝ), φ t * t ^ r
          = (∫ t in Set.Ioi (1:ℝ), (φ t - L) * t ^ r)
            + ∫ t in Set.Ioi (1:ℝ), L * t ^ r := by
        rw [← integral_add hψint1 hLint]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _; ring
      rw [hsplit, integral_const_mul, hval1]
      field_simp; ring
    rw [hkey, abs_mul, abs_of_pos hε]
    have hUsplit : ∫ t in Set.Ioi (1:ℝ), (φ t - L) * t ^ r
        = (∫ t in Set.Ioc (1:ℝ) T, (φ t - L) * t ^ r)
          + ∫ t in Set.Ioi T, (φ t - L) * t ^ r := by
      rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hψintOc hψintT,
          Ioc_union_Ioi_eq_Ioi hT1]
    have head : |∫ t in Set.Ioc (1:ℝ) T, (φ t - L) * t ^ r|
        ≤ M * ∫ t in Set.Ioc (1:ℝ) T, t ^ r := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul M (fun t => t ^ r)]
      refine setIntegral_mono_on hψintOc.norm (hintOc.const_mul M) measurableSet_Ioc
        (fun t ht => ?_)
      have htpos : (0:ℝ) < t := lt_trans one_pos ht.1
      have htr : (0:ℝ) ≤ t ^ r := Real.rpow_nonneg htpos.le r
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg htr]
      exact mul_le_mul_of_nonneg_right (hφLbound t) htr
    have tail : |∫ t in Set.Ioi T, (φ t - L) * t ^ r|
        ≤ δ * ∫ t in Set.Ioi T, t ^ r := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul δ (fun t => t ^ r)]
      refine setIntegral_mono_on hψintT.norm (hintT.const_mul δ) measurableSet_Ioi
        (fun t ht => ?_)
      have htpos : (0:ℝ) < t := hTpos.trans ht
      have htr : (0:ℝ) ≤ t ^ r := Real.rpow_nonneg htpos.le r
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg htr]
      exact mul_le_mul_of_nonneg_right (hTδ t ht) htr
    calc ε * |∫ t in Set.Ioi (1:ℝ), (φ t - L) * t ^ r|
        ≤ ε * (|∫ t in Set.Ioc (1:ℝ) T, (φ t - L) * t ^ r|
                + |∫ t in Set.Ioi T, (φ t - L) * t ^ r|) := by
          refine mul_le_mul_of_nonneg_left ?_ hε.le
          rw [hUsplit]; exact abs_add_le _ _
      _ ≤ ε * (M * (∫ t in Set.Ioc (1:ℝ) T, t ^ r)
              + δ * (∫ t in Set.Ioi T, t ^ r)) := by
          refine mul_le_mul_of_nonneg_left ?_ hε.le
          exact add_le_add head tail
      _ = M * (ε * ∫ t in Set.Ioc (1:ℝ) T, t ^ r)
          + δ * (ε * ∫ t in Set.Ioi T, t ^ r) := by ring
      _ = M * (1 - T ^ (-ε)) + δ * T ^ (-ε) := by rw [hεIoc, hεIoiT]
      _ ≤ M * (1 - T ^ (-ε)) + δ := by
          have h1 : T ^ (-ε) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hT1 (by linarith)
          have h2 : δ * T ^ (-ε) ≤ δ := by
            calc δ * T ^ (-ε) ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδpos.le
              _ = δ := mul_one δ
          linarith
  filter_upwards [self_mem_nhdsWithin,
    htend.eventually_lt_const (show δ < δ' by rw [hδdef]; linarith)] with ε hε hlt
  exact (hbd ε (Set.mem_Ioi.mp hε)).trans_lt hlt

end Integrability

/-! ## The PNT-rate corollary `M_μ(n)/n → 0` -/

open ArithmeticFunction Finset Asymptotics

/-- The unweighted Möbius mean tends to zero: `M_μ(n)/n → 0`, from `mmuRate_holds` at `A = 1`. -/
theorem Mmu_div_tendsto_zero : Tendsto (fun n : ℕ => Mmu n / (n:ℝ)) atTop (𝓝 0) := by
  obtain ⟨C, x₀, hC, hb⟩ := mmuRate_holds 1 (by norm_num)
  have hg : Tendsto (fun n : ℕ => C / Real.log n) atTop (𝓝 0) := by
    have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv] using hlog.inv_tendsto_atTop.const_mul C
  have habs : ∀ᶠ n : ℕ in atTop, |Mmu n / (n:ℝ)| ≤ C / Real.log n := by
    filter_upwards [eventually_ge_atTop (max x₀ 2)] with n hn
    have hnx : x₀ ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
    have hnpos : (0:ℝ) < (n:ℝ) := by linarith
    have hlogpos : (0:ℝ) < Real.log n := Real.log_pos (by linarith)
    have hbn := hb n hnx
    rw [Real.rpow_one] at hbn
    have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hnpos
    have hl0 : Real.log n ≠ 0 := ne_of_gt hlogpos
    rw [abs_div, Nat.abs_cast]
    calc |Mmu n| / (n:ℝ)
        ≤ (C * (n:ℝ) / Real.log n) / (n:ℝ) := (div_le_div_iff_of_pos_right hnpos).mpr hbn
      _ = C / Real.log n := by field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hg.neg) hg ?_ ?_
  · exact habs.mono fun n h => (abs_le.mp h).1
  · exact habs.mono fun n h => (abs_le.mp h).2

/-- `∑_{k≤n} μ(k) = M_μ(n)` with the summation index starting at `0` (the `k=0` term vanishes). -/
theorem sum_Icc_zero_moebius (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, ((moebius k : ℤ) : ℝ) = Mmu n := by
  rw [Mmu]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
  · intro x hx hx'; rw [Finset.mem_Icc] at hx hx'
    have hx0 : x = 0 := by omega
    subst hx0; simp

/-! ## Phase 1 — the weighted partial sum converges (Abel summation against `mmuRate`) -/

/-- The Abel-summand `bigO` domination `deriv(t⁻¹)·M_μ(⌊t⌋) = O(1/(t log²t))` (from `mmuRate` at
`A=2`), feeding the Abel-summation limit theorem. -/
theorem abelSummand_isBigO :
    (fun t : ℝ => deriv (fun x : ℝ => x⁻¹) t *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((moebius k : ℤ) : ℝ))
      =O[atTop] (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹) := by
  have hMmuSum : ∀ n : ℕ, ∑ k ∈ Finset.Icc 0 n, ((moebius k : ℤ) : ℝ) = Mmu n := by
    intro n
    rw [Mmu]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx
      rw [Finset.mem_Icc] at hx ⊢; omega
    · intro x hx hx'
      rw [Finset.mem_Icc] at hx hx'
      have : x = 0 := by omega
      subst this
      simp
  obtain ⟨C₂, x₀, hC₂, hb₂⟩ := Salt.SW.mmuRate_holds 2 (by norm_num)
  rw [Asymptotics.isBigO_iff]
  refine ⟨4 * C₂, ?_⟩
  filter_upwards [eventually_ge_atTop (max (x₀:ℝ) 3)] with t ht
  have ht3 : (3:ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have htx0 : (x₀:ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htpos : (0:ℝ) < t := by linarith
  have hfloor3 : 3 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht3)
  have hx0n : x₀ ≤ ⌊t⌋₊ := Nat.le_floor htx0
  have hlogt : (0:ℝ) < Real.log t := Real.log_pos (by linarith)
  have hfloorR3 : (3:ℝ) ≤ (⌊t⌋₊:ℝ) := by exact_mod_cast hfloor3
  have hLn : (0:ℝ) < Real.log ⌊t⌋₊ := Real.log_pos (by linarith)
  have A2 : (⌊t⌋₊:ℝ) ≤ t := Nat.floor_le htpos.le
  have hfloor_ge : t - 1 < (⌊t⌋₊:ℝ) := by have := Nat.lt_floor_add_one t; linarith
  have htsq : t ≤ (⌊t⌋₊:ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (⌊t⌋₊:ℝ) - (t - 1) by linarith)
      (show (0:ℝ) ≤ (⌊t⌋₊:ℝ) + (t - 1) by linarith), ht3, sq_nonneg (t - 2)]
  have hlogt_le : Real.log t ≤ 2 * Real.log ⌊t⌋₊ := by
    have h := Real.log_le_log htpos htsq
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have B3 : (Real.log t) ^ 2 ≤ 4 * (Real.log ⌊t⌋₊) ^ 2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 * Real.log ⌊t⌋₊ - Real.log t by linarith)
      (show (0:ℝ) ≤ 2 * Real.log ⌊t⌋₊ + Real.log t by linarith)]
  have hrp : (Real.log ⌊t⌋₊) ^ (2:ℝ) = (Real.log ⌊t⌋₊) ^ 2 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have A1 : |Mmu ⌊t⌋₊| ≤ C₂ * ⌊t⌋₊ / (Real.log ⌊t⌋₊) ^ 2 := by
    have := hb₂ ⌊t⌋₊ hx0n
    rwa [hrp] at this
  rw [deriv_inv, hMmuSum ⌊t⌋₊, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (t ^ 2)⁻¹),
    abs_of_nonneg (inv_nonneg.mpr (mul_nonneg htpos.le (sq_nonneg (Real.log t))))]
  set M := |Mmu ⌊t⌋₊| with hM
  have hLn2 : (0:ℝ) < (Real.log ⌊t⌋₊) ^ 2 := pow_pos hLn 2
  have B1 : M * (Real.log ⌊t⌋₊) ^ 2 ≤ C₂ * ⌊t⌋₊ := (le_div_iff₀ hLn2).mp A1
  have key : M * (t * (Real.log t) ^ 2) ≤ 4 * C₂ * t ^ 2 := by
    calc M * (t * (Real.log t) ^ 2)
        ≤ M * (t * (4 * (Real.log ⌊t⌋₊) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left B3 htpos.le) (abs_nonneg _)
      _ = 4 * t * (M * (Real.log ⌊t⌋₊) ^ 2) := by ring
      _ ≤ 4 * t * (C₂ * ⌊t⌋₊) := mul_le_mul_of_nonneg_left B1 (by linarith)
      _ ≤ 4 * t * (C₂ * t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left A2 hC₂.le) (by linarith)
      _ = 4 * C₂ * t ^ 2 := by ring
  rw [← div_eq_inv_mul, ← div_eq_mul_inv,
    div_le_div_iff₀ (by positivity) (mul_pos htpos (pow_pos hlogt 2))]
  exact key

/-- **Phase 1 (the stone).** The weighted Möbius partial sum `Mw(n) = Σ_{d≤n} μ(d)/d` converges:
`Tendsto mwWeighted atTop (𝓝 L)` for some `L`. Via mathlib's Abel-summation limit
`tendsto_sum_mul_atTop_nhds_one_sub_integral₀` with `c = μ`, `f = (·)⁻¹`, boundary limit
`M_μ(n)/n → 0`, and the `bigO`-integrable tail `1/(t log²t)`. -/
theorem mwWeighted_tendsto_exists : ∃ L : ℝ, Tendsto mwWeighted atTop (𝓝 L) := by
  have hf_diff : ∀ t ∈ Set.Ici (1:ℝ), DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le one_pos ht))).differentiableAt
  have hf_int : LocallyIntegrableOn (deriv (fun x : ℝ => x⁻¹)) (Set.Ici (1:ℝ)) := by
    rw [deriv_inv']
    refine ((ContinuousOn.inv₀ ((continuous_pow 2).continuousOn) ?_).neg).locallyIntegrableOn
      measurableSet_Ici
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le one_pos hx))
  have h_lim : Tendsto (fun n : ℕ => (fun x : ℝ => x⁻¹) (n : ℝ)
      * ∑ k ∈ Finset.Icc 0 n, ((moebius k : ℤ) : ℝ)) atTop (𝓝 0) := by
    refine Mmu_div_tendsto_zero.congr' ?_
    filter_upwards with n
    rw [sum_Icc_zero_moebius n, div_eq_inv_mul]
  have hsum : ∀ n : ℕ, ∑ k ∈ Finset.Icc 0 n, (fun x : ℝ => x⁻¹) (k : ℝ) * ((moebius k : ℤ) : ℝ)
      = mwWeighted n := by
    intro n
    rw [mwWeighted]
    rw [← Finset.sum_subset (show Finset.Icc 1 n ⊆ Finset.Icc 0 n from by
          intro x hx; rw [Finset.mem_Icc] at *; omega) ?_]
    · exact Finset.sum_congr rfl (fun k _ => by rw [mul_comm, ← div_eq_mul_inv])
    · intro x hx hx'
      rw [Finset.mem_Icc] at hx hx'
      have hx0 : x = 0 := by omega
      subst hx0; simp
  have key := tendsto_sum_mul_atTop_nhds_one_sub_integral₀
    (fun k : ℕ => ((moebius k : ℤ) : ℝ)) (by simp) hf_diff hf_int h_lim abelSummand_isBigO
    integrableAtFilter_inv_mul_log_sq
  exact ⟨_, key.congr fun n => hsum n⟩

/-! ## The Abel identity `(★)` : `1/ζ(1+ε) = ε ∫_{t>1} Mw(⌊t⌋) t^{-(1+ε)}` -/

/-- **The Abel identity `(★)`.** For `ε > 0`, `(1/ζ(1+ε)).re = ε ∫_{t>1} Mw(⌊t⌋) t^{-1-ε} dt`.
Via mathlib's `LSeries_eq_mul_integral` applied to `μ(·)/·` (partial sums `Mw`, bounded so
`O(n^0)`), and `L(μ,s) = 1/ζ(s)`. -/
theorem mwWeighted_integral_eq (ε : ℝ) (hε : 0 < ε) :
    ((riemannZeta ((ε : ℂ) + 1))⁻¹).re
      = ε * ∫ t in Set.Ioi (1:ℝ), mwWeighted ⌊t⌋₊ * t ^ (-1 - ε) := by
  set mc : ℕ → ℂ := fun n => (moebius n : ℂ) / (n : ℂ) with hmc
  have hs1 : (1:ℝ) < ((ε : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]; linarith
  have hterm : ∀ n : ℕ, LSeries.term mc (ε : ℂ) n
      = LSeries.term (fun k => (moebius k : ℂ)) ((ε : ℂ) + 1) n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpow : (n : ℂ) ^ ((ε : ℂ) + 1) = (n : ℂ) ^ (ε : ℂ) * (n : ℂ) := by
        rw [Complex.cpow_add _ _ hn0, Complex.cpow_one]
      simp only [LSeries.term_of_ne_zero hn, hmc]
      rw [div_div, hpow, mul_comm ((n : ℂ) ^ (ε : ℂ)) (n : ℂ)]
  have hLSeq : LSeries mc (ε : ℂ) = LSeries (fun k => (moebius k : ℂ)) ((ε : ℂ) + 1) := by
    unfold LSeries; exact tsum_congr hterm
  have hzne : riemannZeta ((ε : ℂ) + 1) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hmul := LSeries_zeta_mul_Lseries_moebius hs1
  rw [LSeries_zeta_eq_riemannZeta hs1] at hmul
  have hzeta : LSeries (fun k => (moebius k : ℂ)) ((ε : ℂ) + 1)
      = (riemannZeta ((ε : ℂ) + 1))⁻¹ := by
    rw [inv_eq_one_div, eq_div_iff hzne, mul_comm]; exact hmul
  have hSummable : LSeriesSummable mc (ε : ℂ) :=
    (summable_congr hterm).mpr ((LSeriesSummable_moebius_iff (s := (ε : ℂ) + 1)).mpr hs1)
  have hcast : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, mc k = ((mwWeighted n : ℝ) : ℂ) := by
    intro n
    rw [mwWeighted, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hmc]; push_cast; ring
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, mc k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (0:ℝ) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hcast n, Complex.norm_real, Real.norm_eq_abs, Real.rpow_zero, norm_one, mul_one]
    exact abs_mwWeighted_le_one hn
  have hInt := LSeries_eq_mul_integral mc (le_refl (0:ℝ))
    (by simpa using hε) hSummable hO
  have hmain : (riemannZeta ((ε : ℂ) + 1))⁻¹
      = ((ε * ∫ t in Set.Ioi (1:ℝ), mwWeighted ⌊t⌋₊ * t ^ (-1 - ε) : ℝ) : ℂ) := by
    rw [← hzeta, ← hLSeq, hInt, Complex.ofReal_mul]
    congr 1
    trans (∫ t in Set.Ioi (1:ℝ), ((mwWeighted ⌊t⌋₊ * t ^ (-1 - ε) : ℝ) : ℂ))
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have htpos : (0:ℝ) < t := lt_trans one_pos ht
      have hcpow : (t : ℂ) ^ (-((ε : ℂ) + 1)) = ((t ^ (-1 - ε) : ℝ) : ℂ) := by
        rw [show (-((ε : ℂ) + 1)) = (((-1 - ε : ℝ)) : ℂ) by push_cast; ring]
        exact (Complex.ofReal_cpow htpos.le (-1 - ε)).symm
      simp only [hcast ⌊t⌋₊, hcpow, ← Complex.ofReal_mul]
    · exact integral_ofReal
  have := congrArg Complex.re hmain
  rwa [Complex.ofReal_re] at this

/-! ## The `ζ`-residue corollary `(1/ζ(1+ε)).re → 0` -/

/-- `(1/ζ(1+ε)).re → 0` as `ε → 0⁺`, from `riemannZeta_residue_one`. -/
theorem inv_zeta_re_tendsto :
    Tendsto (fun ε : ℝ => ((riemannZeta ((ε : ℂ) + 1))⁻¹).re) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hres := riemannZeta_residue_one
  have hinv : Tendsto (fun s : ℂ => (riemannZeta s)⁻¹) (𝓝[≠] (1:ℂ)) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℂ => ((s - 1) * riemannZeta s)⁻¹) (𝓝[≠] (1:ℂ)) (𝓝 ((1:ℂ)⁻¹)) :=
      hres.inv₀ (by norm_num)
    have h2 : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1:ℂ)) (𝓝 0) := by
      have hc : Continuous (fun s : ℂ => s - 1) := continuous_id.sub continuous_const
      have h := (hc.tendsto (1:ℂ)).mono_left
        (nhdsWithin_le_nhds (a := (1:ℂ)) (s := {(1:ℂ)}ᶜ))
      simpa using h
    have h3 : Tendsto (fun s : ℂ => (s - 1) * ((s - 1) * riemannZeta s)⁻¹)
        (𝓝[≠] (1:ℂ)) (𝓝 0) := by
      have := h2.mul h1
      simpa using this
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hsub, one_mul]
  have hmap : Tendsto (fun ε : ℝ => (ε : ℂ) + 1) (𝓝[>] (0:ℝ)) (𝓝[≠] (1:ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => (ε : ℂ) + 1) (𝓝 (0:ℝ)) (𝓝 ((0:ℂ) + 1)) :=
        (Complex.continuous_ofReal.tendsto 0).add tendsto_const_nhds
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεpos : 0 < ε := hε
      have hne : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hεpos
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hc
      exact hne (by linear_combination hc)
  have hcomp := (Complex.continuous_re.tendsto (0:ℂ)).comp (hinv.comp hmap)
  simpa [Function.comp_def] using hcomp

/-! ## The identification `L = 0` and the theorem -/

/-- **The Möbius decay theorem.** `Σ_{d≤n} μ(d)/d → 0`. Equivalent to `Σ μ(d)/d = 0` / `1/ζ(1) = 0`,
a genuine PNT corollary. The gate of the sharp Barban–Vehov cancellation (DH-MAIN rung 1d). -/
theorem mwWeighted_tendsto_zero : Tendsto mwWeighted atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ := mwWeighted_tendsto_exists
  have hmeas : Measurable (fun t : ℝ => mwWeighted ⌊t⌋₊) :=
    (measurable_from_top : Measurable mwWeighted).comp Nat.measurable_floor
  have hB : ∀ t : ℝ, |mwWeighted ⌊t⌋₊| ≤ 1 := by
    intro t
    rcases Nat.eq_zero_or_pos ⌊t⌋₊ with h | h
    · rw [h]; simp [mwWeighted]
    · exact abs_mwWeighted_le_one h
  have hφlim : Tendsto (fun t : ℝ => mwWeighted ⌊t⌋₊) atTop (𝓝 L) :=
    hL.comp tendsto_nat_floor_atTop
  have hTan := tannery_abel_mean hmeas hB hφlim
  have hGre : Tendsto (fun ε : ℝ => ((riemannZeta ((ε : ℂ) + 1))⁻¹).re) (𝓝[>] (0:ℝ)) (𝓝 L) := by
    refine hTan.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (mwWeighted_integral_eq ε hε).symm
  have hL0 : L = 0 := tendsto_nhds_unique hGre inv_zeta_re_tendsto
  rwa [hL0] at hL

end Salt.SW
