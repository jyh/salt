/-
# The poly-log bound on `1/ζ` over the shallow half-plane (`T-1ζ′`)

`zeta_inv_shallow` : `∃ c₄ > 0, ∃ C > 0, ∀ σ t,`
`1 − c₄/log(|t|+2)⁹ ≤ σ → σ+it ≠ 1 → ‖ζ(σ+it)⁻¹‖ ≤ C·log(|t|+2)⁷`.

Second node of the trophy chain (`T-lo′ → T-1ζ′ → T-Mμ`).  A three-case dispatch
(frozen at `docs/exploration/s2-trackA-design.md`, AMENDMENT 2):

1. `|t| ≥ 2`: the corollary of `zeta_lower_shallow` (`T-lo′`).  From `‖ζ‖ ≥ c/L⁷ > 0`
   we get `ζ ≠ 0` and `‖ζ⁻¹‖ = ‖ζ‖⁻¹ ≤ L⁷/c` (`L = log(|t|+2)`).
2. `|t| < 2 ∧ σ ≤ 3`: the compact pole-patch.  On `s ≠ 1`, `ζ = Zc/(s−1)` so
   `‖ζ⁻¹‖ = ‖s−1‖/‖Zc‖`.  `Zc` (`= (s−1)ζ`, entire, `Zc 1 = 1`) is continuous and
   nonvanishing on the compact rectangle `R = {a ≤ Re ≤ 3, |Im| ≤ 2}`
   (`a = 1 − c₄/log2⁹`): a zero would give `ζ = 0`, impossible by
   `riemannZeta_ne_zero_of_one_le_re` (`Re ≥ 1`) or by the landed
   `zeta_zero_free_region` (`1/2 ≤ Re < 1`; compatibility below).  Compactness
   (`IsCompact.exists_isMinOn` on `‖Zc‖`) gives `δ > 0`, so `‖ζ⁻¹‖ ≤ ‖s−1‖/δ ≤ 4/δ`.
3. `|t| < 2 ∧ σ > 3`: `Re s > 3 ≥ 2`, so `‖ζ‖ ≥ 1/4` (`zeta_norm_ge`), `‖ζ⁻¹‖ ≤ 4`.

Compatibility (the III.3″ discipline): the patch must sit inside
`zeta_zero_free_region`, whose landed shape is `Re ρ ≤ 1 − c₃/log(|Im ρ|+2)` for
`Re ρ ≥ 1/2` (log¹, range `Re ≥ 1/2`) — matching the freeze (the constant is the
existential `c₃`, not the design's `1/50456`, but the *shape* is what the patch
consumes).  Choosing `c₄ := min c₄₀ (min (log2⁹/2) (c₃·log2⁹/(2·log4)))` forces
`a ≥ 1/2` and `c₄/log2⁹ < c₃/log4`, so no zero of `ζ` meets `R` (`|Im| ≤ 2 ⇒
log(|Im|+2) ≤ log4`).  Both `c₄` and `C` sit OUTSIDE the `∀` (III.4: `T-Mμ`
destructures them once); `C := max (1/c) (max (4/(δ·log2⁷)) (4/log2⁷))`.

III.3″ witness (mpmath, dps 40): the ratio `1/|ζ(s)| / log(|t|+2)⁷`, evaluated at
  · patch near-pole  σ=1−1e−6, t=0    : 1.30e−5   (small: `1/|ζ| → 0` at the pole)
  · patch interior   σ=1−1e−6, t=1    : 0.473
  · patch deep       σ=0.9,    t=1    : 0.502   (the largest observed)
  · patch corner     σ=3,      t=1.5  : 0.197
  · boundary         σ=1−1e−6, t=2    : 0.146
  · corollary        σ≈1,      t=1e6  : 9.31e−9
stays ≤ 0.51 across the patch and `→0` in the corollary region, so a finite `C`
exists (empirically `≈ 1`) with margin.  The proof's `C` is the branch-max, larger
than the empirical value — it also absorbs the symbolic `c, c₃, δ`.
-/
import Salt.SW.ZetaLowerShallow
import Salt.SW.ZetaZeroFree

namespace Salt.SW

open Complex Metric

/-- **The compact pole-patch lower bound for `Zc`.**  Given `1/2 ≤ a` and the
zero-free compatibility `1 − a < c₃/log 4` (`c₃` the `zeta_zero_free_region`
constant, passed as `Hzfr`), `Zc = (s−1)ζ` is continuous and nonvanishing on the
compact rectangle `R = {a ≤ Re ≤ 3, |Im| ≤ 2}`, so `‖Zc‖` attains a positive
minimum `δ` there. -/
lemma Zc_patch_lower {a c₃ : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1) (hc₃ : 0 < c₃)
    (hcompat : 1 - a < c₃ / Real.log 4)
    (Hzfr : ∀ {ρ : ℂ}, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re →
      ρ.re ≤ 1 - c₃ / Real.log (|ρ.im| + 2)) :
    ∃ δ > 0, ∀ z : ℂ, a ≤ z.re → z.re ≤ 3 → |z.im| ≤ 2 → δ ≤ ‖Zc z‖ := by
  set R : Set ℂ := {z : ℂ | a ≤ z.re ∧ z.re ≤ 3 ∧ |z.im| ≤ 2} with hRdef
  -- `R` is closed (three continuous inequalities) and bounded, hence compact.
  have hEq : R = {z : ℂ | a ≤ z.re} ∩ ({z : ℂ | z.re ≤ 3} ∩ {z : ℂ | |z.im| ≤ 2}) := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3⟩
  have hRclosed : IsClosed R := by
    rw [hEq]
    exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        (isClosed_le Complex.continuous_im.abs continuous_const))
  have hRsub : R ⊆ closedBall (0 : ℂ) 5 := by
    intro z hz
    obtain ⟨hzlo, hzhi, hzim⟩ := hz
    rw [mem_closedBall, Complex.dist_eq, sub_zero]
    have hnorm := Complex.norm_le_abs_re_add_abs_im z
    have hre : |z.re| ≤ 3 := by rw [abs_of_pos (by linarith : (0 : ℝ) < z.re)]; exact hzhi
    linarith [hnorm, hzim, hre]
  have hRcompact : IsCompact R :=
    (isCompact_closedBall (0 : ℂ) 5).of_isClosed_subset hRclosed hRsub
  have hRne : R.Nonempty := by
    refine ⟨(1 : ℂ), ?_, ?_, ?_⟩
    · rw [Complex.one_re]; exact ha1
    · rw [Complex.one_re]; norm_num
    · rw [Complex.one_im, abs_zero]; norm_num
  -- `Zc` is nonvanishing on `R`.
  have hZcne : ∀ z ∈ R, Zc z ≠ 0 := by
    intro z hz
    obtain ⟨hzlo, hzhi, hzim⟩ := hz
    rcases eq_or_ne z 1 with rfl | hz1
    · rw [Zc_one]; exact one_ne_zero
    · rw [Zc_eq_of_ne hz1]
      refine mul_ne_zero (sub_ne_zero.mpr hz1) ?_
      intro hζ0
      have hzre_half : 1 / 2 ≤ z.re := le_trans ha hzlo
      rcases le_or_gt 1 z.re with h1 | h1
      · exact riemannZeta_ne_zero_of_one_le_re h1 hζ0
      · have hreg := Hzfr hζ0 hzre_half
        have hlogpos : 0 < Real.log (|z.im| + 2) := Real.log_pos (by linarith [abs_nonneg z.im])
        have hlog4 : Real.log (|z.im| + 2) ≤ Real.log 4 :=
          Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith [hzim])
        have hmono : c₃ / Real.log 4 ≤ c₃ / Real.log (|z.im| + 2) :=
          div_le_div_of_nonneg_left hc₃.le hlogpos hlog4
        linarith [hreg, hmono, hcompat, hzlo]
  -- The extreme value theorem furnishes the positive minimum.
  have hcont : ContinuousOn (fun z => ‖Zc z‖) R := (Zc_differentiable.continuous.norm).continuousOn
  obtain ⟨z₀, hz₀R, hz₀min⟩ := hRcompact.exists_isMinOn hRne hcont
  refine ⟨‖Zc z₀‖, norm_pos_iff.mpr (hZcne z₀ hz₀R), ?_⟩
  intro z hzlo hzhi hzim
  exact isMinOn_iff.mp hz₀min z ⟨hzlo, hzhi, hzim⟩

/-- **`T-1ζ′` — the poly-log bound on `1/ζ` over the shallow half-plane.**  There is
a window width `c₄ > 0` and a constant `C > 0` with
`‖ζ(σ+it)⁻¹‖ ≤ C·log(|t|+2)⁷` throughout the shallow strip
`1 − c₄/log(|t|+2)⁹ ≤ σ` (off the pole `s ≠ 1`).  Corollary of `zeta_lower_shallow`
for `|t| ≥ 2`; the compact pole-patch (`Zc_patch_lower`, gated by
`zeta_zero_free_region`) for `|t| < 2, σ ≤ 3`; and `zeta_norm_ge` for `σ > 3`. -/
theorem zeta_inv_shallow : ∃ c₄ > 0, ∃ C > 0, ∀ σ t : ℝ,
    1 - c₄ / Real.log (|t| + 2) ^ 9 ≤ σ → (σ : ℂ) + (t : ℂ) * I ≠ 1 →
      ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ C * Real.log (|t| + 2) ^ 7 := by
  obtain ⟨c₄₀, hc₄₀, c, hc, Hlow⟩ := zeta_lower_shallow
  obtain ⟨c₃, hc₃, Hzfr⟩ := zeta_zero_free_region
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog29pos : 0 < Real.log 2 ^ 9 := pow_pos hlog2pos 9
  have hlog27pos : 0 < Real.log 2 ^ 7 := pow_pos hlog2pos 7
  have h2log4pos : 0 < 2 * Real.log 4 := by linarith
  -- the window constant `c₄`, small enough for the zero-free compatibility
  set c₄ : ℝ := min c₄₀ (min (Real.log 2 ^ 9 / 2) (c₃ * Real.log 2 ^ 9 / (2 * Real.log 4)))
    with hc₄def
  have hBpos : 0 < c₃ * Real.log 2 ^ 9 / (2 * Real.log 4) :=
    div_pos (mul_pos hc₃ hlog29pos) h2log4pos
  have hc₄pos : 0 < c₄ := lt_min hc₄₀ (lt_min (by positivity) hBpos)
  have hc₄_le0 : c₄ ≤ c₄₀ := min_le_left _ _
  have hc₄_leA : c₄ ≤ Real.log 2 ^ 9 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hc₄_leB : c₄ ≤ c₃ * Real.log 2 ^ 9 / (2 * Real.log 4) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  -- the box floor `a` and its compatibility facts
  set a : ℝ := 1 - c₄ / Real.log 2 ^ 9 with hadef
  have hah : c₄ / Real.log 2 ^ 9 ≤ 1 / 2 := by rw [div_le_iff₀ hlog29pos]; linarith [hc₄_leA]
  have ha_half : 1 / 2 ≤ a := by rw [hadef]; linarith [hah]
  have ha_one : a ≤ 1 := by rw [hadef]; linarith [div_pos hc₄pos hlog29pos]
  have hcross : c₄ * Real.log 4 < c₃ * Real.log 2 ^ 9 := by
    have h := hc₄_leB
    rw [le_div_iff₀ h2log4pos] at h
    nlinarith [h, mul_pos hc₃ hlog29pos]
  have hcompat : 1 - a < c₃ / Real.log 4 := by
    rw [hadef]
    have : c₄ / Real.log 2 ^ 9 < c₃ / Real.log 4 :=
      (div_lt_div_iff₀ hlog29pos hlog4pos).mpr hcross
    linarith [this]
  -- the compact-patch minimum `δ`
  obtain ⟨δ, hδpos, hδ⟩ := Zc_patch_lower ha_half ha_one hc₃ hcompat Hzfr
  have hδlog27pos : 0 < δ * Real.log 2 ^ 7 := mul_pos hδpos hlog27pos
  -- the overall constant `C`
  set C : ℝ := max (1 / c) (max (4 / (δ * Real.log 2 ^ 7)) (4 / Real.log 2 ^ 7)) with hCdef
  have hCge1 : 1 / c ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCge2 : 4 / (δ * Real.log 2 ^ 7) ≤ C := by
    rw [hCdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCge3 : 4 / Real.log 2 ^ 7 ≤ C := by
    rw [hCdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨c₄, hc₄pos, C, lt_of_lt_of_le (one_div_pos.mpr hc) hCge1, ?_⟩
  intro σ t hσwin hs_ne
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hsdef
  set L : ℝ := Real.log (|t| + 2) with hLdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hL2 : Real.log 2 ≤ L := by
    rw [hLdef]; exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hLpos : 0 < L := lt_of_lt_of_le hlog2pos hL2
  have hL7pos : 0 < L ^ 7 := pow_pos hLpos 7
  have hL27 : Real.log 2 ^ 7 ≤ L ^ 7 := pow_le_pow_left₀ hlog2pos.le hL2 7
  by_cases ht2 : 2 ≤ |t|
  · -- CASE 1 : `|t| ≥ 2`, the corollary of `zeta_lower_shallow`
    have hσ0 : 1 - c₄₀ / L ^ 9 ≤ σ := by
      have hmono : c₄ / L ^ 9 ≤ c₄₀ / L ^ 9 := by
        rw [div_le_div_iff₀ (pow_pos hLpos 9) (pow_pos hLpos 9)]
        exact mul_le_mul_of_nonneg_right hc₄_le0 (pow_pos hLpos 9).le
      linarith [hσwin, hmono]
    have hlow := Hlow σ t ht2 hσ0
    rw [← hsdef, ← hLdef] at hlow
    have hinv : ‖(riemannZeta s)⁻¹‖ ≤ L ^ 7 / c := by
      rw [norm_inv, ← one_div, show L ^ 7 / c = 1 / (c / L ^ 7) by rw [one_div_div]]
      exact one_div_le_one_div_of_le (div_pos hc hL7pos) hlow
    calc ‖(riemannZeta s)⁻¹‖ ≤ L ^ 7 / c := hinv
      _ = 1 / c * L ^ 7 := by ring
      _ ≤ C * L ^ 7 := mul_le_mul_of_nonneg_right hCge1 hL7pos.le
  · rw [not_le] at ht2
    by_cases hσ3 : σ ≤ 3
    · -- CASE 2 : `|t| < 2, σ ≤ 3`, the compact pole-patch
      have haσ : a ≤ σ := by
        rw [hadef]
        have hmono : c₄ / L ^ 9 ≤ c₄ / Real.log 2 ^ 9 :=
          div_le_div_of_nonneg_left hc₄pos.le hlog29pos (pow_le_pow_left₀ hlog2pos.le hL2 9)
        linarith [hσwin, hmono]
      have hδs : δ ≤ ‖Zc s‖ := hδ s (hsre ▸ haσ) (hsre ▸ hσ3) (by rw [hsim]; linarith [ht2])
      have hs1_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne
      have hs1norm : ‖s - 1‖ ≤ 4 := by
        have hre : (s - 1).re = σ - 1 := by simp [hsdef]
        have him : (s - 1).im = t := by simp [hsdef]
        have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
        rw [hre, him] at h
        have hab1 : |σ - 1| ≤ 2 := by
          rw [abs_le]; exact ⟨by linarith [ha_half, haσ], by linarith [hσ3]⟩
        linarith [h, hab1, ht2]
      have hZcs : Zc s = (s - 1) * riemannZeta s := Zc_eq_of_ne hs_ne
      have hZcs_ne : Zc s ≠ 0 := by rw [← norm_pos_iff]; linarith [hδs, hδpos]
      have hζs_ne : riemannZeta s ≠ 0 := by intro h0; apply hZcs_ne; rw [hZcs, h0, mul_zero]
      have hζlb : δ / 4 ≤ ‖riemannZeta s‖ := by
        have h1 : ‖Zc s‖ = ‖s - 1‖ * ‖riemannZeta s‖ := by rw [hZcs, norm_mul]
        have h2 : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 4 * ‖riemannZeta s‖ :=
          mul_le_mul_of_nonneg_right hs1norm (norm_nonneg _)
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
        linarith [hδs, h1, h2]
      have hinv : ‖(riemannZeta s)⁻¹‖ ≤ 4 / δ := by
        rw [norm_inv, ← one_div, show (4 : ℝ) / δ = 1 / (δ / 4) by rw [one_div_div]]
        exact one_div_le_one_div_of_le (div_pos hδpos (by norm_num)) hζlb
      have hstep : 4 / δ ≤ 4 / (δ * Real.log 2 ^ 7) * L ^ 7 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hδpos hδlog27pos]
        nlinarith [mul_le_mul_of_nonneg_left hL27 hδpos.le]
      calc ‖(riemannZeta s)⁻¹‖ ≤ 4 / δ := hinv
        _ ≤ 4 / (δ * Real.log 2 ^ 7) * L ^ 7 := hstep
        _ ≤ C * L ^ 7 := mul_le_mul_of_nonneg_right hCge2 hL7pos.le
    · -- CASE 3 : `|t| < 2, σ > 3`, the deep tail
      rw [not_le] at hσ3
      have hsre2 : (2 : ℝ) ≤ s.re := by rw [hsre]; linarith [hσ3]
      have hζge : (1 : ℝ) / 4 ≤ ‖riemannZeta s‖ := zeta_norm_ge hsre2
      have hinv : ‖(riemannZeta s)⁻¹‖ ≤ 4 := by
        rw [norm_inv, show (4 : ℝ) = 1 / (1 / 4) by norm_num, ← one_div (‖riemannZeta s‖)]
        exact one_div_le_one_div_of_le (by norm_num) hζge
      have hstep : (4 : ℝ) ≤ 4 / Real.log 2 ^ 7 * L ^ 7 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog27pos]
        nlinarith [hL27, hlog27pos]
      calc ‖(riemannZeta s)⁻¹‖ ≤ 4 := hinv
        _ ≤ 4 / Real.log 2 ^ 7 * L ^ 7 := hstep
        _ ≤ C * L ^ 7 := mul_le_mul_of_nonneg_right hCge3 hL7pos.le

end Salt.SW
