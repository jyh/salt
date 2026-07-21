/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ParsevalAsm
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# S8 MR-CORE, node A3a-R4e — the zone arithmetic collapsing the summed Perron error

Source pin: **MR arXiv v4** (`docs/sources/1501.04585v4.pdf`), §7, pp. 21–23.

This file collapses the RHS of `Salt.MR.perron_sum_error_bound`
(`ParsevalAsm.lean`) — the per-term `min`-device sum
`∑ₘ ‖aₘ‖·2·(x/m)ᶜ·min(π+2·log(1+T/c), 1/(T·|log(x/m)|))` — to an explicit
`(x/T)·(log T + log X)`-grade bound, on the MR range `m ∈ [X,4X]`, `x ∈ [X,2X]`,
`c = 1`, `‖aₘ‖ ≤ 1`.

## The R4e ladder

* **R1 — `log_ratio_ge`**: the log–ratio lower bound `|r−1|/max 1 r ≤ |log r|`
  (from `Real.log_le_sub_one_of_pos` on `r` and on `1/r`), plus the MR-range
  corollary `log_ratio_ge_dist`: `|x−m|/(4X) ≤ |log(x/m)|`.
* **R2 — `harmonic_zone_bound`**: the Finset harmonic estimate
  `∑_{k=K}^{N} 1/k ≤ 1 + log(N/K)` (mathlib `harmonic_le_one_add_log` and
  `log_add_one_le_harmonic`).
* **R3 — `zone_count`**: `#{m : a ≤ m ≤ b} ≤ b − a + 1` (via `Nat.card_Icc`),
  with the crossover corollary `#{m : |x−m| ≤ r} ≤ 2r + 1`.
* **R4 — `perron_sum_error_collapsed`**: the assembly — the near band
  (`|x−m| < 1`, the `BIG` branch, `≤ 3` integers) plus the far shells
  (`⌊|x−m|⌋ = k`, the decay branch, reindexed to R2).

The near/far split is taken at radius `1` (not `δ = 1/T`): the grade
`(x/T)·(log T + log X)` is unchanged (the design's `δ`-balance only tunes the
constant), and the fixed radius keeps the counting integer-clean.  Constants are
generous absolutes; the exact arithmetic is recorded in the node NOTES.
-/

namespace Salt.MR

open Finset Complex

/-! ## R1 — the log–ratio lower bound. -/

/-- **R1 `log_ratio_ge`** — the elementary log–ratio lower bound: for `r > 0`,
`|r − 1| / max 1 r ≤ |log r|`.  Both cases reduce to `log x ≤ x − 1`
(`Real.log_le_sub_one_of_pos`): the `r ≥ 1` branch applies it to `1/r`, the
`r < 1` branch to `r` directly. -/
theorem log_ratio_ge {r : ℝ} (hr : 0 < r) : |r - 1| / max 1 r ≤ |Real.log r| := by
  by_cases h1 : 1 ≤ r
  · rw [max_eq_right h1, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r - 1),
      abs_of_nonneg (Real.log_nonneg h1), div_le_iff₀ (by linarith : (0 : ℝ) < r)]
    have hinv := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / r by positivity)
    rw [Real.log_div one_ne_zero hr.ne', Real.log_one, zero_sub] at hinv
    have hrr : (1 / r) * r = 1 := by field_simp
    nlinarith [hinv, hrr, hr]
  · have hlt : r < 1 := not_le.mp h1
    rw [max_eq_left hlt.le, abs_of_nonpos (by linarith : r - 1 ≤ 0),
      abs_of_nonpos (Real.log_nonpos hr.le hlt.le), div_one]
    have := Real.log_le_sub_one_of_pos hr
    linarith

/-- **R1 corollary `log_ratio_ge_dist`** — the MR-range decay lower bound: for
`0 < X`, `0 < m ≤ 4X`, `0 < x ≤ 4X`,
`|x − m| / (4X) ≤ |log(x/m)|`.  From `log_ratio_ge` at `r = x/m` after
`max 1 (x/m) ≤ 4X/m` and `|x/m − 1| = |x − m|/m`. -/
theorem log_ratio_ge_dist {X x m : ℝ} (hX : 0 < X) (hm : 0 < m)
    (hmX : m ≤ 4 * X) (hx : 0 < x) (hxX : x ≤ 4 * X) :
    |x - m| / (4 * X) ≤ |Real.log (x / m)| := by
  have hxm : (0 : ℝ) < x / m := div_pos hx hm
  have hmax : max 1 (x / m) ≤ 4 * X / m := by
    refine max_le ?_ ?_
    · rw [le_div_iff₀ hm]; linarith
    · rw [div_le_div_iff₀ hm hm]; nlinarith
  have hR1 := log_ratio_ge hxm
  have hpos : (0 : ℝ) < max 1 (x / m) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hstep : |x / m - 1| / (4 * X / m) ≤ |x / m - 1| / max 1 (x / m) := by
    apply div_le_div_of_nonneg_left (abs_nonneg _) hpos hmax
  have heq : |x / m - 1| / (4 * X / m) = |x - m| / (4 * X) := by
    rw [show x / m - 1 = (x - m) / m by field_simp, abs_div, abs_of_pos hm]
    field_simp
  rw [heq] at hstep
  exact hstep.trans hR1

/-! ## R2 — the Finset harmonic estimate. -/

/-- **R2 `harmonic_zone_bound`** — the tail harmonic sum bound: for `1 ≤ K ≤ N`,
`∑_{k=K}^{N} 1/k ≤ 1 + log(N/K)`.  From `harmonic_le_one_add_log` (the head bound
`∑_{k=1}^{N} ≤ 1 + log N`) and `log_add_one_le_harmonic` (the prefix lower bound
`log K ≤ ∑_{k=1}^{K−1}`), split at `K` by a disjoint `Icc` union. -/
theorem harmonic_zone_bound {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) :
    ∑ k ∈ Finset.Icc K N, ((k : ℝ))⁻¹ ≤ 1 + Real.log ((N : ℝ) / (K : ℝ)) := by
  have hupper : ∑ k ∈ Finset.Icc 1 N, ((k : ℝ))⁻¹ ≤ 1 + Real.log (N : ℝ) := by
    have h := harmonic_le_one_add_log N
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using h
  have hlower : Real.log (K : ℝ) ≤ ∑ k ∈ Finset.Icc 1 (K - 1), ((k : ℝ))⁻¹ := by
    have h := log_add_one_le_harmonic (K - 1)
    rw [Nat.sub_add_cancel hK] at h
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using h
  have hunion : Finset.Icc 1 (K - 1) ∪ Finset.Icc K N = Finset.Icc 1 N := by
    ext a; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 (K - 1)) (Finset.Icc K N) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  have hsplit : ∑ k ∈ Finset.Icc 1 N, ((k : ℝ))⁻¹
      = ∑ k ∈ Finset.Icc 1 (K - 1), ((k : ℝ))⁻¹
        + ∑ k ∈ Finset.Icc K N, ((k : ℝ))⁻¹ := by
    rw [← Finset.sum_union hdisj, hunion]
  have hlogdiv : Real.log ((N : ℝ) / (K : ℝ)) = Real.log (N : ℝ) - Real.log (K : ℝ) :=
    Real.log_div (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
  rw [hlogdiv]
  linarith [hupper, hlower, hsplit]

/-! ## R3 — the zone integer count. -/

/-- **R3 `zone_count`** — the interval integer count: the number of naturals `m ∈ S`
with `a ≤ m ≤ b` is `≤ b − a + 1`.  The filtered set embeds in
`Finset.Icc ⌈a⌉₊ ⌊b⌋₊` (`Nat.card_Icc`); the cardinality `⌊b⌋₊ + 1 − ⌈a⌉₊`
is `≤ b − a + 1` by
`Nat.floor_le`/`Nat.le_ceil`. -/
theorem zone_count (S : Finset ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((S.filter (fun m : ℕ => a ≤ (m : ℝ) ∧ (m : ℝ) ≤ b)).card : ℝ) ≤ b - a + 1 := by
  have hb : 0 ≤ b := ha.trans hab
  have hsub : S.filter (fun m : ℕ => a ≤ (m : ℝ) ∧ (m : ℝ) ≤ b)
      ⊆ Finset.Icc ⌈a⌉₊ ⌊b⌋₊ := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr hm.2.1, Nat.le_floor hm.2.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hle : ⌈a⌉₊ ≤ ⌊b⌋₊ + 1 :=
    (Nat.ceil_mono hab).trans (Nat.ceil_le_floor_add_one b)
  have hcast : ((⌊b⌋₊ + 1 - ⌈a⌉₊ : ℕ) : ℝ)
      = (⌊b⌋₊ : ℝ) + 1 - (⌈a⌉₊ : ℝ) := by
    rw [Nat.cast_sub hle]; push_cast; ring
  have key : ((S.filter (fun m : ℕ => a ≤ (m : ℝ) ∧ (m : ℝ) ≤ b)).card : ℝ)
      ≤ ((⌊b⌋₊ + 1 - ⌈a⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcard
  rw [hcast] at key
  have h1 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le hb
  have h2 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
  linarith

/-- **R3 corollary `zone_count_crossover`** — the crossover-band count: for `0 ≤ r ≤ x`,
`#{m ∈ S : |x − m| ≤ r} ≤ 2r + 1`.  The direct `δ`-balance form (`δ = 1/T`,
`r = δx`). -/
theorem zone_count_crossover (S : Finset ℕ) {x r : ℝ} (hr : 0 ≤ r) (hrx : r ≤ x) :
    ((S.filter (fun m : ℕ => |x - (m : ℝ)| ≤ r)).card : ℝ) ≤ 2 * r + 1 := by
  have hfe : S.filter (fun m : ℕ => |x - (m : ℝ)| ≤ r)
      = S.filter (fun m : ℕ => x - r ≤ (m : ℝ) ∧ (m : ℝ) ≤ x + r) := by
    apply Finset.filter_congr
    intro m _
    rw [abs_le]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  rw [hfe]
  have h := zone_count S (by linarith : (0 : ℝ) ≤ x - r) (by linarith : x - r ≤ x + r)
  linarith [h]

/-! ## R4 — the assembly. -/

/-- **Harmonic image reindex** — if `g` is injective on `F` with `1 ≤ g m ≤ N`, then
`∑_{m ∈ F} 1/(g m) ≤ 1 + log N` (push the sum through `g`'s image into `[1,N]`,
then R2). -/
theorem sum_inv_image_le {F : Finset ℕ} {N : ℕ} (hN : 1 ≤ N) (g : ℕ → ℕ)
    (hginj : ∀ a ∈ F, ∀ b ∈ F, g a = g b → a = b)
    (hg1 : ∀ m ∈ F, 1 ≤ g m) (hgN : ∀ m ∈ F, g m ≤ N) :
    ∑ m ∈ F, 1 / ((g m : ℕ) : ℝ) ≤ 1 + Real.log (N : ℝ) := by
  have himg : ∑ j ∈ F.image g, 1 / (j : ℝ) = ∑ m ∈ F, 1 / ((g m : ℕ) : ℝ) :=
    Finset.sum_image hginj
  rw [← himg]
  have hsub : F.image g ⊆ Finset.Icc 1 N := by
    intro j hj; rw [Finset.mem_image] at hj; obtain ⟨m, hm, rfl⟩ := hj
    rw [Finset.mem_Icc]; exact ⟨hg1 m hm, hgN m hm⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)) ?_
  have hz := harmonic_zone_bound (le_refl 1) hN
  simp only [Nat.cast_one, div_one, one_div] at hz ⊢
  exact hz

/-- **Termwise decay bound** — for the MR range and any `0 < D ≤ |x − m|`, the decay
branch is `≤ (4X/T)/D`.  From `log_ratio_ge_dist` (`|x−m|/(4X) ≤ |log(x/m)|`). -/
theorem decay_le_of_dist {X x T m D : ℝ} (hX : 0 < X) (hT : 0 < T) (hm : 0 < m)
    (hmX : m ≤ 4 * X) (hx : 0 < x) (hxX : x ≤ 4 * X) (hD : 0 < D) (hDdist : D ≤ |x - m|) :
    1 / (T * |Real.log (x / m)|) ≤ (4 * X / T) / D := by
  have hlog := log_ratio_ge_dist hX hm hmX hx hxX
  have hchain : D / (4 * X) ≤ |Real.log (x / m)| := by
    refine le_trans ?_ hlog; gcongr
  have hDpos4 : (0 : ℝ) < D / (4 * X) := by positivity
  have hstep : 1 / (T * |Real.log (x / m)|) ≤ 1 / (T * (D / (4 * X))) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left hchain hT.le
  have heq : 1 / (T * (D / (4 * X))) = (4 * X / T) / D := by
    field_simp
  rwa [heq] at hstep

/-- **One far side** — `F` is a far-zone piece with an injective reindex `g` into
`[1,N]` and a termwise bound `min ≤ (4X/T)/(g m)`; then
`∑_{m ∈ F} min ≤ (4X/T)(1 + log N)`. -/
theorem far_side_bound {x X T : ℝ} (hX : 0 < X) (hT : 0 < T)
    (F : Finset ℕ) {N : ℕ} (hN : 1 ≤ N) (g : ℕ → ℕ)
    (hginj : ∀ a ∈ F, ∀ b ∈ F, g a = g b → a = b)
    (hg1 : ∀ m ∈ F, 1 ≤ g m) (hgN : ∀ m ∈ F, g m ≤ N)
    (hterm : ∀ m ∈ F, min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
        ≤ (4 * X / T) / ((g m : ℝ))) :
    ∑ m ∈ F, min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
      ≤ (4 * X / T) * (1 + Real.log (N : ℝ)) := by
  have h1 := Finset.sum_le_sum hterm
  have h2 : ∑ m ∈ F, (4 * X / T) / ((g m : ℝ))
      = (4 * X / T) * ∑ m ∈ F, 1 / ((g m : ℝ)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by rw [mul_one_div])
  have h3 := sum_inv_image_le hN g hginj hg1 hgN
  have h4 : (0 : ℝ) ≤ 4 * X / T := div_nonneg (by linarith) hT.le
  calc ∑ m ∈ F, min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
      ≤ (4 * X / T) * ∑ m ∈ F, 1 / ((g m : ℝ)) := h2 ▸ h1
    _ ≤ (4 * X / T) * (1 + Real.log (N : ℝ)) := mul_le_mul_of_nonneg_left h3 h4

/-- **The `min`-sum bound** — the heart of R4e: on the MR range the summed
`min`-device collapses to `3·BIG + (8X/T)(1 + log⌊3X⌋)`.  Near band `|x−m| < 1`
(`≤ 3` integers, the `BIG` branch) plus the two far sides (`m ≥ x+1`, `m ≤ x−1`),
each reindexed injectively into `[1, ⌊3X⌋]` and closed by `far_side_bound`. -/
theorem zone_min_sum_le (s0 : Finset ℕ) {X x T : ℝ}
    (hX : 1 ≤ X) (hT : 0 < T) (hx : X ≤ x) (hx2 : x ≤ 2 * X)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X) :
    ∑ m ∈ s0, min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
      ≤ 3 * (Real.pi + 2 * Real.log (1 + T))
        + (8 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hBIG_nn : (0 : ℝ) ≤ Real.pi + 2 * Real.log (1 + T) := by
    have h1 := Real.pi_pos
    have h2 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + T)
    linarith
  have hN1 : 1 ≤ ⌊3 * X⌋₊ := Nat.le_floor (by push_cast; linarith)
  rw [← Finset.sum_filter_add_sum_filter_not s0 (fun m : ℕ => |x - (m : ℝ)| < 1)]
  -- Near band: the BIG branch, at most 3 integers.
  have hnear : ∑ m ∈ s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1),
        min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
      ≤ 3 * (Real.pi + 2 * Real.log (1 + T)) := by
    have hle : ∑ m ∈ s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1),
          min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
        ≤ ∑ _m ∈ s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1),
          (Real.pi + 2 * Real.log (1 + T)) :=
      Finset.sum_le_sum (fun m _ => min_le_left _ _)
    rw [Finset.sum_const, nsmul_eq_mul] at hle
    have hcard : ((s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1)).card : ℝ) ≤ 3 := by
      have hsub : s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1)
          ⊆ s0.filter (fun m : ℕ => |x - (m : ℝ)| ≤ 1) := by
        intro m hm; rw [Finset.mem_filter] at hm ⊢; exact ⟨hm.1, le_of_lt hm.2⟩
      have h1 : ((s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1)).card : ℝ)
          ≤ ((s0.filter (fun m : ℕ => |x - (m : ℝ)| ≤ 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have h2 := zone_count_crossover s0 (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (1 : ℝ) ≤ x)
      linarith
    calc ∑ m ∈ s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1),
          min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
        ≤ ((s0.filter (fun m : ℕ => |x - (m : ℝ)| < 1)).card : ℝ)
            * (Real.pi + 2 * Real.log (1 + T)) := hle
      _ ≤ 3 * (Real.pi + 2 * Real.log (1 + T)) := mul_le_mul_of_nonneg_right hcard hBIG_nn
  -- Far band: split at m ≥ x+1 vs m ≤ x−1, each an injective harmonic reindex.
  have hfar : ∑ m ∈ s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1),
        min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
      ≤ (8 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not
        (s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1)) (fun m : ℕ => x + 1 ≤ (m : ℝ))]
    have hfpos : ∑ m ∈ (s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1)).filter
          (fun m : ℕ => x + 1 ≤ (m : ℝ)),
          min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
        ≤ (4 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by
      refine far_side_bound hX0 hT _ hN1 (fun m => m - ⌈x⌉₊) ?_ ?_ ?_ ?_
      · intro a ha b hb hab
        simp only [Finset.mem_filter] at ha hb
        have hca : ⌈x⌉₊ < a := by
          have := Nat.ceil_lt_add_one hx0.le
          have h' : (↑⌈x⌉₊ : ℝ) < ↑a := by linarith [ha.2]
          exact_mod_cast h'
        have hcb : ⌈x⌉₊ < b := by
          have := Nat.ceil_lt_add_one hx0.le
          have h' : (↑⌈x⌉₊ : ℝ) < ↑b := by linarith [hb.2]
          exact_mod_cast h'
        omega
      · intro m hm
        simp only [Finset.mem_filter] at hm
        have := Nat.ceil_lt_add_one hx0.le
        have h' : (↑⌈x⌉₊ : ℝ) < ↑m := by linarith [hm.2]
        have : ⌈x⌉₊ < m := by exact_mod_cast h'
        omega
      · intro m hm
        simp only [Finset.mem_filter] at hm
        obtain ⟨hmlo, hmhi⟩ := hrange m hm.1.1
        have hc := Nat.ceil_lt_add_one hx0.le
        have hcm : ⌈x⌉₊ < m := by
          have h' : (↑⌈x⌉₊ : ℝ) < ↑m := by linarith [hm.2]
          exact_mod_cast h'
        have hcast : ((m - ⌈x⌉₊ : ℕ) : ℝ) ≤ 3 * X := by
          rw [Nat.cast_sub hcm.le]
          have := Nat.le_ceil x
          linarith
        exact Nat.le_floor hcast
      · intro m hm
        simp only [Finset.mem_filter] at hm
        obtain ⟨hmlo, hmhi⟩ := hrange m hm.1.1
        have hm0 : (0 : ℝ) < m := by linarith
        have hcm : ⌈x⌉₊ < m := by
          have := Nat.ceil_lt_add_one hx0.le
          have h' : (↑⌈x⌉₊ : ℝ) < ↑m := by linarith [hm.2]
          exact_mod_cast h'
        have hD0 : (0 : ℝ) < ((m - ⌈x⌉₊ : ℕ) : ℝ) := by
          have : 0 < m - ⌈x⌉₊ := by omega
          exact_mod_cast this
        have hDdist : ((m - ⌈x⌉₊ : ℕ) : ℝ) ≤ |x - (m : ℝ)| := by
          rw [Nat.cast_sub hcm.le, abs_sub_comm, abs_of_nonneg (by linarith [hm.2])]
          have := Nat.le_ceil x
          linarith
        exact (min_le_right _ _).trans
          (decay_le_of_dist hX0 hT hm0 hmhi hx0 (by linarith) hD0 hDdist)
    have hfneg : ∑ m ∈ (s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1)).filter
          (fun m : ℕ => ¬ (x + 1 ≤ (m : ℝ))),
          min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
        ≤ (4 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by
      have hle1 : ∀ m ∈ (s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1)).filter
          (fun m : ℕ => ¬ (x + 1 ≤ (m : ℝ))), (m : ℝ) ≤ x - 1 := by
        intro m hm
        simp only [Finset.mem_filter] at hm
        have hlt : (m : ℝ) < x + 1 := not_le.mp hm.2
        have hge : (1 : ℝ) ≤ |x - (m : ℝ)| := not_lt.mp hm.1.2
        have hxm1 : (1 : ℝ) ≤ x - (m : ℝ) := by
          by_contra hc
          have hlt2 : x - (m : ℝ) < 1 := not_le.mp hc
          have : |x - (m : ℝ)| < 1 := abs_lt.mpr ⟨by linarith, hlt2⟩
          linarith
        linarith
      refine far_side_bound hX0 hT _ hN1 (fun m => ⌊x⌋₊ - m) ?_ ?_ ?_ ?_
      · intro a ha b hb hab
        have hma : (a : ℝ) ≤ x - 1 := hle1 a ha
        have hmb : (b : ℝ) ≤ x - 1 := hle1 b hb
        have ha' : a + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
        have hb' : b + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
        omega
      · intro m hm
        have hmx : (m : ℝ) ≤ x - 1 := hle1 m hm
        have hm' : m + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
        omega
      · intro m hm
        have hmx : (m : ℝ) ≤ x - 1 := hle1 m hm
        simp only [Finset.mem_filter] at hm
        obtain ⟨hmlo, hmhi⟩ := hrange m hm.1.1
        have hm' : m + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
        have hcast : ((⌊x⌋₊ - m : ℕ) : ℝ) ≤ 3 * X := by
          rw [Nat.cast_sub (by omega)]
          have := Nat.floor_le hx0.le
          linarith
        exact Nat.le_floor hcast
      · intro m hm
        have hmx : (m : ℝ) ≤ x - 1 := hle1 m hm
        simp only [Finset.mem_filter] at hm
        obtain ⟨hmlo, hmhi⟩ := hrange m hm.1.1
        have hm0 : (0 : ℝ) < m := by linarith
        have hm' : m + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
        have hD0 : (0 : ℝ) < ((⌊x⌋₊ - m : ℕ) : ℝ) := by
          have : 0 < ⌊x⌋₊ - m := by omega
          exact_mod_cast this
        have hDdist : ((⌊x⌋₊ - m : ℕ) : ℝ) ≤ |x - (m : ℝ)| := by
          rw [Nat.cast_sub (by omega), abs_of_nonneg (by linarith)]
          have := Nat.floor_le hx0.le
          linarith
        exact (min_le_right _ _).trans
          (decay_le_of_dist hX0 hT hm0 hmhi hx0 (by linarith) hD0 hDdist)
    have heq8 : (8 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ))
        = (4 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ))
          + (4 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by ring
    linarith [hfpos, hfneg, heq8]
  linarith [hnear, hfar]

/-- **R4 `zone_sum_collapsed`** — the collapse of `perron_sum_error_bound`'s RHS
(at `c = 1`, `‖aₘ‖ ≤ 1`, MR range): the `min`-device sum is
`≤ 12·(π + 2·log(1+T)) + (32X/T)·(1 + log(3X))`, the explicit
`(x/T)·(log T + log X)`-grade bound.  Each summand `≤ 4·min` (since `‖aₘ‖ ≤ 1`,
`x/m ≤ 2`); then `zone_min_sum_le`, and `log⌊3X⌋ ≤ log(3X)`. -/
theorem zone_sum_collapsed (a : ℕ → ℂ) (s0 : Finset ℕ) {X x T : ℝ}
    (hX : 1 ≤ X) (hT : 0 < T) (hx : X ≤ x) (hx2 : x ≤ 2 * X)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X) :
    ∑ m ∈ s0, ‖a m‖ * (2 * (x / m)
        * min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|)))
      ≤ 12 * (Real.pi + 2 * Real.log (1 + T))
        + (32 * X / T) * (1 + Real.log (3 * X)) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hBIG_nn : (0 : ℝ) ≤ Real.pi + 2 * Real.log (1 + T) := by
    have h1 := Real.pi_pos
    have h2 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + T)
    linarith
  have hstepA : ∑ m ∈ s0, ‖a m‖ * (2 * (x / m)
        * min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|)))
      ≤ 4 * ∑ m ∈ s0,
          min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    obtain ⟨hmlo, hmhi⟩ := hrange m hm
    have hm0 : (0 : ℝ) < m := by linarith
    set M := min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|)) with hMdef
    have hMnn : (0 : ℝ) ≤ M := by rw [hMdef]; exact le_min hBIG_nn (by positivity)
    have hxm2 : x / m ≤ 2 := by rw [div_le_iff₀ hm0]; linarith
    calc ‖a m‖ * (2 * (x / m) * M)
        ≤ 1 * (4 * M) := by
          refine mul_le_mul (ha m hm) ?_ ?_ zero_le_one
          · nlinarith [hxm2, hMnn]
          · exact mul_nonneg (by positivity) hMnn
      _ = 4 * M := one_mul _
  have hstepB := zone_min_sum_le s0 hX hT hx hx2 hrange
  have hlogfloor : Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ) ≤ Real.log (3 * X) := by
    have hfp : 1 ≤ ⌊3 * X⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊3 * X⌋₊))
      (Nat.floor_le (by linarith))
  calc ∑ m ∈ s0, ‖a m‖ * (2 * (x / m)
          * min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|)))
      ≤ 4 * ∑ m ∈ s0,
          min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|)) := hstepA
    _ ≤ 4 * (3 * (Real.pi + 2 * Real.log (1 + T))
          + (8 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hstepB (by norm_num)
    _ = 12 * (Real.pi + 2 * Real.log (1 + T))
          + (32 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by ring
    _ ≤ 12 * (Real.pi + 2 * Real.log (1 + T))
          + (32 * X / T) * (1 + Real.log (3 * X)) := by
        have h32 : (0 : ℝ) ≤ 32 * X / T := by positivity
        have hmul := mul_le_mul_of_nonneg_left
          (by linarith [hlogfloor] :
            (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) ≤ 1 + Real.log (3 * X)) h32
        linarith [hmul]

/-- **R4 `perron_sum_error_collapsed`** — the end-to-end statement: the truncated
Perron summed error over the MR range (`c = 1`, `‖aₘ‖ ≤ 1`) is bounded by the
explicit `(x/T)·(log T + log X)`-grade constant.  Chains
`perron_sum_error_bound` (the per-term `min`-device, at `c = 1`) with
`zone_sum_collapsed` (the zone arithmetic), after `rpow_one`/`div_one` normalise
the `c = 1` shape. -/
theorem perron_sum_error_collapsed (a : ℕ → ℂ) (s0 : Finset ℕ) {X x T : ℝ}
    (hX : 1 ≤ X) (hT : 0 < T) (hx : X ≤ x) (hx2 : x ≤ 2 * X)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hne : ∀ m ∈ s0, (m : ℝ) ≠ x) :
    ‖∑ m ∈ s0, a m * (perronContour (x / m) 1 T
        - 2 * (Real.pi : ℂ) * I * (if 1 < x / m then (1 : ℂ) else 0))‖
      ≤ 12 * (Real.pi + 2 * Real.log (1 + T))
        + (32 * X / T) * (1 + Real.log (3 * X)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hpos : ∀ m ∈ s0, 0 < m := by
    intro m hm
    obtain ⟨hmlo, _⟩ := hrange m hm
    exact_mod_cast (by linarith : (0 : ℝ) < m)
  have hbound := perron_sum_error_bound a s0 hx0 (by norm_num : (0 : ℝ) < 1) hT hpos hne
  refine hbound.trans ?_
  have hrw : ∑ m ∈ s0, ‖a m‖ * (2 * (x / m) ^ (1 : ℝ)
        * min (Real.pi + 2 * Real.log (1 + T / 1)) (1 / (T * |Real.log (x / m)|)))
      = ∑ m ∈ s0, ‖a m‖ * (2 * (x / m)
        * min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Real.rpow_one, div_one]
  rw [hrw]
  exact zone_sum_collapsed a s0 hX hT hx hx2 ha hrange

end Salt.MR
