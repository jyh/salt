/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.WindowSW
import Salt.Chen.WindowBVDescent
import Salt.Chen.BlockPricing

/-!
# WBV4 — the catch-#54 assembly (the window BV close)

Design: `docs/blueprints/flags.md`, the `2026-07-13 C54-RECON … FROZEN` freeze (route (i),
"the one-sided cutoff carrier"; items 7 + 9 of the frozen 9-item list) and the
`2026-07-14 WBV1`/`WBV2`/`WBV3` entries.  This is the wave's close: the top-level
windowed bilinear-BV `L¹`-over-`d` bound (`general_BV_cutoff_final`, item 7) combining
WBV3's small-conductor side (`smallconductor_window_sum`) with WBV2's large-conductor
descent (`dyadic_energy_le_cutoff`), and the feed into `BlockPricing`'s existing `hHD`
slot (`hHD_of_generalBV_window`, item 9).

## The imprimitive-fold finding (route-(i) re-verification — item 7)

The recon FROZE route (i) with "the windowed orthogonality is EXACT, no imprimitivity
error".  This is TRUE of `apDiscBilinCutoff_orthogonality` (an exact identity) but the
recon's optimism about the *imprimitive-to-primitive fold* needs honest correction:

* **The fold IS mechanical.**  `cutoffTwist_coprimeRestrict_primitive` (below) is the
  exact analogue of `bilinTwist_coprimeRestrict_primitive`: because a Dirichlet character
  is multiplicative (`Salt.LS.chi_cast_mul`), `χ(mn) = χ(m)·χ(n)`, so the windowed twist
  folds *factor-by-factor* into the primitive twist of the coprime-restricted
  coefficients `coprimeRestrict α d`, `coprimeRestrict β d`.  **No error at the fold** —
  a ~30-line mirror, landed here.

* **The α-side coprimality ERROR re-appears.**  The folded coefficient `coprimeRestrict α d`
  depends on `d` (not just on the conductor `f`), so — exactly as in the landed FACTORED
  `Salt.Chen.bilinear_hLargeDisc` — the conductor regroup (`regroup_cutoff`) followed by
  the φ-swap (`swapPhi_generic`, reused verbatim) applies only to a *fixed-coefficient*
  reference (the FULL-`α` primitive twist).  The per-`χ` triangle split therefore leaves a
  genuine `α`-side coprimality error `‖cutoffTwist d χ − cutoffTwist (conductor) (primitive)‖`.
  It is the SINGLE-norm (window does not factor) analogue of `bilinear_hLargeDisc`'s
  `hErrSum`; there is NO second (β-side) error because `blockPrimeInd N` is already
  coprime-supported (`coprimeRestrict_blockPrimeInd`, `d < N`), but the α-side one is real.

So the honest window close mirrors `general_BV_weak` + `bilinear_hLargeDisc`: the
small-conductor side is COMPLETE (`smallconductor_window_sum`, no per-`d` slot); the
large-conductor side carries the fixed-`α` main energy `hMainEnergy` (discharged
DOWNSTREAM by `dyadic_energy_le_cutoff`, whose four-term needs `hlev`/`hD0lo`/`hMlev`
but — crucially — NO `hdiv`: there is no `e`-dilation / δ-fibering on the plain window
path, so the divisor-count threshold of the α-side never enters) and the α-side error
`hErrSum` (a crude BDH/thin bound downstream).

## What this file lands

1. `cutoffTwist_coprimeRestrict_primitive` — the mechanical fold (the resolution of the
   imprimitive-fold question).  FULL.
2. `regroup_cutoff` — the single-norm conductor regroup (mirror of `regroup_bilin`).  FULL.
3. `cutoff_hLargeDisc` — the large-conductor discharge (mirror of `bilinear_hLargeDisc`):
   the per-`χ` split into the fixed-`α` primitive main (regrouped + φ-swapped onto
   `∑_f (1/φf)·cutoffPrimEnergy`, closed by `hMainEnergy`) and the α-side error `hErrSum`.
   FULL.
4. `general_BV_cutoff_final` (item 7) — the top-level windowed `L¹`-over-`d` bound,
   `smallconductor_window_sum` (small) + `norm_apDiscBilinCutoff_le` ∘ `cutoff_hLargeDisc`
   (large).  FULL.
5. `hHD_of_generalBV_window` (item 9) + the composition `#check` block (item 3).

Only `[propext, Classical.choice, Quot.sound]` are used.
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## 1. The imprimitive fold for the windowed twist -/

open Classical in
/-- **The windowed imprimitive fold — FULL (mirror of `bilinTwist_coprimeRestrict_primitive`).**
The imprimitive windowed twist mod `d` by `χ` equals the *primitive* windowed twist of the
coprime-restricted coefficients `coprimeRestrict α d`, `coprimeRestrict β d` by
`χ⋆ = χ.primitiveCharacter` at the conductor `f = χ.conductor`.  Because `χ` is
multiplicative (`Salt.LS.chi_cast_mul`), `χ(mn) = χ(m)·χ(n)`, so the fold is factor-by-factor:
off the units mod `d` both `χ` and the coprime restriction vanish; on the units `χ⋆ = χ`
(`primitiveCharacter_apply_of_isUnit`).  **No error is created** — the cutoff `m·n ≤ T`
rides through untouched (it does not depend on the modulus). -/
lemma cutoffTwist_coprimeRestrict_primitive {d : ℕ} [NeZero d] (α β : ℕ → ℂ) (X Y T : ℕ)
    (χ : DirichletCharacter ℂ d) :
    cutoffTwist α β X Y T d χ
      = cutoffTwist (coprimeRestrict α d) (coprimeRestrict β d) X Y T χ.conductor
          χ.primitiveCharacter := by
  classical
  unfold cutoffTwist coprimeRestrict
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Salt.LS.chi_cast_mul χ m n, Salt.LS.chi_cast_mul χ.primitiveCharacter m n]
  by_cases hm : IsUnit ((m : ℕ) : ZMod d)
  · by_cases hn : IsUnit ((n : ℕ) : ZMod d)
    · rw [if_pos hm, if_pos hn,
        Salt.LS.primitiveCharacter_apply_of_isUnit χ hm,
        Salt.LS.primitiveCharacter_apply_of_isUnit χ hn]
    · rw [if_neg hn, MulChar.map_nonunit χ hn]; ring
  · rw [if_neg hm, MulChar.map_nonunit χ hm]; ring

/-! ## 2. The single-norm conductor regroup (mirror of `regroup_bilin`) -/

open Classical in
/-- **The windowed conductor regroup — FULL (single-norm mirror of `regroup_bilin`).**  Summing
the primitive windowed energy `‖cutoffTwist … (conductor χ) (primitive χ)‖` over the
non-principal characters mod `q` is bounded by summing `cutoffPrimEnergy` over the divisors
`f ∣ q`, `f ∈ [2, Q]`.  The map `χ ↦ ⟨conductor χ, χ⋆⟩` is injective (left inverse
`changeLevel`), every term is `≥ 0`, and each `f`-fiber is the full primitive-character set.
Byte-identical to `regroup_bilin` with the product norm replaced by the single windowed norm. -/
lemma regroup_cutoff {q Q : ℕ} [NeZero q] (hqQ : q ≤ Q) (α β : ℕ → ℂ) (X Y T : ℕ) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖cutoffTwist α β X Y T χ.conductor χ.primitiveCharacter‖
      ≤ ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), cutoffPrimEnergy α β X Y T f := by
  classical
  set D := (Finset.Icc 2 Q).filter (· ∣ q) with hD
  set tt : (f : ℕ) → Finset (DirichletCharacter ℂ f) :=
    fun f => Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive) with htt
  set i : DirichletCharacter ℂ q → Σ f : ℕ, DirichletCharacter ℂ f :=
    fun χ => ⟨χ.conductor, χ.primitiveCharacter⟩ with hi
  set G : (Σ f : ℕ, DirichletCharacter ℂ f) → ℝ :=
    fun p => ‖cutoffTwist α β X Y T p.1 p.2‖ with hG
  set r : (Σ f : ℕ, DirichletCharacter ℂ f) → DirichletCharacter ℂ q :=
    fun p => if h : p.1 ∣ q then DirichletCharacter.changeLevel h p.2 else 1 with hr
  set T' := D.sigma tt with hT
  have hri : ∀ χ : DirichletCharacter ℂ q, r (i χ) = χ := by
    intro χ
    simp only [hr, hi]
    rw [dif_pos χ.conductor_dvd_level]
    exact DirichletCharacter.changeLevel_primitiveCharacter (χ := χ)
  have hinj : ∀ a ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
      ∀ b ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, i a = i b → a = b := by
    intro a _ b _ hab
    have h := congrArg r hab
    rwa [hri a, hri b] at h
  have hRHS : ∑ p ∈ T', G p = ∑ f ∈ D, cutoffPrimEnergy α β X Y T f := by
    rw [hT, Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    simp only [hG, htt, cutoffPrimEnergy]
  calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          ‖cutoffTwist α β X Y T χ.conductor χ.primitiveCharacter‖
      = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, G (i χ) := by
        refine Finset.sum_congr rfl (fun χ _ => ?_); simp only [hG, hi]
    _ = ∑ p ∈ (Finset.univ.erase 1).image i, G p := (Finset.sum_image hinj).symm
    _ ≤ ∑ p ∈ T', G p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · rw [Finset.image_subset_iff]
          intro χ hχ
          rw [Finset.mem_erase] at hχ
          obtain ⟨hχ1, _⟩ := hχ
          rw [hT, Finset.mem_sigma]
          have hcd : χ.conductor ∣ q := χ.conductor_dvd_level
          have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
          have hc_pos : 0 < χ.conductor := by
            rcases Nat.eq_zero_or_pos χ.conductor with h0 | hp
            · exact absurd (Nat.eq_zero_of_zero_dvd (h0 ▸ hcd)) (NeZero.ne q)
            · exact hp
          have hc_ne1 : χ.conductor ≠ 1 := by
            intro h
            exact hχ1 (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
          have hc_le : χ.conductor ≤ q := Nat.le_of_dvd hqpos hcd
          simp only [hi]
          refine ⟨?_, ?_⟩
          · rw [hD, Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨by omega, le_trans hc_le hqQ⟩, hcd⟩
          · rw [htt, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, DirichletCharacter.primitiveCharacter_isPrimitive (χ := χ)⟩
        · intro p _ _; simp only [hG]; positivity
    _ = ∑ f ∈ D, cutoffPrimEnergy α β X Y T f := hRHS

/-! ## 3. The large-conductor discharge (mirror of `bilinear_hLargeDisc`) -/

open Classical in
/-- **WBV4 large-conductor discharge — FULL (mirror of `bilinear_hLargeDisc`).**  The
large-conductor windowed character energy over `Dset ∩ (D0, ∞)` splits (per `χ`, one triangle
`‖a‖ ≤ ‖b‖ + ‖a − b‖`) into the FULL-`α` primitive MAIN term `‖cutoffTwist (conductor) (primitive)‖`
and the α-side coprimality ERROR `‖cutoffTwist d χ − cutoffTwist (conductor) (primitive)‖`.  The
main term is regrouped by conductor (`regroup_cutoff`, the fold's resolution) and φ-swapped
(`swapPhi_generic`, reused verbatim) onto `∑_{f≤D} (1/φf)·cutoffPrimEnergy`, closed by the named
`hMainEnergy` (the cutoff dyadic-in-conductor shell arithmetic — discharged downstream by
`dyadic_energy_le_cutoff`); the summed error is the named `hErrSum`.  Klarge = `Kmain + Kerr`. -/
theorem cutoff_hLargeDisc (α β : ℕ → ℂ) (X Y T D D0 : ℕ) (Dset : Finset ℕ)
    {A Kmain Kerr : ℝ}
    (hD1 : 1 ≤ D) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (hMainEnergy : 4 * (1 + Real.log D) *
        ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
      ≤ Kmain * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A)
    (hErrSum : ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
          (1 / (d.totient : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
              ‖cutoffTwist α β X Y T d χ - cutoffTwist α β X Y T χ.conductor χ.primitiveCharacter‖
        ≤ Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist α β X Y T d χ‖
      ≤ (Kmain + Kerr) * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
  classical
  set Dset' := Dset.filter (fun d => ¬ d ≤ D0) with hDset'
  set MainSum := ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        ‖cutoffTwist α β X Y T χ.conductor χ.primitiveCharacter‖ with hMainSum
  set ErrSum := ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        ‖cutoffTwist α β X Y T d χ - cutoffTwist α β X Y T χ.conductor χ.primitiveCharacter‖
    with hErrSumDef
  -- Step 1: S ≤ MainSum + ErrSum (per-χ triangle split).
  have hSplit : ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
          ‖cutoffTwist α β X Y T d χ‖
      ≤ MainSum + ErrSum := by
    rw [hMainSum, hErrSumDef, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun d _ => ?_)
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun χ _ => ?_)
    have h := norm_sub_norm_le (cutoffTwist α β X Y T d χ)
      (cutoffTwist α β X Y T χ.conductor χ.primitiveCharacter)
    linarith [h]
  -- Step 2: MainSum ≤ Kmain·  (regroup + extend + φ-swap + hMainEnergy).
  have hMainLe : MainSum ≤ Kmain * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
    have hsubset : Dset' ⊆ Finset.Icc 1 D := by
      intro d hd
      rw [hDset', Finset.mem_filter] at hd
      rw [Finset.mem_Icc]
      exact ⟨by omega, hDsetD d hd.1⟩
    calc MainSum
        ≤ ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
            ∑ f ∈ (Finset.Icc 2 D).filter (· ∣ d), cutoffPrimEnergy α β X Y T f := by
          rw [hMainSum]
          refine Finset.sum_le_sum (fun d hd => ?_)
          rw [hDset', Finset.mem_filter] at hd
          have hdD : d ≤ D := hDsetD d hd.1
          have hd1 : 1 ≤ d := by omega
          haveI : NeZero d := ⟨by omega⟩
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Eq.trans_le ?_ (regroup_cutoff hdD α β X Y T)
          exact Finset.sum_congr
            (congrArg (fun i => @Finset.erase (DirichletCharacter ℂ d) i Finset.univ 1)
              (Subsingleton.elim _ _)) (fun _ _ => rfl)
      _ ≤ ∑ d ∈ Finset.Icc 1 D, (1 / (d.totient : ℝ)) *
            ∑ f ∈ (Finset.Icc 2 D).filter (· ∣ d), cutoffPrimEnergy α β X Y T f := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ => ?_)
          exact mul_nonneg (by positivity)
            (Finset.sum_nonneg (fun f _ => cutoffPrimEnergy_nonneg _ _ _ _ _ _))
      _ ≤ 4 * (1 + Real.log D) *
            ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f :=
          swapPhi_generic hD1 (cutoffPrimEnergy α β X Y T)
            (fun f => cutoffPrimEnergy_nonneg α β X Y T f)
      _ ≤ Kmain * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := hMainEnergy
  -- Step 3: combine.
  calc ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist α β X Y T d χ‖
      ≤ MainSum + ErrSum := hSplit
    _ ≤ Kmain * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A
        + Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A :=
        add_le_add hMainLe hErrSum
    _ = (Kmain + Kerr) * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by ring

/-! ## 4. THE WINDOW CLOSE — `general_BV_cutoff_final` (item 7) -/

open Classical in
/-- **WBV4 (item 7, FULL) — `general_BV_cutoff_final`: the windowed bilinear-BV `L¹`-over-`d`
bound.**  The mirror of `general_BV_alpha_final` at the *cutoff* carrier: the windowed AP
discrepancy at residue `2`, summed over `Dset`, meets the target envelope, split at `D0` into

* the **small-conductor** side (`d ≤ D0`), COMPLETE via WBV3's `smallconductor_window_sum` (no
  per-`d` slot — the interval-SW is baked in);
* the **large-conductor** side (`D0 < d`), `norm_apDiscBilinCutoff_le` per `d` then
  `cutoff_hLargeDisc` (the fold + regroup + φ-swap onto `cutoffPrimEnergy`), carrying the named
  `hMainEnergy` (discharged downstream by WBV2's `dyadic_energy_le_cutoff`) and the α-side error
  `hErrSum`.

Threshold set (documented in the module header): the small side wants `0 < L`, `D0 ≤ L^C0`,
`D0 ≤ (log N)^C0`, `N ≤ M`, and the scale coupling `K·L^{A+C0} ≤ Kβ·(log N)^{A+2C0}`; the large
side wants `1 ≤ D`, `∀ d ∈ Dset, d ≤ D`, plus the two named analytic inputs `hMainEnergy`,
`hErrSum`.  Crucially there is NO `hdiv` (no `e`-dilation / δ-fibering on the plain window path)
and no `hlev`/`hD0lo`/`hMlev` at this level — those live in the downstream discharge of
`hMainEnergy` via `dyadic_energy_le_cutoff`. -/
theorem general_BV_cutoff_final {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M T D0 D : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ) (Kβ Kmain Kerr : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → N₀ ≤ N → M ≤ 2 * N → D0 ≤ N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (0 < Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        ((N : ℝ) ≤ (M : ℝ)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + C0) ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) →
        (4 * (1 + Real.log D) *
            ∑ f ∈ Finset.Icc 2 D,
              (1 / (f.totient : ℝ)) * cutoffPrimEnergy α (blockPrimeInd N) X M T f
          ≤ Kmain * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) →
        (∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
            (1 / (d.totient : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
                ‖cutoffTwist α (blockPrimeInd N) X M T d χ
                  - cutoffTwist α (blockPrimeInd N) X M T χ.conductor χ.primitiveCharacter‖
          ≤ Kerr * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) →
        ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
          ≤ (Kβ + (Kmain + Kerr)) * ((X : ℝ) * (M : ℝ))
              / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K, N₀, hK0, hsmall⟩ := smallconductor_window_sum (A := A) (C0 := C0) hA hC0
  refine ⟨K, N₀, hK0, fun α X N M T D0 D Dset r Kβ Kmain Kerr hα hKβ hN hM2N hD0N hDge1 hcop2
    hLpos hD0 hD0N' hNM hscale hD1 hDsetD hMainEnergy hErrSum => ?_⟩
  classical
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  -- Split at the threshold `D0`.
  rw [← Finset.sum_filter_add_sum_filter_not Dset (fun d => d ≤ D0)
        (fun d => ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖)]
  -- The small-conductor branch (COMPLETE, WBV3).
  have hSmall : ∑ d ∈ Dset.filter (fun d => d ≤ D0),
        ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
      ≤ Kβ * ((X : ℝ) * (M : ℝ)) / L ^ A :=
    hsmall α X N M T D0 Dset r Kβ hα hKβ hN hM2N hD0N hDge1 hcop2 hLpos hD0 hD0N' hNM hscale
  -- The large-conductor branch (WBV2 descent + fold + regroup).
  have hLarge : ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
      ≤ (Kmain + Kerr) * ((X : ℝ) * (M : ℝ)) / L ^ A := by
    refine le_trans (Finset.sum_le_sum (fun d hd => ?_))
      (cutoff_hLargeDisc α (blockPrimeInd N) X M T D D0 Dset hD1 hDsetD hMainEnergy hErrSum)
    rw [Finset.mem_filter] at hd
    have hd1 : 1 ≤ d := hDge1 d hd.1
    haveI : NeZero d := ⟨by omega⟩
    refine (norm_apDiscBilinCutoff_le α (blockPrimeInd N) X M (r d) T (hcop2 d hd.1)).trans_eq ?_
    congr 1
    exact Finset.sum_congr
      (congrArg (fun i => @Finset.erase (DirichletCharacter ℂ d) i Finset.univ 1)
        (Subsingleton.elim _ _))
      (fun _ _ => rfl)
  -- Assemble.
  calc ∑ d ∈ Dset.filter (fun d => d ≤ D0),
          ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
        + ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
          ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
      ≤ Kβ * ((X : ℝ) * (M : ℝ)) / L ^ A
        + (Kmain + Kerr) * ((X : ℝ) * (M : ℝ)) / L ^ A := add_le_add hSmall hLarge
    _ = (Kβ + (Kmain + Kerr)) * ((X : ℝ) * (M : ℝ)) / L ^ A := by ring

/-! ## 5. THE hHD FEED — `hHD_of_generalBV_window` (item 9)

The `blockBox_windowDisc_eq` identification (WBV3) turns a decided (`hord`-cleared, high-piece)
box's honest discrepancy into the **difference** of the two one-sided cutoff carriers at
`T = x` and `T = x/2+1`.  Taking norms (the T-difference triangle: two `apDiscBilinCutoff`
applications per box, one per cutoff) and summing over `d`, `general_BV_cutoff_final` prices
both — giving the per-`(j, box)` honest-discrepancy `L¹`-over-`d` bound directly at the
`BlockPricing.blockBoxHonestDisc` object.

**Feeding `BlockPricing`'s EXISTING slot.**  `BlockPricing.hHDblocks_of_perBlock` takes a
per-block bound `hBlock : ∀ j, ∑_d (if d<bound then |blockHonestDisc j d| else 0) ≤ RBlock j`
and closes the `hHD` double sum of `hBVblocks_of_generalBV`.  The full-block `blockHonestDisc_j d`
is the `O(log²x)`-piece sum of box honest discrepancies
`∑_{(a,b) piece} blockBoxHonestDisc … j N M a b d`
(the `SwitchStrip.apDiscBilin_sum_alpha` additivity over the decided/band `m`-pieces and the
dyadic `p₃`-pieces).  On the **high pieces** (`N ≥ y`, so `hord : b ≤ z·N+1` holds, per the recon
R1) each box is priced by `hHD_of_generalBV_window` below.

**The `hLowPieces` residual (documented named object).**  On the **low pieces** the ordering
clearance `hord` fails (the box straddles the ordering diagonal `p₂ ≤ p₃`), so the corner-free
identification does not apply.  The residual honest budget for these pieces stays a NAMED
hypothesis of the block assembly, of the shape
```
hLowPieces : ∑_{j} ∑_{(a,b) low piece} ∑_{d<bound} |blockBoxHonestDisc x z y ε₀ j N M a b d|
               ≤ RLow            (RLow ≤ x/(log x)^{10}-budget slack)
```
— the ordering diagonal at low pieces is THIN (the band where `p₂ ≈ p₃`), dischargeable
downstream by a crude thin-band count or a dedicated H-glue/SW4 node; it is NOT part of the
window carrier and is deliberately left for that node.  `hHD_of_generalBV_window` supplies the
high-piece prices; `hLowPieces` + the piece-decomposition assemble them into `hBlock`. -/

open Classical in
/-- **WBV4 (item 9, FULL) — `hHD_of_generalBV_window`: the per-`(j, box)` honest-discrepancy price
at the T-difference.**  On a decided (`hord`-cleared) box `[a, b) × (N, M]`, the honest box
discrepancy summed over `d ∈ Dset` is bounded by TWICE the one-sided cutoff price: via
`blockBox_windowDisc_eq` the honest discrepancy IS the difference of the `T = x` and `T = x/2+1`
cutoff carriers (`nuChen d = 1/φd`, `nuChen_eq_inv_totient`), so `|blockBoxHonestDisc| ≤
‖apDiscBilinCutoff x‖ + ‖apDiscBilinCutoff (x/2+1)‖` (the triangle), and the two summed carrier
prices `hprice_hi`/`hprice_lo` are exactly what `general_BV_cutoff_final` supplies at the two
cutoffs.  This is the high-piece building block of `BlockPricing.hHDblocks_of_perBlock`'s
per-block `hBlock`; see the section header for the piece-decomposition and the `hLowPieces`
residual. -/
theorem hHD_of_generalBV_window {x z y : ℕ} {ε₀ : ℝ} {j N M a b X : ℕ} (Dset : Finset ℕ)
    {P : ℝ}
    (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * N + 1) (hxlo : x / 2 + 1 ≤ x)
    (hprice_hi : ∑ d ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
        (blockPrimeInd N) X M 2 d x‖ ≤ P)
    (hprice_lo : ∑ d ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
        (blockPrimeInd N) X M 2 d (x / 2 + 1)‖ ≤ P) :
    ∑ d ∈ Dset, |blockBoxHonestDisc x z y ε₀ j N M a b d| ≤ 2 * P := by
  classical
  -- per-`d`: the honest box discrepancy IS the cutoff T-difference; take the triangle.
  have hd_le : ∀ d ∈ Dset,
      |blockBoxHonestDisc x z y ε₀ j N M a b d|
        ≤ ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd N) X M 2 d x‖
          + ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd N) X M 2 d
              (x / 2 + 1)‖ := by
    intro d _
    -- the identification (`blockBox_windowDisc_eq`) rewritten as `(honest : ℂ) = A(x) − A(x/2+1)`.
    have hid : ((blockBoxHonestDisc x z y ε₀ j N M a b d : ℝ) : ℂ)
        = apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd N) X M 2 d x
          - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd N) X M 2 d
              (x / 2 + 1) := by
      rw [blockBox_windowDisc_eq (X := X) (d := d) hz hbX hord hxlo, blockBoxHonestDisc,
        nuChen_apply]
      push_cast
      ring
    have hnorm : |blockBoxHonestDisc x z y ε₀ j N M a b d|
        = ‖((blockBoxHonestDisc x z y ε₀ j N M a b d : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, hid]
    exact norm_sub_le _ _
  -- sum over `d` and consume the two one-sided prices.
  calc ∑ d ∈ Dset, |blockBoxHonestDisc x z y ε₀ j N M a b d|
      ≤ ∑ d ∈ Dset,
          (‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
                (blockPrimeInd N) X M 2 d x‖
            + ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
                (blockPrimeInd N) X M 2 d (x / 2 + 1)‖) := Finset.sum_le_sum hd_le
    _ = (∑ d ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
            (blockPrimeInd N) X M 2 d x‖)
        + (∑ d ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
            (blockPrimeInd N) X M 2 d (x / 2 + 1)‖) := Finset.sum_add_distrib
    _ ≤ P + P := add_le_add hprice_hi hprice_lo
    _ = 2 * P := by ring

/-! ## 6. Composition sanity (item 3) — the end-to-end chain elaborates

The honest-discrepancy price feeds the BVP switch line:

* `general_BV_cutoff_final` — the windowed `L¹`-over-`d` carrier price at each cutoff `T` (the
  `hprice_hi`/`hprice_lo` inputs of `hHD_of_generalBV_window`, at `T = x` and `T = x/2+1`);
* `hHD_of_generalBV_window` — the per-`(j, box)` honest-discrepancy price (the T-difference
  triangle);
* `BlockPricing.hHDblocks_of_perBlock` — assembles the per-block `hHD` from the per-piece prices
  (high pieces via `hHD_of_generalBV_window`, low pieces via the documented `hLowPieces`);
* `BlockPricing.hBVblocks_of_generalBV` — the `hBVblocks` shape of the block-remainder close;
* `SwitchBlocks.mainA3_of_block_remainders` — the BVP endpoint that names `hBVblocks`.

Each declaration below elaborates, confirming the composition chain is well-typed end-to-end. -/

section CompositionSanity

#check @Salt.Chen.general_BV_cutoff_final
#check @Salt.Chen.hHD_of_generalBV_window
#check @Salt.Chen.hHDblocks_of_perBlock
#check @Salt.Chen.hBVblocks_of_generalBV
#check @Salt.Chen.mainA3_of_block_remainders

end CompositionSanity

end Salt.Chen
