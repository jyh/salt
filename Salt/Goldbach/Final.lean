/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Glue

/-!
# G-FINAL — the min-side tail correction (Goldbach terminal, part III: items 1–2)

The corrected design (pilot ledger 2026-07-16 ~10:00, G-GLUE catch-the-house #4): the LIVE-LOW
tail's Term B (the additive `2·Y` leg of the trivial AP bound, `Y := pieceM k'`) is TOO BIG at the
claimed bound — the live floors force `M ≈ 4XM/(zy) ≈ N^{0.5357}`, so `Σ_m 2·M·bnd ≈ N^{1.03}` per
box, above `N/(log N)^{11}`.  The fix, house-verified at the worst case, is **the min-side count**:
the trivial AP bound counts over EITHER side of the bilinear pair, so the additive leg is really
`2·min(X, Y)` with `X := 2^{i+1}−1`, `Y := pieceM k'`; and `min(X, Y) ≤ √(X·Y) = √(X·M)`, which on a
LIVE-LOW box (`¬hDwide`: `√(XM)/L^{18} < D = opQ·bnd`) is `< opQ·bnd·L^{18}`, giving
`Term B ≤ 2·opQ·bnd²·L^{18} ≈ N^{0.994}·L^{18} ≪ N/(log N)^{11}` at the tower margin.

This file lands (items 1–2, Final.lean per the pre-authorized split):

* **`apDiscBilinCutoff_symm`** — the windowed carrier is symmetric under `(α, X) ↔ (β, Y)` (the
  cutoff `m·n ≤ T`, the residue condition, and `IsUnit (m·n)` are all `m ↔ n` symmetric).
* **`gold_box_disc_trivial_min`** (item 1a) — the min-side per-modulus bound
  `‖apDiscBilinCutoff α β X Y R d T‖ ≤ 2·X·Y/d + 2·min(X, Y)`: the `Y`-side is
  `Tail.gold_box_disc_trivial`; the `X`-side is the same lemma on `(β, α, Y, X)` transported by the
  symmetry; the `min` combines them.
* **`gold_box_tail_min`** (item 1b) — the `QImage` harmonic tail with the min additive leg:
  `Σ_m (2·X·Y/m + 2·min(X, Y)) ≤ 2·X·Y/Q·(1 + log bnd) + 2·min(X, Y)·bnd` (Term A the landed
  harmonic saving; Term B the min leg times `#QImage ≤ bnd`).
* **`gold_box_carrier_tail_min` / `gold_box_price_tail_min`** — the LIVE-LOW carrier bridge with the
  min leg (mirror of `Tail2.gold_box_carrier_tail` / `gold_box_price_tail`).
* **`min_le_sqrt_mul`** — the elementary `min(X, Y) ≤ √(X·Y)` (`min² ≤ X·Y`).
* **`goldBtailMin` / `goldPriceMin` / `gold_box_hprice_at_min`** — the min-form piecewise price and
  the terminal's `hprice` slot at it (mirror of `Glue.goldBtail` / `goldPrice` /
  `gold_box_hprice_at`, superseding the `2·M·bnd` leg with the min leg).
* **`goldBtailMinSlot` / `gold_box_hbox_at_min`** — the min-form `htail` tail crumb and the `hbox`
  summand of `gold_hSum_geo` (mirror of `Glue.goldBtailSlot` / `gold_box_hbox_at`).

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1a. The windowed-carrier symmetry and the min-side per-modulus bound -/

/-- **`apDiscBilinCutoff_symm`.**  The windowed fixed-residue bilinear AP discrepancy is symmetric
under swapping the two coefficient/range pairs: `apDiscBilinCutoff α β X Y R d T =
apDiscBilinCutoff β α Y X R d T`.  The cutoff `m·n ≤ T`, the residue test `(m·n) ≡ R`, and
`IsUnit (m·n)` are all symmetric in `m, n`, so `Finset.sum_comm'` (reindexing the dependent double
sum) plus `mul_comm` on `m·n` and on the coefficient product close both residue and unit legs. -/
theorem apDiscBilinCutoff_symm (α β : ℕ → ℂ) (X Y R d T : ℕ) :
    apDiscBilinCutoff α β X Y R d T = apDiscBilinCutoff β α Y X R d T := by
  classical
  unfold apDiscBilinCutoff
  have key : ∀ (γ δ : ℕ → ℂ),
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
          (if ((m * n : ℕ) : ZMod d) = (R : ZMod d) then γ m * δ n else 0))
        = (∑ p ∈ Finset.Icc 1 Y, ∑ q ∈ (Finset.Icc 1 X).filter (fun q => p * q ≤ T),
            (if ((p * q : ℕ) : ZMod d) = (R : ZMod d) then δ p * γ q else 0)) := by
    intro γ δ
    rw [Finset.sum_comm' (s := Finset.Icc 1 X)
        (t := fun m => (Finset.Icc 1 Y).filter (fun n => m * n ≤ T))
        (t' := Finset.Icc 1 Y) (s' := fun n => (Finset.Icc 1 X).filter (fun m => m * n ≤ T))
        (by intro m n; simp only [Finset.mem_filter]; tauto)]
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr ?_ (fun m _ => ?_))
    · apply Finset.filter_congr; intro m _; rw [Nat.mul_comm]
    · rw [Nat.mul_comm m n, mul_comm (γ m) (δ n)]
  have keyU : ∀ (γ δ : ℕ → ℂ),
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
          (if IsUnit ((m * n : ℕ) : ZMod d) then γ m * δ n else 0))
        = (∑ p ∈ Finset.Icc 1 Y, ∑ q ∈ (Finset.Icc 1 X).filter (fun q => p * q ≤ T),
            (if IsUnit ((p * q : ℕ) : ZMod d) then δ p * γ q else 0)) := by
    intro γ δ
    rw [Finset.sum_comm' (s := Finset.Icc 1 X)
        (t := fun m => (Finset.Icc 1 Y).filter (fun n => m * n ≤ T))
        (t' := Finset.Icc 1 Y) (s' := fun n => (Finset.Icc 1 X).filter (fun m => m * n ≤ T))
        (by intro m n; simp only [Finset.mem_filter]; tauto)]
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr ?_ (fun m _ => ?_))
    · apply Finset.filter_congr; intro m _; rw [Nat.mul_comm]
    · rw [Nat.mul_comm m n, mul_comm (γ m) (δ n)]
  rw [key α β, keyU α β]

/-- **`gold_box_disc_trivial_min` (item 1a).**  The min-side crude per-modulus bound: for bounded
coefficients `‖α‖, ‖β‖ ≤ 1`, modulus `d ≥ 1`, and residue `R` coprime to `d`,
`‖apDiscBilinCutoff α β X Y R d T‖ ≤ 2·X·Y/d + 2·min(X, Y)`.  The trivial AP bound counts over
EITHER side of the bilinear pair: the `Y`-side is `gold_box_disc_trivial` (`+2·Y`); the `X`-side
is the same lemma applied to `(β, α, Y, X)` and transported through `apDiscBilinCutoff_symm`
(`+2·X`); `rcases le_total (X:ℝ) Y` picks the smaller leg. -/
theorem gold_box_disc_trivial_min {α β : ℕ → ℂ} {X Y R d T : ℕ}
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1)
    (hd : 1 ≤ d) (hcop : Nat.Coprime R d) :
    ‖apDiscBilinCutoff α β X Y R d T‖ ≤ 2 * ((X : ℝ) * Y / d) + 2 * min (X : ℝ) Y := by
  have hY : ‖apDiscBilinCutoff α β X Y R d T‖ ≤ 2 * ((X : ℝ) * Y / d) + 2 * Y :=
    gold_box_disc_trivial hα hβ hd hcop
  have hX0 : ‖apDiscBilinCutoff β α Y X R d T‖ ≤ 2 * ((Y : ℝ) * X / d) + 2 * X :=
    gold_box_disc_trivial hβ hα hd hcop
  have hX : ‖apDiscBilinCutoff α β X Y R d T‖ ≤ 2 * ((X : ℝ) * Y / d) + 2 * X := by
    rw [apDiscBilinCutoff_symm α β X Y R d T]
    have heq : 2 * ((Y : ℝ) * X / d) + 2 * X = 2 * ((X : ℝ) * Y / d) + 2 * X := by ring
    linarith [hX0]
  rcases le_total (X : ℝ) Y with h | h
  · rw [min_eq_left h]; linarith [hX]
  · rw [min_eq_right h]; linarith [hY]

/-! ## 1b. The `QImage` harmonic tail with the min additive leg -/

/-- **`gold_box_tail_min` (item 1b).**  The `QImage` harmonic tail with the min-side additive leg:
`Σ_{m = Q·d, d ∣ Ps, d < bnd} (2·X·Y/m + 2·min(X, Y)) ≤ 2·X·Y/Q·(1 + log bnd) + 2·min(X, Y)·bnd`.
Term A (the `X·Y/m` legs) is the landed harmonic saving `(2·X·Y/Q)·Σ_d 1/d ≤ (2·X·Y/Q)·(1 + log
bnd)`; Term B (the `2·min(X, Y)` legs) contributes `2·min(X, Y)·#QImage ≤ 2·min(X, Y)·bnd`.  Mirror
of `Tail.gold_box_tail_le` with `Y ↦ min(X, Y)` in the additive constant. -/
theorem gold_box_tail_min (X Y Q Ps : ℕ) (bound : ℝ) (hQ : 1 ≤ Q) (hb : 1 ≤ bound) :
    (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
        (2 * ((X : ℝ) * Y / m) + 2 * min (X : ℝ) Y))
      ≤ 2 * (X : ℝ) * Y / Q * (1 + Real.log bound) + 2 * min (X : ℝ) Y * bound := by
  classical
  set c : ℝ := 2 * min (X : ℝ) Y with hcdef
  have hc0 : (0 : ℝ) ≤ c := by
    rw [hcdef]; have : (0 : ℝ) ≤ min (X : ℝ) Y := le_min (by positivity) (by positivity); linarith
  set S := (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound) with hSdef
  have hb0 : (0 : ℝ) ≤ bound := le_trans zero_le_one hb
  have hsub : S ⊆ Finset.Icc 1 ⌊bound⌋₊ := by
    intro d hd
    rw [hSdef, Finset.mem_filter] at hd
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_floor (le_of_lt hd.2)⟩
  rw [Finset.sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left (by omega) hxy)]
  rw [Finset.sum_add_distrib]
  have hAeq : (∑ d ∈ S, 2 * ((X : ℝ) * Y / ((Q * d : ℕ) : ℝ)))
      = (2 * (X : ℝ) * Y / Q) * (∑ d ∈ S, (1 / (d : ℝ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    push_cast; ring
  have hharm : (∑ d ∈ S, (1 / (d : ℝ))) ≤ 1 + Real.log bound := by
    calc (∑ d ∈ S, (1 / (d : ℝ)))
        ≤ ∑ d ∈ Finset.Icc 1 ⌊bound⌋₊, (1 / (d : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      _ = (harmonic ⌊bound⌋₊ : ℝ) := by
          rw [harmonic_eq_sum_Icc]; push_cast; simp only [one_div]
      _ ≤ 1 + Real.log bound := harmonic_floor_le_one_add_log bound hb
  have hApos : (0 : ℝ) ≤ 2 * (X : ℝ) * Y / Q := by positivity
  have hA : (∑ d ∈ S, 2 * ((X : ℝ) * Y / ((Q * d : ℕ) : ℝ)))
      ≤ 2 * (X : ℝ) * Y / Q * (1 + Real.log bound) := by
    rw [hAeq]; exact mul_le_mul_of_nonneg_left hharm hApos
  have hcardS : (S.card : ℝ) ≤ bound := by
    calc (S.card : ℝ) ≤ ((Finset.Icc 1 ⌊bound⌋₊).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = (⌊bound⌋₊ : ℝ) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
      _ ≤ bound := Nat.floor_le hb0
  have hB : (∑ _d ∈ S, c) ≤ c * bound := by
    rw [Finset.sum_const, nsmul_eq_mul]
    calc (S.card : ℝ) * c ≤ bound * c := mul_le_mul_of_nonneg_right hcardS hc0
      _ = c * bound := by ring
  have hcomb := add_le_add hA hB
  rw [hcdef] at hcomb ⊢
  linarith [hcomb]

/-! ## 1c. The LIVE-LOW carrier bridge with the min leg -/

open Classical in
set_option maxHeartbeats 800000 in
/-- **`gold_box_carrier_tail_min`.**  The one-sided windowed carrier sum over the `QImage` moduli,
bounded by the min-side crude harmonic tail (mirror of `Tail2.gold_box_carrier_tail`, `+2·Y ↦
+2·min(X, M)`).  The coefficient norms feed `gold_box_disc_trivial_min` per modulus; the `crtClassG`
coprimality supplies the `R`-unit hypothesis; `gold_box_tail_min` closes the `QImage` sum. -/
theorem gold_box_carrier_tail_min (N z y : ℕ) (ε₀ : ℝ) (j k' Q a Ps : ℕ) (QR : ℝ) (Dlev T : ℕ)
    (hQPs : Nat.Coprime Q Ps) (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
    (hQ1 : 1 ≤ Q) (hb : 1 ≤ QR * Dlev) (i : ℕ) :
    (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
        ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
              (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
              (crtClassG Q (m / Q) N a) m T‖)
      ≤ 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q * (1 + Real.log (QR * Dlev))
          + 2 * min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) * (QR * Dlev) := by
  have hinner : ∀ m, ‖restrictAlpha (blockAlpha z y ε₀ j) 0
      (min (z * pieceN k' + 1) (N / 2 + 1)) m‖ ≤ 1 :=
    fun m => norm_restrictAlpha_le_one (fun m' => norm_blockAlpha_le_one z y ε₀ j m') 0 _ m
  have halpha : ∀ m, ‖restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
      (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)) m‖ ≤ 1 :=
    fun m => norm_restrictAlpha_le_one hinner (2 ^ i) (2 ^ (i + 1)) m
  have hbeta : ∀ n, ‖blockPrimeInd (pieceN k') n‖ ≤ 1 := blockPrimeInd_norm_le_one (pieceN k')
  refine le_trans (Finset.sum_le_sum (fun m hm => ?_))
    (gold_box_tail_min (2 ^ (i + 1) - 1) (pieceM k') Q Ps (QR * Dlev) hQ1 hb)
  have hcop : Nat.Coprime (crtClassG Q (m / Q) N a) m :=
    gold_crtClassG_coprime_of_mem (QR * Dlev) hQ1 hQPs hQNa hPsN hm
  have hm1 : 1 ≤ m := by
    obtain ⟨d, hd, hmd⟩ := Finset.mem_image.mp hm
    have hdp : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hpos : 0 < Q * d := Nat.mul_pos (by omega) hdp
    rw [← hmd]; exact hpos
  exact gold_box_disc_trivial_min halpha hbeta hm1 hcop

open Classical in
set_option maxHeartbeats 800000 in
/-- **`gold_box_price_tail_min`.**  The two-cutoff carrier sum — the EXACT `hprice`-slot LHS of
`gold_hBVblocksW_discharge'` at a LIVE-LOW box — bounded by `2×` the single-cutoff min harmonic
tail.  This is the min-form LIVE-LOW branch value the piecewise `goldPriceMin` takes. -/
theorem gold_box_price_tail_min (N z y : ℕ) (ε₀ : ℝ) (j k' k Q a Ps : ℕ) (QR : ℝ) (Dlev i : ℕ)
    (hQPs : Nat.Coprime Q Ps) (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
    (hQ1 : 1 ≤ Q) (hb : 1 ≤ QR * Dlev) :
    (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
        ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
              (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
              (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
      + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
          ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
              (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
              (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
      ≤ 2 * (2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q * (1 + Real.log (QR * Dlev))
          + 2 * min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) * (QR * Dlev)) := by
  have h1 := gold_box_carrier_tail_min N z y ε₀ j k' Q a Ps QR Dlev (goldCut N (k + 1))
    hQPs hQNa hPsN hQ1 hb i
  have h2 := gold_box_carrier_tail_min N z y ε₀ j k' Q a Ps QR Dlev (goldCut N k)
    hQPs hQNa hPsN hQ1 hb i
  linarith [h1, h2]

/-! ## 1d. The elementary `min(X, Y) ≤ √(X·Y)` -/

/-- **`min_le_sqrt_mul`.**  For `0 ≤ X, Y`, `min X Y ≤ √(X·Y)` — since `min² ≤ X·Y` (`min ≤ X` and
`min ≤ Y`, both nonneg).  This is the geometric-mean bound the live-low `htail` close uses to
convert the `2·min(X, M)·bnd` leg into `2·√(X·M)·bnd`, then cap `√(X·M) < opQ·bnd·L^{18}` from
`¬hDwide`. -/
theorem min_le_sqrt_mul {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    min X Y ≤ Real.sqrt (X * Y) := by
  have hmin0 : 0 ≤ min X Y := le_min hX hY
  have hsq : min X Y * min X Y ≤ X * Y :=
    mul_le_mul (min_le_left _ _) (min_le_right _ _) hmin0 hX
  rw [show X * Y = X * Y from rfl]
  calc min X Y = Real.sqrt (min X Y * min X Y) := by rw [Real.sqrt_mul_self hmin0]
    _ ≤ Real.sqrt (X * Y) := Real.sqrt_le_sqrt hsq

/-! ## 2 (min-form Glue mirrors). The piecewise price with the min tail leg -/

/-- **`goldBtailMin`** — the min-form LIVE-LOW branch value: `gold_box_price_tail_min`'s RHS, the
crude two-cutoff harmonic tail with the min additive leg `2·min(X, M)·bnd` in place of `Glue`'s
`2·M·bnd` (`X := 2^{i+1}−1`, `M := pieceM k'`). -/
noncomputable def goldBtailMin (Q : ℕ) (bnd : ℝ) (k' i : ℕ) : ℝ :=
  2 * (2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q * (1 + Real.log bnd)
      + 2 * min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) * bnd)

open Classical in
/-- **`goldPriceMin`** — the min-form piecewise per-box price (mirror of `Glue.goldPrice` with
`goldBtail ↦ goldBtailMin`).  DEAD → `0`; LIVE-HIGH (wide window) → `boxPriceKerr Kc k' i`;
LIVE-LOW → `boxPriceKerr Kc k' i + goldBtailMin Q bnd k' i`. -/
noncomputable def goldPriceMin (Kc : ℝ) (N D Q : ℕ) (bnd : ℝ) (k' i : ℕ) : ℝ :=
  if min (opZ N * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i then 0
  else boxPriceKerr Kc k' i
    + (if (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))
       then 0
       else goldBtailMin Q bnd k' i)

set_option maxHeartbeats 800000 in
/-- **`gold_box_hprice_at_min` (item 1, the min-form `hprice` slot).**  The terminal's `hprice` slot
(`gold_hBVblocksW_discharge'`, `PDiag.lean:511`) at `Price j k' k i := goldPriceMin Kc N D Q
(QR·Dlev) k' i`, the 3-way case split compiled.  DEAD via `gold_box_price_vanish`; LIVE-HIGH via
`gold_box_hprice_op`; LIVE-LOW via `gold_box_price_tail_min` (+ `boxPriceKerr_nonneg`).  Mirror of
`Glue.gold_box_hprice_at` with the min tail. -/
theorem gold_box_hprice_at_min : ∃ (Kc : ℝ) (x₁ : ℕ), 1 ≤ Kc ∧
    ∀ (N : ℕ), x₁ ≤ N → ∀ (ε₀ : ℝ) (j k' k i K Q a D Ps Dlev : ℕ) (QR : ℝ),
      Nat.Coprime Q Ps → Nat.Coprime Q (N - a) → Nat.Coprime Ps N → 1 ≤ Q →
      1 ≤ QR * Dlev →
      i ∈ dyadicBoundary (pieceN k') (pieceM k')
        (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K →
      ((goldCut N (k + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) →
      (∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
          (fun d => Q * d), d ≤ D) →
      (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
          ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ N) (opY N) ε₀ j) 0
              (min (opZ N * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
              (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
        + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
              (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ N) (opY N) ε₀ j) 0
                (min (opZ N * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
                (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
        ≤ goldPriceMin Kc N D Q (QR * Dlev) k' i := by
  classical
  obtain ⟨Kc, x₁, hKc, hop⟩ := gold_box_hprice_op
  refine ⟨Kc, x₁, hKc, ?_⟩
  intro N hN ε₀ j k' k i K Q a D Ps Dlev QR hQPs hQNa hPsN hQ1 hb hi hDge hDsetD
  unfold goldPriceMin
  by_cases hcap : min (opZ N * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i
  · rw [if_pos hcap]
    exact le_of_eq (gold_box_price_vanish hcap _)
  · rw [if_neg hcap]
    by_cases hwide : (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)))
        ^ ((13 : ℝ) + 5) ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))
    · rw [if_pos hwide, add_zero]
      exact hop N hN ε₀ j k' k i K Q a D Ps Dlev QR k
        hQPs hQNa hPsN hQ1 hi hDge hwide hDsetD
    · rw [if_neg hwide]
      have htail := gold_box_price_tail_min N (opZ N) (opY N) ε₀ j k' k Q a Ps QR Dlev i
        hQPs hQNa hPsN hQ1 hb
      have hnn : (0 : ℝ) ≤ boxPriceKerr Kc k' i :=
        boxPriceKerr_nonneg (le_trans zero_le_one hKc) k' i
      unfold goldBtailMin
      linarith [htail]

open Classical in
/-- **`goldBtailMinSlot`** — the min-form tail contribution `gold_hSum_geo`'s `htail` slot consumes:
`0` on DEAD and LIVE-HIGH boxes, `goldBtailMin Q bnd k' i` on LIVE-LOW boxes (mirror of
`Glue.goldBtailSlot`). -/
noncomputable def goldBtailMinSlot (N D Q : ℕ) (bnd : ℝ) (k' i : ℕ) : ℝ :=
  if min (opZ N * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i then 0
  else if (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
        ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))
     then 0
     else goldBtailMin Q bnd k' i

/-- **`gold_box_hbox_at_min` (item 1, the min-form `hbox` summand).**  The `hbox` summand of
`gold_hSum_geo` at `Price 0 k' k i := goldPriceMin Kc N D Q bnd k' i` and `Btail k' k i :=
goldBtailMinSlot N D Q bnd k' i`, `Cgeo := 3^{12}·gboxConst`.  Mirror of `Glue.gold_box_hbox_at`
with the min tail term. -/
theorem gold_box_hbox_at_min {Kc : ℝ} (hKc : 1 ≤ Kc) : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    ∀ (D Q : ℕ) (bnd : ℝ) (k' k i K : ℕ),
      i ∈ dyadicBoundary (pieceN k') (pieceM k')
        (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K →
      goldPriceMin Kc N D Q bnd k' i
        ≤ (3 ^ 12 * gboxConst) * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12
          + goldBtailMinSlot N D Q bnd k' i := by
  obtain ⟨x₁, hbox⟩ := gold_box_hbox_geoN hKc
  refine ⟨x₁, fun N hN D Q bnd k' k i K hi => ?_⟩
  have hgeo0 : (0 : ℝ)
      ≤ (3 ^ 12 * gboxConst) * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 := by
    have : (0 : ℝ) ≤ gboxConst := gboxConst_nonneg
    positivity
  have hlive_of : ¬ (min (opZ N * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i) →
      2 ^ i < opZ N * pieceN k' + 1 :=
    fun h => lt_of_lt_of_le (not_le.mp h) (min_le_left _ _)
  unfold goldPriceMin goldBtailMinSlot
  split_ifs with hcap hwide
  · linarith
  · have hkerr := hbox N hN k' k i K hi (hlive_of hcap); linarith
  · have hkerr := hbox N hN k' k i K hi (hlive_of hcap); linarith

/-! ## Byte-locks — the min pieces fill the terminal's slots -/

section ByteLock

-- item 1a/1b — the min-side per-modulus bound + the min harmonic tail
#check @Salt.Goldbach.apDiscBilinCutoff_symm
#check @Salt.Goldbach.gold_box_disc_trivial_min
#check @Salt.Goldbach.gold_box_tail_min
-- the LIVE-LOW carrier bridge with the min leg
#check @Salt.Goldbach.gold_box_carrier_tail_min
#check @Salt.Goldbach.gold_box_price_tail_min
-- the min-form piecewise price + the two terminal slots at it
#check @Salt.Goldbach.gold_box_hprice_at_min
#check @Salt.Goldbach.gold_box_hbox_at_min
-- the geometric-mean cap fact
#check @Salt.Goldbach.min_le_sqrt_mul
-- the landed suppliers this composes (DEAD / LIVE-HIGH branch value + geometric hbox)
#check @Salt.Goldbach.gold_box_hprice_op
#check @Salt.Goldbach.gold_box_hbox_geoN
-- the consumers whose slots these fill
#check @Salt.Goldbach.gold_hSum_geo
#check @Salt.Goldbach.gold_hBVblocksW_discharge'

end ByteLock

end Salt.Goldbach
