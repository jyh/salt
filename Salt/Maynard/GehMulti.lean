/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehVaughan

/-!
# The GEH door — the multiblock heart (design node D-N2a, the `hdom` discharge)

Design freeze: `docs/exploration/s2-b3-design.md`, RE-CUT block (2026-07-17);
boundary recon `docs/exploration/pilot.md` ~12:50 (S2-B3-RECON2).  This file
lands the **multiblock combinator** that turns the amended (uniform) `GEH_min`
into a `PieceObligationU`, discharging the `hdom` domination that
`pieceObligationU_of_GEH_single` left as a hypothesis.

## Why the amendment is the whole game

The frozen `GEH_min` had `∃ B C` *after* `∀ family` and a single top cutoff.  The
Type-II bilinear term `vP3` is a sum over an `x`-growing family of dyadic blocks;
with a per-family haircut there is no common `B`, and with a single cutoff the
prefix-`y` truncation of the top blocks is uncontrolled.  The AMENDED `GEH_min`
(house, 2026-07-16) fixes both:

* `∃ B C` OUTSIDE `∀ α β N M` — **one `(B, C)` for every block** (uniform over
  the coefficient/SW class fixed by `(ε, A, k, j, KF)`).
* the cutoff is any prefix `y ≤ 4 N M` — **the top-block truncation is legal**.

`pieceObligationU_of_multiblock` exploits exactly this: it destructures `GEH_min`
ONCE, applies the `∀`-family bound to each of the `m x` blocks with the SAME
`(B, C)`, and sums.  The block-count inflation `m x ≤ D (log x)^p` is absorbed by
invoking `GEH_min` at the inflated saving `A + p`:
`∑_blocks C x/log^{A+p} = m x · C x/log^{A+p} ≤ D C x/log^A`.

## Case space (enumerated; a NEW case is a STOP-AND-FLAG)

The combinator's proof splits on exactly these corners; the instantiations must
supply hypotheses covering each:

* **block grid** — the `m x` dyadic blocks, indexed `i ∈ range (m x)`; each is a
  balanced convolution `dconv (α i x) (β i x)` on scales `(N i x, M i x)`.
* **partial end blocks** — the top block whose support `(N M, 4 N M]` overruns
  the cutoff `y`; handled by `seqDiscrepancy_truncate` (the `y`-uniform cutoff is
  what makes this legal), the bottom block by the same support truncation.
* **the `y`-truncation** — each block is applied to `GEH_min` at cutoff
  `min y (4 N M) ≤ 4 N M`; the identity `seqDiscrepancy f y = seqDiscrepancy f
  (min y (4NM))` (support `≤ 4NM`, from `CoeffAt`) rewires it.
* **`(d, q)` coprimality corners** — internal to `seqDiscrepancy`; untouched here
  (the block weights are honest `dconv`, `CoeffAt`-admissible).
* **`A`-inflation bookkeeping** — invoke at `A + p`, cancel `log^p` against
  `m x ≤ D log^p x`.
* **small `x`** — `x = 2` uses the crude universal bound
  `seqDiscrepancy_le_two_mul_sum_abs` (no `GEH_min`, no window); folded into the
  constant like `lambdaLevelU_of_pieceObligationsU`'s `Ctwo`.
-/

open Finset

/-- **Dyadic-block support.**  A balanced Dirichlet convolution `dconv α β` whose
first factor is supported on `Ioc NN (2 NN)` and second on `Ioc MM (2 MM)`
vanishes above `4 NN MM` (the top of the product support `(NN MM, 4 NN MM]`).
The support fact that lets the top block's prefix-`y` truncation be rewired to a
`GEH_min` cutoff `≤ 4 N M`. -/
theorem dconv_eq_zero_of_support {α β : ℕ → ℝ} {NN MM : ℕ}
    (hα : ∀ n, α n ≠ 0 → n ∈ Finset.Ioc NN (2 * NN))
    (hβ : ∀ n, β n ≠ 0 → n ∈ Finset.Ioc MM (2 * MM))
    {n : ℕ} (hn : 4 * NN * MM < n) : dconv α β n = 0 := by
  unfold dconv
  refine Finset.sum_eq_zero (fun d hd => ?_)
  rcases eq_or_ne (α d) 0 with h0 | h0
  · rw [h0, zero_mul]
  rcases eq_or_ne (β (n / d)) 0 with h1 | h1
  · rw [h1, mul_zero]
  exfalso
  have hd2 := hα d h0
  have hq2 := hβ (n / d) h1
  rw [Finset.mem_Ioc] at hd2 hq2
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have heq : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  have hle : d * (n / d) ≤ (2 * NN) * (2 * MM) := Nat.mul_le_mul hd2.2 hq2.2
  rw [heq] at hle
  have hrw : (2 * NN) * (2 * MM) = 4 * NN * MM := by ring
  rw [hrw] at hle
  omega

/-- **Cutoff truncation for `seqDiscrepancy`.**  If a weight `f` vanishes above
`S` and `S ≤ y`, then its sequence discrepancy at cutoff `y` equals its
discrepancy at cutoff `S` (the tail `(S, y]` contributes only zeros to both the
residue sums and the coprime mean).  Applied with `S = 4 N M`, this rewires a
block's cutoff-`y` discrepancy to the top cutoff `GEH_min` controls. -/
theorem seqDiscrepancy_truncate {f : ℕ → ℝ} {S : ℕ} (hf : ∀ n, S < n → f n = 0)
    (y q : ℕ) (hSy : S ≤ y) : seqDiscrepancy f y q = seqDiscrepancy f S q := by
  rcases eq_or_ne q 0 with hq | hq
  · subst hq; simp [seqDiscrepancy]
  have hsub : Finset.Icc 1 S ⊆ Finset.Icc 1 y := Finset.Icc_subset_Icc_right hSy
  have hzero : ∀ n ∈ Finset.Icc 1 y, n ∉ Finset.Icc 1 S → f n = 0 := by
    intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    exact hf n (by omega)
  have hM : (∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then f n else 0)
      = ∑ n ∈ Finset.Icc 1 S, if Nat.Coprime n q then f n else 0 := by
    refine (Finset.sum_subset hsub ?_).symm
    intro n hn hnot; rw [hzero n hn hnot]; simp
  rw [seqDiscrepancy_eq f y q hq, seqDiscrepancy_eq f S q hq]
  refine congrArg (Finset.sup' _ _) (funext fun a => ?_)
  have hR : (∑ n ∈ Finset.Icc 1 y, if n % q = a then f n else 0)
      = ∑ n ∈ Finset.Icc 1 S, if n % q = a then f n else 0 := by
    refine (Finset.sum_subset hsub ?_).symm
    intro n hn hnot; rw [hzero n hn hnot]; simp
  rw [hR, hM]

/-! ## The multiblock combinator -/

/-- **The multiblock combinator (the `hdom` heart).**  Given the amended, uniform
`GEH_min θ` and a decomposition of a weight `w`'s sequence discrepancy into `m x`
balanced dyadic blocks — all in the same coefficient/SW class `(k, j, KF)`, all
window-admissible, block count `≤ D (log x)^p` — the weight `w` satisfies the
`y`-uniform piece obligation `PieceObligationU θ w`.

The single `GEH_min` haircut/constant `(B, C)` serves EVERY block (the amendment's
`∃ B C`-before-`∀`-family uniformity); the inflated saving `A + p` absorbs the
block count: `∑_{i<m x} C x/log^{A+p} = m x · C x/log^{A+p} ≤ D C x/log^A`.

`hdecomp` is stated at the common cutoff `y` (what weight-level subadditivity
supplies); the top-block prefix overrun is rewired internally to the GEH cutoff
`min y (4 N M) ≤ 4 N M` via `seqDiscrepancy_truncate` (support from `CoeffAt`).
`hwin` is required only where used (`i < m x`, `x ≥ 3`); the `x = 2` corner is
discharged by the crude universal bound, folded into the constant. -/
theorem pieceObligationU_of_multiblock {θ ε : ℝ} (hε : 0 < ε)
    (hGEH : GEH_min θ) (w : ℕ → ℕ → ℝ)
    (k j : ℕ) (KF : ℝ → ℝ) (p D : ℝ) (hp : 0 ≤ p) (_hD : 0 ≤ D)
    (m : ℕ → ℕ) (α β : ℕ → ℕ → ℕ → ℝ) (N M : ℕ → ℕ → ℕ)
    (hα : ∀ i, CoeffAt (α i) (N i) k)
    (hβ : ∀ i, CoeffAt (β i) (M i) k)
    (hSW : ∀ i, SWAtData (β i) (M i) j KF)
    (hwin : ∀ x, 3 ≤ x → ∀ i, i < m x →
      (x : ℝ) ^ ε ≤ (N i x : ℝ) ∧ (N i x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      (x : ℝ) ^ ε ≤ (M i x : ℝ) ∧ (M i x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      N i x * M i x ≤ x ∧ x ≤ 4 * N i x * M i x)
    (hcount : ∀ x, 3 ≤ x → (m x : ℝ) ≤ D * Real.log x ^ p)
    (hdecomp : ∀ x, 3 ≤ x → ∀ y q : ℕ, y ≤ x →
      seqDiscrepancy (w x) y q
        ≤ ∑ i ∈ Finset.range (m x),
            seqDiscrepancy (dconv (α i x) (β i x)) y q) :
    PieceObligationU θ w := by
  intro A hA
  have hA' : 0 < A + p := by linarith
  obtain ⟨B, C, hB0, hbound⟩ := hGEH ε (A + p) hε hA' k j KF
  set Cpos : ℝ := max C 0 with hCpos
  have hCpos0 : 0 ≤ Cpos := le_max_right _ _
  set K2 : ℕ := ⌊(2 : ℝ) ^ θ / Real.log 2 ^ B⌋₊ with hK2
  set Cs : ℝ := 2 * ∑ n ∈ Finset.Icc 1 2, |w 2 n| with hCs
  set Ctwo : ℝ := (K2 : ℝ) * Cs * Real.log 2 ^ A / 2 with hCtwo
  refine ⟨B, max (D * Cpos) Ctwo, hB0, fun x y hx hyx => ?_⟩
  rcases lt_or_ge x 3 with hlt | hge
  · -- Small-x corner: x = 2 (crude universal bound, no GEH, no window).
    have hx2 : x = 2 := by omega
    subst hx2
    simp only [Nat.cast_ofNat]
    rw [← hK2]
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2Apos : (0 : ℝ) < Real.log 2 ^ A := Real.rpow_pos_of_pos hlog2pos A
    have hterm : ∀ q : ℕ, seqDiscrepancy (w 2) y q ≤ Cs := by
      intro q
      refine (seqDiscrepancy_le_two_mul_sum_abs (w 2) y q).trans ?_
      rw [hCs]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right hyx) (fun n _ _ => abs_nonneg _)) (by norm_num)
    have hsum2 : (∑ q ∈ Finset.Icc 1 K2, seqDiscrepancy (w 2) y q) ≤ (K2 : ℝ) * Cs := by
      refine (Finset.sum_le_sum (fun q _ => hterm q)).trans (le_of_eq ?_)
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      push_cast [Nat.add_sub_cancel]; ring
    have heq2 : (K2 : ℝ) * Cs = Ctwo * 2 / Real.log 2 ^ A := by
      rw [hCtwo]; field_simp
    rw [heq2] at hsum2
    refine hsum2.trans ?_
    exact (div_le_div_iff_of_pos_right hlog2Apos).mpr
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by norm_num))
  · -- Main regime: x ≥ 3, one (B, C) for every block.
    have hx2le : 2 ≤ x := by omega
    have hx1 : (1 : ℝ) < (x : ℝ) := by
      have : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hge
      linarith
    have hx0 : (0 : ℝ) ≤ (x : ℝ) := by linarith
    have hlogxpos : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hlogApos : (0 : ℝ) < Real.log x ^ A := Real.rpow_pos_of_pos hlogxpos A
    have hlogppos : (0 : ℝ) < Real.log x ^ p := Real.rpow_pos_of_pos hlogxpos p
    have hlogA'pos : (0 : ℝ) < Real.log x ^ (A + p) := Real.rpow_pos_of_pos hlogxpos (A + p)
    have hsplit : Real.log x ^ (A + p) = Real.log x ^ A * Real.log x ^ p :=
      Real.rpow_add hlogxpos A p
    have perBlock : ∀ i ∈ Finset.range (m x),
        (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
            seqDiscrepancy (dconv (α i x) (β i x)) y q)
          ≤ C * x / Real.log x ^ (A + p) := by
      intro i hi
      obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6⟩ := hwin x hge i (Finset.mem_range.mp hi)
      have hsupp : ∀ n, 4 * N i x * M i x < n → dconv (α i x) (β i x) n = 0 :=
        fun n hn => dconv_eq_zero_of_support (fun t ht => (hα i x t).1 ht)
          (fun t ht => (hβ i x t).1 ht) hn
      have hcut : ∀ q : ℕ, seqDiscrepancy (dconv (α i x) (β i x)) y q
          = seqDiscrepancy (dconv (α i x) (β i x)) (min y (4 * N i x * M i x)) q := by
        intro q
        rcases lt_or_ge (4 * N i x * M i x) y with hgt | hle
        · rw [min_eq_right (le_of_lt hgt)]
          exact seqDiscrepancy_truncate hsupp y q (le_of_lt hgt)
        · rw [min_eq_left hle]
      have hGEHi := hbound (α i) (β i) (N i) (M i) (hα i) (hβ i) (hSW i) x
        (min y (4 * N i x * M i x)) hx2le (min_le_right _ _) hw1 hw2 hw3 hw4 hw5 hw6
      calc (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
              seqDiscrepancy (dconv (α i x) (β i x)) y q)
          = ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
              seqDiscrepancy (dconv (α i x) (β i x)) (min y (4 * N i x * M i x)) q :=
            Finset.sum_congr rfl (fun q _ => hcut q)
        _ ≤ C * x / Real.log x ^ (A + p) := hGEHi
    calc (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊, seqDiscrepancy (w x) y q)
        ≤ ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
            ∑ i ∈ Finset.range (m x), seqDiscrepancy (dconv (α i x) (β i x)) y q :=
          Finset.sum_le_sum (fun q _ => hdecomp x hge y q hyx)
      _ = ∑ i ∈ Finset.range (m x),
            ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
              seqDiscrepancy (dconv (α i x) (β i x)) y q := Finset.sum_comm
      _ ≤ ∑ i ∈ Finset.range (m x), C * x / Real.log x ^ (A + p) :=
          Finset.sum_le_sum perBlock
      _ ≤ ∑ i ∈ Finset.range (m x), Cpos * x / Real.log x ^ (A + p) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact (div_le_div_iff_of_pos_right hlogA'pos).mpr
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0)
      _ = (m x : ℝ) * (Cpos * x / Real.log x ^ (A + p)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (D * Real.log x ^ p) * (Cpos * x / Real.log x ^ (A + p)) :=
          mul_le_mul_of_nonneg_right (hcount x hge)
            (div_nonneg (mul_nonneg hCpos0 hx0) (le_of_lt hlogA'pos))
      _ = D * Cpos * x / Real.log x ^ A := by
          rw [hsplit]; field_simp [hlogApos.ne', hlogppos.ne']
      _ ≤ max (D * Cpos) Ctwo * x / Real.log x ^ A :=
          (div_le_div_iff_of_pos_right hlogApos).mpr
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0)

/-! ## The Type-II instantiation and the assembly (`hdom` discharged) -/

/-- **The Type-II multiblock obligation (the `hdom` discharge).**  The Type-II
Vaughan piece `vP3 (cbrt x) (cbrt x)` satisfies the `y`-uniform piece obligation
at `θ = 3999/4000`, given its dyadic block data: the block families
`(α i, β i, N i, M i)` (all `CoeffAt`/`SWAtData`-admissible at one `(k, j, KF)`),
the balanced window (`ε`, at `i < m x`), the polylog block count, and the
block subadditive decomposition `hdecomp`.  This is `pieceObligationU_of_GEH_single`'s
`hdom` DISCHARGED via the real multiblock summation — no single-block idealisation.

The block data is the contract for the dyadic-decomposition supplier (the `α, β`
being `μ·1_{>U}` and `typeIIData V` dyadically restricted) and `GehSW` (the
`SWAtData` on the block-localised `typeIIData` family, `j = 1`). -/
theorem pieceObligationU_of_GEH_multiblock {ε : ℝ} (hε : 0 < ε)
    (hGEH : GEH_min (3999 / 4000))
    (k j : ℕ) (KF : ℝ → ℝ) (p D : ℝ) (hp : 0 ≤ p) (hD : 0 ≤ D)
    (m : ℕ → ℕ) (α β : ℕ → ℕ → ℕ → ℝ) (N M : ℕ → ℕ → ℕ)
    (hα : ∀ i, CoeffAt (α i) (N i) k)
    (hβ : ∀ i, CoeffAt (β i) (M i) k)
    (hSW : ∀ i, SWAtData (β i) (M i) j KF)
    (hwin : ∀ x, 3 ≤ x → ∀ i, i < m x →
      (x : ℝ) ^ ε ≤ (N i x : ℝ) ∧ (N i x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      (x : ℝ) ^ ε ≤ (M i x : ℝ) ∧ (M i x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      N i x * M i x ≤ x ∧ x ≤ 4 * N i x * M i x)
    (hcount : ∀ x, 3 ≤ x → (m x : ℝ) ≤ D * Real.log x ^ p)
    (hdecomp : ∀ x, 3 ≤ x → ∀ y q : ℕ, y ≤ x →
      seqDiscrepancy (fun n => vP3 (cbrt x) (cbrt x) n) y q
        ≤ ∑ i ∈ Finset.range (m x),
            seqDiscrepancy (dconv (α i x) (β i x)) y q) :
    PieceObligationU (3999 / 4000) (fun x n => vP3 (cbrt x) (cbrt x) n) :=
  pieceObligationU_of_multiblock hε hGEH (fun x n => vP3 (cbrt x) (cbrt x) n)
    k j KF p D hp hD m α β N M hα hβ hSW hwin hcount hdecomp

/-- **The assembly with `hdom` discharged.**  `GEH_min (3999/4000)` plus the
Type-II block data (routed through `pieceObligationU_of_GEH_multiblock`) plus the
head/Type-I piece obligations gives the `y`-uniform meeting point
`LambdaLevelU (3999/4000)` — the multiblock twin of `lambdaLevelU_of_GEH_min` with
the single-block `hdom` hypothesis REMOVED (the Type-II domination is now a
theorem, not an assumption).  Feeds `lambdaLevel_of_lambdaLevelU` → the D-N2c
π-seam → `hasLevel_of_piLevel` → the D-N3 bounded-gaps conclusion. -/
theorem lambdaLevelU_of_GEH_multiblock {ε : ℝ} (hε : 0 < ε)
    (hGEH : GEH_min (3999 / 4000))
    (k j : ℕ) (KF : ℝ → ℝ) (p D : ℝ) (hp : 0 ≤ p) (hD : 0 ≤ D)
    (m : ℕ → ℕ) (α β : ℕ → ℕ → ℕ → ℝ) (N M : ℕ → ℕ → ℕ)
    (hα : ∀ i, CoeffAt (α i) (N i) k)
    (hβ : ∀ i, CoeffAt (β i) (M i) k)
    (hSW : ∀ i, SWAtData (β i) (M i) j KF)
    (hwin : ∀ x, 3 ≤ x → ∀ i, i < m x →
      (x : ℝ) ^ ε ≤ (N i x : ℝ) ∧ (N i x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      (x : ℝ) ^ ε ≤ (M i x : ℝ) ∧ (M i x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      N i x * M i x ≤ x ∧ x ≤ 4 * N i x * M i x)
    (hcount : ∀ x, 3 ≤ x → (m x : ℝ) ≤ D * Real.log x ^ p)
    (hdecomp : ∀ x, 3 ≤ x → ∀ y q : ℕ, y ≤ x →
      seqDiscrepancy (fun n => vP3 (cbrt x) (cbrt x) n) y q
        ≤ ∑ i ∈ Finset.range (m x),
            seqDiscrepancy (dconv (α i x) (β i x)) y q)
    (hHead : PieceObligationU (3999 / 4000) (fun x n => vErr (cbrt x) (cbrt x) n))
    (hTypeI1 : PieceObligationU (3999 / 4000) (fun x n => vP1 (cbrt x) n))
    (hTypeI2 : PieceObligationU (3999 / 4000) (fun x n => vP2 (cbrt x) (cbrt x) n)) :
    LambdaLevelU (3999 / 4000) :=
  lambdaLevelU_of_pieceObligationsU hHead hTypeI1 hTypeI2
    (pieceObligationU_of_GEH_multiblock hε hGEH k j KF p D hp hD m α β N M
      hα hβ hSW hwin hcount hdecomp)

/-! ## Tail + mid composition (Type-I glue, D-N2a step 5) -/

/-- **Piece obligations add.**  If a weight `g` splits pointwise as `gt + gm` and
both summands satisfy `PieceObligationU θ`, then so does `g` (subadditivity of
`seqDiscrepancy` across the split, the two haircuts reconciled by range
monotonicity, the `x = 2` corner by the crude bound).  This is the Type-I glue:
`hTypeI1 = (elementary tail) + (multiblock mid)`, each a `PieceObligationU`, gives
the full `vP1` obligation — the tail from `GehTypeI` (when landed) and the mid
from `pieceObligationU_of_multiblock`. -/
theorem pieceObligationU_add {θ : ℝ} {g gt gm : ℕ → ℕ → ℝ}
    (hsplit : ∀ x n, g x n = gt x n + gm x n)
    (ht : PieceObligationU θ gt) (hm : PieceObligationU θ gm) :
    PieceObligationU θ g := by
  intro A hA
  obtain ⟨Bt, Ct, hBt, hbt⟩ := ht A hA
  obtain ⟨Bm, Cm, hBm, hbm⟩ := hm A hA
  set B : ℝ := max Bt Bm with hBdef
  have hBtle : Bt ≤ B := le_max_left _ _
  have hBmle : Bm ≤ B := le_max_right _ _
  have hBge0 : 0 ≤ B := le_trans hBt hBtle
  set Ksmall : ℕ := ⌊(2 : ℝ) ^ θ / Real.log 2 ^ B⌋₊ with hKs
  set Csmall : ℝ :=
    (Ksmall : ℝ) * (2 * ∑ n ∈ Finset.Icc 1 2, |g 2 n|) * Real.log 2 ^ A / 2 with hCsmall
  refine ⟨B, max (Ct + Cm) Csmall, hBge0, fun x y hx hyx => ?_⟩
  have hptwise : ∀ q, seqDiscrepancy (g x) y q
      ≤ seqDiscrepancy (gt x) y q + seqDiscrepancy (gm x) y q := by
    intro q
    have hfun : g x = (fun n => gt x n + gm x n) := by funext n; exact hsplit x n
    rw [hfun]; exact seqDiscrepancy_add_le (gt x) (gm x) y q
  rcases lt_or_ge x 3 with hlt | hge
  · have hx2 : x = 2 := by omega
    subst hx2
    simp only [Nat.cast_ofNat]
    rw [← hKs]
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2Apos : (0 : ℝ) < Real.log 2 ^ A := Real.rpow_pos_of_pos hlog2pos A
    have hterm : ∀ q : ℕ,
        seqDiscrepancy (g 2) y q ≤ 2 * ∑ n ∈ Finset.Icc 1 2, |g 2 n| := by
      intro q
      refine (seqDiscrepancy_le_two_mul_sum_abs (g 2) y q).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right hyx) (fun n _ _ => abs_nonneg _)) (by norm_num)
    have hle1 : (∑ q ∈ Finset.Icc 1 Ksmall, seqDiscrepancy (g 2) y q)
        ≤ (Ksmall : ℝ) * (2 * ∑ n ∈ Finset.Icc 1 2, |g 2 n|) := by
      refine (Finset.sum_le_sum (fun q _ => hterm q)).trans (le_of_eq ?_)
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      push_cast [Nat.add_sub_cancel]; ring
    refine hle1.trans ?_
    have hchain : (Ksmall : ℝ) * (2 * ∑ n ∈ Finset.Icc 1 2, |g 2 n|)
        = Csmall * 2 / Real.log 2 ^ A := by rw [hCsmall]; field_simp
    rw [hchain]
    exact (div_le_div_iff_of_pos_right hlog2Apos).mpr
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by norm_num))
  · have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hge
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogx1 : 1 ≤ Real.log x := by
      rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      apply Real.log_le_log (Real.exp_pos 1)
      calc Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
        _ ≤ (x : ℝ) := hxR
    have hlogxApos : (0 : ℝ) < Real.log x ^ A := Real.rpow_pos_of_pos hlogxpos A
    have hxθnn : (0 : ℝ) ≤ (x : ℝ) ^ θ := by positivity
    have mkSub : ∀ Bi : ℝ, Bi ≤ B →
        Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊
          ⊆ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ Bi⌋₊ := by
      intro Bi hBi
      apply Finset.Icc_subset_Icc_right
      apply Nat.floor_le_floor
      exact div_le_div_of_nonneg_left hxθnn (Real.rpow_pos_of_pos hlogxpos Bi)
        (Real.rpow_le_rpow_of_exponent_le hlogx1 hBi)
    have hct : (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
          seqDiscrepancy (gt x) y q) ≤ Ct * x / Real.log x ^ A :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (mkSub Bt hBtle)
        (fun q _ _ => seqDiscrepancy_nonneg _ _ _)) (hbt x y hx hyx)
    have hcm : (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
          seqDiscrepancy (gm x) y q) ≤ Cm * x / Real.log x ^ A :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (mkSub Bm hBmle)
        (fun q _ _ => seqDiscrepancy_nonneg _ _ _)) (hbm x y hx hyx)
    calc (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊, seqDiscrepancy (g x) y q)
        ≤ ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
            (seqDiscrepancy (gt x) y q + seqDiscrepancy (gm x) y q) :=
          Finset.sum_le_sum (fun q _ => hptwise q)
      _ = (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
              seqDiscrepancy (gt x) y q)
            + (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
                seqDiscrepancy (gm x) y q) := Finset.sum_add_distrib
      _ ≤ Ct * x / Real.log x ^ A + Cm * x / Real.log x ^ A := add_le_add hct hcm
      _ = (Ct + Cm) * x / Real.log x ^ A := by ring
      _ ≤ max (Ct + Cm) Csmall * x / Real.log x ^ A :=
          (div_le_div_iff_of_pos_right hlogxApos).mpr
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hxpos))
