/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetThinTS
import Salt.MR.CofactorSupply
import Salt.MR.CofactorDist
import Salt.MR.SupStation

/-!
# USetBalance — the SERIAL BALANCE (U-9b/c/d), the last work of §8.3's `hU`

The three landed branch files of `hU` are composed here into the single exit the seam row's
`hU` binder wants (`SeamBallWeighted.prop_A3_T1_row_split_weighted`):

  `(∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ Uset fb Pseq Qseq δ Jb, ‖spoly N a t‖^2) ≤ U`.

## The ladder

* **U-9b `uset_integral_to_branches`** (§2) — the composition.  The `𝒰`-integral is
  dominated by a well-spaced discrete sum (`USetThin.wellspaced_discretize`, per block
  index `j`), the eq-(16) decomposition splits `spoly` into the `Σ_{j∈I} Q_j R_j` main leg
  plus the Lemma-12 error (`USetThin.meansq_on_subset_of_decomp`), and each block sum splits
  at the level `δ'` into the two landed branches.

  **THE SPLIT IS EXHAUSTIVE, byte-wise** (§1): `TsetSmall H P Q j c ε 𝒯 =
  𝒯.filter (‖ramQ H P Q j c ·‖ ≤ ε)` (`USetThinTS`:164) and `tLset H P Q j c δ' 𝒯 =
  𝒯.filter (δ' < ‖ramQ H P Q j c ·‖)` (`USetThinTL`:184).  At `ε := δ'` — the SAME level,
  the SAME `H P Q j c`, the SAME `𝒯` — these are `filter p` and `filter ¬p` of one
  predicate, so `sum_TS_add_TL` is an identity, not an inequality.  Nothing is lost or
  double-counted at the seam of the two branches.

* **U-9c `hU_supplied` / `hU_balance`** (§4, §6–§8) — the grade arithmetic.  The `𝒯_S` exit
  is per-`j` at the SHARP co-factor length (⟦V4a⟧ finding 1: `M ≍ 2X e^{−j/H}`, never the
  dyadic `N`); the `𝒯_L` exit is per-`j` at `54·C_q·Rbd²·(H/j)²`, so the block sum needs
  `Σ_{j∈I} 1/j²` — the honest page is `sum_inv_sq_Icc_le`, `Σ_{j=j₀}^{j₁} 1/j² ≤ 1/(j₀−1)`
  by telescoping, and `j₀ = ⌊H log P⌋` is where the `1/log P` of MR p.29 actually lives.
  The exit is then fed to `USetPins.balance_exit` at `CofactorDist`'s RATIFIED `θ₂₉₃`, and
  `hU_balance_beats_door` records that it clears the door's floor `c₀ ≥ 1/500`.

* **U-9d `hU_discharged`** (§9) — the byte-fit: the row with its `hU` binder GONE.

The two feeds (§3, §5) are the landed branch exits re-shaped for §2's `∀ 𝒯 ⊆ A` binder:
`USetThinTS.uset_TS_branch_meanvalue` and `CofactorSupply.tL_supply_discharged` (⟦V5d⟧'s
prize — the co-factor-free form, so the `𝒯_L` branch carries NO `Rbd` hypothesis).

## The gates that ride the exit in-statement (law #253, ⟦V4⟧'s law)

`TannGate X Tann` (`USetPins`:320) is carried by the exit — a polylog `Tann` makes the
whole thinness row vacuous (`TannGate_fails_polylog_deg`), so dropping it is unsound, not
merely weaker.  Alongside it: the `α`-gate at `η′ := η/2` (⟦V4a⟧ finding 2 — the honest
Lemma-8 exponent is `α = α_J + log K₀/log P_J`, NOT `α_J`), the `hκ30` block gates, the kill
gate, the collision tower `X₁`, the descent gate, and MR Step 0's `T ≤ X`.

## What is NOT here

The row's `𝒯`-leg (§8.1+§8.2, MR's `Σ_j E_j` — a separate unscoped block, ⟦V4⟧'s map
correction), the far arm of the A-10 cap, and `hSup` (closed at `SupStation`).

Source pins (D5): MR arXiv v4 (`1501.04585v4`) pp. 19–20, 27–29 (§8.3);
`docs/exploration/hsup-design.md` ⟦V4⟧/⟦V4a⟧/⟦V4b⟧/⟦V5⟧/⟦V5d⟧.
-/

namespace Salt.MR

open scoped BigOperators
open Finset MeasureTheory

/-! ## §1 — the `𝒯_S ∥ 𝒯_L` split is EXHAUSTIVE -/

/-- **`𝒯_L` is the complement filter of `𝒯_S`.**  `tLset` filters `δ' < ‖ramQ‖`;
`TsetSmall` at the SAME level filters `‖ramQ‖ ≤ δ'`.  `not_le` is the whole content — the
byte-check that the two branch files split one predicate and not two. -/
lemma tLset_eq_filter_not (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (δ' : ℝ) (𝒯 : Finset ℝ) :
    tLset H P Q j c δ' 𝒯 = 𝒯.filter (fun t => ¬ (‖ramQ H P Q j c t‖ ≤ δ')) := by
  classical
  ext t
  simp only [tLset, Finset.mem_filter, not_le]

/-- **The exhaustive split of a block sum.**  An IDENTITY: the `𝒯_S` and `𝒯_L` branches of
a well-spaced `𝒯` partition it, so no mass is lost or double-counted between the two landed
exits. -/
lemma sum_TS_add_TL (H : ℝ) (N Xd P Q j : ℕ) (b c : ℕ → ℂ) (δ' : ℝ) (𝒯 : Finset ℝ) :
    (∑ t ∈ TsetSmall H P Q j c δ' 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2)
      + (∑ t ∈ tLset H P Q j c δ' 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2)
      = ∑ t ∈ 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2 := by
  classical
  rw [tLset_eq_filter_not, TsetSmall]
  exact Finset.sum_filter_add_sum_filter_not 𝒯 _ _

/-! ## §2 — U-9b: the `𝒰` integral → the two branch exits -/

/-- **U-9b — THE COMPOSITION** (`uset_integral_to_branches`).  For a measurable
`A ⊆ [−T,T]` (the consumer's `(Ann ∖ ball) ∩ 𝒰`), with per-block branch bounds `Sb j`, `Lb j`
valid for EVERY well-spaced `𝒯 ⊆ A` (which is the shape the discretisation needs — the
witness set is produced inside the proof, one per block index):

  `∫_A ‖spoly N a‖² ≤ 4·|I|·Σ_{j∈I} (Sb j + Lb j) + 2E`.

The three factors, honestly: `2·|I|` is the eq-(16) Cauchy–Schwarz across blocks
(`meansq_on_subset_of_decomp`), the extra `2` is the even/odd parity halving of the
well-spaced discretisation (`wellspaced_discretize`), and `E` is Lemma 12's full-range error
row, carried as a parameter (the consumer plugs `lemma12_meansq_on_subset`'s). -/
theorem uset_integral_to_branches
    (H : ℝ) (N Xd P Q : ℕ) (a b c : ℕ → ℂ) (T E : ℝ) (hT : 0 ≤ T)
    (herr : (∫ t in (-T)..T, ‖ramErr H N Xd P Q a b c t‖ ^ 2) ≤ E)
    (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T)
    (δ' : ℝ) (Sb Lb : ℕ → ℝ)
    (hTS : ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 → (↑𝒯 : Set ℝ) ⊆ A →
      (∑ t ∈ TsetSmall H P Q j c δ' 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2) ≤ Sb j)
    (hTL : ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 → (↑𝒯 : Set ℝ) ⊆ A →
      (∑ t ∈ tLset H P Q j c δ' 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2) ≤ Lb j) :
    (∫ t in A, ‖spoly N a t‖ ^ 2)
      ≤ 4 * ((ramI H P Q).card : ℝ) * (∑ j ∈ ramI H P Q, (Sb j + Lb j)) + 2 * E := by
  classical
  -- (i) eq (16): the block decomposition on `A`
  have hstep1 := meansq_on_subset_of_decomp (N := N) (a := a) (I := ramI H P Q)
    (mainPoly := ramMain H N Xd P Q b c) (errPoly := ramErr H N Xd P Q a b c)
    (E := E) (T := T) (A := A) hT hAm hAsub
    (fun j _ => continuous_ramMain H N Xd P Q b c j) (continuous_ramErr H N Xd P Q a b c)
    (fun t => spoly_ram_decomp H N Xd P Q a b c t) herr
  -- (ii) per block: discretise, then split the well-spaced sum at `δ'`
  have hper : ∀ j ∈ ramI H P Q,
      (∫ t in A, ‖ramMain H N Xd P Q b c j t‖ ^ 2) ≤ 2 * (Sb j + Lb j) := by
    intro j hj
    obtain ⟨𝒯, h𝒯A, hws, hle⟩ := wellspaced_discretize T
      (fun t => ‖ramMain H N Xd P Q b c j t‖ ^ 2)
      ((continuous_ramMain H N Xd P Q b c j).norm.pow 2)
      (fun t => by positivity) A hAm hAsub
    refine hle.trans ?_
    have hsplit := sum_TS_add_TL H N Xd P Q j b c δ' 𝒯
    have h1 := hTS j hj 𝒯 hws h𝒯A
    have h2 := hTL j hj 𝒯 hws h𝒯A
    rw [← hsplit]
    linarith
  have hsum : (∑ j ∈ ramI H P Q, ∫ t in A, ‖ramMain H N Xd P Q b c j t‖ ^ 2)
      ≤ 2 * ∑ j ∈ ramI H P Q, (Sb j + Lb j) := by
    refine le_trans (Finset.sum_le_sum hper) ?_
    rw [← Finset.mul_sum]
  have hcard0 : (0 : ℝ) ≤ 2 * ((ramI H P Q).card : ℝ) := by positivity
  calc (∫ t in A, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in A, ‖ramMain H N Xd P Q b c j t‖ ^ 2) + 2 * E := hstep1
    _ ≤ 2 * ((ramI H P Q).card : ℝ) * (2 * ∑ j ∈ ramI H P Q, (Sb j + Lb j)) + 2 * E := by
        have := mul_le_mul_of_nonneg_left hsum hcard0
        linarith
    _ = 4 * ((ramI H P Q).card : ℝ) * (∑ j ∈ ramI H P Q, (Sb j + Lb j)) + 2 * E := by ring

/-! ## §3 — the `𝒯_S` feed: the landed U-5 exit in the `∀ 𝒯 ⊆ A` shape -/

/-- **The `𝒯_S` branch bound, uniformly over the well-spaced witnesses.**  `U-5`'s exit
(`uset_TS_branch_meanvalue`) is already `𝒯`-uniform — every gate it carries is either
`t`-free or supplied by `𝒯 ⊆ A ⊆ [−T,T] ∩ 𝒰` — so the feed is one `intro`.

⟦V4a⟧ finding 1 (THE SHARP `M`) is in-statement: the length `Ms j` is a per-block parameter
with `ramRrange H N Xd j ⊆ [1, Ms j]`; the consumer must feed the CO-FACTOR length
`≍ 2·Xd·e^{−j/H}`, never the dyadic `N` (that costs a factor `e^{j/H}`).
⟦V4a⟧ finding 2 (THE `α` GATE) is in-statement too: `hVα : log V ≤ α·log P_Jb` with
`α ≤ 1/4 − η`; at the pin `δ := P_J^{−α_J}`, `V := K₀/δ` the honest `α` is
`α_J + log K₀/log P_J`, discharged by taking `η′ := η/2`. -/
theorem TS_feed_of_thin
    (fb : ℕ → ℂ) (hfb1 : ∀ n : ℕ, ‖fb n‖ ≤ 1) (Pseq Qseq : ℕ → ℕ) (δ : ℝ)
    (Jset Jb : ℕ) (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ Jset) (hδ0 : 0 < δ)
    (T V : ℝ) (hT : 1 < T) (hV : 1 ≤ V)
    (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log (Qseq Jb)) (hLL5 : 5 ≤ Real.log (Real.log T))
    (α η X : ℝ) (hVα : Real.log V ≤ α * Real.log (Pseq Jb)) (hα : α ≤ 1 / 4 - η)
    (hη2 : 2 * η ≤ 1) (hTX : T ≤ X)
    (Rset : Set ℝ) (hRsub : Rset ⊆ Set.Icc (-T) T)
    (H : ℝ) (N Xd P Q : ℕ) (b c : ℕ → ℂ) (δ' : ℝ) (Ms : ℕ → ℕ)
    (hM : ∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j))
    (hbudget : ∀ j ∈ ramI H P Q,
      thinBundle T V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) :
    ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 →
      (↑𝒯 : Set ℝ) ⊆ Rset ∩ Uset fb Pseq Qseq δ Jset →
      (∑ t ∈ TsetSmall H P Q j c δ' 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2)
        ≤ 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * T))
            * ∑ m ∈ Finset.Icc 1 (Ms j), ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  intro j hj 𝒯 hws hsubA
  exact uset_TS_branch_meanvalue fb hfb1 Pseq Qseq δ Jset Jb hJb1 hJbJ hδ0 T V hT hV hVinv
    hP3 hQT hκ30 hLL5 𝒯 hws (fun t ht => hRsub (hsubA (Finset.mem_coe.mpr ht)).1)
    (fun t ht => (hsubA (Finset.mem_coe.mpr ht)).2) α η X hVα hα hη2 hTX
    H N Xd P Q j (Ms j) b c δ' (hM j hj) (hbudget j hj)

/-! ## §4 — the `j`-sum page: `Σ_{j∈I} 1/j²` -/

/-- **The telescoped block sum, with the endpoint kept.**  `Σ_{j=j₀}^{j₁} 1/j² ≤
1/(j₀−1) − 1/j₁` for `2 ≤ j₀ ≤ j₁`: the step is `1/(m+1)² ≤ 1/m − 1/(m+1)`. -/
lemma sum_inv_sq_Icc_le_sub (j₀ : ℕ) (hj₀ : 2 ≤ j₀) :
    ∀ j₁ : ℕ, j₀ ≤ j₁ →
      ∑ j ∈ Finset.Icc j₀ j₁, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 1 / ((j₀ : ℝ) - 1) - 1 / (j₁ : ℝ) := by
  intro j₁
  induction j₁ with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rcases Nat.lt_or_ge n j₀ with hn | hn
    · have hj0n : j₀ = n + 1 := by omega
      subst hj0n
      rw [Finset.Icc_self, Finset.sum_singleton]
      have hnR : (2 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hj₀
      have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
      have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      rw [div_sub_div _ _ (by linarith : ((n : ℝ) + 1 - 1) ≠ 0)
        (by linarith : ((n : ℝ) + 1) ≠ 0)]
      rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
      ring_nf
      nlinarith [hn0]
    · have hstep := ih hn
      have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      have hj0n : (2 : ℝ) ≤ (j₀ : ℝ) := by exact_mod_cast hj₀
      have hnj : (j₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
      rw [Finset.sum_Icc_succ_top (by omega), hcast]
      have hkey : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        rw [div_sub_div _ _ (by linarith : (n : ℝ) ≠ 0) (by linarith : ((n : ℝ) + 1) ≠ 0)]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        ring_nf
        nlinarith [hn0]
      linarith

/-- **THE `j`-SUM PAGE** (`sum_inv_sq_Icc_le`).  `Σ_{j∈[j₀,j₁]} 1/j² ≤ 1/(j₀−1)` for
`2 ≤ j₀`.  This is the honest weight of the `𝒯_L` block sum: `U-8`'s exit is per-`j` at
`54·C·Rbd²·(H/j)²`, so the `j`-sum contributes `H²/(j₀−1)` with `j₀ = ⌊H log P⌋` — MR
p.29's `1/log P`, in the only form the kernel will sign. -/
lemma sum_inv_sq_Icc_le (j₀ j₁ : ℕ) (hj₀ : 2 ≤ j₀) :
    ∑ j ∈ Finset.Icc j₀ j₁, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 1 / ((j₀ : ℝ) - 1) := by
  have hj0R : (2 : ℝ) ≤ (j₀ : ℝ) := by exact_mod_cast hj₀
  rcases Nat.lt_or_ge j₁ j₀ with h | h
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    have hpos : (0 : ℝ) < (j₀ : ℝ) - 1 := by linarith
    exact le_of_lt (div_pos one_pos hpos)
  · have hstep := sum_inv_sq_Icc_le_sub j₀ hj₀ j₁ h
    have hj1 : (0 : ℝ) < (j₁ : ℝ) := by
      have : (2 : ℝ) ≤ (j₁ : ℝ) := le_trans hj0R (by exact_mod_cast h)
      linarith
    have : (0 : ℝ) ≤ 1 / (j₁ : ℝ) := by positivity
    linarith

/-! ## §5 — the `𝒯_L` feed: the landed U-7/U-8 exit in the `∀ 𝒯 ⊆ A` shape -/

/-- **THE PER-BLOCK `𝒯_L` GATE BUNDLE** — the enumerated union of U-8's window gates (the
block base, the `X₀` law `hκ30`, the kill gate) and U-7's co-factor gates (the descent
anchor `k₀`, the sharp co-factor length `M`, the loglog gate, the `Rbd` endpoint) at block
index `j`.  Everything that grows with `X` is a named expression (law #253); nothing is
absorbed into a numeral.

Note that U-7's `M` (`ramRbot − 1 ≤ M ≤ 2(ramRbot − 1)`, `2·ramRbot < M + 3`) and U-5's `Ms`
(`ramRrange ⊆ [1, Ms]`, so `Ms ≥ ⌊2·ramRbot⌋`) are DIFFERENT roundings of the same
co-factor length and are kept as separate parameters — identifying them would be a false
byte-fit. -/
def TLBlockGates (cq X₀ H : ℝ) (P N Xn : ℕ) (Mt kk : ℕ → ℕ) (T L cg Cb Xg θ Dmax Rrad : ℝ)
    (j : ℕ) : Prop :=
  H ≤ (j : ℝ) ∧ 3 ≤ ramQbase H P j ∧ (ramQbase H P j : ℝ) ≤ T ∧
  30 ≤ Real.log T / Real.log (ramQbase H P j) ∧
  Real.log (ramQbase H P j) ≤ L ∧
  420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (ramQbase H P j)) ^ 2 ∧
  X₀ ≤ ((kk j : ℕ) : ℝ) ∧ Real.exp 64 ≤ ((kk j : ℕ) : ℝ) ∧
  ballMertensThreshold ≤ ((kk j : ℕ) : ℝ) ∧
  Mt j ≤ N ∧ ((kk j : ℕ) : ℝ) < ramRbot H Xn j ∧ ramRbot H Xn j ≤ ((kk j : ℕ) : ℝ) + 1 ∧
  1 < ramRbot H Xn j ∧ ramRbot H Xn j - 1 ≤ ((Mt j : ℕ) : ℝ) ∧
  ((Mt j : ℕ) : ℝ) ≤ 2 * (ramRbot H Xn j - 1) ∧ 2 * ramRbot H Xn j < ((Mt j : ℕ) : ℝ) + 3 ∧
  ((Mt j : ℕ) : ℝ) ≤ Xg ∧
  (1 / 32 - θ) * Real.log (Real.log Xg) ≤ (1 / 16) * Real.log (Real.log ((kk j : ℕ) : ℝ)) ∧
  0 ≤ cofactorMfl Xg θ ((kk j : ℕ) : ℝ) ∧
  2 / ramRbot H Xn j
    ≤ cofactorRbd cg Cb Xg θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ) (Dmax + 1) Rrad / 3

/-- **The `𝒯_L` branch bound, uniformly over the well-spaced witnesses** — `⟦V5d⟧`'s prize
`CofactorSupply.tL_supply_discharged` (NOT `tL_main_sumsq`: the co-factor supply is already
discharged, so no `Rbd` hypothesis survives) re-shaped for the `U-9b` composition.

The only per-`t` input is the geometric bundle `hgeo`, stated on the AMBIENT set `Rset` (the
row's far leg `(Ann ∖ ball)`) rather than on the internally-produced `𝒯`: the far radius
`Rrad ≤ |t − t₁| ≤ Dmax` is exactly what removing the ball buys, and the contour box
`|t| + T*(k, log k) ≤ 3X` is a property of the annulus. -/
theorem TL_feed_of_supply :
    ∃ Cq cq T₀ X₀ C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (H : ℝ), 2 ≤ H → ∀ (P Q N Xn : ℕ) (Mt kk : ℕ → ℕ) (cf : ℕ → ℂ),
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (T V L δ' : ℝ), T₀ ≤ T → 1 < T → 5 ≤ Real.log (Real.log T) → 1 ≤ V → V⁻¹ ≤ δ' →
        Real.log T ≤ L → 1 ≤ Real.log T → Real.exp 1 ≤ L → Real.log V ≤ 100 * Real.log L →
      ∀ (cg Cb Xg θ t₁ Dmax Rrad : ℝ),
        0 < cg → cg ≤ 1 / Real.exp 1 → 2 * cg < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        Real.exp 1 ≤ Xg → Real.exp 1 ≤ Real.log Xg → 0 < θ → θ ≤ 1 / 32 →
        P83 Xg θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 Xg → P ≤ Q → |t₁| ≤ Xg →
        pretDistSq (ellLin g) (costwist t₁) Xg ≤ (1 / 16) * Real.log (Real.log Xg) →
        collisionGate Xg 25 C → 0 < Rrad →
      ∀ (Rset : Set ℝ), Rset ⊆ Set.Icc (-T) T →
      ∀ j : ℕ, TLBlockGates cq X₀ H P N Xn Mt kk T L cg Cb Xg θ Dmax Rrad j →
        (∀ t ∈ Rset, Rrad ≤ |t - t₁| ∧ |t - t₁| ≤ Dmax ∧
          ∀ k : ℕ, kk j ≤ k → k ≤ Mt j → |t| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ 3 * Xg) →
      ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 → (↑𝒯 : Set ℝ) ⊆ Rset →
        (∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N Xn P Q (ellLin g) cf j t‖ ^ 2)
          ≤ 54 * Cq * cofactorRbd cg Cb Xg θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
              (Dmax + 1) Rrad ^ 2 * (H / (j : ℝ)) ^ 2 := by
  obtain ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, hmain⟩ := tL_supply_discharged
  refine ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, ?_⟩
  intro g hg H hH P Q N Xn Mt kk cf hcf1 T V L δ' hT₀T hT hLL5 hV1 hVδ hTL hlogT1 hLe hlogV
    cg Cb Xg θ t₁ Dmax Rrad hc0 hce hc1 hCb0 hCbound hX hLX hθ0 hθ32 hPlow hQhigh hPQ ht₁
    hrow hgate hR0 Rset hRsub j hblk hgeo 𝒯 hws h𝒯R
  obtain ⟨hHj, hB3, hBT, hκ30, hWL, hkill, hX₀k, hk₀64, hk₀th, hMN, hk₀lo, hk₀hi, hbot,
    hlow, hhigh, hMtop, hMX, hll, hMfl0, hend⟩ := hblk
  exact hmain g hg H hH P Q j N Xn (Mt j) (kk j) cf hcf1 hHj T V L δ' 𝒯 hws
    (fun t ht => hRsub (h𝒯R (Finset.mem_coe.mpr ht))) hT₀T hT hB3 hBT hκ30 hLL5 hV1 hVδ
    hTL hlogT1 hLe hWL hlogV hkill cg Cb Xg θ t₁ Dmax Rrad hc0 hce hc1 hCb0 hCbound hX₀k
    hk₀64 hk₀th hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hMX hll hX hLX hθ0 hθ32 hPlow hQhigh
    hPQ ht₁ hrow hgate hR0 hMfl0 hend
    (fun t ht => hgeo t (h𝒯R (Finset.mem_coe.mpr (tLset_subset H P Q j cf δ' 𝒯 ht))))

/-! ## §6 — U-9c: the block sum, and the explicit exit `U` -/

/-- **U-9c (the honest `j`-sum page).**  The `𝒯_S` branch is bounded uniformly over blocks
by `KS` (the mean-value grade at the sharp co-factor length — `M·Σ_m 1/m² ≍ 1`, so nothing
in it grows with `j`); the `𝒯_L` branch is `54·C_q·Rbd²·(H/j)²`, whose block sum is the
`Σ 1/j²` telescope.  `j₀ = ⌊H log P⌋` is `ramI`'s lower endpoint, so the `𝒯_L` weight is
`H²/(⌊H log P⌋ − 1)` — the `H/log P` of MR p.29, with the honest floor. -/
theorem block_sum_bound (H : ℝ) (P Q : ℕ) (Sb Lb : ℕ → ℝ) (KS Cq Rbar : ℝ)
    (hKS : ∀ j ∈ ramI H P Q, Sb j ≤ KS) (hCq : 0 ≤ Cq)
    (hLbj : ∀ j ∈ ramI H P Q, Lb j ≤ 54 * Cq * Rbar ^ 2 * H ^ 2 * (1 / (j : ℝ) ^ 2))
    (hj₀ : 2 ≤ ⌊H * Real.log P⌋₊) :
    ∑ j ∈ ramI H P Q, (Sb j + Lb j)
      ≤ ((ramI H P Q).card : ℝ) * KS
        + 54 * Cq * Rbar ^ 2 * H ^ 2 / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1) := by
  have hS : ∑ j ∈ ramI H P Q, Sb j ≤ ((ramI H P Q).card : ℝ) * KS := by
    have h := Finset.sum_le_sum hKS
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  have hcoef0 : (0 : ℝ) ≤ 54 * Cq * Rbar ^ 2 * H ^ 2 := by positivity
  have hL : ∑ j ∈ ramI H P Q, Lb j
      ≤ 54 * Cq * Rbar ^ 2 * H ^ 2 / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1) := by
    refine le_trans (Finset.sum_le_sum hLbj) ?_
    rw [← Finset.mul_sum]
    have hsum : ∑ j ∈ ramI H P Q, (1 : ℝ) / (j : ℝ) ^ 2
        ≤ 1 / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1) := by
      rw [ramI]
      exact sum_inv_sq_Icc_le _ _ hj₀
    calc 54 * Cq * Rbar ^ 2 * H ^ 2 * ∑ j ∈ ramI H P Q, (1 : ℝ) / (j : ℝ) ^ 2
        ≤ 54 * Cq * Rbar ^ 2 * H ^ 2 * (1 / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left hsum hcoef0
      _ = 54 * Cq * Rbar ^ 2 * H ^ 2 / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1) := by ring
  rw [Finset.sum_add_distrib]
  linarith

/-- **U-9c (the exit `U`, explicit).**  `U-9b`'s composition at the branch bounds of §3/§5:

  `∫_{(Ann∖ball)∩𝒰} ‖spoly‖² ≤ 4|I|·(|I|·KS + 54·C_q·R̄²·H²/(⌊H log P⌋−1)) + 2E`.

Every factor is an expression: `|I|` the block count, `KS` the `𝒯_S` mean-value grade, `R̄`
the uniform co-factor bound, `E` Lemma 12's error row.  This is the `U` the row's `hU`
binder takes. -/
theorem hU_exit_of_branches
    (H : ℝ) (N Xd P Q : ℕ) (a b c : ℕ → ℂ) (T E : ℝ) (hT : 0 ≤ T)
    (herr : (∫ t in (-T)..T, ‖ramErr H N Xd P Q a b c t‖ ^ 2) ≤ E)
    (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T)
    (δ' : ℝ) (Sb Lb : ℕ → ℝ) (KS Cq Rbar : ℝ) (hCq : 0 ≤ Cq)
    (hj₀ : 2 ≤ ⌊H * Real.log (P : ℝ)⌋₊)
    (hTS : ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 → (↑𝒯 : Set ℝ) ⊆ A →
      (∑ t ∈ TsetSmall H P Q j c δ' 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2) ≤ Sb j)
    (hTL : ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 → (↑𝒯 : Set ℝ) ⊆ A →
      (∑ t ∈ tLset H P Q j c δ' 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2) ≤ Lb j)
    (hKS : ∀ j ∈ ramI H P Q, Sb j ≤ KS)
    (hLbj : ∀ j ∈ ramI H P Q, Lb j ≤ 54 * Cq * Rbar ^ 2 * H ^ 2 * (1 / (j : ℝ) ^ 2)) :
    (∫ t in A, ‖spoly N a t‖ ^ 2)
      ≤ 4 * ((ramI H P Q).card : ℝ)
          * (((ramI H P Q).card : ℝ) * KS
              + 54 * Cq * Rbar ^ 2 * H ^ 2 / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E := by
  have hcomp := uset_integral_to_branches H N Xd P Q a b c T E hT herr A hAm hAsub δ' Sb Lb
    hTS hTL
  have hblk := block_sum_bound H P Q Sb Lb KS Cq Rbar hKS hCq hLbj hj₀
  have hcard0 : (0 : ℝ) ≤ 4 * ((ramI H P Q).card : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hblk hcard0
  linarith

/-- The `𝒯_L` block weight in the shape `block_sum_bound` consumes: `(H/j)² = H²·(1/j²)`,
and the per-block co-factor bound is majorised by the uniform `R̄`. -/
lemma tL_block_weight (Cq H r Rbar : ℝ) (j : ℕ) (hCq : 0 ≤ Cq) (hr0 : 0 ≤ r)
    (hr : r ≤ Rbar) :
    54 * Cq * r ^ 2 * (H / (j : ℝ)) ^ 2 ≤ 54 * Cq * Rbar ^ 2 * H ^ 2 * (1 / (j : ℝ) ^ 2) := by
  have hsq : r ^ 2 ≤ Rbar ^ 2 := by nlinarith
  have hform : (H / (j : ℝ)) ^ 2 = H ^ 2 * (1 / (j : ℝ) ^ 2) := by rw [div_pow]; ring
  have hcoef : (0 : ℝ) ≤ 54 * Cq * (H ^ 2 * (1 / (j : ℝ) ^ 2)) := by positivity
  rw [hform]
  calc 54 * Cq * r ^ 2 * (H ^ 2 * (1 / (j : ℝ) ^ 2))
      = 54 * Cq * (H ^ 2 * (1 / (j : ℝ) ^ 2)) * r ^ 2 := by ring
    _ ≤ 54 * Cq * (H ^ 2 * (1 / (j : ℝ) ^ 2)) * Rbar ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hcoef
    _ = 54 * Cq * Rbar ^ 2 * H ^ 2 * (1 / (j : ℝ) ^ 2) := by ring

/-! ## §7 — U-9b/c: `hU` SUPPLIED (the enumerated union → the explicit `U`) -/

/-- **U-9b/c — THE `hU` SUPPLY** (`hU_supplied`).  The seam row's `𝒰` integral, bounded by
the composition of §2 fed by the two landed branch exits of §3 and §5:

  `∫_{(Ann∖ball)∩𝒰} ‖spoly N a‖²
      ≤ 4|I|·(|I|·KS + 54·C_q·R̄²·H²/(⌊H log P⌋−1)) + 2E`.

**THE `Tann` GATE RIDES IN-STATEMENT** (⟦V4⟧'s law): `TannGate X Tann` is not decoration —
it is what supplies `Uset_thin`'s `hκ30` at the `J`-block, through
`USetPins.kappa30_of_TannGate` at the pin `log Q_Jb ≤ (log X)^{1/2}`.  A polylog `Tann`
refuses the gate (`TannGate_fails_polylog_deg`), and with it the whole thinness row.

The other gates, enumerated: MR Step 0 (`Tann ≤ X`); the `𝒰`-thinness level data
(`0 < δ`, `1 ≤ V`, `V⁻¹ ≤ δ/K₀`, `V⁻¹ ≤ δ'`, `3 ≤ P_Jb`, `Q_Jb ≤ Tann`, `loglog Tann ≥ 5`);
the `α`-gate at `η′` (`log V ≤ α log P_Jb`, `α ≤ 1/4 − η`, `2η ≤ 1` — ⟦V4a⟧ finding 2, the
`K₀`-inflation absorbed by `η′ := η/2`); the sharp co-factor length `Ms` with its budget
(⟦V4a⟧ finding 1); U-7's `t`-free gates (the `c`-generic window `cg ≤ 1/e`, the
short-interval datum, the `P83/Q83` pins, the ball datum, the collision gate at the `X₁`
tower); the per-block bundle `TLBlockGates` (the block base, the `X₀` law `hκ30`, the kill
gate, the descent anchor `k₀`, the `Rbd` endpoint); the contour box; and the two stated
grade budgets `KS`, `R̄`.

The far-leg geometry is DERIVED, not assumed: `Rrad ≤ seamRad X` plus `t ∉ ball` gives
CASE B's radius input, which is exactly what the row's ball removal buys. -/
theorem hU_supplied :
    ∃ Cq cq T₀ X₀ C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
      ∀ (g fb a cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖fb n‖ ≤ 1) →
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq Ms Mt kk : ℕ → ℕ),
      ∀ (X Tann t₁ δ δ' V L α η cg Cb θ Dmax Rrad KS Rbar E : ℝ),
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        1 < (Qseq Jb : ℝ) → Real.log (Qseq Jb) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        0 < δ → 1 ≤ Jb → Jb ≤ Jset → 1 ≤ V →
        V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ) → V⁻¹ ≤ δ' →
        3 ≤ Pseq Jb → (Qseq Jb : ℝ) ≤ Tann →
        Real.log V ≤ α * Real.log (Pseq Jb) → α ≤ 1 / 4 - η → 2 * η ≤ 1 →
        Real.log V ≤ 100 * Real.log L →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q, thinBundle Tann V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        0 < cg → cg ≤ 1 / Real.exp 1 → 2 * cg < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        0 < θ → θ ≤ 1 / 32 → P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 C → 0 < Rrad → Rrad ≤ seamRad X → Tann + |t₁| ≤ Dmax →
        (∀ j ∈ ramI H P Q, TLBlockGates cq X₀ H P N Xd Mt kk Tann L cg Cb X θ Dmax Rrad j) →
        (∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
          ∀ k : ℕ, kk j ≤ k → k ≤ Mt j → |t| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ 3 * X) →
        (∀ j ∈ ramI H P Q, 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
            * (∑ m ∈ Finset.Icc 1 (Ms j),
                ‖ramRcoeff H N Xd P Q j (ellLin g) m‖ ^ 2 / (m : ℝ) ^ 2) ≤ KS) →
        (∀ j ∈ ramI H P Q,
          cofactorRbd cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ) (Dmax + 1) Rrad ≤ Rbar) →
        2 ≤ ⌊H * Real.log (P : ℝ)⌋₊ →
        (∫ t in (-Tann)..Tann, ‖ramErr H N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ Uset fb Pseq Qseq δ Jset,
            ‖spoly N a t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (((ramI H P Q).card : ℝ) * KS
                  + 54 * Cq * Rbar ^ 2 * H ^ 2
                      / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E := by
  obtain ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, hTLfeed⟩ := TL_feed_of_supply
  refine ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, ?_⟩
  intro g fb a cf hg hfb1 hcf1 H hH N Xd P Q Jset Jb Pseq Qseq Ms Mt kk
    X Tann t₁ δ δ' V L α η cg Cb θ Dmax Rrad KS Rbar E
    hX0 hXe hLXe hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hδ0 hJb1 hJbJ hV1 hVinv hVδ hP3 hQT hVα hα hη2 hlogV hMs hbudget
    hc0 hce hc1 hCb0 hCbound hθ0 hθ32 hPlow hQhigh hPQ ht₁ hrow hcoll hR0 hRrad hDmax
    hblk hbox hKS hRbdU hj₀ herr
  have hTann0 : (0 : ℝ) ≤ Tann := by linarith
  have hκ30 : 30 ≤ Real.log Tann / Real.log (Qseq Jb) :=
    kappa30_of_TannGate X Tann (Qseq Jb) hQ1 hQpin hTgate
  have hRm : MeasurableSet (seamAnn X Tann \ seamBall X t₁) :=
    (measurableSet_seamAnn X Tann).diff (measurableSet_seamBall X t₁)
  have hAm : MeasurableSet ((seamAnn X Tann \ seamBall X t₁) ∩ Uset fb Pseq Qseq δ Jset) :=
    hRm.inter (measurableSet_Uset fb Pseq Qseq δ Jset)
  have hRsub : (seamAnn X Tann \ seamBall X t₁) ⊆ Set.Icc (-Tann) Tann :=
    fun _ ht => seamAnn_subset_Icc X Tann ht.1
  have hAsub : ((seamAnn X Tann \ seamBall X t₁) ∩ Uset fb Pseq Qseq δ Jset)
      ⊆ Set.Icc (-Tann) Tann := fun _ ht => hRsub ht.1
  -- the `𝒯_S` feed (U-5)
  have hTSfeed := TS_feed_of_thin fb hfb1 Pseq Qseq δ Jset Jb hJb1 hJbJ hδ0 Tann V hT1 hV1
    hVinv hP3 hQT hκ30 hLL5 α η X hVα hα hη2 hTX
    (seamAnn X Tann \ seamBall X t₁) hRsub H N Xd P Q (ellLin g) cf δ' Ms hMs hbudget
  -- the `𝒯_L` feed (U-7 ∘ U-8), with the far-leg geometry DERIVED from the ball removal
  have hTLj : ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 →
      (↑𝒯 : Set ℝ) ⊆ (seamAnn X Tann \ seamBall X t₁) ∩ Uset fb Pseq Qseq δ Jset →
      (∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N Xd P Q (ellLin g) cf j t‖ ^ 2)
        ≤ 54 * Cq * cofactorRbd cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
            (Dmax + 1) Rrad ^ 2 * (H / (j : ℝ)) ^ 2 := by
    intro j hj 𝒯 hws h𝒯A
    refine hTLfeed g hg H hH P Q N Xd Mt kk cf hcf1 Tann V L δ' hT₀T hT1 hLL5 hV1 hVδ hTLle
      hlogT1 hLe hlogV cg Cb X θ t₁ Dmax Rrad hc0 hce hc1 hCb0 hCbound hXe hLXe hθ0 hθ32
      hPlow hQhigh hPQ ht₁ hrow hcoll hR0 (seamAnn X Tann \ seamBall X t₁) hRsub j
      (hblk j hj) ?_ 𝒯 hws (fun x hx => (h𝒯A hx).1)
    intro t ht
    have hTabs : |t| ≤ Tann := ht.1.2
    have hnot : ¬ (|t - t₁| ≤ seamRad X) := ht.2
    refine ⟨le_trans hRrad (le_of_lt (not_le.mp hnot)), ?_, hbox j hj t hTabs⟩
    have habs : |t - t₁| ≤ |t| + |t₁| := by
      calc |t - t₁| = |t + -t₁| := by rw [sub_eq_add_neg]
        _ ≤ |t| + |-t₁| := abs_add_le _ _
        _ = |t| + |t₁| := by rw [abs_neg]
    linarith
  refine hU_exit_of_branches H N Xd P Q a (ellLin g) cf Tann E hTann0 herr
    ((seamAnn X Tann \ seamBall X t₁) ∩ Uset fb Pseq Qseq δ Jset) hAm hAsub δ'
    (fun j => 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
      * ∑ m ∈ Finset.Icc 1 (Ms j), ‖ramRcoeff H N Xd P Q j (ellLin g) m‖ ^ 2 / (m : ℝ) ^ 2)
    (fun j => 54 * Cq * cofactorRbd cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
      (Dmax + 1) Rrad ^ 2 * (H / (j : ℝ)) ^ 2)
    KS Cq Rbar (le_of_lt hCq) hj₀ (fun j hj 𝒯 hws h𝒯A => hTSfeed j hj 𝒯 hws h𝒯A) hTLj hKS ?_
  intro j hj
  have hk64 := (hblk j hj).2.2.2.2.2.2.2.1
  have h65 : (65 : ℝ) ≤ ((kk j : ℕ) : ℝ) := by
    linarith [Real.add_one_le_exp (64 : ℝ), hk64]
  have hk1 : (1 : ℝ) ≤ ((kk j : ℕ) : ℝ) := by linarith
  exact tL_block_weight Cq H _ Rbar j (le_of_lt hCq)
    (cofactorRbd_nonneg hc1 hCb0 hk1) (hRbdU j hj)

/-! ## §8 — U-9c: the balance at the RATIFIED pin `θ₂₉₃` -/

/-- **U-9c — THE BALANCE** (`hU_balance`).  The `θ = ρ/3` pin collapses §8.3's two legs into
one: with the block leg at `(log X)^{5θ−2ρ}` and the Lemma-12 error leg at
`(T/X+1)(log X)^{−θ+ε}`, the exit is

  `U ≤ 2·(T/X+1)·(log X)^{−θ₂₉₃+ε}`,   `θ₂₉₃ = 1/(32(3e+1)) ≈ 1/293`.

The pin is `CofactorDist.theta293` (⟦V5⟧'s ρ-amendment, RATIFIED) — `θ₂₉₃ = ρ₂₉₃/3` is
exactly `USetPins.theta83 ρ₂₉₃`, so `balance_exit` applies verbatim.  The door's floor is
cleared with margin `1.7067×` (`exit_margin_293` / `exit_margin_293_sharp`), and any `o(1)`
with `ε ≤ 1/1000` still clears it (`exit_beats_c0_293`).

`TannGate X Tann` rides here too, and works: it is what makes `Tann` positive, hence
`0 ≤ Tann/X` — the only nonnegativity `balance_exit` needs. -/
theorem hU_balance (X Tann ε Umain Urem Uint : ℝ) (hε : 0 ≤ ε) (hL : 1 ≤ Real.log X)
    (hX0 : 0 < X) (hTgate : TannGate X Tann)
    (hUint : Uint ≤ Umain + Urem)
    (hmain : Umain ≤ (Real.log X) ^ (5 * theta293 - 2 * rho293))
    (hrem : Urem ≤ (Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) :
    Uint ≤ 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  have hTann0 : (0 : ℝ) < Tann := lt_of_lt_of_le (Real.exp_pos _) hTgate
  have hTX : (0 : ℝ) ≤ Tann / X := le_of_lt (div_pos hTann0 hX0)
  have hth : theta83 rho293 = theta293 := by
    rw [theta83]; exact theta293_eq_rho_div_three.symm
  have hmain' : Umain ≤ (Real.log X) ^ (5 * theta83 rho293 - 2 * rho293) := by rwa [hth]
  have hrem' : Urem ≤ (Tann / X + 1) * (Real.log X) ^ (-theta83 rho293 + ε) := by rwa [hth]
  have h := balance_exit X Tann rho293 ε Umain Urem hε hL hTX hmain' hrem'
  rw [hth] at h
  linarith

/-- **The balanced exit CLEARS THE DOOR.**  At any `o(1)` with `ε ≤ 1/1000` the exponent
`−θ₂₉₃ + ε` is at most `−1/500`, so

  `U ≤ 2·(T/X+1)·(log X)^{−1/500}`,

which is the door's floor `c₀ ≥ 1/500` — cleared with the ratified margin `1.7067×`
(`exit_margin_293`: `1.706/500 ≤ θ₂₉₃`; `exit_margin_293_sharp`: `θ₂₉₃ < 1.707/500`). -/
theorem hU_balance_beats_door (X Tann ε Uint : ℝ) (hε : ε ≤ 1 / 1000)
    (hL : 1 ≤ Real.log X) (hX0 : 0 < X) (hTgate : TannGate X Tann)
    (hUint : Uint ≤ 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε))) :
    Uint ≤ 2 * ((Tann / X + 1) * (Real.log X) ^ (-(1 : ℝ) / 500)) := by
  have hTann0 : (0 : ℝ) < Tann := lt_of_lt_of_le (Real.exp_pos _) hTgate
  have hTX : (0 : ℝ) ≤ Tann / X := le_of_lt (div_pos hTann0 hX0)
  have hexp : -theta293 + ε ≤ -(1 : ℝ) / 500 := by
    have h := exit_beats_c0_293 ε hε
    linarith
  have hstep : (Real.log X) ^ (-theta293 + ε) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) :=
    Real.rpow_le_rpow_of_exponent_le hL hexp
  have hmul : (Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)
      ≤ (Tann / X + 1) * (Real.log X) ^ (-(1 : ℝ) / 500) :=
    mul_le_mul_of_nonneg_left hstep (by linarith)
  linarith

/-! ## §9 — U-9d: the row with `hU` GONE -/

/-- **U-9d — `hU` DISCHARGED** (`hU_discharged`).  `SeamBallWeighted.prop_A3_T1_row_split_
weighted` with its second binder supplied by §7: the seam row now carries only the ball leg,
the `𝒯`-leg (§8.1+§8.2, out of scope) and the EXPLICIT `U`.  The compile is the certificate
that §7's exit byte-fits the row's `hU` slot — the set
`(seamAnn X Tann ∖ seamBall X t₁) ∩ Uset fb Pseq Qseq δ Jset`, the integrand
`‖spoly N a t‖^2`, and the direction of the inequality are the row's, verbatim.

The plug-point is `prop_A3_T1_row_split_weighted` (`SeamBallWeighted`:248) rather than
`prop_A3_T1_row_station` (`SupStation`:782): the station's extra content is a PRODUCED `t₁`
(a near-minimiser it manufactures), whereas §7's exit needs `t₁` as a FREE parameter (the
far-leg radius `Rrad ≤ |t − t₁|` and the ball datum `pretDistSq … (costwist t₁)` are stated
about the same `t₁` the `𝒰` integral is centred on).  Composing with the station is a
one-line consumer step once its `t₁` is in hand; forcing it here would fix `t₁` before the
`𝒰` side has said anything about it. -/
theorem hU_discharged :
    ∃ Cq cq T₀ X₀ C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
      ∀ (g fb a cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖fb n‖ ≤ 1) →
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq Ms Mt kk : ℕ → ℕ),
      ∀ (X Tann t₁ δ δ' V L α η cg Cb θ Dmax Rrad KS Rbar E S : ℝ),
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        1 < (Qseq Jb : ℝ) → Real.log (Qseq Jb) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        0 < δ → 1 ≤ Jb → Jb ≤ Jset → 1 ≤ V →
        V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ) → V⁻¹ ≤ δ' →
        3 ≤ Pseq Jb → (Qseq Jb : ℝ) ≤ Tann →
        Real.log V ≤ α * Real.log (Pseq Jb) → α ≤ 1 / 4 - η → 2 * η ≤ 1 →
        Real.log V ≤ 100 * Real.log L →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q, thinBundle Tann V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        0 < cg → cg ≤ 1 / Real.exp 1 → 2 * cg < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        0 < θ → θ ≤ 1 / 32 → P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 C → 0 < Rrad → Rrad ≤ seamRad X → Tann + |t₁| ≤ Dmax →
        (∀ j ∈ ramI H P Q, TLBlockGates cq X₀ H P N Xd Mt kk Tann L cg Cb X θ Dmax Rrad j) →
        (∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
          ∀ k : ℕ, kk j ≤ k → k ≤ Mt j → |t| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ 3 * X) →
        (∀ j ∈ ramI H P Q, 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
            * (∑ m ∈ Finset.Icc 1 (Ms j),
                ‖ramRcoeff H N Xd P Q j (ellLin g) m‖ ^ 2 / (m : ℝ) ^ 2) ≤ KS) →
        (∀ j ∈ ramI H P Q,
          cofactorRbd cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ) (Dmax + 1) Rrad ≤ Rbar) →
        2 ≤ ⌊H * Real.log (P : ℝ)⌋₊ →
        (∫ t in (-Tann)..Tann, ‖ramErr H N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        -- the row's own frame (`SeamBallWeighted`:248), `hU` ABSENT
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ seamTtot fb Pseq Qseq δ Jset,
                ‖spoly N a t‖ ^ 2)
            + (4 * ((ramI H P Q).card : ℝ)
                * (((ramI H P Q).card : ℝ) * KS
                    + 54 * Cq * Rbar ^ 2 * H ^ 2
                        / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E) := by
  obtain ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, hsup⟩ := hU_supplied
  refine ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, ?_⟩
  intro g fb a cf hg hfb1 hcf1 H hH N Xd P Q Jset Jb Pseq Qseq Ms Mt kk
    X Tann t₁ δ δ' V L α η cg Cb θ Dmax Rrad KS Rbar E S
    hX0 hXe hLXe hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hδ0 hJb1 hJbJ hV1 hVinv hVδ hP3 hQT hVα hα hη2 hlogV hMs hbudget
    hc0 hce hc1 hCb0 hCbound hθ0 hθ32 hPlow hQhigh hPQ ht₁ hrow hcoll hR0 hRrad hDmax
    hblk hbox hKS hRbdU hj₀ herr hXN hN2 hsupp hSup
  have hU := hsup g fb a cf hg hfb1 hcf1 H hH N Xd P Q Jset Jb Pseq Qseq Ms Mt kk
    X Tann t₁ δ δ' V L α η cg Cb θ Dmax Rrad KS Rbar E
    hX0 hXe hLXe hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hδ0 hJb1 hJbJ hV1 hVinv hVδ hP3 hQT hVα hα hη2 hlogV hMs hbudget
    hc0 hce hc1 hCb0 hCbound hθ0 hθ32 hPlow hQhigh hPQ ht₁ hrow hcoll hR0 hRrad hDmax
    hblk hbox hKS hRbdU hj₀ herr
  have hLX : (0 : ℝ) ≤ Real.log X := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  exact prop_A3_T1_row_split_weighted a N fb Pseq Qseq δ Jset X Tann t₁ S _ hLX
    (by linarith) hX0 hXN hN2 hsupp hSup hU

end Salt.MR
