/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RamareMR
import Salt.MR.SeamNumber
import Salt.MR.ThmA2Spine

/-!
# `SeamRowWindowed` — the WINDOW-RELATIVIZED coefficient contract

Freeze: `docs/exploration/s8-freeze-0727.md` ⟦AMENDMENT F⟧ (CONTRACT-TWIN).

`ThmA2Spine.seam_coef_contract_absurd` proves that `SeamNumber.seam_row_number`'s Lemma-12
binders close to `False` at a live S8 datum: the *unconditional* factorization

  `hcoef : ∀ p m, p prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p*m) = b m * c p`

together with (R6) `a n ≠ 0 → X_d ≤ n ≤ 2X_d` forces `c` to vanish at every band prime that
carries a live cofactor off the window, hence `a ≡ 0` on all coprime band multiples.  This
file lands the maestro-ruled repair: the relativized contract, the certificate that it is
satisfiable exactly where the landed one is not, and **the Lemma-12 row at the relativized
pair** — `lemma12_meansq_mr_windowed` and its two consumption forms.

Everything is additive; `seam_row_number` and the `RamareMR` chain are byte-untouched
(iron rule 1).

## §1 — W-1: the relativized binder pair, and why `hwin` is DROPPED not relativized

`SeamCoefW` puts the window INSIDE the antecedent:

  `∀ p m, p prime → P ≤ p → p ≤ Q → ¬ p ∣ m → X_d ≤ pm → pm ≤ 2X_d → a (p*m) = b m * c p`.

Relativizing `hwin` would be **vacuous**: `hwin` says `c p · b m ≠ 0 → X_d ≤ pm ≤ 2X_d`, and
putting `X_d ≤ pm ≤ 2X_d` in its antecedent makes it `True`.  `hwin` is a *joint support*
statement about `(b,c)` — `supp(c)·supp(b) ⊆ [X_d,2X_d]` — and it is as unsatisfiable at the
datum as `hcoef` is: at the natural instantiation `c = F`, `b = F` for the multiplicative `F`
underlying `a = 1_{[X_d,2X_d]}·F` one has `c p · b m = F(p)F(m) ≠ 0` for a vast set of
off-window `pm` (take `m = 1`).  So the honest pair is `SeamCoefW` **alone**, beside the
`1`-bounds and (R6).

`seamCoefW_of_global` records the direction that makes the twin ADDITIVE: the landed binder
implies the relativized one, so every model of the landed contract is a model of the twin's.

## §2 — the use-site map, and where the twin actually lands

`seam_row_number` (`SeamNumber`:98) feeds the pair to two consumers —
`SeamCalibrationK.seam_row_calibratedK` takes both binders,
`TypicalPriceK.sum_lemma12Rows_priced_calibratedK2` takes `hwin`.  At the leaves:

* `hwin` (1) `RamareErr.ramWindowErr_eq_seamPoly`:201, through `seam_sum_identity`:107;
* `hwin` (2) `TypicalPrice.ramP2_term_norm_le_win`:245, through `ramP2mass_direct`
  (`SeamCalibrationK`:678) into `TypicalPriceK.lemma12Rows_pricedK`:84;
* `hcoef` (3) `RamareWindows.spoly_ramare_split`, through `RamareErr.ramErr_moment_split`:667;
* row 3 of `lemma12Rows` (`TypicalDensity.blockfree_sum_le`) uses `hasupp`/`‖a‖ ≤ 1` only —
  contract-free.

All three have ONE root cause, named in `RamareErr`'s own R5 header: `RamareWindows`' clean
term sums the cofactor `m` over `{m : pm ∈ [1,N]}` — the *full* range, the dyadic window
having been folded into `a` — instead of MR's own `{m : X ≤ pm ≤ 2X}` (`RamareErr.ramHonMR`).

**`RamareMR` has already re-derived Lemma 12 at MR's range and retired `hwin` outright**
(`lemma12_meansq_mr`, 2026-07-25): the seam identity becomes the coefficient-free
`RamareErr.seam_sum_identity_mr`, MR's SECOND seam window `[2X, 2Xe^{1/H}]` is paid honestly
as a fourth row (`ramSeamUpPoly_moment`, `≤ (2T+80X)(4eX/H+1)/(2X)²`, with the `4×` saving
from `1/n² ≤ 1/(2X)²`), the `p²` row moves inside `[X,2X]`, and the Cauchy–Schwarz prefactor
goes `3 → 4`.  **The second-window price the freeze asked for is therefore already banked**;
`seam_rows_grade` collapses both seams to `520·(T/X + 1)/H` — MR's own grade.

What `RamareMR` did NOT do is relativize `hcoef`: `lemma12_meansq_mr` still takes it globally,
so it is still unsatisfiable at the S8 datum.  Its single use is
`spoly_ramare_split_mr`:598 — inside a `Finset.sum_congr` over `ramHonMR N X p`, i.e. **only
at cofactors with `X ≤ pm ≤ 2X`**.  §3 below is exactly that: the split, the four-row
`ramErr` identity, and the three mean-square exits, re-cut at `SeamCoefW`.  The one changed
line is the congr binder (`fun m _` → `fun m hm`, reading the window out of `hm`).

## §3 — W-2, as far as one file reaches

`lemma12_meansq_mr_windowed` IS the seam row at the relativized pair; it is `W-2` at the
layer where the contract lives.  The full `seam_row_number_windowed` needs one more thing,
and it is a LADDER REWIRE, not a proof: `TLegExit.lemma12Rows` (:91) transcribes
`RamareErr.lemma12_meansq_sharp`'s THREE rows at prefactor `2·(3·…)`, and the whole
`TLegExit → SeamCalibrationK → TypicalPriceK → SeamNumber` ladder is priced against that
shape.  The `RamareMR` row is four rows at `2·(4·…)`.  So the delta on
`seam_row_number`'s right-hand side, in-statement (law #253), is:

* the second seam window enters as the new fourth row, `≤ 2 ×` the first
  (`second_window_le_first_row`), and
* every row inflates by `4/3` from the prefactor;

a single safe cover for both: **multiply `seam_row_number`'s
`480·(T_ann/X_d + 1)·(Σ_j … + C·(2/M))` summand by `4`**.  Nothing else in the row moves —
the `hSup`, `𝒰`-side and level-1 terms never see the contract.

W-4 (`CapFreeArm.seam_row_number_capfree`:1154) carries the identical binder pair through the
identical ladder, so it inherits this file's §1/§2 verbatim and the same rewire residual; no
separate design is needed.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) p.20 (Lemma 12's proof, both `d_m` rows),
§8.2 p.27; `docs/exploration/s8-freeze-0727.md` ⟦AMENDMENT F⟧; `RamareErr` R5; `RamareMR`.
-/

noncomputable section

namespace Salt.MR

open Finset Complex MeasureTheory
open scoped BigOperators

/-! ## §1 — W-1: the window-relativized coefficient contract -/

/-- **W-1 — THE RELATIVIZED FACTORIZATION** (`SeamCoefW`).  `seam_row_number`'s `hcoef` with
the dyadic window moved INSIDE the antecedent: the Lemma-12 factorization is asserted only at
those coprime band factorizations `n = pm` that the coefficient `a` can actually see.

This is the exact shape the S8 datum satisfies: `a = 1_{[X_d,2X_d]}·F` with `F` multiplicative
gives `a (pm) = F(pm) = F(m)F(p) = b m · c p` **on the window** and `0` off it, while the
global form asserts the on-window value everywhere and is refuted
(`ThmA2Spine.seam_coef_contract_absurd`). -/
def SeamCoefW (Xd P Q : ℕ) (a b c : ℕ → ℂ) : Prop :=
  ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m →
    (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
      a (p * m) = b m * c p

/-- The K-ladder's levelled form — `seam_row_number`'s `hcoef` binder, relativized level by
level. -/
def SeamCoefWLevels (A G M Jb Xd : ℕ) (a b c : ℕ → ℂ) : Prop :=
  ∀ j ∈ Finset.Icc 1 Jb, SeamCoefW Xd (calP A G j) (calQK A G M j) a b c

/-- **THE TWIN IS ADDITIVE** (iron rule 1).  The landed global binder implies the relativized
one, so `SeamCoefW` is strictly weaker and every model of `seam_row_number`'s contract is a
model of the twin's. -/
theorem seamCoefW_of_global {Xd P Q : ℕ} {a b c : ℕ → ℂ}
    (hcoef : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p) :
    SeamCoefW Xd P Q a b c :=
  fun p m hp hP hQ hd _ _ => hcoef p m hp hP hQ hd

/-- The levelled form of `seamCoefW_of_global`. -/
theorem seamCoefWLevels_of_global {A G M Jb Xd : ℕ} {a b c : ℕ → ℂ}
    (hcoef : ∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p →
      p ≤ calQK A G M j → ¬ p ∣ m → a (p * m) = b m * c p) :
    SeamCoefWLevels A G M Jb Xd a b c :=
  fun j hj => seamCoefW_of_global (hcoef j hj)

/-! ## §2 — W-3: the satisfiability certificate -/

/-- **The S8 coefficient shape**: a multiplicative `F` cut to the dyadic window `[X_d, 2X_d]`.
This is `1_{(X_d,2X_d]}·g_𝒥·f` in the freeze's glyphs, with the window written closed (the
half-open convention is immaterial to the contract). -/
def winCut (Xd : ℕ) (F : ℕ → ℂ) : ℕ → ℂ :=
  fun n => if Xd ≤ n ∧ n ≤ 2 * Xd then F n else 0

/-- `winCut` satisfies (R6) — its support is the dyadic window, by construction. -/
theorem winCut_supp (Xd : ℕ) (F : ℕ → ℂ) {n : ℕ} (h : winCut Xd F n ≠ 0) :
    Xd ≤ n ∧ n ≤ 2 * Xd := by
  by_contra hc
  exact h (by simp only [winCut, if_neg hc])

/-- (R6) in the real-valued shape `RamareMR`'s `hasupp` binder takes. -/
theorem winCut_supp_real (Xd : ℕ) (F : ℕ → ℂ) {n : ℕ} (h : winCut Xd F n ≠ 0) :
    (Xd : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (Xd : ℝ) := by
  obtain ⟨h1, h2⟩ := winCut_supp Xd F h
  refine ⟨by exact_mod_cast h1, ?_⟩
  have : ((n : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at this
  linarith

/-- `winCut` inherits the `1`-bound (R5). -/
theorem norm_winCut_le (Xd : ℕ) {F : ℕ → ℂ} (hF : ∀ n, ‖F n‖ ≤ 1) (n : ℕ) :
    ‖winCut Xd F n‖ ≤ 1 := by
  simp only [winCut]
  split_ifs with h
  · exact hF n
  · simp

/-- `winCut` is the value of `F` inside the window. -/
theorem winCut_of_mem {Xd n : ℕ} (F : ℕ → ℂ) (h1 : Xd ≤ n) (h2 : n ≤ 2 * Xd) :
    winCut Xd F n = F n := by
  simp only [winCut]
  rw [if_pos ⟨h1, h2⟩]

/-- **W-3 (the general certificate) — THE NATURAL INSTANTIATION SATISFIES THE TWIN.**
For any `F` with the coprime-multiplicativity `F(pm) = F(m)F(p)` — i.e. exactly the
`g_𝒥·f` of the S8 datum — the triple

  `a := 1_{[X_d,2X_d]}·F`,  `b := F`,  `c := F`

satisfies the relativized contract at EVERY band, with no gate on `X_d`, `P`, `Q`.

This is what the landed pair provably cannot do: at this same `a` no `(b,c)` whatever
satisfies the global `hcoef` once the band is wide enough to push a live cofactor off the
window (`ThmA2Spine.seam_coef_contract_absurd`; made unconditional at a concrete datum in
`seam_coef_contract_windowed_sat` below). -/
theorem seamCoefW_winCut {Xd P Q : ℕ} {F : ℕ → ℂ}
    (hmul : ∀ p m : ℕ, p.Prime → ¬ p ∣ m → F (p * m) = F m * F p) :
    SeamCoefW Xd P Q (winCut Xd F) F F := by
  intro p m hp _ _ hd hlo hhi
  have h1 : Xd ≤ p * m := by
    have h : (Xd : ℝ) ≤ ((p * m : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  have h2 : p * m ≤ 2 * Xd := by
    have h : ((p * m : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  rw [winCut_of_mem F h1 h2]
  exact hmul p m hp hd

/-- **W-3 — THE CERTIFICATE, UNCONDITIONAL.**  At the concrete live datum
`X_d = 10`, band `[P,Q] = [2,7]`, `a = 1_{[10,20]}`, `b = c = 1`:

* the **relativized** contract holds, with the `1`-bounds and (R6), and `a` is live at a
  coprime band factorization (`14 = 2·7`);
* the **landed** contract is refuted for EVERY pair `(b',c')` — not merely for this one.

The refutation is `ThmA2Spine.seam_coef_contract_absurd` read at `p₀ = 2, m₀ = 7`
(live: `14 ∈ [10,20]`), `p₁ = 3` (off-window: `21 > 20`), `m₁ = 5` (live: `15 ∈ [10,20]`) —
the band `[2,7]` is wider than a factor `2`, which every calibrated band is.  So the twin's
binder pair is not a repair of taste: it is the difference between a satisfiable contract and
an empty one. -/
theorem seam_coef_contract_windowed_sat :
    ∃ (Xd P Q : ℕ) (a b c : ℕ → ℂ),
      (∀ n, ‖a n‖ ≤ 1) ∧ (∀ n, ‖b n‖ ≤ 1) ∧ (∀ n, ‖c n‖ ≤ 1) ∧
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) ∧
      SeamCoefW Xd P Q a b c ∧
      (∃ p m : ℕ, p.Prime ∧ P ≤ p ∧ p ≤ Q ∧ ¬ p ∣ m ∧ a (p * m) ≠ 0) ∧
      (∀ b' c' : ℕ → ℂ,
        ¬ (∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b' m * c' p)) := by
  classical
  refine ⟨10, 2, 7, winCut 10 (fun _ => (1 : ℂ)), (fun _ => (1 : ℂ)), (fun _ => (1 : ℂ)),
    norm_winCut_le 10 (fun _ => by norm_num), (fun _ => by norm_num), (fun _ => by norm_num),
    (fun _ hn => winCut_supp 10 _ hn),
    seamCoefW_winCut (fun _ _ _ _ => by norm_num), ?_, ?_⟩
  · refine ⟨2, 7, by norm_num, le_rfl, by norm_num, by decide, ?_⟩
    rw [show (2 : ℕ) * 7 = 14 from rfl, winCut_of_mem _ (by norm_num) (by norm_num)]
    norm_num
  · intro b' c' hcoef
    refine seam_coef_contract_absurd (a := winCut 10 (fun _ => (1 : ℂ))) (b := b') (c := c')
      (Xd := 10) (fun _ hn => winCut_supp 10 _ hn) hcoef
      (p₀ := 2) (p₁ := 3) (m₀ := 7) (m₁ := 5)
      (by norm_num) le_rfl (by norm_num) (by decide) ?_
      (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num) (by decide) ?_
    · rw [show (2 : ℕ) * 7 = 14 from rfl, winCut_of_mem _ (by norm_num) (by norm_num)]
      norm_num
    · rw [show (3 : ℕ) * 5 = 15 from rfl, winCut_of_mem _ (by norm_num) (by norm_num)]
      norm_num

/-! ## §3 — W-2: the Lemma-12 row at the relativized pair -/

/-- **THE PATCHED SPLIT** (`spoly_ramare_split_mr_windowed`).  `RamareMR.spoly_ramare_split_mr`
with `hcoef` replaced by `SeamCoefW`.

The proof is that theorem's, with ONE line changed: the final `Finset.sum_congr` runs over
`ramHonMR N X p = {m ∈ [1,N] : X ≤ pm ≤ 2X}`, so its membership hypothesis — discarded in the
original as `fun m _` — is precisely the window antecedent `SeamCoefW` asks for.  Nothing else
in the split ever reads the factorization: this is the whole content of "the relativized pair
suffices once the cofactor range is MR's own". -/
theorem spoly_ramare_split_mr_windowed (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N)
    (a b c : ℕ → ℂ) (hcoefW : SeamCoefW X P Q a b c)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (t : ℝ) :
    spoly N a t
      = ramCleanMR N X P Q b c t + ramP2corrMR N X P Q a b c t + ramCopTail N P Q a t := by
  classical
  have hper : ∀ p ∈ (Finset.Icc P Q).filter Nat.Prime,
      (∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
          (fun m => p * m ∈ Finset.Icc 1 N),
        ramareWeight P Q p m •
          (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)))
        = (∑ m ∈ ramHonMR N X p,
            (b m * c p / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
              * ((blockOmega P Q m : ℂ) + 1)⁻¹)
          + ∑ m ∈ (ramHonMR N X p).filter (fun m => p ∣ m),
              (ramareWeight P Q p m •
                  (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
                - (b m * c p / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
                    * ((blockOmega P Q m : ℂ) + 1)⁻¹) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hPp, hpQ⟩, hpp⟩ := hp
    have hrestrict : (∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
          (fun m => p * m ∈ Finset.Icc 1 N),
        ramareWeight P Q p m *
          (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)))
        = ∑ m ∈ ramHonMR N X p,
          ramareWeight P Q p m *
            (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
      refine (Finset.sum_subset (ramHonMR_subset N X p hX hN hpp.pos) (fun m hm hmn => ?_)).symm
      have ha : a (p * m) = 0 := by
        by_contra h
        obtain ⟨h1, h2⟩ := hasupp _ h
        rw [mem_honest_cofactor hpp.pos] at hm
        refine hmn ?_
        rw [ramHonMR, Finset.mem_filter, Finset.mem_Icc]
        push_cast at h1 h2
        refine ⟨⟨?_, ?_⟩, h1, h2⟩
        · rcases Nat.eq_zero_or_pos m with rfl | hm0
          · simp at hm
          · exact hm0
        · exact le_trans (Nat.le_mul_of_pos_left m hpp.pos) hm.2
      rw [ha]
      simp
    simp only [Complex.real_smul] at hrestrict ⊢
    rw [hrestrict, Finset.sum_filter (fun m => p ∣ m), ← Finset.sum_add_distrib]
    -- ⟦THE ONE CHANGED LINE⟧ the congr's own membership IS the window antecedent
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [ramHonMR, Finset.mem_filter] at hm
    obtain ⟨-, hlo, hhi⟩ := hm
    by_cases hpm : p ∣ m
    · rw [if_pos hpm]; ring
    · rw [if_neg hpm, add_zero, hcoefW p m hpp hPp hpQ hpm hlo hhi,
        ramareWeight_coprime P Q p m (hpp.coprime_iff_not_dvd.mpr hpm)]
      push_cast
      ring
  have hmain : (∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
      ∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
          (fun m => p * m ∈ Finset.Icc 1 N),
        ramareWeight P Q p m •
          (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)))
      = ramCleanMR N X P Q b c t + ramP2corrMR N X P Q a b c t := by
    rw [ramCleanMR, ramP2corrMR, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hper
  rw [spoly_ramare_eq16 N a P Q t, hmain, ramCopTail]

/-- **The four-row `ramErr` identity at the relativized pair** — `RamareMR.ramErr_decomp_mr`
with `SeamCoefW` in place of `hcoef`.  The two seam-row halves (`cleanMR_dyadic`,
`cleanMR_dyadic_sub_main`) are coefficient-free and are cited, not re-derived. -/
theorem ramErr_decomp_mr_windowed (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hP : 1 ≤ P) (a b c : ℕ → ℂ) (hcoefW : SeamCoefW X P Q a b c)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (t : ℝ) :
    ramErr H N X P Q a b c t
      = ramSeamLoPoly H N X P Q b c t - ramSeamUpPoly H N X P Q b c t
        + ramP2corrMR N X P Q a b c t + ramCopTail N P Q a t := by
  have hH0 : (0 : ℝ) < H := by linarith
  rw [ramErr, spoly_ramare_split_mr_windowed N X P Q hX hN a b c hcoefW hasupp t,
    cleanMR_dyadic H hH0 N X P Q hP b c t, ← cleanMR_dyadic_sub_main H hH N X P Q hX b c t]
  abel

/-- **The four-row error split at the relativized pair.** -/
theorem ramErr_moment_split_mr_windowed (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hP : 1 ≤ P) (a b c : ℕ → ℂ) (hcoefW : SeamCoefW X P Q a b c)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramErr H N X P Q a b c t‖ ^ 2)
      ≤ 4 * ((∫ t in (-T)..T, ‖ramSeamLoPoly H N X P Q b c t‖ ^ 2)
          + (∫ t in (-T)..T, ‖ramSeamUpPoly H N X P Q b c t‖ ^ 2)
          + (∫ t in (-T)..T, ‖ramP2corrMR N X P Q a b c t‖ ^ 2)
          + (∫ t in (-T)..T, ‖ramCopTail N P Q a t‖ ^ 2)) := by
  have hneg : (∫ t in (-T)..T, ‖-ramSeamUpPoly H N X P Q b c t‖ ^ 2)
      = ∫ t in (-T)..T, ‖ramSeamUpPoly H N X P Q b c t‖ ^ 2 :=
    intervalIntegral.integral_congr (fun t _ => by rw [norm_neg])
  have h := moment_split4 (f := ramErr H N X P Q a b c)
    (g₁ := ramSeamLoPoly H N X P Q b c) (g₂ := fun t => -ramSeamUpPoly H N X P Q b c t)
    (g₃ := ramP2corrMR N X P Q a b c) (g₄ := ramCopTail N P Q a)
    (continuous_ramErr H N X P Q a b c) (continuous_ramSeamLoPoly H N X P Q b c)
    (continuous_ramSeamUpPoly H N X P Q b c).neg (continuous_ramP2corrMR N X P Q a b c)
    (continuous_ramCopTail N P Q a)
    (fun t => by
      rw [ramErr_decomp_mr_windowed H hH N X P Q hX hN hP a b c hcoefW hasupp t]; ring) T hT
  rw [hneg] at h
  exact h

/-- **W-2 — LEMMA 12'S MEAN SQUARE AT THE RELATIVIZED PAIR** (`lemma12_meansq_mr_windowed`).

`RamareMR.lemma12_meansq_mr` with the global `hcoef` replaced by `SeamCoefW`.  Both of
`seam_row_number`'s contract binders are now gone in the honest direction: `hwin` was retired
by `RamareMR` (paying MR p.20's second seam window as the explicit fourth row
`(2T + 80X)·(4e·X/H + 1)/(2X)²`), and `hcoef` is relativized here.

What remains on the coefficient side is exactly what the S8 datum supplies and
`seam_coef_contract_windowed_sat` certifies satisfiable: `‖b‖, ‖c‖ ≤ 1`, MR's dyadic support
`hasupp`, and the on-window factorization.  Nothing in this statement is weaker than
`lemma12_meansq_mr`'s — the right-hand side is byte-identical. -/
theorem lemma12_meansq_mr_windowed (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hP : 1 ≤ P) (a b c : ℕ → ℂ) (hcoefW : SeamCoefW X P Q a b c)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in (-T)..T, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + 2 * (4 * ((2 * T + 20 * (N : ℝ))
                  * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2)
              + (2 * T + 80 * (X : ℝ))
                  * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2)
              + (2 * T + 20 * (N : ℝ))
                  * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
              + (2 * T + 20 * (N : ℝ))
                  * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
                      ‖a n‖ ^ 2 / (n : ℝ) ^ 2)) := by
  refine lemma12_meansq_of_windowErr H N X P Q a b c T _ hT ?_
  refine (ramErr_moment_split_mr_windowed H hH N X P Q hX hN hP a b c hcoefW hasupp T hT).trans ?_
  gcongr
  · exact ramSeamLoPoly_moment H hH N X P Q hX hN hP b c hb hc T hT
  · exact ramSeamUpPoly_moment H hH N X P Q hX hP b c hb hc T hT
  · exact ramP2corrMR_moment N X P Q hX hN a b c T
  · exact ramCopTail_moment N P Q a T

/-- **W-2 (exit) — the tail-free form at the relativized pair.**  Under the §8.3 support pin
the coprime-tail row vanishes identically; three rows remain. -/
theorem lemma12_meansq_mr_blockSupport_windowed (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hP : 1 ≤ P) (a b c : ℕ → ℂ) (hcoefW : SeamCoefW X P Q a b c)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (hsupp : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P Q n)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in (-T)..T, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + 2 * (4 * ((2 * T + 20 * (N : ℝ))
                  * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2)
              + (2 * T + 80 * (X : ℝ))
                  * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2)
              + (2 * T + 20 * (N : ℝ))
                  * ∑ n ∈ Finset.Icc 1 N,
                      ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)) := by
  refine lemma12_meansq_of_windowErr H N X P Q a b c T _ hT ?_
  refine (ramErr_moment_split_mr_windowed H hH N X P Q hX hN hP a b c hcoefW hasupp T hT).trans ?_
  have h1 := ramSeamLoPoly_moment H hH N X P Q hX hN hP b c hb hc T hT
  have h2 := ramSeamUpPoly_moment H hH N X P Q hX hP b c hb hc T hT
  have h3 := ramP2corrMR_moment N X P Q hX hN a b c T
  have h4 := ramCopTail_moment_zero N P Q a hsupp T
  rw [h4]
  linarith

/-- **W-2 (consumption) — the `(T/X + 1)/H` form at the relativized pair.**  The two seam rows
collapse to `520·(T/X + 1)/H` (`RamareMR.seam_rows_grade`) — MR's own grade, both windows
included — and the `p²` mass stays in-statement.  This is the `[−T,T]` shape the `U-1`
consumer takes; it is `RamareMR.lemma12_meansq_mr_consume` with a contract that a live S8
datum can actually meet. -/
theorem lemma12_meansq_mr_consume_windowed (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hN2 : (N : ℝ) ≤ 2 * (X : ℝ)) (hHX : H ≤ (X : ℝ)) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ) (hcoefW : SeamCoefW X P Q a b c)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (hsupp : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P Q n)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in (-T)..T, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + 4160 * (T / (X : ℝ) + 1) / H
        + 8 * (2 * T + 20 * (N : ℝ))
            * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 := by
  refine (lemma12_meansq_mr_blockSupport_windowed H hH N X P Q hX hN hP a b c hcoefW hb hc
    hasupp hsupp T hT).trans ?_
  have hg := seam_rows_grade H hH N X hX hN2 hHX T hT
  have hbridge : (4160 : ℝ) * (T / (X : ℝ) + 1) / H = 8 * (520 * (T / (X : ℝ) + 1) / H) := by
    ring
  rw [hbridge]
  linarith

/-! ## §4 — the ladder delta, as a number -/

/-- **THE SECOND WINDOW'S SIZE, AGAINST THE FIRST** (`second_window_le_first_row`).  MR p.20's
overcount row — the one `SeamNumber`'s `hwin` was zeroing by fiat, paid honestly by
`RamareMR.ramSeamUpPoly_moment` — is at most TWICE the undercount row, in the raw shape
`TLegExit.lemma12Rows` carries its rows at:

  `(2T + 80X)·(4e·X/H + 1)/(2X)² ≤ 2·(2T + 20N)·(2e·X/H + 1)/X²`   (`2X ≤ N`).

With the `3 → 4` prefactor inflation the fourth row forces on `lemma12Rows`, this is what the
§3 delta — "multiply `seam_row_number`'s `480·(T_ann/X_d + 1)·(Σ_j … + C·(2/M))` summand by
`4`" — pays for.  Stated as a bare inequality so the ladder rewire can cite a number instead
of an argument. -/
theorem second_window_le_first_row {H T Nr : ℝ} {X : ℕ} (hH : 2 ≤ H) (hX : 1 ≤ X)
    (hT : 0 ≤ T) (hN : 2 * (X : ℝ) ≤ Nr) :
    (2 * T + 80 * (X : ℝ)) * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2)
      ≤ 2 * ((2 * T + 20 * Nr) * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2)) := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hE0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hpre : 2 * T + 80 * (X : ℝ) ≤ 2 * (2 * T + 20 * Nr) := by linarith
  have hmass : (4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2
      ≤ (2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hq : (0 : ℝ) ≤ Real.exp 1 * (X : ℝ) / H := by positivity
    have e1 : (4 * Real.exp 1 * (X : ℝ) / H + 1) * (X : ℝ) ^ 2
        = 4 * (Real.exp 1 * (X : ℝ) / H) * (X : ℝ) ^ 2 + (X : ℝ) ^ 2 := by ring
    have e2 : (2 * Real.exp 1 * (X : ℝ) / H + 1) * (2 * (X : ℝ)) ^ 2
        = 8 * (Real.exp 1 * (X : ℝ) / H) * (X : ℝ) ^ 2 + 4 * (X : ℝ) ^ 2 := by ring
    rw [e1, e2]
    nlinarith [mul_nonneg hq (sq_nonneg (X : ℝ)), sq_nonneg (X : ℝ)]
  have hmass0 : (0 : ℝ) ≤ (4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2 := by
    positivity
  calc (2 * T + 80 * (X : ℝ)) * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2)
      ≤ (2 * (2 * T + 20 * Nr))
          * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_right hpre hmass0
    _ ≤ (2 * (2 * T + 20 * Nr))
          * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left hmass ?_
        linarith
    _ = 2 * ((2 * T + 20 * Nr) * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2)) := by ring

end Salt.MR
