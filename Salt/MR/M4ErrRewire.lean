/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SeamRowWindowed
import Salt.MR.M4P2MR
import Salt.MR.M4Sieve

/-!
# `M4ErrRewire` — ⟦THE WALL⟧'s `p²` stone and the `hwin`-free `E` row

Design: `docs/exploration/m4-residue-design-0728.md`, Part W (v2's `W1` verdict supersedes
v1's text).  Flags: "THE JOIN lands as an honest prefix", ⟦THE WALL⟧.

**THE WALL.**  `FrameWitness.err_at_witness` reaches `A2Frame3.err` through
`USetResiduals.E_priced_row_scale`, whose `p²`-mass slot is
`SeamCalibrationK.ramP2mass_direct` — and *that* stone reads the JOINT-SUPPORT binder

  `hwin : ∀ p m, p prime → P ≤ p → p ≤ Q → c p · b m ≠ 0 → X_d ≤ pm ≤ 2X_d`.

`M4Seam.m4_row_cf_block_eq_zero` is the kernel witness that `hwin` alone collapses the
capstone's datum: at `m = 1` it forces `c P = 0` at every block prime below the window.  The
window LAW is therefore uninhabitable by the door's `P`-exact sieved `λχ̄`, and no
relativization of `hwin` helps (`SeamRowWindowed` §1: relativizing a joint-support claim is
vacuous).

**THE REWIRE.**  `RamareMR` already retired `hwin` on the *identity* side by moving the
cofactor range to MR's own `ramHonMR N X p = {m : X ≤ pm ≤ 2X}` — the window lives IN THE
INDEX SET.  `SeamRowWindowed.ramErr_moment_split_mr_windowed` decomposes the SAME `ramErr`
object with neither `hwin` nor the unrestricted `hcoef`, at the relativized pair `SeamCoefW`.
What was missing is the ONE stone below: the sharp `p²` mass at `ramP2domMR`, i.e.
`ramP2mass_direct`'s `16·log₂(2X)/(X·P)` grade with the window read off the index set instead
of off `hwin`.  §1 lands it; §2 assembles the `hwin`-free `E` row at the split's prefactor
`4`; §3 records the door datum's inhabitation of the surviving binder set.

## §1 HAS MOVED (`M4P2MR`)

The `p²` stone `ramP2massMR_direct` and its two halves now live in `Salt/MR/M4P2MR.lean`,
verbatim — this file's cone passes through `M4Sieve` (hence `CapFreeArm3`), and ⟦WALL 1⟧'s
row repair needs the stone strictly upstream of the seam row.  Its route is unchanged:

### the two halves (`ramP2mass_direct`'s own route, `Σf² ≤ (max f)(Σ f)`)

* the **max** half `‖coeff_n‖/n ≤ 2·log₂(2X)/X`: off the fibre the coefficient is `0`, and on
  it the window comes from `ramHonMR` membership (`mem_ramP2domMR_window`), so `X ≤ n ≤ 2X`;
  the fibre has `≤ ω(n) ≤ log₂(2X)` points and each term has norm `≤ 2`
  (`SmallStones.ramP2_term_norm_le` — the unconditional bound, no `hwin`);
* the **Σ** half `Σ_n ‖coeff_n‖/n ≤ 8/P`: `SmallStones.ramP2mass_le`'s own ledger, stopped
  one step before its lossy `Σf² ≤ (Σf)²`.

The product is `16·log₂(2X)/(X·P)` — `ramP2mass_direct`'s grade verbatim, with `hwin` gone.

Three of `SmallStones`' helpers on the `Σ` side (`card_ramP2_cofactors_le`,
`ramP2_inner_row_le`, `ramP2_dom_sum_le`) are `private` there, so they are re-derived here
verbatim; this is `SeamCalibrationK`'s own precedent for `TypicalPrice`'s privates.

## §2's grade arithmetic (the refuter's page)

The windowed split pays `4` where `USetResiduals.ramErr_moment_split` pays `3`, and the two
seam rows collapse to `RamareMR.seam_rows_grade`'s `520·(T/X+1)/H` instead of the unwindowed
`720·(T/X+1)/H`.  Against `A2Frame3.err`'s standing right-hand side:

  `4·520 = 2080  ≤  2160 = 3·720`,

so the seam half fits with `80·(T/X+1)/H` to spare, and the `p²` half fits at the cost of a
`4/3` inflation of the `EP2` slot (`FrameWitness.witEP2`) — which is what the frame's four
`witEP2` sites now carry.  Nothing in `A2Frame3` moves.
-/

noncomputable section

namespace Salt.MR

open Finset
open scoped BigOperators

/-! ## §2 — THE `hwin`-FREE `E` ROW -/

/-- **THE WINDOWED `E` ROW** (`E_priced_mr`).  `USetResiduals.E_priced`'s twin through
`SeamRowWindowed.ramErr_moment_split_mr_windowed`:

  `∫_{−T}^{T} ‖ramErr‖² ≤ 4·(520·(T/X_d + 1)/H + (2T+20N)·16·log₂(2X_d)/(X_d·P))`.

Three changes against `E_priced`, all in the honest direction:

* `hcoef` (unsatisfiable at the S8 datum, `ThmA2Spine.seam_coef_contract_absurd`) becomes
  the relativized `SeamCoefW`;
* **`hwin` is GONE** — MR's cofactor range carries the window, and the `p²` mass is priced by
  §1's `ramP2massMR_direct`;
* the Cauchy–Schwarz prefactor is the four-row split's `4` in place of the three-row `3`, and
  MR's SECOND seam window is paid explicitly inside `RamareMR.seam_rows_grade`'s `520`. -/
theorem E_priced_mr (H : ℝ) (hH : 2 ≤ H) (N Xd P Q : ℕ) (hXd : 1 ≤ Xd) (hN : 2 * Xd ≤ N)
    (hN2 : (N : ℝ) ≤ 2 * (Xd : ℝ)) (hHX : H ≤ (Xd : ℝ)) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoefW : SeamCoefW Xd P Q a b c)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (Xd : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (Xd : ℝ))
    -- ⟦R3a — THE TAIL IS PRICED, NOT PINNED⟧ `homega` (the single-`P` support pin,
    -- unsatisfiable at the door's band datum) is replaced by the coprime-tail MASS
    (Mtail : ℝ)
    (hMtail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramErr H N Xd P Q a b c t‖ ^ 2)
      ≤ 4 * (520 * (T / (Xd : ℝ) + 1) / H
          + (2 * T + 20 * (N : ℝ))
              * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))
          + (2 * T + 20 * (N : ℝ)) * Mtail) := by
  have hsplit := ramErr_moment_split_mr_windowed H hH N Xd P Q hXd hN hP a b c hcoefW
    hasupp T hT
  have h1 := ramSeamLoPoly_moment H hH N Xd P Q hXd hN hP b c hb hc T hT
  have h2 := ramSeamUpPoly_moment H hH N Xd P Q hXd hP b c hb hc T hT
  have h3 := ramP2corrMR_moment N Xd P Q hXd hN a b c T
  have h4 := ramCopTail_moment N P Q a T
  have hgrade := seam_rows_grade H hH N Xd hXd hN2 hHX T hT
  have hmass := ramP2massMR_direct N Xd P Q hXd hN hP a b c ha hb hc
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hfac : (0 : ℝ) ≤ 2 * T + 20 * (N : ℝ) := by linarith
  have hp2 : (∫ t in (-T)..T, ‖ramP2corrMR N Xd P Q a b c t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ))
          * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))) :=
    h3.trans (mul_le_mul_of_nonneg_left hmass hfac)
  have htail : (∫ t in (-T)..T, ‖ramCopTail N P Q a t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * Mtail :=
    h4.trans (mul_le_mul_of_nonneg_left hMtail hfac)
  linarith

/-- **THE WINDOWED `E` ROW AT THE ROW SCALE** (`E_priced_mr_row_scale`).
`USetResiduals.E_priced_row_scale`'s move, verbatim: the row's `T/X` grade is read at the
REAL scale `X`, the seam row at the DYADIC scale `X_d`, and the two meet under `X ≤ X_d`
(⟦V4⟧'s law — stated separately so the mismatch is visible). -/
theorem E_priced_mr_row_scale (H : ℝ) (hH : 2 ≤ H) (N Xd P Q : ℕ) (hXd : 1 ≤ Xd)
    (hN : 2 * Xd ≤ N) (hN2 : (N : ℝ) ≤ 2 * (Xd : ℝ)) (hHX : H ≤ (Xd : ℝ)) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ) (hcoefW : SeamCoefW Xd P Q a b c)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (Xd : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (Xd : ℝ))
    (Mtail : ℝ)
    (hMtail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail)
    (T X : ℝ) (hT : 0 ≤ T) (hX0 : 0 < X) (hXdX : X ≤ (Xd : ℝ)) :
    (∫ t in (-T)..T, ‖ramErr H N Xd P Q a b c t‖ ^ 2)
      ≤ 4 * (520 * (T / X + 1) / H
          + (2 * T + 20 * (N : ℝ))
              * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))
          + (2 * T + 20 * (N : ℝ)) * Mtail) := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hscale : T / (Xd : ℝ) ≤ T / X := div_le_div_of_nonneg_left hT hX0 hXdX
  have hrow : 520 * (T / (Xd : ℝ) + 1) / H ≤ 520 * (T / X + 1) / H := by
    have h1 : 520 * (T / (Xd : ℝ) + 1) ≤ 520 * (T / X + 1) := by linarith
    rw [div_le_div_iff_of_pos_right hH0]
    exact h1
  refine (E_priced_mr H hH N Xd P Q hXd hN hN2 hHX hP a b c hcoefW ha hb hc hasupp Mtail
    hMtail T hT).trans ?_
  linarith

/-! ### ⟦THE ENDPOINT WALL⟧ — the STRICT/FUSED `E` row

`SeamRowWindowed` §3′ re-cuts the same `ramErr` object at the STRICT pair law `SeamCoefWS`
and pays the released endpoint cofactors inside the `p²` row (the fused filter
`p ∣ m ∨ p·m = X`).  The split is still FOUR rows at prefactor `4`, so `err_grade_fit` and
its `4·520 ≤ 2160` are untouched; the ONLY change on the right is the fused stone's extra
summand, carried here as the named `endMass`. -/

/-- ⟦THE ENDPOINT MASS⟧ `M_end = 4·(log₂(2X_d))²/X_d²` — the price of releasing the window's
lower endpoint from the pair law, i.e. `M4P2MR.ramP2massEndMR_direct`'s excess over
`ramP2massMR_direct`.  Named so the five `hEP2` sites can carry it as a SEPARATE summand
(the ⟦R3a⟧ `Mtail` pattern) with `witEP2`'s numerals byte-untouched. -/
noncomputable def endMass (Xd : ℕ) : ℝ :=
  4 * (Real.logb 2 (2 * (Xd : ℝ))) ^ 2 / (Xd : ℝ) ^ 2

lemma endMass_nonneg (Xd : ℕ) : 0 ≤ endMass Xd := by
  rw [endMass]; positivity

/-- **THE STRICT/FUSED `E` ROW** (`E_priced_mr_end`).  `E_priced_mr` at `SeamCoefWS`, with the
`p²` mass supplied by the FUSED stone `M4P2MR.ramP2massEndMR_direct`.  Against `E_priced_mr`
the binder `hcoefW` weakens to `hcoefWS` and the right-hand side gains one summand,
`(2T+20N)·M_end`. -/
theorem E_priced_mr_end (H : ℝ) (hH : 2 ≤ H) (N Xd P Q : ℕ) (hXd : 1 ≤ Xd) (hN : 2 * Xd ≤ N)
    (hN2 : (N : ℝ) ≤ 2 * (Xd : ℝ)) (hHX : H ≤ (Xd : ℝ)) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoefWS : SeamCoefWS Xd P Q a b c)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (Xd : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (Xd : ℝ))
    (Mtail : ℝ)
    (hMtail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramErr H N Xd P Q a b c t‖ ^ 2)
      ≤ 4 * (520 * (T / (Xd : ℝ) + 1) / H
          + (2 * T + 20 * (N : ℝ))
              * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))
          + (2 * T + 20 * (N : ℝ)) * endMass Xd
          + (2 * T + 20 * (N : ℝ)) * Mtail) := by
  simp only [endMass]
  have hsplit := ramErr_moment_split_mr_windowed_end H hH N Xd P Q hXd hN hP a b c hcoefWS
    hasupp T hT
  have h1 := ramSeamLoPoly_moment H hH N Xd P Q hXd hN hP b c hb hc T hT
  have h2 := ramSeamUpPoly_moment H hH N Xd P Q hXd hP b c hb hc T hT
  have h3 := ramP2corrEndMR_moment N Xd P Q hXd hN a b c T
  have h4 := ramCopTail_moment N P Q a T
  have hgrade := seam_rows_grade H hH N Xd hXd hN2 hHX T hT
  have hmass := ramP2massEndMR_direct N Xd P Q hXd hN hP a b c ha hb hc
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hfac : (0 : ℝ) ≤ 2 * T + 20 * (N : ℝ) := by linarith
  have hp2 : (∫ t in (-T)..T, ‖ramP2corrEndMR N Xd P Q a b c t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ))
          * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))
            + 4 * (Real.logb 2 (2 * (Xd : ℝ))) ^ 2 / (Xd : ℝ) ^ 2) :=
    h3.trans (mul_le_mul_of_nonneg_left hmass hfac)
  have htail : (∫ t in (-T)..T, ‖ramCopTail N P Q a t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * Mtail :=
    h4.trans (mul_le_mul_of_nonneg_left hMtail hfac)
  linarith

/-- **THE STRICT/FUSED `E` ROW AT THE ROW SCALE** (`E_priced_mr_row_scale_end`). -/
theorem E_priced_mr_row_scale_end (H : ℝ) (hH : 2 ≤ H) (N Xd P Q : ℕ) (hXd : 1 ≤ Xd)
    (hN : 2 * Xd ≤ N) (hN2 : (N : ℝ) ≤ 2 * (Xd : ℝ)) (hHX : H ≤ (Xd : ℝ)) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ) (hcoefWS : SeamCoefWS Xd P Q a b c)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (Xd : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (Xd : ℝ))
    (Mtail : ℝ)
    (hMtail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail)
    (T X : ℝ) (hT : 0 ≤ T) (hX0 : 0 < X) (hXdX : X ≤ (Xd : ℝ)) :
    (∫ t in (-T)..T, ‖ramErr H N Xd P Q a b c t‖ ^ 2)
      ≤ 4 * (520 * (T / X + 1) / H
          + (2 * T + 20 * (N : ℝ))
              * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))
          + (2 * T + 20 * (N : ℝ)) * endMass Xd
          + (2 * T + 20 * (N : ℝ)) * Mtail) := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hscale : T / (Xd : ℝ) ≤ T / X := div_le_div_of_nonneg_left hT hX0 hXdX
  have hrow : 520 * (T / (Xd : ℝ) + 1) / H ≤ 520 * (T / X + 1) / H := by
    have h1 : 520 * (T / (Xd : ℝ) + 1) ≤ 520 * (T / X + 1) := by linarith
    rw [div_le_div_iff_of_pos_right hH0]
    exact h1
  refine (E_priced_mr_end H hH N Xd P Q hXd hN hN2 hHX hP a b c hcoefWS ha hb hc hasupp Mtail
    hMtail T hT).trans ?_
  linarith

/-- **THE GRADE FIT** (`err_grade_fit`).  The arithmetic behind the rewire, isolated so that
the refuter's page is a Lean object: the windowed row's `4·(520·g + E′)` sits under
`A2Frame3.err`'s standing `3·(720·g + E)` as soon as the `EP2` slot carries the `4/3`
inflation `4·E′ ≤ 3·E`.  The seam half is `4·520 = 2080 ≤ 2160 = 3·720`, with
`80·g/H` to spare. -/
theorem err_grade_fit {g H Ep Ep' : ℝ} (hg : 0 ≤ g) (hH : 0 < H)
    (hE : 4 * Ep' ≤ 3 * Ep) :
    4 * (520 * g / H + Ep') ≤ 3 * (720 * g / H + Ep) := by
  have hgH : 0 ≤ g / H := div_nonneg hg hH.le
  have h1 : 4 * (520 * g / H) ≤ 3 * (720 * g / H) := by
    have : 520 * g / H = 520 * (g / H) := by ring
    rw [this]
    have h2 : 720 * g / H = 720 * (g / H) := by ring
    rw [h2]
    linarith
  linarith

/-! ## §3 — THE DOOR DATUM INHABITS THE SURVIVING BINDER SET

⟦THE WALL⟧'s second half.  With `hwin` gone the err chain's coefficient demand is exactly

  `SeamCoefW X_d P P a b cf`  +  `‖a‖, ‖b‖, ‖cf‖ ≤ 1`  +  `hasupp`  +  `hsupp`,

and the design's factorization of the door's sieved `λχ̄` window datum meets it — at EVERY
cofactor `m`, INCLUDING `P ∣ m` and including `m = 1` (the point at which the old `hwin`
collapsed the datum, `M4Seam.m4_row_cf_block_eq_zero`).  The reason is complete
multiplicativity: `λ` factors with NO coprimality (`M4Residue.liouvilleC_mul`) and `χ̄` is a
`MulChar`, so the sieve indicator and the phase are the only non-multiplicative pieces — and
both are absorbed into the COFACTOR slot, where the phase reads at the dilated frequency
`αP` and the indicator at the shifted argument `P·m`.

**THE RESIDUE THIS SECTION EXPOSES.**  `CapFreeArm3.A2Frame3.err` pins the cofactor slot to
`ellLin g` (the completely multiplicative extension of the row's own `g`), and the row leg
needs it there.  `doorCofactor` below is NOT of that shape — it carries `1_𝒮(P·)` and the
phase.  So the surviving obstruction to instantiating the capstone at the door datum is the
frame's `b`-SLOT PIN, not the window law: `A2Frame3.err`'s `ellLin g` must become a free
`1`-bounded `b` before `m4_meansq_per_chi_gen`'s err-side binders can be re-stated at it.
That statement lives in `CapFreeArm3`, outside this wave's authorization. -/

/-- The unimodular door phase (`M4Window.norm_exp_phase`, which is `private` there). -/
private lemma normMR_exp_phase (β : ℝ) (k : ℕ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * ((k : ℕ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * ((k : ℕ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- **`λχ̄` IS COMPLETELY MULTIPLICATIVE.**  `liouvilleC_mul` (no coprimality) and `χ`'s
`MulChar` law, composed through the conjugation ring hom. -/
theorem liouChi_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (m n : ℕ) :
    liouChi χ (m * n) = liouChi χ m * liouChi χ n := by
  unfold liouChi
  rw [liouvilleC_mul]
  have hcast : ((m * n : ℕ) : ZMod q) = (m : ZMod q) * (n : ZMod q) := by push_cast; ring
  rw [hcast, map_mul, map_mul]
  ring

/-- **THE DOOR'S WINDOW DATUM** at frequency `α`: the sieved `λχ̄`, phased.  This is the
coefficient sequence `M4Door`/`M4BridgePhase` hand the mean-square obligation. -/
noncomputable def doorDatum {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J : ℕ) (α : ℝ) : ℕ → ℂ :=
  fun n => memSCoeff Pseq Qseq J (liouChi χ) n
    * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((n : ℕ) : ℂ))

/-- **THE DOOR'S COFACTOR SLOT AT THE BLOCK PIN `P`**: the sieve indicator read at `P·m`,
the cofactor's own `λχ̄`, and the phase at the DILATED frequency `αP`. -/
noncomputable def doorCofactor {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J P : ℕ) (α : ℝ) : ℕ → ℂ :=
  fun m => (if MemS Pseq Qseq J (P * m) then (1 : ℂ) else 0) * liouChi χ m
    * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((α * (P : ℝ) : ℝ) : ℂ) * ((m : ℕ) : ℂ))

/-- **THE DOOR DATUM FACTORIZES — AT EVERY `m`.**  `a(P·m) = b(m)·cf(P)` with
`cf = λχ̄` and `b = doorCofactor`, with NO coprimality, NO window restriction, and no
exception at `m = 1`. -/
theorem doorDatum_factorizes {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J P : ℕ) (α : ℝ) (m : ℕ) :
    doorDatum χ Pseq Qseq J α (P * m)
      = doorCofactor χ Pseq Qseq J P α m * liouChi χ P := by
  have hphase : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (((P * m : ℕ)) : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((α * (P : ℝ) : ℝ) : ℂ)
          * ((m : ℕ) : ℂ)) := by
    congr 1
    push_cast
    ring
  simp only [doorDatum, doorCofactor, memSCoeff]
  rw [hphase]
  split_ifs with hS
  · rw [liouChi_mul]; ring
  · ring

/-- `doorCofactor` is `1`-bounded. -/
theorem norm_doorCofactor_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J P : ℕ) (α : ℝ) (m : ℕ) : ‖doorCofactor χ Pseq Qseq J P α m‖ ≤ 1 := by
  rw [doorCofactor, norm_mul, norm_mul, normMR_exp_phase, mul_one]
  have hχ := norm_liouChi_le_one χ m
  split_ifs with hS
  · rw [norm_one, one_mul]; exact hχ
  · rw [norm_zero, zero_mul]; norm_num

/-- `doorDatum` is `1`-bounded. -/
theorem norm_doorDatum_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J : ℕ) (α : ℝ) (n : ℕ) : ‖doorDatum χ Pseq Qseq J α n‖ ≤ 1 := by
  rw [doorDatum, norm_mul, normMR_exp_phase, mul_one]
  exact norm_memSCoeff_le_one (norm_liouChi_le_one χ) Pseq Qseq J n

/-- **THE DOOR DATUM SATISFIES THE RELATIVIZED PAIR LAW** at the block pin `P = Q`, at any
dyadic scale `X_d` — the window antecedents are simply not used, because the factorization
is unconditional. -/
theorem doorDatum_seamCoefW {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J P Xd : ℕ) (α : ℝ) :
    SeamCoefW Xd P P (doorDatum χ Pseq Qseq J α) (doorCofactor χ Pseq Qseq J P α)
      (liouChi χ) := by
  intro p m _ hPp hpP _ _ _
  have hpe : p = P := le_antisymm hpP hPp
  subst hpe
  exact doorDatum_factorizes χ Pseq Qseq J p α m

/-- **⟦THE INHABITATION⟧** (`doorDatum_inhabits_err_binders`).  The whole coefficient side of
the rewired err chain — the three `1`-bounds and the relativized pair law — at the door's own
sieved, phased `λχ̄` datum.  Nothing here is conditional: no scale gate, no window, no
coprimality.  Compare `M4Seam.m4_row_cf_block_eq_zero`, which shows the PRE-rewire binder set
(with `hwin`) forces `cf P = 0` and so admits no such datum at all. -/
theorem doorDatum_inhabits_err_binders {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Pseq Qseq : ℕ → ℕ) (J P Xd : ℕ) (α : ℝ) :
    (∀ n, ‖doorDatum χ Pseq Qseq J α n‖ ≤ 1)
      ∧ (∀ m, ‖doorCofactor χ Pseq Qseq J P α m‖ ≤ 1)
      ∧ (∀ p, ‖liouChi χ p‖ ≤ 1)
      ∧ SeamCoefW Xd P P (doorDatum χ Pseq Qseq J α) (doorCofactor χ Pseq Qseq J P α)
          (liouChi χ) :=
  ⟨norm_doorDatum_le_one χ Pseq Qseq J α,
   norm_doorCofactor_le_one χ Pseq Qseq J P α,
   norm_liouChi_le_one χ,
   doorDatum_seamCoefW χ Pseq Qseq J P Xd α⟩

end Salt.MR
