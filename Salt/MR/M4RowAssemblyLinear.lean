/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4RowLinear
import Salt.MR.M4Assembly
import Salt.MR.M4Collapse
import Salt.MR.M4DoorClosePool
import Salt.MR.M4AssemblyPool
import Salt.MR.M4BaseNarrow
import Salt.MR.M4RowsChiEnd

/-!
# `M4RowAssemblyLinear` — THE ASSEMBLY LAYER at the LINEAR door

⟦LADDER-L, lane G2, layer 2⟧  `M4RowLinear`'s successor: the door-fuse frames
(`DoorFuseFrame_L`, `_pool`, `_gk`), the assembly exits, the pool/join registers, the
collapse and the narrowed base.  Same convention throughout — `AdoorL M = 2^36·M` in the
anchor slot, the `G`-slot untouched, the landed body replayed, nothing landed moved.

The cross-lane scaffold lives in `M4RowLinear`'s `Salt.MR.G2Scaffold`; it is opened here.
-/

noncomputable section

open scoped BigOperators
open Complex MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

-- ⟦THE LINEAR ANCHOR'S ELABORATION COST⟧ every twin below reads `AdoorL M = 2^36·M` where its
-- landed original reads `Adoor M = 2^36·(⌊log₂ M⌋ + 1)`, so each `calP`/`calQK` occurrence
-- carries a longer term and the register-against-register instantiations (~40–100 conjuncts,
-- no tactic search anywhere) cost proportionally more `whnf` steps.  The limit is raised
-- file-wide rather than per-declaration because the cost is uniform across the page.
set_option maxHeartbeats 4000000

open G2Scaffold

/-! ## §1 — `M4Assembly` -/

/-- The `χ̄`-twist of the untwisted door datum IS the door's sieved χ-twisted datum. -/
theorem chiBarCoeff_doorCoeffU_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) :
    chiBarCoeff q χ (doorCoeffU_L M) = doorChiCoeff_L χ M := by
  funext n
  simp only [chiBarCoeff_apply, doorCoeffU_L, doorChiCoeff_L, memSCoeff, liouChi]
  split_ifs
  · ring
  · rw [mul_zero]

/-- **THE BRIDGE** — the door's ROW datum is the `χ̄`-twist of one untwisted sequence.  This is
what makes a supplier written at `chiBarCoeff q χ a` and a supplier written at
`winCutH X_d (doorChiCoeff_L χ M)` interchangeable in §3's slots. -/
theorem chiBarCoeff_doorRowDatum_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd : ℕ) :
    chiBarCoeff q χ (winCutH Xd (doorCoeffU_L M)) = winCutH Xd (doorChiCoeff_L χ M) := by
  rw [chiBarCoeff_winCutH, chiBarCoeff_doorCoeffU_L]

/-- **⟦A4 — THE SOCKET AT THE DOOR GRADE⟧** (`m4_chiSummedFreeRowBig_of_doorGrade_L`).

The `Σ_χ` door row, graded base by base by §3, inhabits `M4ChiSocketWire`'s large-`j` socket at
an ABSTRACT `RSbig`, under ONE arithmetic gate:

  `henv : arcDen 12 H · a2DoorGrade_L M (A+s) 2^j (C₁ (A+s)) (M₀ (A+s)) ≤ RSbig j H`.

⟦THE φ(q) LEDGER, IN THE OPEN⟧ the character count is paid as `φ(q) ≤ q ≤ arcDen 12 H` — the
socket's own modulus gate — and appears in `henv` explicitly.  Nothing is absorbed: this file
does not read `m4_second_road_rs_ceiling_L`, and `henv` is precisely the arithmetic the next
executor owes.

`C₁ M₀ : ℕ → ℝ` are indexed by the BASE `A + s` because `m4_hT0band_at_door_discharged_L`
chooses them per instance; `hgrade` is §3's conclusion, quantified over exactly the socket's
bases. -/
theorem m4_chiSummedFreeRowBig_of_doorGrade_L {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    {C₁ M₀ : ℕ → ℝ}
    {RSbig : ℕ → ℕ → ℝ}
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloorL M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig_L R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) := a2DoorGrade_L_nonneg hM (log_natCast_nonneg' (A + s)) hh0
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans
    (hgrade H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H j A s hjfl

/-- **⟦A4 — ITEM 11, INHABITED AT THE DOOR GRADE⟧** (`m4_chiSummedFreeRow_of_doorGrade_L`).
§4 spliced through `M4ChiSocketWire.m4_chiSummedFreeRow_of_big`: the second road's ONE
analytic slot `M4ChiSummed.M4ChiSummedFreeRow` holds at

  `RS j H = if doorRowFloorL M ≤ j then RSbig j H else 4·arcDen 12 H`,

the small-`j` half being the landed absolute grade (`m4_chiSummedFreeRow_trivial_L`), which
⟦gate 4⟧ never reads (`M4ChiSocketWire.m4ChiRowGraded_an`). -/
theorem m4_chiSummedFreeRow_of_doorGrade_L {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    {C₁ M₀ : ℕ → ℝ}
    {RSbig : ℕ → ℕ → ℝ}
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloorL M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) :=
  m4_chiSummedFreeRow_of_big_L (m4_chiSummedFreeRowBig_of_doorGrade_L hM hgrade henv)

/-- **⟦A4 — THE ASSEMBLY⟧** (`m4_chiSummedFreeRow_of_doorAssembly_L`).  ⟦Item 11⟧ of
`m4_second_road_L` — `M4ChiSummed.M4ChiSummedFreeRow` — inhabited at the door grade

  `RS j H = if doorRowFloorL M ≤ j then RSbig j H else 4·arcDen 12 H`,

from the NAMED gates alone.  THE COMPLETE GATE LIST:

* `hM` — `1 ≤ M`;
* `hframe` — `DoorFuseFrame_L` at every base the socket reaches (eleven fields, above);
* `hrows` — the weighted seam-row family at `a2Mrow_L`, PER CHARACTER, in
  `ThmA2ChiSummed.thm_a2'_of_rows_chiSummed`'s frozen binder.  Its own residue, when supplied
  by the `χ`-side D2 page: the §5 graded-razor + socket-floor gates at `(q, 2T)`, the
  co-factor binder `Rbd` with its `Cq`-gate (supplier `RbdSupply.rbd_binder_of_doorSocket_free`
  / `m4_supplier_all_chi`), the `𝒯_S` budget `KS`, Lemma 12's `χ`-summed error row, the
  carried ball binder `hSup` (supplied here by §1a at the door pin `t₁ ≡ 0`), the `𝒯`-side
  frame `CalFrameK`, the reconciliation gates (R1)–(R6) and the weighting frame.  **See the
  header's ⟦THE WALL⟧ for why the D2 door page cannot fill it as it stands.**
* `hband` — the `T₀`-band at `t0BandB X_d (cfbC₁ X_d C₁) M₀`, PER CHARACTER, discharged by
  `M4T0DatumDischarge.m4_hT0band_at_door_discharged` under its own named gates (`400 ≤ X_d`,
  `x₀ ≤ X_d`, `16 ≤ X_d`, `q ≤ (log X_d)^{10}`, the covering window `[P,Q]` from
  `door_cover_L`/`door_window_bounds_L`, the three mass/Rankin gates per `k ∈ [X_d, 2X_d]`, the
  grade fit `8C' ≤ (log X_d)^{A−1/2+1/1000}` and `hErr`);
* `henv` — THE ARITHMETIC, and the only thing this file leaves open:
  `arcDen 12 H · a2DoorGrade_L M (A+s) 2^j (C₁ (A+s)) (M₀ (A+s)) ≤ RSbig j H`.  The `arcDen`
  factor IS the ⟦φ(q) LEDGER⟧'s debit `φ(q) ≤ q ≤ arcDen 12 H`, carried in the open. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_L {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_L M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
          ≤ a2Mrow_L (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorGrade_L hM (C₁ := C₁) (M₀ := M₀) ?_ henv
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb : SocketBaseL R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_L hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows
    ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-- **⟦THE WALL⟧** (`doorRows_global_hcoef_kills_block_L`).
`ThmA2Spine.seam_coef_contract_forces_vanishing` read at the DOOR's block `j`: a datum that is
window-supported (`M4RowsChi.m4_hrowsSum_chi_door`'s `hasupp`, `M4RowsChi.lean:1166`) and obeys
the GLOBAL Lemma-12 factorization (its `hcoef`, `M4RowsChi.lean:1161-1162`) is KILLED on the
whole block by one live product plus one block prime that pushes off the window:
`a (p₁·m) = 0` for every `m` coprime to `p₁`.

At the door ladder `[P_j, Q_j] = [2^{E_j}, 2^{j²M·E_j}]` the ratio is far above `2`, so such a
`p₁` sits next to every live `p₀`.  This is why `m4_chiFreeRowSq_sum_at_door_L` CARRIES its
`hrowsSum` slot instead of filling it from the D2 door page, and why the landed `q = 1`
supplier `ThmA2Rows.a2Rows_of_capfree3_end` (`ThmA2Rows.lean:1057-1060`) states the STRICT
relativized pair law `SeamRowWindowed.SeamCoefWS` instead of the global contract. -/
theorem doorRows_global_hcoef_kills_block_L {a b c : ℕ → ℂ} {M Xd j : ℕ}
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (hcoef : ∀ p m : ℕ, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
      p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m → a (p * m) = b m * c p)
    {p₀ p₁ m₀ : ℕ} (hp₀ : p₀.Prime) (hP₀ : calP (AdoorL M) (3072 * M) j ≤ p₀)
    (hQ₀ : p₀ ≤ calQK (AdoorL M) (3072 * M) M j) (hd₀ : ¬ p₀ ∣ m₀)
    (hlive : a (p₀ * m₀) ≠ 0)
    (hp₁ : p₁.Prime) (hP₁ : calP (AdoorL M) (3072 * M) j ≤ p₁)
    (hQ₁ : p₁ ≤ calQK (AdoorL M) (3072 * M) M j) (hd₁ : ¬ p₁ ∣ m₀)
    (hoff : 2 * Xd < p₁ * m₀) :
    ∀ m : ℕ, ¬ p₁ ∣ m → a (p₁ * m) = 0 :=
  seam_coef_contract_forces_vanishing hasupp hcoef hp₀ hP₀ hQ₀ hd₀ hlive hp₁ hP₁ hQ₁ hd₁ hoff

set_option linter.unusedVariables false in
/-- `a2DoorGrade_L` (:213), at the lever.  The body is byte-identical: the only ladder read is
`a2Level1_L M`, which is LEVEL 1 and K-invariant.  The twin exists for uniformity of the
family's shape (`K` first, everywhere), exactly as `M4Close.m4RawMS_gk` does. -/
def a2DoorGrade_L_gk (K : ℕ) (M : ℕ) (X h C₁ M₀ : ℝ) : ℝ :=
  8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
    + 1787702400 * a2Level1_L M
    + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
    + 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
    + 6315000 / h

/-- `a2DoorGrade_L_nonneg` (:229), at the lever. -/
theorem a2DoorGrade_nonneg_L_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) {X h C₁ M₀ : ℝ}
    (hX : 0 ≤ Real.log X)
    (hh : 0 < h) : 0 ≤ a2DoorGrade_L_gk K M X h C₁ M₀ :=
  a2DoorGrade_L_nonneg hM hX hh

/-- `m4_chiFreeRowSq_sum_at_door_L` (:289), at the lever. -/
theorem m4_chiFreeRowSq_sum_at_door_L_gk (K : ℕ) {q : ℕ} [NeZero q] {M Xd j : ℕ}
    {Cs Ccc C₁ M₀ ε : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)) (hX3 : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ))
    (hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ))
    (hhX : ((2 ^ j : ℕ) : ℝ)
      ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ)))
    (hTann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
    (hceil : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ ((Xd : ℕ) : ℝ) →
      TannGate ((Xd : ℕ) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
          * (∫ t in seamAnn ((Xd : ℕ) : ℝ) (2 * T),
              ‖spoly (2 * Xd) (winCutH Xd (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
        ≤ a2Mrow_L_gk K Cs Ccc M Xd ((Xd : ℕ) : ℝ) ε)
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 ((Xd : ℕ) : ℝ)))..(seamT0 ((Xd : ℕ) : ℝ)),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) t‖ ^ 2)
        ≤ t0BandB ((Xd : ℕ) : ℝ) (cfbC₁ ((Xd : ℕ) : ℝ) C₁) M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500))
    (hgRows : 5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ)))
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500))
    (hεwin : 0 ≤ ε ∧ ε ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)) :
    ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j Xd
      ≤ (q.totient : ℝ) * a2DoorGrade_L_gk K M ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) C₁ M₀ := by
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hbase := thm_a2'_of_rows_chiSummed_L_gk K (q := q) (N := 2 * Xd) (M := M) (Xd := Xd)
    (a := fun χ => winCutH Xd (doorChiCoeff_L_gk K χ M)) (X := ((Xd : ℕ) : ℝ))
    (h := ((2 ^ j : ℕ) : ℝ)) (Cs := fun _ => Cs) (Ccc := fun _ => Ccc)
    (C₁' := fun _ => cfbC₁ ((Xd : ℕ) : ℝ) C₁) (M₀ := fun _ => M₀) (ε := fun _ => ε)
    hM hX hX3 hh4 hhX (fun χ n => doorRow_ha1_L_gk K χ M Xd n)
    (fun χ n hn => doorRow_hsupp0_L_gk K χ M Xd n hn) hN2 hTann hceil hrowsSum hT0bandSum
    (fun _ => hgP1) (fun _ => hgRows) (fun _ => hεwin) hL4096
  simp only [shortSum_winCutH_seamS0] at hbase
  refine le_trans hbase (le_of_eq ?_)
  rw [a2_sum_const_chars]
  unfold a2DoorGrade_L_gk
  ring

/-- `DoorFuseFrame_L` (:440), at the lever.  Two of the eleven fields move: `gP1`'s `𝒫₁` is
written at the levered base and `gRows` reads `ThmA2.a2RowsSum_gk`. -/
structure DoorFuseFrame_L_gk (K : ℕ) (M Xd j : ℕ) (Cs Ccc ε : ℝ) : Prop where
  /-- `e ≤ X_d` — the frozen interface's lower scale pin. -/
  X_exp : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)
  /-- `3 ≤ X_d`. -/
  X_three : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ)
  /-- `4 ≤ 2^j` — the AS-2 MVT guard (NOT `3`). -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- Lemma 14's window frame `2^j ≤ X_d·(log X_d)^{−1/5}`. -/
  h_window : ((2 ^ j : ℕ) : ℝ)
    ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ))
  /-- `TannGate X_d (2X_d/2^j)` — the annulus gate at the family's bottom height. -/
  tann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))
  /-- `5 ≤ loglog(2X_d/2^j)` — the `h`-ceiling. -/
  ceil5 : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
  /-- The first GRADING gate, on the `𝒯`-leg constant `Cs`, AT THE LEVER. -/
  gP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
    ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
  /-- The second GRADING gate, at the levered row sum. -/
  gRows : 5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ)))
    ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
  /-- The `𝒰`-leg's exponent room, lower end. -/
  eps_lo : 0 ≤ ε
  /-- The `𝒰`-leg's exponent room, upper end (`θ₂₉₃ = 1/(32(3e+1))`). -/
  eps_hi : ε ≤ theta293 - 1 / 500
  /-- The third GRADING gate. -/
  L4096 : 4096 ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)

/-- `m4_chiSummedFreeRowBig_of_doorGrade_L` (:355), at the lever. -/
theorem m4_chiSummedFreeRowBig_of_doorGrade_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) {C₁ M₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloorL M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig_L_gk K R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) := a2DoorGrade_nonneg_L_gk K hM (log_natCast_nonneg' (A + s)) hh0
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans
    (hgrade H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H j A s hjfl

/-- `m4_chiSummedFreeRow_of_doorGrade_L` (:392), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorGrade_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    {C₁ M₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloorL M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) :=
  m4_chiSummedFreeRow_of_big_L_gk K
    (m4_chiSummedFreeRowBig_of_doorGrade_L_gk K hM hgrade henv)

/-- `m4_chiSummedFreeRow_of_doorAssembly_L` (:492), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_L_gk K M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow_L_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorGrade_L_gk K hM (C₁ := C₁) (M₀ := M₀) ?_ henv
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb : SocketBaseL R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_L_gk K hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows
    ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-- `doorRows_global_hcoef_kills_block_L` (:543), at the lever. -/
theorem doorRows_global_hcoef_kills_block_L_gk (K : ℕ) {a b c : ℕ → ℂ} {M Xd j : ℕ}
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (hcoef : ∀ p m : ℕ, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
      p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m → a (p * m) = b m * c p)
    {p₀ p₁ m₀ : ℕ} (hp₀ : p₀.Prime) (hP₀ : calP (AdoorL M) (s13GK K M) j ≤ p₀)
    (hQ₀ : p₀ ≤ calQK (AdoorL M) (s13GK K M) M j) (hd₀ : ¬ p₀ ∣ m₀)
    (hlive : a (p₀ * m₀) ≠ 0)
    (hp₁ : p₁.Prime) (hP₁ : calP (AdoorL M) (s13GK K M) j ≤ p₁)
    (hQ₁ : p₁ ≤ calQK (AdoorL M) (s13GK K M) M j) (hd₁ : ¬ p₁ ∣ m₀)
    (hoff : 2 * Xd < p₁ * m₀) :
    ∀ m : ℕ, ¬ p₁ ∣ m → a (p₁ * m) = 0 :=
  seam_coef_contract_forces_vanishing hasupp hcoef hp₀ hP₀ hQ₀ hd₀ hlive hp₁ hP₁ hQ₁ hd₁ hoff
/-! ## §2 — `M4Collapse` -/

set_option maxHeartbeats 1600000 in
-- the same cause as `M4DoorClose` §5 and `M4T0Discharge` §5: the register mentions
-- `DoorRowCarriedT0_L` under six binders and is elaborated against
-- `m4_wave_closed_of_dyadicRow_L`'s own list; no tactic search happens below
/-- **THE M4 WAVE, THE COPRIME ARM DISCHARGED** (`m4_wave_closed_coprime_discharged_L`).

`M4T0Discharge.m4_wave_closed_T0_discharged` with ARM 2 swapped: the coprime supply is no
longer assumed at `M4CoprimeBlockMeanSq_L` (the interface ⟦COPRIME-SCOPE⟧ proved unsuppliable)
but DERIVED, through `M4CoprimeSupply.m4_coprimeN_supplied` and
`M4NonCoprime.m4_nonCoprime_classMeanSq_N`, from the free-base row datum
`M4ChiFreeRowMeanSq_L R M MS` at the register's own grade `MS`.

What remains carried is ONE analytic item — that row datum — plus regime arithmetic.  The
module header enumerates the whole register (⟦THE FINAL REGISTER⟧) and says precisely why
the row datum is not itself discharged here (⟦THE WALL⟧). -/
theorem m4_wave_closed_coprime_discharged_L (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            -- ⟦ARM 1 DISCHARGED: the T₀-free per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0_L Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦the regime fact⟧ (subsumes the line above)
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦G1⟧ the trivial envelope dominates the arc denominator
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            -- ⟦G2⟧ the slack-`4` residue against the floor's own constant
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M) →
            -- ⟦ARM 2 DISCHARGED: the free-base row datum is the ONLY analytic carry left⟧
            M4ChiFreeRowMeanSq_L R M MS →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hbridge⟩ := doorRowCarried_of_t0free_L Qm
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_dyadicRow_carried_L
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_dyadicRow_L
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl Qm, Xsk, Kcf Qm, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl Qm, hXsk0, hKcf0 Qm, hCtail0,
    hK0, hX₀0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcarT0 hgate harc harc8 hG1 hG2 hrowfree
  -- ⟦ARM 1⟧ the T₀-free register becomes the carried one, instance by instance
  have hcar : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
        ∀ s ≤ H,
          DoorRowCarried_L Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
            (doorLadder R.x H (i + 1) + s) j (MS j H) := by
    intro H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH
    haveI : NeZero q := ⟨by omega⟩
    have hqQm : q ≤ Qm := by
      have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hRq
    exact hbridge Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail q χ M
      (doorLadder R.x H (i + 1) + s) j (MS j H) hqQm
      (hcarT0 H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH)
  -- ⟦ARM 2⟧ the row datum → the narrowed coprime family → every class of `q`
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H)
      (fun H => 2 * MStr H) H := fun H =>
    m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
  have hcpN : M4CoprimeBlockMeanSqN_L R M
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_coprimeN_supplied_L (doorRowFloorL M) hMSan0 hMStr0 han hG1 hG2 harc8 hrowfree
  have hnc : M4ClassBlockMeanSq_L R M k
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_nonCoprime_classMeanSq_N_L (k := k) hM hBcl0 hgate harc hcpN
  refine hR δ Braw MS MSan MStr (doorRowFloorL M) M k hgates hMSan0 hMStr0 hBraw0 han htr
    hdrift hdel hrest (hrow R Qm M k MS hM hQm htriv hcar) ?_
  intro H hlo hhi q hq hqQ i hik r hrq _hncop
  exact hnc H hlo hhi q hq hqQ i hik r hrq

set_option maxHeartbeats 1600000 in
-- §1's budget, for §1's cause: the twin restates the whole register (`DoorRowCarriedT0_L`
-- under six binders) and elaborates it against §1's; the proof itself is one destructuring
/-- **THE COLLISION FORM** (`m4_wave_closed_coprime_discharged_False_L`).  §1's register with
`logChowla2Fails R.eps R.x R.ω` assumed: the chain closes to `False`.  Byte-for-byte §1 with
`¬ P` read as `P → False`. -/
theorem m4_wave_closed_coprime_discharged_False_L (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0_L Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M) →
            M4ChiFreeRowMeanSq_L R M MS →
            logChowla2Fails R.eps R.x R.ω → False := by
  obtain ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩ := m4_wave_closed_coprime_discharged_L Qm
  exact ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩

/-- **THE M4 WAVE, BOTH ARMS DISCHARGED, AT THE LEVER** — `m4_wave_closed_coprime_discharged_L`
(:158). -/
theorem m4_wave_closed_coprime_discharged_L_gk (K : ℕ) (hK : K ≤ 170000000) (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            -- ⟦ARM 1 DISCHARGED: the T₀-free per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0_L_gk K Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦the regime fact⟧ (subsumes the line above)
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦G1⟧ the trivial envelope dominates the arc denominator
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            -- ⟦G2⟧ the slack-`4` residue against the floor's own constant
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M) →
            -- ⟦ARM 2 DISCHARGED: the free-base row datum is the ONLY analytic carry left⟧
            M4ChiFreeRowMeanSq_L_gk K R M MS →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hbridge⟩ := doorRowCarried_of_t0free_L_gk K Qm
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_dyadicRow_carried_L_gk K hK
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_dyadicRow_L_gk K
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl Qm, Xsk, Kcf Qm, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl Qm, hXsk0, hKcf0 Qm, hCtail0,
    hK0, hX₀0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcarT0 hgate harc harc8 hG1 hG2 hrowfree
  -- ⟦ARM 1⟧ the T₀-free register becomes the carried one, instance by instance
  have hcar : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
        ∀ s ≤ H,
          DoorRowCarried_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
            (doorLadder R.x H (i + 1) + s) j (MS j H) := by
    intro H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH
    haveI : NeZero q := ⟨by omega⟩
    have hqQm : q ≤ Qm := by
      have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hRq
    exact hbridge Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail q χ M
      (doorLadder R.x H (i + 1) + s) j (MS j H) hqQm
      (hcarT0 H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH)
  -- ⟦ARM 2⟧ the row datum → the narrowed coprime family → every class of `q`
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H)
      (fun H => 2 * MStr H) H := fun H =>
    m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
  have hcpN : M4CoprimeBlockMeanSqN_L_gk K R M
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_coprimeN_supplied_L_gk K (doorRowFloorL M) hMSan0 hMStr0 han hG1 hG2 harc8 hrowfree
  have hnc : M4ClassBlockMeanSq_L_gk K R M k
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_nonCoprime_classMeanSq_N_L_gk K (k := k) hM hBcl0 hgate harc hcpN
  refine hR δ Braw MS MSan MStr (doorRowFloorL M) M k hgates hMSan0 hMStr0 hBraw0 han htr
    hdrift hdel hrest (hrow R Qm M k MS hM hQm htriv hcar) ?_
  intro H hlo hhi q hq hqQ i hik r hrq _hncop
  exact hnc H hlo hhi q hq hqQ i hik r hrq

/-- **THE SAME, IN `False` FORM, AT THE LEVER** —
`m4_wave_closed_coprime_discharged_False_L` (:254). -/
theorem m4_wave_closed_coprime_discharged_False_L_gk (K : ℕ) (hK : K ≤ 170000000)
    (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0_L_gk K Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M) →
            M4ChiFreeRowMeanSq_L_gk K R M MS →
            logChowla2Fails R.eps R.x R.ω → False := by
  obtain ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩ := m4_wave_closed_coprime_discharged_L_gk K hK Qm
  exact ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩
/-! ## §3 — `M4DoorClosePool` -/

def DoorRowCarriedPool_L (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε C₁' M₀ cqS cgS cW SW Rbar0 Dmask π₀ : ℝ),
    -- ⟦the two pins⟧
    ((Xd : ℝ) = X) ∧ (((2 ^ j : ℕ) : ℝ) = h) ∧
    -- ⟦the scale page, at the BLOCK scale⟧
    (Real.exp (Real.exp 1) ≤ X) ∧ (Real.exp 2 ≤ Real.log X) ∧
    (h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) ∧
    (Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X) ∧
    TannGate X (2 * (X / h)) ∧ (5 ≤ Real.log (Real.log (2 * (X / h)))) ∧
    (T₀ ≤ 2 * (X / h)) ∧ (Real.exp 1 ≤ 2 * (X / h)) ∧
    (Real.log X ≤ L) ∧ (Real.exp 1 ≤ L) ∧ ((256 : ℝ) ≤ Real.log X) ∧
    -- ⟦the door and the band⟧
    (calQK (AdoorL M) (3072 * M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) i)
                (calQK (AdoorL M) (3072 * M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) i : ℕ) : ℝ)
            / Real.log ((calQK (AdoorL M) (3072 * M) M i : ℕ) : ℝ))) ∧
    -- ⟦the window floors at the witness ladder⟧
    (∀ v ∈ ramI (H83 X theta293) P Q, (5 : ℝ) ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X)
          - Real.log (Real.log (ramRbot (H83 X theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log X)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      seamRad X ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (3072 * M) 2)
          (calQK (AdoorL M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
        ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, kmin ≤ ((witKk (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((witMt (H83 X theta293) Xd v : ℕ) : ℝ) ≤ Ymax) ∧
    -- ⟦the calibration, the radius, the short-interval datum⟧
    ((0 : ℝ) < seamRad X) ∧
    ((1 : ℝ) ≤ V) ∧ (V⁻¹ ≤ δ') ∧ (Real.log V ≤ 100 * Real.log L) ∧
    (δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ))) ∧
    (656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) ∧
    (Real.exp (mrAlpha (1 / 12) 2
        * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
    ((0 : ℝ) ≤ Cb) ∧ ShortIntervalDatum Cb ∧
    (2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) ∧
    -- ⟦the `kmin`/`Ymax` ladder⟧
    (Xcap ≤ kmin) ∧ ((0 : ℝ) ≤ cofactorMfl X theta293 kmin) ∧
    ((2 : ℝ) ≤ kmin) ∧ (kmin ≤ X) ∧
    ((1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin) ∧
    (pin2Gate ≤ Ymax) ∧ (Real.log Ymax ≤ 2 * Real.log kmin) ∧
    (Real.log X ≤ Real.log Ymax) ∧
    (32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) ∧
    -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6)⟧
    (420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293)) ∧
    -- ⟦the ε-window⟧
    ((0 : ℝ) ≤ ε) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the coprime-tail page (⟦THE K6 PATTERN⟧: the threshold where `Ctail` is bound)⟧
    (100 * Real.log (Q : ℝ) ≤ Real.log (Xd : ℝ)) ∧
    (((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))) ∧
    (10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) ∧
    (Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) ∧
    (2688 * Ctail * Real.log (Real.log X) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the per-piece cap-free floor: only the Mertens mask debit is carried⟧
    ((0 : ℝ) ≤ Dmask) ∧
    (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (3072 * M) i)
          (calQK (AdoorL M) (3072 * M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kcf + 25
            + Dmask)
      < Real.log (Real.log X)) ∧
    -- ⟦THE SOCKET'S GATES⟧ (`m4_supplier_complete` at `Ps := 1`, `J := 2`)
    ((0 : ℝ) < cW) ∧ (cW ≤ 1 / Real.exp 1) ∧ (2 * cW < 1) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cqS (H83 X theta293) P (2 * Xd) Xd Mt kk X L cgS Cb X theta293
        (seamRad X) v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ)) ≤ 3 * X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 1 ≤ Dd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Dd v ≤ kk v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Xsk ≤ Real.sqrt (Xa v)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.sqrt (Xa v) ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.exp 1 ≤ Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((Mt v : ℕ) : ℝ) ≤ 2 * Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * Xa v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      (0 : ℝ) ≤ cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X → ∀ i : ℕ,
      ((kk v / Dd v : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa v →
        |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) ∧
    ((0 : ℝ) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cSq * caseASwide cW Cb (cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ))
          ((kk v / Dd v : ℕ) : ℝ) (Xa v)
        + cSq * ((Dd v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 / ramRbot (H83 X theta293) Xd v
      ≤ cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) / 3) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) ≤ Rbar0) ∧
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293)) ∧
    -- ⟦THE ENDPOINT⟧ (`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is the converse)
    (doorChiCoeff_L χ M Xd = 0) ∧
    -- ⟦THE CARRY: the `T₀`-band arm, at `m4_hT0band_at_door_L`'s own conclusion⟧
    ((∫ t in (-(seamT0 X))..(seamT0 X),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
      ≤ t0BandB X C₁' M₀) ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    ((0 : ℝ) ≤ π₀) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀) ∧
    (5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀) ∧
    ((Real.log X) ^ (-theta293 + ε) ≤ π₀) ∧
    (4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

set_option maxHeartbeats 4000000 in
-- the same cause as `M4DoorClose` §3: the ~99-conjunct destructuring plus the capstone's
-- ~87-argument application is what costs the heartbeats — no tactic search happens here
/-- **THE DOOR ROW'S MEAN SQUARE, CARRIED, AT THE POOL** (`m4_door_meansq_carried_pool_L`).
`M4DoorClose.m4_door_meansq_carried` at `DoorRowCarriedPool_L`: at every door instance meeting
the pooled register, the door's sieved, `χ`-twisted, UN-PHASED datum satisfies the capstone's
five-summand mean-square bound at the grade `B`.

The `∃`-bound constants are `M4DoorClose`'s, at the pooled capstone. -/
theorem m4_door_meansq_carried_pool_L :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (Qm q : ℕ) (χ : DirichletCharacter ℂ q), 0 < q → q ≤ Qm →
        ∀ (M Xd j : ℕ) (B : ℝ), 1 ≤ M → doorRowFloorL M ≤ j →
          DoorRowCarriedPool_L Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M Xd j B →
            1 / ((Xd : ℕ) : ℝ)
                * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
                    ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                        * shortSum (doorChiCoeff_L χ M)
                            (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
              ≤ B := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hgen⟩ :=
    m4_meansq_per_chi_gen_pool_L
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  -- ⟦THE SKOLEM CUT⟧ the masked-floor constant, as a function of the modulus range
  choose Kcf hKcf0 hcfl using capFreeFloor3_pieceDatum
  obtain ⟨Ctail, hCtail0, htail⟩ := m4_door_tail_supply_L
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro Qm q χ hq hqQm M Xd j B hM hj0 hcar
  obtain ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, C₁', M₀,
    cqS, cgS, cW, SW, Rbar0, Dmask, π₀,
    hXdX, hhj, hXee, hlX2, hhX, hhceil, hTann, hceil5, hT₀le, hTbot, hLXL, hLe, hL256,
    hXdQ, hP3, hlogP2, hQbot, hQlog, hQL, hPlow, hQhigh, hPQ, hQ0, hHX, hH2, hPj1, hQXd,
    hXdbig, hdom, hW5, hkth, hMtX, hC16, hRradW, hthinpin, hMtpin, hkkg, hMtY,
    hRrad0, hV1, hVδ, hlogV, hδsq, hksthr, hVJg, hCb0, hCbound, hXthr,
    hX₀k, hMfl0k, hk2, hkX, hgateW, hYpin, hWY, hXY, hthrY,
    hcqgate, hCqgate, hε0, habs,
    hQlogXd, hdomband, hlogb, hPQratio, h2688,
    hDmask0, hdebit, hcfthr,
    hc0, hce, hc1, hblk, hbox, hD1, hDk, hX₀j, hsqXa, hpin,
    hXae, hMXa, hXaX, hMfl0, hboxw, hS0, hSbd, hendGen, hRbdU, hRbar00, hRgrade,
    hend, hT0band, hcff, hpool, hgP1, hgRows, hgU, hgBand, henv⟩ := hcar
  subst hXdX
  subst hhj
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦the scale's arithmetic⟧
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hXee
  have h1ee : (1 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h1 := Real.add_one_le_exp (Real.exp 1)
    have h2 := Real.exp_pos 1
    linarith
  have hXd1 : 1 ≤ Xd := by
    have : (1 : ℝ) ≤ ((Xd : ℕ) : ℝ) := le_trans h1ee hXee
    exact_mod_cast this
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hlog1 : (1 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hLXe : Real.exp 1 ≤ Real.log ((Xd : ℕ) : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hP1 : 1 ≤ P := by omega
  have hP2 : 2 ≤ P := by omega
  -- ⟦THE LENGTH FLOOR IS FREE⟧: both `4 ≤ h` and the capstone's window gate
  have hj2 : 2 ≤ j := by
    have hA : 2 ^ 18 ≤ AdoorL M := AdoorL_ge_old hM
    have hAle : AdoorL M ≤ M * AdoorL M := Nat.le_mul_of_pos_left _ hM
    have hjf : M * AdoorL M ≤ j := hj0
    have h18 : (2 : ℕ) ≤ 2 ^ 18 := by norm_num
    omega
  have hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    have hN : (4 : ℕ) ≤ 2 ^ j := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    exact_mod_cast hN
  have hQ1h : ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) :=
    doorL_length_gate_iff.mpr hj0
  -- ⟦THE DATUM SIDE (class (C)): the cut and its three S8 slots⟧
  have haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd →
      winCutH Xd (doorChiCoeff_L χ M) n = doorChiCoeff_L χ M n :=
    fun n h1 h2 => winCutH_of_mem _ h1 h2
  have ha0 : winCutH Xd (doorChiCoeff_L χ M) Xd = 0 := winCutH_supp0 _ le_rfl
  -- ⟦the pin chain and the per-block puncture law⟧
  have hcoefPin : SeamCoefW Xd P Q (winCutH Xd (doorChiCoeff_L χ M)) (doorChiCoeff_L χ M)
      (liouChi χ) :=
    doorChiCoeff_seamCoefW_at_door_H_L χ hM hlog1 hQXd hPlow haH ha0 hend
  have hcoefBand := doorChiCoeff_seamCoefW_punct_H_L χ hM haH ha0 hend
  -- ⟦the per-piece cap-free floor⟧
  have hfloor : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (3072 * M))
        (calQK (AdoorL M) (3072 * M) M)) ((Xd : ℕ) : ℝ) := by
    intro 𝒥 h𝒥
    exact hcfl Qm q χ (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 𝒥
      ((Xd : ℕ) : ℝ) Dmask hqQm hXee hDmask0 (hdebit 𝒥 h𝒥) hcfthr
  -- ⟦THE SOCKET⟧ at `Ps := 1`, `J := 2`, read at the door datum
  have hsock0 := hsup q χ (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M)
    (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q 2 1 Mt kk Dd Xa cqS L cgS Cb
    ((Xd : ℕ) : ℝ) theta293 (seamRad ((Xd : ℕ) : ℝ)) ((Xd : ℕ) : ℝ) 0 Rbar0 cW SW
    hc0 hce hc1 hCb0 hCbound hP1 le_rfl hRrad0 theta293_pos theta293_lt_one_div_32.le
    hLXe hPlow hQhigh hPQ hfloor hblk hbox hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0
    hboxw hS0 hSbd hendGen hRbdU
  have hsockR : CofactorSocket (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q
      ((Xd : ℕ) : ℝ) (seamRad ((Xd : ℕ) : ℝ)) 0 (4 * Rbar0) (doorChiCoeff_L χ M) := by
    have hs := cofactorSocket_doorChiCoeff_L χ hsock0
    have he : (2 : ℝ) ^ (2 : ℕ) * Rbar0 = 4 * Rbar0 := by ring
    rwa [he] at hs
  -- ⟦THE COPRIME TAIL⟧: `Mtail` and `EP2` are computed, not carried
  have hNcast : (((2 * Xd : ℕ)) : ℝ) = 2 * ((Xd : ℕ) : ℝ) := by push_cast; ring
  obtain ⟨hMtail, hMtail0, hEP2⟩ := htail q χ M P Q Xd (2 * Xd) ((Xd : ℕ) : ℝ) ε
    rfl hNcast hX0 hL256 hP2 hPQ hXd1 hQlogXd hdomband hPlow hlogb habs hPQratio h2688
  -- ⟦THE CAPSTONE, AT THE POOL⟧
  have hres := hgen Qm q χ hqQm (2 * Xd) Xd P Q M (winCutH Xd (doorChiCoeff_L χ M)) (liouChi χ)
    (doorChiCoeff_L χ M)
    (fun i => memSPunctCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 i
      (liouChi χ))
    ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) δ' V VJ L Cb (seamRad ((Xd : ℕ) : ℝ)) (4 * Rbar0)
    kmin Ymax ε _ _ C₁' M₀ π₀
    rfl rfl hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe hM hXdQ hQ1h hP3
    hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkkg hMtY
    hRrad0 le_rfl le_rfl hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0k hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 habs hEP2 le_rfl
    (doorRow_ha1_L χ M Xd) (norm_liouChi_le_one χ)
    (fun n hn => doorRow_hsupp0_L χ M Xd n hn) (fun n hn => doorRow_hasupp_L χ M Xd n hn)
    hMtail0 hMtail
    (norm_doorChiCoeff_le_one_L χ M) (fun i n => norm_doorPunctCoeff_le_one_L χ M i n)
    (by positivity) hRgrade hsockR hcoefBand hcoefPin hT0band hcff hpool hgP1 hgRows hgU
    hgBand
  -- ⟦THE DATUM BRIDGE⟧ the cut is invisible to the row's short sum
  simp only [shortSum_winCutH_seamS0] at hres
  exact le_trans hres henv

/-- **THE DOOR'S DYADIC ROW, CARRIED, AT THE POOL** (`m4_dyadicRow_carried_pool_L`). -/
theorem m4_dyadicRow_carried_pool_L :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
            ∀ s ≤ H,
              DoorRowCarriedPool_L Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
                (doorLadder R.x H (i + 1) + s) j (MS j H)) →
        M4ChiDyadicRowMeanSq_L R M k MS := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_door_meansq_carried_pool_L
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro R Qm M k MS hM hQm htriv hcar H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hApos : 0 < doorLadder R.x H (i + 1) + s := by
    have := doorLadder_floor hxH (i + 1); omega
  by_cases hcase : doorRowFloorL M ≤ j
  · have hqQm : q ≤ Qm := by
      have hR : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hR
    exact hrow Qm q χ hq hqQm M (doorLadder R.x H (i + 1) + s) j (MS j H) hM hcase
      (hcar H hlo hhi q hq hqQ i hik χ j hjL hcase s hsH)
  · exact le_trans (doorRow_trivial_grade_L χ M j hApos) (htriv j H (not_le.mp hcase))

def DoorRowCarriedT0Pool_L (Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q Ddis : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε Xw cqS cgS cW SW Rbar0 Dmask π₀ : ℝ),
    -- ⟦the two pins⟧
    ((Xd : ℝ) = X) ∧ (((2 ^ j : ℕ) : ℝ) = h) ∧
    -- ⟦the scale page, at the BLOCK scale⟧
    (Real.exp (Real.exp 1) ≤ X) ∧ (Real.exp 2 ≤ Real.log X) ∧
    (h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) ∧
    (Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X) ∧
    TannGate X (2 * (X / h)) ∧ (5 ≤ Real.log (Real.log (2 * (X / h)))) ∧
    (T₀ ≤ 2 * (X / h)) ∧ (Real.exp 1 ≤ 2 * (X / h)) ∧
    (Real.log X ≤ L) ∧ (Real.exp 1 ≤ L) ∧ ((256 : ℝ) ≤ Real.log X) ∧
    -- ⟦the door and the band⟧
    (calQK (AdoorL M) (3072 * M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) i)
                (calQK (AdoorL M) (3072 * M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) i : ℕ) : ℝ)
            / Real.log ((calQK (AdoorL M) (3072 * M) M i : ℕ) : ℝ))) ∧
    -- ⟦the window floors at the witness ladder⟧
    (∀ v ∈ ramI (H83 X theta293) P Q, (5 : ℝ) ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X)
          - Real.log (Real.log (ramRbot (H83 X theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log X)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      seamRad X ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (3072 * M) 2)
          (calQK (AdoorL M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
        ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, kmin ≤ ((witKk (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((witMt (H83 X theta293) Xd v : ℕ) : ℝ) ≤ Ymax) ∧
    -- ⟦the calibration, the radius, the short-interval datum⟧
    ((0 : ℝ) < seamRad X) ∧
    ((1 : ℝ) ≤ V) ∧ (V⁻¹ ≤ δ') ∧ (Real.log V ≤ 100 * Real.log L) ∧
    (δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ))) ∧
    (656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) ∧
    (Real.exp (mrAlpha (1 / 12) 2
        * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
    ((0 : ℝ) ≤ Cb) ∧ ShortIntervalDatum Cb ∧
    (2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) ∧
    -- ⟦the `kmin`/`Ymax` ladder⟧
    (Xcap ≤ kmin) ∧ ((0 : ℝ) ≤ cofactorMfl X theta293 kmin) ∧
    ((2 : ℝ) ≤ kmin) ∧ (kmin ≤ X) ∧
    ((1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin) ∧
    (pin2Gate ≤ Ymax) ∧ (Real.log Ymax ≤ 2 * Real.log kmin) ∧
    (Real.log X ≤ Real.log Ymax) ∧
    (32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) ∧
    -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6)⟧
    (420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293)) ∧
    -- ⟦the ε-window⟧
    ((0 : ℝ) ≤ ε) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the coprime-tail page (⟦THE K6 PATTERN⟧: the threshold where `Ctail` is bound)⟧
    (100 * Real.log (Q : ℝ) ≤ Real.log (Xd : ℝ)) ∧
    (((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))) ∧
    (10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) ∧
    (Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) ∧
    (2688 * Ctail * Real.log (Real.log X) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the per-piece cap-free floor: only the Mertens mask debit is carried⟧
    ((0 : ℝ) ≤ Dmask) ∧
    (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (3072 * M) i)
          (calQK (AdoorL M) (3072 * M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kcf + 25
            + Dmask)
      < Real.log (Real.log X)) ∧
    -- ⟦THE SOCKET'S GATES⟧ (`m4_supplier_complete` at `Ps := 1`, `J := 2`)
    ((0 : ℝ) < cW) ∧ (cW ≤ 1 / Real.exp 1) ∧ (2 * cW < 1) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cqS (H83 X theta293) P (2 * Xd) Xd Mt kk X L cgS Cb X theta293
        (seamRad X) v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ)) ≤ 3 * X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 1 ≤ Dd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Dd v ≤ kk v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Xsk ≤ Real.sqrt (Xa v)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.sqrt (Xa v) ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.exp 1 ≤ Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((Mt v : ℕ) : ℝ) ≤ 2 * Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * Xa v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      (0 : ℝ) ≤ cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X → ∀ i : ℕ,
      ((kk v / Dd v : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa v →
        |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) ∧
    ((0 : ℝ) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cSq * caseASwide cW Cb (cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ))
          ((kk v / Dd v : ℕ) : ℝ) (Xa v)
        + cSq * ((Dd v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 / ramRbot (H83 X theta293) Xd v
      ≤ cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) / 3) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) ≤ Rbar0) ∧
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293)) ∧
    -- ⟦THE ENDPOINT⟧ (`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is the converse)
    (doorChiCoeff_L χ M Xd = 0) ∧
    -- ⟦ARM 1 DISCHARGED: the T₀-band gates, not the T₀-band integral⟧
    DoorRowT0Gates Kbox X₀w q Ddis X Xw Dmask ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    ((0 : ℝ) ≤ π₀) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀) ∧
    (5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀) ∧
    ((Real.log X) ^ (-theta293 + ε) ≤ π₀) ∧
    (4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * (cfbC₁ X (t0dC1_L Cb)) ^ 2 * Real.exp (-(1 / Real.exp 1) * t0dM0 X)
        + 1787702400 * a2Level1_L M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

set_option maxHeartbeats 4000000 in
-- the same cause as `M4T0Discharge.doorRowCarried_of_t0free`: two ~99-conjunct registers are
-- elaborated against each other; no tactic search happens, every step is a projection
/-- **THE BRIDGE, AT THE POOL** (`doorRowCarried_of_t0free_pool_L`).
`M4T0Discharge.doorRowCarried_of_t0free` at the pooled pair. -/
theorem doorRowCarried_of_t0free_pool_L (Qm : ℕ) :
    ∃ Kbox X₀w : ℝ, 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ) (q : ℕ) [NeZero q]
        (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ), q ≤ Qm →
        DoorRowCarriedT0Pool_L Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B →
          DoorRowCarriedPool_L Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hdis⟩ := m4_t0band_discharged_L Qm
  refine ⟨Kbox, X₀w, hK0, hX₀0, ?_⟩
  intro Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail q _ χ M Xd j B hq hfree
  obtain ⟨P, Q, Ddis, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, Xw, cqS, cgS, cW,
    SW, Rbar0, Dmask, π₀, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33,
    d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49, d50, d51,
    d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67, d68, d69,
    d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85, d86, d87,
    d88, d89, d90, d91, d92, d93, d94, d95, d96, d97, d98, d99⟩ := hfree
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := d92
  have hT0 : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
        ≤ t0BandB X (cfbC₁ X (t0dC1_L Cb)) (t0dM0 X) :=
    hdis q χ M Xd Ddis X Xw Cb Dmask hq g1 d1 g2 g3 g4 g5 d46 d47 d68 g6 g7 g8
  exact ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, cfbC₁ X (t0dC1_L Cb),
    t0dM0 X, cqS, cgS, cW, SW, Rbar0, Dmask, π₀, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11,
    d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29,
    d30, d31, d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47,
    d48, d49, d50, d51, d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65,
    d66, d67, d68, d69, d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83,
    d84, d85, d86, d87, d88, d89, d90, d91, hT0, d93, d94, d95, d96, d97, d98, d99⟩

set_option maxHeartbeats 1600000 in
-- `m4_wave_structurally_closed_L`'s own budget: the register mentions `DoorRowCarriedPool_L`
-- under six binders, and that is the whole cost
theorem m4_wave_structurally_closed_pool_L (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            -- ⟦the modulus cap: the door's characters inside the capstone's range⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            -- ⟦the small lengths' trivial grade⟧
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            -- ⟦ARM 1 + the regime gates: the per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedPool_L Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            -- ⟦R2's two gates⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦ARM 2: the coprime supply, interval/length-general⟧
            M4CoprimeBlockMeanSq_L R M
              (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_dyadicRow_carried_pool_L
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_dyadicRow_L
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl Qm, Xsk, Kcf Qm, Ctail,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl Qm, hXsk0, hKcf0 Qm, hCtail0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcar hgate harc hcp
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H)
      (fun H => 2 * MStr H) H := fun H =>
    m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
  -- ⟦R2⟧ the wave asks only the NON-COPRIME classes; `m4_nonCoprime_classMeanSq_L` delivers all
  have hnc : M4ClassBlockMeanSq_L R M k
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_nonCoprime_classMeanSq_L (k := k) hM hBcl0 hgate harc hcp
  refine hR δ Braw MS MSan MStr (doorRowFloorL M) M k hgates hMSan0 hMStr0 hBraw0 han htr
    hdrift hdel hrest (hrow R Qm M k MS hM hQm htriv hcar) ?_
  intro H hlo hhi q hq hqQ i hik r hrq _hncop
  exact hnc H hlo hhi q hq hqQ i hik r hrq

set_option maxHeartbeats 1600000 in
-- `m4_wave_closed_T0_discharged_L`'s own budget, at the pooled register
theorem m4_wave_closed_T0_discharged_pool_L (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            -- ⟦ARM 1 DISCHARGED: the T₀-free per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0Pool_L Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦ARM 2: the coprime supply, interval/length-general — the ONLY analytic carry left⟧
            M4CoprimeBlockMeanSq_L R M
              (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hbridge⟩ := doorRowCarried_of_t0free_pool_L Qm
  obtain ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hmain⟩ :=
    m4_wave_structurally_closed_pool_L Qm
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcar hgate harc hcp
  refine hR δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv ?_ hgate harc hcp
  intro H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH
  haveI : NeZero q := ⟨by omega⟩
  have hqQm : q ≤ Qm := by
    have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
    exact_mod_cast hRq
  exact hbridge Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail q χ M
    (doorLadder R.x H (i + 1) + s) j (MS j H) hqQm
    (hcar H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH)

def DoorRowCarriedJoin_L (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε C₁' M₀ cqS cgS cW SW Rbar0 Dmask π₀ : ℝ),
    -- ⟦the two pins⟧
    ((Xd : ℝ) = X) ∧ (((2 ^ j : ℕ) : ℝ) = h) ∧
    -- ⟦the scale page, at the BLOCK scale⟧
    (Real.exp (Real.exp 1) ≤ X) ∧ (Real.exp 2 ≤ Real.log X) ∧
    (h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) ∧
    (Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X) ∧
    TannGate X (2 * (X / h)) ∧ (5 ≤ Real.log (Real.log (2 * (X / h)))) ∧
    (T₀ ≤ 2 * (X / h)) ∧ (Real.exp 1 ≤ 2 * (X / h)) ∧
    (Real.log X ≤ L) ∧ (Real.exp 1 ≤ L) ∧ ((256 : ℝ) ≤ Real.log X) ∧
    -- ⟦the door and the band⟧
    (calQK (AdoorL M) (3072 * M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) i)
                (calQK (AdoorL M) (3072 * M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) i : ℕ) : ℝ)
            / Real.log ((calQK (AdoorL M) (3072 * M) M i : ℕ) : ℝ))) ∧
    -- ⟦the window floors at the witness ladder⟧
    (∀ v ∈ ramI (H83 X theta293) P Q, (5 : ℝ) ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X)
          - Real.log (Real.log (ramRbot (H83 X theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log X)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      seamRad X ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (3072 * M) 2)
          (calQK (AdoorL M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
        ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, kmin ≤ ((witKk (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((witMt (H83 X theta293) Xd v : ℕ) : ℝ) ≤ Ymax) ∧
    -- ⟦the calibration, the radius, the short-interval datum⟧
    ((0 : ℝ) < seamRad X) ∧
    ((1 : ℝ) ≤ V) ∧ (V⁻¹ ≤ δ') ∧ (Real.log V ≤ 100 * Real.log L) ∧
    (δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ))) ∧
    (656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) ∧
    (Real.exp (mrAlpha (1 / 12) 2
        * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
    ((0 : ℝ) ≤ Cb) ∧ ShortIntervalDatum Cb ∧
    (2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) ∧
    -- ⟦the `kmin`/`Ymax` ladder⟧
    (Xcap ≤ kmin) ∧ ((0 : ℝ) ≤ cofactorMfl X theta293 kmin) ∧
    ((2 : ℝ) ≤ kmin) ∧ (kmin ≤ X) ∧
    ((1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin) ∧
    (pin2Gate ≤ Ymax) ∧ (Real.log Ymax ≤ 2 * Real.log kmin) ∧
    (Real.log X ≤ Real.log Ymax) ∧
    (32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) ∧
    -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6)⟧
    (420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293)) ∧
    -- ⟦the ε-window⟧
    ((0 : ℝ) ≤ ε) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the coprime-tail page (⟦THE K6 PATTERN⟧: the threshold where `Ctail` is bound)⟧
    (100 * Real.log (Q : ℝ) ≤ Real.log (Xd : ℝ)) ∧
    (((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))) ∧
    (10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) ∧
    (Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) ∧
    (2688 * Ctail * Real.log (Real.log X) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the per-piece cap-free floor: only the Mertens mask debit is carried⟧
    ((0 : ℝ) ≤ Dmask) ∧
    (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (3072 * M) i)
          (calQK (AdoorL M) (3072 * M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kcf + 25
            + Dmask)
      < Real.log (Real.log X)) ∧
    -- ⟦THE SOCKET'S GATES⟧ (`m4_supplier_complete` at `Ps := 1`, `J := 2`)
    ((0 : ℝ) < cW) ∧ (cW ≤ 1 / Real.exp 1) ∧ (2 * cW < 1) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cqS (H83 X theta293) P (2 * Xd) Xd Mt kk X L cgS Cb X theta293
        (seamRad X) v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ)) ≤ 3 * X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 1 ≤ Dd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Dd v ≤ kk v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Xsk ≤ Real.sqrt (Xa v)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.sqrt (Xa v) ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.exp 1 ≤ Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((Mt v : ℕ) : ℝ) ≤ 2 * Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * Xa v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      (0 : ℝ) ≤ cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X → ∀ i : ℕ,
      ((kk v / Dd v : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa v →
        |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) ∧
    ((0 : ℝ) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cSq * caseASwide cW Cb (cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ))
          ((kk v / Dd v : ℕ) : ℝ) (Xa v)
        + cSq * ((Dd v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 / ramRbot (H83 X theta293) Xd v
      ≤ cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) / 3) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) ≤ Rbar0) ∧
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293)) ∧
    -- ⟦THE ENDPOINT⟧ (`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is the converse)
    (doorChiCoeff_L χ M Xd = 0) ∧
    -- ⟦THE CARRY: the `T₀`-band arm, at `m4_hT0band_at_door_L`'s own conclusion⟧
    ((∫ t in (-(seamT0 X))..(seamT0 X),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
      ≤ t0BandB X C₁' M₀) ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    ((0 : ℝ) ≤ π₀) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀) ∧
    (5760 * (a2RowsSum'_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀) ∧
    ((Real.log X) ^ (-theta293 + ε) ≤ π₀) ∧
    (4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

set_option maxHeartbeats 4000000 in
-- the same cause as §2, at the joined capstone
theorem m4_door_meansq_carried_join_L :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (Qm q : ℕ) (χ : DirichletCharacter ℂ q), 0 < q → q ≤ Qm →
        ∀ (M Xd j : ℕ) (B : ℝ), 1 ≤ M → doorRowFloorL M ≤ j →
          DoorRowCarriedJoin_L Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M Xd j B →
            1 / ((Xd : ℕ) : ℝ)
                * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
                    ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                        * shortSum (doorChiCoeff_L χ M)
                            (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
              ≤ B := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hgen⟩ :=
    m4_meansq_per_chi_gen_join_L
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  -- ⟦THE SKOLEM CUT⟧ the masked-floor constant, as a function of the modulus range
  choose Kcf hKcf0 hcfl using capFreeFloor3_pieceDatum
  obtain ⟨Ctail, hCtail0, htail⟩ := m4_door_tail_supply_L
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro Qm q χ hq hqQm M Xd j B hM hj0 hcar
  obtain ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, C₁', M₀,
    cqS, cgS, cW, SW, Rbar0, Dmask, π₀,
    hXdX, hhj, hXee, hlX2, hhX, hhceil, hTann, hceil5, hT₀le, hTbot, hLXL, hLe, hL256,
    hXdQ, hP3, hlogP2, hQbot, hQlog, hQL, hPlow, hQhigh, hPQ, hQ0, hHX, hH2, hPj1, hQXd,
    hXdbig, hdom, hW5, hkth, hMtX, hC16, hRradW, hthinpin, hMtpin, hkkg, hMtY,
    hRrad0, hV1, hVδ, hlogV, hδsq, hksthr, hVJg, hCb0, hCbound, hXthr,
    hX₀k, hMfl0k, hk2, hkX, hgateW, hYpin, hWY, hXY, hthrY,
    hcqgate, hCqgate, hε0, habs,
    hQlogXd, hdomband, hlogb, hPQratio, h2688,
    hDmask0, hdebit, hcfthr,
    hc0, hce, hc1, hblk, hbox, hD1, hDk, hX₀j, hsqXa, hpin,
    hXae, hMXa, hXaX, hMfl0, hboxw, hS0, hSbd, hendGen, hRbdU, hRbar00, hRgrade,
    hend, hT0band, hcff, hpool, hgP1, hgRows, hgU, hgBand, henv⟩ := hcar
  subst hXdX
  subst hhj
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦the scale's arithmetic⟧
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hXee
  have h1ee : (1 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h1 := Real.add_one_le_exp (Real.exp 1)
    have h2 := Real.exp_pos 1
    linarith
  have hXd1 : 1 ≤ Xd := by
    have : (1 : ℝ) ≤ ((Xd : ℕ) : ℝ) := le_trans h1ee hXee
    exact_mod_cast this
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hlog1 : (1 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hLXe : Real.exp 1 ≤ Real.log ((Xd : ℕ) : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hP1 : 1 ≤ P := by omega
  have hP2 : 2 ≤ P := by omega
  -- ⟦THE LENGTH FLOOR IS FREE⟧: both `4 ≤ h` and the capstone's window gate
  have hj2 : 2 ≤ j := by
    have hA : 2 ^ 18 ≤ AdoorL M := AdoorL_ge_old hM
    have hAle : AdoorL M ≤ M * AdoorL M := Nat.le_mul_of_pos_left _ hM
    have hjf : M * AdoorL M ≤ j := hj0
    have h18 : (2 : ℕ) ≤ 2 ^ 18 := by norm_num
    omega
  have hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    have hN : (4 : ℕ) ≤ 2 ^ j := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    exact_mod_cast hN
  have hQ1h : ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) :=
    doorL_length_gate_iff.mpr hj0
  -- ⟦THE DATUM SIDE (class (C)): the cut and its three S8 slots⟧
  have haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd →
      winCutH Xd (doorChiCoeff_L χ M) n = doorChiCoeff_L χ M n :=
    fun n h1 h2 => winCutH_of_mem _ h1 h2
  have ha0 : winCutH Xd (doorChiCoeff_L χ M) Xd = 0 := winCutH_supp0 _ le_rfl
  -- ⟦the pin chain and the per-block puncture law⟧
  have hcoefPin : SeamCoefW Xd P Q (winCutH Xd (doorChiCoeff_L χ M)) (doorChiCoeff_L χ M)
      (liouChi χ) :=
    doorChiCoeff_seamCoefW_at_door_H_L χ hM hlog1 hQXd hPlow haH ha0 hend
  have hcoefBand := doorChiCoeff_seamCoefW_punct_H_L χ hM haH ha0 hend
  -- ⟦the per-piece cap-free floor⟧
  have hfloor : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (3072 * M))
        (calQK (AdoorL M) (3072 * M) M)) ((Xd : ℕ) : ℝ) := by
    intro 𝒥 h𝒥
    exact hcfl Qm q χ (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 𝒥
      ((Xd : ℕ) : ℝ) Dmask hqQm hXee hDmask0 (hdebit 𝒥 h𝒥) hcfthr
  -- ⟦THE SOCKET⟧ at `Ps := 1`, `J := 2`, read at the door datum
  have hsock0 := hsup q χ (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M)
    (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q 2 1 Mt kk Dd Xa cqS L cgS Cb
    ((Xd : ℕ) : ℝ) theta293 (seamRad ((Xd : ℕ) : ℝ)) ((Xd : ℕ) : ℝ) 0 Rbar0 cW SW
    hc0 hce hc1 hCb0 hCbound hP1 le_rfl hRrad0 theta293_pos theta293_lt_one_div_32.le
    hLXe hPlow hQhigh hPQ hfloor hblk hbox hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0
    hboxw hS0 hSbd hendGen hRbdU
  have hsockR : CofactorSocket (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q
      ((Xd : ℕ) : ℝ) (seamRad ((Xd : ℕ) : ℝ)) 0 (4 * Rbar0) (doorChiCoeff_L χ M) := by
    have hs := cofactorSocket_doorChiCoeff_L χ hsock0
    have he : (2 : ℝ) ^ (2 : ℕ) * Rbar0 = 4 * Rbar0 := by ring
    rwa [he] at hs
  -- ⟦THE COPRIME TAIL⟧: `Mtail` and `EP2` are computed, not carried
  have hNcast : (((2 * Xd : ℕ)) : ℝ) = 2 * ((Xd : ℕ) : ℝ) := by push_cast; ring
  obtain ⟨hMtail, hMtail0, hEP2⟩ := htail q χ M P Q Xd (2 * Xd) ((Xd : ℕ) : ℝ) ε
    rfl hNcast hX0 hL256 hP2 hPQ hXd1 hQlogXd hdomband hPlow hlogb habs hPQratio h2688
  -- ⟦THE CAPSTONE, AT THE POOL⟧
  have hres := hgen Qm q χ hqQm (2 * Xd) Xd P Q M (winCutH Xd (doorChiCoeff_L χ M)) (liouChi χ)
    (doorChiCoeff_L χ M)
    (fun i => memSPunctCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 i
      (liouChi χ))
    ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) δ' V VJ L Cb (seamRad ((Xd : ℕ) : ℝ)) (4 * Rbar0)
    kmin Ymax ε _ _ C₁' M₀ π₀
    rfl rfl hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe hM hXdQ hQ1h hP3
    hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkkg hMtY
    hRrad0 le_rfl le_rfl hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0k hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 habs hEP2 le_rfl
    (doorRow_ha1_L χ M Xd) (norm_liouChi_le_one χ)
    (fun n hn => doorRow_hsupp0_L χ M Xd n hn) (fun n hn => doorRow_hasupp_L χ M Xd n hn)
    hMtail0 hMtail
    (norm_doorChiCoeff_le_one_L χ M) (fun i n => norm_doorPunctCoeff_le_one_L χ M i n)
    (by positivity) hRgrade hsockR hcoefBand hcoefPin hT0band hcff hpool hgP1 hgRows hgU
    hgBand
  -- ⟦THE DATUM BRIDGE⟧ the cut is invisible to the row's short sum
  simp only [shortSum_winCutH_seamS0] at hres
  exact le_trans hres henv

theorem m4_dyadicRow_carried_join_L :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
            ∀ s ≤ H,
              DoorRowCarriedJoin_L Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
                (doorLadder R.x H (i + 1) + s) j (MS j H)) →
        M4ChiDyadicRowMeanSq_L R M k MS := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_door_meansq_carried_join_L
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro R Qm M k MS hM hQm htriv hcar H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hApos : 0 < doorLadder R.x H (i + 1) + s := by
    have := doorLadder_floor hxH (i + 1); omega
  by_cases hcase : doorRowFloorL M ≤ j
  · have hqQm : q ≤ Qm := by
      have hR : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hR
    exact hrow Qm q χ hq hqQm M (doorLadder R.x H (i + 1) + s) j (MS j H) hM hcase
      (hcar H hlo hhi q hq hqQ i hik χ j hjL hcase s hsH)
  · exact le_trans (doorRow_trivial_grade_L χ M j hApos) (htriv j H (not_le.mp hcase))

def DoorRowCarriedT0Join_L (Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q Ddis : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε Xw cqS cgS cW SW Rbar0 Dmask π₀ : ℝ),
    -- ⟦the two pins⟧
    ((Xd : ℝ) = X) ∧ (((2 ^ j : ℕ) : ℝ) = h) ∧
    -- ⟦the scale page, at the BLOCK scale⟧
    (Real.exp (Real.exp 1) ≤ X) ∧ (Real.exp 2 ≤ Real.log X) ∧
    (h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) ∧
    (Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X) ∧
    TannGate X (2 * (X / h)) ∧ (5 ≤ Real.log (Real.log (2 * (X / h)))) ∧
    (T₀ ≤ 2 * (X / h)) ∧ (Real.exp 1 ≤ 2 * (X / h)) ∧
    (Real.log X ≤ L) ∧ (Real.exp 1 ≤ L) ∧ ((256 : ℝ) ≤ Real.log X) ∧
    -- ⟦the door and the band⟧
    (calQK (AdoorL M) (3072 * M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) i)
                (calQK (AdoorL M) (3072 * M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) i : ℕ) : ℝ)
            / Real.log ((calQK (AdoorL M) (3072 * M) M i : ℕ) : ℝ))) ∧
    -- ⟦the window floors at the witness ladder⟧
    (∀ v ∈ ramI (H83 X theta293) P Q, (5 : ℝ) ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X)
          - Real.log (Real.log (ramRbot (H83 X theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log X)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      seamRad X ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (3072 * M) 2)
          (calQK (AdoorL M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
        ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, kmin ≤ ((witKk (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((witMt (H83 X theta293) Xd v : ℕ) : ℝ) ≤ Ymax) ∧
    -- ⟦the calibration, the radius, the short-interval datum⟧
    ((0 : ℝ) < seamRad X) ∧
    ((1 : ℝ) ≤ V) ∧ (V⁻¹ ≤ δ') ∧ (Real.log V ≤ 100 * Real.log L) ∧
    (δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ))) ∧
    (656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) ∧
    (Real.exp (mrAlpha (1 / 12) 2
        * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
    ((0 : ℝ) ≤ Cb) ∧ ShortIntervalDatum Cb ∧
    (2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) ∧
    -- ⟦the `kmin`/`Ymax` ladder⟧
    (Xcap ≤ kmin) ∧ ((0 : ℝ) ≤ cofactorMfl X theta293 kmin) ∧
    ((2 : ℝ) ≤ kmin) ∧ (kmin ≤ X) ∧
    ((1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin) ∧
    (pin2Gate ≤ Ymax) ∧ (Real.log Ymax ≤ 2 * Real.log kmin) ∧
    (Real.log X ≤ Real.log Ymax) ∧
    (32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) ∧
    -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6)⟧
    (420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293)) ∧
    -- ⟦the ε-window⟧
    ((0 : ℝ) ≤ ε) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the coprime-tail page (⟦THE K6 PATTERN⟧: the threshold where `Ctail` is bound)⟧
    (100 * Real.log (Q : ℝ) ≤ Real.log (Xd : ℝ)) ∧
    (((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))) ∧
    (10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) ∧
    (Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) ∧
    (2688 * Ctail * Real.log (Real.log X) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the per-piece cap-free floor: only the Mertens mask debit is carried⟧
    ((0 : ℝ) ≤ Dmask) ∧
    (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (3072 * M) i)
          (calQK (AdoorL M) (3072 * M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kcf + 25
            + Dmask)
      < Real.log (Real.log X)) ∧
    -- ⟦THE SOCKET'S GATES⟧ (`m4_supplier_complete` at `Ps := 1`, `J := 2`)
    ((0 : ℝ) < cW) ∧ (cW ≤ 1 / Real.exp 1) ∧ (2 * cW < 1) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cqS (H83 X theta293) P (2 * Xd) Xd Mt kk X L cgS Cb X theta293
        (seamRad X) v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ)) ≤ 3 * X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 1 ≤ Dd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Dd v ≤ kk v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Xsk ≤ Real.sqrt (Xa v)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.sqrt (Xa v) ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.exp 1 ≤ Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((Mt v : ℕ) : ℝ) ≤ 2 * Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * Xa v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      (0 : ℝ) ≤ cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X → ∀ i : ℕ,
      ((kk v / Dd v : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa v →
        |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) ∧
    ((0 : ℝ) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cSq * caseASwide cW Cb (cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ))
          ((kk v / Dd v : ℕ) : ℝ) (Xa v)
        + cSq * ((Dd v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 / ramRbot (H83 X theta293) Xd v
      ≤ cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) / 3) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) ≤ Rbar0) ∧
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293)) ∧
    -- ⟦THE ENDPOINT⟧ (`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is the converse)
    (doorChiCoeff_L χ M Xd = 0) ∧
    -- ⟦ARM 1 DISCHARGED: the T₀-band gates, not the T₀-band integral⟧
    DoorRowT0Gates Kbox X₀w q Ddis X Xw Dmask ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    ((0 : ℝ) ≤ π₀) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀) ∧
    (5760 * (a2RowsSum'_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀) ∧
    ((Real.log X) ^ (-theta293 + ε) ≤ π₀) ∧
    (4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * (cfbC₁ X (t0dC1_L Cb)) ^ 2 * Real.exp (-(1 / Real.exp 1) * t0dM0 X)
        + 1787702400 * a2Level1_L M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

set_option maxHeartbeats 4000000 in
-- the same cause as `M4T0Discharge.doorRowCarried_of_t0free`: two ~99-conjunct registers are
-- elaborated against each other; no tactic search happens, every step is a projection
/-- **THE BRIDGE, AT THE JOIN** (`doorRowCarried_of_t0free_join_L`).
`M4T0Discharge.doorRowCarried_of_t0free` at the JOINED pair.  The conjunct COUNT is
unchanged from §4 (the `a2RowsSum_L` → `a2RowsSum'_L` swap is a value swap inside conjunct 96),
so the destructure indices `d1 … d99` and the discharge's reads `d46 d47 d68` are §4's
verbatim. -/
theorem doorRowCarried_of_t0free_join_L (Qm : ℕ) :
    ∃ Kbox X₀w : ℝ, 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ) (q : ℕ) [NeZero q]
        (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ), q ≤ Qm →
        DoorRowCarriedT0Join_L Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B →
          DoorRowCarriedJoin_L Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hdis⟩ := m4_t0band_discharged_L Qm
  refine ⟨Kbox, X₀w, hK0, hX₀0, ?_⟩
  intro Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail q _ χ M Xd j B hq hfree
  obtain ⟨P, Q, Ddis, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, Xw, cqS, cgS, cW,
    SW, Rbar0, Dmask, π₀, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33,
    d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49, d50, d51,
    d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67, d68, d69,
    d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85, d86, d87,
    d88, d89, d90, d91, d92, d93, d94, d95, d96, d97, d98, d99⟩ := hfree
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := d92
  have hT0 : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
        ≤ t0BandB X (cfbC₁ X (t0dC1_L Cb)) (t0dM0 X) :=
    hdis q χ M Xd Ddis X Xw Cb Dmask hq g1 d1 g2 g3 g4 g5 d46 d47 d68 g6 g7 g8
  exact ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, cfbC₁ X (t0dC1_L Cb),
    t0dM0 X, cqS, cgS, cW, SW, Rbar0, Dmask, π₀, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11,
    d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29,
    d30, d31, d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47,
    d48, d49, d50, d51, d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65,
    d66, d67, d68, d69, d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83,
    d84, d85, d86, d87, d88, d89, d90, d91, hT0, d93, d94, d95, d96, d97, d98, d99⟩

set_option maxHeartbeats 1600000 in
-- `m4_wave_structurally_closed_L`'s own budget: the register mentions `DoorRowCarriedJoin_L`
-- under six binders, and that is the whole cost
theorem m4_wave_structurally_closed_join_L (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            -- ⟦the modulus cap: the door's characters inside the capstone's range⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            -- ⟦the small lengths' trivial grade⟧
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            -- ⟦ARM 1 + the regime gates: the per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedJoin_L Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            -- ⟦R2's two gates⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦ARM 2: the coprime supply, interval/length-general⟧
            M4CoprimeBlockMeanSq_L R M
              (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_dyadicRow_carried_join_L
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_dyadicRow_L
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl Qm, Xsk, Kcf Qm, Ctail,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl Qm, hXsk0, hKcf0 Qm, hCtail0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcar hgate harc hcp
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H)
      (fun H => 2 * MStr H) H := fun H =>
    m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
  -- ⟦R2⟧ the wave asks only the NON-COPRIME classes; `m4_nonCoprime_classMeanSq_L` delivers all
  have hnc : M4ClassBlockMeanSq_L R M k
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_nonCoprime_classMeanSq_L (k := k) hM hBcl0 hgate harc hcp
  refine hR δ Braw MS MSan MStr (doorRowFloorL M) M k hgates hMSan0 hMStr0 hBraw0 han htr
    hdrift hdel hrest (hrow R Qm M k MS hM hQm htriv hcar) ?_
  intro H hlo hhi q hq hqQ i hik r hrq _hncop
  exact hnc H hlo hhi q hq hqQ i hik r hrq

set_option maxHeartbeats 1600000 in
-- `m4_wave_closed_T0_discharged_L`'s own budget, at the joined register
theorem m4_wave_closed_T0_discharged_join_L (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            -- ⟦ARM 1 DISCHARGED: the T₀-free per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0Join_L Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦ARM 2: the coprime supply, interval/length-general — the ONLY analytic carry left⟧
            M4CoprimeBlockMeanSq_L R M
              (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hbridge⟩ := doorRowCarried_of_t0free_join_L Qm
  obtain ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hmain⟩ :=
    m4_wave_structurally_closed_join_L Qm
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcar hgate harc hcp
  refine hR δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv ?_ hgate harc hcp
  intro H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH
  haveI : NeZero q := ⟨by omega⟩
  have hqQm : q ≤ Qm := by
    have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
    exact_mod_cast hRq
  exact hbridge Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail q χ M
    (doorLadder R.x H (i + 1) + s) j (MS j H) hqQm
    (hcar H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH)

/-- **THE DOOR ROW'S CARRIED REGISTER, AT THE POOL, AT THE G-LEVER**
(`DoorRowCarriedPool_L_gk`).  `a2RowsSum_L M Xd`, `a2Level1_L M`, `calH (H1doorL M)` and
`doorRowFloorL M` are LEVEL 1 / `G`-free and keep their landed names.  The `gRows` conjunct is
the ONE that moves: `M4MeanSqPool.m4_meansq_per_chi_gen_pool_gk` reads it at
`ThmA2.a2RowsSum_gk`, so the register supplies it there.  Since `a2RowsSum_L_gk ≤ a2RowsSum_L`
(`ThmA2.a2RowsSum_gk_le`) this is a WEAKER conjunct than the landed one — the register asks
less, so the theorem it feeds is stronger, and the polarity is the safe way round. -/
def DoorRowCarriedPool_L_gk (K : ℕ) (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε C₁' M₀ cqS cgS cW SW Rbar0 Dmask π₀ : ℝ),
    -- ⟦the two pins⟧
    ((Xd : ℝ) = X) ∧ (((2 ^ j : ℕ) : ℝ) = h) ∧
    -- ⟦the scale page, at the BLOCK scale⟧
    (Real.exp (Real.exp 1) ≤ X) ∧ (Real.exp 2 ≤ Real.log X) ∧
    (h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) ∧
    (Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X) ∧
    TannGate X (2 * (X / h)) ∧ (5 ≤ Real.log (Real.log (2 * (X / h)))) ∧
    (T₀ ≤ 2 * (X / h)) ∧ (Real.exp 1 ≤ 2 * (X / h)) ∧
    (Real.log X ≤ L) ∧ (Real.exp 1 ≤ L) ∧ ((256 : ℝ) ≤ Real.log X) ∧
    -- ⟦the door and the band⟧
    (calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) i)
                (calQK (AdoorL M) (s13GK K M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) i : ℕ) : ℝ)
            / Real.log ((calQK (AdoorL M) (s13GK K M) M i : ℕ) : ℝ))) ∧
    -- ⟦the window floors at the witness ladder⟧
    (∀ v ∈ ramI (H83 X theta293) P Q, (5 : ℝ) ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X)
          - Real.log (Real.log (ramRbot (H83 X theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log X)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      seamRad X ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
          (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
        ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, kmin ≤ ((witKk (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((witMt (H83 X theta293) Xd v : ℕ) : ℝ) ≤ Ymax) ∧
    -- ⟦the calibration, the radius, the short-interval datum⟧
    ((0 : ℝ) < seamRad X) ∧
    ((1 : ℝ) ≤ V) ∧ (V⁻¹ ≤ δ') ∧ (Real.log V ≤ 100 * Real.log L) ∧
    (δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ))) ∧
    (656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) ∧
    (Real.exp (mrAlpha (1 / 12) 2
        * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
    ((0 : ℝ) ≤ Cb) ∧ ShortIntervalDatum Cb ∧
    (2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) ∧
    -- ⟦the `kmin`/`Ymax` ladder⟧
    (Xcap ≤ kmin) ∧ ((0 : ℝ) ≤ cofactorMfl X theta293 kmin) ∧
    ((2 : ℝ) ≤ kmin) ∧ (kmin ≤ X) ∧
    ((1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin) ∧
    (pin2Gate ≤ Ymax) ∧ (Real.log Ymax ≤ 2 * Real.log kmin) ∧
    (Real.log X ≤ Real.log Ymax) ∧
    (32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) ∧
    -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6)⟧
    (420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293)) ∧
    -- ⟦the ε-window⟧
    ((0 : ℝ) ≤ ε) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the coprime-tail page (⟦THE K6 PATTERN⟧: the threshold where `Ctail` is bound)⟧
    (100 * Real.log (Q : ℝ) ≤ Real.log (Xd : ℝ)) ∧
    (((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))) ∧
    (10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) ∧
    (Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) ∧
    (2688 * Ctail * Real.log (Real.log X) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the per-piece cap-free floor: only the Mertens mask debit is carried⟧
    ((0 : ℝ) ≤ Dmask) ∧
    (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (s13GK K M) i)
          (calQK (AdoorL M) (s13GK K M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kcf + 25
            + Dmask)
      < Real.log (Real.log X)) ∧
    -- ⟦THE SOCKET'S GATES⟧ (`m4_supplier_complete` at `Ps := 1`, `J := 2`)
    ((0 : ℝ) < cW) ∧ (cW ≤ 1 / Real.exp 1) ∧ (2 * cW < 1) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cqS (H83 X theta293) P (2 * Xd) Xd Mt kk X L cgS Cb X theta293
        (seamRad X) v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ)) ≤ 3 * X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 1 ≤ Dd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Dd v ≤ kk v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Xsk ≤ Real.sqrt (Xa v)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.sqrt (Xa v) ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.exp 1 ≤ Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((Mt v : ℕ) : ℝ) ≤ 2 * Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * Xa v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      (0 : ℝ) ≤ cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X → ∀ i : ℕ,
      ((kk v / Dd v : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa v →
        |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) ∧
    ((0 : ℝ) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cSq * caseASwide cW Cb (cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ))
          ((kk v / Dd v : ℕ) : ℝ) (Xa v)
        + cSq * ((Dd v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 / ramRbot (H83 X theta293) Xd v
      ≤ cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) / 3) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) ≤ Rbar0) ∧
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293)) ∧
    -- ⟦THE ENDPOINT⟧ (`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is the converse)
    (doorChiCoeff_L_gk K χ M Xd = 0) ∧
    -- ⟦THE CARRY: the `T₀`-band arm, at `m4_hT0band_at_door_L`'s own conclusion⟧
    ((∫ t in (-(seamT0 X))..(seamT0 X),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
      ≤ t0BandB X C₁' M₀) ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    ((0 : ℝ) ≤ π₀) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀) ∧
    (5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀) ∧
    ((Real.log X) ^ (-theta293 + ε) ≤ π₀) ∧
    (4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

set_option maxHeartbeats 4000000 in
/-- **THE DOOR ROW'S MEAN SQUARE, CARRIED, AT THE POOL, AT THE G-LEVER**
(`m4_door_meansq_carried_pool_L_gk`).  Capstone: `M4MeanSqPool.m4_meansq_per_chi_gen_pool_gk`,
whence `K ≤ 1.7·10⁸`.  `m4_supplier_complete` and `capFreeFloor3_pieceDatum` are
`(Pseq, Qseq)`-generic and are reused verbatim. -/
theorem m4_door_meansq_carried_pool_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (Qm q : ℕ) (χ : DirichletCharacter ℂ q), 0 < q → q ≤ Qm →
        ∀ (M Xd j : ℕ) (B : ℝ), 1 ≤ M → doorRowFloorL M ≤ j →
          DoorRowCarriedPool_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M Xd j B →
            1 / ((Xd : ℕ) : ℝ)
                * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
                    ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                        * shortSum (doorChiCoeff_L_gk K χ M)
                            (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
              ≤ B := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hgen⟩ :=
    m4_meansq_per_chi_gen_pool_L_gk K hK
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  -- ⟦THE SKOLEM CUT⟧ the masked-floor constant, as a function of the modulus range
  choose Kcf hKcf0 hcfl using capFreeFloor3_pieceDatum
  obtain ⟨Ctail, hCtail0, htail⟩ := m4_door_tail_supply_L_gk K
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro Qm q χ hq hqQm M Xd j B hM hj0 hcar
  obtain ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, C₁', M₀,
    cqS, cgS, cW, SW, Rbar0, Dmask, π₀,
    hXdX, hhj, hXee, hlX2, hhX, hhceil, hTann, hceil5, hT₀le, hTbot, hLXL, hLe, hL256,
    hXdQ, hP3, hlogP2, hQbot, hQlog, hQL, hPlow, hQhigh, hPQ, hQ0, hHX, hH2, hPj1, hQXd,
    hXdbig, hdom, hW5, hkth, hMtX, hC16, hRradW, hthinpin, hMtpin, hkkg, hMtY,
    hRrad0, hV1, hVδ, hlogV, hδsq, hksthr, hVJg, hCb0, hCbound, hXthr,
    hX₀k, hMfl0k, hk2, hkX, hgateW, hYpin, hWY, hXY, hthrY,
    hcqgate, hCqgate, hε0, habs,
    hQlogXd, hdomband, hlogb, hPQratio, h2688,
    hDmask0, hdebit, hcfthr,
    hc0, hce, hc1, hblk, hbox, hD1, hDk, hX₀j, hsqXa, hpin,
    hXae, hMXa, hXaX, hMfl0, hboxw, hS0, hSbd, hendGen, hRbdU, hRbar00, hRgrade,
    hend, hT0band, hcff, hpool, hgP1, hgRows, hgU, hgBand, henv⟩ := hcar
  subst hXdX
  subst hhj
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦the scale's arithmetic⟧
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hXee
  have h1ee : (1 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h1 := Real.add_one_le_exp (Real.exp 1)
    have h2 := Real.exp_pos 1
    linarith
  have hXd1 : 1 ≤ Xd := by
    have : (1 : ℝ) ≤ ((Xd : ℕ) : ℝ) := le_trans h1ee hXee
    exact_mod_cast this
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hlog1 : (1 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hLXe : Real.exp 1 ≤ Real.log ((Xd : ℕ) : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hP1 : 1 ≤ P := by omega
  have hP2 : 2 ≤ P := by omega
  -- ⟦THE LENGTH FLOOR IS FREE⟧: both `4 ≤ h` and the capstone's window gate
  have hj2 : 2 ≤ j := by
    have hA : 2 ^ 18 ≤ AdoorL M := AdoorL_ge_old hM
    have hAle : AdoorL M ≤ M * AdoorL M := Nat.le_mul_of_pos_left _ hM
    have hjf : M * AdoorL M ≤ j := hj0
    have h18 : (2 : ℕ) ≤ 2 ^ 18 := by norm_num
    omega
  have hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    have hN : (4 : ℕ) ≤ 2 ^ j := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    exact_mod_cast hN
  have hQ1h : ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) :=
    (door_length_gate_iff_L_gk K).mpr hj0
  -- ⟦THE DATUM SIDE (class (C)): the cut and its three S8 slots⟧
  have haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd →
      winCutH Xd (doorChiCoeff_L_gk K χ M) n = doorChiCoeff_L_gk K χ M n :=
    fun n h1 h2 => winCutH_of_mem _ h1 h2
  have ha0 : winCutH Xd (doorChiCoeff_L_gk K χ M) Xd = 0 := winCutH_supp0 _ le_rfl
  -- ⟦the pin chain and the per-block puncture law⟧
  have hcoefPin : SeamCoefW Xd P Q (winCutH Xd (doorChiCoeff_L_gk K χ M)) (doorChiCoeff_L_gk K χ M)
      (liouChi χ) :=
    doorChiCoeff_seamCoefW_at_door_H_L_gk K χ hM hlog1 hQXd hPlow haH ha0 hend
  have hcoefBand := doorChiCoeff_seamCoefW_punct_H_L_gk K χ hM haH ha0 hend
  -- ⟦the per-piece cap-free floor⟧
  have hfloor : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M)) ((Xd : ℕ) : ℝ) := by
    intro 𝒥 h𝒥
    exact hcfl Qm q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 𝒥
      ((Xd : ℕ) : ℝ) Dmask hqQm hXee hDmask0 (hdebit 𝒥 h𝒥) hcfthr
  -- ⟦THE SOCKET⟧ at `Ps := 1`, `J := 2`, read at the door datum
  have hsock0 := hsup q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M)
    (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q 2 1 Mt kk Dd Xa cqS L cgS Cb
    ((Xd : ℕ) : ℝ) theta293 (seamRad ((Xd : ℕ) : ℝ)) ((Xd : ℕ) : ℝ) 0 Rbar0 cW SW
    hc0 hce hc1 hCb0 hCbound hP1 le_rfl hRrad0 theta293_pos theta293_lt_one_div_32.le
    hLXe hPlow hQhigh hPQ hfloor hblk hbox hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0
    hboxw hS0 hSbd hendGen hRbdU
  have hsockR : CofactorSocket (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q
      ((Xd : ℕ) : ℝ) (seamRad ((Xd : ℕ) : ℝ)) 0 (4 * Rbar0) (doorChiCoeff_L_gk K χ M) := by
    have hs := cofactorSocket_doorChiCoeff_L_gk K χ hsock0
    have he : (2 : ℝ) ^ (2 : ℕ) * Rbar0 = 4 * Rbar0 := by ring
    rwa [he] at hs
  -- ⟦THE COPRIME TAIL⟧: `Mtail` and `EP2` are computed, not carried
  have hNcast : (((2 * Xd : ℕ)) : ℝ) = 2 * ((Xd : ℕ) : ℝ) := by push_cast; ring
  obtain ⟨hMtail, hMtail0, hEP2⟩ := htail q χ M P Q Xd (2 * Xd) ((Xd : ℕ) : ℝ) ε
    rfl hNcast hX0 hL256 hP2 hPQ hXd1 hQlogXd hdomband hPlow hlogb habs hPQratio h2688
  -- ⟦THE CAPSTONE, AT THE POOL⟧
  have hres := hgen Qm q χ hqQm (2 * Xd) Xd P Q M (winCutH Xd (doorChiCoeff_L_gk K χ M)) (liouChi χ)
    (doorChiCoeff_L_gk K χ M)
    (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 i
      (liouChi χ))
    ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) δ' V VJ L Cb (seamRad ((Xd : ℕ) : ℝ)) (4 * Rbar0)
    kmin Ymax ε _ _ C₁' M₀ π₀
    rfl rfl hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe hM hXdQ hQ1h hP3
    hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkkg hMtY
    hRrad0 le_rfl le_rfl hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0k hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 habs hEP2 le_rfl
    (doorRow_ha1_L_gk K χ M Xd) (norm_liouChi_le_one χ)
    (fun n hn => doorRow_hsupp0_L_gk K χ M Xd n hn) (fun n hn => doorRow_hasupp_L_gk K χ M Xd n hn)
    hMtail0 hMtail
    (norm_doorChiCoeff_le_one_L_gk K χ M) (fun i n => norm_doorPunctCoeff_le_one_L_gk K χ M i n)
    (by positivity) hRgrade hsockR hcoefBand hcoefPin hT0band hcff hpool hgP1 hgRows hgU
    hgBand
  -- ⟦THE DATUM BRIDGE⟧ the cut is invisible to the row's short sum
  simp only [shortSum_winCutH_seamS0] at hres
  exact le_trans hres henv

/-- **THE DOOR'S DYADIC ROW, CARRIED, AT THE POOL, AT THE G-LEVER**
(`m4_dyadicRow_carried_pool_L_gk`). -/
theorem m4_dyadicRow_carried_pool_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
            ∀ s ≤ H,
              DoorRowCarriedPool_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
                (doorLadder R.x H (i + 1) + s) j (MS j H)) →
        M4ChiDyadicRowMeanSq_L_gk K R M k MS := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_door_meansq_carried_pool_L_gk K hK
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro R Qm M k MS hM hQm htriv hcar H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hApos : 0 < doorLadder R.x H (i + 1) + s := by
    have := doorLadder_floor hxH (i + 1); omega
  by_cases hcase : doorRowFloorL M ≤ j
  · have hqQm : q ≤ Qm := by
      have hR : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hR
    exact hrow Qm q χ hq hqQm M (doorLadder R.x H (i + 1) + s) j (MS j H) hM hcase
      (hcar H hlo hhi q hq hqQ i hik χ j hjL hcase s hsH)
  · exact le_trans (doorRow_trivial_grade_L_gk K χ M j hApos) (htriv j H (not_le.mp hcase))

/-- **THE POOLED REGISTER, ARM 1 DISCHARGED, AT THE G-LEVER**
(`DoorRowCarriedT0Pool_L_gk`).  `DoorRowT0Gates` is `G`-FREE and keeps its landed name. -/
def DoorRowCarriedT0Pool_L_gk (K : ℕ) (Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q Ddis : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε Xw cqS cgS cW SW Rbar0 Dmask π₀ : ℝ),
    -- ⟦the two pins⟧
    ((Xd : ℝ) = X) ∧ (((2 ^ j : ℕ) : ℝ) = h) ∧
    -- ⟦the scale page, at the BLOCK scale⟧
    (Real.exp (Real.exp 1) ≤ X) ∧ (Real.exp 2 ≤ Real.log X) ∧
    (h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) ∧
    (Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X) ∧
    TannGate X (2 * (X / h)) ∧ (5 ≤ Real.log (Real.log (2 * (X / h)))) ∧
    (T₀ ≤ 2 * (X / h)) ∧ (Real.exp 1 ≤ 2 * (X / h)) ∧
    (Real.log X ≤ L) ∧ (Real.exp 1 ≤ L) ∧ ((256 : ℝ) ≤ Real.log X) ∧
    -- ⟦the door and the band⟧
    (calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) i)
                (calQK (AdoorL M) (s13GK K M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) i : ℕ) : ℝ)
            / Real.log ((calQK (AdoorL M) (s13GK K M) M i : ℕ) : ℝ))) ∧
    -- ⟦the window floors at the witness ladder⟧
    (∀ v ∈ ramI (H83 X theta293) P Q, (5 : ℝ) ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X)
          - Real.log (Real.log (ramRbot (H83 X theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log X)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      seamRad X ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
          (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
        ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, kmin ≤ ((witKk (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((witMt (H83 X theta293) Xd v : ℕ) : ℝ) ≤ Ymax) ∧
    -- ⟦the calibration, the radius, the short-interval datum⟧
    ((0 : ℝ) < seamRad X) ∧
    ((1 : ℝ) ≤ V) ∧ (V⁻¹ ≤ δ') ∧ (Real.log V ≤ 100 * Real.log L) ∧
    (δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ))) ∧
    (656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) ∧
    (Real.exp (mrAlpha (1 / 12) 2
        * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
    ((0 : ℝ) ≤ Cb) ∧ ShortIntervalDatum Cb ∧
    (2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) ∧
    -- ⟦the `kmin`/`Ymax` ladder⟧
    (Xcap ≤ kmin) ∧ ((0 : ℝ) ≤ cofactorMfl X theta293 kmin) ∧
    ((2 : ℝ) ≤ kmin) ∧ (kmin ≤ X) ∧
    ((1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin) ∧
    (pin2Gate ≤ Ymax) ∧ (Real.log Ymax ≤ 2 * Real.log kmin) ∧
    (Real.log X ≤ Real.log Ymax) ∧
    (32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) ∧
    -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6)⟧
    (420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293)) ∧
    -- ⟦the ε-window⟧
    ((0 : ℝ) ≤ ε) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the coprime-tail page (⟦THE K6 PATTERN⟧: the threshold where `Ctail` is bound)⟧
    (100 * Real.log (Q : ℝ) ≤ Real.log (Xd : ℝ)) ∧
    (((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))) ∧
    (10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) ∧
    (Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) ∧
    (2688 * Ctail * Real.log (Real.log X) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the per-piece cap-free floor: only the Mertens mask debit is carried⟧
    ((0 : ℝ) ≤ Dmask) ∧
    (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (s13GK K M) i)
          (calQK (AdoorL M) (s13GK K M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kcf + 25
            + Dmask)
      < Real.log (Real.log X)) ∧
    -- ⟦THE SOCKET'S GATES⟧ (`m4_supplier_complete` at `Ps := 1`, `J := 2`)
    ((0 : ℝ) < cW) ∧ (cW ≤ 1 / Real.exp 1) ∧ (2 * cW < 1) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cqS (H83 X theta293) P (2 * Xd) Xd Mt kk X L cgS Cb X theta293
        (seamRad X) v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ)) ≤ 3 * X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 1 ≤ Dd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Dd v ≤ kk v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Xsk ≤ Real.sqrt (Xa v)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.sqrt (Xa v) ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.exp 1 ≤ Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((Mt v : ℕ) : ℝ) ≤ 2 * Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * Xa v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      (0 : ℝ) ≤ cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X → ∀ i : ℕ,
      ((kk v / Dd v : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa v →
        |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) ∧
    ((0 : ℝ) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cSq * caseASwide cW Cb (cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ))
          ((kk v / Dd v : ℕ) : ℝ) (Xa v)
        + cSq * ((Dd v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 / ramRbot (H83 X theta293) Xd v
      ≤ cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) / 3) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) ≤ Rbar0) ∧
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293)) ∧
    -- ⟦THE ENDPOINT⟧ (`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is the converse)
    (doorChiCoeff_L_gk K χ M Xd = 0) ∧
    -- ⟦ARM 1 DISCHARGED: the T₀-band gates, not the T₀-band integral⟧
    DoorRowT0Gates Kbox X₀w q Ddis X Xw Dmask ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    ((0 : ℝ) ≤ π₀) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀) ∧
    (5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀) ∧
    ((Real.log X) ^ (-theta293 + ε) ≤ π₀) ∧
    (4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * (cfbC₁ X (t0dC1_L Cb)) ^ 2 * Real.exp (-(1 / Real.exp 1) * t0dM0 X)
        + 1787702400 * a2Level1_L M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

set_option maxHeartbeats 4000000 in
/-- **THE BRIDGE AT THE POOL, AT THE G-LEVER**
(`doorRowCarried_of_t0free_pool_L_gk`). -/
theorem doorRowCarried_of_t0free_pool_L_gk (K : ℕ) (Qm : ℕ) :
    ∃ Kbox X₀w : ℝ, 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ) (q : ℕ) [NeZero q]
        (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ), q ≤ Qm →
        DoorRowCarriedT0Pool_L_gk K Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B →
          DoorRowCarriedPool_L_gk K Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hdis⟩ := m4_t0band_discharged_L_gk K Qm
  refine ⟨Kbox, X₀w, hK0, hX₀0, ?_⟩
  intro Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail q _ χ M Xd j B hq hfree
  obtain ⟨P, Q, Ddis, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, Xw, cqS, cgS, cW,
    SW, Rbar0, Dmask, π₀, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33,
    d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49, d50, d51,
    d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67, d68, d69,
    d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85, d86, d87,
    d88, d89, d90, d91, d92, d93, d94, d95, d96, d97, d98, d99⟩ := hfree
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := d92
  have hT0 : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
        ≤ t0BandB X (cfbC₁ X (t0dC1_L Cb)) (t0dM0 X) :=
    hdis q χ M Xd Ddis X Xw Cb Dmask hq g1 d1 g2 g3 g4 g5 d46 d47 d68 g6 g7 g8
  exact ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, cfbC₁ X (t0dC1_L Cb),
    t0dM0 X, cqS, cgS, cW, SW, Rbar0, Dmask, π₀, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11,
    d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29,
    d30, d31, d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47,
    d48, d49, d50, d51, d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65,
    d66, d67, d68, d69, d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83,
    d84, d85, d86, d87, d88, d89, d90, d91, hT0, d93, d94, d95, d96, d97, d98, d99⟩

/-- **THE DOOR ROW'S CARRIED REGISTER, AT THE R1×R2 JOIN, AT THE
G-LEVER** (`DoorRowCarriedJoin_L_gk`). -/
def DoorRowCarriedJoin_L_gk (K : ℕ) (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε C₁' M₀ cqS cgS cW SW Rbar0 Dmask π₀ : ℝ),
    -- ⟦the two pins⟧
    ((Xd : ℝ) = X) ∧ (((2 ^ j : ℕ) : ℝ) = h) ∧
    -- ⟦the scale page, at the BLOCK scale⟧
    (Real.exp (Real.exp 1) ≤ X) ∧ (Real.exp 2 ≤ Real.log X) ∧
    (h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) ∧
    (Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X) ∧
    TannGate X (2 * (X / h)) ∧ (5 ≤ Real.log (Real.log (2 * (X / h)))) ∧
    (T₀ ≤ 2 * (X / h)) ∧ (Real.exp 1 ≤ 2 * (X / h)) ∧
    (Real.log X ≤ L) ∧ (Real.exp 1 ≤ L) ∧ ((256 : ℝ) ≤ Real.log X) ∧
    -- ⟦the door and the band⟧
    (calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) i)
                (calQK (AdoorL M) (s13GK K M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) i : ℕ) : ℝ)
            / Real.log ((calQK (AdoorL M) (s13GK K M) M i : ℕ) : ℝ))) ∧
    -- ⟦the window floors at the witness ladder⟧
    (∀ v ∈ ramI (H83 X theta293) P Q, (5 : ℝ) ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X)
          - Real.log (Real.log (ramRbot (H83 X theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log X)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      seamRad X ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
          (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
        ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, kmin ≤ ((witKk (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((witMt (H83 X theta293) Xd v : ℕ) : ℝ) ≤ Ymax) ∧
    -- ⟦the calibration, the radius, the short-interval datum⟧
    ((0 : ℝ) < seamRad X) ∧
    ((1 : ℝ) ≤ V) ∧ (V⁻¹ ≤ δ') ∧ (Real.log V ≤ 100 * Real.log L) ∧
    (δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ))) ∧
    (656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) ∧
    (Real.exp (mrAlpha (1 / 12) 2
        * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
    ((0 : ℝ) ≤ Cb) ∧ ShortIntervalDatum Cb ∧
    (2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) ∧
    -- ⟦the `kmin`/`Ymax` ladder⟧
    (Xcap ≤ kmin) ∧ ((0 : ℝ) ≤ cofactorMfl X theta293 kmin) ∧
    ((2 : ℝ) ≤ kmin) ∧ (kmin ≤ X) ∧
    ((1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin) ∧
    (pin2Gate ≤ Ymax) ∧ (Real.log Ymax ≤ 2 * Real.log kmin) ∧
    (Real.log X ≤ Real.log Ymax) ∧
    (32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) ∧
    -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6)⟧
    (420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293)) ∧
    -- ⟦the ε-window⟧
    ((0 : ℝ) ≤ ε) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the coprime-tail page (⟦THE K6 PATTERN⟧: the threshold where `Ctail` is bound)⟧
    (100 * Real.log (Q : ℝ) ≤ Real.log (Xd : ℝ)) ∧
    (((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))) ∧
    (10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) ∧
    (Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) ∧
    (2688 * Ctail * Real.log (Real.log X) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the per-piece cap-free floor: only the Mertens mask debit is carried⟧
    ((0 : ℝ) ≤ Dmask) ∧
    (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (s13GK K M) i)
          (calQK (AdoorL M) (s13GK K M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kcf + 25
            + Dmask)
      < Real.log (Real.log X)) ∧
    -- ⟦THE SOCKET'S GATES⟧ (`m4_supplier_complete` at `Ps := 1`, `J := 2`)
    ((0 : ℝ) < cW) ∧ (cW ≤ 1 / Real.exp 1) ∧ (2 * cW < 1) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cqS (H83 X theta293) P (2 * Xd) Xd Mt kk X L cgS Cb X theta293
        (seamRad X) v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ)) ≤ 3 * X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 1 ≤ Dd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Dd v ≤ kk v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Xsk ≤ Real.sqrt (Xa v)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.sqrt (Xa v) ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.exp 1 ≤ Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((Mt v : ℕ) : ℝ) ≤ 2 * Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * Xa v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      (0 : ℝ) ≤ cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X → ∀ i : ℕ,
      ((kk v / Dd v : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa v →
        |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) ∧
    ((0 : ℝ) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cSq * caseASwide cW Cb (cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ))
          ((kk v / Dd v : ℕ) : ℝ) (Xa v)
        + cSq * ((Dd v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 / ramRbot (H83 X theta293) Xd v
      ≤ cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) / 3) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) ≤ Rbar0) ∧
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293)) ∧
    -- ⟦THE ENDPOINT⟧ (`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is the converse)
    (doorChiCoeff_L_gk K χ M Xd = 0) ∧
    -- ⟦THE CARRY: the `T₀`-band arm, at `m4_hT0band_at_door_L`'s own conclusion⟧
    ((∫ t in (-(seamT0 X))..(seamT0 X),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
      ≤ t0BandB X C₁' M₀) ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    ((0 : ℝ) ≤ π₀) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀) ∧
    (5760 * (a2RowsSum'_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀) ∧
    ((Real.log X) ^ (-theta293 + ε) ≤ π₀) ∧
    (4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

set_option maxHeartbeats 4000000 in
/-- **THE DOOR ROW'S MEAN SQUARE, CARRIED, AT THE JOIN, AT THE
G-LEVER** (`m4_door_meansq_carried_join_L_gk`).  Capstone:
`M4MeanSqPrime.m4_meansq_per_chi_gen_join_gk`, whence `K ≤ 1.7·10⁸`. -/
theorem m4_door_meansq_carried_join_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (Qm q : ℕ) (χ : DirichletCharacter ℂ q), 0 < q → q ≤ Qm →
        ∀ (M Xd j : ℕ) (B : ℝ), 1 ≤ M → doorRowFloorL M ≤ j →
          DoorRowCarriedJoin_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M Xd j B →
            1 / ((Xd : ℕ) : ℝ)
                * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
                    ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                        * shortSum (doorChiCoeff_L_gk K χ M)
                            (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
              ≤ B := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hgen⟩ :=
    m4_meansq_per_chi_gen_join_L_gk K hK
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  -- ⟦THE SKOLEM CUT⟧ the masked-floor constant, as a function of the modulus range
  choose Kcf hKcf0 hcfl using capFreeFloor3_pieceDatum
  obtain ⟨Ctail, hCtail0, htail⟩ := m4_door_tail_supply_L_gk K
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro Qm q χ hq hqQm M Xd j B hM hj0 hcar
  obtain ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, C₁', M₀,
    cqS, cgS, cW, SW, Rbar0, Dmask, π₀,
    hXdX, hhj, hXee, hlX2, hhX, hhceil, hTann, hceil5, hT₀le, hTbot, hLXL, hLe, hL256,
    hXdQ, hP3, hlogP2, hQbot, hQlog, hQL, hPlow, hQhigh, hPQ, hQ0, hHX, hH2, hPj1, hQXd,
    hXdbig, hdom, hW5, hkth, hMtX, hC16, hRradW, hthinpin, hMtpin, hkkg, hMtY,
    hRrad0, hV1, hVδ, hlogV, hδsq, hksthr, hVJg, hCb0, hCbound, hXthr,
    hX₀k, hMfl0k, hk2, hkX, hgateW, hYpin, hWY, hXY, hthrY,
    hcqgate, hCqgate, hε0, habs,
    hQlogXd, hdomband, hlogb, hPQratio, h2688,
    hDmask0, hdebit, hcfthr,
    hc0, hce, hc1, hblk, hbox, hD1, hDk, hX₀j, hsqXa, hpin,
    hXae, hMXa, hXaX, hMfl0, hboxw, hS0, hSbd, hendGen, hRbdU, hRbar00, hRgrade,
    hend, hT0band, hcff, hpool, hgP1, hgRows, hgU, hgBand, henv⟩ := hcar
  subst hXdX
  subst hhj
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦the scale's arithmetic⟧
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hXee
  have h1ee : (1 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h1 := Real.add_one_le_exp (Real.exp 1)
    have h2 := Real.exp_pos 1
    linarith
  have hXd1 : 1 ≤ Xd := by
    have : (1 : ℝ) ≤ ((Xd : ℕ) : ℝ) := le_trans h1ee hXee
    exact_mod_cast this
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hlog1 : (1 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hLXe : Real.exp 1 ≤ Real.log ((Xd : ℕ) : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hP1 : 1 ≤ P := by omega
  have hP2 : 2 ≤ P := by omega
  -- ⟦THE LENGTH FLOOR IS FREE⟧: both `4 ≤ h` and the capstone's window gate
  have hj2 : 2 ≤ j := by
    have hA : 2 ^ 18 ≤ AdoorL M := AdoorL_ge_old hM
    have hAle : AdoorL M ≤ M * AdoorL M := Nat.le_mul_of_pos_left _ hM
    have hjf : M * AdoorL M ≤ j := hj0
    have h18 : (2 : ℕ) ≤ 2 ^ 18 := by norm_num
    omega
  have hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    have hN : (4 : ℕ) ≤ 2 ^ j := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    exact_mod_cast hN
  have hQ1h : ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) :=
    (door_length_gate_iff_L_gk K).mpr hj0
  -- ⟦THE DATUM SIDE (class (C)): the cut and its three S8 slots⟧
  have haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd →
      winCutH Xd (doorChiCoeff_L_gk K χ M) n = doorChiCoeff_L_gk K χ M n :=
    fun n h1 h2 => winCutH_of_mem _ h1 h2
  have ha0 : winCutH Xd (doorChiCoeff_L_gk K χ M) Xd = 0 := winCutH_supp0 _ le_rfl
  -- ⟦the pin chain and the per-block puncture law⟧
  have hcoefPin : SeamCoefW Xd P Q (winCutH Xd (doorChiCoeff_L_gk K χ M)) (doorChiCoeff_L_gk K χ M)
      (liouChi χ) :=
    doorChiCoeff_seamCoefW_at_door_H_L_gk K χ hM hlog1 hQXd hPlow haH ha0 hend
  have hcoefBand := doorChiCoeff_seamCoefW_punct_H_L_gk K χ hM haH ha0 hend
  -- ⟦the per-piece cap-free floor⟧
  have hfloor : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M)) ((Xd : ℕ) : ℝ) := by
    intro 𝒥 h𝒥
    exact hcfl Qm q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 𝒥
      ((Xd : ℕ) : ℝ) Dmask hqQm hXee hDmask0 (hdebit 𝒥 h𝒥) hcfthr
  -- ⟦THE SOCKET⟧ at `Ps := 1`, `J := 2`, read at the door datum
  have hsock0 := hsup q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M)
    (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q 2 1 Mt kk Dd Xa cqS L cgS Cb
    ((Xd : ℕ) : ℝ) theta293 (seamRad ((Xd : ℕ) : ℝ)) ((Xd : ℕ) : ℝ) 0 Rbar0 cW SW
    hc0 hce hc1 hCb0 hCbound hP1 le_rfl hRrad0 theta293_pos theta293_lt_one_div_32.le
    hLXe hPlow hQhigh hPQ hfloor hblk hbox hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0
    hboxw hS0 hSbd hendGen hRbdU
  have hsockR : CofactorSocket (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q
      ((Xd : ℕ) : ℝ) (seamRad ((Xd : ℕ) : ℝ)) 0 (4 * Rbar0) (doorChiCoeff_L_gk K χ M) := by
    have hs := cofactorSocket_doorChiCoeff_L_gk K χ hsock0
    have he : (2 : ℝ) ^ (2 : ℕ) * Rbar0 = 4 * Rbar0 := by ring
    rwa [he] at hs
  -- ⟦THE COPRIME TAIL⟧: `Mtail` and `EP2` are computed, not carried
  have hNcast : (((2 * Xd : ℕ)) : ℝ) = 2 * ((Xd : ℕ) : ℝ) := by push_cast; ring
  obtain ⟨hMtail, hMtail0, hEP2⟩ := htail q χ M P Q Xd (2 * Xd) ((Xd : ℕ) : ℝ) ε
    rfl hNcast hX0 hL256 hP2 hPQ hXd1 hQlogXd hdomband hPlow hlogb habs hPQratio h2688
  -- ⟦THE CAPSTONE, AT THE POOL⟧
  have hres := hgen Qm q χ hqQm (2 * Xd) Xd P Q M (winCutH Xd (doorChiCoeff_L_gk K χ M)) (liouChi χ)
    (doorChiCoeff_L_gk K χ M)
    (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 i
      (liouChi χ))
    ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) δ' V VJ L Cb (seamRad ((Xd : ℕ) : ℝ)) (4 * Rbar0)
    kmin Ymax ε _ _ C₁' M₀ π₀
    rfl rfl hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe hM hXdQ hQ1h hP3
    hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkkg hMtY
    hRrad0 le_rfl le_rfl hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0k hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 habs hEP2 le_rfl
    (doorRow_ha1_L_gk K χ M Xd) (norm_liouChi_le_one χ)
    (fun n hn => doorRow_hsupp0_L_gk K χ M Xd n hn) (fun n hn => doorRow_hasupp_L_gk K χ M Xd n hn)
    hMtail0 hMtail
    (norm_doorChiCoeff_le_one_L_gk K χ M) (fun i n => norm_doorPunctCoeff_le_one_L_gk K χ M i n)
    (by positivity) hRgrade hsockR hcoefBand hcoefPin hT0band hcff hpool hgP1 hgRows hgU
    hgBand
  -- ⟦THE DATUM BRIDGE⟧ the cut is invisible to the row's short sum
  simp only [shortSum_winCutH_seamS0] at hres
  exact le_trans hres henv

/-- **THE DOOR'S DYADIC ROW, CARRIED, AT THE JOIN, AT THE G-LEVER**
(`m4_dyadicRow_carried_join_L_gk`). -/
theorem m4_dyadicRow_carried_join_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
            ∀ s ≤ H,
              DoorRowCarriedJoin_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
                (doorLadder R.x H (i + 1) + s) j (MS j H)) →
        M4ChiDyadicRowMeanSq_L_gk K R M k MS := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_door_meansq_carried_join_L_gk K hK
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro R Qm M k MS hM hQm htriv hcar H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hApos : 0 < doorLadder R.x H (i + 1) + s := by
    have := doorLadder_floor hxH (i + 1); omega
  by_cases hcase : doorRowFloorL M ≤ j
  · have hqQm : q ≤ Qm := by
      have hR : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hR
    exact hrow Qm q χ hq hqQm M (doorLadder R.x H (i + 1) + s) j (MS j H) hM hcase
      (hcar H hlo hhi q hq hqQ i hik χ j hjL hcase s hsH)
  · exact le_trans (doorRow_trivial_grade_L_gk K χ M j hApos) (htriv j H (not_le.mp hcase))

/-- **THE JOINED REGISTER, ARM 1 DISCHARGED, AT THE G-LEVER**
(`DoorRowCarriedT0Join_L_gk`). -/
def DoorRowCarriedT0Join_L_gk (K : ℕ) (Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q Ddis : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε Xw cqS cgS cW SW Rbar0 Dmask π₀ : ℝ),
    -- ⟦the two pins⟧
    ((Xd : ℝ) = X) ∧ (((2 ^ j : ℕ) : ℝ) = h) ∧
    -- ⟦the scale page, at the BLOCK scale⟧
    (Real.exp (Real.exp 1) ≤ X) ∧ (Real.exp 2 ≤ Real.log X) ∧
    (h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) ∧
    (Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X) ∧
    TannGate X (2 * (X / h)) ∧ (5 ≤ Real.log (Real.log (2 * (X / h)))) ∧
    (T₀ ≤ 2 * (X / h)) ∧ (Real.exp 1 ≤ 2 * (X / h)) ∧
    (Real.log X ≤ L) ∧ (Real.exp 1 ≤ L) ∧ ((256 : ℝ) ≤ Real.log X) ∧
    -- ⟦the door and the band⟧
    (calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) i)
                (calQK (AdoorL M) (s13GK K M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) i : ℕ) : ℝ)
            / Real.log ((calQK (AdoorL M) (s13GK K M) M i : ℕ) : ℝ))) ∧
    -- ⟦the window floors at the witness ladder⟧
    (∀ v ∈ ramI (H83 X theta293) P Q, (5 : ℝ) ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X)
          - Real.log (Real.log (ramRbot (H83 X theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log X)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      seamRad X ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
          (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
        ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, kmin ≤ ((witKk (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((witMt (H83 X theta293) Xd v : ℕ) : ℝ) ≤ Ymax) ∧
    -- ⟦the calibration, the radius, the short-interval datum⟧
    ((0 : ℝ) < seamRad X) ∧
    ((1 : ℝ) ≤ V) ∧ (V⁻¹ ≤ δ') ∧ (Real.log V ≤ 100 * Real.log L) ∧
    (δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ))) ∧
    (656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) ∧
    (Real.exp (mrAlpha (1 / 12) 2
        * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
    ((0 : ℝ) ≤ Cb) ∧ ShortIntervalDatum Cb ∧
    (2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) ∧
    -- ⟦the `kmin`/`Ymax` ladder⟧
    (Xcap ≤ kmin) ∧ ((0 : ℝ) ≤ cofactorMfl X theta293 kmin) ∧
    ((2 : ℝ) ≤ kmin) ∧ (kmin ≤ X) ∧
    ((1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin) ∧
    (pin2Gate ≤ Ymax) ∧ (Real.log Ymax ≤ 2 * Real.log kmin) ∧
    (Real.log X ≤ Real.log Ymax) ∧
    (32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) ∧
    -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6)⟧
    (420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293)) ∧
    -- ⟦the ε-window⟧
    ((0 : ℝ) ≤ ε) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the coprime-tail page (⟦THE K6 PATTERN⟧: the threshold where `Ctail` is bound)⟧
    (100 * Real.log (Q : ℝ) ≤ Real.log (Xd : ℝ)) ∧
    (((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))) ∧
    (10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) ∧
    (Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) ∧
    (2688 * Ctail * Real.log (Real.log X) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the per-piece cap-free floor: only the Mertens mask debit is carried⟧
    ((0 : ℝ) ≤ Dmask) ∧
    (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (s13GK K M) i)
          (calQK (AdoorL M) (s13GK K M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kcf + 25
            + Dmask)
      < Real.log (Real.log X)) ∧
    -- ⟦THE SOCKET'S GATES⟧ (`m4_supplier_complete` at `Ps := 1`, `J := 2`)
    ((0 : ℝ) < cW) ∧ (cW ≤ 1 / Real.exp 1) ∧ (2 * cW < 1) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cqS (H83 X theta293) P (2 * Xd) Xd Mt kk X L cgS Cb X theta293
        (seamRad X) v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ)) ≤ 3 * X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 1 ≤ Dd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Dd v ≤ kk v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Xsk ≤ Real.sqrt (Xa v)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.sqrt (Xa v) ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.exp 1 ≤ Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((Mt v : ℕ) : ℝ) ≤ 2 * Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * Xa v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      (0 : ℝ) ≤ cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X → ∀ i : ℕ,
      ((kk v / Dd v : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa v →
        |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) ∧
    ((0 : ℝ) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cSq * caseASwide cW Cb (cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ))
          ((kk v / Dd v : ℕ) : ℝ) (Xa v)
        + cSq * ((Dd v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 / ramRbot (H83 X theta293) Xd v
      ≤ cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) / 3) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) ≤ Rbar0) ∧
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293)) ∧
    -- ⟦THE ENDPOINT⟧ (`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is the converse)
    (doorChiCoeff_L_gk K χ M Xd = 0) ∧
    -- ⟦ARM 1 DISCHARGED: the T₀-band gates, not the T₀-band integral⟧
    DoorRowT0Gates Kbox X₀w q Ddis X Xw Dmask ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    ((0 : ℝ) ≤ π₀) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀) ∧
    (5760 * (a2RowsSum'_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀) ∧
    ((Real.log X) ^ (-theta293 + ε) ≤ π₀) ∧
    (4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * (cfbC₁ X (t0dC1_L Cb)) ^ 2 * Real.exp (-(1 / Real.exp 1) * t0dM0 X)
        + 1787702400 * a2Level1_L M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

set_option maxHeartbeats 4000000 in
/-- **THE BRIDGE AT THE JOIN, AT THE G-LEVER**
(`doorRowCarried_of_t0free_join_L_gk`). -/
theorem doorRowCarried_of_t0free_join_L_gk (K : ℕ) (Qm : ℕ) :
    ∃ Kbox X₀w : ℝ, 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ) (q : ℕ) [NeZero q]
        (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ), q ≤ Qm →
        DoorRowCarriedT0Join_L_gk K Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B →
          DoorRowCarriedJoin_L_gk K Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hdis⟩ := m4_t0band_discharged_L_gk K Qm
  refine ⟨Kbox, X₀w, hK0, hX₀0, ?_⟩
  intro Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail q _ χ M Xd j B hq hfree
  obtain ⟨P, Q, Ddis, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, Xw, cqS, cgS, cW,
    SW, Rbar0, Dmask, π₀, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33,
    d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49, d50, d51,
    d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67, d68, d69,
    d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85, d86, d87,
    d88, d89, d90, d91, d92, d93, d94, d95, d96, d97, d98, d99⟩ := hfree
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := d92
  have hT0 : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
        ≤ t0BandB X (cfbC₁ X (t0dC1_L Cb)) (t0dM0 X) :=
    hdis q χ M Xd Ddis X Xw Cb Dmask hq g1 d1 g2 g3 g4 g5 d46 d47 d68 g6 g7 g8
  exact ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, cfbC₁ X (t0dC1_L Cb),
    t0dM0 X, cqS, cgS, cW, SW, Rbar0, Dmask, π₀, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11,
    d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29,
    d30, d31, d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47,
    d48, d49, d50, d51, d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65,
    d66, d67, d68, d69, d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83,
    d84, d85, d86, d87, d88, d89, d90, d91, hT0, d93, d94, d95, d96, d97, d98, d99⟩
/-! ## §4 — `M4AssemblyPool` -/

/-- **⟦THE SLOT FUSE AT THE POOL⟧** (`m4_chiFreeRowSq_sum_at_door_pool_L`).
`ThmA2Pool.thm_a2'_of_rows_chiSummed_pool` instantiated at the door datum

  `N := 2X_d`,  `X := X_d`,  `h := 2^j`,  `a χ := winCutH X_d (doorChiCoeff_L χ M)`,

whose right-hand side collapses to `φ(q)·a2DoorGrade_pool_L M X_d 2^j C₁ M₀ π₀`.

⟦THE GATE LIST AGAINST `M4Assembly.m4_chiFreeRowSq_sum_at_door`⟧ `hM`, `hX`, `hX3`, `hh4`,
`hhX`, `hTann`, `hceil`, `hrowsSum`, `hT0bandSum` are VERBATIM.  `hgP1`/`hgRows` read `≤ π₀`;
`hεwin` and `hL4096` are GONE, replaced by the two stated pool gates `hgU`/`hgBand`.  `0 ≤ π₀`
is derived from `hgBand` and `hX3`, not assumed. -/
theorem m4_chiFreeRowSq_sum_at_door_pool_L {q : ℕ} [NeZero q] {M Xd j : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)) (hX3 : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ))
    (hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ))
    (hhX : ((2 ^ j : ℕ) : ℝ)
      ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ)))
    (hTann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
    (hceil : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ ((Xd : ℕ) : ℝ) →
      TannGate ((Xd : ℕ) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
          * (∫ t in seamAnn ((Xd : ℕ) : ℝ) (2 * T),
              ‖spoly (2 * Xd) (winCutH Xd (doorChiCoeff_L χ M)) t‖ ^ 2)
        ≤ a2Mrow_L Cs Ccc M Xd ((Xd : ℕ) : ℝ) ε)
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 ((Xd : ℕ) : ℝ)))..(seamT0 ((Xd : ℕ) : ℝ)),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) t‖ ^ 2)
        ≤ t0BandB ((Xd : ℕ) : ℝ) (cfbC₁ ((Xd : ℕ) : ℝ) C₁) M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
    (hgU : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀)
    (hgBand : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j Xd
      ≤ (q.totient : ℝ)
          * a2DoorGrade_pool_L M ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
  have hpool : (0 : ℝ) ≤ π₀ := by
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by
      have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) hX3
      have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
      linarith
    have hrp : (0 : ℝ) < (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) :=
      Real.rpow_pos_of_pos hL0 _
    linarith
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hbase := thm_a2'_of_rows_chiSummed_pool_L (q := q) (N := 2 * Xd) (M := M) (Xd := Xd)
    (a := fun χ => winCutH Xd (doorChiCoeff_L χ M)) (X := ((Xd : ℕ) : ℝ))
    (h := ((2 ^ j : ℕ) : ℝ)) (π₀ := π₀) (Cs := fun _ => Cs) (Ccc := fun _ => Ccc)
    (C₁' := fun _ => cfbC₁ ((Xd : ℕ) : ℝ) C₁) (M₀ := fun _ => M₀) (ε := fun _ => ε)
    hM hX hX3 hh4 hhX (fun χ n => doorRow_ha1_L χ M Xd n)
    (fun χ n hn => doorRow_hsupp0_L χ M Xd n hn) hN2 hTann hceil hrowsSum hT0bandSum
    hpool (fun _ => hgP1) (fun _ => hgRows) (fun _ => hgU) hgBand
  simp only [shortSum_winCutH_seamS0] at hbase
  refine le_trans hbase (le_of_eq ?_)
  rw [a2_sum_const_chars]
  unfold a2DoorGrade_pool_L
  ring

/-- **THE FUSE FRAME AT ONE BASE, POOLED** (`DoorFuseFrame_pool_L`) — the character-blind half
of `m4_chiFreeRowSq_sum_at_door_pool_L`'s gate list, field by field.

Against `M4Assembly.DoorFuseFrame`'s eleven fields: the six frame fields are verbatim; `gP1`
and `gRows` read `≤ π₀`; `eps_lo`/`eps_hi` are REPLACED by the single `eps_pool` (so `ε` is
otherwise free); `L4096` is REPLACED by `band_pool`.  **Ten fields.**  Nonnegativity of `π₀`
is a derived lemma (`pool_nonneg_L`), not a field. -/
structure DoorFuseFrame_pool_L (M Xd j : ℕ) (Cs Ccc ε π₀ : ℝ) : Prop where
  /-- `e ≤ X_d` — the frozen interface's lower scale pin. -/
  X_exp : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)
  /-- `3 ≤ X_d`. -/
  X_three : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ)
  /-- `4 ≤ 2^j` — the AS-2 MVT guard (NOT `3`). -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- Lemma 14's window frame `2^j ≤ X_d·(log X_d)^{−1/5}`. -/
  h_window : ((2 ^ j : ℕ) : ℝ)
    ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ))
  /-- `TannGate X_d (2X_d/2^j)` — the annulus gate at the family's bottom height. -/
  tann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))
  /-- `5 ≤ loglog(2X_d/2^j)` — the `h`-ceiling. -/
  ceil5 : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
  /-- The first GRADING gate, on the `𝒯`-leg constant `Cs`, AT THE POOL. -/
  gP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀
  /-- The second GRADING gate, on the Lemma-12 row sum and `Ccc`, AT THE POOL. -/
  gRows : 5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀
  /-- **THE `𝒰`-LEG, POOLED** — replacing `eps_lo`/`eps_hi`: the leg's own value sits under
  the pool, so `ε` carries no exponent-room constraint. -/
  eps_pool : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀
  /-- **THE BAND ABSORPTION, POOLED** — replacing `L4096`. -/
  band_pool : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀

section
variable {M Xd j : ℕ} {Cs Ccc ε π₀ : ℝ}

/-- The pool is nonnegative — DERIVED from `band_pool` and `X_three`, which is why the frame
has ten fields and not eleven. -/
theorem pool_nonneg_L (h : DoorFuseFrame_pool_L M Xd j Cs Ccc ε π₀) : 0 ≤ π₀ := by
  have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by
    have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) h.X_three
    have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  have hrp : (0 : ℝ) < (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) :=
    Real.rpow_pos_of_pos hL0 _
  have := h.band_pool
  linarith

end

/-- **⟦THE SOCKET AT THE POOLED DOOR GRADE⟧** (`m4_chiSummedFreeRowBig_of_doorGrade_pool_L`) —
`M4Assembly.m4_chiSummedFreeRowBig_of_doorGrade` with `a2DoorGrade_pool_L` in both slots.  The
⟦φ(q) LEDGER⟧ is paid identically: `φ(q) ≤ q ≤ arcDen 12 H`, explicit in `henv`. -/
theorem m4_chiSummedFreeRowBig_of_doorGrade_pool_L {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    {C₁ M₀ π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloorL M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)) (π₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig_L R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) (π₀ (A + s)) :=
    a2DoorGrade_pool_L_nonneg hM (log_natCast_nonneg' (A + s)) hh0 (hpool (A + s))
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans
    (hgrade H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H j A s hjfl

/-- **⟦ITEM 11, INHABITED AT THE POOLED DOOR GRADE⟧**
(`m4_chiSummedFreeRow_of_doorGrade_pool_L`) — §4 spliced through
`M4ChiSocketWire.m4_chiSummedFreeRow_of_big`, at the same `m4ChiRowGraded_L` shape. -/
theorem m4_chiSummedFreeRow_of_doorGrade_pool_L {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    {C₁ M₀ π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloorL M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)) (π₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) :=
  m4_chiSummedFreeRow_of_big_L
    (m4_chiSummedFreeRowBig_of_doorGrade_pool_L hM hpool hgrade henv)

/-- **⟦THE ASSEMBLY, POOLED⟧** (`m4_chiSummedFreeRow_of_doorAssembly_pool_L`) — ⟦item 11⟧ of
`m4_second_road_L` from the NAMED gates alone, at the pooled grade.

THE COMPLETE GATE LIST: `hM`; `hframe` — `DoorFuseFrame_pool_L` (TEN fields) at every base the
socket reaches, with the base-indexed pool `π₀`; `hrows` and `hband` — `M4Assembly`'s own two
suppliers, BYTE FOR BYTE unchanged (neither mentions the pool); `henv` — the arithmetic, now
against `a2DoorGrade_pool_L`. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_L {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_pool_L M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
          ≤ a2Mrow_L (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorGrade_pool_L hM (C₁ := C₁) (M₀ := M₀) (π₀ := π₀) hpool ?_
    henv
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb : SocketBaseL R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_pool_L hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows hF.eps_pool
    hF.band_pool

set_option linter.unusedVariables false in
/-- `a2DoorGrade_pool_L` (:61), at the lever.  Body byte-identical (`a2Level1_L` is K-invariant);
the twin exists for uniformity of the family's shape. -/
def a2DoorGrade_pool_L_gk (K : ℕ) (M : ℕ) (X h C₁ M₀ π₀ : ℝ) : ℝ :=
  8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
    + 1787702400 * a2Level1_L M
    + 188133 * π₀
    + 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
    + 6315000 / h

/-- `a2DoorGrade_pool_L_nonneg` (:77), at the lever. -/
theorem a2DoorGrade_pool_nonneg_L_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) {X h C₁ M₀ π₀ : ℝ}
    (hX : 0 ≤ Real.log X)
    (hh : 0 < h) (hπ : 0 ≤ π₀) : 0 ≤ a2DoorGrade_pool_L_gk K M X h C₁ M₀ π₀ :=
  a2DoorGrade_pool_L_nonneg hM hX hh hπ

/-- `m4_chiFreeRowSq_sum_at_door_pool_L` (:117), at the lever. -/
theorem m4_chiFreeRowSq_sum_at_door_pool_L_gk (K : ℕ) {q : ℕ} [NeZero q] {M Xd j : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)) (hX3 : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ))
    (hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ))
    (hhX : ((2 ^ j : ℕ) : ℝ)
      ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ)))
    (hTann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
    (hceil : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ ((Xd : ℕ) : ℝ) →
      TannGate ((Xd : ℕ) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
          * (∫ t in seamAnn ((Xd : ℕ) : ℝ) (2 * T),
              ‖spoly (2 * Xd) (winCutH Xd (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
        ≤ a2Mrow_L_gk K Cs Ccc M Xd ((Xd : ℕ) : ℝ) ε)
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 ((Xd : ℕ) : ℝ)))..(seamT0 ((Xd : ℕ) : ℝ)),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) t‖ ^ 2)
        ≤ t0BandB ((Xd : ℕ) : ℝ) (cfbC₁ ((Xd : ℕ) : ℝ) C₁) M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
    (hgU : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀)
    (hgBand : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j Xd
      ≤ (q.totient : ℝ)
          * a2DoorGrade_pool_L_gk K M ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
  have hpool : (0 : ℝ) ≤ π₀ := by
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by
      have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) hX3
      have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
      linarith
    have hrp : (0 : ℝ) < (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) :=
      Real.rpow_pos_of_pos hL0 _
    linarith
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hbase := thm_a2'_of_rows_chiSummed_pool_L_gk K (q := q) (N := 2 * Xd) (M := M) (Xd := Xd)
    (a := fun χ => winCutH Xd (doorChiCoeff_L_gk K χ M)) (X := ((Xd : ℕ) : ℝ))
    (h := ((2 ^ j : ℕ) : ℝ)) (π₀ := π₀) (Cs := fun _ => Cs) (Ccc := fun _ => Ccc)
    (C₁' := fun _ => cfbC₁ ((Xd : ℕ) : ℝ) C₁) (M₀ := fun _ => M₀) (ε := fun _ => ε)
    hM hX hX3 hh4 hhX (fun χ n => doorRow_ha1_L_gk K χ M Xd n)
    (fun χ n hn => doorRow_hsupp0_L_gk K χ M Xd n hn) hN2 hTann hceil hrowsSum hT0bandSum
    hpool (fun _ => hgP1) (fun _ => hgRows) (fun _ => hgU) hgBand
  simp only [shortSum_winCutH_seamS0] at hbase
  refine le_trans hbase (le_of_eq ?_)
  rw [a2_sum_const_chars]
  unfold a2DoorGrade_pool_L_gk
  ring

/-- `DoorFuseFrame_pool_L` (:175), at the lever.  Two of the ten fields move: `gP1`'s `𝒫₁` is
written at the levered base and `gRows` reads `ThmA2.a2RowsSum_gk`. -/
structure DoorFuseFrame_pool_L_gk (K : ℕ) (M Xd j : ℕ) (Cs Ccc ε π₀ : ℝ) : Prop where
  /-- `e ≤ X_d` — the frozen interface's lower scale pin. -/
  X_exp : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)
  /-- `3 ≤ X_d`. -/
  X_three : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ)
  /-- `4 ≤ 2^j` — the AS-2 MVT guard (NOT `3`). -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- Lemma 14's window frame `2^j ≤ X_d·(log X_d)^{−1/5}`. -/
  h_window : ((2 ^ j : ℕ) : ℝ)
    ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ))
  /-- `TannGate X_d (2X_d/2^j)` — the annulus gate at the family's bottom height. -/
  tann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))
  /-- `5 ≤ loglog(2X_d/2^j)` — the `h`-ceiling. -/
  ceil5 : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
  /-- The first GRADING gate, on the `𝒯`-leg constant `Cs`, AT THE POOL AND THE LEVER. -/
  gP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀
  /-- The second GRADING gate, at the levered row sum and `Ccc`, AT THE POOL. -/
  gRows : 5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀
  /-- **THE `𝒰`-LEG, POOLED** — `ε` carries no exponent-room constraint. -/
  eps_pool : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀
  /-- **THE BAND ABSORPTION, POOLED** — replacing `L4096`. -/
  band_pool : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀

/-- `m4_chiSummedFreeRowBig_of_doorGrade_pool_L` (:225), at the lever. -/
theorem m4_chiSummedFreeRowBig_of_doorGrade_pool_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M)
    {C₁ M₀ π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloorL M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)) (π₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig_L_gk K R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) (π₀ (A + s)) :=
    a2DoorGrade_pool_nonneg_L_gk K hM (log_natCast_nonneg' (A + s)) hh0 (hpool (A + s))
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans
    (hgrade H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H j A s hjfl

/-- `m4_chiSummedFreeRow_of_doorGrade_pool_L` (:259), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorGrade_pool_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) {C₁ M₀ π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloorL M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)) (π₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) :=
  m4_chiSummedFreeRow_of_big_L_gk K
    (m4_chiSummedFreeRowBig_of_doorGrade_pool_L_gk K hM hpool hgrade henv)

/-- `m4_chiSummedFreeRow_of_doorAssembly_pool_L` (:285), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_pool_L_gk K M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow_L_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorGrade_pool_L_gk K hM (C₁ := C₁) (M₀ := M₀) (π₀ := π₀) hpool
    ?_ henv
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb : SocketBaseL R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_pool_L_gk K hM hF.X_exp hF.X_three hF.h_four hF.h_window
    hF.tann hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows hF.eps_pool
    hF.band_pool
/-! ## §5 — `M4BaseNarrow` -/

/-- **THE ROW DATUM AT ONE BASE** (`M4RowDatumAt_L`).  One `(H, L, χ, A)`; the dyadic lengths
`j ≤ log₂L` and the shifts `s ≤ L` are the only quantifiers left.  This is what the
per-instance register speaks, and what §2–§4 consume. -/
def M4RowDatumAt_L (M : ℕ) (MS : ℕ → ℕ → ℝ) (H L : ℕ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (A : ℕ) : Prop :=
  ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
    1 / ((A + s : ℕ) : ℝ)
        * (∫ y in ((A + s : ℕ) : ℝ)..(2 * ((A + s : ℕ) : ℝ)),
            ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                * shortSum (doorChiCoeff_L χ M)
                    (seamS0 (2 * (A + s)) ((A + s : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ MS j H

/-- **THE FREE SHIFTED BRIDGE, AT ONE BASE** (`m4_freeShiftBlock_at_L`).  `M4CoprimeSupply` §2
at a fixed base: the per-length, per-shift row mean square becomes the shifted block sum of
squared sieved-twisted window sums, at the grade `2·MS` plus the explicit slack residue
`(2·(2·MS) + 8)·(2^j)²` — neither residue term carries a factor `A`. -/
theorem m4_freeShiftBlock_at_L {M H L q : ℕ} {χ : DirichletCharacter ℂ q} {MS : ℕ → ℕ → ℝ}
    {A B : ℕ} (hA : 0 < A) (hL4 : 4 ≤ L) (hfit : B + L ≤ 2 * A + 4)
    (hrow : M4RowDatumAt_L M MS H L χ A) :
    ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
      ∑ n ∈ Finset.Ioc (A + s) (B + s),
          ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * (2 * MS j H) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
  intro j hjL s hsL
  have hL0 : 0 < L := by omega
  have h2j : 2 ^ j ≤ L :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hjL) (Nat.pow_log_le_self 2 hL0.ne')
  have hh0 : 0 < 2 ^ j := Nat.two_pow_pos _
  have hAs : 0 < A + s := by omega
  have hAsR : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by exact_mod_cast hAs
  -- ⟦the fit, at the interface's slack⟧
  have hfitS : (B + s) + 2 ^ j ≤ 2 * (A + s) + 4 := by omega
  -- ⟦the coverage, on the DROPPED block⟧
  have hcov : ∀ n ∈ Finset.Ioc (A + s) (B + s - 4), ∀ m ∈ Finset.Ioc n (n + 2 ^ j),
      m ∉ seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ) → doorChiCoeff_L χ M m = 0 := by
    intro n hn m hm hns
    have hn' := Finset.mem_Ioc.mp hn
    have hne : A + s < B + s - 4 := lt_of_lt_of_le hn'.1 hn'.2
    exact absurd (mem_seamS0_of_block_window (X := (((A + s : ℕ)) : ℝ))
      (N := 2 * (A + s)) le_rfl (by omega) hn hm) hns
  -- ⟦the row datum, read at the removed phase⟧
  have hMSrow : 1 / (((A + s : ℕ)) : ℝ)
      * (∫ y in (((A + s : ℕ)) : ℝ)..(2 * (((A + s : ℕ)) : ℝ)),
          ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff_L χ M) 0)
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ MS j H := by
    rw [doorCoeffPhase_zero]
    exact hrow j hjL s hsL
  have hMS0 : (0 : ℝ) ≤ MS j H :=
    le_trans (meanSq_nonneg (doorCoeffPhase (doorChiCoeff_L χ M) 0)
      (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) ((2 ^ j : ℕ) : ℝ) hAsR) hMSrow
  -- ⟦the slack-`4` block bound⟧
  have hslack := sum_Ioc_absWindowSum_sq_div_le_slack4
    (c := doorChiCoeff_L χ M) (fun m => norm_doorChiCoeff_le_one_L χ M m)
    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) 0 (H := 2 ^ j) (A := A + s) (B := B + s)
    (MS := MS j H) hh0 hAs hfitS hcov hMSrow
  -- ⟦the exchange at the shifted block⟧
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
        ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hnB : (n : ℝ) ≤ (((B + s : ℕ)) : ℝ) := by exact_mod_cast hn2
    have hvnn : (0 : ℝ) ≤ ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ) := by
      positivity
    calc ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
        = (n : ℝ) * (‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
          field_simp
      _ ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hnB hvnn
  have hex : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
      ≤ (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H
          + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg _)
  -- ⟦the two comparisons the free block affords⟧
  have hBs2 : (((B + s : ℕ)) : ℝ) ≤ 2 * (A : ℝ) + 4 := by
    have hnat : B + s ≤ 2 * A + 4 := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hBAs : (((B + s : ℕ)) : ℝ) ≤ 2 * (((A + s : ℕ)) : ℝ) := by
    have hnat : B + s ≤ 2 * (A + s) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hD0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ) := by positivity
  have h1 : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
      ≤ (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H) :=
    mul_le_mul_of_nonneg_right hBs2 (by positivity)
  have h2 : (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      ≤ 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) :=
    mul_le_mul_of_nonneg_right hBAs (by positivity)
  have h3 : 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    field_simp
    ring
  have hsplit : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H
        + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
        + (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    ring
  have hr : (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
      = 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + 4 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
  have hfinal : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
      ≤ 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (2 * (2 * MS j H) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    rw [hsplit] at hex
    have hgoal : 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (2 * (2 * MS j H) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2
        = (2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + 4 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2) + 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
    rw [hgoal, ← hr, ← h3]
    linarith
  simpa only [absWindowSum_doorChiCoeff_zero_L] using hfinal

set_option maxHeartbeats 1600000 in
-- the dyadic assembly is `M4Maximal`'s at a free block: the triple-nested `Finset` sums are
-- re-elaborated against the free `(A, B]` and `L`, which is what costs the heartbeats
/-- **THE FREE MAXIMAL STEP, AT ONE BASE** (`m4_chiBlock_at_L`).  The χ-layer of the narrowed
coprime family at a fixed base, from the shifted fixed-length datum, at the graded price
`m4BclGraded j₀ Fan Ftr`. -/
theorem m4_chiBlock_at_L {R : ChowlaRegime} {M H L q : ℕ} {χ : DirichletCharacter ℂ q}
    {F : ℕ → ℕ → ℝ} {Fan Ftr : ℕ → ℝ} (j₀ : ℕ) {A B : ℕ}
    (hlo : R.Hlo ≤ H) (hnar : (H : ℝ) ≤ arcDen 12 H * (L : ℝ))
    (hA : 0 < A) (hfit : B + L ≤ 2 * A + 4)
    (hFan0 : 0 ≤ Fan H) (hFtr0 : 0 ≤ Ftr H)
    (han : ∀ j : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (hG1 : 2 * arcDen 12 H ^ 2 ≤ Ftr H)
    (hG2 : 108 / 5 * Fan H + 432 / 5 ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : 8 * arcDen 12 H ≤ (H : ℝ))
    (hfix : ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
      ∑ n ∈ Finset.Ioc (A + s) (B + s),
          ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * F j H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2)
    (hLH : L ≤ H) :
    ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2
      ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
  classical
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hBcl0 : (0 : ℝ) ≤ m4BclGraded j₀ Fan Ftr H := m4BclGraded_nonneg hFan0 hFtr0
  -- ⟦THE NARROWING, read against the arc gate: the free length cannot be short⟧
  have hL8R : (8 : ℝ) ≤ (L : ℝ) :=
    le_of_mul_le_mul_left (by linarith : arcDen 12 H * 8 ≤ arcDen 12 H * (L : ℝ)) harc0
  have hL8 : 8 ≤ L := by exact_mod_cast hL8R
  have hL0 : 0 < L := by omega
  have hL0R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL0
  by_cases hAB : B < A
  · -- ⟦the empty block⟧
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hBcl0 (sq_nonneg _)) (Nat.cast_nonneg _)
  rw [Nat.not_lt] at hAB
  -- ⟦the non-empty block: the fit's three consequences⟧
  have hA4 : 4 ≤ A := by omega
  have hB2A : B ≤ 2 * A := by omega
  have hL2A : (L : ℝ) ≤ 2 * (A : ℝ) := by
    have hnat : L ≤ 2 * A := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  set Lg := Nat.log 2 L with hLg
  set X : ℕ → ℕ → ℕ → ℝ := fun j t n =>
    ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2 with hX
  set SL : ℝ := ∑ j ∈ Finset.range (Lg + 1), (3 / 2 : ℝ) ^ j with hSL
  have hSL0 : (0 : ℝ) ≤ SL := (geom_weight_sum_pos Lg).le
  -- ⟦STEP 1⟧ the pointwise maximal bound, at the free length and the geometric weights
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B, SL
          * ∑ j ∈ Finset.range (Lg + 1),
              (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j :=
    Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic_L χ M L n
  -- ⟦STEP 2⟧ the sums commute (the weight rides the `j`-index only)
  have hswap : ∑ n ∈ Finset.Ioc A B, SL
        * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j
      = SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, X j t n) * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    exact Finset.sum_comm
  -- ⟦STEP 3⟧ each (scale, offset) pair is a shifted fixed-length block sum
  have hsle : ∀ j t : ℕ, t ≤ L / 2 ^ (j + 1) → 2 ^ (j + 1) * t ≤ L := by
    intro j t ht
    calc 2 ^ (j + 1) * t ≤ 2 ^ (j + 1) * (L / 2 ^ (j + 1)) := Nat.mul_le_mul_left _ ht
      _ = L / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_comm _ _
      _ ≤ L := Nat.div_mul_le_self L (2 ^ (j + 1))
  have hshift : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, X j t n
      = ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
          ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2 := fun j t =>
    sum_Ioc_shift (fun n => ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2) A B _
  -- ⟦the analytic half: the datum, read through the envelope⟧
  have hjtL : ∀ j t : ℕ, j ≤ Lg → j₀ ≤ j → t ≤ L / 2 ^ (j + 1) →
      ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * Fan H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t hjLg hj₀ ht
    rw [hshift j t]
    have hd := hfix j hjLg (2 ^ (j + 1) * t) (hsle j t ht)
    have hFle := han j hj₀
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hP0 hA0R]
  -- ⟦the trivial half: the ABSOLUTE grade `1`, no row datum consulted⟧
  have hjtS : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, X j t n
      ≤ (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t
    rw [hshift j t]
    have hterm : ∀ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
        ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by
      intro n _
      have h := norm_sum_doorSievedWindow_le_L χ M (2 ^ j) n
      have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ := norm_nonneg _
      nlinarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have hcast : ((B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) : ℕ) : ℝ) ≤ (A : ℝ) := by
      have hnat : B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) ≤ A := by omega
      exact_mod_cast hnat
    have h2j : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
    nlinarith
  -- ⟦STEP 4⟧ the per-scale count × weight
  set W : ℕ → ℝ := fun j =>
    (((L / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 with hW
  have hW0 : ∀ j, (0 : ℝ) ≤ W j := fun j => dyadic_count_weight_term_nonneg L j
  have hWw0 : ∀ j, (0 : ℝ) ≤ W j * (2 / 3 : ℝ) ^ j := fun j =>
    mul_nonneg (hW0 j) (by positivity)
  have hjL : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j hjm
    have hjmem := Finset.mem_filter.mp hjm
    have hjLg : j ≤ Lg := by have := Finset.mem_range.mp hjmem.1; omega
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            (Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
              + (2 * Fan H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
      Finset.sum_le_sum fun t ht =>
        hjtL j t hjLg hjmem.2 (by have := Finset.mem_range.mp ht; omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((Fan H * (A : ℝ) + (2 * Fan H + 8)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  have hjS : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j _
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1), (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
      Finset.sum_le_sum fun t _ => hjtS j t
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (A : ℝ) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((A : ℝ) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  -- ⟦STEP 5⟧ THE SPLIT, at the geometric weights
  have hCan0 : (0 : ℝ) ≤ Fan H * (A : ℝ) + (2 * Fan H + 8) := by nlinarith
  have hlarge : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8))
          * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum hjL
      _ ≤ ∑ j ∈ Finset.range (Lg + 1),
            (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hCan0 (hWw0 j))
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hsmall : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    have hsub : (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
            (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := Finset.sum_le_sum hjS
      _ ≤ ∑ j ∈ Finset.range j₀, (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg hA0R (hWw0 j))
      _ = (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by rw [Finset.mul_sum]
  have hcount : ∑ j ∈ Finset.range (Lg + 1),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
        + (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Lg + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧ §4's two weighted counts, then the ledger
  have hLgN : Nat.log 2 L ≤ Nat.log 2 H := Nat.log_mono_right hLH
  have hgl1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ Lg := one_le_pow₀ (by norm_num)
  have hglg : (3 / 2 : ℝ) ^ Lg ≤ (3 / 2 : ℝ) ^ (Nat.log 2 H) := by
    rw [hLg]; gcongr; norm_num
  have hfull : SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
      ≤ 54 / 5 * (L : ℝ) ^ 2 := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_le hL0
  have hhead : SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_small_le hL0 j₀
  -- ⟦G1, STRENGTHENED⟧ the two consequences the weighted head needs
  have hFtrL : 2 * (H : ℝ) ≤ Ftr H * (L : ℝ) := by
    have h2 : 2 * arcDen 12 H * (L : ℝ) ≤ Ftr H * (L : ℝ) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hL0R.le
    linarith [hnar]
  have hFtrL2 : (H : ℝ) ^ 2 ≤ Ftr H * (L : ℝ) ^ 2 := by
    have hsq : (H : ℝ) ^ 2 ≤ (arcDen 12 H * (L : ℝ)) ^ 2 := by nlinarith [hnar, hH0R.le]
    nlinarith [hsq, sq_nonneg ((L : ℝ))]
  -- ⟦the first budget line⟧ the trivial head's `(4/3)^{j₀}` half AND the slack residue
  have hEkey : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H * (L : ℝ) ^ 2 :=
    by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hH0R]
    have hstep : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (H : ℝ)
        ≤ 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (H : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hglg
        (by positivity : (0 : ℝ) ≤ 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ))
      nlinarith [h, hH0R.le]
    have hmain : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (H : ℝ)
        ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ * Ftr H * (L : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hFtrL
        (by positivity : (0 : ℝ) ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀
          * (L : ℝ))
      nlinarith [h]
    linarith
  have hres : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2
        + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀)
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hstep : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2
        ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ)) := by
      have h1 : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2 ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hG2 (sq_nonneg ((L : ℝ)))
        nlinarith [this]
      nlinarith [mul_le_mul_of_nonneg_left hL2A
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ))]
    have hgl : (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ))
        ≤ (2 / 9) * ((A : ℝ) * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg)) := by
      nlinarith [mul_le_mul_of_nonneg_left hgl1
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (A : ℝ))]
    have hbud := mul_le_mul_of_nonneg_left hEkey hA0R
    nlinarith [hstep, hgl, hbud]
  -- ⟦the second budget line⟧ the trivial head's `(8/3)^{j₀}` half — ⟦G1⟧ at `arcDen²`
  have hres2 : (A : ℝ) * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
    have hkey : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) := by
      have h1 : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hglg
          (by positivity : (0 : ℝ) ≤ 9 / 5 * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2)
        nlinarith [h]
      have h2 : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hFtrL2 (by positivity)
      linarith
    have hdiv : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2) := by
      have hrw : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2)
          = (9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2))
              / (H : ℝ) ^ 2 := by
        field_simp
      rw [hrw, le_div_iff₀ hH2]
      linarith [hkey]
    nlinarith [mul_le_mul_of_nonneg_left hdiv hA0R]
  have hfinal : (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (54 / 5 * (L : ℝ) ^ 2)
        + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
          + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hexp : m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ)
        = 54 / 5 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
          + 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ)
          + 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ) := by
      unfold m4BclGraded m4Cmax
      ring
    rw [hexp]
    nlinarith [hres, hres2]
  calc ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2
      ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j := by
        rw [← hswap]; exact hstep1
    _ ≤ SL * ((Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
          + (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hcount hSL0
    _ = (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * (SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j)
          + (A : ℝ) * (SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) := by ring
    _ ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (54 / 5 * (L : ℝ) ^ 2)
          + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
            + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) := by
        have h1 := mul_le_mul_of_nonneg_left hfull hCan0
        have h2 := mul_le_mul_of_nonneg_left hhead hA0R
        linarith
    _ ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := hfinal

/-- **THE χ-REDUCTION AT ONE BASE** (`m4_classBlock_at_L`).  The class sup's block mean square
from the χ-layer's, at the SAME grade. -/
theorem m4_classBlock_at_L {M L q : ℕ} (hq : 0 < q) {r : ℕ} (hcop : Nat.Coprime q r)
    {A B : ℕ} {Bc : ℝ}
    (hchi : ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2 ≤ Bc * (L : ℝ) ^ 2 * (A : ℝ)) :
    ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff_L M) L n q r) ^ 2
      ≤ Bc * (L : ℝ) ^ 2 * (A : ℝ) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hpt : ∀ n : ℕ, (classSup (doorSievedCoeff_L M) L n q r) ^ 2
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L χ M L n) ^ 2 := by
    intro n
    have hle := classSup_le_inv_totient_sum_doorChiSup_L hcop M L n
    have h0 := classSup_nonneg (doorSievedCoeff_L M) L n q r
    have hsq : (classSup (doorSievedCoeff_L M) L n q r) ^ 2
        ≤ ((q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup_L χ M L n) ^ 2 := by
      nlinarith
    exact hsq.trans (sq_inv_totient_sum_le_sum_sq (fun χ => doorChiSup_L χ M L n))
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff_L M) L n q r) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B,
          (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L χ M L n) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc A B,
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L χ M L n) ^ 2
      = (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hswap] at hstep1
  exact hstep1.trans (inv_totient_sum_le hchi)

/-- **THE COPRIME BLOCK MEAN SQUARE, AT ONE BASE** (`m4_coprimeBlock_at_L`) — §2 ∘ §3 ∘ §4
composed at a fixed `(H, L, q, r, A, B)`, at the grade
`m4BclGraded (doorRowFloorL M) (2·MSan) (2·MStr)` — **verbatim** the grade the register
carries, so no register line moves. -/
theorem m4_coprimeBlock_at_L {R : ChowlaRegime} {M H L q r A B : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ}
    (hlo : R.Hlo ≤ H) (hLH : L ≤ H) (hnar : (H : ℝ) ≤ arcDen 12 H * (L : ℝ))
    (hq : 0 < q) (hcop : Nat.Coprime q r) (hA : 0 < A) (hfit : B + L ≤ 2 * A + 4)
    (hMSan0 : 0 ≤ MSan H) (hMStr0 : 0 ≤ MStr H)
    (han : ∀ j : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H)
    (hG1 : arcDen 12 H ^ 2 ≤ MStr H)
    (hG2 : 44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M)
    (harc8 : 8 * arcDen 12 H ≤ (H : ℝ))
    (hrow : ∀ χ : DirichletCharacter ℂ q, M4RowDatumAt_L M MS H L χ A) :
    ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff_L M) L n q r) ^ 2
      ≤ m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hL8R : (8 : ℝ) ≤ (L : ℝ) :=
    le_of_mul_le_mul_left (by linarith : arcDen 12 H * 8 ≤ arcDen 12 H * (L : ℝ)) harc0
  have hL8 : 8 ≤ L := by exact_mod_cast hL8R
  have hFan0 : (0 : ℝ) ≤ 2 * MSan H := mul_nonneg (by norm_num) hMSan0
  have hFtr0 : (0 : ℝ) ≤ 2 * MStr H := mul_nonneg (by norm_num) hMStr0
  have hG1' : 2 * arcDen 12 H ^ 2 ≤ 2 * MStr H := by linarith
  have hG2' : 108 / 5 * (2 * MSan H) + 432 / 5 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M := by linarith
  refine m4_classBlock_at_L hq hcop (fun χ => ?_)
  refine m4_chiBlock_at_L (R := R) (F := fun j _ => 2 * MS j H) (doorRowFloorL M)
    hlo hnar hA hfit hFan0 hFtr0 (fun j hj => ?_) hG1' hG2' harc8 ?_ hLH
  · have := han j hj; linarith
  · exact m4_freeShiftBlock_at_L hA (by omega) hfit (hrow χ)

set_option maxHeartbeats 1600000 in
-- `M4NonCoprime.m4_nonCoprime_classMeanSq_N`'s own cause: the dilated branch's `calc` carries
-- four nested `classSup` sums over re-indexed blocks; no tactic search happens below
/-- **⟦R2⟧ FROM THE LADDER'S ROW DATA** (`m4_classBlockMeanSq_of_rowDatum_L`).
`M4ClassBlockMeanSq_L` at EVERY class of `q`, from the row datum at the ladder bases and at
their dilations.  The two consumption sites of `m4_nonCoprime_classMeanSq_N_L`, and nothing
else, are what the two hypotheses `hrow1`/`hrowd` feed. -/
theorem m4_classBlockMeanSq_of_rowDatum_L {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ}
    (hM : 1 ≤ M) (hMSan0 : ∀ H : ℕ, 0 ≤ MSan H) (hMStr0 : ∀ H : ℕ, 0 ≤ MStr H)
    (han : ∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ))
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ))
    (hrow1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
        M4RowDatumAt_L M MS H H χ (doorLadder R.x H (i + 1)))
    (hrowd : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ arcDen 12 H →
        M4RowDatumAt_L M MS H (H / d + 1) χ (doorLadder R.x H (i + 1) / d - 1)) :
    M4ClassBlockMeanSq_L R M k
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) := by
  intro H hlo hhi q hq hqQ i hik r hrq
  -- ⟦the block, and the ladder's two facts⟧
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
  have hfit : doorLadder R.x H i + H ≤ 2 * doorLadder R.x H (i + 1) := doorLadder_fit R.x H i
  have hApos : 0 < doorLadder R.x H (i + 1) := by omega
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hH0R : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  by_cases hcase : Nat.gcd r q = 1
  · -- ⟦d₀ = 1⟧ the class is already coprime: the datum at the door block, `L = H`
    have hcopqr : Nat.Coprime q r := by
      rw [Nat.Coprime, Nat.gcd_comm]; exact hcase
    have hnarrow : (H : ℝ) ≤ arcDen 12 H * (H : ℝ) := by nlinarith
    exact m4_coprimeBlock_at_L (R := R) hlo le_rfl hnarrow hq hcopqr hApos (by omega)
      (hMSan0 H) (hMStr0 H) (fun j hj => han j H hj) (hG1 H hlo hhi) (hG2 H hlo hhi)
      (harc8 H hlo hhi) (fun χ => hrow1 H hlo hhi q hq hqQ i hik χ)
  · -- ⟦d₀ > 1⟧ ONE dilation, then the `d₀`-to-one re-index of the block
    have hd2 : 2 ≤ Nat.gcd r q := by omega
    have hdq : Nat.gcd r q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)
    have h2q : 2 * q ≤ H := by
      have hR : ((2 * q : ℕ) : ℝ) ≤ (H : ℝ) := by
        push_cast
        have := harc H hlo hhi
        linarith
      exact_mod_cast hR
    have hdA : Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hdA2 : 2 * Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hA2 : 2 ≤ doorLadder R.x H (i + 1) / Nat.gcd r q :=
      (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hA'pos : 0 < doorLadder R.x H (i + 1) / Nat.gcd r q - 1 := by omega
    -- ⟦the reduced pair⟧
    have hq₀ : 0 < q / Nat.gcd r q :=
      Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)) hd
    have hq₀Q : ((q / Nat.gcd r q : ℕ) : ℝ) ≤ arcDen 12 H := by
      refine le_trans ?_ hqQ
      exact_mod_cast Nat.div_le_self q (Nat.gcd r q)
    have hcop₀ : Nat.Coprime (q / Nat.gcd r q) (r / Nat.gcd r q) :=
      (m4_class_dilate_coprime hq r).symm
    -- ⟦the dilated window length⟧
    have hH'H : H / Nat.gcd r q + 1 ≤ H := by
      have hstep : H / Nat.gcd r q ≤ H / 2 := Nat.div_le_div_left hd2 (by norm_num)
      omega
    -- ⟦THE NARROWING, at the dilated length: `H ≤ d₀·L ≤ arcDen·L`⟧
    have hdR : (Nat.gcd r q : ℝ) ≤ arcDen 12 H := by
      refine le_trans ?_ hqQ
      exact_mod_cast hdq
    have hnarrow : (H : ℝ) ≤ arcDen 12 H * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := by
      have hexp : Nat.gcd r q * (H / Nat.gcd r q + 1)
          = Nat.gcd r q * (H / Nat.gcd r q) + Nat.gcd r q := by ring
      have hdm : Nat.gcd r q * (H / Nat.gcd r q) + H % Nat.gcd r q = H :=
        Nat.div_add_mod H (Nat.gcd r q)
      have hmod : H % Nat.gcd r q < Nat.gcd r q := Nat.mod_lt _ hd
      have hnat : H ≤ Nat.gcd r q * (H / Nat.gcd r q + 1) := by omega
      have hR : (H : ℝ) ≤ (Nat.gcd r q : ℝ) * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hL0 : (0 : ℝ) ≤ ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    -- ⟦the pointwise transport, then the fibre count, then the datum, then the ledger⟧
    have hpt : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff_L M) H n q r) ^ 2
          ≤ (fun n' => (classSup (doorSievedCoeff_L M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2) (n / Nat.gcd r q) := by
      intro n _
      have hle := classSup_le_dilate_L (M := M) (H := H) (q := q) (r := r) (n := n)
        (W := arcDen 12 H) hM hq hqQ (hgate H hlo hhi)
      have h0 := classSup_nonneg (doorSievedCoeff_L M) H n q r
      simp only
      nlinarith
    have hmaps : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        n / Nat.gcd r q ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
          (doorLadder R.x H i / Nat.gcd r q) := fun n hn => div_mem_reindexed hd hdA hn
    have hdatum := m4_coprimeBlock_at_L (R := R) (MS := MS) (MSan := MSan) (MStr := MStr)
      hlo hH'H hnarrow hq₀ hcop₀ hA'pos (dilBlock_reindex_fit hd hdA hfit)
      (hMSan0 H) (hMStr0 H) (fun j hj => han j H hj) (hG1 H hlo hhi) (hG2 H hlo hhi)
      (harc8 H hlo hhi)
      (fun χ => hrowd H hlo hhi (q / Nat.gcd r q) hq₀ hq₀Q i hik χ (Nat.gcd r q) hd2 hdR)
    have hd0R : (0 : ℝ) ≤ (Nat.gcd r q : ℝ) := Nat.cast_nonneg _
    have hBcl0 : (0 : ℝ) ≤ m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H)
        (fun H => 2 * MStr H) H :=
      m4BclGraded_nonneg (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
        (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff_L M) H n q r) ^ 2
        ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L M) (H / Nat.gcd r q + 1) (n / Nat.gcd r q)
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 := Finset.sum_le_sum hpt
      _ ≤ (Nat.gcd r q : ℝ)
            * ∑ n' ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
                (doorLadder R.x H i / Nat.gcd r q),
              (classSup (doorSievedCoeff_L M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 :=
          sum_Ioc_comp_div_le
            (f := fun n' => (classSup (doorSievedCoeff_L M) (H / Nat.gcd r q + 1) n'
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2)
            (fun _ => sq_nonneg _) (d := Nat.gcd r q) hd hmaps
      _ ≤ (Nat.gcd r q : ℝ)
            * (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
                * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) ^ 2
                * ((doorLadder R.x H (i + 1) / Nat.gcd r q - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hdatum hd0R
      _ ≤ m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
            * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) :=
          d0_ledger hd hH'H hBcl0

/-- **THE BASE-NARROWED ROW INTERFACE** (`M4ChiFreeRowMeanSqN_L`) —
`M4CoprimeSupply.M4ChiFreeRowMeanSq` with ⟦THE BASE NARROWING⟧ `Φ H · L ≤ A` inserted
directly after `0 < A`, and NOTHING else changed.  Strictly weaker as a hypothesis on a
supplier, strictly stronger as a demand on a consumer. -/
def M4ChiFreeRowMeanSqN_L (R : ChowlaRegime) (M : ℕ) (MS : ℕ → ℕ → ℝ) (Φ : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 L,
      ∀ A : ℕ, 0 < A → Φ H * (L : ℝ) ≤ (A : ℝ) → ∀ s ≤ L,
        1 / ((A + s : ℕ) : ℝ)
            * (∫ y in ((A + s : ℕ) : ℝ)..(2 * ((A + s : ℕ) : ℝ)),
                ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                    * shortSum (doorChiCoeff_L χ M)
                        (seamS0 (2 * (A + s)) ((A + s : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
          ≤ MS j H

set_option maxHeartbeats 1600000 in
-- the same cause as `M4DoorClose` §4: the `∀d` register mentions `DoorRowCarriedT0_L` under
-- seven binders and is elaborated against `DoorRowCarried_L`'s ~85 conjuncts through the
-- bridge; no tactic search happens below
/-- **THE ROW DATA AT THE LADDER AND ITS DILATIONS** (`m4_rowDatum_dilated_L`), from ⟦W5⟧'s
`∀d` per-instance register.  The three outputs are exactly what
`m4_wave_closed_of_dyadicRow_L` and §5 consume. -/
theorem m4_rowDatum_dilated_L :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ)
        (Kbox X₀w : ℕ → ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧ (∀ Qm : ℕ, 0 ≤ Kbox Qm) ∧
      (∀ Qm : ℕ, 0 < X₀w Qm) ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
            doorRowFloorL M ≤ j → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H →
              ∀ s ≤ H / d + 1,
                DoorRowCarriedT0_L (Kbox Qm) (X₀w Qm) Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk
                    (Kcf Qm) Ctail χ M
                  (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H)) →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
            ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
              M4RowDatumAt_L M MS H H χ (doorLadder R.x H (i + 1)))
            ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ d : ℕ, 2 ≤ d →
                (d : ℝ) ≤ arcDen 12 H →
                  M4RowDatumAt_L M MS H (H / d + 1) χ
                    (doorLadder R.x H (i + 1) / d - 1)) := by
  -- ⟦THE SKOLEM CUT⟧ the `T₀`-bridge's two constants, as functions of the modulus range
  choose Kbox X₀w hK0 hX₀0 hbridge using doorRowCarried_of_t0free_L
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hmeansq⟩ :=
    m4_door_meansq_carried_L
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hK0, hX₀0, ?_⟩
  intro R Qm M k MS hM hQm htriv harc hcarT0
  -- ⟦the carried form, at every dilated base⟧
  have hcar : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
        ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H → ∀ s ≤ H / d + 1,
          DoorRowCarried_L Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
            (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H) := by
    intro H hlo hhi q hq hqQ i hik χ j hjH hj0 d hd hdA s hsL
    haveI : NeZero q := ⟨by omega⟩
    have hqQm : q ≤ Qm := by
      have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hRq
    exact hbridge Qm Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail q χ M
      (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H) hqQm
      (hcarT0 H hlo hhi q hq hqQ i hik χ j hjH hj0 d hd hdA s hsL)
  -- ⟦the mean square at every dilated base and every dyadic length⟧
  have hms : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
        ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H → ∀ s ≤ H / d + 1,
          1 / ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)
              * (∫ y in ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)..(2
                    * ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)),
                  ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                      * shortSum (doorChiCoeff_L χ M)
                          (seamS0 (2 * (doorLadder R.x H (i + 1) / d - 1 + s))
                            ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)) y
                          ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
            ≤ MS j H := by
    intro H hlo hhi q hq hqQ i hik χ j hjH d hd hdA s hsL
    -- ⟦the dilated base is positive: `2d ≤ H < X_{i+1}` forces `⌊X_{i+1}/d⌋ ≥ 2`⟧
    have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
    have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
    have h2d : 2 * d ≤ H := by
      have hR : ((2 * d : ℕ) : ℝ) ≤ (H : ℝ) := by
        push_cast
        have := harc H hlo hhi
        linarith
      exact_mod_cast hR
    have hA2 : 2 ≤ doorLadder R.x H (i + 1) / d :=
      (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hXpos : 0 < doorLadder R.x H (i + 1) / d - 1 + s := by omega
    by_cases hcase : doorRowFloorL M ≤ j
    · have hqQm : q ≤ Qm := by
        have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
        exact_mod_cast hRq
      exact hmeansq Qm q χ hq hqQm M (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H) hM
        hcase
        (hcar H hlo hhi q hq hqQ i hik χ j hjH hcase d hd hdA s hsL)
    · exact le_trans (doorRow_trivial_grade_L χ M j hXpos) (htriv j H (not_le.mp hcase))
  constructor
  · -- ⟦the ladder bases: the `d = 1` instance at the shift `s + 1`⟧
    intro H hlo hhi q hq hqQ i hik χ j hjL s hsL
    have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
    have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hd1 : ((1 : ℕ) : ℝ) ≤ arcDen 12 H := by push_cast; linarith
    have heq : doorLadder R.x H (i + 1) / 1 - 1 + (s + 1) = doorLadder R.x H (i + 1) + s := by
      rw [Nat.div_one]; omega
    have h := hms H hlo hhi q hq hqQ i hik χ j hjL 1 (by norm_num) hd1 (s + 1)
      (by rw [Nat.div_one]; omega)
    rwa [heq] at h
  · -- ⟦the dilated bases⟧
    intro H hlo hhi q hq hqQ i hik χ d hd2 hdA j hjL s hsL
    have hH2 : H / d + 1 ≤ H := by
      have h2d : 2 * d ≤ H := by
        have hR : ((2 * d : ℕ) : ℝ) ≤ (H : ℝ) := by
          push_cast
          have := harc H hlo hhi
          linarith
        exact_mod_cast hR
      have hstep : H / d ≤ H / 2 := Nat.div_le_div_left hd2 (by norm_num)
      omega
    exact hms H hlo hhi q hq hqQ i hik χ j (le_trans hjL (Nat.log_mono_right hH2)) d
      (by omega) hdA s hsL

set_option maxHeartbeats 1600000 in
-- the register mentions `DoorRowCarriedT0_L` under seven binders and is elaborated against
-- `m4_wave_closed_of_dyadicRow_L`'s own list; no tactic search happens below
/-- **THE M4 WAVE, COLLAPSED** (`m4_wave_collapsed_L`) — ⟦THE FINAL REGISTER⟧, regime and
witnessed data ONLY, with **no analytic arm at all**, closes the M4/S9 road:

  (the regime gates) + (the witnessed data) → `¬ logChowla2Fails R.eps R.x R.ω`.

Against `M4Collapse.m4_wave_closed_coprime_discharged` the diff is exactly TWO lines: the
per-instance register gains ⟦W5⟧'s ruled `∀d` quantifier over the DILATED bases, and the last
analytic line `M4CoprimeSupply.M4ChiFreeRowMeanSq R M MS` is GONE.  Every other byte — the
fifteen hoisted constants, the outer `(C, U1floor, g)` shape, the envelope gates, the drift
line, the two delivered lines, the modulus caps, ⟦G1⟧, ⟦G2⟧, ⟦the regime fact⟧, and the
conclusion — is identical.

## ⟦THE FINAL REGISTER⟧ — the S11 spine's consumption contract, complete

**(a) REGIME-ABSORBABLE GATES**, each an inequality in the regime's own parameters,
choosable by the spine before any datum is exhibited:

1. the OUTER shapes, chosen BEFORE `R`: `U1floor ≤ R.Hlo` and `g R.Hhi R.ω ≤ R.x` at the
   spine's own `U1floor : ℕ` and `g : ℕ → ℕ → ℕ`;
2. `M4DoorGates_L Cg R M k δ` — the EIGHT fields of `M4Close.M4DoorGates` (`hM`, `hδ`, `hMδ`,
   `hlogω`, `hpow`, `hcount`, `hreach`, `hblocks`);
3. `1 ≤ M`;
4. the three envelope positivities `0 ≤ MSan H`, `0 ≤ MStr H`, `0 ≤ Braw H`;
5. the two envelope gates `MS j H ≤ MSan H` at `j₀ ≤ j` and `MS j H ≤ MStr H` at `j < j₀`,
   `j₀ = doorRowFloorL M = M·AdoorL M`;
6. the `q`-graded drift price
   `(1 + 2π·arcDen 12 H/q)²·(q²·(3·m4BclGraded j₀ (2·MSan) (2·MStr) H)) ≤ Braw H`;
7. `√(Braw H) ≤ mrtDeliveredGrade (C/2) H`;
8. `δ/4 + 4·2^k/R.x ≤ mrtDeliveredGrade (C/2) H`;
9. the modulus cap `arcDen 12 H ≤ Qm` — with `Qm` in the WITNESSED group (beside `M`, `k`),
   so it is chosen AFTER `R`: `m4_modulusCap_discharged` closes it outright at
   `Qm := ⌈arcDen 12 R.Hhi⌉₊`;
10. the small lengths' trivial grade `4 ≤ MS j H` at `j < j₀`;
11. **the PER-INSTANCE `T₀`-free register, `∀d`** —
    `DoorRowCarriedT0_L Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
    (⌊doorLadder R.x H (i+1)/d⌋ − 1 + s) j (MS j H)`, at every `H ∈ [R.Hlo, R.Hhi]`, every
    `q ≤ arcDen 12 H`, every `i < k`, every `χ mod q`, every `j ≤ log₂H` above the floor,
    every `d` with `0 < d` and `(d:ℝ) ≤ arcDen 12 H`, and every `s ≤ ⌊H/d⌋ + 1` — itself
    ~98 conjuncts (the scale page at the BLOCK scale, the band gates, the door gates, the
    socket's ~25, the tail threshold, the endpoint, the `DoorRowT0Gates` EIGHT and the
    instance envelope);
12. the dilation cap, `M`-RELATIVE: `arcDen 12 H < calP (AdoorL M) (3072M) 1 = 2^{AdoorL M}`
    (`M4Residue.door_dilation_gate'`) — a demand on the witnessed `M`, not a numeral cap on
    the window length (`M4Spine`'s ⟦WALL C⟧, the misplaced numeral);
13. `2·arcDen 12 H ≤ H`;
14. ⟦the regime fact⟧ `8·arcDen 12 H ≤ H`;
15. ⟦G1⟧ `arcDen 12 H ^ 2 ≤ MStr H`;
16. ⟦G2⟧ `12·MSan H + 24 ≤ 4^{j₀}`.

**(b) WITNESSED DATA** — what the spine must exhibit, and check non-vacuous: `C ≥ 0`,
`U1floor`, `g`, then `δ`, `Braw`, `MS`, `MSan`, `MStr`, `Qm`, `M`, `k`.  `Qm` sits here — not
outside — because the four opaque constants it feeds (`Kfl`, `Kcf`, `Kbox`, `X₀w`) are now
CHOICE FUNCTIONS of it (`ℕ → ℝ`), Skolemised out of their suppliers; that is what lets gates
9 and 12 be read against the regime and the door instead of against numerals.  `R` is NOT
witnessed: the exit produces it (only `R.eps = ε`, `U1floor ≤ R.Hlo`, `g R.Hhi R.ω ≤ R.x` are
visible).
The anti-vacuity duty sits at line 11, at the BOTTOM ladder rungs, the TOP dyadic length and
the LARGEST dilation `d ≍ arcDen 12 H`, where the scale page's coupling gate
`h ≤ X·(log X)^{−1/5}` bites; `hreach` and the `g`-arm are what buy the room, through
`M4Collapse.doorLadder_pow_lower` (`R.x/2^{i} ≤ X_i`) and `hcount` (`2^k ≤ 4R.ω`):
`⌊X_{i+1}/d⌋ − 1 ≥ R.x/(4·R.ω·arcDen 12 H) − 2`.

**(c) ANALYTIC ARMS** — none. -/
theorem m4_wave_collapsed_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ)
        (Kcf : ℕ → ℝ) (Ctail : ℝ) (Kbox X₀w : ℕ → ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧ (∀ Qm : ℕ, 0 ≤ Kbox Qm) ∧
      (∀ Qm : ℕ, 0 < X₀w Qm) ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (Qm M k : ℕ),
            M4DoorGates_L Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            -- ⟦THE PER-INSTANCE REGISTER, ∀d OVER THE DILATED BASES (⟦W5⟧)⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H →
                  ∀ s ≤ H / d + 1,
                    DoorRowCarriedT0_L (Kbox Qm) (X₀w Qm) Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk
                        (Kcf Qm) Ctail χ M
                      (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦the regime fact⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦G1⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            -- ⟦G2⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hK0, hX₀0, hdata⟩ :=
    m4_rowDatum_dilated_L
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_dyadicRow_L
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr Qm M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcarT0 hgate harc harc8 hG1 hG2
  obtain ⟨hrow1, hrowd⟩ := hdata R Qm M k MS hM hQm htriv harc hcarT0
  -- ⟦the dyadic row datum: the `d = 1` family is exactly `M4ChiDyadicRowMeanSq_L`⟧
  have hdyad : M4ChiDyadicRowMeanSq_L R M k MS :=
    fun H hlo hhi q hq hqQ i hik χ j hjL s hsH =>
      hrow1 H hlo hhi q hq hqQ i hik χ j hjL s hsH
  -- ⟦R2 at every class of `q`, from the ladder's row data and their dilations⟧
  have hnc : M4ClassBlockMeanSq_L R M k
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_classBlockMeanSq_of_rowDatum_L hM hMSan0 hMStr0 han hG1 hG2 harc8 hgate harc
      hrow1 hrowd
  refine hR δ Braw MS MSan MStr (doorRowFloorL M) M k hgates hMSan0 hMStr0 hBraw0 han htr
    hdrift hdel hrest hdyad ?_
  intro H hlo hhi q hq hqQ i hik r hrq _hncop
  exact hnc H hlo hhi q hq hqQ i hik r hrq

set_option maxHeartbeats 1600000 in
-- the twin restates the whole register and elaborates it against the theorem above; the
-- proof itself is one destructuring
/-- **THE COLLISION FORM** (`m4_wave_collapsed_False_L`).  `m4_wave_collapsed_L`'s register with
`logChowla2Fails R.eps R.x R.ω` assumed: the chain closes to `False`.  Byte-for-byte the
theorem above with `¬ P` read as `P → False`. -/
theorem m4_wave_collapsed_False_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ)
        (Kcf : ℕ → ℝ) (Ctail : ℝ) (Kbox X₀w : ℕ → ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧ (∀ Qm : ℕ, 0 ≤ Kbox Qm) ∧
      (∀ Qm : ℕ, 0 < X₀w Qm) ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (Qm M k : ℕ),
            M4DoorGates_L Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H →
                  ∀ s ≤ H / d + 1,
                    DoorRowCarriedT0_L (Kbox Qm) (X₀w Qm) Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk
                        (Kcf Qm) Ctail χ M
                      (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M) →
            logChowla2Fails R.eps R.x R.ω → False := by
  obtain ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩ := m4_wave_collapsed_L
  exact ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩

/-- `M4RowDatumAt_L` (:124), at the lever. -/
def M4RowDatumAt_L_gk (K : ℕ) (M : ℕ) (MS : ℕ → ℕ → ℝ) (H L : ℕ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (A : ℕ) : Prop :=
  ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
    1 / ((A + s : ℕ) : ℝ)
        * (∫ y in ((A + s : ℕ) : ℝ)..(2 * ((A + s : ℕ) : ℝ)),
            ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                * shortSum (doorChiCoeff_L_gk K χ M)
                    (seamS0 (2 * (A + s)) ((A + s : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ MS j H

/-- `m4_freeShiftBlock_at_L` (:145), at the lever. -/
theorem m4_freeShiftBlock_at_L_gk (K : ℕ) {M H L q : ℕ} {χ : DirichletCharacter ℂ q}
    {MS : ℕ → ℕ → ℝ}
    {A B : ℕ} (hA : 0 < A) (hL4 : 4 ≤ L) (hfit : B + L ≤ 2 * A + 4)
    (hrow : M4RowDatumAt_L_gk K M MS H L χ A) :
    ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
      ∑ n ∈ Finset.Ioc (A + s) (B + s),
          ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * (2 * MS j H) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
  intro j hjL s hsL
  have hL0 : 0 < L := by omega
  have h2j : 2 ^ j ≤ L :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hjL) (Nat.pow_log_le_self 2 hL0.ne')
  have hh0 : 0 < 2 ^ j := Nat.two_pow_pos _
  have hAs : 0 < A + s := by omega
  have hAsR : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by exact_mod_cast hAs
  -- ⟦the fit, at the interface's slack⟧
  have hfitS : (B + s) + 2 ^ j ≤ 2 * (A + s) + 4 := by omega
  -- ⟦the coverage, on the DROPPED block⟧
  have hcov : ∀ n ∈ Finset.Ioc (A + s) (B + s - 4), ∀ m ∈ Finset.Ioc n (n + 2 ^ j),
      m ∉ seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ) → doorChiCoeff_L_gk K χ M m = 0 := by
    intro n hn m hm hns
    have hn' := Finset.mem_Ioc.mp hn
    have hne : A + s < B + s - 4 := lt_of_lt_of_le hn'.1 hn'.2
    exact absurd (mem_seamS0_of_block_window (X := (((A + s : ℕ)) : ℝ))
      (N := 2 * (A + s)) le_rfl (by omega) hn hm) hns
  -- ⟦the row datum, read at the removed phase⟧
  have hMSrow : 1 / (((A + s : ℕ)) : ℝ)
      * (∫ y in (((A + s : ℕ)) : ℝ)..(2 * (((A + s : ℕ)) : ℝ)),
          ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff_L_gk K χ M) 0)
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ MS j H := by
    rw [doorCoeffPhase_zero]
    exact hrow j hjL s hsL
  have hMS0 : (0 : ℝ) ≤ MS j H :=
    le_trans (meanSq_nonneg (doorCoeffPhase (doorChiCoeff_L_gk K χ M) 0)
      (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) ((2 ^ j : ℕ) : ℝ) hAsR) hMSrow
  -- ⟦the slack-`4` block bound⟧
  have hslack := sum_Ioc_absWindowSum_sq_div_le_slack4
    (c := doorChiCoeff_L_gk K χ M) (fun m => norm_doorChiCoeff_le_one_L_gk K χ M m)
    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) 0 (H := 2 ^ j) (A := A + s) (B := B + s)
    (MS := MS j H) hh0 hAs hfitS hcov hMSrow
  -- ⟦the exchange at the shifted block⟧
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
        ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hnB : (n : ℝ) ≤ (((B + s : ℕ)) : ℝ) := by exact_mod_cast hn2
    have hvnn : (0 : ℝ) ≤ ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ) := by
      positivity
    calc ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
        = (n : ℝ) * (‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
          field_simp
      _ ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hnB hvnn
  have hex : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
      ≤ (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H
          + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg _)
  -- ⟦the two comparisons the free block affords⟧
  have hBs2 : (((B + s : ℕ)) : ℝ) ≤ 2 * (A : ℝ) + 4 := by
    have hnat : B + s ≤ 2 * A + 4 := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hBAs : (((B + s : ℕ)) : ℝ) ≤ 2 * (((A + s : ℕ)) : ℝ) := by
    have hnat : B + s ≤ 2 * (A + s) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hD0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ) := by positivity
  have h1 : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
      ≤ (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H) :=
    mul_le_mul_of_nonneg_right hBs2 (by positivity)
  have h2 : (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      ≤ 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) :=
    mul_le_mul_of_nonneg_right hBAs (by positivity)
  have h3 : 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    field_simp
    ring
  have hsplit : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H
        + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
        + (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    ring
  have hr : (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
      = 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + 4 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
  have hfinal : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
      ≤ 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (2 * (2 * MS j H) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    rw [hsplit] at hex
    have hgoal : 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (2 * (2 * MS j H) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2
        = (2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + 4 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2) + 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
    rw [hgoal, ← hr, ← h3]
    linarith
  simpa only [absWindowSum_doorChiCoeff_zero_L_gk K] using hfinal

set_option maxHeartbeats 1600000 in
-- the dyadic assembly is `M4Maximal`'s at a free block: the triple-nested `Finset` sums are
-- re-elaborated against the free `(A, B]` and `L`, which is what costs the heartbeats
/-- `m4_chiBlock_at_L` (:272), at the lever. -/
theorem m4_chiBlock_at_L_gk (K : ℕ) {R : ChowlaRegime} {M H L q : ℕ} {χ : DirichletCharacter ℂ q}
    {F : ℕ → ℕ → ℝ} {Fan Ftr : ℕ → ℝ} (j₀ : ℕ) {A B : ℕ}
    (hlo : R.Hlo ≤ H) (hnar : (H : ℝ) ≤ arcDen 12 H * (L : ℝ))
    (hA : 0 < A) (hfit : B + L ≤ 2 * A + 4)
    (hFan0 : 0 ≤ Fan H) (hFtr0 : 0 ≤ Ftr H)
    (han : ∀ j : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (hG1 : 2 * arcDen 12 H ^ 2 ≤ Ftr H)
    (hG2 : 108 / 5 * Fan H + 432 / 5 ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : 8 * arcDen 12 H ≤ (H : ℝ))
    (hfix : ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
      ∑ n ∈ Finset.Ioc (A + s) (B + s),
          ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * F j H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2)
    (hLH : L ≤ H) :
    ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
      ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
  classical
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hBcl0 : (0 : ℝ) ≤ m4BclGraded j₀ Fan Ftr H := m4BclGraded_nonneg hFan0 hFtr0
  -- ⟦THE NARROWING, read against the arc gate: the free length cannot be short⟧
  have hL8R : (8 : ℝ) ≤ (L : ℝ) :=
    le_of_mul_le_mul_left (by linarith : arcDen 12 H * 8 ≤ arcDen 12 H * (L : ℝ)) harc0
  have hL8 : 8 ≤ L := by exact_mod_cast hL8R
  have hL0 : 0 < L := by omega
  have hL0R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL0
  by_cases hAB : B < A
  · -- ⟦the empty block⟧
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hBcl0 (sq_nonneg _)) (Nat.cast_nonneg _)
  rw [Nat.not_lt] at hAB
  -- ⟦the non-empty block: the fit's three consequences⟧
  have hA4 : 4 ≤ A := by omega
  have hB2A : B ≤ 2 * A := by omega
  have hL2A : (L : ℝ) ≤ 2 * (A : ℝ) := by
    have hnat : L ≤ 2 * A := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  set Lg := Nat.log 2 L with hLg
  set X : ℕ → ℕ → ℕ → ℝ := fun j t n =>
    ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2 with hX
  set SL : ℝ := ∑ j ∈ Finset.range (Lg + 1), (3 / 2 : ℝ) ^ j with hSL
  have hSL0 : (0 : ℝ) ≤ SL := (geom_weight_sum_pos Lg).le
  -- ⟦STEP 1⟧ the pointwise maximal bound, at the free length and the geometric weights
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B, SL
          * ∑ j ∈ Finset.range (Lg + 1),
              (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j :=
    Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic_L_gk K χ M L n
  -- ⟦STEP 2⟧ the sums commute (the weight rides the `j`-index only)
  have hswap : ∑ n ∈ Finset.Ioc A B, SL
        * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j
      = SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, X j t n) * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    exact Finset.sum_comm
  -- ⟦STEP 3⟧ each (scale, offset) pair is a shifted fixed-length block sum
  have hsle : ∀ j t : ℕ, t ≤ L / 2 ^ (j + 1) → 2 ^ (j + 1) * t ≤ L := by
    intro j t ht
    calc 2 ^ (j + 1) * t ≤ 2 ^ (j + 1) * (L / 2 ^ (j + 1)) := Nat.mul_le_mul_left _ ht
      _ = L / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_comm _ _
      _ ≤ L := Nat.div_mul_le_self L (2 ^ (j + 1))
  have hshift : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, X j t n
      = ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
          ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2 := fun j t =>
    sum_Ioc_shift (fun n => ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2) A B _
  -- ⟦the analytic half: the datum, read through the envelope⟧
  have hjtL : ∀ j t : ℕ, j ≤ Lg → j₀ ≤ j → t ≤ L / 2 ^ (j + 1) →
      ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * Fan H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t hjLg hj₀ ht
    rw [hshift j t]
    have hd := hfix j hjLg (2 ^ (j + 1) * t) (hsle j t ht)
    have hFle := han j hj₀
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hP0 hA0R]
  -- ⟦the trivial half: the ABSOLUTE grade `1`, no row datum consulted⟧
  have hjtS : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, X j t n
      ≤ (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t
    rw [hshift j t]
    have hterm : ∀ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
        ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by
      intro n _
      have h := norm_sum_doorSievedWindow_le_L_gk K χ M (2 ^ j) n
      have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ := norm_nonneg _
      nlinarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have hcast : ((B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) : ℕ) : ℝ) ≤ (A : ℝ) := by
      have hnat : B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) ≤ A := by omega
      exact_mod_cast hnat
    have h2j : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
    nlinarith
  -- ⟦STEP 4⟧ the per-scale count × weight
  set W : ℕ → ℝ := fun j =>
    (((L / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 with hW
  have hW0 : ∀ j, (0 : ℝ) ≤ W j := fun j => dyadic_count_weight_term_nonneg L j
  have hWw0 : ∀ j, (0 : ℝ) ≤ W j * (2 / 3 : ℝ) ^ j := fun j =>
    mul_nonneg (hW0 j) (by positivity)
  have hjL : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j hjm
    have hjmem := Finset.mem_filter.mp hjm
    have hjLg : j ≤ Lg := by have := Finset.mem_range.mp hjmem.1; omega
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            (Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
              + (2 * Fan H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
      Finset.sum_le_sum fun t ht =>
        hjtL j t hjLg hjmem.2 (by have := Finset.mem_range.mp ht; omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((Fan H * (A : ℝ) + (2 * Fan H + 8)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  have hjS : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j _
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1), (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
      Finset.sum_le_sum fun t _ => hjtS j t
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (A : ℝ) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((A : ℝ) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  -- ⟦STEP 5⟧ THE SPLIT, at the geometric weights
  have hCan0 : (0 : ℝ) ≤ Fan H * (A : ℝ) + (2 * Fan H + 8) := by nlinarith
  have hlarge : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8))
          * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum hjL
      _ ≤ ∑ j ∈ Finset.range (Lg + 1),
            (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hCan0 (hWw0 j))
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hsmall : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    have hsub : (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
            (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := Finset.sum_le_sum hjS
      _ ≤ ∑ j ∈ Finset.range j₀, (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg hA0R (hWw0 j))
      _ = (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by rw [Finset.mul_sum]
  have hcount : ∑ j ∈ Finset.range (Lg + 1),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
        + (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Lg + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧ §4's two weighted counts, then the ledger
  have hLgN : Nat.log 2 L ≤ Nat.log 2 H := Nat.log_mono_right hLH
  have hgl1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ Lg := one_le_pow₀ (by norm_num)
  have hglg : (3 / 2 : ℝ) ^ Lg ≤ (3 / 2 : ℝ) ^ (Nat.log 2 H) := by
    rw [hLg]; gcongr; norm_num
  have hfull : SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
      ≤ 54 / 5 * (L : ℝ) ^ 2 := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_le hL0
  have hhead : SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_small_le hL0 j₀
  -- ⟦G1, STRENGTHENED⟧ the two consequences the weighted head needs
  have hFtrL : 2 * (H : ℝ) ≤ Ftr H * (L : ℝ) := by
    have h2 : 2 * arcDen 12 H * (L : ℝ) ≤ Ftr H * (L : ℝ) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hL0R.le
    linarith [hnar]
  have hFtrL2 : (H : ℝ) ^ 2 ≤ Ftr H * (L : ℝ) ^ 2 := by
    have hsq : (H : ℝ) ^ 2 ≤ (arcDen 12 H * (L : ℝ)) ^ 2 := by nlinarith [hnar, hH0R.le]
    nlinarith [hsq, sq_nonneg ((L : ℝ))]
  -- ⟦the first budget line⟧ the trivial head's `(4/3)^{j₀}` half AND the slack residue
  have hEkey : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H * (L : ℝ) ^ 2 :=
    by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hH0R]
    have hstep : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (H : ℝ)
        ≤ 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (H : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hglg
        (by positivity : (0 : ℝ) ≤ 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ))
      nlinarith [h, hH0R.le]
    have hmain : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (H : ℝ)
        ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ * Ftr H * (L : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hFtrL
        (by positivity : (0 : ℝ) ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀
          * (L : ℝ))
      nlinarith [h]
    linarith
  have hres : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2
        + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀)
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hstep : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2
        ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ)) := by
      have h1 : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2 ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hG2 (sq_nonneg ((L : ℝ)))
        nlinarith [this]
      nlinarith [mul_le_mul_of_nonneg_left hL2A
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ))]
    have hgl : (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ))
        ≤ (2 / 9) * ((A : ℝ) * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg)) := by
      nlinarith [mul_le_mul_of_nonneg_left hgl1
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (A : ℝ))]
    have hbud := mul_le_mul_of_nonneg_left hEkey hA0R
    nlinarith [hstep, hgl, hbud]
  -- ⟦the second budget line⟧ the trivial head's `(8/3)^{j₀}` half — ⟦G1⟧ at `arcDen²`
  have hres2 : (A : ℝ) * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
    have hkey : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) := by
      have h1 : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hglg
          (by positivity : (0 : ℝ) ≤ 9 / 5 * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2)
        nlinarith [h]
      have h2 : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hFtrL2 (by positivity)
      linarith
    have hdiv : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2) := by
      have hrw : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2)
          = (9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2))
              / (H : ℝ) ^ 2 := by
        field_simp
      rw [hrw, le_div_iff₀ hH2]
      linarith [hkey]
    nlinarith [mul_le_mul_of_nonneg_left hdiv hA0R]
  have hfinal : (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (54 / 5 * (L : ℝ) ^ 2)
        + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
          + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hexp : m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ)
        = 54 / 5 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
          + 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ)
          + 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ) := by
      unfold m4BclGraded m4Cmax
      ring
    rw [hexp]
    nlinarith [hres, hres2]
  calc ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
      ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j := by
        rw [← hswap]; exact hstep1
    _ ≤ SL * ((Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
          + (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hcount hSL0
    _ = (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * (SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j)
          + (A : ℝ) * (SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) := by ring
    _ ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (54 / 5 * (L : ℝ) ^ 2)
          + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
            + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) := by
        have h1 := mul_le_mul_of_nonneg_left hfull hCan0
        have h2 := mul_le_mul_of_nonneg_left hhead hA0R
        linarith
    _ ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := hfinal

/-- `m4_classBlock_at_L` (:601), at the lever. -/
theorem m4_classBlock_at_L_gk (K : ℕ) {M L q : ℕ} (hq : 0 < q) {r : ℕ} (hcop : Nat.Coprime q r)
    {A B : ℕ} {Bc : ℝ}
    (hchi : ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2 ≤ Bc * (L : ℝ) ^ 2 * (A : ℝ)) :
    ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff_L_gk K M) L n q r) ^ 2
      ≤ Bc * (L : ℝ) ^ 2 * (A : ℝ) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hpt : ∀ n : ℕ, (classSup (doorSievedCoeff_L_gk K M) L n q r) ^ 2
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L_gk K χ M L n) ^ 2 := by
    intro n
    have hle := classSup_le_inv_totient_sum_doorChiSup_L_gk K hcop M L n
    have h0 := classSup_nonneg (doorSievedCoeff_L_gk K M) L n q r
    have hsq : (classSup (doorSievedCoeff_L_gk K M) L n q r) ^ 2
        ≤ ((q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup_L_gk K χ M L n) ^ 2 := by
      nlinarith
    exact hsq.trans (sq_inv_totient_sum_le_sum_sq (fun χ => doorChiSup_L_gk K χ M L n))
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff_L_gk K M) L n q r) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B,
          (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L_gk K χ M L n) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc A B,
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L_gk K χ M L n) ^ 2
      = (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hswap] at hstep1
  exact hstep1.trans (inv_totient_sum_le hchi)

/-- `m4_coprimeBlock_at_L` (:633), at the lever. -/
theorem m4_coprimeBlock_at_L_gk (K : ℕ) {R : ChowlaRegime} {M H L q r A B : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ}
    (hlo : R.Hlo ≤ H) (hLH : L ≤ H) (hnar : (H : ℝ) ≤ arcDen 12 H * (L : ℝ))
    (hq : 0 < q) (hcop : Nat.Coprime q r) (hA : 0 < A) (hfit : B + L ≤ 2 * A + 4)
    (hMSan0 : 0 ≤ MSan H) (hMStr0 : 0 ≤ MStr H)
    (han : ∀ j : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H)
    (hG1 : arcDen 12 H ^ 2 ≤ MStr H)
    (hG2 : 44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M)
    (harc8 : 8 * arcDen 12 H ≤ (H : ℝ))
    (hrow : ∀ χ : DirichletCharacter ℂ q, M4RowDatumAt_L_gk K M MS H L χ A) :
    ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff_L_gk K M) L n q r) ^ 2
      ≤ m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hL8R : (8 : ℝ) ≤ (L : ℝ) :=
    le_of_mul_le_mul_left (by linarith : arcDen 12 H * 8 ≤ arcDen 12 H * (L : ℝ)) harc0
  have hL8 : 8 ≤ L := by exact_mod_cast hL8R
  have hFan0 : (0 : ℝ) ≤ 2 * MSan H := mul_nonneg (by norm_num) hMSan0
  have hFtr0 : (0 : ℝ) ≤ 2 * MStr H := mul_nonneg (by norm_num) hMStr0
  have hG1' : 2 * arcDen 12 H ^ 2 ≤ 2 * MStr H := by linarith
  have hG2' : 108 / 5 * (2 * MSan H) + 432 / 5 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M := by linarith
  refine m4_classBlock_at_L_gk K hq hcop (fun χ => ?_)
  refine m4_chiBlock_at_L_gk K (R := R) (F := fun j _ => 2 * MS j H) (doorRowFloorL M)
    hlo hnar hA hfit hFan0 hFtr0 (fun j hj => ?_) hG1' hG2' harc8 ?_ hLH
  · have := han j hj; linarith
  · exact m4_freeShiftBlock_at_L_gk K hA (by omega) hfit (hrow χ)

set_option maxHeartbeats 1600000 in
-- `M4NonCoprime.m4_nonCoprime_classMeanSq_N`'s own cause: the dilated branch's `calc` carries
-- four nested `classSup` sums over re-indexed blocks; no tactic search happens below
/-- `m4_classBlockMeanSq_of_rowDatum_L` (:675), at the lever. -/
theorem m4_classBlockMeanSq_of_rowDatum_L_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ}
    (hM : 1 ≤ M) (hMSan0 : ∀ H : ℕ, 0 ≤ MSan H) (hMStr0 : ∀ H : ℕ, 0 ≤ MStr H)
    (han : ∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ))
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ))
    (hrow1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
        M4RowDatumAt_L_gk K M MS H H χ (doorLadder R.x H (i + 1)))
    (hrowd : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ arcDen 12 H →
        M4RowDatumAt_L_gk K M MS H (H / d + 1) χ (doorLadder R.x H (i + 1) / d - 1)) :
    M4ClassBlockMeanSq_L_gk K R M k
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) := by
  intro H hlo hhi q hq hqQ i hik r hrq
  -- ⟦the block, and the ladder's two facts⟧
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
  have hfit : doorLadder R.x H i + H ≤ 2 * doorLadder R.x H (i + 1) := doorLadder_fit R.x H i
  have hApos : 0 < doorLadder R.x H (i + 1) := by omega
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hH0R : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  by_cases hcase : Nat.gcd r q = 1
  · -- ⟦d₀ = 1⟧ the class is already coprime: the datum at the door block, `L = H`
    have hcopqr : Nat.Coprime q r := by
      rw [Nat.Coprime, Nat.gcd_comm]; exact hcase
    have hnarrow : (H : ℝ) ≤ arcDen 12 H * (H : ℝ) := by nlinarith
    exact m4_coprimeBlock_at_L_gk K (R := R) hlo le_rfl hnarrow hq hcopqr hApos (by omega)
      (hMSan0 H) (hMStr0 H) (fun j hj => han j H hj) (hG1 H hlo hhi) (hG2 H hlo hhi)
      (harc8 H hlo hhi) (fun χ => hrow1 H hlo hhi q hq hqQ i hik χ)
  · -- ⟦d₀ > 1⟧ ONE dilation, then the `d₀`-to-one re-index of the block
    have hd2 : 2 ≤ Nat.gcd r q := by omega
    have hdq : Nat.gcd r q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)
    have h2q : 2 * q ≤ H := by
      have hR : ((2 * q : ℕ) : ℝ) ≤ (H : ℝ) := by
        push_cast
        have := harc H hlo hhi
        linarith
      exact_mod_cast hR
    have hdA : Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hdA2 : 2 * Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hA2 : 2 ≤ doorLadder R.x H (i + 1) / Nat.gcd r q :=
      (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hA'pos : 0 < doorLadder R.x H (i + 1) / Nat.gcd r q - 1 := by omega
    -- ⟦the reduced pair⟧
    have hq₀ : 0 < q / Nat.gcd r q :=
      Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)) hd
    have hq₀Q : ((q / Nat.gcd r q : ℕ) : ℝ) ≤ arcDen 12 H := by
      refine le_trans ?_ hqQ
      exact_mod_cast Nat.div_le_self q (Nat.gcd r q)
    have hcop₀ : Nat.Coprime (q / Nat.gcd r q) (r / Nat.gcd r q) :=
      (m4_class_dilate_coprime hq r).symm
    -- ⟦the dilated window length⟧
    have hH'H : H / Nat.gcd r q + 1 ≤ H := by
      have hstep : H / Nat.gcd r q ≤ H / 2 := Nat.div_le_div_left hd2 (by norm_num)
      omega
    -- ⟦THE NARROWING, at the dilated length: `H ≤ d₀·L ≤ arcDen·L`⟧
    have hdR : (Nat.gcd r q : ℝ) ≤ arcDen 12 H := by
      refine le_trans ?_ hqQ
      exact_mod_cast hdq
    have hnarrow : (H : ℝ) ≤ arcDen 12 H * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := by
      have hexp : Nat.gcd r q * (H / Nat.gcd r q + 1)
          = Nat.gcd r q * (H / Nat.gcd r q) + Nat.gcd r q := by ring
      have hdm : Nat.gcd r q * (H / Nat.gcd r q) + H % Nat.gcd r q = H :=
        Nat.div_add_mod H (Nat.gcd r q)
      have hmod : H % Nat.gcd r q < Nat.gcd r q := Nat.mod_lt _ hd
      have hnat : H ≤ Nat.gcd r q * (H / Nat.gcd r q + 1) := by omega
      have hR : (H : ℝ) ≤ (Nat.gcd r q : ℝ) * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hL0 : (0 : ℝ) ≤ ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    -- ⟦the pointwise transport, then the fibre count, then the datum, then the ledger⟧
    have hpt : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
          ≤ (fun n' => (classSup (doorSievedCoeff_L_gk K M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2) (n / Nat.gcd r q) := by
      intro n _
      have hle := classSup_le_dilate_L_gk K (M := M) (H := H) (q := q) (r := r) (n := n)
        (W := arcDen 12 H) hM hq hqQ (hgate H hlo hhi)
      have h0 := classSup_nonneg (doorSievedCoeff_L_gk K M) H n q r
      simp only
      nlinarith
    have hmaps : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        n / Nat.gcd r q ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
          (doorLadder R.x H i / Nat.gcd r q) := fun n hn => div_mem_reindexed hd hdA hn
    have hdatum := m4_coprimeBlock_at_L_gk K (R := R) (MS := MS) (MSan := MSan) (MStr := MStr)
      hlo hH'H hnarrow hq₀ hcop₀ hA'pos (dilBlock_reindex_fit hd hdA hfit)
      (hMSan0 H) (hMStr0 H) (fun j hj => han j H hj) (hG1 H hlo hhi) (hG2 H hlo hhi)
      (harc8 H hlo hhi)
      (fun χ => hrowd H hlo hhi (q / Nat.gcd r q) hq₀ hq₀Q i hik χ (Nat.gcd r q) hd2 hdR)
    have hd0R : (0 : ℝ) ≤ (Nat.gcd r q : ℝ) := Nat.cast_nonneg _
    have hBcl0 : (0 : ℝ) ≤ m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H)
        (fun H => 2 * MStr H) H :=
      m4BclGraded_nonneg (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
        (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
        ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L_gk K M) (H / Nat.gcd r q + 1) (n / Nat.gcd r q)
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 := Finset.sum_le_sum hpt
      _ ≤ (Nat.gcd r q : ℝ)
            * ∑ n' ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
                (doorLadder R.x H i / Nat.gcd r q),
              (classSup (doorSievedCoeff_L_gk K M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 :=
          sum_Ioc_comp_div_le
            (f := fun n' => (classSup (doorSievedCoeff_L_gk K M) (H / Nat.gcd r q + 1) n'
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2)
            (fun _ => sq_nonneg _) (d := Nat.gcd r q) hd hmaps
      _ ≤ (Nat.gcd r q : ℝ)
            * (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
                * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) ^ 2
                * ((doorLadder R.x H (i + 1) / Nat.gcd r q - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hdatum hd0R
      _ ≤ m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
            * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) :=
          d0_ledger hd hH'H hBcl0

/-- `M4ChiFreeRowMeanSqN_L` (:811), at the lever. -/
def M4ChiFreeRowMeanSqN_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (MS : ℕ → ℕ → ℝ)
    (Φ : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 L,
      ∀ A : ℕ, 0 < A → Φ H * (L : ℝ) ≤ (A : ℝ) → ∀ s ≤ L,
        1 / ((A + s : ℕ) : ℝ)
            * (∫ y in ((A + s : ℕ) : ℝ)..(2 * ((A + s : ℕ) : ℝ)),
                ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                    * shortSum (doorChiCoeff_L_gk K χ M)
                        (seamS0 (2 * (A + s)) ((A + s : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
          ≤ MS j H

/-- **THE ROW DATUM AT EVERY DILATED BASE, AT THE LEVER** — `m4_rowDatum_dilated_L`
(:907). -/
theorem m4_rowDatum_dilated_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ)
        (Kbox X₀w : ℕ → ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧ (∀ Qm : ℕ, 0 ≤ Kbox Qm) ∧
      (∀ Qm : ℕ, 0 < X₀w Qm) ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
            doorRowFloorL M ≤ j → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H →
              ∀ s ≤ H / d + 1,
                DoorRowCarriedT0_L_gk K (Kbox Qm) (X₀w Qm) Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk
                    (Kcf Qm) Ctail χ M
                  (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H)) →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
            ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
              M4RowDatumAt_L_gk K M MS H H χ (doorLadder R.x H (i + 1)))
            ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ d : ℕ, 2 ≤ d →
                (d : ℝ) ≤ arcDen 12 H →
                  M4RowDatumAt_L_gk K M MS H (H / d + 1) χ
                    (doorLadder R.x H (i + 1) / d - 1)) := by
  -- ⟦THE SKOLEM CUT⟧ the `T₀`-bridge's two constants, as functions of the modulus range
  choose Kbox X₀w hK0 hX₀0 hbridge using doorRowCarried_of_t0free_L_gk K
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hmeansq⟩ :=
    m4_door_meansq_carried_L_gk K hK
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hK0, hX₀0, ?_⟩
  intro R Qm M k MS hM hQm htriv harc hcarT0
  -- ⟦the carried form, at every dilated base⟧
  have hcar : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
        ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H → ∀ s ≤ H / d + 1,
          DoorRowCarried_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
            (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H) := by
    intro H hlo hhi q hq hqQ i hik χ j hjH hj0 d hd hdA s hsL
    haveI : NeZero q := ⟨by omega⟩
    have hqQm : q ≤ Qm := by
      have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hRq
    exact hbridge Qm Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail q χ M
      (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H) hqQm
      (hcarT0 H hlo hhi q hq hqQ i hik χ j hjH hj0 d hd hdA s hsL)
  -- ⟦the mean square at every dilated base and every dyadic length⟧
  have hms : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
        ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H → ∀ s ≤ H / d + 1,
          1 / ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)
              * (∫ y in ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)..(2
                    * ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)),
                  ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                      * shortSum (doorChiCoeff_L_gk K χ M)
                          (seamS0 (2 * (doorLadder R.x H (i + 1) / d - 1 + s))
                            ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)) y
                          ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
            ≤ MS j H := by
    intro H hlo hhi q hq hqQ i hik χ j hjH d hd hdA s hsL
    -- ⟦the dilated base is positive: `2d ≤ H < X_{i+1}` forces `⌊X_{i+1}/d⌋ ≥ 2`⟧
    have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
    have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
    have h2d : 2 * d ≤ H := by
      have hR : ((2 * d : ℕ) : ℝ) ≤ (H : ℝ) := by
        push_cast
        have := harc H hlo hhi
        linarith
      exact_mod_cast hR
    have hA2 : 2 ≤ doorLadder R.x H (i + 1) / d :=
      (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hXpos : 0 < doorLadder R.x H (i + 1) / d - 1 + s := by omega
    by_cases hcase : doorRowFloorL M ≤ j
    · have hqQm : q ≤ Qm := by
        have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
        exact_mod_cast hRq
      exact hmeansq Qm q χ hq hqQm M (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H) hM
        hcase
        (hcar H hlo hhi q hq hqQ i hik χ j hjH hcase d hd hdA s hsL)
    · exact le_trans (doorRow_trivial_grade_L_gk K χ M j hXpos) (htriv j H (not_le.mp hcase))
  constructor
  · -- ⟦the ladder bases: the `d = 1` instance at the shift `s + 1`⟧
    intro H hlo hhi q hq hqQ i hik χ j hjL s hsL
    have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
    have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hd1 : ((1 : ℕ) : ℝ) ≤ arcDen 12 H := by push_cast; linarith
    have heq : doorLadder R.x H (i + 1) / 1 - 1 + (s + 1) = doorLadder R.x H (i + 1) + s := by
      rw [Nat.div_one]; omega
    have h := hms H hlo hhi q hq hqQ i hik χ j hjL 1 (by norm_num) hd1 (s + 1)
      (by rw [Nat.div_one]; omega)
    rwa [heq] at h
  · -- ⟦the dilated bases⟧
    intro H hlo hhi q hq hqQ i hik χ d hd2 hdA j hjL s hsL
    have hH2 : H / d + 1 ≤ H := by
      have h2d : 2 * d ≤ H := by
        have hR : ((2 * d : ℕ) : ℝ) ≤ (H : ℝ) := by
          push_cast
          have := harc H hlo hhi
          linarith
        exact_mod_cast hR
      have hstep : H / d ≤ H / 2 := Nat.div_le_div_left hd2 (by norm_num)
      omega
    exact hms H hlo hhi q hq hqQ i hik χ j (le_trans hjL (Nat.log_mono_right hH2)) d
      (by omega) hdA s hsL
/-! ## §6 — `M4RowsChiEnd` -/

/-- The Lemma-12 row sum is a sum of nonnegative terms (`1 ≤ X_d`, `2 ≤ H₁`, `1 ≤ P_j`). -/
private lemma d5_rowsSum_nonneg {A G Jb Xd : ℕ} {H1 : ℝ} (hXd : 1 ≤ Xd) (hH1 : 2 ≤ H1) :
    (0 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 Jb,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
        + 1 / (Xd : ℝ)) := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have hcalH : (0 : ℝ) < calH H1 j := by rw [calH]; nlinarith
  have hP1 : (1 : ℝ) ≤ ((calP A G j : ℕ) : ℝ) := by
    have h : 1 ≤ calP A G j := by simp only [calP]; exact Nat.one_le_two_pow
    exact_mod_cast h
  have hlogb : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have h1 : (0 : ℝ) ≤ (Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
      * (Real.exp 1 / (Xd : ℝ) ^ 2)) := by
    have hq : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH H1 j :=
      div_nonneg (by positivity) hcalH.le
    have hr : (0 : ℝ) ≤ Real.exp 1 / (Xd : ℝ) ^ 2 := by positivity
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1) hr
    nlinarith
  have h2 : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ) :=
    div_nonneg (by linarith) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 / (Xd : ℝ) := by positivity
  linarith

/-- **⟦THE SLOT, MET⟧** (`m4_hrowsSlot_at_door_end_L`).  The statement below is
`M4Assembly.m4_chiSummedFreeRow_of_doorAssembly`'s `hrows` binder VERBATIM at
`Cs ≡ Ct`, `Ccc ≡ Cp` — the compile is the certificate of the byte-fit.  Supplied by §6
through the datum bridge `M4Assembly.chiBarCoeff_doorRowDatum`.

`cU`, `bU` are the door's UNTWISTED Ramaré data (the twist is applied by the chain, not by
the consumer); `t₁` is the per-modulus ball-centre family the carried capstone speaks at. -/
theorem m4_hrowsSlot_at_door_end_L :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowEndBase_L M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                        (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ a2Mrow_L Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_door_end_L
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  -- ⟦THE DOOR INSTANCE'S OWN FRAME⟧
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have ha1 : ∀ n : ℕ, ‖winCutH (A + s) (doorCoeffU_L M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  have hslot := hrows q cU (winCutH (A + s) (doorCoeffU_L M)) bU ha1 hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS (fun n hn => winCutH_asupp hn) hD.reg hD.big hD.dom
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L] using hslot

/-- **⟦A4 — ITEM 11, WITH THE `hrows` SLOT GONE⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_end_L`).  `M4Assembly.m4_chiSummedFreeRow_of_doorAssembly`
instantiated at §7's supplier: `M4ChiSummed.M4ChiSummedFreeRow` — ⟦item 11⟧ of
`m4_second_road_L` — at the door grade

  `RS j H = if doorRowFloorL M ≤ j then RSbig j H else 4·arcDen 12 H`,

from the named gates alone, **with `hrows` no longer among them**.

⟦THE RESIDUE, AFTER THE FUSE⟧ (the PORT-AUDIT law)
* `hM` — `1 ≤ M`;
* `hb1`, `hc1` — the two `1`-bounds on the door's untwisted Ramaré data;
* `hframe` — `M4Assembly.DoorFuseFrame` at every base (eleven fields), unchanged;
* `hbase` — `DoorRowEndBase_L` at every base: the STRICT pair law plus the `q = 1` chain's own
  `X_d`-side reconciliation gates and the two weighting-frame numerals.  **This is what
  replaced `hrows`**;
* `hcap` — the carried A3 capstone family at the door pin `S ≡ 0`; supplier
  `M4RowsChi.m4_rowChi_capstone` (its own residue is that theorem's docstring);
* `hband` — the `T₀`-band per character, discharged by
  `M4T0DatumDischarge.m4_hT0band_at_door_discharged` under its own named gates;
* `henv` — THE ARITHMETIC, `arcDen 12 H · a2DoorGrade_L … ≤ RSbig j H`, still the only thing
  the assembly leaves open (the `φ(q) ≤ q ≤ arcDen 12 H` ledger IN THE OPEN).

Nothing else survives; in particular the assembly's `hrows` binder does not appear. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_end_L :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowEndBase_L M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                        (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H j A s : ℕ, doorRowFloorL M ≤ j →
          arcDen 12 H * a2DoorGrade_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
              (M₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end_L
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband henv
  exact m4_chiSummedFreeRow_of_doorAssembly_L (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) hM hframe
    (hslot R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband henv

/-- ⟦THE CANONICAL M4Assembly-SIDE MINT⟧ the `χ̄`-twist of the levered untwisted datum IS the
levered sieved χ-twisted datum — `M4Assembly.chiBarCoeff_doorCoeffU` (:175). -/
theorem chiBarCoeff_doorCoeffU_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) :
    chiBarCoeff q χ (doorCoeffU_L_gk K M) = doorChiCoeff_L_gk K χ M := by
  funext n
  simp only [chiBarCoeff_apply, doorCoeffU_L_gk, doorChiCoeff_L_gk, memSCoeff, liouChi]
  split_ifs
  · ring
  · rw [mul_zero]

/-- ⟦THE CANONICAL M4Assembly-SIDE MINT⟧ **THE BRIDGE AT THE G-LEVER** —
`M4Assembly.chiBarCoeff_doorRowDatum` (:195).  `chiBarCoeff_winCutH` is datum-generic and is
reused verbatim. -/
theorem chiBarCoeff_doorRowDatum_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd : ℕ) :
    chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M)) = winCutH Xd (doorChiCoeff_L_gk K χ M) := by
  rw [chiBarCoeff_winCutH, chiBarCoeff_doorCoeffU_L_gk]

/-- **THE DOOR BRIDGE, STRICT/FUSED, AT THE G-LEVER**
(`m4MrowChiEnd_le_a2Mrow_L_gk`).  Re-derived, NOT weakened through `a2Mrow_L_gk_le`: the target
`a2Mrow_L_gk` is the SMALLER number, so the polarity forbids a `le_trans` through the landed
bridge. -/
theorem m4MrowChiEnd_le_a2Mrow_L_gk (K : ℕ) {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    {Ct Cp X ε : ℝ}
    (hCp : 0 ≤ Cp) :
    m4MrowChiEnd Ct Cp (AdoorL M) (s13GK K M) M 2 Xd (H1doorL M) (1 / 12) X ε 0
      ≤ a2Mrow_L_gk K Ct Cp M Xd X ε := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlvl := level1_term_door_decays_L_gk K (M := M) hM (R := 9) (by norm_num)
  have hRS0 : (0 : ℝ) ≤ (∑ j ∈ Finset.Icc 1 2,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 16 * Real.logb 2 (2 * (Xd : ℝ))
            / ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
        + 1 / (Xd : ℝ))) + Cp * (2 / (M : ℝ)) := by
    have h2 : (0 : ℝ) ≤ Cp * (2 / (M : ℝ)) := by positivity
    linarith [d5_rowsSum_nonneg (A := AdoorL M) (G := s13GK K M) (Jb := 2) (Xd := Xd)
      (H1 := H1doorL M) hXd (H1door_two_L hM)]
  unfold m4MrowChiEnd a2Mrow_L_gk a2RowsSum_L_gk
  rw [← a2Level1_L_gk_eq K M]
  have hlvl' : 18 * (calH (H1doorL M) 1
        * Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) + 1)
      * ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
      * (4 * (calH (H1doorL M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
            * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1doorL M) 1)
          + 60 * (calH (H1doorL M) 1 / mrAlpha (1 / 12 : ℝ) 1)
              * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1doorL M) 1))
      ≤ 47520 * ((Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
          / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by
    calc 18 * (calH (H1doorL M) 1
            * Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) + 1)
          * ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
          * (4 * (calH (H1doorL M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
                * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1doorL M) 1)
              + 60 * (calH (H1doorL M) 1 / mrAlpha (1 / 12 : ℝ) 1)
                  * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1doorL M) 1))
        = 2 * (calH (H1doorL M) 1
              * Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) + 1) * 9
            * ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
            * (4 * (calH (H1doorL M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
                  * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1doorL M) 1)
                + 60 * (calH (H1doorL M) 1 / mrAlpha (1 / 12 : ℝ) 1)
                    * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1doorL M) 1)) := by ring
      _ ≤ 5280 * 9 * ((Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
            / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := hlvl
      _ = 47520 * ((Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
            / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by ring
  linarith

/-- **⟦THE D5 DELIVERABLE AT THE DOOR⟧ THE `a2Mrow_L`-GENRE ROW FAMILY,
STRICT/FUSED, AT THE G-LEVER** (`m4_hrowsSum_chi_door_end_L_gk`).  Frame:
`ThmA2.calFrameK_doorH1_at_gk`, whence `K ≤ 1.7·10⁸`. -/
theorem m4_hrowsSum_chi_door_end_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        -- ⟦THE STRICT RELATIVIZED PAIR LAW⟧ in place of the refuted global `hcoef`
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) j) (calQK (AdoorL M) (s13GK K M) M j)
            a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                    (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (AdoorL M) (s13GK K M))
                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ a2Mrow_L_gk K Ct Cp M Xd X ε := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_end
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hasupp hQXd
    hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  refine (hrows q c a bfam ha1 hb1 hc1 N Xd (AdoorL M) (s13GK K M) M 2 (H1doorL M) X h
    (1 / 12) ε t₁ (fun _ => 0) (calFrameK_doorH1_at_L_gk K M Xd hM hK hXdQ) hNXd hN4 hcoefWS
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd_le_a2Mrow_L_gk K hM hXd1 hCp.le

/-- **THE PER-BASE GATE BUNDLE OF THE DOOR ROW SUPPLIER, AT THE G-LEVER**
(`DoorRowEndBase_L_gk`).  Seven fields, names UNCHANGED: `Q2_le`, `coefWS`, `reg`, `big`,
`dom`, `h_four`, `Q1_le_h`.  `Q1_le_h` is LEVEL 1 and therefore K-INVARIANT in content
(`GLever.calQK_gk_one_eq`), but it is written at the levered symbol so the bundle reads
uniformly. -/
structure DoorRowEndBase_L_gk (K : ℕ) (M Xd j : ℕ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) : Prop where
  /-- The door's cutoff `Q₂ ≤ X_d`, which is also `CalFrameK`'s at the door family. -/
  Q2_le : calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd
  /-- ⟦THE REPAIR⟧ the STRICT relativized pair law, level by level. -/
  coefWS : ∀ i ∈ Finset.Icc 1 2,
    SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) i) (calQK (AdoorL M) (s13GK K M) M i)
      (winCutH Xd (doorCoeffU_L_gk K M)) (bU i) cU
  /-- (R1) `log Q₂ ≤ √(log X_d)`. -/
  reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- (R2) `100 ≤ √(log X_d)`. -/
  big : (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- (R4) the per-level error-domination product. -/
  dom : ∀ i ∈ Finset.Icc 1 2,
    ((Nat.sqrt Xd : ℝ) + 1)
        * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) i)
              (calQK (AdoorL M) (s13GK K M) M i), (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) i : ℕ) : ℝ)
          / Real.log ((calQK (AdoorL M) (s13GK K M) M i : ℕ) : ℝ))
  /-- The weighting frame's floor `4 ≤ 2^j` (`DoorFuseFrame_L.h_four`'s twin). -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- The weighting frame's `Q₁ ≤ h` at `h = 2^j`. -/
  Q1_le_h : ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)

/-- **⟦THE SLOT, MET⟧ AT THE G-LEVER** (`m4_hrowsSlot_at_door_end_L_gk`). -/
theorem m4_hrowsSlot_at_door_end_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowEndBase_L_gk K M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow_L_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_door_end_L_gk K hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  -- ⟦THE DOOR INSTANCE'S OWN FRAME⟧
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have ha1 : ∀ n : ℕ, ‖winCutH (A + s) (doorCoeffU_L_gk K M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  have hslot := hrows q cU (winCutH (A + s) (doorCoeffU_L_gk K M)) bU ha1 hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS (fun n hn => winCutH_asupp hn) hD.reg hD.big hD.dom
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L_gk] using hslot

/-- **⟦ITEM 11⟧ AT THE ASSEMBLY WIRE, AT THE LEVER** —
`m4_chiSummedFreeRow_of_doorAssembly_end_L` (:885). -/
theorem m4_chiSummedFreeRow_of_doorAssembly_end_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L_gk K M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowEndBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H j A s : ℕ, doorRowFloorL M ≤ j →
          arcDen 12 H * a2DoorGrade_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
              (M₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end_L_gk K hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband henv
  exact m4_chiSummedFreeRow_of_doorAssembly_L_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) hM hframe
    (hslot R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband henv
/-! ## §Xw — ⟦KWIDE-65⟧ THE WIDE-CEILING TWINS (this file)

Mechanical widening of the flat `hK : K ≤ 170000000` binders on the `L`-chain: the ceiling
moves INSIDE the internal `∀ M` as `K ≤ 170000000 * M`, so the raised lever `KlevF` can flow.
Statements and proofs are verbatim apart from that antecedent and the `_kwide` re-pointing.
The originals are untouched.
-/

/-- ⟦WIDE CEILING TWIN⟧ (`m4_wave_closed_coprime_discharged_L_gk_kwide`) —
`m4_wave_closed_coprime_discharged_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_wave_closed_coprime_discharged_L_gk_kwide (K : ℕ) (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M → K ≤ 170000000 * M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            -- ⟦ARM 1 DISCHARGED: the T₀-free per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0_L_gk K Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦the regime fact⟧ (subsumes the line above)
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦G1⟧ the trivial envelope dominates the arc denominator
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            -- ⟦G2⟧ the slack-`4` residue against the floor's own constant
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M) →
            -- ⟦ARM 2 DISCHARGED: the free-base row datum is the ONLY analytic carry left⟧
            M4ChiFreeRowMeanSq_L_gk K R M MS →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hbridge⟩ := doorRowCarried_of_t0free_L_gk K Qm
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_dyadicRow_carried_L_gk_kwide K
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_dyadicRow_L_gk K
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl Qm, Xsk, Kcf Qm, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl Qm, hXsk0, hKcf0 Qm, hCtail0,
    hK0, hX₀0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hKw hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcarT0 hgate harc harc8 hG1 hG2 hrowfree
  -- ⟦ARM 1⟧ the T₀-free register becomes the carried one, instance by instance
  have hcar : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
        ∀ s ≤ H,
          DoorRowCarried_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
            (doorLadder R.x H (i + 1) + s) j (MS j H) := by
    intro H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH
    haveI : NeZero q := ⟨by omega⟩
    have hqQm : q ≤ Qm := by
      have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hRq
    exact hbridge Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail q χ M
      (doorLadder R.x H (i + 1) + s) j (MS j H) hqQm
      (hcarT0 H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH)
  -- ⟦ARM 2⟧ the row datum → the narrowed coprime family → every class of `q`
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H)
      (fun H => 2 * MStr H) H := fun H =>
    m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
  have hcpN : M4CoprimeBlockMeanSqN_L_gk K R M
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_coprimeN_supplied_L_gk K (doorRowFloorL M) hMSan0 hMStr0 han hG1 hG2 harc8 hrowfree
  have hnc : M4ClassBlockMeanSq_L_gk K R M k
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_nonCoprime_classMeanSq_N_L_gk K (k := k) hM hBcl0 hgate harc hcpN
  refine hR δ Braw MS MSan MStr (doorRowFloorL M) M k hgates hMSan0 hMStr0 hBraw0 han htr
    hdrift hdel hrest (hrow R Qm M k MS hM hKw hQm htriv hcar) ?_
  intro H hlo hhi q hq hqQ i hik r hrq _hncop
  exact hnc H hlo hhi q hq hqQ i hik r hrq

/-- ⟦WIDE CEILING TWIN⟧ (`m4_wave_closed_coprime_discharged_False_L_gk_kwide`) —
`m4_wave_closed_coprime_discharged_False_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_wave_closed_coprime_discharged_False_L_gk_kwide (K : ℕ)
    (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M → K ≤ 170000000 * M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0_L_gk K Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloorL M) →
            M4ChiFreeRowMeanSq_L_gk K R M MS →
            logChowla2Fails R.eps R.x R.ω → False := by
  obtain ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩ := m4_wave_closed_coprime_discharged_L_gk_kwide K Qm
  exact ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩

/-- ⟦WIDE CEILING TWIN⟧ (`m4_door_meansq_carried_pool_L_gk_kwide`) —
`m4_door_meansq_carried_pool_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_door_meansq_carried_pool_L_gk_kwide (K : ℕ) :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (Qm q : ℕ) (χ : DirichletCharacter ℂ q), 0 < q → q ≤ Qm →
        ∀ (M Xd j : ℕ) (B : ℝ), 1 ≤ M → K ≤ 170000000 * M → doorRowFloorL M ≤ j →
          DoorRowCarriedPool_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M Xd j B →
            1 / ((Xd : ℕ) : ℝ)
                * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
                    ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                        * shortSum (doorChiCoeff_L_gk K χ M)
                            (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
              ≤ B := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hgen⟩ :=
    m4_meansq_per_chi_gen_pool_L_gk_kwide K
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  -- ⟦THE SKOLEM CUT⟧ the masked-floor constant, as a function of the modulus range
  choose Kcf hKcf0 hcfl using capFreeFloor3_pieceDatum
  obtain ⟨Ctail, hCtail0, htail⟩ := m4_door_tail_supply_L_gk K
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro Qm q χ hq hqQm M Xd j B hM hKw hj0 hcar
  obtain ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, C₁', M₀,
    cqS, cgS, cW, SW, Rbar0, Dmask, π₀,
    hXdX, hhj, hXee, hlX2, hhX, hhceil, hTann, hceil5, hT₀le, hTbot, hLXL, hLe, hL256,
    hXdQ, hP3, hlogP2, hQbot, hQlog, hQL, hPlow, hQhigh, hPQ, hQ0, hHX, hH2, hPj1, hQXd,
    hXdbig, hdom, hW5, hkth, hMtX, hC16, hRradW, hthinpin, hMtpin, hkkg, hMtY,
    hRrad0, hV1, hVδ, hlogV, hδsq, hksthr, hVJg, hCb0, hCbound, hXthr,
    hX₀k, hMfl0k, hk2, hkX, hgateW, hYpin, hWY, hXY, hthrY,
    hcqgate, hCqgate, hε0, habs,
    hQlogXd, hdomband, hlogb, hPQratio, h2688,
    hDmask0, hdebit, hcfthr,
    hc0, hce, hc1, hblk, hbox, hD1, hDk, hX₀j, hsqXa, hpin,
    hXae, hMXa, hXaX, hMfl0, hboxw, hS0, hSbd, hendGen, hRbdU, hRbar00, hRgrade,
    hend, hT0band, hcff, hpool, hgP1, hgRows, hgU, hgBand, henv⟩ := hcar
  subst hXdX
  subst hhj
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦the scale's arithmetic⟧
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hXee
  have h1ee : (1 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h1 := Real.add_one_le_exp (Real.exp 1)
    have h2 := Real.exp_pos 1
    linarith
  have hXd1 : 1 ≤ Xd := by
    have : (1 : ℝ) ≤ ((Xd : ℕ) : ℝ) := le_trans h1ee hXee
    exact_mod_cast this
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hlog1 : (1 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hLXe : Real.exp 1 ≤ Real.log ((Xd : ℕ) : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hP1 : 1 ≤ P := by omega
  have hP2 : 2 ≤ P := by omega
  -- ⟦THE LENGTH FLOOR IS FREE⟧: both `4 ≤ h` and the capstone's window gate
  have hj2 : 2 ≤ j := by
    have hA : 2 ^ 18 ≤ AdoorL M := AdoorL_ge_old hM
    have hAle : AdoorL M ≤ M * AdoorL M := Nat.le_mul_of_pos_left _ hM
    have hjf : M * AdoorL M ≤ j := hj0
    have h18 : (2 : ℕ) ≤ 2 ^ 18 := by norm_num
    omega
  have hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    have hN : (4 : ℕ) ≤ 2 ^ j := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    exact_mod_cast hN
  have hQ1h : ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) :=
    (door_length_gate_iff_L_gk K).mpr hj0
  -- ⟦THE DATUM SIDE (class (C)): the cut and its three S8 slots⟧
  have haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd →
      winCutH Xd (doorChiCoeff_L_gk K χ M) n = doorChiCoeff_L_gk K χ M n :=
    fun n h1 h2 => winCutH_of_mem _ h1 h2
  have ha0 : winCutH Xd (doorChiCoeff_L_gk K χ M) Xd = 0 := winCutH_supp0 _ le_rfl
  -- ⟦the pin chain and the per-block puncture law⟧
  have hcoefPin : SeamCoefW Xd P Q (winCutH Xd (doorChiCoeff_L_gk K χ M)) (doorChiCoeff_L_gk K χ M)
      (liouChi χ) :=
    doorChiCoeff_seamCoefW_at_door_H_L_gk K χ hM hlog1 hQXd hPlow haH ha0 hend
  have hcoefBand := doorChiCoeff_seamCoefW_punct_H_L_gk K χ hM haH ha0 hend
  -- ⟦the per-piece cap-free floor⟧
  have hfloor : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M)) ((Xd : ℕ) : ℝ) := by
    intro 𝒥 h𝒥
    exact hcfl Qm q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 𝒥
      ((Xd : ℕ) : ℝ) Dmask hqQm hXee hDmask0 (hdebit 𝒥 h𝒥) hcfthr
  -- ⟦THE SOCKET⟧ at `Ps := 1`, `J := 2`, read at the door datum
  have hsock0 := hsup q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M)
    (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q 2 1 Mt kk Dd Xa cqS L cgS Cb
    ((Xd : ℕ) : ℝ) theta293 (seamRad ((Xd : ℕ) : ℝ)) ((Xd : ℕ) : ℝ) 0 Rbar0 cW SW
    hc0 hce hc1 hCb0 hCbound hP1 le_rfl hRrad0 theta293_pos theta293_lt_one_div_32.le
    hLXe hPlow hQhigh hPQ hfloor hblk hbox hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0
    hboxw hS0 hSbd hendGen hRbdU
  have hsockR : CofactorSocket (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q
      ((Xd : ℕ) : ℝ) (seamRad ((Xd : ℕ) : ℝ)) 0 (4 * Rbar0) (doorChiCoeff_L_gk K χ M) := by
    have hs := cofactorSocket_doorChiCoeff_L_gk K χ hsock0
    have he : (2 : ℝ) ^ (2 : ℕ) * Rbar0 = 4 * Rbar0 := by ring
    rwa [he] at hs
  -- ⟦THE COPRIME TAIL⟧: `Mtail` and `EP2` are computed, not carried
  have hNcast : (((2 * Xd : ℕ)) : ℝ) = 2 * ((Xd : ℕ) : ℝ) := by push_cast; ring
  obtain ⟨hMtail, hMtail0, hEP2⟩ := htail q χ M P Q Xd (2 * Xd) ((Xd : ℕ) : ℝ) ε
    rfl hNcast hX0 hL256 hP2 hPQ hXd1 hQlogXd hdomband hPlow hlogb habs hPQratio h2688
  -- ⟦THE CAPSTONE, AT THE POOL⟧
  have hres := hgen Qm q χ hqQm (2 * Xd) Xd P Q M (winCutH Xd (doorChiCoeff_L_gk K χ M)) (liouChi χ)
    (doorChiCoeff_L_gk K χ M)
    (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 i
      (liouChi χ))
    ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) δ' V VJ L Cb (seamRad ((Xd : ℕ) : ℝ)) (4 * Rbar0)
    kmin Ymax ε _ _ C₁' M₀ π₀
    rfl rfl hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe hM hKw hXdQ hQ1h hP3
    hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkkg hMtY
    hRrad0 le_rfl le_rfl hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0k hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 habs hEP2 le_rfl
    (doorRow_ha1_L_gk K χ M Xd) (norm_liouChi_le_one χ)
    (fun n hn => doorRow_hsupp0_L_gk K χ M Xd n hn) (fun n hn => doorRow_hasupp_L_gk K χ M Xd n hn)
    hMtail0 hMtail
    (norm_doorChiCoeff_le_one_L_gk K χ M) (fun i n => norm_doorPunctCoeff_le_one_L_gk K χ M i n)
    (by positivity) hRgrade hsockR hcoefBand hcoefPin hT0band hcff hpool hgP1 hgRows hgU
    hgBand
  -- ⟦THE DATUM BRIDGE⟧ the cut is invisible to the row's short sum
  simp only [shortSum_winCutH_seamS0] at hres
  exact le_trans hres henv

/-- ⟦WIDE CEILING TWIN⟧ (`m4_dyadicRow_carried_pool_L_gk_kwide`) —
`m4_dyadicRow_carried_pool_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_dyadicRow_carried_pool_L_gk_kwide (K : ℕ) :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M → K ≤ 170000000 * M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
            ∀ s ≤ H,
              DoorRowCarriedPool_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
                (doorLadder R.x H (i + 1) + s) j (MS j H)) →
        M4ChiDyadicRowMeanSq_L_gk K R M k MS := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_door_meansq_carried_pool_L_gk_kwide K
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro R Qm M k MS hM hKw hQm htriv hcar H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hApos : 0 < doorLadder R.x H (i + 1) + s := by
    have := doorLadder_floor hxH (i + 1); omega
  by_cases hcase : doorRowFloorL M ≤ j
  · have hqQm : q ≤ Qm := by
      have hR : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hR
    exact hrow Qm q χ hq hqQm M (doorLadder R.x H (i + 1) + s) j (MS j H) hM hKw hcase
      (hcar H hlo hhi q hq hqQ i hik χ j hjL hcase s hsH)
  · exact le_trans (doorRow_trivial_grade_L_gk K χ M j hApos) (htriv j H (not_le.mp hcase))

/-- ⟦WIDE CEILING TWIN⟧ (`m4_door_meansq_carried_join_L_gk_kwide`) —
`m4_door_meansq_carried_join_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_door_meansq_carried_join_L_gk_kwide (K : ℕ) :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (Qm q : ℕ) (χ : DirichletCharacter ℂ q), 0 < q → q ≤ Qm →
        ∀ (M Xd j : ℕ) (B : ℝ), 1 ≤ M → K ≤ 170000000 * M → doorRowFloorL M ≤ j →
          DoorRowCarriedJoin_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M Xd j B →
            1 / ((Xd : ℕ) : ℝ)
                * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
                    ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                        * shortSum (doorChiCoeff_L_gk K χ M)
                            (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
              ≤ B := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hgen⟩ :=
    m4_meansq_per_chi_gen_join_L_gk_kwide K
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  -- ⟦THE SKOLEM CUT⟧ the masked-floor constant, as a function of the modulus range
  choose Kcf hKcf0 hcfl using capFreeFloor3_pieceDatum
  obtain ⟨Ctail, hCtail0, htail⟩ := m4_door_tail_supply_L_gk K
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro Qm q χ hq hqQm M Xd j B hM hKw hj0 hcar
  obtain ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, C₁', M₀,
    cqS, cgS, cW, SW, Rbar0, Dmask, π₀,
    hXdX, hhj, hXee, hlX2, hhX, hhceil, hTann, hceil5, hT₀le, hTbot, hLXL, hLe, hL256,
    hXdQ, hP3, hlogP2, hQbot, hQlog, hQL, hPlow, hQhigh, hPQ, hQ0, hHX, hH2, hPj1, hQXd,
    hXdbig, hdom, hW5, hkth, hMtX, hC16, hRradW, hthinpin, hMtpin, hkkg, hMtY,
    hRrad0, hV1, hVδ, hlogV, hδsq, hksthr, hVJg, hCb0, hCbound, hXthr,
    hX₀k, hMfl0k, hk2, hkX, hgateW, hYpin, hWY, hXY, hthrY,
    hcqgate, hCqgate, hε0, habs,
    hQlogXd, hdomband, hlogb, hPQratio, h2688,
    hDmask0, hdebit, hcfthr,
    hc0, hce, hc1, hblk, hbox, hD1, hDk, hX₀j, hsqXa, hpin,
    hXae, hMXa, hXaX, hMfl0, hboxw, hS0, hSbd, hendGen, hRbdU, hRbar00, hRgrade,
    hend, hT0band, hcff, hpool, hgP1, hgRows, hgU, hgBand, henv⟩ := hcar
  subst hXdX
  subst hhj
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦the scale's arithmetic⟧
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hXee
  have h1ee : (1 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h1 := Real.add_one_le_exp (Real.exp 1)
    have h2 := Real.exp_pos 1
    linarith
  have hXd1 : 1 ≤ Xd := by
    have : (1 : ℝ) ≤ ((Xd : ℕ) : ℝ) := le_trans h1ee hXee
    exact_mod_cast this
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hlog1 : (1 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hLXe : Real.exp 1 ≤ Real.log ((Xd : ℕ) : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hP1 : 1 ≤ P := by omega
  have hP2 : 2 ≤ P := by omega
  -- ⟦THE LENGTH FLOOR IS FREE⟧: both `4 ≤ h` and the capstone's window gate
  have hj2 : 2 ≤ j := by
    have hA : 2 ^ 18 ≤ AdoorL M := AdoorL_ge_old hM
    have hAle : AdoorL M ≤ M * AdoorL M := Nat.le_mul_of_pos_left _ hM
    have hjf : M * AdoorL M ≤ j := hj0
    have h18 : (2 : ℕ) ≤ 2 ^ 18 := by norm_num
    omega
  have hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    have hN : (4 : ℕ) ≤ 2 ^ j := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    exact_mod_cast hN
  have hQ1h : ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) :=
    (door_length_gate_iff_L_gk K).mpr hj0
  -- ⟦THE DATUM SIDE (class (C)): the cut and its three S8 slots⟧
  have haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd →
      winCutH Xd (doorChiCoeff_L_gk K χ M) n = doorChiCoeff_L_gk K χ M n :=
    fun n h1 h2 => winCutH_of_mem _ h1 h2
  have ha0 : winCutH Xd (doorChiCoeff_L_gk K χ M) Xd = 0 := winCutH_supp0 _ le_rfl
  -- ⟦the pin chain and the per-block puncture law⟧
  have hcoefPin : SeamCoefW Xd P Q (winCutH Xd (doorChiCoeff_L_gk K χ M)) (doorChiCoeff_L_gk K χ M)
      (liouChi χ) :=
    doorChiCoeff_seamCoefW_at_door_H_L_gk K χ hM hlog1 hQXd hPlow haH ha0 hend
  have hcoefBand := doorChiCoeff_seamCoefW_punct_H_L_gk K χ hM haH ha0 hend
  -- ⟦the per-piece cap-free floor⟧
  have hfloor : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M)) ((Xd : ℕ) : ℝ) := by
    intro 𝒥 h𝒥
    exact hcfl Qm q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 𝒥
      ((Xd : ℕ) : ℝ) Dmask hqQm hXee hDmask0 (hdebit 𝒥 h𝒥) hcfthr
  -- ⟦THE SOCKET⟧ at `Ps := 1`, `J := 2`, read at the door datum
  have hsock0 := hsup q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M)
    (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q 2 1 Mt kk Dd Xa cqS L cgS Cb
    ((Xd : ℕ) : ℝ) theta293 (seamRad ((Xd : ℕ) : ℝ)) ((Xd : ℕ) : ℝ) 0 Rbar0 cW SW
    hc0 hce hc1 hCb0 hCbound hP1 le_rfl hRrad0 theta293_pos theta293_lt_one_div_32.le
    hLXe hPlow hQhigh hPQ hfloor hblk hbox hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0
    hboxw hS0 hSbd hendGen hRbdU
  have hsockR : CofactorSocket (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q
      ((Xd : ℕ) : ℝ) (seamRad ((Xd : ℕ) : ℝ)) 0 (4 * Rbar0) (doorChiCoeff_L_gk K χ M) := by
    have hs := cofactorSocket_doorChiCoeff_L_gk K χ hsock0
    have he : (2 : ℝ) ^ (2 : ℕ) * Rbar0 = 4 * Rbar0 := by ring
    rwa [he] at hs
  -- ⟦THE COPRIME TAIL⟧: `Mtail` and `EP2` are computed, not carried
  have hNcast : (((2 * Xd : ℕ)) : ℝ) = 2 * ((Xd : ℕ) : ℝ) := by push_cast; ring
  obtain ⟨hMtail, hMtail0, hEP2⟩ := htail q χ M P Q Xd (2 * Xd) ((Xd : ℕ) : ℝ) ε
    rfl hNcast hX0 hL256 hP2 hPQ hXd1 hQlogXd hdomband hPlow hlogb habs hPQratio h2688
  -- ⟦THE CAPSTONE, AT THE POOL⟧
  have hres := hgen Qm q χ hqQm (2 * Xd) Xd P Q M (winCutH Xd (doorChiCoeff_L_gk K χ M)) (liouChi χ)
    (doorChiCoeff_L_gk K χ M)
    (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 i
      (liouChi χ))
    ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) δ' V VJ L Cb (seamRad ((Xd : ℕ) : ℝ)) (4 * Rbar0)
    kmin Ymax ε _ _ C₁' M₀ π₀
    rfl rfl hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe hM hKw hXdQ hQ1h hP3
    hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkkg hMtY
    hRrad0 le_rfl le_rfl hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0k hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 habs hEP2 le_rfl
    (doorRow_ha1_L_gk K χ M Xd) (norm_liouChi_le_one χ)
    (fun n hn => doorRow_hsupp0_L_gk K χ M Xd n hn) (fun n hn => doorRow_hasupp_L_gk K χ M Xd n hn)
    hMtail0 hMtail
    (norm_doorChiCoeff_le_one_L_gk K χ M) (fun i n => norm_doorPunctCoeff_le_one_L_gk K χ M i n)
    (by positivity) hRgrade hsockR hcoefBand hcoefPin hT0band hcff hpool hgP1 hgRows hgU
    hgBand
  -- ⟦THE DATUM BRIDGE⟧ the cut is invisible to the row's short sum
  simp only [shortSum_winCutH_seamS0] at hres
  exact le_trans hres henv

/-- ⟦WIDE CEILING TWIN⟧ (`m4_dyadicRow_carried_join_L_gk_kwide`) —
`m4_dyadicRow_carried_join_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_dyadicRow_carried_join_L_gk_kwide (K : ℕ) :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M → K ≤ 170000000 * M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
            ∀ s ≤ H,
              DoorRowCarriedJoin_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
                (doorLadder R.x H (i + 1) + s) j (MS j H)) →
        M4ChiDyadicRowMeanSq_L_gk K R M k MS := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_door_meansq_carried_join_L_gk_kwide K
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro R Qm M k MS hM hKw hQm htriv hcar H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hApos : 0 < doorLadder R.x H (i + 1) + s := by
    have := doorLadder_floor hxH (i + 1); omega
  by_cases hcase : doorRowFloorL M ≤ j
  · have hqQm : q ≤ Qm := by
      have hR : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hR
    exact hrow Qm q χ hq hqQm M (doorLadder R.x H (i + 1) + s) j (MS j H) hM hKw hcase
      (hcar H hlo hhi q hq hqQ i hik χ j hjL hcase s hsH)
  · exact le_trans (doorRow_trivial_grade_L_gk K χ M j hApos) (htriv j H (not_le.mp hcase))

/-- ⟦WIDE CEILING TWIN⟧ (`m4_rowDatum_dilated_L_gk_kwide`) —
`m4_rowDatum_dilated_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_rowDatum_dilated_L_gk_kwide (K : ℕ) :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ)
        (Kbox X₀w : ℕ → ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧ (∀ Qm : ℕ, 0 ≤ Kbox Qm) ∧
      (∀ Qm : ℕ, 0 < X₀w Qm) ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M → K ≤ 170000000 * M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
            doorRowFloorL M ≤ j → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H →
              ∀ s ≤ H / d + 1,
                DoorRowCarriedT0_L_gk K (Kbox Qm) (X₀w Qm) Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk
                    (Kcf Qm) Ctail χ M
                  (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H)) →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
            ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
              M4RowDatumAt_L_gk K M MS H H χ (doorLadder R.x H (i + 1)))
            ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ d : ℕ, 2 ≤ d →
                (d : ℝ) ≤ arcDen 12 H →
                  M4RowDatumAt_L_gk K M MS H (H / d + 1) χ
                    (doorLadder R.x H (i + 1) / d - 1)) := by
  -- ⟦THE SKOLEM CUT⟧ the `T₀`-bridge's two constants, as functions of the modulus range
  choose Kbox X₀w hK0 hX₀0 hbridge using doorRowCarried_of_t0free_L_gk K
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hmeansq⟩ :=
    m4_door_meansq_carried_L_gk_kwide K
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hK0, hX₀0, ?_⟩
  intro R Qm M k MS hM hKw hQm htriv harc hcarT0
  -- ⟦the carried form, at every dilated base⟧
  have hcar : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
        ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H → ∀ s ≤ H / d + 1,
          DoorRowCarried_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
            (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H) := by
    intro H hlo hhi q hq hqQ i hik χ j hjH hj0 d hd hdA s hsL
    haveI : NeZero q := ⟨by omega⟩
    have hqQm : q ≤ Qm := by
      have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hRq
    exact hbridge Qm Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail q χ M
      (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H) hqQm
      (hcarT0 H hlo hhi q hq hqQ i hik χ j hjH hj0 d hd hdA s hsL)
  -- ⟦the mean square at every dilated base and every dyadic length⟧
  have hms : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
        ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H → ∀ s ≤ H / d + 1,
          1 / ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)
              * (∫ y in ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)..(2
                    * ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)),
                  ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                      * shortSum (doorChiCoeff_L_gk K χ M)
                          (seamS0 (2 * (doorLadder R.x H (i + 1) / d - 1 + s))
                            ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)) y
                          ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
            ≤ MS j H := by
    intro H hlo hhi q hq hqQ i hik χ j hjH d hd hdA s hsL
    -- ⟦the dilated base is positive: `2d ≤ H < X_{i+1}` forces `⌊X_{i+1}/d⌋ ≥ 2`⟧
    have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
    have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
    have h2d : 2 * d ≤ H := by
      have hR : ((2 * d : ℕ) : ℝ) ≤ (H : ℝ) := by
        push_cast
        have := harc H hlo hhi
        linarith
      exact_mod_cast hR
    have hA2 : 2 ≤ doorLadder R.x H (i + 1) / d :=
      (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hXpos : 0 < doorLadder R.x H (i + 1) / d - 1 + s := by omega
    by_cases hcase : doorRowFloorL M ≤ j
    · have hqQm : q ≤ Qm := by
        have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
        exact_mod_cast hRq
      exact hmeansq Qm q χ hq hqQm M (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H) hM hKw
        hcase
        (hcar H hlo hhi q hq hqQ i hik χ j hjH hcase d hd hdA s hsL)
    · exact le_trans (doorRow_trivial_grade_L_gk K χ M j hXpos) (htriv j H (not_le.mp hcase))
  constructor
  · -- ⟦the ladder bases: the `d = 1` instance at the shift `s + 1`⟧
    intro H hlo hhi q hq hqQ i hik χ j hjL s hsL
    have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
    have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hd1 : ((1 : ℕ) : ℝ) ≤ arcDen 12 H := by push_cast; linarith
    have heq : doorLadder R.x H (i + 1) / 1 - 1 + (s + 1) = doorLadder R.x H (i + 1) + s := by
      rw [Nat.div_one]; omega
    have h := hms H hlo hhi q hq hqQ i hik χ j hjL 1 (by norm_num) hd1 (s + 1)
      (by rw [Nat.div_one]; omega)
    rwa [heq] at h
  · -- ⟦the dilated bases⟧
    intro H hlo hhi q hq hqQ i hik χ d hd2 hdA j hjL s hsL
    have hH2 : H / d + 1 ≤ H := by
      have h2d : 2 * d ≤ H := by
        have hR : ((2 * d : ℕ) : ℝ) ≤ (H : ℝ) := by
          push_cast
          have := harc H hlo hhi
          linarith
        exact_mod_cast hR
      have hstep : H / d ≤ H / 2 := Nat.div_le_div_left hd2 (by norm_num)
      omega
    exact hms H hlo hhi q hq hqQ i hik χ j (le_trans hjL (Nat.log_mono_right hH2)) d
      (by omega) hdA s hsL

/-- ⟦WIDE CEILING TWIN⟧ (`m4_hrowsSum_chi_door_end_L_gk_kwide`) —
`m4_hrowsSum_chi_door_end_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_hrowsSum_chi_door_end_L_gk_kwide (K : ℕ) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        -- ⟦THE STRICT RELATIVIZED PAIR LAW⟧ in place of the refuted global `hcoef`
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) j) (calQK (AdoorL M) (s13GK K M) M j)
            a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                    (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (AdoorL M) (s13GK K M))
                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ a2Mrow_L_gk K Ct Cp M Xd X ε := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_end
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd M X h ε t₁ hM hKw hXdQ hNXd hN4 hcoefWS hasupp hQXd
    hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  refine (hrows q c a bfam ha1 hb1 hc1 N Xd (AdoorL M) (s13GK K M) M 2 (H1doorL M) X h
    (1 / 12) ε t₁ (fun _ => 0) (calFrameK_doorH1_at_L_gk_kwide K M Xd hM hKw hXdQ) hNXd hN4 hcoefWS
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd_le_a2Mrow_L_gk K hM hXd1 hCp.le

/-- ⟦WIDE CEILING TWIN⟧ (`m4_hrowsSlot_at_door_end_L_gk_kwide`) —
`m4_hrowsSlot_at_door_end_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_hrowsSlot_at_door_end_L_gk_kwide (K : ℕ) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowEndBase_L_gk K M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow_L_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_door_end_L_gk_kwide K
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  -- ⟦THE DOOR INSTANCE'S OWN FRAME⟧
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have ha1 : ∀ n : ℕ, ‖winCutH (A + s) (doorCoeffU_L_gk K M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  have hslot := hrows q cU (winCutH (A + s) (doorCoeffU_L_gk K M)) bU ha1 hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hKw hD.Q2_le le_rfl hN4 hD.coefWS (fun n hn => winCutH_asupp hn) hD.reg hD.big hD.dom
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L_gk] using hslot

/-- ⟦WIDE CEILING TWIN⟧ (`m4_chiSummedFreeRow_of_doorAssembly_end_L_gk_kwide`) —
`m4_chiSummedFreeRow_of_doorAssembly_end_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_end_L_gk_kwide (K : ℕ) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L_gk K M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowEndBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H j A s : ℕ, doorRowFloorL M ≤ j →
          arcDen 12 H * a2DoorGrade_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
              (M₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end_L_gk_kwide K
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε RSbig cU bU t₁ hM hKw hb1 hc1 hframe hbase hcap hband henv
  exact m4_chiSummedFreeRow_of_doorAssembly_L_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) hM hframe
    (hslot R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap) hband henv

end Salt.MR

end
