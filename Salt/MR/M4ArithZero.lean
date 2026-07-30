/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4RowsChiZero
import Salt.MR.M4SocketDischarge

/-!
# ⟦THE SIEVE-VANISHING TWIN CHAIN — THE ARITHMETIC PAGE⟧ (`M4ArithZero`)

`M4RowsChiZero` carried the Lemma-12 row up to ⟦item 11⟧ with the density constant `C_p`
a FREE nonnegative real.  This file spends that freedom: it re-runs the terminal fuse
(`M4ArithPage`'s gated arithmetic exit and `M4SocketDischarge`'s composite) at `C_p` free,
and then PRICES the residual gate that survives at `C_p := 0`.

## ⟦THE RESIDUAL, AND WHY IT IS A DIFFERENT ANIMAL⟧

`M4Assembly.DoorFuseFrame`'s second grading gate is

```
      gRows :  5760 · (a2RowsSum M X_d  +  C_p · (2/M))  ≤  (log X_d)^{−1/500} .
```

The ⟦SECOND HORN⟧ refutation rides the SECOND summand: at `C_p > 0` it caps
`loglog X_d ≤ 500·(log M − log(11520 C_p))`, the socket caps `log M ≤ loglog H − 24.6`, and
the arm floors `loglog X_d ≥ 7000·loglog H` — jointly unsatisfiable, `C_p`-independently.

At `C_p := 0` that summand is gone and only `5760·a2RowsSum M X_d` remains.  §4 computes it
EXACTLY (`a2RowsSum_door_decomp`):

```
      a2RowsSum M X_d = (5/2)·e²·a2Level1 M
                        + (2e + 2)/X_d
                        + 16·log₂(2X_d)·(1/P₁ + 1/P₂) ,
```

the identity `1/H1door M = a2Level1 M` (`DoorFrameH1`'s G6 certificate read as a quotient)
turning the two window rows `2e²/H_j`, `j = 1, 2`, into `(5/2)e²·a2Level1 M`.  Every summand
is of the ALREADY-PRICED summand-2 genre — `a2Level1 M = (log Q₁)^{1/3}/P₁^{1/12}` decays like
`2^{−Adoor M/12}` — so `GRowsZeroGate` asks only

```
      loglog X_d/500 + loglog Q₁/3 + 14   ≤  (log 2/12)·Adoor M          (level 1)
      loglog X_d/500 + 13                 ≤  log X_d                     (the endpoint)
      loglog X_d·(1 + 1/500) + 15         ≤  (log 2)·Adoor M             (the p² rows)
```

against the arm's floor `loglog X_d ≥ 7000·loglog H + 1.25·10⁵`.  Written in the refuter's own
variables (`λ = loglog H`, `μ = loglog X_d`) the binding one is the first, i.e.

```
      λ  ≤  0.0578 · Adoor M / (14 + 1/3)     (up to the additive constants),
```

⟦THE MARGIN, ARITHMETICALLY, AT THE ANCHOR'S FLOOR⟧  `Adoor M = 2^36·(log₂M + 1)` and ⟦C1⟧'s
anchor `log₂M + 1 ≥ 2484` give `Adoor M ≥ 1.707·10^14`, hence
`(log 2/12)·Adoor M ≥ 9.86·10^12`.  Writing the arm as `μ ≥ 7000λ + 1.25·10⁵` and
`loglog Q₁ ≤ λ + log(Adoor M) ≈ λ + 32.8`, the level-1 field is met whenever

```
      7166.7·λ + 1.375·10⁵ + 36K   ≤   28.88 · Adoor M ,
```

i.e. up to `λ ≈ 6.9·10^11` — against `M4ArithPage.m4_arith_anchor_of_C1`'s own register cap
`λ ≤ 10^11`, a factor of `≈ 6.9`.  It is not tight at the floor and it does not have to be:
`Adoor M` grows with `log₂M`, and at the register top `λ = 10^11` the field needs only
`log₂M + 1 ≥ 361`, eight orders under the socket's own ceiling `log M ≤ λ − 24.6`.

Crucially the demand is on `Adoor M`, which the anchor makes LARGE, not on `M` against `λ`,
which the socket makes small: the exponent-1-versus-exponent-14 collision of the
⟦SECOND HORN⟧ does not arise at all.

⟦WHAT IS AND IS NOT CLAIMED⟧  `GRowsZeroGate` is DISCHARGED here into `gRows` at `C_p = 0`
(`gRows_zero_of_gate`) — that is a theorem.  Whether the register's own `(M, X_d, H)` meets
`GRowsZeroGate` is the consumer's arithmetic, in the open, exactly as `DoorArithFrame`'s five
fields are; nothing here asserts it.  What IS established is that the gate is now of the
`Adoor M`-genre and no longer of the refuted `M`-versus-`λ` genre.

## Contents

* §1 ⟦item 11⟧ at the gated arithmetic, `C_p` free
  (`m4_chiSummedFreeRow_of_doorArith_zero`);
* §2 the socket composite (`m4_socket_discharged_conditional_zero`) and its band-free form
  (`m4_socket_discharged_bandfree_zero`);
* §3 the door scales the pricing reads;
* §4 the residual: the exact decomposition, the slot workhorse, and `gRows_zero_of_gate`.

⟦PURELY ADDITIVE⟧  No landed declaration is touched.  `M4ArithPage.m4_arith_henv`,
`M4Assembly.m4_chiSummedFreeRowBig_of_doorGradeGated`, `m4_arith_gate4`,
`m4_arith_rs_ceiling_met` and `M4SocketDischarge.m4_hband_at_door_slot` are REUSED verbatim.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — ⟦ITEM 11⟧ AT THE GATED ARITHMETIC, `C_p` FREE

`M4SocketDischarge.m4_chiSummedFreeRow_of_doorArith_end`'s twin.  The only differences are
the density constant's quantifier and the `dom`-free base bundle. -/

/-- **⟦ITEM 11 AT THE DOOR'S ENVELOPE, `hrows`-FREE, DENSITY-FREE⟧**
(`m4_chiSummedFreeRow_of_doorArith_zero`).  `M4ChiSummed.M4ChiSummedFreeRow` at the spliced
grade `m4ChiRowGraded M (fun _ H => RSanDoor H)` from `hM`, `hb1`, `hc1`, `hframe`, `hbase`,
`hcap`, `hband`, `harith`, with the density constant `Cp` universally quantified over the
nonnegatives — in particular available at `Cp := 0`. -/
theorem m4_chiSummedFreeRow_of_doorArith_zero :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K : ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoor H)) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε cU bU t₁ K hM hb1 hc1 hframe hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_big
    (m4_chiSummedFreeRowBig_of_doorGradeGated (C₁ := C₁) (M₀ := M₀) ?_ (m4_arith_henv harith))
  intro H L q j A s hb
  obtain ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  haveI : NeZero q := ⟨hq.ne'⟩
  have hbb : SocketBase R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hbb
  exact m4_chiFreeRowSq_sum_at_door hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hbb)
    (hband H L q j A s hbb) hF.gP1 hF.gRows ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-! ## §2 — THE SOCKET COMPOSITE, `C_p` FREE

`M4SocketDischarge` §3/§4 at §1.  `m4_arith_gate4` and `m4_arith_rs_ceiling_met` are
character-blind and density-blind, so they ride unchanged. -/

/-- **⟦THE SOCKET, DISCHARGED, DENSITY-FREE⟧** (`m4_socket_discharged_conditional_zero`).
`M4SocketDischarge.m4_socket_discharged_conditional`'s twin: `m4_second_road`'s three demands
(⟦item 11⟧, ⟦gate 4⟧, the ceiling) at one hypothesis set, with `Cp` free and `hbase` the
six-field `DoorRowZeroBase`. -/
theorem m4_socket_discharged_conditional_zero :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
        1 ≤ M → 2 / 10 ^ 49 ≤ δ₀ →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
        (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoor H))
          ∧ (∀ j H : ℕ, doorRowFloor M ≤ j →
              m4ChiRowGraded M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
          ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hitem11⟩ := m4_chiSummedFreeRow_of_doorArith_zero
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε cU bU t₁ K δ₀ hM hδ₀ hHreg hb1 hc1 hframe hbase hcap hband harith
  refine ⟨hitem11 Cp hCp R M C₁ M₀ ε cU bU t₁ K hM hb1 hc1 hframe hbase hcap hband harith,
    m4_arith_gate4 M, ?_⟩
  intro H hlo hhi
  obtain ⟨hL0, hlam⟩ := hHreg H hlo hhi
  exact m4_arith_rs_ceiling_met hδ₀ hL0 hlam

/-- **⟦THE SOCKET, DISCHARGED, `T₀`-BAND INCLUDED, DENSITY-FREE⟧**
(`m4_socket_discharged_bandfree_zero`).  §2 with `hband` supplied by
`M4SocketDischarge.m4_hband_at_door_slot`. -/
theorem m4_socket_discharged_bandfree_zero (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
            2 / 10 ^ 49 ≤ δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorRowZeroBase M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                            (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
            M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoor H))
              ∧ (∀ j H : ℕ, doorRowFloor M ≤ j →
                  m4ChiRowGraded M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hcomp⟩ := m4_socket_discharged_conditional_zero
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ := m4_hband_at_door_slot hMmu Aexp hAexp R M hM C₁ M₀
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact hcomp Cp hCp R M C₁ M₀ ε cU bU t₁ K δ₀ hM hδ₀ hHreg hb1 hc1 hframe hbase hcap
    (hbandslot hbandbase) harith

/-! ## §3 — THE DOOR SCALES THE PRICING READS

Three facts about the door's level-1 ladder, all definitional once `calE_one` is unfolded. -/

/-- `log P₁ = Adoor M · log 2` — the door's level-1 prime cut is `2^{Adoor M}` on the nose
(`SeamCalibration.calE_one`). -/
lemma log_calP_door_one (M : ℕ) :
    Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) = (Adoor M : ℝ) * Real.log 2 := by
  rw [calP, calE_one]
  push_cast
  rw [Real.log_pow]

/-- `P₁ ≤ P₂` at the door family (`e₂ = 4·A·G ≥ A = e₁`). -/
lemma calP_door_one_le_two {M : ℕ} (hM : 1 ≤ M) :
    calP (Adoor M) (3072 * M) 1 ≤ calP (Adoor M) (3072 * M) 2 := by
  refine Nat.pow_le_pow_right (by norm_num) ?_
  rw [calE_one, calE]
  have h1 : 1 ≤ (3072 * M) ^ (2 - 1) := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (Nat.factorial 2) ^ 2 := Nat.one_le_pow _ _ (Nat.factorial_pos 2)
  calc Adoor M = Adoor M * 1 * 1 := by ring
    _ ≤ Adoor M * (3072 * M) ^ (2 - 1) * (Nat.factorial 2) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

/-- `1/H1door M = a2Level1 M` — the G6 certificate read as a quotient
(`DoorFrameH1.H1door`, `ThmA2.a2Level1`). -/
lemma one_div_H1door_eq_a2Level1 (M : ℕ) : 1 / H1door M = a2Level1 M := by
  rw [H1door, a2Level1, one_div_div]

/-! ## §4 — THE RESIDUAL AT `C_p = 0`, PRICED

The exact decomposition, one workhorse, and the gate. -/

/-- **⟦THE EXACT DECOMPOSITION⟧** (`a2RowsSum_door_decomp`).  `ThmA2.a2RowsSum` at the door
family, summed:

  `a2RowsSum M X_d = (5/2)·e²·a2Level1 M + (2e + 2)/X_d + 16·log₂(2X_d)·(1/P₁ + 1/P₂)` .

The two window rows contribute `2e²/H_1 + 2e²/H_2 = 2e²(1 + 1/4)/H1door M`, and
`1/H1door M = a2Level1 M`; the `e/X_d` residue of each window row and the two `1/X_d` terms
make up `(2e + 2)/X_d`.  This is the identity behind the design's "`2.5e²·a2Level1 M`". -/
private lemma window_row_eq {Xd H : ℝ} (hXd : 0 < Xd) (hH : 0 < H) :
    Xd * ((2 * Real.exp 1 * Xd / H + 1) * (Real.exp 1 / Xd ^ 2))
      = 2 * Real.exp 1 ^ 2 / H + Real.exp 1 / Xd := by
  field_simp

theorem a2RowsSum_door_decomp {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) :
    a2RowsSum M Xd
      = 5 / 2 * Real.exp 1 ^ 2 * a2Level1 M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 16 * Real.logb 2 (2 * (Xd : ℝ))
            * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ)) := by
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hH2 : (2 : ℝ) ≤ H1door M := H1door_two hM
  have hH0 : (0 : ℝ) < H1door M := by linarith
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [a2RowsSum, hIcc, Finset.sum_insert (by decide), Finset.sum_singleton,
    show calH (H1door M) 1 = H1door M by rw [calH]; norm_num,
    show calH (H1door M) 2 = 4 * H1door M by rw [calH]; norm_num,
    window_row_eq hXd0 hH0, window_row_eq hXd0 (by linarith : (0 : ℝ) < 4 * H1door M),
    ← one_div_H1door_eq_a2Level1]
  ring

/-- **⟦THE SLOT WORKHORSE⟧** (`slot_of_log_gate`).  A bound of the shape
`v ≤ κ·(log X_d)^{−1/500}` is EXACTLY a linear inequality between `log v`, `log κ` and
`loglog X_d`.  Every summand of §4's decomposition is priced through this one lemma. -/
private lemma slot_of_log_gate {v κ L : ℝ} (hv : 0 < v) (hκ : 0 < κ) (hL : 0 < L)
    (h : Real.log v + Real.log L / 500 ≤ Real.log κ) :
    v ≤ κ * L ^ (-(1 : ℝ) / 500) := by
  have hrw : κ * L ^ (-(1 : ℝ) / 500) = Real.exp (Real.log κ - Real.log L / 500) := by
    rw [Real.rpow_def_of_pos hL]
    conv_lhs => rw [← Real.exp_log hκ]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hrw]
  conv_lhs => rw [← Real.exp_log hv]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **⟦THE ZERO-DENSITY `gRows` GATE⟧** (`GRowsZeroGate`) — what
`M4Assembly.DoorFuseFrame.gRows` asks once the density summand is `0`, in its LOG form.  Four
fields, all in the refuter's own variables (`μ = loglog X_d`, `Adoor M = 2^36·(log₂M + 1)`):

* `base` — `1 ≤ log X_d` (the base is above `e`; `DoorFuseFrame.X_exp` already gives it);
* `level1` — `μ/500 + loglog Q₁/3 + 14 ≤ (log 2/12)·Adoor M`.  **This is the binding one**:
  `a2Level1 M = (log Q₁)^{1/3}/P₁^{1/12}` and `P₁ = 2^{Adoor M}`, so the level-1 rows decay
  like `2^{−Adoor M/12}` while the target decays like `e^{−μ/500}`.  Under the arm
  (`μ ≥ 7000λ + 1.25·10⁵`) it reads `λ ≲ 0.0578·Adoor M/(14 + 1/3)`;
* `endpt` — `μ/500 + 13 ≤ log X_d`, the `(2e + 2)/X_d` residue (a `1/X_d` against a
  `(log X_d)^{−1/500}`: slack of an exponential);
* `p2` — `μ(1 + 1/500) + 15 ≤ (log 2)·Adoor M`, the two `p²` rows `16·log₂(2X_d)/P_j`.

⟦WHAT CHANGED AGAINST THE REFUTED GATE⟧  the demand is on `Adoor M`, which ⟦C1⟧'s anchor
`log₂M + 1 ≥ 2484` makes `≥ 1.707·10^14`; the refuted `C_p·(2/M)` summand demanded
`μ ≤ 500·(log M − log(11520 C_p))` — a demand on `log M`, which the socket's own
`doorRowFloor M ≤ j ≤ log₂ L` caps at `λ − 24.6`.  Nothing here reads `log M` at all. -/
structure GRowsZeroGate (M Xd : ℕ) : Prop where
  /-- `1 ≤ log X_d`. -/
  base : 1 ≤ Real.log (Xd : ℝ)
  /-- ⟦THE LEVEL-1 SLOT⟧ `μ/500 + loglog Q₁/3 + 14 ≤ (log 2/12)·Adoor M`. -/
  level1 : Real.log (Real.log (Xd : ℝ)) / 500
      + Real.log (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) / 3 + 14
    ≤ Real.log 2 / 12 * (Adoor M : ℝ)
  /-- ⟦THE ENDPOINT SLOT⟧ `μ/500 + 13 ≤ log X_d`. -/
  endpt : Real.log (Real.log (Xd : ℝ)) / 500 + 13 ≤ Real.log (Xd : ℝ)
  /-- ⟦THE `p²` SLOT⟧ `μ·(1 + 1/500) + 15 ≤ (log 2)·Adoor M`. -/
  p2 : Real.log (Real.log (Xd : ℝ)) * (1 + 1 / 500) + 15 ≤ Real.log 2 * (Adoor M : ℝ)

/-- Three numerals the pricing spends, all from `log 2 < 0.6931471808`. -/
private lemma pricing_numerals :
    Real.log 14400 ≤ 14 * Real.log 2 ∧ Real.log 3 ≤ 2 * Real.log 2 ∧
      Real.log 43200 ≤ 16 * Real.log 2 ∧ Real.log 460800 ≤ 19 * Real.log 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 14400)
      (by norm_num : (14400 : ℝ) ≤ 2 ^ (14 : ℕ))
    rw [Real.log_pow] at h; push_cast at h; linarith
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (3 : ℝ) ≤ 2 ^ (2 : ℕ))
    rw [Real.log_pow] at h; push_cast at h; linarith
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 43200)
      (by norm_num : (43200 : ℝ) ≤ 2 ^ (16 : ℕ))
    rw [Real.log_pow] at h; push_cast at h; linarith
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 460800)
      (by norm_num : (460800 : ℝ) ≤ 2 ^ (19 : ℕ))
    rw [Real.log_pow] at h; push_cast at h; linarith

/-- **⟦THE RESIDUAL, PRICED⟧** (`gRows_zero_of_gate`).  At `C_p = 0` the frame's second
grading gate follows from `GRowsZeroGate` alone:

  `5760·(a2RowsSum M X_d + 0·(2/M)) ≤ (log X_d)^{−1/500}` .

The three slots are `1/3` of the budget each, priced through `slot_of_log_gate`. -/
theorem gRows_zero_of_gate {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hg : GRowsZeroGate M Xd) :
    5760 * (a2RowsSum M Xd + (0 : ℝ) * (2 / (M : ℝ)))
      ≤ (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
  obtain ⟨h14400, h3, h43200, h460800⟩ := pricing_numerals
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlt2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hLX : (1 : ℝ) ≤ Real.log (Xd : ℝ) := hg.base
  have hLX0 : (0 : ℝ) < Real.log (Xd : ℝ) := by linarith
  have hQ1 : (1 : ℝ) ≤ Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) :=
    one_le_log_calQK_door_one hM
  have hQ10 : (0 : ℝ) < Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := by linarith
  have hP1 : (64 : ℝ) ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := calP_door_one_ge M
  have hP10 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hP12 : ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
      ≤ ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ) := by
    exact_mod_cast calP_door_one_le_two hM
  have hP20 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ) := by linarith
  have hlogP1 := log_calP_door_one M
  have hlog3 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  -- ⟦SLOT 1 — the level-1 rows⟧
  have hq3 : (0 : ℝ)
      < (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hQ10 _
  have hp12 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
    Real.rpow_pos_of_pos hP10 _
  have ha2pos : (0 : ℝ) < a2Level1 M := by rw [a2Level1]; exact div_pos hq3 hp12
  have hepos : (0 : ℝ) < Real.exp 1 ^ 2 := pow_pos (Real.exp_pos 1) 2
  have hlvl0 : (0 : ℝ) < 14400 * Real.exp 1 ^ 2 * a2Level1 M :=
    mul_pos (mul_pos (by norm_num) hepos) ha2pos
  have hlvllog : Real.log (14400 * Real.exp 1 ^ 2 * a2Level1 M)
      = Real.log 14400 + 2
          + (1 : ℝ) / 3 * Real.log (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ))
          - (1 : ℝ) / 12 * ((Adoor M : ℝ) * Real.log 2) := by
    rw [Real.log_mul (by positivity) ha2pos.ne', Real.log_mul (by norm_num) hepos.ne',
      a2Level1, Real.log_div hq3.ne' hp12.ne', Real.log_rpow hQ10, Real.log_rpow hP10,
      Real.log_pow, Real.log_exp, hlogP1]
    push_cast
    ring
  have hslot1 : 14400 * Real.exp 1 ^ 2 * a2Level1 M
      ≤ 1 / 3 * (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
    refine slot_of_log_gate hlvl0 (by norm_num) hLX0 ?_
    rw [hlvllog, hlog3]
    have := hg.level1
    linarith
  -- ⟦SLOT 2 — the endpoint residue⟧
  have hendle : 5760 * (2 * Real.exp 1 + 2) / (Xd : ℝ) ≤ 43200 / (Xd : ℝ) := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hinv : (0 : ℝ) ≤ 1 / (Xd : ℝ) := (div_pos one_pos hXd0).le
    have hnum : 5760 * (2 * Real.exp 1 + 2) ≤ 43200 := by linarith
    calc 5760 * (2 * Real.exp 1 + 2) / (Xd : ℝ)
        = 5760 * (2 * Real.exp 1 + 2) * (1 / (Xd : ℝ)) := by ring
      _ ≤ 43200 * (1 / (Xd : ℝ)) := mul_le_mul_of_nonneg_right hnum hinv
      _ = 43200 / (Xd : ℝ) := by ring
  have hslot2 : 5760 * (2 * Real.exp 1 + 2) / (Xd : ℝ)
      ≤ 1 / 3 * (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
    refine hendle.trans (slot_of_log_gate (div_pos (by norm_num) hXd0)
      (by norm_num) hLX0 ?_)
    rw [Real.log_div (by norm_num) hXd0.ne', hlog3]
    have := hg.endpt
    linarith
  -- ⟦SLOT 3 — the two `p²` rows⟧
  have hlogb : Real.logb 2 (2 * (Xd : ℝ)) ≤ 5 / 2 * Real.log (Xd : ℝ) := by
    rw [Real.logb, Real.log_mul (by norm_num) hXd0.ne', div_le_iff₀ hl2]
    nlinarith
  have hinv2 : 1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
      + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ)
      ≤ 2 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    have h : 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ)
        ≤ 1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le hP10 hP12
    have h2 : 2 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
        = 1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
          + 1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by ring
    linarith
  have hp2le : 92160 * Real.logb 2 (2 * (Xd : ℝ))
        * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
          + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ))
      ≤ 460800 * Real.log (Xd : ℝ) / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    have hA : (0 : ℝ) ≤ 1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
        + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ) :=
      add_nonneg (div_pos one_pos hP10).le (div_pos one_pos hP20).le
    have hB : (0 : ℝ) ≤ 92160 * (5 / 2 * Real.log (Xd : ℝ)) := by linarith
    have h2 : 92160 * Real.logb 2 (2 * (Xd : ℝ)) ≤ 92160 * (5 / 2 * Real.log (Xd : ℝ)) := by
      linarith
    refine (mul_le_mul h2 hinv2 hA hB).trans (le_of_eq ?_)
    rw [div_eq_mul_one_div, div_eq_mul_one_div]
    ring
  have hslot3 : 92160 * Real.logb 2 (2 * (Xd : ℝ))
        * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
          + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ))
      ≤ 1 / 3 * (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
    refine hp2le.trans (slot_of_log_gate
      (div_pos (mul_pos (by norm_num) hLX0) hP10) (by norm_num) hLX0 ?_)
    rw [Real.log_div (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 460800) hLX0)) hP10.ne',
      Real.log_mul (by norm_num) hLX0.ne', hlogP1, hlog3]
    have := hg.p2
    linarith
  -- ⟦THE THREE SLOTS, SUMMED⟧
  rw [a2RowsSum_door_decomp hM hXd]
  have hsum : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1 M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 16 * Real.logb 2 (2 * (Xd : ℝ))
            * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ))
        + (0 : ℝ) * (2 / (M : ℝ)))
      = 14400 * Real.exp 1 ^ 2 * a2Level1 M
        + 5760 * (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 92160 * Real.logb 2 (2 * (Xd : ℝ))
            * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ)) := by ring
  rw [hsum]
  linarith

end Salt.MR
