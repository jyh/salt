/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.V7A
import Salt.MR.V7E

/-!
# `V7Ks` — ⟦DREAM-SPACE⟧ the `Ks` rethread: `logChowla2_ineffective_v7_ksarm`

⟦DREAM-SPACE, night 08/14 — branch artifact; consumes nothing until waking review⟧

`V7E.logChowla2_ineffective_v7` carries THREE inner riders (`e^{-100} ≤ Ks`,
`XCeilRiderStrict ε g`, the `K_vt` cushion).  This file proposes the terminal with the `Ks`
floor rider of those three discharged, leaving **two**.

## The mechanism

V7-A traced the `Ks` rider to its leaf: `e^{-100} ≤ Ks` reduces to an explicit NUMERICAL lower
bound on Siegel's ineffective constant at `ε = 1/16`, which neither the corpus nor the
literature supplies — so the rider is NOT provable AS STATED.  V7-A also supplied the leaf that
replaces it: `capfloor_floor4_of_pos` derives the `floor4` field of `S13CapGatePerBlock` from
`0 < Ks` plus the WINDOW `log(1/Ks) ≤ 3·log H/16`, with no numeral anywhere.

The numeral does not mention `A`, so enlarging `A` cannot establish it; the window, by contrast,
is `A`-satisfiable.  That is the whole difference: the terminal
mints `Ks` before it chooses its design constant `A`, so `A` may be chosen above `16·log(1/Ks)/3`
— exactly the move V7-C landed for `T₀` (a new arm of `A`'s own `max`), except that here the arm
must be met at the LEAF, so the window has to be threaded down to `capfloor_floor4`.

⟦THE THREAD — four hops, not nine⟧ on the live path the rider is carried by exactly four
declarations between `capfloor_floor4` and the terminal, and this file re-states each with the
window in place of the numeral:

```
capfloor_floor4                    (S13CapFloor:449)   -> capfloor_floor4_of_pos      (V7A:216)
s13CapFloor_all_L_gk_sharpT0       (S16ComposeV4:670)  -> §2  _kswin
s16_capGate_supply_L_gk_sharpT0    (S16ComposeV4:714)  -> §3  _kswin
s15_crossing_..._khoist_csfree     (V7B:1676)          -> §4  _kswin
logChowla2_witnessed_..._csfree    (V7B:1721)          -> §5  _kswin
logChowla2_ineffective_v7          (V7E:74)            -> §6  _ksarm
```

The carried form is `log(1/Ks) ≤ 3·log R.Hlo/16` at the three regime-scoped hops (§2–§4) and
`log(1/Ks) ≤ 3·e^{3.2A}/16` at the `A`-scoped hop (§5), the two joined by the flat witness
floor's own `e^{3.2A} ≤ log R.Hlo` (`flatWitFloor_log_ge`, already a `have` in the landed body).
At §6 the arm is discharged from `A ≥ 16·log(1/Ks)/3` against `3.2A + 1 ≤ e^{3.2A}`.

⟦NO STRENGTH IS TRADED⟧ `A` now depends on `Ks`, but `A` was already an unpinned constant whose
only exported properties are `162 ≤ A` and `A₀ ≤ A` for the CALLER's `A₀` — so the `∃`-prefix
promises exactly what `v7`'s did.  `capfloor_floor4_of_sharp` (V7A:202) is the receipt that the
windowed leaf subsumes the landed one: nothing downstream weakens.

**PURELY ADDITIVE.**  `logChowla2_ineffective_v7`, `logChowla2_ineffective_v6`, `…_v6_csarm`,
`…_v6_T0arm` and every hop copied from are byte-untouched and remain citable.  A2's name is
unchanged: the limit is still `ineffective` — the `K_vt` cushion is the Siegel-genre core
and this file does not touch it.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla
open scoped BigOperators

/-! ## §1 — ⟦THE LEAF, REGIME-SCOPED⟧ `floor4` from the window at `R.Hlo` -/

/-- **⟦`floor4` AT THE REGIME FLOOR⟧** `V7A.capfloor_floor4_of_pos` with the window moved off
the socket's own `H` and onto the regime's bottom `R.Hlo` — the form the hops can carry, since
`R` is in scope at every one of them and `H` is not.  The step is `R.Hlo ≤ H` (the socket base's
first field) and `log` monotone. -/
theorem capfloor_floor4_of_regimeWin {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hKs0 : 0 < Ks)
    (hwin : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16) :
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hHloR : (4000000 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast R.hHlo_floor
  have hloR : ((R.Hlo : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo
  have hmono : Real.log ((R.Hlo : ℕ) : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hloR
  exact capfloor_floor4_of_pos hfl hb hAN hTlo hKs0 (by linarith)

/-! ## §2 — ⟦HOP 7⟧ the floor wave, windowed

`S16ComposeV4.s13CapFloor_all_L_gk_sharpT0` (:670) with `hKs : e^{-100} ≤ Ks` replaced by
`0 < Ks` + the regime window.  The only proof edit is the `floor4` entry. -/

/-- ⟦`Ks`-WINDOWED TWIN⟧ (`s13CapFloor_all_L_gk_sharpT0_kswin`) —
`S16ComposeV4.s13CapFloor_all_L_gk_sharpT0` with the `Ks` numeral rider replaced by positivity
plus the regime window.  Body verbatim apart from the `floor4` entry. -/
theorem s13CapFloor_all_L_gk_sharpT0_kswin (K : ℕ) {R : ChowlaRegime} {M H L q j As s Nd : ℕ}
    {T₀ Kq Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j As s) (hM : 1 ≤ M)
    (hAN : As ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)))
    (hT₀ : T₀ ≤ Real.exp (Real.sqrt ((R.Hlo : ℕ) : ℝ) / 2)) (hKq : Kq ≤ Real.exp 100)
    (hKs0 : 0 < Ks)
    (hKsw : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16) :
    ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann ∧
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ∧
    T₀ ≤ Tann ∧
    8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) ∧
    8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
      ≤ Real.log (Real.log (5 * Tann + 1)) ∧
    Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) ∧
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) ∧
    Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hloR : ((R.Hlo : ℕ) : ℝ) ≤ ((H : ℕ) : ℝ) := by exact_mod_cast hlo
  have hsq : Real.sqrt ((R.Hlo : ℕ) : ℝ) / 2 ≤ Real.sqrt ((H : ℕ) : ℝ) / 2 := by
    have := Real.sqrt_le_sqrt hloR
    linarith
  exact
    ⟨capfloor_QTann_L_gk K hfl hb hAN hM hTlo hQ2reg,
     capfloor_kappa30Q_L_gk K hfl hb hAN hM hTlo hQ2reg,
     capfloor_T0_Tann_sharp hfl hb hAN hTlo (le_trans hT₀ (Real.exp_le_exp.mpr hsq)),
     capfloor_floor1 hfl hb hAN hTlo,
     capfloor_floor2 hfl hb hAN hTlo,
     capfloor_floor3 hfl hb hAN hTlo hKq,
     capfloor_floor4_of_regimeWin hfl hb hAN hTlo hKs0 hKsw,
     hQ2reg⟩

/-! ## §3 — ⟦HOP 8⟧ the cap-gate supply, windowed -/

set_option maxHeartbeats 1000000 in
-- Same cause as the landed original: 37 structure fields are checked against the levered
-- per-block gate in one `exact`.
/-- ⟦`Ks`-WINDOWED TWIN⟧ (`s16_capGate_supply_L_gk_sharpT0_kswin`) —
`S16ComposeV4.s16_capGate_supply_L_gk_sharpT0` on §2's windowed floor wave.  Body verbatim
apart from the floor-wave call. -/
theorem s16_capGate_supply_L_gk_sharpT0_kswin (K : ℕ) {Cq cs T₀ Kq Ks C : ℝ}
    {R : ChowlaRegime} {M : ℕ} {epsf : ℕ → ℝ}
    (hM : 1 ≤ M) (hfl : loglogFloor50 ≤ R.Hlo) (hcs : Real.exp (-100) ≤ cs)
    (hblk : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → s13BlockFloor_L_gk K M ≤ A + s)
    (hT₀ : T₀ ≤ Real.exp (Real.sqrt ((R.Hlo : ℕ) : ℝ) / 2)) (hKq : Kq ≤ Real.exp 100)
    (hKs0 : 0 < Ks)
    (hKsw : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16)
    (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hεr : ∀ A : ℕ, theta293 - 1 / 500 ≤ epsf A)
    (hcap : S16BaseScaleCap96_L_gk K R M) (hcof : S16CofactorSupply_L_gk K Cq R M) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
        2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
        5 ≤ Real.log (Real.log (2 * T)) →
        ∃ (P Q : ℕ) (Rrad Rbd CR EP2 : ℝ),
          S13CapGatePerBlock_L_gk K Cq cs T₀ Kq Ks C M (A + s) q P Q H (2 * T)
            Rrad Rbd CR EP2 (epsf (A + s)) := by
  intro H L q j A s hb T hTlo hThi hTgate hTll
  have hbb : SocketBase R M H L q j A s := socketBase_of_socketBaseL hM hb
  obtain ⟨Rrad, Rbd, CR, hRbd0, hRbdg, hCqg, hRsock⟩ := hcof H L q j A s hb T hTlo hThi
  -- the grid wave, at the linear door
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, -, g17, g18⟩ :=
    s13CapGrid_all_L_gk K hM (le_refl (1 : ℝ)) hfl hb (hblk H L q j A s hb) hTlo hThi
  -- `1 < 2T` off the annulus gate
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hT1 : (1 : ℝ) < 2 * T := by
    have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
    linarith
  have hT0le : (0 : ℝ) ≤ 2 * T := by linarith
  have hAN : A ≤ A + s := Nat.le_add_right _ _
  have hTflo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ 2 * T := by linarith
  -- the floor wave, at the linear door — §2's windowed twin
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, -⟩ :=
    s13CapFloor_all_L_gk_sharpT0_kswin K hfl hbb hM hAN hTflo g6 hT₀ hKq hKs0 hKsw
  -- the eps wave, LADDER-BLIND
  obtain ⟨hP83pin, hgradepin⟩ := s13CapEps_pins_supply hfl hbb
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ :=
    s13CapEps_all hfl hbb (hεr (A + s)) hC0 hC hT0le hThi hP83pin hgradepin
  refine ⟨s13BandP (A + s), s13BandQ (A + s), Rrad, Rbd, CR,
    s13CapEP2 C q (A + s) (s13BandP (A + s)) (s13BandQ (A + s)) (2 * T), ?_⟩
  exact
    { logX_eight := g1
      H83_two := g2
      QTann := f1
      kappa30Q := f2
      q_logX := g3
      T0_Tann := f3
      floor1 := f4
      floor2 := f5
      floor3 := f6
      floor4 := f7
      logqT_L := g4
      P_low := g5
      Q2_reg := g6
      Q_pos := g7
      Q_high := g8
      P_le_Q := g9
      budget := fun i hi =>
        s16_budget_field_L_gk_96 K hM hb.2.2.2.1 g7 g1
          (s13CapGrid_Lambda_lo hfl hbb) g3 hT1 hThi g8 g6 (hcap H L q j A s hb) hi
      Hj := g10
      B3 := g11
      BT := g12
      kappa30 := g13
      BT10 := g14
      WL := g15
      gate := s16_capGrid_gate_cs hcs (s13CapGrid_mu_2000 hfl hbb)
        (s13CapGrid_Lambda_lo hfl hbb)
      Rbd_nonneg := hRbd0
      Rbd_grade := hRbdg
      Cq_gate := hCqg
      Rbd_socket := hRsock
      epsr_nonneg := e1
      abs8640 := e2
      EP2_gate := e3
      q_arcDen := e4
      phi_row := e5
      p2_row := e6
      tail_row := e7
      Q_hundred := g17
      band_product := g18 }

/-! ## §4 — ⟦HOP 9⟧ the crossing supply, windowed

`V7B.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree` with the `Ks` antecedent moved
INSIDE its own `∀ R` binder and replaced by the window (the carrier names `R.Hlo`, so — exactly
as the landed `sharpT0` move did for `T₀` — it cannot sit in front of the regime).  `0 < Ks` is
already a conjunct of the `∃`-prefix, so nothing new is asked of the caller. -/

set_option maxHeartbeats 3200000 in
-- Same cause as the landed original: the eighteen-slot `hcapWS` family re-elaborates.
/-- ⟦`Ks`-WINDOWED TWIN⟧ (`s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin`) —
`V7B.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree` with `Real.exp (-100) ≤ Ks`
replaced by `log(1/Ks) ≤ 3·log R.Hlo/16`, inside the regime binder.  Body verbatim apart from
the intro pattern and the cap-gate call. -/
theorem s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin :
    ∃ Cq cs T₀ Kq Ks C : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ Real.exp 100 ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      ∀ K : ℕ,
        (Kq ≤ Real.exp 100 →
        ∀ (R : ChowlaRegime) (M : ℕ), 1 ≤ M → loglogFloor50 ≤ R.Hlo →
          Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16 →
          T₀ ≤ Real.exp (Real.sqrt ((R.Hlo : ℕ) : ℝ) / 2) →
          (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → s13BlockFloor_L_gk K M ≤ A + s) →
          S16CofactorSupply_L_gk K Cq R M → S16BaseScaleCap96_L_gk K R M →
          S15CrossingBound_L_gk K R M) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hwire⟩ :=
    m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs
  obtain ⟨C, hC0, hC40, hband⟩ := m4_tail_mass_at_band_bounded
  refine ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40, ?_⟩
  intro K hKq R M hM hfl hKsw hT₀ hblk hcof hcap
  -- ⟦THE cs RIDER, SPENT FROM THE PREFIX⟧ `hcsf` is the carried conjunct (V7-B);
  -- ⟦THE Ks RIDER, SPENT AS A WINDOW⟧ `hKs0` is the prefix's own positivity
  have hgate := s16_capGate_supply_L_gk_sharpT0_kswin K hM hfl hcsf hblk hT₀ hKq hKs0 hKsw
    hC0 hC40 (fun _ => le_rfl) hcap hcof
  refine hwire K R M liouvilleC (fun _ => theta293 - 1 / 500) liouvilleC_norm_le_one ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨P, Q, Rrad, Rbd, CR, EP2, hg⟩ := hgate H L q j A s hsb T hTlo hThi hTgate hTll
  have hq : 1 ≤ q := hsb.2.2.2.1
  have hA : 0 < A := hsb.2.2.2.2.2.2.2.1
  have hNd : 1 ≤ A + s := by omega
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by have := hg.logX_eight; linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
  have hT1 : (1 : ℝ) < 2 * T := by linarith
  exact doorCapBundle_at_workingPoint_perBlock_L_gk K hband hM hNd hq hg hT1 hThi hTll

/-! ## §5 — ⟦HOP 10⟧ the flat terminal, windowed

`V7B.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree` with the `Ks`
antecedent replaced by the `A`-scoped window `log(1/Ks) ≤ 3·e^{3.2A}/16`.  The landed body
already carries `hlo : e^{3.2A} ≤ log R.Hlo` (`flatWitFloor_log_ge`), which is exactly the
bridge from this form to §4's. -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 3200000 in
-- Same cause as the landed original: the hoisted prefix plus the three window discharges
-- re-elaborate the terminal's conclusion.
/-- ⟦`Ks`-WINDOWED TWIN⟧ (`logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin`)
— `V7B`'s cs-free flat terminal with `Real.exp (-100) ≤ Ks` replaced by
`Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16`.  This is the declaration a `ksarm` mint
reads.  Body otherwise verbatim. -/
theorem logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_winU Awin) :
    ∃ (ε : ℚ) (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧
        ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
          K ≤ 170000000 * flatDoorM A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          T₀ ≤ Real.exp (Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ) / 2) →
          Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 →
          ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            (S16CofactorSupply_L_gk K Cq R (flatDoorM A) →
              S16BaseScaleCap96_L_gk K R (flatDoorM A) →
                ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, hcondU⟩ :=
    flat_conditional_uniform_win_xceil_kwide_khoist Awin hband
  -- ⟦THE CROSSING CONSTANTS, HOISTED ABOVE THE LEVER⟧ — §4's windowed twin
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40,
    hsupplyU⟩ := s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  obtain ⟨_Ct0, -, -, hcond0⟩ := hcondU 0
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond0 (max 162 (budgetAFlat (ε : ℝ) β)) (le_max_left _ _) (le_max_right _ _)
  have hzero : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := by
    intro Hhi ω hgate
    obtain ⟨-, -, hωw⟩ := hgate
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [Real.log_natCast_nonneg ω]
  obtain ⟨R0, hR0eps, -, -, -, -, -⟩ :=
    hbody0 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) hzero le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have hεR : (1 : ℝ) / 500 ≤ (ε : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hεpin
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
    exact h
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  have hsupply := hsupplyU K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA26 hAwin hAge hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge
  refine ⟨fun hopq => flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hx0win hopq hT₀ hKsw g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g hg (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by
    rw [hReps]
    have : (1 : ℚ) / 2 ^ 9 ≤ 1 / 500 := by norm_num
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  -- ⟦THE BRIDGE⟧ the `A`-scoped window becomes §4's regime-scoped one at the flat floor
  have hKswR : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16 := by linarith
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win hA26 K hKw hδ₀ hδpin hKc hKcb
    hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win heps hlo hwin
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk K (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel hKw
    (hsupply hKqb R (flatDoorM A) hM1 hfl hKswR (by rw [hHlo]; exact hT₀) hblk hcof hcapsc)

/-! ## §6 — ⟦THE PROPOSED TERMINAL⟧ `v7` with the `Ks` rider discharged at the arm

Body: `V7E.logChowla2_ineffective_v7`'s, with exactly two changes — the design constant's `max`
gains a SEVENTH arm `16·log(1/Ks)/3` (so each of the eight landed absorption proofs ends in one
extra `le_max_right`), and the `Ks` arrow is discharged from inside against that arm instead of
being asked of the caller. -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 3200000 in
-- Same cause as `v7`: the `∃`-prefix and the window discharges re-elaborate the conclusion
-- under the raised lever.
/-- **⟦DREAM-SPACE, night 08/14 — branch artifact; consumes nothing until waking review⟧**

**⟦`v7` WITH THE `Ks` RIDER DISCHARGED⟧** (`logChowla2_ineffective_v7_ksarm`) —
`V7E.logChowla2_ineffective_v7` with the `Ks` arrow GONE from the inner implication.

⟦THE SURVIVING LIST⟧ outer hypotheses: NOTHING.  Inner, exactly **two** items:

* `XCeilRiderStrict ε g` — the caller's own request;
* the `K_vt` cushion
  `32·Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊ + 32·(2·log (flatDoorM A) + log 4 + 50) ≤ log R.Hhi / 4`.

⟦WHAT MOVED⟧ `Real.exp (-100) ≤ Ks` is no longer asked — and it is NOT delivered either: V7-A
traced it to an explicit NUMERICAL lower bound on Siegel's ineffective constant at `ε = 1/16`,
which neither the corpus nor the literature supplies, so the rider is NOT provable AS STATED.
What replaces it is the WINDOW `log(1/Ks) ≤ 3·log H/16`,
which `capfloor_floor4_of_pos` shows is all the `floor4` socket ever needed, and which any
`Ks > 0` meets once the design base is large enough.  §2–§5 carry that window down the four
hops that used to carry the numeral; §6 meets it by giving `A`'s `max` a seventh arm,
`16·log(1/Ks)/3`, legal for the same reason the other six are — `Ks` is minted at the crossing
supply, BEFORE the lever chooses `A`.

⟦NOTHING TRADED⟧ `A` now depends on `Ks`, but the `∃`-prefix's promises about `A` are unchanged
(`162 ≤ A`, `A₀ ≤ A` at the caller's own `A₀`), and `V7A.capfloor_floor4_of_sharp` is the
receipt that the windowed leaf subsumes the landed numeral one.

⟦STILL INEFFECTIVE⟧ the name is unchanged on purpose.  The `K_vt` cushion is the Siegel-genre
core and this file does not touch it; only the `Ks` FLOOR rider — an artefact of the numeral
chosen at `S13CapFloor:449` — is gone.  ⟦AND IT IS NOT DESTROYED, IT IS RELOCATED⟧ the
ineffective load formerly borne by the `Ks` rider is now borne by the DESIGN CONSTANT `A`,
through the new seventh `max` arm `16·log(1/Ks)/3`: `A` is no longer pinned by effective
thresholds alone, so this object's ineffectivity sits in `K_vt` AND in `A`.  Note the coupling
that follows: `A` indexes the `K_vt` cushion through `KlevF A` and `flatDoorM A`, so the
relocation touches the cushion's INDEXING even though the cushion's statement is byte-untouched
— the same situation V7-C created when it put `T₀` into this same `max`.

`logChowla2_ineffective_v7`, `…_v6`, `…_v6_csarm` and `…_v6_T0arm` are byte-untouched and remain
citable. -/
theorem logChowla2_ineffective_v7_ksarm (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
            + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
          ¬ logChowla2Fails R.eps R.x R.ω)) := by
  -- ⟦THE REPAIRED CO-FACTOR SUPPLY⟧ its four Skolem constants, minted outside everything
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ := cofkR_cofactorSupply_L_gk
  obtain ⟨Awin, -, hband⟩ := s16_bandLaneWinL_holdsU
  -- ⟦THE cs-FREE, Ks-WINDOWED FLAT TERMINAL⟧ §5
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ :=
    logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin Awin hband
  -- ⟦THE DESIGN CONSTANT, WITH THE `Ks`-ARM AND THE `T₀`-ARM⟧ seven arms now: the five landed
  -- thresholds, `T₀` (V7-C), and `16·log(1/Ks)/3` — every one of the seven constants is minted
  -- BEFORE the lever, `Ks` at the crossing-supply obtain just above.
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (16 * Real.log (1 / Ks) / 3) (max T₀
      (max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
        (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))))) := ⟨_, rfl⟩
  have hKsA : 16 * Real.log (1 / Ks) / 3 ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hT₀A : T₀ ≤ A := by rw [hAdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hA162 : (162 : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hA₀A : A₀ ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAwinA : Awin ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_right (max (max A₀ 162) Awin)
      (cofkRThr Cq Cb Xsk Y0)) (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _)
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  -- ⟦RIDER 3, DISCHARGED AT THE ARM⟧ the seventh `max` slot clears the window outright
  have hKswin : Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 := by linarith
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
    have h2 : Real.exp (3.2 * A) / 10 + 1 ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
      Real.add_one_le_exp _
    linarith
  have hopq : Hopq ≤ flatDesignBase A := by
    have h2 : Real.exp (3.2 * A) + 1 ≤ Real.exp (Real.exp (3.2 * A)) := Real.add_one_le_exp _
    have hR : ((Hopq : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by linarith
    have hceil := le_trans hR (Nat.le_ceil (Real.exp (Real.exp (3.2 * A))))
    rw [flatDesignBase]; exact_mod_cast hceil
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, hCt, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hKw
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A, hKvt0, ?_⟩
  intro g hg
  -- ⟦RIDER 2, DISCHARGED⟧ V7-C's arm at the design constant's own `T₀` slot
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKswin g hg
  refine ⟨R, hReps, by rw [hHlo]; exact hbase hopq, hRg, hRtow, hdes, hwin, ?_⟩
  intro hKvtcush
  -- ⟦ITEM 3, DISCHARGED⟧ the base-scale cap at `K = KlevF A`
  have heps500 : (1 : ℚ) / 500 ≤ R.eps := by rw [hReps]; exact hεpin
  have hxceil : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [hReps]; exact hRx
  -- ⟦RULING 9, DISCHARGED⟧ the co-factor supply at the repaired ladder
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA26
  have heps500R : (1 : ℝ) / 500 ≤ (R.eps : ℝ) := by
    rw [hReps]
    have h := (Rat.cast_le (K := ℝ)).mpr hεpin
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
    exact h
  have h518 : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by nlinarith [hdes, hA162]
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA162
  have hthrgate : cofkRThr Cq Cb Xsk Y0 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    linarith [hthrA, hlo, hexp1]
  have hcofsupply : S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) :=
    hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush
  exact hfire2 hcofsupply
    (s16_baseScaleCap96_L_at_klevF hA26 (flatDoorM_one_le hA26) heps500 hxceil hwin)

/-! ## §7 — ⟦NO TRADE⟧ the landed `v7`, re-derived from §6 -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 3200000 in
/-- **⟦NO TRADE⟧** a HAND-RETYPED copy of `V7E.logChowla2_ineffective_v7`'s statement, re-derived
from §6 by discarding the arrow (`fun _ => …`).  Be exact about what the kernel referees here:
it referees §6 AGAINST THIS RESTATEMENT, not against the landed declaration — this compiles
only if §6's statement is the restatement's with the ONE line `Real.exp (-100) ≤ Ks →` deleted
and nothing else moved, every other conjunct passed through by name, in order.  The restatement
is tied to the landed declaration by the `example` immediately below, whose type is exactly this
statement and whose proof term is `logChowla2_ineffective_v7` itself; without that receipt the
chain would stop at a retyped lookalike, and with it the copy is self-enforcing under future
edits to either side. -/
theorem logChowla2_ineffective_v7_of_ksarm (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
              + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
            ≤ Real.log (R.Hhi : ℝ) / 4 →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
    a15, a16, a17, a18, a19, a20, a21, a22, hmain⟩ := logChowla2_ineffective_v7_ksarm A₀
  exact ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
    a15, a16, a17, a18, a19, a20, a21, a22, fun _ => hmain⟩

/-! ## §7a — ⟦THE RECEIPT⟧ the restatement IS the landed declaration's type -/

set_option exponentiation.threshold 4000 in
/-- **⟦THE RESTATEMENT, TIED TO THE LANDED DECLARATION⟧** §7 retypes `v7`'s statement by hand, so
on its own it certifies only that §6 implies THAT TEXT.  This `example` closes the gap: its type
is §7's statement, character for character, and its proof term is the landed
`V7E.logChowla2_ineffective_v7` itself, so the kernel must accept the landed declaration AT the
restatement's type — i.e. the two types are the same up to defeq.  Any future drift between the
copy and `V7E:74` — a reordered conjunct, a changed constant, a silently strengthened bound —
fails to elaborate HERE, which is what makes §7's claim self-enforcing rather than a promise. -/
example (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
              + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
            ≤ Real.log (R.Hhi : ℝ) / 4 →
            ¬ logChowla2Fails R.eps R.x R.ω)) :=
  logChowla2_ineffective_v7 A₀

end Salt.MR

end
