/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S13CapGateLinear
import Salt.MR.S16FlatTerminalLinear

/-!
# `S16FlatFinal` — THE CROSSING BOUND, SUPPLIED, AND THE FLAT LINEAR TERMINAL WITHOUT IT

⟦CAPGATE-L⟧  `S16FlatTerminalLinear` §6 carried `S15CrossingBound_L_gk 32000000 R (flatDoorM A)`
as its fifth rider — the ONE remaining named supply of the linear ladder.  This file supplies
it and re-cuts the terminal with the rider REMOVED-BECAUSE-PROVEN.

⟦THE TWO HOPS⟧

* §1 `s15_crossing_supplied_L_gk` — `S16Budget.s15_crossing_supplied_wide_gk (:2461)` at the
  linear ladder.  The WIRE is `S16FlatTerminalLinear.m4_fuse_hcap_of_capWS_L_gk` (§8, landed);
  the CAP GATE is `S13CapGateLinear.s16_capGate_supply_L_gk` (this wave) composed through
  `doorCapBundle_at_workingPoint_perBlock_L_gk`.

* §2 `logChowla2_witnessed_scale_flat_L_v2` — `S16FlatTerminalLinear`'s §6 with the crossing
  discharged in-proof off the register the same §6 already SUPPLIES
  (`s15_sel''_L_gk_witness_flat_bumped`), through `s15_block_at_socket_L_gk`.

⟦WHAT THE DISCHARGE COSTS, EXACTLY⟧ the crossing does not vanish; it is PAID.  The v2 terminal
carries, in its place: the fuse's four numeric riders `e^{-100} ≤ cs`, `T₀ ≤ e^{e^{100}}`,
`Kq ≤ e^{100}`, `e^{-100} ≤ Ks` (spent on EXISTENTIALLY BOUND constants the statement itself
produces), and the two predicates the landed wide terminal also carries — ⟦RULING 9⟧'s
co-factor debt `S16CofactorSupply_L_gk` and ⟦ITEM 3⟧'s base-scale cap
`S16BaseScaleCap96_L_gk`, both at the LINEAR door and the LINEAR socket, hence both WEAKER
than their landed counterparts (`s16_baseScaleCap96_L_of_baseScaleCap96` proves the cap
direction outright).  What is GONE is the crossing itself: `cs`/`T₀`/`Kq`/`Ks` are now
witnessed constants of this theorem rather than an opaque `Prop` about an integral.

**PURELY ADDITIVE.**  No landed declaration is touched.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE CROSSING BOUND AT THE LINEAR LADDER, SUPPLIED -/

set_option maxHeartbeats 1000000 in
-- the eighteen-slot `hcapWS` family re-elaborates against the wire's own shape
/-- **⟦THE CROSSING SUPPLY AT THE LINEAR LADDER⟧** (`s15_crossing_supplied_L_gk`) —
`S16Budget.s15_crossing_supplied_wide_gk (:2461)` at `AdoorL M = 2^36·M`.  The body is the
landed one, reading `m4_fuse_hcap_of_capWS_L_gk` for the wire, `s16_capGate_supply_L_gk` for
the gate and `doorCapBundle_at_workingPoint_perBlock_L_gk` for the join. -/
theorem s15_crossing_supplied_L_gk (K : ℕ) :
    ∃ Cq cs T₀ Kq Ks C : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      (Real.exp (-100) ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ (R : ChowlaRegime) (M : ℕ), 1 ≤ M → loglogFloor50 ≤ R.Hlo →
          (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → s13BlockFloor_L_gk K M ≤ A + s) →
          S16CofactorSupply_L_gk K Cq R M → S16BaseScaleCap96_L_gk K R M →
          S15CrossingBound_L_gk K R M) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs0, hT₀3, hKq0, hKs0, hwire⟩ :=
    m4_fuse_hcap_of_capWS_L_gk K
  obtain ⟨C, hC0, hC40, hband⟩ := m4_tail_mass_at_band_bounded
  refine ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro hcs hT₀ hKq hKs R M hM hfl hblk hcof hcap
  have hgate := s16_capGate_supply_L_gk K hM hfl hcs hblk hT₀ hKq hKs hC0 hC40
    (fun _ => le_rfl) hcap hcof
  refine hwire R M liouvilleC (fun _ => theta293 - 1 / 500) liouvilleC_norm_le_one ?_
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

/-! ## §2 — THE FLAT LINEAR TERMINAL WITH THE CROSSING GONE -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 1600000 in
-- same cause as the landed §6: the seventeen-binder prefix re-elaborates beside the crossing
-- supply's six constants
/-- **⟦THE FLAT LINEAR TERMINAL, `v2`⟧** (`logChowla2_witnessed_scale_flat_L_v2`) —
`S16FlatTerminalLinear.logChowla2_witnessed_scale_flat_L` with rider 5
(`S15CrossingBound_L_gk 32000000 R (flatDoorM A)`) **REMOVED-BECAUSE-PROVEN**.

⟦THE SURVIVING HYPOTHESIS LIST, EXACT AND COMPLETE⟧ the outer hypothesis is `hband`
(`S16BandLaneCBoundedL 32000000`) and the design floor `A₀ ≥ 162`.  The inner implication
asks for, in order:

1. `Kc ≤ 2^539` — the wide socket ceiling (true at the closed form `KExpr = 12·10^{161}
   = 2^{538.42}`; the chain's own `Kc` exports positivity only);
2. `Ct ≤ 2^23` — the wide constant-pool ceiling (true at `6·e^{14} = 2^{22.78}`, same caveat);
3. `(x₀ : ℝ) ≤ e^{e^{3.2A}/10}` — ⟦THE `x0` WINDOW⟧, a real constraint on the opaque Siegel
   threshold, CARRIED;
4. `Hopq ≤ flatDesignBase A` — ⟦THE ARM CENSUS⟧, ⟦REF-FLAT-SAT⟧'s Siegel-honest surviving form
   of the width demand: a quantitative ceiling on the road's opaque arm, whose `H₀red`/`H₀D3`
   carry the Siegel-ineffective `K_Chen`.  CARRIED, same genre as 3;
5. `e^{-100} ≤ cs`, `T₀ ≤ e^{e^{100}}`, `Kq ≤ e^{100}`, `e^{-100} ≤ Ks` — ⟦NEW, FROM THE
   CROSSING SUPPLY⟧ the fuse's four numeric riders.  They are spent on constants THIS
   THEOREM EXISTENTIALLY PRODUCES (`cs`, `T₀`, `Kq`, `Ks` are bound in the ∃-prefix with
   `0 < cs`, `3 ≤ T₀`, `0 < Kq`, `0 < Ks` already exported), exactly as the landed wide
   terminal `S16Budget.logChowla2_witnessed_scale_final'_v3` carries them.

and the conclusion's own two carried predicates, again ⟦NEW, FROM THE CROSSING SUPPLY⟧ and
again exactly the landed wide terminal's pair, at the LINEAR door and socket:

* `S16CofactorSupply_L_gk 32000000 Cq R (flatDoorM A)` — ⟦RULING 9⟧'s shelved `Rbd`/`Cq` debt;
* `S16BaseScaleCap96_L_gk 32000000 R (flatDoorM A)` — ⟦ITEM 3⟧'s base-scale cap at the
  divisor `9.60000096`.  WEAKER than the landed `S16BaseScaleCap96_gk`, which implies it
  (`s16_baseScaleCap96_L_of_baseScaleCap96`).

⟦WHAT IS EXPORTED, UNCHANGED FROM §6⟧ `R.eps = ε`, `R.Hlo = flatWitFloor ε β A Hopq`,
`g R.Hhi R.ω ≤ R.x`, the road's WIDTH CERTIFICATE, `3.2A ≤ loglog H₋`, and the width line
`loglog H₊ ≤ 2·e^{1.6A}` (itself REMOVED-BECAUSE-PROVEN in §6, kept as an export).
`A` is SYMBOLIC and above the caller's `A₀`. -/
theorem logChowla2_witnessed_scale_flat_L_v2 (hband : S16BandLaneCBoundedL 32000000)
    (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
      (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
      (Kc ≤ 2 ^ 539 → Ct ≤ 2 ^ 23 →
        (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
        Hopq ≤ flatDesignBase A →
        Real.exp (-100) ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (S16CofactorSupply_L_gk 32000000 Cq R (flatDoorM A) →
            S16BaseScaleCap96_L_gk 32000000 R (flatDoorM A) →
              ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hcap, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hA26, hA₀A, hAge, hCapLe, hbody⟩ :=
    logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_L 32000000 (by norm_num) hband
      A₀ hA₀
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40, hsupply⟩ :=
    s15_crossing_supplied_L_gk 32000000
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`
  obtain ⟨R0, hR0eps, -, -, -, -⟩ :=
    hbody (flatWitFloor ε β A Hopq) (fun _ _ => 0) (flatCap_le_flatWitFloor hCapLe)
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have hεR : (1 : ℝ) / 500 ≤ (ε : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hεpin
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
    exact h
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb, hβ, hA26, hA₀A, hAge,
    fun hopq => flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hKb hCtb hx0win hopq hcs hT₀ hKq hKs g
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  -- ⟦THE REGISTER, SUPPLIED⟧ at the flat design modulus
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have hKle : (32000000 : ℕ) ≤ 170000000 * flatDoorM A := by
    calc (32000000 : ℕ) ≤ 170000000 * 1 := by norm_num
      _ ≤ 170000000 * flatDoorM A := Nat.mul_le_mul_left _ hM1
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by
    rw [hReps]
    have : (1 : ℚ) / 2 ^ 9 ≤ 1 / 500 := by norm_num
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  have hsel := s15_sel''_L_gk_witness_flat_bumped hA26 32000000 hKle hδ₀ hδpin hKc hKb
    hCt hCtb hCgle hMflb hx0win heps hlo hwin
  -- ⟦THE CROSSING, SUPPLIED⟧ the block floor off the register's own `blk` line
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk 32000000 (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk 32000000 (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel
    (hsupply hcs hT₀ hKq hKs R (flatDoorM A) hM1 hfl hblk hcof hcapsc)

end Salt.MR

end
