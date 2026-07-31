/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S12Compose
import Salt.MR.M4ClosureRepair
import Salt.MR.HloExportMR

/-!
# ⟦S12-FUSE⟧ — THE CAPSTONE TWIN THAT COMPOSES FROM THE FUSES

⟦THE GRANT⟧ HEAD-SCOUT's EDGE 1, maestro ruling 1 (`docs/blueprints/flags.md`, 2026-07-30
20:25): the landed capstone `S12Compose.logChowla2_capstone_final` carries residue item ⟦B1⟧
`DoorFuseFrame M (A+s) j Ct Cp (epsf (A+s))` — the PRE-R1 frame whose `gRows` field reads
`a2RowsSum`'s growing `p²` row, unprovable at any `M ≥ 2` (the shortfall is exactly `×M`).
ROUTE (b) is: keep the landed capstone untouched and mint the TWIN that gets ⟦item 11⟧ from
`M4ClosureRepair`'s fuses instead of from the `A4` terminal.

Everything here is PURELY ADDITIVE: `S12Compose` is not edited, `M4ClosureRepair` is not
edited, no landed declaration is touched.

## §1 — THE WIRE RE-PLUMB

The fuses (`M4ClosureRepair` §5) take `hcap` and `hband` as RAW analytic integral bounds; the
landed capstone carries them as the residue items `hcapWS` (the `DoorCapErrWS` / E-binder /
`DoorCapBasePerBlock` composite) and `hbandbase` (`DoorBandBase`).  §1 mints the two
composites that turn the capstone's residue items into the fuses' raw binders:

* `m4_fuse_hcap_of_capWS` — `M4CapWire.m4_hcap_at_door_perBlock` composed with
  `RamErrWS.m4_capE_at_door`, i.e. the exact inner block of
  `S11Hoist.m4_socket_discharged_capwired_ws_hoisted_perBlock_split`, extracted;
* `m4_fuse_hband_of_bandBase` — `S11Hoist.m4_hband_at_door_slot_split`, whose conclusion is
  ALREADY the fuses' `hband` binder byte for byte.  (`DoorBandBase` itself remains an
  UNSUPPLIED residue item corpus-wide; only its CONSUMPTION is re-routed here.)

## §2 — THE TWO TERMINAL CONJUNCTS

The `A4` terminal returned three conjuncts; the fuses return only ⟦item 11⟧.  The other two
are minted here from the landed `ρ`-page: `m4_fuse_gate4_at_sock` (⟦gate 4⟧'s read, which is
`M4ArithRho.m4_arith_gate4_rho`, definitional in `m4ChiRowGraded`) and `m4_fuse_ceil_at_sock`
(the `H`-uniform ceiling, `M4ArithRho.m4_arith_rs_ceiling_met_of_delta` at `δ_sock`).  The
numeric content of the second is the landed `96·(1+2π)²·(108/5) ≤ 110525` step —
`doorRhoOfDelta`'s divisor is `110525` and the exact constant is `109993.67`, a `0.48%` slack.

## §3 — THE FUSE AT A NONNEGATIVE DENSITY CONSTANT

`M4ClosureRepair.m4_closure_fuse_zero'` binds `∀ Cp, 0 < Cp`; the capstone's prefix binds
`∀ Cp, 0 ≤ Cp`.  The strictness is not used anywhere below the fuse — the supplier
`M4RowsChiZeroPrime.m4_hrowsSlot_at_door_zero'` asks `0 ≤ Cp` — so §3 mints the fuse at the
nonnegative binder, and the twin's prefix stays byte-identical to the landed capstone's.

## §4 — THE TWIN

`logChowla2_capstone_final'`: the landed capstone's prefix and conclusion VERBATIM, the
⟦A⟧-group residue and ⟦B2⟧–⟦B6⟧ byte-compatible, and ⟦B1⟧ replaced by the fuse's own five
demands at the DECAY pool.

⚠ ⟦THE `epsrf` COLLISION — the honest reading of HEAD-SCOUT's EDGE 4⟧.  The decay pool's
`eps_pool` field is `(log X_d)^{−θ₂₉₃+ε} ≤ (log X_d)^{−θ₂₉₃}`, so on this road the crossing
exponent is pinned `ε ≤ 0` (`M4ClosureRepair.eps_pool_at_decayPool`); the fuse feeds ONE `ε`
to both that field and its `hcap` binder, and `m4_fuse_hcap_of_capWS` emits `hcap` at the cap
bundle's own exponent.  So the twin's pool pin and its ⟦B2⟧ window (`0 ≤ epsrf`) together pin
`epsrf ≡ 0` at every base the socket reaches, where `DoorCapBasePerBlock.abs8640` reads
`8640 ≤ (log X_d)^0 = 1`.  ⟦B2⟧ is nonetheless kept EXACTLY as landed (the pin belongs at
instantiation, not in the statement), and the collision is stated here rather than hidden:
the fuse road removes B1's `×M` shortfall and replaces it with a single named exponent
collision between the pool's `𝒰`-leg and the cap bundle's `𝒰`-leg gate.  Both landed pool
forms (`decayPool` and `constPool`) carry `hε : ε ≤ 0`, so the collision is a property of the
FUSES as landed, not of the pool choice; clearing it needs one new `eps_pool` stone at
`0 < ε < θ₂₉₃` against a base-LOWER threshold (`constPool` admits one, `decayPool` does not).

## ⟦THE `R.Hlo` CAP⟧ (maestro amendment, EDGE 5)

Both twins consume `HloExportMR.m4_second_road_L2_hloCap`, not the landed
`S12Compose.m4_second_road_L2`: they export `Hcap : ℕ` beside `x₀` in the top constant block
and carry `R.Hlo ≤ max Hcap U1floor` in the `∃ R` payload, immediately after the `9/2` tower
conjunct.  The capstone fires the road at the ENLARGED floor
`max U1floor (max arcFloor36 loglogFloor50)`, so the exported cap is
`Hcap := max Hcap_road (max arcFloor36 loglogFloor50)`; `max` associativity/commutativity
turns the road's `max Hcap_road (max U1floor F)` into the twin's `max Hcap U1floor` exactly,
with no slack given away.  Fired at any `U1floor ≥ Hcap` the payload pins `R.Hlo = U1floor`
between the two conjuncts, which is the two-sided `loglog R.Hlo` band the compose needs.

## §5 — THE TWIN AT THE RAW CAP

`logChowla2_capstone_final_rawcap'` is §4's twin with ⟦B4⟧ carried as the RAW analytic
`hcap` binder instead of the `hcapWS` composite — the shape `M4AssemblyFrames` §9's
`m4_closure_fuse_zero'_at_socket` also carries ("spine-witnessed; carried").  It is the
variant with NO exponent collision: at `epsrf ≡ 0` (the pin ⟦B2⟧ and the pool pin jointly
force, and the instance `M4ClosureRepair` §1's header calls "intended") the raw binder is a
plain analytic demand, and `abs8640` never enters.  The two twins differ in ONE residue item
and nothing else.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE WIRE RE-PLUMB -/

set_option maxHeartbeats 1000000 in
-- The eighteen-slot `hcapWS` body re-elaborates against the wire's own family shape (the same
-- cause as `S11Hoist` §5, from which this block is extracted).
/-- **⟦THE FUSE'S `hcap`, FROM THE CAPSTONE'S `hcapWS`⟧** (`m4_fuse_hcap_of_capWS`).

Input: the landed capstone's ⟦B4⟧ residue item, byte for byte — the `DoorCapErrWS` witness
plus the E-binder implication into `DoorCapBasePerBlock`, at the SAME five constants
`Cq cs T₀ Kq Ks` the capstone carries.

Output: `M4ClosureRepair.m4_closure_fuse_end'`/`_zero'`'s `hcap` binder at the door pin
`t₁ ≡ 0`, byte for byte.

The proof is the inner block of
`S11Hoist.m4_socket_discharged_capwired_ws_hoisted_perBlock_split`, extracted so that the
fuse route can consume it without the `A4` terminal. -/
theorem m4_fuse_hcap_of_capWS :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
              DoorCapErrWS M (A + s) q Xd P Q b cf (2 * T) E Mtail
                ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                      ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                        (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU M)))
                        (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                    → DoorCapBasePerBlock Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                        (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, hwire⟩ := m4_hcap_at_door_perBlock
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, ?_⟩
  intro R M cU ε hc1 hcapWS
  refine hwire R M cU ε hc1 ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (m4_capE_at_door hws)⟩

/-- **⟦THE FUSE'S `hband`, FROM THE CAPSTONE'S `DoorBandBase`⟧** (`m4_fuse_hband_of_bandBase`).

`S11Hoist.m4_hband_at_door_slot_split` restated at the fuse's binder: its conclusion IS
`M4ClosureRepair.m4_closure_fuse_end'`/`_zero'`'s `hband` binder, byte for byte, so the
re-plumb costs nothing.  The prefix is the split-hoisted one the capstone needs (`x₀` in the
top constant block, `C'` after `M`, `R` after `C'`).

⚠ `DoorBandBase` is a HYPOTHESIS everywhere and a theorem nowhere in the corpus; this lemma
re-routes its CONSUMPTION only, and it stays a residue item of the twin exactly as it is a
residue item of the landed capstone. -/
theorem m4_fuse_hband_of_bandBase (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ x₀ : ℕ, ∀ (M : ℕ), 1 ≤ M →
      ∃ C' : ℝ, 0 < C' ∧
        ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
          ((∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q,
                (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                  ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                  ≤ t0BandB (((A + s : ℕ)) : ℝ)
                      (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) :=
  m4_hband_at_door_slot_split hMmu Aexp hAexp

/-! ## §2 — THE TWO TERMINAL CONJUNCTS -/

/-- **⟦GATE 4 AT THE SOCKET THRESHOLD⟧** (`m4_fuse_gate4_at_sock`) — the `A4` terminal's
SECOND output conjunct, minted standalone.  `M4ArithRho.m4_arith_gate4_rho` at
`ρ := doorRhoOfDelta δ_sock`: the read is definitional in `m4ChiRowGraded`'s `an`-slot, so
nothing but the envelope's own reflexivity is spent. -/
theorem m4_fuse_gate4_at_sock (M : ℕ) (δ₀ K : ℝ) :
    ∀ j H : ℕ, doorRowFloor M ≤ j →
      m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ K)) H) j H
        ≤ RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ K)) H :=
  m4_arith_gate4_rho M (doorRhoOfDelta (s12DeltaSock δ₀ K))

/-- **⟦THE `H`-UNIFORM CEILING AT THE SOCKET THRESHOLD⟧** (`m4_fuse_ceil_at_sock`) — the `A4`
terminal's THIRD output conjunct, minted standalone.
`M4ArithRho.m4_arith_rs_ceiling_met_of_delta` at `δ := δ_sock`, whose numeric content is
`96·(1+2π)²·(108/5) ≤ 110525` — exactly `doorRhoOfDelta`'s divisor, the exact left side being
`109993.67` (`0.48%` slack).  The only hypotheses are the socket threshold's positivity and
the register's own `H`-floor. -/
theorem m4_fuse_ceil_at_sock {δ₀ K : ℝ} (hδ₀ : 0 < δ₀) (hK : 0 < K) {H : ℕ}
    (hL0 : 0 ≤ Real.log (H : ℝ)) (hlam : 50 ≤ Real.log (Real.log (H : ℝ))) :
    96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ K)) H)
      ≤ s12DeltaSock δ₀ K ^ 2 :=
  m4_arith_rs_ceiling_met_of_delta (s12DeltaSock_pos hδ₀ hK).ne' hL0 hlam

/-! ## §3 — THE FUSE AT A NONNEGATIVE DENSITY CONSTANT -/

/-- **⟦THE FUSE, `zero'` CHAIN, AT `0 ≤ C_p`⟧** (`m4_closure_fuse_zero'_nonneg`) —
`M4ClosureRepair.m4_closure_fuse_zero'` with its `0 < Cp` binder relaxed to `0 ≤ Cp`.

Nothing below the fuse uses the strictness: the density constant enters only through
`GRowsZeroGate'''`'s `dens` slot (which the caller supplies) and through
`M4RowsChiZeroPrime.m4_hrowsSlot_at_door_zero'`, whose own binder is `0 ≤ Cp`.  The proof is
the landed fuse's, with `m4_chiSummedFreeRow_of_doorAssembly_pool'_gated` applied directly
instead of through `..._pool_zero'_gated`'s strict wrapper. -/
theorem m4_closure_fuse_zero'_nonneg :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (K ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
            ≤ decayPool (A + s)) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          GRowsZeroGate''' M (A + s) Cp (decayPool (A + s))) →
        (∀ A : ℕ, ε A ≤ 0) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) →
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
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε K ρ cU bU t₁ hM hb1 hc1 hbf hgP1 hgRows heps hL4096 hbase hcap
    hband harith
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_gated (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := decayPool)
    (RSbig := fun _ H => RSanDoorRho ρ H) hM ?_
    (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband decayPool_nonneg
    (m4_arith_henv_rho_pool decayPool_nonneg harith (price_at_decayPool_socket harith))
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_cc_decay (hbf H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-! ## §4 — THE TWIN -/

set_option maxHeartbeats 1000000 in
-- The statement re-elaborates the full residue against the re-cut prefix (as in `S12Compose`
-- §3/§4).
/-- **⟦THE CAPSTONE TWIN, FROM THE FUSES⟧** (`logChowla2_capstone_final'`).

`S12Compose.logChowla2_capstone_final` with ⟦item 11⟧ taken from `M4ClosureRepair`'s
`zero'` fuse instead of from the `A4` terminal.  UNCHANGED, byte for byte: the prefix (the
eleven constants and `x₀` in the top block, `∀ Cp ≥ 0`, `R` before `M`, `C'` after `M`), the
conclusion `¬ logChowla2Fails R.eps R.x R.ω`, the ⟦A⟧-group spine arithmetic (A1–A5), and the
residue items ⟦B2⟧ (the `epsrf` window), ⟦B3⟧ (the five-field per-base bundle), ⟦B4⟧
(`hcapWS`), ⟦B5⟧ (`DoorBandBase`) and ⟦B6⟧ (`DoorArithFrameRho`).

⟦THE EDGE-5 CARRY⟧ the road consumed is `HloExportMR.m4_second_road_L2_hloCap`, so the prefix
additionally exports `Hcap : ℕ` beside `x₀` and the payload additionally carries
`R.Hlo ≤ max Hcap U1floor` right after the tower conjunct — see the file header for the
`max`-arithmetic that keeps the carry exact across the capstone's enlarged floor.

⟦THE ONE DELTA⟧ residue item ⟦B1⟧ — `DoorFuseFrame M (A+s) j Ct Cp (epsf (A+s))`, the pre-R1
frame with the `×M` `gRows` shortfall — is REPLACED by the fuse's own five demands at the
decay pool:

1. `DoorBaseFrame (A+s) j` — the six frame fields that never mention a pool;
2. the `gP1` gate `374784·Ct·e³/𝒫₁ ≤ decayPool (A+s)`;
3. `GRowsZeroGate''' M (A+s) Cp (decayPool (A+s))` — the FOUR-slot re-split, whose `p²` slot
   is `X_d`-FREE (this is where B1's `×M` shortfall dies);
4. the pool's `𝒰`-leg pin `∀ A, epsrf A ≤ 0`;
5. the corrected band threshold `4096 ≤ (log X_d)^{1−1/500−θ₂₉₃}`.

`epsf` survives in the binder list (prefix byte-compatibility, written `_epsf` to keep the
linter quiet) but is now INERT: ⟦B1⟧ was its only consumer.

⚠ See the file header for the `epsrf` collision: item 4 above and ⟦B2⟧'s `0 ≤ epsrf` pin
`epsrf ≡ 0` at every base the socket reaches, where ⟦B4⟧'s `DoorCapBasePerBlock.abs8640`
reads `8640 ≤ 1`. -/
theorem logChowla2_capstone_final' (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ Ct Cq cs T₀ Kq Ks : ℝ) (x₀ Hcap : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
        ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
          ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
            R.Hlo ≤ max Hcap U1floor ∧
            ∀ (M : ℕ), 1 ≤ M →
              ∃ C' : ℝ, 0 < C' ∧
                ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                  -- ⟦A⟧ THE SPINE ARITHMETIC
                  M4DoorGates Cg R M k δ₀ →
                  8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloor M : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    m4SmallGradeFits (doorRowFloor M)
                      (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ K)) H)
                      (fun H => 2 * rStrWitness H) H) →
                  -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE DECAY POOL
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
                      ≤ decayPool (A + s)) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    GRowsZeroGate''' M (A + s) Cp (decayPool (A + s))) →
                  (∀ A : ℕ, epsrf A ≤ 0) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (4096 : ℝ)
                      ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) →
                  -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    calQK (Adoor M) (3072 * M) M 2 ≤ A + s ∧
                      Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
                          ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                      ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                      5 ≤ Real.log (Real.log (2 * T)) →
                      ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
                        (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
                        DoorCapErrWS M (A + s) q Xd P Q b cf (2 * T) E Mtail
                          ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                                ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                                  (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU M)))
                                  (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                              → DoorCapBasePerBlock Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb
                                  b cf (2 * T) VJ V Lr η εd (epsrf (A + s)) Rbd CR KS E EP2)) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ K))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, Hcap, hCg, hε, hK, hδ₀, hroad⟩ := m4_second_road_L2_hloCap
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_nonneg
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, hcapwire⟩ := m4_fuse_hcap_of_capWS
  obtain ⟨x₀, hbandsplit⟩ := m4_fuse_hband_of_bandBase mmuChiRate_holds_gated Aexp hAexp
  refine ⟨Cg, ε, K, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀,
    max Hcap (max arcFloor36 loglogFloor50), hCg, hε, hK, hδ₀, hCt, hCq, hcs, hT₀, hKq,
    hKs, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hM
  obtain ⟨C', hC'pos, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows heps hL4096
    _hepsr hbase5 hcapWS hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ K with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hK
  have hδssq : δs ^ 2 = δ₀ / (16 * K) := s12DeltaSock_sq hδ₀ hK
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorRowZeroBase M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM (fun i m => norm_doorPunctCoeffU_le_one M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows heps hL4096 hbase
      (hcapwire R M liouvilleC epsrf (fun p => liouvilleC_norm_le_one p) hcapWS)
      (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧ minted in §2
  have hgate4 : ∀ j H : ℕ, doorRowFloor M ≤ j →
      m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * K))
    (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloor M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloor M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloor M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloor M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
    have hKpos : (0 : ℝ) < 16 * K := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * K) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * K * (δ₀ / (8 * K)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

/-! ## §5 — THE TWIN AT THE RAW CAP -/

set_option maxHeartbeats 1000000 in
-- Same cause as §4.
/-- **⟦THE CAPSTONE TWIN, AT THE RAW CAP⟧** (`logChowla2_capstone_final_rawcap'`).

§4's twin with residue item ⟦B4⟧ carried as the fuse's RAW `hcap` binder (the door pin
`t₁ ≡ 0`, the coefficient pin `cU := liouvilleC`) instead of the `DoorCapErrWS` / E-binder /
`DoorCapBasePerBlock` composite.  EVERY other item, the prefix (including `Hcap` and the
EDGE-5 payload conjunct), the eleven constants and the conclusion are §4's, byte for byte.

⟦WHY IT EXISTS⟧ the fuse feeds ONE exponent to its `hcap` binder and to the pool's `𝒰`-leg
field, and the pool pins that exponent `≤ 0`.  Routed through the cap bundle (§4) this
collides with `DoorCapBasePerBlock`'s `epsr_nonneg`/`abs8640` pair; carried raw it does not
— at `epsrf ≡ 0` the binder is exactly the analytic statement the closure examiner's `ε := 0`
probe intended.  `Cq`, `cs`, `T₀`, `Kq`, `Ks` are still the cap wire's own constants, so a
later wave that re-attaches a cap route inherits them unchanged. -/
theorem logChowla2_capstone_final_rawcap' (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ Ct Cq cs T₀ Kq Ks : ℝ) (x₀ Hcap : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
        ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
          ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
            R.Hlo ≤ max Hcap U1floor ∧
            ∀ (M : ℕ), 1 ≤ M →
              ∃ C' : ℝ, 0 < C' ∧
                ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                  -- ⟦A⟧ THE SPINE ARITHMETIC
                  M4DoorGates Cg R M k δ₀ →
                  8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloor M : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    m4SmallGradeFits (doorRowFloor M)
                      (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ K)) H)
                      (fun H => 2 * rStrWitness H) H) →
                  -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE DECAY POOL
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
                      ≤ decayPool (A + s)) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    GRowsZeroGate''' M (A + s) Cp (decayPool (A + s))) →
                  (∀ A : ℕ, epsrf A ≤ 0) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (4096 : ℝ)
                      ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500 - theta293)) →
                  -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    calQK (Adoor M) (3072 * M) M 2 ≤ A + s ∧
                      Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
                          ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                      ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                  -- ⟦B4 RAW⟧ the crossing bound, carried
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                      (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                      5 ≤ Real.log (Real.log (2 * T)) →
                      (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                          ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                        ≤ 8 * (0 : ℝ) ^ 2
                          + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                \ seamBall (((A + s : ℕ)) : ℝ) 0)
                              ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                  (calP (Adoor M) (3072 * M))
                                  (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                                  (mrAlpha (1 / 12)) 2,
                              ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                          + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                              * (Real.log (((A + s : ℕ)) : ℝ))
                                  ^ (-theta293 + epsrf (A + s)))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ K))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, Hcap, hCg, hε, hK, hδ₀, hroad⟩ := m4_second_road_L2_hloCap
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_nonneg
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS
  obtain ⟨x₀, hbandsplit⟩ := m4_fuse_hband_of_bandBase mmuChiRate_holds_gated Aexp hAexp
  refine ⟨Cg, ε, K, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀,
    max Hcap (max arcFloor36 loglogFloor50), hCg, hε, hK, hδ₀, hCt, hCq, hcs, hT₀, hKq,
    hKs, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hM
  obtain ⟨C', hC'pos, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows heps hL4096
    _hepsr hbase5 hcapraw hbandbase harith
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  set δs : ℝ := s12DeltaSock δ₀ K with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hK
  have hδssq : δs ^ 2 = δ₀ / (16 * K) := s12DeltaSock_sq hδ₀ hK
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  have hbase : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorRowZeroBase M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness (A + s) hM, h2, h3, h4, h5⟩
  have hrow : M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM (fun i m => norm_doorPunctCoeffU_le_one M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows heps hL4096 hbase hcapraw
      (hbandslot R C₁ M₀ hbandbase) harith
  have hgate4 : ∀ j H : ℕ, doorRowFloor M ≤ j →
      m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  refine hR δ₀ (δ₀ / (8 * K))
    (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloor M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloor M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloor M) (hj0 H hlo hhi)
    linarith
  · intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloor M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
    have hKpos : (0 : ℝ) < 16 * K := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * K) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · have hval : 2 * K * (δ₀ / (8 * K)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

end Salt.MR

end
