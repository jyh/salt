/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4RowsChiEnd
import Salt.MR.M4ArithPage

/-!
# ⟦A4 — THE FINAL FUSE: THE SOCKET, DISCHARGED IN ITS HONEST CONDITIONAL FORM⟧
(`M4SocketDischarge`)

`docs/blueprints/flags.md` ⟦D5-WS lands⟧ + ⟦ASSEMBLY-ARITH lands⟧ (both 2026-07-30).  Two
halves landed within eight minutes of each other and were deliberately left uncomposed
(dependency hygiene — the siblings were aloft at the same time):

* `M4RowsChiEnd.m4_chiSummedFreeRow_of_doorAssembly_end` — ⟦item 11⟧ with the `hrows` binder
  GONE, at the STRICT relativized pair law;
* `M4ArithPage.m4_chiSummedFreeRowBig_of_doorGradeGated` / `m4_arith_henv` /
  `m4_arith_gate4` / `m4_arith_rs_ceiling_met` — the arithmetic, closed at
  `RSanDoor H = doorRho / strataResidual H²`, `doorRho = 2⁻³⁴¹`.

This file is the ten-line composition the second entry names, plus the `hband` discharge the
first entry lists as LANDED-BUT-UNWIRED, plus the bundling of the second road's three demands
(⟦item 11⟧, ⟦gate 4⟧, the ceiling) at ONE hypothesis set.

## ⟦THE ONE STRUCTURAL POINT⟧ — why this is not a `.trans` of the two exits

`M4RowsChiEnd.m4_chiSummedFreeRow_of_doorAssembly_end` carries `M4Assembly`'s **UNGATED**
`henv` (`∀ H j A s, doorRowFloor M ≤ j → …`), and ⟦ASSEMBLY-ARITH⟧'s structural finding is
that no analytic `RSbig` can meet that shape (at `A + s = 2` the third summand alone exceeds
`188132`).  So the fuse does NOT go through `_end`'s conclusion: it goes through `_end`'s
`hrows` SUPPLIER (`m4_hrowsSlot_at_door_end`) into the GATED socket
(`m4_chiSummedFreeRowBig_of_doorGradeGated`), which takes `henv` only at `SocketBase`.  §1 is
that re-composition; it is `M4ArithPage.m4_chiSummedFreeRow_of_doorArith`'s proof with the D2
`hrows` slot replaced by D5's `_end` supplier.

## ⟦THE COMPLETE HYPOTHESIS LIST OF `m4_socket_discharged_conditional`⟧

The PORT-AUDIT enumeration law, applied at the terminal.  Grouped by supplier-status; nothing
is absorbed, nothing is weakened, and no binder below is a restatement of another.

**⟦SPINE-WITNESSED⟧** — the register's own witnessed-data group instantiates these; they are
not analytic facts and no page can prove them:

* `hbase : ∀ H L q j A s, SocketBase R M H L q j A s → DoorRowEndBase M (A+s) j cU bU`
  — seven fields, of which `coefWS` is ⟦THE STRICT PAIR LAW⟧ at the door's OWN blocks
  (`SeamRowWindowed.SeamCoefWS`, level by level).  This is the spine's witnessed-data item:
  the `q = 1` side carries the same object at `ThmA2Rows.a2Rows_of_capfree3_end`.  The
  remaining six fields (`Q2_le`, `reg`, `big`, `dom`, `h_four`, `Q1_le_h`) are the `q = 1`
  chain's own `X_d`-side reconciliation gates and the two weighting-frame numerals.
* `hframe : ∀ H L q j A s, SocketBase R M H L q j A s → DoorFuseFrame M (A+s) j Ct Cp (ε (A+s))`
  — eleven fields, `M4Assembly`'s frozen frame at the base `X_d = A + s`, `h = 2^j`.
* `harith : ∀ H L q j A s, SocketBase R M H L q j A s →`
  `DoorArithFrame M H j (A+s) (C₁ (A+s)) (M₀ (A+s)) K`
  — ten fields, ⟦C4⟧'s arm + ⟦C1⟧'s anchor + the `M₀` window + the `j`-floor + the `H`-floor,
  with ⟦C3⟧'s `K` SYMBOLIC (never evaluated, never `cffKVt`).

**⟦REGIME⟧** — facts about the register `R` and the closing constant:

* `hδ₀ : 2/10⁴⁹ ≤ δ₀`;
* `hHreg : ∀ H ∈ [R.Hlo, R.Hhi], 0 ≤ log H ∧ 50 ≤ loglog H`.

**⟦DATA⟧** — the door's untwisted Ramaré data:

* `hM : 1 ≤ M`;  `hb1 : ∀ i m, ‖bU i m‖ ≤ 1`;  `hc1 : ∀ p, ‖cU p‖ ≤ 1`.

**⟦CARRIED⟧** — one binder, with its supplier named and its own residue enumerated:

* `hcap` — the A3 capstone family at the door pin `S ≡ 0`, per `(H,L,q,j,A,s,χ,T)`.
  Supplier: `M4RowsChi.m4_rowChi_capstone`.  **NOT instantiated here**, and the reason is
  byte-precise rather than aesthetic: `m4_rowChi_capstone` is quantified over ~45 binders of
  which THREE are open supply-side objects at the door — the co-factor bound `Rbd` with its
  `Cq`-gate (supplier `RbdSupply`), the `𝒯_S` grade budget `KS` with its two gates, and
  Lemma 12's `χ`-SUMMED error row `E` with its four absorption gates — and the razor family
  is quantified at `(q, 2T)` with `T` bound INSIDE the slot.  Instantiating it would replace
  one named binder by a per-`(q,T)` bundle of ~45 fields and discharge nothing.  That is a
  wave, not a fuse.  (Its ball binder `hSup` IS already discharged at the door pin by
  `M4Assembly.m4_hSup_door_at_zero`, `t₁ ≡ 0`, `S ≡ 0`.)

**⟦DISCHARGED IN THIS COMPOSITE⟧** — binders that appear in NEITHER statement below:

* `hrows` — the weighted seam-row family at `a2Mrow`, per character.  Gone via
  `M4RowsChiEnd.m4_hrowsSlot_at_door_end` (⟦D5⟧, the strict-pair re-cut).  Replaced by
  `hbase`, which asks strictly less on two axes (the relativized pair law; `hwin` absent).
* `henv` — the arithmetic `arcDen 12 H · a2DoorGrade ≤ RSbig j H`.  Gone via
  `M4ArithPage.m4_arith_henv` at `RSbig := fun _ H => RSanDoor H`, under `harith`.
* ⟦gate 4⟧ — `∀ j H, doorRowFloor M ≤ j →`
  `m4ChiRowGraded M (fun _ H => RSanDoor H) j H ≤ RSanDoor H`.
  Gone via `M4ArithPage.m4_arith_gate4`: UNCONDITIONAL, no hypothesis at all.
* ⟦the ceiling⟧ — `M4SecondRoad.m4_second_road_rs_ceiling`'s demand
  `96(1+2π)²·strataResidual H²·(108/5·RSanDoor H) ≤ δ₀²`.  Gone via
  `M4ArithPage.m4_arith_rs_ceiling_met`, from `hδ₀` and `hHreg` alone.
* `hband` — the `T₀`-band per character.  Carried by
  `m4_socket_discharged_conditional` (§3) and GONE from `m4_socket_discharged_bandfree`
  (§4), where it is discharged by `M4T0DatumDischarge.m4_hT0band_at_door_discharged` and
  replaced by `DoorBandBase` (§2, nine fields) plus the supplier's own `∃C' ∃x₀` threshold
  and the landed slot `MmuChiRate`.

## ⟦WHAT THE `∃C' ∃x₀` IN §4 IS, AND WHY IT SITS WHERE IT SITS⟧

`m4_hT0band_at_door_discharged` produces its constant `C'` and base threshold `x₀` AFTER the
covering window `[P, Q]` is fixed, and the door's window is `[calP (Adoor M) (3072M) 1,
calQK (Adoor M) (3072M) M 2]` — a function of `M`.  So `C'` and `x₀` depend on `M` and cannot
be hoisted past it.  §4 therefore reads `∀ R M, 1 ≤ M → ∃ C' x₀, 0 < C' ∧ …`: the honest
"there is a threshold beyond which" shape, with the threshold VISIBLE in `DoorBandBase.x₀_le`
and the grade fit VISIBLE in `DoorBandBase.grade`.  Nothing is absorbed into an `∃`.

## ⟦THE LOG SCALES⟧

Unchanged from the two halves and never conflated here: `arcDen 12 H = (log H)¹²` (the
`φ(q)` ledger, never evaluated), `loglog H` (the `H`-side scale), `loglog X` at the socket's
own base `X = A + s`, `Nat.log 2` (the dyadic index and ⟦C1⟧'s anchor), and `√(log X_d)` (the
D5 reconciliation gates' fifth scale).  `DoorBandBase.qfit` reads `q ≤ (log X_d)^{10}` — a
BASE-side conductor gate, which is NOT `SocketBase`'s `q ≤ arcDen 12 H` (an `H`-side one);
the two are independent and both are carried.

⟦PURELY ADDITIVE⟧  No landed declaration is touched.  Every frozen shape — `ThmA2.a2Mrow`,
`M4ChiSummed.M4ChiSummedFreeRow`, `M4Assembly.SocketBase`/`DoorFuseFrame`,
`M4RowsChiEnd.DoorRowEndBase`, `M4ArithPage.DoorArithFrame`/`RSanDoor`, and
`M4SecondRoad.m4_second_road`'s ⟦gate 4⟧ and ceiling — is met, never adjusted.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE `_end` ASSEMBLY, AT THE GATED ARITHMETIC

⟦ASSEMBLY-ARITH⟧'s deliberately-omitted ten lines.  `M4ArithPage.m4_chiSummedFreeRow_of_doorArith`
composes `M4Assembly`'s D2 `hrows` slot with the gated socket; this composes ⟦D5⟧'s `_end`
slot with the same gated socket.  The two differ ONLY in which supplier fills the `hgrade`
argument of `m4_chiSummedFreeRowBig_of_doorGradeGated`; the arithmetic side is byte-identical. -/

/-- **⟦ITEM 11 AT THE DOOR'S ENVELOPE, `hrows`-FREE⟧**
(`m4_chiSummedFreeRow_of_doorArith_end`).  `M4ChiSummed.M4ChiSummedFreeRow` — ⟦item 11⟧ of
`M4SecondRoad.m4_second_road` — at the spliced grade
`m4ChiRowGraded M (fun _ H => RSanDoor H)`, from `hM`, `hb1`, `hc1`, `hframe`, `hbase`,
`hcap`, `hband`, `harith`.

Against `M4ArithPage.m4_chiSummedFreeRow_of_doorArith` this trades ONE binder for THREE:
`hrows` (the weighted row family, refuted at the door by
`M4Assembly.doorRows_global_hcoef_kills_block` when supplied from the global pair law) is
replaced by `hb1`/`hc1`/`hbase` — the door's two data `1`-bounds and ⟦D5⟧'s per-base gate
bundle, whose `coefWS` field is the STRICT relativized pair law. -/
theorem m4_chiSummedFreeRow_of_doorArith_end :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K : ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowEndBase M (A + s) j cU bU) →
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
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε cU bU t₁ K hM hb1 hc1 hframe hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_big
    (m4_chiSummedFreeRowBig_of_doorGradeGated (C₁ := C₁) (M₀ := M₀) ?_ (m4_arith_henv harith))
  intro H L q j A s hb
  obtain ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hsL⟩ := hb
  haveI : NeZero q := ⟨hq.ne'⟩
  have hbb : SocketBase R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hsL⟩
  have hF := hframe H L q j A s hbb
  exact m4_chiFreeRowSq_sum_at_door hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hslot R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hbb)
    (hband H L q j A s hbb) hF.gP1 hF.gRows ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-! ## §2 — THE `T₀`-BAND SLOT, DISCHARGED

`M4T0DatumDischarge.m4_hT0band_at_door_discharged`'s conclusion IS the assembly's `hband`
binder at `X_d := A + s`, `N := 2(A+s)`, `X := ((A+s : ℕ) : ℝ)` — the datum
`winCutH X_d (doorChiCoeff χ M)`, the phase `seamS0 (2X_d) X_d` and the bound
`t0BandB X_d (cfbC₁ X_d C₁) M₀` all match with no rewriting whatever.  Four of its fifteen
gates are discharged in-file (`(X_d : ℝ) = X` by `rfl`; `X_d ≤ N` and `N ≤ 2X_d` by the pin
`N = 2X_d`; `16 ≤ X_d` from `400 ≤ X_d`), two more by the door's own ladder
(`M4T0DatumDischarge.door_cover` / `door_window_bounds` at
`[P,Q] = [calP (Adoor M) (3072M) 1, calQK (Adoor M) (3072M) M 2]`), and the remaining eight
are `DoorBandBase` below — carried, per base, in the open. -/

/-- **THE PER-BASE GATE BUNDLE OF THE `T₀`-BAND SUPPLIER** (`DoorBandBase`) — exactly what
`M4T0DatumDischarge.m4_hT0band_at_door_discharged` asks at ONE socket base `X_d = A + s` and
modulus `q`, after the door's covering window and the pin `N = 2X_d` are supplied.

`x₀` and `C'` are the supplier's own existential witnesses (see the header, ⟦WHAT THE
`∃C' ∃x₀` IS⟧); `Aexp` is its saving parameter, carried symbolically. -/
structure DoorBandBase (x₀ : ℕ) (C' Aexp : ℝ) (M Xd q : ℕ) (C₁ M₀ : ℝ) : Prop where
  /-- `400 ≤ X_d` — the supplier's base floor (it also gives `16 ≤ X_d`). -/
  X400 : (400 : ℝ) ≤ ((Xd : ℕ) : ℝ)
  /-- `1 ≤ C₁` — the band constant's normalisation. -/
  C₁_one : (1 : ℝ) ≤ C₁
  /-- `x₀ ≤ X_d` — the supplier's threshold, VISIBLE. -/
  x₀_le : x₀ ≤ Xd
  /-- `q ≤ (log X_d)^{10}` — the BASE-side conductor gate.  **Not** `SocketBase`'s
  `q ≤ arcDen 12 H`, which is an `H`-side gate; the two are independent. -/
  qfit : (q : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (10 : ℕ)
  /-- The half-range mass gate, on `[X_d, 2X_d]`. -/
  gHalf : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    16 * Aexp * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)
  /-- The `O(1)`-range Rankin gate at the door's upper cutoff `Q₂`. -/
  gO1 : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    8 * Aexp * Real.log (Real.log (k : ℝ))
        * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.log (k : ℝ)
  /-- The covering-window gate at `[P₁, Q₂]`. -/
  gWin : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    Real.exp (2 * Real.exp 1
        * (Real.log (Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ))
            - Real.log (Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) + 25))
      ≤ (Real.log (k : ℝ)) ^ Aexp
  /-- The grade fit `8C' ≤ (log X_d)^{A − 1/2 + 1/1000}`. -/
  grade : 8 * C' ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
  /-- `cfb_t0band_supply_of_sup`'s own `hErr`. -/
  err : 4 * Real.log ((Xd : ℕ) : ℝ) ^ (-(1 : ℝ) / 2 + 1 / 1000)
    ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀)

/-- **⟦THE `hband` SLOT, MET⟧** (`m4_hband_at_door_slot`).  The statement's conclusion is
`M4Assembly.m4_chiSummedFreeRow_of_doorAssembly`'s `hband` binder VERBATIM — the compile is
the certificate of the byte-fit.  Its own residue is the landed slot `MmuChiRate`, the saving
parameter `Aexp > 0`, `1 ≤ M`, and `DoorBandBase` per base. -/
theorem m4_hband_at_door_slot (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp)
    (R : ChowlaRegime) (M : ℕ) (hM : 1 ≤ M) (C₁ M₀ : ℕ → ℝ) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      ((∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) := by
  obtain ⟨hP4, hPQ⟩ := door_window_bounds M hM
  obtain ⟨C', x₀, hC'pos, hband⟩ := m4_hT0band_at_door_discharged hMmu Aexp hAexp
    (calP (Adoor M) (3072 * M) 1) (calQK (Adoor M) (3072 * M) M 2) hP4 hPQ
  obtain ⟨hcovP, hcovQ⟩ := door_cover M hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro hgates H L q j A s hb χ
  have hq : 0 < q := hb.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hgates H L q j A s hb
  have h16 : 16 ≤ A + s := by
    have h400 : (400 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := hD.X400
    have : (16 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by linarith
    exact_mod_cast this
  exact hband q χ M (A + s) (2 * (A + s)) rfl hD.X400 (by omega) le_rfl hD.C₁_one
    hD.x₀_le h16 hD.qfit hcovP hcovQ hD.gHalf hD.gO1 hD.gWin hD.grade hD.err

/-! ## §3 — ⟦THE COMPOSITE⟧: THE SOCKET DISCHARGED, CONDITIONALLY

The three things `M4SecondRoad.m4_second_road` asks of the door's row grade — ⟦item 11⟧,
⟦gate 4⟧, and the ceiling — at ONE hypothesis set, with `hrows` and `henv` GONE. -/

/-- **⟦A4 — THE SOCKET, DISCHARGED IN ITS HONEST CONDITIONAL FORM⟧**
(`m4_socket_discharged_conditional`).  At `RS := m4ChiRowGraded M (fun _ H => RSanDoor H)`:

⟦i⟧ `M4ChiSummed.M4ChiSummedFreeRow R M RS` — ⟦item 11⟧, the analytic slot of `m4_second_road`;
⟦ii⟧ `∀ j H, doorRowFloor M ≤ j → RS j H ≤ RSanDoor H` — ⟦gate 4⟧ at `j₀ = doorRowFloor M`,
  `RSan = RSanDoor`;
⟦iii⟧ `∀ H ∈ [R.Hlo, R.Hhi], 96(1+2π)²·strataResidual H²·(108/5·RSanDoor H) ≤ δ₀²` — the
  demand of `M4SecondRoad.m4_second_road_rs_ceiling`, byte for byte.

THE COMPLETE HYPOTHESIS LIST (the module header groups these by supplier-status):
`hM`, `hδ₀`, `hHreg`, `hb1`, `hc1`, `hframe`, `hbase`, `hcap`, `hband`, `harith`.

⟦GONE FROM THIS STATEMENT⟧ `hrows` (D5's `_end` re-cut), `henv` (the arithmetic page),
⟦gate 4⟧ (unconditional) and the ceiling (from `hδ₀`+`hHreg` alone).  ⟦CARRIED⟧ `hcap` — the
A3 capstone family; supplier `M4RowsChi.m4_rowChi_capstone`, residue in the module header. -/
theorem m4_socket_discharged_conditional :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
        1 ≤ M → 2 / 10 ^ 49 ≤ δ₀ →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
        (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowEndBase M (A + s) j cU bU) →
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
  obtain ⟨Ct, Cp, hCt, hCp, hitem11⟩ := m4_chiSummedFreeRow_of_doorArith_end
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε cU bU t₁ K δ₀ hM hδ₀ hHreg hb1 hc1 hframe hbase hcap hband harith
  refine ⟨hitem11 R M C₁ M₀ ε cU bU t₁ K hM hb1 hc1 hframe hbase hcap hband harith,
    m4_arith_gate4 M, ?_⟩
  intro H hlo hhi
  obtain ⟨hL0, hlam⟩ := hHreg H hlo hhi
  exact m4_arith_rs_ceiling_met hδ₀ hL0 hlam

/-! ## §4 — THE SAME, WITH THE `T₀`-BAND GONE

§3 with `hband` supplied by §2.  `C'` and `x₀` are the band supplier's own witnesses at the
door's covering window, so they sit inside the `∀ R M` prefix (header, ⟦WHAT THE `∃C' ∃x₀`
IS⟧).  The landed slot `MmuChiRate` and the saving parameter `Aexp` ride as hypotheses of the
theorem, in the open. -/

/-- **⟦A4 — THE SOCKET, DISCHARGED, `T₀`-BAND INCLUDED⟧**
(`m4_socket_discharged_bandfree`).  §3's three conjuncts with `hband` REPLACED by
`DoorBandBase` at every base — eight named fields, no analytic content hidden.

THE COMPLETE HYPOTHESIS LIST: `hMmu : MmuChiRate` (the landed twisted-`μ` rate slot),
`Aexp > 0`; then per instance `hM`, `hδ₀`, `hHreg`, `hb1`, `hc1`, `hframe`, `hbase`, `hcap`,
`hbandbase`, `harith`.

⟦GONE FROM THIS STATEMENT⟧ `hrows`, `henv`, ⟦gate 4⟧, the ceiling, and `hband`.
⟦CARRIED⟧ `hcap` alone among the analytic slots — everything else is a frame, a datum bound,
or a regime fact. -/
theorem m4_socket_discharged_bandfree (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
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
              DoorRowEndBase M (A + s) j cU bU) →
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
  obtain ⟨Ct, Cp, hCt, hCp, hcomp⟩ := m4_socket_discharged_conditional
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ := m4_hband_at_door_slot hMmu Aexp hAexp R M hM C₁ M₀
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact hcomp R M C₁ M₀ ε cU bU t₁ K δ₀ hM hδ₀ hHreg hb1 hc1 hframe hbase hcap
    (hbandslot hbandbase) harith

end Salt.MR
