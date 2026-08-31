/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.V7Headline
import Salt.MR.BandRatedSocket

/-!
# `V7Rated` — R-1 Wave 1: the V7 rethread onto the RATED socket

Authority: the helm's R-1 Wave 1 commission brief (Fable, 2026-08-30, in the private record).
Released by ruling x's condition on QUEUE P2 item 6's 2(b) receipt.

The landed headline `V7Headline.logChowla2_ineffective_v7_ksarm_g0` consumes the OLD socket
through a `Kvt : ℕ → ℕ → ℝ` Skolem FUNCTION and carries the `K_vt` cushion as a CALLER-FACING
HYPOTHESIS, evaluated at `Qm = ⌈arcDen 12 R.Hhi⌉₊` — an argument that grows with the same `H₊`
that funds the budget, which is why the cushion was unprovable there (the "headroom is an
exponent" refutation, `arc.md` §4).  `BandRatedSocket.cofkL_capFreeFloor_at_socket_rated`'s
`Kvt` is ONE symbolic nonnegative real with **no dependence on `H₊` and no `Qm` evaluation
point**: an `H₊`-independent real against a budget `log H₊/4` that the chain's own regime choice
drives to infinity is a different problem — **the chain can pay it itself**.

## The five nodes (commission §2)

* **N0** (`cofkL_capFreeFloor_at_socket_rated_uniform`) — the `Kvt`-uniformity hoist:
  `∀ K, ∃ Z δ Kvt` → `∃ Z δ Kvt, ∀ K`.  The landed socket's witnesses come from
  `capFreeFloor3_pieceDatum_arcDen_rated` applied to NO arguments (`BandRatedSocket.lean:304`),
  so the `(K : ℕ)` binder is vacuous over the existentials; same proof, `intro K` moved after
  the `refine`.
* **N1** (`armVt` + `cofkR_cushion_of_armVt`) — the EIGHTH `max` arm and the cushion's
  discharge: at `armVt Kvt = max 162 (log (1 + Kvt)) ≤ A` the cushion inequality is PROVED,
  not assumed — `32·Kvt ≤ e^A·e^{2.2A}/8` (exp-beats-linear) and the `flatDoorM` debit is
  linear in `A` against the exponential budget `e^{3.2A} ≤ log H₋ ≤ log H₊`.
* **N1b** (`cofkR_cofactorSupply_L_gk_rated`) — the wave's cost centre: the SIBLING of
  `RegisterRepair.cofkR_cofactorSupply_L_gk` on the rated socket.  Four Skolem REALS instead
  of three-plus-a-function; the cushion carries NO evaluation point.  Body verbatim from the
  landed name apart from four mechanical edits (the socket obtain, the dead `hqQm`, and the
  floor application).
* **N2** (`logChowla2_v7_rated`) — the headline: the ksarm spine reproved on the rated
  supplier, the `A`-mint grown by the eighth arm, the cushion DISCHARGED inside, `g ≡ 0`
  as in `V7Headline`.  **The `Kvt` binder and the cushion arrow leave the statement.**
* **N5** (`logChowla2_ineffective_v7_ksarm_g0_of_rated`) — the no-trade receipt: the landed
  `_g0` statement reproved FROM the new headline at `Kvt := fun _ _ => 0`, tied to the landed
  declaration by the `example` beneath it, so "derivable-from-stronger" is a kernel fact.

⛔ SIBLINGS, never edits: `cofkL_capFreeFloor_at_socket_rated`, `cofkR_cofactorSupply_L_gk`,
`logChowla2_ineffective_v7_ksarm`, `logChowla2_ineffective_v7_ksarm_g0` and every parent are
byte-untouched and remain citable.  Scope precision (commission §0): `Qm` is gone from the
**V7 live path**, not "the whole chain" — `cofkL_cofactorSupply_L_gk_of_bulk`
(`CofactorBulk.lean:363`) still consumes the old socket, off-path, untouched here.
-/

noncomputable section

namespace Salt.MR

/-! ## §1 — N0: the `Kvt`-uniformity hoist at the rated socket -/

section SocketUniform

open Finset Complex DirichletCharacter Salt.SW Salt.Entropy.Chowla

set_option maxHeartbeats 1000000 in
-- same elaboration load as the landed socket: the arc-range floor's eight-binder
-- instantiation in one `exact`
/-- **⟦THE RATED SOCKET, `K`-UNIFORM⟧** (`cofkL_capFreeFloor_at_socket_rated_uniform`).
`BandRatedSocket.cofkL_capFreeFloor_at_socket_rated` with the `∃ Z δ Kvt` hoisted over the
lever: ONE triple of witnesses serving every `K`.  The hoist is free because the landed
socket's witnesses come from `capFreeFloor3_pieceDatum_arcDen_rated` applied to no arguments
(`BandRatedSocket.lean:304`) — the `(K : ℕ)` binder is vacuous over the existentials.  Proof
verbatim from the landed name with `intro K` moved after the `refine`. -/
theorem cofkL_capFreeFloor_at_socket_rated_uniform :
    ∃ Z δ Kvt : ℝ, 1 ≤ Z ∧ 0 < δ ∧ 0 ≤ Kvt ∧
      ∀ (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} (χ : DirichletCharacter ℂ q),
        SocketBaseL R M H L q j A s → 1 ≤ M →
        (1 : ℝ) / 500 ≤ (R.eps : ℝ) →
        (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        32 * Kvt + 32 * (2 * Real.log (M : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
        ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
            (calQK (AdoorL M) (s13GK K M) M)) (((A + s : ℕ)) : ℝ) := by
  obtain ⟨Z, δ, Kvt, hZ, hδ, hK0, hK⟩ := capFreeFloor3_pieceDatum_arcDen_rated
  refine ⟨Z, δ, Kvt, hZ, hδ, hK0, ?_⟩
  intro K R M H L q j A s χ hb hM hε hlo hcush 𝒥 h𝒥
  have hq0 : 0 < q := hb.2.2.2.1
  haveI : NeZero q := ⟨by omega⟩
  have h1 : R.Hlo ≤ H := hb.1
  have h2 : H ≤ R.Hhi := hb.2.1
  have harc : (q : ℝ) ≤ arcDen 12 H := hb.2.2.2.2.1
  -- ⟦the design floor⟧
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hH4 : (4000000 : ℝ) ≤ (H : ℝ) := by linarith
  have hlogH : (14 : ℝ) ≤ Real.log (H : ℝ) := cofk_log_big hH4
  have hlogHe : Real.exp 1 ≤ Real.log (H : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  -- ⟦`H₊ ≥ 10^14`⟧
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hlogHlo : (14 : ℝ) ≤ Real.log (R.Hlo : ℝ) := cofk_log_big hHlo4
  have hexp : Real.exp (518 : ℝ) ≤ Real.log (R.Hlo : ℝ) := by
    have h := Real.exp_le_exp.mpr hlo
    rwa [Real.exp_log (by linarith)] at h
  have hquart : (10 : ℝ) ^ 8 ≤ Real.exp (518 : ℝ) := by
    have h := cofk_exp_quartic (u := (518 : ℝ)) (by norm_num)
    have hnum : (290029400 : ℝ) ≤ (1 + (518 : ℝ) / 4) ^ 4 := by norm_num
    linarith
  have hlogHlo8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hlo : ℝ) := by linarith
  have hlogmono : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hHloH
  have hlogHhi : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) :=
    Real.log_le_log (by linarith) hHHhi
  have hLH8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hhi : ℝ) := by linarith
  have hHhi14 : (10 : ℝ) ^ 14 ≤ (R.Hhi : ℝ) := by
    have hlogle : Real.log ((10 : ℝ) ^ 14) ≤ Real.log (R.Hhi : ℝ) := by
      rw [show ((10 : ℝ) ^ 14) = (10 : ℝ) ^ (14 : ℕ) by norm_num, Real.log_pow]
      push_cast
      linarith [cofk_log_ten_le, hLH8]
    have h2' := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log (by positivity), Real.exp_log hHhi0] at h2'
  -- ⟦the scale gate, the debit page, the threshold⟧
  have hXee : Real.exp (Real.exp 1) ≤ (((A + s : ℕ)) : ℝ) :=
    cofkL_X_ge_expexp hb hε hHhi14 hH4
  have hgate : 32 * diskConst q / goldenL1 q ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    cofkL_scale_gate_at_socket hb hε hlo harc
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hD0 : (0 : ℝ) ≤ 2 * Real.log (M : ℝ) + Real.log 4 + 50 := by
    have h1' : (0 : ℝ) ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
    have h2' : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hdebit := cofkL_debit_bound K M (((A + s : ℕ)) : ℝ) hM 𝒥 h𝒥
  have hthr := cofkL_threshold_at_socket_rated (Kvt := Kvt)
    (D := 2 * Real.log (M : ℝ) + Real.log 4 + 50) hb hε hlo hcush
  exact hK q H χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 𝒥
    (((A + s : ℕ)) : ℝ) (2 * Real.log (M : ℝ) + Real.log 4 + 50)
    hlogHe harc hXee hD0 hgate hdebit hthr

end SocketUniform

/-! ## §2 — N1: the eighth arm, and the cushion's discharge -/

section RatedSupply

open Salt.Entropy.Chowla

/-- **⟦THE EIGHTH ARM⟧** (`armVt`).  The design constant's slot for the rated socket's floor
constant: `armVt Kvt = max 162 (log (1 + Kvt))`.  The `162` keeps the flat design floor
independent of `Kvt`'s size; the logarithmic half is what pays `32·Kvt` out of the exponential
budget.  `Kvt ≥ 0` is exported by the rated socket, so `1 + Kvt > 0` and the `log` is
well-grounded. -/
def armVt (Kvt : ℝ) : ℝ := max 162 (Real.log (1 + Kvt))

/-- **⟦THE CUSHION, DISCHARGED AT THE ARM⟧** (`cofkR_cushion_of_armVt`).  At any design
constant `A` above the eighth arm, the `K_vt` cushion is a THEOREM of the regime's own
exports: `A ≥ log(1+Kvt)` gives `32·Kvt ≤ e^A·e^{2.2A}/8 = e^{3.2A}/8` (exp-beats-linear at
`e^{2.2A} ≥ 256`), the `flatDoorM` debit is linear (`log(flatDoorM A) ≤ 1.6A`) against the
same `e^{3.2A}/8`, and `e^{3.2A} ≤ log H₋ ≤ log H₊` closes.  ⭐ SPEND NOTHING ON GRADE: every
numeral here is crude on purpose — the budget clears by orders of magnitude. -/
theorem cofkR_cushion_of_armVt {Kvt A : ℝ} (R : ChowlaRegime)
    (hKvt0 : 0 ≤ Kvt) (harm : armVt Kvt ≤ A)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ)) :
    32 * Kvt + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
      ≤ Real.log ((R.Hhi : ℕ) : ℝ) / 4 := by
  have hA162 : (162 : ℝ) ≤ A :=
    le_trans (show (162 : ℝ) ≤ armVt Kvt from le_max_left _ _) harm
  have hAK : Real.log (1 + Kvt) ≤ A :=
    le_trans (show Real.log (1 + Kvt) ≤ armVt Kvt from le_max_right _ _) harm
  have h1K : (0 : ℝ) < 1 + Kvt := by linarith
  -- ⟦the `32·Kvt` half: exp beats linear⟧
  have hKexp : 1 + Kvt ≤ Real.exp A := by
    have h := Real.exp_le_exp.mpr hAK
    rwa [Real.exp_log h1K] at h
  have hsplit : Real.exp (3.2 * A) = Real.exp A * Real.exp (2.2 * A) := by
    rw [← Real.exp_add]; congr 1; ring
  have h22 : (256 : ℝ) ≤ Real.exp (2.2 * A) := by
    linarith [Real.add_one_le_exp (2.2 * A)]
  have hKhalf : 32 * Kvt ≤ Real.exp (3.2 * A) / 8 := by
    have hmul : Real.exp A * 256 ≤ Real.exp A * Real.exp (2.2 * A) :=
      mul_le_mul_of_nonneg_left h22 (Real.exp_pos A).le
    rw [hsplit]
    linarith [hKexp, hmul, (Real.exp_pos A).le]
  -- ⟦the debit half: linear in `A` against the exponential budget⟧
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA26
  have hM1R : (1 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := by exact_mod_cast hM1
  have hMle : ((flatDoorM A : ℕ) : ℝ) ≤ Real.exp (3.2 * A / 2) := by
    have h := flatDoorM_le A
    have hE0 : (0 : ℝ) < Real.exp (3.2 * A / 2) := Real.exp_pos _
    linarith
  have hlogM : Real.log ((flatDoorM A : ℕ) : ℝ) ≤ 3.2 * A / 2 := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < ((flatDoorM A : ℕ) : ℝ)) hMle
    rwa [Real.log_exp] at h
  have hlog4 : Real.log 4 ≤ 4 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
  have hlog40 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hquart := flat_exp_ge_quartic (y := 3.2 * A) (by linarith)
  have hDhalf : 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
      ≤ Real.exp (3.2 * A) / 8 := by
    -- `8·32·(3.2A + 54) ≤ (3.2A)⁴/256` at `A ≥ 162`: quartic beats linear with orders of room
    have hy518 : (518 : ℝ) ≤ 3.2 * A := by linarith
    have hy2 : (518 : ℝ) * (3.2 * A) ≤ (3.2 * A) ^ 2 := by nlinarith
    have hy4 : (518 : ℝ) ^ 2 * (3.2 * A) ^ 2 ≤ (3.2 * A) ^ 4 := by
      nlinarith [hy2, sq_nonneg (3.2 * A)]
    nlinarith [hquart, hlogM, hlog4, hy518, hy2, hy4]
  -- ⟦the close: the budget is the regime's own export⟧
  have hHlo0 : (0 : ℝ) < ((R.Hlo : ℕ) : ℝ) := by
    have h : (4000000 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast R.hHlo_floor
    linarith
  have hHloHhi : Real.log ((R.Hlo : ℕ) : ℝ) ≤ Real.log ((R.Hhi : ℕ) : ℝ) :=
    Real.log_le_log hHlo0 (by exact_mod_cast R.hHlohi)
  linarith [hKhalf, hDhalf, hlo, hHloHhi]

/-! ## §3 — N1b: the co-factor supply at the RATED socket

The SIBLING of `RegisterRepair.cofkR_cofactorSupply_L_gk` (⛔ sibling, never an edit — the
landed name stays byte-untouched and citable).  The refuter pass found the seam the freeze
missed: the ksarm spine has NO socket call; the socket is consumed at
`RegisterRepair.lean:490` INSIDE the supply theorem, whose STATEMENT hardcodes
`Kvt : ℕ → ℕ → ℝ` and the `⌈arcDen 12 R.Hhi⌉₊` cushion.  This sibling rethreads exactly that:
`Kvt : ℝ` in the `∃`-prefix, the cushion with NO evaluation point.  Body verbatim from the
landed name apart from FOUR mechanical edits: (i) the `choose … using
cofkL_capFreeFloor_at_socket` becomes an `obtain` from the `K`-uniform rated socket (`Z`, `δ`
discarded); (ii) the `refine` passes the plain real; (iii) the dead `hqQm` line is deleted;
(iv) the floor application drops the `⌈arcDen 12 R.Hhi⌉₊` and `hqQm` arguments. -/

set_option maxHeartbeats 24000000 in
-- the ~35-binder instantiation of `m4_supplier_complete` and the seventeen discharged
-- conjuncts elaborate in ONE context; no tactic search happens at the top level (same cause
-- as the landed sibling)
/-- **⟦THE CO-FACTOR DEBT, DISCHARGED AT THE REPAIRED LADDER — RATED⟧**
(`cofkR_cofactorSupply_L_gk_rated`).  `RegisterRepair.cofkR_cofactorSupply_L_gk` with the
`K_vt` floor taken from the RATED socket: **four Skolem REALS instead of
three-plus-a-function**, and the ONE named cushion
`32·K_vt + 32·(2 log M + log 4 + 50) ≤ log H₊/4` carries **no evaluation point** — there is
no `Qm` anywhere in the statement.  `K_vt` here is an `H₊`-independent real (the rated
assembly's constant plus `max 0 (bandArcConst Z δ)`), which is what lets the V7 chain pay the
cushion itself (`cofkR_cushion_of_armVt`). -/
theorem cofkR_cofactorSupply_L_gk_rated :
    ∃ (Xsk Y0 Kvt Cb : ℝ),
      0 < Xsk ∧ pin2Gate ≤ Y0 ∧ 0 ≤ Kvt ∧ 0 ≤ Cb ∧
      ∀ (K : ℕ) (Cq : ℝ) (R : ChowlaRegime) (M : ℕ), 1 ≤ M → 0 < Cq →
        (1 : ℝ) / 500 ≤ (R.eps : ℝ) →
        (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        loglogFloor50 ≤ R.Hlo →
        cofkRThr Cq Cb Xsk Y0 ≤ Real.log (R.Hlo : ℝ) →
        32 * Kvt + 32 * (2 * Real.log (M : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
        S16CofactorSupply_L_gk K Cq R M := by
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  obtain ⟨Y0, hY0pin, hfarclose⟩ := farErr34_local_closes
  obtain ⟨_Z, _δ, Kvt, _, _, hKvt0, hKvt⟩ := cofkL_capFreeFloor_at_socket_rated_uniform
  obtain ⟨Cb, hCb0, hCbound⟩ := exists_shortIntervalDatum
  refine ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, ?_⟩
  intro K Cq R M hM hCq hε hlo hfl hgate hcush H Lw q j A s hb T hTlo hThi
  have hq0 : 0 < q := hb.2.2.2.1
  haveI : NeZero q := ⟨by omega⟩
  have hbb : SocketBase R M H Lw q j A s := socketBase_of_socketBaseL hM hb
  obtain ⟨hH4, hHhi14⟩ := cofkL_socket_floors hb hlo
  -- ⟦THE SOCKET'S OWN SCALE FACTS⟧
  have h2j0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hAs1 : 0 < A + s := by have := hb.2.2.2.2.2.2.2.1; omega
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs1
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hAsR h2j0) hTlo
  have hTflo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ 2 * T := by linarith
  have hmu2000 : (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := s13CapGrid_mu_2000 hfl hbb
  have hLam : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    s13CapGrid_Lambda_lo hfl hbb
  have hmuF : Real.log (R.Hhi : ℝ) - 14 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    cofkL_mu_floor hb hε hHhi14 hH4
  obtain ⟨-, -, hTpos, hlogT⟩ := capfloor_core hfl hbb (Nat.le_add_right A s) hTflo
  have hPQ : s13BandP (A + s) ≤ s13BandQ (A + s) := s13CapGrid_P_le_Q hmu2000 hLam
  have hQpos : 0 < s13BandQ (A + s) := s13CapGrid_Q_pos hmu2000
  have hfloorχ : ∀ χ : DirichletCharacter ℂ q, ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M)) (((A + s : ℕ)) : ℝ) :=
    fun χ => hKvt K χ hb hM hε hlo hcush
  -- ⟦THE BLOCK SCALE, NAMED ONCE⟧
  obtain ⟨Xd, hXd⟩ : ∃ n : ℕ, A + s = n := ⟨A + s, rfl⟩
  rw [hXd] at hmu2000 hLam hmuF hPQ hQpos hfloorχ hTflo hThi hlogT hAsR ⊢
  -- ⟦THE SCALE ARITHMETIC⟧
  have hLg0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hLgexp : Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ))) = Real.log ((Xd : ℕ) : ℝ) :=
    Real.exp_log hLg0
  have h21 : (10 : ℝ) ^ (21 : ℕ) = 1000000000000000000000 := by norm_num
  rw [h21] at hLam
  have hLg166 : Real.exp 166 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h := Real.exp_le_exp.mpr (show (166 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) by
      linarith)
    rwa [hLgexp] at h
  have hexp165 : (2 : ℝ) ≤ Real.exp 165 := by linarith [Real.add_one_le_exp (165 : ℝ)]
  have hexp166 : Real.exp 166 = Real.exp 1 * Real.exp 165 := by rw [← Real.exp_add]; norm_num
  have he27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hball : 2 * Real.exp 165 + 2 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    nlinarith [hLg166, hexp166, hexp165, he27]
  have hLgbig : (10 : ℝ) ^ 6 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h : (10 : ℝ) ^ 6 ≤ Real.exp 166 := by
      have h1 : (1 : ℝ) + 41.5 ≤ Real.exp 41.5 := by
        linarith [Real.add_one_le_exp (41.5 : ℝ)]
      have h2 : Real.exp 41.5 * Real.exp 41.5 = Real.exp 83 := by
        rw [← Real.exp_add]; norm_num
      have h3 : Real.exp 83 * Real.exp 83 = Real.exp 166 := by rw [← Real.exp_add]; norm_num
      have h4 : (1806 : ℝ) ≤ Real.exp 83 := by nlinarith [h1, h2]
      nlinarith [h3, h4]
    linarith
  -- ⟦THE THRESHOLD, READ AT THE SOCKET⟧
  have hHloHhi : Real.log (R.Hlo : ℝ) ≤ Real.log (R.Hhi : ℝ) := by
    have h1 : R.Hlo ≤ H := hb.1
    have h2 : H ≤ R.Hhi := hb.2.1
    have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
    have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
    have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
    exact Real.log_le_log (by linarith) (by linarith)
  have hthrLL : cofkRThr Cq Cb Xsk Y0 - 14
      ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by linarith
  have hZ1 : (1 : ℝ) ≤ 1 + Cq + cofkRConst Cb := by
    linarith [cofkRConst_pos hCb0]
  have hlogZ0 : (0 : ℝ) ≤ Real.log (1 + Cq + cofkRConst Cb) := Real.log_nonneg hZ1
  have hY00 : (0 : ℝ) < Y0 := lt_of_lt_of_le pin2Gate_pos hY0pin
  have hthrpieces : Xsk ≤ cofkRThr Cq Cb Xsk Y0 ∧ Y0 ≤ cofkRThr Cq Cb Xsk Y0 := by
    rw [cofkRThr]
    constructor <;> nlinarith [hlogZ0, hY00, hXsk0]
  -- `log X ≥ (loglog X)²/4`, the one quadratic the constant-absorption uses
  have hquad : Real.log (Real.log ((Xd : ℕ) : ℝ)) ^ 2 / 4 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h1 : 1 + Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2
        ≤ Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2) := by
      linarith [Real.add_one_le_exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2)]
    have h2 : Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2)
        * Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2)
        = Real.log ((Xd : ℕ) : ℝ) := by
      rw [← Real.exp_add, show Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2
        + Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2
        = Real.log (Real.log ((Xd : ℕ) : ℝ)) by ring, hLgexp]
    nlinarith [h1, h2, hLam]
  have habs : ∀ z : ℝ, 0 < z → z ≤ cofkRThr Cq Cb Xsk Y0 →
      Real.log z ≤ Real.log ((Xd : ℕ) : ℝ) / 4 := by
    intro z hz0 hzthr
    have hlz : Real.log z ≤ z := by
      linarith [Real.log_le_sub_one_of_pos hz0]
    have hthr14 : cofkRThr Cq Cb Xsk Y0 ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) + 14 := by
      linarith
    nlinarith [hquad, hLam, hlz, hzthr, hthr14]
  have hXskgate : Xsk ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) := by
    have h := habs Xsk hXsk0 hthrpieces.1
    have h2 := Real.exp_le_exp.mpr h
    rwa [Real.exp_log hXsk0] at h2
  have hY0gate : Y0 ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) := by
    have h := habs Y0 hY00 hthrpieces.2
    have h2 := Real.exp_le_exp.mpr h
    rwa [Real.exp_log hY00] at h2
  -- ⟦THE GRADING GATE⟧
  have hgradegate : 1728 * Cq * (4 * cofkRConst Cb) ^ 2
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (2 * theta293) := by
    have hθ300 : (1 : ℝ) / 300 ≤ theta293 := by
      have hpos : (0 : ℝ) < 32 * (3 * Real.exp 1 + 1) := by nlinarith
      rw [theta293, le_div_iff₀ hpos]
      nlinarith [Real.exp_one_lt_d9]
    have hpow : (Real.log ((Xd : ℕ) : ℝ)) ^ (2 * theta293)
        = Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) * (2 * theta293)) := by
      rw [Real.rpow_def_of_pos hLg0]
    have hstep : (6666 : ℝ) + 3 * Real.log (1 + Cq + cofkRConst Cb)
        ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) * (2 * theta293) := by
      have hLL0 : (0 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by linarith
      have h1 : Real.log (Real.log ((Xd : ℕ) : ℝ)) / 150
          ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) * (2 * theta293) := by
        nlinarith [hθ300, hLL0]
      have h2 : (10 : ℝ) ^ 6 + 450 * Real.log (1 + Cq + cofkRConst Cb) - 14
          ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by
        have := hthrLL
        rw [cofkRThr] at this
        linarith
      linarith
    have hZ3 : Real.exp ((6666 : ℝ) + 3 * Real.log (1 + Cq + cofkRConst Cb))
        = Real.exp 6666 * (1 + Cq + cofkRConst Cb) ^ 3 := by
      rw [Real.exp_add]
      congr 1
      rw [show (3 : ℝ) * Real.log (1 + Cq + cofkRConst Cb)
        = Real.log ((1 + Cq + cofkRConst Cb) ^ 3) by
          rw [Real.log_pow]; push_cast; ring]
      exact Real.exp_log (pow_pos (by linarith) 3)
    have hbig : Real.exp 6666 * (1 + Cq + cofkRConst Cb) ^ 3
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (2 * theta293) := by
      rw [hpow, ← hZ3]
      exact Real.exp_le_exp.mpr hstep
    have he6666 : (27648 : ℝ) ≤ Real.exp 6666 := by
      have h1 : (1 : ℝ) + 3333 ≤ Real.exp 3333 := by
        linarith [Real.add_one_le_exp (3333 : ℝ)]
      have h2 : Real.exp 3333 * Real.exp 3333 = Real.exp 6666 := by
        rw [← Real.exp_add]; norm_num
      nlinarith
    have hRc0 : (0 : ℝ) < cofkRConst Cb := cofkRConst_pos hCb0
    have hCqZ : Cq ≤ 1 + Cq + cofkRConst Cb := by linarith
    have hRZ : cofkRConst Cb ^ 2 ≤ (1 + Cq + cofkRConst Cb) ^ 2 := by nlinarith
    have hcube : Cq * cofkRConst Cb ^ 2 ≤ (1 + Cq + cofkRConst Cb) ^ 3 := by
      nlinarith [hCqZ, hRZ, hCq.le, hRc0, hZ1]
    have hid : 1728 * Cq * (4 * cofkRConst Cb) ^ 2 = 27648 * (Cq * cofkRConst Cb ^ 2) := by
      ring
    rw [hid]
    have hZ0 : (0 : ℝ) ≤ (1 + Cq + cofkRConst Cb) ^ 3 := pow_nonneg (by linarith) 3
    calc 27648 * (Cq * cofkRConst Cb ^ 2)
        ≤ 27648 * (1 + Cq + cofkRConst Cb) ^ 3 := by linarith
      _ ≤ Real.exp 6666 * (1 + Cq + cofkRConst Cb) ^ 3 := by nlinarith [he6666, hZ0]
      _ ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (2 * theta293) := hbig
  -- ⟦THE BAND⟧
  have hθ0 : (0 : ℝ) < theta293 := theta293_pos
  have hθ32 : theta293 ≤ 1 / 32 := theta293_lt_one_div_32.le
  have hLX : Real.exp 1 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have hLe2 : Real.exp 2 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have hH1 : (1 : ℝ) ≤ H83 ((Xd : ℕ) : ℝ) theta293 := by
    rw [H83]; exact Real.one_le_rpow (by linarith) hθ0.le
  have hH0 : (0 : ℝ) < H83 ((Xd : ℕ) : ℝ) theta293 := by linarith
  have hPlow : P83 ((Xd : ℕ) : ℝ) theta293 ≤ ((s13BandP Xd : ℕ) : ℝ) := s13CapGrid_P_low Xd
  have hQhigh : ((s13BandQ Xd : ℕ) : ℝ) ≤ Q83 ((Xd : ℕ) : ℝ) := s13CapGrid_Q_high Xd
  have hQ1 : 1 ≤ s13BandQ Xd := hQpos
  have hP83pos : (0 : ℝ) < P83 ((Xd : ℕ) : ℝ) theta293 := by rw [P83]; exact Real.exp_pos _
  have hPexp : (2 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - theta293) := by
    have h1 : (Real.exp 1) ^ (1 - theta293)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - theta293) :=
      Real.rpow_le_rpow (Real.exp_pos 1).le hLX (by linarith)
    have h2 : (Real.exp 1) ^ (31 / 32 : ℝ) ≤ (Real.exp 1) ^ (1 - theta293) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : (Real.exp 1) ^ (31 / 32 : ℝ) = Real.exp (31 / 32) := Real.exp_one_rpow _
    have h4 := cofk_two_le_exp_31_32
    rw [h3] at h2
    linarith
  have hP83log : Real.log (P83 ((Xd : ℕ) : ℝ) theta293)
      = (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - theta293) := by rw [P83, Real.log_exp]
  have hP83ge : (3 : ℝ) ≤ P83 ((Xd : ℕ) : ℝ) theta293 := by
    rw [P83]
    have h1 : Real.exp 2 ≤ Real.exp ((Real.log ((Xd : ℕ) : ℝ)) ^ (1 - theta293)) :=
      Real.exp_le_exp.mpr hPexp
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    linarith
  have hP3R : (3 : ℝ) ≤ ((s13BandP Xd : ℕ) : ℝ) := by linarith
  have hP3 : 3 ≤ s13BandP Xd := by exact_mod_cast hP3R
  have hP1 : 1 ≤ s13BandP Xd := by omega
  have hlogP2 : (2 : ℝ) ≤ Real.log ((s13BandP Xd : ℕ) : ℝ) := by
    have h := Real.log_le_log hP83pos hPlow
    rw [hP83log] at h
    linarith
  have hQlog : Real.log ((s13BandQ Xd : ℕ) : ℝ)
      ≤ Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ)) :=
    log_le_of_le_Q83 hQ1 hQhigh
  have hQL : Real.log ((s13BandQ Xd : ℕ) : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have hdiv : Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ))
        ≤ Real.log ((Xd : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hRrad0 : (0 : ℝ) < seamRad ((Xd : ℕ) : ℝ) := by
    rw [seamRad]; exact Real.rpow_pos_of_pos hLg0 _
  -- ⟦CONJUNCTS 2 AND 3: THE `T`-WINDOW IS THE SOCKET'S OWN ARITHMETIC⟧
  have h2T0 : (0 : ℝ) < 2 * T := by linarith
  have hQT : ((s13BandQ Xd : ℕ) : ℝ) ≤ 2 * T := by
    have hQ0R : (0 : ℝ) < ((s13BandQ Xd : ℕ) : ℝ) := by exact_mod_cast hQpos
    have hstep : Real.log ((s13BandQ Xd : ℕ) : ℝ) ≤ Real.log (2 * T) := by
      have hdiv : Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ))
          ≤ Real.log ((Xd : ℕ) : ℝ) / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
        nlinarith
      linarith
    have h := Real.exp_le_exp.mpr hstep
    rwa [Real.exp_log hQ0R, Real.exp_log h2T0] at h
  have h30g : 30 * (Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ)))
      ≤ Real.log (2 * T) := by
    have hdiv : Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ))
        ≤ Real.log ((Xd : ℕ) : ℝ) / 60 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 60)]
      nlinarith
    linarith
  -- ⟦THE BLOCKS⟧
  have hBpos : ∀ v : ℕ, (0 : ℝ) < ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v
    rw [ramRbot]
    exact mul_pos hAsR (Real.exp_pos _)
  have hB34 : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4)
        ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    have hlow := cofkR_band_log_lower hH0 hQ1 hQhigh hLe2 hv
    have hid : (1 - 1 / Real.log (Real.log ((Xd : ℕ) : ℝ))) * Real.log ((Xd : ℕ) : ℝ)
        = Real.log ((Xd : ℕ) : ℝ)
          - (1 / Real.log (Real.log ((Xd : ℕ) : ℝ))) * Real.log ((Xd : ℕ) : ℝ) := by ring
    rw [hid] at hlow
    have hinv : (1 : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 4)]
      linarith
    have hstep : 3 * Real.log ((Xd : ℕ) : ℝ) / 4
        ≤ Real.log (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v) := by
      nlinarith [hlow, hinv, hLg0]
    have h := Real.exp_le_exp.mpr hstep
    rwa [Real.exp_log (hBpos v)] at h
  -- the three exponential comparisons every block fact below runs on
  have hehalf : (1 : ℝ) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) :=
    Real.one_le_exp (by linarith)
  have hequart : (1 : ℝ) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) :=
    Real.one_le_exp (by linarith)
  have hesplit : Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4)
      * Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)
      = Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have he2half : (2 : ℝ) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := by
    linarith [Real.add_one_le_exp (Real.log ((Xd : ℕ) : ℝ) / 2)]
  have he2quart : (2 : ℝ) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) := by
    linarith [Real.add_one_le_exp (Real.log ((Xd : ℕ) : ℝ) / 4)]
  have hquarthalf : Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4)
      ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := Real.exp_le_exp.mpr (by linarith)
  have hgap34 : Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) + 1
      ≤ Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
    nlinarith [hesplit, hehalf, he2quart]
  have hgapq : Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) + 1
      ≤ Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
    nlinarith [hesplit, hehalf, he2quart, hquarthalf]
  have hpinhalf : pin2Gate ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := by
    rw [pin2Gate]
    exact Real.exp_le_exp.mpr (by linarith)
  -- the landed band facts, at the repaired scale
  have hBX : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      2 * ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v ≤ ((Xd : ℕ) : ℝ) :=
    fun v hv => cofkL_two_ramRbot_le hH1 hlogP2 hv
  have hkth : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ballQuarterThreshold + 1 ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
    fun v hv => cofk_ballQuarter_at_band hH0 hQ1 hQhigh hball hv
  have hW5 : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      (5 : ℝ) ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
    fun v hv => cofkL_five_le_ramRbot (hkth v hv)
  have hC16 : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      18 + Real.log (Real.log ((Xd : ℕ) : ℝ))
          - Real.log (Real.log (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)) :=
    fun v hv => cofk_descent_at_band hH0 hQ1 hQhigh (by linarith) (by linarith) hv
  have hRradW : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      seamRad ((Xd : ℕ) : ℝ) ≤ Real.sqrt 2 * ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
    fun v hv => cofk_seamRad_at_band hH0 hQ1 hQhigh (by linarith) hv
  have hXskj : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Xsk ≤ Real.sqrt (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v) :=
    fun v hv => cofk_wideThreshold_at_band hH0 hQ1 hQhigh hLe2 hXskgate hv
  -- ⟦THE REPAIRED LADDER `D = ⌈log X⌉₊`⟧
  have hDge : Real.log ((Xd : ℕ) : ℝ) ≤ ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hDle : ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hLg0.le)
  have hDone : 1 ≤ ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ := by
    have h : (1 : ℝ) ≤ ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by linarith
    exact_mod_cast h
  have hWlow : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
            / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) :=
    fun v hv => cofkR_window_lower (by linarith) hDone hDle (hB34 v hv)
  have hWpos : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      (0 : ℝ) < ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by
    intro v hv; linarith [hWlow v hv, hehalf]
  have hlogW : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      1 / 2 * Real.log ((Xd : ℕ) : ℝ)
        ≤ Real.log (((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
            / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)) := by
    intro v hv
    have h := Real.log_le_log (Real.exp_pos (Real.log ((Xd : ℕ) : ℝ) / 2)) (hWlow v hv)
    rw [Real.log_exp] at h
    linarith only [h]
  have hWXle : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ≤ ((Xd : ℕ) : ℝ) := by
    intro v hv
    have h1 : (witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) ≤ witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
      Nat.div_le_self _ _
    have h1R : ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 := (witKk_cut (H := H83 ((Xd : ℕ) : ℝ) theta293) (Xd := Xd) (j := v)
      (by linarith [hW5 v hv])).1
    linarith [hBX v hv, hBpos v]
  -- ⟦THE WINDOW TOP⟧
  have hMtlow : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)
        ≤ ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
    intro v hv
    have h := (witMt_window (H := H83 ((Xd : ℕ) : ℝ) theta293) (Xd := Xd) (j := v)
      (by linarith [hW5 v hv])).1
    linarith [hB34 v hv, hgap34]
  have hMtX : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) ≤ 2 * ramRbot
        (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
    fun v hv => cofkL_Mt_le_two_ramRbot (hW5 v hv)
  have hlogMt : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      1 / 2 * Real.log ((Xd : ℕ) : ℝ)
        ≤ Real.log (((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)) := by
    intro v hv
    have h := Real.log_le_log (Real.exp_pos (Real.log ((Xd : ℕ) : ℝ) / 2)) (hMtlow v hv)
    rw [Real.log_exp] at h
    linarith only [h]
  have hlogB : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      1 / 2 * Real.log ((Xd : ℕ) : ℝ)
        ≤ Real.log (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v) := by
    intro v hv
    have h := Real.log_le_log (Real.exp_pos (3 * Real.log ((Xd : ℕ) : ℝ) / 4)) (hB34 v hv)
    rw [Real.log_exp] at h
    linarith only [h, hLg0]
  -- ⟦THE EXIT CHARGES, AT THE REPAIRED LADDER⟧
  have hpow0 : (0 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := Real.rpow_nonneg hLg0.le _
  have hcSq0 := cofk_cSq_pos
  have hS0 : (0 : ℝ) ≤ cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) :=
    mul_nonneg (cofkRSconst_pos hCb0).le hpow0
  have hSbd : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      cSq * caseASwide (1 / Real.exp 1) Cb
          (cofactorMfl ((Xd : ℕ) : ℝ) theta293
            ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
              / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ))
          ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
            / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
          (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v)
        + cSq * ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
      ≤ cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
    intro v hv
    have hW2 : (2 : ℝ) ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := le_trans he2half (hWlow v hv)
    have hcase := cofkR_caseASwide_priced hCb0 hW2 (hWXle v hv) hLe2 (by linarith)
      (hlogW v hv) (hlogB v hv)
    have hD4 : ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
      have h1 : ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hLg0 hDge (by norm_num)
      have h2 : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 4 : ℝ))
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith only [hLgbig])
          (by linarith only [rho293_le_seam])
      linarith only [h1, h2]
    have h1 := mul_le_mul_of_nonneg_left hcase hcSq0.le
    have h2 := mul_le_mul_of_nonneg_left hD4 hcSq0.le
    calc cSq * caseASwide (1 / Real.exp 1) Cb
            (cofactorMfl ((Xd : ℕ) : ℝ) theta293
              ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
                / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ))
            ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
              / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
            (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v)
          + cSq * ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
        ≤ cSq * ((3 * gradeAbsConstC (1 / Real.exp 1) Cb + 2 * farCStar2 + 8)
              * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
            + cSq * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by linarith only [h1, h2]
      _ = cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
          rw [cofkRSconst]; ring
  have hMfl0 : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      (0 : ℝ) ≤ cofactorMfl ((Xd : ℕ) : ℝ) theta293
        ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
          / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by
    intro v hv
    exact cofkR_mfl_nonneg (le_trans he2half (hWlow v hv)) (hWXle v hv) hLe2
      (hlogW v hv) (by linarith)
  -- ⟦THE FAR ARM AT EVERY BLOCK⟧
  have hfarb : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      farSupS34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad ((Xd : ℕ) : ℝ))
        ≤ 5 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
    intro v hv
    have hY0Mt : Y0 ≤ ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) :=
      le_trans hY0gate (le_trans hquarthalf (hMtlow v hv))
    have hB2 : (2 : ℝ) ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
      linarith [hW5 v hv]
    have hMt0 : (0 : ℝ) < ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith [hMtlow v hv, hehalf]
    have hlogMtle := Real.log_le_log hMt0 (hMtX v hv)
    have hkkhalf : ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v / 2
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith [cofkL_ramRbot_le_kk (hW5 v hv)]
    have hlogkk := Real.log_le_log (by linarith : (0 : ℝ)
      < ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v / 2) hkkhalf
    rw [Real.log_mul (by norm_num) (ne_of_gt (hBpos v))] at hlogMtle
    rw [Real.log_div (ne_of_gt (hBpos v)) (by norm_num)] at hlogkk
    have hlogBbig : 3 * Real.log 2 ≤ Real.log (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v) := by
      linarith only [hlogB v hv, Real.log_two_lt_d9, hLgbig]
    have hlogMt2kk : Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        ≤ 2 * Real.log ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith only [hlogMtle, hlogkk, hlogBbig]
    exact cofkR_farSup_priced (by linarith only [hLgbig]) (hfarclose _ _ hY0Mt hlogMt2kk)
      (hlogMt v hv)
  -- ⟦THE `R̄₀` CEILING⟧
  have hRbdU : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      cofactorRbdGen (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
          ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad ((Xd : ℕ) : ℝ))
        ≤ cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
    intro v hv
    rw [cofactorRbdGen, cofkRConst]
    have hmax : max (2 * (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)))
        (farSupS34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad ((Xd : ℕ) : ℝ)))
        ≤ (2 * cofkRSconst Cb + 5) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
      have hSP : (0 : ℝ) ≤ cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := hS0
      exact max_le (by linarith only [hpow0])
        (le_trans (hfarb v hv) (by linarith only [hSP]))
    linarith only [hmax]
  -- ⟦THE ENDPOINT CHARGE⟧
  have hLgleB : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.log ((Xd : ℕ) : ℝ) ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    have h1 : 1 + 3 * Real.log ((Xd : ℕ) : ℝ) / 8
        ≤ Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8) := by
      linarith [Real.add_one_le_exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)]
    have h2 : Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)
        * Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)
        = Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [hB34 v hv, h1, h2, hLg0]
  have hsr : seamRad ((Xd : ℕ) : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
    rw [seamRad]
    have h1 : (Real.log ((Xd : ℕ) : ℝ)) ^ ((1 : ℝ) / 46)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rwa [Real.rpow_one] at h1
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
    rwa [Real.sqrt_one] at h
  have hendGen : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      2 / ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        ≤ cofactorRbdGen (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
            ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
              (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
            (seamRad ((Xd : ℕ) : ℝ)) / 3 := by
    intro v hv
    have hMt0 : (0 : ℝ) < ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith [hMtlow v hv, hehalf]
    have hkk0 : (0 : ℝ) < Real.log ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      have h2 : (2 : ℝ) ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
        linarith only [cofkL_ramRbot_le_kk (hW5 v hv), hW5 v hv]
      exact Real.log_pos (by linarith only [h2])
    have hfar0 : (0 : ℝ) ≤ farErr34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ))) :=
      farErr34_nonneg hkk0 (Real.log_nonneg (by linarith [hMtlow v hv, he2half]))
        (Tstar2_pos hMt0).le
    have hchain : 2 / ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        ≤ farSupS34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad ((Xd : ℕ) : ℝ)) := by
      rw [farSupS34]
      have h1 : (2 : ℝ) / ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
          ≤ 2 / Real.log ((Xd : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hLg0 (hLgleB v hv)
      have h2 : (2 : ℝ) / Real.log ((Xd : ℕ) : ℝ) ≤ 2 / seamRad ((Xd : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hRrad0 hsr
      have hinv : (0 : ℝ) < (seamRad ((Xd : ℕ) : ℝ))⁻¹ := inv_pos.mpr hRrad0
      have h3 : (2 : ℝ) / seamRad ((Xd : ℕ) : ℝ)
          ≤ 2 * Real.sqrt 2 / seamRad ((Xd : ℕ) : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        nlinarith [hs2, hinv]
      linarith
    rw [cofactorRbdGen]
    have hfin := le_trans hchain
      (le_max_right (2 * (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)))
      (farSupS34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
        (seamRad ((Xd : ℕ) : ℝ))))
    linarith only [hfin]
  -- ⟦THE LADDER GATES⟧
  have hLg2leB : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.log ((Xd : ℕ) : ℝ) + 2 ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    have h1 : 1 + 3 * Real.log ((Xd : ℕ) : ℝ) / 8
        ≤ Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8) := by
      linarith [Real.add_one_le_exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)]
    have h2 : Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)
        * Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)
        = Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [hB34 v hv, h1, h2, hLgbig]
  have hDdk : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ ≤ witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    have hR : ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith only [hDle, hLg2leB v hv, cofkL_ramRbot_le_kk (hW5 v hv)]
    exact_mod_cast hR
  have hsqXa : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.sqrt (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v)
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
            / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by
    intro v hv
    have hBle : ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ)) := by
      rw [Real.exp_log hAsR]
      linarith only [hBX v hv, hBpos v]
    have hmono := Real.sqrt_le_sqrt hBle
    have hsq : Real.sqrt (Real.exp (Real.log ((Xd : ℕ) : ℝ)))
        = Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := by
      have hsplit2 : Real.exp (Real.log ((Xd : ℕ) : ℝ))
          = Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)
            * Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hsplit2, Real.sqrt_mul_self (Real.exp_pos _).le]
    rw [hsq] at hmono
    linarith only [hmono, hWlow v hv]
  have hpinW : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      pin2Gate ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) :=
    fun v hv => le_trans hpinhalf (hWlow v hv)
  have hXae : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.exp 1 ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    linarith only [hW5 v hv, Real.exp_one_lt_d9]
  -- ⟦THE TWO CONTOUR BOXES⟧
  have hTX : (2 : ℝ) * T ≤ ((Xd : ℕ) : ℝ) := hThi
  have hbox : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ∀ t : ℝ, |t| ≤ 2 * T →
        |t| + Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ))
          ≤ 3 * ((Xd : ℕ) : ℝ) := by
    intro v hv t ht
    exact cofkR_box_of_le (le_trans hpinhalf (hMtlow v hv))
      (by linarith only [hMtX v hv, hBX v hv]) (by linarith only [ht, hTX])
  have hboxw : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ∀ t : ℝ, |t| ≤ 2 * T → ∀ i : ℕ,
        ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
          / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ≤ (i : ℝ) →
          (i : ℝ) ≤ 2 * ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v →
            |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * ((Xd : ℕ) : ℝ) := by
    intro v hv t ht i hi1 hi2
    exact cofkR_box_of_le (le_trans (hpinW v hv) hi1)
      (by linarith only [hi2, hBX v hv]) (by linarith only [ht, hTX])
  -- ⟦`TLBlockGates34` AT THE WITNESS⟧
  have hlogLs0 : (0 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by linarith
  have hrp : (0 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg hLg0.le _
  have hp5 : (0 : ℝ) ≤ (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5 := pow_nonneg hlogLs0 5
  have hcq0 : (0 : ℝ) ≤ 420 * Real.log ((Xd : ℕ) : ℝ)
      * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5 := by
    have h1 : (0 : ℝ) ≤ 420 * Real.log ((Xd : ℕ) : ℝ) := by linarith
    exact mul_nonneg (mul_nonneg h1 hrp) hp5
  have hcqgate : 420 * Real.log ((Xd : ℕ) : ℝ)
        * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5
      ≤ (420 * Real.log ((Xd : ℕ) : ℝ)
          * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5)
        * (Real.log ((s13BandP Xd : ℕ) : ℝ)) ^ 2 := by
    have hsq : (1 : ℝ) ≤ (Real.log ((s13BandP Xd : ℕ) : ℝ)) ^ 2 := by nlinarith [hlogP2]
    nlinarith [hcq0, hsq]
  have hblk : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      TLBlockGates34 (420 * Real.log ((Xd : ℕ) : ℝ)
          * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5)
        (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (2 * Xd) Xd
        (witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
        (witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
        (2 * T) (Real.log ((Xd : ℕ) : ℝ)) (1 / Real.exp 1) Cb
        ((Xd : ℕ) : ℝ) theta293 (seamRad ((Xd : ℕ) : ℝ)) v := by
    intro v hv
    have hbaseQ : ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v ≤ s13BandQ Xd :=
      ramQbase_le_top hH0 hQ1 hPQ hv
    have hbase3 : 3 ≤ ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v :=
      le_trans hP3 (ramQbase_ge_bot _ _ _)
    have hb3R : (3 : ℝ)
        ≤ ((ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v : ℕ) : ℝ) := by
      exact_mod_cast hbase3
    have hblog0 : (0 : ℝ)
        < Real.log ((ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v : ℕ) : ℝ) :=
      Real.log_pos (by linarith only [hb3R])
    have hbQ : Real.log ((ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v : ℕ) : ℝ)
        ≤ Real.log ((s13BandQ Xd : ℕ) : ℝ) :=
      Real.log_le_log (by linarith only [hb3R]) (by exact_mod_cast hbaseQ)
    have h30 : (30 : ℝ) ≤ Real.log (2 * T)
        / Real.log ((ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v : ℕ) : ℝ) := by
      rw [le_div_iff₀ hblog0]
      linarith only [h30g, hbQ, hQlog, hblog0]
    exact tlBlockGates34_at_witness hH1 hP3 hlogP2 hQ1 hPQ hcq0 hv hQT h30 hQL hcqgate
      (by linarith only [hW5 v hv]) (hkth v hv) le_rfl (hBX v hv) (hC16 v hv) hRrad0
      (hRradW v hv)
  -- ⟦THE HEAD⟧
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hce : (1 : ℝ) / Real.exp 1 ≤ 1 / Real.exp 1 := le_refl _
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith [Real.exp_one_gt_d9])]
    linarith [Real.exp_one_gt_d9]
  -- ⟦THE EXIT⟧
  have hRb0 : (0 : ℝ) ≤ 4 * (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)) := by
    linarith only [mul_nonneg (cofkRConst_pos hCb0).le hpow0]
  refine ⟨seamRad ((Xd : ℕ) : ℝ),
    4 * (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)),
    4 * cofkRConst Cb, hRb0, le_of_eq (by ring), hgradegate, ?_⟩
  intro t₁ χ
  have hs := hsup q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M)
    (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd (s13BandP Xd) (s13BandQ Xd) 2 1
    (witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
    (witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
    (fun _ : ℕ => ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊)
    (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
    (420 * Real.log ((Xd : ℕ) : ℝ)
      * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5)
    (Real.log ((Xd : ℕ) : ℝ)) (1 / Real.exp 1) Cb ((Xd : ℕ) : ℝ) theta293
    (seamRad ((Xd : ℕ) : ℝ)) (2 * T) t₁
    (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)) (1 / Real.exp 1)
    (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
    hc0 hce hc1 hCb0 hCbound hP1 (le_refl 1) hRrad0 hθ0 hθ32 hLX hPlow hQhigh hPQ
    (hfloorχ χ) hblk hbox (fun _ _ => hDone) hDdk hXskj hsqXa hpinW hXae hMtX hBX hMfl0
    hboxw hS0 hSbd hendGen hRbdU
  have he : (2 : ℝ) ^ (2 : ℕ) * (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
      = 4 * (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)) := by norm_num
  rwa [he] at hs

end RatedSupply

/-! ## §4 — N2: the headline.  The cushion LEAVES the statement -/

section RatedHeadline

open Salt.Entropy.Chowla
open scoped BigOperators

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 3200000 in
-- Same cause as `…_ksarm`: the `∃`-prefix and the window discharges re-elaborate the
-- conclusion under the raised lever.
/-- **⟦THE RATED HEADLINE⟧** (`logChowla2_v7_rated`) — the ksarm spine reproved on the RATED
co-factor supply, at the exhibited caller `g ≡ 0`.  **The `Kvt` function binder and the
`K_vt` cushion arrow LEAVE the statement**: with the rated socket's `Kvt` one closed
`H₊`-independent real, the cushion is paid by the design constant's EIGHTH `max` arm
(`armVt Kvt`, discharged by `cofkR_cushion_of_armVt`), so the conclusion is
`¬ logChowla2Fails R.eps R.x R.ω` with NO caller-facing hypothesis.

⟦THE SURVIVING LIST⟧ outer hypotheses: NOTHING.  Inner: NOTHING.  This is the program's first
hypothesis-free headline: every rider of the v6/v7 chain — `cs`, `T₀`, `Ks`, `XCeil`, and now
the `K_vt` cushion — is discharged inside.

⟦THE SCOPE, STATED⟧ what the statement does and does not say, in its own bytes:

* the tolerance `ε` is OPAQUE and bounded only from BELOW — all that is exported is
  `1 / 500 ≤ ε` (with the regime's own `ε ≤ 1/2`).  The theorem is at one produced ε-FLOOR,
  not at every `ε`, and not at any named value;
* the window is `(x/ω, x]` weighted by `1/n` against `ε · log ω` (`logChowla2Fails`) — a
  windowed partial sum, not the full logarithmic average over `n ≤ x` against `log x`;
* the shift is `n + 1` (the `2` counts the factors `λ(n)·λ(n+1)`, not the shift);
* `ineffective` residue: the design constant `A` is produced by `Classical.choice` through
  the chain and carries Siegel's ineffective constant through its seventh arm
  (`16·log(1/Ks)/3`) and the rated floor constant through its eighth (`armVt Kvt`) — the
  residual ineffectivity prices SCALE-EXTRACTABILITY, not truth, and it sits in BOTH arms;
* nothing here bears on twin primes — the transport wall is untouched at this rung.

⟦KEPT, FROZEN⟧ the tower conjunct and the `loglog H₊ ≤ 2·e^{1.6A}` export are carried
verbatim from the parent (`V7Ks.lean:446-450`): the kernel census found zero live kernel
consumers either way, but `arc.md`'s erratum-(a) argument reads the second export off the
headline, and keeping both is what makes the parent's `_g0` derivable-from-stronger as a
KERNEL FACT (`logChowla2_ineffective_v7_ksarm_g0_of_rated` below).

`logChowla2_ineffective_v7_ksarm`, `logChowla2_ineffective_v7_ksarm_g0`,
`logChowla2_ineffective_v7`, `…_v6`, `…_v6_csarm`, `…_v6_T0arm` and every parent are
byte-untouched and remain citable. -/
theorem logChowla2_v7_rated (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧ Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      Mfl ≤ flatDoorM A ∧ 0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        ¬ logChowla2Fails R.eps R.x R.ω := by
  -- ⟦THE RATED CO-FACTOR SUPPLY⟧ four Skolem REALS, minted outside everything
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ :=
    cofkR_cofactorSupply_L_gk_rated
  obtain ⟨Awin, -, hband⟩ := s16_bandLaneWinL_holdsU
  -- ⟦THE cs-FREE, Ks-WINDOWED FLAT TERMINAL⟧ V7Ks §5
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ :=
    logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin Awin hband
  -- ⟦THE DESIGN CONSTANT, EIGHT ARMS⟧ the seven landed arms verbatim (`A'`), the eighth
  -- (`armVt Kvt`) outermost — every constant still minted BEFORE the lever: `Kvt` arrives at
  -- the supply obtain above, before the mint.
  obtain ⟨A', hA'def⟩ : ∃ a : ℝ, a = max (16 * Real.log (1 / Ks) / 3) (max T₀
      (max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
        (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))))) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (armVt Kvt) A' := ⟨_, rfl⟩
  have harmA : armVt Kvt ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hlift : A' ≤ A := by rw [hAdef]; exact le_max_right _ _
  have hKsA : 16 * Real.log (1 / Ks) / 3 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]; exact le_max_left _ _
  have hT₀A : T₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hA162 : (162 : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hA₀A : A₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAwinA : Awin ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_right (max (max A₀ 162) Awin)
      (cofkRThr Cq Cb Xsk Y0)) (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _)
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  -- ⟦THE `Ks` WINDOW, AT THE SEVENTH ARM⟧ as in the parent
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
  -- ⟦THE `T₀` ARM⟧ V7-C's discharge, as in the parent
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  -- ⟦THE EXHIBITED CALLER⟧ `g ≡ 0` meets the strict rider; the `g`-conjunct is discarded
  obtain ⟨R, hReps, hHlo, -, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKswin (fun _ _ : ℕ => 0)
      (xceilRiderStrict_zero ε)
  -- ⟦THE BASE-SCALE CAP⟧ at `K = KlevF A`, as in the parent
  have heps500 : (1 : ℚ) / 500 ≤ R.eps := by rw [hReps]; exact hεpin
  have hxceil : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [hReps]; exact hRx
  -- ⟦THE RATED SUPPLY, WITH THE CUSHION PAID BY THE EIGHTH ARM⟧
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
  have hKvtcush : 32 * Kvt
      + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
      ≤ Real.log (R.Hhi : ℝ) / 4 :=
    cofkR_cushion_of_armVt R hKvt0 harmA hlo
  have hcofsupply : S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) :=
    hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush
  have hfireR : ¬ logChowla2Fails R.eps R.x R.ω :=
    hfire2 hcofsupply
      (s16_baseScaleCap96_L_at_klevF hA26 (flatDoorM_one_le hA26) heps500 hxceil hwin)
  exact ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A,
    R, hReps, by rw [hHlo]; exact hbase hopq, hRtow, hdes, hwin, hfireR⟩

/-! ## §5 — N5: the no-trade receipt

The V7Ks §7/§7a house pattern: the landed `_g0` statement reproved from the rated headline,
then tied to the landed declaration by an `example` whose proof term is the landed name
itself.  This makes "derivable-from-stronger" a kernel fact instead of a docstring claim. -/

set_option exponentiation.threshold 4000 in
/-- **⟦NO TRADE⟧** a HAND-RETYPED copy of `V7Headline.logChowla2_ineffective_v7_ksarm_g0`'s
statement, re-derived from `logChowla2_v7_rated` at `Kvt := fun _ _ => 0` (nonnegativity by
`le_refl`, the cushion arrow by `fun _ => ·`).  Be exact about what the kernel referees here:
it referees the rated headline AGAINST THIS RESTATEMENT, not against the landed declaration —
the `example` immediately below closes that gap: its type is exactly this statement and its
proof term is the landed `logChowla2_ineffective_v7_ksarm_g0` itself, so any drift between
the copy and `V7Headline.lean:157` fails to elaborate HERE. -/
theorem logChowla2_ineffective_v7_ksarm_g0_of_rated (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
            + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
          ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
    a15, a16, a17, a18, a19, a20, a21,
    R, hReps, hHlo, hRtow, hdes, hwin, hfire⟩ := logChowla2_v7_rated A₀
  exact ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, fun _ _ => 0,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
    a15, a16, a17, a18, a19, a20, a21, fun _ _ => le_refl 0,
    R, hReps, hHlo, hRtow, hdes, hwin, fun _ => hfire⟩

set_option exponentiation.threshold 4000 in
/-- **⟦THE RESTATEMENT, TIED TO THE LANDED DECLARATION⟧** the theorem above retypes the landed
`_g0` statement by hand, so on its own it certifies only that the rated headline implies THAT
TEXT.  This `example`'s type is that statement, character for character, and its proof term is
the landed `V7Headline.logChowla2_ineffective_v7_ksarm_g0` itself — the kernel accepts the
landed declaration AT the restatement's type, so the two are the same up to defeq and the copy
is self-enforcing under future edits to either side. -/
example (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
            + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
          ¬ logChowla2Fails R.eps R.x R.ω)) :=
  logChowla2_ineffective_v7_ksarm_g0 A₀

end RatedHeadline

end Salt.MR

end
