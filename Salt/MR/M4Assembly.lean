/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ChiSocketWire
import Salt.MR.M4RowsChi
import Salt.MR.M4T0DatumDischarge
import Salt.MR.BallSupChi

/-!
# ⟦A4 — THE ASSEMBLY, THE WIRING HALF⟧ (`M4Assembly`)

Design provenance: the 0730 council's ⟦C5⟧ wave plan, fired on the two banks of
2026-07-30 (flags, `THE FIRST BANK lands` … `D2-REDERIVE lands`).  This file composes the
morning's landed stones into ⟦item 11⟧ of `m4_second_road` — `M4ChiSummed.M4ChiSummedFreeRow`
— at a NAMED door grade, with every gate the chain carries riding as an explicit hypothesis.

**The arithmetic is deliberately absent.**  Whether the grade this file produces meets
`m4_second_road_rs_ceiling` at the ratified g-arm/anchor numbers is the next executor's page;
here the grade is a `def` and the comparison is a hypothesis (`henv`).

## ⟦THE CHAIN⟧

1. §1 THE BALL WIRE — the `hSup` binder that `M4RowsChi.m4_rowChi_capstone` carries, supplied
   two ways: at the door pin `t₁ ≡ 0` by vacuity (`CapFreeArm.ball_leg_vacuous_at_zero`), and
   at FREE per-`χ` centres by `BallSupChi.ball_sup_pieceDatum`.
2. §2 THE DOOR DATUM BRIDGE — the door's row datum `winCutH X_d (doorChiCoeff χ M)` is the
   `χ̄`-twist of ONE untwisted sequence `doorCoeffU M`, so a supplier stated at
   `chiBarCoeff q χ a` and a supplier stated at the door datum speak the same object.
3. §3 THE SLOT FUSE + THE SHAPE CLOSE — `ThmA2ChiSummed.thm_a2'_of_rows_chiSummed` at the
   door datum (`N := 2X_d`, `X := X_d`, `h := 2^j`), whose left-hand side IS
   `∑_χ chiFreeRowSq χ M j X_d` after `M4DoorRow.shortSum_winCutH_seamS0`, and whose
   right-hand side is `φ(q)·a2DoorGrade M X_d 2^j C₁ M₀`.
4. §4 THE SOCKET FORM — `M4ChiSocketWire.M4ChiSummedFreeRowBig` met at the frozen binders,
   then `m4_chiSummedFreeRow_of_big` splices it to ⟦item 11⟧ at `m4ChiRowGraded M RSbig`.
5. §5 THE SAME WITH THE GATE LIST EXPANDED — `SocketBase` + `DoorFuseFrame` + the two per-`χ`
   slots + the arithmetic gate `henv`, and nothing else.
6. §6 THE WALL, IN THE KERNEL — `doorRows_global_hcoef_kills_block`.

## ⟦THE WALL FOUND ON THE WAY⟧ — `m4_hrowsSum_chi_door` does NOT fit the door datum

The wave brief asked for §3's `hrowsSum` slot to be filled by `M4RowsChi.m4_hrowsSum_chi_door`.
It cannot be, and the obstruction is in the corpus already:

* `m4_hrowsSum_chi_door` carries the **GLOBAL, unconditional** Lemma-12 factorization
  `∀ j ∈ [1,2], ∀ p m, p.Prime → P_j ≤ p → p ≤ Q_j → ¬p∣m → a (p·m) = bfam j m · c p`
  (`M4RowsChi.lean:1161-1162`), inherited from `m4_rowChi_number_of_capstone`
  (`M4RowsChi.lean:595-596`) and ultimately from `TLegChi`/`SeamNumber`;
* the SAME statement carries `hasupp : ∀ n, a n ≠ 0 → X_d ≤ n ≤ 2X_d`
  (`M4RowsChi.lean:1166`), which pins the datum to the dyadic window;
* `ThmA2Spine.seam_coef_contract_absurd` proves that pair CONTRADICTORY as soon as the datum
  is live somewhere and the block `[P_j, Q_j]` spans a ratio `> 2` (it does: `P₁ = 2^{E₁}`,
  `Q₁ = 2^{M·E₁}`), which is exactly why `SeamRowWindowed.SeamCoefW`/`SeamCoefWS` exist.

The LANDED `q = 1` row supplier `ThmA2Rows.a2Rows_of_capfree3_end` (`ThmA2Rows.lean:1057-1060`)
carries the STRICT relativized pair law `X_d < p·m → p·m ≤ 2X_d → a (p·m) = bfam j m · c p`,
not the global one.  So the `χ`-side re-derivation is one endpoint-wall repair behind the
`q = 1` side.  **Nothing here is patched to hide that**: §3 takes `hrowsSum` as a NAMED slot
in `thm_a2'_of_rows_chiSummed`'s own frozen shape, which any supplier — D2's, once re-cut at
`SeamCoefWS`, or the `q = 1` page read per character — plugs into unchanged.

## ⟦THE SECOND FROZEN-SHAPE FINDING⟧ — the ball leg at the door is `S ≡ 0`, not a sup

`m4_hrowsSum_chi_door` hard-codes the carried capstone's ball summand as `8·(0 : ℝ)^2`
(`M4RowsChi.lean:1181`), and the door bridge `m4MrowChi_le_a2Mrow` is stated at `S := 0`
(`M4RowsChi.lean:1104`) because `ThmA2.a2Mrow` has NO ball summand at all.  So
`BallSupChi.ball_sup_pieceDatum`'s nonzero `ballSupS X (pieceCenterS0 C X A)` cannot be wired
into the DOOR row without moving the frozen `a2Mrow`; at the door pin the ball leg is
discharged by emptiness instead (§1a), and BallSupChi's sup is wired at the FREE-centre shape
(§1b) where `m4_hrowsSum_chi`'s `S` is still a parameter.

## ⟦THE TRAPS RESPECTED⟧

`arcDen 12 H` is never evaluated and never conflated with a `log X` scale; the four log
scales stay apart (`Nat.log 2` for the dyadic index, `arcDen 12 H` for the modulus range and
the `φ(q)` ledger, `log X_d` for the grade, `loglog` inside the band summand only); the socket's
`RS` stays `q`-FREE and the `φ(q)` debit is carried in the open as `arcDen 12 H`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE BALL WIRE

`M4RowsChi.m4_rowChi_capstone` carries its ball leg as the binder

  `hSup : ∀ χ, ∀ t, seamT0 X ≤ |t| → |t| ≤ T_ann → |t − t₁ χ| ≤ seamRad X →`
  `        ∀ m ≤ N, ‖spolyA (χ̄a) t m‖ ≤ S χ · m/(1 + |t − t₁ χ|)`

(`M4RowsChi.lean:457-460`).  Two suppliers land here. -/

/-- **§1a — THE DOOR PIN: the ball leg is VACUOUS.**  At `t₁ ≡ 0` the seam ball misses the
seam annulus (`CenterCore.seamRad_lt_seamT0`), so the carried `hSup` holds at `S ≡ 0` for
EVERY datum and every character — the `8S²` summand of `m4MrowChi` is zero, which is what
`M4RowsChi.m4MrowChi_le_a2Mrow` (stated at `S := 0`) and `ThmA2.a2Mrow` (which has no ball
summand) require.  This is the wire the DOOR takes. -/
theorem m4_hSup_door_at_zero (q : ℕ) (a : ℕ → ℂ) (N : ℕ) {X Tann : ℝ}
    (hL : 1 < Real.log X) :
    ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann →
      |t - (fun _ : DirichletCharacter ℂ q => (0 : ℝ)) χ| ≤ seamRad X → ∀ m : ℕ, m ≤ N →
        ‖spolyA (chiBarCoeff q χ a) t m‖
          ≤ (fun _ : DirichletCharacter ℂ q => (0 : ℝ)) χ * m
              / (1 + |t - (fun _ : DirichletCharacter ℂ q => (0 : ℝ)) χ|) :=
  fun χ => ball_leg_vacuous_at_zero (N := N) (a := chiBarCoeff q χ a) (T := Tann) hL

/-- **§1b — THE FREE-CENTRE WIRE: `BallSupChi`'s sup, per character.**
`BallSupChi.ball_sup_pieceDatum` read at a per-`χ` centre family `t₁` and a per-`χ` datum
family `adat`, delivering `m4_rowChi_capstone`'s carried `hSup` at the CHARACTER-UNIFORM sup
`S χ := ballSupS X (pieceCenterS0 C X A)`.

`χ` precedes `t₁` in `ball_sup_pieceDatum`, so per-`χ` centres cost nothing (C2-SCOPE K-3).
Every gate of the landed page rides in-statement; the `𝒥 = {jb}` block, the covering mass and
the Rankin tail are the ones `RamareMassTail` supplies.

⟦NOT USABLE AT THE DOOR⟧ see the header's second frozen-shape finding: `a2Mrow` has no `8S²`
summand, so this wire feeds `m4_hrowsSum_chi` (where `S` is a parameter), never
`m4_hrowsSum_chi_door` (where `S` is pinned to `0`). -/
theorem m4_hSup_pieceDatum_perChi (A : ℝ) (hA : 0 < A) {Mmass : ℝ} (hMmass : 0 ≤ Mmass) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧
      ∀ (X Tann : ℝ) (N : ℕ) (q : ℕ) [NeZero q]
        (adat : DirichletCharacter ℂ q → ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (jb : ℕ)
        (t₁ : DirichletCharacter ℂ q → ℝ),
        ballMertensThreshold ≤ X → (x₀ : ℝ) ≤ X / 2 →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X →
        (q : ℝ) ≤ Real.log (X / 2) ^ (10 : ℕ) →
        (∀ χ : DirichletCharacter ℂ q, |t₁ χ| ≤ (Nat.sqrt (Nat.sqrt ⌊X⌋₊) : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          (∑ b ∈ Finset.Icc 1 (Nat.sqrt k),
              ramTailWeight (Pseq jb) (Qseq jb) 0 b / (b : ℝ)) ≤ Mmass) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          (∑ b ∈ Finset.Ioc (Nat.sqrt k) k,
              ramTailWeight (Pseq jb) (Qseq jb) 0 b / (b : ℝ)) ≤ 1 / Real.log (k : ℝ) ^ A) →
        (∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, (n : ℝ) ≤ X → adat χ n = 0) →
        (∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, X < (n : ℝ) →
          adat χ n = pieceDatum χ ({jb} : Finset ℕ) Pseq Qseq n) →
        (∀ χ : DirichletCharacter ℂ q, ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
          pretDistSq (pieceDatum χ ({jb} : Finset ℕ) Pseq Qseq) (costwist (t₁ χ)) x
            ≤ (1 / 16) * Real.log (Real.log X)) →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann →
          |t - t₁ χ| ≤ seamRad X → ∀ m : ℕ, m ≤ N →
            ‖spolyA (adat χ) t m‖
              ≤ ballSupS X (pieceCenterS0 C X A) * m / (1 + |t - t₁ χ|) := by
  obtain ⟨C, x₀, hCpos, hsup⟩ := ball_sup_pieceDatum A hA hMmass
  refine ⟨C, x₀, hCpos, ?_⟩
  intro X Tann N q hne adat Pseq Qseq jb t₁ hXth hx₀ hXN hN2 hq ht₁ hmass htail hsupp hDatum
    hcap χ
  haveI : NeZero q := hne
  exact hsup X Tann N (adat χ) q χ Pseq Qseq jb (t₁ χ) hXth hx₀ hXN hN2 hq (ht₁ χ) hmass htail
    (hsupp χ) (hDatum χ) (hcap χ)

/-! ## §2 — THE DOOR DATUM BRIDGE

`M4T0DatumDischarge.m4_hT0band_at_door_discharged` and `M4DoorClose` speak the door's row
datum as `winCutH X_d (doorChiCoeff χ M)`; `M4RowsChi.m4_hrowsSum_chi_door` speaks it as
`chiBarCoeff q χ a` for an UNTWISTED `a`.  The two are the same object at

  `a := winCutH X_d (doorCoeffU M)`,

because the `χ̄`-twist commutes with both the sieve indicator and the half-open window cut. -/

/-- **THE UNTWISTED DOOR DATUM** (`doorCoeffU M = 1_𝒮·λ`) — `doorChiCoeff`'s untwisted twin at
the door's own K-family.  `liouvilleC`, never `lam` (the ⟦lam collision⟧: the row's sum runs
over integers). -/
def doorCoeffU (M : ℕ) : ℕ → ℂ :=
  memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC

/-- The `χ̄`-twist of the untwisted door datum IS the door's sieved χ-twisted datum. -/
theorem chiBarCoeff_doorCoeffU {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) :
    chiBarCoeff q χ (doorCoeffU M) = doorChiCoeff χ M := by
  funext n
  simp only [chiBarCoeff_apply, doorCoeffU, doorChiCoeff, memSCoeff, liouChi]
  split_ifs
  · ring
  · rw [mul_zero]

/-- The `χ̄`-twist commutes with the half-open dyadic cut. -/
theorem chiBarCoeff_winCutH {q : ℕ} (χ : DirichletCharacter ℂ q) (Xd : ℕ) (F : ℕ → ℂ) :
    chiBarCoeff q χ (winCutH Xd F) = winCutH Xd (chiBarCoeff q χ F) := by
  funext n
  simp only [chiBarCoeff_apply, winCutH]
  split_ifs
  · rfl
  · rw [mul_zero]

/-- **THE BRIDGE** — the door's ROW datum is the `χ̄`-twist of one untwisted sequence.  This is
what makes a supplier written at `chiBarCoeff q χ a` and a supplier written at
`winCutH X_d (doorChiCoeff χ M)` interchangeable in §3's slots. -/
theorem chiBarCoeff_doorRowDatum {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd : ℕ) :
    chiBarCoeff q χ (winCutH Xd (doorCoeffU M)) = winCutH Xd (doorChiCoeff χ M) := by
  rw [chiBarCoeff_winCutH, chiBarCoeff_doorCoeffU]

/-! ## §3 — THE DOOR GRADE, AND THE SLOT FUSE

`ThmA2ChiSummed.thm_a2'_of_rows_chiSummed`'s five-summand right-hand side, read at the door's
CHARACTER-UNIFORM constants (`Cs χ ≡ Cs`, `Ccc χ ≡ Ccc`, `C₁' χ ≡ cfbC₁ X C₁`, `M₀ χ ≡ M₀`,
`ε χ ≡ ε` — which is what both landed suppliers deliver: `m4_hrowsSum_chi_door`'s `Ct`, `Cp`
are the `q = 1` universal constants, and `m4_hT0band_at_door_discharged`'s `C'`, `M₀` are
`χ`-free), collapses to `φ(q)` times ONE `χ`-free number. -/

/-- **THE DOOR GRADE** (`a2DoorGrade M X h C₁ M₀`) — the five summands of
`ThmA2.thm_a2'_of_rows`' frozen interface at the door parameters, `T`-FREE and `χ`-FREE.

`∑_χ` of the frozen exit at the door's character-uniform constants is exactly
`φ(q)·a2DoorGrade` (`m4_chiFreeRowSq_sum_at_door`): the `T₀`-band summand's character sum
degenerates to `φ(q)` copies, and the other four are `χ`-free already. -/
def a2DoorGrade (M : ℕ) (X h C₁ M₀ : ℝ) : ℝ :=
  8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
    + 1787702400 * a2Level1 M
    + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
    + 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
    + 6315000 / h

/-- `0 ≤ log n` for every natural `n` (at `n = 0` both sides are `0`) — the socket's bases are
naturals, so the grade's `log X_d` factors never go negative. -/
theorem log_natCast_nonneg' (n : ℕ) : 0 ≤ Real.log ((n : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- The door grade is nonnegative — needed to pay the `φ(q) ≤ arcDen 12 H` ledger step. -/
theorem a2DoorGrade_nonneg (M : ℕ) {X h C₁ M₀ : ℝ} (hX : 0 ≤ Real.log X) (hh : 0 < h) :
    0 ≤ a2DoorGrade M X h C₁ M₀ := by
  have hQ1 : (1 : ℝ) ≤ ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := by
    exact_mod_cast one_le_calQK (Adoor M) (3072 * M) M 1
  have hP1 : (1 : ℝ) ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    have h : 1 ≤ calP (Adoor M) (3072 * M) 1 := by
      simp only [calP]; exact Nat.one_le_two_pow
    exact_mod_cast h
  have hlvl : (0 : ℝ) ≤ a2Level1 M := by
    unfold a2Level1
    have h1 : (0 : ℝ) ≤ (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (Real.log_nonneg hQ1) _
    have h2 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
      Real.rpow_pos_of_pos (by linarith) _
    exact div_nonneg h1 h2.le
  have h500 : (0 : ℝ) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) := Real.rpow_nonneg hX _
  have h4345 : (0 : ℝ) ≤ (Real.log X) ^ (-(43 : ℝ) / 45) := Real.rpow_nonneg hX _
  have hband : (0 : ℝ) ≤ 8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀) := by
    positivity
  have hball : (0 : ℝ) ≤ 304128 * ballSupC ^ 2
      * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by
    have : (0 : ℝ) ≤ (Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2 :=
      mul_nonneg h4345 (sq_nonneg _)
    positivity
  have hh6 : (0 : ℝ) ≤ 6315000 / h := by positivity
  unfold a2DoorGrade
  linarith

/-- **⟦THE SLOT FUSE + THE SHAPE CLOSE⟧** (`m4_chiFreeRowSq_sum_at_door`).

`ThmA2ChiSummed.thm_a2'_of_rows_chiSummed` instantiated at the door datum

  `N := 2X_d`,  `X := X_d`,  `h := 2^j`,  `a χ := winCutH X_d (doorChiCoeff χ M)`,

whose LEFT-hand side is `∑_χ chiFreeRowSq χ M j X_d` — `M4ChiSummed.chiFreeRowSq`'s body at
the same two pins, with the cut invisible to the row's short sum
(`M4DoorRow.shortSum_winCutH_seamS0`) — and whose RIGHT-hand side collapses to
`φ(q)·a2DoorGrade M X_d 2^j C₁ M₀`.

⟦THE GATE LIST — nothing absorbed⟧
* `hM` — `1 ≤ M`, the door's parameter;
* `hX`, `hX3` — `e ≤ X_d` and `3 ≤ X_d` (the frozen interface's scale pins);
* `hh4`, `hhX` — `4 ≤ 2^j` (the AS-2 MVT guard) and Lemma 14's window frame
  `2^j ≤ X_d·(log X_d)^{−1/5}`;
* `hTann`, `hceil` — `TannGate X_d (2X_d/2^j)` and `5 ≤ loglog(2X_d/2^j)`, the `h`-ceiling;
* `hrowsSum` — the weighted seam-row family at `a2Mrow Cs Ccc M X_d X_d ε`, PER CHARACTER, in
  `thm_a2'_of_rows_chiSummed`'s own frozen binder.  **CARRIED, NOT DISCHARGED** — see the
  header's ⟦THE WALL⟧: `M4RowsChi.m4_hrowsSum_chi_door` meets this shape but its own `hcoef`
  is the global factorization contract `ThmA2Spine.seam_coef_contract_absurd` refutes at a
  window-cut datum, and the door's datum is window-cut;
* `hT0bandSum` — the `T₀`-band at `t0BandB X_d (cfbC₁ X_d C₁) M₀`, PER CHARACTER.  This slot
  IS discharged by `M4T0DatumDischarge.m4_hT0band_at_door_discharged` (whose datum is
  literally `winCutH X_d (doorChiCoeff χ M)`), under its own named gates: `400 ≤ X_d`,
  `x₀ ≤ X_d`, `16 ≤ X_d`, `q ≤ (log X_d)^{10}`, the covering window `[P, Q]`, the three
  Rankin/mass gates per `k ∈ [X_d, 2X_d]`, the grade fit and `hErr`;
* `hgP1`, `hgRows`, `hL4096` — the three GRADING gates of the frozen interface;
* `hεwin` — the `𝒰`-leg's exponent room `0 ≤ ε ≤ θ₂₉₃ − 1/500`.

The datum-side binders `ha`/`hsupp` are NOT hypotheses: they are discharged in-file from
`M4DoorRow.doorRow_ha1` / `doorRow_hsupp0`, and `hN2` is the pin `N = 2X_d` itself. -/
theorem m4_chiFreeRowSq_sum_at_door {q : ℕ} [NeZero q] {M Xd j : ℕ} {Cs Ccc C₁ M₀ ε : ℝ}
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
              ‖spoly (2 * Xd) (winCutH Xd (doorChiCoeff χ M)) t‖ ^ 2)
        ≤ a2Mrow Cs Ccc M Xd ((Xd : ℕ) : ℝ) ε)
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 ((Xd : ℕ) : ℝ)))..(seamT0 ((Xd : ℕ) : ℝ)),
        ‖dpolyA (winCutH Xd (doorChiCoeff χ M)) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) t‖ ^ 2)
        ≤ t0BandB ((Xd : ℕ) : ℝ) (cfbC₁ ((Xd : ℕ) : ℝ) C₁) M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500))
    (hgRows : 5760 * (a2RowsSum M Xd + Ccc * (2 / (M : ℝ)))
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500))
    (hεwin : 0 ≤ ε ∧ ε ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)) :
    ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j Xd
      ≤ (q.totient : ℝ) * a2DoorGrade M ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) C₁ M₀ := by
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hbase := thm_a2'_of_rows_chiSummed (q := q) (N := 2 * Xd) (M := M) (Xd := Xd)
    (a := fun χ => winCutH Xd (doorChiCoeff χ M)) (X := ((Xd : ℕ) : ℝ))
    (h := ((2 ^ j : ℕ) : ℝ)) (Cs := fun _ => Cs) (Ccc := fun _ => Ccc)
    (C₁' := fun _ => cfbC₁ ((Xd : ℕ) : ℝ) C₁) (M₀ := fun _ => M₀) (ε := fun _ => ε)
    hM hX hX3 hh4 hhX (fun χ n => doorRow_ha1 χ M Xd n)
    (fun χ n hn => doorRow_hsupp0 χ M Xd n hn) hN2 hTann hceil hrowsSum hT0bandSum
    (fun _ => hgP1) (fun _ => hgRows) (fun _ => hεwin) hL4096
  simp only [shortSum_winCutH_seamS0] at hbase
  refine le_trans hbase (le_of_eq ?_)
  rw [a2_sum_const_chars]
  unfold a2DoorGrade
  ring

/-! ## §4 — THE SOCKET FORM

`M4ChiSocketWire.M4ChiSummedFreeRowBig`'s binders are FROZEN: the two regime bounds, the
cap-general length `L ≤ H`, the modulus range `0 < q ≤ arcDen 12 H`, the dyadic window index
`j ≤ log₂ L`, the door's length floor `doorRowFloor M ≤ j`, the three base antecedents of
⟦R-P5⟧ (`0 < A`, `2^j ≤ A`, `√H ≤ A`, the x-scale antecedent), the base cap `A ≤ 2·R.x`
(the (α) base-cap surgery, JYH-granted 2026-07-30) and the free shift `s ≤ L`.
They are met here verbatim — every one of them is either passed to the fused grade, packed
into `SocketBase`, or simply UNUSED (the base antecedents only weaken the socket). -/

/-- **⟦A4 — THE SOCKET AT THE DOOR GRADE⟧** (`m4_chiSummedFreeRowBig_of_doorGrade`).

The `Σ_χ` door row, graded base by base by §3, inhabits `M4ChiSocketWire`'s large-`j` socket at
an ABSTRACT `RSbig`, under ONE arithmetic gate:

  `henv : arcDen 12 H · a2DoorGrade M (A+s) 2^j (C₁ (A+s)) (M₀ (A+s)) ≤ RSbig j H`.

⟦THE φ(q) LEDGER, IN THE OPEN⟧ the character count is paid as `φ(q) ≤ q ≤ arcDen 12 H` — the
socket's own modulus gate — and appears in `henv` explicitly.  Nothing is absorbed: this file
does not read `m4_second_road_rs_ceiling`, and `henv` is precisely the arithmetic the next
executor owes.

`C₁ M₀ : ℕ → ℝ` are indexed by the BASE `A + s` because `m4_hT0band_at_door_discharged`
chooses them per instance; `hgrade` is §3's conclusion, quantified over exactly the socket's
bases. -/
theorem m4_chiSummedFreeRowBig_of_doorGrade {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ}
    {RSbig : ℕ → ℕ → ℝ}
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloor M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) := a2DoorGrade_nonneg M (log_natCast_nonneg' (A + s)) hh0
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans
    (hgrade H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H j A s hjfl

/-- **⟦A4 — ITEM 11, INHABITED AT THE DOOR GRADE⟧** (`m4_chiSummedFreeRow_of_doorGrade`).
§4 spliced through `M4ChiSocketWire.m4_chiSummedFreeRow_of_big`: the second road's ONE
analytic slot `M4ChiSummed.M4ChiSummedFreeRow` holds at

  `RS j H = if doorRowFloor M ≤ j then RSbig j H else 4·arcDen 12 H`,

the small-`j` half being the landed absolute grade (`m4_chiSummedFreeRow_trivial`), which
⟦gate 4⟧ never reads (`M4ChiSocketWire.m4ChiRowGraded_an`). -/
theorem m4_chiSummedFreeRow_of_doorGrade {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ}
    {RSbig : ℕ → ℕ → ℝ}
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloor M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) :=
  m4_chiSummedFreeRow_of_big (m4_chiSummedFreeRowBig_of_doorGrade hgrade henv)

/-! ## §5 — THE SAME, WITH THE GATE LIST EXPANDED

§4 takes §3's fused conclusion as one hypothesis.  This section restates it with §3's gate
list written out, so that ⟦item 11⟧ at the door grade is reachable from the NAMED gates alone.
`SocketBase` is the socket's own base condition, named once so the three quantified
hypotheses share one prefix; `DoorFuseFrame` is §3's character-blind frame, field by field. -/

/-- **THE SOCKET'S BASE CONDITION, NAMED** (`SocketBase`) — exactly `M4ChiSummedFreeRowBig`'s
antecedents at one base, carried verbatim (never weakened): the two regime bounds, the
cap-general length, the modulus range, the dyadic window index, the door's length floor, the
three ⟦R-P5⟧ base antecedents with the x-scale one, **the base cap `A ≤ 2·R.x`**, and the
free shift.

⟦THE BASE CAP FIELD — the (α) base-cap surgery, JYH-granted 2026-07-30⟧ this is the field
that makes the `hframe` hypothesis SATISFIABLE.  `DoorFuseFrame.gP1` and the `X_d`-dependent
part of `gRows` are UPPER caps on `X_d = A + s` (their right-hand side
`(log X_d)^{-1/500}` decays), while `SocketBase` used to be closed upward — so
`∀ base, SocketBase → DoorFuseFrame` was refutable on the up-set (the refuter's kernel kill
`hframe_unsatisfiable`, `flags.md` 2026-07-30 08:47).  With the cap the quantifier runs over
a BOUNDED base range and the caps are checked against `log(2·R.x)` at the `g`-arm; see
`M4SocketDischarge`'s header ⟦THE SATISFIABILITY, AFTER THE CAP⟧ for the arithmetic. -/
def SocketBase (R : ChowlaRegime) (M H L q j A s : ℕ) : Prop :=
  R.Hlo ≤ H ∧ H ≤ R.Hhi ∧ L ≤ H ∧ 0 < q ∧ (q : ℝ) ≤ arcDen 12 H ∧ j ≤ Nat.log 2 L ∧
    doorRowFloor M ≤ j ∧ 0 < A ∧ 2 ^ j ≤ A ∧ Real.sqrt (H : ℝ) ≤ (A : ℝ) ∧
    (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) ∧ (A : ℝ) ≤ 2 * (R.x : ℝ) ∧ s ≤ L

/-- **THE FUSE FRAME AT ONE BASE** (`DoorFuseFrame`) — the CHARACTER-BLIND half of
`m4_chiFreeRowSq_sum_at_door`'s gate list, field by field.  Nothing is absorbed: each field is
one of `ThmA2.thm_a2'_of_rows`' own in-statement side conditions, read at `X := X_d`,
`h := 2^j`. -/
structure DoorFuseFrame (M Xd j : ℕ) (Cs Ccc ε : ℝ) : Prop where
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
  /-- `5 ≤ loglog(2X_d/2^j)` — the `h`-ceiling, MRT's bare `h ≥ 3` replaced honestly. -/
  ceil5 : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
  /-- The first GRADING gate, on the `𝒯`-leg constant `Cs`. -/
  gP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
    ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
  /-- The second GRADING gate, on the Lemma-12 row sum and the density constant `Ccc`. -/
  gRows : 5760 * (a2RowsSum M Xd + Ccc * (2 / (M : ℝ)))
    ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
  /-- The `𝒰`-leg's exponent room, lower end. -/
  eps_lo : 0 ≤ ε
  /-- The `𝒰`-leg's exponent room, upper end (`θ₂₉₃ = 1/(32(3e+1))`). -/
  eps_hi : ε ≤ theta293 - 1 / 500
  /-- The third GRADING gate. -/
  L4096 : 4096 ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)

/-- **⟦A4 — THE ASSEMBLY⟧** (`m4_chiSummedFreeRow_of_doorAssembly`).  ⟦Item 11⟧ of
`m4_second_road` — `M4ChiSummed.M4ChiSummedFreeRow` — inhabited at the door grade

  `RS j H = if doorRowFloor M ≤ j then RSbig j H else 4·arcDen 12 H`,

from the NAMED gates alone.  THE COMPLETE GATE LIST:

* `hM` — `1 ≤ M`;
* `hframe` — `DoorFuseFrame` at every base the socket reaches (eleven fields, above);
* `hrows` — the weighted seam-row family at `a2Mrow`, PER CHARACTER, in
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
  `door_cover`/`door_window_bounds`, the three mass/Rankin gates per `k ∈ [X_d, 2X_d]`, the
  grade fit `8C' ≤ (log X_d)^{A−1/2+1/1000}` and `hErr`);
* `henv` — THE ARITHMETIC, and the only thing this file leaves open:
  `arcDen 12 H · a2DoorGrade M (A+s) 2^j (C₁ (A+s)) (M₀ (A+s)) ≤ RSbig j H`.  The `arcDen`
  factor IS the ⟦φ(q) LEDGER⟧'s debit `φ(q) ≤ q ≤ arcDen 12 H`, carried in the open. -/
theorem m4_chiSummedFreeRow_of_doorAssembly {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorFuseFrame M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
          ≤ a2Mrow (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorGrade (C₁ := C₁) (M₀ := M₀) ?_ henv
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb : SocketBase R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows
    ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-! ## §6 — THE WALL, IN THE KERNEL

The obstruction the header states in prose, re-exported at the door's own ladder so it is a
checked object and not a note. -/

/-- **⟦THE WALL⟧** (`doorRows_global_hcoef_kills_block`).
`ThmA2Spine.seam_coef_contract_forces_vanishing` read at the DOOR's block `j`: a datum that is
window-supported (`M4RowsChi.m4_hrowsSum_chi_door`'s `hasupp`, `M4RowsChi.lean:1166`) and obeys
the GLOBAL Lemma-12 factorization (its `hcoef`, `M4RowsChi.lean:1161-1162`) is KILLED on the
whole block by one live product plus one block prime that pushes off the window:
`a (p₁·m) = 0` for every `m` coprime to `p₁`.

At the door ladder `[P_j, Q_j] = [2^{E_j}, 2^{j²M·E_j}]` the ratio is far above `2`, so such a
`p₁` sits next to every live `p₀`.  This is why `m4_chiFreeRowSq_sum_at_door` CARRIES its
`hrowsSum` slot instead of filling it from the D2 door page, and why the landed `q = 1`
supplier `ThmA2Rows.a2Rows_of_capfree3_end` (`ThmA2Rows.lean:1057-1060`) states the STRICT
relativized pair law `SeamRowWindowed.SeamCoefWS` instead of the global contract. -/
theorem doorRows_global_hcoef_kills_block {a b c : ℕ → ℂ} {M Xd j : ℕ}
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (hcoef : ∀ p m : ℕ, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
      p ≤ calQK (Adoor M) (3072 * M) M j → ¬ p ∣ m → a (p * m) = b m * c p)
    {p₀ p₁ m₀ : ℕ} (hp₀ : p₀.Prime) (hP₀ : calP (Adoor M) (3072 * M) j ≤ p₀)
    (hQ₀ : p₀ ≤ calQK (Adoor M) (3072 * M) M j) (hd₀ : ¬ p₀ ∣ m₀)
    (hlive : a (p₀ * m₀) ≠ 0)
    (hp₁ : p₁.Prime) (hP₁ : calP (Adoor M) (3072 * M) j ≤ p₁)
    (hQ₁ : p₁ ≤ calQK (Adoor M) (3072 * M) M j) (hd₁ : ¬ p₁ ∣ m₀)
    (hoff : 2 * Xd < p₁ * m₀) :
    ∀ m : ℕ, ¬ p₁ ∣ m → a (p₁ * m) = 0 :=
  seam_coef_contract_forces_vanishing hasupp hcoef hp₀ hP₀ hQ₀ hd₀ hlive hp₁ hP₁ hQ₁ hd₁ hoff

/-! ## §GK — the G-lever twin

The additive `_gk` family at `G := s13GK K M` (`GLever`): each declaration below is its landed
original with `(K : ℕ)` as a new FIRST binder and every `3072 * M` read of the door's growth
base rewritten to `s13GK K M`.  `J` stays `2`; `Adoor M` is unchanged.

⟦WHAT KEEPS ITS LANDED NAME, AND WHY⟧

* `doorRowFloor M = M · Adoor M` and `SocketBase` are `G`-FREE — the socket's base condition is
  reused VERBATIM by every twin below.
* `a2Level1 M` is LEVEL 1 and therefore K-INVARIANT (`GLever.calP_gk_one_eq`,
  `calQK_gk_one_eq`), so `a2DoorGrade_gk`'s body is byte-identical to `a2DoorGrade`'s: the
  grade's five summands read the ladder only at level 1 (through `a2Level1`) or not at all.
  The twin is declared anyway, uniformly in `K`, so that every consumer below reads ONE symbol
  and the family stays mechanical.
* `chiBarCoeff_winCutH` (:184) and `log_natCast_nonneg'` (:223) are datum-generic and
  `G`-blind; `m4_hSup_door_at_zero` (:104) and `m4_hSup_pieceDatum_perChi` (:125) speak an
  abstract datum.  None of the four is twinned.

⟦THE §2 TRIO IS NOT RE-DECLARED HERE — CROSS-GROUP COLLISION, RESOLVED IN FAVOUR OF THE
LANDED COPY⟧  `doorCoeffU_gk` (:171), `chiBarCoeff_doorCoeffU_gk` (:175) and
`chiBarCoeff_doorRowDatum_gk` (:195) are ALREADY LANDED, byte-identically, in
`M4RowsChiEnd`'s own `§GK` (its header marks them ⟦PROVISIONAL, M4Assembly-SIDE⟧ and says to
delete them here if this file ever grows its own).  `M4RowsChiEnd` is a SIBLING of this file,
not an ancestor, so declaring them a second time makes the two branches unmergeable: the
first common descendant (`M4ArithZero`) fails with `environment already contains
'Salt.MR.doorCoeffU_gk'`.  They are therefore left where they are; nothing downstream is
missing.  Moving them back here is a one-commit maestro decision, not an executor's.

The two moved slots that DO carry the lever into a statement are `hgP1` (the level-1 `𝒫₁` at
the levered base — the same symbol by `calP_gk_one_eq`, written at the lever for uniformity)
and `hgRows` (at `ThmA2.a2RowsSum_gk`, which reads `𝒫₂` and genuinely moves). -/

set_option linter.unusedVariables false in
/-- `a2DoorGrade` (:213), at the lever.  The body is byte-identical: the only ladder read is
`a2Level1 M`, which is LEVEL 1 and K-invariant.  The twin exists for uniformity of the
family's shape (`K` first, everywhere), exactly as `M4Close.m4RawMS_gk` does. -/
def a2DoorGrade_gk (K : ℕ) (M : ℕ) (X h C₁ M₀ : ℝ) : ℝ :=
  8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
    + 1787702400 * a2Level1 M
    + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
    + 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
    + 6315000 / h

/-- The levered grade IS the landed one — recorded so the twin's fidelity is a checked object
and not a claim (`a2Level1` is K-invariant). -/
theorem a2DoorGrade_gk_eq (K : ℕ) (M : ℕ) (X h C₁ M₀ : ℝ) :
    a2DoorGrade_gk K M X h C₁ M₀ = a2DoorGrade M X h C₁ M₀ := rfl

/-- `a2DoorGrade_nonneg` (:229), at the lever. -/
theorem a2DoorGrade_nonneg_gk (K : ℕ) (M : ℕ) {X h C₁ M₀ : ℝ} (hX : 0 ≤ Real.log X)
    (hh : 0 < h) : 0 ≤ a2DoorGrade_gk K M X h C₁ M₀ :=
  a2DoorGrade_nonneg M hX hh

/-- `m4_chiFreeRowSq_sum_at_door` (:289), at the lever. -/
theorem m4_chiFreeRowSq_sum_at_door_gk (K : ℕ) {q : ℕ} [NeZero q] {M Xd j : ℕ}
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
              ‖spoly (2 * Xd) (winCutH Xd (doorChiCoeff_gk K χ M)) t‖ ^ 2)
        ≤ a2Mrow_gk K Cs Ccc M Xd ((Xd : ℕ) : ℝ) ε)
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 ((Xd : ℕ) : ℝ)))..(seamT0 ((Xd : ℕ) : ℝ)),
        ‖dpolyA (winCutH Xd (doorChiCoeff_gk K χ M)) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) t‖ ^ 2)
        ≤ t0BandB ((Xd : ℕ) : ℝ) (cfbC₁ ((Xd : ℕ) : ℝ) C₁) M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500))
    (hgRows : 5760 * (a2RowsSum_gk K M Xd + Ccc * (2 / (M : ℝ)))
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500))
    (hεwin : 0 ≤ ε ∧ ε ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)) :
    ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_gk K χ M j Xd
      ≤ (q.totient : ℝ) * a2DoorGrade_gk K M ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) C₁ M₀ := by
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hbase := thm_a2'_of_rows_chiSummed_gk K (q := q) (N := 2 * Xd) (M := M) (Xd := Xd)
    (a := fun χ => winCutH Xd (doorChiCoeff_gk K χ M)) (X := ((Xd : ℕ) : ℝ))
    (h := ((2 ^ j : ℕ) : ℝ)) (Cs := fun _ => Cs) (Ccc := fun _ => Ccc)
    (C₁' := fun _ => cfbC₁ ((Xd : ℕ) : ℝ) C₁) (M₀ := fun _ => M₀) (ε := fun _ => ε)
    hM hX hX3 hh4 hhX (fun χ n => doorRow_ha1_gk K χ M Xd n)
    (fun χ n hn => doorRow_hsupp0_gk K χ M Xd n hn) hN2 hTann hceil hrowsSum hT0bandSum
    (fun _ => hgP1) (fun _ => hgRows) (fun _ => hεwin) hL4096
  simp only [shortSum_winCutH_seamS0] at hbase
  refine le_trans hbase (le_of_eq ?_)
  rw [a2_sum_const_chars]
  unfold a2DoorGrade_gk
  ring

/-- `DoorFuseFrame` (:440), at the lever.  Two of the eleven fields move: `gP1`'s `𝒫₁` is
written at the levered base and `gRows` reads `ThmA2.a2RowsSum_gk`. -/
structure DoorFuseFrame_gk (K : ℕ) (M Xd j : ℕ) (Cs Ccc ε : ℝ) : Prop where
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
  gP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
    ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
  /-- The second GRADING gate, at the levered row sum. -/
  gRows : 5760 * (a2RowsSum_gk K M Xd + Ccc * (2 / (M : ℝ)))
    ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
  /-- The `𝒰`-leg's exponent room, lower end. -/
  eps_lo : 0 ≤ ε
  /-- The `𝒰`-leg's exponent room, upper end (`θ₂₉₃ = 1/(32(3e+1))`). -/
  eps_hi : ε ≤ theta293 - 1 / 500
  /-- The third GRADING gate. -/
  L4096 : 4096 ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)

/-- `m4_chiSummedFreeRowBig_of_doorGrade` (:355), at the lever. -/
theorem m4_chiSummedFreeRowBig_of_doorGrade_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {C₁ M₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloor M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_gk K χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig_gk K R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) := a2DoorGrade_nonneg_gk K M (log_natCast_nonneg' (A + s)) hh0
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans
    (hgrade H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H j A s hjfl

/-- `m4_chiSummedFreeRow_of_doorGrade` (:392), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorGrade_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {C₁ M₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloor M ≤ j → ∀ A : ℕ, 0 < A →
        2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
        (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) →
        (A : ℝ) ≤ 2 * (R.x : ℝ) → ∀ s ≤ L,
          ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_gk K χ M j (A + s)
            ≤ (q.totient : ℝ)
                * a2DoorGrade_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                    (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M RSbig) :=
  m4_chiSummedFreeRow_of_big_gk K (m4_chiSummedFreeRowBig_of_doorGrade_gk K hgrade henv)

/-- `m4_chiSummedFreeRow_of_doorAssembly` (:492), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorFuseFrame_gk K M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorGrade_gk K (C₁ := C₁) (M₀ := M₀) ?_ henv
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb : SocketBase R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_gk K hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows
    ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-- `doorRows_global_hcoef_kills_block` (:543), at the lever. -/
theorem doorRows_global_hcoef_kills_block_gk (K : ℕ) {a b c : ℕ → ℂ} {M Xd j : ℕ}
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (hcoef : ∀ p m : ℕ, p.Prime → calP (Adoor M) (s13GK K M) j ≤ p →
      p ≤ calQK (Adoor M) (s13GK K M) M j → ¬ p ∣ m → a (p * m) = b m * c p)
    {p₀ p₁ m₀ : ℕ} (hp₀ : p₀.Prime) (hP₀ : calP (Adoor M) (s13GK K M) j ≤ p₀)
    (hQ₀ : p₀ ≤ calQK (Adoor M) (s13GK K M) M j) (hd₀ : ¬ p₀ ∣ m₀)
    (hlive : a (p₀ * m₀) ≠ 0)
    (hp₁ : p₁.Prime) (hP₁ : calP (Adoor M) (s13GK K M) j ≤ p₁)
    (hQ₁ : p₁ ≤ calQK (Adoor M) (s13GK K M) M j) (hd₁ : ¬ p₁ ∣ m₀)
    (hoff : 2 * Xd < p₁ * m₀) :
    ∀ m : ℕ, ¬ p₁ ∣ m → a (p₁ * m) = 0 :=
  seam_coef_contract_forces_vanishing hasupp hcoef hp₀ hP₀ hQ₀ hd₀ hlive hp₁ hP₁ hQ₁ hd₁ hoff

end Salt.MR

-- #audit (temporary)
