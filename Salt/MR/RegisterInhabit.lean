/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CofactorBulk

/-!
# `RegisterInhabit` — ⟦THE CO-FACTOR REGISTER IS NOT INHABITABLE AS CUT⟧

`CofactorBulk.cofkL_cofactorSupply_L_gk_of_bulk` reduces ⟦RULING 9⟧'s co-factor debt to the
seventeen-conjunct register `CofactorBulkL`.  This file was opened to INHABIT that register at
the terminal's own scale.  It does the opposite, and proves it:

**`CofactorBulkL Cq Xsk Cb Xd T` is FALSE at every scale past a `Cb`-determined threshold —
in particular at every socket of every regime the terminal produces.**

## §1 — THE ARITHMETIC OF THE REFUTATION (three lines, no analysis)

Read the register's own conjuncts at any single block `v` of the band (the band is nonempty
by the register's OWN first conjunct `P ≤ Q`):

* conjunct 12 — `cSq·caseASwide(…) + cSq·1 ≤ S`, and `caseASwide ≥ 0`, so **`S ≥ cSq = 20736`**;
* conjunct 14 — `cofactorRbdGen S … ≤ R̄₀`, and `cofactorRbdGen S W Y Rmax R = 3·max(2S, …)`,
  so **`R̄₀ ≥ 6S ≥ 6·cSq`**;
* conjunct 16 — `4·R̄₀ ≤ C_R₂(Cb)·(log X)^{−ρ₂₉₃}`.

Together: `24·cSq ≤ C_R₂(Cb)·(log X)^{−ρ₂₉₃}`, i.e. `24·cSq·(log X)^{ρ₂₉₃} ≤ C_R₂(Cb)` — a
FIXED constant on the right and an unbounded increasing function of the scale on the left.
The register is therefore satisfiable only below `loglog X ≤ log(C_R₂(Cb)/(24·cSq))/ρ₂₉₃`.
The terminal's own `μ`-floor (`cofkL_mu_floor`: `loglog(A+s) ≥ log H₊ − 14`) puts every socket
of every terminal regime ASTRONOMICALLY above that line (`log H₊ ≥ e^{3.2A} ≥ e^{518}`), so the
`∀`-hypothesis of `cofkL_cofactorSupply_L_gk_of_bulk` is unsatisfiable at the terminal:
the theorem is true and VACUOUS there, and `logChowla2_ineffective_v6` cannot be minted
through it.

## §2 — WHERE THE DEFECT IS: `CofactorBulk` §1's `D(j) = 1`

The defect is NOT in `m4_supplier_complete`, and NOT in the grading.  It is the choice of the
**trivial dilation ladder** `D(j) = 1` in `CofactorBulk` §1.  The supplier's own exit charge is

  `cSq·caseASwide c Cb (cofactorMfl X θ ⌊k₀/D⌋) ⌊k₀/D⌋ (Xa) + cSq·D^{−1/4} ≤ S`

— the second summand is `cSq·D^{−1/4}`, and law #253's ladder gates (`1 ≤ D ≤ k₀`,
`√(Xa) ≤ ⌊k₀/D⌋`) permit `D` up to `≈ √k₀`.  At `D = 1` that summand is the CONSTANT `cSq`,
which floors `S` and hence floors `R̄₀`, and no constant floor can live under a decaying
ceiling.  Everything else in the design is coherent: the three `caseASwide` summands decay at
`(log X)^{−c(1/32−θ₂₉₃)}` (at the pin `c = 1/e` this is EXACTLY `(log X)^{−ρ₂₉₃}`, the identity
`(1/32 − θ₂₉₃)/e = 3·θ₂₉₃` being the whole point of `θ₂₉₃ = 1/(32(3e+1))`),
`(log Xw)^{−1/(32e)}` and `(log Xa)^{−1/2+1/1000}`; and the far arm's
`farSupS34 W Y Rmax R = 2√2/R + farErr34` decays at `(log X)^{−1/46}` (the seam radius) and
`(log X)^{−3/20}` (the `T*₂` numerator against `(log W)^{3/4}`).  All of those beat the
`(log X)^{−2θ₂₉₃}` the predicate demands (§3).

## §3 — WHAT THE PREDICATE ACTUALLY DEMANDS, AND THE PRICE OF THE REPAIR

`S16CofactorSupply_L_gk` does NOT ask for `C_R = gradeCR2 Cb`: its `C_R` is EXISTENTIAL
(`S13CapGateLinear:897`), constrained only by the pair `Rbd ≤ C_R·(log X)^{−ρ₂₉₃}` and
`1728·C_q·C_R² ≤ (log X)^{2θ₂₉₃}`.  Eliminating `C_R` between them (`s16cof_exit_decay`) gives
the register's TRUE law:

  **`Rbd ≤ (log X)^{−2θ₂₉₃}/√(1728·C_q)`** — the exit ceiling must DECAY, at rate `2θ₂₉₃`.

Against the supplier's floor `Rbd ≥ 24·S ≥ 24·cSq·D^{−1/4}` this prices the repair exactly
(`cofk_dilation_price`):

  **`D ≥ (24·cSq)⁴·(1728·C_q)²·(log X)^{8θ₂₉₃}`.**

`8θ₂₉₃ ≈ 0.0273`, so `D := ⌈log X⌉` clears it by a factor `(log X)^{0.97}` — and sits far
under the ladder's own ceiling `√k₀ ≈ X^{1/4}`.  The repair is one wave: re-instantiate
`m4_supplier_complete` at a nontrivial constant ladder, with `C_R` chosen as
`4·R̄₀·(log X)^{ρ₂₉₃}` (a constant, since `R̄₀` decays at exactly that rate) rather than pinned
at `gradeCR2 Cb`.

**PURELY ADDITIVE.**  No landed declaration is touched; `CofactorBulk` still compiles and its
theorems remain true (they are implications whose hypothesis this file refutes).
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — `cSq` and `gradeCR2` as numerals -/

/-- `0 < cSq` (`cSq = 20736`, Route III's price). -/
theorem cofk_cSq_pos : (0 : ℝ) < cSq := by rw [cSq]; norm_num

/-- `0 < gradeCR2 Cb` at any admissible short-interval constant. -/
theorem cofk_gradeCR2_pos {Cb : ℝ} (hCb0 : 0 ≤ Cb) : (0 : ℝ) < gradeCR2 Cb :=
  lt_trans (by norm_num) (one_lt_gradeCR2 hCb0)

/-! ## §1 — ⟦THE REGISTER'S TRUE LAW⟧ THE EXIT CEILING MUST DECAY

`S16CofactorSupply_L_gk`'s two grading conjuncts, with the existential `C_R` eliminated. -/

/-- **⟦THE EXIT CEILING DECAYS AT RATE `2θ₂₉₃`⟧** (`s16cof_exit_decay`).  Whatever `C_R` the
supplier chooses, the pair `Rbd ≤ C_R·(log X)^{−ρ₂₉₃}` and `1728·C_q·C_R² ≤ (log X)^{2θ₂₉₃}`
forces `Rbd·√(1728·C_q) ≤ (log X)^{−2θ₂₉₃}`.  `ρ₂₉₃ = 3θ₂₉₃` is what makes the two exponents
combine to `θ₂₉₃ − ρ₂₉₃ = −2θ₂₉₃`. -/
theorem s16cof_exit_decay {Cq X CR Rbd : ℝ} (hCq : 0 < Cq) (hX : (1 : ℝ) ≤ Real.log X)
    (hg1 : Rbd ≤ CR * (Real.log X) ^ (-rho293))
    (hg2 : 1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293)) :
    Rbd * Real.sqrt (1728 * Cq) ≤ (Real.log X) ^ (-(2 * theta293)) := by
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hcq0 : (0 : ℝ) < 1728 * Cq := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (1728 * Cq) := Real.sqrt_pos.mpr hcq0
  have hsq : Real.sqrt (1728 * Cq) * Real.sqrt (1728 * Cq) = 1728 * Cq :=
    Real.mul_self_sqrt hcq0.le
  -- `C_R ≤ (log X)^{θ₂₉₃}/√(1728·C_q)`
  have hCRb : CR * Real.sqrt (1728 * Cq) ≤ (Real.log X) ^ theta293 := by
    have hsqle : Real.sqrt ((CR * Real.sqrt (1728 * Cq)) ^ 2)
        ≤ Real.sqrt (((Real.log X) ^ theta293) ^ 2) := by
      refine Real.sqrt_le_sqrt ?_
      have hexp : ((Real.log X) ^ theta293) ^ 2 = (Real.log X) ^ (2 * theta293) := by
        rw [← Real.rpow_natCast ((Real.log X) ^ theta293) 2, ← Real.rpow_mul hL0.le]
        norm_num [mul_comm]
      have hlhs : (CR * Real.sqrt (1728 * Cq)) ^ 2 = 1728 * Cq * CR ^ 2 := by
        rw [mul_pow]
        nlinarith [hsq]
      rw [hexp, hlhs]
      exact hg2
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq (Real.rpow_nonneg hL0.le _)] at hsqle
    exact le_trans (le_abs_self _) hsqle
  -- multiply the first grading conjunct by `√(1728·C_q) > 0`
  have hneg : (0 : ℝ) < (Real.log X) ^ (-rho293) := Real.rpow_pos_of_pos hL0 _
  have hstep : Rbd * Real.sqrt (1728 * Cq)
      ≤ (Real.log X) ^ theta293 * (Real.log X) ^ (-rho293) := by
    have h1 : Rbd * Real.sqrt (1728 * Cq)
        ≤ (CR * (Real.log X) ^ (-rho293)) * Real.sqrt (1728 * Cq) :=
      mul_le_mul_of_nonneg_right hg1 hs0.le
    have h2 : (CR * (Real.log X) ^ (-rho293)) * Real.sqrt (1728 * Cq)
        = (CR * Real.sqrt (1728 * Cq)) * (Real.log X) ^ (-rho293) := by ring
    have h3 : (CR * Real.sqrt (1728 * Cq)) * (Real.log X) ^ (-rho293)
        ≤ (Real.log X) ^ theta293 * (Real.log X) ^ (-rho293) :=
      mul_le_mul_of_nonneg_right hCRb hneg.le
    linarith [h1, h2 ▸ h1, h3]
  have hcomb : (Real.log X) ^ theta293 * (Real.log X) ^ (-rho293)
      = (Real.log X) ^ (-(2 * theta293)) := by
    rw [← Real.rpow_add hL0, rho293]
    congr 1
    ring
  linarith [hcomb ▸ hstep]

/-! ## §2 — ⟦THE REFUTATION⟧ -/

/-- The band is nonempty: `⌊H·log P⌋₊` is a block of `ramI H P Q` whenever `P ≤ Q` and
`0 < P`.  (The register's own first conjunct supplies `P ≤ Q`.) -/
theorem cofk_ramI_bot_mem {H : ℝ} {P Q : ℕ} (hH0 : 0 ≤ H) (hP0 : 0 < P) (hPQ : P ≤ Q) :
    ⌊H * Real.log (P : ℝ)⌋₊ ∈ ramI H P Q := by
  rw [ramI, Finset.mem_Icc]
  refine ⟨le_refl _, Nat.floor_le_floor ?_⟩
  have hlog : Real.log (P : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by exact_mod_cast hP0) (by exact_mod_cast hPQ)
  exact mul_le_mul_of_nonneg_left hlog hH0

/-- **⟦THE REGISTER FLOORS ITS OWN CEILING⟧** (`cofkL_bulk_grade_floor`).  Conjuncts 12, 14
and 16 of `CofactorBulkL`, read at the band's bottom block: `24·cSq ≤ C_R₂(Cb)·(log X)^{−ρ₂₉₃}`.
The left side is a fixed positive numeral (`24·20736 = 497664`); the right side tends to `0`. -/
theorem cofkL_bulk_grade_floor {Cq Xsk Cb : ℝ} {Xd : ℕ} {T : ℝ}
    (hCb0 : 0 ≤ Cb) (hX : Real.exp 1 ≤ Real.log (Xd : ℝ))
    (hreg : CofactorBulkL Cq Xsk Cb Xd T) :
    24 * cSq ≤ gradeCR2 Cb * (Real.log (Xd : ℝ)) ^ (-rho293) := by
  obtain ⟨S, Rbar0, hPQ, -, -, hkth, -, -, -, -, -, -, -, hSbdr, -, hRbdUr, -,
    hRgrade, -⟩ := hreg
  have he1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hL0 : (0 : ℝ) < Real.log (Xd : ℝ) := by linarith
  -- the band's bottom block
  have hH0 : (0 : ℝ) ≤ H83 (Xd : ℝ) theta293 := by
    rw [H83]; exact Real.rpow_nonneg hL0.le _
  have hP0 : 0 < s13BandP Xd := by
    rw [s13BandP]
    exact Nat.ceil_pos.mpr (by rw [P83]; exact Real.exp_pos _)
  have hmem := cofk_ramI_bot_mem (H := H83 (Xd : ℝ) theta293) hH0 hP0 hPQ
  set v : ℕ := ⌊H83 (Xd : ℝ) theta293 * Real.log ((s13BandP Xd : ℕ) : ℝ)⌋₊ with hvdef
  -- the two window floors, off the register's own C7 gate
  have hB5 : (5 : ℝ) ≤ ramRbot (H83 (Xd : ℝ) theta293) Xd v :=
    cofkL_five_le_ramRbot (hkth v hmem)
  have hkk1 : 1 ≤ witKk (H83 (Xd : ℝ) theta293) Xd v := cofkL_one_le_kk hB5
  have hkkR : (1 : ℝ) ≤ ((witKk (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ) := by
    exact_mod_cast hkk1
  -- ⟦S ≥ cSq⟧ — the wide exit's constant summand at the trivial ladder
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have hcase0 : (0 : ℝ) ≤ caseASwide (1 / Real.exp 1) Cb
      (cofactorMfl (Xd : ℝ) theta293 ((witKk (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ))
      ((witKk (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)
      (ramRbot (H83 (Xd : ℝ) theta293) Xd v) :=
    caseASwide_nonneg hc1 hCb0 hkkR (by linarith)
  have hcSq0 := cofk_cSq_pos
  have hScSq : cSq ≤ S := by
    have h := hSbdr v hmem
    nlinarith [hcase0, hcSq0]
  -- ⟦R̄₀ ≥ 6S⟧ — `cofactorRbdGen` is `3·max(2S, …)`
  have h6S : 6 * S ≤ Rbar0 := by
    have h := hRbdUr v hmem
    rw [cofactorRbdGen] at h
    have hmax : 2 * S ≤ max (2 * S)
        (farSupS34 ((witKk (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad (Xd : ℝ))) := le_max_left _ _
    linarith
  linarith

/-- **⟦THE REGISTER IS FALSE PAST THE `Cb`-THRESHOLD⟧** (`cofkL_bulk_infeasible`). -/
theorem cofkL_bulk_infeasible {Cq Xsk Cb : ℝ} {Xd : ℕ} {T : ℝ}
    (hCb0 : 0 ≤ Cb) (hX : Real.exp 1 ≤ Real.log (Xd : ℝ))
    (hbig : gradeCR2 Cb < 24 * cSq * (Real.log (Xd : ℝ)) ^ rho293) :
    ¬ CofactorBulkL Cq Xsk Cb Xd T := by
  intro hreg
  have h := cofkL_bulk_grade_floor hCb0 hX hreg
  have he1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hL0 : (0 : ℝ) < Real.log (Xd : ℝ) := by linarith
  have hpos : (0 : ℝ) < (Real.log (Xd : ℝ)) ^ rho293 := Real.rpow_pos_of_pos hL0 _
  rw [Real.rpow_neg hL0.le] at h
  -- `24·cSq ≤ C_R₂·(L^ρ)⁻¹` multiplied by `L^ρ > 0`
  have hmul : 24 * cSq * (Real.log (Xd : ℝ)) ^ rho293
      ≤ gradeCR2 Cb * ((Real.log (Xd : ℝ)) ^ rho293)⁻¹ * (Real.log (Xd : ℝ)) ^ rho293 :=
    mul_le_mul_of_nonneg_right h hpos.le
  rw [inv_mul_cancel_right₀ (ne_of_gt hpos)] at hmul
  linarith

/-- **⟦THE THRESHOLD IN `loglog` FORM⟧** (`cofkL_bulk_infeasible_loglog`).  The scale gate of
`cofkL_bulk_infeasible`, stated where the terminal reads it: `loglog X` past
`log(C_R₂(Cb)/(24·cSq))/ρ₂₉₃`. -/
theorem cofkL_bulk_infeasible_loglog {Cq Xsk Cb : ℝ} {Xd : ℕ} {T : ℝ}
    (hCb0 : 0 ≤ Cb) (hX : Real.exp 1 ≤ Real.log (Xd : ℝ))
    (hthr : Real.log (gradeCR2 Cb)
      < Real.log (24 * cSq) + rho293 * Real.log (Real.log (Xd : ℝ))) :
    ¬ CofactorBulkL Cq Xsk Cb Xd T := by
  refine cofkL_bulk_infeasible hCb0 hX ?_
  have he1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hL0 : (0 : ℝ) < Real.log (Xd : ℝ) := by linarith
  have hg0 : (0 : ℝ) < gradeCR2 Cb := cofk_gradeCR2_pos hCb0
  have hcSq0 := cofk_cSq_pos
  have h24 : (0 : ℝ) < 24 * cSq := by linarith
  -- exponentiate the threshold
  have hrp : (Real.log (Xd : ℝ)) ^ rho293
      = Real.exp (rho293 * Real.log (Real.log (Xd : ℝ))) := by
    rw [Real.rpow_def_of_pos hL0]
    congr 1
    ring
  have hexp : Real.exp (Real.log (gradeCR2 Cb))
      < Real.exp (Real.log (24 * cSq) + rho293 * Real.log (Real.log (Xd : ℝ))) :=
    Real.exp_lt_exp.mpr hthr
  rw [Real.exp_log hg0, Real.exp_add, Real.exp_log h24] at hexp
  rw [hrp]
  exact hexp

/-! ## §3 — ⟦THE REFUTATION AT THE TERMINAL'S OWN SOCKET⟧ -/

/-- **⟦THE BULK HYPOTHESIS IS FALSE AT EVERY TERMINAL SOCKET⟧**
(`cofkL_bulk_false_at_socket`).  `cofkL_mu_floor` puts `loglog(A+s) ≥ log H₊ − 14` at every
socket of every regime carrying the terminal's exports; past the `Cb`-threshold the register
cannot hold, FOR ANY `T`.  Since `cofkL_cofactorSupply_L_gk_of_bulk` consumes the register at
exactly these sockets, its `∀`-hypothesis is unsatisfiable there. -/
theorem cofkL_bulk_false_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ} {Cq Xsk Cb : ℝ}
    (hb : SocketBaseL R M H L q j A s)
    (hε : (1 : ℝ) / 500 ≤ (R.eps : ℝ))
    (hlo : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hCb0 : 0 ≤ Cb)
    (hthr : Real.log (gradeCR2 Cb)
      < Real.log (24 * cSq) + rho293 * (Real.log (R.Hhi : ℝ) - 14)) :
    ∀ T : ℝ, ¬ CofactorBulkL Cq Xsk Cb (A + s) T := by
  intro T
  obtain ⟨hH4, hHhi14⟩ := cofkL_socket_floors hb hlo
  have hXee : Real.exp (Real.exp 1) ≤ (((A + s : ℕ)) : ℝ) :=
    cofkL_X_ge_expexp hb hε hHhi14 hH4
  have hLX : Real.exp 1 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 1)) hXee
    rwa [Real.log_exp] at h
  have hmu := cofkL_mu_floor hb hε hHhi14 hH4
  have hrho0 : (0 : ℝ) < rho293 := by
    rw [rho293]; linarith [theta293_pos]
  have hmul : rho293 * (Real.log (R.Hhi : ℝ) - 14)
      ≤ rho293 * Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    mul_le_mul_of_nonneg_left hmu hrho0.le
  exact cofkL_bulk_infeasible_loglog hCb0 hLX (by linarith)

/-! ## §4 — ⟦THE SCALE FACTS THE REPAIR WILL RE-USE⟧

Four of the register's seventeen conjuncts are pure scale facts at the band, and they hold at
the terminal's socket by an astronomical margin.  They are proved here at a FREE block scale
(with the gate stated, law #253) so the repaired register can consume them verbatim. -/

/-- **⟦THE WINDOW BOTTOM IS `≥ √X` ACROSS THE WHOLE BAND⟧** (`cofk_sqrt_le_ramRbot`).  Every
block index of `ramI H P Q` sits at or below `⌊H·log Q⌋₊`, so `B_v = X·e^{−v/H} ≥ X/Q`; and the
band's top endpoint obeys `log Q ≤ log X/loglog X ≤ log X/2`.  Hence `B_v ≥ e^{log X/2} = √X`
at every block.  This single fact carries the C7 gate, the `X₀` threshold, the seam radius and
the `loglog` descent charge. -/
theorem cofk_sqrt_le_ramRbot {Xd P Q v : ℕ} {H : ℝ} (hH0 : 0 < H) (hQ1 : 1 ≤ Q)
    (hQhigh : ((Q : ℕ) : ℝ) ≤ Q83 ((Xd : ℕ) : ℝ))
    (hLe2 : Real.exp 2 ≤ Real.log ((Xd : ℕ) : ℝ))
    (hv : v ∈ ramI H P Q) :
    Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) ≤ ramRbot H Xd v := by
  -- the scale: `log X ≥ e² > 0`, hence `loglog X ≥ 2`
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLpos : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hLL2 : (2 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos 2) hLe2
    rwa [Real.log_exp] at h
  have hLL0 : (0 : ℝ) < Real.log (Real.log ((Xd : ℕ) : ℝ)) := by linarith
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := by
    rcases lt_or_ge (0 : ℝ) ((Xd : ℕ) : ℝ) with h | h
    · exact h
    · exfalso
      have hz : ((Xd : ℕ) : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
      rw [hz, Real.log_zero] at hLpos
      linarith
  -- the band's top endpoint
  have hQlog : Real.log ((Q : ℕ) : ℝ)
      ≤ Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ)) :=
    log_le_of_le_Q83 hQ1 hQhigh
  have hQhalf : Real.log ((Q : ℕ) : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) / 2 := by
    have hdiv : Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ))
        ≤ Real.log ((Xd : ℕ) : ℝ) / 2 := by
      rw [div_le_div_iff₀ hLL0 (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hLpos, hLL2]
    linarith
  -- the block index
  rw [ramI, Finset.mem_Icc] at hv
  have hQ1R : (1 : ℝ) ≤ ((Q : ℕ) : ℝ) := by exact_mod_cast hQ1
  have hlogQ0 : (0 : ℝ) ≤ Real.log ((Q : ℕ) : ℝ) := Real.log_nonneg hQ1R
  have hvR : (v : ℝ) ≤ H * Real.log ((Q : ℕ) : ℝ) := by
    have h1 : ((⌊H * Real.log ((Q : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) ≤ H * Real.log ((Q : ℕ) : ℝ) :=
      Nat.floor_le (by positivity)
    have h2 : (v : ℝ) ≤ ((⌊H * Real.log ((Q : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hv.2
    linarith
  have hvH : (v : ℝ) / H ≤ Real.log ((Xd : ℕ) : ℝ) / 2 := by
    rw [div_le_iff₀ hH0]
    nlinarith [hvR, mul_le_mul_of_nonneg_left hQhalf hH0.le]
  -- the exponential
  have hrw : ((Xd : ℕ) : ℝ) * Real.exp (-(v : ℝ) / H)
      = Real.exp (Real.log ((Xd : ℕ) : ℝ) + (-(v : ℝ) / H)) := by
    rw [Real.exp_add, Real.exp_log hX0]
  rw [ramRbot, hrw]
  refine Real.exp_le_exp.mpr ?_
  rw [neg_div]
  linarith

/-- **⟦THE C7 GATE AT THE BAND⟧** (`cofk_ballQuarter_at_band`).  `e^{e^{165}} + 1 ≤ √X` once
`log X ≥ 2·e^{165} + 2` — which the terminal's `μ`-floor beats by a full exponential level
(`log X ≥ H₊/10⁶ ≥ e^{e^{518}}/10⁶`). -/
theorem cofk_ballQuarter_at_band {Xd P Q v : ℕ} {H : ℝ} (hH0 : 0 < H) (hQ1 : 1 ≤ Q)
    (hQhigh : ((Q : ℕ) : ℝ) ≤ Q83 ((Xd : ℕ) : ℝ))
    (hbig : 2 * Real.exp 165 + 2 ≤ Real.log ((Xd : ℕ) : ℝ))
    (hv : v ∈ ramI H P Q) :
    ballQuarterThreshold + 1 ≤ ramRbot H Xd v := by
  have hle : Real.exp 2 ≤ Real.exp 165 := Real.exp_le_exp.mpr (by norm_num)
  have hpos : (0 : ℝ) < Real.exp 165 := Real.exp_pos _
  have hbot := cofk_sqrt_le_ramRbot hH0 hQ1 hQhigh (by linarith) hv
  have hstep : Real.exp (Real.exp 165 + 1) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod : Real.exp (Real.exp 165 + 1) = Real.exp (Real.exp 165) * Real.exp 1 := by
    rw [← Real.exp_add]
  have h1 : (1 : ℝ) ≤ Real.exp (Real.exp 165) := Real.one_le_exp (Real.exp_pos 165).le
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hgap : Real.exp (Real.exp 165) + 1 ≤ Real.exp (Real.exp 165) * Real.exp 1 := by
    nlinarith [h1, he]
  rw [ballQuarterThreshold]
  linarith [hprod ▸ hstep]

/-- **⟦THE SUPPLIER'S OPAQUE WIDE THRESHOLD, ABSORBED⟧** (`cofk_wideThreshold_at_band`).
`X₀ ≤ √(B_v)` holds as soon as `X₀ ≤ e^{log X/4}` — and `X₀` is minted by
`m4_supplier_complete` OUTSIDE every quantifier, so the terminal's own design constant `A`
(chosen after it) absorbs it. -/
theorem cofk_wideThreshold_at_band {Xsk : ℝ} {Xd P Q v : ℕ} {H : ℝ} (hH0 : 0 < H) (hQ1 : 1 ≤ Q)
    (hQhigh : ((Q : ℕ) : ℝ) ≤ Q83 ((Xd : ℕ) : ℝ))
    (hLe2 : Real.exp 2 ≤ Real.log ((Xd : ℕ) : ℝ))
    (hXsk : Xsk ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4))
    (hv : v ∈ ramI H P Q) :
    Xsk ≤ Real.sqrt (ramRbot H Xd v) := by
  have hbot := cofk_sqrt_le_ramRbot hH0 hQ1 hQhigh hLe2 hv
  have hsq : Real.sqrt (Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2))
      = Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) := by
    rw [show Real.log ((Xd : ℕ) : ℝ) / 2
        = Real.log ((Xd : ℕ) : ℝ) / 4 + Real.log ((Xd : ℕ) : ℝ) / 4 by ring,
      Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  have hmono : Real.sqrt (Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)) ≤ Real.sqrt (ramRbot H Xd v) :=
    Real.sqrt_le_sqrt hbot
  rw [hsq] at hmono
  linarith

/-- **⟦THE SEAM RADIUS AT THE BAND⟧** (`cofk_seamRad_at_band`).  `seamRad X = (log X)^{1/46}`
sits under `log X ≤ e^{log X/2} ≤ B_v`, hence under `√2·B_v`. -/
theorem cofk_seamRad_at_band {Xd P Q v : ℕ} {H : ℝ} (hH0 : 0 < H) (hQ1 : 1 ≤ Q)
    (hQhigh : ((Q : ℕ) : ℝ) ≤ Q83 ((Xd : ℕ) : ℝ))
    (hL16 : (16 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ))
    (hv : v ∈ ramI H P Q) :
    seamRad ((Xd : ℕ) : ℝ) ≤ Real.sqrt 2 * ramRbot H Xd v := by
  have he2 : Real.exp 2 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have hbot := cofk_sqrt_le_ramRbot hH0 hQ1 hQhigh he2 hv
  -- `(log X)^{1/46} ≤ log X`
  have hrp : (Real.log ((Xd : ℕ) : ℝ)) ^ ((1 : ℝ) / 46) ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h1 : (Real.log ((Xd : ℕ) : ℝ)) ^ ((1 : ℝ) / 46)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rwa [Real.rpow_one] at h1
  -- `log X ≤ e^{log X/2}` off the square of `1 + u ≤ e^u`
  have hquad : Real.log ((Xd : ℕ) : ℝ) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := by
    have h1 : 1 + Real.log ((Xd : ℕ) : ℝ) / 4 ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) :=
      by linarith [Real.add_one_le_exp (Real.log ((Xd : ℕ) : ℝ) / 4)]
    have h2 : Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)
        = Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) * Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [h1, h2, hL16]
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
    rwa [Real.sqrt_one] at h
  have hB0 : (0 : ℝ) ≤ ramRbot H Xd v := by
    have := Real.exp_pos (Real.log ((Xd : ℕ) : ℝ) / 2)
    linarith
  have hfin : ramRbot H Xd v ≤ Real.sqrt 2 * ramRbot H Xd v := by nlinarith [hs2, hB0]
  rw [seamRad]
  linarith

/-- **⟦THE `loglog` DESCENT CHARGE AT THE BAND⟧** (`cofk_descent_at_band`).  `B_v ≥ √X` gives
`loglog(B_v − 1) ≥ loglog X − log 4`, so the charge's left side is `≤ 18 + log 4 < 19.4`, while
its right side is `32·θ₂₉₃·loglog X ≥ loglog X/10` (`32·θ₂₉₃ = 1/(3e+1) ≥ 1/10`).  The gate is
therefore `loglog X ≥ 194` — against the terminal's own `loglog X ≥ e^{518} − 14`. -/
theorem cofk_descent_at_band {Xd P Q v : ℕ} {H : ℝ} (hH0 : 0 < H) (hQ1 : 1 ≤ Q)
    (hQhigh : ((Q : ℕ) : ℝ) ≤ Q83 ((Xd : ℕ) : ℝ))
    (hLL : (194 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)))
    (hL16 : (16 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ))
    (hv : v ∈ ramI H P Q) :
    18 + Real.log (Real.log ((Xd : ℕ) : ℝ)) - Real.log (Real.log (ramRbot H Xd v - 1))
      ≤ 32 * theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)) := by
  have he2 : Real.exp 2 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have hbot := cofk_sqrt_le_ramRbot hH0 hQ1 hQhigh he2 hv
  set L : ℝ := Real.log ((Xd : ℕ) : ℝ) with hLdef
  -- `e^{L/4} ≤ e^{L/2} − 1 ≤ B_v − 1`
  have hq : Real.exp (L / 2) = Real.exp (L / 4) * Real.exp (L / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp 4 ≤ Real.exp (L / 4) := Real.exp_le_exp.mpr (by linarith)
  have h4n : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hstep : Real.exp (L / 4) ≤ ramRbot H Xd v - 1 := by nlinarith [hq, h4, h4n, hbot]
  -- `log(B−1) ≥ L/4` and `loglog(B−1) ≥ loglog X − log 4`
  have hlogB : L / 4 ≤ Real.log (ramRbot H Xd v - 1) := by
    have h := Real.log_le_log (Real.exp_pos (L / 4)) hstep
    rwa [Real.log_exp] at h
  have hL4pos : (0 : ℝ) < L / 4 := by linarith
  have hlogdiv : Real.log (L / 4) = Real.log L - Real.log 4 := by
    rw [Real.log_div (by linarith) (by norm_num)]
  have hll : Real.log L - Real.log 4 ≤ Real.log (Real.log (ramRbot H Xd v - 1)) := by
    have h := Real.log_le_log hL4pos hlogB
    rwa [hlogdiv] at h
  -- `32·θ₂₉₃ ≥ 1/10`
  have hthe : (1 : ℝ) / 10 ≤ 32 * theta293 := by
    rw [theta293]
    have he : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
    have hpos : (0 : ℝ) < 3 * Real.exp 1 + 1 := by linarith [Real.exp_pos (1 : ℝ)]
    have heq : 32 * (1 / (32 * (3 * Real.exp 1 + 1))) = 1 / (3 * Real.exp 1 + 1) := by
      field_simp
    rw [heq]
    exact one_div_le_one_div_of_le hpos (by linarith)
  have hlog4 : Real.log 4 ≤ 1.4 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have hLL0 : (0 : ℝ) ≤ Real.log L := by linarith
  nlinarith [hthe, hll, hlog4, hLL, hLL0]

/-! ## §5 — ⟦THE PRICE OF THE REPAIR⟧ -/

/-- `a·b⁻¹ ≤ c⁻¹ → a·c ≤ b` at positive `b`, `c` — the two inverses cleared in one step. -/
private lemma cofk_inv_chain {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) (h : a * b⁻¹ ≤ c⁻¹) :
    a * c ≤ b := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have h2 := mul_le_mul_of_nonneg_right h (mul_pos hb hc).le
  have e1 : a * b⁻¹ * (b * c) = a * c := by field_simp
  have e2 : c⁻¹ * (b * c) = b := by field_simp
  rw [e1, e2] at h2
  exact h2

/-- **⟦THE DILATION LADDER'S PRICE⟧** (`cofk_dilation_price`).  The supplier's own exit charge
carries the summand `cSq·D^{−1/4}` (`m4_supplier_complete`'s `hSbd`), and the socket's exit is
`Rbd = 2^J·R̄₀ = 4·R̄₀ ≥ 24·S`.  Against §1's decay law this forces

  `24·cSq·√(1728·C_q)·(log X)^{2θ₂₉₃} ≤ D^{1/4}`,

i.e. `D ≳ (log X)^{8θ₂₉₃}`.  `D = 1` (the ladder `CofactorBulk` §1 chose) violates it at every
scale past a fixed threshold; `D = ⌈log X⌉` clears it by `(log X)^{1−8θ₂₉₃}` and stays far under
law #253's own ceiling `D ≲ √k₀`. -/
theorem cofk_dilation_price {Cq X S Rbd CR D : ℝ} (hCq : 0 < Cq) (hX : (1 : ℝ) ≤ Real.log X)
    (hD : 1 ≤ D)
    (hS : cSq * D ^ (-(1 / 4 : ℝ)) ≤ S)
    (hRbd : 24 * S ≤ Rbd)
    (hg1 : Rbd ≤ CR * (Real.log X) ^ (-rho293))
    (hg2 : 1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293)) :
    24 * cSq * Real.sqrt (1728 * Cq) * (Real.log X) ^ (2 * theta293) ≤ D ^ ((1 : ℝ) / 4) := by
  have hdecay := s16cof_exit_decay hCq hX hg1 hg2
  have hD0 : (0 : ℝ) < D := by linarith
  have hcq0 : (0 : ℝ) < 1728 * Cq := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (1728 * Cq) := Real.sqrt_pos.mpr hcq0
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hD4 : (0 : ℝ) < D ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hD0 _
  have hT0 : (0 : ℝ) < (Real.log X) ^ (2 * theta293) := Real.rpow_pos_of_pos hL0 _
  -- `D^{−1/4} = (D^{1/4})⁻¹`, `(log X)^{−2θ} = ((log X)^{2θ})⁻¹`
  have hDinv : D ^ (-(1 / 4 : ℝ)) = (D ^ ((1 : ℝ) / 4))⁻¹ := by
    rw [show (-(1 / 4 : ℝ)) = -((1 : ℝ) / 4) by norm_num, Real.rpow_neg hD0.le]
  have hTinv : (Real.log X) ^ (-(2 * theta293)) = ((Real.log X) ^ (2 * theta293))⁻¹ := by
    rw [Real.rpow_neg hL0.le]
  -- chain: `(24·cSq·√(1728C_q))·(D^{1/4})⁻¹ ≤ Rbd·√(1728C_q) ≤ ((log X)^{2θ})⁻¹`
  have hchain : (24 * cSq * Real.sqrt (1728 * Cq)) * (D ^ ((1 : ℝ) / 4))⁻¹
      ≤ ((Real.log X) ^ (2 * theta293))⁻¹ := by
    have h1 : 24 * (cSq * D ^ (-(1 / 4 : ℝ))) ≤ Rbd := by linarith
    have h2 : 24 * (cSq * D ^ (-(1 / 4 : ℝ))) * Real.sqrt (1728 * Cq)
        ≤ Rbd * Real.sqrt (1728 * Cq) := mul_le_mul_of_nonneg_right h1 hs0.le
    have h3 : 24 * (cSq * D ^ (-(1 / 4 : ℝ))) * Real.sqrt (1728 * Cq)
        = (24 * cSq * Real.sqrt (1728 * Cq)) * (D ^ ((1 : ℝ) / 4))⁻¹ := by
      rw [hDinv]; ring
    rw [h3] at h2
    rw [hTinv] at hdecay
    linarith
  exact cofk_inv_chain hD4 hT0 hchain

end Salt.MR

end
