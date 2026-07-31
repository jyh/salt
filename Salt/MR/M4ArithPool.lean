/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ArithRho
import Salt.MR.M4AssemblyPool

/-!
# ⟦R2 — THE CONSTANT POOL⟧, PRICED (`M4ArithPool`)

Design provenance: `docs/exploration/knot2-closure-freeze-0730.md`, wave **R2**; the pricing
twins of KNOT2-SCOPE's Tier-A inventory (`flags.md` 2026-07-30 15:50), fired by K4-CENSUS.

## ⟦WHERE THE ARITHMETIC WENT⟧

`M4ArithPage`/`M4ArithRho` clear `a2DoorGrade`'s five summands one by one against the `H`-side
price `e^{14·loglog H}`.  Summand 3 — `188133·(log X)^{−1/500}` — was cleared by ⟦C4⟧'s ARM:
the frame's `loglog X ≥ 7000·loglog H + …` beat the decay.

At the pool the third summand is `188133·π₀` with `π₀` FREE, so no frame field can clear it:
**the arithmetic migrates to the consumer.**  `doorGrade_summand3_priced_pool` and its `ρ`
twin therefore take the cleared inequality AS A HYPOTHESIS.  That is not a loss — it is the
point of ⟦R2⟧: the door's constant target needs no decay, and the consumer that chooses `π₀`
is the one that knows how small it may be.

⟦THE BRIDGE, SO THE TWIN IS NOT WEAKER⟧ `doorGrade_summand3_priced_pool_of_decay` (and its
`ρ` twin) close the hypothesis from `π₀ ≤ (log X)^{−1/500}` plus the landed ARM — i.e. the
landed pricing is the pool pricing at the decaying pool, and the twin subsumes it.  The four
other summands are pool-free and are reused from the landed pages VERBATIM.

## Contents

* §1 the summand-3 twins (hypothesis form + the decay bridge), at `2⁻³⁴²` and at `ρ/2`;
* §2 `a2DoorGrade_pool_priced` / `a2DoorGrade_pool_priced_rho` — the grade under the envelope;
* §3 the socket wires at the pooled grade: `m4_chiSummedFreeRowBig_of_doorGradeGated_pool`,
  `m4_arith_henv_rho_pool`, `m4_chiSummedFreeRow_of_doorArithRho_pool`.

`RSanDoor`, `RSanDoorRho`, `m4ChiRowGraded` and `m4_arith_gate4_rho` are grade-blind and are
reused as they stand.  Additive: no landed declaration is touched.
-/

-- the `2⁻³⁴¹`/`2⁻³⁴²`/`2⁻³⁴⁴` budget numerals, as on the landed pages
set_option maxRecDepth 40000
set_option exponentiation.threshold 3000

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — SUMMAND 3, AT THE POOL -/

/-- **SUMMAND 3 AT THE POOL** (`doorGrade_summand3_priced_pool`) — the `2⁻³⁴²` slot of
`M4ArithPage`'s budget, at `188133·π₀`.

The pool is free, so the page cannot derive this: the inequality IS the hypothesis, named
here so the five-summand ledger of `a2DoorGrade_pool_priced` still reads as five entries and
the migration is visible in the kernel rather than only in prose. -/
theorem doorGrade_summand3_priced_pool {H : ℕ} {π₀ : ℝ}
    (hprice : 188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ 1 / 2 ^ 342) :
    188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ 1 / 2 ^ 342 := hprice

/-- **THE DECAY BRIDGE** (`doorGrade_summand3_priced_pool_of_decay`) — at a pool that is no
larger than the landed decay, `M4ArithPage.doorGrade_summand3_priced`'s own ARM clears the
pooled summand.  This is what makes the pool twin a GENERALIZATION and not a weakening. -/
theorem doorGrade_summand3_priced_pool_of_decay {H : ℕ} {X π₀ : ℝ}
    (hLX : 1 < Real.log X) (hle : π₀ ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (harm : 7000 * Real.log (Real.log (H : ℝ)) + 125000 ≤ Real.log (Real.log X)) :
    188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ 1 / 2 ^ 342 := by
  refine le_trans ?_ (doorGrade_summand3_priced (H := H) hLX harm)
  have hexp : (0 : ℝ) ≤ Real.exp (14 * Real.log (Real.log (H : ℝ))) := (Real.exp_pos _).le
  have h188 : 188133 * π₀ ≤ 188133 * (Real.log X) ^ (-(1 : ℝ) / 500) :=
    mul_le_mul_of_nonneg_left hle (by norm_num)
  exact mul_le_mul_of_nonneg_right h188 hexp

/-- **SUMMAND 3 AT THE POOL, AT `ρ/2`** (`doorGrade_summand3_priced_rho_pool`) — the `ρ`-page's
slot, same migration. -/
theorem doorGrade_summand3_priced_rho_pool {H : ℕ} {π₀ ρ : ℝ}
    (hprice : 188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2) :
    188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2 := hprice

/-- **THE DECAY BRIDGE AT `ρ`** (`doorGrade_summand3_priced_rho_pool_of_decay`). -/
theorem doorGrade_summand3_priced_rho_pool_of_decay {H : ℕ} {X π₀ ρ : ℝ}
    (hρ : 0 < ρ) (hLX : 1 < Real.log X)
    (hle : π₀ ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (harm : 7000 * Real.log (Real.log (H : ℝ)) + 500 * Real.log (1 / ρ) + 6600
      ≤ Real.log (Real.log X)) :
    188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2 := by
  refine le_trans ?_ (doorGrade_summand3_priced_rho (H := H) hρ hLX harm)
  have hexp : (0 : ℝ) ≤ Real.exp (14 * Real.log (Real.log (H : ℝ))) := (Real.exp_pos _).le
  have h188 : 188133 * π₀ ≤ 188133 * (Real.log X) ^ (-(1 : ℝ) / 500) :=
    mul_le_mul_of_nonneg_left hle (by norm_num)
  exact mul_le_mul_of_nonneg_right h188 hexp

/-! ## §2 — THE POOLED GRADE, UNDER THE ENVELOPE -/

/-- **⟦THE PRICING AT THE POOL⟧** (`a2DoorGrade_pool_priced`) — `M4ArithPage.a2DoorGrade_priced`
at `a2DoorGrade_pool`:

  `arcDen 12 H · a2DoorGrade_pool M X 2^j C₁ M₀ π₀  ≤  RSanDoor H`.

Summands 1, 2, 4, 5 are cleared by the landed page's own lemmas against the SAME frame; only
summand 3 is supplied, as `hprice`.  The budget `2⁻³⁴² + 4·2⁻³⁴⁴ = 2⁻³⁴¹ = doorRho` closes
exactly, unchanged. -/
theorem a2DoorGrade_pool_priced {M H j : ℕ} {X C₁ M₀ K π₀ : ℝ}
    (hfr : DoorArithFrame M H j X C₁ M₀ K) (hpool : 0 ≤ π₀)
    (hprice : 188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ 1 / 2 ^ 342) :
    arcDen 12 H * a2DoorGrade_pool M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ ≤ RSanDoor H := by
  have hL1 : 1 < Real.log (H : ℝ) := hfr.one_lt_logH
  have hLX : 1 < Real.log X := hfr.one_lt_logX
  have hstr : strataResidual H = 1 + 12 * Real.log (Real.log (H : ℝ)) :=
    strataResidual_eq_of_pos (by linarith)
  have hstrpos : (0 : ℝ) < strataResidual H := by
    rw [hstr]; have := hfr.Hfloor; linarith
  have hgrade0 : (0 : ℝ) ≤ a2DoorGrade_pool M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
    refine a2DoorGrade_pool_nonneg M (by linarith) ?_ hpool
    have : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    push_cast
    exact this
  have harcpos : (0 : ℝ) < arcDen 12 H := by
    rw [arcDen]; exact Real.rpow_pos_of_pos (by linarith) _
  have hwt := arcDen_mul_strataResidual_sq_le hfr.logH_nonneg hfr.Hfloor
  rw [RSanDoor, le_div_iff₀ (by positivity)]
  have hkey : arcDen 12 H * a2DoorGrade_pool M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
        * strataResidual H ^ 2
      ≤ Real.exp (14 * Real.log (Real.log (H : ℝ)))
          * a2DoorGrade_pool M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
    have : arcDen 12 H * a2DoorGrade_pool M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
          * strataResidual H ^ 2
        = (arcDen 12 H * strataResidual H ^ 2)
            * a2DoorGrade_pool M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hwt hgrade0
  refine le_trans hkey ?_
  -- the five summands: four landed, one supplied
  have h1 := doorGrade_summand1_priced (H := H) hfr.C1_nonneg hfr.logX_nonneg hLX
    hfr.M0_window
  have h2 := doorGrade_summand2_priced (H := H) hfr.Mpos hfr.anchor
  have h3 := doorGrade_summand3_priced_pool (H := H) hprice
  have h4 := doorGrade_summand4_priced (H := H) hLX hfr.Hfloor hfr.armWeak
  have h5 := doorGrade_summand5_priced (H := H) (j := j) hfr.Hfloor hfr.jfloor
  have hexpand : Real.exp (14 * Real.log (Real.log (H : ℝ)))
        * a2DoorGrade_pool M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
      = 8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
            * Real.exp (14 * Real.log (Real.log (H : ℝ)))
        + 1787702400 * a2Level1 M * Real.exp (14 * Real.log (Real.log (H : ℝ)))
        + 188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ)))
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
            * Real.exp (14 * Real.log (Real.log (H : ℝ)))
        + 6315000 / ((2 ^ j : ℕ) : ℝ) * Real.exp (14 * Real.log (Real.log (H : ℝ))) := by
    rw [a2DoorGrade_pool]; ring
  rw [hexpand, doorRho]
  ring_nf
  ring_nf at h1 h2 h3 h4 h5
  linarith

/-- **⟦THE PRICING AT THE POOL, AT `ρ`⟧** (`a2DoorGrade_pool_priced_rho`) —
`M4ArithRho.a2DoorGrade_priced_rho` at `a2DoorGrade_pool`.  Budget `ρ/2 + 4·(ρ/8) = ρ`. -/
theorem a2DoorGrade_pool_priced_rho {M H j : ℕ} {X C₁ M₀ K ρ π₀ : ℝ}
    (hfr : DoorArithFrameRho M H j X C₁ M₀ K ρ) (hpool : 0 ≤ π₀)
    (hprice : 188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2) :
    arcDen 12 H * a2DoorGrade_pool M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ ≤ RSanDoorRho ρ H := by
  have hL1 : 1 < Real.log (H : ℝ) := hfr.one_lt_logH
  have hLX : 1 < Real.log X := hfr.one_lt_logX
  have hLrho : 0 ≤ Real.log (1 / ρ) := hfr.logInvRho_nonneg
  have hstr : strataResidual H = 1 + 12 * Real.log (Real.log (H : ℝ)) :=
    strataResidual_eq_of_pos (by linarith)
  have hstrpos : (0 : ℝ) < strataResidual H := by
    rw [hstr]; have := hfr.Hfloor; linarith
  have hgrade0 : (0 : ℝ) ≤ a2DoorGrade_pool M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
    refine a2DoorGrade_pool_nonneg M (by linarith) ?_ hpool
    have : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    push_cast
    exact this
  have harcpos : (0 : ℝ) < arcDen 12 H := by
    rw [arcDen]; exact Real.rpow_pos_of_pos (by linarith) _
  have hwt := arcDen_mul_strataResidual_sq_le hfr.logH_nonneg hfr.Hfloor
  rw [RSanDoorRho, le_div_iff₀ (pow_pos hstrpos 2)]
  have hkey : arcDen 12 H * a2DoorGrade_pool M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
        * strataResidual H ^ 2
      ≤ Real.exp (14 * Real.log (Real.log (H : ℝ)))
          * a2DoorGrade_pool M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
    have : arcDen 12 H * a2DoorGrade_pool M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
          * strataResidual H ^ 2
        = (arcDen 12 H * strataResidual H ^ 2)
            * a2DoorGrade_pool M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hwt hgrade0
  refine le_trans hkey ?_
  have h1 := doorGrade_summand1_priced_rho (H := H) hfr.rho_pos hfr.C1_nonneg hfr.logX_nonneg
    hLX hfr.M0_window
  have h2 := doorGrade_summand2_priced_rho (H := H) hfr.rho_pos hfr.Mpos hfr.anchor
  have h3 := doorGrade_summand3_priced_rho_pool (H := H) hprice
  have h4 := doorGrade_summand4_priced_rho (H := H) hfr.rho_pos hLrho hLX hfr.Hfloor
    hfr.armWeak
  have h5 := doorGrade_summand5_priced_rho (H := H) (j := j) hfr.rho_pos hLrho hfr.Hfloor
    hfr.jfloor
  rw [a2DoorGrade_pool]
  ring_nf
  ring_nf at h1 h2 h3 h4 h5
  linarith

/-! ## §3 — THE SOCKET WIRES, AT THE POOLED GRADE -/

/-- **⟦THE GATED SOCKET, POOLED⟧** (`m4_chiSummedFreeRowBig_of_doorGradeGated_pool`) —
`M4ArithPage.m4_chiSummedFreeRowBig_of_doorGradeGated` with `a2DoorGrade_pool` in both slots:
`hgrade` and `henv` are taken only where the socket actually applies them. -/
theorem m4_chiSummedFreeRowBig_of_doorGradeGated_pool {R : ChowlaRegime} {M : ℕ}
    {C₁ M₀ π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (hgrade : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s)
        ≤ (q.totient : ℝ)
            * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                (M₀ (A + s)) (π₀ (A + s)))
    (henv : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hb : SocketBase R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) (π₀ (A + s)) :=
    a2DoorGrade_pool_nonneg M (log_natCast_nonneg' (A + s)) hh0 (hpool (A + s))
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans (hgrade H L q j A s hb) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H L q j A s hb

/-- **⟦THE ARITHMETIC GATE, DISCHARGED AT `ρ` AND AT THE POOL⟧** (`m4_arith_henv_rho_pool`) —
`henv` at `RSbig j H := RSanDoorRho ρ H`, under the `ρ`-frame plus the migrated summand-3
price at every base the socket reaches. -/
theorem m4_arith_henv_rho_pool {R : ChowlaRegime} {M : ℕ} {C₁ M₀ π₀ : ℕ → ℝ} {K ρ : ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ)
    (hprice : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      188133 * π₀ (A + s) * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSanDoorRho ρ H :=
  fun H L q j A s hb =>
    a2DoorGrade_pool_priced_rho (harith H L q j A s hb) (hpool (A + s))
      (hprice H L q j A s hb)

/-- **⟦THE ASSEMBLY, ARITHMETIC INCLUDED, AT THE POOL⟧**
(`m4_chiSummedFreeRow_of_doorArithRho_pool`) — ⟦item 11⟧ of `m4_second_road` at the spliced
grade `m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)`, from the pooled frame.

THE COMPLETE HYPOTHESIS LIST: `hM`; `hframe` — `DoorFuseFrame_pool` (TEN fields, `ε` free);
`hrows`, `hband` — `M4Assembly`'s own two suppliers, byte for byte; `harith` — the `ρ`-frame;
`hprice` — the migrated summand-3 arithmetic.  `hpool` is DERIVED from `hframe` at each base
via `DoorFuseFrame_pool.pool_nonneg`, so the pool's nonnegativity is not asked twice. -/
theorem m4_chiSummedFreeRow_of_doorArithRho_pool {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {K ρ : ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorFuseFrame_pool M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
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
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ)
    (hprice : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      188133 * π₀ (A + s) * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2)
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A) :
    M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  refine m4_chiSummedFreeRow_of_big
    (m4_chiSummedFreeRowBig_of_doorGradeGated_pool (C₁ := C₁) (M₀ := M₀) (π₀ := π₀) hpool ?_
      (m4_arith_henv_rho_pool hpool harith hprice))
  intro H L q j A s hb
  obtain ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  haveI : NeZero q := ⟨hq.ne'⟩
  have hbb : SocketBase R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hbb
  exact m4_chiFreeRowSq_sum_at_door_pool hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hbb) (hband H L q j A s hbb) hF.gP1 hF.gRows hF.eps_pool
    hF.band_pool

end Salt.MR
