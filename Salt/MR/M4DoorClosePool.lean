/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4T0Discharge
import Salt.MR.M4MeanSqPrime

/-!
# ⟦R4 — THE DOOR-ROW REGISTER AT THE FREE POOL⟧ (`M4DoorClosePool`)

Design provenance: `docs/blueprints/flags.md` 2026-07-30 17:51 (⟦R3-A + R3-B LAND⟧), ⟦THE
RESIDUE (the R4 wave)⟧ item (2): *"the `DoorRowCarried` def twin (~150-line restatement — the
brief's '4-line' was wrong, banked)"*.

⟦R2⟧ freed the three `X`-side decaying sources of the frozen five-summand interface into one
constant pool `π₀` (`M4MeanSqPool.m4_meansq_per_chi_gen_pool`).  `M4DoorClose`'s per-instance
register `DoorRowCarried` — the ~98-conjunct `Prop` the whole M4 wave is stated against —
still speaks the LANDED interface: its three grading conjuncts read `≤ (log X)^{−1/500}`, its
`ε`-window carries the exponent-room gate `ε ≤ θ₂₉₃ − 1/500`, and its envelope's third
summand is `188133·(log X)^{−1/500}`.  This file restates it at the pool.

## ⟦THE DIFF, EXACTLY — three places, ninety-five conjuncts untouched⟧

Against `M4DoorClose.DoorRowCarried` (98 conjuncts), `DoorRowCarriedPool` (99) differs in:

1. the real binder block gains `π₀` (existentially bound with the instance's other opaque
   reals, so the register's SIGNATURE does not change);
2. the `ε`-window loses its middle conjunct `ε ≤ θ₂₉₃ − 1/500` — ⟦R2⟧'s gift.  ⚠ ⟦MAESTRO
   ERRATUM #2, HONOURED⟧ `8640 ≤ (log X)^ε` STAYS: it is a `𝒰`-leg gate, not a pool gate;
3. the grading block's THREE conjuncts become FIVE — `0 ≤ π₀`, `gP1 ≤ π₀`, `gRows ≤ π₀`,
   `(log X)^{−θ₂₉₃+ε} ≤ π₀`, `4096·(log X)^{−1+1/500} ≤ π₀` — and the envelope's third
   summand becomes `188133·π₀`.

The same three-place diff is applied to `M4T0Discharge.DoorRowCarriedT0`, whose only other
difference from `DoorRowCarried` is that its `T₀` conjunct is the discharge's gate list
`DoorRowT0Gates` rather than the band integral.

## Contents

* §1 `DoorRowCarriedPool` — the register at the pool;
* §2 `m4_door_meansq_carried_pool` — the workhorse re-thread (the ~98-conjunct destructure
  and the capstone's application, at `m4_meansq_per_chi_gen_pool`);
* §3 `m4_dyadicRow_carried_pool` — `M4Maximal.M4ChiDyadicRowMeanSq` at the pooled register;
* §4 `DoorRowCarriedT0Pool` and `doorRowCarried_of_t0free_pool` — the `M4T0Discharge` mirror:
  the `T₀`-free pooled register implies the pooled one, the band integral supplied by
  `M4T0Discharge.m4_t0band_discharged` exactly as at the landed pair;
* §5 `m4_wave_structurally_closed_pool` and `m4_wave_closed_T0_discharged_pool` — the two
  wave closers at the pooled register (pure register swaps: `M4Maximal`'s consumers never
  read a grading conjunct);
* §6 **THE FUSE**: `DoorRowCarriedJoin`, `m4_door_meansq_carried_join` and
  `m4_dyadicRow_carried_join` — the register at the R1×R2 JOIN, i.e. §1 with its `gRows`
  conjunct at `ThmA2.a2RowsSum'`, over `M4MeanSqPrime.m4_meansq_per_chi_gen_join`.

⟦PURELY ADDITIVE⟧  No landed declaration is touched.  Setting `π₀ := (log X)^{−1/500}`
recovers the landed registers, `gU`/`gBand` then being derivable from the dropped `ε`-room
gate and the `4096` room — which is exactly `ThmA2Prime.thm_a2'_of_rows'`'s own derivation.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE PER-INSTANCE REGISTER, AT THE POOL

`M4DoorClose` §1's register, restated at `π₀`.  See the module header for the three-place
diff; everything else — the two pins, the scale page, the door and band, the window floors,
the calibration, the `kmin`/`Ymax` ladder, the two opaque K6 gates, the coprime-tail page, the
cap-free floor, the socket's gates, the endpoint and the `T₀`-band carry — is byte-identical
to the landed text. -/

def DoorRowCarriedPool (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
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
    (calQK (Adoor M) (3072 * M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) i)
                (calQK (Adoor M) (3072 * M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) i : ℕ) : ℝ)
            / Real.log ((calQK (Adoor M) (3072 * M) M i : ℕ) : ℝ))) ∧
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
      thinBundleG X VJ (calH (H1door M) 2) (calP (Adoor M) (3072 * M) 2)
          (calQK (Adoor M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
        * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
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
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (Adoor M) (3072 * M) i)
          (calQK (Adoor M) (3072 * M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
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
    (doorChiCoeff χ M Xd = 0) ∧
    -- ⟦THE CARRY: the `T₀`-band arm, at `m4_hT0band_at_door`'s own conclusion⟧
    ((∫ t in (-(seamT0 X))..(seamT0 X),
        ‖dpolyA (winCutH Xd (doorChiCoeff χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
      ≤ t0BandB X C₁' M₀) ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    ((0 : ℝ) ≤ π₀) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀) ∧
    (5760 * (a2RowsSum M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀) ∧
    ((Real.log X) ^ (-theta293 + ε) ≤ π₀) ∧
    (4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1 M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

/-! ## §2 — THE WORKHORSE, AT THE POOL

`M4DoorClose` §3's proof verbatim over `M4MeanSqPool.m4_meansq_per_chi_gen_pool`.  Two lines
of the re-thread move: the destructure drops `hεup` and gains `π₀`/`hpool`/`hgU`/`hgBand`,
and the capstone's application feeds the pool where it fed the two `(log X)^{−1/500}` gates
and `hL4096`. -/

set_option maxHeartbeats 4000000 in
-- the same cause as `M4DoorClose` §3: the ~99-conjunct destructuring plus the capstone's
-- ~87-argument application is what costs the heartbeats — no tactic search happens here
/-- **THE DOOR ROW'S MEAN SQUARE, CARRIED, AT THE POOL** (`m4_door_meansq_carried_pool`).
`M4DoorClose.m4_door_meansq_carried` at `DoorRowCarriedPool`: at every door instance meeting
the pooled register, the door's sieved, `χ`-twisted, UN-PHASED datum satisfies the capstone's
five-summand mean-square bound at the grade `B`.

The `∃`-bound constants are `M4DoorClose`'s, at the pooled capstone. -/
theorem m4_door_meansq_carried_pool :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (Qm q : ℕ) (χ : DirichletCharacter ℂ q), 0 < q → q ≤ Qm →
        ∀ (M Xd j : ℕ) (B : ℝ), 1 ≤ M → doorRowFloor M ≤ j →
          DoorRowCarriedPool Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M Xd j B →
            1 / ((Xd : ℕ) : ℝ)
                * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
                    ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                        * shortSum (doorChiCoeff χ M)
                            (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
              ≤ B := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hgen⟩ :=
    m4_meansq_per_chi_gen_pool
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  -- ⟦THE SKOLEM CUT⟧ the masked-floor constant, as a function of the modulus range
  choose Kcf hKcf0 hcfl using capFreeFloor3_pieceDatum
  obtain ⟨Ctail, hCtail0, htail⟩ := m4_door_tail_supply
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
    have hA : 2 ^ 18 ≤ Adoor M := Adoor_ge_old M
    have hAle : Adoor M ≤ M * Adoor M := Nat.le_mul_of_pos_left _ hM
    have hjf : M * Adoor M ≤ j := hj0
    have h18 : (2 : ℕ) ≤ 2 ^ 18 := by norm_num
    omega
  have hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    have hN : (4 : ℕ) ≤ 2 ^ j := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    exact_mod_cast hN
  have hQ1h : ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) :=
    door_length_gate_iff.mpr hj0
  -- ⟦THE DATUM SIDE (class (C)): the cut and its three S8 slots⟧
  have haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd →
      winCutH Xd (doorChiCoeff χ M) n = doorChiCoeff χ M n :=
    fun n h1 h2 => winCutH_of_mem _ h1 h2
  have ha0 : winCutH Xd (doorChiCoeff χ M) Xd = 0 := winCutH_supp0 _ le_rfl
  -- ⟦the pin chain and the per-block puncture law⟧
  have hcoefPin : SeamCoefW Xd P Q (winCutH Xd (doorChiCoeff χ M)) (doorChiCoeff χ M)
      (liouChi χ) :=
    doorChiCoeff_seamCoefW_at_door_H χ hM hlog1 hQXd hPlow haH ha0 hend
  have hcoefBand := doorChiCoeff_seamCoefW_punct_H χ hM haH ha0 hend
  -- ⟦the per-piece cap-free floor⟧
  have hfloor : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M)) ((Xd : ℕ) : ℝ) := by
    intro 𝒥 h𝒥
    exact hcfl Qm q χ (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 𝒥
      ((Xd : ℕ) : ℝ) Dmask hqQm hXee hDmask0 (hdebit 𝒥 h𝒥) hcfthr
  -- ⟦THE SOCKET⟧ at `Ps := 1`, `J := 2`, read at the door datum
  have hsock0 := hsup q χ (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M)
    (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q 2 1 Mt kk Dd Xa cqS L cgS Cb
    ((Xd : ℕ) : ℝ) theta293 (seamRad ((Xd : ℕ) : ℝ)) ((Xd : ℕ) : ℝ) 0 Rbar0 cW SW
    hc0 hce hc1 hCb0 hCbound hP1 le_rfl hRrad0 theta293_pos theta293_lt_one_div_32.le
    hLXe hPlow hQhigh hPQ hfloor hblk hbox hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0
    hboxw hS0 hSbd hendGen hRbdU
  have hsockR : CofactorSocket (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q
      ((Xd : ℕ) : ℝ) (seamRad ((Xd : ℕ) : ℝ)) 0 (4 * Rbar0) (doorChiCoeff χ M) := by
    have hs := cofactorSocket_doorChiCoeff χ hsock0
    have he : (2 : ℝ) ^ (2 : ℕ) * Rbar0 = 4 * Rbar0 := by ring
    rwa [he] at hs
  -- ⟦THE COPRIME TAIL⟧: `Mtail` and `EP2` are computed, not carried
  have hNcast : (((2 * Xd : ℕ)) : ℝ) = 2 * ((Xd : ℕ) : ℝ) := by push_cast; ring
  obtain ⟨hMtail, hMtail0, hEP2⟩ := htail q χ M P Q Xd (2 * Xd) ((Xd : ℕ) : ℝ) ε
    rfl hNcast hX0 hL256 hP2 hPQ hXd1 hQlogXd hdomband hPlow hlogb habs hPQratio h2688
  -- ⟦THE CAPSTONE, AT THE POOL⟧
  have hres := hgen Qm q χ hqQm (2 * Xd) Xd P Q M (winCutH Xd (doorChiCoeff χ M)) (liouChi χ)
    (doorChiCoeff χ M)
    (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 i
      (liouChi χ))
    ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) δ' V VJ L Cb (seamRad ((Xd : ℕ) : ℝ)) (4 * Rbar0)
    kmin Ymax ε _ _ C₁' M₀ π₀
    rfl rfl hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe hM hXdQ hQ1h hP3
    hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkkg hMtY
    hRrad0 le_rfl le_rfl hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0k hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 habs hEP2 le_rfl
    (doorRow_ha1 χ M Xd) (norm_liouChi_le_one χ)
    (fun n hn => doorRow_hsupp0 χ M Xd n hn) (fun n hn => doorRow_hasupp χ M Xd n hn)
    hMtail0 hMtail
    (norm_doorChiCoeff_le_one χ M) (fun i n => norm_doorPunctCoeff_le_one χ M i n)
    (by positivity) hRgrade hsockR hcoefBand hcoefPin hT0band hcff hpool hgP1 hgRows hgU
    hgBand
  -- ⟦THE DATUM BRIDGE⟧ the cut is invisible to the row's short sum
  simp only [shortSum_winCutH_seamS0] at hres
  exact le_trans hres henv

/-! ## §3 — THE GRADED ROW DATUM AT THE DOOR, AT THE POOL

`M4DoorClose` §4 verbatim over §2.  `M4DoorClose.doorRow_trivial_grade` is REUSED — the
trivial grade at the small lengths reads no interface gate at all. -/

/-- **THE DOOR'S DYADIC ROW, CARRIED, AT THE POOL** (`m4_dyadicRow_carried_pool`). -/
theorem m4_dyadicRow_carried_pool :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloor M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloor M ≤ j →
            ∀ s ≤ H,
              DoorRowCarriedPool Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
                (doorLadder R.x H (i + 1) + s) j (MS j H)) →
        M4ChiDyadicRowMeanSq R M k MS := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_door_meansq_carried_pool
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro R Qm M k MS hM hQm htriv hcar H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hApos : 0 < doorLadder R.x H (i + 1) + s := by
    have := doorLadder_floor hxH (i + 1); omega
  by_cases hcase : doorRowFloor M ≤ j
  · have hqQm : q ≤ Qm := by
      have hR : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hR
    exact hrow Qm q χ hq hqQm M (doorLadder R.x H (i + 1) + s) j (MS j H) hM hcase
      (hcar H hlo hhi q hq hqQ i hik χ j hjL hcase s hsH)
  · exact le_trans (doorRow_trivial_grade χ M j hApos) (htriv j H (not_le.mp hcase))

/-! ## §4 — THE `M4T0Discharge` MIRROR

`M4T0Discharge` §4's register and bridge at the pool.  The bridge is the landed one's proof
verbatim: 98 conjuncts transport as projections and the one that does not — the `T₀`-band
integral — is supplied by `M4T0Discharge.m4_t0band_discharged`, which reads only the `X`-side
gates `DoorRowT0Gates` and the register's `(X_d : ℝ) = X`, `0 ≤ Cb`, `ShortIntervalDatum Cb`
and mask-debit conjuncts.  **The discharge is blind to the pool**: it touches no grading
conjunct and no `ε`-window conjunct. -/

def DoorRowCarriedT0Pool (Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
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
    (calQK (Adoor M) (3072 * M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) i)
                (calQK (Adoor M) (3072 * M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) i : ℕ) : ℝ)
            / Real.log ((calQK (Adoor M) (3072 * M) M i : ℕ) : ℝ))) ∧
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
      thinBundleG X VJ (calH (H1door M) 2) (calP (Adoor M) (3072 * M) 2)
          (calQK (Adoor M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
        * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
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
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (Adoor M) (3072 * M) i)
          (calQK (Adoor M) (3072 * M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
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
    (doorChiCoeff χ M Xd = 0) ∧
    -- ⟦ARM 1 DISCHARGED: the T₀-band gates, not the T₀-band integral⟧
    DoorRowT0Gates Kbox X₀w q Ddis X Xw Dmask ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    ((0 : ℝ) ≤ π₀) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀) ∧
    (5760 * (a2RowsSum M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀) ∧
    ((Real.log X) ^ (-theta293 + ε) ≤ π₀) ∧
    (4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * (cfbC₁ X (t0dC1 Cb)) ^ 2 * Real.exp (-(1 / Real.exp 1) * t0dM0 X)
        + 1787702400 * a2Level1 M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

set_option maxHeartbeats 4000000 in
-- the same cause as `M4T0Discharge.doorRowCarried_of_t0free`: two ~99-conjunct registers are
-- elaborated against each other; no tactic search happens, every step is a projection
/-- **THE BRIDGE, AT THE POOL** (`doorRowCarried_of_t0free_pool`).
`M4T0Discharge.doorRowCarried_of_t0free` at the pooled pair. -/
theorem doorRowCarried_of_t0free_pool (Qm : ℕ) :
    ∃ Kbox X₀w : ℝ, 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ) (q : ℕ) [NeZero q]
        (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ), q ≤ Qm →
        DoorRowCarriedT0Pool Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B →
          DoorRowCarriedPool Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hdis⟩ := m4_t0band_discharged Qm
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
      ‖dpolyA (winCutH Xd (doorChiCoeff χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
        ≤ t0BandB X (cfbC₁ X (t0dC1 Cb)) (t0dM0 X) :=
    hdis q χ M Xd Ddis X Xw Cb Dmask hq g1 d1 g2 g3 g4 g5 d46 d47 d68 g6 g7 g8
  exact ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, cfbC₁ X (t0dC1 Cb),
    t0dM0 X, cqS, cgS, cW, SW, Rbar0, Dmask, π₀, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11,
    d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29,
    d30, d31, d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47,
    d48, d49, d50, d51, d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65,
    d66, d67, d68, d69, d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83,
    d84, d85, d86, d87, d88, d89, d90, d91, hT0, d93, d94, d95, d96, d97, d98, d99⟩


/-! ## §5 — THE TWO WAVE CLOSERS, AT THE POOLED REGISTER

`M4DoorClose` §5 and `M4T0Discharge` §5 with the register name swapped and nothing else:
`M4Maximal.m4_wave_closed_of_dyadicRow` and `M4NonCoprime.m4_nonCoprime_classMeanSq` never
read a grading conjunct, so the pool is invisible to them. -/

set_option maxHeartbeats 1600000 in
-- `m4_wave_structurally_closed`'s own budget: the register mentions `DoorRowCarriedPool`
-- under six binders, and that is the whole cost
theorem m4_wave_structurally_closed_pool (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloor M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloor M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloor M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            -- ⟦the modulus cap: the door's characters inside the capstone's range⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            -- ⟦the small lengths' trivial grade⟧
            (∀ j H : ℕ, j < doorRowFloor M → 4 ≤ MS j H) →
            -- ⟦ARM 1 + the regime gates: the per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloor M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedPool Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            -- ⟦R2's two gates⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦ARM 2: the coprime supply, interval/length-general⟧
            M4CoprimeBlockMeanSq R M
              (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_dyadicRow_carried_pool
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_dyadicRow
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl Qm, Xsk, Kcf Qm, Ctail,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl Qm, hXsk0, hKcf0 Qm, hCtail0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcar hgate harc hcp
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H)
      (fun H => 2 * MStr H) H := fun H =>
    m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
  -- ⟦R2⟧ the wave asks only the NON-COPRIME classes; `m4_nonCoprime_classMeanSq` delivers all
  have hnc : M4ClassBlockMeanSq R M k
      (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_nonCoprime_classMeanSq (k := k) hM hBcl0 hgate harc hcp
  refine hR δ Braw MS MSan MStr (doorRowFloor M) M k hgates hMSan0 hMStr0 hBraw0 han htr
    hdrift hdel hrest (hrow R Qm M k MS hM hQm htriv hcar) ?_
  intro H hlo hhi q hq hqQ i hik r hrq _hncop
  exact hnc H hlo hhi q hq hqQ i hik r hrq

set_option maxHeartbeats 1600000 in
-- `m4_wave_closed_T0_discharged`'s own budget, at the pooled register
theorem m4_wave_closed_T0_discharged_pool (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloor M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloor M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloor M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloor M → 4 ≤ MS j H) →
            -- ⟦ARM 1 DISCHARGED: the T₀-free per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloor M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0Pool Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦ARM 2: the coprime supply, interval/length-general — the ONLY analytic carry left⟧
            M4CoprimeBlockMeanSq R M
              (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hbridge⟩ := doorRowCarried_of_t0free_pool Qm
  obtain ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hmain⟩ :=
    m4_wave_structurally_closed_pool Qm
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


/-! ## §6 — ⟦THE FUSE⟧: THE REGISTER AT THE R1×R2 JOIN

§1–§3 moved the register to ⟦R2⟧'s pool.  `M4MeanSqPrime.m4_meansq_per_chi_gen_join` is the
same capstone at BOTH ⟦R1⟧'s primed row sum and the pool: against the pooled capstone exactly
ONE binder moves, `hgRows` reading `ThmA2.a2RowsSum'`.  So the JOINED register is
`DoorRowCarriedPool` with that one conjunct primed, and its workhorse is §2's proof with the
joined capstone in place of the pooled one.

⟦WHAT THE JOINED REGISTER READS⟧ no conjunct of `DoorRowCarriedJoin` carries an `X_d`-decaying
right-hand side (⟦R2⟧) and none carries a `log₂(2X_d)` numerator (⟦R1⟧): the `gRows` conjunct
is `5760·(a2RowsSum' M X_d + C_p·(2/M)) ≤ π₀`, whose `p²` slot is the `X_d`-FREE `24/𝒫ⱼ`.
This is `M4AssemblyPrime.DoorFuseFrame_pool'`'s `gRows` field, at the row layer.

⚠ ⟦THE DIRECTION⟧ `a2RowsSum' ≤ a2RowsSum`, so `DoorRowCarriedJoin` asks a STRONGER `gRows`
than `DoorRowCarriedPool` and there is no implication from the pooled register to the joined
one.  The joined register is what a consumer who has R1's row supplier can meet; that is the
whole point, and it is why `m4_meansq_per_chi_gen_join` — not `_pool` — is its capstone. -/

def DoorRowCarriedJoin (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
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
    (calQK (Adoor M) (3072 * M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) i)
                (calQK (Adoor M) (3072 * M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) i : ℕ) : ℝ)
            / Real.log ((calQK (Adoor M) (3072 * M) M i : ℕ) : ℝ))) ∧
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
      thinBundleG X VJ (calH (H1door M) 2) (calP (Adoor M) (3072 * M) 2)
          (calQK (Adoor M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
        * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
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
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (Adoor M) (3072 * M) i)
          (calQK (Adoor M) (3072 * M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
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
    (doorChiCoeff χ M Xd = 0) ∧
    -- ⟦THE CARRY: the `T₀`-band arm, at `m4_hT0band_at_door`'s own conclusion⟧
    ((∫ t in (-(seamT0 X))..(seamT0 X),
        ‖dpolyA (winCutH Xd (doorChiCoeff χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
      ≤ t0BandB X C₁' M₀) ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    ((0 : ℝ) ≤ π₀) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀) ∧
    (5760 * (a2RowsSum' M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀) ∧
    ((Real.log X) ^ (-theta293 + ε) ≤ π₀) ∧
    (4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1 M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

set_option maxHeartbeats 4000000 in
-- the same cause as §2, at the joined capstone
theorem m4_door_meansq_carried_join :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (Qm q : ℕ) (χ : DirichletCharacter ℂ q), 0 < q → q ≤ Qm →
        ∀ (M Xd j : ℕ) (B : ℝ), 1 ≤ M → doorRowFloor M ≤ j →
          DoorRowCarriedJoin Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M Xd j B →
            1 / ((Xd : ℕ) : ℝ)
                * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
                    ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                        * shortSum (doorChiCoeff χ M)
                            (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
              ≤ B := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hgen⟩ :=
    m4_meansq_per_chi_gen_join
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  -- ⟦THE SKOLEM CUT⟧ the masked-floor constant, as a function of the modulus range
  choose Kcf hKcf0 hcfl using capFreeFloor3_pieceDatum
  obtain ⟨Ctail, hCtail0, htail⟩ := m4_door_tail_supply
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
    have hA : 2 ^ 18 ≤ Adoor M := Adoor_ge_old M
    have hAle : Adoor M ≤ M * Adoor M := Nat.le_mul_of_pos_left _ hM
    have hjf : M * Adoor M ≤ j := hj0
    have h18 : (2 : ℕ) ≤ 2 ^ 18 := by norm_num
    omega
  have hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    have hN : (4 : ℕ) ≤ 2 ^ j := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    exact_mod_cast hN
  have hQ1h : ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) :=
    door_length_gate_iff.mpr hj0
  -- ⟦THE DATUM SIDE (class (C)): the cut and its three S8 slots⟧
  have haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd →
      winCutH Xd (doorChiCoeff χ M) n = doorChiCoeff χ M n :=
    fun n h1 h2 => winCutH_of_mem _ h1 h2
  have ha0 : winCutH Xd (doorChiCoeff χ M) Xd = 0 := winCutH_supp0 _ le_rfl
  -- ⟦the pin chain and the per-block puncture law⟧
  have hcoefPin : SeamCoefW Xd P Q (winCutH Xd (doorChiCoeff χ M)) (doorChiCoeff χ M)
      (liouChi χ) :=
    doorChiCoeff_seamCoefW_at_door_H χ hM hlog1 hQXd hPlow haH ha0 hend
  have hcoefBand := doorChiCoeff_seamCoefW_punct_H χ hM haH ha0 hend
  -- ⟦the per-piece cap-free floor⟧
  have hfloor : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M)) ((Xd : ℕ) : ℝ) := by
    intro 𝒥 h𝒥
    exact hcfl Qm q χ (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 𝒥
      ((Xd : ℕ) : ℝ) Dmask hqQm hXee hDmask0 (hdebit 𝒥 h𝒥) hcfthr
  -- ⟦THE SOCKET⟧ at `Ps := 1`, `J := 2`, read at the door datum
  have hsock0 := hsup q χ (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M)
    (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q 2 1 Mt kk Dd Xa cqS L cgS Cb
    ((Xd : ℕ) : ℝ) theta293 (seamRad ((Xd : ℕ) : ℝ)) ((Xd : ℕ) : ℝ) 0 Rbar0 cW SW
    hc0 hce hc1 hCb0 hCbound hP1 le_rfl hRrad0 theta293_pos theta293_lt_one_div_32.le
    hLXe hPlow hQhigh hPQ hfloor hblk hbox hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0
    hboxw hS0 hSbd hendGen hRbdU
  have hsockR : CofactorSocket (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q
      ((Xd : ℕ) : ℝ) (seamRad ((Xd : ℕ) : ℝ)) 0 (4 * Rbar0) (doorChiCoeff χ M) := by
    have hs := cofactorSocket_doorChiCoeff χ hsock0
    have he : (2 : ℝ) ^ (2 : ℕ) * Rbar0 = 4 * Rbar0 := by ring
    rwa [he] at hs
  -- ⟦THE COPRIME TAIL⟧: `Mtail` and `EP2` are computed, not carried
  have hNcast : (((2 * Xd : ℕ)) : ℝ) = 2 * ((Xd : ℕ) : ℝ) := by push_cast; ring
  obtain ⟨hMtail, hMtail0, hEP2⟩ := htail q χ M P Q Xd (2 * Xd) ((Xd : ℕ) : ℝ) ε
    rfl hNcast hX0 hL256 hP2 hPQ hXd1 hQlogXd hdomband hPlow hlogb habs hPQratio h2688
  -- ⟦THE CAPSTONE, AT THE POOL⟧
  have hres := hgen Qm q χ hqQm (2 * Xd) Xd P Q M (winCutH Xd (doorChiCoeff χ M)) (liouChi χ)
    (doorChiCoeff χ M)
    (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 i
      (liouChi χ))
    ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) δ' V VJ L Cb (seamRad ((Xd : ℕ) : ℝ)) (4 * Rbar0)
    kmin Ymax ε _ _ C₁' M₀ π₀
    rfl rfl hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe hM hXdQ hQ1h hP3
    hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkkg hMtY
    hRrad0 le_rfl le_rfl hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0k hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 habs hEP2 le_rfl
    (doorRow_ha1 χ M Xd) (norm_liouChi_le_one χ)
    (fun n hn => doorRow_hsupp0 χ M Xd n hn) (fun n hn => doorRow_hasupp χ M Xd n hn)
    hMtail0 hMtail
    (norm_doorChiCoeff_le_one χ M) (fun i n => norm_doorPunctCoeff_le_one χ M i n)
    (by positivity) hRgrade hsockR hcoefBand hcoefPin hT0band hcff hpool hgP1 hgRows hgU
    hgBand
  -- ⟦THE DATUM BRIDGE⟧ the cut is invisible to the row's short sum
  simp only [shortSum_winCutH_seamS0] at hres
  exact le_trans hres henv

/-! ### The graded row datum at the joined register -/

theorem m4_dyadicRow_carried_join :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloor M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloor M ≤ j →
            ∀ s ≤ H,
              DoorRowCarriedJoin Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
                (doorLadder R.x H (i + 1) + s) j (MS j H)) →
        M4ChiDyadicRowMeanSq R M k MS := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_door_meansq_carried_join
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro R Qm M k MS hM hQm htriv hcar H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hApos : 0 < doorLadder R.x H (i + 1) + s := by
    have := doorLadder_floor hxH (i + 1); omega
  by_cases hcase : doorRowFloor M ≤ j
  · have hqQm : q ≤ Qm := by
      have hR : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hR
    exact hrow Qm q χ hq hqQm M (doorLadder R.x H (i + 1) + s) j (MS j H) hM hcase
      (hcar H hlo hhi q hq hqQ i hik χ j hjL hcase s hsH)
  · exact le_trans (doorRow_trivial_grade χ M j hApos) (htriv j H (not_le.mp hcase))

end Salt.MR
