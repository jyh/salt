/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4T0Datum
import Salt.MR.M4Puncture
import Salt.MR.M4NonCoprime
import Salt.MR.M4MeanSq
import Salt.MR.M4Maximal

/-!
# `M4DoorClose` — ⟦W2-DOOR-CARRIED⟧: the structural close of the M4 wave

`M4DoorRow` landed the door row's supply as far as it went and named TWO walls.  Both are
down (the counter-wave: `hwinBand` DELETED from the capstone, the length-graded re-cut of
`M4Maximal.M4ChiDyadicRowMeanSq`), and `M4T0Datum` reduced the last analytic item — the
`hT0band` slot at the door's sieved χ-twisted datum — to a pricing residue whose route is a
morning ruling.  This file performs the close that does NOT wait on that ruling: it
discharges every DATUM-side binder of `M4MeanSq.m4_meansq_per_chi_gen` at the door's own cut
datum, and CARRIES the rest as a named register.

## ⟦THE FINAL CARRIED REGISTER⟧, in three classes

**(A) analytic-carried — TWO arms, and only two.**

1. **the `T₀`-band arm** — one conjunct of `DoorRowCarried`, at
   `M4T0Datum.m4_hT0band_at_door`'s own conclusion shape,

   `∫_{−T₀}^{T₀} ‖dpolyA (winCutH X_d (doorChiCoeff χ M)) (seamS0 (2X_d) X) t‖² dt
      ≤ t0BandB X C₁′ M₀`,  `T₀ = seamT0 X`,

   i.e. the RAW slot, not `cfb_t0band_supply_of_sup`'s composed form.  Reason: the raw slot
   is what `m4_meansq_per_chi_gen` reads, and `m4_hT0band_at_door` /
   `m4_hT0band_at_door_of_wide` both END at exactly this proposition — so the morning
   route plugs by `exact`, at either of its two granularities, with no adapter.  The
   per-instance `(C₁′, M₀)` are existentially bound inside `DoorRowCarried`, which is what
   lets a supplier choose `C₁′ = cfbC₁ X C₁` and `M₀ = cfbM0 K q X`.

2. **the coprime-supply arm** — `M4NonCoprime.M4CoprimeBlockMeanSq R M Bcl`, carried at its
   INTERVAL/LENGTH-GENERAL shape (`∀ L ≤ H`, `∀ A B` with `B + L ≤ 2A + 4`), which is what
   ⟦R2⟧'s deviation asks for: `m4_nonCoprime_classMeanSq` consumes exactly that and needs no
   further adapter, so the compose crosses R2 with the landed dilation machinery alone.

**(B) regime — the gates, ∀-quantified over the block range.**  All of `DoorRowCarried`'s
remaining conjuncts, plus the four register lines of `m4_wave_closed_of_dyadicRow`
(the drift line, the two `mrtDeliveredGrade` lines, and the `M4DoorGates` bundle) and the
two `M4NonCoprime` gates (`log H ≤ 2^21845`, `2·arcDen 12 H ≤ H`).  By group:

* the SCALE page at the BLOCK scale `X = X_d = X_{i+1} + s` — never `log R.x`: `e^e ≤ X`,
  `e² ≤ log X`, `256 ≤ log X` (the tail page's own floor), the window gates at `h = 2^j`,
  the `TannGate`, the `T₀`/`L` gates, the ε-window `0 ≤ ε ≤ θ − 1/500`, `8640 ≤ (log X)^ε`;
* the BAND gates at the Ramaré band `[P, Q]`, `Q ≤ ⌊Q83 X⌋₊` PER INSTANCE (`P` and `Q` are
  existentially bound inside `DoorRowCarried`, so each block picks its own);
* the DOOR gates: `𝒬K_2 ≤ X_d`, `log 𝒬K_2 ≤ √(log X_d)`, the two Mertens domination lines
  (at the door blocks and at the band), the `a2RowsSum`/`4096` interface room;
* the TAIL threshold `2688·C·loglog X ≤ (log X)^ε` at the OPAQUE mass constant `C = Ctail`
  — stated where `C` is bound (⟦THE K6 PATTERN⟧), which is why `Ctail` is hoisted into this
  file's existential rather than chosen;
* the SOCKET's ~25 gates, verbatim from `CaseAWide.m4_supplier_complete` at `Ps := 1`,
  `J := 2`, `Tann := X`, `t₁ := 0`, `Rrad := seamRad X`: the `c`-contract, `TLBlockGates34`
  on `ramI (H83 X θ) P Q`, the wide supply's dilation/anchor gates at `(Dd, Xa)`, the
  annulus box gates, the uniform CASE-A ceiling `S` and the two `cofactorRbdGen` charges;
* the `g`-arm/`U1floor` shapes of the outer register: `U1floor ≤ R.Hlo` and `g R.Hhi R.ω ≤
  R.x` are chosen BEFORE `R` (the consumer's, unchanged from `m4_wave_closed_of_chi`), and
  `m4SmallGradeFits`'s threshold `2·4^{doorRowFloor M}·D ≤ H·MSan H` is the one that must
  swallow `4^{M·Adoor M}` — see `M4Maximal`'s ⟦THE CONSUMPTION NOTE⟧ and
  `M4DoorRow.door_smallGrade_fits`.

**(C) witnessed — discharged here, carried by nobody.**

`ha1`, `hcf1`, `hsupp0`, `hasupp` (§2 of `M4DoorRow`, at the half-open cut `winCutH`);
`hb1` and `hbf1` (the door datum and its PUNCTURED level family
`memSPunctCoeff … 2 j (liouChi χ)`); `hMtail0`/`hMtail`/`hEP2`/`hEP2w` (the whole coprime-tail
page, from `M4DoorRow.m4_door_tail_supply` — `Mtail` and `EP2` are *computed*, not carried);
`hsockR` (`m4_supplier_complete` ∘ `M4DoorRow.cofactorSocket_doorChiCoeff`); `hcoefBand`
(`M4Puncture.doorChiCoeff_seamCoefW_punct_H` — the post-WALL-1 windowed per-level form);
`hcoefPin` (`M4Band.doorChiCoeff_seamCoefW_at_door_H`); the per-piece cap-free floor
(`CofactorSupplier.capFreeFloor3_pieceDatum`, so only the Mertens mask debit `Dmask` is a
carried numeral); `hh4` and `hQ1h` (BOTH from the length floor — see below); and the two
pins `(X_d : ℝ) = X`, `N = 2X_d`, which are `rfl` at the door datum.

## ⟦THE ENDPOINT CONVENTION⟧

`hend : doorChiCoeff χ M X_d = 0` is a conjunct of `DoorRowCarried`, i.e. carried PER
INSTANCE.  It is not a proof convenience: `M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is
the kernel converse — a half-open cut satisfies the band pair law only if the sieved datum
vanishes at the block bottom.  Its discharge condition is arithmetic and datum-free:
`X_d ∉ 𝒮`, i.e. some door block `[𝒫_i, 𝒬K_i]` contains no prime factor of `X_d`
(`M4Band.memSCoeff_eq_zero_of_not_memS`).  A consumer that may CHOOSE the block bottom (the
door ladder's `s`-shift is exactly that freedom, `s ≤ H`) discharges it by choosing `s`;
this file does not choose, so the gate is named and carried.

## ⟦THE LENGTH FLOOR IS FREE⟧

`m4_door_meansq_carried` takes `doorRowFloor M ≤ j` and DERIVES both `4 ≤ h` and the
capstone's own window gate `𝒬K_1 ≤ h` from it (`M4DoorRow.door_length_gate_iff`, the
converse direction).  So the graded split's partition costs the supplier nothing at the
large lengths — and at the small ones the grade is the trivial `4`
(`doorRow_trivial_grade`, `‖(1/h)·shortSum‖ ≤ (h+1)/h ≤ 2`), which is what
`M4Maximal.m4SmallGradeFits` is priced against.

## ⟦WHAT LANDS⟧

* `DoorRowCarried` — the per-instance register, as ONE `Prop` (§1);
* `doorRow_trivial_grade` — the `j < j₀` half, at the absolute grade `4` (§2);
* `m4_door_meansq_carried` — the workhorse: the five-summand mean square at the door's BARE
  datum, from `DoorRowCarried` alone (§3);
* `m4_dyadicRow_carried` — `M4Maximal.M4ChiDyadicRowMeanSq` discharged at the door datum,
  the graded family split at `doorRowFloor M` (§4);
* `m4_wave_structurally_closed` — the end-to-end statement
  `(the register) → ¬ logChowla2Fails R.eps R.x R.ω` (§5).

## ⟦THE TRAPS RESPECTED⟧

the four log scales (every `log` here is at the BLOCK scale `X_d`, never `log R.x`;
`Nat.log 2` only in the dyadic index); `liouChi`, never `lamChi`; the datum is UN-PHASED
(`doorChiCoeff χ M` bare, frequency `0`); half-open throughout (`winCutH`, `seamS0`'s strict
filter); strict gates never weakened; `X_d` and `Q` are pinned PER INSTANCE inside the
existential; the K6 existential-scope discipline (`Ctail`, `Kcf`, `Xsk` and the capstone's
seven constants are bound OUTSIDE the instance quantifier, their gates INSIDE).
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE PER-INSTANCE REGISTER

Everything `M4MeanSq.m4_meansq_per_chi_gen` asks at ONE door instance that this file does
not discharge, as a single `Prop`.  The instance is `(χ, M, X_d, j)`; the scale is
`X = X_d`, the block is `N = 2X_d`, the window length is `h = 2^j`, and the Ramaré band
`[P, Q]` is chosen INSIDE (per instance, as ⟦THE BAND-PER-INSTANCE⟧ demands).

`B` is the instance's grade: the last conjunct says the capstone's five-summand right-hand
side is at most `B`, so a consumer supplies the ENVELOPE here rather than downstream. -/

/-- **THE DOOR ROW'S CARRIED REGISTER** (`DoorRowCarried`) — see the module header's three
classes.  The two analytic carries are `hend` (the endpoint) and the `T₀`-band integral; all
the rest is regime arithmetic at the block scale. -/
def DoorRowCarried (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε C₁' M₀ cqS cgS cW SW Rbar0 Dmask : ℝ),
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
    ((0 : ℝ) ≤ ε) ∧ (ε ≤ theta293 - 1 / 500) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
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
    (374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500)) ∧
    (5760 * (a2RowsSum M Xd + Ccc * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500)) ∧
    ((4096 : ℝ) ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1 M
        + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(13 : ℝ) / 15) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

/-! ## §2 — THE SMALL LENGTHS: THE TRIVIAL GRADE `4`

⟦WALL 2⟧'s repair asks a grade only where the capstone SPEAKS; below the floor a supplier
owes the trivial one.  It is `4`, absolutely: the window `(y, y+h]` carries at most `h + 1`
lattice points (`M4Dyadic.norm_shortSum_le`), so `‖(1/h)·shortSum‖ ≤ (h+1)/h ≤ 2` at `h ≥ 1`
— and `h = 2^j ≥ 1` at EVERY `j`, including `j = 0`.  The mean over `[X_d, 2X_d]` then costs
nothing. -/

/-- **THE TRIVIAL GRADE AT THE DOOR ROW** (`doorRow_trivial_grade`).  The door row's mean
square at ANY dyadic length is at most `4` — the bound `M4Maximal`'s graded split charges the
`j < j₀` half at, and the one `M4DoorRow.door_smallGrade_fits` is priced against. -/
theorem doorRow_trivial_grade {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) {Xd : ℕ} (j : ℕ)
    (hXd : 0 < Xd) :
    1 / ((Xd : ℕ) : ℝ)
        * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
            ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                * shortSum (doorChiCoeff χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
                    ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ 4 := by
  have hXd0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := by exact_mod_cast hXd
  have hhN : 0 < 2 ^ j := Nat.two_pow_pos j
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hhN
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  -- ⟦the pointwise bound⟧
  have hpt : ∀ y ∈ Set.Icc ((Xd : ℕ) : ℝ) (2 * ((Xd : ℕ) : ℝ)),
      ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
          * shortSum (doorChiCoeff χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
              ((2 ^ j : ℕ) : ℝ)‖ ^ 2 ≤ 4 := by
    intro y hy
    have hy0 : (0 : ℝ) ≤ y := le_trans hXd0.le hy.1
    have hs := norm_shortSum_le (norm_doorChiCoeff_le_one χ M)
      (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) (x := y) (hlen := ((2 ^ j : ℕ) : ℝ)) hy0 hh0.le
    have hnm : ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
        * shortSum (doorChiCoeff χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖
        = 1 / ((2 ^ j : ℕ) : ℝ)
            * ‖shortSum (doorChiCoeff χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
                ((2 ^ j : ℕ) : ℝ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb : ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
        * shortSum (doorChiCoeff χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
            ((2 ^ j : ℕ) : ℝ)‖ ≤ 2 := by
      rw [hnm]
      have h2h : ‖shortSum (doorChiCoeff χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
          ((2 ^ j : ℕ) : ℝ)‖ ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by linarith
      calc 1 / ((2 ^ j : ℕ) : ℝ)
            * ‖shortSum (doorChiCoeff χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
                ((2 ^ j : ℕ) : ℝ)‖
          ≤ 1 / ((2 ^ j : ℕ) : ℝ) * (2 * ((2 ^ j : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left h2h (by positivity)
        _ = 2 := by field_simp
    have h0 := norm_nonneg (((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
      * shortSum (doorChiCoeff χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ))
    nlinarith
  -- ⟦the mean⟧
  have hint := shortSum_sq_intervalIntegrable (doorChiCoeff χ M)
    (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) ((2 ^ j : ℕ) : ℝ) ((Xd : ℕ) : ℝ) (2 * ((Xd : ℕ) : ℝ))
  have hmono := intervalIntegral.integral_mono_on (a := ((Xd : ℕ) : ℝ))
    (b := 2 * ((Xd : ℕ) : ℝ)) (by linarith) hint intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hbound : (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
      ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
          * shortSum (doorChiCoeff χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
              ((2 ^ j : ℕ) : ℝ)‖ ^ 2) ≤ ((Xd : ℕ) : ℝ) * 4 := by
    calc _ ≤ (2 * ((Xd : ℕ) : ℝ) - ((Xd : ℕ) : ℝ)) * 4 := hmono
      _ = ((Xd : ℕ) : ℝ) * 4 := by ring
  calc 1 / ((Xd : ℕ) : ℝ)
        * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
            ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                * shortSum (doorChiCoeff χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
                    ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ 1 / ((Xd : ℕ) : ℝ) * (((Xd : ℕ) : ℝ) * 4) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 4 := by field_simp

/-! ## §3 — THE WORKHOSE: THE FIVE-SUMMAND MEAN SQUARE AT THE DOOR'S BARE DATUM

`m4_meansq_per_chi_gen` instantiated at

  `a := winCutH X_d (doorChiCoeff χ M)`,  `b := doorChiCoeff χ M`,  `cf := liouChi χ`,
  `bfam j := memSPunctCoeff 𝒫 𝒬K 2 j (liouChi χ)`,
  `X := X_d`,  `N := 2X_d`,  `h := 2^j`,  `Rrad := seamRad X`,  `Rbar := 4·R̄₀`,

with the ENTIRE class-(C) list of the module header discharged in place, and the conclusion
transported off the cut by `M4DoorRow.shortSum_winCutH_seamS0`. -/

set_option maxHeartbeats 4000000 in
-- the ~90-binder instantiation: `DoorRowCarried`'s ~85-conjunct destructuring plus the
-- capstone's 86-argument application (four hoisted suppliers, one statement) is what costs
-- the heartbeats — no tactic search happens here, every step is `exact`-shaped
/-- **THE DOOR ROW'S MEAN SQUARE, CARRIED** (`m4_door_meansq_carried`).  At every door
instance meeting `DoorRowCarried`, the door's sieved, χ-twisted, UN-PHASED datum satisfies
the capstone's five-summand mean-square bound at the grade `B` — the datum binders
discharged, the register carried.

The `∃`-bound constants are the K6 discipline's: `Cq, cq, T₀, Xcap, Cs, Ccc, Kfl` are
`m4_meansq_per_chi_gen`'s; `Xsk` is `CaseAWide.m4_supplier_complete`'s wide threshold; `Kcf`
is `CofactorSupplier.capFreeFloor3_pieceDatum`'s masked-floor constant; `Ctail` is
`M4DoorRow.m4_door_tail_supply`'s coprime-tail mass constant.  All four suppliers are hoisted
ONCE, outside the instance quantifier. -/
theorem m4_door_meansq_carried (Qm : ℕ) :
    ∃ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ,
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 0 < q → q ≤ Qm →
        ∀ (M Xd j : ℕ) (B : ℝ), 1 ≤ M → doorRowFloor M ≤ j →
          DoorRowCarried Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B →
            1 / ((Xd : ℕ) : ℝ)
                * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
                    ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                        * shortSum (doorChiCoeff χ M)
                            (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
              ≤ B := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hgen⟩ :=
    m4_meansq_per_chi_gen Qm
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  obtain ⟨Kcf, hKcf0, hcfl⟩ := capFreeFloor3_pieceDatum Qm
  obtain ⟨Ctail, hCtail0, htail⟩ := m4_door_tail_supply
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro q χ hq hqQm M Xd j B hM hj0 hcar
  obtain ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, C₁', M₀,
    cqS, cgS, cW, SW, Rbar0, Dmask,
    hXdX, hhj, hXee, hlX2, hhX, hhceil, hTann, hceil5, hT₀le, hTbot, hLXL, hLe, hL256,
    hXdQ, hP3, hlogP2, hQbot, hQlog, hQL, hPlow, hQhigh, hPQ, hQ0, hHX, hH2, hPj1, hQXd,
    hXdbig, hdom, hW5, hkth, hMtX, hC16, hRradW, hthinpin, hMtpin, hkkg, hMtY,
    hRrad0, hV1, hVδ, hlogV, hδsq, hksthr, hVJg, hCb0, hCbound, hXthr,
    hX₀k, hMfl0k, hk2, hkX, hgateW, hYpin, hWY, hXY, hthrY,
    hcqgate, hCqgate, hε0, hεup, habs,
    hQlogXd, hdomband, hlogb, hPQratio, h2688,
    hDmask0, hdebit, hcfthr,
    hc0, hce, hc1, hblk, hbox, hD1, hDk, hX₀j, hsqXa, hpin,
    hXae, hMXa, hXaX, hMfl0, hboxw, hS0, hSbd, hendGen, hRbdU, hRbar00, hRgrade,
    hend, hT0band, hcff, hgP1, hgRows, hL4096, henv⟩ := hcar
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
    have hA : 2 ^ 18 ≤ Adoor M := Adoor_ge M
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
    exact hcfl q χ (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 𝒥
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
  -- ⟦THE CAPSTONE⟧
  have hres := hgen q χ hqQm (2 * Xd) Xd P Q M (winCutH Xd (doorChiCoeff χ M)) (liouChi χ)
    (doorChiCoeff χ M)
    (fun i => memSPunctCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 i
      (liouChi χ))
    ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) δ' V VJ L Cb (seamRad ((Xd : ℕ) : ℝ)) (4 * Rbar0)
    kmin Ymax ε _ _ C₁' M₀
    rfl rfl hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe hM hXdQ hQ1h hP3
    hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkkg hMtY
    hRrad0 le_rfl le_rfl hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0k hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 hεup habs hEP2 le_rfl
    (doorRow_ha1 χ M Xd) (norm_liouChi_le_one χ)
    (fun n hn => doorRow_hsupp0 χ M Xd n hn) (fun n hn => doorRow_hasupp χ M Xd n hn)
    hMtail0 hMtail
    (norm_doorChiCoeff_le_one χ M) (fun i n => norm_doorPunctCoeff_le_one χ M i n)
    (by positivity) hRgrade hsockR hcoefBand hcoefPin hT0band hcff hgP1 hgRows hL4096
  -- ⟦THE DATUM BRIDGE⟧ the cut is invisible to the row's short sum
  simp only [shortSum_winCutH_seamS0] at hres
  exact le_trans hres henv

/-! ## §4 — THE GRADED ROW DATUM AT THE DOOR

`M4Maximal.M4ChiDyadicRowMeanSq R M k MS`, split at the door's own floor `doorRowFloor M`:
above it §3 fires at the carried register, below it §2's absolute `4`.  ⟦WALL 2⟧'s repair is
what makes the two halves compatible — the grade is `MS j H`, not `MS H`. -/

/-- **THE DOOR'S DYADIC ROW, CARRIED** (`m4_dyadicRow_carried`).  `M4ChiDyadicRowMeanSq` at
the door datum, from THE FINAL CARRIED REGISTER: the per-instance `DoorRowCarried` (which
holds the `T₀`-band arm, the endpoint gate and every regime gate) plus the trivial grade at
the small lengths, plus the modulus cap `arcDen 12 H ≤ Qm` that puts the door's characters
inside `m4_meansq_per_chi_gen`'s range. -/
theorem m4_dyadicRow_carried (Qm : ℕ) :
    ∃ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ,
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧
      ∀ (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloor M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloor M ≤ j →
            ∀ s ≤ H,
              DoorRowCarried Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                (doorLadder R.x H (i + 1) + s) j (MS j H)) →
        M4ChiDyadicRowMeanSq R M k MS := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_door_meansq_carried Qm
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro R M k MS hM hQm htriv hcar H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hApos : 0 < doorLadder R.x H (i + 1) + s := by
    have := doorLadder_floor hxH (i + 1); omega
  by_cases hcase : doorRowFloor M ≤ j
  · -- ⟦the capstone speaks: §3 at the carried register⟧
    have hqQm : q ≤ Qm := by
      have hR : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hR
    exact hrow q χ hq hqQm M (doorLadder R.x H (i + 1) + s) j (MS j H) hM hcase
      (hcar H hlo hhi q hq hqQ i hik χ j hjL hcase s hsH)
  · -- ⟦below the floor: the trivial grade⟧
    exact le_trans (doorRow_trivial_grade χ M j hApos) (htriv j H (not_le.mp hcase))

/-! ## §5 — THE STRUCTURAL CLOSE

`M4Maximal.m4_wave_closed_of_dyadicRow` ∘ §4 ∘ `M4NonCoprime.m4_nonCoprime_classMeanSq`.
⟦R2⟧'s slot is the coprime-block supply at its interval/length-general shape — carried named,
because the landed adapters (the dilation, the `d₀`-to-one re-index) consume exactly that and
nothing weaker.  ⟦R3⟧ is §4.  The conclusion is `¬ logChowla2Fails R.eps R.x R.ω`. -/

set_option maxHeartbeats 1600000 in
-- same cause as §3: elaborating the register (which mentions `DoorRowCarried` under six
-- binders) against `m4_wave_closed_of_dyadicRow`'s own list is the whole cost
/-- **THE M4 WAVE, STRUCTURALLY CLOSED** (`m4_wave_structurally_closed`).

  ⟦THE FINAL CARRIED REGISTER⟧ → `¬ logChowla2Fails R.eps R.x R.ω`,

with the register in the module header's three classes.  The two ANALYTIC arms are

* the `T₀`-band arm, inside `DoorRowCarried` (`M4T0Datum.m4_hT0band_at_door` is the plug),
* the coprime-supply arm `M4CoprimeBlockMeanSq R M (m4BclGraded j₀ (2·MSan) (2·MStr))`;

everything else is regime arithmetic (the `g`-arm/`U1floor` shapes of the outer register, the
drift and delivered lines, the two `M4NonCoprime` gates, the modulus cap) or witnessed here.

The floor is the door's own, `j₀ = doorRowFloor M = M·Adoor M`; `M4Maximal`'s ⟦THE
CONSUMPTION NOTE⟧ is the ordering that makes it workable (`M` fixed before `U1floor`). -/
theorem m4_wave_structurally_closed (Qm : ℕ) :
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
                  DoorRowCarried Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            -- ⟦R2's two gates⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.log (H : ℝ) ≤ (2 : ℝ) ^ (21845 : ℕ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦ARM 2: the coprime supply, interval/length-general⟧
            M4CoprimeBlockMeanSq R M
              (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_dyadicRow_carried Qm
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_dyadicRow
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcar hlogcap harc hcp
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H)
      (fun H => 2 * MStr H) H := fun H =>
    m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
  -- ⟦R2⟧ the wave asks only the NON-COPRIME classes; `m4_nonCoprime_classMeanSq` delivers all
  have hnc : M4ClassBlockMeanSq R M k
      (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_nonCoprime_classMeanSq (k := k) hM hBcl0 hlogcap harc hcp
  refine hR δ Braw MS MSan MStr (doorRowFloor M) M k hgates hMSan0 hMStr0 hBraw0 han htr
    hdrift hdel hrest (hrow R M k MS hM hQm htriv hcar) ?_
  intro H hlo hhi q hq hqQ i hik r hrq _hncop
  exact hnc H hlo hhi q hq hqQ i hik r hrq

end Salt.MR

end
