/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4T0Discharge
import Salt.MR.M4CoprimeSupply

/-!
# `M4Collapse` — ⟦THE SWAP⟧: the M4 wave's SECOND carried analytic arm, discharged

`M4T0Discharge.m4_wave_closed_T0_discharged` left ONE analytic arm carried — the coprime
supply `M4NonCoprime.M4CoprimeBlockMeanSq R M (m4BclGraded j₀ (2·MSan) (2·MStr))`, read at
the OVER-GENERAL interface.  ⟦COPRIME-SCOPE⟧ then proved that interface unsuppliable (its
grade's small-length summand is off by `H/L` for any route) and landed the NARROWED twin
`M4CoprimeBlockMeanSqN` beside it, together with the chain that supplies the twin from the
free-base row datum:

  `M4CoprimeSupply.m4_coprimeN_supplied` : `M4ChiFreeRowMeanSq R M MS` → the twin,
  `M4NonCoprime.m4_nonCoprime_classMeanSq_N` : the twin → `M4ClassBlockMeanSq R M k Bcl`.

This file performs THE SWAP: the exit re-composed with that chain in place of the raw arm.
The carried analytic item is no longer a coprime BLOCK family but the door's own ROW datum —
the same currency the `T₀`-free register already speaks (`M4Maximal.M4ChiDyadicRowMeanSq`'s
mean square, with the block bottom freed).

## ⟦WHY THE EXIT IS RE-COMPOSED AND NOT PATCHED⟧

`m4_wave_closed_T0_discharged` consumes `M4CoprimeBlockMeanSq` (the full interface) *inside*
its own proof, through `M4DoorClose.m4_wave_structurally_closed` and
`M4NonCoprime.m4_nonCoprime_classMeanSq`.  The narrowed twin does not imply the full one, so
no adapter exists in that direction; the swap is therefore performed by re-running the two
compositions here, ADDITIVELY, off the same three landed stones
(`M4Maximal.m4_wave_closed_of_dyadicRow`, `M4DoorClose.m4_dyadicRow_carried`,
`M4T0Discharge.doorRowCarried_of_t0free`).  Nothing upstream moves; both landed exits stand.

## ⟦THE REGISTER, LINE BY LINE⟧ — the diff against `m4_wave_closed_T0_discharged`

ONE line replaced, THREE added, and no other byte moves:

* **replaced** — `M4CoprimeBlockMeanSq R M (m4BclGraded (doorRowFloor M) …)`
  becomes `M4CoprimeSupply.M4ChiFreeRowMeanSq R M MS`, the free-base row datum at the
  register's OWN grade `MS` (no new envelope: the same `MS` the `T₀`-free register grades
  each instance by);
* **added** — ⟦G1⟧ `arcDen 12 H ^ 2 ≤ MStr H`, ⟦G2⟧ `44·MSan H + 87 ≤ (4/3)^{j₀}` and ⟦the
  regime
  fact⟧ `8·arcDen 12 H ≤ H`, all three `H`-only thresholds of class (a), all three exactly
  `m4_coprimeN_supplied`'s (see `M4CoprimeSupply`'s ⟦THE TWO GATES⟧ and ⟦THE REGIME FACT
  CARRIED⟧ for why each is a threshold and not a saving).

The landed line `2·arcDen 12 H ≤ H` is kept although ⟦the regime fact⟧ subsumes it
(`arcDen 12 H ≥ 1` past the window floor, `M4NonCoprime.one_le_arcDen_of_regime`): keeping it
makes the machine-diff against the landed exit exactly one replacement plus three additions.
A consumer may drop it.

## ⟦THE FINAL REGISTER⟧ — the S11 spine's consumption contract

What `m4_wave_closed_coprime_discharged` asks, in the two classes.  Nothing else is asked;
this list IS the contract.

**(a) REGIME-ABSORBABLE GATES** — every one an inequality in the regime's own parameters,
choosable by the spine before any datum is exhibited:

1. the OUTER shapes, chosen BEFORE `R`: `U1floor ≤ R.Hlo` and `g R.Hhi R.ω ≤ R.x` at the
   spine's own `U1floor : ℕ` and `g : ℕ → ℕ → ℕ` (the `g`-arm/`U1floor` shapes — the exit
   quantifies over both, so the spine may demand `R.x` as large as it likes in terms of
   `R.Hhi` and `R.ω`);
2. `M4DoorGates Cg R M k δ` — the EIGHT fields of `M4Close.M4DoorGates`: `hM` (`1 ≤ M`),
   `hδ` (`0 < δ`), `hMδ` (`24·Cg/δ ≤ M`), `hlogω` (`4 ≤ log ω`), `hpow` (`2^{k+1} ≤ R.x`),
   `hcount` (`k ≤ log ω/log 2 + 2`), `hreach` (`doorLadder R.x H k ≤ R.x/R.ω` at every `H`
   in range), `hblocks` (`SieveBlockGate (Adoor M) (3072M) M 2` at every door block);
3. `1 ≤ M`;
4. the three envelope positivities `0 ≤ MSan H`, `0 ≤ MStr H`, `0 ≤ Braw H`;
5. the two envelope gates `MS j H ≤ MSan H` at `j₀ ≤ j` and `MS j H ≤ MStr H` at `j < j₀`,
   `j₀ = doorRowFloor M = M·Adoor M`;
6. the `q`-graded drift price
   `(1 + 2π·arcDen 12 H/q)²·(q²·(3·m4BclGraded j₀ (2·MSan) (2·MStr) H)) ≤ Braw H`;
7. `√(Braw H) ≤ mrtDeliveredGrade (C/2) H`;
8. `δ/4 + 4·2^k/R.x ≤ mrtDeliveredGrade (C/2) H`;
9. the modulus cap `arcDen 12 H ≤ Qm`;
10. the small lengths' trivial grade `4 ≤ MS j H` at `j < j₀`;
11. the PER-INSTANCE `T₀`-free register `DoorRowCarriedT0 Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl
    Xsk Kcf Ctail χ M (doorLadder R.x H (i+1) + s) j (MS j H)`, at every
    `H ∈ [R.Hlo, R.Hhi]`, every `q ≤ arcDen 12 H`, every `i < k`, every `χ mod q`, every
    `j ≤ log₂H` above the floor and every shift `s ≤ H` — itself ~98 conjuncts: the scale
    page at the BLOCK scale `X = X_d`, the band gates, the door gates, the socket's ~25, the
    tail threshold, the endpoint `doorChiCoeff χ M X_d = 0`, the `DoorRowT0Gates` EIGHT
    (`X₀w ≤ √X`, `√X ≤ Xw`, `Xw ≤ X`, `1 ≤ Ddis`, `Ddis(Xw+1) ≤ X−1`, the `700·(…)`
    loglog threshold, `seamT0 X + Tstar(2X) ≤ 3X`, `Ddis^{−1/4} ≤ (log X)^{−1009/90000}`)
    and the instance envelope;
12. the dilation cap, `M`-RELATIVE: `arcDen 12 H < calP (Adoor M) (3072M) 1 = 2^{Adoor M}`
    (`M4Residue.door_dilation_gate'`);
13. `2·arcDen 12 H ≤ H` (kept; see ⟦THE REGISTER, LINE BY LINE⟧);
14. ⟦the regime fact⟧ `8·arcDen 12 H ≤ H`;
15. ⟦G1⟧ `arcDen 12 H ^ 2 ≤ MStr H`;
16. ⟦G2⟧ `44·MSan H + 87 ≤ (4/3)^{j₀}`.

**(b) WITNESSED DATA** — what the spine must exhibit, and check non-vacuous: `C ≥ 0`,
`U1floor`, `g`, then `δ`, `Braw`, `MS`, `MSan`, `MStr`, `M`, `k`.  `R` is NOT witnessed: the
exit produces it (only `R.eps = ε`, `U1floor ≤ R.Hlo`, `g R.Hhi R.ω ≤ R.x` are visible).
The anti-vacuity duty sits at line 11: the instances at the BOTTOM ladder rungs and the TOP
dyadic length are where the scale page's coupling gate `h ≤ X·(log X)^{−1/5}` bites, and
`hreach` + the `g`-arm are what buy the room (`doorLadder R.x H k ≤ R.x/R.ω` with `R.x`
chosen against `R.ω·R.Hhi`).

**(c) THE ONE ANALYTIC ITEM STILL CARRIED** — `M4ChiFreeRowMeanSq R M MS`.  See ⟦THE WALL⟧.

## ⟦THE WALL⟧ — why the row datum is carried and not derived

The `T₀`-free register (line 11) supplies the row's mean square at the LADDER bases
`doorLadder R.x H (i+1) + s`, `s ≤ H`, and — under ⟦W5⟧'s ruled `∀d` extension — would
supply it at the DILATED bases `⌊doorLadder R.x H (i+1)/d⌋ − 1 + s`, `s ≤ ⌊H/d⌋ + 1`,
`d ≤ arcDen 12 H`, which are exactly the two families
`M4NonCoprime.m4_nonCoprime_classMeanSq_N` reads its coprime datum at.

`M4CoprimeSupply.M4ChiFreeRowMeanSq` is quantified over a FREE base (`∀ A : ℕ, 0 < A → ∀ s ≤
L`, `M4CoprimeSupply.lean` §2).  No register can discharge that: at `A ≍ 2^j` the mean square
is `≍ 1` while the grade `MS j H` above the floor is a saving, and the capstone is silent
there anyway (its coupling gate `h ≤ X(log X)^{−1/5}` fails at `X ≍ h`).  So the free base is
over-general in exactly the genre ⟦COPRIME-SCOPE⟧ found one level up — narrowed there in the
LENGTH (`H ≤ arcDen 12 H·L`), still free here in the BASE.  The repair is a ruled twin of the
row interface with the base tied to the ladder, threaded through `M4CoprimeSupply` §2/§3/§1
(each consumes its input at the SAME `A` it concludes at, so the threading is mechanical) —
a statement design, not an executor's call.  Until it is ruled, the row datum is carried.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE SWAP

`M4Maximal.m4_wave_closed_of_dyadicRow` ∘ `M4DoorClose.m4_dyadicRow_carried` ∘
`M4T0Discharge.doorRowCarried_of_t0free`, with the non-coprime class datum produced by
`m4_nonCoprime_classMeanSq_N` ∘ `m4_coprimeN_supplied` instead of by
`m4_nonCoprime_classMeanSq` at the raw arm.  The floor is the door's own,
`j₀ = doorRowFloor M`, at both consumption sites. -/

set_option maxHeartbeats 1600000 in
-- the same cause as `M4DoorClose` §5 and `M4T0Discharge` §5: the register mentions
-- `DoorRowCarriedT0` under six binders and is elaborated against
-- `m4_wave_closed_of_dyadicRow`'s own list; no tactic search happens below
/-- **THE M4 WAVE, THE COPRIME ARM DISCHARGED** (`m4_wave_closed_coprime_discharged`).

`M4T0Discharge.m4_wave_closed_T0_discharged` with ARM 2 swapped: the coprime supply is no
longer assumed at `M4CoprimeBlockMeanSq` (the interface ⟦COPRIME-SCOPE⟧ proved unsuppliable)
but DERIVED, through `M4CoprimeSupply.m4_coprimeN_supplied` and
`M4NonCoprime.m4_nonCoprime_classMeanSq_N`, from the free-base row datum
`M4ChiFreeRowMeanSq R M MS` at the register's own grade `MS`.

What remains carried is ONE analytic item — that row datum — plus regime arithmetic.  The
module header enumerates the whole register (⟦THE FINAL REGISTER⟧) and says precisely why
the row datum is not itself discharged here (⟦THE WALL⟧). -/
theorem m4_wave_closed_coprime_discharged (Qm : ℕ) :
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
                  DoorRowCarriedT0 Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦the regime fact⟧ (subsumes the line above)
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦G1⟧ the trivial envelope dominates the arc denominator
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            -- ⟦G2⟧ the slack-`4` residue against the floor's own constant
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloor M) →
            -- ⟦ARM 2 DISCHARGED: the free-base row datum is the ONLY analytic carry left⟧
            M4ChiFreeRowMeanSq R M MS →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hbridge⟩ := doorRowCarried_of_t0free Qm
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_dyadicRow_carried
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_dyadicRow
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl Qm, Xsk, Kcf Qm, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl Qm, hXsk0, hKcf0 Qm, hCtail0,
    hK0, hX₀0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcarT0 hgate harc harc8 hG1 hG2 hrowfree
  -- ⟦ARM 1⟧ the T₀-free register becomes the carried one, instance by instance
  have hcar : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloor M ≤ j →
        ∀ s ≤ H,
          DoorRowCarried Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
            (doorLadder R.x H (i + 1) + s) j (MS j H) := by
    intro H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH
    haveI : NeZero q := ⟨by omega⟩
    have hqQm : q ≤ Qm := by
      have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hRq
    exact hbridge Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail q χ M
      (doorLadder R.x H (i + 1) + s) j (MS j H) hqQm
      (hcarT0 H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH)
  -- ⟦ARM 2⟧ the row datum → the narrowed coprime family → every class of `q`
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H)
      (fun H => 2 * MStr H) H := fun H =>
    m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
  have hcpN : M4CoprimeBlockMeanSqN R M
      (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_coprimeN_supplied (doorRowFloor M) hMSan0 hMStr0 han hG1 hG2 harc8 hrowfree
  have hnc : M4ClassBlockMeanSq R M k
      (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_nonCoprime_classMeanSq_N (k := k) hM hBcl0 hgate harc hcpN
  refine hR δ Braw MS MSan MStr (doorRowFloor M) M k hgates hMSan0 hMStr0 hBraw0 han htr
    hdrift hdel hrest (hrow R Qm M k MS hM hQm htriv hcar) ?_
  intro H hlo hhi q hq hqQ i hik r hrq _hncop
  exact hnc H hlo hhi q hq hqQ i hik r hrq

/-! ## §2 — THE COLLISION FORM

The house's twin (`M4WaveClosed.m4_wave_closed_False`'s convention): the same register, with
the failure branch assumed at the exit's own regime, closes to `False`. -/

set_option maxHeartbeats 1600000 in
-- §1's budget, for §1's cause: the twin restates the whole register (`DoorRowCarriedT0`
-- under six binders) and elaborates it against §1's; the proof itself is one destructuring
/-- **THE COLLISION FORM** (`m4_wave_closed_coprime_discharged_False`).  §1's register with
`logChowla2Fails R.eps R.x R.ω` assumed: the chain closes to `False`.  Byte-for-byte §1 with
`¬ P` read as `P → False`. -/
theorem m4_wave_closed_coprime_discharged_False (Qm : ℕ) :
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
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloor M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0 Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloor M) →
            M4ChiFreeRowMeanSq R M MS →
            logChowla2Fails R.eps R.x R.ω → False := by
  obtain ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩ := m4_wave_closed_coprime_discharged Qm
  exact ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩

/-! ## §3 — THE LADDER'S LOWER BOUND (banked for ⟦THE WALL⟧'s repair)

The base-narrowed row interface ⟦THE WALL⟧ calls for must be dischargeable at
`m4_nonCoprime_classMeanSq_N`'s two consumption sites, i.e. at

* `A = doorLadder R.x H (i+1)`, `L = H` (the coprime branch), and
* `A = ⌊doorLadder R.x H (i+1)/d₀⌋ − 1`, `L = ⌊H/d₀⌋ + 1` (the dilated branch),

and a narrowing of the shape `Φ H · L ≤ A` is what makes the capstone's coupling gate
`h ≤ X·(log X)^{−1/5}` available at `X = A + s`, `h = 2^j ≤ L` — the gate is a RATIO, so the
dilated branch inherits it from the coprime one unchanged (`A` and `L` are both divided by
`d₀`).  What the ladder itself owes is the LOWER bound below: `doorLadder_floor` gives only
`H + 1 ≤ X_i`, which is exactly the comparison the narrowing cannot use.  With this, and with
`M4Close.M4DoorGates.hcount` (`k ≤ log ω/log 2 + 2`, whence `2^k ≤ 4·R.ω`), every rung in
range satisfies `R.x/(4·R.ω) ≤ X_{i+1}`, and the `g`-arm (`g R.Hhi R.ω ≤ R.x`, with `g` the
consumer's own) buys `Φ H · H ≤ R.x/(4·R.ω)`.  No consumer yet: this is banked. -/

/-- **THE LADDER'S GEOMETRIC LOWER BOUND** (`doorLadder_pow_lower`).  `x/2^i ≤ X_i`: the
descent halves at worst, since `X_{i+1} = ⌊(X_i + H + 1)/2⌋ ≥ ⌊X_i/2⌋`.  The companion of
`M4Door.doorLadder_floor` (`H + 1 ≤ X_i`) on the other side — see §3's header. -/
theorem doorLadder_pow_lower (x H i : ℕ) : x / 2 ^ i ≤ doorLadder x H i := by
  induction i with
  | zero => simp
  | succ n ih =>
      have hdiv : x / 2 ^ (n + 1) = x / 2 ^ n / 2 := by
        rw [pow_succ, Nat.div_div_eq_div_mul]
      rw [doorLadder_succ, hdiv]
      omega

/-! ## §GK — the G-lever twin

⟦THE BLOCK IS CLEARED⟧ this section was banked BLOCKED: both exits compose five suppliers
owned by other files, and none carried a `_gk` sibling.  All five now do —
`M4T0Discharge`'s `DoorRowCarriedT0_gk` / `doorRowCarried_of_t0free_gk`, `M4DoorClose`'s
`m4_dyadicRow_carried_gk`, `M4Maximal`'s `m4_wave_closed_of_dyadicRow_gk`,
`M4CoprimeSupply`'s `M4ChiFreeRowMeanSq_gk` / `m4_coprimeN_supplied_gk` and
`M4NonCoprime`'s `M4CoprimeBlockMeanSqN_gk` / `m4_nonCoprime_classMeanSq_N_gk` — so the two
twins below are the landed proofs with those names substituted.

The only literal this file reads directly is
`arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)` — LEVEL 1, hence K-INVARIANT
(`GLever.calP_gk_one_eq`); it is written at `s13GK K M` for uniformity with
`m4_nonCoprime_classMeanSq_N_gk`'s slot, which is the SAME symbol.  `hK : K ≤ 1.7·10⁸` is
`m4_meansq_per_chi_gen_gk`'s frame side condition, inherited through `M4DoorClose`. -/


/-- **THE M4 WAVE, BOTH ARMS DISCHARGED, AT THE LEVER** — `m4_wave_closed_coprime_discharged`
(:158). -/
theorem m4_wave_closed_coprime_discharged_gk (K : ℕ) (hK : K ≤ 170000000) (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ → 1 ≤ M →
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
                  DoorRowCarriedT0_gk K Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦the regime fact⟧ (subsumes the line above)
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦G1⟧ the trivial envelope dominates the arc denominator
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            -- ⟦G2⟧ the slack-`4` residue against the floor's own constant
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloor M) →
            -- ⟦ARM 2 DISCHARGED: the free-base row datum is the ONLY analytic carry left⟧
            M4ChiFreeRowMeanSq_gk K R M MS →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hbridge⟩ := doorRowCarried_of_t0free_gk K Qm
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_dyadicRow_carried_gk K hK
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_dyadicRow_gk K
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl Qm, Xsk, Kcf Qm, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl Qm, hXsk0, hKcf0 Qm, hCtail0,
    hK0, hX₀0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcarT0 hgate harc harc8 hG1 hG2 hrowfree
  -- ⟦ARM 1⟧ the T₀-free register becomes the carried one, instance by instance
  have hcar : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloor M ≤ j →
        ∀ s ≤ H,
          DoorRowCarried_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
            (doorLadder R.x H (i + 1) + s) j (MS j H) := by
    intro H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH
    haveI : NeZero q := ⟨by omega⟩
    have hqQm : q ≤ Qm := by
      have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hRq
    exact hbridge Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail q χ M
      (doorLadder R.x H (i + 1) + s) j (MS j H) hqQm
      (hcarT0 H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH)
  -- ⟦ARM 2⟧ the row datum → the narrowed coprime family → every class of `q`
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H)
      (fun H => 2 * MStr H) H := fun H =>
    m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
  have hcpN : M4CoprimeBlockMeanSqN_gk K R M
      (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_coprimeN_supplied_gk K (doorRowFloor M) hMSan0 hMStr0 han hG1 hG2 harc8 hrowfree
  have hnc : M4ClassBlockMeanSq_gk K R M k
      (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_nonCoprime_classMeanSq_N_gk K (k := k) hM hBcl0 hgate harc hcpN
  refine hR δ Braw MS MSan MStr (doorRowFloor M) M k hgates hMSan0 hMStr0 hBraw0 han htr
    hdrift hdel hrest (hrow R Qm M k MS hM hQm htriv hcar) ?_
  intro H hlo hhi q hq hqQ i hik r hrq _hncop
  exact hnc H hlo hhi q hq hqQ i hik r hrq

/-- **THE SAME, IN `False` FORM, AT THE LEVER** —
`m4_wave_closed_coprime_discharged_False` (:254). -/
theorem m4_wave_closed_coprime_discharged_False_gk (K : ℕ) (hK : K ≤ 170000000)
    (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ → 1 ≤ M →
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
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloor M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0_gk K Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloor M) →
            M4ChiFreeRowMeanSq_gk K R M MS →
            logChowla2Fails R.eps R.x R.ω → False := by
  obtain ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩ := m4_wave_closed_coprime_discharged_gk K hK Qm
  exact ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩

end Salt.MR

end

-- #audit (temporary)
