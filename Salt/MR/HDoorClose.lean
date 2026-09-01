/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HDoorSupply
import Salt.MR.M4WaveClosed
import Salt.MR.M4CoprimeSupply

/-!
# QUEUE 7b — THE CLOSING WAVE: the door's mean-square lane at the inflated cap (`HDoorClose`)

Commissioned by the helm 2026-08-31 18:52, executor tier: discharge `M4BlockMeanSqSupQH 2`
and close `HDoorArc.M4SievedDoorSqH`'s slot onto the same datum the `h = 1` door closes onto.

## ⛔ THE ROUTE THE COMMISSION NAMED IS THE LANE `M4WaveClosed` ABANDONED — flagged, then re-cut

The commission routed through `HDoorSupply.m4_blockMeanSqSupQH_of_classPriceH`, the `h`-family
of `M4ClassPrice.m4_blockMeanSqSupQ_of_classPrice`.  `M4WaveClosed`'s own header
(`:16-24`) says of that node:

> *"That lemma is true and its arithmetic is exact, but its hypothesis is **not what a
> mean-square supplier can deliver** … it asserts cancellation in *every* short interval of the
> block — strictly stronger than anything the MRT method proves … Taking the maximum over the
> block before squaring throws the method away."*

⇒ **routing the close through it would discharge the socket onto a demand the method cannot
meet: a green build, a clean audit, and a hypothesis with no possible supplier.**  §2 of that
file exists to replace exactly this step.  **This module takes the replacement.**  No landed
byte moves and no statement act is taken — only the lane changes.

## The lane, and where the cap is READ

```
M4ChiBlockMeanSqH h        ⟵ the ESTIMATE, untouched (the door's conditional at h = 1 too)
  │  m4_classMeanSq_of_chiMeanSqH      cap: THREAD
  ├── + the non-coprime slot           cap: THREAD (carried, exactly as at h = 1)
  ▼
M4ClassBlockMeanSqH h
  │  m4_blockMeanSqSupQH_of_classMeanSqH   cap: THREAD
  ▼
M4BlockMeanSqSupQH h       ⟵ HDoorSupply §9.3's input
  │  m4_cover_assembly_supQH · m4_sievedDoorSqH_of_supH_uniform
  ▼
M4SievedDoorSqH h          ⟵ HDoorArc N4s, the socket 7b left open
  │  m4_doorL2_supply_500_H
  ▼
MRTUniformityXiL2H h       ⟵ the twisted L² door
```

**Every link on this lane carries the cap as a THREAD.**  Not one of them reads it — the
`q`-uniform machinery §1 of the door-slot measurement enumerated (`classSup`,
`classSup_le_inv_totient_sum_doorChiSup`, `le_doorChiSup`, `sum_windowClass_memSCoeff`,
`norm_sum_residueClassOn_liou_le`) is the whole content, and it never sees the allowance.

## ⚠️ WHAT THIS CLOSES, AND WHAT IT DOES NOT — read before citing

✅ **CLOSED: the CAP.**  At `h = 2` the door predicate needs *no gate, no floor and no constant*
that the `h = 1` door did not need.  Every cap-reading arm the wave met is discharged in
`HDoorSupply` (§1–§8) or free at the socket's own floor.

⛔ **NOT CLOSED, AND NOT CLAIMED: the ESTIMATE, AND ITS RANGE.**  `M4ChiBlockMeanSqH 2` asks for
the χ-uniform block mean square at `q ≤ 2·arcDen 12 H` where `M4ChiBlockMeanSq` supplies it at
`q ≤ arcDen 12 H`.  **That widening is a real demand and it is NOT derivable from the `h = 1`
datum** — whether the producers' bound is `q`-uniform is unpriced, and this module does not
price it.  So the honest statement of the close is:

> ***the `h = 2` door needs exactly the `h = 1` door's conditional, restated over a modulus
> range twice as wide — and nothing else.***

That is strictly weaker than "the door predicate is inhabited unconditionally at `h = 2`", and
the difference is the one thing a reader of this file must not blur.
-/

namespace Salt.MR

open scoped BigOperators
open Salt.Entropy.Chowla

/-! ## §1 — the two data, at the inflated cap -/

/-- **THE χ-UNIFORM BLOCK MEAN SQUARE AT THE INFLATED CAP** (`M4ChiBlockMeanSqH`) —
`M4WaveClosed.M4ChiBlockMeanSq` with `q ≤ arcDen 12 H` inflated to `q ≤ h·arcDen 12 H`.
**This is where the ESTIMATE lives and it is the only place the inflation is a real demand.** -/
def M4ChiBlockMeanSqH (h : ℕ) (R : ChowlaRegime) (M k : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (doorChiSup χ M H n) ^ 2
        ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE CLASS BLOCK MEAN SQUARE AT THE INFLATED CAP** (`M4ClassBlockMeanSqH`) —
`M4WaveClosed.M4ClassBlockMeanSq` with the same one change. -/
def M4ClassBlockMeanSqH (h : ℕ) (R : ChowlaRegime) (M k : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
    ∀ i < k, ∀ r, r < q →
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff M) H n q r) ^ 2
        ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-! ## §2 — the χ-reduction and the assembly, both cap-THREAD -/

/-- **THE χ-REDUCTION AT THE INFLATED CAP** (`m4_classMeanSq_of_chiMeanSqH`) — the `h`-family of
`M4WaveClosed.m4_classMeanSq_of_chiMeanSq`.  The cap is a THREAD: `hqQ` is introduced and handed
to `hchi`, and nothing between reads it.  No loss at all, as at `h = 1`. -/
theorem m4_classMeanSq_of_chiMeanSqH {h : ℕ} {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hchi : M4ChiBlockMeanSqH h R M k Bcl) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
      ∀ i < k, ∀ r, r < q → Nat.Coprime q r →
        ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff M) H n q r) ^ 2
          ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by
  intro H hlo hhi q hq hqQ i hik r _ hcop
  haveI : NeZero q := ⟨hq.ne'⟩
  have hpt : ∀ n : ℕ, (classSup (doorSievedCoeff M) H n q r) ^ 2
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup χ M H n) ^ 2 := by
    intro n
    have hle := classSup_le_inv_totient_sum_doorChiSup hcop M H n
    have h0 := classSup_nonneg (doorSievedCoeff M) H n q r
    have hsq : (classSup (doorSievedCoeff M) H n q r) ^ 2
        ≤ ((q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup χ M H n) ^ 2 := by
      nlinarith
    exact hsq.trans (sq_inv_totient_sum_le_sum_sq (fun χ => doorChiSup χ M H n))
  have hstep1 : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (classSup (doorSievedCoeff M) H n q r) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup χ M H n) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup χ M H n) ^ 2
      = (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (doorChiSup χ M H n) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hswap] at hstep1
  refine hstep1.trans ?_
  exact inv_totient_sum_le (fun χ => hchi H hlo hhi q hq hqQ i hik χ)

/-- **THE TWO HALVES, GLUED** (`m4_classBlockMeanSqH_of_chi`) — the `h`-family of the
`by_cases` inside `M4WaveClosed.m4_wave_closed_of_chi`.  The non-coprime slot is CARRIED, not
assumed away, **exactly as it is at `h = 1`**: the landed close does not discharge it either. -/
theorem m4_classBlockMeanSqH_of_chi {h : ℕ} {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hchi : M4ChiBlockMeanSqH h R M k Bcl)
    (hnoncop : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ (h : ℝ) * arcDen 12 H → ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
        ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff M) H n q r) ^ 2
          ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) :
    M4ClassBlockMeanSqH h R M k Bcl := by
  intro H hlo hhi q hq hqQ i hik r hr
  by_cases hcop : Nat.Coprime q r
  · exact m4_classMeanSq_of_chiMeanSqH hchi H hlo hhi q hq hqQ i hik r hr hcop
  · exact hnoncop H hlo hhi q hq hqQ i hik r hr hcop

/-- **THE ASSEMBLY AT THE INFLATED CAP** (`m4_blockMeanSqSupQH_of_classMeanSqH`) — the
`h`-family of `M4WaveClosed.m4_blockMeanSqSupQ_of_classMeanSq`, **and the node the closing wave
exists for**: it lands `HDoorSupply.M4BlockMeanSqSupQH` from the shape a mean-square supplier
actually produces, where the commission's route asked for a pointwise class price.

The split of §1 then Chebyshev at `#(range q) = q`; the cap is a THREAD throughout. -/
theorem m4_blockMeanSqSupQH_of_classMeanSqH {h : ℕ} {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hcl : M4ClassBlockMeanSqH h R M k Bcl) : M4BlockMeanSqSupQH h R M k Bcl := by
  intro H hlo hhi b q hq hqQ i hik
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hpt : ∀ n : ℕ,
      (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (q : ℝ) * ∑ r ∈ Finset.range q, (classSup (doorSievedCoeff M) H n q r) ^ 2 := by
    intro n
    have hsplit := subWindowSup_le_sum_classSup (doorSievedCoeff M) H n hq b
    have h0 := subWindowSup_nonneg (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))
    have hsq : (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (∑ r ∈ Finset.range q, classSup (doorSievedCoeff M) H n q r) ^ 2 := by
      nlinarith
    refine hsq.trans ?_
    have hcheb := sq_sum_le_card_mul_sum_sq
      (s := Finset.range q) (f := fun r => classSup (doorSievedCoeff M) H n q r)
    rwa [Finset.card_range] at hcheb
  have hstep1 : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (q : ℝ) * ∑ r ∈ Finset.range q, (classSup (doorSievedCoeff M) H n q r) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (q : ℝ) * ∑ r ∈ Finset.range q, (classSup (doorSievedCoeff M) H n q r) ^ 2
      = (q : ℝ) * ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff M) H n q r) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  have hper : ∑ r ∈ Finset.range q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff M) H n q r) ^ 2
      ≤ (q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) := by
    calc ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff M) H n q r) ^ 2
        ≤ ∑ _r ∈ Finset.range q,
            (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) :=
          Finset.sum_le_sum fun r hr =>
            hcl H hlo hhi q hq hqQ i hik r (Finset.mem_range.mp hr)
      _ = (q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ (q : ℝ) * ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff M) H n q r) ^ 2 := by rw [← hswap]; exact hstep1
    _ ≤ (q : ℝ) * ((q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ))) :=
        mul_le_mul_of_nonneg_left hper hq0
    _ = Bcl H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by ring

/-! ## §3 — the exits: the socket, the door mint, and the `h = 2` lane -/

/-- **THE SOCKET EXIT AT THE INFLATED CAP** (`m4_sievedDoorSqH_of_classMeanSqH`) — the
`h`-family of `M4WaveClosed.m4_sievedDoorSq_of_classMeanSq`, composed through
`HDoorSupply` §9.3.  The drift line is the `q`-FREE reading, so the price on the page is the
landed absolute one times `h²` and nothing is hidden in a `q`. -/
theorem m4_sievedDoorSqH_of_classMeanSqH {h : ℕ} {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {Bcl Braw : ℕ → ℝ}
    (hgates : M4DoorGates Cg R M k δ) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hdrift : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (1 + 2 * Real.pi) ^ 2 * (((h : ℝ) * arcDen 12 H) ^ 2 * (3 * Bcl H)) ≤ Braw H)
    (hcl : M4ClassBlockMeanSqH h R M k Bcl) :
    M4SievedDoorSqH h R M Braw :=
  m4_sievedDoorSqH_of_blockQH hgates hBcl0 hdrift (m4_blockMeanSqSupQH_of_classMeanSqH hcl)

/-- ⭐⭐ **THE CLOSE** (`m4_sievedDoorSqH_of_chiMeanSqH`) — `HDoorArc`'s N4s socket discharged
from the χ-uniform block mean square and the non-coprime slot at the inflated cap: **the same
two data the `h = 1` door closes onto** (`M4WaveClosed.m4_wave_closed_of_chi`), and nothing
else.

⇒ ***THE CAP IS CLOSED AT `h`.*** Between this statement and the door predicate there is no
gate, no floor and no constant that the `h = 1` lane did not already carry.

⛔ ***AND THE ESTIMATE IS NOT, NOR ITS RANGE.*** `M4ChiBlockMeanSqH h` asks for the χ mean
square at `q ≤ h·arcDen 12 H` where the landed datum supplies `q ≤ arcDen 12 H`. **That
widening is a real demand on the producers and it is NOT derivable here.** The honest reading:
*the `h`-door needs exactly the `1`-door's conditional, restated over an `h`-times wider
modulus range.* -/
theorem m4_sievedDoorSqH_of_chiMeanSqH {h : ℕ} {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {Bcl Braw : ℕ → ℝ}
    (hgates : M4DoorGates Cg R M k δ) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hdrift : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (1 + 2 * Real.pi) ^ 2 * (((h : ℝ) * arcDen 12 H) ^ 2 * (3 * Bcl H)) ≤ Braw H)
    (hchi : M4ChiBlockMeanSqH h R M k Bcl)
    (hnoncop : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ (h : ℝ) * arcDen 12 H → ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
        ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff M) H n q r) ^ 2
          ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) :
    M4SievedDoorSqH h R M Braw :=
  m4_sievedDoorSqH_of_classMeanSqH hgates hBcl0 hdrift
    (m4_classBlockMeanSqH_of_chi hchi hnoncop)

/-- ⭐⭐ **THE TWISTED `L²` DOOR, OFF THE χ DATUM** (`m4_doorL2_supply_500_H_of_chiMeanSqH`) —
`HDoorArc.m4_doorL2_supply_500_H` with its `hsock` replaced by what now discharges it.

**QUEUE 7b's leave-behind is answered as an object: the mint's `hsock` closes.**  What the
twisted door waits on is now, in two names, `M4ChiBlockMeanSqH h` and the non-coprime slot —
**the same pair the untwisted door waits on**, at the wider modulus range. -/
theorem m4_doorL2_supply_500_H_of_chiMeanSqH (h : ℕ) (hh : 0 < h) :
    ∃ (Cg KXi : ℝ), 1 ≤ Cg ∧ 0 < KXi ∧ ∃ H₀ : ℕ,
      ∀ (R : ChowlaRegime), R.eps = 1 / 500 → H₀ ≤ R.Hlo →
        ∀ (Braw Bcl : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
          M4DoorGates Cg R M k δ →
          (∀ H : ℕ, 0 ≤ Braw H) →
          (∀ H : ℕ, 0 ≤ Bcl H) →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
            (1 + 2 * Real.pi) ^ 2 * (((h : ℝ) * arcDen 12 H) ^ 2 * (3 * Bcl H)) ≤ Braw H) →
          M4ChiBlockMeanSqH h R M k Bcl →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q →
            (q : ℝ) ≤ (h : ℝ) * arcDen 12 H → ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
              ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                  (classSup (doorSievedCoeff M) H n q r) ^ 2
                ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            MRTUniformityXiL2H h R (2 * KXi * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ)) := by
  obtain ⟨Cg, KXi, hCg, hKXi, H₀, hmint⟩ := m4_doorL2_supply_500_H h hh
  refine ⟨Cg, KXi, hCg, hKXi, H₀, ?_⟩
  intro R hReps hfloor Braw Bcl Bceil δ M k hgates hBraw0 hBcl0 hdrift hchi hnoncop hceil
  exact hmint R hReps hfloor Braw Bceil δ M k hgates hBraw0
    (m4_sievedDoorSqH_of_chiMeanSqH hgates hBcl0 hdrift hchi hnoncop) hceil

/-- ⭐ **THE COMMISSIONED LANE, AT `h = 2`** (`m4_doorL2_supply_500_two_of_chiMeanSq`) — the
`h = 2` instance, the shift the program actually uses.  Nothing is discharged here that is not
discharged at general `h`; the instance exists so the commissioned object has a name. -/
theorem m4_doorL2_supply_500_two_of_chiMeanSq :
    ∃ (Cg KXi : ℝ), 1 ≤ Cg ∧ 0 < KXi ∧ ∃ H₀ : ℕ,
      ∀ (R : ChowlaRegime), R.eps = 1 / 500 → H₀ ≤ R.Hlo →
        ∀ (Braw Bcl : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
          M4DoorGates Cg R M k δ →
          (∀ H : ℕ, 0 ≤ Braw H) →
          (∀ H : ℕ, 0 ≤ Bcl H) →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
            (1 + 2 * Real.pi) ^ 2 * ((2 * arcDen 12 H) ^ 2 * (3 * Bcl H)) ≤ Braw H) →
          M4ChiBlockMeanSqH 2 R M k Bcl →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q →
            (q : ℝ) ≤ 2 * arcDen 12 H → ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
              ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                  (classSup (doorSievedCoeff M) H n q r) ^ 2
                ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            MRTUniformityXiL2H 2 R (2 * KXi * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ)) := by
  obtain ⟨Cg, KXi, hCg, hKXi, H₀, hmint⟩ := m4_doorL2_supply_500_H_of_chiMeanSqH 2 (by norm_num)
  refine ⟨Cg, KXi, hCg, hKXi, H₀, ?_⟩
  intro R hReps hfloor Braw Bcl Bceil δ M k hgates hBraw0 hBcl0 hdrift hchi hnoncop hceil
  have hcast : (((2 : ℕ) : ℝ)) = (2 : ℝ) := by norm_num
  exact hmint R hReps hfloor Braw Bcl Bceil δ M k hgates hBraw0 hBcl0
    (by simpa only [hcast] using hdrift) hchi (by simpa only [hcast] using hnoncop) hceil

/-! ## §4 — the anti-vacuity duty for the two new sockets

Both `M4ChiBlockMeanSqH` and `M4ClassBlockMeanSqH` enter the close as HYPOTHESES, and the
kernel cannot check that a hypothesis is inhabited: uninhabited, they would make every
consumer of the `h`-mint vacuously usable with a green build and a clean audit.  Witnesses at
the trivial grade, mirroring `M4WaveClosed.m4_classBlockMeanSq_trivial`.

⚠️ At the trivial grade `M4GradeGate` of course fails — **that failure is the analytic gap, and
it is a different thing from vacuity.** -/

/-- **`M4ClassBlockMeanSqH` IS INHABITED** (`m4_classBlockMeanSqH_trivial`) — the `h`-clone of
`M4WaveClosed.m4_classBlockMeanSq_trivial`.  The cap is never read, which is itself the
evidence that all of this socket's content is the GRADE. -/
theorem m4_classBlockMeanSqH_trivial (h : ℕ) (R : ChowlaRegime) (M k : ℕ) :
    M4ClassBlockMeanSqH h R M k (fun _ => 1) := by
  intro H _ hhi q _ _ i _ r _
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hterm : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (classSup (doorSievedCoeff M) H n q r) ^ 2 ≤ (H : ℝ) ^ 2 := by
    intro n _
    have h := classSup_le_of_norm_le_one (norm_doorSievedCoeff_le_one M) H n q r
    have h0 := classSup_nonneg (doorSievedCoeff M) H n q r
    nlinarith
  have hsum : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (classSup (doorSievedCoeff M) H n q r) ^ 2
      ≤ ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
        * (H : ℝ) ^ 2 := by
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff M) H n q r) ^ 2
        ≤ ∑ _n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i), (H : ℝ) ^ 2 :=
          Finset.sum_le_sum hterm
      _ = ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
            * (H : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
      ≤ (doorLadder R.x H (i + 1) : ℝ) := by
    rw [Nat.card_Ioc]
    have hfit := doorLadder_fit R.x H i
    have hn : doorLadder R.x H i - doorLadder R.x H (i + 1) ≤ doorLadder R.x H (i + 1) := by
      omega
    exact_mod_cast hn
  have hpos := doorLadder_pos hxH (i + 1)
  nlinarith

/-- **`M4ChiBlockMeanSqH` IS INHABITED** (`m4_chiBlockMeanSqH_trivial`) — the same duty for the
χ datum, off `M4CoprimeSupply.doorChiSup_le_len`.  ⛔ This one matters most: `M4ChiBlockMeanSqH`
is what the close leaves OPEN, and an open socket that nobody can inhabit would make the whole
`h`-door chain vacuous. -/
theorem m4_chiBlockMeanSqH_trivial (h : ℕ) (R : ChowlaRegime) (M k : ℕ) :
    M4ChiBlockMeanSqH h R M k (fun _ => 1) := by
  intro H _ hhi q _ _ i _ χ
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hterm : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (doorChiSup χ M H n) ^ 2 ≤ (H : ℝ) ^ 2 := by
    intro n _
    have h := doorChiSup_le_len χ M H n
    have h0 := doorChiSup_nonneg χ M H n
    nlinarith
  have hsum : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (doorChiSup χ M H n) ^ 2
      ≤ ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
        * (H : ℝ) ^ 2 := by
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (doorChiSup χ M H n) ^ 2
        ≤ ∑ _n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i), (H : ℝ) ^ 2 :=
          Finset.sum_le_sum hterm
      _ = ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
            * (H : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
      ≤ (doorLadder R.x H (i + 1) : ℝ) := by
    rw [Nat.card_Ioc]
    have hfit := doorLadder_fit R.x H i
    have hn : doorLadder R.x H i - doorLadder R.x H (i + 1) ≤ doorLadder R.x H (i + 1) := by
      omega
    exact_mod_cast hn
  have hpos := doorLadder_pos hxH (i + 1)
  nlinarith

end Salt.MR
