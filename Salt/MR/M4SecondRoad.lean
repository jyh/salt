/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Gauss
import Salt.MR.M4BridgeBlock

/-!
# ⟦S-4⟧ — THE SECOND ROAD'S TERMINAL REGISTER (`M4SecondRoad`)

Wave ④ stage S-4 of the second-road freeze v2: the composition of ③'s blocked drift with
④'s χ-summed, stratified supply, and the register it exits at — `m4_second_road`.

## ⟦THE ℓ-WITNESS AND THE q = 1 PINCH — a co-design finding⟧

`M4BridgeBlock`'s socket demands FOUR obligations on the block length `ℓ H q`:

```
   1 ≤ ℓ,   ℓ ≤ H,   H ≤ arcDen 12 H · ℓ   (the count),   arcDen 12 H · ℓ ≤ q·H   (the drift).
```

Wave ③ found that a `q`-uniform `ℓ` cannot meet both of the last two and made `ℓ`
`q`-dependent.  **That repair is not enough**: at `q = 1` the two read
`H ≤ arcDen·ℓ ≤ H`, i.e. `arcDen 12 H · ℓ = H` EXACTLY, and no natural number does that for
generic `H` — the `q`-dependence buys nothing at the corner `q = 1`, which is in range
(`NearRatTight` may hand out `q = 1`).  **So `m4_sievedDoorSq_of_blk`'s four obligations are
jointly unsatisfiable and the landed socket has no consumer.**

⟦THE REPAIR, and why it is free⟧ the count binder is a NARROWING — it is handed TO the
supply, which only ever uses it as "the block length is not much shorter than `H/arcDen`".
Weakening it to

```
   H ≤ arcDen 12 H ^ 2 · ℓ
```

opens the admissible interval `ℓ ∈ [H/arcDen², H/arcDen]` — of ratio `arcDen ≥ e^{12}`, so it
contains an integer at EVERY `q ≥ 1` — and the whole supply chain of §S-2/S-3 is already
stated at the weakened narrowing (`M4ChiSummed`'s `arcDen³` block form absorbs the further
dilation loss).  §1 below re-cuts the socket at the weakened binder; everything else in
`M4BridgeBlock` is consumed verbatim.  The witness is then even `q`-UNIFORM:

```
   ℓ H q := max 1 (H / (⌊arcDen 12 H⌋₊ + 1)) .
```

## ⟦THE COMPOSED PRICE⟧

```
   ‖∫ ‖S_H(α)‖²‖  ≤  4(1+2π)² · 3 · (8 · (1 + log arcDen)² · B_cl) · H²
```

— `4(1+2π)²` the blocked drift (F3, absolute: no `arcDen`, no `q`), `3` the door cover, `8`
the two shift factors, `(1 + log arcDen)²` the divisor residual (the ONLY `q`-trace), and
`B_cl = m4BclGraded j₀ (2·RSan) (2·RStr)` the χ-summed supply's own grade.  The register's
drift conjunct (⟦item 4′⟧) is exactly the composed constant `96(1+2π)²·(1+log arcDen)²·B_cl`,
in place of the landed `(1+2π)²·arcDen²·3·B_blk`.  **No `arcDen` power and no `q` survives in
the price.**

## ⟦THE REGISTER RE-CUT — where it lives, and why not in place⟧

D-1(b) named `M4Join.m4_wave_exit_sup_split` as the target register and assigned wave ④ the
re-cut of its drift line.  The re-cut CANNOT be performed in place: `M4Join` sits below
`M4ClassPrice` in the import graph and the supply chain (`M4CoprimeSupply`, `M4ChiSummed`,
`M4Gauss`) sits six levels above it, so the composed conjunct cannot even be stated there;
and a re-cut to the *blocked* form alone would hard-wire the pinched binder above.  So the
re-cut register is `m4_second_road` HERE, with `m4_wave_exit_sup_split` left byte-unchanged
as the shape it was ratified to be.  The conclusion `¬ logChowla2Fails R.eps R.x R.ω` is
byte-identical to the landed one; `M4DoorGates` is consumed unchanged, `hMδ` included.

## Contents

* §1 THE ℓ-WITNESS — `blockLen` and its four obligations.
* §2 THE RE-CUT BLOCKED SOCKET — `M4SievedDoorSqBlk2`, `m4_sievedDoorSq_of_blk2`,
  `M4BlockMeanSqBlk2`, `m4_cover_assembly_blk2`.
* §3 THE SUPPLY — `m4_blockMeanSqBlk2_of_chiSummed`.
* §4 THE REGISTER — `m4_second_road`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE ℓ-WITNESS -/

/-- `4 ≤ arcDen 12 H` past the regime's window floor — the sibling of
`M4NonCoprime.one_le_arcDen_of_regime`, at the strength the `ℓ`-witness's floor arithmetic
needs (`e ≤ log H` gives `arcDen ≥ e^{12}`; `4` is all that is spent). -/
theorem four_le_arcDen_of_regime {R : ChowlaRegime} {H : ℕ} (hlo : R.Hlo ≤ H) :
    (4 : ℝ) ≤ arcDen 12 H := by
  have hLexp : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
  have he : (2 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hL2 : (2 : ℝ) ≤ Real.log (H : ℝ) := le_trans he.le hLexp
  have harcnp : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [harcnp]
  calc (4 : ℝ) ≤ 2 ^ (12 : ℕ) := by norm_num
    _ ≤ Real.log (H : ℝ) ^ (12 : ℕ) := by
        exact pow_le_pow_left₀ (by norm_num) hL2 12

/-- **THE BLOCK LENGTH** — `ℓ H q := max 1 (H / (⌊arcDen 12 H⌋₊ + 1))`.

`q`-UNIFORM (the signature keeps the socket's `ℕ → ℕ → ℕ` shape).  Wave ③'s `q`-dependence
was a response to the pinch that the weakened count binder removes; with the binder at
`arcDen²` the interval of admissible lengths is `[H/arcDen², H/arcDen]` and this witness sits
at its top end, where the drift binder holds at EVERY `q ≥ 1` with the whole factor `q` to
spare. -/
def blockLen (H : ℕ) (_q : ℕ) : ℕ := max 1 (H / (⌊arcDen 12 H⌋₊ + 1))

theorem one_le_blockLen (H q : ℕ) : 1 ≤ blockLen H q := le_max_left _ _

theorem blockLen_le (H q : ℕ) (hH : 1 ≤ H) : blockLen H q ≤ H := by
  unfold blockLen
  exact max_le hH (Nat.div_le_self H _)

/-- The floor ceiling `D = ⌊arcDen⌋₊ + 1` sits between `arcDen` and `2·arcDen`. -/
theorem arcDen_lt_floor_succ (H : ℕ) :
    arcDen 12 H < ((⌊arcDen 12 H⌋₊ + 1 : ℕ) : ℝ) := by
  push_cast
  exact Nat.lt_floor_add_one _

theorem floor_succ_le_two_mul {H : ℕ} (h1 : (1 : ℝ) ≤ arcDen 12 H) :
    ((⌊arcDen 12 H⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * arcDen 12 H := by
  push_cast
  have := Nat.floor_le (le_trans zero_le_one h1)
  linarith

/-- **THE DRIFT BINDER AT THE WITNESS** — `arcDen 12 H · ℓ ≤ q·H` for every `q ≥ 1`.  The
witness sits at the TOP of the admissible interval, so the drift binder holds already at
`q = 1` and the factor `q` is pure slack. -/
theorem blockLen_drift {R : ChowlaRegime} {H q : ℕ} (hlo : R.Hlo ≤ H) (hq : 0 < q)
    (hgate : 128 * arcDen 12 H ^ 2 ≤ (H : ℝ)) :
    arcDen 12 H * ((blockLen H q : ℕ) : ℝ) ≤ (q : ℝ) * (H : ℝ) := by
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  have hD := arcDen_lt_floor_succ H
  have hkey : arcDen 12 H * ((blockLen H q : ℕ) : ℝ) ≤ (H : ℝ) := by
    unfold blockLen
    rcases Nat.eq_zero_or_pos (H / (⌊arcDen 12 H⌋₊ + 1)) with hz | hpos
    · rw [hz, max_eq_left (Nat.zero_le 1)]
      push_cast
      nlinarith
    · rw [max_eq_right hpos]
      have hcast := Nat.cast_div_le (α := ℝ) (m := H) (n := ⌊arcDen 12 H⌋₊ + 1)
      have hD0 : (0 : ℝ) < ((⌊arcDen 12 H⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      have hstep : arcDen 12 H * ((H / (⌊arcDen 12 H⌋₊ + 1) : ℕ) : ℝ)
          ≤ arcDen 12 H * ((H : ℝ) / ((⌊arcDen 12 H⌋₊ + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcast harc0.le
      have hfrac : arcDen 12 H * ((H : ℝ) / ((⌊arcDen 12 H⌋₊ + 1 : ℕ) : ℝ)) ≤ (H : ℝ) := by
        rw [mul_div_assoc'] at *
        rw [div_le_iff₀ hD0]
        nlinarith
      linarith
  nlinarith

/-- **THE COUNT BINDER AT THE WITNESS, WEAKENED** — `H ≤ arcDen 12 H ² · ℓ`.  This is the
repaired binder of the module header; the landed `H ≤ arcDen·ℓ` is what pinches at `q = 1`.
-/
theorem blockLen_narrow {R : ChowlaRegime} {H q : ℕ} (hlo : R.Hlo ≤ H)
    (hgate : 128 * arcDen 12 H ^ 2 ≤ (H : ℝ)) :
    (H : ℝ) ≤ arcDen 12 H ^ 2 * ((blockLen H q : ℕ) : ℝ) := by
  have harc4 : (4 : ℝ) ≤ arcDen 12 H := four_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hD2 := floor_succ_le_two_mul (H := H) (by linarith)
  have hD0 : (0 : ℝ) < ((⌊arcDen 12 H⌋₊ + 1 : ℕ) : ℝ) := by
    have := arcDen_lt_floor_succ H; linarith
  -- ⟦the ℕ-division floor, honestly⟧ `H ≤ D·(H/D) + D ≤ D·ℓ + D`
  have hmod : H ≤ (⌊arcDen 12 H⌋₊ + 1) * (H / (⌊arcDen 12 H⌋₊ + 1))
      + (⌊arcDen 12 H⌋₊ + 1) := by
    have h1 := Nat.div_add_mod H (⌊arcDen 12 H⌋₊ + 1)
    have h2 : H % (⌊arcDen 12 H⌋₊ + 1) < ⌊arcDen 12 H⌋₊ + 1 :=
      Nat.mod_lt _ (Nat.succ_pos _)
    omega
  have hle : H / (⌊arcDen 12 H⌋₊ + 1) ≤ blockLen H q := le_max_right _ _
  have hmulR : (H : ℝ) ≤ ((⌊arcDen 12 H⌋₊ + 1 : ℕ) : ℝ) * ((blockLen H q : ℕ) : ℝ)
      + ((⌊arcDen 12 H⌋₊ + 1 : ℕ) : ℝ) := by
    have hstep : H ≤ (⌊arcDen 12 H⌋₊ + 1) * (blockLen H q) + (⌊arcDen 12 H⌋₊ + 1) := by
      have := Nat.mul_le_mul_left (⌊arcDen 12 H⌋₊ + 1) hle
      omega
    exact_mod_cast hstep
  have hL0 : (0 : ℝ) ≤ ((blockLen H q : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦`H ≤ 2·arcDen·(ℓ + 1)`, then the two arc floors⟧
  have hchain : (H : ℝ) ≤ 2 * arcDen 12 H * ((blockLen H q : ℕ) : ℝ) + 2 * arcDen 12 H := by
    nlinarith
  nlinarith

/-- **THE ARC FLOOR AT THE WITNESS** — `32·arcDen 12 H ≤ ℓ`.  What the stratified consumer
reads to keep every stratum's re-indexed block non-degenerate. -/
theorem blockLen_arc_floor {R : ChowlaRegime} {H q : ℕ} (hlo : R.Hlo ≤ H)
    (hgate : 128 * arcDen 12 H ^ 2 ≤ (H : ℝ)) :
    32 * arcDen 12 H ≤ ((blockLen H q : ℕ) : ℝ) := by
  have harc4 : (4 : ℝ) ≤ arcDen 12 H := four_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hD2 := floor_succ_le_two_mul (H := H) (by linarith)
  have hD0 : (0 : ℝ) < ((⌊arcDen 12 H⌋₊ + 1 : ℕ) : ℝ) := by
    have := arcDen_lt_floor_succ H; linarith
  have hmod : H ≤ (⌊arcDen 12 H⌋₊ + 1) * (H / (⌊arcDen 12 H⌋₊ + 1))
      + (⌊arcDen 12 H⌋₊ + 1) := by
    have h1 := Nat.div_add_mod H (⌊arcDen 12 H⌋₊ + 1)
    have h2 : H % (⌊arcDen 12 H⌋₊ + 1) < ⌊arcDen 12 H⌋₊ + 1 :=
      Nat.mod_lt _ (Nat.succ_pos _)
    omega
  have hle : H / (⌊arcDen 12 H⌋₊ + 1) ≤ blockLen H q := le_max_right _ _
  have hmulR : (H : ℝ) ≤ ((⌊arcDen 12 H⌋₊ + 1 : ℕ) : ℝ) * ((blockLen H q : ℕ) : ℝ)
      + ((⌊arcDen 12 H⌋₊ + 1 : ℕ) : ℝ) := by
    have hstep : H ≤ (⌊arcDen 12 H⌋₊ + 1) * (blockLen H q) + (⌊arcDen 12 H⌋₊ + 1) := by
      have := Nat.mul_le_mul_left (⌊arcDen 12 H⌋₊ + 1) hle
      omega
    exact_mod_cast hstep
  have hL0 : (0 : ℝ) ≤ ((blockLen H q : ℕ) : ℝ) := Nat.cast_nonneg _
  have hchain : (H : ℝ) ≤ 2 * arcDen 12 H * ((blockLen H q : ℕ) : ℝ) + 2 * arcDen 12 H := by
    nlinarith
  nlinarith

/-! ## §2 — THE RE-CUT BLOCKED SOCKET

`M4BridgeBlock` §3/§4 at the weakened count binder.  Nothing else moves: the blocked drift,
the block geometry and the door cover are consumed verbatim. -/

/-- `M4BridgeBlock.M4SievedDoorSqBlk` with the count binder weakened to `H ≤ arcDen²·ℓ`
(⟦the q = 1 repair⟧).  Weakening a HYPOTHESIS of the supply makes this predicate STRONGER
than the landed one, and the whole χ-summed chain supplies it. -/
def M4SievedDoorSqBlk2 (R : ChowlaRegime) (M : ℕ) (ℓ : ℕ → ℕ → ℕ) (Bblk : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
      (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q → ℓ H q ≤ H →
      (H : ℝ) ≤ arcDen 12 H ^ 2 * (ℓ H q : ℝ) →
        (∫ n, blockSupSq (doorSievedCoeff M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
            ∂(logMeasure R.x R.ω))
          ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2

/-- **THE BLOCKED SOCKET, RE-CUT** (`m4_sievedDoorSq_of_blk2`) — `M4BridgeBlock`'s socket
theorem with `hℓcnt` weakened to `H ≤ arcDen²·ℓ`.  The proof is the landed one verbatim: the
count binder is only ever handed to the supply, never used by the socket. -/
theorem m4_sievedDoorSq_of_blk2 {R : ChowlaRegime} {M : ℕ} {ℓ : ℕ → ℕ → ℕ} {Bblk Braw : ℕ → ℝ}
    (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hℓ1 : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q)
    (hℓH : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → ℓ H q ≤ H)
    (hℓcnt : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (H : ℝ) ≤ arcDen 12 H ^ 2 * (ℓ H q : ℝ))
    (hℓdrift : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      arcDen 12 H * (ℓ H q : ℝ) ≤ (q : ℝ) * (H : ℝ))
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * (1 + 2 * Real.pi) ^ 2 * Bblk H ≤ Braw H)
    (hblk : M4SievedDoorSqBlk2 R M ℓ Bblk) : M4SievedDoorSq R M Braw := by
  intro htr H _ hlo hhi α hα
  have hH : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  obtain ⟨b, q, hq, hqQ, hd⟩ := hα
  have hℓ1' := hℓ1 H q hlo hhi hq hqQ
  have hℓH' := hℓH H q hlo hhi hq hqQ
  have hℓcnt' := hℓcnt H q hlo hhi hq hqQ
  have hℓdrift' := hℓdrift H q hlo hhi hq hqQ
  have hℓ0 : 0 < ℓ H q := hℓ1'
  set c := doorSievedCoeff M with hc
  set β : ℝ := (b : ℝ) / (q : ℝ) with hβ
  set L := ℓ H q with hL
  set N := numBlocks H L with hN
  have hpt : ∀ n : ℕ, ‖absWindowSum c H n α‖ ^ 2
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β := by
    intro n
    have h := norm_absWindowSum_sq_le_drift_blocked (B₅ := 12) (H := H) (q := q) (n := n)
      (ℓ := L) hq hH hℓ0 (β := β) (θ := α - β) hd hℓdrift' c
    have he : β + (α - β) = α := by ring
    rw [he] at h
    exact h
  have hmono : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ ∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_mono hpt
  have hconst : (∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β
        ∂(logMeasure R.x R.ω))
      = (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * ∫ n, blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_const_mul _ _
  have hsupply := hblk htr H hlo hhi b q hq hqQ hℓ1' hℓH' hℓcnt'
  have hfac0 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) := by positivity
  have hstep : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := by
    rw [hconst] at hmono
    exact le_trans hmono (mul_le_mul_of_nonneg_left hsupply hfac0)
  have hNL : N * L ≤ 2 * H := by
    have h1 : N * L ≤ H + L := by rw [hN]; exact numBlocks_mul_le H L
    omega
  have hNLR : (N : ℝ) * (L : ℝ) ≤ 2 * (H : ℝ) := by
    have : ((N * L : ℕ) : ℝ) ≤ ((2 * H : ℕ) : ℝ) := by exact_mod_cast hNL
    push_cast at this
    linarith
  have hNL0 : (0 : ℝ) ≤ (N : ℝ) * (L : ℝ) := by positivity
  have hsq : ((N : ℝ) * (L : ℝ)) ^ 2 ≤ 4 * (H : ℝ) ^ 2 := by nlinarith
  have hB := hB0 H
  have hpi2 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 := sq_nonneg _
  have hfin : (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
      ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by
    calc (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
        = (1 + 2 * Real.pi) ^ 2 * Bblk H * (((N : ℝ) * (L : ℝ)) ^ 2) := by ring
      _ ≤ (1 + 2 * Real.pi) ^ 2 * Bblk H * (4 * (H : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hpi2 hB)
      _ = 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by ring
  have hgr := hgrade H hlo hhi
  calc (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := hstep
    _ ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := hfin
    _ ≤ Braw H * (H : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hgr (sq_nonneg _)

/-- `M4BridgeBlock.M4BlockMeanSqBlk` at the weakened count binder. -/
def M4BlockMeanSqBlk2 (R : ChowlaRegime) (M k : ℕ) (ℓ : ℕ → ℕ → ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
    1 ≤ ℓ H q → ℓ H q ≤ H → (H : ℝ) ≤ arcDen 12 H ^ 2 * (ℓ H q : ℝ) →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          blockSupSq (doorSievedCoeff M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
        ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2
            * (doorLadder R.x H (i + 1) : ℝ)

/-- `M4BridgeBlock.m4_cover_assembly_blk` at the weakened count binder — the same
`integral_door_cover_le_clean`, the same door-gate bundle, the same absolute factor `3`. -/
theorem m4_cover_assembly_blk2 {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {ℓ : ℕ → ℕ → ℕ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqBlk2 R M k ℓ Bblk) :
    M4SievedDoorSqBlk2 R M ℓ (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ h1 h2 h3
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2 := by
    have := hB0 H; positivity
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => blockSupSq (doorSievedCoeff M) H (ℓ H q) n ((b : ℝ) / (q : ℝ)))
    (P := Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount
    (fun n => blockSupSq_nonneg _ _ _ _ _) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ h1 h2 h3)
  refine le_trans hmain (le_of_eq ?_)
  ring

/-! ## §3 — THE SUPPLY

`M4Gauss`'s stratified free-block bound, read at the drift blocks of every door-ladder
block.  The shifted bases stay inside the ladder block's own doubled interval
(`M4BridgeBlock` §5), which is the whole content of the transfer. -/

set_option maxHeartbeats 1200000 in
-- the block sum is re-associated over the drift blocks and then over the ladder block, and
-- the stratified bound is instantiated once per drift block; every arithmetic step is
-- `linarith`/`nlinarith` with hints
/-- **⟦S-4a⟧ THE BLOCKED BLOCK MEAN SQUARE, FROM THE χ-SUMMED SUPPLY**
(`m4_blockMeanSqBlk2_of_chiSummed`).

Per drift block `m < N` the base is `n + m·ℓ` with `n` in the ladder block
`(X_{i+1}, X_i]`, i.e. a FREE block `(X_{i+1} + m·ℓ, X_i + m·ℓ]` whose fit is the ladder's
own (`X_i + H ≤ 2X_{i+1}` and `ℓ ≤ H`) and whose bottom is at most `2X_{i+1}`
(`M4BridgeBlock.blockBase_le_two_mul`'s arithmetic).  `M4Gauss`'s stratified bound fires
there, and the drift blocks contribute the factor `N`. -/
theorem m4_blockMeanSqBlk2_of_chiSummed {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hM : 1 ≤ M) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 2 ≤ (H : ℝ))
    (hchi : M4ChiSummedBlockMeanSqN R M Bcl) :
    M4BlockMeanSqBlk2 R M k blockLen
      (fun H => 8 * strataResidual H ^ 2 * Bcl H) := by
  intro H hlo hhi b q hq hqQ hℓ1 hℓH hℓcnt i hik
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harcH := harc H hlo hhi
  have hres0 : (0 : ℝ) ≤ strataResidual H := strataResidual_nonneg harc1
  have hB0 := hBcl0 H
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
  have hfit : doorLadder R.x H i + H ≤ 2 * doorLadder R.x H (i + 1) := doorLadder_fit R.x H i
  have hApos : 0 < doorLadder R.x H (i + 1) := by omega
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  set L := blockLen H q with hLdef
  set N := numBlocks H L with hN
  have hLarc : 32 * arcDen 12 H ≤ (L : ℝ) := blockLen_arc_floor (R := R) hlo harcH
  have hAarc : 32 * arcDen 12 H ≤ (A : ℝ) := by
    have : (H : ℝ) ≤ (A : ℝ) := by exact_mod_cast (by omega : H ≤ A)
    nlinarith
  -- ⟦the drift blocks, one free block each⟧
  have hstrat := m4_freeBlockSup_of_chiSummed (R := R) (M := M) (Bcl := Bcl) hM hBcl0 hgate
    hchi H hlo hhi L hℓH hℓcnt hLarc b q hq hqQ
  have hper : ∀ m ∈ Finset.range N,
      ∑ n ∈ Finset.Ioc A B, (subWindowSup (doorSievedCoeff M) L (n + m * L)
          ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ 8 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by
    intro m hm
    have hmL : m * L ≤ H := mul_le_of_lt_numBlocks (Finset.mem_range.mp hm)
    have hshift : ∑ n ∈ Finset.Ioc A B,
        (subWindowSup (doorSievedCoeff M) L (n + m * L) ((b : ℝ) / (q : ℝ))) ^ 2
        = ∑ n ∈ Finset.Ioc (A + m * L) (B + m * L),
            (subWindowSup (doorSievedCoeff M) L n ((b : ℝ) / (q : ℝ))) ^ 2 :=
      sum_Ioc_shift (fun n => (subWindowSup (doorSievedCoeff M) L n ((b : ℝ) / (q : ℝ))) ^ 2)
        A B _
    rw [hshift]
    have hApos' : 0 < A + m * L := by omega
    have hAarc' : 32 * arcDen 12 H ≤ ((A + m * L : ℕ) : ℝ) := by
      have : (A : ℝ) ≤ ((A + m * L : ℕ) : ℝ) := by
        exact_mod_cast (by omega : A ≤ A + m * L)
      linarith
    have hfit' : (B + m * L) + L ≤ 2 * (A + m * L) := by omega
    have h := hstrat (A + m * L) (B + m * L) hApos' hAarc' hfit'
    have hbase : ((A + m * L : ℕ) : ℝ) ≤ 2 * (A : ℝ) := by
      have hnat : A + m * L ≤ 2 * A := by omega
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this ⊢
      linarith
    have hfac0 : (0 : ℝ) ≤ 4 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hbase hfac0]
  -- ⟦the drift-block sum⟧
  have hswap : ∑ n ∈ Finset.Ioc A B, blockSupSq (doorSievedCoeff M) H L n ((b : ℝ) / (q : ℝ))
      = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.Ioc A B,
          (subWindowSup (doorSievedCoeff M) L (n + m * L) ((b : ℝ) / (q : ℝ))) ^ 2 := by
    unfold blockSupSq
    exact Finset.sum_comm
  rw [hswap]
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine le_of_eq ?_
  ring

/-! ## §4 — THE REGISTER -/

/-- **⟦THE SECOND ROAD'S TERMINAL REGISTER⟧ — `m4_second_road`.**

The re-cut of `M4Join.m4_wave_exit_sup_split` (D-1(b)) at the composed
blocked-drift × stratified-Gauss × χ-summed supply.  The conclusion
`¬ logChowla2Fails R.eps R.x R.ω` is BYTE-IDENTICAL to the landed one.

⟦THE GATE CENSUS⟧ — finite, and every gate is one of: **witnessed** (discharged inside),
**regime-absorbable** (one-sided, `H`-only, on the window range `[Hlo, Hhi]`, hence
absorbable by the `g`-arm/`U1floor` of the outer register), or **consumer data**:

1. `M4DoorGates Cg R M k δ` — UNCHANGED, `hMδ` included (⟦UNTOUCHABLE⟧).
2. `1 ≤ M` — consumer data.
3. `∀ H, 0 ≤ RSan H`, `∀ H, 0 ≤ RStr H`, `∀ H, 0 ≤ Braw H` — envelope nonnegativity.
4. `∀ j H, j₀ ≤ j → RS j H ≤ RSan H` — the analytic envelope (consumer data).
5. `arcDen 12 H ^ 7 ≤ RStr H` on the window range — ⟦G1⟧, the trivial envelope's threshold
   (regime-absorbable: `RStr` is witnessed data and this is a floor on it).
6. `44·RSan H + 87·arcDen 12 H ≤ (4/3)^{j₀}` — ⟦G2⟧, the slack residue against the floor's
   own constant (a formality at `j₀ = M·Adoor M ≥ 2^18`).
7. `128·arcDen 12 H ³ ≤ H` — the window floor: ONE-SIDED, `H`-only (`(log H)^{36} ≪ H`).
8. `arcDen 12 H < calP (Adoor M) (3072M) 1` — the `M`-RELATIVE dilation gate.  **NOT** the
   retired numeral `log H ≤ 2^{21845}`: no `H`-upper appears anywhere in this register.
9. the composed drift price (⟦item 4′, RE-CUT⟧):
   `96(1+2π)²·(1 + log arcDen 12 H)²·m4BclGraded j₀ (2·RSan) (2·RStr) H ≤ Braw H`.
   **No `arcDen` power, no `q`, no `q²`** — this is the line the whole road exists to cut.
10. `M4GradeGateSplit R δ₀ δ Braw k` — the budget line at the head's own constant `δ₀`.
11. `M4ChiSummedFreeRow R M RS` — THE ANALYTIC SLOT, the socket of S-1.

⟦F5 CHECK⟧ every `H`-conjunct above is a LOWER bound on `H` or an upper bound on a
*witnessed envelope*; there is no `X`-upper anywhere, so no `X`-upper rides with an
`X`-lower in any bundle. -/
theorem m4_second_road :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
            M4DoorGates Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            M4GradeGateSplit R δ₀ δ Braw k →
            M4ChiSummedFreeRow R M RS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_split
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3 hdgate
    hdrift hgrade hrow
  -- ⟦the window floor, read at the two powers the chain spends⟧
  have harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    nlinarith [h1, harc1]
  have harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 2 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    nlinarith [h1, harc1]
  have hchi : M4ChiSummedBlockMeanSqN R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  -- ⟦the blocked block mean square⟧
  have hblk2 := m4_blockMeanSqBlk2_of_chiSummed (k := k) hM hBcl0 hdgate harc hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  -- ⟦the cover, then the socket⟧
  have hcov := m4_cover_assembly_blk2 hgates hBblk0 hblk2
  refine hR δ Braw M k hgates hBraw0 hgrade ?_
  refine m4_sievedDoorSq_of_blk2 (ℓ := blockLen)
    (fun H => by have := hBblk0 H; positivity)
    (fun H q _ _ _ _ => one_le_blockLen H q) ?_ ?_ ?_ ?_ hcov
  · intro H q hlo hhi _ _
    have h1 := harc H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hH1 : 1 ≤ H := by
      have : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
      exact_mod_cast this
    exact blockLen_le H q hH1
  · intro H q hlo hhi _ _
    exact blockLen_narrow (R := R) hlo (harc H hlo hhi)
  · intro H q hlo hhi hq _
    exact blockLen_drift (R := R) hlo hq (harc H hlo hhi)
  · intro H hlo hhi
    have h := hdrift H hlo hhi
    have hres0 : (0 : ℝ) ≤ strataResidual H :=
      strataResidual_nonneg (one_le_arcDen_of_regime (R := R) hlo)
    have hB := hBcl0 H
    nlinarith [h]

end Salt.MR

end
