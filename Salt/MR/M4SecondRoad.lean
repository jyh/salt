/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Gauss
import Salt.MR.M4BridgeBlock
import Salt.MR.M4Collapse

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

## ⟦WAVE ⑤ — THE `D₀`-TRUNCATION TEST: REFUTED (2026-07-29)⟧

Wave ⑤'s first item was ⟦REF-SAND's A-6 gift⟧ / ⟦D0-TEST's SITE A⟧: take the strata
`d > D₀` by the landed GATE-FREE trivial bound and collapse ⟦gate 8⟧'s demand from
`arcDen 12 H` to an ABSOLUTE `D₀ = 2/√Bblk`, dissolving the door-anchor sandwich with no
`DoorFrame` re-pin.  **It does not close, and the reason is structural, not arithmetic.**

⟦THE EXACT ACCOUNTING⟧ at one stratum `d ∣ q`, over the block `(A, B]` with `B − A ≤ A`:

```
   analytic (§3 above → M4Gauss §5):  ∑ₙ strataTerm_d  ≤  Bcl·(L+d)²·A/d²   (≈ Bcl·L²A/d²)
   trivial  (gate-free, the count):   ∑ₙ (L/d + 1)²    ≈        L²A/d²
```

The **`1/d²` scaling is IDENTICAL on both sides** — the χ-summed supply is read at the
stratum's OWN dilated cap `capL L d ≈ L/d` and its own re-indexed block `⌊A/d⌋`, so its
budget decays with `d` exactly as fast as the trivial count does.  The trivial branch is
therefore worse by the factor `1/Bcl` at EVERY `d`; there is no `d` at which it becomes
competitive, and the per-stratum ("SITE A") admissibility `(L/d + 1)² ≤ Bblk·L²` — which IS
absolute, and IS proved below (`truncD_admissible`) — compares the trivial stratum against
the WHOLE block budget, not against the `1/d²`-decayed slot the recombination actually
leaves it.

⟦WHERE THE `1/d²` WENT⟧ it is the first road's `d₀`-ledger (`M4NonCoprime.d0_ledger_sharp`),
and §5 of `M4Gauss` SPENDS it: the weighted Cauchy–Schwarz at `1/d` is what converts the
strata recombination's cost from `τ(q)²` (a positive power of `log H` — fatal by the
residual law) into the `loglog`-scale residual `(∑_{d∣q} 1/d)² ≤ (1 + log arcDen)²`.  **The
weighted recombination and the `D₀`-truncation are mutually exclusive: each needs the same
ledger.**  Wave ④'s per-stratum granularity was preserved exactly as ⟦D0-TEST⟧ steered, and
it is not the binding constraint — the recombination is.

⟦WHAT `D₀` IS STILL WORTH⟧ the only surviving leverage is the DIVISOR TAIL
`∑_{d∣q, d>D₀} 1/d`, which must fall below `Bblk/(1.07·(1+log arcDen))` — ⟦D0-TEST's SITE
B⟧.  Honest `τ`-free bound: `∑_{d∣q,d>D₀} 1/d ≤ q/(2D₀²)` (complementary divisors
`e = q/d < q/D₀`, then `∑_{e<Y} e ≤ Y²/2`), giving

```
   D₀ ≥ √(1.07·(1 + log arcDen)·arcDen / (2·Bblk))   ⟹   log₂ D₀ ≈ 6·log₂ log H + 169 ,
```

i.e. **exactly half the exponent of ⟦gate 8⟧'s own `log₂ arcDen = 12·log₂ log H` — worth
ONE anchor bit** (⟦SANDWICH-REF⟧: each `+1` bit multiplies the margin ×1.96).  Wigert's
`τ(q) ≤ exp((log 2 + o(1))·log q/loglog q)` would buy `≈ log₂ q/loglog q` instead — about
5–6 anchor bits at the closing scale, still not the 16 bits `2^18 → 2^34` that ⟦REF-SAND⟧
prices.  **And in every case `D₀` carries `arcDen`, so ⟦gate 8⟧ does not become `H`-free.**
⟦D0-TEST⟧'s banked "DISSOLVED by 3.9·10⁴×, log₂ D₀ ∝ ln lnln Hhi" does not reproduce: its
SITE-A margin priced an admissibility the stratified recombination never demands, and its
SITE-B growth law is a `loglog` where the divisor tail forces a `log`.

**⟦THE CONSEQUENCE⟧ ⟦gate 8⟧ stands at `arcDen 12 H < calP (Adoor M) (3072M) 1`, and the
door-anchor ask (⟦REF-SAND⟧'s 2^34 minimum / 2^36 for ≥2× headroom) goes back to JYH.  No
statement of §1–§4 moves.**

## Contents

* §1 THE ℓ-WITNESS — `blockLen` and its four obligations.
* §2 THE RE-CUT BLOCKED SOCKET — `M4SievedDoorSqBlk2`, `m4_sievedDoorSq_of_blk2`,
  `M4BlockMeanSqBlk2`, `m4_cover_assembly_blk2`.
* §3 THE SUPPLY — `m4_blockMeanSqBlk2_of_chiSummed`.
* §4 THE REGISTER — `m4_second_road`.
* §5 THE `D₀` CONSTANT — `truncBudget`, `truncD`, `truncD_admissible`, and the zero-byte
  instantiation of the door gate at `D₀`.
* §6 THE PRICING AUDIT — the register's own gates witnessed (`rSanWitness`, `rStrWitness`,
  `g2_of_j0_floor`) and the composed `RS`-grade demand the port must deliver
  (`m4_second_road_rs_ceiling`).
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

/-- **⟦R-P5⟧ `2^k ≤ 4·ω` FROM THE COVER'S OWN BLOCK COUNT** (`two_pow_le_four_mul_of_count`).
`M4Close.M4DoorGates.hcount` reads `k ≤ log ω/log 2 + 2`; exponentiating it is the ℕ fact the
door ladder's geometric floor needs.  Below `k = 2` the claim is `2^k ≤ 4 ≤ 4ω` outright. -/
theorem two_pow_le_four_mul_of_count {k ω : ℕ} (hω : 2 ≤ ω)
    (hcount : (k : ℝ) ≤ Real.log (ω : ℝ) / Real.log 2 + 2) : 2 ^ k ≤ 4 * ω := by
  by_cases hk : k ≤ 2
  · have h1 : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk
    omega
  · have hω0 : (0 : ℝ) < (ω : ℝ) := by
      have h : (0 : ℕ) < ω := by omega
      exact_mod_cast h
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hk2 : 2 ≤ k := by omega
    have hcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
      rw [Nat.cast_sub hk2]; norm_num
    have h1 : ((k - 2 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (ω : ℝ) := by
      rw [hcast]
      have hstep : (k : ℝ) - 2 ≤ Real.log (ω : ℝ) / Real.log 2 := by linarith
      calc ((k : ℝ) - 2) * Real.log 2
          ≤ Real.log (ω : ℝ) / Real.log 2 * Real.log 2 :=
            mul_le_mul_of_nonneg_right hstep hlog2.le
        _ = Real.log (ω : ℝ) := by field_simp
    have h2 : Real.log ((2 : ℝ) ^ (k - 2)) ≤ Real.log (ω : ℝ) := by
      rw [Real.log_pow]; exact h1
    have hp : (0 : ℝ) < (2 : ℝ) ^ (k - 2) := by positivity
    have h3 : (2 : ℝ) ^ (k - 2) ≤ (ω : ℝ) := by
      have h4 := Real.exp_le_exp.mpr h2
      rwa [Real.exp_log hp, Real.exp_log hω0] at h4
    have h4 : 2 ^ (k - 2) ≤ ω := by exact_mod_cast h3
    have h5 : 4 * 2 ^ (k - 2) = 2 ^ k := by
      have hkk : (k - 2) + 2 = k := by omega
      calc 4 * 2 ^ (k - 2) = 2 ^ (k - 2) * 2 ^ 2 := by ring
        _ = 2 ^ ((k - 2) + 2) := (pow_add 2 (k - 2) 2).symm
        _ = 2 ^ k := by rw [hkk]
    omega

/-- **⟦R-P5⟧ THE LADDER'S x-SCALE FLOOR** (`doorLadder_ge_x_div_four_omega`) — the supply side
of the socket's x-scale antecedent.  Every rung in the cover's range is at least `⌊x/(4ω)⌋`:
`M4Collapse.doorLadder_pow_lower` gives `⌊x/2^i⌋ ≤ X_i` (the descent halves at worst), and
`two_pow_le_four_mul_of_count` turns the cover's block count into `2^i ≤ 2^k ≤ 4ω`.

This is the composition ⟦R-P5⟧ named: the socket's bases ARE x-scale, and this is why. -/
theorem doorLadder_ge_x_div_four_omega {x ω H k i : ℕ} (hω : 2 ≤ ω)
    (hcount : (k : ℝ) ≤ Real.log (ω : ℝ) / Real.log 2 + 2) (hik : i ≤ k) :
    x / (4 * ω) ≤ doorLadder x H i := by
  have hpow : 2 ^ i ≤ 4 * ω :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hik) (two_pow_le_four_mul_of_count hω hcount)
  have h1 : x / (4 * ω) ≤ x / 2 ^ i := Nat.div_le_div_left hpow (Nat.two_pow_pos i)
  exact le_trans h1 (doorLadder_pow_lower x H i)

/-- **⟦(α)⟧ THE LADDER'S CEILING** (`doorLadder_le_start`) — the supply side of the socket's
BASE CAP (**the (α) base-cap surgery, JYH-granted 2026-07-30**).

`X_i ≤ x` at every rung, once the ladder sits above its own floor (`H + 1 ≤ x`, which is
`M4Close.regime_window_headroom`): the descent `X_{i+1} = ⌊(X_i + H + 1)/2⌋` averages two
quantities that are each at most `x`, and `⌊·/2⌋` is monotone.  `doorLadder_upper`'s
`X_i ≤ (H+1) + x/2^i` is NOT enough here — it gives only `1.5·x` at `i = 1` — so the cap is
proved by the descent's own induction instead.

Composed with `m·ℓ ≤ H ≤ x − 1` this is exactly `X_{i+1} + m·ℓ ≤ 2·x`, the socket's cap at
the ONE place its base becomes concrete. -/
theorem doorLadder_le_start {x H : ℕ} (hx : H + 1 ≤ x) (i : ℕ) : doorLadder x H i ≤ x := by
  induction i with
  | zero => simp
  | succ n ih => rw [doorLadder_succ]; omega

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
    (hcount : (k : ℝ) ≤ Real.log (R.ω : ℝ) / Real.log 2 + 2)
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
  have hL16 : 16 * arcDen 12 H ^ 2 ≤ (H : ℝ) := by
    nlinarith [harcH, sq_nonneg (arcDen 12 H)]
  -- ⟦R-P5, THE x-SCALE LADDER AT THIS RUNG⟧ the base antecedents `M4Gauss` now asks for,
  -- discharged from the ladder's geometric floor (`doorLadder_ge_x_div_four_omega`), its
  -- CEILING (`doorLadder_le_start`, the (α) base cap) and the regime's own wave-II headroom
  -- `8·H₊·log²H₊ ≤ ⌊x/ω⌋` (whose two log factors are `≥ 1` at `H₊ ≥ 4·10⁶`)
  -- — NO new regime field, NO `g`-arm movement
  have hω0N : 0 < 4 * R.ω := by have := R.hω; omega
  have hω0 : (0 : ℝ) < (R.ω : ℝ) := by
    have h : 0 < R.ω := by have := R.hω; omega
    exact_mod_cast h
  have hxdiv : R.x / (4 * R.ω) ≤ A := by
    rw [hA]
    exact doorLadder_ge_x_div_four_omega (H := H) R.hω hcount (by omega)
  -- ⟦(α) THE BASE CAP AT THIS RUNG⟧ the ceiling side of the socket's fourth base antecedent
  -- (the (α) base-cap surgery, JYH-granted 2026-07-30): the ladder never exceeds its own
  -- top, so `X_{i+1} ≤ x` and every drift-shifted base is `≤ x + H ≤ 2x`
  have hAtop : A ≤ R.x := by
    rw [hA]
    exact doorLadder_le_start hxH (i + 1)
  have hHhi4 : (4000000 : ℝ) ≤ (R.Hhi : ℝ) := by
    have h : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
    exact_mod_cast h
  have hlogHhi : (1 : ℝ) ≤ Real.log (R.Hhi : ℝ) := by
    have hexp : Real.exp 1 ≤ (R.Hhi : ℝ) := by nlinarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by linarith)).mpr hexp
  have hxω : 8 * (R.ω : ℝ) * (R.Hhi : ℝ) ≤ (R.x : ℝ) := by
    have hh := R.hheadroom'
    have hcast : (((R.x / R.ω : ℕ)) : ℝ) ≤ (R.x : ℝ) / (R.ω : ℝ) := Nat.cast_div_le
    have hlogsq : (1 : ℝ) ≤ Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) := by
      nlinarith [hlogHhi]
    have h1 : 8 * (R.Hhi : ℝ) ≤ (R.x : ℝ) / (R.ω : ℝ) := by
      calc 8 * (R.Hhi : ℝ) = 8 * (R.Hhi : ℝ) * 1 := by ring
        _ ≤ 8 * (R.Hhi : ℝ) * (Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogsq (by linarith)
        _ = 8 * (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) := by ring
        _ ≤ (((R.x / R.ω : ℕ)) : ℝ) := hh
        _ ≤ (R.x : ℝ) / (R.ω : ℝ) := hcast
    rw [le_div_iff₀ hω0] at h1
    linarith
  have hHhiR : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast hhi
  have h8ωH : 8 * R.ω * H ≤ R.x := by
    have h : (8 : ℝ) * (R.ω : ℝ) * (H : ℝ) ≤ (R.x : ℝ) := by nlinarith [hxω, hHhiR, hω0]
    exact_mod_cast h
  have h2HA : 2 * (H : ℝ) ≤ (A : ℝ) := by
    have hn : 2 * H ≤ A := by
      refine le_trans ((Nat.le_div_iff_mul_le hω0N).mpr ?_) hxdiv
      calc 2 * H * (4 * R.ω) = 8 * R.ω * H := by ring
        _ ≤ R.x := h8ωH
    exact_mod_cast hn
  have hxA : (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * (A : ℝ) := by
    have hdivub : R.x ≤ 4 * R.ω * (R.x / (4 * R.ω)) + 4 * R.ω :=
      le_mul_div_add (A := R.x) (d := 4 * R.ω) hω0N
    have h1 := (Nat.cast_le (α := ℝ)).mpr hdivub
    have h2 : (((R.x / (4 * R.ω) : ℕ)) : ℝ) ≤ (A : ℝ) := by exact_mod_cast hxdiv
    push_cast at h1
    have hbig : 8 * (R.ω : ℝ) ≤ (R.x : ℝ) := by nlinarith [hxω, hHhi4, hω0]
    nlinarith [h1, h2, hω0, hbig]
  -- ⟦the drift blocks, one free block each⟧
  have hstrat := m4_freeBlockSup_of_chiSummed (R := R) (M := M) (Bcl := Bcl) hM hBcl0 hgate
    hchi H hlo hhi L hℓH hℓcnt hLarc hL16 b q hq hqQ
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
    have hAle : (A : ℝ) ≤ ((A + m * L : ℕ) : ℝ) := by
      exact_mod_cast (by omega : A ≤ A + m * L)
    have h2HA' : 2 * (H : ℝ) ≤ ((A + m * L : ℕ) : ℝ) := by linarith
    have hxA' : (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * ((A + m * L : ℕ) : ℝ) := by
      nlinarith [hxA, hAle, hω0]
    have hcapA' : ((A + m * L : ℕ) : ℝ) ≤ 2 * (R.x : ℝ) := by
      have hnat : A + m * L ≤ 2 * R.x :=
        calc A + m * L ≤ R.x + H := Nat.add_le_add hAtop hmL
          _ ≤ 2 * R.x := by omega
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this ⊢
      linarith
    have hfit' : (B + m * L) + L ≤ 2 * (A + m * L) := by omega
    have h := hstrat (A + m * L) (B + m * L) hApos' h2HA' hxA' hcapA' hfit'
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

⟦THE GATE CENSUS — FINAL AUDIT (wave ⑤, ⟦T-3e⟧)⟧ — finite, and every gate is classified
**witnessed** (a witness is exhibited in §6), **regime-absorbable** (one-sided `H`-LOWER on
the window range, hence absorbable by the `g`-arm/`U1floor` of the outer register),
**consumer data**, **THE ANALYTIC SLOT**, or **`H`-UPPER** (the sandwich genre — named, with
its binding order):

1. `M4DoorGates Cg R M k δ` — UNCHANGED, `hMδ` included (⟦UNTOUCHABLE⟧).  *consumer data.*
2. `1 ≤ M` — *consumer data.*
3. `∀ H, 0 ≤ RSan H`, `∀ H, 0 ≤ RStr H`, `∀ H, 0 ≤ Braw H` — *witnessed*
   (`rSanWitness_nonneg`, `rStrWitness_nonneg`; `Braw` by the consumer's own choice).
4. `∀ j H, j₀ ≤ j → RS j H ≤ RSan H` — the analytic envelope.  *consumer data* (the port's
   deliverable; its ceiling is `m4_second_road_rs_ceiling`).
5. `arcDen 12 H ^ 7 ≤ RStr H` — ⟦G1⟧, a FLOOR on witnessed data.  *witnessed*
   (`rStrWitness_G1` at `RStr H := max 1 (arcDen 12 H ^ 7)`).
6. `44·RSan H + 87·arcDen 12 H ≤ (4/3)^{j₀}` — ⟦G2⟧.  *`H`-UPPER, NON-BINDING*: at the
   anti-vacuity envelope it caps `loglog H ≲ 0.024·M·Adoor M` (`g2_of_j0_floor`), slacker
   than ⟦gate 8⟧ by the factor `0.415·M ≈ 8·10⁶¹` at the honest `M`.  Discharged from the
   `j₀`-floor `j₀ ≳ 22 + 48·loglog H`, which `doorRowFloor M = M·Adoor M ≈ 5·10⁶⁷` clears by
   55 orders even at the tower's top.
7. `128·arcDen 12 H ³ ≤ H` — the window floor.  *regime-absorbable* (`H`-LOWER, `H`-only:
   `(log H)^{36} ≪ H`).
8. `arcDen 12 H < calP (Adoor M) (3072M) 1` — the `M`-RELATIVE dilation gate.  **THE ONE
   BINDING `H`-UPPER**: `loglog H < 0.0578·Adoor M`.  It is NOT the retired numeral
   `log H ≤ 2^{21845}` (⟦WALL C⟧'s genre, an absolute cap) — it is `M`-relative, and `M` is
   in the register's own witnessed group, chosen AFTER `R`.  **Wave ⑤ tested the
   ⟦A-6 / D0-TEST⟧ `D₀`-truncation against it and the truncation is REFUTED** — see the
   module header, `truncD_admissible` and `stratum_sq_le_chiSummed_at_truncD` for the exact
   accounting.  The door-anchor ask goes to JYH.
9. the composed drift price (⟦item 4′, RE-CUT⟧):
   `96(1+2π)²·(1 + log arcDen 12 H)²·m4BclGraded j₀ (2·RSan) (2·RStr) H ≤ Braw H`.
   **No `arcDen` power, no `q`, no `q²`** — this is the line the whole road exists to cut.
   *consumer data*; composed with ⟦10⟧ it is the port's ceiling (§6).
10. `M4GradeGateSplit R δ₀ δ Braw k` — the budget line at the head's own constant `δ₀`.
    *consumer data.*
11. `M4ChiSummedFreeRow R M RS` — **THE ANALYTIC SLOT**, the socket of S-1.  Inhabited
    (`m4_chiSummedFreeRow_trivial`); the port must inhabit it at the §6 ceiling.
    **⟦R-P5, wave P-1⟧ the socket now carries THREE BASE ANTECEDENTS inside its own
    `∀`-prefix** (`2^j ≤ A`, `√H ≤ A`, `R.x ≤ 16·R.ω·arcDen 12 H·A` — see `M4ChiSummed`'s
    header), **and ⟦(α)⟧ a FOURTH, the base cap `A ≤ 2·R.x`** (the (α) base-cap surgery,
    JYH-granted 2026-07-30; it is what makes the door's `DoorFuseFrame` hypotheses
    satisfiable — see `M4ChiSummed`'s ⟦THE (α) BASE-CAP SURGERY⟧).  All four only WEAKEN the
    socket, so this register line gains NOTHING: no new conjunct, no new gate, no anchor
    movement, and the port adds ZERO `H`-demand.  The cap is discharged INSIDE this
    theorem's proof, at §3's `m4_blockMeanSqBlk2_of_chiSummed`, from `doorLadder_le_start`
    and the regime's own `H + 1 ≤ R.x` — no new hypothesis on the register.

⟦F5 CHECK, RE-RUN — WITH THE x-ANTECEDENT⟧ `R.x` occurs in this register in exactly one
place — `g R.Hhi R.ω ≤ R.x`, an `X`-LOWER supplied by the spine — so there is no `X`-upper
anywhere and no `X`-upper can ride with an `X`-lower in any bundle (grep re-run over
`M4ChiSummed`, `M4Gauss`, `M4SecondRoad`: clean).  **The socket's new x-scale antecedent does
NOT change this**: `R.x ≤ 16·R.ω·arcDen 12 H·A` is a HYPOTHESIS inside ⟦item 11⟧'s Prop, not
a conjunct of this register — it is what the socket's SUPPLIER may assume, discharged here
from the ladder's own geometric floor (`doorLadder_ge_x_div_four_omega`, §3) and the regime's
wave-II headroom, with no new field and no `g`-arm movement.  Read as an `X`-comparison it is
an `X`-UPPER *given to* the supplier, i.e. an `X`-LOWER *on the base* — the same direction as
the `g`-arm, never against it.  ⟦WALL-D/F5's `DoorRowCarriedT0` bundle is not reached at
all.⟧  The
`H`-conjuncts are: one LOWER (⟦7⟧, regime-absorbable), two UPPERS (⟦6⟧ slack by 61 orders,
⟦8⟧ binding), and the rest are envelope floors on witnessed data. -/
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
  have hblk2 := m4_blockMeanSqBlk2_of_chiSummed (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
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

/-! ## §5 — THE `D₀` CONSTANT (⟦T-1⟧, wave ⑤)

The truncation ceiling, stated as a PRE-`R` constant of `δ₀` alone — no `H`, no `q`, no `X`
— together with the per-stratum admissibility it is calibrated for, and the record that the
door gate is instantiable at it with zero new bytes.  The module header states why the
composition nevertheless does not close. -/

/-- **THE SPLIT BUDGET** `truncBudget δ₀ = (δ₀/2)² / (96(1+2π)²)`.

The block-level allowance the register leaves per stratum, traced through the composition of
⟦item 10⟧ (`M4GradeGateSplit`: `√(Braw H) ≤ δ₀`, i.e. `Braw H ≤ δ₀²` — and `≤ (δ₀/2)²` once
the door's own two grade terms take their half) and ⟦item 9⟧ (the composed drift price
`96(1+2π)²·(1+log arcDen)²·B_cl ≤ Braw`).  `(1 + log arcDen)²` is deliberately NOT divided
out: it multiplies the *graded* factor, and the trivial branch this budget prices carries no
`B_cl`.

At the honest closing numbers (`δ₀ = 2·10⁻⁴⁹`, `96(1+2π)² ≈ 5092`) this is `≈ 2·10⁻¹⁰²`. -/
def truncBudget (δ₀ : ℝ) : ℝ := (δ₀ / 2) ^ 2 / (96 * (1 + 2 * Real.pi) ^ 2)

theorem truncBudget_pos {δ₀ : ℝ} (h : 0 < δ₀) : 0 < truncBudget δ₀ := by
  unfold truncBudget
  have hpi : (0 : ℝ) < 1 + 2 * Real.pi := by
    have := Real.pi_pos; linarith
  positivity

/-- **THE TRUNCATION CEILING** `D₀ = ⌈2/√(truncBudget δ₀)⌉₊` — ⟦T-1⟧.

`(Cg, δ₀)`-ONLY: no `H`, no `q`, no `X`, no `M`.  At `δ₀ = 2·10⁻⁴⁹` the honest magnitude is
`≈ 1.4·10⁵¹` (`log₂ D₀ ≈ 170`), reproducing ⟦REF-SAND⟧'s `2^163` and ⟦D0-TEST⟧'s SITE-A
`2.9·10⁵⁰` to within the `96(1+2π)²`-vs-`Bblk` bookkeeping.  Against the door's own bottom
block `calP (Adoor M) (3072M) 1 = 2^{Adoor M}` with `Adoor M ≥ 2^18 = 262144` the gate
`D₀ < 2^{Adoor M}` is free by 261 974 bits — which is exactly why the truncation was worth
testing. -/
def truncD (δ₀ : ℝ) : ℕ := ⌈2 / Real.sqrt (truncBudget δ₀)⌉₊

theorem truncD_ge (δ₀ : ℝ) : 2 / Real.sqrt (truncBudget δ₀) ≤ ((truncD δ₀ : ℕ) : ℝ) :=
  Nat.le_ceil _

/-- **⟦THE SITE-A ADMISSIBILITY⟧** (`truncD_admissible`) — for a stratum `d > D₀` on a window
of length `L ≥ D₀`, the GATE-FREE trivial bound `L/d + 1` is under the split budget:

```
      (L/d + 1)²  ≤  truncBudget δ₀ · L² .
```

⟦THE ±1, HONESTLY⟧ `d > D₀ ≥ 2/√B` gives `L/d < √B·L/2`, and `L ≥ D₀ ≥ 2/√B` gives
`1 ≤ √B·L/2` — the two halves that the `2` in `D₀`'s numerator buys, one for the quotient
and one for the `+1`.  This is why the constant is `2/√B` and not `1/√B`.

⟦LENGTH-INVARIANT⟧ `L` enters only through `L ≥ D₀`, so the SAME `D₀` serves the ambient
`H`, the drift block `ℓ`, and the dilated `H/d` — ⟦D0-TEST⟧'s "ABSOLUTE".

⟦AND WHY IT DOES NOT COMPOSE⟧ the stratified recombination (`M4Gauss` §5) does not offer the
stratum the budget `truncBudget δ₀ · L²`; after the weighted Cauchy–Schwarz it offers
`4·B_cl·L²/d²`, which the trivial bound misses by `1/B_cl` at every `d`.  See the module
header. -/
theorem truncD_admissible {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {L d : ℕ}
    (hd : truncD δ₀ < d) (hL : truncD δ₀ ≤ L) :
    ((L : ℝ) / (d : ℝ) + 1) ^ 2 ≤ truncBudget δ₀ * (L : ℝ) ^ 2 := by
  have hB : 0 < truncBudget δ₀ := truncBudget_pos hδ₀
  have hs : 0 < Real.sqrt (truncBudget δ₀) := Real.sqrt_pos.mpr hB
  have hceil := truncD_ge δ₀
  have hdR : ((truncD δ₀ : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hLR : ((truncD δ₀ : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hd2 : 2 / Real.sqrt (truncBudget δ₀) < (d : ℝ) := lt_of_le_of_lt hceil hdR
  have hL2 : 2 / Real.sqrt (truncBudget δ₀) ≤ (L : ℝ) := le_trans hceil hLR
  have hd0 : (0 : ℝ) < (d : ℝ) := lt_of_le_of_lt (by positivity) hd2
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  -- ⟦the two halves the `2` buys⟧
  have hds : (2 : ℝ) < (d : ℝ) * Real.sqrt (truncBudget δ₀) := by
    rw [div_lt_iff₀ hs] at hd2; linarith
  have hLs : (2 : ℝ) ≤ (L : ℝ) * Real.sqrt (truncBudget δ₀) := by
    rw [div_le_iff₀ hs] at hL2; linarith
  have hquot : (L : ℝ) / (d : ℝ) ≤ (L : ℝ) * Real.sqrt (truncBudget δ₀) / 2 := by
    rw [div_le_iff₀ hd0]
    nlinarith [mul_le_mul_of_nonneg_left hds.le hL0]
  have hkey : (L : ℝ) / (d : ℝ) + 1 ≤ (L : ℝ) * Real.sqrt (truncBudget δ₀) := by linarith
  have hnn : (0 : ℝ) ≤ (L : ℝ) / (d : ℝ) + 1 := by positivity
  have hsq : Real.sqrt (truncBudget δ₀) ^ 2 = truncBudget δ₀ := Real.sq_sqrt hB.le
  calc ((L : ℝ) / (d : ℝ) + 1) ^ 2
      ≤ ((L : ℝ) * Real.sqrt (truncBudget δ₀)) ^ 2 := by nlinarith
    _ = truncBudget δ₀ * (L : ℝ) ^ 2 := by rw [mul_pow, hsq]; ring

/-- **⟦THE ZERO-BYTE INSTANTIATION⟧** (`stratum_sq_le_chiSummed_at_truncD`) — ⟦D0-TEST⟧'s
structural fact, recorded in the kernel: the per-stratum bound holds with the door gate read
at `D₀` and NOTHING else moved.  `q` and the ceiling `W` are pure intermediates of the door
side (`M4Residue.door_dilation_gate'` concludes `d < calP …`; neither occurs), so the whole
chain instantiates at `W := truncD δ₀` on the strata `d ≤ D₀`.

What no instantiation supplies is the strata `d > D₀`; see the module header. -/
theorem stratum_sq_le_chiSummed_at_truncD {M K n q d Lw : ℕ} {δ₀ : ℝ} (hM : 1 ≤ M)
    (hq : 0 < q) (hd0 : 0 < d) (hdq : d ∣ q) (hdD : (d : ℝ) ≤ ((truncD δ₀ : ℕ) : ℝ))
    (hgate : ((truncD δ₀ : ℕ) : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) (b : ℤ)
    (hlen : dilLen K n d ≤ Lw) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
        ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff M m‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup χ M Lw (n / d)) ^ 2 :=
  stratum_sq_le_chiSummed hM hq hd0 hdq hdD hgate b hlen

/-! ## §6 — THE PRICING AUDIT (⟦T-3⟧, wave ⑤)

The register's own gates, witnessed where they are witnessable and priced where they are
not.  Nothing here is consumed by `m4_second_road`; it is the SATISFIABILITY record the port
gate quotes. -/

/-- **⟦G1's WITNESS⟧** — `RStr H := max 1 (arcDen 12 H ^ 7)`.

⟦gate 5⟧ (`arcDen 12 H ^ 7 ≤ RStr H`) is an envelope FLOOR on witnessed data, so it is
inhabited outright; the `max 1` is what makes ⟦gate 3⟧ (`∀ H, 0 ≤ RStr H`, stated for EVERY
`H`, not only the window range) hold off-range as well.  `arcDen⁷` is the `φ(q)` ledger's
first entry: `arcDen³` from the χ-summed narrowing, `arcDen⁴` from the dilated cap — see
`M4ChiSummed`'s ⟦φ(q) LEDGER⟧. -/
def rStrWitness (H : ℕ) : ℝ := max 1 (arcDen 12 H ^ 7)

theorem rStrWitness_nonneg (H : ℕ) : 0 ≤ rStrWitness H :=
  le_trans zero_le_one (le_max_left _ _)

theorem rStrWitness_G1 (H : ℕ) : arcDen 12 H ^ 7 ≤ rStrWitness H := le_max_right _ _

/-- **⟦THE ANALYTIC ENVELOPE AT ANTI-VACUITY⟧** — `RSan H := max 1 (4·arcDen 12 H)`, the
socket's own anti-vacuity grade (`M4ChiSummed.m4_chiSummedFreeRow_trivial` at
`RS j H := 4·arcDen 12 H`) rounded up so ⟦gate 3⟧ holds off-range.  The PORT replaces this by
something far smaller; `m4_second_road_rs_ceiling` below is the number it must beat. -/
def rSanWitness (H : ℕ) : ℝ := max 1 (4 * arcDen 12 H)

theorem rSanWitness_nonneg (H : ℕ) : 0 ≤ rSanWitness H :=
  le_trans zero_le_one (le_max_left _ _)

theorem rSanWitness_envelope (H : ℕ) : 4 * arcDen 12 H ≤ rSanWitness H := le_max_right _ _

/-- **⟦G2's `j₀` FLOOR⟧** (`g2_of_j0_floor`) — at the anti-vacuity envelope, ⟦gate 6⟧
`44·RSan H + 87·arcDen 12 H ≤ (4/3)^{j₀}` follows from the floor

```
      4 · log (263 · max 1 (arcDen 12 H))  ≤  j₀ ,
```

because `log(4/3) ≥ 1/4` (`(4/3)⁴ = 256/81 > e`, the constant `M4Spine` already spends).

⟦THE HONEST SIZE⟧ the floor reads `j₀ ≳ 22 + 48·loglog H`.  The door's own `j₀` is
`doorRowFloor M = M·Adoor M ≥ 2^18·M`, which at the honest `M = 1.93·10⁶²` is `≈ 5·10⁶⁷` —
above the floor by more than 55 orders even at the tower's top (`loglog Hhi ≈ 9·10¹⁰` gives
a floor `≈ 4·10¹²`).

⟦AND THE F5 READING⟧ ⟦gate 6⟧ is, at this envelope, an `H`-UPPER in disguise: it caps
`arcDen 12 H ≤ (4/3)^{j₀}/263`, i.e. `loglog H ≲ 0.024·M·Adoor M`.  It is NOT the binding
one — ⟦gate 8⟧ caps `loglog H ≲ 0.058·Adoor M`, tighter by the whole factor `0.415·M ≈
8·10⁶¹`.  So while ⟦gate 8⟧ stands, ⟦gate 6⟧ is slack by 61 orders; if ⟦gate 8⟧ were ever
retired, ⟦gate 6⟧ becomes the (vastly weaker) successor sandwich, and the analytic envelope
the port delivers — far below `4·arcDen` — pushes it further out still. -/
theorem g2_of_j0_floor (H : ℕ) {j₀ : ℕ}
    (hj : 4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ (j₀ : ℝ)) :
    44 * rSanWitness H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀ := by
  set m := max (1 : ℝ) (arcDen 12 H) with hm
  have hm1 : (1 : ℝ) ≤ m := le_max_left _ _
  have harc : arcDen 12 H ≤ m := le_max_right _ _
  have hRS : rSanWitness H ≤ 4 * m := by
    unfold rSanWitness
    exact max_le (by linarith) (by linarith)
  have hpos : (0 : ℝ) < 263 * m := by linarith
  have hpow : (0 : ℝ) < (4 / 3 : ℝ) ^ j₀ := by positivity
  have hlog43 : (1 : ℝ) / 4 ≤ Real.log (4 / 3) := by
    have h : (1 : ℝ) ≤ Real.log ((4 / 3 : ℝ) ^ (4 : ℕ)) := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < (4 / 3 : ℝ) ^ (4 : ℕ))]
      have := Real.exp_one_lt_d9
      norm_num
      linarith
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hj0 : (0 : ℝ) ≤ (j₀ : ℝ) := Nat.cast_nonneg _
  have hlogle : Real.log (263 * m) ≤ Real.log ((4 / 3 : ℝ) ^ j₀) := by
    rw [Real.log_pow]
    linarith [mul_le_mul_of_nonneg_left hlog43 hj0]
  have hfin : 263 * m ≤ (4 / 3 : ℝ) ^ j₀ := by
    have hexp := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log hpos, Real.exp_log hpow] at hexp
  linarith

/-- **⟦THE COMPOSED `RS`-GRADE DEMAND⟧** (`m4_second_road_rs_ceiling`) — the number the port
gate quotes.

Composing ⟦item 9⟧ (the drift price) with ⟦item 10⟧ (`M4GradeGateSplit`) and dropping the
`H`-DECAYING half of `m4BclGraded` (its weighted head runs at `(4/3)^{j₀}·H^{-0.415}` and
`(8/3)^{j₀}·H^{-1.415}`, both nonnegative, so dropping them is free), the register's own
gates force

```
      96(1+2π)² · (1 + log arcDen 12 H)² · (108/5) · RSan H  ≤  δ₀² .
```

⟦THE SHAPE OF THE DEMAND — DOES IT DECAY?⟧ **It decays, and only at `loglog` scale.**
`96(1+2π)²·(108/5) ≈ 1.1·10⁵` is absolute; the only `H`-motion is `(1 + log arcDen)² =
(1 + 12·loglog H)²` in the DENOMINATOR of the ceiling.  So the port must deliver

```
      RSan H  ≲  δ₀² / (1.1·10⁵ · (1 + 12 loglog H)²)   ≈  2.5·10⁻¹⁰⁵ / (loglog H)²
```

at `δ₀ = 2·10⁻⁴⁹` (`96(1+2π)²·(108/5) ≈ 1.1·10⁵`, `δ₀² = 4·10⁻⁹⁸`)

— a CONSTANT times `(loglog H)^{-2}`, which is INSIDE ⟦D1-SCOPE⟧'s residual law (bounded
powers of `loglog H` are free; only positive powers of `log H` are fatal), and far weaker
than KMT's own `ε ≥ (log H)^{-1/200}`.  **No power of `arcDen` and no `q` appears** — that
is the whole content of the second road.  The `RStr` half is untouched by this ceiling: its
coefficient carries `H^{-0.415}` and vanishes against any envelope once `H ≳ 2^{j₀}` (the
`M4Maximal.m4SmallGradeFits` threshold), which is why ⟦G1⟧ can be witnessed at `arcDen⁷`
while ⟦G2⟧'s analytic half cannot. -/
theorem m4_second_road_rs_ceiling {R : ChowlaRegime} {δ₀ δ : ℝ} {RSan RStr Braw : ℕ → ℝ}
    {j₀ k : ℕ} (hδ : 0 ≤ δ)
    (hRSan0 : ∀ H : ℕ, 0 ≤ RSan H) (hRStr0 : ∀ H : ℕ, 0 ≤ RStr H)
    (hdrift : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H ≤ Braw H)
    (hgrade : M4GradeGateSplit R δ₀ δ Braw k) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSan H) ≤ δ₀ ^ 2 := by
  intro H hlo hhi
  have hpi : (0 : ℝ) < 1 + 2 * Real.pi := by have := Real.pi_pos; linarith
  have hBcl0 : 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hd := hdrift H hlo hhi
  have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
  have hBraw0 : 0 ≤ Braw H := le_trans (mul_nonneg hfac0 hBcl0) hd
  -- ⟦item 10 caps the budget by `δ₀²`⟧
  have hg := hgrade H hlo hhi
  have htail : (0 : ℝ) ≤ 4 * 2 ^ k / (R.x : ℝ) := by positivity
  have hsqrt : Real.sqrt (Braw H) ≤ δ₀ := by linarith
  have hsq : Real.sqrt (Braw H) ^ 2 = Braw H := Real.sq_sqrt hBraw0
  have hBrawδ : Braw H ≤ δ₀ ^ 2 := by
    have h0 : (0 : ℝ) ≤ Real.sqrt (Braw H) := Real.sqrt_nonneg _
    nlinarith
  -- ⟦the graded price dominates its analytic half⟧
  have hhead : (0 : ℝ) ≤ (9 / 2 * (3 / 2 : ℝ) ^ Nat.log 2 H * (4 / 3 : ℝ) ^ j₀ / (H : ℝ)
      + 9 / 5 * (3 / 2 : ℝ) ^ Nat.log 2 H * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2)
        * (2 * RStr H) := by
    have := hRStr0 H
    positivity
  have hlow : 108 / 5 * RSan H
      ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    unfold m4BclGraded m4Cmax
    linarith
  calc 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSan H)
      ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
        mul_le_mul_of_nonneg_left hlow hfac0
    _ ≤ Braw H := hd
    _ ≤ δ₀ ^ 2 := hBrawδ

/-! ## §GK — the G-lever twin

The additive `_gk` family at `G := s13GK K M` (`GLever`): each declaration below is its
landed original with `(K : ℕ)` as a new FIRST binder, every literal `3072 * M` rewritten to
`s13GK K M`, and the door datum read at the lever (`doorSievedCoeff_gk`, `doorChiSup_gk`).
`J` stays `2`; ⟦gate 8⟧'s `arcDen 12 H < calP (Adoor M) (s13GK K M) 1` is the LANDED level-1
symbol (`GLever.calP_gk_one_eq`), so the `M`-RELATIVE dilation gate is unmoved by the lever.
The block-length page (`blockLen` and its five lemmas), the truncation budget
(`truncBudget`, `truncD`) and the witness envelopes read no door object and keep their
landed names.
-/

/-- `M4SievedDoorSqBlk2` (:291), at the lever. -/
def M4SievedDoorSqBlk2_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (ℓ : ℕ → ℕ → ℕ)
    (Bblk : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
      (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q → ℓ H q ≤ H →
      (H : ℝ) ≤ arcDen 12 H ^ 2 * (ℓ H q : ℝ) →
        (∫ n, blockSupSq (doorSievedCoeff_gk K M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
            ∂(logMeasure R.x R.ω))
          ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2

/-- `m4_sievedDoorSq_of_blk2` (:303), at the lever. -/
theorem m4_sievedDoorSq_of_blk2_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {ℓ : ℕ → ℕ → ℕ}
    {Bblk Braw : ℕ → ℝ}
    (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hℓ1 : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q)
    (hℓH : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → ℓ H q ≤ H)
    (hℓcnt : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (H : ℝ) ≤ arcDen 12 H ^ 2 * (ℓ H q : ℝ))
    (hℓdrift : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      arcDen 12 H * (ℓ H q : ℝ) ≤ (q : ℝ) * (H : ℝ))
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * (1 + 2 * Real.pi) ^ 2 * Bblk H ≤ Braw H)
    (hblk : M4SievedDoorSqBlk2_gk K R M ℓ Bblk) : M4SievedDoorSq_gk K R M Braw := by
  intro htr H _ hlo hhi α hα
  have hH : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  obtain ⟨b, q, hq, hqQ, hd⟩ := hα
  have hℓ1' := hℓ1 H q hlo hhi hq hqQ
  have hℓH' := hℓH H q hlo hhi hq hqQ
  have hℓcnt' := hℓcnt H q hlo hhi hq hqQ
  have hℓdrift' := hℓdrift H q hlo hhi hq hqQ
  have hℓ0 : 0 < ℓ H q := hℓ1'
  set c := doorSievedCoeff_gk K M with hc
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

/-- `M4BlockMeanSqBlk2` (:372), at the lever. -/
def M4BlockMeanSqBlk2_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (ℓ : ℕ → ℕ → ℕ)
    (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
    1 ≤ ℓ H q → ℓ H q ≤ H → (H : ℝ) ≤ arcDen 12 H ^ 2 * (ℓ H q : ℝ) →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          blockSupSq (doorSievedCoeff_gk K M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
        ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2
            * (doorLadder R.x H (i + 1) : ℝ)

/-- `m4_cover_assembly_blk2` (:383), at the lever. -/
theorem m4_cover_assembly_blk2_gk (K : ℕ) {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {ℓ : ℕ → ℕ → ℕ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates_gk K Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqBlk2_gk K R M k ℓ Bblk) :
    M4SievedDoorSqBlk2_gk K R M ℓ (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ h1 h2 h3
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2 := by
    have := hB0 H; positivity
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => blockSupSq (doorSievedCoeff_gk K M) H (ℓ H q) n ((b : ℝ) / (q : ℝ)))
    (P := Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount
    (fun n => blockSupSq_nonneg _ _ _ _ _) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ h1 h2 h3)
  refine le_trans hmain (le_of_eq ?_)
  ring

set_option maxHeartbeats 1200000 in
-- the block sum is re-associated over the drift blocks and then over the ladder block, and
-- the stratified bound is instantiated once per drift block; every arithmetic step is
-- `linarith`/`nlinarith` with hints
/-- `m4_blockMeanSqBlk2_of_chiSummed` (:485), at the lever. -/
theorem m4_blockMeanSqBlk2_of_chiSummed_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hM : 1 ≤ M) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 2 ≤ (H : ℝ))
    (hcount : (k : ℝ) ≤ Real.log (R.ω : ℝ) / Real.log 2 + 2)
    (hchi : M4ChiSummedBlockMeanSqN_gk K R M Bcl) :
    M4BlockMeanSqBlk2_gk K R M k blockLen
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
  have hL16 : 16 * arcDen 12 H ^ 2 ≤ (H : ℝ) := by
    nlinarith [harcH, sq_nonneg (arcDen 12 H)]
  -- ⟦R-P5, THE x-SCALE LADDER AT THIS RUNG⟧ the base antecedents `M4Gauss` now asks for,
  -- discharged from the ladder's geometric floor (`doorLadder_ge_x_div_four_omega`), its
  -- CEILING (`doorLadder_le_start`, the (α) base cap) and the regime's own wave-II headroom
  -- `8·H₊·log²H₊ ≤ ⌊x/ω⌋` (whose two log factors are `≥ 1` at `H₊ ≥ 4·10⁶`)
  -- — NO new regime field, NO `g`-arm movement
  have hω0N : 0 < 4 * R.ω := by have := R.hω; omega
  have hω0 : (0 : ℝ) < (R.ω : ℝ) := by
    have h : 0 < R.ω := by have := R.hω; omega
    exact_mod_cast h
  have hxdiv : R.x / (4 * R.ω) ≤ A := by
    rw [hA]
    exact doorLadder_ge_x_div_four_omega (H := H) R.hω hcount (by omega)
  -- ⟦(α) THE BASE CAP AT THIS RUNG⟧ the ceiling side of the socket's fourth base antecedent
  -- (the (α) base-cap surgery, JYH-granted 2026-07-30): the ladder never exceeds its own
  -- top, so `X_{i+1} ≤ x` and every drift-shifted base is `≤ x + H ≤ 2x`
  have hAtop : A ≤ R.x := by
    rw [hA]
    exact doorLadder_le_start hxH (i + 1)
  have hHhi4 : (4000000 : ℝ) ≤ (R.Hhi : ℝ) := by
    have h : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
    exact_mod_cast h
  have hlogHhi : (1 : ℝ) ≤ Real.log (R.Hhi : ℝ) := by
    have hexp : Real.exp 1 ≤ (R.Hhi : ℝ) := by nlinarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by linarith)).mpr hexp
  have hxω : 8 * (R.ω : ℝ) * (R.Hhi : ℝ) ≤ (R.x : ℝ) := by
    have hh := R.hheadroom'
    have hcast : (((R.x / R.ω : ℕ)) : ℝ) ≤ (R.x : ℝ) / (R.ω : ℝ) := Nat.cast_div_le
    have hlogsq : (1 : ℝ) ≤ Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) := by
      nlinarith [hlogHhi]
    have h1 : 8 * (R.Hhi : ℝ) ≤ (R.x : ℝ) / (R.ω : ℝ) := by
      calc 8 * (R.Hhi : ℝ) = 8 * (R.Hhi : ℝ) * 1 := by ring
        _ ≤ 8 * (R.Hhi : ℝ) * (Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogsq (by linarith)
        _ = 8 * (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) := by ring
        _ ≤ (((R.x / R.ω : ℕ)) : ℝ) := hh
        _ ≤ (R.x : ℝ) / (R.ω : ℝ) := hcast
    rw [le_div_iff₀ hω0] at h1
    linarith
  have hHhiR : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast hhi
  have h8ωH : 8 * R.ω * H ≤ R.x := by
    have h : (8 : ℝ) * (R.ω : ℝ) * (H : ℝ) ≤ (R.x : ℝ) := by nlinarith [hxω, hHhiR, hω0]
    exact_mod_cast h
  have h2HA : 2 * (H : ℝ) ≤ (A : ℝ) := by
    have hn : 2 * H ≤ A := by
      refine le_trans ((Nat.le_div_iff_mul_le hω0N).mpr ?_) hxdiv
      calc 2 * H * (4 * R.ω) = 8 * R.ω * H := by ring
        _ ≤ R.x := h8ωH
    exact_mod_cast hn
  have hxA : (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * (A : ℝ) := by
    have hdivub : R.x ≤ 4 * R.ω * (R.x / (4 * R.ω)) + 4 * R.ω :=
      le_mul_div_add (A := R.x) (d := 4 * R.ω) hω0N
    have h1 := (Nat.cast_le (α := ℝ)).mpr hdivub
    have h2 : (((R.x / (4 * R.ω) : ℕ)) : ℝ) ≤ (A : ℝ) := by exact_mod_cast hxdiv
    push_cast at h1
    have hbig : 8 * (R.ω : ℝ) ≤ (R.x : ℝ) := by nlinarith [hxω, hHhi4, hω0]
    nlinarith [h1, h2, hω0, hbig]
  -- ⟦the drift blocks, one free block each⟧
  have hstrat := m4_freeBlockSup_of_chiSummed_gk K (R := R) (M := M) (Bcl := Bcl) hM hBcl0 hgate
    hchi H hlo hhi L hℓH hℓcnt hLarc hL16 b q hq hqQ
  have hper : ∀ m ∈ Finset.range N,
      ∑ n ∈ Finset.Ioc A B, (subWindowSup (doorSievedCoeff_gk K M) L (n + m * L)
          ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ 8 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by
    intro m hm
    have hmL : m * L ≤ H := mul_le_of_lt_numBlocks (Finset.mem_range.mp hm)
    have hshift : ∑ n ∈ Finset.Ioc A B,
        (subWindowSup (doorSievedCoeff_gk K M) L (n + m * L) ((b : ℝ) / (q : ℝ))) ^ 2
        = ∑ n ∈ Finset.Ioc (A + m * L) (B + m * L),
            (subWindowSup (doorSievedCoeff_gk K M) L n ((b : ℝ) / (q : ℝ))) ^ 2 :=
      sum_Ioc_shift (fun n => (subWindowSup (doorSievedCoeff_gk K M) L n ((b : ℝ) / (q : ℝ))) ^ 2)
        A B _
    rw [hshift]
    have hApos' : 0 < A + m * L := by omega
    have hAle : (A : ℝ) ≤ ((A + m * L : ℕ) : ℝ) := by
      exact_mod_cast (by omega : A ≤ A + m * L)
    have h2HA' : 2 * (H : ℝ) ≤ ((A + m * L : ℕ) : ℝ) := by linarith
    have hxA' : (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * ((A + m * L : ℕ) : ℝ) := by
      nlinarith [hxA, hAle, hω0]
    have hcapA' : ((A + m * L : ℕ) : ℝ) ≤ 2 * (R.x : ℝ) := by
      have hnat : A + m * L ≤ 2 * R.x :=
        calc A + m * L ≤ R.x + H := Nat.add_le_add hAtop hmL
          _ ≤ 2 * R.x := by omega
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this ⊢
      linarith
    have hfit' : (B + m * L) + L ≤ 2 * (A + m * L) := by omega
    have h := hstrat (A + m * L) (B + m * L) hApos' h2HA' hxA' hcapA' hfit'
    have hbase : ((A + m * L : ℕ) : ℝ) ≤ 2 * (A : ℝ) := by
      have hnat : A + m * L ≤ 2 * A := by omega
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this ⊢
      linarith
    have hfac0 : (0 : ℝ) ≤ 4 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hbase hfac0]
  -- ⟦the drift-block sum⟧
  have hswap : ∑ n ∈ Finset.Ioc A B, blockSupSq (doorSievedCoeff_gk K M) H L n ((b : ℝ) / (q : ℝ))
      = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.Ioc A B,
          (subWindowSup (doorSievedCoeff_gk K M) L (n + m * L) ((b : ℝ) / (q : ℝ))) ^ 2 := by
    unfold blockSupSq
    exact Finset.sum_comm
  rw [hswap]
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine le_of_eq ?_
  ring

/-- `m4_second_road` (:683), at the lever. -/
theorem m4_second_road_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
            M4DoorGates_gk K Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            M4GradeGateSplit R δ₀ δ Braw k →
            M4ChiSummedFreeRow_gk K R M RS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_split_gk K
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
  have hchi : M4ChiSummedBlockMeanSqN_gk K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied_gk K j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  -- ⟦the blocked block mean square⟧
  have hblk2 := m4_blockMeanSqBlk2_of_chiSummed_gk K (k := k) hM hBcl0 hdgate harc
    hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  -- ⟦the cover, then the socket⟧
  have hcov := m4_cover_assembly_blk2_gk K hgates hBblk0 hblk2
  refine hR δ Braw M k hgates hBraw0 hgrade ?_
  refine m4_sievedDoorSq_of_blk2_gk K (ℓ := blockLen)
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

/-- `stratum_sq_le_chiSummed_at_truncD` (:848), at the lever. -/
theorem stratum_sq_le_chiSummed_at_truncD_gk (K : ℕ) {M Kw n q d Lw : ℕ} {δ₀ : ℝ} (hM : 1 ≤ M)
    (hq : 0 < q) (hd0 : 0 < d) (hdq : d ∣ q) (hdD : (d : ℝ) ≤ ((truncD δ₀ : ℕ) : ℝ))
    (hgate : ((truncD δ₀ : ℕ) : ℝ) < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) (b : ℤ)
    (hlen : dilLen Kw n d ≤ Lw) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
        ratPhase b q r * ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_gk K M m‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup_gk K χ M Lw (n / d)) ^ 2 :=
  stratum_sq_le_chiSummed_gk K hM hq hd0 hdq hdD hgate b hlen

end Salt.MR

end

-- #audit (temporary)
