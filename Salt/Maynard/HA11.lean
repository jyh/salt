/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Transfer
import Salt.Maynard.TransferSharp

/-!
# `hA11` — the transfer-ratio bound `A1_1 ≤ c·A1` with `c < 1`

The second-moment (Chebyshev) overshoot of the S₂ assembly needs the first
moment `A1_1/A1` to be bounded by an **explicit constant `c < 1`** (rather than
the trivial `A1_1 ≤ T·A1`, which is far too large).  We prove

    A1_1 ≤ (7/10)·A1                       (`A1_1_le_seven_tenths`)

via the pointwise split `A1_1 ≤ (log k)⁻¹·(A1 + B1)` (`A1_1_upper_split`) and
the sharp one-dimensional transfer bounds `B1_upper_sharp`, `A1_lower_sharp`.

## The arithmetic (why `7/10`)

With `b = bParam k R = k·log k/log R`, the frozen `T = k^{1/8}/log k` gives
`b·log R₀ ≤ T·log k = k^{1/8}` (from `log_R0_le` + `hT`), hence

    log(1 + b·log R₀) ≤ log 2 + (1/8)·log k          (`hUb`)

so the sharp upper bound reads `B1 ≤ 4·φW·b⁻¹·(log 2 + (1/8)log k) + errA1`,
i.e. (writing `Q = φW·b⁻¹`)  `B1 ≤ 4Q log 2 + (1/2)Q log k + errA1`.  The
`A1` lower bound reads `A1 ≥ Q·(1 − s(R₀−1)⁻¹) − errB1 ≥ (4/5)Q − errB1`,
using `b·log(R₀−1) ≥ 4` ⇒ `1 − s(R₀−1)⁻¹ ≥ 4/5`.  With the three
lower-order pieces dominated by the `Q log k` main term (the genuine
`R`-large / `k`-large regime), this yields

    B1 ≤ (13/25)·Q·log k ,   A1 ≥ (79/100)·Q ,

so `B1 ≤ ((7/10)log k − 1)·A1` (needs `log k ≥ 790/33 ≈ 23.9`, covered by
`log k ≥ 300`), and finally `A1_1 ≤ (log k)⁻¹(A1+B1) ≤ (7/10)A1`.

The exact ratio the driver receives is **`c = 7/10`**.

## Honest scope of the hypotheses

Everything geometric/analytic is genuinely derived.  Four side hypotheses
isolate the largeness regime and are stated explicitly (never the conclusion):

* `hT`   : the frozen `T = k^{1/8}/log k` (fixes `b·log R₀ ≤ k^{1/8}`);
* `hb4`  : `4 ≤ b·log(R₀−1)`  — the `R`-large condition making `1−s⁻¹ ≥ 4/5`;
* `hEA`, `hEB` : the two `err ≪ main` conditions, i.e. `errA1 ≤ (1/100)Q log k`
  and `errB1 ≤ (1/100)Q`.  These are exactly the "`R ≥ R₁`" statements: with
  `Q = φW·b⁻¹ = φW·log R/(k log k)`, `Q·log k = φW·log R/k` grows in `R` while
  `errA1 k W`, `errB1 k W` are fixed `W`-only constants.
* `hlogk` : `300 ≤ log k`, the `k`-large condition absorbing the `4Q log 2`
  boundary term and the residual `+1/log k`.

See the PORT-BLOCKER note at the end for the one sub-step (reducing `hEA`/`hEB`
to a raw `log R ≥ …` threshold) that is deferred.
-/

open Finset

namespace Salt.Maynard

/-- **`hA11`.**  The transfer-ratio bound `A1_1 ≤ (7/10)·A1`, the explicit
`c = 7/10 < 1` consumed by the Chebyshev overshoot.  Proved from
`A1_1_upper_split` + `B1_upper_sharp` + `A1_lower_sharp`; the four largeness
hypotheses `hT`/`hb4`/`hEA`/`hEB`/`hlogk` are documented in the module header. -/
theorem A1_1_le_seven_tenths (k R W : ℕ) (T : ℝ)
    (hW : W ≠ 0) (hk : 3 ≤ k) (hR : 2 ≤ R)
    (hT : T = (k : ℝ) ^ ((1 : ℝ) / 8) / Real.log k) (hT1 : 1 ≤ T)
    (hX : 4 ≤ R0 k R T)
    (hlogk : 300 ≤ Real.log k)
    (hb4 : 4 ≤ bParam k R * Real.log (R0 k R T - 1))
    (hEA : errA1 k W ≤ (1 / 100) * ((Nat.totient W / W : ℝ) * (bParam k R)⁻¹) * Real.log k)
    (hEB : errB1 k W ≤ (1 / 100) * ((Nat.totient W / W : ℝ) * (bParam k R)⁻¹)) :
    A1_1 k R W T ≤ (7 / 10 : ℝ) * A1 k R W T := by
  -- basic positivity
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW
  have hbpos : 0 < bParam k R := bParam_pos (by omega) hR
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hlogkpos : 0 < Real.log k := Real.log_pos hkR
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hlogRpos : 0 < Real.log R := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have hφWpos : (0 : ℝ) < (Nat.totient W / W : ℝ) :=
    div_pos (by exact_mod_cast Nat.totient_pos.mpr hWpos) (by exact_mod_cast hWpos)
  have hφW0 : (0 : ℝ) ≤ (Nat.totient W / W : ℝ) := hφWpos.le
  have hbinv0 : (0 : ℝ) ≤ (bParam k R)⁻¹ := inv_nonneg.mpr hbpos.le
  have hQpos : (0 : ℝ) < (Nat.totient W / W : ℝ) * (bParam k R)⁻¹ :=
    mul_pos hφWpos (inv_pos.mpr hbpos)
  have hQ0 : (0 : ℝ) ≤ (Nat.totient W / W : ℝ) * (bParam k R)⁻¹ := hQpos.le
  -- ==== b·log R₀ ≤ k^{1/8} ====
  have hR0_1 : 1 ≤ R0 k R T := by omega
  have hLR0nn : 0 ≤ Real.log (R0 k R T) := Real.log_nonneg (by exact_mod_cast hR0_1)
  have hlogR0 : Real.log (R0 k R T) ≤ (T / (k : ℝ)) * Real.log R := log_R0_le hR hR0_1
  have hbTk : bParam k R * ((T / (k : ℝ)) * Real.log R) = (k : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [hT]
    unfold bParam
    field_simp
  have hbU : bParam k R * Real.log (R0 k R T) ≤ (k : ℝ) ^ ((1 : ℝ) / 8) := by
    calc bParam k R * Real.log (R0 k R T)
        ≤ bParam k R * ((T / (k : ℝ)) * Real.log R) :=
          mul_le_mul_of_nonneg_left hlogR0 hbpos.le
      _ = (k : ℝ) ^ ((1 : ℝ) / 8) := hbTk
  -- ==== log(1 + b·log R₀) ≤ log 2 + (1/8)·log k ====
  have hk18_ge1 : (1 : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.one_le_rpow hkR.le (by norm_num)
  have harg_pos : 0 < 1 + bParam k R * Real.log (R0 k R T) := by
    have := mul_nonneg hbpos.le hLR0nn; linarith
  have hle2 : 1 + bParam k R * Real.log (R0 k R T) ≤ 2 * (k : ℝ) ^ ((1 : ℝ) / 8) := by
    linarith [hbU, hk18_ge1]
  have hUb : Real.log (1 + bParam k R * Real.log (R0 k R T))
      ≤ Real.log 2 + (1 / 8) * Real.log k := by
    have hmono := Real.log_le_log harg_pos hle2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hkpos] at hmono
    linarith [hmono]
  -- ==== B1 ≤ (13/25)·Q·log k ====
  have hsharpB := B1_upper_sharp k R W T hW hk hR hT1 hX
  have hstepB : 4 * (Nat.totient W / W : ℝ) * (bParam k R)⁻¹
        * Real.log (1 + bParam k R * Real.log (R0 k R T))
      ≤ 4 * (Nat.totient W / W : ℝ) * (bParam k R)⁻¹
        * (Real.log 2 + (1 / 8) * Real.log k) :=
    mul_le_mul_of_nonneg_left hUb (mul_nonneg (mul_nonneg (by norm_num) hφW0) hbinv0)
  have hlt : 4 * Real.log 2 ≤ (1 / 100) * Real.log k := by
    linarith [Real.log_two_lt_d9, hlogk]
  have hlog2 : 4 * ((Nat.totient W / W : ℝ) * (bParam k R)⁻¹) * Real.log 2
      ≤ (1 / 100) * ((Nat.totient W / W : ℝ) * (bParam k R)⁻¹) * Real.log k := by
    nlinarith [mul_le_mul_of_nonneg_left hlt hQ0]
  have hB1 : B1 k R W T
      ≤ (13 / 25) * ((Nat.totient W / W : ℝ) * (bParam k R)⁻¹) * Real.log k := by
    nlinarith [hsharpB, hstepB, hlog2, hEA]
  -- ==== A1 ≥ (79/100)·Q ====
  have hsharpA := A1_lower_sharp k R W T hW hk hR hT1 hX
  have hdenpos : 0 < 1 + bParam k R * Real.log (R0 k R T - 1) := by linarith [hb4]
  have hVlo : (4 / 5 : ℝ) ≤ 1 - (1 + bParam k R * Real.log (R0 k R T - 1))⁻¹ := by
    have hcancel : (1 + bParam k R * Real.log (R0 k R T - 1))
        * (1 + bParam k R * Real.log (R0 k R T - 1))⁻¹ = 1 := mul_inv_cancel₀ hdenpos.ne'
    have hinv0 : 0 ≤ (1 + bParam k R * Real.log (R0 k R T - 1))⁻¹ := inv_nonneg.mpr hdenpos.le
    nlinarith [hcancel, hinv0,
      mul_nonneg (show (0 : ℝ) ≤ (1 + bParam k R * Real.log (R0 k R T - 1)) - 5 by
        linarith [hb4]) hinv0]
  have hstepA : (Nat.totient W / W : ℝ) * (bParam k R)⁻¹ * (4 / 5)
      ≤ (Nat.totient W / W : ℝ) * (bParam k R)⁻¹
        * (1 - (1 + bParam k R * Real.log (R0 k R T - 1))⁻¹) :=
    mul_le_mul_of_nonneg_left hVlo hQ0
  have hA1lo : (79 / 100) * ((Nat.totient W / W : ℝ) * (bParam k R)⁻¹) ≤ A1 k R W T := by
    nlinarith [hsharpA, hstepA, hEB]
  -- ==== combine ====
  -- Abstract the heavy sums `A1`/`B1`/`A1_1` (and `Q = φW·b⁻¹`, `L = log k`) to
  -- opaque reals so the final linear arithmetic never unfolds their definitions.
  have hsplit := A1_1_upper_split k R W T hk hR
  set Q := (Nat.totient W / W : ℝ) * (bParam k R)⁻¹ with hQdef
  set L := Real.log k with hLdef
  set a := A1 k R W T with hadef
  set b := B1 k R W T with hbdef
  set a11 := A1_1 k R W T with ha11def
  clear_value Q L a b a11
  -- surviving facts:  hB1 : b ≤ 13/25·Q·L ,  hA1lo : 79/100·Q ≤ a ,
  --                   hsplit : a11 ≤ L⁻¹·(a+b) ,  hQpos : 0<Q ,  hlogk : 300≤L
  have hfac : (0 : ℝ) ≤ (7 / 10) * L - 1 := by linarith only [hlogk]
  have hcomb : a + b ≤ (7 / 10) * (L * a) := by
    have hkey1 : (79 / 100) * Q * ((7 / 10) * L - 1) ≤ a * ((7 / 10) * L - 1) :=
      mul_le_mul_of_nonneg_right hA1lo hfac
    have hkey2 : (0 : ℝ) ≤ Q * ((33 / 1000) * L - 79 / 100) :=
      mul_nonneg hQpos.le (by linarith only [hlogk])
    have e1 : (79 / 100) * Q * ((7 / 10) * L - 1) = (553 / 1000) * (Q * L) - (79 / 100) * Q := by
      ring
    have e2 : a * ((7 / 10) * L - 1) = (7 / 10) * (L * a) - a := by ring
    have e3 : Q * ((33 / 1000) * L - 79 / 100) = (33 / 1000) * (Q * L) - (79 / 100) * Q := by
      ring
    rw [e1, e2] at hkey1
    rw [e3] at hkey2
    linarith only [hkey1, hkey2, hB1]
  have hEq : L⁻¹ * ((7 / 10) * (L * a)) = (7 / 10) * a := by
    rw [show (7 / 10 : ℝ) * (L * a) = L * ((7 / 10) * a) from by ring,
      inv_mul_cancel_left₀ hlogkpos.ne']
  have hstep := mul_le_mul_of_nonneg_left hcomb (inv_nonneg.mpr hlogkpos.le)
  rw [hEq] at hstep
  calc a11 ≤ L⁻¹ * (a + b) := hsplit
    _ ≤ (7 / 10) * a := hstep

/-!
## PORT-BLOCKER — reducing `hEA`/`hEB` to a raw `log R` threshold

The four largeness hypotheses of `A1_1_le_seven_tenths` are all genuine
"`k`/`R` large" statements (never the conclusion `A1_1 ≤ (7/10)A1`).  Three of
them — `hT` (frozen `T`), `hb4` (`b·log(R₀−1) ≥ 4`), `hlogk` (`log k ≥ 300`) —
are already in the cleanest downstream-usable form.

The remaining sub-step, deferred here, is the algebraic reduction of the two
`err ≪ main` hypotheses

    hEA :  errA1 k W ≤ (1/100)·(φW·b⁻¹)·log k
    hEB :  errB1 k W ≤ (1/100)·(φW·b⁻¹)

to a single explicit lower bound on `log R`.  With `b⁻¹ = log R/(k·log k)`,

    (φW·b⁻¹)·log k = φW·log R / k ,     (φW·b⁻¹) = φW·log R/(k·log k) ,

so `hEA`/`hEB` are *equivalent* to

    log R ≥ 100·k·errA1 k W / φW       and      log R ≥ 100·k·log k·errB1 k W / φW ,

i.e. a raw `R ≥ R₁(k,W)` threshold with `errA1 k W`, `errB1 k W` the fixed
`W`-only constants of `TransferSharp`.  Formalizing that equivalence needs the
`b⁻¹`-substitution (`field_simp` over `log R ≠ 0`, `log k ≠ 0`, `k ≠ 0`) plus a
`div_le_iff`/`le_div_iff` massage of each side; it is routine but orthogonal to
the transfer-ratio content, so `hEA`/`hEB` are taken as hypotheses here and the
`R₁` threshold is threaded by the driver.  This is the single narrowest
resisting piece; everything else in `hA11` is proved outright.
-/

end Salt.Maynard
