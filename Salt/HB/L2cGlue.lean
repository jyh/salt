/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cMasterUncond

/-!
# HB-L2c — the downstream instantiation of the master (node HB-L2c, Horn A glue)

`hb_l2c_master_final` (`Salt.HB.L2cMop`) exports the `hb_lemma2` conclusion shape on the
exact identity, conditional on the frozen hypothesis packet

* `hz100 : 100 ^ 16 ≤ z`,
* `hz8   : Lwin x ^ 8 ≤ z`,
* `hzx   : (z : ℝ) ^ 3 ≤ x`,
* `hLz0  : Lwin x ≤ Real.exp (z0 z x)`   (Amendment 5),
* `hcount` (the `ER_Tsw'` `CHI-SIEVE` residual — abstract, not discharged here),

plus the character input `hsq`.  This file shows the packet is dischargeable **at a
concrete downstream witness** and assembles `glue_master`, the master specialised to it.

## The witness (and a freeze-level correction — see FINDING below)

The freeze's §S6/Amendment-5 sketch names `z := q^{1/z0*}` with `z0*` a *constant* and
`x ∈ [q^250, q^500]`, asserting `z0 ≥ 250`-grade so that `hLz0` is "trivially true".
**That is false for large `q`.**  With `z = q^c` (`c` constant) and `x ∈ [q^250,q^500]`,

  `z0 = Lwin x / log z ≈ c⁻¹ · (log x / log q) ∈ [250/c, 500/c]`  — a *bounded* constant,

whereas `Lwin x = log(2x+2) → ∞`.  So `exp (z0 z x)` is bounded while `Lwin x` is
unbounded: `hLz0 : Lwin x ≤ exp (z0 z x)` **fails once `q` is large enough**
(`Lwin x > exp(500/c)`).  Since the Horn-A quantity step needs *arbitrarily large* `q`,
the literal witness cannot be used.

The honest fix is `z = q^{o(1)}` — `z0 z x → ∞` slowly.  Concretely we take

  `zwit x := ⌈exp ((Lwin x) ^ (2/3))⌉`,   so `log (zwit x) ≈ (Lwin x)^{2/3}`,
  hence `z0 (zwit x) x ≈ (Lwin x)^{1/3} → ∞`.

The exponent `2/3 ∈ (1/2, 1)` is forced: `> 1/2` makes the junk line `o(x)` (the
`exp(2z0)·x/z^{1/8}` term decays), `< 1` keeps `hLz0` (needs `log z ≲ Lwin/log Lwin`).
A genuine `q`-power (exponent-of-`q` bounded below) lands in *neither* window.  This is a
`FINDING` on the freeze's downstream spec; the master statement itself is untouched.

The threshold constant `(20 : ℝ)^6 ≤ Lwin x` used below is generous (chosen for clean
`rpow` arithmetic, not optimised); it corresponds to a finite prefix `q < q₀` being
excluded, which the quantity step tolerates (only *infinitely many* `q` are needed).

Single-writer file (`L2cGlue.lean`); imports the landed L2c surface via `Salt.HB.L2cMop`
and touches no other file.  `hsq`/`hcount` remain abstract inputs.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 — the downstream witness and its two-sided bounds -/

/-- **The downstream `z`-witness** `zwit x := ⌈exp ((Lwin x)^{2/3})⌉` — sub-polynomial in
    the modulus (`log (zwit x) ≈ (Lwin x)^{2/3}`), so `z0 (zwit x) x → ∞` and `hLz0` holds
    (see the module FINDING). -/
noncomputable def zwit (x : ℕ) : ℕ := ⌈Real.exp ((Lwin x) ^ ((2 : ℝ) / 3))⌉₊

/-- `exp ((Lwin x)^{2/3}) ≤ zwit x`. -/
lemma zwit_ge (x : ℕ) : Real.exp ((Lwin x) ^ ((2 : ℝ) / 3)) ≤ (zwit x : ℝ) := by
  unfold zwit; exact Nat.le_ceil _

/-- `zwit x < exp ((Lwin x)^{2/3}) + 1`. -/
lemma zwit_lt (x : ℕ) : (zwit x : ℝ) < Real.exp ((Lwin x) ^ ((2 : ℝ) / 3)) + 1 := by
  unfold zwit; exact Nat.ceil_lt_add_one (Real.exp_pos _).le

/-- **The `u`-substitution facts.**  For `Lwin x ≥ 20^6`, writing `u := (Lwin x)^{1/6}`:
    `u ≥ 20`, `u > 0`, `Lwin x = u^6`, `(Lwin x)^{2/3} = u^4`, and `log (Lwin x) ≤ 6u`.
    Reduces every downstream estimate to a polynomial inequality in `u`. -/
lemma glue_ufacts {x : ℕ} (hL : (20 : ℝ) ^ 6 ≤ Lwin x) :
    ∃ u : ℝ, 20 ≤ u ∧ 0 < u ∧ Lwin x = u ^ 6 ∧ (Lwin x) ^ ((2 : ℝ) / 3) = u ^ 4 ∧
      Real.log (Lwin x) ≤ 6 * u := by
  have hLpos : 0 < Lwin x := by
    have h6 : (0 : ℝ) < 20 ^ 6 := by norm_num
    linarith
  refine ⟨(Lwin x) ^ ((1 : ℝ) / 6), ?_, ?_, ?_, ?_, ?_⟩
  · -- 20 ≤ u
    have e20 : ((20 : ℝ) ^ 6) ^ ((1 : ℝ) / 6) = 20 := by
      rw [← Real.rpow_natCast (20 : ℝ) 6, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 20)]
      norm_num
    calc (20 : ℝ) = ((20 : ℝ) ^ 6) ^ ((1 : ℝ) / 6) := e20.symm
      _ ≤ (Lwin x) ^ ((1 : ℝ) / 6) := Real.rpow_le_rpow (by positivity) hL (by norm_num)
  · exact Real.rpow_pos_of_pos hLpos _
  · -- Lwin x = u^6
    rw [← Real.rpow_natCast ((Lwin x) ^ ((1 : ℝ) / 6)) 6, ← Real.rpow_mul hLpos.le]
    norm_num
  · -- (Lwin x)^{2/3} = u^4
    rw [← Real.rpow_natCast ((Lwin x) ^ ((1 : ℝ) / 6)) 4, ← Real.rpow_mul hLpos.le]
    norm_num
  · -- log (Lwin x) ≤ 6u
    have hu6 : Lwin x = ((Lwin x) ^ ((1 : ℝ) / 6)) ^ 6 := by
      rw [← Real.rpow_natCast ((Lwin x) ^ ((1 : ℝ) / 6)) 6, ← Real.rpow_mul hLpos.le]; norm_num
    have hupos : 0 < (Lwin x) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hLpos _
    have hlogle : Real.log ((Lwin x) ^ ((1 : ℝ) / 6)) ≤ (Lwin x) ^ ((1 : ℝ) / 6) - 1 :=
      Real.log_le_sub_one_of_pos hupos
    have hlp : Real.log (Lwin x) = 6 * Real.log ((Lwin x) ^ ((1 : ℝ) / 6)) := by
      conv_lhs => rw [hu6]
      rw [Real.log_pow]; push_cast; ring
    rw [hlp]; nlinarith [hlogle, hupos]

/-! ## §2 — the four packet discharges at `zwit x` -/

/-- **(G1) `hz100` discharge.**  `100^16 ≤ zwit x` for `Lwin x ≥ 20^6`. -/
lemma glue_hz100 {x : ℕ} (hL : (20 : ℝ) ^ 6 ≤ Lwin x) : 100 ^ 16 ≤ zwit x := by
  obtain ⟨u, hu20, hupos, hLu6, hLu4, hlog⟩ := glue_ufacts hL
  have hzge : Real.exp (u ^ 4) ≤ (zwit x : ℝ) := by rw [← hLu4]; exact zwit_ge x
  have hu4 : (160000 : ℝ) ≤ u ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) hu20 4; norm_num at this ⊢; linarith
  have h100 : Real.log 100 ≤ 99 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100); linarith
  have hge : ((100 : ℝ) ^ 16) ≤ (zwit x : ℝ) := by
    have h1 : (100 : ℝ) ^ 16 = Real.exp ((16 : ℕ) * Real.log 100) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [h1]
    refine le_trans (Real.exp_le_exp.mpr ?_) hzge
    push_cast; nlinarith [h100, hu4]
  exact_mod_cast hge

/-- **(G2) `hz8` discharge.**  `Lwin x ^ 8 ≤ zwit x` for `Lwin x ≥ 20^6`.  Key arithmetic:
    `8·log(Lwin x) ≤ (Lwin x)^{2/3} = u^4` since `log(Lwin x) ≤ 6u` and `48u ≤ u^4`. -/
lemma glue_hz8 {x : ℕ} (hL : (20 : ℝ) ^ 6 ≤ Lwin x) : Lwin x ^ 8 ≤ (zwit x : ℝ) := by
  obtain ⟨u, hu20, hupos, hLu6, hLu4, hlog⟩ := glue_ufacts hL
  have hLpos : 0 < Lwin x := by
    have h6 : (0 : ℝ) < 20 ^ 6 := by norm_num
    linarith
  have hzge : Real.exp (u ^ 4) ≤ (zwit x : ℝ) := by rw [← hLu4]; exact zwit_ge x
  have hu3 : (8000 : ℝ) ≤ u ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) hu20 3; norm_num at this ⊢; linarith
  have h1 : Lwin x ^ 8 = Real.exp ((8 : ℕ) * Real.log (Lwin x)) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hLpos 8)]
  rw [h1]
  refine le_trans (Real.exp_le_exp.mpr ?_) hzge
  push_cast
  -- 8 * log L ≤ u^4 ; log L ≤ 6u ; 48u ≤ u^3·u = u^4
  nlinarith [hlog, hu20, hupos, hu3, mul_le_mul_of_nonneg_right hu3 hupos.le]

/-- **(G3) `hzx` discharge.**  `(zwit x : ℝ)^3 ≤ x` for `Lwin x ≥ 20^6`.  Uses the identity
    `exp (Lwin x) = 2x+2` and `z ≤ 2·exp(u^4)`, so `z^3 ≤ 8 exp(3u^4) ≤ x` (as
    `18 exp(3u^4) ≤ exp(u^6) = 2x+2`, i.e. `log 18 + 3u^4 ≤ u^6`). -/
lemma glue_hzx {x : ℕ} (hL : (20 : ℝ) ^ 6 ≤ Lwin x) : (zwit x : ℝ) ^ 3 ≤ x := by
  obtain ⟨u, hu20, hupos, hLu6, hLu4, hlog⟩ := glue_ufacts hL
  have hexpL : Real.exp (Lwin x) = 2 * (x : ℝ) + 2 := by
    rw [Lwin, Real.exp_log (by positivity)]
  have hzlt : (zwit x : ℝ) < Real.exp (u ^ 4) + 1 := by rw [← hLu4]; exact zwit_lt x
  have hZ1 : (1 : ℝ) ≤ Real.exp (u ^ 4) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
  have hzle : (zwit x : ℝ) ≤ 2 * Real.exp (u ^ 4) := by linarith
  have hz0 : (0 : ℝ) ≤ (zwit x : ℝ) := by positivity
  have hcube : (zwit x : ℝ) ^ 3 ≤ (2 * Real.exp (u ^ 4)) ^ 3 := pow_le_pow_left₀ hz0 hzle 3
  have hcube' : (2 * Real.exp (u ^ 4)) ^ 3 = 8 * Real.exp (3 * u ^ 4) := by
    rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  -- 18 exp(3u^4) ≤ exp(u^6)
  have hu4pos : (0 : ℝ) < u ^ 4 := by positivity
  have hlog18 : Real.log 18 ≤ 18 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 18); linarith
  have h18 : (18 : ℝ) * Real.exp (3 * u ^ 4) ≤ Real.exp (u ^ 6) := by
    have hle : Real.exp (Real.log 18 + 3 * u ^ 4) ≤ Real.exp (u ^ 6) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hlog18, hu20, hupos, pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 20) hu20 4,
        pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 20) hu20 2]
    rwa [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 18)] at hle
  have hexp6 : Real.exp (u ^ 6) = 2 * (x : ℝ) + 2 := by rw [← hLu6, hexpL]
  have hkey : 8 * Real.exp (3 * u ^ 4) ≤ (x : ℝ) := by
    have he1 : (1 : ℝ) ≤ Real.exp (3 * u ^ 4) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
    rw [hexp6] at h18; linarith
  calc (zwit x : ℝ) ^ 3 ≤ (2 * Real.exp (u ^ 4)) ^ 3 := hcube
    _ = 8 * Real.exp (3 * u ^ 4) := hcube'
    _ ≤ (x : ℝ) := hkey

/-- **(G4) `hLz0` discharge.**  `Lwin x ≤ exp (z0 (zwit x) x)` for `Lwin x ≥ 20^6`.  This
    is the packet hypothesis the literal `q`-power witness FAILS (module FINDING): at
    `zwit x` we have `z0 = Lwin x / log(zwit x) ≥ log(Lwin x)` (since
    `log(Lwin x)·log(zwit x) ≤ 6u·(u^4+log2) ≤ u^6 = Lwin x`), hence `exp(z0) ≥ Lwin x`. -/
lemma glue_hLz0 {x : ℕ} (hL : (20 : ℝ) ^ 6 ≤ Lwin x) :
    Lwin x ≤ Real.exp (z0 (zwit x) x) := by
  obtain ⟨u, hu20, hupos, hLu6, hLu4, hlog⟩ := glue_ufacts hL
  have hLpos : 0 < Lwin x := by
    have h6 : (0 : ℝ) < 20 ^ 6 := by norm_num
    linarith
  have hzge : Real.exp (u ^ 4) ≤ (zwit x : ℝ) := by rw [← hLu4]; exact zwit_ge x
  have hzlt : (zwit x : ℝ) < Real.exp (u ^ 4) + 1 := by rw [← hLu4]; exact zwit_lt x
  have hZ1 : (1 : ℝ) ≤ Real.exp (u ^ 4) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
  have hzpos : (0 : ℝ) < (zwit x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hzge
  have hlogzge : u ^ 4 ≤ Real.log (zwit x) := by
    rw [← Real.log_exp (u ^ 4)]; exact Real.log_le_log (Real.exp_pos _) hzge
  have hlogzpos : 0 < Real.log (zwit x) := lt_of_lt_of_le (by positivity) hlogzge
  have hlogzle : Real.log (zwit x) ≤ u ^ 4 + Real.log 2 := by
    have h2z : (zwit x : ℝ) ≤ 2 * Real.exp (u ^ 4) := by linarith
    calc Real.log (zwit x) ≤ Real.log (2 * Real.exp (u ^ 4)) := Real.log_le_log hzpos h2z
      _ = Real.log 2 + u ^ 4 := by
          rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
      _ = u ^ 4 + Real.log 2 := by ring
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have key : Real.log (Lwin x) ≤ z0 (zwit x) x := by
    rw [z0, le_div_iff₀ hlogzpos]
    have hmul : Real.log (Lwin x) * Real.log (zwit x) ≤ 6 * u * (u ^ 4 + Real.log 2) :=
      mul_le_mul hlog hlogzle hlogzpos.le (by positivity)
    calc Real.log (Lwin x) * Real.log (zwit x)
        ≤ 6 * u * (u ^ 4 + Real.log 2) := hmul
      _ ≤ Lwin x := by
          rw [hLu6]
          nlinarith [hu20, hupos, hlog2, pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 20) hu20 5,
            pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 20) hu20 6]
  calc Lwin x = Real.exp (Real.log (Lwin x)) := (Real.exp_log hLpos).symm
    _ ≤ Real.exp (z0 (zwit x) x) := Real.exp_le_exp.mpr key

/-- **The packet provider.**  All four frozen packet hypotheses discharged at `zwit x` from
    the single scale hypothesis `Lwin x ≥ 20^6`.  (`hsq` and `hcount` stay abstract.) -/
lemma glue_packet {x : ℕ} (hL : (20 : ℝ) ^ 6 ≤ Lwin x) :
    100 ^ 16 ≤ zwit x ∧ Lwin x ^ 8 ≤ (zwit x : ℝ) ∧ (zwit x : ℝ) ^ 3 ≤ x ∧
      Lwin x ≤ Real.exp (z0 (zwit x) x) :=
  ⟨glue_hz100 hL, glue_hz8 hL, glue_hzx hL, glue_hLz0 hL⟩

/-! ## §3 — (G5) the junk record: the master's junk line is `o(x)`

At `zwit x`, `z0 → ∞` slowly, so the freeze's target "junk `≤ x/q^c`" for a *fixed* `c > 0`
is unreachable (the `exp(2z0)` factor grows super-polynomially in `q`); but the junk line
is still `o(x)` — `exp(2z0)·x/z^{1/8}` decays because `z^{1/8} = exp((Lwin)^{2/3}/8)` beats
`exp(2z0) = exp((Lwin)^{2/3}·o(1))`.  We record the clean subordinate bound `junk ≤ x`. -/

/-- **(G5) the junk-line record.**  The master's third (junk) summand at `zwit x` is
    `≤ x` — it does not dominate the trivial scale (and is in fact `o(x)`; the coarse `≤ x`
    already exhibits its subordinacy).  This is the shape the HB-ENGINE campaign absorbs
    into the twin-count error term. -/
lemma glue_junk_le {x : ℕ} (hL : (20 : ℝ) ^ 6 ≤ Lwin x) :
    L2cCmain * Real.exp (2 * z0 (zwit x) x)
        * ((x : ℝ) / (zwit x : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3
      ≤ (x : ℝ) := by
  obtain ⟨u, hu20, hupos, hLu6, hLu4, hlog⟩ := glue_ufacts hL
  have hexpL : Real.exp (Lwin x) = 2 * (x : ℝ) + 2 := by rw [Lwin, Real.exp_log (by positivity)]
  have hexp6 : Real.exp (u ^ 6) = 2 * (x : ℝ) + 2 := by rw [← hLu6, hexpL]
  have hzge : Real.exp (u ^ 4) ≤ (zwit x : ℝ) := by rw [← hLu4]; exact zwit_ge x
  have hzpos : (0 : ℝ) < (zwit x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hzge
  have hlogzge : u ^ 4 ≤ Real.log (zwit x) := by
    rw [← Real.log_exp (u ^ 4)]; exact Real.log_le_log (Real.exp_pos _) hzge
  have hlogzpos : 0 < Real.log (zwit x) := lt_of_lt_of_le (by positivity) hlogzge
  have hu2 : (400 : ℝ) ≤ u ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) hu20 2; norm_num at this ⊢; linarith
  -- z0 ≤ u^2, so exp(2 z0) ≤ exp(2 u^2)
  have hz0le : z0 (zwit x) x ≤ u ^ 2 := by
    rw [z0, hLu6, div_le_iff₀ hlogzpos]
    calc u ^ 6 = u ^ 2 * u ^ 4 := by ring
      _ ≤ u ^ 2 * Real.log (zwit x) := mul_le_mul_of_nonneg_left hlogzge (by positivity)
  have hexp2z0 : Real.exp (2 * z0 (zwit x) x) ≤ Real.exp (2 * u ^ 2) :=
    Real.exp_le_exp.mpr (by linarith [hz0le])
  have hL3 : Lwin x ^ 3 = u ^ 18 := by rw [hLu6]; ring
  -- x is large: exp(5u^4/4) ≤ x
  have hEge1 : (1 : ℝ) ≤ Real.exp (10 * (u ^ 4 / 8)) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
  have h4E : 4 * Real.exp (10 * (u ^ 4 / 8)) ≤ Real.exp (u ^ 6) := by
    have hle : Real.exp (Real.log 4 + 10 * (u ^ 4 / 8)) ≤ Real.exp (u ^ 6) := by
      refine Real.exp_le_exp.mpr ?_
      have hlog4 : Real.log 4 ≤ 4 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
      have hp4 : (400 : ℝ) * u ^ 4 ≤ u ^ 2 * u ^ 4 := mul_le_mul_of_nonneg_right hu2 (by positivity)
      nlinarith [hlog4, hu2, hupos, hp4]
    rwa [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)] at hle
  have hxge : Real.exp (10 * (u ^ 4 / 8)) ≤ (x : ℝ) := by
    rw [hexp6] at h4E; nlinarith [h4E, hEge1]
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hxge
  -- roots: exp(u^4/8) ≤ z^{1/8} and ≤ x^{1/10}
  have hz18 : Real.exp (u ^ 4 / 8) ≤ (zwit x : ℝ) ^ (1 / 8 : ℝ) := by
    have h := Real.rpow_le_rpow (Real.exp_pos (u ^ 4)).le hzge (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rwa [show (Real.exp (u ^ 4)) ^ (1 / 8 : ℝ) = Real.exp (u ^ 4 / 8) from by
      rw [← Real.exp_mul]; ring_nf] at h
  have hx110 : Real.exp (u ^ 4 / 8) ≤ (x : ℝ) ^ (1 / 10 : ℝ) := by
    have h := Real.rpow_le_rpow (Real.exp_pos _).le hxge (by norm_num : (0 : ℝ) ≤ 1 / 10)
    rwa [← Real.exp_mul, show (10 * (u ^ 4 / 8)) * (1 / 10 : ℝ) = u ^ 4 / 8 from by ring] at h
  -- the two junk sub-terms are each ≤ x / exp(u^4/8)
  have hsum : (x : ℝ) / (zwit x : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10)
      ≤ 2 * ((x : ℝ) / Real.exp (u ^ 4 / 8)) := by
    have hA : (x : ℝ) / (zwit x : ℝ) ^ (1 / 8 : ℝ) ≤ (x : ℝ) / Real.exp (u ^ 4 / 8) :=
      div_le_div_of_nonneg_left hxpos.le (Real.exp_pos _) hz18
    have hB : (x : ℝ) ^ ((9 : ℝ) / 10) ≤ (x : ℝ) / Real.exp (u ^ 4 / 8) := by
      rw [le_div_iff₀ (Real.exp_pos _)]
      calc (x : ℝ) ^ ((9 : ℝ) / 10) * Real.exp (u ^ 4 / 8)
          ≤ (x : ℝ) ^ ((9 : ℝ) / 10) * (x : ℝ) ^ (1 / 10 : ℝ) :=
            mul_le_mul_of_nonneg_left hx110 (by positivity)
        _ = (x : ℝ) := by rw [← Real.rpow_add hxpos]; norm_num
    linarith
  -- the scalar bound: 2^32 · u^18 · exp(2u^2 − u^4/8) ≤ 1
  have hscalar : (2 : ℝ) ^ 32 * u ^ 18 * Real.exp (2 * u ^ 2 - u ^ 4 / 8) ≤ 1 := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hlogu : Real.log u ≤ u := by
      have := Real.log_le_sub_one_of_pos hupos; linarith
    have hlog232 : Real.log ((2 : ℝ) ^ 32) ≤ 32 := by
      rw [Real.log_pow]; push_cast; nlinarith [hlog2]
    have h1pos : (0 : ℝ) < (2 : ℝ) ^ 32 * u ^ 18 := by positivity
    have h1ne : ((2 : ℝ) ^ 32 * u ^ 18) ≠ 0 := h1pos.ne'
    have h3ne : ((2 : ℝ) ^ 32) ≠ 0 := by norm_num
    have h4ne : (u ^ 18) ≠ 0 := (show (0 : ℝ) < u ^ 18 by positivity).ne'
    have hargpos : (0 : ℝ) < (2 : ℝ) ^ 32 * u ^ 18 * Real.exp (2 * u ^ 2 - u ^ 4 / 8) := by
      positivity
    have hlu : Real.log (u ^ 18) = 18 * Real.log u := by rw [Real.log_pow]; push_cast; ring
    have hlogarg : Real.log ((2 : ℝ) ^ 32 * u ^ 18 * Real.exp (2 * u ^ 2 - u ^ 4 / 8)) ≤ 0 := by
      rw [Real.log_mul h1ne (Real.exp_pos _).ne', Real.log_mul h3ne h4ne, Real.log_exp, hlu]
      have hkey4 : (32 : ℝ) + 18 * u + 2 * u ^ 2 ≤ u ^ 4 / 8 := by
        have hp2 : (400 : ℝ) * u ^ 2 ≤ u ^ 2 * u ^ 2 :=
          mul_le_mul_of_nonneg_right hu2 (by positivity)
        have hp20 : (0 : ℝ) ≤ (u - 20) * u := mul_nonneg (by linarith [hu20]) hupos.le
        nlinarith [hu20, hu2, hupos, hp2, hp20]
      set E := Real.log ((2 : ℝ) ^ 32)
      set Lu := Real.log u
      linarith [hlog232, hlogu, hkey4]
    calc (2 : ℝ) ^ 32 * u ^ 18 * Real.exp (2 * u ^ 2 - u ^ 4 / 8)
        = Real.exp (Real.log ((2 : ℝ) ^ 32 * u ^ 18 * Real.exp (2 * u ^ 2 - u ^ 4 / 8))) :=
          (Real.exp_log hargpos).symm
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hlogarg
      _ = 1 := Real.exp_zero
  -- assemble
  rw [L2cCmain]
  calc (2 : ℝ) ^ 31 * Real.exp (2 * z0 (zwit x) x)
          * ((x : ℝ) / (zwit x : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3
      ≤ (2 : ℝ) ^ 31 * Real.exp (2 * u ^ 2)
          * (2 * ((x : ℝ) / Real.exp (u ^ 4 / 8))) * u ^ 18 := by
        rw [hL3]; gcongr
    _ = ((2 : ℝ) ^ 32 * u ^ 18 * Real.exp (2 * u ^ 2 - u ^ 4 / 8)) * (x : ℝ) := by
        rw [Real.exp_sub]; field_simp
    _ ≤ 1 * (x : ℝ) := mul_le_mul_of_nonneg_right hscalar hxpos.le
    _ = (x : ℝ) := one_mul _

/-- **The scale bridge.**  The single hypothesis `Lwin x ≥ 20^6` used throughout follows
    from `x` past the explicit finite threshold `exp(20^6) ≤ 2x+2`.  Downstream (`x ≥ q^250`)
    this holds for every `q ≥ q₀` with `q₀ := ⌈exp(20^6 / 250)⌉` — a finite prefix `q < q₀`
    excluded, which the Horn-A *quantity* step tolerates (only infinitely many `q` are
    needed).  (The threshold is generous, chosen for clean arithmetic, not optimised.) -/
lemma glue_scale {x : ℕ} (hx : Real.exp ((20 : ℝ) ^ 6) ≤ 2 * (x : ℝ) + 2) :
    (20 : ℝ) ^ 6 ≤ Lwin x := by
  rw [Lwin]
  calc (20 : ℝ) ^ 6 = Real.log (Real.exp ((20 : ℝ) ^ 6)) := (Real.log_exp _).symm
    _ ≤ Real.log (2 * (x : ℝ) + 2) := Real.log_le_log (Real.exp_pos _) hx

/-! ## §4 — the assembled master at the witness -/

open Classical in
/-- **`glue_master` — the L2c master specialised to the downstream witness `zwit x`.**
    A4 (ratified 2026-07-20): now consumes `hb_l2c_master_unconditional` — the packet
    (`hz100`/`hz8`/`hzx`) is discharged by G1–G3 from the single scale hypothesis
    `Lwin x ≥ 20^6`, and **no residual remains**: `hcount` and `hLz0` are gone (the
    CHI-SIEVE freeze proved both unnecessary; see `Salt/HB/L2cMasterUncond.lean`).
    Only the character input `hsq` remains.  This is the exact `hb_lemma2`-shape
    conclusion the Horn-A composition (WP1∘WP2, `S(3)` main term) consumes. -/
theorem glue_master (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {x : ℕ}
    (hL : (20 : ℝ) ^ 6 ≤ Lwin x) :
    S2 χ (l2cWindow χ (zwit x) x) - S1 (l2cWindow χ (zwit x) x)
      ≤ L2cCmain * ((x : ℝ) / z0 (zwit x) x)
        + L2cCmain * ((x : ℝ) / Real.log x) * Real.exp (5 * z0 (zwit x) x)
            * PretenseSum χ (2 * x + 2)
        + L2cCmain * Real.exp (2 * z0 (zwit x) x)
            * ((x : ℝ) / (zwit x : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10))
            * Lwin x ^ 3 :=
  hb_l2c_master_unconditional χ hsq (glue_hz100 hL) (glue_hz8 hL) (glue_hzx hL)

end Salt.HB
