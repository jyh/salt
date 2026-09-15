/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TierSBridge
import Salt.MR.StrideGradeReceipt12b
import Mathlib

/-!
# ⟦TIER S — THE LADDER⟧ S-3's BAND, THROUGH THE ENTROPY-ARROW BRIDGE, TO D10's INFINITE SCALE SET
(`TierSLadder`)

**LANDED 2026-09-14 23:1x: Pl AND L PROVED by ONE Opus executor on the helm's word after math's
non-author pass (NO KILL), each statement byte- and type-identical to freeze v1.1 under its
three-arm guard; N, Sc, K, and — transcribed at v1.1 — math's `hah9` leaf and the CROWN TWIN P6
were proved at the freeze.  7 names, 7 landed.  NO LANDED FILE TOUCHED.  HONEST LABEL, FIRST
LINE: NO NEW UNCONDITIONAL THEOREM IS CLAIMED HERE, AND NOTHING BEARS ON TWIN PRIMES — at a fixed
stride `P ≤ 2310` the consumer D10 is a SECOND PROOF of a terminal the crown route already lands
(QUEUE, the Tier S block).  THE EVIDENCE FOR THAT LABEL IS IN THIS FILE (the refuter's M11(a)): the landed
unconditional statements of K's set are at `P = primorial z` only, so §6's crown twin
`twinLogWeight_support_infinite_of_crown_g12b` states the SAME set from the crown road at every
`0 < P ≤ 2310` — after the wave, K and it are the two roads meeting at one theorem.**

The link the entropy-arrow bridge (`TierSBridge.lean`) left NAMED: B gives, per `A₀`, ONE band
`[x₀, exp(31·Hhi₀/ε)/a]` on which no admissible class fails, and K2 reads it into D12 and out as
`AffFullRangeAt a b h ε (ε·log ω₀ + log x₀ + 1) N` at every `N` under the roof — a band-DEPENDENT
additive constant on a FINITE interval.  D10 (`TwinParityAtomClasses.lean:635`,
`twinLogWeight_support_infinite_of_affFullRange`) wants ONE `(ε, A)` over an INFINITE set of scales
`S`, at every admissible class, at the scale `(N − r)/P`.  The ladder is exactly the arithmetic on
EXPORTED terms the bridge's freeze §8 named: (N) the `(2ε, 1)`-normalisation at one scale — the
band constant is absorbed once `ε·log ω₀ + log x₀ ≤ ε·log M`; (Pl) the PLACEMENT — that threshold
sits below the band's roof with room for the class rounding, which is where the design floor
`Hhi₀ ≥ flatDesignBase 162 ≥ 2^600` is spent (S-3 freeze §5: on the structure floor `4·10⁶` alone
`P = 2310` FAILS, crossing near `3.9·10⁷`); (Sc) the class-scale placement at `N := P·K` — every
residue `r < P` lands at `(N − r)/P ∈ {K − 1, K}` (S-4's K6, author-owned, now stated and proved);
and (L) the ladder itself: one band per `A₀ := M`, the scale `N(M) := P·⌊roof(M)⌋₊`, and
`S := range N`, infinite because the roof is unbounded along `A₀` (S-4's K2′, extended to
`N(M) ≥ M`).  K is the consumer control: L feeds D10 in one `exact`.

What this does NOT buy: `P ≤ 2310` is the bridge's cap (the composition's `a ≤ 2310`, council
2026-09-13 A② clause 2), so at `P = primorial z` this is `z ≤ 12`; the `z = 13` grade question is
nobody's here.  The values exported — `ε = 1/(500·P)`, `A = 1` — are the stride lane's own
(D10's docstring: the pin `1/(1000·P)` doubled, `500×` under the `ε < 1/P` budget).
-/

noncomputable section

open scoped BigOperators
open Salt.Entropy.Chowla
open Salt.TwinBar

namespace Salt.MR

/-! ## §0 — N: the `(2ε, 1)`-normalisation at one scale (PROVED; reads no `sorry`) -/

/-- **⟦LADDER N⟧ (class A, PROVED) — THE BAND CONSTANT IS ABSORBED INTO A DOUBLED SLOPE.**  From
`AffFullRangeAt a b h ε A M` and `A ≤ ε·log M + 1`, `AffFullRangeAt a b h (2ε) 1 M`.  No sign
condition on `ε` is needed: the hypothesis on `A` carries it. -/
theorem affFullRangeAt_normalise (a b h : ℕ) (ε A : ℝ) (M : ℕ)
    (hAM : A ≤ ε * Real.log (M : ℝ) + 1) (hfr : AffFullRangeAt a b h ε A M) :
    AffFullRangeAt a b h (2 * ε) 1 M := by
  unfold AffFullRangeAt at hfr ⊢
  have h2 : 2 * ε * Real.log (M : ℝ) = ε * Real.log (M : ℝ) + ε * Real.log (M : ℝ) := by ring
  linarith

/-! ## §1 — Sc: the class-scale placement (PROVED; S-4's K6 as a kernel fact) -/

/-- **⟦LADDER Sc⟧ (class A, PROVED) — AT `N := P·K` EVERY RESIDUE LANDS IN `{K − 1, K}`.**
For `r < P`: `K − 1 ≤ (P·K − r)/P ≤ K` (ℕ-subtraction and ℕ-division, D10's own scale form
`(N − r)/P`; at `K = 0` both sides are `0`).  Driven at `P = 2310`, all `r < P`,
`K ∈ {1, 2, 10⁶}` in `drive_ladder_v1.py`. -/
theorem class_scale_in_band (P K r : ℕ) (hP : 0 < P) (hr : r < P) :
    K - 1 ≤ (P * K - r) / P ∧ (P * K - r) / P ≤ K := by
  refine ⟨?_, Nat.div_le_of_le_mul (Nat.sub_le _ _)⟩
  rw [Nat.le_div_iff_mul_le hP]
  calc (K - 1) * P = P * K - P := by rw [Nat.sub_mul, one_mul, mul_comm]
    _ ≤ P * K - r := Nat.sub_le_sub_left hr.le _

/-! ## §2 — the numeric leaf `log (P·2) ≤ 9` at `P ≤ 2310` (PROVED; math's, transcribed at v1.1) -/

/-- **⟦LADDER hah9⟧ (class A, PROVED) — `log (P·2) ≤ 9` AT EVERY `0 < P ≤ 2310`.**  The move of
`hah9_of_primorial_le_2310` (`StrideGradeReceipt12b.lean:71`) with `primorial z` replaced by `P`: it
reads only `P ≤ 2310`.  L's route (step 1) and the crown twin (§6) both open with it.  ⚠ LABEL:
math's construction (the refuter's probe `hah9_of_le_2310` on freeze v1), transcribed by h2c at
v1.1. -/
theorem hah9_of_le_2310 (P : ℕ) (hP : 0 < P) (hP2310 : P ≤ 2310) :
    Real.log ((P * 2 : ℕ) : ℝ) ≤ 9 := by
  have hle : P * 2 ≤ 4620 := by omega
  have hR : ((P * 2 : ℕ) : ℝ) ≤ 4620 := by exact_mod_cast hle
  have hR0 : (0 : ℝ) < ((P * 2 : ℕ) : ℝ) := by
    have hpos : 0 < P * 2 := by omega
    exact_mod_cast hpos
  have he9 : (4620 : ℝ) ≤ Real.exp 9 := by
    have h3 : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h5 : (2.7182818283 : ℝ) ^ (9 : ℕ) ≤ (Real.exp 1) ^ (9 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h4.le 9
    have h6 : (4620 : ℝ) ≤ (2.7182818283 : ℝ) ^ (9 : ℕ) := by norm_num
    rw [h3]; linarith
  calc Real.log ((P * 2 : ℕ) : ℝ) ≤ Real.log (Real.exp 9) :=
      Real.log_le_log hR0 (by linarith)
    _ = 9 := Real.log_exp 9

/-! ## §3 — Pl: THE PLACEMENT (PROVED in the wave, 2026-09-14) -/

/-- **⟦LADDER Pl⟧ (class C, PROVED in the wave) — ABOVE THE DESIGN FLOOR THE NORMALISATION
THRESHOLD SITS BELOW THE ROOF, WITH ROOM FOR THE CLASS ROUNDING.**  At the pin `ε = 1/(500·(a·2))` and any
`Hhi₀ ≥ 2^600` (`flatDesignBase_ge_pow600` at `A ≥ 162`, which B exports):
`ε·xTightCeil ε Hhi₀ + xTightCeilArm ε Hhi₀ + ε·log a + ε·log 3 ≤ 31·Hhi₀`.  Divided by `ε` this
is `xTightCeil + xTightCeilArm/ε ≤ 31·Hhi₀/ε − log a − log 3`: the left side bounds
`(ε·log ω₀ + log x₀)/ε`, the threshold above which the band constant is absorbed (N); the right
side is `log (roof/3)`, and `⌊roof⌋₊ − 1 ≥ roof/3` once `roof ≥ 3`.  The `log 3` is the rounding
(Sc); the `log a` is the stride in D10's scale.  S-3 freeze §5 drove the version without the
rounding: at the structure floor `4·10⁶` the instance `P = 2310` FAILS (margin `0.118`), the
crossing is near `3.9·10⁷`, and at `2^600` the margin is astronomical — `drive_ladder_v1.py`. -/
theorem ladder_placement (a : ℕ) (ha : 0 < a) (ha2310 : a ≤ 2310) (ε : ℚ)
    (hε : ε = 1 / (500 * ((a * 2 : ℕ) : ℚ))) (Hhi₀ : ℕ) (hH : 2 ^ 600 ≤ Hhi₀) :
    (ε : ℝ) * xTightCeil ε Hhi₀ + xTightCeilArm ε Hhi₀
      + (ε : ℝ) * Real.log (a : ℝ) + (ε : ℝ) * Real.log 3 ≤ 31 * ((Hhi₀ : ℕ) : ℝ) := by
  -- §a  the stride and the pin `ε = 1/(1000·a)`
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have haR0 : (a : ℝ) ≠ 0 := ne_of_gt haR
  have ha1R : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha2310R : (a : ℝ) ≤ 2310 := by exact_mod_cast ha2310
  have hXQ : (0 : ℚ) < 500 * ((a * 2 : ℕ) : ℚ) := by
    have h0 : 0 < a * 2 := by omega
    have h1 : (0 : ℚ) < ((a * 2 : ℕ) : ℚ) := by exact_mod_cast h0
    linarith
  have heQ : (0 : ℚ) < ε := by rw [hε]; exact div_pos one_pos hXQ
  have he : (ε : ℝ) = 1 / (1000 * (a : ℝ)) := by
    rw [hε]; push_cast
    rw [show (500 : ℝ) * ((a : ℝ) * 2) = 1000 * (a : ℝ) from by ring]
  have hepos : (0 : ℝ) < (ε : ℝ) := by rw [he]; positivity
  have he1000 : (ε : ℝ) ≤ 1 / 1000 := by
    rw [he]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h30ub : 30 / (ε : ℝ) ≤ 69300000 := by
    rw [div_le_iff₀ hepos, he, mul_one_div,
      le_div_iff₀ (by linarith : (0 : ℝ) < 1000 * (a : ℝ))]
    linarith
  -- §b  the design floor as `2^64 ≤ Hhi₀`; `2^600` then leaves the context entirely
  have h64N : (18446744073709551616 : ℕ) ≤ Hhi₀ := by
    refine le_trans ?_ hH
    set_option exponentiation.threshold 700 in norm_num
  clear hH
  have hH4 : 4000000 ≤ Hhi₀ := le_trans (by norm_num) h64N
  have hH64 : (18446744073709551616 : ℝ) ≤ ((Hhi₀ : ℕ) : ℝ) := by exact_mod_cast h64N
  have hHpos : (0 : ℝ) < ((Hhi₀ : ℕ) : ℝ) := by linarith
  -- §c  `log H` sub-linearly: split at `2^64`, then `log t ≤ t − 1`
  have hlogc : Real.log 18446744073709551616 = 64 * Real.log 2 := by
    rw [show (18446744073709551616 : ℝ) = 2 ^ (64 : ℕ) from by norm_num, Real.log_pow]
    norm_num
  have hlog2ub : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlogH : Real.log ((Hhi₀ : ℕ) : ℝ) ≤ 45 + ((Hhi₀ : ℕ) : ℝ) / 18446744073709551616 := by
    have hqpos : (0 : ℝ) < ((Hhi₀ : ℕ) : ℝ) / 18446744073709551616 :=
      div_pos hHpos (by norm_num)
    have h1 := Real.log_le_sub_one_of_pos hqpos
    rw [Real.log_div hHpos.ne' (by norm_num), hlogc] at h1
    linarith
  have hlogHnn : (0 : ℝ) ≤ Real.log ((Hhi₀ : ℕ) : ℝ) := Real.log_nonneg (by linarith)
  have hcH : (69300000 : ℝ) * (((Hhi₀ : ℕ) : ℝ) / 18446744073709551616)
      ≤ ((Hhi₀ : ℕ) : ℝ) := by
    rw [← mul_div_assoc, div_le_iff₀ (by norm_num : (0 : ℝ) < 18446744073709551616)]
    linarith
  have hLH : 30 / (ε : ℝ) * Real.log ((Hhi₀ : ℕ) : ℝ) ≤ 3118500000 + ((Hhi₀ : ℕ) : ℝ) := by
    have hA : 30 / (ε : ℝ) * Real.log ((Hhi₀ : ℕ) : ℝ)
        ≤ 69300000 * Real.log ((Hhi₀ : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right h30ub hlogHnn
    have hB : (69300000 : ℝ) * Real.log ((Hhi₀ : ℕ) : ℝ)
        ≤ 69300000 * (45 + ((Hhi₀ : ℕ) : ℝ) / 18446744073709551616) :=
      mul_le_mul_of_nonneg_left hlogH (by norm_num)
    linarith
  -- §d  the floor term `2·log (4^n + 1)`, with `n ≤ ε²·H ≤ H/10⁶`
  have hfloorQ : ((⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) : ℚ) ≤ ε ^ 2 * (Hhi₀ : ℚ) :=
    Nat.floor_le (by positivity)
  have hnR : ((⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) : ℝ) ≤ (ε : ℝ) ^ 2 * ((Hhi₀ : ℕ) : ℝ) := by
    exact_mod_cast hfloorQ
  have he2 : (ε : ℝ) ^ 2 ≤ 1 / 1000000 := by nlinarith [hepos, he1000]
  have hnH : ((⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) : ℝ) ≤ ((Hhi₀ : ℕ) : ℝ) / 1000000 := by
    have h1 : (ε : ℝ) ^ 2 * ((Hhi₀ : ℕ) : ℝ) ≤ 1 / 1000000 * ((Hhi₀ : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right he2 hHpos.le
    linarith
  have hnnn : (0 : ℝ) ≤ ((⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpow4 : ((4 ^ ⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) : ℝ)
      = (4 : ℝ) ^ (⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) := by norm_cast
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) from by norm_num, Real.log_pow]; norm_num
  have hlogterm : Real.log (((4 ^ ⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) : ℝ) + 1)
      ≤ Real.log 2 + ((⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) : ℝ) * Real.log 4 := by
    rw [hpow4]
    have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ (⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) := one_le_pow₀ (by norm_num)
    have hle : (4 : ℝ) ^ (⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) + 1
        ≤ 2 * (4 : ℝ) ^ (⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) := by linarith
    have h2 := Real.log_le_log (by positivity) hle
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
  have hL4 : 2 * Real.log (((4 ^ ⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) : ℝ) + 1)
      ≤ 2 + 3 * (((Hhi₀ : ℕ) : ℝ) / 1000000) := by
    have hlog4ub : Real.log 4 ≤ 1.3862943616 := by rw [hlog4]; linarith
    have hp1 : ((⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) : ℝ) * Real.log 4
        ≤ ((⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) : ℝ) * 1.3862943616 :=
      mul_le_mul_of_nonneg_left hlog4ub hnnn
    have hp2 : ((⌊ε ^ 2 * (Hhi₀ : ℚ)⌋₊ : ℕ) : ℝ) * 1.3862943616
        ≤ ((Hhi₀ : ℕ) : ℝ) / 1000000 * 1.3862943616 :=
      mul_le_mul_of_nonneg_right hnH (by norm_num)
    linarith
  -- §e  the two constants: the stride's log (through hah9) and `log 3`
  have hloga : Real.log (a : ℝ) ≤ 9 := by
    have h1 := hah9_of_le_2310 a ha ha2310
    have h2 : (a : ℝ) ≤ ((a * 2 : ℕ) : ℝ) := by push_cast; linarith
    exact le_trans (Real.log_le_log haR h2) h1
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hea : (ε : ℝ) * Real.log (a : ℝ) ≤ 9 / 1000 := by
    have h1 : (ε : ℝ) * Real.log (a : ℝ) ≤ (ε : ℝ) * 9 :=
      mul_le_mul_of_nonneg_left hloga hepos.le
    linarith
  have he3 : (ε : ℝ) * Real.log 3 ≤ 2 / 1000 := by
    have h1 : (ε : ℝ) * Real.log 3 ≤ (ε : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hlog3 hepos.le
    linarith
  -- §f  the two ceilings, bounded, then one linear close
  have hC0 : (0 : ℝ) ≤ xTightCeil ε Hhi₀ := xTightCeil_nonneg ε heQ Hhi₀ hH4
  have hCub : xTightCeil ε Hhi₀ ≤ 3118500020 + 2 * ((Hhi₀ : ℕ) : ℝ) := by
    simp only [xTightCeil]
    linarith
  have heC : (ε : ℝ) * xTightCeil ε Hhi₀ ≤ xTightCeil ε Hhi₀ / 1000 := by
    have h := mul_le_mul_of_nonneg_right he1000 hC0
    linarith
  have hH20 : ((Hhi₀ : ℕ) : ℝ) / 10 ^ 20 ≤ ((Hhi₀ : ℕ) : ℝ) :=
    div_le_self hHpos.le (by norm_num)
  have hArm : xTightCeilArm ε Hhi₀
      = xTightCeil ε Hhi₀ + 18 + Real.log 2 + ((Hhi₀ : ℕ) : ℝ) / 10 ^ 20 := by
    simp only [xTightCeilArm]
  rw [hArm]
  linarith

/-! ## §4 — L: THE LADDER (PROVED in the wave, 2026-09-14) -/

/-- **⟦LADDER L⟧ (class C, PROVED in the wave) — D10's HYPOTHESIS PACKAGE AT EVERY STRIDE
`P ≤ 2310`.**  `ε = 1/(500·P)`, `A = 1`, and an INFINITE `S` such that at every `N ∈ S` and every admissible class
`r`, `AffFullRangeAt P r 2 ε A ((N − r)/P)`.

Route (as fired 2026-09-14; the statement byte- and type-identical to the freeze under its guard):
`hah9 : log (P·2) ≤ 9` from `P ≤ 2310`;
B (`band_not_logChowlaFailsAff_g12b P 2`) at `A₀ := M` for every `M : ℕ`, `choose`d into a band
`(ε_M, A_M, x₀ M, ω₀ M, Hhi₀ M)` with `ε_M = 1/(1000·P)` at every `M`; the roof `R M := exp(31·Hhi₀
M/ε)/P`, `K M := ⌊R M⌋₊`, `N M := P·K M`, `S := Set.range N`.  `S.Infinite` by
`Set.infinite_of_not_bddAbove`: `N M ≥ M`, since `Hhi₀ M ≥ M` (K2′'s chain: `nat_le_flatDesignBase`,
`flatDesignBase_mono`, the v1.1 conjunct) and `exp x ≥ 1 + x`.  At `N M` and `r ∈ admClasses P`:
`r < P` and `Coprime (r+2) P` (`Nat.coprime_mul_iff_left`) give B's class binders; Sc places
`M_r := (N M − r)/P` in `[K − 1, K]`; K2 (`affFullRangeAt_band_of_not_fails`) at `M_r` under the
roof; N with the threshold from Pl (`Hhi₀ M ≥ 2^600` by `flatDesignBase_ge_pow600`); the exported
`ε = 2·ε_M` by `push_cast`. -/
theorem ladder_affFullRange_g12b (P : ℕ) (hP : 0 < P) (hP2310 : P ≤ 2310) :
    ∃ (ε A : ℝ), ε = 1 / (500 * (P : ℝ)) ∧ A = 1 ∧ ∃ S : Set ℕ, S.Infinite ∧
      ∀ N ∈ S, ∀ r ∈ admClasses P, AffFullRangeAt P r 2 ε A ((N - r) / P) := by
  have hah9 := hah9_of_le_2310 P hP hP2310
  -- P2: the rounding in ℕ-subtraction
  have p2 : ∀ (R : ℝ), 3 ≤ R → ∀ Mr : ℕ, ⌊R⌋₊ - 1 ≤ Mr → R / 3 ≤ (Mr : ℝ) := by
    intro R hR Mr hMr
    have h1 : R < (⌊R⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one R
    have hK : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by norm_num; linarith)
    have hcast : ((⌊R⌋₊ - 1 : ℕ) : ℝ) = (⌊R⌋₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hK]; norm_num
    have h2 : ((⌊R⌋₊ - 1 : ℕ) : ℝ) ≤ (Mr : ℝ) := by exact_mod_cast hMr
    linarith
  -- P3: the export cast
  have p3 : 2 * (((1 / (500 * ((P * 2 : ℕ) : ℚ)) : ℚ)) : ℝ) = 1 / (500 * (P : ℝ)) := by
    have hPR : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
    push_cast
    field_simp
  -- P4: B's two ceilings + Pl + a scale above roof/3 ⇒ N's hypothesis
  have p4 : ∀ (ε : ℚ), 0 < ε → ∀ (x₀ ω₀ Hhi₀ Mr : ℕ),
      Real.log ((ω₀ : ℕ) : ℝ) ≤ xTightCeil ε Hhi₀ →
      Real.log ((x₀ : ℕ) : ℝ) ≤ xTightCeilArm ε Hhi₀ →
      (ε : ℝ) * xTightCeil ε Hhi₀ + xTightCeilArm ε Hhi₀
        + (ε : ℝ) * Real.log (P : ℝ) + (ε : ℝ) * Real.log 3 ≤ 31 * ((Hhi₀ : ℕ) : ℝ) →
      Real.exp (31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ)) / (P : ℝ) / 3 ≤ (Mr : ℝ) →
      (ε : ℝ) * Real.log (ω₀ : ℝ) + Real.log (x₀ : ℝ) + 1 ≤ (ε : ℝ) * Real.log (Mr : ℝ) + 1 := by
    intro ε hε0 x₀ ω₀ Hhi₀ Mr c1 c2 hPl hMr
    have hεR : (0 : ℝ) < ε := by exact_mod_cast hε0
    have hPR : (0 : ℝ) < P := by exact_mod_cast hP
    have hEpos : 0 < Real.exp (31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ)) := Real.exp_pos _
    have hpos : 0 < Real.exp (31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ)) / (P : ℝ) / 3 := by positivity
    have hlog := Real.log_le_log hpos hMr
    rw [Real.log_div (div_pos hEpos hPR).ne' (by norm_num), Real.log_div hEpos.ne' hPR.ne',
      Real.log_exp] at hlog
    have hmul : (ε : ℝ) * (31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ)) = 31 * ((Hhi₀ : ℕ) : ℝ) := by
      field_simp
    have hM := mul_le_mul_of_nonneg_left hlog hεR.le
    have hexp : (ε : ℝ) * (31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ) - Real.log (P : ℝ) - Real.log 3)
        = 31 * ((Hhi₀ : ℕ) : ℝ) - (ε : ℝ) * Real.log (P : ℝ) - (ε : ℝ) * Real.log 3 := by
      rw [mul_sub, mul_sub, hmul]
    have hω := mul_le_mul_of_nonneg_left c1 hεR.le
    linarith [hω, hM, c2, hPl, hexp]
  -- P5: the per-scale core — one band per M, exporting M ≤ Hhi₀ AND 4000000 ≤ Hhi₀
  have p5 : ∀ M : ℕ, ∃ Hhi₀ : ℕ, M ≤ Hhi₀ ∧ 4000000 ≤ Hhi₀ ∧ ∃ ε : ℚ, 0 < ε ∧
      ε = 1 / (500 * ((P * 2 : ℕ) : ℚ)) ∧
      ∀ r ∈ admClasses P, ∀ Mr : ℕ,
        Real.exp (31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ)) / (P : ℝ) / 3 ≤ (Mr : ℝ) →
        (Mr : ℝ) ≤ Real.exp (31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ)) / (P : ℝ) →
        AffFullRangeAt P r 2 (1 / (500 * (P : ℝ))) 1 Mr := by
    intro M
    obtain ⟨ε, A, hε, _, heq, h162, hA0A, x₀, ω₀, Hhi₀, hx₀, hω₀, hH4, c1, c2, _c3, hfl, hall⟩ :=
      band_not_logChowlaFailsAff_g12b P 2 hP two_pos hah9 hP2310 (M : ℝ)
    have hMH : M ≤ Hhi₀ := by
      have hM : M ≤ flatDesignBase (M : ℝ) := nat_le_flatDesignBase M (M : ℝ) (by
        have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        have h1 : Real.log (Real.log (M : ℝ)) ≤ Real.log (M : ℝ) :=
          Real.log_le_self (Real.log_natCast_nonneg M)
        have h2 : Real.log (M : ℝ) ≤ (M : ℝ) := Real.log_le_self hMnn
        linarith)
      exact le_trans hM (le_trans (flatDesignBase_mono hA0A) hfl)
    refine ⟨Hhi₀, hMH, hH4, ε, hε, heq, ?_⟩
    intro r hr Mr hlo hhi
    have hr' := hr
    simp only [admClasses, Finset.mem_filter, Finset.mem_range] at hr'
    have hgcd : Nat.gcd (r + 2) P ∣ 2 := gcd_dvd_two_of_coprime hr'.2
    have hPR : (0 : ℝ) < P := by exact_mod_cast hP
    have hMrpos : (0 : ℝ) < (Mr : ℝ) := lt_of_lt_of_le (by positivity) hlo
    have hroof : Real.log ((P * Mr : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ) := by
      have hle : ((P * Mr : ℕ) : ℝ) ≤ Real.exp (31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ)) := by
        have h := (le_div_iff₀ hPR).mp hhi
        push_cast
        linarith [mul_comm (P : ℝ) (Mr : ℝ)]
      have hpos : (0 : ℝ) < ((P * Mr : ℕ) : ℝ) := by push_cast; positivity
      calc Real.log ((P * Mr : ℕ) : ℝ)
          ≤ Real.log (Real.exp (31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ))) := Real.log_le_log hpos hle
        _ = 31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ) := Real.log_exp _
    have hK2 := affFullRangeAt_band_of_not_fails P r 2 hP ε hε x₀ ω₀ Hhi₀ hx₀ hω₀
      (hall r hr'.1 hgcd) Mr hroof
    have hPl := ladder_placement P hP hP2310 ε heq Hhi₀
      (le_trans (flatDesignBase_ge_pow600 h162) hfl)
    have hthr := p4 ε hε x₀ ω₀ Hhi₀ Mr c1 c2 hPl hlo
    have hN := affFullRangeAt_normalise P r 2 (ε : ℝ) _ Mr hthr hK2
    have hcast : 2 * (ε : ℝ) = 1 / (500 * (P : ℝ)) := by rw [heq]; exact p3
    rwa [hcast] at hN
  -- the wrapper: one band per `A₀ := M`, the roof `R M`, the scale `N M := P·⌊R M⌋₊`
  choose Hhi₀ hMH hH4 ε _hε heq hall using p5
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have heR : ∀ M : ℕ, (ε M : ℝ) = 1 / (1000 * (P : ℝ)) := by
    intro M
    rw [heq M]; push_cast
    rw [show (500 : ℝ) * ((P : ℝ) * 2) = 1000 * (P : ℝ) from by ring]
  have h31 : ∀ M : ℕ, 31 / (ε M : ℝ) = 31000 * (P : ℝ) := by
    intro M
    rw [heR M, div_div_eq_mul_div, div_one]; ring
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ → ℝ,
      ∀ M : ℕ, R M = Real.exp (31 / (ε M : ℝ) * ((Hhi₀ M : ℕ) : ℝ)) / (P : ℝ) :=
    ⟨fun M => Real.exp (31 / (ε M : ℝ) * ((Hhi₀ M : ℕ) : ℝ)) / (P : ℝ), fun _ => rfl⟩
  have hRge : ∀ M : ℕ, 31000 * ((Hhi₀ M : ℕ) : ℝ) ≤ R M := by
    intro M
    rw [hRdef M, le_div_iff₀ hPR, h31 M]
    linarith [Real.add_one_le_exp (31000 * (P : ℝ) * ((Hhi₀ M : ℕ) : ℝ)),
      Nat.cast_nonneg (α := ℝ) (Hhi₀ M)]
  have hR3 : ∀ M : ℕ, (3 : ℝ) ≤ R M := by
    intro M
    have h4 : (4000000 : ℝ) ≤ ((Hhi₀ M : ℕ) : ℝ) := by exact_mod_cast hH4 M
    linarith [hRge M]
  have hR0 : ∀ M : ℕ, (0 : ℝ) ≤ R M := fun M => le_trans (by norm_num) (hR3 M)
  have hNge : ∀ M : ℕ, M ≤ P * ⌊R M⌋₊ := by
    intro M
    have h2 : (M : ℝ) ≤ ((Hhi₀ M : ℕ) : ℝ) := by exact_mod_cast hMH M
    have hMR : (M : ℝ) ≤ R M := by
      linarith [hRge M, Nat.cast_nonneg (α := ℝ) (Hhi₀ M)]
    exact le_trans (Nat.le_floor hMR) (Nat.le_mul_of_pos_left _ hP)
  refine ⟨1 / (500 * (P : ℝ)), 1, rfl, rfl, Set.range (fun M : ℕ => P * ⌊R M⌋₊), ?_, ?_⟩
  · -- `S.Infinite`: the roof is unbounded along `A₀`, since `N M ≥ M`
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨b, hb⟩
    have h1 : P * ⌊R (b + 1)⌋₊ ≤ b := hb ⟨b + 1, rfl⟩
    have h2 := hNge (b + 1)
    exact absurd (le_trans h2 h1) (by omega)
  · -- Sc places the scale in `[K − 1, K]`; P2 rounds; `K ≤ R M` closes the roof side
    rintro _ ⟨M, rfl⟩ r hr
    have hr' := hr
    simp only [admClasses, Finset.mem_filter, Finset.mem_range] at hr'
    obtain ⟨hlo', hhi'⟩ := class_scale_in_band P ⌊R M⌋₊ r hP hr'.1
    have hlo : Real.exp (31 / (ε M : ℝ) * ((Hhi₀ M : ℕ) : ℝ)) / (P : ℝ) / 3
        ≤ (((P * ⌊R M⌋₊ - r) / P : ℕ) : ℝ) := by
      rw [← hRdef M]; exact p2 (R M) (hR3 M) _ hlo'
    have hhi : (((P * ⌊R M⌋₊ - r) / P : ℕ) : ℝ)
        ≤ Real.exp (31 / (ε M : ℝ) * ((Hhi₀ M : ℕ) : ℝ)) / (P : ℝ) := by
      rw [← hRdef M]
      have h1 : (((P * ⌊R M⌋₊ - r) / P : ℕ) : ℝ) ≤ ((⌊R M⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hhi'
      exact le_trans h1 (Nat.floor_le (hR0 M))
    exact hall M r hr ((P * ⌊R M⌋₊ - r) / P) hlo hhi

/-! ## §5 — K: the consumer control (PROVED from L) -/

/-- **⟦LADDER K⟧ (class A, PROVED from L) — L FEEDS D10 IN ONE `exact`.**  At a squarefree stride
`P ≤ 2310` the direct road's terminal `{n | twinLogWeight P n ≠ 0}.Infinite` follows from L and
D10 (`twinLogWeight_support_infinite_of_affFullRange`): `0 ≤ 1/(500·P)` and `1/(500·P) < 1/P`.
A SECOND PROOF of a landed terminal — the honest label above. -/
theorem twinLogWeight_support_infinite_of_ladder (P : ℕ) (hPsq : Squarefree P) (hP : 0 < P)
    (hP2310 : P ≤ 2310) : {n : ℕ | twinLogWeight P n ≠ 0}.Infinite := by
  obtain ⟨ε, A, hε, _hA, S, hS, hall⟩ := ladder_affFullRange_g12b P hP hP2310
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  refine twinLogWeight_support_infinite_of_affFullRange hPsq ?_ ?_ hS hall
  · rw [hε]; positivity
  · rw [hε]
    exact one_div_lt_one_div_of_lt hPR (by linarith)

/-! ## §6 — P6: THE CROWN TWIN (PROVED; math's construction, transcribed at v1.1) -/

/-- **⟦LADDER P6 — THE CROWN TWIN⟧ (class B, PROVED) — K's SET FROM THE CROWN ROAD ALONE, AT EVERY
`0 < P ≤ 2310`, NO `Squarefree`.**  `r := P − 1` is admissible at every `P ≥ 1`
(`(P−1)(P+1) = P² − 1`); the `_g12b` analogue of `logChowlaAffSupplyW_of_headG` —
`log_chowla_aff_of_door_crowned_unslotted_g12b` into `log_chowla_aff_composed_of_headG_g12b`, whose
granted `a ≤ 2310` is `hP2310` — is a three-line `LogChowlaAffSupplyW P (P − 1) 2`; then
`zRough_oddOmega_infinite_of_affSupplyW` and a `mono` through `twinLogWeight`'s `if` and
`liouville_apply`.  WHY IT IS HERE (the refuter's M11(a)): the landed unconditional statements of
this set are at `P = primorial z` only, and the general-`P` consumer's only landed supplier stops at
`P ≤ 548` — so without this twin, K would read as the FIRST unconditional statement of the terminal
on `main` at e.g. `P = 557`, and the honest label ("a second proof") would drift upward on its own.
With it, after the wave the two roads meet at ONE theorem: this name and K state the same set.
⚠ LABEL: math's construction (the refuter's probe P6 on freeze v1, kernel-checked at the three
axioms), transcribed by h2c at v1.1 — the S-4 B/K2′ situation again, labelled against our own
interest; it goes on `main` without a non-author pass of its own. -/
theorem twinLogWeight_support_infinite_of_crown_g12b (P : ℕ) (hP : 0 < P) (hP2310 : P ≤ 2310) :
    {n : ℕ | twinLogWeight P n ≠ 0}.Infinite := by
  have hah9 := hah9_of_le_2310 P hP hP2310
  obtain ⟨k, rfl⟩ : ∃ k, P = k + 1 := ⟨P - 1, by omega⟩
  have hcop : Nat.Coprime (k * (k + 2)) (k + 1) := by
    rw [Nat.coprime_mul_iff_left]
    refine ⟨Nat.coprime_self_add_right.mpr (Nat.coprime_one_right k), ?_⟩
    rw [show k + 2 = (k + 1) + 1 from rfl]
    exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  have hgcd : Nat.gcd (k + 2) (k + 1) ∣ 2 := gcd_dvd_two_of_coprime hcop
  have hsup : LogChowlaAffSupplyW (k + 1) k 2 := by
    intro A₀
    obtain ⟨ε, A, -, -, hA162, hA₀A, Ra, -, -, -, hHlo, -, hnf⟩ :=
      log_chowla_aff_composed_of_headG_g12b (k + 1) k 2 hP two_pos hah9 hP2310 A₀
        (log_chowla_aff_of_door_crowned_unslotted_g12b (k + 1) k 2 hP two_pos (by omega) hgcd
          hah9 A₀)
    exact ⟨A, hA162, hA₀A, Ra.toChowlaRegime, hHlo, hnf⟩
  have hinf := zRough_oddOmega_infinite_of_affSupplyW hP hcop hsup
  refine hinf.mono ?_
  rintro n ⟨hc, hodd⟩
  simp only [Set.mem_setOf_eq]
  have hn0 : n * (n + 2) ≠ 0 := by
    intro h0; rw [h0] at hodd; simp at hodd
  have hn : n ≠ 0 := by rintro rfl; simp at hn0
  unfold twinLogWeight
  rw [if_pos hc, ArithmeticFunction.liouville_apply hn0, hodd.neg_one_pow]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  norm_num [hnR]

end Salt.MR

end
