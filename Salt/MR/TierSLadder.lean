/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TierSBridge
import Mathlib

/-!
# ⟦TIER S — THE LADDER⟧ S-3's BAND, THROUGH THE ENTROPY-ARROW BRIDGE, TO D10's INFINITE SCALE SET
(`TierSLadder`)

**FREEZE v1 — STATEMENT-ONLY.  TWO STATEMENTS `sorry`-BODIED (L, Pl); THREE CONTROLS PROVED (N, Sc,
K).  NO LANDED FILE TOUCHED.  HONEST LABEL, FIRST LINE: NO NEW UNCONDITIONAL THEOREM IS CLAIMED
HERE, AND NOTHING BEARS ON TWIN PRIMES — at a fixed stride `P ≤ 2310` the consumer D10 is a SECOND
PROOF of a terminal the crown route already lands (QUEUE, the Tier S block).**

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
`K ∈ {1, 2, 10⁶}` in `drive_s5_v1.py`. -/
theorem class_scale_in_band (P K r : ℕ) (hP : 0 < P) (hr : r < P) :
    K - 1 ≤ (P * K - r) / P ∧ (P * K - r) / P ≤ K := by
  refine ⟨?_, Nat.div_le_of_le_mul (Nat.sub_le _ _)⟩
  rw [Nat.le_div_iff_mul_le hP]
  calc (K - 1) * P = P * K - P := by rw [Nat.sub_mul, one_mul, mul_comm]
    _ ≤ P * K - r := Nat.sub_le_sub_left hr.le _

/-! ## §2 — Pl: THE PLACEMENT (FROZEN; `sorry`-bodied by order) -/

/-- **⟦LADDER Pl⟧ (class C, FROZEN) — ABOVE THE DESIGN FLOOR THE NORMALISATION THRESHOLD SITS
BELOW THE ROOF, WITH ROOM FOR THE CLASS ROUNDING.**  At the pin `ε = 1/(500·(a·2))` and any
`Hhi₀ ≥ 2^600` (`flatDesignBase_ge_pow600` at `A ≥ 162`, which B exports):
`ε·xTightCeil ε Hhi₀ + xTightCeilArm ε Hhi₀ + ε·log a + ε·log 3 ≤ 31·Hhi₀`.  Divided by `ε` this
is `xTightCeil + xTightCeilArm/ε ≤ 31·Hhi₀/ε − log a − log 3`: the left side bounds
`(ε·log ω₀ + log x₀)/ε`, the threshold above which the band constant is absorbed (N); the right
side is `log (roof/3)`, and `⌊roof⌋₊ − 1 ≥ roof/3` once `roof ≥ 3`.  The `log 3` is the rounding
(Sc); the `log a` is the stride in D10's scale.  S-3 freeze §5 drove the version without the
rounding: at the structure floor `4·10⁶` the instance `P = 2310` FAILS (margin `0.118`), the
crossing is near `3.9·10⁷`, and at `2^600` the margin is astronomical — `drive_s5_v1.py`. -/
theorem ladder_placement (a : ℕ) (ha : 0 < a) (ha2310 : a ≤ 2310) (ε : ℚ)
    (hε : ε = 1 / (500 * ((a * 2 : ℕ) : ℚ))) (Hhi₀ : ℕ) (hH : 2 ^ 600 ≤ Hhi₀) :
    (ε : ℝ) * xTightCeil ε Hhi₀ + xTightCeilArm ε Hhi₀
      + (ε : ℝ) * Real.log (a : ℝ) + (ε : ℝ) * Real.log 3 ≤ 31 * ((Hhi₀ : ℕ) : ℝ) := by
  sorry

/-! ## §3 — L: THE LADDER (FROZEN; `sorry`-bodied by order) -/

/-- **⟦LADDER L⟧ (class C, FROZEN) — D10's HYPOTHESIS PACKAGE AT EVERY STRIDE `P ≤ 2310`.**
`ε = 1/(500·P)`, `A = 1`, and an INFINITE `S` such that at every `N ∈ S` and every admissible class
`r`, `AffFullRangeAt P r 2 ε A ((N − r)/P)`.

Route (statement-only; priced in the freeze, NOT fired): `hah9 : log (P·2) ≤ 9` from `P ≤ 2310`;
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
  sorry

/-! ## §4 — K: the consumer control (PROVED from L; reads `sorry` through L only) -/

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

end Salt.MR

end
