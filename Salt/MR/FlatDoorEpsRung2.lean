/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FlatDoorEpsChain
import Mathlib

/-!
# ⟦TIER S — THE DOOR AT THE HEAD'S GRADE, `ε`-FAMILY: RUNG 2⟧ (`FlatDoorEpsRung2`)
The rung-2 waves' own file, born EMPTY at the price (2026-09-16, on the Captain's word that rung 2
may be priced and fired) and filled wave by wave: every cap the rung-2 walk names — the `_b9`
twins' `log h ≤ 9`, the count leaf's `K ≤ 2^539`, the arm's `H₊/10²⁰` cut, the rated supply's
threshold constants — re-cut as an `_L` sibling with ONE charge parameter `L ≥ log h` and every
threshold affine in `L`, paid at the head by a ninth `max`-arm on the design constant `A`; then
the forms, the replays, the head and the chain re-threaded at generic `0 < ε ≤ 1/500` with NO
cap, and the ONE theorem `flatDoorEpsFamilyW_holds : FlatDoorEpsFamilyW` that inhabits the frozen
file's named `Prop` and discharges its four readers' `hW` binder.  `FlatDoorEpsChain` (rung 1,
Wc) and `FlatDoorEpsFamily` (frozen) are IMPORTED and never edited: every re-cut is a sibling
here, never an edit of a landed name.  Nothing here bears on twin primes (the frozen file's
honest label, first line).
-/

noncomputable section

open scoped BigOperators
open Salt.Entropy.Chowla

namespace Salt.MR

/-! ## §1 — ⟦THE `L`-CHARGE⟧ the rung-2 interface, and row R8/R9 at generic `L`

Every `_L` sibling below replaces the `_b9` twins' cap binder `(hh9 : Real.log h ≤ 9)` by the
CHARGE `{L : ℝ} (hL0 : 0 ≤ L) (hhL : Real.log (h : ℝ) ≤ L)`, and every numeral the landed proof
derived from `h ≤ 8103` by a term AFFINE in `L`.  The one converter the rung-2 walk found is
`log (1/ε) ≤ log 500 + L` (from `1/(500·h) ≤ ε`), and `log 500 ≤ 9 · log 2 ≤ 6.24` (`500 < 512`)
is the numeral that replaces the cap's `16`.  Nothing here bears on twin primes. -/

/-- **⟦log 500 AT THE HEAD'S GRADE⟧** (`epsRung2_log500_le`) — `log 500 ≤ 6.24`, through
`500 < 512 = 2 ^ 9` and `log 2 < 0.6931471808` (`9 · log 2 = 6.2383…`; the true value is
`6.21460809…`).  This is the ONE new numeral the `L`-cut needs: at the cap the twins read
`1/ε ≤ 500·h ≤ 4051500 < 2 ^ 22` and closed with `22 · log 2 ≤ 16`, and at generic `L` the same
step reads `log (1/ε) ≤ log 500 + L ≤ 6.24 + L`. -/
theorem epsRung2_log500_le : Real.log (500 : ℝ) ≤ 6.24 := by
  have h : Real.log (500 : ℝ) ≤ Real.log ((2 : ℝ) ^ (9 : ℕ)) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h
  push_cast at h
  linarith [Real.log_two_lt_d9]

/-- **⟦THE CONVERTER AT GENERIC `L`⟧** (`epsRung2_log_inv_eps_le`) — the rung-2 interface's one
affine site: from the lattice-top pin `1/(500·h) ≤ ε` and the charge `log h ≤ L`,
`log (1/ε) ≤ 6.24 + L`.  This is the term that replaces the `_b9` twins' `log (1/ε) ≤ 16`. -/
theorem epsRung2_log_inv_eps_le {h : ℕ} (hh : 0 < h) {L : ℝ} (hhL : Real.log (h : ℝ) ≤ L)
    {e : ℝ} (he : 0 < e) (hpin : 1 / (500 * (h : ℝ)) ≤ e) :
    Real.log (1 / e) ≤ 6.24 + L := by
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hupos : (0 : ℝ) < 1 / e := div_pos one_pos he
  have hinv500 : 1 / e ≤ 500 * (h : ℝ) := by
    rw [div_le_iff₀ he]
    rw [div_le_iff₀ (by positivity)] at hpin
    linarith
  have hlogmul : Real.log (500 * (h : ℝ)) = Real.log 500 + Real.log (h : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hhR)
  have h1 : Real.log (1 / e) ≤ Real.log (500 * (h : ℝ)) := Real.log_le_log hupos hinv500
  rw [hlogmul] at h1
  linarith [epsRung2_log500_le, hhL]

set_option maxHeartbeats 1000000 in
-- as the source (`V7RatedH.lean:1313`): the exponent comparison closes through `exp` rewrites
-- and three `nlinarith` calls, and the `L`-cut adds one more atom to the closing `linarith`.
/-- **⟦R8 — `klevF_capNumeral_h_b9` AT THE HEAD'S GRADE⟧** (`klevF_capNumeral_L`) — the `_b9`
twin's ONE cap site (`V7RatedH.lean:1334`, `h ≤ 8103` by `h_le_8103_of_hh9`) feeds exactly one
number, `log (1/ε) ≤ 16`.  At generic `L` it reads `log (1/ε) ≤ 6.24 + L`, and the close
`9.6·(c' + 21) ≤ 69·e^{2t}` becomes `9.6·(c' + 11.24 + L) ≤ 69·e^{2t}`: the `L` is paid by the
WEAKEST hypothesis the tower admits, `hLt : L ≤ e^{1.6A}` (at `A ≥ 26` that is `L ≤ 10^17`),
through `e^{2t} ≥ 2t + 1` — never a numeral cap on `L`.  Every other step is the `_b9` twin's. -/
theorem klevF_capNumeral_L {h : ℕ} (hh : 0 < h) {L : ℝ} (hL0 : 0 ≤ L)
    (hhL : Real.log (h : ℝ) ≤ L) {A : ℝ} (hA : 26 ≤ A)
    (hLt : L ≤ Real.exp (3.2 * A / 2)) {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    (heps500 : (1 : ℚ) / (500 * (h : ℚ)) ≤ R.eps)
    (hHhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    9.60000096 * (Real.log ((R.Hhi : ℕ) : ℝ) + Real.log (1 / (R.eps : ℝ)) + 5)
      ≤ Real.log ((calP (AdoorL M) (s13GK (KlevF A) M) 2 : ℕ) : ℝ) := by
  set t : ℝ := Real.exp (3.2 * A / 2) with htdef
  have ht17 : (10 : ℝ) ^ 17 ≤ t := flat_exp_half_ge hA
  have ht0 : (0 : ℝ) < t := by nlinarith [ht17]
  have htbig : (100000000 : ℝ) ≤ t := by nlinarith [ht17]
  have hHhiN : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
  have hHhiR : (4000000 : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast hHhiN
  have hepsR : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hhQ : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  have h5q : (1 : ℚ) ≤ 500 * (h : ℚ) * R.eps := by
    rw [div_le_iff₀ (by positivity)] at heps500; linarith
  have h5r : (1 : ℝ) ≤ 500 * (h : ℝ) * (R.eps : ℝ) := by exact_mod_cast h5q
  have hpinR : 1 / (500 * (h : ℝ)) ≤ (R.eps : ℝ) := by
    have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    rw [div_le_iff₀ (by positivity)]; linarith
  have hinvle : Real.log (1 / (R.eps : ℝ)) ≤ 6.24 + L :=
    epsRung2_log_inv_eps_le hh hhL hepsR hpinR
  have hL624 : (0 : ℝ) ≤ 6.24 + L := add_nonneg (by norm_num) hL0
  have hlogHhipos : (0 : ℝ) < Real.log ((R.Hhi : ℕ) : ℝ) := by
    have h : Real.log 1 < Real.log ((R.Hhi : ℕ) : ℝ) :=
      Real.log_lt_log one_pos (by linarith)
    simpa using h
  have hlogHhi_le : Real.log ((R.Hhi : ℕ) : ℝ) ≤ Real.exp (2 * t) := by
    calc Real.log ((R.Hhi : ℕ) : ℝ)
        = Real.exp (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) := (Real.exp_log hlogHhipos).symm
      _ ≤ Real.exp (2 * t) := Real.exp_le_exp.mpr hHhi
  have hexp2t : (2 : ℝ) * t + 1 ≤ Real.exp (2 * t) := Real.add_one_le_exp (2 * t)
  have hexp2t_big : (100 : ℝ) ≤ Real.exp (2 * t) := by linarith [htbig, hexp2t]
  have hlog2lo : (0.6931 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hAd : 1 ≤ AdoorL M := one_le_AdoorL hM
  have hnat : 2 ^ (KlevF A) ≤ 4 * (AdoorL M * s13GK (KlevF A) M) := by
    have h1 : 2 ^ (KlevF A) ≤ s13GK (KlevF A) M := by
      rw [s13GK]
      calc 2 ^ (KlevF A) ≤ 3072 * 2 ^ (KlevF A) := Nat.le_mul_of_pos_left _ (by norm_num)
        _ ≤ 3072 * 2 ^ (KlevF A) * M := Nat.le_mul_of_pos_right _ (by omega)
    calc 2 ^ (KlevF A) ≤ s13GK (KlevF A) M := h1
      _ ≤ AdoorL M * s13GK (KlevF A) M := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ 4 * (AdoorL M * s13GK (KlevF A) M) := Nat.le_mul_of_pos_left _ (by norm_num)
  have hnatR : (2 : ℝ) ^ (KlevF A) ≤ ((4 * (AdoorL M * s13GK (KlevF A) M) : ℕ) : ℝ) := by
    have h : ((2 ^ (KlevF A) : ℕ) : ℝ) ≤ ((4 * (AdoorL M * s13GK (KlevF A) M) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa using h
  have h2K : (2 : ℝ) ^ (KlevF A) = Real.exp (((KlevF A : ℕ) : ℝ) * Real.log 2) := by
    conv_rhs => rw [← Real.log_pow]
    exact (Real.exp_log (by positivity)).symm
  have hKge : (4 : ℝ) * t ≤ ((KlevF A : ℕ) : ℝ) := by
    have h := KlevF_ge A
    have hkc : ((kcap : ℕ) : ℝ) = 4 := by rw [kcap]; norm_num
    rw [hkc, ← htdef] at h
    exact h
  have hKlog : 2 * t + 0.7724 * t ≤ ((KlevF A : ℕ) : ℝ) * Real.log 2 := by
    nlinarith [hKge, hlog2lo, ht0]
  have hsplit : Real.exp (2 * t + 0.7724 * t) = Real.exp (2 * t) * Real.exp (0.7724 * t) :=
    Real.exp_add _ _
  have hexpres : (100 : ℝ) ≤ Real.exp (0.7724 * t) := by
    have h := Real.add_one_le_exp (0.7724 * t)
    nlinarith [h, htbig]
  have hpow_lo : (69 : ℝ) * Real.exp (2 * t) ≤ (2 : ℝ) ^ (KlevF A) * Real.log 2 := by
    have hchain : Real.exp (2 * t) * Real.exp (0.7724 * t) ≤ (2 : ℝ) ^ (KlevF A) := by
      rw [h2K, ← hsplit]
      exact Real.exp_le_exp.mpr hKlog
    have hexp2pos : (0 : ℝ) < Real.exp (2 * t) := Real.exp_pos _
    have hmul : Real.exp (2 * t) * 100 ≤ Real.exp (2 * t) * Real.exp (0.7724 * t) :=
      mul_le_mul_of_nonneg_left hexpres (le_of_lt hexp2pos)
    have hstep1 : (100 : ℝ) * Real.exp (2 * t) ≤ (2 : ℝ) ^ (KlevF A) := by
      linarith [hchain, hmul]
    have h2Knn : (0 : ℝ) ≤ (2 : ℝ) ^ (KlevF A) := by positivity
    have hstep2 : 100 * Real.exp (2 * t) * 0.6931 ≤ (2 : ℝ) ^ (KlevF A) * Real.log 2 :=
      mul_le_mul hstep1 hlog2lo (by norm_num) h2Knn
    linarith [hstep2, hexp2pos]
  rw [s16_logP2]
  have hcast : ((4 * (AdoorL M * s13GK (KlevF A) M) : ℕ) : ℝ) * Real.log 2
      ≥ (2 : ℝ) ^ (KlevF A) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hnatR (by linarith)
  linarith [hlogHhi_le, hinvle, hpow_lo, hcast, hexp2t_big, hexp2t, hLt, hL624, ht0]

/-- **⟦R9 — `s16_baseScaleCap96_LH_at_klevF_b9` AT THE HEAD'S GRADE⟧**
(`s16_baseScaleCap96_LH_at_klevF_L`) — SUPPLIER-SWAP: `klevF_capNumeral_h_b9 ↦
klevF_capNumeral_L`.  No cap site of its own; the `L` binders ride through.  BODY: the `_b9`
twin's, verbatim. -/
theorem s16_baseScaleCap96_LH_at_klevF_L {h : ℕ} (hh : 0 < h) {L : ℝ} (hL0 : 0 ≤ L)
    (hhL : Real.log (h : ℝ) ≤ L) {A : ℝ} (hA : 26 ≤ A)
    (hLt : L ≤ Real.exp (3.2 * A / 2)) {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) (heps500 : (1 : ℚ) / (500 * (h : ℚ)) ≤ R.eps)
    (hx : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ))
    (hHhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S16BaseScaleCap96_LH_gk h (KlevF A) R M :=
  s16_baseScaleCap96_LH_of_end h (KlevF A) (s16_baseScaleCapEnd_LH_of_xceil hx)
    (klevF_capNumeral_L hh hL0 hhL hA hLt hM heps500 hHhi)

/-! ## §2 — ⟦R5⟧ the `XThread` charge at a generic count cap `Kb`

`xt_log_inv_rho_le_scaled`'s cap is NOT on `h` but on the socket's count parameter,
`hKcb : Kc ≤ 2 ^ 539`, and its ONE spending site is the split
`2 ^ 580 = 2 ^ 41 · 2 ^ 539` inside `hlo` (`XThread.lean:271`, `:283`).  At a generic real
ceiling `Kb ≥ 1` the split is `2 ^ 41 · Kb`, the `Kb` CANCELS EXACTLY in `hval`
(`110525 · 16 · Kb / (2 ^ 41 · Kb · c) = 1768400 / (2 ^ 41 · c)`), and the conclusion's `403`
becomes `29 + log Kb` — `29` is `41 · log 2 = 28.4190…` rounded up, and nothing else. -/

/-- **⟦R5 — `xt_log_inv_rho_le_scaled` AT A GENERIC COUNT CEILING⟧** (`xt_log_inv_rho_le_L`) —
the landed binder `(hKcb : Kc ≤ 2 ^ 539)` is replaced by `{Kb : ℝ} (hKb1 : 1 ≤ Kb)
(hKcb : Kc ≤ Kb)`, and the landed conclusion `≤ 403 + log c` by `≤ 29 + log Kb + log c`.  At
`Kb := 2 ^ 539` the two agree to `29 + 539 · log 2 = 402.60… ≤ 403`, so this sibling is not
weaker than its source at the source's own pin.  BODY: the source's, with `2 ^ 580 ↦ 2 ^ 41 · Kb`
at `hlo`, `hstep`, `hval`, `h1`, `h2`, and the `hsplit` line dropped (there is nothing to
split). -/
theorem xt_log_inv_rho_le_L {c δ₀ Kc Kb : ℝ} (hc1 : 1 ≤ c) (hδ₀ : 0 < δ₀)
    (hδpin : 1 / (838400 * c) ≤ δ₀) (hKc : 0 < Kc) (hKb1 : 1 ≤ Kb) (hKcb : Kc ≤ Kb) :
    Real.log (1 / doorRhoOfDelta (s12DeltaSock δ₀ Kc)) ≤ 29 + Real.log Kb + Real.log c := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hKb0 : (0 : ℝ) < Kb := by linarith
  have hδs : 0 < s12DeltaSock δ₀ Kc := s12DeltaSock_pos hδ₀ hKc
  have hρpos : 0 < doorRhoOfDelta (s12DeltaSock δ₀ Kc) := doorRhoOfDelta_pos hδs.ne'
  have hp41one : (1 : ℝ) ≤ 2 ^ (41 : ℕ) := one_le_pow₀ (by norm_num)
  have hlo : (1 : ℝ) / (2 ^ (41 : ℕ) * Kb * c) ≤ doorRhoOfDelta (s12DeltaSock δ₀ Kc) := by
    rw [doorRhoOfDelta]
    refine le_min ?_ ?_
    · rw [div_le_one (by positivity)]
      have hKbc : (1 : ℝ) ≤ Kb * c := by nlinarith
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 2 ^ (41 : ℕ) * (Kb * c) := mul_le_mul hp41one hKbc (by norm_num) (by positivity)
        _ = 2 ^ (41 : ℕ) * Kb * c := by ring
    rw [s12DeltaSock_sq hδ₀ hKc, le_div_iff₀ (by norm_num : (0 : ℝ) < 110525),
      le_div_iff₀ (by positivity : (0 : ℝ) < 16 * Kc)]
    have hstep : 1 / ((2 : ℝ) ^ (41 : ℕ) * Kb * c) * 110525 * (16 * Kc)
        ≤ 1 / ((2 : ℝ) ^ (41 : ℕ) * Kb * c) * 110525 * (16 * Kb) := by
      have hcpos : (0 : ℝ) < 1 / ((2 : ℝ) ^ (41 : ℕ) * Kb * c) * 110525 * 16 := by positivity
      nlinarith [hKcb, hcpos]
    have hval : 1 / ((2 : ℝ) ^ (41 : ℕ) * Kb * c) * 110525 * (16 * Kb)
        = 1768400 / (2 ^ (41 : ℕ) * c) := by
      field_simp; ring
    have hnum : (1768400 : ℝ) / (2 ^ (41 : ℕ) * c) ≤ 1 / (838400 * c) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hc0]
    linarith [hδpin]
  have h1 : (1 : ℝ) / doorRhoOfDelta (s12DeltaSock δ₀ Kc) ≤ 2 ^ (41 : ℕ) * Kb * c := by
    rw [div_le_iff₀ hρpos]
    calc (1 : ℝ) = (2 ^ (41 : ℕ) * Kb * c) * (1 / (2 ^ (41 : ℕ) * Kb * c)) := by field_simp
      _ ≤ (2 ^ (41 : ℕ) * Kb * c) * doorRhoOfDelta (s12DeltaSock δ₀ Kc) :=
        mul_le_mul_of_nonneg_left hlo (by positivity)
  have h2 : Real.log (1 / doorRhoOfDelta (s12DeltaSock δ₀ Kc))
      ≤ Real.log ((2 : ℝ) ^ (41 : ℕ) * Kb * c) := Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at h2
  push_cast at h2
  linarith [Real.log_two_lt_d9]

/-! ## §3 — ⟦R7⟧ the three S16 flat arms at generic `L`

The two cap sites are `S16FlatTerminalLinear.lean:2461` (`h ≤ 8103`, feeding
`⌈1/ε⌉₊ ≤ 500·h ≤ 4051500` and `4·4051500⁴ ≤ arcFloor36 = 10¹³⁸`) and `:2489` (the budget chain's
`1/ε⁶ ≤ 4.43·10³⁹`).  Neither numeral survives a generic `L`: both are bounds on `h`, so at
generic `L` they read `4·(500·h)⁴ ≤ e^{27 + 4L}` and `1/ε⁶ ≤ 1.5625·10¹⁶ · e^{6L}`, and the
FIXED registers they were compared against (`10¹³⁸`, `4·10³⁹·A`) no longer dominate.  Both are
therefore paid through `flatDesignBase A = ⌈e^{e^{3.2A}}⌉₊`'s TOWER by ONE affine hypothesis,

  `hAL : 10 + 2 * L ≤ A`     (`a₀ = 10`, `a₁ = 2`),

which is the walk's row 7a `A ≥ 3.05 + 1.875·log(1/ε)` re-derived at the object and rounded up:
the budget needs `3.2·A ≥ log(4·12000·log 4·1.5626·10¹⁶) + log A + 6L ≈ 47 + log A + 6L`, and
`a₁ = 2` leaves `0.2·A ≥ 17 + log A`, true at `A = 162` by `32.4 ≥ 22.1` and increasing.
⛔ `hA : 162 ≤ A` is KEPT (the replays read it), so `hAL` bites only at `L > 76`. -/

/-- **⟦R7a — `flat_arm_eps_le_h_b9` AT THE HEAD'S GRADE⟧** (`flat_arm_eps_le_L`) — the landed
route `4·⌈1/ε⌉₊⁴ ≤ 4·4051500⁴ ≤ arcFloor36 ≤ flatDesignBase A` has a FIXED register in the
middle, and at generic `L` the left end is `4·(500·h)⁴ ≤ 2.5·10¹¹ · e^{4L} ≤ e^{27 + 4L}`, which
`10¹³⁸` cannot hold.  The `_L` route goes straight to the tower: `27 + 4L ≤ 2A + 7 ≤ e^{3.2A}`
under `hAL`.  `⌈1/ε⌉₊ ≤ 500·h` is the source's, verbatim (it never read the cap). -/
theorem flat_arm_eps_le_L {h : ℕ} (hh : 0 < h) {L : ℝ} (hL0 : 0 ≤ L)
    (hhL : Real.log (h : ℝ) ≤ L) {A : ℝ} {ε : ℚ}
    (hA : 162 ≤ A) (hAL : 10 + 2 * L ≤ A) (hε : 0 < ε) (hεpin : 1 / (500 * (h : ℚ)) ≤ ε) :
    4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4 ≤ flatDesignBase A := by
  have hq0 : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  have hceil : ⌈(1 / ε : ℚ)⌉₊ ≤ 500 * h := by
    refine Nat.ceil_le.mpr ?_
    rw [div_le_iff₀ hε]
    have hq : (1 : ℚ) / (500 * (h : ℚ)) ≤ ε := hεpin
    rw [div_le_iff₀ (by positivity)] at hq
    push_cast
    nlinarith [hq, hq0, hε]
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hceilR : ((⌈(1 / ε : ℚ)⌉₊ : ℕ) : ℝ) ≤ 500 * (h : ℝ) := by exact_mod_cast hceil
  have hhexp : (h : ℝ) ≤ Real.exp L := by
    calc (h : ℝ) = Real.exp (Real.log (h : ℝ)) := (Real.exp_log hhR).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hhL
  have hh4 : (h : ℝ) ^ 4 ≤ Real.exp (4 * L) := by
    have hp := pow_le_pow_left₀ hhR.le hhexp 4
    have hid : (Real.exp L) ^ (4 : ℕ) = Real.exp (4 * L) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hid] at hp
    exact hp
  have hceil4 : ((⌈(1 / ε : ℚ)⌉₊ : ℕ) : ℝ) ^ 4 ≤ (500 * (h : ℝ)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hceilR 4
  have hE4 : (1 : ℝ) ≤ Real.exp (4 * L) := by
    have := Real.add_one_le_exp (4 * L); linarith
  have hbase : ((4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4 : ℕ) : ℝ) ≤ 250000000000 * Real.exp (4 * L) := by
    push_cast
    nlinarith [hceil4, hh4, hE4]
  have hE27 : (250000000000 : ℝ) ≤ Real.exp 27 := by
    have he : Real.exp 27 = (Real.exp 1) ^ (27 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    rw [he]
    calc (250000000000 : ℝ) ≤ (2.7 : ℝ) ^ (27 : ℕ) := by norm_num
      _ ≤ (Real.exp 1) ^ (27 : ℕ) := pow_le_pow_left₀ (by norm_num) h1.le 27
  have hfin : ((4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4 : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by
    calc ((4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4 : ℕ) : ℝ)
        ≤ 250000000000 * Real.exp (4 * L) := hbase
      _ ≤ Real.exp 27 * Real.exp (4 * L) :=
          mul_le_mul_of_nonneg_right hE27 (Real.exp_pos _).le
      _ = Real.exp (27 + 4 * L) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (2 * A + 7) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (Real.exp (3.2 * A)) :=
          Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp (3.2 * A)])
  rw [flatDesignBase]
  exact_mod_cast le_trans hfin (Nat.le_ceil _)

set_option maxHeartbeats 1000000 in
-- the `L`-cut carries the degree-2 monomial `A · e^{6L}` through `hbX` and `hexpfin` where the
-- source compared `budgetX` against the single numeral `10^44 · A`; the closes are linear, but
-- the `budgetX` product expansion under them is not, and it runs past the default budget.
/-- **⟦R7b — `flat_arm_budget_le_h_b9` AT THE HEAD'S GRADE⟧** (`flat_arm_budget_le_L`) — the cap
site `:2489` feeds ONE number, `1/ε⁶ ≤ 4.43·10³⁹`, which at generic `L` is
`1/ε⁶ ≤ 1.5625·10¹⁶ · e^{6L}`; the landed `budgetXFlat ≤ 10⁴⁴·A` then reads
`4·budgetXFlat ≤ 2.6·10²⁰ · A · e^{6L}`, and the close `4·10⁴⁴·A ≤ e^{3.2A}` becomes
`2.6·10²⁰·A·e^{6L} ≤ e^{3A−30}·e^{0.2A+30}` under `hAL : 10 + 2L ≤ A` (which gives
`6L ≤ 3A − 30`).  The second `max` arm (`2·log A + 2`) is the source's, untouched. -/
theorem flat_arm_budget_le_L {h : ℕ} (hh : 0 < h) {L : ℝ} (hL0 : 0 ≤ L)
    (hhL : Real.log (h : ℝ) ≤ L) {A β : ℝ} {ε : ℚ} (hA : 162 ≤ A) (hAL : 10 + 2 * L ≤ A)
    (hβ : 0 < β) (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (ε : ℝ)) (hε2 : (ε : ℝ) ≤ 1 / 2)
    (hbudA : budgetAFlat (ε : ℝ) β ≤ A) :
    budgetFloorFlat (ε : ℝ) β A ≤ flatDesignBase A := by
  have hx0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hhexp : (h : ℝ) ≤ Real.exp L := by
    calc (h : ℝ) = Real.exp (Real.log (h : ℝ)) := (Real.exp_log hx0).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hhL
  have h6b : (h : ℝ) ^ 6 ≤ Real.exp (6 * L) := by
    have hp := pow_le_pow_left₀ hx0.le hhexp 6
    have hid : (Real.exp L) ^ (6 : ℕ) = Real.exp (6 * L) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hid] at hp
    exact hp
  set e : ℝ := (ε : ℝ) with hedef
  have hepos : (0 : ℝ) < e := by
    rw [hedef]; exact lt_of_lt_of_le (by positivity) hε
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hden : (0 : ℝ) < e ^ 6 * β ^ 2 := by positivity
  have hbud' : 2304 * Real.log 4 ≤ A * (e ^ 6 * β ^ 2) := by
    rw [budgetAFlat, div_le_iff₀ hden] at hbudA
    linarith [hbudA]
  have he6 : e ^ 6 ≤ 1 / 64 := by
    have hp := pow_le_pow_left₀ hepos.le hε2 6
    norm_num at hp; linarith
  have hbsq : (1 : ℝ) / β ^ 2 ≤ A / 204352 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hbud', he6, hl2lo, hlog4, sq_nonneg β, hβ, pow_pos hepos 6]
  have hb1 : (1 : ℝ) / β ≤ 1 + A / 204352 := by
    have ht : (1 : ℝ) / β ≤ 1 + 1 / β ^ 2 := by
      have hq : (1 : ℝ) / β ^ 2 = (1 / β) ^ 2 := by field_simp
      nlinarith [sq_nonneg (1 / β - 1), hq]
    linarith [hbsq]
  have he6lo : (1 : ℝ) / (15625000000000000 * (h : ℝ) ^ 6) ≤ e ^ 6 := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (500 * (h : ℝ))) hε 6
    have hid : ((1 : ℝ) / (500 * (h : ℝ))) ^ 6 = 1 / (15625000000000000 * (h : ℝ) ^ 6) := by
      field_simp; ring
    rw [hid] at hp; exact hp
  have hE6 : (1 : ℝ) ≤ Real.exp (6 * L) := by
    have := Real.add_one_le_exp (6 * L); linarith
  have hepow : (1 : ℝ) / e ^ 6 ≤ 15625000000000000 * Real.exp (6 * L) := by
    rw [div_le_iff₀ (by positivity)]
    have hstep : (1 : ℝ) ≤ 15625000000000000 * (h : ℝ) ^ 6 * e ^ 6 := by
      have hpos : (0 : ℝ) < 15625000000000000 * (h : ℝ) ^ 6 := by positivity
      have := mul_le_mul_of_nonneg_left he6lo hpos.le
      calc (1 : ℝ) = 15625000000000000 * (h : ℝ) ^ 6 * (1 / (15625000000000000 * (h : ℝ) ^ 6)) := by
            field_simp
        _ ≤ 15625000000000000 * (h : ℝ) ^ 6 * e ^ 6 := this
    nlinarith [hstep, mul_nonneg (sub_nonneg.mpr h6b) (le_of_lt (pow_pos hepos 6))]
  have hS : (1 : ℝ) / β ^ 2 + 1 / β + 1 ≤ A := by
    have : A / 204352 + (1 + A / 204352) + 1 ≤ A := by linarith
    linarith [hbsq, hb1]
  have hSpos : (0 : ℝ) ≤ 1 / β ^ 2 + 1 / β + 1 := by positivity
  have hTL : (1 : ℝ) / e ^ 6 + 1 ≤ 15626000000000000 * Real.exp (6 * L) := by
    linarith [hepow, hE6]
  have hTpos : (0 : ℝ) ≤ 1 / e ^ 6 + 1 := by positivity
  have hApos : (0 : ℝ) < A := by linarith
  have hprod : (1 / β ^ 2 + 1 / β + 1) * (1 / e ^ 6 + 1)
      ≤ A * (15626000000000000 * Real.exp (6 * L)) :=
    mul_le_mul hS hTL hTpos hApos.le
  have hSTnn : (0 : ℝ) ≤ (1 / β ^ 2 + 1 / β + 1) * (1 / e ^ 6 + 1) := mul_nonneg hSpos hTpos
  have hlog4hi : Real.log 4 ≤ 1.3862943616 := by rw [hlog4]; linarith
  have hAE162 : (162 : ℝ) ≤ A * Real.exp (6 * L) := by nlinarith [hE6, hApos]
  have hbX : 4 * budgetXFlat e β ≤ 260000000000000000000 * (A * Real.exp (6 * L)) := by
    rw [budgetXFlat, budgetX]
    nlinarith [hprod, hlog4hi, hSTnn, hAE162]
  have hE62 : (10 : ℝ) ^ (26 : ℕ) ≤ Real.exp 62 := by
    have he : Real.exp 62 = (Real.exp 1) ^ (62 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    rw [he]
    calc (10 : ℝ) ^ (26 : ℕ) ≤ (2.7 : ℝ) ^ (62 : ℕ) := by norm_num
      _ ≤ (Real.exp 1) ^ (62 : ℕ) := pow_le_pow_left₀ (by norm_num) h1.le 62
  have hQ : 260000000000000000000 * A ≤ Real.exp (0.2 * A + 30) := by
    have hsp : Real.exp (0.2 * A + 30) = Real.exp 62 * Real.exp (0.2 * A - 32) := by
      rw [← Real.exp_add]; ring_nf
    have hlin : (0.2 : ℝ) * A - 31 ≤ Real.exp (0.2 * A - 32) := by
      have := Real.add_one_le_exp (0.2 * A - 32); linarith
    have hnn : (0 : ℝ) ≤ 0.2 * A - 31 := by linarith
    have hprd : (10 : ℝ) ^ (26 : ℕ) * (0.2 * A - 31) ≤ Real.exp 62 * Real.exp (0.2 * A - 32) :=
      mul_le_mul hE62 hlin hnn (by positivity)
    rw [hsp]
    nlinarith [hprd, hA]
  have hexpfin : 260000000000000000000 * (A * Real.exp (6 * L)) ≤ Real.exp (3.2 * A) := by
    have hEle : Real.exp (6 * L) ≤ Real.exp (3 * A - 30) := Real.exp_le_exp.mpr (by linarith)
    have hsp2 : Real.exp (3.2 * A) = Real.exp (3 * A - 30) * Real.exp (0.2 * A + 30) := by
      rw [← Real.exp_add]; ring_nf
    have hP : (0 : ℝ) < Real.exp (3 * A - 30) := Real.exp_pos _
    have hAmul : A * Real.exp (6 * L) ≤ A * Real.exp (3 * A - 30) :=
      mul_le_mul_of_nonneg_left hEle hApos.le
    have hstepB : Real.exp (3 * A - 30) * (260000000000000000000 * A)
        ≤ Real.exp (3 * A - 30) * Real.exp (0.2 * A + 30) :=
      mul_le_mul_of_nonneg_left hQ hP.le
    rw [hsp2]
    linarith [hAmul, hstepB]
  have hmax : max (4 * budgetXFlat e β) (2 * Real.log A + 2) ≤ Real.exp (3.2 * A) := by
    refine max_le ?_ ?_
    · linarith [hbX, hexpfin]
    · have hlA : Real.log A ≤ A - 1 := Real.log_le_sub_one_of_pos hApos
      have h2A : (2 : ℝ) * A ≤ Real.exp (3.2 * A) := by
        nlinarith [Real.add_one_le_exp (3.2 * A)]
      linarith
  rw [budgetFloorFlat, flatDesignBase]
  exact Nat.ceil_le_ceil (Real.exp_le_exp.mpr hmax)

/-- **⟦R7c — `flat_witFloor_eq_designBase_h_b9` AT THE HEAD'S GRADE⟧**
(`flat_witFloor_eq_designBase_L`) — SUPPLIER-SWAP: the two `h`-scaled arms become `_L`
(`flat_arm_budget_le_L`, `flat_arm_eps_le_L`); the three `ε`-free arms are the landed ones, and
no cap site of its own.  BODY: the `_b9` twin's, verbatim. -/
theorem flat_witFloor_eq_designBase_L {h : ℕ} (hh : 0 < h) {L : ℝ} (hL0 : 0 ≤ L)
    (hhL : Real.log (h : ℝ) ≤ L) {A β : ℝ} {ε : ℚ} {Hopq : ℕ} (hA : 162 ≤ A)
    (hAL : 10 + 2 * L ≤ A) (hβ : 0 < β)
    (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (ε : ℝ)) (hε2 : (ε : ℝ) ≤ 1 / 2) (hεq : 0 < ε)
    (hεqpin : 1 / (500 * (h : ℚ)) ≤ ε) (hbudA : budgetAFlat (ε : ℝ) β ≤ A)
    (hopq : Hopq ≤ flatDesignBase A) :
    flatWitFloor ε β A Hopq = flatDesignBase A := by
  have hbud := flat_arm_budget_le_L hh hL0 hhL hA hAL hβ hε hε2 hbudA
  have hepsarm := flat_arm_eps_le_L hh hL0 hhL hA hAL hεq hεqpin
  have harc := flat_arm_arcFloor_le hA
  have hll := flat_arm_loglogFloor_le hA
  have hdf := flat_designFloor_eq_designBase hA
  rw [flatWitFloor, hdf]
  omega

/-! ## §4 — ⟦R11⟧ the `flatDoorM` bump at a generic count `c`

`flatDoorM_bfloor_bump_g12`'s cap `hcb : c ≤ 1202604` is spent in ONE place —
`hcsqb : c ² ≤ 1446256380816`, feeding `hcap : 1.648361472·10²³ · c² ≤ 2 ³⁵⁵` — and `2 ³⁵⁵` is a
FIXED register, so at generic `c` it cannot hold: the left end is `e^{54 + 2L}`.  The `_L` route
replaces the register by `flatDoorM`'s own tower, `flatDoorM_ge A : e^{1.6A}/310301 − 1 ≤
flatDoorM A`, and pays `L` by the SAME affine hypothesis §3 uses, `hAL : 10 + 2·L ≤ A`
(`a₀ = 10`, `a₁ = 2`).  The demand is only `0.6·A ≥ 57`, i.e. `A ≥ 95`, so at `A ≥ 162` the
row has 40 nats of headroom and `a₁ = 2` is not this row's binding constraint. -/

/-- **⟦R11a — `flatDoorM_bfloor_bump_g12` AT A GENERIC COUNT⟧** (`flatDoorM_bfloor_bump_L`) —
the landed binder `(hcb : c ≤ 1202604)` is replaced by the charge `{L} (hL0 : 0 ≤ L)
(hcL : log c ≤ L)` and the tower hypothesis `(hAL : 10 + 2 * L ≤ A)`; `hc1`, `hA`, `hδ`, `hδb`,
`hCg` and the conclusion are the source's.
⚠️ `_hL0` carries the interface's `0 ≤ L` slot and is UNREFERENCED here (it is derivable:
`1 ≤ c` gives `0 ≤ log c ≤ L`), so it is underscored; its TYPE and POSITION are unchanged and a
consumer still supplies it.  BODY: `hkey` and `hstep` verbatim (neither reads the
cap — `hstep`'s `24·2·10¹²·838400·4096 = 1.648361472·10²³` is EXACT at the pins); `hcsqb`,
`hcap` and `hpow` replaced by the tower route `1.648361472·10²³·c² ≤ e^{54}·e^{2L} =
e^{54+2L} ≤ e^{A+44} ≤ e^{1.6A}/310301 − 1 ≤ flatDoorM A`. -/
theorem flatDoorM_bfloor_bump_L {A Cg δ₀ L : ℝ} {c : ℕ} (hc1 : 1 ≤ c) (_hL0 : 0 ≤ L)
    (hcL : Real.log (c : ℝ) ≤ L) (hA : 162 ≤ A) (hAL : 10 + 2 * L ≤ A) (hδ : 0 < δ₀)
    (hδb : 1 / (838400 * 2 ^ 12 * (c : ℝ) ^ 2) ≤ δ₀) (hCg : Cg ≤ 2 * 10 ^ 12) :
    24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ) := by
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hcsqpos : (0 : ℝ) < (c : ℝ) ^ 2 := by nlinarith [hcR1]
  have hkey : (1 : ℝ) / (838400 * 2 ^ 12) ≤ (c : ℝ) ^ 2 * δ₀ := by
    have h := mul_le_mul_of_nonneg_left hδb hcsqpos.le
    calc (1 : ℝ) / (838400 * 2 ^ 12)
        = (c : ℝ) ^ 2 * (1 / (838400 * 2 ^ 12 * (c : ℝ) ^ 2)) := by field_simp
      _ ≤ (c : ℝ) ^ 2 * δ₀ := h
  have hstep : 24 * Cg / δ₀ ≤ (164836147200000000000000 : ℝ) * (c : ℝ) ^ 2 := by
    rw [div_le_iff₀ hδ]
    nlinarith [hkey, hCg]
  have hcexp : (c : ℝ) ≤ Real.exp L := by
    calc (c : ℝ) = Real.exp (Real.log (c : ℝ)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hcL
  have hcsqE : (c : ℝ) ^ 2 ≤ Real.exp (2 * L) := by
    have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (c : ℝ)) hcexp 2
    have hid : (Real.exp L) ^ (2 : ℕ) = Real.exp (2 * L) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hid] at hp
    exact hp
  have hE54 : (164836147200000000000000 : ℝ) ≤ Real.exp 54 := by
    have he : Real.exp 54 = (Real.exp 1) ^ (54 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    rw [he]
    calc (164836147200000000000000 : ℝ) ≤ (2.7 : ℝ) ^ (54 : ℕ) := by norm_num
      _ ≤ (Real.exp 1) ^ (54 : ℕ) := pow_le_pow_left₀ (by norm_num) h1.le 54
  have hlhs : (164836147200000000000000 : ℝ) * (c : ℝ) ^ 2 ≤ Real.exp (A + 44) := by
    calc (164836147200000000000000 : ℝ) * (c : ℝ) ^ 2
        ≤ Real.exp 54 * (c : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hE54 hcsqpos.le
      _ ≤ Real.exp 54 * Real.exp (2 * L) :=
          mul_le_mul_of_nonneg_left hcsqE (Real.exp_pos _).le
      _ = Real.exp (54 + 2 * L) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (A + 44) := Real.exp_le_exp.mpr (by linarith)
  have hE13 : (310301 : ℝ) ≤ Real.exp 13 := by
    have he : Real.exp 13 = (Real.exp 1) ^ (13 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    rw [he]
    calc (310301 : ℝ) ≤ (2.7 : ℝ) ^ (13 : ℕ) := by norm_num
      _ ≤ (Real.exp 1) ^ (13 : ℕ) := pow_le_pow_left₀ (by norm_num) h1.le 13
  have hMge : Real.exp (3.2 * A / 2) / 310301 - 1 ≤ ((flatDoorM A : ℕ) : ℝ) := flatDoorM_ge A
  have htower : Real.exp (A + 44) ≤ Real.exp (3.2 * A / 2) / 310301 - 1 := by
    have hsp : Real.exp (3.2 * A / 2) = Real.exp (A + 57) * Real.exp (0.6 * A - 57) := by
      rw [← Real.exp_add]; ring_nf
    have h57 : Real.exp (A + 57) = Real.exp (A + 44) * Real.exp 13 := by
      rw [← Real.exp_add]; ring_nf
    have hEA44 : (1 : ℝ) ≤ Real.exp (A + 44) := by
      have := Real.add_one_le_exp (A + 44); linarith
    have hbig : (2 : ℝ) ≤ Real.exp (0.6 * A - 57) := by
      have := Real.add_one_le_exp (0.6 * A - 57); linarith
    have hstepa : (310301 : ℝ) * Real.exp (A + 44) ≤ Real.exp (A + 57) := by
      rw [h57]
      have := mul_le_mul_of_nonneg_left hE13 (Real.exp_pos (A + 44)).le
      linarith
    have hstepb : Real.exp (A + 57) + Real.exp (A + 57) ≤ Real.exp (3.2 * A / 2) := by
      rw [hsp]
      have := mul_le_mul_of_nonneg_left hbig (Real.exp_pos (A + 57)).le
      linarith
    rw [le_sub_iff_add_le, le_div_iff₀ (by norm_num : (0 : ℝ) < 310301)]
    nlinarith [hstepa, hstepb, hEA44]
  linarith [hstep, hlhs, htower, hMge]


/-! ## §W4 — the rated supply's sub-suppliers at generic `L`

The seventeen `_b9` lemmas BELOW the rated cofactor supply, re-cut with the rung-2 charge
`{Lc : ℝ} (hL0 : 0 ≤ Lc) (hhL : Real.log h ≤ Lc)` in place of `(hh9 : Real.log h ≤ 9)`.
⛔ The charge is named `Lc`, not `L`: fifteen of the seventeen landed statements already bind
`L : ℕ`, the socket's block length inside `SocketBaseLH h R M H L q j A s`.

WHERE THE CAP WAS PAID, AND WHAT PAYS IT NOW — two towers carry the whole wave, and both are the
SAME quantity `loglog H₋`:
* `hloL : 518 + k·Lc ≤ loglog H₋` (`k = 1` everywhere but the uniform page, where `k = 6`), for
  every site that spent the cap against `log H₊ ≥ 10^8`.  It gives
  `log H₋ ≥ exp (518 + Lc) = exp 518 · exp Lc ≥ 10^8 · (1 + Lc)`.
* `hflL : 50 + Lc ≤ loglog H₋`, BESIDE (never in place of) the cap grid's numeral floor
  `hfl : loglogFloor50 ≤ H₋`, which the bodies still spend through
  `regime_Hfloor_of_loglogFloor50`.  It gives `log H ≥ 10^21 · (1 + Lc)`.
Both follow from `518 + 6·Lc ≤ loglog H₋` by `linarith`, so the root (wave 5) strengthens ONE
hypothesis.  No conclusion moves except `cofkL_mu_floor_L`'s, and NO numeral caps `Lc`.
Nothing here bears on twin primes. -/

/-- **⟦THE `518`-TOWER AT GENERIC `L`⟧** (`cofk_tower_logfloor_L`) — the rung-2 payer for every
site whose `_b9` twin spent `log h ≤ 9` against `log H₊ ≥ 10^8`.  From `518 + L ≤ loglog H₋`,
`log H₋ ≥ exp (518 + L) = exp 518 · exp L ≥ 10^8 · (1 + L)`, and the socket's `H₋ ≤ H ≤ H₊`
carries it to both.  `exp 518 ≥ (1 + 518/4)^4 = 290029415.06… ≥ 10^8` (`cofk_exp_quartic`,
margin `2.900×`) and `exp L ≥ 1 + L` (`Real.add_one_le_exp`). -/
theorem cofk_tower_logfloor_L {R : ChowlaRegime} {h M H L q j A s : ℕ} {Lc : ℝ}
    (hL0 : 0 ≤ Lc) (hb : SocketBaseLH h R M H L q j A s)
    (hloL : (518 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (10 : ℝ) ^ 8 * (1 + Lc) ≤ Real.log (R.Hlo : ℝ)
      ∧ Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ)
      ∧ Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) := by
  have h1 : R.Hlo ≤ H := hb.1
  have h2 : H ≤ R.Hhi := hb.2.1
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hlogHlo : (14 : ℝ) ≤ Real.log (R.Hlo : ℝ) := cofk_log_big hHlo4
  have hexp : Real.exp (518 + Lc) ≤ Real.log (R.Hlo : ℝ) := by
    have h := Real.exp_le_exp.mpr hloL
    rwa [Real.exp_log (by linarith)] at h
  have hquart : (10 : ℝ) ^ 8 ≤ Real.exp (518 : ℝ) := by
    have h := cofk_exp_quartic (u := (518 : ℝ)) (by norm_num)
    have hnum : (290029400 : ℝ) ≤ (1 + (518 : ℝ) / 4) ^ 4 := by norm_num
    linarith
  have hexpL : (1 : ℝ) + Lc ≤ Real.exp Lc := by
    have h := Real.add_one_le_exp Lc; linarith
  have hmul : (10 : ℝ) ^ 8 * (1 + Lc) ≤ Real.exp 518 * Real.exp Lc :=
    mul_le_mul hquart hexpL (by linarith) (Real.exp_pos _).le
  rw [Real.exp_add] at hexp
  exact ⟨by linarith, Real.log_le_log (by linarith) hHloH,
    Real.log_le_log (by linarith) hHHhi⟩

/-- **⟦THE CAP-GRID TOWER AT GENERIC `L`⟧** (`s13_tower_logH_L`) — the rung-2 payer for the sites
whose `_b9` twin spent `log h ≤ 9` against the cap grid's NUMERAL floor `loglogFloor50 ≤ H₋`,
which carries no `L` at all.  From `50 + L ≤ loglog H₋`,
`log H ≥ log H₋ ≥ exp (50 + L) = exp 50 · exp L ≥ 10^21 · (1 + L)`
(`capfloor_ten21_le_exp50`, `Real.add_one_le_exp`). -/
theorem s13_tower_logH_L {R : ChowlaRegime} {h M H L q j A s : ℕ} {Lc : ℝ}
    (hL0 : 0 ≤ Lc) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (10 : ℝ) ^ 21 * (1 + Lc) ≤ Real.log (H : ℝ) := by
  have h1 : R.Hlo ≤ H := hb.1
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hlogHlo : (14 : ℝ) ≤ Real.log (R.Hlo : ℝ) := cofk_log_big hHlo4
  have hexp : Real.exp (50 + Lc) ≤ Real.log (R.Hlo : ℝ) := by
    have h := Real.exp_le_exp.mpr hflL
    rwa [Real.exp_log (by linarith)] at h
  have hexpL : (1 : ℝ) + Lc ≤ Real.exp Lc := by
    have h := Real.add_one_le_exp Lc; linarith
  have hmul : (10 : ℝ) ^ 21 * (1 + Lc) ≤ Real.exp 50 * Real.exp Lc :=
    mul_le_mul capfloor_ten21_le_exp50 hexpL (by linarith) (Real.exp_pos _).le
  have hmono : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hHloH
  rw [Real.exp_add] at hexp
  linarith

/-- `capfloor_twoj_le_H_LH_b9` at generic `L` (`capfloor_twoj_le_H_L`) — TRANSPORT, a LEAF.  The
`_b9` twin already carries its cap as an UNSPENT binder (`_hh9`), and the charge is unspent here
too; it is kept so every sibling in this section has ONE interface.  BODY: the twin's,
verbatim. -/
theorem capfloor_twoj_le_H_L {h : ℕ} (_hh : 0 < h) {Lc : ℝ} (_hL0 : 0 ≤ Lc)
    (_hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseLH h R M H L q j A s) : 2 ^ j ≤ H := by
  have hjL : j ≤ Nat.log 2 L := hb.2.2.2.2.2.1
  have hLH : L ≤ H := hb.2.2.1
  have hH : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · subst hL0
    have hj : j = 0 := by simpa using hjL
    subst hj
    simpa using (by omega : 1 ≤ H)
  · exact le_trans (le_trans (Nat.pow_le_pow_right (by norm_num) hjL)
      (Nat.pow_log_le_self 2 (by omega))) hLH

/-- `s13_socketBase_logA_ge_sqrt_LH_b9` at generic `L` (`s13_socketBase_logA_ge_sqrt_L`) — the
cap-grid LEAF, and the one site in this section where the twin paid its cap out of a NUMERAL
floor.  `hlog'` reads the x-scale's `log h` at `L` (`9 ↦ L`); the twin absorbed the `9` in the
`2000 ≤ √H` margin, and NO numeral margin absorbs an unbounded `L`, so the payer is
`s13_tower_logH_L`: `w² = log H ≥ 10^21 · (1 + L)`.  The close is LINEAR once three facts are
taken — `L ≤ w²`, `24·w ≤ w²/50` (from `w ≥ 2000`) and `w²/2 ≤ u` (`hwu`) — which give
`L + 24·w ≤ 4.5·u + 20` and then
`log A ≥ 8·u·log 2 − 5·log 2 − L − 24·w + 24 ≥ 5.54517·u + 0.534 − 4.5·u ≥ u`
(margin `0.0451·u`, and `u ≥ 2000`).  Every other step is the twin's, verbatim. -/
theorem s13_socketBase_logA_ge_sqrt_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    Real.sqrt (H : ℝ) ≤ Real.log (A : ℝ) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have hlogHbig : (4000000 : ℝ) ≤ Real.log (H : ℝ) := le_trans s13_four_million_le_exp50 hexp50
  -- ⟦THE CHARGE'S PAYER — the cap grid's floor carries no `L`, this does⟧
  have htow : (10 : ℝ) ^ 21 * (1 + Lc) ≤ Real.log (H : ℝ) := s13_tower_logH_L hL0 hb hflL
  set u : ℝ := Real.sqrt (H : ℝ) with hu
  set w : ℝ := Real.sqrt (Real.log (H : ℝ)) with hw
  have hu2 : u ^ 2 = (H : ℝ) := Real.sq_sqrt (by positivity)
  have hw2 : w ^ 2 = Real.log (H : ℝ) := Real.sq_sqrt hlogH0.le
  have hu0 : (0 : ℝ) < u := by rw [hu]; exact Real.sqrt_pos.mpr (by linarith)
  have hw0 : (0 : ℝ) < w := by rw [hw]; exact Real.sqrt_pos.mpr hlogH0
  have hu2000 : (2000 : ℝ) ≤ u := by nlinarith [hu2, hu0, hHR]
  have hw2000 : (2000 : ℝ) ≤ w := by nlinarith [hw2, hw0, hlogHbig]
  have hlogu : Real.log u = Real.log (H : ℝ) / 2 := by
    rw [hu]; exact Real.log_sqrt (by positivity)
  have hlogule : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu0
  have hHu : Real.log (H : ℝ) ≤ 2 * u - 2 := by rw [hlogu] at hlogule; linarith
  have hlogw : Real.log w = Real.log (Real.log (H : ℝ)) / 2 := by
    rw [hw]; exact Real.log_sqrt hlogH0.le
  have hlogwle : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hw0
  have hllH : Real.log (Real.log (H : ℝ)) ≤ 2 * w - 2 := by rw [hlogw] at hlogwle; linarith
  have hwu : w ^ 2 ≤ 2 * u := by rw [hw2]; linarith
  -- ⟦the x-scale, in logs, at the CHARGE⟧
  set m : ℕ := ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ with hm
  have hxs : ((4 ^ m : ℕ) : ℝ) ^ 2 ≤ 2 * ((h : ℝ) * arcDen 12 H) * (A : ℝ) :=
    s13_socketBase_xscale_LH hb
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hAR : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hL12 : (0 : ℝ) < Real.log (H : ℝ) ^ (12 : ℕ) := by positivity
  have hhl : (0 : ℝ) < (h : ℝ) * Real.log (H : ℝ) ^ (12 : ℕ) := mul_pos hh0 hL12
  have hlhs0 : (0 : ℝ) < ((4 ^ m : ℕ) : ℝ) ^ 2 := by positivity
  have hlog := Real.log_le_log hlhs0 hxs
  have hLx : Real.log (((4 ^ m : ℕ) : ℝ) ^ 2) = 4 * (m : ℝ) * Real.log 2 := by
    have h4 : ((4 ^ m : ℕ) : ℝ) = (4 : ℝ) ^ m := by push_cast; ring
    rw [h4, ← pow_mul, Real.log_pow, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hRR : Real.log (2 * ((h : ℝ) * arcDen 12 H) * (A : ℝ))
      = Real.log 2 + Real.log (h : ℝ) + 12 * Real.log (Real.log (H : ℝ)) + Real.log (A : ℝ) := by
    rw [harcpow, Real.log_mul (mul_pos two_pos hhl).ne' hAR.ne', Real.log_mul two_ne_zero hhl.ne',
      Real.log_mul hh0.ne' hL12.ne', Real.log_pow]
    push_cast; ring
  rw [hLx, hRR] at hlog
  have hlog' : 4 * (m : ℝ) * Real.log 2
      ≤ Real.log 2 + Lc + 12 * Real.log (Real.log (H : ℝ)) + Real.log (A : ℝ) := by linarith
  have hmfl : 2 * u - 1 ≤ (m : ℝ) := by rw [hm, hu]; exact s13_socketBase_mFloor hhi
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  -- ⟦the close, made LINEAR: the tower pays `L` and the `24·w` debit out of `w²`⟧
  have hwL : (10 : ℝ) ^ 21 * (1 + Lc) ≤ w ^ 2 := by rw [hw2]; exact htow
  have hwLc : Lc ≤ w ^ 2 := by linarith
  have hww : 2000 * w ≤ w * w := mul_le_mul_of_nonneg_right hw2000 hw0.le
  have hw24 : 24 * w ≤ w ^ 2 / 50 := by rw [pow_two]; linarith
  have hclose : Lc + 24 * w - 20 ≤ 4.5 * u := by linarith
  have hml : (2 * u - 1) * Real.log 2 ≤ (m : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hmfl (by linarith)
  have hul : 5.5451774424 * u ≤ 8 * u * Real.log 2 := by
    have h8 : (0 : ℝ) ≤ 8 * u := by linarith
    have hmul := mul_le_mul_of_nonneg_left hl2lo.le h8
    linarith
  linarith [hlog', hml, hllH, hclose, hul, hl2hi, hu0]

/-- `s13_socketBase_loglogA_sharp_LH_b9` at generic `L` (`s13_socketBase_loglogA_sharp_L`) —
SUPPLIER-SWAP (`s13_socketBase_logA_ge_sqrt_L`).  The twin spends its cap NOWHERE in its own
body, only in the supplier call; the charge and the cap-grid tower ride through unchanged.
BODY: the twin's, verbatim. -/
theorem s13_socketBase_loglogA_sharp_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    Real.log (H : ℝ) / 2 ≤ Real.log (Real.log (A : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  set u : ℝ := Real.sqrt (H : ℝ) with hu
  have hu0 : (0 : ℝ) < u := by rw [hu]; exact Real.sqrt_pos.mpr (by linarith)
  have hmain : u ≤ Real.log (A : ℝ) := s13_socketBase_logA_ge_sqrt_L hh hL0 hhL hfl hb hflL
  have hlogu : Real.log u = Real.log (H : ℝ) / 2 := by
    rw [hu]; exact Real.log_sqrt (by positivity)
  have hmono := Real.log_le_log hu0 hmain
  rw [hlogu] at hmono
  linarith

/-- `s13CapGrid_mu_lo_LH_b9` at generic `L` (`s13CapGrid_mu_lo_L`) — SUPPLIER-SWAP
(`s13_socketBase_logA_ge_sqrt_L`).  The twin spends its cap only in the supplier call.
BODY: the twin's, verbatim. -/
theorem s13CapGrid_mu_lo_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    Real.sqrt (H : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hmono : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    Real.log_le_log hA0 (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) s])
  exact le_trans (s13_socketBase_logA_ge_sqrt_L hh hL0 hhL hfl hb hflL) hmono

/-- `capfloor_core_LH_b9` at generic `L` (`capfloor_core_L`) — SUPPLIER-SWAP
(`s13_socketBase_logA_ge_sqrt_L`, `capfloor_twoj_le_H_L`).  The twin spends its cap only in the
two supplier calls; the `10^21 ≤ log H` leg and the height leg are numeral-free in `h`.
BODY: the twin's, verbatim. -/
theorem capfloor_core_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (H : ℝ) ∧ Real.sqrt (H : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) ∧
      0 < Tann ∧ Real.log ((Nd : ℕ) : ℝ) / 2 ≤ Real.log Tann := by
  have hlo : R.Hlo ≤ H := hb.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have hv : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (H : ℝ) :=
    le_trans capfloor_ten21_le_exp50 hexp50
  -- the base
  have hsqrtH : Real.sqrt (H : ℝ) ≤ Real.log (A : ℝ) :=
    s13_socketBase_logA_ge_sqrt_L hh hL0 hhL hfl hb hflL
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hANR : (A : ℝ) ≤ ((Nd : ℕ) : ℝ) := by exact_mod_cast hAN
  have hNd0 : (0 : ℝ) < ((Nd : ℕ) : ℝ) := lt_of_lt_of_le hA0 hANR
  have hm : Real.sqrt (H : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) :=
    le_trans hsqrtH (Real.log_le_log hA0 hANR)
  -- the height
  have h2j : 2 ^ j ≤ H := capfloor_twoj_le_H_L hh hL0 hhL hb
  have h2jR : ((2 ^ j : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h2j
  have h2j0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hTpos : 0 < Tann := lt_of_lt_of_le (div_pos hNd0 h2j0) hTlo
  have hlogdiv : Real.log ((Nd : ℕ) : ℝ) - Real.log ((2 ^ j : ℕ) : ℝ) ≤ Real.log Tann := by
    have hz := Real.log_le_log (div_pos hNd0 h2j0) hTlo
    rwa [Real.log_div (ne_of_gt hNd0) (ne_of_gt h2j0)] at hz
  have hlog2j : Real.log ((2 ^ j : ℕ) : ℝ) ≤ Real.log (H : ℝ) := Real.log_le_log h2j0 h2jR
  have hHhalf : Real.log (H : ℝ) ≤ Real.sqrt (H : ℝ) / 2 := capfloor_logH_le_half_sqrt hHR
  exact ⟨hv, hm, hTpos, by linarith⟩

/-- `s13CapGrid_mu_2000_LH_b9` at generic `L` (`s13CapGrid_mu_2000_L`) — SUPPLIER-SWAP
(`s13CapGrid_mu_lo_L`).  The twin spends its cap only in the supplier call; the `2000 ≤ √H` step
is numeral-free in `h`.  BODY: the twin's, verbatim. -/
theorem s13CapGrid_mu_2000_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hs2 : Real.sqrt (H : ℝ) ^ 2 = (H : ℝ) := Real.sq_sqrt (by positivity)
  have hs0 : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have h2000 : (2000 : ℝ) ≤ Real.sqrt (H : ℝ) := by nlinarith [hs2, hs0, hHR]
  exact le_trans h2000 (s13CapGrid_mu_lo_L hh hL0 hhL hfl hb hflL)

/-- `s13CapGrid_Lambda_sharp_LH_b9` at generic `L` (`s13CapGrid_Lambda_sharp_L`) — SUPPLIER-SWAP
(`s13_socketBase_logA_ge_sqrt_L`, `s13_socketBase_loglogA_sharp_L`).  The twin spends its cap only
in the two supplier calls.  BODY: the twin's, verbatim. -/
theorem s13CapGrid_Lambda_sharp_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    Real.log (H : ℝ) / 2 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hsq := s13_socketBase_logA_ge_sqrt_L hh hL0 hhL hfl hb hflL
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hs2 : Real.sqrt (H : ℝ) ^ 2 = (H : ℝ) := Real.sq_sqrt (by positivity)
  have hs0 : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have h2000 : (2000 : ℝ) ≤ Real.sqrt (H : ℝ) := by nlinarith [hs2, hs0, hHR]
  have hlogA0 : (0 : ℝ) < Real.log (A : ℝ) := by linarith
  have hmono : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    Real.log_le_log hA0 (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) s])
  exact le_trans (s13_socketBase_loglogA_sharp_L hh hL0 hhL hfl hb hflL)
    (Real.log_le_log hlogA0 hmono)

/-- `s13CapGrid_Lambda_lo_LH_b9` at generic `L` (`s13CapGrid_Lambda_lo_L`) — SUPPLIER-SWAP
(`s13CapGrid_Lambda_sharp_L`).  The twin spends its cap only in the supplier call; the close
against `2·10^21 ≤ exp 50` is numeral-free in `h`.  BODY: the twin's, verbatim. -/
theorem s13CapGrid_Lambda_lo_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseLH h R M H L q j A s)
    (hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have hsharp := s13CapGrid_Lambda_sharp_L hh hL0 hhL hfl hb hflL
  linarith [capgrid_exp50_lo]

/-- `cofkL_socket_floors_h_b9` at generic `L` (`cofkL_socket_floors_L`) — TRANSPORT, a LEAF.  The
twin's raise cost `26·log 10 + 4·log h ≤ 60.086 + 36` against `log H₊ ≥ 10^8`; at the charge the
cost is `26·log 10 + 4·L ≤ 60.086 + 4·L` and the payer is `cofk_tower_logfloor_L`,
`log H₊ ≥ 10^8 · (1 + L)` — so `hlo` gains the affine term and NOTHING else moves.  The
conclusion is the twin's, unchanged.  `26 · 2.311 = 60.086` (`cofk_log_ten_le`); the margin is
`10^8 − 60.086` on the constant and `10^8 − 4` on the `L`-coefficient. -/
theorem cofkL_socket_floors_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseLH h R M H L q j A s)
    (hloL : (518 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (4000000 : ℝ) ≤ (H : ℝ) ∧ (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 ≤ (R.Hhi : ℝ) := by
  have h1 : R.Hlo ≤ H := hb.1
  have h2 : H ≤ R.Hhi := hb.2.1
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hLhh : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hH4 : (4000000 : ℝ) ≤ (H : ℝ) := by linarith
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  obtain ⟨hlolo, hmono1, hmono2⟩ := cofk_tower_logfloor_L hL0 hb hloL
  have hLH8L : (10 : ℝ) ^ 8 * (1 + Lc) ≤ Real.log (R.Hhi : ℝ) := by linarith
  refine ⟨hH4, ?_⟩
  have hlogle : Real.log ((10 : ℝ) ^ 26 * (h : ℝ) ^ 4) ≤ Real.log (R.Hhi : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    linarith [cofk_log_ten_le]
  have h2' := Real.exp_le_exp.mpr hlogle
  rwa [Real.exp_log (by positivity), Real.exp_log hHhi0] at h2'

/-- `pieceFloor_vt_threshold_of_loglog_rated_h_b9` at generic `L`
(`pieceFloor_vt_threshold_of_loglog_rated_L`) — a LEAF, and the ONE lemma of the seventeen that
needs NO payer at all: its own binder `hbud` already bounds `log h`.  The twin spends its cap in
a single unnamed place — the `hL9 : 0 ≤ 9 − Lh` inside `hprod`, whose `linarith` reads `hh9` from
the CONTEXT — to absorb the two widened logarithms through one product.  At the charge that
product is FALSE for large `L` (at `L = 100`, `Λ = 1`: `112 · 119 = 13328` against `2 · 19² =
722`), so the bound on `Lh` is taken from `hbud` instead, which is strictly weaker than any new
hypothesis: `log (7 + 12Λ) ≤ 6 + 12Λ` gives `156·Lh ≤ 76·Λ + 108`, i.e. `Lh ≤ 0.4872·Λ +
0.6924`, and the product then closes with `132.07·Λ² + 231.30·Λ + 92.67 ≥ 0` to spare.  The
charge is therefore carried as an UNSPENT binder, for one interface across the section.  Every
other step is the twin's, verbatim. -/
theorem pieceFloor_vt_threshold_of_loglog_rated_L {q H h : ℕ} [NeZero q]
    {X K Kbig D Z δ : ℝ} (hZ : 1 ≤ Z) (hδ : 0 < δ) (hh : 0 < h)
    (hH : Real.exp 1 ≤ Real.log (H : ℝ))
    (hq : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H)
    {Lc : ℝ} (_hL0 : 0 ≤ Lc) (_hhL : Real.log (h : ℝ) ≤ Lc)
    (hbud : 156 * Real.log h + 8 * Real.log 2
      ≤ 28 * Real.log (Real.log (H : ℝ))
        + 4 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ))) + 84)
    (hKB : K + bandArcConst Z δ ≤ Kbig)
    (hthr : 40 * Real.log (Real.log (Real.log X))
        + 1900 * Real.log (Real.log (H : ℝ))
        + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
        + 2300 + 32 * Kbig + 32 * D
      < Real.log (Real.log X)) :
    40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
          + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q
          + bandConstQ Z δ q + K + 25 + D)
      < Real.log (Real.log X) := by
  have hLH1 := one_le_loglog_of_exp_le hH
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hLh0 : (0 : ℝ) ≤ Real.log h := Real.log_nonneg hh1
  have hband := bandConstQ_le_of_le_arcDen_h (q := q) (H := H) (h := h) hZ hδ hh hH hq
  set LH : ℝ := Real.log (Real.log (H : ℝ)) with hLHdef
  set Lh : ℝ := Real.log h with hLhdef
  have hlogq := log_le_of_le_arcDen_h hh hH hq
  have hcap := mertensCap_le_of_le_arcDen_h (q := q) hh hH hq
  have hvkd := vkDebitConst_le_of_le_arcDen_h (q := q) hh hH hq
  have hvkm := vkMidDebitSharp_le_of_le_arcDen_h (q := q) hh hH hq
  have h7pos : (0 : ℝ) < 7 + 12 * LH := by linarith
  have hlognn : (0 : ℝ) ≤ Real.log (7 + 12 * LH) := Real.log_nonneg (by linarith)
  have hp2 : (0 : ℝ) < Lh + 12 * LH := by linarith
  have hp4 : (0 : ℝ) < 7 + Lh + 12 * LH := by linarith
  -- ⟦THE CHARGE'S PAYER — `hbud` itself, no new hypothesis⟧
  have hlogsub : Real.log (7 + 12 * LH) ≤ 6 + 12 * LH := by
    have h := Real.log_le_sub_one_of_pos h7pos
    linarith
  have hbd : 156 * Lh ≤ 76 * LH + 108 := by
    have h2lo := Real.log_two_gt_d9
    linarith
  have hprod : (Lh + 12 * LH) * (7 + Lh + 12 * LH) ≤ 2 * (7 + 12 * LH) ^ 2 := by
    have hLH0 : (0 : ℝ) ≤ LH := by linarith
    have ha : (0 : ℝ) ≤ 76 * LH + 108 - 156 * Lh := by linarith
    nlinarith [mul_nonneg ha hLh0, mul_nonneg ha hLH0, ha, hLH1]
  have habs24 : Real.log (Lh + 12 * LH) + Real.log (7 + Lh + 12 * LH)
      ≤ Real.log 2 + 2 * Real.log (7 + 12 * LH) := by
    have h1 : Real.log ((Lh + 12 * LH) * (7 + Lh + 12 * LH))
        ≤ Real.log (2 * (7 + 12 * LH) ^ 2) :=
      Real.log_le_log (mul_pos hp2 hp4) hprod
    rw [Real.log_mul (ne_of_gt hp2) (ne_of_gt hp4),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    push_cast at h1
    linarith
  linarith

/-- `capFreeFloor3_pieceDatum_arcDen_rated_h_b9` at generic `L`
(`capFreeFloor3_pieceDatum_arcDen_rated_L`) — SUPPLIER-SWAP
(`pieceFloor_vt_threshold_of_loglog_rated_L`).  The twin spends its cap only in the supplier
call, and that supplier needs no payer, so this page needs none either.  BODY: the twin's,
verbatim. -/
theorem capFreeFloor3_pieceDatum_arcDen_rated_L (h : ℕ) (hh : 0 < h)
    {Lc : ℝ} (hL0 : 0 ≤ Lc) (hhL : Real.log (h : ℝ) ≤ Lc) :
    ∃ Z δ K : ℝ, 1 ≤ Z ∧ 0 < δ ∧ 0 ≤ K ∧
      ∀ (q : ℕ) [NeZero q] (H : ℕ) (χ : DirichletCharacter ℂ q)
        (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X D : ℝ),
      Real.exp 1 ≤ Real.log (H : ℝ) → (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
      156 * Real.log h + 8 * Real.log 2
          ≤ 28 * Real.log (Real.log (H : ℝ))
            + 4 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ))) + 84 →
      Real.exp (Real.exp 1) ≤ X → 0 ≤ D →
      32 * Salt.SW.diskConst q / goldenL1 q ≤ Real.log X →
      (∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)) ≤ D →
      40 * Real.log (Real.log (Real.log X))
          + 1900 * Real.log (Real.log (H : ℝ))
          + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
          + 2300 + 32 * K + 32 * D
        < Real.log (Real.log X) →
        CapFreeFloor3 (pieceDatum χ 𝒥 Pseq Qseq) X := by
  obtain ⟨Z, δ, K, hZ, hδ, hK0, hK⟩ := capFreeFloor3_pieceDatum_vt_rated
  refine ⟨Z, δ, K + max 0 (bandArcConst Z δ), hZ, hδ,
    add_nonneg hK0 (le_max_left _ _), ?_⟩
  intro q _ H χ Pseq Qseq 𝒥 X D hH harc hbud hX hD0 hgate hdebit hthr
  exact hK q χ Pseq Qseq 𝒥 X D hX hD0 hgate hdebit
    (pieceFloor_vt_threshold_of_loglog_rated_L hZ hδ hh hH harc hL0 hhL hbud
      (by linarith [le_max_right (0 : ℝ) (bandArcConst Z δ)]) hthr)

set_option maxHeartbeats 1000000 in
-- as the twin: the floor's arithmetic closes over the primorial and square-root brackets in one
-- block, and the charge adds the `h²·L` monomial to the same bracket
/-- `cofkL_logX_floor_h_b9` at generic `L` (`cofkL_logX_floor_L`) — a LEAF, and the deepest
NUMERAL-LIFT of the wave.  The twin's `− log h` cost is read at `9` in `hlow`/`hmulL`/`hsm1`
(`9.6932 = 9 + 0.6932`); at the charge it is `L + 0.6932`, and `hsm1` then asks
`10^6 · h² · (L + 0.6932) ≤ H₊`, which the twin's own `hHhi : 10^26 · h⁴ ≤ H₊` CANNOT pay —
it would need `L ≤ 10^20`, a numeral cap, which is a STOP.  The payer is `cofk_tower_logfloor_L`,
and it is spent MULTIPLICATIVELY so that no logarithm of a product is needed:
`log H₊ ≥ 10^8 · (1 + L)` with the twin's own `hsq : log H₊ ≤ 2·√H₊ − 2` gives
`√H₊ ≥ 5·10^7 · (1 + L) + 1 ≥ L + 1`, and the twin's own `hprod : 10^13 · h² · √H₊ ≤ H₊` then
gives `10^13 · h² · (L + 1) ≤ H₊`, which covers `10^6 · h² · (L + 0.6932)` by `10^7×`.
The final bracket keeps its margin: `hsm1` still bounds `10^6 · h² ≤ 1.443 · H₊`, so the close
reads `10^6·h²·log A ≥ 9.0896·H₊ − 3.9995·H₊ = 5.09·H₊ ≥ H₊`.  Every other step is the twin's,
verbatim. -/
theorem cofkL_logX_floor_L {R : ChowlaRegime} {h M H L q j A s : ℕ} (hh : 0 < h)
    {Lc : ℝ} (hL0 : 0 ≤ Lc) (hhL : Real.log (h : ℝ) ≤ Lc)
    (hb : SocketBaseLH h R M H L q j A s)
    (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ))
    (hHhi : (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 ≤ (R.Hhi : ℝ))
    (hH : (4000000 : ℝ) ≤ (H : ℝ))
    (hloL : (518 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (R.Hhi : ℝ) / (10 ^ 6 * (h : ℝ) ^ 2) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have h2 : H ≤ R.Hhi := hb.2.1
  have h8 : 0 < A := hb.2.2.2.2.2.2.2.1
  have h11 : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * ((h : ℝ) * arcDen 12 H) * (A : ℝ) :=
    hb.2.2.2.2.2.2.2.2.2.2.1
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hh2 : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith [hh1]
  have hh24 : (h : ℝ) ^ 2 ≤ (h : ℝ) ^ 4 := by nlinarith [hh2, sq_nonneg ((h : ℝ))]
  have hLh0 : (0 : ℝ) ≤ Real.log h := Real.log_nonneg hh1
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by nlinarith [hHhi, hh2, hh24]
  -- ⟦THE CHARGE'S PAYER — the `518`-tower, carried to `log H₊`⟧
  obtain ⟨hlolo, hmono1, hmono2⟩ := cofk_tower_logfloor_L hL0 hb hloL
  have hLH8L : (10 : ℝ) ^ 8 * (1 + Lc) ≤ Real.log (R.Hhi : ℝ) := by linarith
  have hlogH : (14 : ℝ) ≤ Real.log (H : ℝ) := cofk_log_big hH
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := by linarith
  have hω0 : (0 : ℝ) < (R.ω : ℝ) := by
    have : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
    linarith
  have harc : (0 : ℝ) < arcDen 12 H := by
    rw [arcDen]; exact Real.rpow_pos_of_pos hlogH0 12
  have harcH : (0 : ℝ) < (h : ℝ) * arcDen 12 H := by positivity
  have hlogarc : Real.log (arcDen 12 H) = 12 * Real.log (Real.log (H : ℝ)) :=
    log_arcDen_twelve hlogH0
  set E : ℕ := ⌊R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)⌋₊ with hEdef
  have hPH0 : 8 * (((4 ^ E : ℕ) : ℝ)) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ) := R.hPHheadroom
  have hW : (((4 ^ E : ℕ) : ℝ)) = (4 : ℝ) ^ E := by push_cast; ring
  rw [hW] at hPH0
  have hmul : (8 * ((4 : ℝ) ^ E) ^ 2) * (R.ω : ℝ)
      ≤ (16 * ((h : ℝ) * arcDen 12 H) * (A : ℝ)) * (R.ω : ℝ) := by
    have := le_trans hPH0 h11; linarith
  have h8w : 8 * ((4 : ℝ) ^ E) ^ 2 ≤ 16 * ((h : ℝ) * arcDen 12 H) * (A : ℝ) :=
    le_of_mul_le_mul_right hmul hω0
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast h8
  have hkey : ((4 : ℝ) ^ E) ^ 2 / (2 * ((h : ℝ) * arcDen 12 H)) ≤ (A : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hlogW : Real.log (((4 : ℝ) ^ E) ^ 2) = 2 * (E : ℝ) * Real.log 4 := by
    rw [← pow_mul, Real.log_pow]
    push_cast; ring
  have harc2 : (0 : ℝ) < 2 * ((h : ℝ) * arcDen 12 H) := by linarith
  have hW2pos : (0 : ℝ) < ((4 : ℝ) ^ E) ^ 2 := by positivity
  have heq : Real.log (((4 : ℝ) ^ E) ^ 2 / (2 * ((h : ℝ) * arcDen 12 H)))
      = 2 * (E : ℝ) * Real.log 4 - Real.log 2 - Real.log h
        - 12 * Real.log (Real.log (H : ℝ)) := by
    rw [Real.log_div (ne_of_gt hW2pos) (ne_of_gt harc2), hlogW,
      Real.log_mul (by norm_num) (ne_of_gt harcH),
      Real.log_mul (ne_of_gt hh0) (ne_of_gt harc), hlogarc]
    ring
  have hlogA : 2 * (E : ℝ) * Real.log 4 - Real.log 2 - Real.log h
      - 12 * Real.log (Real.log (H : ℝ)) ≤ Real.log (A : ℝ) := by
    have hle : Real.log (((4 : ℝ) ^ E) ^ 2 / (2 * ((h : ℝ) * arcDen 12 H)))
        ≤ Real.log (A : ℝ) := Real.log_le_log (div_pos hW2pos harc2) hkey
    rw [heq] at hle
    exact hle
  have hEfl : (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) - 1 ≤ (E : ℝ) := by
    have hq : (R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)) < (E : ℚ) + 1 := by
      rw [hEdef]; exact Nat.lt_floor_add_one _
    have hR : ((R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ) : ℚ) : ℝ) < ((E : ℚ) : ℝ) + 1 := by
      exact_mod_cast hq
    push_cast at hR
    linarith
  have hεh : (1 : ℝ) ≤ 500 * (h : ℝ) * (R.eps : ℝ) := by
    have h500 : (0 : ℝ) < 500 * (h : ℝ) := by linarith
    rw [div_le_iff₀ h500] at hε
    linarith
  have heps2 : (1 : ℝ) ≤ 250000 * (h : ℝ) ^ 2 * (R.eps : ℝ) ^ 2 := by nlinarith [hεh]
  have hepsH : (R.Hhi : ℝ) ≤ 250000 * (h : ℝ) ^ 2 * ((R.eps : ℝ) ^ 2 * (R.Hhi : ℝ)) := by
    nlinarith [heps2, hHhi0]
  have hEbig : (R.Hhi : ℝ) ≤ 250000 * (h : ℝ) ^ 2 * ((E : ℝ) + 1) := by
    have hstep : 250000 * (h : ℝ) ^ 2 * ((R.eps : ℝ) ^ 2 * (R.Hhi : ℝ))
        ≤ 250000 * (h : ℝ) ^ 2 * ((E : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hEfl]) (by positivity)
    linarith [hepsH, hstep]
  have hE0 : (0 : ℝ) ≤ (E : ℝ) := Nat.cast_nonneg _
  have hHle : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hlogmono : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) := Real.log_le_log hH0 hHle
  have hllmono : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log (R.Hhi : ℝ)) :=
    Real.log_le_log hlogH0 hlogmono
  have hllsub : Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (R.Hhi : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hsq : Real.log (R.Hhi : ℝ) ≤ 2 * Real.sqrt (R.Hhi : ℝ) - 2 :=
    cofk_log_le_two_sqrt hHhi0
  -- ⟦the charge, bought from the tower through `hsq` — NO log of a product⟧
  have hLcsq : Lc + 1 ≤ Real.sqrt (R.Hhi : ℝ) := by linarith
  have hv : (10 : ℝ) ^ 13 * (h : ℝ) ^ 2 ≤ Real.sqrt (R.Hhi : ℝ) := by
    have hid : ((10 : ℝ) ^ 13 * (h : ℝ) ^ 2) ^ 2 = (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 := by ring
    have h1 : Real.sqrt (((10 : ℝ) ^ 13 * (h : ℝ) ^ 2) ^ 2) ≤ Real.sqrt (R.Hhi : ℝ) :=
      Real.sqrt_le_sqrt (by rw [hid]; exact hHhi)
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hvsq : Real.sqrt (R.Hhi : ℝ) * Real.sqrt (R.Hhi : ℝ) = (R.Hhi : ℝ) :=
    Real.mul_self_sqrt hHhi0.le
  have hv0 : (0 : ℝ) ≤ Real.sqrt (R.Hhi : ℝ) := Real.sqrt_nonneg _
  have hprod : (10 : ℝ) ^ 13 * (h : ℝ) ^ 2 * Real.sqrt (R.Hhi : ℝ) ≤ (R.Hhi : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right hv hv0) (le_of_eq hvsq)
  have hlog4 : (1.3862 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9]
  have hlog2 : Real.log 2 ≤ 0.6932 := by linarith [Real.log_two_lt_d9]
  have hElog : (1.3862 : ℝ) * (E : ℝ) ≤ (E : ℝ) * Real.log 4 := by
    have h := mul_le_mul_of_nonneg_left hlog4 hE0
    linarith only [h]
  have hdebit : 12 * Real.log (Real.log (H : ℝ)) ≤ 24 * Real.sqrt (R.Hhi : ℝ) := by
    linarith only [hllmono, hllsub, hsq]
  have hlow : 2.7724 * (E : ℝ) - (Lc + 0.6932) - 24 * Real.sqrt (R.Hhi : ℝ)
      ≤ Real.log (A : ℝ) := by
    linarith only [hElog, hlogA, hdebit, hlog2, hhL]
  have hXpos : (0 : ℝ) < 10 ^ 6 * (h : ℝ) ^ 2 := by positivity
  have hmulL : (10 ^ 6 * (h : ℝ) ^ 2)
        * (2.7724 * (E : ℝ) - (Lc + 0.6932) - 24 * Real.sqrt (R.Hhi : ℝ))
      ≤ (10 ^ 6 * (h : ℝ) ^ 2) * Real.log (A : ℝ) :=
    mul_le_mul_of_nonneg_left hlow hXpos.le
  have hh2nn : (0 : ℝ) ≤ (h : ℝ) ^ 2 := by positivity
  have hLch2 : (0 : ℝ) ≤ (h : ℝ) ^ 2 * Lc := mul_nonneg hh2nn hL0
  have hsm1 : 10 ^ 6 * (h : ℝ) ^ 2 * (Lc + 0.6932) ≤ (R.Hhi : ℝ) := by
    have hstep : (10 : ℝ) ^ 13 * (h : ℝ) ^ 2 * (Lc + 1)
        ≤ (10 : ℝ) ^ 13 * (h : ℝ) ^ 2 * Real.sqrt (R.Hhi : ℝ) :=
      mul_le_mul_of_nonneg_left hLcsq (by positivity)
    linarith only [hstep, hprod, hLch2, hh2nn]
  have hhs : (0 : ℝ) ≤ (h : ℝ) ^ 2 * Real.sqrt (R.Hhi : ℝ) := by positivity
  have hsm2 : 24 * (10 ^ 6 * ((h : ℝ) ^ 2 * Real.sqrt (R.Hhi : ℝ))) ≤ (R.Hhi : ℝ) := by
    nlinarith only [hprod, hhs]
  have hfloor : (R.Hhi : ℝ) / (10 ^ 6 * (h : ℝ) ^ 2) ≤ Real.log (A : ℝ) := by
    rw [div_le_iff₀ hXpos]
    linarith only [hmulL, hEbig, hsm1, hsm2, hLch2]
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast h8
  have hAs : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hlogAs : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    Real.log_le_log (by linarith) hAs
  linarith

/-- `cofkL_mu_floor_h_b9` at generic `L` (`cofkL_mu_floor_L`) — **THE ONE STATEMENT OF THE
SEVENTEEN WHOSE CONCLUSION MOVES.**  The twin's `32` IS its cap: `log (10^6 · h²) = 6·log 10 +
2·log h ≤ 6 · 2.311 + 2 · 9 = 31.866 ≤ 32`.  At the charge the same reading is
`6·log 10 + 2·L ≤ 13.866 + 2·L`, so the floor reads `log H₊ − (14 + 2·L)` — the constant is
`13.866` rounded UP to `14`, a bound rounded toward slack, margin `0.134`, and the
`L`-coefficient is exactly `2` (`cofk_log_ten_le : log 10 ≤ 2.311`).  At `L = 9` this is
`14 + 18 = 32`, the twin's own numeral, so the sibling is a strict generalisation.
⚠️ This numeral is the rated supply's input at its `hmuF`/`hthrLL`/`hthr14`/`h2` sites.
SUPPLIER-SWAP `cofkL_logX_floor_L`.  BODY otherwise the twin's, verbatim. -/
theorem cofkL_mu_floor_L {R : ChowlaRegime} {h M H L q j A s : ℕ} (hh : 0 < h)
    {Lc : ℝ} (hL0 : 0 ≤ Lc) (hhL : Real.log (h : ℝ) ≤ Lc)
    (hb : SocketBaseLH h R M H L q j A s)
    (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ))
    (hHhi : (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 ≤ (R.Hhi : ℝ))
    (hH : (4000000 : ℝ) ≤ (H : ℝ))
    (hloL : (518 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    Real.log (R.Hhi : ℝ) - (14 + 2 * Lc) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hLh0 : (0 : ℝ) ≤ Real.log h := Real.log_nonneg hh1
  have hh2 : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith [hh1]
  have hh24 : (h : ℝ) ^ 2 ≤ (h : ℝ) ^ 4 := by nlinarith [hh2, sq_nonneg ((h : ℝ))]
  have hfl := cofkL_logX_floor_L hh hL0 hhL hb hε hHhi hH hloL
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by nlinarith [hHhi, hh2, hh24]
  have hXpos : (0 : ℝ) < (10 : ℝ) ^ 6 * (h : ℝ) ^ 2 := by positivity
  have hbigpos : (0 : ℝ) < (R.Hhi : ℝ) / ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2) := div_pos hHhi0 hXpos
  have hstep : Real.log ((R.Hhi : ℝ) / ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2))
      ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    Real.log_le_log hbigpos hfl
  have hsplit : Real.log ((R.Hhi : ℝ) / ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2))
      = Real.log (R.Hhi : ℝ) - Real.log ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2) := by
    rw [Real.log_div (ne_of_gt hHhi0) (ne_of_gt hXpos)]
  have h106 : Real.log ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2) ≤ 14 + 2 * Lc := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    linarith [cofk_log_ten_le, hhL, hLh0]
  rw [hsplit] at hstep
  linarith

/-- `cofkL_X_ge_expexp_h_b9` at generic `L` (`cofkL_X_ge_expexp_L`) — SUPPLIER-SWAP
(`cofkL_logX_floor_L`).  The twin spends its cap NOWHERE in its own body — only in the supplier
call — so the charge and the tower ride through and no numeral moves; its own
`3 ≤ H₊ / (10^6 · h²)` step reads `hHhi` and `h² ≤ h⁴` alone.  BODY: the twin's, verbatim. -/
theorem cofkL_X_ge_expexp_L {R : ChowlaRegime} {h M H L q j A s : ℕ} (hh : 0 < h)
    {Lc : ℝ} (hL0 : 0 ≤ Lc) (hhL : Real.log (h : ℝ) ≤ Lc)
    (hb : SocketBaseLH h R M H L q j A s)
    (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ))
    (hHhi : (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 ≤ (R.Hhi : ℝ))
    (hH : (4000000 : ℝ) ≤ (H : ℝ))
    (hloL : (518 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    Real.exp (Real.exp 1) ≤ (((A + s : ℕ)) : ℝ) := by
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hh2 : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith [hh1]
  have hh24 : (h : ℝ) ^ 2 ≤ (h : ℝ) ^ 4 := by nlinarith [hh2, sq_nonneg ((h : ℝ))]
  have hfl := cofkL_logX_floor_L hh hL0 hhL hb hε hHhi hH hloL
  have h8 : 0 < A := hb.2.2.2.2.2.2.2.1
  have hApos : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by
    have : 1 ≤ A + s := by omega
    have h : (1 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by exact_mod_cast this
    linarith
  have hXpos : (0 : ℝ) < (10 : ℝ) ^ 6 * (h : ℝ) ^ 2 := by positivity
  have he : Real.exp 1 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have h4 : (3 : ℝ) ≤ (R.Hhi : ℝ) / ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2) := by
      rw [le_div_iff₀ hXpos]; nlinarith [hHhi, hh24]
    linarith
  have h := Real.exp_le_exp.mpr he
  rwa [Real.exp_log hApos] at h

set_option maxHeartbeats 1000000 in
-- as the twin: the socket floors and the quintic's logarithm elaborate in one block
/-- `cofkL_scale_gate_at_socket_h_b9` at generic `L` (`cofkL_scale_gate_at_socket_L`) —
SUPPLIER-SWAP (`cofkL_mu_floor_L`, whose floor now reads `log H₊ − (14 + 2·L)`, and
`cofkL_logX_floor_L`).  TWO cap sites, both paid by `cofk_tower_logfloor_L` through
`hLH8L : 10^8 · (1 + L) ≤ log H₊`:
* `hHhi14` needs `26·log 10 + 4·L ≤ 60.086 + 4·L ≤ log H₊`; the tower gives `10^8 + 10^8·L`;
* `hchain` needs `1899 + 5·(L + 12·Λ) ≤ log H₊ − (14 + 2·L)`, and with `Λ ≤ 2·√(log H₊) − 2` and
  `10^4 · √(log H₊) ≤ log H₊` that is `1793 + 7·L ≤ 0.988 · log H₊` — clear by `9.9·10^7` on the
  constant and by `10^8 / 7` on the `L`-coefficient.
So `hlo` gains the affine term and NOTHING else moves; the conclusion is the twin's.  BODY
otherwise the twin's, verbatim. -/
theorem cofkL_scale_gate_at_socket_L {R : ChowlaRegime} {h M H L q j A s : ℕ} [NeZero q]
    (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc) (hhL : Real.log (h : ℝ) ≤ Lc)
    (hb : SocketBaseLH h R M H L q j A s)
    (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ))
    (hloL : (518 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (harc : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H) :
    32 * Salt.SW.diskConst q / goldenL1 q ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have h1 : R.Hlo ≤ H := hb.1
  have h2 : H ≤ R.Hhi := hb.2.1
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hlogHlo : (14 : ℝ) ≤ Real.log (R.Hlo : ℝ) := cofk_log_big hHlo4
  -- ⟦THE CHARGE'S PAYER — the `518`-tower, in place of the twin's `exp 518 ≥ 10^8`⟧
  obtain ⟨hlolo, hmono1, hmono2⟩ := cofk_tower_logfloor_L hL0 hb hloL
  have hlogHlo8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hlo : ℝ) := by linarith
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hH4 : (4000000 : ℝ) ≤ (H : ℝ) := by linarith
  have hHlo0 : (0 : ℝ) < (R.Hlo : ℝ) := by linarith
  have hlogH : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) := hmono1
  have hlogHhi : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) := hmono2
  have hLH8L : (10 : ℝ) ^ 8 * (1 + Lc) ≤ Real.log (R.Hhi : ℝ) := by linarith
  have hLH8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hhi : ℝ) := by nlinarith [hL0]
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hHhi14 : (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 ≤ (R.Hhi : ℝ) := by
    have hLhh : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
    have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    have hlogle : Real.log ((10 : ℝ) ^ 26 * (h : ℝ) ^ 4) ≤ Real.log (R.Hhi : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      linarith [cofk_log_ten_le]
    have h2' := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log (by positivity), Real.exp_log hHhi0] at h2'
  have hHe : Real.exp 1 ≤ Real.log (H : ℝ) := by
    have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    linarith
  -- ⟦the `μ`-floor and the scale floor, at the INFLATED socket and the charge⟧
  have hmu := cofkL_mu_floor_L hh hL0 hhL hb hε hHhi14 hH4 hloL
  have hfl := cofkL_logX_floor_L hh hL0 hhL hb hε hHhi14 hH4 hloL
  have hlogXpos : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have hbig : (0 : ℝ) < (R.Hhi : ℝ) / ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2) := by positivity
    linarith
  -- ⟦`loglog H` against `√(log H₊)`⟧
  have hLH0 : (0 : ℝ) < Real.log (R.Hhi : ℝ) := by linarith
  have hΛ : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log (R.Hhi : ℝ)) :=
    Real.log_le_log (by linarith) hlogHhi
  have hlogLH : Real.log (Real.log (R.Hhi : ℝ)) ≤ 2 * Real.sqrt (Real.log (R.Hhi : ℝ)) - 2 :=
    cofk_log_le_two_sqrt hLH0
  have hv : (10 : ℝ) ^ 4 ≤ Real.sqrt (Real.log (R.Hhi : ℝ)) := by
    have h1' : Real.sqrt (((10 : ℝ) ^ 4) ^ 2) ≤ Real.sqrt (Real.log (R.Hhi : ℝ)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by norm_num)] at h1'
  have hv0 : (0 : ℝ) ≤ Real.sqrt (Real.log (R.Hhi : ℝ)) := Real.sqrt_nonneg _
  have hvsq : Real.sqrt (Real.log (R.Hhi : ℝ)) * Real.sqrt (Real.log (R.Hhi : ℝ))
      = Real.log (R.Hhi : ℝ) := Real.mul_self_sqrt hLH0.le
  have hprodv : (10 : ℝ) ^ 4 * Real.sqrt (Real.log (R.Hhi : ℝ)) ≤ Real.log (R.Hhi : ℝ) := by
    nlinarith [hv, hvsq, hv0]
  -- ⟦the quintic, and its logarithm — the inflation adds `5·L`⟧
  have hlogq : Real.log q ≤ Real.log h + 12 * Real.log (Real.log (H : ℝ)) :=
    log_le_of_le_arcDen_h hh hHe harc
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne q); exact_mod_cast this
  have hqpos : (0 : ℝ) < 1900 * (q : ℝ) ^ 5 := by positivity
  have hlogpoly : Real.log (1900 * (q : ℝ) ^ 5) = Real.log 1900 + 5 * Real.log q := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlog1900 : Real.log 1900 ≤ 1899 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1900 by norm_num)
    linarith
  have hchain : Real.log (1900 * (q : ℝ) ^ 5)
      ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
    rw [hlogpoly]; linarith
  have hfin : 1900 * (q : ℝ) ^ 5 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h := Real.exp_le_exp.mpr hchain
    rwa [Real.exp_log hqpos, Real.exp_log hlogXpos] at h
  exact le_trans scaleGate_le_quintic hfin

set_option maxHeartbeats 1000000 in
-- as the twin: the three legs and the square-root close elaborate in one block
/-- `cofkL_threshold_at_socket_rated_h_b9` at generic `L` (`cofkL_threshold_at_socket_rated_L`) —
SUPPLIER-SWAP (`cofkL_mu_floor_L`): the typed `hμ` carries its floor `log H₊ − 32 ↦
log H₊ − (14 + 2·L)`, and `hHhi14` pays `26·log 10 + 4·L` as in the scale gate.  The two places
the moved floor is re-spent both keep their margin under the `518`-tower:
* `hμbig : 10^8 − 32 ≤ μ` survives because `μ ≥ 10^8·(1+L) − 14 − 2·L = 10^8 − 14 +
  (10^8 − 2)·L`, and the `L`-part is nonnegative — the `320 ≤ √μ` floor is untouched;
* `hmargin` becomes `2430.5 + 1.5·L < 0.072 · log H₊`, and the tower gives
  `0.072 · log H₊ ≥ 7.2·10^6 · (1 + L)` — slack `7.2·10^6` on the constant and `4.8·10^6×` on
  the `L`-coefficient.
The conclusion is the twin's.  BODY otherwise the twin's, verbatim. -/
theorem cofkL_threshold_at_socket_rated_L {R : ChowlaRegime} {h M H L q j A s : ℕ}
    {Kvt D : ℝ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc) (hhL : Real.log (h : ℝ) ≤ Lc)
    (hb : SocketBaseLH h R M H L q j A s)
    (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ))
    (hloL : (518 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hcush : 32 * Kvt + 32 * D ≤ Real.log (R.Hhi : ℝ) / 4) :
    40 * Real.log (Real.log (Real.log (((A + s : ℕ)) : ℝ)))
        + 1900 * Real.log (Real.log (H : ℝ))
        + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
        + 2300 + 32 * Kvt + 32 * D
      < Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have h1 : R.Hlo ≤ H := hb.1
  have h2 : H ≤ R.Hhi := hb.2.1
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hlogHlo : (14 : ℝ) ≤ Real.log (R.Hlo : ℝ) := cofk_log_big hHlo4
  -- ⟦THE CHARGE'S PAYER — the `518`-tower⟧
  obtain ⟨hlolo, hmono1, hmono2⟩ := cofk_tower_logfloor_L hL0 hb hloL
  have hlogHlo8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hlo : ℝ) := by linarith
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hH4 : (4000000 : ℝ) ≤ (H : ℝ) := by linarith
  have hHlo0 : (0 : ℝ) < (R.Hlo : ℝ) := by linarith
  have hlogH : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) := hmono1
  have hlogHhi : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) := hmono2
  have hLH8L : (10 : ℝ) ^ 8 * (1 + Lc) ≤ Real.log (R.Hhi : ℝ) := by linarith
  have hLH8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hhi : ℝ) := by nlinarith [hL0]
  have hlogH1 : (1 : ℝ) < Real.log (H : ℝ) := by linarith
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hHhi14 : (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 ≤ (R.Hhi : ℝ) := by
    have hLhh : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
    have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    have hlogle : Real.log ((10 : ℝ) ^ 26 * (h : ℝ) ^ 4) ≤ Real.log (R.Hhi : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      linarith [cofk_log_ten_le]
    have h2' := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log (by positivity), Real.exp_log hHhi0] at h2'
  -- ⟦THE `μ`-FLOOR, at the INFLATED socket and the charge⟧
  have hmu := cofkL_mu_floor_L hh hL0 hhL hb hε hHhi14 hH4 hloL
  set μ : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hμdef
  set LH : ℝ := Real.log (R.Hhi : ℝ) with hLHdef
  have hμ : LH - (14 + 2 * Lc) ≤ μ := hmu
  have hμbig : (10 : ℝ) ^ 8 - 32 ≤ μ := by linarith
  have hμ0 : (0 : ℝ) < μ := by nlinarith
  -- ⟦the `logloglog` leg⟧ `40·log μ ≤ μ/4`
  have hlogμ : Real.log μ ≤ 2 * Real.sqrt μ - 2 := cofk_log_le_two_sqrt hμ0
  have hsμ : (320 : ℝ) ≤ Real.sqrt μ := by
    have h1' : Real.sqrt ((320 : ℝ) ^ 2) ≤ Real.sqrt μ := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by norm_num)] at h1'
  have hsμ0 : (0 : ℝ) ≤ Real.sqrt μ := Real.sqrt_nonneg _
  have hsμsq : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ0.le
  have hprodμ : 320 * Real.sqrt μ ≤ μ := by nlinarith [hsμ, hsμsq, hsμ0]
  have hleg1 : 40 * Real.log μ ≤ μ / 4 := by linarith
  -- ⟦the `loglog H` legs⟧ dominated by `4280·√(log H₊)`
  have hΛ : Real.log (Real.log (H : ℝ)) ≤ Real.log LH :=
    Real.log_le_log (by linarith) hlogHhi
  have hLH0 : (0 : ℝ) < LH := by linarith
  have hlogLH : Real.log LH ≤ 2 * Real.sqrt LH - 2 := cofk_log_le_two_sqrt hLH0
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := Real.log_nonneg (by linarith)
  have hv : (10 : ℝ) ^ 4 ≤ Real.sqrt LH := by
    have h1' : Real.sqrt (((10 : ℝ) ^ 4) ^ 2) ≤ Real.sqrt LH := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by norm_num)] at h1'
  have hv0 : (0 : ℝ) ≤ Real.sqrt LH := Real.sqrt_nonneg _
  have hvsq : Real.sqrt LH * Real.sqrt LH = LH := Real.mul_self_sqrt hLH0.le
  have hprodv : (10 : ℝ) ^ 4 * Real.sqrt LH ≤ LH := by nlinarith [hv, hvsq, hv0]
  have hlogterm : Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
      ≤ 6 + 24 * Real.sqrt LH := by
    have hpos : (0 : ℝ) < 7 + 12 * Real.log (Real.log (H : ℝ)) := by linarith
    have hsub : Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
        ≤ 7 + 12 * Real.log (Real.log (H : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos hpos
    linarith
  have hleg2 : 1900 * Real.log (Real.log (H : ℝ))
      + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ))) + 2300
      ≤ 4280 * Real.sqrt LH + 2420 := by linarith
  -- ⟦the close — linear once the tower is in hand⟧
  have hmargin : 4280 * Real.sqrt LH + 2420 + LH / 4 < μ / 2 + μ / 4 := by
    linarith [hprodv, hμ, hLH8L, hL0]
  linarith

set_option maxHeartbeats 1000000 in
-- as the twin: the design floor, the budget and the four page calls elaborate in one block
/-- `cofkL_capFreeFloor_at_socket_rated_uniform_h_b9` at generic `L`
(`cofkL_capFreeFloor_at_socket_rated_uniform_L`) — SUPPLIER-SWAP of all four `h`-pages
(`capFreeFloor3_pieceDatum_arcDen_rated_L`, `cofkL_X_ge_expexp_L`,
`cofkL_scale_gate_at_socket_L`, `cofkL_threshold_at_socket_rated_L`), and **the ONE page of the
seventeen whose tower coefficient is not `1`.**
⛔ `k = 6`, and it is FORCED by the twin's own `hbud`, which this page DISCHARGES rather than
takes: `hbud` reads `156·log h` against `28·loglog H`, so at the charge it needs
`loglog H ≥ (156/28)·L = 5.572·L` — the weakest integer `k` is `6`, and the inner `hlo` therefore
reads `518 + 6·L ≤ loglog H₋`.  At `k = 6` the budget is `156·L + 8·log 2 ≤ 14504 + 168·L + 84`,
clear by `12·L + 14582` (the twin's own reading was `1409.5` against `14504`).
The other three pages need only `518 + L`, which follows by `linarith` since `L ≥ 0`, so the
root supplies ONE hypothesis for the whole wave.  `hHhi14` pays `26·log 10 + 4·L` as before.
The conclusion is the twin's.  BODY otherwise the twin's, verbatim. -/
theorem cofkL_capFreeFloor_at_socket_rated_uniform_L (h : ℕ) (hh : 0 < h)
    {Lc : ℝ} (hL0 : 0 ≤ Lc) (hhL : Real.log (h : ℝ) ≤ Lc) :
    ∃ Z δ Kvt : ℝ, 1 ≤ Z ∧ 0 < δ ∧ 0 ≤ Kvt ∧
      ∀ (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} (χ : DirichletCharacter ℂ q),
        SocketBaseLH h R M H L q j A s → 1 ≤ M →
        (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ) →
        (518 : ℝ) + 6 * Lc ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        32 * Kvt + 32 * (2 * Real.log (M : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
        ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
            (calQK (AdoorL M) (s13GK K M) M)) (((A + s : ℕ)) : ℝ) := by
  obtain ⟨Z, δ, Kvt, hZ, hδ, hK0, hK⟩ := capFreeFloor3_pieceDatum_arcDen_rated_L h hh hL0 hhL
  refine ⟨Z, δ, Kvt, hZ, hδ, hK0, ?_⟩
  intro K R M H L q j A s χ hb hM hε hlo6 hcush 𝒥 h𝒥
  have hlo : (518 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)) := by linarith
  have hq0 : 0 < q := hb.2.2.2.1
  haveI : NeZero q := ⟨by omega⟩
  have h1 : R.Hlo ≤ H := hb.1
  have h2 : H ≤ R.Hhi := hb.2.1
  have harc : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H := hb.2.2.2.2.1
  -- ⟦the design floor⟧
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hH4 : (4000000 : ℝ) ≤ (H : ℝ) := by linarith
  have hlogH : (14 : ℝ) ≤ Real.log (H : ℝ) := cofk_log_big hH4
  have hlogHe : Real.exp 1 ≤ Real.log (H : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  -- ⟦`H₊` above the charge's floor⟧
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hlogHlo : (14 : ℝ) ≤ Real.log (R.Hlo : ℝ) := cofk_log_big hHlo4
  obtain ⟨hlolo, hmono1, hmono2⟩ := cofk_tower_logfloor_L hL0 hb hlo
  have hlogHlo8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hlo : ℝ) := by linarith
  have hlogmono : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) := hmono1
  have hlogHhi : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) := hmono2
  have hLH8L : (10 : ℝ) ^ 8 * (1 + Lc) ≤ Real.log (R.Hhi : ℝ) := by linarith
  have hLH8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hhi : ℝ) := by nlinarith [hL0]
  have hHhi14 : (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 ≤ (R.Hhi : ℝ) := by
    have hLhh : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
    have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    have hlogle : Real.log ((10 : ℝ) ^ 26 * (h : ℝ) ^ 4) ≤ Real.log (R.Hhi : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      linarith [cofk_log_ten_le]
    have h2' := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log (by positivity), Real.exp_log hHhi0] at h2'
  -- ⟦THE BUDGET, DISCHARGED FROM THE SOCKET'S OWN `Λ`-FLOOR AT `k = 6` — no binder added⟧
  have hΛ518 : (518 : ℝ) + 6 * Lc ≤ Real.log (Real.log (H : ℝ)) := by
    have hmono : Real.log (Real.log (R.Hlo : ℝ)) ≤ Real.log (Real.log (H : ℝ)) :=
      Real.log_le_log (by linarith) hlogmono
    linarith
  have hlognn : (0 : ℝ) ≤ Real.log (7 + 12 * Real.log (Real.log (H : ℝ))) :=
    Real.log_nonneg (by linarith)
  have hbud : 156 * Real.log h + 8 * Real.log 2
      ≤ 28 * Real.log (Real.log (H : ℝ))
        + 4 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ))) + 84 := by
    have h2lt := Real.log_two_lt_d9
    linarith
  -- ⟦the scale gate, the debit page, the threshold — all at the INFLATED socket and the charge⟧
  have hXee : Real.exp (Real.exp 1) ≤ (((A + s : ℕ)) : ℝ) :=
    cofkL_X_ge_expexp_L hh hL0 hhL hb hε hHhi14 hH4 hlo
  have hgate : 32 * Salt.SW.diskConst q / goldenL1 q ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    cofkL_scale_gate_at_socket_L hh hL0 hhL hb hε hlo harc
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hD0 : (0 : ℝ) ≤ 2 * Real.log (M : ℝ) + Real.log 4 + 50 := by
    have h1' : (0 : ℝ) ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
    have h2' : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hdebit := cofkL_debit_bound K M (((A + s : ℕ)) : ℝ) hM 𝒥 h𝒥
  have hthr := cofkL_threshold_at_socket_rated_L (Kvt := Kvt)
    (D := 2 * Real.log (M : ℝ) + Real.log 4 + 50) hh hL0 hhL hb hε hlo hcush
  exact hK q H χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 𝒥
    (((A + s : ℕ)) : ℝ) (2 * Real.log (M : ℝ) + Real.log 4 + 50)
    hlogHe harc hbud hXee hD0 hgate hdebit hthr

/-! ## §W5 — the rated supply's root at generic `Lc`

Wave 5, one declaration: the rated supply's ROOT, which is the single consumer of wave 4's
nineteen `_L` siblings.  It carries the whole rung-2 charge in TWO binders — the tower
`518 + 6·Lc` and the threshold `cofkRThr … + 2·Lc` — and its body is the twin's, verbatim, with
the six supplier calls swapped for their `_L` siblings and the mu-floor's four `32`-sites read at
the charge.  Nothing in §1–§W4 moves. -/

set_option maxHeartbeats 24000000 in
-- as the twin: the ~35-binder instantiation of `m4_supplier_complete` and the
-- seventeen discharged conjuncts elaborate in ONE context
/-- `cofkR_cofactorSupply_L_gk_rated_h_b9` at generic `L` (`cofkR_cofactorSupply_L_gk_rated_L`) —
NUMERAL-LIFT of all six sub-suppliers to their `_L` siblings
(`cofkL_capFreeFloor_at_socket_rated_uniform_L`, `cofkL_socket_floors_L`, `s13CapGrid_mu_2000_L`,
`s13CapGrid_Lambda_lo_L`, `cofkL_mu_floor_L`, `capfloor_core_L`).  TWO binders carry the whole
charge; no other numeral in the body moves.
⚖️ **THE TOWER, `518 + 6·L`.**  `k = 6` is the uniform page's own, forced by the `hbud` that page
DISCHARGES.  The other five need only `518 + L` (`cofkL_socket_floors_L`, `cofkL_mu_floor_L`) or
`50 + L` (`s13CapGrid_mu_2000_L`, `s13CapGrid_Lambda_lo_L`, `capfloor_core_L`), and both follow
from the one binder by `linarith` on `L ≥ 0` — ONE hypothesis for the whole wave.
⛔ **THE THRESHOLD, `cofkRThr … + 2·L`, AND `k = 2` IS FORCED.**  `cofkL_mu_floor_L`'s conclusion
is `log H₊ − (14 + 2·L)`, so `hmuF` carries `14 + 2·L`.  Along
`cofkRThr + k·L ≤ log H₋ ≤ log H₊ ≤ loglog Xd + 14 + 2·L` the threshold reads
`cofkRThr ≤ loglog Xd + 14 + (2 − k)·L`, so `hthrLL`, `hthr14` and `h2` carry the constant `14`
plus a residue `(2 − k)·L`.  `hstep` closes `6666 + 3·log Z ≤ loglog Xd · 2θ₂₉₃` through
`loglog Xd / 150`, where the `log Z` terms cancel EXACTLY (`450/150 = 3`), so it needs
`(10^6 − 14 − (2 − k)·L)/150 ≥ 6666`, i.e. `(2 − k)·L ≤ 100 − 14 = 86`.  At `k = 2` that is
`0 ≤ 86` at EVERY `L`, margin `(10^6 − 14)/150 − 6666 = 6666.5733… − 6666 = 0.5733` — WIDER than
the twin's own `0.4533` from `(10^6 − 32)/150`; at `k = 1` it is spent at `L = 86`, at `k = 0` at
`L = 43`.  So `k = 2` is the smallest that closes uniformly in `L`.
`θ₂₉₃` is not widened and `6666` does not move.
⚠️ The two binders are STRICTLY STRONGER than the twin's at every `L > 0` — at `L = 9` they ask
`572` and `cofkRThr + 18` where the twin asked `518` and `cofkRThr` — which is the price of
genericity in `h`; `hmuF` there reads `14 + 18 = 32`, the twin's own numeral.
BODY otherwise the twin's, verbatim. -/
theorem cofkR_cofactorSupply_L_gk_rated_L (h : ℕ) (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) :
    ∃ (Xsk Y0 Kvt Cb : ℝ),
      0 < Xsk ∧ pin2Gate ≤ Y0 ∧ 0 ≤ Kvt ∧ 0 ≤ Cb ∧
      ∀ (K : ℕ) (Cq : ℝ) (R : ChowlaRegime) (M : ℕ), 1 ≤ M → 0 < Cq →
        (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ) →
        (518 : ℝ) + 6 * Lc ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        loglogFloor50 ≤ R.Hlo →
        cofkRThr Cq Cb Xsk Y0 + 2 * Lc ≤ Real.log (R.Hlo : ℝ) →
        32 * Kvt + 32 * (2 * Real.log (M : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
        S16CofactorSupply_LH_gk h K Cq R M := by
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  obtain ⟨Y0, hY0pin, hfarclose⟩ := farErr34_local_closes
  obtain ⟨_Z, _δ, Kvt, _, _, hKvt0, hKvt⟩ :=
    cofkL_capFreeFloor_at_socket_rated_uniform_L h hh hL0 hhL
  obtain ⟨Cb, hCb0, hCbound⟩ := exists_shortIntervalDatum
  refine ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, ?_⟩
  intro K Cq R M hM hCq hε hlo hfl hgate hcush H Lw q j A s hb T hTlo hThi
  -- the five pages below need only `518 + L` / `50 + L`; `L ≥ 0` supplies both from `hlo`
  have hloL : (518 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)) := by linarith
  have hflL : (50 : ℝ) + Lc ≤ Real.log (Real.log (R.Hlo : ℝ)) := by linarith
  have hq0 : 0 < q := hb.2.2.2.1
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨hH4, hHhi14⟩ := cofkL_socket_floors_L hh hL0 hhL hb hloL
  -- ⟦THE SOCKET'S OWN SCALE FACTS⟧
  have h2j0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hAs1 : 0 < A + s := by have := hb.2.2.2.2.2.2.2.1; omega
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs1
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hAsR h2j0) hTlo
  have hTflo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ 2 * T := by linarith
  have hmu2000 : (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    s13CapGrid_mu_2000_L hh hL0 hhL hfl hb hflL
  have hLam : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    s13CapGrid_Lambda_lo_L hh hL0 hhL hfl hb hflL
  have hmuF : Real.log (R.Hhi : ℝ) - (14 + 2 * Lc)
      ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    cofkL_mu_floor_L hh hL0 hhL hb hε hHhi14 hH4 hloL
  obtain ⟨-, -, hTpos, hlogT⟩ :=
    capfloor_core_L hh hL0 hhL hfl hb (Nat.le_add_right A s) hTflo hflL
  have hPQ : s13BandP (A + s) ≤ s13BandQ (A + s) := s13CapGrid_P_le_Q hmu2000 hLam
  have hQpos : 0 < s13BandQ (A + s) := s13CapGrid_Q_pos hmu2000
  have hfloorχ : ∀ χ : DirichletCharacter ℂ q, ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M)) (((A + s : ℕ)) : ℝ) :=
    fun χ => hKvt K χ hb hM hε hlo hcush
  -- ⟦THE BLOCK SCALE, NAMED ONCE⟧
  obtain ⟨Xd, hXd⟩ : ∃ n : ℕ, A + s = n := ⟨A + s, rfl⟩
  rw [hXd] at hmu2000 hLam hmuF hPQ hQpos hfloorχ hTflo hThi hlogT hAsR ⊢
  -- ⟦THE SCALE ARITHMETIC⟧
  have hLg0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hLgexp : Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ))) = Real.log ((Xd : ℕ) : ℝ) :=
    Real.exp_log hLg0
  have h21 : (10 : ℝ) ^ (21 : ℕ) = 1000000000000000000000 := by norm_num
  rw [h21] at hLam
  have hLg166 : Real.exp 166 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h := Real.exp_le_exp.mpr (show (166 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) by
      linarith)
    rwa [hLgexp] at h
  have hexp165 : (2 : ℝ) ≤ Real.exp 165 := by linarith [Real.add_one_le_exp (165 : ℝ)]
  have hexp166 : Real.exp 166 = Real.exp 1 * Real.exp 165 := by rw [← Real.exp_add]; norm_num
  have he27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hball : 2 * Real.exp 165 + 2 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    nlinarith [hLg166, hexp166, hexp165, he27]
  have hLgbig : (10 : ℝ) ^ 6 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h : (10 : ℝ) ^ 6 ≤ Real.exp 166 := by
      have h1 : (1 : ℝ) + 41.5 ≤ Real.exp 41.5 := by
        linarith [Real.add_one_le_exp (41.5 : ℝ)]
      have h2 : Real.exp 41.5 * Real.exp 41.5 = Real.exp 83 := by
        rw [← Real.exp_add]; norm_num
      have h3 : Real.exp 83 * Real.exp 83 = Real.exp 166 := by rw [← Real.exp_add]; norm_num
      have h4 : (1806 : ℝ) ≤ Real.exp 83 := by nlinarith [h1, h2]
      nlinarith [h3, h4]
    linarith
  -- ⟦THE THRESHOLD, READ AT THE SOCKET⟧
  have hHloHhi : Real.log (R.Hlo : ℝ) ≤ Real.log (R.Hhi : ℝ) := by
    have h1 : R.Hlo ≤ H := hb.1
    have h2 : H ≤ R.Hhi := hb.2.1
    have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
    have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
    have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
    exact Real.log_le_log (by linarith) (by linarith)
  have hthrLL : cofkRThr Cq Cb Xsk Y0 - 14
      ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by linarith
  have hZ1 : (1 : ℝ) ≤ 1 + Cq + cofkRConst Cb := by
    linarith [cofkRConst_pos hCb0]
  have hlogZ0 : (0 : ℝ) ≤ Real.log (1 + Cq + cofkRConst Cb) := Real.log_nonneg hZ1
  have hY00 : (0 : ℝ) < Y0 := lt_of_lt_of_le pin2Gate_pos hY0pin
  have hthrpieces : Xsk ≤ cofkRThr Cq Cb Xsk Y0 ∧ Y0 ≤ cofkRThr Cq Cb Xsk Y0 := by
    rw [cofkRThr]
    constructor <;> nlinarith [hlogZ0, hY00, hXsk0]
  -- `log X ≥ (loglog X)²/4`, the one quadratic the constant-absorption uses
  have hquad : Real.log (Real.log ((Xd : ℕ) : ℝ)) ^ 2 / 4 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h1 : 1 + Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2
        ≤ Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2) := by
      linarith [Real.add_one_le_exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2)]
    have h2 : Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2)
        * Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2)
        = Real.log ((Xd : ℕ) : ℝ) := by
      rw [← Real.exp_add, show Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2
        + Real.log (Real.log ((Xd : ℕ) : ℝ)) / 2
        = Real.log (Real.log ((Xd : ℕ) : ℝ)) by ring, hLgexp]
    nlinarith [h1, h2, hLam]
  have habs : ∀ z : ℝ, 0 < z → z ≤ cofkRThr Cq Cb Xsk Y0 →
      Real.log z ≤ Real.log ((Xd : ℕ) : ℝ) / 4 := by
    intro z hz0 hzthr
    have hlz : Real.log z ≤ z := by
      linarith [Real.log_le_sub_one_of_pos hz0]
    have hthr14 : cofkRThr Cq Cb Xsk Y0 ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) + 14 := by
      linarith
    nlinarith [hquad, hLam, hlz, hzthr, hthr14]
  have hXskgate : Xsk ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) := by
    have h := habs Xsk hXsk0 hthrpieces.1
    have h2 := Real.exp_le_exp.mpr h
    rwa [Real.exp_log hXsk0] at h2
  have hY0gate : Y0 ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) := by
    have h := habs Y0 hY00 hthrpieces.2
    have h2 := Real.exp_le_exp.mpr h
    rwa [Real.exp_log hY00] at h2
  -- ⟦THE GRADING GATE⟧
  have hgradegate : 1728 * Cq * (4 * cofkRConst Cb) ^ 2
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (2 * theta293) := by
    have hθ300 : (1 : ℝ) / 300 ≤ theta293 := by
      have hpos : (0 : ℝ) < 32 * (3 * Real.exp 1 + 1) := by nlinarith
      rw [theta293, le_div_iff₀ hpos]
      nlinarith [Real.exp_one_lt_d9]
    have hpow : (Real.log ((Xd : ℕ) : ℝ)) ^ (2 * theta293)
        = Real.exp (Real.log (Real.log ((Xd : ℕ) : ℝ)) * (2 * theta293)) := by
      rw [Real.rpow_def_of_pos hLg0]
    have hstep : (6666 : ℝ) + 3 * Real.log (1 + Cq + cofkRConst Cb)
        ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) * (2 * theta293) := by
      have hLL0 : (0 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by linarith
      have h1 : Real.log (Real.log ((Xd : ℕ) : ℝ)) / 150
          ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) * (2 * theta293) := by
        nlinarith [hθ300, hLL0]
      have h2 : (10 : ℝ) ^ 6 + 450 * Real.log (1 + Cq + cofkRConst Cb) - 14
          ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by
        have := hthrLL
        rw [cofkRThr] at this
        linarith
      linarith
    have hZ3 : Real.exp ((6666 : ℝ) + 3 * Real.log (1 + Cq + cofkRConst Cb))
        = Real.exp 6666 * (1 + Cq + cofkRConst Cb) ^ 3 := by
      rw [Real.exp_add]
      congr 1
      rw [show (3 : ℝ) * Real.log (1 + Cq + cofkRConst Cb)
        = Real.log ((1 + Cq + cofkRConst Cb) ^ 3) by
          rw [Real.log_pow]; push_cast; ring]
      exact Real.exp_log (pow_pos (by linarith) 3)
    have hbig : Real.exp 6666 * (1 + Cq + cofkRConst Cb) ^ 3
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (2 * theta293) := by
      rw [hpow, ← hZ3]
      exact Real.exp_le_exp.mpr hstep
    have he6666 : (27648 : ℝ) ≤ Real.exp 6666 := by
      have h1 : (1 : ℝ) + 3333 ≤ Real.exp 3333 := by
        linarith [Real.add_one_le_exp (3333 : ℝ)]
      have h2 : Real.exp 3333 * Real.exp 3333 = Real.exp 6666 := by
        rw [← Real.exp_add]; norm_num
      nlinarith
    have hRc0 : (0 : ℝ) < cofkRConst Cb := cofkRConst_pos hCb0
    have hCqZ : Cq ≤ 1 + Cq + cofkRConst Cb := by linarith
    have hRZ : cofkRConst Cb ^ 2 ≤ (1 + Cq + cofkRConst Cb) ^ 2 := by nlinarith
    have hcube : Cq * cofkRConst Cb ^ 2 ≤ (1 + Cq + cofkRConst Cb) ^ 3 := by
      nlinarith [hCqZ, hRZ, hCq.le, hRc0, hZ1]
    have hid : 1728 * Cq * (4 * cofkRConst Cb) ^ 2 = 27648 * (Cq * cofkRConst Cb ^ 2) := by
      ring
    rw [hid]
    have hZ0 : (0 : ℝ) ≤ (1 + Cq + cofkRConst Cb) ^ 3 := pow_nonneg (by linarith) 3
    calc 27648 * (Cq * cofkRConst Cb ^ 2)
        ≤ 27648 * (1 + Cq + cofkRConst Cb) ^ 3 := by linarith
      _ ≤ Real.exp 6666 * (1 + Cq + cofkRConst Cb) ^ 3 := by nlinarith [he6666, hZ0]
      _ ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (2 * theta293) := hbig
  -- ⟦THE BAND⟧
  have hθ0 : (0 : ℝ) < theta293 := theta293_pos
  have hθ32 : theta293 ≤ 1 / 32 := theta293_lt_one_div_32.le
  have hLX : Real.exp 1 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have hLe2 : Real.exp 2 ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have hH1 : (1 : ℝ) ≤ H83 ((Xd : ℕ) : ℝ) theta293 := by
    rw [H83]; exact Real.one_le_rpow (by linarith) hθ0.le
  have hH0 : (0 : ℝ) < H83 ((Xd : ℕ) : ℝ) theta293 := by linarith
  have hPlow : P83 ((Xd : ℕ) : ℝ) theta293 ≤ ((s13BandP Xd : ℕ) : ℝ) := s13CapGrid_P_low Xd
  have hQhigh : ((s13BandQ Xd : ℕ) : ℝ) ≤ Q83 ((Xd : ℕ) : ℝ) := s13CapGrid_Q_high Xd
  have hQ1 : 1 ≤ s13BandQ Xd := hQpos
  have hP83pos : (0 : ℝ) < P83 ((Xd : ℕ) : ℝ) theta293 := by rw [P83]; exact Real.exp_pos _
  have hPexp : (2 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - theta293) := by
    have h1 : (Real.exp 1) ^ (1 - theta293)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - theta293) :=
      Real.rpow_le_rpow (Real.exp_pos 1).le hLX (by linarith)
    have h2 : (Real.exp 1) ^ (31 / 32 : ℝ) ≤ (Real.exp 1) ^ (1 - theta293) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : (Real.exp 1) ^ (31 / 32 : ℝ) = Real.exp (31 / 32) := Real.exp_one_rpow _
    have h4 := cofk_two_le_exp_31_32
    rw [h3] at h2
    linarith
  have hP83log : Real.log (P83 ((Xd : ℕ) : ℝ) theta293)
      = (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - theta293) := by rw [P83, Real.log_exp]
  have hP83ge : (3 : ℝ) ≤ P83 ((Xd : ℕ) : ℝ) theta293 := by
    rw [P83]
    have h1 : Real.exp 2 ≤ Real.exp ((Real.log ((Xd : ℕ) : ℝ)) ^ (1 - theta293)) :=
      Real.exp_le_exp.mpr hPexp
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    linarith
  have hP3R : (3 : ℝ) ≤ ((s13BandP Xd : ℕ) : ℝ) := by linarith
  have hP3 : 3 ≤ s13BandP Xd := by exact_mod_cast hP3R
  have hP1 : 1 ≤ s13BandP Xd := by omega
  have hlogP2 : (2 : ℝ) ≤ Real.log ((s13BandP Xd : ℕ) : ℝ) := by
    have h := Real.log_le_log hP83pos hPlow
    rw [hP83log] at h
    linarith
  have hQlog : Real.log ((s13BandQ Xd : ℕ) : ℝ)
      ≤ Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ)) :=
    log_le_of_le_Q83 hQ1 hQhigh
  have hQL : Real.log ((s13BandQ Xd : ℕ) : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
    have hdiv : Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ))
        ≤ Real.log ((Xd : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hRrad0 : (0 : ℝ) < seamRad ((Xd : ℕ) : ℝ) := by
    rw [seamRad]; exact Real.rpow_pos_of_pos hLg0 _
  -- ⟦CONJUNCTS 2 AND 3: THE `T`-WINDOW IS THE SOCKET'S OWN ARITHMETIC⟧
  have h2T0 : (0 : ℝ) < 2 * T := by linarith
  have hQT : ((s13BandQ Xd : ℕ) : ℝ) ≤ 2 * T := by
    have hQ0R : (0 : ℝ) < ((s13BandQ Xd : ℕ) : ℝ) := by exact_mod_cast hQpos
    have hstep : Real.log ((s13BandQ Xd : ℕ) : ℝ) ≤ Real.log (2 * T) := by
      have hdiv : Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ))
          ≤ Real.log ((Xd : ℕ) : ℝ) / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
        nlinarith
      linarith
    have h := Real.exp_le_exp.mpr hstep
    rwa [Real.exp_log hQ0R, Real.exp_log h2T0] at h
  have h30g : 30 * (Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ)))
      ≤ Real.log (2 * T) := by
    have hdiv : Real.log ((Xd : ℕ) : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ))
        ≤ Real.log ((Xd : ℕ) : ℝ) / 60 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 60)]
      nlinarith
    linarith
  -- ⟦THE BLOCKS⟧
  have hBpos : ∀ v : ℕ, (0 : ℝ) < ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v
    rw [ramRbot]
    exact mul_pos hAsR (Real.exp_pos _)
  have hB34 : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4)
        ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    have hlow := cofkR_band_log_lower hH0 hQ1 hQhigh hLe2 hv
    have hid : (1 - 1 / Real.log (Real.log ((Xd : ℕ) : ℝ))) * Real.log ((Xd : ℕ) : ℝ)
        = Real.log ((Xd : ℕ) : ℝ)
          - (1 / Real.log (Real.log ((Xd : ℕ) : ℝ))) * Real.log ((Xd : ℕ) : ℝ) := by ring
    rw [hid] at hlow
    have hinv : (1 : ℝ) / Real.log (Real.log ((Xd : ℕ) : ℝ)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 4)]
      linarith
    have hstep : 3 * Real.log ((Xd : ℕ) : ℝ) / 4
        ≤ Real.log (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v) := by
      nlinarith [hlow, hinv, hLg0]
    have h := Real.exp_le_exp.mpr hstep
    rwa [Real.exp_log (hBpos v)] at h
  -- the three exponential comparisons every block fact below runs on
  have hehalf : (1 : ℝ) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) :=
    Real.one_le_exp (by linarith)
  have hequart : (1 : ℝ) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) :=
    Real.one_le_exp (by linarith)
  have hesplit : Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4)
      * Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)
      = Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have he2half : (2 : ℝ) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := by
    linarith [Real.add_one_le_exp (Real.log ((Xd : ℕ) : ℝ) / 2)]
  have he2quart : (2 : ℝ) ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) := by
    linarith [Real.add_one_le_exp (Real.log ((Xd : ℕ) : ℝ) / 4)]
  have hquarthalf : Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4)
      ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := Real.exp_le_exp.mpr (by linarith)
  have hgap34 : Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) + 1
      ≤ Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
    nlinarith [hesplit, hehalf, he2quart]
  have hgapq : Real.exp (Real.log ((Xd : ℕ) : ℝ) / 4) + 1
      ≤ Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
    nlinarith [hesplit, hehalf, he2quart, hquarthalf]
  have hpinhalf : pin2Gate ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := by
    rw [pin2Gate]
    exact Real.exp_le_exp.mpr (by linarith)
  -- the landed band facts, at the repaired scale
  have hBX : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      2 * ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v ≤ ((Xd : ℕ) : ℝ) :=
    fun v hv => cofkL_two_ramRbot_le hH1 hlogP2 hv
  have hkth : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ballQuarterThreshold + 1 ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
    fun v hv => cofk_ballQuarter_at_band hH0 hQ1 hQhigh hball hv
  have hW5 : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      (5 : ℝ) ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
    fun v hv => cofkL_five_le_ramRbot (hkth v hv)
  have hC16 : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      18 + Real.log (Real.log ((Xd : ℕ) : ℝ))
          - Real.log (Real.log (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)) :=
    fun v hv => cofk_descent_at_band hH0 hQ1 hQhigh (by linarith) (by linarith) hv
  have hRradW : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      seamRad ((Xd : ℕ) : ℝ) ≤ Real.sqrt 2 * ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
    fun v hv => cofk_seamRad_at_band hH0 hQ1 hQhigh (by linarith) hv
  have hXskj : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Xsk ≤ Real.sqrt (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v) :=
    fun v hv => cofk_wideThreshold_at_band hH0 hQ1 hQhigh hLe2 hXskgate hv
  -- ⟦THE REPAIRED LADDER `D = ⌈log X⌉₊`⟧
  have hDge : Real.log ((Xd : ℕ) : ℝ) ≤ ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hDle : ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hLg0.le)
  have hDone : 1 ≤ ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ := by
    have h : (1 : ℝ) ≤ ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by linarith
    exact_mod_cast h
  have hWlow : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
            / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) :=
    fun v hv => cofkR_window_lower (by linarith) hDone hDle (hB34 v hv)
  have hWpos : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      (0 : ℝ) < ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by
    intro v hv; linarith [hWlow v hv, hehalf]
  have hlogW : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      1 / 2 * Real.log ((Xd : ℕ) : ℝ)
        ≤ Real.log (((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
            / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)) := by
    intro v hv
    have h := Real.log_le_log (Real.exp_pos (Real.log ((Xd : ℕ) : ℝ) / 2)) (hWlow v hv)
    rw [Real.log_exp] at h
    linarith only [h]
  have hWXle : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ≤ ((Xd : ℕ) : ℝ) := by
    intro v hv
    have h1 : (witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) ≤ witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
      Nat.div_le_self _ _
    have h1R : ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 := (witKk_cut (H := H83 ((Xd : ℕ) : ℝ) theta293) (Xd := Xd) (j := v)
      (by linarith [hW5 v hv])).1
    linarith [hBX v hv, hBpos v]
  -- ⟦THE WINDOW TOP⟧
  have hMtlow : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)
        ≤ ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
    intro v hv
    have h := (witMt_window (H := H83 ((Xd : ℕ) : ℝ) theta293) (Xd := Xd) (j := v)
      (by linarith [hW5 v hv])).1
    linarith [hB34 v hv, hgap34]
  have hMtX : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) ≤ 2 * ramRbot
        (H83 ((Xd : ℕ) : ℝ) theta293) Xd v :=
    fun v hv => cofkL_Mt_le_two_ramRbot (hW5 v hv)
  have hlogMt : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      1 / 2 * Real.log ((Xd : ℕ) : ℝ)
        ≤ Real.log (((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)) := by
    intro v hv
    have h := Real.log_le_log (Real.exp_pos (Real.log ((Xd : ℕ) : ℝ) / 2)) (hMtlow v hv)
    rw [Real.log_exp] at h
    linarith only [h]
  have hlogB : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      1 / 2 * Real.log ((Xd : ℕ) : ℝ)
        ≤ Real.log (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v) := by
    intro v hv
    have h := Real.log_le_log (Real.exp_pos (3 * Real.log ((Xd : ℕ) : ℝ) / 4)) (hB34 v hv)
    rw [Real.log_exp] at h
    linarith only [h, hLg0]
  -- ⟦THE EXIT CHARGES, AT THE REPAIRED LADDER⟧
  have hpow0 : (0 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := Real.rpow_nonneg hLg0.le _
  have hcSq0 := cofk_cSq_pos
  have hS0 : (0 : ℝ) ≤ cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) :=
    mul_nonneg (cofkRSconst_pos hCb0).le hpow0
  have hSbd : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      cSq * caseASwide (1 / Real.exp 1) Cb
          (cofactorMfl ((Xd : ℕ) : ℝ) theta293
            ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
              / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ))
          ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
            / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
          (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v)
        + cSq * ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
      ≤ cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
    intro v hv
    have hW2 : (2 : ℝ) ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := le_trans he2half (hWlow v hv)
    have hcase := cofkR_caseASwide_priced hCb0 hW2 (hWXle v hv) hLe2 (by linarith)
      (hlogW v hv) (hlogB v hv)
    have hD4 : ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
      have h1 : ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hLg0 hDge (by norm_num)
      have h2 : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 4 : ℝ))
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith only [hLgbig])
          (by linarith only [rho293_le_seam])
      linarith only [h1, h2]
    have h1 := mul_le_mul_of_nonneg_left hcase hcSq0.le
    have h2 := mul_le_mul_of_nonneg_left hD4 hcSq0.le
    calc cSq * caseASwide (1 / Real.exp 1) Cb
            (cofactorMfl ((Xd : ℕ) : ℝ) theta293
              ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
                / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ))
            ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
              / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
            (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v)
          + cSq * ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
        ≤ cSq * ((3 * gradeAbsConstC (1 / Real.exp 1) Cb + 2 * farCStar2 + 8)
              * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
            + cSq * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by linarith only [h1, h2]
      _ = cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
          rw [cofkRSconst]; ring
  have hMfl0 : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      (0 : ℝ) ≤ cofactorMfl ((Xd : ℕ) : ℝ) theta293
        ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
          / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by
    intro v hv
    exact cofkR_mfl_nonneg (le_trans he2half (hWlow v hv)) (hWXle v hv) hLe2
      (hlogW v hv) (by linarith)
  -- ⟦THE FAR ARM AT EVERY BLOCK⟧
  have hfarb : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      farSupS34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad ((Xd : ℕ) : ℝ))
        ≤ 5 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
    intro v hv
    have hY0Mt : Y0 ≤ ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) :=
      le_trans hY0gate (le_trans hquarthalf (hMtlow v hv))
    have hB2 : (2 : ℝ) ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
      linarith [hW5 v hv]
    have hMt0 : (0 : ℝ) < ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith [hMtlow v hv, hehalf]
    have hlogMtle := Real.log_le_log hMt0 (hMtX v hv)
    have hkkhalf : ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v / 2
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith [cofkL_ramRbot_le_kk (hW5 v hv)]
    have hlogkk := Real.log_le_log (by linarith : (0 : ℝ)
      < ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v / 2) hkkhalf
    rw [Real.log_mul (by norm_num) (ne_of_gt (hBpos v))] at hlogMtle
    rw [Real.log_div (ne_of_gt (hBpos v)) (by norm_num)] at hlogkk
    have hlogBbig : 3 * Real.log 2 ≤ Real.log (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v) := by
      linarith only [hlogB v hv, Real.log_two_lt_d9, hLgbig]
    have hlogMt2kk : Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        ≤ 2 * Real.log ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith only [hlogMtle, hlogkk, hlogBbig]
    exact cofkR_farSup_priced (by linarith only [hLgbig]) (hfarclose _ _ hY0Mt hlogMt2kk)
      (hlogMt v hv)
  -- ⟦THE `R̄₀` CEILING⟧
  have hRbdU : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      cofactorRbdGen (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
          ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad ((Xd : ℕ) : ℝ))
        ≤ cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
    intro v hv
    rw [cofactorRbdGen, cofkRConst]
    have hmax : max (2 * (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)))
        (farSupS34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad ((Xd : ℕ) : ℝ)))
        ≤ (2 * cofkRSconst Cb + 5) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := by
      have hSP : (0 : ℝ) ≤ cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293) := hS0
      exact max_le (by linarith only [hpow0])
        (le_trans (hfarb v hv) (by linarith only [hSP]))
    linarith only [hmax]
  -- ⟦THE ENDPOINT CHARGE⟧
  have hLgleB : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.log ((Xd : ℕ) : ℝ) ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    have h1 : 1 + 3 * Real.log ((Xd : ℕ) : ℝ) / 8
        ≤ Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8) := by
      linarith [Real.add_one_le_exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)]
    have h2 : Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)
        * Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)
        = Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [hB34 v hv, h1, h2, hLg0]
  have hsr : seamRad ((Xd : ℕ) : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
    rw [seamRad]
    have h1 : (Real.log ((Xd : ℕ) : ℝ)) ^ ((1 : ℝ) / 46)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rwa [Real.rpow_one] at h1
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
    rwa [Real.sqrt_one] at h
  have hendGen : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      2 / ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        ≤ cofactorRbdGen (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
            ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
              (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
            (seamRad ((Xd : ℕ) : ℝ)) / 3 := by
    intro v hv
    have hMt0 : (0 : ℝ) < ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith [hMtlow v hv, hehalf]
    have hkk0 : (0 : ℝ) < Real.log ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      have h2 : (2 : ℝ) ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
        linarith only [cofkL_ramRbot_le_kk (hW5 v hv), hW5 v hv]
      exact Real.log_pos (by linarith only [h2])
    have hfar0 : (0 : ℝ) ≤ farErr34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ))) :=
      farErr34_nonneg hkk0 (Real.log_nonneg (by linarith [hMtlow v hv, he2half]))
        (Tstar2_pos hMt0).le
    have hchain : 2 / ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        ≤ farSupS34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad ((Xd : ℕ) : ℝ)) := by
      rw [farSupS34]
      have h1 : (2 : ℝ) / ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
          ≤ 2 / Real.log ((Xd : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hLg0 (hLgleB v hv)
      have h2 : (2 : ℝ) / Real.log ((Xd : ℕ) : ℝ) ≤ 2 / seamRad ((Xd : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hRrad0 hsr
      have hinv : (0 : ℝ) < (seamRad ((Xd : ℕ) : ℝ))⁻¹ := inv_pos.mpr hRrad0
      have h3 : (2 : ℝ) / seamRad ((Xd : ℕ) : ℝ)
          ≤ 2 * Real.sqrt 2 / seamRad ((Xd : ℕ) : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        nlinarith [hs2, hinv]
      linarith
    rw [cofactorRbdGen]
    have hfin := le_trans hchain
      (le_max_right (2 * (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)))
      (farSupS34 ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
        (Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)))
        (seamRad ((Xd : ℕ) : ℝ))))
    linarith only [hfin]
  -- ⟦THE LADDER GATES⟧
  have hLg2leB : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.log ((Xd : ℕ) : ℝ) + 2 ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    have h1 : 1 + 3 * Real.log ((Xd : ℕ) : ℝ) / 8
        ≤ Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8) := by
      linarith [Real.add_one_le_exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)]
    have h2 : Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)
        * Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 8)
        = Real.exp (3 * Real.log ((Xd : ℕ) : ℝ) / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [hB34 v hv, h1, h2, hLgbig]
  have hDdk : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ ≤ witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    have hR : ((⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ) := by
      linarith only [hDle, hLg2leB v hv, cofkL_ramRbot_le_kk (hW5 v hv)]
    exact_mod_cast hR
  have hsqXa : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.sqrt (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v)
        ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
            / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by
    intro v hv
    have hBle : ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        ≤ Real.exp (Real.log ((Xd : ℕ) : ℝ)) := by
      rw [Real.exp_log hAsR]
      linarith only [hBX v hv, hBpos v]
    have hmono := Real.sqrt_le_sqrt hBle
    have hsq : Real.sqrt (Real.exp (Real.log ((Xd : ℕ) : ℝ)))
        = Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := by
      have hsplit2 : Real.exp (Real.log ((Xd : ℕ) : ℝ))
          = Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2)
            * Real.exp (Real.log ((Xd : ℕ) : ℝ) / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hsplit2, Real.sqrt_mul_self (Real.exp_pos _).le]
    rw [hsq] at hmono
    linarith only [hmono, hWlow v hv]
  have hpinW : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      pin2Gate ≤ ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
        / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) :=
    fun v hv => le_trans hpinhalf (hWlow v hv)
  have hXae : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Real.exp 1 ≤ ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v := by
    intro v hv
    linarith only [hW5 v hv, Real.exp_one_lt_d9]
  -- ⟦THE TWO CONTOUR BOXES⟧
  have hTX : (2 : ℝ) * T ≤ ((Xd : ℕ) : ℝ) := hThi
  have hbox : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ∀ t : ℝ, |t| ≤ 2 * T →
        |t| + Tstar2 ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd v : ℕ) : ℝ))
          ≤ 3 * ((Xd : ℕ) : ℝ) := by
    intro v hv t ht
    exact cofkR_box_of_le (le_trans hpinhalf (hMtlow v hv))
      (by linarith only [hMtX v hv, hBX v hv]) (by linarith only [ht, hTX])
  have hboxw : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ∀ t : ℝ, |t| ≤ 2 * T → ∀ i : ℕ,
        ((witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd v
          / ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ≤ (i : ℝ) →
          (i : ℝ) ≤ 2 * ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd v →
            |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * ((Xd : ℕ) : ℝ) := by
    intro v hv t ht i hi1 hi2
    exact cofkR_box_of_le (le_trans (hpinW v hv) hi1)
      (by linarith only [hi2, hBX v hv]) (by linarith only [ht, hTX])
  -- ⟦`TLBlockGates34` AT THE WITNESS⟧
  have hlogLs0 : (0 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by linarith
  have hrp : (0 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg hLg0.le _
  have hp5 : (0 : ℝ) ≤ (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5 := pow_nonneg hlogLs0 5
  have hcq0 : (0 : ℝ) ≤ 420 * Real.log ((Xd : ℕ) : ℝ)
      * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5 := by
    have h1 : (0 : ℝ) ≤ 420 * Real.log ((Xd : ℕ) : ℝ) := by linarith
    exact mul_nonneg (mul_nonneg h1 hrp) hp5
  have hcqgate : 420 * Real.log ((Xd : ℕ) : ℝ)
        * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5
      ≤ (420 * Real.log ((Xd : ℕ) : ℝ)
          * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5)
        * (Real.log ((s13BandP Xd : ℕ) : ℝ)) ^ 2 := by
    have hsq : (1 : ℝ) ≤ (Real.log ((s13BandP Xd : ℕ) : ℝ)) ^ 2 := by nlinarith [hlogP2]
    nlinarith [hcq0, hsq]
  have hblk : ∀ v ∈ ramI (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      TLBlockGates34 (420 * Real.log ((Xd : ℕ) : ℝ)
          * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5)
        (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) (2 * Xd) Xd
        (witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
        (witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
        (2 * T) (Real.log ((Xd : ℕ) : ℝ)) (1 / Real.exp 1) Cb
        ((Xd : ℕ) : ℝ) theta293 (seamRad ((Xd : ℕ) : ℝ)) v := by
    intro v hv
    have hbaseQ : ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v ≤ s13BandQ Xd :=
      ramQbase_le_top hH0 hQ1 hPQ hv
    have hbase3 : 3 ≤ ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v :=
      le_trans hP3 (ramQbase_ge_bot _ _ _)
    have hb3R : (3 : ℝ)
        ≤ ((ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v : ℕ) : ℝ) := by
      exact_mod_cast hbase3
    have hblog0 : (0 : ℝ)
        < Real.log ((ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v : ℕ) : ℝ) :=
      Real.log_pos (by linarith only [hb3R])
    have hbQ : Real.log ((ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v : ℕ) : ℝ)
        ≤ Real.log ((s13BandQ Xd : ℕ) : ℝ) :=
      Real.log_le_log (by linarith only [hb3R]) (by exact_mod_cast hbaseQ)
    have h30 : (30 : ℝ) ≤ Real.log (2 * T)
        / Real.log ((ramQbase (H83 ((Xd : ℕ) : ℝ) theta293) (s13BandP Xd) v : ℕ) : ℝ) := by
      rw [le_div_iff₀ hblog0]
      linarith only [h30g, hbQ, hQlog, hblog0]
    exact tlBlockGates34_at_witness hH1 hP3 hlogP2 hQ1 hPQ hcq0 hv hQT h30 hQL hcqgate
      (by linarith only [hW5 v hv]) (hkth v hv) le_rfl (hBX v hv) (hC16 v hv) hRrad0
      (hRradW v hv)
  -- ⟦THE HEAD⟧
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hce : (1 : ℝ) / Real.exp 1 ≤ 1 / Real.exp 1 := le_refl _
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith [Real.exp_one_gt_d9])]
    linarith [Real.exp_one_gt_d9]
  -- ⟦THE EXIT⟧
  have hRb0 : (0 : ℝ) ≤ 4 * (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)) := by
    linarith only [mul_nonneg (cofkRConst_pos hCb0).le hpow0]
  refine ⟨seamRad ((Xd : ℕ) : ℝ),
    4 * (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)),
    4 * cofkRConst Cb, hRb0, le_of_eq (by ring), hgradegate, ?_⟩
  intro t₁ χ
  have hs := hsup q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M)
    (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd (s13BandP Xd) (s13BandQ Xd) 2 1
    (witMt (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
    (witKk (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
    (fun _ : ℕ => ⌈Real.log ((Xd : ℕ) : ℝ)⌉₊)
    (ramRbot (H83 ((Xd : ℕ) : ℝ) theta293) Xd)
    (420 * Real.log ((Xd : ℕ) : ℝ)
      * (Real.log ((Xd : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log ((Xd : ℕ) : ℝ))) ^ 5)
    (Real.log ((Xd : ℕ) : ℝ)) (1 / Real.exp 1) Cb ((Xd : ℕ) : ℝ) theta293
    (seamRad ((Xd : ℕ) : ℝ)) (2 * T) t₁
    (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)) (1 / Real.exp 1)
    (cofkRSconst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
    hc0 hce hc1 hCb0 hCbound hP1 (le_refl 1) hRrad0 hθ0 hθ32 hLX hPlow hQhigh hPQ
    (hfloorχ χ) hblk hbox (fun _ _ => hDone) hDdk hXskj hsqXa hpinW hXae hMtX hBX hMfl0
    hboxw hS0 hSbd hendGen hRbdU
  have he : (2 : ℝ) ^ (2 : ℕ) * (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293))
      = 4 * (cofkRConst Cb * (Real.log ((Xd : ℕ) : ℝ)) ^ (-rho293)) := by norm_num
  rwa [he] at hs

/-! ## §W2 — ⟦THE COUNT LEAF AT GENERIC `ε`⟧ `|Ξ_H| ≤ 2^283·c^20`, the charge being the lattice
count `c` itself: no cap, no logarithm, and no numeral ceiling -/

-- the chain file's own line (`FlatDoorEpsChain.lean:32`): `norm_num` declines an exponent above
-- the threshold and leaves the goal OPEN, and the ceiling `2^283` is above the default 256.
set_option exponentiation.threshold 4000 in
/-- **⟦THE COUNT HOOK AT THE HEAD'S GRADE⟧** (`bigXi_bounded_ceiling_eps`) —
`bigXi_bounded_ceiling_of_cap` (`FlatDoorEpsChain.lean:410`, at the cap `1/(500·8103) ≤ ε`) with
the cap's numeral `8103` replaced by the CHARGE `c ≥ 1`: the hypothesis reads `1/(500·c) ≤ ε`,
and the ceiling is a FUNCTION of the charge, `2^283·c^20`.  The charge is the lattice count
itself, so no logarithm enters.

⟦THE THRESHOLD⟧ `T := 2^68·c^3` (the landed `T = 2^68` is this at `c = 1`, up to the `c^3`).
The four demands, each with its slack: `N0' = 2^20 ≤ 2^68 ≤ T`; `4 ≤ ε²·T`, which reads
`ε²·T ≥ 2^68·c/250000 ≥ 1.18059·10^15`; `16^10 = 2^40 ≤ 2^68 ≤ T`; and
`(2/ε²)^10 ≤ (2·250000·c²)^10 ≤ 2^190·c^20 ≤ 2^612·c^27 = T^9`, using
`10·log₂ 500000 = 189.3156…` and `500000 ≤ 524288 = 2^19`.

⟦THE CONSTANT⟧ `1/ε ≤ 500·c` gives `1/ε² ≤ 250000·c²`, and `ε ≤ 1/500` gives `ε² ≤ 1/250000`,
so `ε²·T ≤ 2^68·c³/250000 ≤ 1180591620717412·c³`, `1/(2ε²) ≤ 125000·c²` and
`102400/ε² ≤ 25600000000·c²`.  `log T = 68·log 2 + 3·log c ≤ 47.14 + 3·(c−1) ≤ 47.14·c` at
`c ≥ 1` (`68·log 2 = 47.13400…`), so `(log T)² ≤ 2222.2·c²`.  Hence
`C₁ ≤ 25600204800·c² + 1188815000000000·2222.2·c⁵ = 2641784718600204800·c⁵ ≤ 2^62·c⁵`
(`2^62 = 4611686018427387904`; `2^61 = 2305843009213693952` does NOT suffice).

⟦THE WITNESS AND ITS SIZE⟧ `32·e^40·(2^62·c^5)²·(500·c)^10`, the `(500·c)^10` from
`1/ε^10 ≤ (500·c)^10`.  On the corpus's own chain (`e^40 ≤ 3^40 ≤ 2^64`), with `32 = 2^5`,
`(2^62)² = 2^124` and `500^10 ≤ 2^90` (`500 < 512`), the total is `2^(5+64+124+90) = 2^283`
times `c^20`.  The true size is `2^282.0563…·c^20`, so `2^282` does NOT suffice: at `b = 20`,
`a = 283` is the smallest exponent this route gives. -/
theorem bigXi_bounded_ceiling_eps (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
    {c : ℕ} (hc1 : 1 ≤ c) (hcε : (1 : ℚ) / (500 * (c : ℚ)) ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧
      ∀ (H : ℕ) [NeZero H], H₀ ≤ H → ((bigXi ε H).card : ℝ) ≤ C := by
  have hc0 : 0 < c := hc1
  have hcQ1 : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcQ0 : (0 : ℚ) < (c : ℚ) := by linarith
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hcR0 : (0 : ℝ) < (c : ℝ) := by linarith
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  -- ⟦THE CAP AT GENERIC `c`⟧ `1/(500·c) ≤ ε` reads `1 ≤ 500·c·ε`
  have hqcap : (1 : ℚ) ≤ 500 * (c : ℚ) * ε := by
    have h := (div_le_iff₀ (show (0 : ℚ) < 500 * (c : ℚ) by linarith)).mp hcε
    calc (1 : ℚ) ≤ ε * (500 * (c : ℚ)) := h
      _ = 500 * (c : ℚ) * ε := by ring
  have hcapR : (1 : ℝ) ≤ 500 * (c : ℝ) * (ε : ℝ) := by exact_mod_cast hqcap
  have hεle : (ε : ℝ) ≤ 1 / 500 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε
    rwa [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
  have heps2 : (ε : ℝ) ^ 2 < 1 / 2 := by nlinarith [hεR0, hεle]
  have hε2le : (ε : ℝ) ^ 2 ≤ 1 / 250000 := by nlinarith [hεR0, hεle]
  have hsqQ : (1 : ℚ) ≤ 250000 * (c : ℚ) ^ 2 * ε ^ 2 := by
    have h := one_le_pow₀ (n := 2) hqcap
    calc (1 : ℚ) ≤ (500 * (c : ℚ) * ε) ^ 2 := h
      _ = 250000 * (c : ℚ) ^ 2 * ε ^ 2 := by ring
  have hsqR : (1 : ℝ) ≤ 250000 * (c : ℝ) ^ 2 * (ε : ℝ) ^ 2 := by
    have h := one_le_pow₀ (n := 2) hcapR
    calc (1 : ℝ) ≤ (500 * (c : ℝ) * (ε : ℝ)) ^ 2 := h
      _ = 250000 * (c : ℝ) ^ 2 * (ε : ℝ) ^ 2 := by ring
  have hTcastR : (((2 ^ 68 * c ^ 3 : ℕ)) : ℝ) = (2 : ℝ) ^ (68 : ℕ) * (c : ℝ) ^ 3 := by
    push_cast; ring
  have hTcastQ : (((2 ^ 68 * c ^ 3 : ℕ)) : ℚ) = (2 : ℚ) ^ (68 : ℕ) * (c : ℚ) ^ 3 := by
    push_cast; ring
  -- ⟦THE THRESHOLD'S FOUR DEMANDS⟧ at `T := 2^68 · c^3`
  have hcpow3 : 0 < c ^ 3 := pow_pos hc0 3
  have hT0 : N0' ≤ 2 ^ 68 * c ^ 3 :=
    le_trans (by unfold N0'; norm_num) (Nat.le_mul_of_pos_right _ hcpow3)
  have hTA : (4 : ℚ) ≤ ε ^ 2 * (((2 ^ 68 * c ^ 3 : ℕ)) : ℚ) := by
    rw [hTcastQ, show (2 : ℚ) ^ (68 : ℕ) = 295147905179352825856 by norm_num]
    have hbig : (4 : ℚ) ≤ 295147905179352825856 * (c : ℚ) / 250000 := by
      linarith only [hcQ1]
    calc (4 : ℚ) = 4 * 1 := by ring
      _ ≤ (295147905179352825856 * (c : ℚ) / 250000) * (250000 * (c : ℚ) ^ 2 * ε ^ 2) :=
          mul_le_mul hbig hsqQ (by norm_num) (by linarith only [hbig])
      _ = ε ^ 2 * (295147905179352825856 * (c : ℚ) ^ 3) := by ring
  have hTB : ((16 : ℕ) : ℝ) ^ (10 : ℕ) ≤ (((2 ^ 68 * c ^ 3 : ℕ)) : ℝ) := by
    rw [hTcastR]
    have h1 : ((16 : ℕ) : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ (68 : ℕ) := by norm_num
    have h2 : (2 : ℝ) ^ (68 : ℕ) ≤ (2 : ℝ) ^ (68 : ℕ) * (c : ℝ) ^ 3 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hcR1)
    linarith
  have hTD : (2 / (ε : ℝ) ^ 2) ^ (10 : ℕ) ≤ ((((2 ^ 68 * c ^ 3 : ℕ)) : ℝ)) ^ (9 : ℕ) := by
    have h1 : (2 : ℝ) / (ε : ℝ) ^ 2 ≤ (2 : ℝ) ^ (19 : ℕ) * (c : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity), show (2 : ℝ) ^ (19 : ℕ) = 524288 by norm_num]
      linarith only [hsqR]
    rw [hTcastR]
    calc ((2 : ℝ) / (ε : ℝ) ^ 2) ^ (10 : ℕ)
        ≤ ((2 : ℝ) ^ (19 : ℕ) * (c : ℝ) ^ 2) ^ (10 : ℕ) :=
          pow_le_pow_left₀ (by positivity) h1 10
      _ = ((2 : ℝ) ^ (19 : ℕ)) ^ (10 : ℕ) * ((c : ℝ) ^ 2) ^ (10 : ℕ) := by rw [mul_pow]
      _ = (2 : ℝ) ^ (190 : ℕ) * (c : ℝ) ^ (20 : ℕ) := by rw [← pow_mul, ← pow_mul]
      _ ≤ (2 : ℝ) ^ (612 : ℕ) * (c : ℝ) ^ (27 : ℕ) :=
          mul_le_mul (pow_le_pow_right₀ (by norm_num) (by norm_num))
            (pow_le_pow_right₀ hcR1 (by norm_num)) (by positivity) (by positivity)
      _ = ((2 : ℝ) ^ (68 : ℕ) * (c : ℝ) ^ 3) ^ (9 : ℕ) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
  -- ⟦THE LOG OF THE THRESHOLD⟧ `log T = 68·log 2 + 3·log c ≤ 47.14·c`
  have hlogT : Real.log ((((2 ^ 68 * c ^ 3 : ℕ)) : ℝ)) ≤ 47.14 * (c : ℝ) := by
    rw [hTcastR, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have hlc : Real.log (c : ℝ) ≤ (c : ℝ) - 1 := Real.log_le_sub_one_of_pos hcR0
    push_cast
    linarith [Real.log_two_lt_d9, hlc, hcR1]
  have hlogT0 : (0 : ℝ) ≤ Real.log ((((2 ^ 68 * c ^ 3 : ℕ)) : ℝ)) := Real.log_natCast_nonneg _
  have hlogTsq : (Real.log ((((2 ^ 68 * c ^ 3 : ℕ)) : ℝ))) ^ 2 ≤ 2222.2 * (c : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ hlogT0 hlogT 2
    calc (Real.log ((((2 ^ 68 * c ^ 3 : ℕ)) : ℝ))) ^ 2 ≤ (47.14 * (c : ℝ)) ^ 2 := h
      _ ≤ 2222.2 * (c : ℝ) ^ 2 := by linarith only [sq_nonneg ((c : ℝ))]
  -- ⟦THE CONSTANT⟧ the generic `hpt`, capped at `2^62 · c^5`
  have hpt : ∀ H n : ℕ, ((repCount (Salt.Entropy.Chowla.primeWindow ε H)
        (Salt.Entropy.Chowla.primeWindow ε H) n : ℕ) : ℝ)
      ≤ ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5)
          * ((ε : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by
    intro H n
    refine le_trans (hpt_holds_thr ε hε0 heps2 (1 / 256) (by norm_num) 16
      repCount_even_le_primorial_sixteen (2 ^ 68 * c ^ 3) hT0 hTA hTB hTD H n) ?_
    have hF : (0 : ℝ) ≤ ((ε : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n :=
      mul_nonneg (div_nonneg (by positivity) (sq_nonneg _)) (sTrunc2_nonneg n)
    have hc3nn : (0 : ℝ) ≤ (c : ℝ) ^ 3 := by positivity
    have hA : (ε : ℝ) ^ 2 * (((2 ^ 68 * c ^ 3 : ℕ)) : ℝ) ≤ 1180591620717412 * (c : ℝ) ^ 3 := by
      rw [hTcastR, show (2 : ℝ) ^ (68 : ℕ) = 295147905179352825856 by norm_num]
      have hstep : (ε : ℝ) ^ 2 * (295147905179352825856 * (c : ℝ) ^ 3)
          ≤ (1 / 250000) * (295147905179352825856 * (c : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right hε2le (by positivity)
      linarith only [hstep, hc3nn]
    have hB : (1 : ℝ) / (2 * (ε : ℝ) ^ 2) ≤ 125000 * (c : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith only [hsqR]
    have hc2le3 : (c : ℝ) ^ 2 ≤ (c : ℝ) ^ 3 := pow_le_pow_right₀ hcR1 (by norm_num)
    have hc3one : (1 : ℝ) ≤ (c : ℝ) ^ 3 := one_le_pow₀ hcR1
    have hbr : (ε : ℝ) ^ 2 * (((2 ^ 68 * c ^ 3 : ℕ)) : ℝ) + 2 + 1 / (2 * (ε : ℝ) ^ 2)
        ≤ 1188815000000000 * (c : ℝ) ^ 3 := by
      have hstep : (ε : ℝ) ^ 2 * (((2 ^ 68 * c ^ 3 : ℕ)) : ℝ) + 2 + 1 / (2 * (ε : ℝ) ^ 2)
          ≤ 1180591620717412 * (c : ℝ) ^ 3 + 2 + 125000 * (c : ℝ) ^ 2 :=
        add_le_add (add_le_add hA le_rfl) hB
      have htail : 1180591620717412 * (c : ℝ) ^ 3 + 2 + 125000 * (c : ℝ) ^ 2
          ≤ 1188815000000000 * (c : ℝ) ^ 3 := by
        linarith only [hc2le3, hc3one, hc3nn]
      exact le_trans hstep htail
    have hprod : ((ε : ℝ) ^ 2 * (((2 ^ 68 * c ^ 3 : ℕ)) : ℝ) + 2 + 1 / (2 * (ε : ℝ) ^ 2))
          * (Real.log ((((2 ^ 68 * c ^ 3 : ℕ)) : ℝ))) ^ 2
        ≤ (1188815000000000 * (c : ℝ) ^ 3) * (2222.2 * (c : ℝ) ^ 2) :=
      mul_le_mul hbr hlogTsq (sq_nonneg _) (by positivity)
    have hu2 : (102400 : ℝ) / (ε : ℝ) ^ 2 ≤ 25600000000 * (c : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith only [hsqR]
    have hCL : (800 / (1 / 256 : ℝ) + 102400 / (ε : ℝ) ^ 2) ≤ 25600204800 * (c : ℝ) ^ 2 := by
      have hstep : (800 / (1 / 256 : ℝ) + 102400 / (ε : ℝ) ^ 2)
          ≤ 204800 + 25600000000 * (c : ℝ) ^ 2 :=
        add_le_add (le_of_eq (by norm_num)) hu2
      have htail : (204800 : ℝ) + 25600000000 * (c : ℝ) ^ 2 ≤ 25600204800 * (c : ℝ) ^ 2 := by
        linarith only [one_le_pow₀ (n := 2) hcR1]
      exact le_trans hstep htail
    have hc5nn : (0 : ℝ) ≤ (c : ℝ) ^ 5 := by positivity
    have hc2le5 : (c : ℝ) ^ 2 ≤ (c : ℝ) ^ 5 := pow_le_pow_right₀ hcR1 (by norm_num)
    have hCsum : (800 / (1 / 256 : ℝ) + 102400 / (ε : ℝ) ^ 2)
          + ((ε : ℝ) ^ 2 * (((2 ^ 68 * c ^ 3 : ℕ)) : ℝ) + 2 + 1 / (2 * (ε : ℝ) ^ 2))
              * (Real.log ((((2 ^ 68 * c ^ 3 : ℕ)) : ℝ))) ^ 2
        ≤ (2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5 := by
      have hstep := add_le_add hCL hprod
      have htail : 25600204800 * (c : ℝ) ^ 2
            + (1188815000000000 * (c : ℝ) ^ 3) * (2222.2 * (c : ℝ) ^ 2)
          ≤ (2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5 := by
        rw [show (2 : ℝ) ^ (62 : ℕ) = 4611686018427387904 by norm_num]
        linarith only [hc2le5, hc5nn]
      exact le_trans hstep htail
    calc ((800 / (1 / 256 : ℝ) + 102400 / (ε : ℝ) ^ 2)
            + ((ε : ℝ) ^ 2 * (((2 ^ 68 * c ^ 3 : ℕ)) : ℝ) + 2 + 1 / (2 * (ε : ℝ) ^ 2))
                * (Real.log ((((2 ^ 68 * c ^ 3 : ℕ)) : ℝ))) ^ 2)
          * ((ε : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n
        = ((800 / (1 / 256 : ℝ) + 102400 / (ε : ℝ) ^ 2)
            + ((ε : ℝ) ^ 2 * (((2 ^ 68 * c ^ 3 : ℕ)) : ℝ) + 2 + 1 / (2 * (ε : ℝ) ^ 2))
                * (Real.log ((((2 ^ 68 * c ^ 3 : ℕ)) : ℝ))) ^ 2)
            * (((ε : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) := by ring
      _ ≤ ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5)
            * (((ε : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) :=
          mul_le_mul_of_nonneg_right hCsum hF
      _ = ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5)
            * ((ε : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by ring
  -- ⟦THE EXPLICIT COUNT, AND THE CEILING⟧
  have hbase := bigXi_bounded_explicit ε hε0 heps2 ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5)
    (Real.exp 40) (Real.exp_pos _) hFac2_lcm_sum_le_exp40 hpt
  have hC1pos : (0 : ℝ) < (2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5 :=
    mul_pos (by norm_num) (pow_pos hcR0 5)
  have hApos : (0 : ℝ) < 32 * Real.exp 40 * ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5) ^ 2 :=
    mul_pos (mul_pos (by norm_num) (Real.exp_pos 40)) (pow_pos hC1pos 2)
  have h500c : (0 : ℝ) < 500 * (c : ℝ) := by linarith
  refine ⟨32 * Real.exp 40 * ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5) ^ 2 * (500 * (c : ℝ)) ^ (10 : ℕ),
    mul_pos hApos (pow_pos h500c 10), ?_, 2, le_rfl, ?_⟩
  · have h40 : Real.exp 40 ≤ 3 ^ (40 : ℕ) := by simpa using exp_forty_le_pow40
    have hnn : (0 : ℝ) ≤ 32 * ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5) ^ 2 * (500 * (c : ℝ)) ^ (10 : ℕ) :=
      le_of_lt (mul_pos (mul_pos (by norm_num) (pow_pos hC1pos 2)) (pow_pos h500c 10))
    have hfold : 32 * Real.exp 40 * ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5) ^ 2
          * (500 * (c : ℝ)) ^ (10 : ℕ)
        = (32 * ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5) ^ 2 * (500 * (c : ℝ)) ^ (10 : ℕ))
            * Real.exp 40 := by ring
    have hcoef : (32 : ℝ) * ((2 : ℝ) ^ (62 : ℕ)) ^ 2 * (500 : ℝ) ^ (10 : ℕ)
        * (3 : ℝ) ^ (40 : ℕ) ≤ (2 : ℝ) ^ (283 : ℕ) := by norm_num
    have hexpand : (32 * ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5) ^ 2 * (500 * (c : ℝ)) ^ (10 : ℕ))
          * (3 : ℝ) ^ (40 : ℕ)
        = ((32 : ℝ) * ((2 : ℝ) ^ (62 : ℕ)) ^ 2 * (500 : ℝ) ^ (10 : ℕ) * (3 : ℝ) ^ (40 : ℕ))
            * (c : ℝ) ^ 20 := by ring
    have hnum : (32 * ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5) ^ 2 * (500 * (c : ℝ)) ^ (10 : ℕ))
          * (3 : ℝ) ^ (40 : ℕ) ≤ 2 ^ 283 * (c : ℝ) ^ 20 := by
      rw [hexpand]
      exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    rw [hfold]
    exact le_trans (mul_le_mul_of_nonneg_left h40 hnn) hnum
  · intro H _ hH2
    have hb := hbase H hH2
    have hid : 32 * Real.exp 40 * ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5) ^ 2 / (ε : ℝ) ^ 10
        ≤ 32 * Real.exp 40 * ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5) ^ 2
            * (500 * (c : ℝ)) ^ (10 : ℕ) := by
      rw [div_le_iff₀ (by positivity)]
      have hp : (1 : ℝ) ≤ (500 * (c : ℝ) * (ε : ℝ)) ^ (10 : ℕ) := one_le_pow₀ hcapR
      have hexp : (500 * (c : ℝ) * (ε : ℝ)) ^ (10 : ℕ)
          = (500 * (c : ℝ)) ^ (10 : ℕ) * (ε : ℝ) ^ 10 := by ring
      rw [hexp] at hp
      calc 32 * Real.exp 40 * ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5) ^ 2
          = (32 * Real.exp 40 * ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5) ^ 2) * 1 := by ring
        _ ≤ (32 * Real.exp 40 * ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5) ^ 2)
              * ((500 * (c : ℝ)) ^ (10 : ℕ) * (ε : ℝ) ^ 10) :=
            mul_le_mul_of_nonneg_left hp (le_of_lt hApos)
        _ = 32 * Real.exp 40 * ((2 : ℝ) ^ (62 : ℕ) * (c : ℝ) ^ 5) ^ 2
              * (500 * (c : ℝ)) ^ (10 : ℕ) * (ε : ℝ) ^ 10 := by ring
    exact le_trans hb hid

/-! ## §W3 — the arm at a generic charge: the shrinking cut, the split, the gate -/

/-- **⟦`6·10^10 ≤ e^25`⟧** (`epsRung2_exp25`) — the numeral the arm's `v ≥ 6·10^10` witness
needs, re-derived here by its own eight lines because `XThread`'s `xt_exp25` is `private`
(`2.7 < e` and `2.7^25 = 6.0826…·10^10`).  No landed file gains a declaration. -/
theorem epsRung2_exp25 : (6e10 : ℝ) ≤ Real.exp 25 := by
  have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h : Real.exp (25 : ℝ) = (Real.exp 1) ^ (25 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have hc : (2.7 : ℝ) ^ (25 : ℕ) ≤ (Real.exp 1) ^ (25 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) he1.le 25
  have hn : (6e10 : ℝ) ≤ (2.7 : ℝ) ^ (25 : ℕ) := by norm_num
  linarith

/-- **⟦THE TOWER CHARGE⟧** (`epsRung2_tower_charge`) — the ONE new fact §W3 needs, and it is the
recipe of wave 4 one level up: a tower floor RAISED by the charge pays a FACTOR of the charge at
the level below.  From `c = e^{log c} ≤ e^{Lc}` and `3.6·10^21 ≤ e^50 = (e^25)²`,

  `3.6·10^21 · c ≤ e^50 · e^{Lc} = e^{50 + Lc} ≤ e^Λ`.

At `Λ := loglog H₊` this is `3.6·10^21·c ≤ log H₊` — the source's `hLbig : 3.6·10^21 ≤ L` with a
factor `c`, which is exactly what buys the `c²`-shrunk cut at the two tower sites below. -/
theorem epsRung2_tower_charge {c Lc lam : ℝ} (hc1 : 1 ≤ c) (hLc : Real.log c ≤ Lc)
    (hlam : 50 + Lc ≤ lam) : 3.6e21 * c ≤ Real.exp lam := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hcle : c ≤ Real.exp Lc := by
    have h := Real.exp_le_exp.mpr hLc
    rwa [Real.exp_log hc0] at h
  have hsq : Real.exp 25 * Real.exp 25 = Real.exp 50 := by
    rw [← Real.exp_add]; norm_num
  have h50 : (3.6e21 : ℝ) ≤ Real.exp 50 := by nlinarith [epsRung2_exp25, hsq]
  calc (3.6e21 : ℝ) * c ≤ Real.exp 50 * Real.exp Lc :=
        mul_le_mul h50 hcle (by linarith) (Real.exp_pos 50).le
    _ = Real.exp (50 + Lc) := (Real.exp_add 50 Lc).symm
    _ ≤ Real.exp lam := Real.exp_le_exp.mpr hlam

set_option maxHeartbeats 2000000 in
-- the arm's four summands, the double exponential's collapse and the closing budget elaborate
-- in one block; the `L`-cut keeps the source's `u ≥ 8·10^41` tower step and multiplies it by
-- `c²`, so the block still does not fit the previous 1000000
/-- **⟦THE ARM, PRICED, AT A GENERIC CHARGE⟧** (`s15Arm_log_le_L`) — `s15Arm_log_le_scaled`
(`XThread.lean:345`) with every cap replaced by a term AFFINE in the charge `Lc`, and the cut
SHRUNK to `H₊/(10^20·c²)`.  The four landed caps and their `_L` forms:

* `hKcb : Kc ≤ 2^539` and `hlogc : log c ≤ 14` (the source's ONE site, `:355–356`) become the
  count ceiling `Kb` with `log Kb ≤ 197 + 20·Lc`, through `xt_log_inv_rho_le_L`: the source's
  `log (1/ρ) ≤ 403 + log c ≤ 417` becomes `log (1/ρ) ≤ 226 + 21·Lc` (`29 + 197 = 226`,
  `20 + 1 = 21`).
* `hΛ : 50 ≤ Λ` (`:363`, `:373`) becomes the gate `50 + Lc ≤ Λ`, which yields BOTH `hΛ50`
  and the new fact `hLcΛ : Lc ≤ Λ − 50` — the charge is paid by the tower floor, not capped.
* `hcb : c ≤ 1201216` (the source's ONE site, `:430`) is DROPPED: `hceil1` reads the pin
  `hδpin` alone and its constant becomes `128·838400·c = 107315200·c`.

⟦THE THREE ARITHMETIC SITES⟧ (1) the exponent: `E ≤ 7000Λ + 10500·Lc + 119600`, and
`10500·Lc ≤ 10500Λ − 525000` off `hLcΛ`, so `E ≤ 17500Λ − 405400` and the source's quadratic
step `17500Λ ≤ v²/2` closes from `Λ ≤ 2(v−1)`, `v² = L`, `v ≥ 6·10^10` exactly as before.
(2) the envelope: the source's constant `13·10^13` becomes `107315214·c` (`128·838400 =
107315200`; the `+14` absorbs the `4ω + 8ω` of the two small summands at `c ≥ 1`, since
`12 ≤ 14c`), and `hfac` needs `107315214·c ≤ H₊`, which the tower gives with 34 orders to
spare (`H₊ ≥ 3.24·10^42·c² ≥ 3.24·10^42·c`).  (3) the closing budget: `e^{L/4} ≥ 1 + L/4 ≥
9·10^20·c`, so `u ≥ 8.1·10^41·c²` and `27·u·(10^20·c²) ≤ u·u` (`27·10^20 ≤ 8.1·10^41`).

At `c = 1`, `Lc = 0` every edited site reduces to the source's line and the conclusion is the
source's `H₊/10^20` exactly.  Nothing here bears on twin primes. -/
theorem s15Arm_log_le_L {c δ₀ Kc Kb Lc : ℝ} (hc1 : 1 ≤ c) (hL0 : 0 ≤ Lc)
    (hLc : Real.log c ≤ Lc) (hδ₀ : 0 < δ₀) (hδpin : 1 / (838400 * c) ≤ δ₀)
    (hKc : 0 < Kc) (hKb1 : 1 ≤ Kb) (hKcb : Kc ≤ Kb)
    (hKbL : Real.log Kb ≤ 197 + 20 * Lc) {Hhi ω : ℕ} (hHhi : 4000000 ≤ Hhi)
    (hΛL : 50 + Lc ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ Real.log ((ω : ℕ) : ℝ) + ((Hhi : ℕ) : ℝ) / (10 ^ 20 * c ^ 2) := by
  have hc0 : (0 : ℝ) < c := by linarith
  set ρ : ℝ := doorRhoOfDelta (s12DeltaSock δ₀ Kc) with hρdef
  have hδs : 0 < s12DeltaSock δ₀ Kc := s12DeltaSock_pos hδ₀ hKc
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  -- ⟦SITE 1⟧ `403 + log c ≤ 417` becomes `29 + log Kb + log c ≤ 226 + 21·Lc`
  have hρlog : Real.log (1 / ρ) ≤ 226 + 21 * Lc :=
    le_trans (xt_log_inv_rho_le_L hc1 hδ₀ hδpin hKc hKb1 hKcb) (by linarith)
  -- ⟦THE SCALES⟧ `L = log H₊`, `Λ = loglog H₊`, and their two exponential witnesses
  set L : ℝ := Real.log ((Hhi : ℕ) : ℝ) with hLdef
  set Λ : ℝ := Real.log L with hΛdef
  have hHhiR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hHhi
  have hHhipos : (0 : ℝ) < ((Hhi : ℕ) : ℝ) := by linarith
  have hLnn : (0 : ℝ) ≤ L := Real.log_nonneg (by linarith)
  -- ⟦SITE 2⟧ the gate at the raised floor yields the source's `hΛ` AND the charge's room
  have hΛ50 : (50 : ℝ) ≤ Λ := by linarith
  have hLcΛ : Lc ≤ Λ - 50 := by linarith
  have hL1 : (1 : ℝ) < L := one_lt_log_of_loglog_ge hLnn (by norm_num : (0 : ℝ) < 50) hΛ50
  have hΛ0 : (0 : ℝ) ≤ Λ := Real.log_nonneg hL1.le
  -- `v := e^{Λ/2}`, so `v² = L` and `v ≥ 6·10^{10}`
  set v : ℝ := Real.exp (Λ / 2) with hvdef
  have hvv : v * v = L := by
    rw [hvdef, ← Real.exp_add, show Λ / 2 + Λ / 2 = Λ by ring, hΛdef]
    exact Real.exp_log (by linarith)
  have hv : (6e10 : ℝ) ≤ v := by
    refine le_trans epsRung2_exp25 ?_
    rw [hvdef]
    exact Real.exp_le_exp.mpr (by linarith)
  have hΛv : Λ ≤ 2 * (v - 1) := by
    have := Real.add_one_le_exp (Λ / 2)
    rw [← hvdef] at this
    linarith
  -- ⟦THE TOWER CHARGE⟧ the source's `hLbig : 3.6·10^21 ≤ L`, with the charge's factor `c`
  have hexpΛ : Real.exp Λ = L := by
    rw [hΛdef]; exact Real.exp_log (by linarith)
  have hcL : (3.6e21 : ℝ) * c ≤ L := by
    have h := epsRung2_tower_charge hc1 hLc hΛL
    rwa [hexpΛ] at h
  -- `u := e^{L/2}`, so `u² = H₊`
  set u : ℝ := Real.exp (L / 2) with hudef
  have huu : u * u = ((Hhi : ℕ) : ℝ) := by
    rw [hudef, ← Real.exp_add, show L / 2 + L / 2 = L by ring, hLdef]
    exact Real.exp_log hHhipos
  have hLu : L ≤ 2 * (u - 1) := by
    have := Real.add_one_le_exp (L / 2)
    rw [← hudef] at this
    linarith
  have huc : (1.8e21 : ℝ) * c ≤ u := by linarith
  -- ⟦SITE 3 — THE EXPONENT⟧ `E ≤ L/2`, now through the LINEAR step `E ≤ 17500Λ − 405400`
  set E : ℝ := 7000 * Λ + 500 * Real.log (1 / ρ) + 6600 + 36 * 0 with hEdef
  have hE : E ≤ L / 2 := by
    rw [hEdef]
    have hlin : 7000 * Λ + 500 * Real.log (1 / ρ) + 6600 + 36 * 0 ≤ 17500 * Λ - 405400 := by
      linarith [hρlog, hLcΛ]
    have hquad : 17500 * Λ - 405400 ≤ L / 2 := by nlinarith [hΛv, hvv, hv]
    linarith
  have hexpE : Real.exp E ≤ u := by
    rw [hudef]; exact Real.exp_le_exp.mpr hE
  -- ⟦THE ARM, BOUNDED⟧
  have hωnn : (0 : ℝ) ≤ ((ω : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlogωnn : (0 : ℝ) ≤ Real.log ((ω : ℕ) : ℝ) := Real.log_natCast_nonneg ω
  -- the `ρ`-arm's closed form
  have harc : arcDen 12 Hhi = Real.exp (12 * Λ) := by
    rw [arcDen, ← hLdef, Real.rpow_def_of_pos (by linarith), hΛdef]
    congr 1
    ring
  have hG : gArmDoorRho 0 0 ((ω : ℕ) : ℝ) ρ Hhi
      = 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by
    have hsplit : Real.exp (12 * Λ + Real.exp E)
        = Real.exp (12 * Λ) * Real.exp (Real.exp E) := Real.exp_add _ _
    have hnn : (0 : ℝ) ≤ 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ) * Real.exp (Real.exp E) := by
      positivity
    rw [gArmDoorRho, harc, ← hLdef, ← hΛdef, ← hEdef, max_eq_right hnn, hsplit]
    ring
  -- the sum, cast
  have hcast : ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
      = 2 * ((ω : ℕ) : ℝ) * (((Hhi : ℕ) : ℝ) + 2) + 8 * ((ω : ℕ) : ℝ)
        + ((⌈128 * ((ω : ℕ) : ℝ) / δ₀⌉₊ : ℕ) : ℝ)
        + ((⌈gArmDoorRho 0 0 ((ω : ℕ) : ℝ) ρ Hhi⌉₊ : ℕ) : ℝ) := by
    rw [s15Arm, s13GArm']
    push_cast
    ring
  -- ⟦SITE 4 — THE CEILING⟧ the pin alone: `128·838400·c = 107315200·c`, no cap on `c`
  have hceil1 : ((⌈128 * ((ω : ℕ) : ℝ) / δ₀⌉₊ : ℕ) : ℝ)
      ≤ 128 * 838400 * c * ((ω : ℕ) : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ 128 * ((ω : ℕ) : ℝ) / δ₀ := by positivity
    have hlt : ((⌈128 * ((ω : ℕ) : ℝ) / δ₀⌉₊ : ℕ) : ℝ) < 128 * ((ω : ℕ) : ℝ) / δ₀ + 1 :=
      Nat.ceil_lt_add_one h0
    have hdiv : 128 * ((ω : ℕ) : ℝ) / δ₀ ≤ 128 * 838400 * c * ((ω : ℕ) : ℝ) := by
      rw [div_le_iff₀ hδ₀]
      have hpin' : (1 : ℝ) ≤ δ₀ * (838400 * c) := by
        rw [← div_le_iff₀ (by positivity : (0 : ℝ) < 838400 * c)]
        exact hδpin
      nlinarith [hωnn, hpin']
    linarith
  have hceil2 : ((⌈gArmDoorRho 0 0 ((ω : ℕ) : ℝ) ρ Hhi⌉₊ : ℕ) : ℝ)
      ≤ 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) + 1 := by
    rw [hG]
    have h0 : (0 : ℝ) ≤ 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by positivity
    linarith [Nat.ceil_lt_add_one h0]
  -- ⟦THE ENVELOPE⟧ `S ≤ (ω+1)·e^Y` at `Y = L + 12λ + e^E + 6`, envelope constant `107315214·c`
  have hX1 : (1 : ℝ) ≤ Real.exp (12 * Λ + Real.exp E) :=
    Real.one_le_exp (by positivity)
  have hHhibig : (107315214 : ℝ) * c ≤ ((Hhi : ℕ) : ℝ) := by
    have hnn : (0 : ℝ) ≤ 1.8e21 * c := by positivity
    have hsq : (1.8e21 * c) * (1.8e21 * c) ≤ u * u := mul_le_mul huc huc hnn (by linarith)
    nlinarith [hsq, huu, hc1, hc0]
  have he6 : (19 : ℝ) ≤ Real.exp 6 := by
    have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h : Real.exp (6 : ℝ) = (Real.exp 1) ^ (6 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    have hc : (2.7 : ℝ) ^ (6 : ℕ) ≤ (Real.exp 1) ^ (6 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he1.le 6
    have hn : (19 : ℝ) ≤ (2.7 : ℝ) ^ (6 : ℕ) := by norm_num
    linarith
  have hYeq : Real.exp (L + (12 * Λ + Real.exp E) + 6)
      = ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) * Real.exp 6 := by
    rw [Real.exp_add, Real.exp_add, hLdef, Real.exp_log hHhipos]
  have henv : ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
      ≤ (((ω : ℕ) : ℝ) + 1) * Real.exp (L + (12 * Λ + Real.exp E) + 6) := by
    rw [hcast, hYeq]
    have hfac : 2 * ((Hhi : ℕ) : ℝ) + 107315214 * c
          + 16 * Real.exp (12 * Λ + Real.exp E)
        ≤ ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) * Real.exp 6 := by
      have h1 : 2 * ((Hhi : ℕ) : ℝ)
          ≤ 2 * (((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E)) := by
        nlinarith [hX1, hHhiR]
      have h2 : (107315214 : ℝ) * c
          ≤ ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by
        nlinarith [hX1, hHhibig, hHhiR]
      have h3 : 16 * Real.exp (12 * Λ + Real.exp E)
          ≤ 16 * (((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E)) := by
        nlinarith [hX1, hHhiR, Real.exp_pos (12 * Λ + Real.exp E)]
      have hprodnn : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by positivity
      nlinarith [h1, h2, h3, he6, hprodnn]
    -- the `+14` of the envelope constant absorbs the two small summands: `12 ≤ 14c` at `c ≥ 1`
    have hcω : (0 : ℝ) ≤ (c - 1) * ((ω : ℕ) : ℝ) := mul_nonneg (by linarith) hωnn
    have hstep : 2 * ((ω : ℕ) : ℝ) * (((Hhi : ℕ) : ℝ) + 2) + 8 * ((ω : ℕ) : ℝ)
        + (128 * 838400 * c * ((ω : ℕ) : ℝ) + 1)
        + (16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) + 1)
        ≤ (((ω : ℕ) : ℝ) + 1) * (2 * ((Hhi : ℕ) : ℝ) + 107315214 * c
            + 16 * Real.exp (12 * Λ + Real.exp E)) := by
      nlinarith [hωnn, hX1, hHhiR, hcω, hc1, Real.exp_pos (12 * Λ + Real.exp E)]
    have hmul : (((ω : ℕ) : ℝ) + 1) * (2 * ((Hhi : ℕ) : ℝ) + 107315214 * c
          + 16 * Real.exp (12 * Λ + Real.exp E))
        ≤ (((ω : ℕ) : ℝ) + 1)
          * (((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) * Real.exp 6) :=
      mul_le_mul_of_nonneg_left hfac (by linarith)
    linarith [hceil1, hceil2, hstep, hmul]
  -- ⟦THE LOG⟧
  rcases Nat.eq_zero_or_pos (s15Arm δ₀ ρ Hhi ω) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    have : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / (10 ^ 20 * c ^ 2) := by positivity
    linarith
  · have hSpos : (0 : ℝ) < ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ) := by exact_mod_cast hpos
    have hlog := Real.log_le_log hSpos henv
    have hprod : Real.log ((((ω : ℕ) : ℝ) + 1) * Real.exp (L + (12 * Λ + Real.exp E) + 6))
        = Real.log (((ω : ℕ) : ℝ) + 1) + (L + (12 * Λ + Real.exp E) + 6) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
    -- `log(ω+1) ≤ log ω + log 2`
    have hω1 : Real.log (((ω : ℕ) : ℝ) + 1) ≤ Real.log ((ω : ℕ) : ℝ) + Real.log 2 := by
      rcases Nat.eq_zero_or_pos ω with hz | hz
      · rw [hz]
        simp only [Nat.cast_zero, Real.log_zero, zero_add, Real.log_one]
        linarith [Real.log_two_gt_d9]
      · have hω1R : (1 : ℝ) ≤ ((ω : ℕ) : ℝ) := by exact_mod_cast hz
        have hle : ((ω : ℕ) : ℝ) + 1 ≤ 2 * ((ω : ℕ) : ℝ) := by linarith
        have h := Real.log_le_log (by linarith : (0 : ℝ) < ((ω : ℕ) : ℝ) + 1) hle
        rwa [Real.log_mul (by norm_num) (by linarith), add_comm (Real.log 2)] at h
    -- the closing budget
    have hΛle : Λ ≤ L := by nlinarith [hΛv, hvv, hv]
    have hclose : Real.log 2 + (L + (12 * Λ + Real.exp E) + 6)
        ≤ ((Hhi : ℕ) : ℝ) / (10 ^ 20 * c ^ 2) := by
      -- ⟦SITE 5 — THE TOWER STEP⟧ `u = (e^{L/4})² ≥ (1 + L/4)²`, and with `L ≥ 3.6·10^21·c`
      -- the linear witness `u ≥ 1.8·10^21·c` is upgraded to `u ≥ 8.1·10^41·c²` — which is what
      -- buys the SHRINKING cut `H₊/(10^20·c²)`.  The headroom is a TOWER and the charge is a
      -- factor, so the whole `c²` is free: `27·10^20 ≤ 8.1·10^41` with 20 orders to spare.
      have hq := Real.add_one_le_exp (L / 4)
      have hq0 : (0 : ℝ) ≤ Real.exp (L / 4) := (Real.exp_pos _).le
      have hqL : (9 * 10 ^ 20 : ℝ) * c ≤ Real.exp (L / 4) := by linarith only [hq, hcL]
      have hqnn : (0 : ℝ) ≤ (9 * 10 ^ 20 : ℝ) * c := by positivity
      have hsq : Real.exp (L / 4) * Real.exp (L / 4) = u := by
        rw [← Real.exp_add, show L / 4 + L / 4 = L / 2 by ring, hudef]
      have hu41 : (8.1e41 : ℝ) * c ^ 2 ≤ u := by
        rw [← hsq]
        calc (8.1e41 : ℝ) * c ^ 2 = ((9 * 10 ^ 20 : ℝ) * c) * ((9 * 10 ^ 20 : ℝ) * c) := by ring
          _ ≤ Real.exp (L / 4) * Real.exp (L / 4) := mul_le_mul hqL hqL hqnn hq0
      -- keep every step LINEAR in `u`: the one product is isolated in `hsquare`.
      have hupos : (0 : ℝ) < u := by rw [hudef]; exact Real.exp_pos _
      have hlin : L + 12 * Λ + Real.exp E + 6.7 ≤ 27 * u := by
        linarith only [hexpE, hΛle, hLu]
      have h27 : (27 : ℝ) * 10 ^ 20 * c ^ 2 ≤ u := by linarith [hu41, sq_nonneg c]
      have hsquare : 27 * u * (10 ^ 20 * c ^ 2) ≤ u * u := by
        have hm := mul_le_mul_of_nonneg_right h27 hupos.le
        linarith only [hm]
      have hkpos : (0 : ℝ) < 10 ^ 20 * c ^ 2 := by positivity
      have hstep : L + 12 * Λ + Real.exp E + 6.7 ≤ ((Hhi : ℕ) : ℝ) / (10 ^ 20 * c ^ 2) := by
        rw [← huu, le_div_iff₀ hkpos]
        have hm2 := mul_le_mul_of_nonneg_right hlin hkpos.le
        linarith only [hm2, hsquare]
      linarith [Real.log_two_lt_d9]
    linarith [hlog, hprod, hω1, hclose]

/-- **⟦THE ARM AT THE LANDED CUT⟧** (`s15Arm_log_le_L_cut20`) — `s15Arm_log_le_L` weakened back
to the landed `H₊/10^20`, for the `h`-lane consumers that read that shape
(`StrideGrade12bWalls.lean:113`).  The step is `H₊/(10^20·c²) ≤ H₊/10^20` at `c ≥ 1`; the charge
is spent entirely inside the arm and nothing of it reaches the conclusion. -/
theorem s15Arm_log_le_L_cut20 {c δ₀ Kc Kb Lc : ℝ} (hc1 : 1 ≤ c) (hL0 : 0 ≤ Lc)
    (hLc : Real.log c ≤ Lc) (hδ₀ : 0 < δ₀) (hδpin : 1 / (838400 * c) ≤ δ₀)
    (hKc : 0 < Kc) (hKb1 : 1 ≤ Kb) (hKcb : Kc ≤ Kb)
    (hKbL : Real.log Kb ≤ 197 + 20 * Lc) {Hhi ω : ℕ} (hHhi : 4000000 ≤ Hhi)
    (hΛL : 50 + Lc ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ Real.log ((ω : ℕ) : ℝ) + ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
  have h := s15Arm_log_le_L (ω := ω) hc1 hL0 hLc hδ₀ hδpin hKc hKb1 hKcb hKbL hHhi hΛL
  have hc0 : (0 : ℝ) < c := by linarith
  have hHnn : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := Nat.cast_nonneg _
  have hc2 : (1 : ℝ) ≤ c ^ 2 := by nlinarith [hc1]
  have hle : ((Hhi : ℕ) : ℝ) / (10 ^ 20 * c ^ 2) ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 10 ^ 20)]
    nlinarith [hHnn, hc2]
  linarith [h, hle]

/-- **⟦THE SUM SPLIT'S `log 2`, AT A GENERIC CHARGE⟧** (`epsChain_arm_split_L`) —
`epsChain_arm_split_cap` (`FlatDoorEpsChain.lean:79`) with the interval cap `ε ≥ 1/(500·8103)`
replaced by the generic pin `ε ≥ 1/(500·c)` and the cut by the shrinking `H₊/(10^20·c²)`.

⛔ THE SOURCE'S ROUTE DOES NOT SURVIVE: it bought `H₊ ≥ 10^21` from `log H₊ ≥ e^50` through
`log H₊ ≤ H₊ − 1`, which is LINEAR in `H₊` and therefore pays no `c²` demand.  This goes through
the square root instead: `u := e^{(log H₊)/2} ≥ 1 + (log H₊)/2 ≥ 1.8·10^21·c`, so
`H₊ = u·u ≥ 3.24·10^42·c²`.

⟦THE DEMAND⟧ `1/(500·c) ≤ ε` gives `ε² ≥ 1/(250000·c²)`, so the margin is
`H₊/c² · (1/250000 − 10^{-20})` and the demand is `H₊/c² ≥ log 2 / (1/250000 − 10^{-20}) =
173286.7951…` against `3.24·10^42`: **the headroom is a tower and the corner is a constant**, with
37 orders to spare. -/
theorem epsChain_arm_split_L {ε : ℚ} {c : ℕ} (hc1 : 1 ≤ c)
    (hcε : (1 : ℚ) / (500 * (c : ℚ)) ≤ ε) {Lc : ℝ} (hLc : Real.log ((c : ℕ) : ℝ) ≤ Lc)
    {Hhi : ℕ} (hH4 : 4000000 ≤ Hhi)
    (hll : 50 + Lc ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log 2 ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ)
      - ((Hhi : ℕ) : ℝ) / (10 ^ 20 * ((c : ℕ) : ℝ) ^ 2) := by
  have hcR : (1 : ℝ) ≤ ((c : ℕ) : ℝ) := by exact_mod_cast hc1
  have hcpos : (0 : ℝ) < ((c : ℕ) : ℝ) := by linarith
  have hcne : ((c : ℕ) : ℝ) ≠ 0 := ne_of_gt hcpos
  have hcQ : (1 : ℚ) ≤ ((c : ℕ) : ℚ) := by exact_mod_cast hc1
  -- ⟦THE PIN AT GENERIC `c`⟧ `1/(500·c) ≤ ε` reads `1 ≤ 500·c·ε`, hence `ε² ≥ 1/(250000·c²)`
  have hqcap : (1 : ℚ) ≤ 500 * ((c : ℕ) : ℚ) * ε := by
    have h := (div_le_iff₀ (show (0 : ℚ) < 500 * ((c : ℕ) : ℚ) by linarith)).mp hcε
    calc (1 : ℚ) ≤ ε * (500 * ((c : ℕ) : ℚ)) := h
      _ = 500 * ((c : ℕ) : ℚ) * ε := by ring
  have hcapR : (1 : ℝ) ≤ 500 * ((c : ℕ) : ℝ) * (ε : ℝ) := by exact_mod_cast hqcap
  have hsq : (1 : ℝ) ≤ 250000 * ((c : ℕ) : ℝ) ^ 2 * (ε : ℝ) ^ 2 := by
    have h := one_le_pow₀ (n := 2) hcapR
    calc (1 : ℝ) ≤ (500 * ((c : ℕ) : ℝ) * (ε : ℝ)) ^ 2 := h
      _ = 250000 * ((c : ℕ) : ℝ) ^ 2 * (ε : ℝ) ^ 2 := by ring
  have hε2 : (1 : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2) ≤ (ε : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hsq]
  -- ⟦THE GATE⟧ the raised floor contains the landed one, since `log c ≥ 0` at `c ≥ 1`
  have hlogc0 : (0 : ℝ) ≤ Real.log ((c : ℕ) : ℝ) := Real.log_nonneg hcR
  have hΛ50 : (50 : ℝ) ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ)) := by linarith
  have hHR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hH4
  have hHpos : (0 : ℝ) < ((Hhi : ℕ) : ℝ) := by linarith
  have hLnn : (0 : ℝ) ≤ Real.log ((Hhi : ℕ) : ℝ) := Real.log_nonneg (by linarith)
  have hL1 : (1 : ℝ) < Real.log ((Hhi : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hLnn (by norm_num : (0 : ℝ) < 50) hΛ50
  have hexpΛ : Real.exp (Real.log (Real.log ((Hhi : ℕ) : ℝ))) = Real.log ((Hhi : ℕ) : ℝ) :=
    Real.exp_log (by linarith)
  have hcL : (3.6e21 : ℝ) * ((c : ℕ) : ℝ) ≤ Real.log ((Hhi : ℕ) : ℝ) := by
    have h := epsRung2_tower_charge hcR hLc hll
    rwa [hexpΛ] at h
  -- ⟦THE SQUARE ROOT⟧ `u² = H₊` and `u ≥ 1.8·10^21·c`, so `H₊ ≥ 3.24·10^42·c²`
  set u : ℝ := Real.exp (Real.log ((Hhi : ℕ) : ℝ) / 2) with hudef
  have huu : u * u = ((Hhi : ℕ) : ℝ) := by
    rw [hudef, ← Real.exp_add,
      show Real.log ((Hhi : ℕ) : ℝ) / 2 + Real.log ((Hhi : ℕ) : ℝ) / 2
        = Real.log ((Hhi : ℕ) : ℝ) by ring]
    exact Real.exp_log hHpos
  have hLu : Real.log ((Hhi : ℕ) : ℝ) ≤ 2 * (u - 1) := by
    have := Real.add_one_le_exp (Real.log ((Hhi : ℕ) : ℝ) / 2)
    rw [← hudef] at this
    linarith
  have hu : (1.8e21 : ℝ) * ((c : ℕ) : ℝ) ≤ u := by linarith
  have hnn : (0 : ℝ) ≤ 1.8e21 * ((c : ℕ) : ℝ) := by positivity
  have hsq2 : (1.8e21 * ((c : ℕ) : ℝ)) * (1.8e21 * ((c : ℕ) : ℝ)) ≤ u * u :=
    mul_le_mul hu hu hnn (by linarith)
  have hHbig : (3.24e42 : ℝ) * ((c : ℕ) : ℝ) ^ 2 ≤ ((Hhi : ℕ) : ℝ) := by
    linarith [hsq2, huu]
  -- ⟦THE MARGIN⟧ `H₊/c² ≥ 3.24·10^42` against a demand of `173286.7951…`
  have hc2pos : (0 : ℝ) < ((c : ℕ) : ℝ) ^ 2 := by positivity
  have ht : (3.24e42 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / ((c : ℕ) : ℝ) ^ 2 := by
    rw [le_div_iff₀ hc2pos]
    linarith [hHbig]
  have hsub : ((Hhi : ℕ) : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2)
      - ((Hhi : ℕ) : ℝ) / (10 ^ 20 * ((c : ℕ) : ℝ) ^ 2)
      = (((Hhi : ℕ) : ℝ) / ((c : ℕ) : ℝ) ^ 2) * (1 / 250000 - 1 / 10 ^ 20) := by
    field_simp
  have hlow : Real.log 2 ≤ ((Hhi : ℕ) : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2)
      - ((Hhi : ℕ) : ℝ) / (10 ^ 20 * ((c : ℕ) : ℝ) ^ 2) := by
    rw [hsub]
    linarith [ht, Real.log_two_lt_d9]
  have hstep : ((Hhi : ℕ) : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2)
      ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hε2 hHpos.le
    calc ((Hhi : ℕ) : ℝ) / (250000 * ((c : ℕ) : ℝ) ^ 2)
        = 1 / (250000 * ((c : ℕ) : ℝ) ^ 2) * ((Hhi : ℕ) : ℝ) := by ring
      _ ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := h
  linarith [hlow, hstep]

/-! ### §W3.2 — ⟦THE GATE FAMILY, ITS TOWER FLOOR A PARAMETER⟧

⛔ THE DESIGN FINDING THIS SECTION ANSWERS.  The landed `XCeilGate` (`XThread.lean:68`) carries
its tower floor as a NUMERAL — `50 ≤ loglog H₊` — and the rider a conditional hop must prove is
quantified over EVERY `(H₊, ω)` on that gate.  On that gate the arm's heart `E ≤ (log H₊)/2` is
`7000·50 + 10500·Lc + 119600 ≤ e^50/2`, which stops closing at

  `Lc > (e^50/2 − 7000·50 − 119600)/10500 = 2.4689·10^17`,

so NO `_L` arm lemma can be applied inside a rider on the LANDED gate at generic `ε`.  The three
`def`s below are the landed three with the floor a PARAMETER; the landed gate is `Λ₀ = 50` (the
three `_fifty` twins are `Iff.rfl`, so the new family is not a new notion), and a HIGHER floor is
a SMALLER gate, so a rider on a lower floor is a rider on a higher one (`_mono`).  W6's forms
carry `XCeilRiderAt (50 + Lc)` and the ninth arm on `A` pays `50 + Lc ≤ 3.2·A`. -/

/-- **⟦THE WIDTH GATE, AT A PARAMETRIC TOWER FLOOR⟧** (`XCeilGateAt`) — `XCeilGate` with `50`
replaced by `lam0`.  `XCeilGateAt 50 = XCeilGate` definitionally (`xCeilGateAt_fifty`). -/
def XCeilGateAt (lam0 : ℝ) (eps : ℚ) (Hhi ω : ℕ) : Prop :=
  4000000 ≤ Hhi ∧ lam0 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ)) ∧
    Real.log ((ω : ℕ) : ℝ) + (eps : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ)
      ≤ 31 / (eps : ℝ) * ((Hhi : ℕ) : ℝ)

/-- **⟦THE BUILDER-SIDE RIDER, AT A PARAMETRIC FLOOR⟧** (`XCeilRiderAt`) — `XCeilRider` on
`XCeilGateAt lam0`. -/
def XCeilRiderAt (lam0 : ℝ) (eps : ℚ) (g : ℕ → ℕ → ℕ) : Prop :=
  ∀ Hhi ω : ℕ, XCeilGateAt lam0 eps Hhi ω →
    Real.log ((g Hhi ω : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((Hhi : ℕ) : ℝ)

/-- **⟦THE CALLER-SIDE RIDER, AT A PARAMETRIC FLOOR⟧** (`XCeilRiderStrictAt`) —
`XCeilRiderStrict` on `XCeilGateAt lam0`: the same bound with the `ε²·H₊` margin kept in hand. -/
def XCeilRiderStrictAt (lam0 : ℝ) (eps : ℚ) (g : ℕ → ℕ → ℕ) : Prop :=
  ∀ Hhi ω : ℕ, XCeilGateAt lam0 eps Hhi ω →
    Real.log ((g Hhi ω : ℕ) : ℝ) + (eps : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ)
      ≤ 31 / (eps : ℝ) * ((Hhi : ℕ) : ℝ)

/-- **⟦THE TWIN AT THE LANDED NUMERAL⟧** (`xCeilGateAt_fifty`) — the new family AT `50` IS the
landed gate, definitionally. -/
theorem xCeilGateAt_fifty {eps : ℚ} {Hhi ω : ℕ} :
    XCeilGateAt 50 eps Hhi ω ↔ XCeilGate eps Hhi ω := Iff.rfl

/-- **⟦THE TWIN AT THE LANDED NUMERAL⟧** (`xCeilRiderAt_fifty`). -/
theorem xCeilRiderAt_fifty {eps : ℚ} {g : ℕ → ℕ → ℕ} :
    XCeilRiderAt 50 eps g ↔ XCeilRider eps g := Iff.rfl

/-- **⟦THE TWIN AT THE LANDED NUMERAL⟧** (`xCeilRiderStrictAt_fifty`). -/
theorem xCeilRiderStrictAt_fifty {eps : ℚ} {g : ℕ → ℕ → ℕ} :
    XCeilRiderStrictAt 50 eps g ↔ XCeilRiderStrict eps g := Iff.rfl

/-- **⟦A HIGHER FLOOR IS A SMALLER GATE⟧** (`xCeilGateAt_mono`) — the floor sits in a HYPOTHESIS
conjunct, so raising it SHRINKS the set of `(H₊, ω)` the gate admits. -/
theorem xCeilGateAt_mono {a b : ℝ} (hab : a ≤ b) {eps : ℚ} {Hhi ω : ℕ}
    (h : XCeilGateAt b eps Hhi ω) : XCeilGateAt a eps Hhi ω :=
  ⟨h.1, le_trans hab h.2.1, h.2.2⟩

/-- **⟦A RIDER ON A LOWER FLOOR IS A RIDER ON A HIGHER ONE⟧** (`xCeilRiderAt_mono`) — the gate is
in hypothesis position inside the rider, so the direction FLIPS against `xCeilGateAt_mono`. -/
theorem xCeilRiderAt_mono {a b : ℝ} (hab : a ≤ b) {eps : ℚ} {g : ℕ → ℕ → ℕ}
    (h : XCeilRiderAt a eps g) : XCeilRiderAt b eps g :=
  fun Hhi ω hgate => h Hhi ω (xCeilGateAt_mono hab hgate)

/-- **⟦THE SAME, STRICT⟧** (`xCeilRiderStrictAt_mono`). -/
theorem xCeilRiderStrictAt_mono {a b : ℝ} (hab : a ≤ b) {eps : ℚ} {g : ℕ → ℕ → ℕ}
    (h : XCeilRiderStrictAt a eps g) : XCeilRiderStrictAt b eps g :=
  fun Hhi ω hgate => h Hhi ω (xCeilGateAt_mono hab hgate)

/-- **⟦THE HEAD-SHAPED FLAT BUILDER ON THE PARAMETRIC GATE⟧**
(`chowlaRegimeFlat_exists_param_head_xceil_at`) — `chowlaRegimeFlat_exists_param_head_xceil`
(`XThread.lean:96`) with the rider asked on `XCeilGateAt lam0` instead of `XCeilGate`.  The seven
exported conjuncts are the landed builder's, byte for byte.

BODY: the source's, with ONE edit.  The source's `hll50 : 50 ≤ loglog R.Hhi` — read at EXACTLY
ONE line, the gate's discharge (`XThread.lean:178`; measured, not assumed) — becomes
`hll : lam0 ≤ loglog R.Hhi`, off the regime's own design law `R.hflat : 3.2·R.A ≤ loglog R.Hlo`
with `hRA : R.A = A`, the caller's `hlamA : lam0 ≤ 3.2·A`, and the same `Hlo ≤ Hhi` monotone
step.  At `lam0 = 50` the hypothesis `hlamA` is `50 ≤ 3.2·A`, which `hA : 26 ≤ A` already gives
(`3.2 · 26 = 83.2`), so this sibling is not weaker than its source at the source's own floor. -/
theorem chowlaRegimeFlat_exists_param_head_xceil_at (lam0 A : ℝ) (hA : 26 ≤ A)
    (hlamA : lam0 ≤ 3.2 * A) (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ)
    (g : ℕ → ℕ → ℕ) (hg : XCeilRiderAt lam0 eps g) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      g R.Hhi R.ω ≤ R.x ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
  obtain ⟨R, hReps, hRA, hRHlo, hRcap, hRwid, hRx⟩ :=
    chowlaRegimeFlat_exists_param_gen_ceiling A hA eps heps heps1 Hlo₀
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  -- ⟦THE ENDPOINT FLOOR⟧
  have hHhi4 : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
  have hHhiR : (4000000 : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast hHhi4
  have hHlo4 : (4000000 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast R.hHlo_floor
  -- ⟦THE `loglog` FLOOR AT THE PARAMETER⟧ off `lam0 ≤ 3.2·A = 3.2·R.A ≤ loglog H₋`
  have hll : lam0 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) := by
    have hflat : 3.2 * R.A ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) := R.hflat
    rw [hRA] at hflat
    have hlogpos : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
      Real.log_pos (by linarith)
    have hmono : Real.log ((R.Hlo : ℕ) : ℝ) ≤ Real.log ((R.Hhi : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      exact_mod_cast R.hHlohi
    have := Real.log_le_log hlogpos hmono
    linarith
  -- ⟦THE WIDTH WINDOW⟧ the majorant field read against the ceiling
  have hωgate : Real.log ((R.ω : ℕ) : ℝ) + (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ)
      ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    set P : ℕ := 4 ^ ⌊R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)⌋₊ with hPdef
    set n : ℕ := ⌊R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)⌋₊ with hndef
    have hPH : 8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ) ≤ ((R.x : ℕ) : ℝ) := R.hPHheadroom
    have hP1 : (1 : ℝ) ≤ ((P : ℕ) : ℝ) := by
      rw [hPdef]
      have : (1 : ℕ) ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
      exact_mod_cast this
    have hω1 : (1 : ℝ) ≤ ((R.ω : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ R.ω := le_trans (by norm_num) R.hω
      exact_mod_cast this
    -- `log 8 + 2·log P + log ω ≤ log x`
    have hpos : (0 : ℝ) < 8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ) := by positivity
    have hlogle : Real.log (8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ))
        ≤ Real.log ((R.x : ℕ) : ℝ) := Real.log_le_log hpos hPH
    have hsplit : Real.log (8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ))
        = Real.log 8 + 2 * Real.log ((P : ℕ) : ℝ) + Real.log ((R.ω : ℕ) : ℝ) := by
      rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow]
      push_cast
      ring
    -- `log P = n·log 4 ≥ (ε²H₊ − 1)·log 4`
    have hlogP : Real.log ((P : ℕ) : ℝ) = (n : ℝ) * Real.log 4 := by
      rw [hPdef]
      have h4 : ((4 ^ n : ℕ) : ℝ) = (4 : ℝ) ^ n := by push_cast; ring
      rw [h4, Real.log_pow]
    have hnge : (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) - 1 ≤ (n : ℝ) := by
      have hQ : R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ) < (n : ℚ) + 1 := by
        rw [hndef]; exact Nat.lt_floor_add_one _
      have hR : (R.eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) < (n : ℝ) + 1 := by exact_mod_cast hQ
      rw [hReps] at hR
      linarith
    have hlog4 : (1.3862 : ℝ) ≤ Real.log 4 := by
      have h : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      rw [h]; linarith [Real.log_two_gt_d9]
    have hlog8 : (2.0794 : ℝ) ≤ Real.log 8 := by
      have h : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      rw [h]; linarith [Real.log_two_gt_d9]
    -- ⟦THE COPRIMALITY FLOOR⟧ `ε²·H₊ ≥ 2`
    have hcop : (2 : ℝ) ≤ (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) := by
      have hQ : ((R.a : ℕ) : ℚ) ≤ R.eps ^ 2 * ((R.Hlo : ℕ) : ℚ) / 2 := R.hcoprime
      have ha1 : (1 : ℚ) ≤ ((R.a : ℕ) : ℚ) := by exact_mod_cast R.ha
      have hQ2 : (2 : ℚ) ≤ R.eps ^ 2 * ((R.Hlo : ℕ) : ℚ) := by linarith
      have hR2 : (2 : ℝ) ≤ (R.eps : ℝ) ^ 2 * ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast hQ2
      rw [hReps] at hR2
      have hmono : (eps : ℝ) ^ 2 * ((R.Hlo : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast R.hHlohi) (sq_nonneg _)
      linarith
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith [hlogle, hsplit, hlogP, hnge, hlog4, hlog8, hRx, hcop, hnn]
  have hgx : Real.log ((g R.Hhi R.ω : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) :=
    hg R.Hhi R.ω ⟨hHhi4, hll, hωgate⟩
  refine ⟨regimeFlatEnlargeX R (le_max_left R.x (g R.Hhi R.ω)), hReps, hRA, hRHlo,
    le_max_right _ _, hRcap, hRwid, ?_⟩
  simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_Hhi]
  rcases le_total R.x (g R.Hhi R.ω) with h | h
  · rw [max_eq_right h]; exact hgx
  · rw [max_eq_left h]; exact hRx

/-! ### §W3.3 — ⟦THE RIDER STEP⟧ the conditional hop's `hg'` block, as a lemma on the new gate -/

/-- **⟦THE RIDER STEP AT A GENERIC CHARGE⟧** (`xCeilRiderAt_arm_add`) — the conditional hop's
`hg'` block (`FlatDoorEpsChain.lean:1022–1041`) lifted out as a standalone lemma and re-cut on
`XCeilGateAt (50 + Lc)`: if `g` satisfies the STRICT rider on that gate, then `s15Arm + g`
satisfies the plain one.  This is what proves the new conclusion has the shape its consumer
needs, and it is the wave's END-TO-END CHECK: the arm's cut and the split's cut must be the SAME
TERM, token for token, or the two closing `linarith`s see two atoms.

BODY: the source block with `epsChain_arm_split_cap ↦ epsChain_arm_split_L`,
`s15Arm_log_le_scaled (c := 8103) ↦ s15Arm_log_le_L (c := ((c : ℕ) : ℝ))`, `hHdiv` at the new
cut `H₊/(10^20·c²)`, and the closing `xt_log_add_le` unchanged.  The source's `rw [hρdef, hδsdef]`
is gone because the `ρ` of the statement here is already written out.  Nothing here bears on twin
primes. -/
theorem xCeilRiderAt_arm_add {ε : ℚ} {c : ℕ} (hc1 : 1 ≤ c)
    (hcε : (1 : ℚ) / (500 * (c : ℚ)) ≤ ε) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hLc : Real.log ((c : ℕ) : ℝ) ≤ Lc) {δ₀ Kc Kb : ℝ} (hδ₀ : 0 < δ₀)
    (hδpin : 1 / (838400 * ((c : ℕ) : ℝ)) ≤ δ₀) (hKc : 0 < Kc) (hKb1 : 1 ≤ Kb)
    (hKcb : Kc ≤ Kb) (hKbL : Real.log Kb ≤ 197 + 20 * Lc) {g : ℕ → ℕ → ℕ}
    (hg : XCeilRiderStrictAt (50 + Lc) ε g) :
    XCeilRiderAt (50 + Lc) ε
      (fun Hhi ω => s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω + g Hhi ω) := by
  intro Hhi ω hgate
  obtain ⟨hH4, hll, hωw⟩ := hgate
  have hcR : (1 : ℝ) ≤ ((c : ℕ) : ℝ) := by exact_mod_cast hc1
  have hHnn : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by positivity
  have hsplit2 : Real.log 2
      ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ)
        - ((Hhi : ℕ) : ℝ) / (10 ^ 20 * ((c : ℕ) : ℝ) ^ 2) :=
    epsChain_arm_split_L hc1 hcε hLc hH4 hll
  have harm : Real.log ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ Real.log ((ω : ℕ) : ℝ) + ((Hhi : ℕ) : ℝ) / (10 ^ 20 * ((c : ℕ) : ℝ) ^ 2) :=
    s15Arm_log_le_L (c := ((c : ℕ) : ℝ)) hcR hL0 hLc hδ₀ hδpin hKc hKb1 hKcb hKbL hH4 hll
  have hgb := hg Hhi ω ⟨hH4, hll, hωw⟩
  have hHdiv : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / (10 ^ 20 * ((c : ℕ) : ℝ) ^ 2) := by positivity
  have harm' : Real.log ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - Real.log 2 := by linarith
  have hgb' : Real.log ((g Hhi ω : ℕ) : ℝ)
      ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - Real.log 2 := by linarith
  have hsum := xt_log_add_le harm' hgb'
  exact le_trans hsum (by linarith)


/-! ## §W1b-i — the envelope at a generic count ceiling, and the four cap lines at a charge paid
by `A`

The rung-2 walk's last numeral caps on the `ρ`-side: the `_g12` walls' count ceiling `K ≤ 2 ^ 539`
becomes a CHARGE `K ≤ Kb` with `1 ≤ Kb`, the envelope's `2 ^ 592` becomes `2 ^ 53 * Kb`
(`2 ^ 592 = 2 ^ 53 * 2 ^ 539`, so `Kb = 2 ^ 539` IS the source), and the `_g14` cap lines' numeral
charge ceiling `439` becomes `16 * A` — paid by the design constant itself through
`Real.add_one_le_exp`, so `Lc` never enters those four.  `Kb` is a REAL VARIABLE throughout and is
never unfolded; no `2 ^ 539` and no `2 ^ 592` occurs in this section.  Nothing here bears on twin
primes. -/

/-- **⟦THE ENVELOPE AT A GENERIC COUNT CEILING⟧ (class B)** — `s16_audit_rho_ge_wide_h_g12`
(`StrideGrade12Walls.lean:92`) with its numeral count cap `K ≤ 2 ^ 539` replaced by the charge
`(hKb1 : 1 ≤ Kb) (hKb : K ≤ Kb)` and its envelope `2 ^ 592` by `2 ^ 53 * Kb`.

BODY: the source's, with `hkey` re-cut for the extra factor —
`1 / (2 ^ 53 * Kb) * (16 * K * 110525) ≤ 1 / 2 ^ 32`, which after `div_le_iff₀` is the LINEAR
`16 * 110525 * K ≤ 2 ^ 21 * Kb`, closed from `K ≤ Kb` by `16 * 110525 = 1768400 ≤ 2097152 = 2 ^ 21`
— the two `field_simp` splits carrying `Kb`, and the `≤ 1` arm from `1 ≤ Kb` and `1 ≤ h ^ 2`.
The source's margin is UNCHANGED at `2097152 / 1768400 = 1.1859036417…×`: `Kb` cancels exactly.
Nothing here bears on twin primes. -/
theorem s16_audit_rho_ge_wide_h_L {h : ℕ} (hh : 0 < h) {δ₀ K Kb : ℝ} (hδ : 0 < δ₀) (hK : 0 < K)
    (hδb : 1 / (2 ^ 32 * (h : ℝ) ^ 2) ≤ δ₀) (hKb1 : 1 ≤ Kb) (hKb : K ≤ Kb) :
    (1 : ℝ) / (2 ^ 53 * Kb * (h : ℝ) ^ 2) ≤ doorRhoOfDelta (s12DeltaSock δ₀ K) := by
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hhsq : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith
  have hh0 : (0 : ℝ) < (h : ℝ) := by linarith
  have hKb0 : (0 : ℝ) < Kb := by linarith
  have hinv : (0 : ℝ) < 1 / (h : ℝ) ^ 2 := by positivity
  rw [doorRhoOfDelta, le_min_iff]
  refine ⟨?_, ?_⟩
  · rw [div_le_one (by positivity)]
    nlinarith [hhsq, hKb1]
  rw [s12DeltaSock_sq hδ hK, div_div, le_div_iff₀ (by positivity)]
  -- ⟦THE SPLIT⟧ the `h²` is a common factor on both sides; peel it off so the comparison
  -- `1768400 * K ≤ 2 ^ 21 * Kb` is seen on its own, and is LINEAR in `K` and `Kb`.
  have hkey : 1 / ((2 : ℝ) ^ 53 * Kb) * (16 * K * 110525) ≤ 1 / (2 : ℝ) ^ 32 := by
    have hd : (0 : ℝ) < 2 ^ 53 * Kb := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    linarith
  have hsplit1 : 1 / ((2 : ℝ) ^ 53 * Kb * (h : ℝ) ^ 2) * (16 * K * 110525)
      = 1 / ((2 : ℝ) ^ 53 * Kb) * (16 * K * 110525) * (1 / (h : ℝ) ^ 2) := by
    field_simp
  have hsplit2 : 1 / (2 : ℝ) ^ 32 * (1 / (h : ℝ) ^ 2)
      = 1 / ((2 : ℝ) ^ 32 * (h : ℝ) ^ 2) := by
    field_simp
  rw [hsplit1]
  refine le_trans (mul_le_mul_of_nonneg_right hkey hinv.le) ?_
  rw [hsplit2]
  exact hδb

/-- **⟦THE `ρ`-CHARGE AT A GENERIC COUNT CEILING⟧ (class A)** —
`s16_audit_neglog_rho_le_wide_h_g12` (`StrideGrade12Walls.lean:124`) with the same charge, its
`411` replaced by `37 + Real.log Kb`.  BODY: the source's, with the envelope's log split ONCE MORE
(`2 ^ 53 * Kb * h ^ 2` is three factors, not two) and the supplier swapped for the sibling above.

THE NUMERAL: `53 * Real.log 2 = 36.7368005696…`, and the certified `Real.log 2 < 0.6931471808`
gives `53 * 0.6931471808 = 36.7368005824`; the CEILING `37` is the round TOWARD SLACK, leaving
`0.2631994176` nats.  At the source's pin `Kb = 2 ^ 539` this reads
`37 + 539 * Real.log 2 = 37 + 373.6063303218… = 410.6063303218… ≤ 411`, so the sibling is NOT
weaker than its source there.  Nothing here bears on twin primes. -/
theorem s16_audit_neglog_rho_le_wide_h_L {h : ℕ} (hh : 0 < h) {δ₀ K Kb : ℝ} (hδ : 0 < δ₀)
    (hK : 0 < K) (hδb : 1 / (2 ^ 32 * (h : ℝ) ^ 2) ≤ δ₀) (hKb1 : 1 ≤ Kb) (hKb : K ≤ Kb) :
    -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 37 + Real.log Kb + 2 * Real.log (h : ℝ) := by
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hKb0 : (0 : ℝ) < Kb := by linarith
  have hge := s16_audit_rho_ge_wide_h_L hh hδ hK hδb hKb1 hKb
  have hpos : (0 : ℝ) < 1 / (2 ^ 53 * Kb * (h : ℝ) ^ 2) := by positivity
  have h1 : Real.log ((1 : ℝ) / (2 ^ 53 * Kb * (h : ℝ) ^ 2))
      ≤ Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := Real.log_le_log hpos hge
  have h2 : Real.log ((1 : ℝ) / (2 ^ 53 * Kb * (h : ℝ) ^ 2))
      = -(53 * Real.log 2) - Real.log Kb - 2 * Real.log (h : ℝ) := by
    rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [h2] at h1
  linarith

/-- **⟦THE `ρ`-CHARGE AT THE RUNG-2 INTERFACE⟧ (class A)** — the `_L` sibling of
`s16_audit_neglog_rho_le_425_h_g12b` (`StrideGrade12bWalls.lean:151`): its cap `Real.log h ≤ 9` is
the charge `Real.log h ≤ Lc`, its count cap is `K ≤ Kb` with the rung-2 interface's rating
`Real.log Kb ≤ 197 + 20 * Lc`, and its numeral `429` is the affine `234 + 22 * Lc`.  BODY: the
source's `le_trans … (by linarith)`, verbatim.

THE NUMERALS, exact (no slack is spent here): the sibling above gives
`37 + Real.log Kb + 2 * Real.log h ≤ 37 + (197 + 20 * Lc) + 2 * Lc`, and `37 + 197 = 234`,
`20 + 2 = 22`.  Nothing here bears on twin primes. -/
theorem s16_audit_neglog_rho_le_h_L {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hhL : Real.log (h : ℝ) ≤ Lc)
    {δ₀ K Kb : ℝ} (hδ : 0 < δ₀) (hK : 0 < K) (hδb : 1 / (2 ^ 32 * (h : ℝ) ^ 2) ≤ δ₀)
    (hKb1 : 1 ≤ Kb) (hKb : K ≤ Kb) (hKbL : Real.log Kb ≤ 197 + 20 * Lc) :
    -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 234 + 22 * Lc := by
  exact le_trans (s16_audit_neglog_rho_le_wide_h_L hh hδ hK hδb hKb1 hKb) (by linarith)

end Salt.MR
