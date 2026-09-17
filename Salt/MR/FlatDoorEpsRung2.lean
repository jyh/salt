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

end Salt.MR
