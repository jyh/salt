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

end Salt.MR
