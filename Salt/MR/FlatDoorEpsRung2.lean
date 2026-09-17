/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FlatDoorEpsChain
import Salt.MR.FlatDoorEpsFamily
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

open private uniformCap_arc uniformCap_shuffle spine_False_core_xi_sq_uniform from
  Salt.MR.S16Uniform

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
`a = 283` is the smallest exponent this route gives.

⚠️ ERRATUM (2026-09-17, wave 6).  «The true size» names ONE number where there are TWO, and the
one it names is the size AFTER the route's `e^40 ≤ 3^40` step, not the witness's own.  Both,
derived — the `c^20` factor is exact in each, so only the constant's `log₂` is at issue, and
`32·e^40·(2^62·c^5)²·(500·c)^10 = 2^129·e^40·500^10·c^20`:

* THE WITNESS ITSELF: `129 + 40/log 2 + 10·log₂ 500 = 129 + 57.70780… + 89.65784… = 276.36564…`,
  that is `2^276.36564…·c^20`;
* AFTER `e^40 ≤ 3^40` (`40·log₂ 3 = 63.39850…`):
  `129 + 63.39850… + 89.65784… = 282.05634…`, that is `2^282.05634…·c^20`.

The figure in the sentence above is the SECOND, and it is the right one to test `a` against,
because `3^40` is the bound this route actually takes.  So `a = 283` stands and the ceiling is
unaffected; what was wrong was the NAME, which made a route-dependent figure read as the
witness's own. -/
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
(`3.2 · 26 = 83.2`), so this sibling is not weaker than its source at the source's own floor.

⚠️ ERRATUM (2026-09-17, wave 6): «ONE edit» is ONE LOGICAL edit — the tower floor becomes the
parameter — carried over THREE proof lines, measured by diffing the two bodies:

* the `have`'s own statement, `hll50 : (50 : ℝ) ≤ loglog R.Hhi` ↦ `hll : lam0 ≤ loglog R.Hhi`;
* the step that puts `A` where `R.A` stood, `have hA26 : (26 : ℝ) ≤ R.A := R.hA` ↦
  `rw [hRA] at hflat`;
* the read at the gate's discharge, `⟨hHhi4, hll50, hωgate⟩` ↦ `⟨hHhi4, hll, hωgate⟩`.

The clause about the READ is exact and unchanged: `hll50` is read at exactly one line
(`XThread.lean:178`, re-measured by the same diff).  Everything else in the 90-line body is the
source's byte for byte. -/
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
never unfolded; `2 ^ 539` and `2 ^ 592` occur in this section's DOC COMMENTS only, never in a
TERM — and it is a HYPOTHESIS carrying such a numeral, never a docstring, that poisons a later
tactic.  Nothing here bears on twin primes. -/

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


/-- **⟦THE WINDOW LINE AT A CHARGE PAID BY `A`⟧ (class A)** — `flat_half_line_g14`
(`StrideGradeReach.lean:183`) with `hc : c ≤ 439` replaced by `hc : c ≤ 16 * A`; the CONCLUSION is
the source's, byte for byte.  BODY: the source's, plus ONE new fact and its use in the close.

THE NEW FACT, shared by all four cap lines here: with `E := Real.exp (3.2 * A / 2)`,
`Real.add_one_le_exp (3.2 * A / 2)` gives `1.6 * A + 1 ≤ E`, hence `16 * A + 10 ≤ 10 * E` and so
`16 * A ≤ 10 * E`.  The charge is therefore paid by the DESIGN CONSTANT and `Lc` never enters.
THE MARGIN, derived: the register's slack here is
`(1 / 2 - 0.7 * 68719476736 / 96286710601) * E ^ 2 = (1 / 2 - 0.4995874655…) * E ^ 2
= 0.0004125344510… * E ^ 2`, and the charge costs `3 * c ≤ 3 * (16 * A) ≤ 30 * E`.  The ONE
product `hEE : 10 ^ 17 * E ≤ E ^ 2` — isolated as a `have` so the close stays LINEAR — makes
`30 * E ≤ 0.0004125344510… * E ^ 2` hold for every `E ≥ 72722`, against the register's
`E ≥ 10 ^ 17`: free by `1.3 * 10 ^ 12 ×`.  Nothing here bears on twin primes. -/
theorem flat_half_line_L {A c : ℝ} (hA : 26 ≤ A) (hc : c ≤ 16 * A) :
    (7 / 10 : ℝ) * ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ) + 3 * c ≤ Real.exp (3.2 * A) / 2 := by
  have hE17 := flat_exp_half_ge hA
  have hE0 : (0 : ℝ) < Real.exp (3.2 * A / 2) := Real.exp_pos _
  have hMle := flatDoorM_le A
  have hM0 : (0 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := Nat.cast_nonneg _
  have hY := flat_exp_sq A
  have hrow : ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ)
      = 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 := by
    rw [doorRowFloorL, AdoorL]; push_cast; ring
  have h1 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 - ((flatDoorM A : ℕ) : ℝ) := by
    linarith
  have h2 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 + ((flatDoorM A : ℕ) : ℝ) := by
    positivity
  have hsq : ((flatDoorM A : ℕ) : ℝ) ^ 2
      ≤ Real.exp (3.2 * A / 2) ^ 2 / 96286710601 := by
    nlinarith [mul_nonneg h1 h2]
  have hE2 : (10 : ℝ) ^ 34 ≤ Real.exp (3.2 * A / 2) ^ 2 := by nlinarith [hE17, hE0]
  -- ⟦THE CHARGE, PAID BY `A`⟧ `1.6·A + 1 ≤ E` ⇒ `16·A ≤ 10·E`; and the ONE product that
  -- lets a LINEAR close beat `30·E` with `0.000412…·E²`.
  have h16 : 16 * A ≤ 10 * Real.exp (3.2 * A / 2) := by
    have hx := Real.add_one_le_exp (3.2 * A / 2)
    linarith
  have hEE : (10 : ℝ) ^ 17 * Real.exp (3.2 * A / 2) ≤ Real.exp (3.2 * A / 2) ^ 2 := by
    nlinarith [hE17, hE0]
  rw [hrow, ← hY]
  linarith [hsq, hE2, hc, h16, hEE]

/-- **⟦THE `anchor` LINE AT A CHARGE PAID BY `A`⟧ (class A)** — `flat_anchor_line_wide_g14`
(`StrideGradeReach.lean:207`) with `hc : c ≤ 439` replaced by `hc : c ≤ 16 * A`; the conclusion is
the source's, byte for byte.  BODY: the source's, plus the shared new fact `16 * A ≤ 10 * E`.

THE MARGIN, derived: `flatDoorM_ge` gives
`39 * 10 ^ 8 * M ≥ 39 * 10 ^ 8 * (E / 310301 - 1) = 12568.4416099… * E - 39 * 10 ^ 8`, against a
left side `28 * E + c + 33 ≤ 38 * E + 33`; the comparison holds for every `E ≥ 311243`, against
`E ≥ 10 ^ 17`: free by `3.2 * 10 ^ 11 ×`.  Nothing here bears on twin primes. -/
theorem flat_anchor_line_wide_L {A c : ℝ} (hA : 26 ≤ A) (hc : c ≤ 16 * A) :
    14 * (2 * Real.exp (3.2 * A / 2)) + c + 33
      ≤ 39 * 10 ^ 8 * ((flatDoorM A : ℕ) : ℝ) := by
  have hE17 := flat_exp_half_ge hA
  have hMge := flatDoorM_ge A
  have h16 : 16 * A ≤ 10 * Real.exp (3.2 * A / 2) := by
    have hx := Real.add_one_le_exp (3.2 * A / 2)
    linarith
  linarith

/-- **⟦THE `𝒯`-LEG BUDGET AT A CHARGE PAID BY `A`⟧ (class A)** — `flat_gP1_line_g14`
(`StrideGradeReach.lean:216`) with `hc : -439 ≤ c` replaced by `hc : -(16 * A) ≤ c` (the charge
enters this one with the OPPOSITE sign); the conclusion is the source's, byte for byte.  BODY: the
source's, plus the shared new fact, used as `-c ≤ 16 * A ≤ 10 * E`.

THE MARGIN, derived: the body's `hAdlog` gives `AdoorL M * Real.log 2 ≥ 153000 * E`, against a
left side `29 + Real.log Ct + 14 * Λ ≤ 29 + 23 * 0.6931471808 + 28 * E = 44.9423851584 + 28 * E`
and a charge of `10 * E`; `(153000 - 28 - 10) * E ≥ 44.9423851584` holds for every `E ≥ 0.0003`,
against `E ≥ 10 ^ 17`: free by `3.3 * 10 ^ 20 ×`.  Nothing here bears on twin primes. -/
theorem flat_gP1_line_L {A c Ct Λ : ℝ} (hA : 26 ≤ A) (hc : -(16 * A) ≤ c) (hCt : 0 < Ct)
    (hCtb : Ct ≤ 2 ^ 23) (hΛ : Λ ≤ 2 * Real.exp (3.2 * A / 2)) :
    29 + Real.log Ct + 14 * Λ ≤ ((AdoorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2 + c := by
  have hE17 := flat_exp_half_ge hA
  have hMge := flatDoorM_ge A
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hAdlo : 221460 * Real.exp (3.2 * A / 2) - 68719476737
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) := by linarith
  have hpos : (0 : ℝ) ≤ 221460 * Real.exp (3.2 * A / 2) - 68719476737 := by linarith
  have h1 : (221460 * Real.exp (3.2 * A / 2) - 68719476737) * Real.log 2
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hAdlo (by linarith)
  have hAdlog : 153000 * Real.exp (3.2 * A / 2)
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 := by
    nlinarith [hpos, hlog2lo, hE17]
  have hCtl : Real.log Ct ≤ 23 * Real.log 2 := by
    have h := Real.log_le_log hCt hCtb
    rwa [Real.log_pow] at h
  have h16 : 16 * A ≤ 10 * Real.exp (3.2 * A / 2) := by
    have hx := Real.add_one_le_exp (3.2 * A / 2)
    linarith
  rw [AdoorL_cast]
  linarith

/-- **⟦THE `level1` BUDGET AT A CHARGE PAID BY `A`⟧ (class A)** — `flat_lvl_line_g14`
(`StrideGradeReach.lean:240`) with `hc : c ≤ 439` replaced by `hc : c ≤ 16 * A`; the conclusion is
the source's, byte for byte.  BODY: the source's, plus the shared new fact `16 * A ≤ 10 * E`.

THE MARGIN, derived: the body's `hbud` gives `(1 / 12) * AdoorL M * Real.log 2 ≥ 12750 * E`,
against a left side bounded by `26 + 28 * E + (2 / 3) * (E - 1) + 10 * E` (the last term is the
charge).  The surviving coefficient on `E` is `12750 - 28 - 2 / 3 - 10 = 12711.33…` against the
constant `26 - 2 / 3 = 25.33…`, so the comparison holds for every `E ≥ 0.002`, against
`E ≥ 10 ^ 17`: free by `5 * 10 ^ 19 ×`.  Nothing here bears on twin primes. -/
theorem flat_lvl_line_L {A c Λ : ℝ} (hA : 26 ≤ A) (hc : c ≤ 16 * A)
    (hΛ : Λ ≤ 2 * Real.exp (3.2 * A / 2)) :
    26 + 14 * Λ + (1 / 3) * Real.log (Real.log ((calQK (AdoorL (flatDoorM A))
        (3072 * flatDoorM A) (flatDoorM A) 1 : ℕ) : ℝ)) + c
      ≤ (1 / 12) * ((AdoorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2 := by
  have hE17 := flat_exp_half_ge hA
  have hE0 : (0 : ℝ) < Real.exp (3.2 * A / 2) := Real.exp_pos _
  have hMle := flatDoorM_le A
  have hMge := flatDoorM_ge A
  have hM0 : (0 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hrow : ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ)
      = 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 := by
    rw [doorRowFloorL, AdoorL]; push_cast; ring
  have hAdlo : 221460 * Real.exp (3.2 * A / 2) - 68719476737
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) := by linarith
  have hpos : (0 : ℝ) ≤ 221460 * Real.exp (3.2 * A / 2) - 68719476737 := by linarith
  have h1 : (221460 * Real.exp (3.2 * A / 2) - 68719476737) * Real.log 2
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hAdlo (by linarith)
  have hAdlog : 153000 * Real.exp (3.2 * A / 2)
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 := by
    nlinarith [hpos, hlog2lo, hE17]
  rw [AdoorL_cast, s15_log_calQK_L_one, hrow]
  have hQpos : (0 : ℝ) < 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 * Real.log 2 := by
    have hM1N : 1 ≤ flatDoorM A := flatDoorM_one_le hA
    have hM1 : (1 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := by exact_mod_cast hM1N
    have : (0 : ℝ) < Real.log 2 := by linarith
    positivity
  have hd1 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 - ((flatDoorM A : ℕ) : ℝ) := by
    linarith
  have hd2 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 + ((flatDoorM A : ℕ) : ℝ) := by
    positivity
  have hsq : ((flatDoorM A : ℕ) : ℝ) ^ 2
      ≤ Real.exp (3.2 * A / 2) ^ 2 / 96286710601 := by
    nlinarith [mul_nonneg hd1 hd2]
  have hQle : 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 * Real.log 2
      ≤ Real.exp (3.2 * A / 2) ^ 2 := by
    nlinarith [hsq, hlog2hi, sq_nonneg (Real.exp (3.2 * A / 2)), hM0,
      sq_nonneg ((flatDoorM A : ℕ) : ℝ)]
  have hlogQ : Real.log (68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 * Real.log 2)
      ≤ 2 * Real.log (Real.exp (3.2 * A / 2)) := by
    have h := Real.log_le_log hQpos hQle
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlogE : Real.log (Real.exp (3.2 * A / 2)) ≤ Real.exp (3.2 * A / 2) - 1 :=
    Real.log_le_sub_one_of_pos hE0
  have hbud : 12750 * Real.exp (3.2 * A / 2)
      ≤ 1 / 12 * (68719476736 * ((flatDoorM A : ℕ) : ℝ)) * Real.log 2 := by
    linarith [hAdlog]
  have h16 : 16 * A ≤ 10 * Real.exp (3.2 * A / 2) := by
    have hx := Real.add_one_le_exp (3.2 * A / 2)
    linarith
  linarith [hΛ, hc, hlogQ, hlogE, hbud, hE17, h16]

/-! ## §W1b-ii — the witness at a generic charge

The two large `S15Sel''_L` witness bodies and the rows that ride them, re-cut at the rung-2
interface: the count cap `c ≤ 8103` becomes the charge `(hcL : Real.log c ≤ Lc)` with the ninth
arm `(hAL : 10 + 2 * Lc ≤ A)`, and each body's ONE cap site is repaid by the design constant.
The FROZEN DUMMY INSTANCE's binders (`hδb`, `hKb`, `hCtb` at `1 / 2 ^ 10`, `2 ^ 20`, `2 ^ 20`)
are the sources' own and are NOT caps on this wave's parameters: they are satisfied at the single
instance `Cg := 0`, `δ₀ := 1 / 2 ^ 10`, `Ct := 1`, `K := 1` that the carriers apply them at, and
the witnesses are applied at that instance only.  Nothing here bears on twin primes. -/


set_option maxHeartbeats 1600000 in
-- as the source: eleven register lines at a SYMBOLIC design point, `blk` a `y⁴`-vs-`e^y` comparison
/-- **⟦THE FLAT WITNESS AT A GENERIC CHARGE⟧ (class B)** — the `_L` sibling of
`s15_sel''_L_witness_flat_b9` (`S15SelLinear.lean:727`): its count cap `c ≤ 8103` is replaced by
the charge `(hcL : Real.log c ≤ Lc)` with the ninth arm on the design constant
`(hAL : 10 + 2 * Lc ≤ A)`.  Every other binder — including the FROZEN DUMMY INSTANCE's `hδb`,
`hKb`, `hCtb`, which are not caps on this wave's parameters — and the conclusion are the source's,
byte for byte.

THE ONE CAP SITE, measured by a `clear`-probe on the source's own body (with a mutation control
that clears the fact BEFORE its site and fails): the cap is read exactly once, through
`hcRb` (`:848`) into `hcsqb : c ^ 2 ≤ 65658609` (`:876`), and spent at `:885` for
`0 ≤ E ^ 2 - 1006632960 * c ^ 2` (`1006632960 = 15 * 67108864 = 15 * 2 ^ 26`).  BODY: the
source's, with that pair replaced by the charge route and the `show` closed by `linarith`.

THE NEW FACT AND ITS NUMERAL, derived: `Real.log 1006632960 = 20.7298…`, so the CEILING `21` is
the round toward slack (`e ^ 21 = 1.3188…e9` against `1.00663…e9`, a factor `1.3101…`); with
`c ^ 2 ≤ e ^ (2 * Lc)` this gives `1006632960 * c ^ 2 ≤ e ^ (21 + 2 * Lc)`, and `hAL` pays the
exponent — `3.2 * A ≥ 32 + 6.4 * Lc`, and `21 + 2 * Lc ≤ 32 + 6.4 * Lc` for every `Lc ≥ 0`, which
`hc1` supplies (`0 = log 1 ≤ log c ≤ Lc`), with `11 + 4.4 * Lc` nats to spare.  At the source's
pin `Lc = 9` the route reads `21 + 18 = 39 ≤ 3.2 * A`, i.e. `A ≥ 12.1875`, free against `hA`.
Nothing here bears on twin primes. -/
theorem s15_sel''_L_witness_flat_L {A : ℝ} (hA : 26 ≤ A) {Cg δ₀ Ct K Lc : ℝ} {x₀ Mfl c : ℕ}
    {R : ChowlaRegime}
    (hc1 : 1 ≤ c) (hcL : Real.log (c : ℝ) ≤ Lc) (hAL : 10 + 2 * Lc ≤ A)
    (hδ : 0 < δ₀) (hδb : 1 / 2 ^ 10 ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 20)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 20)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    -- amended per REF-FLAT-SAT: the `Λ` slot carries the `Nat.ceil` overshoot factor `2`
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R (flatDoorM A) := by
  set E : ℝ := Real.exp (3.2 * A / 2) with hEdef
  set Mr : ℝ := ((flatDoorM A : ℕ) : ℝ) with hMrdef
  have hE17 : (10 : ℝ) ^ 17 ≤ E := flat_exp_half_ge hA
  have hE0 : (0 : ℝ) < E := by positivity
  have hY : E ^ 2 = Real.exp (3.2 * A) := flat_exp_sq A
  have hMle : Mr ≤ E / 310301 := flatDoorM_le A
  have hMge : E / 310301 - 1 ≤ Mr := flatDoorM_ge A
  have hM1N : 1 ≤ flatDoorM A := flatDoorM_one_le hA
  have hM1 : (1 : ℝ) ≤ Mr := by rw [hMrdef]; exact_mod_cast hM1N
  have hM0 : (0 : ℝ) ≤ Mr := by linarith
  have hE1 : (1 : ℝ) ≤ E := by linarith [hE17]
  have hE6 : E ≤ E ^ (6 : ℕ) := le_self_pow₀ hE1 (by norm_num)
  have hE61 : (1 : ℝ) ≤ E ^ (6 : ℕ) := one_le_pow₀ hE1
  have hE2 : (10 : ℝ) ^ 34 ≤ E ^ 2 := by nlinarith [hE17, hE0]
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hρlog : -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 36 :=
    s15w_neglog_rho_le hδ hK hδb hKb
  have hinv : Real.log (1 / doorRhoOfDelta (s12DeltaSock δ₀ K))
      = -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := by rw [one_div, Real.log_inv]
  have hAd : ((AdoorL (flatDoorM A) : ℕ) : ℝ) = 68719476736 * Mr := AdoorL_cast _
  have hrow : ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ) = 68719476736 * Mr ^ 2 := by
    rw [doorRowFloorL, AdoorL]; push_cast; ring
  have hAdlo : 221460 * E - 68719476737 ≤ 68719476736 * Mr := by linarith [hMge]
  have hAdlog : 153000 * E ≤ 68719476736 * Mr * Real.log 2 := by
    have hpos : (0 : ℝ) ≤ 221460 * E - 68719476737 := by linarith [hE17]
    have h1 : (221460 * E - 68719476737) * Real.log 2 ≤ 68719476736 * Mr * Real.log 2 :=
      mul_le_mul_of_nonneg_right hAdlo (by linarith)
    nlinarith [hpos, hlog2lo, hE17]
  refine
    { hM := hM1N
      mfloor := hMfl
      bfloor := hbfl
      gRows := ?_
      x0M := ?_
      blk := ?_
      half := ?_
      rho := ?_
      anchor := ?_
      gP1 := ?_
      lvl := ?_ }
  · rw [hAd]
    linarith [hhi, hAdlo, hE17]
  · have hMhalf : E / 620602 ≤ Mr := by linarith [hMge, hE17]
    have hsq : (E / 620602) ^ 2 ≤ Mr ^ 2 := by
      have h1 : (0 : ℝ) ≤ Mr - E / 620602 := by linarith
      have h2 : (0 : ℝ) ≤ Mr + E / 620602 := by positivity
      nlinarith [mul_nonneg h1 h2]
    have hkey : Real.exp (3.2 * A) / 10
        ≤ ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2 := by
      rw [hrow, ← hY]
      have hE2pos : (0 : ℝ) ≤ E ^ 2 := sq_nonneg E
      have hl2 : (0 : ℝ) ≤ Real.log 2 := by linarith
      have hd : (0 : ℝ) ≤ Mr ^ 2 - (E / 620602) ^ 2 := by linarith [hsq]
      have hstep : (68719476736 : ℝ) * (E / 620602) ^ 2 * Real.log 2
          ≤ 68719476736 * Mr ^ 2 * Real.log 2 := by nlinarith [mul_nonneg hl2 hd]
      have hfin : E ^ 2 / 10 ≤ 68719476736 * (E / 620602) ^ 2 * Real.log 2 := by
        nlinarith [mul_nonneg hE2pos (show (0 : ℝ) ≤ Real.log 2 - 0.6931471803 by linarith)]
      linarith [hstep, hfin]
    have hpowid : ((2 : ℝ) ^ (doorRowFloorL (flatDoorM A) : ℕ))
        = Real.exp (((doorRowFloorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2) := by
      rw [← Real.log_pow]
      exact (Real.exp_log (by positivity)).symm
    have hfin : (x₀ : ℝ) ≤ (2 : ℝ) ^ (doorRowFloorL (flatDoorM A) : ℕ) := by
      rw [hpowid]
      exact le_trans hx0win (Real.exp_le_exp.mpr hkey)
    exact_mod_cast hfin
  · have hbeN : s13BlockExp_L (flatDoorM A) ≤ 2 ^ 104 * (flatDoorM A) ^ 6 :=
      s13BlockExp_L_le hM1N
    have hbeR : ((s13BlockExp_L (flatDoorM A) : ℕ) : ℝ) ≤ 2 ^ 104 * Mr ^ 6 := by
      have h : ((s13BlockExp_L (flatDoorM A) : ℕ) : ℝ)
          ≤ ((2 ^ 104 * (flatDoorM A) ^ 6 : ℕ) : ℝ) := by exact_mod_cast hbeN
      push_cast at h
      linarith
    have h218 : ((2 : ℝ) ^ (18 : ℕ)) = 262144 := by norm_num
    have hM18 : Mr * 2 ^ (18 : ℕ) ≤ E := by
      have h : Mr * 310301 ≤ E := by
        have hd := hMle
        rw [le_div_iff₀ (by norm_num)] at hd
        linarith
      rw [h218]
      linarith [h, hM0]
    have hM18' : (Mr * 2 ^ (18 : ℕ)) ^ (6 : ℕ) ≤ E ^ (6 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hM18 6
    have hid6 : (Mr * 2 ^ (18 : ℕ)) ^ (6 : ℕ) = Mr ^ (6 : ℕ) * 2 ^ (108 : ℕ) := by
      rw [mul_pow, ← pow_mul]
    have hM6 : Mr ^ (6 : ℕ) * 2 ^ (108 : ℕ) ≤ E ^ (6 : ℕ) := by rw [← hid6]; exact hM18'
    have h108 : ((2 : ℝ) ^ (108 : ℕ)) = 16 * (2 : ℝ) ^ (104 : ℕ) := by
      rw [show (108 : ℕ) = 4 + 104 by norm_num, pow_add]; norm_num
    have hlhs : ((s13BlockExp_L (flatDoorM A) : ℕ) : ℝ) + 1
        + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 55 * E ^ (6 : ℕ) := by
      have h1 : (2 : ℝ) ^ (104 : ℕ) * Mr ^ (6 : ℕ) ≤ E ^ (6 : ℕ) / 16 := by
        rw [h108] at hM6
        linarith [hM6]
      linarith [hbeR, hhi, hE6, h1, hE61, hE1]
    have hHlopos : (0 : ℝ) < ((R.Hlo : ℕ) : ℝ) := by
      have h := R.hHlo_floor
      have : (0 : ℕ) < R.Hlo := by omega
      exact_mod_cast this
    have hHloge : Real.exp (E ^ 2) ≤ ((R.Hlo : ℕ) : ℝ) := by
      have h := Real.exp_le_exp.mpr (hY ▸ hlo)
      rwa [Real.exp_log hHlopos] at h
    have hHhige : Real.exp (E ^ 2) ≤ ((R.Hhi : ℕ) : ℝ) := by
      have : ((R.Hlo : ℕ) : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast R.hHlohi
      linarith
    have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
    have hcR0 : (0 : ℝ) < (c : ℝ) := by linarith
    -- ⟦THE ONE CAP SITE⟧ the source's `hcRb`/`hcsqb` pair, replaced by the charge route
    -- `1006632960 * c ^ 2 ≤ e ^ 21 * e ^ (2 * Lc) = e ^ (21 + 2 * Lc) ≤ e ^ (3.2 * A) = E ^ 2`.
    have hcE : 1006632960 * (c : ℝ) ^ 2 ≤ E ^ (2 : ℕ) := by
      have hL0 : (0 : ℝ) ≤ Lc := le_trans (Real.log_nonneg hcR1) hcL
      have hE21 : (1006632960 : ℝ) ≤ Real.exp 21 := by
        have he : Real.exp 21 = (Real.exp 1) ^ (21 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
        have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
        rw [he]
        calc (1006632960 : ℝ) ≤ (2.7 : ℝ) ^ (21 : ℕ) := by norm_num
          _ ≤ (Real.exp 1) ^ (21 : ℕ) := pow_le_pow_left₀ (by norm_num) h1.le 21
      have hcexp : (c : ℝ) ≤ Real.exp Lc := by
        calc (c : ℝ) = Real.exp (Real.log (c : ℝ)) := (Real.exp_log (by linarith)).symm
          _ ≤ Real.exp Lc := Real.exp_le_exp.mpr hcL
      have hcsqE : (c : ℝ) ^ 2 ≤ Real.exp (2 * Lc) := by
        have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (c : ℝ)) hcexp 2
        have hid : (Real.exp Lc) ^ (2 : ℕ) = Real.exp (2 * Lc) := by
          rw [← Real.exp_nat_mul]; norm_num
        rw [hid] at hp
        exact hp
      have hstep : 1006632960 * (c : ℝ) ^ 2 ≤ Real.exp 21 * Real.exp (2 * Lc) := by
        calc 1006632960 * (c : ℝ) ^ 2 ≤ Real.exp 21 * (c : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right hE21 (by positivity)
          _ ≤ Real.exp 21 * Real.exp (2 * Lc) :=
              mul_le_mul_of_nonneg_left hcsqE (Real.exp_pos _).le
      have hmono : Real.exp (21 + 2 * Lc) ≤ Real.exp (3.2 * A) := Real.exp_le_exp.mpr (by linarith)
      rw [hY]
      calc 1006632960 * (c : ℝ) ^ 2 ≤ Real.exp 21 * Real.exp (2 * Lc) := hstep
        _ = Real.exp (21 + 2 * Lc) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (3.2 * A) := hmono
    have hepsR : (1 : ℝ) / (512 * (c : ℝ)) ≤ (R.eps : ℝ) := by
      have hcast : (((1 : ℚ) / (2 ^ 9 * (c : ℚ)) : ℚ) : ℝ) ≤ ((R.eps : ℚ) : ℝ) :=
        (Rat.cast_le (K := ℝ)).mpr heps
      have heq : (((1 : ℚ) / (2 ^ 9 * (c : ℚ)) : ℚ) : ℝ) = 1 / (512 * (c : ℝ)) := by
        push_cast; norm_num
      rw [heq] at hcast
      exact hcast
    have hepsR0 : (0 : ℝ) ≤ 1 / (512 * (c : ℝ)) := by positivity
    have hepssq : (1 : ℝ) / (262144 * (c : ℝ) ^ 2) ≤ (R.eps : ℝ) ^ 2 := by
      have hmul := mul_le_mul hepsR hepsR hepsR0 (le_trans hepsR0 hepsR)
      calc (1 : ℝ) / (262144 * (c : ℝ) ^ 2)
          = (1 / (512 * (c : ℝ))) * (1 / (512 * (c : ℝ))) := by field_simp; ring
        _ ≤ (R.eps : ℝ) * (R.eps : ℝ) := hmul
        _ = (R.eps : ℝ) ^ 2 := by ring
    have hfloorR : (R.eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) - 1
        ≤ ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
      have h := Nat.lt_floor_add_one (R.eps ^ 2 * (R.Hhi : ℚ))
      have h' : ((R.eps ^ 2 * (R.Hhi : ℚ) : ℚ) : ℝ)
          < ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast h
      push_cast at h'
      linarith
    have hprod : (1 : ℝ) / (262144 * (c : ℝ) ^ 2) * Real.exp (E ^ 2)
        ≤ (R.eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) :=
      mul_le_mul hepssq hHhige (Real.exp_pos _).le (by positivity)
    have hquart : (E ^ 2) ^ 4 / 256 ≤ Real.exp (E ^ 2) := flat_exp_ge_quartic (by positivity)
    have hbig : 15 * E ^ (6 : ℕ) ≤ 1 / (262144 * (c : ℝ) ^ 2) * Real.exp (E ^ 2) := by
      have hcsq : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by nlinarith [hcR1]
      have h2 : (1 : ℝ) / (262144 * (c : ℝ) ^ 2) * ((E ^ 2) ^ 4 / 256)
          = E ^ (6 : ℕ) * E ^ (2 : ℕ) / (67108864 * (c : ℝ) ^ 2) := by field_simp; ring
      have h3 : (15 : ℝ) * E ^ (6 : ℕ)
          ≤ E ^ (6 : ℕ) * E ^ (2 : ℕ) / (67108864 * (c : ℝ) ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        have hEsq : (1209000000000000000 : ℝ) ≤ E ^ (2 : ℕ) := by nlinarith [hE17, hE0]
        have hE60 : (0 : ℝ) ≤ E ^ (6 : ℕ) := by positivity
        nlinarith [mul_nonneg hE60
          (show (0 : ℝ) ≤ E ^ (2 : ℕ) - 1006632960 * (c : ℝ) ^ 2 by linarith [hcE])]
      have h1 : (1 : ℝ) / (262144 * (c : ℝ) ^ 2) * ((E ^ 2) ^ 4 / 256)
          ≤ 1 / (262144 * (c : ℝ) ^ 2) * Real.exp (E ^ 2) := by
        have hpos : (0 : ℝ) ≤ 1 / (262144 * (c : ℝ) ^ 2) := by positivity
        exact mul_le_mul_of_nonneg_left hquart hpos
      linarith [h1, h2, h3]
    linarith [hlhs, hfloorR, hprod, hbig, hE61]
  · rw [hinv, hrow]
    have hsq : Mr ^ 2 ≤ E ^ 2 / 96286710601 := by
      have h1 : (0 : ℝ) ≤ E / 310301 - Mr := by linarith
      have h2 : (0 : ℝ) ≤ E / 310301 + Mr := by positivity
      nlinarith [mul_nonneg h1 h2]
    have hlogH : E ^ 2 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by rw [hY]; exact hlo
    linarith [hsq, hlogH, hρlog, hE2]
  · linarith [hρlog]
  · rw [hinv]
    have hlo39 : (12568 : ℝ) * E - 3900000001 ≤ 39 * 10 ^ 8 * Mr := by
      linarith [hMge, hE0]
    linarith [hhi, hρlog, hlo39, hE17]
  · rw [hAd]
    have hCtl : Real.log Ct ≤ 20 * Real.log 2 := by
      have h := Real.log_le_log hCt hCtb
      rwa [Real.log_pow] at h
    have hρ' : -(36 : ℝ) ≤ Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := by linarith [hρlog]
    linarith [hAdlog, hhi, hCtl, hρ', hlog2hi, hE17]
  · rw [hAd, s15_log_calQK_L_one, hrow]
    have hQpos : (0 : ℝ) < 68719476736 * Mr ^ 2 * Real.log 2 := by
      have : (0 : ℝ) < Real.log 2 := by linarith
      positivity
    have hsq : Mr ^ 2 ≤ E ^ 2 / 96286710601 := by
      have h1 : (0 : ℝ) ≤ E / 310301 - Mr := by linarith
      have h2 : (0 : ℝ) ≤ E / 310301 + Mr := by positivity
      nlinarith [mul_nonneg h1 h2]
    have hQle : 68719476736 * Mr ^ 2 * Real.log 2 ≤ E ^ 2 := by
      nlinarith [hsq, hlog2hi, sq_nonneg E, hM0, sq_nonneg Mr]
    have hlogQ : Real.log (68719476736 * Mr ^ 2 * Real.log 2) ≤ 2 * Real.log E := by
      have h := Real.log_le_log hQpos hQle
      rw [Real.log_pow] at h
      push_cast at h
      linarith
    have hlogE : Real.log E ≤ E - 1 := Real.log_le_sub_one_of_pos hE0
    have hbud : 12750 * E ≤ 1 / 12 * (68719476736 * Mr) * Real.log 2 := by
      linarith [hAdlog]
    linarith [hhi, hρlog, hlogQ, hlogE, hbud, hE17]


set_option maxHeartbeats 1600000 in
-- as the source: the levered `blk` line carries `4^K` against `e^{e^{3.2A}}` symbolically
/-- **⟦THE LEVERED WITNESS AT A GENERIC CHARGE⟧ (class B)** — the `_L` sibling of
`s15_sel''_L_gk_witness_flat_b9` (`S15SelLinear.lean:936`): the same interface edit as the
sibling above (`c ≤ 8103 ↦ (hcL : Real.log c ≤ Lc)` with `(hAL : 10 + 2 * Lc ≤ A)`), its first
step calling that sibling.  Conclusion and every other binder are the source's, byte for byte.

THE ONE CAP SITE, measured by the same `clear`-probe: apart from the supplier call (`:953`,
which is the interface edit itself), the cap is read exactly once — `hcRb` (`:1041`) into
`hcsqb : c ^ 2 ≤ 65658609` (`:1042`), spent at `:1084` inside `hstep`.  BODY: the source's, with
that pair replaced by the charge route, `hE2big`/`hexpmono` re-cut, `hsplit40`/`hexp40` retired
(the `e ^ 40 ≥ 10 ^ 17` slot is what the charge now occupies), and `hstep` closed by a `calc`.

THE NEW FACTS AND THEIR NUMERALS, derived.  (a) `2 * 262144 = 524288 = 2 ^ 19` and
`Real.log 524288 = 13.1697…`, so the CEILING `14` is the round toward slack
(`e ^ 14 = 1202604.28…` against `524288`, a factor `2.2937…`); with `c ^ 2 ≤ e ^ (2 * Lc)` this
gives `524288 * c ^ 2 ≤ e ^ (14 + 2 * Lc)`.  (b) the source's `766 * E + 40 ≤ E ^ 2` becomes
`14 + 2 * Lc + 766 * E ≤ E ^ 2`, paid by `2 * Lc ≤ A - 10` (`hAL`) and `A ≤ E`
(`Real.add_one_le_exp (3.2 * A / 2)` gives `1.6 * A + 1 ≤ E`, and `A ≥ 26`), leaving
`767 * E + 4 ≤ E ^ 2` against `E ≥ 10 ^ 17`: free by `1.3 * 10 ^ 14 ×`.  At the source's pin
`Lc = 9` the charge reads `14 + 18 = 32`, inside the source's own `40` by `8` nats.
Nothing here bears on twin primes. -/
theorem s15_sel''_L_gk_witness_flat_L {A : ℝ} (hA : 26 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {Cg δ₀ Ct K Lc : ℝ} {x₀ Mfl c : ℕ}
    (hc1 : 1 ≤ c) (hcL : Real.log (c : ℝ) ≤ Lc) (hAL : 10 + 2 * Lc ≤ A)
    {R : ChowlaRegime}
    (hδ : 0 < δ₀) (hδb : 1 / 2 ^ 10 ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 20)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 20)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    -- amended per REF-FLAT-SAT: the `Λ` slot carries the `Nat.ceil` overshoot factor `2`
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L_gk Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R
      (flatDoorM A) := by
  refine s15_sel''_L_gk_of_L Klev
    (s15_sel''_L_witness_flat_L hA hc1 hcL hAL hδ hδb hK hKb hCt hCtb hbfl hMfl hx0win heps hlo hhi)
    ?_
  set E : ℝ := Real.exp (3.2 * A / 2) with hEdef
  set Mr : ℝ := ((flatDoorM A : ℕ) : ℝ) with hMrdef
  have hE17 : (10 : ℝ) ^ 17 ≤ E := flat_exp_half_ge hA
  have hE0 : (0 : ℝ) < E := by positivity
  have hE1 : (1 : ℝ) ≤ E := by linarith [hE17]
  have hY : E ^ 2 = Real.exp (3.2 * A) := flat_exp_sq A
  have hMle : Mr ≤ E / 310301 := flatDoorM_le A
  have hM1N : 1 ≤ flatDoorM A := flatDoorM_one_le hA
  have hM0 : (0 : ℝ) ≤ Mr := Nat.cast_nonneg _
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hbeN : s13BlockExp_L_gk Klev (flatDoorM A) ≤ 2 ^ 104 * 4 ^ Klev * (flatDoorM A) ^ 6 :=
    s13BlockExp_L_gk_le hM1N
  have hbeR : ((s13BlockExp_L_gk Klev (flatDoorM A) : ℕ) : ℝ)
      ≤ 2 ^ (104 : ℕ) * 4 ^ Klev * Mr ^ (6 : ℕ) := by
    have h : ((s13BlockExp_L_gk Klev (flatDoorM A) : ℕ) : ℝ)
        ≤ ((2 ^ 104 * 4 ^ Klev * (flatDoorM A) ^ 6 : ℕ) : ℝ) := by exact_mod_cast hbeN
    push_cast at h
    linarith
  have h218 : ((2 : ℝ) ^ (18 : ℕ)) = 262144 := by norm_num
  have hM18 : Mr * 2 ^ (18 : ℕ) ≤ E := by
    have h : Mr * 310301 ≤ E := by
      have hd := hMle
      rw [le_div_iff₀ (by norm_num)] at hd
      linarith
    rw [h218]; linarith [h, hM0]
  have hid6 : (Mr * 2 ^ (18 : ℕ)) ^ (6 : ℕ) = Mr ^ (6 : ℕ) * 2 ^ (108 : ℕ) := by
    rw [mul_pow, ← pow_mul]
  have hM6 : Mr ^ (6 : ℕ) * 2 ^ (108 : ℕ) ≤ E ^ (6 : ℕ) := by
    rw [← hid6]; exact pow_le_pow_left₀ (by positivity) hM18 6
  have h108 : ((2 : ℝ) ^ (108 : ℕ)) = 16 * (2 : ℝ) ^ (104 : ℕ) := by
    rw [show (108 : ℕ) = 4 + 104 by norm_num, pow_add]; norm_num
  have hpow104 : (2 : ℝ) ^ (104 : ℕ) * Mr ^ (6 : ℕ) ≤ E ^ (6 : ℕ) / 16 := by
    rw [h108] at hM6; linarith [hM6]
  have hE6exp : E ^ (6 : ℕ) ≤ Real.exp (6 * E) := by
    have h : Real.log (E ^ (6 : ℕ)) ≤ 6 * E := by
      rw [Real.log_pow]
      push_cast
      linarith [Real.log_le_sub_one_of_pos hE0]
    have h2 := Real.exp_le_exp.mpr h
    rwa [Real.exp_log (by positivity)] at h2
  have hKR : (Klev : ℝ) ≤ 170000000 * Mr := by rw [hMrdef]; exact_mod_cast hKle
  have hMr310 : Mr * 310301 ≤ E := by
    have hd := hMle
    rw [le_div_iff₀ (by norm_num)] at hd
    linarith
  have hK0 : (0 : ℝ) ≤ (Klev : ℝ) := Nat.cast_nonneg _
  have h4K : (4 : ℝ) ^ Klev ≤ Real.exp (760 * E) := by
    have hlog4 : Real.log ((4 : ℝ) ^ Klev) = (Klev : ℝ) * Real.log 4 := by
      rw [Real.log_pow]
    have hlog4v : Real.log 4 ≤ 1.3862943616 := by
      have h : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
      rw [h]; linarith [hlog2hi]
    have hKE : (Klev : ℝ) ≤ 548 * E := by linarith [hKR, hMr310, hM0]
    have hbound : Real.log ((4 : ℝ) ^ Klev) ≤ 760 * E := by
      rw [hlog4]
      have h1 : (Klev : ℝ) * Real.log 4 ≤ (Klev : ℝ) * 1.3862943616 :=
        mul_le_mul_of_nonneg_left hlog4v hK0
      nlinarith [h1, hKE]
    have h2 := Real.exp_le_exp.mpr hbound
    rwa [Real.exp_log (by positivity)] at h2
  have hprodL : (2 : ℝ) ^ (104 : ℕ) * 4 ^ Klev * Mr ^ (6 : ℕ)
      ≤ Real.exp (766 * E) / 16 := by
    have h4K0 : (0 : ℝ) < (4 : ℝ) ^ Klev := by positivity
    have hstep : (2 : ℝ) ^ (104 : ℕ) * 4 ^ Klev * Mr ^ (6 : ℕ)
        ≤ (E ^ (6 : ℕ) / 16) * (4 : ℝ) ^ Klev := by
      have h := mul_le_mul_of_nonneg_right hpow104 h4K0.le
      linarith [h]
    have hstep2 : (E ^ (6 : ℕ) / 16) * (4 : ℝ) ^ Klev
        ≤ (Real.exp (6 * E) / 16) * Real.exp (760 * E) :=
      mul_le_mul (by linarith [hE6exp]) h4K (by positivity) (by positivity)
    have hid : (Real.exp (6 * E) / 16) * Real.exp (760 * E) = Real.exp (766 * E) / 16 := by
      rw [show (766 : ℝ) * E = 6 * E + 760 * E by ring, Real.exp_add]
      ring
    linarith [hstep, hstep2, hid]
  have hHlopos : (0 : ℝ) < ((R.Hlo : ℕ) : ℝ) := by
    have h := R.hHlo_floor
    have : (0 : ℕ) < R.Hlo := by omega
    exact_mod_cast this
  have hHhige : Real.exp (E ^ 2) ≤ ((R.Hhi : ℕ) : ℝ) := by
    have h := Real.exp_le_exp.mpr (hY ▸ hlo)
    rw [Real.exp_log hHlopos] at h
    have h2 : ((R.Hlo : ℕ) : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast R.hHlohi
    linarith
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hcR0 : (0 : ℝ) < (c : ℝ) := by linarith
  -- ⟦THE ONE CAP SITE⟧ the source's `hcRb`/`hcsqb` pair, replaced by the charge route
  -- `2 * 262144 * c ^ 2 = 524288 * c ^ 2 ≤ e ^ 14 * e ^ (2 * Lc) = e ^ (14 + 2 * Lc)`.
  have hL0 : (0 : ℝ) ≤ Lc := le_trans (Real.log_nonneg hcR1) hcL
  have hcE2 : 2 * 262144 * (c : ℝ) ^ 2 ≤ Real.exp (14 + 2 * Lc) := by
    have hE14 : (524288 : ℝ) ≤ Real.exp 14 := by
      have he : Real.exp 14 = (Real.exp 1) ^ (14 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      rw [he]
      calc (524288 : ℝ) ≤ (2.7 : ℝ) ^ (14 : ℕ) := by norm_num
        _ ≤ (Real.exp 1) ^ (14 : ℕ) := pow_le_pow_left₀ (by norm_num) h1.le 14
    have hcexp : (c : ℝ) ≤ Real.exp Lc := by
      calc (c : ℝ) = Real.exp (Real.log (c : ℝ)) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp Lc := Real.exp_le_exp.mpr hcL
    have hcsqE : (c : ℝ) ^ 2 ≤ Real.exp (2 * Lc) := by
      have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (c : ℝ)) hcexp 2
      have hid : (Real.exp Lc) ^ (2 : ℕ) = Real.exp (2 * Lc) := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [hid] at hp
      exact hp
    calc 2 * 262144 * (c : ℝ) ^ 2 ≤ Real.exp 14 * (c : ℝ) ^ 2 := by
          have := mul_le_mul_of_nonneg_right hE14 (by positivity : (0 : ℝ) ≤ (c : ℝ) ^ 2)
          linarith
      _ ≤ Real.exp 14 * Real.exp (2 * Lc) :=
          mul_le_mul_of_nonneg_left hcsqE (Real.exp_pos _).le
      _ = Real.exp (14 + 2 * Lc) := (Real.exp_add _ _).symm
  have hepsR : (1 : ℝ) / (512 * (c : ℝ)) ≤ (R.eps : ℝ) := by
    have hcast : (((1 : ℚ) / (2 ^ 9 * (c : ℚ)) : ℚ) : ℝ) ≤ ((R.eps : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).mpr heps
    have heq : (((1 : ℚ) / (2 ^ 9 * (c : ℚ)) : ℚ) : ℝ) = 1 / (512 * (c : ℝ)) := by
      push_cast; norm_num
    rw [heq] at hcast
    exact hcast
  have hepsR0 : (0 : ℝ) ≤ 1 / (512 * (c : ℝ)) := by positivity
  have hepssq : (1 : ℝ) / (262144 * (c : ℝ) ^ 2) ≤ (R.eps : ℝ) ^ 2 := by
    have hmul := mul_le_mul hepsR hepsR hepsR0 (le_trans hepsR0 hepsR)
    calc (1 : ℝ) / (262144 * (c : ℝ) ^ 2)
        = (1 / (512 * (c : ℝ))) * (1 / (512 * (c : ℝ))) := by field_simp; ring
      _ ≤ (R.eps : ℝ) * (R.eps : ℝ) := hmul
      _ = (R.eps : ℝ) ^ 2 := by ring
  have hfloorR : (R.eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) - 1
      ≤ ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (R.eps ^ 2 * (R.Hhi : ℚ))
    have h' : ((R.eps ^ 2 * (R.Hhi : ℚ) : ℚ) : ℝ)
        < ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast h
    push_cast at h'
    linarith
  have hprod : (1 : ℝ) / (262144 * (c : ℝ) ^ 2) * Real.exp (E ^ 2)
      ≤ (R.eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) :=
    mul_le_mul hepssq hHhige (Real.exp_pos _).le (by positivity)
  -- ⟦THE CHARGE IN THE EXPONENT⟧ the source's `766 * E + 40 ≤ E ^ 2`, with the fixed `40`
  -- replaced by the charge `14 + 2 * Lc`, paid by `2 * Lc ≤ A - 10 ≤ E - 10`.
  have hAE : A ≤ E := by
    have hx := Real.add_one_le_exp (3.2 * A / 2)
    rw [← hEdef] at hx
    linarith
  have hE2big : 14 + 2 * Lc + 766 * E ≤ E ^ 2 := by
    have hmul : (10 : ℝ) ^ 17 * E ≤ E * E := by nlinarith [hE17, hE0]
    nlinarith [hmul, hE17, hE0, hAE, hAL]
  have hexpmono : Real.exp (14 + 2 * Lc + 766 * E) ≤ Real.exp (E ^ 2) :=
    Real.exp_le_exp.mpr hE2big
  have hbig : 2 * Real.exp (766 * E) ≤ 1 / (262144 * (c : ℝ) ^ 2) * Real.exp (E ^ 2) := by
    have hexpp : (0 : ℝ) < Real.exp (766 * E) := Real.exp_pos _
    have hstep : 2 * 262144 * (c : ℝ) ^ 2 * Real.exp (766 * E) ≤ Real.exp (E ^ 2) := by
      calc 2 * 262144 * (c : ℝ) ^ 2 * Real.exp (766 * E)
          ≤ Real.exp (14 + 2 * Lc) * Real.exp (766 * E) :=
            mul_le_mul_of_nonneg_right hcE2 hexpp.le
        _ = Real.exp (14 + 2 * Lc + 766 * E) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (E ^ 2) := hexpmono
    have hden : (0 : ℝ) < 262144 * (c : ℝ) ^ 2 := by positivity
    have hre : (1 : ℝ) / (262144 * (c : ℝ) ^ 2) * Real.exp (E ^ 2)
        = Real.exp (E ^ 2) / (262144 * (c : ℝ) ^ 2) := by ring
    rw [hre, le_div_iff₀ hden]
    nlinarith [hstep]
  have hEle : (18 : ℝ) * E + 5 ≤ Real.exp (766 * E) := by
    have h1 : (1 : ℝ) + 766 * E ≤ Real.exp (766 * E) := by
      linarith [Real.add_one_le_exp (766 * E)]
    linarith [hE17]
  linarith [hbeR, hprodL, hhi, hfloorR, hprod, hbig, hEle]


/-- **⟦THE LEVERED BLOCK LINE AT A GENERIC CHARGE⟧ (class A)** — the `_L` sibling of
`flat_blk_line_gk_b9` (`S15SelLinearWide.lean:565`): the same interface edit, read off the
levered witness above at the SAME frozen dummy instance
(`Cg := 0`, `δ₀ := 1 / 2 ^ 10`, `Ct := 1`, `K := 1`, `x₀ := 0`, `Mfl := 0`).  The conclusion and
every other binder are the source's, byte for byte.  BODY: the source's term, with the supplier
swapped and `hcb` replaced by `hcL`/`hAL`.  Nothing here bears on twin primes. -/
theorem flat_blk_line_gk_L {A : ℝ} (hA : 26 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {Lc : ℝ} {c : ℕ} (hc1 : 1 ≤ c)
    (hcL : Real.log (c : ℝ) ≤ Lc) (hAL : 10 + 2 * Lc ≤ A)
    {R : ChowlaRegime}
    (heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    -- amended per REF-FLAT-SAT: the `Λ` slot carries the `Nat.ceil` overshoot factor `2`
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    ((s13BlockExp_L_gk Klev (flatDoorM A) : ℕ) : ℝ) + 1
        + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) :=
  (s15_sel''_L_gk_witness_flat_L (A := A) (Cg := 0) (δ₀ := 1 / 2 ^ 10) (Ct := 1) (K := 1)
    (x₀ := 0) (Mfl := 0) (c := c) hA Klev hKle hc1 hcL hAL (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp) (by simp)
    (by simpa using (Real.exp_pos (Real.exp (3.2 * A) / 10)).le) heps hlo hhi).blk

/-! ## §W1c — the selector at a tower-relative clearing register

The landed `S15Sel''_L.rho` (`S15SelLinear.lean:122`) is the FIXED numeral `-log ρ ≤ 10 ^ 14`,
and the 2026-09-17 flag measured it REFUTED at the rung-2 charge `-log ρ ≤ 16 * A`: `16 * A`
outgrows `10 ^ 14` and `A` is bounded above by nothing.  The register was only ever spent
AGAINST THE TOWER — its four binding readers on the conditional road all close through one
numeric core, `14 * e ^ (λ / 2) + 10 ^ 15 ≤ c * e ^ λ` at `e ^ λ = log H₋`.  So the siblings
here state the register RELATIVE to the tower,

    `rho : -Real.log ρ ≤ Real.log H₋ / 10000`,

and every other field is the landed structure's, byte for byte, under the SAME field name — so
every projection (`.hM`, `.blk`, `.half`, …) keeps its name at the consumers.  Nothing here
bears on twin primes. -/

/-- **⟦THE `M`-SELECTION REGISTER AT A TOWER-RELATIVE CHARGE⟧** (`S15Sel''_L_T`) —
`S15Sel''_L` (`S15SelLinear.lean:104`) with ONE field changed: `rho`'s fixed `10 ^ 14` becomes
`log H₋ / 10 ^ 4`.  The ten other fields, their names and their docstrings are the source's,
byte for byte. -/
structure S15Sel''_L_T (Cg δ₀ Ct ρ : ℝ) (x₀ Mfl : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop where
  /-- the door's parameter is a modulus. -/
  hM : 1 ≤ M
  /-- ⟦`M`-LOWER 0⟧ the graded twin's own `ℕ`-floor. -/
  mfloor : Mfl ≤ M
  /-- ⟦`M`-LOWER 1⟧ `MSelect'.bfloor` = `M4DoorGates.hMδ`. -/
  bfloor : 24 * Cg / δ₀ ≤ (M : ℝ)
  /-- ⟦`M`-LOWER 2⟧ `MSelect'.gRows`, at the LINEAR anchor. -/
  gRows : 242 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ ((AdoorL M : ℕ) : ℝ)
  /-- ⟦RESTORED⟧ the opaque threshold at the LINEAR row floor. -/
  x0M : x₀ ≤ 2 ^ doorRowFloorL M
  /-- ⟦`M`-UPPER 1⟧ `MSelect'.blockCeil` AND ⟦F3⟧'s `block`, at the LINEAR block exponent. -/
  blk : ((s13BlockExp_L M : ℕ) : ℝ) + 1 + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)
  /-- ⟦`M`-UPPER 2⟧ THE WINDOW GATE at the LINEAR half-window floor. -/
  half : (7 / 10 : ℝ) * ((doorRowFloorL M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
    ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 2
  /-- ⟦THE ONE CHANGED FIELD⟧ the clearing charge RELATIVE TO THE TOWER —
  `ρ ≥ e ^ (-(log H₋) / 10 ^ 4)`.  The landed `S15Sel''_L.rho`'s fixed `10 ^ 14` is this
  register at `log H₋ ≥ 10 ^ 18`, so the landed structure implies this one at the landed
  tower floor (`S15Sel''_L.toT`, below). -/
  rho : -Real.log ρ ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 10000
  /-- ⟦THE REPAIR⟧ the `ρ`-frame's ⟦C1⟧ anchor at `DoorArithFrameRho_L.anchor`'s OWN right
  side `3.9·10⁹·M` — LINEAR in the door's parameter, hence exponential in `λ₋`. -/
  anchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33
    ≤ 39 * 10 ^ 8 * (M : ℝ)
  /-- the `𝒯`-leg budget at `constPool`, at the LINEAR anchor. -/
  gP1 : 29 + Real.log Ct + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ
  /-- the `level1` budget — the const-pool line, at the LINEAR anchor. -/
  lvl : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      + (1 / 3) * Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ))
      + (-Real.log ρ)
    ≤ (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2

/-- **⟦THE LEVERED REGISTER AT A TOWER-RELATIVE CHARGE⟧** (`S15Sel''_L_gk_T`) —
`S15Sel''_L_gk` (`S15SelLinear.lean:139`) with the same ONE field changed. -/
structure S15Sel''_L_gk_T (K : ℕ) (Cg δ₀ Ct ρ : ℝ) (x₀ Mfl : ℕ) (R : ChowlaRegime) (M : ℕ) :
    Prop where
  /-- the door's parameter is a modulus. -/
  hM : 1 ≤ M
  /-- ⟦`M`-LOWER 0⟧ the graded twin's own `ℕ`-floor. -/
  mfloor : Mfl ≤ M
  /-- ⟦`M`-LOWER 1⟧ `MSelect'_gk K.bfloor`. -/
  bfloor : 24 * Cg / δ₀ ≤ (M : ℝ)
  /-- ⟦`M`-LOWER 2⟧ `MSelect'_gk K.gRows`, at the LINEAR anchor. -/
  gRows : 242 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ ((AdoorL M : ℕ) : ℝ)
  /-- ⟦RESTORED⟧ the opaque threshold at the LINEAR row floor. -/
  x0M : x₀ ≤ 2 ^ doorRowFloorL M
  /-- ⟦`M`-UPPER 1⟧ the block ceiling at the levered LINEAR block exponent. -/
  blk : ((s13BlockExp_L_gk K M : ℕ) : ℝ) + 1 + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)
  /-- ⟦`M`-UPPER 2⟧ THE WINDOW GATE at the LINEAR half-window floor. -/
  half : (7 / 10 : ℝ) * ((doorRowFloorL M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
    ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 2
  /-- ⟦THE ONE CHANGED FIELD⟧ the clearing charge RELATIVE TO THE TOWER. -/
  rho : -Real.log ρ ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 10000
  /-- ⟦THE REPAIR⟧ the ⟦C1⟧ anchor at `3.9·10⁹·M`. -/
  anchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33
    ≤ 39 * 10 ^ 8 * (M : ℝ)
  /-- the `𝒯`-leg budget at `constPool`, at the LINEAR anchor. -/
  gP1 : 29 + Real.log Ct + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ
  /-- the `level1` budget at the LINEAR anchor. -/
  lvl : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      + (1 / 3) * Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ))
      + (-Real.log ρ)
    ≤ (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2

/-- **⟦THE LANDED REGISTER IMPLIES THE TOWER-RELATIVE ONE, AT THE LANDED TOWER FLOOR⟧**
(`S15Sel''_L.toT`) — so every rung-1 witness of `S15Sel''_L` inhabits the sibling and nothing
is lost.  Ten fields transport verbatim; `rho` is the ONE arithmetic step.

THE NUMERAL, derived: `hlam` gives `50 ≤ log (log H₋)`, and `log H₋ > 1` (so
`e ^ (log (log H₋)) = log H₋` by `Real.exp_log`) because `R.hHlo_floor` puts `H₋ ≥ 4 · 10 ^ 6`.
Hence `log H₋ ≥ e ^ 50 = (e ^ 25) ^ 2 ≥ (6 · 10 ^ 10) ^ 2 = 3.6 · 10 ^ 21` (`epsRung2_exp25`,
§W3), so `log H₋ / 10 ^ 4 ≥ 3.6 · 10 ^ 17 ≥ 10 ^ 14 ≥ -log ρ`: free by `3600 ×`.
Nothing here bears on twin primes. -/
theorem S15Sel''_L.toT {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (h : S15Sel''_L Cg δ₀ Ct ρ x₀ Mfl R M)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) :
    S15Sel''_L_T Cg δ₀ Ct ρ x₀ Mfl R M where
  hM := h.hM
  mfloor := h.mfloor
  bfloor := h.bfloor
  gRows := h.gRows
  x0M := h.x0M
  blk := h.blk
  half := h.half
  rho := by
    have hHR : (4000000 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast R.hHlo_floor
    have hy : (0 : ℝ) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := Real.log_nonneg (by linarith)
    have h1 : (1 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
      one_lt_log_of_loglog_ge hy (by norm_num : (0 : ℝ) < 50) hlam
    have hexp : Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) = Real.log ((R.Hlo : ℕ) : ℝ) :=
      Real.exp_log (by linarith)
    have h50 : Real.exp (50 : ℝ) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
      rw [← hexp]; exact Real.exp_le_exp.mpr hlam
    have hsplit : Real.exp (50 : ℝ) = Real.exp 25 * Real.exp 25 := by
      rw [← Real.exp_add]; norm_num
    have h36 : (3.6e21 : ℝ) ≤ Real.exp (50 : ℝ) := by
      rw [hsplit]; nlinarith [epsRung2_exp25, Real.exp_pos (25 : ℝ)]
    linarith [h.rho, h36, h50]
  anchor := h.anchor
  gP1 := h.gP1
  lvl := h.lvl

/-- **⟦THE LANDED LEVERED REGISTER IMPLIES ITS TOWER-RELATIVE SIBLING⟧**
(`S15Sel''_L_gk.toT`) — `S15Sel''_L.toT` at the lever; the `rho` step is the same arithmetic,
and the ten other fields transport verbatim.  Nothing here bears on twin primes. -/
theorem S15Sel''_L_gk.toT {K : ℕ} {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (h : S15Sel''_L_gk K Cg δ₀ Ct ρ x₀ Mfl R M)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) :
    S15Sel''_L_gk_T K Cg δ₀ Ct ρ x₀ Mfl R M where
  hM := h.hM
  mfloor := h.mfloor
  bfloor := h.bfloor
  gRows := h.gRows
  x0M := h.x0M
  blk := h.blk
  half := h.half
  rho := by
    have hHR : (4000000 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast R.hHlo_floor
    have hy : (0 : ℝ) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := Real.log_nonneg (by linarith)
    have h1 : (1 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
      one_lt_log_of_loglog_ge hy (by norm_num : (0 : ℝ) < 50) hlam
    have hexp : Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) = Real.log ((R.Hlo : ℕ) : ℝ) :=
      Real.exp_log (by linarith)
    have h50 : Real.exp (50 : ℝ) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
      rw [← hexp]; exact Real.exp_le_exp.mpr hlam
    have hsplit : Real.exp (50 : ℝ) = Real.exp 25 * Real.exp 25 := by
      rw [← Real.exp_add]; norm_num
    have h36 : (3.6e21 : ℝ) ≤ Real.exp (50 : ℝ) := by
      rw [hsplit]; nlinarith [epsRung2_exp25, Real.exp_pos (25 : ℝ)]
    linarith [h.rho, h36, h50]
  anchor := h.anchor
  gP1 := h.gP1
  lvl := h.lvl

/-- `S15Sel''_L.head` at the tower-relative register (`S15SelLinear.lean:172`).  STATEMENT: the
source's with `S15Sel''_L ↦ S15Sel''_L_T`.  BODY: the source's, verbatim — it reads `blk` only.
Nothing here bears on twin primes. -/
theorem S15Sel''_L_T.head {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hsel : S15Sel''_L_T Cg δ₀ Ct ρ x₀ Mfl R M)
    (hΛ : 0 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) :
    s13BlockExp_L M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1 := by
  have h := hsel.blk
  have hR : ((s13BlockExp_L M : ℕ) : ℝ) ≤ ((4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
    push_cast; linarith
  have : s13BlockExp_L M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ := by exact_mod_cast hR
  omega

/-- `S15Sel''_L_gk.head` at the tower-relative register (`S15SelLinear.lean:183`).  STATEMENT:
the source's with `S15Sel''_L_gk ↦ S15Sel''_L_gk_T`.  BODY: the source's, verbatim.
Nothing here bears on twin primes. -/
theorem S15Sel''_L_gk_T.head {K : ℕ} {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hsel : S15Sel''_L_gk_T K Cg δ₀ Ct ρ x₀ Mfl R M)
    (hΛ : 0 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) :
    s13BlockExp_L_gk K M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1 := by
  have h := hsel.blk
  have hR : ((s13BlockExp_L_gk K M : ℕ) : ℝ) ≤ ((4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
    push_cast; linarith
  have : s13BlockExp_L_gk K M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ := by exact_mod_cast hR
  omega

/-- `s15_sel''_L_gk_of_L` at the tower-relative register (`S15SelLinear.lean:524`).  STATEMENT:
the source's with both structures suffixed `_T`.  BODY: the source's, verbatim — `rho`
transports like the other nine, because it is the SAME field in both siblings.
Nothing here bears on twin primes. -/
theorem s15_sel''_L_gk_T_of_L_T (Klev : ℕ) {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime}
    {M : ℕ} (hsel : S15Sel''_L_T Cg δ₀ Ct ρ x₀ Mfl R M)
    (hblk : ((s13BlockExp_L_gk Klev M : ℕ) : ℝ) + 1
        + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)) :
    S15Sel''_L_gk_T Klev Cg δ₀ Ct ρ x₀ Mfl R M where
  hM := hsel.hM
  mfloor := hsel.mfloor
  bfloor := hsel.bfloor
  gRows := hsel.gRows
  x0M := hsel.x0M
  blk := hblk
  half := hsel.half
  rho := hsel.rho
  anchor := hsel.anchor
  gP1 := hsel.gP1
  lvl := by rw [calQK_gk_one_eq]; exact hsel.lvl

/-- `s15_bandGate''_of_grade_L_gk` at the tower-relative register
(`S16FlatTerminalLinear.lean:800`).  STATEMENT: the source's with
`S15Sel''_L_gk ↦ S15Sel''_L_gk_T`; the conclusion is the source's, byte for byte.  BODY: the
source's, verbatim — it reads `x0M`, `blk` and `hM`, and never `rho`.
Nothing here bears on twin primes. -/
theorem s15_bandGate''_of_grade_L_gk_T (K : ℕ) {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ}
    {R : ChowlaRegime} {M : ℕ} {C' : ℝ} (hfl : loglogFloor50 ≤ R.Hlo)
    (hsel : S15Sel''_L_gk_T K Cg δ₀ Ct ρ x₀ Mfl R M)
    (hgrade : 8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
      ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))) :
    S13BandGate'_L_gk K R M x₀ C' (fun _ => 1) where
  x0_le := hsel.x0M
  C1_one := fun _ => le_rfl
  grade := hgrade
  block := by
    intro H L q j A s hb
    exact s15_block_at_socket_L_gk K (socketBase_of_socketBaseL hsel.hM hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk

/-- **⟦THE λ-ENGINE AT A TOWER-RELATIVE REGISTER⟧** (`flat_lambda_core_T`) —
`flat_lambda_core` (`TowerFlatExport.lean:212`) with the additive constant `10 ^ 15` cut to
`1000` and the coefficient `2 · 10 ^ (-4)` raised to `8 · 10 ^ (-4)`.  BODY: the source's, with
its inline `2.7 < e` / `2.7 ^ 25` derivation replaced by the landed `epsRung2_exp25` (§W3),
which is that derivation's own conclusion.

THE MARGIN, derived: with `u = e ^ (λ / 2) ≥ e ^ 25 ≥ 6 · 10 ^ 10` and `e ^ λ = u ^ 2`, the
demand is `14 * u + 1000 ≤ 0.0008 * u ^ 2`; at the floor `u = 6 · 10 ^ 10` the right side is
`0.0008 * 3.6 · 10 ^ 21 = 2.88 · 10 ^ 18` against a left side `8.4 · 10 ^ 11 + 1000`, free by
`3.4 · 10 ^ 6 ×`, and improving in `u`.  Nothing here bears on twin primes. -/
theorem flat_lambda_core_T {lam : ℝ} (hlam : 50 ≤ lam) :
    14 * Real.exp (lam / 2) + 1000 ≤ 0.0008 * Real.exp lam := by
  set u : ℝ := Real.exp (lam / 2) with hu
  have hupos : (0 : ℝ) < u := Real.exp_pos _
  have husq : u * u = Real.exp lam := by
    rw [hu, ← Real.exp_add]; congr 1; ring
  have h25 : Real.exp (25 : ℝ) ≤ u := by
    rw [hu]; exact Real.exp_le_exp.mpr (by linarith)
  have hulo : (6e10 : ℝ) ≤ u := le_trans epsRung2_exp25 h25
  nlinarith [hulo, hupos, husq]

/-- `s12c_eps_threshold_at_socket_flat` at the tower-relative register
(`FlatConsumers.lean:72`).  STATEMENT: the source's with the ONE binder
`hrho : -log ρ ≤ 10 ^ 14` replaced by `hrho : -log ρ ≤ log H₋ / 10 ^ 4`; the conclusion is the
source's, byte for byte.  BODY: the source's, with `flat_lambda_core ↦ flat_lambda_core_T` and
`hrho` rewritten to the tower atom `e ^ (log (log H₋)) / 10 ^ 4` (which the `set` then folds to
`e ^ lam / 10 ^ 4`) before the close.  ⚠️ There is NO `hρ : 0 < ρ` binder here and none is
needed.

THE MARGIN, derived: the close needs `14 * u + 13 + (-log ρ) ≤ (θ - ε) * ll`, and the register
now pays `0.0001 * e ^ lam` where `hll`/`hprod` supply `(θ - ε) * ll ≥ ll / 500 ≥
0.001 * e ^ lam`.  So `0.0008` (the core) `+ 0.0001` (the register) `= 0.0009 ≤ 0.001`: the
slack coefficient on `e ^ lam` is `0.0001`, plus the core's own `1000 - 13 = 987`.  This is the
TIGHTEST of the four readers.  Nothing here bears on twin primes. -/
theorem s12c_eps_threshold_at_socket_flat_T {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ ε : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 10000)
    (hε : ε ≤ theta293 - 1 / 500) :
    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
      ≤ (theta293 - ε) * Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  obtain ⟨hlogHlo0, -⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hlogHlo1 : (1 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hlogHlo0 (by norm_num : (0 : ℝ) < 50) hlam
  have hrhoE : -Real.log ρ ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) / 10000 := by
    rw [Real.exp_log (by linarith : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ))]; exact hrho
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hll := s12c_llX_ge hfl hb
  have hcore := flat_lambda_core_T hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by linarith
  have hcoef : (1 : ℝ) / 500 ≤ theta293 - ε := by linarith
  have hprod : (1 : ℝ) / 500 * ll ≤ (theta293 - ε) * ll :=
    mul_le_mul_of_nonneg_right hcoef hll0
  have h1 : 14 * Λ ≤ 14 * Real.exp (lam / 2) := by linarith
  linarith

/-- `s15_heps293_at_socket_flat` at the tower-relative register (`FlatConsumers.lean:117`).
STATEMENT: the source's with the ONE `hrho` binder moved to the tower; the conclusion is the
source's, byte for byte.  BODY: the source's, with `flat_lambda_core_17 ↦ flat_lambda_core_T`
and `hrho ↦ hrhoE` in `hkey`'s close.

THE MARGIN, derived: `hkey` needs `14 * u + 13 + 0.0001 * e ^ lam ≤ θ * ll`, and `h2` supplies
`θ * ll ≥ 0.0017 * e ^ lam`; `0.0008 + 0.0001 = 0.0009 ≤ 0.0017`, slack coefficient `0.0008`.
Nothing here bears on twin primes. -/
theorem s15_heps293_at_socket_flat_T {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hρ : 0 < ρ)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 10000) :
    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi := by
  obtain ⟨hlogHlo0, -⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hlogHlo1 : (1 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hlogHlo0 (by norm_num : (0 : ℝ) < 50) hlam
  have hrhoE : -Real.log ρ ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) / 10000 := by
    rw [Real.exp_log (by linarith : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ))]; exact hrho
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpool : constPool ρ R.Hhi = Real.exp (Real.log ρ - Real.log 376266 - 14 * Λ) := by
    rw [constPool_def, hLamdef, Real.exp_sub, Real.exp_sub, Real.exp_log hρ,
      Real.exp_log (by norm_num : (0 : ℝ) < 376266), div_div]
  have hlhs : (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) = Real.exp (-(theta293 * ll)) := by
    rw [Real.rpow_def_of_pos hX0, hlldef]; congr 1; ring
  rw [hlhs, hpool]
  refine Real.exp_le_exp.mpr ?_
  have hθ : (0.0034 : ℝ) ≤ theta293 := by have := s13_theta293_margin_lo; linarith
  have hll := s12c_llX_ge hfl hb
  have hcore := flat_lambda_core_T hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by
    have : (0 : ℝ) < Real.exp lam / 2 := by positivity
    linarith [hll]
  have hkey : 14 * Λ + 13 + (-Real.log ρ) ≤ theta293 * ll := by
    have h1 : 14 * Λ ≤ 14 * Real.exp (lam / 2) := by linarith [htow]
    have h2 : theta293 * ll ≥ 0.0034 * (Real.exp lam / 2) := by
      nlinarith [hθ, hll, hll0]
    nlinarith [h1, h2, hcore, hrhoE]
  linarith [hkey, hlog376]

/-- `s15_hband4096_at_socket_flat` at the tower-relative register (`FlatConsumers.lean:159`).
STATEMENT: the source's with the ONE `hrho` binder moved to the tower; the conclusion is the
source's, byte for byte.  BODY: the source's, with `flat_lambda_core_17 ↦ flat_lambda_core_T`
and `hrho ↦ hrhoE` in the close.

THE MARGIN, derived: the close needs `14 * u + 9 + 13 + 0.0001 * e ^ lam ≤ 0.998 * ll`, and
`h2` supplies `0.998 * ll ≥ 0.0017 * e ^ lam`; `0.0009 ≤ 0.0017`, slack coefficient `0.0008`.
Nothing here bears on twin primes. -/
theorem s15_hband4096_at_socket_flat_T {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hρ : 0 < ρ)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 10000) :
    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500) * constPool ρ R.Hhi := by
  obtain ⟨hlogHlo0, -⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hlogHlo1 : (1 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hlogHlo0 (by norm_num : (0 : ℝ) < 50) hlam
  have hrhoE : -Real.log ρ ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) / 10000 := by
    rw [Real.exp_log (by linarith : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ))]; exact hrho
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpool : constPool ρ R.Hhi = Real.exp (Real.log ρ - Real.log 376266 - 14 * Λ) := by
    rw [constPool_def, hLamdef, Real.exp_sub, Real.exp_sub, Real.exp_log hρ,
      Real.exp_log (by norm_num : (0 : ℝ) < 376266), div_div]
  have hlhs : (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
      = Real.exp ((1 - (1 : ℝ) / 500) * ll) := by
    rw [Real.rpow_def_of_pos hX0, hlldef]; congr 1; ring
  rw [hlhs, hpool, ← Real.exp_add]
  have h4096 : (4096 : ℝ) ≤ Real.exp 9 := by
    have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7 : ℝ) ^ (9 : ℕ) ≤ (Real.exp 1) ^ (9 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 9
    have hn : (4096 : ℝ) ≤ (2.7 : ℝ) ^ (9 : ℕ) := by norm_num
    rw [h]; linarith
  refine le_trans h4096 (Real.exp_le_exp.mpr ?_)
  have hll := s12c_llX_ge hfl hb
  have hcore := flat_lambda_core_T hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by
    have : (0 : ℝ) < Real.exp lam / 2 := by positivity
    linarith [hll]
  have h1 : 14 * Λ ≤ 14 * Real.exp (lam / 2) := by linarith [htow]
  have h2 : (1 - (1 : ℝ) / 500) * ll ≥ 0.0017 * Real.exp lam := by nlinarith [hll, hll0]
  linarith [h1, h2, hcore, hrhoE, hlog376]

/-- `s15_gRows_const_at_socket_flat_doorL_gk` at the tower-relative register
(`S16FlatTerminalLinear.lean:964`).  STATEMENT: the source's with the ONE `hrho` binder moved
to the tower; the conclusion is the source's, byte for byte.  BODY: the source's, with
`flat_lambda_core_17 ↦ flat_lambda_core_T`, `hrho ↦ hrhoE` in `hendbud`'s close, and the ONE
positivity fact `hE0` the smaller core no longer carries for free (the landed `10 ^ 15` inside
`flat_lambda_core_17` had bounded `e ^ lam` below all by itself).

THE MARGIN, derived: `hendbud` needs `26 + 14 * u + 0.0001 * e ^ lam ≤ log (A + s)`, and
`hll`/`hllle` supply `log (A + s) ≥ e ^ lam / 2 + 1`; `0.0009 ≤ 0.5`, slack coefficient
`0.4991`.  This is the SLACKEST of the four readers.  Nothing here bears on twin primes. -/
theorem s15_gRows_const_at_socket_flat_doorL_gk_T (K : ℕ) {R : ChowlaRegime}
    {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseL R M H L q j A s) (hM : 1 ≤ M)
    (hρ0 : 0 < ρ) (_hρ1 : ρ ≤ 1)
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 10000)
    (hlvl : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        + (1 / 3) * Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ))
        + (-Real.log ρ)
      ≤ (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2) :
    GRowsZeroGate'''_L_gk K M (A + s) 0 (constPool ρ R.Hhi) := by
  obtain ⟨hlogHlo0, hlamT⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hlogHlo1 : (1 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hlogHlo0 (by norm_num : (0 : ℝ) < 50) hlamT
  have hrhoE : -Real.log ρ ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) / 10000 := by
    rw [Real.exp_log (by linarith : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ))]; exact hrho
  have hE0 : (0 : ℝ) < Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) := Real.exp_pos _
  have hbb : SocketBase R M H L q j A s := socketBase_of_socketBaseL hM hb
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le _hρ1
  have hQ0 : (0 : ℝ)
      ≤ Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) := by
    rw [calQK_L_one_gk_eq]; exact s15_loglogQ1_L_nonneg hM
  obtain ⟨-, hL50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have hp2 : 27 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ := by
    linarith [hlvl, hQ0, hL50, hlogρ]
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hA : 0 < A := hbb.2.2.2.2.2.2.2.1
  have hAs : 0 < A + s := by omega
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hbb
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hllle : Real.log (Real.log (((A + s : ℕ)) : ℝ)) ≤ Real.log (((A + s : ℕ)) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hll := s12c_llX_ge hfl hbb
  have hcore := flat_lambda_core_T hlam50
  have hendbud : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + (-Real.log ρ)
      ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h1 : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        ≤ 14 * Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := by linarith
    linarith [hcore, hll, hllle, hrhoE, h1, hE0]
  exact gRowsZeroGate'''_L_gk_of_budget K hM hAs hρ0 (by linarith) hp2 hendbud

/-! ### §W1c(b) — R11's second half, re-targeted at the tower-relative register

The four rows the 2026-09-17 flag stopped on, unchanged in every respect but their conclusion:
they now produce the `_T` siblings, whose `rho` field the charge `-log ρ ≤ 16 * A` PAYS. -/

/-- **⟦THE CHARGE CARRIER AT A CHARGE PAID BY `A`⟧** (`s15_sel''_L_witness_flat_charge_L`) —
`s15_sel''_L_witness_flat_charge_g12b` (`StrideGrade12bWalls.lean:49`) at the rung-2 interface:
`hcb : c ≤ 8103 ↦ hcL`/`hAL`, `hρlog : -log ρ ≤ 429 ↦ ≤ 16 * A`, `hCtb` at `2 ^ 23` kept, and
the conclusion at `S15Sel''_L_T`.  `hbase` is §W1b-ii's `s15_sel''_L_witness_flat_L` at the same
FROZEN dummy literals; `half`/`anchor`/`gP1`/`lvl` are §W1b-i's four `_L` cap lines at
`c ≤ 16 * A` (the source's widening `429 ≤ 439` disappears, as priced).

THE `rho` BULLET, derived — this is the row the landed `10 ^ 14` register refuted, and the one
the tower-relative register pays.  With `E := e ^ (3.2 * A / 2)`: `Real.add_one_le_exp` gives
`1.6 * A + 1 ≤ E`, `flat_exp_half_ge` gives `E ≥ 10 ^ 17`, `flat_exp_sq` gives
`E ^ 2 = e ^ (3.2 * A)`, and the ONE product `hEE : 10 ^ 5 * E ≤ E ^ 2` (isolated as a `have`,
so the close stays LINEAR) then chains
`160000 * A ≤ 100000 * E - 100000 ≤ E ^ 2 - 100000 = e ^ (3.2 * A) - 100000 ≤ log H₋`,
i.e. `16 * A ≤ log H₋ / 10 ^ 4`.  `hEE` needs only `E ≥ 10 ^ 5` against the register's
`E ≥ 10 ^ 17`: free by `10 ^ 12 ×`.  Nothing here bears on twin primes. -/
theorem s15_sel''_L_witness_flat_charge_L {A : ℝ} (hA : 26 ≤ A) {Cg δ₀ Ct ρ Lc : ℝ}
    {x₀ Mfl c : ℕ} {R : ChowlaRegime} (hc1 : 1 ≤ c)
    (hcL : Real.log (c : ℝ) ≤ Lc) (hAL : 10 + 2 * Lc ≤ A)
    (hρlog : -Real.log ρ ≤ 16 * A)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    -- amended per REF-FLAT-SAT: the `Λ` slot carries the `Nat.ceil` overshoot factor `2`
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L_T Cg δ₀ Ct ρ x₀ Mfl R (flatDoorM A) := by
  have hbase := s15_sel''_L_witness_flat_L (A := A) (Cg := 0) (δ₀ := 1 / 2 ^ 10) (Ct := 1)
    (K := 1) (Lc := Lc) (x₀ := x₀) (Mfl := Mfl) (c := c) (R := R) hA hc1 hcL hAL (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp) hMfl
    hx0win heps hlo hhi
  have hinv : Real.log (1 / ρ) = -Real.log ρ := by rw [one_div, Real.log_inv]
  refine
    { hM := hbase.hM
      mfloor := hMfl
      bfloor := hbfl
      gRows := hbase.gRows
      x0M := hbase.x0M
      blk := hbase.blk
      half := ?_
      rho := ?_
      anchor := ?_
      gP1 := ?_
      lvl := ?_ }
  · rw [hinv]
    exact le_trans (flat_half_line_L hA hρlog) (by linarith [hlo])
  · -- ⟦THE TOWER-RELATIVE REGISTER, PAID BY THE DESIGN CONSTANT⟧
    have hE17 := flat_exp_half_ge hA
    have hE0 : (0 : ℝ) < Real.exp (3.2 * A / 2) := Real.exp_pos _
    have hY := flat_exp_sq A
    have h16 : 1.6 * A + 1 ≤ Real.exp (3.2 * A / 2) := by
      have hx := Real.add_one_le_exp (3.2 * A / 2)
      linarith
    have hEE : (100000 : ℝ) * Real.exp (3.2 * A / 2) ≤ Real.exp (3.2 * A / 2) ^ 2 := by
      nlinarith [hE17, hE0]
    linarith [hρlog, hlo, hY, hEE, h16]
  · rw [hinv]
    -- amended per REF-FLAT-SAT: the wide anchor line, at the doubled `Λ` slot
    exact le_trans (by linarith [hhi]) (flat_anchor_line_wide_L hA hρlog)
  · exact flat_gP1_line_L hA (by linarith [hρlog]) hCt hCtb hhi
  · exact flat_lvl_line_L hA hρlog hhi

/-- **⟦THE SELECTOR AT A CHARGE PAID BY `A`⟧** (`s15_sel''_L_witness_flat_wide_L`) —
`s15_sel''_L_witness_flat_wide_g12b` (`StrideGrade12bWalls.lean:162`) at the rung-2 interface:
`hcb`/`hh9c ↦ hcL`/`hAL`, `hKb : K ≤ 2 ^ 539 ↦ {Kb} hKb1`/`hKb`/`hKbL`, conclusion at
`S15Sel''_L_T`.  BODY: the source's, with the charge from §W1b-i's
`s16_audit_neglog_rho_le_h_L`.

THE NUMERALS, derived: that supplier gives `-log ρ ≤ 234 + 22 * Lc`; `hAL` gives
`Lc ≤ (A - 10) / 2`, so `234 + 22 * Lc ≤ 234 + 11 * (A - 10) = 124 + 11 * A`, and
`124 + 11 * A ≤ 16 * A` iff `A ≥ 24.8`, against `hA : 26 ≤ A`.  Nothing here bears on twin
primes. -/
theorem s15_sel''_L_witness_flat_wide_L {A : ℝ} (hA : 26 ≤ A) {Cg δ₀ Ct K Kb Lc : ℝ}
    {x₀ Mfl c : ℕ} {R : ChowlaRegime}
    (hc1 : 1 ≤ c) (hcL : Real.log (c : ℝ) ≤ Lc) (hAL : 10 + 2 * Lc ≤ A)
    (hδ : 0 < δ₀) (hδb : 1 / (2 ^ 32 * (c : ℝ) ^ 2) ≤ δ₀)
    (hK : 0 < K) (hKb1 : 1 ≤ Kb) (hKb : K ≤ Kb) (hKbL : Real.log Kb ≤ 197 + 20 * Lc)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L_T Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R (flatDoorM A) :=
  s15_sel''_L_witness_flat_charge_L hA hc1 hcL hAL
    (le_trans (s16_audit_neglog_rho_le_h_L hc1 hcL hδ hK hδb hKb1 hKb hKbL) (by linarith))
    hCt hCtb hbfl hMfl hx0win heps hlo hhi

/-- **⟦THE LEVERED SELECTOR AT A CHARGE PAID BY `A`⟧**
(`s15_sel''_L_gk_witness_flat_wide_L`) — `s15_sel''_L_gk_witness_flat_wide_g12b`
(`StrideGrade12bWalls.lean:183`) at the rung-2 interface, conclusion at `S15Sel''_L_gk_T`.
BODY: the source's, with the two suppliers swapped for their `_L` twins — the selector above
and §W1b-ii's `flat_blk_line_gk_L` — through `s15_sel''_L_gk_T_of_L_T`.  Nothing here bears on
twin primes. -/
theorem s15_sel''_L_gk_witness_flat_wide_L {A : ℝ} (hA : 26 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {Cg δ₀ Ct K Kb Lc : ℝ} {x₀ Mfl c : ℕ}
    {R : ChowlaRegime}
    (hc1 : 1 ≤ c) (hcL : Real.log (c : ℝ) ≤ Lc) (hAL : 10 + 2 * Lc ≤ A)
    (hδ : 0 < δ₀) (hδb : 1 / (2 ^ 32 * (c : ℝ) ^ 2) ≤ δ₀)
    (hK : 0 < K) (hKb1 : 1 ≤ Kb) (hKb : K ≤ Kb) (hKbL : Real.log Kb ≤ 197 + 20 * Lc)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L_gk_T Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R
      (flatDoorM A) :=
  s15_sel''_L_gk_T_of_L_T Klev
    (s15_sel''_L_witness_flat_wide_L hA hc1 hcL hAL hδ hδb hK hKb1 hKb hKbL hCt hCtb hbfl hMfl
      hx0win heps hlo hhi)
    (flat_blk_line_gk_L hA Klev hKle hc1 hcL hAL heps hlo hhi)

/-- **⟦R11's SECOND HALF, CLOSED AT A CHARGE PAID BY `A`⟧**
(`s15_sel''_L_gk_witness_flat_bumped_win_L`) — `s15_sel''_L_gk_witness_flat_bumped_win_h_g12b`
(`StrideGrade12bWalls.lean:210`) at the rung-2 interface: `hh9 : log h ≤ 9 ↦ {Lc} hL0`/`hhL`/
`hAL`, `hKb : K ≤ 2 ^ 539 ↦ {Kb} hKb1`/`hKb`/`hKbL`, conclusion at `S15Sel''_L_gk_T`.  BODY:
the source's, with the bump from §W1's `flatDoorM_bfloor_bump_L`; the bridge
`1 / (2 ^ 32 * h ^ 2) ≤ 1 / (838400 * 2 ^ 12 * h ^ 2)` is the source's, on
`838400 * 4096 = 3434086400 ≤ 2 ^ 32 = 4294967296`.  Nothing here bears on twin primes. -/
theorem s15_sel''_L_gk_witness_flat_bumped_win_L {A : ℝ} (hA : 162 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {h : ℕ} (hh : 0 < h) {Lc : ℝ} (hL0 : 0 ≤ Lc)
    (hhL : Real.log (h : ℝ) ≤ Lc) (hAL : 10 + 2 * Lc ≤ A)
    {Cg δ₀ Ct K Kb : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime}
    (hδ : 0 < δ₀) (hδb : 1 / (838400 * 2 ^ 12 * (h : ℝ) ^ 2) ≤ δ₀)
    (hK : 0 < K) (hKb1 : 1 ≤ Kb) (hKb : K ≤ Kb) (hKbL : Real.log Kb ≤ 197 + 20 * Lc)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hCg : Cg ≤ 2 * 10 ^ 12) (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (h : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L_gk_T Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R
      (flatDoorM A) := by
  exact s15_sel''_L_gk_witness_flat_wide_L (flat162_ge_26 hA) Klev hKle hh hhL hAL hδ
    (by
      have h1 : (0 : ℝ) < (h : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
        positivity
      have : (1 : ℝ) / (2 ^ 32 * (h : ℝ) ^ 2) ≤ 1 / (838400 * 2 ^ 12 * (h : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [h1]
      linarith [hδb] : (1 : ℝ) / (2 ^ 32 * (h : ℝ) ^ 2) ≤ δ₀) hK hKb1 hKb hKbL hCt hCtb
    (flatDoorM_bfloor_bump_L hh hL0 hhL hA hAL hδ hδb hCg)
    hMfl hx0win heps hlo hhi

/-- **⟦THE CONDITIONAL HOP'S SIX READS, ON THE NEW SELECTOR⟧** (`s15_replay_reads_L_gk_T`) —
this wave's END-TO-END CHECK.  It takes a `S15Sel''_L_gk_T` and the conditional replay's own
context hypotheses and produces, by calling `s15_bandGate''_of_grade_L_gk_T` and the four `_T`
readers EXACTLY as `FlatDoorEpsChain.lean:1086` and `:1098-1108` call their sources, the five
facts those six lines produce.

⭐ THE POINT: `hsel.rho` feeds all four `_T` consumers with NO conversion — the register's new
shape is exactly the shape the four readers now want, so the hop composes with the argument
lists byte for byte.  The third conjunct's `ε` is pinned by the replay's own `le_rfl`
(`:1102`), which is why it reads `theta293 - (theta293 - 1 / 500)`.  Nothing here bears on twin
primes. -/
theorem s15_replay_reads_L_gk_T (K : ℕ) {R : ChowlaRegime} {Cg δ₀ Ct ρ C' : ℝ}
    {x₀ Mfl M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hsel : S15Sel''_L_gk_T K Cg δ₀ Ct ρ x₀ Mfl R M)
    (hgrade : 8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
      ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)))
    (hb : SocketBaseL R M H L q j A s) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hlam50 : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2)) :
    S13BandGate'_L_gk K R M x₀ C' (fun _ => 1)
      ∧ GRowsZeroGate'''_L_gk K M (A + s) 0 (constPool ρ R.Hhi)
      ∧ 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
          ≤ (theta293 - (theta293 - 1 / 500)) * Real.log (Real.log (((A + s : ℕ)) : ℝ))
      ∧ (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi
      ∧ (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
          * constPool ρ R.Hhi :=
  ⟨s15_bandGate''_of_grade_L_gk_T K hfl hsel hgrade,
   s15_gRows_const_at_socket_flat_doorL_gk_T K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho hsel.lvl,
   s12c_eps_threshold_at_socket_flat_T hfl (socketBase_of_socketBaseL hsel.hM hb) hlam50 htow
     hsel.rho le_rfl,
   s15_heps293_at_socket_flat_T hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
     hsel.rho,
   s15_hband4096_at_socket_flat_T hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
     hsel.rho⟩


/-! ## §W6 — the re-thread at generic `ε`, and the theorem

Rung 1 proved the family under the cap `1/(500·8103) ≤ ε` by re-cutting the flat road's chain at
generic `ε` (`FlatDoorEpsChain`: eight forms, a head, seven replays, the chain) and closing it in
the frozen file.  In that chain the numeral `8103` plays the role of the lattice count `c`
everywhere.  §§1–W5 above re-cut every capped helper as an `_L` sibling at a charge `L ≥ log c`.
This section re-threads the chain over those siblings at `c := ⌈1/(500·ε)⌉₊` with NO cap, and
states `flatDoorEpsFamilyW_holds : FlatDoorEpsFamilyW`, the frozen file's named `Prop`.  Nothing
here bears on twin primes. -/

set_option exponentiation.threshold 4000 in
/-- **⟦THE COUNT CEILING'S LOG, ONCE⟧** (`epsRung2_log_Kb_le`) — the rung-2 count leaf bounds
`|Ξ_H|` by `2^283·c^20` (`bigXi_bounded_ceiling_eps`), and every consumer of that ceiling reads it
only through its LOGARITHM, affine in `Lc = log c`.  This is the one place the large numeral is
touched: `log (2^283·c^20) = 283·log 2 + 20·log c`, and `283 · 0.6931471808 = 196.1606521664 < 197`
(`Real.log_two_lt_d9`), so the affine ceiling `197 + 20·Lc` holds with slack `0.8393478336`.  The
numeral is never evaluated — `Real.log_mul` and `Real.log_pow` strip it first. -/
theorem epsRung2_log_Kb_le {c : ℕ} (hc1 : 1 ≤ c) :
    Real.log (2 ^ 283 * (c : ℝ) ^ 20) ≤ 197 + 20 * Real.log (c : ℝ) := by
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have h1 : ((2 : ℝ) ^ (283 : ℕ)) ≠ 0 := by positivity
  have h2 : ((c : ℝ) ^ (20 : ℕ)) ≠ 0 := by positivity
  rw [Real.log_mul h1 h2, Real.log_pow, Real.log_pow]
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  push_cast
  linarith

set_option exponentiation.threshold 4000 in
/-- **⟦THE COUNT CEILING IS AT LEAST ONE⟧** (`epsRung2_one_le_Kb`) — the `hKb1` binder every
`_L` sibling that takes a generic ceiling asks for, at the rung-2 ceiling. -/
theorem epsRung2_one_le_Kb {c : ℕ} (hc1 : 1 ≤ c) : (1 : ℝ) ≤ 2 ^ 283 * (c : ℝ) ^ 20 := by
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (283 : ℕ) := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ (c : ℝ) ^ (20 : ℕ) := one_le_pow₀ hcR
  nlinarith [h1, h2]

/-! ### §W6.1 — ⟦THE EIGHT `W`-FORMS⟧ each `_Eps` form at the charge `c`, with no cap

Each `W` sibling is its `_Eps` form (`FlatDoorEpsChain` §1) with SIX substitutions and no others,
derived mechanically from the source `def`s rather than typed:

* `(1 : ℚ) / (500 * 8103) ≤ ε` ↦ `1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε` — the cap becomes the
  CHARGE: `c` is a parameter and the pin is at `c`, so the form is inhabited at every `ε`;
* `(1 : ℝ) / (838400 * 8103) ≤ δ₀` ↦ `(1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀`;
* `≤ 2 ^ 539` ↦ `≤ 2 ^ 283 * (c : ℝ) ^ 20` — the count leaf's ceiling at the charge;
* `XCeilRider ε g` ↦ `XCeilRiderAt (50 + Real.log (c : ℝ)) ε g` (and the strict twin), because on
  the landed gate's `50` floor no `_L` arm lemma closes past `Lc > 2.4689·10^17` (§W3.2);
* `S15Sel''_L_gk K …` ↦ `S15Sel''_L_gk_T K …` (§W1c), in the conditional form alone;
* after every `budgetAFlat (ε : ℝ) β ≤ A →`, the new binder `10 + 2 * Real.log (c : ℝ) ≤ A`, paid
  once by the ninth arm on the design constant. -/

-- derived from `FlatHeadFormEps` (`FlatDoorEpsChain.lean:130–147` @ a5bb7de0)
def FlatHeadFormEpsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧ 0 < δ₀ ∧
      1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 26 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap = max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            XCeilRiderAt (50 + Real.log (c : ℝ)) ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((bigXi R.eps H).card : ℝ) ≤ K) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            R.Hlo ≤ max Hcap (max extraFloor U1floor) ∧
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
              P R

-- derived from `FlatSocketFormEps` (`FlatDoorEpsChain.lean:149–176` @ a5bb7de0)
def FlatSocketFormEpsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧ 0 < δ₀ ∧
      1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRiderAt (50 + Real.log (c : ℝ)) ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              (∀ (a e : ℕ → ℂ) (Bsieve : ℕ → ℝ) (Binsert : ℝ),
                (∀ m, lamCoeff m = a m + e m) →
                (∀ H : ℕ, 0 ≤ Bsieve H) →
                (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
                  NearRatTight (arcDen 12 H) H α →
                    (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                      ≤ Bsieve H * (H : ℝ) ^ 2) →
                (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
                  (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
                    ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                      ∂(logMeasure R.x R.ω)) ≤ Binsert) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  K * (2 * Bsieve H) + 2 * Binsert ≤ δ₀) →
                P R)

-- derived from `FlatDoorL2FormEps` (`FlatDoorEpsChain.lean:178–199` @ a5bb7de0)
def FlatDoorL2FormEpsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg : ℝ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧ 0 < δ₀ ∧
      1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧
      (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRiderAt (50 + Real.log (c : ℝ)) ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
                M4DoorGates_L_gk K Cg R M k δ →
                (∀ H : ℕ, 0 ≤ Braw H) →
                M4SievedDoorSq_L_gk K R M Braw →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                  P R

-- derived from `FlatRoadFormEps` (`FlatDoorEpsChain.lean:201–233` @ a5bb7de0)
def FlatRoadFormEpsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg : ℝ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧ 0 < δ₀ ∧
      1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧
      (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRiderAt (50 + Real.log (c : ℝ)) ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
                M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
                (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
                (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                    ≤ Braw H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                M4ChiSummedFreeRow_L_gk K R M RS →
                  P R

-- derived from `FlatCapstoneFormEps` (`FlatDoorEpsChain.lean:235–326` @ a5bb7de0)
def FlatCapstoneFormEpsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ) : Prop :=
    ∃ (Cg : ℝ) (Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      Kc ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRiderAt (50 + Real.log (c : ℝ)) ε g →
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
                Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (M : ℕ), Mfl ≤ M → K ≤ 170000000 * M →
                  ∃ C' : ℝ, 0 < C' ∧
                    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                        ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                    ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                      -- ⟦A⟧ THE SPINE ARITHMETIC
                      M4DoorGates_L_gk K Cg R M k δ₀ →
                      8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                          (fun H => 2 * rStrWitness H) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                          (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                          5 ≤ Real.log (Real.log (2 * T)) →
                          (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                            ≤ 8 * (0 : ℝ) ^ 2
                              + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                    \ seamBall (((A + s : ℕ)) : ℝ) 0)
                                  ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                      (calP (AdoorL M) (s13GK K M))
                                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                      (mrAlpha (1 / 12)) 2,
                                  ‖spoly (2 * (A + s))
                                    (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                              + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                                  * (Real.log (((A + s : ℕ)) : ℝ))
                                      ^ (-theta293 + epsrf (A + s)))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        P R

-- derived from `FlatConditionalFormEps` (`FlatDoorEpsChain.lean:328–350` @ a5bb7de0)
def FlatConditionalFormEpsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ) : Prop :=
    ∃ (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      Kc ≤ 2 ^ 283 * (c : ℝ) ^ 20 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRiderStrictAt (50 + Real.log (c : ℝ)) ε g →
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ M : ℕ,
                S15Sel''_L_gk_T K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                 K ≤ 170000000 * M →
                S15CrossingBound_L_gk K R M → P R

-- derived from `FlatKswinFormEps` (`FlatDoorEpsChain.lean:352–378` @ a5bb7de0)
def FlatKswinFormEpsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ) : Prop :=
    ∃ (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧
        ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A → 10 + 2 * Real.log (c : ℝ) ≤ A →
          K ≤ 170000000 * flatDoorM A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          T₀ ≤ Real.exp (Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ) / 2) →
          Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 →
          ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrictAt (50 + Real.log (c : ℝ)) ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            (S16CofactorSupply_L_gk K Cq R (flatDoorM A) →
              S16BaseScaleCap96_L_gk K R (flatDoorM A) →
                P R))

-- derived from `V7RatedFormEps` (`FlatDoorEpsChain.lean:380–394` @ a5bb7de0)
def V7RatedFormEpsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (A₀ : ℝ) : Prop :=
    ∃ (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧ Cg ≤ 2 * 10 ^ 12 ∧ 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧
      (1 : ℝ) / (838400 * (c : ℝ)) ≤ δ₀ ∧
      Mfl ≤ flatDoorM A ∧ 0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        P R

/-- **⟦THE ZERO CALLER MEETS THE STRICT RIDER AT ANY FLOOR⟧** (`xceilRiderStrictAt_zero`) — the
landed `xceilRiderStrict_zero` (`V7Headline.lean:91`) on `XCeilRiderStrictAt lam0`, its four lines
unchanged: `log 0 = 0` and the gate's own width conjunct carry the margin.  Read twice in the
re-thread, at the `ε`-ceiling probe and at the exhibited caller. -/
theorem xceilRiderStrictAt_zero (lam0 : ℝ) (ε : ℚ) :
    XCeilRiderStrictAt lam0 ε (fun _ _ : ℕ => 0) := by
  intro Hhi ω hgate
  obtain ⟨-, -, hωw⟩ := hgate
  simp only [Nat.cast_zero, Real.log_zero]
  linarith [Real.log_natCast_nonneg ω]


/-! ### §W6.2 — ⟦THE HEAD AT GENERIC `ε`, NO CAP⟧ -/

/-- **⟦THE `A`-UNIFORM FLAT HEAD AT THE CHARGE⟧** (`flat_head_uniform_xceil_epsW`) —
`flat_head_uniform_xceil_eps` (`FlatDoorEpsChain.lean:552`) with its cap binder
`1/(500·8103) ≤ ε` replaced by the two-component charge `1 ≤ c` + `1/(500·c) ≤ ε`, and THREE
edits in the body, each measured at the object by the wave's edit-site census:

* the mint against the pin (`:605–610`): `1 ≤ 500·c·ε` gives `838400·c·ε ≥ 1676.8`, against the
  mint's own denominator `256·(1 + 8·log 2) ≤ 1675.5654262784` — the source's margin, now
  `1.2345737216` wide and free of `c`;
* the count hook (`:612`): §W2's `bigXi_bounded_ceiling_eps`, whose ceiling is `2^283·c^20`;
* the builder (`:627`): §W3.2's parametric-floor twin at `lam0 = 50 + log c`, whose new
  hypothesis `50 + log c ≤ 3.2·A` is paid by `10 + 2·log c ≤ A` and `26 ≤ A`
  (`50 + Lc ≤ 45 + A/2 ≤ 3.2·A`).

Everything else is the source's body token for token; the exported tuple gains ONE component
(`1 ≤ c`) and the `A`-quantifier ONE binder.  Nothing here bears on twin primes. -/
theorem flat_head_uniform_xceil_epsW (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
    {c : ℕ} (hc1 : 1 ≤ c) (hcε : (1 : ℚ) / (500 * (c : ℚ)) ≤ ε) (P : ChowlaRegime → Prop)
    (hP : ∀ R : ChowlaRegime, R.eps = ε →
      MRTUniformityXiL2 R ((ε : ℝ) / (256 * (1 + 4 * Real.log 4))) →
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) →
        MRTUniformityXiL2 R ρ → ¬ logChowla2Fails R.eps R.x R.ω) → P R) :
    FlatHeadFormEpsW ε c P := by
  classical
  unfold FlatHeadFormEpsW
  obtain ⟨cE, hcE, hcEge, H₀red, hred⟩ := hreduce_holds_final_bounded
  obtain ⟨cD3', hcD3', hcD3'ge, H₀D3, hD3'⟩ := primeWindow_sum_inv_ge_bounded
  obtain ⟨C', hC', hCcap, hcm'⟩ := circle_method_estimate_sq_bounded (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  -- ⟦THE LEAVES' WITNESSES, PINNED⟧ the door-head's device (`DoorReceipt.lean:1012–1021`)
  obtain ⟨cD3, hcD3def⟩ : ∃ c : ℝ, c = 1 / 4 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ c : ℝ, c = 1 + 2 * (2 * Real.log 4) := ⟨_, rfl⟩
  have hcD3 : 0 < cD3 := by rw [hcD3def]; norm_num
  have hcD3ge : 1 / 4 ≤ cD3 := by rw [hcD3def]
  have hC : 0 < C := by rw [hCdef]; positivity
  have hCnum : C ≤ 655 / 100 := by rw [hCdef, hlog4eq]; linarith
  have hCle : C' ≤ C := by rw [hCdef]; exact hCcap
  -- ⟦THE `ε` BOUNDS⟧ E1's recipe, read off `ε ≤ 1/500` instead of off the pin
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  have hεle : (ε : ℝ) ≤ 1 / 500 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε
    rwa [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := by
    have h : (1 : ℝ) / 500 ≤ cE / (32 * Real.log 4) := by
      rw [le_div_iff₀ (by positivity), hlog4eq]; linarith
    linarith
  have hε_half_lt : (ε : ℝ) < 1 / 2 := by linarith
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := by
    have h : (1 : ℝ) / 500 ≤ cD3 / 16 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]; linarith
    linarith
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := by
    have h : (1 : ℝ) / 500 ≤ cD3 / (16 * C) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
    linarith
  have hεQ1 : ε ≤ 1 / 2 := by
    have h2 : (1 : ℚ) / 500 ≤ 1 / 2 := by norm_num
    linarith
  -- ⟦THE MINT⟧ the head's `δ₀` at the pinned witnesses IS the frozen file's term, exactly
  have hmint : cD3 / (16 * C) * (ε : ℝ) / 4 = (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) := by
    rw [hcD3def, hCdef]
    have hne : (1 : ℝ) + 2 * (2 * Real.log 4) ≠ 0 := by positivity
    field_simp
    ring
  -- ⟦THE MINT AGAINST THE PIN, AT THE CHARGE⟧ the source's `hqcap`/`hcapR`/`hδnum` at `c`
  -- in place of `8103`: `1 ≤ 500·c·ε` gives `838400·c·ε ≥ 1676.8`, and the mint's own
  -- denominator is `256·(1 + 8·log 2) ≤ 256 · 6.5451774464 = 1675.5654262784` — the source's
  -- own margin, now `1.2345737216` wide and INDEPENDENT of `c`.
  have hcQ : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcQ0 : (0 : ℚ) < 500 * (c : ℚ) := by linarith
  have hqcap : (1 : ℚ) ≤ 500 * (c : ℚ) * ε := by
    rw [div_le_iff₀ hcQ0] at hcε; linarith
  have hcapR : (1 : ℝ) ≤ 500 * (c : ℝ) * (ε : ℝ) := by exact_mod_cast hqcap
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hδnum : (1 : ℝ) / (838400 * (c : ℝ)) ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    rw [hmint, div_le_div_iff₀ (by linarith) (by positivity), hlog4eq]
    linarith
  -- ⟦THE COUNT HOOK AT THE CAP⟧ §2, in place of the pinned hook
  obtain ⟨K, hK, hKb, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded_ceiling_eps ε hε0 hε hc1 hcε
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = cD3 * (ε : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hcD3 hεR0) (by positivity)
  -- ⟦THE HEAD'S OWN FOUR-ARM FLOOR⟧ (flat) — `A`-FREE, which is the whole point
  obtain ⟨Hopq, hOpqdef⟩ : ∃ n : ℕ, n = max (max H₀red H₀D3) H₀xi := ⟨_, rfl⟩
  refine ⟨K, cD3 / (16 * C) * (ε : ℝ) / 4, β, Hopq, hε0, hK, hKb,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num),
    hc1, hcε, hδnum, hβpos, ?_⟩
  -- ⟦THE HOIST⟧ the landed proof chose `A := max A₀ (budgetAFlat ε β)` HERE
  intro A hA26 hAge hAL
  -- ⟦THE TOWER FLOOR THE NINTH ARM PAYS⟧ `50 + Lc ≤ 45 + A/2 ≤ 3.2·A` at `A ≥ 26`
  have hlamA : 50 + Real.log (c : ℝ) ≤ 3.2 * A := by linarith
  obtain ⟨F, hFdef⟩ : ∃ n : ℕ, n = max Hopq (budgetFloorFlat (ε : ℝ) β A) := ⟨_, rfl⟩
  refine ⟨max (flatDesignFloor A) (max F (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), by rw [hFdef], ?_⟩
  intro extraFloor U1floor g₅ hg₅
  obtain ⟨Rf, hReps, hRA, hRHlo, hRg, _hRcapEq, hRwid, hRx⟩ :=
    chowlaRegimeFlat_exists_param_head_xceil_at (50 + Real.log (c : ℝ)) A hA26 hlamA ε hε0 hεQ1
      (max F (max extraFloor U1floor)) g₅ hg₅
  have hFlo : F ≤ Rf.Hlo := le_trans (le_max_left _ _) hRHlo
  have hxiHlo : H₀xi ≤ Rf.Hlo := by
    rw [hFdef, hOpqdef] at hFlo
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hFlo
  have hbudHlo : budgetFloorFlat (ε : ℝ) β A ≤ Rf.Hlo := by
    rw [hFdef] at hFlo; exact le_trans (le_max_right _ _) hFlo
  have hredHlo : max H₀red H₀D3 ≤ Rf.Hlo := by
    rw [hFdef, hOpqdef] at hFlo
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hFlo
  refine ⟨Rf.toChowlaRegime, hReps,
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, hRx, ?_,
    fun _ => hRwid, ?_, ?_⟩
  · -- ⟦THE EXPORTED COUNT GATE⟧ the road's `hXi`, at this head's own `ε`
    intro H' _ hlo' _
    rw [hReps]
    exact hxi H' (le_trans hxiHlo hlo')
  · -- ⟦THE CAP⟧ the flat base equation, shuffled onto the consumer's floors
    rw [_hRcapEq]
    exact uniformCap_shuffle _ _ _ _ _
  -- ⟦THE SLOT⟧ `P R` from the door AT THE MINT and the tail AT THE MINT
  intro ρ _hρpos hρ hdoor
  refine hP Rf.toChowlaRegime hReps
    (mrtUniformityXiL2_mono (le_trans hρ hmint.le) hdoor) ?_
  intro ρ' _hρ'pos hρ'le hdoor' hfail
  have hρ4 : ρ' ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by rw [hmint]; exact hρ'le
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrementFlat Rf
  have hH4 : 4000000 ≤ H := le_trans Rf.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow Rf.eps H : liouvilleWindow H ; logMeasure Rf.x Rf.ω]
      ≤ (H : ℝ) / (Rf.A * Real.log H) := by
    rw [mutualInfo_window_comm_flat]; exact hMI
  have hepsc : (Rf.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max H₀red H₀D3 ≤ H := le_trans hredHlo hlo
  have hβR : cD3 * (Rf.eps : ℝ) / (144 * Real.log 4) = β := by rw [hReps, hβdef]
  have hAgeR : budgetAFlat (Rf.eps : ℝ) (cD3 * (Rf.eps : ℝ) / (144 * Real.log 4)) ≤ Rf.A := by
    rw [hβR, hReps, hRA]; exact hAge
  have hfloorH : budgetFloorFlat (Rf.eps : ℝ)
      (cD3 * (Rf.eps : ℝ) / (144 * Real.log 4)) Rf.A ≤ H := by
    rw [hβR, hReps, hRA]
    exact le_trans hbudHlo hlo
  obtain ⟨t, g, ht, hg, hgle, hbudget1⟩ :=
    hbudget1_witnessFlat Rf H cD3 C hcD3 hC
      (by rw [hReps]; exact le_of_lt hε_half_lt)
      (by rw [hReps]; exact hε_D3)
      (by rw [hReps]; exact hε_D3C) hhi hAgeR hfloorH
  -- ⟦THE K-FREE hbudget2⟧ `ρ ≤ c₀ε/4 < c₀ε`
  have hbudget2 : ρ' < cD3 / (16 * C) * (Rf.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hρ4, hpos]
  -- ⟦THE CORE⟧ at the FLAT threshold `κ = H/(A·log H)`, with the two transports supplied here
  refine spine_False_core_xi_sq_uniform Rf.toChowlaRegime hdoor' cE hcE H₀red hred cD3 hcD3
    H₀D3 ?_ C hC ?_ H hlo hhi hH₀ hepsc t g
    ((H : ℝ) / (Rf.A * Real.log H)) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail
  · -- ⟦TRANSPORT 1⟧ the `D3` FLOOR moves DOWN to the pinned `1/4`
    intro eps H' hH0 hsq h1
    refine le_trans ?_ (hD3' eps H' hH0 hsq h1)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by rw [hcD3def]; exact hcD3'ge)
      (inv_nonneg.mpr (Real.log_natCast_nonneg H'))
  · -- ⟦TRANSPORT 2⟧ the circle-method GRADE moves UP to the pinned `1 + 2·(2·log 4)`
    intro eps H' _ x1 hx1 hcard
    refine le_trans (hcm' eps H' x1 hx1 hcard) ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle ?_) ?_
    · rw [div_eq_mul_inv]
      exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (Real.log_natCast_nonneg _))
    · positivity

/-! ### §W6.3 — ⟦THE FOUR PASS-THROUGH HOPS⟧ socket · doorL2 · road · capstone

Rung 1's census promised FIVE pure pass-through replays; this wave's re-census, taken at the
object with a `clear`-probe on each hop's body (and a mutation control that goes red), found
FOUR.  The conditional, the terminal and the rated hop each spend the charge at a named site and
are re-threaded one section down.  In these four the charge is PASSED THROUGH: each `obtain` and
each `refine` tuple gains ONE component (`1 ≤ c`), each `A`-quantifier application gains ONE
argument (`hAL`), and no other token moves.  Nothing here bears on twin primes. -/

/-- **⟦flat_socket_generic, AT THE CHARGE⟧** (`flat_socket_generic_epsW`) — the source's body
(`FlatDoorEpsChain.lean:713`) with `hc1` threaded through the tuple and `hAL` through the
`A`-application.  No cap is read here; the `clear`-probe confirms it. -/
theorem flat_socket_generic_epsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatHeadFormEpsW ε c P) :
    FlatSocketFormEpsW ε c P := by
  unfold FlatSocketFormEpsW
  obtain ⟨K, δ₀, β, Hopq, hε, hK, hKb, hδ₀, hc1, hεpin, hδpin, hβ, hhead⟩ :=
    h
  obtain ⟨H₀, hH₀⟩ := sum_bigXi_norm_windowExpSum_sq_le_twelve ε hε
  refine ⟨K, δ₀, β, max Hopq H₀, hε, hK, hKb, hδ₀, hc1, hεpin, hδpin, hβ, ?_⟩
  intro A hA162 hAge hAL
  obtain ⟨Hcap, hCapEq, hhd⟩ := hhead A (by linarith) hAge hAL
  refine ⟨max Hcap H₀, by rw [hCapEq]; exact uniformCap_arc _ _ _ _ _, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, _, hRU1, hRg, hRx, hcount, hRtow, hRcap, hR⟩ :=
    hhd 0 (max U1floor H₀) g hg
  have hU1 : U1floor ≤ R.Hlo := le_trans (le_max_left _ _) hRU1
  have harc : H₀ ≤ R.Hlo := le_trans (le_max_right _ _) hRU1
  refine ⟨R, hReps, hU1, hRg, hRx, hRtow, le_trans hRcap (by omega), ?_⟩
  intro a e Bsieve Binsert hsplit hB0 hsock hins hρ
  refine hR δ₀ hδ₀ le_rfl ?_
  intro H _ hlo hhi
  exact le_trans (hH₀ R hReps harc a e Bsieve K Binsert hsplit hB0 hsock hcount hins
    H hlo hhi) (hρ H hlo hhi)

/-- **⟦flat_doorL2_generic, AT THE CHARGE⟧** (`flat_doorL2_generic_epsW`) — the source's body
(`:738`), same two threadings.  `hKb` (the count's POSITIVITY) is read at the budget line and is
unchanged; the count CEILING `hKbb` is only passed on. -/
theorem flat_doorL2_generic_epsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatSocketFormEpsW ε c P) :
    FlatDoorL2FormEpsW ε c P := by
  unfold FlatDoorL2FormEpsW
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  obtain ⟨Kb, δ₀, β, Hopq, hε, hKb, hKbb, hδ₀, hc1, hεpin, hδpin, hβ, hsk⟩ :=
    h
  refine ⟨Cg, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hc1, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge hAL
  obtain ⟨Hcap, hCapLe, hexit⟩ := hsk A hA162 hAge hAL
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hR⟩ := hexit U1floor g hg
  refine ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, ?_⟩
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  have hA : 1 ≤ AdoorL M := one_le_AdoorL hgates.hM
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
    intro H hhi
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  refine hR (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2
      liouvilleC)
    (fun m => lamCoeff m - memSCoeff (calP (AdoorL M) (s13GK K M))
      (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC m)
    Braw (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) (fun m => by ring) hBraw0
    (hsock m4_bandTransport) ?_ ?_
  · intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (AdoorL M) (s13GK K M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · intro H hlo hhi
    rw [l2_budget_line Kb (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * Kb * Braw H ≤ 2 * Kb * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

/-- **⟦flat_road_generic, AT THE CHARGE⟧** (`flat_road_generic_epsW`) — the source's body
(`:783`), same two threadings. -/
theorem flat_road_generic_epsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatDoorL2FormEpsW ε c P) :
    FlatRoadFormEpsW ε c P := by
  unfold FlatRoadFormEpsW
  obtain ⟨Cg, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hc1, hεpin, hδpin, hβ, hdoor⟩ :=
    h
  refine ⟨Cg, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hc1, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge hAL
  obtain ⟨Hcap, hCapLe, hmain⟩ := hdoor K A hA162 hAge hAL
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hR⟩ := hmain U1floor g hg
  refine ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
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
  have hchi : M4ChiSummedBlockMeanSqN_L_gk K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied_L_gk K j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummed_L_gk K (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  have hcov := m4_cover_assembly_blk2_L_gk K hgates hBblk0 hblk2
  refine hR Braw Bceil δ M k hgates hBraw0 ?_ hceil hbudget
  refine m4_sievedDoorSq_of_blk2_L_gk K (ℓ := blockLen)
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

/-- **⟦flat_capstone_generic, AT THE CHARGE⟧** (`flat_capstone_generic_epsW`) — the source's
body (`:845`), same two threadings.  `hKc` (positivity) is read by the socket's `δ`-share and is
unchanged; the ceiling `hKcb` is only passed on. -/
theorem flat_capstone_generic_epsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatRoadFormEpsW ε c P) (Awin : ℝ) (hband : S16BandLaneCBoundedL_winU Awin) :
    FlatCapstoneFormEpsW ε c P Awin := by
  unfold FlatCapstoneFormEpsW
  obtain ⟨Cg, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hKcb, hδ₀, hc1, hεpin, hδpin, hβ, hroadU⟩ :=
    h
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  refine ⟨Cg, Kc, δ₀, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, s11GradeFloor_one_le _, hCgle,
    hc1, hεpin, hδpin, hKcb,
    (fun A hA162 hAw => flatDoorM_gradeFloor_win hA162 hCband0 (by linarith)),
    hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_L_gk_ceiling_kwide K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge hAL
  obtain ⟨Hcap, hCapLe, hroad⟩ := hroadU K A hA26 hAge hAL
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g hg
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRx, hRtow, by omega, ?_⟩
  intro M hMfloor hKw
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit K M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_L_gk K R M
      (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho_L M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
    have hKcpos : (0 : ℝ) < 16 * Kc := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

/-! ### §W6.4 — ⟦THE CONDITIONAL HOP ON THE GENERIC GATE⟧ -/

/-- **⟦flat_conditional_generic, AT THE CHARGE⟧** (`flat_conditional_generic_epsW`) — the
source's body (`FlatDoorEpsChain.lean:993`) with the two threadings and TWO edits:

* **the rider block** (`:1014–1041`, 28 lines): rung 1 priced the substituted arm
  `g' = s15Arm δ₀ ρ + g` inline — `log 8103 ≤ 9`, `s15Arm_log_le_scaled` at `c := 8103`, the
  sum split by `epsChain_arm_split_cap`, `xt_log_add_le`.  §W3.3's `xCeilRiderAt_arm_add` is that
  whole block as ONE lemma at a generic count, so the hop is now ONE call.  The count ceiling
  enters through its LOG alone (`epsRung2_log_Kb_le`), never as a numeral — and the call needs no
  `rw [hρdef, hδsdef]`, because `set` leaves `ρ` and `δs` definitionally where the lemma wants
  them;
* **the six selector reads** (`:1083–1108`): the form now carries `S15Sel''_L_gk_T`, the
  tower-relative register (§W1c), so `hsel.head` is unchanged (dot notation finds the sibling's
  own `head`) and the other five readers become their `_T` twins with argument lists identical.
  Every other projection — `.hM`, `.mfloor`, `.bfloor`, `.gRows`, `.half`, `.anchor`, `.gP1`,
  `.lvl`, `.blk`, `.rho` — keeps its name.

Nothing here bears on twin primes. -/
theorem flat_conditional_generic_epsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ)
    (h : FlatCapstoneFormEpsW ε c P Awin) :
    FlatConditionalFormEpsW ε c P Awin := by
  unfold FlatConditionalFormEpsW
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hCg, hε, hKc, hδ₀, hMfl,
    hCgle, hc1, hεpin, hδpin, hKcb, hMflb, hβ, hcapU⟩ :=
    h
  refine ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl,
    hCgle, hc1, hεpin, hδpin, hKcb, hMflb, hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcapK⟩ := hcapU K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge hAL
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapK A hA26 hAge hAL
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦THE ONE GENUINE ESTIMATE, SPENT⟧ the substituted `g' = s15Arm δ₀ ρ + g` still obeys the
  -- builder-side rider.  THE ONE EDIT ON THIS HOP, at the charge: rung 1 priced the arm inline by
  -- `s15Arm_log_le_scaled` at `c := 8103` and paid the sum split's `log 2` by
  -- `epsChain_arm_split_cap`; §W3.3's `xCeilRiderAt_arm_add` is that whole block as ONE lemma at a
  -- generic count, so the hop reads it in one call.  The count ceiling enters only through its
  -- LOG (`epsRung2_log_Kb_le`), never as a numeral.
  have hLc0 : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast hc1)
  have hg' : XCeilRiderAt (50 + Real.log (c : ℝ)) ε
      (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω) :=
    xCeilRiderAt_arm_add hc1 hεpin hLc0 le_rfl hδ₀ hδpin hKc
      (epsRung2_one_le_Kb hc1) hKcb (epsRung2_log_Kb_le hc1) hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω) hg'
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRx, hRtow, ?_⟩
  intro M hsel hKw
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor hKw
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the LINEAR anchor
  have harith := s15_doorArithFrameRho_L_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register⟧
  have hgate : S13BandGate'_L_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_L_gk_T K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_gen le_rfl (s13_g2_jfloor_of_MSelect'_L_gk K (by linarith) hS))
    (s13_gate8_L_gk le_rfl (s13_gate8_of_MSelect'_L_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_L_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket_L hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorL_gk_T K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat_T hfl (socketBase_of_socketBaseL hsel.hM hb) hlam50 htow
        hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flat_T hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flat_T hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM (hgate.block H L q j A s hb)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_L_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith

/-! ### §W6.5 — ⟦THE TERMINAL HOP AT THE CHARGE⟧ -/

/-- **⟦flat_kswin_generic, AT THE CHARGE⟧** (`flat_kswin_generic_epsW`) — the source's body
(`FlatDoorEpsChain.lean:1121`), the two threadings, and the EIGHT sites where rung 1 spent the
cap, each at the charge:

* `:1132–1134` **the `ε`-ceiling probe's OWN design constant** — the one place in the whole
  chain, besides the ninth arm, where an `A` is MINTED rather than passed down.  Rung 1 read one
  regime's `heps1` at `max 162 (budgetAFlat ε β)`; at the charge the form's third `A`-binder is
  `10 + 2·Lc ≤ A`, which that `max` does not pay — it would need `Lc ≤ 76`, a numeral cap on `c`.
  The arm is re-minted at `162 + 2·Lc`, which pays all three binders at `0 ≤ Lc`;
* `:1135–1139` the zero rider → §W6.1's `xceilRiderStrictAt_zero`;
* `:1149–1158` the cap's two spellings → ONE cast: the RATIONAL spelling the `_b9` twins needed a
  second cast for IS the form's own `hεpin` now, at `c`;
* `:1167` and `:1175` `flat_witFloor_eq_designBase_L` (§3), twice;
* `:1183–1186` `1/(2^9·c) ≤ 1/(500·c) ≤ ε`, at `500 ≤ 512 = 2^9`;
* `:1191–1195` `1/(838400·2^12·c²) ≤ 1/(838400·c)`, at `c ≤ 4096·c²` for `c ≥ 1`;
* `:1196–1198` the bumped witness → §W1c(b)'s `_L` sibling at `h := c`, `Lc := log c`,
  `hhL := le_rfl`, whose count binders are `epsRung2_one_le_Kb`, the form's ceiling and
  `epsRung2_log_Kb_le`.

Nothing here bears on twin primes. -/
theorem flat_kswin_generic_epsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ)
    (h : FlatConditionalFormEpsW ε c P Awin) :
    FlatKswinFormEpsW ε c P Awin := by
  unfold FlatKswinFormEpsW
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hc1, hεpin, hδpin, hKcb, hMflb, hβ, hcondU⟩ :=
    h
  -- ⟦THE CROSSING CONSTANTS, HOISTED ABOVE THE LEVER⟧ — §4's windowed twin
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40,
    hsupplyU⟩ := s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  have hc0 : 0 < c := by omega
  have hLc0 : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast hc1)
  obtain ⟨_Ct0, -, -, hcond0⟩ := hcondU 0
  -- ⛔ THE ONE MINTED `A` OUTSIDE THE NINTH ARM.  Rung 1 read one regime's `heps1` at
  -- `max 162 (budgetAFlat ε β)`; at the charge the form's third `A`-binder is
  -- `10 + 2·Lc ≤ A`, which that `max` does NOT pay (it would need `Lc ≤ 76`, i.e. a numeral
  -- cap on `c`).  The arm is re-minted at `162 + 2·Lc`, which pays all three at `0 ≤ Lc`.
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond0 (max (162 + 2 * Real.log (c : ℝ)) (budgetAFlat (ε : ℝ) β))
      (le_trans (by linarith) (le_max_left _ _)) (le_max_right _ _)
      (le_trans (by linarith) (le_max_left _ _))
  have hzero : XCeilRiderStrictAt (50 + Real.log (c : ℝ)) ε (fun _ _ : ℕ => 0) :=
    xceilRiderStrictAt_zero _ ε
  obtain ⟨R0, hR0eps, -, -, -, -, -⟩ :=
    hbody0 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) hzero le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  -- ⟦THE CHARGE, IN THE REAL SPELLING⟧ the `_L` siblings take the pin over `ℝ`; the RATIONAL
  -- spelling the `_b9` twins needed a second cast for is now the form's own `hεpin`, at `c`.
  have hcQ1 : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hεR : (1 : ℝ) / (500 * (c : ℝ)) ≤ (ε : ℝ) := by
    have hq := hεpin
    rw [div_le_iff₀ (by linarith)] at hq
    have h1R : (1 : ℝ) ≤ (ε : ℝ) * (500 * (c : ℝ)) := by exact_mod_cast hq
    rw [div_le_iff₀ (by linarith)]
    linarith
  refine ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hc1, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  have hsupply := hsupplyU K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA26 hAwin hAge hAL hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge hAL
  refine ⟨fun hopq => flat_witFloor_eq_designBase_L (h := c) hc0 hLc0 le_rfl hA26 hAL hβ
    hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hx0win hopq hT₀ hKsw g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g hg (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase_L (h := c) hc0 hLc0 le_rfl hA26 hAL hβ
      hεR hε2 hε hεpin hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  -- `1/(2^9·c) ≤ 1/(500·c) ≤ ε`, the source's step at the charge: `500 ≤ 512 = 2^9`
  have heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps := by
    rw [hReps]
    have h512 : (500 : ℚ) * (c : ℚ) ≤ 2 ^ 9 * (c : ℚ) := by
      have h9 : (2 : ℚ) ^ 9 = 512 := by norm_num
      rw [h9]; linarith
    have hb : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ 1 / (500 * (c : ℚ)) :=
      one_div_le_one_div_of_le (by linarith) h512
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  -- ⟦THE BRIDGE⟧ the `A`-scoped window becomes §4's regime-scoped one at the flat floor
  have hKswR : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16 := by linarith
  -- `1/(838400·2^12·c²) ≤ 1/(838400·c)`: `c ≤ 4096·c²` at `c ≥ 1`
  have hδb : (1 : ℝ) / (838400 * 2 ^ 12 * (c : ℝ) ^ 2) ≤ δ₀ := by
    refine le_trans ?_ hδpin
    have hden : (838400 : ℝ) * (c : ℝ) ≤ 838400 * 2 ^ 12 * (c : ℝ) ^ 2 := by
      have h12 : (2 : ℝ) ^ (12 : ℕ) = 4096 := by norm_num
      rw [h12]; nlinarith
    exact one_div_le_one_div_of_le (by linarith) hden
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win_L hA26 K hKw (h := c) hc0 hLc0 le_rfl hAL
    hδ₀ hδb hKc (epsRung2_one_le_Kb hc1) hKcb (epsRung2_log_Kb_le hc1)
    hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win heps hlo hwin
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk K (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel hKw
    (hsupply hKqb R (flatDoorM A) hM1 hfl hKswR (by rw [hHlo]; exact hT₀) hblk hcof hcapsc)

/-! ### §W6.6 — ⟦THE NINTH ARM AND THE RATED HOP⟧

The design constant `A` is minted in exactly one place on the road (`FlatDoorEpsChain.lean:1228`),
as a `max` of eight arms.  This is where the whole charge is paid: a NINTH arm `162 + 2·Lc`, put
OUTERMOST, with the source's eight verbatim inside it.  It is a `max`, so it costs nothing anyone
downstream can see — every consumer reads `A` through an inequality — and it pays five demands:

```
  162 ≤ A                        everything            via `hlift`, as the source
  10 + 2·Lc ≤ A                  the forms' binder     162 + 2·Lc ≥ 10 + 2·Lc
  518 + 6·Lc ≤ loglog H₋         the rated root        3.2·(162 + 2·Lc) = 518.4 + 6.4·Lc
  cofkRThr + 2·Lc ≤ log H₋       the rated root        cofkRThr ≤ A, 2·Lc ≤ A, 2·A ≤ 3.2·A + 1
  Lc ≤ e^(1.6·A)                 the base-scale cap    Lc ≤ A ≤ 1.6·A + 1 ≤ e^(1.6·A)
```

⛔ `10 + 2·Lc ≤ A` does NOT pay the third: `3.2·(10 + 2·Lc) = 32 + 6.4·Lc` is short of `518`.
That is the whole reason the arm is `162 + 2·Lc`. -/

/-- **⟦flat_v7_generic, AT THE CHARGE⟧** (`flat_v7_generic_epsW`) — the source's body (`:1211`)
with the ninth arm, three `_L` suppliers in place of their `_b9` twins
(`cofkR_cofactorSupply_L_gk_rated_L`, `s16_baseScaleCap96_LH_at_klevF_L`, and the zero rider),
the two `ε`-numeral casts at `c`, and the source's `le_max` chains each gaining ONE
`le_trans … (le_max_right _ _)` for the new outer arm.

ONE REORDERING: the rated supply's `obtain` moves BELOW the terminal's, because the charge
`1 ≤ c` is a component of the form and the supply now reads it.  Every constant is still minted
before the lever — `Kvt` still arrives before `A` is chosen, which is what that ordering was for.
Nothing here bears on twin primes. -/
theorem flat_v7_generic_epsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : ∀ Awin : ℝ, S16BandLaneCBoundedL_winU Awin → FlatKswinFormEpsW ε c P Awin)
    (A₀ : ℝ) :
    V7RatedFormEpsW ε c P A₀ := by
  unfold V7RatedFormEpsW
  obtain ⟨Awin, -, hband⟩ := s16_bandLaneWinL_holdsU
  -- ⟦THE cs-FREE, Ks-WINDOWED FLAT TERMINAL⟧ V7Ks §5
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hc1, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ :=
    h Awin hband
  have hc0 : 0 < c := by omega
  have hLc0 : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast hc1)
  -- ⟦THE RATED CO-FACTOR SUPPLY⟧ four Skolem REALS, still minted BEFORE the lever; the obtain
  -- moves below the terminal's only because the charge `1 ≤ c` is a component of the form.
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ :=
    cofkR_cofactorSupply_L_gk_rated_L c hc0 hLc0 le_rfl
  -- ⟦THE DESIGN CONSTANT, EIGHT ARMS⟧ the seven landed arms verbatim (`A'`), the eighth
  -- (`armVt Kvt`) outermost — every constant still minted BEFORE the lever: `Kvt` arrives at
  -- the supply obtain above, before the mint.
  obtain ⟨A', hA'def⟩ : ∃ a : ℝ, a = max (16 * Real.log (1 / Ks) / 3) (max T₀
      (max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
        (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))))) := ⟨_, rfl⟩
  -- ⟦THE NINTH ARM⟧ `162 + 2·Lc`, OUTERMOST, the source's eight verbatim inside it.  It is the
  -- only place the charge is spent on the design constant, and it pays five demands at once:
  -- `162 ≤ A` (via `hlift`, as the source), `10 + 2·Lc ≤ A` (the forms' new binder),
  -- `518 + 6·Lc ≤ loglog H₋` (3.2·(162 + 2·Lc) = 518.4 + 6.4·Lc), `cofkRThr + 2·Lc ≤ log H₋`
  -- and `Lc ≤ e^(1.6·A)`.  ⛔ `10 + 2·Lc ≤ A` does NOT pay the third, which is why the arm is
  -- `162 + 2·Lc` and not `10 + 2·Lc`.
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (162 + 2 * Real.log (c : ℝ)) (max (armVt Kvt) A') :=
    ⟨_, rfl⟩
  have hA162b : 162 + 2 * Real.log (c : ℝ) ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hAL : 10 + 2 * Real.log (c : ℝ) ≤ A := by linarith
  have harmA : armVt Kvt ≤ A := by
    rw [hAdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hlift : A' ≤ A := by
    rw [hAdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hKsA : 16 * Real.log (1 / Ks) / 3 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]; exact le_max_left _ _
  have hT₀A : T₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hA162 : (162 : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hA₀A : A₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAwinA : Awin ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_right (max (max A₀ 162) Awin)
      (cofkRThr Cq Cb Xsk Y0)) (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _)
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  -- ⟦THE `Ks` WINDOW, AT THE SEVENTH ARM⟧ as in the parent
  have hKswin : Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 := by linarith
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
    have h2 : Real.exp (3.2 * A) / 10 + 1 ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
      Real.add_one_le_exp _
    linarith
  have hopq : Hopq ≤ flatDesignBase A := by
    have h2 : Real.exp (3.2 * A) + 1 ≤ Real.exp (Real.exp (3.2 * A)) := Real.add_one_le_exp _
    have hR : ((Hopq : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by linarith
    have hceil := le_trans hR (Nat.le_ceil (Real.exp (Real.exp (3.2 * A))))
    rw [flatDesignBase]; exact_mod_cast hceil
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, hCt, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hAL hKw
  -- ⟦THE `T₀` ARM⟧ V7-C's discharge, as in the parent
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  -- ⟦THE EXHIBITED CALLER⟧ `g ≡ 0` meets the strict rider; the `g`-conjunct is discarded
  obtain ⟨R, hReps, hHlo, -, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKswin (fun _ _ : ℕ => 0)
      (xceilRiderStrictAt_zero _ ε)
  -- ⟦THE BASE-SCALE CAP⟧ at `K = KlevF A`, as in the parent
  have heps500 : (1 : ℚ) / (500 * (c : ℚ)) ≤ R.eps := by
    rw [hReps]; exact hεpin
  have hxceil : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [hReps]; exact hRx
  -- ⟦THE RATED SUPPLY, WITH THE CUSHION PAID BY THE EIGHTH ARM⟧
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA26
  have hcQ1 : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have heps500R : (1 : ℝ) / (500 * (c : ℝ)) ≤ (R.eps : ℝ) := by
    rw [hReps]
    have hq := hεpin
    rw [div_le_iff₀ (by linarith)] at hq
    have h1R : (1 : ℝ) ≤ (ε : ℝ) * (500 * (c : ℝ)) := by exact_mod_cast hq
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- ⟦THE NINTH ARM, FIRST READER⟧ `3.2·(162 + 2·Lc) = 518.4 + 6.4·Lc ≥ 518 + 6·Lc` at `0 ≤ Lc`
  have h518 : (518 : ℝ) + 6 * Real.log (c : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    linarith [hdes, hA162b, hLc0]
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA162
  -- ⟦THE NINTH ARM, SECOND READER⟧ `cofkRThr ≤ A`, `2·Lc ≤ A`, `2·A ≤ 3.2·A + 1 ≤ e^(3.2A)`
  have hthrgate : cofkRThr Cq Cb Xsk Y0 + 2 * Real.log (c : ℝ)
      ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    linarith [hthrA, hlo, hexp1, hAL, hA162]
  have hKvtcush : 32 * Kvt
      + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
      ≤ Real.log (R.Hhi : ℝ) / 4 :=
    cofkR_cushion_of_armVt R hKvt0 harmA hlo
  -- ⟦THE NINTH ARM, THIRD READER⟧ `Lc ≤ A ≤ 1.6·A + 1 ≤ e^(1.6·A)`
  have hexp16 : 3.2 * A / 2 + 1 ≤ Real.exp (3.2 * A / 2) := Real.add_one_le_exp _
  have hLt : Real.log (c : ℝ) ≤ Real.exp (3.2 * A / 2) := by linarith
  have hcofsupply : S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) :=
    s16CofactorSupply_L_of_LH hc0
      (hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush)
  have hfireR : P R :=
    hfire2 hcofsupply
      (s16BaseScaleCap96_L_of_LH hc0
        (s16_baseScaleCap96_LH_at_klevF_L (h := c) hc0 hLc0 le_rfl
          hA26 hLt (flatDoorM_one_le hA26) heps500 hxceil hwin))
  exact ⟨Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hc1, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A,
    R, hReps, by rw [hHlo]; exact hbase hopq, hRtow, hdes, hwin, hfireR⟩

/-! ### §W6.7 — ⟦THE CHAIN AND THE THEOREM⟧ -/

/-- **⟦THE CHAIN, AT THE CHARGE⟧** (`flat_chain_generic_epsW`) — `flat_chain_generic_eps`
(`FlatDoorEpsChain.lean:1340`) with every hop's `W` sibling and `c` threaded beside `ε`.  The
charge and the `δ₀` pin travel INSIDE the forms, so no hop takes either as a hypothesis and this
composition is the landed one token for token. -/
theorem flat_chain_generic_epsW (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatHeadFormEpsW ε c P) (A₀ : ℝ) : V7RatedFormEpsW ε c P A₀ :=
  flat_v7_generic_epsW ε c P (fun Awin hband => flat_kswin_generic_epsW ε c P Awin
    (flat_conditional_generic_epsW ε c P Awin
      (flat_capstone_generic_epsW ε c P
        (flat_road_generic_epsW ε c P
          (flat_doorL2_generic_epsW ε c P (flat_socket_generic_epsW ε c P h))) Awin hband))) A₀

/-- **⟦W-ε — THE SECOND RUNG, AND THE END OF THE LADDER⟧** (`flatDoorEpsFamilyW_holds`) — the
frozen file's named `Prop` `FlatDoorEpsFamilyW`, INHABITED: the flat door at the head's grade for
EVERY `0 < ε ≤ 1/500`, with no cap and no numeral on `ε`.

THE CHARGE IS CHOSEN, NOT ASSUMED.  `c := ⌈1/(500·ε)⌉₊`, so `1 ≤ c` (the ceiling of a positive
rational is positive) and `1/(500·c) ≤ ε` (`Nat.le_ceil` gives `1/(500·ε) ≤ c`, hence
`1 ≤ 500·ε·c`).  That is the whole of what rung 1 had to ASSUME.  Every numeral rung 1 read off
`c = 8103` is read off this `c` instead, and the one place a numeral could have re-entered — the
design constant — takes a ninth `max`-arm affine in `log c` (§W6.6).

The proof is the frozen file's capped proof (`FlatDoorEpsFamily.lean:155–180`) token for token
with `flat_chain_generic_eps` replaced by `flat_chain_generic_epsW ε c` and the payload `P`
written out as that proof writes it; the unpack gains ONE `-` for the charge component.

⇒ The frozen file's `mrtUniformityXiL2_holds_flat_epsFamily_capped_of_epsFamily` discharges rung
1 from this, and C3 · E2′ · E2″ · C4 become unconditional IN USE by supplying this theorem to
their `hW` binder — their statements are untouched, and the frozen file is not edited.
Nothing here bears on twin primes. -/
theorem flatDoorEpsFamilyW_holds : FlatDoorEpsFamilyW := by
  unfold FlatDoorEpsFamilyW
  intro ε hε0 hε A₀
  have hε0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  obtain ⟨c, hcdef⟩ : ∃ n : ℕ, n = ⌈(1 / (500 * ε) : ℚ)⌉₊ := ⟨_, rfl⟩
  have hεQ0 : (0 : ℚ) < 500 * ε := by linarith
  have hc1 : 1 ≤ c := by
    have h : 0 < c := by
      rw [hcdef]; exact Nat.ceil_pos.mpr (div_pos one_pos hεQ0)
    omega
  have hcQ1 : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcQ0 : (0 : ℚ) < 500 * (c : ℚ) := by linarith
  have hcε : (1 : ℚ) / (500 * (c : ℚ)) ≤ ε := by
    have hle : (1 : ℚ) / (500 * ε) ≤ (c : ℚ) := by rw [hcdef]; exact Nat.le_ceil _
    rw [div_le_iff₀ hεQ0] at hle
    rw [div_le_iff₀ hcQ0]
    linarith
  have hV := flat_chain_generic_epsW ε c
    (fun R : ChowlaRegime => MRTUniformityXiL2 R ((ε : ℝ) / (256 * (1 + 4 * Real.log 4))) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) →
        MRTUniformityXiL2 R ρ → ¬ logChowla2Fails R.eps R.x R.ω)
    (flat_head_uniform_xceil_epsW ε hε0 hε hc1 hcε _ (fun _ _ hd hs => ⟨hd, hs⟩)) A₀
  obtain ⟨Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hA162, hA₀A, R, hReps, hHlo, -, hdes, -, hdoor, hslot⟩ := hV
  exact ⟨(ε : ℝ) / (256 * (1 + 4 * Real.log 4)), A, by positivity, le_rfl,
    flatDoorMint_floor_le_grade (ε : ℝ) hε0R.le, hA162, hA₀A, R, hReps, hHlo, hdes,
    hdoor, hslot⟩

/-! ### §W6.8 — ⟦THE COMPOSITION, EXHIBITED⟧ (2026-09-17, the second outside read's finding 1)

Until this section NO landed declaration APPLIED `flatDoorEpsFamilyW_holds`: «unconditional IN
USE» named a composition that had been run only in scratch (by the author at the harvest, and by
the outside reader, each at the three axioms).  The two theorems below LAND it for the two
consumers whose applied statement is NEW — E2′ and its `_floor` twin — by supplying the theorem
to their `hW` binder and nothing else.

The other two consumers are NOT applied here, on purpose.  Supplying `hW` to C3
(`mrtUniformityXiL2_holds_flat_of_epsFamily`) yields the statement of
`mrtUniformityXiL2_holds_flat` (`DoorReceipt.lean:1110`), and supplying it to C4
(`mrtUniformityXiL2_holds_flat_epsFamily_capped_of_epsFamily`) yields rung 1's
(`mrtUniformityXiL2_holds_flat_epsFamily_capped`); both are ALREADY LANDED with no hypothesis, so
an applied copy would land no new statement.  The value of C3 and C4 is the implication each
states.

⚠ READER'S NOTE — TWO `c`s IN THIS FILE (the same read's finding 2).  The CHARGE is `c : ℕ`
throughout.  The four cap lines of §W1b-i (`flat_half_line_L` · `flat_anchor_line_wide_L` ·
`flat_gP1_line_L` · `flat_lvl_line_L`) bind a REAL `c`: it is their landed sources' slack binder,
kept so that each conclusion stays its source's byte for byte, and at its one call site, in
§W1c(b), it is instantiated from the clearing register `Real.log ρ` (through
`hρlog : -Real.log ρ ≤ 16 * A`), never from the charge.  Nothing here bears on twin primes. -/

/-- **⟦E2′, WITH `hW` SUPPLIED⟧** (`logChowla2_epsFamily_flatDoor_holds`) — the frozen file's
`logChowla2_epsFamily_of_flatDoor` (`FlatDoorEpsFamily.lean:208`) applied to
`flatDoorEpsFamilyW_holds`: its statement token for token with the `(hW : FlatDoorEpsFamilyW)`
binder GONE, under no hypothesis but `0 < ε ≤ 1/500`.  It is an EXISTENCE statement on the flat
family's own regime, not a statement about every regime.  Nothing here bears on twin primes. -/
theorem logChowla2_epsFamily_flatDoor_holds (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500) (A₀ : ℝ) :
    ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧ ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
      3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧ ¬ logChowla2Fails R.eps R.x R.ω :=
  logChowla2_epsFamily_of_flatDoor flatDoorEpsFamilyW_holds ε hε0 hε A₀

/-- **⟦E2's CONCLUSION, NO CROWN AND NO `hW`⟧** (`logChowla2_epsFamily_flatDoor_floor_holds`) —
`logChowla2_epsFamily_of_flatDoor_floor` (`FlatDoorEpsFamily.lean:224`) applied to
`flatDoorEpsFamilyW_holds`: the conclusion of E2 (`logChowla2_epsFamily_of_allGrades`,
`EpsFamilyReceipt.lean:42`) token for token, under E2's binders in E2's order MINUS its leading
`(hcrown : MRTDoorAllGrades)`.  ⚠ This does NOT discharge E2's `hcrown`: E2 is untouched, its
binder stands, and the crown still has no producer.  What this shows is that E2's CONCLUSION is
reached by a second route, the flat door.  Nothing here bears on twin primes. -/
theorem logChowla2_epsFamily_flatDoor_floor_holds (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
    (extraFloor : ℕ) :
    ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ ¬ logChowla2Fails R.eps R.x R.ω :=
  logChowla2_epsFamily_of_flatDoor_floor flatDoorEpsFamilyW_holds ε hε0 hε extraFloor

end Salt.MR
