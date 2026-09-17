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

end Salt.MR
