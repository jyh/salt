/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.BandRatedAssembly
import Salt.MR.RegisterSupply

/-!
# The cap-free floor at the linear socket, with a RATED constant (`BandRatedSocket`)

QUEUE P2 item 6's residual **(b)**, third and last link: the sibling of
`RegisterSupply.cofkL_capFreeFloor_at_socket` built on
`BandRatedAssembly.capFreeFloor3_pieceDatum_arcDen_rated`, so that the constant arriving at the
`K_vt` cushion is a RATED one.

## The three differences from the landed name, and what each costs

1. ⭐ **`Qm` IS GONE — the landed name takes a modulus cap and this one does not.**  Not a
   weakening dressed as a strengthening: `Qm` existed for the band arm's induction-max over the
   characters of every modulus `q ≤ Q`, and the rated band branch has no such max.  This is the
   parameter the arc's R-1 row worried about, since the cushion evaluates the landed floor at
   `Qm = ⌈arcDen 12 R.Hhi⌉₊`, an argument that GROWS with `H₊`.  **A supplier with no `Qm` cannot
   be evaluated at a growing one.**
2. **The threshold's `loglog H` coefficient rises `350 → 1900`** (`BandRatedAssembly`'s
   `pieceFloor_vt_threshold_of_loglog_rated`), which is the whole arithmetic price of putting
   `bandConstQ` on the page.  §2 below pays it **at the same cushion the landed socket uses**:
   `32·K_vt + 32·D ≤ log H₊/4`, byte-identical.  The socket's own margin is `√(log H₊)` against
   `log H₊`, so a coefficient bump of 5.4× is spent out of a square-root's worth of room.
3. **The supplier's scale gate `32·diskConst q / goldenL1 q ≤ log X` is DISCHARGED here, not
   carried.**  QUEUE item 6 recorded it as *"CARRIED, NOT DISCHARGED … that discharge belongs to
   the consumer"* — this file is that consumer.  §1 does it: the gate is `O(q⁵)` and the socket's
   `μ`-floor gives `loglog X ≥ log H₊ − 14`, while `q ≤ arcDen 12 H` gives `log q ≤ 12·loglog H`.
   ⇒ **The rated socket theorem's binder list is the landed one MINUS `Qm`, plus the two `q`-free
   existentials `Z`, `δ`.  Nothing is handed on to the V7 chain that was not there before.**

⛔ SIBLINGS, never edits: `cofkL_capFreeFloor_at_socket` and its threshold lemma are untouched and
remain the corpus's statement of record for the unrated route.
-/

namespace Salt.MR

open Finset Complex DirichletCharacter Salt.SW Salt.Entropy.Chowla

/-! ## §1 — the supplier's scale gate, discharged at the socket -/

/-- `log 2 ≤ log((3+√5)/2)`: the golden argument is `≥ 5/2 ≥ 2`.  This is the only place the
golden constant needs a numerical LOWER bound; `log_golden_le_one` bounds the other side. -/
theorem log_golden_ge_log_two : Real.log 2 ≤ Real.log ((3 + Real.sqrt 5) / 2) := by
  have h5 : (2 : ℝ) ≤ Real.sqrt 5 := by
    have h := Real.sqrt_le_sqrt (show (4 : ℝ) ≤ 5 by norm_num)
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  exact Real.log_le_log (by norm_num) (by linarith)

/-- **THE GATE IS A QUINTIC** (`scaleGate_le_quintic`).  `32·diskConst q / goldenL1 q ≤ 1900·q⁵`.

`diskConst q ≤ (81/2)q²` and `1/goldenL1 q = q^{5/2}/c ≤ q³/c`, and `c = log((3+√5)/2) ≥ log 2`,
so `32·(81/2)/c = 1296/c ≤ 1900`.  ⭐ SPEND NOTHING ON GRADE: `q^{5/2} ≤ q³` throws away half an
exponent and `1900` rounds `1870` up, because §1's consumer clears any polynomial by
`log H₊` against `(loglog H₊)⁶⁰`. -/
theorem scaleGate_le_quintic {q : ℕ} [NeZero q] :
    32 * diskConst q / goldenL1 q ≤ 1900 * (q : ℝ) ^ 5 := by
  have hqN : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqN
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hc0 : 0 < Real.log ((3 + Real.sqrt 5) / 2) := e4a_log_golden_pos
  have hcnum : (0.6931 : ℝ) ≤ Real.log ((3 + Real.sqrt 5) / 2) :=
    le_trans (by linarith [Real.log_two_gt_d9]) log_golden_ge_log_two
  have hdisk : diskConst q ≤ 81 / 2 * (q : ℝ) ^ 2 := diskConst_le hqN
  have hdisk0 : (0 : ℝ) ≤ diskConst q := le_trans (by norm_num) (diskConst_ge_head hqN)
  have hg0 : 0 < goldenL1 q := goldenL1_pos q
  have hinv0 : (0 : ℝ) ≤ 1 / goldenL1 q := le_of_lt (by positivity)
  have hrpow3 : (q : ℝ) ^ (5 / 2 : ℝ) ≤ (q : ℝ) ^ (3 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (5 / 2 : ℝ) ≤ (3 : ℝ))
    rwa [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  have hinv : 1 / goldenL1 q ≤ (q : ℝ) ^ (3 : ℕ) / Real.log ((3 + Real.sqrt 5) / 2) := by
    rw [goldenL1, one_div_div]
    gcongr
  have hq5 : (0 : ℝ) ≤ (q : ℝ) ^ 5 := by positivity
  calc 32 * diskConst q / goldenL1 q = 32 * diskConst q * (1 / goldenL1 q) := by ring
    _ ≤ 32 * (81 / 2 * (q : ℝ) ^ 2) * ((q : ℝ) ^ (3 : ℕ)
          / Real.log ((3 + Real.sqrt 5) / 2)) := by
        refine mul_le_mul ?_ hinv hinv0 (by positivity)
        linarith
    _ = 1296 / Real.log ((3 + Real.sqrt 5) / 2) * (q : ℝ) ^ 5 := by ring
    _ ≤ 1900 * (q : ℝ) ^ 5 := by
        have hle : 1296 / Real.log ((3 + Real.sqrt 5) / 2) ≤ 1900 := by
          rw [div_le_iff₀ hc0]; nlinarith
        nlinarith [hq5]

set_option maxHeartbeats 400000 in
-- the socket preamble and the quintic's logarithm are elaborated in one `linarith` simplex
/-- **⟦THE SCALE GATE AT THE LINEAR SOCKET⟧** (`cofkL_scale_gate_at_socket`).
`chi_Llower_real_of_L1`'s own gate, discharged from the socket and the regime — the hypothesis
QUEUE item 6 booked to the consumer.

The whole content is that two logarithms are far apart: `log(1900·q⁵) ≤ 1899 + 60·loglog H`
against `loglog X ≥ log H₊ − 14 ≥ 10⁴·√(log H₊) − 14`, with `loglog H ≤ 2√(log H₊)`. -/
theorem cofkL_scale_gate_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ} [NeZero q]
    (hb : SocketBaseL R M H L q j A s)
    (hε : (1 : ℝ) / 500 ≤ (R.eps : ℝ))
    (hlo : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (harc : (q : ℝ) ≤ arcDen 12 H) :
    32 * diskConst q / goldenL1 q ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  -- ⟦the design floor, unwound⟧ — as in `cofkL_threshold_at_socket`
  have h1 : R.Hlo ≤ H := hb.1
  have h2 : H ≤ R.Hhi := hb.2.1
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hlogHlo : (14 : ℝ) ≤ Real.log (R.Hlo : ℝ) := cofk_log_big hHlo4
  have hexp : Real.exp (518 : ℝ) ≤ Real.log (R.Hlo : ℝ) := by
    have h := Real.exp_le_exp.mpr hlo
    rwa [Real.exp_log (by linarith)] at h
  have hquart : (10 : ℝ) ^ 8 ≤ Real.exp (518 : ℝ) := by
    have h := cofk_exp_quartic (u := (518 : ℝ)) (by norm_num)
    have hnum : (290029400 : ℝ) ≤ (1 + (518 : ℝ) / 4) ^ 4 := by norm_num
    linarith
  have hlogHlo8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hlo : ℝ) := by linarith
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hH4 : (4000000 : ℝ) ≤ (H : ℝ) := by linarith
  have hHlo0 : (0 : ℝ) < (R.Hlo : ℝ) := by linarith
  have hlogH : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) := Real.log_le_log hHlo0 hHloH
  have hlogHhi : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) :=
    Real.log_le_log (by linarith) hHHhi
  have hLH8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hhi : ℝ) := by linarith
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hHhi14 : (10 : ℝ) ^ 14 ≤ (R.Hhi : ℝ) := by
    have hlogle : Real.log ((10 : ℝ) ^ 14) ≤ Real.log (R.Hhi : ℝ) := by
      rw [show ((10 : ℝ) ^ 14) = (10 : ℝ) ^ (14 : ℕ) by norm_num, Real.log_pow]
      push_cast
      linarith [cofk_log_ten_le, hLH8]
    have h2' := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log (by positivity), Real.exp_log hHhi0] at h2'
  have hHe : Real.exp 1 ≤ Real.log (H : ℝ) := by
    have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    linarith
  -- ⟦the `μ`-floor and the scale floor⟧
  have hmu := cofkL_mu_floor hb hε hHhi14 hH4
  have hfl := cofkL_logX_floor hb hε hHhi14 hH4
  have hlogXpos : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have hbig : (0 : ℝ) < (R.Hhi : ℝ) / 10 ^ 6 := by positivity
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
  -- ⟦the quintic, and its logarithm⟧
  have hlogq : Real.log q ≤ 12 * Real.log (Real.log (H : ℝ)) := log_le_of_le_arcDen hHe harc
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

/-! ## §2 — the threshold at the socket, at the rated coefficient -/

set_option maxHeartbeats 1000000 in
-- the `_vt` threshold's five legs are bracketed against `√(log H₊)` in one simplex, as in the
-- landed `cofkL_threshold_at_socket`
/-- **⟦THE THRESHOLD AT THE LINEAR SOCKET, RATED⟧** (`cofkL_threshold_at_socket_rated`).
`BandRatedAssembly.pieceFloor_vt_threshold_of_loglog_rated`'s antecedent, discharged from the
socket, the regime, and ⟦THE SAME CUSHION THE LANDED SOCKET USES⟧ — `32·K_vt + 32·D ≤ log H₊/4`,
byte-identical to `cofkL_threshold_at_socket`'s.

⭐ **THAT THE CUSHION IS UNCHANGED IS THE POINT OF THE LEMMA.**  Rating the band constant raises
the `loglog H` coefficient `350 → 1900`; the socket's margin is `√(log H₊)` against `log H₊`, so
the legs go from `1180·√(log H₊)` to `4280·√(log H₊)` and the close still has four orders of
room. -/
theorem cofkL_threshold_at_socket_rated {R : ChowlaRegime} {M H L q j A s : ℕ} {Kvt D : ℝ}
    (hb : SocketBaseL R M H L q j A s)
    (hε : (1 : ℝ) / 500 ≤ (R.eps : ℝ))
    (hlo : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)))
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
  have hexp : Real.exp (518 : ℝ) ≤ Real.log (R.Hlo : ℝ) := by
    have h := Real.exp_le_exp.mpr hlo
    rwa [Real.exp_log (by linarith)] at h
  have hquart : (10 : ℝ) ^ 8 ≤ Real.exp (518 : ℝ) := by
    have h := cofk_exp_quartic (u := (518 : ℝ)) (by norm_num)
    have hnum : (290029400 : ℝ) ≤ (1 + (518 : ℝ) / 4) ^ 4 := by norm_num
    linarith
  have hlogHlo8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hlo : ℝ) := by linarith
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hH4 : (4000000 : ℝ) ≤ (H : ℝ) := by linarith
  have hHlo0 : (0 : ℝ) < (R.Hlo : ℝ) := by linarith
  have hlogH : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) := Real.log_le_log hHlo0 hHloH
  have hlogHhi : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) :=
    Real.log_le_log (by linarith) hHHhi
  have hLH8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hhi : ℝ) := by linarith
  have hlogH1 : (1 : ℝ) < Real.log (H : ℝ) := by linarith
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hHhi14 : (10 : ℝ) ^ 14 ≤ (R.Hhi : ℝ) := by
    have hlogle : Real.log ((10 : ℝ) ^ 14) ≤ Real.log (R.Hhi : ℝ) := by
      rw [show ((10 : ℝ) ^ 14) = (10 : ℝ) ^ (14 : ℕ) by norm_num, Real.log_pow]
      push_cast
      linarith [cofk_log_ten_le, hLH8]
    have h2' := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log (by positivity), Real.exp_log hHhi0] at h2'
  -- ⟦THE `μ`-FLOOR⟧
  have hmu := cofkL_mu_floor hb hε hHhi14 hH4
  set μ : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hμdef
  set LH : ℝ := Real.log (R.Hhi : ℝ) with hLHdef
  have hμ : LH - 14 ≤ μ := hmu
  have hμbig : (10 : ℝ) ^ 8 - 14 ≤ μ := by linarith
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
  -- ⟦the close⟧
  have hmargin : 4280 * Real.sqrt LH + 2420 + LH / 4 < μ / 2 + μ / 4 := by
    nlinarith [hprodv, hv, hμ, hv0]
  linarith

/-! ## §3 — the exit: the rated cap-free floor at the linear anchors -/

set_option maxHeartbeats 1000000 in
-- the arc-range floor's eight-binder instantiation is elaborated against the socket in one
-- `exact`
/-- **⟦THE CAP-FREE FLOOR AT THE LINEAR ANCHORS, RATED⟧**
(`cofkL_capFreeFloor_at_socket_rated`) — QUEUE P2 item 6 residual (b), the rethread's last link.

The drop-in sibling of `RegisterSupply.cofkL_capFreeFloor_at_socket`: same conclusion, same
socket, **the same cushion `32·K_vt + 32·(2 log M + log 4 + 50) ≤ log H₊/4`**, and
⭐ **NO `Qm` — every character of every modulus on the arc range is covered, because the rated
band branch has no induction-max to cap.**  `Z` and `δ` are the `q`-free, `χ`-free existentials
of `margin_band_threshold_rated`; `K_vt` is `capFreeFloor3_margin_all_chi_vt_rated`'s constant
plus `max 0 (bandArcConst Z δ)`.

⛔ **WHAT THIS DOES *NOT* CLAIM.**  `K_vt` is still one symbolic nonnegative real and the cushion
is still a hypothesis; what has changed is the SHAPE of what stands behind it — a constant with a
stated growth rate in `q`, evaluated nowhere.  The V7 chain's own rethread onto this sibling is a
further step and is not taken here. -/
theorem cofkL_capFreeFloor_at_socket_rated (K : ℕ) :
    ∃ Z δ Kvt : ℝ, 1 ≤ Z ∧ 0 < δ ∧ 0 ≤ Kvt ∧
      ∀ {R : ChowlaRegime} {M H L q j A s : ℕ} (χ : DirichletCharacter ℂ q),
        SocketBaseL R M H L q j A s → 1 ≤ M →
        (1 : ℝ) / 500 ≤ (R.eps : ℝ) →
        (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        32 * Kvt + 32 * (2 * Real.log (M : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
        ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
            (calQK (AdoorL M) (s13GK K M) M)) (((A + s : ℕ)) : ℝ) := by
  obtain ⟨Z, δ, Kvt, hZ, hδ, hK0, hK⟩ := capFreeFloor3_pieceDatum_arcDen_rated
  refine ⟨Z, δ, Kvt, hZ, hδ, hK0, ?_⟩
  intro R M H L q j A s χ hb hM hε hlo hcush 𝒥 h𝒥
  have hq0 : 0 < q := hb.2.2.2.1
  haveI : NeZero q := ⟨by omega⟩
  have h1 : R.Hlo ≤ H := hb.1
  have h2 : H ≤ R.Hhi := hb.2.1
  have harc : (q : ℝ) ≤ arcDen 12 H := hb.2.2.2.2.1
  -- ⟦the design floor⟧
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hH4 : (4000000 : ℝ) ≤ (H : ℝ) := by linarith
  have hlogH : (14 : ℝ) ≤ Real.log (H : ℝ) := cofk_log_big hH4
  have hlogHe : Real.exp 1 ≤ Real.log (H : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  -- ⟦`H₊ ≥ 10^14`⟧
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hlogHlo : (14 : ℝ) ≤ Real.log (R.Hlo : ℝ) := cofk_log_big hHlo4
  have hexp : Real.exp (518 : ℝ) ≤ Real.log (R.Hlo : ℝ) := by
    have h := Real.exp_le_exp.mpr hlo
    rwa [Real.exp_log (by linarith)] at h
  have hquart : (10 : ℝ) ^ 8 ≤ Real.exp (518 : ℝ) := by
    have h := cofk_exp_quartic (u := (518 : ℝ)) (by norm_num)
    have hnum : (290029400 : ℝ) ≤ (1 + (518 : ℝ) / 4) ^ 4 := by norm_num
    linarith
  have hlogHlo8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hlo : ℝ) := by linarith
  have hlogmono : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hHloH
  have hlogHhi : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) :=
    Real.log_le_log (by linarith) hHHhi
  have hLH8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hhi : ℝ) := by linarith
  have hHhi14 : (10 : ℝ) ^ 14 ≤ (R.Hhi : ℝ) := by
    have hlogle : Real.log ((10 : ℝ) ^ 14) ≤ Real.log (R.Hhi : ℝ) := by
      rw [show ((10 : ℝ) ^ 14) = (10 : ℝ) ^ (14 : ℕ) by norm_num, Real.log_pow]
      push_cast
      linarith [cofk_log_ten_le, hLH8]
    have h2' := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log (by positivity), Real.exp_log hHhi0] at h2'
  -- ⟦the scale gate, the debit page, the threshold⟧
  have hXee : Real.exp (Real.exp 1) ≤ (((A + s : ℕ)) : ℝ) :=
    cofkL_X_ge_expexp hb hε hHhi14 hH4
  have hgate : 32 * diskConst q / goldenL1 q ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    cofkL_scale_gate_at_socket hb hε hlo harc
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hD0 : (0 : ℝ) ≤ 2 * Real.log (M : ℝ) + Real.log 4 + 50 := by
    have h1' : (0 : ℝ) ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
    have h2' : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hdebit := cofkL_debit_bound K M (((A + s : ℕ)) : ℝ) hM 𝒥 h𝒥
  have hthr := cofkL_threshold_at_socket_rated (Kvt := Kvt)
    (D := 2 * Real.log (M : ℝ) + Real.log 4 + 50) hb hε hlo hcush
  exact hK q H χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 𝒥
    (((A + s : ℕ)) : ℝ) (2 * Real.log (M : ℝ) + Real.log 4 + 50)
    hlogHe harc hXee hD0 hgate hdebit hthr

end Salt.MR
