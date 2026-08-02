/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S13CapGateLinear
import Salt.MR.RbdSupply

/-!
# `RegisterSupply` — THE TWO CARRIED PREDICATES OF `logChowla2_ineffective_v3`, PRICED

`S16Compose.logChowla2_ineffective_v3` (`Salt/MR/S16Compose.lean:1112`) carries exactly two
conclusion-side supply predicates, both at the LINEAR door and the LINEAR socket:

* `S16BaseScaleCap96_L_gk 32000000 R (flatDoorM A)` — ⟦ITEM 3⟧'s base-scale cap
  (`S13CapGateLinear.lean:891`);
* `S16CofactorSupply_L_gk 32000000 Cq R (flatDoorM A)` — ⟦RULING 9⟧'s co-factor debt
  (`S13CapGateLinear.lean:897`).

This file prices both against the socket's own fields and the regime's own fields.

## §1 — ⟦W2⟧ THE BASE-SCALE CAP, AND THE `x`-WINDOW IT NEEDS

**THE FINDING (2026-08-02, at the bytes).**  The cap is *not* a wide numeric inequality the
socket discharges by itself.  Its left side `loglog(A+s)` is bounded above by NOTHING but the
socket's own `(A : ℝ) ≤ 2·R.x`, and `ChowlaRegime` bounds `R.x` only from BELOW
(`hheadroom`, `hheadroom'`, `hPHheadroom`, `hxbig` are all lower bounds).  Its right side
`log 𝒫₂/9.60000096` reads only `M` and the lever `K` — never the regime.  So at a FIXED `M`
the predicate FAILS at regimes whose outer scale is large enough, and the terminal hands the
caller `g R.Hhi R.ω ≤ R.x` for a CALLER-CHOSEN `g` — a lower bound, which can be driven above
any ceiling the anchor provides.

What is true, and what §1 proves, is the reduction: ONE explicit window on the regime's outer
scale discharges the cap.  `s16_baseScaleCap96_L_of_xwindow` takes
`loglog(3·R.x) ≤ log 𝒫₂/9.60000096`; `s16_baseScaleCap96_L_of_x_small` takes the friendlier
`loglog(3·R.x) ≤ 𝒢K` (the lever's own numeral — at `K = 32000000` this permits every outer
scale below `exp exp (3072·2^{32000000}·M)`).  The residual is therefore a MISSING EXPORT of
the terminal, named exactly: an `x`-CEILING beside the `x`-floor it already exports.

## §2 — ⟦W1(a)⟧ THE DEBIT PAGE AT THE LINEAR ANCHORS

`RbdSupply.m4_supplier_all_chi` (`:190`) reads the door blocks in exactly ONE binder, the
powerset Mertens debit.  §2 discharges it at `Pseq := calP (AdoorL M) (s13GK K M)`,
`Qseq := calQK (AdoorL M) (s13GK K M) M`, `J := 2`, with the anchor CANCELLING:

  `log 𝒬_i = (i²M)·log 𝒫_i`  (`cofkL_logQK_eq`)  ⟹  `loglog 𝒬_i − loglog 𝒫_i = log(i²M)`

— no `A`, no `G`, hence identical at `Adoor` and at `AdoorL`.  The debit is
`D = 2·log M + log 4 + 50` (`cofkL_debit_bound`).

## §3 — ⟦W1(b)⟧ THE `μ`-FLOOR AND THE `_vt` THRESHOLD

`RbdSupply.pieceFloor_vt_threshold_of_loglog` reduces the `_vt` floor's threshold to ONE
`loglog X` lower bound.  §3 supplies it from the socket + the regime:

* `cofkL_mu_floor` — `loglog(A+s) ≥ log H₊ − 14`.  The gain is EXPONENTIAL: the regime's
  `hPHheadroom` (`8·(4^⌊ε²H₊⌋)²·ω ≤ x`) against the socket's `x ≤ 16·ω·(log H)¹²·A` puts
  `log A ≥ H₊/10⁶`, so `loglog A ≥ log H₊ − 14`, where the naive coupling `ω·H₊ ≤ x` gives
  only `loglog A ≳ loglog H₊`.  This one step is the whole margin: supply `e^{λ₊}` against
  demand `≈ 390·λ₊`.
* `cofkL_threshold_at_socket` — the threshold verbatim, with the `_vt` constant `K_vt` and the
  mask debit `D` carried under ONE explicit cushion `32·K_vt + 32·D ≤ log H₊/4`.  At the
  terminal's regime `loglog H₋ ≥ 3.2·A ≥ 518`, so the cushion exceeds `e^{518}/128 ≈ 10^{222}`.

**PURELY ADDITIVE.**  No landed declaration is touched.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — three crude brackets, used throughout -/

/-- `log t ≤ 2√t − 2` — `log ≤ id − 1` read at `√t`, doubled. -/
theorem cofk_log_le_two_sqrt {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ 2 * Real.sqrt t - 2 := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt ht.le
  rw [h2] at h1
  linarith

/-- `(1 + u/4)^4 ≤ e^u` for `0 ≤ u` — the quartic bracket that turns the design floor
`loglog H₋ ≥ 518` into a numeral. -/
theorem cofk_exp_quartic {u : ℝ} (hu : 0 ≤ u) : (1 + u / 4) ^ 4 ≤ Real.exp u := by
  have h1 : 1 + u / 4 ≤ Real.exp (u / 4) := by linarith [Real.add_one_le_exp (u / 4)]
  have h0 : (0 : ℝ) ≤ 1 + u / 4 := by linarith
  have hE0 : (0 : ℝ) < Real.exp (u / 4) := Real.exp_pos _
  have hs : (1 + u / 4) ^ 2 ≤ Real.exp (u / 4) ^ 2 := by nlinarith
  have hs0 : (0 : ℝ) ≤ (1 + u / 4) ^ 2 := sq_nonneg _
  have hq : ((1 + u / 4) ^ 2) ^ 2 ≤ (Real.exp (u / 4) ^ 2) ^ 2 := by nlinarith
  have e1 : Real.exp (u / 4) ^ 2 = Real.exp (u / 2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (u / 2) ^ 2 = Real.exp u := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  calc (1 + u / 4) ^ 4 = ((1 + u / 4) ^ 2) ^ 2 := by ring
    _ ≤ (Real.exp (u / 4) ^ 2) ^ 2 := hq
    _ = Real.exp u := by rw [e1, e2]

/-- `14 ≤ log t` past the regime's own `H₋`-floor `4·10⁶` (`2²¹ ≤ 4·10⁶`). -/
theorem cofk_log_big {t : ℝ} (ht : (4000000 : ℝ) ≤ t) : (14 : ℝ) ≤ Real.log t := by
  have h1 : Real.log ((2 : ℝ) ^ (21 : ℕ)) ≤ Real.log t :=
    Real.log_le_log (by norm_num) (by norm_num; linarith)
  rw [Real.log_pow] at h1
  push_cast at h1
  linarith [Real.log_two_gt_d9]

/-- `log 10 ≤ 2.311` — from `10³ ≤ 2¹⁰`. -/
theorem cofk_log_ten_le : Real.log 10 ≤ 2.311 := by
  have h : Real.log ((10 : ℝ) ^ (3 : ℕ)) ≤ Real.log ((2 : ℝ) ^ (10 : ℕ)) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith [Real.log_two_lt_d9]

/-! ## §1 — ⟦W2⟧ THE BASE-SCALE CAP AT THE LINEAR DOOR -/

/-- The base-scale cap's right side is nonnegative. -/
theorem s16_logP2_nonneg (A G : ℕ) : (0 : ℝ) ≤ Real.log ((calP A G 2 : ℕ) : ℝ) := by
  rw [s16_logP2]
  have h1 : (0 : ℝ) ≤ ((4 * (A * G) : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  exact mul_nonneg h1 h2

/-- **⟦THE CAP, REDUCED TO ONE `x`-WINDOW⟧** (`s16_baseScaleCap96_L_of_xwindow`).  The socket's
scale is bounded above by the regime's outer scale and by nothing else (`A ≤ 2x`,
`s ≤ L ≤ H ≤ H₊`, `ω·H₊ ≤ x`, `ω ≥ 2`), whence `A + s ≤ 3x`.  So ONE window on `loglog(3x)`
discharges ⟦ITEM 3⟧ at the linear door and the linear socket. -/
theorem s16_baseScaleCap96_L_of_xwindow (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    (hx : Real.log (Real.log (3 * (R.x : ℝ)))
      ≤ Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) / 9.60000096) :
    S16BaseScaleCap96_L_gk K R M := by
  intro H L q j A s hb
  have h2 : H ≤ R.Hhi := hb.2.1
  have h3 : L ≤ H := hb.2.2.1
  have h8 : 0 < A := hb.2.2.2.2.2.2.2.1
  have h12 : (A : ℝ) ≤ 2 * (R.x : ℝ) := hb.2.2.2.2.2.2.2.2.2.2.2.1
  have h13 : s ≤ L := hb.2.2.2.2.2.2.2.2.2.2.2.2
  -- ⟦the regime's own window coupling⟧ `ω·H₊ ≤ x` with `ω ≥ 2`
  have hω : 0 < R.ω := lt_of_lt_of_le (by norm_num) R.hω
  have hhead : R.Hhi * R.ω ≤ R.x := (Nat.le_div_iff_mul_le hω).mp R.hheadroom
  have h2Hhi : 2 * R.Hhi ≤ R.x := by
    have hstep : R.Hhi * 2 ≤ R.Hhi * R.ω := Nat.mul_le_mul_left _ R.hω
    omega
  have h2HhiR : 2 * (R.Hhi : ℝ) ≤ (R.x : ℝ) := by exact_mod_cast h2Hhi
  have hsHhi : (s : ℝ) ≤ (R.Hhi : ℝ) := by
    have hs : s ≤ R.Hhi := le_trans h13 (le_trans h3 h2)
    exact_mod_cast hs
  have hsum : (((A + s : ℕ)) : ℝ) ≤ 3 * (R.x : ℝ) := by push_cast; linarith
  have hA1 : (1 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    have : 1 ≤ A + s := by omega
    exact_mod_cast this
  have hlogA0 : (0 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := Real.log_nonneg hA1
  by_cases hsmall : Real.log (((A + s : ℕ)) : ℝ) ≤ 1
  · -- the degenerate corner: `loglog(A+s) ≤ 0`, and the cap's right side is nonnegative
    have hle0 : Real.log (Real.log (((A + s : ℕ)) : ℝ)) ≤ 0 :=
      Real.log_nonpos hlogA0 hsmall
    have hR : (0 : ℝ) ≤ Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) / 9.60000096 :=
      div_nonneg (s16_logP2_nonneg (AdoorL M) (s13GK K M)) (by norm_num)
    linarith
  · have hbig : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith [not_le.mp hsmall]
    have hApos : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by linarith
    have hstep : Real.log (((A + s : ℕ)) : ℝ) ≤ Real.log (3 * (R.x : ℝ)) :=
      Real.log_le_log hApos hsum
    have hll : Real.log (Real.log (((A + s : ℕ)) : ℝ))
        ≤ Real.log (Real.log (3 * (R.x : ℝ))) :=
      Real.log_le_log (by linarith) hstep
    linarith

/-- **⟦THE FRIENDLY WINDOW⟧** (`s16_baseScaleCap96_L_of_x_small`).  The cap's right side
dominates the lever's own numeral `𝒢K = 3072·2^K·M` by the factor
`4·2³⁶·log 2/9.60000096 ≈ 1.9·10^{10}`, so a window at `𝒢K` suffices. -/
theorem s16_baseScaleCap96_L_of_x_small (K : ℕ) {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    (hx : Real.log (Real.log (3 * (R.x : ℝ))) ≤ ((s13GK K M : ℕ) : ℝ)) :
    S16BaseScaleCap96_L_gk K R M := by
  refine s16_baseScaleCap96_L_of_xwindow K (le_trans hx ?_)
  rw [s16_logP2]
  have hG0 : (0 : ℝ) ≤ ((s13GK K M : ℕ) : ℝ) := Nat.cast_nonneg _
  have hGpos : (1 : ℝ) ≤ ((s13GK K M : ℕ) : ℝ) := by
    have := one_le_s13GK K hM; exact_mod_cast this
  have hA36 : (68719476736 : ℝ) ≤ ((AdoorL M : ℕ) : ℝ) := by
    have h : (68719476736 : ℕ) ≤ AdoorL M := by
      rw [AdoorL, show (68719476736 : ℕ) = 2 ^ 36 by norm_num]
      exact Nat.le_mul_of_pos_right _ hM
    exact_mod_cast h
  have h2 : (0.6931 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hcast : ((4 * (AdoorL M * s13GK K M) : ℕ) : ℝ)
      = 4 * (((AdoorL M : ℕ) : ℝ) * ((s13GK K M : ℕ) : ℝ)) := by push_cast; ring
  rw [hcast, le_div_iff₀ (by norm_num)]
  have hstep1 : 68719476736 * ((s13GK K M : ℕ) : ℝ)
      ≤ ((AdoorL M : ℕ) : ℝ) * ((s13GK K M : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hA36 hG0
  have hstep2 : (4 * (68719476736 * ((s13GK K M : ℕ) : ℝ))) * 0.6931
      ≤ (4 * (((AdoorL M : ℕ) : ℝ) * ((s13GK K M : ℕ) : ℝ))) * Real.log 2 := by
    refine mul_le_mul (by linarith) h2 (by norm_num) (by nlinarith [hA36, hG0])
  nlinarith [hstep2, hGpos]

/-! ## §2 — ⟦W1(a)⟧ THE DEBIT PAGE AT THE LINEAR ANCHORS -/

/-- `log 𝒫_i = e_i·log 2`. -/
theorem cofkL_logP_eq (A G i : ℕ) :
    Real.log ((calP A G i : ℕ) : ℝ) = ((calE A G i : ℕ) : ℝ) * Real.log 2 := by
  have hc : ((calP A G i : ℕ) : ℝ) = (2 : ℝ) ^ (calE A G i) := by
    rw [calP]; push_cast; ring
  rw [hc, Real.log_pow]

/-- **⟦THE ANCHOR CANCELLATION⟧** (`cofkL_logQK_eq`).  `log 𝒬_i = (i²M)·log 𝒫_i` — no `A`,
no `G`.  This is why the co-factor debit is IDENTICAL at `Adoor` and at `AdoorL`. -/
theorem cofkL_logQK_eq (A G M i : ℕ) :
    Real.log ((calQK A G M i : ℕ) : ℝ)
      = ((i ^ 2 * M : ℕ) : ℝ) * Real.log ((calP A G i : ℕ) : ℝ) := by
  have hc : ((calQK A G M i : ℕ) : ℝ) = (2 : ℝ) ^ ((i ^ 2 * M) * calE A G i) := by
    rw [calQK]; push_cast; ring
  rw [hc, Real.log_pow, cofkL_logP_eq]
  push_cast
  ring

/-- `e_i ≥ 2` at the linear anchor: `e_i ≥ A_L(M) = 2³⁶·M ≥ 2³⁶`. -/
theorem cofkL_calE_ge (K M i : ℕ) (hM : 1 ≤ M) :
    2 ≤ calE (AdoorL M) (s13GK K M) i := by
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hM
  have hA : (2 : ℕ) ^ 36 ≤ AdoorL M := by
    rw [AdoorL]; exact Nat.le_mul_of_pos_right _ hM
  have hGp : 0 < (s13GK K M) ^ (i - 1) := pow_pos (by omega) _
  have hf : 0 < (Nat.factorial i) ^ 2 := pow_pos (Nat.factorial_pos i) 2
  have h1 : AdoorL M ≤ AdoorL M * (s13GK K M) ^ (i - 1) :=
    Nat.le_mul_of_pos_right _ hGp
  have h2 : AdoorL M * (s13GK K M) ^ (i - 1)
      ≤ AdoorL M * (s13GK K M) ^ (i - 1) * (Nat.factorial i) ^ 2 :=
    Nat.le_mul_of_pos_right _ hf
  have h3 : (2 : ℕ) ≤ 2 ^ 36 := by norm_num
  rw [calE]
  exact le_trans h3 (le_trans hA (le_trans h1 h2))

/-- `e ≤ 𝒫_i` at the linear anchor (in fact `𝒫_i ≥ 2^{2³⁶}`). -/
theorem cofkL_calP_ge_e (K M i : ℕ) (hM : 1 ≤ M) :
    Real.exp 1 ≤ ((calP (AdoorL M) (s13GK K M) i : ℕ) : ℝ) := by
  have hE := cofkL_calE_ge K M i hM
  have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ (calE (AdoorL M) (s13GK K M) i) :=
    Nat.pow_le_pow_right (by norm_num) hE
  have h4' : (4 : ℕ) ≤ 2 ^ (calE (AdoorL M) (s13GK K M) i) :=
    le_trans (by norm_num) h4
  have h4R : (4 : ℝ) ≤ ((calP (AdoorL M) (s13GK K M) i : ℕ) : ℝ) := by
    rw [calP]; exact_mod_cast h4'
  have he : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
  linarith

/-- `𝒫_i ≤ 𝒬_i` at the linear anchor. -/
theorem cofkL_calP_le_calQK (K M i : ℕ) (hM : 1 ≤ M) (hi : 1 ≤ i) :
    calP (AdoorL M) (s13GK K M) i ≤ calQK (AdoorL M) (s13GK K M) M i := by
  rw [calP, calQK]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have h1 : 0 < i ^ 2 * M := Nat.mul_pos (pow_pos (by omega) 2) (by omega)
  exact Nat.le_mul_of_pos_left _ h1

/-- **⟦THE BLOCK DEBIT AT THE LINEAR ANCHOR⟧** (`cofkL_block_debit`).  One block's Mertens
mass is `log(i²M) + 25` — the anchor has cancelled. -/
theorem cofkL_block_debit (K M i : ℕ) (X : ℝ) (hM : 1 ≤ M) (hi : 1 ≤ i) :
    (∑ p ∈ blockWindowPrimes (calP (AdoorL M) (s13GK K M) i)
        (calQK (AdoorL M) (s13GK K M) M i) X, (1 : ℝ) / (p : ℝ))
      ≤ Real.log ((i ^ 2 * M : ℕ) : ℝ) + 25 := by
  have hPe := cofkL_calP_ge_e K M i hM
  have hPQ := cofkL_calP_le_calQK K M i hM hi
  have hbase := blockWindow_mertens_const _ _ X hPe hPQ
  have hE := cofkL_calE_ge K M i hM
  have hlogP : (0 : ℝ) < Real.log ((calP (AdoorL M) (s13GK K M) i : ℕ) : ℝ) := by
    rw [cofkL_logP_eq]
    have h1 : (2 : ℝ) ≤ ((calE (AdoorL M) (s13GK K M) i : ℕ) : ℝ) := by exact_mod_cast hE
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hiM : (0 : ℝ) < ((i ^ 2 * M : ℕ) : ℝ) := by
    have h : 0 < i ^ 2 * M := Nat.mul_pos (pow_pos (by omega) 2) (by omega)
    exact_mod_cast h
  have hdiff : Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M i : ℕ) : ℝ))
      = Real.log ((i ^ 2 * M : ℕ) : ℝ)
        + Real.log (Real.log ((calP (AdoorL M) (s13GK K M) i : ℕ) : ℝ)) := by
    rw [cofkL_logQK_eq, Real.log_mul (ne_of_gt hiM) (ne_of_gt hlogP)]
  rw [hdiff] at hbase
  linarith

/-- **⟦THE DEBIT PAGE⟧** (`cofkL_debit_bound`).  `m4_supplier_all_chi`'s ONE anchor-reading
binder, discharged at `J = 2` and the LINEAR anchors: `D = 2·log M + log 4 + 50`. -/
theorem cofkL_debit_bound (K M : ℕ) (X : ℝ) (hM : 1 ≤ M) :
    ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (s13GK K M) i)
          (calQK (AdoorL M) (s13GK K M) M i) X, (1 : ℝ) / (p : ℝ))
        ≤ 2 * Real.log (M : ℝ) + Real.log 4 + 50 := by
  intro 𝒥 h𝒥
  rw [Finset.mem_powerset] at h𝒥
  have hnn : ∀ i ∈ (Finset.Icc 1 2 : Finset ℕ), i ∉ 𝒥 →
      (0 : ℝ) ≤ ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (s13GK K M) i)
        (calQK (AdoorL M) (s13GK K M) M i) X, (1 : ℝ) / (p : ℝ) :=
    fun i _ _ => Finset.sum_nonneg (fun p _ => by positivity)
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg h𝒥 hnn
  have hset : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [hset, Finset.sum_pair (by norm_num)] at hsub
  have h1 := cofkL_block_debit K M 1 X hM (le_refl 1)
  have h2 := cofkL_block_debit K M 2 X hM (by norm_num)
  have e1 : ((1 ^ 2 * M : ℕ) : ℝ) = (M : ℝ) := by push_cast; ring
  have e2 : ((2 ^ 2 * M : ℕ) : ℝ) = 4 * (M : ℝ) := by push_cast; ring
  rw [e1] at h1
  rw [e2] at h2
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlog4M : Real.log (4 * (M : ℝ)) = Real.log 4 + Real.log (M : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hMpos)
  rw [hlog4M] at h2
  linarith

/-! ## §3 — ⟦W1(b)⟧ THE `μ`-FLOOR AND THE `_vt` THRESHOLD -/

set_option maxHeartbeats 1000000 in
-- the primorial majorant `4^{2⌊ε²H₊⌋}` and the rpow arc denominator elaborate against the
-- regime's own field in one `linarith only` chain
/-- **⟦THE `log X` FLOOR AT THE LINEAR SOCKET⟧** (`cofkL_logX_floor`).  `log(A+s) ≥ H₊/10⁶`.

⟦THE EXPONENTIAL GAIN⟧ the regime's `hPHheadroom` (`8·(4^⌊ε²H₊⌋)²·ω ≤ x`) against the
socket's `x ≤ 16·ω·(log H)¹²·A` gives `A ≥ 4^{2⌊ε²H₊⌋}/(2(log H)¹²)`, so `log A ≥ H₊/10⁶` —
LINEAR in `H₊`, not logarithmic.  The naive coupling `ω·H₊ ≤ x` would give only
`loglog A ≳ loglog H₊`, which the `_vt` threshold's `350·loglog H` beats.  This one step is
the whole margin. -/
theorem cofkL_logX_floor {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseL R M H L q j A s)
    (hε : (1 : ℝ) / 500 ≤ (R.eps : ℝ))
    (hHhi : (10 : ℝ) ^ 14 ≤ (R.Hhi : ℝ))
    (hH : (4000000 : ℝ) ≤ (H : ℝ)) :
    (R.Hhi : ℝ) / 10 ^ 6 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have h2 : H ≤ R.Hhi := hb.2.1
  have h8 : 0 < A := hb.2.2.2.2.2.2.2.1
  have h11 : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) :=
    hb.2.2.2.2.2.2.2.2.2.2.1
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by nlinarith
  have hlogH : (14 : ℝ) ≤ Real.log (H : ℝ) := cofk_log_big hH
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := by linarith
  have hω0 : (0 : ℝ) < (R.ω : ℝ) := by
    have : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
    linarith
  -- ⟦the arc denominator⟧
  have harc : (0 : ℝ) < arcDen 12 H := by
    rw [arcDen]; exact Real.rpow_pos_of_pos hlogH0 12
  have hlogarc : Real.log (arcDen 12 H) = 12 * Real.log (Real.log (H : ℝ)) :=
    log_arcDen_twelve hlogH0
  -- ⟦the primorial majorant⟧
  set E : ℕ := ⌊R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)⌋₊ with hEdef
  have hPH0 : 8 * (((4 ^ E : ℕ) : ℝ)) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ) := R.hPHheadroom
  have hW : (((4 ^ E : ℕ) : ℝ)) = (4 : ℝ) ^ E := by push_cast; ring
  rw [hW] at hPH0
  -- ⟦the combination, `ω` cancelled⟧
  have hmul : (8 * ((4 : ℝ) ^ E) ^ 2) * (R.ω : ℝ)
      ≤ (16 * arcDen 12 H * (A : ℝ)) * (R.ω : ℝ) := by
    have := le_trans hPH0 h11; linarith
  have h8w : 8 * ((4 : ℝ) ^ E) ^ 2 ≤ 16 * arcDen 12 H * (A : ℝ) :=
    le_of_mul_le_mul_right hmul hω0
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast h8
  have hkey : ((4 : ℝ) ^ E) ^ 2 / (2 * arcDen 12 H) ≤ (A : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- ⟦the logarithm of the floor⟧
  have hlogW : Real.log (((4 : ℝ) ^ E) ^ 2) = 2 * (E : ℝ) * Real.log 4 := by
    rw [← pow_mul, Real.log_pow]
    push_cast; ring
  have harc2 : (0 : ℝ) < 2 * arcDen 12 H := by linarith
  have hW2pos : (0 : ℝ) < ((4 : ℝ) ^ E) ^ 2 := by positivity
  have heq : Real.log (((4 : ℝ) ^ E) ^ 2 / (2 * arcDen 12 H))
      = 2 * (E : ℝ) * Real.log 4 - Real.log 2 - 12 * Real.log (Real.log (H : ℝ)) := by
    rw [Real.log_div (ne_of_gt hW2pos) (ne_of_gt harc2), hlogW,
      Real.log_mul (by norm_num) (ne_of_gt harc), hlogarc]
    ring
  have hlogA : 2 * (E : ℝ) * Real.log 4 - Real.log 2
      - 12 * Real.log (Real.log (H : ℝ)) ≤ Real.log (A : ℝ) := by
    have hle : Real.log (((4 : ℝ) ^ E) ^ 2 / (2 * arcDen 12 H)) ≤ Real.log (A : ℝ) :=
      Real.log_le_log (div_pos hW2pos harc2) hkey
    rw [heq] at hle
    exact hle
  -- ⟦the floor of the primorial exponent⟧
  have hEfl : (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) - 1 ≤ (E : ℝ) := by
    have hq : (R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)) < (E : ℚ) + 1 := by
      rw [hEdef]; exact Nat.lt_floor_add_one _
    have hR : ((R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ) : ℚ) : ℝ) < ((E : ℚ) : ℝ) + 1 := by
      exact_mod_cast hq
    push_cast at hR
    linarith
  have heps2 : (1 : ℝ) / 250000 ≤ (R.eps : ℝ) ^ 2 := by nlinarith [hε]
  have hE0 : (0 : ℝ) ≤ (E : ℝ) := Nat.cast_nonneg _
  have hmulE : (1 : ℝ) / 250000 * (R.Hhi : ℝ) ≤ (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) :=
    mul_le_mul_of_nonneg_right heps2 hHhi0.le
  have hEbig : (R.Hhi : ℝ) / 250000 - 1 ≤ (E : ℝ) := by linarith only [hEfl, hmulE]
  -- ⟦the two crude brackets on `H₊`⟧
  have hHle : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hlogmono : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) := Real.log_le_log hH0 hHle
  have hllmono : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log (R.Hhi : ℝ)) :=
    Real.log_le_log hlogH0 hlogmono
  have hllsub : Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (R.Hhi : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hsq : Real.log (R.Hhi : ℝ) ≤ 2 * Real.sqrt (R.Hhi : ℝ) - 2 :=
    cofk_log_le_two_sqrt hHhi0
  have hv : (10 : ℝ) ^ 7 ≤ Real.sqrt (R.Hhi : ℝ) := by
    have h1 : Real.sqrt (((10 : ℝ) ^ 7) ^ 2) ≤ Real.sqrt (R.Hhi : ℝ) :=
      Real.sqrt_le_sqrt (by rw [show (((10 : ℝ) ^ 7) ^ 2) = (10 : ℝ) ^ 14 by norm_num]; exact hHhi)
    rwa [Real.sqrt_sq (by norm_num)] at h1
  have hvsq : Real.sqrt (R.Hhi : ℝ) * Real.sqrt (R.Hhi : ℝ) = (R.Hhi : ℝ) :=
    Real.mul_self_sqrt hHhi0.le
  have hv0 : (0 : ℝ) ≤ Real.sqrt (R.Hhi : ℝ) := Real.sqrt_nonneg _
  have hprod : (10 : ℝ) ^ 7 * Real.sqrt (R.Hhi : ℝ) ≤ (R.Hhi : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right hv hv0) (le_of_eq hvsq)
  -- ⟦the numeral: `log A ≥ H₊/10⁶`⟧
  have hlog4 : (1.3862 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9]
  have hlog2 : Real.log 2 ≤ 0.6932 := by linarith [Real.log_two_lt_d9]
  have hElog : (1.3862 : ℝ) * (E : ℝ) ≤ (E : ℝ) * Real.log 4 := by
    have h := mul_le_mul_of_nonneg_left hlog4 hE0
    linarith only [h]
  have hterm : (R.Hhi : ℝ) / 90200 - 2.7725 ≤ 2 * (E : ℝ) * Real.log 4 := by
    linarith only [hElog, hEbig]
  have hdebit : 12 * Real.log (Real.log (H : ℝ)) ≤ 24 * Real.sqrt (R.Hhi : ℝ) := by
    linarith only [hllmono, hllsub, hsq]
  have hfloor : (R.Hhi : ℝ) / 10 ^ 6 ≤ Real.log (A : ℝ) := by
    linarith only [hterm, hdebit, hlog2, hlogA, hprod, hHhi]
  -- ⟦the exit⟧
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast h8
  have hAs : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hlogAs : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    Real.log_le_log (by linarith) hAs
  linarith

/-- The socket's scale clears the supplier's own scale gate `e^e ≤ X`. -/
theorem cofkL_X_ge_expexp {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseL R M H L q j A s)
    (hε : (1 : ℝ) / 500 ≤ (R.eps : ℝ))
    (hHhi : (10 : ℝ) ^ 14 ≤ (R.Hhi : ℝ))
    (hH : (4000000 : ℝ) ≤ (H : ℝ)) :
    Real.exp (Real.exp 1) ≤ (((A + s : ℕ)) : ℝ) := by
  have hfl := cofkL_logX_floor hb hε hHhi hH
  have h8 : 0 < A := hb.2.2.2.2.2.2.2.1
  have hApos : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by
    have : 1 ≤ A + s := by omega
    have h : (1 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by exact_mod_cast this
    linarith
  have he : Real.exp 1 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have h4 : (3 : ℝ) ≤ (R.Hhi : ℝ) / 10 ^ 6 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    linarith
  have h := Real.exp_le_exp.mpr he
  rwa [Real.exp_log hApos] at h

/-- **⟦THE `μ`-FLOOR⟧** (`cofkL_mu_floor`) — `loglog(A+s) ≥ log H₊ − 14`. -/
theorem cofkL_mu_floor {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseL R M H L q j A s)
    (hε : (1 : ℝ) / 500 ≤ (R.eps : ℝ))
    (hHhi : (10 : ℝ) ^ 14 ≤ (R.Hhi : ℝ))
    (hH : (4000000 : ℝ) ≤ (H : ℝ)) :
    Real.log (R.Hhi : ℝ) - 14 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hfl := cofkL_logX_floor hb hε hHhi hH
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by nlinarith
  have hbigpos : (0 : ℝ) < (R.Hhi : ℝ) / 10 ^ 6 := div_pos hHhi0 (by norm_num)
  have hstep : Real.log ((R.Hhi : ℝ) / 10 ^ 6)
      ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    Real.log_le_log hbigpos hfl
  have hsplit : Real.log ((R.Hhi : ℝ) / 10 ^ 6)
      = Real.log (R.Hhi : ℝ) - Real.log ((10 : ℝ) ^ 6) := by
    rw [Real.log_div (ne_of_gt hHhi0) (by norm_num)]
  have h106 : Real.log ((10 : ℝ) ^ 6) ≤ 14 := by
    rw [show ((10 : ℝ) ^ 6) = (10 : ℝ) ^ (6 : ℕ) by norm_num, Real.log_pow]
    push_cast
    linarith [cofk_log_ten_le]
  rw [hsplit] at hstep
  linarith

set_option maxHeartbeats 1000000 in
-- the `_vt` threshold's five legs are bracketed against `√(log H₊)` in one simplex
/-- **⟦THE THRESHOLD AT THE LINEAR SOCKET⟧** (`cofkL_threshold_at_socket`).
`RbdSupply.pieceFloor_vt_threshold_of_loglog`'s antecedent, discharged from the socket, the
regime, and ONE explicit cushion on the two carried opaque constants.

⟦THE CUSHION IS THE HONEST HOLE⟧ `K_vt` (the `capFreeFloor3_margin_all_chi_vt` witness) has no
effective bound anywhere in the corpus.  It is carried here under `32·K_vt + 32·D ≤ log H₊/4`,
which at the terminal's regime (`3.2·A ≤ loglog H₋`, `162 ≤ A`) permits `K_vt ≤ e^{518}/128`. -/
theorem cofkL_threshold_at_socket {R : ChowlaRegime} {M H L q j A s : ℕ} {Kvt D : ℝ}
    (hb : SocketBaseL R M H L q j A s)
    (hε : (1 : ℝ) / 500 ≤ (R.eps : ℝ))
    (hlo : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hcush : 32 * Kvt + 32 * D ≤ Real.log (R.Hhi : ℝ) / 4) :
    40 * Real.log (Real.log (Real.log (((A + s : ℕ)) : ℝ)))
        + 350 * Real.log (Real.log (H : ℝ))
        + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
        + 2300 + 32 * Kvt + 32 * D
      < Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have h1 : R.Hlo ≤ H := hb.1
  have h2 : H ≤ R.Hhi := hb.2.1
  -- ⟦the design floor, unwound⟧ `log H₋ ≥ e^{518} ≥ 10^8`
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
  -- ⟦propagation to `H` and `H₊`⟧
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hH4 : (4000000 : ℝ) ≤ (H : ℝ) := by linarith
  have hHlo0 : (0 : ℝ) < (R.Hlo : ℝ) := by linarith
  have hlogH : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) := Real.log_le_log hHlo0 hHloH
  have hlogHhi : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) :=
    Real.log_le_log (by linarith) hHHhi
  have hLH8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hhi : ℝ) := by linarith
  have hlogH1 : (1 : ℝ) < Real.log (H : ℝ) := by linarith
  -- ⟦`H₊ ≥ 10^14`, from `log H₊ ≥ 10^8`⟧
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
  -- ⟦the `loglog H` legs⟧ dominated by `1180·√(log H₊)`
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
  have hleg2 : 350 * Real.log (Real.log (H : ℝ))
      + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ))) + 2300
      ≤ 1180 * Real.sqrt LH + 2420 := by linarith
  -- ⟦the close⟧
  have hmargin : 1180 * Real.sqrt LH + 2420 + LH / 4 < μ / 2 + μ / 4 := by
    nlinarith [hprodv, hv, hμ, hv0]
  linarith

/-! ## §4 — ⟦THE ANCHOR-READING PART OF THE CO-FACTOR SUPPLY, DISCHARGED⟧

`m4_supplier_all_chi`'s ~30 binders split cleanly in two: the per-piece cap-free floor (its
`hfloor` slot, the ONLY place the door blocks `Pseq`/`Qseq` are read, and the only place the
character `χ` appears) and the anchor-blind ladder bulk (`Mt`/`kk`/`Dd`/`Xa`,
`TLBlockGates34`, the `S`/`R̄₀` grading).  §4 closes the FIRST half at the linear anchors and
the linear socket, from §2's debit page and §3's threshold. -/

set_option maxHeartbeats 1000000 in
-- the arc-range floor's eight-binder instantiation is elaborated against the socket in one
-- `exact`
/-- **⟦THE CAP-FREE FLOOR AT THE LINEAR ANCHORS⟧** (`cofkL_capFreeFloor_at_socket`).  For every
modulus cap `Qm` there is a floor constant `K_vt ≥ 0` such that, at every socket instance whose
regime carries the terminal's own exports (`ε ≥ 1/500`, `3.2·A ≤ loglog H₋` with `162 ≤ A`) and
whose cushion tolerates `K_vt`, EVERY character mod `q ≤ Qm` and EVERY piece `𝒥 ⊆ {1,2}`
carries `CapFreeFloor3` at the block scale `X = A+s`.

⟦WHAT THIS SETTLES⟧ ⟦COFK-L⟧'s verdict, at the bytes: the L-vs-landed delta of ⟦RULING 9⟧'s
debt is the debit page and the `μ`-floor, and BOTH are paid here.  What remains of
`S16CofactorSupply_L_gk` is anchor-blind and character-free — it reads neither `AdoorL` nor
`s13GK` nor `χ`. -/
theorem cofkL_capFreeFloor_at_socket (K Qm : ℕ) :
    ∃ Kvt : ℝ, 0 ≤ Kvt ∧
      ∀ {R : ChowlaRegime} {M H L q j A s : ℕ} (χ : DirichletCharacter ℂ q),
        SocketBaseL R M H L q j A s → 1 ≤ M → q ≤ Qm →
        (1 : ℝ) / 500 ≤ (R.eps : ℝ) →
        (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        32 * Kvt + 32 * (2 * Real.log (M : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
        ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
            (calQK (AdoorL M) (s13GK K M) M)) (((A + s : ℕ)) : ℝ) := by
  obtain ⟨Kvt, hK0, hK⟩ := capFreeFloor3_pieceDatum_arcDen Qm
  refine ⟨Kvt, hK0, ?_⟩
  intro R M H L q j A s χ hb hM hqQm hε hlo hcush 𝒥 h𝒥
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
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hD0 : (0 : ℝ) ≤ 2 * Real.log (M : ℝ) + Real.log 4 + 50 := by
    have h1' : (0 : ℝ) ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
    have h2' : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hdebit := cofkL_debit_bound K M (((A + s : ℕ)) : ℝ) hM 𝒥 h𝒥
  have hthr := cofkL_threshold_at_socket (Kvt := Kvt)
    (D := 2 * Real.log (M : ℝ) + Real.log 4 + 50) hb hε hlo hcush
  exact hK q H χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 𝒥
    (((A + s : ℕ)) : ℝ) (2 * Real.log (M : ℝ) + Real.log 4 + 50)
    hqQm hlogHe harc hXee hD0 hdebit hthr

end Salt.MR

end
