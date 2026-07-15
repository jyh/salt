/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.Fold
import Salt.BV.Defs
import Salt.BV.AbelCore

/-!
# The SW rung, node S6d — THE GATE: `siegelWalfisz_holds`

Design: `docs/blueprints/sw.md`, S6 row (the S6d cell). This is the final node of
the `sw` rung: it discharges the frozen analytic hypothesis `Salt.BV.SiegelWalfisz`
(the ψ-form Siegel–Walfisz theorem) by de-smoothing the S6c folded estimate
`psi1AP_main_bound` through the first-difference sandwich `psi1AP_sandwich`, then
feeds it to the already-landed `Salt.BV.bounded_gaps_of_siegelWalfisz` to obtain
**unconditional** bounded prime gaps.

## Route (the blueprint's de-smoothing, mechanically)

S6c supplies, for every `A', C' > 0`, constants `K₀, x₀ > 0` with
`|φ(q)·ψ₁(y; q, a) − y²/2| ≤ K₀·y²/(log y)^{A'}` for reduced `a`, `q ≤ (log y)^{C'}`,
`y ≥ x₀` (`psi1AP_main_bound`). We instantiate at `A' := 2A+4`, `C' := C+1`.

The sandwich (`psi1AP_sub_lower`/`psi1AP_sub_upper`) brackets the *discrete*
`ψ(N; q, a) = psiAP N q a = psiAPr (N:ℝ) q a` between forward/backward
difference quotients of `ψ₁` at width `h := N / (log N)^{A+2}`:
`(ψ₁(N) − ψ₁(N−h))/h ≤ ψ(N;q,a) ≤ (ψ₁(N+h) − ψ₁(N))/h`.

Feeding the three main-term estimates and setting `P := (log N)^{A+2}` (so
`N = h·P` and `(log N)^{2A+4} = P²`), both jaws collapse — via the magic
substitution `h·N/P = h²` — to `h²`-scaled error inequalities that close with
`K := 1/2 + K₀·(1 + 2^{2A+4})`. The log-slop `log(N±h) ≥ (log N)/2` (for `N`
large) covers the shifted evaluation points, and the `q ≤ (log(N−h))^{C+1}` side
condition absorbs `2^{C+1} ≤ log N`. Both "N large" thresholds and the
initial finite segment `2 ≤ N < X₁` (bounded crudely by `ψ(N;q,a) ≤ N·log N`)
are absorbed into the single existential constant `K`.

`siegelWalfisz_holds` is the frozen `Salt.BV.SiegelWalfisz` verbatim;
`bounded_gaps_unconditional` is the one-line composition with the landed
`bounded_gaps_of_siegelWalfisz`.
-/

open Salt.LS ArithmeticFunction

namespace Salt.SW

set_option maxHeartbeats 1200000 in
-- The arithmetic core threads two divisions (`/φ`, `/P`) and several `h²`-scaled
-- nlinarith closes; the elaborator needs headroom past the default.
/-- **The de-smoothing arithmetic core.** Given the sandwich bracket
(`hS1`/`hS2`) and the three main-term brackets (`hpp`/`hp0l`/`hpm`) at the geometric
data `N = h·P`, `Q ≤ P`, `1 ≤ P`, the discrepancy `|S − N/φ|` is `≤ Km·N/Q` with
`Km = 1/2 + K₀·(1+D)`. Pure real arithmetic: the substitution `h·N/P = h²`
collapses both jaws to `h²`-scaled inequalities. -/
private lemma gate_arith (N h P Q φ K₀ D S pp p0 pm Km : ℝ)
    (hh : 0 < h) (hP : 0 < P) (hQ : 0 < Q) (hφ : 1 ≤ φ)
    (hK₀ : 0 < K₀) (hD : (16 : ℝ) ≤ D)
    (hPQ : Q ≤ P) (hP1 : 1 ≤ P)
    (hNhP : N = h * P)
    (hKm : Km = 1 / 2 + K₀ * (1 + D))
    (hS1 : h * S ≤ pp - p0)
    (hS2 : p0 - pm ≤ h * S)
    (hpp : φ * pp ≤ (N + h) ^ 2 / 2 + K₀ * (N + h) ^ 2 / P ^ 2)
    (hp0l : N ^ 2 / 2 - K₀ * N ^ 2 / P ^ 2 ≤ φ * p0)
    (hpm : φ * pm ≤ (N - h) ^ 2 / 2 + K₀ * (N - h) ^ 2 * D / P ^ 2) :
    |S - N / φ| ≤ Km * N / Q := by
  have hφ0 : 0 < φ := by linarith
  have hN0 : 0 ≤ N := by nlinarith [hNhP, hh.le, hP.le]
  have hP2 : 0 < P ^ 2 := by positivity
  have hhN_P : h * N / P = h ^ 2 := by
    have h1 : h * N = h ^ 2 * P := by rw [hNhP]; ring
    rw [h1, mul_div_assoc, div_self (ne_of_gt hP), mul_one]
  have hKmh2 : Km * h ^ 2 = h ^ 2 / 2 + K₀ * (1 + D) * h ^ 2 := by rw [hKm]; ring
  have hKmnn : 0 ≤ Km * h ^ 2 := by rw [hKm]; positivity
  have hφKm : Km * h ^ 2 ≤ φ * (Km * h ^ 2) := le_mul_of_one_le_left hKmnn hφ
  have hKh2 : 0 ≤ K₀ * h ^ 2 := mul_nonneg hK₀.le (sq_nonneg h)
  have hDfact : 0 ≤ K₀ * (D - 4) * h ^ 2 :=
    mul_nonneg (mul_nonneg hK₀.le (by linarith)) (sq_nonneg h)
  -- error bounds (each ≤ a multiple of h²)
  have hEp : K₀ * (N + h) ^ 2 / P ^ 2 ≤ 4 * K₀ * h ^ 2 := by
    have hNplus : (N + h) ^ 2 = h ^ 2 * (P + 1) ^ 2 := by rw [hNhP]; ring
    rw [hNplus, div_le_iff₀ hP2]
    have hPsq : (P + 1) ^ 2 ≤ 4 * P ^ 2 := by nlinarith [hP1]
    have e : K₀ * (h ^ 2 * (P + 1) ^ 2) = (K₀ * h ^ 2) * (P + 1) ^ 2 := by ring
    rw [e]
    calc (K₀ * h ^ 2) * (P + 1) ^ 2 ≤ (K₀ * h ^ 2) * (4 * P ^ 2) :=
          mul_le_mul_of_nonneg_left hPsq hKh2
      _ = 4 * K₀ * h ^ 2 * P ^ 2 := by ring
  have hE0 : K₀ * N ^ 2 / P ^ 2 ≤ K₀ * h ^ 2 := by
    have hE0eq : K₀ * N ^ 2 / P ^ 2 = K₀ * h ^ 2 := by
      rw [hNhP, show K₀ * (h * P) ^ 2 = (K₀ * h ^ 2) * P ^ 2 by ring, mul_div_assoc,
        div_self (ne_of_gt hP2), mul_one]
    rw [hE0eq]
  have hEm : K₀ * (N - h) ^ 2 * D / P ^ 2 ≤ K₀ * D * h ^ 2 := by
    have hNminus : (N - h) ^ 2 = h ^ 2 * (P - 1) ^ 2 := by rw [hNhP]; ring
    rw [hNminus, div_le_iff₀ hP2]
    have hPmd : (P - 1) ^ 2 ≤ P ^ 2 := by nlinarith [hP1]
    have e : K₀ * (h ^ 2 * (P - 1) ^ 2) * D = (K₀ * D * h ^ 2) * (P - 1) ^ 2 := by ring
    rw [e]
    calc (K₀ * D * h ^ 2) * (P - 1) ^ 2 ≤ (K₀ * D * h ^ 2) * P ^ 2 :=
          mul_le_mul_of_nonneg_left hPmd (by positivity)
      _ = K₀ * D * h ^ 2 * P ^ 2 := by ring
  -- UPPER jaw
  have hUpP : S ≤ N / φ + Km * N / P := by
    have hstep : pp - p0 ≤ h * N / φ + Km * h ^ 2 := by
      rw [← sub_nonneg]
      have hφc : φ * (h * N / φ + Km * h ^ 2 - (pp - p0))
          = h * N + φ * (Km * h ^ 2) - φ * (pp - p0) := by field_simp
      have hpos' : 0 ≤ h * N + Km * h ^ 2 - φ * (pp - p0) := by
        rw [hKmh2]; nlinarith [hpp, hp0l, hEp, hE0, hDfact]
      have hpos : 0 ≤ h * N + φ * (Km * h ^ 2) - φ * (pp - p0) := by linarith [hpos', hφKm]
      have := (mul_nonneg_iff_of_pos_left hφ0).mp (by rw [hφc]; exact hpos)
      linarith [this]
    have hmul : h * S ≤ h * (N / φ + Km * N / P) := by
      have hrw : h * (N / φ + Km * N / P) = h * N / φ + Km * (h * N / P) := by ring
      rw [hrw, hhN_P]; linarith [hS1, hstep]
    exact le_of_mul_le_mul_left hmul hh
  -- LOWER jaw
  have hLoP : N / φ - Km * N / P ≤ S := by
    have hstep : h * N / φ - Km * h ^ 2 ≤ p0 - pm := by
      rw [← sub_nonneg]
      have hφc : φ * (p0 - pm - (h * N / φ - Km * h ^ 2))
          = φ * (p0 - pm) - h * N + φ * (Km * h ^ 2) := by field_simp; ring
      have hpos' : 0 ≤ φ * (p0 - pm) - h * N + Km * h ^ 2 := by
        rw [hKmh2]; nlinarith [hp0l, hpm, hE0, hEm, hDfact]
      have hpos : 0 ≤ φ * (p0 - pm) - h * N + φ * (Km * h ^ 2) := by linarith [hpos', hφKm]
      have := (mul_nonneg_iff_of_pos_left hφ0).mp (by rw [hφc]; exact hpos)
      linarith [this]
    have hmul : h * (N / φ - Km * N / P) ≤ h * S := by
      have hrw : h * (N / φ - Km * N / P) = h * N / φ - Km * (h * N / P) := by ring
      rw [hrw, hhN_P]; linarith [hS2, hstep]
    exact le_of_mul_le_mul_left hmul hh
  -- combine + relax P → Q
  have hrelax : Km * N / P ≤ Km * N / Q := by
    have hKN : 0 ≤ Km * N := mul_nonneg (by rw [hKm]; positivity) hN0
    gcongr
  rw [abs_le]
  exact ⟨by linarith [hLoP, hrelax], by linarith [hUpP, hrelax]⟩

set_option maxHeartbeats 1200000 in
-- Assembles the sandwich, the three main-bound brackets, the log-slop, and the
-- initial-segment absorption in one pass; needs headroom past the default.
/-- **THE GATE — `siegelWalfisz_holds`.** The frozen `Salt.BV.SiegelWalfisz`
hypothesis, discharged: `|ψ(x; q, a) − x/φ(q)| ≤ K·x/(log x)^A` uniformly for
`q ≤ (log x)^C`, reduced `a`. De-smooths `psi1AP_main_bound` (S6c) through
`psi1AP_sandwich` (S0) at `h = x/(log x)^{A+2}`. -/
theorem siegelWalfisz_holds : Salt.BV.SiegelWalfisz := by
  intro A C hA hC
  -- S6c at A' = 2A+4, C' = C+1
  obtain ⟨K₀, x₀, hK₀pos, hmain⟩ :=
    psi1AP_main_bound (2 * A + 4) (C + 1) (by positivity) (by linarith)
  -- constants
  set D : ℝ := (2 : ℝ) ^ (2 * A + 4) with hDdef
  have hD16 : (16 : ℝ) ≤ D := by
    rw [hDdef]
    calc (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      _ ≤ (2 : ℝ) ^ (2 * A + 4) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  set Km : ℝ := 1 / 2 + K₀ * (1 + D) with hKmdef
  have hKmpos : 0 < Km := by rw [hKmdef]; positivity
  -- thresholds absorbed into K
  set Mlog : ℝ := max 2 ((2 : ℝ) ^ (C + 1)) with hMdef
  set X₁ : ℝ := max (2 * x₀) (Real.exp Mlog) with hX1def
  have hX1pos : 0 < X₁ := lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  set Kinit : ℝ := (Real.log X₁ + 1) * (Real.log X₁) ^ A with hKinitdef
  set K : ℝ := max Km Kinit with hKdef
  have hK0 : 0 ≤ K := le_trans hKmpos.le (le_max_left _ _)
  refine ⟨K, hK0, ?_⟩
  intro x q a hx2 hq hqlog hcop
  -- common facts on x, L
  have hxpos_nat : 0 < x := by omega
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast hxpos_nat
  have hN0 : 0 ≤ (x : ℝ) := le_of_lt hxpos
  set L : ℝ := Real.log (x : ℝ) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; exact Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hL0 : 0 ≤ L := le_of_lt hLpos
  have hLApos : 0 < L ^ A := Real.rpow_pos_of_pos hLpos A
  -- totient facts
  haveI : NeZero q := ⟨hq.ne'⟩
  set φ : ℝ := (q.totient : ℝ) with hφdef
  have hφ1 : 1 ≤ φ := by
    rw [hφdef]; exact_mod_cast (Nat.totient_pos.mpr hq)
  -- residue reduction a → a % q
  have hr : a % q < q := Nat.mod_lt a hq
  have hcopr : Nat.Coprime q (a % q) := ((Salt.BV.coprime_mod_left a q).mp hcop).symm
  have hmm : a % q % q = a % q := Nat.mod_mod_of_dvd a (dvd_refl q)
  have hpsiEq : psiAP x q a = psiAP x q (a % q) := by
    unfold psiAP; simp only [hmm]
  rw [hpsiEq]
  -- goal: |psiAP x q (a%q) - x/φ| ≤ K * x / L^A
  by_cases hbig : X₁ ≤ (x : ℝ)
  · -- BIG case: sandwich + main bound
    -- log threshold facts
    have hexpN : Real.exp Mlog ≤ (x : ℝ) := le_trans (le_max_right _ _) hbig
    have hM_le_L : Mlog ≤ L := by rw [hLdef]; exact (Real.le_log_iff_exp_le hxpos).mpr hexpN
    have hL2 : (2 : ℝ) ≤ L := le_trans (le_max_left _ _) hM_le_L
    have hLC1 : (2 : ℝ) ^ (C + 1) ≤ L := le_trans (le_max_right _ _) hM_le_L
    have hL1 : (1 : ℝ) ≤ L := by linarith
    have hx0N : 2 * x₀ ≤ (x : ℝ) := le_trans (le_max_left _ _) hbig
    -- P, h and geometry
    set P : ℝ := L ^ (A + 2) with hPdef
    have hPpos : 0 < P := Real.rpow_pos_of_pos hLpos _
    have hP1 : (1 : ℝ) ≤ P := by
      rw [hPdef]
      calc (1 : ℝ) = (1 : ℝ) ^ (A + 2) := (Real.one_rpow _).symm
        _ ≤ L ^ (A + 2) := Real.rpow_le_rpow zero_le_one hL1 (by positivity)
    have hPQ : L ^ A ≤ P := by
      rw [hPdef]; exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hP2ge : (2 : ℝ) ≤ P := by
      rw [hPdef]
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ (2 : ℝ) ^ (A + 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ ≤ L ^ (A + 2) := Real.rpow_le_rpow (by norm_num) hL2 (by positivity)
    set h : ℝ := (x : ℝ) / P with hhdef
    have hhpos : 0 < h := div_pos hxpos hPpos
    have hNhP : (x : ℝ) = h * P := by rw [hhdef, div_mul_cancel₀ _ (ne_of_gt hPpos)]
    have hh_le_half : h ≤ (x : ℝ) / 2 := by
      rw [hhdef]; exact div_le_div_of_nonneg_left hN0 (by norm_num) hP2ge
    have hNhalf : (x : ℝ) / 2 ≤ (x : ℝ) - h := by linarith [hh_le_half]
    have hNmh_pos : 0 ≤ (x : ℝ) - h := by linarith [hNhalf, hN0]
    -- range facts for the main bound (x₀ ≤ each point)
    have hx0half : x₀ ≤ (x : ℝ) / 2 := by linarith [hx0N]
    have hxge_N : x₀ ≤ (x : ℝ) := by linarith [hx0half, hN0]
    have hxge_Nph : x₀ ≤ (x : ℝ) + h := by linarith [hxge_N, hhpos]
    have hxge_Nmh : x₀ ≤ (x : ℝ) - h := by linarith [hNhalf, hx0half]
    -- log-slop
    have hlogNph : L ≤ Real.log ((x : ℝ) + h) := by
      rw [hLdef]; exact Real.log_le_log hxpos (by linarith [hhpos])
    have hlogNmh_ge : L / 2 ≤ Real.log ((x : ℝ) - h) := by
      have hlog_half : Real.log ((x : ℝ) / 2) ≤ Real.log ((x : ℝ) - h) :=
        Real.log_le_log (by positivity) hNhalf
      have hlogN2 : Real.log ((x : ℝ) / 2) = L - Real.log 2 := by
        rw [Real.log_div (ne_of_gt hxpos) (by norm_num), ← hLdef]
      have hlog2_1 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      have hlog2_small : Real.log 2 ≤ L / 2 := le_trans hlog2_1 (by linarith [hL2])
      linarith [hlog_half, hlogN2, hlog2_small]
    have hlogNmh_pos : 0 < Real.log ((x : ℝ) - h) := by linarith [hlogNmh_ge, hL2]
    -- power identities
    have hLP2 : L ^ (2 * A + 4) = P ^ 2 := by
      rw [hPdef, sq, ← Real.rpow_add hLpos]; congr 1; ring
    have hP2pos : 0 < P ^ 2 := by positivity
    -- (log(N+h))^(2A+4) ≥ P²
    have hLogNph_pow : P ^ 2 ≤ (Real.log ((x : ℝ) + h)) ^ (2 * A + 4) := by
      rw [← hLP2]; exact Real.rpow_le_rpow hL0 hlogNph (by positivity)
    -- (log(N-h))^(2A+4) ≥ P²/D  (via P² ≤ D·(log(N-h))^(2A+4))
    have hL2pow : (L / 2) ^ (2 * A + 4) = P ^ 2 / D := by
      rw [Real.div_rpow hL0 (by norm_num), hLP2, hDdef]
    have hDpos : 0 < D := by rw [hDdef]; positivity
    have hP2DW : P ^ 2 ≤ D * (Real.log ((x : ℝ) - h)) ^ (2 * A + 4) := by
      have hL2W : (L / 2) ^ (2 * A + 4) ≤ (Real.log ((x : ℝ) - h)) ^ (2 * A + 4) :=
        Real.rpow_le_rpow (by linarith [hLpos]) hlogNmh_ge (by positivity)
      have hP2eqD : P ^ 2 = D * (L / 2) ^ (2 * A + 4) := by
        rw [hL2pow, mul_div_cancel₀ _ (ne_of_gt hDpos)]
      rw [hP2eqD]; exact mul_le_mul_of_nonneg_left hL2W hDpos.le
    -- q-conditions at the three points
    have hqL : (q : ℝ) ≤ L ^ C := by rw [hLdef]; exact hqlog
    have hqcond_N : (q : ℝ) ≤ L ^ (C + 1) :=
      le_trans hqL (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
    have hqcond_Nph : (q : ℝ) ≤ (Real.log ((x : ℝ) + h)) ^ (C + 1) :=
      le_trans hqcond_N (Real.rpow_le_rpow hL0 hlogNph (by positivity))
    have hqcond_Nmh : (q : ℝ) ≤ (Real.log ((x : ℝ) - h)) ^ (C + 1) := by
      have hLC1_pow : L ^ (C + 1) = L ^ C * L := by rw [Real.rpow_add hLpos, Real.rpow_one]
      have hL2C : (L / 2) ^ (C + 1) = L ^ (C + 1) / 2 ^ (C + 1) := Real.div_rpow hL0 (by norm_num) _
      have hLCLe : L ^ C ≤ (L / 2) ^ (C + 1) := by
        rw [hL2C, le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _), hLC1_pow]
        exact mul_le_mul_of_nonneg_left hLC1 (Real.rpow_nonneg hL0 C)
      exact le_trans hqL (le_trans hLCLe
        (Real.rpow_le_rpow (by linarith [hLpos]) hlogNmh_ge (by positivity)))
    -- the three main-bound brackets
    have hqN' : (q : ℝ) ≤ (Real.log (x : ℝ)) ^ (C + 1) := by rw [← hLdef]; exact hqcond_N
    have hb0 := hmain q (a := a % q) hr hcopr (x := (x : ℝ)) hxge_N hqN'
    have hbp := hmain q (a := a % q) hr hcopr (x := (x : ℝ) + h) hxge_Nph hqcond_Nph
    have hbm := hmain q (a := a % q) hr hcopr (x := (x : ℝ) - h) hxge_Nmh hqcond_Nmh
    -- rewrite log ↑x = L and collapse denominators
    rw [← hLdef, hLP2] at hb0
    -- hp0l
    have hp0l : (x : ℝ) ^ 2 / 2 - K₀ * (x : ℝ) ^ 2 / P ^ 2 ≤ φ * psi1AP (x : ℝ) q (a % q) := by
      have := (abs_le.mp hb0).1; rw [← hφdef] at this; linarith [this]
    -- hpp
    have hppbound : K₀ * ((x : ℝ) + h) ^ 2 / (Real.log ((x : ℝ) + h)) ^ (2 * A + 4)
        ≤ K₀ * ((x : ℝ) + h) ^ 2 / P ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) hP2pos hLogNph_pow
    have hpp : φ * psi1AP ((x : ℝ) + h) q (a % q)
        ≤ ((x : ℝ) + h) ^ 2 / 2 + K₀ * ((x : ℝ) + h) ^ 2 / P ^ 2 := by
      have := (abs_le.mp hbp).2; rw [← hφdef] at this; linarith [this, hppbound]
    -- hpm
    have hden_pos : 0 < (Real.log ((x : ℝ) - h)) ^ (2 * A + 4) :=
      Real.rpow_pos_of_pos hlogNmh_pos _
    have hmbound : K₀ * ((x : ℝ) - h) ^ 2 / (Real.log ((x : ℝ) - h)) ^ (2 * A + 4)
        ≤ K₀ * ((x : ℝ) - h) ^ 2 * D / P ^ 2 := by
      rw [div_le_div_iff₀ hden_pos hP2pos]
      calc K₀ * ((x : ℝ) - h) ^ 2 * P ^ 2
          ≤ K₀ * ((x : ℝ) - h) ^ 2 * (D * (Real.log ((x : ℝ) - h)) ^ (2 * A + 4)) :=
            mul_le_mul_of_nonneg_left hP2DW (by positivity)
        _ = K₀ * ((x : ℝ) - h) ^ 2 * D * (Real.log ((x : ℝ) - h)) ^ (2 * A + 4) := by ring
    have hpm : φ * psi1AP ((x : ℝ) - h) q (a % q)
        ≤ ((x : ℝ) - h) ^ 2 / 2 + K₀ * ((x : ℝ) - h) ^ 2 * D / P ^ 2 := by
      have := (abs_le.mp hbm).2; rw [← hφdef] at this; linarith [this, hmbound]
    -- the sandwich brackets
    have hpsiAPr : psiAPr (x : ℝ) q (a % q) = psiAP x q (a % q) := by
      rw [psiAPr, Nat.floor_natCast]
    have hS1 : h * psiAP x q (a % q)
        ≤ psi1AP ((x : ℝ) + h) q (a % q) - psi1AP (x : ℝ) q (a % q) := by
      have hlow := psi1AP_sub_lower (x := (x : ℝ)) (y := (x : ℝ) + h) hN0 (by linarith [hhpos])
        q (a % q)
      rw [hpsiAPr, show (x : ℝ) + h - (x : ℝ) = h by ring] at hlow
      exact hlow
    have hS2 : psi1AP (x : ℝ) q (a % q) - psi1AP ((x : ℝ) - h) q (a % q)
        ≤ h * psiAP x q (a % q) := by
      have hup := psi1AP_sub_upper (x := (x : ℝ) - h) (y := (x : ℝ)) hNmh_pos (by linarith [hhpos])
        q (a % q)
      rw [hpsiAPr, show (x : ℝ) - ((x : ℝ) - h) = h by ring] at hup
      exact hup
    -- apply the arithmetic core, then relax Km → K
    have hcore := gate_arith (x : ℝ) h P (L ^ A) φ K₀ D (psiAP x q (a % q))
      (psi1AP ((x : ℝ) + h) q (a % q)) (psi1AP (x : ℝ) q (a % q))
      (psi1AP ((x : ℝ) - h) q (a % q)) Km hhpos hPpos hLApos hφ1 hK₀pos hD16 hPQ hP1 hNhP
      hKmdef hS1 hS2 hpp hp0l hpm
    calc |psiAP x q (a % q) - (x : ℝ) / φ|
        ≤ Km * (x : ℝ) / L ^ A := hcore
      _ ≤ K * (x : ℝ) / L ^ A :=
          (div_le_div_iff_of_pos_right hLApos).mpr
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hN0)
  · -- SMALL case: crude bound ψ(N;q,a) ≤ N·log N
    have hxX1 : (x : ℝ) < X₁ := lt_of_not_ge hbig
    have hLlog : L ≤ Real.log X₁ := by rw [hLdef]; exact Real.log_le_log hxpos (le_of_lt hxX1)
    -- crude: psiAP ≤ x·L
    have hcrude : psiAP x q (a % q) ≤ (x : ℝ) * L := by
      rw [hLdef]
      calc psiAP x q (a % q)
          ≤ ∑ _n ∈ Finset.Icc 1 x, Real.log (x : ℝ) := by
            unfold psiAP
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun n _ _ => vonMangoldt_nonneg)) ?_
            refine Finset.sum_le_sum (fun n hn => ?_)
            rw [Finset.mem_Icc] at hn
            exact le_trans vonMangoldt_le_log
              (Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2))
        _ = (x : ℝ) * Real.log (x : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            push_cast [Nat.add_sub_cancel]; ring
    have hAP0 : 0 ≤ psiAP x q (a % q) := Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
    have hφpos : 0 < φ := by linarith [hφ1]
    have hdivle : (x : ℝ) / φ ≤ (x : ℝ) := div_le_self hN0 hφ1
    have hdiv0 : 0 ≤ (x : ℝ) / φ := div_nonneg hN0 (by linarith [hφ1])
    -- |psiAP - x/φ| ≤ x·L + x
    have habs : |psiAP x q (a % q) - (x : ℝ) / φ| ≤ (x : ℝ) * L + (x : ℝ) := by
      rw [abs_le]
      constructor
      · linarith [hAP0, hdivle, hdiv0]
      · linarith [hcrude, hdiv0]
    -- x·L + x ≤ K · x / L^A
    have hKL : (L + 1) * L ^ A ≤ K := by
      calc (L + 1) * L ^ A ≤ (Real.log X₁ + 1) * (Real.log X₁) ^ A := by
            apply mul_le_mul (by linarith [hLlog])
              (Real.rpow_le_rpow hL0 hLlog hA.le) hLApos.le (by linarith [hLlog, hL0])
        _ = Kinit := (hKinitdef).symm
        _ ≤ K := le_max_right _ _
    refine le_trans habs ?_
    rw [le_div_iff₀ hLApos]
    calc ((x : ℝ) * L + (x : ℝ)) * L ^ A
        = (x : ℝ) * ((L + 1) * L ^ A) := by ring
      _ ≤ (x : ℝ) * K := mul_le_mul_of_nonneg_left hKL hN0
      _ = K * (x : ℝ) := mul_comm _ _

/-- **Bounded prime gaps, unconditionally.** The one-line composition of the
just-landed gate with the already-landed `Salt.BV.bounded_gaps_of_siegelWalfisz`
(the full Bombieri–Vinogradov + Maynard chain). This is the headline the whole
project builds toward: infinitely many pairs of primes within a bounded gap. -/
theorem bounded_gaps_unconditional :
    ∃ C : ℕ, ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-(C : ℤ)) (C : ℤ) :=
  Salt.BV.bounded_gaps_of_siegelWalfisz siegelWalfisz_holds

end Salt.SW
