/-
Copyright (c) 2026 Salt contributors.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Salt.MR.HExit

/-!
# The uniform-constant hoist of the S1′ representation (A-7)

`prop21_unconditional_clean` (`HExit.lean`) states the S1′ representation with the
E-grade constants INSIDE the `X`-quantifier:

  `∃ X₀, ∀ {X h c₀ y η}, gates → ∃ C_E C_R, ‖…‖ ≤ C_E·A(X) + C_R·B(X)`.

The `hCenter` supply (the ball-sup centre) needs one constant pair for a whole RANGE of
scales (`k ∈ [⌊X⌋₊, N]`), i.e. the additive restatement

  `∃ X₀ C_E C_R, 0 ≤ C_E ∧ 0 ≤ C_R ∧ ∀ {X h c₀ y η}, gates → ‖…‖ ≤ C_E·A(X) + C_R·B(X)`.

**The hoist is sound**: every constant in the landed chain traces to an `X`-free source.

* the E-constant `C_E` — `mult_shiu_MS_EXIT` (`MultShiu.lean`) is ALREADY uniform:
  `∃ C_E, ∀ x y, 8 ≤ y → y ≤ x → …`, the constant obtained from `mult_shiu_MS_A` +
  `mult_shiu_MS_B` (Mertens/`ms_b_smooth_factor` constants) before any scale is named.
  It depends on the datum `g` and the twist `t₀` only, both of which are already
  parameters of the theorem, fixed before `X`.
* the ramp constant `C_R` — `rampSliverMass_bound_unconditional` obtains its `C` from
  `ramp_sliver_bound` (concretely `C = 4·C_cheb`) with `C_cheb` the SHORT-INTERVAL
  Chebyshev constant of `shortInterval_vonMangoldt_le` (concretely `250`), which is
  obtained BEFORE any `X` is named (`ShortIntervalPsi.lean:407`).  So `C_R = 32·C_cheb`
  is a numeral-grade absolute constant, `g`-free and `X`-free.

The obstruction is purely *statement-shaped*: the landed stones package their constants
in `∃` under the `X`-binder, so the value is opaque to a caller.  This file re-runs the
same proofs with the `∃`-introductions hoisted — no landed line is edited, no landed
statement is weakened.  Concretely:

* `ramp_sliver_bound_const` — `RampSliver.ramp_sliver_bound` with the witness `4·C_cheb`
  made explicit in the statement (same proof);
* `window_regime_of_large` — the per-window regime discharge of
  `prop21_unconditional_clean`, extracted as a standalone lemma (same proof);
* `prop21_unconditional_ofC` — `prop21_unconditional` with the MS-EXIT constant supplied
  as a hypothesis instead of `∃`-eliminated inside (same proof);
* `prop21_unconditional_uniform` — THE STONE: the hoisted form above;
* `prop21_uniform_at_scale` — the same at the recommended pin
  `h = X/√(log X)`, `c₀ = 1 + 1/log X`, `y = (log X)^4`, `η = 1/log y`, with every gate
  discharged from a single threshold (the shape the A-9 assembly consumes).
-/

namespace Salt.MR

open Complex MeasureTheory Set
open ArithmeticFunction
open scoped BigOperators LSeries.notation

/-! ## The ramp leg with the constant explicit -/

/-- **The `l`-side elementary count** (the `RampSliver` private helper, re-stated here so
the explicit-constant re-run below is self-contained).  The number of window partners
`l ∈ (⌊y⌋, ⌊y+y·h/X⌋]` is `≤ y·h/X + 1`. -/
private lemma lcard_le_of_pos {X h y : ℝ} (hy : (0 : ℝ) ≤ y) (hh : (0 : ℝ) ≤ h)
    (hX : (0 : ℝ) < X) :
    ((Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊).card : ℝ) ≤ y * h / X + 1 := by
  have hnn : (0 : ℝ) ≤ y + y * h / X := by positivity
  have hmono : ⌊y⌋₊ ≤ ⌊y + y * h / X⌋₊ :=
    Nat.floor_mono (by nlinarith [div_nonneg (mul_nonneg hy hh) hX.le])
  rw [Nat.card_Ioc, Nat.cast_sub hmono]
  have hup : (⌊y + y * h / X⌋₊ : ℝ) ≤ y + y * h / X := Nat.floor_le hnn
  have hlo : y - 1 < (⌊y⌋₊ : ℝ) := by have := Nat.lt_floor_add_one y; linarith
  linarith

/-- **The ramp sliver bound with the constant EXPLICIT** — `ramp_sliver_bound` with its
`∃ C` witness `4·C_cheb` written into the statement.  Same hypotheses, same proof; the
only change is that the constant is now visible to the caller, which is what the uniform
hoist needs (the landed `∃ C` is opaque under the `X`-binder). -/
theorem ramp_sliver_bound_const (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X h y : ℝ} (hX : Real.exp 1 ≤ X) (hh : h = X / Real.sqrt (Real.log X))
    (hy10 : (10 : ℝ) ≤ y) (hygate : Real.sqrt (Real.log X) ≤ y)
    {C_cheb : ℝ} (hCheb : 0 ≤ C_cheb)
    (hgrain : ∀ l ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊,
        (∑ k ∈ Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊, vonMangoldt k)
          ≤ C_cheb * (h / (l : ℝ))) :
    rampSliverMass g X h y ≤ 4 * C_cheb * (X / Real.log X) * Real.log y := by
  -- basic regime facts
  set LX : ℝ := Real.log X with hLdef
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL1 : (1 : ℝ) ≤ LX := by
    rw [hLdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hLpos : (0 : ℝ) < LX := by linarith
  set sq : ℝ := Real.sqrt LX with hsqdef
  have hsqpos : (0 : ℝ) < sq := Real.sqrt_pos.mpr hLpos
  have hsq1 : (1 : ℝ) ≤ sq := by
    rw [hsqdef, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hL1
  have hsqsq : sq * sq = LX := Real.mul_self_sqrt hLpos.le
  have hhval : h = X / sq := by rw [hh, hsqdef]
  have hhpos : (0 : ℝ) < h := by rw [hhval]; positivity
  have hhnn : (0 : ℝ) ≤ h := hhpos.le
  have hhX : h ≤ X := by rw [hhval, div_le_iff₀ hsqpos]; nlinarith
  have hypos : (0 : ℝ) < y := by linarith
  have hy2 : (2 : ℝ) ≤ y := by linarith
  have hygate' : sq ≤ y := by rw [hsqdef]; exact hygate
  -- log(2y) ≤ 2 log y
  have hlogy_pos : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlog2y : Real.log (2 * y) ≤ 2 * Real.log y := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2
    linarith
  have hlog2y_nn : (0 : ℝ) ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  -- the per-partner bound `M`
  set M : ℝ := C_cheb * (h / y) * Real.log (2 * y) with hMdef
  have hM_nn : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  -- each `l`-fiber is `≤ M`
  have hfiber : ∀ l ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊,
      (∑ k ∈ Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊,
        ‖lambdaLin (restrictAbove y g) k‖ * ‖lambdaLin (restrictAbove y g) l‖) ≤ M := by
    intro l hl
    rw [Finset.mem_Ioc] at hl
    have hlgt : y < (l : ℝ) := by
      have := Nat.lt_floor_add_one y
      have hc : (⌊y⌋₊ : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hl.1
      linarith
    have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
    have hle2y : (l : ℝ) ≤ 2 * y := by
      have h1 : (l : ℝ) ≤ (⌊y + y * h / X⌋₊ : ℝ) := by exact_mod_cast hl.2
      have h2 : (⌊y + y * h / X⌋₊ : ℝ) ≤ y + y * h / X :=
        Nat.floor_le (by positivity)
      have h3 : y * h / X ≤ y := by
        rw [div_le_iff₀ hXpos]; nlinarith
      linarith
    -- factor out ‖Λ_ℓ l‖
    rw [← Finset.sum_mul]
    -- the k-sum ≤ C_cheb·(h/l) via lambdaLin ≤ Λ and the grain
    have hksum : (∑ k ∈ Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊,
        ‖lambdaLin (restrictAbove y g) k‖) ≤ C_cheb * (h / (l : ℝ)) := by
      refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (hgrain l (Finset.mem_Ioc.mpr hl))
      exact lambdaLin_norm_le (restrictAbove y g) (restrictAbove_norm_le hg) k
    -- ‖Λ_ℓ l‖ ≤ log(2y)
    have hlmass : ‖lambdaLin (restrictAbove y g) l‖ ≤ Real.log (2 * y) :=
      le_trans (lambdaLin_norm_le (restrictAbove y g) (restrictAbove_norm_le hg) l)
        (le_trans vonMangoldt_le_log (Real.log_le_log hlpos hle2y))
    -- combine
    calc (∑ k ∈ Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊,
            ‖lambdaLin (restrictAbove y g) k‖) * ‖lambdaLin (restrictAbove y g) l‖
        ≤ (C_cheb * (h / (l : ℝ))) * Real.log (2 * y) :=
          mul_le_mul hksum hlmass (norm_nonneg _) (by positivity)
      _ ≤ (C_cheb * (h / y)) * Real.log (2 * y) := by
          gcongr
      _ = M := by rw [hMdef]
  -- sum over `l`, then the geometric assembly
  have hsum_le : rampSliverMass g X h y
      ≤ ((Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊).card : ℝ) * M := by
    rw [rampSliverMass]
    refine le_trans (Finset.sum_le_card_nsmul _ _ M hfiber) ?_
    rw [nsmul_eq_mul]
  refine le_trans hsum_le ?_
  -- (card)·M ≤ (y·h/X + 1)·M ≤ 4·C_cheb·(X/L)·log y
  have hcard := lcard_le_of_pos (le_of_lt hypos) hhnn hXpos
  have hstep1 : ((Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊).card : ℝ) * M ≤ (y * h / X + 1) * M :=
    mul_le_mul_of_nonneg_right hcard hM_nn
  refine le_trans hstep1 ?_
  -- geometric part: (y·h/X + 1)·(h/y) ≤ 2·(X/L)
  have hgeom : (y * h / X + 1) * (h / y) ≤ 2 * (X / LX) := by
    have hexp : (y * h / X + 1) * (h / y) = h * h / X + h / y := by
      field_simp
    rw [hexp]
    have h_hhX : h * h / X = X / LX := by
      rw [hhval]; field_simp; nlinarith [hsqsq]
    have h_hy_le : h / y ≤ X / LX := by
      rw [hhval, div_div]
      rw [div_le_div_iff₀ (by positivity) hLpos]
      nlinarith [hsqsq, mul_le_mul_of_nonneg_left hygate' hsqpos.le]
    rw [h_hhX]; linarith
  -- assemble: M = C_cheb·(h/y)·log(2y), so (y·h/X+1)·M = C_cheb·log(2y)·((y·h/X+1)·(h/y))
  have hrw : (y * h / X + 1) * M = C_cheb * Real.log (2 * y) * ((y * h / X + 1) * (h / y)) := by
    rw [hMdef]; ring
  rw [hrw]
  calc C_cheb * Real.log (2 * y) * ((y * h / X + 1) * (h / y))
      ≤ C_cheb * Real.log (2 * y) * (2 * (X / LX)) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ C_cheb * (2 * Real.log y) * (2 * (X / LX)) := by
        gcongr
    _ = 4 * C_cheb * (X / LX) * Real.log y := by ring

/-! ## The window-regime discharge, extracted -/

/-- **The `log⁴ = o(√X)` threshold (∃-packaged)** — the `HExit` private helper
`logpow4_le_sqrt_eventually`, re-stated here (a `private` declaration is not visible
across modules).  There is an `X₁` beyond which `(log X)⁴ ≤ √X/2`. -/
private lemma logpow4_le_sqrt_ev :
    ∃ X₁ : ℝ, ∀ X : ℝ, X₁ ≤ X → (Real.log X) ^ 4 ≤ Real.sqrt X / 2 := by
  have hlo : (fun x : ℝ => Real.log x ^ (4 : ℝ)) =o[Filter.atTop] fun x : ℝ => x ^ (1 / 2 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop 4 (by norm_num : (0 : ℝ) < 1 / 2)
  have hbound := hlo.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [Filter.eventually_atTop] at hbound
  obtain ⟨a, ha⟩ := hbound
  refine ⟨max a 1, fun X hX => ?_⟩
  have hXa : a ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hlogXnn : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
  have hkey := ha X hXa
  have h1nn : (0 : ℝ) ≤ Real.log X ^ (4 : ℝ) := Real.rpow_nonneg hlogXnn 4
  have h2nn : (0 : ℝ) ≤ X ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg h1nn, Real.norm_of_nonneg h2nn,
    show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← Real.sqrt_eq_rpow] at hkey
  linarith [hkey]

/-- **The per-window regime, discharged from the outer regime** — the `hreg` block of
`prop21_unconditional_clean` extracted as a standalone lemma (same proof).  For
`X ≥ 17179869184` with `(log X)⁴ ≤ √X/2`, the `h`-pin and `10 ≤ y ≤ √X`, every window
partner `l ∈ (⌊y⌋, ⌊y+y·h/X⌋]` satisfies the three `rampSliverMass` grain conditions. -/
theorem window_regime_of_large {X h y : ℝ} (hXbig : (17179869184 : ℝ) ≤ X)
    (hlog4 : (Real.log X) ^ 4 ≤ Real.sqrt X / 2)
    (hh : h = X / Real.sqrt (Real.log X)) (hy10 : (10 : ℝ) ≤ y) (hyX : y ≤ Real.sqrt X) :
    ∀ l ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊,
      (65536 : ℝ) ≤ X / (l : ℝ) ∧
      X / (l : ℝ) ≤ (h / (l : ℝ)) * Real.sqrt (Real.sqrt (Real.sqrt (X / (l : ℝ)))) ∧
      h / (l : ℝ) ≤ X / (l : ℝ) := by
  -- outer-regime facts
  have hX : Real.exp 1 ≤ X :=
    (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 17179869184)).trans hXbig
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hsqlogX : (0 : ℝ) < Real.sqrt (Real.log X) := Real.sqrt_pos.mpr hlogXpos
  have hsqge1 : (1 : ℝ) ≤ Real.sqrt (Real.log X) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlogX1
  have hh0 : (0 : ℝ) < h := by rw [hh]; exact div_pos hXpos hsqlogX
  have hhX : h ≤ X := by rw [hh, div_le_iff₀ hsqlogX]; nlinarith [hsqge1, hXpos]
  have hy0 : (0 : ℝ) < y := by linarith
  have hsqrtXnn : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hsqrtXge : (131072 : ℝ) ≤ Real.sqrt X := by
    have h1 : ((131072 : ℝ)) ^ 2 ≤ X := by nlinarith [hXbig]
    calc (131072 : ℝ) = Real.sqrt (131072 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt X := Real.sqrt_le_sqrt h1
  intro l hl
  rw [Finset.mem_Ioc] at hl
  obtain ⟨hllo, hlhi⟩ := hl
  have hl1 : 1 ≤ l := by omega
  have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl1
  have hyhX_nn : (0 : ℝ) ≤ y + y * h / X :=
    add_nonneg hy0.le (div_nonneg (mul_nonneg hy0.le hh0.le) hXpos.le)
  have hyh : y * h / X ≤ y := by
    rw [mul_div_assoc]
    have hhX1 : h / X ≤ 1 := by rw [div_le_one hXpos]; exact hhX
    calc y * (h / X) ≤ y * 1 := mul_le_mul_of_nonneg_left hhX1 hy0.le
      _ = y := mul_one y
  have hle2sqrt : (l : ℝ) ≤ 2 * Real.sqrt X := by
    have hlhiR : (l : ℝ) ≤ y + y * h / X := by
      calc (l : ℝ) ≤ (⌊y + y * h / X⌋₊ : ℝ) := by exact_mod_cast hlhi
        _ ≤ y + y * h / X := Nat.floor_le hyhX_nn
    linarith [hyh, hyX]
  have hXl_ge : Real.sqrt X / 2 ≤ X / (l : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hlpos]
    nlinarith [Real.mul_self_sqrt hXpos.le, mul_le_mul_of_nonneg_left hle2sqrt hsqrtXnn]
  have hXlpos : (0 : ℝ) < X / (l : ℝ) := div_pos hXpos hlpos
  refine ⟨?_, ?_, ?_⟩
  · -- (a) 65536 ≤ X/l
    have h65 : (65536 : ℝ) ≤ Real.sqrt X / 2 := by linarith [hsqrtXge]
    linarith [hXl_ge]
  · -- (b) X/l ≤ (h/l)·√√√(X/l)
    set Xl := X / (l : ℝ) with hXldef
    set s := Real.sqrt (Real.sqrt (Real.sqrt Xl)) with hsdef
    have hs8 : s ^ 8 = Xl := by
      have ha4 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt Xl) := Real.sqrt_nonneg _
      have ha2 : (0 : ℝ) ≤ Real.sqrt Xl := Real.sqrt_nonneg _
      have e2 : s ^ 2 = Real.sqrt (Real.sqrt Xl) := Real.sq_sqrt ha4
      have e4 : s ^ 4 = Real.sqrt Xl := by
        rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, e2, Real.sq_sqrt ha2]
      rw [show s ^ 8 = (s ^ 4) ^ 2 by ring, e4, Real.sq_sqrt hXlpos.le]
    have hspos : (0 : ℝ) < s :=
      Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hXlpos))
    have hkey8 : (Real.sqrt (Real.log X)) ^ 8 ≤ s ^ 8 := by
      rw [hs8, show (Real.sqrt (Real.log X)) ^ 8 = ((Real.sqrt (Real.log X)) ^ 2) ^ 4 by ring,
        Real.sq_sqrt hlogXpos.le]
      exact le_trans hlog4 hXl_ge
    have hkey : Real.sqrt (Real.log X) ≤ s :=
      le_of_pow_le_pow_left₀ (by norm_num) hspos.le hkey8
    have hhl : h / (l : ℝ) = Xl / Real.sqrt (Real.log X) := by
      rw [hXldef, hh, div_right_comm]
    rw [hhl, div_mul_eq_mul_div, le_div_iff₀ hsqlogX]
    exact mul_le_mul_of_nonneg_left hkey hXlpos.le
  · -- (c) h/l ≤ X/l
    exact div_le_div_of_nonneg_right hhX hlpos.le

/-! ## The S1′ representation with the MS-EXIT constant supplied -/

/-- **`prop21_unconditional` with the E-constant SUPPLIED** — identical statement and
identical proof, except that the MS-EXIT constant `C_E` and its uniform bound `hCE`
(`mult_shiu_MS_EXIT`, which is ALREADY `∀ x y` uniform) arrive as hypotheses instead of
being `∃`-eliminated inside the proof.  That is the whole content of the hoist: the
landed stone's `∃ C_E` sits under the `X`-binder of every consumer, this one does not.
The datum is carried as `d` with `hd : d = g·(·)^{-it₀}` purely to keep the hypothesis
readable. -/
theorem prop21_unconditional_ofC (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ)
    (d : ℕ → ℂ) (hd : d = fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I))
    {X h c₀ y η E_ramp C_E : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc₀ : 1 < c₀)
    (hη : η = 1 / Real.log y) (hc' : 0 < c₀ - 2 * η) (hy10 : 10 ≤ y) (hyX : y ≤ Real.sqrt X)
    (hCE : ∀ x z : ℝ, 8 ≤ z → z ≤ x →
      (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter (fun q => q.1 * q.2 ≤ ⌊x⌋₊),
            ‖ellLin (restrictBelow z d) q.1‖ * ‖ellLin (restrictAbove z d) q.2‖
              / (q.2 : ℝ) ^ (1 / Real.log z))
          + (∫ α in (0 : ℝ)..(1 / Real.log z),
              ∑ q ∈ (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter
                  (fun q => q.1 * q.2.1 * q.2.2 ≤ ⌊x⌋₊),
                ‖ellLin (restrictBelow z d) q.1‖
                  * (‖lambdaLin (restrictAbove z d) q.2.1‖ / (q.2.1 : ℝ) ^ α)
                  * ‖ellLin (restrictAbove z d) q.2.2‖ / (q.2.2 : ℝ) ^ (2 * (1 / Real.log z) + α))
        ≤ C_E * (x / Real.log x) * Real.log z)
    (hsliver : ‖rampTerm d X h y η‖ ≤ E_ramp) :
    ‖(∑' n, seamCoeff (ellLin g) (fun _ => 1) t₀ n * (hatK X h n : ℂ))
        - prop21RHS d t₀ X h c₀ y η‖
      ≤ C_E * ((X + h) / Real.log (X + h)) * Real.log y + E_ramp := by
  subst hd
  set gtw := fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I) with hgtwdef
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hη0 : (0 : ℝ) ≤ η := by rw [hη]; positivity
  have hgtw : ∀ p, p.Prime → ‖gtw p‖ ≤ 1 := by
    intro p hp
    have hval : gtw p = g p * (p : ℂ) ^ (-(t₀ : ℂ) * I) := by rw [hgtwdef]
    rw [hval, norm_mul, norm_twist t₀ hp.one_lt.le, mul_one]
    exact hg p hp
  have hyXh : y ≤ X + h := by
    have hsqrtle : Real.sqrt X ≤ X := by
      have h1 : Real.sqrt X ≤ Real.sqrt (X * X) := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_mul_self (by linarith)] at h1
    linarith
  refine prop21_analog (ellLin_norm_le_one g hg) t₀ hX hh hc₀ ?_
  rw [← prop21_contour_leg_unwindowed (ellLin_norm_le_one g hg) t₀ hX hh hc₀]
  -- the collapse (V5-2c at the centered datum) and the seam reconciliation (V5-4)
  have hcol := aligned_collapse_assembled gtw hgtw (t₀ := t₀) (y := y) hX hh hc₀ hη0 hc'
  have hseamsum : (∑' n, seamCoeff (ellLin g) (fun _ => 1) t₀ n * (hatK X h n : ℂ))
      = ∑' N, (ellLin (restrictBelow y gtw) ⍟ ellLin (restrictAbove y gtw)) N
          * (hatK X h N : ℂ) := by
    have hrec := endpoint_reconciliation_full g t₀ y
    rw [← hgtwdef] at hrec
    rw [hrec]
  have hEta := norm_etaSum_le_msA gtw (X := X) hh hη
  rw [← hη] at hEta
  have hTwoEta := norm_twoEtaSum_le_msB gtw y (X := X) hh hη0
  have hexit := hCE (X + h) y (by linarith) hyXh
  rw [← hη] at hexit
  -- abbreviate the three residual sums
  set MainSum := ∑' N, (ellLin (restrictBelow y gtw) ⍟ ellLin (restrictAbove y gtw)) N
    * (hatK X h N : ℂ) with hMSdef
  set EtaSum := ∑' N, (ellLin (restrictBelow y gtw)
    ⍟ shiftCoeff (-(η : ℂ)) (ellLin (restrictAbove y gtw))) N * (hatK X h N : ℂ) with hESdef
  set TwoEtaSum := ∑' N, (∫ α in (0 : ℝ)..η,
      ((ellLin (restrictBelow y gtw) ⍟ shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y gtw)))
        ⍟ shiftCoeff (-(α : ℂ) - 2 * (η : ℂ)) (ellLin (restrictAbove y gtw))) N)
      * (hatK X h N : ℂ) with hTESdef
  rw [hseamsum, hcol,
    show MainSum - (MainSum - EtaSum - TwoEtaSum - rampTerm gtw X h y η)
      = EtaSum + TwoEtaSum + rampTerm gtw X h y η from by ring]
  calc ‖EtaSum + TwoEtaSum + rampTerm gtw X h y η‖
      ≤ ‖EtaSum + TwoEtaSum‖ + ‖rampTerm gtw X h y η‖ := norm_add_le _ _
    _ ≤ ‖EtaSum‖ + ‖TwoEtaSum‖ + ‖rampTerm gtw X h y η‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ _ := by
        refine le_trans (add_le_add (add_le_add hEta hTwoEta) hsliver) ?_
        have := add_le_add_right hexit E_ramp
        linarith

/-! ## THE STONE — the uniform-constant hoist -/

/-- **A-7 — `prop21_unconditional_uniform`: the S1′ representation with the E-constants
OUTSIDE the `X`-quantifier.**  The additive restatement of `prop21_unconditional_clean`
that the `hCenter` supply needs: ONE pair `(C_E, C_R)` (and one threshold `X₀`) valid at
every scale `X ≥ X₀` simultaneously, rather than a pair chosen after `X`.

  `∃ X₀ C_E C_R, 0 ≤ C_E ∧ 0 ≤ C_R ∧ ∀ {X h c₀ y η}, X₀ ≤ X → (the same gates) →`
  `  ‖(∑' n, seamCoeff (ellLin g) 1 t₀ n · hatK X h n) − prop21RHS …‖`
  `    ≤ C_E·((X+h)/log(X+h))·log y + C_R·(X/log X)·log y`.

Gates, hypotheses and conclusion are byte-identical to `prop21_unconditional_clean`'s;
only the binder order changes.  Provenance of the two constants (both `X`-free):
`C_E = max C_E' 0` with `C_E'` from `mult_shiu_MS_EXIT` (uniform in `x, y` already;
depends on `g, t₀` only, which are fixed before `X`), and `C_R = 32·C_cheb` with
`C_cheb` the short-interval Chebyshev constant of `shortInterval_vonMangoldt_le`
(a numeral: `250`, so `C_R = 8000` — `g`-free and `X`-free). -/
theorem prop21_unconditional_uniform (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ X₀ C_E C_R : ℝ, 0 ≤ C_E ∧ 0 ≤ C_R ∧
      ∀ {X h c₀ y η : ℝ}, X₀ ≤ X →
        h = X / Real.sqrt (Real.log X) → 1 < c₀ → η = 1 / Real.log y →
        0 < c₀ - 2 * η → 10 ≤ y → y ≤ Real.sqrt X → Real.sqrt (Real.log X) ≤ y →
      ‖(∑' n, seamCoeff (ellLin g) (fun _ => 1) t₀ n * (hatK X h n : ℂ))
          - prop21RHS (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) t₀ X h c₀ y η‖
        ≤ C_E * ((X + h) / Real.log (X + h)) * Real.log y
          + C_R * (X / Real.log X) * Real.log y := by
  -- BOTH constants are obtained BEFORE any scale is named
  obtain ⟨Cc, hCc0, hCbound⟩ := shortInterval_vonMangoldt_le
  obtain ⟨X₁, hX₁⟩ := logpow4_le_sqrt_ev
  have hgtw : ∀ p, p.Prime → ‖(fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀ hp.one_lt.le, mul_one]
    exact hg p hp
  obtain ⟨C_E, hCE⟩ := mult_shiu_MS_EXIT (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) hgtw
  refine ⟨max X₁ 17179869184, max C_E 0, 32 * Cc, le_max_right _ _, by linarith, ?_⟩
  intro X h c₀ y η hXlb hh hc₀ hη hc' hy10 hyX hygate
  -- outer-regime facts
  have hXbig : (17179869184 : ℝ) ≤ X := le_trans (le_max_right _ _) hXlb
  have hXX₁ : X₁ ≤ X := le_trans (le_max_left _ _) hXlb
  have hX : Real.exp 1 ≤ X :=
    (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 17179869184)).trans hXbig
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hsqlogX : (0 : ℝ) < Real.sqrt (Real.log X) := Real.sqrt_pos.mpr (by linarith)
  have hsqge1 : (1 : ℝ) ≤ Real.sqrt (Real.log X) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlogX1
  have hh0 : (0 : ℝ) < h := by rw [hh]; exact div_pos hXpos hsqlogX
  have hhX : h ≤ X := by rw [hh, div_le_iff₀ hsqlogX]; nlinarith [hsqge1, hXpos]
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hexp10 : Real.exp 1 ≤ 10 := by linarith [Real.exp_one_lt_three]
  have hylog1 : (1 : ℝ) ≤ Real.log y := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (le_trans hexp10 hy10)
  have hη0 : (0 : ℝ) ≤ η := by rw [hη]; exact le_of_lt (div_pos one_pos hlogy)
  have hη1 : η ≤ 1 := by rw [hη, div_le_one hlogy]; exact hylog1
  -- the per-window regime, then THE GRAIN at the uniform Chebyshev constant
  have hreg := window_regime_of_large hXbig (hX₁ X hXX₁) hh hy10 hyX
  have hgrain : ∀ l ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊,
      (∑ k ∈ Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊, vonMangoldt k)
        ≤ Cc * (h / (l : ℝ)) := by
    intro l hl
    obtain ⟨h1, h2, h3⟩ := hreg l hl
    have hkey := hCbound (X / (l : ℝ)) (h / (l : ℝ)) h1 h2 h3
    rwa [show (X + h) / (l : ℝ) = X / (l : ℝ) + h / (l : ℝ) from add_div X h (l : ℝ)]
  -- the ramp leg at the explicit constant, then the norm bridge
  have hmass := ramp_sliver_bound_const (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) hgtw
    hX hh hy10 hygate hCc0 hgrain
  have hsliver : ‖rampTerm (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) X h y η‖
      ≤ 8 * (4 * Cc * (X / Real.log X) * Real.log y) :=
    le_trans (ramp_norm_le_sliverMass y (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I))
      hy0 hXpos hh0 hhX hη0 hη1) (mul_le_mul_of_nonneg_left hmass (by norm_num))
  -- the S1′ representation at the hoisted E-constant
  have hmain := prop21_unconditional_ofC g hg t₀
    (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) rfl hX1 hh0 hc₀ hη hc' hy10 hyX hCE hsliver
  refine le_trans hmain ?_
  -- bump `C_E` to `max C_E 0` (the head factor is nonnegative) and reassociate `C_R`
  have hXh1 : (1 : ℝ) < X + h := by linarith
  have hlogXh : (0 : ℝ) < Real.log (X + h) := Real.log_pos hXh1
  have hA : (0 : ℝ) ≤ (X + h) / Real.log (X + h) * Real.log y :=
    mul_nonneg (div_nonneg (by linarith) hlogXh.le) hlogy.le
  have hbump : C_E * ((X + h) / Real.log (X + h)) * Real.log y
      ≤ max C_E 0 * ((X + h) / Real.log (X + h)) * Real.log y := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left C_E 0) hA
  linarith [hbump]

/-! ## The at-scale corollary (the recommended pin) -/

/-- **A-7 at the recommended pin — `prop21_uniform_at_scale`.**  The uniform hoist with
every free parameter instantiated at the freeze's recommended values

  `h = X/√(log X)`,  `c₀ = 1 + 1/log X`,  `y = (log X)^4`,  `η = 1/log y`,

and EVERY gate discharged from the single threshold `X₀` (so the consumer supplies only
`X₀ ≤ X`).  The gate page: `10 ≤ y` and `c₀ − 2η > 0` come from `log X ≥ 2` (hence
`log log X ≥ log 2 > 1/2`, the α-box corner `4·loglog ≥ 1`); `y ≤ √X` is the
`log⁴ = o(√X)` threshold; `√(log X) ≤ y` is `√L ≤ L⁴` at `L ≥ 1`.  This is the shape
the A-9 `center_halasz_supply` assembly consumes: one `(C_E, C_R)` for the whole range
`k ∈ [⌊X⌋₊, N]` (instantiate at `X := (k : ℝ)`). -/
theorem prop21_uniform_at_scale (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ X₀ C_E C_R : ℝ, 0 ≤ C_E ∧ 0 ≤ C_R ∧ ∀ X : ℝ, X₀ ≤ X →
      ‖(∑' n, seamCoeff (ellLin g) (fun _ => 1) t₀ n
            * (hatK X (X / Real.sqrt (Real.log X)) n : ℂ))
          - prop21RHS (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) t₀ X
              (X / Real.sqrt (Real.log X)) (1 + 1 / Real.log X) (Real.log X ^ 4)
              (1 / Real.log (Real.log X ^ 4))‖
        ≤ C_E * ((X + X / Real.sqrt (Real.log X))
              / Real.log (X + X / Real.sqrt (Real.log X))) * Real.log (Real.log X ^ 4)
          + C_R * (X / Real.log X) * Real.log (Real.log X ^ 4) := by
  obtain ⟨X₀, C_E, C_R, hCE0, hCR0, hbound⟩ := prop21_unconditional_uniform g hg t₀
  obtain ⟨X₁, hX₁⟩ := logpow4_le_sqrt_ev
  refine ⟨max (max X₀ X₁) (Real.exp 2), C_E, C_R, hCE0, hCR0, ?_⟩
  intro X hXlb
  have hX₀ : X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXlb
  have hXX₁ : X₁ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXlb
  have hXe2 : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hXlb
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 2) hXe2
  -- `log X ≥ 2`, hence `log log X ≥ log 2 > 1/2`
  have hL2 : (2 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) hXe2
  have hLpos : (0 : ℝ) < Real.log X := by linarith
  have hLL : Real.log (Real.log X ^ 4) = 4 * Real.log (Real.log X) := by
    rw [Real.log_pow]; norm_num
  have hlogL : Real.log 2 ≤ Real.log (Real.log X) := Real.log_le_log (by norm_num) hL2
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hLLpos : (0 : ℝ) < Real.log (Real.log X) := by linarith
  -- the gates
  have hc₀ : (1 : ℝ) < 1 + 1 / Real.log X := by
    have hpos : (0 : ℝ) < 1 / Real.log X := by positivity
    linarith
  have hy10 : (10 : ℝ) ≤ Real.log X ^ 4 := by
    have h2 : (4 : ℝ) ≤ Real.log X * Real.log X := by nlinarith
    nlinarith [h2, sq_nonneg (Real.log X * Real.log X - 4)]
  have hyX : Real.log X ^ 4 ≤ Real.sqrt X := by
    have hkey := hX₁ X hXX₁
    have h0 : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg X
    linarith
  have hygate : Real.sqrt (Real.log X) ≤ Real.log X ^ 4 := by
    have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
    have h8 : Real.log X ≤ (Real.log X ^ 4) ^ 2 := by
      rw [show (Real.log X ^ 4) ^ 2 = Real.log X ^ 8 by ring]
      exact le_self_pow₀ hL1 (by norm_num)
    calc Real.sqrt (Real.log X) ≤ Real.sqrt ((Real.log X ^ 4) ^ 2) := Real.sqrt_le_sqrt h8
      _ = Real.log X ^ 4 := Real.sqrt_sq (by positivity)
  have hc' : (0 : ℝ) < 1 + 1 / Real.log X - 2 * (1 / Real.log (Real.log X ^ 4)) := by
    rw [hLL]
    have h1 : 2 * (1 / (4 * Real.log (Real.log X))) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    have h2 : (0 : ℝ) < 1 / Real.log X := by positivity
    linarith
  exact hbound (X := X) (h := X / Real.sqrt (Real.log X)) (c₀ := 1 + 1 / Real.log X)
    (y := Real.log X ^ 4) (η := 1 / Real.log (Real.log X ^ 4))
    hX₀ rfl hc₀ rfl hc' hy10 hyX hygate

end Salt.MR
