/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PinFamily
import Salt.MR.SupClose

/-!
# THE PIN-2 RESIDUAL WAVE (`PinFamily2`)

`⟦V7⟧` of `docs/exploration/hsup-design.md` closes the second wall at the R2 pin
`y₂ = exp(L^{2/5})` (`PinFamily`, §5's `farErr34_local_closes`) and enumerates the residual
list this file works: the width-gate twin, the seam gate at `T*₂`, and the `SupClose` pin
layer at `y₂`.  Iron rule 1 is respected literally: **no landed statement is touched, no
existing file is edited**; every stone below is a NEW twin.

## §1 — THE WIDTH-GATE TWIN (⟦V7⟧'s BANDWIDTH RULING)

`PinFamily.width_pin_gate_bandwidth_fails_pin2` is the one genuine hit of ⟦V6b⟧ freeze risk
(ii): `GradeConst.pin_width_gates`'s fourth conjunct `y ≤ 2·T₀⁸ ≈ 512·L⁴` is FALSE at
`y = y₂`.  ⟦V7⟧'s RULING is that the width `A` was always FREE (it is a parameter of
`GradeConst.crossKer_width_sigma_bound_param`, pinned to `(y/2)^{1/8}` only by the CHOICE
made in `WidthGrade.width_pin_gates`): **`A` stays at the old scale**

  `A := (L⁴/2)^{1/8} ≈ 0.92·√L`,

and only the `y`-gate discharge changes.  `WidthGrade.width_pin_gates` reads its window gate
`2A⁸ ≤ n` off the IDENTITY `2A⁸ = y`; at the decoupled width it becomes the TWO-STAGE step

  `2A⁸ = L⁴ ≤ y₂ < n`   (`pow_four_le_ypin2`, then the window floor),

which is where `PinFamily.two_mul_pow_four_le_ypin2` is spent.  The other three conjuncts
(`A⁸ = L⁴/2`, `4 ≤ A`, `A ≤ T₀`) are the OLD ones verbatim — they never saw `y₂`.  So the
width layer DOES re-instantiate at `y₂`, with `h` still pinned at `k/√L` and with the same
absolute bracket `175616(1+Cb)` (`GradeConst.width_pin_bracket_le` at `y = L⁴`, untouched).
No statement changes anywhere; this is a `[B]`-tier twin, not a design block.

## §2 — THE SEAM GATE AT `T*₂`

`SeamGate`'s route (b) is height-agnostic (the geometry bounds `|t₁| ≤ T_ann + seamRad X`
with no reference to the truncation height), so raising the height to `T*₂` changes exactly
ONE step: the monotonicity `Tstar2_mono`.  At the R2 pin that step is CHEAPER than
`FarStar.Tstar_mono`'s `x/log x` argument, because

  `log T*₂(k) = (log k)^{2/5} + (log k)^{3/5}`   (`PinFamily.log_Tstar2_self`)

is MANIFESTLY increasing — two `rpow` monotonicities and `exp`.  The gate radius, the
per-`k` gate and the package mirror `FarStar`'s FS-4 triple.

## §3 — THE `SupClose` PIN LAYER AT `y₂`

`SupClose`'s S-C/S-D/S-E at `y₂`:

* `joint_supF_pin_trunc2` — `PinFamily.joint_supF_pin_at2` under
  `SupClose.center_dist_floor_recentred` (the recentring gate is pin-free);
* `joint_cs_trunc_pin2` — `TruncFactor.joint_cs_factoring_trunc` at `y₂`; the byte-exactness
  certificate for the twin above.  The far arm is threaded verbatim and NOT discharged;
* `crossKer_width_pin_const2` / `beta_integral_pin_const2` / `rhs_grade_at_scale_trunc2` —
  the width face at the DECOUPLED width of §1: the `crossKer` runs at `y₂` while the
  amplitude `widthKamp Cb k h (L⁴) c₀` — and therefore the exit constant
  `gradeAbsConst Cb` — is the corpus one, BYTE-IDENTICAL.  `GradeConst.rhsAgradeConst_le` is
  applied unchanged at `y = L⁴`; that is the whole content of the ruling.

**THE MIXED-PIN CONVENTION.**  From §3c on, two pins appear in one statement: the SPLIT
point is `y₂` (it is what `crossKer`, `smoothSeries`, `largeSeries` and `prop21RHS` read) and
the WIDTH is `L⁴` (it is what `widthKamp`/`widthKampBr` read, through `A = (y/2)^{1/8}`).
Consumers must keep them apart; the statements below always write the width argument as the
literal `L ^ 4`.

The `c` stays at the corpus `1/(2e)` throughout (matching `SupClose` exactly).

## §4 — `FarStar`'s FS-5 at `y₂`

`rhs_grade_at_scale_closed_star2` (all three arithmetic sockets discharged at the new pin,
exit constant `gradeAbsConst Cb + farCStar2`) and its per-scale form `hRHS_socket_star2`.
**`ball_sup_closed_star2` is NOT claimed**: `CenterSupply.ball_sup_supplied` has the corpus
pin written into its `hRHS` hypothesis, so no `y₂`-shaped socket can feed it (see the note on
`hRHS_socket_star2`).

## §5 — the CASE-A exit constant at `y₂`

`caseAS2` (= `CofactorGrade.caseAS` with `farCStar2`), its nonnegativity, and the `E`-slot
compose `caseAS2_absorbs_E_slot(_closes)` — ⟦V6b⟧ freeze risk (iii) cashed at the consumer.

## RESIDUALS (exact, for the next wave)

1. **`ball_sup_closed_star2`** — blocked by `CenterSupply.ball_sup_supplied`'s corpus-pinned
   `hRHS` binder (`CenterSupply` :477–482).  Needs a pin-generic twin of
   `ball_sup_supplied` → `center_halasz_supply` → `ball_sup_of_center`, or a statement
   change (Fable/JYH tier).  `hRHS_socket_star2` is the ready `y₂` object.
2. **The free-`c` width layer at `y₂`** — `RHSGradeC.beta_integral_pin_constC` and
   `GradeWindowC.rhs_grade_at_scale_windowC` re-run at `y₂` with the decoupled width, i.e.
   §3c/§3d with the exponent `c` freed.  That is what `CofactorGrade.caseA_rhs_socket`'s twin
   needs; §5 gives the constant and the `E`-slot, not the socket.
3. **The window-floor form** — `caseA_rhs_socket2` (the `hMwin` shape at `T*₂`) rides (2).
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## §1 — the width-gate twin: `A` at the OLD scale, the `y`-gate in two stages -/

/-- **The two-stage step (`pow_four_le_ypin2`).**  `L⁴ ≤ y₂` at the pin-2 gate.  This is the
inequality the decoupled width gate needs: the old width satisfies `2A⁸ = L⁴`, and the `y₂`
window's floor is `y₂`, so the gate `2A⁸ ≤ n` follows from `L⁴ ≤ y₂ < n`.  Half of
`PinFamily.two_mul_pow_four_le_ypin2`, kept as a named step because it is what every
consumer of §1 cites. -/
theorem pow_four_le_ypin2 {L : ℝ} (hL : 32768 ≤ L) : L ^ 4 ≤ ypin2 L := by
  have h := two_mul_pow_four_le_ypin2 hL
  have h0 : (0 : ℝ) ≤ L ^ 4 := by positivity
  linarith

/-- **⟦V7⟧'s WIDTH-GATE TWIN (`width_pin_gates_pin2_old_A`).**  `WidthGrade.width_pin_gates`
at the `y₂` window with the width `A` held at the OLD scale `A = (L⁴/2)^{1/8}`:

  `A⁸ = L⁴/2`,  `4 ≤ A`,  `A ≤ T₀`,  and  `2A⁸ ≤ n` on `Ioo ⌊y₂⌋₊ ⌈k/y₂⌉₊`.

The first three conjuncts are the landed ones verbatim (they read only `L⁴`, never the pin).
The fourth — the ONLY place the pin enters — is discharged in TWO stages instead of by the
identity `2A⁸ = y`: `2A⁸ = L⁴ ≤ y₂` (`pow_four_le_ypin2`) and `y₂ < n` (the window floor).

Compare `PinFamily.width_pin_gate_bandwidth_fails_pin2`: the gate that FAILS at `y₂` is
`y ≤ 2T₀⁸` with `y := y₂`, i.e. the choice `A = (y₂/2)^{1/8}`.  Here `A` is not that. -/
theorem width_pin_gates_pin2_old_A {k L T₀ A : ℝ} (hk : pin2Gate ≤ k) (hL : L = Real.log k)
    (hT₀ : 0 < T₀) (hyT : L ^ 4 ≤ 2 * T₀ ^ 8) (hA : A = (L ^ 4 / 2) ^ (1 / 8 : ℝ)) :
    A ^ 8 = L ^ 4 / 2 ∧ 4 ≤ A ∧ A ≤ T₀ ∧
      ∀ n ∈ Finset.Ioo ⌊ypin2 L⌋₊ ⌈k / ypin2 L⌉₊, 2 * A ^ 8 ≤ (n : ℝ) := by
  obtain ⟨-, hL32, -, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hy4 : (131072 : ℝ) ≤ L ^ 4 := by
    have h4 : (32768 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL32 4
    norm_num at h4
    linarith
  have hy2 : (0 : ℝ) < L ^ 4 / 2 := by linarith
  have hA0 : (0 : ℝ) ≤ A := by rw [hA]; exact Real.rpow_nonneg hy2.le _
  have hA8 : A ^ 8 = L ^ 4 / 2 := by
    rw [hA, ← Real.rpow_natCast ((L ^ 4 / 2) ^ (1 / 8 : ℝ)) 8, ← Real.rpow_mul hy2.le]
    norm_num
  have h48 : ((4 : ℝ)) ^ 8 = 65536 := by norm_num
  refine ⟨hA8, ?_, ?_, ?_⟩
  · refine le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) hA0 ?_
    rw [hA8, h48]; linarith
  · refine le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) hT₀.le ?_
    rw [hA8]; linarith
  · intro n hn
    rw [Finset.mem_Ioo] at hn
    have hyn : ypin2 L < (n : ℝ) := (Nat.floor_lt (ypin2_pos L).le).mp hn.1
    have hstage : L ^ 4 ≤ ypin2 L := pow_four_le_ypin2 hL32
    rw [hA8]; linarith

/-- **The width-gate twin AT THE PIN (`width_pin_gates_pin2_at_pin`).**
`GradeConst.pin_width_gates`'s conjunct list at `h = k/√L`, with the third/fourth
(`131072 ≤ y`, `y ≤ 2T₀⁸`) replaced by the DECOUPLED width's own three facts of
`width_pin_gates_pin2_old_A`.  This is the bundle `§3`'s width face consumes:

`0 < h`, `T₀ = 2(√L+1)`, `A⁸ = L⁴/2`, `4 ≤ A`, `A ≤ T₀`, and the `y₂`-window gate.

The bandwidth conjunct is now a statement about `L⁴` (TRUE, with a factor 512 to spare — the
landed `pin_width_gates` proves exactly it), not about `y₂` (FALSE). -/
theorem width_pin_gates_pin2_at_pin {k L h A : ℝ} (hk : pin2Gate ≤ k) (hL : L = Real.log k)
    (hh : h = k / Real.sqrt L) (hA : A = (L ^ 4 / 2) ^ (1 / 8 : ℝ)) :
    0 < h ∧ 2 * (k + h) / h = 2 * (Real.sqrt L + 1) ∧ A ^ 8 = L ^ 4 / 2 ∧ 4 ≤ A
      ∧ A ≤ 2 * (k + h) / h
      ∧ ∀ n ∈ Finset.Ioo ⌊ypin2 L⌋₊ ⌈k / ypin2 L⌉₊, 2 * A ^ 8 ≤ (n : ℝ) := by
  obtain ⟨hk0, hL32, -, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hk hL
  have hL64 : (64 : ℝ) ≤ L := by linarith
  obtain ⟨hh0, hT, -, hyT⟩ := pin_width_gates hL64 hk0 hh rfl
  have hT₀0 : (0 : ℝ) < 2 * (k + h) / h := by rw [hT]; positivity
  obtain ⟨hA8, hA4, hAT, hgate⟩ := width_pin_gates_pin2_old_A hk hL hT₀0 hyT hA
  exact ⟨hh0, hT, hA8, hA4, hAT, hgate⟩

/-! ## §2 — the seam gate at `T*₂` (`FarStar`'s FS-4 triple, re-pinned) -/

/-- `0 < T*₂` at every positive scale — no gate at all (`ypin2` is an `exp`, `k^{η₂}` an
`rpow` of a positive base). -/
lemma Tstar2_pos {k L : ℝ} (hk : 0 < k) : 0 < Tstar2 k L :=
  mul_pos (ypin2_pos L) (Real.rpow_pos_of_pos hk _)

/-- **FS-1m at the R2 pin (`Tstar2_mono`).**  `k ↦ T*₂(k, log k)` is monotone on
`k ≥ exp 32768`.  Where `FarStar.Tstar_mono` needs the derivative-free `x/log x`
monotonicity (`log T* = 4 loglog k + log k/(4 loglog k)`, a genuine two-term competition),
here `PinFamily.log_Tstar2_self` makes the log MANIFESTLY increasing:

  `log T*₂(k) = (log k)^{2/5} + (log k)^{3/5}`,

a sum of two increasing `rpow`s of `log k`.  The gate is the family's own `pin2Gate`. -/
theorem Tstar2_mono {k K : ℝ} (hk : pin2Gate ≤ k) (hkK : k ≤ K) :
    Tstar2 k (Real.log k) ≤ Tstar2 K (Real.log K) := by
  have hK : pin2Gate ≤ K := le_trans hk hkK
  obtain ⟨hk0, hLk32, -, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hk rfl
  obtain ⟨hK0, hLK32, -, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hK rfl
  have hLk0 : (0 : ℝ) < Real.log k := by linarith
  have hlog : Real.log k ≤ Real.log K := Real.log_le_log hk0 hkK
  have h25 : (Real.log k) ^ ((2 : ℝ) / 5) ≤ (Real.log K) ^ ((2 : ℝ) / 5) :=
    Real.rpow_le_rpow hLk0.le hlog (by norm_num)
  have h35 : (Real.log k) ^ ((3 : ℝ) / 5) ≤ (Real.log K) ^ ((3 : ℝ) / 5) :=
    Real.rpow_le_rpow hLk0.le hlog (by norm_num)
  have hTk0 : (0 : ℝ) < Tstar2 k (Real.log k) := Tstar2_pos hk0
  have hTK0 : (0 : ℝ) < Tstar2 K (Real.log K) := Tstar2_pos hK0
  have hlogT : Real.log (Tstar2 k (Real.log k)) ≤ Real.log (Tstar2 K (Real.log K)) := by
    rw [log_Tstar2_self hk, log_Tstar2_self hK]; linarith
  calc Tstar2 k (Real.log k) = Real.exp (Real.log (Tstar2 k (Real.log k))) :=
        (Real.exp_log hTk0).symm
    _ ≤ Real.exp (Real.log (Tstar2 K (Real.log K))) := Real.exp_le_exp.mpr hlogT
    _ = Tstar2 K (Real.log K) := Real.exp_log hTK0

/-- **FS-4 at the R2 pin — the gate radius (`seamGateRstar2`).**
`R := T_ann + seamRad X + T*₂(2X, log 2X) + 1` — `SeamGate.seamGateR` with the row's largest
presentable truncation height raised from `(log 2X)⁴` to `T*₂(2X)`.  `T*₂(2X)` is
`exp((log 2X)^{2/5} + (log 2X)^{3/5})` — SUB-polynomial in `X` (the exponent is `o(log X)`),
so in the `polyT` regime the radius still satisfies `R ≪ X`. -/
def seamGateRstar2 (X T : ℝ) : ℝ := T + seamRad X + Tstar2 (2 * X) (Real.log (2 * X)) + 1

lemma seamGateRstar2_nonneg {X T : ℝ} (hT : 0 ≤ T) (hX : 1 ≤ X) : 0 ≤ seamGateRstar2 X T := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hLX : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX
  have hr : (0 : ℝ) ≤ seamRad X := seamRad_nonneg hLX
  have hTs : (0 : ℝ) < Tstar2 (2 * X) (Real.log (2 * X)) := Tstar2_pos (by linarith)
  unfold seamGateRstar2
  linarith

/-- **FS-4 at the R2 pin — THE GATE (`seam_gate_star2_of_nonempty`).**  `SeamGate`'s
`seam_gate_of_nonempty` with `Tstar2_mono` in place of `log_pow_four_le_of_le_two_mul`: on
the ball leg's own domain, at the minimality radius `seamGateRstar2 X T_ann`,

  `|t₁| + T*₂(k, log k) ≤ seamGateRstar2 X T_ann`  for every `exp 32768 ≤ k ≤ 2X`.

Still no `hgap`, no localization, no numeral shift, and no reference to `X` as a bound on
`|t₁|`.  The gate on `k` is the pin-2 family's own (`pin2Gate ≤ k`), which every consumer of
`PinFamily` already carries. -/
theorem seam_gate_star2_of_nonempty {X T t₁ k : ℝ} (hk : pin2Gate ≤ k) (hkX : k ≤ 2 * X)
    (hne : (seamAnn X T ∩ seamBall X t₁).Nonempty) :
    |t₁| + Tstar2 k (Real.log k) ≤ seamGateRstar2 X T := by
  have h1 := seamAnn_inter_seamBall_center_le hne
  have h2 := Tstar2_mono hk hkX
  unfold seamGateRstar2
  linarith

/-- **FS-4 at the R2 pin — the minimizer (`exists_min_gate_star2`).**
`CompactMin.exists_min_dist_abs` at `R := seamGateRstar2 X T_ann`. -/
theorem exists_min_gate_star2 (f : ℕ → ℂ) {X T : ℝ} (hT : 0 ≤ T) (hX : 1 ≤ X) :
    ∃ t₁ : ℝ, |t₁| ≤ seamGateRstar2 X T ∧ ∀ v : ℝ, |v| ≤ seamGateRstar2 X T →
      pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist v) X :=
  exists_min_dist_abs f X (seamGateRstar2_nonneg hT hX)

/-- **FS-4 at the R2 pin — the bundle (`seam_gate_star2_package`).**
`SeamGate.seam_gate_package` / `FarStar.seam_gate_star_package` at the R2 height: ONE centre
carrying the compact minimality at radius `seamGateRstar2 X T_ann` and, on the ball leg's own
domain, the recentring gate at every `T*₂(k, log k)`, `exp 32768 ≤ k ≤ 2X`. -/
theorem seam_gate_star2_package (f : ℕ → ℂ) {X T : ℝ} (hT : 0 ≤ T) (hX : 1 ≤ X) :
    ∃ t₁ : ℝ,
      (∀ v : ℝ, |v| ≤ seamGateRstar2 X T →
        pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist v) X)
      ∧ ∀ k : ℝ, pin2Gate ≤ k → k ≤ 2 * X →
          (seamAnn X T ∩ seamBall X t₁).Nonempty →
          |t₁| + Tstar2 k (Real.log k) ≤ seamGateRstar2 X T := by
  obtain ⟨t₁, -, hmin⟩ := exists_min_gate_star2 f hT hX
  exact ⟨t₁, hmin, fun k hk hkX hne => seam_gate_star2_of_nonempty hk hkX hne⟩

/-! ## §3 — the `SupClose` pin layer at `y₂`

### §3a — the privates, re-derived

`GradeConst`'s `rhs_sigma_div_integrableC`, `rhs_shift_integrableC`, `continuous_rpow_negC`,
`widthKamp_nonneg` and `pin_regroup` are `private`; re-derived below verbatim (same
statements, same proofs), exactly as `SupClose` re-derives `GradeConst`'s pin privates. -/

/-- Interval-integrability of the σ-integrand `Fbound σ/σ`.  Re-derivation of `GradeConst`'s
private `rhs_sigma_div_integrableC`. -/
private lemma rhs_sigma_div_integrable2 {M L b : ℝ} (hL0 : 0 < L) (hb : 1 / L ≤ b) :
    IntervalIntegrable (fun σ : ℝ => rhsFbound M L σ / σ) volume (1 / L) b := by
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hpos : ∀ σ ∈ Set.uIcc (1 / L) b, (0 : ℝ) < σ := by
    intro σ hσ
    rw [Set.uIcc_of_le hb, Set.mem_Icc] at hσ
    exact lt_of_lt_of_le hLinv0 hσ.1
  apply ContinuousOn.intervalIntegrable
  simp only [rhsFbound]
  refine ContinuousOn.div (ContinuousOn.mul ?_ ?_) continuousOn_id
    (fun σ hσ => (hpos σ hσ).ne')
  · exact continuousOn_const.mul
      (continuousOn_const.div continuousOn_id (fun σ hσ => (hpos σ hσ).ne'))
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul (ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_)
      continuousOn_const)
    exact continuousOn_const.mul (ContinuousOn.log
      ((continuous_id.mul continuous_const).continuousOn)
      (fun σ hσ => (mul_pos (hpos σ hσ) hL0).ne'))

/-- Interval-integrability of `bridge_adapter`'s translated integrand.  Re-derivation of
`GradeConst`'s private `rhs_shift_integrableC`. -/
private lemma rhs_shift_integrable2 {M L η Kα : ℝ} (hL0 : 0 < L) (hη0 : 0 ≤ η) :
    IntervalIntegrable
      (fun β : ℝ => Kα * (rhsFbound M L (β + 1 / L) / (β + 1 / L))) volume 0 η := by
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hpos : ∀ β ∈ Set.uIcc (0 : ℝ) η, (0 : ℝ) < β + 1 / L := by
    intro β hβ
    rw [Set.uIcc_of_le hη0, Set.mem_Icc] at hβ
    linarith [hβ.1]
  apply ContinuousOn.intervalIntegrable
  simp only [rhsFbound]
  refine continuousOn_const.mul (ContinuousOn.div (ContinuousOn.mul ?_ ?_) ?_
    (fun β hβ => (hpos β hβ).ne'))
  · exact continuousOn_const.mul
      (continuousOn_const.div (by fun_prop) (fun β hβ => (hpos β hβ).ne'))
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul (ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_)
      continuousOn_const)
    exact continuousOn_const.mul (ContinuousOn.log (by fun_prop)
      (fun β hβ => (mul_pos (hpos β hβ) hL0).ne'))
  · fun_prop

/-- Continuity of `α ↦ a^{−α}`.  Re-derivation of `GradeConst`'s private
`continuous_rpow_negC`. -/
private lemma continuous_rpow_neg2 {a : ℝ} (ha : 0 < a) :
    Continuous (fun α : ℝ => a ^ (-α)) := by
  have hrw : (fun α : ℝ => a ^ (-α)) = fun α : ℝ => Real.exp (Real.log a * (-α)) := by
    funext α; rw [Real.rpow_def_of_pos ha]
  rw [hrw]
  exact Real.continuous_exp.comp (by fun_prop)

/-- The width amplitude is nonnegative.  Re-derivation of `GradeConst`'s private
`widthKamp_nonneg`. -/
private lemma widthKamp_nonneg2 {Cb X h y c₀ : ℝ} (hCb0 : 0 ≤ Cb) (hX0 : 0 < X) (hh : 0 < h)
    (hy0 : 0 < y) : 0 ≤ widthKamp Cb X h y c₀ := by
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hy2 : (0 : ℝ) < y / 2 := by linarith
  have hA0 : (0 : ℝ) < (y / 2) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hy2 _
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold widthKamp widthKampBr
  have hrp : (0 : ℝ) ≤ (X + h) ^ c₀ := Real.rpow_nonneg hXh0.le _
  positivity

/-- Regrouping on OPAQUE reals.  Re-derivation of `GradeConst`'s private `pin_regroup`. -/
private lemma pin_regroup2 {a b Kf Lg P Q S : ℝ} (hab : a ≤ b) (hKf : 0 ≤ Kf) (hLg : 0 ≤ Lg)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hS : 0 ≤ S) :
    a * Kf * Lg * (P * Q) * S ≤ b * Kf * Lg * P * Q * S := by
  have hlhs : a * Kf * Lg * (P * Q) * S = a * (Kf * Lg * (P * Q) * S) := by ring
  have hrhs : b * Kf * Lg * P * Q * S = b * (Kf * Lg * (P * Q) * S) := by ring
  rw [hlhs, hrhs]
  exact mul_le_mul_of_nonneg_right hab (by positivity)

/-! ### §3b — S-C/S-D at `y₂` -/

/-- **S-C at `y₂` (`joint_supF_pin_trunc2`).**  `SupClose.joint_supF_pin_trunc` at the R2
pin: `TruncFactor.joint_cs_factoring_trunc`'s `hsupF` binder, discharged from the COMPACT
minimality alone (`|v| ≤ R`).

The recentring step (`SupClose.center_dist_floor_recentred`) is entirely pin-free — it moves
the contour centre, never the split point — so the ONLY change versus the landed stone is
that `PinFamily.joint_supF_pin_at2` replaces `SupClose.joint_supF_pin_at`, i.e. the gate
`Real.exp 3 ≤ k` becomes the family gate `pin2Gate ≤ k` and the pin equations become
`y = y₂`, `η = η₂`.  The conclusion `rhsFbound M L (β + 1/L)` is byte-identical (⟦V6b⟧
freeze risk (i): the `σ`-sup is attained at the left endpoint `1/L`, which does not move). -/
theorem joint_supF_pin_trunc2 {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t₁ X k L c₀ y η R T : ℝ}
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀eq : c₀ = 1 + 1 / L) (hXk : ⌊X⌋₊ ≤ ⌊k⌋₊) (hgate : |t₁| + T ≤ R)
    (hmin : ∀ v : ℝ, |v| ≤ R →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) :
    ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ, |t - (t₀ + t₁)| ≤ T →
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) + (β : ℂ))‖
        ≤ rhsFbound (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
            L (β + 1 / L) := by
  intro α hα β hβ t ht
  exact joint_supF_pin_at2 hg hk hL hy hη hc₀eq hα.1 hβ.1 hα.2 hβ.2 t
    (center_dist_floor_recentred hg hXk hmin hgate ht)

/-- **S-D at `y₂` (`joint_cs_trunc_pin2`).**  `SupClose.joint_cs_trunc_pin` at the R2 pin:
`TruncFactor.joint_cs_factoring_trunc` with `hsupF` discharged by S-C.  This compile is the
byte-exactness certificate for `joint_supF_pin_trunc2`.

The far arm (`Ffar`, `Kfar`, `hFar`, `hKfar`) is threaded VERBATIM and NOT discharged — at
`y₂` its numerals are `PinFamily`'s §4 (`far_supF_bound2`, `far_kernel_bound_star2` at
`T := T*₂`, `hfar_star2`).  The only pin-sensitive gate inside is `0 < c₀ − 2η₂`, which is
FREER here than at the corpus pin (`η₂ ≤ 1/64` versus `η ≤ 1/8`). -/
theorem joint_cs_trunc_pin2 {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t₁ X k L c₀ y η h R T Ffar Kfar : ℝ}
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀eq : c₀ = 1 + 1 / L) (hh0 : 0 < h) (hXk : ⌊X⌋₊ ≤ ⌊k⌋₊) (hgate : |t₁| + T ≤ R)
    (hmin : ∀ v : ℝ, |v| ≤ R →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hFfar0 : 0 ≤ Ffar)
    (hFar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Ffar)
    (hKfar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀ (t₀ + t₁)
        α β T ≤ Kfar)
    (hInt : JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
      (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) k L c₀ y η h) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁) k h c₀ y η‖
      ≤ (1 / Real.pi) * (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
            rhsFbound (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                L (β + 1 / L)
              * crossKer (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀
                  (t₀ + t₁) α β)
        + (1 / Real.pi) * (η ^ 2 * (Ffar * Kfar)) := by
  obtain ⟨hIβ, hIβ', hIα, hIα'⟩ := hInt
  obtain ⟨hk0, hL32, -, -, -, hη0, hη64, -, -, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hη0' : (0 : ℝ) < η := by rw [hη]; exact hη0
  have hη64' : η ≤ 1 / 64 := by rw [hη]; exact hη64
  have hkexp : Real.exp 32768 ≤ k := hk
  have hk1 : (1 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (32768 : ℝ)]
  refine joint_cs_factoring_trunc hk1 hh0 hη0'.le ?_ hFfar0 ?_
    (joint_supF_pin_trunc2 hg hk hL hy hη hc₀eq hXk hgate hmin) hFar hKfar hIβ hIβ' hIα hIα'
  · rw [hc₀eq]; linarith
  · exact fun _ _ β hβ => rhsFbound_nonneg _ _ (by linarith [hβ.1])

/-! ### §3c — the width face at the DECOUPLED width (⟦V7⟧'s ruling, in force) -/

/-- **R-2b at `y₂` (`crossKer_width_pin_const2`).**  `GradeConst.crossKer_width_pin_const`
with the split point at `y₂` and the width at the OLD scale:

  `crossKer g k h y₂ c₀ t₀ α β ≤ widthKamp Cb k h (L⁴) c₀ · (k+h)^{−α} · (1/σ)`.

`GradeConst.crossKer_width_sigma_bound_param` carries `A` as a FREE parameter under three
gates; §1's `width_pin_gates_pin2_at_pin` supplies all three at `A = (L⁴/2)^{1/8}`, and the
regrouping is the landed one.  **The amplitude is the corpus amplitude, byte-for-byte** —
which is why `GradeConst.width_pin_bracket_le`'s absolute numeral `175616(1+Cb)` and
`GradeConst.rhsAgradeConst_le`'s `gradeAbsConst Cb` survive the re-pin untouched.

The bandwidth constraint that ⟦V7⟧ found broken at `y₂` never appears: it is the gate
`y ≤ 2T₀⁸` of the CHOICE `A = (y/2)^{1/8}`, and that choice is not made here. -/
theorem crossKer_width_pin_const2 (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {k h L c₀ t₀' α β σ Cb : ℝ} (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hc₀ : c₀ = 1 + 1 / L)
    (hh : h = k / Real.sqrt L) (hσ : σ = β + 1 / L)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαβ : α + β ≤ 1 / 4) :
    crossKer g k h (ypin2 L) c₀ t₀' α β
      ≤ widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α) * (1 / σ) := by
  obtain ⟨hk0, hL32, -, -, -, -, -, -, -, hy131072, -, -, hyk⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hL3 : (3 : ℝ) ≤ L := by linarith
  obtain ⟨hh0, hT, -, hA4, hAT, hygate⟩ := width_pin_gates_pin2_at_pin hk hL hh rfl
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hLinv : (0 : ℝ) < 1 / L := by positivity
  have hσ0 : (0 : ℝ) < σ := by rw [hσ]; linarith
  have hbd := crossKer_width_sigma_bound_param g hg (t₀ := t₀') hCb0 hCbound hL hL3
    (by linarith) hyk hc₀ hh0 hσ hα0 hβ0 hαβ hA4 hAT hygate
  refine hbd.trans ?_
  have hcw : (3 : ℝ) / 4 ≤ c₀ - α - β := by rw [hc₀]; linarith
  have hcw0 : (0 : ℝ) < c₀ - α - β := by linarith
  have hbr : 4 * (2 * (k + h) / h) ^ 2 / (c₀ - α - β) + 2 * (2 * (k + h) / h)
      ≤ 4 * (2 * (k + h) / h) ^ 2 / (3 / 4) + 2 * (2 * (k + h) / h) := by
    have hd : 4 * (2 * (k + h) / h) ^ 2 / (c₀ - α - β)
        ≤ 4 * (2 * (k + h) / h) ^ 2 / (3 / 4) := by
      rw [div_le_div_iff₀ hcw0 (by norm_num)]
      nlinarith [sq_nonneg (2 * (k + h) / h)]
    linarith
  have hA0 : (0 : ℝ) < (L ^ 4 / 2) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  exact pin_regroup2 (a := 4 * (2 * (k + h) / h) ^ 2 / (c₀ - α - β) + 2 * (2 * (k + h) / h))
    (b := 4 * (2 * (k + h) / h) ^ 2 / (3 / 4) + 2 * (2 * (k + h) / h))
    (Kf := Real.pi / (L ^ 4 / 2) ^ (1 / 8 : ℝ)
      * (2 / ((L ^ 4 / 2) ^ (1 / 8 : ℝ)) ^ 2 + 8 * Cb / (L ^ 4 / 2) ^ (1 / 8 : ℝ)))
    (Lg := 9 * (Real.log 4 + 4)) (P := (k + h) ^ c₀) (Q := (k + h) ^ (-α))
    (S := 1 / σ) hbr (by positivity) (by linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)])
    (Real.rpow_nonneg hkh0.le _) (Real.rpow_nonneg hkh0.le _) (by positivity)

/-- **A-6a at `y₂` (`beta_integral_pin_const2`).**  `GradeConst.beta_integral_pin_const` with
the `crossKer` at `y₂` and the amplitude at the decoupled width.  Everything between the
pointwise bound and the σ-integral (`BridgeAdapt.bridge_adapter`,
`PretSupply.joint_sigma_integral`) is pin-agnostic and is instantiated, not re-proved. -/
theorem beta_integral_pin_const2 (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Cb t₀' M k L c₀ y η h α : ℝ} (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L) (hM0 : 0 ≤ M)
    (hα0 : 0 ≤ α) (hαη : α ≤ η)
    (hIβ : IntervalIntegrable (fun β => rhsFbound M L (β + 1 / L)
        * crossKer g k h y c₀ t₀' α β) volume 0 η) :
    (∫ β in (0 : ℝ)..η, rhsFbound M L (β + 1 / L) * crossKer g k h y c₀ t₀' α β)
      ≤ (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α)) * rhsSigmaG M L := by
  obtain ⟨hk0, hL32, -, -, -, hη0, hη64, hηL, -, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hη0' : (0 : ℝ) < η := by rw [hη]; exact hη0
  have hη64' : η ≤ 1 / 64 := by rw [hη]; exact hη64
  have hLη : 1 / L ≤ η := by rw [hη]; linarith
  have hh0 : (0 : ℝ) < h := by rw [hh]; positivity
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hy40 : (0 : ℝ) < L ^ 4 := by positivity
  have hK0 : (0 : ℝ) ≤ widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α) :=
    mul_nonneg (widthKamp_nonneg2 hCb0 hk0 hh0 hy40) (Real.rpow_nonneg hkh0.le _)
  have hcross : ∀ β ∈ Icc (0 : ℝ) η,
      crossKer g k h y c₀ t₀' α β
        ≤ (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α)) * (1 / (β + 1 / L)) := by
    intro β hβ
    rw [hy]
    exact crossKer_width_pin_const2 g hg hCb0 hCbound hk hL hc₀ hh rfl hα0 hβ.1
      (by linarith [hβ.2])
  have hsup0 : ∀ β ∈ Icc (0 : ℝ) η, 0 ≤ rhsFbound M L (β + 1 / L) := by
    intro β hβ
    exact rhsFbound_nonneg M L (by linarith [hβ.1])
  have hFnn : ∀ σ ∈ Icc (1 / L) (2 * η), 0 ≤ rhsFbound M L σ := by
    intro σ hσ
    exact rhsFbound_nonneg M L (lt_of_lt_of_le hLinv0 hσ.1)
  have hIσ := rhs_sigma_div_integrable2 (M := M) (L := L) (b := 2 * η) hL0 (by linarith)
  have hBA := bridge_adapter (g := g) (X := k) (h := h) (y := y) (c₀ := c₀) (t₀ := t₀')
    (L := L) (η := η) (Kα := widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α)) (α := α)
    (supF := fun _ β => rhsFbound M L (β + 1 / L)) (Fbound := rhsFbound M L)
    hL0 hLη hK0 hsup0 hcross (fun β _ => le_rfl) hFnn hIβ
    (rhs_shift_integrable2 hL0 hη0'.le) hIσ
  refine le_trans hBA ?_
  refine mul_le_mul_of_nonneg_left ?_ hK0
  have hlogk3 : (3 : ℝ) ≤ Real.log k := by rw [← hL]; linarith
  rw [hL]
  exact joint_sigma_integral (Fbound := rhsFbound M (Real.log k))
    (c := 1 / (2 * Real.exp 1)) (X := k) (b := 2 * η) (M := M) (CSF := rhsCSF)
    (by positivity)
    (by
      rw [show 2 * (1 / (2 * Real.exp 1)) = 1 / Real.exp 1 from by ring,
        div_lt_one (Real.exp_pos 1)]
      linarith [Real.exp_one_gt_d9])
    hlogk3 hM0 rhsCSF_pos.le (by rw [← hL]; linarith) (by rw [← hL]; exact hIσ)
    (fun σ _ => le_rfl)

/-! ### §3d — S-E at `y₂`: the truncated grade at scale -/

set_option maxHeartbeats 800000 in
-- As at `SupClose.rhs_grade_at_scale_trunc`: the `M`-term is a large opaque `pretDistSq`
-- expression repeated across the α/β integrals, and the mixed-pin amplitude adds one more
-- expression to unify; elaboration exceeds the default budget.
/-- **S-E at `y₂` — THE TRUNCATED GRADE AT SCALE (`rhs_grade_at_scale_trunc2`).**
`SupClose.rhs_grade_at_scale_trunc` at the R2 pin:

  `‖prop21RHS … y₂ η₂‖ ≤ gradeAbsConst Cb · k · e^{−(1/(2e))·M} + (1/π)·η₂²·(Ffar·Kfar)`,
  `M = 𝔻²(seamCoeff (ellLin g) 1 t₀, costwist t₁; X)`.

**The main term is BYTE-IDENTICAL to the corpus one** — same `gradeAbsConst Cb`, same
`e^{−M/(2e)}`, no `y₂` anywhere in it.  That is ⟦V7⟧'s width ruling cashed: the width `A`
stayed at `(L⁴/2)^{1/8}`, so `GradeConst.rhsAgradeConst_le` applies UNCHANGED at `y = L⁴`
while the series split runs at `y₂`.

The far remainder is `SupClose`'s own, unabsorbed and now at the R2 pin, where `PinFamily`'s
§4 prices it: `Ffar := farFbound L` (`far_supF_bound2` — the F-page does not move) and
`Kfar := farKfarStar2 …` at `T := T*₂` (`far_kernel_bound_star2`), with `hfar_star2` the
arithmetic.  Absorbing it is §4's business (the `rhs_grade_at_scale_closed` twin), not
this stone's. -/
theorem rhs_grade_at_scale_trunc2 {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Cb t₀ t₁ X k L c₀ y η h R T Ffar Kfar : ℝ}
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L)
    (hXk : ⌊X⌋₊ ≤ ⌊k⌋₊) (hgate : |t₁| + T ≤ R)
    (hmin : ∀ v : ℝ, |v| ≤ R →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hFfar0 : 0 ≤ Ffar)
    (hFar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Ffar)
    (hKfar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀ (t₀ + t₁)
        α β T ≤ Kfar)
    (hInt : JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
      (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) k L c₀ y η h) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁) k h c₀ y η‖
      ≤ gradeAbsConst Cb * k
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
        + (1 / Real.pi) * (η ^ 2 * (Ffar * Kfar)) := by
  obtain ⟨hIβ, hIβ', hIα, hIα'⟩ := hInt
  obtain ⟨hk0, hL32, -, -, -, hη0, -, -, -, -, -, -, hyk⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hη0' : (0 : ℝ) < η := by rw [hη]; exact hη0
  have hh0 : (0 : ℝ) < h := by rw [hh]; positivity
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hkexp : Real.exp 32768 ≤ k := hk
  have hk64 : Real.exp 64 ≤ k :=
    le_trans (Real.exp_le_exp.mpr (by norm_num : (64 : ℝ) ≤ 32768)) hkexp
  have hy0 : (0 : ℝ) < y := by rw [hy]; exact ypin2_pos L
  have hy40 : (0 : ℝ) < L ^ 4 := by positivity
  have hM0 : (0 : ℝ) ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X :=
    pretDistSq_nonneg _ _ _
      (fun n => norm_seamCoeff_le (fun m => ellLin_norm_le_one g hg m) (fun _ => by simp) t₀ n)
      (fun n => le_of_eq (costwist_norm t₁ n))
  have hgtw : ∀ p, p.Prime →
      ‖(fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist (t₀ + t₁) hp.one_lt.le, mul_one]
    exact hg p hp
  have hKamp0 : (0 : ℝ) ≤ widthKamp Cb k h (L ^ 4) c₀ := widthKamp_nonneg2 hCb0 hk0 hh0 hy40
  have hG0 : (0 : ℝ) ≤ rhsSigmaG
      (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L := by
    unfold rhsSigmaG
    have hE : (0 : ℝ) ≤ Real.exp (1 / (2 * Real.exp 1) * 48)
        / (1 - 2 * (1 / (2 * Real.exp 1))) := by
      have hd : (0 : ℝ) < 1 - 2 * (1 / (2 * Real.exp 1)) := by
        rw [show 2 * (1 / (2 * Real.exp 1)) = 1 / Real.exp 1 from by ring]
        have h1 : 1 / Real.exp 1 < 1 := by
          rw [div_lt_one (Real.exp_pos 1)]; linarith [Real.exp_one_gt_d9]
        linarith
      positivity
    exact mul_nonneg rhsCSF_pos.le (by positivity)
  -- the truncated factoring at `y₂`, with the compact minimality as the only frequency
  -- hypothesis
  have hJ1 := joint_cs_trunc_pin2 hg hk hL hy hη hc₀ hh0 hXk hgate hmin hFfar0 hFar hKfar
    ⟨hIβ, hIβ', hIα, hIα'⟩
  -- the MAIN term: the width face at the DECOUPLED width
  have hper : ∀ α ∈ Icc (0 : ℝ) η,
      (∫ β in (0 : ℝ)..η,
          rhsFbound (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
              L (β + 1 / L)
            * crossKer (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀
                (t₀ + t₁) α β)
        ≤ (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α))
            * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                L :=
    fun α hα => beta_integral_pin_const2 _ hgtw hCb0 hCbound hk hL hy hη hc₀ hh hM0
      hα.1 hα.2 (hIβ α hα)
  have hKcont : Continuous
      (fun α : ℝ => (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α))
        * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L) :=
    ((continuous_rpow_neg2 hkh0).const_mul _).mul continuous_const
  have hmono := intervalIntegral.integral_mono_on hη0'.le hIα
    (hKcont.intervalIntegrable 0 η) hper
  have hfe : ∀ α : ℝ, (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α))
        * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L
      = (widthKamp Cb k h (L ^ 4) c₀
            * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
          * ((k + h) ^ (-α)) := fun α => by ring
  have hpull : (∫ α in (0 : ℝ)..η, (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α))
        * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
      = (widthKamp Cb k h (L ^ 4) c₀
            * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
          * ∫ α in (0 : ℝ)..η, (k + h) ^ (-α) := by
    simp only [hfe]
    exact intervalIntegral.integral_const_mul _ _
  have hint_le : (∫ α in (0 : ℝ)..η, (k + h) ^ (-α)) ≤ 1 / L := by
    have h1 : (∫ α in (0 : ℝ)..η, (k + h) ^ (-α)) ≤ 1 / Real.log (k + h) :=
      alpha_rpow_integral_le (by linarith [Real.add_one_le_exp (32768 : ℝ)]) hη0'.le
    have h2 : L ≤ Real.log (k + h) := by
      rw [hL]; exact Real.log_le_log hk0 (by linarith)
    have h3 : (0 : ℝ) < Real.log (k + h) := by linarith
    have h4 : 1 / Real.log (k + h) ≤ 1 / L := by
      rw [div_le_div_iff₀ h3 hL0]; linarith
    linarith
  have hstep : (1 / Real.pi) * ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
        rhsFbound (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
            L (β + 1 / L)
          * crossKer (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀
              (t₀ + t₁) α β
      ≤ (1 / Real.pi) * ((widthKamp Cb k h (L ^ 4) c₀
          * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
            * (1 / L)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
              rhsFbound (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                  L (β + 1 / L)
                * crossKer (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀
                    (t₀ + t₁) α β)
        ≤ ∫ α in (0 : ℝ)..η, (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α))
            * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                L := hmono
      _ = (widthKamp Cb k h (L ^ 4) c₀
            * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
              * ∫ α in (0 : ℝ)..η, (k + h) ^ (-α) := hpull
      _ ≤ (widthKamp Cb k h (L ^ 4) c₀
            * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
              * (1 / L) := mul_le_mul_of_nonneg_left hint_le (mul_nonneg hKamp0 hG0)
  have hmaineq : (1 / Real.pi) * ((widthKamp Cb k h (L ^ 4) c₀
        * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
          * (1 / L))
      = rhsAgradeConst Cb k h (L ^ 4) c₀
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
    have hexpeq : Real.exp (-(1 / (2 * Real.exp 1)
          * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X))
        = Real.exp (-(1 / (2 * Real.exp 1))
          * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
      rw [neg_mul]
    have hπne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    unfold rhsAgradeConst rhsSigmaG
    rw [← hexpeq]
    field_simp
  -- the amplitude at the absolute constant: the CORPUS page, at `y = L⁴`, unchanged
  have habs : rhsAgradeConst Cb k h (L ^ 4) c₀
        * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
      ≤ gradeAbsConst Cb * k
        * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) :=
    mul_le_mul_of_nonneg_right (rhsAgradeConst_le hCb0 hk64 hL rfl hh hc₀) (Real.exp_nonneg _)
  have hmain := hstep.trans (le_of_eq hmaineq)
  linarith

/-! ## §4 — FarStar's FS-5 at `y₂`: the closed chain

`FarStar`'s FS-5 triple, re-run at the R2 pin.  The first two members land here; the third
(`ball_sup_closed_star2`) does NOT, and the reason is recorded at the end of the section
rather than papered over. -/

set_option maxHeartbeats 800000 in
-- As at `FarClose.rhs_grade_at_scale_closed` / `FarStar.rhs_grade_at_scale_closed_star`: the
-- composition instantiates the truncated grade's sockets, each carrying the five pin
-- expressions, and the `M`-term is a large opaque `pretDistSq`; the unification exceeds the
-- default budget.
/-- **FS-5a at `y₂` — THE CLOSED GRADE AT SCALE (`rhs_grade_at_scale_closed_star2`).**
`FarStar.rhs_grade_at_scale_closed_star` at the R2 pin, `T := T*₂`, `R := seamGateRstar2`:

  `‖prop21RHS … y₂ η₂‖ ≤ (gradeAbsConst Cb + farCStar2)·k·e^{−(1/(2e))·𝔻²}`.

All three of the landed chain's arithmetic sockets are discharged, at the NEW pin:

* `hKfar` by `PinFamily.far_kernel_bound_star2` (FS-2 at `T*₂`),
* `hfar` by `PinFamily.hfar_star2` (FS-3 at `T*₂` — with margin `2L⁴/y₂ ≤ 1`, i.e.
  `exp(−L^{2/5})`-small, against `FarStar`'s `2/(√L·log L)`),
* `hgate` by §2's `seam_gate_star2_of_nonempty` from the ball leg's nonemptiness.

The exit constant is `gradeAbsConst Cb + farCStar2`: the main half is the CORPUS constant
(§3's ruling — the width never moved) and only the far half carries the pin.

**The carried hypotheses, enumerated.**  (1) the pin equations `hL/hy/hη/hc₀/hh` and the
family gate `exp 32768 ≤ k`; (2) `hXk`, `hXe`, and the row's two scale relations `hX2k`,
`hkX`; (3) `hne`, the ball leg's domain being nonempty; (4) `hmin`, the compact minimality at
radius `seamGateRstar2 X T_ann`; (5) `hMcap`, the crown's A-10 ball cap; (6) the
`JointIntegrableAt` bundle.  **No far socket, no kernel socket, no gate socket.** -/
theorem rhs_grade_at_scale_closed_star2 {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Cb t₀ t₁ X k L c₀ y η h Tann : ℝ}
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L)
    (hXk : ⌊X⌋₊ ≤ ⌊k⌋₊) (hXe : Real.exp 1 ≤ X) (hX2k : X ≤ 2 * k) (hkX : k ≤ 2 * X)
    (hne : (seamAnn X Tann ∩ seamBall X t₁).Nonempty)
    (hmin : ∀ v : ℝ, |v| ≤ seamGateRstar2 X Tann →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hMcap : pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
      ≤ 1 / 16 * Real.log (Real.log X))
    (hInt : JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
      (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) k L c₀ y η h) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁) k h c₀ y η‖
      ≤ (gradeAbsConst Cb + farCStar2) * k
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
  obtain ⟨hk0, hL32, -, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hgtw : ∀ p, p.Prime →
      ‖(fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist (t₀ + t₁) hp.one_lt.le, mul_one]
    exact hg p hp
  have hgate : |t₁| + Tstar2 k L ≤ seamGateRstar2 X Tann := by
    rw [hL]
    exact seam_gate_star2_of_nonempty hk hkX hne
  have hKf : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀ (t₀ + t₁)
          α β (Tstar2 k L)
        ≤ farKfarStar2 (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k L := by
    rw [hh]
    exact far_kernel_bound_star2 hk hL hy hη hc₀
  have hmain := rhs_grade_at_scale_trunc2 hg hCb0 hCbound hk hL hy hη hc₀ hh hXk hgate hmin
    (farFbound_nonneg hL0.le) (far_supF_bound2 hg hk hL hy hη hc₀) hKf hInt
  have hprice := far_term_priced (M := pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀)
      (costwist t₁) X) (X := X) hXe hk0.le farCStar2_nonneg hMcap
    (hfar_star2 hgtw hk hL hy hη hXe hX2k)
  have hring : (gradeAbsConst Cb + farCStar2) * k
        * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
      = gradeAbsConst Cb * k
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
        + farCStar2 * k
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
    ring
  linarith

set_option maxHeartbeats 800000 in
-- As at `FarStar.hRHS_socket_star`: the binder shape carries five pin expressions per socket,
-- unified against the closed grade's own pin equations.
/-- **FS-5b at `y₂` — THE PER-SCALE SOCKET (`hRHS_socket_star2`).**
`FarStar.hRHS_socket_star` at the R2 pin: the `∀ k ∈ [⌊X⌋₊, N]` form of FS-5a, with
`T k := T*₂(k, log k)` and `Kfar k := farKfarStar2`, and its three per-scale sockets
(`hgate`, `hKf`, `hfar`) DISCHARGED.  What remains quantified over the scale is only the
family gate `exp 32768 ≤ k` and upstream's own integrability.

**⚠ THE CONSUMER GAP (recorded, not papered over).**  `FarStar.hRHS_socket_star`'s value is
that its statement is `CenterSupply.ball_sup_supplied`'s `hRHS` hypothesis BYTE-FOR-BYTE.
That is not available here: `ball_sup_supplied` (`CenterSupply` :477–482) has the CORPUS pin
`(log k)⁴`, `1/log((log k)⁴)` written INTO its hypothesis, so no `y₂`-shaped socket can feed
it.  Closing that needs either a pin-generic twin of the `CenterSupply` chain
(`ball_sup_supplied` → `center_halasz_supply` → `ball_sup_of_center`) or a statement change
on a landed stone — Fable/JYH tier, Iron rule 1.  The socket below is therefore the honest
`y₂` object, ready for such a twin, and `ball_sup_closed_star2` is NOT claimed. -/
theorem hRHS_socket_star2 {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Cb t₀ t₁ X Tann : ℝ} {N : ℕ}
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb) (hXe : Real.exp 1 ≤ X)
    (hN2X : (N : ℝ) ≤ 2 * X)
    (hmin : ∀ v : ℝ, |v| ≤ seamGateRstar2 X Tann →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hMcap : pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
      ≤ 1 / 16 * Real.log (Real.log X))
    (hkg : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → pin2Gate ≤ (k : ℝ))
    (hne : (seamAnn X Tann ∩ seamBall X t₁).Nonempty)
    (hInt : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
        (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) (k : ℝ)
        (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (ypin2 (Real.log (k : ℝ)))
        (eta2 (Real.log (k : ℝ))) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) :
    ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
          (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
          (ypin2 (Real.log (k : ℝ))) (eta2 (Real.log (k : ℝ)))‖
        ≤ (gradeAbsConst Cb + farCStar2) * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  intro k hk1 hk2
  have hk := hkg k hk1 hk2
  have hkexp : Real.exp 32768 ≤ (k : ℝ) := hk
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 32768) hkexp
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by
    have h65 : (32769 : ℝ) ≤ (k : ℝ) := by linarith [Real.add_one_le_exp (32768 : ℝ)]
    linarith
  have hXk : ⌊X⌋₊ ≤ ⌊(k : ℝ)⌋₊ := by rw [Nat.floor_natCast]; exact hk1
  have hX2k : X ≤ 2 * (k : ℝ) := by
    have h1 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
    have h2 : (⌊X⌋₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hkX : (k : ℝ) ≤ 2 * X := le_trans (by exact_mod_cast hk2) hN2X
  exact rhs_grade_at_scale_closed_star2 hg hCb0 hCbound hk rfl rfl rfl rfl rfl hXk hXe hX2k
    hkX hne hmin hMcap (hInt k hk1 hk2)

/-! ## §5 — the CASE-A exit constant at `y₂` (⟦V7⟧'s `caseAS` re-read)

`CofactorGrade.caseAS` is the CASE-A exit `S = gradeAbsConstC c Cb·e^{−cM} + (far arm at
`T*`) + (the centre supply's desmooth/`E` slot)`.  At the R2 pin only two of its three
summands move, and neither moves in SHAPE:

* the far summand's constant becomes `farCStar2` (`PinFamily`'s §4) — same
  `(log W)^{−1/(32e)}` currency;
* the `E` slot is where the `S1′` error at `y₂` has to fit, and it does, for EVERY `C_E`
  (`PinFamily.E_slot_pin2_le`, ⟦V6b⟧ freeze risk (iii)) — the `2/5` choice makes the
  absorption loose, which is exactly why it was pinned at `2/5` and not `1/2`.

The grade summand's constant `gradeAbsConstC c Cb` does NOT move (§3's ruling at a free `c`
is the residual — see the module report). -/

/-- **The CASE-A exit constant at the R2 pin (`caseAS2`).**  `CofactorGrade.caseAS` with
`farCStar2` in place of `farCStar`.  Shape-identical; only the far arm's absolute constant
changes with the pin. -/
def caseAS2 (c Cb M W : ℝ) : ℝ :=
  gradeAbsConstC c Cb * Real.exp (-c * M)
    + farCStar2 * Real.log W ^ (-(1 / (32 * Real.exp 1)))
    + 4 * Real.log W ^ (-(1 : ℝ) / 2 + 1 / 1000)

lemma caseAS2_nonneg {c Cb M W : ℝ} (hc1 : 2 * c < 1) (hCb0 : 0 ≤ Cb) (hW : 1 ≤ W) :
    0 ≤ caseAS2 c Cb M W := by
  have h1 : (0 : ℝ) ≤ gradeAbsConstC c Cb := gradeAbsConstC_nonneg hc1 hCb0
  have hlogW : (0 : ℝ) ≤ Real.log W := Real.log_nonneg hW
  have h3 : (0 : ℝ) ≤ Real.log W ^ (-(1 / (32 * Real.exp 1))) := Real.rpow_nonneg hlogW _
  have h4 : (0 : ℝ) ≤ Real.log W ^ (-(1 : ℝ) / 2 + 1 / 1000) := Real.rpow_nonneg hlogW _
  have h5 : (0 : ℝ) ≤ Real.exp (-c * M) := (Real.exp_pos _).le
  unfold caseAS2
  have h6 : (0 : ℝ) ≤ gradeAbsConstC c Cb * Real.exp (-c * M) := mul_nonneg h1 h5
  have h7 : (0 : ℝ) ≤ farCStar2 * Real.log W ^ (-(1 / (32 * Real.exp 1))) :=
    mul_nonneg farCStar2_nonneg h3
  linarith

/-- **The `E`-slot compose at `y₂` (`caseAS2_absorbs_E_slot`).**  The `S1′` error at the R2
pin, after the `W/log W` normalisation, is `C_E·(log W)^{2/5}/log W`; `caseAS2`'s third
summand `4·(log W)^{−1/2+1/1000}` swallows it as soon as `C_E ≤ 4·(log W)^{101/1000}`:

  `gradeAbsConstC c Cb·e^{−cM} + farCStar2·(log W)^{−1/(32e)} + C_E·(log W)^{2/5}/log W
     ≤ caseAS2 c Cb M W`.

This is `PinFamily.E_slot_pin2_le` composed into the CASE-A constant — ⟦V6b⟧'s freeze risk
(iii) cashed at the consumer.  The `C_E`-dependent threshold is the one ⟦V6b⟧ flags; it is
kept in-statement (law #253) rather than hidden in an `X₀`. -/
theorem caseAS2_absorbs_E_slot {c Cb M W C_E : ℝ} (hW : 32768 ≤ Real.log W)
    (hgate : C_E ≤ 4 * Real.log W ^ ((101 : ℝ) / 1000)) :
    gradeAbsConstC c Cb * Real.exp (-c * M)
        + farCStar2 * Real.log W ^ (-(1 / (32 * Real.exp 1)))
        + C_E * Real.log W ^ ((2 : ℝ) / 5) / Real.log W
      ≤ caseAS2 c Cb M W := by
  have hslot := E_slot_pin2_le hW hgate
  unfold caseAS2
  linarith

/-- **The `E`-slot closes at `y₂`, for every `C_E`** (`caseAS2_absorbs_E_slot_closes`).
`PinFamily.E_slot_pin2_closes` in `caseAS2`'s shape: the threshold on `log W` is explicit and
grows with `C_E`, and nothing else in the CASE-A constant is `C_E`-dependent. -/
theorem caseAS2_absorbs_E_slot_closes (C_E : ℝ) :
    ∃ L₀ : ℝ, 32768 ≤ L₀ ∧ ∀ c Cb M W : ℝ, L₀ ≤ Real.log W →
      gradeAbsConstC c Cb * Real.exp (-c * M)
          + farCStar2 * Real.log W ^ (-(1 / (32 * Real.exp 1)))
          + C_E * Real.log W ^ ((2 : ℝ) / 5) / Real.log W
        ≤ caseAS2 c Cb M W := by
  obtain ⟨L₀, hL₀, hslot⟩ := E_slot_pin2_closes C_E
  refine ⟨L₀, hL₀, ?_⟩
  intro c Cb M W hLW
  have h := hslot (Real.log W) hLW
  unfold caseAS2
  linarith

end Salt.MR
