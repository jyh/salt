/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ThmA2
import Salt.MR.CapFreeArm3

/-!
# S8 ladder, node A2-7 — **THE ROW SUPPLIERS AND THE GLUE** (`ThmA2Rows`)

Freeze: `docs/exploration/s8-freeze-0727.md`, ⟦AMENDMENT H⟧ (the final wave).

`ThmA2.thm_a2'_of_rows` takes the weighted seam-row family as its `hrows` binder.  This
file supplies that binder on both branches of the `CapFreeFloor` dichotomy and composes the
two into `thm_a2'`.

* §1 — the WEIGHTING GATES, on fresh variables: the four numerals `9 / 244 / 3 / (3/2)`
  of `ThmA2`'s `a2Mrow` docstring, proved once (`a2_weight_gates`).
* §2 — `a2Rows_of_capfree`: `CapFreeArm.seam_row_number_capfree` at `Tann := 2T`, fed by
  `ThmA2.A2Frame` and the `Tann`-free binders, weighted into `a2Mrow`.  UNCONDITIONAL on
  its branch (the `CapFreeFloor` datum is the branch hypothesis).
* §3 — `a2Rows_of_cap`: `CapFreeArm.seam_row_number_nocap` at `t₁ := v₀`, the routing
  witness, with `PocketSocket` from `CapFreeArm.pocketSocket_of_row`.  CONDITIONAL, in
  statement, on the ball-leg supply `hStation` (see the T3 note below).
* §4 — `thm_a2'`: the `by_cases` glue.

## The T3 gap and the station, stated exactly (law #253)

`a2Rows_of_cap` carries the ball-leg supply as a hypothesis

  `hStation : ∀ t₁, |t₁| ≤ X → ∀ t, seamT0 X ≤ |t| → |t| ≤ X → |t − t₁| ≤ seamRad X →
              ∀ m ≤ N, ‖spolyA a t m‖ ≤ Sb·m/(1 + |t − t₁|)`

rather than deriving it from `SPartStation.seam_ball_leg_station_M_gen`.  TWO reasons, both
structural and both recorded here rather than hidden:

1. **The T3 gap** (⟦AMENDMENT B⟧, `ThmA2` §6).  The station's `hMcap` — the A-10 cap
   `𝔻²(seamCoeff g 1 t₀, p^{it₁}; x) ≤ (1/16)loglog X` on `x ∈ [X,2X]` — is a statement
   about the `t₀`-SHIFTED datum, and the routing witness gives only
   `𝔻²(g, p^{iv₀}; X) ≤ (1/32)loglog X + 25` on the BARE datum.  It is not derivable; it is
   an input.  `a2_station_supply_pointwise` below states the station AT A FIXED CENTRE with
   that cap (and the `M₀` floor, and the datum equation) as visible binders — that is the
   exact price of `hStation`, kernel-checked, one centre at a time.
2. **The threshold is centre-dependent as stated.**  `seam_ball_leg_station_M_gen` reads
   `∃ X₀, 0 < X₀ ∧ ∀ X …, X₀ ≤ √X → …` UNDER `∀ t₀ t₁`, so its `X₀` may depend on the
   centre.  The branch's centre `v₀` is produced inside the proof (by
   `ThmA2.a2_row_cap_of_not_capFreeFloor`), so no single `X₀ ≤ √X` hypothesis can be stated
   in advance.  (The landed proof's witness is in fact `t₁`-free — it is
   `max (max X₁ ballMertensThreshold) (exp 4096)` with `X₁` from `center_halasz_supply_wide`
   at `t₀` — but that is invisible to a consumer of the statement.)

`M_window_bridge_seam` supplies the station's `M₀` floor on the box `|v| ≤ X`; the station's
recentring gate needs it out to `Rad ≥ |t₁| + T*(2X, log 2X)`, so on this branch the floor
is carried at `Rad` (the D10 defect, at the row's own centre).

## The `8S²` summand on the cap branch

The cap branch's row is run at a produced centre, so its ball leg is NOT vacuous and the
row's `8S²` summand is present — while `a2Mrow` has no `M`-shaped slot (the interface's
`M`-term rides the `T₀` band, `ThmA2` §4).  It is paid, in statement, out of `a2Mrow`'s FREE
constant slot: `a2Rows_of_cap` asks `C + M·Sb²/2 ≤ Ccc` and the obligation then surfaces
at `thm_a2'_of_rows`' own `hgRows` gate at that `Ccc`.  Nothing is absorbed silently, and
⟦AMENDMENT G⟧'s `×4` cover is left intact for what it was priced for.
-/

noncomputable section

namespace Salt.MR

open MeasureTheory Complex
open scoped BigOperators

/-! ## §1 — the weighting gates

`ThmA2`'s `a2Mrow` docstring, proved: at `X/h ≤ T`, `2T ≤ X`, `X ≤ 4X_d`, `Q₁ ≤ h` and
`h ≥ 4` the four `Tann`-linear factors of the seam row weigh in at `9`, `244`, `3` and
`3/2`.  On FRESH variables, so that no `set` body meets a nonlinear call. -/

/-- **THE FOUR NUMERALS** (`a2_weight_gates`).  With `w := (X/h)/T` the weight of the
dyadic family: `0 ≤ w ≤ 1`, and

  `w·(2T·Q₁/X_d + 1) ≤ 9`,  `w·(2·(2T)/X_d + 240) ≤ 244`,
  `w·(2T/X_d + 1) ≤ 3`,     `w·(2T/X + 1) ≤ 3/2`.

Everything reduces to `(X/h)/X_d ≤ 4/h` (from `X ≤ 4X_d`) and `w ≤ 1` (from `X/h ≤ T`). -/
private lemma a2_weight_gates {X h T Xd Q1 : ℝ} (hh4 : 4 ≤ h) (hX0 : 0 < X)
    (hT : X / h ≤ T) (hXd : X ≤ 4 * Xd) (hQ1 : Q1 ≤ h) (hQ10 : 0 ≤ Q1) :
    0 ≤ X / h / T ∧ X / h / T ≤ 1 ∧
      X / h / T * (2 * T * Q1 / Xd + 1) ≤ 9 ∧
      X / h / T * (2 * (2 * T) / Xd + 240) ≤ 244 ∧
      X / h / T * (2 * T / Xd + 1) ≤ 3 ∧
      X / h / T * (2 * T / X + 1) ≤ 3 / 2 := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hu0 : (0 : ℝ) < X / h := div_pos hX0 hh0
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le hu0 hT
  have hXd0 : (0 : ℝ) < Xd := by linarith
  have hw0 : (0 : ℝ) ≤ X / h / T := le_of_lt (div_pos hu0 hT0)
  have hw1 : X / h / T ≤ 1 := (div_le_one hT0).mpr hT
  have hratio : X / h / Xd ≤ 4 / h := by
    rw [div_div, div_le_div_iff₀ (by positivity) hh0]
    nlinarith
  have hr0 : (0 : ℝ) ≤ X / h / Xd := le_of_lt (div_pos hu0 hXd0)
  refine ⟨hw0, hw1, ?_, ?_, ?_, ?_⟩
  · have hid : X / h / T * (2 * T * Q1 / Xd + 1) = 2 * Q1 * (X / h / Xd) + X / h / T := by
      field_simp
    have h8 : 2 * Q1 * (X / h / Xd) ≤ 8 := by
      have hstep : 2 * Q1 * (X / h / Xd) ≤ 2 * Q1 * (4 / h) :=
        mul_le_mul_of_nonneg_left hratio (by linarith)
      have hval : 2 * Q1 * (4 / h) ≤ 8 := by
        rw [show 2 * Q1 * (4 / h) = 8 * Q1 / h by ring, div_le_iff₀ hh0]
        linarith
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * (2 * T) / Xd + 240)
        = 4 * (X / h / Xd) + 240 * (X / h / T) := by
      field_simp; ring
    have h16 : 4 * (X / h / Xd) ≤ 4 := by
      have hstep : 4 * (X / h / Xd) ≤ 4 * (4 / h) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      have hval : 4 * (4 / h) ≤ 4 := by
        rw [show 4 * (4 / h) = 16 / h by ring, div_le_iff₀ hh0]
        linarith
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * T / Xd + 1) = 2 * (X / h / Xd) + X / h / T := by
      field_simp
    have h8 : 2 * (X / h / Xd) ≤ 2 := by
      have hstep : 2 * (X / h / Xd) ≤ 2 * (4 / h) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      have hval : 2 * (4 / h) ≤ 2 := by
        rw [show 2 * (4 / h) = 8 / h by ring, div_le_iff₀ hh0]
        linarith
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * T / X + 1) = 2 / h + X / h / T := by
      field_simp
    have h2 : 2 / h ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hh0 (by norm_num)]
      linarith
    rw [hid]; linarith

/-- The weighting, summand by summand: four bounds compose into one. -/
private lemma a2_row_weigh {w A B C D a b c d : ℝ}
    (hA : w * A ≤ a) (hB : w * B ≤ b) (hC : w * C ≤ c) (hD : w * D ≤ d) :
    w * (A + B + C + D) ≤ a + b + c + d := by
  have h : w * (A + B + C + D) = w * A + w * B + w * C + w * D := by ring
  rw [h]; linarith

/-- The §8.1 level-1 summand, weighted: the weight rides into the row's own free factor `R`
(`DoorFrameH1.level1_term_door_decays`' `R`-slot), where the `9`-gate meets it. -/
private lemma a2_level1_weigh {w Hq Lq R Pq Br Z : ℝ}
    (hkey : ∀ R' : ℝ, 0 ≤ R' → 2 * (Hq * Lq + 1) * R' * Pq * Br ≤ 5280 * R' * Z)
    (hR0 : 0 ≤ w * R) (hR9 : w * R ≤ 9) (hZ0 : 0 ≤ Z) :
    w * (2 * (Hq * Lq + 1) * R * Pq * Br) ≤ 47520 * Z := by
  have hid : w * (2 * (Hq * Lq + 1) * R * Pq * Br)
      = 2 * (Hq * Lq + 1) * (w * R) * Pq * Br := by ring
  rw [hid]
  refine le_trans (hkey (w * R) hR0) ?_
  nlinarith [mul_nonneg hZ0 (by linarith : (0 : ℝ) ≤ 9 - w * R)]

/-- The `Cs`-summand, weighted at the `244`-gate: `1536·244 = 374784`. -/
private lemma a2_term2_weigh {w Cs R Y : ℝ} (hCs : 0 ≤ Cs) (hY : 0 ≤ Y) (hR : w * R ≤ 244) :
    w * (1536 * Cs * Real.exp 3 * R * Y) ≤ 374784 * Cs * Real.exp 3 * Y := by
  have hid : w * (1536 * Cs * Real.exp 3 * R * Y)
      = 1536 * Cs * Real.exp 3 * Y * (w * R) := by ring
  have h0 : (0 : ℝ) ≤ 1536 * Cs * Real.exp 3 * Y := by positivity
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR h0]

/-- The Lemma-12 summand, weighted at the `3`-gate: `480·3 = 1440`, and ⟦AMENDMENT G⟧'s
`×4` cover carries it to `a2Mrow`'s `5760`. -/
private lemma a2_term3_weigh {w R S : ℝ} (hS : 0 ≤ S) (hR : w * R ≤ 3) :
    w * (480 * R * S) ≤ 5760 * S := by
  have hid : w * (480 * R * S) = 480 * S * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 480) hS)]

/-- **THE LEMMA-12 SUMMAND AT ⟦WALL 1⟧'s MR ROW** (`a2_term3_weigh_mr`).  The `hwin`-free
four-row exit prices the seam row at `960·(T_ann/X_d+1)·(…)` in place of `480·(…)`
(`M4RowMR`), so the `3`-gate gives `960·3 = 2880` — still inside `a2Mrow`'s `5760`, which is
⟦AMENDMENT G⟧'s `×4` cover of `1440`.  **The interface numeral does not move.** -/
private lemma a2_term3_weigh_mr {w R S : ℝ} (hS : 0 ≤ S) (hR : w * R ≤ 3) :
    w * (960 * R * S) ≤ 5760 * S := by
  have hid : w * (960 * R * S) = 960 * S * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 960) hS)]

/-- The `𝒰`-leg summand, weighted at the `3/2`-gate: `2·(3/2) = 3`. -/
private lemma a2_term4_weigh {w R Z : ℝ} (hZ : 0 ≤ Z) (hR : w * R ≤ 3 / 2) :
    w * (2 * (R * Z)) ≤ 3 * Z := by
  have hid : w * (2 * (R * Z)) = 2 * Z * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (by linarith : (0 : ℝ) ≤ 2 * Z)]

/-- `a2RowsSum` is a sum of nonnegative terms (`1 ≤ X_d`, `H₁ ≥ 2`, `P_j ≥ 1`). -/
private lemma a2RowsSum_nonneg {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) :
    0 ≤ a2RowsSum M Xd := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hH1 : (2 : ℝ) ≤ H1door M := H1door_two hM
  unfold a2RowsSum
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have hcalH : (0 : ℝ) < calH (H1door M) j := by
    rw [calH]; nlinarith
  have hP1 : (1 : ℝ) ≤ ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ) := by
    have h : 1 ≤ calP (Adoor M) (3072 * M) j := by
      simp only [calP]; exact Nat.one_le_two_pow
    exact_mod_cast h
  have hlogb : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have h1 : (0 : ℝ) ≤ (Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1door M) j + 1)
      * (Real.exp 1 / (Xd : ℝ) ^ 2)) := by
    have hq : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH (H1door M) j :=
      div_nonneg (by positivity) hcalH.le
    have hr : (0 : ℝ) ≤ Real.exp 1 / (Xd : ℝ) ^ 2 := by positivity
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ)
      / calH (H1door M) j + 1) hr
    nlinarith
  have h2 : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ))
      / ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ) :=
    div_nonneg (by linarith) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 / (Xd : ℝ) := by positivity
  linarith

/-- The cap branch's weighting: five summands, the ball leg folded into the row slot. -/
private lemma a2_row_weigh_cap {w Sq A B C D a b c d : ℝ}
    (hA : w * A ≤ a) (hB : w * B ≤ b) (hSC : w * Sq + w * C ≤ c) (hD : w * D ≤ d) :
    w * (Sq + (A + B + C) + D) ≤ a + b + c + d := by
  have h : w * (Sq + (A + B + C) + D) = w * A + w * B + (w * Sq + w * C) + w * D := by ring
  rw [h]; linarith

/-- **THE BALL LEG, INTO THE ROW SLOT.**  `a2Mrow` has no `M`-shaped summand, so the
socketed row's `8S²` is paid by `a2Mrow`'s FREE constant `Ccc` at `C + M·Sb²/2 ≤ Ccc`:
`5760·Ccc·(2/M) ≥ 5760·C·(2/M) + 5760·Sb²`, of which `8·Sb²` is a `720`-th.  ⟦AMENDMENT G⟧'s
`×4` cover (the `1440 → 5760` headroom) is NOT spent here. -/
private lemma a2_ball_into_rows {Sb RS Cst Ccc Mr : ℝ} (hRS : 0 ≤ RS) (hC0 : 0 ≤ Cst)
    (hM1 : 1 ≤ Mr) (hCcc : Cst + Mr * Sb ^ 2 / 2 ≤ Ccc) :
    8 * Sb ^ 2 + 1440 * (RS + Cst * (2 / Mr)) ≤ 5760 * (RS + Ccc * (2 / Mr)) := by
  have hM0 : (0 : ℝ) < Mr := by linarith
  have hq0 : (0 : ℝ) < 2 / Mr := by positivity
  have hstep : (Cst + Mr * Sb ^ 2 / 2) * (2 / Mr) ≤ Ccc * (2 / Mr) :=
    mul_le_mul_of_nonneg_right hCcc hq0.le
  have hexp : (Cst + Mr * Sb ^ 2 / 2) * (2 / Mr) = Cst * (2 / Mr) + Sb ^ 2 := by
    field_simp
  rw [hexp] at hstep
  have hCq : (0 : ℝ) ≤ Cst * (2 / Mr) := mul_nonneg hC0 hq0.le
  linarith [sq_nonneg Sb]

/-- The Lemma-12 summand at the `3`-gate, unweighted by the cover: `480·3 = 1440`. -/
private lemma a2_term3_weigh_flat {w R S : ℝ} (hS : 0 ≤ S) (hR : w * R ≤ 3) :
    w * (480 * R * S) ≤ 1440 * S := by
  have hid : w * (480 * R * S) = 480 * S * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 480) hS)]

/-- The cap branch's third slot: ball leg plus Lemma-12 rows, into `a2Mrow`'s `5760`.

**THE ONE-STEP RE-PROOF** (⟦THE WALL⟧'s wave, REFUTE-RESIDUE correction 4).  The rows are
weighed at `a2_term3_weigh`'s FULL `5760` — the same constant the cap-FREE branch spends —
and the `8S²` ball leg is paid ENTIRELY out of `Ccc`'s free slack, of which it is a
`720`-th: `hCcc` gives `Ccc·(2/M) ≥ Cst·(2/M) + S²`, hence `5760·S²` of room against a
demand of `8·S²`.  ⟦AMENDMENT G⟧'s `×4` cover (`1440 → 5760`) is therefore NOT spent here at
all — it stays available to the rows, exactly as on the cap-free branch, which is what makes
the two branches' `hR : w·R ≤ 3` gates readable as the same gate. -/
private lemma a2_term3_ball_weigh {w R Sb RS Cst Ccc Mr : ℝ}
    (hw1 : w ≤ 1) (hRS : 0 ≤ RS) (hC0 : 0 ≤ Cst) (hM1 : 1 ≤ Mr)
    (hCcc : Cst + Mr * Sb ^ 2 / 2 ≤ Ccc) (hR : w * R ≤ 3) :
    w * (8 * Sb ^ 2) + w * (480 * R * (RS + Cst * (2 / Mr)))
      ≤ 5760 * (RS + Ccc * (2 / Mr)) := by
  have hM0 : (0 : ℝ) < Mr := by linarith
  have hq0 : (0 : ℝ) < 2 / Mr := by positivity
  have hCq : (0 : ℝ) ≤ Cst * (2 / Mr) := mul_nonneg hC0 hq0.le
  have hball : w * (8 * Sb ^ 2) ≤ 8 * Sb ^ 2 := by nlinarith [sq_nonneg Sb]
  have hrows := a2_term3_weigh (w := w) (R := R) (S := RS + Cst * (2 / Mr))
    (by linarith) hR
  have hslack : (Cst + Mr * Sb ^ 2 / 2) * (2 / Mr) ≤ Ccc * (2 / Mr) :=
    mul_le_mul_of_nonneg_right hCcc hq0.le
  have hexp : (Cst + Mr * Sb ^ 2 / 2) * (2 / Mr) = Cst * (2 / Mr) + Sb ^ 2 := by field_simp
  rw [hexp] at hslack
  linarith [sq_nonneg Sb]

/-! ## §2 — the CAP-FREE branch supplies `hrows`

`CapFreeArm.seam_row_number_capfree` at `Tann := 2T` for every `T` in the dyadic family
`X/h ≤ T`, `2T ≤ X`, weighted by `(X/h)/T` and read against `ThmA2.a2Mrow`.  The `Tann`
binders come from `ThmA2.A2Frame` (with `box`/`ksGate` transferred from the window's top by
the landed anti-monotone lemmas); the `E`-pair collapses at the row's own ceiling
(`hErow` by `le_rfl`); the `Tann`-free binders are carried one for one. -/

set_option maxHeartbeats 1000000 in
-- one predicate-blind application of the landed cap-free row at `Tann = 2T`, with ~60
-- binders threaded; the elaboration of that single application is the whole cost
/-- **THE CAP-FREE ROW FAMILY** (`a2Rows_of_capfree`).  On the `CapFreeFloor` branch, the
`hrows` binder of `ThmA2.thm_a2'_of_rows` — the WEIGHTED seam-row family at the corrected
door pin (`A = Adoor M`, `G = 3072M`, `Jb = 2`, `H₁ = H1door M`, `η = 1/12`) — with the
row's own constants `Cs`, `C` exposed for the interface's two grading gates.

The four weighting numerals are `ThmA2`'s own (`a2Mrow`'s docstring), proved in §1 from
`X/h ≤ T`, `2T ≤ X`, `X ≤ 4X_d` (the row's `X ≤ N ≤ 4X_d`), `Q₁ ≤ h` (the `[P₁,Q₁] ⊆ [1,h]`
gate) and `h ≥ 4`.  Nothing is conditional: on this branch the ball leg is VACUOUS
(`t₁ := 0`, `S := 0`) inside the landed capstone, so no station, no produced centre, no
`8S²`. -/
theorem a2Rows_of_capfree :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad kmin Ymax ε EP2 : ℝ),
        1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
        A2Frame g cf a N Xd P Q (Adoor M) (3072 * M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        CapFreeFloor g X →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
          p ≤ calQK (Adoor M) (3072 * M) M j → ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
          p ≤ calQK (Adoor M) (3072 * M) M j → c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
                    (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_capfree
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin Ymax ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hCb0 hPlow
    hQ0 hQhigh hPQ83 hfloor hR0 hRrad hRlow hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW
    hYpin hWY hXY hthr hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef hwin hQXd hXdbig hN4
    hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (3072 * M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at M Xd hM hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`⟧
  have hinst := hrow g c a b cf hg hc1 hb1 hcf1 N Xd P Q (Adoor M) (3072 * M) M 2 m₀ Ms Mt kk
    (H1door M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad kmin Ymax ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hfloor hR0 hRrad hRlow (F.blocks _ h2a h2b)
    (F.box_at h2b) hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl (F.err _ h2a h2b) hXN hN2 hsupp
    hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum_nonneg hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge M]
  have hlvl0 : (0 : ℝ) ≤ a2Level1 M := by
    unfold a2Level1
    exact div_nonneg
      (Real.rpow_nonneg (le_trans (by norm_num) (one_le_log_calQK_door_one hM)) _)
      (Real.rpow_pos_of_pos hP0 _).le
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow
  refine a2_row_weigh ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_weigh hRS0 hg3
  · exact a2_term4_weigh hZ0 hg32


/-! ## §3 — the SOCKETED branch supplies `hrows`

`CapFreeArm.seam_row_number_nocap` at the routing witness, with the collision socket closed
by `CapFreeArm.pocketSocket_of_row` and the ball leg carried (the T3 note in the module
docstring).  Everything else — frame, weighting, numerals — is §2's, verbatim. -/

set_option maxHeartbeats 1000000 in
-- one predicate-blind application of the landed socketed row at `Tann = 2T`, `t₁ = v₀`
/-- **THE SOCKETED ROW FAMILY** (`a2Rows_of_cap`).  On the `¬ CapFreeFloor` branch, the
`hrows` binder of `ThmA2.thm_a2'_of_rows`: `CapFreeArm.seam_row_number_nocap` at the ROUTING
WITNESS `t₁ := v₀` (`ThmA2.a2_row_cap_of_not_capFreeFloor` — hence the `800 < loglog X`
threshold, ⟦AMENDMENT E⟧'s T-NEW-1 break-even), with the collision socket supplied by
`CapFreeArm.pocketSocket_of_row` (whose constant `Ccol` is exposed, and whose gate
`collisionGate X 25 Ccol` is carried in-statement).

**CONDITIONAL, in statement, on exactly two named things** (law #253, nothing absorbed):

* `hStation` — the ball-leg supply at grade `Sb`, UNIFORMLY over centres in the box
  `|t₁| ≤ X`.  `SPartStation.seam_ball_leg_station_M_gen` is what supplies it at each fixed
  centre; `a2_station_supply_pointwise` below prints that price with the T3-gap cap
  (`hMcap`), the `M₀` floor and the datum equation as visible binders.  It is carried, not
  derived, because the centre `v₀` is produced inside this proof while the station's
  threshold `X₀` sits under `∀ t₁` in its statement (module docstring, item 2).
* `hCcc` — `C + M·Sb²/2 ≤ Ccc`: the row's `8S²` ball summand paid out of `a2Mrow`'s FREE
  constant slot, since `a2Mrow` has no `M`-shaped summand of its own.  The analytic
  obligation then surfaces at `thm_a2'_of_rows`' `hgRows` gate, read at this `Ccc`.

Everything else is the cap-free branch's list verbatim: §2's single `CapFreeFloor g X`
becomes the five binders `800 < loglog X`, `¬ CapFreeFloor g X`, `collisionGate X 25 Ccol`,
`hStation`, `hCcc` (and the two extra reals `Sb`, `Ccc`); nothing else moves. -/
theorem a2Rows_of_cap :
    ∃ Cq cq T₀ X₀ Cs C Ccol : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad kmin Ymax ε EP2 Sb Ccc : ℝ),
        1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
        A2Frame g cf a N Xd P Q (Adoor M) (3072 * M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        800 < Real.log (Real.log X) → ¬ CapFreeFloor g X →
        collisionGate X 25 Ccol →
        (∀ t₁ : ℝ, |t₁| ≤ X → ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ X → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ Sb * (m : ℝ) / (1 + |t - t₁|)) →
        C + (M : ℝ) * Sb ^ 2 / 2 ≤ Ccc →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
          p ≤ calQK (Adoor M) (3072 * M) M j → ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
          p ≤ calQK (Adoor M) (3072 * M) M j → c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
                    (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow Cs Ccc M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_nocap
  obtain ⟨Ccol, hpock⟩ := pocketSocket_of_row
  refine ⟨Cq, cq, T₀, X₀, Cs, C, Ccol, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin Ymax ε
    EP2 Sb Ccc hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hCb0
    hPlow hQ0 hQhigh hPQ83 hLL hnfl hgate hStation hCcc hR0 hRrad hRlow hCbound hX₀k hMfl0
    hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate hε0 habs hEP2 hXN hN2 hsupp
    hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (3072 * M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at M Xd hM hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROUTING WITNESS⟧ the bare-datum cap at `v₀`, and the socket it closes
  obtain ⟨v₀, hv₀box, hv₀cap⟩ := a2_row_cap_of_not_capFreeFloor hLL hnfl
  have hsock : PocketSocket g P Q X theta293 v₀ :=
    hpock g hg P Q X theta293 v₀ hXe hLXe theta293_pos
      (le_of_lt theta293_lt_one_div_32) hPlow hQhigh hPQ83 hv₀box hv₀cap hgate
  -- ⟦THE BALL LEG⟧ the carried supply, read at the produced centre
  have hSup : ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ 2 * T → |t - v₀| ≤ seamRad X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ Sb * (m : ℝ) / (1 + |t - v₀|) :=
    fun t h1 h2 h3 m hm => hStation v₀ hv₀box t h1 (le_trans h2 h2b) h3 m hm
  -- ⟦THE ROW, at `Tann = 2T`, `t₁ = v₀`⟧
  have hinst := hrow g c a b cf hg hc1 hb1 hcf1 N Xd P Q (Adoor M) (3072 * M) M 2 m₀ Ms Mt kk
    (H1door M) X (2 * T) v₀ δ' V VJ L (1 / 12) Cb Rrad kmin Ymax ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2)) Sb
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow (F.blocks _ h2a h2b)
    (F.box_at h2b) hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl (F.err _ h2a h2b) hXN hN2 hsupp
    hSup hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, hw1, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hM1' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hRS0 : (0 : ℝ) ≤ a2RowsSum M Xd := a2RowsSum_nonneg hM hXd1
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge M]
  have hlvl0 : (0 : ℝ) ≤ a2Level1 M := by
    unfold a2Level1
    exact div_nonneg
      (Real.rpow_nonneg (le_trans (by norm_num) (one_le_log_calQK_door_one hM)) _)
      (Real.rpow_pos_of_pos hP0 _).le
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow
  refine a2_row_weigh_cap ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_ball_weigh hw1 hRS0 hC.le hM1' hCcc hg3
  · exact a2_term4_weigh hZ0 hg32


/-! ## §4 — THE GLUE

`by_cases` on `CapFreeArm.CapFreeFloor g X`, the STRICT `(1/32)loglog X + 25` datum floor on
the box `|v| ≤ X` that `CapFreeArm.box_gate_le_X` (S10) makes the right box — so the
dichotomy is exhaustive and the two suppliers of §2/§3 cover it.  Both branch constant sets
are exposed (the two row capstones are separate existentials at the statement level, so no
consumer may identify them); the binders they share are stated ONCE, the four that mention a
branch constant twice. -/

set_option maxHeartbeats 1000000 in
-- the composition: two branch suppliers into `ThmA2.thm_a2'_of_rows`, one `by_cases`
/-- **`thm_A2′`** (`thm_a2'`).  The frozen five-summand interface of
`ThmA2.thm_a2'_of_rows`, with its `hrows` binder DISCHARGED on both branches of the
`CapFreeFloor` dichotomy:

  `(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
  `  ≤ 8448·C₁'²·exp(−M₀/e) + 1787702400·(log Q₁)^{1/3}/P₁^{1/12}`
  `   + 188133·(log X)^{−1/500} + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)²`
  `   + 6315000/h`.

The side conditions are the union of the two branches' lists (§2's = §3's minus three
binders) with `thm_a2'_of_rows`' own, all in-statement.  The two branch constant sets ride
side by side: `(Cq₁,cq₁,T₀₁,X₀₁,Cs₁,C₁)` from `a2Rows_of_capfree`,
`(Cq₂,cq₂,T₀₂,X₀₂,Cs₂,C₂)` and the collision constant `Ccol` from `a2Rows_of_cap`; FIVE
binders are stated at both (`A2Frame`, `X₀ ≤ kmin`, the `Cq`-gate, and the two grading
gates `hgP1`/`hgRows`) — the two capstones are separate existentials, so their constants
cannot be identified by any consumer.

⚠ CONDITIONAL exactly where §3 is: `hStation` (the ball-leg supply over the box, whose
per-centre price `a2_station_supply_pointwise` prints, T3 cap included) and `hCcc` (the
`8S²` slot).  On the `CapFreeFloor` branch neither is used — that branch is unconditional. -/
theorem thm_a2' :
    ∃ Cq₁ cq₁ T₀₁ X₀₁ Cs₁ C₁ Cq₂ cq₂ T₀₂ X₀₂ Cs₂ C₂ Ccol : ℝ,
      0 < Cq₁ ∧ 0 < cq₁ ∧ 3 ≤ T₀₁ ∧ 0 < X₀₁ ∧ 0 < Cs₁ ∧ 0 < C₁ ∧
      0 < Cq₂ ∧ 0 < cq₂ ∧ 3 ≤ T₀₂ ∧ 0 < X₀₂ ∧ 0 < Cs₂ ∧ 0 < C₂ ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad kmin Ymax ε EP2 Sb Ccc C₁' M₀ : ℝ),
        1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
        A2Frame g cf a N Xd P Q (Adoor M) (3072 * M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq₁ T₀₁ →
        A2Frame g cf a N Xd P Q (Adoor M) (3072 * M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq₂ T₀₂ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        800 < Real.log (Real.log X) →
        collisionGate X 25 Ccol →
        (∀ t₁ : ℝ, |t₁| ≤ X → ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ X → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ Sb * (m : ℝ) / (1 + |t - t₁|)) →
        C₂ + (M : ℝ) * Sb ^ 2 / 2 ≤ Ccc →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        ShortIntervalDatum Cb →
        X₀₁ ≤ kmin → X₀₂ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq₁ * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        1728 * Cq₂ * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
          p ≤ calQK (Adoor M) (3072 * M) M j → ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
          p ≤ calQK (Adoor M) (3072 * M) M j → c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
                    (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        3 ≤ X → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
        TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
        (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X C₁' M₀ →
        374784 * Cs₁ * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
          ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        374784 * Cs₂ * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
          ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        5760 * (a2RowsSum M Xd + C₁ * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        5760 * (a2RowsSum M Xd + Ccc * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        (0 ≤ ε ∧ ε ≤ theta293 - 1 / 500) →
        4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
        1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
          ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
            + 1787702400 * a2Level1 M
            + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
            + 304128 * ballSupC ^ 2
                * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
            + 6315000 / h := by
  obtain ⟨Cq₁, cq₁, T₀₁, X₀₁, Cs₁, C₁, hCq₁, hcq₁, hT₀₁, hX₀₁, hCs₁, hC₁, hcapfree⟩ :=
    a2Rows_of_capfree
  obtain ⟨Cq₂, cq₂, T₀₂, X₀₂, Cs₂, C₂, Ccol, hCq₂, hcq₂, hT₀₂, hX₀₂, hCs₂, hC₂, hcap⟩ :=
    a2Rows_of_cap
  refine ⟨Cq₁, cq₁, T₀₁, X₀₁, Cs₁, C₁, Cq₂, cq₂, T₀₂, X₀₂, Cs₂, C₂, Ccol,
    hCq₁, hcq₁, hT₀₁, hX₀₁, hCs₁, hC₁, hCq₂, hcq₂, hT₀₂, hX₀₂, hCs₂, hC₂, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin Ymax ε
    EP2 Sb Ccc C₁' M₀ hM hXdQ F₁ F₂ hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ
    hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hLL hgate hStation hCcc hR0 hRrad hRlow hCbound hX₀k₁
    hX₀k₂ hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate₁ hCqgate₂ hε0 habs
    hEP2 hXN hN2 hsupp hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp hX3 hhX hTann hceil
    hT0band hgP1₁ hgP1₂ hgRows₁ hgRows₂ hεwin hL4096
  -- ⟦R3c⟧ the row's `EP₂` budget is now the ε-GRADED one; the frozen interface still
  -- carries the sharp `(log X)^{−θ₂₉₃}` gate, which is stronger (`ε ≥ 0`, `log X ≥ 1`)
  have hL1 : (1 : ℝ) ≤ Real.log X := le_trans (Real.one_le_exp (by norm_num)) hlX2
  have hEP2ε : 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) :=
    le_trans hEP2 (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  by_cases hfl : CapFreeFloor g X
  · exact thm_a2'_of_rows hM hXe hX3 hh4 hhX ha1 hsupp hN2 hTann hceil
      (hcapfree g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin
        Ymax ε EP2 hM hXdQ F₁ hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV
        hCb0 hPlow hQ0 hQhigh hPQ83 hfl hR0 hRrad hRlow hCbound hX₀k₁ hMfl0 hk2 hkX hkk
        hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate₁ hε0 habs hEP2ε hXN hN2 hsupp hNXd hcoef
        hwin hQXd hXdbig hN4 hdom ha1 hasupp)
      hT0band hgP1₁ hgRows₁ hεwin hL4096
  · exact thm_a2'_of_rows hM hXe hX3 hh4 hhX ha1 hsupp hN2 hTann hceil
      (hcap g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin
        Ymax ε EP2 Sb Ccc hM hXdQ F₂ hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1
        hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hLL hfl hgate hStation hCcc hR0 hRrad hRlow
        hCbound hX₀k₂ hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate₂ hε0
        habs hEP2ε hXN hN2 hsupp hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp)
      hT0band hgP1₂ hgRows₂ hεwin hL4096


/-! ## §5 — the price of `hStation`, and the frame from the window's endpoints

Two service stones.  `a2_station_supply_pointwise` prints what `hStation` costs AT ONE
CENTRE — `SPartStation.seam_ball_leg_station_M_gen` read at `T := X`, with the T3-gap cap
`hMcap` among its visible binders.  `a2Frame_satisfiable_partial` discharges the six
monotone `∀Tann` members of `ThmA2.A2Frame` from the window's ENDPOINT data (which is
`thm_a2'_of_rows`' own `hTann`/`hceil` pair), leaving the three genuinely per-instance
members (`thin`, `blocks`, `err`) and the two top-instance ones (`box`, `ksGate`) as
binders. -/

/-- **THE PRICE OF `hStation`, AT ONE CENTRE** (`a2_station_supply_pointwise`).
`SPartStation.seam_ball_leg_station_M_gen` at `T := X` — the shape §3's `hStation` binder
asks for, one centre `t₁` at a time, with its hypotheses printed:

* the dissection gates `1 ≤ D`, `√X ≤ X_d ≤ X`, `D(X_d+1) ≤ X−1`;
* the recentring gate `|t₁| + T*(2X, log 2X) ≤ Rad` and the `M₀` FLOOR on `|v| ≤ Rad`
  (`MWindowBridge.M_window_bridge_seam` gives that floor on `|v| ≤ X`; the extra reach is
  the D10 defect at the row's own centre);
* `hDatum`, `a` = the seam datum above `X`;
* **`hMcap`, THE T3 GAP** — the A-10 cap `𝔻²(seamCoeff F 1 t₀, p^{it₁}; x) ≤ (1/16)loglog X`
  on `x ∈ [X,2X]`, which the routing witness of §3 does NOT supply (it caps the BARE datum
  at `X`, not the `t₀`-shifted one on the window).

The threshold `X₀` sits under `∀ t₀ t₁` here exactly as in the landed statement — which is
why §3 carries the supply rather than deriving it. -/
theorem a2_station_supply_pointwise {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) (hFb : ∀ n, ‖F n‖ ≤ 1) (t₀ t₁ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N D : ℕ) (Cb Xd M₀ Rad : ℝ) (a : ℕ → ℂ),
        X₀ ≤ Real.sqrt X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X →
        0 ≤ Cb → ShortIntervalDatum Cb →
        1 ≤ D → Real.sqrt X ≤ Xd → Xd ≤ X → (D : ℝ) * (Xd + 1) ≤ X - 1 →
        |t₁| + Tstar (2 * X) (Real.log (2 * X)) ≤ Rad →
        (∀ v : ℝ, |v| ≤ Rad →
          M₀ ≤ pretDistSq (seamCoeff (ellLin F) (fun _ => 1) t₀) (costwist v) X) →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff F (fun _ => 1) t₀ n) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
          pretDistSq (seamCoeff F (fun _ => 1) t₀) (costwist t₁) x
            ≤ 1 / 16 * Real.log (Real.log X)) →
        ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ X → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N →
            ‖spolyA a t m‖
              ≤ ballSupS X (cSq * (gradeAbsConstC (1 / (2 * Real.exp 1)) Cb
                      * Real.exp (-(1 / (2 * Real.exp 1)) * (M₀ - dilGap X Xd))
                    + farCStar * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1)))
                    + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
                  + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) * m / (1 + |t - t₁|) := by
  obtain ⟨X₀, hX₀0, hst⟩ := seam_ball_leg_station_M_gen hFm hFb t₀ t₁
  exact ⟨X₀, hX₀0, fun X N D Cb Xd M₀ Rad a => hst X N D Cb Xd M₀ Rad X a⟩

/-- **THE FRAME FROM THE WINDOW'S ENDPOINTS** (`a2Frame_satisfiable_partial`).  Six of
`ThmA2.A2Frame`'s eleven members are monotone across `[2X/h, X]` and follow from endpoint
data alone:

* `tannGate`, `one_lt`, `T0_le` from the BOTTOM endpoint (`TannGate` is `exp(30√log X) ≤ ·`,
  increasing in `Tann`);
* `loglog5` and `one_le_log` from the bottom endpoint too, THROUGH the positivity that
  `TannGate` supplies — `5 ≤ loglog u` alone does NOT force `u > 1` (⟦AMENDMENT F⟧'s
  loglog-below-1 trap), so the chain runs `1 < 2X/h ⟹ 0 < log(2X/h) ⟹ e⁵ ≤ log(2X/h)`;
* `log_le_L` from the TOP endpoint (`log Tann ≤ log X ≤ L`).

`thin`, `blocks` and `err` are genuinely per-instance and stay binders; `box` and `ksGate`
are single top-instance statements and pass through verbatim.  The two endpoint hypotheses
`hTann`/`hceil` are `thm_a2'_of_rows`' own binders, so a consumer already holds them. -/
theorem a2Frame_satisfiable_partial {g cf a : ℕ → ℂ} {N Xd P Q A G M Jb : ℕ}
    {Ms Mt kk : ℕ → ℕ} {H1 X h δ' VJ L η Cb Rrad EP2 cq T₀ : ℝ}
    (hLX0 : 0 < Real.log X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hT₀le : T₀ ≤ 2 * (X / h)) (hLXL : Real.log X ≤ L)
    (hthin : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
      ∀ j ∈ ramI (H83 X theta293) P Q,
        thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb) * X ^ (1 - 2 * η)
          ≤ ((Ms j : ℕ) : ℝ))
    (hblocks : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
      ∀ j ∈ ramI (H83 X theta293) P Q,
        TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk Tann L (1 / Real.exp 1) Cb X
          theta293 Rrad j)
    (hbox : ∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ X)
    (hksGate : 32 * (Real.log X) ^ (2 + 2 * theta293)
      * (20512 * δ' ^ 2 * (1 + Real.log (2 * X))) ≤ (Real.log X) ^ (-theta293))
    (herr : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
      (∫ t in (-Tann)..Tann, ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2)
        ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2)) :
    A2Frame g cf a N Xd P Q A G M Jb Ms Mt kk H1 X h δ' VJ L η Cb Rrad EP2 cq T₀ := by
  have hgate : Real.exp (30 * (Real.log X) ^ ((1 : ℝ) / 2)) ≤ 2 * (X / h) := hTann
  have hexp1 : (1 : ℝ) < Real.exp (30 * (Real.log X) ^ ((1 : ℝ) / 2)) := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_lt_exp.mpr (by positivity)
  have hbot1 : (1 : ℝ) < 2 * (X / h) := lt_of_lt_of_le hexp1 hgate
  have hbotlog : (0 : ℝ) < Real.log (2 * (X / h)) := Real.log_pos hbot1
  have hbote5 : Real.exp 5 ≤ Real.log (2 * (X / h)) :=
    (Real.le_log_iff_exp_le hbotlog).mp hceil
  have hkey : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
      Real.exp 5 ≤ Real.log Tann ∧ 0 < Tann := by
    intro Tann h1 h2
    have hT1 : (1 : ℝ) < Tann := lt_of_lt_of_le hbot1 h1
    refine ⟨le_trans hbote5 (Real.log_le_log (by linarith) h1), by linarith⟩
  refine ⟨fun Tann h1 _ => le_trans hgate h1, fun Tann h1 _ => lt_of_lt_of_le hbot1 h1,
    fun Tann h1 _ => le_trans hT₀le h1, fun Tann h1 h2 => ?_, fun Tann h1 h2 => ?_,
    fun Tann h1 h2 => ?_, hthin, hblocks, hbox, hksGate, herr⟩
  · have hl := (hkey Tann h1 h2).1
    have h5 : Real.log (Real.exp 5) ≤ Real.log (Real.log Tann) :=
      Real.log_le_log (Real.exp_pos 5) hl
    rwa [Real.log_exp] at h5
  · have hl := (hkey Tann h1 h2).1
    have he5 : (1 : ℝ) ≤ Real.exp 5 := Real.one_le_exp (by norm_num)
    linarith
  · exact le_trans (Real.log_le_log (hkey Tann h1 h2).2 h2) hLXL


/-! ## §6 — THE `3X` MINT: the cap-free branch, at the SATISFIABLE frame

`CapFreeArm3`'s additive mint read into the same `hrows` slot.  `ThmA2.A2Frame.box` is
unsatisfiable at `|t| = X` (flags, `TLGATES-SCOPE` R2); `CapFreeArm3.A2Frame3.box` is the
sibling convention `≤ 3X` and IS satisfiable.  The two stones here are §2's and §5's twins:
the row family at the mint, and the frame's endpoint discharge — now including the `box`
field itself, from `T*₂(M_j, log M_j) ≤ 2X`.

⚠ `a2Rows_of_capfree3`'s CONCLUSION is `a2Rows_of_capfree`'s byte for byte, so it plugs
`ThmA2.thm_a2'_of_rows`' `hrows` slot with no change on the consumer side. -/

set_option maxHeartbeats 1000000 in
-- one predicate-blind application of the `3X`-minted cap-free row at `Tann = 2T`
/-- **THE CAP-FREE ROW FAMILY, AT THE `3X` MINT** (`a2Rows_of_capfree3`).
`a2Rows_of_capfree` with its `X`-box inputs replaced by the mint's: the frame is
`CapFreeArm3.A2Frame3` (whose `box` field is the SATISFIABLE `≤ 3X` one) and the row is
`CapFreeArm3.seam_row_number_capfree3`.

⟦THE SOCKET CUT⟧ the third `X`-box input — the datum `CapFreeArm3.CapFreeFloor3` — is GONE,
and with it `g`, `hg`, `ShortIntervalDatum` and the whole `kmin`/`Ymax` ladder.  In their
place the row carries `CofactorSocket … X Rrad 0 R̄ b` at the window's TOP (antitone in the
height, `CofactorSocket.mono`, exactly as `A2Frame3.box_at` is) plus the single grade
`R̄ ≤ gradeCR2 C_b·(log X)^{−ρ₂₉₃}`.  The co-factor datum is the SAME free `b` the
factorization binder already carried.

The weighting arithmetic, the four numerals and the CONCLUSION are §2's verbatim. -/
theorem a2Rows_of_capfree3 :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (Adoor M) (3072 * M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the window's TOP, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
          p ≤ calQK (Adoor M) (3072 * M) M j → ¬ p ∣ m →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
                    (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_capfree3
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (3072 * M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at M Xd hM hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (Adoor M) (3072 * M) M 2 m₀ Ms
    Mt kk
    (H1door M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum_nonneg hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge M]
  have hlvl0 : (0 : ℝ) ≤ a2Level1 M := by
    unfold a2Level1
    exact div_nonneg
      (Real.rpow_nonneg (le_trans (by norm_num) (one_le_log_calQK_door_one hM)) _)
      (Real.rpow_pos_of_pos hP0 _).le
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow
  refine a2_row_weigh ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_weigh_mr hRS0 hg3
  · exact a2_term4_weigh hZ0 hg32

set_option maxHeartbeats 1000000 in
-- one predicate-blind application of the strict/fused `3X`-minted row at `Tann = 2T`
/-- **THE CAP-FREE ROW FAMILY AT THE `3X` MINT — STRICT/FUSED** (`a2Rows_of_capfree3_end`).
`a2Rows_of_capfree3` at ⟦THE ENDPOINT WALL⟧'s repair (flags ⟦ENDPOINT-ROW-SCOPE⟧,
⟦ENDPOINT-REF⟧): the inlined pair-law binder carries the STRICT antecedent `X_d < p·m`, and
the row is `CapFreeArm3.seam_row_number_capfree3_end`.

⟦AMENDMENT 1⟧ is what makes this ADDITIVE.  The endpoint mass is absorbed upstream, inside
`M4RowMR.four_rows_le_end`'s unspent `1.5×` on the `B2` slot, so
`seam_row_number_capfree3_end`'s right-hand side is the landed one BYTE FOR BYTE.  Hence
`a2Mrow`, `a2RowsSum`, `a2_term3_weigh_mr`, `thm_a2'_of_rows` and the whole frozen five-
summand interface do not move: this is a new theorem beside `a2Rows_of_capfree3`, not a
restatement of it.  The weighting arithmetic, the four numerals and the CONCLUSION are
`a2Rows_of_capfree3`'s verbatim. -/
theorem a2Rows_of_capfree3_end :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (Adoor M) (3072 * M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the window's TOP, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
          p ≤ calQK (Adoor M) (3072 * M) M j → ¬ p ∣ m →
          (Xd : ℝ) < (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
                    (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_capfree3_end
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (3072 * M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at M Xd hM hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (Adoor M) (3072 * M) M 2 m₀ Ms
    Mt kk
    (H1door M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum_nonneg hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge M]
  have hlvl0 : (0 : ℝ) ≤ a2Level1 M := by
    unfold a2Level1
    exact div_nonneg
      (Real.rpow_nonneg (le_trans (by norm_num) (one_le_log_calQK_door_one hM)) _)
      (Real.rpow_pos_of_pos hP0 _).le
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow
  refine a2_row_weigh ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_weigh_mr hRS0 hg3
  · exact a2_term4_weigh hZ0 hg32

/-- **THE `3X` FRAME FROM THE WINDOW'S ENDPOINTS** (`a2Frame3_satisfiable_partial`).
`a2Frame_satisfiable_partial`'s six monotone discharges, PLUS — and this is what the R2
repair buys — the `box` field itself, from the single arithmetic datum

  `T*₂(M_j, log M_j) ≤ 2X`  for `j ∈ ramI`,

since `|t| ≤ X` then gives `|t| + T*₂ ≤ 3X`.  The corresponding `A2Frame` field is
UNSATISFIABLE (at `|t| = X` it reads `X + T*₂ ≤ X` with `T*₂ > 0`), so no analogue of this
discharge exists on the landed frame: seven of eleven members land here against six there.

`thin`, `blocks` and `err` stay genuinely per-instance binders; `ksGate` passes through. -/
theorem a2Frame3_satisfiable_partial {b cf a : ℕ → ℂ} {N Xd P Q A G M Jb : ℕ}
    {Ms Mt kk : ℕ → ℕ} {H1 X h δ' VJ L η Cb Rrad EP2 cq T₀ : ℝ}
    (hLX0 : 0 < Real.log X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hT₀le : T₀ ≤ 2 * (X / h)) (hLXL : Real.log X ≤ L)
    (hthin : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
      ∀ j ∈ ramI (H83 X theta293) P Q,
        thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb) * X ^ (1 - 2 * η)
          ≤ ((Ms j : ℕ) : ℝ))
    (hblocks : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
      ∀ j ∈ ramI (H83 X theta293) P Q,
        TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk Tann L (1 / Real.exp 1) Cb X
          theta293 Rrad j)
    (hMtbox : ∀ j ∈ ramI (H83 X theta293) P Q,
      Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 2 * X)
    (hksGate : 32 * (Real.log X) ^ (2 + 2 * theta293)
      * (20512 * δ' ^ 2 * (1 + Real.log (2 * X))) ≤ (Real.log X) ^ (-theta293))
    (herr : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
      (∫ t in (-Tann)..Tann, ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2)
        ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2)) :
    A2Frame3 b cf a N Xd P Q A G M Jb Ms Mt kk H1 X h δ' VJ L η Cb Rrad EP2 cq T₀ := by
  have hgate : Real.exp (30 * (Real.log X) ^ ((1 : ℝ) / 2)) ≤ 2 * (X / h) := hTann
  have hexp1 : (1 : ℝ) < Real.exp (30 * (Real.log X) ^ ((1 : ℝ) / 2)) := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_lt_exp.mpr (by positivity)
  have hbot1 : (1 : ℝ) < 2 * (X / h) := lt_of_lt_of_le hexp1 hgate
  have hbotlog : (0 : ℝ) < Real.log (2 * (X / h)) := Real.log_pos hbot1
  have hbote5 : Real.exp 5 ≤ Real.log (2 * (X / h)) :=
    (Real.le_log_iff_exp_le hbotlog).mp hceil
  have hkey : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
      Real.exp 5 ≤ Real.log Tann ∧ 0 < Tann := by
    intro Tann h1 h2
    have hT1 : (1 : ℝ) < Tann := lt_of_lt_of_le hbot1 h1
    refine ⟨le_trans hbote5 (Real.log_le_log (by linarith) h1), by linarith⟩
  -- ⟦THE BOX, NOW DISCHARGEABLE⟧ `|t| ≤ X` and `T*₂ ≤ 2X` give `|t| + T*₂ ≤ 3X`
  have hbox : ∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X := by
    intro j hj t ht
    have := hMtbox j hj
    linarith
  refine ⟨fun Tann h1 _ => le_trans hgate h1, fun Tann h1 _ => lt_of_lt_of_le hbot1 h1,
    fun Tann h1 _ => le_trans hT₀le h1, fun Tann h1 h2 => ?_, fun Tann h1 h2 => ?_,
    fun Tann h1 h2 => ?_, hthin, hblocks, hbox, hksGate, herr⟩
  · have hl := (hkey Tann h1 h2).1
    have h5 : Real.log (Real.exp 5) ≤ Real.log (Real.log Tann) :=
      Real.log_le_log (Real.exp_pos 5) hl
    rwa [Real.log_exp] at h5
  · have hl := (hkey Tann h1 h2).1
    have he5 : (1 : ℝ) ≤ Real.exp 5 := Real.one_le_exp (by norm_num)
    linarith
  · exact le_trans (Real.log_le_log (hkey Tann h1 h2).2 h2) hLXL


/-! ## §GK — the G-lever twin

The two row suppliers, the glue and the two `3X`-mint suppliers, re-read at
`G := s13GK K M` (`GLever`).  Every statement is the landed one with `3072 * M` replaced by
`s13GK K M`; the LEVEL-1 objects keep their landed names (`H1door M`, `a2Level1 M`, and the
whole §8.1 decay certificate, transported by `DoorFrameH1.level1_term_door_decays_gk`), and
the frame is `ThmA2.calFrameK_doorH1_at_gk` — which is where the lever's only real cost, the
`+K` in `A_gate_logK`, is paid, hence the side condition `K ≤ 1.7·10⁸` on every twin here.

The proofs are the landed ones verbatim: `CapFreeArm.seam_row_number_capfree` /
`seam_row_number_nocap` are PARAMETRIC in `(A, G)`, so the lever is passed straight through
and no estimate is re-run.  `thm_a2'_gk`'s conclusion is BYTE-IDENTICAL to `thm_a2'`'s. -/

lemma a2RowsSum_nonneg_gk (K : ℕ) {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) :
    0 ≤ a2RowsSum_gk K M Xd := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hH1 : (2 : ℝ) ≤ H1door M := H1door_two hM
  unfold a2RowsSum_gk
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have hcalH : (0 : ℝ) < calH (H1door M) j := by
    rw [calH]; nlinarith
  have hP1 : (1 : ℝ) ≤ ((calP (Adoor M) (s13GK K M) j : ℕ) : ℝ) := by
    have h : 1 ≤ calP (Adoor M) (s13GK K M) j := by
      simp only [calP]; exact Nat.one_le_two_pow
    exact_mod_cast h
  have hlogb : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have h1 : (0 : ℝ) ≤ (Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1door M) j + 1)
      * (Real.exp 1 / (Xd : ℝ) ^ 2)) := by
    have hq : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH (H1door M) j :=
      div_nonneg (by positivity) hcalH.le
    have hr : (0 : ℝ) ≤ Real.exp 1 / (Xd : ℝ) ^ 2 := by positivity
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ)
      / calH (H1door M) j + 1) hr
    nlinarith
  have h2 : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ))
      / ((calP (Adoor M) (s13GK K M) j : ℕ) : ℝ) :=
    div_nonneg (by linarith) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 / (Xd : ℝ) := by positivity
  linarith

set_option maxHeartbeats 1000000 in
theorem a2Rows_of_capfree_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad kmin Ymax ε EP2 : ℝ),
        1 ≤ M → calQK (Adoor M) (s13GK K M) M 2 ≤ Xd →
        A2Frame g cf a N Xd P Q (Adoor M) (s13GK K M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        CapFreeFloor g X →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (s13GK K M) j ≤ p →
          p ≤ calQK (Adoor M) (s13GK K M) M j → ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (Adoor M) (s13GK K M) j ≤ p →
          p ≤ calQK (Adoor M) (s13GK K M) M j → c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (s13GK K M) j)
                    (calQK (Adoor M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (s13GK K M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow_gk K Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_capfree
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin Ymax ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hCb0 hPlow
    hQ0 hQhigh hPQ83 hfloor hR0 hRrad hRlow hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW
    hYpin hWY hXY hthr hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef hwin hQXd hXdbig hN4
    hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (s13GK K M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_gk K M Xd hM hK hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`⟧
  have hinst := hrow g c a b cf hg hc1 hb1 hcf1 N Xd P Q (Adoor M) (s13GK K M) M 2 m₀ Ms Mt kk
    (H1door M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad kmin Ymax ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hfloor hR0 hRrad hRlow (F.blocks _ h2a h2b)
    (F.box_at h2b) hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl (F.err _ h2a h2b) hXN hN2 hsupp
    hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum_gk K M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum_nonneg_gk K hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_gk K M]
  have hlvl0 : (0 : ℝ) ≤ a2Level1 M := a2Level1_nonneg hM
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow_gk
  refine a2_row_weigh ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays_gk K hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_weigh hRS0 hg3
  · exact a2_term4_weigh hZ0 hg32

set_option maxHeartbeats 1000000 in
theorem a2Rows_of_cap_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Cq cq T₀ X₀ Cs C Ccol : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad kmin Ymax ε EP2 Sb Ccc : ℝ),
        1 ≤ M → calQK (Adoor M) (s13GK K M) M 2 ≤ Xd →
        A2Frame g cf a N Xd P Q (Adoor M) (s13GK K M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        800 < Real.log (Real.log X) → ¬ CapFreeFloor g X →
        collisionGate X 25 Ccol →
        (∀ t₁ : ℝ, |t₁| ≤ X → ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ X → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ Sb * (m : ℝ) / (1 + |t - t₁|)) →
        C + (M : ℝ) * Sb ^ 2 / 2 ≤ Ccc →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (s13GK K M) j ≤ p →
          p ≤ calQK (Adoor M) (s13GK K M) M j → ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (Adoor M) (s13GK K M) j ≤ p →
          p ≤ calQK (Adoor M) (s13GK K M) M j → c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (s13GK K M) j)
                    (calQK (Adoor M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (s13GK K M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow_gk K Cs Ccc M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_nocap
  obtain ⟨Ccol, hpock⟩ := pocketSocket_of_row
  refine ⟨Cq, cq, T₀, X₀, Cs, C, Ccol, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin Ymax ε
    EP2 Sb Ccc hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hCb0
    hPlow hQ0 hQhigh hPQ83 hLL hnfl hgate hStation hCcc hR0 hRrad hRlow hCbound hX₀k hMfl0
    hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate hε0 habs hEP2 hXN hN2 hsupp
    hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (s13GK K M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_gk K M Xd hM hK hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROUTING WITNESS⟧ the bare-datum cap at `v₀`, and the socket it closes
  obtain ⟨v₀, hv₀box, hv₀cap⟩ := a2_row_cap_of_not_capFreeFloor hLL hnfl
  have hsock : PocketSocket g P Q X theta293 v₀ :=
    hpock g hg P Q X theta293 v₀ hXe hLXe theta293_pos
      (le_of_lt theta293_lt_one_div_32) hPlow hQhigh hPQ83 hv₀box hv₀cap hgate
  -- ⟦THE BALL LEG⟧ the carried supply, read at the produced centre
  have hSup : ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ 2 * T → |t - v₀| ≤ seamRad X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ Sb * (m : ℝ) / (1 + |t - v₀|) :=
    fun t h1 h2 h3 m hm => hStation v₀ hv₀box t h1 (le_trans h2 h2b) h3 m hm
  -- ⟦THE ROW, at `Tann = 2T`, `t₁ = v₀`⟧
  have hinst := hrow g c a b cf hg hc1 hb1 hcf1 N Xd P Q (Adoor M) (s13GK K M) M 2 m₀ Ms Mt kk
    (H1door M) X (2 * T) v₀ δ' V VJ L (1 / 12) Cb Rrad kmin Ymax ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2)) Sb
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow (F.blocks _ h2a h2b)
    (F.box_at h2b) hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl (F.err _ h2a h2b) hXN hN2 hsupp
    hSup hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, hw1, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hM1' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hRS0 : (0 : ℝ) ≤ a2RowsSum_gk K M Xd := a2RowsSum_nonneg_gk K hM hXd1
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_gk K M]
  have hlvl0 : (0 : ℝ) ≤ a2Level1 M := a2Level1_nonneg hM
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow_gk
  refine a2_row_weigh_cap ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays_gk K hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_ball_weigh hw1 hRS0 hC.le hM1' hCcc hg3
  · exact a2_term4_weigh hZ0 hg32

set_option maxHeartbeats 1000000 in
theorem thm_a2'_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Cq₁ cq₁ T₀₁ X₀₁ Cs₁ C₁ Cq₂ cq₂ T₀₂ X₀₂ Cs₂ C₂ Ccol : ℝ,
      0 < Cq₁ ∧ 0 < cq₁ ∧ 3 ≤ T₀₁ ∧ 0 < X₀₁ ∧ 0 < Cs₁ ∧ 0 < C₁ ∧
      0 < Cq₂ ∧ 0 < cq₂ ∧ 3 ≤ T₀₂ ∧ 0 < X₀₂ ∧ 0 < Cs₂ ∧ 0 < C₂ ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad kmin Ymax ε EP2 Sb Ccc C₁' M₀ : ℝ),
        1 ≤ M → calQK (Adoor M) (s13GK K M) M 2 ≤ Xd →
        A2Frame g cf a N Xd P Q (Adoor M) (s13GK K M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq₁ T₀₁ →
        A2Frame g cf a N Xd P Q (Adoor M) (s13GK K M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq₂ T₀₂ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        800 < Real.log (Real.log X) →
        collisionGate X 25 Ccol →
        (∀ t₁ : ℝ, |t₁| ≤ X → ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ X → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ Sb * (m : ℝ) / (1 + |t - t₁|)) →
        C₂ + (M : ℝ) * Sb ^ 2 / 2 ≤ Ccc →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        ShortIntervalDatum Cb →
        X₀₁ ≤ kmin → X₀₂ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq₁ * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        1728 * Cq₂ * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (s13GK K M) j ≤ p →
          p ≤ calQK (Adoor M) (s13GK K M) M j → ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (Adoor M) (s13GK K M) j ≤ p →
          p ≤ calQK (Adoor M) (s13GK K M) M j → c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (s13GK K M) j)
                    (calQK (Adoor M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (s13GK K M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        3 ≤ X → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
        TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
        (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X C₁' M₀ →
        374784 * Cs₁ * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
          ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        374784 * Cs₂ * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
          ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        5760 * (a2RowsSum_gk K M Xd + C₁ * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        5760 * (a2RowsSum_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        (0 ≤ ε ∧ ε ≤ theta293 - 1 / 500) →
        4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
        1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
          ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
            + 1787702400 * a2Level1 M
            + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
            + 304128 * ballSupC ^ 2
                * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
            + 6315000 / h := by
  obtain ⟨Cq₁, cq₁, T₀₁, X₀₁, Cs₁, C₁, hCq₁, hcq₁, hT₀₁, hX₀₁, hCs₁, hC₁, hcapfree⟩ :=
    a2Rows_of_capfree_gk K hK
  obtain ⟨Cq₂, cq₂, T₀₂, X₀₂, Cs₂, C₂, Ccol, hCq₂, hcq₂, hT₀₂, hX₀₂, hCs₂, hC₂, hcap⟩ :=
    a2Rows_of_cap_gk K hK
  refine ⟨Cq₁, cq₁, T₀₁, X₀₁, Cs₁, C₁, Cq₂, cq₂, T₀₂, X₀₂, Cs₂, C₂, Ccol,
    hCq₁, hcq₁, hT₀₁, hX₀₁, hCs₁, hC₁, hCq₂, hcq₂, hT₀₂, hX₀₂, hCs₂, hC₂, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin Ymax ε
    EP2 Sb Ccc C₁' M₀ hM hXdQ F₁ F₂ hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ
    hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hLL hgate hStation hCcc hR0 hRrad hRlow hCbound hX₀k₁
    hX₀k₂ hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate₁ hCqgate₂ hε0 habs
    hEP2 hXN hN2 hsupp hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp hX3 hhX hTann hceil
    hT0band hgP1₁ hgP1₂ hgRows₁ hgRows₂ hεwin hL4096
  -- ⟦R3c⟧ the row's `EP₂` budget is now the ε-GRADED one; the frozen interface still
  -- carries the sharp `(log X)^{−θ₂₉₃}` gate, which is stronger (`ε ≥ 0`, `log X ≥ 1`)
  have hL1 : (1 : ℝ) ≤ Real.log X := le_trans (Real.one_le_exp (by norm_num)) hlX2
  have hEP2ε : 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) :=
    le_trans hEP2 (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  by_cases hfl : CapFreeFloor g X
  · exact thm_a2'_of_rows_gk K hM hXe hX3 hh4 hhX ha1 hsupp hN2 hTann hceil
      (hcapfree g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin
        Ymax ε EP2 hM hXdQ F₁ hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV
        hCb0 hPlow hQ0 hQhigh hPQ83 hfl hR0 hRrad hRlow hCbound hX₀k₁ hMfl0 hk2 hkX hkk
        hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate₁ hε0 habs hEP2ε hXN hN2 hsupp hNXd hcoef
        hwin hQXd hXdbig hN4 hdom ha1 hasupp)
      hT0band hgP1₁ hgRows₁ hεwin hL4096
  · exact thm_a2'_of_rows_gk K hM hXe hX3 hh4 hhX ha1 hsupp hN2 hTann hceil
      (hcap g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin
        Ymax ε EP2 Sb Ccc hM hXdQ F₂ hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1
        hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hLL hfl hgate hStation hCcc hR0 hRrad hRlow
        hCbound hX₀k₂ hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate₂ hε0
        habs hEP2ε hXN hN2 hsupp hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp)
      hT0band hgP1₂ hgRows₂ hεwin hL4096

set_option maxHeartbeats 1000000 in
theorem a2Rows_of_capfree3_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (Adoor M) (s13GK K M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (Adoor M) (s13GK K M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the window's TOP, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (s13GK K M) j ≤ p →
          p ≤ calQK (Adoor M) (s13GK K M) M j → ¬ p ∣ m →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (s13GK K M) j)
                    (calQK (Adoor M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (s13GK K M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow_gk K Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_capfree3
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (s13GK K M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_gk K M Xd hM hK hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (Adoor M) (s13GK K M) M 2 m₀ Ms
    Mt kk
    (H1door M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum_gk K M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum_nonneg_gk K hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_gk K M]
  have hlvl0 : (0 : ℝ) ≤ a2Level1 M := a2Level1_nonneg hM
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow_gk
  refine a2_row_weigh ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays_gk K hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_weigh_mr hRS0 hg3
  · exact a2_term4_weigh hZ0 hg32

set_option maxHeartbeats 1000000 in
theorem a2Rows_of_capfree3_end_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (Adoor M) (s13GK K M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (Adoor M) (s13GK K M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the window's TOP, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (s13GK K M) j ≤ p →
          p ≤ calQK (Adoor M) (s13GK K M) M j → ¬ p ∣ m →
          (Xd : ℝ) < (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (s13GK K M) j)
                    (calQK (Adoor M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (s13GK K M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow_gk K Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_capfree3_end
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (s13GK K M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_gk K M Xd hM hK hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (Adoor M) (s13GK K M) M 2 m₀ Ms
    Mt kk
    (H1door M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum_gk K M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum_nonneg_gk K hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_gk K M]
  have hlvl0 : (0 : ℝ) ≤ a2Level1 M := a2Level1_nonneg hM
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow_gk
  refine a2_row_weigh ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays_gk K hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_weigh_mr hRS0 hg3
  · exact a2_term4_weigh hZ0 hg32

-- #audit (temporary)

end Salt.MR
