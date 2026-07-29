/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ThmA2Rows
import Salt.MR.SeamCalibrationK
import Salt.MR.M4ErrRewire

/-!
# `FrameWitness` — THE `A2Frame3` INHABITANT (the TLGATES-SCOPE witness table, in Lean)

`ThmA2Rows.a2Rows_of_capfree3` consumes an `A2Frame3` bundle.  `a2Frame3_satisfiable_partial`
discharges seven of its eleven fields from the window's endpoints; the remaining four —
`thin`, `blocks`, `ksGate`, `err` — were, until this file, uninhabited: `TLBlockGates34` was
lifted to a hypothesis list at commit `1cfb470` and never modelled.  Flags,
`TLGATES-SCOPE`: *"`TLBlockGates34` has NO landed inhabitant anywhere."*

This file builds the inhabitant at the scoper's witness table.

## THE WITNESS TABLE

* **`P = Q`** — ⟦SUPERSEDED BY THE BAND RE-CUT, 2026-07-28; §2 is kept as the point
  specialization, §2′ is what the chain now runs on⟧ the block window was a single point, so
  `ramI H P P = {⌊H log P⌋₊}` is a SINGLETON (`ramI_self`) and `ramQbase H P j = P` at its
  only member (`ramQbase_at_pin`).  Every `∀ j ∈ ramI` collapsed to one instance.  The door
  datum CALLS that convenience (`M4RowSupply`'s point-vs-band note: at a point the coprime
  tail's charge is `O(1)`), so §4–§9 now run on the BAND `[P, Q]` through §2′'s sandwich
  `P ≤ ramQbase H P j ≤ Q`, with `Q` pinned at `⌊Q₈₃ X⌋₊`.
* **`kk`, `Mt`, `Ms`, `m₀` are DETERMINED, not free** — all four are read off the window
  bottom `B_j = X_d·e^{−j/H}` (`ramRbot`):

  | slot | witness | source |
  |---|---|---|
  | `kk j` | `⌈B_j⌉₊ − 1` | the half-open window cut (`witKk_cut`) |
  | `Mt j` | `⌊2B_j⌋₊ − 2` | the sharp Abel length (`RamRAdapter.ramR_abel_window_floor`) |
  | `Ms j` | `⌈2B_j⌉₊` | the co-factor range's ceiling (`witMs_range`) |
  | `m₀ j` | `⌊B_j⌋₊` | the row's own floor (`witM0_le`) |

  `kk`/`Mt` are exactly `CofactorBall.caseB_window_geometry`'s pair, made concrete so that a
  frame can name them; the six window conjuncts C9–C14 come from `4 ≤ B_j` alone.
* **`δ' = (log X)^{−3}`, `V = (log X)^3`** — the calibration (`ksGate_at_witness`,
  `calibration_at_witness`).

## THE FOUR FIELDS

1. `blocks_at_witness` — `TLBlockGates34`'s **seventeen** conjuncts (the scoper corrected
   "16"), per `j ∈ ramI` and per admissible height.  C1–C6 are the block-base gates
   (C4 is **THE `h`-CEILING**, see below); C7–C15 the window geometry; C16 the loglog
   descent charge; C17 the endpoint charge, discharged through `farSupS34`'s main term.
2. `thin_at_witness` — the thin-bundle demand, reduced from `∀ Tann ∀ j` to ONE inequality
   at the window's TOP `Tann = X` and the singleton's only `j` (`thinBundleG` is monotone
   in the height, `thinBundleG_mono_T`).
3. `ksGate_at_witness` — pure `rpow` arithmetic at `δ' = (log X)^{−3}`.
4. `err_at_witness` — the moment route: `USetResiduals.E_priced_row_scale` (the factor-3
   split `RamareWindows.ramErr_moment_split`) at the `N = 2X_d` pin, with the `p²`-mass slot
   filled by `SeamCalibrationK.ramP2mass_direct`.  **§8′ supersedes it as the frame's
   supplier**: `err_at_witness_mr` reaches the same conclusion through
   `M4ErrRewire.E_priced_mr_row_scale` with the window law `hwin` GONE (⟦THE WALL⟧).
   `err_at_witness` is kept, unweakened, as the historical route and the `3` vs `4` witness.

## THE `h`-CEILING (law #253, in-statement)

`TLBlockGates34`'s C4 — `30 ≤ log Tann / log(ramQbase)` — is read at the window's BOTTOM
`Tann = 2X/h`.  At the POINT chain (§3) that is

  `log h + 30·(log X)^{1−θ₂₉₃} ≤ log X`;

at the BAND chain (§3′), where the base runs up to `Q ≤ Q₈₃ X`, it is

  `log h + 30·(log X/loglog X) ≤ log X`,   i.e.   `h ≤ X^{1−30/loglog X}`.

⟦THE CORNER⟧ that is the SMALLEST charge any admissible band top can carry — the reason `Q`
is pinned at `⌊Q₈₃ X⌋₊` and not left free: pushing `Q` up breaks the §8.3 window, pulling it
down raises the tail grade `log P/log Q`, and the `30/loglog X` charge vanishes on the loglog
scale either way.  Neither form follows from the other gates (the window bottom is a free
parameter of the dyadic family), so both are carried as named hypotheses `hhceil` and never
derived.

## WHAT IS CARRIED, AND WHY

Every scale floor appears as a SYMBOLIC named hypothesis, never as a numeral: the scoper's
`loglog X ≥ 996.4` (C4), `loglog X ≥ 6412.6` (the ε-window) and "~7 orders of margin"
(thin) are derived CONTEXT for why the hypotheses are clearable at door numerology — they
are not inlined here.  The two capstone existentials `Cq₁`/`cq₁` are opaque
(flags, K6), so their gates ride as binders `hcqgate`/`hCqgate`: the M4-5 consumer
instantiates them INSIDE the capstone's existential scope, where their magnitudes are
readable.

## THE `p²`-MASS FINDING

REPAIR-REF priced a NEW sharp `p²`-mass stone ("no landed bound at all").  It is landed:
`SeamCalibrationK.ramP2mass_direct` gives

  `Σ_{n≤N} ‖ramP2coeff N P Q a b c n‖²/n² ≤ 16·log₂(2X_d)/(X_d·P)`,

exactly the `C·D/(P·X_d)` grade with `D = log₂(2X_d)` the honest fibre multiplicity
(`fiber_card_le_omega` + `2^{ω(n)} ≤ n ≤ 2X_d`).  Nothing new was needed; §6 consumes it.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — THE WITNESS VALUES

All four ladder slots are functions of the window bottom `B_j = ramRbot H X_d j` alone. -/

/-- **The witness cut** `k₀(j) = ⌈B_j⌉₊ − 1` — the largest integer strictly below the window
bottom (`CofactorBall.exists_window_cut`'s witness, made concrete). -/
noncomputable def witKk (H : ℝ) (Xd j : ℕ) : ℕ := ⌈ramRbot H Xd j⌉₊ - 1

/-- **The witness Abel length** `M(j) = ⌊2B_j⌋₊ − 2` — the ⟦V4a⟧ sharp-`M` law
(`RamRAdapter.ramR_abel_window_floor`'s value). -/
noncomputable def witMt (H : ℝ) (Xd j : ℕ) : ℕ := ⌊2 * ramRbot H Xd j⌋₊ - 2

/-- **The witness thin ladder** `M_s(j) = ⌈2B_j⌉₊` — the smallest integer above the co-factor
range's top, so `ramRrange ⊆ [1, M_s(j)]`. -/
noncomputable def witMs (H : ℝ) (Xd j : ℕ) : ℕ := ⌈2 * ramRbot H Xd j⌉₊

/-- **The witness row floor** `m₀(j) = ⌊B_j⌋₊` — the largest integer below the window
bottom, so `m₀(j) ≤ B_j` (the row's `hm₀`). -/
noncomputable def witM0 (H : ℝ) (Xd j : ℕ) : ℕ := ⌊ramRbot H Xd j⌋₊

/-! ### The window cut and the sharp length -/

/-- **The cut, at the witness.**  `k₀ = ⌈B⌉₊ − 1` satisfies `k₀ < B ≤ k₀+1` whenever
`1 ≤ B` — `CofactorBall.exists_window_cut`'s content at its own witness. -/
lemma witKk_cut {H : ℝ} {Xd j : ℕ} (hW : 1 ≤ ramRbot H Xd j) :
    ((witKk H Xd j : ℕ) : ℝ) < ramRbot H Xd j ∧
      ramRbot H Xd j ≤ ((witKk H Xd j : ℕ) : ℝ) + 1 := by
  set W := ramRbot H Xd j with hWdef
  have hceil : W ≤ (⌈W⌉₊ : ℝ) := Nat.le_ceil W
  have hlt : (⌈W⌉₊ : ℝ) < W + 1 := Nat.ceil_lt_add_one (by linarith)
  have h1 : 1 ≤ ⌈W⌉₊ := by
    have : (1 : ℝ) ≤ (⌈W⌉₊ : ℝ) := le_trans hW hceil
    exact_mod_cast this
  have hcast : ((witKk H Xd j : ℕ) : ℝ) = (⌈W⌉₊ : ℝ) - 1 := by
    rw [witKk, ← hWdef, Nat.cast_sub h1, Nat.cast_one]
  rw [hcast]
  exact ⟨by linarith, by linarith⟩

/-- **The Abel window, at the witness.**  `RamRAdapter.ramR_abel_window_floor` read at
`W := B_j`; `witMt` is literally its `⌊2W⌋₊ − 2`. -/
lemma witMt_window {H : ℝ} {Xd j : ℕ} (hW : 4 ≤ ramRbot H Xd j) :
    ramRbot H Xd j - 1 ≤ ((witMt H Xd j : ℕ) : ℝ) ∧
      ((witMt H Xd j : ℕ) : ℝ) ≤ 2 * (ramRbot H Xd j - 1) ∧
      2 * ramRbot H Xd j < ((witMt H Xd j : ℕ) : ℝ) + 3 :=
  ramR_abel_window_floor hW

/-- **THE SIX WINDOW CONJUNCTS** (C9–C14 of `TLBlockGates34`) from `4 ≤ B_j` alone — the
concrete form of `CofactorBall.caseB_window_geometry`, at named `kk`/`Mt`. -/
lemma witness_window_geometry {H : ℝ} {Xd j : ℕ} (hW : 4 ≤ ramRbot H Xd j) :
    ((witKk H Xd j : ℕ) : ℝ) < ramRbot H Xd j ∧
      ramRbot H Xd j ≤ ((witKk H Xd j : ℕ) : ℝ) + 1 ∧
      1 < ramRbot H Xd j ∧
      ramRbot H Xd j - 1 ≤ ((witMt H Xd j : ℕ) : ℝ) ∧
      ((witMt H Xd j : ℕ) : ℝ) ≤ 2 * (ramRbot H Xd j - 1) ∧
      2 * ramRbot H Xd j < ((witMt H Xd j : ℕ) : ℝ) + 3 := by
  obtain ⟨h1, h2⟩ := witKk_cut (by linarith)
  obtain ⟨h3, h4, h5⟩ := witMt_window hW
  exact ⟨h1, h2, by linarith, h3, h4, h5⟩

/-- `B_j ≤ X_d`: the window bottom never exceeds the dyadic scale (`e^{−j/H} ≤ 1`). -/
lemma ramRbot_le_scale {H : ℝ} (hH : 0 < H) (Xd j : ℕ) :
    ramRbot H Xd j ≤ (Xd : ℝ) := by
  rw [ramRbot]
  have hexp : Real.exp (-(j : ℝ) / H) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg j)) hH.le
  nlinarith [Nat.cast_nonneg (α := ℝ) Xd, Real.exp_pos (-(j : ℝ) / H)]

/-! ### The ladder slots the ROW (not the frame) consumes -/

/-- `ramRrange ⊆ [1, M_s(j)]` at `M_s(j) = ⌈2B_j⌉₊` — `a2Rows_of_capfree3`'s `hMs`. -/
lemma witMs_range (H : ℝ) (N Xd j : ℕ) :
    ramRrange H N Xd j ⊆ Finset.Icc 1 (witMs H Xd j) := by
  intro m hm
  have h1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  have h2 : (m : ℝ) ≤ 2 * ramRbot H Xd j := ramRrange_le_top hm
  refine Finset.mem_Icc.mpr ⟨h1, ?_⟩
  have hc : (m : ℝ) ≤ ((witMs H Xd j : ℕ) : ℝ) :=
    le_trans h2 (by rw [witMs]; exact Nat.le_ceil _)
  exact_mod_cast hc

/-- `m₀(j) = ⌊B_j⌋₊ ≤ B_j` — `a2Rows_of_capfree3`'s `hm₀`. -/
lemma witM0_le (H : ℝ) (Xd j : ℕ) : ((witM0 H Xd j : ℕ) : ℝ) ≤ ramRbot H Xd j :=
  Nat.floor_le (ramRbot_nonneg H Xd j)

/-- `2 ≤ m₀(j)` — `a2Rows_of_capfree3`'s `hm₀2`, from `4 ≤ B_j`. -/
lemma witM0_two_le {H : ℝ} {Xd j : ℕ} (hW : 4 ≤ ramRbot H Xd j) : 2 ≤ witM0 H Xd j := by
  rw [witM0]
  exact Nat.le_floor (by push_cast; linarith)

/-- `M_s(j) ≤ 4(m₀(j) − 1)` — `a2Rows_of_capfree3`'s `hMs4` (the trap-7 ladder collision,
cleared with room to spare at `B_j ≥ 4`: `2B+1 ≤ 4B−8` needs only `B ≥ 4.5`; the honest
constant here is `B ≥ 5`). -/
lemma witMs_le_four_mul {H : ℝ} {Xd j : ℕ} (hW : 5 ≤ ramRbot H Xd j) :
    ((witMs H Xd j : ℕ) : ℝ) ≤ 4 * (((witM0 H Xd j : ℕ) : ℝ) - 1) := by
  set B := ramRbot H Xd j with hB
  have hup : ((witMs H Xd j : ℕ) : ℝ) < 2 * B + 1 := by
    rw [witMs, ← hB]; exact Nat.ceil_lt_add_one (by linarith)
  have hlow : B - 1 < ((witM0 H Xd j : ℕ) : ℝ) := by
    rw [witM0, ← hB]; exact Nat.sub_one_lt_floor B
  linarith

/-! ## §2 — THE SINGLETON `ramI` AT `P = Q`

The witness table's first entry.  `ramI H P Q = Icc ⌊H log P⌋₊ ⌊H log Q⌋₊`; at `P = Q` the
two endpoints coincide, so the index set is a singleton and `ramQbase H P j = P` there. -/

/-- **`ramI` IS A SINGLETON AT `P = Q`.** -/
lemma ramI_self (H : ℝ) (P : ℕ) : ramI H P P = {⌊H * Real.log (P : ℝ)⌋₊} := by
  rw [ramI]; exact Finset.Icc_self _

lemma mem_ramI_self {H : ℝ} {P j : ℕ} (hj : j ∈ ramI H P P) :
    j = ⌊H * Real.log (P : ℝ)⌋₊ := by
  rw [ramI_self] at hj; exact Finset.mem_singleton.mp hj

lemma ramI_self_mem (H : ℝ) (P : ℕ) : ⌊H * Real.log (P : ℝ)⌋₊ ∈ ramI H P P := by
  rw [ramI_self]; exact Finset.mem_singleton_self _

lemma ramI_self_nonempty (H : ℝ) (P : ℕ) : (ramI H P P).Nonempty :=
  ⟨_, ramI_self_mem H P⟩

/-- **THE BLOCK BASE COLLAPSES TO `P`** (`ramQbase_at_pin`).  `ramQbase H P j = max P
⌈e^{j/H}⌉₊`, and at the singleton's index `j = ⌊H log P⌋₊ ≤ H log P` the second argument is
`≤ P`.  This is what makes C2–C6 read at `P` itself. -/
lemma ramQbase_at_pin {H : ℝ} {P j : ℕ} (hH : 0 < H) (hP : 1 ≤ P) (hj : j ∈ ramI H P P) :
    ramQbase H P j = P := by
  have hjeq := mem_ramI_self hj
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hlogP : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg (by exact_mod_cast hP)
  have hjle : (j : ℝ) ≤ H * Real.log (P : ℝ) := by
    rw [hjeq]; exact Nat.floor_le (by positivity)
  have hdiv : (j : ℝ) / H ≤ Real.log (P : ℝ) := by
    rw [div_le_iff₀ hH]; nlinarith
  have hexp : Real.exp ((j : ℝ) / H) ≤ (P : ℝ) := by
    calc Real.exp ((j : ℝ) / H) ≤ Real.exp (Real.log (P : ℝ)) := Real.exp_le_exp.mpr hdiv
      _ = (P : ℝ) := Real.exp_log hP0
  rw [ramQbase, max_eq_left (Nat.ceil_le.mpr hexp)]

/-- **C1 at the singleton** — `H ≤ j`.  `j = ⌊H log P⌋₊ > H log P − 1 ≥ 2H − 1 ≥ H`. -/
lemma ramI_self_index_ge {H : ℝ} {P j : ℕ} (hH : 1 ≤ H) (hlogP : 2 ≤ Real.log (P : ℝ))
    (hj : j ∈ ramI H P P) : H ≤ (j : ℝ) := by
  have hjeq := mem_ramI_self hj
  have hlt : H * Real.log (P : ℝ) < (j : ℝ) + 1 := by
    rw [hjeq]; exact Nat.lt_floor_add_one _
  nlinarith

/-! ## §2′ — ⟦THE BAND RE-CUT⟧: THE `ramQbase` SANDWICH ON `[P, Q]`

⟦THE POINT-vs-BAND WALL⟧ (flags, `1bab8e3`).  `P = Q` above was TLGATES-SCOPE's *"easiest
witness; a genuine band also works"* — and the door datum calls it.  At a POINT the Ramaré
block-free mass is `≍ 1/X_d`, so the coprime tail's charge `(2X+20N)·M_tail` is `O(1)` and no
ε-window absorbs it (`M4RowSupply`'s header).  The repair is mathematically forced: re-cut the
witness chain at the BAND `[P, Q]`, with **`Q` pinned at `⌊Q₈₃ X⌋₊`** — the corner where C4's
`h`-ceiling charge is the minimal `30·log X/loglog X` while the tail grade
`log P/log Q` is the minimal `loglog X·(log X)^{−θ₂₉₃}`.

At a band `ramI H P Q = Icc ⌊H log P⌋₊ ⌊H log Q⌋₊` is no longer a singleton and
`ramQbase H P j = max P ⌈e^{j/H}⌉₊` is no longer `P`.  What survives — and it is exactly what
every `TLBlockGates34` conjunct reads — is the SANDWICH

  `P ≤ ramQbase H P j ≤ Q`   for every `j ∈ ramI H P Q`.

C2/C6 (the gates that want the base LARGE) transport UP from `P`; C3/C4/C5 (the gates that
want it SMALL) transport DOWN from `Q`.  ⟦DRIFT vs the brief⟧ C5 (`log ramQbase ≤ L`) is an
UPPER bound on the base, so it transports DOWN from `Q` too — `log P ≤ L` cannot supply it. -/

/-- **THE SANDWICH, BOTTOM** (`ramQbase_ge_bot`).  `P ≤ ramQbase H P j` at every `j`, with no
hypothesis at all — `le_max_left`. -/
lemma ramQbase_ge_bot (H : ℝ) (P j : ℕ) : P ≤ ramQbase H P j := le_max_left _ _

/-- **THE SANDWICH, TOP** (`ramQbase_le_top`).  At `j ≤ ⌊H log Q⌋₊` the block height obeys
`j/H ≤ log Q`, hence `⌈e^{j/H}⌉₊ ≤ Q`; with `P ≤ Q` the `max` is too. -/
lemma ramQbase_le_top {H : ℝ} {P Q j : ℕ} (hH : 0 < H) (hQ1 : 1 ≤ Q) (hPQ : P ≤ Q)
    (hj : j ∈ ramI H P Q) : ramQbase H P j ≤ Q := by
  rw [ramI, Finset.mem_Icc] at hj
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
  have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg (by exact_mod_cast hQ1)
  have hjR : (j : ℝ) ≤ H * Real.log (Q : ℝ) := by
    have h1 : ((j : ℕ) : ℝ) ≤ ((⌊H * Real.log (Q : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hj.2
    exact le_trans h1 (Nat.floor_le (by positivity))
  have hdiv : (j : ℝ) / H ≤ Real.log (Q : ℝ) := by rw [div_le_iff₀ hH]; nlinarith
  have hexp : Real.exp ((j : ℝ) / H) ≤ (Q : ℝ) := by
    calc Real.exp ((j : ℝ) / H) ≤ Real.exp (Real.log (Q : ℝ)) := Real.exp_le_exp.mpr hdiv
      _ = (Q : ℝ) := Real.exp_log hQ0
  exact max_le hPQ (Nat.ceil_le.mpr hexp)

/-- **C1 AT THE BAND** (`ramI_index_ge`).  `H ≤ j` for every `j ∈ ramI H P Q`, from the
BOTTOM endpoint alone: `j ≥ ⌊H log P⌋₊ > H log P − 1 ≥ 2H − 1 ≥ H`. -/
lemma ramI_index_ge {H : ℝ} {P Q j : ℕ} (hH : 1 ≤ H) (hlogP : 2 ≤ Real.log (P : ℝ))
    (hj : j ∈ ramI H P Q) : H ≤ (j : ℝ) := by
  rw [ramI, Finset.mem_Icc] at hj
  have hlt : H * Real.log (P : ℝ) < ((⌊H * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hjR : ((⌊H * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  nlinarith

/-! ## §3 — THE `h`-CEILING (K8, law #253)

`TLBlockGates34`'s C4 is `30 ≤ log Tann / log(ramQbase)`, read at the window's BOTTOM
`Tann = 2X/h`.  With `ramQbase = P` and `log P ≤ (log X)^{1−θ}` this is exactly

  `log h + 30·(log X)^{1−θ₂₉₃} ≤ log X`,

the `h`-ceiling.  It is NOT a consequence of the other gates — the dyadic family's `h` is a
free parameter — so it enters every downstream statement as a named hypothesis. -/

/-- **THE `h`-CEILING, IN ITS USABLE FORM.**  From `log h + 30(log X)^{1−θ} ≤ log X` and
`log P ≤ (log X)^{1−θ}`: `30 log P ≤ log(2X/h)`. -/
lemma h_ceiling_gate {X h : ℝ} {P : ℕ} (hX0 : 0 < X) (hh0 : 0 < h)
    (hhceil : Real.log h + 30 * (Real.log X) ^ (1 - theta293) ≤ Real.log X)
    (hPlog : Real.log (P : ℝ) ≤ (Real.log X) ^ (1 - theta293)) :
    30 * Real.log (P : ℝ) ≤ Real.log (2 * (X / h)) := by
  have hlog : Real.log (2 * (X / h)) = Real.log 2 + Real.log X - Real.log h := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_div hX0.ne' hh0.ne']
    ring
  have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [hlog]
  linarith

/-- **C4, at any admissible height.**  The `h`-ceiling is read at the bottom and transported
up by monotonicity of `log`. -/
lemma c4_at_height {X h Tann : ℝ} {P : ℕ} (hX0 : 0 < X) (hh0 : 0 < h)
    (hbot : 2 * (X / h) ≤ Tann) (hlogP0 : 0 < Real.log (P : ℝ))
    (hhceil : Real.log h + 30 * (Real.log X) ^ (1 - theta293) ≤ Real.log X)
    (hPlog : Real.log (P : ℝ) ≤ (Real.log X) ^ (1 - theta293)) :
    30 ≤ Real.log Tann / Real.log (P : ℝ) := by
  have hbot0 : (0 : ℝ) < 2 * (X / h) := by positivity
  have hmono : Real.log (2 * (X / h)) ≤ Real.log Tann := Real.log_le_log hbot0 hbot
  have := h_ceiling_gate (P := P) hX0 hh0 hhceil hPlog
  rw [le_div_iff₀ hlogP0]
  linarith

/-! ### §3′ — THE BAND `h`-CEILING (⟦THE BAND RE-CUT⟧'s C4)

At the band the C4 charge is read at the TOP `Q`, not at `P`, and the `Q₈₃` pin turns
`log Q ≤ log X/loglog X` — so the `h`-ceiling becomes

  `log h + 30·(log X/loglog X) ≤ log X`,

i.e. `h ≤ X^{1−30/loglog X}`.  THE CORNER: this is the *smallest* charge any admissible band
top can carry (any `Q > Q₈₃` breaks the §8.3 window, any `Q < Q₈₃` raises the tail grade), and
it VANISHES on the loglog scale — which is what makes the band re-cut free at the door. -/

/-- `log Q ≤ log X/loglog X` from `Q ≤ Q₈₃ X` — `M4RowSupply.m4_tail_gate_at_pins`' first
step, restated here because `FrameWitness` is upstream of that file. -/
lemma log_le_of_le_Q83 {X : ℝ} {Q : ℕ} (hQ1 : 1 ≤ Q) (hQ : (Q : ℝ) ≤ Q83 X) :
    Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
  have h := Real.log_le_log hQ0 hQ
  rwa [Q83, Real.log_exp] at h

/-- **THE BAND `h`-CEILING, IN ITS USABLE FORM** (`h_ceiling_gate_band`).  From
`log h + 30·(log X/loglog X) ≤ log X` and `log Q ≤ log X/loglog X`: `30 log Q ≤ log(2X/h)`. -/
lemma h_ceiling_gate_band {X h : ℝ} {Q : ℕ} (hX0 : 0 < X) (hh0 : 0 < h)
    (hhceil : Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X)
    (hQlog : Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) :
    30 * Real.log (Q : ℝ) ≤ Real.log (2 * (X / h)) := by
  have hlog : Real.log (2 * (X / h)) = Real.log 2 + Real.log X - Real.log h := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_div hX0.ne' hh0.ne']
    ring
  have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [hlog]
  linarith

/-- **C4 AT THE BAND, AT ANY ADMISSIBLE HEIGHT** (`c4_at_height_band`).  The band `h`-ceiling
is read at the window's BOTTOM and transported up by monotonicity of `log`, through the
SANDWICH's top `ramQbase H P j ≤ Q`. -/
lemma c4_at_height_band {X h Tann H : ℝ} {P Q j : ℕ} (hX0 : 0 < X) (hh0 : 0 < h)
    (hbot : 2 * (X / h) ≤ Tann)
    (hbase3 : 3 ≤ ramQbase H P j) (hbaseQ : ramQbase H P j ≤ Q)
    (hhceil : Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X)
    (hQlog : Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) :
    30 ≤ Real.log Tann / Real.log ((ramQbase H P j : ℕ) : ℝ) := by
  have hb3 : (3 : ℝ) ≤ ((ramQbase H P j : ℕ) : ℝ) := by exact_mod_cast hbase3
  have hb0 : (0 : ℝ) < ((ramQbase H P j : ℕ) : ℝ) := by linarith
  have hblog0 : 0 < Real.log ((ramQbase H P j : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hbQ : Real.log ((ramQbase H P j : ℕ) : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log hb0 (by exact_mod_cast hbaseQ)
  have hbot0 : (0 : ℝ) < 2 * (X / h) := by positivity
  have hmono : Real.log (2 * (X / h)) ≤ Real.log Tann := Real.log_le_log hbot0 hbot
  have hband := h_ceiling_gate_band (Q := Q) hX0 hh0 hhceil hQlog
  rw [le_div_iff₀ hblog0]
  linarith

/-! ## §4 — FIELD 1: `blocks` (`TLBlockGates34`'s SEVENTEEN conjuncts)

The clause-by-clause discharge at the witness table.  Grouping by constraint direction:

| clause | statement | source |
|---|---|---|
| C1 | `H ≤ j` | the singleton index (`ramI_self_index_ge`) |
| C2 | `3 ≤ ramQbase` | `ramQbase = P ≥ 3` |
| C3 | `ramQbase ≤ Tann` | named `hPT` (the window bottom clears `P`) |
| C4 | `30 ≤ log Tann/log ramQbase` | **THE `h`-CEILING** (`c4_at_height`) |
| C5 | `log ramQbase ≤ L` | named `hPL` |
| C6 | the `cq`-inequality | named `hcqgate` (K6: `cq₁` is opaque) |
| C7 | `ballQuarterThreshold ≤ kk` | named `hkth`, via `kk ≥ B−1` |
| C8 | `Mt ≤ N` | `⌊2B⌋₊ ≤ 2X_d ≤ N` |
| C9–C14 | the window geometry | `witness_window_geometry` (from `4 ≤ B`) |
| C15 | `Mt ≤ X` | `Mt ≤ 2(B−1)` and named `hMtX` |
| C16 | the loglog descent charge | named `hC16`, moved onto `kk` by monotonicity |
| C17 | the endpoint charge | `farSupS34`'s main term `2√2/R`, named `hRradW` |

C6/C16 are the two genuinely arithmetic floors (the scoper's `loglog X ≥ 996.4` /
`≥ 6412.6` grades); both ride as symbolic hypotheses, per law #253. -/

/-- **THE `TLBlockGates34` INHABITANT AT THE BAND** (`tlBlockGates34_at_witness`).
All seventeen conjuncts at `kk = witKk`, `Mt = witMt`, on the BAND `[P, Q]` — the block base
`ramQbase H P j` now varies with `j`, and §2′'s sandwich `P ≤ ramQbase H P j ≤ Q` is what
routes each conjunct to its endpoint: C2/C6 up from `P`, C3/C4/C5 down from `Q`. -/
theorem tlBlockGates34_at_witness
    {cq H L Cb X Rrad Tann : ℝ} {P Q N Xd j : ℕ}
    (hH1 : 1 ≤ H) (hP3 : 3 ≤ P) (hlogP2 : 2 ≤ Real.log (P : ℝ))
    (hQ1 : 1 ≤ Q) (hPQ : P ≤ Q) (hcq0 : 0 ≤ cq)
    (hj : j ∈ ramI H P Q)
    -- C3–C6: the block-base gates, read through the sandwich
    (hQT : (Q : ℝ) ≤ Tann)
    (h30 : 30 ≤ Real.log Tann / Real.log ((ramQbase H P j : ℕ) : ℝ))
    (hQL : Real.log (Q : ℝ) ≤ L)
    (hcqgate : 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2)
    -- C7–C16: the window floors
    (hW4 : 4 ≤ ramRbot H Xd j)
    (hkth : ballQuarterThreshold + 1 ≤ ramRbot H Xd j)
    (hMN : 2 * Xd ≤ N)
    (hMtX : 2 * ramRbot H Xd j ≤ X)
    (hC16 : 18 + Real.log (Real.log X) - Real.log (Real.log (ramRbot H Xd j - 1))
        ≤ 32 * theta293 * Real.log (Real.log X))
    -- C17: the endpoint charge
    (hRrad0 : 0 < Rrad) (hRradW : Rrad ≤ Real.sqrt 2 * ramRbot H Xd j) :
    TLBlockGates34 cq H P N Xd (witMt H Xd) (witKk H Xd) Tann L (1 / Real.exp 1) Cb X
      theta293 Rrad j := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hP1 : 1 ≤ P := by omega
  -- ⟦THE SANDWICH⟧ `P ≤ ramQbase H P j ≤ Q`, in the real-valued shapes the gates want
  have hbP : P ≤ ramQbase H P j := ramQbase_ge_bot H P j
  have hbQ : ramQbase H P j ≤ Q := ramQbase_le_top hH0 hQ1 hPQ hj
  have hbPR : ((P : ℕ) : ℝ) ≤ ((ramQbase H P j : ℕ) : ℝ) := by exact_mod_cast hbP
  have hbQR : ((ramQbase H P j : ℕ) : ℝ) ≤ ((Q : ℕ) : ℝ) := by exact_mod_cast hbQ
  have hP0R : (0 : ℝ) < (P : ℝ) := by positivity
  have hb0R : (0 : ℝ) < ((ramQbase H P j : ℕ) : ℝ) := lt_of_lt_of_le hP0R hbPR
  have hlogP0 : 0 < Real.log (P : ℝ) := by linarith
  have hlogbP : Real.log (P : ℝ) ≤ Real.log ((ramQbase H P j : ℕ) : ℝ) :=
    Real.log_le_log hP0R hbPR
  have hlogbQ : Real.log ((ramQbase H P j : ℕ) : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log hb0R hbQR
  obtain ⟨hg1, hg2, hg3, hg4, hg5, hg6⟩ := witness_window_geometry hW4
  have hkkge : ramRbot H Xd j - 1 ≤ ((witKk H Xd j : ℕ) : ℝ) := by linarith
  -- ⟦C8⟧ `⌊2B⌋₊ ≤ 2X_d ≤ N`
  have hC8 : witMt H Xd j ≤ N := by
    have hle : (2 : ℝ) * ramRbot H Xd j ≤ ((2 * Xd : ℕ) : ℝ) := by
      have := ramRbot_le_scale hH0 Xd j; push_cast; linarith
    have hfl : ⌊2 * ramRbot H Xd j⌋₊ ≤ 2 * Xd := by
      have h := Nat.floor_le_floor hle
      rwa [Nat.floor_natCast] at h
    rw [witMt]; omega
  -- ⟦C16⟧ the descent charge, moved onto `kk` by monotonicity of `log ∘ log`
  have hBm1 : (0 : ℝ) < ramRbot H Xd j - 1 := by linarith
  have hlogB : 0 < Real.log (ramRbot H Xd j - 1) := Real.log_pos (by linarith)
  have hlogmono : Real.log (ramRbot H Xd j - 1) ≤ Real.log ((witKk H Xd j : ℕ) : ℝ) :=
    Real.log_le_log hBm1 hkkge
  have hkklog : 0 < Real.log ((witKk H Xd j : ℕ) : ℝ) := lt_of_lt_of_le hlogB hlogmono
  have hC16' : 18 + Real.log (Real.log X) - Real.log (Real.log ((witKk H Xd j : ℕ) : ℝ))
      ≤ 32 * theta293 * Real.log (Real.log X) := by
    have := Real.log_le_log hlogB hlogmono
    linarith
  -- ⟦C17⟧ the endpoint charge, through `farSupS34`'s main term
  have hMt1 : (1 : ℝ) ≤ ((witMt H Xd j : ℕ) : ℝ) := by linarith
  have hMtlog : 0 ≤ Real.log ((witMt H Xd j : ℕ) : ℝ) := Real.log_nonneg hMt1
  have hTs0 : 0 ≤ Tstar2 ((witMt H Xd j : ℕ) : ℝ) (Real.log ((witMt H Xd j : ℕ) : ℝ)) := by
    rw [Tstar2]
    exact mul_nonneg (by rw [ypin2]; positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hfar : 0 ≤ farErr34 ((witKk H Xd j : ℕ) : ℝ) ((witMt H Xd j : ℕ) : ℝ)
      (Tstar2 ((witMt H Xd j : ℕ) : ℝ) (Real.log ((witMt H Xd j : ℕ) : ℝ))) :=
    farErr34_nonneg hkklog hMtlog hTs0
  have hB0 : (0 : ℝ) < ramRbot H Xd j := by linarith
  have hmain : 2 / ramRbot H Xd j ≤ 2 * Real.sqrt 2 / Rrad := by
    rw [div_le_div_iff₀ hB0 hRrad0]
    nlinarith
  have hC17 : 2 / ramRbot H Xd j
      ≤ cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 ((witKk H Xd j : ℕ) : ℝ)
          ((witMt H Xd j : ℕ) : ℝ)
          (Tstar2 ((witMt H Xd j : ℕ) : ℝ) (Real.log ((witMt H Xd j : ℕ) : ℝ))) Rrad / 3 := by
    rw [cofactorRbd34loc]
    have hid : (3 : ℝ) * max (2 * caseAS2 (1 / Real.exp 1) Cb
          (cofactorMfl X theta293 ((witKk H Xd j : ℕ) : ℝ)) ((witKk H Xd j : ℕ) : ℝ))
        (farSupS34 ((witKk H Xd j : ℕ) : ℝ) ((witMt H Xd j : ℕ) : ℝ)
          (Tstar2 ((witMt H Xd j : ℕ) : ℝ) (Real.log ((witMt H Xd j : ℕ) : ℝ))) Rrad) / 3
        = max (2 * caseAS2 (1 / Real.exp 1) Cb
          (cofactorMfl X theta293 ((witKk H Xd j : ℕ) : ℝ)) ((witKk H Xd j : ℕ) : ℝ))
        (farSupS34 ((witKk H Xd j : ℕ) : ℝ) ((witMt H Xd j : ℕ) : ℝ)
          (Tstar2 ((witMt H Xd j : ℕ) : ℝ) (Real.log ((witMt H Xd j : ℕ) : ℝ))) Rrad) := by
      ring
    rw [hid]
    refine le_trans ?_ (le_max_right _ _)
    rw [farSupS34]
    linarith
  refine ⟨ramI_index_ge hH1 hlogP2 hj, ?_, ?_, h30, ?_, ?_, ?_, hC8,
    hg1, hg2, hg3, hg4, hg5, hg6, by linarith, hC16', hC17⟩
  · -- ⟦C2⟧ UP from `P`: `3 ≤ P ≤ ramQbase`
    omega
  · -- ⟦C3⟧ DOWN from `Q`: `ramQbase ≤ Q ≤ Tann`
    linarith
  · -- ⟦C5⟧ DOWN from `Q`: `log ramQbase ≤ log Q ≤ L`
    linarith
  · -- ⟦C6⟧ UP from `P`: the gate is monotone in the base (`cq ≥ 0`)
    have hsq : (Real.log (P : ℝ)) ^ 2 ≤ (Real.log ((ramQbase H P j : ℕ) : ℝ)) ^ 2 := by
      nlinarith
    have hmono := mul_le_mul_of_nonneg_left hsq hcq0
    linarith
  · linarith

/-- **FIELD 1, IN THE FRAME'S SHAPE** (`blocks_at_witness`).  `A2Frame3.blocks` verbatim:
`∀ Tann` in the window `[2X/h, X]`, `∀ j ∈ ramI`.  C3 and C4 are stated at the window's
BOTTOM and transported up — C4 through the `h`-ceiling (`c4_at_height`), which is what makes
the bottom reachable at all. -/
theorem blocks_at_witness
    {cq L Cb X h Rrad : ℝ} {P Q N Xd : ℕ}
    (hX0 : 0 < X) (hh0 : 0 < h)
    (hH1 : 1 ≤ H83 X theta293) (hP3 : 3 ≤ P) (hlogP2 : 2 ≤ Real.log (P : ℝ))
    (hQ1 : 1 ≤ Q) (hPQ : P ≤ Q) (hcq0 : 0 ≤ cq)
    -- C3/C4: the window bottom clears the band TOP, and THE BAND `h`-CEILING
    (hQbot : (Q : ℝ) ≤ 2 * (X / h))
    (hhceil : Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X)
    (hQlog : Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X))
    -- C5/C6
    (hQL : Real.log (Q : ℝ) ≤ L)
    (hcqgate : 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2)
    -- C7–C16, per block
    (hW4 : ∀ j ∈ ramI (H83 X theta293) P Q, 4 ≤ ramRbot (H83 X theta293) Xd j)
    (hkth : ∀ j ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd j)
    (hMN : 2 * Xd ≤ N)
    (hMtX : ∀ j ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd j ≤ X)
    (hC16 : ∀ j ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X) - Real.log (Real.log (ramRbot (H83 X theta293) Xd j - 1))
        ≤ 32 * theta293 * Real.log (Real.log X))
    -- C17
    (hRrad0 : 0 < Rrad)
    (hRradW : ∀ j ∈ ramI (H83 X theta293) P Q,
      Rrad ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd j) :
    ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
      ∀ j ∈ ramI (H83 X theta293) P Q,
        TLBlockGates34 cq (H83 X theta293) P N Xd (witMt (H83 X theta293) Xd)
          (witKk (H83 X theta293) Xd) Tann L (1 / Real.exp 1) Cb X theta293 Rrad j := by
  intro Tann hbot _ j hj
  have hH0 : (0 : ℝ) < H83 X theta293 := by linarith
  have hbase3 : 3 ≤ ramQbase (H83 X theta293) P j :=
    le_trans hP3 (ramQbase_ge_bot (H83 X theta293) P j)
  have hbaseQ : ramQbase (H83 X theta293) P j ≤ Q := ramQbase_le_top hH0 hQ1 hPQ hj
  exact tlBlockGates34_at_witness hH1 hP3 hlogP2 hQ1 hPQ hcq0 hj (le_trans hQbot hbot)
    (c4_at_height_band hX0 hh0 hbot hbase3 hbaseQ hhceil hQlog) hQL hcqgate (hW4 j hj)
    (hkth j hj) hMN (hMtX j hj) (hC16 j hj) hRrad0 (hRradW j hj)

/-! ## §5 — FIELD 2: `thin`

`A2Frame3.thin` is `∀ Tann ∀ j ∈ ramI, thinBundleG Tann … · X^{1−2η} ≤ M_s(j)`.  Two
reductions carry it to a SINGLE inequality:

* `thinBundleG` is monotone in the height (`thinBundleG_mono_T`), so the demand is worst at
  the window's TOP `Tann = X`;
* `M_s(j) = ⌈2B_j⌉₊ ≥ B_j`, so it suffices to clear the window BOTTOM `B_j`.

What is left — `thinBundleG X VJ … · X^{1−2η} ≤ B_j` — is the scoper's door-pin margin
(≈ 7 orders at `P = Q = ⌈P₈₃⌉₊`, where `B_j ≈ X_d/P` beats `X^{5/6}` by the whole gap between
`e^{−(log X)^{1−θ}}` and `X^{−1/6}`).  It rides as the named hypothesis `hpin`; the numerals
are derived context, not Lean content. -/

/-- **`thinBundleG` is monotone in the height.**  The only `T`-dependence is
`exp(2·(log T/log P_j)·loglog T)`, a product of two nonnegative increasing factors. -/
lemma thinBundleG_mono_T {VJ Hj T T' : ℝ} {Pj Qj : ℕ}
    (hPj1 : 1 < (Pj : ℝ)) (hT : Real.exp 1 ≤ T) (hTT : T ≤ T') :
    thinBundleG T VJ Hj Pj Qj ≤ thinBundleG T' VJ Hj Pj Qj := by
  have hlogPj : 0 < Real.log (Pj : ℝ) := Real.log_pos hPj1
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hT'0 : (0 : ℝ) < T' := lt_of_lt_of_le hT0 hTT
  have hlogT : (1 : ℝ) ≤ Real.log T := (Real.le_log_iff_exp_le hT0).mpr hT
  have hlogTT : Real.log T ≤ Real.log T' := Real.log_le_log hT0 hTT
  have hll : Real.log (Real.log T) ≤ Real.log (Real.log T') :=
    Real.log_le_log (by linarith) hlogTT
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log T) := Real.log_nonneg hlogT
  have hq0 : (0 : ℝ) ≤ Real.log T / Real.log (Pj : ℝ) := by positivity
  have hqq : Real.log T / Real.log (Pj : ℝ) ≤ Real.log T' / Real.log (Pj : ℝ) := by
    exact div_le_div_of_nonneg_right hlogTT hlogPj.le
  have hprod : 2 * (Real.log T / Real.log (Pj : ℝ)) * Real.log (Real.log T)
      ≤ 2 * (Real.log T' / Real.log (Pj : ℝ)) * Real.log (Real.log T') := by
    nlinarith
  have hexp := Real.exp_le_exp.mpr hprod
  rw [thinBundleG, thinBundleG]
  have hVJ0 : (0 : ℝ) ≤ 840 * VJ ^ 2 := by positivity
  have hcard : (0 : ℝ) ≤ ((ramI Hj Pj Qj).card : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hexp hVJ0
  exact mul_le_mul_of_nonneg_left (by linarith) hcard

/-- **FIELD 2 AT THE WITNESS** (`thin_at_witness`).  `A2Frame3.thin`, from the single
door-pin inequality at the window's top. -/
theorem thin_at_witness {X h VJ Hj η : ℝ} {H : ℝ} {Pj Qj Xd P Q : ℕ}
    (hX1 : (0 : ℝ) < X) (hPj1 : 1 < (Pj : ℝ))
    (hTbot : Real.exp 1 ≤ 2 * (X / h))
    (hpin : ∀ j ∈ ramI H P Q,
      thinBundleG X VJ Hj Pj Qj * X ^ (1 - 2 * η) ≤ ramRbot H Xd j) :
    ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
      ∀ j ∈ ramI H P Q,
        thinBundleG Tann VJ Hj Pj Qj * X ^ (1 - 2 * η) ≤ ((witMs H Xd j : ℕ) : ℝ) := by
  intro Tann hbot htop j hj
  have hmono := thinBundleG_mono_T (Qj := Qj) (VJ := VJ) (Hj := Hj) hPj1
    (le_trans hTbot hbot) htop
  have hx : (0 : ℝ) ≤ X ^ (1 - 2 * η) := Real.rpow_nonneg hX1.le _
  have h1 := mul_le_mul_of_nonneg_right hmono hx
  have h2 := hpin j hj
  have h3 : ramRbot H Xd j ≤ ((witMs H Xd j : ℕ) : ℝ) := by
    have hc : 2 * ramRbot H Xd j ≤ ((witMs H Xd j : ℕ) : ℝ) := by
      rw [witMs]; exact Nat.le_ceil _
    have := ramRbot_nonneg H Xd j
    linarith
  linarith

/-! ## §6 — FIELD 3: `ksGate`, and the calibration `δ' = (log X)^{−3}`

The kernel/short-interval gate is pure `rpow` arithmetic once `δ'` is pinned.  At
`δ' = (log X)^{−3}` (so `δ'² = (log X)^{−6}`) the left side is

  `32·20512·(log X)^{2+2θ−6}·(1 + log 2X) = 656384·(log X)^{2θ−4}·(1 + log 2X)`,

and the gate becomes the single threshold `656384(1 + log 2X) ≤ (log X)^{4−3θ}` — SiegelBand's
threshold genre.  With `θ₂₉₃ ≈ 1/294` that is `(log X)^{≈2.99}` against `≈ log X`: roomy at
any door scale, and stated symbolically. -/

/-- **FIELD 3** (`ksGate_at_witness`).  `A2Frame3.ksGate` at `δ'² ≤ (log X)^{−6}`, from one
named threshold. -/
theorem ksGate_at_witness {X δ' : ℝ} (hL0 : 0 < Real.log X)
    (hδ0 : 0 ≤ 1 + Real.log (2 * X))
    (hδ : δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ)))
    (hthr : 656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) :
    32 * (Real.log X) ^ (2 + 2 * theta293)
      * (20512 * δ' ^ 2 * (1 + Real.log (2 * X))) ≤ (Real.log X) ^ (-theta293) := by
  have hrp : (0 : ℝ) < (Real.log X) ^ (2 + 2 * theta293) := Real.rpow_pos_of_pos hL0 _
  have hrp2 : (0 : ℝ) < (Real.log X) ^ (2 * theta293 - 4) := Real.rpow_pos_of_pos hL0 _
  -- replace `δ'²` by the pin
  have hstep : 32 * (Real.log X) ^ (2 + 2 * theta293)
        * (20512 * δ' ^ 2 * (1 + Real.log (2 * X)))
      ≤ 32 * (Real.log X) ^ (2 + 2 * theta293)
        * (20512 * (Real.log X) ^ (-(6 : ℝ)) * (1 + Real.log (2 * X))) := by
    have h1 : 20512 * δ' ^ 2 * (1 + Real.log (2 * X))
        ≤ 20512 * (Real.log X) ^ (-(6 : ℝ)) * (1 + Real.log (2 * X)) := by
      nlinarith
    nlinarith
  refine hstep.trans ?_
  -- collapse the two `rpow`s, then apply the threshold
  have hcol : (Real.log X) ^ (2 + 2 * theta293) * (Real.log X) ^ (-(6 : ℝ))
      = (Real.log X) ^ (2 * theta293 - 4) := by
    rw [← Real.rpow_add hL0]; ring_nf
  have hexit : (Real.log X) ^ (4 - 3 * theta293) * (Real.log X) ^ (2 * theta293 - 4)
      = (Real.log X) ^ (-theta293) := by
    rw [← Real.rpow_add hL0]; ring_nf
  calc 32 * (Real.log X) ^ (2 + 2 * theta293)
        * (20512 * (Real.log X) ^ (-(6 : ℝ)) * (1 + Real.log (2 * X)))
      = 656384 * (1 + Real.log (2 * X))
          * ((Real.log X) ^ (2 + 2 * theta293) * (Real.log X) ^ (-(6 : ℝ))) := by ring
    _ = 656384 * (1 + Real.log (2 * X)) * (Real.log X) ^ (2 * theta293 - 4) := by rw [hcol]
    _ ≤ (Real.log X) ^ (4 - 3 * theta293) * (Real.log X) ^ (2 * theta293 - 4) :=
        mul_le_mul_of_nonneg_right hthr hrp2.le
    _ = (Real.log X) ^ (-theta293) := hexit

/-- **THE CALIBRATION AT THE WITNESS** (`calibration_at_witness`).  `V = (log X)^3`,
`δ' = V⁻¹ = (log X)^{−3}` discharges the row's three `V`-binders `hV1`/`hVδ`/`hlogV`
(`a2Rows_of_capfree3`) AND the `δ'²` input of `ksGate_at_witness`, at one stroke. -/
theorem calibration_at_witness {X L : ℝ} (hLe : Real.exp 1 ≤ Real.log X)
    (hLX : Real.log X ≤ L) :
    (1 : ℝ) ≤ (Real.log X) ^ (3 : ℝ) ∧
      ((Real.log X) ^ (3 : ℝ))⁻¹ ≤ (Real.log X) ^ (-(3 : ℝ)) ∧
      Real.log ((Real.log X) ^ (3 : ℝ)) ≤ 100 * Real.log L ∧
      ((Real.log X) ^ (-(3 : ℝ))) ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ)) := by
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hL1 : (1 : ℝ) ≤ Real.log X := le_trans he1 hLe
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  refine ⟨Real.one_le_rpow hL1 (by norm_num), ?_, ?_, ?_⟩
  · rw [← Real.rpow_neg_one ((Real.log X) ^ (3 : ℝ)), ← Real.rpow_mul hL0.le]
    norm_num
  · -- `log((log X)^3) = 3·loglog X ≤ log L ≤ 100 log L`
    rw [Real.log_rpow hL0]
    have hll : Real.log (Real.log X) ≤ Real.log L := Real.log_le_log hL0 hLX
    have hll0 : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hL1
    linarith
  · rw [← Real.rpow_natCast ((Real.log X) ^ (-(3 : ℝ))) 2, ← Real.rpow_mul hL0.le]
    norm_num

/-! ## §7 — THE `box` DATUM: `T*₂(M_j, log M_j) ≤ 2X`

`a2Frame3_satisfiable_partial` needs this one arithmetic fact to discharge the `box` field
(the R2 repair's payload).  `T*₂` is SUB-polynomial — `log T*₂(Y) = (log Y)^{2/5} +
(log Y)^{3/5}` (`PinFamily.log_Tstar2_self`) — so it clears `X` itself, let alone `2X`, at
any scale where `2(log X)^{3/5} ≤ log X`. -/

/-- **`T*₂(X, log X) ≤ X`.**  The sub-polynomial growth, made explicit. -/
theorem Tstar2_le_self {X : ℝ} (hX : pin2Gate ≤ X)
    (hthr : 2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) :
    Tstar2 X (Real.log X) ≤ X := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le pin2Gate_pos hX
  have hLX : (32768 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 32768]
    exact Real.log_le_log (Real.exp_pos _) (by rwa [pin2Gate] at hX)
  have h2535 : (Real.log X) ^ ((2 : ℝ) / 5) ≤ (Real.log X) ^ ((3 : ℝ) / 5) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hlogT : Real.log (Tstar2 X (Real.log X)) ≤ Real.log X := by
    rw [log_Tstar2_self hX]; linarith
  have hT0 : (0 : ℝ) < Tstar2 X (Real.log X) := Tstar2_pos hX0
  calc Tstar2 X (Real.log X) = Real.exp (Real.log (Tstar2 X (Real.log X))) :=
        (Real.exp_log hT0).symm
    _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr hlogT
    _ = X := Real.exp_log hX0

/-- **THE `box` DATUM AT THE WITNESS** (`Tstar2_box_at_witness`).  `T*₂(M_j, log M_j) ≤ 2X`
for every `j ∈ ramI`, from `M_j ≤ X` (C15) and the `pin2Gate` floor the row already carries
(`a2Rows_of_capfree3`'s `hMtpin`). -/
theorem Tstar2_box_at_witness {X : ℝ} {H : ℝ} {Xd P Q : ℕ}
    (hXthr : 2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X)
    (hMtpin : ∀ j ∈ ramI H P Q, pin2Gate ≤ ((witMt H Xd j : ℕ) : ℝ))
    (hMtX : ∀ j ∈ ramI H P Q, ((witMt H Xd j : ℕ) : ℝ) ≤ X) :
    ∀ j ∈ ramI H P Q,
      Tstar2 ((witMt H Xd j : ℕ) : ℝ) (Real.log ((witMt H Xd j : ℕ) : ℝ)) ≤ 2 * X := by
  intro j hj
  have hX : pin2Gate ≤ X := le_trans (hMtpin j hj) (hMtX j hj)
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le pin2Gate_pos hX
  exact le_trans (le_trans (Tstar2_mono (hMtpin j hj) (hMtX j hj)) (Tstar2_le_self hX hXthr))
    (by linarith)

/-! ## §8 — FIELD 4: `err` (the moment route)

The factor-3 split `RamareWindows.ramErr_moment_split`, assembled by
`USetResiduals.E_priced_row_scale`:

  `∫_{−T}^{T} ‖ramErr‖² ≤ 3·(720(T/X+1)/H + (2T+20N)·Σ_{n≤N}‖ramP2coeff‖²/n²)`.

Three things fill its slots:

* **the `N = 2X_d` pin** — `E_priced`'s `hN2 : N ≤ 2X_d` against the row's `2X_d ≤ N`;
* **the three datum binders** REPAIR-REF named — the coefficient law on `[P,Q]`, `hwin`, and
  the `blockOmega` support pin;
* **the `p²`-mass stone**.  REPAIR-REF priced this as build-from-scratch ("no landed bound at
  all").  IT IS LANDED: `SeamCalibrationK.ramP2mass_direct` gives

    `Σ_{n≤N} ‖ramP2coeff N P Q a b c n‖²/n² ≤ 16·log₂(2X_d)/(X_d·P)`,

  the `C·D/(P·X_d)` grade, with the fibre multiplicity bounded honestly by
  `D = ω(n) ≤ log₂(2X_d)` (`fiber_card_le_omega`, `2^{ω(n)} ≤ n ≤ 2X_d`) and the `Σf` factor
  by `8/P`.  Nothing new was needed here. -/

/-- **THE `EP2` SLOT AT THE WITNESS** — the `p²`-mass row, evaluated once at the window's
top so that the frame's `EP2` is a CONSTANT (the field demands one `EP2` for all heights).

**THE `4/3` INFLATION** (⟦THE WALL⟧'s rewire — `M4ErrRewire`).  The `hwin`-free route pays
the four-row split's Cauchy–Schwarz prefactor `4` where `USetResiduals.E_priced` paid `3`,
while `A2Frame3.err`'s right-hand side is byte-unchanged; the `EP2` slot absorbs the ratio
(`M4ErrRewire.err_grade_fit` at `E = (4/3)·E′`).  The SEAM half needs no inflation —
`RamareMR.seam_rows_grade` collapses BOTH MR windows to `520`, and `4·520 = 2080 ≤ 2160 =
3·720`.  The four sites carrying `witEP2 … ≤ EP2` (`err_at_witness`, `a2Frame3_witness`,
`M4MeanSq.m4_meansq_per_chi_gen`, `M4MeanSq.m4_meansq_or_trivial`) therefore state the same
TEXT and a strictly stronger DEMAND; each is a named binder, threaded and never derived, so
the strengthening is silent by construction and paid at the door (`12·EP2 ≤ (log X)^{−θ}`
still clears — the row is `≍ log₂(2X)/P` at `P ≥ P₈₃`, super-polylog). -/
noncomputable def witEP2 (X : ℝ) (N Xd P : ℕ) : ℝ :=
  (4 / 3) * ((2 * X + 20 * (N : ℝ))
    * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))))

/-- The `p²` row itself, at the window's top — `witEP2` is `(4/3)·witEP2raw`. -/
noncomputable def witEP2raw (X : ℝ) (N Xd P : ℕ) : ℝ :=
  (2 * X + 20 * (N : ℝ)) * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))

lemma witEP2raw_nonneg {X : ℝ} {N Xd P : ℕ} (hX0 : 0 ≤ X) (hXd1 : 1 ≤ Xd) :
    0 ≤ witEP2raw X N Xd P := by
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  rw [witEP2raw]
  have h1 : (0 : ℝ) ≤ 2 * X + 20 * (N : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)) :=
    div_nonneg (by linarith) (by positivity)
  exact mul_nonneg h1 h2

/-- `witEP2 = (4/3)·witEP2raw` — the inflation, as an identity. -/
lemma witEP2_eq (X : ℝ) (N Xd P : ℕ) : witEP2 X N Xd P = (4 / 3) * witEP2raw X N Xd P := rfl

lemma witEP2_nonneg {X : ℝ} {N Xd P : ℕ} (hX0 : 0 ≤ X) (hXd1 : 1 ≤ Xd) :
    0 ≤ witEP2 X N Xd P := by
  rw [witEP2_eq]
  have := witEP2raw_nonneg (X := X) (N := N) (Xd := Xd) (P := P) hX0 hXd1
  linarith

/-- **THE INFLATED ROW, AT THE TWO PINS.**  At `X_d = X`, `N = 2X` (`M4MeanSq`'s forced
pins) the `EP2` slot is a clean `1/P` row: `(2X + 40X)·16·log₂(2X)/(X·P) = 672·log₂(2X)/P`,
and the `4/3` inflation carries it to `896·log₂(2X)/P`. -/
theorem witEP2_eval {X : ℝ} {N Xd P : ℕ} (hXd : (Xd : ℝ) = X) (hN : (N : ℝ) = 2 * X)
    (hX0 : 0 < X) (hP0 : (0 : ℝ) < (P : ℝ)) :
    witEP2 X N Xd P = 896 * Real.logb 2 (2 * X) / (P : ℝ) := by
  rw [witEP2_eq, witEP2raw, hN, hXd]
  field_simp
  ring

/-- **THE `12·EP2` GATE SURVIVES THE `4/3` BUMP** (`witEP2_gate`).  `A2Frame3`'s Perron gate
`12·EP2 ≤ (log X)^{−θ₂₉₃}` is a NAMED binder of the capstone, so the inflation of `witEP2`
strengthens what a consumer must supply.  It costs nothing: at the two pins the inflated row
is `896·log₂(2X)/P`, `USetResiduals.EP2_gate_of_row` fires at
`Kmass = 896·log₂(2X)`, and its front-constant demand is the single threshold

  `10752·log₂(2X) ≤ (log X)²`

(the refuter's `log X ≥ 1.6·10⁴` grade, carried SYMBOLICALLY per law #253).  `P₈₃`'s four
polylog powers (`USetResiduals.P83_ge_polylog`) then beat the two spent, so the gate clears
with `(log X)^{2−5θ₂₉₃}` to spare — exactly as before the bump. -/
theorem witEP2_gate {X EP2 : ℝ} {N Xd P : ℕ}
    (hXd : (Xd : ℝ) = X) (hN : (N : ℝ) = 2 * X) (hX0 : 0 < X)
    (hL : 256 ≤ Real.log X) (hP83 : P83 X theta293 ≤ (P : ℝ))
    (hEP2 : EP2 ≤ witEP2 X N Xd P)
    (hthr : 10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) :
    12 * EP2 ≤ (Real.log X) ^ (-theta293) := by
  have hP0 : (0 : ℝ) < (P : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hP83
  rw [witEP2_eval hXd hN hX0 hP0] at hEP2
  exact EP2_gate_of_row (Kmass := 896 * Real.logb 2 (2 * X)) hL hP83 hEP2 (by linarith)

/-- **FIELD 4 AT THE WITNESS** (`err_at_witness`).  `A2Frame3.err`, for every admissible
height, at `EP2 = witEP2`. -/
theorem err_at_witness {X h EP2 : ℝ} {N Xd P : ℕ} {b a cf : ℕ → ℂ}
    (hH : 2 ≤ H83 X theta293)
    (hXd1 : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hN2 : (N : ℝ) ≤ 2 * (Xd : ℝ))
    (hHX : H83 X theta293 ≤ (Xd : ℝ)) (hP : 1 ≤ P)
    (hX0 : 0 < X) (hh0 : 0 < h) (hXd : X ≤ (Xd : ℝ))
    -- the three datum binders (REPAIR-REF's list) + the norm caps
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ P → ¬ p ∣ m → a (p * m) = b m * cf p)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖cf p‖ ≤ 1)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ P → cf p * b m ≠ 0 →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ))
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P P n)
    (hEP2 : witEP2 X N Xd P ≤ EP2) :
    ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
      (∫ t in (-Tann)..Tann, ‖ramErr (H83 X theta293) N Xd P P a b cf t‖ ^ 2)
        ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) := by
  intro Tann hbot htop
  have hT0 : (0 : ℝ) ≤ Tann := le_trans (by positivity) hbot
  -- `ramP2mass_direct`'s window pin is the ℕ-shape of `E_priced`'s
  have hwinN : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ P → cf p * b m ≠ 0 →
      Xd ≤ p * m ∧ p * m ≤ 2 * Xd := by
    intro p m hp h1 h2 h3
    obtain ⟨u, v⟩ := hwin p m hp h1 h2 h3
    have hu : ((Xd : ℕ) : ℝ) ≤ ((p * m : ℕ) : ℝ) := by push_cast; linarith
    have hv : ((p * m : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by push_cast; linarith
    exact ⟨by exact_mod_cast hu, by exact_mod_cast hv⟩
  have hmass := ramP2mass_direct N P P Xd hXd1 hP a b cf ha hb hc hasupp hwinN
  have hmass0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N,
      ‖ramP2coeff N P P a b cf n‖ ^ 2 / (n : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun n _ => by positivity)
  have hpriced := E_priced_row_scale (H83 X theta293) hH N Xd P P hXd1 hN hN2 hHX hP
    a b cf hcoef hb hc hwin hsupp Tann X hT0 hX0 hXd
  refine hpriced.trans ?_
  have hfactor : (2 * Tann + 20 * (N : ℝ)) ≤ 2 * X + 20 * (N : ℝ) := by linarith
  have hfac0 : (0 : ℝ) ≤ 2 * Tann + 20 * (N : ℝ) := by positivity
  have hstep : (2 * Tann + 20 * (N : ℝ))
      * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P P a b cf n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ witEP2 X N Xd P := by
    rw [witEP2_eq, witEP2raw]
    have hXd1R : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
    have hLb : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
      Real.logb_nonneg (by norm_num) (by linarith)
    have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
    have htop0 : (0 : ℝ) ≤ (2 * X + 20 * (N : ℝ))
        * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))) :=
      mul_nonneg (by positivity) (div_nonneg (by linarith) (by positivity))
    calc (2 * Tann + 20 * (N : ℝ))
          * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P P a b cf n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ (2 * X + 20 * (N : ℝ))
          * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P P a b cf n‖ ^ 2 / (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hfactor hmass0
      _ ≤ (2 * X + 20 * (N : ℝ))
          * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))) :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
      _ ≤ 4 / 3 * ((2 * X + 20 * (N : ℝ))
          * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))) := by linarith
  have hH0 : (0 : ℝ) < H83 X theta293 := by linarith
  have : (2 * Tann + 20 * (N : ℝ))
      * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P P a b cf n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ EP2 := le_trans hstep hEP2
  linarith

/-! ## §8′ — FIELD 4, REWIRED: ⟦THE WALL⟧'s `hwin`-FREE SUPPLY

`err_at_witness` above reaches the field through `USetResiduals.E_priced_row_scale`, whose
`p²`-mass slot is `SeamCalibrationK.ramP2mass_direct` — and that stone reads the JOINT
SUPPORT law

  `hwin : ∀ p m, p prime → P ≤ p → p ≤ Q → cf p · b m ≠ 0 → X_d ≤ pm ≤ 2X_d`.

`M4Seam.m4_row_cf_block_eq_zero` is the kernel witness that `hwin` ALONE collapses the
capstone's datum: read at `m = 1` it forces `cf P = 0` at every block prime below the window,
so the binder set could host no `P`-exact sieved datum whatever.  Relativizing `hwin` is
vacuous (`SeamRowWindowed` §1: it is a joint-support claim, not a pointwise law).

The rewire moves the window OFF the hypothesis and INTO the index set — MR's own cofactor
range `ramHonMR N X p = {m : X ≤ pm ≤ 2X}` — which is what `RamareMR` already did on the
identity side and `SeamRowWindowed.ramErr_moment_split_mr_windowed` on the moment side.
`M4ErrRewire` supplies the one missing stone (`ramP2massMR_direct`, the sharp `p²` mass at
`ramP2domMR`, `hwin`-free) and the priced row (`E_priced_mr_row_scale`).  The price is the
four-row split's prefactor `4` against `E_priced`'s `3`, absorbed by `witEP2`'s `4/3`
inflation on the `EP2` half and by `520 ≤ 540` on the seam half. -/

/-- **FIELD 4 AT THE WITNESS, `hwin`-FREE** (`err_at_witness_mr`).  `A2Frame3.err` for every
admissible height at `EP2 = witEP2`, through `M4ErrRewire.E_priced_mr_row_scale`.

Against `err_at_witness` the binder list

* **LOSES `hwin` outright** (⟦THE WALL⟧), and
* replaces the unconditional factorization `hcoef` by the relativized `SeamCoefW`
  (`SeamRowWindowed`'s W-1 — satisfiable exactly where the landed one is not,
  `seam_coef_contract_windowed_sat`),

both strict weakenings; the conclusion is `err_at_witness`'s byte for byte, so
`A2Frame3.err` does not move. -/
theorem err_at_witness_mr {X h EP2 : ℝ} {N Xd P Q : ℕ} {b a cf : ℕ → ℂ}
    (hH : 2 ≤ H83 X theta293)
    (hXd1 : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hN2 : (N : ℝ) ≤ 2 * (Xd : ℝ))
    (hHX : H83 X theta293 ≤ (Xd : ℝ)) (hP : 1 ≤ P)
    (hX0 : 0 < X) (hh0 : 0 < h) (hXd : X ≤ (Xd : ℝ))
    -- ⟦the relativized pair — NO `hwin`⟧
    (hcoefW : SeamCoefW Xd P Q a b cf)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖cf p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    -- ⟦R3a — THE TAIL IS PRICED, NOT PINNED⟧ `homega` leaves; the coprime-tail MASS and
    -- its budget line arrive, the `(2X+20N)·M_tail` landing in the ε-graded `EP₂` slot
    (Mtail : ℝ) (hMtail0 : 0 ≤ Mtail)
    (hMtail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail)
    (hEP2 : witEP2 X N Xd P + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * Mtail) ≤ EP2) :
    ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
      (∫ t in (-Tann)..Tann, ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2)
        ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) := by
  intro Tann hbot htop
  have hT0 : (0 : ℝ) ≤ Tann := le_trans (by positivity) hbot
  have hXd1R : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hLb : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hmassnn : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)) :=
    div_nonneg (by linarith) (by positivity)
  -- `E_priced_mr`'s support law is the real-valued shape of the frame's
  have hasuppR : ∀ n : ℕ, a n ≠ 0 → (Xd : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (Xd : ℝ) := by
    intro n hn
    obtain ⟨u, v⟩ := hasupp n hn
    refine ⟨by exact_mod_cast u, ?_⟩
    have hv : ((n : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by exact_mod_cast v
    push_cast at hv
    linarith
  have hpriced := E_priced_mr_row_scale (H83 X theta293) hH N Xd P Q hXd1 hN hN2 hHX hP
    a b cf hcoefW ha hb hc hasuppR Mtail hMtail Tann X hT0 hX0 hXd
  refine hpriced.trans ?_
  -- ⟦THE `EP2` HALF⟧ the `4/3` inflation, at the window's top
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hfactor : (2 * Tann + 20 * (N : ℝ)) ≤ 2 * X + 20 * (N : ℝ) := by linarith
  have hstep : (2 * Tann + 20 * (N : ℝ))
        * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))
      ≤ (2 * X + 20 * (N : ℝ))
        * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))) :=
    mul_le_mul_of_nonneg_right hfactor hmassnn
  have hstept : (2 * Tann + 20 * (N : ℝ)) * Mtail ≤ (2 * X + 20 * (N : ℝ)) * Mtail :=
    mul_le_mul_of_nonneg_right hfactor hMtail0
  rw [witEP2_eq, witEP2raw] at hEP2
  have hE : 4 * ((2 * Tann + 20 * (N : ℝ))
        * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))
      + (2 * Tann + 20 * (N : ℝ)) * Mtail) ≤ 3 * EP2 := by
    linarith
  -- ⟦THE SEAM HALF⟧ `4·520 ≤ 3·720`, with `80·(T/X+1)/H` to spare
  have hH0 : (0 : ℝ) < H83 X theta293 := by linarith
  have hg : (0 : ℝ) ≤ Tann / X + 1 := by positivity
  have hfit := err_grade_fit (g := Tann / X + 1) (H := H83 X theta293)
    (Ep' := (2 * Tann + 20 * (N : ℝ))
        * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))
      + (2 * Tann + 20 * (N : ℝ)) * Mtail) (Ep := EP2) hg hH0 hE
  linarith

/-! ## §8″ — ⟦THE ENDPOINT WALL⟧: the STRICT/FUSED supply

`SeamRowWindowed` §3′ re-cuts the err chain at the STRICT pair law `SeamCoefWS` — the
factorization asked only STRICTLY above the dyadic bottom, which is exactly where the door's
HALF-OPEN cut agrees with its datum — and pays the released endpoint cofactors inside the
`p²` row (the fused filter `p ∣ m ∨ p·m = X`).  The split stays at FOUR rows, so `witEP2` and
its `896`/`10752` numerals do not move; the whole price is the named `M4ErrRewire.endMass`
riding as a SEPARATE `hEP2` summand, exactly as ⟦R3a⟧'s `Mtail` does. -/

/-- **FIELD 4 AT THE WITNESS, STRICT + FUSED** (`err_at_witness_mr_end`).  `err_at_witness_mr`
with `hcoefW` weakened to `hcoefWS` and one extra `hEP2` summand.  The conclusion is
byte-identical, so `A2Frame3.err` does not move. -/
theorem err_at_witness_mr_end {X h EP2 : ℝ} {N Xd P Q : ℕ} {b a cf : ℕ → ℂ}
    (hH : 2 ≤ H83 X theta293)
    (hXd1 : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hN2 : (N : ℝ) ≤ 2 * (Xd : ℝ))
    (hHX : H83 X theta293 ≤ (Xd : ℝ)) (hP : 1 ≤ P)
    (hX0 : 0 < X) (hh0 : 0 < h) (hXd : X ≤ (Xd : ℝ))
    -- ⟦the STRICT pair — no endpoint obligation⟧
    (hcoefWS : SeamCoefWS Xd P Q a b cf)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖cf p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (Mtail : ℝ) (hMtail0 : 0 ≤ Mtail)
    (hMtail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail)
    (hEP2 : witEP2 X N Xd P + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * Mtail)
        + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * endMass Xd) ≤ EP2) :
    ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
      (∫ t in (-Tann)..Tann, ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2)
        ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) := by
  intro Tann hbot htop
  have hT0 : (0 : ℝ) ≤ Tann := le_trans (by positivity) hbot
  have hXd1R : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hLb : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hmassnn : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)) :=
    div_nonneg (by linarith) (by positivity)
  have hasuppR : ∀ n : ℕ, a n ≠ 0 → (Xd : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (Xd : ℝ) := by
    intro n hn
    obtain ⟨u, v⟩ := hasupp n hn
    refine ⟨by exact_mod_cast u, ?_⟩
    have hv : ((n : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by exact_mod_cast v
    push_cast at hv
    linarith
  have hpriced := E_priced_mr_row_scale_end (H83 X theta293) hH N Xd P Q hXd1 hN hN2 hHX hP
    a b cf hcoefWS ha hb hc hasuppR Mtail hMtail Tann X hT0 hX0 hXd
  refine hpriced.trans ?_
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hfactor : (2 * Tann + 20 * (N : ℝ)) ≤ 2 * X + 20 * (N : ℝ) := by linarith
  have hstep : (2 * Tann + 20 * (N : ℝ))
        * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))
      ≤ (2 * X + 20 * (N : ℝ))
        * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ))) :=
    mul_le_mul_of_nonneg_right hfactor hmassnn
  have hstepe : (2 * Tann + 20 * (N : ℝ)) * endMass Xd
      ≤ (2 * X + 20 * (N : ℝ)) * endMass Xd :=
    mul_le_mul_of_nonneg_right hfactor (endMass_nonneg Xd)
  have hstept : (2 * Tann + 20 * (N : ℝ)) * Mtail ≤ (2 * X + 20 * (N : ℝ)) * Mtail :=
    mul_le_mul_of_nonneg_right hfactor hMtail0
  rw [witEP2_eq, witEP2raw] at hEP2
  have hE : 4 * ((2 * Tann + 20 * (N : ℝ))
        * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))
      + (2 * Tann + 20 * (N : ℝ)) * endMass Xd
      + (2 * Tann + 20 * (N : ℝ)) * Mtail) ≤ 3 * EP2 := by
    linarith
  have hH0 : (0 : ℝ) < H83 X theta293 := by linarith
  have hg : (0 : ℝ) ≤ Tann / X + 1 := by positivity
  have hfit := err_grade_fit (g := Tann / X + 1) (H := H83 X theta293)
    (Ep' := (2 * Tann + 20 * (N : ℝ))
        * (16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)))
      + (2 * Tann + 20 * (N : ℝ)) * endMass Xd
      + (2 * Tann + 20 * (N : ℝ)) * Mtail) (Ep := EP2) hg hH0 hE
  linarith

/-! ## §9 — THE ASSEMBLY: `a2Frame3_witness`

`a2Frame3_satisfiable_partial`'s seven, composed with §4/§5/§6/§8's four.  The result is the
first inhabitant of `A2Frame3` — hence the first model of `TLBlockGates34` anywhere, and the
object `ThmA2Rows.a2Rows_of_capfree3` was waiting for.

**THE NAMED-HYPOTHESIS LIST IS M4-5's CHECKLIST.**  Every binder below is either

* a scale gate the M4-5 consumer clears at door numerology (all the `(log X)`-shaped ones —
  the scoper's `loglog X ≥ 996.4` and `≥ 6412.6` are what "clears" means, and the ε-window
  already forces the stronger of the two), or
* a datum the S8 supply hands over (`hcoefW`, `hasupp`, `hsupp`, the norm caps — `hwin` is
  no longer among them, see §8′), or
* an OPAQUE CAPSTONE EXISTENTIAL's gate (`hcqgate` — flags K6): `cq₁` is bound by
  `hUG34_supplied`'s `∃`, so this binder must be instantiated INSIDE that existential's
  scope, never before it.

Only `hhceil` — the `h`-ceiling — is structural: it constrains the dyadic family's window
bottom and is not implied by anything else here. -/

/-- **THE `A2Frame3` WITNESS** (`a2Frame3_witness`).  `A2Frame3` at

  `P = Q = ` the block pin,  `kk = witKk`, `Mt = witMt`, `Ms = witMs`,

with all eleven fields discharged.  See the section docstring for how to read the binder
list. -/
theorem a2Frame3_witness
    {b cf a : ℕ → ℂ} {N Xd P Q A G M Jb : ℕ}
    {H1 X h δ' VJ L η Cb Rrad EP2 cq T₀ : ℝ}
    -- ⟦the scale page⟧
    (hX0 : 0 < X) (hh0 : 0 < h) (hLX0 : 0 < Real.log X) (hLXL : Real.log X ≤ L)
    (hXd1 : 1 ≤ Xd) (hXdX : X ≤ (Xd : ℝ))
    -- ⟦the window's endpoints — `a2Frame3_satisfiable_partial`'s own⟧
    (hTann : TannGate X (2 * (X / h)))
    (hceil5 : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hT₀le : T₀ ≤ 2 * (X / h))
    (hTbot : Real.exp 1 ≤ 2 * (X / h))
    -- ⟦THE BAND `h`-CEILING (K8, law #253) — carried, never derived⟧
    (hhceil : Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X)
    -- ⟦the block band: C2–C6 at the sandwich⟧
    (hH2 : 2 ≤ H83 X theta293) (hP3 : 3 ≤ P) (hlogP2 : 2 ≤ Real.log (P : ℝ))
    (hQ1 : 1 ≤ Q) (hPQ : P ≤ Q) (hcq0 : 0 ≤ cq)
    (hQbot : (Q : ℝ) ≤ 2 * (X / h))
    (hQlog : Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X))
    (hQL : Real.log (Q : ℝ) ≤ L)
    (hcqgate : 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2)
    -- ⟦the window floors: C7–C17⟧
    (hW4 : ∀ j ∈ ramI (H83 X theta293) P Q, 4 ≤ ramRbot (H83 X theta293) Xd j)
    (hkth : ∀ j ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd j)
    (hMN : 2 * Xd ≤ N)
    (hMtX : ∀ j ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd j ≤ X)
    (hC16 : ∀ j ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X) - Real.log (Real.log (ramRbot (H83 X theta293) Xd j - 1))
        ≤ 32 * theta293 * Real.log (Real.log X))
    (hRrad0 : 0 < Rrad)
    (hRradW : ∀ j ∈ ramI (H83 X theta293) P Q,
      Rrad ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd j)
    -- ⟦thin: the door-pin margin at the window's TOP⟧
    (hPj1 : 1 < ((calP A G Jb : ℕ) : ℝ))
    (hthinpin : ∀ j ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb) * X ^ (1 - 2 * η)
        ≤ ramRbot (H83 X theta293) Xd j)
    -- ⟦the box datum⟧
    (hXthr : 2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X)
    (hMtpin : ∀ j ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ))
    -- ⟦ksGate: the calibration and its threshold⟧
    (hδsq : δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ)))
    (hlog2X : 0 ≤ 1 + Real.log (2 * X))
    (hksthr : 656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293))
    -- ⟦err: the S8 datum + the `N = 2X_d` pin + the `EP2` gate — `hwin`-FREE (§8′)⟧
    (hN2 : (N : ℝ) ≤ 2 * (Xd : ℝ)) (hHX : H83 X theta293 ≤ (Xd : ℝ))
    (hcoefW : SeamCoefW Xd P Q a b cf)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖cf p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    -- ⟦R3a⟧ the coprime-tail mass in place of the single-`P` support pin
    (Mtail : ℝ) (hMtail0 : 0 ≤ Mtail)
    (hMtail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail)
    (hEP2 : witEP2 X N Xd P + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * Mtail) ≤ EP2) :
    A2Frame3 b cf a N Xd P Q A G M Jb (witMs (H83 X theta293) Xd)
      (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd) H1 X h δ' VJ L η Cb Rrad
      EP2 cq T₀ := by
  have hH1 : (1 : ℝ) ≤ H83 X theta293 := by linarith
  -- `M_j ≤ X` (C15) — needed again for the `box` datum
  have hMtXle : ∀ j ∈ ramI (H83 X theta293) P Q,
      ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ X := by
    intro j hj
    obtain ⟨-, -, -, -, h5, -⟩ := witness_window_geometry (hW4 j hj)
    have := hMtX j hj
    linarith
  exact a2Frame3_satisfiable_partial hLX0 hTann hceil5 hT₀le hLXL
    (thin_at_witness (Pj := calP A G Jb) (Qj := calQK A G M Jb) hX0 hPj1 hTbot hthinpin)
    (blocks_at_witness hX0 hh0 hH1 hP3 hlogP2 hQ1 hPQ hcq0 hQbot hhceil hQlog hQL hcqgate
      hW4 hkth hMN hMtX hC16 hRrad0 hRradW)
    (Tstar2_box_at_witness hXthr hMtpin hMtXle)
    (ksGate_at_witness hLX0 hlog2X hδsq hksthr)
    (err_at_witness_mr hH2 hXd1 hMN hN2 hHX (by omega) hX0 hh0 hXdX hcoefW ha hb hc
      hasupp Mtail hMtail0 hMtail hEP2)

/-- **THE `A2Frame3` WITNESS, STRICT + FUSED** (`a2Frame3_witness_end`).  `a2Frame3_witness`
with its err field taken from §8″: the pair law weakens to `SeamCoefWS` (no endpoint
obligation on the datum) and the `hEP2` line gains the endpoint summand.  Every other binder,
and the conclusion, are `a2Frame3_witness`'s byte for byte. -/
theorem a2Frame3_witness_end
    {b cf a : ℕ → ℂ} {N Xd P Q A G M Jb : ℕ}
    {H1 X h δ' VJ L η Cb Rrad EP2 cq T₀ : ℝ}
    (hX0 : 0 < X) (hh0 : 0 < h) (hLX0 : 0 < Real.log X) (hLXL : Real.log X ≤ L)
    (hXd1 : 1 ≤ Xd) (hXdX : X ≤ (Xd : ℝ))
    (hTann : TannGate X (2 * (X / h)))
    (hceil5 : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hT₀le : T₀ ≤ 2 * (X / h))
    (hTbot : Real.exp 1 ≤ 2 * (X / h))
    (hhceil : Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X)
    (hH2 : 2 ≤ H83 X theta293) (hP3 : 3 ≤ P) (hlogP2 : 2 ≤ Real.log (P : ℝ))
    (hQ1 : 1 ≤ Q) (hPQ : P ≤ Q) (hcq0 : 0 ≤ cq)
    (hQbot : (Q : ℝ) ≤ 2 * (X / h))
    (hQlog : Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X))
    (hQL : Real.log (Q : ℝ) ≤ L)
    (hcqgate : 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2)
    (hW4 : ∀ j ∈ ramI (H83 X theta293) P Q, 4 ≤ ramRbot (H83 X theta293) Xd j)
    (hkth : ∀ j ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd j)
    (hMN : 2 * Xd ≤ N)
    (hMtX : ∀ j ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd j ≤ X)
    (hC16 : ∀ j ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X) - Real.log (Real.log (ramRbot (H83 X theta293) Xd j - 1))
        ≤ 32 * theta293 * Real.log (Real.log X))
    (hRrad0 : 0 < Rrad)
    (hRradW : ∀ j ∈ ramI (H83 X theta293) P Q,
      Rrad ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd j)
    (hPj1 : 1 < ((calP A G Jb : ℕ) : ℝ))
    (hthinpin : ∀ j ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb) * X ^ (1 - 2 * η)
        ≤ ramRbot (H83 X theta293) Xd j)
    (hXthr : 2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X)
    (hMtpin : ∀ j ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ))
    (hδsq : δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ)))
    (hlog2X : 0 ≤ 1 + Real.log (2 * X))
    (hksthr : 656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293))
    -- ⟦err: the STRICT pair + the `N = 2X_d` pin + the endpoint-augmented `EP2` gate⟧
    (hN2 : (N : ℝ) ≤ 2 * (Xd : ℝ)) (hHX : H83 X theta293 ≤ (Xd : ℝ))
    (hcoefWS : SeamCoefWS Xd P Q a b cf)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖cf p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (Mtail : ℝ) (hMtail0 : 0 ≤ Mtail)
    (hMtail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail)
    (hEP2 : witEP2 X N Xd P + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * Mtail)
        + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * endMass Xd) ≤ EP2) :
    A2Frame3 b cf a N Xd P Q A G M Jb (witMs (H83 X theta293) Xd)
      (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd) H1 X h δ' VJ L η Cb Rrad
      EP2 cq T₀ := by
  have hH1 : (1 : ℝ) ≤ H83 X theta293 := by linarith
  have hMtXle : ∀ j ∈ ramI (H83 X theta293) P Q,
      ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ X := by
    intro j hj
    obtain ⟨-, -, -, -, h5, -⟩ := witness_window_geometry (hW4 j hj)
    have := hMtX j hj
    linarith
  exact a2Frame3_satisfiable_partial hLX0 hTann hceil5 hT₀le hLXL
    (thin_at_witness (Pj := calP A G Jb) (Qj := calQK A G M Jb) hX0 hPj1 hTbot hthinpin)
    (blocks_at_witness hX0 hh0 hH1 hP3 hlogP2 hQ1 hPQ hcq0 hQbot hhceil hQlog hQL hcqgate
      hW4 hkth hMN hMtX hC16 hRrad0 hRradW)
    (Tstar2_box_at_witness hXthr hMtpin hMtXle)
    (ksGate_at_witness hLX0 hlog2X hδsq hksthr)
    (err_at_witness_mr_end hH2 hXd1 hMN hN2 hHX (by omega) hX0 hh0 hXdX hcoefWS ha hb hc
      hasupp Mtail hMtail0 hMtail hEP2)

/-! ## §10 — BEYOND THE FRAME: the row's own ladder binders

`a2Rows_of_capfree3` asks for four more things about `Ms`/`m₀` that the frame does not
carry — and they are exactly the trap-7 quartet (`Ms` pushed UP by `thin`, pinned DOWN by
the row's `hMs4`).  At the witness values they all fall out of `5 ≤ B_j`:

  `⌈2B⌉₊ ≤ 2B + 1`  and  `4(⌊B⌋₊ − 1) > 4B − 8`,  so `2B + 1 ≤ 4B − 8` needs only `B ≥ 4.5`.

The collision is therefore NOT tight at the door pin — the thin side asks `M_s ≥
thinBundleG·X^{5/6}` (`thin_at_witness`'s `hpin`), the row side caps it at `≈ 4B_j`, and
`B_j ≈ X_d/P` clears `X^{5/6}` by the whole gap between `e^{−(log X)^{1−θ}}` and `X^{−1/6}`. -/

/-- **THE ROW LADDER AT THE WITNESS** (`row_ladder_at_witness`).
`a2Rows_of_capfree3`'s `hMs`, `hm₀2`, `hm₀`, `hMs4` — all four, from `5 ≤ B_j`. -/
theorem row_ladder_at_witness {H : ℝ} {N Xd P Q : ℕ}
    (hW5 : ∀ j ∈ ramI H P Q, 5 ≤ ramRbot H Xd j) :
    (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (witMs H Xd j)) ∧
      (∀ j ∈ ramI H P Q, 2 ≤ witM0 H Xd j) ∧
      (∀ j ∈ ramI H P Q, ((witM0 H Xd j : ℕ) : ℝ) ≤ ramRbot H Xd j) ∧
      (∀ j ∈ ramI H P Q,
        ((witMs H Xd j : ℕ) : ℝ) ≤ 4 * (((witM0 H Xd j : ℕ) : ℝ) - 1)) :=
  ⟨fun j _ => witMs_range H N Xd j,
   fun j hj => witM0_two_le (by linarith [hW5 j hj]),
   fun j _ => witM0_le H Xd j,
   fun j hj => witMs_le_four_mul (hW5 j hj)⟩

end Salt.MR
