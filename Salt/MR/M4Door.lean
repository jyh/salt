/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Sieve

/-!
# M4-8 — THE DOOR GLUE (`M4Door`)

Source: the campaign freeze `docs/exploration/s9-freeze-0726.md` ⟦AMENDMENT B⟧ row `M4-8`
(:283) — "door glue B3/B4/B6; + HS-6's window-generality dyadic split rides here; + the
door-normalisation `log ω` absorption into `M`"; the wave plan
`docs/exploration/m4-plan-0728.md` (:172); and `docs/blueprints/flags.md`, ⟦THE OVERNIGHT
TRIO⟧ — M4-1's one-block vacuity finding, which NAMES this row's central deliverable.

## What this row owes, and to whom

`M4Sieve.m4_sieve_insert` (M4-1's door exit) is stated with the total complement mass
carried as an abstract `B`.  M4-1's ⟦VACUITY FINDING⟧ (`door_window_not_one_block`,
kernel-checked) shows that `B` **cannot** be supplied by a single sieve block: the door
window `(x/ω, x]` spans a factor `ω ≥ 2`, and `Ioc (x/ω) (x+H) ⊆ Icc X (2X)` is false for
every `X`.  **M4-8 supplies `B`** — by covering the door window with a ladder of blocks,
pricing each with `M4Sieve.m4_sieve_block_mass`, and summing.  That is `m4_door_sieve_mass`,
the named seam, and it is this file's centre of gravity.

## ⟦THE OVERHANG FINDING⟧ (this row's own sharpest result — the sibling of M4-1's)

The cover **cannot be exactly dyadic**.  `m4_sieve_block_mass` prices a block `(a, b]`
through the Fubini double count `sum_window_double_count`, whose window is `(a, b+H]` — the
short windows `(n, n+H]` at `n ≤ b` reach `H` past the block top.  Its sieve-block gate is
therefore `Ioc a (b + H) ⊆ Icc X (2X)` at `X ≤ a`, i.e. `b + H ≤ 2a`.  An exactly dyadic
block has `b = 2a`, so the gate reads `H ≤ 0`: **exact dyadic blocks are unfittable**, the
same failure mode (kernel-true, consumable by nobody) that M4-1 found one level up.

The repair is `doorLadder` (§2): the *H-offset* dyadic ladder

  `X_0 = x`,  `X_{i+1} = (X_i + H + 1) / 2`  (`ℕ`-division),

whose fit `X_i + H ≤ 2·X_{i+1}` is **unconditional** — it is exactly what the rounding-up
`+1` buys — and which still decays dyadically, `X_i ≤ (H+1) + x/2^i`, toward the fixed
point `H+1`.  The count is therefore the dyadic one, `log ω/log 2 + 2` (`doorCount`), and
the endpoint sum is the geometric `∑_i 2^i/x` the freeze names.

## ⟦THE FOUR LOG SCALES⟧ (the trap, pinned glyph by glyph)

1. `log H` — the window scale; `W = (log H)^{12}` lives here (P-2, `B₅ = 12`), and
   `M4Dyadic.dyadCount_logPow_le_numeral`'s `174·loglog H + 2` is a **`log H`** numeral.
   **This file never writes `W`**: the outer cover at depth `W^{10}` is M4-4's object
   (`M4Dyadic`), for the *rescaled outer variable* `y`, and it is a different cover from
   this one.
2. `log X` — the sieve scale; `SieveBlockGate`'s `√log X ≥ 100` and the regularity gate
   live here, one per block, at `X = X_{i+1}`.
3. `log x` — the door's own outer scale; it appears only through `2^{k+1} ≤ x`.
4. **`log ω` — the FOURTH log, the one this row is really about.**  The door normaliser
   `Z = ∑_{n ∈ (x/ω,x]} 1/n` satisfies `Z ∈ [log ω − 1, log ω + 1]`
   (`LogMeasure.harmonic_window_bounds`), and the cover count is `k ≍ log ω/log 2`.  These
   are the SAME `log ω`, and their ratio is an absolute constant — the absorption below.

## ⟦THE `log ω` ABSORPTION INTO `M`⟧ (the freeze's :283 clause, discharged)

`SieveGlue.lean:81–82` defers "the door-normalisation `log ω` absorption into `M` — verified
at instantiation, not here (M4-8)".  Here it is, as arithmetic:

* the cover has `k ≤ log ω/log 2 + 2` blocks (`doorCount_le`);
* the door normaliser has `Z ≥ log ω − 1` (`harmonic_window_bounds`);
* hence `k ≤ 3·Z` for every `ω` with `log ω ≥ 4` (`door_count_le_three_mul_norm`; the ratio
  is decreasing in `log ω`, worst at the floor, where it is `2.59 < 3`).

So the cover's `log ω` is **cancelled** by the normaliser's `log ω`, leaving the absolute
factor `3`; and an absolute factor is exactly what the K-ladder's `M`-gate absorbs
**linearly** (`SieveGlue`'s HS-1 doctrine: the engine's constant costs a linear `M`-rescale
and nothing else).  The gate moves `8C/δ ↦ 24C/δ` and the door grade is `δ/4·H` again.

⟦THE GATE VARIANT, AND WHY⟧ — the per-block primitive taken here is
`M4Sieve.sieve_mass_le_quarter`: **the `δ/4` grade at the freeze's own `8C/δ` gate**, not
`sieve_mass_le_eighth`'s `δ/8` at `16C/δ`.  Reason: the freeze's target grade for the row is
`δ/4·H` (M4-7's budget reads the door bound at `δ/4`), and M4-1's finding is that `8C/δ`
*delivers* `δ/4` (in fact `π²δ/48 ≈ 0.206·δ`) — the `δ/8` in the freeze's prose was
inherited from `eq28_clears_of_M_const`, where the coefficient is `2C`, not `C`.  Taking
`δ/8` here would double the door gate to `48C/δ` after absorption, for a grade the consumer
does not ask for.  The absorption is applied at the per-block grade `δ₀ := δ/3`, so the
door-level gate is `8C/δ₀ = 24C/δ`.

## Conventions

* **Half-open throughout.**  Every window is `Finset.Ioc`: the door's `Ioc (x/ω) x`
  (`logMeasure`'s own carrier), the short windows `Ioc n (n+H)` (`absWindowSum`), the ladder
  blocks `Ioc X_{i+1} X_i`.  The ONE closed interval in the chain is the sieve engine's
  `Icc X (2X)`, and `M4Sieve.card_notMemS_of_subset_Icc` pays its uncovered lattice point
  `m = X` — that `+1`, spread over the `≤ H` short windows that see it, is the `H/X_i` term
  of `m4_sieve_block_mass`, and summing it over the cover is §3's geometric sum (HS-6,
  composed).
* **The count is IN-STATEMENT** (law #253): `doorCount ω = ⌈log ω/log 2⌉₊ + 1`, and every
  covering statement carries `k` explicitly with `(k:ℝ) ≤ log ω/log 2 + 2` as a hypothesis
  or a supplied bound.  No `O(log ω)` prose.
* **`ℕ`-scales.**  Unlike `M4Dyadic` (whose scales are REAL, because its cover meets the
  `thm_a2'` window `[X, 2X]` at real endpoints), the door ladder is `ℕ`-valued: it must feed
  `m4_sieve_block_mass`, whose `a`, `b`, `X` are naturals.  `⌊·⌋` never appears in a scale;
  the only rounding is the `ℕ`-division in `doorLadder`, and the `+1` inside it is the
  rounding-up that buys the fit.
* **One constant.**  `m4_sieve_block_mass`'s `∃ C` is opened ONCE per exit and threaded into
  the `M`-gate (`SieveGlue.sec9_eq28_exit_calFamily`'s discipline).

## What is CITED, never re-derived

`M4Sieve.m4_sieve_block_mass` (the whole sieve leg, `hsieve_of_engine` inside it),
`M4Sieve.norm_absWindowSum_memS_insert` (the insert identity),
`M4Sieve.integral_logMeasure_le_add` (the additive pass-through, Dirac-reduced — so no
integrability side condition anywhere in this file), `ShiftCorr.integral_logMeasure_eq`,
`LogMeasure.harmonic_window_bounds`, `LogMeasure.logMeasure_apply_singleton`,
`M4Dyadic.sum_div_le_of_window` (the `1/n ≍ 1/X′` comparison),
`M4Dyadic.card_shortWindow_le` (the upper half of §1's `±1` band).

## Contents

* §1 THE `logMeasure` MASS PAGE — the singleton mass, the harmonic block comparison, the
  `±1` endpoint band (`2/H` wide), and `Z ≥ log ω − 1`.
* §2 THE DOOR LADDER — `doorLadder`, its unconditional fit, its dyadic envelope, the
  exhaustion `X_k ≤ x/ω`, and the in-statement count `doorCount`.
* §3 THE COVER-SUMMED SIEVE MASS — `m4_door_sieve_mass`, the named seam.
* §4 THE `log ω` ABSORPTION — `door_count_le_three_mul_norm`, `door_mass_normalised_le`.
* §5 THE EXIT — `m4_door_glue`, its two data instantiations, and the inhabitation witness.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE `logMeasure` MASS PAGE

The door's measure is the harmonic one.  This section is its accounting page, read in the
order the glue reads it: the singleton mass, the block comparison `1/n ≍ 1/X′`, the
integer-sum ↔ integral transcription with its `±1` endpoints, and the normaliser's
`log ω`-scale bounds. -/

/-- **THE SINGLETON MASS, in `ℝ`.**  `μ{m} = (1/m)/Z` for `m` in the door window, with
`Z = ∑_{n ∈ (x/ω,x]} 1/n` the normaliser.  (`logMeasure_apply_singleton` is `ℝ≥0∞`-valued;
this is its real shadow, the form every mass computation below is stated in.) -/
theorem logMeasure_singleton_toReal {x ω m : ℕ} (hm : m ∈ Finset.Ioc (x / ω) x) :
    (logMeasure x ω {m}).toReal
      = (m : ℝ)⁻¹ / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
  rw [logMeasure_apply_singleton hm, ENNReal.toReal_div, norm_toReal]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- The door normaliser is positive (the window is nonempty and every weight is `> 0`). -/
theorem door_norm_pos {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) :
    0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
  refine Finset.sum_pos (fun n hn => ?_) (window_nonempty hx hω)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast window_one_le hn
  positivity

/-- **`Z ≥ log ω − 1`** — the lower half of `harmonic_window_bounds`, named because §4's
absorption reads exactly this arm. -/
theorem door_norm_ge {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) :
    Real.log ω - 1 ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
  (harmonic_window_bounds hx hω hωx).1

/-- **`Z ≥ 1`** at `log ω ≥ 2` — the gate `M4Sieve.m4_sieve_insert` asks for, discharged
from the `log ω` scale. -/
theorem door_norm_one_le {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hL : 2 ≤ Real.log ω) : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
  have := door_norm_ge hx hω hωx
  linarith

/-- **THE SHARP NORMALISATION.**  `∫ f dμ ≤ B/Z` whenever the harmonic window sum is `≤ B`.

This is the sharpening of `M4Sieve.integral_logMeasure_le_of_weighted`, which spends `Z` by
the crude `Z⁻¹ ≤ 1`.  The door glue cannot afford that: the cover count is `≍ log ω` and
only `Z ≍ log ω` pays for it (§4).  Proved through `ShiftCorr.integral_logMeasure_eq`, so no
integrability side condition is incurred. -/
theorem integral_logMeasure_le_div {x ω : ℕ} {f : ℕ → ℝ} {B : ℝ}
    (hZ : 0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
    (hB : ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹ ≤ B) :
    (∫ n, f n ∂(logMeasure x ω)) ≤ B / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
  rw [integral_logMeasure_eq, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hB (by positivity)

/-- **`1/n ≍ 1/X′` ON A BLOCK, upper.**  `∑_{n ∈ (a,b]} f(n)/n ≤ (∑ f)/a` — `M4Dyadic`'s §5
comparison, instantiated at a `ℕ` block.  This is how the harmonic weight is spent inside
`m4_sieve_block_mass`. -/
theorem sum_div_Ioc_le {a b : ℕ} (ha : 0 < (a : ℝ)) {f : ℕ → ℝ}
    (hf : ∀ n ∈ Finset.Ioc a b, 0 ≤ f n) :
    ∑ n ∈ Finset.Ioc a b, f n / (n : ℝ) ≤ (∑ n ∈ Finset.Ioc a b, f n) / (a : ℝ) :=
  sum_div_le_of_window ha hf (fun n hn => by exact_mod_cast (Finset.mem_Ioc.mp hn).1)

/-- **`1/n ≍ 1/X′` ON A BLOCK, lower.**  The mass divided by the block top is below the
harmonic sum: the direction that *recovers* mass, kept so the comparison is two-sided (the
dyadic choice's whole content). -/
theorem le_sum_div_Ioc {a b : ℕ} {f : ℕ → ℝ} (hf : ∀ n ∈ Finset.Ioc a b, 0 ≤ f n) :
    (∑ n ∈ Finset.Ioc a b, f n) / (b : ℝ) ≤ ∑ n ∈ Finset.Ioc a b, f n / (n : ℝ) := by
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun n hn => ?_
  have hmem := Finset.mem_Ioc.mp hn
  have hnb : (n : ℝ) ≤ (b : ℝ) := by exact_mod_cast hmem.2
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le a) hmem.1
    exact_mod_cast this
  have := hf n hn
  gcongr

/-- **THE `±1` ENDPOINT, lower half.**  A real half-open window `(x, x+h]` all of whose
integers are present carries at least `h − 1` of them.  (`M4Dyadic.card_shortWindow_le` is
the upper half, `≤ h + 1`; it is cited, not re-proved.) -/
theorem card_shortWindow_ge (s0 : Finset ℕ) {x hlen : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ hlen)
    (hfull : ∀ m : ℕ, x < (m : ℝ) → (m : ℝ) ≤ x + hlen → m ∈ s0) :
    hlen - 1 ≤ ((s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + hlen)).card : ℝ) := by
  have hxh : (0 : ℝ) ≤ x + hlen := by linarith
  have hsub : Finset.Ioc ⌊x⌋₊ ⌊x + hlen⌋₊
      ⊆ s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + hlen) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have h1 : x < (m : ℝ) := (Nat.floor_lt hx).mp hm.1
    have h2 : (m : ℝ) ≤ x + hlen := (Nat.le_floor_iff hxh).mp hm.2
    exact Finset.mem_filter.mpr ⟨hfull m h1 h2, h1, h2⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at hcard
  have hfl : ⌊x⌋₊ ≤ ⌊x + hlen⌋₊ := Nat.floor_mono (by linarith)
  have hcast : ((⌊x + hlen⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)
      ≤ ((s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + hlen)).card : ℝ) := by
    exact_mod_cast hcard
  have hcastR : ((⌊x + hlen⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) = (⌊x + hlen⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) := by
    push_cast [Nat.cast_sub hfl]
    ring
  have hlo : x + hlen < (⌊x + hlen⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hhi : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  rw [hcastR] at hcast
  linarith

/-- **THE `±1` ENDPOINT, both halves.**  `|#{m ∈ (x, x+h]} − h| ≤ 1`. -/
theorem card_shortWindow_abs_sub_le_one (s0 : Finset ℕ) {x hlen : ℝ} (hx : 0 ≤ x)
    (hh : 0 ≤ hlen) (hfull : ∀ m : ℕ, x < (m : ℝ) → (m : ℝ) ≤ x + hlen → m ∈ s0) :
    |((s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + hlen)).card : ℝ) - hlen| ≤ 1 := by
  have hup := card_shortWindow_le s0 hx hh
  have hlo := card_shortWindow_ge s0 hx hh hfull
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **THE `2/H` — the freeze's exact endpoint accounting, derived.**

The integer count of a real window of length `h` sits in the band `[h − 1, h + 1]`; after
the normalisation by `h` that the door's carrier applies (the `1/h` in
`‖(1/h)·shortSum a s₀ x h‖`), the band is `[1 − 1/h, 1 + 1/h]` — of **total width `2/h`**.
That is the freeze's "`±1` each side ⟹ `2/H`": one endpoint at each end of the window, each
costing one lattice point, and the two costs are read against the same `h`.

Nothing is assumed: both arms come from `card_shortWindow_ge` / `card_shortWindow_le`, and
the width is their difference. -/
theorem card_shortWindow_band (s0 : Finset ℕ) {x hlen : ℝ} (hx : 0 ≤ x) (hh : 0 < hlen)
    (hfull : ∀ m : ℕ, x < (m : ℝ) → (m : ℝ) ≤ x + hlen → m ∈ s0) :
    1 - 1 / hlen
        ≤ ((s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + hlen)).card : ℝ) / hlen ∧
      ((s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + hlen)).card : ℝ) / hlen
        ≤ 1 + 1 / hlen ∧
      (1 + 1 / hlen) - (1 - 1 / hlen) = 2 / hlen := by
  have hup := card_shortWindow_le s0 hx hh.le
  have hlo := card_shortWindow_ge s0 hx hh.le hfull
  refine ⟨?_, ?_, by ring⟩
  · rw [le_div_iff₀ hh]
    have he : (1 - 1 / hlen) * hlen = hlen - 1 := by field_simp
    rw [he]
    exact hlo
  · rw [div_le_iff₀ hh]
    have he : (1 + 1 / hlen) * hlen = hlen + 1 := by field_simp
    rw [he]
    exact hup

/-! ## §2 — THE DOOR LADDER

The cover of the door window `(x/ω, x]` that `m4_sieve_block_mass` can actually eat.  See
⟦THE OVERHANG FINDING⟧ in the preamble for why the exactly-dyadic ladder is unusable. -/

/-- **THE DOOR LADDER.**  `X_0 = x`, `X_{i+1} = (X_i + H + 1)/2` (`ℕ`-division) — the dyadic
descent with an `H`-offset and a rounding-up.  The offset is what makes the sieve-block gate
`X_i + H ≤ 2·X_{i+1}` hold *unconditionally* (`doorLadder_fit`); the ladder still halves,
`X_i ≤ (H+1) + x/2^i` (`doorLadder_upper`), toward the fixed point `H + 1`. -/
def doorLadder (x H : ℕ) : ℕ → ℕ
  | 0 => x
  | i + 1 => (doorLadder x H i + H + 1) / 2

@[simp] theorem doorLadder_zero (x H : ℕ) : doorLadder x H 0 = x := rfl

theorem doorLadder_succ (x H i : ℕ) :
    doorLadder x H (i + 1) = (doorLadder x H i + H + 1) / 2 := rfl

/-- **THE FIT — the whole point of the ladder, and it is unconditional.**
`X_i + H ≤ 2·X_{i+1}`: the short windows `(n, n+H]` at `n ≤ X_i` reach `H` past the block
top, and the block's own sieve window `Icc X_{i+1} (2·X_{i+1})` still contains them. -/
theorem doorLadder_fit (x H i : ℕ) :
    doorLadder x H i + H ≤ 2 * doorLadder x H (i + 1) := by
  rw [doorLadder_succ]; omega

/-- The floor `H + 1` is invariant under the descent: once above it, always above it. -/
theorem doorLadder_floor {x H : ℕ} (hx : H + 1 ≤ x) (i : ℕ) : H + 1 ≤ doorLadder x H i := by
  induction i with
  | zero => simpa using hx
  | succ n ih => rw [doorLadder_succ]; omega

/-- The ladder is antitone, one step at a time (above the floor). -/
theorem doorLadder_step_le {x H : ℕ} (hx : H + 1 ≤ x) (i : ℕ) :
    doorLadder x H (i + 1) ≤ doorLadder x H i := by
  have := doorLadder_floor hx i
  rw [doorLadder_succ]; omega

/-- **THE BLOCK'S SIEVE-BLOCK CONTAINMENT** (the gate `m4_sieve_block_mass` demands).
`Ioc X_{i+1} (X_i + H) ⊆ Icc X_{i+1} (2·X_{i+1})` — the half-open door block, widened by the
double count's overhang, inside the engine's closed dyadic block. -/
theorem doorLadder_block_subset (x H i : ℕ) :
    Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i + H)
      ⊆ Finset.Icc (doorLadder x H (i + 1)) (2 * doorLadder x H (i + 1)) := by
  intro n hn
  rw [Finset.mem_Ioc] at hn
  rw [Finset.mem_Icc]
  exact ⟨hn.1.le, le_trans hn.2 (doorLadder_fit x H i)⟩

/-- **THE DYADIC ENVELOPE, upper.**  `X_i ≤ (H + 1) + x/2^i`: the ladder halves the gap to
its fixed point at every step. -/
theorem doorLadder_upper (x H : ℕ) (i : ℕ) :
    (doorLadder x H i : ℝ) ≤ (H : ℝ) + 1 + (x : ℝ) / 2 ^ i := by
  induction i with
  | zero =>
    simp only [doorLadder_zero, pow_zero, div_one]
    have : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    linarith
  | succ n ih =>
    have hne : ((2 : ℝ) ^ n) ≠ 0 := by positivity
    have hcast : (((doorLadder x H n + H + 1) / 2 : ℕ) : ℝ)
        ≤ ((doorLadder x H n + H + 1 : ℕ) : ℝ) / 2 := Nat.cast_div_le
    have hstep : ((doorLadder x H n + H + 1 : ℕ) : ℝ) / 2
        ≤ ((H : ℝ) + 1 + (x : ℝ) / 2 ^ n + (H : ℝ) + 1) / 2 := by
      push_cast
      linarith
    have hfin : ((H : ℝ) + 1 + (x : ℝ) / 2 ^ n + (H : ℝ) + 1) / 2
        = (H : ℝ) + 1 + (x : ℝ) / 2 ^ (n + 1) := by
      rw [pow_succ]
      field_simp
      ring
    rw [doorLadder_succ]
    calc (((doorLadder x H n + H + 1) / 2 : ℕ) : ℝ)
        ≤ ((doorLadder x H n + H + 1 : ℕ) : ℝ) / 2 := hcast
      _ ≤ ((H : ℝ) + 1 + (x : ℝ) / 2 ^ n + (H : ℝ) + 1) / 2 := hstep
      _ = (H : ℝ) + 1 + (x : ℝ) / 2 ^ (n + 1) := hfin

/-- **THE DYADIC ENVELOPE, lower.**  `(x+1)/2^i ≤ X_i + 1`: the ladder never falls below the
dyadic scale (this is what keeps the endpoint sum geometric rather than wild). -/
theorem doorLadder_lower (x H : ℕ) (i : ℕ) :
    ((x : ℝ) + 1) / 2 ^ i ≤ (doorLadder x H i : ℝ) + 1 := by
  induction i with
  | zero => simp
  | succ n ih =>
    have hnat : doorLadder x H n + H + 1 ≤ 2 * doorLadder x H (n + 1) + 1 := by
      rw [doorLadder_succ]; omega
    have hR : (doorLadder x H n : ℝ) + (H : ℝ) + 1 ≤ 2 * (doorLadder x H (n + 1) : ℝ) + 1 := by
      exact_mod_cast hnat
    have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    have hhalf : (doorLadder x H n : ℝ) / 2 ≤ (doorLadder x H (n + 1) : ℝ) := by linarith
    have hpow : (0 : ℝ) < 2 ^ n := by positivity
    have hstep : ((x : ℝ) + 1) / 2 ^ (n + 1) = (((x : ℝ) + 1) / 2 ^ n) / 2 := by
      rw [pow_succ]; field_simp
    rw [hstep]
    linarith

/-- The per-block reciprocal, at the dyadic grade: `1/X_i ≤ 2^{i+1}/x`, under the gate
`2^{i+1} ≤ x` (the ladder has not descended past `1`). -/
theorem doorLadder_inv_le {x H i : ℕ} (hpow : 2 ^ (i + 1) ≤ x) :
    1 / (doorLadder x H i : ℝ) ≤ 2 ^ (i + 1) / (x : ℝ) := by
  have hpowR : (2 : ℝ) ^ (i + 1) ≤ (x : ℝ) := by exact_mod_cast hpow
  have hp0 : (0 : ℝ) < 2 ^ i := by positivity
  have hp1 : (0 : ℝ) < (2 : ℝ) ^ (i + 1) := by positivity
  have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le hp1 hpowR
  have hlow := doorLadder_lower x H i
  have hpsucc : (2 : ℝ) ^ (i + 1) = 2 ^ i * 2 := by rw [pow_succ]
  have ht : (2 : ℝ) ≤ ((x : ℝ) + 1) / 2 ^ i := by
    rw [le_div_iff₀ hp0]
    linarith
  have hsplit : ((x : ℝ) + 1) / 2 ^ (i + 1) = (((x : ℝ) + 1) / 2 ^ i) / 2 := by
    rw [pow_succ]; field_simp
  have hXlow : ((x : ℝ) + 1) / 2 ^ (i + 1) ≤ (doorLadder x H i : ℝ) := by
    rw [hsplit]; linarith
  have hgap : ((x : ℝ) + 1) / 2 ^ (i + 1) - (x : ℝ) / 2 ^ (i + 1) = 1 / 2 ^ (i + 1) := by
    field_simp
    ring
  have hpinv : (0 : ℝ) < 1 / 2 ^ (i + 1) := by positivity
  have hxle : (x : ℝ) / 2 ^ (i + 1) ≤ (doorLadder x H i : ℝ) := by linarith
  have hone : (1 : ℝ) ≤ (x : ℝ) / 2 ^ (i + 1) := by
    rw [le_div_iff₀ hp1]; linarith
  have hXpos : (0 : ℝ) < (doorLadder x H i : ℝ) := by linarith
  rw [div_le_div_iff₀ hXpos hx0]
  rw [div_le_iff₀ hp1] at hxle
  linarith

/-- The geometric endpoint sum: `∑_{i<k} 2^{i+2} ≤ 4·2^k`. -/
theorem sum_range_two_pow_shift_le (k : ℕ) :
    ∑ i ∈ Finset.range k, (2 : ℝ) ^ (i + 2) ≤ 4 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : (2 : ℝ) ^ (n + 2) = 4 * 2 ^ n := by ring
    have h2 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    have h3 : (0 : ℝ) < 2 ^ n := by positivity
    rw [h1, h2]
    linarith

/-- `⌊x/ω⌋ > x/ω − 1` — the `ℕ`-division slack, stated once. -/
theorem natDiv_gt {x ω : ℕ} (hω : 0 < ω) :
    (x : ℝ) / (ω : ℝ) - 1 < ((x / ω : ℕ) : ℝ) := by
  have hωR : (0 : ℝ) < (ω : ℝ) := by exact_mod_cast hω
  have hdm : ω * (x / ω) + x % ω = x := Nat.div_add_mod x ω
  have hmod : x % ω < ω := Nat.mod_lt _ hω
  have hdmR : (ω : ℝ) * ((x / ω : ℕ) : ℝ) + ((x % ω : ℕ) : ℝ) = (x : ℝ) := by
    exact_mod_cast hdm
  have hmodR : ((x % ω : ℕ) : ℝ) < (ω : ℝ) := by exact_mod_cast hmod
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hωR]
  nlinarith

/-- **THE COVER REACHES THE DOOR BOTTOM.**  With `2ω ≤ 2^k` and the (door-trivial) room
`2ω(H+2) ≤ x`, the ladder has descended below `⌊x/ω⌋` by step `k`. -/
theorem doorLadder_reaches {x H ω k : ℕ} (hω : 0 < ω)
    (hpow : 2 * (ω : ℝ) ≤ 2 ^ k) (hbig : 2 * (ω : ℝ) * ((H : ℝ) + 2) ≤ (x : ℝ)) :
    doorLadder x H k ≤ x / ω := by
  have hωR : (0 : ℝ) < (ω : ℝ) := by exact_mod_cast hω
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hpk : (0 : ℝ) < 2 ^ k := by positivity
  have hup := doorLadder_upper x H k
  have hdiv : (x : ℝ) / 2 ^ k ≤ (x : ℝ) / (2 * (ω : ℝ)) := by
    rw [div_le_div_iff₀ hpk (by positivity)]
    nlinarith
  have hHx : (H : ℝ) + 2 ≤ (x : ℝ) / (2 * (ω : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hhalf : (x : ℝ) / (2 * (ω : ℝ)) = ((x : ℝ) / (ω : ℝ)) / 2 := by
    field_simp
  rw [hhalf] at hdiv hHx
  have hkey : (doorLadder x H k : ℝ) ≤ (x : ℝ) / (ω : ℝ) - 1 := by linarith
  have hlt := natDiv_gt (x := x) (ω := ω) hω
  have hfin : (doorLadder x H k : ℝ) < ((x / ω : ℕ) : ℝ) := by linarith
  exact_mod_cast hfin.le

/-! ### The count, in-statement (law #253) -/

/-- **THE DOOR COVER'S COUNT**: `⌈log ω/log 2⌉₊ + 1` blocks — the dyadic count of the door
window's own depth `ω`.  (NOT `M4Dyadic.dyadCount`, whose depth is the outer cover's `W^{10}`
and whose numeral `174·loglog H + 2` is a `log H` object; see ⟦THE FOUR LOG SCALES⟧.) -/
def doorCount (ω : ℕ) : ℕ := ⌈Real.log ω / Real.log 2⌉₊ + 1

/-- **THE COUNT BOUND, in-statement**: `doorCount ω ≤ log ω/log 2 + 2`. -/
theorem doorCount_le {ω : ℕ} (hω : 1 ≤ ω) :
    (doorCount ω : ℝ) ≤ Real.log ω / Real.log 2 + 2 := by
  have hωR : (1 : ℝ) ≤ (ω : ℝ) := by exact_mod_cast hω
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : (0 : ℝ) ≤ Real.log ω / Real.log 2 :=
    div_nonneg (Real.log_nonneg hωR) hlog2.le
  have hceil := Nat.ceil_lt_add_one h0
  unfold doorCount
  push_cast
  linarith

/-- **THE LADDER OUTRUNS THE DEPTH**: `2ω ≤ 2^{doorCount ω}` — mirroring
`M4Dyadic.pow_ten_le_two_pow_dyadIdx`, at depth `ω` instead of `W^{10}`. -/
theorem two_mul_le_two_pow_doorCount {ω : ℕ} (hω : 1 ≤ ω) :
    2 * (ω : ℝ) ≤ 2 ^ (doorCount ω) := by
  have hωR : (1 : ℝ) ≤ (ω : ℝ) := by exact_mod_cast hω
  have hω0 : (0 : ℝ) < (ω : ℝ) := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : Real.log ω / Real.log 2 ≤ (⌈Real.log ω / Real.log 2⌉₊ : ℝ) := Nat.le_ceil _
  have hmul : Real.log ω ≤ (⌈Real.log ω / Real.log 2⌉₊ : ℝ) * Real.log 2 := by
    rw [div_le_iff₀ hlog2] at hceil; exact hceil
  have hlogs : Real.log ω ≤ Real.log ((2 : ℝ) ^ ⌈Real.log ω / Real.log 2⌉₊) := by
    rw [Real.log_pow]; exact hmul
  have hR : (0 : ℝ) < (2 : ℝ) ^ ⌈Real.log ω / Real.log 2⌉₊ := by positivity
  have hbase : (ω : ℝ) ≤ (2 : ℝ) ^ ⌈Real.log ω / Real.log 2⌉₊ := by
    have h := Real.exp_le_exp.mpr hlogs
    rwa [Real.exp_log hω0, Real.exp_log hR] at h
  unfold doorCount
  rw [pow_succ]
  linarith

/-! ## §3 — THE COVER-SUMMED SIEVE MASS (THE NAMED SEAM)

M4-1's `m4_sieve_insert` carries the total complement mass as `B`; M4-1's ⟦VACUITY
FINDING⟧ proves `B` cannot come from one block.  Here it comes from the cover. -/

/-- **THE LADDER SPLIT.**  For an antitone `ℕ` ladder, `(X_k, X_0]` is the disjoint union of
its blocks `(X_{i+1}, X_i]`, `i < k`.  Stated as an identity of sums in an arbitrary
`AddCommMonoid`, so the consumer may carry a real weight, a complex sum, or a mass through it
unchanged (`M4Dyadic.sum_dyadPart`'s convention). -/
theorem sum_Ioc_ladder_split {Mo : Type*} [AddCommMonoid Mo] {Xs : ℕ → ℕ}
    (hanti : ∀ i, Xs (i + 1) ≤ Xs i) (f : ℕ → Mo) (k : ℕ) :
    ∑ n ∈ Finset.Ioc (Xs k) (Xs 0), f n
      = ∑ i ∈ Finset.range k, ∑ n ∈ Finset.Ioc (Xs (i + 1)) (Xs i), f n := by
  have hle : ∀ j i : ℕ, i ≤ j → Xs j ≤ Xs i := by
    intro j
    induction j with
    | zero => intro i hi; rw [Nat.le_zero.mp hi]
    | succ n ih =>
      intro i hi
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact le_trans (hanti n) (ih i (by omega))
      · have hin : i = n + 1 := by omega
        rw [hin]
  induction k with
  | zero => simp
  | succ n ih =>
    have hcons := Finset.sum_Ioc_consecutive f (hanti n) (hle n 0 (Nat.zero_le n))
    rw [Finset.sum_range_succ, ← ih, ← hcons]
    exact add_comm _ _

/-- **THE PER-BLOCK SIEVE GATE BUNDLE (HS-3).**  The three analytic gates of
`TypicalDensity.typical_density_le`, as they reach `m4_sieve_block_mass`, at one block scale
`X`: positivity, the large-`X` guard `√log X ≥ 100`, MR's regularity `log 𝒬_j ≤ √log X`, and
the error-domination inequality.  Bundled because the door cover must present them once per
block (`∀ i < k`); each still rides its own conjunct (law #253). -/
def SieveBlockGate (A G M J X : ℕ) : Prop :=
  0 < (X : ℝ) ∧
  (100 : ℝ) ≤ Real.sqrt (Real.log X) ∧
  (∀ j ∈ Finset.Icc 1 J, Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log X)) ∧
  (∀ j ∈ Finset.Icc 1 J,
    ((Nat.sqrt X : ℝ) + 1) * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
      ≤ (X : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ)))

/-- **THE COVER SUMMATION, at a general nonnegative weight.**  A per-block bound
`P + H/X_{i+1}`, uniform over the ladder, becomes a total bound over the WHOLE door window
with the count `k` in-statement and the endpoint terms collected geometrically.

This is the mechanical half of `m4_door_sieve_mass`, isolated so that the sieve content and
the covering bookkeeping do not have to be read at once. -/
theorem door_cover_sum_le {x H ω k : ℕ} {f : ℕ → ℝ} {P : ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hxH : H + 1 ≤ x) (hreach : doorLadder x H k ≤ x / ω)
    (hpow : 2 ^ (k + 1) ≤ x)
    (hblk : ∀ i < k, ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n
        ≤ P + (H : ℝ) / (doorLadder x H (i + 1) : ℝ)) :
    ∑ n ∈ Finset.Ioc (x / ω) x, f n ≤ (k : ℝ) * P + 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hpowR : (2 : ℝ) ^ (k + 1) ≤ (x : ℝ) := by exact_mod_cast hpow
  have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hpowR
  -- ⟦STEP 1⟧ enlarge the door window to the ladder's own range
  have hsub : Finset.Ioc (x / ω) x ⊆ Finset.Ioc (doorLadder x H k) (doorLadder x H 0) := by
    rw [doorLadder_zero]
    intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨lt_of_le_of_lt hreach hn.1, hn.2⟩
  have hstep1 : ∑ n ∈ Finset.Ioc (x / ω) x, f n
      ≤ ∑ n ∈ Finset.Ioc (doorLadder x H k) (doorLadder x H 0), f n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf0 n)
  -- ⟦STEP 2⟧ the ladder split
  have hsplit := sum_Ioc_ladder_split (Xs := fun i => doorLadder x H i)
    (fun i => doorLadder_step_le hxH i) f k
  -- ⟦STEP 3⟧ the per-block bound, summed
  have hstep3 : ∑ i ∈ Finset.range k,
      ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n
      ≤ ∑ i ∈ Finset.range k, (P + (H : ℝ) / (doorLadder x H (i + 1) : ℝ)) :=
    Finset.sum_le_sum (fun i hi => hblk i (Finset.mem_range.mp hi))
  -- ⟦STEP 4⟧ the endpoint sum is geometric (HS-6, composed)
  have hgeo : ∑ i ∈ Finset.range k, (H : ℝ) / (doorLadder x H (i + 1) : ℝ)
      ≤ 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by
    have hterm : ∀ i ∈ Finset.range k,
        (H : ℝ) / (doorLadder x H (i + 1) : ℝ) ≤ (H : ℝ) * ((2 : ℝ) ^ (i + 2) / (x : ℝ)) := by
      intro i hi
      have hik := Finset.mem_range.mp hi
      have hpow' : 2 ^ (i + 1 + 1) ≤ x :=
        le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hpow
      have hinv := doorLadder_inv_le (x := x) (H := H) (i := i + 1) hpow'
      have hrw : (H : ℝ) / (doorLadder x H (i + 1) : ℝ)
          = (H : ℝ) * (1 / (doorLadder x H (i + 1) : ℝ)) := by ring
      have heq : i + 1 + 1 = i + 2 := by omega
      rw [heq] at hinv
      rw [hrw]
      exact mul_le_mul_of_nonneg_left hinv hH0
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, ← Finset.sum_div]
    have hgs := sum_range_two_pow_shift_le k
    have hdiv : (∑ i ∈ Finset.range k, (2 : ℝ) ^ (i + 2)) / (x : ℝ) ≤ (4 * 2 ^ k) / (x : ℝ) := by
      rw [div_le_div_iff₀ hx0 hx0]
      nlinarith
    calc (H : ℝ) * ((∑ i ∈ Finset.range k, (2 : ℝ) ^ (i + 2)) / (x : ℝ))
        ≤ (H : ℝ) * ((4 * 2 ^ k) / (x : ℝ)) := mul_le_mul_of_nonneg_left hdiv hH0
      _ = 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by ring
  -- ⟦STEP 5⟧ the arithmetic
  have hconst : ∑ i ∈ Finset.range k, (P + (H : ℝ) / (doorLadder x H (i + 1) : ℝ))
      = (k : ℝ) * P + ∑ i ∈ Finset.range k, (H : ℝ) / (doorLadder x H (i + 1) : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsplit] at hstep1
  rw [hconst] at hstep3
  linarith

/-- **`m4_door_sieve_mass` — THE NAMED SEAM.**  The total harmonic complement mass over the
WHOLE door window `(x/ω, x]`, obtained by summing `M4Sieve.m4_sieve_block_mass` over the
door ladder:

`∑_{n ∈ (x/ω,x]} #{m ∈ (n, n+H] : m ∉ 𝒮}/n ≤ k·(δ/4)·H + 4·2^k·H/x`.

⟦THE TWO TERMS, NAMED⟧
* `k·(δ/4)·H` — the sieve mass, `k` blocks each at the M-gate `8C/δ ≤ M` (`M4Sieve`'s §4, the
  `δ/4` variant — see ⟦THE GATE VARIANT⟧ in the preamble).  The count `k` is IN-STATEMENT;
  `doorCount_le` supplies `k ≤ log ω/log 2 + 2`, and §4 cancels it against the door
  normaliser.
* `4·2^k·H/x` — **HS-6, COMPOSED**.  Per block, the half-open endpoint `m = X_i` of the
  engine's `Ioc X (2X)` costs `H/X_i` (`M4Sieve.card_notMemS_of_subset_Icc`: one lattice
  point, spread over the `≤ H` short windows that see it).  Summed over the cover this is the
  GEOMETRIC sum `H·∑_{i<k} 1/X_{i+1} ≤ H·∑_{i<k} 2^{i+2}/x ≤ 4·2^k·H/x` (`doorLadder_inv_le`
  + `sum_range_two_pow_shift_le`) — the freeze's `2^i/x`-shape, bounded honestly rather than
  by the crude `k/X_k`.  At the exhausting count (`2^k ≍ 2ω`) the grade is `8·H·ω/x`, which
  the door regime's `x ≥ ω·H + …` floor clears with room.

⟦THE GATES, ALL CARRIED⟧  the ladder's floor `H + 1 ≤ x`, the exhaustion
`doorLadder x H k ≤ x/ω` (supplied by `doorLadder_reaches`), the geometric gate
`2^{k+1} ≤ x`, and the per-block HS-3 bundle.  Nothing is evaluated; `A`, `G`, `M`, `J` stay
variable (the ⟦V9c LAW⟧). -/
theorem m4_door_sieve_mass :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A G M J x ω H k : ℕ) (δ : ℝ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 0 < δ → 8 * C / δ ≤ (M : ℝ) →
      H + 1 ≤ x → doorLadder x H k ≤ x / ω → 2 ^ (k + 1) ≤ x →
      (∀ i < k, SieveBlockGate A G M J (doorLadder x H (i + 1))) →
      ∑ n ∈ Finset.Ioc (x / ω) x,
          ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ) * (n : ℝ)⁻¹
        ≤ (k : ℝ) * (δ / 4 * (H : ℝ)) + 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by
  obtain ⟨C, hC, hblk⟩ := m4_sieve_block_mass
  refine ⟨C, hC, ?_⟩
  intro A G M J x ω H k δ hA hG hM hδ hMδ hxH hreach hpow hgate
  refine door_cover_sum_le
    (f := fun n => ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ) * (n : ℝ)⁻¹)
    (P := δ / 4 * (H : ℝ)) (fun n => by positivity) hxH hreach hpow ?_
  intro i hi
  obtain ⟨hX0, hbig, hreg, herr⟩ := hgate i hi
  exact hblk A G M J (doorLadder x H (i + 1)) H (doorLadder x H (i + 1))
    (doorLadder x H i) δ hA hG hM hδ hMδ hX0 le_rfl (doorLadder_block_subset x H i)
    hbig hreg herr

/-! ## §4 — THE `log ω` ABSORPTION INTO `M`

The freeze's :283 clause, and `SieveGlue.lean:81–82`'s deferred residual #2.  Two lemmas:
the cancellation itself, and the rescale it licenses. -/

/-- **THE CANCELLATION.**  The cover's block count and the door normaliser are the SAME
`log ω`, and their ratio is an absolute constant: `k ≤ 3·Z` for every `ω` with `log ω ≥ 4`.

The `3` is not cosmetic: `(L/log 2 + 2)/(L − 1)` is strictly decreasing in `L` (its numerator
grows at rate `1/log 2 ≈ 1.443`, its denominator at rate `1`), so the worst case is the floor
`L = 4`, where the ratio is `(5.771 + 2)/3 = 2.59 < 3`.  Asymptotically it is
`1/log 2 = 1.4427`. -/
theorem door_count_le_three_mul_norm {ω k : ℕ} {Z : ℝ}
    (hL : 4 ≤ Real.log ω) (hk : (k : ℝ) ≤ Real.log ω / Real.log 2 + 2)
    (hZ : Real.log ω - 1 ≤ Z) : (k : ℝ) ≤ 3 * Z := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hd9 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hd9' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkmul : (k : ℝ) * Real.log 2 ≤ Real.log ω + 2 * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right hk hlog2.le
    rwa [add_mul, div_mul_cancel₀ _ hlog2.ne'] at h
  have hkm : (k : ℝ) * 0.6931471803 ≤ (k : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hd9.le hk0
  linarith

/-- **THE RESCALE THE CANCELLATION LICENSES.**  With the per-block grade taken at `δ/3` (the
`M`-gate at `8C/(δ/3) = 24C/δ`), the cover-summed, door-normalised mass is back at the
freeze's `δ/4·H`, and the endpoint term survives divided by `Z`.

This is the whole content of "the `log ω` absorption into `M`": an absolute factor `3` in
front of a `δ`-grade is a LINEAR rescale of the K-ladder's re-pin parameter `M`, exactly the
cost `SieveGlue`'s HS-1 pays for the engine's own constant. -/
theorem door_mass_normalised_le {k : ℕ} {Z δ Hr Gm : ℝ}
    (hZ0 : 0 < Z) (hk3 : (k : ℝ) ≤ 3 * Z) (hδ : 0 ≤ δ) (hH : 0 ≤ Hr) :
    ((k : ℝ) * (δ / 3 / 4 * Hr) + Gm) / Z ≤ δ / 4 * Hr + Gm / Z := by
  have hnn : (0 : ℝ) ≤ δ / 3 / 4 * Hr := by positivity
  have hmul : (k : ℝ) * (δ / 3 / 4 * Hr) ≤ (3 * Z) * (δ / 3 / 4 * Hr) :=
    mul_le_mul_of_nonneg_right hk3 hnn
  have hsplit : ((k : ℝ) * (δ / 3 / 4 * Hr) + Gm) / Z
      = (k : ℝ) * (δ / 3 / 4 * Hr) / Z + Gm / Z := by rw [add_div]
  rw [hsplit]
  have hkey : (k : ℝ) * (δ / 3 / 4 * Hr) / Z ≤ δ / 4 * Hr := by
    rw [div_le_iff₀ hZ0]
    have he : (3 * Z) * (δ / 3 / 4 * Hr) = δ / 4 * Hr * Z := by ring
    linarith
  linarith

/-! ## §5 — THE EXIT

`m4_door_glue`: the composed statement M4-7 consumes.  Every constant is symbolic and every
gate is named. -/

/-- **`m4_door_glue` — THE M4-8 EXIT.**  The door's `logMeasure`-`L¹` window norm at a
general 1-bounded datum, with the block indicator `1_𝒮` inserted and the complement paid by
the cover-summed sieve mass:

`∫‖∑_{n<m≤n+H} a(m)e(αm)‖ dμ ≤ ∫‖∑ 1_𝒮(m)a(m)e(αm)‖ dμ + (δ/4)·H + 4·2^k·H/x`.

⟦THE GATE LIST, ALL IN-STATEMENT⟧
* **the M-gate** `24C/δ ≤ M` — the freeze's `8C/δ` at the per-block grade `δ/3`, i.e. the
  `log ω` absorption of §4 already applied (⟦THE GATE VARIANT⟧, preamble);
* **HS-3's gates**, one bundle per block: `∀ i < k, SieveBlockGate A G M J X_{i+1}`;
* **the count** `k`, with `(k:ℝ) ≤ log ω/log 2 + 2` (`doorCount_le` supplies it at
  `k := doorCount ω`);
* **`Z`'s bounds** — the door regime `2 ≤ x`, `2 ≤ ω`, `ω ≤ x` gives
  `Z ∈ [log ω − 1, log ω + 1]`, and `4 ≤ log ω` is the floor at which the absorption's
  constant is `3`;
* **the ladder's gates** — `H + 1 ≤ x` (the floor invariant), `doorLadder x H k ≤ x/ω` (the
  exhaustion, `doorLadder_reaches`), `2^{k+1} ≤ x` (the geometric gate).

⟦ONE CONSTANT⟧ `card_blockfree_le`'s `C`, opened once and threaded into the M-gate. -/
theorem m4_door_glue :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A G M J x ω H k : ℕ) (a : ℕ → ℂ) (α δ : ℝ),
      (∀ m, ‖a m‖ ≤ 1) →
      1 ≤ A → 1 ≤ G → 1 ≤ M → 0 < δ → 24 * C / δ ≤ (M : ℝ) →
      2 ≤ x → 2 ≤ ω → ω ≤ x → 4 ≤ Real.log ω →
      H + 1 ≤ x → doorLadder x H k ≤ x / ω → 2 ^ (k + 1) ≤ x →
      (k : ℝ) ≤ Real.log ω / Real.log 2 + 2 →
      (∀ i < k, SieveBlockGate A G M J (doorLadder x H (i + 1))) →
      (∫ n, ‖absWindowSum a H n α‖ ∂(logMeasure x ω))
        ≤ (∫ n, ‖absWindowSum (memSCoeff (calP A G) (calQK A G M) J a) H n α‖
              ∂(logMeasure x ω))
          + δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by
  obtain ⟨C, hC, hmass⟩ := m4_door_sieve_mass
  refine ⟨C, hC, ?_⟩
  intro A G M J x ω H k a α δ ha hA hG hM hδ hMδ hx hω hωx hL hxH hreach hpow hk hgate
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hpowR : (2 : ℝ) ^ (k + 1) ≤ (x : ℝ) := by exact_mod_cast hpow
  have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hpowR
  -- ⟦the normaliser⟧
  have hZlo : Real.log ω - 1 ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    door_norm_ge hx hω hωx
  have hZ0 : (0 : ℝ) < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
  have hZ1 : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
  -- ⟦the insert⟧ (M4-1, cited)
  have hadd : (∫ n, ‖absWindowSum a H n α‖ ∂(logMeasure x ω))
      ≤ (∫ n, ‖absWindowSum (memSCoeff (calP A G) (calQK A G M) J a) H n α‖
            ∂(logMeasure x ω))
        + ∫ n, ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ) ∂(logMeasure x ω) :=
    integral_logMeasure_le_add
      (fun n => norm_absWindowSum_memS_insert ha (calP A G) (calQK A G M) J H n α)
  -- ⟦the mass, at the per-block grade δ/3 — the M-gate 24C/δ IS 8C/(δ/3)⟧
  have hδ3 : (0 : ℝ) < δ / 3 := by linarith
  have hMδ3 : 8 * C / (δ / 3) ≤ (M : ℝ) := by
    have he : 8 * C / (δ / 3) = 24 * C / δ := by field_simp; ring
    rw [he]; exact hMδ
  have hB := hmass A G M J x ω H k (δ / 3) hA hG hM hδ3 hMδ3 hxH hreach hpow hgate
  -- ⟦the sharp normalisation⟧
  have hint : (∫ n, ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ)
        ∂(logMeasure x ω))
      ≤ ((k : ℝ) * (δ / 3 / 4 * (H : ℝ)) + 4 * 2 ^ k * (H : ℝ) / (x : ℝ))
          / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    integral_logMeasure_le_div hZ0 hB
  -- ⟦the absorption⟧
  have hk3 : (k : ℝ) ≤ 3 * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    door_count_le_three_mul_norm hL hk hZlo
  have habs := door_mass_normalised_le (k := k)
    (Z := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) (δ := δ) (Hr := (H : ℝ))
    (Gm := 4 * 2 ^ k * (H : ℝ) / (x : ℝ)) hZ0 hk3 hδ.le hH0
  -- ⟦the endpoint term: `Z ≥ 1` can only help⟧
  have hnn : (0 : ℝ) ≤ 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by positivity
  have hend : (4 * 2 ^ k * (H : ℝ) / (x : ℝ)) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹
      ≤ 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by
    rw [div_le_iff₀ hZ0]
    nlinarith
  linarith

/-- The M4-8 exit at the λ-datum (`M4Residue.liouvilleC`) — the raw door window. -/
theorem m4_door_glue_liouville :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A G M J x ω H k : ℕ) (α δ : ℝ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 0 < δ → 24 * C / δ ≤ (M : ℝ) →
      2 ≤ x → 2 ≤ ω → ω ≤ x → 4 ≤ Real.log ω →
      H + 1 ≤ x → doorLadder x H k ≤ x / ω → 2 ^ (k + 1) ≤ x →
      (k : ℝ) ≤ Real.log ω / Real.log 2 + 2 →
      (∀ i < k, SieveBlockGate A G M J (doorLadder x H (i + 1))) →
      (∫ n, ‖absWindowSum liouvilleC H n α‖ ∂(logMeasure x ω))
        ≤ (∫ n, ‖absWindowSum (memSCoeff (calP A G) (calQK A G M) J liouvilleC) H n α‖
              ∂(logMeasure x ω))
          + δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by
  obtain ⟨C, hC, hglue⟩ := m4_door_glue
  exact ⟨C, hC, fun A G M J x ω H k α δ =>
    hglue A G M J x ω H k liouvilleC α δ liouvilleC_norm_le_one⟩

/-- The M4-8 exit at the row's own datum `λχ̄` (`CapFreeAssembly.liouChi`) — the `f` M4-5
plugs into `thm_A2′`, with `1_𝒮` inserted and the complement priced by the cover. -/
theorem m4_door_glue_liouChi {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A G M J x ω H k : ℕ) (α δ : ℝ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 0 < δ → 24 * C / δ ≤ (M : ℝ) →
      2 ≤ x → 2 ≤ ω → ω ≤ x → 4 ≤ Real.log ω →
      H + 1 ≤ x → doorLadder x H k ≤ x / ω → 2 ^ (k + 1) ≤ x →
      (k : ℝ) ≤ Real.log ω / Real.log 2 + 2 →
      (∀ i < k, SieveBlockGate A G M J (doorLadder x H (i + 1))) →
      (∫ n, ‖absWindowSum (liouChi χ) H n α‖ ∂(logMeasure x ω))
        ≤ (∫ n, ‖absWindowSum (memSCoeff (calP A G) (calQK A G M) J (liouChi χ)) H n α‖
              ∂(logMeasure x ω))
          + δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by
  obtain ⟨C, hC, hglue⟩ := m4_door_glue
  exact ⟨C, hC, fun A G M J x ω H k α δ =>
    hglue A G M J x ω H k (liouChi χ) α δ (norm_liouChi_le_one χ)⟩

/-- **THE COVER IS INHABITED** (the anti-vacuity duty — `TLGATES-SCOPE`'s lesson, and
M4-1's).  At the in-statement count `k := doorCount ω`, the ladder's two quantitative gates
— the exhaustion `doorLadder x H k ≤ x/ω` and the count bound — are *both* discharged from
door-regime data alone (`2ω(H+2) ≤ x`).  So `m4_door_glue`'s hypothesis list is not
vacuously satisfiable-by-nobody: this lemma is the witness. -/
theorem doorCount_gates {x H ω : ℕ} (hω : 1 ≤ ω)
    (hbig : 2 * (ω : ℝ) * ((H : ℝ) + 2) ≤ (x : ℝ)) :
    doorLadder x H (doorCount ω) ≤ x / ω ∧
      ((doorCount ω : ℕ) : ℝ) ≤ Real.log ω / Real.log 2 + 2 :=
  ⟨doorLadder_reaches hω (two_mul_le_two_pow_doorCount hω) hbig, doorCount_le hω⟩

end Salt.MR

end
