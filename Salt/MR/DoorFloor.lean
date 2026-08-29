/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.SpineFinal
import Salt.MR.DoorDischarge

/-!
# `H₀door` — the SPINE-BUDGET head's missing consumable (MR gate, stone S11)

`log_chowla_two_budget_head` (`Salt/Entropy/Chowla/SpineFinal.lean:749`) fixes an
honest `ε : ℚ` and the door threshold `δ₀ = (cD3/(16·C))·ε/(2·K) > 0` — BOTH
before its `∀ extraFloor : ℕ` quantifier, which is what makes the interface
non-circular — and then hands the caller, for every floor demand `extraFloor`, a
regime `R` with `extraFloor ≤ R.Hlo`.  Its doc-comment (`:747-748`) names the
intended instance:

> The `∀ extraFloor` interface is what the short-interval MR compose (S11)
> consumes to place `H₀door(δ₀)` under `R.Hlo`.

No `H₀door` existed in Lean; `extraFloor := H₀door(δ₀)` could not be typed.  This
file supplies it, its API, and the kernel-checked instantiation certificate.

## The shape (why `⌈exp(δ₀^{-4/5})⌉₊`)

The Matomäki–Radziwiłł–Tao short-interval door (Tao arXiv:1509.05422v2 Prop. 2.4, proven
in arXiv:1503.05121) delivers its uniformity at window length `H` with quality
grade `(log H)^{-5/4}` — `doorGrade H` below.  The head consumes a door at any
`δ ≤ δ₀`, so the compose must push the regime's window range up to where the MR
grade has already fallen below `δ₀`:

`(log H)^{-5/4} ≤ δ₀  ⟺  log H ≥ δ₀^{-4/5}  ⟺  H ≥ exp(δ₀^{-4/5})`.

Hence `H0door δ₀ := ⌈exp(δ₀^{-4/5})⌉₊`, the least natural number at or above that
crossing point (`doorGrade_le_of_H0door_le` is the defining property; the ceiling
is what makes it a `ℕ`, the type of the `extraFloor` slot).

The definition is **symbolic on purpose**.  At the spine's own `δ₀ ≈ 2·10⁻⁴⁹` it
reads `exp(9·10³⁸)` — implied-constant-free, a SHAPE and not a pin (a
`C_MRT = 10⁶` would shift it to `exp(1.1·10⁴⁴)`, harmlessly and one-sided).  No
closed numeral of that size is ever formed, so nothing here can reach `norm_num`
or the numeral-exponent linter.  Every bound below is proved from monotonicity.

## The S10a hand-off

`regime_W_headroom_of_floor` (`Salt/MR/DoorDischarge.lean:42`) needs its threshold
binder `hthr`.  `regime_hthr_of_scale` supplies exactly that binder from a plain
scale bound `6250000 ≤ log H₊` plus the `ε`-side arm, and
`regime_W_headroom_of_H0door` chains it to the floor: once `H0door δ₀ ≤ R.Hhi`
with `δ₀ ≤ 6250000^{-5/4}`, Tao's W-constraint `W = log⁵H₊ ≤ (log X)^{1/125}`
holds.  At the door's numerology (`log H₀door ≈ 9·10³⁸` against a demand of
`6.25·10⁶`) that arm is satisfied with ~32 orders of headroom.

## Provenance of the numerology

`docs/exploration/door-road-0724.md:52` (`δ₀ ≈ 2·10⁻⁴⁹`, `H₀door ≈ exp(9·10³⁸)`,
`x ≈ exp exp(9·10³⁸)`) and `docs/exploration/chi-check-0724.md:88-99` (the ledger
check: `(log H)^{-5/4} = δ₀ ⇒ log H = exp(0.8·112.13) = 8.99·10³⁸`, monotone, and
the `B5 = 5` consistency `H > W^{203}`).  `docs/exploration/mr-freeze.md:21` is the
S11 compose order this file's `budget_head_grade_closed` is cut to fit.
-/

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ### The two definitions -/

/-- **The MR door grade** at window length `H`: the uniformity quality
`(log H)^{-5/4}`.  It is the `W^{-1/4}` saving of the character expansion read at
`W = (log H)^5`.  Decreasing in `H` (`doorGrade_anti`) — longer windows buy a
better door.

⛔ **THIS IS THE *PIN*, NOT WHAT MRT DELIVERS, AND THE DISTINCTION IS LOAD-BEARING.**
An earlier wording said `(log H)^{-5/4}` was *"delivered by the Matomäki–Radziwiłł–Tao
short-interval theorem"*.  It is not.  MRT's own rate is
`((log H)^{1/4}·loglog H) / W^{1/4}` (`arXiv:1503.05121v3` Thm 2.3 (2.2), p.9, read from
the PDF); `W^{-1/4}` alone DROPS the `(log H)^{1/4}·loglog H` numerator.  What the corpus
carries as the delivered rate is `mrtDeliveredGrade` (`M4Exit.lean:153`),
`C_MRT·(log H)^{-11/4}·loglog H`, which is (2.2) read at `W = (log H)^{12}`; `mrtGate`
is the crossing at which delivery falls under this pin, the exponent gap being
`-5/4 − (−11/4) = 3/2`.  **The pin is the WEAKER target and delivery is stronger — the
safe direction, and the reason the two objects are separate.**

⚠️ **`B₅` PARAMETER NOTE:** the `W = (log H)^5` above is `B₅ = 5`, **S7's value, RETIRED by
the S9 re-freeze** (`docs/exploration/s9-design-0726.md` ⟦AMENDMENT A⟧).  The live sweep is
`B₅ = 12` and its apparatus is `DoorFloor1500.lean`, where Tao Prop 2.4's W-constraint reads
`W^{125} = (log H₊)^{1500} ≤ log X_min` and BOTH arms are discharged
(`regime_W_headroom_of_floor_1500`; §2 `W_second_arm` for `W ≤ H^{1/250}`).  **The `B₅ = 5`
forms are kept deliberately as the historical record, which is exactly why a grep finds
`(log H)^5` here and it reads like a live constraint.**  This pin's VALUE is unaffected —
a target computed at the old `B₅` is simply a weaker target — but do not cite `B5 = 5` as
current.  *(Repaired 2026-08-23 under QUEUE item 15's documentation rider; the original
sentence is preserved in this note rather than deleted.)* -/
noncomputable def doorGrade (H : ℕ) : ℝ := Real.log (H : ℝ) ^ (-(5 / 4 : ℝ))

/-- **`H₀door` — the door floor.**  The least window length at which the MR grade
`doorGrade` has fallen to `δ₀`, i.e. `⌈exp(δ₀^{-4/5})⌉₊`.  This is the value the
S11 compose feeds to the `∀ extraFloor : ℕ` slot of
`log_chowla_two_budget_head`, placing the whole regime window range inside the
door's reach (`budget_head_grade_closed`).

SHAPE, NOT NUMERAL: at `δ₀ ≈ 2·10⁻⁴⁹` this is `exp(9·10³⁸)`; it is never
evaluated, only compared. -/
noncomputable def H0door (δ₀ : ℝ) : ℕ := ⌈Real.exp (δ₀ ^ (-(4 / 5 : ℝ)))⌉₊

/-! ### The rpow workhorse

Negative-exponent `rpow` is antitone in the base.  Stated once here; every
monotonicity fact below is an instance (`positivity` is blind to `rpow` bases, so
the positivity side conditions are threaded by hand — the live trap). -/

/-- `x ↦ x^(-p)` is antitone on the positive reals for `0 ≤ p`. -/
theorem rpow_neg_anti {a b p : ℝ} (ha : 0 < a) (hab : a ≤ b) (hp : 0 ≤ p) :
    b ^ (-p) ≤ a ^ (-p) := by
  have hb : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  rw [Real.rpow_neg ha.le, Real.rpow_neg hb.le]
  have h := one_div_le_one_div_of_le (Real.rpow_pos_of_pos ha p)
    (Real.rpow_le_rpow ha.le hab hp)
  rwa [one_div, one_div] at h

/-! ### Basic API -/

/-- The door floor is a genuine (positive) floor demand. -/
theorem H0door_pos (δ₀ : ℝ) : 0 < H0door δ₀ :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

/-- The ceiling's defining bound: `exp(δ₀^{-4/5}) ≤ H₀door(δ₀)`. -/
theorem exp_le_H0door (δ₀ : ℝ) :
    Real.exp (δ₀ ^ (-(4 / 5 : ℝ))) ≤ (H0door δ₀ : ℝ) :=
  Nat.le_ceil _

/-- A smaller door threshold demands a higher floor: `H₀door` is antitone. -/
theorem H0door_anti {δ₁ δ₂ : ℝ} (h1 : 0 < δ₁) (h : δ₁ ≤ δ₂) : H0door δ₂ ≤ H0door δ₁ :=
  Nat.ceil_le_ceil (Real.exp_le_exp.mpr (rpow_neg_anti h1 h (by norm_num)))

/-- The grade is positive at every window length `2 ≤ H` — the `0 < δ` arm of the
budget head's door quantifier. -/
theorem doorGrade_pos {H : ℕ} (hH : 2 ≤ H) : 0 < doorGrade H := by
  have h1 : (1 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 1 < H)
  exact Real.rpow_pos_of_pos (Real.log_pos h1) _

/-- The grade improves with window length: `doorGrade` is antitone above `2`. -/
theorem doorGrade_anti {H₁ H₂ : ℕ} (h1 : 2 ≤ H₁) (h : H₁ ≤ H₂) :
    doorGrade H₂ ≤ doorGrade H₁ := by
  have hH1 : (1 : ℝ) < (H₁ : ℝ) := by exact_mod_cast (by omega : 1 < H₁)
  have hL1 : (0 : ℝ) < Real.log (H₁ : ℝ) := Real.log_pos hH1
  have hle : Real.log (H₁ : ℝ) ≤ Real.log (H₂ : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast h)
  exact rpow_neg_anti hL1 hle (by norm_num)

/-! ### The floor's defining property -/

/-- Above the floor the window length's logarithm clears `δ₀^{-4/5}`. -/
theorem log_ge_of_H0door_le {δ₀ : ℝ} {H : ℕ} (h : H0door δ₀ ≤ H) :
    δ₀ ^ (-(4 / 5 : ℝ)) ≤ Real.log (H : ℝ) := by
  have hcast : ((H0door δ₀ : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h
  have h1 : Real.exp (δ₀ ^ (-(4 / 5 : ℝ))) ≤ (H : ℝ) := le_trans (exp_le_H0door δ₀) hcast
  have h2 := Real.log_le_log (Real.exp_pos _) h1
  rwa [Real.log_exp] at h2

/-- **The defining property of `H₀door`.**  Above the floor, the MR grade has
already fallen below the door threshold: `H₀door(δ₀) ≤ H → (log H)^{-5/4} ≤ δ₀`.
This is what lets the compose feed a genuine `δ ≤ δ₀` to the budget head. -/
theorem doorGrade_le_of_H0door_le {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {H : ℕ} (h : H0door δ₀ ≤ H) :
    doorGrade H ≤ δ₀ := by
  have ht : (0 : ℝ) < δ₀ ^ (-(4 / 5 : ℝ)) := Real.rpow_pos_of_pos hδ₀ _
  have hL : δ₀ ^ (-(4 / 5 : ℝ)) ≤ Real.log (H : ℝ) := log_ge_of_H0door_le h
  have hLpos : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le ht hL
  -- the exponent identity `(δ₀^{-4/5})^{5/4} = δ₀⁻¹`
  have hid : (δ₀ ^ (-(4 / 5 : ℝ))) ^ (5 / 4 : ℝ) = δ₀⁻¹ := by
    rw [← Real.rpow_mul hδ₀.le,
      show (-(4 / 5 : ℝ)) * (5 / 4 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hmono : δ₀⁻¹ ≤ Real.log (H : ℝ) ^ (5 / 4 : ℝ) := by
    rw [← hid]; exact Real.rpow_le_rpow ht.le hL (by norm_num)
  have hgrade : doorGrade H = (Real.log (H : ℝ) ^ (5 / 4 : ℝ))⁻¹ := by
    rw [doorGrade, Real.rpow_neg hLpos.le]
  rw [hgrade]
  have h := one_div_le_one_div_of_le (inv_pos.mpr hδ₀) hmono
  rwa [one_div, one_div, inv_inv] at h

/-- The floor's scale bound in the form the S10a threshold reads: if `δ₀` is below
`c^{-5/4}` then every window length above `H₀door(δ₀)` has `log H ≥ c`. -/
theorem le_log_of_H0door_le {δ₀ c : ℝ} (hc : 0 < c) (hδ₀ : 0 < δ₀)
    (hsmall : δ₀ ≤ c ^ (-(5 / 4 : ℝ))) {H : ℕ} (h : H0door δ₀ ≤ H) :
    c ≤ Real.log (H : ℝ) := by
  have h1 : (c ^ (-(5 / 4 : ℝ))) ^ (-(4 / 5 : ℝ)) ≤ δ₀ ^ (-(4 / 5 : ℝ)) :=
    rpow_neg_anti hδ₀ hsmall (by norm_num)
  have h2 : (c ^ (-(5 / 4 : ℝ))) ^ (-(4 / 5 : ℝ)) = c := by
    rw [← Real.rpow_mul hc.le,
      show (-(5 / 4 : ℝ)) * (-(4 / 5 : ℝ)) = 1 by norm_num, Real.rpow_one]
  rw [h2] at h1
  exact le_trans h1 (log_ge_of_H0door_le h)

/-! ### The S10a threshold hand-off -/

/-- The scale arithmetic behind the S10a threshold: `625·log L ≤ L/2` for
`L ≥ 6.25·10⁶`.  Proof: `log L = 2·log √L ≤ 2√L` and `L = √L·√L ≥ 2500·√L`. -/
theorem log_scale_threshold {L : ℝ} (hL : 6250000 ≤ L) : 625 * Real.log L ≤ L / 2 := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hs : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  have hroot : Real.sqrt (6250000 : ℝ) = 2500 := by
    rw [show (6250000 : ℝ) = 2500 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsq : (2500 : ℝ) ≤ Real.sqrt L := by
    have := Real.sqrt_le_sqrt hL
    rwa [hroot] at this
  have hkey : 2500 * Real.sqrt L ≤ L := by nlinarith [hs, hsq, Real.sqrt_nonneg L]
  have hlog : Real.log L = 2 * Real.log (Real.sqrt L) := by
    rw [Real.log_sqrt hLpos.le]; ring
  have hlt : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLpos)
  rw [hlog]
  linarith [hkey, hlt]

/-- **The `hthr` binder of `regime_W_headroom_of_floor`, supplied.**  Byte-shaped
to `Salt/MR/DoorDischarge.lean:43-45`: the `625·loglog H₊` term is absorbed by
half of `log H₊` once the scale clears `6.25·10⁶`, and the `ε`-side arm carries
the other half. -/
theorem regime_hthr_of_scale (R : ChowlaRegime)
    (hbig : 6250000 ≤ Real.log (R.Hhi : ℝ))
    (heps : Real.log (1 / (4 * Real.log 2 * (R.eps : ℝ) ^ 2)) + 3
        ≤ Real.log (R.Hhi : ℝ) / 2) :
    625 * Real.log (Real.log (R.Hhi : ℝ))
        + Real.log (1 / (4 * Real.log 2 * (R.eps : ℝ) ^ 2)) + 3
      ≤ Real.log (R.Hhi : ℝ) := by
  have h := log_scale_threshold hbig
  linarith

/-- **The door floor discharges Tao's W-constraint.**  Once the regime's upper
window endpoint clears `H₀door(δ₀)` (with `δ₀` below `6250000^{-5/4} ≈ 3·10⁻⁹` —
at the spine's `δ₀ ≈ 2·10⁻⁴⁹`, ~40 orders of slack in `δ₀`), S10a fires:
`(log H₊)^625 ≤ log X_min`, i.e. `W = (log H₊)^5 ≤ (log X_min)^{1/125}`. -/
theorem regime_W_headroom_of_H0door (R : ChowlaRegime) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hsmall : δ₀ ≤ (6250000 : ℝ) ^ (-(5 / 4 : ℝ)))
    (hfloor : H0door δ₀ ≤ R.Hhi)
    (heps : Real.log (1 / (4 * Real.log 2 * (R.eps : ℝ) ^ 2)) + 3
        ≤ Real.log (R.Hhi : ℝ) / 2) :
    (Real.log (R.Hhi : ℝ)) ^ (625 : ℕ) ≤ Real.log ((R.x : ℝ) / (2 * (R.ω : ℝ))) :=
  regime_W_headroom_of_floor R
    (regime_hthr_of_scale R (le_log_of_H0door_le (by norm_num) hδ₀ hsmall hfloor) heps)

/-! ### The certificate: the `extraFloor` slot accepts `H0door δ₀` -/

/-- **D-3 — `extraFloor := H₀door(δ₀)` types and instantiates.**  The `∀ extraFloor`
head of `log_chowla_two_budget_head` fired at the door floor computed from the
head's OWN `δ₀`.  Note the ordering that makes this non-circular: `ε` and `δ₀` are
fixed by the head BEFORE `extraFloor` is quantified, so `H0door δ₀` is a legal
argument — the compile of this theorem is the certificate. -/
theorem budget_head_at_H0door :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ H0door δ₀ ≤ R.Hlo ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨ε, δ₀, hε, hδ₀, h⟩ := log_chowla_two_budget_head
  obtain ⟨R, hReps, hRfloor, hR⟩ := h (H0door δ₀)
  exact ⟨ε, δ₀, hε, hδ₀, R, hReps, hRfloor, hR⟩

/-- **The compose-facing form.**  Same instantiation, carrying the payoff: at the
`H₀door(δ₀)` floor EVERY window length in the regime's range already has MR grade
`≤ δ₀`, so a short-interval door supplied at the grade of any such window is an
admissible `δ` for the head.  This is the S11 junction in one statement; what
remains for S11 is the MR side — producing `MRTUniformityXi R (doorGrade H)`. -/
theorem budget_head_grade_closed :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ H0door δ₀ ≤ R.Hlo ∧
        (∀ H : ℕ, R.Hlo ≤ H → 0 < doorGrade H ∧ doorGrade H ≤ δ₀) ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨ε, δ₀, hε, hδ₀, h⟩ := log_chowla_two_budget_head
  obtain ⟨R, hReps, hRfloor, hR⟩ := h (H0door δ₀)
  refine ⟨ε, δ₀, hε, hδ₀, R, hReps, hRfloor, ?_, hR⟩
  intro H hH
  have hfloor : H0door δ₀ ≤ H := le_trans hRfloor hH
  refine ⟨doorGrade_pos ?_, doorGrade_le_of_H0door_le hδ₀ hfloor⟩
  have h4 : 4000000 ≤ R.Hlo := R.hHlo_floor
  omega

/-- **The compose-facing form, g-twin (REGIME-CUT).**  Additive twin of
`budget_head_grade_closed` fired at the g-carrying head
(`log_chowla_two_budget_head_g`): the same door-floor instantiation
`extraFloor := H0door δ₀` and the same grade payoff, now carrying the two extra
levers through to the caller —

* `U1floor ≤ R.Hlo`, a SECOND floor demand riding its own binder (no `max` is
  needed at this call site: the head keeps `extraFloor` and `U1floor` separate,
  so the door floor stays exactly `H0door δ₀` in its own slot);
* `g R.Hhi R.ω ≤ R.x`, the parametric outer-scale clearance, left UNINSTANTIATED
  here — downstream stones choose `g`.

Non-circularity is unchanged and now covers the new binders: `U1floor` and `g`
are fixed before the head is fired, `ε` and `δ₀` are fixed by the head before
`extraFloor` is quantified, so `H0door δ₀` remains a legal argument.  The grade
block below is `budget_head_grade_closed`'s, unchanged: it reads only `hRfloor`
and `R.hHlo_floor`, neither of which moves. -/
theorem budget_head_grade_closed_g (U1floor : ℕ) (g : ℕ → ℕ → ℕ) :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ H0door δ₀ ≤ R.Hlo ∧
        U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
        (∀ H : ℕ, R.Hlo ≤ H → 0 < doorGrade H ∧ doorGrade H ≤ δ₀) ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨ε, δ₀, hε, hδ₀, h⟩ := log_chowla_two_budget_head_g
  -- the head's tower-law conjunct (⟦THE NAMED AMENDMENT⟧) is not consumed here
  obtain ⟨R, hReps, hRfloor, hRU1, hRg, -, hR⟩ := h (H0door δ₀) U1floor g
  refine ⟨ε, δ₀, hε, hδ₀, R, hReps, hRfloor, hRU1, hRg, ?_, hR⟩
  intro H hH
  have hfloor : H0door δ₀ ≤ H := le_trans hRfloor hH
  refine ⟨doorGrade_pos ?_, doorGrade_le_of_H0door_le hδ₀ hfloor⟩
  have h4 : 4000000 ≤ R.Hlo := R.hHlo_floor
  omega

/-! ## The two ε-dependent MRT thresholds — QUEUE item 12's remaining worker-tier arm

`QUEUE.md`'s item 12 leaves `H₀mrt(ε)` and `H₊*(ε)` with the seam *"instantiate the budget heads'
existing `∀ extraFloor` binder — ZERO edits inside `SpineFinal`"*.  They are the `h`-side and
`X`-side floors at which two of `MRTThmA1`'s three error terms fall below a demanded `ε`, and they
are built here, beside `H0door`, because this is the file whose business is floor demands for that
binder.

⛔⛔ **THE ERROR TERMS ARE TAKEN FROM THE LANDED STATEMENT, NOT FROM THE SCOPING BRIEF.**
`MRTThmA1` (`Salt/MR/MRTThmA1.lean:126`) reads `(log log h)^2 / (log h)^2` — **SQUARED**.  The v2
scoping brief's demand table (§4) writes the same term `(loglog h)²/(log h)` — **UNSQUARED**, a
strictly weaker claim, and it is the form a reader arriving at that table would port.  The Lean
statement was repaired at the PDF on 2026-08-25 with two instruments; the brief was written 08/21
and was not.  ⇒ 🔑 ***A SCOPING BRIEF IS A SNAPSHOT OF A STATEMENT THAT KEPT MOVING — DERIVE
THRESHOLDS FROM THE OBJECT, NEVER FROM THE DOCUMENT THAT SCOPED IT.***
⚠️ **AND THE DIRECTION IS THE OPPOSITE OF THE ONE I FIRST WROTE HERE — measured, not reasoned.**
A squared denominator makes the term SMALLER, hence EASIER to clear, so the correct floor is LOWER
than the brief's form demands: at `u = log h = 4/ε` the squared term is `0.0085` at `ε = 0.1` while
the unsquared term is `0.34` and FAILS. **A floor ported from the brief would therefore be too
HIGH** — conservative for this term, wasteful for the consumer, and wrong as a statement about A.1.
*The dangerous direction is the mirror — a squared-derived floor consumed by a statement still
carrying the unsquared form — and it does not arise: all three landed sites (`MRTThmA1:126`,
`MRTPortA1:95`, `MRTPropA3:3865`) carry the SQUARED form, checked here.* ⇒ ***KNOWING WHICH
TRANSCRIPTION IS RIGHT DOES NOT TELL YOU WHICH WAY THE ERROR WOULD HAVE PUSHED YOU; THAT IS A
SECOND QUESTION AND IT HAS ITS OWN ANSWER.***

⚖️ **WHY `≤ ε` AND NOT `≤ ε/3`:** each threshold clears ONE term against a demanded `ε`, and the
consumer splitting a budget across the three terms instantiates at `ε/3`.  Putting the split here
would bake a three-term assumption into a two-term interface.  **The third term, `exp(−M(f;X))`, is
not a threshold at all** — it is `M`-driven, and v2 §4 discharges it separately.

📌 **SHAPE, NOT NUMERAL** — as `H0door` says of itself.  These are never evaluated, only compared;
`H₊*(ε)` in particular is `exp(ε^(-50))`, which is not a number anyone should try to read. -/

/-- **`H₀mrt(ε)` — the `h`-side MRT floor.**  The window length above which `MRTThmA1`'s middle
error term `(loglog h)²/(log h)²` has fallen to `ε`.

The exponent is `4/ε` rather than anything sharper because the proof routes through
`log u ≤ 2√u`; a sharper floor would buy nothing, since this is compared and never evaluated. -/
noncomputable def H0mrt (ε : ℝ) : ℕ := ⌈Real.exp (4 / ε)⌉₊

/-- **`H₊*(ε)` — the `X`-side MRT floor.**  The outer scale above which `MRTThmA1`'s tail error
term `1/(log X)^{1/50}` has fallen to `ε`. -/
noncomputable def HplusStar (ε : ℝ) : ℕ := ⌈Real.exp ((1 / ε) ^ (50 : ℕ))⌉₊

/-- Both floors are genuine (positive) floor demands, so they are legal `extraFloor` arguments. -/
theorem H0mrt_pos (ε : ℝ) : 0 < H0mrt ε := Nat.ceil_pos.mpr (Real.exp_pos _)

theorem HplusStar_pos (ε : ℝ) : 0 < HplusStar ε := Nat.ceil_pos.mpr (Real.exp_pos _)

/-- The workhorse: `log u ≤ 2√u` for `u > 0`, from `log t ≤ t − 1` at `t = √u`.

⭐ This is what makes the `h`-side threshold elementary: the naive route wants `log u / u → 0` as a
limit, and a limit does not give a FLOOR. -/
theorem log_le_two_sqrt {u : ℝ} (hu : 0 < u) : Real.log u ≤ 2 * Real.sqrt u := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have h1 : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hu.le] at h1
  linarith

/-- **`H₀mrt` clears the middle term.**  For `0 < ε ≤ 1` and `h ≥ H₀mrt(ε)`,

    `(log log h)² / (log h)²  ≤  ε` .

This is the `h`-side demand of `MRTThmA1` as landed — **squared denominator**. -/
theorem mrt_middle_le_of_H0mrt {ε h : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hh : ((H0mrt ε : ℕ) : ℝ) ≤ h) :
    (Real.log (Real.log h)) ^ 2 / Real.log h ^ 2 ≤ ε := by
  -- the ceiling's defining bound pushes `h` past `exp (4/ε)`
  have hexp : Real.exp (4 / ε) ≤ h := le_trans (Nat.le_ceil _) hh
  have hh0 : 0 < h := lt_of_lt_of_le (Real.exp_pos _) hexp
  set u : ℝ := Real.log h with hu_def
  have hu4 : 4 / ε ≤ u := by
    rw [hu_def, ← Real.log_exp (4 / ε)]
    exact Real.log_le_log (Real.exp_pos _) hexp
  have h4e : (4 : ℝ) ≤ 4 / ε := by
    rw [le_div_iff₀ hε]; nlinarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  -- `(log u)^2 ≤ 4u`
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hls : Real.log u ≤ 2 * Real.sqrt u := log_le_two_sqrt hu0
  have hsq : (Real.log u) ^ 2 ≤ 4 * u := by
    have h1 : (Real.log u) ^ 2 ≤ (2 * Real.sqrt u) ^ 2 := by
      exact pow_le_pow_left₀ hlog0 hls 2
    have h2 : (2 * Real.sqrt u) ^ 2 = 4 * u := by
      rw [mul_pow, Real.sq_sqrt hu0.le]; ring
    linarith [h1, h2.le, h2.ge]
  -- `4u / u^2 = 4/u ≤ ε`
  have hfin : 4 / u ≤ ε := by
    rw [div_le_iff₀ hu0]
    have : 4 / ε * ε ≤ u * ε := by
      exact mul_le_mul_of_nonneg_right hu4 hε.le
    rw [div_mul_cancel₀ _ hε.ne'] at this
    linarith
  calc (Real.log u) ^ 2 / u ^ 2 ≤ (4 * u) / u ^ 2 := by
        gcongr
    _ = 4 / u := by field_simp
    _ ≤ ε := hfin

/-- **`H₊*` clears the tail term.**  For `0 < ε` and `X ≥ H₊*(ε)`,

    `1 / (log X)^{1/50}  ≤  ε` . -/
theorem mrt_tail_le_of_HplusStar {ε X : ℝ} (hε : 0 < ε)
    (hX : ((HplusStar ε : ℕ) : ℝ) ≤ X) :
    1 / (Real.log X) ^ ((1 : ℝ) / 50) ≤ ε := by
  have hexp : Real.exp ((1 / ε) ^ (50 : ℕ)) ≤ X := le_trans (Nat.le_ceil _) hX
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hinv0 : (0 : ℝ) < 1 / ε := by positivity
  have hL : (1 / ε) ^ (50 : ℕ) ≤ Real.log X := by
    rw [← Real.log_exp ((1 / ε) ^ (50 : ℕ))]
    exact Real.log_le_log (Real.exp_pos _) hexp
  have hLpos : (0 : ℝ) < Real.log X := lt_of_lt_of_le (by positivity) hL
  -- `(1/ε) ≤ (log X)^(1/50)`
  have hkey : 1 / ε ≤ (Real.log X) ^ ((1 : ℝ) / 50) := by
    have hmono : ((1 / ε) ^ (50 : ℕ)) ^ ((1 : ℝ) / 50)
        ≤ (Real.log X) ^ ((1 : ℝ) / 50) :=
      Real.rpow_le_rpow (by positivity) hL (by norm_num)
    have hcollapse : ((1 / ε) ^ (50 : ℕ)) ^ ((1 : ℝ) / 50) = 1 / ε := by
      rw [← Real.rpow_natCast (1 / ε) 50, ← Real.rpow_mul hinv0.le]
      norm_num
    rwa [hcollapse] at hmono
  have hpow0 : (0 : ℝ) < (Real.log X) ^ ((1 : ℝ) / 50) := Real.rpow_pos_of_pos hLpos _
  have := one_div_le_one_div_of_le hinv0 hkey
  rwa [one_div_one_div] at this

/-! ### The certificate: the budget head accepts BOTH MRT floors — and they ride DIFFERENT binders

⛔⛔ **THE QUEUE'S SEAM SAYS "instantiate the existing `∀ extraFloor` binder", AND THAT IS TRUE OF
ONE THRESHOLD, NOT BOTH.**  Measured at the head's own signature
(`log_chowla_two_budget_head_g`, `SpineFinal.lean:873-880`):

```
  extraFloor ≤ R.Hlo         a floor on the WINDOW LENGTH  ⇒  H0mrt ε rides here
  U1floor    ≤ R.Hlo         a second floor on the same quantity
  g R.Hhi R.ω ≤ R.x          the OUTER-SCALE clearance     ⇒  HplusStar ε rides HERE, not above
```
`H₀mrt` bounds `h` and `H₊*` bounds `X`, and the head keeps those in **separate slots**.  Firing
both at `extraFloor` would have placed an `X`-floor on `R.Hlo` — **a demand on the wrong quantity
that still typechecks**, because both slots are `ℕ`.  ⇒ 🔑 ***WHEN TWO THRESHOLDS BOUND DIFFERENT
QUANTITIES AND BOTH SLOTS HAVE THE SAME TYPE, THE TYPE CHECKER CANNOT TELL YOU WHICH ONE YOU
MEANT.*** The `g` slot takes a constant function; no `max` and no reshaping is needed.

⚠️ **AND THE LETTER TRAP THE SCOPING BRIEF FLAGS ONE LINE ABOVE ITS OWN THRESHOLD ROW.**  The
head's `ε` is a **`ℚ`** — the Chowla budget, `R.eps`.  This theorem's `ε` is a **`ℝ`** — the MRT
error demand.  They are different quantities and are deliberately spelled `e` and `ε` here.  *The
brief warns about exactly this for two different `A`s; the same hazard is live for `ε` and nobody
had written it down.*

⭐ Non-circularity is D-3's, unchanged: `e` and `δ₀` are fixed by the head BEFORE the floors are
quantified, so `H0mrt ε` and `HplusStar ε` are legal arguments — **the compile is the
certificate.** -/

/-- **The two MRT floors, instantiated at the budget head, with their payoffs.**  Fires
`log_chowla_two_budget_head_g` at `extraFloor := H₀mrt(ε)` and `g := fun _ _ => H₊*(ε)`, so the
regime's own window range and outer scale already clear both of `MRTThmA1`'s threshold-shaped error
terms at the demanded `ε`.

⛔ **`U1floor` is spent at `0`** — this certificate makes no claim on that slot, exactly as
`MRTPort.lean:72` records the socket doing.  ⛔ **And `exp(−M(f;X))` is untouched**: it is not a
threshold term at all, and v2 §4 discharges it separately. -/
theorem budget_head_at_mrt_floors (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (e : ℚ) (δ₀ : ℝ), 0 < e ∧ 0 < δ₀ ∧
      ∃ R : ChowlaRegime, R.eps = e ∧
        H0mrt ε ≤ R.Hlo ∧ HplusStar ε ≤ R.x ∧
        (∀ h : ℝ, ((R.Hlo : ℕ) : ℝ) ≤ h →
            (Real.log (Real.log h)) ^ 2 / Real.log h ^ 2 ≤ ε) ∧
        (∀ X : ℝ, ((R.x : ℕ) : ℝ) ≤ X →
            1 / (Real.log X) ^ ((1 : ℝ) / 50) ≤ ε) ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨e, δ₀, he, hδ₀, h⟩ := log_chowla_two_budget_head_g
  obtain ⟨R, hReps, hRfloor, -, hRx, -, hR⟩ :=
    h (H0mrt ε) 0 (fun _ _ => HplusStar ε)
  refine ⟨e, δ₀, he, hδ₀, R, hReps, hRfloor, hRx, ?_, ?_, hR⟩
  · intro hh hhle
    refine mrt_middle_le_of_H0mrt hε hε1 (le_trans ?_ hhle)
    exact_mod_cast Nat.cast_le.mpr hRfloor
  · intro X hX
    refine mrt_tail_le_of_HplusStar hε (le_trans ?_ hX)
    exact_mod_cast Nat.cast_le.mpr hRx

/-! ### The same instantiation on the L² branch — because the L¹ branch has no producer

⛔⛔ **THE CERTIFICATE ABOVE FIRES A HEAD WHOSE DOOR NOTHING SUPPLIES, AND SO DOES D-3.**  Measured
by asking, of the head's own door hypothesis, *where is it supplied?*:

```
  MRTUniformityXi    (L¹)  consumed at M4Exit:303,:396, this file ×4, SpineClose, SpineFlat,
                           Theorem23Shell …                       PRODUCED: nowhere
  MRTUniformity      (L¹)  every occurrence is `hdoor :` hypothesis position
                                                                  PRODUCED: nowhere
  MRTUniformityXiL2  (L²)  consumed by the `_sq` head family
                           PRODUCED: mrtUniformityXiL2_of_absWindowSqBound (M4Window:606)
                                     mrtUniformityXiL2H_of_absWindowSqBound (HDoorArc:394)
  adapter L² ⇒ L¹                                                 DOES NOT EXIST
  adapter L¹ ⇒ L²          mrtUniformityXiL2_of_xi (MRTDoor:255) — the OTHER direction
```

⇒ 🔑 ***A GREEN EXEMPLAR IS NOT A CURRENT ONE.***  I built the certificate above by mirroring the
landed D-3, and **D-3 predates the L² route** — it was right when written and the route moved under
it.  Copying a landed pattern copies its ROUTE ASSUMPTIONS silently, and nothing in a build can
report that.

⚖️ **THIS IS A TWIN, NOT A REPLACEMENT, AND D-3 IS NOT TOUCHED.**  The thresholds are
door-agnostic — floors on `R.Hlo` and `R.x`, which no door reads — and
`log_chowla_two_budget_head_g_sq_count` carries **the same three binders**, so the identical
instantiation lands on the branch that has a producer.  The L¹ form stays as the record.

⛔ **WHAT IS NOT CLAIMED: that the L¹ branch is DEAD.**  A deliberate interface awaiting a producer
and an abandoned one look identical to a census — that is the standing dead-branch caveat, and
which of the two this is is not a worker-tier call.  **Measured here is only: consumed many times,
produced zero times, no `L² ⇒ L¹` adapter.** -/

/-- **The MRT floors at the `_sq` (L²) head.**  Twin of `budget_head_at_mrt_floors` fired at
`log_chowla_two_budget_head_g_sq_count`, whose door `MRTUniformityXiL2` **has landed producers**.
Same instantiation: `extraFloor := H₀mrt(ε)`, `g := fun _ _ => H₊*(ε)`, `U1floor` spent at `0`.

⛔⛔ **THE `K` CONJUNCT IS RE-EXPORTED, AND DROPPING IT WAS A REAL DEFECT — CAUGHT BY WALKING ONE
STEP FURTHER INTO THE CONSUMER.**  The only landed producer of this door,
`mrtUniformityXiL2_of_absWindowSqBound` (`M4Window.lean:606`), needs **two** things from the SAME
regime: `hfloor : H₀ ≤ R.Hlo` (which the floors supply) **and** `hXi`, the `|Ξ_H| ≤ K` count bound
— whose statement is character-for-character the head's own conjunct.
⇒ *An earlier draft of this docstring said the count could be taken "from the head directly".*
**That is FALSE: the head is an `∃ R`, so firing it again yields a DIFFERENT witness**, and a floor
proved about one regime says nothing about another.  ⇒ 🔑 ***UNDER AN EXISTENTIAL, TWO FACTS ARE
COMPOSABLE ONLY IF THEY LEAVE THROUGH THE SAME WITNESS — "available upstream" IS NOT "available
TOGETHER".***  A dropped conjunct under an `∃` is not a weaker theorem, it is an UNUSABLE one, and
nothing in a build would ever say so.

✅ **AND THE FIT IS KERNEL-VERIFIED, NOT ASSERTED.**  A scratch probe fed this statement's
`hRfloor` and `hcard` into `mrtUniformityXiL2_of_absWindowSqBound` at `H₀ := H0mrt ε`, with every
campaign-open hypothesis as an explicit binder (**no `sorry` anywhere**) — it elaborates,
`EXIT=0`.  *Since the whole lesson here is that a build never checks composition, the composition
was checked on purpose rather than believed.*
📌 **NOT stated as a named theorem in the corpus, deliberately:** `M4Window` is not in this file's
import closure (+8 modules, no cycle), so where that composition should LIVE is a placement
question, not a proof question — reported rather than decided. -/
theorem budget_head_sq_at_mrt_floors (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (e : ℚ) (K δ₀ : ℝ), 0 < e ∧ 0 < K ∧ 0 < δ₀ ∧
      ∃ R : ChowlaRegime, R.eps = e ∧
        H0mrt ε ≤ R.Hlo ∧ HplusStar ε ≤ R.x ∧
        (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
            ((bigXi R.eps H).card : ℝ) ≤ K) ∧
        (∀ h : ℝ, ((R.Hlo : ℕ) : ℝ) ≤ h →
            (Real.log (Real.log h)) ^ 2 / Real.log h ^ 2 ≤ ε) ∧
        (∀ X : ℝ, ((R.x : ℕ) : ℝ) ≤ X →
            1 / (Real.log X) ^ ((1 : ℝ) / 50) ≤ ε) ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨e, K, δ₀, he, hK, hδ₀, h⟩ := log_chowla_two_budget_head_g_sq_count
  obtain ⟨R, hReps, hRfloor, -, hRx, hcard, -, hR⟩ :=
    h (H0mrt ε) 0 (fun _ _ => HplusStar ε)
  refine ⟨e, K, δ₀, he, hK, hδ₀, R, hReps, hRfloor, hRx, hcard, ?_, ?_, hR⟩
  · intro hh hhle
    refine mrt_middle_le_of_H0mrt hε hε1 (le_trans ?_ hhle)
    exact_mod_cast Nat.cast_le.mpr hRfloor
  · intro X hX
    refine mrt_tail_le_of_HplusStar hε (le_trans ?_ hX)
    exact_mod_cast Nat.cast_le.mpr hRx

end Salt.MR
