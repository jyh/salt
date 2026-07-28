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

The Matomäki–Radziwiłł–Tao short-interval door (Tao 1509.05422 Prop. 2.4, proven
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
`(log H)^{-5/4}` delivered by the Matomäki–Radziwiłł–Tao short-interval theorem
(Tao 1509.05422 Prop. 2.4).  It is the `W^{-1/4}` saving of the character
expansion read at the door's own sieve parameter `W = (log H)^5` (S7's `B5 = 5`;
`docs/exploration/chi-check-0724.md`, KILL-CHECK 2).  Decreasing in `H`
(`doorGrade_anti`) — longer windows buy a better door. -/
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
  obtain ⟨R, hReps, hRfloor, hRU1, hRg, hR⟩ := h (H0door δ₀) U1floor g
  refine ⟨ε, δ₀, hε, hδ₀, R, hReps, hRfloor, hRU1, hRg, ?_, hR⟩
  intro H hH
  have hfloor : H0door δ₀ ≤ H := le_trans hRfloor hH
  refine ⟨doorGrade_pos ?_, doorGrade_le_of_H0door_le hδ₀ hfloor⟩
  have h4 : 4000000 ≤ R.Hlo := R.hHlo_floor
  omega

end Salt.MR
