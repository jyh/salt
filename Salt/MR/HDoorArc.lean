/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Window
import Salt.Entropy.Chowla.ShiftFork

/-!
# QUEUE 7b — the arc supply at the TWISTED frequency set (`HDoorArc`)

Nodes **N1–N3** of the helm/Fable commission
`seat/briefs/2026-08-26-helm-COMMISSION-7b-hdoor.md` (freeze v2, 4-refuter pass). Worker-tier;
the design is closed and the shape is picked — **(a ∧ b)**, the NAMED transfer chain with `h`
visible in every statement, over (c)'s respelling of the door.

## What 7b's blocker actually was

Membership in `bigXiH h eps H` is largeness at the **TWISTED** frequency `h·ξ`
(`mem_bigXiH_iff`: `ξ ∈ bigXiH h eps H ↔ (h : ZMod H) * ξ ∈ bigXi eps H`), while the L² h-door
integrates at the **UNTWISTED** `−ξ.val/H` and the landed arc supply
(`M4Window.nearRatTight_of_bigXiArcTight`) certifies that frequency only for members of the
UNTWISTED set.  The transfer exists and costs a denominator-cap inflation of **exactly `h`**;
these three nodes are that transfer, stated so the `h` is on the page at every step.

⛔ **B₅ stays `12` throughout — iron rule 1.**  The cap that moves is the ALLOWANCE
`arcDen B₅ H → h · arcDen B₅ H`, never the exponent.
-/

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## N1 — integer translation invariance -/

/-- **N1** (`nearRatTight_intCast_add`).  `NearRatTight` is invariant under an integer shift of
its frequency.  BOTH arms are carried: the route below uses `.mp`, and `.mpr` is stated because
a one-armed translation lemma is the kind of thing a later consumer silently re-proves.

Witnesses: `.mp` sends `(a, q) ↦ (a − k·q, q)` and `.mpr` sends `(a, q) ↦ (a + k·q, q)`.  The
denominator `q` and the radius `Q/(q·H)` are untouched in each direction — only the numerator
moves — so no side condition beyond the `0 < q` already inside the predicate. -/
theorem nearRatTight_intCast_add {Q : ℝ} {H : ℕ} {α : ℝ} (k : ℤ) :
    NearRatTight Q H (α + (k : ℝ)) ↔ NearRatTight Q H α := by
  constructor
  · rintro ⟨a, q, hq, hqQ, hd⟩
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    refine ⟨a - k * (q : ℤ), q, hq, hqQ, ?_⟩
    have hrw : α - ((a - k * (q : ℤ) : ℤ) : ℝ) / (q : ℝ)
        = α + (k : ℝ) - (a : ℝ) / (q : ℝ) := by
      field_simp
      push_cast
      ring
    rw [hrw]
    exact hd
  · rintro ⟨a, q, hq, hqQ, hd⟩
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    refine ⟨a + k * (q : ℤ), q, hq, hqQ, ?_⟩
    have hrw : α + (k : ℝ) - ((a + k * (q : ℤ) : ℤ) : ℝ) / (q : ℝ)
        = α - (a : ℝ) / (q : ℝ) := by
      field_simp
      push_cast
      ring
    rw [hrw]
    exact hd

/-! ## N2 — dividing the frequency by `h`, at the cost of `h` in the cap -/

/-- **N2** (`nearRatTight_div_nat`).  Tightness at `h·β` with allowance `Q` gives tightness at
`β` with allowance `h·Q`.  Witness `(a, q) ↦ (a, h·q)`.

⭐ **THE SLACK IS `h`, NOT `h²`, and the reason is an exact cancellation:** the inflated
allowance and the inflated witness denominator cancel in the radius,
`(h·Q)/((h·q)·H) = Q/(q·H)`, so the entire margin is the single `1/h` contraction of the
distance `|β − a/(h·q)| = |h·β − a/q| / h`.  Pricing it as `h²` would be reading the two
inflations as independent.

No `0 ≤ Q` slot is needed: the hypothesis's own witness already forces `1 ≤ q ≤ Q`. -/
theorem nearRatTight_div_nat {Q : ℝ} {H h : ℕ} {β : ℝ} (hh : 0 < h)
    (hβ : NearRatTight Q H ((h : ℝ) * β)) :
    NearRatTight ((h : ℝ) * Q) H β := by
  obtain ⟨a, q, hq, hqQ, hd⟩ := hβ
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hQ1 : (1 : ℝ) ≤ Q := by
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  refine ⟨a, h * q, Nat.mul_pos hh hq, ?_, ?_⟩
  · push_cast
    exact mul_le_mul_of_nonneg_left hqQ hhR.le
  · -- the distance contracts by exactly `1/h`; the radius is unchanged by the cancellation
    have hdist : β - (a : ℝ) / ((h * q : ℕ) : ℝ)
        = ((h : ℝ) * β - (a : ℝ) / (q : ℝ)) / (h : ℝ) := by
      push_cast
      field_simp
    have hrad : ((h : ℝ) * Q) / (((h * q : ℕ) : ℝ) * (H : ℝ)) = Q / ((q : ℝ) * (H : ℝ)) := by
      push_cast
      by_cases hH : (H : ℝ) = 0
      · rw [hH]; simp
      · field_simp
    rw [hdist, hrad, abs_div, abs_of_pos hhR]
    rw [div_le_iff₀ hhR]
    have h1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
    have hQq : (0 : ℝ) ≤ Q / ((q : ℝ) * (H : ℝ)) := by positivity
    nlinarith [hd, hQq]

/-! ## N3 — the arc supply, transported to the twisted set -/

/-- ⭐⭐ **N3** (`nearRatTight_of_bigXiArcTight_H`) — the commission's target for this file.
`M4Window.nearRatTight_of_bigXiArcTight` certifies `−ξ.val/H` for members of the UNTWISTED
`bigXi`; this certifies it for members of the TWISTED `bigXiH h`, at the allowance inflated by
exactly `h`.

**Route, all three steps named.**  `mem_bigXiH_iff` turns `ξ ∈ bigXiH h eps H` into
`η ∈ bigXi eps H` for `η := (h : ZMod H) * ξ`, so the landed supply applies AT `η`.  The two
frequencies differ by an integer and a factor `h`:

  `−η.val/H = h·(−ξ.val/H) + k`,   `k := (h * ξ.val) / H`,  sign POSITIVE,

because `η.val = (h * ξ.val) % H` and `H·k + η.val = h * ξ.val`.  N1 strips the `+k`; N2
divides by `h` and pays for it in the cap.

⛔ **THE CAST SEAM IS ADDITIVE, NEVER SUBTRACTIVE.**  The identity is taken in the form
`H·k + η.val = h·ξ.val` (`Nat.div_add_mod`), NOT as `η.val = h·ξ.val − H·k`: the latter is
ℕ-TRUNCATED subtraction and `push_cast` stalls on it silently rather than failing.

📌 **The `∃ H₀` guard is INHERITED AND KEPT, deliberately** — it is not simplifiable to bare
`NeZero`.  The `h`-inflated cap clears `1` at small `H` for large `h` (at `H = 2` once
`h ≥ 116`), so the `h`-form is non-vacuous in a regime the `h = 1` form is not, and the guard is
what keeps that corner honest rather than accidentally true.
⚠️ `h = 1` is a passing CONTROL on this chain, never a validation: at `h = 1` the twist, the
shift `k`, and N2's scaling are all simultaneously trivial. -/
theorem nearRatTight_of_bigXiArcTight_H {B₅ : ℝ} (harc : BigXiArcTight B₅)
    {eps : ℚ} (heps : 0 < eps) {h : ℕ} (hh : 0 < h) :
    ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXiH h eps H,
      NearRatTight ((h : ℝ) * arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)) := by
  obtain ⟨H₀, hH₀⟩ := nearRatTight_of_bigXiArcTight harc heps
  refine ⟨H₀, ?_⟩
  intro H _ hH ξ hξ
  have hHpos : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hHpos
  -- the twisted member is an untwisted member of `bigXi`
  have hη : (h : ZMod H) * ξ ∈ bigXi eps H := mem_bigXiH_iff.mp hξ
  have hbase := hH₀ H hH ((h : ZMod H) * ξ) hη
  -- the val identity, and the ADDITIVE cast seam
  have hval : ((h : ZMod H) * ξ).val = (h * ξ.val) % H := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  have hdm : H * ((h * ξ.val) / H) + (h * ξ.val) % H = h * ξ.val :=
    Nat.div_add_mod (h * ξ.val) H
  have hcast : (H : ℝ) * (((h * ξ.val) / H : ℕ) : ℝ) + ((((h * ξ.val) % H : ℕ)) : ℝ)
      = (h : ℝ) * (ξ.val : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hdm
  -- the frequency identity
  have hfreq : -((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ)
      = (h : ℝ) * (-(ξ.val : ℝ) / (H : ℝ)) + ((((h * ξ.val) / H : ℕ) : ℤ) : ℝ) := by
    rw [hval]
    -- ⛔ NOT `push_cast`: it rewrites the ℕ-division's cast into an ℤ-DIVISION OF CASTS,
    -- which is a different term (`Int.ediv` vs `Nat.div`) and leaves the goal open.
    have hkz : ((((h * ξ.val) / H : ℕ) : ℤ) : ℝ) = (((h * ξ.val) / H : ℕ) : ℝ) :=
      Int.cast_natCast _
    rw [hkz]
    -- the linear step, on hcast's own atoms and nothing else
    have key : -((((h * ξ.val) % H : ℕ)) : ℝ)
        = (h : ℝ) * (-(ξ.val : ℝ)) + (((h * ξ.val) / H : ℕ) : ℝ) * (H : ℝ) := by
      linarith [hcast]
    -- then one division, with `H ≠ 0` discharged
    calc -((((h * ξ.val) % H : ℕ)) : ℝ) / (H : ℝ)
        = ((h : ℝ) * (-(ξ.val : ℝ)) + (((h * ξ.val) / H : ℕ) : ℝ) * (H : ℝ)) / (H : ℝ) := by
          rw [key]
      _ = (h : ℝ) * (-(ξ.val : ℝ) / (H : ℝ)) + (((h * ξ.val) / H : ℕ) : ℝ) := by
          field_simp
  rw [hfreq] at hbase
  -- N1 strips the integer shift, N2 divides the frequency and inflates the cap
  exact nearRatTight_div_nat hh ((nearRatTight_intCast_add _).mp hbase)

end Salt.MR
