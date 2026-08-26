/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Window
import Salt.Entropy.Chowla.ShiftFork

/-!
# QUEUE 7b — the arc supply at the TWISTED frequency set (`HDoorArc`)

Nodes **N1–N3** (the arc transfer) and **N4a–N4d** (the `h`-`L²` adapter chain) of the
helm/Fable commission
`seat/briefs/2026-08-26-helm-COMMISSION-7b-hdoor.md` (freeze v2, 4-refuter pass). Worker-tier;
the design is closed and the shape is picked — **(a ∧ b)**, the NAMED transfer chain with `h`
visible in every statement, over (c)'s respelling of the door.

## What 7b's blocker actually was

Membership in `bigXiH h eps H` is largeness at the **TWISTED** frequency `h·ξ`
(`mem_bigXiH_iff`: `ξ ∈ bigXiH h eps H ↔ (h : ZMod H) * ξ ∈ bigXi eps H`), while the L² h-door
integrates at the **UNTWISTED** `−ξ.val/H` and the landed arc supply
(`M4Window.nearRatTight_of_bigXiArcTight`) certifies that frequency only for members of the
UNTWISTED set.  The transfer exists and costs a denominator-cap inflation of **exactly `h`**;
N1–N3 are that transfer, stated so the `h` is on the page at every step, and N4a–N4d carry it
through the landed `L²` adapter chain to the twisted door predicate `MRTUniformityXiL2H`.

⛔ **B₅ stays `12` throughout — iron rule 1.**  The cap that moves is the ALLOWANCE
`arcDen B₅ H → h · arcDen B₅ H`, never the exponent.
-/

open scoped BigOperators
open MeasureTheory

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

/-! ## N4a–N4d — the `h`-`L²` adapter chain

Clones of the **`L²` chain** in `M4Window.lean` (§5, `:397-627`), NOT of the `L¹` adapter.
Two literal substitutions throughout: the summation set `bigXi R.eps H → bigXiH h R.eps H`,
and the arc/socket cap `arcDen B₅ H → (h : ℝ) * arcDen B₅ H`.  The cores' proofs use nothing
about `bigXi` beyond `Finset`-hood, and nothing about the cap beyond its being the SAME real
in `harc` and `hsock` — which is exactly why N3's inflated supply plugs straight in.

⛔ **The cap moves; `B₅` does not** (iron rule 1).  `(h : ℝ) * arcDen B₅ H` is the allowance
N3 hands out, and `hsock` must be stated at that same inflated allowance — which is what makes
its supplier `M4SievedDoorSqH` (N4s) and **not** the landed `M4SievedDoorSq`.
-/

/-- **N4a** (`sum_bigXiH_norm_windowExpSum_sq_le`) — the `Ξ_H`-summed `L²` arc adapter at the
twisted set, the clone of `sum_bigXi_norm_windowExpSum_sq_le` (`M4Window.lean:397-475`).

The census is the landed one, unchanged: **the count `K` multiplies ONLY the sieved leg** (the
socket grades at each tight-major `α`, so summing over the set costs the cardinality), and
**the insert leg is paid ONCE** (the raw−sieved difference is `α`-independent, so its total
Fourier mass is a single object).  The two `2`s are the `(a+b)² ≤ 2a² + 2b²` split.

⭐ **`hins` is FREE at this set** — `parseval_insert_budget_door`
(`M4ParsevalStone.lean:341-343`) quantifies over an ARBITRARY `Xi : Finset (ZMod H)`, so it is
instantiated at `Xi := bigXiH h R.eps H` with no re-derivation of the Parseval stone.

⛔ **`hsock` is at the INFLATED cap and that is load-bearing.**  A per-`α` socket at the landed
`arcDen B₅ H` does NOT discharge it: `nearRatTight_mono` raises caps one way, so the `α`-set at
`h · arcDen B₅ H` strictly CONTAINS the landed socket's and the implication runs backwards.
The supplier is `M4SievedDoorSqH` (N4s), declared open. -/
theorem sum_bigXiH_norm_windowExpSum_sq_le (h : ℕ) (R : ChowlaRegime) (a e : ℕ → ℂ)
    (Bsieve : ℕ → ℝ) (K Binsert : ℝ) {B₅ : ℝ} {H₀ : ℕ}
    (hsplit : ∀ m, lamCoeff m = a m + e m)
    (hfloor : H₀ ≤ R.Hlo)
    (harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXiH h R.eps H,
      NearRatTight ((h : ℝ) * arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (hB0 : ∀ H : ℕ, 0 ≤ Bsieve H)
    (hsock : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight ((h : ℝ) * arcDen B₅ H) H α →
        (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
          ≤ Bsieve H * (H : ℝ) ^ 2)
    (hXi : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      ((bigXiH h R.eps H).card : ℝ) ≤ K)
    (hins : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (∑ ξ ∈ bigXiH h R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω)) ≤ Binsert) :
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (∑ ξ ∈ bigXiH h R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
        ≤ K * (2 * Bsieve H) + 2 * Binsert := by
  intro H _ hlo hhi
  have hH0 : H ≠ 0 := NeZero.ne H
  have hHpos : (0 : ℝ) < (H : ℝ) := by positivity
  have hinvpos : (0 : ℝ) < 1 / (H : ℝ) ^ 2 := by positivity
  have hfun : lamCoeff = fun m => a m + e m := funext hsplit
  -- ⟦the per-frequency line⟧ arc → socket → the `(a+b)²` split, at one `ξ`.
  have hterm : ∀ ξ ∈ bigXiH h R.eps H,
      (1 / (H : ℝ) ^ 2) * (∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
        ≤ 2 * Bsieve H + 2 * ((1 / (H : ℝ) ^ 2) *
            ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω)) := by
    intro ξ hξ
    have harcξ := harc H (le_trans hfloor hlo) ξ hξ
    have hrw : (∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
        = ∫ n, ‖absWindowSum (fun m => a m + e m) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
            ∂(logMeasure R.x R.ω) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
      simp only [norm_windowExpSum_eq_absWindowSum, hfun]
    rw [hrw]
    have hspl := integral_norm_absWindowSum_sq_split R.x R.ω H a e (-(ξ.val : ℝ) / (H : ℝ))
    have hs := hsock H hlo hhi (-(ξ.val : ℝ) / (H : ℝ)) harcξ
    have hA : (1 / (H : ℝ) ^ 2) * (∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
        ∂(logMeasure R.x R.ω)) ≤ Bsieve H := by
      have h := mul_le_mul_of_nonneg_left hs hinvpos.le
      have heq : (1 / (H : ℝ) ^ 2) * (Bsieve H * (H : ℝ) ^ 2) = Bsieve H := by
        field_simp
      linarith [h, heq.le, heq.ge]
    have hmul := mul_le_mul_of_nonneg_left hspl hinvpos.le
    have hexp : (1 / (H : ℝ) ^ 2) *
        (2 * (∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω))
          + 2 * ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω))
        = 2 * ((1 / (H : ℝ) ^ 2) * ∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω))
          + 2 * ((1 / (H : ℝ) ^ 2) * ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω)) := by ring
    rw [hexp] at hmul
    linarith
  -- ⟦the census⟧ the sieved leg pays the count `K`; the insert leg pays once.
  have hcard := hXi H hlo hhi
  have hI := hins H hlo hhi
  have h2B : (0 : ℝ) ≤ 2 * Bsieve H := by have := hB0 H; linarith
  have hKB := mul_le_mul_of_nonneg_right hcard h2B
  calc (∑ ξ ∈ bigXiH h R.eps H, (1 / (H : ℝ) ^ 2) *
          ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ ∑ _ξ ∈ bigXiH h R.eps H, (2 * Bsieve H + 2 * ((1 / (H : ℝ) ^ 2) *
          ∫ n, ‖absWindowSum e H n (-(_ξ.val : ℝ) / (H : ℝ))‖ ^ 2
            ∂(logMeasure R.x R.ω))) := Finset.sum_le_sum hterm
    _ = ((bigXiH h R.eps H).card : ℝ) * (2 * Bsieve H)
          + 2 * ∑ ξ ∈ bigXiH h R.eps H, (1 / (H : ℝ) ^ 2) *
              ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                ∂(logMeasure R.x R.ω) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    _ ≤ K * (2 * Bsieve H) + 2 * Binsert := by linarith

/-- **N4b** (`sum_bigXiH_norm_windowExpSum_sq_le_sub`) — N4a at the SUBTRACTIVE spelling of the
split, for a supplier whose insert leg arrives as `λ − a` rather than as a named `e`.  Clone of
`sum_bigXi_norm_windowExpSum_sq_le_sub` (`M4Window.lean:480-502`); same theorem, `hsplit`
discharged by `ring`. -/
theorem sum_bigXiH_norm_windowExpSum_sq_le_sub (h : ℕ) (R : ChowlaRegime) (a : ℕ → ℂ)
    (Bsieve : ℕ → ℝ) (K Binsert : ℝ) {B₅ : ℝ} {H₀ : ℕ}
    (hfloor : H₀ ≤ R.Hlo)
    (harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXiH h R.eps H,
      NearRatTight ((h : ℝ) * arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (hB0 : ∀ H : ℕ, 0 ≤ Bsieve H)
    (hsock : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight ((h : ℝ) * arcDen B₅ H) H α →
        (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
          ≤ Bsieve H * (H : ℝ) ^ 2)
    (hXi : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      ((bigXiH h R.eps H).card : ℝ) ≤ K)
    (hins : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (∑ ξ ∈ bigXiH h R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖absWindowSum (fun m => lamCoeff m - a m) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω)) ≤ Binsert) :
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (∑ ξ ∈ bigXiH h R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
        ≤ K * (2 * Bsieve H) + 2 * Binsert :=
  sum_bigXiH_norm_windowExpSum_sq_le h R a (fun m => lamCoeff m - a m) Bsieve K Binsert
    (fun m => by ring) hfloor harc hB0 hsock hXi hins

/-- **N4c** (`sum_bigXiH_norm_windowExpSum_sq_le_parseval`) — N4a at the Parseval stone's own
spelling, the byte-plug for `parseval_insert_budget_door` (`M4ParsevalStone.lean:341`), whose
exit carries the `(1/H²)` OUTSIDE the `ξ`-sum and whose integrand is the *difference of two
window sums*, not a window sum of a difference sequence.  Clone of
`sum_bigXi_norm_windowExpSum_sq_le_parseval` (`M4Window.lean:510-557`); the two spellings are
identified through `absWindowSum_add_coeff` and `Finset.mul_sum`, no new analysis.

⭐ The stone's `Xi` binder being arbitrary is what makes this a substitution rather than a
port: at `Xi := bigXiH h R.eps H` its conclusion is already this `hins`. -/
theorem sum_bigXiH_norm_windowExpSum_sq_le_parseval (h : ℕ) (R : ChowlaRegime) (a : ℕ → ℂ)
    (Bsieve : ℕ → ℝ) (K Binsert : ℝ) {B₅ : ℝ} {H₀ : ℕ}
    (hfloor : H₀ ≤ R.Hlo)
    (harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXiH h R.eps H,
      NearRatTight ((h : ℝ) * arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (hB0 : ∀ H : ℕ, 0 ≤ Bsieve H)
    (hsock : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight ((h : ℝ) * arcDen B₅ H) H α →
        (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
          ≤ Bsieve H * (H : ℝ) ^ 2)
    (hXi : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      ((bigXiH h R.eps H).card : ℝ) ≤ K)
    (hins : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ bigXiH h R.eps H,
        ∫ n, ‖absWindowSum lamCoeff H n (-(ξ.val : ℝ) / (H : ℝ))
            - absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω) ≤ Binsert) :
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (∑ ξ ∈ bigXiH h R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
        ≤ K * (2 * Bsieve H) + 2 * Binsert := by
  refine sum_bigXiH_norm_windowExpSum_sq_le_sub h R a Bsieve K Binsert hfloor harc hB0
    hsock hXi ?_
  intro H _ hlo hhi
  have hsub : ∀ (n : ℕ) (α : ℝ),
      absWindowSum (fun m => lamCoeff m - a m) H n α
        = absWindowSum lamCoeff H n α - absWindowSum a H n α := by
    intro n α
    have h := absWindowSum_add_coeff a (fun m => lamCoeff m - a m) H n α
    have hfun : (fun m => a m + (lamCoeff m - a m)) = lamCoeff := funext fun m => by ring
    rw [hfun] at h
    rw [h]
    ring
  have hcongr : (∑ ξ ∈ bigXiH h R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖absWindowSum (fun m => lamCoeff m - a m) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
      = (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ bigXiH h R.eps H,
        ∫ n, ‖absWindowSum lamCoeff H n (-(ξ.val : ℝ) / (H : ℝ))
            - absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
    simp only [hsub]
  rw [hcongr]
  exact hins H hlo hhi

/-- ⭐⭐ **N4d** (`mrtUniformityXiL2H_of_absWindowSqBound`) — THE CLOSE ONTO THE TWISTED SUMMED
DOOR: N4a delivered as `MRTUniformityXiL2H h R ρ` (`ShiftFork.lean:523-527`).  Clone of
`mrtUniformityXiL2_of_absWindowSqBound` (`M4Window.lean:606-627`).

`hρ` is the one thing the adapter cannot supply: the door's grade `ρ` is `H`-free while the
adapter's right-hand side carries the socket grade at the running `H`.  Any `H`-uniform ceiling
over `[R.Hlo, R.Hhi]` does it.

⛔ **SIX SLOTS, AND `hXi` IS NOT DROPPABLE.**  It is tempting to read the landed `L²` seam's
absence of a count hypothesis (`contradiction_of_mrtDoorXiL2H` has none) as licence to drop
`hXi` here; that is the wrong reading of the `K`-free `δ`.  The count is consumed HERE, once,
against the sieved leg only — the Σ-shaped conclusion is simply unreachable without it.  What
the restructure buys is that the count never reaches the SEAM, not that it is never paid.

📌 At shift `h` the set is the `μ_h`-preimage of `Ξ_H`, of cardinality `≤ gcd(h,H)·|Ξ_H|`, so
the `K` supplied here is the inflated one — N5's composition of `bigXiH_card_le_mul` with
`bigXi_bounded_500`'s third conjunct, never `bigXiH_bounded`. -/
theorem mrtUniformityXiL2H_of_absWindowSqBound (h : ℕ) (R : ChowlaRegime) (a e : ℕ → ℂ)
    (Bsieve : ℕ → ℝ) (K Binsert ρ : ℝ) {B₅ : ℝ} {H₀ : ℕ}
    (hsplit : ∀ m, lamCoeff m = a m + e m)
    (hfloor : H₀ ≤ R.Hlo)
    (harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXiH h R.eps H,
      NearRatTight ((h : ℝ) * arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (hB0 : ∀ H : ℕ, 0 ≤ Bsieve H)
    (hsock : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight ((h : ℝ) * arcDen B₅ H) H α →
        (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
          ≤ Bsieve H * (H : ℝ) ^ 2)
    (hXi : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      ((bigXiH h R.eps H).card : ℝ) ≤ K)
    (hins : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (∑ ξ ∈ bigXiH h R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω)) ≤ Binsert)
    (hρ : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → K * (2 * Bsieve H) + 2 * Binsert ≤ ρ) :
    MRTUniformityXiL2H h R ρ := by
  intro H _ hlo hhi
  exact le_trans (sum_bigXiH_norm_windowExpSum_sq_le h R a e Bsieve K Binsert hsplit hfloor
    harc hB0 hsock hXi hins H hlo hhi) (hρ H hlo hhi)

end Salt.MR
