/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# λ-BV wave 2-S, step F3 — THE REGIME PAIRING (Entropy half): share the tower

The affine seam `contradiction_of_mrtDoorXiL2Aff` (`StrideFork.lean:759`) consumes the `L²`
door at the AFFINE target regime `R_aff : ChowlaRegimeAff`, through `logMeasureAff R.a R.x R.ω`
(the log-measure of `(x/ω, x]` pushed along `n ↦ a·n`) and the set `bigXiAff`.  The landed door
supply is the road's own `∃ R` at a PLAIN regime `R_door` through `logMeasure R.x R.ω`.  The door
does not transport along `regimeEnlargeX` (the measure moves with `x`), and no lemma compares the
towers at bases `B` and `a·B`; so the pairing is a NODE (F1 verdict item 8, F2 verdict A5), priced
in the math seat's price brief (`2026-09-04-math-PRICE-lbv-w2S-F3-regime-pairing.md`) and frozen
in its freeze brief (`2026-09-04-math-FREEZE-lbv-w2S-F3.md`).

THE DESIGN — SHARE THE TOWER, SHRINK THE SCALE.  Given `R_door` with `a ∣ R_door.a·R_door.Hlo`
and `a ∣ R_door.x`, the affine regime is `R_door` with `x := x/a`, `Hlo := R_door.a·Hlo/a`,
`a := a`, EVERYTHING ELSE VERBATIM (`regimeShrinkX_stride`).  Its tower is LITERALLY the door
regime's (`regimeShrinkX_stride_tower`: `chowlaTower C0 a (R.a·Hlo/a) = chowlaTower C0 R.a Hlo`),
so `hfit`/`hJcon` transfer by `chowlaTower_eq_base_one`; the `x`-fields at `x/a` are the
`StrideScale` conjuncts the RECEIPT exports (the multiplier is threaded through the road on the
MR side, `StridePairReceipt.lean`, because the outer-scale rider cannot carry the `hPHheadroom`
floor scaled by `a` — freeze §1(B)).  The affine pushforward measure at `(x/a, ω)` is supported on
multiples of `a` that all lie INSIDE the plain window at `(x, ω)` (the image is a subset — v2,
refuter R4: zero multiples fall outside), so the plain `L²` door over the affine set transports
to the affine door at grade `a·(Z_x/Z_{x/a})·ρ + (endpoint)`, the endpoint a NAMED nonnegative
slack term — every factor EXPLICIT in `mrtUniformityXiL2AffW_of_set`.

THE STATEMENT ACT (Fable tier, freeze §3): the affine door at TAO'S OWN RANGE —
`MRTUniformityXiL2AffW`, quantified over `H` with `R.a ∣ H` and `R.a·R.Hlo ≤ H`.  F1-D2's
`R.Hlo ≤ H` was copied from the `h`-door and is WIDER than the affine windows (which start at
`a·Hlo`, `Regime.lean:38`); and the affine arc bridge (`StridePairReceipt.nearRatTight_of_bigXiAff`)
needs the `1/H` grid to carry `(b+h)η/a` EXACTLY, which is `a ∣ H` (Tao textdump:1296-1300,
"H ≡ 0 (mod a)").  F1-D2 is untouched (iron rule 1); the wide door implies the windowed one
(`mrtUniformityXiL2AffW_of_aff`), and the seam is cloned at the new range
(`contradiction_of_mrtDoorXiL2AffW`), whose entropy-side caller supplies `a ∣ H` from
`dvd_chowlaTower`.

HONEST LABEL.  Nothing here produces a door: the receipt is the MR half's.  Nothing here bears on
twin primes.  Every declaration below is statement-only at the freeze (sorry-bodied, recipe in
the docstring), built as a module through `../saltbuild.sh`; NO executor fires before the helm's
refuter verdict.  ⛔ MERGE FENCE (iron rule 2): `math/lbv-w2s-f3` never reaches `main` until every
obligation in this file and in `StridePairReceipt.lean` lands sorry-free.

Degenerate values (the W4 law): `a = 0` is excluded by `1 ≤ a` wherever division by `a` occurs;
`R.a * R.Hlo / a` at `a ∤ R.a·R.Hlo` would silently floor — every consumer carries `hdiv`;
`H = 0` is excluded by `[NeZero H]`; at `(a, b) = (1, 0)` the windowed door is the landed
`MRTUniformityXiL2H` (`mrtUniformityXiL2AffW_one_zero_eq`).
-/
import Salt.Entropy.Chowla.StrideFork
import Salt.Entropy.Chowla.TowerFlatBuilder
import Mathlib

-- v2 (refuter verdict A5): the transport's integrand bound `‖windowExpSum H n α‖ ≤ H` lives in
-- `MRTDoor.lean` as a `private` lemma (its `Salt.MR` twin `norm_windowExpSum_le` is unreachable
-- from an Entropy module).  Reached by `open private`, the corpus's sanctioned device
-- (`DoorReceipt.lean:64` does the same for `uniformCap_shuffle`).
open private norm_windowExpSum_trivial from Salt.Entropy.Chowla.MRTDoor

open MeasureTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ## F3-P1 — the multiplier's export: the `x`-floors at `x/a` -/

/-- **F3-P1 (def).**  What the receipt exports about the door regime's outer scale so that the
scale can be divided by `a`: `a ∣ x` and the six `x`-fields of `ChowlaRegime` (`Regime.lean`:
`hx`, `hωx`, `hheadroom`, `hheadroom'`, `hPHheadroom`, `hxbig`) read at `x / a` with every other
field the regime's own.  Produced on the MR side by the multiplier builder
(`chowlaRegimeFlat_exists_param_gen_ceiling_mul`: `x := a·x₀`, the floors at `x₀` are the
builder's own) and threaded INERT through the road (no hop reads `R.x` except through these
fields and the ceiling).  Consumed by `regimeShrinkX_stride`. -/
def StrideScale (a : ℕ) (R : ChowlaRegime) : Prop :=
  a ∣ R.x ∧ 2 ≤ R.x / a ∧ R.ω ≤ R.x / a ∧ R.Hhi ≤ R.x / a / R.ω ∧
    8 * (R.Hhi : ℝ) * Real.log R.Hhi * Real.log R.Hhi ≤ ((R.x / a / R.ω : ℕ) : ℝ) ∧
    8 * ((4 ^ ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) ^ 2 * (R.ω : ℝ) ≤ ((R.x / a : ℕ) : ℝ) ∧
    (R.ω : ℝ) * (R.Hhi : ℝ) + 48 * (R.ω : ℝ) * (1 + 2 / (R.eps : ℝ) ^ 2) / (R.eps : ℝ)
      ≤ ((R.x / a : ℕ) : ℝ)

/-- **F3-P1a (class A).**  `StrideScale 1 R` holds for every regime: `Nat.div_one` turns each
conjunct into the regime's own field (`R.hx`, `R.hωx`, `R.hheadroom`, `R.hheadroom'`,
`R.hPHheadroom`, `R.hxbig`); `one_dvd`.  The conservativity control at `a = 1`. -/
theorem strideScale_one (R : ChowlaRegime) : StrideScale 1 R := by
  sorry

/-! ## F3-P2 — the tower clears its base at every `C0 ≥ 2` -/

/-- **F3-P2 (class A).**  `B ≤ chowlaTower C0 1 B j` at any `C0 ≥ 2` and base `B ≥ 4·10⁶` — the
general-`C0` twin of `chowlaTower_base_ge` (`RegimeParam.lean`, literal `C0 = 2`).  `induction j`;
`zero`: `change B ≤ 1 * B; omega`; `succ`: `tower_mult_ge_two hC0 (le_trans hB ih)`
(`Tower.lean:73`) and `chowlaTower_succ`, then `Nat.le_mul_of_pos_right`.  Feeds `hHlohi` of the
shrunk regime: `R.a·R.Hlo/a ≤ R.a·R.Hlo = chowlaTower C0 R.a R.Hlo 0 ≤ chowlaTower … J ≤ R.Hhi`
through `chowlaTower_eq_base_one`. -/
theorem chowlaTower_ge_base {C0 B : ℕ} (hC0 : 2 ≤ C0) (hB : 4000000 ≤ B) (j : ℕ) :
    B ≤ chowlaTower C0 1 B j := by
  sorry

/-! ## F3-P3 — the shrunk regime: share the tower -/

/-- **F3-P3 (class B) — THE SHRINK.**  The door regime `R` with `x := R.x / a`, `Hlo :=
R.a * R.Hlo / a`, `a := a`, every other field VERBATIM.  Field by field:
`hx`, `hωx`, `hheadroom`, `hheadroom'`, `hPHheadroom`, `hxbig` are `hs`'s six conjuncts
(`hheadroom'` and the two real-valued ones read `R.x / a / R.ω` and `R.x / a` LITERALLY as the
new fields do — no cast lemma needed); `hω`, `heps`, `heps1`, `hC0`, `hHlohi`-free fields copy.
`ha := ha`.  `hHlo : a ≤ R.a*R.Hlo/a` from `hloM` and `ha1096` (`omega`).  `hHlo_floor := hloM`.
`hcoprime : (a : ℚ) ≤ eps²·(R.a*R.Hlo/a)/2` — from `hlo4` cast to `ℚ`: `4·⌈1/ε⌉₊⁴ ≤ Hlo'` gives
`4 ≤ ε²·Hlo'·ε²·⌈1/ε⌉₊²/…`; the builder's own script (`TowerFlatBuilder.lean:268-276`, `h4le :
4 ≤ eps²·Hlo`) yields `2 ≤ eps²·Hlo'/2 · (1/ε²)`… — simplest: from `hlo4`, `(1/ε)⁴ ≤ ⌈1/ε⌉₊⁴ ≤
Hlo'/4`, so `ε²·Hlo'/2 ≥ 2/ε² ≥ 2·500² = 500000 ≥ 1096 ≥ a` using `heps500` (`nlinarith` after
`one_div_le` at `ε ≤ 1/500`).  `hPNTwindow : √Hlo' ≤ ε²·Hlo'/2` — the builder's `hPNT` block
VERBATIM (`TowerFlatBuilder.lean:277-300`) at `m := ⌈1/ε⌉₊`, from `hlo4`.  `hHlohi`:
`Nat.div_le_self`
then `chowlaTower_ge_base R.hC0 (base ≥ 4·10⁶) R.J` at base `R.a * R.Hlo` read through
`chowlaTower_eq_base_one` and `R.hfit`.  `hfit`: `chowlaTower R.C0 a (R.a*R.Hlo/a) R.J =
chowlaTower R.C0 1 (a * (R.a*R.Hlo/a)) R.J` (`chowlaTower_eq_base_one`) `= chowlaTower R.C0 1
(R.a*R.Hlo) R.J` (`Nat.mul_div_cancel' hdiv`) `= chowlaTower R.C0 R.a R.Hlo R.J`
(`chowlaTower_eq_base_one` backwards) `≤ R.Hhi` (`R.hfit`).  `hJcon`: the same three rewrites on
`towerDropSum_eq_base_one`, then `R.hJcon`.  The floor-division corner `R.x / a / R.ω` is
`R.x / (a * R.ω)` by `Nat.div_div_eq_div_mul` if a consumer wants it; the fields do not.
Hypotheses are stated at the VALUES the fields read (`R.a * R.Hlo / a`), so the caller's
discharge is one `rw` from the receipt's pin (`R.Hlo = a·B`, `a ∣ a·B`). -/
def regimeShrinkX_stride (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a) (ha1096 : a ≤ 1096)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a)
    (hloM : 4000000 ≤ R.a * R.Hlo / a) : ChowlaRegime := by
  sorry

/-- **F3-P4 (class A ×8).**  The projections of the shrunk regime.  Each is `rfl` once F3-P3 is
a `where`-structure (the executor writes F3-P3 as a structure literal, NOT a tactic block, so
that these reduce); mark `@[simp]`. -/
theorem regimeShrinkX_stride_x (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a) (ha1096 : a ≤ 1096)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride R a ha ha1096 heps500 hs hdiv hlo4 hloM).x = R.x / a := by
  sorry

theorem regimeShrinkX_stride_omega (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a) (ha1096 : a ≤ 1096)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride R a ha ha1096 heps500 hs hdiv hlo4 hloM).ω = R.ω := by
  sorry

theorem regimeShrinkX_stride_a (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a) (ha1096 : a ≤ 1096)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride R a ha ha1096 heps500 hs hdiv hlo4 hloM).a = a := by
  sorry

theorem regimeShrinkX_stride_eps (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a) (ha1096 : a ≤ 1096)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride R a ha ha1096 heps500 hs hdiv hlo4 hloM).eps = R.eps := by
  sorry

theorem regimeShrinkX_stride_Hlo (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a) (ha1096 : a ≤ 1096)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride R a ha ha1096 heps500 hs hdiv hlo4 hloM).Hlo = R.a * R.Hlo / a := by
  sorry

theorem regimeShrinkX_stride_Hhi (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a) (ha1096 : a ≤ 1096)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride R a ha ha1096 heps500 hs hdiv hlo4 hloM).Hhi = R.Hhi := by
  sorry

theorem regimeShrinkX_stride_C0 (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a) (ha1096 : a ≤ 1096)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride R a ha ha1096 heps500 hs hdiv hlo4 hloM).C0 = R.C0 := by
  sorry

theorem regimeShrinkX_stride_J (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a) (ha1096 : a ≤ 1096)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride R a ha ha1096 heps500 hs hdiv hlo4 hloM).J = R.J := by
  sorry

/-- **F3-P5 (class A) — THE SHARED TOWER, AS A THEOREM.**  The stride-`a` tower from the shrunk
base IS the door regime's tower, level by level: `chowlaTower_eq_base_one` twice around
`Nat.mul_div_cancel' hdiv`.  This is the tripwire for the base: under a wrong `Hlo'` (say
`R.Hlo / a` at `R.a ≠ 1`, or `R.Hlo` itself) the identity is FALSE at `j = 0`
(`a * Hlo' ≠ R.a * R.Hlo`). -/
theorem regimeShrinkX_stride_tower (R : ChowlaRegime) (a : ℕ) (hdiv : a ∣ R.a * R.Hlo) (j : ℕ) :
    chowlaTower R.C0 a (R.a * R.Hlo / a) j = chowlaTower R.C0 R.a R.Hlo j := by
  sorry

/-- **F3-P6 (class A).**  The scale is divided EXACTLY: `(x/a) * a = x` from `a ∣ x`
(`Nat.div_mul_cancel hs.1`), read through `regimeShrinkX_stride_x`.  This is what makes the
affine pushforward's top endpoint `a·(x/a) = x` the plain window's top endpoint, with no
`⌊·⌋` corner at the top (the bottom corner is `sum_window_image_le`'s inclusion). -/
theorem regimeShrinkX_stride_x_mul (R : ChowlaRegime) (a : ℕ) (ha : 1 ≤ a) (ha1096 : a ≤ 1096)
    (heps500 : R.eps ≤ 1 / 500) (hs : StrideScale a R) (hdiv : a ∣ R.a * R.Hlo)
    (hlo4 : 4 * ⌈(1 / R.eps : ℚ)⌉₊ ^ 4 ≤ R.a * R.Hlo / a) (hloM : 4000000 ≤ R.a * R.Hlo / a) :
    (regimeShrinkX_stride R a ha ha1096 heps500 hs hdiv hlo4 hloM).x * a = R.x := by
  sorry

/-! ## F3-P7 — the affine set on the `a`-grid only -/

/-- **F3-P7 (def).**  The affine large-spectrum set RESTRICTED TO `a ∣ H`: `bigXiAff a b h eps H`
when `a ∣ H`, `∅` otherwise.  The affine arc bridge (MR side) needs the `1/H` grid to carry
`(b+h)η/a` exactly, which is `a ∣ H` (Tao's own range); a set family that is empty off the grid
lets the road's `∀ H ∈ [Hlo, Hhi]` door be stated at EVERY `H` (vacuous off the grid) and read at
the tower values, which are multiples of `a` (`dvd_chowlaTower`).  The `if` is on a decidable
proposition (`Nat.decidable_dvd`… `inferInstance`); `classical` if needed. -/
noncomputable def bigXiAffD (a b h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] : Finset (ZMod H) := by
  classical
  exact if a ∣ H then bigXiAff a b h eps H else ∅

/-- **F3-P7a (class A).**  On the grid the restricted set is the affine set: `unfold bigXiAffD;
simp [hdvd]` (or `rw [if_pos hdvd]` after `unfold`). -/
theorem bigXiAffD_of_dvd {a b h : ℕ} {eps : ℚ} {H : ℕ} [NeZero H] (hdvd : a ∣ H) :
    bigXiAffD a b h eps H = bigXiAff a b h eps H := by
  sorry

/-- **F3-P7b (class A).**  The restricted set's cardinality never exceeds the affine set's:
`split_ifs` — `le_rfl` on the grid, `Finset.card_empty ▸ Nat.zero_le` off it.  Feeds the count
hook (`bigXiAff_bounded_ceiling_of_pin`, `StrideFork.lean:413`) to the road's `K`. -/
theorem bigXiAffD_card_le (a b h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] :
    (bigXiAffD a b h eps H).card ≤ (bigXiAff a b h eps H).card := by
  sorry

/-! ## F3-P8 — the `L²` door over an arbitrary set family, at the plain measure -/

/-- **F3-P8 (def).**  The Ξ-summed `L²` MRT door at a PLAIN regime over an ARBITRARY frequency-set
family `Xi : (eps : ℚ) → (H : ℕ) → [NeZero H] → Finset (ZMod H)`: `MRTUniformityXiL2H h`
(`ShiftFork.lean:538`) with `bigXiH h` replaced by `Xi`.  The road's door-L2 supply is generic in
the set (`parseval_insert_budget_door` takes `Xi` as a binder; the adapter reads the set only
through `harc`, `hXi`, `hins`), so the road can be replayed once at `Xi` (MR side).  At `Xi :=
bigXiH h` it is the landed door (`mrtUniformityXiL2Set_bigXiH_eq`, the anti-drift receipt); at
`Xi := bigXiAffD a b h` it is the affine-set door at the plain measure, the transport's input.
The quantifiers stay OUTSIDE the integral (REF-L2 mandate R4). -/
noncomputable def MRTUniformityXiL2Set
    (Xi : ∀ (_eps : ℚ) (H : ℕ) [NeZero H], Finset (ZMod H)) (R : ChowlaRegime) (ρ : ℝ) : Prop :=
  ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
    ∑ ξ ∈ Xi R.eps H, (1 / (H : ℝ) ^ 2)
        * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure R.x R.ω) ≤ ρ

/-- **F3-P8a (class A) — THE ANTI-DRIFT RECEIPT.**  At the landed set family the generic door IS
the landed `h`-door, definitionally: `rfl` (both unfold to the same `∀ H …`).  If the generic
definition drifts from `ShiftFork.lean:538` this fails to elaborate. -/
theorem mrtUniformityXiL2Set_bigXiH_eq (h : ℕ) (R : ChowlaRegime) (ρ : ℝ) :
    MRTUniformityXiL2Set (fun eps H _ => bigXiH h eps H) R ρ = MRTUniformityXiL2H h R ρ := by
  sorry

/-! ## F3-P9 — THE STATEMENT ACT: the affine door at Tao's range -/

/-- **F3-P9 (def, Fable statement act).**  The Ξ-summed `L²` door at `(a, b, h)` AT TAO'S RANGE:
F1-D2 (`StrideFork.lean:652`) with the range `R.Hlo ≤ H` replaced by `R.a ∣ H ∧ R.a * R.Hlo ≤ H`
(textdump:1296-1300: `H ≡ 0 (mod a)`, `H ≥ a·H₋`).  Two reasons, both forced (freeze §3):
(i) the affine tower windows START at `a·Hlo` (`Regime.lean:38`, index `0 = a·Hlo`) and the
shared plain door covers `[R_door.Hlo, Hhi] = [a·Hlo_aff, Hhi]` only — the range `[Hlo_aff,
a·Hlo_aff)` of F1-D2 is a range NO supply reaches; (ii) the arc bridge's grid (`affOffset`'s
`H / a`) is exact only at `a ∣ H`.  F1-D2 is UNTOUCHED (iron rule 1); the wide door implies this
one (F3-P10) and the seam is cloned here (F3-P11).  Set, measure, frequency and normalisation are
F1-D2's byte for byte. -/
noncomputable def MRTUniformityXiL2AffW (h : ℕ) (R : ChowlaRegimeAff) (ρ : ℝ) : Prop :=
  ∀ H : ℕ, ∀ [NeZero H], R.a ∣ H → R.a * R.Hlo ≤ H → H ≤ R.Hhi →
    ∑ ξ ∈ bigXiAff R.a R.b h R.eps H, (1 / (H : ℝ) ^ 2)
        * ∫ m, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasureAff R.a R.x R.ω)
      ≤ ρ

/-- **F3-P10 (class A) — the conservativity receipt.**  The wide door implies the windowed one:
`intro H _ _ hlo hhi; exact hd H (le_trans (Nat.le_mul_of_pos_left _ R.ha) hlo) hhi`
(`R.ha : 1 ≤ R.a`, so `R.Hlo ≤ R.a * R.Hlo`). -/
theorem mrtUniformityXiL2AffW_of_aff (h : ℕ) (R : ChowlaRegimeAff) (ρ : ℝ)
    (hd : MRTUniformityXiL2Aff h R ρ) : MRTUniformityXiL2AffW h R ρ := by
  sorry

/-- **F3-P10a (class A, v2) — the windowed door is monotone in its grade.**  The twin of
`mrtUniformityXiL2H_mono` (`S16FlatTerminalExitH.lean:69`): `intro H _ hdvd hlo hhi; exact
le_trans (hdoor H hdvd hlo hhi) hle`.  Added on the refuter verdict (A7): the crown states its
grade with a SLACK binder `Zr` and a NAMED endpoint `E`, and lands there from the transport's
literal grade `a·(Z/Z')·ρ + K·a/(…)` by THIS step (`Z/Z' ≤ 1.02` by F3-P17, the endpoint by
F3-P18) — a step the v1 recipe assumed and no obligation carried. -/
theorem mrtUniformityXiL2AffW_mono (h : ℕ) (R : ChowlaRegimeAff) {ρ ρ' : ℝ}
    (hdoor : MRTUniformityXiL2AffW h R ρ) (hle : ρ ≤ ρ') : MRTUniformityXiL2AffW h R ρ' := by
  sorry

/-- **F3-P11 (class A) — THE `L²` SEAM AT TAO'S RANGE.**  `contradiction_of_mrtDoorXiL2Aff`
(`StrideFork.lean:759`) with the door fired at `hdvd hlo hhi`: `have hd := hdoor H hdvd hlo hhi;
linarith`.  The entropy-side caller (F4) supplies `hdvd` from `dvd_chowlaTower` and `hlo` from the
window's index `≥ a·Hlo`. -/
theorem contradiction_of_mrtDoorXiL2AffW (h : ℕ) (R : ChowlaRegimeAff) {ρ c₀ ε : ℝ} {H : ℕ}
    [NeZero H] (hdvd : R.a ∣ H) (hlo : R.a * R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    (hdoor : MRTUniformityXiL2AffW h R ρ)
    (hsmall : ρ < c₀ * ε)
    (hlower : c₀ * ε ≤ ∑ ξ ∈ bigXiAff R.a R.b h R.eps H, (1 / (H : ℝ) ^ 2)
        * ∫ m, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
            ∂(logMeasureAff R.a R.x R.ω)) :
    False := by
  sorry

/-- **F3-P12 (class B) — the `(1, 0)` compat of the windowed door.**  At `R.a = 1`, `R.b = 0`
(the affine regime `ChowlaRegimeAff.ofRegime R 0 _` of a regime with `R.a = 1`) the windowed
door is the landed `MRTUniformityXiL2H h`: `propext`; `1 ∣ H` is `one_dvd` and `1 * R.Hlo =
R.Hlo` is `one_mul`, the set is `bigXiAff_one_zero`, the measure `logMeasureAff_one` — the body
of `mrtUniformityXiL2H_eq_xiL2Aff_one_zero` (`StrideFork.lean:692`) with the two extra binders
introduced and discharged.  Records that the range change is invisible at stride `1`, and
nothing more (it cannot police the range at `a ≥ 2`; F3-P9's docstring carries the reasons). -/
theorem mrtUniformityXiL2AffW_one_zero_eq (h : ℕ) (R : ChowlaRegime) (hR1 : R.a = 1) (ρ : ℝ) :
    MRTUniformityXiL2H h R ρ
      = MRTUniformityXiL2AffW h (ChowlaRegimeAff.ofRegime R 0 (Nat.zero_le _)) ρ := by
  sorry

/-! ## F3-P13–P16 — the measure transport: plain door over the affine set ⇒ affine door -/

/-- **F3-P13 (class A, a private copy).**  `ChowlaFailure.lean:40`'s `logMeasure_integral_eq`,
which is `private` to its module and was copied verbatim as `logMeasure_integral_eq_aff` in
`StrideFork.lean:99` — ALSO private there.  Copy the 12-line body a third time (its proof is
`f`-generic: `logMeasure` is a scaled finite sum of Dirac masses). -/
private theorem logMeasure_integral_eq_pair (f : ℕ → ℝ) (x ω : ℕ) :
    ∫ n, f n ∂(logMeasure x ω)
      = (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹ := by
  sorry

/-- **F3-P14 (class A — v2, was B) — the image window sits INSIDE the scaled window.**
For `0 ≤ f ≤ M` and `x = a * x'`: the image `{a·n : x'/ω < n ≤ x'}` (F1-S1's window) is a
SUBSET of the plain window `(a·x'/ω, a·x']` at `(a·x', ω)`, unconditionally: writing `x' = qω + r`
with `q = x'/ω`, `0 ≤ r < ω`, one has `a·x'/ω = a·q + ⌊a·r/ω⌋ ≤ a·q + a − 1 < a·(q+1)`, and
`a·(q+1)` is the LEAST image element; the top `a·x'` is the window's own top.  (v1 claimed "at
most ONE multiple outside" — the refuter verdict (R4, R3) measured ZERO: the endpoint term
`M/(a·(x'/ω)+1)` is pure nonnegative SLACK, kept NAMED because it is what the crown's `E` and
freeze §2 price; no number moves.)  Route: `Finset.sum_le_sum_of_subset_of_nonneg` on the
inclusion (`Finset.mem_image`, `Finset.mem_Ioc`; the inequality `a * x' / ω < a * (q + 1)` by
`Nat.div_lt_iff_lt_mul` at `0 < ω` — case-split `rcases Nat.eq_zero_or_pos ω`, at `ω = 0` both
Nat floors are `0` and the image sits in `Ioc 0 (a·x')` — then `Nat.lt_of_div_lt_div`-free
arithmetic: `a * x' < a * (q+1) * ω` from `x' < (q+1)·ω`, `Nat.lt_div_add_one_mul_self`… or
`Nat.div_add_mod x' ω` + `Nat.mod_lt` + `nlinarith`), then `le_add_of_nonneg_right` with
`0 ≤ M/(…)` from `0 ≤ M` (`le_trans (hf0 0) (hfM 0)`) and a positive denominator.  At `a = 1`
the image is the window. -/
theorem sum_window_image_le (a x' ω : ℕ) (ha : 0 < a) (f : ℕ → ℝ) (M : ℝ)
    (hf0 : ∀ m, 0 ≤ f m) (hfM : ∀ m, f m ≤ M) :
    ∑ m ∈ (Finset.Ioc (x' / ω) x').image (fun n => a * n), f m / (m : ℝ)
      ≤ ∑ m ∈ Finset.Ioc (a * x' / ω) (a * x'), f m / (m : ℝ)
          + M / ((a : ℝ) * ((x' / ω : ℕ) : ℝ) + 1) := by
  sorry

/-- **F3-P15 (class B) — the stride measure against the plain measure at the scaled window.**
For `0 ≤ f ≤ M`, with `Z(x, ω) := Σ_{n ∈ Ioc (x/ω) x} 1/n`:
`∫ f dμ_aff(a, x', ω) ≤ a·(Z(a x', ω)/Z(x', ω))·∫ f dμ(a x', ω) + a·M/((a·(x'/ω)+1)·Z(x', ω))`.
Proof: `integral_logMeasureAff` (F1-M3) turns the left side into `∫ f(a n) dμ(x', ω)`;
`logMeasure_integral_eq_pair` writes both integrals as normalised sums; `sum_window_aff_eq`
(F1-S1, with `f m / m` spelled as `f m * m⁻¹` — `div_eq_mul_inv`) reindexes the left sum to the
image; `sum_window_image_le` bounds the image sum; multiply through by `Z(x', ω)⁻¹ > 0`
(`harmonic_window_bounds` gives `Z ≥ log ω − 1 > 0` at `log ω ≥ 2`, i.e. `hω : 8 ≤ ω`).  Every
factor is EXPLICIT (the normaliser ratio is NOT yet `1.02`: that is F3-P17; the endpoint term
is nonnegative slack carried from F3-P14). -/
theorem integral_logMeasureAff_le_plain (a x' ω : ℕ) (ha : 0 < a) (hx : 2 ≤ x') (hω : 8 ≤ ω)
    (hωx : ω ≤ x') (f : ℕ → ℝ) (M : ℝ) (hf0 : ∀ m, 0 ≤ f m) (hfM : ∀ m, f m ≤ M) :
    ∫ m, f m ∂(logMeasureAff a x' ω)
      ≤ (a : ℝ) * ((∑ n ∈ Finset.Ioc (a * x' / ω) (a * x'), (n : ℝ)⁻¹)
            / (∑ n ∈ Finset.Ioc (x' / ω) x', (n : ℝ)⁻¹))
          * ∫ m, f m ∂(logMeasure (a * x') ω)
        + (a : ℝ) * M / (((a : ℝ) * ((x' / ω : ℕ) : ℝ) + 1)
            * ∑ n ∈ Finset.Ioc (x' / ω) x', (n : ℝ)⁻¹) := by
  sorry

/-- **F3-P16 (class B) — THE TRANSPORT.**  From the plain `L²` door over the affine set at the door
regime `Rd` (`MRTUniformityXiL2Set (bigXiAffD a b h) Rd ρ`) to the affine door AT TAO'S RANGE at
the shrunk regime `Ra := ofRegime (regimeShrinkX_stride Rd a …) b hb`, at grade
`a·(Z(Rd.x, ω)/Z(Ra.x, ω))·ρ + K·a/((a·(Ra.x/ω)+1)·Z(Ra.x, ω))`.  Per `H` on the grid
(`hdvd : a ∣ H`; `bigXiAffD_of_dvd` rewrites the set — in `hdoor` AND in `hK`, both stated at
the grid-restricted family `bigXiAffD`, which is exactly what the receipt exports; v2 on the
refuter verdict (R1): v1's `hK` at the unrestricted `bigXiAff` was NOT implied by the chain's
count, since `bigXiAffD = ∅` off the grid — the hypothesis is now the WEAKER one, the one P16
uses): for each `ξ`, `f := ‖windowExpSum H · (−ξ/H)‖²` has `0 ≤ f ≤ H²`
(`norm_windowExpSum_trivial`, `MRTDoor.lean:219`, opened `private` above — v2, A5: v1 cited a
phantom name and an MR name unreachable from this module; `sq_nonneg`, `pow_le_pow_left`);
`integral_logMeasureAff_le_plain` at `x' := Ra.x` (`regimeShrinkX_stride_x_mul` gives `a * Ra.x
= Rd.x`, so the plain measure is `Rd`'s), multiply by `1/H²`, sum over `ξ ∈ bigXiAff`
(`Finset.sum_le_sum`, `Finset.mul_sum`), the first sum is `≤ ρ` by `hdoor H hlo' hhi` (`hlo' :
Rd.Hlo ≤ H` from `Rd.Hlo ≤ Rd.a * Rd.Hlo = a * Ra.Hlo ≤ H`), the second is `card · (H²/H²) ·
a/((…)·Z) ≤ K·a/((…)·Z)` by `hK H hlo' hhi` after the same rewrite.  Ranges: `Ra.Hhi = Rd.Hhi`,
`Ra.eps = Rd.eps`, `Ra.ω = Rd.ω`, `Ra.a = a`, `Ra.b = b` (the projections; `ofRegime` is `{ R with
… }`).  `hω : 8 ≤ Rd.ω` from `Rd.hωbig` (`log ω ≥ 129`) — the caller's numeral. -/
theorem mrtUniformityXiL2AffW_of_set (h : ℕ) (Rd : ChowlaRegime) (a b : ℕ) (ha : 1 ≤ a)
    (ha1096 : a ≤ 1096) (heps500 : Rd.eps ≤ 1 / 500) (hs : StrideScale a Rd)
    (hdiv : a ∣ Rd.a * Rd.Hlo) (hlo4 : 4 * ⌈(1 / Rd.eps : ℚ)⌉₊ ^ 4 ≤ Rd.a * Rd.Hlo / a)
    (hloM : 4000000 ≤ Rd.a * Rd.Hlo / a)
    (hb : b ≤ (regimeShrinkX_stride Rd a ha ha1096 heps500 hs hdiv hlo4 hloM).Hlo)
    (hω : 8 ≤ Rd.ω) (K ρ : ℝ)
    (hK : ∀ H : ℕ, ∀ [NeZero H], Rd.Hlo ≤ H → H ≤ Rd.Hhi →
      ((bigXiAffD a b h Rd.eps H).card : ℝ) ≤ K)
    (hdoor : MRTUniformityXiL2Set (fun eps H _ => bigXiAffD a b h eps H) Rd ρ) :
    MRTUniformityXiL2AffW h
      (ChowlaRegimeAff.ofRegime (regimeShrinkX_stride Rd a ha ha1096 heps500 hs hdiv hlo4 hloM)
        b hb)
      ((a : ℝ) * ((∑ n ∈ Finset.Ioc (Rd.x / Rd.ω) Rd.x, (n : ℝ)⁻¹)
            / (∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹)) * ρ
        + K * (a : ℝ) / (((a : ℝ) * ((Rd.x / a / Rd.ω : ℕ) : ℝ) + 1)
            * ∑ n ∈ Finset.Ioc (Rd.x / a / Rd.ω) (Rd.x / a), (n : ℝ)⁻¹)) := by
  sorry

/-- **F3-P17 (class A) — M2's first measurement, the normaliser ratio.**  `Z(x, ω)/Z(x', ω) ≤
1.02` whenever `101 ≤ log ω` (`harmonic_window_bounds`, `LogMeasure.lean:115`, at both windows:
`Z(x, ω) ≤ log ω + 1`, `Z(x', ω) ≥ log ω − 1`, and `(L+1)/(L−1) ≤ 1.02 ⟺ L ≥ 101`).  `div_le_iff₀`
then `linarith`.  The regime supplies `log ω ≥ 129` through `hωbig` at `ε ≤ 1/500`
(`(16/ε)·log(ε²H₊) + 64/ε + 1 ≥ 64·500 + 1`), the caller's one-line numeral. -/
theorem strideZRatio_le (x x' ω : ℕ) (hx : 2 ≤ x) (hx' : 2 ≤ x') (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hωx' : ω ≤ x') (hlog : 101 ≤ Real.log ω) :
    (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) / (∑ n ∈ Finset.Ioc (x' / ω) x', (n : ℝ)⁻¹)
      ≤ 1.02 := by
  sorry

/-- **F3-P18 (class A) — M2's second measurement, the endpoint term.**  `K·a/((a·q+1)·Z) ≤
K·a/((a·q+1)·(log ω − 1))` at `Z ≥ log ω − 1 > 0` (`harmonic_window_bounds`, `hlog : 2 ≤ log ω`)
and `0 ≤ K`: `div_le_div_of_nonneg_left` with the denominators ordered.  `Z : ℝ` — the REAL
harmonic normaliser `Σ_{n ∈ Ioc (x'/ω) x'} 1/n` of F3-P16's grade (v2, refuter verdict A3: v1
bound `Z` as `ℕ` and cast it, a lemma true as spelled and uninstantiable at its only consumer).
The caller closes the numeral from `hheadroom'` (`q = x'/ω ≥ 8·Hhi·log²Hhi`) and `loglog Hhi ≥
50`, against `K ≤ 2^539` — freeze §2 prices it. -/
theorem strideEndpoint_le (K a Z : ℝ) (q ω : ℕ) (hK : 0 ≤ K) (ha : 0 ≤ a)
    (hlog : 2 ≤ Real.log ω) (hZ : Real.log ω - 1 ≤ Z) :
    K * a / ((a * (q : ℝ) + 1) * Z) ≤ K * a / ((a * (q : ℝ) + 1) * (Real.log ω - 1)) := by
  sorry

/-! ## F3-P19–P20 — the flat base at the shrunk regime (the caller's numerals) -/

/-- **F3-P19 (class A) — R5, CORRECTED.**  The price brief's `loglog(a·B) ≤ loglog B + 1` does
NOT fit the ONE consumer that reads `Hlo` from above: H6's `hbaseceil` (`DoorReceipt.lean:
819-821` at `h = 1`; `flat_L_width_priced`'s `hbase`) wants `loglog Hlo ≤ 3.2·A + log 2`
LITERALLY, with `log 2` of
slack that `flatDesignBase_loglog_le` (`S16FlatTerminalLinear.lean:1535`) already spends on the
`Nat.ceil` overshoot.  So the lemma is stated at the flat base with the factor `a` absorbed
inside the ceiling's own margin: `log(a·B) = log a + log B ≤ 7 + (exp(3.2A) + log 2)` (the
`B ≤ 2·exp(exp(3.2A))` step of `flatDesignBase_loglog_le`'s proof, re-derived: `B ≤ exp(exp(3.2A))
+ 1`), and `7 + log 2 + exp(3.2A) ≤ 2·exp(3.2A)` at `A ≥ 162` (`exp(3.2A) ≥ 3.2A + 1 ≥ 519`), so
`loglog(a·B) ≤ log(2·exp(3.2A)) = 3.2A + log 2`.  `Real.log_mul`, `Real.log_le_log`,
`Real.add_one_le_exp`, `Real.log_exp`.  This is the ONLY place the node reads `Hlo` from above
by other than `loglog` monotonicity (R11's step-0 census, freeze §1(C)). -/
theorem loglog_mul_flatDesignBase_le {A : ℝ} (hA : 162 ≤ A) {a : ℕ} (ha : 1 ≤ a)
    (ha7 : Real.log (a : ℝ) ≤ 7) :
    Real.log (Real.log ((a * flatDesignBase A : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
  sorry

/-- **F3-P20 (class A).**  The flat base clears the shrunk regime's two `Hlo`-floors:
`4·⌈1/ε⌉₊⁴ ≤ flatDesignBase A` at `ε ≥ 1/548000` (`⌈1/ε⌉₊ ≤ 548000`, `4·548000⁴ < 10²⁴ ≤
exp(exp 518) ≤ flatDesignBase A`: `Nat.ceil_le`, `Nat.le_ceil`, `Real.add_one_le_exp` twice with
`exp 518 ≥ 519` and `exp 519 ≥ 10²⁴` by `Real.exp_one_gt_d9` and `Real.exp_nat_mul` — or the
corpus's `regime_Hfloor_of_loglogFloor50`-style numerals), and `4000000 ≤ flatDesignBase A` the
same way.  Stated at the pin's floor `1/548000 = 1/(500·1096)`, which `ε = 1/(500·(a·h))` meets
at every `a·h ≤ 1096`. -/
theorem flatDesignBase_clears_stride_floors {A : ℝ} (hA : 162 ≤ A) {eps : ℚ}
    (heps : 1 / 548000 ≤ eps) :
    4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4 ≤ flatDesignBase A ∧ 4000000 ≤ flatDesignBase A := by
  sorry

end Salt.Entropy.Chowla
