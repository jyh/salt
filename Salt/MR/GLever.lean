/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SeamCalibrationK

/-!
# `GLever` — THE G-LEVER BASE (`s13GK`)

The ratified re-cut of the door's growth base.  The landed door family runs at `G = 3072·M`
(`DoorFrame`); the lever inserts one free dyadic factor,

  `s13GK K M := 3072 · 2^K · M`,

and every consumer is twinned ADDITIVELY at `G := s13GK K M` (the `_gk` family).  `Jb` stays
`2` everywhere and `Adoor M` is untouched: the lever moves the base and nothing else.

## The two standing facts

* **LEVEL 1 IS K-INVARIANT.**  `calE A G 1 = A` (`SeamCalibration.calE_one`) does not read `G`
  at all, so `calP A (s13GK K M) 1 = calP A (3072M) 1` and `calQK A (s13GK K M) M' 1
  = calQK A (3072M) M' 1` — `calP_gk_one_eq`, `calQK_gk_one_eq`.  Every door object that
  reads `G` ONLY at level 1 (`H1door`, `a2Level1`, `doorRowFloor`, the whole `DoorFrameH1`
  page, `M4Residue`'s dilation gates) therefore keeps its LANDED NAME under the lever; it
  gets a transport equality, never a twin.
* **LEVEL 2 IS MULTIPLICATIVE.**  `calE A (s13GK K M) 2 = 2^K · calE A (3072M) 2`
  (`calE_gk_two`) — the identity ported from the refuter probe `probe_G_lever_calE`.  The
  lever's whole cost to the frame is one `+K` inside a base-2 exponent
  (`DoorFrame.log_calE_door_two_gk`, at `(2L + 52 + K)`).

## G-monotonicity

The corpus carries only the `j`-monotonicity of the ladders (`calE_mono`, `calQK_mono`).  The
lever needs the OTHER variable: `calE`, `calP`, `calQK` are monotone in `G` at fixed `j`
(`calE_mono_G`, `calP_mono_G`, `calQK_mono_G`), and `3072M ≤ s13GK K M` (`le_s13GK`), so every
gate that is a LOWER bound on `G` (`CalFrameK.G_gateK`, `64·Jb²M ≤ ηG`) survives the lever a
fortiori, and every read of `1/𝒫` or `1/𝒬` only shrinks.

## The stones

* `s13GK`, `s13GK_zero`, `s13GK_pos`, `one_le_s13GK`, `le_s13GK` — the base.
* `calE_mono_G`, `calP_mono_G`, `calQK_mono_G` — G-monotonicity (NEW; class A).
* `calE_le_gk`, `calP_le_gk`, `calQK_le_gk` — the three at the lever.
* `calE_gk_one`, `calP_gk_one_eq`, `calQK_gk_one_eq` — the level-1 transport.
* `calE_gk_two` — the level-2 identity.

The two door-side re-derivations (`log_calE_door_two_gk` at `(2L+52+K)` and the frame
inhabitant `calFrameK_satisfiable_door_gk` with its `K ≤ 1.7·10⁸` side condition) live in
`DoorFrame`'s own `§GK` section, since `Adoor` is defined there.
-/

namespace Salt.MR

/-! ## §0 — the lever -/

/-- **THE G-LEVER** `s13GK K M := 3072·2^K·M`.  `K = 0` is the landed door base
(`s13GK_zero`); `J` stays `2` and `Adoor M` is unchanged. -/
def s13GK (K M : ℕ) : ℕ := 3072 * 2 ^ K * M

/-- The lever at `K = 0` IS the landed base — the twin family is a genuine generalisation. -/
lemma s13GK_zero (M : ℕ) : s13GK 0 M = 3072 * M := by
  rw [s13GK, pow_zero, mul_one]

lemma s13GK_pos (K : ℕ) {M : ℕ} (hM : 1 ≤ M) : 0 < s13GK K M :=
  Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.two_pow_pos K)) hM

lemma one_le_s13GK (K : ℕ) {M : ℕ} (hM : 1 ≤ M) : 1 ≤ s13GK K M := s13GK_pos K hM

/-- **THE LEVER ONLY GROWS `G`** — the direction every `G`-lower-bound gate needs. -/
lemma le_s13GK (K M : ℕ) : 3072 * M ≤ s13GK K M := by
  rw [s13GK]
  exact Nat.mul_le_mul_right M (Nat.le_mul_of_pos_right 3072 (Nat.two_pow_pos K))

/-! ## §1 — G-monotonicity of the three ladders (NEW: the corpus has only `j`-monotonicity) -/

/-- `calE A G j = A·G^{j−1}(j!)²` is monotone in the BASE `G`, at fixed level. -/
lemma calE_mono_G (A j : ℕ) {G G' : ℕ} (h : G ≤ G') : calE A G j ≤ calE A G' j := by
  rw [calE, calE]
  exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left h (j - 1))) le_rfl

/-- `calP A G j = 2^{e_j}` is monotone in the base `G`. -/
lemma calP_mono_G (A j : ℕ) {G G' : ℕ} (h : G ≤ G') : calP A G j ≤ calP A G' j := by
  rw [calP, calP]
  exact Nat.pow_le_pow_right (by norm_num) (calE_mono_G A j h)

/-- `calQK A G M j = 2^{(j²M)e_j}` is monotone in the base `G`. -/
lemma calQK_mono_G (A M j : ℕ) {G G' : ℕ} (h : G ≤ G') : calQK A G M j ≤ calQK A G' M j := by
  rw [calQK, calQK]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul le_rfl (calE_mono_G A j h))

lemma calE_le_gk (A j K M : ℕ) : calE A (3072 * M) j ≤ calE A (s13GK K M) j :=
  calE_mono_G A j (le_s13GK K M)

lemma calP_le_gk (A j K M : ℕ) : calP A (3072 * M) j ≤ calP A (s13GK K M) j :=
  calP_mono_G A j (le_s13GK K M)

lemma calQK_le_gk (A M' j K M : ℕ) : calQK A (3072 * M) M' j ≤ calQK A (s13GK K M) M' j :=
  calQK_mono_G A M' j (le_s13GK K M)

/-! ## §2 — LEVEL 1 IS K-INVARIANT -/

/-- `e₁ = A`: level 1 never reads `G`, so the lever is invisible there. -/
lemma calE_gk_one (A K M : ℕ) : calE A (s13GK K M) 1 = A := calE_one A (s13GK K M)

/-- **THE LEVEL-1 `𝒫` TRANSPORT** — `P₁` is the same symbol at the lever and at the door. -/
lemma calP_gk_one_eq (A K M : ℕ) : calP A (s13GK K M) 1 = calP A (3072 * M) 1 := by
  rw [calP, calP, calE_one, calE_one]

/-- **THE LEVEL-1 `𝒬K` TRANSPORT** — `Q₁` is the same symbol at the lever and at the door. -/
lemma calQK_gk_one_eq (A K M M' : ℕ) :
    calQK A (s13GK K M) M' 1 = calQK A (3072 * M) M' 1 := by
  rw [calQK, calQK, calE_one, calE_one]

/-! ## §3 — LEVEL 2 IS MULTIPLICATIVE -/

/-- **THE LEVER'S LEVEL-2 IDENTITY** `e₂(3072·2^K·M) = 2^K · e₂(3072M)` — ported from the
refuter probe `probe_G_lever_calE`.  `e₂ = A·G·(2!)²` is linear in `G`, so the lever's factor
comes straight out. -/
lemma calE_gk_two (A K M : ℕ) : calE A (s13GK K M) 2 = 2 ^ K * calE A (3072 * M) 2 := by
  simp only [calE, s13GK, Nat.factorial]
  ring

end Salt.MR

-- #audit (temporary)
