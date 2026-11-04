/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4RowSpineLinear

/-!
# The sieved door at the `blockLen` witness (`BlockLenDoor`)

`m4_sievedDoorSq_of_blk2_L_gk` takes a block length `ℓ` and four binders on it: `1 ≤ ℓ`,
`ℓ ≤ H`, the count binder `H ≤ arcDen² · ℓ` and the drift binder `arcDen · ℓ ≤ q · H`. At the
witness `ℓ := blockLen` (`M4SecondRoad.lean`) all four follow from one hypothesis, the arc gate
`128 · arcDen 12 H ² ≤ H` on the regime's window, and the door assemblies proved them inline with
the same three bullets at every site (the tactics catalogue's candidate #1). This module states the
door at the witness once, with the arc gate in place of the four binders.
-/

namespace Salt.MR
open Salt.Entropy.Chowla

/-- **The `_L_gk` sieved door at the `blockLen` witness needs only the arc gate.**
`m4_sievedDoorSq_of_blk2_L_gk` at `ℓ := blockLen`, its four block-length binders discharged by
`one_le_blockLen`, `blockLen_le` (from `1 ≤ H`, which the gate gives), `blockLen_narrow` and
`blockLen_drift`. -/
theorem m4_sievedDoorSq_of_blk2_blockLen_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Bblk Braw : ℕ → ℝ} (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 2 ≤ (H : ℝ))
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * (1 + 2 * Real.pi) ^ 2 * Bblk H ≤ Braw H)
    (hblk : M4SievedDoorSqBlk2_L_gk K R M blockLen Bblk) : M4SievedDoorSq_L_gk K R M Braw :=
  m4_sievedDoorSq_of_blk2_L_gk K hB0 (fun H q _ _ _ _ => one_le_blockLen H q)
    (fun H q hlo hhi _ _ => blockLen_le H q (by
      have h := harc H hlo hhi
      have h1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
      have : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
      exact_mod_cast this))
    (fun H q hlo hhi _ _ => blockLen_narrow (R := R) hlo (harc H hlo hhi))
    (fun H q hlo hhi hq _ => blockLen_drift (R := R) hlo hq (harc H hlo hhi))
    hgrade hblk

end Salt.MR
