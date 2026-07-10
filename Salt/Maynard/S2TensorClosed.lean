import Salt.Maynard.HMainClose
import Salt.Maynard.HOmit

/-!
# S₂ tensor lower bound — fully assembled (C3b closed)

Combines `s2_tensor_lower` (S2Tensor.lean) with the two now-closed sum-level
atoms `H_main_bound_closed` (HMainClose.lean) and `H_omit_bound_closed`
(HOmit.lean).  The only remaining hypotheses are structural (`hR`) plus the
`k ≥ 16` / `3T ≤ k` regime conditions and the narrow transfer atom
`hA11 : A₁⁽¹⁾ ≤ (1/4)·A₁` (a bound on the ratio `A₁⁽¹⁾/A₁`, discharged from
`A1_1_upper_split` + the sharp `B₁/A₁` bounds in a later node).
-/

namespace Salt.Maynard

open scoped BigOperators

/-- **C3b, fully assembled.** For the concrete tensor weight, the S₂
diagonal quadratic form (restricted to `uₘ = 1`) is bounded below by
`(1/4)·B₁²·A₁^{k-1}` — the ratio-critical S₂ lower bound, now conditional
only on the regime hypotheses and the narrow `hA11` transfer atom. -/
theorem s2_tensor_lower_closed (k R : ℕ) (m : Fin k) (T : ℝ) (hR : 2 ≤ R)
    (hk : 16 ≤ k) (hT : 0 ≤ T) (hTk : 3 * T ≤ (k : ℝ))
    (hA11 : A1_1 k R (W k) T ≤ (1 / 4 : ℝ) * A1 k R (W k) T)
    (hB1 : 0 ≤ B1 k R (W k) T) :
    (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
        (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
          / ∏ i, (Nat.totient (u i) : ℝ))
      ≥ (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1) := by
  have hDcube : (k : ℕ) ^ 3 ≤ D₀ k := le_max_left _ _
  have hD : 16 * k ≤ D₀ k := by
    have hk3 : 16 * k ≤ k ^ 3 := by
      have h16 : 16 ≤ k * k := le_trans hk (Nat.le_mul_of_pos_left k (by omega))
      calc 16 * k ≤ (k * k) * k := Nat.mul_le_mul_right k h16
        _ = k ^ 3 := by ring
    exact le_trans hk3 hDcube
  exact s2_tensor_lower k R m T hR hB1
    (H_main_bound_closed k R m T hR hk hT hTk hA11)
    (H_omit_bound_closed k R m T hR (by omega) hD)

end Salt.Maynard
