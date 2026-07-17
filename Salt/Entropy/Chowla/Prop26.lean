/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The multiplicativity p-averaging (Tao 1509.05422 Prop 2.6), spine node STMT2 / W3-F

The class-C node of the log-Chowla-2 producer chain: Tao's Proposition 2.6 at the
Liouville model (`a=1,b=0,h=1,c_p=1,g₁=g₂=λ`), the step from the single correlation
`X = E[λ(n)λ(n+1)]` to the F-bridge expectation
`∫ fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n) ∂(logMeasure x ω)`.

## The frozen conclusion (`fBridge_of_singleCorr`)

The consumer `h211_of_logChowla2Fails` (`ChowlaFailure.lean`) threads this node's
conclusion through its `hprop26` binder:

    ∀ {δ : ℝ}, 0 < δ → δ ≤ |X| → ∃ c : ℝ, 0 < c ∧
      c * (δ * H / log H) ≤ |∫ fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)|

with `X = ∫ λ(n)·λ(n+1) ∂(logMeasure x ω)`.

## The mathematics (Tao p. 14–15 at the model)

Pointwise (`fBridgeF_liouville_apply`), the integrand is the residue-gated
double product

    F_n = ∑_{p ∈ 𝒫_H} ∑_{j < H} 1_{p ∣ n+j} · λ(n+j+1) · (windowVal … (j+p)),

so `∫ F_n = ∑_{p,j} T(p,j)` with `T(p,j) = ∫_n 1_{p∣n+j} λ(n+j+1)λ(n+j+p+1)`.
The reduction Tao performs on each `T(p,j)`:

1. **Multiplicativity** `λ(pn)λ(pn+p) = λ(n)λ(n+1)` (`liouville_mul` + `liouville_prime`).
2. **Dilation** (`dilation_error_div`, landed): the residue-class window sum
   `E[1_{n≡r(p)} f(n)]` equals `(1/p)·E'[f(pm+r)]` up to the explicit error
   `2·M·r/p²/Z`; at `r=0` the reduction is EXACT.
3. **Shift invariance** for the `+1` offset (`liouvilleWindow` starts at `λ(n+1)`,
   the failure Prop at `λ(n)`) — the `harmonic_shift_l1_le`-grade error.
4. **Sum over `j < H` and `p ∈ 𝒫_H`**: the main term is `(∑_p 1/p)·H·X`; the
   Mertens LOWER bound `∑_p 1/p ≥ cM/log H` (hypothesis `hmert`, node D3) supplies
   the `H/log H` grade.

## STOP-AND-FLAG status (this landing)

The structural spine — the pointwise unfold, the residue-projection identity, and
the per-pair dilation reduction — is proven here (`fBridgeF_liouville_apply`,
`residueProj_residueWindow`, `perPair_dilation`).  The full main-term extraction
(steps 1–4 composed with explicit-constant error-below-half-main control) needs
a shift-invariance-for-correlation-integrals lemma NOT in the landed carrier set;
it is isolated as the δ-independent hypothesis `hreduce` of `fBridge_of_singleCorr`
(the F-bridge integral dominates half the main term `(∑_p 1/p)·H·|X|`).  The
frozen conclusion is derived from `hreduce` + `hmert` + `hseed` by the glue below.
The residual (a discharge of `hreduce`, requiring the regime set
`hx hω hωx hne heps heps1 hωbig`) is the STMT2 flag / W3-e-final obligation.
-/
import Salt.Entropy.Chowla.ChowlaFailure
import Salt.Entropy.Chowla.Dilation
import Salt.Entropy.Chowla.FBridge
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-- **The residue-projection identity.**  Reducing the residue datum `Y_H = n mod P_H`
through the natural projection `ZMod P_H →+* ZMod p` recovers `n mod p`: both are the
`ℕ`-cast of `n`, and ring homs commute with `Nat.cast`. -/
lemma residueProj_residueWindow (eps : ℚ) (H : ℕ) (p : primeWindow eps H) (n : ℕ) :
    residueProj eps H p (residueWindow eps H n) = (n : ZMod (p : ℕ)) := by
  simp only [residueWindow, residueProj]
  exact map_natCast _ n

/-- **Window value of the Liouville window** (junk-zero at the interior index):
`windowVal H (liouvilleWindow H n) j = λ(n+j+1)` for `j < H` (`liouvilleWindow`
starts at `λ(n+1)`). -/
lemma windowVal_liouvilleWindow (H n j : ℕ) (hj : j < H) :
    windowVal H (liouvilleWindow H n) j = ArithmeticFunction.liouville (n + j + 1) := by
  unfold windowVal
  rw [dif_pos hj, liouvilleWindow_apply]

/-- **STMT2, structural spine (2a): the pointwise F-bridge unfold.**  At the Liouville
model the integrand is the residue-gated double product: for each window prime `p`
and each `j < H`, the gate `p ∣ n+j` selects `λ(n+j+1)·(windowVal … (j+p))` (the
second factor carries the junk-zero boundary convention, i.e. `λ(n+j+p+1)` when
`j+p < H`, else `0`).  This is Tao's (2.12)/(3.14) shape read at
`v = liouvilleWindow H n`, `y = residueWindow eps H n`. -/
lemma fBridgeF_liouville_apply (eps : ℚ) (H n : ℕ) :
    fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
      = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          if ((n + j : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ)
          else 0 := by
  unfold fBridgeF
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [residueProj_residueWindow]
  unfold fBridgeG
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjH : j < H := Finset.mem_range.mp hj
  have hgate : ((j : ℕ) : ZMod (p : ℕ)) = -((n : ℕ) : ZMod (p : ℕ))
      ↔ ((n + j : ℕ) : ZMod (p : ℕ)) = 0 := by
    rw [Nat.cast_add, add_comm, add_eq_zero_iff_eq_neg]
  by_cases hc : ((n + j : ℕ) : ZMod (p : ℕ)) = 0
  · rw [if_pos (hgate.mpr hc), if_pos hc, windowVal_liouvilleWindow H n j hjH]
  · rw [if_neg (fun h => hc (hgate.mp h)), if_neg hc]

/-- Every real-cast Liouville value has modulus `≤ 1` (`±1` on positive arguments,
`0` at `0`). -/
lemma abs_liouville_le_one (k : ℕ) : |(ArithmeticFunction.liouville k : ℝ)| ≤ 1 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rcases Finset.mem_insert.mp (liouville_mem_pm_one hk) with h | h
    · rw [h]; norm_num
    · rw [Finset.mem_singleton.mp h]; norm_num

/-- **STMT2, structural spine (2a): the per-pair dilation reduction.**  The direct
specialization of the landed carrier `dilation_error_div` to the `(p, j)` correlation
`f_{p,j}(n) = λ(n+j+1)·λ(n+j+p+1)` at the parameter mapping

    q ↦ p,   r ↦ rj  (the residue `n ≡ rj (mod p)` realizing the gate `p ∣ n+j`),
    f ↦ f_{p,j},   M ↦ 1,   Z ↦ the window normalizer.

The residue-class window sum (over `{n ≡ rj (p)}`, normalized by `Z`) equals
`(1/p)·(dilated sum of f_{p,j}(pm+rj))/Z` up to the EXPLICIT error `2·rj/p²/Z`
(exact at `rj = 0`).  This is Tao's affine/dilation step per `(p, j)`; summing it
over `j < H` and `p ∈ 𝒫_H`, together with multiplicativity and shift invariance,
is the residual `hreduce` producer. -/
lemma perPair_dilation {x ω : ℕ} (p j rj : ℕ) (hp : 1 ≤ p) (hrj : rj ≤ x / ω)
    {Z : ℝ} (hZ : 0 < Z) :
    |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = rj),
        ((ArithmeticFunction.liouville (n + j + 1) : ℝ)
          * (ArithmeticFunction.liouville (n + j + p + 1) : ℝ)) / (n : ℝ)) / Z
        - 1 / (p : ℝ) *
          ((∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = rj)).image (fun n => n / p),
              ((ArithmeticFunction.liouville (p * m + rj + j + 1) : ℝ)
                * (ArithmeticFunction.liouville (p * m + rj + j + p + 1) : ℝ)) / (m : ℝ)) / Z)|
      ≤ 2 * 1 * (rj : ℝ) / (p : ℝ) ^ 2 / Z :=
  dilation_error_div hp hrj
    (f := fun n => (ArithmeticFunction.liouville (n + j + 1) : ℝ)
        * (ArithmeticFunction.liouville (n + j + p + 1) : ℝ)) (M := 1)
    (fun k => by
      rw [abs_mul]
      exact (mul_le_one₀ (abs_liouville_le_one _) (abs_nonneg _) (abs_liouville_le_one _)))
    hZ

/-- **STMT2 / Tao Prop 2.6 (frozen conclusion).**  From the single-correlation lower
bound `hseed : δ ≤ |X|` (`X = ∫ λ(n)λ(n+1) ∂logMeasure`, produced by
`singleCorr_of_fails`), the Mertens LOWER bound `hmert : cM/log H ≤ ∑_p 1/p` (node D3),
and the multiplicativity p-averaging reduction `hreduce` (the F-bridge integral
dominates half the main term `(∑_p 1/p)·H·|X|`), the F-bridge expectation obeys the
`c·(δ·H/log H)` lower bound with `c = cM/2`.

`hreduce` is δ-INDEPENDENT (it compares the F-bridge integral to `|X|`), so it sits
before the frozen trailing binder `{δ} (hδ) (hseed)`; its discharge (the full
multiplicativity + dilation + shift-invariance + error-below-half chain, using the
regime set `hx hω hωx hne heps heps1 hωbig`) is the residual W3-e-final obligation
(see the module note and `flags.md`). -/
theorem fBridge_of_singleCorr (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hlog : 1 ≤ Real.log (H : ℝ)) {cM : ℝ} (hcM : 0 < cM)
    (hmert : cM / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
    (hreduce : (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|)
    {δ : ℝ} (hδ : 0 < δ)
    (hseed : δ ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|) :
    ∃ c : ℝ, 0 < c ∧
      c * (δ * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)| := by
  set SP : ℝ := ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) with hSP
  set X : ℝ := |∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| with hX
  have hlogpos : (0 : ℝ) < Real.log (H : ℝ) := by linarith
  have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hSPnn : (0 : ℝ) ≤ SP := by
    rw [hSP]; exact Finset.sum_nonneg (fun p hp => by positivity)
  have hXnn : (0 : ℝ) ≤ X := abs_nonneg _
  -- `cM ≤ SP · log H` from the Mertens lower bound.
  have hcM_le : cM ≤ SP * Real.log (H : ℝ) := (div_le_iff₀ hlogpos).mp hmert
  -- `cM · δ ≤ SP · X · log H` from `hcM_le` and `hseed`.
  have hkey : cM * δ ≤ SP * X * Real.log (H : ℝ) := by
    calc cM * δ ≤ (SP * Real.log (H : ℝ)) * X :=
          mul_le_mul hcM_le hseed hδ.le (mul_nonneg hSPnn hlogpos.le)
      _ = SP * X * Real.log (H : ℝ) := by ring
  refine ⟨cM / 2, by linarith, ?_⟩
  -- `(cM/2)·(δH/log H) ≤ (1/2)·SP·H·X ≤ |∫F|`.
  have hle1 : (cM / 2) * (δ * (H : ℝ) / Real.log (H : ℝ)) ≤ (1 / 2) * SP * (H : ℝ) * X := by
    rw [mul_div_assoc', div_le_iff₀ hlogpos]
    nlinarith [mul_le_mul_of_nonneg_right hkey hHnn, hHnn, hSPnn, hXnn, hlogpos.le]
  exact hle1.trans hreduce

end Salt.Entropy.Chowla
