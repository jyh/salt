/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.SpineFinal

/-!
# The sign-split mass floor (wall-L4)

Design provenance: the 08/15 wall-dream's surviving `L4` arm, design block
`l4a1-design-block-0815.md` (REV-2, refuter-passed).

## The objects

On the log-Chowla window `(x/ω, x]` the two `λ(n)·λ(n+1)` sign classes carry the
`1/n`-weighted masses `agreeMass` (the product is `+1`) and `disagreeMass` (the
product is `−1`).  Both definitions and both identities below are UNCONDITIONAL in
`x` and `ω`: no regime hypothesis enters them.

Because `λ` vanishes only at `0` (`ArithmeticFunction.liouville_ne_zero`) and every
window element is `≥ 1` (`window_one_le`), the two classes exhaust the window.
`agreeMass_add_disagreeMass` is the resulting partition `A + D = Σ 1/n`, and
`agreeMass_sub_disagreeMass` identifies `A − D` with exactly the sum whose absolute
value `logChowla2Fails` compares against `ε·log ω`.  The `±1` alphabet of `λ` is used
in the second identity and in no other proof here.

## The floor

`sign_split_of_not_fails` is parametric in the regime and takes the plain hypothesis
`¬ logChowla2Fails R.eps R.x R.ω`; from the two identities and
`harmonic_window_bounds` alone each mass is at least `((1 − ε)·log ω − 1)/2`.  No case
split, no minimum lemma and no sign hypothesis enter, and the chain is non-strict end
to end.  `sign_split_quarter_log` weakens it to the `ε`-free form using `R.heps1`
together with `0 ≤ log ω`, `sign_split_door_only` instantiates the parametric form at
the spine's witnessed regime through `log_chowla_two_door_only_xi`, and
`regime_logOmega_ge` — the in-leaf re-derivation of `129 ≤ log ω` from `hωbig` — makes
the floor positive (`sign_split_pos`) rather than vacuous.

Scope: log-weighted, at the single `ε` the spine fixes, at one regime, conditional on
the door.
-/

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ### D1 · the two sign-class masses -/

open ArithmeticFunction in
/-- **The agreeing class's harmonic mass** on the window `(x/ω, x]`: the `1/n`-weighted
count of those `n` with `λ(n)·λ(n+1) > 0`.  Unconditional in `x` and `ω`; the filter
predicate is an inequality between integers, decidable by `Int.decLt`. -/
noncomputable def agreeMass (x ω : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => 0 < liouville n * liouville (n + 1)),
    (n : ℝ)⁻¹

open ArithmeticFunction in
/-- **The disagreeing class's harmonic mass** on the window `(x/ω, x]`: the `1/n`-weighted
count of those `n` with `λ(n)·λ(n+1) < 0`.  Unconditional in `x` and `ω`. -/
noncomputable def disagreeMass (x ω : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => liouville n * liouville (n + 1) < 0),
    (n : ℝ)⁻¹

/-- Both masses are sums of reciprocals of naturals, hence nonnegative (sanity furniture;
nothing below consumes it). -/
theorem agreeMass_nonneg (x ω : ℕ) : 0 ≤ agreeMass x ω :=
  Finset.sum_nonneg fun n _ => by positivity

/-- Companion of `agreeMass_nonneg` (sanity furniture; nothing below consumes it). -/
theorem disagreeMass_nonneg (x ω : ℕ) : 0 ≤ disagreeMass x ω :=
  Finset.sum_nonneg fun n _ => by positivity

/-! ### The two window helpers -/

open ArithmeticFunction in
/-- On the window the pair product never vanishes: `λ` is nonzero away from `0`, and
`window_one_le` puts `n ≥ 1` unconditionally (no regime hypothesis). -/
private theorem liouville_pair_ne_zero {x ω n : ℕ} (hn : n ∈ Finset.Ioc (x / ω) x) :
    liouville n * liouville (n + 1) ≠ 0 :=
  mul_ne_zero (liouville_ne_zero (Nat.one_le_iff_ne_zero.mp (window_one_le hn)))
    (liouville_ne_zero (by omega : n + 1 ≠ 0))

open ArithmeticFunction in
/-- The `±1` alphabet of the pair product, for `n ≠ 0`. -/
private theorem liouville_pair_eq_one_or {n : ℕ} (hn : n ≠ 0) :
    liouville n * liouville (n + 1) = 1 ∨ liouville n * liouville (n + 1) = -1 := by
  rw [liouville_apply hn, liouville_apply (by omega : n + 1 ≠ 0)]
  rcases neg_one_pow_eq_or ℤ (cardFactors n) with h1 | h1 <;>
    rcases neg_one_pow_eq_or ℤ (cardFactors (n + 1)) with h2 | h2 <;>
      rw [h1, h2] <;> norm_num

open ArithmeticFunction in
/-- The filter bridge: on the window, `< 0` and `¬ (0 < ·)` cut out the SAME set, because
the pair product is never `0`.  Needed because `Finset.sum_filter_add_sum_filter_not`
partitions along the negation, not along the strict opposite inequality. -/
private theorem disagree_filter_eq (x ω : ℕ) :
    (Finset.Ioc (x / ω) x).filter (fun n => liouville n * liouville (n + 1) < 0)
      = (Finset.Ioc (x / ω) x).filter
          (fun n => ¬ (0 < liouville n * liouville (n + 1))) := by
  refine Finset.filter_congr fun n hn => ?_
  have h := liouville_pair_ne_zero hn
  exact ⟨fun hlt => not_lt.mpr hlt.le, fun hnp => lt_of_le_of_ne (not_lt.mp hnp) h⟩

/-! ### T1 · the partition -/

open ArithmeticFunction in
/-- **The partition (unconditional).**  The two sign classes exhaust the window, so their
masses add up to the window's whole harmonic mass `Σ 1/n`.  Stated for bare naturals:
no regime hypothesis is used or available. -/
theorem agreeMass_add_disagreeMass (x ω : ℕ) :
    agreeMass x ω + disagreeMass x ω = ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
  unfold agreeMass disagreeMass
  rw [disagree_filter_eq, Finset.sum_filter_add_sum_filter_not]

/-! ### T2 · the difference -/

open ArithmeticFunction in
/-- **The difference (unconditional).**  The signed gap between the two masses is exactly
the correlation sum whose absolute value `logChowla2Fails` measures.  This is the only
proof in the file that uses the `±1` alphabet of `λ`. -/
theorem agreeMass_sub_disagreeMass (x ω : ℕ) :
    agreeMass x ω - disagreeMass x ω
      = ∑ n ∈ Finset.Ioc (x / ω) x,
          (liouville n : ℝ) * (liouville (n + 1) : ℝ) / (n : ℝ) := by
  have key := Finset.sum_filter_add_sum_filter_not (Finset.Ioc (x / ω) x)
    (fun n => 0 < liouville n * liouville (n + 1))
    (fun n => (liouville n : ℝ) * (liouville (n + 1) : ℝ) / (n : ℝ))
  rw [← key]
  have hA : ∑ n ∈ (Finset.Ioc (x / ω) x).filter
        (fun n => 0 < liouville n * liouville (n + 1)),
        (liouville n : ℝ) * (liouville (n + 1) : ℝ) / (n : ℝ) = agreeMass x ω := by
    unfold agreeMass
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_filter] at hn
    have hd := liouville_pair_eq_one_or (Nat.one_le_iff_ne_zero.mp (window_one_le hn.1))
    have h1 : liouville n * liouville (n + 1) = 1 := by
      rcases hd with h | h
      · exact h
      · exact absurd hn.2 (by rw [h]; norm_num)
    have hcast : (liouville n : ℝ) * (liouville (n + 1) : ℝ) = 1 := by
      have hc := congrArg (fun z : ℤ => (z : ℝ)) h1
      push_cast at hc
      exact hc
    rw [hcast, one_div]
  have hD : ∑ n ∈ (Finset.Ioc (x / ω) x).filter
        (fun n => ¬ (0 < liouville n * liouville (n + 1))),
        (liouville n : ℝ) * (liouville (n + 1) : ℝ) / (n : ℝ) = -disagreeMass x ω := by
    unfold disagreeMass
    rw [disagree_filter_eq, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_filter] at hn
    have hd := liouville_pair_eq_one_or (Nat.one_le_iff_ne_zero.mp (window_one_le hn.1))
    have h1 : liouville n * liouville (n + 1) = -1 := by
      rcases hd with h | h
      · exact absurd (by rw [h]; norm_num : (0 : ℤ) < liouville n * liouville (n + 1)) hn.2
      · exact h
    have hcast : (liouville n : ℝ) * (liouville (n + 1) : ℝ) = -1 := by
      have hc := congrArg (fun z : ℤ => (z : ℝ)) h1
      push_cast at hc
      exact hc
    rw [hcast, neg_div, one_div]
  rw [hA, hD]
  ring

/-! ### D0 · the regime's own `log ω` floor -/

/-- **`129 ≤ log ω` at every regime.**  Re-derived in this leaf from `R.hωbig`,
`R.heps1` and `R.hPNTwindow`: `ε ≤ 1/2` puts `64/ε ≥ 128`, and `ε²·H₊ ≥ ε²·H₋ ≥ 4000 ≥ 1`
makes the `log` term of `hωbig` nonnegative, so `hωbig`'s right-hand side is at least
`0 + 128 + 1`.  `Salt.MR.s13_logOmega_ge` runs the same three ingredients to the weaker
`4`; it lives downstream of this file, so the argument is repeated here rather than
imported. -/
theorem regime_logOmega_ge (R : ChowlaRegime) : (129 : ℝ) ≤ Real.log (R.ω : ℝ) := by
  have hεpos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hεhalf : (R.eps : ℝ) ≤ 1 / 2 := by
    have h : ((R.eps : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast R.heps1
    simpa using h
  have hHloR : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hsqrt : (2000 : ℝ) ≤ Real.sqrt (R.Hlo : ℝ) := by
    have h : Real.sqrt (4000000 : ℝ) ≤ Real.sqrt (R.Hlo : ℝ) := Real.sqrt_le_sqrt hHloR
    rwa [show (4000000 : ℝ) = 2000 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2000)] at h
  have hw := R.hPNTwindow
  have h4000 : (4000 : ℝ) ≤ (R.eps : ℝ) ^ 2 * (R.Hlo : ℝ) := by linarith
  have hHle : (R.Hlo : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast R.hHlohi
  have hmono : (R.eps : ℝ) ^ 2 * (R.Hlo : ℝ) ≤ (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) :=
    mul_le_mul_of_nonneg_left hHle (sq_nonneg _)
  have hlogpos : (0 : ℝ) ≤ Real.log ((R.eps : ℝ) ^ 2 * (R.Hhi : ℝ)) :=
    Real.log_nonneg (by linarith)
  have h16 : (0 : ℝ) ≤ 16 / (R.eps : ℝ) * Real.log ((R.eps : ℝ) ^ 2 * (R.Hhi : ℝ)) :=
    mul_nonneg (by positivity) hlogpos
  have h64 : (128 : ℝ) ≤ 64 / (R.eps : ℝ) := by
    rw [le_div_iff₀ hεpos]; linarith
  linarith [R.hωbig]

/-! ### T3 · the sign-split floor -/

/-- "Conditional on the MRT door (MRTUniformityXi, the Ξ_H-restricted form — Tao
arXiv:1509.05422v2 Prop 2.4, proved in Matomäki–Radziwiłł–Tao arXiv:1503.05121 but not yet
formalized here), the log-Chowla-2 spine's ONE witnessed regime (x, ω, ε) admits a
two-sided sign-mass floor: on the window (x/ω, x], each of the two λ(n)λ(n+1) sign
classes carries harmonic log-mass at least ((1−ε)·log ω − 1)/2, hence at least
(1/4)·log ω − 1/2 — and that floor is POSITIVE (≥ 31.75, via the regime's own
129 ≤ log ω). Log-weighted, fixed-ε, single regime, door-conditional; this is a
non-degeneracy bound, NOT equidistribution and NOT natural-density Chowla (Tao's
transport disclaimer, chowla.txt:196-200; the grade-inflation law,
wall3-d4-ratified.md:401)." -/
theorem sign_split_of_not_fails {R : ChowlaRegime}
    (h : ¬ logChowla2Fails R.eps R.x R.ω) :
    (((1 : ℝ) - (R.eps : ℝ)) * Real.log (R.ω : ℝ) - 1) / 2 ≤ agreeMass R.x R.ω ∧
      (((1 : ℝ) - (R.eps : ℝ)) * Real.log (R.ω : ℝ) - 1) / 2 ≤ disagreeMass R.x R.ω := by
  unfold logChowla2Fails at h
  rw [not_lt, ← agreeMass_sub_disagreeMass] at h
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  have hsum := agreeMass_add_disagreeMass R.x R.ω
  have hZ := (harmonic_window_bounds R.hx R.hω R.hωx).1
  constructor <;> linarith

/-- "Conditional on the MRT door (MRTUniformityXi, the Ξ_H-restricted form — Tao
arXiv:1509.05422v2 Prop 2.4, proved in Matomäki–Radziwiłł–Tao arXiv:1503.05121 but not yet
formalized here), the log-Chowla-2 spine's ONE witnessed regime (x, ω, ε) admits a
two-sided sign-mass floor: on the window (x/ω, x], each of the two λ(n)λ(n+1) sign
classes carries harmonic log-mass at least ((1−ε)·log ω − 1)/2, hence at least
(1/4)·log ω − 1/2 — and that floor is POSITIVE (≥ 31.75, via the regime's own
129 ≤ log ω). Log-weighted, fixed-ε, single regime, door-conditional; this is a
non-degeneracy bound, NOT equidistribution and NOT natural-density Chowla (Tao's
transport disclaimer, chowla.txt:196-200; the grade-inflation law,
wall3-d4-ratified.md:401)." -/
theorem sign_split_door_only :
    ∃ (δ₀ : ℝ) (R : ChowlaRegime), 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
        (((1 : ℝ) - (R.eps : ℝ)) * Real.log (R.ω : ℝ) - 1) / 2 ≤ agreeMass R.x R.ω ∧
          (((1 : ℝ) - (R.eps : ℝ)) * Real.log (R.ω : ℝ) - 1) / 2
            ≤ disagreeMass R.x R.ω := by
  obtain ⟨δ₀, R, hδ₀pos, hbody⟩ := log_chowla_two_door_only_xi
  exact ⟨δ₀, R, hδ₀pos,
    fun δ hδpos hδ hdoor => sign_split_of_not_fails (hbody δ hδpos hδ hdoor)⟩

/-! ### T4 · the `ε`-free form -/

/-- "Conditional on the MRT door (MRTUniformityXi, the Ξ_H-restricted form — Tao
arXiv:1509.05422v2 Prop 2.4, proved in Matomäki–Radziwiłł–Tao arXiv:1503.05121 but not yet
formalized here), the log-Chowla-2 spine's ONE witnessed regime (x, ω, ε) admits a
two-sided sign-mass floor: on the window (x/ω, x], each of the two λ(n)λ(n+1) sign
classes carries harmonic log-mass at least ((1−ε)·log ω − 1)/2, hence at least
(1/4)·log ω − 1/2 — and that floor is POSITIVE (≥ 31.75, via the regime's own
129 ≤ log ω). Log-weighted, fixed-ε, single regime, door-conditional; this is a
non-degeneracy bound, NOT equidistribution and NOT natural-density Chowla (Tao's
transport disclaimer, chowla.txt:196-200; the grade-inflation law,
wall3-d4-ratified.md:401)." -/
theorem sign_split_quarter_log {R : ChowlaRegime}
    (h : ¬ logChowla2Fails R.eps R.x R.ω) :
    (1 / 4 : ℝ) * Real.log (R.ω : ℝ) - 1 / 2 ≤ agreeMass R.x R.ω ∧
      (1 / 4 : ℝ) * Real.log (R.ω : ℝ) - 1 / 2 ≤ disagreeMass R.x R.ω := by
  obtain ⟨hA, hD⟩ := sign_split_of_not_fails h
  have hω2 : 2 ≤ R.ω := R.hω
  have hω1 : (1 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast (by omega : 1 ≤ R.ω)
  have hlog0 : 0 ≤ Real.log (R.ω : ℝ) := Real.log_nonneg hω1
  have heps : (R.eps : ℝ) ≤ 1 / 2 := by
    have hq : ((R.eps : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast R.heps1
    simpa using hq
  constructor <;> nlinarith [hlog0, heps, mul_nonneg (sub_nonneg.mpr heps) hlog0]

/-! ### T5 · non-vacuity -/

/-- **The floor is positive**, `≥ 31.75`, from `regime_logOmega_ge` alone: the bound of
`sign_split_quarter_log` is not an empty inequality at any regime. -/
theorem sign_split_pos (R : ChowlaRegime) :
    (0 : ℝ) < (1 / 4 : ℝ) * Real.log (R.ω : ℝ) - 1 / 2 := by
  have h := regime_logOmega_ge R
  linarith

/-- **The mass-relative form.**  Measured against the window's own harmonic mass
`Z = Σ_{n ∈ (x/ω, x]} 1/n`, each sign class carries at least `Z/5`: the upper harmonic
bound gives `Z ≤ log ω + 1`, and `129 ≤ log ω` makes `(log ω)/4 − 1/2 ≥ (log ω + 1)/5`.
The constant `5` is what this route yields; it is not claimed to be sharp. -/
theorem sign_split_fifth {R : ChowlaRegime}
    (h : ¬ logChowla2Fails R.eps R.x R.ω) :
    (∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹) / 5 ≤ agreeMass R.x R.ω ∧
      (∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹) / 5 ≤ disagreeMass R.x R.ω := by
  obtain ⟨hA, hD⟩ := sign_split_quarter_log h
  have hZ := (harmonic_window_bounds R.hx R.hω R.hωx).2
  have hlog := regime_logOmega_ge R
  constructor <;> linarith

end Salt.Entropy.Chowla
