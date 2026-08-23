/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The Theorem-2.3 conditional shell (Tao arXiv:1509.05422v1 §2–§3), spine node W3-E-GLUE

The wave-3 capstone: compose the four landed keystones of the log-Chowla spine
into a single contradiction theorem, with every still-unproven input threaded
through as an EXPLICIT named hypothesis (the tower / regime / GB tracks /
W3-e-final discharge them downstream).  The composition is `⟹ False`.

The chain (`docs/exploration/s3-a3-design.md`, the MRT-door / additive-energy
seam sketch):

* `outer_combine` (W3-a-3c) turns the `(2.11)` door `h211` into a lower bound
  on the OUTER mean of the two-point correlation, up to the explicit `ERROR`.
* `circle_method_estimate` (Lemma 3.4) bounds the correlation PER window by
  `C·(H/log H)·(ε² + Σ_ξ (1/H)‖dft(window)‖)` — entered as `hcirc` (its
  discharger is `circle_method_estimate`, obtained at `x₁ = x₂ = liouvilleWindow`;
  the constant `C` is existential there, so it is a shell parameter here).
* `bigXi_bounded_of_sieve` (Lemma 3.5) gives `|Ξ_H| ≤ K` — entered as `hXi`
  (its discharger is `bigXi_bounded_of_sieve` at `H ≥ H₀`, `H₀` from the regime).
* `contradiction_of_mrtDoor` (Prop 2.4 seam) fires the door at `α = −ξ/H` and
  collides `c₀ε ≤ Σ` with `K·δ < c₀ε` — INVOKED as the closer.

**Bridge A** (`windowExpSum_norm_eq_dft`): the circle method's Fourier carrier
`‖dft(fun j ↦ windowVal H (liouvilleWindow H n) j.val) ξ‖` equals the door's
`‖windowExpSum H n (−ξ.val/H)‖`.  The two are the same `H`-term window sum; they
differ by the `i ↦ i+1` phase offset (an overall unit-modulus factor
`exp(2πiα)`, so the norms agree) and the `ZMod H ↔ Fin H` reindex.  The door is
instantiated at `α = −ξ.val/H`, matching the mathlib character `exp(+2πi·/N)`.

**Bridge B** (inline): `outer_combine` bounds `|∫ correlation|`; `hcirc` bounds
the correlation per window; `norm_integral_le_integral_norm` + `integral_finsetSum`
(integrability by `integrable_of_finiteSupport`, `logMeasure` is finitely
supported) pass the integral inside the finite `ξ`-sum and Bridge A converts each
`∫‖dft‖` into the door's `∫‖windowExpSum‖`.
-/
import Salt.Entropy.Chowla.OuterCombine
import Salt.Entropy.Chowla.MRTDoor
import Salt.Entropy.Chowla.LargeSpectrumBound
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-- The explicit `outer_combine` error term, abbreviated for the shell's budget
hypotheses.  Matches the second summand of `outer_combine`'s conclusion LHS
verbatim (`ε²H/log H` plus the `boxGrade`-weighted good/bad budgets). -/
noncomputable def shellError (R : ChowlaRegime) (H : ℕ) (t g κ : ℝ) : ℝ :=
  (R.eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
    + 2 * boxGrade R.eps H * ((t + 2 * Real.log 2) / g
        + (κ + (Real.log (PH R.eps H : ℝ)
            - H[residueWindow R.eps H; logMeasure R.x R.ω])) / t)

/-- **Bridge A** (the dft ↔ windowExpSum carrier identification).

The circle method's Fourier term at the Liouville window `x₁ = liouvilleWindow H n`,
`‖ZMod.dft (fun j ↦ windowVal H (liouvilleWindow H n) j.val) ξ‖`, equals the MRT
door's `‖windowExpSum H n (−ξ.val/H)‖`.  Both are the same `H`-term window sum;
they differ by the door's `i ↦ i+1` phase offset — an overall unit-modulus factor
`exp(2πiα)` with `α = −ξ.val/H` — so the norms coincide.  The mathlib character
`stdAddChar` has phase `exp(+2πi·/N)`, matching the door fired at `α = −ξ.val/H`;
no reflection is needed. -/
private lemma windowExpSum_norm_eq_dft {H : ℕ} [NeZero H] (n : ℕ) (ξ : ZMod H) :
    ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖
      = ‖ZMod.dft (fun j : ZMod H =>
          (windowVal H (liouvilleWindow H n) (ZMod.val j) : ℂ)) ξ‖ := by
  classical
  set Φ : ZMod H → ℂ := fun j => (windowVal H (liouvilleWindow H n) (ZMod.val j) : ℂ) with hΦ
  -- the character-to-exp conversion, per `expSum_eq_char_sum`
  have hchar : ∀ j : ZMod H, ZMod.stdAddChar (-(j * ξ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I
          * ((-(ξ.val : ℝ) / (H : ℝ)) : ℂ) * ((ZMod.val j : ℕ) : ℂ)) := by
    intro j
    have hrw : -(j * ξ) = ((-((ZMod.val j * ξ.val : ℕ)) : ℤ) : ZMod H) := by
      push_cast [ZMod.natCast_zmod_val]; ring
    rw [hrw, ZMod.stdAddChar_coe]; push_cast; ring_nf
  -- the reindex equiv `Fin H ≃ ZMod H`
  let e : Fin H ≃ ZMod H :=
    { toFun := fun i => ((i : ℕ) : ZMod H)
      invFun := fun j => ⟨ZMod.val j, ZMod.val_lt j⟩
      left_inv := fun i => by
        apply Fin.ext; exact ZMod.val_natCast_of_lt i.isLt
      right_inv := fun j => by simp }
  have hev : ∀ i : Fin H, ZMod.val (e i) = (i : ℕ) := fun i => ZMod.val_natCast_of_lt i.isLt
  have hΦe : ∀ i : Fin H, Φ (e i) = (liouvilleWindow H n i : ℂ) := by
    intro i
    have hwv : windowVal H (liouvilleWindow H n) (ZMod.val (e i)) = liouvilleWindow H n i := by
      rw [hev i, windowVal, dif_pos i.isLt]
    simp only [hΦ, hwv]
  -- the factored identity: `windowExpSum = exp(2πiα) · dft Φ ξ`, `α = −ξ.val/H`
  have key : windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-(ξ.val : ℝ) / (H : ℝ)) : ℂ))
          * ZMod.dft Φ ξ := by
    unfold windowExpSum
    rw [dft_is_fourier_coeff, Finset.mul_sum, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hchar (e i), smul_eq_mul, hΦe i, hev i, ← mul_assoc, ← Complex.exp_add,
      mul_comm ((liouvilleWindow H n i : ℂ))]
    congr 2
    push_cast; ring
  rw [key, norm_mul]
  have hu : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-(ξ.val : ℝ) / (H : ℝ)) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have : (2 * (Real.pi : ℂ) * Complex.I * ((-(ξ.val : ℝ) / (H : ℝ)) : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero]
  rw [hu, one_mul]

/-- **W3-E-GLUE, the Theorem-2.3 conditional shell.**

The wave-3 capstone: the four landed keystones of the log-Chowla spine compose to
a contradiction, with every still-open input threaded through as a named
hypothesis (dischargers noted per hypothesis).

* `outer_combine` (INVOKED) turns the `(2.11)` door `h211` into the correlation
  mass lower bound `c₁·εH/log H − shellError ≤ |∫ correlation|`.
* `hcirc` is the per-window `circle_method_estimate` bound (discharger:
  `circle_method_estimate` at `x₁ = x₂ = liouvilleWindow H n`; its constant `C`
  is existential there, hence a shell parameter).
* `hXi` is the large-spectrum count `|Ξ_H| ≤ K` (discharger:
  `bigXi_bounded_of_sieve` at `H ≥ H₀`, `H₀` supplied by the regime).
* `contradiction_of_mrtDoor` (INVOKED) fires the MRT theorem-door at `α = −ξ/H`.

Bridge A (`windowExpSum_norm_eq_dft`) identifies the circle carrier with the door
carrier; Bridge B (inline: `abs_integral_le_integral_abs`, `integral_finsetSum`)
passes the integral through the finite `ξ`-sum.  `hbudget1`/`hbudget2` are the
numeric-closure inequalities the regime / W3-e-final discharge. -/
theorem log_chowla_two_shell
    (R : ChowlaRegime) {H : ℕ} [NeZero H] (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    -- `outer_combine`'s regime-derivable prerequisites (tower / regime dischargers):
    (hH : 3 ≤ H) (hlog : 1 ≤ Real.log (H : ℝ)) (hne : (primeWindow R.eps H).Nonempty)
    (hreg : Real.sqrt (H : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) / 2)
    (hhead : 8 * (PH R.eps H : ℝ) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ))
    {t : ℝ} (ht : 0 < t) {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
        / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    {κ : ℝ} (hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω] ≤ κ)
    {c₁ : ℝ} (hc₁ : 0 < c₁)
    -- the `(2.11)` contradiction door (`outer_combine` input `h211`):
    (h211 : c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ n, fBridgeF R.eps H (liouvilleWindow H n) (residueWindow R.eps H n)
            ∂(logMeasure R.x R.ω)|)
    -- the circle-method Fourier bound (discharger: `circle_method_estimate`):
    {C : ℝ} (hC : 0 < C)
    (hcirc : ∀ n : ℕ,
      |∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ))
                * ‖ZMod.dft (fun j : ZMod H =>
                    (windowVal H (liouvilleWindow H n) (ZMod.val j) : ℂ)) ξ‖))
    -- the large-spectrum count (discharger: `bigXi_bounded_of_sieve`):
    {K : ℝ} (hXi : ((bigXi R.eps H).card : ℝ) ≤ K)
    -- the MRT theorem-door (Prop 2.4) and the two numeric-closure budgets:
    {δ c₀ : ℝ} (hdoor : MRTUniformity R δ)
    (hbudget1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
          + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + shellError R H t g κ
        ≤ c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)))
    (hbudget2 : K * δ < c₀ * (R.eps : ℝ)) :
    False := by
  classical
  haveI hpm : IsProbabilityMeasure (logMeasure R.x R.ω) :=
    isProbabilityMeasure_logMeasure R.hx R.hω
  have hHpos : 0 < H := NeZero.pos H
  have hlogpos : 0 < Real.log (H : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hApos : 0 < C * ((H : ℝ) / Real.log (H : ℝ)) :=
    mul_pos hC (div_pos (by exact_mod_cast hHpos) hlogpos)
  have heps1R : (R.eps : ℝ) ≤ 1 := by
    have h : R.eps ≤ 1 := le_trans R.heps1 (by norm_num)
    exact_mod_cast h
  -- (I) the `outer_combine` mass lower bound (with `shellError` folded, defeq).
  have hoc : c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) - shellError R H t g κ
      ≤ |∫ n, (∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ))
          ∂(logMeasure R.x R.ω)| :=
    outer_combine R.eps H R.hx R.hω R.hωx R.heps heps1R hne hreg hH hlog hhead
      ht hg hgle hI hc₁ h211
  -- abbreviations
  set gm : ℕ → ℝ := fun n => ∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
      (windowVal H (liouvilleWindow H n) j : ℝ)
        * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) with hgm
  set door : ℝ := ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ))
      * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ∂(logMeasure R.x R.ω) with hdoorS
  set RHS : ℕ → ℝ := fun n => C * ((H : ℝ) / Real.log (H : ℝ))
      * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ))
          * ‖ZMod.dft (fun j : ZMod H =>
              (windowVal H (liouvilleWindow H n) (ZMod.val j) : ℂ)) ξ‖) with hRHS
  have hcirc' : ∀ n, |gm n| ≤ RHS n := hcirc
  -- Bridge B, step 1+2: `|∫ gm| ≤ ∫ RHS`.
  have hB : |∫ n, gm n ∂(logMeasure R.x R.ω)| ≤ ∫ n, RHS n ∂(logMeasure R.x R.ω) :=
    le_trans abs_integral_le_integral_abs
      (integral_mono_ae (integrable_of_finiteSupport _) (integrable_of_finiteSupport _)
        (Filter.Eventually.of_forall hcirc'))
  -- Bridge B, step 3: `∫ RHS = C·(H/log H)·(ε² + door)` (Bridge A per `ξ`).
  have hRHSeq : ∫ n, RHS n ∂(logMeasure R.x R.ω)
      = C * ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2 + door) := by
    rw [hRHS, integral_const_mul]
    congr 1
    rw [integral_add (integrable_const _) (integrable_of_finiteSupport _), integral_const,
      probReal_univ, one_smul,
      integral_finsetSum (bigXi R.eps H) (fun ξ _ => integrable_of_finiteSupport _)]
    congr 1
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [integral_const_mul]
    congr 1
    exact integral_congr_ae
      (Filter.Eventually.of_forall (fun n => (windowExpSum_norm_eq_dft n ξ).symm))
  -- (★): assemble the chain.
  have hstar : c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) - shellError R H t g κ
      ≤ C * ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2 + door) :=
    le_trans hoc (le_trans hB (le_of_eq hRHSeq))
  -- derive the door's mass lower bound `c₀·ε ≤ door`.
  have hmul : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
      ≤ C * ((H : ℝ) / Real.log (H : ℝ)) * door := by
    have hexp : C * ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2 + door)
        = C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + C * ((H : ℝ) / Real.log (H : ℝ)) * door := by ring
    linarith [hstar, hbudget1, hexp]
  have hlower : c₀ * (R.eps : ℝ) ≤ door := le_of_mul_le_mul_left hmul hApos
  -- fire the MRT theorem-door.
  exact contradiction_of_mrtDoor R hlo hhi hHpos hdoor hXi hbudget2 hlower

/-- **W3-E-GLUE, the Ξ_H-restricted Theorem-2.3 conditional shell** (S0 XI-REWIRE).

Identical content to `log_chowla_two_shell`, but consuming the Tao-faithful
`MRTUniformityXi R δ` (`MRTDoor.lean`, α restricted to the ≤ K major-arc
frequencies `−ξ/H`, `ξ ∈ Ξ_H`) in place of the full `∀ α`-outside door.  The
door enters ONLY at the final seam call — the entire `outer_combine`/circle-method
derivation of the mass lower bound `hlower : c₀·ε ≤ door` (the same `door` sum,
`Σ_{ξ∈Ξ_H} (1/H)∫‖windowExpSum H · (−ξ/H)‖`) is door-independent, so it is
reproduced verbatim; only the closer swaps `contradiction_of_mrtDoor` for the
Ξ_H seam `contradiction_of_mrtDoorXi`.  Because the weakened door no longer
speaks at `α = 0`, `δ`-nonnegativity is no longer derivable from the door and is
taken as the explicit hypothesis `hδ : 0 ≤ δ` (per the SALVAGE ruling; the seam
consumes it directly).  Additive — `log_chowla_two_shell` is untouched. -/
theorem log_chowla_two_shell_xi
    (R : ChowlaRegime) {H : ℕ} [NeZero H] (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    (hH : 3 ≤ H) (hlog : 1 ≤ Real.log (H : ℝ)) (hne : (primeWindow R.eps H).Nonempty)
    (hreg : Real.sqrt (H : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) / 2)
    (hhead : 8 * (PH R.eps H : ℝ) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ))
    {t : ℝ} (ht : 0 < t) {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
        / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    {κ : ℝ} (hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω] ≤ κ)
    {c₁ : ℝ} (hc₁ : 0 < c₁)
    (h211 : c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ n, fBridgeF R.eps H (liouvilleWindow H n) (residueWindow R.eps H n)
            ∂(logMeasure R.x R.ω)|)
    {C : ℝ} (hC : 0 < C)
    (hcirc : ∀ n : ℕ,
      |∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ))
                * ‖ZMod.dft (fun j : ZMod H =>
                    (windowVal H (liouvilleWindow H n) (ZMod.val j) : ℂ)) ξ‖))
    {K : ℝ} (hXi : ((bigXi R.eps H).card : ℝ) ≤ K)
    -- the Ξ_H-restricted MRT door (Prop 2.4 major-arc form), explicit `0 ≤ δ`:
    {δ c₀ : ℝ} (hδ : 0 ≤ δ) (hdoor : MRTUniformityXi R δ)
    (hbudget1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
          + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + shellError R H t g κ
        ≤ c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)))
    (hbudget2 : K * δ < c₀ * (R.eps : ℝ)) :
    False := by
  classical
  haveI hpm : IsProbabilityMeasure (logMeasure R.x R.ω) :=
    isProbabilityMeasure_logMeasure R.hx R.hω
  have hHpos : 0 < H := NeZero.pos H
  have hlogpos : 0 < Real.log (H : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hApos : 0 < C * ((H : ℝ) / Real.log (H : ℝ)) :=
    mul_pos hC (div_pos (by exact_mod_cast hHpos) hlogpos)
  have heps1R : (R.eps : ℝ) ≤ 1 := by
    have h : R.eps ≤ 1 := le_trans R.heps1 (by norm_num)
    exact_mod_cast h
  -- (I) the `outer_combine` mass lower bound (with `shellError` folded, defeq).
  have hoc : c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) - shellError R H t g κ
      ≤ |∫ n, (∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ))
          ∂(logMeasure R.x R.ω)| :=
    outer_combine R.eps H R.hx R.hω R.hωx R.heps heps1R hne hreg hH hlog hhead
      ht hg hgle hI hc₁ h211
  -- abbreviations
  set gm : ℕ → ℝ := fun n => ∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
      (windowVal H (liouvilleWindow H n) j : ℝ)
        * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) with hgm
  set door : ℝ := ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ))
      * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ∂(logMeasure R.x R.ω) with hdoorS
  set RHS : ℕ → ℝ := fun n => C * ((H : ℝ) / Real.log (H : ℝ))
      * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ))
          * ‖ZMod.dft (fun j : ZMod H =>
              (windowVal H (liouvilleWindow H n) (ZMod.val j) : ℂ)) ξ‖) with hRHS
  have hcirc' : ∀ n, |gm n| ≤ RHS n := hcirc
  -- Bridge B, step 1+2: `|∫ gm| ≤ ∫ RHS`.
  have hB : |∫ n, gm n ∂(logMeasure R.x R.ω)| ≤ ∫ n, RHS n ∂(logMeasure R.x R.ω) :=
    le_trans abs_integral_le_integral_abs
      (integral_mono_ae (integrable_of_finiteSupport _) (integrable_of_finiteSupport _)
        (Filter.Eventually.of_forall hcirc'))
  -- Bridge B, step 3: `∫ RHS = C·(H/log H)·(ε² + door)` (Bridge A per `ξ`).
  have hRHSeq : ∫ n, RHS n ∂(logMeasure R.x R.ω)
      = C * ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2 + door) := by
    rw [hRHS, integral_const_mul]
    congr 1
    rw [integral_add (integrable_const _) (integrable_of_finiteSupport _), integral_const,
      probReal_univ, one_smul,
      integral_finsetSum (bigXi R.eps H) (fun ξ _ => integrable_of_finiteSupport _)]
    congr 1
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [integral_const_mul]
    congr 1
    exact integral_congr_ae
      (Filter.Eventually.of_forall (fun n => (windowExpSum_norm_eq_dft n ξ).symm))
  -- (★): assemble the chain.
  have hstar : c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) - shellError R H t g κ
      ≤ C * ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2 + door) :=
    le_trans hoc (le_trans hB (le_of_eq hRHSeq))
  -- derive the door's mass lower bound `c₀·ε ≤ door`.
  have hmul : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
      ≤ C * ((H : ℝ) / Real.log (H : ℝ)) * door := by
    have hexp : C * ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2 + door)
        = C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + C * ((H : ℝ) / Real.log (H : ℝ)) * door := by ring
    linarith [hstar, hbudget1, hexp]
  have hlower : c₀ * (R.eps : ℝ) ≤ door := le_of_mul_le_mul_left hmul hApos
  -- fire the Ξ_H-restricted MRT theorem-door (explicit `0 ≤ δ`).
  exact contradiction_of_mrtDoorXi R hlo hhi hHpos hδ hdoor hXi hbudget2 hlower

/-- **W3-E-GLUE, the L² (Ξ-SUMMED) Theorem-2.3 conditional shell** (⟦THE L² RESTRUCTURE⟧
stone 2).

Identical content to `log_chowla_two_shell_xi`, with Bridge A SQUARED and Bridge B verbatim:
the circle-method input `hcirc` is now the squared socket (discharger:
`circle_method_estimate_sq`, `CircleMethod.lean` — same constant `C = 1 + 2C₀`, so
`hbudget1` is UNCHANGED), and the door-facing conclusion is the Ξ-SUMMED L² mass

`c₀·ε ≤ Σ_{ξ∈Ξ_H} (1/H²)·∫‖windowExpSum H · (−ξ.val/H)‖² dμ`.

**The shed.**  `hXi : |Ξ_H| ≤ K` and the parameter `K` are GONE: the Ξ-summed door
pays its total mass ONCE rather than once per frequency, so the closure budget is
`ρ < c₀·ε` with `ρ` K-free (the freeze's `δ/2`-genre glue).  Everything else rides
unchanged — `outer_combine`, the `shellError` terms (they sit outside the ξ-sum), the
Bridge B integral exchange (`abs_integral_le_integral_abs`, `integral_finsetSum`,
`integrable_of_finiteSupport`).

**THE FUSE.**  `hdoor` is the Ξ-summed L² door predicate `MRTUniformityXiL2 R ρ`
(`MRTDoor.lean`), and the closer is its seam `contradiction_of_mrtDoorXiL2`; the mass
lower bound this shell derives is that seam's `hlower` slot verbatim.  The seam warning
on `MRTUniformityXi` carries over — THE `∀ H` / `Ξ_H` QUANTIFIERS STAY OUTSIDE THE
INTEGRAL (the predicate is a finite sum of integrals, no `sup` inside; a sup-inside form
would be Tao (4.1), OPEN).

Additive — `log_chowla_two_shell` and `log_chowla_two_shell_xi` are untouched. -/
theorem log_chowla_two_shell_xi_sq
    (R : ChowlaRegime) {H : ℕ} [NeZero H] (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    (hH : 3 ≤ H) (hlog : 1 ≤ Real.log (H : ℝ)) (hne : (primeWindow R.eps H).Nonempty)
    (hreg : Real.sqrt (H : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) / 2)
    (hhead : 8 * (PH R.eps H : ℝ) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ))
    {t : ℝ} (ht : 0 < t) {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
        / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    {κ : ℝ} (hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω] ≤ κ)
    {c₁ : ℝ} (hc₁ : 0 < c₁)
    (h211 : c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ n, fBridgeF R.eps H (liouvilleWindow H n) (residueWindow R.eps H n)
            ∂(logMeasure R.x R.ω)|)
    -- the SQUARED circle-method Fourier bound (discharger: `circle_method_estimate_sq`):
    {C : ℝ} (hC : 0 < C)
    (hcirc : ∀ n : ℕ,
      |∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2)
                * ‖ZMod.dft (fun j : ZMod H =>
                    (windowVal H (liouvilleWindow H n) (ZMod.val j) : ℂ)) ξ‖ ^ 2))
    -- the Ξ-SUMMED L² MRT door (`MRTDoor.lean`); NO `K`, NO `|Ξ_H| ≤ K` hypothesis:
    {ρ c₀ : ℝ} (hdoor : MRTUniformityXiL2 R ρ)
    -- the two numeric-closure budgets (`hbudget1` UNCHANGED; `hbudget2` is K-FREE):
    (hbudget1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
          + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + shellError R H t g κ
        ≤ c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)))
    (hbudget2 : ρ < c₀ * (R.eps : ℝ)) :
    False := by
  classical
  haveI hpm : IsProbabilityMeasure (logMeasure R.x R.ω) :=
    isProbabilityMeasure_logMeasure R.hx R.hω
  have hHpos : 0 < H := NeZero.pos H
  have hlogpos : 0 < Real.log (H : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hApos : 0 < C * ((H : ℝ) / Real.log (H : ℝ)) :=
    mul_pos hC (div_pos (by exact_mod_cast hHpos) hlogpos)
  have heps1R : (R.eps : ℝ) ≤ 1 := by
    have h : R.eps ≤ 1 := le_trans R.heps1 (by norm_num)
    exact_mod_cast h
  -- (I) the `outer_combine` mass lower bound (with `shellError` folded, defeq).
  have hoc : c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) - shellError R H t g κ
      ≤ |∫ n, (∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ))
          ∂(logMeasure R.x R.ω)| :=
    outer_combine R.eps H R.hx R.hω R.hωx R.heps heps1R hne hreg hH hlog hhead
      ht hg hgle hI hc₁ h211
  -- abbreviations
  set gm : ℕ → ℝ := fun n => ∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
      (windowVal H (liouvilleWindow H n) j : ℝ)
        * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) with hgm
  set door : ℝ := ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2)
      * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure R.x R.ω) with hdoorS
  set RHS : ℕ → ℝ := fun n => C * ((H : ℝ) / Real.log (H : ℝ))
      * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2)
          * ‖ZMod.dft (fun j : ZMod H =>
              (windowVal H (liouvilleWindow H n) (ZMod.val j) : ℂ)) ξ‖ ^ 2) with hRHS
  have hcirc' : ∀ n, |gm n| ≤ RHS n := hcirc
  -- Bridge B, step 1+2: `|∫ gm| ≤ ∫ RHS`.
  have hB : |∫ n, gm n ∂(logMeasure R.x R.ω)| ≤ ∫ n, RHS n ∂(logMeasure R.x R.ω) :=
    le_trans abs_integral_le_integral_abs
      (integral_mono_ae (integrable_of_finiteSupport _) (integrable_of_finiteSupport _)
        (Filter.Eventually.of_forall hcirc'))
  -- Bridge B, step 3: `∫ RHS = C·(H/log H)·(ε² + door)` (Bridge A SQUARED, per `ξ`).
  have hRHSeq : ∫ n, RHS n ∂(logMeasure R.x R.ω)
      = C * ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2 + door) := by
    rw [hRHS, integral_const_mul]
    congr 1
    rw [integral_add (integrable_const _) (integrable_of_finiteSupport _), integral_const,
      probReal_univ, one_smul,
      integral_finsetSum (bigXi R.eps H) (fun ξ _ => integrable_of_finiteSupport _)]
    congr 1
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [integral_const_mul]
    congr 1
    exact integral_congr_ae
      (Filter.Eventually.of_forall (fun n =>
        congrArg (fun z : ℝ => z ^ 2) (windowExpSum_norm_eq_dft n ξ).symm))
  -- (★): assemble the chain.
  have hstar : c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) - shellError R H t g κ
      ≤ C * ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2 + door) :=
    le_trans hoc (le_trans hB (le_of_eq hRHSeq))
  -- derive the door's L² mass lower bound `c₀·ε ≤ door`.
  have hmul : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
      ≤ C * ((H : ℝ) / Real.log (H : ℝ)) * door := by
    have hexp : C * ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2 + door)
        = C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + C * ((H : ℝ) / Real.log (H : ℝ)) * door := by ring
    linarith [hstar, hbudget1, hexp]
  have hlower : c₀ * (R.eps : ℝ) ≤ door := le_of_mul_le_mul_left hmul hApos
  -- fire the Ξ-SUMMED L² MRT theorem-door (K-FREE: one collision, no `card·δ` factor).
  exact contradiction_of_mrtDoorXiL2 R hlo hhi hdoor hbudget2 hlower

end Salt.Entropy.Chowla
