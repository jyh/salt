/-
Copyright (c) 2026 Salt contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Salt.MR.ZetaPowLower
import Salt.MR.LargeValues

/-!
# L11 — Halász inequality for primes (θ = 3/4)   `halasz_primes_pow`

Node **L11** of the S8 / MR-CORE campaign (P-lane, deepest stone).  Ports
Matomäki–Radziwiłł **Lemma 11** (`docs/sources/mr_extract.md` §2.3, p.17–18),
under the **θ = 3/4** override frozen in `docs/exploration/s8-freeze.md [P3]/L11`
(MR's original is θ = 2/3 + ε; our zero-free region is the VK θ = 3/4 one, so the
in-statement exponent is `3/4` and the polylog carries the `(loglog)⁴` correction).

## The frozen shape (BINDING — iron rule 1)

For a prime-supported polynomial `P(s) = Σ_{P ≤ p ≤ 2P} a_p · p^{−s}` with
`|a_p| ≤ 1`, and a well-spaced set `𝒯 ⊆ [−T, T]`:

  `Σ_{t ∈ 𝒯} |P(it)|² ≪`
      `(P + |𝒯|·P·exp(−log P / ((log T)^{3/4}·(loglog T)⁴))·(log T)²)·Σ|a_p|² / log P`.

The contour sits at `σ = 1 − c / ((log T)^{3/4}·(loglog T)⁴)`; the `exp(−log P·(1−σ))`
decay is exactly `p^{−(1−σ)}` at the contour depth.  The `−loglog` powers are
in-statement.

## The Zeno ladder (the source's own proof structure)

* **R1** — per-`t` prime-sum → contour representation.  Gateway (Lemma 10, L²-duality)
  is `primes_dual_iff` below (a specialization of the landed `l2_duality`): it turns the
  target into a bound on the pairwise prime sum `Σ_{P≤p≤2P} p^{i(t−t′)}` (diagonal
  `t = t′` gives `≈ P/log P`; off-diagonal gives the `exp`-decay).  The remaining
  *core* — the Perron/Mellin representation of that pairwise sum and its contour shift
  — is the RESISTANCE (see the map at the foot of this file).
* **R2** — the contour shift priced by the ζ′/ζ region bound.  `zeta_near_strip_growth`
  below: across the near strip `[1, 1+w]`, `w = cR/((log|t|)^{3/4}(loglog|t|)⁴)`,
  `log‖ζ‖` grows by at most the ABSOLUTE constant `400` — the "ζ is tame near the
  1-line" statement underlying the contour price.  Rides `zeta_near_logDeriv_bound`
  (`ZetaPowLower.lean:781`) ∘ `zeta_near_bridge` (`:843`).
* **R3** — the per-`t` decay: `prime_contour_decay` / `_frozen` below, the frozen
  `p^{−(1−σ)} ≤ exp(−log P·(1−σ))` shape.
* **R4** — the well-spaced summation.  `primePoly_wellspaced_l2` below feeds the L7
  keystone `wellspaced_l2` (the trivial mean-value half of the assembly).

## Representation note (dpoly ↔ `p^{−it}`)

The corpus-native carrier is `dpoly N a t = Σ_{1≤n≤N} aₙ·exp(i·t·log n) = Σ aₙ·n^{it}`.
`P(it) = Σ a_p p^{−it} = conj(Σ conj(a_p) p^{it})`, so `‖P(it)‖ = ‖dpoly (2P) (conj∘ã) t‖`
and `Σ|a_p|²` is conjugation-invariant; the well-spaced sum is a `t ↦ −t` bijection.
Hence the R4 rung is stated in the `dpoly` carrier (faithful up to the harmless
conjugation/sign symmetry), while the R1 gateway is stated in the honest `p^{−it}` carrier.
-/

namespace Salt.MR

open scoped BigOperators
open Complex

/-- **Prime-supported coefficient sequence.**  `primeCoeff P a n = a n` when `n` is a
prime in `[P, 2P]`, else `0`.  The carrier of `P(s) = Σ_{P≤p≤2P} a_p p^{−s}`. -/
noncomputable def primeCoeff (P : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n.Prime ∧ P ≤ n ∧ n ≤ 2 * P then a n else 0

/-! ## R3 — the per-`t` contour decay (the frozen `exp` shape) -/

/-- **R3 (base).**  At a contour of depth `δ ≥ 0`, a prime `p ≥ P ≥ 2` decays at least as
fast as the left endpoint: `p^{−δ} ≤ exp(−(δ·log P))`.  (`p^{−δ} = exp(−δ·log p)` and
`log p ≥ log P > 0`.) -/
lemma prime_contour_decay {P p : ℕ} {δ : ℝ} (hP : 2 ≤ P) (hp : P ≤ p) (hδ : 0 ≤ δ) :
    (p : ℝ) ^ (-δ) ≤ Real.exp (-(δ * Real.log P)) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hP
  have hPp : (P : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le hP0 hPp
  have hlog : Real.log P ≤ Real.log p := Real.log_le_log hP0 hPp
  have hrw : (p : ℝ) ^ (-δ) = Real.exp (Real.log p * (-δ)) := Real.rpow_def_of_pos hp0 _
  rw [hrw]
  apply Real.exp_le_exp.mpr
  nlinarith [hlog, hδ]

/-- **R3 (frozen).**  The in-statement `exp(−log P / ((log T)^{3/4}(loglog T)⁴))` decay:
substituting `δ = c / ((log T)^{3/4}(loglog T)⁴)` into `prime_contour_decay` exhibits the
frozen contour depth `(1−σ)`. -/
lemma prime_contour_decay_frozen {P p : ℕ} {c Tval : ℝ} (hP : 2 ≤ P) (hp : P ≤ p)
    (hc : 0 ≤ c)
    (hden : 0 < (Real.log Tval) ^ ((3 : ℝ) / 4) * (Real.log (Real.log Tval)) ^ (4 : ℕ)) :
    (p : ℝ) ^ (-(c / ((Real.log Tval) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log Tval)) ^ (4 : ℕ))))
      ≤ Real.exp (-(Real.log P * c / ((Real.log Tval) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log Tval)) ^ (4 : ℕ)))) := by
  set D : ℝ := (Real.log Tval) ^ ((3 : ℝ) / 4) * (Real.log (Real.log Tval)) ^ (4 : ℕ) with hD
  have hδ : 0 ≤ c / D := div_nonneg hc (le_of_lt hden)
  have hbase := prime_contour_decay (δ := c / D) hP hp hδ
  have hEq : Real.log P * c / D = (c / D) * Real.log P := by ring
  rw [hEq]; exact hbase

/-! ## R4 — the well-spaced summation (trivial mean-value half) -/

/-- **R4 (trivial half).**  Feeding the prime-supported carrier `dpoly (2P) (primeCoeff P a)`
into the L7 keystone `wellspaced_l2` gives the trivial mean-value bound
`Σ_{t∈𝒯} ‖P‖² ≤ 84·(T+2P)·log(4P)·Σ ‖a_p‖²`.  The Halász prime-window GAIN — the `exp`-decay
replacing the linear `T` — is the RESISTANCE; this rung supplies only the summation machinery
(R1–R3 supply the gain). -/
theorem primePoly_wellspaced_l2 (P : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) :
    ∑ t ∈ 𝒯, ‖dpoly (2 * P) (primeCoeff P a) t‖ ^ 2
      ≤ 84 * (T + ((2 * P : ℕ) : ℝ)) * Real.log (2 * ((2 * P : ℕ) : ℝ))
          * ∑ n ∈ Finset.Icc 1 (2 * P), ‖primeCoeff P a n‖ ^ 2 :=
  wellspaced_l2 (2 * P) (primeCoeff P a) T hT 𝒯 hws hsub

/-! ## R2 — the contour price (ζ is tame near the 1-line) -/

/-- **R2.**  Across the near strip `[1, 1+w]`, `w = cR / ((log|t|)^{3/4}(loglog|t|)⁴)`,
`log‖ζ‖` grows by at most the ABSOLUTE constant `400`.  Rides the hypothesis-free region
bound `zeta_near_logDeriv_bound` (`‖ζ′/ζ‖ ≤ 400·L^{3/4}ℓ⁴/cR` on the strip) through the FTC
bridge `zeta_near_bridge`; the `L^{3/4}ℓ⁴` cancels against the strip width `w`, leaving the
price `w·Bnd = 400`.  This is the "ζ is tame near the 1-line" statement underlying the
contour shift (R1-core). -/
lemma zeta_near_strip_growth :
    ∃ cR T₀ : ℝ, 0 < cR ∧ cR ≤ 1 ∧ 3 ≤ T₀ ∧
      ∀ t : ℝ, T₀ ≤ |t| →
        Real.log ‖riemannZeta (((1 + cR / (Real.log |t| ^ ((3 : ℝ) / 4)
                * Real.log (Real.log |t|) ^ (4 : ℕ))) : ℝ) + (t : ℂ) * I)‖
          - Real.log ‖riemannZeta ((1 : ℝ) + (t : ℂ) * I)‖ ≤ 400 := by
  obtain ⟨cR, T₀, hcR0, hcR1, hT₀3, hloglog, hbnd⟩ := zeta_near_logDeriv_bound
  refine ⟨cR, T₀, hcR0, hcR1, hT₀3, ?_⟩
  intro t ht
  have htabs : (3 : ℝ) ≤ |t| := le_trans hT₀3 ht
  have hll : (1 : ℝ) ≤ Real.log (Real.log |t|) := hloglog t ht
  have hLtpos : 0 < Real.log |t| := Real.log_pos (by linarith)
  set D : ℝ := Real.log |t| ^ ((3 : ℝ) / 4) * Real.log (Real.log |t|) ^ (4 : ℕ) with hD
  have hDpos : 0 < D := by
    rw [hD]; exact mul_pos (Real.rpow_pos_of_pos hLtpos _) (pow_pos (by linarith) 4)
  have hcRne : cR ≠ 0 := ne_of_gt hcR0
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hnear : ∀ v : ℝ, (1 : ℝ) ≤ v → v ≤ 1 + cR / D →
      ‖logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)‖ ≤ 400 * D / cR := by
    intro v hv1 hv2
    rw [hD] at hv2
    have hb := hbnd t v ht hv1 hv2
    rw [← hD] at hb
    exact hb
  have hbridge := zeta_near_bridge (a := 1) (b := 1 + cR / D)
    (by have : (0 : ℝ) ≤ cR / D := div_nonneg (le_of_lt hcR0) (le_of_lt hDpos); linarith)
    le_rfl htabs hnear
  have hval : (1 + cR / D - 1) * (400 * D / cR) = 400 := by field_simp; ring
  rw [hval] at hbridge
  exact hbridge

/-! ## R1 — the duality gateway (Lemma 10 specialization) -/

/-- **R1 (gateway).**  Specializing the landed L²-duality principle `l2_duality` (MR Lemma 10,
`MVHilbert.lean`) to the prime matrix `φ(t,p) = p^{−it}` turns the target operator bound into
its dual — a bound on `Σ_p ‖Σ_t p^{it} b_t‖²`, whose expansion is the pairwise prime sum
`Σ_p p^{i(t−t′)}` (diagonal `t=t′ → ≈ P/log P`; off-diagonal → the contour `exp`-decay of R2/R3).
The RESISTANCE is the Perron/Mellin representation of that pairwise sum. -/
lemma primes_dual_iff (𝒯 : Finset ℝ) (S : Finset ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    (∀ a : ℕ → ℂ, ∑ t ∈ 𝒯, ‖∑ p ∈ S, (p : ℂ) ^ (-(t : ℂ) * I) * a p‖ ^ 2
        ≤ Δ * ∑ p ∈ S, ‖a p‖ ^ 2) ↔
    (∀ b : ℝ → ℂ, ∑ p ∈ S, ‖∑ t ∈ 𝒯, (starRingEnd ℂ) ((p : ℂ) ^ (-(t : ℂ) * I)) * b t‖ ^ 2
        ≤ Δ * ∑ t ∈ 𝒯, ‖b t‖ ^ 2) :=
  l2_duality 𝒯 S (fun t p => (p : ℂ) ^ (-(t : ℂ) * I)) hΔ

/-!
## Resistance map (R1-core — the remaining blocker)

Landed tonight (all sorry-free): the four ladder sub-stones —
`primes_dual_iff` (R1 gateway), `zeta_near_strip_growth` (R2 price = 400),
`prime_contour_decay`/`_frozen` (R3), `primePoly_wellspaced_l2` (R4).

**R1-core (the blocker):** the Perron/Mellin representation of the pairwise prime sum
`g(u) := Σ_{P≤p≤2P} p^{iu}` and its contour shift.  Via `−ζ′/ζ = LSeries Λ`
(`Salt.SW.neg_logDeriv_LSeries_eq_LSeries_twist`) + truncated Perron
(`Salt.MR.perron_trunc`) one writes `Σ_{P≤p≤2P} Λ(n) n^{iu}` as a vertical integral of
`−ζ′/ζ(s+iu)·(kernel)`, then shifts the contour left to `σ = 1 − cR/((log T)^{3/4}(loglog T)⁴)`.
No zeros are crossed (VK zero-free region `zeta_zero_free_region_pow`,
`GrowthPow.lean:1044`), the shifted integrand is priced by the region bound (R2 machinery),
and the `p^{−(1−σ)}` factor supplies the R3 `exp`-decay.  Assembling
(diagonal `+` off-diagonal `+` prime↔prime-power passage `+` `√` from `L²`-duality) then
closes `halasz_primes_pow` in the frozen shape.

Estimated residual: a Fable-tier design block (the Perron representation of `g(u)` and the
left-shift certificate from `near_norm_logDeriv_Zc_le` — the wrapper `zeta_near_logDeriv_bound`
certifies only the RIGHT strip `[1,1+w]`; the left shift needs the disc-core with the
`hdist` min-distance-to-zeros hypothesis supplied by the pow region).  See NOTES in the
executor report.
-/

end Salt.MR
