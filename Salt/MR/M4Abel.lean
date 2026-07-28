/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MinorArcCore
import Salt.MR.BigXiArc
import Salt.Vk.Shift

/-!
# M4-0′ — the MRT (4.2) integration by parts: the drift kill

The §4 major-arc port opens with a phase `e(θm)` of *very small* frequency:
after the window rewrite of M4-0 the residual frequency obeys
`|θ| ≤ arcDen B₅ H / (q·H)` — the tight major-arc radius divided by the
denominator.  Matomäki–Radziwiłł–Tao's (4.2) removes that phase by partial
summation: it is a weight of modulus `1` whose *increments* are `O(|θ|)`, so
Abel summation against the partial sums `S(K) = ∑_{M < m ≤ K} A(m)` costs a
main term `‖S(N)‖` plus a **drift** term proportional to `|θ|` times the
accumulated mass of the partial sums.  Over a window of length `≤ H` the drift
factor is `2π|θ|·H ≤ 2π·arcDen/q` — the `(W/(Hq))·∫₀^{H/d} dH′` factor of the
freeze row, in its discrete (Riemann-sum) skeleton.

## What is here

* **The complex-weight Abel identity** (`sum_Ioc_abel_complex`).
  `MinorArcCore.sum_Ioc_abel` is the same identity for a **real** weight
  `w : ℕ → ℝ` (coerced into `ℂ`).  A phase weight is genuinely complex, so the
  identity is re-proved verbatim at `w : ℕ → ℂ`; the induction is the landed
  one with the `push_cast` step deleted (there is no cast left to push).
  The landed *bounds* built on it (`norm_sum_Ioc_weighted_le`,
  `MinorArcExit.norm_sum_Ioc_weighted_le_antitone`) require `Monotone`/antitone
  weights and do **not** transfer — nothing below cites them.

* **The raw IBP inequality** (`norm_sum_Ioc_abel_le`).  The triangle inequality
  applied to the identity, with no hypotheses at all:
  `‖∑ w·A‖ ≤ ‖w(N)‖·‖S(N)‖ + ∑_{M ≤ i < N} ‖w(i+1) − w(i)‖·‖S(i)‖`.
  Everything else in the file is a specialisation of this one line.

* **The uniform drift bound** (`norm_sum_Ioc_weighted_le_drift`).  A weight
  capped by `Wt` at the right endpoint with increments capped by `D`, against a
  uniform partial-sum bound `B`, costs `(Wt + D·(N−M))·B`.  This is the complex
  analogue of `norm_sum_Ioc_weighted_le`'s `2W·B` — and note that it is *not*
  implied by it: a phase weight has no monotonicity to trade on, and the honest
  currency is the increment size, not the total variation of a monotone ramp.

* **The phase step** (`norm_eR_succ_sub`).  `‖e(θ(i+1)) − e(θi)‖ ≤ 2π|θ|`,
  straight off the landed `Salt.Vk.eR_lipschitz` (the character is
  `2π`-Lipschitz; `eR x = exp(2πix)`, so the `2π` lives *inside* `eR` and the
  Lipschitz constant is `2π`, not `1`).

* **The drift kill**, three shapes:
  - `norm_phase_sum_Ioc_ibp` — the sharpest, hypothesis-free form:
    `‖∑ e(θm)A(m)‖ ≤ ‖S(N)‖ + 2π|θ|·∑_{M ≤ i < N} ‖S(i)‖`.  The trailing sum is
    the discrete `∫₀^{H′} dH′` of the freeze row; the integral-form consumer
    reads it as a Riemann sum.
  - `norm_phase_sum_Ioc_drift` — the uniform form
    `≤ (1 + 2π|θ|·(N−M))·B` against any uniform partial-sum bound `B`.
  - `norm_phase_sum_Ioc_drift_sup` — the same with `B` taken to be the *actual*
    supremum `sup_{M ≤ K ≤ N} ‖S(K)‖`, so the statement carries no hypothesis
    beyond `M ≤ N`.

* **The arcDen instantiation** (`norm_phase_sum_arcDen_drift`,
  `norm_phase_sum_arcDen_drift_sup`).  At `|θ| ≤ arcDen B₅ H / (q·H)` over a
  window of length `≤ H`, the drift factor collapses to `1 + 2π·arcDen B₅ H/q`
  — a constant in `H`, which is the whole point of (4.2): the phase is gone and
  the price is `q`-graded, not `H`-graded.
-/

namespace Salt.MR

open Salt.ExpSum

/-! ## The complex-weight Abel identity

`MinorArcCore.sum_Ico_telescope` is `private`, so the telescope is re-proved
here (four lines) rather than cited. -/

/-- Telescoping over `Ico`, at a complex-valued weight. -/
private theorem sum_Ico_telescope_c (w : ℕ → ℂ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ i ∈ Finset.Ico M N, (w (i + 1) - w i) = w N - w M := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hN ih => rw [Finset.sum_Ico_succ_top hN, ih]; ring

/-- **Abel summation on `Ioc`, complex weight.**  With `S K = ∑_{M < m ≤ K} A m`,
`∑_{M < m ≤ N} w(m) A(m) = w(N) S(N) − ∑_{M ≤ i < N} (w(i+1) − w(i)) S(i)`.

This is `MinorArcCore.sum_Ioc_abel` with `w : ℕ → ℝ` replaced by `w : ℕ → ℂ`;
the induction is identical (the landed proof's closing `push_cast` is vacuous
here and is dropped). -/
theorem sum_Ioc_abel_complex (M : ℕ) (w : ℕ → ℂ) (A : ℕ → ℂ) {N : ℕ} (hMN : M ≤ N) :
    ∑ m ∈ Finset.Ioc M N, w m * A m
      = w N * (∑ m ∈ Finset.Ioc M N, A m)
        - ∑ i ∈ Finset.Ico M N, (w (i + 1) - w i) * (∑ m ∈ Finset.Ioc M i, A m) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ioc_succ_top hN (fun m => w m * A m),
        Finset.sum_Ico_succ_top hN
          (fun i => (w (i + 1) - w i) * (∑ m ∈ Finset.Ioc M i, A m)),
        Finset.sum_Ioc_succ_top hN A, ih]
      ring

/-- The telescope is not consumed by the bounds below (a phase weight has no
total-variation structure to exploit), but it is the identity's sanity check:
a *constant* weight collapses `sum_Ioc_abel_complex` to `w · S(N)`. -/
theorem sum_Ioc_abel_complex_const (M : ℕ) (c : ℂ) (A : ℕ → ℂ) {N : ℕ} (hMN : M ≤ N) :
    ∑ m ∈ Finset.Ioc M N, c * A m = c * ∑ m ∈ Finset.Ioc M N, A m := by
  have h := sum_Ioc_abel_complex M (fun _ => c) A hMN
  simpa using h

/-! ## The raw integration-by-parts inequality

One triangle inequality on the identity.  No hypothesis on `w` — the whole
content of the drift kill is that a *phase* weight makes the two factors on the
right small: `‖w(N)‖ = 1` and `‖w(i+1) − w(i)‖ ≤ 2π|θ|`. -/

/-- **The IBP inequality.**  `‖∑_{M < m ≤ N} w(m)A(m)‖` is at most
`‖w(N)‖·‖S(N)‖` plus the accumulated drift `∑_{M ≤ i < N} ‖w(i+1) − w(i)‖·‖S(i)‖`. -/
theorem norm_sum_Ioc_abel_le (M : ℕ) (w A : ℕ → ℂ) {N : ℕ} (hMN : M ≤ N) :
    ‖∑ m ∈ Finset.Ioc M N, w m * A m‖
      ≤ ‖w N‖ * ‖∑ m ∈ Finset.Ioc M N, A m‖
        + ∑ i ∈ Finset.Ico M N, ‖w (i + 1) - w i‖ * ‖∑ m ∈ Finset.Ioc M i, A m‖ := by
  rw [sum_Ioc_abel_complex M w A hMN]
  refine le_trans (norm_sub_le _ _) (add_le_add (le_of_eq (norm_mul _ _)) ?_)
  refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun i _ => norm_mul _ _)

/-- **The uniform drift bound.**  A complex weight of size `≤ Wt` at the right
endpoint whose increments are `≤ D` across the window, tested against a uniform
partial-sum bound `B`, costs the factor `Wt + D·(N − M)`.

The complex companion of `MinorArcCore.norm_sum_Ioc_weighted_le` (`2W·B`, for a
*monotone* real weight): there the currency is the total variation of a ramp,
here it is the per-step drift.  Neither implies the other. -/
theorem norm_sum_Ioc_weighted_le_drift {M N : ℕ} (hMN : M ≤ N) {w A : ℕ → ℂ}
    {B D Wt : ℝ} (hwN : ‖w N‖ ≤ Wt)
    (hdrift : ∀ i, M ≤ i → i < N → ‖w (i + 1) - w i‖ ≤ D)
    (hpart : ∀ K, M ≤ K → K ≤ N → ‖∑ m ∈ Finset.Ioc M K, A m‖ ≤ B) :
    ‖∑ m ∈ Finset.Ioc M N, w m * A m‖ ≤ (Wt + D * ((N - M : ℕ) : ℝ)) * B := by
  refine le_trans (norm_sum_Ioc_abel_le M w A hMN) ?_
  have hWt0 : (0 : ℝ) ≤ Wt := le_trans (norm_nonneg _) hwN
  have h1 : ‖w N‖ * ‖∑ m ∈ Finset.Ioc M N, A m‖ ≤ Wt * B :=
    mul_le_mul hwN (hpart N hMN le_rfl) (norm_nonneg _) hWt0
  have h2 : ∑ i ∈ Finset.Ico M N, ‖w (i + 1) - w i‖ * ‖∑ m ∈ Finset.Ioc M i, A m‖
      ≤ D * ((N - M : ℕ) : ℝ) * B := by
    calc ∑ i ∈ Finset.Ico M N, ‖w (i + 1) - w i‖ * ‖∑ m ∈ Finset.Ioc M i, A m‖
        ≤ ∑ _i ∈ Finset.Ico M N, D * B := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          simp only [Finset.mem_Ico] at hi
          have hDi := hdrift i hi.1 hi.2
          exact mul_le_mul hDi (hpart i hi.1 (le_of_lt hi.2)) (norm_nonneg _)
            (le_trans (norm_nonneg _) hDi)
      _ = D * ((N - M : ℕ) : ℝ) * B := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]; ring
  have hsplit : Wt * B + D * ((N - M : ℕ) : ℝ) * B = (Wt + D * ((N - M : ℕ) : ℝ)) * B := by
    ring
  linarith

/-! ## The phase step

`eR x = exp(2πix)` (`Salt/ExpSum/Basic.lean`), so the `2π` is *inside* the
character and the Lipschitz constant is `2π`.  `Salt.Vk.eR_lipschitz` is the
landed mean-value inequality `‖eR x − eR y‖ ≤ 2π|x − y|`. -/

/-- **The drift of a phase weight.**  Consecutive values of `m ↦ e(θm)` differ by
at most `2π|θ|` — one step of the phase, no more. -/
theorem norm_eR_succ_sub (θ : ℝ) (i : ℕ) :
    ‖eR (θ * ((i + 1 : ℕ) : ℝ)) - eR (θ * (i : ℝ))‖ ≤ 2 * Real.pi * |θ| := by
  have h := Salt.Vk.eR_lipschitz (θ * ((i + 1 : ℕ) : ℝ)) (θ * (i : ℝ))
  have hd : θ * ((i + 1 : ℕ) : ℝ) - θ * (i : ℝ) = θ := by push_cast; ring
  rwa [hd] at h

/-! ## The drift kill

Three shapes of MRT (4.2).  The first is sharpest and hypothesis-free; the
second and third trade the accumulated sum for a uniform bound, which is what
the §4 consumer wants. -/

/-- **MRT (4.2), sharp form.**  Partial summation removes the phase `e(θm)` at
the cost of the main term `‖S(N)‖` and a drift term `2π|θ|` times the
*accumulated* partial-sum mass.

The trailing sum `∑_{M ≤ i < N} ‖S(i)‖` is the discrete `∫₀^{H′}·dH′` of the
freeze row: a consumer that wants the integral form reads it as a Riemann sum
over the window, and the prefactor `2π|θ| ≤ 2π·W/(Hq)` supplies the `W/(Hq)`. -/
theorem norm_phase_sum_Ioc_ibp {M N : ℕ} (hMN : M ≤ N) (θ : ℝ) (A : ℕ → ℂ) :
    ‖∑ m ∈ Finset.Ioc M N, eR (θ * (m : ℝ)) * A m‖
      ≤ ‖∑ m ∈ Finset.Ioc M N, A m‖
        + 2 * Real.pi * |θ| * ∑ i ∈ Finset.Ico M N, ‖∑ m ∈ Finset.Ioc M i, A m‖ := by
  refine le_trans (norm_sum_Ioc_abel_le M (fun m : ℕ => eR (θ * (m : ℝ))) A hMN) ?_
  simp only [norm_eR, one_mul]
  refine add_le_add le_rfl ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact mul_le_mul_of_nonneg_right (norm_eR_succ_sub θ i) (norm_nonneg _)

/-- **MRT (4.2), uniform form — THE DRIFT KILL.**  Against any uniform bound `B`
on the partial sums `S(K) = ∑_{M < m ≤ K} A(m)`, the phase `e(θm)` costs exactly
the factor `1 + 2π|θ|·(N − M)`: the `1` is the trivial (phase-free) bound, and
`2π|θ|·(N − M)` is the drift accumulated across the window. -/
theorem norm_phase_sum_Ioc_drift {M N : ℕ} (hMN : M ≤ N) (θ : ℝ) {A : ℕ → ℂ} {B : ℝ}
    (hpart : ∀ K, M ≤ K → K ≤ N → ‖∑ m ∈ Finset.Ioc M K, A m‖ ≤ B) :
    ‖∑ m ∈ Finset.Ioc M N, eR (θ * (m : ℝ)) * A m‖
      ≤ (1 + 2 * Real.pi * |θ| * ((N - M : ℕ) : ℝ)) * B :=
  norm_sum_Ioc_weighted_le_drift (M := M) (N := N) hMN
    (w := fun m : ℕ => eR (θ * (m : ℝ))) (A := A) (B := B) (D := 2 * Real.pi * |θ|)
    (Wt := 1) (by simp) (fun i _ _ => norm_eR_succ_sub θ i) hpart

/-- **MRT (4.2), sup form.**  The uniform form with `B` instantiated at the
actual supremum of the partial sums over the window — so the statement carries
no hypothesis beyond `M ≤ N`.  This is the shape the §4 consumer reads:
`‖∑_{M < m ≤ N} e(θm)a(m)‖ ≤ (1 + 2π|θ|(N−M))·sup_{M ≤ K ≤ N} ‖S(K)‖`. -/
theorem norm_phase_sum_Ioc_drift_sup {M N : ℕ} (hMN : M ≤ N) (θ : ℝ) (A : ℕ → ℂ) :
    ‖∑ m ∈ Finset.Ioc M N, eR (θ * (m : ℝ)) * A m‖
      ≤ (1 + 2 * Real.pi * |θ| * ((N - M : ℕ) : ℝ))
          * (Finset.Icc M N).sup' ⟨M, Finset.mem_Icc.mpr ⟨le_rfl, hMN⟩⟩
              (fun K => ‖∑ m ∈ Finset.Ioc M K, A m‖) := by
  have hne : (Finset.Icc M N).Nonempty := ⟨M, Finset.mem_Icc.mpr ⟨le_rfl, hMN⟩⟩
  have hpart : ∀ K, M ≤ K → K ≤ N →
      ‖∑ m ∈ Finset.Ioc M K, A m‖
        ≤ (Finset.Icc M N).sup' hne (fun K => ‖∑ m ∈ Finset.Ioc M K, A m‖) := by
    intro K h1 h2
    exact Finset.le_sup' (f := fun K => ‖∑ m ∈ Finset.Ioc M K, A m‖)
      (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  exact norm_phase_sum_Ioc_drift hMN θ hpart

/-! ## The arcDen instantiation

`arcDen B₅ H = (log H)^{B₅}` is `Salt/MR/BigXiArc.lean`'s denominator cap; the
tight major-arc radius delivered by M4-0 is `arcDen B₅ H / (q·H)`.  Over a
window of length `≤ H` the drift factor is then bounded **independently of `H`**:
`2π|θ|·(N − M) ≤ 2π·arcDen B₅ H / q`. -/

/-- The drift factor at the tight major-arc radius: `|θ| ≤ arcDen/(q·H)` and a
window of length `≤ H` give `|θ|·(N − M) ≤ arcDen/q`. -/
theorem abs_mul_window_le_of_arcDen {B₅ : ℝ} {H q M N : ℕ} (hq : 0 < q) (hH : 0 < H)
    (hlen : N - M ≤ H) {θ : ℝ} (hθ : |θ| ≤ arcDen B₅ H / ((q : ℝ) * (H : ℝ))) :
    |θ| * ((N - M : ℕ) : ℝ) ≤ arcDen B₅ H / (q : ℝ) := by
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlenR : ((N - M : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlen
  have h1 : |θ| * ((N - M : ℕ) : ℝ) ≤ |θ| * (H : ℝ) :=
    mul_le_mul_of_nonneg_left hlenR (abs_nonneg θ)
  have h2 : |θ| * (H : ℝ) ≤ arcDen B₅ H / ((q : ℝ) * (H : ℝ)) * (H : ℝ) :=
    mul_le_mul_of_nonneg_right hθ hHR.le
  have h3 : arcDen B₅ H / ((q : ℝ) * (H : ℝ)) * (H : ℝ) = arcDen B₅ H / (q : ℝ) := by
    field_simp
  linarith

/-- **THE M4-0′ PAYLOAD.**  At the tight major-arc radius `|θ| ≤ arcDen/(q·H)`,
over a window of length `≤ H`, the phase `e(θm)` is removed at the `H`-free
price `1 + 2π·arcDen B₅ H / q`.

This is the freeze row's `(W/(Hq))·∫₀^{H/d} dH′` factor: `W/(Hq)` is the radius,
the window length `≤ H` is the integration range, and their product is the
`q`-graded constant above. -/
theorem norm_phase_sum_arcDen_drift {B₅ : ℝ} {H q M N : ℕ} (hMN : M ≤ N) (hq : 0 < q)
    (hH : 0 < H) (hlen : N - M ≤ H) {θ : ℝ}
    (hθ : |θ| ≤ arcDen B₅ H / ((q : ℝ) * (H : ℝ))) {A : ℕ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hpart : ∀ K, M ≤ K → K ≤ N → ‖∑ m ∈ Finset.Ioc M K, A m‖ ≤ B) :
    ‖∑ m ∈ Finset.Ioc M N, eR (θ * (m : ℝ)) * A m‖
      ≤ (1 + 2 * Real.pi * (arcDen B₅ H / (q : ℝ))) * B := by
  refine le_trans (norm_phase_sum_Ioc_drift hMN θ hpart) ?_
  refine mul_le_mul_of_nonneg_right ?_ hB
  have hstep := abs_mul_window_le_of_arcDen (B₅ := B₅) hq hH hlen hθ
  have heq : 2 * Real.pi * |θ| * ((N - M : ℕ) : ℝ)
      = 2 * Real.pi * (|θ| * ((N - M : ℕ) : ℝ)) := by ring
  rw [heq]
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  linarith [mul_le_mul_of_nonneg_left hstep hpi]

/-- The payload in sup form: no hypothesis on the coefficients `A` at all. -/
theorem norm_phase_sum_arcDen_drift_sup {B₅ : ℝ} {H q M N : ℕ} (hMN : M ≤ N) (hq : 0 < q)
    (hH : 0 < H) (hlen : N - M ≤ H) {θ : ℝ}
    (hθ : |θ| ≤ arcDen B₅ H / ((q : ℝ) * (H : ℝ))) (A : ℕ → ℂ) :
    ‖∑ m ∈ Finset.Ioc M N, eR (θ * (m : ℝ)) * A m‖
      ≤ (1 + 2 * Real.pi * (arcDen B₅ H / (q : ℝ)))
          * (Finset.Icc M N).sup' ⟨M, Finset.mem_Icc.mpr ⟨le_rfl, hMN⟩⟩
              (fun K => ‖∑ m ∈ Finset.Ioc M K, A m‖) := by
  have hne : (Finset.Icc M N).Nonempty := ⟨M, Finset.mem_Icc.mpr ⟨le_rfl, hMN⟩⟩
  have hpart : ∀ K, M ≤ K → K ≤ N →
      ‖∑ m ∈ Finset.Ioc M K, A m‖
        ≤ (Finset.Icc M N).sup' hne (fun K => ‖∑ m ∈ Finset.Ioc M K, A m‖) := by
    intro K h1 h2
    exact Finset.le_sup' (f := fun K => ‖∑ m ∈ Finset.Ioc M K, A m‖)
      (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hB : (0 : ℝ) ≤ (Finset.Icc M N).sup' hne (fun K => ‖∑ m ∈ Finset.Ioc M K, A m‖) := by
    have h := hpart M le_rfl hMN
    simpa using h
  exact norm_phase_sum_arcDen_drift hMN hq hH hlen hθ hB hpart

end Salt.MR
