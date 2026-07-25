/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PropA3Core

/-!
# GRADE-CLOSE ladder, rung B-2 — the compact-minimizer packaging (`CompactMin`)

**The sixth vacuity catch** (`docs/exploration/hsup-design.md`, the
⟦GRADE-SCOPE VERDICT + AMENDMENT V3⟧ block; `docs/blueprints/flags.md`).  A
hypothesis of the shape

  `hmin : ∀ v : ℝ, 𝔻(f, n^{it₁}; X)² ≤ 𝔻(f, n^{iv}; X)²`

— a *global* minimizer of the frequency map over all of `ℝ` — is VACUOUS in the
live band.  `𝔻(f, n^{iv}; X)²` is the FINITE sum `∑_{p≤X}(1 − Re f(p)n^{-iv})/p`;
for unimodular data Kronecker/Weyl density makes its `ℝ`-infimum `0`, which
contradicts any band floor `𝔻² ≥ c·loglog X`.  So `hmin`-on-`ℝ` plus a band floor
is an empty hypothesis set: kernel-valid, mathematically inert.

**The repair packaged here.**  The contour is TRUNCATED at height `T*`, so the
consumer only ever needs the minimizer over the compact `[−R, R]` (`R = X + T*`),
where **attainment is free** (extreme value theorem) and the `ℝ`-caveat recorded
at `RHSGrade.lean:61-63` is moot.  This file supplies:

* `pretDistSq_continuous_freq` (C1) — `v ↦ 𝔻(f, n^{iv}; X)²` is continuous (a
  finite sum over `p ≤ ⌊X⌋₊` of continuous terms).
* `exists_min_dist_on_Icc` (C2) — the honest, non-vacuous `hmin`: a minimizer on
  `Set.Icc (-R) R` for ANY `R ≥ 0`, with the minimality quantified over the
  compact only.
* `pretDistSq_freq_lipschitz` (C3a) — the frequency map is Lipschitz with
  constant `∑_{p≤X} log p / p ≤ log X + (log 4 + 4)` (`mertens_first_upper`),
  sharp constant `1` per term via `‖e^{iθ} − e^{iφ}‖ ≤ |θ − φ|`.
* `overhang_no_undercut` (C3) — the overhang floor, in its HONEST form.
* `compact_min_package` (C4) — the consumer-facing bundle.

## The C3 architecture as built: minimizer-localization, NOT overhang-comparison

The V3 sketch offered two routes for the overhang `|v| ∈ (X, X + T*]`:

1. *overhang-comparison* — prove `𝔻²(t₁) ≤ 𝔻²(v)` for overhang `v` from a floor
   at `v` plus the ball-live cap at `t₁`.  **Not taken.**  It is unnecessary AND
   its near-corner is unfixable: the recentered floor `dist_one_floor_pow` needs
   `|v − t₁| ≥ 1`, and when the minimizer sits at the very edge (`t₁ ∈ (X−1, X]`,
   `v` just above `X`) the only available substitute is C3a, whose drift over
   `|v − t₁| ≈ 1` is `log X`-sized — i.e. `loglog`-useless.
2. *minimizer-localization* — **taken.**  Run C2 at `R := X + T*` FROM THE START.
   Then `hmin` holds on the whole truncated range BY MINIMALITY and there is no
   overhang argument to make: the overhang is INSIDE the compact.

That leaves a genuine question, which `overhang_no_undercut` answers: how far can
the enlarged minimizer wander?  **Full localization `|t₁| ≤ X` is FALSE** — take
`f := n^{i(X + 1/log X)}`; its distance vanishes at `v = X + 1/log X > X` while
the cap at `t₀ = X` still holds (`∑_p (1 − cos(log p/log X))/p = O(1)`).  What IS
true is localization RELATIVE TO THE LIVE-BAND WITNESS: if `t₀ ∈ [−X, X]` carries
the ball-live cap `𝔻²(f, n^{it₀}; X)² ≤ S` and `v` is a *deep* overhang point
(`|v − t₀| ≥ 1`, `|v| ≤ 3X`), then the two-cap triangle
(`dist_one_shift_le_of_two_caps`) forces `𝔻(1, n^{i(v−t₀)}; X)² ≤ 4S`, which the
uncapped floor `dist_one_floor_pow` refutes as soon as

  `4S < loglog X − (3/4)·loglog(4X+3) − 5·logloglog(4X+16) − C`.

Hence `S < 𝔻²(f, n^{iv}; X)²`: the deep overhang CANNOT undercut the cap, and the
`[−R,R]`-minimizer satisfies `|t₁ − t₀| < 1`, so `|t₁| ≤ X + 1`.

**Numeral note (honest, and load-bearing for the consumer).**  The gap hypothesis
is STRICT and is NOT satisfied at the frozen S8 numerals `S = (1/16)·loglog X`:
there `4S = (1/4)·loglog X` sits exactly at the floor's leading term
`loglog X − (3/4)loglog(4X+3) ≈ (1/4)loglog X`.  Localization therefore needs a
cap strictly below `(1/16)·loglog X` (e.g. `S = (1/64)·loglog X` clears it for
large `X`).  This is carried as the named hypothesis `hgap`, never assumed.

## Posture

No statement anywhere else is touched; this file only ADDS.  Everything is stated
for arbitrary 1-bounded `f`, arbitrary compact radius `R`, and a named cap `S`;
the analytic input is exactly the two LANDED stones `dist_one_floor_pow`
(`DistHalasz.lean:179`) and `pretDist_triangle` (`PretentiousTriangle.lean:172`),
plus `mertens_first_upper` (`PrimeSigmaShift.lean:45`) for C3a.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## C1 — continuity of the frequency map -/

/-- The twist `v ↦ n^{iv} = e^{iv·log n}` is continuous in the frequency `v`
(for each fixed argument `n`). -/
lemma continuous_costwist_freq (n : ℕ) : Continuous fun v : ℝ => costwist v n := by
  unfold costwist
  refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
  exact Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)

/-- **C1 — the frequency map is continuous.**  `v ↦ 𝔻(f, n^{iv}; X)²` is continuous:
`pretDistSq` is a FINITE sum (over the primes `p ≤ ⌊X⌋₊`) of the terms
`(1 − Re(f(p)·conj(n^{iv})))/p`, each continuous in `v` by `continuous_costwist_freq`
composed with `Complex.continuous_conj` and `Complex.continuous_re`.

This is what makes the truncated `hmin` of `exists_min_dist_on_Icc` non-vacuous:
the extreme value theorem applies on every compact `[−R, R]`. -/
theorem pretDistSq_continuous_freq (f : ℕ → ℂ) (X : ℝ) :
    Continuous fun v : ℝ => pretDistSq f (costwist v) X := by
  unfold pretDistSq
  refine continuous_finsetSum _ (fun p _ => ?_)
  refine Continuous.div_const (continuous_const.sub ?_) _
  exact Complex.continuous_re.comp
    (continuous_const.mul (Complex.continuous_conj.comp (continuous_costwist_freq p)))

/-! ## C2 — attainment on a compact (the honest `hmin`) -/

/-- **C2 — the compact minimizer (the vacuity repair).**  For any radius `R ≥ 0`
there is `t₁ ∈ [−R, R]` minimizing `v ↦ 𝔻(f, n^{iv}; X)²` over `[−R, R]`.

Attainment is FREE here (`isCompact_Icc` + C1 + `IsCompact.exists_isMinOn`); the
`ℝ`-caveat of the global form — Kronecker density drives the `ℝ`-infimum of the
finite prime sum to `0`, making `hmin`-on-`ℝ` vacuous against any band floor — is
moot on the compact.  Run at `R := X + T*` (the contour truncation height) this
supplies the consumer's `hmin` over the ENTIRE truncated contour range, so no
overhang comparison is needed at all. -/
theorem exists_min_dist_on_Icc (f : ℕ → ℂ) (X : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ t₁ ∈ Set.Icc (-R) R, ∀ v ∈ Set.Icc (-R) R,
      pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist v) X := by
  have hne : (Set.Icc (-R) R).Nonempty := ⟨0, Set.mem_Icc.mpr ⟨by linarith, hR⟩⟩
  obtain ⟨t₁, ht₁, hmin⟩ := isCompact_Icc.exists_isMinOn hne
    (pretDistSq_continuous_freq f X).continuousOn
  exact ⟨t₁, ht₁, fun v hv => isMinOn_iff.mp hmin v hv⟩

/-- **C2, absolute-value form.**  The same minimizer, with the compact written as
`|·| ≤ R` — the shape the truncated-contour consumer states its `hmin` in. -/
theorem exists_min_dist_abs (f : ℕ → ℂ) (X : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ t₁ : ℝ, |t₁| ≤ R ∧ ∀ v : ℝ, |v| ≤ R →
      pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist v) X := by
  obtain ⟨t₁, ht₁, hmin⟩ := exists_min_dist_on_Icc f X hR
  refine ⟨t₁, abs_le.mpr ⟨(Set.mem_Icc.mp ht₁).1, (Set.mem_Icc.mp ht₁).2⟩, fun v hv => ?_⟩
  exact hmin v (Set.mem_Icc.mpr ⟨(abs_le.mp hv).1, (abs_le.mp hv).2⟩)

/-! ## C3a — the Lipschitz stone -/

/-- **The per-argument twist Lipschitz bound.**  `‖n^{iv} − n^{iw}‖ ≤ |v − w|·|log n|`.
Sharp constant `1`: factor out the unimodular `n^{iw}` and apply
`Real.norm_exp_I_mul_ofReal_sub_one_le` (`‖e^{ix} − 1‖ ≤ |x|`, i.e. `2|sin(x/2)| ≤ |x|`).
Going through `Re` per real/imaginary part instead would cost a factor `2`. -/
lemma norm_costwist_sub_le (v w : ℝ) (n : ℕ) :
    ‖costwist v n - costwist w n‖ ≤ |v - w| * |Real.log n| := by
  have hsplit : costwist v n
      = costwist w n * Complex.exp (Complex.I * (((v - w) * Real.log n : ℝ) : ℂ)) := by
    unfold costwist
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfac : costwist v n - costwist w n
      = costwist w n * (Complex.exp (Complex.I * (((v - w) * Real.log n : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← hsplit]
  rw [hfac, norm_mul, costwist_norm, one_mul]
  calc ‖Complex.exp (Complex.I * (((v - w) * Real.log n : ℝ) : ℂ)) - 1‖
      ≤ ‖((v - w) * Real.log n : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |v - w| * |Real.log n| := by rw [Real.norm_eq_abs, abs_mul]

/-- **C3a — the frequency map is Lipschitz.**  For 1-bounded `f` and `X ≥ 1`,

  `|𝔻(f, n^{iv}; X)² − 𝔻(f, n^{iw}; X)²| ≤ |v − w|·(log X + (log 4 + 4))`.

Per prime the drift is `|Re(f(p)(n^{-iw} − n^{-iv}))|/p ≤ |v − w|·log p/p`
(`norm_costwist_sub_le` + `Complex.abs_re_le_norm`), and Mertens' first theorem
(`mertens_first_upper`) sums `∑_{p≤X} log p/p ≤ log X + (log 4 + 4)`.

NOTE the scale: the constant is `log X`-sized, i.e. HUGE next to the `loglog X`
band scale.  C3a is therefore useless for near-corner comparisons (it cannot beat
an `o(loglog X)` slack over a unit frequency shift) — which is precisely why C3
below takes the minimizer-localization route rather than an overhang comparison.
It is landed for its independent uses (measurability/modulus-of-continuity of the
frequency profile, net/discretization arguments over the truncated contour). -/
theorem pretDistSq_freq_lipschitz {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {X : ℝ} (hX : 1 ≤ X)
    (v w : ℝ) :
    |pretDistSq f (costwist v) X - pretDistSq f (costwist w) X|
      ≤ |v - w| * (Real.log X + (Real.log 4 + 4)) := by
  have hvw : (0 : ℝ) ≤ |v - w| := abs_nonneg _
  have hdiff : pretDistSq f (costwist v) X - pretDistSq f (costwist w) X
      = ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
          ((f p * (starRingEnd ℂ) (costwist w p)).re
            - (f p * (starRingEnd ℂ) (costwist v p)).re) / (p : ℝ) := by
    unfold pretDistSq
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have hterm : ∀ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
      |((f p * (starRingEnd ℂ) (costwist w p)).re
        - (f p * (starRingEnd ℂ) (costwist v p)).re) / (p : ℝ)|
        ≤ |v - w| * (Real.log p / (p : ℝ)) := by
    intro p hp
    have hpr : p.Prime := (Finset.mem_filter.mp hp).2
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.one_lt.le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hre : (f p * (starRingEnd ℂ) (costwist w p)).re
        - (f p * (starRingEnd ℂ) (costwist v p)).re
        = (f p * (starRingEnd ℂ) (costwist w p - costwist v p)).re := by
      rw [map_sub, mul_sub, Complex.sub_re]
    have hlogabs : |Real.log (p : ℝ)| = Real.log (p : ℝ) :=
      abs_of_nonneg (Real.log_nonneg hp1)
    have hnum : |(f p * (starRingEnd ℂ) (costwist w p - costwist v p)).re|
        ≤ |v - w| * Real.log (p : ℝ) := by
      have h1 := Complex.abs_re_le_norm (f p * (starRingEnd ℂ) (costwist w p - costwist v p))
      rw [norm_mul, Complex.norm_conj] at h1
      have h2 : ‖costwist w p - costwist v p‖ ≤ |v - w| * Real.log (p : ℝ) := by
        have h3 := norm_costwist_sub_le w v p
        rwa [abs_sub_comm w v, hlogabs] at h3
      have h4 : ‖f p‖ * ‖costwist w p - costwist v p‖ ≤ 1 * (|v - w| * Real.log (p : ℝ)) :=
        mul_le_mul (hf p) h2 (norm_nonneg _) zero_le_one
      linarith [h1, h4]
    rw [hre, abs_div, abs_of_pos hppos]
    rw [div_le_iff₀ hppos]
    have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
    calc |(f p * (starRingEnd ℂ) (costwist w p - costwist v p)).re|
        ≤ |v - w| * Real.log (p : ℝ) := hnum
      _ = |v - w| * (Real.log (p : ℝ) / (p : ℝ)) * (p : ℝ) := by field_simp
  rw [hdiff]
  calc |∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
          ((f p * (starRingEnd ℂ) (costwist w p)).re
            - (f p * (starRingEnd ℂ) (costwist v p)).re) / (p : ℝ)|
      ≤ ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
          |((f p * (starRingEnd ℂ) (costwist w p)).re
            - (f p * (starRingEnd ℂ) (costwist v p)).re) / (p : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
          |v - w| * (Real.log p / (p : ℝ)) := Finset.sum_le_sum hterm
    _ = |v - w| * ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
          Real.log p / (p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ |v - w| * (Real.log X + (Real.log 4 + 4)) := by
        exact mul_le_mul_of_nonneg_left (mertens_first_upper hX) hvw

/-! ## C3 — the overhang floor (the honest form) -/

/-- **The two-cap triangle.**  If `f` is within `√S` (in `𝔻`) of BOTH pure characters
`n^{it₀}` and `n^{iv}`, then those two characters are within `2√S` of each other:
`𝔻(1, n^{i(v−t₀)}; X)² ≤ 4S`.  This is `pretDist_triangle` at
`(n^{it₀}, f, n^{iv})` plus the center shift `pretDistSq_costwist_shift`.

It is the engine of `overhang_no_undercut`: an overhang point that undercut the
cap would drag `n^{i(v−t₀)}` pretentiously close to `1`, which the uncapped floor
`dist_one_floor_pow` forbids once `|v − t₀| ≥ 1`. -/
theorem dist_one_shift_le_of_two_caps {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {t₀ v X S : ℝ}
    (hS0 : 0 ≤ S)
    (h0 : pretDistSq f (costwist t₀) X ≤ S) (h1 : pretDistSq f (costwist v) X ≤ S) :
    pretDistSq (fun _ => 1) (costwist (v - t₀)) X ≤ 4 * S := by
  have htri := pretDist_triangle (f := costwist t₀) (g := f) (h := costwist v) X
    (norm_costwist_le t₀) hf (norm_costwist_le v)
  have e0 : pretDist (costwist t₀) f X ≤ Real.sqrt S := by
    rw [pretDist_comm]; unfold pretDist; exact Real.sqrt_le_sqrt h0
  have e1 : pretDist f (costwist v) X ≤ Real.sqrt S := by
    unfold pretDist; exact Real.sqrt_le_sqrt h1
  have hnn : 0 ≤ pretDist (costwist t₀) (costwist v) X := Real.sqrt_nonneg _
  have hsq : pretDist (costwist t₀) (costwist v) X ^ 2
      = pretDistSq (costwist t₀) (costwist v) X :=
    Real.sq_sqrt (pretDistSq_nonneg _ _ _ (norm_costwist_le t₀) (norm_costwist_le v))
  have hSsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0
  rw [← pretDistSq_costwist_shift t₀ v X, ← hsq]
  nlinarith [htri, e0, e1, hnn, hSsq, Real.sqrt_nonneg S]

/-- **C3 — the overhang cannot undercut the cap (`overhang_no_undercut`).**

Fix a live-band witness `t₀` with `|t₀| ≤ X` carrying the ball-live cap
`𝔻(f, n^{it₀}; X)² ≤ S`.  Let `v` be a DEEP overhang point: `|v| ≤ 3X` (the
truncated contour range `R = X + T*` with `T* ≤ 2X` is inside this) and
`|v − t₀| ≥ 1`.  Then, under the strict floor-versus-cap gap

  `4S < loglog X − (3/4)·loglog(4X+3) − 5·logloglog(4X+16) − C`,

the distance at `v` strictly EXCEEDS the cap: `S < 𝔻(f, n^{iv}; X)²`.

Proof: if not, `dist_one_shift_le_of_two_caps` gives `𝔻(1, n^{i(v−t₀)}; X)² ≤ 4S`
while `dist_one_floor_pow` (uncapped, at `|v − t₀| ≥ 1`) bounds the same quantity
below by the left side of `hgap` after the height monotonicity
`|v − t₀| ≤ |v| + |t₀| ≤ 4X`.

Consequence (`compact_min_package`): the minimizer over the truncated range must
sit within frequency-distance `1` of the witness, hence `|t₁| ≤ X + 1`.  Full
localization `|t₁| ≤ X` is FALSE — see the module docstring's counterexample. -/
theorem overhang_no_undercut :
    ∃ C : ℝ, ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) → ∀ X S t₀ v : ℝ,
      Real.exp 1 ≤ X → 0 ≤ S → |t₀| ≤ X → |v| ≤ 3 * X → 1 ≤ |v - t₀| →
      pretDistSq f (costwist t₀) X ≤ S →
      4 * S < Real.log (Real.log X)
          - (3 / 4) * Real.log (Real.log (4 * X + 3))
          - 5 * Real.log (Real.log (Real.log (4 * X + 16))) - C →
      S < pretDistSq f (costwist v) X := by
  obtain ⟨C, hC⟩ := dist_one_floor_pow
  refine ⟨C, fun f hf X S t₀ v hX hS0 ht0 hv hfar hcap hgap => ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  -- both caps hold, so the two characters are `𝔻`-close
  have h4S := dist_one_shift_le_of_two_caps hf hS0 hcap hcon
  -- the uncapped floor at the shifted frequency
  have hfloor := hC X (v - t₀) hX hfar
  -- the height: `|v − t₀| ≤ 4X`
  have hb0 : (0 : ℝ) ≤ |v - t₀| := abs_nonneg _
  have hb4 : |v - t₀| ≤ 4 * X := by
    obtain ⟨hv1, hv2⟩ := abs_le.mp hv
    obtain ⟨ht1, ht2⟩ := abs_le.mp ht0
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hX2 : (2 : ℝ) ≤ X := by
    have h := Real.add_one_le_exp (1 : ℝ); linarith
  -- monotonicity of the two `o(loglog)` corrections in the height
  have hmon3 : Real.log (Real.log (|v - t₀| + 3)) ≤ Real.log (Real.log (4 * X + 3)) := by
    have hpos : (0 : ℝ) < Real.log (|v - t₀| + 3) := Real.log_pos (by linarith)
    exact Real.log_le_log hpos (Real.log_le_log (by linarith) (by linarith))
  have hmon16 : Real.log (Real.log (Real.log (|v - t₀| + 16)))
      ≤ Real.log (Real.log (Real.log (4 * X + 16))) := by
    have he16 : Real.exp 1 < |v - t₀| + 16 := by
      have h := Real.exp_one_lt_d9
      linarith
    have h1 : (1 : ℝ) < Real.log (|v - t₀| + 16) := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ < Real.log (|v - t₀| + 16) := Real.log_lt_log (Real.exp_pos 1) he16
    have hpos : (0 : ℝ) < Real.log (Real.log (|v - t₀| + 16)) := Real.log_pos h1
    refine Real.log_le_log hpos (Real.log_le_log (by linarith) ?_)
    exact Real.log_le_log (by linarith) (by linarith)
  linarith [hfloor, h4S, hmon3, hmon16, hgap]

/-! ## C4 — the consumer-facing package -/

/-- **C4 — the compact-minimizer package (the B-2 exit).**  For 1-bounded `f`,
`X ≥ e`, a truncated-contour radius `R` with `X ≤ R ≤ 3X` (i.e. `R = X + T*`,
`T* ≤ 2X`), a live-band witness `t₀` with `|t₀| ≤ X` carrying the cap
`𝔻(f, n^{it₀}; X)² ≤ S`, and the strict floor-versus-cap gap `hgap`, there is a
frequency `t₁` with

* `|t₁| ≤ R` — it lives in the truncated range;
* `∀ v, |v| ≤ R → 𝔻(f, n^{it₁}; X)² ≤ 𝔻(f, n^{iv}; X)²` — the HONEST `hmin`,
  quantified over the compact only (the vacuity repair);
* `𝔻(f, n^{it₁}; X)² ≤ S` — the cap is inherited by minimality, so `t₁` is itself
  a live-band center;
* `𝔻(f, n^{it₁}; X)² ≤ 𝔻(f, n^{iv}; X)²` for every `|v| ≤ X` in particular, so
  `𝔻²(t₁)` sits below the `[−X, X]`-infimum `M(f; X)` — the terminal's M-shaped
  comparison, in the SOUND direction (a smaller `𝔻²` is a weaker grade claim);
* `|t₁ − t₀| < 1` and `|t₁| ≤ X + 1` — near-localization (C3).

Nothing here is conditional on an unattained infimum: the minimizer is produced by
the extreme value theorem on `[−R, R]`. -/
theorem compact_min_package :
    ∃ C : ℝ, ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) → ∀ X R S t₀ : ℝ,
      Real.exp 1 ≤ X → 0 ≤ S → |t₀| ≤ X → X ≤ R → R ≤ 3 * X →
      pretDistSq f (costwist t₀) X ≤ S →
      4 * S < Real.log (Real.log X)
          - (3 / 4) * Real.log (Real.log (4 * X + 3))
          - 5 * Real.log (Real.log (Real.log (4 * X + 16))) - C →
      ∃ t₁ : ℝ, |t₁| ≤ R
        ∧ (∀ v : ℝ, |v| ≤ R →
            pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist v) X)
        ∧ pretDistSq f (costwist t₁) X ≤ S
        ∧ |t₁ - t₀| < 1
        ∧ |t₁| ≤ X + 1 := by
  obtain ⟨C, hC⟩ := overhang_no_undercut
  refine ⟨C, fun f hf X R S t₀ hX hS0 ht0 hXR hR3 hcap hgap => ?_⟩
  have hX2 : (2 : ℝ) ≤ X := by
    have h := Real.add_one_le_exp (1 : ℝ); linarith
  have hR0 : (0 : ℝ) ≤ R := by linarith
  obtain ⟨t₁, ht₁R, hmin⟩ := exists_min_dist_abs f X hR0
  -- the witness lies in the truncated range, so the cap is inherited
  have ht0R : |t₀| ≤ R := le_trans ht0 hXR
  have hcapt₁ : pretDistSq f (costwist t₁) X ≤ S := le_trans (hmin t₀ ht0R) hcap
  -- near-localization: a deep overhang point would strictly exceed the cap
  have hnear : |t₁ - t₀| < 1 := by
    by_contra hfar
    rw [not_lt] at hfar
    have ht₁3 : |t₁| ≤ 3 * X := le_trans ht₁R hR3
    exact absurd hcapt₁ (not_le.mpr (hC f hf X S t₀ t₁ hX hS0 ht0 ht₁3 hfar hcap hgap))
  refine ⟨t₁, ht₁R, hmin, hcapt₁, hnear, ?_⟩
  obtain ⟨h1, h2⟩ := abs_le.mp ht0
  obtain ⟨h3, h4⟩ := abs_lt.mp hnear
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Salt.MR
