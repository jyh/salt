/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.LargeValueCount
import Salt.MR.HybridMVT

/-!
# KMT port, wave P-3: the discrete hybrid large sieve (Lemma 6.3) and the hybrid
large-value count (Lemma 6.5)

Freeze: `docs/exploration/port-freeze-0729.md` (wave P-3, "6.3 + 6.5 at `qT`").
READER-A's §6 mapping: 6.3 *is* the corpus's own written-out Gallagher template
(`wellspaced_l2`, `Salt/MR/LargeValues.lean`) with the mean-value input swapped from the
`t`-only MVT to P-2's `hybrid_char_mvt`; 6.5 *is* `large_value_count`
(`Salt/MR/LargeValueCount.lean`) at `T → qT`, the `k!`-combinatorial core being
character-free and reused verbatim.

## D1 — the discrete hybrid large sieve (KMT Lemma 6.3)

For `s ⊆ [1, N]`, a set `ℰ` of pairs `(χ, t)` with `χ` running over *all* characters mod
`q`, ordinates in `[−T, T]`, and the **per-fibre** spacing condition (two ordinates paired
with the *same* `χ` differ by at least `1`; ordinates paired with different characters are
unconstrained — `FibreWellSpaced`):

`∑_{(χ,t) ∈ ℰ} ‖∑_{n∈s} aₙ χ(n) n^{it}‖²`
`  ≤ 84·(φ(q)·(T+1) + φ(q)·N/q)·log(2N)·∑_{n∈s, (n,q)=1} ‖aₙ‖²`.

Route (the template's, per fibre): `gallagher_pointwise` at `δ = 1` at each `(χ, t)`,
summed over the fibre by the unit-window disjointness (`sum_intervalIntegral_le`), then the
weighted AM–GM at `L = log(2N)` — **and only then** the `χ`-sum, so that the mean-value
input is `hybrid_char_mvt` (all `φ(q)` characters at once) rather than `φ(q)` copies of the
`q = 1` theorem.  R-P3's warning is exactly this: summing the `q = 1` result over `χ` pays
`φ(q)·N`, losing the `1/q` on the `N`-term.  The derivative moment is the same hybrid MVT
at the frequency-twisted coefficients (`hybrid_char_mvt_deriv`), whose `(log N)²` the AM–GM
collapses to a single `log(2N)`.

The `T + 1` (rather than `T`) is the honest cost of the window widening: Gallagher's unit
windows at ordinates in `[−T, T]` live in `[−(T+½), T+½]`, and `2·φ(q)·(T+½) = φ(q)·2T +
φ(q)`.  The stray `φ(q)` is **not** absorbable into `φ(q)·N/q` (that term can be smaller
than `φ(q)` for large `q`), so it is carried in the statement; at any `T ≥ 1` a caller may
read `T + 1 ≤ 2T`.  The constant `84` is the template's and is inessential (`28` suffices).

## D2 — the hybrid large-value count (KMT Lemma 6.5)

For `c` supported on primes in `[P, 2P]` with `‖c_m‖ ≤ 1/m` and `ℰ` as above with
`V⁻¹ ≤ ‖∑_{P≤p≤2P} c_p χ(p) p^{it}‖` at every `(χ, t) ∈ ℰ`:

`|ℰ| ≤ 1680·(qT)^{2 log V/log P}·V²·exp(2·(log qT/log P)·loglog qT)`.

The spine is the landed one, re-run: (a) the `k`-th power step at the `χ`-polynomial —
`dpolyChi q (Icc 1 N) c χ = dpoly N (c·χ)`, and complete multiplicativity distributes over
the `k`-fold convolution (`kconv_coeffChiTwist`), so the `kconv` machinery (support, `ω`-count,
`k!` sup bound, `L¹`/`L²` masses) is consumed **verbatim** — the twist only multiplies each
coefficient by a unit-modulus factor; (b) the well-spaced `L²` input swapped to D1; (c) the
`T → qT` rewrite inside `pow_V_le` / `pack_exp_le`, which are pure real analysis and are
reused unchanged at the argument `qT`.  The corpus's product-form bound (vs KMT's sum-form)
is the accepted weakening.  The constant `1680 = 2·840` — the `2` is the bracket domination
`φ(q)(T+1) + φ(q)·(2P)^k/q ≤ 2·(qT + (2P)^k)` at `T ≥ 1`.

## Conventions and traps

* **CATCH #A (`σ = 1`).**  The coefficient convention is the corpus's: `c_m` is the
  *already-divided* coefficient, `‖c_m‖ ≤ 1/m` (i.e. `c_p = a_p/p` with `|a_p| ≤ 1`
  pre-folded).  KMT states Lemma 6.5 at `σ = 0` with `|a_p| ≤ 1`; the dictionary is
  `V_corpus = V_KMT·P^{-0}`-shaped, i.e. the paper's `V` at height `P^α` reads here as the
  threshold on the `σ = 1` polynomial.  All statements below are at the corpus convention.
* **CATCH #B (the `t`-sign).**  `dpolyChi` is written at `n^{+it}` (KMT's convention); the
  corpus's large-value callers write `P(1−it)`.  A caller holding the lower bound at
  `1 − it` supplies it here at the *negated* ordinate set `{(χ, −t) : (χ,t) ∈ ℰ}`, which is
  `FibreWellSpaced` and inside `[−T, T]` exactly when `ℰ` is, and has the same cardinality;
  for the mean-square form the invariance is `dpolyS_meanSq_reflect`.
* **The four log scales.**  `log(2N)` (D1's Gallagher factor, `N = (2P)^k` downstream),
  `log P` (the amplification exponent's denominator), `log(qT)` and `loglog(qT)` (D2's
  packaging).  Only `log(qT)` and `loglog(qT)` carry `q`.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory intervalIntegral Set

/-! ## The `(χ, t)` index set and its per-fibre spacing -/

/-- **Per-fibre well-spacing of a `(χ, t)`-set.**  Two members of `ℰ` sharing the *same*
character have ordinates at least `1` apart.  Ordinates attached to *different* characters
are unconstrained — this is READER-A's ambiguity, resolved to the same-`χ` reading (it is
what the fibrewise Gallagher argument needs, and it is the weaker hypothesis). -/
def FibreWellSpaced {q : ℕ} (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) : Prop :=
  ∀ p ∈ ℰ, ∀ r ∈ ℰ, p.1 = r.1 → p.2 ≠ r.2 → 1 ≤ |p.2 - r.2|

/-- **The fibre decomposition of a `(χ, t)`-set.**  Every finite set of pairs is the disjoint
union of its character fibres: there is a family `𝒯 : (characters) → Finset ℝ` with
`t ∈ 𝒯 χ ↔ (χ, t) ∈ ℰ`, through which every `ℝ`-valued sum over `ℰ` regroups.

Packaged existentially so that no *statement* in this file mentions a decidable-equality
instance on characters (there is none; the construction uses `Classical` internally). -/
lemma exists_charFibre {q : ℕ} (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) :
    ∃ 𝒯 : DirichletCharacter ℂ q → Finset ℝ,
      (∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ∈ 𝒯 χ ↔ (χ, t) ∈ ℰ) ∧
      ∀ f : DirichletCharacter ℂ q → ℝ → ℝ,
        (∑ χ : DirichletCharacter ℂ q, ∑ t ∈ 𝒯 χ, f χ t) = ∑ p ∈ ℰ, f p.1 p.2 := by
  classical
  refine ⟨fun χ => (ℰ.filter (fun p => p.1 = χ)).image Prod.snd, ?_, ?_⟩
  · intro χ t
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨p, ⟨hp, hp1⟩, hp2⟩
      have hpe : p = (χ, t) := Prod.ext hp1 hp2
      rw [← hpe]; exact hp
    · intro h; exact ⟨(χ, t), ⟨h, rfl⟩, rfl⟩
  · intro f
    have hinj : ∀ χ : DirichletCharacter ℂ q,
        ∀ x ∈ ℰ.filter (fun p => p.1 = χ), ∀ y ∈ ℰ.filter (fun p => p.1 = χ),
          x.2 = y.2 → x = y := by
      intro χ x hx y hy h
      rw [Finset.mem_filter] at hx hy
      exact Prod.ext (hx.2.trans hy.2.symm) h
    have hstep : ∀ χ : DirichletCharacter ℂ q,
        (∑ t ∈ (ℰ.filter (fun p => p.1 = χ)).image Prod.snd, f χ t)
          = ∑ p ∈ ℰ.filter (fun p => p.1 = χ), f p.1 p.2 := by
      intro χ
      rw [Finset.sum_image (hinj χ)]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.1 hp).2]
    rw [Finset.sum_congr rfl fun χ _ => hstep χ]
    exact Finset.sum_fiberwise ℰ (fun p => p.1) (fun p => f p.1 p.2)

/-! ## The `χ`-twisted derivative -/

/-- Termwise derivative of a `χ`-twisted summand: the frequency `log n` folds into the
coefficient exactly as in the untwisted case (`hasDerivAt_dpoly_term`), the character value
riding along as a constant. -/
lemma hasDerivAt_dpolyChi_term (q : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (n : ℕ)
    (t : ℝ) :
    HasDerivAt (fun t : ℝ => a n * χ (n : ZMod q)
        * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)))
      (dtwist a n * χ (n : ZMod q)
        * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ))) t := by
  have hb : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hg : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ) * (Real.log n : ℂ))
      (Complex.I * 1 * (Real.log n : ℂ)) t := (hb.const_mul Complex.I).mul_const _
  have hexp := hg.cexp
  have hfull := hexp.const_mul (a n * χ (n : ZMod q))
  have hval : dtwist a n * χ (n : ZMod q)
        * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ))
      = a n * χ (n : ZMod q) * (Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ))
          * (Complex.I * 1 * (Real.log n : ℂ))) := by
    unfold dtwist; ring
  rw [hval]
  exact hfull

/-- **The `χ`-twisted derivative.**  `dpolyChi q s a χ` is differentiable in `t`, with
derivative the frequency-twisted `χ`-polynomial `dpolyChi q s (dtwist a) χ`. -/
theorem hasDerivAt_dpolyChi (q : ℕ) (s : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    HasDerivAt (dpolyChi q s a χ) (dpolyChi q s (dtwist a) χ t) t := by
  have h := HasDerivAt.sum (u := s)
    (A := fun n => fun t : ℝ => a n * χ (n : ZMod q)
      * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)))
    (A' := fun n => dtwist a n * χ (n : ZMod q)
      * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)))
    (fun n _ => hasDerivAt_dpolyChi_term q a χ n t)
  have hf : (∑ n ∈ s, fun t : ℝ => a n * χ (n : ZMod q)
        * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)))
      = dpolyChi q s a χ := by
    funext u; rw [Finset.sum_apply]; rfl
  rw [hf] at h
  exact h

/-- `deriv (dpolyChi q s a χ) t = dpolyChi q s (dtwist a) χ t`. -/
theorem deriv_dpolyChi (q : ℕ) (s : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    deriv (dpolyChi q s a χ) t = dpolyChi q s (dtwist a) χ t :=
  (hasDerivAt_dpolyChi q s a χ t).deriv

/-- Each `χ`-twisted summand is globally `C¹`. -/
lemma contDiff_dpolyChi_term (q : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ContDiff ℝ 1 (fun t : ℝ => a n * χ (n : ZMod q)
      * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ))) := by
  have hof : ContDiff ℝ 1 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have harg : ContDiff ℝ 1 (fun t : ℝ => Complex.I * (t : ℂ) * (Real.log n : ℂ)) :=
    (contDiff_const.mul hof).mul contDiff_const
  exact contDiff_const.mul (Complex.contDiff_exp.comp harg)

/-- **`dpolyChi` is globally `C¹`** — the hypothesis `gallagher_pointwise` consumes. -/
theorem contDiff_dpolyChi (q : ℕ) (s : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) : ContDiff ℝ 1 (dpolyChi q s a χ) := by
  unfold dpolyChi
  exact ContDiff.sum (fun n _ => contDiff_dpolyChi_term q a χ n)

/-- `deriv (dpolyChi q s a χ)` is continuous (it is again a `dpolyChi`). -/
lemma continuous_deriv_dpolyChi (q : ℕ) (s : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) : Continuous (deriv (dpolyChi q s a χ)) := by
  have h : deriv (dpolyChi q s a χ) = dpolyChi q s (dtwist a) χ :=
    funext (fun t => deriv_dpolyChi q s a χ t)
  rw [h]
  exact continuous_dpolyChi q s (dtwist a) χ

/-! ## The derivative moment through the hybrid MVT -/

/-- The frequency-twisted coefficient mass on an arbitrary subset of `[1, N]`:
`∑_{n∈s} ‖aₙ·i·log n‖² ≤ (log N)²·∑_{n∈s} ‖aₙ‖²`.  (`sum_dtwist_sq_le` is the case
`s = Icc 1 N`.) -/
lemma sum_dtwist_sq_le_subset {N : ℕ} (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 N) (a : ℕ → ℂ) :
    ∑ n ∈ s, ‖dtwist a n‖ ^ 2 ≤ (Real.log N) ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun n hn => ?_)
  rw [norm_dtwist_sq]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hn' := Finset.mem_Icc.mp (hs hn)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn'.1)
  have hlognN : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hn'.1)
      (by exact_mod_cast hn'.2)
  exact pow_le_pow_left₀ hlogn hlognN 2

/-- **The hybrid MVT for the derivative.**  The same `(2φ(q)T + 7φ(q)N/q)` mean value, at
the frequency-twisted coefficients, whose mass costs a factor `(log N)²`:

`∑_{χ mod q} ∫_{-T}^{T} ‖(d/dt) ∑_{n∈s} aₙ χ(n) n^{it}‖² dt`
`  ≤ (2φ(q)T + 7φ(q)N/q)·(log N)²·∑_{n∈s, (n,q)=1} ‖aₙ‖²`. -/
lemma hybrid_char_mvt_deriv {N : ℕ} (q : ℕ) [NeZero q] (s : Finset ℕ)
    (hs : s ⊆ Finset.Icc 1 N) (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T, ‖deriv (dpolyChi q s a χ) t‖ ^ 2)
      ≤ (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
          * ((Real.log N) ^ 2 * ∑ n ∈ s.filter (fun n => Nat.Coprime n q), ‖a n‖ ^ 2) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hCnn : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q := by
    have h1 : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T := by positivity
    have h2 : (0 : ℝ) ≤ 7 * (q.totient : ℝ) * (N : ℝ) / q := by positivity
    linarith
  have hrw : (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T, ‖deriv (dpolyChi q s a χ) t‖ ^ 2)
      = ∑ χ : DirichletCharacter ℂ q,
          ∫ t in (-T)..T, ‖dpolyChi q s (dtwist a) χ t‖ ^ 2 := by
    refine Finset.sum_congr rfl fun χ _ => ?_
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [deriv_dpolyChi]
  rw [hrw]
  refine (hybrid_char_mvt q s hs (dtwist a) T).trans (mul_le_mul_of_nonneg_left ?_ hCnn)
  exact sum_dtwist_sq_le_subset (s.filter (fun n => Nat.Coprime n q))
    ((Finset.filter_subset _ _).trans hs) a

/-! ## D1 — the discrete hybrid large sieve (KMT Lemma 6.3) -/

/-- **The closing arithmetic of D1.**  The Gallagher/AM–GM output `(2φ(T+½) + 7Z)·(1+2L)`
fits under `84·(φ(T+1) + Z)·L` once `L ≥ ½` (which `L = log(2N)` gives at `N ≥ 1`).  Here
`Z` stands for the `φ(q)·N/q` off-diagonal term.  The constant `84` is the `q = 1`
template's; `28` would suffice. -/
lemma hybrid_l2_arith {φ T Z L : ℝ} (hφ : 0 ≤ φ) (hT : 0 ≤ T) (hZ : 0 ≤ Z)
    (hL : 1 / 2 ≤ L) :
    (2 * φ * (T + 1 / 2) + 7 * Z) * (1 + 2 * L) ≤ 84 * (φ * (T + 1) + Z) * L := by
  have hslack : (0 : ℝ) ≤ L - 1 / 2 := by linarith
  have hA : (0 : ℝ) ≤ φ * T := mul_nonneg hφ hT
  nlinarith [mul_nonneg hA hslack, mul_nonneg hφ hslack, mul_nonneg hZ hslack, hA, hφ, hZ]

/-- **The per-fibre Gallagher step.**  For one character `χ` and one well-spaced fibre
`𝒯 ⊆ [−T, T]`, the pointwise Sobolev bound at `δ = 1` plus the unit-window disjointness
plus the integrated weighted AM–GM at any `L > 0`:

`∑_{t∈𝒯} ‖F_χ(t)‖² ≤ (1+L)·∫_{-(T+½)}^{T+½}‖F_χ‖² + L⁻¹·∫_{-(T+½)}^{T+½}‖F_χ′‖²`.

This is exactly the middle of `wellspaced_l2`'s proof, isolated so that the `χ`-sum can be
taken *after* it (the fold-then-Gallagher order R-P3's warning forces). -/
lemma dpolyChi_fibre_gallagher (q : ℕ) (s : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : 0 ≤ T) (𝒯 : Finset ℝ)
    (hws : WellSpaced 𝒯) (hsub𝒯 : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) {L : ℝ} (hL : 0 < L) :
    ∑ t ∈ 𝒯, ‖dpolyChi q s a χ t‖ ^ 2
      ≤ (1 + L) * (∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2)
        + L⁻¹ * ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpolyChi q s a χ) u‖ ^ 2 := by
  have hcF := continuous_dpolyChi q s a χ
  have hcF' := continuous_deriv_dpolyChi q s a χ
  have hsubwin : ∀ t ∈ 𝒯,
      Set.Ioc (t - 1 / 2) (t + 1 / 2) ⊆ Set.Ioc (-(T + 1 / 2)) (T + 1 / 2) := by
    intro t ht
    have h := Set.mem_Icc.mp (hsub𝒯 t ht)
    exact Set.Ioc_subset_Ioc (by linarith [h.1]) (by linarith [h.2])
  -- Gallagher pointwise (δ = 1) at each ordinate of the fibre
  have hgal : ∀ t ∈ 𝒯, ‖dpolyChi q s a χ t‖ ^ 2
      ≤ (∫ u in (t - 1 / 2)..(t + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2)
        + 2 * ∫ u in (t - 1 / 2)..(t + 1 / 2),
            ‖dpolyChi q s a χ u‖ * ‖deriv (dpolyChi q s a χ) u‖ := by
    intro t _
    have hg := Salt.LS.gallagher_pointwise (contDiff_dpolyChi q s a χ)
      (show (0 : ℝ) < 1 from one_pos) t
    simpa only [inv_one, one_mul] using hg
  have hsum1 : ∑ t ∈ 𝒯, ‖dpolyChi q s a χ t‖ ^ 2
      ≤ (∑ t ∈ 𝒯, ∫ u in (t - 1 / 2)..(t + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2)
        + 2 * ∑ t ∈ 𝒯, ∫ u in (t - 1 / 2)..(t + 1 / 2),
            ‖dpolyChi q s a χ u‖ * ‖deriv (dpolyChi q s a χ) u‖ := by
    have hle := Finset.sum_le_sum (fun t ht => hgal t ht)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hle
    exact hle
  -- unit-window disjointness on both sums
  have hA : (∑ t ∈ 𝒯, ∫ u in (t - 1 / 2)..(t + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2)
      ≤ ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2 :=
    sum_intervalIntegral_le (fun u => ‖dpolyChi q s a χ u‖ ^ 2)
      (hcF.norm.pow 2) (fun u => sq_nonneg _) 𝒯 _ _ (by linarith) hws hsubwin
  have hB0 : (∑ t ∈ 𝒯, ∫ u in (t - 1 / 2)..(t + 1 / 2),
        ‖dpolyChi q s a χ u‖ * ‖deriv (dpolyChi q s a χ) u‖)
      ≤ ∫ u in (-(T + 1 / 2))..(T + 1 / 2),
          ‖dpolyChi q s a χ u‖ * ‖deriv (dpolyChi q s a χ) u‖ :=
    sum_intervalIntegral_le (fun u => ‖dpolyChi q s a χ u‖ * ‖deriv (dpolyChi q s a χ) u‖)
      (hcF.norm.mul hcF'.norm)
      (fun u => mul_nonneg (norm_nonneg _) (norm_nonneg _)) 𝒯 _ _ (by linarith) hws hsubwin
  -- the integrated AM–GM on the cross term
  have hi_FF' : IntervalIntegrable
      (fun u => 2 * (‖dpolyChi q s a χ u‖ * ‖deriv (dpolyChi q s a χ) u‖))
      MeasureTheory.volume (-(T + 1 / 2)) (T + 1 / 2) :=
    (continuous_const.mul (hcF.norm.mul hcF'.norm)).intervalIntegrable _ _
  have hi_amgm : IntervalIntegrable
      (fun u => L * ‖dpolyChi q s a χ u‖ ^ 2 + L⁻¹ * ‖deriv (dpolyChi q s a χ) u‖ ^ 2)
      MeasureTheory.volume (-(T + 1 / 2)) (T + 1 / 2) :=
    ((continuous_const.mul (hcF.norm.pow 2)).add
      (continuous_const.mul (hcF'.norm.pow 2))).intervalIntegrable _ _
  have hi_F2 : IntervalIntegrable (fun u => ‖dpolyChi q s a χ u‖ ^ 2)
      MeasureTheory.volume (-(T + 1 / 2)) (T + 1 / 2) := (hcF.norm.pow 2).intervalIntegrable _ _
  have hi_F'2 : IntervalIntegrable (fun u => ‖deriv (dpolyChi q s a χ) u‖ ^ 2)
      MeasureTheory.volume (-(T + 1 / 2)) (T + 1 / 2) := (hcF'.norm.pow 2).intervalIntegrable _ _
  have hCross : 2 * (∫ u in (-(T + 1 / 2))..(T + 1 / 2),
        ‖dpolyChi q s a χ u‖ * ‖deriv (dpolyChi q s a χ) u‖)
      ≤ L * (∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2)
        + L⁻¹ * ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpolyChi q s a χ) u‖ ^ 2 := by
    have heq : (∫ u in (-(T + 1 / 2))..(T + 1 / 2),
          L * ‖dpolyChi q s a χ u‖ ^ 2 + L⁻¹ * ‖deriv (dpolyChi q s a χ) u‖ ^ 2)
        = L * (∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2)
          + L⁻¹ * ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpolyChi q s a χ) u‖ ^ 2 := by
      rw [intervalIntegral.integral_add (hi_F2.const_mul L) (hi_F'2.const_mul L⁻¹),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hL2 : (∫ u in (-(T + 1 / 2))..(T + 1 / 2),
          2 * (‖dpolyChi q s a χ u‖ * ‖deriv (dpolyChi q s a χ) u‖))
        = 2 * ∫ u in (-(T + 1 / 2))..(T + 1 / 2),
            ‖dpolyChi q s a χ u‖ * ‖deriv (dpolyChi q s a χ) u‖ := by
      rw [intervalIntegral.integral_const_mul]
    rw [← heq, ← hL2]
    exact intervalIntegral.integral_mono_on (by linarith) hi_FF' hi_amgm
      (fun u _ => two_mul_le_amgm hL)
  have hb := mul_le_mul_of_nonneg_left hB0 (by norm_num : (0 : ℝ) ≤ 2)
  linarith [hsum1, hA, hb, hCross]

/-- **D1 (family form) — the discrete hybrid large sieve, KMT Lemma 6.3.**  Stated over a
family of fibres `𝒯 χ` (one well-spaced ordinate set per character), which is the shape the
proof runs in; `hybrid_wellspaced_l2` is the `(χ,t)`-set restatement. -/
theorem hybrid_wellspaced_l2_family {N : ℕ} (q : ℕ) [NeZero q] (s : Finset ℕ)
    (hs : s ⊆ Finset.Icc 1 N) (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (𝒯 : DirichletCharacter ℂ q → Finset ℝ) (hws : ∀ χ, WellSpaced (𝒯 χ))
    (hsub𝒯 : ∀ χ, ∀ t ∈ 𝒯 χ, t ∈ Set.Icc (-T) T) :
    (∑ χ : DirichletCharacter ℂ q, ∑ t ∈ 𝒯 χ, ‖dpolyChi q s a χ t‖ ^ 2)
      ≤ 84 * ((q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * (N : ℝ) / q)
          * Real.log (2 * N) * ∑ n ∈ s.filter (fun n => Nat.Coprime n q), ‖a n‖ ^ 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hφnn : (0 : ℝ) ≤ (q.totient : ℝ) := by positivity
  rcases s.eq_empty_or_nonempty with hemp | hne
  · subst hemp
    simp [dpolyChi]
  -- `s` nonempty forces `N ≥ 1`
  obtain ⟨n₀, hn₀⟩ := hne
  have hN : 0 < N := by
    have := Finset.mem_Icc.1 (hs hn₀)
    omega
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set M := ∑ n ∈ s.filter (fun n => Nat.Coprime n q), ‖a n‖ ^ 2 with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun n _ => by positivity)
  set LL := Real.log (2 * (N : ℝ)) with hLLdef
  set LN := Real.log (N : ℝ) with hLNdef
  have hLLpos : 0 < LL := Real.log_pos (by linarith)
  have hLLnn : 0 ≤ LL := hLLpos.le
  have hLNnn : 0 ≤ LN := Real.log_nonneg hN1
  have hLNLL : LN ≤ LL := Real.log_le_log (by linarith) (by linarith)
  have hLLhalf : (1 : ℝ) / 2 ≤ LL := by
    have hlog2 : Real.log 2 ≤ LL := Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  have hT' : (0 : ℝ) ≤ T + 1 / 2 := by linarith
  -- the per-fibre Gallagher step, then the χ-sum
  have hper : ∀ χ : DirichletCharacter ℂ q,
      ∑ t ∈ 𝒯 χ, ‖dpolyChi q s a χ t‖ ^ 2
        ≤ (1 + LL) * (∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2)
          + LL⁻¹ * ∫ u in (-(T + 1 / 2))..(T + 1 / 2),
              ‖deriv (dpolyChi q s a χ) u‖ ^ 2 := fun χ =>
    dpolyChi_fibre_gallagher q s a χ hT (𝒯 χ) (hws χ) (hsub𝒯 χ) hLLpos
  have hsplit : (∑ χ : DirichletCharacter ℂ q,
        ((1 + LL) * (∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2)
          + LL⁻¹ * ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpolyChi q s a χ) u‖ ^ 2))
      = (1 + LL) * (∑ χ : DirichletCharacter ℂ q,
            ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2)
        + LL⁻¹ * ∑ χ : DirichletCharacter ℂ q,
            ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpolyChi q s a χ) u‖ ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the two hybrid mean values, at the widened window
  set C := 2 * (q.totient : ℝ) * (T + 1 / 2) + 7 * (q.totient : ℝ) * (N : ℝ) / q with hCdef
  have hCnn : (0 : ℝ) ≤ C := by
    have h1 : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * (T + 1 / 2) := by positivity
    have h2 : (0 : ℝ) ≤ 7 * (q.totient : ℝ) * (N : ℝ) / q := by positivity
    rw [hCdef]; linarith
  have hI : (∑ χ : DirichletCharacter ℂ q,
        ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2) ≤ C * M :=
    hybrid_char_mvt q s hs a (T + 1 / 2)
  have hJ : (∑ χ : DirichletCharacter ℂ q,
        ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpolyChi q s a χ) u‖ ^ 2)
      ≤ C * (LN ^ 2 * M) := hybrid_char_mvt_deriv q s hs a hT'
  have hCM0 : (0 : ℝ) ≤ C * M := mul_nonneg hCnn hM0
  have hLLinvLN : LL⁻¹ * LN ^ 2 ≤ LL := by
    have hsq : LN ^ 2 ≤ LL ^ 2 := by nlinarith [hLNnn, hLNLL]
    have h1 : LL⁻¹ * LN ^ 2 ≤ LL⁻¹ * LL ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hLLnn)
    have h2 : LL⁻¹ * LL ^ 2 = LL := by field_simp
    linarith [h1, h2]
  have hJ' : LL⁻¹ * (∑ χ : DirichletCharacter ℂ q,
        ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpolyChi q s a χ) u‖ ^ 2)
      ≤ LL * (C * M) := by
    calc LL⁻¹ * (∑ χ : DirichletCharacter ℂ q,
          ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpolyChi q s a χ) u‖ ^ 2)
        ≤ LL⁻¹ * (C * (LN ^ 2 * M)) := mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hLLnn)
      _ = (LL⁻¹ * LN ^ 2) * (C * M) := by ring
      _ ≤ LL * (C * M) := mul_le_mul_of_nonneg_right hLLinvLN hCM0
  -- the closing arithmetic
  have hX : (0 : ℝ) ≤ (q.totient : ℝ) * T := by positivity
  have hZ : (0 : ℝ) ≤ (q.totient : ℝ) * (N : ℝ) / q := by positivity
  have harith : C * (1 + 2 * LL)
      ≤ 84 * ((q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * (N : ℝ) / q) * LL := by
    rw [hCdef,
      show 2 * (q.totient : ℝ) * (T + 1 / 2) + 7 * (q.totient : ℝ) * (N : ℝ) / q
        = 2 * (q.totient : ℝ) * (T + 1 / 2) + 7 * ((q.totient : ℝ) * (N : ℝ) / q) from by ring]
    exact hybrid_l2_arith hφnn hT hZ hLLhalf
  calc (∑ χ : DirichletCharacter ℂ q, ∑ t ∈ 𝒯 χ, ‖dpolyChi q s a χ t‖ ^ 2)
      ≤ ∑ χ : DirichletCharacter ℂ q,
          ((1 + LL) * (∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2)
            + LL⁻¹ * ∫ u in (-(T + 1 / 2))..(T + 1 / 2),
                ‖deriv (dpolyChi q s a χ) u‖ ^ 2) := Finset.sum_le_sum fun χ _ => hper χ
    _ = (1 + LL) * (∑ χ : DirichletCharacter ℂ q,
            ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2)
          + LL⁻¹ * ∑ χ : DirichletCharacter ℂ q,
              ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpolyChi q s a χ) u‖ ^ 2 := hsplit
    _ ≤ (1 + LL) * (C * M) + LL * (C * M) := by
          have h1 : (1 + LL) * (∑ χ : DirichletCharacter ℂ q,
                ∫ u in (-(T + 1 / 2))..(T + 1 / 2), ‖dpolyChi q s a χ u‖ ^ 2)
              ≤ (1 + LL) * (C * M) :=
            mul_le_mul_of_nonneg_left hI (by linarith)
          linarith [h1, hJ']
    _ = (C * (1 + 2 * LL)) * M := by ring
    _ ≤ 84 * ((q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * (N : ℝ) / q) * LL * M :=
          mul_le_mul_of_nonneg_right harith hM0

/-- **D1 — THE DISCRETE HYBRID LARGE SIEVE (KMT Lemma 6.3).**  For `s ⊆ [1, N]`, coefficients
`a`, and a finite set `ℰ` of pairs `(χ, t)` with `χ` running over the characters mod `q`,
ordinates in `[−T, T]`, and per-fibre spacing (`FibreWellSpaced`: same-`χ` ordinates are
`1`-separated):

`∑_{(χ,t)∈ℰ} ‖∑_{n∈s} aₙ·χ(n)·n^{it}‖²`
`  ≤ 84·(φ(q)·(T+1) + φ(q)·N/q)·log(2N)·∑_{n∈s, (n,q)=1} ‖aₙ‖²`.

The mass is the sharp coprime-restricted one (non-coprime `n` contribute nothing since
`χ(n) = 0`).  The `φ(q)/q` on the `N`-term is the whole point: it is bought by running the
mean value on residue classes (P-2's `hybrid_char_mvt`) *before* the character sum — summing
the `q = 1` `wellspaced_l2` over `χ` would pay `φ(q)·N`.  See the module docstring for the
`T + 1` accounting and for CATCH #B (the `t`-sign). -/
theorem hybrid_wellspaced_l2 {N : ℕ} (q : ℕ) [NeZero q] (s : Finset ℕ)
    (hs : s ⊆ Finset.Icc 1 N) (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ p ∈ ℰ, p.2 ∈ Set.Icc (-T) T) :
    (∑ p ∈ ℰ, ‖dpolyChi q s a p.1 p.2‖ ^ 2)
      ≤ 84 * ((q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * (N : ℝ) / q)
          * Real.log (2 * N) * ∑ n ∈ s.filter (fun n => Nat.Coprime n q), ‖a n‖ ^ 2 := by
  obtain ⟨𝒯, hmem, hsum⟩ := exists_charFibre ℰ
  rw [← hsum (fun χ t => ‖dpolyChi q s a χ t‖ ^ 2)]
  refine hybrid_wellspaced_l2_family q s hs a hT 𝒯 (fun χ => ?_) (fun χ t ht => ?_)
  · intro t ht u hu htu
    exact hws (χ, t) ((hmem χ t).1 ht) (χ, u) ((hmem χ u).1 hu) rfl htu
  · exact hsub (χ, t) ((hmem χ t).1 ht)

/-! ## D2 — the hybrid large-value count (KMT Lemma 6.5) -/

/-- The `χ`-twisted coefficient sequence `n ↦ aₙ·χ(n)`.  It is the whole content of the
`χ`-twist: `dpolyChi q (Icc 1 N) a χ = dpoly N (coeffChiTwist q χ a)`. -/
noncomputable def coeffChiTwist (q : ℕ) (χ : DirichletCharacter ℂ q) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * χ (n : ZMod q)

/-- On a full initial segment the `χ`-polynomial is an ordinary Dirichlet polynomial with
twisted coefficients. -/
lemma dpolyChi_Icc (q : ℕ) (N : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t : ℝ) :
    dpolyChi q (Finset.Icc 1 N) a χ t = dpoly N (coeffChiTwist q χ a) t := rfl

/-- `‖coeffChiTwist q χ a n‖ ≤ ‖a n‖` — the twist is by a value of modulus `≤ 1`. -/
lemma norm_coeffChiTwist_le (q : ℕ) (χ : DirichletCharacter ℂ q) (a : ℕ → ℂ) (n : ℕ) :
    ‖coeffChiTwist q χ a n‖ ≤ ‖a n‖ := by
  rw [coeffChiTwist, norm_mul]
  have h := DirichletCharacter.norm_le_one χ (n : ZMod q)
  nlinarith [norm_nonneg (a n), norm_nonneg (χ (n : ZMod q))]

/-- **Complete multiplicativity distributes over the `k`-fold convolution.**  The `k`-th
power of the `χ`-twisted polynomial has coefficients `(c^{*k})ₙ·χ(n)`: the twist commutes
with `kconv`.  This is why the whole `kconv` combinatorial core (support floor, `ω`-count,
the `k!` sup bound, the `L¹`/`L²` masses) is *character-free* and reused verbatim. -/
lemma kconv_coeffChiTwist (q : ℕ) (χ : DirichletCharacter ℂ q) (N : ℕ) (c : ℕ → ℂ) :
    ∀ (k n : ℕ), kconv N (coeffChiTwist q χ c) k n = kconv N c k n * χ (n : ZMod q) := by
  intro k
  induction k with
  | zero =>
      intro n
      by_cases h : n = 1
      · subst h
        rw [kconv, kconv]
        simp
      · rw [kconv, kconv]
        simp [h]
  | succ k ih =>
      intro n
      rw [kconv, kconv, dconv, dconv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hprod : p.1 * p.2 = n := (Finset.mem_filter.1 hp).2
      rw [ih p.2, coeffChiTwist, ← hprod]
      have hcast : (((p.1 * p.2 : ℕ)) : ZMod q) = (p.1 : ZMod q) * (p.2 : ZMod q) := by
        push_cast; ring
      rw [hcast, map_mul]
      ring

/-- **The `k`-th power step at the `χ`-polynomial.**  `‖P_χ(t)‖^{2k}` is the mean square of
the `χ`-polynomial of the `k`-fold convolution — the object D1 is fed. -/
lemma norm_dpolyChi_pow (q : ℕ) (N k : ℕ) (c : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖dpolyChi q (Finset.Icc 1 N) c χ t‖ ^ (2 * k)
      = ‖dpolyChi q (Finset.Icc 1 (N ^ k)) (kconv N c k) χ t‖ ^ 2 := by
  rw [dpolyChi_Icc, dpolyChi_Icc]
  have hcoeff : kconv N (coeffChiTwist q χ c) k = coeffChiTwist q χ (kconv N c k) :=
    funext (fun n => by rw [kconv_coeffChiTwist q χ N c k n, coeffChiTwist])
  have h1 : ‖dpoly N (coeffChiTwist q χ c) t‖ ^ (2 * k)
      = ‖dpoly (N ^ k) (kconv N (coeffChiTwist q χ c) k) t‖ ^ 2 := by
    rw [← dpoly_pow, norm_pow, ← pow_mul, mul_comm]
  rw [h1, hcoeff]

/-- **The card lower bound at the `(χ,t)`-set.**  If `V⁻¹ ≤ ‖P_χ(t)‖` on all of `ℰ`, the
`2k`-th power moment over `ℰ` is at least `|ℰ|·V^{−2k}`. -/
lemma card_mul_pow_le_hybrid (q : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) (k : ℕ) (V : ℝ)
    (hV : 0 < V) (ℰ : Finset (DirichletCharacter ℂ q × ℝ))
    (hlb : ∀ p ∈ ℰ, V⁻¹ ≤ ‖dpolyChi q s c p.1 p.2‖) :
    (ℰ.card : ℝ) * (V⁻¹) ^ (2 * k)
      ≤ ∑ p ∈ ℰ, ‖dpolyChi q s c p.1 p.2‖ ^ (2 * k) := by
  have h := Finset.card_nsmul_le_sum ℰ (fun p => ‖dpolyChi q s c p.1 p.2‖ ^ (2 * k))
    ((V⁻¹) ^ (2 * k))
    (fun p hp => pow_le_pow_left₀ (by positivity) (hlb p hp) (2 * k))
  simpa [nsmul_eq_mul] using h

/-- **D2, the algebraic spine.**  The amplification inequality at the `(χ,t)`-set: `k`-th
power (`norm_dpolyChi_pow`) into D1 (`hybrid_wellspaced_l2`), with the coefficient inputs
`kconv_l2_le_window` / `csum_window_le` from the landed file (character-free).  The
transcendental packaging (`pow_V_le`, `pack_exp_le` at `qT`) is the next step. -/
theorem hybrid_large_value_count_combined (q : ℕ) [NeZero q] (P : ℕ) (c : ℕ → ℂ)
    {T : ℝ} (hT : 0 ≤ T) (V : ℝ) (hV : 0 < V) (hP : 1 ≤ P)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ p ∈ ℰ, p.2 ∈ Set.Icc (-T) T)
    (hsupp : ∀ m, c m ≠ 0 → m.Prime ∧ P ≤ m)
    (hcoeff : ∀ m, c m ≠ 0 → ‖c m‖ ≤ (m : ℝ)⁻¹) (k : ℕ)
    (hlb : ∀ p ∈ ℰ, V⁻¹ ≤ ‖dpolyChi q (Finset.Icc 1 (2 * P)) c p.1 p.2‖) :
    (ℰ.card : ℝ) * (V⁻¹) ^ (2 * k)
      ≤ 84 * ((q.totient : ℝ) * (T + 1)
            + (q.totient : ℝ) * (((2 * P) ^ k : ℕ) : ℝ) / q)
          * Real.log (2 * (((2 * P) ^ k : ℕ) : ℝ))
          * ((Nat.factorial k : ℝ) / (P : ℝ) ^ k * 2 ^ k) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hφnn : (0 : ℝ) ≤ (q.totient : ℝ) := by positivity
  set X := (((2 * P) ^ k : ℕ) : ℝ) with hXdef
  have hXge : (1 : ℝ) ≤ X := by
    have h0 : (1 : ℕ) ≤ (2 * P) ^ k := Nat.one_le_pow _ _ (by omega)
    rw [hXdef]; exact_mod_cast h0
  -- the power step onto the k-fold convolution, then D1
  have hpow : (∑ p ∈ ℰ, ‖dpolyChi q (Finset.Icc 1 (2 * P)) c p.1 p.2‖ ^ (2 * k))
      = ∑ p ∈ ℰ,
          ‖dpolyChi q (Finset.Icc 1 ((2 * P) ^ k)) (kconv (2 * P) c k) p.1 p.2‖ ^ 2 :=
    Finset.sum_congr rfl fun p _ => norm_dpolyChi_pow q (2 * P) k c p.1 p.2
  have hD1 := hybrid_wellspaced_l2 (N := (2 * P) ^ k) q (Finset.Icc 1 ((2 * P) ^ k))
    (Finset.Subset.refl _) (kconv (2 * P) c k) hT ℰ hws hsub
  -- the coefficient side: the coprime-filtered mass is at most the full L² mass
  have hmass : (∑ n ∈ (Finset.Icc 1 ((2 * P) ^ k)).filter (fun n => Nat.Coprime n q),
        ‖kconv (2 * P) c k n‖ ^ 2)
      ≤ (Nat.factorial k : ℝ) / (P : ℝ) ^ k * 2 ^ k := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => by positivity)) ?_
    refine le_trans (kconv_l2_le_window (2 * P) P c hP hsupp hcoeff k) ?_
    have hfacnn : (0 : ℝ) ≤ (Nat.factorial k : ℝ) / (P : ℝ) ^ k := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hfacnn
    have hcsum := csum_window_le P c hP hsupp hcoeff
    have hcsum_nn : (0 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 (2 * P), ‖c m‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    exact pow_le_pow_left₀ hcsum_nn hcsum k
  have hpre_nn : (0 : ℝ) ≤ 84 * ((q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * X / q)
      * Real.log (2 * X) := by
    have hb : (0 : ℝ) ≤ (q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * X / q := by
      have h1 : (0 : ℝ) ≤ (q.totient : ℝ) * (T + 1) := by positivity
      have h2 : (0 : ℝ) ≤ (q.totient : ℝ) * X / q := by
        rw [hXdef]; positivity
      linarith
    have hlog : (0 : ℝ) ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
    exact mul_nonneg (mul_nonneg (by norm_num) hb) hlog
  calc (ℰ.card : ℝ) * (V⁻¹) ^ (2 * k)
      ≤ ∑ p ∈ ℰ, ‖dpolyChi q (Finset.Icc 1 (2 * P)) c p.1 p.2‖ ^ (2 * k) :=
        card_mul_pow_le_hybrid q (Finset.Icc 1 (2 * P)) c k V hV ℰ hlb
    _ = ∑ p ∈ ℰ,
          ‖dpolyChi q (Finset.Icc 1 ((2 * P) ^ k)) (kconv (2 * P) c k) p.1 p.2‖ ^ 2 := hpow
    _ ≤ 84 * ((q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * X / q) * Real.log (2 * X)
          * ∑ n ∈ (Finset.Icc 1 ((2 * P) ^ k)).filter (fun n => Nat.Coprime n q),
              ‖kconv (2 * P) c k n‖ ^ 2 := hD1
    _ ≤ 84 * ((q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * X / q) * Real.log (2 * X)
          * ((Nat.factorial k : ℝ) / (P : ℝ) ^ k * 2 ^ k) :=
        mul_le_mul_of_nonneg_left hmass hpre_nn

/-- **D2 — THE HYBRID LARGE-VALUE COUNT (KMT Lemma 6.5).**  For `c` supported on primes in
`[P, 2P]` with `‖c_m‖ ≤ 1/m` (CATCH #A: `c_p = a_p/p` pre-folded, the corpus's `σ = 1`
convention), and a per-fibre well-spaced `(χ,t)`-set `ℰ` with ordinates in `[−T, T]` on
which `V⁻¹ ≤ ‖∑_{P≤p≤2P} c_p χ(p) p^{it}‖`:

`|ℰ| ≤ 1680·(qT)^{2 log V/log P}·V²·exp(2·(log qT/log P)·loglog qT)`.

The landed `large_value_count` is the `q = 1` corner; the `T → qT` rewrite is exactly what
the hybrid mean value delivers (the `q` enters only through the two `log(qT)` scales).
Assembled from `hybrid_large_value_count_combined` (the algebraic spine at
`k = ⌈log qT/log P⌉`), `pow_V_le` (the `V^{2k}` leg) and `pack_exp_le` (the exp leg) — the
last two are pure real analysis, reused unchanged at the argument `qT`.  The constant
`1680 = 2·840`, the `2` paying for the bracket domination
`φ(q)(T+1) + φ(q)(2P)^k/q ≤ 2·(qT + (2P)^k)`.

Thresholds (the landed original's shapes, at `qT` where forced): `3 ≤ P`, `1 ≤ T`,
`1 < qT`, `P ≤ qT`, `1 ≤ V`, `log qT/log P ≥ 30`, `loglog qT ≥ 5`.  CATCH #B: a caller
holding `|P_χ(1−it)| ≥ V⁻¹` applies this at the negated ordinate set, of the same
cardinality. -/
theorem hybrid_large_value_count (q : ℕ) [NeZero q] (P : ℕ) (c : ℕ → ℂ) (T V : ℝ)
    (hP3 : 3 ≤ P) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T) (hPqT : (P : ℝ) ≤ (q : ℝ) * T)
    (hV : 1 ≤ V) (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log P)
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ p ∈ ℰ, p.2 ∈ Set.Icc (-T) T)
    (hsupp : ∀ m, c m ≠ 0 → m.Prime ∧ P ≤ m)
    (hcoeff : ∀ m, c m ≠ 0 → ‖c m‖ ≤ (m : ℝ)⁻¹)
    (hlb : ∀ p ∈ ℰ, V⁻¹ ≤ ‖dpolyChi q (Finset.Icc 1 (2 * P)) c p.1 p.2‖) :
    (ℰ.card : ℝ)
      ≤ 1680 * ((q : ℝ) * T) ^ (2 * Real.log V / Real.log P) * V ^ 2
          * Real.exp (2 * (Real.log ((q : ℝ) * T) / Real.log P)
              * Real.log (Real.log ((q : ℝ) * T))) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hVpos : (0 : ℝ) < V := by linarith
  have hP1 : 1 ≤ P := by omega
  have hPpos : (0 : ℝ) < P := by
    have : (3 : ℝ) ≤ P := by exact_mod_cast hP3
    linarith
  have hlogP1 : 1 ≤ Real.log P := by
    have h1 : Real.exp 1 < (P : ℝ) := by
      have h2 := Real.exp_one_lt_d9
      have h3 : (3 : ℝ) ≤ P := by exact_mod_cast hP3
      linarith
    have := Real.log_lt_log (Real.exp_pos 1) h1
    rw [Real.log_exp] at this; linarith
  have hlogPpos : 0 < Real.log P := by linarith
  set S := (q : ℝ) * T with hSdef
  have hSpos : (0 : ℝ) < S := by rw [hSdef]; linarith
  have hlogS0 : 0 < Real.log S := Real.log_pos hqT
  set k := ⌈Real.log S / Real.log P⌉₊ with hkdef
  have hκlek : Real.log S / Real.log P ≤ (k : ℝ) := Nat.le_ceil _
  have hkub : (k : ℝ) ≤ Real.log S / Real.log P + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ Real.log S / Real.log P))
  have hk1 : 1 ≤ k := by
    have h30 : (30 : ℝ) ≤ (k : ℝ) := le_trans hκ30 hκlek
    have : (1 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  set X := (((2 * P) ^ k : ℕ) : ℝ) with hXdef
  have hXge : (1 : ℝ) ≤ X := by
    have h0 : (1 : ℕ) ≤ (2 * P) ^ k := Nat.one_le_pow _ _ (by omega)
    rw [hXdef]; exact_mod_cast h0
  -- the domination premise `S ≤ (2P)^k`
  have hSk : S ≤ X := by
    have hκlogP : Real.log S / Real.log P * Real.log P = Real.log S :=
      div_mul_cancel₀ _ (ne_of_gt hlogPpos)
    have hstep : Real.log S ≤ (k : ℝ) * Real.log P := by
      have h := mul_le_mul_of_nonneg_right hκlek (le_of_lt hlogPpos)
      rwa [hκlogP] at h
    have hlogle : Real.log S ≤ Real.log X := by
      have hcast : X = ((2 : ℝ) * P) ^ k := by rw [hXdef]; push_cast; ring
      have hle2P : Real.log P ≤ Real.log (2 * (P : ℝ)) := Real.log_le_log hPpos (by linarith)
      have h1 : (k : ℝ) * Real.log P ≤ Real.log X := by
        rw [hcast, Real.log_pow]
        exact mul_le_mul_of_nonneg_left hle2P (le_of_lt hkpos)
      linarith
    calc S = Real.exp (Real.log S) := (Real.exp_log hSpos).symm
      _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr hlogle
      _ = X := Real.exp_log (by linarith)
  -- the spine, the bracket domination, the two transcendental legs
  have hcomb :=
    hybrid_large_value_count_combined q P c hT0 V hVpos hP1 ℰ hws hsub hsupp hcoeff k hlb
  have hpack :=
    pack_exp_le P S hP3 hqT hlogP1 hPqT hκ30 hLL5 k hk1 hkub (by rw [← hXdef]; exact hSk)
  have hpowV := pow_V_le V S P hV hSpos hlogPpos k (by linarith)
  set L := Real.log (2 * X) with hLdef
  set W := (Nat.factorial k : ℝ) / (P : ℝ) ^ k * 2 ^ k with hWdef
  have hLnn : (0 : ℝ) ≤ L := by rw [hLdef]; exact Real.log_nonneg (by linarith)
  have hWnn : (0 : ℝ) ≤ W := by rw [hWdef]; positivity
  -- `φ(q)(T+1) + φ(q)X/q ≤ 2(S + X)`
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφnn : (0 : ℝ) ≤ (q.totient : ℝ) := by positivity
  have hbracket : (q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * X / q ≤ 2 * (S + X) := by
    have h1 : (q.totient : ℝ) * (T + 1) ≤ 2 * S := by
      have hTT : T + 1 ≤ 2 * T := by linarith
      calc (q.totient : ℝ) * (T + 1) ≤ (q : ℝ) * (T + 1) :=
            mul_le_mul_of_nonneg_right hφq (by linarith)
        _ ≤ (q : ℝ) * (2 * T) := mul_le_mul_of_nonneg_left hTT hqr.le
        _ = 2 * S := by rw [hSdef]; ring
    have h2 : (q.totient : ℝ) * X / q ≤ X := by
      rw [div_le_iff₀ hqr]
      calc (q.totient : ℝ) * X ≤ (q : ℝ) * X :=
            mul_le_mul_of_nonneg_right hφq (by linarith)
        _ = X * q := by ring
    linarith
  have hcomb2 : (ℰ.card : ℝ) * (V⁻¹) ^ (2 * k) ≤ 2 * (84 * (S + X) * L * W) := by
    refine le_trans hcomb ?_
    have hstep : 84 * ((q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * X / q) * L * W
        ≤ 84 * (2 * (S + X)) * L * W := by
      have hLW : (0 : ℝ) ≤ L * W := mul_nonneg hLnn hWnn
      nlinarith [hbracket, hLW]
    calc 84 * ((q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * X / q) * L * W
        ≤ 84 * (2 * (S + X)) * L * W := hstep
      _ = 2 * (84 * (S + X) * L * W) := by ring
  -- close
  have hBnn : (0 : ℝ) ≤ 84 * (S + X) * L * W := by
    have h1 : (0 : ℝ) ≤ S + X := by linarith
    positivity
  have hVk : (0 : ℝ) < V ^ (2 * k) := by positivity
  rw [inv_pow, ← div_eq_mul_inv] at hcomb2
  have hcard : (ℰ.card : ℝ) ≤ 2 * (84 * (S + X) * L * W) * V ^ (2 * k) :=
    (div_le_iff₀ hVk).mp hcomb2
  have hVTnn : (0 : ℝ) ≤ V ^ 2 * S ^ (2 * Real.log V / Real.log P) := by positivity
  have h2Bnn : (0 : ℝ) ≤ 2 * (84 * (S + X) * L * W) := by linarith
  calc (ℰ.card : ℝ)
      ≤ 2 * (84 * (S + X) * L * W) * V ^ (2 * k) := hcard
    _ ≤ 2 * (84 * (S + X) * L * W) * (V ^ 2 * S ^ (2 * Real.log V / Real.log P)) :=
        mul_le_mul_of_nonneg_left hpowV h2Bnn
    _ ≤ 2 * (840 * Real.exp (2 * (Real.log S / Real.log P) * Real.log (Real.log S)))
          * (V ^ 2 * S ^ (2 * Real.log V / Real.log P)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hVTnn
        rw [hLdef, hWdef, hXdef]
        exact hpack
    _ = 1680 * S ^ (2 * Real.log V / Real.log P) * V ^ 2
          * Real.exp (2 * (Real.log S / Real.log P) * Real.log (Real.log S)) := by ring

end Salt.MR
