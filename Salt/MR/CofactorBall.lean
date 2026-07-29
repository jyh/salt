/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CofactorDist
import Salt.MR.CenterSupply
import Salt.MR.RamRAdapter

/-!
# CofactorBall — CASE B of the co-factor dichotomy (U7-D)

The `⟦V5⟧` ladder's **U7-D** (`docs/exploration/hsup-design.md`): the *pretentious-pocket*
arm of the U-7 dichotomy.  Here the damped co-factor datum `ℓ(g_x)` HAS a pocket — a
frequency `t₁*` where its pretentious distance sits below the A.4 floor — and the CASE-A
`c`-generic grade machinery is **not needed at all**.

## The mathematics, in one paragraph

U7-C's collision lemma (`CofactorDist.pocket_collision_window`) says the pocket cannot hide:
under the row's own cap `𝔻²(ℓ g, p^{it₁}; X) ≤ (1/16)loglog X` and the pocket's
`𝔻²(ℓ g_x, p^{it₁*}; X) ≤ (1/32 − θ)loglog X`, the two centres **collide**,
`|t₁* − t₁| < 1`.  So on the row's FAR leg `|t − t₁| ≥ seamRad X` every frequency is at
distance `> seamRad X − 1` from the pocket centre (`pocket_far_from_ball`), i.e. at LARGE
radius.  The landed GS 7.1 transfer (`BallSup.transfer_at_scale`) prices the twisted partial
sums at `√2/(1+|t−t₁*|)` times their value AT the pocket centre — and at the centre the
TRIVIAL bound `‖∑_{n≤k} f(n)n^{−it₁*}‖ ≤ k` (S₀ = 1, `center_trivial_bound`) already
suffices, because the transfer's own `1/(1+|t−t₁*|) ≤ 1/seamRad X = (log X)^{−1/46}` is
already `6×` better (in the exponent) than the `(log X)^{−ρ}`, `ρ = 3θ ≈ 1/98`, the row
needs.  **No Halász input, no `c`-generic grade, no window floor.**

## What is proved here

* **D-1** `center_trivial_bound` / `damped_partial_trivial` — the `S₀ = O(1)` input:
  `ball_sup_of_center`'s `hCenter` binder, discharged by the triangle inequality alone at
  the damped datum `ℓ(g_x)` (1-bounded by `gxDatum_norm_le_one` + `ellLin_norm_le_one`).
* **D-2** `far_transfer_sup` — the radius transfer, a CLONE (not a byte-reuse; see below) of
  `BallSup.ball_sup_of_center` at LARGE radius: the exit constant is
  `farSupS W Y Rmax R = 2√2/R + farErr W Y Rmax`, with the GS 7.1 error paid ADDITIVELY
  (`farErr`) rather than multiplied by the weight.
* **D-3** `caseB_ramR_bound` — the assembly: collision ∘ far-leg ∘ D-2 ∘ the `x`-integral
  interchange ∘ `RamRAdapter.ramR_abel_sup`, exiting in `USetThinTL.tL_main_sumsq`'s `Rbd`
  binder shape `‖ramR H N X P Q j (ellLin g) t‖ ≤ 3·farSupS …`.
* **D-4** `collisionGate_discharged` — U7-C's residual: the asymptotic page
  `∃ X₀, ∀ X ≥ X₀, collisionGate X 25 C`, with `X₀ = exp(exp(10⁶ + 75·C⁺))` STATED (law
  #253: the tower is in the open, never absorbed).

## THE D-2 FIT VERDICT: clone, not byte-reuse — and exactly why

`ball_sup_of_center` cannot be instantiated here, for two independent reasons, both
structural (Iron rule 1: neither landed statement is touched):

1. **The radius binder.**  `ball_sup_of_center` carries `|t − t₁| ≤ seamRad X` and pays the
   weight `1+|t−t₁| ≤ 1+seamRad X` ON THE ERROR (`ballSupS X S₀ = 2√2·S₀ + ballTail X·(1+
   seamRad X)`).  CASE B lives at `|t − t₁*| > seamRad X − 1` and needs the error paid at the
   AMBIENT radius `Rmax`, where multiplying by `1+Rmax` would destroy it.  Hence `farErr`,
   additive, and the exit `farSupS = 2√2/R + farErr`.
2. **The datum binder.**  `hDatum : ∀ n, X < n → a n = f n` is stated for ALL `n > X`, while
   the co-factor coefficient is supported in the closed WINDOW `[X_j, 2X_j] ∩ [1,N]` — it
   vanishes above `2X_j`, so the binder is false for our `a`.  `spolyA_window_split` is the
   windowed clone of `BallSup.spolyA_datum_split` (cut at a NATURAL `k₀`, which also disposes
   of the half-open endpoint convention: `k₀ < X_j ≤ k₀+1`).

Everything else IS byte-reused: `transfer_at_scale`, `ballErr`, `ballSupC`,
`SmallStones.sixteenth_loglog_le_SPartial_div_eight`, `CenterSupply.pretDistSq_twist_slot`
(the `hMball` twist-slot — ⟦V5⟧'s Z-2, already discharged upstream), `ramR_abel_sup`,
`ellLin_gxDatum`, `inv_blockOmega_succ_eq_integral`, and the three collision stones.

## THE `t`-CONVENTION

As in `RamRAdapter`: everything is at the SAME `t` that `ramR` is evaluated at, twist
`n^{−it}` (`spolyA`).  **No `dpoly`, no `−𝒯` flip, no ordinate-set negation appears in this
file.**  The only negations are inside `eIu (-t) n` — the corpus spelling of `n^{−it}` — and
inside `ramRbot`'s `exp(−j/H)`.

## Named hypotheses (each a real, recorded socket — none forced closed)

* `hMball`-shaped caps: supplied per-`x` at the POCKET centre, in the A.4 `(1/16)loglog`
  shape at the TRANSFER scale `k₀` (not the global scale `X`).  The scale descent
  `X ↝ X_j` is the consumer's (U7-F's) — it is a monotonicity of `pretDistSq` in the scale
  plus the `loglog X ↝ loglog X_j` numeral, and it is NOT performed here.
* `hend : 2/X_j ≤ S` — `ramR_abel_sup`'s half-open endpoint charge (free in the regime).
* `hMN : M ≤ N` — the sharp Abel length must fit inside the dyadic length.
* `hk₀lo/hk₀hi` — the window cut `k₀ < X_j ≤ k₀+1` (`exists_window_cut` constructs it).
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 (D-1) — the trivial partial sum at the pocket centre (`S₀ = 1`) -/

/-- **D-1, abstract.**  For a 1-bounded datum the twisted partial sum is bounded by the
length: `‖∑_{n≤k} f(n)·n^{−it₁}‖ ≤ 1·k`.  This is `BallSup.ball_sup_of_center`'s `hCenter`
binder at `S₀ = 1` — the CASE-B input, where no Halász bound is needed because the transfer's
own `1/(1+|t−t₁*|)` factor already carries the whole grade. -/
theorem center_trivial_bound {f : ℕ → ℂ} (hfle : ∀ n, ‖f n‖ ≤ 1) (t₁ : ℝ) (k : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 k, f n * eIu (-t₁) n‖ ≤ 1 * (k : ℝ) := by
  have hterm : ∀ n ∈ Finset.Icc 1 k, ‖f n * eIu (-t₁) n‖ ≤ 1 := by
    intro n _
    rw [norm_mul, norm_eIu, mul_one]
    exact hfle n
  calc ‖∑ n ∈ Finset.Icc 1 k, f n * eIu (-t₁) n‖
      ≤ ∑ n ∈ Finset.Icc 1 k, ‖f n * eIu (-t₁) n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 k, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = 1 * (k : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp

/-- **D-1 at the damped datum.**  The `x`-damped co-factor datum `ℓ(g_x)` is 1-bounded for
`x ∈ [0,1]` (`gxDatum_norm_le_one` ∘ `ellLin_norm_le_one`), so its twisted partial sums at
ANY centre `t₁'` obey the trivial bound.  Every constant here is `x`-FREE — this is the
uniformity that lets the `[0,1]` average be taken at the end (§4). -/
theorem damped_partial_trivial {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1)
    (P Q : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (t₁' : ℝ) (k : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 k, ellLin (gxDatum g P Q x) n * eIu (-t₁') n‖ ≤ 1 * (k : ℝ) :=
  center_trivial_bound
    (fun n => ellLin_norm_le_one _ (fun p hp => gxDatum_norm_le_one hx0 hx1 hg p hp) n) t₁' k

/-! ## §2 — the windowed datum split (the half-open endpoint, disposed of at a natural cut) -/

/-- **The windowed datum split.**  If `a` vanishes on `n ≤ k₀` and agrees with `f` on the
window `k₀ < n ≤ M`, then for `k₀ ≤ m ≤ M`

  `A_t(m) = F_t(m) − F_t(k₀)`,  `F_t(u) = ∑_{n≤u} f(n)n^{−it}`.

The windowed clone of `BallSup.spolyA_datum_split` (whose `hDatum` is stated for ALL `n > X`
— false for a co-factor coefficient, which is supported in `[X_j, 2X_j]`).  Cutting at a
NATURAL `k₀` also disposes of the half-open endpoint convention: `k₀` is the largest integer
strictly below the window bottom. -/
lemma spolyA_window_split {a f : ℕ → ℂ} {k₀ M : ℕ}
    (hsupp : ∀ n : ℕ, n ≤ k₀ → a n = 0)
    (hDatum : ∀ n : ℕ, k₀ < n → n ≤ M → a n = f n)
    (t : ℝ) {m : ℕ} (hkm : k₀ ≤ m) (hmM : m ≤ M) :
    spolyA a t m
      = (∑ n ∈ Finset.Icc 1 m, f n * eIu (-t) n)
        - ∑ n ∈ Finset.Icc 1 k₀, f n * eIu (-t) n := by
  classical
  have hAe : spolyA a t m = ∑ n ∈ Finset.Icc 1 m, a n * eIu (-t) n := by
    unfold spolyA
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    exact div_cpow_eq_eIu (a n) t (by omega)
  have hsub : Finset.Icc 1 k₀ ⊆ Finset.Icc 1 m := Finset.Icc_subset_Icc_right hkm
  have h1 : (∑ n ∈ Finset.Icc 1 m \ Finset.Icc 1 k₀, f n * eIu (-t) n)
      + ∑ n ∈ Finset.Icc 1 k₀, f n * eIu (-t) n
      = ∑ n ∈ Finset.Icc 1 m, f n * eIu (-t) n := Finset.sum_sdiff hsub
  have h2 : (∑ n ∈ Finset.Icc 1 m, a n * eIu (-t) n)
      = ∑ n ∈ Finset.Icc 1 m \ Finset.Icc 1 k₀, a n * eIu (-t) n := by
    refine (Finset.sum_subset Finset.sdiff_subset ?_).symm
    intro n hn hn'
    have hnk : n ∈ Finset.Icc 1 k₀ := by
      by_contra hc
      exact hn' (Finset.mem_sdiff.mpr ⟨hn, hc⟩)
    rw [hsupp n (Finset.mem_Icc.mp hnk).2, zero_mul]
  have h3 : (∑ n ∈ Finset.Icc 1 m \ Finset.Icc 1 k₀, a n * eIu (-t) n)
      = ∑ n ∈ Finset.Icc 1 m \ Finset.Icc 1 k₀, f n * eIu (-t) n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_sdiff.mp hn
    have hgt : k₀ < n := by
      by_contra hc
      exact hn2 (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn1).1, by omega⟩)
    rw [hDatum n hgt (le_trans (Finset.mem_Icc.mp hn1).2 hmM)]
  rw [hAe, h2, h3, ← h1]
  ring

/-! ## §3 (D-2) — THE RADIUS TRANSFER at large radius -/

/-- **The additively-paid GS 7.1 error.**  `farErr W Y Rmax` majorises the SUM of the two
transfer errors (at the two endpoints of the window `[W, Y]`), divided by the length: it is
`4·ballSupC·(1 + log(3 + Rmax·(1+log Y)))/√(log W)`, of grade
`(log W)^{−1/2}·log(Rmax·log Y)` — the `(log X)^{−1/2+o(1)}` second term of the frozen interface,
NEVER multiplied by the weight (that is the whole difference from `ballTail`, which CASE A
can afford and CASE B cannot). -/
noncomputable def farErr (W Y Rmax : ℝ) : ℝ :=
  4 * ballSupC * (1 + Real.log (3 + Rmax * (1 + Real.log Y))) / Real.sqrt (Real.log W)

/-- **The CASE-B exit constant.**  `farSupS W Y Rmax R = 2√2/R + farErr W Y Rmax`: the
trivial centre bound `S₀ = 1` transferred at radius `≥ R` (main term), plus the additive GS
7.1 error.  At the intended pin `R = seamRad X = (log X)^{1/46}` and `Rmax = T+1` this is
`(log X)^{−1/46} + (log X)^{−1/2}·log T`. -/
noncomputable def farSupS (W Y Rmax R : ℝ) : ℝ := 2 * Real.sqrt 2 / R + farErr W Y Rmax

/-- `log` of a natural cast is nonnegative — `log 0 = 0` in this library, so no `1 ≤ M`
hypothesis is ever needed for the window top. -/
lemma log_natCast_nonneg (M : ℕ) : 0 ≤ Real.log (M : ℝ) := by
  rcases Nat.eq_zero_or_pos M with rfl | h
  · simp
  · exact Real.log_nonneg (by exact_mod_cast h)

lemma farErr_nonneg {W Y Rmax : ℝ} (hY : 0 ≤ Real.log Y) (hRmax : 0 ≤ Rmax) :
    0 ≤ farErr W Y Rmax := by
  have h1 : (1 : ℝ) ≤ 3 + Rmax * (1 + Real.log Y) := by nlinarith
  have h2 : 0 ≤ Real.log (3 + Rmax * (1 + Real.log Y)) := Real.log_nonneg h1
  have h3 := ballSupC_pos
  unfold farErr
  positivity

lemma farSupS_nonneg {W Y Rmax R : ℝ} (hR : 0 < R) (hY : 0 ≤ Real.log Y) (hRmax : 0 ≤ Rmax) :
    0 ≤ farSupS W Y Rmax R := by
  have h1 := farErr_nonneg (W := W) hY hRmax
  have h2 : (0 : ℝ) ≤ 2 * Real.sqrt 2 / R := by positivity
  unfold farSupS
  linarith

/-- **D-2 — THE RADIUS TRANSFER.**  A window datum `a` (supported in `(k₀, M]`, where it
agrees with a 1-bounded multiplicative `f`) whose centre `t₁'` satisfies the A.4 ball
hypothesis on the whole window has its twisted partial sums bounded by

  `‖A_t(m)‖ ≤ farSupS k₀ M Rmax R · m`   for all `m ≤ M`,

whenever `R ≤ 1 + |t − t₁'| ` and `|t − t₁'| ≤ Rmax`.  **The centre input is the TRIVIAL
bound** (`center_trivial_bound`, `S₀ = 1`): CASE B needs no Halász estimate.

`hMk : M ≤ 2k₀` is the dyadic width of the window (`M ≤ 2(X_j−1) ≤ 2k₀`); it is what turns
the two endpoint errors, each `≤ ballSupC·M·L/√(log k₀)`, into `farErr·m`. -/
theorem far_transfer_sup {M k₀ : ℕ} {a f : ℕ → ℂ} {t t₁' Rmax R : ℝ}
    (hk₀ : 3 ≤ k₀) (hMk : (M : ℝ) ≤ 2 * (k₀ : ℝ))
    (hf1 : f 1 = 1) (hfmul : ∀ p q : ℕ, Nat.Coprime p q → f (p * q) = f p * f q)
    (hfle : ∀ n, ‖f n‖ ≤ 1)
    (hsupp : ∀ n : ℕ, n ≤ k₀ → a n = 0)
    (hDatum : ∀ n : ℕ, k₀ < n → n ≤ M → a n = f n)
    (hMball : ∀ y : ℝ, (k₀ : ℝ) ≤ y → y ≤ (M : ℝ) →
      pretDistSq (fun n => f n * eIu (-t₁') n) (fun _ => 1) y
        ≤ Salt.Mertens.SPartial y / 8)
    (hR0 : 0 < R) (hRle : R ≤ 1 + |t - t₁'|) (hRmax : |t - t₁'| ≤ Rmax) :
    ∀ m : ℕ, m ≤ M → ‖spolyA a t m‖ ≤ farSupS (k₀ : ℝ) (M : ℝ) Rmax R * (m : ℝ) := by
  intro m hm
  have hk₀R : (3 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
  have hr0 : (0 : ℝ) ≤ |t - t₁'| := abs_nonneg _
  have hRmax0 : (0 : ℝ) ≤ Rmax := le_trans hr0 hRmax
  have hMR : (0 : ℝ) ≤ Real.log (M : ℝ) := log_natCast_nonneg M
  have hSnn : 0 ≤ farSupS (k₀ : ℝ) (M : ℝ) Rmax R := farSupS_nonneg hR0 hMR hRmax0
  rcases le_or_gt m k₀ with hcase | hcase
  · -- below the window the polynomial is empty
    have hz : spolyA a t m = 0 := by
      unfold spolyA
      refine Finset.sum_eq_zero fun n hn => ?_
      have hnm : n ≤ m := (Finset.mem_Icc.mp hn).2
      rw [hsupp n (le_trans hnm hcase), zero_div]
    rw [hz, norm_zero]
    positivity
  · -- the live range `k₀ < m ≤ M ≤ 2k₀`
    have hkm : k₀ ≤ m := hcase.le
    have hmR : (k₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    have hmM : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm
    have hm3 : (3 : ℝ) ≤ (m : ℝ) := le_trans hk₀R hmR
    have hM2m : (M : ℝ) ≤ 2 * (m : ℝ) := le_trans hMk (by linarith)
    have hd : (0 : ℝ) < 1 + |t - t₁'| := by positivity
    -- the two logs
    have hlogk : (0 : ℝ) < Real.log (k₀ : ℝ) := Real.log_pos (by linarith)
    have hsk : (0 : ℝ) < Real.sqrt (Real.log (k₀ : ℝ)) := Real.sqrt_pos.mpr hlogk
    -- the datum split
    have hsplit := spolyA_window_split hsupp hDatum t hkm hm
    -- the transfer at scale `m`
    have hAm : ‖∑ n ∈ Finset.Icc 1 m, f n * eIu (-t) n‖
        ≤ Real.sqrt 2 / (1 + |t - t₁'|) * (1 * (m : ℝ)) + ballErr (m : ℝ) |t - t₁'| := by
      have h := transfer_at_scale hf1 hfmul hfle (t := t) (t₁ := t₁') (x := (m : ℝ)) hm3
        (hMball (m : ℝ) hmR hmM)
      rw [Nat.floor_natCast] at h
      refine h.trans ?_
      have hq : (0 : ℝ) ≤ Real.sqrt 2 / (1 + |t - t₁'|) := by positivity
      have := mul_le_mul_of_nonneg_left (center_trivial_bound hfle t₁' m) hq
      linarith
    -- the transfer at scale `k₀`
    have hAk : ‖∑ n ∈ Finset.Icc 1 k₀, f n * eIu (-t) n‖
        ≤ Real.sqrt 2 / (1 + |t - t₁'|) * (1 * (m : ℝ)) + ballErr (k₀ : ℝ) |t - t₁'| := by
      have h := transfer_at_scale hf1 hfmul hfle (t := t) (t₁ := t₁') (x := (k₀ : ℝ)) hk₀R
        (hMball (k₀ : ℝ) le_rfl (le_trans hmR hmM))
      rw [Nat.floor_natCast] at h
      refine h.trans ?_
      have hq : (0 : ℝ) ≤ Real.sqrt 2 / (1 + |t - t₁'|) := by positivity
      have hc := center_trivial_bound hfle t₁' k₀
      have hmono : 1 * (k₀ : ℝ) ≤ 1 * (m : ℝ) := by linarith
      have := mul_le_mul_of_nonneg_left (le_trans hc hmono) hq
      linarith
    -- the error majorant, uniform on the window
    have herr : ∀ y : ℝ, (k₀ : ℝ) ≤ y → y ≤ (M : ℝ) →
        ballErr y |t - t₁'|
          ≤ ballSupC * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))))
              / Real.sqrt (Real.log (k₀ : ℝ)) * (M : ℝ) := by
      intro y hy1 hy2
      have hy0 : (0 : ℝ) < y := by linarith
      have hlogy : (0 : ℝ) < Real.log y := lt_of_lt_of_le hlogk (Real.log_le_log (by linarith) hy1)
      have hsy : Real.sqrt (Real.log (k₀ : ℝ)) ≤ Real.sqrt (Real.log y) :=
        Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hy1)
      have hlogM : Real.log y ≤ Real.log (M : ℝ) := Real.log_le_log hy0 hy2
      -- (i) the `y/√(log y)` factor
      have hq : y / Real.sqrt (Real.log y) ≤ (M : ℝ) / Real.sqrt (Real.log (k₀ : ℝ)) := by
        rw [div_le_div_iff₀ (lt_of_lt_of_le hsk hsy) hsk]
        have ha : y * Real.sqrt (Real.log (k₀ : ℝ)) ≤ (M : ℝ) * Real.sqrt (Real.log (k₀ : ℝ)) :=
          mul_le_mul_of_nonneg_right hy2 hsk.le
        have hb : (M : ℝ) * Real.sqrt (Real.log (k₀ : ℝ)) ≤ (M : ℝ) * Real.sqrt (Real.log y) :=
          mul_le_mul_of_nonneg_left hsy (by linarith)
        linarith
      -- (ii) the log factor
      have hprod0 : (0 : ℝ) ≤ |t - t₁'| * (1 + Real.log y) :=
        mul_nonneg hr0 (by linarith)
      have hin1 : (0 : ℝ) < 3 + |t - t₁'| * (1 + Real.log y) := by linarith
      have hin2 : 3 + |t - t₁'| * (1 + Real.log y)
          ≤ 3 + Rmax * (1 + Real.log (M : ℝ)) := by
        have := mul_le_mul hRmax (by linarith : 1 + Real.log y ≤ 1 + Real.log (M : ℝ))
          (by linarith) hRmax0
        linarith
      have hlogfac : 1 + Real.log (3 + |t - t₁'| * (1 + Real.log y))
          ≤ 1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))) := by
        have := Real.log_le_log hin1 hin2
        linarith
      have hnn1 : (0 : ℝ) ≤ 1 + Real.log (3 + |t - t₁'| * (1 + Real.log y)) := by
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 3 + |t - t₁'| * (1 + Real.log y))
        linarith
      have hq0 : (0 : ℝ) ≤ y / Real.sqrt (Real.log y) := by positivity
      have hC := ballSupC_pos
      calc ballErr y |t - t₁'|
          = ballSupC * (y / Real.sqrt (Real.log y))
              * (1 + Real.log (3 + |t - t₁'| * (1 + Real.log y))) := rfl
        _ ≤ ballSupC * ((M : ℝ) / Real.sqrt (Real.log (k₀ : ℝ)))
              * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ)))) := by gcongr
        _ = ballSupC * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))))
              / Real.sqrt (Real.log (k₀ : ℝ)) * (M : ℝ) := by ring
    -- assemble
    have hEm := herr (m : ℝ) hmR hmM
    have hEk := herr (k₀ : ℝ) le_rfl (le_trans hmR hmM)
    have hnorm : ‖spolyA a t m‖
        ≤ ‖∑ n ∈ Finset.Icc 1 m, f n * eIu (-t) n‖
          + ‖∑ n ∈ Finset.Icc 1 k₀, f n * eIu (-t) n‖ := by
      rw [hsplit]
      exact norm_sub_le _ _
    -- the main term: `1/(1+|t−t₁'|) ≤ 1/R`
    have hwt : Real.sqrt 2 / (1 + |t - t₁'|) ≤ Real.sqrt 2 / R := by
      have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      exact div_le_div_of_nonneg_left h2 hR0 hRle
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := by linarith
    have hmain : Real.sqrt 2 / (1 + |t - t₁'|) * (1 * (m : ℝ))
        ≤ Real.sqrt 2 / R * (m : ℝ) := by
      have := mul_le_mul_of_nonneg_right hwt hmnn
      linarith
    -- the error term: `M ≤ 2m`
    have hAnn : (0 : ℝ) ≤ ballSupC * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))))
        / Real.sqrt (Real.log (k₀ : ℝ)) := by
      have hC := ballSupC_pos
      have h1 : (1 : ℝ) ≤ 3 + Rmax * (1 + Real.log (M : ℝ)) := by nlinarith
      have := Real.log_nonneg h1
      positivity
    have herr2 : ballSupC * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))))
          / Real.sqrt (Real.log (k₀ : ℝ)) * (M : ℝ)
        ≤ ballSupC * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))))
          / Real.sqrt (Real.log (k₀ : ℝ)) * (2 * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hM2m hAnn
    have hexp : farSupS (k₀ : ℝ) (M : ℝ) Rmax R * (m : ℝ)
        = 2 * (Real.sqrt 2 / R * (m : ℝ))
          + 2 * (ballSupC * (1 + Real.log (3 + Rmax * (1 + Real.log (M : ℝ))))
              / Real.sqrt (Real.log (k₀ : ℝ)) * (2 * (m : ℝ))) := by
      unfold farSupS farErr
      ring
    linarith

/-! ## §4 — the `[0,1]` interchange, at the PARTIAL-SUM level

`RamWeight.ramR_eq_integral_damp` averages the Ramaré weight at the level of the whole
polynomial.  The Abel page (`RamRAdapter.ramR_abel_sup`, which owns the half-open endpoint
charge) wants the average one level down — at `spolyA (ramRcoeff …)`.  Same one-line
mechanism (`inv_blockOmega_succ_eq_integral` under a finite sum), so the LANDED
`ramR_abel_sup` is reused verbatim instead of being re-proved for the damped coefficient. -/

/-- The `x`-damped co-factor coefficient: `ramRcoeff` with the Ramaré weight `(ω+1)⁻¹`
replaced by the multiplicative monomial `x^ω` (the coefficient of `RamWeight.ramRdamp`). -/
noncomputable def ramRdampCoeff (H : ℝ) (N X P Q j : ℕ) (b : ℕ → ℂ) (x : ℝ) (m : ℕ) : ℂ :=
  if m ∈ ramRrange H N X j then b m * ((x : ℝ) : ℂ) ^ blockOmega P Q m else 0

lemma ramRdampCoeff_eq_mask (H : ℝ) (N X P Q j : ℕ) (b : ℕ → ℂ) (x : ℝ) (m : ℕ) :
    ramRdampCoeff H N X P Q j b x m
      = (if m ∈ ramRrange H N X j then b m else 0) * ((x : ℝ) : ℂ) ^ blockOmega P Q m := by
  unfold ramRdampCoeff
  split_ifs with h
  · rfl
  · rw [zero_mul]

lemma ramRcoeff_eq_mask (H : ℝ) (N X P Q j : ℕ) (b : ℕ → ℂ) (m : ℕ) :
    ramRcoeff H N X P Q j b m
      = (if m ∈ ramRrange H N X j then b m else 0) * ((blockOmega P Q m : ℂ) + 1)⁻¹ := by
  unfold ramRcoeff
  split_ifs with h
  · rfl
  · rw [zero_mul]

/-- **THE INTERCHANGE at the partial sums.**  `A_t(m)` of the Ramaré-weighted coefficient is
the `[0,1]` average of `A_t(m)` of the damped ones. -/
lemma spolyA_ramRcoeff_eq_integral (H : ℝ) (N X P Q j : ℕ) (b : ℕ → ℂ) (t : ℝ) (m : ℕ) :
    spolyA (ramRcoeff H N X P Q j b) t m
      = ∫ x in (0:ℝ)..1, spolyA (ramRdampCoeff H N X P Q j b x) t m := by
  have hcont : ∀ n : ℕ, IntervalIntegrable
      (fun x : ℝ => ramRdampCoeff H N X P Q j b x n / (n : ℂ) ^ ((t : ℂ) * Complex.I))
      MeasureTheory.volume 0 1 := by
    intro n
    refine Continuous.intervalIntegrable ?_ _ _
    simp only [ramRdampCoeff_eq_mask]
    fun_prop
  calc spolyA (ramRcoeff H N X P Q j b) t m
      = ∑ n ∈ Finset.Icc 1 m,
          ∫ x in (0:ℝ)..1,
            ramRdampCoeff H N X P Q j b x n / (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
        unfold spolyA
        refine Finset.sum_congr rfl (fun n _ => ?_)
        simp only [ramRdampCoeff_eq_mask]
        rw [show (fun x : ℝ => (if n ∈ ramRrange H N X j then b n else 0)
              * ((x : ℝ) : ℂ) ^ blockOmega P Q n / (n : ℂ) ^ ((t : ℂ) * Complex.I))
            = fun x : ℝ => ((if n ∈ ramRrange H N X j then b n else 0)
              / (n : ℂ) ^ ((t : ℂ) * Complex.I)) * ((x : ℝ) : ℂ) ^ blockOmega P Q n from by
          funext x; ring]
        rw [intervalIntegral.integral_const_mul, integral_cpow_unit, ramRcoeff_eq_mask]
        ring
    _ = ∫ x in (0:ℝ)..1, spolyA (ramRdampCoeff H N X P Q j b x) t m := by
        unfold spolyA
        exact (intervalIntegral.integral_finsetSum (fun n _ => hcont n)).symm

/-- **THE `x`-UNIFORM EXIT.**  A bound on the damped partial sums that is uniform over
`x ∈ [0,1]` is a bound on the Ramaré-weighted partial sum — the shape `ramR_abel_sup`'s `hA`
binder wants.  (The `[0,1]` twin of `RamWeight.ramR_norm_le_of_damp_le`; the unit interval's
length is `1`, so no constant is paid.) -/
theorem spolyA_ramRcoeff_le_of_damp {H : ℝ} {N X P Q j m : ℕ} {b : ℕ → ℂ} {t B : ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖spolyA (ramRdampCoeff H N X P Q j b x) t m‖ ≤ B) :
    ‖spolyA (ramRcoeff H N X P Q j b) t m‖ ≤ B := by
  rw [spolyA_ramRcoeff_eq_integral]
  have hbd : ∀ x ∈ Set.uIoc (0 : ℝ) 1, ‖spolyA (ramRdampCoeff H N X P Q j b x) t m‖ ≤ B := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact h x ⟨hx.1.le, hx.2⟩
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd

/-! ## §5 — D-2 at the damped co-factor datum -/

/-- The damped co-factor coefficient IS the window-masked `ellLin` datum of `g_x`
(`ellLin_gxDatum`, the ⟦V5⟧ W2 absorption identity). -/
lemma ramRdampCoeff_ellLin (H : ℝ) (N X P Q j : ℕ) (g : ℕ → ℂ) (x : ℝ) (m : ℕ) :
    ramRdampCoeff H N X P Q j (ellLin g) x m
      = if m ∈ ramRrange H N X j then ellLin (gxDatum g P Q x) m else 0 := by
  unfold ramRdampCoeff
  split_ifs with h
  · rw [ellLin_gxDatum]
  · rfl

/-- The damped datum is multiplicative in `ball_sup_of_center`'s literal binder shape
(including the `0`-slot, which `ellLin_mul_coprime` does not cover). -/
lemma ellLin_mul_coprime_all (f : ℕ → ℂ) (p q : ℕ) (hco : Nat.Coprime p q) :
    ellLin f (p * q) = ellLin f p * ellLin f q := by
  rcases eq_or_ne p 0 with rfl | hp
  · have hq : q = 1 := by simpa [Nat.coprime_zero_left] using hco
    subst hq; simp [ellLin]
  rcases eq_or_ne q 0 with rfl | hq
  · have hp1 : p = 1 := by simpa [Nat.coprime_zero_right] using hco
    subst hp1; simp [ellLin]
  exact ellLin_mul_coprime f hp hq hco

/-- **D-2 at the damped co-factor datum.**  The radius transfer, instantiated at
`a = ramRdampCoeff …` and `f = ellLin (g_x)`: the window binders are discharged from the
cut `k₀ < X_j ≤ k₀+1` and `M ≤ min(N, 2X_j)`, the datum binders from
`gxDatum_norm_le_one`/`ellLin_gxDatum`, and the centre input is the TRIVIAL bound.

Every constant in the conclusion is `x`-FREE — that is what §4's average consumes. -/
theorem damped_partial_transfer {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1)
    {H : ℝ} {N Xn P Q j M k₀ : ℕ} {x t t₁' Rmax R : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hk₀ : 3 ≤ k₀) (hMN : M ≤ N)
    (hk₀lo : (k₀ : ℝ) < ramRbot H Xn j) (hk₀hi : ramRbot H Xn j ≤ (k₀ : ℝ) + 1)
    (hhigh : (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1))
    (hMball : ∀ y : ℝ, (k₀ : ℝ) ≤ y → y ≤ (M : ℝ) →
      pretDistSq (fun n => ellLin (gxDatum g P Q x) n * eIu (-t₁') n) (fun _ => 1) y
        ≤ Salt.Mertens.SPartial y / 8)
    (hR0 : 0 < R) (hRle : R ≤ 1 + |t - t₁'|) (hRmax : |t - t₁'| ≤ Rmax) :
    ∀ m : ℕ, m ≤ M →
      ‖spolyA (ramRdampCoeff H N Xn P Q j (ellLin g) x) t m‖
        ≤ farSupS (k₀ : ℝ) (M : ℝ) Rmax R * (m : ℝ) := by
  have hMk : (M : ℝ) ≤ 2 * (k₀ : ℝ) := by linarith
  have hMtop2 : (M : ℝ) ≤ 2 * ramRbot H Xn j := by linarith
  refine far_transfer_sup (f := ellLin (gxDatum g P Q x)) hk₀ hMk (ellLin_one _)
    (ellLin_mul_coprime_all _)
    (fun n => ellLin_norm_le_one _ (fun p hp => gxDatum_norm_le_one hx0 hx1 hg p hp) n)
    ?_ ?_ hMball hR0 hRle hRmax
  · -- `hsupp`: below the cut the window indicator is off
    intro n hn
    have hlt : (n : ℝ) < ramRbot H Xn j := by
      have : (n : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hn
      linarith
    rw [ramRdampCoeff, if_neg (notMem_ramRrange_of_lt hlt)]
  · -- `hDatum`: inside the window the coefficient IS `ℓ(g_x)`
    intro n hn1 hn2
    have hmem : n ∈ ramRrange H N Xn j := by
      have hnk : (k₀ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn1
      have hnM : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn2
      rw [ramRrange, Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, le_trans hn2 hMN⟩, ?_, ?_⟩
      · have : ramRbot H Xn j ≤ (n : ℝ) := by linarith
        rwa [ramRbot] at this
      · have : (n : ℝ) ≤ 2 * ramRbot H Xn j := le_trans hnM hMtop2
        rw [ramRbot] at this
        linarith
    rw [ramRdampCoeff_ellLin, if_pos hmem]

/-- **The window cut exists.**  For any window bottom `W ≥ 1` there is a natural `k₀` with
`k₀ < W ≤ k₀+1` — the largest integer strictly below `W`.  This is the cut that disposes of
the half-open endpoint convention (`ramRrange` is closed at the bottom, the Abel window is
open there). -/
lemma exists_window_cut {W : ℝ} (hW : 1 ≤ W) : ∃ k₀ : ℕ, (k₀ : ℝ) < W ∧ W ≤ (k₀ : ℝ) + 1 := by
  have hceil : W ≤ (⌈W⌉₊ : ℝ) := Nat.le_ceil W
  have hlt : (⌈W⌉₊ : ℝ) < W + 1 := Nat.ceil_lt_add_one (by linarith)
  have h1 : 1 ≤ ⌈W⌉₊ := by
    have : (1 : ℝ) ≤ (⌈W⌉₊ : ℝ) := le_trans hW hceil
    exact_mod_cast this
  refine ⟨⌈W⌉₊ - 1, ?_, ?_⟩ <;>
    rw [Nat.cast_sub h1, Nat.cast_one] <;> linarith

/-- **The window geometry is satisfiable** — non-vacuity of D-3's five window binders.  At a
co-factor window bottom `X_j ≥ 4` the cut `k₀ = ⌈X_j⌉₊ − 1` (`exists_window_cut`) and the
sharp Abel length `M = ⌊2X_j⌋₊ − 2` (`RamRAdapter.ramR_abel_window_floor`, the ⟦V4a⟧ sharp-`M`
law) discharge all of them at once.  `hMN : M ≤ N` and `hend` remain the consumer's. -/
lemma caseB_window_geometry {H : ℝ} {Xn j : ℕ} (hW : 4 ≤ ramRbot H Xn j) :
    ∃ k₀ M : ℕ,
      (k₀ : ℝ) < ramRbot H Xn j ∧ ramRbot H Xn j ≤ (k₀ : ℝ) + 1 ∧
      ramRbot H Xn j - 1 ≤ (M : ℝ) ∧ (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1) ∧
      2 * ramRbot H Xn j < (M : ℝ) + 3 := by
  obtain ⟨k₀, h1, h2⟩ := exists_window_cut (show (1 : ℝ) ≤ ramRbot H Xn j by linarith)
  obtain ⟨h3, h4, h5⟩ := ramR_abel_window_floor hW
  exact ⟨k₀, ⌊2 * ramRbot H Xn j⌋₊ - 2, h1, h2, h3, h4, h5⟩

/-! ## §6 (D-3) — THE CASE-B ASSEMBLY -/

/-- **D-3a — the assembly from the COLLIDED pocket family.**  Given, for every `x ∈ [0,1]`, a
pocket centre `t₁'(x)` already collided with the row centre (`|t₁'(x) − t₁| < 1`, U7-C's
`pocket_collision_window`) together with the A.4 ball hypothesis at that centre on the
transfer window, the co-factor is bounded on the row's FAR leg:

  `‖R_{j,H}(1+it)‖ ≤ 3·farSupS k₀ M (Dmax+1) R`  for `R ≤ |t − t₁| ≤ Dmax`.

The `3` is `ramR_abel_sup`'s: `2` from Abel plus `1` for the half-open endpoint charge
(`hend`).  At the intended pin `R = seamRad X` the main term is
`6√2·(log X)^{−1/46}` — ⟦V5⟧'s "6× better than needed". -/
theorem caseB_ramR_of_collided {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1)
    {H : ℝ} {N Xn P Q j M k₀ : ℕ} {t t₁ Dmax R : ℝ}
    (hk₀ : 3 ≤ k₀) (hMN : M ≤ N)
    (hk₀lo : (k₀ : ℝ) < ramRbot H Xn j) (hk₀hi : ramRbot H Xn j ≤ (k₀ : ℝ) + 1)
    (hbot : 1 < ramRbot H Xn j)
    (hlow : ramRbot H Xn j - 1 ≤ (M : ℝ)) (hhigh : (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1))
    (hMtop : 2 * ramRbot H Xn j < (M : ℝ) + 3)
    (hR0 : 0 < R) (hfar : R ≤ |t - t₁|) (hDmax : |t - t₁| ≤ Dmax)
    (hend : 2 / ramRbot H Xn j ≤ farSupS (k₀ : ℝ) (M : ℝ) (Dmax + 1) R)
    (hpocket : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ t₁' : ℝ, |t₁' - t₁| < 1 ∧
      ∀ y : ℝ, (k₀ : ℝ) ≤ y → y ≤ (M : ℝ) →
        pretDistSq (fun n => ellLin (gxDatum g P Q x) n * eIu (-t₁') n) (fun _ => 1) y
          ≤ Salt.Mertens.SPartial y / 8) :
    ‖ramR H N Xn P Q j (ellLin g) t‖ ≤ 3 * farSupS (k₀ : ℝ) (M : ℝ) (Dmax + 1) R := by
  refine ramR_abel_sup (fun n => ellLin_norm_le_one g hg n) hbot hlow hhigh hMtop hend ?_
  intro m hm
  refine spolyA_ramRcoeff_le_of_damp ?_
  intro x hx
  obtain ⟨t₁', hcoll, hMball⟩ := hpocket x hx
  -- the far leg, moved onto the pocket centre
  have hRle : R ≤ 1 + |t - t₁'| := by
    have := pocket_far_from_ball hcoll hfar
    linarith
  have hRmax : |t - t₁'| ≤ Dmax + 1 := by
    have h1 : |t - t₁'| ≤ |t - t₁| + |t₁ - t₁'| := by
      rw [show t - t₁' = (t - t₁) + (t₁ - t₁') by ring]
      exact abs_add_le _ _
    have h2 : |t₁ - t₁'| = |t₁' - t₁| := abs_sub_comm _ _
    linarith
  exact damped_partial_transfer hg hx.1 hx.2 hk₀ hMN hk₀lo hk₀hi hhigh hMball hR0 hRle
    hRmax m hm

/-- **D-3 — THE CASE-B `Rbd`.**  U7-C's collision lemma wired in: what is assumed is exactly
the CASE-B hypothesis (a pocket for the damped datum at every damping parameter `x ∈ [0,1]`,
below the `(1/32 − θ)loglog X` grade) plus the row's own A.4 cap, and what comes out is
`USetThinTL.tL_main_sumsq`'s `Rbd` binder

  `‖ramR H N Xn P Q j (ellLin g) t‖ ≤ 3·farSupS k₀ M (Dmax+1) R`

on the far leg `R ≤ |t − t₁| ≤ Dmax`.  Nonnegativity of the `Rbd` (the other half of
`tL_main_sumsq`'s socket) is `farSupS_nonneg`.

**The scale bookkeeping.**  The collision runs at the GLOBAL scale `X`; the transfer runs at
the co-factor window `[k₀, M] ≈ [X_j, 2X_j]`, `X_j = X·e^{−j/H}`.  The two are linked only
through the hypotheses: the pocket family carries its A.4 cap in the `(1/16)loglog k₀` shape
AT THE TRANSFER SCALE.  The descent from the global cap to the window cap (monotonicity of
`pretDistSq` in the scale, plus `loglog X ↝ loglog X_j`) is the consumer's, and is NOT
performed here. -/
theorem caseB_ramR_bound :
    ∃ C : ℝ, ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (H : ℝ) (N Xn P Q j M k₀ : ℕ) (X θ t₁ Dmax R : ℝ),
      -- U7-C's collision inputs, at the global scale `X`
      Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 0 < θ → θ ≤ 1 / 32 →
      P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
      pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
      collisionGate X 25 C →
      -- CASE B: the damped datum has a pocket at every damping parameter
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ t₁' : ℝ, |t₁'| ≤ 3 * X ∧
        pretDistSq (ellLin (gxDatum g P Q x)) (costwist t₁') X
          ≤ (1 / 32 - θ) * Real.log (Real.log X) ∧
        ∀ y : ℝ, (k₀ : ℝ) ≤ y → y ≤ (M : ℝ) →
          pretDistSq (ellLin (gxDatum g P Q x)) (costwist t₁') y
            ≤ (1 / 16) * Real.log (Real.log (k₀ : ℝ))) →
      -- the co-factor window geometry
      ballMertensThreshold ≤ (k₀ : ℝ) → M ≤ N →
      (k₀ : ℝ) < ramRbot H Xn j → ramRbot H Xn j ≤ (k₀ : ℝ) + 1 →
      1 < ramRbot H Xn j → ramRbot H Xn j - 1 ≤ (M : ℝ) →
      (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1) → 2 * ramRbot H Xn j < (M : ℝ) + 3 →
      0 < R → 2 / ramRbot H Xn j ≤ farSupS (k₀ : ℝ) (M : ℝ) (Dmax + 1) R →
      -- the far leg
      ∀ t : ℝ, R ≤ |t - t₁| → |t - t₁| ≤ Dmax →
        ‖ramR H N Xn P Q j (ellLin g) t‖ ≤ 3 * farSupS (k₀ : ℝ) (M : ℝ) (Dmax + 1) R := by
  obtain ⟨C, hC⟩ := pocket_collision_window
  refine ⟨C, fun g hg H N Xn P Q j M k₀ X θ t₁ Dmax R hX hLX hθ0 hθ32 hPlow hQhigh hPQ ht₁
    hrow hgate hpocket hk₀th hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hR0 hend t hfar hDmax => ?_⟩
  have hk₀ : 3 ≤ k₀ := by
    have h1 : (3 : ℝ) ≤ (k₀ : ℝ) := le_trans three_le_ballMertensThreshold hk₀th
    exact_mod_cast h1
  refine caseB_ramR_of_collided hg hk₀ hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hR0 hfar hDmax
    hend ?_
  intro x hx
  obtain ⟨t₁', ht₁'abs, hpock, hcap⟩ := hpocket x hx
  refine ⟨t₁', hC g hg P Q X x θ t₁ t₁' hX hLX hθ0 hθ32 hx.1 hx.2 hPlow hQhigh hPQ ht₁
    ht₁'abs hrow hpock hgate, ?_⟩
  intro y hy1 hy2
  rw [← pretDistSq_twist_slot]
  exact le_trans (hcap y hy1 hy2) (sixteenth_loglog_le_SPartial_div_eight hk₀th hy1)

/-! ## §7 (D-4) — THE COLLISION GATE, DISCHARGED (⟦V5c⟧'s residual)

`collisionGate X 25 C` is U7-C's named `X₀` socket.  Every charge in it is `o(loglog X)`, so
the gate holds past an EXPLICIT threshold — stated, never absorbed (law #253).  The tower is
`X₀ = exp(exp(10⁶ + 75·C⁺))`; the `C` is the floor's own constant, which already carries
`e^{100} ≈ 2.7·10⁴³`, so the honest threshold is `X ≳ exp exp(2·10⁴⁵)` — ⟦V5⟧'s Z-3 estimate,
confirmed. -/

/-- `log u ≤ 2√u` for `u > 0` — `log u = 2·log √u ≤ 2(√u − 1)`. -/
private lemma log_le_two_sqrt {u : ℝ} (hu : 0 < u) : Real.log u ≤ 2 * Real.sqrt u := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have h1 : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log u = 2 * Real.log (Real.sqrt u) := by
    rw [Real.log_sqrt hu.le]; ring
  linarith

/-- `√(u+1) ≤ √u + 1`. -/
private lemma sqrt_add_one_le {u : ℝ} (hu : 0 ≤ u) : Real.sqrt (u + 1) ≤ Real.sqrt u + 1 := by
  have hsq := Real.sq_sqrt hu
  have hnn := Real.sqrt_nonneg u
  have hstep : u + 1 ≤ (Real.sqrt u + 1) ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt hstep
  rwa [Real.sqrt_sq (by positivity)] at this

/-- The two height-drift charges share one page: for `X ≥ 10` and `c ≤ 16`,
`loglog(4X+c) ≤ log 2 + loglog X` (through `4X+c ≤ X²`). -/
private lemma loglog_drift {X c : ℝ} (hX : 10 ≤ X) (hc0 : 0 ≤ c) (hc : c ≤ 16)
    (hlogX : 1 ≤ Real.log X) :
    Real.log (Real.log (4 * X + c)) ≤ Real.log 2 + Real.log (Real.log X) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hpos : (0 : ℝ) < 4 * X + c := by linarith
  have hle : 4 * X + c ≤ X ^ 2 := by nlinarith
  have h1 : Real.log (4 * X + c) ≤ 2 * Real.log X := by
    have h := Real.log_le_log hpos hle
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  have h2 : (0 : ℝ) < Real.log (4 * X + c) := by
    have : Real.log X ≤ Real.log (4 * X + c) := Real.log_le_log hX0 (by linarith)
    linarith
  have h3 : Real.log (Real.log (4 * X + c)) ≤ Real.log (2 * Real.log X) :=
    Real.log_le_log h2 h1
  rwa [Real.log_mul (by norm_num) (by linarith)] at h3

/-- **D-4 — the asymptotic discharge of the collision gate.**  `∃ X₀, ∀ X ≥ X₀,
collisionGate X 25 C`, at the EXPLICIT threshold `X₀ = exp(exp(10⁶ + 75·max(0,C)))`.

The five charges of `collisionGate_of_five`, each put under `0.0135·loglog X`:
(1) `0.8536·√25·√L = 4.268·√L ≤ 0.0135·L` once `√L ≥ 1000`;
(2) the window constant `25`;
(3) the height drift `(3/4)(loglog(4X+3) − loglog X) ≤ (3/4)log 2` (`loglog_drift`);
(4) `5·logloglog(4X+16) ≤ 5·log(L+1) ≤ 10(√L+1)` (`log_le_two_sqrt`, `sqrt_add_one_le`);
(5) the floor's own constant `C`, which is what puts the `75·C⁺` in the tower. -/
theorem collisionGate_discharged (C : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X → collisionGate X 25 C := by
  refine ⟨Real.exp (Real.exp (1000000 + 75 * max 0 C)), Real.exp_pos _, ?_⟩
  intro X hX
  have hCm : (0 : ℝ) ≤ max 0 C := le_max_left _ _
  have hCle : C ≤ max 0 C := le_max_right _ _
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
  -- `log X ≥ exp L₀` and `loglog X ≥ L₀`
  have hlogX : Real.exp (1000000 + 75 * max 0 C) ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos _) hX
    rwa [Real.log_exp] at h
  have hL : 1000000 + 75 * max 0 C ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log (Real.exp_pos _) hlogX
    rwa [Real.log_exp] at h
  have hL6 : (1000000 : ℝ) ≤ Real.log (Real.log X) := by linarith
  have hlogX6 : (1000000 : ℝ) ≤ Real.log X := by
    have := Real.add_one_le_exp (1000000 + 75 * max 0 C)
    linarith
  have hX10 : (10 : ℝ) ≤ X := by
    have h1 : Real.exp (1000000 : ℝ) ≤ X := by
      rw [← Real.exp_log hX0]
      exact Real.exp_le_exp.mpr hlogX6
    have h2 := Real.add_one_le_exp (1000000 : ℝ)
    linarith
  -- the root of `L`
  have hL0 : (0 : ℝ) ≤ Real.log (Real.log X) := by linarith
  have hs : (1000 : ℝ) ≤ Real.sqrt (Real.log (Real.log X)) := by
    have h1 : Real.sqrt (1000000 : ℝ) ≤ Real.sqrt (Real.log (Real.log X)) :=
      Real.sqrt_le_sqrt hL6
    have h2 : Real.sqrt (1000000 : ℝ) = 1000 := by
      rw [show (1000000 : ℝ) = 1000 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    linarith [h2 ▸ h1]
  have hssq : Real.sqrt (Real.log (Real.log X)) ^ 2 = Real.log (Real.log X) :=
    Real.sq_sqrt hL0
  refine collisionGate_of_five X 25 C (by linarith) ?_ (by linarith) ?_ ?_ ?_
  · -- (1) the cross term
    have h25 : Real.sqrt (25 : ℝ) = 5 := by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [h25]
    nlinarith [hs, hssq]
  · -- (3) the height drift at `4X+3`
    have h := loglog_drift (X := X) (c := 3) hX10 (by norm_num) (by norm_num) (by linarith)
    have hlog2 : Real.log 2 ≤ 0.7 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  · -- (4) the floor's `5·logloglog`
    have h := loglog_drift (X := X) (c := 16) hX10 (by norm_num) (by norm_num) (by linarith)
    have hlog2 : Real.log 2 ≤ 0.7 := by
      have := Real.log_two_lt_d9
      linarith
    -- `loglog(4X+16) ≤ L + 1`, and it is positive
    have hpos : (0 : ℝ) < 4 * X + 16 := by linarith
    have hp1 : (1 : ℝ) < Real.log (4 * X + 16) := by
      have : Real.log X ≤ Real.log (4 * X + 16) := Real.log_le_log hX0 (by linarith)
      linarith
    have hp2 : (0 : ℝ) < Real.log (Real.log (4 * X + 16)) :=
      Real.log_pos hp1
    have hle : Real.log (Real.log (4 * X + 16)) ≤ Real.log (Real.log X) + 1 := by linarith
    have hstep : Real.log (Real.log (Real.log (4 * X + 16)))
        ≤ Real.log (Real.log (Real.log X) + 1) := Real.log_le_log hp2 hle
    have hlog := log_le_two_sqrt (u := Real.log (Real.log X) + 1) (by linarith)
    have hsq := sqrt_add_one_le (u := Real.log (Real.log X)) hL0
    nlinarith [hs, hssq]
  · -- (5) the floor's own constant — the source of the tower
    linarith

end Salt.MR
