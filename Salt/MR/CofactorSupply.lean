/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CofactorGrade
import Salt.MR.USetThinTL

/-!
# CofactorSupply — THE DICHOTOMY ASSEMBLY (U7-F): the last stone of U-7

The `⟦V5⟧` ladder's **U7-F** (`docs/exploration/hsup-design.md`).  `CofactorGrade` (U7-E)
prices the co-factor when the damped datum has NO pretentious pocket; `CofactorBall` (U7-D)
prices it when it HAS one.  Here the two arms are fused into a SINGLE bound with no
disjunction left in the statement, and that bound discharges `USetThinTL.tL_main_sumsq`'s
named `Rbd` hypothesis — the socket the whole U-7 campaign was opened to fill.

## THE ROUTE VERDICT: per-`x`, at the damped partial sums (NOT the two `Rbd`s)

Both landed arms state their defining hypothesis over the WHOLE damping family
(`∀ x ∈ [0,1]`): CASE A wants the window floor at every `x`, CASE B a pocket at every `x`.
Their negations do not match — `¬(∀x, floor x)` gives a pocket at ONE `x`, which is not
CASE B's input.  **So the dichotomy cannot be run at the `Rbd` level.**

It runs one level down instead, at `CofactorBall.spolyA_ramRcoeff_le_of_damp`'s binder, where
both arms are already per-`x`:

* `CofactorGrade.caseA_damped_partial` — per-`x`, takes the supply at that `x` alone;
* `CofactorBall.damped_partial_transfer` — per-`x`, takes the pocket at that `x` alone.

Only `CofactorGrade.caseA_partial_supply` is stated `(∀x floor) → (∀x bound)`.  It is
recovered per-`x` with **no restatement** by the *empty-window* instance (§3): run it at the
datum `g' := g_x` and the EMPTY block window `(P,Q) := (1,0)`, where `gxDatum g' 1 0 x' = g'`
for every `x'` (`gxDatum_trivial_window`), so its `∀x` hypothesis IS the single `x`-slice
floor and its `∀x` conclusion IS the single `x`-slice bound.  Iron rule 1 respected: no
landed statement is touched.

The exit is therefore `3·max (2·caseAS …) (farSupS …)` — `max (6·caseAS) (3·farSupS)`, the
two arms' own exits — with `ramR_abel_sup` paying the single factor `3` once.

## THE THREE TRANSPORTS (`CofactorGrade`'s docstring names them; all three are here)

1. **The twist slot.**  CASE A's floor is at the twisted datum `ℓ(g_x·p^{−it})` and frequency
   `costwist (v−t)`; the pocket lives at the bare `ℓ(g_x)` and frequency `costwist v`.  The
   transport is `RHSGrade.twisted_datum_dist_eq` byte-verbatim (`caseA_floor_slot`, §2) —
   `𝔻²(ℓ(g·p^{−iu}), p^{iv}; z) = 𝔻²(ℓ g, p^{i(v+u)}; z)`, at `u := t`, `v := v−t`.
   (`CenterSupply.pretDistSq_twist_slot` is the OTHER twist slot — the one that moves a
   frequency into the datum; it is used in §4 for CASE B's `hMball`.)

2. **The scale descent, and WHICH DIRECTION IS FREE.**  `pretDistSq f g x` sums over `p ≤ x`,
   so it is MONOTONE INCREASING in the scale (`RHSGrade.pretDistSq_mono_scale`).  Hence:

   * a POCKET (an upper bound) descends from the global scale `X` to the window scales
     `y ≤ M` for FREE — which is why §4 runs the dichotomy at the GLOBAL scale `X` and never
     ascends;
   * a FLOOR (a lower bound) descends from `X` to a window scale `k` only against the prime
     tail, and that tail is PRICED: `pretDistSq_tail_le` (§1) charges
     `2·(S(X) − S(k₀))`, `S` the Mertens partial sum, carried as an EXPRESSION (law #253),
     never as an `O(1)`.  It is what makes the CASE-A floor value

     `Mfl = (1/32 − θ)·loglog X − 2·(S(X) − S(k₀))`

     rather than the naked `(1/32 − θ)·loglog X`.  §6 evaluates the charge: under the
     live-regime gate `(1 − 1/loglog X)·log X ≤ log k₀` it is `≤ 4/loglog X + 24/log k₀
     + 24/log X` — `o(1)`, and it costs the CASE-A constant only the harmless factor
     `e^{(2/e)(S(X)−S(k₀))}`.

3. **The contour-window restriction.**  The floor is needed at every `v` with
   `|v − t| ≤ T*(k, log k)`; the pocket is a statement about `|v| ≤ 3X`.  The bridge is the
   stated gate `|t| + T*(k, log k) ≤ 3X` on the window scales (`hTcontour`), i.e. ⟦V5⟧'s
   `|t| ≤ T ≤ X` and `T* ≤ X`.

## What is proved here

* **§1 `pretDistSq_tail_le`** — the priced scale ascent (the Mertens tail, abstract).
* **§2 `caseA_floor_slot`** — transport 1.
* **§3 `gxDatum_trivial_window` / `caseA_partial_supply_slice`** — the per-`x` CASE-A supply.
* **§4 (F-1) `pocket_transport`** — THE DICHOTOMY, per `x`: either the CASE-A window-floor
  slice at `Mfl`, or CASE B's pocket-family slice at `x` (in `damped_partial_transfer`'s
  literal `hMball` shape).
* **§5 (F-2) `cofactor_Rbd`** — the fused bound, the dichotomy discharged internally.
* **§6 (F-4) `descent_tail_le` / `cofactorMfl_nonneg_of_descent` / `cofactor_Rbd_293`** —
  the Mertens page for the descent charge, its non-vacuity, and the pin `c = 1/e`,
  `θ = θ₂₉₃`, exiting at `(log X)^{−ρ₂₉₃}` with the collision gate discharged.
* **§7 (F-3) `tL_supply_discharged`** — `USetThinTL.tL_main_sumsq` with its `Rbd`
  hypothesis GONE.  The prize.

## Law #253 — every gate in the open

`X₀` (the CASE-A supply threshold), `X₁` (the collision tower `exp exp(10⁶+75C⁺)`),
`e^{64} ≤ k₀`, `ballMertensThreshold ≤ k₀`, `M ≤ X`, the loglog descent gate, the contour
gate, the far-leg gates `R ≤ |t−t₁| ≤ Dmax`, the endpoint charge: all in-statement.  Nothing
is absorbed into an "for `X` large enough".
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — THE PRICED SCALE ASCENT (the Mertens tail, abstract)

`pretDistSq` grows with the scale; the growth is at most `2/p` per prime, so the whole
ascent from `k` to `X` costs twice the Mertens mass of the gap.  This is the ONLY place a
floor is allowed to travel upward in scale, and the price is an EXPRESSION. -/

/-- `‖a‖ ≤ 1` in coordinate form (`PretentiousTriangle`'s is `private`). -/
private lemma sq_re_add_sq_im_le_F {a : ℂ} (ha : ‖a‖ ≤ 1) : a.re ^ 2 + a.im ^ 2 ≤ 1 := by
  have h : a.re ^ 2 + a.im ^ 2 = ‖a‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [h]; nlinarith [norm_nonneg a, ha]

/-- Each summand of `pretDistSq` is at most `2` for 1-bounded data — the twin of
`PretentiousTriangle.pretDistSq_term_nonneg`. -/
theorem pretDistSq_term_le_two {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    1 - (a * (starRingEnd ℂ) b).re ≤ 2 := by
  have e : (a * (starRingEnd ℂ) b).re = a.re * b.re + a.im * b.im := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [e]
  nlinarith [sq_re_add_sq_im_le_F ha, sq_re_add_sq_im_le_F hb,
    sq_nonneg (a.re + b.re), sq_nonneg (a.im + b.im)]

/-- `SPartial` is monotone (a sum of nonnegative terms over a growing prime set). -/
theorem SPartial_mono_floor {k X : ℝ} (hkX : ⌊k⌋₊ ≤ ⌊X⌋₊) :
    Salt.Mertens.SPartial k ≤ Salt.Mertens.SPartial X := by
  unfold Salt.Mertens.SPartial
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

/-- **THE PRICED ASCENT (`pretDistSq_tail_le`).**  For 1-bounded data and `⌊k⌋₊ ≤ ⌊X⌋₊`

  `𝔻²(f, g; X) ≤ 𝔻²(f, g; k) + 2·(S(X) − S(k))`,

`S` the Mertens partial sum `Σ_{p ≤ ·} 1/p`.  Each new prime contributes at most `2/p`
(`pretDistSq_term_le_two`).  **This is the transport that a FLOOR must pay** when it is
moved from the global scale down to a window scale; the pocket (an upper bound) travels the
other way for free (`pretDistSq_mono_scale`). -/
theorem pretDistSq_tail_le {f g : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    {k X : ℝ} (hkX : ⌊k⌋₊ ≤ ⌊X⌋₊) :
    pretDistSq f g X
      ≤ pretDistSq f g k + 2 * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial k) := by
  classical
  set A := (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime with hA
  set B := (Finset.range (⌊k⌋₊ + 1)).filter Nat.Prime with hB
  have hBA : B ⊆ A := by
    intro p hp
    rw [hB, Finset.mem_filter, Finset.mem_range] at hp
    rw [hA, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2⟩
  -- both sides split as `(A \ B) + B`
  have hsplitD : pretDistSq f g X
      = (∑ p ∈ A \ B, (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ)) + pretDistSq f g k := by
    unfold pretDistSq
    rw [← hA, ← hB]
    exact (Finset.sum_sdiff hBA).symm
  have hsplitS : Salt.Mertens.SPartial X
      = (∑ p ∈ A \ B, (1 : ℝ) / (p : ℝ)) + Salt.Mertens.SPartial k := by
    unfold Salt.Mertens.SPartial
    rw [← hA, ← hB]
    exact (Finset.sum_sdiff hBA).symm
  have hterm : ∑ p ∈ A \ B, (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ)
      ≤ ∑ p ∈ A \ B, 2 * ((1 : ℝ) / (p : ℝ)) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hpp : p.Prime := by
      have := Finset.mem_sdiff.mp hp
      rw [hA, Finset.mem_filter] at this
      exact this.1.2
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    rw [div_le_iff₀ hppos]
    have := pretDistSq_term_le_two (hf p) (hg p)
    have h2 : 2 * ((1 : ℝ) / (p : ℝ)) * (p : ℝ) = 2 := by field_simp
    rw [h2]
    exact this
  have hsum2 : ∑ p ∈ A \ B, 2 * ((1 : ℝ) / (p : ℝ))
      = 2 * ∑ p ∈ A \ B, (1 : ℝ) / (p : ℝ) := by rw [Finset.mul_sum]
  rw [hsplitD, hsplitS]
  rw [hsum2] at hterm
  linarith

/-! ## §2 — TRANSPORT 1: the twist slot -/

/-- **TRANSPORT 1 (`caseA_floor_slot`).**  CASE A's floor datum is the `t`-twisted damped
datum read at the shifted frequency `v − t`; that is exactly the bare damped datum read at
`v`.  `RHSGrade.twisted_datum_dist_eq` byte-verbatim, at `u := t`, `v := v − t`. -/
theorem caseA_floor_slot (g : ℕ → ℂ) (P Q : ℕ) (x t v z : ℝ) :
    pretDistSq (ellLin (fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(t : ℂ) * Complex.I)))
        (costwist (v - t)) z
      = pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) z := by
  rw [twisted_datum_dist_eq, show v - t + t = v from by ring]

/-! ## §3 — the per-`x` CASE-A supply, by the EMPTY-WINDOW instance

`caseA_partial_supply` is stated `(∀x floor) → (∀x bound)`.  Instantiating it at the datum
`g_x` and the EMPTY block window `(1,0)` — where the damping is the identity for every
parameter — turns both `∀x`s into the single `x`-slice.  No landed statement is touched. -/

/-- The empty block window `(P,Q) = (1,0)` damps nothing: `g_{x'} = g` for every `x'`. -/
theorem gxDatum_trivial_window (g : ℕ → ℂ) (x : ℝ) : gxDatum g 1 0 x = g := by
  funext p
  unfold gxDatum
  rw [if_neg (by omega : ¬(1 ≤ p ∧ p ≤ 0)), mul_one]

/-- **THE PER-`x` CASE-A SUPPLY** (`caseA_partial_supply_slice`).  `caseA_partial_supply` for
ONE damping parameter, with the floor stated in the transported (bare-datum) slot:

  `∀ k ∈ [⌊W⌋₊, N], ∀ v, |v − t| ≤ T*(k, log k) → M ≤ 𝔻²(ℓ(g_x), p^{iv}; k)`
  `⟹  ∀ k ∈ [⌊W⌋₊, N], ‖∑_{n≤k} ℓ(g_x)(n)·n^{−it}‖ ≤ caseAS c Cb M W · k`.

The `∃ X₀` is the landed one, hoisted over everything (`center_halasz_supply_A`'s datum-free
witness); the gates `X₀ ≤ W`, `e ≤ W`, `W ≤ N ≤ 2W`, `e^{64} ≤ k` are `caseA_partial_supply`'s
own, at the SHIFTED scale (law #253). -/
theorem caseA_partial_supply_slice :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ (P Q : ℕ) (c Cb t W M x : ℝ) (N : ℕ),
        0 ≤ x → x ≤ 1 →
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        X₀ ≤ W → Real.exp 1 ≤ W → W ≤ (N : ℝ) → (N : ℝ) ≤ 2 * W →
        (∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N → Real.exp 64 ≤ (k : ℝ)) → 0 ≤ M →
        (∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N → ∀ v : ℝ,
          |v - t| ≤ Tstar (k : ℝ) (Real.log (k : ℝ)) →
            M ≤ pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) (k : ℝ)) →
        ∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N →
          ‖∑ n ∈ Finset.Icc 1 k, ellLin (gxDatum g P Q x) n * eIu (-t) n‖
            ≤ caseAS c Cb M W * (k : ℝ) := by
  obtain ⟨X₀, hX₀0, hsupply⟩ := caseA_partial_supply
  refine ⟨X₀, hX₀0, ?_⟩
  intro g hg P Q c Cb t W M x N hx0 hx1 hc0 hce hc1 hCb0 hCbound hX₀W hWe hWN hN2 hk64 hM0
    hfloor
  have hgx : ∀ p : ℕ, p.Prime → ‖gxDatum g P Q x p‖ ≤ 1 :=
    fun p hp => gxDatum_norm_le_one hx0 hx1 hg p hp
  -- the empty-window instance: the whole damping family collapses to the single slice
  have h := hsupply (gxDatum g P Q x) hgx 1 0 c Cb t W M N hc0 hce hc1 hCb0 hCbound hX₀W hWe
    hWN hN2 hk64 hM0 ?_
  · intro k hk1 hk2
    have h0 := h 0 (Set.mem_Icc.mpr ⟨le_rfl, by norm_num⟩) k hk1 hk2
    simpa only [gxDatum_trivial_window] using h0
  · intro x' _ k hk1 hk2 v hv
    simpa only [gxDatum_trivial_window, caseA_floor_slot] using hfloor k hk1 hk2 v hv

/-! ## §4 (F-1) — THE DICHOTOMY, TRANSPORTED

The split is taken at the **GLOBAL** scale `X`, on the bare damped datum, over the contour
box `|v| ≤ 3X`:

* if a pocket exists there, it descends to the co-factor window for FREE (monotonicity) and
  arrives in `damped_partial_transfer`'s literal `hMball` shape;
* if none exists, the resulting floor descends to the window scales against the PRICED tail
  (§1), and arrives as CASE A's `hMwin` slice at the value `cofactorMfl`.

Taking the split at `X` (rather than at the window) is what makes the pocket side free: the
only priced transport is the floor's, and it is priced once, by an expression. -/

/-- **THE CASE-A FLOOR VALUE.**  `(1/32 − θ)·loglog X` — ⟦V5⟧'s grade at the GLOBAL scale —
less the priced scale descent `2·(S(X) − S(W))` of §1.  Carried as an EXPRESSION (law #253);
§6 evaluates it. -/
def cofactorMfl (X θ W : ℝ) : ℝ :=
  (1 / 32 - θ) * Real.log (Real.log X)
    - 2 * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W)

/-- **THE FUSED `Rbd`.**  `max` of the two arms' own exits, `6·caseAS` and `3·farSupS`, with
`ramR_abel_sup`'s factor `3` pulled out front. -/
def cofactorRbd (c Cb X θ W Y Rmax R : ℝ) : ℝ :=
  3 * max (2 * caseAS c Cb (cofactorMfl X θ W) W) (farSupS W Y Rmax R)

lemma cofactorRbd_nonneg {c Cb X θ W Y Rmax R : ℝ} (hc1 : 2 * c < 1) (hCb0 : 0 ≤ Cb)
    (hW : 1 ≤ W) : 0 ≤ cofactorRbd c Cb X θ W Y Rmax R := by
  have h1 : (0 : ℝ) ≤ 2 * caseAS c Cb (cofactorMfl X θ W) W := by
    have := caseAS_nonneg (c := c) (Cb := Cb) (M := cofactorMfl X θ W) (W := W) hc1 hCb0 hW
    linarith
  have h2 : 2 * caseAS c Cb (cofactorMfl X θ W) W
      ≤ max (2 * caseAS c Cb (cofactorMfl X θ W) W) (farSupS W Y Rmax R) := le_max_left _ _
  unfold cofactorRbd
  linarith

/-- **F-1 — THE POCKET TRANSPORT.**  At a FIXED damping parameter `x ∈ [0,1]`: either the
CASE-A window floor holds at the value `cofactorMfl X θ k₀`, or the CASE-B pocket family
exists at `x`, already in `CofactorBall.damped_partial_transfer`'s `hMball` shape.

**The three transports, all here.**
1. the twist slot: performed by `caseA_partial_supply_slice` (§3, `caseA_floor_slot`), so the
   floor is stated here in the BARE slot `𝔻²(ℓ(g_x), p^{iv}; k)`;
2. the scale descent: the pocket's is FREE (`pretDistSq_mono_scale`, `y ≤ M ≤ X`); the
   floor's is PRICED (`pretDistSq_tail_le`, and `SPartial_mono_floor` moves the charge from
   the scale `k` to the window bottom `k₀`);
3. the contour window: `hTcontour` converts `|v − t| ≤ T*(k, log k)` into `|v| ≤ 3X`, the box
   `pocket_collision_window` needs.

`hll` is the loglog descent gate — the pocket at grade `(1/32 − θ)loglog X` must sit under
the A.4 window cap `(1/16)loglog k₀`; it holds with room whenever `loglog X ≤ 2·loglog k₀`
(law #253: stated, never absorbed). -/
theorem pocket_transport {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (P Q : ℕ)
    {k₀ M : ℕ} {X θ t x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hk₀th : ballMertensThreshold ≤ (k₀ : ℝ)) (hMX : (M : ℝ) ≤ X)
    (hll : (1 / 32 - θ) * Real.log (Real.log X) ≤ (1 / 16) * Real.log (Real.log (k₀ : ℝ)))
    (hTcontour : ∀ k : ℕ, k₀ ≤ k → k ≤ M →
      |t| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ 3 * X) :
    (∀ k : ℕ, k₀ ≤ k → k ≤ M → ∀ v : ℝ, |v - t| ≤ Tstar (k : ℝ) (Real.log (k : ℝ)) →
        cofactorMfl X θ (k₀ : ℝ)
          ≤ pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) (k : ℝ))
      ∨ (∃ t₁' : ℝ, |t₁'| ≤ 3 * X ∧
          pretDistSq (ellLin (gxDatum g P Q x)) (costwist t₁') X
            ≤ (1 / 32 - θ) * Real.log (Real.log X) ∧
          ∀ y : ℝ, (k₀ : ℝ) ≤ y → y ≤ (M : ℝ) →
            pretDistSq (fun n => ellLin (gxDatum g P Q x) n * eIu (-t₁') n) (fun _ => 1) y
              ≤ Salt.Mertens.SPartial y / 8) := by
  classical
  have hgx : ∀ p : ℕ, p.Prime → ‖gxDatum g P Q x p‖ ≤ 1 :=
    fun p hp => gxDatum_norm_le_one hx0 hx1 hg p hp
  have hEll : ∀ n : ℕ, ‖ellLin (gxDatum g P Q x) n‖ ≤ 1 := ellLin_norm_le_one _ hgx
  by_cases hpocket : ∃ v : ℝ, |v| ≤ 3 * X ∧
      pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) X
        ≤ (1 / 32 - θ) * Real.log (Real.log X)
  · -- the pocket arm: the descent to the window is FREE
    right
    obtain ⟨v, hvabs, hv⟩ := hpocket
    refine ⟨v, hvabs, hv, ?_⟩
    intro y hy1 hy2
    rw [← pretDistSq_twist_slot]
    have hcw : ∀ n : ℕ, ‖costwist v n‖ ≤ 1 := fun n => le_of_eq (costwist_norm v n)
    have hmono : pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) y
        ≤ pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) X :=
      pretDistSq_mono_scale hEll hcw (le_trans hy2 hMX)
    have h16 := sixteenth_loglog_le_SPartial_div_eight hk₀th hy1
    linarith
  · -- the floor arm: the descent to the window is PRICED
    left
    simp only [not_exists, not_and, not_le] at hpocket
    intro k hk1 hk2 v hv
    have hcw : ∀ n : ℕ, ‖costwist v n‖ ≤ 1 := fun n => le_of_eq (costwist_norm v n)
    -- transport 3: the contour window sits inside the collision box
    have hvabs : |v| ≤ 3 * X := by
      have h1 : |v| ≤ |v - t| + |t| := by
        have := abs_add_le (v - t) t
        simpa using this
      have h2 := hTcontour k hk1 hk2
      linarith
    have hXbig := hpocket v hvabs
    -- transport 2: the priced ascent, charged at the window bottom
    have hkM : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk2
    have hkX : ⌊(k : ℝ)⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono (le_trans hkM hMX)
    have htail := pretDistSq_tail_le (f := ellLin (gxDatum g P Q x)) (g := costwist v)
      hEll hcw hkX
    have hSk : Salt.Mertens.SPartial (k₀ : ℝ) ≤ Salt.Mertens.SPartial (k : ℝ) := by
      refine SPartial_mono_floor ?_
      rw [Nat.floor_natCast, Nat.floor_natCast]
      exact hk1
    unfold cofactorMfl
    linarith

/-! ## §5 (F-2) — THE FUSED `Rbd`

The dichotomy is discharged INSIDE the proof, one damping parameter at a time, at
`spolyA_ramRcoeff_le_of_damp`'s binder.  No disjunction survives in the statement. -/

/-- **F-2 — THE CO-FACTOR `Rbd`** (`cofactor_Rbd`).  `USetThinTL.tL_main_sumsq`'s `Rbd`
binder, with the co-factor dichotomy discharged internally:

  `‖R_{j,H}(1+it)‖ ≤ cofactorRbd c Cb X θ k₀ M (Dmax+1) R
                   = 3·max (2·caseAS c Cb (cofactorMfl X θ k₀) k₀) (farSupS k₀ M (Dmax+1) R)`.

Nonnegativity of the `Rbd` (the other half of `tL_main_sumsq`'s socket) is
`cofactorRbd_nonneg`.

**THE CARRIED HYPOTHESES, ENUMERATED — the UNION of the two arms' (this is the whole list).**

*Shared with CASE A (`CofactorGrade.caseA_ramR_bound`):*
1. `hg` — the primes' norm bound on the row's datum;
2. the `c`-contract `0 < c`, `c ≤ 1/e`, `2c < 1`;
3. `0 ≤ Cb` and `ShortIntervalDatum Cb` — the amplitude side's short-interval datum;
4. `X₀ ≤ k₀` and `e^{64} ≤ k₀` — the supply threshold and the corpus scale gate, at the
   SHIFTED scale (law #253);
5. `hMfl0 : 0 ≤ cofactorMfl X θ k₀` — the floor value is a floor.

*Shared with CASE B (`CofactorBall.caseB_ramR_bound`):*
6. `ballMertensThreshold ≤ k₀` — the A.4/Mertens window threshold;
7. the collision inputs at the GLOBAL scale: `e ≤ X`, `e ≤ log X`, `0 < θ ≤ 1/32`,
   `P₈₃(X,θ) ≤ P`, `Q ≤ Q₈₃(X)`, `P ≤ Q`, `|t₁| ≤ X`, the row's own A.4 cap `hrow`, and the
   named gate `collisionGate X 25 C` (⟦V5⟧'s Z-3 tower — `collisionGate_discharged`);
8. the far leg `0 < R`, `R ≤ |t − t₁| ≤ Dmax`.

*Shared by both (the window geometry — `CofactorBall.caseB_window_geometry` builds five of
them from `4 ≤ X_j`, `exists_window_cut` the cut):*
9. `hMN : M ≤ N`, `hk₀lo`, `hk₀hi`, `hbot`, `hlow`, `hhigh`, `hMtop`;
10. `hend` — `ramR_abel_sup`'s half-open endpoint charge, at the fused `Rbd/3`.

*NEW here — the three transport gates of §4 (law #253):*
11. `hMX : M ≤ X` — the co-factor window sits below the global scale;
12. `hll : (1/32 − θ)·loglog X ≤ (1/16)·loglog k₀` — the loglog descent gate;
13. `hTcontour : ∀ k ∈ [k₀,M], |t| + T*(k, log k) ≤ 3X` — the contour window inside the
    collision box.

Gone versus the two arms taken separately: the disjunction, and BOTH arms' `∀x` defining
hypotheses (`hMwin` and the pocket family) — they are what the dichotomy manufactures. -/
theorem cofactor_Rbd :
    ∃ X₀ C : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (H : ℝ) (N Xn P Q j M k₀ : ℕ) (c Cb X θ t t₁ Dmax R : ℝ),
        -- (2),(3) the `c`-contract and the amplitude datum
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        -- (4),(6) the scale gates, at the SHIFTED scale
        X₀ ≤ (k₀ : ℝ) → Real.exp 64 ≤ (k₀ : ℝ) → ballMertensThreshold ≤ (k₀ : ℝ) →
        -- (9) the co-factor window geometry
        M ≤ N → (k₀ : ℝ) < ramRbot H Xn j → ramRbot H Xn j ≤ (k₀ : ℝ) + 1 →
        1 < ramRbot H Xn j → ramRbot H Xn j - 1 ≤ (M : ℝ) →
        (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1) → 2 * ramRbot H Xn j < (M : ℝ) + 3 →
        -- (11),(12),(13) THE TRANSPORT GATES
        (M : ℝ) ≤ X →
        (1 / 32 - θ) * Real.log (Real.log X) ≤ (1 / 16) * Real.log (Real.log (k₀ : ℝ)) →
        (∀ k : ℕ, k₀ ≤ k → k ≤ M → |t| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ 3 * X) →
        -- (7) the collision inputs, at the GLOBAL scale
        Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 0 < θ → θ ≤ 1 / 32 →
        P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 C →
        -- (8) the far leg
        0 < R → R ≤ |t - t₁| → |t - t₁| ≤ Dmax →
        -- (5) the floor value, and (10) the half-open endpoint charge
        0 ≤ cofactorMfl X θ (k₀ : ℝ) →
        2 / ramRbot H Xn j ≤ cofactorRbd c Cb X θ (k₀ : ℝ) (M : ℝ) (Dmax + 1) R / 3 →
        ‖ramR H N Xn P Q j (ellLin g) t‖
          ≤ cofactorRbd c Cb X θ (k₀ : ℝ) (M : ℝ) (Dmax + 1) R := by
  obtain ⟨X₀, hX₀0, hslice⟩ := caseA_partial_supply_slice
  obtain ⟨C, hC⟩ := pocket_collision_window
  refine ⟨X₀, C, hX₀0, ?_⟩
  intro g hg H N Xn P Q j M k₀ c Cb X θ t t₁ Dmax R hc0 hce hc1 hCb0 hCbound hX₀k hk₀64
    hk₀th hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hMX hll hTcont hX hLX hθ0 hθ32 hPlow hQhigh
    hPQ ht₁ hrow hgate hR0 hfar hDmax hMfl0 hend
  -- the window arithmetic (`caseA_ramR_bound`'s own)
  have hk₀0 : (0 : ℝ) < (k₀ : ℝ) := lt_of_lt_of_le (Real.exp_pos 64) hk₀64
  have hk₀3R : (3 : ℝ) ≤ (k₀ : ℝ) := by
    have h65 : (65 : ℝ) ≤ (k₀ : ℝ) := by linarith [Real.add_one_le_exp (64 : ℝ)]
    linarith
  have hk₀3 : 3 ≤ k₀ := by exact_mod_cast hk₀3R
  have hk₀e : Real.exp 1 ≤ (k₀ : ℝ) := le_trans (Real.exp_le_exp.mpr (by norm_num)) hk₀64
  have hk₀MR : (k₀ : ℝ) ≤ (M : ℝ) := by linarith
  have hk₀M : k₀ ≤ M := by exact_mod_cast hk₀MR
  have hM2k₀ : (M : ℝ) ≤ 2 * (k₀ : ℝ) := by linarith
  have hfl : ⌊((k₀ : ℕ) : ℝ)⌋₊ = k₀ := Nat.floor_natCast k₀
  have hk64 : ∀ k : ℕ, ⌊((k₀ : ℕ) : ℝ)⌋₊ ≤ k → k ≤ M → Real.exp 64 ≤ (k : ℝ) := by
    intro k hk1 _
    rw [hfl] at hk1
    have : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  set S : ℝ := max (2 * caseAS c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ))
    (farSupS (k₀ : ℝ) (M : ℝ) (Dmax + 1) R) with hS
  have hSA : 2 * caseAS c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) ≤ S := le_max_left _ _
  have hSB : farSupS (k₀ : ℝ) (M : ℝ) (Dmax + 1) R ≤ S := le_max_right _ _
  have hRbdS : cofactorRbd c Cb X θ (k₀ : ℝ) (M : ℝ) (Dmax + 1) R = 3 * S := rfl
  have hendS : 2 / ramRbot H Xn j ≤ S := by
    rw [hRbdS] at hend; linarith
  rw [hRbdS]
  refine ramR_abel_sup (fun n => ellLin_norm_le_one g hg n) hbot hlow hhigh hMtop hendS ?_
  intro m hm
  refine spolyA_ramRcoeff_le_of_damp ?_
  intro x hx
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rcases pocket_transport hg P Q hx.1 hx.2 hk₀th hMX hll hTcont with hA | hB
  · -- CASE A at this `x`
    have hsup : ∀ k : ℕ, k₀ ≤ k → k ≤ M →
        ‖∑ n ∈ Finset.Icc 1 k, ellLin (gxDatum g P Q x) n * eIu (-t) n‖
          ≤ caseAS c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) * (k : ℝ) := by
      intro k hk1 hk2
      refine hslice g hg P Q c Cb t (k₀ : ℝ) (cofactorMfl X θ (k₀ : ℝ)) x M hx.1 hx.2 hc0 hce
        hc1 hCb0 hCbound hX₀k hk₀e hk₀MR hM2k₀ hk64 hMfl0 ?_ k (by rw [hfl]; exact hk1) hk2
      intro k' hk1' hk2' v hv
      rw [hfl] at hk1'
      exact hA k' hk1' hk2' v hv
    have hS0 : (0 : ℝ) ≤ caseAS c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) :=
      caseAS_nonneg hc1 hCb0 (by linarith)
    have hbd := caseA_damped_partial (g := g) (H := H) (N := N) (Xn := Xn) (P := P) (Q := Q)
      (j := j) (M := M) (k₀ := k₀) (x := x) (t := t) hS0 hMN hk₀M hk₀lo hk₀hi hhigh hsup m hm
    have hmul : 2 * caseAS c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) * (m : ℝ) ≤ S * (m : ℝ) :=
      mul_le_mul_of_nonneg_right hSA hm0
    linarith
  · -- CASE B at this `x`
    obtain ⟨t₁', ht₁'abs, hpock, hcap⟩ := hB
    have hcoll := hC g hg P Q X x θ t₁ t₁' hX hLX hθ0 hθ32 hx.1 hx.2 hPlow hQhigh hPQ ht₁
      ht₁'abs hrow hpock hgate
    have hRle : R ≤ 1 + |t - t₁'| := by
      have := pocket_far_from_ball hcoll hfar
      linarith
    have hRmax : |t - t₁'| ≤ Dmax + 1 := by
      have h1 : |t - t₁'| ≤ |t - t₁| + |t₁ - t₁'| := by
        rw [show t - t₁' = (t - t₁) + (t₁ - t₁') by ring]
        exact abs_add_le _ _
      have h2 : |t₁ - t₁'| = |t₁' - t₁| := abs_sub_comm _ _
      linarith
    have hbd := damped_partial_transfer hg hx.1 hx.2 hk₀3 hMN hk₀lo hk₀hi hhigh hcap hR0 hRle
      hRmax m hm
    have hmul : farSupS (k₀ : ℝ) (M : ℝ) (Dmax + 1) R * (m : ℝ) ≤ S * (m : ℝ) :=
      mul_le_mul_of_nonneg_right hSB hm0
    linarith

/-! ## §6 (F-4) — THE DESCENT CHARGE EVALUATED, AND THE PIN

§1 charged the floor's scale descent by the EXPRESSION `2·(S(X) − S(W))`.  Here that
expression is evaluated by sharp Mertens-2 under the live-regime gate — the page ⟦V5⟧'s
`j/H` numeral is for — and the whole thing is read at the pin `c = 1/e`, `θ = θ₂₉₃`. -/

/-- **THE DESCENT CHARGE (`descent_tail_le`).**  Under the live-regime gate

  `(1 − 1/loglog X)·log X ≤ log W`

— i.e. `W ≥ X^{1−1/loglog X}`, which for the co-factor window bottom `W = X_j = X·e^{−j/H}`
is exactly `j ≤ H·log X/loglog X`, the block range §8.3 actually runs over —

  `2·(S(X) − S(W)) ≤ 4/loglog X + 24/log W + 24/log X`,

which is `o(1)`.  So the CASE-A floor loses only `o(1)` to the descent, and the CASE-A
constant only the factor `e^{(2/e)·o(1)} → 1`.

The page: sharp Mertens-2 twice (`Salt.Mertens.mertens_second_sharp_real`, the explicit
`12/log t`) leaves `loglog X − loglog W`, and that is `≤ (log X − log W)/log W ≤ 2/loglog X`
by `log u ≤ u − 1` at `u = log X/log W` together with the gate.  Every constant is explicit
(law #253); nothing is `O(1)`-absorbed. -/
theorem descent_tail_le {X W : ℝ} (hW2 : 2 ≤ W) (hWX : W ≤ X)
    (hlX : Real.exp 2 ≤ Real.log X)
    (hgate : (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log W) :
    2 * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W)
      ≤ 4 / Real.log (Real.log X) + 24 / Real.log W + 24 / Real.log X := by
  have he2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have ha0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le he2 hlX
  have hX2 : (2 : ℝ) ≤ X := le_trans hW2 hWX
  have hb0 : (0 : ℝ) < Real.log W := Real.log_pos (by linarith)
  -- `L := loglog X ≥ 2`
  have hL2 : (2 : ℝ) ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log he2 hlX
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) < Real.log (Real.log X) := by linarith
  -- the gate gives `log W ≥ (1/2)·log X`
  have hhalf : (1 : ℝ) / 2 * Real.log X ≤ Real.log W := by
    have h1 : (1 : ℝ) / Real.log (Real.log X) ≤ 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL2
    nlinarith
  -- `loglog X − loglog W ≤ (log X − log W)/log W`
  have hstep1 : Real.log (Real.log X) - Real.log (Real.log W)
      ≤ (Real.log X - Real.log W) / Real.log W := by
    have hq : (0 : ℝ) < Real.log X / Real.log W := by positivity
    have h := Real.log_le_sub_one_of_pos hq
    rw [Real.log_div (ne_of_gt ha0) (ne_of_gt hb0)] at h
    have heq : Real.log X / Real.log W - 1 = (Real.log X - Real.log W) / Real.log W := by
      field_simp
    linarith [heq ▸ h]
  -- and that is `≤ 2/loglog X`
  have hstep2 : (Real.log X - Real.log W) / Real.log W ≤ 2 / Real.log (Real.log X) := by
    rw [div_le_div_iff₀ hb0 hL0]
    have hgap : Real.log (Real.log X) * (Real.log X - Real.log W) ≤ Real.log X := by
      have h1 : Real.log X - Real.log W ≤ Real.log X / Real.log (Real.log X) := by
        have h2 : (1 - 1 / Real.log (Real.log X)) * Real.log X
            = Real.log X - Real.log X / Real.log (Real.log X) := by
          field_simp
        linarith [h2 ▸ hgate]
      have h3 : Real.log (Real.log X) * (Real.log X / Real.log (Real.log X)) = Real.log X := by
        field_simp
      nlinarith
    nlinarith
  -- sharp Mertens-2 at both endpoints
  have hMX := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hX2)
  have hMW := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hW2)
  have h12X : (0 : ℝ) ≤ 12 / Real.log X := by positivity
  have h12W : (0 : ℝ) ≤ 12 / Real.log W := by positivity
  have hkey : Real.log (Real.log X) - Real.log (Real.log W) ≤ 2 / Real.log (Real.log X) := by
    linarith
  -- `linarith` does NOT distribute a numeral across a division (`4/b` and `2/b` are distinct
  -- atoms to it), so the three doublings are spelled out by `ring` first.
  have e1 : (4 : ℝ) / Real.log (Real.log X) = 2 * (2 / Real.log (Real.log X)) := by ring
  have e2 : (24 : ℝ) / Real.log W = 2 * (12 / Real.log W) := by ring
  have e3 : (24 : ℝ) / Real.log X = 2 * (12 / Real.log X) := by ring
  rw [e1, e2, e3]
  linarith [hMX.1, hMX.2, hMW.1, hMW.2]

/-- **THE FLOOR VALUE IS A FLOOR — non-vacuity of `hMfl0`.**  `cofactor_Rbd`'s hypothesis
`0 ≤ cofactorMfl X θ k₀` is not an accident of the statement: at any `θ ≤ 1/64` the descent
charge of `descent_tail_le` is `o(loglog X)`, so half the grade survives it.  The gate
`hbig` is the explicit form of "`o(loglog X)`", stated (law #253); at the ⟦V5c⟧ tower
`loglog X ≳ 2·10⁴⁵` it holds with a factor `10⁴³` to spare. -/
theorem cofactorMfl_nonneg_of_descent {X W θ : ℝ} (hW2 : 2 ≤ W) (hWX : W ≤ X)
    (hlX : Real.exp 2 ≤ Real.log X)
    (hgate : (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log W)
    (hθ : θ ≤ 1 / 64)
    (hbig : 4 / Real.log (Real.log X) + 24 / Real.log W + 24 / Real.log X
      ≤ (1 / 64) * Real.log (Real.log X)) :
    0 ≤ cofactorMfl X θ W := by
  have hL2 : (2 : ℝ) ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log (Real.exp_pos 2) hlX
    rwa [Real.log_exp] at h
  have hdesc := descent_tail_le hW2 hWX hlX hgate
  have hgrade : (1 / 64 : ℝ) * Real.log (Real.log X)
      ≤ (1 / 32 - θ) * Real.log (Real.log X) := by
    have h1 : (1 / 64 : ℝ) ≤ 1 / 32 - θ := by linarith
    nlinarith
  unfold cofactorMfl
  linarith

/-- **THE PIN'S GRADE, WITH THE DESCENT CHARGE VISIBLE.**  At `c = 1/e` and
`θ = θ₂₉₃` the CASE-A grade factor is the ⟦V5⟧ `(log X)^{−ρ₂₉₃}` times exactly the descent
charge's exponential:

  `e^{−(1/e)·cofactorMfl X θ₂₉₃ W} = e^{(2/e)·(S(X)−S(W))}·(log X)^{−ρ₂₉₃}`.

`CofactorGrade.caseA_grade_numeral` (i.e. `CofactorDist.balance_exponent_293`,
`ρ = (1/32 − θ)/e`) read at the GLOBAL scale; nothing is estimated. -/
theorem cofactorMfl_grade_293 {X W : ℝ} (hX : Real.exp 1 ≤ X) :
    Real.exp (-(1 / Real.exp 1) * cofactorMfl X theta293 W)
      = Real.exp ((2 / Real.exp 1)
          * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W))
        * Real.log X ^ (-rho293) := by
  have hsplit : -(1 / Real.exp 1) * cofactorMfl X theta293 W
      = (2 / Real.exp 1) * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W)
        + -(1 / Real.exp 1) * ((1 / 32 - theta293) * Real.log (Real.log X)) := by
    unfold cofactorMfl; ring
  rw [hsplit, Real.exp_add, caseA_grade_numeral hX]

/-- **F-4 — THE CASE-A CONSTANT AT THE PIN.**  `caseAS` at `c = 1/e`, floor `cofactorMfl`:

  `caseAS (1/e) Cb (cofactorMfl X θ₂₉₃ W) W`
    `= C₁(1/e,Cb)·e^{(2/e)(S(X)−S(W))}·(log X)^{−ρ₂₉₃}`
      `+ farCStar·(log W)^{−1/(32e)} + 4·(log W)^{−1/2+1/1000}`.

The leading exponent is `ρ₂₉₃ = 3θ₂₉₃ ≈ 0.01024` at the GLOBAL scale `X`; the two additive
terms carry the larger exponents `1/(32e) ≈ 0.01150` and `0.499` at the SHIFTED scale `W`.
The only trace of the descent is the factor `e^{(2/e)(S(X)−S(W))}`, which `descent_tail_le`
puts at `1 + o(1)`. -/
theorem caseAS_293 {X W Cb : ℝ} (hX : Real.exp 1 ≤ X) :
    caseAS (1 / Real.exp 1) Cb (cofactorMfl X theta293 W) W
      = gradeAbsConstC (1 / Real.exp 1) Cb
          * (Real.exp ((2 / Real.exp 1)
              * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W))
            * Real.log X ^ (-rho293))
        + farCStar * Real.log W ^ (-(1 / (32 * Real.exp 1)))
        + 4 * Real.log W ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
  unfold caseAS
  rw [cofactorMfl_grade_293 hX]

/-- **F-4 — THE `Rbd` AT THE PIN** (`cofactor_Rbd_293`).  `cofactor_Rbd` at `c = 1/e` (where
the `c`-contract's three gates pass) and `θ = θ₂₉₃`, with the collision gate DISCHARGED:
`collisionGate X 25 C` is replaced by the explicit threshold `X₁ ≤ X`
(`CofactorBall.collisionGate_discharged`, `X₁ = exp exp(10⁶ + 75·C⁺)` — ⟦V5⟧'s Z-3 tower,
in the open).  What is left in front of the exit is

  `3·max (2·caseAS (1/e) Cb (cofactorMfl X θ₂₉₃ k₀) k₀) (farSupS k₀ M (Dmax+1) R)`,

whose CASE-A half `caseAS_293` reads as `(log X)^{−ρ₂₉₃}` up to the descent factor and whose
CASE-B half is `2√2/R + farErr` — at the intended `R = seamRad X = (log X)^{1/16}` the
`6×`-better exponent of ⟦V5⟧. -/
theorem cofactor_Rbd_293 :
    ∃ X₀ X₁ : ℝ, 0 < X₀ ∧ 0 < X₁ ∧
      ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (H : ℝ) (N Xn P Q j M k₀ : ℕ) (Cb X t t₁ Dmax R : ℝ),
        0 ≤ Cb → ShortIntervalDatum Cb →
        X₀ ≤ (k₀ : ℝ) → Real.exp 64 ≤ (k₀ : ℝ) → ballMertensThreshold ≤ (k₀ : ℝ) →
        M ≤ N → (k₀ : ℝ) < ramRbot H Xn j → ramRbot H Xn j ≤ (k₀ : ℝ) + 1 →
        1 < ramRbot H Xn j → ramRbot H Xn j - 1 ≤ (M : ℝ) →
        (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1) → 2 * ramRbot H Xn j < (M : ℝ) + 3 →
        (M : ℝ) ≤ X →
        (1 / 32 - theta293) * Real.log (Real.log X)
          ≤ (1 / 16) * Real.log (Real.log (k₀ : ℝ)) →
        (∀ k : ℕ, k₀ ≤ k → k ≤ M → |t| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ 3 * X) →
        Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → X₁ ≤ X →
        P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        0 < R → R ≤ |t - t₁| → |t - t₁| ≤ Dmax →
        0 ≤ cofactorMfl X theta293 (k₀ : ℝ) →
        2 / ramRbot H Xn j
          ≤ cofactorRbd (1 / Real.exp 1) Cb X theta293 (k₀ : ℝ) (M : ℝ) (Dmax + 1) R / 3 →
        ‖ramR H N Xn P Q j (ellLin g) t‖
          ≤ cofactorRbd (1 / Real.exp 1) Cb X theta293 (k₀ : ℝ) (M : ℝ) (Dmax + 1) R := by
  obtain ⟨X₀, C, hX₀0, hmain⟩ := cofactor_Rbd
  obtain ⟨X₁, hX₁0, hgate⟩ := collisionGate_discharged C
  refine ⟨X₀, X₁, hX₀0, hX₁0, ?_⟩
  intro g hg H N Xn P Q j M k₀ Cb X t t₁ Dmax R hCb0 hCbound hX₀k hk₀64 hk₀th hMN hk₀lo hk₀hi
    hbot hlow hhigh hMtop hMX hll hTcont hX hLX hX₁X hPlow hQhigh hPQ ht₁ hrow hR0 hfar hDmax
    hMfl0 hend
  have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [show 2 * (1 / Real.exp 1) = 2 / Real.exp 1 from by ring,
      div_lt_one (Real.exp_pos 1)]
    exact he2
  exact hmain g hg H N Xn P Q j M k₀ (1 / Real.exp 1) Cb X theta293 t t₁ Dmax R hc0 le_rfl
    hc1 hCb0 hCbound hX₀k hk₀64 hk₀th hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hMX hll hTcont
    hX hLX theta293_pos (le_of_lt theta293_lt_one_div_32) hPlow hQhigh hPQ ht₁ hrow
    (hgate X hX₁X) hR0 hfar hDmax hMfl0 hend

/-! ## §7 (F-3) — THE PRIZE: `tL_main_sumsq` WITH ITS `Rbd` HYPOTHESIS GONE

`USetThinTL.tL_main_sumsq` (U-8's exit) carries the co-factor supply as the named hypothesis

  `0 ≤ Rbd → (∀ t ∈ 𝒯_L, ‖ramR H N X P Q j bb t‖ ≤ Rbd) → …`

— the socket the whole U-7 campaign was opened to fill.  §5 fills it.  The composition below
is the certificate: the `𝒯_L` branch of §8.3's `hU`, at the row datum `bb := ℓ(g)`, with NO
co-factor hypothesis left. -/

/-- **F-3 — THE `𝒯_L` EXIT, CO-FACTOR SUPPLY DISCHARGED** (`tL_supply_discharged`).

  `Σ_{t∈𝒯_L} ‖Q_{j,H}·R_{j,H}‖² ≤ 54·C·Rbd₇²·(H/j)²`,
  `Rbd₇ = cofactorRbd c Cb X θ k₀ M (Dmax+1) R = 3·max(2·caseAS …, farSupS …)`,

with the `Rbd` binder of `tL_main_sumsq` DISCHARGED by `cofactor_Rbd` and its nonnegativity
by `cofactorRbd_nonneg`.  Every hypothesis below is either U-8's own (the well-spaced
ordinate set, the `T`/`V`/`L` window, the kill gate) or U-7's own (§5's enumerated union);
none of them mentions the co-factor.

The only genuinely NEW hypothesis is the per-`t` bundle `hTL`: on the `𝒯_L` branch each
ordinate must sit on the row's FAR leg (`R ≤ |t − t₁| ≤ Dmax`, CASE B's radius input) and
inside the contour box (`|t| + T*(k, log k) ≤ 3X`, transport 3).  Both are `𝒰`-side
properties of the ordinate set, stated (law #253) and not assumed away. -/
theorem tL_supply_discharged :
    ∃ Cq cq T₀ X₀ C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (H : ℝ), 2 ≤ H → ∀ (P Q j N Xn M k₀ : ℕ) (cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      H ≤ (j : ℝ) →
      -- U-8's own window
      ∀ (T V L δ' : ℝ) (𝒯 : Finset ℝ), WellSpaced 𝒯 →
      (∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) → T₀ ≤ T → 1 < T →
      3 ≤ ramQbase H P j → (ramQbase H P j : ℝ) ≤ T →
      30 ≤ Real.log T / Real.log (ramQbase H P j) →
      5 ≤ Real.log (Real.log T) → 1 ≤ V → V⁻¹ ≤ δ' →
      Real.log T ≤ L → 1 ≤ Real.log T → Real.exp 1 ≤ L →
      Real.log (ramQbase H P j) ≤ L → Real.log V ≤ 100 * Real.log L →
      420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cq * (Real.log (ramQbase H P j)) ^ 2 →
      -- U-7's own gates (all `t`-free)
      ∀ (cg Cb Xg θ t₁ Dmax R : ℝ),
        0 < cg → cg ≤ 1 / Real.exp 1 → 2 * cg < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        X₀ ≤ (k₀ : ℝ) → Real.exp 64 ≤ (k₀ : ℝ) → ballMertensThreshold ≤ (k₀ : ℝ) →
        M ≤ N → (k₀ : ℝ) < ramRbot H Xn j → ramRbot H Xn j ≤ (k₀ : ℝ) + 1 →
        1 < ramRbot H Xn j → ramRbot H Xn j - 1 ≤ (M : ℝ) →
        (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1) → 2 * ramRbot H Xn j < (M : ℝ) + 3 →
        (M : ℝ) ≤ Xg →
        (1 / 32 - θ) * Real.log (Real.log Xg)
          ≤ (1 / 16) * Real.log (Real.log (k₀ : ℝ)) →
        Real.exp 1 ≤ Xg → Real.exp 1 ≤ Real.log Xg → 0 < θ → θ ≤ 1 / 32 →
        P83 Xg θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 Xg → P ≤ Q → |t₁| ≤ Xg →
        pretDistSq (ellLin g) (costwist t₁) Xg ≤ (1 / 16) * Real.log (Real.log Xg) →
        collisionGate Xg 25 C → 0 < R →
        0 ≤ cofactorMfl Xg θ (k₀ : ℝ) →
        2 / ramRbot H Xn j
          ≤ cofactorRbd cg Cb Xg θ (k₀ : ℝ) (M : ℝ) (Dmax + 1) R / 3 →
        -- the per-`t` gates on the `𝒯_L` branch: the far leg and the contour box
        (∀ t ∈ tLset H P Q j cf δ' 𝒯, R ≤ |t - t₁| ∧ |t - t₁| ≤ Dmax ∧
          ∀ k : ℕ, k₀ ≤ k → k ≤ M → |t| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ 3 * Xg) →
        ∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N Xn P Q (ellLin g) cf j t‖ ^ 2
          ≤ 54 * Cq * cofactorRbd cg Cb Xg θ (k₀ : ℝ) (M : ℝ) (Dmax + 1) R ^ 2
              * (H / (j : ℝ)) ^ 2 := by
  obtain ⟨Cq, cq, T₀, hCq, hcq, hT₀, htL⟩ := tL_main_sumsq
  obtain ⟨X₀, C, hX₀0, hRbd⟩ := cofactor_Rbd
  refine ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, ?_⟩
  intro g hg H hH P Q j N Xn M k₀ cf hcf1 hHj T V L δ' 𝒯 hws hsub hT₀T hT hB3 hBT hκ30 hLL5
    hV1 hVδ hTL hlogT1 hLe hWL hlogV hkill cg Cb Xg θ t₁ Dmax R hc0 hce hc1 hCb0 hCbound
    hX₀k hk₀64 hk₀th hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hMX hll hX hLX hθ0 hθ32 hPlow
    hQhigh hPQ ht₁ hrow hgate hR0 hMfl0 hend hper
  have hk₀1 : (1 : ℝ) ≤ (k₀ : ℝ) := by
    have h65 : (65 : ℝ) ≤ (k₀ : ℝ) := by
      linarith [Real.add_one_le_exp (64 : ℝ), hk₀64]
    linarith
  refine htL H hH P Q j N Xn cf (ellLin g) hcf1 hHj T V L δ'
    (cofactorRbd cg Cb Xg θ (k₀ : ℝ) (M : ℝ) (Dmax + 1) R) 𝒯 hws hsub hT₀T hT hB3 hBT hκ30
    hLL5 hV1 hVδ hTL hlogT1 hLe hWL hlogV hkill (cofactorRbd_nonneg hc1 hCb0 hk₀1) ?_
  intro t ht
  obtain ⟨hfar, hDmax, hTcont⟩ := hper t ht
  exact hRbd g hg H N Xn P Q j M k₀ cg Cb Xg θ t t₁ Dmax R hc0 hce hc1 hCb0 hCbound hX₀k
    hk₀64 hk₀th hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hMX hll hTcont hX hLX hθ0 hθ32 hPlow
    hQhigh hPQ ht₁ hrow hgate hR0 hfar hDmax hMfl0 hend

end Salt.MR
