/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SeamBallWeighted
import Salt.MR.JointHead

/-!
# A-4 — the `hpret` supply: the concrete pointwise `supF` majorant

The HCENTER ladder's node **A-4** (`docs/exploration/hsup-design.md`, ⟦THE HCENTER FREEZE⟧
+ ⟦HCENTER AMENDMENT V2⟧): the discharge of `JointHead.sigma_wiring`'s `hpret` socket with
a CONCRETE majorant for the joint head's `𝒮·𝓛` sup object, built from the landed B-ladder.

## The socket

`JointHead.sigma_wiring` (:271) carries

```
(hpret : ∀ σ ∈ Icc (1 / L) (2 * η), Fbound σ ≤ Real.exp (-M) * L)
```

and the `Fbound` there is the `σ = β + 1/L` reparametrisation of `joint_cs_factoring`'s
per-`(α,β)` sup binder (:195)

```
(hsupF : ∀ α ∈ Icc (0:ℝ) η, ∀ β ∈ Icc (0:ℝ) η, ∀ t : ℝ,
    ‖smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ supF α β)
```

The JointHead docstring's "PENDING" note on that socket is STALE (freeze, retired herewith):
`SupF.head_sigma_bound` (:818, σ-uniform, general `g`) and `SupF.smooth_ratio_bound` (:403,
ABSOLUTE constant) both landed since, so `hpret` is a **re-shape** of landed estimates, not a
new estimate.

## The chain (the freeze's, as landed here)

For `s = c₀ + (t−t₀)i` with `c₀ > 1` and `α, β ∈ [0, 1/log y]`:

1. **the mixed-argument reduction** — `SupF.smooth_ratio_bound` moves the smooth leg from the
   line `c₀−α−β` (whose real part may be `< 1`) to the safe line `c₀+β`, at the cost of the
   ABSOLUTE `C_S = exp(6e³(1 + (log 4 + 4)))`;
2. **the product identity** — `HalaszRepAsm.lseries_ellLin_eq_smooth_mul_large` collapses
   `𝒮(s+β)·𝓛(s+β)` to the single L-series `LSeries (ellLin g) (s+β)` (legal: `Re(s+β) > 1`);
3. **the head decay** — `SupF.head_sigma_bound` at `σ = c₀ − 1 + β` gives
   `C_F·(1/σ)·exp(−(1/e)·𝔻²(1, ℓ·p^{−i(t−t₀)}; e^{1/σ}))`, `C_F = exp(cpeel + (log 4 + cpeel))`;
   the `1/e` is the exponent this route's supply CARRIES (the `p^{−σ} ≥ 1/e` termwise cut) —
   it is not re-graded here;
4. **the distance floor** — `SupF.scale_floor` (:869) trades the frozen scale `e^{1/σ}` for
   `X` at the cost `−2·log(σ·log X) − 48`.

**The order is load-bearing** (the banked HalaszDirect page): the `c`-downgrade
`exp(−(1/e)𝔻²) ≤ exp(−c·𝔻²)` (legal by `𝔻² ≥ 0`) comes BEFORE the floor — applying the floor
first would need `𝔻²(X) − 2log(σL) − 48 ≥ 0`, false near the top of the σ-range.

## THE M-SHAPE (⟦AMENDMENT V2⟧ item 4, the R-1e kill)

The exits carry the **explicit** `pretDistSq (ellLin g) (costwist (t−t₀)) X` (P1) or a
consumer-supplied floor `M` for it (P2/P3).  **No `M_range`, no numeric exponent, no bare
power**: the consumer picks the `M` and owns the numerals, exactly as the two-M / S-3
discipline requires.  Nothing in this file cites `sigma_cutoff_pretentious_half`.

## What lands here

* `head_dist_floor_gen` [P1a] — the M-FREE clone of `HalaszDirect.window_sup_decay_gen`:
  the head decay with the distance term explicit (no `M_range`, hence no window binder).
* `supF_pret_pointwise` [P1] — the composed pointwise bound for the **mixed product**
  `𝒮(s−α−β)·𝓛(s+β)`, i.e. the object `joint_cs_factoring`'s `supF` binder names.
* `supF_pret_majorant_sigma` [P2] — the same bound reparametrised to the σ-line
  (`c₀ = 1 + 1/log X`, `β = σ − 1/log X`), in the `∀ σ ∈ Icc (1/L) b, Fbound σ ≤ majorant`
  shape `sigma_wiring`'s `hpret` demands, with the floor `M` carried as a per-`t` antecedent.
* `smooth_euler_product` [SF-0's residual] — `smoothSeries y g w = smoothEuler y g w` at
  EVERY `w : ℂ`, the bridge SupF names but does not land.
* `joint_sigma_integral` [P3] — the σ-integrated exit via
  `SeamBallWeighted.sigma_cutoff_pretentious_gen`: the flat (no `(1+M)`) form, at a GENERAL
  `c` and a FREE `M`.

## `smooth_euler_product` — SF-0's named residual, LANDED here (no socket)

`SupF`'s SF-0 block is stated on the finite Euler product `smoothEuler` and NOT on
`smoothSeries`, with the deviation recorded in its own docstring (`SupF` :256-264):

> SF-0 is stated on the FINITE Euler product `smoothEuler`, which is entire and equals
> `smoothSeries` at `Re > 1` (**`smooth_euler_product` when landed**).

Without that bridge the mixed-argument reduction cannot reach the joint head's object at all
(the `supF` binder is written on `smoothSeries`).  It is landed here — and UNCONDITIONALLY,
at every `w : ℂ`, not merely on `Re > 1`: `ellLin (restrictBelow y g)` has FINITE support (the
`y`-smooth squarefree numbers, i.e. the products over subsets of `{p ≤ y}`), so `smoothSeries`
is a finite sum at every `w`, and `Finset.prod_add` over `P.powerset` reindexes
`∏_{p≤y}(1 + g p·p^{−w})` to exactly that sum along `T ↦ ∏T` (`Nat.primeFactors_prod` /
`Nat.prod_primeFactors_of_squarefree` are the two halves of the bijection).  Nothing in this
file is conditional on an unproved analytic input.

## The residual this file does NOT close (recorded, not papered over)

`joint_cs_factoring`'s `hsupF` quantifies over **all** `t : ℝ`, while the pretentious decay is
`t`-dependent through `𝔻²(ℓ, p^{it}; X)`.  A `t`-uniform `supF` therefore needs a floor valid
on the WHOLE line, not on a window — precisely the two-M architecture item the freeze routed
to JYH.  P2 states the floor as a per-`t` antecedent so that either resolution (a global floor,
or the A-10 ball-centre dichotomy) instantiates it without a statement change.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set

/-! ## §0 — the local re-derivations

Three landed pages are `private` to their own files (`GrandComp` / `HalaszDirect`); they are
re-derived here byte-for-byte, exactly as `HalaszDirect` re-derives `GrandComp`'s twist
lemma.  No statement is changed. -/

/-- Local copy of `GrandComp.dist_triv_left_eq` / `HalaszDirect.dist_triv_left_eq_local`
(`private` in both): the trivial-left-datum distance `𝔻²(1, f·costwist(−t); X)` equals
`𝔻²(f, costwist t; X)`. -/
private lemma dist_triv_left_eq_pret (f : ℕ → ℂ) (t X : ℝ) :
    pretDistSq (fun _ => 1) (fun n => f n * costwist (-t) n) X
      = pretDistSq f (costwist t) X := by
  unfold pretDistSq
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hre : ((fun _ => (1 : ℂ)) p
        * (starRingEnd ℂ) ((fun n => f n * costwist (-t) n) p)).re
      = (f p * (starRingEnd ℂ) (costwist t p)).re := by
    simp only [one_mul, Complex.conj_re, costwist_conj]
  rw [hre]

/-- **Idempotence of the squarefree linearization.**  `ℓ(ℓ(g)) = ℓ(g)`: `ellLin` reads its
datum only at primes, and `ellLin g p = g p` there (`ellLin_apply_prime`).  This is what lets
`head_sigma_bound` — whose datum hypothesis is the GLOBAL `∀ n, ‖g n‖ ≤ 1` — be applied to
`LSeries (ellLin g)` from the corpus-standard PRIME bound on `g` (via `ellLin_norm_le_one`). -/
private lemma ellLin_idem (g : ℕ → ℂ) : ellLin (ellLin g) = ellLin g := by
  funext n
  change (if n = 0 then 0 else if Squarefree n then ∏ p ∈ n.primeFactors, ellLin g p else 0)
      = (if n = 0 then 0 else if Squarefree n then ∏ p ∈ n.primeFactors, g p else 0)
  split_ifs with _ _
  · rfl
  · exact Finset.prod_congr rfl
      (fun p hp => ellLin_apply_prime g (Nat.prime_of_mem_primeFactors hp))
  · rfl

/-- Local copy of `HalaszDirect.sigma_core_intervalIntegrable` (`private` there): the σ-cutoff
integrand `σ ↦ σ^{−2}·exp(−c(M − 2log(σL) − 48))` is interval-integrable on `[1/L, b]`. -/
private lemma sigma_core_integrable_pret {c L M b : ℝ} (hL : 0 < L) (hb : 1 / L ≤ b) :
    IntervalIntegrable
      (fun σ : ℝ => (1 / σ ^ 2) * Real.exp (-c * (M - 2 * Real.log (σ * L) - 48)))
      volume (1 / L) b := by
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hpos : ∀ σ ∈ Set.uIcc (1 / L) b, (0 : ℝ) < σ := by
    intro σ hσ
    rw [Set.uIcc_of_le hb, Set.mem_Icc] at hσ
    exact lt_of_lt_of_le hLinv0 hσ.1
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.mul ?_ ?_
  · exact continuousOn_const.div (continuousOn_pow 2) (fun σ hσ => pow_ne_zero 2 (hpos σ hσ).ne')
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul (ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_)
      continuousOn_const)
    exact continuousOn_const.mul (ContinuousOn.log
      ((continuous_id.mul continuous_const).continuousOn)
      (fun σ hσ => (mul_pos (hpos σ hσ) hL).ne'))

/-! ## §0.5 — SF-0's bridge: `smoothSeries = smoothEuler` (`smooth_euler_product`)

The identity `SupF` :262 names ("`smooth_euler_product` when landed") and needs, but does not
land.  It holds at EVERY `w : ℂ` — there is no abscissa here: the smooth coefficient is
supported on the products over subsets of `{p ≤ y}`, a finite set. -/

/-- A product of distinct primes is squarefree. -/
private lemma squarefree_prod_primes :
    ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) → Squarefree (∏ p ∈ s, p) := by
  intro s
  induction s using Finset.cons_induction with
  | empty => intro _; simp
  | cons a s ha ih =>
      intro hs
      have hap : a.Prime := hs a (Finset.mem_cons_self a s)
      have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_cons_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
        Nat.Coprime.prod_right (fun q hq =>
          (Nat.coprime_primes hap (hs' q hq)).mpr (by rintro rfl; exact ha hq))
      rw [Finset.prod_cons, Nat.squarefree_mul_iff]
      exact ⟨hcop, hap.squarefree, ih hs'⟩

/-- `n^{−s}` across a `Finset` product of naturals (`natCast_mul_cpow`, iterated). -/
private lemma natCast_prod_cpow (s : Finset ℕ) (w : ℂ) :
    ((∏ p ∈ s, p : ℕ) : ℂ) ^ w = ∏ p ∈ s, ((p : ℕ) : ℂ) ^ w := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s _ha ih => rw [Finset.prod_cons, Finset.prod_cons, natCast_mul_cpow, ih]

/-- `ℓ` at a product of distinct primes is the product of the datum's values there. -/
private lemma ellLin_prod_primes (h : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    ellLin h (∏ p ∈ s, p) = ∏ p ∈ s, h p := by
  have hsq : Squarefree (∏ p ∈ s, p) := squarefree_prod_primes s hs
  simp only [ellLin, if_neg hsq.ne_zero, if_pos hsq, Nat.primeFactors_prod hs]

/-- **SF-0's bridge** (`smooth_euler_product`).  The smooth Dirichlet series and the finite
smooth Euler product agree at EVERY `w : ℂ`:

  `smoothSeries y g w = smoothEuler y g w`.

`SupF` (:250-264) states its SF-0 ratio bound on `smoothEuler` precisely because
`smoothSeries` is a `tsum` that could a priori be junk below its abscissa, and names this
identity as the missing link ("when landed").  There is in fact NO abscissa issue: the
coefficient `ellLin (restrictBelow y g)` vanishes off the products `∏T` over subsets
`T ⊆ {p ≤ y}` (a finite family), so the `tsum` is a finite sum everywhere.

Proof: `Finset.prod_add` expands `∏_{p≤y}(1 + g p·p^{−w})` over `P.powerset`;
`tsum_eq_sum` collapses the L-series to the image of `P.powerset` under `T ↦ ∏T`;
`Nat.primeFactors_prod` gives injectivity of that map (and `Nat.prod_primeFactors_of_squarefree`
its surjectivity onto the support), and `natCast_prod_cpow` matches the two summands. -/
theorem smooth_euler_product (y : ℝ) (g : ℕ → ℂ) (w : ℂ) :
    smoothSeries y g w = smoothEuler y g w := by
  classical
  set P : Finset ℕ := (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime with hP
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hPle : ∀ p ∈ P, (p : ℝ) ≤ y := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_range] at hp
    have hple : p ≤ ⌊y⌋₊ := by omega
    have hpos : 0 < ⌊y⌋₊ := lt_of_lt_of_le hp.2.pos hple
    have h1y : (1 : ℝ) ≤ y := Nat.floor_pos.mp hpos
    calc (p : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hple
      _ ≤ y := Nat.floor_le (by linarith)
  have hrb : ∀ p ∈ P, restrictBelow y g p = g p := by
    intro p hp
    unfold restrictBelow
    rw [if_pos (hPle p hp)]
  -- the Euler side: expand the finite product over the powerset
  have hEuler : smoothEuler y g w
      = ∑ T ∈ P.powerset, ∏ p ∈ T, (g p * ((p : ℕ) : ℂ) ^ (-w)) := by
    rw [smoothEuler, ← hP,
      Finset.prod_congr rfl (fun p _ => add_comm (1 : ℂ) (g p * ((p : ℕ) : ℂ) ^ (-w))),
      Finset.prod_add (fun p => g p * ((p : ℕ) : ℂ) ^ (-w)) (fun _ => 1) P]
    simp
  -- the L-series side: the coefficient is supported on the products over subsets of `P`
  have hinj : ∀ T₁ ∈ P.powerset, ∀ T₂ ∈ P.powerset,
      (∏ p ∈ T₁, p) = (∏ p ∈ T₂, p) → T₁ = T₂ := by
    intro T₁ h₁ T₂ h₂ heq
    have p₁ : ∀ p ∈ T₁, p.Prime := fun p hp => hPprime p (Finset.mem_powerset.mp h₁ hp)
    have p₂ : ∀ p ∈ T₂, p.Prime := fun p hp => hPprime p (Finset.mem_powerset.mp h₂ hp)
    rw [← Nat.primeFactors_prod p₁, ← Nat.primeFactors_prod p₂, heq]
  have hsupp : ∀ n ∉ P.powerset.image (fun T => ∏ p ∈ T, p),
      LSeries.term (ellLin (restrictBelow y g)) w n = 0 := by
    intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term]
    rw [LSeries.term_of_ne_zero hn0]
    have hz : ellLin (restrictBelow y g) n = 0 := by
      by_contra hne
      apply hn
      have hsq : Squarefree n := by
        by_contra hsq
        exact hne (by simp only [ellLin, if_neg hn0, if_neg hsq])
      have hprod : (∏ p ∈ n.primeFactors, restrictBelow y g p) ≠ 0 := by
        rwa [show ellLin (restrictBelow y g) n
            = ∏ p ∈ n.primeFactors, restrictBelow y g p from by
          simp only [ellLin, if_neg hn0, if_pos hsq]] at hne
      have hsub : n.primeFactors ⊆ P := by
        intro p hp
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpne : restrictBelow y g p ≠ 0 := fun h0 => hprod (Finset.prod_eq_zero hp h0)
        have hpy : (p : ℝ) ≤ y := by
          by_contra hlt
          exact hpne (by unfold restrictBelow; rw [if_neg hlt])
        rw [hP, Finset.mem_filter, Finset.mem_range]
        exact ⟨by have := Nat.le_floor hpy; omega, hpp⟩
      exact Finset.mem_image.mpr ⟨n.primeFactors, Finset.mem_powerset.mpr hsub,
        Nat.prod_primeFactors_of_squarefree hsq⟩
    rw [hz, zero_div]
  have hLS : smoothSeries y g w
      = ∑ T ∈ P.powerset, ∏ p ∈ T, (g p * ((p : ℕ) : ℂ) ^ (-w)) := by
    rw [smoothSeries, LSeries, tsum_eq_sum hsupp, Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun T hT => ?_)
    have hTp : ∀ p ∈ T, p.Prime := fun p hp => hPprime p (Finset.mem_powerset.mp hT hp)
    have hTne : (∏ p ∈ T, p) ≠ 0 := (squarefree_prod_primes T hTp).ne_zero
    rw [LSeries.term_of_ne_zero hTne, ellLin_prod_primes (restrictBelow y g) hTp,
      Finset.prod_congr rfl (fun p hp => hrb p (Finset.mem_powerset.mp hT hp)),
      Finset.prod_mul_distrib, ← natCast_prod_cpow T (-w), Complex.cpow_neg]
    field_simp
  rw [hLS, hEuler]

/-! ## §1 (P1a) — the head decay with the EXPLICIT distance

`HalaszDirect.window_sup_decay_gen` with `M_range` REMOVED: the exit carries
`pretDistSq (ellLin g) (costwist u) X` itself, so no window membership is needed and no
numeral is frozen (the M-shape, ⟦AMENDMENT V2⟧ item 4).  The datum is the bare `ellLin g`
(no `seamCoeff` twist) because the joint head's argument is already centred at `t₀`. -/

/-- **P1a — the M-free head decay** (`head_dist_floor_gen`).  For `g` 1-bounded at primes,
`0 < c ≤ 1/e`, `σ ∈ (0,1]` and `e^{1/σ} ≤ X`,

  `‖L(ℓ)(1+σ+iu)‖ ≤ C_F·(1/σ)·exp(−c·(𝔻²(ℓ, p^{iu}; X) − 2·log(σ·log X) − 48))`,
  `C_F = exp(cpeel + (log 4 + cpeel))`.

Composition: `head_sigma_bound` at the datum `ellLin g` (legal by `ellLin_idem` +
`ellLin_norm_le_one`), its distance rewritten by `dist_triv_left_eq_pret`, then the exponent
chain `c·(𝔻²(X) − 2log(σL) − 48) ≤ c·𝔻²(e^{1/σ}) ≤ (1/e)·𝔻²(e^{1/σ})` — floor first inside
the `c`-scaled bracket, `c ≤ 1/e` applied to the ALREADY-floored nonnegative distance (the
order the HalaszDirect page banks). -/
theorem head_dist_floor_gen {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c u X σ : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hYX : Real.exp (1 / σ) ≤ X) :
    ‖LSeries (ellLin g) (((1 + σ : ℝ) : ℂ) + (u : ℝ) * I)‖
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / σ)
        * Real.exp (-c * (pretDistSq (ellLin g) (costwist u) X
            - 2 * Real.log (σ * Real.log X) - 48)) := by
  have hEllOne : ∀ n : ℕ, ‖ellLin g n‖ ≤ 1 := fun n => ellLin_norm_le_one g hg n
  have hcw : ∀ n : ℕ, ‖costwist u n‖ ≤ 1 := fun n => le_of_eq (costwist_norm u n)
  have hHead := head_sigma_bound (g := ellLin g) hEllOne hσ0 hσ1 u
  rw [ellLin_idem g, dist_triv_left_eq_pret (ellLin g) u (Real.exp (1 / σ))] at hHead
  refine hHead.trans ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (Real.exp_nonneg _) (div_nonneg zero_le_one hσ0.le))
  apply Real.exp_le_exp.mpr
  have hd := scale_floor (f := ellLin g) (g := costwist u) hEllOne hcw hσ0 hσ1 hYX
  have hnn : 0 ≤ pretDistSq (ellLin g) (costwist u) (Real.exp (1 / σ)) :=
    pretDistSq_nonneg _ _ _ hEllOne hcw
  have h1 : c * (pretDistSq (ellLin g) (costwist u) X
        - 2 * Real.log (σ * Real.log X) - 48)
      ≤ c * pretDistSq (ellLin g) (costwist u) (Real.exp (1 / σ)) :=
    mul_le_mul_of_nonneg_left hd hc0.le
  have h2 : c * pretDistSq (ellLin g) (costwist u) (Real.exp (1 / σ))
      ≤ (1 / Real.exp 1) * pretDistSq (ellLin g) (costwist u) (Real.exp (1 / σ)) :=
    mul_le_mul_of_nonneg_right hce hnn
  linarith

/-! ## §2 (P1) — the mixed-argument `supF` majorant

The object is `joint_cs_factoring`'s `hsupF` binder byte-for-byte: the product
`𝒮(s−α−β)·𝓛(s+β)` at `s = c₀ + (t−t₀)i`.  The two legs sit on DIFFERENT lines; the smooth
leg's line may have real part `< 1`.  `smooth_ratio_bound` is exactly the move that fixes
that, and it is the only place the `α`-shift is paid for. -/

/-- **P1 — the composed pointwise `supF` bound** (`supF_pret_pointwise`).  For `g` 1-bounded
at primes, `e ≤ y`, `α, β ∈ [0, 1/log y]`, `c₀ > 1`, `σ := c₀ − 1 + β ∈ (0,1]` and
`e^{1/σ} ≤ X`:

  `‖𝒮(s−α−β)·𝓛(s+β)‖
     ≤ C_S·C_F·(1/σ)·exp(−c·(𝔻²(ℓ, p^{i(t−t₀)}; X) − 2·log(σ·log X) − 48))`

with `C_S = exp(6e³(1 + (log 4 + 4)))` (`smooth_ratio_bound`'s absolute constant) and
`C_F = exp(cpeel + (log 4 + cpeel))` (`head_sigma_bound`'s).  The exponent `c` is free in
`(0, 1/e]`; `1/e` is what the supply carries.

The smooth leg is transported between the `smoothSeries` (L-series) and `smoothEuler`
(finite-product) presentations by `smooth_euler_product` (§0.5) — SF-0's recorded deviation,
closed.  UNCONDITIONAL: no socket. -/
theorem supF_pret_pointwise {g : ℕ → ℂ} {y : ℝ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀ t X c₀ α β : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hy : Real.exp 1 ≤ y) (hc₀ : 1 < c₀) (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β)
    (hαy : α ≤ 1 / Real.log y) (hβy : β ≤ 1 / Real.log y)
    (hσ1 : c₀ - 1 + β ≤ 1) (hYX : Real.exp (1 / (c₀ - 1 + β)) ≤ X) :
    ‖smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ Real.exp (6 * Real.exp 3 * (1 + (Real.log 4 + 4)))
          * Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / (c₀ - 1 + β))
          * Real.exp (-c * (pretDistSq (ellLin g) (costwist (t - t₀)) X
              - 2 * Real.log ((c₀ - 1 + β) * Real.log X) - 48)) := by
  have hσ0 : (0 : ℝ) < c₀ - 1 + β := by linarith
  set s : ℂ := (c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I with hsdef
  have hsre : s.re = c₀ := by rw [hsdef]; simp
  have hs : 1 < s.re := by rw [hsre]; exact hc₀
  have hsβre : 1 < (s + (β : ℂ)).re := by
    rw [Complex.add_re, hsre, Complex.ofReal_re]; linarith
  -- (1) the mixed-argument reduction, transported to the `smoothSeries` presentation
  have hratio := smooth_ratio_bound (g := g) hg hs hy hα0 hβ0 hαy hβy
  simp only [← smooth_euler_product] at hratio
  -- (2) the product identity on the safe line `Re = c₀ + β > 1`
  have hsplit := lseries_ellLin_eq_smooth_mul_large y g hg hsβre
  -- (3)+(4) the head decay with the floored, explicit distance
  have hline : s + (β : ℂ)
      = ((1 + (c₀ - 1 + β) : ℝ) : ℂ) + ((t - t₀ : ℝ) : ℂ) * I := by
    rw [hsdef]; push_cast; ring
  have hhead := head_dist_floor_gen (g := g) hg (c := c) (u := t - t₀) (X := X)
    (σ := c₀ - 1 + β) hc0 hce hσ0 hσ1 hYX
  calc ‖smoothSeries y g (s - (α : ℂ) - (β : ℂ)) * largeSeries y g (s + (β : ℂ))‖
      = ‖smoothSeries y g (s - (α : ℂ) - (β : ℂ))‖ * ‖largeSeries y g (s + (β : ℂ))‖ :=
        norm_mul _ _
    _ ≤ Real.exp (6 * Real.exp 3 * (1 + (Real.log 4 + 4)))
          * ‖smoothSeries y g (s + (β : ℂ))‖ * ‖largeSeries y g (s + (β : ℂ))‖ :=
        mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
    _ = Real.exp (6 * Real.exp 3 * (1 + (Real.log 4 + 4)))
          * ‖smoothSeries y g (s + (β : ℂ)) * largeSeries y g (s + (β : ℂ))‖ := by
        rw [norm_mul]; ring
    _ = Real.exp (6 * Real.exp 3 * (1 + (Real.log 4 + 4)))
          * ‖LSeries (ellLin g) (((1 + (c₀ - 1 + β) : ℝ) : ℂ) + ((t - t₀ : ℝ) : ℂ) * I)‖ := by
        rw [← hline, ← hsplit]
    _ ≤ Real.exp (6 * Real.exp 3 * (1 + (Real.log 4 + 4)))
          * (Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / (c₀ - 1 + β))
            * Real.exp (-c * (pretDistSq (ellLin g) (costwist (t - t₀)) X
              - 2 * Real.log ((c₀ - 1 + β) * Real.log X) - 48))) :=
        mul_le_mul_of_nonneg_left hhead (Real.exp_nonneg _)
    _ = Real.exp (6 * Real.exp 3 * (1 + (Real.log 4 + 4)))
          * Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / (c₀ - 1 + β))
          * Real.exp (-c * (pretDistSq (ellLin g) (costwist (t - t₀)) X
              - 2 * Real.log ((c₀ - 1 + β) * Real.log X) - 48)) := by ring

/-! ## §3 (P2) — the σ-line reparametrisation (the `hpret` shape)

`sigma_wiring`'s `Fbound` lives on the σ-line `σ = β + 1/L`, i.e. at the corpus pin
`c₀ = 1 + 1/log X`.  P2 is P1 there, with the distance replaced by a consumer-supplied floor
`M` carried as a per-`t` ANTECEDENT — the M-shape: no `M_range`, no numeral, the consumer
instantiates. -/

/-- **P2 — the `hpret`-shaped majorant** (`supF_pret_majorant_sigma`).  At the pin
`c₀ = 1 + 1/log X` and `β = σ − 1/log X`, for `σ ∈ [1/log X, 1]`, `α ∈ [0, 1/log y]`,
`β ≤ 1/log y`, and any `M` with `M ≤ 𝔻²(ℓ, p^{i(t−t₀)}; X)`:

  `‖𝒮(s−α−β)·𝓛(s+β)‖ ≤ C_S·C_F·(1/σ)·exp(−c·(M − 2·log(σ·log X) − 48))`.

This is exactly `Fbound σ ≤ majorant` in `sigma_wiring`'s quantifier shape (`∀ σ` supplied by
the consumer's range hypotheses), for the CONCRETE `Fbound` given by the joint head's `𝒮·𝓛`
object.  The `t`-uniformity of a `supF` built from it is the consumer's business: the floor
`hMt` is stated per `t` precisely so that a global floor, a window floor, or the A-10
ball-centre dichotomy each instantiate it without a statement change. -/
theorem supF_pret_majorant_sigma {g : ℕ → ℂ} {y : ℝ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀ t X M σ α : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hy : Real.exp 1 ≤ y) (hX0 : 0 < X) (hLX : 0 < Real.log X)
    (hσlo : 1 / Real.log X ≤ σ) (hσ1 : σ ≤ 1)
    (hα0 : 0 ≤ α) (hαy : α ≤ 1 / Real.log y)
    (hβy : σ - 1 / Real.log X ≤ 1 / Real.log y)
    (hMt : M ≤ pretDistSq (ellLin g) (costwist (t - t₀)) X) :
    ‖smoothSeries y g ((((1 + 1 / Real.log X : ℝ) : ℂ) + ((t - t₀ : ℝ) : ℂ) * I)
          - (α : ℂ) - ((σ - 1 / Real.log X : ℝ) : ℂ))
        * largeSeries y g ((((1 + 1 / Real.log X : ℝ) : ℂ) + ((t - t₀ : ℝ) : ℂ) * I)
          + ((σ - 1 / Real.log X : ℝ) : ℂ))‖
      ≤ Real.exp (6 * Real.exp 3 * (1 + (Real.log 4 + 4)))
          * Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / σ)
          * Real.exp (-c * (M - 2 * Real.log (σ * Real.log X) - 48)) := by
  have hLinv0 : (0 : ℝ) < 1 / Real.log X := by positivity
  have hσ0 : (0 : ℝ) < σ := lt_of_lt_of_le hLinv0 hσlo
  -- the scale condition `e^{1/σ} ≤ X` is automatic on `σ ≥ 1/log X`
  have hinvσ : 1 / σ ≤ Real.log X := by
    have h := one_div_le_one_div_of_le hLinv0 hσlo
    rwa [one_div_one_div] at h
  have hYX : Real.exp (1 / σ) ≤ X := by
    calc Real.exp (1 / σ) ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr hinvσ
      _ = X := Real.exp_log hX0
  have hσeq : (1 + 1 / Real.log X) - 1 + (σ - 1 / Real.log X) = σ := by ring
  have hP1 := supF_pret_pointwise (g := g) (y := y) hg (c := c) (t₀ := t₀) (t := t)
    (X := X) (c₀ := 1 + 1 / Real.log X) (α := α) (β := σ - 1 / Real.log X)
    hc0 hce hy (by linarith) hα0 (by linarith) hαy hβy
    (by rw [hσeq]; exact hσ1) (by rw [hσeq]; exact hYX)
  rw [hσeq] at hP1
  refine hP1.trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (by positivity)
  have : -c * (pretDistSq (ellLin g) (costwist (t - t₀)) X
        - 2 * Real.log (σ * Real.log X) - 48)
      ≤ -c * (M - 2 * Real.log (σ * Real.log X) - 48) := by nlinarith
  exact this

/-! ## §4 (P3) — the σ-integral: the flat exit

The `halasz_direct` pattern (`HalaszDirect` :245-451), run against the JOINT head's majorant.

**THE DELTA over `halasz_direct_gen` / `halasz_direct_ball`.**  Those exits integrate
`‖L(ℓ_seam)(1+σ+it)‖/σ` — the BARE L-series at the seam datum, with `M_range` hard-wired into
the statement and the exponent pinned (`1/e` there, `1/(2e)` in the ball arm).  P3 integrates
an ABSTRACT `Fbound` dominated by the joint head's MIXED-PRODUCT majorant (the `α`-shifted
`𝒮·𝓛` object, so the `C_S` ratio price is inside the constant), at a GENERAL `c` and a FREE
`M`.  It is therefore neither of the two banked arms and cites neither: it cites
`sigma_cutoff_pretentious_gen` at the caller's own `c` (`0 < c`, `2c < 1`), leaving the S-3
citation choice — and every numeral — to the consumer.  Nothing here mentions `_half`. -/

/-- **P3 — the σ-integrated joint-head exit** (`joint_sigma_integral`).  For `log X ≥ 3`,
`1/log X ≤ b`, `0 < c` with `2c < 1`, `M ≥ 0`, a nonnegative constant `CSF` and any `Fbound`
which is (i) interval-integrable against `1/σ` and (ii) dominated by the P2 majorant,

  `∫_{1/logX}^{b} Fbound σ/σ dσ ≤ CSF·(e^{48c}/(1−2c))·e^{−cM}·log X`.

Flat — no `(1+M)` factor: the direct form carries the SCALE of the distance, so the integrand
is `K·σ^{2c−2}` and the σ-integral closes without the GHS two-regime split.  Instantiate
`CSF := C_S·C_F` and `hFb` from `supF_pret_majorant_sigma`. -/
theorem joint_sigma_integral {Fbound : ℝ → ℝ} {c X b M CSF : ℝ}
    (hc0 : 0 < c) (hc1 : 2 * c < 1) (hL : 3 ≤ Real.log X) (hM0 : 0 ≤ M)
    (hCSF : 0 ≤ CSF) (hb : 1 / Real.log X ≤ b)
    (hint : IntervalIntegrable (fun σ => Fbound σ / σ) volume (1 / Real.log X) b)
    (hFb : ∀ σ ∈ Icc (1 / Real.log X) b,
        Fbound σ ≤ CSF * (1 / σ)
          * Real.exp (-c * (M - 2 * Real.log (σ * Real.log X) - 48))) :
    (∫ σ in (1 / Real.log X)..b, Fbound σ / σ)
      ≤ CSF * ((Real.exp (c * 48) / (1 - 2 * c)) * Real.exp (-(c * M)) * Real.log X) := by
  have hLpos : (0 : ℝ) < Real.log X := by linarith
  have hLinv0 : (0 : ℝ) < 1 / Real.log X := by positivity
  have hpoint : ∀ σ ∈ Icc (1 / Real.log X) b,
      Fbound σ / σ
        ≤ CSF * ((1 / σ ^ 2)
            * Real.exp (-c * (M - 2 * Real.log (σ * Real.log X) - 48))) := by
    intro σ hσ
    have hσ0 : (0 : ℝ) < σ := lt_of_lt_of_le hLinv0 hσ.1
    have hσne : σ ≠ 0 := hσ0.ne'
    rw [div_le_iff₀ hσ0]
    refine (hFb σ hσ).trans (le_of_eq ?_)
    field_simp
  have hmaj := (sigma_core_integrable_pret (c := c) (L := Real.log X) (M := M) (b := b)
    hLpos hb).const_mul CSF
  have hmono := intervalIntegral.integral_mono_on hb hint hmaj hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  refine hmono.trans ?_
  exact mul_le_mul_of_nonneg_left
    (sigma_cutoff_pretentious_gen (C := 48) hc0 hc1 hL hM0 (by norm_num) hb) hCSF

end Salt.MR
