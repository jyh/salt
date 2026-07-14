/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.CountClose

/-!
# AB4 — the sharp `pairSet'` and the count-line TRUE close (`tripleSum_le_cbar_final`)

Design: `docs/blueprints/flags.md`, the AB3 entry ("A LANDED DESIGN GAP FLAGGED", **catch #55**).

The landed `pairSet`/`S2set` (`Salt.Chen.TripleCount`) cut the inner `p₂`-window at
`p₂² ≤ x` (`p₂ ≤ √x`), whereas BJS Lemma 52 — and the landed `cbar` — correspond to the
SHARP admissible cutoff `p₂ ≤ √(x/p₁)` (forced, since any triple has `p₁p₂² ≤ p₁p₂p₃ ≤ x`;
pairs with `p₂ > √(x/p₁)` have `U = ⌊x/p₁p₂⌋ < p₂`, i.e. an EMPTY `p₃`-fibre).  Those extra
pairs carry positive weight `1/(p₁p₂·log(x/p₁p₂))` in `weightedPairSum`, and their mass — the
BJS (187) tail — is `Θ(1/log x)`, NOT `o(1/log x)`, so the landed chain over-counts by the
constant `∫_{1/8}^{1/3}(1/β)(1/(1−β))log(1/(1−2β)) dβ ≈ 0.744` (a genuine `~3×` overshoot,
`0.554` vs `c̄/2 ≈ 0.1815`).

**This file installs the fix at the sharp cutoff** (all in a NEW file — no landed node is
edited).  It re-runs the whole count line against

  `pairSet' x z y` : `z ≤ p₁ ≤ y < p₂`, both prime, with the SHARP inner cutoff
  `p₁·p₂² ≤ x`  (`q.1 * (q.2 * q.2) ≤ x`).

The projection `tripleSet → pairSet'` STILL lands in it (`p₁p₂² ≤ p₁p₂p₃ ≤ x`), so the
`card_tripleSet_le_pairSum` reduction re-proves; and since `pairSet' ⊆ pairSet` (a stricter
cutoff), `per_pair_weighted_le` transfers verbatim.  The `p₁`-dependent inner window is

  `S2set' x y p₁` : `y < p₂`, `p₁·p₂² ≤ x`, prime  (i.e. `p₂ ≤ √(x/p₁)`),

and `pairSet'` FIBERS over `p₁` as `S1set ×ᵈ S2set'(p₁)` (`pairSet'_fiber`,
`weightedPairSum'_fibered`).

## The (187)-tail finding (executor-verified)

At the SHARP cutoff the tail does NOT survive as a `Θ(1/log x)` term.  The inner Abel pass
(`applicationA`) is run over the p₁-dependent window `primesInWindow yR (√(x/p₁))`, whose
integral `∫_{yR}^{√(x/p₁)} h_{p₁}/(t log t)` IS exactly `Ifun x yR p₁` (`Ifun`'s upper limit is
`√(N/u) = √(x/p₁)`).  So **the (187) tail integral VANISHES** — it is replaced by a single
boundary prime `⌊√(x/p₁)⌋₊` (the one prime that can sit exactly at `p₂ = √(x/p₁)`), whose
contribution `h_{p₁}(pb)/pb = O(x^{-1/6}/log x)` is `o(1/log x)` per fibre.  The `√(x/p₁)+1`
sliver of the AB3 wide tail is thus avoided entirely.

## Composition (SW4)

`Salt.Chen.mainA3_of_hBVswitch` carries `tripleSum x z y` symbolically; the numeric re-gate
consumes a `tripleSum ≤ (c̄/2 + o(1))·x/log x`-form.  `weightedPairSum'_le_cbar` (the analytic
heart) gives `weightedPairSum' ≤ c̄/log x + O(1/log²x)` and `tripleSum_le_cbar_final` composes it
with the count reduction into the leading `(c̄/2)`-form.

No `sorry`, no `native_decide`, no new axioms.
-/

open Salt.LS ArithmeticFunction
open MeasureTheory intervalIntegral Set
open scoped BigOperators

namespace Salt.Chen

/-! ## Section 1 — the sharp definitions -/

/-- The SHARP `p₁`-dependent inner `p₂`-window: `y < p₂`, `p₁·p₂² ≤ x` (i.e. `p₂ ≤ √(x/p₁)`),
prime.  This is BJS (185)'s admissible cutoff; the landed `S2set` uses the looser `p₂² ≤ x`. -/
def S2set' (x y p₁ : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun p => y < p ∧ p₁ * (p * p) ≤ x ∧ p.Prime)

/-- The SHARP admissible pair set: `z ≤ p₁ ≤ y < p₂`, both prime, with the sharp inner cutoff
`p₁·p₂² ≤ x` (`q.1 * (q.2 * q.2) ≤ x`).  Contains `proj(tripleSet)` (`p₁p₂² ≤ p₁p₂p₃ ≤ x`) and
is contained in the landed `pairSet` (a stricter cutoff). -/
def pairSet' (x z y : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 x ×ˢ Finset.Icc 1 x)).filter
    (fun q => z ≤ q.1 ∧ q.1 ≤ y ∧ y < q.2 ∧ q.1 * (q.2 * q.2) ≤ x ∧ q.1.Prime ∧ q.2.Prime)

/-- The SHARP c̄-weighted pair reciprocal sum
`Σ_{(p₁,p₂) ∈ pairSet'} 1/(p₁p₂·log(N/p₁p₂))`. -/
noncomputable def weightedPairSum' (x z y : ℕ) : ℝ :=
  ∑ q ∈ pairSet' x z y, 1 / ((q.1 : ℝ) * q.2 * logND x q)

/-! ## Section 2 — `pairSet' ⊆ pairSet` and the three re-proofs at the sharp cutoff -/

/-- **The sharp set is stricter.**  `pairSet' x z y ⊆ pairSet x z y`: the sharp cutoff
`p₁·p₂² ≤ x` implies the loose one `p₂² ≤ x` (since `p₁ ≥ 1`). -/
theorem pairSet'_subset_pairSet (x z y : ℕ) : pairSet' x z y ⊆ pairSet x z y := by
  intro q hq
  rw [pairSet', Finset.mem_filter] at hq
  rw [pairSet, Finset.mem_filter]
  obtain ⟨hmem, hz1, hy1, hy2, hsharp, hp1, hp2⟩ := hq
  refine ⟨hmem, hz1, hy1, hy2, ?_, hp1, hp2⟩
  -- `q.2 * q.2 ≤ q.1 * (q.2 * q.2) ≤ x`, using `1 ≤ q.1`
  calc q.2 * q.2 ≤ q.1 * (q.2 * q.2) := Nat.le_mul_of_pos_left _ hp1.pos
    _ ≤ x := hsharp

/-- **Step 1 at the sharp cutoff.**  `per_pair_weighted_le` transfers verbatim to `pairSet'`
via the subset (its proof only uses `q.2 ≤ √x`, which the stricter cutoff still gives). -/
theorem per_pair_weighted_le' {K : ℝ} (hK0 : 0 ≤ K)
    (hpsi : ∀ n : ℕ, 3 ≤ n → |psiTot n - (n : ℝ)| ≤ K * n / Real.log n)
    {x z y : ℕ} (hLval4 : 4 ≤ Real.log (Lval x y)) {q : ℕ × ℕ} (hq : q ∈ pairSet' x z y) :
    primeCountIoc (Lfun x q) (Ufun x q)
      ≤ (1 + 3 * K / Real.log (Lval x y))
          * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x y : ℝ)))
          * ((x : ℝ) / 2) * (1 / ((q.1 : ℝ) * q.2 * logND x q))
        + 1 / Real.log (Lval x y) :=
  per_pair_weighted_le hK0 hpsi hLval4 (pairSet'_subset_pairSet x z y hq)

/-- **The projection reduction at the sharp cutoff.**  `#{admissible triples} ≤ Σ_{pairSet'}
#{p₃ ∈ (L,U]}`.  The projection `tripleSet → pairSet'` lands in `pairSet'`
(`p₁p₂² ≤ p₁p₂p₃ ≤ x`); the per-fibre MapsTo/InjOn is identical to the landed
`card_tripleSet_le_pairSum` (it never touches the inner cutoff). -/
theorem card_tripleSet_le_pairSum' (x z y : ℕ) :
    ((tripleSet x z y).card : ℝ)
      ≤ ∑ q ∈ pairSet' x z y, primeCountIoc (Lfun x q) (Ufun x q) := by
  classical
  have Hmem : ∀ t ∈ tripleSet x z y, (t.1, t.2.1) ∈ pairSet' x z y := by
    intro t ht
    rw [tripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
    obtain ⟨⟨ht1, ht21, _⟩, hz1, hy1, hy2, h23, hp1, hp2, _hp3, _hlo, hhi⟩ := ht
    rw [pairSet', Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨ht1, ht21⟩, hz1, hy1, hy2, ?_, hp1, hp2⟩
    -- SHARP: `p₁·p₂² ≤ p₁·p₂·p₃ = prod ≤ x`
    calc t.1 * (t.2.1 * t.2.1) ≤ t.1 * (t.2.1 * t.2.2) := by gcongr
      _ = prod3 t := by rw [prod3]; ring
      _ ≤ x := hhi
  rw [Finset.card_eq_sum_card_fiberwise Hmem]
  push_cast
  refine Finset.sum_le_sum (fun q _hq => ?_)
  rw [primeCountIoc]
  refine Nat.cast_le.mpr ?_
  refine Finset.card_le_card_of_injOn (fun t => t.2.2) ?_ ?_
  · -- MapsTo: each fibre element's p₃ lands in the prime window (L, U]  (identical to landed)
    intro t ht
    rw [Finset.mem_coe, Finset.mem_filter] at ht
    obtain ⟨htmem, hprojq⟩ := ht
    have hq1 : q.1 = t.1 := by rw [← hprojq]
    have hq2 : q.2 = t.2.1 := by rw [← hprojq]
    rw [tripleSet, Finset.mem_filter] at htmem
    obtain ⟨_, _, _, _, _, hp1, hp2, hp3, hlo, hhi⟩ := htmem
    have hden : 0 < q.1 * q.2 := by rw [hq1, hq2]; exact Nat.mul_pos hp1.pos hp2.pos
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, hp3⟩
    · rw [Lfun]
      by_contra hle
      rw [not_lt] at hle
      have hden2 : 0 < 2 * q.1 * q.2 := by
        rw [hq1, hq2]; exact Nat.mul_pos (Nat.mul_pos (by norm_num) hp1.pos) hp2.pos
      have hmul : t.2.2 * (2 * q.1 * q.2) ≤ x := (Nat.le_div_iff_mul_le hden2).mp hle
      rw [hq1, hq2] at hmul
      have heq : 2 * prod3 t = t.2.2 * (2 * t.1 * t.2.1) := by rw [prod3]; ring
      omega
    · rw [Ufun]
      refine (Nat.le_div_iff_mul_le hden).mpr ?_
      rw [hq1, hq2]
      calc t.2.2 * (t.1 * t.2.1) = prod3 t := by rw [prod3]; ring
        _ ≤ x := hhi
  · -- InjOn (identical to landed)
    intro t ht t' ht' heq
    rw [Finset.mem_coe, Finset.mem_filter] at ht ht'
    obtain ⟨ht1, ht2⟩ := Prod.ext_iff.mp (ht.2.trans ht'.2.symm)
    exact Prod.ext ht1 (Prod.ext ht2 heq)

/-- **The C3d headline (reduction form) at the sharp cutoff.**
`tripleSum x z y ≤ Σ_{pairSet'} #{p₃ ∈ (L,U]}`. -/
theorem triple_count_le_pairSum' (x z y : ℕ) :
    tripleSum x z y ≤ ∑ q ∈ pairSet' x z y, primeCountIoc (Lfun x q) (Ufun x q) := by
  rw [tripleSum_eq_card]; exact card_tripleSet_le_pairSum' x z y

/-- **Step 2 at the sharp cutoff.**  `tripleSum` bounded by the SHARP c̄-weighted double sum
`weightedPairSum'` plus the `|pairSet'|/L₀` remainder — the exact input the two Abel passes
consume at the sharp window.  Mirrors the landed `tripleSum_le_weighted_pairSum`. -/
theorem tripleSum_le_weighted_pairSum' {x z y : ℕ}
    (hLval4 : 4 ≤ Real.log (Lval x y)) :
    ∃ K : ℝ, 0 ≤ K ∧
      tripleSum x z y ≤
        (1 + 3 * K / Real.log (Lval x y))
            * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x y : ℝ)))
            * ((x : ℝ) / 2) * weightedPairSum' x z y
        + ((pairSet' x z y).card : ℝ) / Real.log (Lval x y) := by
  obtain ⟨K, hK0, hpsi⟩ := psiTot_pnt
  refine ⟨K, hK0, ?_⟩
  have hstep : ∀ q ∈ pairSet' x z y,
      primeCountIoc (Lfun x q) (Ufun x q)
        ≤ (1 + 3 * K / Real.log (Lval x y))
            * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x y : ℝ))) * ((x : ℝ) / 2)
            * (1 / ((q.1 : ℝ) * q.2 * logND x q)) + 1 / Real.log (Lval x y) :=
    fun q hq => per_pair_weighted_le' hK0 hpsi hLval4 hq
  calc tripleSum x z y
      ≤ ∑ q ∈ pairSet' x z y, primeCountIoc (Lfun x q) (Ufun x q) :=
        triple_count_le_pairSum' x z y
    _ ≤ ∑ q ∈ pairSet' x z y, ((1 + 3 * K / Real.log (Lval x y))
            * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x y : ℝ))) * ((x : ℝ) / 2)
            * (1 / ((q.1 : ℝ) * q.2 * logND x q)) + 1 / Real.log (Lval x y)) :=
        Finset.sum_le_sum hstep
    _ = (1 + 3 * K / Real.log (Lval x y))
          * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x y : ℝ))) * ((x : ℝ) / 2)
          * weightedPairSum' x z y
        + ((pairSet' x z y).card : ℝ) / Real.log (Lval x y) := by
        rw [weightedPairSum', Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          nsmul_eq_mul, mul_one_div]

/-! ## Section 3 — the fibered re-index and the sharp inner bridge -/

/-- **`pairSet'` fibers over `p₁`.**  `q ∈ pairSet' x z y ↔ q.1 ∈ S1set x z y ∧
q.2 ∈ S2set' x y q.1`.  The outer window `S1set` is unchanged; the inner window
`S2set'(p₁)` carries the sharp `p₁`-dependent cutoff. -/
theorem pairSet'_fiber (x z y : ℕ) (q : ℕ × ℕ) :
    q ∈ pairSet' x z y ↔ q.1 ∈ S1set x z y ∧ q.2 ∈ S2set' x y q.1 := by
  simp only [pairSet', S1set, S2set', Finset.mem_filter, Finset.mem_product]
  tauto

/-- **The fibered re-index (sharp).**  `weightedPairSum'` factors over `p₁` into the inner
`p₂`-Abel-pass carrier at the SHARP window:
`weightedPairSum' = Σ_{p₁ ∈ S1set}(1/p₁)·Σ_{p₂ ∈ S2set'(p₁)} h_{p₁}(p₂)/p₂`.
The sharp analogue of the landed `weightedPairSum_fibered`; uses `Finset.sum_finset_product`
(the fiber is `p₁`-dependent, so `pairSet'` does not factor as a plain product). -/
theorem weightedPairSum'_fibered (x z y : ℕ) :
    weightedPairSum' x z y
      = ∑ p₁ ∈ S1set x z y, (1 / (p₁ : ℝ))
          * ∑ p₂ ∈ S2set' x y p₁, hbjs (x : ℝ) (p₁ : ℝ) (p₂ : ℝ) / (p₂ : ℝ) := by
  rw [weightedPairSum',
    Finset.sum_finset_product (pairSet' x z y) (S1set x z y) (fun p₁ => S2set' x y p₁)
      (fun p => pairSet'_fiber x z y p)]
  refine Finset.sum_congr rfl (fun p₁ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p₂ _ => ?_)
  simp only [hbjs, logND]
  ring

/-- `∑_{insert a s} f ≤ f a + ∑_s f` for `0 ≤ f a` (folding the boundary prime). -/
private lemma sum_insert_le_add {s : Finset ℕ} {a : ℕ} {f : ℕ → ℝ} (hfa : 0 ≤ f a) :
    ∑ i ∈ insert a s, f i ≤ f a + ∑ i ∈ s, f i := by
  by_cases h : a ∈ s
  · rw [Finset.insert_eq_of_mem h]; linarith
  · rw [Finset.sum_insert h]

/-- **The sharp inner bridge.**  The `p₁`-dependent ℕ-window `S2set' x yN p₁` (`yN < p₂`,
`p₁p₂² ≤ x`, i.e. `p₂ ≤ √(x/p₁)`) is contained in `primesInWindow yR (√(x/p₁))` together with
the single boundary prime `⌊√(x/p₁)⌋₊` (the one prime that can sit exactly at
`p₂ = √(x/p₁)`), whenever `yR ≤ yN + 1`.  This is the sharp analogue of AB3's
`S2set_subset_primesInWindow`: at the sharp cutoff the Abel window's upper limit is EXACTLY
`√(x/p₁) = Ifun`'s upper limit, so the (187) tail integral vanishes — replaced by one prime. -/
theorem S2set'_subset_insert {x yN p₁ : ℕ} {yR : ℝ}
    (hyR : yR ≤ (yN : ℝ) + 1) (hp1 : 0 < p₁) :
    S2set' x yN p₁ ⊆ insert (⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊)
      (Salt.BrunLower.primesInWindow yR (Real.sqrt ((x : ℝ) / (p₁ : ℝ)))) := by
  intro p hp
  rw [S2set', Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨_, hyp, hpx, hpp⟩ := hp
  have hp1R : (0 : ℝ) < (p₁ : ℝ) := by exact_mod_cast hp1
  have hpxR : (p₁ : ℝ) * ((p : ℝ) * (p : ℝ)) ≤ (x : ℝ) := by exact_mod_cast hpx
  have hp2x : (p : ℝ) * (p : ℝ) ≤ (x : ℝ) / (p₁ : ℝ) := by
    rw [le_div_iff₀ hp1R]; nlinarith [hpxR]
  have hple : (p : ℝ) ≤ Real.sqrt ((x : ℝ) / (p₁ : ℝ)) := by
    rw [← Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ (p : ℝ))]
    exact Real.sqrt_le_sqrt hp2x
  have hyRp : yR ≤ (p : ℝ) := by
    have : (yN : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast (by omega : yN + 1 ≤ p)
    linarith
  rw [Finset.mem_insert]
  rcases lt_or_eq_of_le hple with hlt | heq
  · -- interior prime `p < √(x/p₁)`
    refine Or.inr ?_
    rw [Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_ceil.mpr hlt, hpp, hyRp⟩
  · -- boundary prime `p = √(x/p₁)`, so `p = ⌊√(x/p₁)⌋₊`
    exact Or.inl (by rw [← heq, Nat.floor_natCast])

/-- Nonnegativity of the inner Abel summand `h_{p₁}(q)/q` whenever `p₁·q < x` and `1 ≤ q`
(then `x/(p₁q) > 1`, so `h_{p₁}(q) = 1/log(x/(p₁q)) > 0`). -/
private lemma hbjs_div_nonneg {x p₁ q : ℕ} (hp1 : 0 < p₁) (hq1 : 1 ≤ q)
    (hpq : (p₁ : ℝ) * (q : ℝ) < (x : ℝ)) :
    0 ≤ hbjs (x : ℝ) (p₁ : ℝ) (q : ℝ) / (q : ℝ) := by
  have hp1R : (0 : ℝ) < (p₁ : ℝ) := by exact_mod_cast hp1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hpqpos : (0 : ℝ) < (p₁ : ℝ) * (q : ℝ) := mul_pos hp1R hqpos
  have hgt1 : (1 : ℝ) < (x : ℝ) / ((p₁ : ℝ) * (q : ℝ)) := by rw [lt_div_iff₀ hpqpos]; linarith
  have hlogpos : 0 < Real.log ((x : ℝ) / ((p₁ : ℝ) * (q : ℝ))) := Real.log_pos hgt1
  rw [hbjs]
  exact div_nonneg (inv_nonneg.mpr hlogpos.le) hqpos.le

/-- **The per-fibre inner bound (the sharp inner Abel pass + the vanished-tail finding).**
For the sharp inner window `S2set' x yN p₁` under the applicationA hypotheses at the sharp
upper limit `w = √(x/p₁)` (verified: `p₁·w = √(x·p₁) < x` reduces to `p₁ < x`):

  `Σ_{p₂ ∈ S2set'(p₁)} h_{p₁}(p₂)/p₂ ≤ h_{p₁}(pb)/pb + I(p₁) + (21/log yR)·h_{p₁}(w)`,

where `pb = ⌊√(x/p₁)⌋₊` is the SINGLE boundary prime that replaces AB3's (187) tail integral
(which VANISHES here — the Abel window's upper limit is exactly `Ifun`'s), and `I(p₁) =
Ifun x yR p₁ = ∫_{yR}^{√(x/p₁)} h_{p₁}/(t log t)`.  Composes `S2set'_subset_insert`,
`sum_insert_le_add`, and `applicationA`. -/
theorem inner_fiber_le {x yN p₁ : ℕ} {yR : ℝ}
    (hyR_lo : yR ≤ (yN : ℝ) + 1) (hyR2 : 2 ≤ yR)
    (hyw : yR ≤ Real.sqrt ((x : ℝ) / (p₁ : ℝ))) (hp1 : 0 < p₁)
    (hpwN : (p₁ : ℝ) * Real.sqrt ((x : ℝ) / (p₁ : ℝ)) < (x : ℝ)) :
    ∑ p₂ ∈ S2set' x yN p₁, hbjs (x : ℝ) (p₁ : ℝ) (p₂ : ℝ) / (p₂ : ℝ)
      ≤ hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
            / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
        + Ifun (x : ℝ) yR (p₁ : ℝ)
        + (21 / Real.log yR) * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) := by
  have hp1R : (0 : ℝ) < (p₁ : ℝ) := by exact_mod_cast hp1
  set w : ℝ := Real.sqrt ((x : ℝ) / (p₁ : ℝ)) with hw
  have hwpos : 0 < w := by linarith [hyw, hyR2]
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have : (0 : ℝ) < (p₁ : ℝ) * w := mul_pos hp1R hwpos; linarith [hpwN]
  -- the inner Abel pass over `primesInWindow yR w`
  have happA := applicationA (N := (x : ℝ)) (p := (p₁ : ℝ)) (y := yR) (w := w) hyR2 hyw hp1R hpwN
  -- the Abel integral IS `Ifun x yR p₁`  (the sharp window = `Ifun`'s upper limit)
  have hIfun : Ifun (x : ℝ) yR (p₁ : ℝ)
      = ∫ t in yR..w, hbjs (x : ℝ) (p₁ : ℝ) t / (t * Real.log t) := by rw [Ifun, hw]
  -- the sharp inner bridge, folded to `w`
  have hsub : S2set' x yN p₁ ⊆ insert (⌊w⌋₊) (Salt.BrunLower.primesInWindow yR w) := by
    have h := S2set'_subset_insert (x := x) (yN := yN) (p₁ := p₁) (yR := yR) hyR_lo hp1
    rwa [← hw] at h
  -- nonnegativity of the summand on the enlarged index set
  have hnn : ∀ i ∈ insert (⌊w⌋₊) (Salt.BrunLower.primesInWindow yR w),
      0 ≤ hbjs (x : ℝ) (p₁ : ℝ) (i : ℝ) / (i : ℝ) := by
    intro i hi
    rw [Finset.mem_insert] at hi
    rcases hi with hi | hi
    · subst hi
      have hfw : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le hwpos.le
      have h1pb : 1 ≤ ⌊w⌋₊ := Nat.le_floor (by push_cast; linarith [hyw, hyR2] : ((1 : ℕ) : ℝ) ≤ w)
      have hpb : (p₁ : ℝ) * (⌊w⌋₊ : ℝ) < (x : ℝ) := by
        have := mul_le_mul_of_nonneg_left hfw hp1R.le; linarith [hpwN]
      exact hbjs_div_nonneg hp1 h1pb hpb
    · rw [Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hlt, _hip, hyi⟩ := hi
      have hiw : (i : ℝ) < w := Nat.lt_ceil.mp hlt
      have h1i : 1 ≤ i := by exact_mod_cast (show (1 : ℝ) ≤ (i : ℝ) by linarith [hyi, hyR2])
      have hpi : (p₁ : ℝ) * (i : ℝ) < (x : ℝ) := by
        have := mul_lt_mul_of_pos_left hiw hp1R; linarith [hpwN]
      exact hbjs_div_nonneg hp1 h1i hpi
  -- assemble
  calc ∑ p₂ ∈ S2set' x yN p₁, hbjs (x : ℝ) (p₁ : ℝ) (p₂ : ℝ) / (p₂ : ℝ)
      ≤ ∑ p₂ ∈ insert (⌊w⌋₊) (Salt.BrunLower.primesInWindow yR w),
          hbjs (x : ℝ) (p₁ : ℝ) (p₂ : ℝ) / (p₂ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hnn i hi)
    _ ≤ hbjs (x : ℝ) (p₁ : ℝ) (⌊w⌋₊ : ℝ) / (⌊w⌋₊ : ℝ)
          + ∑ p₂ ∈ Salt.BrunLower.primesInWindow yR w,
              hbjs (x : ℝ) (p₁ : ℝ) (p₂ : ℝ) / (p₂ : ℝ) :=
        sum_insert_le_add (hnn _ (Finset.mem_insert_self _ _))
    _ ≤ hbjs (x : ℝ) (p₁ : ℝ) (⌊w⌋₊ : ℝ) / (⌊w⌋₊ : ℝ)
          + ((∫ t in yR..w, hbjs (x : ℝ) (p₁ : ℝ) t / (t * Real.log t))
              + (21 / Real.log yR) * hbjs (x : ℝ) (p₁ : ℝ) w) := by linarith [happA]
    _ = hbjs (x : ℝ) (p₁ : ℝ) (⌊w⌋₊ : ℝ) / (⌊w⌋₊ : ℝ) + Ifun (x : ℝ) yR (p₁ : ℝ)
          + (21 / Real.log yR) * hbjs (x : ℝ) (p₁ : ℝ) w := by rw [hIfun]; ring

/-! ## Section 4 — the outer pass and the analytic heart -/

/-- **The per-fibre window hypotheses.**  From the operating relations `log p₁ ≤ log x/3`,
`log yR = log x/3` (i.e. `p₁ ≤ yR = x^{1/3}`), the two `applicationA` conditions at the sharp
upper limit hold: `yR ≤ √(x/p₁)` (since `p₁ ≤ x^{1/3}`) and `p₁·√(x/p₁) < x` (reduces to
`p₁² < x`). -/
private lemma fiber_window {x : ℕ} {yR p₁R : ℝ}
    (hx1 : 1 < (x : ℝ)) (hyR0 : 0 < yR) (hlogy : Real.log yR = Real.log x / 3)
    (hp1ge1 : 1 ≤ p₁R) (hp1log : Real.log p₁R ≤ Real.log x / 3) :
    yR ≤ Real.sqrt ((x : ℝ) / p₁R) ∧ p₁R * Real.sqrt ((x : ℝ) / p₁R) < (x : ℝ) := by
  have hp1R : 0 < p₁R := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos hx1
  have hxp1 : 0 < (x : ℝ) / p₁R := div_pos hxpos hp1R
  have hsqpos : 0 < Real.sqrt ((x : ℝ) / p₁R) := Real.sqrt_pos.mpr hxp1
  have hlogsqrt : Real.log (Real.sqrt ((x : ℝ) / p₁R)) = (Real.log x - Real.log p₁R) / 2 := by
    rw [Real.log_sqrt hxp1.le, Real.log_div hxpos.ne' hp1R.ne']
  refine ⟨?_, ?_⟩
  · -- yR ≤ √(x/p₁): via logs
    rw [← Real.log_le_log_iff hyR0 hsqpos, hlogsqrt, hlogy]; linarith
  · -- p₁·√(x/p₁) < x: via `√(x/p₁) ≤ √x` and `p₁ < √x` (`p₁² < x`)
    have hp1sqlt : p₁R ^ 2 < (x : ℝ) := by
      have hlog2 : Real.log (p₁R ^ 2) < Real.log x := by
        rw [Real.log_pow]; push_cast; nlinarith [hp1log, hLpos]
      have hp2pos : 0 < p₁R ^ 2 := by positivity
      exact (Real.log_lt_log_iff hp2pos hxpos).mp hlog2
    have hp1ltsqrt : p₁R < Real.sqrt (x : ℝ) := (Real.lt_sqrt hp1R.le).mpr hp1sqlt
    have hsqrtx_pos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
    have hdivle : Real.sqrt ((x : ℝ) / p₁R) ≤ Real.sqrt (x : ℝ) :=
      Real.sqrt_le_sqrt (div_le_self hxpos.le hp1ge1)
    calc p₁R * Real.sqrt ((x : ℝ) / p₁R)
        ≤ p₁R * Real.sqrt (x : ℝ) := by
          exact mul_le_mul_of_nonneg_left hdivle hp1R.le
      _ < Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
          mul_lt_mul_of_pos_right hp1ltsqrt hsqrtx_pos
      _ = (x : ℝ) := Real.mul_self_sqrt hxpos.le

/-- **The analytic heart (FULL) — the SHARP weighted double sum is `c̄/log x + o(1/log x)`.**
Under the operating relations `z = x^{1/8}`, `y = x^{1/3}` (their real carriers `zR`, `yR`) with
the ℕ-carrier bridges, the sharp weighted double sum satisfies

  `weightedPairSum' x zN yN ≤ c̄/log x + [outer corrections] + Σ_{p₁} (1/p₁)·[inner corrections]`,

where the correction terms — the two outer boundary primes `zN`, `yN`, the outer Abel error
`(21/log zR)·I(zR)`, and per fibre the sharp boundary prime `⌊√(x/p₁)⌋₊` and the inner Abel
error `(21/log yR)·h_{p₁}(√(x/p₁))` — are each `o(1/log x)` (see `weightedPairSum'_correction_le`).
This is the sharp-cutoff FIX of catch #55: the leading constant is `c̄`, not `c̄ + 0.744`.
Composes `weightedPairSum'_fibered`, `inner_fiber_le` per fibre (via `fiber_window`), the outer
bridge `S1set_subset_insert`, `applicationB`, and `Ifun_integral_eq_cbar`. -/
theorem weightedPairSum'_le_cbar {x zN yN : ℕ} {zR yR : ℝ}
    (hx1 : 1 < (x : ℝ))
    (hzR2 : 2 ≤ zR) (hzRyR : zR ≤ yR)
    (hlogz : Real.log zR = Real.log x / 8) (hlogy : Real.log yR = Real.log x / 3)
    (hzN_le : (zN : ℝ) ≤ zR) (hzN_ge : zR ≤ (zN : ℝ) + 1)
    (hyN_le : (yN : ℝ) ≤ yR) (hyN_ge : yR ≤ (yN : ℝ) + 1) :
    weightedPairSum' x zN yN
      ≤ cbar / Real.log x
        + ( Ifun (x : ℝ) yR (zN : ℝ) / (zN : ℝ) + Ifun (x : ℝ) yR (yN : ℝ) / (yN : ℝ)
            + (21 / Real.log zR) * Ifun (x : ℝ) yR zR )
        + ∑ p₁ ∈ S1set x zN yN, (1 / (p₁ : ℝ))
            * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                  / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                + (21 / Real.log yR)
                    * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) ) := by
  have hLpos : 0 < Real.log x := Real.log_pos hx1
  have hyR0 : 0 < yR := by linarith
  have hzR0 : 0 < zR := by linarith
  have hyR2 : (2 : ℝ) ≤ yR := by linarith
  -- per-fibre data for `p₁ ∈ S1set`
  have hfiber : ∀ p₁ ∈ S1set x zN yN,
      0 < p₁ ∧ (1 : ℝ) ≤ (p₁ : ℝ) ∧ Real.log (p₁ : ℝ) ≤ Real.log x / 3
        ∧ yR ≤ Real.sqrt ((x : ℝ) / (p₁ : ℝ))
        ∧ (p₁ : ℝ) * Real.sqrt ((x : ℝ) / (p₁ : ℝ)) < (x : ℝ) := by
    intro p₁ hp
    rw [S1set, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨_, _⟩, _hzp, hpyN, hpp⟩ := hp
    have hp1pos : 0 < p₁ := hpp.pos
    have hp1ge1 : (1 : ℝ) ≤ (p₁ : ℝ) := by exact_mod_cast hp1pos
    have hp1le : (p₁ : ℝ) ≤ yR := le_trans (by exact_mod_cast hpyN) hyN_le
    have hp1log : Real.log (p₁ : ℝ) ≤ Real.log x / 3 := by
      rw [← hlogy]; exact Real.log_le_log (by linarith) hp1le
    obtain ⟨hyw, hpwN⟩ := fiber_window hx1 hyR0 hlogy hp1ge1 hp1log
    exact ⟨hp1pos, hp1ge1, hp1log, hyw, hpwN⟩
  -- STEP 1: bound the inner sum per fibre (× 1/p₁), splitting off `Ifun`
  have hstep : ∀ p₁ ∈ S1set x zN yN,
      (1 / (p₁ : ℝ)) * ∑ p₂ ∈ S2set' x yN p₁, hbjs (x : ℝ) (p₁ : ℝ) (p₂ : ℝ) / (p₂ : ℝ)
        ≤ (1 / (p₁ : ℝ)) * Ifun (x : ℝ) yR (p₁ : ℝ)
          + (1 / (p₁ : ℝ)) * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
              + (21 / Real.log yR)
                  * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) ) := by
    intro p₁ hp
    obtain ⟨hp1pos, hp1ge1, _, hyw, hpwN⟩ := hfiber p₁ hp
    have hinv : (0 : ℝ) ≤ 1 / (p₁ : ℝ) := by positivity
    have hib := inner_fiber_le (x := x) (yN := yN) (p₁ := p₁) (yR := yR) hyN_ge hyR2 hyw hp1pos hpwN
    calc (1 / (p₁ : ℝ)) * ∑ p₂ ∈ S2set' x yN p₁, hbjs (x : ℝ) (p₁ : ℝ) (p₂ : ℝ) / (p₂ : ℝ)
        ≤ (1 / (p₁ : ℝ)) * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
              + Ifun (x : ℝ) yR (p₁ : ℝ)
              + (21 / Real.log yR) * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) ) :=
          mul_le_mul_of_nonneg_left hib hinv
      _ = _ := by ring
  -- OUTER: bound `Σ_{S1set} (1/p₁)·Ifun` via the outer bridge + applicationB + cbar identity
  have houter : ∑ p₁ ∈ S1set x zN yN, (1 / (p₁ : ℝ)) * Ifun (x : ℝ) yR (p₁ : ℝ)
      ≤ Ifun (x : ℝ) yR (zN : ℝ) / (zN : ℝ) + Ifun (x : ℝ) yR (yN : ℝ) / (yN : ℝ)
        + (cbar / Real.log x + (21 / Real.log zR) * Ifun (x : ℝ) yR zR) := by
    -- nonnegativity of `(1/p₁)·Ifun` for `p₁` with `0 < p₁`, `log p₁ ≤ log x/3`
    have hg_nonneg : ∀ p₁ : ℕ, 0 < p₁ → Real.log (p₁ : ℝ) ≤ Real.log x / 3 →
        0 ≤ (1 / (p₁ : ℝ)) * Ifun (x : ℝ) yR (p₁ : ℝ) := by
      intro p₁ hp1pos hp1log
      have hp1R : (0 : ℝ) < (p₁ : ℝ) := by exact_mod_cast hp1pos
      have hIfun_nn : 0 ≤ Ifun (x : ℝ) yR (p₁ : ℝ) :=
        Ifun_nonneg hx1 hyR0 hlogy hp1R hp1log
      positivity
    -- membership-side nonneg on `insert zN (insert yN (primesInWindow zR yR))`
    have hzN_pos : 0 < zN := by
      have : (1 : ℝ) ≤ (zN : ℝ) := by linarith [hzN_ge, hzR2]
      exact_mod_cast this
    have hyN_pos : 0 < yN := by
      have : (1 : ℝ) ≤ (yN : ℝ) := by linarith [hyN_ge, hzR2, hzRyR]
      exact_mod_cast this
    have hzN_log : Real.log (zN : ℝ) ≤ Real.log x / 3 := by
      rw [← hlogy]; exact Real.log_le_log (by exact_mod_cast hzN_pos) (le_trans hzN_le hzRyR)
    have hyN_log : Real.log (yN : ℝ) ≤ Real.log x / 3 := by
      rw [← hlogy]; exact Real.log_le_log (by exact_mod_cast hyN_pos) hyN_le
    have hnn_ins : ∀ i ∈ insert zN (insert yN (Salt.BrunLower.primesInWindow zR yR)),
        0 ≤ (1 / (i : ℝ)) * Ifun (x : ℝ) yR (i : ℝ) := by
      intro i hi
      rw [Finset.mem_insert, Finset.mem_insert] at hi
      rcases hi with hi | hi | hi
      · rw [hi]; exact hg_nonneg zN hzN_pos hzN_log
      · rw [hi]; exact hg_nonneg yN hyN_pos hyN_log
      · rw [Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_range] at hi
        obtain ⟨hlt, hip, hyi⟩ := hi
        have hiw : (i : ℝ) < yR := Nat.lt_ceil.mp hlt
        have hipos : 0 < i := hip.pos
        have hilog : Real.log (i : ℝ) ≤ Real.log x / 3 := by
          rw [← hlogy]; exact le_of_lt (Real.log_lt_log (by exact_mod_cast hipos) hiw)
        exact hg_nonneg i hipos hilog
    -- the outer PW-sum via applicationB (rewriting `(1/p₁)·Ifun = Ifun/p₁`)
    have hPWeq : ∑ p₁ ∈ Salt.BrunLower.primesInWindow zR yR,
          (1 / (p₁ : ℝ)) * Ifun (x : ℝ) yR (p₁ : ℝ)
        = ∑ p₁ ∈ Salt.BrunLower.primesInWindow zR yR, Ifun (x : ℝ) yR (p₁ : ℝ) / (p₁ : ℝ) :=
      Finset.sum_congr rfl (fun p₁ _ => by ring)
    have happB := applicationB hx1 hyR0 hlogy hzR2 hzRyR hlogz
    have hcbar := Ifun_integral_eq_cbar hx1 hyR0 hlogy hzR0 hlogz
    have hPW : ∑ p₁ ∈ Salt.BrunLower.primesInWindow zR yR, (1 / (p₁ : ℝ)) * Ifun (x : ℝ) yR (p₁ : ℝ)
        ≤ cbar / Real.log x + (21 / Real.log zR) * Ifun (x : ℝ) yR zR := by
      rw [hPWeq]; rw [← hcbar]; exact happB
    -- fold the two boundary primes
    calc ∑ p₁ ∈ S1set x zN yN, (1 / (p₁ : ℝ)) * Ifun (x : ℝ) yR (p₁ : ℝ)
        ≤ ∑ p₁ ∈ insert zN (insert yN (Salt.BrunLower.primesInWindow zR yR)),
            (1 / (p₁ : ℝ)) * Ifun (x : ℝ) yR (p₁ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (S1set_subset_insert hzN_ge hyN_le)
            (fun i hi _ => hnn_ins i hi)
      _ ≤ (1 / (zN : ℝ)) * Ifun (x : ℝ) yR (zN : ℝ)
            + ∑ p₁ ∈ insert yN (Salt.BrunLower.primesInWindow zR yR),
                (1 / (p₁ : ℝ)) * Ifun (x : ℝ) yR (p₁ : ℝ) :=
          sum_insert_le_add (hg_nonneg zN hzN_pos hzN_log)
      _ ≤ (1 / (zN : ℝ)) * Ifun (x : ℝ) yR (zN : ℝ)
            + ( (1 / (yN : ℝ)) * Ifun (x : ℝ) yR (yN : ℝ)
                + ∑ p₁ ∈ Salt.BrunLower.primesInWindow zR yR,
                    (1 / (p₁ : ℝ)) * Ifun (x : ℝ) yR (p₁ : ℝ) ) := by
          have := sum_insert_le_add (s := Salt.BrunLower.primesInWindow zR yR) (a := yN)
            (f := fun p₁ => (1 / (p₁ : ℝ)) * Ifun (x : ℝ) yR (p₁ : ℝ))
            (hg_nonneg yN hyN_pos hyN_log)
          linarith [this]
      _ ≤ Ifun (x : ℝ) yR (zN : ℝ) / (zN : ℝ) + Ifun (x : ℝ) yR (yN : ℝ) / (yN : ℝ)
            + (cbar / Real.log x + (21 / Real.log zR) * Ifun (x : ℝ) yR zR) := by
          have e1 : (1 / (zN : ℝ)) * Ifun (x : ℝ) yR (zN : ℝ)
              = Ifun (x : ℝ) yR (zN : ℝ) / (zN : ℝ) := by ring
          have e2 : (1 / (yN : ℝ)) * Ifun (x : ℝ) yR (yN : ℝ)
              = Ifun (x : ℝ) yR (yN : ℝ) / (yN : ℝ) := by ring
          rw [e1, e2]; linarith [hPW]
  -- ASSEMBLE
  rw [weightedPairSum'_fibered]
  calc ∑ p₁ ∈ S1set x zN yN, (1 / (p₁ : ℝ))
          * ∑ p₂ ∈ S2set' x yN p₁, hbjs (x : ℝ) (p₁ : ℝ) (p₂ : ℝ) / (p₂ : ℝ)
      ≤ ∑ p₁ ∈ S1set x zN yN, ( (1 / (p₁ : ℝ)) * Ifun (x : ℝ) yR (p₁ : ℝ)
          + (1 / (p₁ : ℝ)) * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
              + (21 / Real.log yR) * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) ) ) :=
        Finset.sum_le_sum hstep
    _ = (∑ p₁ ∈ S1set x zN yN, (1 / (p₁ : ℝ)) * Ifun (x : ℝ) yR (p₁ : ℝ))
        + ∑ p₁ ∈ S1set x zN yN, (1 / (p₁ : ℝ))
            * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                  / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                + (21 / Real.log yR) * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) ) :=
        Finset.sum_add_distrib
    _ ≤ _ := by linarith [houter]

/-! ## Section 5 — `tripleSum_le_cbar_final`: the count line's TRUE close at `c̄/2` -/

/-- **AB4 — `tripleSum_le_cbar_final`, the sharp-cutoff count close.**  Composing the sharp
count reduction `tripleSum_le_weighted_pairSum'` with the analytic heart
`weightedPairSum'_le_cbar`, the switch count is bounded with the LEADING constant `c̄/2`
(NOT the landed `pairSet`'s `0.554 ≈ (c̄+0.744)/2` — catch #55 FIXED):

  `tripleSum ≤ (1 + 3K/L₀)(1 + W₀)·(c̄/2)·(x/log x) + Rem`,

with `L₀ = log⌊x/(2y√x)⌋`, `W₀ = 4log2/log(2·⌊x/(2y√x)⌋)`, `K` the unconditional PNT-error
constant, and `Rem = (1 + 3K/L₀)(1 + W₀)·(x/2)·[corrections] + |pairSet'|/L₀ ≥ 0` the lower-order
pieces (the two outer boundary primes, the outer/inner Abel errors, `|pairSet'|/L₀` — each
`o(x/log x)`; see `weightedPairSum'_le_cbar`).  The operating relations are supplied by the SW4
gate (as for the landed `triple_count_le`).  The multiplicative slack `(1 + 3K/L₀)(1 + W₀) → 1`. -/
theorem tripleSum_le_cbar_final {x zN yN : ℕ} {zR yR : ℝ}
    (hx1 : 1 < (x : ℝ))
    (hzR2 : 2 ≤ zR) (hzRyR : zR ≤ yR)
    (hlogz : Real.log zR = Real.log x / 8) (hlogy : Real.log yR = Real.log x / 3)
    (hzN_le : (zN : ℝ) ≤ zR) (hzN_ge : zR ≤ (zN : ℝ) + 1)
    (hyN_le : (yN : ℝ) ≤ yR) (hyN_ge : yR ≤ (yN : ℝ) + 1)
    (hLval4 : 4 ≤ Real.log (Lval x yN)) :
    ∃ K : ℝ, 0 ≤ K ∧
      tripleSum x zN yN
        ≤ (1 + 3 * K / Real.log (Lval x yN))
              * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)))
              * (cbar / 2) * ((x : ℝ) / Real.log x)
          + ( (1 + 3 * K / Real.log (Lval x yN))
                * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)))
                * ((x : ℝ) / 2)
                * ( ( Ifun (x : ℝ) yR (zN : ℝ) / (zN : ℝ) + Ifun (x : ℝ) yR (yN : ℝ) / (yN : ℝ)
                      + (21 / Real.log zR) * Ifun (x : ℝ) yR zR )
                    + ∑ p₁ ∈ S1set x zN yN, (1 / (p₁ : ℝ))
                        * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                              / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                            + (21 / Real.log yR)
                                * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) ) )
            + ((pairSet' x zN yN).card : ℝ) / Real.log (Lval x yN) ) := by
  obtain ⟨K, hK0, hbound⟩ := tripleSum_le_weighted_pairSum' (x := x) (z := zN) (y := yN) hLval4
  refine ⟨K, hK0, ?_⟩
  have hwps := weightedPairSum'_le_cbar hx1 hzR2 hzRyR hlogz hlogy hzN_le hzN_ge hyN_le hyN_ge
  have hL₀pos : 0 < Real.log (Lval x yN) := by linarith [hLval4]
  have hLvalgt1 : (1 : ℝ) < (Lval x yN : ℝ) := by
    by_contra h
    have := Real.log_nonpos (by positivity) (not_lt.mp h)
    linarith [hLval4]
  have h2Lpos : 0 < Real.log (2 * (Lval x yN : ℝ)) :=
    Real.log_pos (by linarith [hLvalgt1])
  have hA₁ : 0 ≤ 1 + 3 * K / Real.log (Lval x yN) := by
    have : 0 ≤ 3 * K / Real.log (Lval x yN) := div_nonneg (by linarith [hK0]) hL₀pos.le
    linarith
  have hA₂ : 0 ≤ 1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)) := by
    have h2 : 0 ≤ 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)) :=
      div_nonneg (by positivity) h2Lpos.le
    linarith
  have hcoef : 0 ≤ (1 + 3 * K / Real.log (Lval x yN))
      * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ))) * ((x : ℝ) / 2) := by
    apply mul_nonneg (mul_nonneg hA₁ hA₂); linarith [hx1]
  have hmul := mul_le_mul_of_nonneg_left hwps hcoef
  calc tripleSum x zN yN
      ≤ (1 + 3 * K / Real.log (Lval x yN))
            * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)))
            * ((x : ℝ) / 2) * weightedPairSum' x zN yN
          + ((pairSet' x zN yN).card : ℝ) / Real.log (Lval x yN) := hbound
    _ ≤ (1 + 3 * K / Real.log (Lval x yN))
            * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)))
            * ((x : ℝ) / 2)
            * ( cbar / Real.log x
                + ( ( Ifun (x : ℝ) yR (zN : ℝ) / (zN : ℝ) + Ifun (x : ℝ) yR (yN : ℝ) / (yN : ℝ)
                      + (21 / Real.log zR) * Ifun (x : ℝ) yR zR )
                    + ∑ p₁ ∈ S1set x zN yN, (1 / (p₁ : ℝ))
                        * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                              / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                            + (21 / Real.log yR)
                                * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) ) ) )
          + ((pairSet' x zN yN).card : ℝ) / Real.log (Lval x yN) := by linarith [hmul]
    _ = _ := by ring

end Salt.Chen
