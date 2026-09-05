/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.BvL
import Salt.SW.BvWeight
import Salt.Maynard.PhiAtom

/-!
# ARM B part B2, wave **W6b-E** (S5–S10) — the Graham / Barban–Vehov MEAN upper bound
# on the easy half `x ≥ z²`

`Σ_{n ≤ x} w(n) ≤ C·x/log z` for `w(n) = (Σ_{d ∣ n} θ^{(z)}_d)²`, the Graham 1978 /
An 2022 §4 argument with every asymptotic replaced by a one-sided bound: the
lcm-collection regroup (`GrahamL2.lean`), the Selberg diagonalisation, the sharp
pointwise decay `|innerG z g| ≤ C₀/(φ(g)·log z)` (`BvL.lean`, S4), and the landed
`μ²/φ` atom `Σ_{g ≤ z, μ²} 1/φ(g) ≤ 4·log(z+1) + C'` (`Maynard/PhiAtom.lean:861`).

## ⚠ THE HONEST LABEL — this proves strictly LESS than Graham's theorem

**The hypothesis is `x ≥ z²`, not `x ≥ z`.** The elementary route carries an additive
`z²`-shaped error (the pair count IS `z²`, and each `(d,e)` pair carries `O(1)` of
truncation error at the floor `⌊N/m⌋`); only cancellation escapes it, and that
cancellation is the HARD half of Graham's theorem. **The range `z ≤ u < z²` is wave
W6b-H's** (`grahamW_sum_le_full` with `(z:ℝ) ≤ x`, class D, staged and not frozen),
and B2's consumer NEEDS it: Jutila (3.6) reaches
`Σ_{z₁ < n ≤ x} a(n)²·n^{1−2α} ≪ x^{2−2α}` only by partial summation of `S(u)` against
`u^{1−2α}` over EVERY `u ∈ (z₁, x]`, and at the strip's bottom every scale contributes at
full weight. **Neither `grahamW_sum_le` nor `sum_sq_sum_bvWeight_le` at `x ≥ z₂²` feeds
(3.6).**

**Moreover `sum_sq_sum_bvWeight_le`'s hypothesis `(z₂:ℝ)² ≤ x` is UNSATISFIABLE at B2's
ratified closure table** `(ε, b, a₁, a₂, c) = (1/120, 1/10, 3, 7/2, 13/2)`, where
`x = D^{13/2} < z₂² = D^7`. The row as frozen is TRUE and lands; B2 reads it at NO scale
until W6b-H (with H9, the below-level range `z₁ < u < z₂`) supplies the `(z₂:ℝ) ≤ x`
form. **The closure table does not move for it** (the re-pick to `c = 9` is rejected on
the block's own #12: the consumer's loss is at `n ≈ z₁`, a `D`-power independent of `c`).
So **W6b-E feeds nothing of Jutila (3.6) until W6b-H + H9 land.** What it DOES buy: it
retires two corpus declines (`docs/blueprints/flags.md`, DH-LCM and DH-COPBV), it founds
W6b-H (S0–S4 feed H6/H7, S9 is H8's `x ≥ z²` branch), and it changes no binder in B2.

## The cross-track import edge `Salt.SW.GrahamMean → Salt.Maynard.PhiAtom`

RULED IN, and cycle-free at depth 2 (receipt taken at `88f1e114`): `PhiAtom`'s import cone
is exactly `Mathlib`, `Salt.Brun.M3Expansion`, `Salt.Brun.CongruenceCounting`, and both of
those import `Mathlib` only; `grep -rn "^import Salt.SW" Salt/Brun/` is EMPTY, so no
`Salt.Brun` module can reach `Salt.SW`. S5 consumes `phiAtom_upper_lossy` at `B = 1`,
`x = z + 1`.

## Rungs landed here

* **S5** `sum_totient_innerG_sq_le` — the `g`-sum DH-LCM declined:
  `Σ_{g ≤ z} φ(g)·innerG(z,g)² ≤ C₁/log z`.
* **S6** `grahamW_sum_eq_floor` — `Σ_{n ≤ N} w(n) = Σ_{m ≤ N} gc(m)·⌊N/m⌋`
  (`grahamW_mean_eq` with `1/n ↦ 1`; the multiples count is `Nat.Ioc_filter_dvd_card_eq_div`).
* **S7** `sum_grahamGc_div_eq` — `Σ_{m ≤ N} gc(m)/m = Σ_{d,e ≤ z} θ_dθ_e/lcm(d,e)` when
  `z² ≤ N` (every `lcm(d,e) ≤ de ≤ z² ≤ N`, so each pair is counted exactly once).
* **S8/S8′** `sum_abs_grahamTheta_le` (`Σ_{d ≤ z} |θ_d| ≤ z/log z`) and
  `sum_abs_grahamGc_le` (`Σ_m |gc(m)| ≤ (z/log z)²`), the `z²` error.
* **S9** `grahamW_sum_le` — THE KEYSTONE'S EASY HALF.
* **S10** `sum_sq_sum_bvWeight_le` — the same for Jutila's two-level weight, by
  `(u − v)² ≤ 2u² + 2v²` and S9 at both levels.

**F6**: no NET `log` in any numerator — the `log(z+1)` inside S5's atom is divided by the
route's `log z` before it leaves the proof.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no `sorry`.
-/

namespace Salt.SW

open ArithmeticFunction

/-! ## Support bookkeeping for the lcm pair sum -/

/-- Extending a double sum from `S × S` to `T × T` when the summand's support sits inside
`S`. Used twice, in opposite directions, to move `grahamGc`'s pair range between
`m.divisors` and `Icc 1 z`. -/
private lemma double_sum_ext {S T : Finset ℕ} (F : ℕ → ℕ → ℝ) (hST : S ⊆ T)
    (h0 : ∀ d e, F d e ≠ 0 → d ∈ S ∧ e ∈ S) :
    ∑ d ∈ S, ∑ e ∈ S, F d e = ∑ d ∈ T, ∑ e ∈ T, F d e := by
  have step1 : ∀ d, ∑ e ∈ S, F d e = ∑ e ∈ T, F d e := fun d =>
    Finset.sum_subset hST (fun e _ he => by
      by_contra hne; exact he (h0 d e hne).2)
  calc ∑ d ∈ S, ∑ e ∈ S, F d e = ∑ d ∈ S, ∑ e ∈ T, F d e :=
        Finset.sum_congr rfl (fun d _ => step1 d)
    _ = ∑ d ∈ T, ∑ e ∈ T, F d e := by
        refine Finset.sum_subset hST (fun d _ hd => ?_)
        refine Finset.sum_eq_zero (fun e _ => ?_)
        by_contra hne; exact hd (h0 d e hne).1

/-- `gc(m)` with the pair range moved from `m.divisors` to `Icc 1 z`, for `m ≥ 1`. The two
ranges carry the same support: `m = lcm d e` forces `d, e ∣ m` (and `m ≠ 0`), while
`θ_d ≠ 0` forces `1 ≤ d ≤ z`. -/
private lemma grahamGc_eq_Icc {z m : ℕ} (hm : 1 ≤ m) :
    grahamGc z m = ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
      if m = Nat.lcm d e then grahamTheta z d * grahamTheta z e else 0 := by
  set F : ℕ → ℕ → ℝ :=
    fun d e => if m = Nat.lcm d e then grahamTheta z d * grahamTheta z e else 0 with hF
  have hne0 : ∀ d e, F d e ≠ 0 →
      m = Nat.lcm d e ∧ grahamTheta z d ≠ 0 ∧ grahamTheta z e ≠ 0 := by
    intro d e hne
    by_cases hif : m = Nat.lcm d e
    · refine ⟨hif, ?_, ?_⟩
      · intro h; exact hne (by rw [hF]; simp only []; rw [if_pos hif, h, zero_mul])
      · intro h; exact hne (by rw [hF]; simp only []; rw [if_pos hif, h, mul_zero])
    · exact absurd (by rw [hF]; simp only []; rw [if_neg hif]) hne
  have hsupp1 : ∀ d e, F d e ≠ 0 → d ∈ m.divisors ∧ e ∈ m.divisors := by
    intro d e hne
    obtain ⟨hif, -, -⟩ := hne0 d e hne
    exact ⟨Nat.mem_divisors.mpr ⟨by rw [hif]; exact Nat.dvd_lcm_left d e, by omega⟩,
      Nat.mem_divisors.mpr ⟨by rw [hif]; exact Nat.dvd_lcm_right d e, by omega⟩⟩
  have hsupp2 : ∀ d e, F d e ≠ 0 → d ∈ Finset.Icc 1 z ∧ e ∈ Finset.Icc 1 z := by
    intro d e hne
    obtain ⟨-, hd, he⟩ := hne0 d e hne
    have hbd : ∀ c : ℕ, grahamTheta z c ≠ 0 → c ∈ Finset.Icc 1 z := by
      intro c hc
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · rcases Nat.eq_zero_or_pos c with rfl | h
        · exact absurd (grahamTheta_zero z) hc
        · exact h
      · by_contra hcz
        exact hc (grahamTheta_of_lt (not_le.mp hcz))
    exact ⟨hbd d hd, hbd e he⟩
  rw [grahamGc_eq, double_sum_ext F Finset.subset_union_left hsupp1,
    ← double_sum_ext F Finset.subset_union_right hsupp2]

/-! ## S5 — the `g`-sum `Σ_g φ(g)·innerG²` -/

/-- **S5 (the `g`-sum DH-LCM declined).** `∃ C₁ > 0, ∀ z ≥ 2,
`Σ_{g ≤ z} φ(g)·innerG(z,g)² ≤ C₁/log z`.

`innerG z g = 0` off squarefree `g`; on squarefree `g`, S4 gives
`φ(g)·innerG² ≤ C₀²/(φ(g)·log²z)`, so the sum is
`(C₀²/log²z)·Σ_{g ≤ z, μ²} 1/φ(g) ≤ (C₀²/log²z)·(4·log(z+1) + C')` by the landed
`phiAtom_upper_lossy` at `B = 1`, `x = z + 1` (the index of `sqfCop` is `Finset.range x`,
hence the shift; its `C'` is EXISTENTIAL — `4·(φ(1)+1) = 8` is a proof-body witness, not
consumable). Then `log(z+1) ≤ log 2 + log z ≤ 2·log z` for `z ≥ 2`.

**The must-PASS control (§2(a′)).** The squarefree restriction is a CONVENIENCE of the
landed atom, not load-bearing: dropping `μ²(g)` and summing `1/φ(g)` over ALL `g ≤ z`
still gives `≪ log z`, with a worse constant — measured at `z = 2·10⁵`,
`(Σ_{g≤z} 1/φ(g))/log z = 1.939` (all `g`) against `1.109` (squarefree), the ratio
tending to `ζ(2)ζ(3)/ζ(6) = 1.9436`. (This is a docstring receipt, not a Lean row: the
only landed antecedent, `phiAtom_upper_lossy`, sums `sqfCop`, which is squarefree BY
CONSTRUCTION — `PhiAtom.lean:45/:49` — and no all-`g` bound is landed.) -/
theorem sum_totient_innerG_sq_le : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ z : ℕ, 2 ≤ z →
    ∑ g ∈ Finset.Icc 1 z, (Nat.totient g : ℝ) * innerG z g ^ 2 ≤ C₁ / Real.log z := by
  obtain ⟨C₀, hC₀, hS4⟩ := abs_innerG_le_sharp
  obtain ⟨C', hC'⟩ := Salt.Maynard.phiAtom_upper_lossy 1 one_ne_zero
  have hmax : (0 : ℝ) ≤ max C' 0 := le_max_right _ _
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  refine ⟨C₀ ^ 2 * (8 + 2 * max C' 0), mul_pos (pow_pos hC₀ 2) (by linarith), fun z hz => ?_⟩
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hlog2z : Real.log 2 ≤ Real.log (z : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hz)
  -- the termwise bound
  have hterm : ∀ g ∈ Finset.Icc 1 z, (Nat.totient g : ℝ) * innerG z g ^ 2
      ≤ (if Squarefree g then C₀ ^ 2 / ((Nat.totient g : ℝ) * Real.log (z : ℝ) ^ 2) else 0) := by
    intro g hg
    have hg1 : 1 ≤ g := (Finset.mem_Icc.mp hg).1
    by_cases hsf : Squarefree g
    · rw [if_pos hsf]
      have hφR : (0 : ℝ) < (Nat.totient g : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hg1
      have hb := hS4 z hz g hg
      have habs := abs_le.mp hb
      have hsq : innerG z g ^ 2 ≤ (C₀ / ((Nat.totient g : ℝ) * Real.log (z : ℝ))) ^ 2 := by
        nlinarith [habs.1, habs.2]
      calc (Nat.totient g : ℝ) * innerG z g ^ 2
          ≤ (Nat.totient g : ℝ) * (C₀ / ((Nat.totient g : ℝ) * Real.log (z : ℝ))) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hφR.le
        _ = C₀ ^ 2 / ((Nat.totient g : ℝ) * Real.log (z : ℝ) ^ 2) := by
            field_simp
    · rw [if_neg hsf, innerG_eq_zero_of_not_squarefree hsf]
      norm_num
  -- the bridge to the landed `μ²/φ` atom
  have hbridge : (Finset.Icc 1 z).filter (fun g => Squarefree g)
      = Salt.Maynard.sqfCop (z + 1) 1 := by
    ext r
    simp only [Salt.Maynard.sqfCop, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hsf⟩
      exact ⟨by omega, hsf, Nat.coprime_one_right r⟩
    · rintro ⟨hlt, hsf, -⟩
      refine ⟨⟨?_, by omega⟩, hsf⟩
      rcases Nat.eq_zero_or_pos r with rfl | h
      · exact absurd hsf not_squarefree_zero
      · exact h
  have hphi : ∑ g ∈ (Finset.Icc 1 z).filter (fun g => Squarefree g), (1 : ℝ) / (Nat.totient g)
      = Salt.Maynard.phiAtomSum (z + 1) 1 := by
    rw [Salt.Maynard.phiAtomSum, hbridge]
  have hatom := hC' (z + 1) (by omega)
  rw [← hphi] at hatom
  -- `log(z+1) ≤ log 2 + log z ≤ 2 log z`
  have hzz : ((z + 1 : ℕ) : ℝ) ≤ 2 * (z : ℝ) := by push_cast; linarith
  have hlogz1 : Real.log ((z + 1 : ℕ) : ℝ) ≤ 2 * Real.log (z : ℝ) := by
    have h1 : Real.log ((z + 1 : ℕ) : ℝ) ≤ Real.log (2 * (z : ℝ)) :=
      Real.log_le_log (by positivity) hzz
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have hatom2 : ∑ g ∈ (Finset.Icc 1 z).filter (fun g => Squarefree g), (1 : ℝ) / (Nat.totient g)
      ≤ (8 + 2 * max C' 0) * Real.log (z : ℝ) := by
    have hC'le : C' ≤ max C' 0 := le_max_left _ _
    have h2 : (1 : ℝ) ≤ 2 * Real.log (z : ℝ) := by linarith
    have h3 : max C' 0 ≤ 2 * max C' 0 * Real.log (z : ℝ) := by nlinarith
    have hone : ((Nat.totient 1 : ℝ) / (1 : ℕ)) = 1 := by norm_num
    rw [hone] at hatom
    linarith
  -- assemble
  calc ∑ g ∈ Finset.Icc 1 z, (Nat.totient g : ℝ) * innerG z g ^ 2
      ≤ ∑ g ∈ Finset.Icc 1 z,
          (if Squarefree g then C₀ ^ 2 / ((Nat.totient g : ℝ) * Real.log (z : ℝ) ^ 2)
            else 0) := Finset.sum_le_sum hterm
    _ = ∑ g ∈ (Finset.Icc 1 z).filter (fun g => Squarefree g),
          C₀ ^ 2 / ((Nat.totient g : ℝ) * Real.log (z : ℝ) ^ 2) := (Finset.sum_filter _ _).symm
    _ = C₀ ^ 2 / Real.log (z : ℝ) ^ 2
          * ∑ g ∈ (Finset.Icc 1 z).filter (fun g => Squarefree g),
              (1 : ℝ) / (Nat.totient g) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun g hg => ?_)
        have hg1 : 1 ≤ g := (Finset.mem_Icc.mp (Finset.mem_filter.mp hg).1).1
        have hφR : (0 : ℝ) < (Nat.totient g : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr hg1
        field_simp
    _ ≤ C₀ ^ 2 / Real.log (z : ℝ) ^ 2 * ((8 + 2 * max C' 0) * Real.log (z : ℝ)) := by
        have : (0 : ℝ) ≤ C₀ ^ 2 / Real.log (z : ℝ) ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hatom2 this
    _ = C₀ ^ 2 * (8 + 2 * max C' 0) / Real.log (z : ℝ) := by
        field_simp

/-! ## S6 — the floor form of the mean -/

/-- **S6.** `Σ_{n ≤ N} w(n) = Σ_{m ≤ N} gc(m)·⌊N/m⌋`. The template is
`GrahamL2.grahamW_mean_eq` with the harmonic weight `1/n` replaced by `1`; the multiples
count `#{n ≤ N : m ∣ n} = N/m` is `Nat.Ioc_filter_dvd_card_eq_div`.

Exit-test row (§2(b)): the theorem discharges `(z, N) = (4, 20)` — both sides are
`10.8907154` off line (the largest `lcm(d,e)` over `d, e ≤ 4` is `12`, and `6` on the
`μ`-support, so the range is not truncating). -/
theorem grahamW_sum_eq_floor (z N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, grahamW z n
      = ∑ m ∈ Finset.Icc 1 N, grahamGc z m * ((N / m : ℕ) : ℝ) := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hstep : ∀ n ∈ Finset.Icc 1 N, grahamW z n
      = ∑ m ∈ Finset.Icc 1 N, if m ∣ n then grahamGc z m else 0 := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hdiv : n.divisors = (Finset.Icc 1 N).filter (fun m => m ∣ n) := by
      ext m
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hmn, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hmn (by omega),
          le_trans (Nat.le_of_dvd (by omega) hmn) hnN⟩, hmn⟩
      · rintro ⟨-, hmn⟩; exact ⟨hmn, by omega⟩
    rw [grahamW_eq_sum_grahamGc, hdiv, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Icc 1 N).filter (fun n => m ∣ n)).card = N / m := by
    rw [hIcc]; exact Nat.Ioc_filter_dvd_card_eq_div N m
  rw [hcard, mul_comm]

-- **S6's binder-shape row** (§2(b)) at `(z, N) = (4, 20)`; both sides are `10.8907154`.
example : ∑ n ∈ Finset.Icc 1 20, grahamW 4 n
    = ∑ m ∈ Finset.Icc 1 20, grahamGc 4 m * ((20 / m : ℕ) : ℝ) :=
  grahamW_sum_eq_floor 4 20

/-! ## S7 — the main term as the lcm double sum -/

/-- **S7.** For `z² ≤ N`, `Σ_{m ≤ N} gc(m)/m = Σ_{d,e ≤ z} θ_dθ_e/lcm(d,e)`. Every pair
`(d, e)` with `1 ≤ d, e ≤ z` has `lcm(d,e) ≤ d·e ≤ z² ≤ N`, so it is counted exactly once
in the `m`-range — no truncation, and `gc(m) = 0` for `m > z²` is neither assumed nor
needed. -/
theorem sum_grahamGc_div_eq {z N : ℕ} (h : z ^ 2 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, grahamGc z m / m
      = ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
          grahamTheta z d * grahamTheta z e / (Nat.lcm d e : ℝ) := by
  have hlcm : ∀ d ∈ Finset.Icc 1 z, ∀ e ∈ Finset.Icc 1 z, Nat.lcm d e ∈ Finset.Icc 1 N := by
    intro d hd e he
    obtain ⟨hd1, hdz⟩ := Finset.mem_Icc.mp hd
    obtain ⟨he1, hez⟩ := Finset.mem_Icc.mp he
    have hde : 0 < d * e := Nat.mul_pos hd1 he1
    have h1 : Nat.lcm d e ≤ d * e := Nat.le_of_dvd hde (Nat.lcm_dvd_mul d e)
    have h2 : d * e ≤ z * z := Nat.mul_le_mul hdz hez
    have h3 : z * z = z ^ 2 := by ring
    refine Finset.mem_Icc.mpr ⟨?_, by omega⟩
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
  calc ∑ m ∈ Finset.Icc 1 N, grahamGc z m / m
      = ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
          (if m = Nat.lcm d e then grahamTheta z d * grahamTheta z e / (m : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [grahamGc_eq_Icc (Finset.mem_Icc.mp hm).1, Finset.sum_div]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        split_ifs
        · rfl
        · exact zero_div _
    _ = ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z, ∑ m ∈ Finset.Icc 1 N,
          (if m = Nat.lcm d e then grahamTheta z d * grahamTheta z e / (m : ℝ) else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun d _ => Finset.sum_comm)
    _ = ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
          grahamTheta z d * grahamTheta z e / (Nat.lcm d e : ℝ) := by
        refine Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => ?_))
        rw [Finset.sum_ite_eq', if_pos (hlcm d hd e he)]

/-! ## S8 / S8′ — the `z²` error -/

/-- `n·log n − log(n!) ≤ n − 1`, by induction: the increment is
`n·log((n+1)/n) ≤ n·(1/n) = 1` (`Real.log_le_sub_one_of_pos`). -/
private lemma sum_log_range_ge : ∀ n : ℕ, 1 ≤ n →
    (n : ℝ) * Real.log n - ∑ d ∈ Finset.range (n + 1), Real.log (d : ℝ) ≤ (n : ℝ) - 1 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num [Finset.sum_range_succ]
    · have ihk := ih hk
      have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hlogstep : (k : ℝ) * Real.log ((k : ℝ) + 1) - (k : ℝ) * Real.log (k : ℝ) ≤ 1 := by
        have h1 : Real.log (((k : ℝ) + 1) / (k : ℝ))
            = Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) :=
          Real.log_div (by linarith) (by linarith)
        have h2 : Real.log (((k : ℝ) + 1) / (k : ℝ)) ≤ ((k : ℝ) + 1) / (k : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have h3 : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
          field_simp
          ring
        rw [h1, h3] at h2
        have h4 : (k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ))
            ≤ (k : ℝ) * (1 / (k : ℝ)) := mul_le_mul_of_nonneg_left h2 hk0.le
        have h5 : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp
        nlinarith [h4, h5]
      rw [Finset.sum_range_succ]
      push_cast
      linarith [ihk, hlogstep]

/-- `Σ_{d=1}^{n} log(n/d) = n·log n − log(n!) ≤ n − 1`. -/
private lemma sum_log_Icc_ge {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - ∑ d ∈ Finset.Icc 1 n, Real.log (d : ℝ) ≤ (n : ℝ) - 1 := by
  have hins : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h := sum_log_range_ge n hn
  rw [hins, Finset.sum_insert (by simp)] at h
  simpa using h

/-- **S8.** `Σ_{d ≤ z} |θ_d| ≤ z/log z`. Termwise `|θ_d| ≤ log(z/d)/log z` (`|μ| ≤ 1`),
and `Σ_{d=1}^{z} log(z/d) = z·log z − log(z!) ≤ z − 1 ≤ z`. Measured slack at `z = 100`:
`Σ|θ_d| = 13.80` against `z/log z = 21.71` — 33 % of room, so the route is not tight. -/
theorem sum_abs_grahamTheta_le {z : ℕ} (hz : 2 ≤ z) :
    ∑ d ∈ Finset.Icc 1 z, |grahamTheta z d| ≤ (z : ℝ) / Real.log z := by
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hterm : ∀ d ∈ Finset.Icc 1 z,
      |grahamTheta z d| ≤ Real.log ((z : ℝ) / (d : ℝ)) / Real.log (z : ℝ) := by
    intro d hd
    obtain ⟨hd1, hdz⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hdzR : (d : ℝ) ≤ (z : ℝ) := by exact_mod_cast hdz
    have hlognn : 0 ≤ Real.log ((z : ℝ) / (d : ℝ)) :=
      Real.log_nonneg ((one_le_div hd0).mpr hdzR)
    have hmu : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
    rw [grahamTheta_of_le hdz, abs_div, abs_mul, abs_of_nonneg hlognn,
      abs_of_pos hlogz]
    calc |((moebius d : ℤ) : ℝ)| * Real.log ((z : ℝ) / (d : ℝ)) / Real.log (z : ℝ)
        ≤ 1 * Real.log ((z : ℝ) / (d : ℝ)) / Real.log (z : ℝ) := by gcongr
      _ = Real.log ((z : ℝ) / (d : ℝ)) / Real.log (z : ℝ) := by rw [one_mul]
  have hsum : ∑ d ∈ Finset.Icc 1 z, Real.log ((z : ℝ) / (d : ℝ)) ≤ (z : ℝ) := by
    have hlogd : ∀ d ∈ Finset.Icc 1 z,
        Real.log ((z : ℝ) / (d : ℝ)) = Real.log (z : ℝ) - Real.log (d : ℝ) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      exact Real.log_div (ne_of_gt hzR) (ne_of_gt hd0)
    rw [Finset.sum_congr rfl hlogd, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Nat.card_Icc]
    have hc : ((z + 1 - 1 : ℕ) : ℝ) = (z : ℝ) := by
      norm_num
    rw [hc]
    linarith [sum_log_Icc_ge (n := z) (by omega)]
  calc ∑ d ∈ Finset.Icc 1 z, |grahamTheta z d|
      ≤ ∑ d ∈ Finset.Icc 1 z, Real.log ((z : ℝ) / (d : ℝ)) / Real.log (z : ℝ) :=
        Finset.sum_le_sum hterm
    _ = (∑ d ∈ Finset.Icc 1 z, Real.log ((z : ℝ) / (d : ℝ))) / Real.log (z : ℝ) := by
        rw [Finset.sum_div]
    _ ≤ (z : ℝ) / Real.log (z : ℝ) := by gcongr

/-- **S8′ (the `z²` error).** `Σ_{m ≤ N} |gc(m)| ≤ (z/log z)²`, uniformly in `N`: each
`(d, e)` pair contributes to at most one `m = lcm(d,e)`, so the sum is at most
`(Σ_{d ≤ z} |θ_d|)²`. -/
theorem sum_abs_grahamGc_le {z : ℕ} (hz : 2 ≤ z) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, |grahamGc z m| ≤ ((z : ℝ) / Real.log z) ^ 2 := by
  have hnn : 0 ≤ ∑ d ∈ Finset.Icc 1 z, |grahamTheta z d| :=
    Finset.sum_nonneg (fun d _ => abs_nonneg _)
  have hstep : ∀ m ∈ Finset.Icc 1 N, |grahamGc z m|
      ≤ ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
          (if m = Nat.lcm d e then |grahamTheta z d| * |grahamTheta z e| else 0) := by
    intro m hm
    rw [grahamGc_eq_Icc (Finset.mem_Icc.mp hm).1]
    calc |∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
            (if m = Nat.lcm d e then grahamTheta z d * grahamTheta z e else 0)|
        ≤ ∑ d ∈ Finset.Icc 1 z, |∑ e ∈ Finset.Icc 1 z,
            (if m = Nat.lcm d e then grahamTheta z d * grahamTheta z e else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
            |if m = Nat.lcm d e then grahamTheta z d * grahamTheta z e else 0| := by
          gcongr with d hd
          exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
            (if m = Nat.lcm d e then |grahamTheta z d| * |grahamTheta z e| else 0) := by
          refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
          split_ifs
          · rw [abs_mul]
          · rw [abs_zero]
  calc ∑ m ∈ Finset.Icc 1 N, |grahamGc z m|
      ≤ ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
          (if m = Nat.lcm d e then |grahamTheta z d| * |grahamTheta z e| else 0) :=
        Finset.sum_le_sum hstep
    _ = ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z, ∑ m ∈ Finset.Icc 1 N,
          (if m = Nat.lcm d e then |grahamTheta z d| * |grahamTheta z e| else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun d _ => Finset.sum_comm)
    _ ≤ ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
          |grahamTheta z d| * |grahamTheta z e| := by
        refine Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun e _ => ?_))
        rw [Finset.sum_ite_eq']
        split_ifs
        · exact le_rfl
        · positivity
    _ = (∑ d ∈ Finset.Icc 1 z, |grahamTheta z d|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
    _ ≤ ((z : ℝ) / Real.log z) ^ 2 := by
        gcongr
        exact sum_abs_grahamTheta_le hz

/-! ## S9 — the keystone's easy half -/

/-- **S9 (THE KEYSTONE'S EASY HALF).** `∃ C > 0, ∀ z ≥ 2, ∀ x ≥ z²,
`Σ_{n ≤ ⌊x⌋} w(n) ≤ C·x/log z`.

Route: S6 turns the sum into `Σ_m gc(m)·⌊⌊x⌋/m⌋`; replacing the floor by the real
quotient costs `Σ_m |gc(m)| ≤ (z/log z)²` (S8′), which at `x ≥ z²` is
`≤ (x/log z)·(1/log z) ≤ (x/log z)/log 2`; the main term is
`⌊x⌋·Σ_m gc(m)/m = ⌊x⌋·Σ_{d,e ≤ z} θ_dθ_e/lcm(d,e)` (S7, using `z² ≤ ⌊x⌋`)
`= ⌊x⌋·Σ_{g ≤ z} φ(g)·innerG² ≤ x·C₁/log z` (the landed `graham_diagonalisation`, then S5).

**THE CONSTANT.** `C = C₁ + 1/log 2` with
`C₁ = C₀²·sup_{z ≥ 2}(4·log(z+1) + C')/log z` — here `C₀` is S1's and `C'` is
`phiAtom_upper_lossy`'s ∃-witness (this proof's explicit form is
`C₁ = C₀²·(8 + 2·max(C',0))`, the same shape with the sup discharged by
`log(z+1) ≤ 2 log z` and `1 ≤ 2 log z`). **`C` is NON-EFFECTIVE** — it runs through
`mmuRate_holds`'s threshold `x₀` inside S1's `C₀` (`MoebiusLog.lean:334`'s `C = Cmw + Cs`,
`MoebiusRateSharp.lean:207-212`) — so no numeral for it is printed here, and none can be.
Beside it, the MEASURED truth: `Σ_{n≤x} w(n)·log z/x = 0.82–0.90` for `z ∈ [20,300]` at
`x = z²` (`0.774` at `z = 10`; `0.741` at `(z,x) = (4,16)`), converging to Graham's `1`,
and insensitive to `x` above `z²` (≤ 0.3 % from `x = z²` to `10z²`).

**The must-FAIL mutation (§2(a)).** Sharpening the right-hand side to `C·x/(log z)^{3/2}`
— equivalently sharpening S5 to `C₁/(log z)²` — is FALSE. It breaks at S5: the `μ²/φ`
atom `Σ_{g ≤ z, μ²} 1/φ(g) ≍ log z` gives exactly ONE `log z`, and no more is available.
Receipt: `Σ_{n≤x} w(n)·(log z)^{3/2}/x = 1.414 / 1.685 / 1.871 / 2.043 / 2.137` at
`z = 20 / 50 / 100 / 200 / 300`, `x = z²` — unbounded, so no `C` works. (The weaker
mutation `x/(log z)^{1/2}` is NOT a valid kill-check: it is a WEAKENING, implied by this
theorem, and would read green under every implementation.)

Exit-test row (§2(b)): the hypotheses instantiate at `z = 4`, `x = 16`; off line
`Σ_{n ≤ 16} w(n) = 8.5551702` and `Σ·log 4/16 = 0.7412490`. -/
theorem grahamW_sum_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 2 ≤ z → ∀ x : ℝ, (z : ℝ) ^ 2 ≤ x →
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, grahamW z n ≤ C * x / Real.log z := by
  obtain ⟨C₁, hC₁, hS5⟩ := sum_totient_innerG_sq_le
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hinv2 : (0 : ℝ) < 1 / Real.log 2 := div_pos one_pos hlog2
  refine ⟨C₁ + 1 / Real.log 2, by linarith, fun z hz x hx => ?_⟩
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hx0 : (0 : ℝ) ≤ x := le_trans (by positivity) hx
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hlog2z : Real.log 2 ≤ Real.log (z : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hz)
  have hzN : z ^ 2 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; exact hx)
  have hfloorx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  -- the main term is nonnegative and bounded by S5 through the diagonalisation
  have hmain : ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, grahamGc z m / (m : ℝ)
      = ∑ g ∈ Finset.Icc 1 z, (Nat.totient g : ℝ) * innerG z g ^ 2 := by
    rw [sum_grahamGc_div_eq hzN, graham_diagonalisation]
  have hmain0 : 0 ≤ ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, grahamGc z m / (m : ℝ) := by
    rw [hmain]
    exact Finset.sum_nonneg (fun g _ => by positivity)
  have hmainle : ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, grahamGc z m / (m : ℝ) ≤ C₁ / Real.log (z : ℝ) := by
    rw [hmain]; exact hS5 z hz
  -- the floor error
  have hfl : ∀ m ∈ Finset.Icc 1 ⌊x⌋₊, grahamGc z m * ((⌊x⌋₊ / m : ℕ) : ℝ)
      ≤ grahamGc z m * ((⌊x⌋₊ : ℝ) / (m : ℝ)) + |grahamGc z m| := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hlo : ((⌊x⌋₊ / m : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) / (m : ℝ) := Nat.cast_div_le
    have hdm := Nat.div_add_mod ⌊x⌋₊ m
    have hmod : ⌊x⌋₊ % m < m := Nat.mod_lt _ hm1
    have hdmR : (m : ℝ) * ((⌊x⌋₊ / m : ℕ) : ℝ) + ((⌊x⌋₊ % m : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) := by
      exact_mod_cast hdm
    have hmodR : ((⌊x⌋₊ % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast hmod
    have hhi : (⌊x⌋₊ : ℝ) / (m : ℝ) - 1 ≤ ((⌊x⌋₊ / m : ℕ) : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hm0]
      nlinarith
    have hdiff : |((⌊x⌋₊ / m : ℕ) : ℝ) - (⌊x⌋₊ : ℝ) / (m : ℝ)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have hprod : grahamGc z m * (((⌊x⌋₊ / m : ℕ) : ℝ) - (⌊x⌋₊ : ℝ) / (m : ℝ))
        ≤ |grahamGc z m| := by
      calc grahamGc z m * (((⌊x⌋₊ / m : ℕ) : ℝ) - (⌊x⌋₊ : ℝ) / (m : ℝ))
          ≤ |grahamGc z m * (((⌊x⌋₊ / m : ℕ) : ℝ) - (⌊x⌋₊ : ℝ) / (m : ℝ))| := le_abs_self _
        _ = |grahamGc z m| * |((⌊x⌋₊ / m : ℕ) : ℝ) - (⌊x⌋₊ : ℝ) / (m : ℝ)| := abs_mul _ _
        _ ≤ |grahamGc z m| * 1 := by gcongr
        _ = |grahamGc z m| := mul_one _
    nlinarith [hprod]
  -- the `z²` error is absorbed at `x ≥ z²`
  have herr : ((z : ℝ) / Real.log z) ^ 2 ≤ (1 / Real.log 2) * x / Real.log (z : ℝ) := by
    have h1 : (z : ℝ) ^ 2 / Real.log (z : ℝ) ^ 2 ≤ x / Real.log (z : ℝ) ^ 2 := by
      gcongr
    have h2 : x / Real.log (z : ℝ) ^ 2 ≤ (1 / Real.log 2) * x / Real.log (z : ℝ) := by
      have heq : (1 / Real.log 2) * x / Real.log (z : ℝ)
          = x / (Real.log 2 * Real.log (z : ℝ)) := by
        rw [one_div, inv_mul_eq_div, div_div]
      rw [heq, div_le_div_iff₀ (pow_pos hlogz 2) (mul_pos hlog2 hlogz)]
      nlinarith [mul_nonneg hx0 (mul_nonneg hlogz.le (sub_nonneg.mpr hlog2z))]
    calc ((z : ℝ) / Real.log z) ^ 2 = (z : ℝ) ^ 2 / Real.log (z : ℝ) ^ 2 := by
          rw [div_pow]
      _ ≤ x / Real.log (z : ℝ) ^ 2 := h1
      _ ≤ (1 / Real.log 2) * x / Real.log (z : ℝ) := h2
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, grahamW z n
      = ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, grahamGc z m * ((⌊x⌋₊ / m : ℕ) : ℝ) :=
        grahamW_sum_eq_floor z ⌊x⌋₊
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
          (grahamGc z m * ((⌊x⌋₊ : ℝ) / (m : ℝ)) + |grahamGc z m|) := Finset.sum_le_sum hfl
    _ = (⌊x⌋₊ : ℝ) * (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, grahamGc z m / (m : ℝ))
          + ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, |grahamGc z m| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun m _ => by ring)
    _ ≤ x * (C₁ / Real.log (z : ℝ)) + ((z : ℝ) / Real.log z) ^ 2 := by
        gcongr
        exact sum_abs_grahamGc_le hz ⌊x⌋₊
    _ ≤ x * (C₁ / Real.log (z : ℝ)) + (1 / Real.log 2) * x / Real.log (z : ℝ) := by
        linarith [herr]
    _ = (C₁ + 1 / Real.log 2) * x / Real.log (z : ℝ) := by
        field_simp

-- **S9's binder-shape row** (§2(b)): the hypotheses `2 ≤ z` and `(z:ℝ)² ≤ x` instantiate
-- at `z = 4`, `x = 16`. Off line `Σ_{n ≤ 16} w(n) = 8.5551702`, `Σ·log 4/16 = 0.7412490`.
example : ∃ C : ℝ,
    ∑ n ∈ Finset.Icc 1 ⌊(16 : ℝ)⌋₊, grahamW 4 n ≤ C * 16 / Real.log ((4 : ℕ) : ℝ) := by
  obtain ⟨C, -, h⟩ := grahamW_sum_le
  exact ⟨C, h 4 (by norm_num) 16 (by norm_num)⟩

/-! ## S10 — the two-level weight -/

/-- **S10.** The same mean bound for Jutila's two-level weight `λ_d = bvWeight z₁ z₂ d`:
`Σ_{n ≤ ⌊x⌋} (Σ_{d ∣ n} λ_d)² ≤ 2(log z₁ + log z₂)/log(z₂/z₁)²·(C·x)` for `x ≥ z₂²`.

`λ_d = (log z₂·θ^{(z₂)}_d − log z₁·θ^{(z₁)}_d)/log(z₂/z₁)` (`BvWeight.lean:78`), so
`(Σ_{d∣n} λ_d)² ≤ (2·log²z₂·w_{z₂}(n) + 2·log²z₁·w_{z₁}(n))/log(z₂/z₁)²` by
`(u − v)² ≤ 2u² + 2v²`; S9 at `z₂` (hypothesis `z₂² ≤ x`) and at `z₁` (`z₁² < z₂² ≤ x`)
then gives `(2·log z₂·C·x + 2·log z₁·C·x)/log(z₂/z₁)²`, which IS the frozen prefactor —
the arithmetic is exact, with no slack introduced or lost.

⚠ **`(z₂:ℝ)² ≤ x` is unsatisfiable at B2's ratified closure table** — see the module
docstring. This row is true, it lands, and B2 reads it at no scale until W6b-H lands. -/
theorem sum_sq_sum_bvWeight_le : ∃ C : ℝ, 0 < C ∧ ∀ z₁ z₂ : ℕ, 2 ≤ z₁ → z₁ < z₂ →
    ∀ x : ℝ, (z₂ : ℝ) ^ 2 ≤ x →
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2
      ≤ 2 * (Real.log z₁ + Real.log z₂) / Real.log ((z₂ : ℝ) / z₁) ^ 2 * (C * x) := by
  obtain ⟨C, hC, hS9⟩ := grahamW_sum_le
  refine ⟨C, hC, fun z₁ z₂ hz₁ hz x hx => ?_⟩
  have hz₂ : 2 ≤ z₂ := by omega
  have hz₁R : (1 : ℝ) < (z₁ : ℝ) := by exact_mod_cast (by omega : 1 < z₁)
  have hz₂R : (1 : ℝ) < (z₂ : ℝ) := by exact_mod_cast (by omega : 1 < z₂)
  have hl₁ : 0 < Real.log (z₁ : ℝ) := Real.log_pos hz₁R
  have hl₂ : 0 < Real.log (z₂ : ℝ) := Real.log_pos hz₂R
  have hL : 0 < Real.log ((z₂ : ℝ) / (z₁ : ℝ)) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ (by linarith), one_mul]
    exact_mod_cast hz
  have hx1 : (z₁ : ℝ) ^ 2 ≤ x := by
    refine le_trans ?_ hx
    have : (z₁ : ℝ) ≤ (z₂ : ℝ) := by exact_mod_cast hz.le
    nlinarith
  have hA : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, grahamW z₂ n ≤ C * x / Real.log (z₂ : ℝ) :=
    hS9 z₂ hz₂ x hx
  have hB : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, grahamW z₁ n ≤ C * x / Real.log (z₁ : ℝ) :=
    hS9 z₁ hz₁ x hx1
  have hsum : ∀ n : ℕ, (∑ d ∈ n.divisors, bvWeight z₁ z₂ d)
      = (Real.log (z₂ : ℝ) * (∑ d ∈ n.divisors, grahamTheta z₂ d)
        - Real.log (z₁ : ℝ) * (∑ d ∈ n.divisors, grahamTheta z₁ d))
        / Real.log ((z₂ : ℝ) / (z₁ : ℝ)) := by
    intro n
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl (fun d _ => rfl)
  have hterm : ∀ n : ℕ, (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2
      ≤ (2 * Real.log (z₂ : ℝ) ^ 2 * grahamW z₂ n + 2 * Real.log (z₁ : ℝ) ^ 2 * grahamW z₁ n)
        / Real.log ((z₂ : ℝ) / (z₁ : ℝ)) ^ 2 := by
    intro n
    rw [hsum n, div_pow, grahamW, grahamW]
    gcongr
    nlinarith [sq_nonneg (Real.log (z₂ : ℝ) * (∑ d ∈ n.divisors, grahamTheta z₂ d)
      + Real.log (z₁ : ℝ) * (∑ d ∈ n.divisors, grahamTheta z₁ d))]
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (2 * Real.log (z₂ : ℝ) ^ 2 * grahamW z₂ n + 2 * Real.log (z₁ : ℝ) ^ 2 * grahamW z₁ n)
            / Real.log ((z₂ : ℝ) / (z₁ : ℝ)) ^ 2 := Finset.sum_le_sum (fun n _ => hterm n)
    _ = (2 * Real.log (z₂ : ℝ) ^ 2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, grahamW z₂ n)
          + 2 * Real.log (z₁ : ℝ) ^ 2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, grahamW z₁ n))
          / Real.log ((z₂ : ℝ) / (z₁ : ℝ)) ^ 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (2 * Real.log (z₂ : ℝ) ^ 2 * (C * x / Real.log (z₂ : ℝ))
          + 2 * Real.log (z₁ : ℝ) ^ 2 * (C * x / Real.log (z₁ : ℝ)))
          / Real.log ((z₂ : ℝ) / (z₁ : ℝ)) ^ 2 := by
        gcongr
    _ = 2 * (Real.log (z₁ : ℝ) + Real.log (z₂ : ℝ)) / Real.log ((z₂ : ℝ) / (z₁ : ℝ)) ^ 2
          * (C * x) := by
        field_simp
        ring

end Salt.SW
