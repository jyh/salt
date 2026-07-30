/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetChi
import Salt.MR.USetBalance
import Salt.MR.USetPins

/-!
# USetChiTS — the `χ`-lift of the `𝒯_S` razor and the balance (wave P-6, stone E, part 2)

Part 1 (`USetChi.lean`) retyped the index set, the block objects and the `𝒯_L` branch.  This
file lands the `𝒯_S` branch (the co-factor at twisted data, the `|ℰ|·√T` razor and its
character debit), the branch-split identity, and the `χ`-summed twin of `USetBalance`'s
`hU`-exit composition.

## The razor, and where the character count actually enters

The `q = 1` razor (`USetThinTS`:303/322) spends the thinness of `𝒰` on Lemma 9's Halász term:
`|𝒯|·√T ≤ W·T^{2α+1/2} ≤ W·T^{1−2η} ≤ W·X^{1−2η}` at the gate `α ≤ 1/4 − η`.  Two things
change under the `χ`-lift and NEITHER costs a `φ(q)`:

* the count is over PAIRS and comes from the hybrid Lemma 6.5 (`UsetChi_thin`), so there is
  **no `φ(q)` union factor** — `|ℰ| ≤ φ(q)·max_χ|𝒯_χ|` is the crude route and is not taken;
* the hybrid count's height is `qT`, so the exponent leg reads `(qT)^{2α} = q^{2α}·T^{2α}`:
  the whole character cost of the razor is the single factor **`q^{2α} ≤ √q`**.

`thin_sqrt_kill` is character-free arithmetic and is reused VERBATIM with `W := q^{2α}·W`.

**THE MARGIN (computed, `charDebit_le_rpow` below).**  At the port's modulus gate
`q ≤ (log H)^{12} ≤ (log X)^{12}` and `2α ≤ 1/2` the debit is `q^{2α} ≤ √q ≤ (log X)^6`, and
`(log X)^6 ≤ X^ε` as soon as `6·loglog X ≤ ε·log X`.  At `ε = 1/1000` (half of the landed
`2η ≥ 1/500`, `USetPins.c0_le_exit_exponent`) the gate holds already at
`log X ≥ e^{40} ≈ 2.4·10^{17}` — whereas the same file's `X₀` law (`hκ30`) forces
`log X ≥ 30^{3/ρ} ≈ 10^{385}`, where `6·loglog X ≈ 5.3·10^3` against `ε·log X ≈ 10^{382}`.
**The razor tolerates the character debit with ≈ 378 orders of magnitude of margin**, and it
consumes at most HALF the `η` it was already paying (`UsetChi_thin_sqrt_kill_absorbed`).

## The two named hypothesis slots

* `Salt.MR.HalaszPrimesChi` (part 1) — the `χ`-twisted MR Lemma 11, wave P-6-CORE's stone C.
* **`HalaszIntegersChi` (this file) — the `χ`-twisted MR Lemma 9 (Halász for integers).**
  **A FINDING, reported: this stone is NOT on the port freeze's stone list (A–E) and is NOT
  in P-3/P-4's supply floor.**  The `𝒯_S` branch cannot run at the landed hybrid MEAN-VALUE
  grade: `hybrid_wellspaced_l2` carries a `φ(q)·(T+1)` row, and at the §8.3 pins `T ≍ X` while
  the co-factor length is `M ≍ X·e^{−j/H}`, so the mean-value row exceeds the `q = 1` exit by
  the factor `e^{j/H} ≍ p` — exactly the factor the whole apparatus exists to save.  The
  trivial-grade row is landed here anyway (`ramRChi_sq_sum_mvt`, MR Step 0's majorant above
  `T ≍ X`), which is what makes the gap visible rather than assumed.

## Sign conventions (CATCH #B ∘ N1, re-armed)

`ramR`/`ramMain` are at `σ = 1`; the reflection to KMT's `n^{+it}` convention is the pair
involution `reflectPair` of part 1.  Every statement below declares which side it is on: the
branch sets and the mean squares are `σ = 1`; only `ramR_chiBar_eq_dpolyChi` and the two
socket consumptions cross over.

Source pins (D5): MR arXiv v4 (`1501.04585v4`) pp. 16–17 (Lemma 9), 27–29 (§8.3);
`docs/exploration/port-freeze-0729.md` v2; `⟦SPECTRUM-SCOPE⟧` in `docs/blueprints/flags.md`.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §1 — the Ramaré co-factor at `χ̄`-twisted data -/

/-- The co-factor mask and the Ramaré weight are character-blind: the twist passes through. -/
lemma ramRcoeff_chiBar (q : ℕ) (χ : DirichletCharacter ℂ q) (H : ℝ) (N X P Q j : ℕ)
    (b : ℕ → ℂ) :
    ramRcoeff H N X P Q j (chiBarCoeff q χ b) = chiBarCoeff q χ (ramRcoeff H N X P Q j b) := by
  funext m
  rw [chiBarCoeff_apply]
  by_cases h : m ∈ ramRrange H N X j
  · rw [ramRcoeff, if_pos h, ramRcoeff, if_pos h, chiBarCoeff_apply]; ring
  · rw [ramRcoeff, if_neg h, ramRcoeff, if_neg h, mul_zero]

/-- `ramR` at twisted data is the `σ = 1` polynomial of its own twisted masked coefficients,
at ANY length `M` containing the co-factor range (the sharp `M` is load-bearing — law #253). -/
lemma ramR_chiBar_eq_spoly (q : ℕ) (χ : DirichletCharacter ℂ q) (H : ℝ) (N X P Q j M : ℕ)
    (b : ℕ → ℂ) (hM : ramRrange H N X j ⊆ Finset.Icc 1 M) (t : ℝ) :
    ramR H N X P Q j (chiBarCoeff q χ b) t
      = spoly M (chiBarCoeff q χ (ramRcoeff H N X P Q j b)) t := by
  rw [ramR_eq_spoly H N X P Q j M (chiBarCoeff q χ b) hM t, ramRcoeff_chiBar]

/-- **The composed bridge (CATCH #B ∘ N1) at `ramR`**: `R_{j,H}(χ̄, 1+it)` is `dpolyChi` at
`χ⁻¹` and `−t`.  This is the shape a `χ`-twisted Lemma 9 consumes. -/
lemma ramR_chiBar_eq_dpolyChi (q : ℕ) (χ : DirichletCharacter ℂ q) (H : ℝ)
    (N X P Q j M : ℕ) (b : ℕ → ℂ) (hM : ramRrange H N X j ⊆ Finset.Icc 1 M) (t : ℝ) :
    ramR H N X P Q j (chiBarCoeff q χ b) t
      = dpolyChi q (Finset.Icc 1 M)
          (fun m => ramRcoeff H N X P Q j b m / (m : ℂ)) χ⁻¹ (-t) := by
  rw [ramR_chiBar_eq_spoly q χ H N X P Q j M b hM t, spoly_chiBarCoeff_eq_dpolyChi]

/-- The twist does not increase the coefficient mass (`‖χ̄(m)‖ ≤ 1`). -/
lemma ramRcoeff_chiBar_mass_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (H : ℝ)
    (N X P Q j M : ℕ) (b : ℕ → ℂ) :
    ∑ m ∈ Finset.Icc 1 M,
        ‖ramRcoeff H N X P Q j (chiBarCoeff q χ b) m‖ ^ 2 / (m : ℝ) ^ 2
      ≤ ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  refine Finset.sum_le_sum (fun m _ => ?_)
  have h : ‖ramRcoeff H N X P Q j (chiBarCoeff q χ b) m‖
      ≤ ‖ramRcoeff H N X P Q j b m‖ := by
    rw [ramRcoeff_chiBar]
    exact norm_chiBarCoeff_le χ _ m
  have h0 : (0 : ℝ) ≤ ‖ramRcoeff H N X P Q j (chiBarCoeff q χ b) m‖ := norm_nonneg _
  have hsq : ‖ramRcoeff H N X P Q j (chiBarCoeff q χ b) m‖ ^ 2
      ≤ ‖ramRcoeff H N X P Q j b m‖ ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_right hsq (by positivity)

/-! ## §2 — the co-factor mean square on a pair set: the two grades -/

/-- **THE SECOND NAMED SLOT — the `χ`-twisted MR Lemma 9 (Halász for integers).**  The
landed `halasz_integers_unconditional_const` (`VdCSocket`:547, `Cvdc = 640`, constant
`2564`) with the index set a per-fibre well-spaced set of PAIRS and the polynomial `χ`-twisted.
The `|ℰ|·√T` term is what the razor of §3 spends the `𝒰`-thinness on.

**REPORTED GAP.**  This stone is not on the port freeze's stone list and not in P-3/P-4's
supply floor; see the module header for why the landed hybrid mean-value grade cannot replace
it.  The constant is left as a parameter `Cint` so that whatever P-6-CORE/P-7 delivers
discharges the slot without a restatement. -/
def HalaszIntegersChi (Cint : ℝ) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (M : ℕ) (a : ℕ → ℂ) (T : ℝ), 1 ≤ T →
  ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
    (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
    ∑ r ∈ ℰ, ‖dpolyChi q (Finset.Icc 1 M) a r.1 r.2‖ ^ 2
      ≤ Cint * ((M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T) * (1 + Real.log (2 * T))
          * ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2

/-- **The co-factor mean square on a pair set (Lemma 9, `χ`-twisted).**  The socket
instantiated at the co-factor's own coefficients and the sharp length `M`, through the
reflected pair set (CATCH #B ∘ N1): `WellSpaced`, `⊆ [−T,T]` and `card` are all
`reflectPair`-stable. -/
theorem ramRChi_sq_sum_le {Cint : ℝ} (hslot : HalaszIntegersChi Cint) (q : ℕ) (hq : 0 < q)
    (H : ℝ) (N X P Q j M : ℕ) (b : ℕ → ℂ) (hM : ramRrange H N X j ⊆ Finset.Icc 1 M)
    (T : ℝ) (hT : 1 ≤ T) (ℰ : Finset (DirichletCharacter ℂ q × ℝ))
    (hws : FibreWellSpaced ℰ) (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) :
    ∑ r ∈ ℰ, ‖ramR H N X P Q j (chiBarCoeff q r.1 b) r.2‖ ^ 2
      ≤ Cint * ((M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T) * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  set a : ℕ → ℂ := fun m => ramRcoeff H N X P Q j b m / (m : ℂ) with hadef
  have hlhs : ∑ r ∈ ℰ, ‖ramR H N X P Q j (chiBarCoeff q r.1 b) r.2‖ ^ 2
      = ∑ r ∈ reflectChi ℰ, ‖dpolyChi q (Finset.Icc 1 M) a r.1 r.2‖ ^ 2 := by
    rw [sum_reflectChi ℰ (fun r => ‖dpolyChi q (Finset.Icc 1 M) a r.1 r.2‖ ^ 2)]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [ramR_chiBar_eq_dpolyChi q r.1 H N X P Q j M b hM r.2]
  have h := hslot q hq M a T hT (reflectChi ℰ) (fibreWellSpaced_reflectChi hws)
    (reflectChi_subset_Icc hsub)
  rw [card_reflectChi] at h
  have hmass : ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2
      = ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hadef, norm_div, Complex.norm_natCast, div_pow]
  rw [hlhs, ← hmass]
  exact h

/-- **The trivial grade (MR Step 0's majorant), unconditional.**  The landed hybrid
mean-value bound `hybrid_wellspaced_l2` on the same pair set: no `√T` term, but a
`φ(q)·(T+1)` row.  This is the honest majorant above `T ≍ X`, and it is what makes the grade
gap of `HalaszIntegersChi` visible: at the §8.3 pins `T ≍ X` and `M ≍ X e^{−j/H}`, this row
exceeds the `q = 1` exit by `e^{j/H}`. -/
theorem ramRChi_sq_sum_mvt (q : ℕ) [NeZero q] (H : ℝ) (N X P Q j M : ℕ) (b : ℕ → ℂ)
    (hM : ramRrange H N X j ⊆ Finset.Icc 1 M) (T : ℝ) (hT : 0 ≤ T)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) :
    ∑ r ∈ ℰ, ‖ramR H N X P Q j (chiBarCoeff q r.1 b) r.2‖ ^ 2
      ≤ 84 * ((q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * (M : ℝ) / q)
          * Real.log (2 * M)
          * ∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.Coprime n q),
              ‖ramRcoeff H N X P Q j b n / (n : ℂ)‖ ^ 2 := by
  set a : ℕ → ℂ := fun m => ramRcoeff H N X P Q j b m / (m : ℂ) with hadef
  have hlhs : ∑ r ∈ ℰ, ‖ramR H N X P Q j (chiBarCoeff q r.1 b) r.2‖ ^ 2
      = ∑ r ∈ reflectChi ℰ, ‖dpolyChi q (Finset.Icc 1 M) a r.1 r.2‖ ^ 2 := by
    rw [sum_reflectChi ℰ (fun r => ‖dpolyChi q (Finset.Icc 1 M) a r.1 r.2‖ ^ 2)]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [ramR_chiBar_eq_dpolyChi q r.1 H N X P Q j M b hM r.2]
  have h := hybrid_wellspaced_l2 (N := M) q (Finset.Icc 1 M) (Finset.Subset.refl _) a hT
    (reflectChi ℰ) (fibreWellSpaced_reflectChi hws) (reflectChi_subset_Icc hsub)
  rw [hlhs]
  exact h

/-! ## §3 — the razor: `|ℰ|·√T ≤ q^{2α}·bundle·X^{1−2η}`, and the character debit -/

/-- **The `X^{o(1)}` bundle of the `χ`-lifted thinness count**, at the hybrid height `S`
(the consumer plugs `S := qT`): the `Q_J²` union factor (character-free — `dyadicPairs` and
`dyadicPairs_card_le_exp` are reused verbatim), Lemma 6.5's absolute `1680`, the level `V²`,
and the count's `exp(2(log S/log P_J)·loglog S)` tail.  Explicit by construction (law #253). -/
noncomputable def thinBundleChi (S V : ℝ) (Pj Qj : ℕ) : ℝ :=
  ((dyadicPairs Pj Qj).card : ℝ)
    * (1680 * V ^ 2 * Real.exp (2 * (Real.log S / Real.log Pj) * Real.log (Real.log S)))

lemma thinBundleChi_nonneg (S V : ℝ) (Pj Qj : ℕ) : 0 ≤ thinBundleChi S V Pj Qj := by
  rw [thinBundleChi]
  have h := Real.exp_pos (2 * (Real.log S / Real.log Pj) * Real.log (Real.log S))
  positivity

/-- **`UsetChi_thin` at the `α_J` gate.**  Lemma 6.5's exponent `2·log V/log P_Jb` is bounded
by `2α` through the in-statement gate `log V ≤ α·log P_Jb`; everything else is the explicit
`thinBundleChi`.  Height `qT` throughout. -/
theorem UsetChi_thin_alpha (q : ℕ) [NeZero q] (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J Jb : ℕ) (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J) (hδ0 : 0 < δ)
    (T V : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T) (hV : 1 ≤ V)
    (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log (Qseq Jb))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetChi q f Pseq Qseq δ J)
    (α : ℝ) (hVα : Real.log V ≤ α * Real.log (Pseq Jb)) :
    (ℰ.card : ℝ)
      ≤ thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb) * ((q : ℝ) * T) ^ (2 * α) := by
  have hP1R : (1 : ℝ) < (Pseq Jb : ℝ) := by
    have h : (3 : ℝ) ≤ (Pseq Jb : ℝ) := by exact_mod_cast hP3
    linarith
  have hlogP : 0 < Real.log (Pseq Jb) := Real.log_pos hP1R
  have hexp : 2 * Real.log V / Real.log (Pseq Jb) ≤ 2 * α := by
    rw [div_le_iff₀ hlogP]
    nlinarith [hVα]
  have hrpow : ((q : ℝ) * T) ^ (2 * Real.log V / Real.log (Pseq Jb))
      ≤ ((q : ℝ) * T) ^ (2 * α) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hqT) hexp
  have hcount := UsetChi_thin q f hf1 Pseq Qseq δ J Jb hJb1 hJbJ hδ0 T V hT1 hqT hV hVinv
    hP3 hQT hκ30 hLL5 ℰ hws hsub hU
  refine hcount.trans ?_
  rw [thinBundleChi]
  set S : ℝ := (q : ℝ) * T with hSdef
  set D : ℝ := ((dyadicPairs (Pseq Jb) (Qseq Jb)).card : ℝ)
      * (1680 * V ^ 2
          * Real.exp (2 * (Real.log S / Real.log (Pseq Jb)) * Real.log (Real.log S))) with hD
  have hK : (0 : ℝ) ≤ D := by
    rw [hD]
    have h := Real.exp_pos (2 * (Real.log S / Real.log (Pseq Jb)) * Real.log (Real.log S))
    positivity
  calc ((dyadicPairs (Pseq Jb) (Qseq Jb)).card : ℝ)
        * (1680 * S ^ (2 * Real.log V / Real.log (Pseq Jb)) * V ^ 2
            * Real.exp (2 * (Real.log S / Real.log (Pseq Jb)) * Real.log (Real.log S)))
      = D * S ^ (2 * Real.log V / Real.log (Pseq Jb)) := by rw [hD]; ring
    _ ≤ D * S ^ (2 * α) := mul_le_mul_of_nonneg_left hrpow hK

/-- **THE RAZOR, `χ`-LIFTED.**  The landed `thin_sqrt_kill` reused VERBATIM (it is
character-free arithmetic) with the bundle carrying the single character debit `q^{2α}` — the
whole cost of the hybrid height `(qT)^{2α} = q^{2α}·T^{2α}`.  MR Step 0's `T ≤ X` and the
gate `α ≤ 1/4 − η` are the landed ones. -/
theorem UsetChi_thin_sqrt_kill (q : ℕ) [NeZero q] (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J Jb : ℕ) (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J) (hδ0 : 0 < δ)
    (T V : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T) (hV : 1 ≤ V)
    (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log (Qseq Jb))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetChi q f Pseq Qseq δ J)
    (α η X : ℝ) (hVα : Real.log V ≤ α * Real.log (Pseq Jb)) (hα : α ≤ 1 / 4 - η)
    (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) :
    (ℰ.card : ℝ) * Real.sqrt T
      ≤ (q : ℝ) ^ (2 * α) * thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb)
          * X ^ (1 - 2 * η) := by
  have hq0 : (0 : ℝ) < q := by
    have := Nat.pos_of_ne_zero (NeZero.ne q); exact_mod_cast this
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hcnt := UsetChi_thin_alpha q f hf1 Pseq Qseq δ J Jb hJb1 hJbJ hδ0 T V hT1 hqT hV
    hVinv hP3 hQT hκ30 hLL5 ℰ hws hsub hU α hVα
  have hsplit : ((q : ℝ) * T) ^ (2 * α) = (q : ℝ) ^ (2 * α) * T ^ (2 * α) :=
    Real.mul_rpow (le_of_lt hq0) hT0
  have hbundle0 : (0 : ℝ) ≤ thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb) :=
    thinBundleChi_nonneg _ _ _ _
  have hdeb0 : (0 : ℝ) ≤ (q : ℝ) ^ (2 * α) := Real.rpow_nonneg (le_of_lt hq0) _
  have hcnt' : (ℰ.card : ℝ)
      ≤ ((q : ℝ) ^ (2 * α) * thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb))
          * T ^ (2 * α) := by
    rw [hsplit] at hcnt
    calc (ℰ.card : ℝ)
        ≤ thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb)
            * ((q : ℝ) ^ (2 * α) * T ^ (2 * α)) := hcnt
      _ = ((q : ℝ) ^ (2 * α) * thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb))
            * T ^ (2 * α) := by ring
  exact thin_sqrt_kill T X
    ((q : ℝ) ^ (2 * α) * thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb)) α η
    (ℰ.card : ℝ) hT1 hTX (by positivity) hα hη2 hcnt'

/-! ### The character debit, priced -/

/-- **The polylog-against-power gate, in-statement.**  `(log X)^k ≤ X^ε` exactly when
`k·loglog X ≤ ε·log X`; nothing is absorbed into a threshold constant. -/
lemma logpow_le_rpow_of_gate (X ε : ℝ) (k : ℕ) (hX : 1 < X)
    (hgate : (k : ℝ) * Real.log (Real.log X) ≤ ε * Real.log X) :
    (Real.log X) ^ k ≤ X ^ ε := by
  have hL0 : 0 < Real.log X := Real.log_pos hX
  have h1 : (Real.log X) ^ k = Real.exp (Real.log (Real.log X) * (k : ℝ)) := by
    rw [← Real.rpow_natCast (Real.log X) k, Real.rpow_def_of_pos hL0]
  have h2 : X ^ ε = Real.exp (Real.log X * ε) := by
    rw [Real.rpow_def_of_pos (show (0 : ℝ) < X by linarith)]
  rw [h1, h2]
  refine Real.exp_le_exp.mpr ?_
  calc Real.log (Real.log X) * (k : ℝ) = (k : ℝ) * Real.log (Real.log X) := by ring
    _ ≤ ε * Real.log X := hgate
    _ = Real.log X * ε := by ring

/-- **The gate holds at `log X ≥ e^{40}`** for `k ≤ 6` and `ε ≥ 1/1000`: `log L ≤ √L`
(the sharp `e·log s ≤ s` at `s = √L`) and `√L ≥ e^{20} ≥ 6000` give `6000·log L ≤ L`.  The
`X₀` law of the `𝒰`-leg (`hκ30`) forces `log X ≥ 30^{3/ρ} ≈ 10^{385}`, so this gate is
slack by ~378 orders of magnitude. -/
lemma logpow_gate_of_exp_floor (X ε : ℝ) (k : ℕ) (hk : k ≤ 6) (hε : 1 / 1000 ≤ ε)
    (hX : Real.exp 40 ≤ Real.log X) :
    (k : ℝ) * Real.log (Real.log X) ≤ ε * Real.log X := by
  set L : ℝ := Real.log X with hLdef
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (Real.exp_pos 40) hX
  have hsq0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  -- `log L ≤ √L`
  have hstep := exp_one_mul_log_le hsq0
  rw [Real.log_sqrt (le_of_lt hL0)] at hstep
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have hlogL : Real.log L ≤ Real.sqrt L := by nlinarith
  -- `√L ≥ e^{20} ≥ 6000`
  have hexp20 : Real.exp 20 ≤ Real.sqrt L := by
    have hsq : Real.exp 40 = (Real.exp 20) ^ 2 := by
      rw [sq, ← Real.exp_add]; norm_num
    have h1 : Real.sqrt (Real.exp 40) ≤ Real.sqrt L := Real.sqrt_le_sqrt hX
    rwa [hsq, Real.sqrt_sq (Real.exp_pos 20).le] at h1
  have h6000 : (6000 : ℝ) ≤ Real.exp 20 := by
    have h20 : Real.exp 20 = Real.exp 1 ^ (20 : ℕ) := by
      have h := Real.exp_nat_mul 1 20
      rw [← h]; norm_num
    rw [h20]
    calc (6000 : ℝ) ≤ 2.7 ^ (20 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (20 : ℕ) := pow_le_pow_left₀ (by norm_num) he 20
  have hkey : 6000 * Real.log L ≤ L := by
    have h1 : (6000 : ℝ) ≤ Real.sqrt L := le_trans h6000 hexp20
    have h2 : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (le_of_lt hL0)
    nlinarith [Real.sqrt_nonneg L]
  have hkR : (k : ℝ) ≤ 6 := by exact_mod_cast hk
  have hlogL0 : Real.log L ≤ Real.sqrt L := hlogL
  nlinarith [Real.sqrt_nonneg L, hkey, hkR]

/-- **THE CHARACTER DEBIT, PRICED.**  At the port's modulus gate `q ≤ (log X)^{12}` and
`2α ≤ 1/2`, the razor's whole character cost is `q^{2α} ≤ √q ≤ (log X)^6 ≤ X^ε` — a polylog
against a fixed power.  The gate `Real.exp 40 ≤ Real.log X` is ~378 orders of magnitude below
the `𝒰`-leg's own `X₀` law, and `ε = 1/1000` is HALF the landed `2η ≥ 1/500`
(`USetPins.c0_le_exit_exponent`), so the debit is paid out of the margin the razor already
had. -/
theorem charDebit_le_rpow (X ε : ℝ) (hX0 : 0 < X) (q : ℕ) (hq1 : 1 ≤ q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ 12) (α : ℝ) (hα : 2 * α ≤ 1 / 2)
    (hε : 1 / 1000 ≤ ε) (hX : Real.exp 40 ≤ Real.log X) :
    (q : ℝ) ^ (2 * α) ≤ X ^ ε := by
  have hL0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 40) hX
  have hX1 : 1 < X := by
    have h := Real.exp_lt_exp.mpr hL0
    rwa [Real.exp_zero, Real.exp_log hX0] at h
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  -- `q^{2α} ≤ q^{1/2} = √q`
  have h1 : (q : ℝ) ^ (2 * α) ≤ (q : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hq1R hα
  have h2 : (q : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt q := rpow_half_eq_sqrt _
  -- `√q ≤ √((log X)^{12}) = (log X)^6`
  have h3 : Real.sqrt q ≤ (Real.log X) ^ 6 := by
    have hpow : (Real.log X) ^ 12 = ((Real.log X) ^ 6) ^ 2 := by ring
    have h4 : Real.sqrt q ≤ Real.sqrt ((Real.log X) ^ 12) := Real.sqrt_le_sqrt hqlog
    rwa [hpow, Real.sqrt_sq (by positivity)] at h4
  have h5 : (Real.log X) ^ 6 ≤ X ^ ε :=
    logpow_le_rpow_of_gate X ε 6 hX1 (logpow_gate_of_exp_floor X ε 6 (le_refl 6) hε hX)
  calc (q : ℝ) ^ (2 * α) ≤ (q : ℝ) ^ ((1 : ℝ) / 2) := h1
    _ = Real.sqrt q := h2
    _ ≤ (Real.log X) ^ 6 := h3
    _ ≤ X ^ ε := h5

/-- **THE RAZOR WITH THE DEBIT ABSORBED.**  `|ℰ|·√T ≤ bundle·X^{1−2η+ε}`: the character debit
costs the exponent `ε`, and at `ε ≤ η` (which `charDebit_le_rpow` delivers with ~378 orders
to spare) the razor still exits at `X^{1−η}` — HALF the margin pays for the whole
`φ(q)`-genre cost. -/
theorem UsetChi_thin_sqrt_kill_absorbed (q : ℕ) [NeZero q] (f : ℕ → ℂ)
    (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J Jb : ℕ) (hJb1 : 1 ≤ Jb)
    (hJbJ : Jb ≤ J) (hδ0 : 0 < δ) (T V : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hV : 1 ≤ V) (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log (Qseq Jb))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetChi q f Pseq Qseq δ J)
    (α η X ε : ℝ) (hVα : Real.log V ≤ α * Real.log (Pseq Jb)) (hα : α ≤ 1 / 4 - η)
    (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) (hX0 : 0 < X)
    (hdebit : (q : ℝ) ^ (2 * α) ≤ X ^ ε) :
    (ℰ.card : ℝ) * Real.sqrt T
      ≤ thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η + ε) := by
  have hraw := UsetChi_thin_sqrt_kill q f hf1 Pseq Qseq δ J Jb hJb1 hJbJ hδ0 T V hT1 hqT hV
    hVinv hP3 hQT hκ30 hLL5 ℰ hws hsub hU α η X hVα hα hη2 hTX
  have hbundle0 : (0 : ℝ) ≤ thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb) :=
    thinBundleChi_nonneg _ _ _ _
  have hXpow0 : (0 : ℝ) < X ^ (1 - 2 * η) := Real.rpow_pos_of_pos hX0 _
  have hstep : (q : ℝ) ^ (2 * α) * thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb)
        * X ^ (1 - 2 * η)
      ≤ thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η + ε) := by
    have hsum : X ^ (1 - 2 * η + ε) = X ^ (1 - 2 * η) * X ^ ε := by
      rw [Real.rpow_add hX0]
    rw [hsum]
    have h1 : (q : ℝ) ^ (2 * α) * thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb)
          * X ^ (1 - 2 * η)
        = (thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η))
            * (q : ℝ) ^ (2 * α) := by ring
    have h2 : thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb)
          * (X ^ (1 - 2 * η) * X ^ ε)
        = (thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η))
            * X ^ ε := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hdebit (by positivity)
  exact le_trans hraw hstep

/-! ## §4 — the `𝒯_S` branch at `(χ, t)` -/

/-- **`𝒯_S` at `(χ, t)`**: the pairs of a per-fibre well-spaced `ℰ` where the `χ̄`-twisted
prime block factor is SMALL (MR's `ε = (log X)^{−100}`; the level is a parameter). -/
noncomputable def TsetSmallChi (q : ℕ) (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (ε : ℝ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) : Finset (DirichletCharacter ℂ q × ℝ) :=
  ℰ.filter (fun r => ‖ramQ H P Q j (chiBarCoeff q r.1 c) r.2‖ ≤ ε)

lemma mem_TsetSmallChi {q : ℕ} {H : ℝ} {P Q j : ℕ} {c : ℕ → ℂ} {ε : ℝ}
    {ℰ : Finset (DirichletCharacter ℂ q × ℝ)} {r : DirichletCharacter ℂ q × ℝ} :
    r ∈ TsetSmallChi q H P Q j c ε ℰ
      ↔ r ∈ ℰ ∧ ‖ramQ H P Q j (chiBarCoeff q r.1 c) r.2‖ ≤ ε := by
  rw [TsetSmallChi, Finset.mem_filter]

lemma TsetSmallChi_subset (q : ℕ) (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (ε : ℝ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) : TsetSmallChi q H P Q j c ε ℰ ⊆ ℰ :=
  Finset.filter_subset _ _

/-- **The `𝒯_S` branch mean square on a pair set** (before the thinness is spent).  The
pointwise `ε²` gain is the landed character-blind `norm_ramMain_sq_le_of_small`; the analysis
is the twisted Lemma 9 of §2.  The count in the Halász term is `|ℰ|` (monotone from `|𝒯_S|`)
— it is `|ℰ|` that `UsetChi_thin` bounds. -/
theorem TSChi_branch_meansq {Cint : ℝ} (hCint : 0 ≤ Cint) (hslot : HalaszIntegersChi Cint)
    (q : ℕ) (hq : 0 < q) (H : ℝ) (N X P Q j M : ℕ) (b c : ℕ → ℂ)
    (hM : ramRrange H N X j ⊆ Finset.Icc 1 M) (ε : ℝ) (T : ℝ) (hT : 1 ≤ T)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) :
    ∑ r ∈ TsetSmallChi q H P Q j c ε ℰ,
        ‖ramMain H N X P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c) j r.2‖ ^ 2
      ≤ ε ^ 2 * (Cint * ((M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T) * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) := by
  have hsubT : TsetSmallChi q H P Q j c ε ℰ ⊆ ℰ := TsetSmallChi_subset q H P Q j c ε ℰ
  have h1 : ∑ r ∈ TsetSmallChi q H P Q j c ε ℰ,
        ‖ramMain H N X P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c) j r.2‖ ^ 2
      ≤ ∑ r ∈ TsetSmallChi q H P Q j c ε ℰ,
          ε ^ 2 * ‖ramR H N X P Q j (chiBarCoeff q r.1 b) r.2‖ ^ 2 :=
    Finset.sum_le_sum (fun r hr =>
      norm_ramMain_sq_le_of_small H N X P Q j (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c)
        ε r.2 (mem_TsetSmallChi.mp hr).2)
  rw [← Finset.mul_sum] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg ε))
  have h9 := ramRChi_sq_sum_le hslot q hq H N X P Q j M b hM T hT
    (TsetSmallChi q H P Q j c ε ℰ) (fibreWellSpaced_of_subset hsubT hws)
    (fun r hr => hsub r (hsubT hr))
  refine h9.trans ?_
  have hcard : ((TsetSmallChi q H P Q j c ε ℰ).card : ℝ) ≤ (ℰ.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubT
  have hA : ((TsetSmallChi q H P Q j c ε ℰ).card : ℝ) * Real.sqrt T
      ≤ (ℰ.card : ℝ) * Real.sqrt T :=
    mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg T)
  have hlog : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hmass : (0 : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun m _ => by positivity)
  nlinarith [mul_nonneg (sub_nonneg.mpr hA) (mul_nonneg hlog hmass), hCint]

/-- **U-5, `χ`-LIFTED (exit) — the `𝒯_S` branch at the MEAN-VALUE grade.**  Once the thinness
budget clears the co-factor length (`bundle·X^{1−2η+ε} ≤ M`, the consumer's `X^{o(1)}`
arithmetic against `M ≍ X e^{−j/H}`), the twisted Lemma 9 degenerates and the branch is priced
at the trivial grade TIMES the pointwise gain `ε_Q²` — MR's `(log X)^{−200}`.  The Halász term
has vanished: that is what the `𝒰`-thinness bought, and the character debit rode inside the
exponent `ε` (§3). -/
theorem usetChi_TS_branch_meanvalue {Cint : ℝ} (hCint : 0 ≤ Cint)
    (hslot : HalaszIntegersChi Cint) (q : ℕ) [NeZero q] (f : ℕ → ℂ)
    (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J Jb : ℕ) (hJb1 : 1 ≤ Jb)
    (hJbJ : Jb ≤ J) (hδ0 : 0 < δ) (T V : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hV : 1 ≤ V) (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log (Qseq Jb))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetChi q f Pseq Qseq δ J)
    (α η X ε : ℝ) (hVα : Real.log V ≤ α * Real.log (Pseq Jb)) (hα : α ≤ 1 / 4 - η)
    (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) (hX0 : 0 < X)
    (hdebit : (q : ℝ) ^ (2 * α) ≤ X ^ ε)
    (H : ℝ) (N Xd P Q j M : ℕ) (b c : ℕ → ℂ) (εQ : ℝ)
    (hM : ramRrange H N Xd j ⊆ Finset.Icc 1 M)
    (hbudget : thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η + ε)
      ≤ (M : ℝ)) :
    ∑ r ∈ TsetSmallChi q H P Q j c εQ ℰ,
        ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c) j r.2‖ ^ 2
      ≤ 2 * Cint * εQ ^ 2 * (M : ℝ) * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hbranch := TSChi_branch_meansq hCint hslot q hq H N Xd P Q j M b c hM εQ T hT1 ℰ hws
    hsub
  have hkill := UsetChi_thin_sqrt_kill_absorbed q f hf1 Pseq Qseq δ J Jb hJb1 hJbJ hδ0 T V
    hT1 hqT hV hVinv hP3 hQT hκ30 hLL5 ℰ hws hsub hU α η X ε hVα hα hη2 hTX hX0 hdebit
  have hcnt : (ℰ.card : ℝ) * Real.sqrt T ≤ (M : ℝ) := le_trans hkill hbudget
  have hlog : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hmass : (0 : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun m _ => by positivity)
  refine hbranch.trans ?_
  have hstep : Cint * ((M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T) * (1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
      ≤ 2 * Cint * (M : ℝ) * (1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) := by
    have hbr : (M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T ≤ 2 * (M : ℝ) := by linarith
    have hcoef : (0 : ℝ) ≤ Cint * ((1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hbr hcoef]
  nlinarith [mul_le_mul_of_nonneg_left hstep (sq_nonneg εQ)]

/-! ## §5 — the branch split and the `χ`-summed `hU` exit -/

/-- `𝒯_L` at pairs is the complement filter of `𝒯_S` at the SAME level — the byte-check that
the two branch files split one predicate and not two. -/
lemma tLsetChi_eq_filter_not (q : ℕ) (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (δ' : ℝ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) :
    tLsetChi q H P Q j c δ' ℰ
      = ℰ.filter (fun r => ¬ (‖ramQ H P Q j (chiBarCoeff q r.1 c) r.2‖ ≤ δ')) := by
  classical
  ext r
  simp only [tLsetChi, Finset.mem_filter, not_le]

/-- **The exhaustive split of a pair-block sum** — an IDENTITY: the `𝒯_S` and `𝒯_L` branches
partition `ℰ`, so no mass is lost or double-counted between the two exits. -/
lemma sum_TSChi_add_TLChi (q : ℕ) (H : ℝ) (N Xd P Q j : ℕ) (b c : ℕ → ℂ) (δ' : ℝ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) :
    (∑ r ∈ TsetSmallChi q H P Q j c δ' ℰ,
        ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c) j r.2‖ ^ 2)
      + (∑ r ∈ tLsetChi q H P Q j c δ' ℰ,
        ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c) j r.2‖ ^ 2)
      = ∑ r ∈ ℰ,
        ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c) j r.2‖ ^ 2 := by
  classical
  rw [tLsetChi_eq_filter_not, TsetSmallChi]
  exact Finset.sum_filter_add_sum_filter_not ℰ _ _

/-- **The fibre packing** — the inverse of `HybridLargeValues.exists_charFibre`: a family of
ordinate sets indexed by the characters assembles into one pair set.  Built with
`Finset.disjiUnion`/`Finset.map`, so no `DecidableEq` on characters is needed. -/
noncomputable def fibrePack {q : ℕ} (𝒯 : DirichletCharacter ℂ q → Finset ℝ) :
    Finset (DirichletCharacter ℂ q × ℝ) :=
  Finset.univ.disjiUnion
    (fun χ => (𝒯 χ).map ⟨fun t => (χ, t), fun t u h => by simpa using h⟩)
    (by
      intro χ _ χ' _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      rintro r ⟨t, _, rfl⟩ ⟨u, _, hu⟩
      exact hne (by simpa using (Prod.mk.injEq _ _ _ _).mp hu.symm |>.1))

@[simp] lemma mem_fibrePack {q : ℕ} {𝒯 : DirichletCharacter ℂ q → Finset ℝ}
    {r : DirichletCharacter ℂ q × ℝ} : r ∈ fibrePack 𝒯 ↔ r.2 ∈ 𝒯 r.1 := by
  rw [fibrePack, Finset.mem_disjiUnion]
  constructor
  · rintro ⟨χ, _, hr⟩
    rw [Finset.mem_map] at hr
    obtain ⟨t, ht, hrt⟩ := hr
    have h1 : χ = r.1 := by simpa using ((Prod.mk.injEq _ _ _ _).mp hrt).1
    have h2 : t = r.2 := by simpa using ((Prod.mk.injEq _ _ _ _).mp hrt).2
    rw [← h1, ← h2]; exact ht
  · intro hr
    exact ⟨r.1, Finset.mem_univ _, Finset.mem_map.mpr ⟨r.2, hr, rfl⟩⟩

/-- Sums over the packed pair set regroup as a double sum over characters and fibres. -/
lemma sum_fibrePack {q : ℕ} (𝒯 : DirichletCharacter ℂ q → Finset ℝ)
    (g : DirichletCharacter ℂ q → ℝ → ℝ) :
    (∑ r ∈ fibrePack 𝒯, g r.1 r.2) = ∑ χ : DirichletCharacter ℂ q, ∑ t ∈ 𝒯 χ, g χ t := by
  rw [fibrePack, Finset.sum_disjiUnion]
  exact Finset.sum_congr rfl (fun χ _ => Finset.sum_map _ _ _)

/-- Fibrewise well-spacing of the packed set is exactly well-spacing of every fibre. -/
lemma fibreWellSpaced_fibrePack {q : ℕ} (𝒯 : DirichletCharacter ℂ q → Finset ℝ)
    (hws : ∀ χ : DirichletCharacter ℂ q, WellSpaced (𝒯 χ)) :
    FibreWellSpaced (fibrePack 𝒯) := by
  intro r hr s hs hchar hord
  rw [mem_fibrePack] at hr hs
  rw [hchar] at hr
  exact hws s.1 r.2 hr s.2 hs hord

set_option maxHeartbeats 800000 in
-- The composition threads the eq-(16) decomposition, the per-character discretisation and
-- the pair-level branch split through one another; the unifier needs room for the composed
-- `ramMain`/`spoly` expressions at twisted data.
/-- **U-9b, `χ`-SUMMED — THE COMPOSITION.**  For a measurable `A ⊆ [−T,T]` (the consumer's
`(Ann ∖ ball) ∩ 𝒰`), with `χ`-SUMMED per-block branch bounds `Sb j`, `Lb j` valid for EVERY
per-fibre well-spaced pair set drawn from `A`:

  `Σ_χ ∫_A ‖Σ_{n≤N} χ̄(n)aₙ/n^{1+it}‖² ≤ 4·|I|·Σ_{j∈I} (Sb j + Lb j) + 2E`.

The three factors are the landed ones: `2·|I|` the eq-(16) Cauchy–Schwarz across blocks
(`meansq_on_subset_of_decomp`, character-blind and applied per `χ`), the extra `2` the
even/odd parity halving of `wellspaced_discretize` (also per `χ`), and `E` the `χ`-SUMMED
Lemma-12 error row — exactly what `HybridMoments.lemma12_meansq_all_chi` supplies.

The one new device is the packing: the discretisation produces one witness set per
`(χ, j)`, and `fibrePack` assembles the `χ`-family at each `j` into the single pair set the
branch bounds speak about. -/
theorem usetChi_integral_to_branches (q : ℕ) [NeZero q]
    (H : ℝ) (N Xd P Q : ℕ) (a b c : ℕ → ℂ) (T E : ℝ) (hT : 0 ≤ T)
    (herr : (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
        ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
          (chiBarCoeff q χ c) t‖ ^ 2) ≤ E)
    (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T)
    (δ' : ℝ) (Sb Lb : ℕ → ℝ)
    (hTS : ∀ j ∈ ramI H P Q, ∀ ℰ : Finset (DirichletCharacter ℂ q × ℝ),
      FibreWellSpaced ℰ → (∀ r ∈ ℰ, r.2 ∈ A) →
      (∑ r ∈ TsetSmallChi q H P Q j c δ' ℰ,
        ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c) j r.2‖ ^ 2) ≤ Sb j)
    (hTL : ∀ j ∈ ramI H P Q, ∀ ℰ : Finset (DirichletCharacter ℂ q × ℝ),
      FibreWellSpaced ℰ → (∀ r ∈ ℰ, r.2 ∈ A) →
      (∑ r ∈ tLsetChi q H P Q j c δ' ℰ,
        ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c) j r.2‖ ^ 2) ≤ Lb j) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in A, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
      ≤ 4 * ((ramI H P Q).card : ℝ) * (∑ j ∈ ramI H P Q, (Sb j + Lb j)) + 2 * E := by
  classical
  -- (i) eq (16) per character, the error kept as its own integral
  have hstep1 : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in A, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        ≤ 2 * ((ramI H P Q).card : ℝ)
            * (∑ j ∈ ramI H P Q, ∫ t in A,
                ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)
          + 2 * (∫ t in (-T)..T, ‖ramErr H N Xd P Q (chiBarCoeff q χ a)
              (chiBarCoeff q χ b) (chiBarCoeff q χ c) t‖ ^ 2) := by
    intro χ
    exact meansq_on_subset_of_decomp (N := N) (a := chiBarCoeff q χ a) (I := ramI H P Q)
      (mainPoly := ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c))
      (errPoly := ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
        (chiBarCoeff q χ c))
      (E := ∫ t in (-T)..T, ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
        (chiBarCoeff q χ c) t‖ ^ 2)
      (T := T) (A := A) hT hAm hAsub
      (fun j _ => continuous_ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j)
      (continuous_ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
        (chiBarCoeff q χ c))
      (fun t => spoly_ram_decomp H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
        (chiBarCoeff q χ c) t)
      (le_refl _)
  -- (ii) per block: discretise every fibre, pack, split at `δ'`
  have hper : ∀ j ∈ ramI H P Q,
      (∑ χ : DirichletCharacter ℂ q, ∫ t in A,
          ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)
        ≤ 2 * (Sb j + Lb j) := by
    intro j hj
    have hdisc : ∀ χ : DirichletCharacter ℂ q, ∃ 𝒯 : Finset ℝ, (↑𝒯 : Set ℝ) ⊆ A ∧
        WellSpaced 𝒯 ∧
        (∫ t in A, ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)
          ≤ 2 * ∑ t ∈ 𝒯,
            ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2 := by
      intro χ
      exact wellspaced_discretize T
        (fun t => ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)
        ((continuous_ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j).norm.pow 2)
        (fun t => by positivity) A hAm hAsub
    choose 𝒯 h𝒯A hws hle using hdisc
    have hpack_sub : ∀ r ∈ fibrePack 𝒯, r.2 ∈ A := by
      intro r hr
      exact h𝒯A r.1 (Finset.mem_coe.mpr (mem_fibrePack.mp hr))
    have hpack_ws : FibreWellSpaced (fibrePack 𝒯) := fibreWellSpaced_fibrePack 𝒯 hws
    have hregroup : (∑ χ : DirichletCharacter ℂ q, ∑ t ∈ 𝒯 χ,
          ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)
        = ∑ r ∈ fibrePack 𝒯,
          ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c) j r.2‖ ^ 2 :=
      (sum_fibrePack 𝒯 (fun χ t =>
        ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)).symm
    have hsplit := sum_TSChi_add_TLChi q H N Xd P Q j b c δ' (fibrePack 𝒯)
    have h1 := hTS j hj (fibrePack 𝒯) hpack_ws hpack_sub
    have h2 := hTL j hj (fibrePack 𝒯) hpack_ws hpack_sub
    have hsum : (∑ χ : DirichletCharacter ℂ q, ∫ t in A,
          ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)
        ≤ 2 * ∑ χ : DirichletCharacter ℂ q, ∑ t ∈ 𝒯 χ,
            ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun χ _ => hle χ)
    rw [hregroup, ← hsplit] at hsum
    linarith
  -- (iii) assemble
  have hchi := Finset.sum_le_sum
    (fun (χ : DirichletCharacter ℂ q) (_ : χ ∈ Finset.univ) => hstep1 χ)
  have hdistrib : (∑ χ : DirichletCharacter ℂ q,
        (2 * ((ramI H P Q).card : ℝ)
            * (∑ j ∈ ramI H P Q, ∫ t in A,
                ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)
          + 2 * (∫ t in (-T)..T, ‖ramErr H N Xd P Q (chiBarCoeff q χ a)
              (chiBarCoeff q χ b) (chiBarCoeff q χ c) t‖ ^ 2)))
      = 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∑ χ : DirichletCharacter ℂ q, ∫ t in A,
              ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)
        + 2 * (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
            ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
              (chiBarCoeff q χ c) t‖ ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  rw [hdistrib] at hchi
  have hblocks : (∑ j ∈ ramI H P Q, ∑ χ : DirichletCharacter ℂ q, ∫ t in A,
        ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)
      ≤ 2 * ∑ j ∈ ramI H P Q, (Sb j + Lb j) := by
    refine le_trans (Finset.sum_le_sum hper) ?_
    rw [← Finset.mul_sum]
  have hcard0 : (0 : ℝ) ≤ 2 * ((ramI H P Q).card : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hblocks hcard0
  linarith

end Salt.MR
