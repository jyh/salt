/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Lemma7Kappa

/-!
# HB 1983, Lemma 7 — node **CHAR-TRIO**: the three character-side riders of W4.5

Wave W4.5 (`Salt/HB/Lemma7Kappa.lean`) closed the sieve algebra of HB's rows `(4.4)`/`(4.5)`
and left its capstone `hb_L2_at_split_point_concrete` carrying **three** binders that are
character theory rather than sieve algebra:

* `hchi01` — `χ_ℝ(p) ∈ {1, −1, 0}` for a real (quadratic) `χ`;
* `hchi0`  — `χ_ℝ(p) = 0 ↔ p ∣ q`;
* `hL1`    — the Euler product for `L(1,χ)` split at `z`:
             `L(1,χ) = (∏_{p ≤ ⌊z⌋}(1 − χ(p)/p))^{−1} · F`.

This file discharges the first two **outright** from the single hypothesis `χ ^ 2 = 1`, and
takes the third as far as it can honestly be taken with what mathlib has (see §3).

## §1–§2 — `hchi01` and `hchi0`

Both come off mathlib's quadratic-character apparatus.  `MulChar.isQuadratic_iff_sq_eq_one`
turns `χ ^ 2 = 1` into `χ.IsQuadratic` (`∀ a, χ a = 0 ∨ χ a = 1 ∨ χ a = −1`), whence the value
trichotomy for `χ_ℝ = Re ∘ χ` and — crucially, and *only* because `χ` is quadratic —
the equivalence `χ_ℝ(n) = 0 ↔ χ(n) = 0` (for a general complex `χ` the real part can vanish at
a unit, e.g. `χ(n) = i`).  Then `MulChar.apply_eq_zero_iff` and
`ZMod.isUnit_prime_iff_not_dvd` give `χ_ℝ(p) = 0 ↔ p ∣ q` at primes, and
`ZMod.isUnit_iff_coprime` the general-`n` form `χ_ℝ(n) = 0 ↔ ¬ n.Coprime q`.

## §3 — `hL1`: what is landed, and what is flagged

**Landed.**  `hbL1 χ z` names the split-at-`z` Euler value
`(∏_{p ≤ ⌊z⌋}(1 − χ(p)/p))^{−1} · F`, so the capstone's `hL1` binder is discharged **by
definition** (`hbL1_eq`), and the composite `hb_L2_at_split_point_charTrio` below has *no*
character binders left at all — only `χ ^ 2 = 1`.  Better, `hbL1` is shown to be the honest
**ordered Euler product over all primes**: whenever the tail log-product converges (the corpus's
own convergence idiom, the `Tendsto (hbEulerLog χ z ·) atTop (𝓝 A)` binder that
`hb_hcorr_closed` already carries), the partial products `∏_{p ≤ Y}(1 − χ(p)/p)^{−1}` converge
to `hbL1 χ z` (`tendsto_hbEulerProdBelow_hbL1`).  Two corollaries fall out: the split point is
immaterial (`hbL1_split_indep`), and `hbL1 χ z` is pinned by any identification of that limit
(`hbL1_eq_of_tendsto`).

**Flagged.**  What is *not* landed is the arithmetic identification of that limit with mathlib's
`DirichletCharacter.LFunction χ 1`, i.e.

    hbL1 χ z = (DirichletCharacter.LFunction χ 1).re      (χ ≠ 1, χ ^ 2 = 1)

`s = 1` is the boundary: mathlib's Euler-product machinery
(`DirichletCharacter.LSeries_eulerProduct_hasProd`, `eulerProduct_completely_multiplicative`)
is stated for `1 < s.re` and rests on `Summable (‖·‖)`, which fails at `s = 1`; and mathlib has
no Mertens-type theorem for `∑_p χ(p)/p`.  Forcing an unconditional statement here would either
be false or would quietly assume the convergence it is supposed to prove.  The route is priced
in `docs/blueprints/flags.md` under `CHAR-TRIO`.  Everything downstream of the capstone is
already independent of that identification: it is needed only where a *lower bound* on the
L-value enters (Siegel, `Salt/SW/Siegel.lean`).
-/

open Filter Set MeasureTheory
open Salt.SW
open scoped Topology

namespace Salt.HB

/-! ## §1 — `hchi01`: the value trichotomy of a real character -/

/-- **`χ_ℝ` takes only the values `1`, `−1`, `0`** when `χ` is real (`χ² = 1`) — the `hchi01`
rider of W4.5, in the binder's own order.  Stated for every natural argument; the prime-indexed
form the capstone wants is `hb_hchi01`. -/
lemma chiRe_eq_one_or_neg_one_or_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (n : ℕ) : Salt.TwinBar.chiRe χ n = 1 ∨ Salt.TwinBar.chiRe χ n = -1 ∨
      Salt.TwinBar.chiRe χ n = 0 := by
  have hQ : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq
  unfold Salt.TwinBar.chiRe
  rcases hQ ((n : ZMod q)) with h | h | h <;> rw [h] <;> simp

/-- **`χ_ℝ(n) = 0 ↔ χ(n) = 0`** for a real character.  This is where `χ² = 1` is genuinely
needed: for a general complex `χ` the real part may vanish at a unit (`χ(n) = ±i`). -/
lemma chiRe_eq_zero_iff_map_eq_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (n : ℕ) : Salt.TwinBar.chiRe χ n = 0 ↔ χ ((n : ZMod q)) = 0 := by
  have hQ : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq
  constructor
  · intro h0
    rcases hQ ((n : ZMod q)) with h | h | h
    · exact h
    · rw [Salt.TwinBar.chiRe, h] at h0; norm_num at h0
    · rw [Salt.TwinBar.chiRe, h] at h0; norm_num at h0
  · intro h0
    rw [Salt.TwinBar.chiRe, h0]
    simp

/-- **`χ_ℝ(n) = 0 ↔ (n, q) ≠ 1`** — the general-`n` form of `hchi0`. -/
lemma chiRe_eq_zero_iff_not_coprime {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (n : ℕ) : Salt.TwinBar.chiRe χ n = 0 ↔ ¬ Nat.Coprime n q := by
  rw [chiRe_eq_zero_iff_map_eq_zero χ hsq n, MulChar.apply_eq_zero_iff,
    ZMod.isUnit_iff_coprime]

/-- **`χ_ℝ(p) = 0 ↔ p ∣ q`** at a prime — the `hchi0` rider of W4.5. -/
lemma chiRe_prime_eq_zero_iff_dvd {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {p : ℕ} (hp : Nat.Prime p) : Salt.TwinBar.chiRe χ p = 0 ↔ p ∣ q := by
  rw [chiRe_eq_zero_iff_map_eq_zero χ hsq p, MulChar.apply_eq_zero_iff,
    ZMod.isUnit_prime_iff_not_dvd hp, not_not]

/-! ## §2 — the two riders in the capstone's exact binder shapes -/

/-- **`hchi01`, discharged** — verbatim in the shape `hb_L2_at_split_point_concrete` binds. -/
theorem hb_hchi01 {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) :
    ∀ p : ℕ, Nat.Prime p → Salt.TwinBar.chiRe χ p = 1 ∨
      Salt.TwinBar.chiRe χ p = -1 ∨ Salt.TwinBar.chiRe χ p = 0 :=
  fun p _ => chiRe_eq_one_or_neg_one_or_zero χ hsq p

/-- **`hchi0`, discharged** — verbatim in the shape `hb_L2_at_split_point_concrete` binds. -/
theorem hb_hchi0 {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) :
    ∀ p : ℕ, Nat.Prime p → (Salt.TwinBar.chiRe χ p = 0 ↔ p ∣ q) :=
  fun _ hp => chiRe_prime_eq_zero_iff_dvd χ hsq hp

/-! ## §3 — `hL1`: the split Euler value as an object, and its ordered-product identity -/

/-- **The split-at-`z` Euler value** `(∏_{p ≤ ⌊z⌋}(1 − χ(p)/p))^{−1} · F` — the right-hand side
of the capstone's `hL1` binder, named.  HB writes it `L(1,χ)`; that identification is the one
piece of the rider this file does not pay (see the module docstring and the `CHAR-TRIO` flag). -/
noncomputable def hbL1 {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) : ℝ :=
  (∏ p ∈ Pz z, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)))⁻¹ * hbF χ z

/-- `hbL1` discharges the capstone's `hL1` binder by definition. -/
lemma hbL1_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) :
    hbL1 χ z = (∏ p ∈ Pz z, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)))⁻¹ * hbF χ z := rfl

/-- The finite factor `∏_{p ≤ ⌊z⌋}(1 − χ(p)/p)` is positive (each factor is `≥ 1/2`). -/
lemma prod_one_sub_chiRe_div_Pz_pos {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) :
    (0 : ℝ) < ∏ p ∈ Pz z, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)) :=
  Finset.prod_pos (fun _ hp => one_sub_chiRe_div_pos χ (mem_Pz.mp hp).2)

@[simp] lemma hbL1_pos {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) : 0 < hbL1 χ z :=
  mul_pos (inv_pos.mpr (prod_one_sub_chiRe_div_Pz_pos χ z)) (hbF_pos χ z)

/-- **The ordered partial Euler product** `∏_{p ≤ ⌊Y⌋}(1 − χ(p)/p)^{−1}` — the object whose
limit HB's `L(1,χ)` is. -/
noncomputable def hbEulerProdBelow {q : ℕ} (χ : DirichletCharacter ℂ q) (Y : ℝ) : ℝ :=
  ∏ p ∈ Pz Y, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ))⁻¹

/-- The primes `≤ ⌊Y⌋` split at `z` into the primes `≤ ⌊z⌋` and the window `(⌊z⌋, ⌊Y⌋]`. -/
lemma Pz_eq_union_windowPrimes {z Y : ℝ} (h : ⌊z⌋₊ ≤ ⌊Y⌋₊) :
    Pz Y = Pz z ∪ windowPrimes z Y := by
  ext p
  simp only [mem_Pz, Finset.mem_union, mem_windowPrimes]
  constructor
  · rintro ⟨hpY, hpp⟩
    by_cases hpz : p ≤ ⌊z⌋₊
    · exact Or.inl ⟨hpz, hpp⟩
    · exact Or.inr ⟨⟨by omega, hpY⟩, hpp⟩
  · rintro (⟨hpz, hpp⟩ | ⟨⟨_, hpY⟩, hpp⟩)
    · exact ⟨by omega, hpp⟩
    · exact ⟨hpY, hpp⟩

lemma Pz_disjoint_windowPrimes {z Y : ℝ} : Disjoint (Pz z) (windowPrimes z Y) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  have h1 := (mem_Pz.mp hp).1
  have h2 := (mem_windowPrimes.mp hp').1.1
  omega

/-- **The split of the ordered partial product at `z`**: for `⌊z⌋ ≤ ⌊Y⌋`,

    ∏_{p ≤ ⌊Y⌋}(1 − χ(p)/p)^{−1} = (∏_{p ≤ ⌊z⌋}(1 − χ(p)/p))^{−1} · ∏_{z < p ≤ Y}(1 − χ(p)/p)^{−1}.
-/
lemma hbEulerProdBelow_split {q : ℕ} (χ : DirichletCharacter ℂ q) {z Y : ℝ}
    (h : ⌊z⌋₊ ≤ ⌊Y⌋₊) :
    hbEulerProdBelow χ Y
      = (∏ p ∈ Pz z, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)))⁻¹ * hbEulerProd χ z Y := by
  rw [hbEulerProdBelow, Pz_eq_union_windowPrimes h,
    Finset.prod_union Pz_disjoint_windowPrimes, hbEulerProd, ← Finset.prod_inv_distrib]

/-- **`hbL1` really is the Euler product over *all* primes.**  Under the corpus's own
convergence hypothesis for the `p > z` log-tail — the same `Tendsto (hbEulerLog χ z ·) atTop`
binder `hb_hcorr_closed` carries — the ordered partial products `∏_{p ≤ Y}(1 − χ(p)/p)^{−1}`
converge to `hbL1 χ z`.  In particular the split point `z` is an accident of bookkeeping, not
part of the value. -/
theorem tendsto_hbEulerProdBelow_hbL1 {q : ℕ} (χ : DirichletCharacter ℂ q) {z A : ℝ}
    (h : Tendsto (fun Y : ℝ => hbEulerLog χ z Y) atTop (𝓝 A)) :
    Tendsto (fun Y : ℝ => hbEulerProdBelow χ Y) atTop (𝓝 (hbL1 χ z)) := by
  have hmain : Tendsto
      (fun Y : ℝ => (∏ p ∈ Pz z, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)))⁻¹ * hbEulerProd χ z Y)
      atTop (𝓝 (hbL1 χ z)) := by
    rw [hbL1_eq]
    exact (tendsto_hbEulerProd_hbF χ h).const_mul _
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop z] with Y hY
  exact (hbEulerProdBelow_split χ (Nat.floor_mono hY)).symm

/-- **`hbL1` is pinned by any identification of the full ordered Euler product.**  This is the
exact hook for the remaining rider: exhibit `B` with `∏_{p ≤ Y}(1 − χ(p)/p)^{−1} → B` and
`hbL1 χ z = B` follows. -/
theorem hbL1_eq_of_tendsto {q : ℕ} (χ : DirichletCharacter ℂ q) {z A B : ℝ}
    (h : Tendsto (fun Y : ℝ => hbEulerLog χ z Y) atTop (𝓝 A))
    (hfull : Tendsto (fun Y : ℝ => hbEulerProdBelow χ Y) atTop (𝓝 B)) :
    hbL1 χ z = B :=
  tendsto_nhds_unique (tendsto_hbEulerProdBelow_hbL1 χ h) hfull

/-- **The split point is immaterial**: two split points at which the tail log-product converges
give the same value. -/
theorem hbL1_split_indep {q : ℕ} (χ : DirichletCharacter ℂ q) {z z' A A' : ℝ}
    (h : Tendsto (fun Y : ℝ => hbEulerLog χ z Y) atTop (𝓝 A))
    (h' : Tendsto (fun Y : ℝ => hbEulerLog χ z' Y) atTop (𝓝 A')) :
    hbL1 χ z = hbL1 χ z' :=
  tendsto_nhds_unique (tendsto_hbEulerProdBelow_hbL1 χ h) (tendsto_hbEulerProdBelow_hbL1 χ h')

/-! ## §4 — the consumer-ready composites -/

/-- **`(L2)` at the split point with the two character-value riders discharged.**  Exactly
`hb_L2_at_split_point_concrete`, with `hchi01`/`hchi0` replaced by the single hypothesis
`χ ^ 2 = 1` (χ real).  Only the L-value binder `hL1` remains. -/
theorem hb_L2_at_split_point_char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hsq : χ ^ 2 = 1)
    {α : ℕ} {β₀ L η z x X L1 Ecorr Eseg Etail EP : ℝ} {Stail : ℂ}
    (hq : 0 < q)
    (hα0 : 0 < α) (hα2 : 2 ∣ α)
    (hβ₀1 : β₀ < 1) (hL : 0 < L) (hη : η = 1 / ((1 - β₀) * L))
    (hz : 32 ≤ z) (hαz : (α : ℝ) < z)
    (hX : 3 ≤ X) (hwin : Real.log X ≤ 500 * L) (hηlarge : 500 ≤ η)
    (hm1 : zeroMult χ (β₀ : ℂ) = 1)
    (htail : ‖Stail + ((zeroMult χ (β₀ : ℂ) : ℕ) : ℂ)
        * ((∫ v in Ioi X, v ^ (β₀ - 2) / Real.log v : ℝ) : ℂ)‖ ≤ Etail)
    (hseg : |(logChiSum χ z X).re
        - (Real.log (Real.log z) - Real.log (Real.log X))| ≤ Eseg)
    (hcorr : |Real.log (hbF χ z) - ((logChiSum χ z X).re + Stail.re)| ≤ Ecorr)
    (hP : |Real.log (primeProdBelow z) + Real.log (Real.log z)
        + Real.eulerMascheroniConstant| ≤ EP)
    (hL1 : L1 = (∏ p ∈ Pz z, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)))⁻¹ * hbF χ z)
    (hsmall : 4 * (Ecorr + Eseg + Etail + 500 * (1 + 2 * Real.log (η * L)) / η)
        + 8 * EP + 2 * (64 / z) ≤ 1) :
    ∃ δ : ℝ,
      hbKappa χ α x L1 * hbS1 χ α z
        = (1 + δ) * (x * Salt.HardyLittlewood.twinSingularSeries * hbCalpha α / (η * L) ^ 2)
      ∧ |δ| ≤ 4 * (Ecorr + Eseg + Etail + 500 * (1 + 2 * Real.log (η * L)) / η)
          + 8 * EP + 2 * (2 * (Real.log q / Real.log z) / z) + 2 * (64 / z) :=
  hb_L2_at_split_point_concrete χ hq (hb_hchi01 χ hsq) (hb_hchi0 χ hsq) hα0 hα2 hβ₀1 hL hη
    hz hαz hX hwin hηlarge hm1 htail hseg hcorr hP hL1 hsmall

/-- **`(L2)` at the split point with **no** character binders at all** — `hchi01`, `hchi0` and
`hL1` all gone, the L-value entering as the corpus's own `hbL1 χ z` (the ordered Euler product,
by `tendsto_hbEulerProdBelow_hbL1`).  This is the shape the N5/N6 consumer wiring should plug
into; identifying `hbL1 χ z` with `(LFunction χ 1).re` is the single remaining rider
(flag `CHAR-TRIO`), and it is needed only where a *lower bound* on the L-value enters. -/
theorem hb_L2_at_split_point_charTrio {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hsq : χ ^ 2 = 1)
    {α : ℕ} {β₀ L η z x X Ecorr Eseg Etail EP : ℝ} {Stail : ℂ}
    (hq : 0 < q)
    (hα0 : 0 < α) (hα2 : 2 ∣ α)
    (hβ₀1 : β₀ < 1) (hL : 0 < L) (hη : η = 1 / ((1 - β₀) * L))
    (hz : 32 ≤ z) (hαz : (α : ℝ) < z)
    (hX : 3 ≤ X) (hwin : Real.log X ≤ 500 * L) (hηlarge : 500 ≤ η)
    (hm1 : zeroMult χ (β₀ : ℂ) = 1)
    (htail : ‖Stail + ((zeroMult χ (β₀ : ℂ) : ℕ) : ℂ)
        * ((∫ v in Ioi X, v ^ (β₀ - 2) / Real.log v : ℝ) : ℂ)‖ ≤ Etail)
    (hseg : |(logChiSum χ z X).re
        - (Real.log (Real.log z) - Real.log (Real.log X))| ≤ Eseg)
    (hcorr : |Real.log (hbF χ z) - ((logChiSum χ z X).re + Stail.re)| ≤ Ecorr)
    (hP : |Real.log (primeProdBelow z) + Real.log (Real.log z)
        + Real.eulerMascheroniConstant| ≤ EP)
    (hsmall : 4 * (Ecorr + Eseg + Etail + 500 * (1 + 2 * Real.log (η * L)) / η)
        + 8 * EP + 2 * (64 / z) ≤ 1) :
    ∃ δ : ℝ,
      hbKappa χ α x (hbL1 χ z) * hbS1 χ α z
        = (1 + δ) * (x * Salt.HardyLittlewood.twinSingularSeries * hbCalpha α / (η * L) ^ 2)
      ∧ |δ| ≤ 4 * (Ecorr + Eseg + Etail + 500 * (1 + 2 * Real.log (η * L)) / η)
          + 8 * EP + 2 * (2 * (Real.log q / Real.log z) / z) + 2 * (64 / z) :=
  hb_L2_at_split_point_char χ hsq hq hα0 hα2 hβ₀1 hL hη hz hαz hX hwin hηlarge hm1 htail hseg
    hcorr hP (hbL1_eq χ z) hsmall

end Salt.HB
