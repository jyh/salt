/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.CountFinal
import Salt.Chen.BetaSW
import Salt.Chen.GlueNormalized

/-!
# CNTW — the AP-restricted count line (H-AMENDMENT 2, D5 + gate correction C6)

Design: `docs/blueprints/chen.md`, "H-AMENDMENT 2" D5 + "GATE RESULT" C6/C3;
`docs/blueprints/flags.md`, the CATCH #65 and H2-GATE entries.

## The convention (D5, fixed against Assembly's `keepW` and A3W's needs)

Assembly's W-carriers (`Salt/Chen/Assembly.lean`, Part H) filter the razor window on `n`:
`keepW Q a P n` keeps `n ≡ a (mod Q)`.  The switch weight counts triples with
`p₁p₂p₃ = n + 2`, so the AP restriction transported to the triple side is on the PRODUCT:

  `n ≡ a (mod Q)  ⟺  prod3 t = n + 2 ≡ a + 2 (mod Q)`      (`window_class_iff`).

Hence:
* `tripleSumW Q a x z y` — the window form (support filter on `n`, matching the SwitchW
  carriers): `Σ_{n ∈ twinWindow x, n ≡ a (Q)} aCount x z y n`;
* `tripleSetW Q a x z y` — the triple form: `{t ∈ tripleSet x z y : prod3 t ≡ a + 2 (Q)}`;
* `tripleSumW_eq_card` — the two agree (the Fubini reindex at the AP class).

## The equidistribution row (D5, the p₃-fiber route the gate verified)

`tripleSet` fibers EXACTLY over `pairSet` with `p₃`-fiber the primes of the interval
`(Lcut, Ufun]` (`Lcut = max(⌊(⌊x/2⌋+1)/p₁p₂⌋, p₂−1)`; `tripleSum_eq_fiberSum`,
`tripleSumW_eq_fiberSum` — an identity, unlike the landed one-directional injection).
Per fiber, the class `p₁p₂p₃ ≡ a+2 (Q)` is a REDUCED class `p₃ ≡ c (Q)`,
`c = u·(a+2)` with `u` the mod-`Q` inverse of `p₁p₂` (`gcd(p₁p₂, Q) = 1` since `p₁, p₂ ≥ z`
exceed every prime of `Q`; `gcd(c, Q) = 1` from `gcd(a+2, Q) = 1`).  The landed fixed-modulus
SW (`BetaSW.prime_indicator_SW`) prices the fiber block `(Lcut, min(Ufun, 2·Lcut)]`
(`Ufun ≤ 2·Lcut + 1`, so at most ONE boundary point escapes the `M ≤ 2N` block shape):

  `|tripleSumW − tripleSum/φ(Q)| ≤ K·x/(log Lval)^A · Σ_{pairSet} 1/(p₁p₂) + 2·|pairSet|`.

## The GLU-2W row ledger (named hypothesis rows; each discharged at the instance)

* `hQ : 0 < Q` — free at `Q = Qval ε` (a primorial).
* `hQa2 : Coprime Q (a+2)` — free at `a = Q − 1` (`Assembly.residue_witness`).
* `hQz : ∀ p prime ∣ Q, p < z` — `Qval ε`'s primes are `< w0N ε ≤ z` (the W-SURG split).
* `hLval3 / hN₀ : 3 ≤ Lval x y`, `N₀ ≤ Lval x y` — x-threshold rows: at the operating point
  `Lval = ⌊x/(2y√x)⌋ ≈ x^{1/6}/2`, so any fixed SW threshold is absorbed by `x₀`.
* `hQrange : (Q : ℝ) ≤ (log(Lval x y))^C` — the C6 range row.  `log Lval ≈ (log x)/6`, and
  `Q ≤ 4^{w₀} ≤ L = log x` (gate C2/C67), so `C ≥ 2` suffices once `L ≥ 6²·6^... `-form —
  concretely `(L/6)² ≥ L` for `L ≥ 36`; C6 verified `C ≥ 2` needed and available.
* Error budget (C6): the SW piece is `≤ K·x/(log Lval)^A·M₁M₂` with `M₁M₂ ≈ 0.4` the
  windowed-Mertens product (`tripleSumW_equidist_mertens`) — a `6^A·K·x/(log x)^A`-form,
  i.e. `x/(log x)^{A−2}`-relative to the AP main scale `x/(φ(Q)·log x) ≥ x/(log x)²`
  (`φ(Q) ≤ Q ≤ L`): beaten for `A ≥ 3`, and the `6^A` constant is absorbed at the
  `A = 13` convention.  The boundary piece `2·|pairSet| ≤ 2·y·√x ≈ 2·x^{5/6}`
  (`pairSet_card_le`) is polynomially small.

## The W keystone (deliverable 3)

`tripleSum_le_cbar_final_W` — the landed count keystone (`CountFinal.tripleSum_le_cbar_final`,
whose c̄ integrals are RATIO-level and AP-invariant per the gate) divided by `φ(Q)`, plus the
equidistribution error: `tripleSumW ≤ (landed c̄/2-form)/φ(Q) + (SW error form)`.  Per gate
correction C3, GLU-2W compares this against the SMOOTH `totalMass/φ(Q)` in GlueNormalized's
`hcount` slot — the composition typechecks (`example` at EOF, values symbolic).

No `sorry`, no `native_decide`, no new axioms.
-/

open scoped BigOperators

namespace Salt.Chen

/-! ## Section 1 — the AP-restricted count: definitions and filter algebra -/

/-- The n-side ↔ product-side class convention (D5): the window filter `n ≡ a (mod Q)`
matches the triple filter `prod3 = n + 2 ≡ a + 2 (mod Q)`. -/
theorem window_class_iff {Q a n : ℕ} : n % Q = a % Q ↔ (n + 2) % Q = (a + 2) % Q :=
  ⟨fun h => Nat.ModEq.add_right 2 h, fun h => Nat.ModEq.add_right_cancel' 2 h⟩

/-- The AP-restricted admissible triple set: triples of `tripleSet` whose product lies in the
shifted class `a + 2 mod Q` (the D5 convention: the SwitchW support filter is on `n`, and
`prod3 t = n + 2`). -/
def tripleSetW (Q a x z y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (tripleSet x z y).filter (fun t => prod3 t % Q = (a + 2) % Q)

/-- **`tripleSumW` — the AP-restricted triple count** (window form, matching the SwitchW
carriers): the switch weights `aCount` summed over the AP-restricted window
`{n ∈ twinWindow x : n ≡ a (mod Q)}`. -/
noncomputable def tripleSumW (Q a x z y : ℕ) : ℝ :=
  ∑ n ∈ (twinWindow x).filter (fun n => n % Q = a % Q), aCount x z y n

/-- Membership in `tripleSetW` (filter algebra). -/
theorem mem_tripleSetW {Q a x z y : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ tripleSetW Q a x z y ↔ t ∈ tripleSet x z y ∧ prod3 t % Q = (a + 2) % Q :=
  Finset.mem_filter

/-- `tripleSetW ⊆ tripleSet` (filter algebra). -/
theorem tripleSetW_subset (Q a x z y : ℕ) : tripleSetW Q a x z y ⊆ tripleSet x z y :=
  Finset.filter_subset _ _

/-- `tripleSumW` is nonnegative. -/
theorem tripleSumW_nonneg (Q a x z y : ℕ) : 0 ≤ tripleSumW Q a x z y :=
  Finset.sum_nonneg (fun n _ => by unfold aCount; positivity)

/-- **`tripleSumW ≤ tripleSum`**: dropping the AP filter only adds nonnegative weights. -/
theorem tripleSumW_le_tripleSum (Q a x z y : ℕ) :
    tripleSumW Q a x z y ≤ tripleSum x z y := by
  unfold tripleSumW tripleSum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun n _ _ => by unfold aCount; positivity)

/-- **The AP Fubini reindex.**  The window form equals the triple form:
`tripleSumW Q a x z y = #tripleSetW Q a x z y`.  Mirror of the landed `tripleSum_eq_card`;
the AP filters correspond under `n = prod3 t − 2` via `window_class_iff`. -/
theorem tripleSumW_eq_card (Q a x z y : ℕ) :
    tripleSumW Q a x z y = ((tripleSetW Q a x z y).card : ℝ) := by
  unfold tripleSumW aCount
  rw [← Nat.cast_sum]
  congr 1
  have Hmem : ∀ t ∈ tripleSetW Q a x z y,
      prod3 t - 2 ∈ (twinWindow x).filter (fun n => n % Q = a % Q) := by
    intro t ht
    rw [tripleSetW, Finset.mem_filter] at ht
    obtain ⟨htS, htQ⟩ := ht
    rw [tripleSet, Finset.mem_filter] at htS
    obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := htS
    rw [Finset.mem_filter, twinWindow, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h2 : prod3 t - 2 + 2 = prod3 t := by omega
    have hstep : (prod3 t - 2) + 2 ≡ a + 2 [MOD Q] := by rw [h2]; exact htQ
    exact Nat.ModEq.add_right_cancel' 2 hstep
  rw [Finset.card_eq_sum_card_fiberwise Hmem]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  obtain ⟨_, hnq⟩ := hn
  congr 1
  rw [tripleSetW, Finset.filter_filter]
  refine Finset.filter_congr (fun t ht => ?_)
  rw [tripleSet, Finset.mem_filter] at ht
  obtain ⟨_, _, _, _, _, _, _, _, hlo, _⟩ := ht
  constructor
  · intro h
    refine ⟨?_, by omega⟩
    rw [h]
    exact Nat.ModEq.add_right 2 hnq
  · rintro ⟨-, h⟩
    omega

/-! ## Section 2 — the exact `p₃`-fiber decomposition over `pairSet`

The landed reduction (`card_tripleSet_le_pairSum`) is one-directional (an injection into
`(Lfun, Ufun]`); the equidistribution row needs an IDENTITY.  The exact fiber over a pair
`q = (p₁, p₂)` is the primes of `(Lcut x q, Ufun x q]` with
`Lcut = max(⌊(⌊x/2⌋+1)/(p₁p₂)⌋, p₂ − 1)`: the first component encodes `x/2 + 2 ≤ p₁p₂p₃`
(ℕ-division: `⌊(⌊x/2⌋+1)/m⌋ < p ⟺ ⌊x/2⌋ + 2 ≤ m·p`), the second `p₂ ≤ p₃`. -/

/-- The exact fiber lower endpoint: `Lcut x q = max(⌊(⌊x/2⌋+1)/(q₁q₂)⌋, q₂ − 1)`. -/
def Lcut (x : ℕ) (q : ℕ × ℕ) : ℕ := max ((x / 2 + 1) / (q.1 * q.2)) (q.2 - 1)

/-- The unrestricted `p₃`-fiber over `q`: primes in `(Lcut x q, Ufun x q]`. -/
def fiberPrimes (x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (Finset.Ioc (Lcut x q) (Ufun x q)).filter (fun p => p.Prime)

/-- The AP-restricted `p₃`-fiber over `q`: primes in `(Lcut x q, Ufun x q]` with
`q₁q₂·p ≡ a + 2 (mod Q)`. -/
def fiberPrimesW (Q a x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (Finset.Ioc (Lcut x q) (Ufun x q)).filter
    (fun p => p.Prime ∧ (q.1 * q.2 * p) % Q = (a + 2) % Q)

/-- The projection of `tripleSet` lands in `pairSet` (landed `Hmem`, extracted). -/
private lemma proj_mem_pairSet {x z y : ℕ} :
    ∀ t ∈ tripleSet x z y, (t.1, t.2.1) ∈ pairSet x z y := by
  intro t ht
  rw [tripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
  obtain ⟨⟨ht1, ht21, _⟩, hz1, hy1, hy2, h23, hp1, hp2, _hp3, _hlo, hhi⟩ := ht
  rw [pairSet, Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨ht1, ht21⟩, hz1, hy1, hy2, ?_, hp1, hp2⟩
  have h1 : t.2.1 * t.2.1 ≤ t.2.1 * t.2.2 := Nat.mul_le_mul_left _ h23
  have h2 : t.2.1 * t.2.2 ≤ prod3 t := by
    rw [prod3]
    calc t.2.1 * t.2.2 ≤ t.1 * (t.2.1 * t.2.2) := Nat.le_mul_of_pos_left _ hp1.pos
      _ = t.1 * t.2.1 * t.2.2 := by ring
  exact le_trans (le_trans h1 h2) hhi

/-- **The parametrized fiber bijection.**  For `q ∈ pairSet` and any product-side class
predicate `C`, the `q`-fiber of `tripleSet` filtered by `C(prod3)` is in bijection (via
`t ↦ p₃`) with the primes of `(Lcut, Ufun]` filtered by `C(q₁q₂·p)`. -/
private lemma fiber_card_bij {x z y : ℕ} {q : ℕ × ℕ} (hq : q ∈ pairSet x z y)
    (C : ℕ → Prop) [DecidablePred C] :
    ((tripleSet x z y).filter (fun t => (t.1, t.2.1) = q ∧ C (prod3 t))).card
      = ((Finset.Ioc (Lcut x q) (Ufun x q)).filter
          (fun p => p.Prime ∧ C (q.1 * q.2 * p))).card := by
  rw [pairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
  obtain ⟨⟨⟨hq1lo, hq1x⟩, hq2lo, hq2x⟩, hzq1, hq1y, hyq2, hq2sq, hp1, hp2⟩ := hq
  have hm : 0 < q.1 * q.2 := Nat.mul_pos hp1.pos hp2.pos
  refine Finset.card_bij (fun t _ => t.2.2) ?_ ?_ ?_
  · -- MapsTo: the fiber element's p₃ lands in the window with the transported class
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htS, hproj, hC⟩ := ht
    have ht1 : q.1 = t.1 := by rw [← hproj]
    have ht2 : q.2 = t.2.1 := by rw [← hproj]
    rw [tripleSet, Finset.mem_filter] at htS
    obtain ⟨-, -, -, -, h23, -, -, hpp3, hlo, hhi⟩ := htS
    have hpe : prod3 t = q.1 * q.2 * t.2.2 := by rw [prod3, ht1, ht2]
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, hpp3, ?_⟩
    · rw [Lcut, max_lt_iff]
      constructor
      · rw [Nat.div_lt_iff_lt_mul hm]
        have hcomm : q.1 * q.2 * t.2.2 = t.2.2 * (q.1 * q.2) := Nat.mul_comm _ _
        omega
      · omega
    · rw [Ufun, Nat.le_div_iff_mul_le hm]
      have hcomm : q.1 * q.2 * t.2.2 = t.2.2 * (q.1 * q.2) := Nat.mul_comm _ _
      omega
    · rwa [hpe] at hC
  · -- InjOn: p₃ determines the fiber element
    intro t₁ h₁ t₂ h₂ heq
    rw [Finset.mem_filter] at h₁ h₂
    have e11 : q.1 = t₁.1 := by rw [← h₁.2.1]
    have e12 : q.2 = t₁.2.1 := by rw [← h₁.2.1]
    have e21 : q.1 = t₂.1 := by rw [← h₂.2.1]
    have e22 : q.2 = t₂.2.1 := by rw [← h₂.2.1]
    refine Prod.ext (by rw [← e11, ← e21]) (Prod.ext (by rw [← e12, ← e22]) heq)
  · -- Surj: each window prime lifts to the triple (q₁, q₂, p)
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hpl, hpu⟩, hpp, hpC⟩ := hp
    rw [Lcut, max_lt_iff] at hpl
    obtain ⟨hpl1, hpl2⟩ := hpl
    rw [Nat.div_lt_iff_lt_mul hm] at hpl1
    rw [Ufun, Nat.le_div_iff_mul_le hm] at hpu
    have hcommp : q.1 * q.2 * p = p * (q.1 * q.2) := Nat.mul_comm _ _
    -- clean-statement facts (the refine slots' types carry unreduced projections,
    -- which `exact` bridges by defeq but `omega` cannot)
    have h4 : q.2 ≤ p := by omega
    have h8 : x / 2 + 2 ≤ q.1 * q.2 * p := by omega
    have h9 : q.1 * q.2 * p ≤ x := by omega
    have hpx : p ≤ x := by
      have hple : p ≤ p * (q.1 * q.2) := Nat.le_mul_of_pos_right p hm
      omega
    refine ⟨(q.1, q.2, p), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [tripleSet, Finset.mem_filter]
      refine ⟨?_, hzq1, hq1y, hyq2, h4, hp1, hp2, hpp, h8, h9⟩
      rw [Finset.mem_product, Finset.mem_product]
      refine ⟨?_, ?_, ?_⟩ <;> rw [Finset.mem_Icc]
      · exact ⟨hq1lo, hq1x⟩
      · exact ⟨hq2lo, hq2x⟩
      · exact ⟨hpp.one_lt.le, hpx⟩
    · exact Prod.mk.eta
    · exact hpC

/-- The unrestricted fiber card identity (filter algebra + the bijection at `C = ⊤`). -/
theorem tripleSet_fiber_card {x z y : ℕ} {q : ℕ × ℕ} (hq : q ∈ pairSet x z y) :
    ((tripleSet x z y).filter (fun t => (t.1, t.2.1) = q)).card = (fiberPrimes x q).card := by
  classical
  calc ((tripleSet x z y).filter (fun t => (t.1, t.2.1) = q)).card
      = ((tripleSet x z y).filter (fun t => (t.1, t.2.1) = q ∧ True)).card := by
        congr 1
        exact Finset.filter_congr (fun t _ => by simp)
    _ = ((Finset.Ioc (Lcut x q) (Ufun x q)).filter (fun p => p.Prime ∧ True)).card :=
        fiber_card_bij hq (fun _ => True)
    _ = (fiberPrimes x q).card := by
        congr 1
        rw [fiberPrimes]
        exact Finset.filter_congr (fun p _ => by simp)

/-- The AP-restricted fiber card identity (filter algebra + the bijection at the class). -/
theorem tripleSetW_fiber_card {Q a x z y : ℕ} {q : ℕ × ℕ} (hq : q ∈ pairSet x z y) :
    ((tripleSetW Q a x z y).filter (fun t => (t.1, t.2.1) = q)).card
      = (fiberPrimesW Q a x q).card := by
  classical
  have h1 : (tripleSetW Q a x z y).filter (fun t => (t.1, t.2.1) = q)
      = (tripleSet x z y).filter
          (fun t => (t.1, t.2.1) = q ∧ prod3 t % Q = (a + 2) % Q) := by
    rw [tripleSetW, Finset.filter_filter]
    exact Finset.filter_congr (fun t _ => by tauto)
  rw [h1]
  exact fiber_card_bij hq (fun v => v % Q = (a + 2) % Q)

/-- **The exact fiber decomposition (unrestricted).**  `tripleSum = Σ_{q ∈ pairSet} #fiber(q)`
— an identity, versus the landed one-directional `card_tripleSet_le_pairSum`. -/
theorem tripleSum_eq_fiberSum (x z y : ℕ) :
    tripleSum x z y = ∑ q ∈ pairSet x z y, ((fiberPrimes x q).card : ℝ) := by
  classical
  have hnat : (tripleSet x z y).card = ∑ q ∈ pairSet x z y, (fiberPrimes x q).card := by
    rw [Finset.card_eq_sum_card_fiberwise (proj_mem_pairSet (x := x) (z := z) (y := y))]
    exact Finset.sum_congr rfl (fun q hq => tripleSet_fiber_card hq)
  rw [tripleSum_eq_card, hnat, Nat.cast_sum]

/-- **The exact fiber decomposition (AP-restricted).**
`tripleSumW = Σ_{q ∈ pairSet} #fiberW(q)`. -/
theorem tripleSumW_eq_fiberSum (Q a x z y : ℕ) :
    tripleSumW Q a x z y = ∑ q ∈ pairSet x z y, ((fiberPrimesW Q a x q).card : ℝ) := by
  classical
  have hproj : ∀ t ∈ tripleSetW Q a x z y, (t.1, t.2.1) ∈ pairSet x z y :=
    fun t ht => proj_mem_pairSet t (Finset.filter_subset _ _ ht)
  have hnat : (tripleSetW Q a x z y).card
      = ∑ q ∈ pairSet x z y, (fiberPrimesW Q a x q).card := by
    rw [Finset.card_eq_sum_card_fiberwise hproj]
    exact Finset.sum_congr rfl (fun q hq => tripleSetW_fiber_card hq)
  rw [tripleSumW_eq_card, hnat, Nat.cast_sum]

/-- The boundary-row card bound for GLU-2W: `|pairSet| ≤ y·√x` (`≈ x^{5/6}` at the operating
point — the `2·|pairSet|` equidistribution boundary term is polynomially small). -/
theorem pairSet_card_le (x z y : ℕ) : (pairSet x z y).card ≤ y * Nat.sqrt x := by
  classical
  rw [pairSet_factor, Finset.card_product]
  have h1 : (S1set x z y).card ≤ y := by
    have hsub : S1set x z y ⊆ Finset.Icc 1 y := by
      intro p hp
      rw [S1set, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨h1p, _⟩, _, hpy, _⟩ := hp
      rw [Finset.mem_Icc]
      omega
    calc (S1set x z y).card ≤ (Finset.Icc 1 y).card := Finset.card_le_card hsub
      _ = y := by rw [Nat.card_Icc]; omega
  have h2 : (S2set x y).card ≤ Nat.sqrt x := by
    have hsub : S2set x y ⊆ Finset.Icc 1 (Nat.sqrt x) := by
      intro p hp
      rw [S2set, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨h1p, _⟩, _, hpx, _⟩ := hp
      rw [Finset.mem_Icc]
      exact ⟨h1p, Nat.le_sqrt.mpr hpx⟩
    calc (S2set x y).card ≤ (Finset.Icc 1 (Nat.sqrt x)).card := Finset.card_le_card hsub
      _ = Nat.sqrt x := by rw [Nat.card_Icc]; omega
  exact Nat.mul_le_mul h1 h2

/-! ## Section 3 — the reduced class: the mod-`Q` inverse and the class transfer -/

/-- Every `m` coprime to `Q > 0` has an inverse mod `Q` that is itself coprime to `Q`. -/
private lemma exists_mod_inverse {m Q : ℕ} (hQ : 0 < Q) (hcop : Nat.Coprime m Q) :
    ∃ u : ℕ, m * u ≡ 1 [MOD Q] ∧ Nat.Coprime u Q := by
  rcases Nat.lt_or_ge Q 2 with hQ2 | hQ2
  · -- Q = 1: everything is congruent; u = 1
    have hQ1 : Q = 1 := by omega
    subst hQ1
    exact ⟨1, Nat.modEq_one, Nat.coprime_one_left 1⟩
  · have hQ1 : 1 < Q := hQ2
    obtain ⟨u, _, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hQ1
    refine ⟨u, ?_, ?_⟩
    · have h0 : m * u % Q = 1 % Q := by rw [hu, Nat.mod_eq_of_lt hQ1]
      exact h0
    · -- gcd(u, Q) divides m·u − Q·⌊m·u/Q⌋ = 1
      have h3 : Q * (m * u / Q) + 1 = m * u := by
        have := Nat.div_add_mod (m * u) Q
        omega
      have h1 : Nat.gcd u Q ∣ m * u := (Nat.gcd_dvd_left u Q).mul_left m
      have h2 : Nat.gcd u Q ∣ Q * (m * u / Q) := (Nat.gcd_dvd_right u Q).mul_right _
      have h5 : m * u - Q * (m * u / Q) = 1 := by omega
      have h6 := Nat.dvd_sub h1 h2
      rw [h5] at h6
      exact Nat.dvd_one.mp h6

/-- **The class transfer.**  With `m·u ≡ 1 (mod Q)`, the product-side class
`m·p ≡ a + 2 (mod Q)` is the reduced `p₃`-class `p ≡ u·(a+2) (mod Q)`. -/
private lemma class_transfer {m Q a u : ℕ} (hmu : m * u ≡ 1 [MOD Q]) (p : ℕ) :
    (m * p) % Q = (a + 2) % Q ↔ p % Q = (u * (a + 2)) % Q := by
  constructor
  · intro h
    have h0 : m * p ≡ a + 2 [MOD Q] := h
    have h1 : u * (m * p) ≡ u * (a + 2) [MOD Q] := Nat.ModEq.mul_left u h0
    have h2 : m * u * p ≡ 1 * p [MOD Q] := Nat.ModEq.mul_right p hmu
    have e1 : u * (m * p) = m * u * p := by ring
    rw [e1] at h1
    rw [one_mul] at h2
    exact (h2.symm.trans h1 : p ≡ u * (a + 2) [MOD Q])
  · intro h
    have h0 : p ≡ u * (a + 2) [MOD Q] := h
    have h1 : m * p ≡ m * (u * (a + 2)) [MOD Q] := Nat.ModEq.mul_left m h0
    have h2 : m * u * (a + 2) ≡ 1 * (a + 2) [MOD Q] := Nat.ModEq.mul_right (a + 2) hmu
    have e1 : m * (u * (a + 2)) = m * u * (a + 2) := by ring
    rw [e1] at h1
    rw [one_mul] at h2
    exact (h1.trans h2 : m * p ≡ a + 2 [MOD Q])

/-! ## Section 4 — the per-fiber SW discrepancy -/

/-- **The per-fiber discrepancy** (the D5 fiber route).  For `q = (p₁, p₂) ∈ pairSet` under
the named AP rows, the fiber's class-count deviates from the `φ(Q)`-share of its prime count
by at most the fixed-modulus SW error at block scale plus the single boundary point:

  `|#fiberW(q) − #fiber(q)/φ(Q)| ≤ K·x/(log Lval)^A · 1/(p₁p₂) + 2`.

Route: `gcd(p₁p₂, Q) = 1` (both primes `≥ z` exceed `Q`'s primes), reduce the class via the
mod-`Q` inverse (`class_transfer`), split `(Lcut, Ufun]` at `min(Ufun, 2·Lcut)` (the leftover
has `≤ 1` point since `Ufun ≤ 2·Lcut + 1`), and price the block by `hSW`
(= `prime_indicator_SW`'s conclusion, threaded so one `(K, N₀)` serves every fiber). -/
private lemma fiberW_discrepancy_le
    {A C K : ℝ} {N₀ : ℕ} (hK : 0 < K) (hA : 0 < A) (hC : 0 < C)
    (hSW : ∀ N M q a : ℕ, N₀ ≤ N → N ≤ M → M ≤ 2 * N →
      0 < q → Nat.Coprime a q → ((q : ℝ) ≤ (Real.log N) ^ C) →
      |(((Finset.Ioc N M).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ)
        - (((Finset.Ioc N M).filter (fun p => p.Prime)).card : ℝ) / (q.totient : ℝ)|
        ≤ K * N / (Real.log N) ^ A)
    {Q a x z y : ℕ} {q : ℕ × ℕ}
    (hQ : 0 < Q) (hQa2 : Nat.Coprime Q (a + 2))
    (hQz : ∀ p : ℕ, p.Prime → p ∣ Q → p < z)
    (hLval3 : 3 ≤ Lval x y) (hN₀ : N₀ ≤ Lval x y)
    (hQrange : (Q : ℝ) ≤ (Real.log (Lval x y)) ^ C)
    (hq : q ∈ pairSet x z y) :
    |((fiberPrimesW Q a x q).card : ℝ)
        - ((fiberPrimes x q).card : ℝ) / (Q.totient : ℝ)|
      ≤ K * (x : ℝ) / (Real.log (Lval x y)) ^ A * (1 / ((q.1 : ℝ) * q.2)) + 2 := by
  classical
  rw [pairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
  obtain ⟨⟨⟨hq1lo, hq1x⟩, hq2lo, hq2x⟩, hzq1, hq1y, hyq2, hq2sq, hp1, hp2⟩ := hq
  have hm : 0 < q.1 * q.2 := Nat.mul_pos hp1.pos hp2.pos
  have hmR : (0 : ℝ) < (q.1 : ℝ) * q.2 := by
    have h1 : (0 : ℝ) < ((q.1 * q.2 : ℕ) : ℝ) := by exact_mod_cast hm
    rwa [Nat.cast_mul] at h1
  -- totient facts
  have hφpos : (0 : ℝ) < (Q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hQ
  have hφ1 : (1 : ℝ) ≤ (Q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hQ
  -- Lval ≤ Lcut (through the landed Lval ≤ Lfun and Lfun ≤ ⌊(⌊x/2⌋+1)/(q₁q₂)⌋)
  have hq2sqrt : q.2 ≤ Nat.sqrt x := Nat.le_sqrt.mpr hq2sq
  have hden_le : 2 * q.1 * q.2 ≤ 2 * y * Nat.sqrt x := by
    calc 2 * q.1 * q.2 = 2 * (q.1 * q.2) := by ring
      _ ≤ 2 * (y * Nat.sqrt x) := Nat.mul_le_mul (le_refl 2) (Nat.mul_le_mul hq1y hq2sqrt)
      _ = 2 * y * Nat.sqrt x := by ring
  have hm2 : 0 < 2 * q.1 * q.2 := Nat.mul_pos (Nat.mul_pos (by norm_num) hp1.pos) hp2.pos
  have hLvalL : Lval x y ≤ Lfun x q := by
    rw [Lval, Lfun]
    refine (Nat.le_div_iff_mul_le hm2).mpr ?_
    calc Lval x y * (2 * q.1 * q.2) ≤ Lval x y * (2 * y * Nat.sqrt x) :=
          Nat.mul_le_mul (le_refl _) hden_le
      _ ≤ x := by rw [Lval]; exact Nat.div_mul_le_self x (2 * y * Nat.sqrt x)
  have hLfunLam : Lfun x q ≤ (x / 2 + 1) / (q.1 * q.2) := by
    have h1 : Lfun x q = x / 2 / (q.1 * q.2) := by
      rw [Lfun, Nat.div_div_eq_div_mul]
      congr 1
      ring
    rw [h1]
    exact Nat.div_le_div_right (by omega)
  have hLvalLcut : Lval x y ≤ Lcut x q := by
    have h3 : (x / 2 + 1) / (q.1 * q.2) ≤ Lcut x q := by
      rw [Lcut]; exact le_max_left _ _
    omega
  have hN₀Lcut : N₀ ≤ Lcut x q := le_trans hN₀ hLvalLcut
  -- log facts
  have hLvalR : (1 : ℝ) < (Lval x y : ℝ) := by exact_mod_cast (by omega : 1 < Lval x y)
  have hlogLval : 0 < Real.log (Lval x y) := Real.log_pos hLvalR
  have hlogmono : Real.log (Lval x y) ≤ Real.log (Lcut x q) := by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < Lval x y))
    exact_mod_cast hLvalLcut
  have hlogLcut : 0 < Real.log (Lcut x q) := lt_of_lt_of_le hlogLval hlogmono
  have hPval : 0 < (Real.log (Lval x y)) ^ A := Real.rpow_pos_of_pos hlogLval A
  have hPcut : 0 < (Real.log (Lcut x q)) ^ A := Real.rpow_pos_of_pos hlogLcut A
  have hPle : (Real.log (Lval x y)) ^ A ≤ (Real.log (Lcut x q)) ^ A :=
    Real.rpow_le_rpow hlogLval.le hlogmono hA.le
  have hQrange' : (Q : ℝ) ≤ (Real.log (Lcut x q)) ^ C :=
    le_trans hQrange (Real.rpow_le_rpow hlogLval.le hlogmono hC.le)
  -- the pair product is coprime to Q (both primes ≥ z exceed Q's primes)
  have hcop1 : Nat.Coprime q.1 Q := (Nat.Prime.coprime_iff_not_dvd hp1).mpr
    (fun hdvd => absurd (hQz q.1 hp1 hdvd) (not_lt.mpr hzq1))
  have hcop2 : Nat.Coprime q.2 Q := (Nat.Prime.coprime_iff_not_dvd hp2).mpr
    (fun hdvd => absurd (hQz q.2 hp2 hdvd) (not_lt.mpr (by omega)))
  have hcopm : Nat.Coprime (q.1 * q.2) Q := Nat.Coprime.mul_left hcop1 hcop2
  -- the inverse and the reduced class
  obtain ⟨u, hmu, hucop⟩ := exists_mod_inverse hQ hcopm
  have hccop : Nat.Coprime (u * (a + 2)) Q := Nat.Coprime.mul_left hucop hQa2.symm
  -- rewrite the W fiber to the SW class shape
  have hWrw : fiberPrimesW Q a x q
      = (Finset.Ioc (Lcut x q) (Ufun x q)).filter
          (fun p => p.Prime ∧ p % Q = (u * (a + 2)) % Q) := by
    rw [fiberPrimesW]
    exact Finset.filter_congr (fun p _ =>
      and_congr_right (fun _ => class_transfer hmu p))
  by_cases hUL0 : Ufun x q ≤ Lcut x q
  · -- the empty fiber (the sharp-cutoff-violating pairs): discrepancy 0
    have hempty : Finset.Ioc (Lcut x q) (Ufun x q) = ∅ :=
      Finset.Ioc_eq_empty (not_lt.mpr hUL0)
    have h1 : fiberPrimesW Q a x q = ∅ := by
      rw [fiberPrimesW, hempty, Finset.filter_empty]
    have h2 : fiberPrimes x q = ∅ := by
      rw [fiberPrimes, hempty, Finset.filter_empty]
    rw [h1, h2]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div, sub_zero, abs_zero]
    have hterm : 0 ≤ K * (x : ℝ) / (Real.log (Lval x y)) ^ A * (1 / ((q.1 : ℝ) * q.2)) := by
      apply mul_nonneg (div_nonneg (mul_nonneg hK.le (Nat.cast_nonneg x)) hPval.le)
      positivity
    linarith
  · -- the live fiber: split at min(Ufun, 2·Lcut) and price the block by SW
    have hUL : Lcut x q < Ufun x q := not_le.mp hUL0
    -- `Ufun ≤ 2·Lcut + 1`
    have hU2L : Ufun x q ≤ 2 * Lcut x q + 1 := by
      have hΛm : x / 2 + 1 < ((x / 2 + 1) / (q.1 * q.2) + 1) * (q.1 * q.2) :=
        (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self _)
      have hUm : Ufun x q * (q.1 * q.2) ≤ x := by
        rw [Ufun]; exact Nat.div_mul_le_self x (q.1 * q.2)
      have hcancel : Ufun x q < 2 * ((x / 2 + 1) / (q.1 * q.2)) + 2 := by
        by_contra hcon
        rw [not_lt] at hcon
        have hmul : (2 * ((x / 2 + 1) / (q.1 * q.2)) + 2) * (q.1 * q.2)
            ≤ Ufun x q * (q.1 * q.2) := Nat.mul_le_mul_right _ hcon
        have hexp : (2 * ((x / 2 + 1) / (q.1 * q.2)) + 2) * (q.1 * q.2)
            = 2 * (((x / 2 + 1) / (q.1 * q.2) + 1) * (q.1 * q.2)) := by ring
        omega
      have hΛL : (x / 2 + 1) / (q.1 * q.2) ≤ Lcut x q := by
        rw [Lcut]; exact le_max_left _ _
      omega
    set M := min (Ufun x q) (2 * Lcut x q) with hM_def
    have hLM : Lcut x q ≤ M := le_min hUL.le (by omega)
    have hM2L : M ≤ 2 * Lcut x q := min_le_right _ _
    have hMU : M ≤ Ufun x q := min_le_left _ _
    -- the SW block bound at the reduced class
    have hdisc := hSW (Lcut x q) M Q (u * (a + 2)) hN₀Lcut hLM hM2L hQ hccop hQrange'
    -- split the two counts at M
    have hsplit : ∀ (pr : ℕ → Prop) [DecidablePred pr],
        ((Finset.Ioc (Lcut x q) (Ufun x q)).filter pr).card
          = ((Finset.Ioc (Lcut x q) M).filter pr).card
            + ((Finset.Ioc M (Ufun x q)).filter pr).card := by
      intro pr _
      rw [← Finset.Ioc_union_Ioc_eq_Ioc hLM hMU, Finset.filter_union,
        Finset.card_union_of_disjoint]
      exact Finset.disjoint_filter_filter (by
        simp only [Finset.disjoint_left, Finset.mem_Ioc]
        intro n hn hn2
        omega)
    have hsplitW := hsplit (fun p => p.Prime ∧ p % Q = (u * (a + 2)) % Q)
    have hsplitT := hsplit (fun p => p.Prime)
    -- tail cards ≤ 1
    have htail : (Finset.Ioc M (Ufun x q)).card ≤ 1 := by
      rw [Nat.card_Ioc]
      omega
    have hW2n : ((Finset.Ioc M (Ufun x q)).filter
        (fun p => p.Prime ∧ p % Q = (u * (a + 2)) % Q)).card ≤ 1 :=
      le_trans (Finset.card_filter_le _ _) htail
    have hT2n : ((Finset.Ioc M (Ufun x q)).filter (fun p => p.Prime)).card ≤ 1 :=
      le_trans (Finset.card_filter_le _ _) htail
    -- cast to ℝ and assemble
    set W₁ : ℝ := (((Finset.Ioc (Lcut x q) M).filter
      (fun p => p.Prime ∧ p % Q = (u * (a + 2)) % Q)).card : ℝ) with hW₁def
    set T₁ : ℝ := (((Finset.Ioc (Lcut x q) M).filter (fun p => p.Prime)).card : ℝ) with hT₁def
    set W₂ : ℝ := (((Finset.Ioc M (Ufun x q)).filter
      (fun p => p.Prime ∧ p % Q = (u * (a + 2)) % Q)).card : ℝ) with hW₂def
    set T₂ : ℝ := (((Finset.Ioc M (Ufun x q)).filter (fun p => p.Prime)).card : ℝ) with hT₂def
    have hWsum : ((fiberPrimesW Q a x q).card : ℝ) = W₁ + W₂ := by
      rw [hWrw, hW₁def, hW₂def]
      exact_mod_cast hsplitW
    have hTsum : ((fiberPrimes x q).card : ℝ) = T₁ + T₂ := by
      rw [fiberPrimes, hT₁def, hT₂def]
      exact_mod_cast hsplitT
    have hW₂le : W₂ ≤ 1 := by rw [hW₂def]; exact_mod_cast hW2n
    have hT₂le : T₂ ≤ 1 := by rw [hT₂def]; exact_mod_cast hT2n
    have hW₂nn : 0 ≤ W₂ := by rw [hW₂def]; positivity
    have hT₂nn : 0 ≤ T₂ := by rw [hT₂def]; positivity
    have hT₂φ_le : T₂ / (Q.totient : ℝ) ≤ 1 := le_trans (div_le_self hT₂nn hφ1) hT₂le
    have hT₂φ_nn : 0 ≤ T₂ / (Q.totient : ℝ) := div_nonneg hT₂nn hφpos.le
    have habs2 : |W₂ - T₂ / (Q.totient : ℝ)| ≤ 1 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    -- the SW error massage: K·Lcut/(log Lcut)^A ≤ K·x/(log Lval)^A · 1/(q₁q₂)
    have hLcutU : (Lcut x q : ℝ) ≤ (x : ℝ) / ((q.1 : ℝ) * q.2) := by
      have h1 : (Lcut x q : ℝ) ≤ (Ufun x q : ℝ) := by exact_mod_cast hUL.le
      refine le_trans h1 ?_
      rw [Ufun]
      refine le_trans Nat.cast_div_le (le_of_eq ?_)
      push_cast
      ring
    have herr : K * (Lcut x q : ℝ) / (Real.log (Lcut x q)) ^ A
        ≤ K * (x : ℝ) / (Real.log (Lval x y)) ^ A * (1 / ((q.1 : ℝ) * q.2)) := by
      have h1 : K * (Lcut x q : ℝ) / (Real.log (Lcut x q)) ^ A
          ≤ K * (Lcut x q : ℝ) / (Real.log (Lval x y)) ^ A :=
        div_le_div_of_nonneg_left (mul_nonneg hK.le (Nat.cast_nonneg _)) hPval hPle
      have h2 : K * (Lcut x q : ℝ) ≤ K * ((x : ℝ) / ((q.1 : ℝ) * q.2)) :=
        mul_le_mul_of_nonneg_left hLcutU hK.le
      have h3 : K * (Lcut x q : ℝ) / (Real.log (Lval x y)) ^ A
          ≤ K * ((x : ℝ) / ((q.1 : ℝ) * q.2)) / (Real.log (Lval x y)) ^ A := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hPval.le)
      have h4 : K * ((x : ℝ) / ((q.1 : ℝ) * q.2)) / (Real.log (Lval x y)) ^ A
          = K * (x : ℝ) / (Real.log (Lval x y)) ^ A * (1 / ((q.1 : ℝ) * q.2)) := by
        field_simp
      linarith [h1, h3, le_of_eq h4]
    -- final triangle
    have hid : ((fiberPrimesW Q a x q).card : ℝ)
          - ((fiberPrimes x q).card : ℝ) / (Q.totient : ℝ)
        = (W₁ - T₁ / (Q.totient : ℝ)) + (W₂ - T₂ / (Q.totient : ℝ)) := by
      rw [hWsum, hTsum]
      ring
    rw [hid]
    calc |(W₁ - T₁ / (Q.totient : ℝ)) + (W₂ - T₂ / (Q.totient : ℝ))|
        ≤ |W₁ - T₁ / (Q.totient : ℝ)| + |W₂ - T₂ / (Q.totient : ℝ)| := abs_add_le _ _
      _ ≤ K * (Lcut x q : ℝ) / (Real.log (Lcut x q)) ^ A + 1 := add_le_add hdisc habs2
      _ ≤ K * (x : ℝ) / (Real.log (Lval x y)) ^ A * (1 / ((q.1 : ℝ) * q.2)) + 2 := by
          linarith [herr]

/-! ## Section 5 — the equidistribution row -/

/-- **The equidistribution row (D5/C6).**  For every saving `A > 0` and range exponent
`C > 0` there are `K > 0` and a threshold `N₀` such that, under the named AP rows
(the GLU-2W ledger in the header),

  `|tripleSumW − tripleSum/φ(Q)| ≤ K·x/(log Lval)^A · Σ_{pairSet} 1/(p₁p₂) + 2·|pairSet|`.

The `(K, N₀)` pair comes from ONE invocation of the landed fixed-modulus SW
(`prime_indicator_SW`), threaded through every `p₃`-fiber (`fiberW_discrepancy_le`);
the fiber decompositions are exact (`tripleSum_eq_fiberSum`, `tripleSumW_eq_fiberSum`). -/
theorem tripleSumW_equidist {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧ ∀ Q a x z y : ℕ,
      0 < Q → Nat.Coprime Q (a + 2) → (∀ p : ℕ, p.Prime → p ∣ Q → p < z) →
      3 ≤ Lval x y → N₀ ≤ Lval x y →
      ((Q : ℝ) ≤ (Real.log (Lval x y)) ^ C) →
      |tripleSumW Q a x z y - tripleSum x z y / (Q.totient : ℝ)|
        ≤ K * (x : ℝ) / (Real.log (Lval x y)) ^ A
            * (∑ q ∈ pairSet x z y, 1 / ((q.1 : ℝ) * q.2))
          + 2 * ((pairSet x z y).card : ℝ) := by
  obtain ⟨K, N₀, hK, hSW⟩ := prime_indicator_SW hA hC
  refine ⟨K, N₀, hK, fun Q a x z y hQ hQa2 hQz hLval3 hN₀ hQrange => ?_⟩
  rw [tripleSumW_eq_fiberSum, tripleSum_eq_fiberSum, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  calc |∑ q ∈ pairSet x z y, (((fiberPrimesW Q a x q).card : ℝ)
          - ((fiberPrimes x q).card : ℝ) / (Q.totient : ℝ))|
      ≤ ∑ q ∈ pairSet x z y, |((fiberPrimesW Q a x q).card : ℝ)
          - ((fiberPrimes x q).card : ℝ) / (Q.totient : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ pairSet x z y,
          (K * (x : ℝ) / (Real.log (Lval x y)) ^ A * (1 / ((q.1 : ℝ) * q.2)) + 2) :=
        Finset.sum_le_sum (fun q hq =>
          fiberW_discrepancy_le hK hA hC hSW hQ hQa2 hQz hLval3 hN₀ hQrange hq)
    _ = K * (x : ℝ) / (Real.log (Lval x y)) ^ A
          * (∑ q ∈ pairSet x z y, 1 / ((q.1 : ℝ) * q.2))
        + 2 * ((pairSet x z y).card : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring

/-- **The Mertens-closed equidistribution row.**  Folding the windowed-Mertens product
(`sum_inv_pairSet_le`, `C₃ = 19`) into the pair reciprocal sum: under the carrier rows
`2 ≤ z ≤ y ≤ √x`, the total error is

  `≤ K·x/(log Lval)^A · M₁·M₂ + 2·|pairSet|`,

with `M₁·M₂ → log(8/3)·log(3/2) ≈ 0.4` at the operating point — the C6-verified
`x/(log x)^{A−2}`-form (`log Lval ≈ (log x)/6`; the `6^A` constant is absorbed at `A = 13`;
`|pairSet| ≤ y·√x` by `pairSet_card_le`). -/
theorem tripleSumW_equidist_mertens {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧ ∀ Q a x z y : ℕ,
      0 < Q → Nat.Coprime Q (a + 2) → (∀ p : ℕ, p.Prime → p ∣ Q → p < z) →
      3 ≤ Lval x y → N₀ ≤ Lval x y →
      ((Q : ℝ) ≤ (Real.log (Lval x y)) ^ C) →
      2 ≤ z → z ≤ y → 1 ≤ y → ((y : ℝ) ≤ Real.sqrt x) →
      |tripleSumW Q a x z y - tripleSum x z y / (Q.totient : ℝ)|
        ≤ K * (x : ℝ) / (Real.log (Lval x y)) ^ A
            * ((Real.log (Real.log (y + 1) / Real.log z) + 19 / Real.log z)
              * (Real.log (Real.log (Real.sqrt x + 1) / Real.log (y + 1))
                  + 19 / Real.log (y + 1)))
          + 2 * ((pairSet x z y).card : ℝ) := by
  obtain ⟨K, N₀, hK, hbase⟩ := tripleSumW_equidist hA hC
  refine ⟨K, N₀, hK, fun Q a x z y hQ hQa2 hQz hLval3 hN₀ hQrange hz2 hzy hy1 hysx => ?_⟩
  have h := hbase Q a x z y hQ hQa2 hQz hLval3 hN₀ hQrange
  have hM := sum_inv_pairSet_le (x := x) hz2 hzy hy1 hysx
  have hlogLval : 0 < Real.log (Lval x y) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Lval x y))
  have hcoef : 0 ≤ K * (x : ℝ) / (Real.log (Lval x y)) ^ A :=
    div_nonneg (mul_nonneg hK.le (Nat.cast_nonneg _))
      (Real.rpow_pos_of_pos hlogLval A).le
  have hmul := mul_le_mul_of_nonneg_left hM hcoef
  linarith [h, hmul]

/-! ## Section 6 — the W count keystone -/

/-- **CNTW — `tripleSum_le_cbar_final_W`, the count keystone at the AP scale.**  The landed
sharp-cutoff count close (`tripleSum_le_cbar_final`: the `c̄/2`-leading bound whose c̄
integrals are ratio-level and AP-invariant per the H2 gate) divided by `φ(Q)`, plus the
equidistribution error — the count input GLU-2W's `hcount` slot consumes at the smooth
scale `totalMass/φ(Q)` (gate correction C3):

  `tripleSumW ≤ [(1 + 3K/L₀)(1 + W₀)·(c̄/2)·(x/log x) + Rem]/φ(Q) + E_SW`,

with `E_SW = Ksw·x/(log Lval)^A·Σ 1/(p₁p₂) + 2·|pairSet|` the named equidistribution error
(row ledger in the header; `Σ 1/(p₁p₂)` Mertens-closes via `sum_inv_pairSet_le`, `|pairSet|`
via `pairSet_card_le`).  The AP rows and the landed keystone rows are stated verbatim;
GLU-2W discharges each at the operating instance. -/
theorem tripleSum_le_cbar_final_W {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ (Ksw : ℝ) (N₀ : ℕ), 0 < Ksw ∧
      ∀ (Q a x zN yN : ℕ) (zR yR : ℝ),
      -- the AP rows (GLU-2W ledger)
      0 < Q → Nat.Coprime Q (a + 2) → (∀ p : ℕ, p.Prime → p ∣ Q → p < zN) →
      3 ≤ Lval x yN → N₀ ≤ Lval x yN →
      ((Q : ℝ) ≤ (Real.log (Lval x yN)) ^ C) →
      -- the landed keystone rows (verbatim `tripleSum_le_cbar_final`)
      1 < (x : ℝ) → 2 ≤ zR → zR ≤ yR →
      Real.log zR = Real.log x / 8 → Real.log yR = Real.log x / 3 →
      (zN : ℝ) ≤ zR → zR ≤ (zN : ℝ) + 1 →
      (yN : ℝ) ≤ yR → yR ≤ (yN : ℝ) + 1 →
      4 ≤ Real.log (Lval x yN) →
      ∃ K : ℝ, 0 ≤ K ∧
        tripleSumW Q a x zN yN
          ≤ ((1 + 3 * K / Real.log (Lval x yN))
                * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)))
                * (cbar / 2) * ((x : ℝ) / Real.log x)
              + ((1 + 3 * K / Real.log (Lval x yN))
                    * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)))
                    * ((x : ℝ) / 2)
                    * ((Ifun (x : ℝ) yR (zN : ℝ) / (zN : ℝ)
                          + Ifun (x : ℝ) yR (yN : ℝ) / (yN : ℝ)
                          + (21 / Real.log zR) * Ifun (x : ℝ) yR zR)
                        + ∑ p₁ ∈ S1set x zN yN, (1 / (p₁ : ℝ))
                            * (hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                                  / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                                + (21 / Real.log yR)
                                    * hbjs (x : ℝ) (p₁ : ℝ)
                                        (Real.sqrt ((x : ℝ) / (p₁ : ℝ)))))
                  + ((pairSet' x zN yN).card : ℝ) / Real.log (Lval x yN)))
            / (Q.totient : ℝ)
          + (Ksw * (x : ℝ) / (Real.log (Lval x yN)) ^ A
              * (∑ q ∈ pairSet x zN yN, 1 / ((q.1 : ℝ) * q.2))
            + 2 * ((pairSet x zN yN).card : ℝ)) := by
  obtain ⟨Ksw, N₀, hKsw, hEq⟩ := tripleSumW_equidist hA hC
  refine ⟨Ksw, N₀, hKsw, fun Q a x zN yN zR yR hQ hQa2 hQz hLval3 hN₀ hQrange
    hx1 hzR2 hzRyR hlogz hlogy hzN_le hzN_ge hyN_le hyN_ge hLval4 => ?_⟩
  obtain ⟨K, hK0, hland⟩ := tripleSum_le_cbar_final (zN := zN) (yN := yN)
    hx1 hzR2 hzRyR hlogz hlogy hzN_le hzN_ge hyN_le hyN_ge hLval4
  refine ⟨K, hK0, ?_⟩
  have hφpos : (0 : ℝ) < (Q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hQ
  have hE := hEq Q a x zN yN hQ hQa2 hQz hLval3 hN₀ hQrange
  -- one side of the equidistribution row
  have hupper : tripleSumW Q a x zN yN
      ≤ tripleSum x zN yN / (Q.totient : ℝ)
        + (Ksw * (x : ℝ) / (Real.log (Lval x yN)) ^ A
            * (∑ q ∈ pairSet x zN yN, 1 / ((q.1 : ℝ) * q.2))
          + 2 * ((pairSet x zN yN).card : ℝ)) := by
    have h1 := le_abs_self (tripleSumW Q a x zN yN
      - tripleSum x zN yN / (Q.totient : ℝ))
    linarith [h1, hE]
  -- the landed keystone, divided by φ(Q)
  have hdiv := mul_le_mul_of_nonneg_right hland (inv_nonneg.mpr hφpos.le)
  rw [← div_eq_mul_inv, ← div_eq_mul_inv] at hdiv
  linarith [hupper, hdiv]

/-! ## Section 7 — the GLU-2W composition (typecheck; values symbolic)

Gate correction C3 fixes the W-instances' `totalMass` convention to the SMOOTH
`(Σ_window Λ)/φ(Q)`.  GlueNormalized's A₃ discharge (`hmA3_normalized`) is carrier-agnostic
— its `hcount` slot takes `log x · T ≤ (cbar + ecount) · totalMass` with `T` and `totalMass`
free reals.  The `example` below typechecks the W-composition: `T := tripleSumW` and
`totalMass := totalMassSmooth / φ(Q)` slot in verbatim, so once GLU-2W derives
`hcountW` from `tripleSum_le_cbar_final_W` + the smooth `lambda_mass_lower/φ(Q)` row
(the same `log x·(c̄/2)(x/log x)/(x/2) = c̄` ratio identity as the landed re-gate — φ(Q)
cancels), the normalized package closes at the AP scale unchanged. -/

/-- Regression (typecheck only): the W count keystone's shape feeds GlueNormalized's
`hcount` slot at the smooth AP scale `totalMass/φ(Q)`; every other slot is untouched. -/
example {x Q a zN yN : ℕ}
    {XW totalMassSmooth Wz Wy Fv slack3 R3 rho ecount mainA3 : ℝ}
    (hXW : 0 < XW) (hXWdef : XW = totalMassSmooth / (Q.totient : ℝ) * Wz)
    (hrawA3 : mainA3
      ≤ Real.log x * (tripleSumW Q a x zN yN * Wy * (Fv + slack3) + R3))
    (hcertA3 : Fv ≤ 243 / 100) (hFslack_nn : 0 ≤ Fv + slack3)
    (hWy : Wy ≤ Wz * rho) (hrho_nn : 0 ≤ rho) (hWz_nn : 0 ≤ Wz)
    (hLTnn : 0 ≤ Real.log x * tripleSumW Q a x zN yN)
    (hcountW : Real.log x * tripleSumW Q a x zN yN
      ≤ (cbar + ecount) * (totalMassSmooth / (Q.totient : ℝ))) :
    mainA3 ≤ XW * (cbar * (3 / 8) * (243 / 100)
        + (((cbar + ecount) * rho * (243 / 100 + slack3) - cbar * (3 / 8) * (243 / 100))
            + Real.log x * R3 / XW)) :=
  hmA3_normalized hXW hXWdef hrawA3 hcertA3 hFslack_nn hWy hrho_nn hWz_nn hLTnn hcountW

end Salt.Chen
