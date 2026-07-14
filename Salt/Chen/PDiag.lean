/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SwitchW2
import Salt.Chen.HeadlineW

/-!
# PDIAG — the honest diagonal close fills the abstract `Plo` slot (catch #68 repair (b))

Design: `docs/blueprints/flags.md`, the `2026-07-14 GLU-2W attempt 1 → ★ CATCH #68` entry
(the RATIFIED repair (b)) + `Salt/Chen/HeadlineW.lean` (the kernel-checked infeasibility
certificate this node routes around) + `Salt/Chen/BandSplit.lean` item 3 (the ratified
numeric plan for the diagonal).

`hBlockW_of_window_prices` (SwitchW2, Part D) carries an ABSTRACT band budget `Plo` — that
landed statement is NOT infeasible.  Only the composed `hBVblocksW_discharge` instantiated
it through `PloW_discharge`, whose diagonal aggregation `½·τ(Ps)·Σ_k y·(pieceM k − pieceN k)`
is the row `catch68_hSum_hNum_infeasible` kills (`> x/4` against the `x/L^{10}` budget, for
EVERY operating point).  This file lands the honest three-ingredient diagonal close and
re-emits the composition:

* **Ingredient (i) — the global diagonal support** (`diagPairSet`,
  `sum_diagTotal_le_diagPairSet`, `diagPairSet_card_le`): a diagonal triple is `(p₁, p, p)`
  with `p₁ ≤ y` and `p² ≤ p₁p² ≤ x ⟹ p ≤ √x`, so the piece-summed class-free diagonal
  count is `≤ y·√x` GLOBALLY (vs the crude `Σ_k y·2^k ≈ 2xy`).  At `y = ⌊x^{1/3}⌋` this is
  the `x^{5/6}`-scale cutoff (BandSplit item 3's `p₁·p₂²` structure, honestly aggregated).
* **Ingredient (ii) — the `w'`-rough divisor crumb** (`rough_divisor_crumb`,
  `dvd_sub_two_of_resW`): per FIXED window point, the residue condition at modulus `Q·d`
  forces `d ∣ prod − 2` (the CRT class is `≡ 2 (mod d)`), and a squarefree `w'`-rough
  number `≤ x` has at most `2^{Nat.log w' x}` divisors — NOT `τ(Ps)`.  The exponent
  `Nat.log w' x` is the NAMED quantity GLU-2W bounds at the tower
  (`2^{log x/log w'} = x^{log 2/log w'} = x^{o(1)}` at `log w' ≈ w₀`).
* **Ingredient (iii) — the ν-weighted unit side** (`nuChen_sum_divisors_eq`,
  `nuChen_sum_divisors_le`): `Σ_{d ∣ Ps} ν(d) = Π_{p ∣ Ps}(1 + 1/(p−1))
  ≤ Π_{p ∣ Ps}(1 − ν(p))⁻¹ ≤ (1+ε)·log yR/log u` via the landed `Hyp4.vratio_prod_le`
  at the switch sieve (guards `hu3`/`huz`/`hthresh` threaded; at GLU-2W `u = w0R ε`
  discharges `hthresh` by `w0R_threshold`).
* **The keystone** (`diagAggW_le_honest`): the aggregated guarded diagonal-disc double sum
  is `≤ y·√x·(2^{Nat.log w' x} + Σ_{d ∣ Ps} ν(d))` — ONE named GLU-2W row, of scale
  `x^{5/6 + log 2/log w' + o(1)}` at the operating point, `x^{1/6−o(1)}` of room against
  `x/L^{10}`.
* **The honest band close** (`bandDiscW_le_three_pieces_diag`, `PloW_honest`): the landed
  `bandDiscW_eq_three` recombined as `½·sym + low + ½·(honest diagonal)`, the sym/low legs
  consumed VERBATIM from A3W2 (`PloW_sym_of_box_disc`/`PloW_low_of_box_disc` feed the same
  `hSym`/`hLow` shapes).
* **The re-composition** (`hBVblocksW_discharge'` + the `example`): the corrected supplier,
  `#check`-chained character-for-character into `mainA3_of_block_remainders_W`'s
  `hBVblocksW` slot, emitting the exact `hA3` shape.  The diagonal enters `hSum` as the
  named `(1/2)·Pdiag` summand with its own row `hdiag` — NOT the fixed per-piece formula.

## The corrected GLU-2W row ledger (vs the A3W2 module-header ledger)

Rows 1–7 and 9 of the A3W2 ledger (`SwitchW2.lean`) are UNCHANGED (level/divisor/crumb/
`hr`/`hQPs`/`Price`/`PsymK`-`PlowK`/`hCE_W`).  Row 8 (the diagonal) is REPLACED by:

8′. **`hdiag`**: `y·√x·(2^{Nat.log w' x} + Σ_{d ∣ Ps} ν(d)) ≤ Pdiag` — discharged at
    GLU-2W by `nuChen_sum_divisors_le` (at `u = w0R ε`, `yR = y`) + the tower crumb bound;
    plus the two NEW structural hypotheses `2 ≤ w'` and
    `∀ p ∈ Ps.primeFactors, w' ≤ p` (free at the primorial instantiation).

Row 10 (`hSum`/`hNum`) keeps its shape with the diagonal summand `(1/2) * Pdiag`.

## Catch-#68 non-applicability

`catch68_hSum_hNum_infeasible` (HeadlineW.lean) requires its `hSum` row to carry the
VERBATIM summand `(1/2) * ((Nat.divisors Ps).card : ℝ) * Σ_k (y:ℝ)·((pieceM k − pieceN k))`
— a fixed formula `> x/2`.  The `hSum` of `hBVblocksW_discharge'` carries `(1/2) * Pdiag`
instead, with `Pdiag` constrained only from BELOW by the `hdiag` row at the honest
`y·√x·(crumb + Σν)` scale; the certificate's hypothesis shapes cannot be instantiated
against this bundle, and the bundle is satisfiable at the honest operating point
(`x^{5/6+o(1)} ≪ x/L^{10}`).  `hBVblocksW_discharge` stays landed as a true theorem with
infeasible aggregate rows (the `triplePrimeSum_le` status).

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]`).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — ingredient (i): the global diagonal support -/

open Classical in
/-- **`diagSum` as a filtered-product card** (class-generic) — the landed `hD` identity
inside `BandClose.diagSum_le_bandDiagCount`, extracted for reuse. -/
lemma diagSum_eq_card (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (C : ℕ → Prop) :
    diagSum x z y ε₀ j N M C
      = (((bandP1Set x z y ε₀ j ×ˢ bandLargeSet x y N M).filter
          (fun w => cwin x C w.1 w.2 w.2)).card : ℝ) := by
  classical
  unfold diagSum
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p₁ _ => ?_)
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : cwin x C p₁ p p <;> simp [h]

/-- `diagSum` is monotone toward the class-free count: dropping the class only grows the
diagonal count (the window conjuncts of `cwin` are class-independent). -/
lemma diagSum_le_diagSum_true (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (C : ℕ → Prop) :
    diagSum x z y ε₀ j N M C ≤ diagSum x z y ε₀ j N M (fun _ => True) := by
  classical
  unfold diagSum
  refine Finset.sum_le_sum (fun p₁ _ => Finset.sum_le_sum (fun p _ => ?_))
  by_cases h : cwin x C p₁ p p
  · have hwin : cwin x (fun _ => True) p₁ p p := ⟨trivial, h.2.1, h.2.2⟩
    rw [if_pos h, if_pos hwin]
  · rw [if_neg h]
    split_ifs <;> norm_num

open Classical in
/-- **The global diagonal pair support.**  Pairs `(p₁, p)` with `p₁` a block small prime
(`z ≤ p₁ ≤ y`), `p > y` prime, and the product `p₁·p²` in the window `[x/2+2, x]`.  Every
dyadic piece's diagonal count fibres into it (`sum_diagTotal_le_diagPairSet`); its card is
`≤ y·√x` (`diagPairSet_card_le`) — the `√x` cutoff from `p² ≤ p₁p² ≤ x`. -/
noncomputable def diagPairSet (x z y : ℕ) (ε₀ : ℝ) (j : ℕ) : Finset (ℕ × ℕ) :=
  (bandP1Set x z y ε₀ j ×ˢ ((Finset.Icc 1 x).filter (fun p => p.Prime ∧ y < p))).filter
    (fun w => x / 2 + 2 ≤ w.1 * w.2 * w.2 ∧ w.1 * w.2 * w.2 ≤ x)

/-- The piece-`k` large-prime set is the `⌊log₂⌋ = k` fibre of the `y`-rough prime set. -/
lemma bandLargeSet_piece_eq (x y k : ℕ) :
    bandLargeSet x y (pieceN k) (pieceM k)
      = ((Finset.Icc 1 x).filter (fun p => p.Prime ∧ y < p)).filter
          (fun p => Nat.log 2 p = k) := by
  classical
  unfold bandLargeSet
  rw [Finset.filter_filter]
  refine Finset.filter_congr (fun p hp => ?_)
  rw [Finset.mem_Icc] at hp
  constructor
  · rintro ⟨hpr, hmax, hM⟩
    exact ⟨⟨hpr, lt_of_le_of_lt (le_max_left _ _) hmax⟩,
      (log_eq_iff_piece hp.1).mpr ⟨lt_of_le_of_lt (le_max_right _ _) hmax, hM⟩⟩
  · rintro ⟨⟨hpr, hy⟩, hlog⟩
    obtain ⟨hN, hM⟩ := (log_eq_iff_piece hp.1).mp hlog
    exact ⟨hpr, max_lt hy hN, hM⟩

/-- **The piece-summed class-free diagonal count is at most the global support card.**
Each pair `(p₁, p)` lands in AT MOST ONE dyadic piece (`k = ⌊log₂ p⌋`) — this is what the
crude aggregation of catch #68 threw away. -/
theorem sum_diagTotal_le_diagPairSet (x z y : ℕ) (ε₀ : ℝ) (j : ℕ) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1),
        diagSum x z y ε₀ j (pieceN k) (pieceM k) (fun _ => True))
      ≤ ((diagPairSet x z y ε₀ j).card : ℝ) := by
  classical
  unfold diagSum
  rw [Finset.sum_comm]
  have hcard : ((diagPairSet x z y ε₀ j).card : ℝ)
      = ∑ p₁ ∈ bandP1Set x z y ε₀ j,
          ∑ p ∈ (Finset.Icc 1 x).filter (fun p => p.Prime ∧ y < p),
            (if cwin x (fun _ => True) p₁ p p then (1 : ℝ) else 0) := by
    unfold diagPairSet
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    refine Finset.sum_congr rfl (fun p₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
    by_cases h : x / 2 + 2 ≤ p₁ * p * p ∧ p₁ * p * p ≤ x
    · have hwin : cwin x (fun _ => True) p₁ p p := ⟨trivial, h.1, h.2⟩
      rw [if_pos h, if_pos hwin]
      norm_num
    · have hnwin : ¬ cwin x (fun _ => True) p₁ p p := fun hc => h ⟨hc.2.1, hc.2.2⟩
      rw [if_neg h, if_neg hnwin]
      norm_num
  rw [hcard]
  refine Finset.sum_le_sum (fun p₁ _ => ?_)
  calc (∑ k ∈ Finset.range (Nat.log 2 x + 1),
        ∑ p ∈ bandLargeSet x y (pieceN k) (pieceM k),
          (if cwin x (fun _ => True) p₁ p p then (1 : ℝ) else 0))
      = ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          ∑ p ∈ ((Finset.Icc 1 x).filter (fun p => p.Prime ∧ y < p)).filter
              (fun p => Nat.log 2 p = k),
            (if cwin x (fun _ => True) p₁ p p then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [bandLargeSet_piece_eq]
    _ = ∑ p ∈ ((Finset.Icc 1 x).filter (fun p => p.Prime ∧ y < p)).filter
          (fun p => Nat.log 2 p ∈ Finset.range (Nat.log 2 x + 1)),
        (if cwin x (fun _ => True) p₁ p p then (1 : ℝ) else 0) :=
        Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ p ∈ (Finset.Icc 1 x).filter (fun p => p.Prime ∧ y < p),
        (if cwin x (fun _ => True) p₁ p p then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => ?_)
        split_ifs <;> norm_num

/-- **Ingredient (i) — the global diagonal count is `≤ y·√x`.**  A diagonal pair has
`p₁ ≤ y` (small-prime ceiling) and `p·p ≤ p₁·p² ≤ x` so `p ≤ √x`: the support injects into
`Icc 1 y × Icc 1 √x`.  At `y = ⌊x^{1/3}⌋` this is the `x^{5/6}`-scale global cutoff. -/
theorem diagPairSet_card_le (x z y : ℕ) (ε₀ : ℝ) (j : ℕ) :
    ((diagPairSet x z y ε₀ j).card : ℝ) ≤ (y : ℝ) * (Nat.sqrt x : ℝ) := by
  classical
  have hsub : diagPairSet x z y ε₀ j ⊆ Finset.Icc 1 y ×ˢ Finset.Icc 1 (Nat.sqrt x) := by
    intro w hw
    unfold diagPairSet at hw
    rw [Finset.mem_filter, Finset.mem_product] at hw
    obtain ⟨⟨h1, h2⟩, _hwlo, hwhi⟩ := hw
    rw [bandP1Set, Finset.mem_filter, Finset.mem_Icc] at h1
    rw [Finset.mem_filter, Finset.mem_Icc] at h2
    obtain ⟨⟨h1lo, _⟩, _, _, h1y, _⟩ := h1
    obtain ⟨⟨h2lo, _⟩, _, _⟩ := h2
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    have hpp : w.2 * w.2 ≤ x := by
      calc w.2 * w.2 ≤ w.1 * (w.2 * w.2) := Nat.le_mul_of_pos_left _ (by omega)
        _ = w.1 * w.2 * w.2 := by ring
        _ ≤ x := hwhi
    exact ⟨⟨h1lo, h1y⟩, h2lo, Nat.le_sqrt.mpr hpp⟩
  calc ((diagPairSet x z y ε₀ j).card : ℝ)
      ≤ ((Finset.Icc 1 y ×ˢ Finset.Icc 1 (Nat.sqrt x)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (y : ℝ) * (Nat.sqrt x : ℝ) := by
        rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc, Nat.add_sub_cancel,
          Nat.add_sub_cancel]
        push_cast
        ring

/-! ## Part B — ingredient (ii): the `w'`-rough divisor crumb -/

/-- For squarefree `g`, `τ(g) ≤ 2^{ω(g)}`: divisors inject into subsets of the prime
support via `d ↦ d.primeFactors` (recovered by `∏`, squarefreeness). -/
lemma card_divisors_le_two_pow_omega {g : ℕ} (hg : Squarefree g) :
    g.divisors.card ≤ 2 ^ g.primeFactors.card := by
  classical
  have hcard : g.divisors.card ≤ g.primeFactors.powerset.card := by
    apply Finset.card_le_card_of_injOn (fun d => d.primeFactors)
    · intro d hd
      simp only [Finset.mem_coe, Finset.mem_powerset] at hd ⊢
      exact Nat.primeFactors_mono (Nat.mem_divisors.mp hd).1 (Nat.mem_divisors.mp hd).2
    · intro d₁ h₁ d₂ h₂ heq
      rw [Finset.mem_coe] at h₁ h₂
      have hd₁ : Squarefree d₁ := hg.squarefree_of_dvd (Nat.mem_divisors.mp h₁).1
      have hd₂ : Squarefree d₂ := hg.squarefree_of_dvd (Nat.mem_divisors.mp h₂).1
      have heq' : d₁.primeFactors = d₂.primeFactors := heq
      calc d₁ = ∏ p ∈ d₁.primeFactors, p :=
            (Nat.prod_primeFactors_of_squarefree hd₁).symm
        _ = ∏ p ∈ d₂.primeFactors, p := by rw [heq']
        _ = d₂ := Nat.prod_primeFactors_of_squarefree hd₂
  rwa [Finset.card_powerset] at hcard

/-- **Ingredient (ii) — the `w'`-rough divisor crumb.**  With every prime of `Ps` at least
`w' ≥ 2`, any `1 ≤ nn ≤ xb` admits at most `2^{Nat.log w' xb}` divisors of `Ps`: the common
divisors sit under `g = gcd(Ps, nn)`, squarefree and `w'`-rough, so `w'^{ω(g)} ≤ g ≤ xb`
pins `ω(g) ≤ ⌊log_{w'} xb⌋`, and `τ(g) ≤ 2^{ω(g)}` finishes.  This is the replacement for
catch #68's `τ(Ps)` factor; the exponent is the named tower quantity
(`2^{log x/log w'} = x^{log 2/log w'} = x^{o(1)}`). -/
theorem rough_divisor_crumb {Ps w' nn xb : ℕ} (hPs : Squarefree Ps) (hw' : 2 ≤ w')
    (hPw' : ∀ p ∈ Ps.primeFactors, w' ≤ p) (hnn : 1 ≤ nn) (hnx : nn ≤ xb) :
    ((Nat.divisors Ps).filter (fun d => d ∣ nn)).card ≤ 2 ^ Nat.log w' xb := by
  classical
  set g := Nat.gcd Ps nn with hgdef
  have hg0 : g ≠ 0 := by
    intro h
    rw [hgdef, Nat.gcd_eq_zero_iff] at h
    omega
  have hgsf : Squarefree g := hPs.squarefree_of_dvd (Nat.gcd_dvd_left _ _)
  have hsub : (Nat.divisors Ps).filter (fun d => d ∣ nn) ⊆ g.divisors := by
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hd.1.1 hd.2, hg0⟩
  have homega : g.primeFactors.card ≤ Nat.log w' xb := by
    have hpow : w' ^ g.primeFactors.card ≤ g := by
      calc w' ^ g.primeFactors.card = ∏ _p ∈ g.primeFactors, w' :=
            (Finset.prod_const w').symm
        _ ≤ ∏ p ∈ g.primeFactors, p :=
            Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
              (fun p hp => hPw' p (Nat.primeFactors_mono (Nat.gcd_dvd_left _ _)
                hPs.ne_zero hp))
        _ = g := Nat.prod_primeFactors_of_squarefree hgsf
    have hgx : g ≤ xb :=
      le_trans (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) hnx
    exact Nat.le_log_of_pow_le (by omega) (le_trans hpow hgx)
  calc ((Nat.divisors Ps).filter (fun d => d ∣ nn)).card
      ≤ g.divisors.card := Finset.card_le_card hsub
    _ ≤ 2 ^ g.primeFactors.card := card_divisors_le_two_pow_omega hgsf
    _ ≤ 2 ^ Nat.log w' xb := Nat.pow_le_pow_right (by omega) homega

/-- The W residue condition at modulus `Q·d` forces `d ∣ v − 2`: the CRT class is `≡ 2`
mod `d` (`crtClassW_modEq_right`), so the `d`-component of the congruence is the switch
congruence.  The residue-side kernel of the crumb. -/
lemma dvd_sub_two_of_resW {Q d a v : ℕ} (hQd : Nat.Coprime Q d) (h2v : 2 ≤ v)
    (hres : ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d))) :
    d ∣ v - 2 := by
  have h1 : v ≡ crtClassW Q d a [MOD Q * d] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hres
  have h2 : v ≡ 2 [MOD d] :=
    (Nat.ModEq.of_mul_left Q h1).trans (crtClassW_modEq_right a hQd)
  exact (Nat.modEq_iff_dvd' h2v).mp h2.symm

/-! ## Part C — ingredient (iii): the ν-weighted unit side -/

/-- `Σ_{d ∣ Ps} ν(d) = Π_{p ∣ Ps} (1 + ν(p))` — `ν` multiplicative, `Ps` squarefree
(mathlib's `prodPrimeFactors_one_add_of_squarefree` at `nuChen_mult`). -/
theorem nuChen_sum_divisors_eq (Ps : ℕ) (hPs : Squarefree Ps) :
    ∑ d ∈ Nat.divisors Ps, nuChen d = ∏ p ∈ Ps.primeFactors, (1 + nuChen p) :=
  (nuChen_mult.prodPrimeFactors_one_add_of_squarefree hPs).symm

/-- **Ingredient (iii) — the unit side via the landed V-ratio machinery.**
`Σ_{d ∣ Ps} ν(d) ≤ (1+ε)·log yR/log u`: factorwise `1 + 1/(p−1) ≤ (1 − 1/(p−1))⁻¹`, then
`Hyp4.vratio_prod_le` at the switch sieve (whose `nu` IS `nuChen`), threading its guard
rows verbatim (at GLU-2W: `u = w0R ε` with `hthresh := w0R_threshold`, `yR = y`).
`x z y` are carrier parameters only. -/
theorem nuChen_sum_divisors_le (x z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) {u yR ε : ℝ}
    (hε : 0 ≤ ε) (hu3 : 3 ≤ u) (huy : u ≤ yR)
    (hthresh : 19 / Real.log u + 4 / (u - 1) ≤ Real.log (1 + ε))
    (hPlow : ∀ p ∈ Ps.primeFactors, u ≤ (p : ℝ))
    (hPy : ∀ p ∈ Ps.primeFactors, (p : ℝ) < yR) :
    ∑ d ∈ Nat.divisors Ps, nuChen d ≤ (1 + ε) * Real.log yR / Real.log u := by
  rw [nuChen_sum_divisors_eq Ps hPs]
  have hfacts : ∀ p ∈ Ps.primeFactors, 0 < nuChen p ∧ nuChen p < 1 := fun p hp =>
    ⟨nuChen_pos (Nat.prime_of_mem_primeFactors hp),
      nuChen_lt_one (Nat.prime_of_mem_primeFactors hp) (hPodd p hp)⟩
  have hstep1 : ∏ p ∈ Ps.primeFactors, (1 + nuChen p)
      ≤ ∏ p ∈ Ps.primeFactors, (1 - nuChen p)⁻¹ := by
    refine Finset.prod_le_prod (fun p hp => by linarith [(hfacts p hp).1]) (fun p hp => ?_)
    obtain ⟨hpos, hlt⟩ := hfacts p hp
    have h1m : (0 : ℝ) < 1 - nuChen p := by linarith
    rw [inv_eq_one_div, le_div_iff₀ h1m]
    nlinarith [sq_nonneg (nuChen p)]
  have hT : ∀ p ∈ Ps.primeFactors,
      p.Prime ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < yR
        ∧ (switchSieve x z y Ps hPs hPodd).nu p ≤ 1 / ((p : ℝ) - 1) := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, hPlow p hp, hPy p hp, ?_⟩
    rw [switchSieve_nu, nuChen_prime (Nat.prime_of_mem_primeFactors hp)]
  have hvr := vratio_prod_le (switchSieve x z y Ps hPs hPodd) Ps.primeFactors
    hε hu3 huy hthresh hT
  calc ∏ p ∈ Ps.primeFactors, (1 + nuChen p)
      ≤ ∏ p ∈ Ps.primeFactors, (1 - nuChen p)⁻¹ := hstep1
    _ = (∏ p ∈ Ps.primeFactors, (1 - nuChen p))⁻¹ := by
        rw [Finset.prod_inv_distrib]
    _ = (∏ p ∈ Ps.primeFactors, (1 - (switchSieve x z y Ps hPs hPodd).nu p))⁻¹ := by
        rw [switchSieve_nu]
    _ ≤ (1 + ε) * Real.log yR / Real.log u := hvr

/-! ## Part D — the keystone: the honest diagonal aggregate -/

/-- **`diagAggW_le_honest` — the honest aggregated diagonal (the catch-#68 repair row).**
The full guarded diagonal-disc double sum over pieces `k` AND divisors `d` is bounded by

  `y·√x · (2^{Nat.log w' x} + Σ_{d ∣ Ps} ν(d))`

— ingredient (i) caps the support globally (each pair lives in ONE piece), ingredient (ii)
caps the residue side per window point by the `w'`-rough crumb (NOT `τ(Ps)`), and the unit
side aggregates against `Σ ν(d)` (ingredient (iii) prices it downstream).  Compare the
infeasible landed aggregation `½·τ(Ps)·Σ_k y·2^k ≈ τ(Ps)·xy`. -/
theorem diagAggW_le_honest (x z y : ℕ) (ε₀ : ℝ) (Q a Ps w' : ℕ) (bound : ℝ) (j : ℕ)
    (hx : 2 ≤ x) (hQ1 : 1 ≤ Q) (hPs : Squarefree Ps) (hQPs : Nat.Coprime Q Ps)
    (hw' : 2 ≤ w') (hPw' : ∀ p ∈ Ps.primeFactors, w' ≤ p) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandDiagDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
      ≤ (y : ℝ) * (Nat.sqrt x : ℝ)
          * ((2 : ℝ) ^ Nat.log w' x + ∑ d ∈ Nat.divisors Ps, nuChen d) := by
  classical
  set R := Finset.range (Nat.log 2 x + 1) with hRdef
  -- ① per (k, d): |diag disc| ≤ residue count + ν·unit count
  have habs : ∀ k d, |bandDiagDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d|
      ≤ diagSum x z y ε₀ j (pieceN k) (pieceM k)
          (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
        + nuChen (Q * d) * diagSum x z y ε₀ j (pieceN k) (pieceM k)
            (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) := by
    intro k d
    unfold bandDiagDiscW
    have hR0 := diagSum_nonneg x z y ε₀ j (pieceN k) (pieceM k)
      (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
    have hU0 := diagSum_nonneg x z y ε₀ j (pieceN k) (pieceM k)
      (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))
    have hc0 : 0 ≤ nuChen (Q * d) := by rw [nuChen_apply]; positivity
    have hcU : 0 ≤ nuChen (Q * d) * diagSum x z y ε₀ j (pieceN k) (pieceM k)
        (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) := mul_nonneg hc0 hU0
    rw [abs_le]
    constructor
    · linarith
    · linarith
  -- ② split the guarded double sum into the residue leg + the unit leg
  have hsplit : (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandDiagDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
      ≤ (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then
            diagSum x z y ε₀ j (pieceN k) (pieceM k)
              (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
          else 0)
        + (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then
            nuChen (Q * d) * diagSum x z y ε₀ j (pieceN k) (pieceM k)
              (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))
          else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun d _ => ?_)
    by_cases hd : (d : ℝ) < bound
    · simp only [if_pos hd]
      exact habs k d
    · simp only [if_neg hd]
      norm_num
  -- ③ the residue leg: per window point, the crumb (ingredients (i)+(ii))
  have hres : (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          diagSum x z y ε₀ j (pieceN k) (pieceM k)
            (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
        else 0)
      ≤ (2 : ℝ) ^ Nat.log w' x
          * ∑ k ∈ R, diagSum x z y ε₀ j (pieceN k) (pieceM k) (fun _ => True) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    calc (∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then
            diagSum x z y ε₀ j (pieceN k) (pieceM k)
              (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
          else 0)
        = ∑ d ∈ Nat.divisors Ps,
            ∑ w ∈ bandP1Set x z y ε₀ j ×ˢ bandLargeSet x y (pieceN k) (pieceM k),
              (if (d : ℝ) < bound then
                (if cwin x (fun v => ((v : ℕ) : ZMod (Q * d))
                    = ((crtClassW Q d a : ℕ) : ZMod (Q * d))) w.1 w.2 w.2
                  then (1 : ℝ) else 0) else 0) := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          by_cases hd : (d : ℝ) < bound
          · rw [if_pos hd, diagSum_eq_card, ← Finset.sum_boole]
            exact Finset.sum_congr rfl (fun w _ => (if_pos hd).symm)
          · rw [if_neg hd]
            exact (Finset.sum_eq_zero (fun w _ => if_neg hd)).symm
      _ = ∑ w ∈ bandP1Set x z y ε₀ j ×ˢ bandLargeSet x y (pieceN k) (pieceM k),
            ∑ d ∈ Nat.divisors Ps,
              (if (d : ℝ) < bound then
                (if cwin x (fun v => ((v : ℕ) : ZMod (Q * d))
                    = ((crtClassW Q d a : ℕ) : ZMod (Q * d))) w.1 w.2 w.2
                  then (1 : ℝ) else 0) else 0) := Finset.sum_comm
      _ ≤ ∑ w ∈ bandP1Set x z y ε₀ j ×ˢ bandLargeSet x y (pieceN k) (pieceM k),
            (2 : ℝ) ^ Nat.log w' x
              * (if cwin x (fun _ => True) w.1 w.2 w.2 then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum (fun w _ => ?_)
          by_cases hwin : x / 2 + 2 ≤ w.1 * w.2 * w.2 ∧ w.1 * w.2 * w.2 ≤ x
          · -- window holds: each admissible `d` divides `prod − 2`
            have hwinT : cwin x (fun _ => True) w.1 w.2 w.2 := ⟨trivial, hwin.1, hwin.2⟩
            rw [if_pos hwinT, mul_one]
            calc (∑ d ∈ Nat.divisors Ps,
                  (if (d : ℝ) < bound then
                    (if cwin x (fun v => ((v : ℕ) : ZMod (Q * d))
                        = ((crtClassW Q d a : ℕ) : ZMod (Q * d))) w.1 w.2 w.2
                      then (1 : ℝ) else 0) else 0))
                ≤ ∑ d ∈ Nat.divisors Ps,
                    (if d ∣ (w.1 * w.2 * w.2 - 2) then (1 : ℝ) else 0) := by
                  refine Finset.sum_le_sum (fun d hd => ?_)
                  by_cases hg : (d : ℝ) < bound
                  · rw [if_pos hg]
                    by_cases hc : cwin x (fun v => ((v : ℕ) : ZMod (Q * d))
                        = ((crtClassW Q d a : ℕ) : ZMod (Q * d))) w.1 w.2 w.2
                    · rw [if_pos hc]
                      have hQd : Nat.Coprime Q d :=
                        hQPs.coprime_dvd_right (Nat.mem_divisors.mp hd).1
                      have hdvd : d ∣ w.1 * w.2 * w.2 - 2 :=
                        dvd_sub_two_of_resW hQd (by omega) hc.1
                      rw [if_pos hdvd]
                    · rw [if_neg hc]
                      split_ifs <;> norm_num
                  · rw [if_neg hg]
                    split_ifs <;> norm_num
              _ = (((Nat.divisors Ps).filter
                    (fun d => d ∣ (w.1 * w.2 * w.2 - 2))).card : ℝ) :=
                  Finset.sum_boole _ _
              _ ≤ (2 : ℝ) ^ Nat.log w' x := by
                  have hcr := rough_divisor_crumb hPs hw' hPw'
                    (show 1 ≤ w.1 * w.2 * w.2 - 2 by omega)
                    (show w.1 * w.2 * w.2 - 2 ≤ x by omega)
                  calc (((Nat.divisors Ps).filter
                        (fun d => d ∣ (w.1 * w.2 * w.2 - 2))).card : ℝ)
                      ≤ ((2 ^ Nat.log w' x : ℕ) : ℝ) := by exact_mod_cast hcr
                    _ = (2 : ℝ) ^ Nat.log w' x := by push_cast; ring
          · -- window fails: every summand vanishes
            have hz1 : ∀ d ∈ Nat.divisors Ps,
                (if (d : ℝ) < bound then
                  (if cwin x (fun v => ((v : ℕ) : ZMod (Q * d))
                      = ((crtClassW Q d a : ℕ) : ZMod (Q * d))) w.1 w.2 w.2
                    then (1 : ℝ) else 0) else 0) = 0 := by
              intro d _
              by_cases hg : (d : ℝ) < bound
              · have hnc : ¬ cwin x (fun v => ((v : ℕ) : ZMod (Q * d))
                    = ((crtClassW Q d a : ℕ) : ZMod (Q * d))) w.1 w.2 w.2 :=
                  fun hc => hwin ⟨hc.2.1, hc.2.2⟩
                rw [if_pos hg, if_neg hnc]
              · rw [if_neg hg]
            have hncT : ¬ cwin x (fun _ => True) w.1 w.2 w.2 :=
              fun hc => hwin ⟨hc.2.1, hc.2.2⟩
            have hrhs : (if cwin x (fun _ => True) w.1 w.2 w.2 then (1 : ℝ) else 0) = 0 :=
              if_neg hncT
            rw [hrhs, mul_zero]
            exact le_of_eq (Finset.sum_eq_zero hz1)
      _ = (2 : ℝ) ^ Nat.log w' x
            * diagSum x z y ε₀ j (pieceN k) (pieceM k) (fun _ => True) := by
          rw [← Finset.mul_sum, Finset.sum_boole, ← diagSum_eq_card]
  -- ④ the global support bound (ingredient (i))
  have hDGb : (∑ k ∈ R, diagSum x z y ε₀ j (pieceN k) (pieceM k) (fun _ => True))
      ≤ (y : ℝ) * (Nat.sqrt x : ℝ) :=
    le_trans (sum_diagTotal_le_diagPairSet x z y ε₀ j) (diagPairSet_card_le x z y ε₀ j)
  -- ⑤ the unit leg: `ν(Q·d) ≤ ν(d)`, support summed globally
  have hunit : (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          nuChen (Q * d) * diagSum x z y ε₀ j (pieceN k) (pieceM k)
            (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))
        else 0)
      ≤ (∑ d ∈ Nat.divisors Ps, nuChen d) * ((y : ℝ) * (Nat.sqrt x : ℝ)) := by
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_le_sum (fun d hd => ?_)
    have hd1 : 0 < d := Nat.pos_of_mem_divisors hd
    have hν0 : 0 ≤ nuChen (Q * d) := by rw [nuChen_apply]; positivity
    have hνle : nuChen (Q * d) ≤ nuChen d := by
      rw [nuChen_apply, nuChen_apply]
      have hdvd : d.totient ∣ (Q * d).totient :=
        Nat.totient_dvd_of_dvd (dvd_mul_left d Q)
      have hpos : 0 < (Q * d).totient :=
        Nat.totient_pos.mpr (Nat.mul_pos hQ1 hd1)
      have hdpos : (0 : ℝ) < (d.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hd1
      apply one_div_le_one_div_of_le hdpos
      exact_mod_cast Nat.le_of_dvd hpos hdvd
    have hνd0 : 0 ≤ nuChen d := by rw [nuChen_apply]; positivity
    have hU0 : ∀ k ∈ R, 0 ≤ diagSum x z y ε₀ j (pieceN k) (pieceM k)
        (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) := fun k _ =>
      diagSum_nonneg x z y ε₀ j (pieceN k) (pieceM k) _
    have hsumU : (∑ k ∈ R, diagSum x z y ε₀ j (pieceN k) (pieceM k)
          (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))))
        ≤ (y : ℝ) * (Nat.sqrt x : ℝ) :=
      le_trans (Finset.sum_le_sum (fun k _ => diagSum_le_diagSum_true x z y ε₀ j
        (pieceN k) (pieceM k) _)) hDGb
    calc (∑ k ∈ R, if (d : ℝ) < bound then
            nuChen (Q * d) * diagSum x z y ε₀ j (pieceN k) (pieceM k)
              (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) else 0)
        ≤ ∑ k ∈ R, nuChen (Q * d) * diagSum x z y ε₀ j (pieceN k) (pieceM k)
            (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          split_ifs with h
          · exact le_refl _
          · exact mul_nonneg hν0 (hU0 k hk)
      _ = nuChen (Q * d) * ∑ k ∈ R, diagSum x z y ε₀ j (pieceN k) (pieceM k)
            (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) := by rw [Finset.mul_sum]
      _ ≤ nuChen d * ((y : ℝ) * (Nat.sqrt x : ℝ)) := by
          refine mul_le_mul hνle hsumU (Finset.sum_nonneg hU0) hνd0
  -- ⑥ assemble
  have hresDG : (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          diagSum x z y ε₀ j (pieceN k) (pieceM k)
            (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
        else 0)
      ≤ (2 : ℝ) ^ Nat.log w' x * ((y : ℝ) * (Nat.sqrt x : ℝ)) :=
    le_trans hres (mul_le_mul_of_nonneg_left hDGb (by positivity))
  calc (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandDiagDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
      ≤ (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then
            diagSum x z y ε₀ j (pieceN k) (pieceM k)
              (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
          else 0)
        + (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then
            nuChen (Q * d) * diagSum x z y ε₀ j (pieceN k) (pieceM k)
              (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))
          else 0) := hsplit
    _ ≤ (2 : ℝ) ^ Nat.log w' x * ((y : ℝ) * (Nat.sqrt x : ℝ))
        + (∑ d ∈ Nat.divisors Ps, nuChen d) * ((y : ℝ) * (Nat.sqrt x : ℝ)) :=
        add_le_add hresDG hunit
    _ = (y : ℝ) * (Nat.sqrt x : ℝ)
        * ((2 : ℝ) ^ Nat.log w' x + ∑ d ∈ Nat.divisors Ps, nuChen d) := by ring

/-! ## Part E — the honest three-piece band close -/

/-- The per-`(k, d)` triangle KEEPING the diagonal disc: `bandDiscW_le_three_pieces`
stopped before its crude `abs_diagDiscW_le_bandDiagCount` step. -/
theorem bandDiscW_le_three_pieces_diag (x z y : ℕ) (ε₀ : ℝ) (j Q a N M d : ℕ)
    (hz : 1 ≤ z) :
    |blockBoxHonestDiscW x z y ε₀ j Q a N M (min (z * N + 1) (x + 1)) (x + 1) d|
      ≤ (1 / 2) * |bandSymRectDiscW x z y ε₀ j Q a N M d|
        + |bandLowDiscW x z y ε₀ j Q a N M (min (z * N + 1) (x + 1)) (x + 1) d|
        + (1 / 2) * |bandDiagDiscW x z y ε₀ j Q a N M d| := by
  rw [bandDiscW_eq_three x z y ε₀ j Q a N M d hz]
  have h1 := abs_add_le ((1 / 2) * bandSymRectDiscW x z y ε₀ j Q a N M d
    + (1 / 2) * bandDiagDiscW x z y ε₀ j Q a N M d)
    (bandLowDiscW x z y ε₀ j Q a N M (min (z * N + 1) (x + 1)) (x + 1) d)
  have h2 := abs_add_le ((1 / 2) * bandSymRectDiscW x z y ε₀ j Q a N M d)
    ((1 / 2) * bandDiagDiscW x z y ε₀ j Q a N M d)
  rw [abs_mul, abs_mul, show |(1 : ℝ) / 2| = 1 / 2 by norm_num] at h2
  linarith

open Classical in
/-- **`PloW_honest` — the honest three-piece supplier for the ABSTRACT `Plo` slot of
`hBlockW_of_window_prices` (catch #68 repair (b)).**  The sym/low legs consume the
VERBATIM `hSym`/`hLow` shapes of the landed `PloW_discharge` (fed, as in A3W2, by
`PloW_sym_of_box_disc`/`PloW_low_of_box_disc`); the diagonal is priced by the NAMED
`Pdiag` against its honest `y·√x·(crumb + Σν)` row (`diagAggW_le_honest`) — replacing the
infeasible `½·τ(Ps)·Σ_k y·(pieceM k − pieceN k)` aggregation. -/
theorem PloW_honest (x z y : ℕ) (ε₀ : ℝ) (Q a Ps w' : ℕ) (bound : ℝ) (j : ℕ)
    (Psym Plow Pdiag : ℝ)
    (hz : 1 ≤ z) (hx : 2 ≤ x) (hQ1 : 1 ≤ Q) (hPs : Squarefree Ps)
    (hQPs : Nat.Coprime Q Ps) (hw' : 2 ≤ w') (hPw' : ∀ p ∈ Ps.primeFactors, w' ≤ p)
    (hSym : (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandSymRectDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0) ≤ Psym)
    (hLow : (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |bandLowDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
          (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0) ≤ Plow)
    (hDiag : (y : ℝ) * (Nat.sqrt x : ℝ)
        * ((2 : ℝ) ^ Nat.log w' x + ∑ d ∈ Nat.divisors Ps, nuChen d) ≤ Pdiag) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
             (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
      ≤ (1 / 2) * Psym + Plow + (1 / 2) * Pdiag := by
  classical
  set R := Finset.range (Nat.log 2 x + 1) with hR
  have hterm : ∀ (k d : ℕ),
      (if (d : ℝ) < bound then
          |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
             (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
        ≤ (1 / 2) * (if (d : ℝ) < bound then
              |bandSymRectDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
          + (if (d : ℝ) < bound then |bandLowDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
              (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
          + (1 / 2) * (if (d : ℝ) < bound then
              |bandDiagDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0) := by
    intro k d
    by_cases hd : (d : ℝ) < bound
    · simp only [if_pos hd]
      exact bandDiscW_le_three_pieces_diag x z y ε₀ j Q a (pieceN k) (pieceM k) d hz
    · simp only [if_neg hd]; norm_num
  refine le_trans (Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun d _ =>
    hterm k d))) ?_
  have hsplit : ∀ k, (∑ d ∈ Nat.divisors Ps,
        ((1 / 2) * (if (d : ℝ) < bound then
              |bandSymRectDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
          + (if (d : ℝ) < bound then |bandLowDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
              (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
          + (1 / 2) * (if (d : ℝ) < bound then
              |bandDiagDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)))
      = (1 / 2) * (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |bandSymRectDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
        + (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then
            |bandLowDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
              (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
        + (1 / 2) * (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |bandDiagDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0) := by
    intro k
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hsymS : (1 / 2) * (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandSymRectDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
      ≤ (1 / 2) * Psym := mul_le_mul_of_nonneg_left hSym hhalf
  have hdiagS : (1 / 2) * (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandDiagDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
      ≤ (1 / 2) * Pdiag :=
    mul_le_mul_of_nonneg_left
      (le_trans (diagAggW_le_honest x z y ε₀ Q a Ps w' bound j hx hQ1 hPs hQPs hw' hPw')
        hDiag) hhalf
  linarith [hLow]

/-! ## Part F — the re-composition: `hBVblocksW_discharge'`

Catch-#68 non-applicability (the mandated shape check): `catch68_hSum_hNum_infeasible`
(`Salt/Chen/HeadlineW.lean`) requires its `hSum` hypothesis to carry the VERBATIM fixed
summand `(1/2) * ((Nat.divisors Ps).card : ℝ) * ∑_k (y : ℝ) * ((pieceM k − pieceN k : ℕ))`
— that formula alone forces `RHD ≥ x/4`.  The `hSum` below carries `(1/2) * Pdiag` in that
position instead, with `Pdiag` constrained only from BELOW by the honest `hdiag` row
`y·√x·(2^{Nat.log w' x} + Σν) ≤ Pdiag` — the certificate's hypotheses cannot be
instantiated against this bundle, and at the honest operating point the row is
`x^{5/6+o(1)} ≪ x/(log x)^{10}`. -/

open Classical in
/-- **`hBVblocksW_discharge'` — THE CORRECTED COMPOSED SUPPLIER (catch #68 repair (b)).**
Identical to the landed `hBVblocksW_discharge` except the band close routes through
`PloW_honest`: the diagonal enters `hSum` as the NAMED `(1/2)·Pdiag` summand priced by its
own row `hdiag` (GLU-2W row 8′), NOT the infeasible `½·τ(Ps)·Σ_k y·2^k` formula.  The box
legs (`hNum_at_opW`) and the sym/low legs (`PloW_sym_of_box_disc`/`PloW_low_of_box_disc`)
are UNCHANGED from A3W2.  New structural hypotheses: `2 ≤ x` (window nonemptiness for the
crumb), `2 ≤ w'`, and the `w'`-rough support row `hPw'` (free at the primorial
instantiation `Ps = ∏_{p ∈ [w', y)} p`). -/
theorem hBVblocksW_discharge' (x z y : ℕ) (ε₀ : ℝ) (Q a Ps w' : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (hQPs : Nat.Coprime Q Ps) (hQ1 : 1 ≤ Q)
    (QR : ℝ) (Dlev : ℕ) (X K : ℕ)
    (hz : 1 ≤ z) (hx2 : 2 ≤ x) (hxlo : x / 2 + 1 ≤ x) (hxX : x ≤ X)
    (hK : Nat.log 2 X ≤ K)
    (hw'2 : 2 ≤ w') (hPw' : ∀ p ∈ Ps.primeFactors, w' ≤ p)
    (hiX : ∀ k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        2 ^ (i + 1) ≤ X + 1)
    (Price : ℕ → ℕ → ℕ → ℝ)
    (hprice : ∀ j k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                  (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter
                (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                    (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                  (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ Price j k i)
    (PsymK PlowK : ℕ → ℕ → ℝ)
    (hpriceSym : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ PsymK j k)
    (hpriceLow : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ PlowK j k)
    (Pdiag RHD RCE : ℝ)
    (hdiag : (y : ℝ) * (Nat.sqrt x : ℝ)
        * ((2 : ℝ) ^ Nat.log w' x + ∑ d ∈ Nat.divisors Ps, nuChen d) ≤ Pdiag)
    (hSum : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        ((∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
              Price j k i)
          + ((1 / 2) * (∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK j k)
             + (∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK j k)
             + (1 / 2) * Pdiag))) ≤ RHD)
    (hCE : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < QR * Dlev then blockConvErrW x z y ε₀ j Q d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (x : ℝ) / (Real.log x) ^ 10) :
    -- the EXACT `hBVblocksW` hypothesis of `mainA3_of_block_remainders_W`:
    (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        rosserRemainder (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd) (QR * Dlev))
      ≤ (x : ℝ) / (Real.log x) ^ 10 := by
  have hBlock : ∀ j ∈ Finset.range (maxBlock x z ε₀ + 1),
      (∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < QR * Dlev then |blockHonestDiscW x z y ε₀ j Q a d| else 0)
        ≤ (∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
              Price j k i)
          + ((1 / 2) * (∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK j k)
             + (∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK j k)
             + (1 / 2) * Pdiag) := by
    intro j _
    refine hBlockW_of_window_prices x z y ε₀ Q a Ps (QR * Dlev) j
      (fun k => ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        Price j k i) _ ?_ ?_
    · intro k _
      exact hNum_at_opW K Q a Ps (QR * Dlev) (Price j k) hQ1 hz
        (le_trans (min_le_right _ _) (Nat.add_le_add_right hxX 1)) (min_le_left _ _)
        hxlo hK (hiX k) (hprice j k)
    · exact PloW_honest x z y ε₀ Q a Ps w' (QR * Dlev) j _ _ Pdiag hz hx2 hQ1 hPs hQPs
        hw'2 hPw'
        (PloW_sym_of_box_disc Ps (QR * Dlev) (PsymK j) hQ1 hxX hxlo (hpriceSym j))
        (PloW_low_of_box_disc Ps (QR * Dlev) (PlowK j) hQ1 hxX hxlo (hpriceLow j))
        hdiag
  refine hBVblocksW_of_generalBV x z y ε₀ Q a Ps hPs hPodd hQPs QR Dlev ?_ hCE hNum
  exact le_trans (Finset.sum_le_sum hBlock) hSum

/-! ## The composition into `mainA3_of_block_remainders_W` — the required `example`

`hBVblocksW_discharge' → mainA3_of_block_remainders_W` lands character-for-character in
the `hBVblocksW` slot (exactly as A3W2's composition did with the now-superseded
`hBVblocksW_discharge`) and emits the `hA3` shape at the W-carrier.  The surviving
hypotheses are the A3W2 ledger rows with row 8 replaced by `hdiag` + `hw'2`/`hPw'`. -/

section CompositionSanity

/-- **The PDIAG discharge composition.**  Everything below
`mainA3_of_block_remainders_W`'s `hBVblocksW` slot is discharged by
`hBVblocksW_discharge'`; the surviving hypotheses are the NAMED numeric/threshold rows
(the corrected module-header ledger).  The conclusion is the EXACT `hA3`-shape
`chen_of_hypotheses_W` consumes. -/
example (x z y : ℕ) (ε₀ : ℝ) (P Q a w' Ps Dlev : ℕ) (ε K QR : ℝ) (X KX : ℕ)
    (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hx : 2 ≤ x) (hyx2 : y ≤ x / 2)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Q (a + 2)) (hQPs : Nat.Coprime Q Ps) (hQ1 : 1 ≤ Q)
    (hD2 : 2 ≤ Dlev) (hQR : 1 ≤ QR)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (hw'2 : 2 ≤ w') (hPw' : ∀ p ∈ Ps.primeFactors, w' ≤ p)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev)
    (hxX : x ≤ X) (hKX : Nat.log 2 X ≤ KX)
    (hiX : ∀ k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) KX,
        2 ^ (i + 1) ≤ X + 1)
    (Price : ℕ → ℕ → ℕ → ℝ)
    (hprice : ∀ j k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) KX,
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                  (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter
                (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                    (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                  (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ Price j k i)
    (PsymK PlowK : ℕ → ℕ → ℝ)
    (hpriceSym : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ PsymK j k)
    (hpriceLow : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ PlowK j k)
    (Pdiag RHD RCE : ℝ)
    (hdiag : (y : ℝ) * (Nat.sqrt x : ℝ)
        * ((2 : ℝ) ^ Nat.log w' x + ∑ d ∈ Nat.divisors Ps, nuChen d) ≤ Pdiag)
    (hSum : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        ((∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) KX,
              Price j k i)
          + ((1 / 2) * (∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK j k)
             + (∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK j k)
             + (1 / 2) * Pdiag))) ≤ RHD)
    (hCE : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < QR * Dlev then blockConvErrW x z y ε₀ j Q d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (x : ℝ) / (Real.log x) ^ 10) :
    -- the EXACT `hA3`-shape at the W-carrier (the AP-scale main term):
    triplePrimeSumW Q a x P y
      ≤ Real.log x *
          (tripleSum x z y / (Q.totient : ℝ)
              * Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd)
              * (Fchain (maxDepth (switchSieve x z y Ps hPs hPodd)) (logRatio y Dlev)
                + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
            + (x : ℝ) / (Real.log x) ^ 10) := by
  have hxlo : x / 2 + 1 ≤ x := by omega
  refine mainA3_of_block_remainders_W x z y P Q a w' Ps Dlev ε₀ ε K QR hz hε₀ hPs hPodd hPy
    hPlow hx hyx2 hQfull hPfull' hQa2 hD2 hQR hε hw0 hεsmall hKe h4 hStop ?_
  exact hBVblocksW_discharge' x z y ε₀ Q a Ps w' hPs hPodd hQPs hQ1 QR Dlev X KX hz hx
    hxlo hxX hKX hw'2 hPw' hiX Price hprice PsymK PlowK hpriceSym hpriceLow Pdiag RHD RCE
    hdiag hSum hCE hNum

-- ingredient (i) — the global diagonal support
#check @Salt.Chen.diagSum_eq_card
#check @Salt.Chen.diagSum_le_diagSum_true
#check @Salt.Chen.diagPairSet
#check @Salt.Chen.bandLargeSet_piece_eq
#check @Salt.Chen.sum_diagTotal_le_diagPairSet
#check @Salt.Chen.diagPairSet_card_le
-- ingredient (ii) — the w'-rough divisor crumb
#check @Salt.Chen.card_divisors_le_two_pow_omega
#check @Salt.Chen.rough_divisor_crumb
#check @Salt.Chen.dvd_sub_two_of_resW
-- ingredient (iii) — the ν-weighted unit side
#check @Salt.Chen.nuChen_sum_divisors_eq
#check @Salt.Chen.nuChen_sum_divisors_le
-- the keystone + the honest band close + the corrected supplier
#check @Salt.Chen.diagAggW_le_honest
#check @Salt.Chen.bandDiscW_le_three_pieces_diag
#check @Salt.Chen.PloW_honest
#check @Salt.Chen.hBVblocksW_discharge'
-- the landed slots this composes with (verbatim reuse)
#check @Salt.Chen.hBlockW_of_window_prices
#check @Salt.Chen.PloW_sym_of_box_disc
#check @Salt.Chen.PloW_low_of_box_disc
#check @Salt.Chen.hNum_at_opW
#check @Salt.Chen.hBVblocksW_of_generalBV
#check @Salt.Chen.mainA3_of_block_remainders_W
#check @Salt.Chen.vratio_prod_le
#check @Salt.Chen.w0R_threshold
-- the catch-#68 certificate this routes around (shapes verified disjoint, see Part F note)
#check @Salt.Chen.catch68_hSum_hNum_infeasible

end CompositionSanity

end Salt.Chen
