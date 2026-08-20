/-
# E4a's cyclotomic machinery — the algebra the final even-χ route did not consume

Every declaration in this module was proved during the E4a campaign and is a THEOREM ABOUT
THE MATHEMATICS (contrast `Salt.MR.EvenChiControls`, whose contents refute rather than
assert).  What distinguishes them from the rest of `Salt.MR.EvenChi*` is only that the
route that actually closes E4a — the η/Gauss-sum descent in `Salt.MR.EvenChiEta` and
`Salt.MR.EvenChiDescent` — reaches its conclusion without calling them.  They are landed
because they are reusable, not because anything downstream is waiting on them.

**Nothing here is load-bearing for the even-χ chain.**  Deleting this file would not break
a single proof in the corpus; that is the point of recording the fact here rather than
leaving a reader to infer it from the import graph.

## What is in it

* **The associate route** (`e4a_step1_associated` … `e4a_step5_unit_witness`,
  `e4a_prod_associated`) — over any domain with a primitive `n`-th root, `∏ (ζ^a − 1)` over
  a coprime index set is associated to `(ζ − 1)^|S|`, so two such products with equal
  cardinality are associated.  This is the "differ by a unit" leg, uniform in `n`, with no
  prime-power branch.
* **The η layer** (`e4a_eta_associated_of_sum_zero`, `e4a_eta_associated_in_ring`,
  `e4a_eta_eq_quotient`, `e4a_zpow_prod_split`) — the ratified amendment `Σ_a f a = 0`
  turned into unit-ness.  `_in_ring` is the version with content: in a FIELD every nonzero
  element is a unit, so the field statement is vacuous; stated in `𝓞 K` it is a real
  constraint.
* **The ∏ 2 sin = √q bridge** (`e4a_prod_sin_sq_eq_q`, `e4a_prod_sin_eq_sqrt_q`,
  `e4a_step7_pair_product`, `e4a_conj_eq_pair`, `e4a_pair_mul_one`,
  `e4a_prod_one_sub_eq_q`, `e4a_range_pair_split`) — the classical evaluation, reached by
  pairing `a` with `q − a` inside `∏ (1 − ζ^k) = q`.
* **The Galois/fibre layer** (`e4a_galois_fibre_swap`, `e4a_galois_fibre_fix`,
  `e4a_galois_eta_swap`, `e4a_prod_units_index`, `e4a_prod_units_galois`,
  `e4a_term_bridge`, `e4a_zeta_pow_mod`, `e4a_zeta_pow_val_mul`,
  `e4a_map_prod_sub_one`(`_pow`/`_gen`)) — a ring map sending `ζ ↦ ζ^b` fixes the FULL
  units-indexed product but SWAPS the two χ-fibres when `χ(b) = −1`.  That distinction is
  the whole content of the layer.
* **Two small facts** — `e4a_fibres_nonempty` (at `χ ≠ 1` neither fibre is empty, so the
  swap arm is non-degenerate) and `e4a_unit_image_isIntegral_pair` (a unit's image and its
  inverse are both integral).

Ported from the E4a probe custody file at the P1-fill port rule; statements are verbatim.
-/
import Salt.MR.EvenChiEta

namespace Salt.MR

open IsPrimitiveRoot

/-! ### The associate route — steps 1 and 2 over an arbitrary domain -/

section

variable {A : Type*} [CommRing A] [IsDomain A] {ζ : A} {n j : ℕ}

/-- **Step 1 of the associate route** — the ratio `(ζ^a − 1)/(ζ − 1)` is an
associate relation, straight from the landed cyclotomic-units API. -/
theorem e4a_step1_associated (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) :
    Associated (ζ - 1) (ζ ^ j - 1) :=
  hζ.associated_sub_one_pow_sub_one_of_coprime hj

/-- **Step 2** — the explicit unit witnessing it, at `i = 1`. -/
theorem e4a_step2_unit_ratio (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n)
    (hj : j.Coprime n) :
    IsUnit (∑ i ∈ Finset.range j, ζ ^ i) :=
  hζ.geom_sum_isUnit hn hj

end

/-! ### The product form, and equal cardinality ⇒ associated -/

theorem e4a_prod_associated {A : Type*} [CommRing A] [IsDomain A] {ζ : A} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (S : Finset ℕ)
    (hS : ∀ a ∈ S, Nat.Coprime a n) :
    Associated (∏ a ∈ S, (ζ ^ a - 1)) ((ζ - 1) ^ S.card) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      have h1 : Associated (ζ ^ a - 1) (ζ - 1) :=
        (hζ.associated_sub_one_pow_sub_one_of_coprime
          (hS a (Finset.mem_insert_self a S))).symm
      have h2 : Associated (∏ b ∈ S, (ζ ^ b - 1)) ((ζ - 1) ^ S.card) :=
        ih (fun b hb => hS b (Finset.mem_insert_of_mem hb))
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ,
        mul_comm ((ζ - 1) ^ S.card) (ζ - 1)]
      exact h1.mul_mul h2

theorem e4a_step4_equal_card_associated {A : Type*} [CommRing A] [IsDomain A]
    {ζ : A} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (S T : Finset ℕ)
    (hS : ∀ a ∈ S, Nat.Coprime a n) (hT : ∀ a ∈ T, Nat.Coprime a n)
    (hcard : S.card = T.card) :
    Associated (∏ a ∈ S, (ζ ^ a - 1)) (∏ a ∈ T, (ζ ^ a - 1)) := by
  have h1 := e4a_prod_associated hζ S hS
  have h2 := e4a_prod_associated hζ T hT
  rw [hcard] at h1
  exact h1.trans h2.symm

/-- **The explicit unit**, extracted — the form the assembly will actually consume. -/
theorem e4a_step5_unit_witness {A : Type*} [CommRing A] [IsDomain A]
    {ζ : A} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (S T : Finset ℕ)
    (hS : ∀ a ∈ S, Nat.Coprime a n) (hT : ∀ a ∈ T, Nat.Coprime a n)
    (hcard : S.card = T.card) :
    ∃ u : Aˣ, (∏ a ∈ S, (ζ ^ a - 1)) * u = ∏ a ∈ T, (ζ ^ a - 1) :=
  e4a_step4_equal_card_associated hζ S T hS hT hcard

/-! ### The pairing `a ↔ q − a` on the concrete root of unity -/

section

variable {q a : ℕ}

/-- **The pairing is inverse**: `ζ^(q−a) = (ζ^a)⁻¹`, stated multiplicatively. -/
theorem e4a_pair_mul_one (hq : 0 < q) (haq : a ≤ q) :
    (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ (q - a)
      * (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ a = 1 := by
  rw [← pow_add, Nat.sub_add_cancel haq]
  exact e4a_zeta_pow_q hq

/-- **The conjugate is the partner**: `conj (ζ^a) = ζ^(q−a)`, by cancelling against `ζ^a`. -/
theorem e4a_conj_eq_pair (hq : 0 < q) (haq : a ≤ q) :
    (starRingEnd ℂ) ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ a)
      = (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ (q - a) := by
  set ζ : ℂ := Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I) with hζdef
  have hne : ζ ^ a ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hnorm : ‖ζ‖ = 1 := by
    rw [hζdef, Complex.norm_exp, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
      Real.exp_zero]
  have hconj : (starRingEnd ℂ) (ζ ^ a) * ζ ^ a = 1 := by
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, norm_pow, hnorm]
    norm_num
  have hpair : ζ ^ (q - a) * ζ ^ a = 1 := e4a_pair_mul_one hq haq
  exact mul_right_cancel₀ hne (hconj.trans hpair.symm)

end

theorem e4a_step7_pair_product {q a : ℕ} (ha : 0 < a) (haq : a < q) :
    (1 - (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ a)
      * (1 - (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ (q - a))
      = (((2 * Real.sin (Real.pi * ((a : ℝ) / q))) ^ 2 : ℝ) : ℂ) := by
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le a) haq
  have hconj := e4a_conj_eq_pair (q := q) (a := a) hq haq.le
  rw [← hconj]
  have hsub : (1 : ℂ) - (starRingEnd ℂ)
      ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ a)
      = (starRingEnd ℂ) (1 - (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ a) := by
    rw [map_sub, map_one]
  rw [hsub, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    e4a_step3_sin_bridge ha haq]

/-- **THE PAYOFF OF THE LINK** — the associate/ratio assembly, now at the CONCRETE ζ the
real statement uses.  Probe 2 instantiated where it is actually needed. -/
theorem e4a_prod_associated_concrete {q : ℕ} (hq : 0 < q) (S : Finset ℕ)
    (hS : ∀ a ∈ S, Nat.Coprime a q) :
    Associated
      (∏ a ∈ S, ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ a - 1))
      ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I) - 1) ^ S.card) :=
  e4a_prod_associated (e4a_zeta_isPrimitiveRoot hq) S hS

theorem e4a_prod_one_sub_eq_q {q : ℕ} (hq : 0 < q) :
    ∏ k ∈ Finset.range (q - 1),
        (1 - (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ (k + 1))
      = (q : ℂ) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq).symm⟩
  have h := (e4a_zeta_isPrimitiveRoot (q := n + 1) (Nat.succ_pos n)).prod_one_sub_pow_eq_order
  simpa using h

theorem e4a_range_pair_split {M : Type*} [CommMonoid M] (g : ℕ → M) (m : ℕ) :
    ∏ k ∈ Finset.range (2 * m), g k
      = ∏ k ∈ Finset.range m, (g k * g (2 * m - 1 - k)) := by
  rw [Finset.prod_mul_distrib, two_mul, Finset.prod_range_add]
  congr 1
  rw [← Finset.prod_range_reflect (fun i => g (m + i)) m]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' : j < m := Finset.mem_range.mp hj
  congr 1
  omega

/-! ### ⭐ `∏ 2 sin(πa/q) = √q` -/

theorem e4a_prod_sin_sq_eq_q {m : ℕ} :
    ∏ k ∈ Finset.range m,
        ((2 * Real.sin (Real.pi * (((k + 1 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ)))) ^ 2 : ℝ)
      = ((2 * m + 1 : ℕ) : ℝ) := by
  have hq : 0 < 2 * m + 1 := Nat.succ_pos _
  have h9 := e4a_prod_one_sub_eq_q (q := 2 * m + 1) hq
  rw [show 2 * m + 1 - 1 = 2 * m from by omega] at h9
  rw [e4a_range_pair_split
      (fun k => 1 - (Complex.exp (((2 * Real.pi / ((2 * m + 1 : ℕ) : ℝ) : ℝ) : ℂ)
        * Complex.I)) ^ (k + 1)) m] at h9
  have hC : ∏ k ∈ Finset.range m,
      ((((2 * Real.sin (Real.pi * (((k + 1 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ)))) ^ 2 : ℝ)) : ℂ)
      = ((2 * m + 1 : ℕ) : ℂ) := by
    rw [← h9]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k < m := Finset.mem_range.mp hk
    have h7 := e4a_step7_pair_product (q := 2 * m + 1) (a := k + 1)
      (Nat.succ_pos k) (by omega)
    rw [show 2 * m - 1 - k + 1 = 2 * m + 1 - (k + 1) from by omega]
    exact h7.symm
  exact_mod_cast hC

/-- **THE CAMPAIGN FORM** — `∏_{a=1}^{(q−1)/2} 2 sin(πa/q) = √q` at odd `q`.  Each factor
is positive on the range, so the square root is taken cleanly. This is the `√q` in
`2 log φ / √q`. -/
theorem e4a_prod_sin_eq_sqrt_q {m : ℕ} :
    ∏ k ∈ Finset.range m,
        (2 * Real.sin (Real.pi * (((k + 1 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ))))
      = Real.sqrt ((2 * m + 1 : ℕ) : ℝ) := by
  have hnn : 0 ≤ ∏ k ∈ Finset.range m,
      (2 * Real.sin (Real.pi * (((k + 1 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ)))) := by
    refine Finset.prod_nonneg fun k hk => ?_
    have hk' : k < m := Finset.mem_range.mp hk
    have hden : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
    have h0 : 0 ≤ Real.pi * (((k + 1 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) := by positivity
    have h1 : Real.pi * (((k + 1 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ≤ Real.pi := by
      have hle : (((k + 1 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ≤ 1 := by
        rw [div_le_one hden]
        have hn : k + 1 ≤ 2 * m + 1 := by omega
        exact_mod_cast hn
      nlinarith [Real.pi_pos]
    have := Real.sin_nonneg_of_nonneg_of_le_pi h0 h1
    linarith
  have hsq : (∏ k ∈ Finset.range m,
      (2 * Real.sin (Real.pi * (((k + 1 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ))))) ^ 2
      = ((2 * m + 1 : ℕ) : ℝ) := by
    rw [← Finset.prod_pow]
    exact e4a_prod_sin_sq_eq_q
  conv_rhs => rw [← hsq]
  exact (Real.sqrt_sq hnn).symm

/-! ### The η layer — the amendment `Σ f = 0` doing its work -/

/-- ## PROBE 14 — **E4a's UNIT-NESS LEG, ASSEMBLED, WITH THE AMENDMENT AS ITS HYPOTHESIS**

`Σ_a f a = 0` in, "the numerator and denominator of η differ by a unit" out — for any
`{−1,0,1}`-valued exponent function on residues coprime to `n`.  This is the ratified
amendment doing its work in one statement: probe 13 turns the sum condition into equal
cardinalities, probe 4 turns equal cardinalities into an associate relation, and
`Associated` IS "differ by a unit".

No division, no norm, no prime-power branch, uniform in `n`. -/
theorem e4a_eta_associated_of_sum_zero {A : Type*} [CommRing A] [IsDomain A]
    {ζ : A} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (s : Finset ℕ) (f : ℕ → ℤ)
    (hcop : ∀ a ∈ s, Nat.Coprime a n)
    (hf : ∀ a ∈ s, f a = 1 ∨ f a = 0 ∨ f a = -1)
    (hsum : ∑ a ∈ s, f a = 0) :
    Associated (∏ a ∈ s.filter (fun a => f a = 1), (ζ ^ a - 1))
               (∏ a ∈ s.filter (fun a => f a = -1), (ζ ^ a - 1)) :=
  e4a_step4_equal_card_associated hζ _ _
    (fun a ha => hcop a (Finset.mem_filter.mp ha).1)
    (fun a ha => hcop a (Finset.mem_filter.mp ha).1)
    (e4a_card_eq_of_sum_zero s f hf hsum)

theorem e4a_zpow_prod_split {K : Type*} [Field K] (s : Finset ℕ) (g : ℕ → K) (f : ℕ → ℤ)
    (hf : ∀ a ∈ s, f a = 1 ∨ f a = 0 ∨ f a = -1) (hg : ∀ a ∈ s, g a ≠ 0) :
    ∏ a ∈ s, (g a) ^ (f a)
      = (∏ a ∈ s.filter (fun a => f a = 1), g a)
        / (∏ a ∈ s.filter (fun a => f a = -1), g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hfa := hf a (Finset.mem_insert_self a s)
      have hga := hg a (Finset.mem_insert_self a s)
      have hf' : ∀ b ∈ s, f b = 1 ∨ f b = 0 ∨ f b = -1 :=
        fun b hb => hf b (Finset.mem_insert_of_mem hb)
      have hg' : ∀ b ∈ s, g b ≠ 0 := fun b hb => hg b (Finset.mem_insert_of_mem hb)
      have hden : ∏ b ∈ s.filter (fun b => f b = -1), g b ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun b hb => hg' b (Finset.mem_filter.mp hb).1
      rw [Finset.prod_insert ha, ih hf' hg', Finset.filter_insert, Finset.filter_insert]
      rcases hfa with h | h | h
      · rw [if_pos h, if_neg (by omega : ¬ f a = -1), Finset.prod_insert
          (fun hc => ha (Finset.mem_filter.mp hc).1), h]
        field_simp
      · rw [if_neg (by omega : ¬ f a = 1), if_neg (by omega : ¬ f a = -1), h]
        simp
      · rw [if_neg (by omega : ¬ f a = 1), if_pos h, Finset.prod_insert
          (fun hc => ha (Finset.mem_filter.mp hc).1), h]
        field_simp

/-- **η ITSELF, AS A QUOTIENT** — probe 15 instantiated at the real sine factors, whose
positivity on `0 < a < q` supplies the nonvanishing hypothesis.  This is the object E4a's
statement names, written in the form the route consumes. -/
theorem e4a_eta_eq_quotient {q : ℕ} (s : Finset ℕ) (f : ℕ → ℤ)
    (hs : ∀ a ∈ s, 0 < a ∧ a < q)
    (hf : ∀ a ∈ s, f a = 1 ∨ f a = 0 ∨ f a = -1) :
    ∏ a ∈ s, (2 * Real.sin (Real.pi * ((a : ℝ) / (q : ℝ)))) ^ (f a)
      = (∏ a ∈ s.filter (fun a => f a = 1), (2 * Real.sin (Real.pi * ((a : ℝ) / (q : ℝ)))))
        / (∏ a ∈ s.filter (fun a => f a = -1),
            (2 * Real.sin (Real.pi * ((a : ℝ) / (q : ℝ))))) := by
  refine e4a_zpow_prod_split s _ f hf (fun a ha => ?_)
  obtain ⟨ha0, haq⟩ := hs a ha
  have hqR : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := lt_trans ha0 haq
    exact_mod_cast this
  have h0 : 0 < Real.pi * ((a : ℝ) / (q : ℝ)) := by
    have : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
    have : (0 : ℝ) < (a : ℝ) / (q : ℝ) := div_pos this hqR
    positivity
  have h1 : Real.pi * ((a : ℝ) / (q : ℝ)) < Real.pi := by
    have hlt : ((a : ℝ) / (q : ℝ)) < 1 := by
      rw [div_lt_one hqR]; exact_mod_cast haq
    nlinarith [Real.pi_pos]
  have := Real.sin_pos_of_pos_of_lt_pi h0 h1
  positivity

/-- ## ⭐ THE RING/FIELD JOIN, CLOSED — E4a's unit-ness IN `𝓞 K`, where it has content.

The gap named at tick 6: in a FIELD every nonzero element is a unit, so
`e4a_eta_associated_of_sum_zero` said nothing there.  Here the same theorem is stated in
the RING OF INTEGERS of `K = ℚ⟮ζ⟯`, where `Associated` is a real constraint — and the
hypothesis is still exactly the ratified amendment `Σ_a f a = 0`. -/
theorem e4a_eta_associated_in_ring {q : ℕ} [NeZero q] (s : Finset ℕ) (f : ℕ → ℤ)
    (hcop : ∀ a ∈ s, Nat.Coprime a q)
    (hf : ∀ a ∈ s, f a = 1 ∨ f a = 0 ∨ f a = -1)
    (hsum : ∑ a ∈ s, f a = 0) :
    Associated (∏ a ∈ s.filter (fun a => f a = 1), ((e4aZetaO q) ^ a - 1))
               (∏ a ∈ s.filter (fun a => f a = -1), ((e4aZetaO q) ^ a - 1)) :=
  e4a_eta_associated_of_sum_zero e4aZetaO_isPrimitiveRoot s f hcop hf hsum

/-- The same for a `χ`-style weight: multiplicativity of the exponent under the reindex.
For a REAL character `χ(b) = ±1`, so `χ(b)⁻¹ = χ(b)` and the twist is an involution. -/
theorem e4a_real_char_inv {q : ℕ} (χ : DirichletCharacter ℝ q) {b : ZMod q}
    (hreal : χ b = 1 ∨ χ b = -1) : (χ b) * (χ b) = 1 := by
  rcases hreal with h | h <;> rw [h] <;> norm_num

/-! ### Pushing a ring map through `∏ (ζ^a − 1)` -/

theorem e4a_map_prod_sub_one {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (ζ : A) (S : Finset ℕ) :
    f (∏ a ∈ S, (ζ ^ a - 1)) = ∏ a ∈ S, ((f ζ) ^ a - 1) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun a _ => by rw [map_sub, map_pow, map_one]

/-- **Step 2** — with `f ζ = ζ^b` (which is what the Galois action does to a root of unity),
the image is the product over the REINDEXED exponents `a·b`.  Composed with
`e4a_units_reindex`, this is the whole mechanism of `σ_b(η) = η^{χ(b)}`. -/
theorem e4a_map_prod_sub_one_pow {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (ζ : A) (ζ' : B) (b : ℕ) (hf : f ζ = ζ' ^ b) (S : Finset ℕ) :
    f (∏ a ∈ S, (ζ ^ a - 1)) = ∏ a ∈ S, (ζ' ^ (b * a) - 1) := by
  rw [e4a_map_prod_sub_one f ζ S]
  exact Finset.prod_congr rfl fun a _ => by rw [hf, ← pow_mul]

section

variable {A B ι : Type*} [CommRing A] [CommRing B]

/-- `e4a_map_prod_sub_one`, freed from `ℕ`-indexing: any index type, any exponent map. -/
theorem e4a_map_prod_sub_one_gen (f : A →+* B) (ζ : A) (S : Finset ι) (e : ι → ℕ) :
    f (∏ a ∈ S, (ζ ^ (e a) - 1)) = ∏ a ∈ S, ((f ζ) ^ (e a) - 1) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun a _ => by rw [map_sub, map_pow, map_one]

end

/-! ### The units-indexed product and its `ZMod`/`ℕ` exponent bridge -/

section

variable {q : ℕ}

/-- `ζ ^ (n % q) = ζ ^ n` — the `% q` left behind by `ZMod.val_mul`, absorbed by
`ζ ^ q = 1`. -/
theorem e4a_zeta_pow_mod (hq : 0 < q) (n : ℕ) :
    (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ (n % q)
      = (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n q]
  rw [pow_add, pow_mul, e4a_zeta_pow_q hq, one_pow, one_mul]

/-- **THE BRIDGE** — `ζ ^ ((x * y).val) = ζ ^ (x.val * y.val)`, the `ZMod`-product
exponent traded for the `ℕ`-product exponent, modulo `ζ ^ q = 1`. -/
theorem e4a_zeta_pow_val_mul (hq : 0 < q) (x y : ZMod q) :
    (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ ((x * y).val)
      = (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ (x.val * y.val) := by
  rw [ZMod.val_mul, e4a_zeta_pow_mod hq]

/-- **THE DELIVERABLE** — the `(ZMod q)ˣ`-indexed cyclotomic product is invariant
under the translation `a ↦ a * b`.  This is the form a Galois reindex acts on. -/
theorem e4a_prod_units_index [NeZero q] (b : (ZMod q)ˣ) :
    ∏ a : (ZMod q)ˣ,
        ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
          ^ (((a * b : (ZMod q)ˣ) : ZMod q).val) - 1)
      = ∏ a : (ZMod q)ˣ,
        ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
          ^ ((a : ZMod q).val) - 1) :=
  e4a_units_reindex
    (fun a => (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
      ^ ((a : ZMod q).val) - 1) b

/-- **THE FORM THE GALOIS REINDEX ACTUALLY CONSUMES** — the exponent is the `ℕ`
product `b.val * a.val`, which is what `e4a_map_prod_sub_one_pow` hands you after
pushing `σ_b : ζ ↦ ζ ^ b.val` through the product.  The bridge turns it into the
`ZMod` product; the deliverable then reindexes it away.  ⭐ Net: `σ_b` FIXES the
full units-indexed product. -/
theorem e4a_prod_units_galois [NeZero q] (b : (ZMod q)ˣ) :
    ∏ a : (ZMod q)ˣ,
        ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
          ^ ((b : ZMod q).val * (a : ZMod q).val) - 1)
      = ∏ a : (ZMod q)ˣ,
        ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
          ^ ((a : ZMod q).val) - 1) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hstep : ∀ a : (ZMod q)ˣ,
      (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
          ^ ((b : ZMod q).val * (a : ZMod q).val) - 1
        = (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
          ^ (((a * b : (ZMod q)ˣ) : ZMod q).val) - 1 := by
    intro a
    rw [Units.val_mul, e4a_zeta_pow_val_mul hq,
      Nat.mul_comm ((b : ZMod q)).val ((a : ZMod q)).val]
  calc ∏ a : (ZMod q)ˣ,
        ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
          ^ ((b : ZMod q).val * (a : ZMod q).val) - 1)
      = ∏ a : (ZMod q)ˣ,
        ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
          ^ (((a * b : (ZMod q)ˣ) : ZMod q).val) - 1) :=
        Finset.prod_congr rfl (fun a _ => hstep a)
    _ = _ := e4a_prod_units_index b

end

/-! ### ⭐ The two arms: `σ_b` FIXES the full product but SWAPS the χ-fibres -/

section

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- The bridge as a per-term rewrite, pulled out of the executor's inline `hstep`.
`omit [NeZero q]`: this step needs only `0 < q`, an explicit hypothesis — the instance is
carried by the section for the two theorems below, not by this one. -/
theorem e4a_term_bridge (hq : 0 < q) (b a : (ZMod q)ˣ) :
    (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
        ^ ((b : ZMod q).val * (a : ZMod q).val) - 1
      = (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
        ^ (((a * b : (ZMod q)ˣ) : ZMod q).val) - 1 := by
  rw [Units.val_mul, e4a_zeta_pow_val_mul hq,
    Nat.mul_comm ((b : ZMod q)).val ((a : ZMod q)).val]

-- The `[DecidableEq (ZMod q)ˣ]` binder on the next three is INERT — it is not used in the
-- type, and the linter is right about that. It is retained because these are VERBATIM ports
-- and dropping a binder is a statement change; the suppression is scoped to the declaration
-- so the linter stays armed for everything else in this file.
set_option linter.unusedDecidableInType false in
/-- ⭐ **KC4, ASSEMBLED (the swap arm)** — at `χ(b) = −1` the Galois-twisted product over
the `χ = +1` fibre IS the untwisted product over the `χ = −1` fibre. -/
theorem e4a_galois_fibre_swap [DecidableEq (ZMod q)ˣ] (χ : (ZMod q)ˣ → ℤ)
    (hmul : ∀ x y, χ (x * y) = χ x * χ y) (hone : χ 1 = 1)
    (b : (ZMod q)ˣ) (hb : χ b = -1) :
    ∏ a ∈ Finset.univ.filter (fun a => χ a = 1),
        ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
          ^ ((b : ZMod q).val * (a : ZMod q).val) - 1)
      = ∏ a ∈ Finset.univ.filter (fun a => χ a = -1),
        ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
          ^ ((a : ZMod q).val) - 1) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [Finset.prod_congr rfl (fun a _ => e4a_term_bridge hq b a)]
  exact e4a_prod_fibre_swap χ hmul hone b hb
    (fun a => (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
      ^ ((a : ZMod q).val) - 1)

set_option linter.unusedDecidableInType false in
/-- ⭐ **KC4, ASSEMBLED (the fix arm)** — at `χ(b) = +1` the fibre is preserved. Both arms,
different conclusions, and the difference IS the exponent `χ(b)`. -/
theorem e4a_galois_fibre_fix [DecidableEq (ZMod q)ˣ] (χ : (ZMod q)ˣ → ℤ)
    (hmul : ∀ x y, χ (x * y) = χ x * χ y) (hone : χ 1 = 1)
    (b : (ZMod q)ˣ) (hb : χ b = 1) :
    ∏ a ∈ Finset.univ.filter (fun a => χ a = 1),
        ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
          ^ ((b : ZMod q).val * (a : ZMod q).val) - 1)
      = ∏ a ∈ Finset.univ.filter (fun a => χ a = 1),
        ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
          ^ ((a : ZMod q).val) - 1) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [Finset.prod_congr rfl (fun a _ => e4a_term_bridge hq b a)]
  exact e4a_prod_fibre_fix χ hmul hone b hb
    (fun a => (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
      ^ ((a : ZMod q).val) - 1)

end

set_option linter.unusedDecidableInType false in
/-- ⭐ **THE CONNECTOR** — a ring map sending `ζ ↦ ζ^{b.val}` carries the `χ = +1` fibre
product to the `χ = −1` one.  This is the shape `e4a_sigma_to_b` will plug into, and it is
now waiting for it rather than missing. -/
theorem e4a_galois_eta_swap {q : ℕ} [NeZero q] [DecidableEq (ZMod q)ˣ]
    (f : ℂ →+* ℂ) (b : (ZMod q)ˣ)
    (hf : f (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
        = (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ ((b : ZMod q).val))
    (χ : (ZMod q)ˣ → ℤ) (hmul : ∀ x y, χ (x * y) = χ x * χ y) (hone : χ 1 = 1)
    (hb : χ b = -1) :
    f (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => χ a = 1),
        ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ ((a : ZMod q).val) - 1))
      = ∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => χ a = -1),
        ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ ((a : ZMod q).val) - 1) := by
  rw [e4a_map_prod_sub_one_gen f _ _ (fun a : (ZMod q)ˣ => (a : ZMod q).val), hf]
  rw [Finset.prod_congr rfl (fun a _ => by rw [← pow_mul] :
    ∀ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => χ a = 1),
      ((Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ ((b : ZMod q).val))
        ^ ((a : ZMod q).val) - 1
      = (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I))
        ^ ((b : ZMod q).val * (a : ZMod q).val) - 1)]
  exact e4a_galois_fibre_swap χ hmul hone b hb

/-! ### Two small facts the layer wants nearby -/

theorem e4a_fibres_nonempty {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) :
    0 < (Finset.univ.filter
          (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = 1)).card
      ∧ 0 < (Finset.univ.filter
          (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = -1)).card := by
  have hpos : 0 < (Finset.univ.filter
      (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = 1)).card :=
    Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr
      ⟨Finset.mem_univ 1, E4aChiBridge.e4a_signOf_one χ⟩⟩
  refine ⟨hpos, ?_⟩
  rw [← e4a_dirichlet_card_eq χ (e4a_signOf_sum_eq_zero χ hχ)]
  exact hpos

/-- And the payoff: a value that IS the image of a unit has itself and its inverse integral. -/
theorem e4a_unit_image_isIntegral_pair {K : Type*} [Field K] [NumberField K]
    (u : (NumberField.RingOfIntegers K)ˣ) :
    IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K (u : NumberField.RingOfIntegers K))
    ∧ IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K
        ((u⁻¹ : (NumberField.RingOfIntegers K)ˣ) : NumberField.RingOfIntegers K)) :=
  ⟨NumberField.RingOfIntegers.isIntegral_coe _, NumberField.RingOfIntegers.isIntegral_coe _⟩

end Salt.MR
