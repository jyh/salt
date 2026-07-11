/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.CollisionYF

/-!
# explicit12 Node C (NC-1) — the S1 collision inner bound for Maynard's weight `yF`

The S1 collision closure needs the per-assignment inner bound `S1InnerBound`
discharged for a GENERAL bounded weight `y` (`|y| ≤ 1`, supported on the box) —
NOT only for a divisor-monotone tensor (`inner_abs_le`'s hypothesis).  The route
here is the design's TERMWISE + contamination-partition + marked-moment proof:

* the termwise absolute bound uses only `|y| ≤ 1` (no monotonicity, no
  domination) — `|term_u| ≤ 1/(∏φ(uᵢ)·Wσ(u)·Wτ(u))`;
* the contamination partition is the landed `inner_abs_le` `hcompl`/`hpart`
  fiberwise skeleton, verbatim except the weight `(∏f₀)²/∏φ ↦ 1/∏φ`;
* the marked moment `box_marked_moment` is the `f₀ ≡ 1` specialization of the
  landed private `erasure_bound` — rebuilt fresh here (it is `private` there),
  the two-slot OR form with a `2^{|Q|}·∏(p−1)⁻¹` contraction that folds into the
  `3^{ω(s)}` binomial at the partition level.

Deliverables:
* `box_marked_moment` — the `k`-dim OR-marked crude moment (`1/∏φ` weight).
* `S1InnerBoundM` — the correction-slotted inner atom (RHS constant `B`, its LHS
  BYTE-IDENTICAL to `S1InnerBound`).
* `s1_inner_bounded` — `yF`'s discharge with `B = M := ∑ 1/∏φ`.
* `collision_lower_orderW_ofM` — the constant-`B` copy of
  `collision_lower_orderW_of`.
* `collision_yF_M` — the corollary at `y = yF`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Twelve

open Salt.Maynard

/-! ## The `f₀ ≡ 1` marked moment engine -/

/-- The crude summand `1/∏φ(uᵢ)` is nonnegative. -/
private theorem box_phiterm_nonneg {k : ℕ} (u : Fin k → ℕ) :
    0 ≤ 1 / ∏ i, (Nat.totient (u i) : ℝ) :=
  div_nonneg zero_le_one (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)

/-- **Single-prime erasure at `f₀ ≡ 1`.** Dividing the forced prime `q₀` out of
coordinate `i₀` contracts the constrained crude moment `∑ 1/∏φ` by EXACTLY
`(q₀−1)⁻¹` (the `1/∏φ` weight has no monotonicity slack), for any
erasure-stable side condition `C`. -/
private theorem box_erase_branch {k R W' : ℕ}
    {q₀ : ℕ} (hq₀ : q₀.Prime) (i₀ : Fin k)
    (C : (Fin k → ℕ) → Prop) [DecidablePred C]
    (hC : ∀ u ∈ kSieveIndex k R W', q₀ ∣ u i₀ → C u →
      C (Function.update u i₀ (u i₀ / q₀))) :
    ∑ u ∈ (kSieveIndex k R W').filter (fun u => q₀ ∣ u i₀ ∧ C u),
        1 / ∏ i, (Nat.totient (u i) : ℝ)
      ≤ ((q₀ : ℝ) - 1)⁻¹
          * ∑ u ∈ (kSieveIndex k R W').filter C,
              1 / ∏ i, (Nat.totient (u i) : ℝ) := by
  classical
  have hq₀R : (1 : ℝ) < (q₀ : ℝ) := by exact_mod_cast hq₀.one_lt
  have hq₀inv : (0 : ℝ) ≤ ((q₀ : ℝ) - 1)⁻¹ := by rw [inv_nonneg]; linarith
  set A := (kSieveIndex k R W').filter (fun u => q₀ ∣ u i₀ ∧ C u) with hA
  have hgdvd : ∀ u : Fin k → ℕ, q₀ ∣ u i₀ →
      ∀ i, Function.update u i₀ (u i₀ / q₀) i ∣ u i := by
    intro u hq i
    rcases eq_or_ne i i₀ with rfl | hne
    · rw [Function.update_self]; exact Nat.div_dvd_of_dvd hq
    · rw [Function.update_of_ne hne]
  have hgmem : ∀ u ∈ A, Function.update u i₀ (u i₀ / q₀)
      ∈ (kSieveIndex k R W').filter C := by
    intro u hu
    rw [hA, Finset.mem_filter] at hu
    obtain ⟨hu𝒟, hq, hCu⟩ := hu
    rw [Finset.mem_filter]
    exact ⟨mem_kSieveIndex_of_dvd hu𝒟 (hgdvd u hq), hC u hu𝒟 hq hCu⟩
  have hterm : ∀ u ∈ A,
      1 / ∏ i, (Nat.totient (u i) : ℝ)
        = ((q₀ : ℝ) - 1)⁻¹
            * (1 / ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ)) := by
    intro u hu
    rw [hA, Finset.mem_filter] at hu
    obtain ⟨hu𝒟, hq, _hCu⟩ := hu
    have hupos : 0 < u i₀ := kSieveIndex_coord_pos hu𝒟 i₀
    have husq : Squarefree (u i₀) := ((mem_kSieveIndex_iff u).mp hu𝒟).1 i₀
    have hsplit : u i₀ = q₀ * (u i₀ / q₀) := (Nat.mul_div_cancel' hq).symm
    have hcop : Nat.Coprime q₀ (u i₀ / q₀) :=
      Nat.coprime_of_squarefree_mul (hsplit ▸ husq)
    have hφeq : (∏ i, (Nat.totient (u i) : ℝ))
        = ((q₀ : ℝ) - 1)
            * ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ) := by
      rw [← Finset.mul_prod_erase Finset.univ
          (fun i => (Nat.totient (u i) : ℝ)) (Finset.mem_univ i₀),
        ← Finset.mul_prod_erase Finset.univ
          (fun i => (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ))
          (Finset.mem_univ i₀)]
      have h1 : (Nat.totient (u i₀) : ℝ)
          = ((q₀ : ℝ) - 1)
              * (Nat.totient (Function.update u i₀ (u i₀ / q₀) i₀) : ℝ) := by
        rw [Function.update_self]
        conv_lhs => rw [hsplit]
        rw [Nat.totient_mul hcop, Nat.totient_prime hq₀, Nat.cast_mul,
          Nat.cast_sub hq₀.one_lt.le, Nat.cast_one]
      have h2 : ∀ i ∈ Finset.univ.erase i₀,
          (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ)
            = (Nat.totient (u i) : ℝ) := by
        intro i hi
        rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
      rw [h1, Finset.prod_congr rfl h2]
      ring
    rw [hφeq]
    simp only [one_div, mul_inv]
  have hginj : ∀ x ∈ A, ∀ y ∈ A,
      Function.update x i₀ (x i₀ / q₀) = Function.update y i₀ (y i₀ / q₀)
        → x = y := by
    intro x hx y hy hxy
    rw [hA, Finset.mem_filter] at hx hy
    funext i
    rcases eq_or_ne i i₀ with hii | hne
    · rw [hii]
      have h3 : x i₀ / q₀ = y i₀ / q₀ := by
        have := congrFun hxy i₀
        rwa [Function.update_self, Function.update_self] at this
      have h1 : x i₀ = q₀ * (x i₀ / q₀) := (Nat.mul_div_cancel' hx.2.1).symm
      have h2 : y i₀ = q₀ * (y i₀ / q₀) := (Nat.mul_div_cancel' hy.2.1).symm
      rw [h1, h3, ← h2]
    · have := congrFun hxy i
      rwa [Function.update_of_ne hne, Function.update_of_ne hne] at this
  calc ∑ u ∈ A, 1 / ∏ i, (Nat.totient (u i) : ℝ)
      = ∑ u ∈ A, ((q₀ : ℝ) - 1)⁻¹
          * (1 / ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ)) :=
        Finset.sum_congr rfl hterm
    _ = ((q₀ : ℝ) - 1)⁻¹
          * ∑ u ∈ A, 1 / ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ) := by
        rw [Finset.mul_sum]
    _ = ((q₀ : ℝ) - 1)⁻¹
          * ∑ v ∈ A.image (fun u => Function.update u i₀ (u i₀ / q₀)),
              1 / ∏ i, (Nat.totient (v i) : ℝ) := by
        have himg : ∑ v ∈ A.image (fun u => Function.update u i₀ (u i₀ / q₀)),
            1 / ∏ i, (Nat.totient (v i) : ℝ)
            = ∑ u ∈ A, 1 / ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ) :=
          Finset.sum_image hginj
        rw [himg]
    _ ≤ ((q₀ : ℝ) - 1)⁻¹
          * ∑ v ∈ (kSieveIndex k R W').filter C,
              1 / ∏ i, (Nat.totient (v i) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hq₀inv
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro v hv
          rw [Finset.mem_image] at hv
          obtain ⟨u, hu, rfl⟩ := hv
          exact hgmem u hu
        · intro v _ _
          exact box_phiterm_nonneg v

/-- **NC-1 deliverable 1 — the `k`-dim `Q`-marked crude moment.** For a finite
set `P` of primes and two slot maps, the crude moment `∑ 1/∏φ` constrained to
"every `q ∈ Q` divides one of its two slots" contracts by
`2^{|Q|}·∏_{q∈Q}(q−1)⁻¹` relative to the unconstrained moment
`M := ∑ 1/∏φ`.  (This is the `f₀ ≡ 1` specialization of the landed private
`erasure_bound`; the `2^{|Q|}` side-choice factor folds into `3^{ω(s)}` in
`s1_inner_bounded`.) -/
theorem box_marked_moment {k R W' : ℕ}
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (sl1 sl2 : {x // x ∈ P} → Fin k) (Q : Finset {x // x ∈ P}) :
    ∑ u ∈ (kSieveIndex k R W').filter
        (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)),
      1 / ∏ i, (Nat.totient (u i) : ℝ)
      ≤ 2 ^ Q.card * (∏ q ∈ Q, (((q : ℕ) : ℝ) - 1)⁻¹)
          * ∑ u ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (u i) : ℝ) := by
  classical
  induction Q using Finset.induction with
  | empty =>
      have hfilter : (kSieveIndex k R W').filter
          (fun u => ∀ q ∈ (∅ : Finset {x // x ∈ P}),
            (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))
          = kSieveIndex k R W' :=
        Finset.filter_true_of_mem (fun u _ => fun q hq =>
          absurd hq (Finset.notMem_empty q))
      rw [hfilter, Finset.card_empty, pow_zero, Finset.prod_empty, one_mul,
        one_mul]
  | insert q₀ Q hq₀Q ih =>
      have hq₀prime : (q₀ : ℕ).Prime := hP _ q₀.2
      have hq₀R : (1 : ℝ) < ((q₀ : ℕ) : ℝ) := by exact_mod_cast hq₀prime.one_lt
      have hq₀inv : (0 : ℝ) ≤ (((q₀ : ℕ) : ℝ) - 1)⁻¹ := by
        rw [inv_nonneg]; linarith
      have hstable : ∀ i₀ : Fin k, ∀ u ∈ kSieveIndex k R W', (q₀ : ℕ) ∣ u i₀ →
          (∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)) →
          (∀ q ∈ Q, (q : ℕ) ∣ (Function.update u i₀ (u i₀ / (q₀ : ℕ))) (sl1 q)
            ∨ (q : ℕ) ∣ (Function.update u i₀ (u i₀ / (q₀ : ℕ))) (sl2 q)) := by
        intro i₀ u _hu hdvd hCu q hq
        have hqne : (q : ℕ) ≠ (q₀ : ℕ) := by
          intro h
          exact hq₀Q (by rwa [Subtype.ext h] at hq)
        have hqprime : (q : ℕ).Prime := hP _ q.2
        have hpres : ∀ j, (q : ℕ) ∣ u j →
            (q : ℕ) ∣ Function.update u i₀ (u i₀ / (q₀ : ℕ)) j := by
          intro j hj
          rcases eq_or_ne j i₀ with hji | hne
          · rw [hji, Function.update_self]
            have hsplit : u i₀ = (q₀ : ℕ) * (u i₀ / (q₀ : ℕ)) :=
              (Nat.mul_div_cancel' hdvd).symm
            have hcop : Nat.Coprime (q : ℕ) (q₀ : ℕ) :=
              (Nat.coprime_primes hqprime hq₀prime).mpr hqne
            have hqm : (q : ℕ) ∣ (q₀ : ℕ) * (u i₀ / (q₀ : ℕ)) := by
              rw [← hsplit, ← hji]
              exact hj
            exact hcop.dvd_of_dvd_mul_left hqm
          · rw [Function.update_of_ne hne]
            exact hj
        rcases hCu q hq with h | h
        · exact Or.inl (hpres _ h)
        · exact Or.inr (hpres _ h)
      have hsub : (kSieveIndex k R W').filter
          (fun u => ∀ q ∈ insert q₀ Q,
            (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))
          ⊆ ((kSieveIndex k R W').filter (fun u => (q₀ : ℕ) ∣ u (sl1 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)))
            ∪ ((kSieveIndex k R W').filter (fun u => (q₀ : ℕ) ∣ u (sl2 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))) := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨hu𝒟, hcondu⟩ := hu
        rw [Finset.forall_mem_insert] at hcondu
        obtain ⟨h0, hQ⟩ := hcondu
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        rcases h0 with h | h
        · exact Or.inl ⟨hu𝒟, h, hQ⟩
        · exact Or.inr ⟨hu𝒟, h, hQ⟩
      have hbr1 := box_erase_branch (R := R) (W' := W') hq₀prime (sl1 q₀)
        (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))
        (hstable (sl1 q₀))
      have hbr2 := box_erase_branch (R := R) (W' := W') hq₀prime (sl2 q₀)
        (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))
        (hstable (sl2 q₀))
      calc ∑ u ∈ (kSieveIndex k R W').filter
            (fun u => ∀ q ∈ insert q₀ Q,
              (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)),
            1 / ∏ i, (Nat.totient (u i) : ℝ)
          ≤ ∑ u ∈ ((kSieveIndex k R W').filter (fun u => (q₀ : ℕ) ∣ u (sl1 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)))
              ∪ ((kSieveIndex k R W').filter (fun u => (q₀ : ℕ) ∣ u (sl2 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))),
              1 / ∏ i, (Nat.totient (u i) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun u _ _ => box_phiterm_nonneg u)
        _ ≤ (∑ u ∈ (kSieveIndex k R W').filter (fun u => (q₀ : ℕ) ∣ u (sl1 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)),
                1 / ∏ i, (Nat.totient (u i) : ℝ))
              + ∑ u ∈ (kSieveIndex k R W').filter (fun u => (q₀ : ℕ) ∣ u (sl2 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)),
                1 / ∏ i, (Nat.totient (u i) : ℝ) := by
            have hui := Finset.sum_union_inter
              (s₁ := (kSieveIndex k R W').filter (fun u => (q₀ : ℕ) ∣ u (sl1 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)))
              (s₂ := (kSieveIndex k R W').filter (fun u => (q₀ : ℕ) ∣ u (sl2 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)))
              (f := fun u => 1 / ∏ i, (Nat.totient (u i) : ℝ))
            have hint : 0 ≤ ∑ u ∈ ((kSieveIndex k R W').filter
                (fun u => (q₀ : ℕ) ∣ u (sl1 q₀)
                  ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)))
                ∩ ((kSieveIndex k R W').filter (fun u => (q₀ : ℕ) ∣ u (sl2 q₀)
                  ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))),
                1 / ∏ i, (Nat.totient (u i) : ℝ) :=
              Finset.sum_nonneg (fun u _ => box_phiterm_nonneg u)
            linarith
        _ ≤ ((((q₀ : ℕ) : ℝ) - 1)⁻¹
              * ∑ u ∈ (kSieveIndex k R W').filter
                  (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)),
                  1 / ∏ i, (Nat.totient (u i) : ℝ))
              + (((q₀ : ℕ) : ℝ) - 1)⁻¹
              * ∑ u ∈ (kSieveIndex k R W').filter
                  (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)),
                  1 / ∏ i, (Nat.totient (u i) : ℝ) :=
            add_le_add hbr1 hbr2
        _ ≤ 2 * ((((q₀ : ℕ) : ℝ) - 1)⁻¹
              * (2 ^ Q.card * (∏ q ∈ Q, (((q : ℕ) : ℝ) - 1)⁻¹)
                  * ∑ u ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (u i) : ℝ))) := by
            have hstep := mul_le_mul_of_nonneg_left ih hq₀inv
            linarith
        _ = 2 ^ (insert q₀ Q).card
              * (∏ q ∈ insert q₀ Q, (((q : ℕ) : ℝ) - 1)⁻¹)
              * ∑ u ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (u i) : ℝ) := by
            rw [Finset.card_insert_of_notMem hq₀Q, Finset.prod_insert hq₀Q,
              pow_succ]
            ring

/-! ## The correction-slotted inner atom and its discharge for `yF` -/

/-- **NC-1 deliverable 2 — the constant-`B` inner atom.** The LHS
`|I(s,α)[y]|` is BYTE-IDENTICAL to `S1InnerBound` (`CollisionQuantW.lean`); the
RHS replaces the weighted moment `∑ (y r)²/∏φ` by a free constant `B`. -/
def S1InnerBoundM (k R W' : ℕ) (y : (Fin k → ℕ) → ℝ) (B : ℝ) : Prop :=
  ∀ {s : ℕ}, Squarefree s →
    ∀ (α : (p : ℕ) → p ∈ s.primeFactors → Fin k × Fin k),
      α ∈ assignments k s →
    |∑ u ∈ kSieveIndex k R W', (∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ))|
      ≤ 3 ^ s.primeFactors.card
          * (∏ p ∈ s.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
          * B

/-- **NC-1 deliverable 3 — the termwise + partition + marked-moment discharge.**
Any bounded weight (`|y| ≤ 1`, supported on the box) satisfies the inner atom at
the CRUDE moment `M := ∑ 1/∏φ`.  No smoothness, no domination: the sign-strip
uses `|y| ≤ 1` termwise, the collision-prime contamination is partitioned by the
landed `hcompl`/fiberwise skeleton, and each fiber is bounded by
`box_marked_moment`. -/
theorem s1_inner_bounded (k R W' : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ r, |y r| ≤ 1) (_hy0 : ∀ r, r ∉ kSieveIndex k R W' → y r = 0) :
    S1InnerBoundM k R W' y
      (∑ r ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (r i) : ℝ)) := by
  classical
  intro s hs α hα
  have hPprime : ∀ p ∈ s.primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  have hslots : ∀ (q : {x // x ∈ s.primeFactors}),
      (α q.1 q.2).1 ≠ (α q.1 q.2).2 := by
    intro q
    have hmem := (Finset.mem_pi.mp hα) q.1 q.2
    rw [Finset.mem_offDiag] at hmem
    exact hmem.2.2
  have hqR : ∀ q : {x // x ∈ s.primeFactors}, (1 : ℝ) < ((q : ℕ) : ℝ) := by
    intro q
    exact_mod_cast (hPprime _ q.2).one_lt
  have hqne0 : ∀ q : {x // x ∈ s.primeFactors}, (((q : ℕ) : ℝ) - 1) ≠ 0 := by
    intro q
    have := hqR q
    intro h
    linarith
  have hσsq : ∀ (sel : Fin k × Fin k → Fin k) i,
      Squarefree (slotProd s α sel i) :=
    fun sel i => hs.squarefree_of_dvd (slotProd_dvd hs α sel i)
  have hT : (0 : ℝ) < ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 1) := by
    apply Finset.prod_pos
    intro q _
    have := hqR q
    linarith
  -- the non-absorbed-prime product reindex (verbatim from `inner_abs_le`)
  have hreindex : ∀ (sel : Fin k × Fin k → Fin k), ∀ u : Fin k → ℕ,
      (∏ i, ∏ p ∈ (slotProd s α sel i
            / Nat.gcd (slotProd s α sel i) (u i)).primeFactors, ((p : ℝ) - 1))
        = ∏ q ∈ s.primeFactors.attach.filter
            (fun q : {x // x ∈ s.primeFactors} => ¬ (q : ℕ) ∣ u (sel (α q.1 q.2))),
            (((q : ℕ) : ℝ) - 1) := by
    intro sel u
    rw [← Finset.prod_fiberwise_of_maps_to
      (g := fun q : {x // x ∈ s.primeFactors} => sel (α q.1 q.2))
      (t := (Finset.univ : Finset (Fin k)))
      (fun q _ => Finset.mem_univ _)
      (fun q : {x // x ∈ s.primeFactors} => (((q : ℕ) : ℝ) - 1))]
    apply Finset.prod_congr rfl
    intro i _
    have hcne : slotProd s α sel i / Nat.gcd (slotProd s α sel i) (u i) ≠ 0 := by
      have hσpos : 0 < slotProd s α sel i := Squarefree.pos (hσsq sel i)
      have hgpos : 0 < Nat.gcd (slotProd s α sel i) (u i) :=
        Nat.gcd_pos_of_pos_left _ hσpos
      have hgle : Nat.gcd (slotProd s α sel i) (u i) ≤ slotProd s α sel i :=
        Nat.le_of_dvd hσpos (Nat.gcd_dvd_left _ _)
      exact (Nat.div_pos hgle hgpos).ne'
    have hset : (slotProd s α sel i
          / Nat.gcd (slotProd s α sel i) (u i)).primeFactors
        = ((s.primeFactors.attach.filter
            (fun q : {x // x ∈ s.primeFactors} => ¬ (q : ℕ) ∣ u (sel (α q.1 q.2)))).filter
            (fun q => sel (α q.1 q.2) = i)).image
              (fun q : {x // x ∈ s.primeFactors} => (q : ℕ)) := by
      ext p
      simp only [Nat.mem_primeFactors, Finset.mem_image, Finset.mem_filter,
        Finset.mem_attach, true_and]
      constructor
      · rintro ⟨hp, hpc, -⟩
        obtain ⟨hpσ, hpu⟩ := (prime_dvd_cofactor_iff (hσsq sel i) hp).mp hpc
        obtain ⟨hmem, hsel⟩ := (prime_dvd_slotProd_iff α sel hp i).mp hpσ
        refine ⟨⟨p, hmem⟩, ⟨?_, hsel⟩, rfl⟩
        simp only
        rw [hsel]
        exact hpu
      · rintro ⟨q, ⟨hqnot, hqsel⟩, rfl⟩
        have hqp : (q : ℕ).Prime := hPprime _ q.2
        refine ⟨hqp, ?_, hcne⟩
        apply (prime_dvd_cofactor_iff (hσsq sel i) hqp).mpr
        refine ⟨(prime_dvd_slotProd_iff α sel hqp i).mpr ⟨q.2, hqsel⟩, ?_⟩
        rw [← hqsel]
        exact hqnot
    rw [hset, Finset.prod_image]
    intro q₁ _ q₂ _ h
    exact Subtype.ext h
  -- termwise absolute bound (via `|y| ≤ 1`, NOT domination)
  have hterm : ∀ u ∈ kSieveIndex k R W',
      |(∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ))|
      ≤ (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
          * ((1 / ∏ i, (Nat.totient (u i) : ℝ))
            * ∏ q ∈ s.primeFactors.attach.filter
                (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                  ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                (((q : ℕ) : ℝ) - 1)) := by
    intro u hu
    have hΦu_pos : 0 < ∏ i, (Nat.totient (u i) : ℝ) := by
      apply Finset.prod_pos; intro i _
      exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos hu i)
    have hΦcast : ∀ v : Fin k → ℕ, 0 ≤ ∏ i, (Nat.totient (v i) : ℝ) :=
      fun v => Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
    have habsμ : ∀ v : Fin k → ℕ, |∏ i, ((μ (v i) : ℤ) : ℝ)| ≤ 1 := by
      intro v
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _)
        (fun i _ => abs_moebius_real_le_one _)
    have hΦlcm_pos : ∀ (sel : Fin k × Fin k → Fin k),
        0 < ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α sel i)) : ℝ) := by
      intro sel
      apply Finset.prod_pos; intro i _
      have hpos : 0 < Nat.lcm (u i) (slotProd s α sel i) :=
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero
          (kSieveIndex_coord_pos hu i).ne' (Squarefree.pos (hσsq sel i)).ne')
      exact_mod_cast Nat.totient_pos.mpr hpos
    -- the ŷ bound: `|∏μ·y/∏φ(lcm)| ≤ 1/(∏φ(uᵢ)·W_sel)`
    have hyhat_le : ∀ (sel : Fin k × Fin k → Fin k),
        |(∏ i, ((μ (Nat.lcm (u i) (slotProd s α sel i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α sel i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α sel i)) : ℝ)|
          ≤ 1 / ((∏ i, (Nat.totient (u i) : ℝ))
              * ∏ i, ∏ p ∈ (slotProd s α sel i
                  / Nat.gcd (slotProd s α sel i) (u i)).primeFactors, ((p : ℝ) - 1)) := by
      intro sel
      have hden : (∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α sel i)) : ℝ))
          = (∏ i, (Nat.totient (u i) : ℝ))
              * ∏ i, ∏ p ∈ (slotProd s α sel i
                  / Nat.gcd (slotProd s α sel i) (u i)).primeFactors, ((p : ℝ) - 1) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _
        exact totient_lcm_split (hσsq sel i) (kSieveIndex_coord_pos hu i)
      rw [← hden, abs_div, abs_mul, abs_of_nonneg (hΦcast _)]
      exact div_le_div₀ zero_le_one
        (mul_le_one₀ (habsμ _) (abs_nonneg _) (hy1 _)) (hΦlcm_pos sel) (le_refl _)
    set Wσ : ℝ := ∏ i, ∏ p ∈ (slotProd s α Prod.fst i
        / Nat.gcd (slotProd s α Prod.fst i) (u i)).primeFactors,
        ((p : ℝ) - 1) with hWσ
    set Wτ : ℝ := ∏ i, ∏ p ∈ (slotProd s α Prod.snd i
        / Nat.gcd (slotProd s α Prod.snd i) (u i)).primeFactors,
        ((p : ℝ) - 1) with hWτ
    have hWpos : ∀ (sel : Fin k × Fin k → Fin k),
        (0:ℝ) < ∏ i, ∏ p ∈ (slotProd s α sel i
          / Nat.gcd (slotProd s α sel i) (u i)).primeFactors, ((p : ℝ) - 1) := by
      intro sel
      apply Finset.prod_pos; intro i _
      apply Finset.prod_pos; intro p hp
      have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      have h2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
      linarith
    have hWσ_pos : 0 < Wσ := hWpos Prod.fst
    have hWτ_pos : 0 < Wτ := hWpos Prod.snd
    have hchain : |(∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ))|
      ≤ (∏ i, (Nat.totient (u i) : ℝ))
          * (1 / ((∏ i, (Nat.totient (u i) : ℝ)) * Wσ))
          * (1 / ((∏ i, (Nat.totient (u i) : ℝ)) * Wτ)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hΦcast u)]
      have hNσ_nonneg : 0 ≤ 1 / ((∏ i, (Nat.totient (u i) : ℝ)) * Wσ) :=
        div_nonneg zero_le_one (mul_nonneg (hΦcast u) hWσ_pos.le)
      apply mul_le_mul _ (hyhat_le Prod.snd) (abs_nonneg _)
        (mul_nonneg (hΦcast u) hNσ_nonneg)
      exact mul_le_mul_of_nonneg_left (hyhat_le Prod.fst) (hΦcast u)
    have halg : (∏ i, (Nat.totient (u i) : ℝ))
        * (1 / ((∏ i, (Nat.totient (u i) : ℝ)) * Wσ))
        * (1 / ((∏ i, (Nat.totient (u i) : ℝ)) * Wτ))
        = (1 / ∏ i, (Nat.totient (u i) : ℝ)) * (Wσ⁻¹ * Wτ⁻¹) := by
      have h1 := hΦu_pos.ne'
      have h2 := hWσ_pos.ne'
      have h3 := hWτ_pos.ne'
      field_simp
    -- complementation identity (verbatim from `inner_abs_le`)
    set Bσ := s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)) with hBσ
    set Bτ := s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).2)) with hBτ
    have hWσ_eq : Wσ = ∏ q ∈ s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => ¬ (q : ℕ) ∣ u ((α q.1 q.2).1)), (((q : ℕ) : ℝ) - 1) :=
      hreindex Prod.fst u
    have hWτ_eq : Wτ = ∏ q ∈ s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => ¬ (q : ℕ) ∣ u ((α q.1 q.2).2)), (((q : ℕ) : ℝ) - 1) :=
      hreindex Prod.snd u
    have hsplitσ : (∏ q ∈ Bσ, (((q : ℕ) : ℝ) - 1)) * Wσ
        = ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 1) := by
      rw [hWσ_eq, hBσ]
      exact Finset.prod_filter_mul_prod_filter_not _ _ _
    have hsplitτ : (∏ q ∈ Bτ, (((q : ℕ) : ℝ) - 1)) * Wτ
        = ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 1) := by
      rw [hWτ_eq, hBτ]
      exact Finset.prod_filter_mul_prod_filter_not _ _ _
    have hdisj : Disjoint Bσ Bτ := by
      rw [Finset.disjoint_left]
      intro q hqσ hqτ
      rw [hBσ, Finset.mem_filter] at hqσ
      rw [hBτ, Finset.mem_filter] at hqτ
      exact hslots q (prime_dvd_coord_unique hu (hPprime _ q.2) hqσ.2 hqτ.2)
    have hunion : s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
          ∨ (q : ℕ) ∣ u ((α q.1 q.2).2))
        = Bσ ∪ Bτ := by
      rw [hBσ, hBτ, Finset.filter_or]
    have hcompl : Wσ⁻¹ * Wτ⁻¹
        = (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
            * ∏ q ∈ s.primeFactors.attach.filter
                (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                  ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                (((q : ℕ) : ℝ) - 1) := by
      have hKinv : (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
          = ((∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 1))⁻¹) ^ 2 := by
        rw [← Finset.prod_inv_distrib, ← Finset.prod_pow]
      rw [hunion, Finset.prod_union hdisj, hKinv]
      have h1 : Wσ⁻¹ = (∏ q ∈ Bσ, (((q : ℕ) : ℝ) - 1))
          / ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 1) := by
        rw [eq_div_iff hT.ne', ← hsplitσ]
        field_simp
      have h2 : Wτ⁻¹ = (∏ q ∈ Bτ, (((q : ℕ) : ℝ) - 1))
          / ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 1) := by
        rw [eq_div_iff hT.ne', ← hsplitτ]
        field_simp
      rw [h1, h2]
      ring
    calc |(∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ))|
        ≤ (∏ i, (Nat.totient (u i) : ℝ))
            * (1 / ((∏ i, (Nat.totient (u i) : ℝ)) * Wσ))
            * (1 / ((∏ i, (Nat.totient (u i) : ℝ)) * Wτ)) := hchain
      _ = (1 / ∏ i, (Nat.totient (u i) : ℝ)) * (Wσ⁻¹ * Wτ⁻¹) := halg
      _ = (1 / ∏ i, (Nat.totient (u i) : ℝ))
            * ((∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
              * ∏ q ∈ s.primeFactors.attach.filter
                  (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                    ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                  (((q : ℕ) : ℝ) - 1)) := by rw [hcompl]
      _ = (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
            * ((1 / ∏ i, (Nat.totient (u i) : ℝ))
              * ∏ q ∈ s.primeFactors.attach.filter
                  (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                    ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                  (((q : ℕ) : ℝ) - 1)) := by ring
  -- the partitioned sum bound (verbatim skeleton, weight `1/∏φ`)
  have hpart : ∑ u ∈ kSieveIndex k R W',
      ((1 / ∏ i, (Nat.totient (u i) : ℝ))
        * ∏ q ∈ s.primeFactors.attach.filter
            (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
              ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
            (((q : ℕ) : ℝ) - 1))
      ≤ 3 ^ s.primeFactors.card
          * ∑ u ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (u i) : ℝ) := by
    have hmaps : ∀ u ∈ kSieveIndex k R W',
        s.primeFactors.attach.filter
          (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
            ∨ (q : ℕ) ∣ u ((α q.1 q.2).2))
          ∈ s.primeFactors.attach.powerset :=
      fun u _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun u => (1 / ∏ i, (Nat.totient (u i) : ℝ))
        * ∏ q ∈ s.primeFactors.attach.filter
            (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
              ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
            (((q : ℕ) : ℝ) - 1))]
    have hQterm : ∀ Q ∈ s.primeFactors.attach.powerset,
        (∑ u ∈ (kSieveIndex k R W').filter
            (fun u => s.primeFactors.attach.filter
              (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)) = Q),
          (1 / ∏ i, (Nat.totient (u i) : ℝ))
            * ∏ q ∈ s.primeFactors.attach.filter
                (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                  ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                (((q : ℕ) : ℝ) - 1))
        ≤ (2 : ℝ) ^ Q.card
            * ∑ u ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (u i) : ℝ) := by
      intro Q hQ
      have hQprim : 0 ≤ ∏ q ∈ Q, (((q : ℕ) : ℝ) - 1) := by
        apply Finset.prod_nonneg
        intro q _
        have := hqR q
        linarith
      have hcongr : ∀ u ∈ (kSieveIndex k R W').filter
          (fun u => s.primeFactors.attach.filter
            (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
              ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)) = Q),
          (1 / ∏ i, (Nat.totient (u i) : ℝ))
            * ∏ q ∈ s.primeFactors.attach.filter
                (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                  ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                (((q : ℕ) : ℝ) - 1)
          = (1 / ∏ i, (Nat.totient (u i) : ℝ))
              * ∏ q ∈ Q, (((q : ℕ) : ℝ) - 1) := by
        intro u hu
        rw [Finset.mem_filter] at hu
        rw [hu.2]
      rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul]
      have hsub2 : (kSieveIndex k R W').filter
          (fun u => s.primeFactors.attach.filter
            (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
              ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)) = Q)
          ⊆ (kSieveIndex k R W').filter
            (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u ((α q.1 q.2).1)
              ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)) := by
        intro u hu
        rw [Finset.mem_filter] at hu ⊢
        refine ⟨hu.1, fun q hq => ?_⟩
        rw [← hu.2, Finset.mem_filter] at hq
        exact hq.2
      have herasure := box_marked_moment (R := R) (W' := W') hPprime
        (fun q => (α q.1 q.2).1) (fun q => (α q.1 q.2).2) Q
      have hQpair : (∏ q ∈ Q, ((((q : ℕ) : ℝ) - 1)⁻¹))
          * (∏ q ∈ Q, (((q : ℕ) : ℝ) - 1)) = 1 := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_eq_one
        intro q _
        exact inv_mul_cancel₀ (hqne0 q)
      calc (∑ u ∈ (kSieveIndex k R W').filter
            (fun u => s.primeFactors.attach.filter
              (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)) = Q),
            1 / ∏ i, (Nat.totient (u i) : ℝ))
            * ∏ q ∈ Q, (((q : ℕ) : ℝ) - 1)
          ≤ (∑ u ∈ (kSieveIndex k R W').filter
              (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u ((α q.1 q.2).1)
                ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
              1 / ∏ i, (Nat.totient (u i) : ℝ))
              * ∏ q ∈ Q, (((q : ℕ) : ℝ) - 1) :=
            mul_le_mul_of_nonneg_right
              (Finset.sum_le_sum_of_subset_of_nonneg hsub2
                (fun u _ _ => box_phiterm_nonneg u)) hQprim
        _ ≤ (2 ^ Q.card * (∏ q ∈ Q, ((((q : ℕ) : ℝ) - 1)⁻¹))
              * ∑ u ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (u i) : ℝ))
              * ∏ q ∈ Q, (((q : ℕ) : ℝ) - 1) :=
            mul_le_mul_of_nonneg_right herasure hQprim
        _ = (2 : ℝ) ^ Q.card
              * ∑ u ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (u i) : ℝ) := by
            linear_combination (2 ^ Q.card
              * ∑ u ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (u i) : ℝ)) * hQpair
    have hbinom : ∑ Q ∈ s.primeFactors.attach.powerset, (2 : ℝ) ^ Q.card
        = 3 ^ s.primeFactors.card := by
      have h := Finset.prod_add (fun _ => (2 : ℝ)) (fun _ => (1 : ℝ))
        s.primeFactors.attach
      simp only [Finset.prod_const_one, mul_one, Finset.prod_const] at h
      rw [Finset.card_attach] at h
      norm_num at h
      rw [← h]
    calc ∑ Q ∈ s.primeFactors.attach.powerset,
          ∑ u ∈ (kSieveIndex k R W').filter
            (fun u => s.primeFactors.attach.filter
              (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)) = Q),
            (1 / ∏ i, (Nat.totient (u i) : ℝ))
              * ∏ q ∈ s.primeFactors.attach.filter
                  (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                    ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                  (((q : ℕ) : ℝ) - 1)
        ≤ ∑ Q ∈ s.primeFactors.attach.powerset, (2 : ℝ) ^ Q.card
            * ∑ u ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (u i) : ℝ) :=
          Finset.sum_le_sum hQterm
      _ = (∑ Q ∈ s.primeFactors.attach.powerset, (2 : ℝ) ^ Q.card)
            * ∑ u ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (u i) : ℝ) :=
          (Finset.sum_mul _ _ _).symm
      _ = 3 ^ s.primeFactors.card
            * ∑ u ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (u i) : ℝ) := by
          rw [hbinom]
  -- identify the attach product, then conclude
  have hKattach : (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
      = ∏ p ∈ s.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 :=
    Finset.prod_attach s.primeFactors (fun p => (((p : ℝ) - 1)⁻¹) ^ 2)
  have hKnonneg : 0 ≤ ∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2 :=
    Finset.prod_nonneg fun q _ => sq_nonneg _
  calc |∑ u ∈ kSieveIndex k R W', (∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ))|
      ≤ ∑ u ∈ kSieveIndex k R W', |(∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ kSieveIndex k R W',
          (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
          * ((1 / ∏ i, (Nat.totient (u i) : ℝ))
            * ∏ q ∈ s.primeFactors.attach.filter
                (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                  ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                (((q : ℕ) : ℝ) - 1)) :=
      Finset.sum_le_sum hterm
    _ = (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
          * ∑ u ∈ kSieveIndex k R W',
              ((1 / ∏ i, (Nat.totient (u i) : ℝ))
                * ∏ q ∈ s.primeFactors.attach.filter
                    (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                      ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                    (((q : ℕ) : ℝ) - 1)) := by
        rw [Finset.mul_sum]
    _ ≤ (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
          * (3 ^ s.primeFactors.card
              * ∑ u ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (u i) : ℝ)) :=
        mul_le_mul_of_nonneg_left hpart hKnonneg
    _ = 3 ^ s.primeFactors.card
          * (∏ p ∈ s.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
          * ∑ r ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (r i) : ℝ) := by
        rw [hKattach]
        ring

/-! ## The constant-`B` assembly and the `yF` corollary -/

/-- **NC-1 deliverable 4 — the constant-`B` copy of `collision_lower_orderW_of`.**
The `y`-generic assembly is a mechanical transcription of the landed
`collision_lower_orderW_of` with the weighted moment `∑ (y r)²/∏φ` replaced by
the free constant `B` (`0 ≤ B`) — the `euler_tailW` step multiplies `B`
unchanged. -/
theorem collision_lower_orderW_ofM (k R W' D : ℕ) (y : (Fin k → ℕ) → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hy0 : ∀ r, r ∉ kSieveIndex k R W' → y r = 0)
    (hInner : S1InnerBoundM k R W' y B)
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hk : 1 ≤ k)
    (hDk : 12 * k ^ 2 ≤ D) :
    |s1CollisionForm k R W' y| ≤ 12 * (k : ℝ) ^ 2 / (D : ℝ) * B := by
  classical
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
  have hDposN : 0 < D := by omega
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDposN
  have hκ : (0 : ℝ) ≤ 12 * (k : ℝ) ^ 2 / (D : ℝ) := by positivity
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · subst hR0
    have hempty : kSieveIndex k 0 W' = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro r hr
      exact absurd ((mem_kSieveIndex_iff r).mp hr).2.2.2 (Nat.not_lt_zero _)
    unfold s1CollisionForm
    rw [hempty]
    simp only [Finset.sum_empty, abs_zero]
    positivity
  have h1mem : (1 : ℕ) ∈ collisionModuli k R := by
    rw [collisionModuli, Finset.mem_range]
    have := Nat.one_le_pow k R hRpos
    omega
  have hcompat := compat_moebius_expansion k R W' y
  have herase := Finset.add_sum_erase (collisionModuli k R)
    (fun t => ((μ t : ℤ) : ℝ)
      * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
          (if t ∣ cRad d e then s1Summand k R W' y d e else 0)) h1mem
  have hG1 : (∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
      (if (1 : ℕ) ∣ cRad d e then s1Summand k R W' y d e else 0))
      = s1FullForm k R W' y := by
    unfold s1FullForm
    apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro e _
    rw [if_pos (one_dvd _)]
  have hμ1 : ((μ 1 : ℤ) : ℝ) = 1 := by
    rw [ArithmeticFunction.moebius_apply_one]
    norm_num
  have hkey : s1CollisionForm k R W' y
      = - ∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
              (if t ∣ cRad d e then s1Summand k R W' y d e else 0) := by
    have hsplit0 := s1_full_split k R W' y
    have hfull := s1_full_eq_yside k R W' y hy0
    simp only [hμ1, one_mul, hG1] at herase
    have e1 : s1CompatForm k R W' y
        = s1FullForm k R W' y
          + ∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
              * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
                  (if t ∣ cRad d e then s1Summand k R W' y d e else 0) := by
      rw [hcompat, ← herase]
    linarith
  have hbound : ∀ t ∈ (collisionModuli k R).erase 1,
      |((μ t : ℤ) : ℝ)
        * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
            (if t ∣ cRad d e then s1Summand k R W' y d e else 0)|
      ≤ (if Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p then
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
            * B
        else 0) := by
    intro t _
    by_cases hgood : Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p
    · rw [if_pos hgood]
      obtain ⟨hsq, _⟩ := hgood
      have hcard : (assignments k t).card
          = (k * k - k) ^ t.primeFactors.card := by
        rw [assignments, Finset.card_pi, Finset.prod_const,
          Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
      have hinvsq_nonneg : 0 ≤ ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 :=
        Finset.prod_nonneg fun p _ => sq_nonneg _
      have hGabs : |∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
          (if t ∣ cRad d e then s1Summand k R W' y d e else 0)|
          ≤ ((assignments k t).card : ℝ)
              * ((3 : ℝ) ^ t.primeFactors.card
                * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * B) := by
        rw [inner_collision_expand k R W' y hsq]
        calc |∑ α ∈ assignments k t,
              ∑ d ∈ (kSieveIndex k R W').filter
                  (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
                ∑ e ∈ (kSieveIndex k R W').filter
                    (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
                  s1Summand k R W' y d e|
            ≤ ∑ α ∈ assignments k t,
                |∑ d ∈ (kSieveIndex k R W').filter
                    (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
                  ∑ e ∈ (kSieveIndex k R W').filter
                      (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
                    s1Summand k R W' y d e| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _α ∈ assignments k t,
                ((3 : ℝ) ^ t.primeFactors.card
                  * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                  * B) := by
              apply Finset.sum_le_sum
              intro α hα
              have hinner := inner_exact k R W' y hy0
                (slotProd t α Prod.fst) (slotProd t α Prod.snd)
              unfold s1Summand
              rw [hinner]
              exact hInner hsq α hα
          _ = ((assignments k t).card : ℝ)
                * ((3 : ℝ) ^ t.primeFactors.card
                  * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                  * B) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hcast : ((assignments k t).card : ℝ) * (3 : ℝ) ^ t.primeFactors.card
          ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card := by
        rw [hcard]
        push_cast
        rw [← mul_pow]
        apply pow_le_pow_left₀
        · positivity
        · have hle : ((k * k - k : ℕ) : ℝ) ≤ (k : ℝ) * (k : ℝ) := by
            have h1 : (k * k - k : ℕ) ≤ k * k := Nat.sub_le _ _
            calc ((k * k - k : ℕ) : ℝ) ≤ ((k * k : ℕ) : ℝ) := by exact_mod_cast h1
              _ = (k : ℝ) * (k : ℝ) := by push_cast; ring
          nlinarith
      calc |((μ t : ℤ) : ℝ)
            * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
                (if t ∣ cRad d e then s1Summand k R W' y d e else 0)|
          ≤ |∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
              (if t ∣ cRad d e then s1Summand k R W' y d e else 0)| := by
            rw [abs_mul]
            have h1 := abs_moebius_real_le_one t
            have h2 := abs_nonneg (∑ d ∈ kSieveIndex k R W',
              ∑ e ∈ kSieveIndex k R W',
                (if t ∣ cRad d e then s1Summand k R W' y d e else 0))
            nlinarith
        _ ≤ ((assignments k t).card : ℝ)
              * ((3 : ℝ) ^ t.primeFactors.card
                * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * B) := hGabs
        _ ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
              * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
              * B := by
            have hrest : 0 ≤ (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * B :=
              mul_nonneg hinvsq_nonneg hB
            calc ((assignments k t).card : ℝ)
                  * ((3 : ℝ) ^ t.primeFactors.card
                    * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                    * B)
                = (((assignments k t).card : ℝ) * (3 : ℝ) ^ t.primeFactors.card)
                    * ((∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                      * B) := by ring
              _ ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
                    * ((∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                      * B) :=
                  mul_le_mul_of_nonneg_right hcast hrest
              _ = (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
                    * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                    * B := by ring
    · rw [if_neg hgood]
      by_cases hsq : Squarefree t
      · have hsmall : ∃ p ∈ t.primeFactors, ¬ D < p := by
          by_contra hall
          push Not at hall
          exact hgood ⟨hsq, hall⟩
        obtain ⟨p, hp, hple⟩ := hsmall
        have hzero := inner_collision_zeroW k R W' D y hDlt
          (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp) (not_lt.mp hple)
        rw [hzero, mul_zero, abs_zero]
      · have hμ0 : ((μ t : ℤ) : ℝ) = 0 := by
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
          norm_num
        rw [hμ0, zero_mul, abs_zero]
  have htail := euler_tailW k (R ^ k + 1) D hk hDk
  calc |s1CollisionForm k R W' y|
      = |∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
              (if t ∣ cRad d e then s1Summand k R W' y d e else 0)| := by
        rw [hkey, abs_neg]
    _ ≤ ∑ t ∈ (collisionModuli k R).erase 1,
          |((μ t : ℤ) : ℝ)
            * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
                (if t ∣ cRad d e then s1Summand k R W' y d e else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ (collisionModuli k R).erase 1,
          (if Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p then
            (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
              * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
              * B
          else 0) :=
        Finset.sum_le_sum hbound
    _ = ∑ t ∈ (((collisionModuli k R).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1),
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
            * B := by
        rw [← Finset.sum_filter, Finset.filter_erase]
    _ = (∑ t ∈ (((collisionModuli k R).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1),
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
          * B := by
        rw [Finset.sum_mul]
    _ ≤ 12 * (k : ℝ) ^ 2 / (D : ℝ) * B :=
        mul_le_mul_of_nonneg_right htail hB

/-- **NC-1 deliverable 5 — the corollary at `y = yF`.**  Maynard's polynomial
weight `yF` (with `Qabs F ≤ 1`) satisfies the S1 collision bound at the crude
moment `M := ∑ 1/∏φ`. -/
theorem collision_yF_M (R W' D : ℕ) (F : Poly) (hQ : Qabs F ≤ 1)
    (hDlt : ∀ p, p.Prime → ¬p ∣ W' → D < p) (hDk : 12 * 5 ^ 2 ≤ D) :
    |s1CollisionForm 5 R W' (yF R W' F)|
      ≤ 12 * (5 : ℝ) ^ 2 / D * ∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ) := by
  have hy0 : ∀ r, r ∉ kSieveIndex 5 R W' → yF R W' F r = 0 := by
    intro r hr; unfold yF; rw [if_neg hr]
  have hy1 : ∀ r, |yF R W' F r| ≤ 1 := fun r =>
    le_trans (yF_abs_le_Qabs R W' F r) (by exact_mod_cast hQ)
  have hInner : S1InnerBoundM 5 R W' (yF R W' F)
      (∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ)) :=
    s1_inner_bounded 5 R W' (yF R W' F) hy1 hy0
  have hM : 0 ≤ ∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ) :=
    Finset.sum_nonneg fun r _ => box_phiterm_nonneg r
  exact collision_lower_orderW_ofM 5 R W' D (yF R W' F) _ hM hy0 hInner hDlt
    (by norm_num) hDk

end Salt.Twelve
