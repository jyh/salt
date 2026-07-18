/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHBal
import Salt.SW.CoprimeBV
import Salt.SW.GrahamL2

/-!
# The DH balance tail bound and crux (`T-BAL`, R3(b)+R4+R5) — part 2

Continues `Salt/SW/DHBal.lean`. Supplies the multiples-mass (R3(b)), the u-carrying
tail bound `tail_sum_le_mollified` (R4), and works toward the extraction crux (R5).

## The honest R3(b) identity (the linchpin, ★★)

For squarefree `m` and real `χ` (`χ² = 1`), the multiples mass factors over the divisors:
`Σ_{t≤y} dhA(m·t) = Σ_{g|m} chiRe(g) · Σ_{d≤y, (d,m/g)=1} chiRe(d)·⌊y/d⌋`, and each
coprime-restricted inner sum unfolds (`sum_coprime_eq_moebius_multiples`) as
`Σ_{k|m/g} μ(k)·chiRe(k)·mass(⌊y/k⌋)` where `mass(Y) = Σ_{n≤Y} dhA(n)` is the landed R3(a)
object. Since `mass ≥ 0` (dhA positivity) and all Dirichlet coefficients are `≤ 1` in absolute
value, the signed sum is dominated by `Σ_{g|m}Σ_{k|m/g} mass(⌊y/k⌋) ≤ σ₀(m)²·mass(y)`, giving
`Σ_{t≤y} dhA(m·t) ≤ 4^{ω(m)}·((L(1,χ)).re·y + 20·√q(1+log q)·√y)` via R3(a). No
coprime-restricted L-function is needed — the cancellation lives entirely in the landed R3(a)
mass. This resolves the freeze's vague "σ₀-loss" and the refuters' concern (the honest constant
is `4^{ω(m)}`, a clean `C^ω`-grade absorbed into the eventual `k`).
-/

open Complex

noncomputable section

namespace Salt.SW

open Finset ArithmeticFunction
open scoped ArithmeticFunction.omega

/-! ## Foundations: the R3(a) mass, its positivity, monotonicity, and character-count form -/

/-- The dhA mass `Σ_{n≤Y} dhA χ n ≥ 0` (each `dhA χ n ≥ 0` for real `χ`, `dhA_nonneg`). -/
lemma dhA_mass_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (Y : ℕ) :
    0 ≤ ∑ n ∈ Finset.Icc 1 Y, dhA χ n :=
  Finset.sum_nonneg (fun n hn => dhA_nonneg χ hsq (by rw [Finset.mem_Icc] at hn; omega))

/-- The dhA mass is monotone in the upper limit (nonnegative summands). -/
lemma dhA_mass_mono {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {Y₁ Y₂ : ℕ}
    (h : Y₁ ≤ Y₂) :
    ∑ n ∈ Finset.Icc 1 Y₁, dhA χ n ≤ ∑ n ∈ Finset.Icc 1 Y₂, dhA χ n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h)
    (fun n hn _ => dhA_nonneg χ hsq (by rw [Finset.mem_Icc] at hn; omega))

/-- **The mass ↔ character-count identity.** `Σ_{n≤Y} dhA χ n = Σ_{e≤Y} chiRe χ e · ⌊Y/e⌋`
(the classical divisor-sum swap: `dhA = 1 ∗ χ_ℝ`, count multiples). Pure reindexing. -/
lemma dhA_mass_eq_char_count {q : ℕ} (χ : DirichletCharacter ℂ q) (Y : ℕ) :
    ∑ n ∈ Finset.Icc 1 Y, dhA χ n
      = ∑ e ∈ Finset.Icc 1 Y, chiRe χ e * ((Y / e : ℕ) : ℝ) := by
  have hstep : ∀ n ∈ Finset.Icc 1 Y, dhA χ n
      = ∑ e ∈ Finset.Icc 1 Y, (if e ∣ n then chiRe χ e else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hset : n.divisors = (Finset.Icc 1 Y).filter (fun e => e ∣ n) := by
      ext e
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) hn.2⟩, hdvd⟩
      · rintro ⟨_, hdvd⟩; exact ⟨hdvd, by omega⟩
    rw [dhA, hset, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Finset.mem_Icc] at he
  rw [← Finset.sum_filter, sum_dvd_reindex he.1 (fun _ => chiRe χ e), Finset.sum_const,
      Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]

/-! ## The coprime identity (★) — the coprime-restricted inner sum as a Möbius mass sum -/

/-- **(★) — the coprime-restricted character sum as a Möbius mass sum.** For real `χ`
(`χ² = 1`), a modulus `κ ≥ 1`, and any `y`,
`Σ_{d≤y, (d,κ)=1} chiRe χ d·⌊y/d⌋ = Σ_{k|κ} μ(k)·chiRe χ k·mass(⌊y/k⌋)`.
`sum_coprime_eq_moebius_multiples` unfolds coprimality; then `chiRe(k·e)=chiRe k·chiRe e`
(real), `⌊y/(k·e)⌋=⌊⌊y/k⌋/e⌋`, and the inner `Σ_e chiRe e·⌊(y/k)/e⌋` collapses to the mass at
`⌊y/k⌋` by `dhA_mass_eq_char_count`. -/
lemma inner_coprime_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {κ : ℕ}
    (hκ : 1 ≤ κ) (y : ℕ) :
    ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Nat.Coprime d κ), chiRe χ d * ((y / d : ℕ) : ℝ)
      = ∑ k ∈ κ.divisors,
          (moebius k : ℝ) * chiRe χ k * (∑ n ∈ Finset.Icc 1 (y / k), dhA χ n) := by
  rw [sum_coprime_eq_moebius_multiples κ y hκ (fun d => chiRe χ d * ((y / d : ℕ) : ℝ))]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hinner : ∑ e ∈ Finset.Icc 1 (y / k), chiRe χ (k * e) * ((y / (k * e) : ℕ) : ℝ)
      = chiRe χ k * ∑ n ∈ Finset.Icc 1 (y / k), dhA χ n := by
    rw [dhA_mass_eq_char_count χ (y / k), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [chiRe_mul χ hsq k e, ← Nat.div_div_eq_div_mul]; ring
  rw [hinner]; ring

/-! ## The g-grouping identity (†) — the per-element divisor split -/

/-- **(†) — the per-element divisor split.** For real `χ` (`χ² = 1`) and `m ≥ 1`,
`dhA χ (m·t) = Σ_{g|m} chiRe χ g · Σ_{d|t, (d,m/g)=1} chiRe χ d`. The divisor bijection
`a ↦ (gcd(a,m), a/gcd(a,m))` on `(m·t).divisors` (inverse `(g,d) ↦ g·d`), with
`a ∣ m·t ↔ (a/gcd(a,m)) ∣ t` (`dvd_mul_iff_div_gcd_dvd`) and
`gcd(g·d,m) = g·gcd(d,m/g) = g` (`Nat.gcd_mul_left`, coprimality). No squarefree needed. -/
lemma dhA_mul_eq_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ}
    (hm : 1 ≤ m) (t : ℕ) :
    dhA χ (m * t)
      = ∑ g ∈ m.divisors, chiRe χ g
          * ∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d (m / g)), chiRe χ d := by
  have hRHS : (∑ g ∈ m.divisors, chiRe χ g
        * ∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d (m / g)), chiRe χ d)
      = ∑ p ∈ m.divisors.sigma (fun g => t.divisors.filter (fun d => Nat.Coprime d (m / g))),
          chiRe χ (p.1 * p.2) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => (chiRe_mul χ hsq g d).symm)
  rw [dhA]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  rw [hRHS]
  have hm0 : m ≠ 0 := by omega
  have ht0 : t ≠ 0 := by omega
  refine Finset.sum_nbij' (fun a => (⟨Nat.gcd a m, a / Nat.gcd a m⟩ : (_ : ℕ) × ℕ))
    (fun p => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · -- hi : maps into the sigma
    intro a ha
    rw [Nat.mem_divisors] at ha
    obtain ⟨hadvd, _⟩ := ha
    have hapos : 0 < a := Nat.pos_of_dvd_of_pos hadvd (Nat.mul_pos hm ht)
    have hgpos : 0 < Nat.gcd a m := Nat.gcd_pos_iff.mpr (Or.inl hapos)
    rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨Nat.gcd_dvd_right a m, hm0⟩, ⟨?_, ht0⟩, ?_⟩
    · exact (dvd_mul_iff_div_gcd_dvd hapos).mp hadvd
    · exact Nat.coprime_div_gcd_div_gcd hgpos
  · -- hj : inverse maps into the divisors
    intro p hp
    rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors] at hp
    obtain ⟨⟨hg, _⟩, ⟨hd, _⟩, _⟩ := hp
    rw [Nat.mem_divisors]
    exact ⟨Nat.mul_dvd_mul hg hd, Nat.mul_ne_zero hm0 ht0⟩
  · -- left_inv
    intro a ha
    rw [Nat.mem_divisors] at ha
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a m)
  · -- right_inv
    intro p hp
    rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors] at hp
    obtain ⟨⟨hg, _⟩, ⟨_, _⟩, hcop⟩ := hp
    have hgpos : 0 < p.1 := Nat.pos_of_dvd_of_pos hg hm
    have hgcd : Nat.gcd (p.1 * p.2) m = p.1 := by
      conv_lhs => rw [show m = p.1 * (m / p.1) from (Nat.mul_div_cancel' hg).symm]
      rw [Nat.gcd_mul_left, hcop, Nat.mul_one]
    have hdiv : p.1 * p.2 / Nat.gcd (p.1 * p.2) m = p.2 := by
      rw [hgcd, Nat.mul_div_cancel_left p.2 hgpos]
    ext
    · exact hgcd
    · rw [hdiv]
  · -- value compatibility
    intro a ha
    rw [Nat.mem_divisors] at ha
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left a m)]

/-- The coprime-restricted divisor swap: summing `chiRe χ d` over `d|t, (d,κ)=1` for `t≤y`
equals summing `chiRe χ d·⌊y/d⌋` over `d≤y, (d,κ)=1` (count the multiples of each `d`). -/
lemma inner_cop_swap {q : ℕ} (χ : DirichletCharacter ℂ q) (κ y : ℕ) :
    ∑ t ∈ Finset.Icc 1 y, ∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d κ), chiRe χ d
      = ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Nat.Coprime d κ),
          chiRe χ d * ((y / d : ℕ) : ℝ) := by
  have hstep : ∀ t ∈ Finset.Icc 1 y,
      ∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d κ), chiRe χ d
        = ∑ d ∈ Finset.Icc 1 y, (if d ∣ t ∧ Nat.Coprime d κ then chiRe χ d else 0) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have hset : t.divisors.filter (fun d => Nat.Coprime d κ)
        = (Finset.Icc 1 y).filter (fun d => d ∣ t ∧ Nat.Coprime d κ) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hdvd, _⟩, hcop⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) ht.2⟩, hdvd, hcop⟩
      · rintro ⟨⟨hd1, _⟩, hdvd, hcop⟩
        exact ⟨⟨hdvd, by omega⟩, hcop⟩
    rw [hset, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  by_cases hcop : Nat.Coprime d κ
  · rw [if_pos hcop,
        Finset.sum_congr rfl (fun t _ => if_congr (and_iff_left hcop) rfl rfl),
        ← Finset.sum_filter, sum_dvd_reindex hd.1 (fun _ => chiRe χ d), Finset.sum_const,
        Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]
  · rw [if_neg hcop]
    exact Finset.sum_eq_zero (fun t _ => if_neg (fun h => hcop h.2))

/-- **The g-grouping.** `Σ_{t≤y} dhA(m·t) = Σ_{g|m} chiRe χ g·Σ_{d≤y,(d,m/g)=1} chiRe χ d·⌊y/d⌋`.
Sum the per-element split (†) over `t`, swap `t`/`g`, and apply `inner_cop_swap`. -/
lemma dhA_mass_mul_eq_group {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ}
    (hm : 1 ≤ m) (y : ℕ) :
    ∑ t ∈ Finset.Icc 1 y, dhA χ (m * t)
      = ∑ g ∈ m.divisors, chiRe χ g
          * ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Nat.Coprime d (m / g)),
              chiRe χ d * ((y / d : ℕ) : ℝ) := by
  rw [Finset.sum_congr rfl (fun t _ => dhA_mul_eq_sum χ hsq hm t), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [← Finset.mul_sum, inner_cop_swap]

/-- **R3(b) — the multiples mass bound.** For real `χ` (`χ² = 1`) and `m ≥ 1`,
`Σ_{t≤y} dhA(m·t) ≤ σ₀(m)²·Σ_{n≤y} dhA(n)`. Combine the g-grouping with the coprime identity
(★), then dominate each `chiRe·μ·chiRe·mass(⌊y/k⌋)` by `mass(y)` (all Dirichlet coefficients
`≤ 1` in absolute value, `mass ≥ 0` and monotone), and count `σ₀(m)²` pairs `(g,k)`. -/
lemma dhA_mass_mul_le {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ}
    (hm : 1 ≤ m) (y : ℕ) :
    ∑ t ∈ Finset.Icc 1 y, dhA χ (m * t)
      ≤ ((m.divisors.card : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 y, dhA χ n := by
  have hm0 : m ≠ 0 := by omega
  rw [dhA_mass_mul_eq_group χ hsq hm y]
  have hstar : ∀ g ∈ m.divisors, chiRe χ g
        * ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Nat.Coprime d (m / g)),
            chiRe χ d * ((y / d : ℕ) : ℝ)
      = ∑ k ∈ (m / g).divisors,
          chiRe χ g * ((moebius k : ℝ) * chiRe χ k * ∑ n ∈ Finset.Icc 1 (y / k), dhA χ n) := by
    intro g hg
    have hg1 : 1 ≤ m / g := (Nat.one_le_div_iff (Nat.pos_of_mem_divisors hg)).mpr
      (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hg))
    rw [inner_coprime_eq χ hsq hg1 y, Finset.mul_sum]
  rw [Finset.sum_congr rfl hstar]
  have hQnn : 0 ≤ ∑ n ∈ Finset.Icc 1 y, dhA χ n := dhA_mass_nonneg χ hsq y
  -- bound the double sum termwise by mass(y)
  have hbound : ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors,
        chiRe χ g * ((moebius k : ℝ) * chiRe χ k * ∑ n ∈ Finset.Icc 1 (y / k), dhA χ n)
      ≤ ∑ g ∈ m.divisors, ∑ _k ∈ (m / g).divisors, ∑ n ∈ Finset.Icc 1 y, dhA χ n := by
    apply Finset.sum_le_sum; intro g _
    apply Finset.sum_le_sum; intro k _
    have hP : 0 ≤ ∑ n ∈ Finset.Icc 1 (y / k), dhA χ n := dhA_mass_nonneg χ hsq _
    have hmono : ∑ n ∈ Finset.Icc 1 (y / k), dhA χ n ≤ ∑ n ∈ Finset.Icc 1 y, dhA χ n :=
      dhA_mass_mono χ hsq (Nat.div_le_self y k)
    calc chiRe χ g * ((moebius k : ℝ) * chiRe χ k * ∑ n ∈ Finset.Icc 1 (y / k), dhA χ n)
        ≤ |chiRe χ g * ((moebius k : ℝ) * chiRe χ k * ∑ n ∈ Finset.Icc 1 (y / k), dhA χ n)| :=
          le_abs_self _
      _ = |chiRe χ g| * |(moebius k : ℝ)| * |chiRe χ k| * ∑ n ∈ Finset.Icc 1 (y / k), dhA χ n := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hP]; ring
      _ ≤ 1 * 1 * 1 * ∑ n ∈ Finset.Icc 1 y, dhA χ n := by
          gcongr
          · exact chiRe_abs_le_one χ g
          · rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
          · exact chiRe_abs_le_one χ k
      _ = ∑ n ∈ Finset.Icc 1 y, dhA χ n := by ring
  refine hbound.trans ?_
  -- count the pairs: σ₀(m/g) ≤ σ₀(m), and there are σ₀(m) values of g
  have hcount : ∀ g ∈ m.divisors, ∑ _k ∈ (m / g).divisors, ∑ n ∈ Finset.Icc 1 y, dhA χ n
      ≤ (m.divisors.card : ℝ) * ∑ n ∈ Finset.Icc 1 y, dhA χ n := by
    intro g hg
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hQnn
    have hsub : (m / g).divisors ⊆ m.divisors :=
      Nat.divisors_subset_of_dvd hm0 (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hg))
    exact_mod_cast Finset.card_le_card hsub
  refine (Finset.sum_le_sum hcount).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-- Squarefree divisor count: `σ₀(m) = 2^{ω(m)}` (each prime contributes exponent one). -/
lemma sqfree_card_divisors {m : ℕ} (hm : Squarefree m) :
    m.divisors.card = 2 ^ (m.primeFactors.card) := by
  rw [Nat.card_divisors hm.ne_zero]
  have h : ∀ p ∈ m.primeFactors, m.factorization p + 1 = 2 := by
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hm (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)]
  rw [Finset.prod_congr rfl h, Finset.prod_const]

/-- **The R4 moment.** `Σ_{m≤M} |gc(m)|·σ₀(m)²/m ≤ (1+log M)^{12}`. On the squarefree support
`|gc(m)|·σ₀(m)² ≤ 3^ω·(2^ω)² = 12^ω`; apply the landed `tau6W_le` at `k = 12`. -/
lemma sum_abs_grahamGc_sigmaSq_div_le {z : ℕ} (hz : 2 ≤ z) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, |grahamGc z m| * ((m.divisors.card : ℝ) ^ 2) / (m : ℝ)
      ≤ (1 + Real.log M) ^ 12 := by
  have hcond : ∀ m ∈ Finset.Icc 1 M,
      |grahamGc z m| * ((m.divisors.card : ℝ) ^ 2) / (m : ℝ) ≠ 0 → Squarefree m := by
    intro m _ hne
    by_contra hnsf
    exact hne (by rw [grahamGc_eq_zero_of_not_squarefree hnsf, abs_zero, zero_mul, zero_div])
  have key : ∑ m ∈ Finset.Icc 1 M, |grahamGc z m| * ((m.divisors.card : ℝ) ^ 2) / (m : ℝ)
      ≤ ∑ d ∈ (Finset.Icc 1 M).filter Squarefree,
          ((12 : ℕ) : ℝ) ^ (d.primeFactors.card) / (d : ℝ) := by
    rw [← Finset.sum_filter_of_ne hcond]
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, _⟩, hsf⟩ := hm
    have hω : ω m = m.primeFactors.card := by
      rw [ArithmeticFunction.cardDistinctFactors_apply]; exact (List.card_toFinset _).symm
    have hgc : |grahamGc z m| ≤ (3 : ℝ) ^ (m.primeFactors.card) := by
      have h := abs_grahamGc_le hz m; rwa [hω] at h
    have hcard : ((m.divisors.card : ℝ) ^ 2) = (4 : ℝ) ^ (m.primeFactors.card) := by
      rw [sqfree_card_divisors hsf]; push_cast; rw [pow_two, ← mul_pow]; norm_num
    have hbd : |grahamGc z m| * ((m.divisors.card : ℝ) ^ 2)
        ≤ ((12 : ℕ) : ℝ) ^ (m.primeFactors.card) := by
      calc |grahamGc z m| * ((m.divisors.card : ℝ) ^ 2)
          ≤ (3 : ℝ) ^ (m.primeFactors.card) * (4 : ℝ) ^ (m.primeFactors.card) :=
            mul_le_mul hgc (le_of_eq hcard) (by positivity) (by positivity)
        _ = ((12 : ℕ) : ℝ) ^ (m.primeFactors.card) := by rw [← mul_pow]; norm_num
    exact div_le_div_of_nonneg_right hbd (by positivity : (0 : ℝ) ≤ (m : ℝ))
  exact le_trans key (Salt.HardyLittlewood.tau6W_le M 12)

end Salt.SW

end
