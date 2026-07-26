/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RamRAdapter

/-!
# MultShiuBridge — the MULT-SHIU seam of MR Lemma 13 (S8 / MR-CORE, Route G node G4c)

MR §8.2 (`docs/sources/1501.04585v4.pdf` pp. 25–27; extract `docs/sources/mr_extract.md`
:129–130, :112–114) prices the level-`j` graded sets `𝒯_{j,r}` by the **ℓ-th moment
device**: on `𝒯_{j,r}` the prime-block factor `‖Q_r(1+it)‖` is *large*, so raising it to the
power `ℓ_{j,r}` normalises the indicator to `1`, and the object `Q_r(1+it)^ℓ · R_v(1+it)` is
re-expanded as a **single** Dirichlet polynomial, to which **Lemma 13**
(`Salt.MR.lemma13_moment`, `MomentsA2.lean:246`) applies.

MR spends one sentence on that re-expansion.  In Lean it is the genuinely new
combinatorial stone — the named seam **MULT-SHIU**, which `lemma13_moment` carries as its
two hypotheses `hsupp`/`hcoeff`.  This file discharges both, and hence prices
`∫_{-T}^{T} |Q^ℓ R|²` outright.

## The stones

* **M-1 `spoly_mul`** — the pairwise product.  For coefficient functions supported on
  `[1,M₁]`, `[1,M₂]`, `spoly M₁ f · spoly M₂ g = spoly (M₁M₂) (f * g)` where `f * g` is the
  **Dirichlet convolution** (mathlib's `ArithmeticFunction` multiplication).  The `t`-twist
  is exactly multiplicative — `((de : ℕ) : ℂ)^{1+it} = d^{1+it} e^{1+it}`
  (`natCast_mul_cpow`) — so no separate twist bridge is needed.
* **M-2 `ramQ_pow_mul_ramR_eq_spoly`** — the ℓ-fold, by induction on `ℓ` over M-1, with the
  window `[Y₁^ℓ · X₀, Mq^ℓ · Mr]` as the two named support stones
  `multShiuCoeff_support_low` / `_high`.  Under the block gate `Y₁ ≤ p ≤ 2Y₁` (`Mq = 2Y₁`)
  this is MR's `[Y₁^ℓ·Xe^{−v/H}, (2Y₁)^ℓ·2Xe^{−v/H}]`: the ℓ half-open prime fibres and the
  closed co-factor window multiply, endpoint by endpoint.
* **M-3 `coeff_bound_factorial_blockDiv`** — the count page, `‖a_n‖ ≤ ℓ!·g(n)` for
  `g = blockDiv Y₁` (MR's `g(p^k) = k+1` on `[Y₁,2Y₁]`, `1` off it).  Proof: the complex
  coefficient is dominated by the real majorant `bp^{*ℓ} * 1` (`bp` = the block-prime
  indicator, `1`-bounded because `ramareWeight` and the data are), and
  `(bp^{*ℓ} * 1)(n) = Σ_{d ∣ n} bp^{*ℓ}(d)`.  The exact-product count `bp^{*ℓ}(d)` is the
  number of **ordered** `ℓ`-tuples of block primes with product `d`; it is `≤ ℓ!` because a
  nonzero value forces `Ω(d) = ℓ`; peeling one prime at level `ℓ+1` therefore has at most
  `ω(d) ≤ Ω(d) = ℓ+1` choices, each contributing `≤ ℓ!`, i.e. `≤ (ℓ+1)!` in all — the
  multinomial bound without the multinomial.  Off the block-smooth divisors it vanishes, so the
  divisor sum is `≤ ℓ!·#{block-smooth d ∣ n} = ℓ!·blockDiv Y₁ n`.
* **M-4 `multShiu_moment`** — the compose: `lemma13_moment` with `hsupp`/`hcoeff`
  discharged, giving
  `∫_{-T}^{T} ‖Q^ℓ R‖² ≤ (2T + 20·(2Y₁)^ℓ Mr)·(ℓ!² · C/(Y₁^ℓ X₀))`.
  Instantiating `Mr ≍ 2Xe^{−v/H}`, `X₀ ≍ Xe^{−v/H}` recovers the paper's
  `(T/X + 2^ℓ Y₁)(ℓ+1)!²` shape up to the admitted `C^ℓ` slop (as documented at
  `lemma13_moment`).

Every gate is in-statement (law #253): the two window subsets, the block gate, the two
`1`-boundedness data, and the `1 ≤ Y₁`, `1 ≤ X₀` floors.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §6 (Lemma 13, pp. 20–21) and §8.2
(pp. 25–27).
-/

namespace Salt.MR

open scoped BigOperators
open Finset Complex

/-! ## §0 — reading a `spoly` at a longer length -/

/-- **Truncation.**  A `spoly` whose coefficients vanish above `M` may be read at any
length `M' ≥ M`: the extra terms are zero. -/
lemma spoly_of_support_le {M M' : ℕ} {a : ℕ → ℂ} (hMM : M ≤ M')
    (ha : ∀ n, M < n → a n = 0) (t : ℝ) :
    spoly M' a t = spoly M a t := by
  unfold spoly
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hMM) ?_).symm
  intro n hn hnot
  rw [Finset.mem_Icc] at hn
  have hMn : M < n := by
    by_contra h
    exact hnot (Finset.mem_Icc.mpr ⟨hn.1, by omega⟩)
  rw [ha n hMn, zero_div]

/-! ## §1 — M-1: the pairwise product of `σ = 1` Dirichlet polynomials

`spoly M₁ f · spoly M₂ g = spoly (M₁M₂) (f ⍟ g)`.  The regroup is the fibration of the
product range `[1,M₁] × [1,M₂]` over the frequency `n = de`; the fibre is the part of
`n`'s divisor antidiagonal inside the two windows, and the pairs outside are killed by the
two support hypotheses. -/

/-- **M-1 — the product of two `σ = 1` Dirichlet polynomials is a `σ = 1` Dirichlet
polynomial** with the Dirichlet-convolution coefficients.  The support hypotheses are
what make the identity exact: the convolution at `n ≤ M₁M₂` may reach factorisations
`n = de` with `d > M₁`, and those terms must vanish. -/
theorem spoly_mul {M₁ M₂ : ℕ} (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, M₁ < n → f n = 0) (hg : ∀ n, M₂ < n → g n = 0) (t : ℝ) :
    spoly M₁ (⇑f) t * spoly M₂ (⇑g) t = spoly (M₁ * M₂) (⇑(f * g)) t := by
  classical
  have hmaps : ∀ z ∈ (Finset.Icc 1 M₁ ×ˢ Finset.Icc 1 M₂),
      z.1 * z.2 ∈ Finset.Icc 1 (M₁ * M₂) := by
    intro z hz
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hz
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
      Nat.mul_le_mul hz.1.2 hz.2.2⟩
  calc spoly M₁ (⇑f) t * spoly M₂ (⇑g) t
      = ∑ z ∈ (Finset.Icc 1 M₁ ×ˢ Finset.Icc 1 M₂),
          (f z.1 * g z.2) / ((z.1 * z.2 : ℕ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
        rw [spoly, spoly, Finset.sum_mul_sum, ← Finset.sum_product']
        refine Finset.sum_congr rfl (fun z hz => ?_)
        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hz
        have h1 : (z.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have h2 : (z.2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hz1 : ((z.1 : ℂ)) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
          rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h0, -⟩; exact h1 h0
        have hz2 : ((z.2 : ℂ)) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
          rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h0, -⟩; exact h2 h0
        rw [natCast_mul_cpow]
        field_simp
    _ = ∑ n ∈ Finset.Icc 1 (M₁ * M₂),
          ∑ z ∈ (Finset.Icc 1 M₁ ×ˢ Finset.Icc 1 M₂).filter (fun z => z.1 * z.2 = n),
            (f z.1 * g z.2) / ((z.1 * z.2 : ℕ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = spoly (M₁ * M₂) (⇑(f * g)) t := by
        rw [spoly]
        refine Finset.sum_congr rfl (fun n hn => ?_)
        rw [Finset.mem_Icc] at hn
        have hn0 : n ≠ 0 := by omega
        have hinner : ∀ z ∈ (Finset.Icc 1 M₁ ×ˢ Finset.Icc 1 M₂).filter
              (fun z => z.1 * z.2 = n),
            (f z.1 * g z.2) / ((z.1 * z.2 : ℕ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
              = (f z.1 * g z.2) / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
          intro z hz
          rw [Finset.mem_filter] at hz
          rw [hz.2]
        rw [Finset.sum_congr rfl hinner, ← Finset.sum_div]
        congr 1
        rw [ArithmeticFunction.mul_apply]
        refine Finset.sum_subset ?_ ?_
        · intro z hz
          rw [Finset.mem_filter] at hz
          exact Nat.mem_divisorsAntidiagonal.mpr ⟨hz.2, hn0⟩
        · intro x hx hxnot
          rw [Nat.mem_divisorsAntidiagonal] at hx
          have hx1 : x.1 ≠ 0 := by
            rintro h
            rw [h, zero_mul] at hx
            exact hn0 hx.1.symm
          have hx2 : x.2 ≠ 0 := by
            rintro h
            rw [h, mul_zero] at hx
            exact hn0 hx.1.symm
          have hnotprod : x ∉ (Finset.Icc 1 M₁ ×ˢ Finset.Icc 1 M₂) := by
            intro hmem
            exact hxnot (Finset.mem_filter.mpr ⟨hmem, hx.1⟩)
          rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hnotprod
          by_cases hb1 : M₁ < x.1
          · rw [hf x.1 hb1, zero_mul]
          · have hb2 : M₂ < x.2 := by
              by_contra hb
              exact hnotprod ⟨⟨Nat.one_le_iff_ne_zero.mpr hx1, by omega⟩,
                ⟨Nat.one_le_iff_ne_zero.mpr hx2, by omega⟩⟩
            rw [hg x.2 hb2, mul_zero]

/-! ## §2 — the prime block polynomial as a `spoly`

The `𝒯_S` twin of `ramR_eq_spoly` (`USetThinTS.lean:94`) on the prime side. -/

/-- **The block-prime coefficients.**  `ramQ H P Q j c` is the `σ = 1` Dirichlet polynomial
of `p ↦ c p` masked to the half-open prime fibre `ramQblock H P Q j`. -/
noncomputable def ramQcoeff (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (p : ℕ) : ℂ :=
  if p ∈ ramQblock H P Q j then c p else 0

lemma ramQcoeff_of_notMem (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) {p : ℕ}
    (hp : p ∉ ramQblock H P Q j) : ramQcoeff H P Q j c p = 0 := by
  rw [ramQcoeff, if_neg hp]

/-- `0` is never in the prime fibre (its members are prime). -/
lemma zero_notMem_ramQblock (H : ℝ) (P Q j : ℕ) : (0 : ℕ) ∉ ramQblock H P Q j := by
  intro h
  rw [ramQblock, Finset.mem_filter] at h
  exact Nat.not_prime_zero h.2.1

/-- **The prime-side adapter.**  `ramQ = spoly Mq (ramQcoeff)` for any length `Mq`
containing the fibre. -/
lemma ramQ_eq_spoly_bounded (H : ℝ) (P Q j Mq : ℕ) (c : ℕ → ℂ)
    (hMq : ramQblock H P Q j ⊆ Finset.Icc 1 Mq) (t : ℝ) :
    ramQ H P Q j c t = spoly Mq (ramQcoeff H P Q j c) t := by
  rw [ramQ, spoly,
    ← Finset.sum_subset hMq (fun p _ hp => by
      rw [ramQcoeff_of_notMem H P Q j c hp, zero_div])]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [ramQcoeff, if_pos hp]

/-! ## §3 — M-2: the ℓ-fold product, its window, and its `spoly` form -/

/-- The prime-block coefficients as an arithmetic function (`a 0 = 0`). -/
noncomputable def ramQaf (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨ramQcoeff H P Q j c, ramQcoeff_of_notMem H P Q j c (zero_notMem_ramQblock H P Q j)⟩

@[simp] lemma ramQaf_apply (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (n : ℕ) :
    (ramQaf H P Q j c) n = ramQcoeff H P Q j c n := rfl

/-- The Ramaré co-factor coefficients as an arithmetic function (`a 0 = 0`). -/
noncomputable def ramRaf (H : ℝ) (N X P Q v : ℕ) (b : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨ramRcoeff H N X P Q v b, by
    refine ramRcoeff_of_notMem H N X P Q v b ?_
    intro h
    have h1 := ramRrange_one_le h
    omega⟩

@[simp] lemma ramRaf_apply (H : ℝ) (N X P Q v : ℕ) (b : ℕ → ℂ) (n : ℕ) :
    (ramRaf H N X P Q v b) n = ramRcoeff H N X P Q v b n := rfl

/-- **The MULT-SHIU coefficient** — the coefficient function of `Q_j(1+it)^ℓ · R_v(1+it)`,
the `ℓ`-fold Dirichlet convolution of the prime block with the Ramaré co-factor. -/
noncomputable def multShiuCoeff (H : ℝ) (N X P Q j v : ℕ) (b c : ℕ → ℂ) (ℓ : ℕ) :
    ArithmeticFunction ℂ :=
  ramQaf H P Q j c ^ ℓ * ramRaf H N X P Q v b

/-- Upper support of a Dirichlet convolution: `supp(f) ⊆ [·,M₁]`, `supp(g) ⊆ [·,M₂]` gives
`supp(f ⍟ g) ⊆ [·, M₁M₂]`. -/
lemma af_mul_support_high {f g : ArithmeticFunction ℂ} {M₁ M₂ : ℕ}
    (hf : ∀ n, M₁ < n → f n = 0) (hg : ∀ n, M₂ < n → g n = 0) :
    ∀ n, M₁ * M₂ < n → (f * g) n = 0 := by
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero (fun x hx => ?_)
  rw [Nat.mem_divisorsAntidiagonal] at hx
  by_cases h1 : M₁ < x.1
  · rw [hf x.1 h1, zero_mul]
  · have h2 : M₂ < x.2 := by
      by_contra h
      have hprod := Nat.mul_le_mul (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h)
      rw [hx.1] at hprod
      omega
    rw [hg x.2 h2, mul_zero]

/-- Lower support of a Dirichlet convolution: `supp(f) ⊆ [L₁,·]`, `supp(g) ⊆ [L₂,·]` gives
`supp(f ⍟ g) ⊆ [L₁L₂, ·]`. -/
lemma af_mul_support_low {f g : ArithmeticFunction ℂ} {L₁ L₂ : ℕ}
    (hf : ∀ n, n < L₁ → f n = 0) (hg : ∀ n, n < L₂ → g n = 0) :
    ∀ n, n < L₁ * L₂ → (f * g) n = 0 := by
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero (fun x hx => ?_)
  rw [Nat.mem_divisorsAntidiagonal] at hx
  by_cases h1 : x.1 < L₁
  · rw [hf x.1 h1, zero_mul]
  · have h2 : x.2 < L₂ := by
      by_contra h
      have hprod := Nat.mul_le_mul (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h)
      rw [hx.1] at hprod
      omega
    rw [hg x.2 h2, mul_zero]

/-- The upper window of the `ℓ`-fold: `Mq^ℓ · Mr`. -/
lemma af_pow_mul_support_high {f r : ArithmeticFunction ℂ} {Mq Mr : ℕ}
    (hf : ∀ n, Mq < n → f n = 0) (hr : ∀ n, Mr < n → r n = 0) (ℓ : ℕ) :
    ∀ n, Mq ^ ℓ * Mr < n → (f ^ ℓ * r) n = 0 := by
  induction ℓ with
  | zero =>
      intro n hn
      rw [pow_zero, one_mul]
      exact hr n (by simpa using hn)
  | succ ℓ ih =>
      intro n hn
      have hrw : f ^ (ℓ + 1) * r = f * (f ^ ℓ * r) := by ring
      rw [hrw]
      refine af_mul_support_high hf ih n ?_
      calc Mq * (Mq ^ ℓ * Mr) = Mq ^ (ℓ + 1) * Mr := by ring
        _ < n := hn

/-- The lower window of the `ℓ`-fold: `Lq^ℓ · Lr`. -/
lemma af_pow_mul_support_low {f r : ArithmeticFunction ℂ} {Lq Lr : ℕ}
    (hf : ∀ n, n < Lq → f n = 0) (hr : ∀ n, n < Lr → r n = 0) (ℓ : ℕ) :
    ∀ n, n < Lq ^ ℓ * Lr → (f ^ ℓ * r) n = 0 := by
  induction ℓ with
  | zero =>
      intro n hn
      rw [pow_zero, one_mul]
      exact hr n (by simpa using hn)
  | succ ℓ ih =>
      intro n hn
      have hrw : f ^ (ℓ + 1) * r = f * (f ^ ℓ * r) := by ring
      rw [hrw]
      refine af_mul_support_low hf ih n ?_
      calc n < Lq ^ (ℓ + 1) * Lr := hn
        _ = Lq * (Lq ^ ℓ * Lr) := by ring

/-- **The window, low end** (`hsupp` for `lemma13_moment`).  Every frequency carried by
`Q_j^ℓ R_v` is at least `Y₁^ℓ · X₀`: `ℓ` block primes, each `≥ Y₁`, times a co-factor
`≥ X₀`. -/
theorem multShiuCoeff_support_low (H : ℝ) (N X P Q j v Y₁ X₀ : ℕ) (b c : ℕ → ℂ) (ℓ : ℕ)
    (hQlow : ∀ p ∈ ramQblock H P Q j, Y₁ ≤ p)
    (hRlow : ∀ m ∈ ramRrange H N X v, X₀ ≤ m) :
    ∀ n, n < Y₁ ^ ℓ * X₀ → (multShiuCoeff H N X P Q j v b c ℓ) n = 0 := by
  refine af_pow_mul_support_low (fun n hn => ?_) (fun n hn => ?_) ℓ
  · rw [ramQaf_apply, ramQcoeff, if_neg]
    intro hmem
    exact absurd (hQlow n hmem) (by omega)
  · rw [ramRaf_apply, ramRcoeff, if_neg]
    intro hmem
    exact absurd (hRlow n hmem) (by omega)

/-- **The window, high end.**  Every frequency carried by `Q_j^ℓ R_v` is at most
`Mq^ℓ · Mr` — with `Mq = 2Y₁` this is MR's `(2Y₁)^ℓ · 2Xe^{−v/H}`. -/
theorem multShiuCoeff_support_high (H : ℝ) (N X P Q j v Mq Mr : ℕ) (b c : ℕ → ℂ) (ℓ : ℕ)
    (hMq : ramQblock H P Q j ⊆ Finset.Icc 1 Mq)
    (hMr : ramRrange H N X v ⊆ Finset.Icc 1 Mr) :
    ∀ n, Mq ^ ℓ * Mr < n → (multShiuCoeff H N X P Q j v b c ℓ) n = 0 := by
  refine af_pow_mul_support_high (fun n hn => ?_) (fun n hn => ?_) ℓ
  · rw [ramQaf_apply, ramQcoeff, if_neg]
    intro hmem
    have h := Finset.mem_Icc.mp (hMq hmem)
    omega
  · rw [ramRaf_apply, ramRcoeff, if_neg]
    intro hmem
    have h := Finset.mem_Icc.mp (hMr hmem)
    omega

/-- **M-2 — the ℓ-fold product IS a `σ = 1` Dirichlet polynomial.**
`Q_j(1+it)^ℓ · R_v(1+it) = Σ_{n ≤ Mq^ℓ Mr} a_n / n^{1+it}` with `a = multShiuCoeff`.  This
is the one sentence MR spends before eq (17). -/
theorem ramQ_pow_mul_ramR_eq_spoly (H : ℝ) (N X P Q j v Mq Mr : ℕ) (b c : ℕ → ℂ)
    (hMq : ramQblock H P Q j ⊆ Finset.Icc 1 Mq)
    (hMr : ramRrange H N X v ⊆ Finset.Icc 1 Mr) (ℓ : ℕ) (t : ℝ) :
    ramQ H P Q j c t ^ ℓ * ramR H N X P Q v b t
      = spoly (Mq ^ ℓ * Mr) (⇑(multShiuCoeff H N X P Q j v b c ℓ)) t := by
  have hqsupp : ∀ n, Mq < n → (ramQaf H P Q j c) n = 0 := by
    intro n hn
    rw [ramQaf_apply, ramQcoeff, if_neg]
    intro hmem
    have h := Finset.mem_Icc.mp (hMq hmem)
    omega
  have hrsupp : ∀ n, Mr < n → (ramRaf H N X P Q v b) n = 0 := by
    intro n hn
    rw [ramRaf_apply, ramRcoeff, if_neg]
    intro hmem
    have h := Finset.mem_Icc.mp (hMr hmem)
    omega
  induction ℓ with
  | zero =>
      rw [multShiuCoeff, pow_zero, one_mul, pow_zero, one_mul, pow_zero, one_mul]
      exact ramR_eq_spoly H N X P Q v Mr b hMr t
  | succ ℓ ih =>
      have hstep : ramQ H P Q j c t ^ (ℓ + 1) * ramR H N X P Q v b t
          = ramQ H P Q j c t * (ramQ H P Q j c t ^ ℓ * ramR H N X P Q v b t) := by ring
      have hmul := spoly_mul (M₁ := Mq) (M₂ := Mq ^ ℓ * Mr) (ramQaf H P Q j c)
        (multShiuCoeff H N X P Q j v b c ℓ) hqsupp
        (af_pow_mul_support_high hqsupp hrsupp ℓ) t
      have hlen : Mq * (Mq ^ ℓ * Mr) = Mq ^ (ℓ + 1) * Mr := by ring
      have hcoe : ramQaf H P Q j c * multShiuCoeff H N X P Q j v b c ℓ
          = multShiuCoeff H N X P Q j v b c (ℓ + 1) := by
        rw [multShiuCoeff, multShiuCoeff]; ring
      have hfun : (⇑(ramQaf H P Q j c) : ℕ → ℂ) = ramQcoeff H P Q j c := rfl
      rw [hlen, hcoe, hfun] at hmul
      rw [hstep, ih, ramQ_eq_spoly_bounded H P Q j Mq c hMq t, hmul]

/-! ## §4 — the real majorant machinery

The count is done over `ℝ`: the complex coefficient is dominated term-by-term by the
convolution of the block-prime indicator with the constant-`1` co-factor majorant, on the
SAME divisor antidiagonal, so no re-indexing is needed. -/

/-- The `1`-bounded co-factor majorant (`ζ`-shaped: `0` at `0`, `1` elsewhere). -/
def oneAf : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else 1, by simp⟩

@[simp] lemma oneAf_apply (n : ℕ) : oneAf n = if n = 0 then 0 else 1 := rfl

lemma oneAf_apply_ne_zero {n : ℕ} (hn : n ≠ 0) : oneAf n = 1 := by
  rw [oneAf_apply, if_neg hn]

/-- Convolution with `oneAf` is the divisor sum. -/
lemma af_mul_oneAf_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    (f * oneAf) n = ∑ d ∈ n.divisors, f d := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun x y => f x * oneAf y)]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Nat.mem_divisors] at hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd.2 (Nat.eq_zero_of_zero_dvd hd.1)
  have hpos : 0 < n / d :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1) (Nat.pos_of_ne_zero hd0)
  rw [oneAf_apply_ne_zero hpos.ne', mul_one]

/-- **The majorant transfer.**  Norms of a Dirichlet convolution are dominated by the
convolution of the majorants. -/
lemma norm_af_mul_le {F G : ArithmeticFunction ℂ} {F' G' : ArithmeticFunction ℝ}
    (hF : ∀ n, ‖F n‖ ≤ F' n) (hG : ∀ n, ‖G n‖ ≤ G' n) (n : ℕ) :
    ‖(F * G) n‖ ≤ (F' * G') n := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun x _ => ?_))
  rw [norm_mul]
  exact mul_le_mul (hF x.1) (hG x.2) (norm_nonneg _)
    (le_trans (norm_nonneg _) (hF x.1))

/-- **The block-prime indicator** — MR's `g` at the primes: `1` on the primes of the dyadic
block `[Y₁, 2Y₁]`, `0` elsewhere. -/
noncomputable def blockPrimeAf (Y₁ : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun p => if p.Prime ∧ Y₁ ≤ p ∧ p ≤ 2 * Y₁ then 1 else 0, by
    rw [if_neg]
    rintro ⟨h, -⟩
    exact Nat.not_prime_zero h⟩

@[simp] lemma blockPrimeAf_apply (Y₁ p : ℕ) :
    (blockPrimeAf Y₁) p = if p.Prime ∧ Y₁ ≤ p ∧ p ≤ 2 * Y₁ then 1 else 0 := rfl

lemma blockPrimeAf_nonneg (Y₁ p : ℕ) : 0 ≤ (blockPrimeAf Y₁) p := by
  rw [blockPrimeAf_apply]
  split_ifs <;> norm_num

lemma blockPrimeAf_le_one (Y₁ p : ℕ) : (blockPrimeAf Y₁) p ≤ 1 := by
  rw [blockPrimeAf_apply]
  split_ifs <;> norm_num

lemma blockPrimeAf_eq_zero_of_not_prime {Y₁ p : ℕ} (hp : ¬ p.Prime) :
    (blockPrimeAf Y₁) p = 0 := by
  rw [blockPrimeAf_apply, if_neg]
  rintro ⟨h, -⟩
  exact hp h

lemma blockPrimeAf_ne_zero_iff {Y₁ p : ℕ} (h : (blockPrimeAf Y₁) p ≠ 0) :
    p.Prime ∧ Y₁ ≤ p ∧ p ≤ 2 * Y₁ := by
  by_contra hc
  rw [blockPrimeAf_apply, if_neg hc] at h
  exact h rfl

/-- The prime-block coefficients are dominated by the block-prime indicator (the datum is
`1`-bounded, the fibre sits inside the block). -/
lemma norm_ramQaf_le (H : ℝ) (P Q j Y₁ : ℕ) {c : ℕ → ℂ} (hc : ∀ p, ‖c p‖ ≤ 1)
    (hblock : ∀ p ∈ ramQblock H P Q j, Y₁ ≤ p ∧ p ≤ 2 * Y₁) (n : ℕ) :
    ‖(ramQaf H P Q j c) n‖ ≤ (blockPrimeAf Y₁) n := by
  rw [ramQaf_apply, ramQcoeff, blockPrimeAf_apply]
  by_cases hmem : n ∈ ramQblock H P Q j
  · rw [if_pos hmem]
    have hp : n.Prime := by
      rw [ramQblock, Finset.mem_filter] at hmem
      exact hmem.2.1
    rw [if_pos ⟨hp, hblock n hmem⟩]
    exact hc n
  · rw [if_neg hmem, norm_zero]
    split_ifs <;> norm_num

/-- The Ramaré co-factor coefficients are `1`-bounded (`norm_ramRcoeff_le_one`), i.e.
dominated by `oneAf`. -/
lemma norm_ramRaf_le (H : ℝ) (N X P Q v : ℕ) {b : ℕ → ℂ} (hb : ∀ m, ‖b m‖ ≤ 1) (n : ℕ) :
    ‖(ramRaf H N X P Q v b) n‖ ≤ oneAf n := by
  by_cases hn : n = 0
  · subst hn
    rw [ArithmeticFunction.map_zero, norm_zero, oneAf_apply, if_pos rfl]
  · rw [oneAf_apply_ne_zero hn, ramRaf_apply]
    exact norm_ramRcoeff_le_one H N X P Q v hb n

/-- **The majorant of the ℓ-fold coefficient**: the `ℓ`-fold block-prime convolution
against the divisor-sum majorant of the co-factor. -/
lemma norm_multShiuCoeff_le (H : ℝ) (N X P Q j v Y₁ : ℕ) {b c : ℕ → ℂ}
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hblock : ∀ p ∈ ramQblock H P Q j, Y₁ ≤ p ∧ p ≤ 2 * Y₁) (ℓ : ℕ) :
    ∀ n, ‖(multShiuCoeff H N X P Q j v b c ℓ) n‖ ≤ ((blockPrimeAf Y₁) ^ ℓ * oneAf) n := by
  induction ℓ with
  | zero =>
      intro n
      rw [multShiuCoeff, pow_zero, one_mul, pow_zero, one_mul]
      exact norm_ramRaf_le H N X P Q v hb n
  | succ ℓ ih =>
      intro n
      have hcL : multShiuCoeff H N X P Q j v b c (ℓ + 1)
          = ramQaf H P Q j c * multShiuCoeff H N X P Q j v b c ℓ := by
        rw [multShiuCoeff, multShiuCoeff]; ring
      have hcR : (blockPrimeAf Y₁) ^ (ℓ + 1) * oneAf
          = blockPrimeAf Y₁ * ((blockPrimeAf Y₁) ^ ℓ * oneAf) := by ring
      rw [hcL, hcR]
      exact norm_af_mul_le (norm_ramQaf_le H P Q j Y₁ hc hblock) ih n

/-! ## §5 — M-3: the count page

`bp^{*ℓ}(d)` is the number of ORDERED `ℓ`-tuples of block primes with product `d`.  The
bound `≤ ℓ!` is the multinomial `ℓ!/∏kᵢ! ≤ ℓ!`; the Lean proof carries the sharper
invariant that a nonzero value forces `Ω(d) = ℓ`, so that the peel-one-prime step has at
most `ω(d) ≤ Ω(d) = ℓ+1` choices. -/

/-- `Ω(a·p) = Ω(a) + 1` for a prime `p` (via the prime-factor-list permutation). -/
private lemma length_primeFactorsList_mul_prime {a p : ℕ} (ha : a ≠ 0) (hp : p.Prime) :
    (a * p).primeFactorsList.length = a.primeFactorsList.length + 1 := by
  have hperm := Nat.perm_primeFactorsList_mul ha hp.pos.ne'
  rw [hperm.length_eq, List.length_append, Nat.primeFactorsList_prime hp]
  simp

/-- Block-smoothness is preserved by multiplying in a block prime. -/
private lemma blockSmooth_mul_prime {Y₁ a p : ℕ} (ha : a ≠ 0) (hp : p.Prime)
    (hsa : BlockSmooth Y₁ a) (hb : Y₁ ≤ p ∧ p ≤ 2 * Y₁) : BlockSmooth Y₁ (a * p) := by
  intro q hq
  rw [Nat.primeFactors_mul ha hp.pos.ne', Finset.mem_union] at hq
  rcases hq with h | h
  · exact hsa q h
  · rw [hp.primeFactors, Finset.mem_singleton] at h
    subst h
    exact hb

/-- `ω(d) ≤ Ω(d)`. -/
private lemma card_primeFactors_le_length (d : ℕ) :
    (d.primeFactors.card : ℝ) ≤ (d.primeFactorsList.length : ℝ) := by
  have h : d.primeFactors.card ≤ d.primeFactorsList.length := by
    have hle := List.toFinset_card_le (l := d.primeFactorsList)
    rwa [Nat.toFinset_factors d] at hle
  exact_mod_cast h

/-- The block primes dividing `d` are at most `ω(d)` many. -/
private lemma sum_blockPrimeAf_divisors_le (Y₁ d : ℕ) :
    ∑ e ∈ d.divisors, (blockPrimeAf Y₁) e ≤ (d.primeFactors.card : ℝ) := by
  classical
  have hsub : d.primeFactors ⊆ d.divisors := by
    intro e he
    rw [Nat.mem_primeFactors] at he
    exact Nat.mem_divisors.mpr ⟨he.2.1, he.2.2⟩
  have hzero : ∀ e ∈ d.divisors, e ∉ d.primeFactors → (blockPrimeAf Y₁) e = 0 := by
    intro e he hne
    rw [Nat.mem_divisors] at he
    refine blockPrimeAf_eq_zero_of_not_prime (fun hp => ?_)
    exact hne (Nat.mem_primeFactors.mpr ⟨hp, he.1, he.2⟩)
  calc ∑ e ∈ d.divisors, (blockPrimeAf Y₁) e
      = ∑ e ∈ d.primeFactors, (blockPrimeAf Y₁) e := (Finset.sum_subset hsub hzero).symm
    _ ≤ ∑ _e ∈ d.primeFactors, (1 : ℝ) :=
        Finset.sum_le_sum (fun e _ => blockPrimeAf_le_one Y₁ e)
    _ = (d.primeFactors.card : ℝ) := by simp

/-- One nonzero term of the peel forces the `Ω`-grading and block-smoothness of `d`. -/
private lemma blockPrimeAf_pow_succ_term {Y₁ ℓ d : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ d.divisorsAntidiagonal)
    (hih : ∀ e : ℕ, ((blockPrimeAf Y₁) ^ ℓ) e ≠ 0 →
      BlockSmooth Y₁ e ∧ e.primeFactorsList.length = ℓ)
    (hne : ((blockPrimeAf Y₁) ^ ℓ) x.1 * (blockPrimeAf Y₁) x.2 ≠ 0) :
    BlockSmooth Y₁ d ∧ d.primeFactorsList.length = ℓ + 1 := by
  rw [Nat.mem_divisorsAntidiagonal] at hx
  have h1 : ((blockPrimeAf Y₁) ^ ℓ) x.1 ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have h2 : (blockPrimeAf Y₁) x.2 ≠ 0 := fun h => hne (by rw [h, mul_zero])
  obtain ⟨hsm, hlen⟩ := hih x.1 h1
  obtain ⟨hp, hblk⟩ := blockPrimeAf_ne_zero_iff h2
  have hx1 : x.1 ≠ 0 := by
    rintro h
    rw [h, zero_mul] at hx
    exact hx.2 hx.1.symm
  refine ⟨?_, ?_⟩
  · rw [← hx.1]
    exact blockSmooth_mul_prime hx1 hp hsm hblk
  · rw [← hx.1, length_primeFactorsList_mul_prime hx1 hp, hlen]

/-- **The count.**  `bp^{*ℓ}(d) ≥ 0`, `≤ ℓ!`, and vanishes off the block-smooth `d` with
`Ω(d) = ℓ` — the ordered-factorisation count, proved by induction on `ℓ`. -/
lemma blockPrimeAf_pow_bound (Y₁ ℓ : ℕ) :
    ∀ d : ℕ, 0 ≤ ((blockPrimeAf Y₁) ^ ℓ) d ∧ ((blockPrimeAf Y₁) ^ ℓ) d ≤ (ℓ.factorial : ℝ)
      ∧ (((blockPrimeAf Y₁) ^ ℓ) d ≠ 0 →
          BlockSmooth Y₁ d ∧ d.primeFactorsList.length = ℓ) := by
  induction ℓ with
  | zero =>
      intro d
      rw [pow_zero, ArithmeticFunction.one_apply]
      refine ⟨by split_ifs <;> norm_num, by split_ifs <;> norm_num, fun hne => ?_⟩
      have hd : d = 1 := by
        by_contra h
        rw [if_neg h] at hne
        exact hne rfl
      subst hd
      exact ⟨blockSmooth_one Y₁, by rw [Nat.primeFactorsList_one]; rfl⟩
  | succ ℓ ih =>
      intro d
      have hih : ∀ e : ℕ, ((blockPrimeAf Y₁) ^ ℓ) e ≠ 0 →
          BlockSmooth Y₁ e ∧ e.primeFactorsList.length = ℓ := fun e => (ih e).2.2
      have hexp : ((blockPrimeAf Y₁) ^ (ℓ + 1)) d
          = ∑ x ∈ d.divisorsAntidiagonal,
              ((blockPrimeAf Y₁) ^ ℓ) x.1 * (blockPrimeAf Y₁) x.2 := by
        rw [pow_succ, ArithmeticFunction.mul_apply]
      refine ⟨?_, ?_, ?_⟩
      · rw [hexp]
        exact Finset.sum_nonneg (fun x _ =>
          mul_nonneg (ih x.1).1 (blockPrimeAf_nonneg Y₁ x.2))
      · rw [hexp]
        by_cases hΩ : d.primeFactorsList.length = ℓ + 1
        · have hstep : ∑ x ∈ d.divisorsAntidiagonal,
              ((blockPrimeAf Y₁) ^ ℓ) x.1 * (blockPrimeAf Y₁) x.2
              ≤ ∑ x ∈ d.divisorsAntidiagonal,
                  (ℓ.factorial : ℝ) * (blockPrimeAf Y₁) x.2 :=
            Finset.sum_le_sum (fun x _ =>
              mul_le_mul_of_nonneg_right (ih x.1).2.1 (blockPrimeAf_nonneg Y₁ x.2))
          have hfac : ∑ x ∈ d.divisorsAntidiagonal, (ℓ.factorial : ℝ) * (blockPrimeAf Y₁) x.2
              = (ℓ.factorial : ℝ) * ∑ e ∈ d.divisors, (blockPrimeAf Y₁) e := by
            rw [← Finset.mul_sum]
            congr 1
            exact Nat.sum_divisorsAntidiagonal' (f := fun _x y => (blockPrimeAf Y₁) y)
          have hω : ∑ e ∈ d.divisors, (blockPrimeAf Y₁) e ≤ ((ℓ : ℝ) + 1) := by
            refine le_trans (sum_blockPrimeAf_divisors_le Y₁ d) ?_
            have h := card_primeFactors_le_length d
            rw [hΩ] at h
            push_cast at h
            linarith
          have hfacnn : (0 : ℝ) ≤ (ℓ.factorial : ℝ) := by positivity
          calc ∑ x ∈ d.divisorsAntidiagonal,
                ((blockPrimeAf Y₁) ^ ℓ) x.1 * (blockPrimeAf Y₁) x.2
              ≤ ∑ x ∈ d.divisorsAntidiagonal, (ℓ.factorial : ℝ) * (blockPrimeAf Y₁) x.2 :=
                hstep
            _ = (ℓ.factorial : ℝ) * ∑ e ∈ d.divisors, (blockPrimeAf Y₁) e := hfac
            _ ≤ (ℓ.factorial : ℝ) * ((ℓ : ℝ) + 1) :=
                mul_le_mul_of_nonneg_left hω hfacnn
            _ = ((ℓ + 1).factorial : ℝ) := by
                rw [Nat.factorial_succ]; push_cast; ring
        · have hzero : ∑ x ∈ d.divisorsAntidiagonal,
              ((blockPrimeAf Y₁) ^ ℓ) x.1 * (blockPrimeAf Y₁) x.2 = 0 := by
            refine Finset.sum_eq_zero (fun x hx => ?_)
            by_contra hne
            exact hΩ (blockPrimeAf_pow_succ_term hx hih hne).2
          rw [hzero]
          positivity
      · rw [hexp]
        intro hne
        obtain ⟨x, hx, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
        exact blockPrimeAf_pow_succ_term hx hih hxne

/-- **The divisor-sum count.**  `(bp^{*ℓ} ⍟ 1)(n) ≤ ℓ! · g(n)` with `g = blockDiv Y₁` —
each block-smooth divisor of `n` is hit by at most `ℓ!` ordered `ℓ`-tuples, and no other
divisor is hit at all. -/
lemma maj_le_factorial_blockDiv (Y₁ ℓ n : ℕ) :
    (((blockPrimeAf Y₁) ^ ℓ) * oneAf) n ≤ (ℓ.factorial : ℝ) * (blockDiv Y₁ n : ℝ) := by
  classical
  rw [af_mul_oneAf_apply]
  have hsub : n.divisors.filter (BlockSmooth Y₁) ⊆ n.divisors := Finset.filter_subset _ _
  have hzero : ∀ d ∈ n.divisors, d ∉ n.divisors.filter (BlockSmooth Y₁) →
      ((blockPrimeAf Y₁) ^ ℓ) d = 0 := by
    intro d hd hnot
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨hd, ((blockPrimeAf_pow_bound Y₁ ℓ d).2.2 h).1⟩)
  calc ∑ d ∈ n.divisors, ((blockPrimeAf Y₁) ^ ℓ) d
      = ∑ d ∈ n.divisors.filter (BlockSmooth Y₁), ((blockPrimeAf Y₁) ^ ℓ) d :=
        (Finset.sum_subset hsub hzero).symm
    _ ≤ ∑ _d ∈ n.divisors.filter (BlockSmooth Y₁), (ℓ.factorial : ℝ) :=
        Finset.sum_le_sum (fun d _ => (blockPrimeAf_pow_bound Y₁ ℓ d).2.1)
    _ = ((n.divisors.filter (BlockSmooth Y₁)).card : ℝ) * (ℓ.factorial : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (ℓ.factorial : ℝ) * (blockDiv Y₁ n : ℝ) := by rw [blockDiv]; ring

/-- **M-3 — the coefficient bound, `lemma13_moment`'s `hcoeff` byte-for-byte.**
`‖a_n‖ ≤ ℓ! · blockDiv Y₁ n` for the coefficients of `Q_j^ℓ R_v`.  The count: `n` in the
support factors as `p₁⋯p_ℓ·m` with the `pᵢ` block primes; the product `d = p₁⋯p_ℓ` is a
block-smooth divisor of `n` and is reached by at most `ℓ!` orderings. -/
theorem coeff_bound_factorial_blockDiv (H : ℝ) (N X P Q j v Y₁ : ℕ) {b c : ℕ → ℂ}
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hblock : ∀ p ∈ ramQblock H P Q j, Y₁ ≤ p ∧ p ≤ 2 * Y₁) (ℓ n : ℕ) :
    ‖(multShiuCoeff H N X P Q j v b c ℓ) n‖ ≤ (ℓ.factorial : ℝ) * (blockDiv Y₁ n : ℝ) :=
  le_trans (norm_multShiuCoeff_le H N X P Q j v Y₁ hb hc hblock ℓ n)
    (maj_le_factorial_blockDiv Y₁ ℓ n)

/-! ## §6 — M-4: the compose (MR §8.2's use of Lemma 13) -/

/-- **M-4 — the MULT-SHIU moment.**  With the block gate `Y₁ ≤ p ≤ 2Y₁` on the prime fibre
and `X₀ ≤ m ≤ Mr` on the co-factor window, and `1`-bounded data,

  `∫_{-T}^{T} ‖Q_j(1+it)^ℓ R_v(1+it)‖² dt ≤ (2T + 20·(2Y₁)^ℓ Mr)·(ℓ!²·C/(Y₁^ℓ X₀))`,

with the absolute Shiu constant `C` of `lemma13_moment`.  This is MR §8.2's application of
Lemma 13 (p. 26), with the MULT-SHIU seam discharged: `hsupp` by
`multShiuCoeff_support_low`, `hcoeff` by `coeff_bound_factorial_blockDiv`. -/
theorem multShiu_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ) (N X P Q j v Y₁ Mr X₀ ℓ : ℕ) (b c : ℕ → ℂ) (T : ℝ),
      1 ≤ Y₁ → 1 ≤ X₀ → 0 ≤ T →
      (∀ p ∈ ramQblock H P Q j, Y₁ ≤ p ∧ p ≤ 2 * Y₁) →
      (∀ m ∈ ramRrange H N X v, X₀ ≤ m) →
      ramRrange H N X v ⊆ Finset.Icc 1 Mr →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∫ t in (-T)..T, ‖ramQ H P Q j c t ^ ℓ * ramR H N X P Q v b t‖ ^ 2)
        ≤ (2 * T + 20 * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ))
            * ((ℓ.factorial : ℝ) ^ 2 * (C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ))) := by
  obtain ⟨C, hC, hL13⟩ := lemma13_moment
  refine ⟨C, hC, ?_⟩
  intro H N X P Q j v Y₁ Mr X₀ ℓ b c T hY₁ hX₀ hT hblock hRlow hMr hb hc
  -- the prime fibre sits in `[1, 2Y₁]`
  have hMq : ramQblock H P Q j ⊆ Finset.Icc 1 (2 * Y₁) := by
    intro p hp
    obtain ⟨hlo, hhi⟩ := hblock p hp
    exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩
  -- the integrand IS a `spoly` (M-2)
  have hint : (∫ t in (-T)..T, ‖ramQ H P Q j c t ^ ℓ * ramR H N X P Q v b t‖ ^ 2)
      = ∫ t in (-T)..T,
          ‖spoly ((2 * Y₁) ^ ℓ * Mr) (⇑(multShiuCoeff H N X P Q j v b c ℓ)) t‖ ^ 2 := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [ramQ_pow_mul_ramR_eq_spoly H N X P Q j v (2 * Y₁) Mr b c hMq hMr ℓ t]
  rw [hint]
  -- `hsupp` (M-2's low window) and `hcoeff` (M-3)
  have hXpos : 1 ≤ Y₁ ^ ℓ * X₀ := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (pow_ne_zero ℓ (by omega)) (by omega))
  exact hL13 Y₁ (Y₁ ^ ℓ * X₀) ((2 * Y₁) ^ ℓ * Mr) ℓ
    (⇑(multShiuCoeff H N X P Q j v b c ℓ)) T hY₁ hXpos hT
    (multShiuCoeff_support_low H N X P Q j v Y₁ X₀ b c ℓ
      (fun p hp => (hblock p hp).1) hRlow)
    (coeff_bound_factorial_blockDiv H N X P Q j v Y₁ hb hc hblock ℓ)

/-! ## §7 — the calibration: the gates ARE MR's own block conditions

`multShiu_moment`'s gates are not extra assumptions.  At the MR calibration
`Y₁ = ⌈e^{j/H}⌉`, `X' = Xe^{−v/H}` the block gate is exactly the width condition
`e^{1/H} ≤ 2` (i.e. `H ≥ 1/log 2`, held here at the corpus' `H ≥ 2`), and the co-factor
gates are the window's own two ends.  §7 discharges all three and pins the exit. -/

/-- **The block gate is the `e^{1/H} ≤ 2` width condition.**  For `H ≥ 2` the half-open
prime fibre `ramQblock` (`[e^{j/H}, e^{(j+1)/H})`) sits inside the dyadic block
`[Y₁, 2Y₁]` at `Y₁ = ⌈e^{j/H}⌉` — MR's `Q(s) = Σ_{Y₁ ≤ p ≤ 2Y₁} c_p p^{−s}` (p. 20). -/
theorem ramQblock_subset_dyadic_block (H : ℝ) (hH : 2 ≤ H) (P Q j : ℕ) :
    ∀ p ∈ ramQblock H P Q j,
      ⌈Real.exp ((j : ℝ) / H)⌉₊ ≤ p ∧ p ≤ 2 * ⌈Real.exp ((j : ℝ) / H)⌉₊ := by
  intro p hp
  rw [ramQblock, Finset.mem_filter] at hp
  obtain ⟨-, -, hlo, hhi⟩ := hp
  have hH0 : (0 : ℝ) < H := by linarith
  refine ⟨Nat.ceil_le.mpr hlo, ?_⟩
  have hexp : Real.exp (1 / H) ≤ 2 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_half_le_two
    rw [div_le_div_iff₀ hH0 (by norm_num)]
    linarith
  have hsplit : Real.exp (((j : ℝ) + 1) / H)
      = Real.exp ((j : ℝ) / H) * Real.exp (1 / H) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hce : Real.exp ((j : ℝ) / H) ≤ (⌈Real.exp ((j : ℝ) / H)⌉₊ : ℝ) := Nat.le_ceil _
  have hp2 : (p : ℝ) < ((2 * ⌈Real.exp ((j : ℝ) / H)⌉₊ : ℕ) : ℝ) := by
    have hstep : (p : ℝ) < Real.exp ((j : ℝ) / H) * 2 :=
      lt_of_lt_of_le hhi
        (le_of_eq_of_le hsplit (mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le))
    push_cast
    linarith [hce]
  exact_mod_cast hp2.le

/-- **The co-factor low gate is the window's own bottom.**  Every `m` in the co-factor
window is `≥ ⌈Xe^{−v/H}⌉` (`ramRrange` is closed at the bottom). -/
theorem ramRrange_ceil_bot_le (H : ℝ) (N X v : ℕ) :
    ∀ m ∈ ramRrange H N X v, ⌈ramRbot H X v⌉₊ ≤ m :=
  fun _ hm => Nat.ceil_le.mpr (ramRrange_bot_le hm)

/-- **M-4, pinned at the MR calibration.**  With `H ≥ 2` and `X ≥ 1`, at
`Y₁ = ⌈e^{j/H}⌉`, `X' = Xe^{−v/H}`,

  `∫_{-T}^{T} ‖Q_j^ℓ R_v‖² ≤ (2T + 20·(2Y₁)^ℓ⌈2X'⌉)·(ℓ!²·C/(Y₁^ℓ⌈X'⌉))`,

i.e. MR's window `[Y₁^ℓ X', (2Y₁)^ℓ·2X']` end to end, with no gate left for the caller
beyond the `1`-boundedness of the two data. -/
theorem multShiu_moment_pinned :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ) (N X P Q j v ℓ : ℕ) (b c : ℕ → ℂ) (T : ℝ),
      2 ≤ H → 1 ≤ X → 0 ≤ T → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∫ t in (-T)..T, ‖ramQ H P Q j c t ^ ℓ * ramR H N X P Q v b t‖ ^ 2)
        ≤ (2 * T + 20 * (((2 * ⌈Real.exp ((j : ℝ) / H)⌉₊) ^ ℓ
              * ⌈2 * ramRbot H X v⌉₊ : ℕ) : ℝ))
            * ((ℓ.factorial : ℝ) ^ 2
                * (C / ((⌈Real.exp ((j : ℝ) / H)⌉₊ ^ ℓ * ⌈ramRbot H X v⌉₊ : ℕ) : ℝ))) := by
  obtain ⟨C, hC, hmom⟩ := multShiu_moment
  refine ⟨C, hC, ?_⟩
  intro H N X P Q j v ℓ b c T hH hX hT hb hc
  have hH0 : (0 : ℝ) < H := by linarith
  have hbot : 0 < ramRbot H X v := by
    rw [ramRbot]
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    positivity
  exact hmom H N X P Q j v ⌈Real.exp ((j : ℝ) / H)⌉₊ ⌈2 * ramRbot H X v⌉₊
    ⌈ramRbot H X v⌉₊ ℓ b c T
    (Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (Real.exp_pos _)).ne')
    (Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hbot).ne')
    hT (ramQblock_subset_dyadic_block H hH P Q j) (ramRrange_ceil_bot_le H N X v)
    (ramRrange_subset_Icc_sharp H N X v _ (Nat.le_ceil _)) hb hc

end Salt.MR
