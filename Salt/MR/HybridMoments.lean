/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MultShiuBridge
import Salt.MR.HybridMVT
import Salt.MR.RamareWindows
import Salt.MR.LambdaRateTwisted

/-!
# KMT port, wave P-4: the χ-summed moments (KMT Lemmas 6.6 and 6.7)

Freeze: `docs/exploration/port-freeze-0729.md` (wave P-4); spec: READER-A's Lemma
6.6/6.7 mappings in `docs/blueprints/flags.md` ⟦THE KMT DEEP READ⟧.

Two deliverables, both obtained by **lifting the landed `q = 1` machinery to the
`χ`-twisted datum and replacing the mean-value engine** — the `q = 1` MVT
`moment_core_bound` gives way to wave P-2's `hybrid_char_mvt`.

## §1 — the shared engine: the `σ = 1` hybrid mean value (`hybrid_char_spoly_mvt`)

`hybrid_char_mvt` (P-2) is stated at `σ = 0` (`dpolyChi`, amplitude `aₙ·n^{it}`).  The
corpus's Dirichlet polynomials are `σ = 1` (`spoly`, amplitude `aₙ/n^{1+it}`).  The
landed bridge `spoly_eq_dpoly` (`MomentsA2.lean:59`) converts one to the other at the
cost of `aₙ ↦ aₙ/n` and `t ↦ −t`; the window `[-T,T]` is symmetric, so the sign is free
(`intervalIntegral.integral_comp_neg`).  The result is the drop-in `σ = 1` replacement
for `moment_core_bound`:

`∑_{χ mod q} ∫_{-T}^{T} ‖∑_{n≤N} χ̄(n)·aₙ/n^{1+it}‖² dt`
`  ≤ (2·φ(q)·T + 7·φ(q)·N/q) · ∑_{n≤N} ‖aₙ‖²/n²`.

Compare `moment_core_bound`'s `(2T + 20N)·∑‖aₙ‖²/n²`: the diagonal costs the honest
`φ(q)`, and the off-diagonal costs `φ(q)/q` of the `q = 1` grade — the `1/q` that
R-P3 flagged as **not droppable** (summing the `q = 1` bound over `φ(q)` characters
would pay `φ(q)·20N`, a factor `q` above target).

## §2 — D1: KMT Lemma 6.6, the `Q^ℓ·A` moment, `χ`-summed

The `q = 1` twin is the landed `multShiu_moment` (`MultShiuBridge.lean:664`).  Its two
seam stones — the window `multShiuCoeff_support_low/_high` and the count
`coeff_bound_factorial_blockDiv` (`‖aₙ‖ ≤ ℓ!·g(n)`, `g = blockDiv Y₁`, the Shiu
majorant `shiu_moment_sq` byte-matches KMT's `g`) — are **character-blind** and are
consumed verbatim at the twisted data.  What the twist needs is exactly one algebraic
fact: `χ̄` is completely multiplicative, so twisting commutes with the `ℓ`-fold
Dirichlet convolution.  That law is wave P-1's `pmul_mul_of_twist`
(`LambdaRateTwisted.lean:153`), and §2 instantiates it (`chiBarAf`, `pmul_pow_of_twist`,
`multShiuCoeff_chiBar`).

**The `(ℓ+1)!²` route taken: the sharper `ℓ!²`.**  KMT's printed factor is `(ℓ+1)!²`;
the corpus's count page delivers `ℓ!²` (`coeff_bound_factorial_blockDiv`: the `ℓ`-fold
ordered block-prime count is `≤ ℓ!`, and the co-factor enters through the `1`-bounded
divisor-sum majorant `oneAf`, not as an `(ℓ+1)`-st factor).  Since `ℓ! ≤ (ℓ+1)!`, the
delivered bound implies the paper's genre; `multShiuChi_moment_KMT` states the
`(ℓ+1)!²` form explicitly for a caller reading the paper.

## §3 — D2: KMT Lemma 6.7, the Ramaré decomposition, `χ`-summed

The `q = 1` twin is the landed `lemma12_meansq` (`RamareWindows.lean:671`) — MR
Lemma 12, which is the "[32, Lemma 12]" of KMT's own proof note ("almost identical
to [32, Lemma 12] … estimates the error terms by Lemma 6.2 instead of the MVT").

The whole eq-(16) identity chain (`spoly_ramare_eq16` → `spoly_ramare_split` →
`clean_term_dyadic` → `ramErr_window_decomp`) is character-blind: it is an identity of
finite sums that holds for **every** coefficient triple satisfying the block
factorisation `a_{pm} = b_m·c_p` (`p ∤ m`, `P ≤ p ≤ Q`), and the twisted triple
`(χ̄a, χ̄b, χ̄c)` satisfies it because `χ̄(pm) = χ̄(p)·χ̄(m)` (`chiBar_hcoef`).  So the
identity work is FREE; only the three error rows are re-priced at the `χ`-summed level:

| row | `q = 1` price | `χ`-summed price here |
|---|---|---|
| `ramCopTail` (the sieve remainder) | `(2T+20N)·mass` | `(2φ(q)T + 7φ(q)N/q)·mass` — §1 |
| `ramP2corr` (the `p²`-correction) | `(2T+20N)·mass` | `(2φ(q)T + 7φ(q)N/q)·mass` — §1 |
| `ramWindowErr` (the grid error) | `2T·windowMass²` | `φ(q)·2T·windowMass²` |

**The window row is the one stated deviation from the brief** (which asked for the
hybrid MVT on both error terms): its frequencies are `p·m`, running up to `QN`, not
`N`, so pricing it by any mean-value theorem inflates the frequency cap — the trap the
landed `q = 1` proof avoids by the `t`-uniform sup bound `ramWindowErr_sup_le`
(`RamareWindows.lean:616`).  That bound is also `χ`-uniform (`‖χ̄(n)·xₙ‖ ≤ ‖xₙ‖`), so
the `χ`-sum costs exactly `φ(q)` and nothing more; the hybrid MVT would cost the same
`φ(q)` on its diagonal and *more* on its off-diagonal.  `windowMassChi_le` is the
monotonicity that makes the `φ(q)`-fold honest.

Per the brief, the sieve-remainder row stays **symbolic**: its mass
`∑_{n≤N, ω(n;P,Q)=0} ‖aₙ‖²/n²` is carried in-statement (law #253), its discharge is
wave P-7's.

## The conjugation convention (the ⟦barred χ⟧ trap, N1)

KMT print `χ̄(n)` in the datum; the corpus bars it too (`lamChi`, `liouChi`,
`chiBarTwist` — see `LambdaRateTwisted.lean`'s header for the orientation argument).
**Every statement in this file is at `χ̄` = `conj ∘ χ`** (`chiBarCoeff`), matching the
consumer (P-6's `𝒰`-lift).  The map `χ ↦ χ̄` is an involution of the character group
(`MulChar.star_apply'`: `conj (χ a) = χ⁻¹ a`), so summing over all `φ(q)` characters
is invariant under it — that bijection is `sum_chiBar_reindex`, and it is what lets
`hybrid_char_mvt` (stated at unbarred `χ`) serve a barred statement at no cost.

Source pins (D5): KMT Lemmas 6.6, 6.7 (pp. 15–16); MR arXiv v4 (`1501.04585v4`)
§6 (Lemma 13), §8.2, and Lemma 12 (pp. 19–20).
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory intervalIntegral Finset

/-! ## §1 — the `χ̄`-twisted coefficient datum and the `σ = 1` hybrid mean value -/

/-- **The `χ̄`-twisted coefficient sequence** `n ↦ χ̄(n)·aₙ`.  The barred convention: see
the file header (N1).  Unlike `Salt.MR.chiTwist` (`ChiEuler.lean:74`) this carries no
phase factor — the `n^{1+it}` of `spoly` supplies it. -/
noncomputable def chiBarCoeff (q : ℕ) (χ : DirichletCharacter ℂ q) (a : ℕ → ℂ) : ℕ → ℂ :=
  fun n => (starRingEnd ℂ) (χ (n : ZMod q)) * a n

@[simp] lemma chiBarCoeff_apply (q : ℕ) (χ : DirichletCharacter ℂ q) (a : ℕ → ℂ) (n : ℕ) :
    chiBarCoeff q χ a n = (starRingEnd ℂ) (χ (n : ZMod q)) * a n := rfl

/-- `‖χ̄(n)‖ ≤ 1`. -/
lemma norm_conj_chi_le_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖(starRingEnd ℂ) (χ (n : ZMod q))‖ ≤ 1 := by
  rw [RCLike.norm_conj]
  exact DirichletCharacter.norm_le_one χ _

/-- The twist does not increase norms: `‖χ̄(n)·aₙ‖ ≤ ‖aₙ‖`. -/
lemma norm_chiBarCoeff_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a : ℕ → ℂ)
    (n : ℕ) : ‖chiBarCoeff q χ a n‖ ≤ ‖a n‖ := by
  rw [chiBarCoeff_apply, norm_mul]
  calc ‖(starRingEnd ℂ) (χ (n : ZMod q))‖ * ‖a n‖ ≤ 1 * ‖a n‖ :=
        mul_le_mul_of_nonneg_right (norm_conj_chi_le_one χ n) (norm_nonneg _)
    _ = ‖a n‖ := one_mul _

/-- The twist preserves `1`-boundedness. -/
lemma norm_chiBarCoeff_le_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) (n : ℕ) : ‖chiBarCoeff q χ a n‖ ≤ 1 :=
  (norm_chiBarCoeff_le χ a n).trans (ha n)

/-- **The `χ ↦ χ̄` reindex.**  `conj ∘ χ = χ⁻¹` (`MulChar.star_apply'`) and inversion is an
involution of the character group, so any sum over *all* `φ(q)` characters is invariant
under barring.  This is what lets the unbarred `hybrid_char_mvt` serve a barred
statement. -/
lemma sum_chiBar_reindex {q : ℕ} [NeZero q] {M : Type*} [AddCommMonoid M]
    (F : DirichletCharacter ℂ q → M) :
    (∑ χ : DirichletCharacter ℂ q, F χ⁻¹) = ∑ χ : DirichletCharacter ℂ q, F χ :=
  Fintype.sum_equiv ⟨fun χ => χ⁻¹, fun χ => χ⁻¹, fun χ => by simp, fun χ => by simp⟩ _ _
    (fun _ => rfl)

/-- `χ̄(n) = χ⁻¹(n)` pointwise (`MulChar.star_apply'`), hence the twisted coefficients of
`χ` are the plainly-twisted coefficients of `χ⁻¹`. -/
lemma chiBarCoeff_eq_inv (q : ℕ) (χ : DirichletCharacter ℂ q) (a : ℕ → ℂ) (n : ℕ) :
    chiBarCoeff q χ a n = χ⁻¹ (n : ZMod q) * a n := by
  rw [chiBarCoeff_apply, starRingEnd_apply, MulChar.star_apply']

/-- **The `σ = 1` ↔ `σ = 0` bridge, twisted.**  `∑_{n≤N} χ̄(n)aₙ/n^{1+it}` is the
`σ = 0` polynomial `dpolyChi` of `χ⁻¹` at coefficients `aₙ/n` and height `−t`.  The two
landed ingredients: `spoly_eq_dpoly` (the untwisted bridge) and `chiBarCoeff_eq_inv`. -/
lemma spoly_chiBarCoeff_eq_dpolyChi (q : ℕ) (χ : DirichletCharacter ℂ q) (N : ℕ)
    (a : ℕ → ℂ) (t : ℝ) :
    spoly N (chiBarCoeff q χ a) t
      = dpolyChi q (Finset.Icc 1 N) (fun n => a n / (n : ℂ)) χ⁻¹ (-t) := by
  rw [spoly_eq_dpoly, dpoly, dpolyChi]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [chiBarCoeff_eq_inv]
  ring

/-- **§1 — THE `σ = 1` HYBRID MEAN VALUE (the drop-in replacement for
`moment_core_bound`).**  For any coefficients `a` and any `N`,

`∑_{χ mod q} ∫_{-T}^{T} ‖∑_{n≤N} χ̄(n)·aₙ/n^{1+it}‖² dt`
`  ≤ (2·φ(q)·T + 7·φ(q)·N/q) · ∑_{n≤N} ‖aₙ‖²/n²`.

The `q = 1` grade is `(2T + 20N)·∑‖aₙ‖²/n²` (`moment_core_bound`); summing *that* over
the `φ(q)` characters would pay `φ(q)·20N`.  The `1/q` here is bought by wave P-2's
per-class separation and is not droppable (R-P3). -/
theorem hybrid_char_spoly_mvt (q : ℕ) [NeZero q] (N : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
      ≤ (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
  -- step 1: rewrite each χ-piece as the σ = 0 polynomial of χ⁻¹ at height −t
  have hpiece : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-T)..T, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        = ∫ t in (-T)..T, ‖dpolyChi q (Finset.Icc 1 N) (fun n => a n / (n : ℂ)) χ⁻¹ t‖ ^ 2 := by
    intro χ
    have hcongr : (∫ t in (-T)..T, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        = ∫ t in (-T)..T,
            ‖dpolyChi q (Finset.Icc 1 N) (fun n => a n / (n : ℂ)) χ⁻¹ (-t)‖ ^ 2 :=
      intervalIntegral.integral_congr
        (fun t _ => by rw [spoly_chiBarCoeff_eq_dpolyChi])
    rw [hcongr, intervalIntegral.integral_comp_neg
      (fun t => ‖dpolyChi q (Finset.Icc 1 N) (fun n => a n / (n : ℂ)) χ⁻¹ t‖ ^ 2)]
    norm_num
  rw [Finset.sum_congr rfl (fun χ _ => hpiece χ)]
  -- step 2: the χ ↦ χ⁻¹ reindex, then P-2's hybrid MVT
  rw [sum_chiBar_reindex (q := q)
    (fun χ => ∫ t in (-T)..T, ‖dpolyChi q (Finset.Icc 1 N) (fun n => a n / (n : ℂ)) χ t‖ ^ 2)]
  refine (hybrid_char_mvt_full q (Finset.Icc 1 N) (Finset.Subset.refl _)
    (fun n => a n / (n : ℂ)) hT).trans ?_
  refine mul_le_mul_of_nonneg_left (le_of_eq (Finset.sum_congr rfl (fun n _ => ?_))) ?_
  · rw [norm_div, Complex.norm_natCast, div_pow]
  · have h1 : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T := by positivity
    have h2 : (0 : ℝ) ≤ 7 * (q.totient : ℝ) * (N : ℝ) / q := by positivity
    linarith

/-! ## §2 — D1: KMT Lemma 6.6, the `Q^ℓ·A` moment, `χ`-summed -/

/-- The `χ̄`-twist as an `ArithmeticFunction` (value `0` at `0`, forced: at `q = 1` the
character does *not* vanish at `0`, since `(0 : ZMod 1) = 1`). -/
noncomputable def chiBarAf (q : ℕ) (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (starRingEnd ℂ) (χ (n : ZMod q)), by simp⟩

@[simp] lemma chiBarAf_apply (q : ℕ) (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (chiBarAf q χ) n = if n = 0 then 0 else (starRingEnd ℂ) (χ (n : ZMod q)) := rfl

lemma chiBarAf_apply_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : n ≠ 0) :
    (chiBarAf q χ) n = (starRingEnd ℂ) (χ (n : ZMod q)) := by
  rw [chiBarAf_apply, if_neg hn]

lemma chiBarAf_one (q : ℕ) (χ : DirichletCharacter ℂ q) : (chiBarAf q χ) 1 = 1 := by
  rw [chiBarAf_apply_ne_zero χ one_ne_zero, Nat.cast_one, map_one, map_one]

/-- **Complete multiplicativity of the `χ̄`-twist on nonzero arguments** — the hypothesis
of wave P-1's `pmul_mul_of_twist`. -/
lemma chiBarAf_mul (q : ℕ) (χ : DirichletCharacter ℂ q) :
    ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → (chiBarAf q χ) (a * b)
      = (chiBarAf q χ) a * (chiBarAf q χ) b := by
  intro a b ha hb
  rw [chiBarAf_apply_ne_zero χ (Nat.mul_ne_zero ha hb), chiBarAf_apply_ne_zero χ ha,
    chiBarAf_apply_ne_zero χ hb, Nat.cast_mul, map_mul, map_mul]

/-- **The `ℓ`-fold twist law.**  `(f·h)^ℓ = (f^ℓ)·h` for the completely multiplicative
`h = χ̄` (`pmul` = pointwise product, `^` = the `ℓ`-fold Dirichlet convolution).  Induction
over `pmul_mul_of_twist`; the base case is `h 1 = 1`. -/
lemma pmul_pow_of_chiBarAf (q : ℕ) (χ : DirichletCharacter ℂ q) (f : ArithmeticFunction ℂ) :
    ∀ ℓ : ℕ, (f.pmul (chiBarAf q χ)) ^ ℓ = (f ^ ℓ).pmul (chiBarAf q χ) := by
  intro ℓ
  induction ℓ with
  | zero =>
      rw [pow_zero, pow_zero]
      ext n
      rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.one_apply]
      by_cases hn : n = 1
      · rw [if_pos hn, one_mul, hn, chiBarAf_one]
      · rw [if_neg hn, zero_mul]
  | succ ℓ ih =>
      rw [pow_succ, pow_succ, ih, ← pmul_mul_of_twist _ _ _ (chiBarAf_mul q χ)]

/-- The prime-block coefficients of the twisted datum are the twist of the coefficients. -/
lemma ramQaf_chiBar (q : ℕ) (χ : DirichletCharacter ℂ q) (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) :
    ramQaf H P Q j (chiBarCoeff q χ c) = (ramQaf H P Q j c).pmul (chiBarAf q χ) := by
  ext n
  rw [ramQaf_apply, ArithmeticFunction.pmul_apply, ramQaf_apply, ramQcoeff, ramQcoeff]
  by_cases hn : n = 0
  · subst hn
    rw [if_neg (zero_notMem_ramQblock H P Q j), chiBarAf_apply, if_pos rfl, mul_zero]
  · rw [chiBarAf_apply_ne_zero χ hn]
    by_cases hmem : n ∈ ramQblock H P Q j
    · rw [if_pos hmem, if_pos hmem, chiBarCoeff_apply]; ring
    · rw [if_neg hmem, if_neg hmem, zero_mul]

/-- The Ramaré co-factor coefficients of the twisted datum are the twist of the
coefficients (the `1/(ω(m)+1)` weight is character-blind). -/
lemma ramRaf_chiBar (q : ℕ) (χ : DirichletCharacter ℂ q) (H : ℝ) (N X P Q v : ℕ)
    (b : ℕ → ℂ) :
    ramRaf H N X P Q v (chiBarCoeff q χ b) = (ramRaf H N X P Q v b).pmul (chiBarAf q χ) := by
  ext n
  rw [ramRaf_apply, ArithmeticFunction.pmul_apply, ramRaf_apply, ramRcoeff, ramRcoeff]
  by_cases hn : n = 0
  · subst hn
    have h0 : (0 : ℕ) ∉ ramRrange H N X v := by
      intro h; have := ramRrange_one_le h; omega
    rw [if_neg h0, chiBarAf_apply, if_pos rfl, mul_zero]
  · rw [chiBarAf_apply_ne_zero χ hn]
    by_cases hmem : n ∈ ramRrange H N X v
    · rw [if_pos hmem, if_pos hmem, chiBarCoeff_apply]; ring
    · rw [if_neg hmem, if_neg hmem, zero_mul]

/-- **The MULT-SHIU coefficient commutes with the twist.**  `aₙ(χ̄b, χ̄c) = χ̄(n)·aₙ(b,c)`:
the `ℓ`-fold prime convolution against the co-factor, twisted, is the twist of the
`ℓ`-fold — the *one* algebraic fact the `χ`-lift of Lemma 6.6 needs. -/
theorem multShiuCoeff_chiBar (q : ℕ) (χ : DirichletCharacter ℂ q) (H : ℝ)
    (N X P Q j v : ℕ) (b c : ℕ → ℂ) (ℓ : ℕ) :
    multShiuCoeff H N X P Q j v (chiBarCoeff q χ b) (chiBarCoeff q χ c) ℓ
      = (multShiuCoeff H N X P Q j v b c ℓ).pmul (chiBarAf q χ) := by
  rw [multShiuCoeff, multShiuCoeff, ramQaf_chiBar, ramRaf_chiBar,
    pmul_pow_of_chiBarAf q χ (ramQaf H P Q j c) ℓ,
    ← pmul_mul_of_twist _ _ _ (chiBarAf_mul q χ)]

/-- The twisted `ℓ`-fold, read as a `σ = 1` polynomial with `χ̄`-twisted coefficients:
`Q_j(χ̄)^ℓ·R_v(χ̄) = ∑_{n ≤ Mq^ℓ Mr} χ̄(n)·aₙ/n^{1+it}` with `a = multShiuCoeff`.  This is
the landed `ramQ_pow_mul_ramR_eq_spoly` (M-2) at twisted data, plus
`multShiuCoeff_chiBar`. -/
theorem ramQ_pow_mul_ramR_chiBar_eq_spoly (q : ℕ) (χ : DirichletCharacter ℂ q) (H : ℝ)
    (N X P Q j v Mq Mr : ℕ) (b c : ℕ → ℂ)
    (hMq : ramQblock H P Q j ⊆ Finset.Icc 1 Mq)
    (hMr : ramRrange H N X v ⊆ Finset.Icc 1 Mr) (ℓ : ℕ) (t : ℝ) :
    ramQ H P Q j (chiBarCoeff q χ c) t ^ ℓ * ramR H N X P Q v (chiBarCoeff q χ b) t
      = spoly (Mq ^ ℓ * Mr)
          (chiBarCoeff q χ (⇑(multShiuCoeff H N X P Q j v b c ℓ))) t := by
  rw [ramQ_pow_mul_ramR_eq_spoly H N X P Q j v Mq Mr (chiBarCoeff q χ b)
    (chiBarCoeff q χ c) hMq hMr ℓ t, spoly, spoly]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [multShiuCoeff_chiBar, ArithmeticFunction.pmul_apply,
    chiBarAf_apply_ne_zero χ (by omega : n ≠ 0), chiBarCoeff_apply]
  ring

/-- **D1 — KMT LEMMA 6.6, THE `Q^ℓ·A` MOMENT, `χ`-SUMMED.**  With the block gate
`Y₁ ≤ p ≤ 2Y₁` on the prime fibre, `X₀ ≤ m ≤ Mr` on the co-factor window, and
`1`-bounded data,

`∑_{χ mod q} ∫_{-T}^{T} ‖Q_j(χ̄, 1+it)^ℓ · R_v(χ̄, 1+it)‖² dt`
`  ≤ (2·φ(q)·T + 7·φ(q)·(2Y₁)^ℓ·Mr/q) · (ℓ!² · C/(Y₁^ℓ·X₀))`,

`C` the absolute Shiu constant.  This is the landed `multShiu_moment` with its mean-value
engine swapped: `lemma13_moment` (the `q = 1` MVT) → `hybrid_char_spoly_mvt` (P-2's
hybrid).  The two seam stones are consumed verbatim (they are character-blind): the
window `multShiuCoeff_support_low`, the count `coeff_bound_factorial_blockDiv`
(`‖aₙ‖ ≤ ℓ!·blockDiv Y₁ n`) — and the mass page is the landed dyadic Shiu sum
`blockDiv_sq_div_sq_sum_le`, whose `g` byte-matches KMT's (READER-A §7).

`ℓ!²` is the *sharp* form of KMT's `(ℓ+1)!²` — see `multShiuChi_moment_KMT`. -/
theorem multShiuChi_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (H : ℝ) (N X P Q j v Y₁ Mr X₀ ℓ : ℕ)
      (b c : ℕ → ℂ) (T : ℝ),
      1 ≤ Y₁ → 1 ≤ X₀ → 0 ≤ T →
      (∀ p ∈ ramQblock H P Q j, Y₁ ≤ p ∧ p ≤ 2 * Y₁) →
      (∀ m ∈ ramRrange H N X v, X₀ ≤ m) →
      ramRrange H N X v ⊆ Finset.Icc 1 Mr →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
          ‖ramQ H P Q j (chiBarCoeff q χ c) t ^ ℓ
            * ramR H N X P Q v (chiBarCoeff q χ b) t‖ ^ 2)
        ≤ (2 * (q.totient : ℝ) * T
              + 7 * (q.totient : ℝ) * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ) / q)
            * ((ℓ.factorial : ℝ) ^ 2 * (C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ))) := by
  obtain ⟨C, hC, hShiuSum⟩ := blockDiv_sq_div_sq_sum_le
  refine ⟨3 * C, by positivity, ?_⟩
  intro q _ H N X P Q j v Y₁ Mr X₀ ℓ b c T hY₁ hX₀ hT hblock hRlow hMr hb hc
  set M := (2 * Y₁) ^ ℓ * Mr with hMdef
  set L := Y₁ ^ ℓ * X₀ with hLdef
  have hLpos : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (pow_ne_zero ℓ (by omega)) (by omega))
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  -- the prime fibre sits in `[1, 2Y₁]`
  have hMq : ramQblock H P Q j ⊆ Finset.Icc 1 (2 * Y₁) := by
    intro p hp
    obtain ⟨hlo, hhi⟩ := hblock p hp
    exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩
  -- step 1: each integrand is a `σ = 1` polynomial with `χ̄`-twisted coefficients
  have hint : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-T)..T, ‖ramQ H P Q j (chiBarCoeff q χ c) t ^ ℓ
          * ramR H N X P Q v (chiBarCoeff q χ b) t‖ ^ 2)
        = ∫ t in (-T)..T,
            ‖spoly M (chiBarCoeff q χ (⇑(multShiuCoeff H N X P Q j v b c ℓ))) t‖ ^ 2 := by
    intro χ
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [ramQ_pow_mul_ramR_chiBar_eq_spoly q χ H N X P Q j v (2 * Y₁) Mr b c hMq hMr ℓ t]
  rw [Finset.sum_congr rfl (fun χ _ => hint χ)]
  -- step 2: the hybrid mean value
  refine (hybrid_char_spoly_mvt q M (⇑(multShiuCoeff H N X P Q j v b c ℓ)) hT).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · -- step 3: the coefficient mass, the count page × the dyadic Shiu sum
    have hsupp := multShiuCoeff_support_low H N X P Q j v Y₁ X₀ b c ℓ
      (fun p hp => (hblock p hp).1) hRlow
    have hcoeff := coeff_bound_factorial_blockDiv H N X P Q j v Y₁ hb hc hblock ℓ
    have hcut : ∑ n ∈ Finset.Icc 1 M,
          ‖(multShiuCoeff H N X P Q j v b c ℓ) n‖ ^ 2 / (n : ℝ) ^ 2
        = ∑ n ∈ Finset.Icc L M,
            ‖(multShiuCoeff H N X P Q j v b c ℓ) n‖ ^ 2 / (n : ℝ) ^ 2 := by
      refine (Finset.sum_subset (fun n hn => ?_) (fun x hx hxni => ?_)).symm
      · rw [Finset.mem_Icc] at hn ⊢; omega
      · have hxL : x < L := by
          rw [Finset.mem_Icc] at hx
          by_contra h
          exact hxni (Finset.mem_Icc.mpr ⟨not_lt.mp h, hx.2⟩)
        rw [hsupp x hxL, norm_zero]; simp
    rw [hcut]
    calc ∑ n ∈ Finset.Icc L M,
          ‖(multShiuCoeff H N X P Q j v b c ℓ) n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Icc L M,
            ((ℓ.factorial : ℝ) ^ 2 * (blockDiv Y₁ n : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          have h1 : ‖(multShiuCoeff H N X P Q j v b c ℓ) n‖ ^ 2
              ≤ (ℓ.factorial : ℝ) ^ 2 * (blockDiv Y₁ n : ℝ) ^ 2 := by
            nlinarith [hcoeff n, norm_nonneg ((multShiuCoeff H N X P Q j v b c ℓ) n),
              mul_nonneg (Nat.cast_nonneg (α := ℝ) ℓ.factorial)
                (Nat.cast_nonneg (α := ℝ) (blockDiv Y₁ n))]
          gcongr
      _ = (ℓ.factorial : ℝ) ^ 2
            * ∑ n ∈ Finset.Icc L M, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
      _ ≤ (ℓ.factorial : ℝ) ^ 2 * (3 * C / (L : ℝ)) :=
          mul_le_mul_of_nonneg_left (hShiuSum Y₁ L M hY₁ hLpos) (by positivity)
  · have h1 : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T := by positivity
    have h2 : (0 : ℝ) ≤ 7 * (q.totient : ℝ) * ((M : ℕ) : ℝ) / q := by positivity
    linarith

/-- **D1, the paper's constant.**  KMT print `(ℓ+1)!²`; `multShiuChi_moment` delivers the
sharper `ℓ!²`.  This is the `(ℓ+1)!²` restatement for a caller reading the paper — a pure
domination step (`ℓ! ≤ (ℓ+1)!`), no new content. -/
theorem multShiuChi_moment_KMT :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (H : ℝ) (N X P Q j v Y₁ Mr X₀ ℓ : ℕ)
      (b c : ℕ → ℂ) (T : ℝ),
      1 ≤ Y₁ → 1 ≤ X₀ → 0 ≤ T →
      (∀ p ∈ ramQblock H P Q j, Y₁ ≤ p ∧ p ≤ 2 * Y₁) →
      (∀ m ∈ ramRrange H N X v, X₀ ≤ m) →
      ramRrange H N X v ⊆ Finset.Icc 1 Mr →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
          ‖ramQ H P Q j (chiBarCoeff q χ c) t ^ ℓ
            * ramR H N X P Q v (chiBarCoeff q χ b) t‖ ^ 2)
        ≤ (2 * (q.totient : ℝ) * T
              + 7 * (q.totient : ℝ) * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ) / q)
            * (((ℓ + 1).factorial : ℝ) ^ 2 * (C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ))) := by
  obtain ⟨C, hC, hmom⟩ := multShiuChi_moment
  refine ⟨C, hC, ?_⟩
  intro q _ H N X P Q j v Y₁ Mr X₀ ℓ b c T hY₁ hX₀ hT hblock hRlow hMr hb hc
  refine (hmom q H N X P Q j v Y₁ Mr X₀ ℓ b c T hY₁ hX₀ hT hblock hRlow hMr hb hc).trans ?_
  have hLpos : 1 ≤ Y₁ ^ ℓ * X₀ := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (pow_ne_zero ℓ (by omega)) (by omega))
  have hLr : (0 : ℝ) < ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ) := by exact_mod_cast hLpos
  have hfac : (ℓ.factorial : ℝ) ^ 2 ≤ ((ℓ + 1).factorial : ℝ) ^ 2 := by
    have h : (ℓ.factorial : ℝ) ≤ ((ℓ + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_succ ℓ)
    nlinarith [Nat.cast_nonneg (α := ℝ) ℓ.factorial]
  have hpre : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T
      + 7 * (q.totient : ℝ) * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ) / q := by
    have h1 : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T := by positivity
    have h2 : (0 : ℝ) ≤ 7 * (q.totient : ℝ) * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ) / q := by
      positivity
    linarith
  refine mul_le_mul_of_nonneg_left ?_ hpre
  have hCL : (0 : ℝ) ≤ C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_right hfac hCL

/-- **D1, the discrete `(17)`-form: the exact `t = 0` Plancherel identity.**  At a single
height the `χ`-sum is not an inequality at all — `char_plancherel` (P-2's fold) gives
equality: `∑_{χ mod q} ‖P(χ̄, 1)‖² = φ(q)·∑_{b unit} ‖∑_{n ≡ b} aₙ/n‖²`.  The cheap
variant KMT use for the `T = 1` row; the `∑_χ`-bound at `T = 1` is
`multShiuChi_moment_T1`. -/
theorem spoly_chiBar_plancherel_at_zero (q : ℕ) [NeZero q] (N : ℕ) (a : ℕ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖spoly N (chiBarCoeff q χ a) 0‖ ^ 2)
      = (q.totient : ℝ) * ∑ b : ZMod q,
          (if IsUnit b then
            ‖dpolyS (classSet q (Finset.Icc 1 N) b) (fun n => a n / (n : ℂ)) 0‖ ^ 2 else 0) := by
  have hpiece : ∀ χ : DirichletCharacter ℂ q,
      ‖spoly N (chiBarCoeff q χ a) 0‖ ^ 2
        = ‖dpolyChi q (Finset.Icc 1 N) (fun n => a n / (n : ℂ)) χ⁻¹ 0‖ ^ 2 := by
    intro χ
    rw [spoly_chiBarCoeff_eq_dpolyChi]
    norm_num
  rw [Finset.sum_congr rfl (fun χ _ => hpiece χ),
    sum_chiBar_reindex (q := q)
      (fun χ => ‖dpolyChi q (Finset.Icc 1 N) (fun n => a n / (n : ℂ)) χ 0‖ ^ 2)]
  exact sum_chi_meanSq_pointwise q (Finset.Icc 1 N) (fun n => a n / (n : ℂ)) 0

/-- **D1 at `T = 1`** — the short-window row of Lemma 6.6, the `T = 1` instance of
`multShiuChi_moment`. -/
theorem multShiuChi_moment_T1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (H : ℝ) (N X P Q j v Y₁ Mr X₀ ℓ : ℕ)
      (b c : ℕ → ℂ),
      1 ≤ Y₁ → 1 ≤ X₀ →
      (∀ p ∈ ramQblock H P Q j, Y₁ ≤ p ∧ p ≤ 2 * Y₁) →
      (∀ m ∈ ramRrange H N X v, X₀ ≤ m) →
      ramRrange H N X v ⊆ Finset.Icc 1 Mr →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∑ χ : DirichletCharacter ℂ q, ∫ t in (-1 : ℝ)..1,
          ‖ramQ H P Q j (chiBarCoeff q χ c) t ^ ℓ
            * ramR H N X P Q v (chiBarCoeff q χ b) t‖ ^ 2)
        ≤ (2 * (q.totient : ℝ)
              + 7 * (q.totient : ℝ) * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ) / q)
            * ((ℓ.factorial : ℝ) ^ 2 * (C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ))) := by
  obtain ⟨C, hC, hmom⟩ := multShiuChi_moment
  refine ⟨C, hC, ?_⟩
  intro q _ H N X P Q j v Y₁ Mr X₀ ℓ b c hY₁ hX₀ hblock hRlow hMr hb hc
  have h := hmom q H N X P Q j v Y₁ Mr X₀ ℓ b c 1 hY₁ hX₀ zero_le_one hblock hRlow hMr hb hc
  calc (∑ χ : DirichletCharacter ℂ q, ∫ t in (-1 : ℝ)..1,
        ‖ramQ H P Q j (chiBarCoeff q χ c) t ^ ℓ
          * ramR H N X P Q v (chiBarCoeff q χ b) t‖ ^ 2)
      ≤ (2 * (q.totient : ℝ) * 1
            + 7 * (q.totient : ℝ) * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ) / q)
          * ((ℓ.factorial : ℝ) ^ 2 * (C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ))) := h
    _ = (2 * (q.totient : ℝ)
            + 7 * (q.totient : ℝ) * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ) / q)
          * ((ℓ.factorial : ℝ) ^ 2 * (C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ))) := by ring

/-! ## §3 — D2: KMT Lemma 6.7, the Ramaré decomposition, `χ`-summed -/

/-- The number of Dirichlet characters mod `q` is `φ(q)` (mathlib's
`card_eq_totient_of_hasEnoughRootsOfUnity`, restated at `Fintype.card`).  Needed for the
one error row that is priced by a `χ`-uniform sup rather than a mean value. -/
lemma card_dirichletChar (q : ℕ) [NeZero q] :
    Fintype.card (DirichletCharacter ℂ q) = q.totient := by
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- `∑_{χ mod q} C = φ(q)·C` for a constant `C`. -/
lemma sum_const_dirichletChar (q : ℕ) [NeZero q] (C : ℝ) :
    (∑ _χ : DirichletCharacter ℂ q, C) = (q.totient : ℝ) * C := by
  rw [Finset.sum_const, Finset.card_univ, card_dirichletChar q, nsmul_eq_mul]

/-- **Complete multiplicativity of `χ̄` on `ℕ`** — unconditional (no nonzero guard: the
character is a monoid hom on `ZMod q` and `((ab : ℕ) : ZMod q) = a·b`). -/
lemma conj_chi_natCast_mul (q : ℕ) (χ : DirichletCharacter ℂ q) (m n : ℕ) :
    (starRingEnd ℂ) (χ ((m * n : ℕ) : ZMod q))
      = (starRingEnd ℂ) (χ (m : ZMod q)) * (starRingEnd ℂ) (χ (n : ZMod q)) := by
  rw [Nat.cast_mul, map_mul, map_mul]

/-- **The block factorisation survives the twist.**  `a_{pm} = b_m·c_p` on the coprime block
gives `χ̄(pm)a_{pm} = (χ̄(m)b_m)·(χ̄(p)c_p)` — the *only* hypothesis of the landed `q = 1`
Lemma 12, so the entire eq-(16) identity chain applies at the twisted data verbatim. -/
theorem chiBar_hcoef (q : ℕ) (χ : DirichletCharacter ℂ q) {P Q : ℕ} {a b c : ℕ → ℂ}
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p) :
    ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m →
      chiBarCoeff q χ a (p * m) = chiBarCoeff q χ b m * chiBarCoeff q χ c p := by
  intro p m hp hPp hpQ hpm
  rw [chiBarCoeff_apply, chiBarCoeff_apply, chiBarCoeff_apply,
    conj_chi_natCast_mul q χ p m, hcoef p m hp hPp hpQ hpm]
  ring

/-- **The window `ℓ¹`-mass is `χ`-uniform.**  `windowMass` is monotone in the coefficient
norms and `‖χ̄(n)·xₙ‖ ≤ ‖xₙ‖`, so twisting can only shrink it.  This is what makes the
`φ(q)`-fold price of the window row honest (see the file header's deviation note). -/
theorem windowMassChi_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (H : ℝ)
    (N X P Q : ℕ) (b c : ℕ → ℂ) :
    windowMass H N X P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c)
      ≤ windowMass H N X P Q b c := by
  rw [windowMass, windowMass]
  refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun p _ => ?_))
  have hcp : ‖chiBarCoeff q χ c p‖ / (p : ℝ) ≤ ‖c p‖ / (p : ℝ) := by
    have h := norm_chiBarCoeff_le χ c p
    gcongr
  have hmass : (∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
          (fun m => p * m ∈ Finset.Icc 1 N), ‖chiBarCoeff q χ b m‖ / (m : ℝ))
        + ∑ m ∈ ramRrange H N X j, ‖chiBarCoeff q χ b m‖ / (m : ℝ)
      ≤ (∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
          (fun m => p * m ∈ Finset.Icc 1 N), ‖b m‖ / (m : ℝ))
        + ∑ m ∈ ramRrange H N X j, ‖b m‖ / (m : ℝ) := by
    refine add_le_add (Finset.sum_le_sum (fun m _ => ?_)) (Finset.sum_le_sum (fun m _ => ?_))
    · have h := norm_chiBarCoeff_le χ b m
      gcongr
    · have h := norm_chiBarCoeff_le χ b m
      gcongr
  have hnn1 : (0 : ℝ) ≤ ‖chiBarCoeff q χ c p‖ / (p : ℝ) := by positivity
  have hnn2 : (0 : ℝ) ≤ (∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
          (fun m => p * m ∈ Finset.Icc 1 N), ‖b m‖ / (m : ℝ))
        + ∑ m ∈ ramRrange H N X j, ‖b m‖ / (m : ℝ) :=
    add_nonneg (Finset.sum_nonneg (fun m _ => by positivity))
      (Finset.sum_nonneg (fun m _ => by positivity))
  exact mul_le_mul hcp hmass
    (add_nonneg (Finset.sum_nonneg (fun m _ => by positivity))
      (Finset.sum_nonneg (fun m _ => by positivity))) (by positivity)

/-- **The `p²`-correction coefficient commutes with the twist.**  On the fibre `pm = n` the
two twisted factors recombine: `χ̄(m)·χ̄(p) = χ̄(n)`, and the Ramaré weight and the
`1/(ω(m)+1)` are real/character-blind. -/
theorem ramP2coeff_chiBar (q : ℕ) (χ : DirichletCharacter ℂ q) (N P Q : ℕ)
    (a b c : ℕ → ℂ) (n : ℕ) :
    ramP2coeff N P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b) (chiBarCoeff q χ c) n
      = chiBarCoeff q χ (ramP2coeff N P Q a b c) n := by
  rw [chiBarCoeff_apply, ramP2coeff, ramP2coeff, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  rw [Finset.mem_filter] at hσ
  rw [← hσ.2, chiBarCoeff_apply, chiBarCoeff_apply, chiBarCoeff_apply,
    conj_chi_natCast_mul q χ σ.1 σ.2]
  ring

/-- The `p²`-correction row of the twisted error, as a `σ = 1` polynomial with
`χ̄`-twisted coefficients (frequencies in `[1,N]`, so the hybrid mean value applies at
the *un-inflated* cap). -/
lemma ramP2corr_chiBar_eq_spoly (q : ℕ) (χ : DirichletCharacter ℂ q) (N P Q : ℕ)
    (a b c : ℕ → ℂ) (t : ℝ) :
    ramP2corr N P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b) (chiBarCoeff q χ c) t
      = spoly N (chiBarCoeff q χ (ramP2coeff N P Q a b c)) t := by
  rw [ramP2corr_eq_spoly]
  congr 1
  funext n
  exact ramP2coeff_chiBar q χ N P Q a b c n

/-- The coprime-tail (sieve-remainder) row of the twisted error, as a `σ = 1` polynomial
with `χ̄`-twisted coefficients (the `ω(n;P,Q) = 0` mask is character-blind). -/
lemma ramCopTail_chiBar_eq_spoly (q : ℕ) (χ : DirichletCharacter ℂ q) (N P Q : ℕ)
    (a : ℕ → ℂ) (t : ℝ) :
    ramCopTail N P Q (chiBarCoeff q χ a) t
      = spoly N (chiBarCoeff q χ (fun n => if blockOmega P Q n = 0 then a n else 0)) t := by
  rw [ramCopTail_eq_spoly]
  congr 1
  funext n
  rw [chiBarCoeff_apply, chiBarCoeff_apply]
  by_cases h : blockOmega P Q n = 0 <;> simp [h]

/-- **The `χ`-summed error moment (the two error terms of KMT Lemma 6.7).**  The exact
error split `ramErr = window + p²-correction + coprime-tail` (`ramErr_moment_split`, an
identity of finite sums, hence character-blind) priced at the `χ`-summed level:

* the **grid/approximation error** rows — the `p²`-correction and the coprime tail — by
  wave P-2's hybrid mean value `hybrid_char_spoly_mvt` at the grade
  `(2φ(q)T + 7φ(q)N/q)`, i.e. the `1/q` saving on the off-diagonal;
* the **window** row by the `χ`-uniform sup `ramWindowErr_sup_le`, costing exactly
  `φ(q)·2T·windowMass²` (its frequencies run to `QN`, not `N` — see the header).

The coprime-tail mass `∑_{n≤N, ω(n;P,Q)=0} ‖aₙ‖²/n²` is the **sieve remainder** and stays
symbolic per the freeze (its discharge is wave P-7's). -/
theorem ramErr_meanSq_all_chi (q : ℕ) [NeZero q] (H : ℝ) (hH : 0 < H) (N X P Q : ℕ)
    (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (T : ℝ) (hT : 0 ≤ T) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
        ‖ramErr H N X P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
          (chiBarCoeff q χ c) t‖ ^ 2)
      ≤ 3 * ((q.totient : ℝ) * (2 * T * (windowMass H N X P Q b c) ^ 2)
          + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
              * (∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
          + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
              * (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
                  ‖a n‖ ^ 2 / (n : ℝ) ^ 2)) := by
  classical
  set W : DirichletCharacter ℂ q → ℝ := fun χ => ∫ t in (-T)..T,
    ‖ramWindowErr H N X P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) t‖ ^ 2 with hWdef
  set Cr : DirichletCharacter ℂ q → ℝ := fun χ => ∫ t in (-T)..T,
    ‖ramP2corr N P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
      (chiBarCoeff q χ c) t‖ ^ 2 with hCdef
  set D : DirichletCharacter ℂ q → ℝ := fun χ => ∫ t in (-T)..T,
    ‖ramCopTail N P Q (chiBarCoeff q χ a) t‖ ^ 2 with hDdef
  -- the per-χ exact split (the identity chain is character-blind)
  have hrow : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-T)..T, ‖ramErr H N X P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
          (chiBarCoeff q χ c) t‖ ^ 2) ≤ 3 * (W χ + Cr χ + D χ) := fun χ =>
    ramErr_moment_split H hH N X P Q hP _ _ _ (chiBar_hcoef q χ hcoef) T hT
  -- the window row: the χ-uniform sup, φ(q)-fold
  have hWbound : (∑ χ : DirichletCharacter ℂ q, W χ)
      ≤ (q.totient : ℝ) * (2 * T * (windowMass H N X P Q b c) ^ 2) := by
    rw [← sum_const_dirichletChar q (2 * T * (windowMass H N X P Q b c) ^ 2)]
    refine Finset.sum_le_sum (fun χ _ => ?_)
    refine (ramWindowErr_moment_triv H N X P Q _ _ T hT).trans ?_
    have hm0 : 0 ≤ windowMass H N X P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) :=
      Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun p _ => by positivity))
    have hle := windowMassChi_le q χ H N X P Q b c
    have hTnn : (0 : ℝ) ≤ 2 * T := by linarith
    have hsq : windowMass H N X P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) ^ 2
        ≤ windowMass H N X P Q b c ^ 2 := by gcongr
    exact mul_le_mul_of_nonneg_left hsq hTnn
  -- the p²-correction row: the hybrid mean value at the un-inflated cap
  have hCbound : (∑ χ : DirichletCharacter ℂ q, Cr χ)
      ≤ (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
          * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 := by
    have hpiece : ∀ χ : DirichletCharacter ℂ q,
        Cr χ = ∫ t in (-T)..T,
          ‖spoly N (chiBarCoeff q χ (ramP2coeff N P Q a b c)) t‖ ^ 2 := by
      intro χ
      rw [hCdef]
      exact intervalIntegral.integral_congr (fun t _ => by rw [ramP2corr_chiBar_eq_spoly])
    rw [Finset.sum_congr rfl (fun χ _ => hpiece χ)]
    exact hybrid_char_spoly_mvt q N (ramP2coeff N P Q a b c) hT
  -- the sieve-remainder row: the hybrid mean value, mass kept symbolic
  have hDbound : (∑ χ : DirichletCharacter ℂ q, D χ)
      ≤ (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
          * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
    have hpiece : ∀ χ : DirichletCharacter ℂ q,
        D χ = ∫ t in (-T)..T,
          ‖spoly N (chiBarCoeff q χ
            (fun n => if blockOmega P Q n = 0 then a n else 0)) t‖ ^ 2 := by
      intro χ
      rw [hDdef]
      exact intervalIntegral.integral_congr (fun t _ => by rw [ramCopTail_chiBar_eq_spoly])
    rw [Finset.sum_congr rfl (fun χ _ => hpiece χ)]
    refine (hybrid_char_spoly_mvt q N
      (fun n => if blockOmega P Q n = 0 then a n else 0) hT).trans ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) ?_
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      by_cases h : blockOmega P Q n = 0 <;> simp [h]
    · have h1 : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T := by positivity
      have h2 : (0 : ℝ) ≤ 7 * (q.totient : ℝ) * (N : ℝ) / q := by positivity
      linarith
  calc (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
        ‖ramErr H N X P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
          (chiBarCoeff q χ c) t‖ ^ 2)
      ≤ ∑ χ : DirichletCharacter ℂ q, 3 * (W χ + Cr χ + D χ) :=
        Finset.sum_le_sum (fun χ _ => hrow χ)
    _ = 3 * ((∑ χ : DirichletCharacter ℂ q, W χ) + (∑ χ : DirichletCharacter ℂ q, Cr χ)
          + ∑ χ : DirichletCharacter ℂ q, D χ) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ 3 * ((q.totient : ℝ) * (2 * T * (windowMass H N X P Q b c) ^ 2)
          + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
              * (∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
          + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
              * (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
                  ‖a n‖ ^ 2 / (n : ℝ) ^ 2)) := by
        have h := add_le_add (add_le_add hWbound hCbound) hDbound
        linarith

/-- **D2 — KMT LEMMA 6.7, THE RAMARÉ DECOMPOSITION, `χ`-SUMMED.**  For `1`-bounded-free
coefficient triples `(a,b,c)` satisfying only the block factorisation
`a_{pm} = b_m·c_p` (`p` prime, `P ≤ p ≤ Q`, `p ∤ m`),

`∑_{χ mod q} ∫_{-T}^{T} ‖∑_{n≤N} χ̄(n)aₙ/n^{1+it}‖² dt`
`  ≤ 2·#ℐ · ∑_{j∈ℐ} ∑_{χ mod q} ∫_{-T}^{T} ‖Q_{j,H}(χ̄,1+it)·R_{j,H}(χ̄,1+it)‖² dt`
`    + 2·(the two error terms + the sieve remainder)`,

with `ℐ = ⌊H log P⌋..⌊H log Q⌋` the `H·log p` grid (N6: the corpus's grid IS KMT's, not
base-2 dyadic) and the error block exactly `ramErr_meanSq_all_chi`'s.

The route is KMT's own proof note — "almost identical to [32, Lemma 12] … estimates the
error terms by Lemma 6.2 instead of the MVT": the identity work of the landed
`lemma12_meansq_of_windowErr` is reused verbatim at the twisted data (character-blind by
`chiBar_hcoef`), and only the error rows are re-priced through wave P-2's hybrid mean
value.  The `#ℐ` factor is the Cauchy–Schwarz over `j` (`cauchy_schwarz_intervalIntegral`),
uniform in `χ`; the `∑_χ ∑_j` is exchanged to `∑_j ∑_χ` so each `j`-block presents the
`χ`-summed moment that D1 (`multShiuChi_moment`) prices. -/
theorem lemma12_meansq_all_chi (q : ℕ) [NeZero q] (H : ℝ) (hH : 0 < H) (N X P Q : ℕ)
    (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (T : ℝ) (hT : 0 ≤ T) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
              ‖ramMain H N X P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)
        + 2 * (3 * ((q.totient : ℝ) * (2 * T * (windowMass H N X P Q b c) ^ 2)
            + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
                * (∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
            + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
                * (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
                    ‖a n‖ ^ 2 / (n : ℝ) ^ 2))) := by
  classical
  -- the per-χ Cauchy–Schwarz-over-`j` reduction, error carried as-is
  have hper : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-T)..T, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        ≤ 2 * ((ramI H P Q).card : ℝ)
            * (∑ j ∈ ramI H P Q, ∫ t in (-T)..T,
                ‖ramMain H N X P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)
          + 2 * (∫ t in (-T)..T, ‖ramErr H N X P Q (chiBarCoeff q χ a)
              (chiBarCoeff q χ b) (chiBarCoeff q χ c) t‖ ^ 2) := fun χ =>
    lemma12_meansq_of_windowErr H N X P Q _ _ _ T _ hT (le_refl _)
  have hsum := Finset.sum_le_sum (fun (χ : DirichletCharacter ℂ q) (_ : χ ∈ Finset.univ) =>
    hper χ)
  have hsplit : (∑ χ : DirichletCharacter ℂ q,
        (2 * ((ramI H P Q).card : ℝ)
            * (∑ j ∈ ramI H P Q, ∫ t in (-T)..T,
                ‖ramMain H N X P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)
          + 2 * (∫ t in (-T)..T, ‖ramErr H N X P Q (chiBarCoeff q χ a)
              (chiBarCoeff q χ b) (chiBarCoeff q χ c) t‖ ^ 2)))
      = 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
              ‖ramMain H N X P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) j t‖ ^ 2)
        + 2 * (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
            ‖ramErr H N X P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
              (chiBarCoeff q χ c) t‖ ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  rw [hsplit] at hsum
  refine hsum.trans ?_
  have herr := ramErr_meanSq_all_chi q H hH N X P Q hP a b c hcoef T hT
  linarith

end Salt.MR
