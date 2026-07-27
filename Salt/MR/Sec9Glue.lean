/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.JFactor
import Salt.MR.SeamCalibrationK

/-!
# Sec9Glue — MR §9's glue: Lemma 5, Lemma 4, and the eq (26)/(27)/(28) chain

Source: Matomäki–Radziwiłł, arXiv `1501.04585v4`, **§9 (pp. 13–15, 30–31)**;
extract `docs/sources/mr_extract.md` §6.1–§6.5 (the byte-verified page).
Design block: `docs/exploration/hsup-design.md` ⟦V9⟧ (the census row "§9 glue
1000–2000; Lemma 5 critical") and ⟦V9c⟧ (the K-ladder: eq (28) is kernel-settled).

## ⟦THE `1_S` LAW⟧ — this file is the home of the `S`-restriction

The restriction `n ∈ S` enters the MR argument at the **door/sieve** level and
nowhere else: the seam row's coefficients never carry it.  §9 is where `1_S` is
introduced (`MemS`), expanded (`lemma5`), budgeted (`lemma5_budget`), and paid for
(`card_not_memS_le_sum` → `sec9_eq28_exit`).

## 🚨 The LOUD CORRECTION carried over from the extract (§6.2)

Lemma 4 and Lemma 5 are **NOT** retired by the door road's `h ≤ h₂`.  Eq (26) is
stated once and used in *both* branches of p. 30; what `h ≤ h₂` retires is only the
standalone long-interval branch.  Lemma 4 (p. 13) and Lemma 5 (p. 15) stay on the
critical path.

## The stones

§0–§1 (**S9-1, the critical stone**) — Lemma 5, MR p. 15:
* `MemS` — MR §2 p. 6's set `S`: the `n` with a prime factor in *every* block
  `[P_j, Q_j]`, `1 ≤ j ≤ J`.
* `gJ` — MR p. 15's `g_𝒥`, the completely multiplicative function with
  `g_𝒥(p^k) = 1` if `p ∉ ⋃_{j∈𝒥}[P_j,Q_j]` and `0` otherwise.  The MR defining
  spec is `gJ_prime_pow` (verbatim, with the `⋃` as a `Finset.biUnion` of the
  pinned `jBlock`s); complete multiplicativity is `gJ_mul`.
* `lemma5_middle` / `lemma5` — the two equalities of MR p. 15's display:
  `∑_{n∈S} a_n = ∑_n a_n ∏_{j=1}^J (1 − g_{{j}}(n))
              = ∑_{𝒥⊆{1,…,J}} (−1)^{#𝒥} ∑_n g_𝒥(n) a_n`.
  Both ride the landed `JFactor.prod_one_sub_eq_alt_sum` (the inclusion–exclusion
  identity, H-5's J1).  `lemma5_MR_middle`/`lemma5_MR` are the `X ≤ n ≤ 2X`
  instances, byte-fit to the source's index range.
* `lemma5_budget` / `lemma5_budget_pinned` — **the `2^J` budget page** (MR p. 28,
  §8.3: *"by Lemmas 3 and 5 (since `2^J ≪ (log X)^{o(1)}`)"*): a uniform bound `B`
  on the `2^J` inclusion–exclusion rows costs exactly `2^J · B`.  The pinned form
  is at the K-ladder's `Jb = 2` (`SeamCalibrationK.calFrameK_satisfiable`), where
  the budget factor is the number `4`.

§2 (**S9-2**) — Lemma 4, MR p. 13 (Lipschitz, Granville–Soundararajan):
* `hTwo` — MR's `h₂ = X/(log X)^{1/5}`.  The extract's §6.1 finding: this is
  **exactly** the lower endpoint of Lemma 4's `y`-range (p. 13) and **exactly** the
  long scale of Lemma 14 (p. 21) — the same constant, not a coincidence.
* `Lemma4Comparison` — the statement of Lemma 4 as a named interface, with the
  implied constant explicit.  Its proof (pp. 13–14) runs through Halász (Lemma 1)
  and Granville–Soundararajan **[12, Lemma 7.1, Theorem 4, Corollary 3]**; those
  three are *not* in the corpus, so Lemma 4 is carried as a hypothesis and this
  file proves what §9 does with it.  ⟦ZENO: honest split, flagged.⟧
* `door_h_le_hTwo` — the door road's branch selector: `h ≪ log X` puts us in the
  `h ≤ h₂` branch of p. 30 as soon as `C(log X)^{6/5} ≤ X`.

§3 (**S9-3**) — the p. 30–31 comparison chain, eq (26)/(27)/(28):
* `sec9_split` — p. 30 (a): the three-term split off `n ∉ S`.
* `sec9_count_identity` — p. 30 (b): the short-interval `n ∉ S` count traded for
  the `n ∈ S` count.
* `sec9_four_term` — p. 30 (c): the four-term bound, **with the coefficient `2`**
  (read twice: the extract's §6.3 flags the rendering trap on `(2 + 1/50)`).
* `card_not_memS_le_sum` — the combinatorial content of p. 31 (e)'s first
  inequality: the `n ∉ S` count is a union bound over the `J` blocks.  (The sieve
  step proper — `[8, Thm 6.17]`, Friedlander–Iwaniec — and the Mertens step
  `∏_{P≤p≤Q}(1−1/p) ≤ log P/log Q` are the `hsieve` hypothesis's content.)
* `sec9_eq28` — p. 31 (f), eq (28): `≤ δ/50 + (2 + 1/50) ∑_j log P_j/log Q_j`.
* `sec9_eq28_exit` — **the exit**: (28) run against the K-ladder.  The demand side
  is *not* re-derived here — it is cited from `SeamCalibrationK.eq28_clears_of_M`
  (⟦V9c⟧: `M ≥ 8/δ` ⟹ `δ/50 + (2+1/50)∑_j ≤ δ`), so the whole §9 comparison lands
  at Theorem 1's `δ`, modulo the two `O(1/h)`-shaped normalisation remainders that
  MR absorb into `C′ loglog h/log h`.

## Honest scope

Three named hypotheses, each an external theorem the corpus does not own:
`Lemma4Comparison` (Granville–Soundararajan), the two Theorem-3 applications
(`hthm3f`, `hthm3one` — MR eq (27)'s exceptional-set accounting), and `hsieve`
(the fundamental lemma of the sieve, p. 31 (e)).  Everything between them is
kernel-checked here.

⟦ZENO residuals — what this file does NOT contain⟧
1. **Lemma 4's proof** (pp. 13–14).  Needs Halász (Lemma 1) *and*
   Granville–Soundararajan **[12, Lemma 7.1, Theorem 4, Corollary 3]**, plus the
   `𝔻(f,p^{it_f};X)² ≥ (1 − 2/π − o(1))loglog X` page for `|t_f| ≥ 1/100`.  A
   separate arc; `Lemma4Comparison` is its interface.
2. **Eq (26) itself** — Step 1's `h₂`-average → Theorem 3's `X`-average bridge.
   It belongs to the Theorem-3 / Lemma-14 arc, not to the p. 30–31 glue; §9 only
   selects its branch (`door_h_le_hTwo`).
3. **Eq (27)'s exceptional-set count** — `≪ X(log h)^{1/3}/(P₁^{1/6−η}δ²) +
   X/((log X)^{1/50}δ²)`, i.e. the `δ²` Chebyshev-on-the-mean-square page.  Carried
   as the two `δ/100` hypotheses instead of derived.
4. **The sieve step proper** — `[8, Thm 6.17]`'s `(1 + 1/100)` and the Mertens
   bound `∏_{P≤p≤Q}(1−1/p) ≤ log P/log Q`; both live inside `hsieve`.  Only the
   union bound (`card_not_memS_le_sum`) is kernel-checked.
5. **The p. 31 parameter set** — `η = 1/150`, `Q₁ = h`, `P₁ = max{h^{δ/4},
   (log h)^{6000}}` and the `C′ = 20000` arithmetic (extract §6.4).  Superseded on
   this road by the K-ladder's own pin (`SeamCalibrationK.calFrameK_satisfiable`),
   whose eq-(28) demand `eq28_clears_of_M` is what `sec9_eq28_exit` cites.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §0  `S` and the `𝒥`-datum `g_𝒥` (MR §2 p. 6, §9 p. 15) -/

/-- **MR's set `S`** (§2, p. 6).  `n ∈ S` iff `n` has at least one prime factor in
every block `[P_j, Q_j]`, `1 ≤ j ≤ J`.  Written with `Decomp.blockOmega`, the
corpus's own block-divisor counter, on the STEP-0 closed blocks. -/
def MemS (Pseq Qseq : ℕ → ℕ) (J n : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 J, 1 ≤ blockOmega (Pseq j) (Qseq j) n

instance decidableMemS (Pseq Qseq : ℕ → ℕ) (J n : ℕ) :
    Decidable (MemS Pseq Qseq J n) := by
  unfold MemS; infer_instance

/-- **MR p. 15's `g_𝒥`.**  For `𝒥 ⊆ {1,…,J}`, the completely multiplicative
function with `g_𝒥(p^j) = 1` if `p ∉ ⋃_{j∈𝒥}[P_j,Q_j]` and `0` otherwise —
equivalently (and this is the corpus-shaped definition) the indicator of "`n` has
no prime factor in any block indexed by `𝒥`".  The prime-power spec MR *state* is
`gJ_prime_pow`; complete multiplicativity is `gJ_mul`.

⚠ MR reuse the letter `j` for both the exponent in `p^j` and the index in
`⋃_{j∈𝒥}` (the extract's §6.2 note).  The exponent is immaterial — that is exactly
what `gJ_prime_pow`'s `k`-uniformity records. -/
def gJ (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (n : ℕ) : ℂ :=
  if ∀ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) n = 0 then 1 else 0

/-- `ω(p^k; P, Q)` is `1` or `0` according as `p` lies in the block or not. -/
lemma blockOmega_prime_pow {P Q p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    blockOmega P Q (p ^ k) = if P ≤ p ∧ p ≤ Q then 1 else 0 := by
  unfold blockOmega BlockPrimeDivs
  rw [Nat.primeFactors_pow p hk, hp.primeFactors]
  by_cases h : P ≤ p ∧ p ≤ Q
  · rw [Finset.filter_singleton, if_pos h, if_pos h, Finset.card_singleton]
  · rw [Finset.filter_singleton, if_neg h, if_neg h, Finset.card_empty]

/-- **The MR defining spec of `g_𝒥`, byte-fit** (p. 15): `g_𝒥(p^k) = 1` if
`p ∉ ⋃_{j∈𝒥}[P_j,Q_j]`, `0` otherwise — for *every* exponent `k ≥ 1`, which is the
"the exponent is immaterial" half of complete multiplicativity.  The `⋃` is the
`Finset.biUnion` of the STEP-0 pinned closed blocks `JFactor.jBlock`. -/
theorem gJ_prime_pow (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) {p k : ℕ} (hp : p.Prime)
    (hk : k ≠ 0) :
    gJ 𝒥 Pseq Qseq (p ^ k)
      = if p ∉ 𝒥.biUnion (fun j => jBlock (Pseq j) (Qseq j)) then 1 else 0 := by
  have hiff : (∀ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) (p ^ k) = 0)
      ↔ p ∉ 𝒥.biUnion (fun j => jBlock (Pseq j) (Qseq j)) := by
    constructor
    · intro hall hmem
      obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hmem
      have hzero := hall j hj
      rw [blockOmega_prime_pow hp hk] at hzero
      rw [mem_jBlock] at hpj
      rw [if_pos hpj.1] at hzero
      exact one_ne_zero hzero
    · intro hnot j hj
      rw [blockOmega_prime_pow hp hk]
      have hout : ¬ (Pseq j ≤ p ∧ p ≤ Qseq j) := by
        intro hc
        exact hnot (Finset.mem_biUnion.mpr ⟨j, hj, mem_jBlock.mpr ⟨hc, hp⟩⟩)
      rw [if_neg hout]
  unfold gJ
  exact if_congr hiff rfl rfl

/-- `ω(·; P, Q)` vanishes on a product exactly when it vanishes on both factors. -/
lemma blockOmega_mul_eq_zero_iff {P Q m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    blockOmega P Q (m * n) = 0
      ↔ blockOmega P Q m = 0 ∧ blockOmega P Q n = 0 := by
  simp only [blockOmega, BlockPrimeDivs, Finset.card_eq_zero,
    Nat.primeFactors_mul hm hn, Finset.filter_union, Finset.union_eq_empty]

/-- **`g_𝒥` is completely multiplicative** (MR p. 15).  No coprimality hypothesis:
the block-avoidance indicator is multiplicative on *all* nonzero pairs, which is
what "completely multiplicative" buys. -/
theorem gJ_mul (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) :
    gJ 𝒥 Pseq Qseq (m * n) = gJ 𝒥 Pseq Qseq m * gJ 𝒥 Pseq Qseq n := by
  unfold gJ
  by_cases hm' : ∀ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) m = 0
  · by_cases hn' : ∀ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) n = 0
    · rw [if_pos hm', if_pos hn', one_mul, if_pos]
      exact fun j hj => (blockOmega_mul_eq_zero_iff hm hn).mpr ⟨hm' j hj, hn' j hj⟩
    · rw [if_pos hm', if_neg hn', mul_zero, if_neg]
      intro hall
      exact hn' (fun j hj => ((blockOmega_mul_eq_zero_iff hm hn).mp (hall j hj)).2)
  · rw [if_neg hm', zero_mul, if_neg]
    intro hall
    exact hm' (fun j hj => ((blockOmega_mul_eq_zero_iff hm hn).mp (hall j hj)).1)

/-- `g_∅ ≡ 1` — the `𝒮_∅` row of the inclusion–exclusion. -/
theorem gJ_empty (Pseq Qseq : ℕ → ℕ) (n : ℕ) : gJ ∅ Pseq Qseq n = 1 := by
  unfold gJ
  rw [if_pos (by simp)]

/-- `g_𝒥 = ∏_{j∈𝒥} g_{{j}}` in the corpus's own `JFactor.blockAvoid` shape: the
bridge from MR's union-indexed `g_𝒥` to the landed H-5 block data. -/
theorem gJ_eq_prod (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (n : ℕ) :
    gJ 𝒥 Pseq Qseq n = ∏ j ∈ 𝒥, blockAvoid (Pseq j) (Qseq j) n := by
  unfold gJ
  by_cases h : ∀ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) n = 0
  · rw [if_pos h]
    exact (Finset.prod_eq_one (fun j hj => by rw [blockAvoid, if_pos (h j hj)])).symm
  · rw [if_neg h]
    have hex : ∃ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) n ≠ 0 := by
      by_contra hc
      refine h (fun j hj => ?_)
      by_contra hz
      exact hc ⟨j, hj, hz⟩
    obtain ⟨j, hj, hjz⟩ := hex
    exact (Finset.prod_eq_zero hj (by rw [blockAvoid, if_neg hjz])).symm

/-- `g_{{j}}` is the single-block avoidance indicator. -/
theorem gJ_singleton (j : ℕ) (Pseq Qseq : ℕ → ℕ) (n : ℕ) :
    gJ {j} Pseq Qseq n = blockAvoid (Pseq j) (Qseq j) n := by
  rw [gJ_eq_prod, Finset.prod_singleton]

/-- `∏_{j∈𝒥} g_{{j}} = g_𝒥` — the multiplicativity of the datum *in the index set*,
which is the form the inclusion–exclusion consumes. -/
theorem prod_gJ_singleton (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (n : ℕ) :
    ∏ j ∈ 𝒥, gJ {j} Pseq Qseq n = gJ 𝒥 Pseq Qseq n := by
  rw [gJ_eq_prod]
  exact Finset.prod_congr rfl (fun j _ => gJ_singleton j Pseq Qseq n)

/-! ## §1  S9-1 — **Lemma 5** (MR p. 15), the critical stone -/

/-- `∏_{j=1}^J (1 − g_{{j}}(n)) = 1_S(n)` — the middle object of MR p. 15's display.
Rides `JFactor.prod_one_sub_blockAvoid` (H-5's J1). -/
theorem prod_one_sub_gJ (Pseq Qseq : ℕ → ℕ) (J n : ℕ) :
    ∏ j ∈ Finset.Icc 1 J, (1 - gJ {j} Pseq Qseq n)
      = if MemS Pseq Qseq J n then (1 : ℂ) else 0 := by
  have hg : ∀ j ∈ Finset.Icc 1 J,
      (1 - gJ {j} Pseq Qseq n) = 1 - blockAvoid (Pseq j) (Qseq j) n :=
    fun j _ => by rw [gJ_singleton]
  rw [Finset.prod_congr rfl hg]
  by_cases h : MemS Pseq Qseq J n
  · rw [if_pos h]
    refine Finset.prod_eq_one (fun j hj => ?_)
    have hj1 : 1 ≤ blockOmega (Pseq j) (Qseq j) n := h j hj
    rw [blockAvoid, if_neg (by omega), sub_zero]
  · rw [if_neg h]
    have hex : ∃ j ∈ Finset.Icc 1 J, blockOmega (Pseq j) (Qseq j) n = 0 := by
      by_contra hc
      refine h (fun j hj => ?_)
      by_contra hlt
      exact hc ⟨j, hj, by omega⟩
    obtain ⟨j, hj, hj0⟩ := hex
    exact Finset.prod_eq_zero hj (by rw [blockAvoid, if_pos hj0, sub_self])

/-- **Lemma 5, the first equality** (MR p. 15):
`∑_{n∈N, n∈S} a_n = ∑_{n∈N} a_n ∏_{j=1}^{J} (1 − g_{{j}}(n))`. -/
theorem lemma5_middle (N : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (a : ℕ → ℂ) :
    ∑ n ∈ N.filter (fun n => MemS Pseq Qseq J n), a n
      = ∑ n ∈ N, a n * ∏ j ∈ Finset.Icc 1 J, (1 - gJ {j} Pseq Qseq n) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [prod_one_sub_gJ]
  by_cases h : MemS Pseq Qseq J n
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- **Lemma 5** (MR p. 15) — *the critical stone*.  The inclusion–exclusion
expansion of the `S`-restriction:
`∑_{n∈N, n∈S} a_n = ∑_{𝒥⊆{1,…,J}} (−1)^{#𝒥} ∑_{n∈N} g_𝒥(n) a_n`.
MR call it "an immediate consequence of the inclusion–exclusion principle" and give
no proof; the identity it is immediate from is the landed
`JFactor.prod_one_sub_eq_alt_sum`. -/
theorem lemma5 (N : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (a : ℕ → ℂ) :
    ∑ n ∈ N.filter (fun n => MemS Pseq Qseq J n), a n
      = ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
          (-1 : ℂ) ^ 𝒥.card * ∑ n ∈ N, gJ 𝒥 Pseq Qseq n * a n := by
  rw [lemma5_middle N Pseq Qseq J a]
  have hpt : ∀ n ∈ N, a n * ∏ j ∈ Finset.Icc 1 J, (1 - gJ {j} Pseq Qseq n)
      = ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
          (-1 : ℂ) ^ 𝒥.card * (gJ 𝒥 Pseq Qseq n * a n) := by
    intro n _
    rw [prod_one_sub_eq_alt_sum (Finset.Icc 1 J) (fun j => gJ {j} Pseq Qseq n),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun 𝒥 _ => ?_)
    rw [prod_gJ_singleton]
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun 𝒥 _ => (Finset.mul_sum _ _ _).symm)

/-- **Lemma 5 at MR's index range** (p. 15, the first equality): `X ≤ n ≤ 2X`. -/
theorem lemma5_MR_middle (X : ℕ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (a : ℕ → ℂ) :
    ∑ n ∈ (Finset.Icc X (2 * X)).filter (fun n => MemS Pseq Qseq J n), a n
      = ∑ n ∈ Finset.Icc X (2 * X),
          a n * ∏ j ∈ Finset.Icc 1 J, (1 - gJ {j} Pseq Qseq n) :=
  lemma5_middle _ Pseq Qseq J a

/-- **Lemma 5 at MR's index range** (p. 15, the second equality): `X ≤ n ≤ 2X`. -/
theorem lemma5_MR (X : ℕ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (a : ℕ → ℂ) :
    ∑ n ∈ (Finset.Icc X (2 * X)).filter (fun n => MemS Pseq Qseq J n), a n
      = ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
          (-1 : ℂ) ^ 𝒥.card * ∑ n ∈ Finset.Icc X (2 * X), gJ 𝒥 Pseq Qseq n * a n :=
  lemma5 _ Pseq Qseq J a

/-- **The `2^J` budget page** (MR p. 28, §8.3: *"by Lemmas 3 and 5 (since
`2^J ≪ (log X)^{o(1)}`)"*).  A bound `B` uniform over the `2^J` inclusion–exclusion
rows costs exactly the factor `2^J` on the `S`-restricted sum.

The extract's §6.1 **[DERIVED]** row: this `2^J` is the whole source of the `o(1)`
in eq (26)'s `(log X)^{−1/20+o(1)}` (MR spell `2^J ≪ (log X)^{o(1)}` out at p. 28
but not at (26)). -/
theorem lemma5_budget {N : Finset ℕ} {Pseq Qseq : ℕ → ℕ} {J : ℕ} {a : ℕ → ℂ}
    {B : ℝ} (hB : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset,
      ‖∑ n ∈ N, gJ 𝒥 Pseq Qseq n * a n‖ ≤ B) :
    ‖∑ n ∈ N.filter (fun n => MemS Pseq Qseq J n), a n‖ ≤ 2 ^ J * B := by
  rw [lemma5]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset,
      ‖(-1 : ℂ) ^ 𝒥.card * ∑ n ∈ N, gJ 𝒥 Pseq Qseq n * a n‖ ≤ B := by
    intro 𝒥 h𝒥
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact hB 𝒥 h𝒥
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [Finset.card_powerset, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
    Nat.cast_pow]
  norm_num

/-- **The budget at the K-ladder's pin** (`SeamCalibrationK.calFrameK_satisfiable`:
`Jb = 2`).  The `2^J` of MR p. 28 is the number `4` there — the ⟦V9c⟧ reading of
"the seam row's formula is a number", carried down to §9. -/
theorem lemma5_budget_pinned {N : Finset ℕ} {Pseq Qseq : ℕ → ℕ} {a : ℕ → ℂ}
    {B : ℝ} (hB : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      ‖∑ n ∈ N, gJ 𝒥 Pseq Qseq n * a n‖ ≤ B) :
    ‖∑ n ∈ N.filter (fun n => MemS Pseq Qseq 2 n), a n‖ ≤ 4 * B := by
  have h := lemma5_budget (N := N) (Pseq := Pseq) (Qseq := Qseq) (J := 2) hB
  norm_num at h
  exact h

/-! ## §2  S9-2 — **Lemma 4** (MR p. 13) and the door road's branch -/

/-- **MR's `h₂`** — `X/(log X)^{1/5}`.  Extract §6.1's finding, recorded: this is
*exactly* the lower endpoint of Lemma 4's `y`-range (p. 13) and *exactly* the long
scale of Lemma 14 (p. 21) and of the p. 30 case split — one constant, not three. -/
noncomputable def hTwo (X : ℝ) : ℝ := X / Real.log X ^ ((1 : ℝ) / 5)

/-- **Lemma 4 (MR p. 13; Lipschitz, Granville–Soundararajan) — the interface.**
For `f : ℕ → [−1,1]` multiplicative, every `x ∈ [X, 2X]` and every
`X/(log X)^{1/5} ≤ y ≤ X`:
`(1/y)∑_{x≤n≤x+y} f(n) = (1/X)∑_{X≤n≤2X} f(n) + O(1/(log X)^{1/20})`,
here with the implied constant named.

⟦ZENO, flagged⟧ The proof (pp. 13–14) reduces to (13) via the minimiser `t_f` of
`𝔻(f, p^{it}; X)` over `|t| ≤ log X`, Halász (Lemma 1) when
`𝔻(f, p^{it_f}; X)² ≥ (1/3)loglog X`, and **[12, Lemma 7.1 and Theorem 4]** +
**[12, Corollary 3]** otherwise; the `|t_f| ≥ 1/100` case uses
`𝔻(f, p^{it_f}; X)² ≥ (1 − 2/π − o(1))loglog X`.  Granville–Soundararajan's three
inputs are not in the corpus, so Lemma 4 is a hypothesis, not a theorem, here. -/
def Lemma4Comparison (f : ℕ → ℝ) (X C : ℝ) : Prop :=
  ∀ x y : ℝ, X ≤ x → x ≤ 2 * X → hTwo X ≤ y → y ≤ X →
    |(1 / y) * ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + y⌋₊, f n
        - (1 / X) * ∑ n ∈ Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊, f n|
      ≤ C / Real.log X ^ ((1 : ℝ) / 20)

/-- **The door road's branch selector** (MR p. 30's case split, extract §6.2's
table).  On the door road `h = O(log X)`, so `h ≤ h₂` by an exponential margin:
the gate is just `C(log X)^{6/5} ≤ X`.  This is the branch in which eq (26) is
LOAD-BEARING (it converts Step 1's `h₂`-average into Theorem 3's `X`-average); the
retired branch is the standalone `h > h₂` one. -/
theorem door_h_le_hTwo {X C h : ℝ} (hlog : 0 < Real.log X)
    (hh : h ≤ C * Real.log X) (hgate : C * Real.log X ^ ((6 : ℝ) / 5) ≤ X) :
    h ≤ hTwo X := by
  have hpow : (0 : ℝ) < Real.log X ^ ((1 : ℝ) / 5) :=
    Real.rpow_pos_of_pos hlog _
  have hcomb : Real.log X * Real.log X ^ ((1 : ℝ) / 5)
      = Real.log X ^ ((6 : ℝ) / 5) := by
    nth_rewrite 1 [← Real.rpow_one (Real.log X)]
    rw [← Real.rpow_add hlog]
    norm_num
  rw [hTwo, le_div_iff₀ hpow]
  calc h * Real.log X ^ ((1 : ℝ) / 5)
      ≤ (C * Real.log X) * Real.log X ^ ((1 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right hh hpow.le
    _ = C * Real.log X ^ ((6 : ℝ) / 5) := by rw [mul_assoc, hcomb]
    _ ≤ X := hgate

/-! ## §3  S9-3 — the p. 30–31 chain: eq (26)/(27)/(28) -/

/-- **MR p. 30 (a)** — splitting off `n ∉ S`:
`|(1/h)∑_{short} f − (1/X)∑_{long} f| ≤ |(1/h)∑_{short,S} f − (1/X)∑_{long,S} f|
   + (1/h)∑_{short, ∉S} 1 + (1/X)∑_{long, ∉S} 1`. -/
theorem sec9_split (Nsh Nlg : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) {h X : ℝ} (hh : 0 < h) (hX : 0 < X) :
    |(1 / h) * ∑ n ∈ Nsh, f n - (1 / X) * ∑ n ∈ Nlg, f n|
      ≤ |(1 / h) * ∑ n ∈ Nsh.filter P, f n - (1 / X) * ∑ n ∈ Nlg.filter P, f n|
        + (1 / h) * ((Nsh.filter (fun n => ¬ P n)).card : ℝ)
        + (1 / X) * ((Nlg.filter (fun n => ¬ P n)).card : ℝ) := by
  have htail : ∀ (S : Finset ℕ), |∑ n ∈ S.filter (fun n => ¬ P n), f n|
      ≤ ((S.filter (fun n => ¬ P n)).card : ℝ) := by
    intro S
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simpa using
      Finset.sum_le_card_nsmul (S.filter (fun n => ¬ P n)) (fun n => |f n|) 1
        (fun n _ => hf n)
  have hNs := (Finset.sum_filter_add_sum_filter_not Nsh P f).symm
  have hNl := (Finset.sum_filter_add_sum_filter_not Nlg P f).symm
  rw [hNs, hNl]
  have hbn := abs_le.mp (htail Nsh)
  have hbl := abs_le.mp (htail Nlg)
  have hmain :=
    abs_le.mp (le_refl |(1 / h) * ∑ n ∈ Nsh.filter P, f n
      - (1 / X) * ∑ n ∈ Nlg.filter P, f n|)
  have hlow : -|(1 / h) * ∑ n ∈ Nsh.filter P, f n
      - (1 / X) * ∑ n ∈ Nlg.filter P, f n|
      ≤ (1 / h) * ∑ n ∈ Nsh.filter P, f n - (1 / X) * ∑ n ∈ Nlg.filter P, f n :=
    neg_abs_le _
  have hhigh : (1 / h) * ∑ n ∈ Nsh.filter P, f n
      - (1 / X) * ∑ n ∈ Nlg.filter P, f n
      ≤ |(1 / h) * ∑ n ∈ Nsh.filter P, f n
          - (1 / X) * ∑ n ∈ Nlg.filter P, f n| := le_abs_self _
  have hh' : (0 : ℝ) < 1 / h := by positivity
  have hX' : (0 : ℝ) < 1 / X := by positivity
  have hsn := mul_le_mul_of_nonneg_left hbn.2 hh'.le
  have hsn' := mul_le_mul_of_nonneg_left hbn.1 hh'.le
  have hsl := mul_le_mul_of_nonneg_left hbl.2 hX'.le
  have hsl' := mul_le_mul_of_nonneg_left hbl.1 hX'.le
  rw [mul_neg] at hsn' hsl'
  refine abs_le.mpr ⟨by nlinarith [hmain.1], by nlinarith [hmain.2]⟩

/-- **MR p. 30 (b)** — the count identity: the short-interval `n ∉ S` count traded
for the `n ∈ S` count.  (MR's `1 + O(1/h)` is `(1/h)·#[x,x+h]`; here that
normalisation is left explicit so nothing is hidden inside an `O`.) -/
theorem sec9_count_identity (S : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (c : ℝ) :
    c * ((S.filter (fun n => ¬ P n)).card : ℝ)
      = c * (S.card : ℝ) - c * ((S.filter P).card : ℝ) := by
  have hcard : ((S.filter P).card : ℝ)
      + ((S.filter (fun n => ¬ P n)).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ)
      (Finset.card_filter_add_card_filter_not (s := S) (p := P))
  rw [← hcard]
  ring

/-- **MR p. 30 (c)** — the four-term bound, **with the coefficient `2`**:
`|(1/h)∑ f − (1/X)∑ f| ≤ |(1/h)∑_{S} f − (1/X)∑_{S} f|
   + |(1/h)∑_{short,S} 1 − (1/X)∑_{long,S} 1| + (2/X)∑_{long,∉S} 1 + O(1/h)`.
The two remainder terms are MR's `O(1/h)` written out: `(1/h)#short − 1` and
`1 − (1/X)#long`. -/
theorem sec9_four_term (Nsh Nlg : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) {h X : ℝ} (hh : 0 < h) (hX : 0 < X) :
    |(1 / h) * ∑ n ∈ Nsh, f n - (1 / X) * ∑ n ∈ Nlg, f n|
      ≤ |(1 / h) * ∑ n ∈ Nsh.filter P, f n - (1 / X) * ∑ n ∈ Nlg.filter P, f n|
        + |(1 / h) * ((Nsh.filter P).card : ℝ)
            - (1 / X) * ((Nlg.filter P).card : ℝ)|
        + 2 * ((1 / X) * ((Nlg.filter (fun n => ¬ P n)).card : ℝ))
        + (((1 / h) * (Nsh.card : ℝ) - 1) + (1 - (1 / X) * (Nlg.card : ℝ))) := by
  have hsplit := sec9_split Nsh Nlg P f hf hh hX
  have hcs := sec9_count_identity Nsh P (1 / h)
  have hcl := sec9_count_identity Nlg P (1 / X)
  have hlow : -|(1 / h) * ((Nsh.filter P).card : ℝ)
      - (1 / X) * ((Nlg.filter P).card : ℝ)|
      ≤ (1 / h) * ((Nsh.filter P).card : ℝ)
        - (1 / X) * ((Nlg.filter P).card : ℝ) := neg_abs_le _
  linarith

/-- **The union bound behind MR p. 31 (e)** — the combinatorial content of
`∑_{X≤n≤2X, n∉S} 1 ≤ ∑_{j≤J} #{n : no block-`j` prime divides `n`}`.  The sieve
step proper (`[8, Thm 6.17]`, Friedlander–Iwaniec, with its explicit `(1 + 1/100)`)
and the Mertens step `∏_{P_j≤p≤Q_j}(1−1/p) ≤ log P_j/log Q_j` bound the individual
terms; this lemma is the part that is pure counting. -/
theorem card_not_memS_le_sum (Nlg : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) :
    (Nlg.filter (fun n => ¬ MemS Pseq Qseq J n)).card
      ≤ ∑ j ∈ Finset.Icc 1 J,
          (Nlg.filter (fun n => blockOmega (Pseq j) (Qseq j) n = 0)).card := by
  have hsub : Nlg.filter (fun n => ¬ MemS Pseq Qseq J n)
      ⊆ (Finset.Icc 1 J).biUnion
          (fun j => Nlg.filter (fun n => blockOmega (Pseq j) (Qseq j) n = 0)) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnN, hnS⟩ := hn
    have hex : ∃ j ∈ Finset.Icc 1 J, blockOmega (Pseq j) (Qseq j) n = 0 := by
      by_contra hc
      refine hnS (fun j hj => ?_)
      by_contra hlt
      exact hc ⟨j, hj, by omega⟩
    obtain ⟨j, hj, hj0⟩ := hex
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hnN, hj0⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- **MR p. 31 (f), eq (28)** — the assembled bound.  Given the two Theorem-3
applications (at `f` and at `1`, each `≤ δ/100` outside eq (27)'s exceptional set)
and the sieve bound `(1/X)∑_{∉S} 1 ≤ (1 + 1/100)∑_j log P_j/log Q_j`, MR p. 30 (c)
collapses to `δ/50 + (2 + 1/50)∑_j log P_j/log Q_j`, plus the normalisation
remainder.

⚠ The parenthesised factor is `(2 + 1/50)` — a single displayed factor multiplying
the sum (the extract's §6.3 "read twice"; the text layer invites the misreading
`δ/50 + 2 + (1/50)∑`).  `2` comes from (c)'s `2/X` term, `1/50` from the doubled
`(1 + 1/100)`. -/
theorem sec9_eq28 {D E Bc Ssum δ R : ℝ} (hD : D ≤ δ / 100) (hE : E ≤ δ / 100)
    (hsieve : Bc ≤ (1 + 1 / 100) * Ssum) :
    D + E + 2 * Bc + R ≤ δ / 50 + (2 + 1 / 50) * Ssum + R := by
  linarith

/-- **THE §9 EXIT** — eq (28) run against the K-ladder, landing at Theorem 1's `δ`.

The demand side is *not* re-derived here: it is cited from
`SeamCalibrationK.eq28_clears_of_M` (⟦V9c⟧ — `M ≥ 8/δ` forces
`δ/50 + (2 + 1/50)∑_{j≤Jb} log P_j/log Q_j ≤ δ`, uniformly in `Jb`).  What §9 owns
is everything to its left: the `1_S` split (p. 30 (a)), the count trade
(p. 30 (b)), the four-term bound with its coefficient `2` (p. 30 (c)), and the
sieve input (p. 31 (e)).

The residual `R` is MR's `O(1/h)`: the two normalisation defects
`(1/h)#[x,x+h] − 1` and `1 − (1/X)#[X,2X]`, which MR absorb into Theorem 1's
`C′ loglog h/log h` (`C′ = 20000`, extract §6.4). -/
theorem sec9_eq28_exit (Nsh Nlg : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (J : ℕ)
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) {h X δ : ℝ} (hh : 0 < h) (hX : 0 < X)
    (hδ : 0 < δ) {A G M : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M)
    (hMδ : 8 / δ ≤ (M : ℝ))
    (hthm3f : |(1 / h) * ∑ n ∈ Nsh.filter (fun n => MemS Pseq Qseq J n), f n
        - (1 / X) * ∑ n ∈ Nlg.filter (fun n => MemS Pseq Qseq J n), f n|
      ≤ δ / 100)
    (hthm3one : |(1 / h) * ((Nsh.filter (fun n => MemS Pseq Qseq J n)).card : ℝ)
        - (1 / X) * ((Nlg.filter (fun n => MemS Pseq Qseq J n)).card : ℝ)|
      ≤ δ / 100)
    (hsieve : (1 / X) * ((Nlg.filter (fun n => ¬ MemS Pseq Qseq J n)).card : ℝ)
      ≤ (1 + 1 / 100) * ∑ j ∈ Finset.Icc 1 J,
          Real.log ((calP A G j : ℕ) : ℝ)
            / Real.log ((calQK A G M j : ℕ) : ℝ)) :
    |(1 / h) * ∑ n ∈ Nsh, f n - (1 / X) * ∑ n ∈ Nlg, f n|
      ≤ δ + (((1 / h) * (Nsh.card : ℝ) - 1) + (1 - (1 / X) * (Nlg.card : ℝ))) := by
  have hfour :=
    sec9_four_term Nsh Nlg (fun n => MemS Pseq Qseq J n) f hf hh hX
  have hclear := eq28_clears_of_M hA hG hM J hδ hMδ
  linarith

end Salt.MR
