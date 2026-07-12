/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BrunLower.Defs
import Salt.BrunLower.MainTerm

/-!
# The block decomposition (blueprint `p0`, node B3a)

The reduction of Halberstam–Richert's main sum `L_ν(z) = Σ_{d∣P(z)} μ(d) χ_ν(d) ω(d)/d`
(`s.mainSum` against B2's coefficient system, node B3's `hdecomp`) to the block/power form
consumed by node B3 (`Salt.BrunLower.MainTerm`).  Source: Halberstam–Richert, *A new look at
Brun's sieve*, Mém. SMF **25** (1971) 97–106 (numdam `10.24033/msmf.39`), pp. 101–104.

## What this node proves (the `(2.11)` elementary-symmetric bound + the endpoint)

The genuinely-new, fully-discharged content is `esymm_le`: for nonnegative weights the `k`-th
**elementary symmetric function** is bounded by `(Σ)^k / k!` — H-R's "elementary inequality for
elementary symmetric functions" cited on p.104.  From it we assemble the block-form endpoints
`mainSum_le_blockForm` / `mainSum_ge_blockForm` (discharging B3's `hdecomp` from the p.104
display) and the composed `mainSum_le_of_upper'` / `mainSum_ge_of_lower'` that consume B3 leaving
only the `(2.16)`-shaped density hypotheses (`hWr`, `hps`) and the block-decomposition identity.

## Primary-source transcription (pp. 101–104, verbatim from the page images)

**(2.7)** `L_ν(z) = Σ_{d∣P(z)} μ(d) χ_ν(d) ω(d)/d`  (ν = 1,2).  Note `L_ν(z) = W(z)` when
`χ_ν(d)=1` for every divisor `d` of `P(z)`.

**LEMMA 3.**  Let `p⁺` denote the successor of `p` in `𝒫`, and write
`P(u,v) = ∏_{u≤p<v, p∈𝒫} p = P(v)/P(u)`.  Then, for ν = 1 and 2,
```
  L_ν(z) = W(z){ 1 + (−1)^{ν−1} Σ_{p<z} (ω(p)/p)(W(p)/W(z))
                      Σ_{t∣P(p⁺,z)} χ_ν(t){1−χ_ν(pt)} ω(t)/t }.
```
*Proof.*  Substitute the (obvious) relation
`χ_ν(d) = 1 − Σ_{p∣d}{ χ_ν((d,P(p⁺,z))) − χ_ν((d,P(p,z))) }` (a telescoping over the prime
factors of `d`) into (2.7); writing `d = δpt` with `δ∣P(p)`, `t∣P(p⁺,z)`, one gets
`L_ν(z) = W(z) + Σ_{p<z} (ω(p)/p) Σ_{δ∣P(p)} μ(δ)(ω(δ)/δ) Σ_{t∣P(p⁺,z)} μ(t)(χ(t)−χ(pt))(ω(t)/t)`.
An application of Lemma 1 (B2's `peel_term_nonneg` mechanism: `μ(t)(χ_ν(t)−χ_ν(pt)) =
(−1)^{ν−1}μ(t)χ_ν(t)(1−χ_ν(pt))`) to the innermost sum, together with `Σ_{δ∣P(p)}μ(δ)ω(δ)/δ =
W(p)`, completes it.

**COROLLARY** (group `p∈[z_n,z_{n-1})`, use `W(p) ≤ W(z_n)`; `|θ|≤1`):
```
  L_ν(z) = W(z){ 1 + θ Σ_{n=1}^{r} (W(z_n)/W(z)) Σ_{z_n≤p<z_{n-1}} (ω(p)/p)
                      Σ_{t∣P(p⁺,z)} χ_ν(t){1−χ_ν(pt)} ω(t)/t },  |θ| ≤ 1.
```

**(2.10)** `χ_ν(d) = 1` iff `d∣P(z_n,z) → Ω(d) ≤ 2b−ν+2n−1`, `= 0` otherwise.  Interpreting the
inner sum (a `t` contributes only when `χ_ν(t)=1, χ_ν(pt)=0`, forcing `Ω(t)=2b−ν+2n−1`, so with
`d=pt`, `Ω(d)=2b−ν+2n` and `d∣P(z_n,z)`) gives the **p.104 display**:
```
  L_ν(z) = W(z){ 1 + θ Σ_{n=1}^{r} (W(z_n)/W(z))
                      Σ_{d∣P(z_n,z), Ω(d)=2b−ν+2n} ω(d)/d },  |θ| ≤ 1.
```

**(2.11)** the inner sum is the `(2b−ν+2n)`-th elementary symmetric function of the arguments
`{ω(p)/p : z_n ≤ p < z}` (`d` squarefree ⇒ a `k`-subset of the window primes; `ω(d)/d =
∏ ω(p)/p`), and by the elementary inequality `e_k ≤ (Σ)^k/k!`,
```
  L_ν(z) = W(z){ 1 + θ Σ_{n=1}^{r} (W(z_n)/W(z)) (1/(2b−ν+2n)!)
                      (Σ_{z_n≤p<z} ω(p)/p)^{2b−ν+2n} },  |θ| ≤ 1.
```
`|θ|≤1` yields the one-sided bounds: upper (ν=1) `L_1 ≤ W(z)(1 + Σ …)`, lower (ν=2)
`L_2 ≥ W(z)(1 − Σ …)`.  These are exactly B3's `hdecomp`/`hdecomp'`.

## ⚠️ Frozen-set note / remaining obligation (Iron Rule 1 — flagged, not improvised)

The `(2.11)` bound (`esymm_le`) and the endpoint assembly are proved here in full.  The
combinatorial identity producing the **p.104 display** — Lemma 3's telescoping/reindexing +
the Corollary's interval grouping + the (2.10) block interpretation — is taken as the explicit
interface hypothesis `hcorr` (stated in the paper's own elementary-symmetric form: the inner
block sum is `Σ_{T ⊆ window n, |T| = 2b−ν+2n} ∏_{p∈T} ω(p)/p`).  It uses only B0/B2 carriers
(the peel `peel_term_nonneg`, `nu` multiplicativity, the ladder) and NO input outside the frozen
set, so it is a pure obligation for a follow-up; see `docs/blueprints/flags.md` (B3a).  The
`(2.16)` density inputs remain B3b's, exactly as before.
-/

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Salt.BrunLower

open BoundingSieve

/-! ## The `(2.11)` elementary symmetric bound -/

/-- **(2.11), H-R p.104.** For nonnegative weights `x` on a finite set `S`, the `k`-th
elementary symmetric function `∑_{T⊆S,|T|=k} ∏_{i∈T} x i` is at most `(∑ x)^k / k!`.  Proof:
the multinomial expansion `(∑ x)^k = ∑_{ν} multinomial·∏ x^ν` (`sum_pow_eq_sum_piAntidiag`)
has all terms `≥ 0`; the `0/1`-valued exponents (indicators of `k`-subsets) contribute exactly
`k!·∏_{i∈T} x i`, so dropping the rest gives `k!·e_k ≤ (∑ x)^k`. -/
lemma esymm_le {α : Type*} (S : Finset α) (x : α → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) (k : ℕ) :
    ∑ T ∈ S.powersetCard k, ∏ i ∈ T, x i ≤ (∑ i ∈ S, x i) ^ k / (k ! : ℝ) := by
  classical
  rw [le_div_iff₀ (by positivity : (0:ℝ) < (k ! : ℝ))]
  set g : (α → ℕ) → ℝ := fun ν => (Nat.multinomial S ν : ℝ) * ∏ i ∈ S, x i ^ (ν i) with hg
  set indic : Finset α → (α → ℕ) := fun T i => if i ∈ T then 1 else 0 with hindic
  have hgnn : ∀ ν, 0 ≤ g ν := fun ν =>
    mul_nonneg (by positivity) (Finset.prod_nonneg fun i hi => pow_nonneg (hx i hi) _)
  have hsum_indic : ∀ T ∈ S.powersetCard k, S.sum (indic T) = k := by
    intro T hT
    obtain ⟨hTS, hTc⟩ := mem_powersetCard.mp hT
    simp only [hindic, Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hTS, hTc, Nat.cast_id]
  have hinj : Set.InjOn indic (S.powersetCard k) := by
    intro T _ T' _ h
    ext a
    have := congrFun h a
    simp only [hindic] at this
    by_cases ha : a ∈ T <;> by_cases ha' : a ∈ T' <;> simp_all
  have hmem : ∀ T ∈ S.powersetCard k, indic T ∈ Finset.piAntidiag S k := by
    intro T hT
    rw [Finset.mem_piAntidiag]
    refine ⟨hsum_indic T hT, ?_⟩
    intro i hi
    have hiT : i ∈ T := by simp only [hindic] at hi; simpa using hi
    exact (mem_powersetCard.mp hT).1 hiT
  have hterm : ∀ T ∈ S.powersetCard k, (∏ i ∈ T, x i) * (k ! : ℝ) = g (indic T) := by
    intro T hT
    have hTS := (mem_powersetCard.mp hT).1
    have hmult : Nat.multinomial S (indic T) = k ! := by
      have hspec := Nat.multinomial_spec S (indic T)
      have hprod1 : (∏ i ∈ S, (indic T i)!) = 1 := by
        apply Finset.prod_eq_one; intro i _; simp only [hindic]; split <;> rfl
      rw [hprod1, one_mul, hsum_indic T hT] at hspec
      exact hspec
    have hprodx : (∏ i ∈ S, x i ^ (indic T i)) = ∏ i ∈ T, x i := by
      rw [show (∏ i ∈ S, x i ^ (indic T i)) = ∏ i ∈ S, (if i ∈ T then x i else 1) from
        Finset.prod_congr rfl (fun i _ => by simp only [hindic]; split <;> simp)]
      rw [← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hTS]
    simp only [hg, hmult, hprodx]
    ring
  calc (∑ T ∈ S.powersetCard k, ∏ i ∈ T, x i) * (k ! : ℝ)
      = ∑ T ∈ S.powersetCard k, g (indic T) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl hterm
    _ = ∑ ν ∈ (S.powersetCard k).image indic, g ν := (Finset.sum_image hinj).symm
    _ ≤ ∑ ν ∈ Finset.piAntidiag S k, g ν := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ν _ _ => hgnn ν)
        intro ν hν
        rw [Finset.mem_image] at hν
        obtain ⟨T, hT, rfl⟩ := hν
        exact hmem T hT
    _ = (∑ i ∈ S, x i) ^ k := by rw [Finset.sum_pow_eq_sum_piAntidiag]

/-! ## The block-inner bound in the sieve -/

/-- `s.nu` is nonnegative on the sifting primes (`p ∣ prodPrimes`), by `nu_pos_of_prime`. -/
lemma nu_nonneg_of_mem_primeFactors (s : BoundingSieve) {p : ℕ}
    (hp : p ∈ s.prodPrimes.primeFactors) : 0 ≤ s.nu p :=
  (s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)).le

/-- The inner block sum (the `(2b−ν+2n)`-th elementary symmetric function of `{ω(p)/p}` over the
window primes) is bounded by `(Σ_{p∈window} ω(p)/p)^k / k!`.  This is `(2.11)` instantiated at the
sieve density `s.nu = ω/·`. -/
lemma block_esymm_le (s : BoundingSieve) (window : ℕ → Finset ℕ)
    (hwin : ∀ n, window n ⊆ s.prodPrimes.primeFactors) (n k : ℕ) :
    ∑ T ∈ (window n).powersetCard k, ∏ p ∈ T, s.nu p
      ≤ (∑ p ∈ window n, s.nu p) ^ k / (k ! : ℝ) :=
  esymm_le (window n) (fun p => s.nu p)
    (fun _p hp => nu_nonneg_of_mem_primeFactors s (hwin n hp)) k

/-! ## The block-form endpoints (discharging B3's `hdecomp` from the p.104 display) -/

/-- **Upper block form** (H-R p.104 display, ν = 1): from the elementary-symmetric block
decomposition (`hcorr`) and `(2.11)`, the main sum is bounded by the power/factorial form that
node B3's `mainSum_le_of_upper` consumes as `hdecomp`. -/
theorem mainSum_le_blockForm (s : BoundingSieve) {Lam z : ℝ} {b r : ℕ}
    (window : ℕ → Finset ℕ) (hwin : ∀ n, window n ⊆ s.prodPrimes.primeFactors)
    (Wr : ℕ → ℝ) (hWrnn : ∀ n ∈ Finset.Icc 1 r, 0 ≤ Wr n)
    (hcorr : s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 1 b d then (1 : ℝ) else 0))
        ≤ W s * (1 + ∑ n ∈ Finset.Icc 1 r, Wr n *
            ∑ T ∈ (window n).powersetCard (2 * b - 1 + 2 * n), ∏ p ∈ T, s.nu p)) :
    s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 1 b d then (1 : ℝ) else 0))
      ≤ W s * (1 + ∑ n ∈ Finset.Icc 1 r,
          Wr n * (∑ p ∈ window n, s.nu p) ^ (2 * b - 1 + 2 * n)
            / ((2 * b - 1 + 2 * n)! : ℝ)) := by
  refine hcorr.trans ?_
  have hWpos : (0 : ℝ) ≤ W s := (W_pos s).le
  have hsum : (∑ n ∈ Finset.Icc 1 r, Wr n *
        ∑ T ∈ (window n).powersetCard (2 * b - 1 + 2 * n), ∏ p ∈ T, s.nu p)
      ≤ ∑ n ∈ Finset.Icc 1 r,
          Wr n * (∑ p ∈ window n, s.nu p) ^ (2 * b - 1 + 2 * n) / ((2 * b - 1 + 2 * n)! : ℝ) := by
    apply Finset.sum_le_sum
    intro n hn
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (block_esymm_le s window hwin n (2 * b - 1 + 2 * n)) (hWrnn n hn)
  exact mul_le_mul_of_nonneg_left (by linarith) hWpos

/-- **Lower block form** (H-R p.104 display, ν = 2): the load-bearing side.  From the
elementary-symmetric block decomposition (`hcorr`) and `(2.11)`, the power/factorial form that
node B3's `mainSum_ge_of_lower` consumes as `hdecomp`. -/
theorem mainSum_ge_blockForm (s : BoundingSieve) {Lam z : ℝ} {b r : ℕ}
    (window : ℕ → Finset ℕ) (hwin : ∀ n, window n ⊆ s.prodPrimes.primeFactors)
    (Wr : ℕ → ℝ) (hWrnn : ∀ n ∈ Finset.Icc 1 r, 0 ≤ Wr n)
    (hcorr : W s * (1 - ∑ n ∈ Finset.Icc 1 r, Wr n *
            ∑ T ∈ (window n).powersetCard (2 * b - 2 + 2 * n), ∏ p ∈ T, s.nu p)
        ≤ s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 2 b d then (1 : ℝ) else 0))) :
    W s * (1 - ∑ n ∈ Finset.Icc 1 r,
          Wr n * (∑ p ∈ window n, s.nu p) ^ (2 * b - 2 + 2 * n)
            / ((2 * b - 2 + 2 * n)! : ℝ))
      ≤ s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 2 b d then (1 : ℝ) else 0)) := by
  refine le_trans ?_ hcorr
  have hWpos : (0 : ℝ) ≤ W s := (W_pos s).le
  have hsum : (∑ n ∈ Finset.Icc 1 r, Wr n *
        ∑ T ∈ (window n).powersetCard (2 * b - 2 + 2 * n), ∏ p ∈ T, s.nu p)
      ≤ ∑ n ∈ Finset.Icc 1 r,
          Wr n * (∑ p ∈ window n, s.nu p) ^ (2 * b - 2 + 2 * n) / ((2 * b - 2 + 2 * n)! : ℝ) := by
    apply Finset.sum_le_sum
    intro n hn
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (block_esymm_le s window hwin n (2 * b - 2 + 2 * n)) (hWrnn n hn)
  exact mul_le_mul_of_nonneg_left (by linarith) hWpos

/-! ## Composed endpoints (consume B3, leaving only `(2.16)`-shaped + `hcorr`) -/

/-- **Upper main-term comparison from the block decomposition** (H-R (2.17), ν = 1).  Composes
`mainSum_le_blockForm` into B3's `mainSum_le_of_upper`: the only remaining hypotheses are the
`(2.16)`-shaped density inputs (`hWr`, `hps`, `hWrnn`) and the block-decomposition identity
`hcorr`. -/
theorem mainSum_le_of_upper' (s : BoundingSieve) {Lam z lam : ℝ} {b r : ℕ}
    (hb : 1 ≤ b) (hlam : 0 < lam) (h12 : lam * Real.exp (1 + lam) < 1)
    (window : ℕ → Finset ℕ) (hwin : ∀ n, window n ⊆ s.prodPrimes.primeFactors)
    (Wr : ℕ → ℝ) (hWrnn : ∀ n ∈ Finset.Icc 1 r, 0 ≤ Wr n)
    (hWr : ∀ n ∈ Finset.Icc 1 r, Wr n ≤ Real.exp (2 * (n : ℝ) * lam))
    (hps : ∀ n ∈ Finset.Icc 1 r, (∑ p ∈ window n, s.nu p) ≤ 2 * (n : ℝ) * lam)
    (hcorr : s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 1 b d then (1 : ℝ) else 0))
        ≤ W s * (1 + ∑ n ∈ Finset.Icc 1 r, Wr n *
            ∑ T ∈ (window n).powersetCard (2 * b - 1 + 2 * n), ∏ p ∈ T, s.nu p)) :
    s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 1 b d then (1 : ℝ) else 0))
      ≤ W s * (1 + 2 * lam ^ (2 * b + 1) * Real.exp (2 * lam)
          / (1 - lam ^ 2 * Real.exp (2 + 2 * lam))) :=
  mainSum_le_of_upper s hb hlam h12 Wr (fun n => ∑ p ∈ window n, s.nu p)
    (fun n => Finset.sum_nonneg fun _p hp => nu_nonneg_of_mem_primeFactors s (hwin n hp))
    hWr hps (mainSum_le_blockForm s window hwin Wr hWrnn hcorr)

/-- **Lower main-term comparison from the block decomposition** (H-R (2.17), ν = 2) — the
load-bearing side.  Composes `mainSum_ge_blockForm` into B3's `mainSum_ge_of_lower`. -/
theorem mainSum_ge_of_lower' (s : BoundingSieve) {Lam z lam : ℝ} {b r : ℕ}
    (hb : 1 ≤ b) (hlam : 0 < lam) (h12 : lam * Real.exp (1 + lam) < 1)
    (window : ℕ → Finset ℕ) (hwin : ∀ n, window n ⊆ s.prodPrimes.primeFactors)
    (Wr : ℕ → ℝ) (hWrnn : ∀ n ∈ Finset.Icc 1 r, 0 ≤ Wr n)
    (hWr : ∀ n ∈ Finset.Icc 1 r, Wr n ≤ Real.exp (2 * (n : ℝ) * lam))
    (hps : ∀ n ∈ Finset.Icc 1 r, (∑ p ∈ window n, s.nu p) ≤ 2 * (n : ℝ) * lam)
    (hcorr : W s * (1 - ∑ n ∈ Finset.Icc 1 r, Wr n *
            ∑ T ∈ (window n).powersetCard (2 * b - 2 + 2 * n), ∏ p ∈ T, s.nu p)
        ≤ s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 2 b d then (1 : ℝ) else 0))) :
    W s * (1 - 2 * lam ^ (2 * b) * Real.exp (2 * lam)
          / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)))
      ≤ s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 2 b d then (1 : ℝ) else 0)) :=
  mainSum_ge_of_lower s hb hlam h12 Wr (fun n => ∑ p ∈ window n, s.nu p)
    (fun n => Finset.sum_nonneg fun _p hp => nu_nonneg_of_mem_primeFactors s (hwin n hp))
    hWr hps (mainSum_ge_blockForm s window hwin Wr hWrnn hcorr)

end Salt.BrunLower
