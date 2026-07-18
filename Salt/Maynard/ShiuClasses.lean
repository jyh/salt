/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.ShiuSieve
import Salt.Maynard.ShiuGraded
import Salt.BV.DivisorSum

/-!
# ShiuClasses — the class assemblies S4-I, S4-III, S4-IV (wave W3)

For the greedy smooth-prefix decomposition `n = c·d` (`ShiuDecomp`) with the
scale thresholds `w` (the smooth budget) and `W ≤ w` (the secondary cut), the
τ-mass of each nondegenerate class in a reduced arithmetic progression is bounded
against the Shiu target grade `C·(z/φ(q))·log z`.

## What this file lands (wave W3)

* **S4-I** (`shiu_classI_le`) — the class-I assembly, **LANDED**.  Class I
  (`ρ = d.minFac > W`) has `d` free of primes `≤ W`, so `τ(d) ≤ 2^K` with the
  *fixed* `K = log z/log W = 80/α` (a `z`-independent constant at the skeleton
  scale); the main term collapses `(log w)²/log W ↦ log z`, and the `W³·w`-junk is
  absorbed by the modulus range.  This closes cleanly.

* **Shared infrastructure** (`tau_rough_le`, `exists_inv_residue`,
  `class_tau_sum_le_prod`, `inner_count_le`, `bigT_sum_split`) — LANDED and
  reusable: the greedy reindex, the CRT inverse residue, the fibre split, and the
  rough-count bridge.

* **S4-III / S4-IV — NOT LANDED (design-route gap, flagged).**  The skeleton's
  route for classes III/IV bounds `τ(d)` *pointwise* — `τ(d) ≤ A^{r+1}` with
  `A = 2^{80/α}` at roughness `v_{r+1}` — and pairs it with the unweighted
  `rough_count_in_ap_le`.  Summed over `r ≤ r_max = ⌊log w/(16 loglog w)⌋` the
  factor `A^{r+1}·exp(8√r·loglog v_r)` reaches `exp(Θ((loglog z)²))`, which is
  *super-polylog* (exceeds `(log z)^C` for every `C`) — so the r-sum overshoots the
  `log z` target even asymptotically.  (Dropping the AP constraint on `d` instead
  loses the `1/φ(q)` saving, which the tiny Rankin power gain `W^{-(1-σ)} = z^{-Θ(α)}`
  cannot repay.)  The honest fix needs a **τ-weighted rough count in AP**
  `Σ_{d≤Y, d≡b(q), d rough} τ(d) ≤ C·(Y/φ(q))·(log-grade)` — ShiuCore-strength for
  the `d`-variable, not among the landed stones.  See `docs/blueprints/flags.md`.

Each landed theorem is stated **parametrically** in the scales `z q a w W …` with
the defining scale hypotheses carried explicitly, so `S5` instantiates at the
skeleton's `w = z^{α/40}`, `W = w^{1/2}`, `K = 80/α`, `Kmain = α/20` (`α = 1/8000`).
The class-II reduction (its capped-power ingredients landed in `ShiuGraded`) and the
degenerate class are handled elsewhere; `S5` composes all classes into `ShiuCore`.

## Shared infrastructure

* `tau_rough_le` — for a `W`-rough `d ≤ z ≤ W^K`, `τ(d) ≤ 2^K` (the constant that
  frees the `d`-part of class I; via `τ ≤ 2^Ω` and `(W+1)^Ω ≤ d`).
* `exists_inv_residue` — for `(c,q)=1`, the fibre `{d : c·d ≡ a (q)}` is a single
  reduced residue class `d ≡ b (q)` with `(b,q)=1` (the CRT inverse, so the inner
  `d`-count is a genuine `rough_count_in_ap_le` instance).
* `class_tau_sum_le_prod` — the greedy reindex `n ↦ (c(n), d(n))`: the class τ-sum
  is bounded by the product sum over `(c,d)` (injective, `c·d = n` recovers `n`).
* `bigT_sum_split` / `inner_count_le` — the fibre split and the per-`c` `d`-count.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Omega

namespace Salt.Maynard

/-! ## Arithmetic helper: the constant τ-bound for rough cofactors -/

/-- `τ(m) ≤ 2^Ω(m)` (reproved locally to avoid an extra `Salt.Brun` import). -/
private lemma card_div_le_two_pow_Omega {m : ℕ} (hm : m ≠ 0) :
    m.divisors.card ≤ 2 ^ Ω m := by
  rw [Nat.card_divisors hm, cardFactors_eq_sum_factorization, Finsupp.sum,
    ← Nat.support_factorization]
  calc m.factorization.support.prod (fun p => m.factorization p + 1)
      ≤ m.factorization.support.prod (fun p => 2 ^ m.factorization p) := by
        apply Finset.prod_le_prod (fun _ _ => by omega)
        intro p _
        exact Nat.succ_le_of_lt Nat.lt_two_pow_self
    _ = 2 ^ (∑ p ∈ m.factorization.support, m.factorization p) := by
        rw [← Finset.prod_pow_eq_pow_sum]

/-- If every prime factor of `d ≠ 0` is `≥ W+1`, then `(W+1)^Ω(d) ≤ d`. -/
private lemma pow_Omega_le_of_rough {d W : ℕ} (hd : d ≠ 0)
    (hrough : ∀ p ∈ d.primeFactors, W + 1 ≤ p) : (W + 1) ^ Ω d ≤ d := by
  have hself : ∏ p ∈ d.primeFactors, p ^ (d.factorization p) = d := by
    rw [← Nat.support_factorization, ← Finsupp.prod]
    exact Nat.prod_factorization_pow_eq_self hd
  have hOmega : Ω d = ∑ p ∈ d.primeFactors, d.factorization p := by
    rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  rw [hOmega, ← Finset.prod_pow_eq_pow_sum]
  calc ∏ p ∈ d.primeFactors, (W + 1) ^ (d.factorization p)
      ≤ ∏ p ∈ d.primeFactors, p ^ (d.factorization p) :=
        Finset.prod_le_prod' (fun p hp => Nat.pow_le_pow_left (hrough p hp) _)
    _ = d := hself

/-- **The rough-cofactor constant bound.**  For `1 ≤ d ≤ z ≤ W^K` (`K,W ≥ 1`) with
`d` free of prime factors `≤ W`, `τ(d) ≤ 2^K`.  This is the constant that frees the
`d`-part in class I (and, at scale `v_{r+1}`, the `A^{r+1}` grade in class IV). -/
lemma tau_rough_le {d W K z : ℕ} (hW1 : 1 ≤ W) (hd1 : 1 ≤ d) (hdz : d ≤ z)
    (hz : z ≤ W ^ K) (hrough : ∀ p, p.Prime → p ≤ W → ¬ p ∣ d) :
    d.divisors.card ≤ 2 ^ K := by
  have hd0 : d ≠ 0 := by omega
  have hpf : ∀ p ∈ d.primeFactors, W + 1 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    by_contra h
    exact hrough p hpp (by omega) hpd
  have hΩ : Ω d ≤ K := by
    have hle : (W + 1) ^ (Ω d) ≤ W ^ K :=
      le_trans (pow_Omega_le_of_rough hd0 hpf) (le_trans hdz hz)
    have hWK : W ^ K ≤ (W + 1) ^ K := Nat.pow_le_pow_left (by omega) K
    have hfin : (W + 1) ^ (Ω d) ≤ (W + 1) ^ K := le_trans hle hWK
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < W + 1)).mp hfin
  calc d.divisors.card ≤ 2 ^ (Ω d) := card_div_le_two_pow_Omega hd0
    _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hΩ

/-! ## Arithmetic helper: the inverse residue class of a fixed cofactor -/

/-- **The CRT inverse residue.**  For `(c,q)=1` and `(a,q)=1`, the fibre
`{d : c·d ≡ a (q)}` is the single reduced residue class `d ≡ b (q)` with
`(b,q)=1` (`b = a·c⁻¹ mod q`).  Only the forward inclusion is needed: it lets the
inner `d`-count be a genuine `rough_count_in_ap_le` instance. -/
lemma exists_inv_residue {q c a : ℕ} (hq : 1 ≤ q) (hc : Nat.Coprime c q)
    (ha : Nat.Coprime a q) :
    ∃ b, b < q ∧ Nat.Coprime b q ∧ ∀ d : ℕ, (c * d) % q = a % q → d % q = b := by
  haveI : NeZero q := ⟨by omega⟩
  set u : ZMod q := (a : ZMod q) * (c : ZMod q)⁻¹ with hu
  refine ⟨u.val, ZMod.val_lt u, ?_, ?_⟩
  · rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    have hcinv : IsUnit ((c : ZMod q)⁻¹) :=
      IsUnit.of_mul_eq_one (c : ZMod q)
        (by rw [mul_comm]; exact ZMod.coe_mul_inv_eq_one c hc)
    exact ((ZMod.isUnit_iff_coprime a q).mpr ha).mul hcinv
  · intro d hd
    have h1 : ((c : ℕ) : ZMod q) * ((d : ℕ) : ZMod q) = ((a : ℕ) : ZMod q) := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]; exact hd
    have hcu : (c : ZMod q) * (c : ZMod q)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one c hc
    have hd2 : (d : ZMod q) = u := by
      rw [hu]
      calc (d : ZMod q) = (c : ZMod q) * (d : ZMod q) * (c : ZMod q)⁻¹ := by
            rw [mul_comm (c : ZMod q) (d : ZMod q), mul_assoc, hcu, mul_one]
        _ = (a : ZMod q) * (c : ZMod q)⁻¹ := by rw [h1]
    have hv := congrArg ZMod.val hd2
    rwa [ZMod.val_natCast] at hv

/-! ## The greedy reindex: class τ-sum ≤ product sum over `(c, d)` -/

open Classical in
/-- **The greedy reindex.**  The τ-mass of a class `{n ≤ z : n ≡ a (q) ∧ Npred n}`
is bounded by the product sum `Σ τ(c)·τ(d)` over pairs `(c,d)` with `c ≤ w`,
`c·d ≤ z`, `c·d ≡ a (q)`, `Cpred c`, `Dpred d` — because `n ↦ (c(n), d(n))` is
injective (`c·d = n` recovers `n`), lands in that pair set (via `hcov`), and
`τ(n) = τ(c)·τ(d)`.  `hcov` packages the class facts that `c = shiuC w n` and
`d = shiuD w n` satisfy the pair constraints. -/
theorem class_tau_sum_le_prod (z q a w : ℕ)
    (Npred Dpred : ℕ → Prop)
    (hcov : ∀ n, 1 ≤ n → n ≤ z → n % q = a → Npred n →
        1 ≤ shiuC w n ∧ shiuC w n ≤ w ∧ Dpred (shiuD w n)) :
    ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ Npred n),
        (n.divisors.card : ℝ)
      ≤ ∑ p ∈ ((Finset.Icc 1 w ×ˢ Finset.Icc 1 z).filter
          (fun p => p.1 * p.2 ≤ z ∧ (p.1 * p.2) % q = a ∧ Dpred p.2)),
          (p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ) := by
  set S := (Finset.Icc 1 z).filter (fun n => n % q = a ∧ Npred n) with hSdef
  set φ : ℕ → ℕ × ℕ := fun n => (shiuC w n, shiuD w n) with hφ
  set BigT := (Finset.Icc 1 w ×ˢ Finset.Icc 1 z).filter
    (fun p => p.1 * p.2 ≤ z ∧ (p.1 * p.2) % q = a ∧ Dpred p.2) with hBigT
  set G : ℕ × ℕ → ℝ := fun p => (p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ) with hG
  -- facts available for each `n ∈ S`
  have hmemS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ z ∧ n % q = a ∧ Npred n := by
    intro n hn
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hn
    exact ⟨hn.1.1, hn.1.2, hn.2.1, hn.2.2⟩
  -- Step 1: `τ(n) = G (φ n)` on `S`.
  have hval : ∀ n ∈ S, (n.divisors.card : ℝ) = G (φ n) := by
    intro n hn
    obtain ⟨hn1, _, _, _⟩ := hmemS n hn
    have hn0 : n ≠ 0 := by omega
    have htau := tau_mul_shiu hn0 w
    simp only [hG, hφ]
    rw [htau]; push_cast; ring
  -- Step 2: `φ` is injective on `S`.
  have hinj : Set.InjOn φ ↑S := by
    intro n hn m hm hnm
    simp only [Finset.mem_coe] at hn hm
    obtain ⟨hn1, _, _, _⟩ := hmemS n hn
    obtain ⟨hm1, _, _, _⟩ := hmemS m hm
    have hn0 : n ≠ 0 := by omega
    have hm0 : m ≠ 0 := by omega
    rw [hφ, Prod.mk.injEq] at hnm
    calc n = shiuC w n * shiuD w n := (shiuC_mul_shiuD hn0 w).symm
      _ = shiuC w m * shiuD w m := by rw [hnm.1, hnm.2]
      _ = m := shiuC_mul_shiuD hm0 w
  -- Step 3: `S.image φ ⊆ BigT`.
  have hsub : S.image φ ⊆ BigT := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨n, hn, rfl⟩ := hp
    obtain ⟨hn1, hnz, hnq, hnP⟩ := hmemS n hn
    have hn0 : n ≠ 0 := by omega
    obtain ⟨hc1, hcw, hDd⟩ := hcov n hn1 hnz hnq hnP
    have hd1 : 1 ≤ shiuD w n := shiuD_pos hn0 w
    have hcd : shiuC w n * shiuD w n = n := shiuC_mul_shiuD hn0 w
    have hdz : shiuD w n ≤ z := by
      have : shiuD w n ≤ shiuC w n * shiuD w n :=
        Nat.le_mul_of_pos_left _ hc1
      omega
    rw [hBigT, hφ, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hc1, hcw⟩, ⟨hd1, hdz⟩⟩, ?_, ?_, hDd⟩
    · rw [hcd]; exact hnz
    · rw [hcd]; exact hnq
  -- Step 4: assemble.
  calc ∑ n ∈ S, (n.divisors.card : ℝ)
      = ∑ n ∈ S, G (φ n) := Finset.sum_congr rfl hval
    _ = ∑ p ∈ S.image φ, G p := (Finset.sum_image hinj).symm
    _ ≤ ∑ p ∈ BigT, G p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)

/-! ## The inner cofactor count via `rough_count_in_ap_le` -/

open Classical in
/-- **The inner `d`-count.**  For a fixed prefix `c ≥ 1`, the number of `t`-rough
cofactors `d ≤ z` with `c·d ≤ z` and `c·d ≡ a (q)` is at most the rough count at
`y = z/c` — a genuine `rough_count_in_ap_le` instance in the inverse residue class
`d ≡ c⁻¹a (q)` (when `(c,q)=1`; the fibre is empty otherwise, since `(a,q)=1`
forces `(c,q)=1`). `hrc` is the instantiated `rough_count_in_ap_le` bound. -/
theorem inner_count_le (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hrc : ∀ y q a t : ℕ, 1 ≤ q → 2 ≤ t → Nat.Coprime a q →
      (((Finset.Icc 1 y).filter (fun m => m % q = a ∧
          ∀ p, p.Prime → p ≤ t → ¬ p ∣ m)).card : ℝ)
        ≤ C₀ * ((y : ℝ) / (q.totient : ℝ) / Real.log t + (t : ℝ) ^ 3))
    (z q a c t : ℕ) (hq : 1 ≤ q) (hc1 : 1 ≤ c) (ht : 2 ≤ t) (ha : Nat.Coprime a q) :
    (((Finset.Icc 1 z).filter (fun d => c * d ≤ z ∧ (c * d) % q = a ∧
        ∀ p, p.Prime → p ≤ t → ¬ p ∣ d)).card : ℝ)
      ≤ C₀ * ((z : ℝ) / c / (q.totient : ℝ) / Real.log t + (t : ℝ) ^ 3) := by
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc1
  set D := (Finset.Icc 1 z).filter (fun d => c * d ≤ z ∧ (c * d) % q = a ∧
      ∀ p, p.Prime → p ≤ t → ¬ p ∣ d) with hDdef
  by_cases hcop : Nat.Coprime c q
  · obtain ⟨b, hblt, hbcop, hbimp⟩ := exists_inv_residue hq hcop ha
    set y := z / c with hy
    have hsub : D ⊆ (Finset.Icc 1 y).filter (fun m => m % q = b ∧
        ∀ p, p.Prime → p ≤ t → ¬ p ∣ m) := by
      intro d hd
      rw [hDdef, Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, _⟩, hcdz, hcda, hrough⟩ := hd
      rw [Finset.mem_filter, Finset.mem_Icc]
      have haq : a % q = a := by
        have : (c * d) % q < q := Nat.mod_lt _ (by omega)
        rw [hcda] at this; exact Nat.mod_eq_of_lt this
      refine ⟨⟨hd1, ?_⟩, ?_, hrough⟩
      · rw [hy, Nat.le_div_iff_mul_le (by omega : 0 < c), Nat.mul_comm]; exact hcdz
      · exact hbimp d (by rw [haq]; exact hcda)
    have hcard : (D.card : ℝ) ≤ (((Finset.Icc 1 y).filter (fun m => m % q = b ∧
        ∀ p, p.Prime → p ≤ t → ¬ p ∣ m)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hyz : (y : ℝ) ≤ (z : ℝ) / c := Nat.cast_div_le
    calc (D.card : ℝ)
        ≤ (((Finset.Icc 1 y).filter (fun m => m % q = b ∧
            ∀ p, p.Prime → p ≤ t → ¬ p ∣ m)).card : ℝ) := hcard
      _ ≤ C₀ * ((y : ℝ) / (q.totient : ℝ) / Real.log t + (t : ℝ) ^ 3) := hrc y q b t hq ht hbcop
      _ ≤ C₀ * ((z : ℝ) / c / (q.totient : ℝ) / Real.log t + (t : ℝ) ^ 3) := by
          gcongr
  · have hempty : D = ∅ := by
      rw [hDdef, Finset.filter_eq_empty_iff]
      intro d _ hcon
      obtain ⟨_, hcda, _⟩ := hcon
      apply hcop
      have hcdq : Nat.Coprime (c * d) q := by
        unfold Nat.Coprime
        rw [Nat.gcd_comm, Nat.gcd_rec, hcda]; exact ha
      exact Nat.Coprime.coprime_dvd_left (dvd_mul_right c d) hcdq
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    have : (0 : ℝ) ≤ C₀ * ((z : ℝ) / c / (q.totient : ℝ) / Real.log t + (t : ℝ) ^ 3) := by
      apply mul_nonneg hC₀.le
      have : (0 : ℝ) ≤ (z : ℝ) / c / (q.totient : ℝ) / Real.log t := by positivity
      positivity
    linarith

/-! ## The product-sum split: group by the smooth prefix -/

open Classical in
/-- **The fibre split.**  A sum of `g(c)` over the filtered `(c,d)` product groups
as `Σ_c g(c)·(fibre count)` — the standard `sum_filter ∘ sum_product` reorganization.
Used to turn the reindexed product sum into `Σ_c τ(c)·#{d-fibre}`, where the inner
count is discharged by `inner_count_le`. -/
theorem bigT_sum_split (z q a w : ℕ) (Dpred : ℕ → Prop) (g : ℕ → ℝ) :
    ∑ p ∈ ((Finset.Icc 1 w ×ˢ Finset.Icc 1 z).filter
        (fun p => p.1 * p.2 ≤ z ∧ (p.1 * p.2) % q = a ∧ Dpred p.2)), g p.1
      = ∑ c ∈ Finset.Icc 1 w, g c *
          (((Finset.Icc 1 z).filter
            (fun d => c * d ≤ z ∧ (c * d) % q = a ∧ Dpred d)).card : ℝ) := by
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro c _
  dsimp only
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ## S4-I — the class-I assembly -/

open Classical in
/-- **S4-I (the class-I assembly).**  For the greedy decomposition `n = c·d` with
budget `w` and secondary cut `W`, the τ-mass of class I (`ρ = d.minFac > W`, so `d`
is `W`-rough) in the reduced progression `n ≡ a (q)` is bounded by
`C·2^K·(Kmain+1)·(z/φ(q))·log z`, where:
* `z ≤ W^K` gives the *fixed* constant `τ(d) ≤ 2^K` (the class-I `d`-part is free —
  at the skeleton scale `K = log z/log W = 80/α` is a constant);
* `(log w)² ≤ Kmain·(log W·log z)` collapses the smooth Rankin main term
  `(log w)²/log W` to `Kmain·log z`;
* the `W³·w`-junk is absorbed by the modulus hypothesis `W³·w·(1+log w)·q ≤ z·log z`.

`S5` instantiates at `w = z^{α/40}`, `W = z^{α/80}`, `K = 80/α`, `Kmain = α/20`. -/
theorem shiu_classI_le :
    ∃ (C : ℝ) (w₀ : ℕ), 0 < C ∧ ∀ (z q a w W K : ℕ) (Kmain : ℝ),
      w₀ ≤ w → 2 ≤ W → 1 ≤ q → 2 ≤ z → Nat.Coprime a q →
      z ≤ W ^ K → 0 ≤ Kmain →
      (Real.log w) ^ 2 ≤ Kmain * (Real.log W * Real.log z) →
      (W : ℝ) ^ 3 * (w : ℝ) * (1 + Real.log w) * (q : ℝ) ≤ (z : ℝ) * Real.log z →
      (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassI w W n),
          (n.divisors.card : ℝ))
        ≤ C * (2 : ℝ) ^ K * (Kmain + 1) * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
  obtain ⟨C₁, v₀, hC₁, hsmooth⟩ := sum_tau_smooth_div_log_le
  obtain ⟨C₀, hC₀, hrc⟩ := rough_count_in_ap_le
  refine ⟨C₀ * (C₁ ^ 2 + 1), max v₀ 2, by positivity, ?_⟩
  intro z q a w W K Kmain hw hW hq hz2 ha hzWK hKm hmain hjunk
  have hw2 : 2 ≤ w := le_trans (le_max_right _ _) hw
  have hv0 : v₀ ≤ w := le_trans (le_max_left _ _) hw
  have hw1 : 1 ≤ w := by omega
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlogW : (0 : ℝ) < Real.log W := Real.log_pos (by exact_mod_cast (by omega : 1 < W))
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hlogw0 : (0 : ℝ) ≤ Real.log w := Real.log_nonneg (by exact_mod_cast hw1)
  set g : ℕ → ℝ := fun c => (c.divisors.card : ℝ) * (2 : ℝ) ^ K with hg
  -- (1) the greedy reindex, with class-I facts.
  have hcov : ∀ n, 1 ≤ n → n ≤ z → n % q = a → shiuClassI w W n →
      1 ≤ shiuC w n ∧ shiuC w n ≤ w ∧
      (fun d => ∀ p, p.Prime → p ≤ W → ¬ p ∣ d) (shiuD w n) := by
    intro n hn1 _ _ hcls
    have hn0 : n ≠ 0 := by omega
    obtain ⟨_, hρ⟩ := hcls
    refine ⟨shiuC_pos hn0 w, shiuC_le hw1 n, ?_⟩
    intro p hpp hpW hpd
    have hmf : (shiuD w n).minFac ≤ p := Nat.minFac_le_of_dvd hpp.two_le hpd
    omega
  have hreindex := class_tau_sum_le_prod z q a w (shiuClassI w W)
    (fun d => ∀ p, p.Prime → p ≤ W → ¬ p ∣ d) hcov
  -- (2) `τ(d) ≤ 2^K` on the product set, then fibre-split.
  set BigT := (Finset.Icc 1 w ×ˢ Finset.Icc 1 z).filter
    (fun p => p.1 * p.2 ≤ z ∧ (p.1 * p.2) % q = a ∧
      (fun d => ∀ p, p.Prime → p ≤ W → ¬ p ∣ d) p.2) with hBigT
  have hprodle : ∑ p ∈ BigT, (p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ)
      ≤ ∑ p ∈ BigT, g p.1 := by
    apply Finset.sum_le_sum
    intro p hp
    rw [hBigT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨_, ⟨hd1, hdz⟩⟩, _, _, hrough⟩ := hp
    have htaud : (p.2.divisors.card : ℝ) ≤ (2 : ℝ) ^ K := by
      have := tau_rough_le (by omega : 1 ≤ W) hd1 hdz hzWK hrough
      calc (p.2.divisors.card : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast this
        _ = (2 : ℝ) ^ K := by push_cast; ring
    rw [hg]
    exact mul_le_mul_of_nonneg_left htaud (by positivity)
  have hsplit := bigT_sum_split z q a w
    (fun d => ∀ p, p.Prime → p ≤ W → ¬ p ∣ d) g
  -- (3) the per-`c` bound: fibre count via `inner_count_le`, weighted by `τ(c)`.
  set h1 : ℝ := (2 : ℝ) ^ K * C₀ * (z : ℝ) / (q.totient : ℝ) / Real.log W with hh1
  set h2 : ℝ := (2 : ℝ) ^ K * C₀ * (W : ℝ) ^ 3 with hh2
  have hpercterm : ∀ c ∈ Finset.Icc 1 w,
      g c * (((Finset.Icc 1 z).filter (fun d => c * d ≤ z ∧ (c * d) % q = a ∧
          (fun dd => ∀ p, p.Prime → p ≤ W → ¬ p ∣ dd) d)).card : ℝ)
        ≤ h1 * ((c.divisors.card : ℝ) / c) + h2 * (c.divisors.card : ℝ) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    have hc1 : 1 ≤ c := hc.1
    have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc1
    have hcardle : (((Finset.Icc 1 z).filter (fun d => c * d ≤ z ∧ (c * d) % q = a ∧
          (fun dd => ∀ p, p.Prime → p ≤ W → ¬ p ∣ dd) d)).card : ℝ)
        ≤ C₀ * ((z : ℝ) / c / (q.totient : ℝ) / Real.log W + (W : ℝ) ^ 3) :=
      inner_count_le C₀ hC₀ hrc z q a c W hq hc1 hW ha
    have hgnn : (0 : ℝ) ≤ g c := by rw [hg]; positivity
    calc g c * (((Finset.Icc 1 z).filter (fun d => c * d ≤ z ∧ (c * d) % q = a ∧
            (fun dd => ∀ p, p.Prime → p ≤ W → ¬ p ∣ dd) d)).card : ℝ)
        ≤ g c * (C₀ * ((z : ℝ) / c / (q.totient : ℝ) / Real.log W + (W : ℝ) ^ 3)) :=
          mul_le_mul_of_nonneg_left hcardle hgnn
      _ = h1 * ((c.divisors.card : ℝ) / c) + h2 * (c.divisors.card : ℝ) := by
          rw [hg, hh1, hh2]; ring
  -- (4) sum the per-`c` bound; plug the two smooth sums.
  have hsmoothsum : ∑ c ∈ Finset.Icc 1 w, (c.divisors.card : ℝ) / c ≤ (C₁ * Real.log w) ^ 2 := by
    have hfilter : (Finset.Icc 1 w).filter (fun c => ∀ p ∈ c.primeFactors, p ≤ w)
        = Finset.Icc 1 w := by
      apply Finset.filter_true_of_mem
      intro c hc p hp
      rw [Finset.mem_Icc] at hc
      exact le_trans (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)) hc.2
    have := hsmooth w w hv0
    rw [hfilter] at this
    exact this
  have htausum : ∑ c ∈ Finset.Icc 1 w, (c.divisors.card : ℝ) ≤ (w : ℝ) * (1 + Real.log w) :=
    Salt.BV.sum_card_divisors_le w hw1
  -- assemble the chain.
  have hchain :
      ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassI w W n), (n.divisors.card : ℝ)
        ≤ h1 * (C₁ * Real.log w) ^ 2 + h2 * ((w : ℝ) * (1 + Real.log w)) := by
    calc ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassI w W n),
            (n.divisors.card : ℝ)
        ≤ ∑ p ∈ BigT, (p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ) := by
          convert hreindex using 2
          ext a
          simp only [Finset.mem_filter]
      _ ≤ ∑ p ∈ BigT, g p.1 := hprodle
      _ = ∑ c ∈ Finset.Icc 1 w, g c *
            (((Finset.Icc 1 z).filter (fun d => c * d ≤ z ∧ (c * d) % q = a ∧
              (fun dd => ∀ p, p.Prime → p ≤ W → ¬ p ∣ dd) d)).card : ℝ) :=
          hsplit
      _ ≤ ∑ c ∈ Finset.Icc 1 w, (h1 * ((c.divisors.card : ℝ) / c) + h2 * (c.divisors.card : ℝ)) :=
          Finset.sum_le_sum hpercterm
      _ = h1 * (∑ c ∈ Finset.Icc 1 w, (c.divisors.card : ℝ) / c)
            + h2 * (∑ c ∈ Finset.Icc 1 w, (c.divisors.card : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ h1 * (C₁ * Real.log w) ^ 2 + h2 * ((w : ℝ) * (1 + Real.log w)) := by
          have hh1nn : (0 : ℝ) ≤ h1 := by rw [hh1]; positivity
          have hh2nn : (0 : ℝ) ≤ h2 := by rw [hh2]; positivity
          gcongr
  -- (5) discharge the scale hypotheses into the target grade.
  refine le_trans hchain ?_
  have hzφnn : (0 : ℝ) ≤ (z : ℝ) / (q.totient : ℝ) := by positivity
  -- Piece 1: `h1·(C₁ log w)² ≤ 2^K·C₀·C₁²·Kmain·(z/φq)·log z`.
  have hpiece1 : h1 * (C₁ * Real.log w) ^ 2
      ≤ (2 : ℝ) ^ K * C₀ * C₁ ^ 2 * Kmain * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
    have hkey : (Real.log w) ^ 2 / Real.log W ≤ Kmain * Real.log z := by
      rw [div_le_iff₀ hlogW]
      calc (Real.log w) ^ 2 ≤ Kmain * (Real.log W * Real.log z) := hmain
        _ = Kmain * Real.log z * Real.log W := by ring
    have hexpand : h1 * (C₁ * Real.log w) ^ 2
        = (2 : ℝ) ^ K * C₀ * C₁ ^ 2 * ((z : ℝ) / (q.totient : ℝ))
            * ((Real.log w) ^ 2 / Real.log W) := by
      rw [hh1]; ring
    rw [hexpand]
    have hfac : (0 : ℝ) ≤ (2 : ℝ) ^ K * C₀ * C₁ ^ 2 * ((z : ℝ) / (q.totient : ℝ)) := by
      positivity
    calc (2 : ℝ) ^ K * C₀ * C₁ ^ 2 * ((z : ℝ) / (q.totient : ℝ))
          * ((Real.log w) ^ 2 / Real.log W)
        ≤ (2 : ℝ) ^ K * C₀ * C₁ ^ 2 * ((z : ℝ) / (q.totient : ℝ)) * (Kmain * Real.log z) :=
          mul_le_mul_of_nonneg_left hkey hfac
      _ = (2 : ℝ) ^ K * C₀ * C₁ ^ 2 * Kmain * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by ring
  -- Piece 2: `h2·w(1+log w) ≤ 2^K·C₀·(z/φq)·log z`.
  have hpiece2 : h2 * ((w : ℝ) * (1 + Real.log w))
      ≤ (2 : ℝ) ^ K * C₀ * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
    have hqW : (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w))
        ≤ (z : ℝ) / (q.totient : ℝ) * Real.log z := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hφpos]
      have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
      have hann : (0 : ℝ) ≤ (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w)) := by
        have : (0 : ℝ) ≤ 1 + Real.log w := by linarith [hlogw0]
        positivity
      calc (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w)) * (q.totient : ℝ)
          ≤ (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w)) * (q : ℝ) :=
            mul_le_mul_of_nonneg_left hφq hann
      _ = (W : ℝ) ^ 3 * (w : ℝ) * (1 + Real.log w) * (q : ℝ) := by ring
      _ ≤ (z : ℝ) * Real.log z := hjunk
    calc h2 * ((w : ℝ) * (1 + Real.log w))
        = (2 : ℝ) ^ K * C₀ * ((W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w))) := by rw [hh2]; ring
      _ ≤ (2 : ℝ) ^ K * C₀ * ((z : ℝ) / (q.totient : ℝ) * Real.log z) :=
          mul_le_mul_of_nonneg_left hqW (by positivity)
      _ = (2 : ℝ) ^ K * C₀ * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by ring
  -- combine the two pieces into `C·2^K·(Kmain+1)·(z/φq)·log z`.
  have hcombine :
      (2 : ℝ) ^ K * C₀ * C₁ ^ 2 * Kmain * ((z : ℝ) / (q.totient : ℝ)) * Real.log z
        + (2 : ℝ) ^ K * C₀ * ((z : ℝ) / (q.totient : ℝ)) * Real.log z
      ≤ C₀ * (C₁ ^ 2 + 1) * (2 : ℝ) ^ K * (Kmain + 1)
          * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
    have hbase : (0 : ℝ) ≤ (2 : ℝ) ^ K * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
      positivity
    have hcoef : C₀ * C₁ ^ 2 * Kmain + C₀ ≤ C₀ * (C₁ ^ 2 + 1) * (Kmain + 1) := by
      nlinarith [sq_nonneg C₁, hKm, hC₀.le, mul_nonneg hC₀.le (sq_nonneg C₁)]
    nlinarith [mul_le_mul_of_nonneg_right hcoef hbase, hbase]
  calc h1 * (C₁ * Real.log w) ^ 2 + h2 * ((w : ℝ) * (1 + Real.log w))
      ≤ (2 : ℝ) ^ K * C₀ * C₁ ^ 2 * Kmain * ((z : ℝ) / (q.totient : ℝ)) * Real.log z
          + (2 : ℝ) ^ K * C₀ * ((z : ℝ) / (q.totient : ℝ)) * Real.log z :=
        add_le_add hpiece1 hpiece2
    _ ≤ C₀ * (C₁ ^ 2 + 1) * (2 : ℝ) ^ K * (Kmain + 1)
          * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := hcombine

end Salt.Maynard
