/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.ShiuTuned
import Salt.Maynard.ShiuClasses
import Salt.Maynard.ShiuGraded
import Salt.Maynard.ShiuClose
import Salt.Maynard.ShiuBlocks

/-!
# ShiuFinal — the four per-class assemblies + the S5 composition (wave W5)

This file closes the `N-SHIU-CORE` rung: `sum_tau_in_ap_le : ShiuCore`.  All the
analytic stones landed in earlier waves (`ShiuTuned` NEW-1/NEW-2, `ShiuClasses`
S4-I + infra, `ShiuGraded` capped-power sums, `ShiuClose` W4-1 + the class-II
reduction + the degenerate bound); this file is the **composition** per the
SHIU-W4 recipe (`docs/blueprints/flags.md`).

## The pinned normalization (SHIU-W4)

`α = 1/8000`, `w = z^{α/3}` (budget), `W = z^{α/6}` (cut), so `w = W²` exactly
(what `classII_dvd_cappedPow` needs).  NEW-1's tuning reference is the *derived*
`z̃ = w = z^{α/3}` with `log z̃ = 2·log W = (α/3)·log z`; `v_r = z̃^{1/r}`.  The
III/IV split is at `P₀ = log z`.

## What this file lands (wave W5)

* **Class II** (`shiu_classII_le`) — the class-II assembly, via the landed
  reduction `classII_dvd_cappedPow` fibred over the prime `ρ ≤ W`, the crude
  `τ ≤ Cε·z^ε`, and the capped-power inverse sum `sum_cappedPow_inv_le`.
-/

open Finset

namespace Salt.Maynard

/-! ## Two elementary composition helpers -/

/-- **The union sum bound** for a nonnegative summand: the sum over a `biUnion` is
at most the double sum over the index and fibre.  (Mathlib has `card_biUnion_le`
but no ready `sum_biUnion_le`; this is the real-valued nonneg analogue.) -/
theorem sum_biUnion_le_of_nonneg {ι M : Type*} [DecidableEq M] (s : Finset ι)
    (t : ι → Finset M) {f : M → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have hunion : ∑ x ∈ t i ∪ s.biUnion t, f x
        ≤ ∑ x ∈ t i, f x + ∑ x ∈ s.biUnion t, f x := by
      have hkey := Finset.sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := f)
      have hinter : (0 : ℝ) ≤ ∑ x ∈ t i ∩ s.biUnion t, f x :=
        Finset.sum_nonneg (fun x _ => hf x)
      linarith
    calc ∑ x ∈ t i ∪ s.biUnion t, f x
        ≤ ∑ x ∈ t i, f x + ∑ x ∈ s.biUnion t, f x := hunion
      _ ≤ ∑ x ∈ t i, f x + ∑ i ∈ s, ∑ x ∈ t i, f x := by linarith [ih]

/-- **The divisibility-in-progression count.**  For `K ≥ 1`, `q ≥ 1`, `(a,q) = 1`,
the number of `n ∈ [1,z]` with `n ≡ a (q)` and `K ∣ n` is at most `z/(K·q) + 1`.
Reindex `n = K·m` (`m ≤ z/K`); the residue condition `(K·m) ≡ a (q)` fixes `m`'s
class `m ≡ K⁻¹a (q)` when `(K,q)=1` (`exists_inv_residue`), and the set is empty
otherwise (a shared prime of `K,q` would divide `a`).  `card_ap_le` closes it. -/
theorem divis_ap_count_le {q a z K : ℕ} (hq : 1 ≤ q) (hK : 1 ≤ K)
    (ha : Nat.Coprime a q) :
    (((Finset.Icc 1 z).filter (fun n => n % q = a ∧ K ∣ n)).card : ℝ)
      ≤ (z : ℝ) / K / q + 1 := by
  classical
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hKpos0 : (0 : ℕ) < K := by omega
  set D := (Finset.Icc 1 z).filter (fun n => n % q = a ∧ K ∣ n) with hD
  by_cases hcop : Nat.Coprime K q
  · obtain ⟨b, hblt, hbcop, hbimp⟩ := exists_inv_residue hq hcop ha
    set T := (Finset.Icc 1 (z / K)).filter (fun m => m % q = b) with hT
    have hcard : D.card ≤ T.card := by
      apply Finset.card_le_card_of_injOn (fun n => n / K)
      · intro n hn
        simp only [hD, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
        obtain ⟨⟨hn1, hnz⟩, hna, hKn⟩ := hn
        obtain ⟨m, rfl⟩ := hKn
        have hmK : K * m / K = m := Nat.mul_div_cancel_left m hKpos0
        simp only [hT, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, hmK]
        have hm1 : 1 ≤ m := by nlinarith [hn1, hKpos0]
        refine ⟨⟨hm1, ?_⟩, ?_⟩
        · rw [Nat.le_div_iff_mul_le hKpos0, Nat.mul_comm]; exact hnz
        · have haq : a % q = a := by
            have hlt : (K * m) % q < q := Nat.mod_lt _ (by omega)
            rw [hna] at hlt; exact Nat.mod_eq_of_lt hlt
          exact hbimp m (by rw [haq]; exact hna)
      · intro n₁ h1 n₂ h2 heq
        simp only [hD, Finset.mem_coe, Finset.mem_filter] at h1 h2
        obtain ⟨_, _, hK1⟩ := h1
        obtain ⟨_, _, hK2⟩ := h2
        obtain ⟨m1, rfl⟩ := hK1
        obtain ⟨m2, rfl⟩ := hK2
        simp only [Nat.mul_div_cancel_left m1 hKpos0, Nat.mul_div_cancel_left m2 hKpos0] at heq
        rw [heq]
    calc (D.card : ℝ)
        ≤ (T.card : ℝ) := by exact_mod_cast hcard
      _ ≤ ((z / K : ℕ) : ℝ) / q + 1 := card_ap_le hq b
      _ ≤ (z : ℝ) / K / q + 1 := by
          have hle : ((z / K : ℕ) : ℝ) ≤ (z : ℝ) / K := Nat.cast_div_le
          gcongr
  · have hempty : D = ∅ := by
      rw [hD, Finset.filter_eq_empty_iff]
      intro n _ hcon
      obtain ⟨hna, hKn⟩ := hcon
      apply hcop
      have hgcd : Nat.gcd n q = 1 := by
        rw [Nat.gcd_comm, Nat.gcd_rec, hna]; exact ha
      exact Nat.Coprime.coprime_dvd_left hKn hgcd
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

/-! ## Class II — the assembly (via the landed capped-power reduction) -/

/-- **Class II (the assembly).**  For the greedy decomposition `n = c·d` with budget
`w ≥ W²` and cut `W ≥ 4`, every class-II integer `n` (`ρ = d.minFac ≤ W`, `c ≤ W`)
is divisible by `cappedPow W ρ` (`classII_dvd_cappedPow`).  Fibring over the prime
`ρ ≤ W`, weighting by the crude `τ(n) ≤ Cε·z^ε`, and counting the divisibility class
in the progression (`divis_ap_count_le`), the capped-power inverse sum
(`sum_cappedPow_inv_le`, `≤ 4/√W`) closes the raw bound:

    Σ_{II, n≡a(q)} τ(n) ≤ Cε·z^ε·( (z/q)·(4/√W) + W ).

The main term is `4·Cε·z^{1+ε}/(q·√W)` (the `z/(K_p·q)` count summed via `Σ 1/K_p
≤ 4/√W`); the `+W` boundary is the `π(W)` off-count of the `+1` per prime.  At the
skeleton scale `ε = α/24`, `W = z^{α/6}`, both fold under `(z/φq)·log z` — the
S5-level fold (`z^ε/√W = z^{−α/24} ≤ 1`, `z^ε·W = z^{5α/24} ≤ z^α`). -/
theorem shiu_classII_le {z q a w W : ℕ} (ε Cε : ℝ)
    (hq : 1 ≤ q) (hW : 4 ≤ W) (hwW : W ^ 2 ≤ w) (ha : Nat.Coprime a q)
    (hCε : 0 < Cε) (hε : 0 ≤ ε)
    (htau : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ Cε * (n : ℝ) ^ ε) :
    (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassII w W n),
        (n.divisors.card : ℝ))
      ≤ Cε * (z : ℝ) ^ ε * ((z : ℝ) / q * (4 / Real.sqrt W) + (W : ℝ)) := by
  classical
  set P := (Finset.range (W + 1)).filter Nat.Prime with hP
  set t : ℕ → Finset ℕ := fun p => (Finset.Icc 1 z).filter
    (fun n => n % q = a ∧ cappedPow W p ∣ n) with ht
  set A := (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassII w W n) with hA
  have hCznn : (0 : ℝ) ≤ Cε * (z : ℝ) ^ ε := by positivity
  -- #P ≤ W
  have hPcard : (P.card : ℝ) ≤ (W : ℝ) := by
    have h1 : P ⊆ Finset.Icc 2 W := by
      intro p hp
      rw [hP, Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_Icc]; exact ⟨hp.2.two_le, by omega⟩
    have h2 : P.card ≤ (Finset.Icc 2 W).card := Finset.card_le_card h1
    have h3 : (Finset.Icc 2 W).card = W - 1 := by rw [Nat.card_Icc]; omega
    calc (P.card : ℝ) ≤ ((W - 1 : ℕ) : ℝ) := by rw [← h3]; exact_mod_cast h2
      _ ≤ (W : ℝ) := by exact_mod_cast (by omega : W - 1 ≤ W)
  -- Step 1: A ⊆ P.biUnion t (each class-II n lies in the ρ-fibre).
  have hAsub : A ⊆ P.biUnion t := by
    intro n hn
    rw [hA, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnz⟩, hna, hcls⟩ := hn
    have hn0 : n ≠ 0 := by omega
    obtain ⟨hd1, hρW, _hcW⟩ := hcls
    have hρp : ((shiuD w n).minFac).Prime := Nat.minFac_prime (by omega)
    have hdvd : cappedPow W ((shiuD w n).minFac) ∣ n :=
      classII_dvd_cappedPow hn0 (by omega : 2 ≤ W) hwW ⟨hd1, hρW, _hcW⟩
    rw [Finset.mem_biUnion]
    refine ⟨(shiuD w n).minFac, ?_, ?_⟩
    · rw [hP, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hρp⟩
    · simp only [ht, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hn1, hnz⟩, hna, hdvd⟩
  -- Step 3: the per-prime bound.
  have hstep3 : ∀ p ∈ P, ∑ n ∈ t p, (n.divisors.card : ℝ)
      ≤ Cε * (z : ℝ) ^ ε * ((z : ℝ) / (cappedPow W p) / q + 1) := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_range] at hp
    have hpp : p.Prime := hp.2
    have hK1 : 1 ≤ cappedPow W p := by rw [cappedPow]; exact Nat.one_le_pow _ _ hpp.pos
    calc ∑ n ∈ t p, (n.divisors.card : ℝ)
        ≤ ∑ _n ∈ t p, Cε * (z : ℝ) ^ ε := by
          apply Finset.sum_le_sum
          intro n hn
          simp only [ht, Finset.mem_filter, Finset.mem_Icc] at hn
          obtain ⟨⟨hn1, hnz⟩, _⟩ := hn
          calc (n.divisors.card : ℝ) ≤ Cε * (n : ℝ) ^ ε := htau n hn1
            _ ≤ Cε * (z : ℝ) ^ ε := by
                apply mul_le_mul_of_nonneg_left _ hCε.le
                exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnz) hε
      _ = (Cε * (z : ℝ) ^ ε) * ((t p).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (Cε * (z : ℝ) ^ ε) * ((z : ℝ) / (cappedPow W p) / q + 1) := by
          apply mul_le_mul_of_nonneg_left _ hCznn
          simp only [ht]
          exact divis_ap_count_le hq hK1 ha
  -- The fold over primes.
  have hfold : ∑ p ∈ P, Cε * (z : ℝ) ^ ε * ((z : ℝ) / (cappedPow W p) / q + 1)
      ≤ Cε * (z : ℝ) ^ ε * ((z : ℝ) / q * (4 / Real.sqrt W) + (W : ℝ)) := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hCznn
    rw [Finset.sum_add_distrib]
    have hsum1 : ∑ p ∈ P, (z : ℝ) / (cappedPow W p) / q
        ≤ (z : ℝ) / q * (4 / Real.sqrt W) := by
      have heq : ∑ p ∈ P, (z : ℝ) / (cappedPow W p) / q
          = (z : ℝ) / q * ∑ p ∈ P, (1 : ℝ) / (cappedPow W p) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
      rw [heq]
      exact mul_le_mul_of_nonneg_left (sum_cappedPow_inv_le hW) (by positivity)
    have hsum2 : ∑ _p ∈ P, (1 : ℝ) ≤ (W : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact hPcard
    linarith [hsum1, hsum2]
  -- Assemble.
  calc ∑ n ∈ A, (n.divisors.card : ℝ)
      ≤ ∑ n ∈ P.biUnion t, (n.divisors.card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hAsub (fun n _ _ => by positivity)
    _ ≤ ∑ p ∈ P, ∑ n ∈ t p, (n.divisors.card : ℝ) :=
        sum_biUnion_le_of_nonneg P t (fun x => by positivity)
    _ ≤ ∑ p ∈ P, Cε * (z : ℝ) ^ ε * ((z : ℝ) / (cappedPow W p) / q + 1) :=
        Finset.sum_le_sum hstep3
    _ ≤ Cε * (z : ℝ) ^ ε * ((z : ℝ) / q * (4 / Real.sqrt W) + (W : ℝ)) := hfold

/-! ## Class III infrastructure: a smoothness-carrying reindex + the trivial d-count

The class-I template (`class_tau_sum_le_prod` / `bigT_sum_split`) loses the
`c`-smoothness in the reindex; classes III/IV need it (the Rankin decay lives on
the smooth prefix).  These primed variants carry the `c`-domain `Sc` as a general
`Finset` so the caller can filter it by the `P₀`-smooth ∧ `W<c` predicate. -/

/-- **The smoothness-carrying reindex.**  Like `class_tau_sum_le_prod` but with the
`c`-domain a general `Finset Sc` (so `Cpred`-restricted) and no `d`-predicate;
`hcov` must land `shiuC w n ∈ Sc`.  (Concrete decidability via `[DecidablePred
Npred]`, so downstream filters match without a `convert` bridge.) -/
theorem class_tau_sum_le_prod' (z q a w : ℕ) (Sc : Finset ℕ)
    (Npred : ℕ → Prop) [DecidablePred Npred]
    (hcov : ∀ n, 1 ≤ n → n ≤ z → n % q = a → Npred n → shiuC w n ∈ Sc) :
    ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ Npred n),
        (n.divisors.card : ℝ)
      ≤ ∑ p ∈ ((Sc ×ˢ Finset.Icc 1 z).filter
          (fun p => p.1 * p.2 ≤ z ∧ (p.1 * p.2) % q = a)),
          (p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ) := by
  classical
  set S := (Finset.Icc 1 z).filter (fun n => n % q = a ∧ Npred n) with hSdef
  set φ : ℕ → ℕ × ℕ := fun n => (shiuC w n, shiuD w n) with hφ
  set BigT := (Sc ×ˢ Finset.Icc 1 z).filter
    (fun p => p.1 * p.2 ≤ z ∧ (p.1 * p.2) % q = a) with hBigT
  set G : ℕ × ℕ → ℝ := fun p => (p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ) with hG
  have hmemS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ z ∧ n % q = a ∧ Npred n := by
    intro n hn
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hn
    exact ⟨hn.1.1, hn.1.2, hn.2.1, hn.2.2⟩
  have hval : ∀ n ∈ S, (n.divisors.card : ℝ) = G (φ n) := by
    intro n hn
    obtain ⟨hn1, _, _, _⟩ := hmemS n hn
    have hn0 : n ≠ 0 := by omega
    have htau := tau_mul_shiu hn0 w
    simp only [hG, hφ]
    rw [htau]; push_cast; ring
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
  have hsub : S.image φ ⊆ BigT := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨n, hn, rfl⟩ := hp
    obtain ⟨hn1, hnz, hnq, hnP⟩ := hmemS n hn
    have hn0 : n ≠ 0 := by omega
    have hcSc := hcov n hn1 hnz hnq hnP
    have hd1 : 1 ≤ shiuD w n := shiuD_pos hn0 w
    have hc1 : 1 ≤ shiuC w n := shiuC_pos hn0 w
    have hcd : shiuC w n * shiuD w n = n := shiuC_mul_shiuD hn0 w
    have hdz : shiuD w n ≤ z := by
      have : shiuD w n ≤ shiuC w n * shiuD w n := Nat.le_mul_of_pos_left _ hc1
      omega
    rw [hBigT, hφ, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨hcSc, ⟨hd1, hdz⟩⟩, ?_, ?_⟩
    · rw [hcd]; exact hnz
    · rw [hcd]; exact hnq
  calc ∑ n ∈ S, (n.divisors.card : ℝ)
      = ∑ n ∈ S, G (φ n) := Finset.sum_congr rfl hval
    _ = ∑ p ∈ S.image φ, G p := (Finset.sum_image hinj).symm
    _ ≤ ∑ p ∈ BigT, G p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)

/-- **The fibre split** with a general `c`-domain `Sc` (no `d`-predicate). -/
theorem bigT_sum_split' (Sc : Finset ℕ) (z q a : ℕ) (g : ℕ → ℝ) :
    ∑ p ∈ ((Sc ×ˢ Finset.Icc 1 z).filter
        (fun p => p.1 * p.2 ≤ z ∧ (p.1 * p.2) % q = a)), g p.1
      = ∑ c ∈ Sc, g c *
          (((Finset.Icc 1 z).filter
            (fun d => c * d ≤ z ∧ (c * d) % q = a)).card : ℝ) := by
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro c _
  dsimp only
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The trivial `d`-count** (no roughness): for a fixed prefix `c ≥ 1`, the number
of `d ≤ z` with `c·d ≤ z` and `c·d ≡ a (q)` is at most `z/(c·q) + 1` — a genuine
`card_ap_le` instance in the inverse residue class (`exists_inv_residue`), empty when
`(c,q) ≠ 1`. -/
theorem inner_count_triv_le {z q a c : ℕ} (hq : 1 ≤ q) (hc1 : 1 ≤ c)
    (ha : Nat.Coprime a q) :
    (((Finset.Icc 1 z).filter (fun d => c * d ≤ z ∧ (c * d) % q = a)).card : ℝ)
      ≤ (z : ℝ) / c / q + 1 := by
  classical
  by_cases hcop : Nat.Coprime c q
  · obtain ⟨b, hblt, hbcop, hbimp⟩ := exists_inv_residue hq hcop ha
    set D := (Finset.Icc 1 z).filter (fun d => c * d ≤ z ∧ (c * d) % q = a) with hD
    have hsub : D ⊆ (Finset.Icc 1 (z / c)).filter (fun m => m % q = b) := by
      intro d hd
      rw [hD, Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, _⟩, hcdz, hcda⟩ := hd
      rw [Finset.mem_filter, Finset.mem_Icc]
      have haq : a % q = a := by
        have hlt : (c * d) % q < q := Nat.mod_lt _ (by omega)
        rw [hcda] at hlt; exact Nat.mod_eq_of_lt hlt
      refine ⟨⟨hd1, ?_⟩, hbimp d (by rw [haq]; exact hcda)⟩
      rw [Nat.le_div_iff_mul_le (by omega : 0 < c), Nat.mul_comm]; exact hcdz
    calc (D.card : ℝ)
        ≤ (((Finset.Icc 1 (z / c)).filter (fun m => m % q = b)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((z / c : ℕ) : ℝ) / q + 1 := card_ap_le hq b
      _ ≤ (z : ℝ) / c / q + 1 := by
          have hle : ((z / c : ℕ) : ℝ) ≤ (z : ℝ) / c := Nat.cast_div_le
          gcongr
  · have hempty : (Finset.Icc 1 z).filter (fun d => c * d ≤ z ∧ (c * d) % q = a) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro d _ hcon
      obtain ⟨_, hcda⟩ := hcon
      apply hcop
      have hcdq : Nat.Coprime (c * d) q := by
        unfold Nat.Coprime; rw [Nat.gcd_comm, Nat.gcd_rec, hcda]; exact ha
      exact Nat.Coprime.coprime_dvd_left (dvd_mul_right c d) hcdq
    rw [hempty, Finset.card_empty, Nat.cast_zero]; positivity

/-! ## NEW-1′ — the inequality-form tuned graded Rankin (the Class-IV enabler)

NEW-1 (`sum_tau_smooth_gt_tuned_le`) requires `r·log v = log z̃` **exactly**, forcing
`z̃ = v^r` (a perfect power).  At the pinned scale `z̃ = W²` this cannot hold across
the class-IV bins (`v_r = z̃^{1/r}` is irrational for a fixed nat `z̃`).  The
resolution: `log W = ½·log z̃` (satisfiable exactly by `z̃ = W²`) is kept, but the
`v`-constraint is **relaxed to `r·log v ≤ log z̃`** (met by any nat `v_r ≤ z̃^{1/r}`).
The proof is NEW-1's, with the three tuning equalities `(1−σ)log v = log r/4`,
`v^{1−σ} = r^{1/4}` weakened to `≤` (the correct direction — the correction term is
upper-bounded).  Reuses the SAME landed helpers.  THIS is the stone that unblocks
the class-IV binned assembly (each bin instantiates `v = v_r`, `σ_r`). -/
theorem sum_tau_smooth_gt_tuned_le' :
    ∃ (Ce C₀ : ℝ), 0 ≤ Ce ∧ 0 ≤ C₀ ∧
    ∀ (N z r v W : ℕ) (σ : ℝ),
      3 ≤ v → 2 ≤ r → 1 ≤ W → 1 < z →
      (r : ℝ) * Real.log r ≤ Real.log z →
      Real.log W = (1 / 2) * Real.log z →
      (r : ℝ) * Real.log v ≤ Real.log z →
      σ = 1 - (r : ℝ) * Real.log r / (4 * Real.log z) →
      ∑ c ∈ (Finset.Icc 1 N).filter (fun c => (∀ p ∈ c.primeFactors, p ≤ v) ∧ W < c),
          (c.divisors.card : ℝ) / (c : ℝ)
        ≤ Real.exp (-((r : ℝ) * Real.log r) / 8
              + (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2 + C₀))
          * Real.exp (2 * ∑ p ∈ (Finset.range (z + 1)).filter Nat.Prime, (p : ℝ)⁻¹ + Ce) := by
  refine ⟨8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ), (Real.log 4 + 4) / 2, ?_, ?_, ?_⟩
  · have hz : (0 : ℝ) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) :=
      tsum_nonneg (fun n => by positivity)
    linarith
  · have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  intro N z r v W σ hv hr hW hz hrange hlogW hlogv_le hσ
  have hv2 : 2 ≤ v := by omega
  have hzpos : (0 : ℝ) < (z : ℝ) := by positivity
  have hlogz : 0 < Real.log z := Real.log_pos (by exact_mod_cast hz)
  have hlogr : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr)
  have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hvpos : (0 : ℝ) < (v : ℝ) := by positivity
  -- the tuning identities (v-constraint now ≤)
  have h1σ : 1 - σ = (r : ℝ) * Real.log r / (4 * Real.log z) := by rw [hσ]; ring
  have h1σ_nn : (0 : ℝ) ≤ 1 - σ :=
    h1σ ▸ div_nonneg (mul_nonneg hrpos.le hlogr.le) (by positivity)
  have h1σ_le : 1 - σ ≤ 1 / 4 := by
    rw [h1σ, div_le_iff₀ (by positivity)]; linarith [hrange]
  have hσ1 : σ ≤ 1 := by linarith [h1σ_nn]
  have hσ_lb : (3 : ℝ) / 4 ≤ σ := by linarith [h1σ_le]
  have hσ_gt : 1 / 2 < σ := by linarith [hσ_lb]
  have hr4nn : (0 : ℝ) ≤ (r : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hrpos.le _
  have hl4 : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  -- log v ≤ log z / r
  have hlv_le : Real.log v ≤ Real.log z / r := by
    rw [le_div_iff₀ hrpos]; linarith [hlogv_le]
  -- Rankin gain: W^{−(1−σ)} = exp(−(1/8) r log r) (exact, uses z̃ = W²)
  have hgain : (W : ℝ) ^ (-(1 - σ)) = Real.exp (-((r : ℝ) * Real.log r) / 8) := by
    rw [Real.rpow_def_of_pos hWpos]; congr 1
    rw [hlogW, h1σ]; field_simp; ring
  -- (1−σ)·log v ≤ log r / 4
  have hσlogv_le : (1 - σ) * Real.log v ≤ Real.log r / 4 := by
    rw [h1σ]
    calc (r : ℝ) * Real.log r / (4 * Real.log z) * Real.log v
        ≤ (r : ℝ) * Real.log r / (4 * Real.log z) * (Real.log z / r) := by
          apply mul_le_mul_of_nonneg_left hlv_le
          positivity
      _ = Real.log r / 4 := by field_simp
  -- v^{1−σ} ≤ r^{1/4}
  have hv1σ_le : (v : ℝ) ^ (1 - σ) ≤ (r : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos hvpos, Real.rpow_def_of_pos hrpos]
    apply Real.exp_le_exp.mpr
    rw [mul_comm (Real.log v) (1 - σ)]
    linarith [hσlogv_le]
  -- v ≤ z
  have hvz : v ≤ z := by
    have hlogvz : Real.log v ≤ Real.log z := by
      calc Real.log v ≤ Real.log z / r := hlv_le
        _ ≤ Real.log z := div_le_self hlogz.le (by exact_mod_cast (by omega : 1 ≤ r))
    have hvzR : (v : ℝ) ≤ (z : ℝ) := by
      have := Real.exp_le_exp.mpr hlogvz
      rwa [Real.exp_log hvpos, Real.exp_log hzpos] at this
    exact_mod_cast hvzR
  -- the correction sub-bound (upper-bounded via v^{1−σ} ≤ r^{1/4})
  have hsubbound : 2 * ((1 - σ) * (v : ℝ) ^ (1 - σ) * (Real.log v + (Real.log 4 + 4)))
      ≤ (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2 + (Real.log 4 + 4) / 2) := by
    have hlogv_nn : (0 : ℝ) ≤ Real.log v :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ v))
    have hσlogv_nn : (0 : ℝ) ≤ (1 - σ) * Real.log v := mul_nonneg h1σ_nn hlogv_nn
    have ht1 : (1 - σ) * (v : ℝ) ^ (1 - σ) * Real.log v
        ≤ (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 4) := by
      calc (1 - σ) * (v : ℝ) ^ (1 - σ) * Real.log v
          = (v : ℝ) ^ (1 - σ) * ((1 - σ) * Real.log v) := by ring
        _ ≤ (r : ℝ) ^ (1 / 4 : ℝ) * ((1 - σ) * Real.log v) :=
            mul_le_mul_of_nonneg_right hv1σ_le hσlogv_nn
        _ ≤ (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 4) :=
            mul_le_mul_of_nonneg_left hσlogv_le hr4nn
    have ht2 : (1 - σ) * (v : ℝ) ^ (1 - σ) * (Real.log 4 + 4)
        ≤ (r : ℝ) ^ (1 / 4 : ℝ) * ((Real.log 4 + 4) / 4) := by
      calc (1 - σ) * (v : ℝ) ^ (1 - σ) * (Real.log 4 + 4)
          = (v : ℝ) ^ (1 - σ) * ((1 - σ) * (Real.log 4 + 4)) := by ring
        _ ≤ (r : ℝ) ^ (1 / 4 : ℝ) * ((1 - σ) * (Real.log 4 + 4)) :=
            mul_le_mul_of_nonneg_right hv1σ_le (mul_nonneg h1σ_nn hl4)
        _ ≤ (r : ℝ) ^ (1 / 4 : ℝ) * ((Real.log 4 + 4) / 4) := by
            apply mul_le_mul_of_nonneg_left _ hr4nn
            nlinarith [h1σ_le, hl4]
    nlinarith [ht1, ht2]
  -- the exponent inequality (identical to NEW-1)
  set Ppv := (Finset.range (v + 1)).filter Nat.Prime with hPpv
  set Ppz := (Finset.range (z + 1)).filter Nat.Prime with hPpz
  have hcorr := sum_rpow_neg_sub_inv_le v (by omega : 1 ≤ v) (by linarith : 0 ≤ σ) hσ1
  rw [← hPpv] at hcorr
  have hexp_bound : 2 * ∑ p ∈ Ppv, (p : ℝ) ^ (-σ)
      ≤ (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2 + (Real.log 4 + 4) / 2)
        + 2 * ∑ p ∈ Ppz, (p : ℝ)⁻¹ := by
    have hsub : ∑ p ∈ Ppv, ((p : ℝ) ^ (-σ) - (p : ℝ)⁻¹)
        = ∑ p ∈ Ppv, (p : ℝ) ^ (-σ) - ∑ p ∈ Ppv, (p : ℝ)⁻¹ := by
      rw [Finset.sum_sub_distrib]
    have hsubset : Ppv ⊆ Ppz := by
      rw [hPpv, hPpz]
      apply Finset.filter_subset_filter
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hmain_ext : ∑ p ∈ Ppv, (p : ℝ)⁻¹ ≤ ∑ p ∈ Ppz, (p : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun p _ _ => by positivity)
    linarith [hcorr, hsub, hmain_ext, hsubbound]
  -- assemble (identical to NEW-1)
  have hraw := sum_tau_smooth_gt_rankin_le N v W σ hv2 hσ_gt hσ1 hW
  have hprod := prod_one_sub_rpow_neg_sq_le_exp_tight v hσ_lb
  rw [← hPpv] at hraw hprod
  rw [← Real.exp_add]
  calc ∑ c ∈ (Finset.Icc 1 N).filter (fun c => (∀ p ∈ c.primeFactors, p ≤ v) ∧ W < c),
          (c.divisors.card : ℝ) / (c : ℝ)
      ≤ (W : ℝ) ^ (-(1 - σ)) * ∏ p ∈ Ppv, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 := hraw
    _ ≤ (W : ℝ) ^ (-(1 - σ))
          * Real.exp (2 * ∑ p ∈ Ppv, (p : ℝ) ^ (-σ) + 8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hWpos.le _)
    _ = Real.exp (-((r : ℝ) * Real.log r) / 8)
          * Real.exp (2 * ∑ p ∈ Ppv, (p : ℝ) ^ (-σ) + 8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
        rw [hgain]
    _ = Real.exp (-((r : ℝ) * Real.log r) / 8
          + (2 * ∑ p ∈ Ppv, (p : ℝ) ^ (-σ) + 8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ))) := by
        rw [← Real.exp_add]
    _ ≤ Real.exp (-((r : ℝ) * Real.log r) / 8
          + (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2 + (Real.log 4 + 4) / 2)
          + (2 * ∑ p ∈ Ppz, (p : ℝ)⁻¹ + 8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ))) := by
        apply Real.exp_le_exp.mpr; linarith [hexp_bound]

/-! ## Class III — the assembly (single raw Rankin at the `P₀`-smooth extreme) -/

/-- Class III: the sub-class of III/IV with `ρ = d.minFac ≤ P₀` (`P₀ = log z` at
scale).  Then the smooth prefix `c` is `P₀`-smooth (`shiuC_prime_lt_minFac`). -/
def shiuClassIII (w W P₀ n : ℕ) : Prop :=
  shiuClassIIIIV w W n ∧ (shiuD w n).minFac ≤ P₀

instance (w W P₀ n : ℕ) : Decidable (shiuClassIII w W P₀ n) := by
  unfold shiuClassIII; infer_instance

/-- **Class III (the assembly).**  For the III/IV sub-class with `ρ ≤ P₀`, the smooth
prefix `c` is `P₀`-smooth and `> W`; the cofactor `d` is bounded crudely
`τ(d) ≤ Cδ·z^δ`.  The reindex (`class_tau_sum_le_prod'`, carrying the `c`-smoothness),
the trivial `d`-count (`inner_count_triv_le`), and the caller-supplied Rankin bound
`RankBd` on the smooth-prefix sum `Σ_{c>W, P₀-smooth, c≤w} τ(c)/c` compose to

    Σ_{III, n≡a(q)} τ(n) ≤ Cδ·z^δ·( (z/q)·RankBd + w·(1+log w) ).

`RankBd` is `sum_tau_smooth_gt_rankin_le` at `v = P₀`, `σ = 3/4` (`W^{−1/4}·EulerProd`,
the Euler product over `p ≤ P₀` subpolynomial); the S5 fold repays `z^δ·z^{−α/24}`.
The `+w(1+log w)` is the boundary from the `+1` per prefix. -/
theorem shiu_classIII_le {z q a w W P₀ : ℕ} (δ Cδ RankBd : ℝ)
    (hq : 1 ≤ q) (hw1 : 1 ≤ w) (ha : Nat.Coprime a q)
    (hCδ : 0 < Cδ) (hδ : 0 ≤ δ)
    (htau : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ Cδ * (n : ℝ) ^ δ)
    (hRank : ∑ c ∈ (Finset.Icc 1 w).filter
        (fun c => (∀ p ∈ c.primeFactors, p ≤ P₀) ∧ W < c),
        (c.divisors.card : ℝ) / (c : ℝ) ≤ RankBd) :
    ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassIII w W P₀ n),
        (n.divisors.card : ℝ)
      ≤ Cδ * (z : ℝ) ^ δ * ((z : ℝ) / q * RankBd + (w : ℝ) * (1 + Real.log w)) := by
  classical
  set Czδ : ℝ := Cδ * (z : ℝ) ^ δ with hCzδ
  have hCzδnn : 0 ≤ Czδ := by rw [hCzδ]; positivity
  set Sc := (Finset.Icc 1 w).filter
    (fun c => (∀ p ∈ c.primeFactors, p ≤ P₀) ∧ W < c) with hSc
  -- reindex with c-smoothness
  have hcov : ∀ n, 1 ≤ n → n ≤ z → n % q = a → shiuClassIII w W P₀ n →
      shiuC w n ∈ Sc := by
    intro n hn1 _ _ hcls
    have hn0 : n ≠ 0 := by omega
    obtain ⟨⟨hd1, _hρW, hWc⟩, hρP0⟩ := hcls
    rw [hSc, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨shiuC_pos hn0 w, shiuC_le hw1 n⟩, ?_, hWc⟩
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.dvd_of_mem_primeFactors hp
    have hplt := shiuC_prime_lt_minFac hn0 hd1 hpp hpdvd
    omega
  have hreindex := class_tau_sum_le_prod' z q a w Sc (shiuClassIII w W P₀) hcov
  set BigT := (Sc ×ˢ Finset.Icc 1 z).filter
    (fun p => p.1 * p.2 ≤ z ∧ (p.1 * p.2) % q = a) with hBigT
  -- τ(d) ≤ Czδ on the pair set
  have hstep : ∑ p ∈ BigT, (p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ)
      ≤ ∑ p ∈ BigT, (p.1.divisors.card : ℝ) * Czδ := by
    apply Finset.sum_le_sum
    intro p hp
    rw [hBigT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨_, hd1, hdz⟩, _⟩ := hp
    have htaud : (p.2.divisors.card : ℝ) ≤ Czδ := by
      rw [hCzδ]
      calc (p.2.divisors.card : ℝ) ≤ Cδ * (p.2 : ℝ) ^ δ := htau p.2 hd1
        _ ≤ Cδ * (z : ℝ) ^ δ := by
            apply mul_le_mul_of_nonneg_left _ hCδ.le
            exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hdz) hδ
    exact mul_le_mul_of_nonneg_left htaud (by positivity)
  have hsplit := bigT_sum_split' Sc z q a (fun c => (c.divisors.card : ℝ) * Czδ)
  -- per-prefix count bound
  have hpercterm : ∀ c ∈ Sc, ((c.divisors.card : ℝ) * Czδ) *
      (((Finset.Icc 1 z).filter (fun d => c * d ≤ z ∧ (c * d) % q = a)).card : ℝ)
      ≤ (c.divisors.card : ℝ) * Czδ * ((z : ℝ) / c / q + 1) := by
    intro c hc
    rw [hSc, Finset.mem_filter, Finset.mem_Icc] at hc
    have hc1 : 1 ≤ c := hc.1.1
    have hcount := inner_count_triv_le (z := z) hq hc1 ha
    exact mul_le_mul_of_nonneg_left hcount (by positivity)
  -- the two smooth sums
  have hRankSc : ∑ c ∈ Sc, (c.divisors.card : ℝ) / (c : ℝ) ≤ RankBd := hRank
  have hTauSc : ∑ c ∈ Sc, (c.divisors.card : ℝ) ≤ (w : ℝ) * (1 + Real.log w) := by
    calc ∑ c ∈ Sc, (c.divisors.card : ℝ)
        ≤ ∑ c ∈ Finset.Icc 1 w, (c.divisors.card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (by rw [hSc]; exact Finset.filter_subset _ _)
            (fun c _ _ => by positivity)
      _ ≤ (w : ℝ) * (1 + Real.log w) := Salt.BV.sum_card_divisors_le w hw1
  -- algebraic regroup
  have halg : ∑ c ∈ Sc, (c.divisors.card : ℝ) * Czδ * ((z : ℝ) / c / q + 1)
      = Czδ * (z : ℝ) / q * (∑ c ∈ Sc, (c.divisors.card : ℝ) / (c : ℝ))
        + Czδ * (∑ c ∈ Sc, (c.divisors.card : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro c _; ring
  -- assemble
  calc ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassIII w W P₀ n),
          (n.divisors.card : ℝ)
      ≤ ∑ p ∈ BigT, (p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ) := hreindex
    _ ≤ ∑ p ∈ BigT, (p.1.divisors.card : ℝ) * Czδ := hstep
    _ = ∑ c ∈ Sc, ((c.divisors.card : ℝ) * Czδ) *
          (((Finset.Icc 1 z).filter
            (fun d => c * d ≤ z ∧ (c * d) % q = a)).card : ℝ) := hsplit
    _ ≤ ∑ c ∈ Sc, (c.divisors.card : ℝ) * Czδ * ((z : ℝ) / c / q + 1) :=
        Finset.sum_le_sum hpercterm
    _ = Czδ * (z : ℝ) / q * (∑ c ∈ Sc, (c.divisors.card : ℝ) / (c : ℝ))
          + Czδ * (∑ c ∈ Sc, (c.divisors.card : ℝ)) := halg
    _ ≤ Czδ * (z : ℝ) / q * RankBd + Czδ * ((w : ℝ) * (1 + Real.log w)) := by
        have h1 : Czδ * (z : ℝ) / q * (∑ c ∈ Sc, (c.divisors.card : ℝ) / (c : ℝ))
            ≤ Czδ * (z : ℝ) / q * RankBd :=
          mul_le_mul_of_nonneg_left hRankSc (by rw [hCzδ]; positivity)
        have h2 : Czδ * (∑ c ∈ Sc, (c.divisors.card : ℝ))
            ≤ Czδ * ((w : ℝ) * (1 + Real.log w)) :=
          mul_le_mul_of_nonneg_left hTauSc hCzδnn
        linarith
    _ = Cδ * (z : ℝ) ^ δ * ((z : ℝ) / q * RankBd + (w : ℝ) * (1 + Real.log w)) := by
        rw [hCzδ]; ring

end Salt.Maynard
