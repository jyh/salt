/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.TnInduction

/-!
# C1c‴ — The Lemma 11 analytic induction: discharging `hTbound` (BJS §2.4)

This file closes the last analytic gap of the two-sided explicit linear sieve keystone
(BJS Theorem 6).  C1c″ (`TnInduction.lean`) reduced both `hmain` comparisons to the single
named hypothesis `hTbound` — the analytic bound on the Buchstab tail
`Σ_{parity} Tₙ ≤ V(z)·(Fchain N ± εCᵢe²·hBJS)`.  Here we discharge it.

## What is proved (sorry-free, axiom-clean)

* **The n = 1 Buchstab identity (the analytically honest core).**  `T_one_upper`:
  `T₁(D,z) = V(D^{1/3}) − V(z)` exactly, via the general **telescoping-product**
  identity `prod_telescope` (`1 − ∏(1−aₚ) = Σ aₚ∏_{q<p}(1−a_q)`, BJS's Buchstab
  collapse) applied to the descending prime chains of length 1.  `T_two_one_zero`:
  `T₁ = 0` on the even (lower) side (position 1 is unchecked).

* **The n = 1 per-level bound (BJS Lemma 11, base case = BJS (39)).**  `hlevel_one_upper`:
  from the identity and hypothesis (4) in the form `V(D^{1/3}) ≤ (3K/s)·V(z)`
  (`h4`, the V-ratio input, `1 < K ≤ 1+ε`), `T₁ ≤ V(z)·(f₁(s) + ε·3·e²·hBJS(s))` on the
  upper operating window `s ∈ [1,3]`.  The closing inequality is `1/s ≤ e²·hBJS(s)`
  (`inv_le_e2_hBJS`) — BJS's `h`, sharper than C1b's `hbar`, is what makes `τ₁ = 3` close.

* **The Buchstab induction assembly (the general chain-to-integral as ONE hypothesis).**
  `hTbound_upper_of_levels` / `hTbound_lower_of_levels`: from the per-level Lemma-11
  bounds `Tₙ ≤ V(z)(fₙ(s) + ετₙe²hBJS(s))` (`hlevel`, the deferred chain-to-integral
  recursion (34)–(38)) and the Lemma-12 τ-close `Στₙ ≤ Cᵢ` (`htau`), the exact
  `hTbound` shape consumed by `hmain_upper`/`hmain_lower` follows (at `N = maxDepth s`,
  where `Fchain (maxDepth s) − 1` **is** the full odd `fseq`-sum, tail-free).

* **The Lemma 12 τ-close (parametric).**  `tau_sum_le_of_recursion`: any τ-sequence
  obeying the contracting geometric recursion `τₙ₊₁ ≤ a·rⁿ + β·τₙ` (`0 ≤ r,β < 1`)
  has uniformly bounded partial sums `Στ ≤ (τ₀ + a/(1−r))/(1−β)` — the finite `C₁`, `C₂`.

## Compiler-plugs

`linear_sieve_upper_rosser_assembled_final` / `..._lower_..._final` feed the assembled
`hTbound` into C1c″'s `hmain_upper`/`hmain_lower`, yielding BJS Theorem 6 (5)/(6) modulo
only the per-level Lemma-11 hypothesis and the τ-close.

## The deferred piece (precise flag in `docs/blueprints/flags.md`)

The general-`n` per-level bound `hlevel` (the chain-to-integral recursion `Tₙ =
Σ_p ν(p)T_{n−1}(D/p,p)` of BJS (34), needing a *restricted sieve below p*) remains a
named hypothesis for `n ≥ 2`; it is discharged concretely only at `n = 1`.  The numeric
frozen-row instantiation `ε = 1/10000 → C₁ = 106, C₂ = 108` needs BJS's exact (31)
constants (`γ₃, κ₃, cₙ`, page-image) — left parametric per the C0-ledger doctrine.
-/

open Finset Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius

namespace Salt.Chen

open List

/-! ## Part A — the telescoping-product identity (BJS's Buchstab collapse)

The combinatorial heart of the chain-to-`V` reduction: over a linearly ordered finite set
of primes, the density defect `1 − ∏(1−aₚ)` reorganises as the descending-chain sum
`Σₚ aₚ·∏_{q<p}(1−a_q)`.  This is what turns `Σ ν(p)V(p)` telescopes into `V`-differences. -/

/-- **Telescoping product** (general).  For any finite `S ⊆ ℕ` and `a : ℕ → ℝ`,
`Σ_{p∈S} a(p)·∏_{q∈S, q<p}(1−a(q)) = 1 − ∏_{p∈S}(1−a(p))`.  Proved by induction removing
the maximum element (the largest prime peels off both sides). -/
theorem prod_telescope (S : Finset ℕ) (a : ℕ → ℝ) :
    ∑ p ∈ S, a p * ∏ q ∈ S.filter (· < p), (1 - a q) = 1 - ∏ p ∈ S, (1 - a p) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert b T hb ih =>
    have hbnotin : b ∉ T := fun h => absurd (hb b h) (lt_irrefl b)
    rw [Finset.sum_insert hbnotin, Finset.prod_insert hbnotin]
    have hfb : (insert b T).filter (· < b) = T := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      exact ⟨fun ⟨h, hlt⟩ => h.resolve_left (by omega), fun h => ⟨Or.inr h, hb x h⟩⟩
    rw [hfb]
    have hcongr : ∀ p ∈ T, (insert b T).filter (· < p) = T.filter (· < p) := by
      intro p hp; ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      exact ⟨fun ⟨h, hlt⟩ => ⟨h.resolve_left (by rintro rfl; have := hb p hp; omega), hlt⟩,
        fun ⟨h, hlt⟩ => ⟨Or.inr h, hlt⟩⟩
    rw [Finset.sum_congr rfl (fun p hp => by rw [hcongr p hp]), ih]; ring

/-! ## Part B — the n = 1 Buchstab identity `T₁ = V(D^{1/3}) − V(z)`

A violating prefix of length 1 is a single sifting prime `p` with `p³ ≥ D` (position 1 is
the odd/upper check `p·p² ≥ D`).  Summing `ν(p)·V(p)` over these telescopes (`prod_telescope`)
to `V(D^{1/3}) − V(z)`, with `V(D^{1/3}) = ∏_{p³<D}(1−ν(p)) = Vlow`. -/

/-- Single-prime structure: a squarefree `c` with a one-element descending list is a prime,
`c = p` and `rlist c = [p]`. -/
theorem single_prime_facts {c : ℕ} (hsf : Squarefree c) (hlen : (rlist c).length = 1) :
    ∃ p, p.Prime ∧ c = p ∧ rlist c = [p] := by
  rw [rlist_length] at hlen
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hlen
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (hp ▸ Finset.mem_singleton_self p)
  have hcp : c = p := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsf]
    rw [hp, Finset.prod_singleton]
  exact ⟨p, hpp, hcp, by rw [rlist, hp, Finset.sort_singleton]⟩

/-- `rmin c = c` for a single-prime `c` (`rlist c = [c]`). -/
theorem rmin_single {c : ℕ} (hrl : rlist c = [c]) : rmin c = c := by
  have h : rmin c = (rlist c).getD ((rlist c).length - 1) 1 := rfl
  rw [h, hrl]; simp

/-- **The length-1 violating prefixes are exactly the sifting primes `p` with `p³ ≥ D`**
(BJS (28) at `n = 1`, upper `ν = 1`). -/
theorem T_one_filter_eq (s : BoundingSieve) (D : ℕ) :
    (divisors s.prodPrimes).filter (fun c => isViolPrefix 1 D c ∧ (rlist c).length = 1)
      = s.prodPrimes.primeFactors.filter (fun p => D ≤ p ^ 3) := by
  ext c
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hcdvd, _⟩, hviol, hlen⟩
    have hsf : Squarefree c := s.prodPrimes_squarefree.squarefree_of_dvd hcdvd
    obtain ⟨p, hpp, hcp, hrl⟩ := single_prime_facts hsf hlen
    obtain ⟨_, _, hfail, _⟩ := hviol
    rw [hlen] at hfail
    have hrp1 : rprefix c 1 = c := by rw [rprefix, Finset.prod_range_one, hrl]; simp [hcp]
    have hre0 : relem c 0 = c := by change (rlist c).getD 0 1 = c; rw [hrl]; simp [hcp]
    rw [hrp1, hre0] at hfail
    exact ⟨by rw [hcp]; exact Nat.mem_primeFactors.mpr ⟨hpp, hcp ▸ hcdvd,
      s.prodPrimes_squarefree.ne_zero⟩, by nlinarith [hfail]⟩
  · rintro ⟨hcpf, hD⟩
    have hpp : c.Prime := Nat.prime_of_mem_primeFactors hcpf
    have hcdvd : c ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors hcpf
    have hrl : rlist c = [c] := by rw [rlist, hpp.primeFactors, Finset.sort_singleton]
    have hlen : (rlist c).length = 1 := by rw [hrl]; rfl
    have hrp1 : rprefix c 1 = c := by rw [rprefix, Finset.prod_range_one, hrl]; simp
    have hre0 : relem c 0 = c := by change (rlist c).getD 0 1 = c; rw [hrl]; simp
    refine ⟨⟨hcdvd, s.prodPrimes_squarefree.ne_zero⟩, ⟨by rw [hlen], by rw [hlen], ?_, ?_⟩, hlen⟩
    · rw [hlen, hrp1, hre0]; nlinarith [hD]
    · intro m hm1 hmlt _; rw [hlen] at hmlt; omega

/-- `Vlow = V(D^{1/3}) = ∏_{p³<D}(1−ν(p))`, the untruncated Möbius density below the
first-check threshold `D^{1/3}`. -/
noncomputable def Vlow (s : BoundingSieve) (D : ℕ) : ℝ :=
  ∏ p ∈ s.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D), (1 - s.nu p)

theorem Vlow_pos (s : BoundingSieve) (D : ℕ) : 0 < Vlow s D := by
  apply Finset.prod_pos
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hdvd : p ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have := s.nu_lt_one_of_prime p hpp hdvd; linarith

/-- `V(z) = W = Vlow · ∏_{p³≥D}(1−ν(p))`: the sifting primes split at the threshold. -/
theorem W_eq_Vlow_mul (s : BoundingSieve) (D : ℕ) :
    Salt.BrunLower.W s
      = Vlow s D * ∏ p ∈ s.prodPrimes.primeFactors.filter (fun p => D ≤ p ^ 3), (1 - s.nu p) := by
  rw [Salt.BrunLower.W, Vlow, ← Finset.prod_union]
  · apply Finset.prod_congr _ (fun _ _ => rfl)
    have hrw : (s.prodPrimes.primeFactors.filter (fun p => D ≤ p ^ 3))
        = (s.prodPrimes.primeFactors.filter (fun p => ¬ (p ^ 3 < D))) := by
      apply Finset.filter_congr; intro p _; simp [not_lt]
    rw [hrw, Finset.filter_union_filter_not_eq]
  · rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_filter] at ha hb; omega

/-- `V(p) = Vlow · ∏_{q³≥D, q<p}(1−ν(q))` for a high prime `p` (all low primes lie below
`p`, so they factor out as the constant `Vlow`). -/
theorem Vbelow_cut (s : BoundingSieve) (D p : ℕ)
    (hp : p ∈ s.prodPrimes.primeFactors.filter (fun p => D ≤ p ^ 3)) :
    Vbelow s p
      = Vlow s D
        * ∏ q ∈ (s.prodPrimes.primeFactors.filter (fun q => D ≤ q ^ 3)).filter (fun q => q < p),
            (1 - s.nu q) := by
  simp only [Finset.mem_filter] at hp
  rw [Vbelow, belowPrimes, Vlow, ← Finset.prod_union]
  · apply Finset.prod_congr _ (fun _ _ => rfl)
    ext q
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ⟨hqP, hqp⟩
      rcases lt_or_ge (q ^ 3) D with h | h
      · exact Or.inl ⟨hqP, h⟩
      · exact Or.inr ⟨⟨hqP, h⟩, hqp⟩
    · rintro (⟨hqP, hq3⟩ | ⟨⟨hqP, _⟩, hqp⟩)
      · refine ⟨hqP, ?_⟩
        by_contra hle; rw [not_lt] at hle
        have := Nat.pow_le_pow_left hle 3; omega
      · exact ⟨hqP, hqp⟩
  · rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_filter] at ha hb; omega

/-- **The n = 1 Buchstab identity** (BJS (28)/(39) at `n = 1`, exact):
`T₁(D,z) = V(D^{1/3}) − V(z) = Vlow − W`. -/
theorem T_one_upper (s : BoundingSieve) (D : ℕ) :
    T s 1 D 1 = Vlow s D - Salt.BrunLower.W s := by
  rw [T, T_one_filter_eq]
  have hstep : ∑ c ∈ s.prodPrimes.primeFactors.filter (fun p => D ≤ p ^ 3),
        s.nu c * Vbelow s (rmin c)
      = ∑ c ∈ s.prodPrimes.primeFactors.filter (fun p => D ≤ p ^ 3),
          s.nu c * (Vlow s D * ∏ q ∈ (s.prodPrimes.primeFactors.filter
            (fun q => D ≤ q ^ 3)).filter (fun q => q < c), (1 - s.nu q)) := by
    apply Finset.sum_congr rfl
    intro c hc
    have hcpf := (Finset.mem_filter.mp hc).1
    have hpp : c.Prime := Nat.prime_of_mem_primeFactors hcpf
    have hrl : rlist c = [c] := by rw [rlist, hpp.primeFactors, Finset.sort_singleton]
    rw [rmin_single hrl, Vbelow_cut s D c hc]
  rw [hstep]
  rw [show ∀ (f : ℕ → ℝ), ∑ c ∈ s.prodPrimes.primeFactors.filter (fun p => D ≤ p ^ 3),
        s.nu c * (Vlow s D * f c)
      = Vlow s D * ∑ c ∈ s.prodPrimes.primeFactors.filter (fun p => D ≤ p ^ 3), s.nu c * f c from
      fun f => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun c _ => by ring)]
  rw [prod_telescope, W_eq_Vlow_mul s D]; ring

/-- **The n = 1 term vanishes on the even (lower) side**: position 1 is unchecked for
`ν = 2` (`1 % 2 ≠ 2 % 2`), so no length-1 prefix violates. -/
theorem T_two_one_zero (s : BoundingSieve) (D : ℕ) : T s 2 D 1 = 0 := by
  rw [T]
  apply Finset.sum_eq_zero
  intro c hc
  exfalso
  obtain ⟨_, hviol, hlen⟩ := Finset.mem_filter.mp hc
  obtain ⟨_, hpar, _, _⟩ := hviol
  rw [hlen] at hpar
  omega

/-! ## Part C — the closing analytic inequality `1/s ≤ e²·hBJS(s)` on `[1,3]`

BJS's majorant `h(s)` (`hBJS`, sharper than C1b's exponential `hbar`) satisfies
`1/s ≤ e²·h(s)` on the upper operating window `[1,3]`, which is exactly what makes the
`τ₁ = 3` base bound close.  (The C1b `hbar`, decaying at rate `6/5`, fails this near
`s = 3`; this is why the per-level bounds are phrased against `hBJS`.) -/

theorem hBJS_pos (s : ℝ) : 0 < hBJS s := by
  unfold hBJS
  split_ifs with h2 h3
  · exact Real.exp_pos _
  · exact Real.exp_pos _
  · have : (0 : ℝ) < s := by linarith [not_le.mp h2]
    positivity

/-- Auxiliary: `exp(s−2) ≤ s` on `[2,3]` (a degree-4 Taylor upper bound). -/
theorem exp_sub_two_le (s : ℝ) (h2 : 2 ≤ s) (h3 : s ≤ 3) : Real.exp (s - 2) ≤ s := by
  have h := Real.exp_bound (x := s - 2) (by rw [abs_le]; constructor <;> linarith) (n := 4)
    (by norm_num)
  rw [abs_le] at h
  have h2' := h.2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2'
  have hx : |s - 2| = s - 2 := by rw [abs_of_nonneg]; linarith
  rw [hx] at h2'
  nlinarith [h2', pow_nonneg (by linarith : (0 : ℝ) ≤ s - 2) 4, sq_nonneg (s - 2),
    sq_nonneg (s - 3)]

/-- **`1/s ≤ e²·hBJS(s)` on `[1,3]`** (the `τ₁ = 3` closing inequality). -/
theorem inv_le_e2_hBJS (s : ℝ) (h1 : 1 ≤ s) (h3 : s ≤ 3) : 1 / s ≤ Real.exp 2 * hBJS s := by
  have hs0 : (0 : ℝ) < s := by linarith
  unfold hBJS
  split_ifs with h2
  · have hid : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
    rw [hid, div_le_one hs0]; exact h1
  · have hb : Real.exp 2 * Real.exp (-s) = Real.exp (2 - s) := by rw [← Real.exp_add]; ring_nf
    rw [hb, div_le_iff₀ hs0]
    have hle : Real.exp (s - 2) ≤ s := exp_sub_two_le s (not_le.mp h2).le h3
    have hinv : Real.exp (2 - s) = (Real.exp (s - 2))⁻¹ := by rw [← Real.exp_neg]; ring_nf
    rw [hinv, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos _)]; linarith [hle]

/-! ## Part D — the n = 1 per-level bound (BJS Lemma 11 base case = (39))

From the identity `T₁ = Vlow − W` and hypothesis (4) in the specialised V-ratio form
`Vlow ≤ (3K/s)·W` (BJS's `V(D^{1/3}) ≤ (3K/s)V(z)`, `1 < K ≤ 1+ε`), the base per-level
bound `T₁ ≤ V(z)(f₁(s) + ε·3·e²·hBJS(s))` follows on `s ∈ [1,3]`. -/

/-- **BJS Lemma 11, base case (39).**  With the V-ratio input `h4 : Vlow ≤ (3K/s)·W`
(hypothesis (4) at `u = D^{1/3}`), on the upper window `s ∈ [1,3]`,
`T₁(D,z) ≤ V(z)·(f₁(s) + ε·τ₁·e²·hBJS(s))` with `τ₁ = 3`. -/
theorem hlevel_one_upper (s : BoundingSieve) (D : ℕ) (sparam ε K : ℝ)
    (hs1 : 1 ≤ sparam) (hs3 : sparam ≤ 3) (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε)
    (h4 : Vlow s D ≤ (3 * K / sparam) * Salt.BrunLower.W s) :
    T s 1 D 1 ≤ Salt.BrunLower.W s * (fseq 1 sparam + ε * 3 * Real.exp 2 * hBJS sparam) := by
  have hsp0 : (0 : ℝ) < sparam := by linarith
  have hW := Salt.BrunLower.W_pos s
  rw [fseq_one_window hs1 hs3, T_one_upper]
  -- T₁ = Vlow − W ≤ (3K/s − 1)·W ; target RHS = W·((3−s)/s + 3ε·e²·hBJS)
  have hstep1 : Vlow s D - Salt.BrunLower.W s
      ≤ (3 * K / sparam) * Salt.BrunLower.W s - Salt.BrunLower.W s := by linarith [h4]
  refine hstep1.trans ?_
  -- need (3K/s − 1)·W ≤ W·((3−s)/s + 3ε·e²·hBJS)
  have hclose : (K - 1) / sparam ≤ ε * Real.exp 2 * hBJS sparam := by
    rw [div_le_iff₀ hsp0]
    have hinv := inv_le_e2_hBJS sparam hs1 hs3
    rw [div_le_iff₀ hsp0] at hinv
    nlinarith [mul_le_mul_of_nonneg_left hinv hε, hKe, hε]
  have hexpand : (3 * K / sparam) * Salt.BrunLower.W s - Salt.BrunLower.W s
      = Salt.BrunLower.W s * ((3 - sparam) / sparam)
        + Salt.BrunLower.W s * (3 * ((K - 1) / sparam)) := by
    field_simp; ring
  rw [hexpand]
  have hfin : Salt.BrunLower.W s * (3 * ((K - 1) / sparam))
      ≤ Salt.BrunLower.W s * (ε * 3 * Real.exp 2 * hBJS sparam) := by
    apply mul_le_mul_of_nonneg_left _ hW.le
    nlinarith [hclose]
  linarith [hfin]

/-! ## Part E — the Lemma 12 τ-close (parametric geometric domination)

BJS Lemma 12 sums the τ-recursion (31) to the finite constants `Στ_{2n−1} = C₁`,
`Στ_{2n} = C₂` (Table 1: `ε = 1/10000 → C₁ = 106, C₂ = 108`).  The recursion has the shape
`τₙ₊₁ ≤ a·rⁿ + β·τₙ` (geometric forcing `a·rⁿ` from the decaying `fₙ`/`h` levels, plus a
contraction `β·τₙ` with `β < 1`).  We prove the uniform partial-sum bound parametrically. -/

/-- **BJS Lemma 12 (parametric).**  A τ-sequence obeying the contracting geometric
recursion `τₙ₊₁ ≤ a·rⁿ + β·τₙ` (with `0 ≤ r < 1`, `0 ≤ β < 1`, `a ≥ 0`, `τ ≥ 0`) has
uniformly bounded partial sums:  `Σ_{n<M} τₙ ≤ (τ₀ + a/(1−r))/(1−β)`.  This is the finite
`Cᵢ` of the τ-close. -/
theorem tau_sum_le_of_recursion (tau : ℕ → ℝ) (a r β : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ha : 0 ≤ a)
    (hnn : ∀ n, 0 ≤ tau n) (hrec : ∀ n, tau (n + 1) ≤ a * r ^ n + β * tau n) (M : ℕ) :
    ∑ n ∈ Finset.range M, tau n ≤ (tau 0 + a / (1 - r)) / (1 - β) := by
  have hβpos : (0 : ℝ) < 1 - β := by linarith
  -- Suffices to bound S_{M+1}; S_M ≤ S_{M+1}.
  suffices hSucc : ∑ n ∈ Finset.range (M + 1), tau n ≤ (tau 0 + a / (1 - r)) / (1 - β) by
    refine le_trans ?_ hSucc
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ M))
      (fun i _ _ => hnn i)
  -- Σ_{n<M} τ(n+1) ≤ a·Σ r^n + β·Σ_{n<M} τ n
  set S := ∑ n ∈ Finset.range (M + 1), tau n with hS
  have hrpos : (0 : ℝ) < 1 - r := by linarith
  have hgeom : ∑ n ∈ Finset.range M, r ^ n ≤ 1 / (1 - r) := by
    have hrne : r ≠ 1 := ne_of_lt hr1
    rw [geom_sum_eq hrne]
    have heq : (r ^ M - 1) / (r - 1) = (1 - r ^ M) / (1 - r) := by
      rw [← neg_div_neg_eq]; congr 1 <;> ring
    rw [heq]
    have hpM : (0 : ℝ) ≤ r ^ M := pow_nonneg hr0 M
    have hsub : 1 / (1 - r) - (1 - r ^ M) / (1 - r) = r ^ M / (1 - r) := by
      rw [div_sub_div_same]; congr 1; ring
    linarith [hsub, div_nonneg hpM hrpos.le]
  have hkey : ∑ n ∈ Finset.range M, tau (n + 1)
      ≤ a * (1 / (1 - r)) + β * ∑ n ∈ Finset.range M, tau n := by
    calc ∑ n ∈ Finset.range M, tau (n + 1)
        ≤ ∑ n ∈ Finset.range M, (a * r ^ n + β * tau n) := Finset.sum_le_sum (fun n _ => hrec n)
      _ = a * ∑ n ∈ Finset.range M, r ^ n + β * ∑ n ∈ Finset.range M, tau n := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ a * (1 / (1 - r)) + β * ∑ n ∈ Finset.range M, tau n := by
          have := mul_le_mul_of_nonneg_left hgeom ha; linarith [this]
  -- Σ_{n<M+1} τ n = τ 0 + Σ_{n<M} τ(n+1)
  have hsplit : S = tau 0 + ∑ n ∈ Finset.range M, tau (n + 1) := by
    rw [hS, Finset.sum_range_succ']; ring
  -- Σ_{n<M} τ n ≤ S
  have hSM : ∑ n ∈ Finset.range M, tau n ≤ S := by
    rw [hS]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ M))
      (fun i _ _ => hnn i)
  have haux : S - tau 0 ≤ a * (1 / (1 - r)) + β * S := by
    have hSeq : S - tau 0 = ∑ n ∈ Finset.range M, tau (n + 1) := by rw [hsplit]; ring
    rw [hSeq]; linarith [hkey, mul_le_mul_of_nonneg_left hSM hβ0]
  -- S(1−β) ≤ τ0 + a/(1−r)
  have hfin : S * (1 - β) ≤ tau 0 + a / (1 - r) := by
    have h1 : a * (1 / (1 - r)) = a / (1 - r) := by ring
    have h2 : S * (1 - β) = S - β * S := by ring
    rw [h1] at haux; rw [h2]; linarith [haux]
  rw [le_div_iff₀ hβpos]; linarith [hfin]

/-! ## Part F — the Buchstab induction assembly (`hTbound`, both parities)

Given the per-level Lemma-11 bounds `Tₙ ≤ V(z)(fₙ(s) + ετₙe²hBJS(s))` (`hlevel`; discharged
concretely at `n = 1` by `hlevel_one_upper`, deferred for `n ≥ 2` — the chain-to-integral
recursion) and the Lemma-12 τ-close `Στₙ ≤ Cᵢ` (`htau`), the exact `hTbound` shape follows
at `N = maxDepth s`.  At that truncation `Fchain (maxDepth s) − 1` **is** the full odd
`fseq`-sum (tail-free), so the fseq-tail absorption of the C0 ledger's S1 row is exact. -/

/-- `Fchain N s − 1 = Σ_{n≤N, odd} fₙ(s)` (unfolding the truncated chain). -/
theorem Fchain_sub_one (N : ℕ) (s : ℝ) :
    Fchain N s - 1 = ∑ n ∈ (Finset.range (N + 1)).filter (fun n => Odd n), fseq n s := by
  rw [Fchain]; ring

/-- `1 − fchain N s = Σ_{n≤N, even} fₙ(s)` (unfolding the truncated chain). -/
theorem one_sub_fchain (N : ℕ) (s : ℝ) :
    1 - fchain N s = ∑ n ∈ (Finset.range (N + 1)).filter (fun n => Even n), fseq n s := by
  rw [fchain]; ring

/-- **`hTbound`, upper (BJS Theorem 6 (5)).**  The odd Buchstab tail bound, assembled from
the per-level Lemma-11 hypothesis and the Lemma-12 τ-close, in the exact shape consumed by
`hmain_upper` (at `N = maxDepth s`, `C₁ = Σ_{odd} τ`). -/
theorem hTbound_upper_of_levels (s : BoundingSieve) (D : ℕ) (sparam ε C₁ : ℝ) (tau : ℕ → ℝ)
    (hε : 0 ≤ ε)
    (hlevel : ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n),
        T s 1 D n ≤ Salt.BrunLower.W s * (fseq n sparam + ε * tau n * Real.exp 2 * hBJS sparam))
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), tau n ≤ C₁) :
    ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), T s 1 D n
      ≤ Salt.BrunLower.W s *
        (Fchain (maxDepth s) sparam - 1 + ε * C₁ * Real.exp 2 * hBJS sparam) := by
  have hW := Salt.BrunLower.W_pos s
  have hh : (0 : ℝ) ≤ hBJS sparam := (hBJS_pos sparam).le
  set F := Finset.filter (fun n => Odd n) (Finset.range (maxDepth s + 1)) with hF
  calc ∑ n ∈ F, T s 1 D n
      ≤ ∑ n ∈ F, Salt.BrunLower.W s * (fseq n sparam + ε * tau n * Real.exp 2 * hBJS sparam) :=
        Finset.sum_le_sum hlevel
    _ = Salt.BrunLower.W s * ((∑ n ∈ F, fseq n sparam)
          + ε * Real.exp 2 * hBJS sparam * ∑ n ∈ F, tau n) := by
        rw [← Finset.mul_sum]; congr 1
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ ≤ Salt.BrunLower.W s * ((Fchain (maxDepth s) sparam - 1)
          + ε * C₁ * Real.exp 2 * hBJS sparam) := by
        apply mul_le_mul_of_nonneg_left _ hW.le
        rw [Fchain_sub_one]
        have hmul : ε * Real.exp 2 * hBJS sparam * ∑ n ∈ F, tau n
            ≤ ε * C₁ * Real.exp 2 * hBJS sparam := by
          have hnn : (0 : ℝ) ≤ ε * Real.exp 2 * hBJS sparam := by positivity
          calc ε * Real.exp 2 * hBJS sparam * ∑ n ∈ F, tau n
              ≤ ε * Real.exp 2 * hBJS sparam * C₁ :=
                mul_le_mul_of_nonneg_left htau hnn
            _ = ε * C₁ * Real.exp 2 * hBJS sparam := by ring
        linarith [hmul]

/-- **`hTbound`, lower (BJS Theorem 6 (6)).**  The even Buchstab tail bound, assembled dual
to the upper, in the exact shape consumed by `hmain_lower`. -/
theorem hTbound_lower_of_levels (s : BoundingSieve) (D : ℕ) (sparam ε C₂ : ℝ) (tau : ℕ → ℝ)
    (hε : 0 ≤ ε)
    (hlevel : ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n),
        T s 2 D n ≤ Salt.BrunLower.W s * (fseq n sparam + ε * tau n * Real.exp 2 * hBJS sparam))
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), tau n ≤ C₂) :
    ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), T s 2 D n
      ≤ Salt.BrunLower.W s *
        (1 - fchain (maxDepth s) sparam + ε * C₂ * Real.exp 2 * hBJS sparam) := by
  have hW := Salt.BrunLower.W_pos s
  have hh : (0 : ℝ) ≤ hBJS sparam := (hBJS_pos sparam).le
  set F := Finset.filter (fun n => Even n) (Finset.range (maxDepth s + 1)) with hF
  calc ∑ n ∈ F, T s 2 D n
      ≤ ∑ n ∈ F, Salt.BrunLower.W s * (fseq n sparam + ε * tau n * Real.exp 2 * hBJS sparam) :=
        Finset.sum_le_sum hlevel
    _ = Salt.BrunLower.W s * ((∑ n ∈ F, fseq n sparam)
          + ε * Real.exp 2 * hBJS sparam * ∑ n ∈ F, tau n) := by
        rw [← Finset.mul_sum]; congr 1
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ ≤ Salt.BrunLower.W s * ((1 - fchain (maxDepth s) sparam)
          + ε * C₂ * Real.exp 2 * hBJS sparam) := by
        apply mul_le_mul_of_nonneg_left _ hW.le
        rw [one_sub_fchain]
        have hmul : ε * Real.exp 2 * hBJS sparam * ∑ n ∈ F, tau n
            ≤ ε * C₂ * Real.exp 2 * hBJS sparam := by
          have hnn : (0 : ℝ) ≤ ε * Real.exp 2 * hBJS sparam := by positivity
          calc ε * Real.exp 2 * hBJS sparam * ∑ n ∈ F, tau n
              ≤ ε * Real.exp 2 * hBJS sparam * C₂ :=
                mul_le_mul_of_nonneg_left htau hnn
            _ = ε * C₂ * Real.exp 2 * hBJS sparam := by ring
        linarith [hmul]

/-! ## Part G — the compiler-plugs into BJS Theorem 6 (5)/(6)

Feeding the assembled `hTbound` into C1c″'s `hmain_upper`/`hmain_lower` gives the full main-
term comparison of BJS Theorem 6, modulo only the per-level Lemma-11 hypothesis and the
Lemma-12 τ-close. -/

/-- **BJS Theorem 6 (5), assembled to the per-level + τ hypotheses (upper).** -/
theorem hmain_upper_of_levels (s : BoundingSieve) (D : ℕ) (sparam ε C₁ : ℝ) (tau : ℕ → ℝ)
    (hε : 0 ≤ ε)
    (hlevel : ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n),
        T s 1 D n ≤ Salt.BrunLower.W s * (fseq n sparam + ε * tau n * Real.exp 2 * hBJS sparam))
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), tau n ≤ C₁) :
    s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      ≤ Salt.BrunLower.W s * (Fchain (maxDepth s) sparam + ε * C₁ * Real.exp 2 * hBJS sparam) :=
  hmain_upper s D (maxDepth s) sparam ε C₁
    (hTbound_upper_of_levels s D sparam ε C₁ tau hε hlevel htau)

/-- **BJS Theorem 6 (6), assembled to the per-level + τ hypotheses (lower).** -/
theorem hmain_lower_of_levels (s : BoundingSieve) (D : ℕ) (sparam ε C₂ : ℝ) (tau : ℕ → ℝ)
    (hε : 0 ≤ ε)
    (hlevel : ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n),
        T s 2 D n ≤ Salt.BrunLower.W s * (fseq n sparam + ε * tau n * Real.exp 2 * hBJS sparam))
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), tau n ≤ C₂) :
    Salt.BrunLower.W s * (fchain (maxDepth s) sparam - ε * C₂ * Real.exp 2 * hBJS sparam)
      ≤ s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam :=
  hmain_lower s D (maxDepth s) sparam ε C₂
    (hTbound_lower_of_levels s D sparam ε C₂ tau hε hlevel htau)

/-- **BJS Theorem 6 (5), fully assembled (upper).**  The explicit upper linear sieve, modulo
the per-level Lemma-11 hypothesis, the τ-close, and the standard sieve side conditions. -/
theorem linear_sieve_upper_rosser_assembled_final (s : BoundingSieve) (D : ℕ) (hD : 2 ≤ D)
    (htm : 0 ≤ s.totalMass) (sparam ε C₁ Q : ℝ) (hQ : 1 ≤ Q) (hε : 0 ≤ ε) (tau : ℕ → ℝ)
    (hlevel : ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n),
        T s 1 D n ≤ Salt.BrunLower.W s * (fseq n sparam + ε * tau n * Real.exp 2 * hBJS sparam))
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), tau n ≤ C₁) :
    s.siftedSum
      ≤ s.totalMass * (Salt.BrunLower.W s *
          (Fchain (maxDepth s) sparam + ε * C₁ * Real.exp 2 * hBJS sparam))
        + rosserRemainder s (Q * D) :=
  linear_sieve_upper_rosser_assembled s D hD htm (maxDepth s) sparam ε C₁ Q hQ
    (hTbound_upper_of_levels s D sparam ε C₁ tau hε hlevel htau)

/-- **BJS Theorem 6 (6), fully assembled (lower).**  The explicit lower linear sieve, modulo
the per-level Lemma-11 hypothesis, the τ-close, and the standard sieve side conditions. -/
theorem linear_sieve_lower_rosser_assembled_final (s : BoundingSieve) (D z : ℕ) (hz2 : 2 ≤ z)
    (hzD : z ≤ D) (hz : ∀ p ∈ s.prodPrimes.primeFactors, p < z) (htm : 0 ≤ s.totalMass)
    (sparam ε C₂ Q : ℝ) (hQ : 1 ≤ Q) (hε : 0 ≤ ε) (tau : ℕ → ℝ)
    (hlevel : ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n),
        T s 2 D n ≤ Salt.BrunLower.W s * (fseq n sparam + ε * tau n * Real.exp 2 * hBJS sparam))
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), tau n ≤ C₂) :
    s.totalMass * (Salt.BrunLower.W s *
        (fchain (maxDepth s) sparam - ε * C₂ * Real.exp 2 * hBJS sparam))
      - rosserRemainder s (Q * D) ≤ s.siftedSum :=
  linear_sieve_lower_rosser_assembled s D z hz2 hzD hz htm (maxDepth s) sparam ε C₂ Q hQ
    (hTbound_lower_of_levels s D sparam ε C₂ tau hε hlevel htau)

end Salt.Chen
