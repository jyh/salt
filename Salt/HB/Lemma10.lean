/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.Sawtooth

/-!
# N7 WAVE A — HB LEMMA 10, RUNG (7.5): the trivial bound on `S_m`

**Gate:** `docs/exploration/n7-assembly-gate-0811.md`, Wave A (§7). Statement design is
LANDED LAW there — R-A1 (bind by CARDINALITY, not by `E`), R-A2 (`I : Finset ℤ`, the
primed conditions as a filter INSIDE the sum), R-A6 (dyadic `m : ℕ`).

**Source:** HB 1983 §7, `docs/sources/hb1983-notes.md:818` —
*"everything reduces to `S_m = Σ′_{n ∈ I} e(m f(n))`, `m > 0`, with the trivial bound
`S_m ≪ E` (7.5)"*.

## What is proved here, and what is deliberately not

`(7.5)` is stated EXACTLY — `‖S_m‖ ≤ #I` — with no `≪` and no `E`. The passage to
`E + 1` is a separate lemma (`card_le_of_mem_Ioc`) so the slack is spent once, in the
open, rather than absorbed into an asymptotic where no reader can price it.

🔑 **`f` is arbitrary, and that is the CONTENT of (7.5), not a shortcut.** The trivial
bound never inspects the phase: every term has modulus one whatever `f` does. HB's two
variants (`(T − Cn̄)/k` and `(T/n − Cn̄)/k`) are R-A3's business at (7.6), where the
phase variation finally matters. Stating (7.5) at general `f` is strictly stronger than
either instance and removes a dependency a reader would otherwise have to check.
-/


open Finset Salt.Weil Salt.LS

namespace Salt.N7

/-- **HB's `S_m`** — the primed exponential sum `Σ′_{n ∈ I} e(m·f(n))`.

The prime is HB's: `(n,k) = 1` together with `n ≡ b (mod q)`. Both ride INSIDE the
definition (R-A2) rather than as hypotheses on the theorem, which is what lets the
`(7.7)` supply rows compose against it without an index-type cast. -/
noncomputable def lem10ExpSum (k q : ℕ) (b : ℤ) (I : Finset ℤ) (m : ℕ) (f : ℤ → ℝ) : ℂ :=
  ∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b), e ((m : ℝ) * f n)

/-- ⭐ **HB (7.5) — THE TRIVIAL BOUND.** `‖S_m‖ ≤ #I`, exactly, with no hypothesis on
`f`, `m`, `k`, `q` or `b`.

*Two things are deliberately absent and their absence is the design (R-A1): there is
no `E`, and there is no `≪`.* The cardinality is the honest bound; the passage to
`E + 1 ≤ 2E` is a separate card lemma at the consumption site, so the slack is spent
once, visibly, instead of being smuggled into an asymptotic. -/
theorem norm_lem10ExpSum_le_card (k q : ℕ) (b : ℤ) (I : Finset ℤ) (m : ℕ) (f : ℤ → ℝ) :
    ‖lem10ExpSum k q b I m f‖ ≤ (I.card : ℝ) := by
  unfold lem10ExpSum
  calc ‖∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b), e ((m : ℝ) * f n)‖
      ≤ ∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b),
          ‖e ((m : ℝ) * f n)‖ := norm_sum_le _ _
    _ = ((I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b)).card : ℝ) := by
        simp [norm_e]
    _ ≤ (I.card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _

/-- **NON-VACUITY.** The bound is attained: at `f = 0` and `I` the singleton `{b}` with
`q = 1`, `k = 1`, the sum is `1` and `#I = 1`. *A `≤` proved by discarding every phase
would read the same as this one if the sum were always zero; it is not.* -/
theorem lem10ExpSum_attains_card :
    lem10ExpSum 1 1 0 {(0 : ℤ)} 1 (fun _ => 0) = 1 := by
  simp [lem10ExpSum]

/-- **THE CARD LEMMA (R-A1's other half), stated where its slack is visible.** If every
`n ∈ I` satisfies `E < n ≤ 2E` then `#I ≤ E + 1`.

⛔ **`1 ≤ E` IS LOAD-BEARING AND I FIRST OMITTED IT — the statement is FALSE without
it.** Witness: `E = -5`, `I = ∅`. The hypothesis holds VACUOUSLY (there is no `n` to
test), the card is `0`, and `E + 1 = -4`, so `0 ≤ -4` is false. *The empty set is the
counterexample, which is why no amount of thinking about the interval finds it — the
interval is not where the falsity lives.* HB states `E ≥ 1` on p.213 and it is not
decoration; a hypothesis that looks like a normalisation is doing real work here. -/
theorem card_le_of_mem_Ioc {E : ℝ} (hE : 1 ≤ E) (I : Finset ℤ)
    (hI : ∀ n ∈ I, E < (n : ℝ) ∧ (n : ℝ) ≤ 2 * E) :
    (I.card : ℝ) ≤ E + 1 := by
  have hsub : I ⊆ Finset.Ioc ⌊E⌋ ⌊2 * E⌋ := by
    intro n hn
    obtain ⟨h1, h2⟩ := hI n hn
    simp only [Finset.mem_Ioc]
    exact ⟨Int.floor_lt.mpr h1, Int.le_floor.mpr h2⟩
  have hcard : I.card ≤ (⌊2 * E⌋ - ⌊E⌋).toNat := by
    have := Finset.card_le_card hsub
    rwa [Int.card_Ioc] at this
  have hmono : ⌊E⌋ ≤ ⌊2 * E⌋ := Int.floor_le_floor (by linarith)
  have hE1 : (⌊E⌋ : ℝ) > E - 1 := by
    have := Int.sub_one_lt_floor E
    linarith
  have h2E : ((⌊2 * E⌋ : ℤ) : ℝ) ≤ 2 * E := Int.floor_le _
  calc (I.card : ℝ) ≤ (((⌊2 * E⌋ - ⌊E⌋).toNat : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((⌊2 * E⌋ : ℤ) : ℝ) - ((⌊E⌋ : ℤ) : ℝ) := by
        have h : (((⌊2 * E⌋ - ⌊E⌋).toNat : ℕ) : ℤ) = ⌊2 * E⌋ - ⌊E⌋ :=
          Int.toNat_of_nonneg (by omega)
        exact_mod_cast h
    _ ≤ E + 1 := by linarith


/-! ## The divisor bookkeeping — gap row 4's open half

The gate calls this *"elementary and Wave A's own"*, and it is; it is recorded here
because `(7.8)` carries `d(k)³` LITERALLY (the freeze rule) and something has to earn
the cube. `d(k)·d(k₀)·d(·) ≤ d(k)³` needs only that a divisor's divisors are among the
original's — `Nat.divisors_subset_of_dvd` plus `Finset.card_le_card`.

📌 *Recorded because it was nearly re-derived: my first search for divisor-count
monotonicity returned EMPTY and the lemma exists. An absent grep is not an absent
lemma — the name was `divisors_subset_of_dvd`, one level below the property I wanted.* -/

/-- **Divisor-count monotonicity under divisibility.** `k₀ ∣ k → d(k₀) ≤ d(k)`. -/
theorem card_divisors_le_of_dvd {k₀ k : ℕ} (hk : k ≠ 0) (h : k₀ ∣ k) :
    k₀.divisors.card ≤ k.divisors.card :=
  Finset.card_le_card (Nat.divisors_subset_of_dvd hk h)

/-- ⭐ **THE `d(k)³` BOOKKEEPING** (gap row 4's open half). Any product of three
divisor-counts, whose last two indices divide the first, is at most `d(k)³`.

*Stated for two arbitrary divisors rather than for the specific pair `(7.8)` produces:
the consumer instantiates, and the general form cannot silently acquire a dependency on
which divisors they were.* -/
theorem divisor_triple_le_cube {k k₀ k₁ : ℕ} (hk : k ≠ 0) (h₀ : k₀ ∣ k) (h₁ : k₁ ∣ k) :
    (k.divisors.card : ℝ) * (k₀.divisors.card : ℝ) * (k₁.divisors.card : ℝ)
      ≤ (k.divisors.card : ℝ) ^ 3 := by
  have m₀ : (k₀.divisors.card : ℝ) ≤ (k.divisors.card : ℝ) := by
    exact_mod_cast card_divisors_le_of_dvd hk h₀
  have m₁ : (k₁.divisors.card : ℝ) ≤ (k.divisors.card : ℝ) := by
    exact_mod_cast card_divisors_le_of_dvd hk h₁
  have hpos : (0 : ℝ) ≤ (k.divisors.card : ℝ) := by positivity
  calc (k.divisors.card : ℝ) * (k₀.divisors.card : ℝ) * (k₁.divisors.card : ℝ)
      ≤ (k.divisors.card : ℝ) * (k.divisors.card : ℝ) * (k₁.divisors.card : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left m₀ hpos) (by positivity)
    _ ≤ (k.divisors.card : ℝ) * (k.divisors.card : ℝ) * (k.divisors.card : ℝ) :=
        mul_le_mul_of_nonneg_left m₁ (by positivity)
    _ = (k.divisors.card : ℝ) ^ 3 := by ring

/-- **THE CUBE IS ATTAINED**, at `k₀ = k₁ = k` — so the bookkeeping bound is not slack
being hidden. A `≤ d(k)³` that could never REACH `d(k)³` would mean the literal cube is
overstated at its source.

⚠️ **THE SOURCE IS NAMED HERE ON PURPOSE: HB 1983's own (7.8)** —
`docs/sources/hb1983-notes.md:832`, where `d(k)³` appears in HB's numbered display, the
cube arriving (`:841`) as `d(k)²·d(k₀) ↦ d(k)³` via `k₀ ∣ k`. **NOT our flagship paper**,
which makes no divisor-cube claim at all (`papers/flagship/main.tex`: zero hits; its only
divisor bound is LINEAR, `S(k;u,v) ≪ d(k)k^{1/2}(k,u,v)^{1/2}`).

📌 *An earlier draft of this docstring said "a claim about the PAPER", unqualified. **This
house has TWO papers** — the SOURCE being formalized and the flagship being written — and
the bare word sent a peer's fence check to the wrong bytes, where it correctly found
nothing. A verdict filed against a paper that never made the claim is a phantom row that
a successor cannot tell from a cleared one.* -/
theorem divisor_triple_attains_cube (k : ℕ) :
    (k.divisors.card : ℝ) * (k.divisors.card : ℝ) * (k.divisors.card : ℝ)
      = (k.divisors.card : ℝ) ^ 3 := by ring

end Salt.N7

/-! ## Axiom audit -/

#audit_axioms Salt.N7.lem10ExpSum
#audit_axioms Salt.N7.norm_lem10ExpSum_le_card
#audit_axioms Salt.N7.lem10ExpSum_attains_card
#audit_axioms Salt.N7.card_le_of_mem_Ioc
#audit_axioms Salt.N7.card_divisors_le_of_dvd
#audit_axioms Salt.N7.divisor_triple_le_cube
#audit_axioms Salt.N7.divisor_triple_attains_cube
