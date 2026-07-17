/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Weil.Kloosterman

/-!
# Weil track, W1.2 + W1.3 — the trace surjection and the Artin–Schreier count

Blueprint: `docs/exploration/pilot.md`, source Harcos §2 Thm 4. Over `K = 𝔽_{p^n}`
with prime field `k = 𝔽_p = ZMod p`, this file supplies the two facts the moment
layer (W2) consumes when it expands a character sum over the Artin–Schreier fibers:

* **W1.2 — trace surjection** (`trace_surjective`): the absolute trace
  `Algebra.trace k K : K →ₗ[k] k` is a `k`-linear surjection (mathlib
  `Algebra.trace_surjective`, valid because a finite extension is separable).

* **W1.3 — the Artin–Schreier map** `δ(x) = x^p − x` (`artinSchreier`), a
  `k`-linear endomorphism of `K`, and Thm 4:
  - `mem_ker_artinSchreier_iff` / `card_ker_artinSchreier` : `ker δ` is the prime
    field, of cardinality `p` (roots of `X^p − X`).
  - `trace_artinSchreier` : `Tr(δ x) = 0` for all `x` (Frobenius-sum telescoping).
  - `range_artinSchreier_eq_ker_trace` : `im δ = ker Tr` (both of `k`-dimension
    `n − 1`, with `im δ ⊆ ker Tr` from the previous fact).
  - `card_artinSchreier_solutions` (**Thm 4, the count**): for `y : K`,
    `#{x : x^p − x = y} = if Tr y = 0 then p else 0`.
-/

namespace Salt.Weil

open scoped BigOperators

section ArtinSchreier

variable (p n : ℕ) [Fact p.Prime]

/-! ### W1.2 — the trace surjection -/

/-- **W1.2.** The absolute trace `Algebra.trace 𝔽_p 𝔽_{p^n} : K →ₗ[k] k` is surjective.
It is `k`-linear by construction (`Algebra.trace` *is* a `LinearMap`); surjectivity is
mathlib's `Algebra.trace_surjective`, which applies because the finite extension `k ⊆ K`
is separable and finite-dimensional. -/
theorem trace_surjective :
    Function.Surjective (Algebra.trace (ZMod p) (GaloisField p n)) :=
  Algebra.trace_surjective (ZMod p) (GaloisField p n)

/-! ### W1.3 — the Artin–Schreier map `δ(x) = x^p − x` -/

/-- **The Artin–Schreier map** `δ(x) = x^p − x = σ(x) − x` as a `ZMod p`-linear
endomorphism of `𝔽_{p^n}`. Additivity is the freshman's dream (`add_pow_char`);
`k`-linearity uses `c^p = c` for `c ∈ 𝔽_p` (`ZMod.pow_card`). -/
noncomputable def artinSchreier : GaloisField p n →ₗ[ZMod p] GaloisField p n where
  toFun x := x ^ p - x
  map_add' a b := by
    change (a + b) ^ p - (a + b) = (a ^ p - a) + (b ^ p - b)
    rw [add_pow_char]; ring
  map_smul' c x := by
    change (c • x) ^ p - c • x = (RingHom.id (ZMod p)) c • (x ^ p - x)
    simp only [RingHom.id_apply, Algebra.smul_def, mul_pow, mul_sub]
    rw [← map_pow, ZMod.pow_card]

@[simp] theorem artinSchreier_apply (x : GaloisField p n) :
    artinSchreier p n x = x ^ p - x := rfl

/-- **W1.3, the kernel (roots of `X^p − X`).** `δ x = 0 ↔ x` lies in the prime
subfield `𝔽_p ⊆ 𝔽_{p^n}`. -/
theorem mem_ker_artinSchreier_iff (x : GaloisField p n) :
    x ∈ LinearMap.ker (artinSchreier p n) ↔ x ∈ (⊥ : Subfield (GaloisField p n)) := by
  rw [LinearMap.mem_ker, artinSchreier_apply, sub_eq_zero,
    Subfield.mem_bot_iff_pow_eq_self (GaloisField p n) p]

/-- The Artin–Schreier kernel has exactly `p` elements (it is the prime field). -/
theorem card_ker_artinSchreier : Nat.card (LinearMap.ker (artinSchreier p n)) = p := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (mem_ker_artinSchreier_iff p n))]
  exact Subfield.card_bot (GaloisField p n) p

/-- **W1.3, `Tr ∘ δ = 0`.** `Tr(x^p − x) = 0` for every `x`: pushing into `K` and
expanding the trace as a Frobenius-orbit sum, `∑_{i<n} (x^p − x)^{p^i}` telescopes to
`x^{p^n} − x = 0`. -/
theorem trace_artinSchreier (hn : n ≠ 0) (x : GaloisField p n) :
    Algebra.trace (ZMod p) (GaloisField p n) (artinSchreier p n x) = 0 := by
  apply FaithfulSMul.algebraMap_injective (ZMod p) (GaloisField p n)
  rw [map_zero, galoisField_trace_eq_sum_frobenius p n hn]
  have hstep : ∀ i, (artinSchreier p n x) ^ (p ^ i) = x ^ (p ^ (i + 1)) - x ^ (p ^ i) := by
    intro i
    rw [artinSchreier_apply, sub_pow_char_pow, ← pow_mul, ← pow_succ']
  rw [Finset.sum_congr rfl (fun i _ => hstep i),
    Finset.sum_range_sub (fun i => x ^ (p ^ i)) n, pow_zero, pow_one,
    galoisField_pow_card p n hn, sub_self]

/-- **W1.3, `im δ = ker Tr`.** The two are equal `k`-subspaces: `im δ ⊆ ker Tr` from
`trace_artinSchreier`, and both have dimension `n − 1` — `ker δ` and `im Tr` each have
dimension `1` (the former is the prime field, the latter is all of `k` by surjectivity),
so rank–nullity pins both `finrank`s. -/
theorem range_artinSchreier_eq_ker_trace (hn : n ≠ 0) :
    LinearMap.range (artinSchreier p n) =
      LinearMap.ker (Algebra.trace (ZMod p) (GaloisField p n)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hle : LinearMap.range (artinSchreier p n) ≤
      LinearMap.ker (Algebra.trace (ZMod p) (GaloisField p n)) := by
    rw [LinearMap.range_le_ker_iff]
    ext x
    simpa using trace_artinSchreier p n hn x
  apply Submodule.eq_of_le_of_finrank_le hle
  -- goal: finrank (ker Tr) ≤ finrank (range δ); both equal n − 1.
  have hK : Module.finrank (ZMod p) (GaloisField p n) = n := GaloisField.finrank p hn
  have hTr := LinearMap.finrank_range_add_finrank_ker
    (Algebra.trace (ZMod p) (GaloisField p n))
  have hrangeTr : Module.finrank (ZMod p)
      (LinearMap.range (Algebra.trace (ZMod p) (GaloisField p n))) = 1 := by
    rw [LinearMap.range_eq_top.mpr (trace_surjective p n), finrank_top, Module.finrank_self]
  have hδ := LinearMap.finrank_range_add_finrank_ker (artinSchreier p n)
  have hkerδ : Module.finrank (ZMod p) (LinearMap.ker (artinSchreier p n)) = 1 := by
    letI : Fintype (LinearMap.ker (artinSchreier p n)) := Fintype.ofFinite _
    have h1 : Fintype.card (LinearMap.ker (artinSchreier p n)) = Fintype.card (ZMod p) ^
        Module.finrank (ZMod p) (LinearMap.ker (artinSchreier p n)) := Module.card_eq_pow_finrank
    rw [ZMod.card, ← Nat.card_eq_fintype_card, card_ker_artinSchreier p n] at h1
    have : p ^ 1 = p ^ Module.finrank (ZMod p) (LinearMap.ker (artinSchreier p n)) := by
      rw [pow_one]; exact h1
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le this).symm
  omega

/-! ### Thm 4 — the count -/

/-- **W1.3 / Harcos Thm 4, the fiber count.** For `y : 𝔽_{p^n}`, the Artin–Schreier
equation `x^p − x = y` has exactly `p` solutions when `Tr y = 0` and none otherwise:
`#{x : x^p − x = y} = if Tr y = 0 then p else 0`. This is the shape W2 uses to
expand `∑_x ψ(Tr(a·(x^p − x) + …))` over the fibers of `δ`. Proof: `y` is hit by `δ`
iff `y ∈ im δ = ker Tr` iff `Tr y = 0`; when hit, the fiber is a coset of `ker δ`,
hence has `#(ker δ) = p` elements. -/
theorem card_artinSchreier_solutions (hn : n ≠ 0) (y : GaloisField p n) :
    Nat.card {x : GaloisField p n // x ^ p - x = y} =
      if Algebra.trace (ZMod p) (GaloisField p n) y = 0 then p else 0 := by
  by_cases hy : Algebra.trace (ZMod p) (GaloisField p n) y = 0
  · rw [if_pos hy]
    have hymem : ∃ x₀, artinSchreier p n x₀ = y := by
      have hmem : y ∈ LinearMap.range (artinSchreier p n) := by
        rw [range_artinSchreier_eq_ker_trace p n hn, LinearMap.mem_ker]; exact hy
      exact LinearMap.mem_range.mp hmem
    obtain ⟨x₀, hx₀⟩ := hymem
    exact Eq.trans (Nat.card_congr
      (({ toFun := fun a => ⟨a.1 - x₀, by
            rw [LinearMap.mem_ker, map_sub, hx₀, artinSchreier_apply, a.2, sub_self]⟩
          invFun := fun z => ⟨z.1 + x₀, by
            rw [← artinSchreier_apply, map_add, LinearMap.mem_ker.mp z.2, hx₀, zero_add]⟩
          left_inv := fun a => by
            apply Subtype.ext; change a.1 - x₀ + x₀ = a.1; ring
          right_inv := fun z => by
            apply Subtype.ext; change z.1 + x₀ - x₀ = z.1; ring } :
        {x : GaloisField p n // x ^ p - x = y} ≃ LinearMap.ker (artinSchreier p n))))
      (card_ker_artinSchreier p n)
  · rw [if_neg hy]
    have hempty : IsEmpty {x : GaloisField p n // x ^ p - x = y} := by
      constructor
      rintro ⟨x, hx⟩
      apply hy
      have hmem : y ∈ LinearMap.range (artinSchreier p n) :=
        LinearMap.mem_range.mpr ⟨x, by rw [artinSchreier_apply]; exact hx⟩
      rw [range_artinSchreier_eq_ker_trace p n hn, LinearMap.mem_ker] at hmem
      exact hmem
    haveI := hempty
    exact Nat.card_of_isEmpty

end ArtinSchreier

end Salt.Weil
