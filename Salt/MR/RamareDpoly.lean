/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Decomp
import Salt.MR.MomentsA2

/-!
# RamareDpoly — the eq(16) → Dirichlet-polynomial `(p,m)` reindex (S8 / MR-CORE, RAMARE-DPOLY)

The seam `RAMARE-DPOLY` of `lemma12_meansq_conditional` (`Salt.MR.MomentsA2`): the
concrete `hdecomp` witness `spoly = Σ_{j∈I} Q_{j,H}·R_{j,H} + errPoly`.  Source:
`docs/sources/1501.04585v4.pdf` pp.19–20 (the Lemma 12 proof, eq (16)).

## The dissolution (RAMARE-DPOLY is C-combinatorial, not D)

`lemma12_meansq_conditional` **decouples** the seam: the analytic content — the
mean-square pricing of the error at the `(T+X)/X·(1/H + 1/P + coprime-tail)` row —
is carried by the *separate* hypothesis `herr : ∫ ‖errPoly‖² ≤ E` (discharged by
the landed keystone `moment_core_bound`, MR Lemma 6 / eq (17)).  What remains in
`hdecomp` is a **pure algebraic identity of Dirichlet polynomials**, no inequality:

* eq (16) itself is *exactly* `Salt.MR.ramare_decomp` (the v4-corrected Ramaré
  identity, already landed) instantiated at `c n = aₙ/n^s` — an `n`-indexed sum.
* The paper writes it in `(p, m)` coordinates (`n = p·m`, `m = n/p`).  Passing from
  the `n`-form to the `(p,m)`-form is the A1 executor's flagged residual (a
  "fiddly `sum_bij'`").  This is **`ramare_decomp_pm`** below — a `Finset.sum_bij'`
  on the sigma-flattened double sums.  It is `C`, not `D`.

Landed here: `ramare_decomp_pm` (the reindex) and `spoly_ramare_eq16` (eq (16) as a
`spoly` identity).  The residual `(p,m)→Σ_j Q_{j,H}·R_{j,H}` regrouping (the
`aₚₘ=bₘcₚ` substitution, the dyadic `p`-blocks, and the overcounting windows
`[Xe^{−1/H},X]`, `[2X,2Xe^{1/H}]`, `[Xe^{−1/H},Xe^{1/H}]`) is mapped in the
RAMARE-DPOLY resistance report — still `C`, gated only on the Lean cost of the
window bookkeeping (see NOTES).

Source pins (D5): MR arXiv **v4** (`1501.04585v4`), §5, Lemma 12, eq (16).
-/

namespace Salt.MR

open Finset
open scoped BigOperators

/-- **R1b — the `(p, m)` reindex of the Ramaré block-prime double sum (the A1
residual).**  The block-prime part of `ramare_decomp` — a sum over `n` (with a
block prime factor) of the Ramaré-weighted expansion over its factorisations
`n = p·(n/p)` — equals the paper's `(p, m)` double sum: over block primes
`P ≤ p ≤ Q` and cofactors `m` with `p·m ∈ S`, of `ramareWeight P Q p m • c (p·m)`.

This is the exact index change `(n, p) ↦ (p, n/p)` (inverse `(p, m) ↦ (p·m, p)`)
that turns eq (16)'s left `n`-sum into its `Σ_{P≤p≤Q} Σ_{X/p≤m≤2X/p}` form.  The
hypothesis `0 ∉ S` (true for `S = Icc 1 N`) rules out the `p·m = 0` degeneracy. -/
theorem ramare_decomp_pm {P Q : ℕ} {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (S : Finset ℕ) (hS0 : 0 ∉ S) (c : ℕ → M) :
    (∑ n ∈ S.filter (fun n => 1 ≤ blockOmega P Q n),
        ∑ p ∈ BlockPrimeDivs P Q n, ramareWeight P Q p (n / p) • c n)
      = ∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
          ∑ m ∈ (S.image (fun n => n / p)).filter (fun m => p * m ∈ S),
            ramareWeight P Q p m • c (p * m) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun x _ => (⟨x.2, x.1 / x.2⟩ : Σ _ : ℕ, ℕ))
    (j := fun y _ => (⟨y.1 * y.2, y.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_ ?_
  · -- hi : i maps the LHS sigma into the RHS sigma
    rintro ⟨n, p⟩ hx
    rw [Finset.mem_sigma] at hx; dsimp only at hx
    rw [Finset.mem_sigma]; dsimp only
    obtain ⟨hn, hp⟩ := hx
    rw [Finset.mem_filter] at hn
    rw [mem_blockPrimeDivs] at hp
    obtain ⟨hpp, hpdvd, _hn0, hPp, hpQ⟩ := hp
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hPp, hpQ⟩, hpp⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_image_of_mem (fun k => k / p) hn.1, ?_⟩
      rw [Nat.mul_div_cancel' hpdvd]; exact hn.1
  · -- hj : j maps the RHS sigma into the LHS sigma
    rintro ⟨p, m⟩ hy
    rw [Finset.mem_sigma] at hy; dsimp only at hy
    rw [Finset.mem_sigma]; dsimp only
    obtain ⟨hp, hm⟩ := hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hPp, hpQ⟩, hpp⟩ := hp
    rw [Finset.mem_filter] at hm
    obtain ⟨_, hpmS⟩ := hm
    have hpm0 : p * m ≠ 0 := fun h => hS0 (h ▸ hpmS)
    have hpB : p ∈ BlockPrimeDivs P Q (p * m) := by
      rw [mem_blockPrimeDivs]; exact ⟨hpp, Dvd.intro m rfl, hpm0, hPp, hpQ⟩
    refine ⟨?_, hpB⟩
    rw [Finset.mem_filter]
    exact ⟨hpmS, Finset.card_pos.mpr ⟨p, hpB⟩⟩
  · -- left_inv : j (i x) = x
    rintro ⟨n, p⟩ hx
    rw [Finset.mem_sigma] at hx; dsimp only at hx
    obtain ⟨_, hp⟩ := hx
    rw [mem_blockPrimeDivs] at hp
    obtain ⟨_, hpdvd, _, _, _⟩ := hp
    dsimp only
    rw [Nat.mul_div_cancel' hpdvd]
  · -- right_inv : i (j y) = y
    rintro ⟨p, m⟩ hy
    rw [Finset.mem_sigma] at hy; dsimp only at hy
    obtain ⟨hp, _⟩ := hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨_, hpp⟩ := hp
    dsimp only
    rw [Nat.mul_div_cancel_left m hpp.pos]
  · -- summand equality
    rintro ⟨n, p⟩ hx
    rw [Finset.mem_sigma] at hx; dsimp only at hx
    obtain ⟨_, hp⟩ := hx
    rw [mem_blockPrimeDivs] at hp
    obtain ⟨_, hpdvd, _, _, _⟩ := hp
    dsimp only
    rw [Nat.mul_div_cancel' hpdvd]

/-- **R1a — the `R_{j,H}` coefficient (coprime branch).**  On the `p ∤ m` part of
eq (16) the Ramaré weight is exactly the paper's `R_{v,H}` coefficient
`1/(#{P≤q≤Q : q|m} + 1) = 1/(ω(m;P,Q) + 1)`.  This is the weight that, paired with
`a_{pm} = b_m c_p`, factors the coprime summand into `(c_p/p^s)·(b_m/m^s)/(ω+1)` —
the integrand of `Q_{j,H}(s)·R_{j,H}(s)`. -/
lemma ramareWeight_coprime (P Q p m : ℕ) (hcop : Nat.Coprime p m) :
    ramareWeight P Q p m = 1 / ((blockOmega P Q m : ℝ) + 1) := by
  rw [ramareWeight, if_pos hcop, blockOmega]

/-- **R1a — the `p²`-correction denominator (non-coprime branch).**  On the `p ∣ m`
part the Ramaré weight is `1/ω(m;P,Q)`, the denominator appearing in the paper's
`p²`-correction term (p.20) `a_{p²m}/(ω(mp;P,Q)·(p²m)^s) − c_p b_{pm}/((ω(mp;P,Q)+1)
·(p²m)^s)`. -/
lemma ramareWeight_not_coprime (P Q p m : ℕ) (hcop : ¬ Nat.Coprime p m) :
    ramareWeight P Q p m = 1 / (blockOmega P Q m : ℝ) := by
  rw [ramareWeight, if_neg hcop, blockOmega, add_zero]

/-- **eq (16) as a `spoly` identity.**  The `σ = 1` Dirichlet polynomial
`spoly N a t = Σ_{1≤n≤N} aₙ/n^{1+it}` splits, for any block `[P,Q]`, as the Ramaré
`(p,m)` double sum plus the coprime tail (`ω(n;P,Q)=0`, i.e. `(n,∏_{P≤p≤Q}p)=1`).
This is MR eq (16), p.19, realised as an exact identity of Dirichlet polynomials:
`ramare_decomp` (the block-prime/tail split) composed with `ramare_decomp_pm` (the
`(p,m)` reindex).  The main term is still in Ramaré-weighted `(p,m)` form; the
downstream `Σ_j Q_{j,H}R_{j,H}` regrouping is the RAMARE-DPOLY residual (NOTES). -/
theorem spoly_ramare_eq16 (N : ℕ) (a : ℕ → ℂ) (P Q : ℕ) (t : ℝ) :
    spoly N a t
      = (∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
          ∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
              (fun m => p * m ∈ Finset.Icc 1 N),
            ramareWeight P Q p m •
              (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)))
        + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
            a n / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
  rw [spoly, ramare_decomp (P := P) (Q := Q) (Finset.Icc 1 N)
      (fun n => a n / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)),
    ramare_decomp_pm (P := P) (Q := Q) (Finset.Icc 1 N) (by simp)
      (fun n => a n / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))]

end Salt.MR
