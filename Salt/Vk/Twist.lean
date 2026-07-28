/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Block
import Salt.ExpSum.Twist

/-!
# VK-TWIST VT-2 — the twisted block Taylor expansion of the ζ-phase

The additive-linear twist `e(βn)` (`β : ℝ`) turns the ζ-phase
`φ(n) = −(t/2π)·log n` into `φ(n) + β·n`.  On a block `n = N₀ + m` this shifts
**only the degree-1 Taylor coefficient**: the twisted phase is the *same*
degree-`k` polynomial with `c₁ ↦ c₁ + β`, with an **identical** remainder — the
remainder of `phi_taylor_block` sees only derivatives of order `≥ 2` of `log`, and
`β·n` has none.

The landed statements:

* `twistCoef β c` — the coefficient vector `c` with `β` added to the degree-1 slot
  (`twistCoef β c j = c j` for every `j ≠ 1`, in particular for the `j ≥ 2` slots
  the VK machinery actually reads).
* `phi_taylor_block_twist` / `phi_taylor_block_twist_PY` — the twisted twins of R1
  (`Salt/Vk/Taylor.lean`), remainder bound **byte-identical** to the untwisted one.
* `vkOrbit_twistCoef` — the orbit coordinate `β_i(y)` is **unchanged** by the twist
  for every `i ≥ 2`.  This is what makes `VkSpaced` (which constrains only
  `js ∈ Icc 2 (k−1)`, `Salt/Vk/Spacing.lean`) and the box separation
  `vk_orbit_fract_sep` transfer verbatim.
* `vk_block_taylor_reduce_twist` — the R4 front end in twisted coefficients: the
  twisted ζ-block sum reduces to a pure polynomial-phase Weyl sum in
  `twistCoef β (vkCoef t N₀)`, plus the *same* Taylor cost.

Conventions (unchanged from the untwisted ladder): `eR x = exp(2πi·x)` with the
`2π` inside, so `e(βn)·n^{−it} = eR (phi t n + β·n)`; `phi` is
`Salt.ExpSum.phi`; no numeral is introduced anywhere — every constant is the
landed one.
-/

namespace Salt.Vk

open Finset Real MeasureTheory Salt.ExpSum Salt.Vmvt
open scoped BigOperators

/-! ## Section 0 — the twisted coefficient vector -/

/-- The twist of a coefficient vector: `β` is added to the **degree-1** slot only.
`twistCoef β (vkCoef t N₀)` is the coefficient vector of the twisted ζ-phase
`φ(t,·) + β·id` on a block. -/
def twistCoef (β : ℝ) (c : ℕ → ℝ) (j : ℕ) : ℝ := c j + (if j = 1 then β else 0)

@[simp] lemma twistCoef_one (β : ℝ) (c : ℕ → ℝ) : twistCoef β c 1 = c 1 + β := by
  simp [twistCoef]

lemma twistCoef_of_ne_one (β : ℝ) (c : ℕ → ℝ) {j : ℕ} (hj : j ≠ 1) :
    twistCoef β c j = c j := by
  simp [twistCoef, hj]

/-- **The blind slots.**  Every coefficient of degree `≥ 2` is untouched by the
twist — these are the only ones the `k`-th difference / the orbit spacing read. -/
lemma twistCoef_of_two_le (β : ℝ) (c : ℕ → ℝ) {j : ℕ} (hj : 2 ≤ j) :
    twistCoef β c j = c j :=
  twistCoef_of_ne_one β c (by omega)

@[simp] lemma twistCoef_zero (β : ℝ) (c : ℕ → ℝ) : twistCoef β c 0 = c 0 :=
  twistCoef_of_ne_one β c (by omega)

/-- **The polynomial split.**  The twisted degree-`k` block polynomial is the
untwisted one plus the linear term `β·m` (`k ≥ 1`). -/
lemma twistCoef_sum_Icc (β : ℝ) (c : ℕ → ℝ) (m : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∑ j ∈ Finset.Icc 1 k, twistCoef β c j * m ^ j
      = (∑ j ∈ Finset.Icc 1 k, c j * m ^ j) + β * m := by
  have hterm : ∀ j ∈ Finset.Icc 1 k,
      twistCoef β c j * m ^ j = c j * m ^ j + (if j = 1 then β * m ^ j else 0) := by
    intro j _
    rw [twistCoef, add_mul]
    congr 1
    by_cases hj : j = 1 <;> simp [hj]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single (1 : ℕ) (fun j _ hj => by simp [hj])
    (fun h => absurd (Finset.mem_Icc.mpr ⟨le_refl 1, hk⟩) h)]
  simp

/-! ## Section 1 — the twisted block Taylor expansion (R1 twin) -/

/-- **VK-TAYLOR-TWIST (real core).**  On the block `x ↦ −(t/2π)·log(N₀+m) + β·x`,
the degree-`k` Taylor polynomial is the untwisted one with `c₁ ↦ c₁ + β`
(`twistCoef β (vkCoef t N₀)`), and the remainder bound is **identical** to
`phi_taylor_block`'s: `≤ (|t|/2π)·(m/N₀)^{k+1}`.  The twist is exactly reproduced
by its own degree-1 coefficient, so it contributes nothing to the error. -/
theorem phi_taylor_block_twist (β t N₀ m : ℝ) (hN : 0 < N₀) (hm : 0 ≤ m) {k : ℕ}
    (hk : 1 ≤ k) :
    |(-(t / (2 * π)) * Real.log (N₀ + m) + β * (N₀ + m))
        - (-(t / (2 * π)) * Real.log N₀ + β * N₀)
        - ∑ j ∈ Finset.Icc 1 k, twistCoef β (vkCoef t N₀) j * m ^ j|
      ≤ (|t| / (2 * π)) * (m / N₀) ^ (k + 1) := by
  rw [twistCoef_sum_Icc β (vkCoef t N₀) m hk]
  have heq : (-(t / (2 * π)) * Real.log (N₀ + m) + β * (N₀ + m))
        - (-(t / (2 * π)) * Real.log N₀ + β * N₀)
        - ((∑ j ∈ Finset.Icc 1 k, vkCoef t N₀ j * m ^ j) + β * m)
      = (-(t / (2 * π)) * Real.log (N₀ + m)) - (-(t / (2 * π)) * Real.log N₀)
        - ∑ j ∈ Finset.Icc 1 k, vkCoef t N₀ j * m ^ j := by ring
  rw [heq]
  exact phi_taylor_block t N₀ m hN hm k

/-- **VK-TAYLOR-TWIST (freeze form).**  The twisted twin of `phi_taylor_block_PY`:
with integer radii `P, Y` and `0 ≤ t`, the twisted block remainder is bounded by
the *same* `2·(t/2π)·((P+Y)/N₀)^{k+1}` for `0 ≤ m ≤ P+Y < N₀`. -/
theorem phi_taylor_block_twist_PY (β t : ℝ) (ht : 0 ≤ t) (N₀ P Y : ℕ) (m : ℝ)
    (hN : 0 < (N₀ : ℝ)) (hm : 0 ≤ m) (hmPY : m ≤ (P : ℝ) + Y) {k : ℕ} (hk : 1 ≤ k) :
    |(-(t / (2 * π)) * Real.log ((N₀ : ℝ) + m) + β * ((N₀ : ℝ) + m))
        - (-(t / (2 * π)) * Real.log (N₀ : ℝ) + β * (N₀ : ℝ))
        - ∑ j ∈ Finset.Icc 1 k, twistCoef β (vkCoef t N₀) j * m ^ j|
      ≤ 2 * (t / (2 * π)) * (((P : ℝ) + Y) / N₀) ^ (k + 1) := by
  rw [twistCoef_sum_Icc β (vkCoef t (N₀ : ℝ)) m hk]
  have heq : (-(t / (2 * π)) * Real.log ((N₀ : ℝ) + m) + β * ((N₀ : ℝ) + m))
        - (-(t / (2 * π)) * Real.log (N₀ : ℝ) + β * (N₀ : ℝ))
        - ((∑ j ∈ Finset.Icc 1 k, vkCoef t (N₀ : ℝ) j * m ^ j) + β * m)
      = (-(t / (2 * π)) * Real.log ((N₀ : ℝ) + m)) - (-(t / (2 * π)) * Real.log (N₀ : ℝ))
        - ∑ j ∈ Finset.Icc 1 k, vkCoef t (N₀ : ℝ) j * m ^ j := by ring
  rw [heq]
  exact phi_taylor_block_PY t ht N₀ P Y m hN hm hmPY k

/-! ## Section 2 — the orbit is blind to the twist above degree 1 -/

/-- Orbit coefficients depend only on the slots `Icc i K`. -/
lemma vkOrbit_congr (K : ℕ) (c c' : ℕ → ℝ) (y : ℝ) (i : ℕ)
    (h : ∀ j ∈ Finset.Icc i K, c j = c' j) :
    vkOrbit K c y i = vkOrbit K c' y i := by
  rw [vkOrbit, vkOrbit]
  exact Finset.sum_congr rfl (fun j hj => by rw [h j hj])

/-- **The orbit is twist-blind above degree 1.**  For every coordinate `i ≥ 2` the
orbit `β_i(y) = ∑_{j ≥ i} C(j,i)·c_j·y^{j−i}` reads only slots `j ≥ i ≥ 2`, which
the twist leaves fixed.  Hence the Diophantine spacing input of `vk_block_core`
(`VkSpaced`, `vk_orbit_fract_sep`, both at `js ∈ Icc 2 (k−1)`) transfers verbatim
from the untwisted to the twisted coefficients. -/
theorem vkOrbit_twistCoef (K : ℕ) (β : ℝ) (c : ℕ → ℝ) (y : ℝ) {i : ℕ} (hi : 2 ≤ i) :
    vkOrbit K (twistCoef β c) y i = vkOrbit K c y i :=
  vkOrbit_congr K _ c y i (fun j hj => by
    rw [Finset.mem_Icc] at hj
    exact twistCoef_of_two_le β c (le_trans hi hj.1))

/-- The `Deg K` (`= {j // j ∈ Icc 1 K}`) form of `vkOrbit_twistCoef`, for the box
centers of `vk_block_core`. -/
theorem vkOrbitPoint_twistCoef (K : ℕ) (β : ℝ) (c : ℕ → ℝ) (y : ℝ) (i : Deg K)
    (hi : 2 ≤ (i : ℕ)) :
    vkOrbitPoint K (twistCoef β c) y i = vkOrbitPoint K c y i :=
  vkOrbit_twistCoef K β c y hi

/-! ## Section 3 — the R4 front end in twisted coefficients -/

/-- **The twisted block Taylor reduction (front end).**  The *twisted* ζ-phase block
sum `∑_{N₀<n≤N₀+P'} e(βn)·n^{−it}` reduces to a pure polynomial-phase Weyl sum in
the twisted coefficients `twistCoef β (vkCoef t N₀)`, plus the **same** Taylor cost
`2π·P'·R` as the untwisted `vk_block_taylor_reduce`.  (The twist's constant part
`β·N₀` is a unit-modulus global phase; its linear part is carried exactly by the
degree-1 coefficient.) -/
theorem vk_block_taylor_reduce_twist (k N₀ P P' Y : ℕ) (t β : ℝ) (ht : 0 ≤ t)
    (hk : 1 ≤ k) (hN : 0 < N₀) (hP' : P' ≤ P) :
    ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n + β * (n : ℝ))‖
      ≤ ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
          eR (∑ j ∈ Finset.Icc 1 k, twistCoef β (vkCoef t N₀) j * (m : ℝ) ^ j)‖
        + 2 * π * ((P' : ℝ) * (2 * (t / (2 * π)) * (((P : ℝ) + Y) / N₀) ^ (k + 1))) := by
  set R : ℝ := 2 * (t / (2 * π)) * (((P : ℝ) + Y) / N₀) ^ (k + 1) with hRdef
  set f : ℤ → ℝ := fun m => phi t ((N₀ : ℤ) + m) + β * (((N₀ : ℤ) + m : ℤ) : ℝ) with hf
  set g : ℤ → ℝ := fun m => (phi t (N₀ : ℤ) + β * ((N₀ : ℤ) : ℝ))
    + ∑ j ∈ Finset.Icc 1 k, twistCoef β (vkCoef t N₀) j * (m : ℝ) ^ j with hg
  -- reindex the block to (0, P']
  have hmap : Finset.Ioc (N₀ : ℤ) ((N₀ : ℤ) + (P' : ℤ))
      = (Finset.Ioc (0 : ℤ) (P' : ℤ)).map (addLeftEmbedding (N₀ : ℤ)) := by
    rw [Finset.map_add_left_Ioc]; norm_num
  have hreindex : ∑ n ∈ Finset.Ioc (N₀ : ℤ) ((N₀ : ℤ) + (P' : ℤ)), eR (phi t n + β * (n : ℝ))
      = ∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (f m) := by
    rw [hmap, Finset.sum_map]
    exact Finset.sum_congr rfl (fun m _ => by rw [hf]; simp [addLeftEmbedding_apply])
  -- the polynomial sum with the constant (twisted) phase pulled out
  have hgsum : ∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m)
      = eR (phi t (N₀ : ℤ) + β * ((N₀ : ℤ) : ℝ)) * ∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
          eR (∑ j ∈ Finset.Icc 1 k, twistCoef β (vkCoef t N₀) j * (m : ℝ) ^ j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by rw [hg, eR_add])
  -- the per-term twisted Taylor bound
  have hR : ∀ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), |f m - g m| ≤ R := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_lt hm.1
    have hmP : (m : ℝ) ≤ (P : ℝ) + Y := by
      have h1 : (m : ℝ) ≤ (P' : ℝ) := by exact_mod_cast hm.2
      have hP'P : (P' : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP'
      have h2 : (0 : ℝ) ≤ (Y : ℝ) := by positivity
      linarith
    have hbase := phi_taylor_block_twist_PY β t ht N₀ P Y (m : ℝ)
      (by exact_mod_cast hN) hm0 hmP hk
    have hfg : f m - g m
        = (-(t / (2 * π)) * Real.log ((N₀ : ℝ) + (m : ℝ)) + β * ((N₀ : ℝ) + (m : ℝ)))
          - (-(t / (2 * π)) * Real.log (N₀ : ℝ) + β * (N₀ : ℝ))
          - ∑ j ∈ Finset.Icc 1 k, twistCoef β (vkCoef t N₀) j * (m : ℝ) ^ j := by
      simp only [hf, hg, Salt.ExpSum.phi]
      push_cast
      ring
    rw [hfg]; exact hbase
  -- assemble
  rw [hreindex]
  have hbr := block_reduction (Finset.Ioc (0 : ℤ) (P' : ℤ)) f g R hR
  have hcard : ((Finset.Ioc (0 : ℤ) (P' : ℤ)).card : ℝ) = (P' : ℝ) := by
    rw [Int.card_Ioc]; simp
  rw [hcard] at hbr
  have hgn : ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m)‖
      = ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
          eR (∑ j ∈ Finset.Icc 1 k, twistCoef β (vkCoef t N₀) j * (m : ℝ) ^ j)‖ := by
    rw [hgsum, norm_mul, norm_eR, one_mul]
  calc ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (f m)‖
      ≤ ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m)‖
        + ‖(∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (f m))
            - ∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m)‖ := by
        have h := norm_add_le (∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m))
          ((∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (f m))
            - ∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m))
        rw [add_sub_cancel] at h
        linarith [h]
    _ ≤ ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m)‖ + 2 * π * ((P' : ℝ) * R) := by
        linarith [hbr]
    _ = ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
          eR (∑ j ∈ Finset.Icc 1 k, twistCoef β (vkCoef t N₀) j * (m : ℝ) ^ j)‖
        + 2 * π * ((P' : ℝ) * R) := by rw [hgn]

end Salt.Vk
