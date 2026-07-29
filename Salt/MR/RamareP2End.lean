/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RamareMR

/-!
# `RamareP2End` — ⟦THE ENDPOINT WALL⟧'s FUSED `p²` row

Flags: ⟦ENDPOINT-ROW-SCOPE⟧ (the fusion design), ⟦ENDPOINT-REF⟧ (the v2 amendments).

**THE WALL.**  `SeamRowWindowed.spoly_ramare_split_mr_windowed` reads its factorization at
the CLOSED window antecedent `X ≤ p·m`, and the door's own cut is HALF-OPEN (`M4DoorRow`'s
`hsupp0`/`hasupp` straddle): at `p·m = X` the datum is `0` while the pair's right-hand side
is not, so the closed law carries an extra endpoint obligation on the datum
(`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` — it is FORCED, not a convenience).

**THE REPAIR IS A FUSION, NOT A FIFTH ROW.**  A genuine fifth Cauchy–Schwarz row would make
the prefactor `5` and `5·520 = 2600 > 2160 = 3·720` — the seam half would no longer fit
`CapFreeArm3.A2Frame3.err`'s standing right-hand side, and no `moment_split5` exists.  So the
endpoint defect is FUSED into the `p²` row instead: its inner filter is enlarged from
`p ∣ m` to

  `p ∣ m  ∨  p·m = X`,

which is exactly the complement of the STRICT antecedent `X < p·m` inside `ramHonMR`.  The
split stays at FOUR rows and `M4ErrRewire.err_grade_fit`'s `4·520 ≤ 2160` is untouched.

**⟦AMENDMENT 6 — SIBLING DISCIPLINE IS LOAD-BEARING.**  The landed `ramP2domMR`,
`ramP2coeffMR`, `ramP2corrMR` are byte-untouched: `SmallStones`:385-460 reads their exact
shapes.  Everything here is a NEW sibling, and the two families coexist.

The price of the fusion is paid in `M4P2MR`: the max half is FREE (the fibre injection into
`primeFactors` never used `p ∣ m`), and the `Σ` half gains `2·ω(X)/X`, whence the fused stone

  `Σ_{n≤N} ‖ramP2coeffEndMR n‖²/n² ≤ 16·log₂(2X)/(X·P) + 4·(log₂(2X))²/X²`.
-/

noncomputable section

namespace Salt.MR

open Finset
open scoped BigOperators

/-! ## §1 — THE FUSED `p²` FAMILY -/

/-- **THE FUSED `p²` DOMAIN**: block-prime/cofactor pairs `(p,m)` with `X ≤ pm ≤ 2X` and
`p ∣ m` **OR** `p·m = X`.  `RamareMR.ramP2domMR` with the endpoint fibre glued on. -/
noncomputable def ramP2domEndMR (N X P Q : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  ((Finset.Icc P Q).filter Nat.Prime).sigma
    (fun p => (ramHonMR N X p).filter (fun m => p ∣ m ∨ p * m = X))

/-- **THE FUSED `p²`-CORRECTION**: `RamareMR.ramP2corrMR` at the enlarged inner filter.  The
clean term `ramCleanMR` does NOT move — the fusion only reassigns which cofactors of
`ramHonMR` are repaired. -/
noncomputable def ramP2corrEndMR (N X P Q : ℕ) (a b c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
    ∑ m ∈ (ramHonMR N X p).filter (fun m => p ∣ m ∨ p * m = X),
      (ramareWeight P Q p m • (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
        - (b m * c p / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
            * ((blockOmega P Q m : ℂ) + 1)⁻¹)

/-- **THE FUSED `p²` COEFFICIENT** at frequency `n` — `RamareMR.ramP2coeffMR`'s sibling over
the fused domain. -/
noncomputable def ramP2coeffEndMR (N X P Q : ℕ) (a b c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ σ ∈ (ramP2domEndMR N X P Q).filter (fun σ => σ.1 * σ.2 = n),
    ((ramareWeight P Q σ.1 σ.2 : ℂ) * a (σ.1 * σ.2)
      - b σ.2 * c σ.1 * ((blockOmega P Q σ.2 : ℂ) + 1)⁻¹)

/-! ## §2 — THE `spoly`/MOMENT/CONTINUITY TRIPLE

`RamareMR`:678-726 verbatim at the fused family.  The fibre map `hmaps` discards the inner
filter predicate outright — it reads only `ramHonMR`'s own window — so the transplant is
byte-for-byte. -/

theorem ramP2corrEndMR_eq_spoly (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (a b c : ℕ → ℂ)
    (t : ℝ) :
    ramP2corrEndMR N X P Q a b c t = spoly N (ramP2coeffEndMR N X P Q a b c) t := by
  classical
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hNR : 2 * (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmaps : ∀ σ ∈ ((Finset.Icc P Q).filter Nat.Prime).sigma
      (fun p => (ramHonMR N X p).filter (fun m => p ∣ m ∨ p * m = X)),
      σ.1 * σ.2 ∈ Finset.Icc 1 N := by
    intro σ hσ
    rw [Finset.mem_sigma] at hσ
    obtain ⟨-, h2⟩ := hσ
    rw [Finset.mem_filter, ramHonMR, Finset.mem_filter] at h2
    obtain ⟨⟨-, hlo, hhi⟩, -⟩ := h2
    rw [Finset.mem_Icc]
    constructor
    · have h : (1 : ℝ) ≤ ((σ.1 * σ.2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
    · have h : ((σ.1 * σ.2 : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; linarith
      exact_mod_cast h
  rw [ramP2corrEndMR, Finset.sum_sigma', ← Finset.sum_fiberwise_of_maps_to hmaps, spoly]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [ramP2coeffEndMR, Finset.sum_div]
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  rw [Finset.mem_filter] at hσ
  rw [Complex.real_smul, ← mul_div_assoc, div_mul_eq_mul_div, div_sub_div_same, hσ.2]

/-- **THE FUSED `p²` ROW'S MOMENT.**  `moment_core_bound` at the `(2T+20N)·Σ‖·‖²/n²` grade —
`RamareMR.ramP2corrMR_moment`'s sibling. -/
theorem ramP2corrEndMR_moment (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (a b c : ℕ → ℂ)
    (T : ℝ) :
    (∫ t in (-T)..T, ‖ramP2corrEndMR N X P Q a b c t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ))
          * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 := by
  have hcongr : (∫ t in (-T)..T, ‖ramP2corrEndMR N X P Q a b c t‖ ^ 2)
      = ∫ t in (-T)..T, ‖spoly N (ramP2coeffEndMR N X P Q a b c) t‖ ^ 2 :=
    intervalIntegral.integral_congr
      (fun t _ => by rw [ramP2corrEndMR_eq_spoly N X P Q hX hN a b c t])
  rw [hcongr]
  exact moment_core_bound N (ramP2coeffEndMR N X P Q a b c) T

lemma continuous_ramP2corrEndMR (N X P Q : ℕ) (a b c : ℕ → ℂ) :
    Continuous (ramP2corrEndMR N X P Q a b c) := by
  classical
  unfold ramP2corrEndMR
  refine continuous_finsetSum _ (fun p hp => continuous_finsetSum _ (fun m hm => ?_))
  rw [Finset.mem_filter] at hp
  obtain ⟨hmH, -⟩ := Finset.mem_filter.mp hm
  rw [ramHonMR, Finset.mem_filter, Finset.mem_Icc] at hmH
  have hm0 : m ≠ 0 := by
    obtain ⟨⟨h1, -⟩, -⟩ := hmH
    omega
  exact ((continuous_cterm (Nat.mul_ne_zero hp.2.pos.ne' hm0) (a (p * m))).const_smul _).sub
    ((continuous_cterm (Nat.mul_ne_zero hp.2.pos.ne' hm0) (b m * c p)).mul continuous_const)

end Salt.MR

end
