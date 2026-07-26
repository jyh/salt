/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SeamCalibration
import Salt.MR.SmallStones
import Salt.MR.TypicalDensity

/-!
# TypicalPrice — the typical-density pricing: `Σ_j lemma12Rows` from formula to number

`docs/exploration/hsup-design.md` ⟦V9⟧'s census row and `docs/blueprints/flags.md`'s NEW
entry: `TLegExit.lemma12Rows`' third row — the `[P,Q]`-block-free coefficient mass
`Σ_{n ≤ N, ω(n;P,Q)=0} ‖a_n‖²/n²` — is left UN-PRICED inside `SeamCalibration.seam_row_calibrated`,
so the seam row is a formula and not a number.  This file wires the landed density engine
(`TypicalDensity.typical_density_le`) into that row, prices the whole of `lemma12Rows`, and
collects the `j`-sum at the calibrated ladder.

## The verdict (read this first)

**The calibrated ladder REFUTES MR's own `Σ_j log P_j/log Q_j` demand.**
`SeamCalibration.calQ A G j = 2^{2e_j} = (calP A G j)²`, so

  `log P_j / log Q_j = 1/2` **exactly, at every level** (`log_calP_div_log_calQ`),

hence `Σ_{j=1}^{Jb} log P_j/log Q_j = Jb/2` (`sum_calibrated_ratio_eq`) — never smaller than
`1/2`, and growing with the cutoff.  MR's choice (4) (p.6) is
`P_j = exp(j^{4j}(log Q₁)^{j−1}log P₁)`, `Q_j = exp(j^{4j+2}(log Q₁)^j)`, i.e.

  `log P_j/log Q_j = log P₁/(j² log Q₁)`,

whose `j`-sum is `≤ (π²/6)·log P₁/log Q₁`, and `log P₁/log Q₁ = δ/4` (§9 p.31, small-`h` case).
The `j²` is the mechanism (`docs/sources/mr_extract.md` §6.7 nit 2); the calibrated ladder has
`log P₁/log Q₁ = 1/2` at level 1 ALONE, i.e. `δ = 2` — vacuous for a `1`-bounded `f`, whose two
means differ by at most `2` unconditionally.  So the pin `Q_j = P_j²` cannot deliver §9's
eq (28); the repair is a re-pin `Q_j = P_j^{K_j}` with `K_j ≳ j²·M`, which is a CALIBRATION-tier
statement change (`CalFrame`'s `G_gate` absorbs the `K`; `A_gate_log` only gains a `log K`) and
is deliberately NOT made here (iron rule 1).

Everything else in the wire is landed and generic in the ladder: `sum_lemma12Rows_priced` keeps
the ladder abstract and leaves `Σ_j log P_j/log Q_j` on the right, so a re-pinned ladder plugs
straight in with no further wiring — only `sum_calibrated_ratio_eq` changes.

## Two further findings the arithmetic forces (recorded, NOT repaired here)

**(ii) the `p²` row's grade is too weak at the seam's scales.**  `ramP2mass_win_le` inherits
`SmallStones.ramP2mass_le`'s route — `Σ f² ≤ (Σ f)²` — which returns `64/P²`.  Against the
prefactor `2T + 20N ≍ X_d(T/X_d + 1)` that is `64X_d/P_j²(T/X_d+1)`, and `CalFrame.Q_le_Xd`
gives `X_d ≥ Q_{Jb} ≥ Q_j = P_j²`, so **every level's `p²` row is `≥ 64`** — not small.
MR's own row is `(T/X+1)/P`.  The loss is exactly the Cauchy–Schwarz step: the direct estimate
is `‖coeff_n‖ ≤ 2ω(n)`, `1/n² ≤ 1/X_d²` on the window, and `#(dom ∩ window) ≤ 4X_d/P`, giving
`≤ 16 log₂(2X_d)/(X_d·P)` and hence MR's grade.  The cheap Lean page: `Σ f² ≤ (max f)(Σ f)`
with `max_n ‖coeff_n‖/n ≤ 2ω(n)/X_d` and `2^{ω(n)} ≤ n` (`Nat.prod_primeFactors_dvd` +
`Finset.pow_card_le_prod`), reusing `winTerm_dom_sum_le`'s `8/P` for the `Σ f`.  This is a
PRICING fix (~100 ln); no statement moves.

**(iii) the window row needs `H₁ ≫ 1`, which the frame permits but the exhibited inhabitant
does not take.**  Row 1 collects to `≈ 480(T/X_d+1)·2e²/H_j` per level; at
`calFrame_satisfiable`'s `H₁ = 2` that is `O(1)`, at MR's own
`H_j = j²P₁^{1/6−η}/(log Q₁)^{1/3}` it is negligible.  `CalFrame.H1_pin` (`H₁³ ≤ P₁^{1/2}`)
allows `H₁` up to `P₁^{1/6}`, so this is a CHOICE of inhabitant, not a wall.

## The stones

* **the bridge** — `coprime_bandProd_of_blockOmega_zero`: `ω(n;P,Q) = 0 → (bandProd P Q).Coprime n`
  (the density engine counts by coprimality; `lemma12Rows` filters by `blockOmega`).
* **T-1** — `blockfree_sum_le`: the density COUNT to the WEIGHTED sum.  At `1`-bounded `a`
  supported in the window `[W, 2W]`, `Σ_{n ≤ N, ω(n;P,Q)=0} ‖a_n‖²/n² ≤ C(log P/log Q)/W + 1/W²`.
  The single shell `(W, 2W]` is all the density is asked for: the window support kills every
  other shell, and the endpoint `n = W` is the visible `1/W²`.
* **the `p²` row** — `ramP2mass_win_le`: `Σ_{n≤N}‖ramP2coeff n‖²/n² ≤ 64/P²`, the window
  transplant of `SmallStones.ramP2mass_le` (whose domain `ramHonMR` carries the window; the
  `RamareWindows.ramP2dom` used by `lemma12Rows` does not, so the window arrives from the
  coefficient support and `hwin` instead, through an indicator).
* **T-2** — `lemma12Rows_priced` and `lemma12Rows_priced_ratio` (THE ROW AS A NUMBER):
  `lemma12Rows ≤ 6(2T+20N)((2e·Xd/H+1)(e/Xd²) + 64/P² + C(log P/log Q)/Xd + 1/Xd²)`, and at
  `N ≤ 4Xd` the `(T/Xd + 1)`-shape MR's §8 rows are stated in.
* **T-3** — `sum_lemma12Rows_priced` (the `j`-collection at a generic ladder),
  `sum_lemma12Rows_priced_calibrated` (the same at `calP`/`calQ`/`calH`), and THE VERDICT:
  `log_calP_div_log_calQ` (`= 1/2`), `sum_calibrated_ratio_eq` (`= Jb/2`),
  `calibrated_ratio_not_MR_shape` (no `ρ/j²` shape holds: `ρ ≥ Jb²/2` is forced),
  `calibrated_sum_ratio_ge_half` (never `o(1)`).

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 p.6 ((2), (3), (4), the density line),
§8.2 p.27, §9 p.31 (eq (28), the two parameter sets); `docs/sources/mr_extract.md` §1, §6.4,
§6.6, §6.7; `docs/exploration/hsup-design.md` ⟦V9⟧.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the bridge: `blockOmega = 0` is coprimality to the band radical -/

/-- **The bridge.**  `TypicalDensity` counts the integers coprime to `bandProd P Q` (the
radical of the band); `TLegExit.lemma12Rows` filters by `blockOmega P Q n = 0` (no prime
factor of `n` lies in `[P,Q]`).  For `n ≠ 0` the first follows from the second. -/
lemma coprime_bandProd_of_blockOmega_zero {P Q n : ℕ} (hn : n ≠ 0)
    (h : blockOmega P Q n = 0) : (bandProd P Q).Coprime n := by
  by_contra hcop
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcop
  have hpb : p ∣ bandProd P Q := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpn : p ∣ n := hpdvd.trans (Nat.gcd_dvd_right _ _)
  obtain ⟨hP, hQ⟩ := (prime_dvd_bandProd_iff hp).mp hpb
  have hmem : p ∈ BlockPrimeDivs P Q n := mem_blockPrimeDivs.mpr ⟨hp, hpn, hn, hP, hQ⟩
  rw [blockOmega, Finset.card_eq_zero] at h
  rw [h] at hmem
  exact absurd hmem (Finset.notMem_empty p)

/-! ## §2 — T-1: the density COUNT to the WEIGHTED sum -/

/-- **T-1 — the block-free coefficient mass, priced** (`blockfree_sum_le`).

`lemma12Rows`' third row carries `Σ_{n ≤ N, ω(n;P,Q) = 0} ‖a_n‖²/n²`.  At a `1`-bounded `a`
supported in the dyadic window `[W, 2W]` the sum sees exactly one shell, on which
`1/n² ≤ 1/W²` and the count is `TypicalDensity.typical_density_le`'s
`C(log P/log Q)·W` — so the mass is `C(log P/log Q)/W`, plus the endpoint `n = W`
(`Ioc W (2W)` misses it) at its visible cost `1/W²`.

The three analytic gates are `typical_density_le`'s own, read at `X := W`: MR's regularity
`log Q ≤ √log W`, the large-`W` guard, and the explicit error-domination inequality.  They
ride the statement (law #253). -/
theorem blockfree_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q W N : ℕ) (a : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ W →
      Real.log Q ≤ Real.sqrt (Real.log W) →
      (100 : ℝ) ≤ Real.sqrt (Real.log W) →
      ((Nat.sqrt W : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (W : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) →
      (∀ n, a n ≠ 0 → W ≤ n ∧ n ≤ 2 * W) →
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
          ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ C * (Real.log P / Real.log Q) / (W : ℝ) + 1 / (W : ℝ) ^ 2 := by
  classical
  obtain ⟨C, hC, hden⟩ := typical_density_le
  refine ⟨C, hC, ?_⟩
  intro P Q W N a hP hPQ hW hreg hbig herr ha hsupp
  have hW0 : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  -- ⟦STEP 1: only the window shell survives, and there `‖a n‖² ≤ 1`⟧
  have hpt : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
      ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ (if n ∈ Finset.Icc W (2 * W) then 1 / (n : ℝ) ^ 2 else 0) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1.1
    by_cases hmem : n ∈ Finset.Icc W (2 * W)
    · rw [if_pos hmem]
      have h1 : ‖a n‖ ^ 2 ≤ 1 := by
        have := ha n
        nlinarith [norm_nonneg (a n)]
      exact div_le_div_of_nonneg_right h1 (by positivity) |>.trans_eq rfl
    · rw [if_neg hmem]
      have haz : a n = 0 := by
        by_contra hne
        exact hmem (Finset.mem_Icc.mpr (hsupp n hne))
      rw [haz]
      simp
  have hstep1 : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ ∑ n ∈ ((Finset.Icc W (2 * W)).filter (fun n => blockOmega P Q n = 0)),
          1 / (n : ℝ) ^ 2 := by
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.2, hn.1.2⟩
  -- ⟦STEP 2: peel the endpoint `n = W`, which `Ioc W (2W)` misses⟧
  have hsub : (Finset.Icc W (2 * W)).filter (fun n => blockOmega P Q n = 0)
      ⊆ insert W ((Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases eq_or_lt_of_le hn.1.1 with h | h
    · exact Finset.mem_insert.mpr (Or.inl h.symm)
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨h, hn.1.2⟩, hn.2⟩
  have hnotmem : W ∉ (Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0) := by
    simp
  have hstep2 : ∑ n ∈ ((Finset.Icc W (2 * W)).filter (fun n => blockOmega P Q n = 0)),
        1 / (n : ℝ) ^ 2
      ≤ 1 / (W : ℝ) ^ 2
        + ∑ n ∈ ((Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0)),
            1 / (n : ℝ) ^ 2 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)).trans ?_
    rw [Finset.sum_insert hnotmem]
  -- ⟦STEP 3: the shell, by the density⟧
  have hcard : (((Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0)).card : ℝ)
      ≤ C * (Real.log P / Real.log Q) * W := by
    refine le_trans ?_ (hden P Q W hP hPQ hreg hbig herr)
    have : ((Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0)).card
        ≤ ((Finset.Ioc W (2 * W)).filter (fun n => (bandProd P Q).Coprime n)).card := by
      refine Finset.card_le_card ?_
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
      exact ⟨hn.1, coprime_bandProd_of_blockOmega_zero (by omega) hn.2⟩
    exact_mod_cast this
  have hshell : ∑ n ∈ ((Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0)),
        1 / (n : ℝ) ^ 2
      ≤ C * (Real.log P / Real.log Q) / (W : ℝ) := by
    have hterm : ∀ n ∈ ((Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0)),
        1 / (n : ℝ) ^ 2 ≤ 1 / (W : ℝ) ^ 2 := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      have hnW : (W : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1.1.le
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have hb := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [nsmul_eq_mul] at hb
    refine hb.trans ?_
    have hmul := mul_le_mul_of_nonneg_right hcard
      (by positivity : (0 : ℝ) ≤ 1 / (W : ℝ) ^ 2)
    refine hmul.trans (le_of_eq ?_)
    field_simp
  linarith [hstep1, hstep2, hshell]


/-! ## §3 — the `p²` row: the window transplant of `SmallStones.ramP2mass_le` -/

/-- Squares below the square of the sum, for non-negative terms (`SmallStones`' private
helper, re-derived: the corpus copy is not exported). -/
private lemma sum_sq_le_sq_sum' {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) : ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  have hS : ∀ i ∈ s, f i ^ 2 ≤ f i * ∑ j ∈ s, f j := by
    intro i hi
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hf hi) (hf i hi)
  calc ∑ i ∈ s, f i ^ 2 ≤ ∑ i ∈ s, f i * ∑ j ∈ s, f j := Finset.sum_le_sum hS
    _ = (∑ i ∈ s, f i) * ∑ j ∈ s, f j := by rw [← Finset.sum_mul]
    _ = (∑ i ∈ s, f i) ^ 2 := (sq _).symm

/-- **The windowed `p²` term weight**: `2/(pm)` on the window `[X_d, 2X_d]`, `0` off it.
The `RamareWindows.ramP2dom` domain carries no window (unlike `RamareMR.ramHonMR`), so the
window arrives from the coefficient support through this indicator. -/
noncomputable def winTerm (Xd p m : ℕ) : ℝ :=
  if (Xd ≤ p * m ∧ p * m ≤ 2 * Xd) then 2 / ((p * m : ℕ) : ℝ) else 0

lemma winTerm_nonneg (Xd p m : ℕ) : 0 ≤ winTerm Xd p m := by
  rw [winTerm]; split_ifs <;> positivity

/-- **Each `ramP2coeff` summand vanishes off the window.**  Off `[X_d, 2X_d]` the first term
dies by the support of `a` and the second by `hwin`; on it, `SmallStones.ramP2_term_norm_le`
gives `2`. -/
lemma ramP2_term_norm_le_win {P Q Xd : ℕ} {a b c : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      Xd ≤ p * m ∧ p * m ≤ 2 * Xd)
    {p : ℕ} (hp : p.Prime) (hP : P ≤ p) (hQ : p ≤ Q) (m : ℕ) :
    ‖(ramareWeight P Q p m : ℂ) * a (p * m)
        - b m * c p * ((blockOmega P Q m : ℂ) + 1)⁻¹‖
      ≤ (if (Xd ≤ p * m ∧ p * m ≤ 2 * Xd) then 2 else 0) := by
  by_cases hmem : Xd ≤ p * m ∧ p * m ≤ 2 * Xd
  · rw [if_pos hmem]
    exact ramP2_term_norm_le ha hb hc p m
  · rw [if_neg hmem]
    have h1 : a (p * m) = 0 := by
      by_contra hne
      exact hmem (hasupp (p * m) hne)
    have h2 : b m * c p = 0 := by
      by_contra hne
      refine hmem (hwin p m hp hP hQ ?_)
      rw [mul_comm]
      exact hne
    rw [h1, h2]
    simp

/-- **The windowed cofactor count.**  Cofactors `m` with `p ∣ m`, `m ≥ 1` and `pm ≤ 2X_d`
inject into `[1, 2X_d/p²]` via `m ↦ m/p` (`SmallStones.card_ramP2_cofactors_le`'s page, stated
for an arbitrary carrier so the `ramP2dom` fiber can be fed in directly). -/
private lemma card_dvd_window_le {p Xd : ℕ} (hp : 0 < p) (S : Finset ℕ)
    (hS : ∀ m ∈ S, p ∣ m ∧ 1 ≤ m ∧ p * m ≤ 2 * Xd) :
    (S.card : ℝ) ≤ 2 * (Xd : ℝ) / (p : ℝ) ^ 2 := by
  classical
  have hcard : S.card ≤ (Finset.Icc 1 (2 * Xd / (p * p))).card := by
    refine Finset.card_le_card_of_injOn (fun m => m / p) ?_ ?_
    · intro m hm
      obtain ⟨hdvd, hm1, hpm⟩ := hS m hm
      obtain ⟨k, hk⟩ := hdvd
      have hk0 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, Nat.mul_zero] at hk; omega
        · exact h0
      have hkdiv : m / p = k := by rw [hk]; exact Nat.mul_div_cancel_left k hp
      have hkle : k ≤ 2 * Xd / (p * p) := by
        rw [Nat.le_div_iff_mul_le (by positivity)]
        calc k * (p * p) = p * (p * k) := by ring
          _ = p * m := by rw [hk]
          _ ≤ 2 * Xd := hpm
      simp only [Finset.coe_Icc, Set.mem_Icc, hkdiv]
      exact ⟨hk0, hkle⟩
    · intro m₁ hm₁ m₂ hm₂ heq
      have h1 : m₁ / p * p = m₁ := Nat.div_mul_cancel (hS m₁ hm₁).1
      have h2 : m₂ / p * p = m₂ := Nat.div_mul_cancel (hS m₂ hm₂).1
      have h3 : m₁ / p = m₂ / p := heq
      rw [← h1, ← h2, h3]
  have hIcc : (Finset.Icc 1 (2 * Xd / (p * p))).card = 2 * Xd / (p * p) := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  rw [hIcc] at hcard
  have hstep : (((2 * Xd / (p * p) : ℕ)) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) / ((p * p : ℕ) : ℝ) :=
    Nat.cast_div_le
  have hcast : ((2 * Xd : ℕ) : ℝ) / ((p * p : ℕ) : ℝ) = 2 * (Xd : ℝ) / (p : ℝ) ^ 2 := by
    push_cast; ring
  have hleft : (S.card : ℝ) ≤ (((2 * Xd / (p * p) : ℕ)) : ℝ) := by exact_mod_cast hcard
  rw [hcast] at hstep
  linarith

/-- **The windowed inner row**: `Σ_m winTerm ≤ 4/p²` — the count `2X_d/p²` against the
weight `2/X_d`, exactly `SmallStones.ramP2_inner_row_le`. -/
private lemma winTerm_inner_row_le {p Xd : ℕ} (hp : 0 < p) (hXd : 1 ≤ Xd) (S : Finset ℕ)
    (hS : ∀ m ∈ S, p ∣ m ∧ 1 ≤ m) :
    ∑ m ∈ S, winTerm Xd p m ≤ 4 / (p : ℝ) ^ 2 := by
  classical
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hsplit : ∑ m ∈ S, winTerm Xd p m
      = ∑ m ∈ S.filter (fun m => Xd ≤ p * m ∧ p * m ≤ 2 * Xd), 2 / ((p * m : ℕ) : ℝ) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun m _ => rfl)
  rw [hsplit]
  have hterm : ∀ m ∈ S.filter (fun m => Xd ≤ p * m ∧ p * m ≤ 2 * Xd),
      2 / ((p * m : ℕ) : ℝ) ≤ 2 / (Xd : ℝ) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    have hlo : (Xd : ℝ) ≤ ((p * m : ℕ) : ℝ) := by exact_mod_cast hm.2.1
    exact div_le_div_of_nonneg_left (by norm_num) hXd0 hlo
  have hbound := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hbound
  refine hbound.trans ?_
  have hc : ((S.filter (fun m => Xd ≤ p * m ∧ p * m ≤ 2 * Xd)).card : ℝ)
      ≤ 2 * (Xd : ℝ) / (p : ℝ) ^ 2 := by
    refine card_dvd_window_le hp _ (fun m hm => ?_)
    rw [Finset.mem_filter] at hm
    exact ⟨(hS m hm.1).1, (hS m hm.1).2, hm.2.2⟩
  have hmul : ((S.filter (fun m => Xd ≤ p * m ∧ p * m ≤ 2 * Xd)).card : ℝ) * (2 / (Xd : ℝ))
      ≤ (2 * (Xd : ℝ) / (p : ℝ) ^ 2) * (2 / (Xd : ℝ)) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  refine hmul.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The whole windowed `p²` domain sum** `Σ_{σ ∈ ramP2dom} winTerm ≤ 8/P`: the `p`-rows are
`≤ 4/p²` and the block primes sit in `[P,Q]`, where `SmallStones.sum_inv_sq_tail_le` gives
`2/P`. -/
private lemma winTerm_dom_sum_le (N P Q Xd : ℕ) (hXd : 1 ≤ Xd) (hP : 1 ≤ P) :
    ∑ σ ∈ ramP2dom N P Q, winTerm Xd σ.1 σ.2 ≤ 8 / (P : ℝ) := by
  classical
  rw [ramP2dom, Finset.sum_sigma]
  have hrow : ∀ p ∈ (Finset.Icc P Q).filter Nat.Prime,
      ∑ m ∈ ((((Finset.Icc 1 N).image (fun n => n / p)).filter
          (fun m => p * m ∈ Finset.Icc 1 N)).filter (fun m => p ∣ m)),
          winTerm Xd p m ≤ 4 / (p : ℝ) ^ 2 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    refine winTerm_inner_row_le hp.2.pos hXd _ (fun m hm => ?_)
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hm
    refine ⟨hm.2, ?_⟩
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hm; omega
    · exact h0
  refine (Finset.sum_le_sum hrow).trans ?_
  have hsub : ∑ p ∈ (Finset.Icc P Q).filter Nat.Prime, 4 / (p : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc P Q, 4 / (n : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => by positivity)
  refine hsub.trans ?_
  have heq : ∑ n ∈ Finset.Icc P Q, 4 / (n : ℝ) ^ 2
      = 4 * ∑ n ∈ Finset.Icc P Q, 1 / (n : ℝ) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [heq]
  have htail := sum_inv_sq_tail_le hP Q
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  calc 4 * ∑ n ∈ Finset.Icc P Q, 1 / (n : ℝ) ^ 2 ≤ 4 * (2 / (P : ℝ)) := by linarith
    _ = 8 / (P : ℝ) := by ring

/-- **The `p²` row's mass at the window** (`ramP2mass_win_le`): `Σ_{n≤N}‖ramP2coeff n‖²/n²
≤ 64/P²`.  This is `SmallStones.ramP2mass_le` transplanted from `RamareMR.ramP2coeffMR`
(whose domain `ramHonMR` builds the window in) to the `RamareWindows.ramP2coeff` that
`TLegExit.lemma12Rows` actually carries — the window arriving instead from the support of `a`
and from `hwin`, through `ramP2_term_norm_le_win`. -/
theorem ramP2mass_win_le (N P Q Xd : ℕ) (hXd : 1 ≤ Xd) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      Xd ≤ p * m ∧ p * m ≤ 2 * Xd) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 64 / (P : ℝ) ^ 2 := by
  classical
  have hmaps : ∀ σ ∈ ramP2dom N P Q, σ.1 * σ.2 ∈ Finset.Icc 1 N := by
    intro σ hσ
    rw [ramP2dom] at hσ
    obtain ⟨-, h2⟩ := Finset.mem_sigma.mp hσ
    obtain ⟨h3, -⟩ := Finset.mem_filter.mp h2
    exact (Finset.mem_filter.mp h3).2
  -- pointwise: `‖coeff n‖/n` below the windowed fiber sum
  have hpt : ∀ n ∈ Finset.Icc 1 N,
      ‖ramP2coeff N P Q a b c n‖ / (n : ℝ)
        ≤ ∑ σ ∈ (ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n),
            winTerm Xd σ.1 σ.2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have heq : (∑ σ ∈ (ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n), winTerm Xd σ.1 σ.2)
        = (∑ σ ∈ (ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n),
            (if (Xd ≤ σ.1 * σ.2 ∧ σ.1 * σ.2 ≤ 2 * Xd) then (2 : ℝ) else 0)) / (n : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun σ hσ => ?_)
      rw [Finset.mem_filter] at hσ
      rw [winTerm, hσ.2]
      split_ifs <;> simp
    rw [heq, div_le_div_iff_of_pos_right hn0, ramP2coeff]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun σ hσ => ?_))
    obtain ⟨hσdom, -⟩ := Finset.mem_filter.mp hσ
    rw [ramP2dom] at hσdom
    obtain ⟨hσp, -⟩ := Finset.mem_sigma.mp hσdom
    obtain ⟨hIcc, hprime⟩ := Finset.mem_filter.mp hσp
    obtain ⟨hPle, hleQ⟩ := Finset.mem_Icc.mp hIcc
    exact ramP2_term_norm_le_win ha hb hc hasupp hwin hprime hPle hleQ σ.2
  have hfiber : (∑ n ∈ Finset.Icc 1 N,
        ∑ σ ∈ (ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n), winTerm Xd σ.1 σ.2)
      = ∑ σ ∈ ramP2dom N P Q, winTerm Xd σ.1 σ.2 :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  have hsum : (∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ / (n : ℝ))
      ≤ ∑ σ ∈ ramP2dom N P Q, winTerm Xd σ.1 σ.2 := by
    rw [← hfiber]; exact Finset.sum_le_sum hpt
  have hdomnn : (0 : ℝ) ≤ ∑ σ ∈ ramP2dom N P Q, winTerm Xd σ.1 σ.2 :=
    Finset.sum_nonneg (fun σ _ => winTerm_nonneg _ _ _)
  calc ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      = ∑ n ∈ Finset.Icc 1 N, (‖ramP2coeff N P Q a b c n‖ / (n : ℝ)) ^ 2 :=
        Finset.sum_congr rfl (fun n _ => (div_pow _ _ _).symm)
    _ ≤ (∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ / (n : ℝ)) ^ 2 :=
        sum_sq_le_sq_sum' (fun n _ => by positivity)
    _ ≤ (∑ σ ∈ ramP2dom N P Q, winTerm Xd σ.1 σ.2) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg (fun n _ => by positivity)) hsum 2
    _ ≤ (8 / (P : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hdomnn (winTerm_dom_sum_le N P Q Xd hXd hP) 2
    _ = 64 / (P : ℝ) ^ 2 := by rw [div_pow]; norm_num

/-! ## §4 — T-2: `lemma12Rows` as a NUMBER -/

/-- **T-2 — THE ROW, PRICED** (`lemma12Rows_priced`).  `TLegExit.lemma12Rows`' three rows,
each replaced by a number:

* row 1 (the window error) is already numeric — `(2e·X_d/H + 1)(e/X_d²)`, carried verbatim;
* row 2 (the `p²` correction) is `64/P²` (`ramP2mass_win_le`);
* row 3 (the block-free mass) is `C(log P/log Q)/X_d + 1/X_d²` (`blockfree_sum_le`) — the
  typical-density price, and the whole point of this file.

The gates are exactly the two engines' own, at the window base `X_d` (which is `lemma12Rows`'
own parameter and the base `hwin` pins the coefficient window to): `2 ≤ P ≤ Q`, the density
regime `log Q ≤ √log X_d`, the large-`X_d` guard, the error-domination inequality, the three
`1`-bounds, the support of `a` in `[X_d, 2X_d]`, and `hwin` in `TLegExit.TLeg_bound`'s own
real-cast shape (law #253: no threshold is hidden). -/
theorem lemma12Rows_priced :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q N Xd : ℕ) (H T : ℝ) (a b c : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd → 0 ≤ T →
      Real.log Q ≤ Real.sqrt (Real.log Xd) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      (∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      lemma12Rows N Xd P Q H T a b c
        ≤ 6 * (2 * T + 20 * (N : ℝ))
            * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
                + 64 / (P : ℝ) ^ 2
                + (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)) := by
  obtain ⟨C, hC, hbf⟩ := blockfree_sum_le
  refine ⟨C, hC, ?_⟩
  intro P Q N Xd H T a b c hP hPQ hXd hT hreg hbig herr ha hb hc hasupp hwin
  -- `hwin` in ℕ shape, for `ramP2mass_win_le`
  have hwinN : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      Xd ≤ p * m ∧ p * m ≤ 2 * Xd := by
    intro p m hp hP1 hQ1 hne
    obtain ⟨h1, h2⟩ := hwin p m hp hP1 hQ1 hne
    constructor
    · have h : (Xd : ℝ) ≤ ((p * m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
    · have h : ((p * m : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
  have hpre : (0 : ℝ) ≤ 2 * T + 20 * (N : ℝ) := by positivity
  have h2 := ramP2mass_win_le N P Q Xd hXd (by omega) a b c ha hb hc hasupp hwinN
  have h3 := hbf P Q Xd N a hP hPQ hXd hreg hbig herr ha hasupp
  have e2 := mul_le_mul_of_nonneg_left h2 hpre
  have e3 := mul_le_mul_of_nonneg_left h3 hpre
  rw [lemma12Rows]
  nlinarith [e2, e3]

/-- **T-2, the `(T/X_d + 1)` exit** (`lemma12Rows_priced_ratio`).  MR's §8 error rows are
stated at the grade `(T/X + 1)·(small)`; this is `lemma12Rows_priced` read at that grade, using
`N ≤ 4X_d` (the seam's own `2X_d ≤ N ≤ 2X` with `X ≍ X_d`) to turn `2T + 20N` into
`80X_d(T/X_d + 1)`.  The block-free row's contribution is then EXACTLY

  `480·C·(log P/log Q)·(T/X_d + 1)`,

i.e. MR p.6's per-level complement density `log P_j/log Q_j` at MR's own §8 prefactor — the
number the `j`-collection has to sum. -/
theorem lemma12Rows_priced_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q N Xd : ℕ) (H T : ℝ) (a b c : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd → 0 ≤ T → 0 < H → (N : ℝ) ≤ 4 * (Xd : ℝ) →
      Real.log Q ≤ Real.sqrt (Real.log Xd) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      (∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      lemma12Rows N Xd P Q H T a b c
        ≤ 480 * (T / (Xd : ℝ) + 1)
            * ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 64 * (Xd : ℝ) / (P : ℝ) ^ 2
                + C * (Real.log P / Real.log Q)
                + 1 / (Xd : ℝ)) := by
  obtain ⟨C, hC, hrow⟩ := lemma12Rows_priced
  refine ⟨C, hC, ?_⟩
  intro P Q N Xd H T a b c hP hPQ hXd hT hH hN4 hreg hbig herr ha hb hc hasupp hwin
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hlogP : (0 : ℝ) ≤ Real.log (P : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hP)
  have hlogQ : (0 : ℝ) < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by omega : 1 < P) hPQ)
  have hratio : (0 : ℝ) ≤ Real.log (P : ℝ) / Real.log (Q : ℝ) := by positivity
  have hBnn : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
      + 64 / (P : ℝ) ^ 2
      + (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2) := by positivity
  have hcoefle : 6 * (2 * T + 20 * (N : ℝ)) ≤ 480 * (Xd : ℝ) * (T / (Xd : ℝ) + 1) := by
    have hTid : (Xd : ℝ) * (T / (Xd : ℝ)) = T := by field_simp
    nlinarith [hN4, hT, hXd0]
  have hstep := hrow P Q N Xd H T a b c hP hPQ hXd hT hreg hbig herr ha hb hc hasupp hwin
  refine hstep.trans ?_
  have hmul := mul_le_mul_of_nonneg_right hcoefle hBnn
  refine hmul.trans (le_of_eq ?_)
  field_simp
  ring

/-! ## §5 — T-3: the `j`-collection, and THE VERDICT at the calibrated ladder -/

/-- **T-3 — the `j`-collection, priced** (`sum_lemma12Rows_priced`).  `TLegExit.TLeg_bound`'s
last summand `Σ_{j=1}^{Jb} lemma12Rows` with every row replaced by a number.  The three
non-density rows are left as a `j`-sum (no uniform bound is imposed, so nothing is lost), and
the density rows collect into

  `480·C·(T/X_d + 1)·Σ_{j=1}^{Jb} log P_j/log Q_j`,

which is exactly MR §9 eq (28)'s `Σ_j log P_j/log Q_j` at the §8 prefactor.  **This is the
quantity MR's choice (4) makes small and the calibrated ladder does not** — see
`sum_calibrated_ratio_eq` and `calibrated_ratio_not_MR_shape` below.

The ladder is generic here: any `P_j`, `Q_j`, `H_j` meeting the per-level gates plugs in, so a
re-pinned calibration needs no further wiring. -/
theorem sum_lemma12Rows_priced :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ) (Jb N Xd : ℕ) (T : ℝ)
      (a b c : ℕ → ℂ),
      1 ≤ Xd → 0 ≤ T → (N : ℝ) ≤ 4 * (Xd : ℝ) →
      (∀ j ∈ Finset.Icc 1 Jb, 2 ≤ Pseq j ∧ Pseq j ≤ Qseq j ∧ 0 < Hseq j) →
      (∀ j ∈ Finset.Icc 1 Jb, Real.log (Qseq j : ℝ) ≤ Real.sqrt (Real.log Xd)) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      (∀ j ∈ Finset.Icc 1 Jb,
        ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand (Pseq j) (Qseq j), (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log (Pseq j : ℝ) / Real.log (Qseq j : ℝ))) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j → c p * b m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      ∑ j ∈ Finset.Icc 1 Jb, lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T a b c
        ≤ 480 * (T / (Xd : ℝ) + 1)
            * ((∑ j ∈ Finset.Icc 1 Jb,
                  ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1)
                      * (Real.exp 1 / (Xd : ℝ) ^ 2))
                    + 64 * (Xd : ℝ) / (Pseq j : ℝ) ^ 2
                    + 1 / (Xd : ℝ)))
              + C * ∑ j ∈ Finset.Icc 1 Jb,
                  Real.log (Pseq j : ℝ) / Real.log (Qseq j : ℝ)) := by
  obtain ⟨C, hC, hrow⟩ := lemma12Rows_priced_ratio
  refine ⟨C, hC, ?_⟩
  intro Pseq Qseq Hseq Jb N Xd T a b c hXd hT hN4 hgates hreg hbig herr ha hb hc hasupp hwin
  have hlevel : ∀ j ∈ Finset.Icc 1 Jb,
      lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T a b c
        ≤ 480 * (T / (Xd : ℝ) + 1)
            * ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1)
                  * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 64 * (Xd : ℝ) / (Pseq j : ℝ) ^ 2
                + 1 / (Xd : ℝ)
                + C * (Real.log (Pseq j : ℝ) / Real.log (Qseq j : ℝ))) := by
    intro j hj
    obtain ⟨hP, hPQ, hH⟩ := hgates j hj
    exact (hrow (Pseq j) (Qseq j) N Xd (Hseq j) T a b c hP hPQ hXd hT hH hN4 (hreg j hj) hbig
      (herr j hj) ha hb hc hasupp (hwin j hj)).trans (le_of_eq (by ring))
  refine (Finset.sum_le_sum hlevel).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **THE RATIO AT THE CALIBRATED LADDER IS `1/2`, EXACTLY, AT EVERY LEVEL.**
`SeamCalibration.calQ A G j = 2^{2e_j}` and `calP A G j = 2^{e_j}`, so
`log P_j/log Q_j = e_j log 2/(2e_j log 2) = 1/2` — independent of `j`, of `A`, and of `G`. -/
theorem log_calP_div_log_calQ {A G : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (j : ℕ) :
    Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQ A G j : ℕ) : ℝ) = 1 / 2 := by
  have hE : 0 < calE A G j := by
    rw [calE]
    exact Nat.mul_pos (Nat.mul_pos hA (pow_pos hG (j - 1)))
      (pow_pos (Nat.factorial_pos j) 2)
  have hER : (0 : ℝ) < ((calE A G j : ℕ) : ℝ) := by exact_mod_cast hE
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [log_calP, log_calQ]
  field_simp

/-- **The `j`-collection of the calibrated ratio is `Jb/2`** — LINEAR in the cutoff, and never
below `1/2`.  MR §9 eq (28) needs `Σ_j log P_j/log Q_j` SMALL (it multiplies `2 + 1/50` and has
to land under Theorem 1's `δ`); under MR's own choice (4) the sum is
`(log P₁/log Q₁)·Σ_j 1/j² ≤ (π²/6)(log P₁/log Q₁)` with `log P₁/log Q₁ = δ/4`.  Here it is
`Jb/2`. -/
theorem sum_calibrated_ratio_eq {A G : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (Jb : ℕ) :
    ∑ j ∈ Finset.Icc 1 Jb,
        Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQ A G j : ℕ) : ℝ)
      = (Jb : ℝ) / 2 := by
  have hcongr : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQ A G j : ℕ) : ℝ) = 1 / 2 :=
    fun j _ => log_calP_div_log_calQ hA hG j
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  push_cast
  ring

/-- **THE VERDICT** (`calibrated_ratio_not_MR_shape`).  MR's choice (4) delivers
`log P_j/log Q_j = log P₁/(j² log Q₁)`, i.e. the `1/j²`-shape whose `j`-sum converges
uniformly in the cutoff.  The calibrated ladder cannot meet that shape at ANY constant `ρ`:
`ρ/j² ≥ 1/2` at `j = Jb` forces `ρ ≥ Jb²/2`, which grows with the cutoff.  Equivalently, the
pin `Q_j = P_j²` is what fails — not the wire. -/
theorem calibrated_ratio_not_MR_shape {A G : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) {Jb : ℕ}
    (hJb : 1 ≤ Jb) {ρ : ℝ}
    (hMR : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQ A G j : ℕ) : ℝ)
        ≤ ρ / (j : ℝ) ^ 2) :
    (Jb : ℝ) ^ 2 / 2 ≤ ρ := by
  have hJbR : (1 : ℝ) ≤ (Jb : ℝ) := by exact_mod_cast hJb
  have h := hMR Jb (Finset.mem_Icc.mpr ⟨hJb, le_refl Jb⟩)
  rw [log_calP_div_log_calQ hA hG Jb] at h
  rw [le_div_iff₀ (by positivity)] at h
  linarith

/-- **The calibrated collection is never `o(1)`**: `Σ_{j=1}^{Jb} log P_j/log Q_j ≥ 1/2` for
every cutoff `Jb ≥ 1`.  The `j = 1` term alone is `1/2`, so in MR §9's accounting the row
contributes `(2 + 1/50)/2 ≈ 1.02` — of the same order as the trivial bound `2` for a
`1`-bounded `f`, and nowhere near `δ`. -/
theorem calibrated_sum_ratio_ge_half {A G : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) {Jb : ℕ}
    (hJb : 1 ≤ Jb) :
    (1 : ℝ) / 2 ≤ ∑ j ∈ Finset.Icc 1 Jb,
        Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQ A G j : ℕ) : ℝ) := by
  rw [sum_calibrated_ratio_eq hA hG Jb]
  have : (1 : ℝ) ≤ (Jb : ℝ) := by exact_mod_cast hJb
  linarith

/-- **T-3 at the calibrated ladder — the seam row's `Σ_j lemma12Rows`, AS A NUMBER**
(`sum_lemma12Rows_priced_calibrated`).  `sum_lemma12Rows_priced` at
`P_j := calP A G j`, `Q_j := calQ A G j`, `H_j := calH H₁ j`, with the density collection
evaluated by `sum_calibrated_ratio_eq`:

  `Σ_j lemma12Rows ≤ 480(T/X_d+1)·(Σ_j[…] + C·Jb/2)`.

The `C·Jb/2` is the finding: it is a CONSTANT times the cutoff, not a small quantity.  Under a
re-pinned ladder `Q_j = P_j^{K_j}` with `K_j = j²M` the same theorem returns `C·(π²/6)/M`
through `sum_lemma12Rows_priced`'s generic form — no statement here changes. -/
theorem sum_lemma12Rows_priced_calibrated :
    ∃ C : ℝ, 0 < C ∧ ∀ (A G Jb N Xd : ℕ) (H1 T : ℝ) (a b c : ℕ → ℂ),
      1 ≤ A → 1 ≤ G → 1 ≤ Xd → 0 ≤ T → 0 < H1 → (N : ℝ) ≤ 4 * (Xd : ℝ) →
      (∀ j ∈ Finset.Icc 1 Jb, Real.log ((calQ A G j : ℕ) : ℝ) ≤ Real.sqrt (Real.log Xd)) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      (∀ j ∈ Finset.Icc 1 Jb,
        ((Nat.sqrt Xd : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQ A G j), (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQ A G j : ℕ) : ℝ))) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQ A G j →
        c p * b m ≠ 0 → (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      ∑ j ∈ Finset.Icc 1 Jb,
          lemma12Rows N Xd (calP A G j) (calQ A G j) (calH H1 j) T a b c
        ≤ 480 * (T / (Xd : ℝ) + 1)
            * ((∑ j ∈ Finset.Icc 1 Jb,
                  ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                      * (Real.exp 1 / (Xd : ℝ) ^ 2))
                    + 64 * (Xd : ℝ) / ((calP A G j : ℕ) : ℝ) ^ 2
                    + 1 / (Xd : ℝ)))
              + C * ((Jb : ℝ) / 2)) := by
  obtain ⟨C, hC, hsum⟩ := sum_lemma12Rows_priced
  refine ⟨C, hC, ?_⟩
  intro A G Jb N Xd H1 T a b c hA hG hXd hT hH1 hN4 hreg hbig herr ha hb hc hasupp hwin
  have hgates : ∀ j ∈ Finset.Icc 1 Jb,
      2 ≤ calP A G j ∧ calP A G j ≤ calQ A G j ∧ 0 < calH H1 j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hE : 0 < calE A G j := by
      rw [calE]
      exact Nat.mul_pos (Nat.mul_pos hA (pow_pos hG (j - 1)))
        (pow_pos (Nat.factorial_pos j) 2)
    refine ⟨?_, ?_, ?_⟩
    · rw [calP]
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ calE A G j := Nat.pow_le_pow_right (by norm_num) hE
    · rw [calP, calQ]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · rw [calH]
      have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
      positivity
  have h := hsum (calP A G) (calQ A G) (calH H1) Jb N Xd T a b c hXd hT hN4 hgates hreg hbig
    herr ha hb hc hasupp hwin
  rwa [sum_calibrated_ratio_eq hA hG Jb] at h

end Salt.MR
