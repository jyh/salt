/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.TBalFinal

/-!
# T-BAL THE COMPOSE — the genuinely-final rungs

The complex-scale (`ρ`) extraction chain, assembled from the landed suppliers
(`docs/blueprints/flags.md`, node T-BAL-R6RHO-2). Everything here mirrors the β₀ template in
`Salt/SW/DHExtractW.lean`, re-run at the complex weight `n^{−ρ}·dhKernR(n/Y)`.

* **R6-4@ρ** (`dhA_kernel_reduction_rho`) — the EXACT reduction of the `m`-restricted complex
  detector to the `m = 1` template `dhD0rho` at rescaled real scales `Y/(m·k)`. The ℂ re-runs of
  the ℝ-weight reindex infra (`sum_dvd_reindex`, `sum_coprime_eq_moebius_multiples`,
  `inner_cop_swap_wt`, `weighted_char_count`); the `(†)` split `dhA_mul_eq_sum` is
  coefficient-generic (reused directly).
* **Collection R6-5/6/7@ρ** — the real, exponent-free collection lemmas
  (`selHmul_collection`, `sum_gcW_selNu_eq_selMainTerm`, `sum_gcW_pairkernel_le`) applied to the
  EXACT complex per-`m` main (`unmoll_extraction_rho`'s `/((1−ρ)(2−ρ))` coefficient).
* **E(ρ) assembly** (`dh_extraction_upper_rho`) — the norm bound
  `‖Σ dhCoeffW·n^{−ρ}·dhKernR − L(1,χ)·selMainTerm·Y^{1−ρ}/((1−ρ)(2−ρ))‖ ≤ C₂ρ·z·(1+log z²)⁹·
  Y^{1/2−σ}` (the exact analog of `dh_extraction_upper_W`).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open Complex Finset ArithmeticFunction

noncomputable section

namespace Salt.SW

variable {q : ℕ}

/-! ## §1 — the ℂ reindex primitives (ℂ re-runs of the ℝ-weight infra) -/

/-- ℂ re-run of `sum_dvd_reindex` (pure reindex bijection `d = k·e`). -/
private lemma sum_dvd_reindex_C {k N : ℕ} (hk : 1 ≤ k) (F : ℕ → ℂ) :
    ∑ d ∈ (Finset.Icc 1 N).filter (fun d => k ∣ d), F d
      = ∑ e ∈ Finset.Icc 1 (N / k), F (k * e) := by
  have himg : (Finset.Icc 1 N).filter (fun d => k ∣ d)
      = (Finset.Icc 1 (N / k)).image (fun e => k * e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hd1, hdN⟩, hkd⟩
      obtain ⟨e, rfl⟩ := hkd
      refine ⟨e, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos e with rfl | he
        · simp at hd1
        · exact he
      · exact (Nat.le_div_iff_mul_le hk).mpr (by rw [mul_comm]; exact hdN)
    · rintro ⟨e, ⟨he1, heN⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hk he1, ?_⟩, Dvd.intro e rfl⟩
      rw [mul_comm]; exact (Nat.le_div_iff_mul_le hk).mp heN
  rw [himg, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hk hxy

/-- ℂ re-run of `sum_divisors_moebius_real` (`Σ_{k∣m} μ(k) = [m=1]`). -/
private lemma sum_divisors_moebius_C (m : ℕ) :
    ∑ k ∈ m.divisors, (moebius k : ℂ) = if m = 1 then (1 : ℂ) else 0 := by
  have hint : ∑ k ∈ m.divisors, (moebius k : ℤ) = if m = 1 then (1 : ℤ) else 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
        ArithmeticFunction.one_apply]
  have hcast : ∑ k ∈ m.divisors, (moebius k : ℂ)
      = ((∑ k ∈ m.divisors, (moebius k : ℤ) : ℤ) : ℂ) := by push_cast; rfl
  rw [hcast, hint]; split_ifs <;> norm_num

/-- ℂ re-run of `sum_coprime_eq_moebius_multiples`. -/
private lemma sum_coprime_eq_moebius_multiples_C (g N : ℕ) (hg : 1 ≤ g) (F : ℕ → ℂ) :
    ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d g), F d
      = ∑ k ∈ g.divisors, (moebius k : ℂ) * ∑ e ∈ Finset.Icc 1 (N / k), F (k * e) := by
  have hg0 : g ≠ 0 := by omega
  have hset : ∀ d : ℕ, g.divisors.filter (fun k => k ∣ d) = (Nat.gcd g d).divisors := by
    intro d
    ext k
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hgcd0 : Nat.gcd g d ≠ 0 := by
      have : 0 < Nat.gcd g d := Nat.gcd_pos_of_pos_left d (by omega)
      omega
    constructor
    · rintro ⟨⟨hkg, _⟩, hkd⟩; exact ⟨⟨hkg, hkd⟩, hgcd0⟩
    · rintro ⟨⟨hkg, hkd⟩, _⟩; exact ⟨⟨hkg, hg0⟩, hkd⟩
  have hpt : ∀ d : ℕ, ∑ k ∈ g.divisors, (moebius k : ℂ) * (if k ∣ d then F d else 0)
      = if Nat.Coprime d g then F d else 0 := by
    intro d
    have hrw : ∑ k ∈ g.divisors, (moebius k : ℂ) * (if k ∣ d then F d else 0)
        = F d * ∑ k ∈ g.divisors.filter (fun k => k ∣ d), (moebius k : ℂ) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      exact Finset.sum_congr rfl (fun k _ => by split_ifs <;> ring)
    rw [hrw, hset d, sum_divisors_moebius_C]
    by_cases hc : Nat.Coprime d g
    · have hg1 : Nat.gcd g d = 1 := by rw [Nat.gcd_comm]; exact hc
      rw [if_pos hg1, if_pos hc, mul_one]
    · have hg1 : ¬ Nat.gcd g d = 1 := by rw [Nat.gcd_comm]; exact hc
      rw [if_neg hg1, if_neg hc, mul_zero]
  have hRHS : ∑ k ∈ g.divisors, (moebius k : ℂ) * ∑ e ∈ Finset.Icc 1 (N / k), F (k * e)
      = ∑ d ∈ Finset.Icc 1 N, (if Nat.Coprime d g then F d else 0) := by
    have e1 : ∀ k ∈ g.divisors, (moebius k : ℂ) * ∑ e ∈ Finset.Icc 1 (N / k), F (k * e)
        = ∑ d ∈ Finset.Icc 1 N, (moebius k : ℂ) * (if k ∣ d then F d else 0) := by
      intro k hk
      rw [← sum_dvd_reindex_C (Nat.pos_of_mem_divisors hk) F, Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun d _ => hpt d)
  rw [Finset.sum_filter, hRHS]

/-- ℂ re-run of `inner_cop_swap_wt` (weighted coprime divisor swap). -/
private lemma inner_cop_swap_wt_C (χ : DirichletCharacter ℂ q) (w : ℕ → ℂ) (κ y : ℕ) :
    ∑ t ∈ Finset.Icc 1 y,
        (∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d κ), (chiRe χ d : ℂ)) * w t
      = ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Nat.Coprime d κ),
          (chiRe χ d : ℂ) * ∑ s ∈ Finset.Icc 1 (y / d), w (d * s) := by
  have hstep : ∀ t ∈ Finset.Icc 1 y,
      (∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d κ), (chiRe χ d : ℂ)) * w t
        = ∑ d ∈ Finset.Icc 1 y,
            (if d ∣ t ∧ Nat.Coprime d κ then (chiRe χ d : ℂ) * w t else 0) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have hset : t.divisors.filter (fun d => Nat.Coprime d κ)
        = (Finset.Icc 1 y).filter (fun d => d ∣ t ∧ Nat.Coprime d κ) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hdvd, _⟩, hcop⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) ht.2⟩, hdvd, hcop⟩
      · rintro ⟨⟨hd1, _⟩, hdvd, hcop⟩
        exact ⟨⟨hdvd, by omega⟩, hcop⟩
    rw [hset, Finset.sum_filter, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun d _ => by split_ifs <;> ring)
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  by_cases hcop : Nat.Coprime d κ
  · rw [if_pos hcop,
        Finset.sum_congr rfl (fun t _ => if_congr (and_iff_left hcop) rfl rfl),
        ← Finset.sum_filter, ← Finset.mul_sum, sum_dvd_reindex_C hd.1 w]
  · rw [if_neg hcop]
    exact Finset.sum_eq_zero (fun t _ => if_neg (fun h => hcop h.2))

/-- ℂ re-run of `weighted_char_count` (the `dhA = χ_ℝ ∗ 1` weighted swap). -/
private lemma weighted_char_count_C (χ : DirichletCharacter ℂ q) (h : ℕ → ℂ) (L : ℕ) :
    ∑ N ∈ Finset.Icc 1 L, (dhA χ N : ℂ) * h N
      = ∑ e ∈ Finset.Icc 1 L, (chiRe χ e : ℂ) * ∑ s ∈ Finset.Icc 1 (L / e), h (e * s) := by
  have hstep : ∀ N ∈ Finset.Icc 1 L, (dhA χ N : ℂ) * h N
      = ∑ e ∈ Finset.Icc 1 L, (if e ∣ N then (chiRe χ e : ℂ) * h N else 0) := by
    intro N hN
    rw [Finset.mem_Icc] at hN
    have hset : N.divisors = (Finset.Icc 1 L).filter (fun e => e ∣ N) := by
      ext e
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) hN.2⟩, hdvd⟩
      · rintro ⟨_, hdvd⟩; exact ⟨hdvd, by omega⟩
    have hdhA : (dhA χ N : ℂ) = ∑ d ∈ N.divisors, (chiRe χ d : ℂ) := by
      rw [dhA]; push_cast; rfl
    rw [hdhA, hset, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Finset.mem_Icc] at he
  rw [← Finset.sum_filter, ← Finset.mul_sum, sum_dvd_reindex_C he.1 h]

/-! ## §2 — R6-4@ρ : the EXACT reduction to the `dhD0rho` template -/

/-- **R6-4@ρ per-`g` core.** ℂ re-run of `dhA_kernel_reduction_inner`: for `g ∣ m`, the
`κ = m/g`-coprime inner sum against the complex kernel weight collapses onto `dhD0rho` at the
rescaled real scales `Y/(m·k)`. -/
private lemma dhA_kernel_reduction_inner_rho (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (ρ : ℂ) {m : ℕ} (hm : 1 ≤ m) {g : ℕ} (hg : g ∈ m.divisors) (Y : ℕ) :
    ∑ t ∈ Finset.Icc 1 (Y / m),
        (∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d (m / g)), (chiRe χ d : ℂ))
          * (((m * t : ℕ) : ℂ) ^ (-ρ) * ((1 - ((m * t : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ))
      = ∑ k ∈ (m / g).divisors,
          (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
            * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)) := by
  have hg1 : 1 ≤ g := Nat.pos_of_mem_divisors hg
  have hgm : g ∣ m := Nat.dvd_of_mem_divisors hg
  have hκ1 : 1 ≤ m / g := (Nat.one_le_div_iff hg1).mpr (Nat.le_of_dvd (by omega) hgm)
  rw [inner_cop_swap_wt_C χ
        (fun t => ((m * t : ℕ) : ℂ) ^ (-ρ) * ((1 - ((m * t : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ))
        (m / g) (Y / m),
      sum_coprime_eq_moebius_multiples_C (m / g) (Y / m) hκ1
        (fun d => (chiRe χ d : ℂ) * ∑ s ∈ Finset.Icc 1 (Y / m / d),
          ((m * (d * s) : ℕ) : ℂ) ^ (-ρ) * ((1 - ((m * (d * s) : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ))]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk1 : 1 ≤ k := Nat.pos_of_mem_divisors hk
  have hfold : (∑ e ∈ Finset.Icc 1 (Y / m / k),
        (chiRe χ (k * e) : ℂ) * ∑ s ∈ Finset.Icc 1 (Y / m / (k * e)),
          ((m * (k * e * s) : ℕ) : ℂ) ^ (-ρ)
            * ((1 - ((m * (k * e * s) : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ))
      = (chiRe χ k : ℂ) * ∑ N ∈ Finset.Icc 1 (Y / m / k), (dhA χ N : ℂ)
          * (((m * (k * N) : ℕ) : ℂ) ^ (-ρ)
            * ((1 - ((m * (k * N) : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)) := by
    rw [weighted_char_count_C χ (fun N => ((m * (k * N) : ℕ) : ℂ) ^ (-ρ)
          * ((1 - ((m * (k * N) : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)) (Y / m / k), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    have hchi : (chiRe χ (k * e) : ℂ) = (chiRe χ k : ℂ) * (chiRe χ e : ℂ) := by
      rw [chiRe_mul χ hsq k e]; push_cast; ring
    have hidx : Y / m / (k * e) = Y / m / k / e := (Nat.div_div_eq_div_mul (Y / m) k e).symm
    rw [hchi, hidx, mul_assoc]
    congr 1
    congr 1
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [mul_assoc k e s]
  have hval : (∑ N ∈ Finset.Icc 1 (Y / m / k), (dhA χ N : ℂ)
        * (((m * (k * N) : ℕ) : ℂ) ^ (-ρ) * ((1 - ((m * (k * N) : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)))
      = ((m * k : ℕ) : ℂ) ^ (-ρ) * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)) := by
    have hfloor : ⌊(Y : ℝ) / ((m * k : ℕ) : ℝ)⌋₊ = Y / (m * k) := Nat.floor_div_eq_div Y (m * k)
    have hLeq : Y / m / k = Y / (m * k) := Nat.div_div_eq_div_mul Y m k
    rw [dhD0rho, hfloor, hLeq, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun N _ => ?_)
    have hcpow : ((m * (k * N) : ℕ) : ℂ) ^ (-ρ)
        = ((m * k : ℕ) : ℂ) ^ (-ρ) * (N : ℂ) ^ (-ρ) := by
      rw [show ((m * (k * N) : ℕ) : ℂ) = (((m * k : ℕ) : ℝ) : ℂ) * ((N : ℝ) : ℂ) by
          push_cast; ring, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
      push_cast; ring
    have hkerR : (1 - ((m * (k * N) : ℕ) : ℝ) / (Y : ℝ))
        = (1 - (N : ℝ) / ((Y : ℝ) / ((m * k : ℕ) : ℝ))) := by
      rw [show ((m * (k * N) : ℕ) : ℝ) = ((m * k : ℕ) : ℝ) * (N : ℝ) by push_cast; ring,
        div_div_eq_mul_div]; ring
    rw [hcpow, show ((1 - ((m * (k * N) : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)
          = ((1 - (N : ℝ) / ((Y : ℝ) / ((m * k : ℕ) : ℝ)) : ℝ) : ℂ) from by rw [hkerR]]
    ring
  rw [hfold, hval]; ring

/-- **R6-4@ρ (`dhA_kernel_reduction_rho`) — THE EXACT REDUCTION at `n^{−ρ}·kernel`.** ℂ re-run of
`dhA_kernel_reduction`: the per-`m` kernel-restricted complex detector sum reduces EXACTLY to the
`m = 1` template `dhD0rho` at rescaled real scales `Y/(m·k)`. The `(†)` split `dhA_mul_eq_sum` is
coefficient-generic (cast to `ℂ`). -/
private lemma dhA_kernel_reduction_rho (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (ρ : ℂ) {m : ℕ} (hm : 1 ≤ m) (Y : ℕ) :
    ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n),
        (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ) * ((1 - (n : ℝ) / (Y : ℝ) : ℝ) : ℂ)
      = ∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
          (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
            * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)) := by
  rw [sum_dvd_reindex_C hm
      (fun n => (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ) * ((1 - (n : ℝ) / (Y : ℝ) : ℝ) : ℂ))]
  have hstep : ∀ t ∈ Finset.Icc 1 (Y / m),
      (dhA χ (m * t) : ℂ) * ((m * t : ℕ) : ℂ) ^ (-ρ)
          * ((1 - ((m * t : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)
        = ∑ g ∈ m.divisors, (chiRe χ g : ℂ)
            * ((∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d (m / g)), (chiRe χ d : ℂ))
                * (((m * t : ℕ) : ℂ) ^ (-ρ)
                  * ((1 - ((m * t : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ))) := by
    intro t _
    have hcast : (dhA χ (m * t) : ℂ) = ∑ g ∈ m.divisors, (chiRe χ g : ℂ)
        * ∑ d ∈ t.divisors.filter (fun d => Nat.Coprime d (m / g)), (chiRe χ d : ℂ) := by
      rw [dhA_mul_eq_sum χ hsq hm t]; push_cast; rfl
    rw [show (dhA χ (m * t) : ℂ) * ((m * t : ℕ) : ℂ) ^ (-ρ)
            * ((1 - ((m * t : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)
          = (dhA χ (m * t) : ℂ) * (((m * t : ℕ) : ℂ) ^ (-ρ)
              * ((1 - ((m * t : ℕ) : ℝ) / (Y : ℝ) : ℝ) : ℂ)) by ring, hcast, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun g _ => by ring)
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [← Finset.mul_sum, dhA_kernel_reduction_inner_rho χ hsq ρ hm hg Y]

/-! ## §3 — the ℂ regroup + the per-`m` residual (collection R6-5/6/7@ρ, reused) -/

/-- ℂ re-run of `dhExtractionW_regroup` (the `gcW` swap, generic in the ℂ factor `f`). -/
private lemma dhExtractionW_regroup_C (χ : DirichletCharacter ℂ q) (lam : ℕ → ℝ) (f : ℕ → ℂ)
    (Y : ℕ) :
    ∑ n ∈ Finset.Icc 1 Y, (dhCoeffW χ lam n : ℂ) * f n
      = ∑ m ∈ Finset.Icc 1 Y, (gcW lam m : ℂ)
          * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n), (dhA χ n : ℂ) * f n := by
  have hstep : ∀ n ∈ Finset.Icc 1 Y, (dhCoeffW χ lam n : ℂ) * f n
      = ∑ m ∈ n.divisors, (gcW lam m : ℂ) * ((dhA χ n : ℂ) * f n) := by
    intro n _
    have hc : (dhCoeffW χ lam n : ℂ)
        = (dhA χ n : ℂ) * ∑ m ∈ n.divisors, (gcW lam m : ℂ) := by
      rw [dhCoeffW, dhWeightSqW_eq_sum_gcW]; push_cast; ring
    rw [hc, show (dhA χ n : ℂ) * (∑ m ∈ n.divisors, (gcW lam m : ℂ)) * f n
        = (∑ m ∈ n.divisors, (gcW lam m : ℂ)) * ((dhA χ n : ℂ) * f n) by ring, Finset.sum_mul]
  have hcomm : ∀ (n m : ℕ), (n ∈ Finset.Icc 1 Y ∧ m ∈ n.divisors)
      ↔ (n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n) ∧ m ∈ Finset.Icc 1 Y) := by
    intro n m
    simp only [Finset.mem_Icc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn1, hnY⟩, hmn, _⟩
      have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos hmn (by omega)
      have hmn' : m ≤ n := Nat.le_of_dvd (by omega) hmn
      exact ⟨⟨⟨hn1, hnY⟩, hmn⟩, hm1, le_trans hmn' hnY⟩
    · rintro ⟨⟨⟨hn1, hnY⟩, hmn⟩, _, _⟩
      exact ⟨⟨hn1, hnY⟩, hmn, by omega⟩
  calc ∑ n ∈ Finset.Icc 1 Y, (dhCoeffW χ lam n : ℂ) * f n
      = ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ n.divisors, (gcW lam m : ℂ) * ((dhA χ n : ℂ) * f n) :=
        Finset.sum_congr rfl hstep
    _ = ∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n),
          (gcW lam m : ℂ) * ((dhA χ n : ℂ) * f n) := Finset.sum_comm' hcomm
    _ = ∑ m ∈ Finset.Icc 1 Y, (gcW lam m : ℂ)
          * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n), (dhA χ n : ℂ) * f n := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]

set_option maxHeartbeats 1200000 in
-- The per-m residual assembles a double-sum norm-triangle over the exact complex main collection
-- (the `clean_cpow_term`/`selHmul_collection` cast + field_simp over `(1−ρ)(2−ρ)`) exceeds default.
/-- **R6-8@ρ per-`m` residual (collection R6-5/6/7@ρ reused).** ℂ/norm analog of
`dh_extraction_per_m`: for squarefree `m ≤ z²`, the per-`m` complex reduction differs from the
EXACT complex main `L(1,χ)·Y^{1−ρ}/((1−ρ)(2−ρ))·selNu(m)` by at most `C₂ρ·Y^{1/2−σ}·Σ_{g,k}
(m·k)^{−1/2}`. The signed main collects EXACTLY (`clean_cpow_term` + `selHmul_collection` cast,
`selNu`); the residual is a norm-triangle over `(g,k)` with `unmoll_extraction_rho` (`x ≥ 2`
guard), `‖(m·k)^{−ρ}‖ = (m·k)^{−σ}`, and `dhD0_scale_err` at `β₀ = ρ.re`. -/
private lemma dh_extraction_per_m_rho [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re < 1)
    (him : |ρ.im| ≤ 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {z Y m : ℕ} (hz : 1 ≤ z) (hY : 2 * z ^ 4 ≤ Y) (hm1 : 1 ≤ m) (hmsf : Squarefree m)
    (hmz2 : m ≤ z ^ 2) :
    ‖(∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
          (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
            * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
       - DirichletCharacter.LFunction χ 1 * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))
           * (selNu χ m : ℂ)‖
      ≤ C2Rho q Z₀ ρ * (Y : ℝ) ^ (1 / 2 - ρ.re)
        * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  set L₁ : ℂ := DirichletCharacter.LFunction χ 1 with hL1def
  set C₂ρ : ℝ := C2Rho q Z₀ ρ with hC2def
  have hu : 0 < 1 - ρ.re := by linarith
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hhi; simp at hhi
  have hsne : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (fun h => hρ1 h.symm)
  have h2ρne : (2 - ρ) ≠ 0 := by
    intro h; have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, Complex.re_ofNat] at this; linarith
  have hm0 : m ≠ 0 := by omega
  have hz4 : 1 ≤ z ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hYm : 1 ≤ Y := by omega
  have hmC0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  have hmu_le : ∀ k : ℕ, ‖(moebius k : ℂ)‖ ≤ 1 := by
    intro k; rw [show (moebius k : ℂ) = ((moebius k : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
  have hguard : ∀ g ∈ m.divisors, ∀ k ∈ (m / g).divisors,
      (1 : ℕ) ≤ m * k ∧ (2 : ℝ) ≤ (Y : ℝ) / ((m * k : ℕ) : ℝ) := by
    intro g hg k hk
    have hg1 : 1 ≤ g := Nat.pos_of_mem_divisors hg
    have hgm : g ∣ m := Nat.dvd_of_mem_divisors hg
    have hk1 : 1 ≤ k := Nat.pos_of_mem_divisors hk
    have hmgpos : 0 < m / g := Nat.div_pos (Nat.le_of_dvd (by omega) hgm) hg1
    have hkm : k ≤ m :=
      le_trans (Nat.le_of_dvd hmgpos (Nat.dvd_of_mem_divisors hk)) (Nat.div_le_self m g)
    have hmk1 : 1 ≤ m * k := Nat.mul_pos hm1 hk1
    have hmkz4 : m * k ≤ z ^ 4 := by
      calc m * k ≤ m * m := Nat.mul_le_mul (le_refl m) hkm
        _ ≤ z ^ 2 * z ^ 2 := Nat.mul_le_mul hmz2 hmz2
        _ = z ^ 4 := by ring
    have h2mk : 2 * (m * k) ≤ Y := le_trans (by omega) hY
    have hmkR : (0 : ℝ) < ((m * k : ℕ) : ℝ) := by exact_mod_cast hmk1
    refine ⟨hmk1, ?_⟩
    rw [le_div_iff₀ hmkR]
    calc (2 : ℝ) * ((m * k : ℕ) : ℝ) = ((2 * (m * k) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Y : ℝ) := by exact_mod_cast h2mk
  -- STEP 1 : the exact main collection
  have hterm : ∀ g ∈ m.divisors, ∀ k ∈ (m / g).divisors,
      (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
          * (L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)))
        = (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (1 / (m : ℂ)))
            * ((moebius k : ℂ) * (chiRe χ k : ℂ) / (k : ℂ)) := by
    intro g hg k hk
    obtain ⟨hmk1, -⟩ := hguard g hg k hk
    have hk0 : (k : ℂ) ≠ 0 := by
      have : k ≠ 0 := by have := Nat.pos_of_mem_divisors hk; omega
      exact_mod_cast this
    have hscale : ((m * k : ℕ) : ℂ) ^ (-ρ)
        * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ)
        = (Y : ℂ) ^ (1 - ρ) / ((m * k : ℕ) : ℂ) := by
      rw [show (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) = (Y : ℂ) / ((m * k : ℕ) : ℂ) by
          push_cast; ring]
      exact clean_cpow_term (d := m * k) (t := Y) hmk1 ρ
    rw [show (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
            * (L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)))
          = (moebius k : ℂ) * (chiRe χ k : ℂ) * L₁ / ((1 - ρ) * (2 - ρ))
            * (((m * k : ℕ) : ℂ) ^ (-ρ)
              * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ)) by ring,
        hscale, show ((m * k : ℕ) : ℂ) = (m : ℂ) * (k : ℂ) by push_cast; ring]
    field_simp
  have hcollC : ∑ g ∈ m.divisors, (chiRe χ g : ℂ)
        * ∑ k ∈ (m / g).divisors, (moebius k : ℂ) * (chiRe χ k : ℂ) / (k : ℂ)
      = (selHmul χ m : ℂ) := by
    rw [← selHmul_collection χ hsq hmsf]; push_cast; rfl
  have hmainval : (∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
        (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
          * (L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))))
      = L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ) := by
    calc (∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
            (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
              * (L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))))
        = ∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
            (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (1 / (m : ℂ)))
              * ((moebius k : ℂ) * (chiRe χ k : ℂ) / (k : ℂ)) := by
          refine Finset.sum_congr rfl (fun g hg => ?_)
          congr 1
          exact Finset.sum_congr rfl (fun k hk => hterm g hg k hk)
      _ = (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (1 / (m : ℂ)))
            * ∑ g ∈ m.divisors, (chiRe χ g : ℂ)
                * ∑ k ∈ (m / g).divisors, (moebius k : ℂ) * (chiRe χ k : ℂ) / (k : ℂ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun g _ => ?_)
          rw [← Finset.mul_sum]; ring
      _ = (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (1 / (m : ℂ))) * (selHmul χ m : ℂ) := by
          rw [hcollC]
      _ = L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ) := by
          rw [selNu, show (selHmul χ m / (m : ℝ) : ℝ) = selHmul χ m / (m : ℝ) from rfl]
          push_cast; field_simp
  rw [← hmainval, ← Finset.sum_sub_distrib]
  -- STEP 2 : the signed residual and its norm triangle
  have hcombine : ∀ g ∈ m.divisors,
      (chiRe χ g : ℂ) * (∑ k ∈ (m / g).divisors, (moebius k : ℂ) * (chiRe χ k : ℂ)
          * ((m * k : ℕ) : ℂ) ^ (-ρ) * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
        - (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
            (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
            * (L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)))
      = ∑ k ∈ (m / g).divisors, (chiRe χ g : ℂ) * ((moebius k : ℂ) * (chiRe χ k : ℂ)
          * ((m * k : ℕ) : ℂ) ^ (-ρ)
          * (dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ))
            - L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)))) := by
    intro g _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [Finset.sum_congr rfl hcombine]
  calc ‖∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors,
          (chiRe χ g : ℂ) * ((moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
            * (dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ))
              - L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))))‖
      ≤ ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors,
          C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re) * ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun g hg => ?_))
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => ?_))
        obtain ⟨hmk1, hx2⟩ := hguard g hg k hk
        have hmkR0 : (0 : ℝ) < ((m * k : ℕ) : ℝ) := by exact_mod_cast hmk1
        have hR3 := unmoll_extraction_rho χ hχ hsq hq hzero hlo hhi him hZ
          (x := (Y : ℝ) / ((m * k : ℕ) : ℝ)) hx2
        rw [← hL1def, ← hC2def] at hR3
        have hcpownorm : ‖((m * k : ℕ) : ℂ) ^ (-ρ)‖ = ((m * k : ℕ) : ℝ) ^ (-ρ.re) := by
          rw [show ((m * k : ℕ) : ℂ) = (((m * k : ℕ) : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_cpow_eq_rpow_re_of_pos hmkR0]
          rw [Complex.neg_re]
        have herr := dhD0_scale_err (β₀ := ρ.re) (a := m * k) (Y := Y) hmk1 hYm
        calc ‖(chiRe χ g : ℂ) * ((moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
                * (dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ))
                  - L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))))‖
            = ‖(chiRe χ g : ℂ)‖ * (‖(moebius k : ℂ)‖ * ‖(chiRe χ k : ℂ)‖
                * ((m * k : ℕ) : ℝ) ^ (-ρ.re)
                * ‖dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ))
                  - L₁ * (((Y : ℝ) / ((m * k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - ρ)
                      / ((1 - ρ) * (2 - ρ))‖) := by
              rw [norm_mul, norm_mul, norm_mul, norm_mul, hcpownorm]
          _ ≤ 1 * (1 * 1 * ((m * k : ℕ) : ℝ) ^ (-ρ.re)
                * (C₂ρ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 / 2 - ρ.re))) := by
              gcongr
              · rw [Complex.norm_real, Real.norm_eq_abs]; exact chiRe_abs_le_one χ g
              · exact hmu_le k
              · rw [Complex.norm_real, Real.norm_eq_abs]; exact chiRe_abs_le_one χ k
          _ = C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re) * ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
              rw [show (1 : ℝ) * (1 * 1 * ((m * k : ℕ) : ℝ) ^ (-ρ.re)
                    * (C₂ρ * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 / 2 - ρ.re)))
                  = C₂ρ * (((m * k : ℕ) : ℝ) ^ (-ρ.re)
                    * ((Y : ℝ) / ((m * k : ℕ) : ℝ)) ^ (1 / 2 - ρ.re)) by ring, herr]
              ring
    _ = C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re)
          * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [Finset.mul_sum]

/-! ## §4 — E(ρ) assembly : `dh_extraction_upper_rho` -/

set_option maxHeartbeats 1200000 in
-- The capstone: ℂ regroup + exact reduction (R6-4@ρ) + signed complex main collection + the
-- per-m residual moment; the double-sum norm-triangle exceeds the default heartbeat budget.
/-- **E(ρ) assembly (`dh_extraction_upper_rho`) — the complex-scale weighted extraction.** The ℂ
analog of `dh_extraction_upper_W`: the Selberg-mollified `ρ`-detector's partial sum is
`L(1,χ)·selMainTerm` main (the FULL complex `L`-value, `/((1−ρ)(2−ρ))`) plus a `Y^{1/2−σ}`
error, `C₂ρ = C2Rho q Z₀ ρ`, under the guard `2z⁴ ≤ Y`. STEP 1 ℂ regroup
(`dhExtractionW_regroup_C`) + kernel (`dhKernR_eq`) + the EXACT reduction
(`dhA_kernel_reduction_rho`); STEP 2 the signed complex main collected EXACTLY
(`sum_gcW_selNu_eq_selMainTerm` cast); STEP 3 signed
subtraction; STEP 4 norm-triangle on the residual only (`dh_extraction_per_m_rho` +
`sum_gcW_pairkernel_le`, `gcW = 0` off squarefree/`> z²`). -/
theorem dh_extraction_upper_rho [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re < 1)
    (him : |ρ.im| ≤ 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {z Y : ℕ} (hz : 1 ≤ z) (hY : 2 * z ^ 4 ≤ Y) :
    ‖∑ n ∈ Finset.Icc 1 Y,
        (dhCoeffW χ (selWeight χ z) n : ℂ) * (n : ℂ) ^ (-ρ)
          * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ)
       - DirichletCharacter.LFunction χ 1 * (selMainTerm χ z : ℂ)
           * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))‖
      ≤ C2Rho q Z₀ ρ * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - ρ.re) := by
  set L₁ : ℂ := DirichletCharacter.LFunction χ 1 with hL1def
  set C₂ρ : ℝ := C2Rho q Z₀ ρ with hC2def
  have hσ0 : 0 < ρ.re := by linarith
  have hu : 0 < 1 - ρ.re := by linarith
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hhi; simp at hhi
  have hsne : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (fun h => hρ1 h.symm)
  have hnpos : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hsne
  have h2ρne : (2 - ρ) ≠ 0 := by
    intro h; have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, Complex.re_ofNat] at this; linarith
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hMnn : 0 ≤ Real.sqrt q * (1 + Real.log q) := by positivity
  have hZ0nn : 0 ≤ Z₀ := le_trans (norm_nonneg _)
    (hZ ρ hlo hhi.le him)
  have hC2nn : 0 ≤ C₂ρ := by
    rw [hC2def, C2Rho, CwRho]
    have h1 : (0:ℝ) ≤ ‖ρ‖ / ρ.re := div_nonneg (norm_nonneg _) hσ0.le
    positivity
  have hY1 : 1 ≤ Y := by have := Nat.one_le_pow 4 z (by omega); omega
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY1
  have hz2Y : z ^ 2 ≤ Y := by
    have h1 : z ^ 2 ≤ z ^ 4 := Nat.pow_le_pow_right hz (by norm_num)
    omega
  have hsfsupp : ∀ d, selWeight χ z d ≠ 0 → Squarefree d :=
    fun d h => selWeight_ne_zero_squarefree χ z h
  -- STEP 1 : ℂ regroup + exact reduction (R6-4@ρ)
  rw [Finset.sum_congr rfl (fun n _ => mul_assoc _ _ _),
      dhExtractionW_regroup_C χ (selWeight χ z)
        (fun n => (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ)) Y]
  have hred : ∀ m ∈ Finset.Icc 1 Y,
      (gcW (selWeight χ z) m : ℂ) * (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n),
          (dhA χ n : ℂ) * ((n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ)))
        = (gcW (selWeight χ z) m : ℂ) * (∑ g ∈ m.divisors, (chiRe χ g : ℂ)
            * ∑ k ∈ (m / g).divisors, (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
              * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ))) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    congr 1
    rw [← dhA_kernel_reduction_rho χ hsq ρ (by omega : 1 ≤ m) Y]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [dhKernR_eq (by rw [div_le_one hYpos]; exact_mod_cast hn.1.2), ← mul_assoc]
  rw [Finset.sum_congr rfl hred]
  -- STEP 2 : the signed complex main collected EXACTLY
  have hgcwselnuC : ∑ m ∈ Finset.Icc 1 Y, (gcW (selWeight χ z) m : ℂ) * (selNu χ m : ℂ)
      = (selMainTerm χ z : ℂ) := by
    rw [← sum_gcW_selNu_eq_selMainTerm χ hsq hz hz2Y]; push_cast; rfl
  have htarget : (∑ m ∈ Finset.Icc 1 Y, (gcW (selWeight χ z) m : ℂ)
        * (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ)))
      = L₁ * (selMainTerm χ z : ℂ) * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) := by
    rw [show (∑ m ∈ Finset.Icc 1 Y, (gcW (selWeight χ z) m : ℂ)
            * (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ)))
          = L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))
              * ∑ m ∈ Finset.Icc 1 Y, (gcW (selWeight χ z) m : ℂ) * (selNu χ m : ℂ) from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring),
      hgcwselnuC]
    ring
  rw [← htarget, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun m _ => by ring :
      ∀ m ∈ Finset.Icc 1 Y,
        (gcW (selWeight χ z) m : ℂ) * (∑ g ∈ m.divisors, (chiRe χ g : ℂ)
              * ∑ k ∈ (m / g).divisors, (moebius k : ℂ) * (chiRe χ k : ℂ)
                  * ((m * k : ℕ) : ℂ) ^ (-ρ) * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
          - (gcW (selWeight χ z) m : ℂ)
              * (L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ))
        = (gcW (selWeight χ z) m : ℂ)
            * ((∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
                (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
                  * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
              - L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ)))]
  -- STEP 3 : norm-triangle on the residual
  refine (norm_sum_le _ _).trans ?_
  have hpm : ∀ m ∈ Finset.Icc 1 Y,
      ‖(gcW (selWeight χ z) m : ℂ)
          * ((∑ g ∈ m.divisors, (chiRe χ g : ℂ) * ∑ k ∈ (m / g).divisors,
              (moebius k : ℂ) * (chiRe χ k : ℂ) * ((m * k : ℕ) : ℂ) ^ (-ρ)
                * dhD0rho χ ρ ((Y : ℝ) / ((m * k : ℕ) : ℝ)))
            - L₁ * (Y : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) * (selNu χ m : ℂ))‖
        ≤ |gcW (selWeight χ z) m| * (C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re)
            * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
    intro m hm
    rw [norm_mul, show ‖(gcW (selWeight χ z) m : ℂ)‖ = |gcW (selWeight χ z) m| from by
      rw [Complex.norm_real, Real.norm_eq_abs]]
    rcases eq_or_ne (gcW (selWeight χ z) m) 0 with hg0 | hg0
    · rw [hg0, abs_zero, zero_mul, zero_mul]
    · have hmsf : Squarefree m := by
        by_contra h; exact hg0 (gcW_eq_zero_of_not_squarefree hsfsupp h)
      have hmz2 : m ≤ z ^ 2 := by
        by_contra h; exact hg0 (gcW_selWeight_eq_zero_of_gt_sq χ (by omega))
      have hm1 : 1 ≤ m := by rw [Finset.mem_Icc] at hm; omega
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have := dh_extraction_per_m_rho χ hχ hsq hq hzero hlo hhi him hZ hz hY hm1 hmsf hmz2
      rw [← hL1def, ← hC2def] at this
      exact this
  refine (Finset.sum_le_sum hpm).trans ?_
  have hYrp : (0 : ℝ) ≤ (Y : ℝ) ^ (1 / 2 - ρ.re) := Real.rpow_nonneg hYpos.le _
  calc ∑ m ∈ Finset.Icc 1 Y, |gcW (selWeight χ z) m| * (C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re)
          * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))
      = C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re) * ∑ m ∈ Finset.Icc 1 Y, |gcW (selWeight χ z) m|
          * ∑ g ∈ m.divisors, ∑ k ∈ (m / g).divisors, ((m * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)
    _ ≤ C₂ρ * (Y : ℝ) ^ (1 / 2 - ρ.re) * ((z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9) :=
        mul_le_mul_of_nonneg_left (sum_gcW_pairkernel_le χ hsq hz hz2Y)
          (mul_nonneg hC2nn hYrp)
    _ = C₂ρ * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - ρ.re) := by ring

end Salt.SW

end
