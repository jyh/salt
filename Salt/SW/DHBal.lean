/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHMollified
import Salt.SW.DHFinal
import Salt.SW.DHTrunc
import Salt.SW.DHBalance
import Salt.SW.ZeroFreeReal
import Salt.SW.Siegel
import Salt.SW.Hyperbola
import Salt.HardyLittlewood.Sharp

/-!
# The DH balance capstone (`T-BAL`) — the mollified main-term balance

This module assembles WP2's analytic-core balance, closing the shifted-detector
repulsion `dh_repulsion` (contract at `DHRepulsion.lean:262`). The design is the
JYH-ratified "T-BAL FREEZE" (`docs/exploration/s3-hb3-design.md`), the survivor
of a 3-angle adversarial panel with the refuters' repairs applied.

Frozen witnesses: `b := 40`, `k := 9`, `c := 2⁻²⁶`.
Parameters: `T := |ρ.im|+2`; `X := qT`; `L := log X + 2`; `z := ⌈X⌉`;
`x := X^40`; `N := ⌈x⌉`; `P := 3√q(1+log q)(1+‖ρ‖/ρ.re)`; `c₀ := 1/126848`.

## Rungs (Zeno stones)

* R1 `norm_bsum_kernel_zero_decay` [B] — the sharp inner Abel (DH-TRUNC-A
  instantiation): the character partial sums damped by the antitone kernel.
* R6 `zfr_harvest` [B] — the zero-free-region harvest wiring `zero_free_region_all`
  to the contract hypotheses.

Later rungs (R2–R5, R7, R8) are the multi-session analytic bulk; the wall is
recorded in `docs/blueprints/flags.md` (node `T-BAL`).

## Honesty (HB-ENGINE, R4)

NO twin claim. `dh_repulsion` is one input to WP2, itself gated behind R4
(beyond-level-½ / Kloosterman — the documented death rung).
-/

open Complex

noncomputable section

namespace Salt.SW

open Finset

/-! ## R6 — the zero-free-region harvest (`zfr_harvest`) -/

/-- **R6 — the ZFR harvest.** For a real primitive character `χ ≠ 1` mod `q` and a
non-real zero `ρ` of `L(·,χ)` with `9/10 ≤ Re ρ < 1`, the landed
`zero_free_region_all` (`c₀ = 1/126848`) harvests the balance's three geometric
facts at one constant `c₀`:
* the width lower bound `c₀/log(q(|Im ρ|+2)) ≤ 1 − Re ρ` (the `x^{1−ρ.re}` damping's
  ZFR floor — poison for `‖1−ρ‖`);
* the pole-distance bound `1/‖1−ρ‖ ≤ log(q(|Im ρ|+2))/c₀` (polylog, absorbed in `k`);
* the shifted-pole bound `1 ≤ ‖2−ρ‖`.
No new ZFR work — pure wiring of the landed region to the contract shape (K1). -/
theorem zfr_harvest {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (him : ρ.im ≠ 0)
    (hlo : 9 / 10 ≤ ρ.re) (hhi : ρ.re < 1) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ 1 - ρ.re ∧
      1 / ‖1 - ρ‖ ≤ Real.log ((q : ℝ) * (|ρ.im| + 2)) / c₀ ∧
      1 ≤ ‖2 - ρ‖ := by
  obtain ⟨c₀, hc₀, hregion⟩ := zero_free_region_all
  refine ⟨c₀, hc₀, ?_, ?_, ?_⟩
  · -- the width floor from the region, at the disjunct `ρ.im ≠ 0`
    have hre : (1 : ℝ) / 2 ≤ ρ.re := by linarith
    have hb := hregion q χ hχ hne hzero hre (Or.inr him)
    linarith
  · -- pole distance: `‖1 − ρ‖ ≥ 1 − ρ.re ≥ c₀/log X > 0`
    have hre : (1 : ℝ) / 2 ≤ ρ.re := by linarith
    have hb := hregion q χ hχ hne hzero hre (Or.inr him)
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hLpos : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
      apply Real.log_pos; nlinarith [abs_nonneg ρ.im, hq1]
    have hwidth : 0 < 1 - ρ.re := by
      have : 0 < c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := div_pos hc₀ hLpos
      linarith
    have hdist : 1 - ρ.re ≤ ‖1 - ρ‖ := by
      have h := Complex.abs_re_le_norm (1 - ρ)
      simp only [Complex.sub_re, Complex.one_re] at h
      calc 1 - ρ.re ≤ |1 - ρ.re| := le_abs_self _
        _ ≤ ‖1 - ρ‖ := h
    have hnpos : 0 < ‖1 - ρ‖ := lt_of_lt_of_le hwidth hdist
    -- `c₀/log X ≤ 1 - ρ.re ≤ ‖1-ρ‖` gives `1/‖1-ρ‖ ≤ log X / c₀`
    rw [div_le_div_iff₀ hnpos hc₀]
    have hcross : c₀ ≤ ‖1 - ρ‖ * Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
      have hb' : c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ 1 - ρ.re := by linarith [hb]
      have hle : c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ ‖1 - ρ‖ := le_trans hb' hdist
      rw [div_le_iff₀ hLpos] at hle
      linarith
    linarith [hcross]
  · -- `‖2 − ρ‖ ≥ Re(2−ρ) = 2 − ρ.re ≥ 1`
    have h := Complex.abs_re_le_norm (2 - ρ)
    simp only [Complex.sub_re] at h
    have h2re : ((2 : ℂ).re) = 2 := by norm_num
    rw [h2re] at h
    calc (1 : ℝ) ≤ 2 - ρ.re := by linarith
      _ ≤ |2 - ρ.re| := le_abs_self _
      _ ≤ ‖2 - ρ‖ := h

/-! ## R1 — the sharp inner Abel (`norm_bsum_kernel_zero_decay`, DH-TRUNC-A) -/

/-- **R1 — DH-TRUNC-A (the sharp inner Abel).** Instantiates the ranged summation-by-parts
primitive `norm_sum_smul_antitone_ranged_le` with the DECAYING partial-sum bound
`Q(n) = P·(n−1)^{−ρ.re}` (from `partial_sum_at_zero_small`, `P := 3√q(1+log q)(1+‖ρ‖/ρ.re)`)
and the antitone linear-kernel weights `w_b = (1 − a·b/x)₊`. For a real character's zero `ρ`
(`0 < Re ρ ≤ 1`) and any outer index `a ≥ 1`, `x > 0`, the kernel-damped character partial sum
decays: the two explicit terms carry the `(N/a)^{−ρ.re}` inner grade the extraction consumes. -/
theorem norm_bsum_kernel_zero_decay {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re ≤ 1)
    {a : ℕ} (_ha : 1 ≤ a) {x : ℝ} (hx : 0 < x) (B : ℕ) :
    ‖∑ b ∈ Finset.Icc 1 B,
        χ (b : ZMod q) * (b : ℂ) ^ (-ρ) * ((dhKernR (((a * b : ℕ) : ℝ) / x)) : ℂ)‖
      ≤ dhKernR (((a * B : ℕ) : ℝ) / x)
          * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) * (B : ℝ) ^ (-ρ.re))
        + ∑ i ∈ Finset.range B,
            (dhKernR (((a * i : ℕ) : ℝ) / x) - dhKernR (((a * (i + 1) : ℕ) : ℝ) / x))
              * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) * (i : ℝ) ^ (-ρ.re)) := by
  set P := 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) with hP
  set c : ℕ → ℂ := fun i => χ (i : ZMod q) * (i : ℂ) ^ (-ρ) with hc
  set w : ℕ → ℝ := fun i => dhKernR (((a * i : ℕ) : ℝ) / x) with hw
  set Q : ℕ → ℝ := fun n => P * (((n - 1 : ℕ)) : ℝ) ^ (-ρ.re) with hQ
  have hlogq : (0 : ℝ) ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hPnn : 0 ≤ P := by
    rw [hP]
    have h1 : (0 : ℝ) ≤ 1 + Real.log q := by linarith
    have h2 : (0 : ℝ) ≤ 1 + ‖ρ‖ / ρ.re := by positivity
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) h1)) h2
  have hρne : ρ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hc0 : c 0 = 0 := by
    rw [hc]; simp only [Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hρne), mul_zero]
  -- generic drop-of-index-0 reindex `range n ↔ Icc 1 (n−1)` when the 0-term vanishes.
  have hdrop : ∀ (g : ℕ → ℂ), g 0 = 0 →
      ∀ n, ∑ i ∈ Finset.range n, g i = ∑ i ∈ Finset.Icc 1 (n - 1), g i := by
    intro g hg0 n
    cases n with
    | zero => simp
    | succ m =>
      rw [Finset.sum_range_succ', hg0, add_zero, Nat.succ_sub_one,
          show Finset.Icc 1 m = Finset.Ico 1 (m + 1) from by
            ext k; simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff],
          Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm i 1])
  -- the ranged partial-sum bound (the decaying `Q`).
  have hpartial : ∀ n, ‖∑ i ∈ Finset.range n, c i‖ ≤ Q n := by
    intro n
    rw [hdrop c hc0 n]
    rcases Nat.eq_zero_or_pos (n - 1) with h0 | hpos
    · rw [h0, show Finset.Icc 1 (0 : ℕ) = ∅ from Finset.Icc_eq_empty (by omega),
        Finset.sum_empty, norm_zero, hQ]
      exact mul_nonneg hPnn (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · have hkey := partial_sum_at_zero_small χ hχ hq hzero hρ0 hρ1 hpos
      simp only [hc, hQ, hP]
      exact hkey
  -- the antitone nonneg kernel weights.
  have hanti : Antitone w := by
    intro i j hij
    simp only [hw, dhKernR]
    refine max_le_max (le_refl 0) ?_
    have hnat : ((a * i : ℕ) : ℝ) ≤ ((a * j : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul (le_refl a) hij
    have hle : ((a * i : ℕ) : ℝ) / x ≤ ((a * j : ℕ) : ℝ) / x :=
      (div_le_div_iff_of_pos_right hx).mpr hnat
    linarith
  have hw0 : ∀ i, 0 ≤ w i := fun i => dhKernR_nonneg _
  -- rewrite the goal's LHS as the `range (B+1)` smul-sum.
  have hwc0 : (fun i => w i • c i) 0 = 0 := by change w 0 • c 0 = 0; rw [hc0, smul_zero]
  have hLHS : ∑ b ∈ Finset.Icc 1 B,
        χ (b : ZMod q) * (b : ℂ) ^ (-ρ) * ((dhKernR (((a * b : ℕ) : ℝ) / x)) : ℂ)
      = ∑ i ∈ Finset.range (B + 1), w i • c i := by
    rw [hdrop (fun i => w i • c i) hwc0 (B + 1), Nat.add_sub_cancel]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [hw, hc, Complex.real_smul]
    ring
  rw [hLHS]
  refine le_trans (norm_sum_smul_antitone_ranged_le hpartial hanti hw0 (B + 1)) (le_of_eq ?_)
  rw [Nat.add_sub_cancel]
  simp only [hw, hQ, Nat.add_sub_cancel]

/-! ## R3 — the dhA mass upper bound (`dhA_mass_upper`, the u-carrier)

The symmetric √N Dirichlet hyperbola (`dhA_hyperbola_symm`) splits `Σ_{n≤y} dhA χ n`
into a `√y`-truncated `d`-leg (whose main term `y·Re(Σ_{d≤√y} χ(d)/d)` carries `L(1,χ)`
via the strip engine at `s = 1`), a transposed character-partial-sum leg, and the corner
block — the last two bounded by Pólya–Vinogradov. Net: `≤ (L(1,χ)).re·y + 20M√y`,
`M = √q(1+log q)`. This is design key **K2**: `S₀` is `L(1,χ)`-PROPORTIONAL, the
u-carrier. No `χ² = 1` needed — the bound is `norm`-level. -/

/-- **R3 — the dhA mass bound (the u-carrier).** For a primitive character `χ` mod `q ≥ 2`
and `y ≥ 1`, `Σ_{n≤y} dhA χ n ≤ (L(1,χ)).re·y + 20·√q·(1+log q)·√y`. The main leg's
`L(1,χ)`-proportional term is design key K2; the `√y` error is the symmetric-hyperbola
Pólya–Vinogradov control of the two short legs. -/
theorem dhA_mass_upper {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {y : ℕ} (hy : 1 ≤ y) :
    ∑ n ∈ Finset.Icc 1 y, dhA χ n
      ≤ (DirichletCharacter.LFunction χ 1).re * (y : ℝ)
        + 20 * (Real.sqrt q * (1 + Real.log q)) * Real.sqrt y := by
  set M : ℝ := Real.sqrt q * (1 + Real.log q) with hMdef
  have hne : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  haveI : Fact (1 < q) := ⟨by omega⟩
  have hchi0 : χ (0 : ZMod q) = 0 := MulChar.map_nonunit χ not_isUnit_zero
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hsqq1 : 1 ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : (1 : ℕ) ≤ q))
  have hMge1 : 1 ≤ M := by rw [hMdef]; nlinarith [hsqq1, hlogq, Real.sqrt_nonneg (q : ℝ)]
  have hMnn : 0 ≤ M := by linarith
  -- Pólya–Vinogradov on the character partial sums.
  have hPV : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod q)‖ ≤ M :=
    fun u => Salt.BV.polya_vinogradov χ hχ hq u
  -- `Σ_{Icc 1 t} χ = Σ_{range (t+1)} χ` (the `k = 0` term vanishes).
  have hIccrange : ∀ t : ℕ,
      ∑ d ∈ Finset.Icc 1 t, χ (d : ZMod q) = ∑ k ∈ Finset.range (t + 1), χ (k : ZMod q) := by
    intro t
    rw [Finset.sum_range_succ' (fun k => χ (k : ZMod q)) t, Nat.cast_zero, hchi0, add_zero,
        show Finset.Icc 1 t = Finset.Ico 1 (t + 1) from by ext x; simp,
        Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm 1 i])
  -- `|Σ_{Icc 1 t} chiRe| ≤ M` (Re of a character partial sum, bounded by PV).
  have hStM : ∀ t : ℕ, |∑ d ∈ Finset.Icc 1 t, chiRe χ d| ≤ M := by
    intro t
    have hre : ∑ d ∈ Finset.Icc 1 t, chiRe χ d = (∑ d ∈ Finset.Icc 1 t, χ (d : ZMod q)).re := by
      rw [Complex.re_sum]; simp only [chiRe]
    rw [hre]
    calc |(∑ d ∈ Finset.Icc 1 t, χ (d : ZMod q)).re|
        ≤ ‖∑ d ∈ Finset.Icc 1 t, χ (d : ZMod q)‖ := Complex.abs_re_le_norm _
      _ = ‖∑ k ∈ Finset.range (t + 1), χ (k : ZMod q)‖ := by rw [hIccrange t]
      _ ≤ M := hPV (t + 1)
  -- The symmetric hyperbola.
  rw [dhA_hyperbola_symm χ y]
  set r : ℕ := Nat.sqrt y with hrdef
  set L1 : ℂ := DirichletCharacter.LFunction χ 1 with hL1def
  -- √-facts.
  have hrge1 : 1 ≤ r := by
    rw [hrdef]
    calc 1 = Nat.sqrt 1 := Nat.sqrt_one.symm
      _ ≤ Nat.sqrt y := Nat.sqrt_le_sqrt hy
  have hrge1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrge1
  have hsqy_pos : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < y))
  have hr_le : (r : ℝ) ≤ Real.sqrt y := by
    rw [show (r : ℝ) = Real.sqrt ((r : ℝ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have hle : r ^ 2 ≤ y := by rw [hrdef]; exact Nat.sqrt_le' y
    exact_mod_cast hle
  have hy_lt : Real.sqrt y < (r : ℝ) + 1 := by
    have h2 := Nat.lt_succ_sqrt y
    have hcast : (y : ℝ) < ((r : ℝ) + 1) ^ 2 := by
      have hh : (y : ℝ) < ((Nat.sqrt y + 1 : ℕ) : ℝ) * ((Nat.sqrt y + 1 : ℕ) : ℝ) := by
        exact_mod_cast h2
      rw [hrdef]; push_cast at hh ⊢; nlinarith [hh]
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (y : ℝ)), Real.sqrt_nonneg (y : ℝ), hcast]
  have hy_div_r : (y : ℝ) / (r : ℝ) ≤ 2 * Real.sqrt y := by
    have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
    rw [div_le_iff₀ hrpos]
    have hyeq : (y : ℝ) = Real.sqrt y * Real.sqrt y := (Real.mul_self_sqrt (by positivity)).symm
    have hsy2r : Real.sqrt y < 2 * (r : ℝ) := by linarith [hy_lt, hrge1R]
    nlinarith [hyeq, mul_pos hsqy_pos (by linarith [hsy2r] : (0 : ℝ) < 2 * (r : ℝ) - Real.sqrt y)]
  -- The main leg: `Σ_{d≤r} chiRe(d)/d ≤ L1.re + 6M/r`.
  have hMainSum : (∑ d ∈ Finset.Icc 1 r, chiRe χ d / (d : ℝ)) ≤ L1.re + 6 * M / (r : ℝ) := by
    set Pr : ℂ := ∑ d ∈ Finset.Icc 1 r, χ (d : ZMod q) * (d : ℂ) ^ (-(1 : ℂ)) with hPrdef
    have hMainRe : (∑ d ∈ Finset.Icc 1 r, chiRe χ d / (d : ℝ)) = Pr.re := by
      rw [hPrdef, Complex.re_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      have hcpow : (d : ℂ) ^ (-(1 : ℂ)) = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by
        rw [Complex.cpow_neg, Complex.cpow_one, Complex.ofReal_inv, Complex.ofReal_natCast]
      rw [hcpow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      simp only [chiRe]
      rw [div_eq_mul_inv]
    rw [hMainRe]
    have hstrip := norm_LFunction_sub_partial_le_strip χ hne hq hPV (s := (1 : ℂ))
      (by rw [Complex.one_re]; norm_num) (le_of_eq Complex.one_re) hrge1
    have hval : 3 * M * (1 + ‖(1 : ℂ)‖ / (1 : ℂ).re) * (r : ℝ) ^ (-(1 : ℂ).re)
        = 6 * M / (r : ℝ) := by
      rw [Complex.one_re, norm_one, Real.rpow_neg (Nat.cast_nonneg r), Real.rpow_one,
          div_eq_mul_inv]
      ring
    have hstrip' : ‖L1 - Pr‖ ≤ 6 * M / (r : ℝ) := by
      rw [← hval]; exact hstrip
    have hdiff : Pr.re - L1.re ≤ 6 * M / (r : ℝ) := by
      calc Pr.re - L1.re = (Pr - L1).re := by rw [Complex.sub_re]
        _ ≤ |(Pr - L1).re| := le_abs_self _
        _ ≤ ‖Pr - L1‖ := Complex.abs_re_le_norm _
        _ = ‖L1 - Pr‖ := by rw [norm_sub_rev]
        _ ≤ 6 * M / (r : ℝ) := hstrip'
    linarith [hdiff]
  -- The `y·mainSum` bound.
  have hyMain : (y : ℝ) * (∑ d ∈ Finset.Icc 1 r, chiRe χ d / (d : ℝ))
      ≤ L1.re * (y : ℝ) + 12 * (M * Real.sqrt y) := by
    have hstep : (y : ℝ) * (∑ d ∈ Finset.Icc 1 r, chiRe χ d / (d : ℝ))
        ≤ (y : ℝ) * (L1.re + 6 * M / (r : ℝ)) :=
      mul_le_mul_of_nonneg_left hMainSum (by positivity)
    have hyr : (y : ℝ) * (6 * M / (r : ℝ)) ≤ 12 * (M * Real.sqrt y) := by
      rw [show (y : ℝ) * (6 * M / (r : ℝ)) = 6 * M * ((y : ℝ) / (r : ℝ)) from by ring]
      calc 6 * M * ((y : ℝ) / (r : ℝ)) ≤ 6 * M * (2 * Real.sqrt y) :=
            mul_le_mul_of_nonneg_left hy_div_r (by positivity)
        _ = 12 * (M * Real.sqrt y) := by ring
    calc (y : ℝ) * (∑ d ∈ Finset.Icc 1 r, chiRe χ d / (d : ℝ))
        ≤ (y : ℝ) * (L1.re + 6 * M / (r : ℝ)) := hstep
      _ = (y : ℝ) * L1.re + (y : ℝ) * (6 * M / (r : ℝ)) := by ring
      _ ≤ (y : ℝ) * L1.re + 12 * (M * Real.sqrt y) := by linarith [hyr]
      _ = L1.re * (y : ℝ) + 12 * (M * Real.sqrt y) := by ring
  -- The fractional block `|Σ chiRe(d)·frac_d| ≤ r`.
  have hterm : ∀ d ∈ Finset.Icc 1 r,
      |chiRe χ d * ((y : ℝ) / (d : ℝ) - ((y / d : ℕ) : ℝ))| ≤ 1 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hfrac_nn : 0 ≤ (y : ℝ) / (d : ℝ) - ((y / d : ℕ) : ℝ) := by
      have hle : ((y / d : ℕ) : ℝ) ≤ (y : ℝ) / (d : ℝ) := Nat.cast_div_le
      linarith [hle]
    have hfrac_lt : (y : ℝ) / (d : ℝ) - ((y / d : ℕ) : ℝ) < 1 := by
      have hmod : y < (y / d + 1) * d := by
        have h1 := Nat.div_add_mod y d
        have h2 : y % d < d := Nat.mod_lt y (by omega)
        nlinarith [h1, h2]
      have hcast : (y : ℝ) / (d : ℝ) < ((y / d : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ hdpos]
        have hh : (y : ℝ) < ((y / d + 1 : ℕ) : ℝ) * ((d : ℕ) : ℝ) := by exact_mod_cast hmod
        push_cast at hh; linarith [hh]
      linarith [hcast]
    have h1 : |chiRe χ d| ≤ 1 := chiRe_abs_le_one χ d
    have h2 : |(y : ℝ) / (d : ℝ) - ((y / d : ℕ) : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg hfrac_nn]; linarith [hfrac_lt]
    calc |chiRe χ d * ((y : ℝ) / (d : ℝ) - ((y / d : ℕ) : ℝ))|
        = |chiRe χ d| * |(y : ℝ) / (d : ℝ) - ((y / d : ℕ) : ℝ)| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hFrac : |∑ d ∈ Finset.Icc 1 r, chiRe χ d * ((y : ℝ) / (d : ℝ) - ((y / d : ℕ) : ℝ))|
      ≤ (r : ℝ) := by
    calc |∑ d ∈ Finset.Icc 1 r, chiRe χ d * ((y : ℝ) / (d : ℝ) - ((y / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Finset.Icc 1 r, |chiRe χ d * ((y : ℝ) / (d : ℝ) - ((y / d : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Finset.Icc 1 r, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (r : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  -- The `d`-leg `A = Σ chiRe(d)·⌊y/d⌋`.
  have hAeq : (∑ d ∈ Finset.Icc 1 r, chiRe χ d * ((y / d : ℕ) : ℝ))
      = (y : ℝ) * (∑ d ∈ Finset.Icc 1 r, chiRe χ d / (d : ℝ))
        - (∑ d ∈ Finset.Icc 1 r, chiRe χ d * ((y : ℝ) / (d : ℝ) - ((y / d : ℕ) : ℝ))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  have hA : (∑ d ∈ Finset.Icc 1 r, chiRe χ d * ((y / d : ℕ) : ℝ))
      ≤ L1.re * (y : ℝ) + 12 * (M * Real.sqrt y) + Real.sqrt y := by
    rw [hAeq]
    have hfrac_le :
        -(∑ d ∈ Finset.Icc 1 r, chiRe χ d * ((y : ℝ) / (d : ℝ) - ((y / d : ℕ) : ℝ)))
          ≤ Real.sqrt y := by
      calc -(∑ d ∈ Finset.Icc 1 r, chiRe χ d * ((y : ℝ) / (d : ℝ) - ((y / d : ℕ) : ℝ)))
          ≤ |∑ d ∈ Finset.Icc 1 r, chiRe χ d * ((y : ℝ) / (d : ℝ) - ((y / d : ℕ) : ℝ))| :=
            neg_le_abs _
        _ ≤ (r : ℝ) := hFrac
        _ ≤ Real.sqrt y := hr_le
    linarith [hyMain, hfrac_le]
  -- The transposed leg `B`.
  have hB : (∑ e ∈ Finset.Icc 1 r, ∑ d ∈ Finset.Icc 1 (y / e), chiRe χ d)
      ≤ M * Real.sqrt y := by
    calc (∑ e ∈ Finset.Icc 1 r, ∑ d ∈ Finset.Icc 1 (y / e), chiRe χ d)
        ≤ |∑ e ∈ Finset.Icc 1 r, ∑ d ∈ Finset.Icc 1 (y / e), chiRe χ d| := le_abs_self _
      _ ≤ ∑ e ∈ Finset.Icc 1 r, |∑ d ∈ Finset.Icc 1 (y / e), chiRe χ d| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ Finset.Icc 1 r, M := Finset.sum_le_sum (fun e _ => hStM (y / e))
      _ = (r : ℝ) * M := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      _ ≤ Real.sqrt y * M := mul_le_mul_of_nonneg_right hr_le hMnn
      _ = M * Real.sqrt y := by ring
  -- The corner block `C`.
  have hnegC : -((∑ d ∈ Finset.Icc 1 r, chiRe χ d) * (r : ℝ)) ≤ M * Real.sqrt y := by
    calc -((∑ d ∈ Finset.Icc 1 r, chiRe χ d) * (r : ℝ))
        ≤ |(∑ d ∈ Finset.Icc 1 r, chiRe χ d) * (r : ℝ)| := neg_le_abs _
      _ = |∑ d ∈ Finset.Icc 1 r, chiRe χ d| * |(r : ℝ)| := abs_mul _ _
      _ = |∑ d ∈ Finset.Icc 1 r, chiRe χ d| * (r : ℝ) := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r : ℝ))]
      _ ≤ M * (r : ℝ) := mul_le_mul_of_nonneg_right (hStM r) (by positivity)
      _ ≤ M * Real.sqrt y := mul_le_mul_of_nonneg_left hr_le hMnn
  -- Final assembly.
  have hkey : Real.sqrt y ≤ 6 * (M * Real.sqrt y) := by
    have h6M : (1 : ℝ) ≤ 6 * M := by linarith [hMge1]
    nlinarith [mul_le_mul_of_nonneg_left h6M (Real.sqrt_nonneg (y : ℝ)), Real.sqrt_nonneg (y : ℝ)]
  linarith [hA, hB, hnegC, hkey]

/-! ## R5-prerequisite — the transposed hyperbola (`sum_hyperbola_comm`)

The `b`-outer twin of `dhA_hyperbola_shift`: swapping the order of the two hyperbola
indices over the region `{(a,b) : 1 ≤ a, 1 ≤ b, a·b ≤ N}`. This is the pure `Finset`
reindex R5 uses to turn the `a`-outer detector hyperbola into `b`-outer form, exposing the
inner `a`-sum as the ζ-partial object `zeta_partial_em` bounds. Class B — no estimates. -/

/-- **The transposed hyperbola (sum_comm over the hyperbola region).** For any commutative
monoid `M` and `F : ℕ → ℕ → M`,
`Σ_{a≤N} Σ_{b≤N/a} F a b = Σ_{b≤N} Σ_{a≤N/b} F a b` — both sum `F a b` over the region
`{(a,b) : 1 ≤ a, 1 ≤ b, a·b ≤ N}`, `a`-outer vs `b`-outer. -/
lemma sum_hyperbola_comm {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) :
    ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), F a b
      = ∑ b ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 (N / b), F a b := by
  apply Finset.sum_comm'
  intro a b
  have hchar : ∀ u v : ℕ, (u ∈ Finset.Icc 1 N ∧ v ∈ Finset.Icc 1 (N / u))
      ↔ (1 ≤ u ∧ 1 ≤ v ∧ u * v ≤ N) := by
    intro u v
    simp only [Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hu1, _⟩, hv1, hvdiv⟩
      exact ⟨hu1, hv1, by rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le (by omega)).mp hvdiv⟩
    · rintro ⟨hu1, hv1, huv⟩
      refine ⟨⟨hu1, le_trans ?_ huv⟩, hv1, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
      · exact Nat.le_mul_of_pos_right u (by omega)
      · rw [Nat.mul_comm]; exact huv
  have hchar2 : ∀ u v : ℕ, (u ∈ Finset.Icc 1 (N / v) ∧ v ∈ Finset.Icc 1 N)
      ↔ (1 ≤ u ∧ 1 ≤ v ∧ u * v ≤ N) := by
    intro u v
    simp only [Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hu1, hudiv⟩, hv1, _⟩
      exact ⟨hu1, hv1, (Nat.le_div_iff_mul_le (by omega)).mp hudiv⟩
    · rintro ⟨hu1, hv1, huv⟩
      refine ⟨⟨hu1, (Nat.le_div_iff_mul_le (by omega)).mpr huv⟩, hv1, le_trans ?_ huv⟩
      exact Nat.le_mul_of_pos_left v (by omega)
  rw [hchar a b, hchar2 a b]

/-! ## R4-prerequisite — the Barban–Vehov `gc` harmonic moment (`sum_abs_grahamGc_div_le`)

The mollifier's `Σ_m |gc(m)|/m` moment. Since `grahamGc z m = 0` off the squarefree support
(`grahamGc_eq_zero_of_not_squarefree`) and `|gc(m)| ≤ 3^ω(m)` there (`abs_grahamGc_le`), the
sum is dominated by `Σ_{m≤M, sqfree} 3^ω(m)/m`, which the landed Hardy–Littlewood divisor
moment `tau6W_le` (k = 3) bounds by `(1+log M)³`. This is the polylog `Σ|gc|`-prefactor R4
consumes (the honest error-side moment; the sharp `1/log z` cancellation is the separate
main-term extraction). -/

/-- **R4-prerequisite — the `gc` harmonic moment.** For `z ≥ 2` and any `M`,
`Σ_{m≤M} |grahamGc z m|/m ≤ (1 + log M)³`. Restrict to the squarefree support of `gc`,
bound `|gc| ≤ 3^ω`, and apply the landed `tau6W_le` at `k = 3`. -/
lemma sum_abs_grahamGc_div_le {z : ℕ} (hz : 2 ≤ z) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, |grahamGc z m| / (m : ℝ) ≤ (1 + Real.log M) ^ 3 := by
  have hcond : ∀ m ∈ Finset.Icc 1 M, |grahamGc z m| / (m : ℝ) ≠ 0 → Squarefree m := by
    intro m _ hne
    by_contra hnsf
    exact hne (by rw [grahamGc_eq_zero_of_not_squarefree hnsf, abs_zero, zero_div])
  have key : ∑ m ∈ Finset.Icc 1 M, |grahamGc z m| / (m : ℝ)
      ≤ ∑ d ∈ (Finset.Icc 1 M).filter Squarefree,
          ((3 : ℕ) : ℝ) ^ (d.primeFactors.card) / (d : ℝ) := by
    rw [← Finset.sum_filter_of_ne hcond]
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, _⟩, _⟩ := hm
    have hωbridge : ArithmeticFunction.cardDistinctFactors m = m.primeFactors.card := by
      rw [ArithmeticFunction.cardDistinctFactors_apply]; exact (List.card_toFinset _).symm
    have hgc : |grahamGc z m| ≤ ((3 : ℕ) : ℝ) ^ (m.primeFactors.card) := by
      have h := abs_grahamGc_le hz m
      rw [hωbridge] at h
      convert h using 2; norm_num
    have hmpos : (0 : ℝ) ≤ (m : ℝ) := by positivity
    exact div_le_div_of_nonneg_right hgc hmpos
  exact le_trans key (Salt.HardyLittlewood.tau6W_le M 3)

end Salt.SW

end
