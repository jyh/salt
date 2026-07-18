/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHTrunc
import Salt.SW.GrahamL2

/-!
# The mollified shifted-detector capstone (HB-ENGINE, DH-TRUNC-M / DH-M)

Design: `docs/exploration/s3-hb3-design.md`, "DH-2b — THE PRODUCT-DETECTOR FREEZE".
Source: Benlİ–Goel–Twiss–Zaman, arXiv:2410.06082, §5.

This module closes **DH-TRUNC-M** — the *mollified* shifted-detector bound — the residual
`DHTrunc`'s `norm_shifted_detector_unmollified_le` left named. The unmollified capstone was the
`w ≡ 1` shadow; here the full Graham square `w(n) = (Σ_{d∣n} θ_d)²` is carried through the
**`gc`-regroup** (`GrahamL2.grahamW_eq_sum_grahamGc`).

## The route (the `gc`-regroup, cleaner than the footer's inclusion–exclusion)

The mollified sum is `D_ρ = Σ_{n≤N} dhCoeff(n)·n^{−ρ}·(1−n/x)₊` with
`dhCoeff = dhA·dhWeightSq` and `dhWeightSq z n = w(n) = Σ_{m∣n} gc(m)`. Regrouping the divisor
sum (`dhDetectorShift_regroup`):
  `D_ρ = Σ_{m≤N} gc(m)·Σ_{n≤N, m∣n} dhA(n)·n^{−ρ}·(1−n/x)₊`.

The inner `m`-divisible sum is bounded UNIFORMLY in `m` by the SAME grade as the unmollified
capstone, `P·(1 + N^{1−β}/(1−β))` with `P = 3√q(1+log q)(1+‖ρ‖/β)`. The key clean fact
(`dvd_mul_iff_div_gcd_dvd`, holding for ALL `m`, no squarefree needed): for the hyperbola
splitting `n = a·b`, the constraint `m ∣ a·b` is equivalent, for fixed `a`, to `dₐ ∣ b` where
`dₐ = m/gcd(m,a)`. The `b`-sum over the AP `{b : dₐ ∣ b}` is a T1-Abel object again (via the
character multiplicativity split `χ_ℝ(dₐb′) = χ_ℝ(dₐ)χ_ℝ(b′)`), so its partial sums are `≤ P`
(`norm_range_filter_dvd_partial_le`), and Abel against the antitone cutoff gives `≤ P` per `a`;
the `a`-sum then assembles via the ζ-partial `sum_Icc_rpow_neg_le`.

## What lands here (all sorry-free, axioms ⊆ [propext, Classical.choice, Quot.sound])

* **`dvd_mul_iff_div_gcd_dvd`** — `m ∣ a·b ↔ (m/gcd(m,a)) ∣ b` (all `m ≥ 1`, no squarefree).
* **`dhDetectorShift_regroup`** — the `gc`-regroup of the mollified detector.
* **`sum_range_filter_dvd_char_eq`** / **`norm_range_filter_dvd_partial_le`** — the AP-restricted
  character partial sum reindex (`b = dₐb′` + multiplicativity) and its uniform `≤ P` bound.
* **`norm_inner_mdiv_le`** — the `m`-uniform inner bound `≤ P·(1+N^{1−β}/(1−β))`.
* **`norm_shifted_detector_mollified_le`** — THE MOLLIFIED CAPSTONE:
  `‖D_ρ‖ ≤ (Σ_{m≤N}|gc(m)|)·P·(1 + N^{1−β}/(1−β))`. The honest error-side assembly; the
  mollifier's `1/log z` cancellation (the DEEP main-term extraction) remains the flagged residual.

## The residual (DH-TRUNC-A + the balance — precisely named, PROSE not `sorry`)

The `Σ_{m}|gc(m)|` prefactor is bounded ABOVE crudely (`|gc| ≤ 3^ω`, no sign cancellation). The
mollifier's true value comes from the SIGN of `gc(m)` (the Barban–Vehov `1/log z` cancellation,
`MoebiusLog.abs_sum_grahamTheta_div_le_inv_log`), which lives in the MAIN TERM of the inner sum's
`a`-side leading `(N/a)^{1−ρ}/(1−ρ)` pole part — NOT captured by the `≤ P` error bound here. That
main-term extraction (Benli §5's genuine `ζ·L·G` computation) plus the sharp inner Abel
(**DH-TRUNC-A**: the `≍(N/a)^{−β}` inner gain, needing Abel against the *ranged* T1
`partial_sum_at_zero_small_range` with the cutoff's linear variation) are the two remaining stones
before the balance `T-BAL` composes with `DHBalance.dh_repulsion_of_LFunction_one_lower` (M4).

## Honesty / death map (HB-ENGINE, R4 — NO twin claim)

NOT a proof of the Twin Prime Conjecture. Delivers competing-estimate substrate for the
conditional `InfinitelyManySiegelZeros → TwinPrimeConjecture`; the death rung is R4.
-/

open Complex

noncomputable section

namespace Salt.SW

open Finset

/-! ## Section 0 — the arithmetic seam `m ∣ a·b ↔ (m/gcd(m,a)) ∣ b`

The clean divisibility fact that lets the `m`-divisibility of the hyperbola pair `(a,b)` be
pushed entirely onto `b` as an arithmetic progression, for ANY `m` (no squarefree hypothesis,
unlike the design footer's inclusion–exclusion over splittings). -/

/-- **The `m`-divisibility transfer.** For `m ≥ 1` and any `a, b`, `m ∣ a·b ↔ (m/gcd(m,a)) ∣ b`.
Writing `g = gcd(m,a)`, `m = g·m'`, `a = g·a'` with `m'` coprime to `a'`: `m ∣ ab ⟺ m' ∣ a'b ⟺
m' ∣ b` (coprimality), and `m' = m/g`. Holds for all `m ≥ 1`. -/
lemma dvd_mul_iff_div_gcd_dvd {m a b : ℕ} (hm : 1 ≤ m) :
    m ∣ a * b ↔ (m / Nat.gcd m a) ∣ b := by
  have hgpos : 0 < Nat.gcd m a := by
    rcases Nat.eq_zero_or_pos (Nat.gcd m a) with h | h
    · rw [Nat.gcd_eq_zero_iff] at h; omega
    · exact h
  have hgm : Nat.gcd m a ∣ m := Nat.gcd_dvd_left m a
  have hga : Nat.gcd m a ∣ a := Nat.gcd_dvd_right m a
  have hmeq : m = Nat.gcd m a * (m / Nat.gcd m a) := (Nat.mul_div_cancel' hgm).symm
  have haeq : a = Nat.gcd m a * (a / Nat.gcd m a) := (Nat.mul_div_cancel' hga).symm
  have hcop : Nat.Coprime (m / Nat.gcd m a) (a / Nat.gcd m a) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have habexp : Nat.gcd m a * ((a / Nat.gcd m a) * b) = a * b := by
    rw [show Nat.gcd m a * ((a / Nat.gcd m a) * b) = (Nat.gcd m a * (a / Nat.gcd m a)) * b by ring,
      ← haeq]
  constructor
  · intro h
    have h1 : Nat.gcd m a * (m / Nat.gcd m a) ∣ Nat.gcd m a * ((a / Nat.gcd m a) * b) := by
      rw [← hmeq, habexp]; exact h
    have h2 : (m / Nat.gcd m a) ∣ (a / Nat.gcd m a) * b :=
      (mul_dvd_mul_iff_left (by omega : Nat.gcd m a ≠ 0)).mp h1
    exact hcop.dvd_of_dvd_mul_left h2
  · intro h
    have h2 : (m / Nat.gcd m a) ∣ (a / Nat.gcd m a) * b := h.mul_left _
    have h1 : Nat.gcd m a * (m / Nat.gcd m a) ∣ Nat.gcd m a * ((a / Nat.gcd m a) * b) :=
      mul_dvd_mul_left _ h2
    rw [← hmeq, habexp] at h1; exact h1

/-! ## Section 1 — the `gc`-regroup of the mollified detector

`w(n) = dhWeightSq z n = grahamW z n = Σ_{m∣n} gc(m)` (`GrahamL2.grahamW_eq_sum_grahamGc`, noting
`dhWeightSq` and `grahamW` are the same definition). Swapping the divisor sum against the outer
`n`-sum turns the mollified detector into a `gc`-weighted sum of `m`-divisible detector pieces —
the seam where the mollifier's local structure separates from the analytic `n`-sum. -/

/-- **The `gc`-regroup.** For any `q, χ, z, x, N, ρ`, the mollified shifted detector is the
`gc(m)`-weighted sum of its `m`-divisible pieces:
`D_ρ = Σ_{m≤N} gc(m)·Σ_{n≤N, m∣n} dhA(n)·n^{−ρ}·(1−n/x)₊`. Pure reindexing via the Selberg
λ²-regroup `w = Σ_{m∣·} gc` and a divisor-sum swap (the `grahamW_mean_eq` pattern, in the
`ℂ`-valued twisted frame). -/
theorem dhDetectorShift_regroup {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℕ) (x : ℝ) (N : ℕ)
    (ρ : ℂ) :
    dhDetectorShift χ z x N ρ
      = ∑ m ∈ Finset.Icc 1 N, (grahamGc z m : ℂ)
          * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m ∣ n),
              (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ) := by
  have hstep : ∀ n ∈ Finset.Icc 1 N,
      (dhCoeff χ z n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)
        = ∑ m ∈ Finset.Icc 1 N, if m ∣ n then
            (grahamGc z m : ℂ)
              * ((dhA χ n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ))
            else 0 := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hw : (dhWeightSq z n : ℂ) = ∑ m ∈ n.divisors, (grahamGc z m : ℂ) := by
      have hgw : dhWeightSq z n = ∑ m ∈ n.divisors, grahamGc z m := grahamW_eq_sum_grahamGc z n
      rw [hgw, Complex.ofReal_sum]
    have hdiv : n.divisors = (Finset.Icc 1 N).filter (fun m => m ∣ n) := by
      ext m
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hmn, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hmn (by omega),
          le_trans (Nat.le_of_dvd (by omega) hmn) hnN⟩, hmn⟩
      · rintro ⟨_, hmn⟩; exact ⟨hmn, by omega⟩
    have hcoeff : (dhCoeff χ z n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)
        = (dhWeightSq z n : ℂ)
            * ((dhA χ n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)) := by
      rw [dhCoeff, Complex.ofReal_mul]; ring
    rw [hcoeff, hw, Finset.sum_mul, hdiv, Finset.sum_filter]
  rw [dhDetectorShift, Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_filter, Finset.mul_sum]

/-! ## Section 2 — the AP-restricted character partial sum (Helper A)

The `m`-divisibility on the hyperbola pair `(a,b)` becomes `dₐ ∣ b` (`dₐ = m/gcd(m,a)`, Section 0),
so each inner `b`-sum is a character partial sum restricted to the arithmetic progression
`{b : dₐ ∣ b}`. Reindexing `b = dₐ·k` and using the character multiplicativity split
`χ_ℝ(dₐk) = χ_ℝ(dₐ)χ_ℝ(k)` (valid since `χ` is real) turns it into a `T1` object, whose partial
sums inherit the zero's cancellation uniformly: `≤ P`. -/

/-- **The AP-restricted reindex.** For real `χ` (`χ² = 1`) and `d ≥ 1`,
`Σ_{b<M, d∣b} χ_ℝ(b)b^{−ρ} = χ_ℝ(d)d^{−ρ}·Σ_{k<⌈M/d⌉} χ_ℝ(k)k^{−ρ}`. Reindex `b = d·k` (a
`Finset.sum_bij'` on the multiples of `d`) plus the character/`cpow` multiplicativity split. -/
lemma sum_range_filter_dvd_char_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {ρ : ℂ} {d : ℕ} (hd : 1 ≤ d) (M : ℕ) :
    ∑ b ∈ Finset.range M, (if d ∣ b then (chiRe χ b : ℂ) * (b : ℂ) ^ (-ρ) else 0)
      = (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)
          * ∑ k ∈ Finset.range ((M + d - 1) / d), (chiRe χ k : ℂ) * (k : ℂ) ^ (-ρ) := by
  have hdpos : 0 < d := by omega
  have hsplit : ∀ k : ℕ, (chiRe χ (d * k) : ℂ) * ((d * k : ℕ) : ℂ) ^ (-ρ)
      = (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ) * ((chiRe χ k : ℂ) * (k : ℂ) ^ (-ρ)) := by
    intro k
    have hc : (chiRe χ (d * k) : ℂ) = (chiRe χ d : ℂ) * (chiRe χ k : ℂ) := by
      rw [chiRe_ofReal χ hsq (d * k), chiRe_ofReal χ hsq d, chiRe_ofReal χ hsq k,
        Nat.cast_mul, map_mul]
    have hp : ((d * k : ℕ) : ℂ) ^ (-ρ) = (d : ℂ) ^ (-ρ) * (k : ℂ) ^ (-ρ) := by
      have h := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg k) (-ρ)
      simp only [Complex.ofReal_natCast] at h
      rw [Nat.cast_mul]; exact h
    rw [hc, hp]; ring
  calc ∑ b ∈ Finset.range M, (if d ∣ b then (chiRe χ b : ℂ) * (b : ℂ) ^ (-ρ) else 0)
      = ∑ b ∈ (Finset.range M).filter (fun b => d ∣ b),
          (chiRe χ b : ℂ) * (b : ℂ) ^ (-ρ) := (Finset.sum_filter _ _).symm
    _ = ∑ k ∈ Finset.range ((M + d - 1) / d),
          (chiRe χ (d * k) : ℂ) * ((d * k : ℕ) : ℂ) ^ (-ρ) := by
        refine Finset.sum_bij' (fun b _ => b / d) (fun k _ => d * k) ?_ ?_ ?_ ?_ ?_
        · intro b hb
          rw [Finset.mem_filter, Finset.mem_range] at hb
          obtain ⟨hbM, hdb⟩ := hb
          have hM1 : 1 ≤ M := by omega
          rw [Finset.mem_range]
          have h1 : b / d ≤ (M - 1) / d := Nat.div_le_div_right (by omega)
          have h2 : (M + d - 1) / d = (M - 1) / d + 1 := by
            rw [show M + d - 1 = (M - 1) + d by omega, Nat.add_div_right _ hdpos]
          omega
        · intro k hk
          rw [Finset.mem_range] at hk
          have hle : k + 1 ≤ (M + d - 1) / d := hk
          rw [Nat.le_div_iff_mul_le hdpos] at hle
          have e1 : (k + 1) * d = k * d + d := by ring
          have hdd : d ≤ (k + 1) * d := Nat.le_mul_of_pos_left d (by omega)
          have e2 : d * k = k * d := by ring
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, dvd_mul_right d k⟩
        · intro b hb
          rw [Finset.mem_filter] at hb
          exact Nat.mul_div_cancel' hb.2
        · intro k _
          exact Nat.mul_div_cancel_left k hdpos
        · intro b hb
          rw [Finset.mem_filter] at hb
          rw [Nat.mul_div_cancel' hb.2]
    _ = ∑ k ∈ Finset.range ((M + d - 1) / d),
          (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ) * ((chiRe χ k : ℂ) * (k : ℂ) ^ (-ρ)) :=
        Finset.sum_congr rfl (fun k _ => hsplit k)
    _ = (chiRe χ d : ℂ) * (d : ℂ) ^ (-ρ)
          * ∑ k ∈ Finset.range ((M + d - 1) / d), (chiRe χ k : ℂ) * (k : ℂ) ^ (-ρ) :=
        (Finset.mul_sum _ _ _).symm

/-- **Helper A — the AP-restricted uniform partial-sum bound.** For real primitive `χ` mod
`q ≥ 2` at a zero `ρ` (`0 < Re ρ ≤ 1`) and `d ≥ 1`, the `d`-restricted character partial sums
inherit the `B`-free bound `P = 3√q(1+log q)(1+‖ρ‖/ρ.re)`:
`‖Σ_{b<M, d∣b} χ_ℝ(b)b^{−ρ}‖ ≤ P`. Reindex (`sum_range_filter_dvd_char_eq`) + `‖χ_ℝ(d)‖ ≤ 1`,
`d^{−β} ≤ 1`, and the T1-uniform `norm_range_partial_at_zero_le` on the `k`-sum. -/
lemma norm_range_filter_dvd_partial_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re ≤ 1)
    {d : ℕ} (hd : 1 ≤ d) (M : ℕ) :
    ‖∑ b ∈ Finset.range M, (if d ∣ b then (chiRe χ b : ℂ) * (b : ℂ) ^ (-ρ) else 0)‖
      ≤ 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) := by
  rw [sum_range_filter_dvd_char_eq χ hsq hd M, norm_mul, norm_mul]
  have h1 : ‖(chiRe χ d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact chiRe_abs_le_one χ d
  have h2 : ‖(d : ℂ) ^ (-ρ)‖ ≤ 1 := by
    rw [norm_natCast_cpow_neg hρ0 d]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith)
  have h3 : ‖∑ k ∈ Finset.range ((M + d - 1) / d), (chiRe χ k : ℂ) * (k : ℂ) ^ (-ρ)‖
      ≤ 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) :=
    norm_range_partial_at_zero_le χ hχ hsq hq hzero hρ0 hρ1 _
  refine le_trans (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
    (norm_nonneg _) (by positivity)) (le_of_eq (by ring))

/-! ## Section 3 — the `m`-uniform inner bound and the mollified capstone

Each `m`-divisible piece `S_m = Σ_{n≤N, m∣n} dhA(n)·n^{−ρ}·(1−n/x)₊` obeys the SAME grade as the
unmollified capstone, uniformly in `m`: the hyperbola (`DHTrunc.dhA_hyperbola_shift` with the
`m∣·` indicator) reduces it to the `a`-sum of AP-restricted `b`-sums, each `≤ P` by Abel
(`DHTrunc.norm_sum_smul_antitone_le`) against Helper A's uniform partial sums, then the `a`-sum
closes via the ζ-partial `DHTrunc.sum_Icc_rpow_neg_le`. The mollifier's local structure has been
fully quarantined into the `Σ_m |gc(m)|` prefactor of the final capstone. -/

/-- **The `m`-uniform inner bound.** For real primitive `χ` mod `q ≥ 2` at a zero `ρ`
(`0 < Re ρ < 1`), `x > 0`, `N ≥ 1`, and any `m ≥ 1`, the `m`-divisible detector piece obeys the
`m`-free `unmollified` grade `‖Σ_{n≤N, m∣n} dhA(n)·n^{−ρ}·(1−n/x)₊‖ ≤ P·(1 + N^{1−β}/(1−β))`,
`P = 3√q(1+log q)(1+‖ρ‖/β)`. Hyperbola + the `m∣ab ⟺ dₐ∣b` transfer (Section 0) + Abel against
Helper A + the ζ-partial. -/
lemma norm_inner_mdiv_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) {m : ℕ} (hm : 1 ≤ m) :
    ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => m ∣ n),
        (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)‖
      ≤ 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re)
          * (1 + (N : ℝ) ^ (1 - ρ.re) / (1 - ρ.re)) := by
  set P : ℝ := 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) with hPdef
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hρnn : 0 ≤ ‖ρ‖ / ρ.re := div_nonneg (norm_nonneg _) hρ0.le
  have hP : 0 ≤ P := by rw [hPdef]; positivity
  have hρne : ρ ≠ 0 := by rintro rfl; simp at hρ0
  have hrangeGen : ∀ K : ℕ, Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := fun K => by
    ext y; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  set g : ℕ → ℂ :=
    fun n => if m ∣ n then (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ) else 0 with hg
  have heq1 : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m ∣ n),
        (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)
      = ∑ n ∈ Finset.Icc 1 N, (dhA χ n : ℂ) * g n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : m ∣ n
    · simp only [hg, if_pos h]; ring
    · simp only [hg, if_neg h, mul_zero]
  rw [heq1, dhA_hyperbola_shift χ g N]
  refine le_trans (norm_sum_le _ _) ?_
  have houter : ∀ a ∈ Finset.Icc 1 N,
      ‖∑ b ∈ Finset.Icc 1 (N / a), (chiRe χ b : ℂ) * g (a * b)‖ ≤ P * (a : ℝ) ^ (-ρ.re) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hgcdpos : 0 < Nat.gcd m a := by
      rcases Nat.eq_zero_or_pos (Nat.gcd m a) with hh | hh
      · rw [Nat.gcd_eq_zero_iff] at hh; omega
      · exact hh
    have hda : 1 ≤ m / Nat.gcd m a :=
      (Nat.one_le_div_iff hgcdpos).mpr (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left m a))
    set c : ℕ → ℂ :=
      fun b => if (m / Nat.gcd m a) ∣ b then (chiRe χ b : ℂ) * (b : ℂ) ^ (-ρ) else 0 with hc
    set w : ℕ → ℝ := fun b => dhKernR (((a * b : ℕ) : ℝ) / x) with hw
    have hw0' : ∀ i, 0 ≤ w i := fun i => by rw [hw]; exact dhKernR_nonneg _
    have h0 : w 0 • c 0 = 0 := by
      have hc0 : c 0 = 0 := by
        simp only [hc, Nat.cast_zero]
        rw [if_pos (dvd_zero _), Complex.zero_cpow (neg_ne_zero.mpr hρne), mul_zero]
      rw [hc0, smul_zero]
    have hw00 : w 0 = 1 := by
      simp only [hw, Nat.mul_zero, Nat.cast_zero, zero_div, dhKernR, sub_zero]
      exact max_eq_right zero_le_one
    have hanti' : Antitone w := by
      intro i j hij
      simp only [hw]
      have hnum : ((a * i : ℕ) : ℝ) ≤ ((a * j : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul (le_refl a) hij
      have hdiv : ((a * i : ℕ) : ℝ) / x ≤ ((a * j : ℕ) : ℝ) / x := by gcongr
      unfold dhKernR
      exact max_le_max (le_refl 0) (by linarith)
    have hpart' : ∀ M' : ℕ, ‖∑ i ∈ Finset.range M', c i‖ ≤ P := fun M' => by
      rw [hPdef]; simp only [hc]
      exact norm_range_filter_dvd_partial_le χ hχ hsq hq hzero hρ0 (le_of_lt hρ1) hda M'
    have hfac : ∑ b ∈ Finset.Icc 1 (N / a), (chiRe χ b : ℂ) * g (a * b)
        = (a : ℂ) ^ (-ρ) * ∑ b ∈ Finset.Icc 1 (N / a), c b * (w b : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      simp only [hg, hc, hw]
      by_cases h : (m / Nat.gcd m a) ∣ b
      · have hmab : m ∣ a * b := (dvd_mul_iff_div_gcd_dvd (by omega)).mpr h
        rw [if_pos hmab, if_pos h]
        have hcpow : ((a * b : ℕ) : ℂ) ^ (-ρ) = (a : ℂ) ^ (-ρ) * (b : ℂ) ^ (-ρ) := by
          have hh := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b) (-ρ)
          simp only [Complex.ofReal_natCast] at hh
          rw [Nat.cast_mul]; exact hh
        rw [hcpow]; ring
      · have hmab : ¬ m ∣ a * b := fun hh => h ((dvd_mul_iff_div_gcd_dvd (by omega)).mp hh)
        rw [if_neg hmab, if_neg h]; ring
    have hconv : ∑ b ∈ Finset.Icc 1 (N / a), c b * (w b : ℂ)
        = ∑ b ∈ Finset.range (N / a + 1), w b • c b := by
      rw [hrangeGen (N / a), Finset.sum_insert (by simp), h0, zero_add]
      exact Finset.sum_congr rfl fun b _ => by rw [Complex.real_smul, mul_comm]
    have hIa : ‖∑ b ∈ Finset.Icc 1 (N / a), c b * (w b : ℂ)‖ ≤ P := by
      rw [hconv]
      have habel := norm_sum_smul_antitone_le hpart' hanti' hw0' (N / a + 1)
      rwa [hw00, mul_one] at habel
    rw [hfac, norm_mul, norm_natCast_cpow_neg hρ0 a, mul_comm]
    exact mul_le_mul_of_nonneg_right hIa (Real.rpow_nonneg (Nat.cast_nonneg a) _)
  refine le_trans (Finset.sum_le_sum houter) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_le hρ0 hρ1 hN) hP

/-- **THE MOLLIFIED CAPSTONE (DH-TRUNC-M).** For a real primitive `χ` mod `q ≥ 2` at a zero `ρ`
with `0 < Re ρ < 1`, `x > 0`, `N ≥ 1`, the mollified shifted detector obeys
`‖D_ρ‖ ≤ (Σ_{m≤N}|gc(m)|)·P·(1 + N^{1−β}/(1−β))`, `P = 3√q(1+log q)(1+‖ρ‖/β)`, `β = Re ρ`.
The `gc`-regroup (`dhDetectorShift_regroup`) separates the mollifier into the `Σ_m|gc(m)|`
prefactor; each `m`-piece carries the unmollified grade `norm_inner_mdiv_le`. This is the honest
error-side assembly (the mollifier's `1/log z` cancellation — the DEEP main-term extraction — is
the flagged residual DH-TRUNC-A/T-BAL; here `|gc|` is bounded ABOVE, no sign cancellation). -/
theorem norm_shifted_detector_mollified_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (z : ℕ) {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    ‖dhDetectorShift χ z x N ρ‖
      ≤ (∑ m ∈ Finset.Icc 1 N, |grahamGc z m|)
          * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re)
              * (1 + (N : ℝ) ^ (1 - ρ.re) / (1 - ρ.re))) := by
  rw [dhDetectorShift_regroup]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ m ∈ Finset.Icc 1 N,
      ‖(grahamGc z m : ℂ) * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m ∣ n),
          (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)‖
        ≤ |grahamGc z m|
            * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re)
                * (1 + (N : ℝ) ^ (1 - ρ.re) / (1 - ρ.re))) := by
    intro m hmem
    rw [Finset.mem_Icc] at hmem
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (norm_inner_mdiv_le χ hχ hsq hq hzero hρ0 hρ1 hx hN hmem.1) (abs_nonneg _)
  exact le_trans (Finset.sum_le_sum hterm) (le_of_eq (Finset.sum_mul _ _ _).symm)

/-! ## Section 4 — DH-TRUNC-A: the sharp (ranged) Abel primitive

The mollified capstone above uses `DHTrunc.norm_sum_smul_antitone_le`, whose inner bound `P·w_0`
is CONSTANT — it collapses the ranged partial sums to a single uniform `P`. The sharp inner Abel
(**DH-TRUNC-A**) needs the DECAYING ranged bounds kept explicit. The core refactor is the
by-parts bound below, which exposes the ranged `Q n` (rather than a uniform `P`); a caller then
plugs in the decaying `Q(k) ≍ P·k^{−β}` (from `DHTrunc.partial_sum_at_zero_small`) and the
cutoff's LINEAR variation to extract the `≍(N/a)^{−β}` inner gain. -/

/-- **DH-TRUNC-A (the sharp Abel primitive — the ranged core).** Finite summation by parts
keeping the RANGED partial-sum bounds `Q n` explicit: if `‖Σ_{i<n} c_i‖ ≤ Q n` for every `n` and
`w` is antitone and `≥ 0`, then
`‖Σ_{i<n} w_i c_i‖ ≤ w_{n−1}·Q n + Σ_{i<n−1} (w_i − w_{i+1})·Q(i+1)`.
The exact object the sharp inner Abel consumes: with a DECAYING `Q(k) ≍ P·k^{−β}` and the
cutoff's linear variation `w_i − w_{i+1}`, the two explicit terms deliver the `(N/a)^{−β}` decay
that `DHTrunc.norm_sum_smul_antitone_le` (this bound with `Q ≡ P`, telescoped) throws away. -/
lemma norm_sum_smul_antitone_ranged_le {c : ℕ → ℂ} {w : ℕ → ℝ} {Q : ℕ → ℝ}
    (hpartial : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, c i‖ ≤ Q n)
    (hanti : Antitone w) (hw0 : ∀ i, 0 ≤ w i) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, w i • c i‖
      ≤ w (n - 1) * Q n + ∑ i ∈ Finset.range (n - 1), (w i - w (i + 1)) * Q (i + 1) := by
  rw [Finset.sum_range_by_parts w c n]
  refine le_trans (norm_sub_le _ _) ?_
  have hb1 : ‖w (n - 1) • ∑ i ∈ Finset.range n, c i‖ ≤ w (n - 1) * Q n := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 _)]
    exact mul_le_mul_of_nonneg_left (hpartial n) (hw0 _)
  have hb2 : ‖∑ i ∈ Finset.range (n - 1),
      (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), c j‖
      ≤ ∑ i ∈ Finset.range (n - 1), (w i - w (i + 1)) * Q (i + 1) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
    have hle : w (i + 1) ≤ w i := hanti (Nat.le_succ i)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith), neg_sub]
    exact mul_le_mul_of_nonneg_left (hpartial (i + 1)) (by linarith)
  linarith [hb1, hb2]

/-! ## Resume map (DH-M → next; PROSE, not `sorry`)

LANDED here (all sorry-free, axioms ⊆ [propext, Classical.choice, Quot.sound]):
* `dvd_mul_iff_div_gcd_dvd`, `dhDetectorShift_regroup`, `sum_range_filter_dvd_char_eq`,
  `norm_range_filter_dvd_partial_le`, `norm_inner_mdiv_le`, and the capstone
  `norm_shifted_detector_mollified_le` (**DH-TRUNC-M**, fully assembled).
* `norm_sum_smul_antitone_ranged_le` (**DH-TRUNC-A** core): the ranged by-parts bound.

### The two remaining stones (precisely named)

1. **DH-TRUNC-A (the decay assembly).** The ranged primitive is landed; the remaining work is to
   INSTANTIATE it with the decaying `Q(k) ≍ P·(k−1)^{−β}` (from `partial_sum_at_zero_small`) and
   the linear cutoff `w_b = (1 − a·dₐ·b/x)₊` (variation `a·dₐ/x` over the support `b ≤ x/(a·dₐ)`),
   then evaluate `w_{n−1}Q(n) + Σ(w_i−w_{i+1})Q(i+1)` — a `Σ_k k^{−β}` over the support — to the
   `(N/a)^{−β}`-grade inner bound. Sharpens `norm_inner_mdiv_le`'s `P·(1+N^{1−β}/(1−β))`.

2. **The main-term extraction + T-BAL (the PRIZE).** The `Σ_m |gc(m)|` prefactor of the capstone
   is bounded ABOVE (`|gc| ≤ 3^ω`), discarding the mollifier's SIGN cancellation. The genuine
   Benli balance extracts the MAIN TERM from the `a`-side leading `(N/a)^{1−ρ}/(1−ρ)` pole part,
   whose mollified value at the pole is `≍ L(1,χ)/log²z` via the SHARP Barban–Vehov
   `MoebiusLog.abs_sum_grahamTheta_div_le_inv_log` / `DHFinal.norm_dhGlin_one_le`. Composed with
   the floor `DHFinal.norm_dhDetectorShift_ge` and inverted by
   `DHBalance.dh_repulsion_of_LFunction_one_lower` (M4) this would reach `dh_repulsion` — the
   documented multi-session crux (may resist; NOT attempted here).

### Honesty (HB-ENGINE, R4 — NO twin claim)

NOT a proof of the Twin Prime Conjecture. Competing-estimate substrate only; the death rung is R4.
-/

end Salt.SW

end
