/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHFinal

/-!
# The shifted-frame truncation balance: the zero-extraction stones (HB-ENGINE, DH-TRUNC)

Design: `docs/exploration/s3-hb3-design.md`, "DH-2b — THE PRODUCT-DETECTOR FREEZE".
Source: Benlİ–Goel–Twiss–Zaman, arXiv:2410.06082, §5.

The shifted mirror of `DHClose.LFunction_one_re_ge_partial` (the UNSHIFTED balance at
`s = 1`). Here we work at a zero `ρ` of `L(·,χ)` and extract its content with NO contour and
NO Mellin, purely from the landed strip engine `norm_LFunction_sub_partial_le_strip`, which
holds AT ANY `s` in the strip `0 < Re s ≤ 1` — in particular at `s = ρ`.

## The key idea (the DHClose pattern at the zero)

At a zero `ρ` of `L(·,χ)`: `0 = L(ρ,χ) = Σ_{n≤N} χ(n) n^{−ρ} + tail`, so the PARTIAL SUM at
`ρ` is SMALL:
  `‖Σ_{n≤N} χ(n) n^{−ρ}‖ = ‖L(ρ,χ) − Σ_{n≤N} χ(n) n^{−ρ}‖ ≤ 3M(1+‖ρ‖/Re ρ)·N^{−Re ρ}`,
with `M = √q(1+log q)` (Pólya–Vinogradov). The zero's content is extracted with NO contour.

## What lands here (all sorry-free, axioms ⊆ [propext, Classical.choice, Quot.sound])

**T1 — the zero-extraction stone (the breakthrough).**
* **`partial_sum_at_zero_small`** — ONE LINE from the strip engine + the vanishing:
  `‖Σ_{n∈Icc 1 N} χ(n) n^{−ρ}‖ ≤ 3√q(1+log q)(1+‖ρ‖/ρ.re) N^{−ρ.re}`. Zero consumed, NO contour.
* **`partial_sum_at_zero_small_range`** — the ranged `Ioc N₁ N₂` version by differencing.

**The ζ-partial elementary lemma (the second stone).**
* **`sum_Icc_rpow_neg_le`** — `Σ_{m≤M} m^{−β} ≤ 1 + M^{1−β}/(1−β)` (`0<β<1`), integral
  comparison, PNT-free; the `M^{1−β}` main-term carrier. **`norm_sum_Icc_cpow_neg_le`** — its
  complex corollary for the un-damped ζ-side partial sum.

**T2 — the shifted-detector hyperbola factorization (the T1-ready frame).**
* **`dhA_hyperbola_shift`** — the combinatorial hyperbola for an arbitrary factor `g`:
  `Σ_{n≤N} dhA(n)g(n) = Σ_{a≤N} Σ_{b≤N/a} χ_ℝ(b) g(ab)`.
* **`shifted_detector_hyperbola`** — the exact factorization of the unmollified shifted detector
  into `Σ_a a^{−ρ}·Σ_b χ_ℝ(b) b^{−ρ} (1−ab/x)₊`; the inner `b`-sum is a T1 object.

**T2 (bound) — the Abel primitive + the capstone bound.**
* **`norm_sum_smul_antitone_le`** — the reusable Abel-summation bound
  `‖Σ_{i<n} w_i c_i‖ ≤ P·w_0` (uniform partial sums `≤ P`, `w` antitone `≥ 0`).
* **`norm_range_partial_at_zero_le`** — the `B`-uniform T1 bound `‖Σ_{b<m} χ(b)b^{−ρ}‖ ≤ P`.
* **`norm_shifted_detector_unmollified_le`** — the capstone: at a zero `ρ`,
  `‖Σ_{n≤N} dhA(n)n^{−ρ}(1−n/x)₊‖ ≤ P·(1 + N^{1−β}/(1−β))`, `P = 3√q(1+log q)(1+‖ρ‖/β)`. The
  zero flows T1 → Abel → factorization → ζ-partial into one `O(N^{1−β})` competing estimate.

## The residual (Rung 3 — precisely named, PROSE not `sorry`)

The capstone is the UNMOLLIFIED bound; its `O(N^{1−β})` grade does not decay to `o(1)`, so it
does not itself contradict the floor `‖D_ρ‖ ≥ 1−1/x` (`DHFinal.norm_dhDetectorShift_ge`, stated
for the MOLLIFIED `dhCoeff = dhA·(Σθ_d)²`). Two independent residuals remain, both multi-session:

> **DH-TRUNC-M (the mollified capstone).** The hyperbola factorization BREAKS for the mollified
> coefficient (`dhCoeff` is not `1∗χ` times a function, so it does not factor as ζ-side × χ-side).
> Benli §5 handles this via the THREE-factor `ζ·L·G` regroup: with `w(n) = Σ_{m∣n} gc(m)`
> (`GrahamL2.grahamW_eq_sum_grahamGc`), `Σ_n dhA(n)w(n)n^{−ρ}K = Σ_{m≤z²} gc(m)·Σ_{n: m∣n} …`,
> and the `gc`-regroup carries the sharp `1/log z` cancellation (`DHFinal.norm_dhGlin_one_le`)
> that damps the `Σχ(n)/n` error to `o(main)`. This is what the mollifier is FOR; the unmollified
> capstone here is its honest `w ≡ 1` shadow.

> **DH-TRUNC-A (the sharp inner Abel).** `norm_sum_smul_antitone_le` gives the CONSTANT inner
> bound `P·w_0`; the balance's decay needs the sharp `≍ (N/a)^{−β}` inner gain, i.e. Abel against
> the *ranged* T1 (`partial_sum_at_zero_small_range`) with the cutoff's exact linear variation,
> not just its total variation `≤ w_0`. Landed at the `O(N^{1−β})` grade; sharp grade is Rung 3.

## Honesty / death map (HB-ENGINE, R4 — NO twin claim)

NOT a proof of the Twin Prime Conjecture. Delivers competing-estimate substrate for the
conditional `InfinitelyManySiegelZeros → TwinPrimeConjecture`; the death rung is R4.
-/

open Complex

noncomputable section

namespace Salt.SW

open Finset

/-! ## T1 — the zero-extraction stone (the shifted balance at the zero `ρ`)

The single breakthrough: the strip engine `norm_LFunction_sub_partial_le_strip` at `s = ρ`
bounds `‖L(ρ,χ) − Σ_{n≤N} χ(n) n^{−ρ}‖`; since `L(ρ,χ) = 0` this IS a bound on the partial sum
itself. The "zero consumed without a contour" — the shifted mirror of `LFunction_one_re_ge_partial`
(which used the same engine at `s = 1`). -/

/-- **T1 — the zero-extraction stone.** For a primitive character `χ` mod `q ≥ 2`, at any zero
`ρ` of `L(·,χ)` in the strip `0 < Re ρ ≤ 1`, the ordered partial sum is small:
`‖Σ_{n∈Icc 1 N} χ(n)·n^{−ρ}‖ ≤ 3·√q·(1+log q)·(1+‖ρ‖/ρ.re)·N^{−ρ.re}`.
One line from the strip engine + `L(ρ,χ) = 0`; no contour, no Mellin. -/
theorem partial_sum_at_zero_small {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-ρ)‖
      ≤ 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) * (N : ℝ) ^ (-ρ.re) := by
  have hne : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hM : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod q)‖
      ≤ Real.sqrt q * (1 + Real.log q) := fun u => Salt.BV.polya_vinogradov χ hχ hq u
  have hstrip := norm_LFunction_sub_partial_le_strip χ hne hq hM hρ0 hρ1 hN
  rwa [hzero, zero_sub, norm_neg] at hstrip

/-- **T1 (ranged).** The zero-extraction stone over a half-open block `Ioc N₁ N₂`
(`1 ≤ N₁ ≤ N₂`), by differencing two `Icc 1 ·` partial sums:
`‖Σ_{n∈Ioc N₁ N₂} χ(n)·n^{−ρ}‖ ≤ 2·(3√q(1+log q)(1+‖ρ‖/ρ.re)·N₁^{−ρ.re})`.
The bound at `N₂` is `≤` the bound at `N₁` since `N^{−ρ.re}` decreases in `N`. -/
theorem partial_sum_at_zero_small_range {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re ≤ 1)
    {N₁ N₂ : ℕ} (h1 : 1 ≤ N₁) (h12 : N₁ ≤ N₂) :
    ‖∑ n ∈ Finset.Ioc N₁ N₂, χ (n : ZMod q) * (n : ℂ) ^ (-ρ)‖
      ≤ 2 * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) * (N₁ : ℝ) ^ (-ρ.re)) := by
  have hIcc : ∀ N : ℕ, Finset.Icc 1 N = Finset.Ioc 0 N := fun N => by
    ext x; rw [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hconsec := Finset.sum_Ioc_consecutive
    (fun n => χ (n : ZMod q) * (n : ℂ) ^ (-ρ)) (Nat.zero_le N₁) h12
  have hdiff : ∑ n ∈ Finset.Ioc N₁ N₂, χ (n : ZMod q) * (n : ℂ) ^ (-ρ)
      = (∑ n ∈ Finset.Icc 1 N₂, χ (n : ZMod q) * (n : ℂ) ^ (-ρ))
        - (∑ n ∈ Finset.Icc 1 N₁, χ (n : ZMod q) * (n : ℂ) ^ (-ρ)) := by
    rw [hIcc N₁, hIcc N₂]; exact eq_sub_of_add_eq' hconsec
  rw [hdiff]
  -- The two endpoint stones.
  have hb1 := partial_sum_at_zero_small χ hχ hq hzero hρ0 hρ1 h1
  have hb2 := partial_sum_at_zero_small χ hχ hq hzero hρ0 hρ1 (le_trans h1 h12)
  -- The prefactor is nonnegative and the power decreases in `N`.
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hρnn : 0 ≤ ‖ρ‖ / ρ.re := div_nonneg (norm_nonneg _) hρ0.le
  have hpre : 0 ≤ 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) := by positivity
  have hmono : (N₂ : ℝ) ^ (-ρ.re) ≤ (N₁ : ℝ) ^ (-ρ.re) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast h1) (by exact_mod_cast h12)
      (by linarith)
  have hb2' : ‖∑ n ∈ Finset.Icc 1 N₂, χ (n : ZMod q) * (n : ℂ) ^ (-ρ)‖
      ≤ 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) * (N₁ : ℝ) ^ (-ρ.re) :=
    hb2.trans (mul_le_mul_of_nonneg_left hmono hpre)
  refine le_trans (norm_sub_le _ _) ?_
  linarith [hb1, hb2']

/-! ## The ζ-partial elementary lemma (the second stone)

The ζ-side partial sums `Σ_{m≤M} m^{−ρ}` are NOT small (ζ has no zero here); they carry the
`M^{1−β}` main term. The honest finite bound is the elementary integral comparison
`Σ_{m≤M} m^{−β} ≤ 1 + M^{1−β}/(1−β)` (`β = Re ρ ∈ (0,1)`), PNT-free, mirroring
`StripConvergence.tail_dser_le`'s antitone-integral technique. This is the finite object the
T2 hyperbola's b-piece needs (the `N^{1−β}·L(1,χ)` main-term carrier). -/

/-- **The ζ-partial real bound.** For `0 < β < 1` and `M ≥ 1`,
`Σ_{m∈Icc 1 M} m^{−β} ≤ 1 + M^{1−β}/(1−β)`. Elementary integral comparison
(`AntitoneOn.sum_le_integral_Ico` on `t ↦ t^{−β}` + `∫_1^M t^{−β} = (M^{1−β}−1)/(1−β)`);
PNT-free. -/
lemma sum_Icc_rpow_neg_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {M : ℕ} (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, (m : ℝ) ^ (-β) ≤ 1 + (M : ℝ) ^ (1 - β) / (1 - β) := by
  have h1β : (0 : ℝ) < 1 - β := by linarith
  -- antitone on Icc 1 M
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-β)) (Set.Icc ((1 : ℕ) : ℝ) ((M : ℕ) : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -β ≤ 0)).mono
      (fun x hx => lt_of_lt_of_le (by exact_mod_cast Nat.one_pos) (Set.mem_Icc.mp hx).1)
  have hsi := AntitoneOn.sum_le_integral_Ico hM hanti
  -- the integral value ∫_1^M t^{−β} = (M^{1−β} − 1)/(1−β)
  have hival : (∫ x in ((1 : ℕ) : ℝ)..((M : ℕ) : ℝ), (fun t : ℝ => t ^ (-β)) x)
      = ((M : ℝ) ^ (1 - β) - 1) / (1 - β) := by
    simp only [Nat.cast_one]
    rw [integral_rpow (Or.inl (show (-1 : ℝ) < -β by linarith)),
      show -β + 1 = 1 - β from by ring, Real.one_rpow]
  rw [hival] at hsi
  -- reindex Icc 2 M ↔ the shifted Ico 1 M sum
  have hmapeq : (Finset.Ico 1 M).map (addRightEmbedding 1) = Finset.Icc 2 M := by
    rw [Finset.map_add_right_Ico]; ext x; rw [Finset.mem_Ico, Finset.mem_Icc]; omega
  have hreindex : ∑ m ∈ Finset.Icc 2 M, (m : ℝ) ^ (-β)
      = ∑ i ∈ Finset.Ico 1 M, ((i + 1 : ℕ) : ℝ) ^ (-β) := by
    rw [← hmapeq, Finset.sum_map]; rfl
  -- assemble: split m = 1, use the reindex and the integral bound
  have hins : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnm : (1 : ℕ) ∉ Finset.Icc 2 M := by simp only [Finset.mem_Icc]; omega
  have hkey : ∑ i ∈ Finset.Ico 1 M, ((i + 1 : ℕ) : ℝ) ^ (-β)
      ≤ ((M : ℝ) ^ (1 - β) - 1) / (1 - β) := hsi
  have hdiv : ((M : ℝ) ^ (1 - β) - 1) / (1 - β) ≤ (M : ℝ) ^ (1 - β) / (1 - β) := by
    rw [sub_div]; linarith [div_nonneg (zero_le_one) h1β.le]
  rw [hins, Finset.sum_insert hnm, Nat.cast_one, Real.one_rpow, hreindex]
  linarith [hkey, hdiv]

/-- **The ζ-partial complex bound.** For a zero-exponent-free shift `ρ` with `0 < Re ρ < 1`,
`‖Σ_{m∈Icc 1 M} m^{−ρ}‖ ≤ 1 + M^{1−Re ρ}/(1−Re ρ)`. Triangle inequality +
`norm_natCast_cpow_neg` + `sum_Icc_rpow_neg_le`. This bounds the un-damped ζ-side partial sum
(no zero used); the `M^{1−β}` growth is the main-term carrier of the balance. -/
lemma norm_sum_Icc_cpow_neg_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {M : ℕ} (hM : 1 ≤ M) :
    ‖∑ m ∈ Finset.Icc 1 M, (m : ℂ) ^ (-ρ)‖ ≤ 1 + (M : ℝ) ^ (1 - ρ.re) / (1 - ρ.re) := by
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ m ∈ Finset.Icc 1 M, ‖(m : ℂ) ^ (-ρ)‖ = (m : ℝ) ^ (-ρ.re) :=
    fun m _ => norm_natCast_cpow_neg hρ0 m
  rw [Finset.sum_congr rfl hterm]
  exact sum_Icc_rpow_neg_le hρ0 hρ1 hM

/-! ## T2 — the shifted-detector hyperbola factorization (the T1-ready frame)

The exact Dirichlet-hyperbola factorization of the UNMOLLIFIED shifted detector
`Σ_{n≤N} dhA(n)·n^{−ρ}·(1−n/x)₊`. Since `dhA = 1∗χ_ℝ`, the pair `(a,b)` with `n = a·b` splits
the sum into a ζ-side free index `a` and a χ-side index `b`; the inner `b`-sum is a CHARACTER
partial sum weighted by the monotone cutoff `(1−ab/x)₊` — exactly the object T1 bounds. This is
the finite frame where "the balance emerges" (Benli §5): NO estimates, a pure algebraic
identity, the substrate the Abel assembly (residual, below) consumes. -/

/-- **The combinatorial hyperbola (arbitrary factor).** For any `g : ℕ → ℂ`,
`Σ_{n≤N} dhA(n)·g(n) = Σ_{a≤N} Σ_{b≤N/a} χ_ℝ(b)·g(a·b)`. Pure reindexing: write
`dhA(n) = Σ_{a∣n} χ_ℝ(n/a)` (`Nat.sum_div_divisors`), swap the order, and reindex the multiples
of `a` in `[1,N]` by `n = a·b` (`b ∈ [1, N/a]`). No reality hypothesis. -/
lemma dhA_hyperbola_shift {q : ℕ} (χ : DirichletCharacter ℂ q) (g : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (dhA χ n : ℂ) * g n
      = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), (chiRe χ b : ℂ) * g (a * b) := by
  have hstep : ∀ n ∈ Finset.Icc 1 N, (dhA χ n : ℂ) * g n
      = ∑ a ∈ Finset.Icc 1 N, (if a ∣ n then (chiRe χ (n / a) : ℂ) * g n else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hset : n.divisors = (Finset.Icc 1 N).filter (fun a => a ∣ n) := by
      ext a
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) hn.2⟩, hdvd⟩
      · rintro ⟨_, hdvd⟩; exact ⟨hdvd, by omega⟩
    have hdhA : (dhA χ n : ℂ) = ∑ a ∈ n.divisors, (chiRe χ (n / a) : ℂ) := by
      rw [show dhA χ n = ∑ a ∈ n.divisors, chiRe χ (n / a) from
          by rw [dhA, ← Nat.sum_div_divisors n (chiRe χ)], Complex.ofReal_sum]
    rw [hdhA, Finset.sum_mul, hset, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_Icc] at ha
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun n _ => n / a) (fun b _ => a * b) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hdvd⟩ := hn
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hdvd),
      Nat.div_le_div_right hnN⟩
  · intro b hb
    rw [Finset.mem_Icc] at hb
    obtain ⟨hb1, hbN⟩ := hb
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right a b⟩
    · have : 0 < a * b := Nat.mul_pos (by omega) (by omega); omega
    · rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le (by omega)).mp hbN
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro b _
    exact Nat.mul_div_cancel_left b (by omega : 0 < a)
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]

/-- **T2 — the shifted-detector hyperbola factorization.** For any `q`, `χ`, `x`, `ρ`, `N`,
the unmollified shifted detector factors as
`Σ_{n≤N} dhA(n)·n^{−ρ}·(1−n/x)₊ = Σ_{a≤N} a^{−ρ}·Σ_{b≤N/a} χ_ℝ(b)·b^{−ρ}·(1−ab/x)₊`.
The inner `b`-sum is a character partial sum (the T1 object) weighted by the monotone cutoff.
Exact algebraic identity (`dhA_hyperbola_shift` + `(ab)^{−ρ} = a^{−ρ}b^{−ρ}`); NO estimates. -/
theorem shifted_detector_hyperbola {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) (ρ : ℂ)
    (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N,
        (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)
      = ∑ a ∈ Finset.Icc 1 N, (a : ℂ) ^ (-ρ) *
          ∑ b ∈ Finset.Icc 1 (N / a),
            (chiRe χ b : ℂ) * (b : ℂ) ^ (-ρ) * ((dhKernR (((a * b : ℕ) : ℝ) / x) : ℝ) : ℂ) := by
  have hcpow : ∀ a b : ℕ, ((a * b : ℕ) : ℂ) ^ (-ρ) = (a : ℂ) ^ (-ρ) * (b : ℂ) ^ (-ρ) := by
    intro a b
    have h := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b) (-ρ)
    simp only [Complex.ofReal_natCast] at h
    rw [Nat.cast_mul]; exact h
  rw [show (∑ n ∈ Finset.Icc 1 N,
      (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ))
      = ∑ n ∈ Finset.Icc 1 N, (dhA χ n : ℂ) *
          ((n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)) from
        Finset.sum_congr rfl fun n _ => by ring,
    dhA_hyperbola_shift χ
      (fun n => (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)) N]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [hcpow]
  ring

/-! ## T2 (bound) — the Abel primitive and the shifted-detector bound (the T1 crux)

The factorization's inner `b`-sum is a character partial sum weighted by the antitone cutoff.
Abel summation against the UNIFORM T1 partial-sum bound (`‖Σ_{b≤B} χ(b)b^{−ρ}‖ ≤ P`) passes the
zero's cancellation through the weight: `‖Σ_b χ(b)b^{−ρ}w_b‖ ≤ P·w_0`. This is the crux the
design named "Abel against T1's ranged partial sums"; the outer `a`-sum then assembles via the
ζ-partial lemma to the unmollified detector bound `O(P·N^{1−β})`. -/

/-- **The Abel-summation bound (reusable primitive).** If the range-partial sums of `c : ℕ → ℂ`
are uniformly bounded by `P` and `w : ℕ → ℝ` is antitone and nonnegative, then
`‖Σ_{i<n} w_i·c_i‖ ≤ P·w_0`. Finite summation by parts (`Finset.sum_range_by_parts`): the
boundary term is `≤ P·w_{n−1}` and the variation term telescopes to `P·(w_0−w_{n−1})`. -/
lemma norm_sum_smul_antitone_le {c : ℕ → ℂ} {w : ℕ → ℝ} {P : ℝ}
    (hpartial : ∀ m : ℕ, ‖∑ i ∈ Finset.range m, c i‖ ≤ P)
    (hanti : Antitone w) (hw0 : ∀ i, 0 ≤ w i) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, w i • c i‖ ≤ P * w 0 := by
  rw [Finset.sum_range_by_parts w c n]
  refine le_trans (norm_sub_le _ _) ?_
  have hb1 : ‖w (n - 1) • ∑ i ∈ Finset.range n, c i‖ ≤ P * w (n - 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hpartial n) (hw0 _)
  have hb2 : ‖∑ i ∈ Finset.range (n - 1),
      (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), c j‖ ≤ P * (w 0 - w (n - 1)) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range (n - 1),
        ‖(w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), c j‖ ≤ P * (w i - w (i + 1)) := by
      intro i _
      have hle : w (i + 1) ≤ w i := hanti (Nat.le_succ i)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith), neg_sub, mul_comm]
      exact mul_le_mul_of_nonneg_right (hpartial (i + 1)) (by linarith)
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_range_sub']
  have halg : P * w (n - 1) + P * (w 0 - w (n - 1)) = P * w 0 := by ring
  linarith [hb1, hb2, halg]

/-- **The uniform T1 partial-sum bound.** For a primitive real `χ` mod `q ≥ 2` at a zero `ρ`
(`0 < Re ρ ≤ 1`), the range-partial sums of `χ(b)·b^{−ρ}` are bounded by the `B`-free constant
`P = 3√q(1+log q)(1+‖ρ‖/ρ.re)`: T1 gives `·B^{−ρ.re}` and `B^{−ρ.re} ≤ 1` for `B ≥ 1`. -/
lemma norm_range_partial_at_zero_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re ≤ 1) (m : ℕ) :
    ‖∑ i ∈ Finset.range m, (chiRe χ i : ℂ) * (i : ℂ) ^ (-ρ)‖
      ≤ 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) := by
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hρnn : 0 ≤ ‖ρ‖ / ρ.re := div_nonneg (norm_nonneg _) hρ0.le
  have hpre : 0 ≤ 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) := by positivity
  have hρne : ρ ≠ 0 := by rintro rfl; simp at hρ0
  have hstep : ∑ i ∈ Finset.range m, (chiRe χ i : ℂ) * (i : ℂ) ^ (-ρ)
      = ∑ i ∈ Finset.range m, (i : ℂ) ^ (-ρ) * χ (i : ZMod q) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [chiRe_ofReal χ hsq i, mul_comm]
  rw [hstep]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have hz : ∑ i ∈ Finset.range m, (i : ℂ) ^ (-ρ) * χ (i : ZMod q) = 0 := by
      interval_cases m
      · simp
      · rw [Finset.sum_range_one, Nat.cast_zero,
          Complex.zero_cpow (neg_ne_zero.mpr hρne), zero_mul]
    rw [hz, norm_zero]; exact hpre
  · have hconv : ∑ i ∈ Finset.range m, (i : ℂ) ^ (-ρ) * χ (i : ZMod q)
        = ∑ n ∈ Finset.Icc 1 (m - 1), χ (n : ZMod q) * (n : ℂ) ^ (-ρ) := by
      rw [icc_sum_eq_range χ hq ρ (m - 1), show m - 1 + 1 = m from by omega]
    rw [hconv]
    refine le_trans (partial_sum_at_zero_small χ hχ hq hzero hρ0 hρ1 (by omega : 1 ≤ m - 1)) ?_
    have hle1 : ((m - 1 : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ m - 1))
        (by linarith)
    calc 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re)
            * ((m - 1 : ℕ) : ℝ) ^ (-ρ.re)
        ≤ 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) * 1 :=
          mul_le_mul_of_nonneg_left hle1 hpre
      _ = 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) := mul_one _

/-- **T2 (capstone) — the unmollified shifted-detector bound.** For a primitive real `χ` mod
`q ≥ 2` at a zero `ρ` with `0 < Re ρ < 1`, `x > 0`, `N ≥ 1`, the UNMOLLIFIED shifted detector
obeys `‖Σ_{n≤N} dhA(n)·n^{−ρ}·(1−n/x)₊‖ ≤ P·(1 + N^{1−β}/(1−β))`, `P = 3√q(1+log q)(1+‖ρ‖/β)`,
`β = Re ρ`. The zero flows through: factorization (T2) → each inner `b`-sum `≤ P` via Abel
against the T1-uniform partial sums → outer `Σ_a a^{−β} ≤ 1 + N^{1−β}/(1−β)` (ζ-partial). The
`O(N^{1−β})` grade is the honest unmollified competing estimate (the mollifier's `1/log z`
cancellation, needed to force `o(main)`, is the flagged residual — see the module footer). -/
theorem norm_shifted_detector_unmollified_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    ‖∑ n ∈ Finset.Icc 1 N,
        (dhA χ n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)‖
      ≤ 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re)
          * (1 + (N : ℝ) ^ (1 - ρ.re) / (1 - ρ.re)) := by
  set P : ℝ := 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re) with hPdef
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hρnn : 0 ≤ ‖ρ‖ / ρ.re := div_nonneg (norm_nonneg _) hρ0.le
  have hP : 0 ≤ P := by rw [hPdef]; positivity
  have hρne : ρ ≠ 0 := by rintro rfl; simp at hρ0
  have hrange : ∀ K : ℕ, Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := fun K => by
    ext y; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  -- inner bound: every hyperbola inner `b`-sum has norm ≤ P
  have hinner : ∀ a ∈ Finset.Icc 1 N,
      ‖∑ b ∈ Finset.Icc 1 (N / a), (chiRe χ b : ℂ) * (b : ℂ) ^ (-ρ)
          * ((dhKernR (((a * b : ℕ) : ℝ) / x) : ℝ) : ℂ)‖ ≤ P := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    set c : ℕ → ℂ := fun b => (chiRe χ b : ℂ) * (b : ℂ) ^ (-ρ) with hc
    set w : ℕ → ℝ := fun b => dhKernR (((a * b : ℕ) : ℝ) / x) with hw
    have hw0' : ∀ i, 0 ≤ w i := fun i => by rw [hw]; exact dhKernR_nonneg _
    have h0 : w 0 • c 0 = 0 := by
      simp only [hc, Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hρne), mul_zero, smul_zero]
    have hw00 : w 0 = 1 := by
      simp only [hw, Nat.mul_zero, Nat.cast_zero, zero_div, dhKernR, sub_zero]
      exact max_eq_right zero_le_one
    have hanti' : Antitone w := by
      intro i j hij
      simp only [hw]
      have hnum : ((a * i : ℕ) : ℝ) ≤ ((a * j : ℕ) : ℝ) :=
        by exact_mod_cast Nat.mul_le_mul (le_refl a) hij
      have hdiv : ((a * i : ℕ) : ℝ) / x ≤ ((a * j : ℕ) : ℝ) / x := by gcongr
      unfold dhKernR
      exact max_le_max (le_refl 0) (by linarith)
    have hpart' : ∀ m : ℕ, ‖∑ i ∈ Finset.range m, c i‖ ≤ P := fun m => by
      rw [hPdef]; simp only [hc]
      exact norm_range_partial_at_zero_le χ hχ hsq hq hzero hρ0 (le_of_lt hρ1) m
    have hconv : ∑ b ∈ Finset.Icc 1 (N / a), c b * (w b : ℂ)
        = ∑ b ∈ Finset.range (N / a + 1), w b • c b := by
      rw [hrange (N / a), Finset.sum_insert (by simp), h0, zero_add]
      exact Finset.sum_congr rfl fun b _ => by rw [Complex.real_smul, mul_comm]
    have hgoal : ∑ b ∈ Finset.Icc 1 (N / a),
          (chiRe χ b : ℂ) * (b : ℂ) ^ (-ρ) * ((dhKernR (((a * b : ℕ) : ℝ) / x) : ℝ) : ℂ)
        = ∑ b ∈ Finset.Icc 1 (N / a), c b * (w b : ℂ) :=
      Finset.sum_congr rfl fun b _ => by simp only [hc, hw]
    rw [hgoal, hconv]
    have habel := norm_sum_smul_antitone_le hpart' hanti' hw0' (N / a + 1)
    rwa [hw00, mul_one] at habel
  -- outer assembly via the factorization and the ζ-partial bound
  rw [shifted_detector_hyperbola χ x ρ N]
  refine le_trans (norm_sum_le _ _) ?_
  have houter : ∀ a ∈ Finset.Icc 1 N,
      ‖(a : ℂ) ^ (-ρ) * ∑ b ∈ Finset.Icc 1 (N / a), (chiRe χ b : ℂ) * (b : ℂ) ^ (-ρ)
          * ((dhKernR (((a * b : ℕ) : ℝ) / x) : ℝ) : ℂ)‖
        ≤ P * (a : ℝ) ^ (-ρ.re) := by
    intro a ha
    rw [norm_mul, norm_natCast_cpow_neg hρ0 a, mul_comm]
    exact mul_le_mul_of_nonneg_right (hinner a ha) (Real.rpow_nonneg (Nat.cast_nonneg a) _)
  refine le_trans (Finset.sum_le_sum houter) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_le hρ0 hρ1 hN) hP

end Salt.SW

end
