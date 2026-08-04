/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.ZetaEM
import Salt.SW.TBalR8
import Salt.SW.DensityCrude

/-!
# THE FULCRUM CAMPAIGN, node TAU-EXT — **the tall box: the `β`-supplier's packaging and interface**

⟦N2-WAVE HOME⟧ closed the density side with a finding: at the ⟦N0 CLEAR⟧ truncation height
`T = efHeight q + 2 = (log q + 2)⁴ + 2` the zero-density theorem collapses to a *count*, the
dyadic-in-`σ` spend telescopes losslessly, and **`β` — one real number, the ceiling on the real
parts of the box's zeros — is the entire interface to the artillery side**
(`efZeroSumM_spend_at_efHeight`). This node supplies that interface.

## The scope read (the trace, recorded because it is the design)

`dh_repulsion_ordered` (`Salt/SW/TBalR8.lean`) hypothesizes `|Im ρ| ≤ 1`. Tracing where that
restriction enters its **proof** — not its statement — gives a clean answer:

* the height hypothesis `him : |ρ.im| ≤ 1` on the zero is consumed at exactly two kinds of site:
  (i) to feed `hZ` — the `zetaHol_bound` packaging — **at the point `ρ` itself**
  (`norm_zeta_rho_le`, `DHExtractRho.lean:59,283,412`), never along a contour, never as a strip
  integral; and (ii) as the argument of `zeta_partial_em`'s height slot, which that lemma
  **ignores** (`ZetaEM.lean:123`, the binder is literally `_him`) because it reduces to the
  height-free `norm_zeta_sub_approx_le_strip`;
* every `β₀`-side use of `hZ` is at a **real** point (`hZ (β₀ : ℂ)`, `DHCore.lean:352,713`,
  `DHExtractW.lean:319,1187`, `CrushE.lean:225`) — height `0`, height-free already;
* the only other structural reading of the height is the crude `‖ρ‖ ≤ 2` inside `C2Rho_le`
  (`TBalR8.lean:1292`), which is a *polynomial* dependence: at `|Im ρ| ≤ T` it becomes
  `‖ρ‖ ≤ 1 + T ≤ Q` with `Q = q(|Im ρ| + 2)` the contract's own base.

**Verdict: route (a).** The height-1 restriction is PACKAGING, not analysis. The engine — the
detector floor, the shift, the row caps, the exponent balance — never reads the height except
through `Z₀` and through `‖ρ‖`, both of which ride polynomially in `Q`.

## What this file lands

1. **The tall packaging, with an EXPLICIT constant.** `zetaHol_bound` (`ZetaEM.lean:152`) is a
   compactness statement on the rectangle `[1/2,1] × [−1,1]`: it produces an *opaque* `Z₀` and it
   does not extend to a `q`-dependent height without making `Z₀` depend on `q` — which would
   destroy the uniformity of the repulsion constant `c`. Both defects are removed here at once by
   taking the Euler–Maclaurin estimate at `N = 1`, where the `N^{1−s}/(s−1)` term **cancels the
   Laurent pole exactly**:

       zetaHol s = 1 + O(‖s‖/σ)   uniformly on   1/2 ≤ Re s < 1,

   giving `‖zetaHol s‖ ≤ 3 + 2|Im s|` on the whole strip — height-FREE, explicit, no compactness.
   The closed edge `Re s = 1` follows by continuity in the real direction. Consequences:
   `zetaHol_bound_tall` (the drop-in `hZ` shape at any height `T`, with `Z₀ = 3 + 2T`) and
   `zetaHol_bound_five` (the *current* `hZ` shape at height 1, with the opaque compactness
   constant replaced by the numeral `5`).

2. **The `β` interface.** `repulsionCeiling` turns the Deuring–Heilbronn contract's shape
   (`1 − β₀ ≥ c·Q^{−b(1−σ)}/(log Q + 2)^k`) into the shape N4 consumes
   (`σ ≤ 1 − A·L^{−1}·log(1/η)`-genre), `repulsion_ceiling_of_contract` performs that inversion
   for one zero, `repulsionCeiling_mono` uniformises it across the box (the worst case is the
   TOP of the box, `Q = q(T+2)`), and `boxZeros_re_le_of_repulsion` assembles the `hβ` hypothesis
   of `efZeroSumM_spend_at_efHeight` verbatim. `efZeroSumM_spend_at_repulsion` is the composite:
   the campaign box's zero sum priced by one polylog constant times `y^{ceiling}`.

## The residual, priced (⟦TAU-EXT-2⟧)

The tall repulsion contract itself — `dh_repulsion_tall`, the twin of `dh_repulsion_ordered` with
`|Im ρ| ≤ 1` replaced by `|Im ρ| ≤ T` — is NOT landed here, because it is not additive: it is a
mechanical re-thread of ten *existing* statements (`norm_zeta_rho_le`, `emrho_perterm`,
`dhAbel_leg1_rho`, `dh_extraction_per_m_rho`, `unmoll_extraction_rho`, `dhAbel_inner_rho`,
`dh_extraction_upper_rho`, `dh_master_ray`, `dh_repulsion_inst`, `dh_repulsion_ordered`) whose
height binder `|ρ.im| ≤ 1` must become `|ρ.im| ≤ T`, plus a re-pricing of `C2Rho_le`
(`‖ρ‖ ≤ 2 ⇝ ‖ρ‖ ≤ 1 + T`) and of the two `Z₀`-carrying numerals `KEβ`, `KEρ`, `A₀` in
`dh_repulsion_ordered`'s `c`, where `Z₀ ⇝ 3 + 2T ≤ 3Q` is absorbed by the `Q`-exponent slack
(`b = 680` against the `104` actually spent — the ⟦N0 CLEAR⟧ audit prices the whole rescale at
**0.095%** of the clearance). Every input that re-thread needs is in this file. The statements it
must produce are exactly the hypotheses `hrep` below.
-/

open Complex DirichletCharacter Filter Set Metric Function
open scoped Topology

namespace Salt.SW

/-! ## 1. The tall `zetaHol` bound — height-free, explicit, and pole-cancelling -/

/-- **The strip bound, open edge.** For `1/2 ≤ Re s < 1`, `‖zetaHol s‖ ≤ 3 + 2|Im s|`.

The mechanism is the `N = 1` specialisation of the height-free Euler–Maclaurin estimate
`norm_zeta_sub_approx_le_strip`: at `N = 1` the approximation's tail term `N^{1−s}/(s−1)` is
*exactly* the Laurent pole `1/(s−1)` that `zetaHol` subtracts, so the two cancel and what is left
is `‖zetaHol s − 1‖ ≤ ‖s‖/Re s`. Then `‖s‖/Re s ≤ 2‖s‖` (from `Re s ≥ 1/2`) and
`‖s‖ ≤ Re s + |Im s| ≤ 1 + |Im s|`. No compactness, no height gate. -/
lemma zetaHol_norm_le_of_lt {s : ℂ} (hσ : 1 / 2 ≤ s.re) (hσ1 : s.re < 1) :
    ‖zetaHol s‖ ≤ 3 + 2 * |s.im| := by
  have hσ0 : (0 : ℝ) < s.re := by linarith
  have hne : s ≠ 1 := by
    intro h; rw [h] at hσ1; simp at hσ1
  have hEM := norm_zeta_sub_approx_le_strip (s := s) hσ0 hσ1 (N := 1) le_rfl
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, Complex.one_cpow,
    Real.one_rpow, mul_one] at hEM
  have hz : riemannZeta s - 1 - 1 / (s - 1) = zetaHol s - 1 := by
    rw [zetaHol_of_ne hne]; ring
  rw [hz] at hEM
  have h1 : ‖zetaHol s‖ - 1 ≤ ‖zetaHol s - 1‖ := by
    have h := norm_sub_norm_le (zetaHol s) (1 : ℂ)
    simpa using h
  have h2 : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    rw [div_le_iff₀ hσ0]; nlinarith [norm_nonneg s]
  have h3 : ‖s‖ ≤ 1 + |s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hσ0] at h; linarith
  linarith

/-- **The strip bound, closed strip.** `‖zetaHol s‖ ≤ 3 + 2|Im s|` for `1/2 ≤ Re s ≤ 1`.

The edge `Re s = 1` is reached from `zetaHol_norm_le_of_lt` by continuity along the real
direction: `zetaHol` is entire, so `x ↦ ‖zetaHol (x + i·Im s)‖` is continuous, and the bound holds
on `(1/2, 1)`, a set in `𝓝[<] 1`. -/
lemma zetaHol_norm_le {s : ℂ} (hσ : 1 / 2 ≤ s.re) (hσ1 : s.re ≤ 1) :
    ‖zetaHol s‖ ≤ 3 + 2 * |s.im| := by
  rcases lt_or_eq_of_le hσ1 with hlt | heq
  · exact zetaHol_norm_le_of_lt hσ hlt
  · set t : ℝ := s.im with htdef
    set f : ℝ → ℂ := fun x => (x : ℂ) + (t : ℂ) * Complex.I with hfdef
    have hfre : ∀ x : ℝ, (f x).re = x := by intro x; simp [hfdef]
    have hfim : ∀ x : ℝ, (f x).im = t := by intro x; simp [hfdef]
    have hfcont : Continuous f := by rw [hfdef]; fun_prop
    have hcont : Continuous fun x : ℝ => ‖zetaHol (f x)‖ :=
      (zetaHol_differentiable.continuous.comp hfcont).norm
    have hs1 : f 1 = s := by
      apply Complex.ext
      · rw [hfre]; exact heq.symm
      · rw [hfim]
    have hev : ∀ᶠ x in 𝓝[<] (1 : ℝ), ‖zetaHol (f x)‖ ≤ 3 + 2 * |t| := by
      filter_upwards [Ioo_mem_nhdsLT (show (1 : ℝ) / 2 < 1 by norm_num)] with x hx
      have h := zetaHol_norm_le_of_lt (s := f x) (by rw [hfre]; exact hx.1.le)
        (by rw [hfre]; exact hx.2)
      rwa [hfim] at h
    have htend : Tendsto (fun x : ℝ => ‖zetaHol (f x)‖) (𝓝[<] (1 : ℝ))
        (𝓝 ‖zetaHol (f 1)‖) := (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    have hle := le_of_tendsto htend hev
    rwa [hs1] at hle

/-- **THE TALL PACKAGING — `zetaHol_bound` at any height, with an explicit constant.**  The
`hZ` hypothesis threaded through the whole Deuring–Heilbronn chain has the shape
`∀ s, 1/2 ≤ Re s → Re s ≤ 1 → |Im s| ≤ H → ‖zetaHol s‖ ≤ Z₀`.  At `H = 1`
(`zetaHol_bound`) `Z₀` is an opaque compactness constant; here it is `3 + 2T` at **any** height
`T ≥ 0`, so the constant is a *named function of the height* and the repulsion constant built
from it stays uniform in `q` once `T` is charged to the contract's base `Q = q(|Im ρ| + 2)`. -/
theorem zetaHol_bound_tall (T : ℝ) :
    ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ T → ‖zetaHol s‖ ≤ 3 + 2 * T := by
  intro s h1 h2 h3
  have h := zetaHol_norm_le h1 h2
  linarith

/-- **The height-1 packaging, de-opaqued.** The exact hypothesis shape the landed chain consumes
(`dh_master_ray`, `dh_repulsion_inst`, …), now with the numeral `5` in place of `zetaHol_bound`'s
existential compactness constant. Any `Z₀`-carrying constant downstream is therefore computable:
`C_w = 34 + 12M + 12M·Z₀ + 36M/(1−β₀) ≤ 34 + 72M + 36M/(1−β₀)` (`DHCore.lean:688`). -/
theorem zetaHol_bound_five :
    ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ 5 := by
  intro s h1 h2 h3
  have h := zetaHol_norm_le h1 h2
  linarith

/-! ## 2. The `β` interface — inverting the repulsion contract into a ceiling -/

/-- **The Deuring–Heilbronn ceiling.** The real-part ceiling that the repulsion contract
`c·Q^{−b(1−σ)}/(log Q + 2)^k ≤ u` (`u = 1 − β₀`) forces on a zero at base `Q`:

    repulsionCeiling b c k Q u = 1 − (log(1/u) − log(1/c) − k·log(log Q + 2)) / (b·log Q).

At `u = η/L` and `Q ≍ q` this is HB's `σ₀ = 1 − A·L^{−1}·log η` verbatim: the numerator is
`log(1/η) + log L − O(log L)` and the denominator is `b·L`. -/
noncomputable def repulsionCeiling (b c k Q u : ℝ) : ℝ :=
  1 - (Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q + 2)) / (b * Real.log Q)

/-- **The inversion.** The repulsion contract at base `Q` is exactly a real-part ceiling: taking
logarithms of `c·Q^{−b(1−σ)}/(log Q + 2)^k ≤ u` and solving for `σ`. -/
theorem repulsion_ceiling_of_contract {b c k Q u σ : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hQ : 1 < Q) (hu : 0 < u)
    (hrep : c * Q ^ (-(b * (1 - σ))) / (Real.log Q + 2) ^ k ≤ u) :
    σ ≤ repulsionCeiling b c k Q u := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hL : 0 < Real.log Q := Real.log_pos hQ
  have hP : (0 : ℝ) < Real.log Q + 2 := by linarith
  have hApos : 0 < c * Q ^ (-(b * (1 - σ))) / (Real.log Q + 2) ^ k :=
    div_pos (mul_pos hc (Real.rpow_pos_of_pos hQ0 _)) (Real.rpow_pos_of_pos hP _)
  have hlog := Real.log_le_log hApos hrep
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (ne_of_gt hc) (by positivity),
    Real.log_rpow hQ0, Real.log_rpow hP] at hlog
  have hD : 0 < b * Real.log Q := mul_pos hb hL
  have hkey : Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q + 2)
      ≤ (1 - σ) * (b * Real.log Q) := by
    rw [Real.log_div one_ne_zero (ne_of_gt hu), Real.log_div one_ne_zero (ne_of_gt hc),
      Real.log_one]
    nlinarith [hlog]
  have hfin := (div_le_iff₀ hD).mpr hkey
  rw [repulsionCeiling]; linarith

/-- **The ceiling is monotone in the base.**  Raising `Q` weakens the ceiling (both because
`log Q` grows in the denominator and because the `−k·log(log Q + 2)` correction eats into the
numerator), so a bound uniform over a box is obtained at the box's TOP, `Q = q(T+2)`.  The
hypothesis `hN` — the numerator is nonnegative at the top — is the regime statement: the Siegel
zero is close enough to `1` that the contract says something, i.e. `η` is small. -/
lemma repulsionCeiling_mono {b c k u Q Q' : ℝ} (hb : 0 < b) (hk : 0 ≤ k)
    (hQ : 1 < Q) (hQQ : Q ≤ Q')
    (hN : 0 ≤ Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q' + 2)) :
    repulsionCeiling b c k Q u ≤ repulsionCeiling b c k Q' u := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQ'1 : 1 < Q' := lt_of_lt_of_le hQ hQQ
  have hL : 0 < Real.log Q := Real.log_pos hQ
  have hL' : 0 < Real.log Q' := Real.log_pos hQ'1
  have hLL : Real.log Q ≤ Real.log Q' := Real.log_le_log hQ0 hQQ
  have hP : (0 : ℝ) < Real.log Q + 2 := by linarith
  have hPP : Real.log (Real.log Q + 2) ≤ Real.log (Real.log Q' + 2) :=
    Real.log_le_log hP (by linarith)
  have hnum : Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q' + 2)
      ≤ Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q + 2) := by
    nlinarith [hk, hPP]
  have hD : 0 < b * Real.log Q := mul_pos hb hL
  have hDD : b * Real.log Q ≤ b * Real.log Q' := by nlinarith
  have hkey : (Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q' + 2))
        / (b * Real.log Q')
      ≤ (Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q + 2))
        / (b * Real.log Q) := by
    rw [div_le_div_iff₀ (mul_pos hb hL') hD]
    nlinarith [mul_le_mul_of_nonneg_right hnum hD.le,
      mul_le_mul_of_nonneg_left hDD (by linarith [hN, hnum] :
        (0 : ℝ) ≤ Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q + 2))]
  rw [repulsionCeiling, repulsionCeiling]
  linarith

/-! ## 3. The box assembly — `hβ` for `efZeroSumM_spend_at_efHeight` -/

/-- **THE `β`-SUPPLIER — the exact plug for `efZeroSumM_spend_at_efHeight`'s `hβ`.**

Given a Deuring–Heilbronn contract valid on the TALL box (`hrep`, the ⟦TAU-EXT-2⟧ deliverable
`dh_repulsion_tall`; at `T = 1` it is the landed `dh_repulsion_ordered` verbatim), every zero of
`L(·,χ)` in the box `{σ₀ ≤ Re ρ ≤ 1, |Im ρ| ≤ T}` has real part at most the single number
`repulsionCeiling b c k (q(T+2)) (1 − β₀)`.

**N4 consumes `β` here.** The three side hypotheses are the honest ones and each names a real
obligation:

* `hord` — the ordering `Re ρ ≤ β₀`, the named `T-BAL-UNORDERED` deviation of the contract
  (`β₀` is the box's *largest* real part, i.e. the exceptional zero);
* `hreal` — the zeros ON the real axis. The exceptional zero `β₀` itself is one of them and it
  does NOT satisfy the ceiling: it must be split off before this lemma is applied, exactly as
  HB (4.11) splits off the `−y^{β₀}/β₀` term of `ψ`;
* `hceil` — the ceiling sits above `16/17`, the contract's window floor, so the zeros in the
  discarded strip `Re ρ < 16/17` are covered for free. In the campaign regime the ceiling is
  `1 − O(L^{−1} log(1/η))`, far above `16/17`.

`hN` is the regime statement (`repulsionCeiling_mono`): the contract is non-vacuous at the top
of the box. -/
theorem boxZeros_re_le_of_repulsion {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) {b c k β₀ σ₀ T : ℝ} (hb : 0 < b) (hc : 0 < c) (hk : 0 ≤ k)
    (hq : 2 ≤ q) (hβ₀ : β₀ < 1)
    (hrep : ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ.im ≠ 0 → |ρ.im| ≤ T → 16 / 17 ≤ ρ.re →
      ρ.re < 1 → ρ.re ≤ β₀ →
      c * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(b * (1 - ρ.re)))
        / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ k ≤ 1 - β₀)
    (hord : ∀ ρ ∈ boxZeros χ σ₀ 1 T, ρ.re ≤ β₀)
    (hreal : ∀ ρ ∈ boxZeros χ σ₀ 1 T, ρ.im = 0 →
      ρ.re ≤ repulsionCeiling b c k ((q : ℝ) * (T + 2)) (1 - β₀))
    (hceil : 16 / 17 ≤ repulsionCeiling b c k ((q : ℝ) * (T + 2)) (1 - β₀))
    (hN : 0 ≤ Real.log (1 / (1 - β₀)) - Real.log (1 / c)
      - k * Real.log (Real.log ((q : ℝ) * (T + 2)) + 2)) :
    ∀ ρ ∈ boxZeros χ σ₀ 1 T,
      ρ.re ≤ repulsionCeiling b c k ((q : ℝ) * (T + 2)) (1 - β₀) := by
  intro ρ hρ
  obtain ⟨hzero, _hlo, hhi, him⟩ := (mem_boxZeros hχ1).mp hρ
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hu : (0 : ℝ) < 1 - β₀ := by linarith
  -- the closed edge `Re ρ = 1` is empty (`L(1,χ) ≠ 0` for `χ ≠ 1`)
  have hlt1 : ρ.re < 1 := by
    rcases lt_or_eq_of_le hhi with h | h
    · exact h
    · exact absurd hzero (LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (le_of_eq h.symm))
  rcases le_or_gt (16 / 17 : ℝ) ρ.re with hwin | hwin
  · rcases eq_or_ne ρ.im 0 with hre0 | hre0
    · exact hreal ρ hρ hre0
    · -- the contract at the zero's own base `Qρ = q(|Im ρ| + 2)`, then raised to the box top
      set Qρ : ℝ := (q : ℝ) * (|ρ.im| + 2) with hQρdef
      have hQρ1 : 1 < Qρ := by
        rw [hQρdef]; nlinarith [abs_nonneg ρ.im]
      have hQρle : Qρ ≤ (q : ℝ) * (T + 2) := by
        rw [hQρdef]; nlinarith [abs_nonneg ρ.im]
      have hstep := repulsion_ceiling_of_contract (σ := ρ.re) hb hc hQρ1 hu
        (hrep ρ hzero hre0 him hwin hlt1 (hord ρ hρ))
      exact le_trans hstep (repulsionCeiling_mono hb hk hQρ1 hQρle hN)
  · linarith [hceil]

/-- **THE COMPOSITE — the campaign box's zero sum priced by the repulsion ceiling.**
`efZeroSumM_spend_at_efHeight` fired at the `β` this node supplies: at the ⟦N0 CLEAR⟧ ruled
height `T = efHeight q + 2` the explicit formula's zero sum is

    ‖∑_{ρ ∈ boxZeros} m_ρ·y^ρ/ρ‖ ≤ 4110·(log q + 2)⁵·y^{repulsionCeiling b c k (q(T+2)) (1−β₀)},

with `q(T+2) = q·((log q + 2)⁴ + 4)`. This is the shape HB (4.11) consumes: at
`1 − β₀ = η/L` the exponent is `1 − A·L^{−1}·log(1/η) + o(1)` and `y ≥ q^{250}` converts it into
the `η^{−250A}` saving. -/
theorem efZeroSumM_spend_at_repulsion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {b c k β₀ σ y : ℝ} (hb : 0 < b) (hc : 0 < c) (hk : 0 ≤ k)
    (hσ : 1 / 2 ≤ σ) (hy : 1 ≤ y) (hβ₀ : β₀ < 1)
    (hrep : ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ.im ≠ 0 → |ρ.im| ≤ efHeight q + 2 →
      16 / 17 ≤ ρ.re → ρ.re < 1 → ρ.re ≤ β₀ →
      c * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(b * (1 - ρ.re)))
        / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ k ≤ 1 - β₀)
    (hord : ∀ ρ ∈ boxZeros χ σ 1 (efHeight q + 2), ρ.re ≤ β₀)
    (hreal : ∀ ρ ∈ boxZeros χ σ 1 (efHeight q + 2), ρ.im = 0 →
      ρ.re ≤ repulsionCeiling b c k ((q : ℝ) * (efHeight q + 4)) (1 - β₀))
    (hceil : 16 / 17 ≤ repulsionCeiling b c k ((q : ℝ) * (efHeight q + 4)) (1 - β₀))
    (hN : 0 ≤ Real.log (1 / (1 - β₀)) - Real.log (1 / c)
      - k * Real.log (Real.log ((q : ℝ) * (efHeight q + 4)) + 2)) :
    ‖efZeroSumM χ (boxZeros χ σ 1 (efHeight q + 2)) y‖
      ≤ 4110 * (Real.log q + 2) ^ 5
        * y ^ repulsionCeiling b c k ((q : ℝ) * (efHeight q + 4)) (1 - β₀) := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have heq : (q : ℝ) * (efHeight q + 2 + 2) = (q : ℝ) * (efHeight q + 4) := by ring
  refine efZeroSumM_spend_at_efHeight χ hχ hq hσ hy ?_
  have h := boxZeros_re_le_of_repulsion (χ := χ) hχ1 (b := b) (c := c) (k := k) (β₀ := β₀)
    (σ₀ := σ) (T := efHeight q + 2) hb hc hk hq hβ₀ hrep hord
    (by rw [heq]; exact hreal) (by rw [heq]; exact hceil) (by rw [heq]; exact hN)
  intro ρ hρ
  have := h ρ hρ
  rwa [heq] at this

/-- **THE UNIT-BOX WITNESS — the `β`-supplier fired off the LANDED artillery.**  This is
`boxZeros_re_le_of_repulsion` composed with `dh_repulsion_ordered` at `T = 1`: no hypothetical
contract, no `sorry`, the real Deuring–Heilbronn repulsion of `Salt/SW/TBalR8.lean`.  It exists
to prove that the interface *composes* — the contract shape emitted by the artillery is exactly
the shape `repulsion_ceiling_of_contract` inverts — so the ⟦TAU-EXT-2⟧ re-thread has nothing left
to discover about the seam: replacing the height binder `1` by `T` in the ten chain statements
turns this theorem into the campaign-box `β`-supplier verbatim, at base `q(T+2)` instead of
`q·3`. -/
theorem boxZeros_re_le_unit_box : ∃ b c k : ℝ, 0 < b ∧ 0 < c ∧ 0 ≤ k ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → 2 ≤ q →
      ∀ β₀ : ℝ, LFunction χ (β₀ : ℂ) = 0 → 1 / 2 < β₀ → β₀ < 1 →
      ∀ σ₀ : ℝ,
        (∀ ρ ∈ boxZeros χ σ₀ 1 1, ρ.re ≤ β₀) →
        (∀ ρ ∈ boxZeros χ σ₀ 1 1, ρ.im = 0 →
          ρ.re ≤ repulsionCeiling b c k ((q : ℝ) * 3) (1 - β₀)) →
        16 / 17 ≤ repulsionCeiling b c k ((q : ℝ) * 3) (1 - β₀) →
        0 ≤ Real.log (1 / (1 - β₀)) - Real.log (1 / c)
          - k * Real.log (Real.log ((q : ℝ) * 3) + 2) →
        ∀ ρ ∈ boxZeros χ σ₀ 1 1,
          ρ.re ≤ repulsionCeiling b c k ((q : ℝ) * 3) (1 - β₀) := by
  obtain ⟨b, c, k, hb, hc, hk, hDH⟩ := dh_repulsion_ordered
  refine ⟨b, c, k, hb, hc, hk, ?_⟩
  intro q _inst χ hχ hχ1 hsq hq β₀ hβ0zero hβ0lo hβ0hi σ₀ hord hreal hceil hN
  have h3 : (q : ℝ) * (1 + 2) = (q : ℝ) * 3 := by norm_num
  have hmain := boxZeros_re_le_of_repulsion (χ := χ) hχ1 (b := b) (c := c) (k := k) (β₀ := β₀)
    (σ₀ := σ₀) (T := 1) hb hc hk hq hβ0hi
    (fun ρ hz him hle hwin hlt hordρ =>
      hDH q χ hχ hχ1 hsq hq β₀ hβ0zero hβ0lo hβ0hi ρ hz him hle hwin hlt hordρ)
    hord (by rw [h3]; exact hreal) (by rw [h3]; exact hceil) (by rw [h3]; exact hN)
  intro ρ hρ
  have h := hmain ρ hρ
  rwa [h3] at h

end Salt.SW
