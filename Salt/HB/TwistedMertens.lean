/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.PretenseSumProof
import Salt.SW.PartialFractions
import Salt.SW.ZetaPole

/-!
# HB 1983, Lemma 3 — the twisted Mertens core (node N4a of the fulcrum campaign)

N3 (`Salt/HB/PretenseSumProof.lean`) landed HB's Lemma 3 with **exactly one** carried
analytic hypothesis, in either of two currencies:

* `hchi : twistedMertens χ N ≤ −log N + Rate` (the truncated Mertens shape), or
* `hcore : vmPairS χ N s ≤ 1/(s−1) − 1/(s−β₀) + Rate` (HB's own Dirichlet-series shape),

which is HB (4.2)+(4.3) added.  **This file discharges that hypothesis down to a single
named remainder**, by executing HB's p.206 route — the Dirichlet-series differencing at
`s = 1 + L^{−1}` against `s′ = 1 + aL^{−1}`, with no truncation anywhere.

## 🔴 CURRENCY FINDING (loud, of this wave)

`hchi`'s *truncated* shape `twistedMertens χ N ≤ −log N + Rate` is **not** what HB proves
and is **not** provable by this route.  `twistedMertens χ N = ∑_{n ≤ N} χ_ℝ(n)Λ(n)/n` is a
**signed** truncation: its terms have no sign, so the truncated sum is *not* dominated by
the full Dirichlet series, and the cut at `N` cannot be paid for.  What HB actually
estimates — and what the kernel can carry — is the **pair** sum `(1 + χ_ℝ)Λ`, every term of
which is `≥ 0` (N3's detector stone), so that truncation is free.  Accordingly this file
targets **`hcore`**, N3's series currency, and the final assembly runs through
`pretenseSum_le_series` rather than `pretenseSum_le`.  N3 anticipated this: `hchi` and
`hcore` are advertised as "equivalent currencies", and only `hcore` is the kernel one.

## The route, part by part

**(1) The identity.**  `−L′/L(s,χ) = ∑_n χ(n)Λ(n)n^{−s}` on `Re s > 1` is landed as
`Salt.SW.neg_logDeriv_LSeries_eq_LSeries_twist` (a re-export of mathlib's
`DirichletCharacter.LSeries_twist_vonMangoldt_eq`) — but for the `LSeries ↗χ` carrier,
while the partial fraction speaks of `DirichletCharacter.LFunction χ`.  §1 bridges the two
logarithmic derivatives (`logDeriv_LFunction_eq_LSeries`, off `LFunction_eq_LSeries` and
the openness of `{Re s > 1}`) and then takes **real parts at real `s`**, which is where
`χ_ℝ = Re χ` enters: `Re(−L′/L(σ,χ)) = ∑_n χ_ℝ(n)Λ(n)n^{−σ}`.  Two consequences, both
unconditional:

* `vmPairS_le_pole` — **HB (4.3) discharged**: `vmPairS χ N σ ≤ 1/(σ−1) + 1 + Re(−L′/L(σ,χ))`
  for `1 < σ ≤ 2`.  The `1/(σ−1) + 1` is the landed `Salt.SW.neg_logDeriv_zeta_le`; the
  truncation `∑_{n ≤ N} ≤ ∑_n` is free because every pair term is `≥ 0`.
* `neg_re_logDeriv_LFunction_le` — the `s′`-side input HB records as
  `L′/L(s′,χ) ≪ ∑Λ(n)n^{−s′} ≪ (s′−1)^{−1}`: `Re(−L′/L(σ′,χ)) ≤ 1/(σ′−1) + 1`, by
  `χ_ℝ ≤ 1` termwise against the ζ-series.

**(2) The differencing (HB (4.1)).**  `neg_re_logDeriv_differenced` is HB's p.206 line
carried out on the *disk-local* partial fraction (`Salt.SW.LFunction_partialFraction` at
`t₀ = 0`, whose disk `ball (2, 3/2)` contains both operating points and exactly the zeros
with `|γ| ≲ 1`).  Writing `A(σ) = L′/L(σ,χ) − ∑_{ρ∈Z} m_ρ/(σ−ρ)` for the remainder,

    −Re L′/L(σ,χ)  ≤  −Re L′/L(σ′,χ)  +  ∑_{ρ∈Z} m_ρ[Re(σ′−ρ)^{−1} − Re(σ−ρ)^{−1}]
                        + ‖A(σ) − A(σ′)‖,

and the middle sum is split exactly as HB splits it: the `ρ = β₀` term supplies the main
term `−1/(σ−β₀)` (up to `+1/(σ′−β₀) ≤ 1/(σ′−1) ≍ La^{−1}`, using only `m_{β₀} ≥ 1` and the
*sign* of `1/(σ′−β₀) − 1/(σ−β₀)`), and every other term is paid by

    ‖(σ−ρ)^{−1} − (σ′−ρ)^{−1}‖ = (σ′−σ)/(‖σ−ρ‖‖σ′−ρ‖) ≤ 4(σ′−σ)·‖ρ−1‖^{−2}

(`per_zero_inv_diff_le`), the factor `4` coming from the repulsion floor via
`dist_one_lower_of_floor`: if `σ − 1 ≤ r₀/2` and `r₀ ≤ ‖ρ−1‖` then `‖σ−ρ‖ ≥ ‖ρ−1‖/2`.
With `σ′ − σ ≍ aL^{−1}` this is HB's `O(aL^{−1}∑_{ρ≠β₀}|ρ−1|^{−2})` verbatim.

**(3) The `(4.1)` sum, near and far.**  `invSq_sum_split_le` prices
`∑_{ρ ∈ Z, ρ ≠ β₀} m_ρ|ρ−1|^{−2}` by splitting at `|ρ−1| = 1/4`:

* the **near** shells are N3's `nearOne_invSq_sum_le` (Prachar + the dyadic decomposition),
  giving `C(r₀^{−2} + log(f+2)·r₀^{−1})` — HB's inputs (2)+(3);
* the **far** zeros — HB's input (1), *the `|γ| ≥ 1` tail* — cost at most `16·∑_ρ m_ρ`,
  and `∑_ρ m_ρ` is bounded by the **Jensen count already exported by
  `LFunction_partialFraction`** (`≪ log(f(|t₀|+2))`, i.e. `≪ L`).  So the tail is `O(L)`,
  and after the prefactor `σ′−σ ≍ aL^{−1}` it is `O(a)` — exactly Davenport ch.14 (3)'s
  `∑_{|γ|≥1}|2−ρ|^{−2} ≪ L`, obtained here from the disk geometry rather than re-proved.
  **The `|γ| ≥ 1` tail therefore needs no separate artillery**: the disk-local partial
  fraction has already absorbed it.

**(4) The compose.**  `vmPairS_le_hb_core` is `hcore` with the rate `hbCoreRate`, and
`hb_lemma3_final` fires N3's slot bridge at it: HB (3.3) with **no `PretenseSum` and no
`hcore` left in it**.  `hbCoreRate_at_operating_point` evaluates the rate at HB's actual
points `σ = 1 + L^{−1}`, `σ′ = 1 + aL^{−1}`, producing his two error terms
`2(L/a) + 4Cs(aL/log η)` in the exact `A/a + B·a` shape that `PretenseSumProof`'s §3
optimizes, and `hbCoreRate_at_hb_optimum` collapses them at `a = (log η)^{1/2}` to
`(2 + 4Cs)·L(log η)^{−1/2}` — **the paper's rate, arrived at from this file's own
constants** rather than assumed.

## 🔴 WHAT IS STILL CARRIED (the exact residue, named)

`hb_lemma3_final`'s hypotheses beyond the transfer-side data (`hsq`, `hA`, `hres`, `hcoef`,
inherited verbatim from N3) are:

1. **`hrem`** — `‖A(σ) − A(σ′)‖ ≤ Rrem`, the difference of the partial fraction's analytic
   remainder at the two operating points.  This is Davenport ch.12 (17)'s `O(1)`.  It is
   **the one genuinely analytic item this wave does not close**: the corpus's bound on the
   remainder itself (`Salt.SW.LFunction_norm_logDeriv_sub_sum`) is `O(log M₀) = O(L)` *and*
   is gated by the unlanded Borel–Carathéodory sup input `hsup`; a *difference* bound of
   size `O(a)` needs a Cauchy estimate on `(h′/h)′` over the disk, which needs the same
   `hsup`.  So `Rrem` is blocked behind `hsup` — **the PB-floor flag of
   `Salt/SW/BCBound.lean`, reached again from a second direction.**
2. **`hβZ`, `hmβ`** — `(β₀ : ℂ) ∈ Z` and `1 ≤ m β₀`: the Siegel zero is one of the disk
   zeros, with multiplicity ≥ 1.  True, but *not exported*: `LFunction_partialFraction`
   states only `∀ ρ ∈ Z, L ρ = 0` (one direction), never `L ρ = 0 → ρ ∈ Z`.  Closing this
   needs a strengthened export of the factorization (`Z = support (divisor …)`), not new
   mathematics.
3. **`hmz`** (in `invSq_sum_split_le`) — `m ρ ≤ zeroMult χ ρ` on `Z`.  Again true and again
   unexported: `LFunction_partialFraction`'s `m` *is* `(divisor (LFunction χ) (ball c R) ·).toNat`,
   which agrees with `analyticOrderNatAt` on the ball, but the existential hides it.
4. **`hfloor`** — the Deuring–Heilbronn repulsion floor `r₀ ≤ ‖ρ − 1‖` off `β₀`.  This is
   *supplied*, not owed: N3's `one_sub_ceiling_le_dist_one` turns
   `Salt.SW.boxZeros_re_le_unit_box` / `boxZeros_re_le_at_efHeight` into exactly this shape.
   It is carried here only because the artillery's own side quartet
   (`hord`/`hreal`/`hceil`/`hN`) is F-side context that N8 supplies once.

Items 2 and 3 are *export* defects of a landed theorem; item 1 is the only mathematics.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction LSeries.notation
open Salt.TwinBar

namespace Salt.HB

/-! ## §1 — the Dirichlet-series identity in real parts (HB's (4.3) side) -/

/-- **The carrier bridge.**  On `Re s > 1` the analytically-continued `LFunction χ` and the
naive `LSeries ↗χ` agree (`DirichletCharacter.LFunction_eq_LSeries`), and `{Re s > 1}` is
open, so their logarithmic derivatives agree there too.  This is what lets the partial
fraction (stated for `LFunction`) and the `−L′/L = ∑χΛn^{−s}` identity (stated for
`LSeries`) be used on the same object. -/
lemma logDeriv_LFunction_eq_LSeries {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f) {s : ℂ}
    (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunction χ) s = logDeriv (LSeries ↗χ) s := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds s] LSeries ↗χ :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z : ℂ | 1 < z.re}, hopen.mem_nhds hs,
        fun _ hz => DirichletCharacter.LFunction_eq_LSeries χ hz⟩
  simp only [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]

/-- The twisted `Λ`-series term at a **real** point, with the real weight factored out. -/
private lemma term_twist_real {f : ℕ} (χ : DirichletCharacter ℂ f) (σ : ℝ) (n : ℕ) :
    LSeries.term (↗χ * ↗vonMangoldt) (σ : ℂ) n
      = χ (n : ZMod f) * ((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hrw : ((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) = (Λ n : ℂ) / (n : ℂ) ^ (σ : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_cpow hn0, Complex.ofReal_natCast,
        Complex.ofReal_neg, Complex.cpow_neg, div_eq_mul_inv]
    rw [LSeries.term_of_ne_zero hn, Pi.mul_apply, hrw]
    ring

/-- The untwisted `Λ`-series term at a **real** point. -/
private lemma term_vm_real (σ : ℝ) (n : ℕ) :
    LSeries.term ↗vonMangoldt (σ : ℂ) n = ((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [LSeries.term_of_ne_zero hn, Complex.ofReal_mul, Complex.ofReal_cpow hn0,
      Complex.ofReal_natCast, Complex.ofReal_neg, Complex.cpow_neg, div_eq_mul_inv]

/-- The real part of the twisted term is `χ_ℝ(n)·Λ(n)·n^{−σ}` — where `χ_ℝ = Re χ` enters. -/
private lemma re_term_twist {f : ℕ} (χ : DirichletCharacter ℂ f) (σ : ℝ) (n : ℕ) :
    (LSeries.term (↗χ * ↗vonMangoldt) (σ : ℂ) n).re = chiRe χ n * (Λ n * (n : ℝ) ^ (-σ)) := by
  rw [term_twist_real χ σ n, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  simp [chiRe]

private lemma re_term_vm (σ : ℝ) (n : ℕ) :
    (LSeries.term ↗vonMangoldt (σ : ℂ) n).re = Λ n * (n : ℝ) ^ (-σ) := by
  rw [term_vm_real σ n, Complex.ofReal_re]

/-- Summability of the untwisted real series `∑ Λ(n)n^{−σ}` at `σ > 1`. -/
private lemma summable_vm_real {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-σ)) := by
  have hσC : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hS := ArithmeticFunction.LSeriesSummable_vonMangoldt hσC
  exact ((Complex.hasSum_re hS.hasSum).summable).congr (fun n => re_term_vm σ n)

/-- Summability of the twisted real series `∑ χ_ℝ(n)Λ(n)n^{−σ}` at `σ > 1`. -/
private lemma summable_twist_real {f : ℕ} (χ : DirichletCharacter ℂ f) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => chiRe χ n * (Λ n * (n : ℝ) ^ (-σ))) := by
  have hσC : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hS := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hσC
  exact ((Complex.hasSum_re hS.hasSum).summable).congr (fun n => re_term_twist χ σ n)

/-- **The twisted identity in real parts.**  For real `σ > 1`,
`Re(−L′/L(σ,χ)) = ∑_n χ_ℝ(n)Λ(n)n^{−σ}`.  Part (1) of the route: the landed
`neg_logDeriv_LSeries_eq_LSeries_twist` carried across the `LFunction` bridge and then
projected onto real parts, where the complex character value becomes N3's `chiRe`. -/
theorem neg_re_logDeriv_LFunction_eq_tsum {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    {σ : ℝ} (hσ : 1 < σ) :
    (-logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re
      = ∑' n : ℕ, chiRe χ n * (Λ n * (n : ℝ) ^ (-σ)) := by
  have hσC : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hS := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hσC
  have hbridge : -logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)
      = LSeries (↗χ * ↗vonMangoldt) (σ : ℂ) := by
    rw [logDeriv_LFunction_eq_LSeries χ hσC, logDeriv_apply, ← neg_div]
    exact Salt.SW.neg_logDeriv_LSeries_eq_LSeries_twist χ hσC
  have hre : (LSeries (↗χ * ↗vonMangoldt) (σ : ℂ)).re
      = ∑' n : ℕ, (LSeries.term (↗χ * ↗vonMangoldt) (σ : ℂ) n).re := Complex.re_tsum hS
  rw [hbridge, hre]
  exact tsum_congr (fun n => re_term_twist χ σ n)

/-- **The untwisted identity in real parts.**  For real `σ > 1`,
`Re(−ζ′/ζ(σ)) = ∑_n Λ(n)n^{−σ}` (mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`,
projected). -/
theorem neg_re_logDeriv_zeta_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      = ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ) := by
  have hσC : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hS := ArithmeticFunction.LSeriesSummable_vonMangoldt hσC
  have hre : (LSeries ↗vonMangoldt (σ : ℂ)).re
      = ∑' n : ℕ, (LSeries.term ↗vonMangoldt (σ : ℂ) n).re := Complex.re_tsum hS
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσC, hre]
  exact tsum_congr (fun n => re_term_vm σ n)

/-- **The `s′`-side input (unconditional).**  HB's p.206 line
`L′/L(s′,χ) ≪ ∑Λ(n)n^{−s′} ≪ (s′−1)^{−1}`: since `χ_ℝ ≤ 1` and `Λ ≥ 0`, the twisted series
is dominated by the ζ-series, which `Salt.SW.neg_logDeriv_zeta_le` bounds by `1/(σ−1) + 1`
on `1 < σ ≤ 2`. -/
theorem neg_re_logDeriv_LFunction_le {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    (-logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
  rw [neg_re_logDeriv_LFunction_eq_tsum χ h1]
  have hdom : ∀ n : ℕ, chiRe χ n * (Λ n * (n : ℝ) ^ (-σ)) ≤ Λ n * (n : ℝ) ^ (-σ) := by
    intro n
    have hnn : (0 : ℝ) ≤ Λ n * (n : ℝ) ^ (-σ) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have h := abs_le.mp (chiRe_abs_le_one χ n)
    nlinarith [h.2]
  refine le_trans (Summable.tsum_le_tsum hdom (summable_twist_real χ h1)
    (summable_vm_real h1)) ?_
  rw [← neg_re_logDeriv_zeta_eq_tsum h1]
  exact Salt.SW.neg_logDeriv_zeta_le h1 h2

/-- **HB (4.3) DISCHARGED (unconditional).**  For `1 < σ ≤ 2`, the truncated detector sum is
bounded by the two full Dirichlet series, the untwisted one already spent at its pole:

    vmPairS χ N σ  ≤  1/(σ−1) + 1 + Re(−L′/L(σ,χ)).

Truncation is free: every term `(1 + χ_ℝ(n))Λ(n)n^{−σ}` is `≥ 0` (N3's detector stone), so
the finite sum is at most the tsum.  The `1/(σ−1) + 1` is `Salt.SW.neg_logDeriv_zeta_le`,
i.e. HB's `−ζ′/ζ(s) = 1/(s−1) + O(1)`. -/
theorem vmPairS_le_pole {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f) (N : ℕ)
    {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    vmPairS χ N σ ≤ 1 / (σ - 1) + 1
      + (-logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re := by
  classical
  have hgnn : ∀ n : ℕ, 0 ≤ (1 + chiRe χ n) * (Λ n * (n : ℝ) ^ (-σ)) := by
    intro n
    exact mul_nonneg (one_add_chiRe_nonneg χ n)
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hgsum : Summable (fun n : ℕ => (1 + chiRe χ n) * (Λ n * (n : ℝ) ^ (-σ))) :=
    ((summable_vm_real h1).add (summable_twist_real χ h1)).congr (fun n => by ring)
  have hfin : vmPairS χ N σ ≤ ∑' n : ℕ, (1 + chiRe χ n) * (Λ n * (n : ℝ) ^ (-σ)) := by
    rw [vmPairS, vmPairW]
    exact hgsum.sum_le_tsum _ (fun n _ => hgnn n)
  have hsplit : ∑' n : ℕ, (1 + chiRe χ n) * (Λ n * (n : ℝ) ^ (-σ))
      = (∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ))
        + ∑' n : ℕ, chiRe χ n * (Λ n * (n : ℝ) ^ (-σ)) := by
    rw [← (summable_vm_real h1).tsum_add (summable_twist_real χ h1)]
    exact tsum_congr (fun n => by ring)
  rw [neg_re_logDeriv_LFunction_eq_tsum χ h1]
  refine le_trans hfin ?_
  rw [hsplit]
  have hzeta : (∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ)) ≤ 1 / (σ - 1) + 1 := by
    rw [← neg_re_logDeriv_zeta_eq_tsum h1]
    exact Salt.SW.neg_logDeriv_zeta_le h1 h2
  linarith

/-! ## §2 — HB's (4.1) differencing at `s = 1 + L^{−1}` versus `s′ = 1 + aL^{−1}` -/

/-- `1/z − 1/w = (w − z)/(zw)` in norm — the elementary shape HB's `s`-vs-`s′` comparison
runs on. -/
lemma norm_inv_sub_inv {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖1 / z - 1 / w‖ = ‖w - z‖ / (‖z‖ * ‖w‖) := by
  rw [div_sub_div _ _ hz hw, norm_div, norm_mul]
  congr 1
  · congr 1; ring

/-- **The repulsion floor made geometric.**  If the operating point `σ` sits within `r₀/2`
of `1` and `ρ` is at distance at least `r₀` from `1`, then `ρ` is at distance at least
`‖ρ−1‖/2` from `σ`.  This is what converts HB's Deuring–Heilbronn floor
`r₀ ≫ L^{−1}log η` into the denominators of (4.1). -/
lemma dist_one_lower_of_floor {σ r0 : ℝ} {ρ : ℂ} (hσ1 : 1 ≤ σ) (hσr : σ - 1 ≤ r0 / 2)
    (hfl : r0 ≤ ‖ρ - 1‖) : ‖ρ - 1‖ / 2 ≤ ‖(σ : ℂ) - ρ‖ := by
  have hcast : ((σ : ℂ) - 1) = (((σ - 1 : ℝ)) : ℂ) := by push_cast; ring
  have hnorm : ‖((σ : ℂ) - 1)‖ = σ - 1 := by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hdec : (σ : ℂ) - ρ = ((σ : ℂ) - 1) - (ρ - 1) := by ring
  have htri : ‖ρ - 1‖ - ‖((σ : ℂ) - 1)‖ ≤ ‖(σ : ℂ) - ρ‖ := by
    rw [hdec]
    have := norm_sub_norm_le ((σ : ℂ) - 1) (ρ - 1)
    have h2 : ‖((σ : ℂ) - 1) - (ρ - 1)‖ = ‖(ρ - 1) - ((σ : ℂ) - 1)‖ := by
      rw [norm_sub_rev]
    linarith [norm_sub_norm_le (ρ - 1) ((σ : ℂ) - 1), h2]
  rw [hnorm] at htri
  linarith

/-- **The per-zero differencing estimate (HB (4.1)).**  For two operating points
`1 ≤ σ ≤ σ′` both within `r₀/2` of `1`, and a zero `ρ` at distance `≥ r₀` from `1`,

    ‖(σ−ρ)^{−1} − (σ′−ρ)^{−1}‖ = (σ′−σ)/(‖σ−ρ‖·‖σ′−ρ‖) ≤ 4(σ′−σ)·‖ρ−1‖^{−2}.

The factor `4` is the two applications of `dist_one_lower_of_floor`; the prefactor `σ′−σ`
is HB's `s′ − s ≪ aL^{−1}`. -/
lemma per_zero_inv_diff_le {σ σ' r0 : ℝ} {ρ : ℂ} (hσ1 : 1 ≤ σ) (hlt : σ ≤ σ')
    (hσr : σ - 1 ≤ r0 / 2) (hσ'r : σ' - 1 ≤ r0 / 2) (hr0 : 0 < r0) (hfl : r0 ≤ ‖ρ - 1‖) :
    ‖1 / ((σ : ℂ) - ρ) - 1 / ((σ' : ℂ) - ρ)‖ ≤ 4 * (σ' - σ) / ‖ρ - 1‖ ^ 2 := by
  have hρ0 : 0 < ‖ρ - 1‖ := lt_of_lt_of_le hr0 hfl
  have hlow : ‖ρ - 1‖ / 2 ≤ ‖(σ : ℂ) - ρ‖ := dist_one_lower_of_floor hσ1 hσr hfl
  have hlow' : ‖ρ - 1‖ / 2 ≤ ‖(σ' : ℂ) - ρ‖ :=
    dist_one_lower_of_floor (le_trans hσ1 hlt) hσ'r hfl
  have hz : ((σ : ℂ) - ρ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow; linarith
  have hw : ((σ' : ℂ) - ρ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow'; linarith
  rw [norm_inv_sub_inv hz hw]
  have hnum : ‖((σ' : ℂ) - ρ) - ((σ : ℂ) - ρ)‖ = σ' - σ := by
    have hcast : ((σ' : ℂ) - ρ) - ((σ : ℂ) - ρ) = (((σ' - σ : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hnum]
  have hden : ‖ρ - 1‖ ^ 2 / 4 ≤ ‖(σ : ℂ) - ρ‖ * ‖(σ' : ℂ) - ρ‖ := by
    nlinarith [hlow, hlow', hρ0]
  have hzpos : (0 : ℝ) < ‖(σ : ℂ) - ρ‖ := by
    rcases (norm_nonneg ((σ : ℂ) - ρ)).lt_or_eq with h | h
    · exact h
    · exact absurd (norm_eq_zero.mp h.symm) hz
  have hwpos : (0 : ℝ) < ‖(σ' : ℂ) - ρ‖ := by
    rcases (norm_nonneg ((σ' : ℂ) - ρ)).lt_or_eq with h | h
    · exact h
    · exact absurd (norm_eq_zero.mp h.symm) hw
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hden, sub_nonneg.mpr hlt]

/-- **THE DIFFERENCING (HB (4.1)+(4.2)), abstract in the partial-fraction data.**  Let `Lf`
be any function admitting the partial-fraction shape at the two real points `σ ≤ σ′`, with
zero set `Z` and multiplicities `m`, the Siegel zero `β₀ ∈ Z` isolated.  Then

    Re(−L′/L(σ))  ≤  −1/(σ−β₀)  +  [Re(−L′/L(σ′))]  +  1/(σ′−β₀)
                       +  4(σ′−σ)·∑_{ρ≠β₀} m_ρ‖ρ−1‖^{−2}  +  Rrem.

Reading of the terms, against HB p.206:

* `−1/(σ−β₀)` is the main term — the Siegel zero's *existence*, spent here and only here;
* `1/(σ′−β₀) ≤ 1/(σ′−1) ≍ La^{−1}` is his "isolate `ρ = β₀`, `(s′−β₀)^{−1} ≪ La^{−1}`";
* `Re(−L′/L(σ′)) ≤ 1/(σ′−1) + 1 ≍ La^{−1}` is `neg_re_logDeriv_LFunction_le`;
* `4(σ′−σ)·Sinv ≍ aL^{−1}·{r₀^{−2} + Lr₀^{−1}}` is the (4.1) error sum, priced by
  `invSq_sum_split_le` below;
* `Rrem` is the remainder difference — Davenport ch.12 (17)'s `O(1)`, the one carried item.

Only `1 ≤ m β₀` and the *sign* of `1/(σ′−β₀) − 1/(σ−β₀)` are used at the isolated zero: no
simplicity hypothesis, no reality hypothesis. -/
theorem neg_re_logDeriv_differenced {Lf : ℂ → ℂ} {Z : Finset ℂ} {m : ℂ → ℕ}
    {σ σ' β₀ r0 Sinv Rrem : ℝ}
    (hσ1 : 1 < σ) (hlt : σ ≤ σ') (hβ1 : β₀ < 1)
    (hβZ : (β₀ : ℂ) ∈ Z) (hmβ : 1 ≤ m (β₀ : ℂ))
    (hr0 : 0 < r0) (hσr : σ - 1 ≤ r0 / 2) (hσ'r : σ' - 1 ≤ r0 / 2)
    (hfloor : ∀ ρ ∈ Z.erase ((β₀ : ℂ)), r0 ≤ ‖ρ - 1‖)
    (hSinv : ∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv)
    (hrem : ‖(logDeriv Lf (σ : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) - ρ))
            - (logDeriv Lf (σ' : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ' : ℂ) - ρ))‖ ≤ Rrem)
    (hs'top : (-logDeriv Lf (σ' : ℂ)).re ≤ 1 / (σ' - 1) + 1) :
    (-logDeriv Lf (σ : ℂ)).re
      ≤ -(1 / (σ - β₀)) + (1 / (σ' - 1) + 1) + 1 / (σ' - β₀)
        + 4 * (σ' - σ) * Sinv + Rrem := by
  classical
  have hσ'1 : 1 < σ' := lt_of_lt_of_le hσ1 hlt
  have hdβ : (0 : ℝ) < σ - β₀ := by linarith
  have hdβ' : (0 : ℝ) < σ' - β₀ := by linarith
  -- the real parts of the two partial-fraction sums
  set S : ℝ := (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) - ρ)).re with hS
  set S' : ℝ := (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ' : ℂ) - ρ)).re with hS'
  set A : ℝ := (logDeriv Lf (σ : ℂ)).re with hA
  set A' : ℝ := (logDeriv Lf (σ' : ℂ)).re with hA'
  -- the remainder hypothesis, projected
  have hproj : -((A - S) - (A' - S')) ≤ Rrem := by
    refine le_trans ?_ hrem
    have habs := Complex.abs_re_le_norm
      ((logDeriv Lf (σ : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) - ρ))
        - (logDeriv Lf (σ' : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ' : ℂ) - ρ)))
    have hre : ((logDeriv Lf (σ : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) - ρ))
        - (logDeriv Lf (σ' : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ' : ℂ) - ρ))).re
        = (A - S) - (A' - S') := by
      simp [hA, hA', hS, hS']
    rw [hre] at habs
    linarith [(abs_le.mp habs).1]
  -- the termwise difference
  have hsumre : ∀ τ : ℝ, (∑ ρ ∈ Z, (m ρ : ℂ) / ((τ : ℂ) - ρ)).re
      = ∑ ρ ∈ Z, ((m ρ : ℂ) / ((τ : ℂ) - ρ)).re := by
    intro τ; exact Complex.re_sum Z _
  have hdiff : S' - S = ∑ ρ ∈ Z,
      (((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re) := by
    rw [hS, hS', hsumre σ, hsumre σ', ← Finset.sum_sub_distrib]
  -- split off `β₀`
  have hsplit : ∑ ρ ∈ Z, (((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re)
      = ((((m (β₀ : ℂ)) : ℂ) / ((σ' : ℂ) - (β₀ : ℂ))).re
          - (((m (β₀ : ℂ)) : ℂ) / ((σ : ℂ) - (β₀ : ℂ))).re)
        + ∑ ρ ∈ Z.erase ((β₀ : ℂ)),
            (((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re) :=
    (Finset.add_sum_erase Z _ hβZ).symm
  -- the isolated `β₀` term: real, and `≤ 1/(σ′−β₀) − 1/(σ−β₀)` since `m β₀ ≥ 1`
  have hβreal : ∀ τ : ℝ, 0 < τ - β₀ →
      (((m (β₀ : ℂ)) : ℂ) / ((τ : ℂ) - (β₀ : ℂ))).re = (m (β₀ : ℂ) : ℝ) / (τ - β₀) := by
    intro τ _
    have hc : ((τ : ℂ) - (β₀ : ℂ)) = (((τ - β₀ : ℝ)) : ℂ) := by push_cast; ring
    rw [hc, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
  have hβterm : (((m (β₀ : ℂ)) : ℂ) / ((σ' : ℂ) - (β₀ : ℂ))).re
      - (((m (β₀ : ℂ)) : ℂ) / ((σ : ℂ) - (β₀ : ℂ))).re
      ≤ 1 / (σ' - β₀) - 1 / (σ - β₀) := by
    rw [hβreal σ' hdβ', hβreal σ hdβ]
    have hmono : 1 / (σ' - β₀) ≤ 1 / (σ - β₀) := by
      apply one_div_le_one_div_of_le hdβ; linarith
    have hm1 : (1 : ℝ) ≤ (m (β₀ : ℂ) : ℝ) := by exact_mod_cast hmβ
    have hstep : ((m (β₀ : ℂ) : ℝ) - 1) * (1 / (σ' - β₀))
        ≤ ((m (β₀ : ℂ) : ℝ) - 1) * (1 / (σ - β₀)) :=
      mul_le_mul_of_nonneg_left hmono (by linarith)
    have he1 : (m (β₀ : ℂ) : ℝ) / (σ' - β₀) = (m (β₀ : ℂ) : ℝ) * (1 / (σ' - β₀)) := by
      rw [mul_one_div]
    have he2 : (m (β₀ : ℂ) : ℝ) / (σ - β₀) = (m (β₀ : ℂ) : ℝ) * (1 / (σ - β₀)) := by
      rw [mul_one_div]
    rw [he1, he2]
    nlinarith [hstep]
  -- the remaining zeros: paid at `4(σ′−σ)‖ρ−1‖^{−2}`
  have hother : ∑ ρ ∈ Z.erase ((β₀ : ℂ)),
      (((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re)
      ≤ 4 * (σ' - σ) * Sinv := by
    have hstep : ∀ ρ ∈ Z.erase ((β₀ : ℂ)),
        (((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re)
          ≤ 4 * (σ' - σ) * ((m ρ : ℝ) / ‖ρ - 1‖ ^ 2) := by
      intro ρ hρ
      have hfl := hfloor ρ hρ
      have hρ0 : 0 < ‖ρ - 1‖ := lt_of_lt_of_le hr0 hfl
      have hnorm := per_zero_inv_diff_le (σ := σ) (σ' := σ') (r0 := r0) (ρ := ρ)
        hσ1.le hlt hσr hσ'r hr0 hfl
      have heq : ((m ρ : ℂ) / ((σ' : ℂ) - ρ)) - ((m ρ : ℂ) / ((σ : ℂ) - ρ))
          = -((m ρ : ℂ) * (1 / ((σ : ℂ) - ρ) - 1 / ((σ' : ℂ) - ρ))) := by ring
      have hre : (((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re)
          = (-((m ρ : ℂ) * (1 / ((σ : ℂ) - ρ) - 1 / ((σ' : ℂ) - ρ)))).re := by
        rw [← heq, Complex.sub_re]
      rw [hre]
      refine le_trans (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)) ?_
      have hmn : ‖((m ρ : ℕ) : ℂ)‖ = (m ρ : ℝ) := by simp
      rw [norm_neg, norm_mul, hmn]
      calc (m ρ : ℝ) * ‖1 / ((σ : ℂ) - ρ) - 1 / ((σ' : ℂ) - ρ)‖
          ≤ (m ρ : ℝ) * (4 * (σ' - σ) / ‖ρ - 1‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hnorm (by positivity)
        _ = 4 * (σ' - σ) * ((m ρ : ℝ) / ‖ρ - 1‖ ^ 2) := by ring
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have hc : (0 : ℝ) ≤ 4 * (σ' - σ) := by linarith
    exact mul_le_mul_of_nonneg_left hSinv hc
  -- assemble
  have hneg : (-logDeriv Lf (σ : ℂ)).re = -A := by rw [hA, Complex.neg_re]
  have hneg' : (-logDeriv Lf (σ' : ℂ)).re = -A' := by rw [hA', Complex.neg_re]
  rw [hneg' ] at hs'top
  rw [hneg]
  have hSS : S' - S ≤ 1 / (σ' - β₀) - 1 / (σ - β₀) + 4 * (σ' - σ) * Sinv := by
    rw [hdiff, hsplit]; linarith
  linarith

/-! ## §3 — the `(4.1)` error sum: the near shells and the `|γ| ≥ 1` tail -/

/-- **HB's (4.1) error sum, split at `|ρ−1| = 1/4`.**  For a primitive `χ` mod `f ≥ 2` and a
finite set `Z` of zeros of `L(·,χ)` all at distance `≥ r₀` from `1`, with multiplicities `m`
dominated by the analytic ones and total mass `≤ J`,

    ∑_{ρ ∈ Z} m_ρ‖ρ−1‖^{−2}  ≤  C(r₀^{−2} + log(f+2)·r₀^{−1})  +  16·J.

The first summand is N3's `nearOne_invSq_sum_le` (Prachar's disc count spent dyadically) —
HB's inputs (2)+(3).  The second is **HB's input (1), the `|γ| ≥ 1` tail**: those zeros are
at distance `≥ 1/4` from `1`, so each costs at most `16·m_ρ`, and their total mass is the
Jensen count that `Salt.SW.LFunction_partialFraction` already exports (`≪ log(f(|t₀|+2))`,
i.e. `≪ L`).  Multiplied by HB's prefactor `aL^{−1}` this is `O(a)` — precisely Davenport
ch.14 (3), obtained from the disk geometry rather than re-proved. -/
theorem invSq_sum_split_le : ∃ C : ℝ, 0 < C ∧
    ∀ {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f), χ.IsPrimitive → 2 ≤ f →
      ∀ {r0 J : ℝ}, 0 < r0 → ∀ {Z : Finset ℂ} {m : ℂ → ℕ},
        (∀ ρ ∈ Z, r0 ≤ ‖ρ - 1‖) →
        (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) →
        (∀ ρ ∈ Z, (m ρ : ℝ) ≤ (Salt.SW.zeroMult χ ρ : ℝ)) →
        (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ J →
        ∑ ρ ∈ Z, (m ρ : ℝ) / ‖ρ - 1‖ ^ 2
          ≤ C * (1 / r0 ^ 2 + Real.log ((f : ℝ) + 2) / r0) + 16 * J := by
  classical
  obtain ⟨C, hC, hnear⟩ := nearOne_invSq_sum_le
  refine ⟨C, hC, ?_⟩
  intro f _inst χ hχ hf r0 J hr0 Z m hfl hzero hmz hJ
  set Zn : Finset ℂ := Z.filter (fun ρ => ‖ρ - 1‖ < 1 / 4) with hZn
  set Zf : Finset ℂ := Z.filter (fun ρ => ¬ (‖ρ - 1‖ < 1 / 4)) with hZf
  have hpart : ∑ ρ ∈ Z, (m ρ : ℝ) / ‖ρ - 1‖ ^ 2
      = (∑ ρ ∈ Zn, (m ρ : ℝ) / ‖ρ - 1‖ ^ 2) + ∑ ρ ∈ Zf, (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not Z _ _).symm
  -- the near part: Prachar, dyadically
  have hnearle : ∑ ρ ∈ Zn, (m ρ : ℝ) / ‖ρ - 1‖ ^ 2
      ≤ C * (1 / r0 ^ 2 + Real.log ((f : ℝ) + 2) / r0) := by
    have hdom : ∑ ρ ∈ Zn, (m ρ : ℝ) / ‖ρ - 1‖ ^ 2
        ≤ ∑ ρ ∈ Zn, (Salt.SW.zeroMult χ ρ : ℝ) / ‖ρ - 1‖ ^ 2 := by
      refine Finset.sum_le_sum fun ρ hρ => ?_
      have hρZ : ρ ∈ Z := (Finset.mem_filter.mp hρ).1
      have hρ0 : 0 < ‖ρ - 1‖ := lt_of_lt_of_le hr0 (hfl ρ hρZ)
      exact (div_le_div_iff_of_pos_right (by positivity)).mpr (hmz ρ hρZ)
    refine le_trans hdom (hnear χ hχ hf hr0 ?_ ?_ ?_)
    · intro ρ hρ; exact hfl ρ (Finset.mem_filter.mp hρ).1
    · intro ρ hρ; exact (Finset.mem_filter.mp hρ).2
    · intro ρ hρ; exact hzero ρ (Finset.mem_filter.mp hρ).1
  -- the far part: HB's `|γ| ≥ 1` tail, priced by the Jensen count
  have hfarle : ∑ ρ ∈ Zf, (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ 16 * J := by
    have hstep : ∀ ρ ∈ Zf, (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ 16 * (m ρ : ℝ) := by
      intro ρ hρ
      have hbig : (1 : ℝ) / 4 ≤ ‖ρ - 1‖ := not_lt.mp (Finset.mem_filter.mp hρ).2
      have hsq : (1 : ℝ) / 16 ≤ ‖ρ - 1‖ ^ 2 := by nlinarith [hbig]
      have hpos : (0 : ℝ) < ‖ρ - 1‖ ^ 2 := by nlinarith [hbig]
      rw [div_le_iff₀ hpos]
      nlinarith [hsq, Nat.cast_nonneg (α := ℝ) (m ρ)]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have hsub : ∑ ρ ∈ Zf, (m ρ : ℝ) ≤ ∑ ρ ∈ Z, (m ρ : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    have : ∑ ρ ∈ Zf, (m ρ : ℝ) ≤ J := le_trans hsub hJ
    linarith
  rw [hpart]; linarith

/-! ## §4 — the compose: `hcore`, then HB (3.3) with the slot filled -/

/-- HB's Lemma-3 rate in the differenced shape: `2 + 2/(σ′−1) + 4(σ′−σ)·Sinv + Rrem`.  At
`σ = 1 + L^{−1}`, `σ′ = 1 + aL^{−1}`, `Sinv ≍ L²(log η)^{−1}` and `Rrem = O(1)` this is
`O(1) + O(La^{−1}) + O(aL(log η)^{−1})` — HB (4.2)'s two error terms, which §3 of
`PretenseSumProof` balances at `a = (log η)^{1/2}`. -/
noncomputable def hbCoreRate (σ σ' Sinv Rrem : ℝ) : ℝ :=
  2 + 2 * (1 / (σ' - 1)) + 4 * (σ' - σ) * Sinv + Rrem

/-- **The rate at HB's operating points `σ = 1 + L^{−1}`, `σ′ = 1 + aL^{−1}`.**  With the
`(4.1)` error sum priced by the repulsion floor in the shape `Sinv ≤ Cs·L²(log η)^{−1}`
(which is what `invSq_sum_split_le` gives at `r₀ ≫ L^{−1}log η`),

    hbCoreRate  ≤  2 + Rrem  +  2·(L/a)  +  4Cs·(aL/(log η)),

which is HB (4.2)'s two error terms `O(La^{−1}) + O(aL(log η)^{−1})` exactly — the pair
`A/a + B·a` that `PretenseSumProof`'s §3 (`hb_rate_optimal`) shows is minimized at
`a = (log η)^{1/2}`. -/
theorem hbCoreRate_at_operating_point {Lp a ell Sinv Rrem Cs : ℝ}
    (hL : 0 < Lp) (ha : 1 ≤ a) (hell : 0 < ell) (hCs : 0 ≤ Cs)
    (hSinv : Sinv ≤ Cs * (Lp ^ 2 / ell)) :
    hbCoreRate (1 + 1 / Lp) (1 + a / Lp) Sinv Rrem
      ≤ 2 + Rrem + 2 * (Lp / a) + 4 * Cs * (a * Lp / ell) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hpre : (0 : ℝ) ≤ 4 * ((1 + a / Lp) - (1 + 1 / Lp)) := by
    have : (1 + a / Lp) - (1 + 1 / Lp) = (a - 1) / Lp := by ring
    rw [this]
    have : (0 : ℝ) ≤ (a - 1) / Lp := div_nonneg (by linarith) hL.le
    linarith
  have hmul : 4 * ((1 + a / Lp) - (1 + 1 / Lp)) * Sinv
      ≤ 4 * ((1 + a / Lp) - (1 + 1 / Lp)) * (Cs * (Lp ^ 2 / ell)) :=
    mul_le_mul_of_nonneg_left hSinv hpre
  have hval : 4 * ((1 + a / Lp) - (1 + 1 / Lp)) * (Cs * (Lp ^ 2 / ell))
      = 4 * Cs * ((a - 1) * Lp / ell) := by
    field_simp
    ring
  have hmono : 4 * Cs * ((a - 1) * Lp / ell) ≤ 4 * Cs * (a * Lp / ell) := by
    have hstep : (a - 1) * Lp / ell ≤ a * Lp / ell :=
      (div_le_div_iff_of_pos_right hell).mpr (by nlinarith [hL.le])
    nlinarith [hstep, hCs]
  have hinv : 2 * (1 / ((1 + a / Lp) - 1)) = 2 * (Lp / a) := by
    have : (1 + a / Lp) - 1 = a / Lp := by ring
    rw [this, one_div_div]
  rw [hbCoreRate, hinv]
  linarith

/-- **The rate at HB's optimum `a = (log η)^{1/2}`** — the paper's `L(log η)^{−1/2}`:

    hbCoreRate  ≤  2 + Rrem + (2 + 4Cs)·L·(log η)^{−1/2}.

Both error terms of (4.2) collapse onto `L/√ℓ` at `a = √ℓ`, which is the balance
`hb_rate_at_optimal_a` proves and `hb_rate_optimal` proves optimal. -/
theorem hbCoreRate_at_hb_optimum {Lp ell Sinv Rrem Cs : ℝ}
    (hL : 0 < Lp) (hell : 1 ≤ ell) (hCs : 0 ≤ Cs)
    (hSinv : Sinv ≤ Cs * (Lp ^ 2 / ell)) :
    hbCoreRate (1 + 1 / Lp) (1 + Real.sqrt ell / Lp) Sinv Rrem
      ≤ 2 + Rrem + (2 + 4 * Cs) * (Lp / Real.sqrt ell) := by
  have hell0 : (0 : ℝ) < ell := by linarith
  have hs : (0 : ℝ) < Real.sqrt ell := Real.sqrt_pos.mpr hell0
  have hs1 : (1 : ℝ) ≤ Real.sqrt ell := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hell
  have hmul : Real.sqrt ell * Real.sqrt ell = ell := Real.mul_self_sqrt hell0.le
  have hne : ell ≠ 0 := ne_of_gt hell0
  have hne' : Real.sqrt ell ≠ 0 := ne_of_gt hs
  refine le_trans (hbCoreRate_at_operating_point hL hs1 hell0 hCs hSinv) ?_
  have hcollapse : Real.sqrt ell * Lp / ell = Lp / Real.sqrt ell := by
    field_simp
    nlinarith [hmul]
  rw [hcollapse]
  have hfin : 2 + Rrem + 2 * (Lp / Real.sqrt ell) + 4 * Cs * (Lp / Real.sqrt ell)
      = 2 + Rrem + (2 + 4 * Cs) * (Lp / Real.sqrt ell) := by ring
  linarith

/-- **`hcore` DISCHARGED down to `Rrem`.**  N3's carried hypothesis, in the currency
`pretenseSum_le_series` consumes:

    vmPairS χ N σ  ≤  1/(σ−1) − 1/(σ−β₀) + hbCoreRate σ σ′ Sinv Rrem.

This is HB (4.2)+(4.3) added: the untwisted pole (4.3) from `vmPairS_le_pole`
(unconditional), the twisted estimate (4.2) from `neg_re_logDeriv_differenced`, whose
`s′`-side input is discharged internally by `neg_re_logDeriv_LFunction_le`.  Everything is
in the kernel except the five carried items listed in the module header — of which only
`hrem` is mathematics. -/
theorem vmPairS_le_hb_core {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f) (N : ℕ)
    {Z : Finset ℂ} {m : ℂ → ℕ} {σ σ' β₀ r0 Sinv Rrem : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hlt : σ ≤ σ') (hσ'2 : σ' ≤ 2) (hβ1 : β₀ < 1)
    (hβZ : (β₀ : ℂ) ∈ Z) (hmβ : 1 ≤ m (β₀ : ℂ))
    (hr0 : 0 < r0) (hσr : σ - 1 ≤ r0 / 2) (hσ'r : σ' - 1 ≤ r0 / 2)
    (hfloor : ∀ ρ ∈ Z.erase ((β₀ : ℂ)), r0 ≤ ‖ρ - 1‖)
    (hSinv : ∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv)
    (hrem : ‖(logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)
              - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) - ρ))
            - (logDeriv (DirichletCharacter.LFunction χ) (σ' : ℂ)
              - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ' : ℂ) - ρ))‖ ≤ Rrem) :
    vmPairS χ N σ ≤ 1 / (σ - 1) - 1 / (σ - β₀) + hbCoreRate σ σ' Sinv Rrem := by
  have hσ'1 : 1 < σ' := lt_of_lt_of_le hσ1 hlt
  have hs'top := neg_re_logDeriv_LFunction_le χ hσ'1 hσ'2
  have hdiff := neg_re_logDeriv_differenced (Lf := DirichletCharacter.LFunction χ)
    (Z := Z) (m := m) hσ1 hlt hβ1 hβZ hmβ hr0 hσr hσ'r hfloor hSinv hrem hs'top
  have hpole := vmPairS_le_pole χ N hσ1 hσ2
  have hβle : 1 / (σ' - β₀) ≤ 1 / (σ' - 1) := by
    apply one_div_le_one_div_of_le (by linarith); linarith
  rw [hbCoreRate]
  linarith

/-- **HB 1983, LEMMA 3 — the pretense sum, with the analytic core discharged.**  N3's
`pretenseSum_le_series` fired at `vmPairS_le_hb_core`:

    2·PretenseSum χ N  ≤  N^{σ−1}·( (1−β₀)/(σ−1)² + hbCoreRate σ σ′ Sinv Rrem ),

where `(1−β₀)/(σ−1)²` is the pole cancellation (`pole_cancel_le`, `≍ Lη^{−1}` at the
operating point) and `N^{σ−1} = N^{1/L} ≤ e^{500}` on the campaign window `N ≤ q^{500}`. -/
theorem pretenseSum_le_differenced {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f) (N : ℕ)
    {Z : Finset ℂ} {m : ℂ → ℕ} {σ σ' β₀ r0 Sinv Rrem : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hlt : σ ≤ σ') (hσ'2 : σ' ≤ 2) (hβ1 : β₀ < 1)
    (hβZ : (β₀ : ℂ) ∈ Z) (hmβ : 1 ≤ m (β₀ : ℂ))
    (hr0 : 0 < r0) (hσr : σ - 1 ≤ r0 / 2) (hσ'r : σ' - 1 ≤ r0 / 2)
    (hfloor : ∀ ρ ∈ Z.erase ((β₀ : ℂ)), r0 ≤ ‖ρ - 1‖)
    (hSinv : ∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv)
    (hrem : ‖(logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)
              - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) - ρ))
            - (logDeriv (DirichletCharacter.LFunction χ) (σ' : ℂ)
              - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ' : ℂ) - ρ))‖ ≤ Rrem) :
    2 * PretenseSum χ N
      ≤ (N : ℝ) ^ (σ - 1) * ((1 - β₀) / (σ - 1) ^ 2 + hbCoreRate σ σ' Sinv Rrem) :=
  pretenseSum_le_series χ N hσ1 hβ1.le
    (vmPairS_le_hb_core χ N hσ1 hσ2 hlt hσ'2 hβ1 hβZ hmβ hr0 hσr hσ'r hfloor hSinv hrem)

/-- **THE NODE, ASSEMBLED — HB (3.3) with Lemma 3's slot filled and its core discharged.**
N3's slot bridge `hb_lemma2_of_pretenseSum_le` fired at `pretenseSum_le_differenced`:

    S⁽²⁾ − S⁽¹⁾ ≤ Cmain·(x/z₀)
                   + Cmain·(x/log x)·e^{Aexp·z₀}·(N^{σ−1}((1−β₀)/(σ−1)² + Rate)/2)
                   + junk.

**No `PretenseSum` and no `hcore` remain.**  The surviving hypotheses are exactly:

* the transfer-side data of N3 — `hsq`, `hA`, `hres`, `hcoef` (unchanged);
* the operating-point arithmetic — `1 < σ ≤ 2`, `σ ≤ σ′ ≤ 2`, `β₀ < 1`, `0 < r₀`, and the
  two proximity conditions `σ − 1 ≤ r₀/2`, `σ′ − 1 ≤ r₀/2` (satisfied at HB's
  `σ = 1 + L^{−1}`, `σ′ = 1 + aL^{−1}` once `r₀ ≫ aL^{−1}`, which the Deuring–Heilbronn
  floor `r₀ ≫ L^{−1}log η` gives for `a = (log η)^{1/2}`);
* `hβZ`, `hmβ` — the Siegel zero is one of the disk zeros, with multiplicity ≥ 1 (an
  *export* defect of `LFunction_partialFraction`, not mathematics);
* `hfloor` — the Deuring–Heilbronn repulsion floor, supplied by N3's
  `one_sub_ceiling_le_dist_one` from the F-side artillery context;
* `hSinv` — the (4.1) error sum, priced unconditionally by `invSq_sum_split_le`;
* **`hrem`** — the partial fraction's remainder *difference*, Davenport ch.12 (17)'s `O(1)`.
  This is the single genuinely analytic item still owed, and it is blocked behind the same
  Borel–Carathéodory sup input `hsup` that `Salt/SW/BCBound.lean` flags. -/
theorem hb_lemma3_final {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f) (hsq : χ ^ 2 = 1)
    {A : Finset ℕ} (hA : CoprimeSupport f A) (x : ℝ) (N : ℕ) (Cmain z0 Aexp junk : ℝ)
    {Z : Finset ℂ} {m : ℂ → ℕ} {σ σ' β₀ r0 Sinv Rrem : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hlt : σ ≤ σ') (hσ'2 : σ' ≤ 2) (hβ1 : β₀ < 1)
    (hβZ : (β₀ : ℂ) ∈ Z) (hmβ : 1 ≤ m (β₀ : ℂ))
    (hr0 : 0 < r0) (hσr : σ - 1 ≤ r0 / 2) (hσ'r : σ' - 1 ≤ r0 / 2)
    (hfloor : ∀ ρ ∈ Z.erase ((β₀ : ℂ)), r0 ≤ ‖ρ - 1‖)
    (hSinv : ∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv)
    (hrem : ‖(logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)
              - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) - ρ))
            - (logDeriv (DirichletCharacter.LFunction χ) (σ' : ℂ)
              - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ' : ℂ) - ρ))‖ ≤ Rrem)
    (hres : overshootMajorant χ A
      ≤ Cmain * (x / z0)
        + Cmain * (x / Real.log x) * Real.exp (Aexp * z0) * PretenseSum χ N + junk)
    (hcoef : 0 ≤ Cmain * (x / Real.log x) * Real.exp (Aexp * z0)) :
    S2 χ A - S1 A
      ≤ Cmain * (x / z0)
        + Cmain * (x / Real.log x) * Real.exp (Aexp * z0)
          * ((N : ℝ) ^ (σ - 1) * ((1 - β₀) / (σ - 1) ^ 2 + hbCoreRate σ σ' Sinv Rrem) / 2)
        + junk := by
  refine hb_lemma2_of_pretenseSum_le χ hsq hA x N Cmain z0 Aexp junk _ hres hcoef ?_
  have h := pretenseSum_le_differenced χ N hσ1 hσ2 hlt hσ'2 hβ1 hβZ hmβ hr0 hσr hσ'r
    hfloor hSinv hrem
  linarith

end Salt.HB
