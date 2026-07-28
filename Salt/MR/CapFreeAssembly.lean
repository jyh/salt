/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.VkTwistLadder
import Salt.MR.SiegelBand
import Salt.MR.RHSGrade
import Salt.MR.M4Residue

/-!
# CFF-ASSEMBLY — THE ASSEMBLED CAP-FREE FLOOR (`CapFreeAssembly`)

Every analytic input to the cap-free datum floor is landed.  This file does the
**composition**: for EVERY Dirichlet character `χ mod q` in a finite modulus range `q ≤ Q`,
and every `X` past a named threshold,

  `CapFreeArm3.CapFreeFloor3 (lamChi χ) X`
    ( = `∀ v, |v| ≤ 3X → (1/32)·loglog X + 25 < 𝔻²(λ·χ̄, n^{iv}; X)`, STRICT ).

No new analysis; three landed suppliers, one case split, one threshold.

## THE CASE GEOMETRY (two cases, not four)

The design brief anticipated four classes (non-real / principal / real-nonprincipal-bulk /
real-nonprincipal-band).  **Two of the four merge away**, and the merge is a fact about the
landed statements, not a shortcut:

* `ChiFloor.chi_floor_of_order` at `k = 2` demands only `χ² = 1` — which the PRINCIPAL
  character satisfies (`1² = 1`).  So the principal bulk needs no separate ζ-drift
  derivation: `pretDistSq_chiPrin_ge` (the `p | q` correction, honest constant `1`) is
  already inside `chi_floor_of_order`, and `dist_one_floor_pow` is already the ζ-floor it
  consumes.  The `k = 2` arm therefore serves principal and real-nonprincipal alike.
* `SiegelBand.chi_floor_band_uniform` carries **no** `χ ≠ 1` hypothesis — its per-character
  input `SiegelArm.chi_Llower_band` covers `χ = 1` through
  `LFunction_band_lower_principal`.  So the band arm serves principal and non-principal
  alike too.

What remains is exactly:

| case | `v`-range | supplier | floor coefficient on `loglog X` |
|---|---|---|---|
| `χ² ≠ 1` | all `|v| ≤ 3X` | `capFreeFloor3_lamChi_unconditional` (VK-TWIST capstone) | `1/16` |
| `χ² = 1` | `1/2 ≤ |v|` | `chi_floor_of_order` at `k = 2` | `1/16` |
| `χ² = 1` | `|v| ≤ 1/2` | `chi_floor_band_uniform Q` | `1` |

**THE SPLIT POINT IS `1/2`, and it is forced from both sides.**  The `k = 2` arm's gate is
`1 ≤ |k·v| = |2v|`, i.e. `|v| ≥ 1/2` exactly; the band arm's range is `|t| ≤ 1`, which
strictly contains `|v| ≤ 1/2`.  The two ranges overlap on `1/2 ≤ |v| ≤ 1`, so there is no
gap and no crossover subtlety: the bulk arm is already strong enough at its own gate (at
`|v| = 1/2` the drift debit is `(3/4)loglog 4 + 5·logloglog 17`, an absolute constant), and
the band arm is used only where the bulk arm is undefined.

## THE MARGIN (why `1/16` beats `1/32` in both bulk arms)

At `k = 2` the floor is `[loglog X − (3/4)loglog(|2v|+3) − 5·logloglog(|2v|+16) − C
− ∑_{p|q,p≤X} 1/p] / 4`.  On the contour box `|v| ≤ 3X` the height terms are `loglog X + O(1)`
and `logloglog X + O(1)` (§1), so the bracket is `(1/4)loglog X − 5·logloglog X − O(1)` and
the quotient is `(1/16)loglog X − (5/4)logloglog X − O(1)` — **double** the demand `1/32`,
with the `logloglog X` and the `q`-content to be cleared by the threshold.  This is the same
`1/16`-vs-`1/32` margin the VK arm carries, arrived at by a completely different route.

⚠ **THE SIGN FLIP, KILL-CHECKED.**  `lam = fun _ => −1`, so
`𝔻²(λχ̄, n^{iv}) = ∑_{p≤X} (1 + Re(χ̄(p)p^{−iv}))/p` — the `1 + Re`, not the `1 − Re` that
`dist_one_floor_pow` floors.  The `k = 2` route is exactly what repairs the sign: squaring
sends `λ ↦ 1` and `n^{iv} ↦ n^{2iv}`, so the floored object is `∑(1 − Re χ₀(p)p^{−2iv})/p` at
the DOUBLED frequency, and `pretDistSq_pow_le` transfers it back at the cost `1/k² = 1/4`.
Concrete corner (`χ = χ₀ mod 1`, `v = 0`, which the BAND arm owns): the true value is
`∑_{p≤X} 2/p ≈ 2·loglog X`, the band floor claims `≥ loglog X − C` — consistent, with the
factor `2` of slack that the `1 + Re` sign is worth.  Second corner (`v` large, bulk arm):
true value `∑(1 + cos(v log p))/p` can dip to `≈ (1/4)loglog X` when `ζ(1+iv)` is small, and
the arm claims `≥ (1/16)loglog X` — consistent, and the `1/4` loss is the honest price of
the power route.

## THE `p | q` DEFICIT, PRICED

`primeDivSum q X = ∑_{p|q, p≤X} 1/p` is bounded by `q` outright (`primeDivSum_le_modulus`:
at most `q+1` prime divisors, each contributing `≤ 1/2`).  Crude, and deliberately so: the
bound is `X`-FREE, which is the only property the regime lever needs (flags, "regime
enlargement absorbs any `X`-independent debit").  It rides in-statement as `(1/4)·q`.

## THE THRESHOLD

One inequality serves all three arms (§4):

  `40·logloglog X + 32·( (1/8)log q + (1/4)q + vkDebitConst(vkEulerCorr q · vkTwistConst q)
                          + vkMidDebit q + K + 25 ) < loglog X`

with `K = K(Q) ≥ 0` the single assembled constant.  The `40·logloglog X` (rather than the VK
capstone's `32·logloglog X`) is the `(5/4)·32` the `k = 2` drift costs; it dominates the VK
demand because `logloglog X ≥ 0` past `X ≥ exp(exp 1)`.  Every summand is nonnegative there,
so the single threshold implies each arm's own.

**The threshold is `X`-dependent only through `logloglog X`** — the same shape the VK
capstone already carries, and the same shape the regime lever already absorbs.  Magnitudes:
`vkMidDebit q ≈ (1/4)e^{100}` forces `loglog X ≳ 2·10⁴⁴` (VT-7 would drop it to `~10³`);
the door's `U1` floor supplies `loglog X ≈ log Hhi ≥ 6.4·10⁶¹`, clearing it by ~17 orders.
`K(Q)` inherits `siegelBandB`'s ineffectivity (the EVT minimum, "POISON 2") — it is
`X`-free, and that is the whole argument.

## THE SUM-DATUM ADAPTER (the `lam` collision, flags `2e3b8fe`)

`Salt.MR.lam` is `fun _ => −1` — correct where `pretDistSq` reads it (primes) and NOWHERE
else (`lam 4 = −1` but `λ(4) = +1`).  The row consumer `ThmA2Rows.a2Rows_of_capfree3` takes
a datum `g` that is ALSO summed over integers, so it must be built from the honest
`M4Residue.liouvilleC`.  §5 lands `liouChi χ = liouvilleC · χ̄` and transports the whole
assembled floor onto it — `pretDistSq` reads primes only
(`RHSGrade.pretDistSq_congr_primes`), and `liouvilleC p = −1 = lam p` at every prime, so the
transport is an EQUALITY of distances, not an estimate.  Consumers that need the row's
1-boundedness side condition take `norm_liouChi_le_one`.

Source pins: `Salt/MR/CapFreeArm3.lean` (`CapFreeFloor3`), `Salt/MR/VkTwistLadder.lean`
(`capFreeFloor3_lamChi_unconditional`), `Salt/MR/ChiFloor.lean` (`chi_floor_of_order`,
`primeDivSum`), `Salt/MR/SiegelBand.lean` (`chi_floor_band_uniform`),
`docs/blueprints/flags.md` (VK-TWIST completion, the `lam` collision, SIEGEL-REGIME).
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the scale facts and the two box-drift bounds

Everything below runs past `X ≥ exp(exp 1)`, the scale floor the VK capstone already
demands.  It buys exactly three things: `X ≥ 8` (enough for `6X + 16 ≤ X²`), `log X ≥ e`
(so `loglog X ≥ 1`), and `logloglog X ≥ 0` (so the threshold's leading term is a debit and
never a credit). -/

/-- **The scale floor, unpacked.**  `exp(exp 1) ≤ X` gives `8 ≤ X`, `e ≤ log X`,
`1 ≤ loglog X` and `0 ≤ logloglog X`. -/
theorem cff_scale_facts {X : ℝ} (hX : Real.exp (Real.exp 1) ≤ X) :
    8 ≤ X ∧ Real.exp 1 ≤ Real.log X ∧ 1 ≤ Real.log (Real.log X)
      ∧ 0 ≤ Real.log (Real.log (Real.log X)) := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he2 : (7 : ℝ) < Real.exp 2 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  have he07 : (1.7 : ℝ) ≤ Real.exp 0.7 := by
    have := Real.add_one_le_exp (0.7 : ℝ); linarith
  have hsplit : Real.exp (2.7 : ℝ) = Real.exp 2 * Real.exp 0.7 := by
    rw [← Real.exp_add]; norm_num
  have h27 : (8 : ℝ) < Real.exp (2.7 : ℝ) := by
    rw [hsplit]; nlinarith [Real.exp_pos (2 : ℝ), Real.exp_pos (0.7 : ℝ)]
  have hmono : Real.exp (2.7 : ℝ) ≤ Real.exp (Real.exp 1) :=
    Real.exp_le_exp.mpr (by linarith)
  have hX8 : (8 : ℝ) ≤ X := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogX : Real.exp 1 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hlogXpos : (0 : ℝ) < Real.log X := by nlinarith [Real.exp_pos (1 : ℝ)]
  have hLL : (1 : ℝ) ≤ Real.log (Real.log X) :=
    (Real.le_log_iff_exp_le hlogXpos).mpr hlogX
  exact ⟨hX8, hlogX, hLL, Real.log_nonneg hLL⟩

/-- `log 2 ≤ 1` — the only numeric log the drift bounds spend. -/
private lemma cff_log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

/-- **DRIFT 1 — the `(3/4)loglog` term on the contour box.**  For `|v| ≤ 3X` past the scale
floor, `loglog(|2v| + 3) ≤ loglog X + log 2`.

The whole content is `|2v| + 3 ≤ 6X + 3 ≤ X²` (which needs only `X ≥ 8`), so the inner log
at most doubles and the outer log pays `log 2`.  Trap `T2` observed: the pretentious scale
stays `X`, never `3X`. -/
theorem cff_box_loglog {X v : ℝ} (hX : Real.exp (Real.exp 1) ≤ X) (hv : |v| ≤ 3 * X) :
    Real.log (Real.log (|2 * v| + 3)) ≤ Real.log (Real.log X) + Real.log 2 := by
  obtain ⟨hX8, hlogX, _, _⟩ := cff_scale_facts hX
  have hlogXpos : (0 : ℝ) < Real.log X := by nlinarith [Real.exp_pos (1 : ℝ)]
  have habs : |2 * v| = 2 * |v| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hbox : |2 * v| + 3 ≤ X ^ 2 := by
    rw [habs]; nlinarith [abs_nonneg v]
  have hpos : (0 : ℝ) < |2 * v| + 3 := by positivity
  have hgt1 : (1 : ℝ) < |2 * v| + 3 := by linarith [abs_nonneg (2 * v)]
  have h1 : Real.log (|2 * v| + 3) ≤ Real.log (X ^ 2) := Real.log_le_log hpos hbox
  have h2 : Real.log (X ^ 2) = 2 * Real.log X := by rw [Real.log_pow]; norm_num
  have hlpos : (0 : ℝ) < Real.log (|2 * v| + 3) := Real.log_pos hgt1
  have h3 : Real.log (Real.log (|2 * v| + 3)) ≤ Real.log (2 * Real.log X) :=
    Real.log_le_log hlpos (by linarith)
  have h4 : Real.log (2 * Real.log X) = Real.log 2 + Real.log (Real.log X) :=
    Real.log_mul (by norm_num) (ne_of_gt hlogXpos)
  linarith

/-- **DRIFT 2 — the `5·logloglog` term on the contour box.**  For `|v| ≤ 3X` past the scale
floor, `logloglog(|2v| + 16) ≤ logloglog X + log 2`.

Two applications of the same doubling: `|2v| + 16 ≤ 6X + 16 ≤ X²` gives
`loglog(|2v|+16) ≤ loglog X + log 2 ≤ 2·loglog X` (here `loglog X ≥ 1` is what is spent),
and one more `log` pays a second `log 2`. -/
theorem cff_box_logloglog {X v : ℝ} (hX : Real.exp (Real.exp 1) ≤ X) (hv : |v| ≤ 3 * X) :
    Real.log (Real.log (Real.log (|2 * v| + 16)))
      ≤ Real.log (Real.log (Real.log X)) + Real.log 2 := by
  obtain ⟨hX8, hlogX, hLL, _⟩ := cff_scale_facts hX
  have hlogXpos : (0 : ℝ) < Real.log X := by nlinarith [Real.exp_pos (1 : ℝ)]
  have hLLpos : (0 : ℝ) < Real.log (Real.log X) := by linarith
  have hlog2 := cff_log_two_le_one
  have habs : |2 * v| = 2 * |v| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hbox : |2 * v| + 16 ≤ X ^ 2 := by
    rw [habs]; nlinarith [abs_nonneg v]
  have hpos : (0 : ℝ) < |2 * v| + 16 := by positivity
  have h1 : Real.log (|2 * v| + 16) ≤ Real.log (X ^ 2) := Real.log_le_log hpos hbox
  have h2 : Real.log (X ^ 2) = 2 * Real.log X := by rw [Real.log_pow]; norm_num
  -- the inner log is `> 1` because `|2v| + 16 ≥ 16 > e`
  have he1 : Real.exp 1 < 16 := by linarith [Real.exp_one_lt_d9]
  have hinner : (1 : ℝ) < Real.log (|2 * v| + 16) := by
    have : Real.exp 1 < |2 * v| + 16 := by linarith [abs_nonneg (2 * v)]
    exact (Real.lt_log_iff_exp_lt hpos).mpr this
  have hinnerpos : (0 : ℝ) < Real.log (|2 * v| + 16) := by linarith
  have h3 : Real.log (Real.log (|2 * v| + 16)) ≤ Real.log (2 * Real.log X) :=
    Real.log_le_log hinnerpos (by linarith)
  have h4 : Real.log (2 * Real.log X) = Real.log 2 + Real.log (Real.log X) :=
    Real.log_mul (by norm_num) (ne_of_gt hlogXpos)
  have h5 : Real.log (Real.log (|2 * v| + 16)) ≤ 2 * Real.log (Real.log X) := by
    linarith
  have h6 : (0 : ℝ) < Real.log (Real.log (|2 * v| + 16)) := Real.log_pos hinner
  have h7 : Real.log (Real.log (Real.log (|2 * v| + 16)))
      ≤ Real.log (2 * Real.log (Real.log X)) := Real.log_le_log h6 h5
  have h8 : Real.log (2 * Real.log (Real.log X))
      = Real.log 2 + Real.log (Real.log (Real.log X)) :=
    Real.log_mul (by norm_num) (ne_of_gt hLLpos)
  linarith

/-! ## §2 — the `p | q` deficit, bounded `X`-freely -/

/-- **The `p | q` deficit is at most `q`.**  `primeDivSum q X = ∑_{p|q, p≤X} 1/p`: the index
set injects into `q.primeFactors ⊆ [0, q]`, so there are at most `q + 1` terms, each at most
`1/2`, and `(q+1)/2 ≤ q` for `q ≥ 1`.

Crude on purpose.  The only property any consumer needs is that the bound is `X`-FREE — the
regime lever absorbs `X`-independent debits and nothing else. -/
theorem primeDivSum_le_modulus {q : ℕ} (hq : q ≠ 0) (X : ℝ) : primeDivSum q X ≤ (q : ℝ) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hsub : (Finset.range (⌊X⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ p ∣ q)
      ⊆ q.primeFactors := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Nat.mem_primeFactors.mpr ⟨hp.2.1, hp.2.2, hq⟩
  have hstep : primeDivSum q X ≤ ∑ p ∈ q.primeFactors, (1 : ℝ) / (p : ℝ) := by
    unfold primeDivSum
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => ?_)
    positivity
  have hhalf : ∑ p ∈ q.primeFactors, (1 : ℝ) / (p : ℝ)
      ≤ ∑ _p ∈ q.primeFactors, (1 : ℝ) / 2 := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    exact one_div_le_one_div_of_le (by norm_num) hp2
  have hconst : ∑ _p ∈ q.primeFactors, (1 : ℝ) / 2
      = (q.primeFactors.card : ℝ) * (1 / 2) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcardN : q.primeFactors.card ≤ q + 1 := by
    have hsub2 : q.primeFactors ⊆ Finset.range (q + 1) := by
      intro p hp
      rw [Finset.mem_range]
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.dvd_of_mem_primeFactors hp)
      omega
    have := Finset.card_le_card hsub2
    rwa [Finset.card_range] at this
  have hcard : (q.primeFactors.card : ℝ) ≤ (q : ℝ) + 1 := by
    have : ((q.primeFactors.card : ℕ) : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast hcardN
    push_cast at this; linarith
  have : (q.primeFactors.card : ℝ) * (1 / 2) ≤ (q : ℝ) := by nlinarith
  linarith [hstep, hhalf, hconst.le]

/-! ## §3 — the three arms

Each arm is stated POINTWISE in the frequency `v` (never as a `CapFreeFloor3`), so the
assembly in §4 can split on `v` inside the floor's own `∀ v`. -/

/-- **ARM 1 (bulk, `χ² = 1`) — the `k = 2` floor on the contour box.**  For every character
with `χ² = 1` (principal INCLUDED), every `X` past the scale floor and every frequency with
`1/2 ≤ |v| ≤ 3X`:

  `(1/16)·loglog X − (5/4)·logloglog X − (1/4)·q − C ≤ 𝔻²(λ·χ̄, n^{iv}; X)`

with `C` uniform in `q`, `χ`, `X`, `v`.  `chi_floor_of_order` at `k = 2` (`Even 2`, `2 ≠ 0`,
`χ² = 1`), the two box drifts of §1, and `primeDivSum_le_modulus`.

The coefficient `1/16` is `(1 − 3/4)/k²` at `k = 2` — double the `CapFreeFloor3` demand. -/
theorem chi_floor_real_bulk :
    ∃ C : ℝ, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (X v : ℝ), q ≠ 0 → χ ^ 2 = 1 →
      Real.exp (Real.exp 1) ≤ X → 1 / 2 ≤ |v| → |v| ≤ 3 * X →
        (1 / 16) * Real.log (Real.log X)
            - (5 / 4) * Real.log (Real.log (Real.log X))
            - (1 / 4) * (q : ℝ) - C
          ≤ pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨C₀, hC₀⟩ := chi_floor_of_order
  refine ⟨(C₀ + 23 / 4) / 4, ?_⟩
  intro q χ X v hq hχ2 hX hv2 hv3
  obtain ⟨hX8, hlogX, hLL, _⟩ := cff_scale_facts hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hXe : Real.exp 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact le_trans (Real.exp_le_exp.mpr h1) hX
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hkt : (1 : ℝ) ≤ |((2 : ℕ) : ℝ) * v| := by
    rw [hcast, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hmain := hC₀ q χ 2 X v (by norm_num) ⟨1, by norm_num⟩ hχ2 hXe hkt
  rw [hcast] at hmain
  have hsq : ((2 : ℝ)) ^ 2 = 4 := by norm_num
  rw [hsq] at hmain
  have hA := cff_box_loglog (X := X) (v := v) hX hv3
  have hB := cff_box_logloglog (X := X) (v := v) hX hv3
  have hP := primeDivSum_le_modulus (q := q) hq X
  have hlog2 := cff_log_two_le_one
  linarith

/-- **ARM 2 (band, all `χ`) — the uniform Siegel-band floor.**  A restatement of
`SiegelBand.chi_floor_band_uniform` with the scale hypothesis at this file's floor
`X ≥ exp(exp 1)` and the range at the split point `|v| ≤ 1/2 ≤ 1`.

Coefficient `1` on `loglog X` — no `k²`, no `primeDivSum`; the debit `C(Q)` is `X`-free and
carries the ineffective Siegel constant, confined here and nowhere else. -/
theorem chi_floor_band_arm (Q : ℕ) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X v : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ 1 / 2 →
        Real.log (Real.log X) - C ≤ pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨C, hC⟩ := chi_floor_band_uniform Q
  refine ⟨C, ?_⟩
  intro q _ χ X v hq hX hv
  have hXe : Real.exp 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact le_trans (Real.exp_le_exp.mpr h1) hX
  exact hC q χ hq X v hXe (by linarith)

/-! ## §4 — THE ASSEMBLED FLOOR

The threshold is carried EXPLICITLY, in-statement (law #253).  Every summand inside the
`32·(…)` is nonnegative past the scale floor, and `logloglog X ≥ 0`, so the single
inequality implies each arm's own demand:

* VK arm: `32·(logloglog X + (1/8)log q + vkDebitConst C + vkMidDebit q + K + 25) < loglog X`
  — implied because `40 ≥ 32` on a nonnegative `logloglog X` and `(1/4)q ≥ 0`;
* bulk arm: `40·logloglog X + 8q + 32·K_bulk + 800 < loglog X` — implied because
  `K ≥ K_bulk` and the VK debits are nonnegative;
* band arm: `(32/31)·(K_band + 25) < loglog X` — implied because `K ≥ K_band ≥ 0` and
  `32/31 ≤ 32`.
-/

/-- **THE ASSEMBLED CAP-FREE FLOOR, at the `λ·χ̄` datum** (`capFreeFloor3_all_chi`).

For every finite modulus range `Q` there is a single constant `K ≥ 0` such that: for every
`q ≤ Q`, EVERY Dirichlet character `χ mod q` — real or complex, principal or not — and every
`X ≥ exp(exp 1)` satisfying

  `40·logloglog X + 32·( (1/8)log q + (1/4)q
        + vkDebitConst(vkEulerCorr q · vkTwistConst q) + vkMidDebit q + K + 25 ) < loglog X`,

the twisted datum `λ·χ̄` satisfies `CapFreeArm3.CapFreeFloor3` — i.e. STRICTLY
`(1/32)·loglog X + 25 < 𝔻²(λχ̄, n^{iv}; X)` for every `|v| ≤ 3X`.

Three landed suppliers, one `χ²`-split and one `|v|`-split; no new analysis.  `K` is
`X`-free and `q`-free (it depends on `Q` alone), which is exactly what makes the threshold
regime-absorbable. -/
theorem capFreeFloor3_all_chi (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + K + 25)
        < Real.log (Real.log X) →
        CapFreeFloor3 (lamChi χ) X := by
  obtain ⟨Kvk, hvk⟩ := capFreeFloor3_lamChi_unconditional
  obtain ⟨Kbulk, hbulk⟩ := chi_floor_real_bulk
  obtain ⟨Kband, hband⟩ := chi_floor_band_arm Q
  refine ⟨max 0 (max Kvk (max Kbulk Kband)), le_max_left _ _, ?_⟩
  set K : ℝ := max 0 (max Kvk (max Kbulk Kband)) with hKdef
  have hK0 : 0 ≤ K := le_max_left _ _
  have hKvk : Kvk ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKbulk : Kbulk ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hKband : Kband ≤ K :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  intro q _ χ X hq hX hthr
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  -- the nonnegative debits inside the threshold
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hC1 : (1 : ℝ) ≤ vkEulerCorr q * vkTwistConst q := by
    nlinarith [one_le_vkEulerCorr q, one_le_vkTwistConst (q := q)]
  have hvkD : (0 : ℝ) ≤ vkDebitConst (vkEulerCorr q * vkTwistConst q) :=
    vkDebitConst_nonneg hC1
  have hvkM : (0 : ℝ) ≤ vkMidDebit q := vkMidDebit_nonneg q
  by_cases hsq : χ ^ 2 = 1
  · -- REAL (principal included): split the box at the frequency `1/2`
    intro v hv
    by_cases hband2 : |v| ≤ 1 / 2
    · -- the Siegel band, coefficient `1`
      have h := hband q χ X v hq hX hband2
      linarith
    · -- the `k = 2` bulk arm, coefficient `1/16`
      have hvbig : 1 / 2 ≤ |v| := le_of_lt (not_le.mp hband2)
      have h := hbulk q χ X v hq0 hsq hX hvbig hv
      linarith
  · -- NON-REAL: the VK-TWIST capstone covers the whole box at once
    refine hvk q χ X hsq hX ?_
    linarith

/-- **The assembled floor at the `X` box** (`capFreeFloor_all_chi`).  The same conclusion at
`CapFreeArm.CapFreeFloor` (`|v| ≤ X`), for consumers still on the un-minted convention.  A
wrapper via `capFreeFloor_of_capFreeFloor3`. -/
theorem capFreeFloor_all_chi (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + K + 25)
        < Real.log (Real.log X) →
        CapFreeFloor (lamChi χ) X := by
  obtain ⟨K, hK0, hK⟩ := capFreeFloor3_all_chi Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ X hq hX hthr
  obtain ⟨hX8, _, _, _⟩ := cff_scale_facts hX
  exact capFreeFloor_of_capFreeFloor3 (by linarith) (hK q χ X hq hX hthr)

/-- **The assembled constant, named** (`cffK`).  `siegelBandB`'s genre: the regime-cut arm
takes a `Bfun : ℕ → ℝ` parameter slot, and this is the inhabitant for the cap-free demand.
`Classical.choose` is spent once, here — the constant is an opaque existential by
construction (it inherits `siegelBandB`'s EVT minimum). -/
def cffK (Q : ℕ) : ℝ := Classical.choose (capFreeFloor3_all_chi Q)

theorem cffK_nonneg (Q : ℕ) : 0 ≤ cffK Q :=
  (Classical.choose_spec (capFreeFloor3_all_chi Q)).1

/-- The defining property of `cffK` — `capFreeFloor3_all_chi`'s body at the chosen
constant. -/
theorem cffK_spec (Q : ℕ) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + cffK Q + 25)
        < Real.log (Real.log X) →
        CapFreeFloor3 (lamChi χ) X :=
  (Classical.choose_spec (capFreeFloor3_all_chi Q)).2

/-! ## §5 — THE SUM-DATUM ADAPTER (the `lam` collision)

`lam = fun _ => −1` is the pretentious DATUM, correct only at primes; the row consumer
`ThmA2Rows.a2Rows_of_capfree3` also SUMS its datum over integers, so it must be fed the
honest `liouvilleC`.  `pretDistSq` reads its left datum at primes only
(`RHSGrade.pretDistSq_congr_primes`), and `liouvilleC p = −1 = lam p` there, so the two
data have EQUAL pretentious distances and the floor transports verbatim. -/

/-- **The honest sum-side datum** `liouChi χ = λ·χ̄`, built from `M4Residue.liouvilleC` (the
ℂ-cast of `ArithmeticFunction.liouville`) rather than from `lam`.  Prime-equal to `lamChi χ`
and correct at every integer: `liouChi χ 4 = χ̄(4)`, while `lamChi χ 4 = −χ̄(4)`. -/
def liouChi {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ → ℂ :=
  fun n => liouvilleC n * (starRingEnd ℂ) (χ (n : ZMod q))

/-- The two data agree at every prime (`liouvilleC p = −1 = lam p`). -/
theorem lamChi_eq_liouChi_prime {q : ℕ} (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : p.Prime) :
    lamChi χ p = liouChi χ p := by
  unfold lamChi liouChi lam
  rw [liouvilleC_prime hp]

/-- **THE ADAPTER (an EQUALITY, not an estimate).**  `𝔻²(λχ̄, g; X) = 𝔻²(liouvilleC·χ̄, g; X)`
for every twist `g` and every scale. -/
theorem pretDistSq_liouChi_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (g : ℕ → ℂ) (X : ℝ) :
    pretDistSq (liouChi χ) g X = pretDistSq (lamChi χ) g X :=
  pretDistSq_congr_primes (fun _p hp => (lamChi_eq_liouChi_prime χ hp).symm) X

/-- The sum-side datum is 1-bounded (at `n = 0` it vanishes, as `liouvilleC` does). -/
theorem norm_liouChi_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖liouChi χ n‖ ≤ 1 := by
  unfold liouChi
  rw [norm_mul, Complex.norm_conj]
  have h1 := liouvilleC_norm_le_one n
  have h2 := DirichletCharacter.norm_le_one χ ((n : ℕ) : ZMod q)
  nlinarith [norm_nonneg (liouvilleC n), norm_nonneg (χ ((n : ℕ) : ZMod q))]

/-- The floor transports from the pretentious datum to the sum-side datum. -/
theorem capFreeFloor3_liouChi_of_lamChi {q : ℕ} (χ : DirichletCharacter ℂ q) {X : ℝ}
    (h : CapFreeFloor3 (lamChi χ) X) : CapFreeFloor3 (liouChi χ) X := by
  intro v hv
  rw [pretDistSq_liouChi_eq]
  exact h v hv

/-- **THE ASSEMBLED FLOOR AT THE ROW'S OWN DATUM** (`capFreeFloor3_liouChi_all`).  The shape
`ThmA2Rows.a2Rows_of_capfree3` consumes: its `g`-slot datum is summed over integers, so it
must be `liouvilleC`-built; its `hg` side condition is `norm_liouChi_le_one`. -/
theorem capFreeFloor3_liouChi_all (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + K + 25)
        < Real.log (Real.log X) →
        CapFreeFloor3 (liouChi χ) X := by
  obtain ⟨K, hK0, hK⟩ := capFreeFloor3_all_chi Q
  exact ⟨K, hK0, fun q _ χ X hq hX hthr =>
    capFreeFloor3_liouChi_of_lamChi χ (hK q χ X hq hX hthr)⟩

end Salt.MR
