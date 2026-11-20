/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RiderTrace
import Salt.MR.RegisterCompose
import Salt.MR.FlatDesignBound
import Salt.MR.SocketLogFrame

/-!
# `V7B` — ⟦CS-THREAD⟧ the `e^{-100} ≤ cs` rider of `logChowla2_ineffective_v6`, DISCHARGED
and carried up the mint chain as a conjunct

`RegisterCompose.logChowla2_ineffective_v6` carries five inner hypotheses.  The first,
`Real.exp (-100) ≤ cs`, is a rider on a constant the theorem's own `∃`-prefix mints, and
`RiderTrace` already pinned in the kernel what that constant IS:

```
cs = min (min (c_vk / (2·K₄)) (c₀ / (2·Cκ))) (1/10) = 3.716·10^{-11}
```

against `e^{-100} = 3.72·10^{-44}` — **33 orders of room** (`cs_closed_form_ge_exp_neg_hundred`,
`RiderTrace.lean:132`).  What `RiderTrace` left open was the CARRY: the closed form is visible
only inside the mint's proof, and every hop above it exports `0 < cs` alone, so the floor could
not be read at the terminal.

This file closes that gap.  The route is the one `RiderTrace`'s closing note names — **conjunct
carry**, the same genre as `NumeralKq`'s `Kq ≤ 126848/10^8` twins — run over the two remaining
leaves and the nine hops above them:

```
§1  per_pair_contour_floored                       1/10^9 ≤ c₀     (off RiderTrace §4)
§2  halaszPrimesChiGated_of_price_floored          e^{-100} ≤ c    (THE MINT)
§3  halasz_primes_chi_pair_of_gates_bounded_cs     ⌉
    halaszPrimesChi_holds_gated_bounded_cs         │
    halaszPrimesChi_pointwise_of_gates_bounded_cs  │  six pass-throughs,
    usetGChi_window_meansq_gated_family_..._cs     │  bodies verbatim + one conjunct
    usetGChi_row_exit_perChi_perBlock_bounded_cs   │
    m4_rowChi_capstone_perBlock_bounded_cs         ⌋
§4  m4_hcap_at_door_perBlock_L_gk_bounded_khoist_cs
    m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs
    s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree   ⟵ the rider is CONSUMED here
    logChowla2_witnessed_scale_flat_..._cqhoist_csfree         ⟵ what a `v7` mint reads
```

⟦WHY THE CARRY IS THE ONLY ROUTE⟧ every statement in the chain is ANTITONE in `cs` (the
decay constant sits in `exp(−cs·log P/D₄)` at the bottom and in `420·L·… ≤ cs·(log Q)²` at
the top: shrinking `cs` weakens), so an `∃ cs, 0 < cs ∧ P cs` can always be re-witnessed at a
SMALLER `cs` and never at a larger one.  A LOWER bound therefore cannot be manufactured above
the mint by any monotonicity argument — it has to be exported from the leaves, which is what
§1–§2 do and what §3–§4 forward.

⟦WHERE THE RIDER DIES⟧ `S16ComposeV4.s16_capGate_supply_L_gk_sharpT0` spends `e^{-100} ≤ cs`
at exactly one field — `gate := s16_capGrid_gate_cs hcs …` (`S16Budget.lean`).  §4's
`…_csfree` twins feed it the carried conjunct instead of an antecedent, so the hypothesis
leaves the statement.

**PURELY ADDITIVE.**  No landed declaration is touched; every twin sits beside its original,
and `logChowla2_ineffective_v6` is byte-untouched.  Minting `v7` off §4's terminal is a
separate node.
-/

namespace Salt.MR

/-! ## §0 — THE FLOOR, AT THE LEAVES' OWN VALUES -/

/-- **⟦THE `cs` FLOOR, GENERALISED TO THE LEAF BOUNDS⟧** `RiderTrace`'s
`cs_closed_form_ge_exp_neg_hundred` pins the floor at the two leaf LITERALS `c_vk = 1/10^8`
and `c₀ = 1/10^9`; the mint only ever knows the leaves through INEQUALITIES (`c_vk` is the
call site's literal, `c₀` is `per_pair_contour`'s existential).  Both slots are monotone, so
the pinned numeral carries. -/
theorem cs_floor_of_leaves {c_vk c₀ : ℝ} (h8 : 1 / 10 ^ 8 ≤ c_vk) (h9 : 1 / 10 ^ 9 ≤ c₀) :
    Real.exp (-100) ≤ min (min (c_vk / (2 * K₄)) (c₀ / (2 * Cκ))) (1 / 10) := by
  have hK : (0 : ℝ) < 2 * K₄ := by rw [K₄]; positivity
  have hC : (0 : ℝ) < 2 * Cκ := by rw [Cκ]; positivity
  have h1 : (1 / 10 ^ 8 : ℝ) / (2 * K₄) ≤ c_vk / (2 * K₄) := by
    rw [div_le_div_iff₀ hK hK]; nlinarith only [h8, hK]
  have h2 : (1 / 10 ^ 9 : ℝ) / (2 * Cκ) ≤ c₀ / (2 * Cκ) := by
    rw [div_le_div_iff₀ hC hC]; nlinarith only [h9, hC]
  exact le_trans cs_closed_form_ge_exp_neg_hundred (min_le_min (min_le_min h1 h2) le_rfl)

end Salt.MR

namespace Salt.MR

open scoped BigOperators
open Complex MeasureTheory Set ArithmeticFunction
open scoped LSeries.notation

/-! ## §1 — RUNG 4: the per-pair contour, `c₀`'s floor carried

`per_pair_contour` passes `shifted_edge_price_strip`'s `c_vk` through verbatim, so
`RiderTrace.shifted_edge_price_strip_bounded`'s `1/10^9 ≤ c_vk` survives the whole assembly.
Since O13-e row 211 the proof is `per_pair_contour_of`, shared with `per_pair_contour`
(`HalaszPrimesCore.lean:2827`), at the bounded strip; the new conjunct is the strip's own. -/

section V7BPerPair
open Complex Salt.SW Salt.Vk Metric intervalIntegral

/-- **THE PER-PAIR CONTOUR BOUND WITH THE FLOORED `c_vk`**: there are `c_vk C₁ C₂ C₃ T₀` with
`1/10^9 ≤ c_vk` such that for `T₀ ≤ T`, `2 ≤ P`, `|u| ≤ 2T`, the twisted prime window
`∑' n, Λ(n)·n^{iu}·primeWindow P n` differs from `windowKernel P 1 u` by at most
`C₁·P·e^{−(c_vk/2)·log P / D₃}·D₄ + C₂·P·log P / T + C₃·D₄·P / T²`, where
`D₃ = (log (5T+1))^{3/4}·(log log (5T+1))^3` and `D₄` has the fourth power. Route:
`per_pair_contour_of` at `shifted_edge_price_strip_bounded` — the rectangle from
`σ₀ = 1 − (c_vk/2)/D₃` to `c = 1 + 1/log P` with `|Im| ≤ 3T`, zero-free by that strip's margin
(which carries the `1/10^9` floor), the pole residue, the four edges, and
`sum_vonMangoldt_cline_bound` on the right edge. Consumed by
`halaszPrimesChiGated_of_price_floored` (§2). -/
theorem per_pair_contour_floored :
    ∃ (c_vk C₁ C₂ C₃ T₀ : ℝ), 0 < c_vk ∧ 1 / 10 ^ 9 ≤ c_vk ∧
      0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 3 ≤ T₀ ∧
      ∀ (T P u : ℝ), T₀ ≤ T → 2 ≤ P → |u| ≤ 2 * T →
        ‖(∑' n, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
              - windowKernel P 1 u‖
          ≤ C₁ * P * Real.exp (-(c_vk / 2) * Real.log P
                / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                    * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)))
              * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                  * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ))
            + C₂ * P * Real.log P / T
            + C₃ * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                  * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) * P / T ^ 2 := by
  obtain ⟨c_vk, CE, T₀s, hc_vk0, hc_vk9, hCE0, hT₀s3, -, hmargin, hstrip⟩ :=
    shifted_edge_price_strip_bounded
  obtain ⟨C₁, C₂, C₃, T₀, hC₁, hC₂, hC₃, hT₀, h⟩ :=
    per_pair_contour_of c_vk CE T₀s hc_vk0 hCE0 hT₀s3 hmargin hstrip
  exact ⟨c_vk, C₁, C₂, C₃, T₀, hc_vk0, hc_vk9, hC₁, hC₂, hC₃, hT₀, h⟩

end V7BPerPair

end Salt.MR

namespace Salt.MR

open scoped BigOperators
open Complex MeasureTheory Set ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

/-! ## §2 — THE MINT, WITH THE FLOOR EXPORTED

`halaszPrimesChiGated_of_price` is where `cs` is born, as
`min (min (c_vk/(2·K₄)) (c₀/(2·Cκ))) (1/10)`.  This twin asks the call site's own literal
`1/10^8 ≤ c_vk` instead of bare positivity, reads `1/10^9 ≤ c₀` off §1, and exports the floor.
Since O13-e row 213: `halaszPrimesChiGated_of_price_of`, the base's (`PortAssembly.lean:1148`). -/

/-- **A1 — THE PAIR DUAL, ASSEMBLED.**  `HalaszPrimesChiGated` from the twisted edge price
(`TwistedWindowPriceGated`, at any admissible constants) and the landed untwisted per-pair
price (`per_pair_contour`).  This is stone C's residue discharged: the socket's diagonal term
is `P`, not `φ(q)·P`.

The decay constant is `c = min(c_vk/(2K₄), c₀/(2Cκ), 1/10)`: the first two match the two
prices' contour depths against the socket's `D₄(qT)` (via `D4_5T1_le_D4` and `D3_5T1_le`,
then `logDn_mono` for `D₄(T) ≤ D₄(qT)`), the third is what makes `1/T ≤ exp(−c log P/D₄(qT))`
at `P ≤ T^10`.  The `(log qT)²` factor absorbs `D₅(5T+1)` and `D₄(5T+1)` (`D5_5T1_le`,
`D4_5T1_le`) and — through `√P ≤ P·exp(−c log P/D₄(qT))` — the Euler debit. -/
theorem halaszPrimesChiGated_of_price_floored {c_vk C₁ C₂ C₃ T₀e : ℝ}
    (hc_vk8 : 1 / 10 ^ 8 ≤ c_vk) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃)
    (hT₀e : Real.exp (Real.exp 100) ≤ T₀e)
    (hprice : TwistedWindowPriceGated c_vk C₁ C₂ C₃ T₀e) :
    ∃ C c T₀ : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (-100) ≤ c ∧ 3 ≤ T₀ ∧
      HalaszPrimesChiGated c_vk C c T₀ := by
  have hc_vk : 0 < c_vk := lt_of_lt_of_le (by norm_num) hc_vk8
  obtain ⟨c₀, E₁, E₂, E₃, T₀z, hc₀, hc₀9, hE₁, hE₂, hE₃, hT₀z, hpp⟩ :=
    per_pair_contour_floored
  obtain ⟨C, T₀, hC, hT₀, h⟩ :=
    halaszPrimesChiGated_of_price_of hc_vk hC₁ hC₂ hC₃ hT₀e hprice hc₀ hE₁ hE₂ hE₃ hT₀z hpp
  have hK₄0 : 0 < K₄ := by rw [K₄]; positivity
  have hCκ0 : 0 < Cκ := by rw [Cκ]; positivity
  exact ⟨C, _, T₀, hC, lt_min (lt_min (by positivity) (by positivity)) (by norm_num),
    cs_floor_of_leaves hc_vk8 hc₀9, hT₀, h⟩

end Salt.MR

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §3 — THE SIX PASS-THROUGHS

`NumeralKq`'s `_bounded` family, each twin re-run with the `cs` floor riding beside the `Kq`
ceiling.  Bodies verbatim from `NumeralKq.lean:207-607`; the only edits are the extra
conjunct in the `∃`-prefix, the extra name in each `obtain`/`refine` tuple, and the callee
re-pointed at its own `_cs` twin. -/

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open Complex MeasureTheory Set ArithmeticFunction DirichletCharacter in
open scoped LSeries.notation in
/-- **⟦cs-FLOORED TWIN⟧** `halasz_primes_chi_pair_of_gates_bounded`
+ the conjunct `Real.exp (-100) ≤ cs` (§2's floor, carried).
the port's pair row; pass-through. -/
theorem halasz_primes_chi_pair_of_gates_bounded_cs {C₁ C₂ C₃ T₀e : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃)
    (hT₀e : Real.exp (Real.exp 100) ≤ T₀e)
    (hprice : TwistedWindowPriceGated (1 / 10 ^ 8) C₁ C₂ C₃ T₀e) :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (-100) ≤ c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
        (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * Complex.I) * chiBarCoeff q r.1 a n‖ ^ 2
          ≤ C * (P + (ℰ.card : ℝ) * P
                  * Real.exp (-c * Real.log P
                      / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                          * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
                  * (Real.log ((q : ℝ) * T)) ^ 2)
              / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C, c, T₀, hC, hc, hcf, hT₀, hgated⟩ :=
    halaszPrimesChiGated_of_price_floored (by norm_num) hC₁ hC₂ hC₃ hT₀e hprice
  obtain ⟨Kq, Ks, hKq, hKqb, hKs, hreg⟩ := twisted_rect_zero_free_siegel_bounded
  refine ⟨C, c, max T₀ T₀e, Kq, Ks, hC, hc, hcf, le_trans hT₀ (le_max_left _ _), hKq, hKqb,
    hKs, ?_⟩
  intro q hq T P hT hP hPT10 hG1 hG2 hG3 hG4 ℰ hws hsub S hS a
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hTfloor : Real.exp (Real.exp 100) ≤ T := le_trans hT₀e (le_trans (le_max_right _ _) hT)
  -- the `A`-instantiation that makes stone C's own `hAq` free
  set A : ℝ := 1 + Real.log (20000 * (vkStripConst q + 8104)) / 100 with hAdef
  have hCq1 : (1 : ℝ) ≤ vkStripConst q := one_le_vkStripConst
  have hlogA0 : (0 : ℝ) ≤ Real.log (20000 * (vkStripConst q + 8104)) :=
    Real.log_nonneg (by linarith)
  have hA1 : (1 : ℝ) ≤ A := by rw [hAdef]; linarith
  have hAq : Real.log (20000 * (vkStripConst q + 8104)) ≤ A * 100 := by
    rw [hAdef]; linarith
  have hAabs : A + 7 ≤ Real.log (Real.log (5 * T + 1)) := by rw [hAdef]; linarith [hG2]
  exact hgated q T P hTT₀ hP hPT10 hG1
    (fun ψ hψ1 => hreg q ψ hψ1 A T hA1 hTfloor hAq hAabs hG3 hG4) ℰ hws hsub S hS a

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open Complex DirichletCharacter in
/-- **⟦cs-FLOORED TWIN⟧** `halaszPrimesChi_holds_gated_bounded`
+ the conjunct `Real.exp (-100) ≤ cs` (§2's floor, carried).
the gated socket row; pass-through. -/
theorem halaszPrimesChi_holds_gated_bounded_cs :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (-100) ≤ c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
        (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * Complex.I) * chiBarCoeff q r.1 a n‖ ^ 2
          ≤ C * (P + (ℰ.card : ℝ) * P
                  * Real.exp (-c * Real.log P
                      / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                          * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
                  * (Real.log ((q : ℝ) * T)) ^ 2)
              / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C₁, C₂, C₃, T₀e, hC₁, hC₂, hC₃, hT₀e, hprice⟩ := twisted_window_price_gated_holds
  exact halasz_primes_chi_pair_of_gates_bounded_cs hC₁ hC₂ hC₃ hT₀e hprice

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open Complex DirichletCharacter in
/-- **⟦cs-FLOORED TWIN⟧** `halaszPrimesChi_pointwise_of_gates_bounded`
+ the conjunct `Real.exp (-100) ≤ cs` (§2's floor, carried).
the pointwise socket; pass-through. -/
theorem halaszPrimesChi_pointwise_of_gates_bounded_cs :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (-100) ≤ c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T : ℝ), T₀ ≤ T →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      HalaszPrimesChi C c q T := by
  obtain ⟨C, c, T₀, Kq, Ks, hC, hc, hcf, hT₀, hKq, hKqb, hKs, hrow⟩ :=
    halaszPrimesChi_holds_gated_bounded_cs
  refine ⟨C, c, T₀, Kq, Ks, hC, hc, hcf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ T hT hG1 hG2 hG3 hG4 P hP hPT10 ℰ hws hsub S hS a
  exact hrow q T P hT hP hPT10 hG1 hG2 hG3 hG4 ℰ hws hsub S hS a

set_option maxHeartbeats 2400000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open MeasureTheory in
/-- **⟦cs-FLOORED TWIN⟧** `usetGChi_window_meansq_gated_family_perBlock_bounded`
+ the conjunct `Real.exp (-100) ≤ cs` (§2's floor, carried).
the χ-summed window mean square, gated; pass-through. -/
theorem usetGChi_window_meansq_gated_family_perBlock_bounded_cs :
    ∃ Cs cs T₀ Kq Ks : ℝ, 0 < Cs ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (f : ℕ → ℂ), (∀ n : ℕ, ‖f n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (T VJ V L X : ℝ), 1 ≤ T → 1 < (q : ℝ) * T →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T →
        30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * T)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → T ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        -- ⟦THE PER-`(q,T)` FLOOR — what the socket's discharge costs⟧
        T₀ ≤ T →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * T) → Real.log ((q : ℝ) * T) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ),
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q,
          thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, H ≤ (j : ℝ)) →
        (∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * T) →
        (∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * T) / Real.log (ramQbase H P j)) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ T ^ 10) →
        (∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L) →
        (∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase H P j)) ^ 2) →
      ∀ Rbd : ℝ, 0 ≤ Rbd →
      ∀ 𝔄 : Set (DirichletCharacter ℂ q × ℝ),
        (∀ χ : DirichletCharacter ℂ q, MeasurableSet {t : ℝ | (χ, t) ∈ 𝔄}) →
        (∀ r ∈ 𝔄, r.2 ∈ Set.Icc (-T) T) →
        𝔄 ⊆ UsetGChi q f Pseq Qseq Hseq αseq J →
        (∀ j ∈ ramI H P Q, ∀ r ∈ 𝔄,
          ‖ramR H N Xd P Q j (chiBarCoeff q r.1 b) r.2‖ ≤ Rbd) →
      ∀ E : ℝ, (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
          ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
        (∑ χ : DirichletCharacter ℂ q,
            ∫ t in {t : ℝ | (χ, t) ∈ 𝔄}, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (∑ j ∈ ramI H P Q,
                  (5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ)
                        * (1 + Real.log (2 * T))
                      * (∑ m ∈ Finset.Icc 1 (Ms j),
                          ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
                    + 81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2))
            + 2 * E := by
  obtain ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hcsf, hT₀, hKq, hKqb, hKs, hpt⟩ :=
    halaszPrimesChi_pointwise_of_gates_bounded_cs
  refine ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hcsf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 T VJ V L X hT1 hqT hP3 hPQ
    hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL
    hgate Rbd hRbd 𝔄 hAm hAsub hUA hR E herr
  exact usetGChi_window_meansq_of_socket_family_perBlock hCs hcs q f hf1 Pseq Qseq Hseq αseq
    J Jb hJb1 hJbJ hH2seq hα0 T VJ V L X (hpt q T hT₀T hG1 hG2 hG3 hG4) hT1 hqT hP3 hPQ hQT
    hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hlogT1 hTL hLe hlogV
    H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate Rbd hRbd
    𝔄 hAm hAsub hUA hR E herr

set_option maxHeartbeats 2400000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open MeasureTheory in
/-- **⟦cs-FLOORED TWIN⟧** `usetGChi_row_exit_perChi_perBlock_bounded`
+ the conjunct `Real.exp (-100) ≤ cs` (§2's floor, carried).
the per-χ row exit; pass-through (only `Cs` rescales). -/
theorem usetGChi_row_exit_perChi_perBlock_bounded_cs :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (Tann VJ V L X : ℝ), 1 ≤ Tann → 1 < (q : ℝ) * Tann →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann →
        30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * Tann)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → Tann ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        T₀ ≤ Tann →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * Tann + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * Tann) → Real.log ((q : ℝ) * Tann) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ),
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q,
          thinBundleGChi ((q : ℝ) * Tann) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, H ≤ (j : ℝ)) →
        (∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * Tann) →
        (∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * Tann) / Real.log (ramQbase H P j)) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ Tann ^ 10) →
        (∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L) →
        (∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase H P j)) ^ 2) →
      ∀ Rbd : ℝ, 0 ≤ Rbd →
      ∀ t₁ : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ j ∈ ramI H P Q,
          ∀ t ∈ seamAnn X Tann \ seamBall X (t₁ χ),
            ‖ramR H N Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd) →
      ∀ E : ℝ, (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
          ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
      ∀ KS : ℝ,
        (∀ j ∈ ramI H P Q,
          5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
              * (∑ m ∈ Finset.Icc 1 (Ms j),
                  ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
            ≤ KS) →
        2 ≤ ⌊H * Real.log (P : ℝ)⌋₊ →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (seamAnn X Tann \ seamBall X (t₁ χ))
            ∩ UsetG (chiBarCoeff q χ c) Pseq Qseq Hseq αseq J,
            ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (((ramI H P Q).card : ℝ) * KS
                  + 54 * Cq * Rbd ^ 2 * H ^ 2
                      / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E := by
  obtain ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hcsf, hT₀, hKq, hKqb, hKs, hfam⟩ :=
    usetGChi_window_meansq_gated_family_perBlock_bounded_cs
  refine ⟨3 * Cs / 2, cs, T₀, Kq, Ks, by linarith, hcs, hcsf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X hT1 hqT hP3
    hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL
    hgate Rbd hRbd t₁ hR E herr KS hKS hj₀ χ
  -- ⟦the Σ_χ exit at the row's own pair set⟧
  have hsum := hfam q c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X
    hT1 hqT hP3 hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T
    hG1 hG2 hG3 hG4 hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3
    hBT hκ30 hBT10 hWL hgate Rbd hRbd
    (rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁)
    (measurableSet_rowPairSetG_fibre q c Pseq Qseq Hseq αseq J X Tann t₁)
    (rowPairSetG_sub q c Pseq Qseq Hseq αseq J X Tann t₁)
    (rowPairSetG_subset_UsetGChi q c Pseq Qseq Hseq αseq J X Tann t₁)
    (fun j hj r hr => hR r.1 j hj r.2 hr.1) E herr
  -- ⟦the per-χ read: every fibre integral is nonnegative, so one is at most the sum⟧
  have hnn : ∀ χ' ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      (0 : ℝ) ≤ ∫ t in {t : ℝ | (χ', t) ∈ rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁},
        ‖spoly N (chiBarCoeff q χ' a) t‖ ^ 2 := by
    intro χ' _
    exact setIntegral_nonneg
      (measurableSet_rowPairSetG_fibre q c Pseq Qseq Hseq αseq J X Tann t₁ χ')
      (fun _ _ => by positivity)
  have hsingle := Finset.single_le_sum hnn (Finset.mem_univ χ)
  -- ⟦the ⟦ii-8⟧ block price, per block⟧
  have hprice := usetGChi_block_price_perBlock H N Xd P Q Ms b X Tann KS Cs Rbd hCs.le hRbd
    hj₀ hKS
  have hcard0 : (0 : ℝ) ≤ 4 * ((ramI H P Q).card : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hprice hcard0
  rw [rowPairSetG_fibre] at hsingle
  linarith

set_option maxHeartbeats 3200000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open MeasureTheory in
/-- **⟦cs-FLOORED TWIN⟧** `m4_rowChi_capstone_perBlock_bounded`
+ the conjunct `Real.exp (-100) ≤ cs` (§2's floor, carried).
the per-χ capstone row, per block; pass-through. -/
theorem m4_rowChi_capstone_perBlock_bounded_cs :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (Tann VJ V L X : ℝ), 1 ≤ Tann → 1 < (q : ℝ) * Tann →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann →
        30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * Tann)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → Tann ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        T₀ ≤ Tann →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * Tann + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * Tann) → Real.log ((q : ℝ) * Tann) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
        -- ⟦THE `X`-SIDE FRAME⟧
        2 ≤ H83 X theta293 → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann →
      ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleGChi ((q : ℝ) * Tann) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, H83 X theta293 ≤ (j : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 3 ≤ ramQbase (H83 X theta293) P j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          (ramQbase (H83 X theta293) P j : ℝ) ≤ (q : ℝ) * Tann) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          30 ≤ Real.log ((q : ℝ) * Tann) / Real.log (ramQbase (H83 X theta293) P j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          (ramQbase (H83 X theta293) P j : ℝ) ≤ Tann ^ 10) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          Real.log (ramQbase (H83 X theta293) P j) ≤ L) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase (H83 X theta293) P j)) ^ 2) →
      ∀ (Rbd CR : ℝ), 0 ≤ Rbd → Rbd ≤ CR * (Real.log X) ^ (-rho293) →
        1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
      ∀ t₁ : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ j ∈ ramI (H83 X theta293) P Q,
          ∀ t ∈ seamAnn X Tann \ seamBall X (t₁ χ),
            ‖ramR (H83 X theta293) N Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd) →
      ∀ KS : ℝ, 0 ≤ KS →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
              * (∑ m ∈ Finset.Icc 1 (Ms j),
                  ‖ramRcoeff (H83 X theta293) N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
            ≤ KS) →
        32 * (Real.log X) ^ (2 + 2 * theta293) * KS ≤ (Real.log X) ^ (-theta293) →
      ∀ (E EP2 εr : ℝ), 0 ≤ εr → 8640 ≤ (Real.log X) ^ εr →
        12 * EP2 ≤ (Real.log X) ^ (-theta293 + εr) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
          ‖ramErr (H83 X theta293) N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
      ∀ S : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann →
          |t - t₁ χ| ≤ seamRad X → ∀ m : ℕ, m ≤ N →
            ‖spolyA (chiBarCoeff q χ a) t m‖ ≤ S χ * m / (1 + |t - t₁ χ|)) →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 8 * S χ ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X (t₁ χ))
                ∩ seamTtotG (chiBarCoeff q χ c) Pseq Qseq Hseq αseq J,
                ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + εr)) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, hexit⟩ :=
    usetGChi_row_exit_perChi_perBlock_bounded_cs
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X hT1 hqT hP3
    hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV hH2 hLXe hL4 hTgate
    N Xd P Q Ms a b cf hcf1 hPlow hQ0 hQhigh hM hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate
    Rbd CR hRbd hRgrade hCqgate t₁ hR KS hKS0 hKS hKSgate E EP2 εr hεr habs hEP2 hErow herr
    hXN hN2 hsupp S hSup χ
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hH0 : (0 : ℝ) ≤ H83 X theta293 := by linarith
  have hHeq : H83 X theta293 = (Real.log X) ^ theta293 := by rw [H83]
  have hTann0 : (0 : ℝ) ≤ Tann := by linarith
  have hfl := floor_pin X P hL4 hPlow
  -- ⟦the per-χ `𝒰` exit, per block⟧
  have hU := hexit q c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X
    hT1 hqT hP3 hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T
    hG1 hG2 hG3 hG4 hlogT1 hTL hLe hlogV (H83 X theta293) hH2 N Xd P Q Ms a b cf hcf1 hM
    hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate Rbd hRbd t₁ hR E herr KS hKS hfl.1 χ
  -- ⟦the block leg, priced at `θ₂₉₃`⟧
  have hmain := balance_priced_main X (H83 X theta293) Cq CR KS Rbd P Q hL0 hH0
    (ramI_card_le_pin X P Q hQ0 hQhigh hLXe) (le_of_eq hHeq) hfl.2
    hCq.le hKS0 hRbd hRgrade hKSgate hCqgate
  -- ⟦Lemma 12's error leg, absorbed⟧
  have hrem := rem_priced X Tann (H83 X theta293) εr EP2 E hL1 hX0 hTann0
    (le_of_eq hHeq.symm) habs hEP2 hErow
  -- ⟦the balance⟧
  have hbal := hUG_balance (chiBarCoeff q χ a) (chiBarCoeff q χ c) N Pseq Qseq Hseq αseq J
    X Tann (t₁ χ) εr _ _ hεr hL1 hX0 hTgate hU hmain hrem
  exact prop_A3_T1_row_split_weightedG (chiBarCoeff q χ a) N (chiBarCoeff q χ c) Pseq Qseq
    Hseq αseq J X Tann (t₁ χ) (S χ) _ hL0.le hTann0 hX0 hXN hN2
    (chiBarCoeff_seam_supp χ hsupp) (hSup χ) hbal

end Salt.MR

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla
open scoped BigOperators

/-! ## §4 — THE FOUR TOP HOPS, AND THE RIDER'S DEATH

Hops 7–8 carry the conjunct through `RegisterCompose`'s `∀K`-hoisted twins.  Hop 9 is where
the rider is SPENT: `s16_capGate_supply_L_gk_sharpT0`'s `hcs` argument is fed the carried
conjunct instead of an antecedent, so `Real.exp (-100) ≤ cs` leaves the statement.  Hop 10
forwards the now-hypothesis-free shape through the flat terminal — **this is the declaration a
`v7` mint reads in place of
`logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist`.**

Bodies verbatim from `RegisterCompose`'s four theorems
`m4_hcap_at_door_perBlock_L_gk_bounded_khoist`, `m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist`,
`s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist` and
`logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist`. -/

set_option maxHeartbeats 3200000 in
-- Same cause as the landed original: one application of a ~45-binder capstone.
/-- ⟦cs-FLOORED TWIN⟧ `RegisterCompose.m4_hcap_at_door_perBlock_L_gk_bounded_khoist`
+ the conjunct `Real.exp (-100) ≤ cs`.  Body verbatim off §3's capstone twin. -/
theorem m4_hcap_at_door_perBlock_L_gk_bounded_khoist_cs :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (K : ℕ) (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 : ℝ),
              DoorCapBasePerBlock_L_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf (2 * T)
                VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, hcapstone⟩ :=
    m4_rowChi_capstone_perBlock_bounded_cs
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro K R M cU ε hcU hfam H L q j A s hb χ T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, hd⟩ :=
    hfam H L q j A s hb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hlogX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := hd.logX_four
    linarith
  have hres := hcapstone q cU hcU (calP (AdoorL M) (s13GK K M))
    (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M)) (mrAlpha (1 / 12)) 2 Jb
    hd.Jb_lo hd.Jb_hi hd.Hseq_two hd.alpha_nonneg
    (2 * T) VJ V Lr (((A + s : ℕ)) : ℝ) hd.Tann_one hd.qTann_one hd.P_three hd.PQ hd.QTann
    hd.kappa30Q hd.loglog5 hd.VJ_bound η εd hd.alpha_eta hd.eta_half hd.Tann_X hd.X_pos
    hd.debit hd.logX_pos hd.q_logX hd.V_one hd.V_inv hd.T0_Tann hd.floor1 hd.floor2
    hd.floor3 hd.floor4 hd.logqT_one hd.logqT_L hd.L_exp hd.logV_L
    hd.H83_two hd.logX_exp hd.logX_four hTgate
    (2 * (A + s)) Xd P Q Mr (winCutH (A + s) (doorCoeffU_L_gk K M)) b cf hd.cf_one hd.P_low
    hd.Q_pos hd.Q_high hd.range hd.budget hd.Hj hd.B3 hd.BT hd.kappa30 hd.BT10 hd.WL hd.gate
    Rbd CR hd.Rbd_nonneg hd.Rbd_grade hd.Cq_gate
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ)) hd.Rbd_binder
    KS hd.KS_nonneg hd.KS_binder hd.KS_gate E EP2 (ε (A + s)) hd.epsr_nonneg hd.abs8640
    hd.EP2_gate hd.E_row hd.E_binder (doorCap_hXN (A + s)) (doorCap_hN2 (A + s))
    (fun n hn => doorRowDatumU_supp0_L_gk K M (A + s) hn)
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ))
    (m4_hSup_door_at_zero q (winCutH (A + s) (doorCoeffU_L_gk K M)) (2 * (A + s)) hlogX1) χ
  rw [chiBarCoeff_doorRowDatum_L_gk] at hres
  simpa using hres

set_option maxHeartbeats 3200000 in
-- Same cause as the landed original: the wire's own statement re-elaborates.
/-- ⟦cs-FLOORED TWIN⟧ `RegisterCompose.m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist`
+ the conjunct `Real.exp (-100) ≤ cs`.  Body verbatim. -/
theorem m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ Real.exp 100 ∧ 0 < Ks ∧
      ∀ (K : ℕ) (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
              G2Scaffold.DoorCapErrWS_L_gk K M (A + s) q Xd P Q b cf (2 * T) E Mtail
                ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                      ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                        (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU_L_gk K M)))
                        (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                    → DoorCapBasePerBlock_L_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                        (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, hwire⟩ :=
    m4_hcap_at_door_perBlock_L_gk_bounded_khoist_cs
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq,
    le_trans hKqb kq_closed_form_le_exp_hundred, hKs, ?_⟩
  intro K R M cU ε hc1 hcapWS
  refine hwire K R M cU ε hc1 ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (G2Scaffold.m4_capE_at_door_L_gk K hws)⟩

set_option maxHeartbeats 3200000 in
-- Same cause as the landed original: the eighteen-slot `hcapWS` family re-elaborates.
/-- **⟦THE RIDER DIES HERE⟧** `RegisterCompose.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist`
with `Real.exp (-100) ≤ cs` MOVED from an antecedent of the inner implication to a CONJUNCT of
the `∃`-prefix — i.e. from something the caller must supply to something this theorem delivers.
`s16_capGate_supply_L_gk_sharpT0`, the only consumer of the rider, is fed the carried conjunct.
Body otherwise verbatim. -/
theorem s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree :
    ∃ Cq cs T₀ Kq Ks C : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ Real.exp 100 ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      ∀ K : ℕ,
        (Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ (R : ChowlaRegime) (M : ℕ), 1 ≤ M → loglogFloor50 ≤ R.Hlo →
          T₀ ≤ Real.exp (Real.sqrt ((R.Hlo : ℕ) : ℝ) / 2) →
          (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → s13BlockFloor_L_gk K M ≤ A + s) →
          S16CofactorSupply_L_gk K Cq R M → S16BaseScaleCap96_L_gk K R M →
          S15CrossingBound_L_gk K R M) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hwire⟩ :=
    m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs
  obtain ⟨C, hC0, hC40, hband⟩ := m4_tail_mass_at_band_bounded
  refine ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40, ?_⟩
  intro K hKq hKs R M hM hfl hT₀ hblk hcof hcap
  -- ⟦THE RIDER, SPENT FROM THE PREFIX⟧ `hcsf` is the carried conjunct, not an antecedent
  have hgate := s16_capGate_supply_L_gk_sharpT0 K hM hfl hcsf hblk hT₀ hKq hKs hC0 hC40
    (fun _ => le_rfl) hcap hcof
  refine hwire K R M liouvilleC (fun _ => theta293 - 1 / 500) liouvilleC_norm_le_one ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨P, Q, Rrad, Rbd, CR, EP2, hg⟩ := hgate H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨hq, hA, hNd, hlogX0, hpow, hexp⟩ := socketLogFrame_facts s hsb hg.logX_eight
  have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
  have hT1 : (1 : ℝ) < 2 * T := by linarith
  exact doorCapBundle_at_workingPoint_perBlock_L_gk K hband hM hNd hq hg hT1 hThi hTll

/-! ### hop 10 — ⟦THE FLAT TERMINAL, cs-FREE⟧ -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 3200000 in
-- Same cause as the landed original: the hoisted prefix plus the three window discharges
-- re-elaborate the terminal's conclusion.
/-- **⟦THE cs-FREE FLAT TERMINAL⟧**
`RegisterCompose.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist` with the `cs`
rider gone from the inner implication and delivered as a prefix conjunct instead.  **This is
the declaration a `v7` mint reads**: replaying `logChowla2_ineffective_v6`'s body against it
drops `Real.exp (-100) ≤ cs` from the terminal's surviving list, leaving four inner items.
Body otherwise verbatim. -/
theorem logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_winU Awin) :
    ∃ (ε : ℚ) (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧
        ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
          K ≤ 170000000 * flatDoorM A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          T₀ ≤ Real.exp (Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ) / 2) →
          Real.exp (-100) ≤ Ks →
          ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            (S16CofactorSupply_L_gk K Cq R (flatDoorM A) →
              S16BaseScaleCap96_L_gk K R (flatDoorM A) →
                ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, hcondU⟩ :=
    flat_conditional_uniform_win_xceil_kwide_khoist Awin hband
  -- ⟦THE CROSSING CONSTANTS, HOISTED ABOVE THE LEVER⟧ — §1's twin
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40,
    hsupplyU⟩ := s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  obtain ⟨_Ct0, -, -, hcond0⟩ := hcondU 0
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond0 (max 162 (budgetAFlat (ε : ℝ) β)) (le_max_left _ _) (le_max_right _ _)
  have hzero : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := xceilRiderStrict_zero ε
  obtain ⟨R0, hR0eps, -, -, -, -, -⟩ :=
    hbody0 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) hzero le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hε2q
  have hεR : (1 : ℝ) / 500 ≤ (ε : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hεpin
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  have hsupply := hsupplyU K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA26 hAwin hAge hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge
  refine ⟨fun hopq => flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hx0win hopq hT₀ hKs g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g hg (flatCap_le_flatWitFloor hCapLe)
  obtain ⟨hdes, hbaseceil, hwin⟩ :=
    flat_des_base_width hA26 hβ hεR hε2 hε hεpin hAge hopq hHlo hRtow
  refine ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  obtain ⟨hM1, heps, hlo, hfl⟩ := regime_flat_head_facts hReps hHlo hεpin hA26
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win (c := 1) hA26 K hKw (by norm_num) (by norm_num) (by simp) hδ₀ (by simpa using hδpin) hKc hKcb
    hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win (by simpa using heps) hlo hwin
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk K (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel hKw
    (hsupply hKqb hKs R (flatDoorM A) hM1 hfl (by rw [hHlo]; exact hT₀) hblk hcof hcapsc)


/-! ## §5 — ⟦THE DELIVERABLE⟧ `v6` WITH THE `cs` RIDER GONE

Body verbatim from `logChowla2_ineffective_v6`, with the terminal re-pointed at §4's
`_csfree` twin and the rider's arrow removed.  This is NOT the `v7` mint — four inner items
remain — it is the demonstration that the carry reaches `v6`'s own statement. -/

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 3200000 in
-- Same cause as `v5`: the `∃`-prefix and the four window discharges re-elaborate the
-- conclusion under the raised lever, now with the co-factor supply discharged inside.
/-- **⟦`v6` WITH RIDER 1 DISCHARGED⟧** (`logChowla2_ineffective_v6_csarm`) — `v6` verbatim
with the `cs` arrow GONE from the inner implication.

⟦WHAT CHANGED⟧ `v6`'s first surviving inner item, `Real.exp (-100) ≤ cs`, was a rider on a
constant `v6`'s own `∃`-prefix mints — and `RiderTrace` had already pinned that constant's
closed form (`3.716·10^{-11}`, 33 orders above `e^{-100}`).  §1–§4 carry the floor from the
two leaves that produce it (`c_vk = 1/10^8`, `c₀ = 1/10^9`) up all nine hops as a CONJUNCT, so
the terminal now DELIVERS `Real.exp (-100) ≤ cs` instead of asking for it.  The list of inner
items drops from five to **four**: `T₀`-sharp, `Ks`, `XCeilRiderStrict ε g`, the `K_vt`
cushion.  Outer: still nothing.

`v6` is byte-untouched and remains citable; this is the form V7-E's mint consumes (composing
with V7-C's `_T0arm` arm leaves three).  V7-E is HELD and is not minted here. -/
theorem logChowla2_ineffective_v6_csarm (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) →
        Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
              + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
            ≤ Real.log (R.Hhi : ℝ) / 4 →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  -- ⟦THE REPAIRED CO-FACTOR SUPPLY⟧ its four Skolem constants, minted outside everything
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ := cofkR_cofactorSupply_L_gk
  obtain ⟨Awin, -, hband⟩ := s16_bandLaneWinL_holdsU
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ :=
    logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree Awin hband
  -- ⟦THE DESIGN CONSTANT⟧ chosen above all four fixed constants AND above the co-factor
  -- threshold — legal exactly because `C_q` is now minted BEFORE the lever (§1)
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
      (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))) := ⟨_, rfl⟩
  have hA162 : (162 : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)
  have hA₀A : A₀ ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)
  have hAwinA : Awin ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    rw [hAdef]
    exact le_trans (le_max_right (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
      (le_max_left _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    rw [hAdef]
    exact le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
    Salt.MR.x0_le_exp_exp_of_four_le hx0nn hx0A
  have hopq : Hopq ≤ flatDesignBase A := le_flatDesignBase_of_le hopqA
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, hCt, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hKw
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A, hKvt0, ?_⟩
  intro hT₀ hKs g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKs g hg
  refine ⟨R, hReps, by rw [hHlo]; exact hbase hopq, hRg, hRtow, hdes, hwin, ?_⟩
  intro hKvtcush
  -- ⟦ITEM 3, DISCHARGED⟧ the base-scale cap at `K = KlevF A`
  -- ⟦RULING 9, DISCHARGED⟧ the co-factor supply at the repaired ladder
  obtain ⟨heps500, hxceil, hM1, heps500R, h518, hfl, hlo, hthrgate⟩ :=
    regime_flat_supply_facts hReps hHlo hRx hdes hεpin hA162 hthrA
  have hcofsupply : S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) :=
    hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush
  exact hfire2 hcofsupply
    (s16_baseScaleCap96_L_at_klevF hA26 (flatDoorM_one_le hA26) heps500 hxceil hwin)

end Salt.MR

end
