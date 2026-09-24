/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.Gate
import Salt.Fulcrum.Dichotomy

/-!
# Siegel–Walfisz from a fixed standoff — the DESIGN-TIER STATEMENT FREEZE

⛔ **Nothing in this file bears on twin primes.** Siegel–Walfisz (`siegelWalfisz_holds`,
`Gate.lean:150`) is already an unconditional theorem of this corpus. What this file changes,
once its wave lands, is the PROOF TERM's dependence on one ineffective input, and nothing else.

## Status: PROVED 2026-09-24 (statements frozen at `f8e81b76`, token-identical)

Provenance: GOLDMINE lane (a) pull 1 (`docs/QUEUE.md` item 15, O13; the sweep brief
`2026-09-24-math-GOLDMINE-sweep1.md` §3), the helm's routing of 2026-09-24 03:07 and its
gate-write of 07:26, and kill-check 1 answered kernel-side by the non-author reader
(`2026-09-24-h2c-KC1-goldmine/`): the closures of `psi1_char_bound`, `psi1_trivchar_bound`
and `psi1_transfer` reach NONE of `siegel_theorem` / `siegel_L_one_exceptional` /
`L1_lower_siegel`. The only exceptional-zero module in any of their closures is
`Salt.SW.LandauPage` — Landau's per-modulus one-exceptional-zero theorem, EFFECTIVE,
`c₁ = 1/5000`.

## The demand, measured

`psi1AP_main_bound` (`Fold.lean:157`) reads Siegel's theorem at ONE site, `Fold.lean:167`:
`siegel_theorem ε` at `ε = 1/(4C)`, used only in the exceptional branch to get
`Cₛ/f^ε ≤ 1 − β₁`, hence `f^ε ≤ (log x)^{1/4}` and the kill of the residue term. Its one
code consumer is `siegelWalfisz_holds` at `Gate.lean:154`, which is parametric in the main
bound at that line. A FIXED standoff `1 − β₁ ≥ c/log f` serves every `(A, C)` at once: with
`f ≤ (log x)^C`, `x^{−(1−β₁)} ≤ exp(−c·log x/(C·log log x))`, which beats every power of
`log x`. The ∀ε family collapses to one strength.

## The label (h2c's closure facts, the helm's wording, 2026-09-24 07:26)

**"Siegel–Walfisz's only INEFFECTIVE dependence on Siegel-zero theory is one standoff
constant"** — and Landau's per-modulus theorem (`LandauPage.lean`, effective) sits beside it
in the closure. NEVER "effective Siegel–Walfisz": under `¬F` the standoff `c` is
`min(c_iso(Q₀), 1/C)` and `c_iso` is nonconstructive (`ContinuousAt.eventually_ne`, the
fulcrum Pass-2 caveat, owed at `Fulcrum/Basic.lean:169`). The theorems below remove Siegel's
`C(ε)`; they do not make `c` computable.

## What makes the claim checkable — a Prop cannot see it

`Salt.BV.SiegelWalfisz` is the same Prop either way and `#print axioms` is the same three
either way. The claim is a property of the PROOF TERM: the transitive constant closure of
`siegelWalfisz_of_standoff` must exclude `siegel_theorem`, `siegel_L_one_exceptional` and
`L1_lower_siegel`, with `siegelWalfisz_holds` REACHING `siegel_theorem` (proof-only) as the
positive control. That certificate is the committed module `Salt.SW.StandoffCert` — a check
that can FAIL, never a `#print axioms` line alone. It is STRICT: a `sorryAx` in a closure is an
error, so its green is non-vacuous by construction. `siegelWalfisz_of_standoff`'s closure still
holds `Salt.SW.LandauPage` (Landau's per-modulus theorem, effective) — as the label says.

## Kill-checks: status and owners (the non-author read's C6, 2026-09-24)

* KC1 (a second Siegel path): ANSWERED — NOT REACHED, kernel-side (h2c, above).
* KC2 (is the standoff strong enough at SMALL conductors, `f = 3` included; no `f`-dependence
  left in the eventual-in-`x` absorption): **OPEN — owner: the refuter pass.**
* KC3 (is it new; no survey run; any prose follows the claim law, "first in any PUBLIC
  artifact as of <survey date>", and credits the textbook statement): **OPEN — owner: the
  refuter pass.**
* KC4 (the honest scope of "effective"): the label above.

## Token checks (order clause 7): the wave changes no landed statement

* `NoSiegelZerosAt` is the body of `Salt.TwinBar.NoSiegelZeros` at one `c`, byte-for-byte
  after `∃ c : ℝ, 0 < c ∧` — witnessed by `noSiegelZeros_iff_exists_at := Iff.rfl`, which is
  a CHECK (it fails to elaborate if the body drifts), not a proof of the candidate.
* The conclusion of `psi1AP_main_bound_of_standoff` is the TYPE of `psi1AP_main_bound`, and
  the conclusion of `siegelWalfisz_of_standoff` is the TYPE of `siegelWalfisz_holds`, each
  compared as `Expr`s by `StandoffCert`'s `#assert_conclusion_is` (syntactic, not defeq).
-/

open Complex DirichletCharacter
open Filter Asymptotics Salt.LS ArithmeticFunction
open scoped Topology

namespace Salt.SW

/-- **The standoff at ONE fixed `c`** — the body of `Salt.TwinBar.NoSiegelZeros` with its
leading `∃ c, 0 < c ∧` removed. Every real primitive quadratic character `χ ≠ 1` mod `q > 1`
has its real zeros below `1 − c/log q`. The `c` is the one strength Siegel–Walfisz reads. -/
def NoSiegelZerosAt (c : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    1 < q → χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
    ∀ β : ℝ, LFunction χ β = 0 → β < 1 →
      β ≤ 1 - c / Real.log q

/-- **Token check, not a proof:** `NoSiegelZerosAt` is exactly the body of `NoSiegelZeros`.
If this line stops elaborating as `Iff.rfl`, the frozen statement has drifted. -/
theorem noSiegelZeros_iff_exists_at :
    Salt.TwinBar.NoSiegelZeros ↔ ∃ c : ℝ, 0 < c ∧ NoSiegelZerosAt c := Iff.rfl

set_option maxHeartbeats 1200000 in
-- The arithmetic core threads two divisions (`/φ`, `/P`) and several `h²`-scaled
-- nlinarith closes; the elaborator needs headroom past the default.
/-- **The de-smoothing arithmetic core.** Given the sandwich bracket
(`hS1`/`hS2`) and the three main-term brackets (`hpp`/`hp0l`/`hpm`) at the geometric
data `N = h·P`, `Q ≤ P`, `1 ≤ P`, the discrepancy `|S − N/φ|` is `≤ Km·N/Q` with
`Km = 1/2 + K₀·(1+D)`. Pure real arithmetic: the substitution `h·N/P = h²`
collapses both jaws to `h²`-scaled inequalities. -/
private lemma standoff_gate_arith (N h P Q φ K₀ D S pp p0 pm Km : ℝ)
    (hh : 0 < h) (hP : 0 < P) (hQ : 0 < Q) (hφ : 1 ≤ φ)
    (hK₀ : 0 < K₀) (hD : (16 : ℝ) ≤ D)
    (hPQ : Q ≤ P) (hP1 : 1 ≤ P)
    (hNhP : N = h * P)
    (hKm : Km = 1 / 2 + K₀ * (1 + D))
    (hS1 : h * S ≤ pp - p0)
    (hS2 : p0 - pm ≤ h * S)
    (hpp : φ * pp ≤ (N + h) ^ 2 / 2 + K₀ * (N + h) ^ 2 / P ^ 2)
    (hp0l : N ^ 2 / 2 - K₀ * N ^ 2 / P ^ 2 ≤ φ * p0)
    (hpm : φ * pm ≤ (N - h) ^ 2 / 2 + K₀ * (N - h) ^ 2 * D / P ^ 2) :
    |S - N / φ| ≤ Km * N / Q := by
  have hφ0 : 0 < φ := by linarith
  have hN0 : 0 ≤ N := by nlinarith [hNhP, hh.le, hP.le]
  have hP2 : 0 < P ^ 2 := by positivity
  have hhN_P : h * N / P = h ^ 2 := by
    have h1 : h * N = h ^ 2 * P := by rw [hNhP]; ring
    rw [h1, mul_div_assoc, div_self (ne_of_gt hP), mul_one]
  have hKmh2 : Km * h ^ 2 = h ^ 2 / 2 + K₀ * (1 + D) * h ^ 2 := by rw [hKm]; ring
  have hKmnn : 0 ≤ Km * h ^ 2 := by rw [hKm]; positivity
  have hφKm : Km * h ^ 2 ≤ φ * (Km * h ^ 2) := le_mul_of_one_le_left hKmnn hφ
  have hKh2 : 0 ≤ K₀ * h ^ 2 := mul_nonneg hK₀.le (sq_nonneg h)
  have hDfact : 0 ≤ K₀ * (D - 4) * h ^ 2 :=
    mul_nonneg (mul_nonneg hK₀.le (by linarith)) (sq_nonneg h)
  -- error bounds (each ≤ a multiple of h²)
  have hEp : K₀ * (N + h) ^ 2 / P ^ 2 ≤ 4 * K₀ * h ^ 2 := by
    have hNplus : (N + h) ^ 2 = h ^ 2 * (P + 1) ^ 2 := by rw [hNhP]; ring
    rw [hNplus, div_le_iff₀ hP2]
    have hPsq : (P + 1) ^ 2 ≤ 4 * P ^ 2 := by nlinarith [hP1]
    have e : K₀ * (h ^ 2 * (P + 1) ^ 2) = (K₀ * h ^ 2) * (P + 1) ^ 2 := by ring
    rw [e]
    calc (K₀ * h ^ 2) * (P + 1) ^ 2 ≤ (K₀ * h ^ 2) * (4 * P ^ 2) :=
          mul_le_mul_of_nonneg_left hPsq hKh2
      _ = 4 * K₀ * h ^ 2 * P ^ 2 := by ring
  have hE0 : K₀ * N ^ 2 / P ^ 2 ≤ K₀ * h ^ 2 := by
    have hE0eq : K₀ * N ^ 2 / P ^ 2 = K₀ * h ^ 2 := by
      rw [hNhP, show K₀ * (h * P) ^ 2 = (K₀ * h ^ 2) * P ^ 2 by ring, mul_div_assoc,
        div_self (ne_of_gt hP2), mul_one]
    rw [hE0eq]
  have hEm : K₀ * (N - h) ^ 2 * D / P ^ 2 ≤ K₀ * D * h ^ 2 := by
    have hNminus : (N - h) ^ 2 = h ^ 2 * (P - 1) ^ 2 := by rw [hNhP]; ring
    rw [hNminus, div_le_iff₀ hP2]
    have hPmd : (P - 1) ^ 2 ≤ P ^ 2 := by nlinarith [hP1]
    have e : K₀ * (h ^ 2 * (P - 1) ^ 2) * D = (K₀ * D * h ^ 2) * (P - 1) ^ 2 := by ring
    rw [e]
    calc (K₀ * D * h ^ 2) * (P - 1) ^ 2 ≤ (K₀ * D * h ^ 2) * P ^ 2 :=
          mul_le_mul_of_nonneg_left hPmd (by positivity)
      _ = K₀ * D * h ^ 2 * P ^ 2 := by ring
  -- UPPER jaw
  have hUpP : S ≤ N / φ + Km * N / P := by
    have hstep : pp - p0 ≤ h * N / φ + Km * h ^ 2 := by
      rw [← sub_nonneg]
      have hφc : φ * (h * N / φ + Km * h ^ 2 - (pp - p0))
          = h * N + φ * (Km * h ^ 2) - φ * (pp - p0) := by field_simp
      have hpos' : 0 ≤ h * N + Km * h ^ 2 - φ * (pp - p0) := by
        rw [hKmh2]; nlinarith [hpp, hp0l, hEp, hE0, hDfact]
      have hpos : 0 ≤ h * N + φ * (Km * h ^ 2) - φ * (pp - p0) := by linarith [hpos', hφKm]
      have := (mul_nonneg_iff_of_pos_left hφ0).mp (by rw [hφc]; exact hpos)
      linarith [this]
    have hmul : h * S ≤ h * (N / φ + Km * N / P) := by
      have hrw : h * (N / φ + Km * N / P) = h * N / φ + Km * (h * N / P) := by ring
      rw [hrw, hhN_P]; linarith [hS1, hstep]
    exact le_of_mul_le_mul_left hmul hh
  -- LOWER jaw
  have hLoP : N / φ - Km * N / P ≤ S := by
    have hstep : h * N / φ - Km * h ^ 2 ≤ p0 - pm := by
      rw [← sub_nonneg]
      have hφc : φ * (p0 - pm - (h * N / φ - Km * h ^ 2))
          = φ * (p0 - pm) - h * N + φ * (Km * h ^ 2) := by field_simp; ring
      have hpos' : 0 ≤ φ * (p0 - pm) - h * N + Km * h ^ 2 := by
        rw [hKmh2]; nlinarith [hp0l, hpm, hE0, hEm, hDfact]
      have hpos : 0 ≤ φ * (p0 - pm) - h * N + φ * (Km * h ^ 2) := by linarith [hpos', hφKm]
      have := (mul_nonneg_iff_of_pos_left hφ0).mp (by rw [hφc]; exact hpos)
      linarith [this]
    have hmul : h * (N / φ - Km * N / P) ≤ h * S := by
      have hrw : h * (N / φ - Km * N / P) = h * N / φ - Km * (h * N / P) := by ring
      rw [hrw, hhN_P]; linarith [hS2, hstep]
    exact le_of_mul_le_mul_left hmul hh
  -- combine + relax P → Q
  have hrelax : Km * N / P ≤ Km * N / Q := by
    have hKN : 0 ≤ Km * N := mul_nonneg (by rw [hKm]; positivity) hN0
    gcongr
  rw [abs_le]
  exact ⟨by linarith [hLoP, hrelax], by linarith [hUpP, hrelax]⟩

set_option maxHeartbeats 1600000 in
-- `psi1AP_main_bound`'s one large term (fold, dispatcher, standoff branch, counting,
-- absorption), copied with one branch rewritten; the same headroom the original needs.
/-- **S6c from a fixed standoff.** `psi1AP_main_bound` (`Fold.lean:157`) with the Siegel
kill at `Fold.lean:167` replaced by the standoff `hS`: the exceptional branch reads
`1 − β₁ ≥ c/log f` at the conductor `f = χ.conductor` (with `1 < f` from primitivity and
`χ ≠ 1`), and `f ≤ (log x)^C` turns `x^{−(1−β₁)}` into a saving beyond every power of
`log x`, absorbed into `x₀` by one more `tendsto`. **Conclusion: `Fold.lean:157`, verbatim**
(certified by `StandoffCert`). FROZEN; class B. -/
theorem psi1AP_main_bound_of_standoff {c : ℝ} (hc : 0 < c) (hS : NoSiegelZerosAt c) :
    ∀ A C : ℝ, 0 < A → 0 < C → ∃ K x₀ : ℝ, 0 < K ∧
    ∀ (q : ℕ) [NeZero q] {a : ℕ}, a < q → Nat.Coprime q a → ∀ {x : ℝ}, x₀ ≤ x →
      (q : ℝ) ≤ (Real.log x) ^ C →
      |(q.totient : ℝ) * psi1AP x q a - x ^ 2 / 2| ≤ K * x ^ 2 / (Real.log x) ^ A := by
  intro A C hA hC
  -- constants
  have hCne : C ≠ 0 := ne_of_gt hC
  obtain ⟨cc, Kc, hccpos, hKcpos, hchar⟩ := psi1_char_bound
  obtain ⟨ct, Kt, hctpos, hKtpos, htriv⟩ := psi1_trivchar_bound
  set c5 : ℝ := min cc ct with hc5def
  have hc5pos : 0 < c5 := lt_min hccpos hctpos
  have hc5cc : c5 ≤ cc := min_le_left _ _
  have hc5ct : c5 ≤ ct := min_le_right _ _
  set Kbig : ℝ := max Kc Kt with hKbigdef
  have hKbigpos : 0 < Kbig := lt_of_lt_of_le hKcpos (le_max_left _ _)
  have hKcKbig : Kc ≤ Kbig := le_max_left _ _
  have hKtKbig : Kt ≤ Kbig := le_max_right _ _
  -- the eventually facts, extracted into x₀
  have hTA : Tendsto (fun x : ℝ => (2 * Kbig + 1) * (Real.log x) ^ (C + A)
      * Real.exp (-(c5 * Real.sqrt (Real.log x)))) atTop (𝓝 0) := by
    have := (log_rpow_mul_exp_neg_sqrt_tendsto (C + A) c5 hc5pos).const_mul (2 * Kbig + 1)
    simpa only [mul_zero, mul_assoc] using this
  have hEvA : ∀ᶠ x : ℝ in atTop, (2 * Kbig + 1) * (Real.log x) ^ (C + A)
      * Real.exp (-(c5 * Real.sqrt (Real.log x))) ≤ 1 / 2 :=
    ((tendsto_order.1 hTA).2 (1/2) (by norm_num)).mono (fun x h => h.le)
  have hEvB : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ (2 * C + 1 + A) / x ≤ 1 / 2 :=
    ((tendsto_order.1 (log_rpow_div_tendsto (2 * C + 1 + A))).2 (1/2) (by norm_num)).mono
      (fun x h => h.le)
  have hSmallEv : ∀ᶠ x : ℝ in atTop,
      C * Real.log (Real.log x) + Real.log 2 ≤ Real.sqrt (Real.log x) :=
    Real.tendsto_log_atTop.eventually (smallness_base hC)
  -- the standoff's absorption: (c5·C/c)·log log x + log 2 ≤ √(log x), eventually
  have hStdEv : ∀ᶠ x : ℝ in atTop,
      c5 * C / c * Real.log (Real.log x) + Real.log 2 ≤ Real.sqrt (Real.log x) :=
    Real.tendsto_log_atTop.eventually (smallness_base (by positivity : (0:ℝ) < c5 * C / c))
  have hLog4Ev : ∀ᶠ x : ℝ in atTop, (4:ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4:ℝ))
  obtain ⟨x₀, hx₀⟩ := (hEvA.and (hEvB.and (hSmallEv.and (hStdEv.and (hLog4Ev.and
    (eventually_ge_atTop (3:ℝ))))))
    ).exists_forall_of_atTop
  refine ⟨1, x₀, one_pos, ?_⟩
  intro q iq a ha hcop x hxx hqLC
  obtain ⟨hEvA', hEvB', hSmall', hStd', hLog4', hX3'⟩ := hx₀ x hxx
  -- basic x facts
  have hxpos : 0 < x := by linarith
  have hLogpos : 0 < Real.log x := by linarith
  have hLognn : 0 ≤ Real.log x := le_of_lt hLogpos
  have hLog1 : 1 ≤ Real.log x := by linarith
  have hspos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLogpos
  have hLApos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hLogpos A
  have hLC1 : 1 ≤ (Real.log x) ^ C := by
    have := Real.rpow_le_rpow (zero_le_one) hLog1 hC.le; rwa [Real.one_rpow] at this
  -- q facts
  have hqpos_nat : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : 1 ≤ q := hqpos_nat
  have hqpos : 0 < (q:ℝ) := by exact_mod_cast hqpos_nat
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  -- T := exp(√log x)
  set T : ℝ := Real.exp (Real.sqrt (Real.log x)) with hTdef
  have hTpos : 0 < T := by rw [hTdef]; exact Real.exp_pos _
  have hs2 : (2:ℝ) ≤ Real.sqrt (Real.log x) := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    calc (2:ℝ) = Real.sqrt 4 := h4.symm
      _ ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt (by linarith)
  have hexp2 : (4:ℝ) ≤ Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [h, Real.exp_pos 1]
  have hTge4 : (4:ℝ) ≤ T := by
    rw [hTdef]
    exact le_trans hexp2 (Real.exp_le_exp.mpr hs2)
  -- smallness: log(q(T+4)) ≤ 2√log x
  have hsmall : Real.log ((q:ℝ) * (T + 4)) ≤ 2 * Real.sqrt (Real.log x) := by
    have hlogmul : Real.log ((q:ℝ) * (T + 4)) = Real.log q + Real.log (T + 4) :=
      Real.log_mul hqpos.ne' (by positivity)
    have hlogq : Real.log q ≤ C * Real.log (Real.log x) := by
      calc Real.log q ≤ Real.log ((Real.log x) ^ C) := Real.log_le_log hqpos hqLC
        _ = C * Real.log (Real.log x) := Real.log_rpow hLogpos C
    have hlogT4 : Real.log (T + 4) ≤ Real.log 2 + Real.sqrt (Real.log x) := by
      have hT2T : T + 4 ≤ 2 * T := by linarith
      calc Real.log (T + 4) ≤ Real.log (2 * T) := Real.log_le_log (by positivity) hT2T
        _ = Real.log 2 + Real.log T := Real.log_mul (by norm_num) (ne_of_gt hTpos)
        _ = Real.log 2 + Real.sqrt (Real.log x) := by rw [hTdef, Real.log_exp]
    rw [hlogmul]; linarith [hlogq, hlogT4, hSmall']
  -- unit witness
  have hau : IsUnit (a : ZMod q) := by rw [ZMod.isUnit_iff_coprime]; exact hcop.symm
  -- the two rpow-power identities used in the counting
  have hLC2 : ((Real.log x) ^ C) ^ 2 = (Real.log x) ^ (2 * C) := by
    rw [← Real.rpow_natCast ((Real.log x) ^ C) 2, ← Real.rpow_mul hLognn]
    congr 1; push_cast; ring
  -- per-character psi1Chi bound for non-principal χ
  have hpsi1_bound : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖psi1Chi x χ‖ ≤ (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x)))
        + (q:ℝ) * Real.log x * x := by
    intro χ hχ1
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hχp_prim : χ.primitiveCharacter.IsPrimitive := χ.primitiveCharacter_isPrimitive
    have hχp_ne1 : χ.primitiveCharacter ≠ 1 := fun h =>
      hχ1 (by rw [← changeLevel_primitiveCharacter χ, h, changeLevel_one])
    have hcond_le : χ.conductor ≤ q := Nat.le_of_dvd hqpos_nat χ.conductor_dvd_level
    have hcondR : (χ.conductor : ℝ) ≤ (q:ℝ) := by exact_mod_cast hcond_le
    have hcondpos : 0 < (χ.conductor : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    have hsmall_p : Real.log ((χ.conductor : ℝ) * (T + 4)) ≤ 2 * Real.sqrt (Real.log x) := by
      have hmono : Real.log ((χ.conductor : ℝ) * (T + 4)) ≤ Real.log ((q:ℝ) * (T + 4)) :=
        Real.log_le_log (mul_pos hcondpos (by linarith [hTge4]))
          (mul_le_mul_of_nonneg_right hcondR (by linarith [hTge4]))
      linarith [hmono, hsmall]
    have hdisp := hchar χ.conductor χ.primitiveCharacter hχp_prim hχp_ne1 hX3' hTdef hsmall_p
    -- ‖ψ₁(x, χ₁)‖ ≤ (Kbig+1) x² e^{−c5√L}
    have hchip_bound : ‖psi1Chi x χ.primitiveCharacter‖
        ≤ (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
      rcases hdisp with hclean | ⟨β₁, hz, _horder, hsq, ⟨hβlo, hβhi⟩, _hβwin, hbnd⟩
      · -- clean branch
        calc ‖psi1Chi x χ.primitiveCharacter‖
            ≤ Kc * x ^ 2 * Real.exp (-(cc * Real.sqrt (Real.log x))) := hclean
          _ ≤ (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
              apply mul_le_mul
              · apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
              · exact Real.exp_le_exp.mpr (by nlinarith [hc5cc, hspos])
              · positivity
              · positivity
      · -- exceptional branch: kill the residue term with Siegel
        have hβpos : 0 < β₁ := by linarith
        -- the standoff at the conductor f = χ.conductor (1 < f: a character mod 1 is 1)
        have h1f : 1 < χ.conductor := by
          rcases Nat.lt_or_ge 1 χ.conductor with h | h
          · exact h
          · exfalso
            have hne := NeZero.ne χ.conductor
            have hf1 : χ.conductor = 1 := by omega
            exact hχp_ne1 (DirichletCharacter.level_one' χ.primitiveCharacter hf1)
        have hstd := hS χ.conductor χ.primitiveCharacter h1f hχp_prim hsq hχp_ne1 β₁ hz hβhi
        have hlogf_pos : 0 < Real.log (χ.conductor : ℝ) :=
          Real.log_pos (by exact_mod_cast h1f)
        have hlogf_le : Real.log (χ.conductor : ℝ) ≤ C * Real.log (Real.log x) := by
          calc Real.log (χ.conductor : ℝ) ≤ Real.log q := Real.log_le_log hcondpos hcondR
            _ ≤ Real.log ((Real.log x) ^ C) := Real.log_le_log hqpos hqLC
            _ = C * Real.log (Real.log x) := Real.log_rpow hLogpos C
        have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hkey : c5 * C * Real.log (Real.log x) ≤ c * Real.sqrt (Real.log x) := by
          have h1 : c5 * C / c * Real.log (Real.log x) ≤ Real.sqrt (Real.log x) := by
            linarith [hStd']
          have h2 := mul_le_mul_of_nonneg_left h1 hc.le
          have h3 : c * (c5 * C / c * Real.log (Real.log x)) = c5 * C * Real.log (Real.log x) := by
            field_simp
          linarith [h2, h3]
        have hsqsq : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
          Real.mul_self_sqrt hLognn
        have hA' : c5 * Real.sqrt (Real.log x) * Real.log (χ.conductor : ℝ) ≤ c * Real.log x := by
          calc c5 * Real.sqrt (Real.log x) * Real.log (χ.conductor : ℝ)
              ≤ c5 * Real.sqrt (Real.log x) * (C * Real.log (Real.log x)) :=
                mul_le_mul_of_nonneg_left hlogf_le (by positivity)
            _ = Real.sqrt (Real.log x) * (c5 * C * Real.log (Real.log x)) := by ring
            _ ≤ Real.sqrt (Real.log x) * (c * Real.sqrt (Real.log x)) :=
                mul_le_mul_of_nonneg_left hkey hspos.le
            _ = c * Real.log x := by
                rw [show Real.sqrt (Real.log x) * (c * Real.sqrt (Real.log x))
                  = c * (Real.sqrt (Real.log x) * Real.sqrt (Real.log x)) by ring, hsqsq]
        have hB' : c5 * Real.sqrt (Real.log x) ≤ c / Real.log (χ.conductor : ℝ) * Real.log x := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlogf_pos]; exact hA'
        have hC' : c / Real.log (χ.conductor : ℝ) * Real.log x ≤ (1 - β₁) * Real.log x :=
          mul_le_mul_of_nonneg_right (by linarith [hstd]) hLognn
        have hstep : c5 * Real.sqrt (Real.log x) ≤ (1 - β₁) * Real.log x := le_trans hB' hC'
        -- the residue-term norm bound
        have hden1 : (1:ℝ) ≤ β₁ * (β₁ + 1) := by nlinarith [hβlo]
        have hnorm_exc : ‖(x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1))‖
            = x ^ (β₁ + 1) / (β₁ * (β₁ + 1)) := norm_exc_term x β₁ hxpos hβpos
        have hexc1 : ‖(x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1))‖ ≤ x ^ (β₁ + 1) := by
          rw [hnorm_exc]; exact div_le_self (Real.rpow_nonneg hxpos.le _) hden1
        have hxβ : x ^ (β₁ + 1) = x ^ 2 * Real.exp (-((1 - β₁) * Real.log x)) := by
          rw [show β₁ + 1 = (2:ℝ) + (β₁ - 1) by ring, Real.rpow_add hxpos]
          congr 1
          · rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
          · rw [Real.rpow_def_of_pos hxpos]; congr 1; ring
        have hexc_le : ‖(x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1))‖
            ≤ x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
          have hxβ_le : x ^ (β₁ + 1) ≤ x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
            rw [hxβ]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.exp_le_exp.mpr (by linarith [hstep])
          linarith [hexc1, hxβ_le]
        -- combine: ‖ψ₁(χ₁)‖ ≤ ‖ψ₁(χ₁)+exc‖ + ‖exc‖
        have heq2 : psi1Chi x χ.primitiveCharacter
            = (psi1Chi x χ.primitiveCharacter
                + (x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1)))
              - (x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1)) := by abel
        calc ‖psi1Chi x χ.primitiveCharacter‖
            = ‖(psi1Chi x χ.primitiveCharacter
                  + (x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1)))
                - (x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1))‖ := by rw [← heq2]
          _ ≤ ‖psi1Chi x χ.primitiveCharacter
                  + (x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1))‖
                + ‖(x:ℂ) ^ ((β₁:ℂ) + 1) / ((β₁:ℂ) * ((β₁:ℂ) + 1))‖ := norm_sub_le _ _
          _ ≤ Kc * x ^ 2 * Real.exp (-(cc * Real.sqrt (Real.log x)))
                + x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := add_le_add hbnd hexc_le
          _ ≤ (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
              have hkc : Kc * x ^ 2 * Real.exp (-(cc * Real.sqrt (Real.log x)))
                  ≤ Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_right hKcKbig (by positivity)
                · exact Real.exp_le_exp.mpr (by nlinarith [hc5cc, hspos])
                · positivity
                · positivity
              nlinarith [hkc]
    -- transfer to χ
    have htransfer := psi1_transfer χ (by linarith : (1:ℝ) ≤ x)
    have htr2 : ‖psi1Chi x χ - psi1Chi x χ.primitiveCharacter‖ ≤ (q:ℝ) * Real.log x * x := by
      calc ‖psi1Chi x χ - psi1Chi x χ.primitiveCharacter‖
          ≤ (q.primeFactors.card : ℝ) * Real.log x * x := htransfer
        _ ≤ (q:ℝ) * Real.log x * x := by
            apply mul_le_mul_of_nonneg_right _ hxpos.le
            exact mul_le_mul_of_nonneg_right (primeFactors_card_le_self q) hLognn
    have heq1 : psi1Chi x χ.primitiveCharacter
        + (psi1Chi x χ - psi1Chi x χ.primitiveCharacter) = psi1Chi x χ := by abel
    calc ‖psi1Chi x χ‖
        = ‖psi1Chi x χ.primitiveCharacter
            + (psi1Chi x χ - psi1Chi x χ.primitiveCharacter)‖ := by rw [heq1]
      _ ≤ ‖psi1Chi x χ.primitiveCharacter‖
            + ‖psi1Chi x χ - psi1Chi x χ.primitiveCharacter‖ := norm_add_le _ _
      _ ≤ (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x)))
            + (q:ℝ) * Real.log x * x := add_le_add hchip_bound htr2
  -- the χ₀ (principal) main-term bound
  have hχ0bound : ‖psi1Chi x (1 : DirichletCharacter ℂ q) - (x:ℂ) ^ 2 / 2‖
      ≤ Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
    calc ‖psi1Chi x (1 : DirichletCharacter ℂ q) - (x:ℂ) ^ 2 / 2‖
        ≤ Kt * x ^ 2 * Real.exp (-(ct * Real.sqrt (Real.log x))) := htriv q hX3' hTdef hsmall
      _ ≤ Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hKtKbig (by positivity)
          · exact Real.exp_le_exp.mpr (by nlinarith [hc5ct, hspos])
          · positivity
          · positivity
  -- assemble the sum bound
  set Gval : ℝ := (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x)))
    + (q:ℝ) * Real.log x * x with hGvaldef
  have hGnn : 0 ≤ Gval := by rw [hGvaldef]; positivity
  have hsumbound : ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖ ≤ (q:ℝ) * Gval := by
    have hper : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        ‖(starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖ ≤ Gval := by
      intro χ hχ
      have hχ1 : χ ≠ 1 := Finset.ne_of_mem_erase hχ
      have hcoef : ‖(starRingEnd ℂ) (χ (a : ZMod q))‖ ≤ 1 := by
        rw [Complex.norm_conj]; exact DirichletCharacter.norm_le_one χ _
      calc ‖(starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖
          = ‖(starRingEnd ℂ) (χ (a : ZMod q))‖ * ‖psi1Chi x χ‖ := norm_mul _ _
        _ ≤ 1 * ‖psi1Chi x χ‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
        _ = ‖psi1Chi x χ‖ := one_mul _
        _ ≤ Gval := hpsi1_bound χ hχ1
    calc ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖
        ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖(starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖ := norm_sum_le _ _
      _ ≤ ∑ _χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), Gval := Finset.sum_le_sum hper
      _ = ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) * Gval := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q:ℝ) * Gval := by
          apply mul_le_mul_of_nonneg_right _ hGnn
          calc ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ)
              ≤ (Fintype.card (DirichletCharacter ℂ q) : ℝ) := by
                exact_mod_cast le_trans (Finset.card_erase_le)
                  (le_of_eq (Finset.card_univ))
            _ ≤ (q:ℝ) := card_dirichletCharacter_le q
  -- the fold identity and the principal-character extraction
  have hf1val : (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) (a : ZMod q))
      * psi1Chi x (1 : DirichletCharacter ℂ q) = psi1Chi x (1 : DirichletCharacter ℂ q) := by
    rw [MulChar.one_apply hau, map_one, one_mul]
  have hDnorm : |(q.totient : ℝ) * psi1AP x q a - x ^ 2 / 2|
      = ‖(q.totient : ℂ) * (psi1AP x q a : ℂ) - (x:ℂ) ^ 2 / 2‖ := by
    rw [show (q.totient : ℂ) * (psi1AP x q a : ℂ) - (x:ℂ) ^ 2 / 2
          = (((q.totient : ℝ) * psi1AP x q a - x ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  -- the master estimate
  have hmaster : ‖(q.totient : ℂ) * (psi1AP x q a : ℂ) - (x:ℂ) ^ 2 / 2‖
      ≤ Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) + (q:ℝ) * Gval := by
    rw [← psi1_fold x ha hcop]
    calc ‖(∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ)
            - (x:ℂ) ^ 2 / 2‖
        = ‖(psi1Chi x (1 : DirichletCharacter ℂ q) - (x:ℂ) ^ 2 / 2)
            + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖ := by
          rw [← Finset.add_sum_erase Finset.univ
            (fun χ => (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ)
            (Finset.mem_univ (1 : DirichletCharacter ℂ q))]
          rw [hf1val]; ring_nf
      _ ≤ ‖psi1Chi x (1 : DirichletCharacter ℂ q) - (x:ℂ) ^ 2 / 2‖
            + ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ‖ := norm_add_le _ _
      _ ≤ Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) + (q:ℝ) * Gval :=
          add_le_add hχ0bound hsumbound
  -- the final absorption arithmetic
  rw [hDnorm]
  refine le_trans hmaster ?_
  -- Kbig x² e + q Gval ≤ (2Kbig+1) L^C x² e + L^{2C+1} x
  have hbound1 : Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) + (q:ℝ) * Gval
      ≤ (2 * Kbig + 1) * (Real.log x) ^ C * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x)))
        + (Real.log x) ^ (2 * C + 1) * x := by
    have he : 0 ≤ Real.exp (-(c5 * Real.sqrt (Real.log x))) := (Real.exp_pos _).le
    have hx2 : 0 ≤ x ^ 2 := by positivity
    -- term-by-term
    have ht1 : Kbig * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x)))
        ≤ Kbig * (Real.log x) ^ C * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
      have hkb : Kbig ≤ Kbig * (Real.log x) ^ C := by nlinarith [hLC1, hKbigpos]
      nlinarith [hkb, mul_nonneg hx2 he]
    have ht2 : (q:ℝ) * ((Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))))
        ≤ (Real.log x) ^ C * (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by
      have hM : 0 ≤ (Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by positivity
      calc (q:ℝ) * ((Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))))
          ≤ (Real.log x) ^ C * ((Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x)))) :=
            mul_le_mul_of_nonneg_right hqLC hM
        _ = (Real.log x) ^ C * (Kbig + 1) * x ^ 2
            * Real.exp (-(c5 * Real.sqrt (Real.log x))) := by ring
    have ht3 : (q:ℝ) * ((q:ℝ) * Real.log x * x) ≤ (Real.log x) ^ (2 * C + 1) * x := by
      have hq2 : (q:ℝ) * (q:ℝ) ≤ (Real.log x) ^ (2 * C) := by
        calc (q:ℝ) * (q:ℝ) ≤ (Real.log x) ^ C * (Real.log x) ^ C := by nlinarith [hqLC, hqpos, hLC1]
          _ = ((Real.log x) ^ C) ^ 2 := by ring
          _ = (Real.log x) ^ (2 * C) := hLC2
      have hLprod : (Real.log x) ^ (2 * C) * Real.log x = (Real.log x) ^ (2 * C + 1) := by
        rw [show (2 * C + 1 : ℝ) = 2 * C + 1 by ring, Real.rpow_add hLogpos, Real.rpow_one]
      calc (q:ℝ) * ((q:ℝ) * Real.log x * x) = ((q:ℝ) * (q:ℝ)) * Real.log x * x := by ring
        _ ≤ (Real.log x) ^ (2 * C) * Real.log x * x := by
            apply mul_le_mul_of_nonneg_right _ hxpos.le
            exact mul_le_mul_of_nonneg_right hq2 hLognn
        _ = (Real.log x) ^ (2 * C + 1) * x := by rw [hLprod]
    have hGexp : (q:ℝ) * Gval
        = (q:ℝ) * ((Kbig + 1) * x ^ 2 * Real.exp (-(c5 * Real.sqrt (Real.log x))))
          + (q:ℝ) * ((q:ℝ) * Real.log x * x) := by rw [hGvaldef]; ring
    rw [hGexp]
    nlinarith [ht1, ht2, ht3]
  refine le_trans hbound1 ?_
  -- (2Kbig+1) L^C x² e + L^{2C+1} x ≤ x²/L^A
  have hLApos2 : (0:ℝ) < 2 * (Real.log x) ^ A := by positivity
  have hA1 : (2 * Kbig + 1) * (Real.log x) ^ C * x ^ 2
        * Real.exp (-(c5 * Real.sqrt (Real.log x)))
      ≤ x ^ 2 / (2 * (Real.log x) ^ A) := by
    rw [le_div_iff₀ hLApos2]
    calc (2 * Kbig + 1) * (Real.log x) ^ C * x ^ 2
            * Real.exp (-(c5 * Real.sqrt (Real.log x))) * (2 * (Real.log x) ^ A)
        = ((2 * Kbig + 1) * ((Real.log x) ^ C * (Real.log x) ^ A)
            * Real.exp (-(c5 * Real.sqrt (Real.log x)))) * (2 * x ^ 2) := by ring
      _ = ((2 * Kbig + 1) * (Real.log x) ^ (C + A)
            * Real.exp (-(c5 * Real.sqrt (Real.log x)))) * (2 * x ^ 2) := by
            rw [← Real.rpow_add hLogpos]
      _ ≤ (1/2) * (2 * x ^ 2) := by
            apply mul_le_mul_of_nonneg_right hEvA' (by positivity)
      _ = x ^ 2 := by ring
  have hB1 : (Real.log x) ^ (2 * C + 1) * x ≤ x ^ 2 / (2 * (Real.log x) ^ A) := by
    rw [le_div_iff₀ hLApos2]
    calc (Real.log x) ^ (2 * C + 1) * x * (2 * (Real.log x) ^ A)
        = (2 * ((Real.log x) ^ (2 * C + 1) * (Real.log x) ^ A)) * x := by ring
      _ = (2 * (Real.log x) ^ (2 * C + 1 + A)) * x := by rw [← Real.rpow_add hLogpos]
      _ ≤ x * x := by
          apply mul_le_mul_of_nonneg_right _ hxpos.le
          have hb := hEvB'
          rw [div_le_iff₀ hxpos] at hb
          linarith [hb]
      _ = x ^ 2 := by ring
  have hhalf : x ^ 2 / (2 * (Real.log x) ^ A) + x ^ 2 / (2 * (Real.log x) ^ A)
      = 1 * x ^ 2 / (Real.log x) ^ A := by
    field_simp
    ring
  rw [← hhalf]
  linarith [hA1, hB1]

set_option maxHeartbeats 1200000 in
-- `siegelWalfisz_holds`'s one-pass de-smoothing, copied; the same headroom the original needs.
/-- **THE GATE FROM A STANDOFF.** `siegelWalfisz_holds` (`Gate.lean:150`) with
`psi1AP_main_bound` at `Gate.lean:154` replaced by `psi1AP_main_bound_of_standoff hc hS`;
the de-smoothing through `psi1AP_sandwich` is untouched. **Conclusion:
`Salt.BV.SiegelWalfisz`, verbatim** (certified by `StandoffCert`). Its proof term must not
reach `siegel_theorem`, `siegel_L_one_exceptional` or `L1_lower_siegel` — that is the whole
result, and `StandoffCert` is what says so. FROZEN; class B, mechanical. -/
theorem siegelWalfisz_of_standoff {c : ℝ} (hc : 0 < c) (hS : NoSiegelZerosAt c) :
    Salt.BV.SiegelWalfisz := by
  intro A C hA hC
  -- S6c at A' = 2A+4, C' = C+1
  obtain ⟨K₀, x₀, hK₀pos, hmain⟩ :=
    psi1AP_main_bound_of_standoff hc hS (2 * A + 4) (C + 1) (by positivity) (by linarith)
  -- constants
  set D : ℝ := (2 : ℝ) ^ (2 * A + 4) with hDdef
  have hD16 : (16 : ℝ) ≤ D := by
    rw [hDdef]
    calc (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      _ ≤ (2 : ℝ) ^ (2 * A + 4) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  set Km : ℝ := 1 / 2 + K₀ * (1 + D) with hKmdef
  have hKmpos : 0 < Km := by rw [hKmdef]; positivity
  -- thresholds absorbed into K
  set Mlog : ℝ := max 2 ((2 : ℝ) ^ (C + 1)) with hMdef
  set X₁ : ℝ := max (2 * x₀) (Real.exp Mlog) with hX1def
  have hX1pos : 0 < X₁ := lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  set Kinit : ℝ := (Real.log X₁ + 1) * (Real.log X₁) ^ A with hKinitdef
  set K : ℝ := max Km Kinit with hKdef
  have hK0 : 0 ≤ K := le_trans hKmpos.le (le_max_left _ _)
  refine ⟨K, hK0, ?_⟩
  intro x q a hx2 hq hqlog hcop
  -- common facts on x, L
  have hxpos_nat : 0 < x := by omega
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast hxpos_nat
  have hN0 : 0 ≤ (x : ℝ) := le_of_lt hxpos
  set L : ℝ := Real.log (x : ℝ) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; exact Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hL0 : 0 ≤ L := le_of_lt hLpos
  have hLApos : 0 < L ^ A := Real.rpow_pos_of_pos hLpos A
  -- totient facts
  haveI : NeZero q := ⟨hq.ne'⟩
  set φ : ℝ := (q.totient : ℝ) with hφdef
  have hφ1 : 1 ≤ φ := by
    rw [hφdef]; exact_mod_cast (Nat.totient_pos.mpr hq)
  -- residue reduction a → a % q
  have hr : a % q < q := Nat.mod_lt a hq
  have hcopr : Nat.Coprime q (a % q) := ((Salt.BV.coprime_mod_left a q).mp hcop).symm
  have hmm : a % q % q = a % q := Nat.mod_mod_of_dvd a (dvd_refl q)
  have hpsiEq : psiAP x q a = psiAP x q (a % q) := by
    unfold psiAP; simp only [hmm]
  rw [hpsiEq]
  -- goal: |psiAP x q (a%q) - x/φ| ≤ K * x / L^A
  by_cases hbig : X₁ ≤ (x : ℝ)
  · -- BIG case: sandwich + main bound
    -- log threshold facts
    have hexpN : Real.exp Mlog ≤ (x : ℝ) := le_trans (le_max_right _ _) hbig
    have hM_le_L : Mlog ≤ L := by rw [hLdef]; exact (Real.le_log_iff_exp_le hxpos).mpr hexpN
    have hL2 : (2 : ℝ) ≤ L := le_trans (le_max_left _ _) hM_le_L
    have hLC1 : (2 : ℝ) ^ (C + 1) ≤ L := le_trans (le_max_right _ _) hM_le_L
    have hL1 : (1 : ℝ) ≤ L := by linarith
    have hx0N : 2 * x₀ ≤ (x : ℝ) := le_trans (le_max_left _ _) hbig
    -- P, h and geometry
    set P : ℝ := L ^ (A + 2) with hPdef
    have hPpos : 0 < P := Real.rpow_pos_of_pos hLpos _
    have hP1 : (1 : ℝ) ≤ P := by
      rw [hPdef]
      calc (1 : ℝ) = (1 : ℝ) ^ (A + 2) := (Real.one_rpow _).symm
        _ ≤ L ^ (A + 2) := Real.rpow_le_rpow zero_le_one hL1 (by positivity)
    have hPQ : L ^ A ≤ P := by
      rw [hPdef]; exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hP2ge : (2 : ℝ) ≤ P := by
      rw [hPdef]
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ (2 : ℝ) ^ (A + 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ ≤ L ^ (A + 2) := Real.rpow_le_rpow (by norm_num) hL2 (by positivity)
    set h : ℝ := (x : ℝ) / P with hhdef
    have hhpos : 0 < h := div_pos hxpos hPpos
    have hNhP : (x : ℝ) = h * P := by rw [hhdef, div_mul_cancel₀ _ (ne_of_gt hPpos)]
    have hh_le_half : h ≤ (x : ℝ) / 2 := by
      rw [hhdef]; exact div_le_div_of_nonneg_left hN0 (by norm_num) hP2ge
    have hNhalf : (x : ℝ) / 2 ≤ (x : ℝ) - h := by linarith [hh_le_half]
    have hNmh_pos : 0 ≤ (x : ℝ) - h := by linarith [hNhalf, hN0]
    -- range facts for the main bound (x₀ ≤ each point)
    have hx0half : x₀ ≤ (x : ℝ) / 2 := by linarith [hx0N]
    have hxge_N : x₀ ≤ (x : ℝ) := by linarith [hx0half, hN0]
    have hxge_Nph : x₀ ≤ (x : ℝ) + h := by linarith [hxge_N, hhpos]
    have hxge_Nmh : x₀ ≤ (x : ℝ) - h := by linarith [hNhalf, hx0half]
    -- log-slop
    have hlogNph : L ≤ Real.log ((x : ℝ) + h) := by
      rw [hLdef]; exact Real.log_le_log hxpos (by linarith [hhpos])
    have hlogNmh_ge : L / 2 ≤ Real.log ((x : ℝ) - h) := by
      have hlog_half : Real.log ((x : ℝ) / 2) ≤ Real.log ((x : ℝ) - h) :=
        Real.log_le_log (by positivity) hNhalf
      have hlogN2 : Real.log ((x : ℝ) / 2) = L - Real.log 2 := by
        rw [Real.log_div (ne_of_gt hxpos) (by norm_num), ← hLdef]
      have hlog2_1 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      have hlog2_small : Real.log 2 ≤ L / 2 := le_trans hlog2_1 (by linarith [hL2])
      linarith [hlog_half, hlogN2, hlog2_small]
    have hlogNmh_pos : 0 < Real.log ((x : ℝ) - h) := by linarith [hlogNmh_ge, hL2]
    -- power identities
    have hLP2 : L ^ (2 * A + 4) = P ^ 2 := by
      rw [hPdef, sq, ← Real.rpow_add hLpos]; congr 1; ring
    have hP2pos : 0 < P ^ 2 := by positivity
    -- (log(N+h))^(2A+4) ≥ P²
    have hLogNph_pow : P ^ 2 ≤ (Real.log ((x : ℝ) + h)) ^ (2 * A + 4) := by
      rw [← hLP2]; exact Real.rpow_le_rpow hL0 hlogNph (by positivity)
    -- (log(N-h))^(2A+4) ≥ P²/D  (via P² ≤ D·(log(N-h))^(2A+4))
    have hL2pow : (L / 2) ^ (2 * A + 4) = P ^ 2 / D := by
      rw [Real.div_rpow hL0 (by norm_num), hLP2, hDdef]
    have hDpos : 0 < D := by rw [hDdef]; positivity
    have hP2DW : P ^ 2 ≤ D * (Real.log ((x : ℝ) - h)) ^ (2 * A + 4) := by
      have hL2W : (L / 2) ^ (2 * A + 4) ≤ (Real.log ((x : ℝ) - h)) ^ (2 * A + 4) :=
        Real.rpow_le_rpow (by linarith [hLpos]) hlogNmh_ge (by positivity)
      have hP2eqD : P ^ 2 = D * (L / 2) ^ (2 * A + 4) := by
        rw [hL2pow, mul_div_cancel₀ _ (ne_of_gt hDpos)]
      rw [hP2eqD]; exact mul_le_mul_of_nonneg_left hL2W hDpos.le
    -- q-conditions at the three points
    have hqL : (q : ℝ) ≤ L ^ C := by rw [hLdef]; exact hqlog
    have hqcond_N : (q : ℝ) ≤ L ^ (C + 1) :=
      le_trans hqL (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
    have hqcond_Nph : (q : ℝ) ≤ (Real.log ((x : ℝ) + h)) ^ (C + 1) :=
      le_trans hqcond_N (Real.rpow_le_rpow hL0 hlogNph (by positivity))
    have hqcond_Nmh : (q : ℝ) ≤ (Real.log ((x : ℝ) - h)) ^ (C + 1) := by
      have hLC1_pow : L ^ (C + 1) = L ^ C * L := by rw [Real.rpow_add hLpos, Real.rpow_one]
      have hL2C : (L / 2) ^ (C + 1) = L ^ (C + 1) / 2 ^ (C + 1) := Real.div_rpow hL0 (by norm_num) _
      have hLCLe : L ^ C ≤ (L / 2) ^ (C + 1) := by
        rw [hL2C, le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _), hLC1_pow]
        exact mul_le_mul_of_nonneg_left hLC1 (Real.rpow_nonneg hL0 C)
      exact le_trans hqL (le_trans hLCLe
        (Real.rpow_le_rpow (by linarith [hLpos]) hlogNmh_ge (by positivity)))
    -- the three main-bound brackets
    have hqN' : (q : ℝ) ≤ (Real.log (x : ℝ)) ^ (C + 1) := by rw [← hLdef]; exact hqcond_N
    have hb0 := hmain q (a := a % q) hr hcopr (x := (x : ℝ)) hxge_N hqN'
    have hbp := hmain q (a := a % q) hr hcopr (x := (x : ℝ) + h) hxge_Nph hqcond_Nph
    have hbm := hmain q (a := a % q) hr hcopr (x := (x : ℝ) - h) hxge_Nmh hqcond_Nmh
    -- rewrite log ↑x = L and collapse denominators
    rw [← hLdef, hLP2] at hb0
    -- hp0l
    have hp0l : (x : ℝ) ^ 2 / 2 - K₀ * (x : ℝ) ^ 2 / P ^ 2 ≤ φ * psi1AP (x : ℝ) q (a % q) := by
      have := (abs_le.mp hb0).1; rw [← hφdef] at this; linarith [this]
    -- hpp
    have hppbound : K₀ * ((x : ℝ) + h) ^ 2 / (Real.log ((x : ℝ) + h)) ^ (2 * A + 4)
        ≤ K₀ * ((x : ℝ) + h) ^ 2 / P ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) hP2pos hLogNph_pow
    have hpp : φ * psi1AP ((x : ℝ) + h) q (a % q)
        ≤ ((x : ℝ) + h) ^ 2 / 2 + K₀ * ((x : ℝ) + h) ^ 2 / P ^ 2 := by
      have := (abs_le.mp hbp).2; rw [← hφdef] at this; linarith [this, hppbound]
    -- hpm
    have hden_pos : 0 < (Real.log ((x : ℝ) - h)) ^ (2 * A + 4) :=
      Real.rpow_pos_of_pos hlogNmh_pos _
    have hmbound : K₀ * ((x : ℝ) - h) ^ 2 / (Real.log ((x : ℝ) - h)) ^ (2 * A + 4)
        ≤ K₀ * ((x : ℝ) - h) ^ 2 * D / P ^ 2 := by
      rw [div_le_div_iff₀ hden_pos hP2pos]
      calc K₀ * ((x : ℝ) - h) ^ 2 * P ^ 2
          ≤ K₀ * ((x : ℝ) - h) ^ 2 * (D * (Real.log ((x : ℝ) - h)) ^ (2 * A + 4)) :=
            mul_le_mul_of_nonneg_left hP2DW (by positivity)
        _ = K₀ * ((x : ℝ) - h) ^ 2 * D * (Real.log ((x : ℝ) - h)) ^ (2 * A + 4) := by ring
    have hpm : φ * psi1AP ((x : ℝ) - h) q (a % q)
        ≤ ((x : ℝ) - h) ^ 2 / 2 + K₀ * ((x : ℝ) - h) ^ 2 * D / P ^ 2 := by
      have := (abs_le.mp hbm).2; rw [← hφdef] at this; linarith [this, hmbound]
    -- the sandwich brackets
    have hpsiAPr : psiAPr (x : ℝ) q (a % q) = psiAP x q (a % q) := by
      rw [psiAPr, Nat.floor_natCast]
    have hS1 : h * psiAP x q (a % q)
        ≤ psi1AP ((x : ℝ) + h) q (a % q) - psi1AP (x : ℝ) q (a % q) := by
      have hlow := psi1AP_sub_lower (x := (x : ℝ)) (y := (x : ℝ) + h) hN0 (by linarith [hhpos])
        q (a % q)
      rw [hpsiAPr, show (x : ℝ) + h - (x : ℝ) = h by ring] at hlow
      exact hlow
    have hS2 : psi1AP (x : ℝ) q (a % q) - psi1AP ((x : ℝ) - h) q (a % q)
        ≤ h * psiAP x q (a % q) := by
      have hup := psi1AP_sub_upper (x := (x : ℝ) - h) (y := (x : ℝ)) hNmh_pos (by linarith [hhpos])
        q (a % q)
      rw [hpsiAPr, show (x : ℝ) - ((x : ℝ) - h) = h by ring] at hup
      exact hup
    -- apply the arithmetic core, then relax Km → K
    have hcore := standoff_gate_arith (x : ℝ) h P (L ^ A) φ K₀ D (psiAP x q (a % q))
      (psi1AP ((x : ℝ) + h) q (a % q)) (psi1AP (x : ℝ) q (a % q))
      (psi1AP ((x : ℝ) - h) q (a % q)) Km hhpos hPpos hLApos hφ1 hK₀pos hD16 hPQ hP1 hNhP
      hKmdef hS1 hS2 hpp hp0l hpm
    calc |psiAP x q (a % q) - (x : ℝ) / φ|
        ≤ Km * (x : ℝ) / L ^ A := hcore
      _ ≤ K * (x : ℝ) / L ^ A :=
          (div_le_div_iff_of_pos_right hLApos).mpr
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hN0)
  · -- SMALL case: crude bound ψ(N;q,a) ≤ N·log N
    have hxX1 : (x : ℝ) < X₁ := lt_of_not_ge hbig
    have hLlog : L ≤ Real.log X₁ := by rw [hLdef]; exact Real.log_le_log hxpos (le_of_lt hxX1)
    -- crude: psiAP ≤ x·L
    have hcrude : psiAP x q (a % q) ≤ (x : ℝ) * L := by
      rw [hLdef]
      calc psiAP x q (a % q)
          ≤ ∑ _n ∈ Finset.Icc 1 x, Real.log (x : ℝ) := by
            unfold psiAP
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun n _ _ => vonMangoldt_nonneg)) ?_
            refine Finset.sum_le_sum (fun n hn => ?_)
            rw [Finset.mem_Icc] at hn
            exact le_trans vonMangoldt_le_log
              (Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2))
        _ = (x : ℝ) * Real.log (x : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            push_cast [Nat.add_sub_cancel]; ring
    have hAP0 : 0 ≤ psiAP x q (a % q) := Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
    have hφpos : 0 < φ := by linarith [hφ1]
    have hdivle : (x : ℝ) / φ ≤ (x : ℝ) := div_le_self hN0 hφ1
    have hdiv0 : 0 ≤ (x : ℝ) / φ := div_nonneg hN0 (by linarith [hφ1])
    -- |psiAP - x/φ| ≤ x·L + x
    have habs : |psiAP x q (a % q) - (x : ℝ) / φ| ≤ (x : ℝ) * L + (x : ℝ) := by
      rw [abs_le]
      constructor
      · linarith [hAP0, hdivle, hdiv0]
      · linarith [hcrude, hdiv0]
    -- x·L + x ≤ K · x / L^A
    have hKL : (L + 1) * L ^ A ≤ K := by
      calc (L + 1) * L ^ A ≤ (Real.log X₁ + 1) * (Real.log X₁) ^ A := by
            apply mul_le_mul (by linarith [hLlog])
              (Real.rpow_le_rpow hL0 hLlog hA.le) hLApos.le (by linarith [hLlog, hL0])
        _ = Kinit := (hKinitdef).symm
        _ ≤ K := le_max_right _ _
    refine le_trans habs ?_
    rw [le_div_iff₀ hLApos]
    calc ((x : ℝ) * L + (x : ℝ)) * L ^ A
        = (x : ℝ) * ((L + 1) * L ^ A) := by ring
      _ ≤ (x : ℝ) * K := mul_le_mul_of_nonneg_left hKL hN0
      _ = K * (x : ℝ) := mul_comm _ _

/-- **The `¬F` horn, cashed.** The fulcrum dichotomy's right arm
(`not_fulcrum_implies_noSiegelZeros`, `Fulcrum/Dichotomy.lean:82`) delivers `NoSiegelZeros`;
unfolding it through `noSiegelZeros_iff_exists_at` hands `siegelWalfisz_of_standoff` its
`c`. So under `¬ FulcrumQualityMin C`, Siegel–Walfisz is proved with no Siegel input — at a
standoff `c` that is nonconstructive (see the label above). FROZEN; class A once the two
above land. -/
theorem not_fulcrum_siegelFree_SW {C : ℝ} (hC : 0 < C)
    (hnF : ¬ Salt.Fulcrum.FulcrumQualityMin C) :
    ∃ c : ℝ, 0 < c ∧ NoSiegelZerosAt c ∧ Salt.BV.SiegelWalfisz := by
  obtain ⟨c, hc, hS⟩ := noSiegelZeros_iff_exists_at.mp
    (Salt.Fulcrum.not_fulcrum_implies_noSiegelZeros hC hnF)
  exact ⟨c, hc, hS, siegelWalfisz_of_standoff hc hS⟩

end Salt.SW
