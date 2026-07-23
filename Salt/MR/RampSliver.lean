/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HalaszRepAsm

/-!
# H-5 v5 — the ramp sliver bound (`RampSliver`)

Stone **V5-5** of the H-5 v5 wave (`docs/exploration/h5-v5-design.md`, stone
`ramp_sliver_bound`).  The (X, X+h] hat-ramp residue of the v5 un-truncation.

After the joint un-truncation (V5-3: both `winCoeff` legs → the full
`lambdaLin (restrictAbove y g)` coefficient, EXACTLY on `N ≤ X`), the hat kernel's
ramp region `(X, X+h]` leaves a residue.  Per the verified joint squeeze
(`h5-v5-design.md`, stone V5-5's ⟦R⟧ block): a defect leg `k ≥ X/y` forces its
window partner `l ∈ (y, y(1+h/X)]` (both prime-power supported) AND both spectator
legs `= 1` (because `N/(kl) < 2`); a defect⊗defect term has `N ≥ (X/y)² > X+h`, so
`hatK = 0`.  The residue therefore collapses to the two-index mass

  `rampSliverMass = Σ_{l ∈ (y, y(1+h/X)]} Σ_{k ∈ (X/l, (X+h)/l]}
                       ‖Λ_ℓ k‖ · ‖Λ_ℓ l‖`,   `Λ_ℓ = lambdaLin (restrictAbove y g)`.

This is the object the four-factor coefficient difference sum reduces to under
V5-3's support argument (the `shiftCoeff (-α)`, `shiftCoeff (-α-2β)` legs of
`alignedCoeff` carry `n^{-α}, n^{-α-2β} ≤ 1` DECAY, dropped for free; `hatK ≤ 1`;
the `α,β` integral contributes `η² ≤ 1`; the leading `(2:ℝ)•` is a bounded factor).
Stating the bound at the mass level keeps V5-5's analytic content (the k-side
short-interval Chebyshev sum) separate from V5-3's elementary support reduction, as
the design's stone division intends; the discharge into `prop21RHS_hat_rep_aligned`
is then a rewrite (V5-2) composed with V5-3.

## TWO BRANCHES (per the regime gate `y ≥ √(log X)`, `SLIVER-V5-REF`-quantified)

* **Branch (b)** — `rampSliverMass_eq_zero_of_gap` (UNCONDITIONAL, elementary): for
  slow/constant `y` (below the gate; concretely whenever the squeeze interval
  `(y, y(1+h/X)]` reaches no new integer, `y·h/X < ⌊y⌋+1−y`), the outer index set is
  EMPTY, so the sliver mass is `0`.  For a bounded `y` the length `y·h/X = y·L^{-1/2}`
  falls below the gap-to-the-next-integer for `X` large (`∃ x₀`), so this fires.

* **Branch (a)** — `ramp_sliver_bound` (CONDITIONAL on THE GRAIN): at the gate
  `y ≥ √(log X)`, with `h = X / √(log X)` and `10 ≤ y`, the mass is
  `≤ C · (X / log X) · log y` — the exact E-grade shape V5-6 consumes.  The l-side
  count `≤ y·L^{-1/2} + 1` and the per-partner `Λ_ℓ(l) ≤ log(2y)` are elementary;
  the k-side needs the SHORT-INTERVAL CHEBYSHEV bound
  `Σ_{k ∈ (X/l, (X+h)/l]} Λ(k) ≤ C_cheb · (h/l)` (`hgrain`), taken here as an
  explicit hypothesis.

## THE GRAIN — THE STONE'S NAMED RESIDUAL (fail-fast, 3 in-corpus attempts)

`hgrain` (`Σ_{k ∈ (a, a+H]} Λ(k) ≤ C·H` at `H ~ a·L^{-1/2}`, Brun–Titchmarsh grade)
is the one analytic ingredient with no unconditional in-corpus route:

* `HalaszSeam.lambdaLin_window_bound` / `Chebyshev.psi_le_const_mul_self`:
  FULL-endpoint `Σ_{(a,b]} Λ ≤ (log 4+4)·b` — ignores `a`, gives `(log4+4)·(a+H)`,
  the `log X` overrun the design forbids on the k-side.
* `MultShiu.lambda_partial_alpha`: `Σ_{k≤K} Λ/k^α ≤ 2(log4+4)K^{1-α}/(1-α)` — a
  FULL sum to `K`; differencing two of them gives `ψ(a+H)−ψ(a)` bounded by the
  mismatched Chebyshev upper/lower constants (`≈5.4` vs `≈0.69`), yielding
  `(upper−lower)·a ≫ H`, not `C·H`.  FAILS.
* `Chen.prime_count_Ioc_le` (`TripleCount.lean:118`) IS a sharp short-interval prime
  count, but it CARRIES A PNT HYPOTHESIS `|psiTot x − x| ≤ K·x/log x` (ζ-theory) —
  forbidden in Part 1 (`h5-v5-design.md` corner ledger: "No ζ-theory in Part 1").

The honest unconditional route is a Selberg-sieve Brun–Titchmarsh
(`Salt/Brun/SelbergPort.lean`'s `selberg_bound_simple`, adapted to the integers of
`(a, a+H]` sifted by `p ≤ √(a+H)`) or the Part-2 PNT.  Either is a separate
C/D-grade stone; V5-5 lands branch (a) CONDITIONAL on `hgrain` (the corpus's
named-residual pattern, cf. `prop21_analog`'s `hfactor`, `contour_A13_A14_head`'s
`hCS`).  RESIDUAL statement, verbatim:

  `∃ C_cheb, ∀ a H, (regime) → Σ_{k ∈ (a, a+H]} Λ(k) ≤ C_cheb · H`   at `H ~ a·L^{-1/2}`.
-/

noncomputable section

namespace Salt.MR

open ArithmeticFunction
open scoped BigOperators

/-- **The joint-squeeze ramp sliver mass.**  The `(X, X+h]` hat-ramp residue after
the un-truncation, collapsed by the verified joint squeeze to the two-index sum over
the defect leg `k ∈ (X/l, (X+h)/l]` (so `k·l ∈ (X, X+h]`) and its window partner
`l ∈ (y, y(1+h/X)]`, with both spectator legs pinned to `1`.  `Λ_ℓ` is the large
von Mangoldt analog `lambdaLin (restrictAbove y g)`. -/
def rampSliverMass (g : ℕ → ℂ) (X h y : ℝ) : ℝ :=
  ∑ l ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊,
    ∑ k ∈ Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊,
      ‖lambdaLin (restrictAbove y g) k‖ * ‖lambdaLin (restrictAbove y g) l‖

/-- The ramp sliver mass is nonnegative (a sum of products of norms). -/
lemma rampSliverMass_nonneg (g : ℕ → ℂ) (X h y : ℝ) : 0 ≤ rampSliverMass g X h y :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))

/-! ## Branch (b) — the empty-squeeze regime (unconditional) -/

/-- **Branch (b) — the sliver vanishes when the squeeze interval reaches no new
integer.**  If `y + y·h/X < ⌊y⌋+1` (the partner interval `(y, y(1+h/X)]` stays below
the next integer — true for bounded `y` and `X` large, where `y·h/X = y·L^{-1/2} → 0`,
the design's `y < √(log X)` branch), then the outer index set `Ioc ⌊y⌋ ⌊y+yh/X⌋` is
empty and the ramp sliver mass is `0`. -/
theorem rampSliverMass_eq_zero_of_gap (g : ℕ → ℂ) {X h y : ℝ}
    (hy : (0 : ℝ) ≤ y) (hh : (0 : ℝ) ≤ h) (hX : (0 : ℝ) < X)
    (hgap : y + y * h / X < (⌊y⌋₊ : ℝ) + 1) :
    rampSliverMass g X h y = 0 := by
  have hnn : (0 : ℝ) ≤ y + y * h / X := by positivity
  have hlt : ⌊y + y * h / X⌋₊ < ⌊y⌋₊ + 1 := by
    rw [Nat.floor_lt hnn]; exact_mod_cast hgap
  have hle : ⌊y + y * h / X⌋₊ ≤ ⌊y⌋₊ := by omega
  rw [rampSliverMass, Finset.Ioc_eq_empty (not_lt.mpr hle), Finset.sum_empty]

/-! ## Branch (a) — the gate `y ≥ √(log X)`, conditional on THE GRAIN -/

/-- **The l-side elementary count.**  The number of window partners
`l ∈ (⌊y⌋, ⌊y+y·h/X⌋]` is `≤ y·h/X + 1` (the interval has real length `y·h/X`,
`= y·L^{-1/2}` in the regime). -/
private lemma rampSliver_lcard_le {X h y : ℝ} (hy : (0 : ℝ) ≤ y) (hh : (0 : ℝ) ≤ h)
    (hX : (0 : ℝ) < X) :
    ((Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊).card : ℝ) ≤ y * h / X + 1 := by
  have hnn : (0 : ℝ) ≤ y + y * h / X := by positivity
  have hmono : ⌊y⌋₊ ≤ ⌊y + y * h / X⌋₊ :=
    Nat.floor_mono (by nlinarith [div_nonneg (mul_nonneg hy hh) hX.le])
  rw [Nat.card_Ioc, Nat.cast_sub hmono]
  have hup : (⌊y + y * h / X⌋₊ : ℝ) ≤ y + y * h / X := Nat.floor_le hnn
  have hlo : y - 1 < (⌊y⌋₊ : ℝ) := by have := Nat.lt_floor_add_one y; linarith
  linarith

/-- **Branch (a) — the ramp sliver bound** (CONDITIONAL on THE GRAIN `hgrain`).
At the regime gate `y ≥ √(log X)` (with `h = X / √(log X)` and `10 ≤ y`), the ramp
sliver mass is `≤ C · (X / log X) · log y` — the E-grade shape V5-6 consumes.  The
k-side short-interval Chebyshev bound `Σ_{k∈(X/l,(X+h)/l]} Λ(k) ≤ C_cheb·(h/l)` is
the sole hypothesis (`hgrain`, THE GRAIN — the stone's named residual, see the module
docstring); everything else — the l-count `≤ y·L^{-1/2}+1`, the partner mass
`Λ_ℓ(l) ≤ log(2y)`, and the geometric assembly `(y·h/X+1)·(h/y) ≤ 2X/log X` — is
elementary.  Concretely `C = 4·C_cheb`. -/
theorem ramp_sliver_bound (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X h y : ℝ} (hX : Real.exp 1 ≤ X) (hh : h = X / Real.sqrt (Real.log X))
    (hy10 : (10 : ℝ) ≤ y) (hygate : Real.sqrt (Real.log X) ≤ y)
    {C_cheb : ℝ} (hCheb : 0 ≤ C_cheb)
    (hgrain : ∀ l ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊,
        (∑ k ∈ Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊, vonMangoldt k)
          ≤ C_cheb * (h / (l : ℝ))) :
    ∃ C : ℝ, rampSliverMass g X h y ≤ C * (X / Real.log X) * Real.log y := by
  refine ⟨4 * C_cheb, ?_⟩
  -- basic regime facts
  set L : ℝ := Real.log X with hLdef
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hLpos : (0 : ℝ) < L := by linarith
  set sq : ℝ := Real.sqrt L with hsqdef
  have hsqpos : (0 : ℝ) < sq := Real.sqrt_pos.mpr hLpos
  have hsq1 : (1 : ℝ) ≤ sq := by
    rw [hsqdef, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hL1
  have hsqsq : sq * sq = L := Real.mul_self_sqrt hLpos.le
  have hhval : h = X / sq := by rw [hh, hsqdef]
  have hhpos : (0 : ℝ) < h := by rw [hhval]; positivity
  have hhnn : (0 : ℝ) ≤ h := hhpos.le
  have hhX : h ≤ X := by rw [hhval, div_le_iff₀ hsqpos]; nlinarith
  have hypos : (0 : ℝ) < y := by linarith
  have hy2 : (2 : ℝ) ≤ y := by linarith
  have hygate' : sq ≤ y := by rw [hsqdef]; exact hygate
  -- log(2y) ≤ 2 log y
  have hlogy_pos : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlog2y : Real.log (2 * y) ≤ 2 * Real.log y := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2
    linarith
  have hlog2y_nn : (0 : ℝ) ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  -- the per-partner bound `M`
  set M : ℝ := C_cheb * (h / y) * Real.log (2 * y) with hMdef
  have hM_nn : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  -- each `l`-fiber is `≤ M`
  have hfiber : ∀ l ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊,
      (∑ k ∈ Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊,
        ‖lambdaLin (restrictAbove y g) k‖ * ‖lambdaLin (restrictAbove y g) l‖) ≤ M := by
    intro l hl
    rw [Finset.mem_Ioc] at hl
    have hlgt : y < (l : ℝ) := by
      have := Nat.lt_floor_add_one y
      have hc : (⌊y⌋₊ : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hl.1
      linarith
    have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
    have hle2y : (l : ℝ) ≤ 2 * y := by
      have h1 : (l : ℝ) ≤ (⌊y + y * h / X⌋₊ : ℝ) := by exact_mod_cast hl.2
      have h2 : (⌊y + y * h / X⌋₊ : ℝ) ≤ y + y * h / X :=
        Nat.floor_le (by positivity)
      have h3 : y * h / X ≤ y := by
        rw [div_le_iff₀ hXpos]; nlinarith
      linarith
    -- factor out ‖Λ_ℓ l‖
    rw [← Finset.sum_mul]
    -- the k-sum ≤ C_cheb·(h/l) via lambdaLin ≤ Λ and the grain
    have hksum : (∑ k ∈ Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊,
        ‖lambdaLin (restrictAbove y g) k‖) ≤ C_cheb * (h / (l : ℝ)) := by
      refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (hgrain l (Finset.mem_Ioc.mpr hl))
      exact lambdaLin_norm_le (restrictAbove y g) (restrictAbove_norm_le hg) k
    have hksum_nn : (0 : ℝ) ≤ ∑ k ∈ Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊,
        ‖lambdaLin (restrictAbove y g) k‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    -- ‖Λ_ℓ l‖ ≤ log(2y)
    have hlmass : ‖lambdaLin (restrictAbove y g) l‖ ≤ Real.log (2 * y) :=
      le_trans (lambdaLin_norm_le (restrictAbove y g) (restrictAbove_norm_le hg) l)
        (le_trans vonMangoldt_le_log (Real.log_le_log hlpos hle2y))
    -- combine
    calc (∑ k ∈ Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊,
            ‖lambdaLin (restrictAbove y g) k‖) * ‖lambdaLin (restrictAbove y g) l‖
        ≤ (C_cheb * (h / (l : ℝ))) * Real.log (2 * y) :=
          mul_le_mul hksum hlmass (norm_nonneg _) (by positivity)
      _ ≤ (C_cheb * (h / y)) * Real.log (2 * y) := by
          gcongr
      _ = M := by rw [hMdef]
  -- sum over `l`, then the geometric assembly
  have hsum_le : rampSliverMass g X h y
      ≤ ((Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊).card : ℝ) * M := by
    rw [rampSliverMass]
    refine le_trans (Finset.sum_le_card_nsmul _ _ M hfiber) ?_
    rw [nsmul_eq_mul]
  refine le_trans hsum_le ?_
  -- (card)·M ≤ (y·h/X + 1)·M ≤ 4·C_cheb·(X/L)·log y
  have hcard := rampSliver_lcard_le (le_of_lt hypos) hhnn hXpos
  have hstep1 : ((Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊).card : ℝ) * M ≤ (y * h / X + 1) * M :=
    mul_le_mul_of_nonneg_right hcard hM_nn
  refine le_trans hstep1 ?_
  -- geometric part: (y·h/X + 1)·(h/y) ≤ 2·(X/L)
  have hgeom : (y * h / X + 1) * (h / y) ≤ 2 * (X / L) := by
    have hexp : (y * h / X + 1) * (h / y) = h * h / X + h / y := by
      field_simp
    rw [hexp]
    have h_hhX : h * h / X = X / L := by
      rw [hhval]; field_simp; nlinarith [hsqsq]
    have h_hy_le : h / y ≤ X / L := by
      rw [hhval, div_div]
      rw [div_le_div_iff₀ (by positivity) hLpos]
      nlinarith [hsqsq, mul_le_mul_of_nonneg_left hygate' hsqpos.le]
    rw [h_hhX]; linarith
  -- assemble: M = C_cheb·(h/y)·log(2y), so (y·h/X+1)·M = C_cheb·log(2y)·((y·h/X+1)·(h/y))
  have hrw : (y * h / X + 1) * M = C_cheb * Real.log (2 * y) * ((y * h / X + 1) * (h / y)) := by
    rw [hMdef]; ring
  rw [hrw]
  calc C_cheb * Real.log (2 * y) * ((y * h / X + 1) * (h / y))
      ≤ C_cheb * Real.log (2 * y) * (2 * (X / L)) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ C_cheb * (2 * Real.log y) * (2 * (X / L)) := by
        gcongr
    _ = 4 * C_cheb * (X / L) * Real.log y := by ring

end Salt.MR
