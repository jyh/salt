/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.MvSplit
import Salt.Twelve.QdiagBridge
import Salt.Twelve.FstarNorm
import Salt.Twelve.PrimorialRatio
import Salt.Twelve.Pigeonhole12
import Salt.Twelve.Certificate
import Salt.Twelve.BudgetPoly
import Salt.Twelve.Params
import Salt.Maynard.CollisionQuantW
import Salt.Maynard.EHLevelTheta
import Salt.Maynard.S2CompatEHW
import Salt.Maynard.Complete

/-!
# Rung 4a — W5-6: the ratio assembly and `gaps_le_twelve` (capstone)

Design: `docs/blueprints/explicit12-design.md`, card **W5-6**.  This is the
endgame assembly for the explicit bounded-prime-gaps rung.  It combines the
sharp `S1`/`S2` sieve bounds and the certified ratio `(θ★/2)·M₅ > 1` into the
sieve inequality `S₁ < Σ_m S₂ᵂ⁽ᵐ⁾`, and — via the free-`W'` diam-12 pigeonhole
(`bounded_gaps_reduces_twelve`, W5-5) — into `gaps_le_twelve`.

The result is landed CONDITIONAL on `S1InnerBound` (Node B, the sharp collision
atom, a separate sub-wave): the hypothesis `hInner` is threaded explicitly and
consumed by the sharp `S1` bound `sharp_S1_upperW`.

Load-bearing new content:
* `S1_lt_sum_S2mW` — the free-`W'`, `Qdiag`-form, per-`m` pigeonhole feeder
  (mirror of `Salt.Maynard.S1_lt_sum_S2m`).
* `sharp_S1_upperW` — the SHARP `S1` upper bound (the crude factor 2 is KILLED),
  consuming `hInner : S1InnerBound`.
* `theta_ratio_cert` — the load-bearing rational `4000·I(F★₁) < 1999·Σ J(F★₁)`
  (equivalently `1999·191881·1000 > 95820·2000²`), transported to `Fstar1`.
* `win_core'` — the ratio core producing `S1 < Σ S2mW`.
* `S2mW_ge_compatMain_theta_uniform` — the coupled-EH lemma at level `θ₊` (STEP 1;
  W5-3 deferred it).
-/

namespace Salt.Twelve

open Salt.Maynard

/-! ## The θ-ratio certificate

`Fstar1` is the ℓ¹-normalisation of `Fstar` (division of every coefficient by
`Qabs Fstar > 0`); both `Ical` and `Jcal` are degree-2 homogeneous, so the
certificate transports by the scale factor `(Qabs Fstar)⁻²` (a positive common
factor).  We replicate the `FstarNorm` scaling lemmas here (they are `private`
there) rather than re-run the 3136-monomial `norm_num`. -/

private def biQuadW (ker : (Fin 5 → ℕ) → (Fin 5 → ℕ) → ℚ) (F : Poly) : ℚ :=
  (F.map (fun p => (F.map (fun q => p.2 * q.2 * ker p.1 q.1)).sum)).sum

private lemma Ical_eq_biQuadW (F : Poly) : Ical F = biQuadW (fun a b => DInt (a + b)) F := rfl

private lemma Jcal_eq_biQuadW (m : Fin 5) (F : Poly) :
    Jcal m F = biQuadW (fun a b => JD a b m) F := rfl

private lemma biQuadW_scale (ker : (Fin 5 → ℕ) → (Fin 5 → ℕ) → ℚ) (F : Poly) (c : ℚ) :
    biQuadW ker (F.map (fun m => (m.1, m.2 * c))) = c ^ 2 * biQuadW ker F := by
  unfold biQuadW
  rw [List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  dsimp only [Function.comp]
  rw [List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
  dsimp only [Function.comp]
  ring

private lemma Ical_scaleW (F : Poly) (c : ℚ) :
    Ical (F.map (fun m => (m.1, m.2 * c))) = c ^ 2 * Ical F := by
  rw [Ical_eq_biQuadW, Ical_eq_biQuadW]; exact biQuadW_scale _ F c

private lemma Jcal_scaleW (m : Fin 5) (F : Poly) (c : ℚ) :
    Jcal m (F.map (fun n => (n.1, n.2 * c))) = c ^ 2 * Jcal m F := by
  rw [Jcal_eq_biQuadW, Jcal_eq_biQuadW]; exact biQuadW_scale _ F c

private lemma Fstar1_eq_scaleW : Fstar1 = Fstar.map (fun m => (m.1, m.2 * (Qabs Fstar)⁻¹)) := by
  unfold Fstar1; simp [div_eq_mul_inv]

private lemma Ical_Fstar1 : Ical Fstar1 = ((Qabs Fstar)⁻¹) ^ 2 * Ical Fstar := by
  rw [Fstar1_eq_scaleW]; exact Ical_scaleW Fstar _

private lemma Jsum_Fstar1 :
    (∑ m : Fin 5, Jcal m Fstar1) = ((Qabs Fstar)⁻¹) ^ 2 * ∑ m : Fin 5, Jcal m Fstar := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Fstar1_eq_scaleW]; exact Jcal_scaleW m Fstar _

/-- **The θ-ratio certificate** (the load-bearing rational).  With `θ★ = 1999/2000`
the pigeonhole needs `(θ★/2)·M₅ > 1`, i.e. `θ★·(Σ J)/I > 2`, i.e.
`1999·Σ J(F★₁) > 4000·I(F★₁)`.  Transported to `Fstar1` by the common positive
scale factor `(Qabs Fstar)⁻²`; the underlying `ℚ` inequality
`4000·(1597/399168) < 1999·(191881/23950080)` is `383280000 < 383570119`. -/
theorem theta_ratio_cert :
    (4000 : ℚ) * Ical Fstar1 < 1999 * ∑ m : Fin 5, Jcal m Fstar1 := by
  have hbase : (4000 : ℚ) * Ical Fstar < 1999 * ∑ m : Fin 5, Jcal m Fstar := by
    rw [I_Fstar, J_Fstar]; norm_num
  have hc : (0 : ℚ) < ((Qabs Fstar)⁻¹) ^ 2 := by
    have : (Qabs Fstar)⁻¹ ≠ 0 := inv_ne_zero Qabs_Fstar_pos.ne'
    positivity
  rw [Ical_Fstar1, Jsum_Fstar1]
  nlinarith [hbase, hc]

/-- **The sharp θ-ratio certificate** (with margin).  `1999·Σ J(F★₁) > 4003·I(F★₁)`
i.e. `M₅ > 4003/1999 = 2.002501` (certified `M₅ = 2.002515`); the extra `+3`
over `theta_ratio_cert`'s `4000` is the `7.6×10⁻⁴` slack that absorbs the level
(`ρ < θ★/2`) and prime-supply (`ε`) losses in the endgame ratio.  `4003` is the
largest integer numerator that works: `1999·191881 = 383570119` while
`4004·95820 = 383663280 > 383570119`. -/
theorem theta_ratio_cert_sharp :
    (4003 : ℚ) * Ical Fstar1 < 1999 * ∑ m : Fin 5, Jcal m Fstar1 := by
  have hbase : (4003 : ℚ) * Ical Fstar < 1999 * ∑ m : Fin 5, Jcal m Fstar := by
    rw [I_Fstar, J_Fstar]; norm_num
  have hc : (0 : ℚ) < ((Qabs Fstar)⁻¹) ^ 2 := by
    have : (Qabs Fstar)⁻¹ ≠ 0 := inv_ne_zero Qabs_Fstar_pos.ne'
    positivity
  rw [Ical_Fstar1, Jsum_Fstar1]
  nlinarith [hbase, hc]

/-- `I(F★₁) > 0` (a positive rational cast to `ℝ`), needed as the ratio base. -/
theorem Ical_Fstar1_pos : 0 < (Ical Fstar1 : ℝ) := by
  have hq : (0 : ℚ) < Ical Fstar1 := by
    rw [Ical_Fstar1, I_Fstar]
    have : (Qabs Fstar)⁻¹ ≠ 0 := inv_ne_zero Qabs_Fstar_pos.ne'
    positivity
  exact_mod_cast hq

/-! ## The ratio core (the load-bearing certified inequality)

Reduces `S₁ᵐᵃⁱⁿ < Σ_m S₂ᵐᵃⁱⁿ` (after cancelling the common `X⁵/W'` factor) to
the certified rational `1999·Σ J > 4003·I`, with the sharp-`S1` collision factor
`(1 + 300/D)` and the level/prime-supply lower bound `δ·log R ≥ 31.465·N'`
folded in.  Here `Nr = N'`, `δ`, `logR`, `I = I(F★₁)`, `SJ = Σ J(F★₁)`, and
`eps = 300/D`.  The `31465/1000 = 31.465 > 63·1999/4003 = 31.4606` gives the
strict margin; `M₅ = SJ/I > 4003/1999` supplies it. -/
theorem win_ratio_core (Nr δ logR I SJ eps : ℝ)
    (hIpos : 0 < I) (hSJcert : (4003 : ℝ) * I < 1999 * SJ)
    (hDL : (31465 : ℝ) / 1000 * Nr ≤ δ * logR)
    (hNr : 0 < Nr) (hepsle : eps ≤ 1 / 100000) :
    63 * Nr * (1 + eps) * I < δ * logR * SJ := by
  have hSJpos : 0 < SJ := by nlinarith [hSJcert, hIpos]
  have h1 : (δ * logR - 31465 / 1000 * Nr) * SJ ≥ 0 := mul_nonneg (by linarith) hSJpos.le
  have h2 : Nr * (1999 * SJ - 4003 * I) ≥ 0 := mul_nonneg hNr.le (by linarith)
  have h3 : eps * (Nr * I) ≤ (1 / 100000) * (Nr * I) :=
    mul_le_mul_of_nonneg_right hepsle (mul_nonneg hNr.le hIpos.le)
  have hC : 0 < Nr * I := mul_pos hNr hIpos
  nlinarith [h1, h2, h3, hC, hIpos, hNr, hSJpos]

/-! ## The pigeonhole feeder (free-`W'`, `Qdiag`-form, per-`m`)

Mirror of `Salt.Maynard.S1_lt_sum_S2m` at the free modulus `W'` and the sharp
`S2` diagonal `Qdiag_mW` (in place of `s2CompatFormM`), with per-`m` compat
lower bounds `cval` and per-`m` EH residuals `errEH`.  The `S2mW_lower` output
plugs directly into `hEHres`. -/
theorem S1_lt_sum_S2mW (K₀ N R ν₀ W' : ℕ) (y : (Fin 5 → ℕ) → ℝ)
    (δ : ℝ) (errEH cval : Fin 5 → ℝ)
    (hφ : 0 < (Nat.totient W' : ℝ)) (hcval : ∀ m : Fin 5, 0 ≤ cval m) (hδ0 : 0 ≤ δ)
    (hDpi : ∀ m : Fin 5, δ ≤ deltaPi 5 K₀ N m)
    (hcompat : ∀ m : Fin 5, cval m ≤ Qdiag_mW 5 R W' m y)
    (hEHres : ∀ m : Fin 5,
      deltaPi 5 K₀ N m / (Nat.totient W' : ℝ) * Qdiag_mW 5 R W' m y - errEH m
        ≤ S2mW 5 K₀ N R ν₀ W' m y)
    (hnum : S1 5 K₀ N R W' ν₀ y
      < (∑ m : Fin 5, δ / (Nat.totient W' : ℝ) * cval m) - ∑ m : Fin 5, errEH m) :
    S1 5 K₀ N R W' ν₀ y < ∑ m : Fin 5, S2mW 5 K₀ N R ν₀ W' m y := by
  have hlow : ∀ m : Fin 5,
      δ / (Nat.totient W' : ℝ) * cval m - errEH m ≤ S2mW 5 K₀ N R ν₀ W' m y := by
    intro m
    refine le_trans ?_ (hEHres m)
    have hDpinn : 0 ≤ deltaPi 5 K₀ N m := le_trans hδ0 (hDpi m)
    have hdiv : δ / (Nat.totient W' : ℝ) ≤ deltaPi 5 K₀ N m / (Nat.totient W' : ℝ) := by
      gcongr; exact hDpi m
    have hmain : δ / (Nat.totient W' : ℝ) * cval m
        ≤ deltaPi 5 K₀ N m / (Nat.totient W' : ℝ) * Qdiag_mW 5 R W' m y :=
      mul_le_mul hdiv (hcompat m) (hcval m) (div_nonneg hDpinn hφ.le)
    linarith
  calc S1 5 K₀ N R W' ν₀ y
      < (∑ m : Fin 5, δ / (Nat.totient W' : ℝ) * cval m) - ∑ m : Fin 5, errEH m := hnum
    _ = ∑ m : Fin 5, (δ / (Nat.totient W' : ℝ) * cval m - errEH m) := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ m : Fin 5, S2mW 5 K₀ N R ν₀ W' m y := Finset.sum_le_sum (fun m _ => hlow m)

/-! ## The sharp `S1` upper bound (factor 2 KILLED)

`S1_upper_of` keeps the crude `2·main`, which is fatal at the certified slack
`7.6×10⁻⁴`.  Instead we route through `S1_le_main_add_errorW` (the un-collapsed
`s1CompatForm` main) and the collision decomposition
`s1CompatForm = yside − s1CollisionForm` (`s1_compat_eq`), bounded by the sharp
collision estimate `collision_lower_orderW_of` (which consumes `hInner`):
`|s1CollisionForm| ≤ (12k²/D)·yside`.  Hence `s1CompatForm ≤ (1 + 12k²/D)·yside`
— the factor tends to `1` as `D → ∞`, no factor of 2. -/
theorem sharp_S1_upperW (k K₀ N R W' ν₀ D : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy0 : ∀ r, r ∉ kSieveIndex k R W' → y r = 0)
    (hInner : S1InnerBound k R W' y)
    (hW' : Squarefree W') (hK₀ : 1 ≤ K₀)
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hlt : ∀ i : Fin k, hSeq k i < D)
    (hk : 1 ≤ k) (hDk : 12 * k ^ 2 ≤ D)
    (hsol : ∀ d ∈ kSieveIndex k R W', ∀ e ∈ kSieveIndex k R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W' = ν₀ % W' ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i)) :
    S1 k K₀ N R W' ν₀ y
      ≤ ((K₀ - 1) * N / W' : ℝ)
          * ((1 + 12 * (k : ℝ) ^ 2 / D)
              * ∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := by
  have hL2 := S1_le_main_add_errorW k K₀ N R W' ν₀ D y hW' hK₀ hDlt hlt hsol
  have hcompat_eq := s1_compat_eq k R W' y hy0
  have hcoll := collision_lower_orderW_of k R W' D y hy0 hInner hDlt hk hDk
  set yside := ∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) with hys
  have hcoeff : (0 : ℝ) ≤ ((K₀ - 1) * N / W' : ℝ) := by
    have h1 : (0 : ℝ) ≤ (K₀ : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
      linarith
    exact div_nonneg (mul_nonneg h1 (by positivity)) (by positivity)
  have hcompat_le : s1CompatForm k R W' y ≤ (1 + 12 * (k : ℝ) ^ 2 / D) * yside := by
    rw [hcompat_eq]
    have h1 : - s1CollisionForm k R W' y ≤ |s1CollisionForm k R W' y| := neg_le_abs _
    have hexp : (1 + 12 * (k : ℝ) ^ 2 / D) * yside = yside + 12 * (k : ℝ) ^ 2 / D * yside := by
      ring
    linarith [hcoll, h1, hexp.le, hexp.ge]
  calc S1 k K₀ N R W' ν₀ y
      ≤ ((K₀ - 1) * N / W' : ℝ) * s1CompatForm k R W' y
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := hL2
    _ ≤ ((K₀ - 1) * N / W' : ℝ) * ((1 + 12 * (k : ℝ) ^ 2 / D) * yside)
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hcompat_le hcoeff) (le_refl _)

/-! ## STEP 1 — the coupled-EH lemma at level `θ₊` (`S2mW_ge_compatMain_theta_uniform`)

W5-3 deferred this to the endgame; it is landed here.  It is the free-`W'`,
`|y| ≤ 1` mirror of `Salt.Maynard.S2m_ge_compatMain_lod_uniform`
(`LevelConsume.lean:326`), consuming `lod_error_pow_theta` (W5-2) at level
`θ₊ = 3999/4000`, `abs_S2mW_sub_compatMainW_le_disc_R_uniform` and
`compat_pair_fiber_leW` (W5-3), with `range_haircut_mono_theta` (W5-2). -/
theorem S2mW_ge_compatMain_theta_uniform (k K₀ W' D : ℕ) (hk : 1 ≤ k) (hK₀ : 1 ≤ K₀)
    (hW' : Squarefree W') (hD : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D ≤ p)
    (hlt : ∀ i : Fin k, hSeq k i < D) (hLoD : HasLevel (3999 / 4000)) :
    ∃ (C₀ B' : ℝ) (N₀ : ℕ), 0 ≤ C₀ ∧ 0 ≤ B' ∧
      ∀ (R ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ), 2 ≤ R → (∀ r, |y r| ≤ 1) →
        (∀ h ∈ H k, Nat.Coprime (ν₀ + h) W') →
        ∀ N : ℕ, N₀ ≤ N → R ≤ N →
          (W' * R ^ 2 ≤ ⌊(N : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log N) ^ B'⌋₊) →
        ∀ m : Fin k,
          S2mW k K₀ N R ν₀ W' m y
            ≥ deltaPi k K₀ N m / (Nat.totient W' : ℝ) * s2CompatFormM k R W' m y
              - C₀ * (1 + Real.log R) ^ (2 * k + 2) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
  classical
  obtain ⟨Clam, hClam0, hdisc⟩ :=
    abs_S2mW_sub_compatMainW_le_disc_R_uniform k K₀ W' D hK₀ hW' hD hlt
  obtain ⟨C, B', N₁, hB'0, hEHb⟩ := lod_error_pow_theta k (2 * k + 4) (by omega) hLoD
  have hCnn : 0 ≤ C := by
    set x₀ := max N₁ 2 with hx₀
    have hmax2 : 2 ≤ x₀ := le_max_right N₁ 2
    have hb := hEHb x₀ (le_max_left N₁ 2)
    have hx0pos : 0 < x₀ := by omega
    have hlogx0 : 0 < Real.log x₀ :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < x₀ by omega))
    have hLHS0 : (0 : ℝ) ≤ ∑ q ∈ (Finset.range (⌊(x₀ : ℝ) ^ (3999 / 4000 : ℝ)
          / (Real.log x₀) ^ B'⌋₊ + 1)).filter Squarefree,
        (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x₀ q :=
      Finset.sum_nonneg (fun q _ => mul_nonneg (by positivity) (maxDiscrepancy_nonneg x₀ q))
    have hpos : 0 < (x₀ : ℝ) / (Real.log x₀) ^ (2 * k + 4) :=
      div_pos (by exact_mod_cast hx0pos) (pow_pos hlogx0 _)
    by_contra hCneg
    have hbad : C * (x₀ : ℝ) / (Real.log x₀) ^ (2 * k + 4) < 0 := by
      rw [mul_div_assoc]; exact mul_neg_of_neg_of_pos (not_le.mp hCneg) hpos
    linarith [hLHS0, hb, hbad]
  refine ⟨2 * Clam ^ 2 * C * ((K₀ : ℝ) + 1), B',
    max (max (max 2 N₁) (D₀ k)) ⌈Real.exp (2 * B')⌉₊, ?_, hB'0, ?_⟩
  · have h1 : (0 : ℝ) ≤ 2 * Clam ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg h1 hCnn) (by positivity)
  intro R ν₀ y hR hy1 hν₀ N hN0 hRN hrange m
  have hlogR : (0 : ℝ) ≤ Real.log R :=
    Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ R))
  have hN0a : max (max 2 N₁) (D₀ k) ≤ N := le_trans (le_max_left _ _) hN0
  have hle2N1 : max 2 N₁ ≤ N := le_trans (le_max_left _ _) hN0a
  have hD0N : D₀ k ≤ N := le_trans (le_max_right _ _) hN0a
  have hexp2N : ⌈Real.exp (2 * B')⌉₊ ≤ N := le_trans (le_max_right _ _) hN0
  have h2N : 2 ≤ N := le_trans (le_max_left 2 N₁) hle2N1
  have hN1N : N₁ ≤ N := le_trans (le_max_right 2 N₁) hle2N1
  have hNpos : 0 < N := by omega
  have hhm : hSeq k m ≤ N := le_trans (hSeq_le_D₀ k m) hD0N
  have hNleK0N : N ≤ K₀ * N := Nat.le_mul_of_pos_left N (by omega)
  have hlogN0 : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show (1 : ℕ) < N by omega))
  have hlogN2B' : 2 * B' ≤ Real.log N := by
    have h1 : Real.exp (2 * B') ≤ (N : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hexp2N)
    calc 2 * B' = Real.log (Real.exp (2 * B')) := (Real.log_exp _).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos _) h1
  have endpoint : ∀ x : ℕ, N ≤ x → x ≤ (K₀ + 1) * N →
      ∑ q ∈ (Finset.range (W' * R ^ 2 + 1)).filter Squarefree,
          (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x q
        ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    intro x hNx hxub
    have hNxr : (N : ℝ) ≤ (x : ℝ) := by exact_mod_cast hNx
    have hmono : ⌊(N : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log N) ^ B'⌋₊
        ≤ ⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log x) ^ B'⌋₊ :=
      Nat.floor_mono (range_haircut_mono_theta B' hB'0 N x h2N hNx hlogN2B')
    have hWRx : W' * R ^ 2 ≤ ⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log x) ^ B'⌋₊ :=
      le_trans hrange hmono
    have hsub : (Finset.range (W' * R ^ 2 + 1)).filter Squarefree
        ⊆ (Finset.range (⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log x) ^ B'⌋₊ + 1)).filter
            Squarefree :=
      Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (by omega))
    have hlogx0 : 0 < Real.log x :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < x by omega))
    have hlogxN : Real.log N ≤ Real.log x := Real.log_le_log (by exact_mod_cast hNpos) hNxr
    have hd1pos : 0 < (Real.log x) ^ (2 * k + 4) := pow_pos hlogx0 _
    have hd2pos : 0 < (Real.log N) ^ (2 * k + 4) := pow_pos hlogN0 _
    have hd21 : (Real.log N) ^ (2 * k + 4) ≤ (Real.log x) ^ (2 * k + 4) :=
      pow_le_pow_left₀ hlogN0.le hlogxN _
    calc ∑ q ∈ (Finset.range (W' * R ^ 2 + 1)).filter Squarefree,
            (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x q
        ≤ ∑ q ∈ (Finset.range (⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log x) ^ B'⌋₊ + 1)).filter
            Squarefree, (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun q _ _ => mul_nonneg (by positivity) (maxDiscrepancy_nonneg x q))
      _ ≤ C * (x : ℝ) / (Real.log x) ^ (2 * k + 4) := hEHb x (le_trans hN1N hNx)
      _ ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
          rw [div_le_div_iff₀ hd1pos hd2pos]
          have hxubr : (x : ℝ) ≤ ((K₀ : ℝ) + 1) * (N : ℝ) := by exact_mod_cast hxub
          have step_num : C * (x : ℝ) ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) := by
            calc C * (x : ℝ) ≤ C * (((K₀ : ℝ) + 1) * (N : ℝ)) :=
                  mul_le_mul_of_nonneg_left hxubr hCnn
              _ = C * ((K₀ : ℝ) + 1) * (N : ℝ) := by ring
          have hcnum : 0 ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) :=
            mul_nonneg (mul_nonneg hCnn (by positivity)) (by positivity)
          exact mul_le_mul step_num hd21 (pow_nonneg hlogN0.le _) hcnum
  have hexp : (K₀ + 1) * N = K₀ * N + N := by ring
  have hx1lb : N ≤ K₀ * N + hSeq k m := le_trans hNleK0N (Nat.le_add_right _ _)
  have hx1ub : K₀ * N + hSeq k m ≤ (K₀ + 1) * N := by rw [hexp]; omega
  have hx2ub : N + hSeq k m ≤ (K₀ + 1) * N := by rw [hexp]; omega
  have hEP1 := endpoint (K₀ * N + hSeq k m) hx1lb hx1ub
  have hEP2 := endpoint (N + hSeq k m) (Nat.le_add_right _ _) hx2ub
  have hfib1 := compat_pair_fiber_leW k R W' hW' m
    (fun q => maxDiscrepancy (K₀ * N + hSeq k m) q)
    (fun q => maxDiscrepancy_nonneg (K₀ * N + hSeq k m) q)
  have hfib2 := compat_pair_fiber_leW k R W' hW' m
    (fun q => maxDiscrepancy (N + hSeq k m) q)
    (fun q => maxDiscrepancy_nonneg (N + hSeq k m) q)
  have hsplit : (∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
          (if IsCollisionPair d e then 0
           else maxDiscrepancy (K₀ * N + hSeq k m) (qModW k W' d e)
                + maxDiscrepancy (N + hSeq k m) (qModW k W' d e)))
      = (∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
          ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
            (if IsCollisionPair d e then 0
             else maxDiscrepancy (K₀ * N + hSeq k m) (qModW k W' d e)))
        + (∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
            ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
              (if IsCollisionPair d e then 0
               else maxDiscrepancy (N + hSeq k m) (qModW k W' d e))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases hcol : IsCollisionPair d e
    · simp only [if_pos hcol, add_zero]
    · simp only [if_neg hcol]
  have hDiscSum : (∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
          (if IsCollisionPair d e then 0
           else maxDiscrepancy (K₀ * N + hSeq k m) (qModW k W' d e)
                + maxDiscrepancy (N + hSeq k m) (qModW k W' d e)))
      ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4)
        + C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    rw [hsplit]
    exact add_le_add (le_trans hfib1 hEP1) (le_trans hfib2 hEP2)
  have hLnn : 0 ≤ Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2) :=
    mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) _)
  have hfinal : |S2mW k K₀ N R ν₀ W' m y
        - deltaPi k K₀ N m / (Nat.totient W' : ℝ) * s2CompatFormM k R W' m y|
      ≤ 2 * Clam ^ 2 * C * ((K₀ : ℝ) + 1) * (1 + Real.log R) ^ (2 * k + 2)
          * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    refine le_trans (hdisc R ν₀ y hR hy1 hν₀ m N hRN) ?_
    calc Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2)
          * (∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
              ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
                (if IsCollisionPair d e then 0
                 else maxDiscrepancy (K₀ * N + hSeq k m) (qModW k W' d e)
                      + maxDiscrepancy (N + hSeq k m) (qModW k W' d e)))
        ≤ Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2)
            * (C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4)
              + C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4)) :=
          mul_le_mul_of_nonneg_left hDiscSum hLnn
      _ = 2 * Clam ^ 2 * C * ((K₀ : ℝ) + 1) * (1 + Real.log R) ^ (2 * k + 2)
            * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by ring
  have := (abs_le.mp hfinal).1
  linarith

/-! ## `win_core'` — the sieve inequality `S₁ < Σ_m S₂ᵂ⁽ᵐ⁾`

The ratio assembly.  Consumes `hInner` through `sharp_S1_upperW` (the factor-2-
killed `S1` upper bound), then reduces to the single numeric ratio-slack `hslack`
via `S1_lt_sum_S2mW`.  `hslack` is exactly the assembled ratio: the sharp `S1`
main (with collision factor `1 + 300/D`) below `Σ_m (δ/φW')·cval m − Σ errEH`,
budgeted `∀ᶠ N`.  Its discharge is the certified `win_ratio_core` (main
comparison) plus the vanishing error budget (see the design's error-budget
table); that `∀ᶠ`-largeness is the frontier assembly (STEP 6). -/
theorem win_core' (N' R ν₀ W' D : ℕ) (δ : ℝ) (errEH cval : Fin 5 → ℝ)
    (hInner : S1InnerBound 5 R W' (yF R W' Fstar1))
    (hW' : Squarefree W')
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hlt : ∀ i : Fin 5, hSeq 5 i < D)
    (hDk : 300 ≤ D)
    (hsol : ∀ d ∈ kSieveIndex 5 R W', ∀ e ∈ kSieveIndex 5 R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W' = ν₀ % W' ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq 5 i))
    (hφpos : 0 < (Nat.totient W' : ℝ)) (hcval : ∀ m : Fin 5, 0 ≤ cval m) (hδ0 : 0 ≤ δ)
    (hDpi : ∀ m : Fin 5, δ ≤ deltaPi 5 64 N' m)
    (hQlow : ∀ m : Fin 5, cval m ≤ Qdiag_mW 5 R W' m (yF R W' Fstar1))
    (hS2low : ∀ m : Fin 5,
      deltaPi 5 64 N' m / (Nat.totient W' : ℝ) * Qdiag_mW 5 R W' m (yF R W' Fstar1) - errEH m
        ≤ S2mW 5 64 N' R ν₀ W' m (yF R W' Fstar1))
    (hslack :
      ((64 - 1) * N' / W' : ℝ)
          * ((1 + 12 * (5 : ℝ) ^ 2 / D)
              * ∑ r ∈ kSieveIndex 5 R W',
                  (yF R W' Fstar1 r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (5 + 1) * (∑ d ∈ kSieveIndex 5 R W', |lam 5 R W' (yF R W' Fstar1) d|) ^ 2
        < (∑ m : Fin 5, δ / (Nat.totient W' : ℝ) * cval m) - ∑ m : Fin 5, errEH m) :
    S1 5 64 N' R W' ν₀ (yF R W' Fstar1)
      < ∑ m : Fin 5, S2mW 5 64 N' R ν₀ W' m (yF R W' Fstar1) := by
  have hy0 : ∀ r, r ∉ kSieveIndex 5 R W' → yF R W' Fstar1 r = 0 := by
    intro r hr; rw [yF]; simp only [if_neg hr]
  have hS1sharp := sharp_S1_upperW 5 64 N' R W' ν₀ D (yF R W' Fstar1) hy0 hInner hW'
    (by norm_num) hDlt hlt (by norm_num) (by omega : 12 * 5 ^ 2 ≤ D) hsol
  have hnum : S1 5 64 N' R W' ν₀ (yF R W' Fstar1)
      < (∑ m : Fin 5, δ / (Nat.totient W' : ℝ) * cval m) - ∑ m : Fin 5, errEH m :=
    lt_of_le_of_lt hS1sharp hslack
  exact S1_lt_sum_S2mW 64 N' R ν₀ W' (yF R W' Fstar1) δ errEH cval hφpos hcval hδ0 hDpi
    hQlow hS2low hnum

/-! ## The capstone `gaps_le_twelve_of_inner`

The Archimedean primorial cutoff `Dstar`.  Its role: `Dstar ≥ 300 = 12·5²`
(required by the `*W` collision spine and `qdiag_bridge`), and — for the frontier
discharge — `300/Dstar ≤ 10⁻⁵` so the sharp-`S1` collision factor `1 + 300/Dstar`
sits inside `win_ratio_core`'s `eps`-budget.  The precise value is the
`primorial_ratio_le`-driven Archimedean constant (`κ⁻¹ ≤ 5√Dstar`, the F-only
`A`-constants of `mv_I_split`/`qdiag_bridge`); `3·10⁷` is a concrete value in
that regime.  (The exact Archimedes step is part of the flagged frontier
discharge — see the module note.) -/
def Dstar : ℕ := 30000000

private lemma prod_primes_squarefreeW {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hap : a.Prime := hs a (Finset.mem_insert_self a s)
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hap (hsp p hp)).mpr (by rintro rfl; exact ha hp)
    rw [Nat.squarefree_mul_iff]
    exact ⟨hcop, hap.squarefree, ih hsp⟩

private lemma primorial_squarefreeW (D : ℕ) : Squarefree (primorial D) := by
  unfold primorial
  exact prod_primes_squarefreeW (fun p hp => (Finset.mem_filter.mp hp).2)

private lemma hSeq_lt_Dstar (i : Fin 5) : hSeq 5 i < Dstar := by
  unfold Dstar
  fin_cases i <;>
    simp only [hSeq_five_zero, hSeq_five_one, hSeq_five_two, hSeq_five_three,
      hSeq_five_four] <;>
    norm_num

/-- **The analytic frontier** (`WinFrontier`, the `∀ N ∃ N'≥N` largeness).
Given `WindowPNT` and `EHall`, for every window base `N` there is `N' ≥ N` and
sieve parameters `R, ν₀, δ, errEH, cval` at which ALL of `win_core'`'s analytic
inputs hold: the CRT collision-solvability, the per-`m` `Δπ` lower bound, the
sharp `Qdiag` lower bound (`cval m ≤ Qdiag`, from `qdiag_bridge`), the `S2ᵂ`
lower bound (`S2mW_lower` with the `θ₊`-level `herr` of
`S2mW_ge_compatMain_theta_uniform`), and the assembled ratio-slack `hslack`
(discharged by `win_ratio_core` + the vanishing `∀ᶠ`/`1/D`/`1/log R` error
budget, `mv_I_split`/`qdiag_bridge`).  This is the endgame's STEP-6 largeness
bundle — a mirror of `Salt.Maynard.analyticFrontier_lod` at level `θ★`; it is
carried as a hypothesis here (the `∀ᶠ N` largeness discharge is deferred to the
FABLE-QUEUE, per the W5-6 PB-floor). -/
def WinFrontier (W' : ℕ) : Prop :=
  WindowPNT → EHall → ∀ N : ℕ, ∃ (N' R ν₀ : ℕ) (δ : ℝ) (errEH cval : Fin 5 → ℝ), N ≤ N' ∧
    (∀ d ∈ kSieveIndex 5 R W', ∀ e ∈ kSieveIndex 5 R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W' = ν₀ % W' ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq 5 i)) ∧
    0 < (Nat.totient W' : ℝ) ∧ (∀ m : Fin 5, 0 ≤ cval m) ∧ 0 ≤ δ ∧
    (∀ m : Fin 5, δ ≤ deltaPi 5 64 N' m) ∧
    (∀ m : Fin 5, cval m ≤ Qdiag_mW 5 R W' m (yF R W' Fstar1)) ∧
    (∀ m : Fin 5,
      deltaPi 5 64 N' m / (Nat.totient W' : ℝ) * Qdiag_mW 5 R W' m (yF R W' Fstar1) - errEH m
        ≤ S2mW 5 64 N' R ν₀ W' m (yF R W' Fstar1)) ∧
    (((64 - 1) * N' / W' : ℝ)
          * ((1 + 12 * (5 : ℝ) ^ 2 / Dstar)
              * ∑ r ∈ kSieveIndex 5 R W',
                  (yF R W' Fstar1 r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (5 + 1) * (∑ d ∈ kSieveIndex 5 R W', |lam 5 R W' (yF R W' Fstar1) d|) ^ 2
        < (∑ m : Fin 5, δ / (Nat.totient W' : ℝ) * cval m) - ∑ m : Fin 5, errEH m)

/-- **W5-6 capstone (conditional on Node B).**  Explicit bounded prime gaps
`≤ 12`: for every `N` there are two primes `p ≠ q > N` with `|q − p| ≤ 12`.
CONDITIONAL on `hInner` (the sharp `S1` collision atom `S1InnerBound` for the
Maynard polynomial weight `yF Fstar1` — Node B, a separate sub-wave) and on the
`WinFrontier` largeness bundle (STEP 6, the `∀ᶠ N` mirror of
`analyticFrontier_lod`; flagged).  Assembled via the free-`W'` diam-12
pigeonhole `bounded_gaps_reduces_twelve` at `W' = primorial Dstar`, with each
window's sieve inequality produced by `win_core'` (which consumes `hInner`
through the factor-2-killed `sharp_S1_upperW`, and the certified ratio
`(θ★/2)·M₅ > 1` via `win_ratio_core`/`theta_ratio_cert`). -/
theorem gaps_le_twelve_of_inner (hPNT : WindowPNT) (hEH : EHall)
    (hInner : ∀ R : ℕ, S1InnerBound 5 R (primorial Dstar) (yF R (primorial Dstar) Fstar1))
    (hFrontier : WinFrontier (primorial Dstar)) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-12 : ℤ) 12 := by
  refine bounded_gaps_reduces_twelve (primorial Dstar) (fun N => ?_)
  obtain ⟨N', R, ν₀, δ, errEH, cval, hNN', hsol, hφpos, hcvnn, hδ0, hDpi, hQlow,
    hS2low, hslack⟩ := hFrontier hPNT hEH N
  refine ⟨N', R, ν₀, yF R (primorial Dstar) Fstar1, hNN', ?_⟩
  exact win_core' N' R ν₀ (primorial Dstar) Dstar δ errEH cval (hInner R)
    (primorial_squarefreeW Dstar) (primorial_hDlt Dstar) hSeq_lt_Dstar
    (by unfold Dstar; norm_num) hsol hφpos hcvnn hδ0 hDpi hQlow hS2low hslack

end Salt.Twelve
