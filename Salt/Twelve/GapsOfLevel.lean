/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.GapsUncond

/-!
# Q3b — the equidistribution interface for bounded gaps ≤ 12

Sprint question Q3 (`docs/exploration/preregistration.md`), executed as option
(b) per the Q3 Fable adjudication (`docs/exploration/pilot.md`): *extract the
weakest precisely-stated equidistribution interface that the landed gaps ≤ 12
chain actually consumes.*

**The find (Q3-recon, verbatim from the ledger).**  The ENTIRE gaps ≤ 12 chain
consumes `EHall` at EXACTLY ONE LINE (`Salt/Twelve/FrontierM.lean:171`), reducing
to the landed `HasLevel (3999/4000)` — strictly weaker in FORM (single level +
BV-shaped haircut; the honest caveat: θ ≈ 1 is EH-strength in DEPTH).

This file lands that reduction as a kernel-checked interface theorem.

## The interface theorem, in classical notation

Write `θ★ = 3999/4000`.  `HasLevel θ★` is the statement that the primes have a
Bombieri–Vinogradov-shaped *level of distribution* `θ★`: for every `A > 0` there
is a `B ≥ 0` and a constant `C` with

  `∑_{q ≤ x^{θ★}/(log x)^B} max_{(a,q)=1} |ψ(x; q, a) − x/φ(q)| ≤ C · x/(log x)^A`

(the corpus's `HasLevel` is phrased with `maxDiscrepancy` and the
`⌊x^θ/(log x)^B⌋₊` cutoff — `Salt/Maynard/Level.lean`).  The interface theorem is

  `gaps_le_twelve_of_hasLevel : WindowPNT → HasLevel (3999/4000) →`
  `  ∀ N, ∃ p ≠ q > N primes with |q − p| ≤ 12`,

and the landed unconditional capstone `gaps_le_twelve` is recovered from it as
the `EHall`-instance (`gaps_le_twelve_of_EHall` below), via the corpus's
`EH_hasLevel ∘ EHall_hasEH` composition — the anti-vacuity check: the old
theorem IS an instance of the new one.

## The θ-caveat (READ THIS)

The minimality here is of **FORM, not of analytic depth**.  `θ★ = 3999/4000` is
*near 1*, so `HasLevel θ★` is EH-strength: assuming a level of distribution this
close to `1` is, in analytic content, of the same difficulty as the
Elliott–Halberstam conjecture itself (the honestly-recorded gap between what is
unconditionally known — Bombieri–Vinogradov gives `θ < 1/2` — and what the
chain requires).  What the extraction genuinely buys is a **single-level,
BV-shaped** hypothesis (`HasLevel θ★`, one level + a `(log x)^B` modulus haircut)
in place of the folklore `∀θ < 1` shape of `EHall` (and the density/smoothing
apparatus of `GEH`).  It is NOT a weakening of the equidistribution range.  Any
literature-facing quotation of this theorem must carry the caveat: the interface
is minimal in shape, and remains EH-strength in depth.

## Precedent in the corpus

The θ = 1/2 instance of the very same interface pattern is already landed:

  `Salt.Maynard.bounded_gaps_from_level : HasLevel (1/2) → ∃ C, ∀ N, …`

(`Salt/Maynard/LevelConsume.lean`), the LoD-shaped bounded-gaps capstone that
consumes exactly one `HasLevel` and recovers the EH form via the same
`EH_hasLevel` composition (`bounded_gaps_from_eh'`).  `gaps_le_twelve_of_hasLevel`
is the θ = θ★ = 3999/4000 instance of that pattern, specialized to the explicit
diameter `12`.

## Structure

`winFrontierMW_of_hasLevel` is the `HasLevel (3999/4000)`-parameterized variant
of `winFrontierMW_of` (`Salt/Twelve/FrontierM.lean`): the body is copied verbatim
with the single `EHall → HasLevel` derivation line deleted and `hLoD` taken as a
hypothesis, producing the `EHall`-free largeness bundle `WinFrontierMWL`.  The
capstone `gaps_le_twelve_of_hasLevel` then mirrors `gaps_le_twelve`
(`Salt/Twelve/GapsUncond.lean`) through this bundle.  (The two private helpers of
`FrontierM` are file-scoped, so they are re-proved here.)
-/

namespace Salt.Twelve

open Salt.Maynard
open Finset Filter

/-! ## Local helpers (file-scoped mirrors of `FrontierM`'s private lemmas) -/

/-- Non-collision pairs have pairwise-coprime lcm coordinates (free `W'`; mirror
of `FrontierM`'s private helper of the same shape). -/
private lemma lcm_pairwise_coprime_of_noncollision {R W' : ℕ} {d e : Fin 5 → ℕ}
    (hd : d ∈ kSieveIndex 5 R W') (he : e ∈ kSieveIndex 5 R W')
    (hcompat : ¬ IsCollisionPair d e) {i j : Fin 5} (hij : i ≠ j) :
    Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j)) := by
  obtain ⟨-, hdcop, -, -⟩ := (mem_kSieveIndex_iff d).mp hd
  obtain ⟨-, hecop, -, -⟩ := (mem_kSieveIndex_iff e).mp he
  have hnc : ∀ a b : Fin 5, a ≠ b → Nat.Coprime (d a) (e b) := by
    intro a b hab
    by_contra h
    exact hcompat ⟨a, b, hab, h⟩
  apply Nat.coprime_of_dvd
  intro p hp hpi hpj
  have hi : p ∣ d i ∨ p ∣ e i := (Nat.Prime.dvd_mul hp).mp (hpi.trans (Nat.lcm_dvd_mul _ _))
  have hj : p ∣ d j ∨ p ∣ e j := (Nat.Prime.dvd_mul hp).mp (hpj.trans (Nat.lcm_dvd_mul _ _))
  rcases hi with hdi | hei <;> rcases hj with hdj | hej
  · exact absurd (hdcop i j hij) (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hdi, hdj⟩)
  · exact absurd (hnc i j hij) (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hdi, hej⟩)
  · exact absurd (hnc j i hij.symm) (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hdj, hei⟩)
  · exact absurd (hecop i j hij) (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hei, hej⟩)

private lemma hSeq_le_nineteen (i : Fin 5) : hSeq 5 i ≤ 19 := by
  fin_cases i <;>
    simp only [hSeq_five_zero, hSeq_five_one, hSeq_five_two, hSeq_five_three,
      hSeq_five_four] <;>
    norm_num

/-! ## The `EHall`-free largeness bundle `WinFrontierMWL` (parameterized by `D`)

Byte-mirror of `FrontierM`'s `WinFrontierMW` with the leading `EHall →` deleted:
the largeness bundle needs only `HasLevel (3999/4000)`, not `EHall`. -/
def WinFrontierMWL (D : ℕ) : Prop :=
  WindowPNT → ∀ N : ℕ,
    ∃ (N' R ν₀ : ℕ) (δ : ℝ) (errEH cval : Fin 5 → ℝ), N ≤ N' ∧
    (∀ d ∈ kSieveIndex 5 R (primorial D), ∀ e ∈ kSieveIndex 5 R (primorial D),
      ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % (primorial D) = ν₀ % (primorial D) ∧
        ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq 5 i)) ∧
    0 < (Nat.totient (primorial D) : ℝ) ∧ (∀ m : Fin 5, 0 ≤ cval m) ∧ 0 ≤ δ ∧
    (∀ m : Fin 5, δ ≤ deltaPi 5 64 N' m) ∧
    (∀ m : Fin 5,
      cval m ≤ Qdiag_mW 5 R (primorial D) m (yF R (primorial D) Fstar1)) ∧
    (∀ m : Fin 5,
      deltaPi 5 64 N' m / (Nat.totient (primorial D) : ℝ)
          * Qdiag_mW 5 R (primorial D) m (yF R (primorial D) Fstar1) - errEH m
        ≤ S2mW 5 64 N' R ν₀ (primorial D) m (yF R (primorial D) Fstar1)) ∧
    (((64 - 1) * N' / (primorial D) : ℝ)
          * ((∑ r ∈ kSieveIndex 5 R (primorial D),
                  (yF R (primorial D) Fstar1 r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
              + 12 * (5 : ℝ) ^ 2 / D
                  * ∑ r ∈ kSieveIndex 5 R (primorial D),
                      1 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (5 + 1)
            * (∑ d ∈ kSieveIndex 5 R (primorial D),
                |lam 5 R (primorial D) (yF R (primorial D) Fstar1) d|) ^ 2
        < (∑ m : Fin 5,
              δ / (Nat.totient (primorial D) : ℝ) * cval m) - ∑ m : Fin 5, errEH m)

/-! ## `winFrontierMW_of_hasLevel` — the discharge from `HasLevel (3999/4000)` -/

/-- **Q3b (the interface extraction).**  The `HasLevel (3999/4000)`-parameterized
variant of `winFrontierMW_of` (`Salt/Twelve/FrontierM.lean`).  The body is that
of `winFrontierMW_of` with the single `EHall → HasLevel` derivation line deleted
and `hLoD : HasLevel (3999/4000)` taken as a hypothesis — witnessing that the
largeness bundle consumes `EHall` at exactly that one point.  Produces the
`EHall`-free bundle `WinFrontierMWL D` for `W' = primorial D` (any cutoff
`D ≥ 300`); the conjunct-7 slack is still carried as the `∀ᶠ`-hypothesis
`hslackEv`. -/
theorem winFrontierMW_of_hasLevel (D : ℕ) (hD : 300 ≤ D)
    (hLoD : HasLevel (3999 / 4000))
    (hslackEv : ∀ C₀ : ℝ, 0 ≤ C₀ → ∀ᶠ N' : ℕ in atTop, WinSlackM D C₀ N') :
    WinFrontierMWL D := by
  intro hPNT N
  classical
  -- modulus facts
  have hW'sqf : Squarefree (primorial D) := primorial_sqf' D
  have hW'pos : 0 < primorial D := primorial_pos'' D
  have hW'ne : (primorial D) ≠ 0 := hW'pos.ne'
  have hφW'pos : (0 : ℝ) < (Nat.totient (primorial D) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hW'pos
  have hDle : ∀ p : ℕ, p.Prime → ¬ p ∣ primorial D → D ≤ p :=
    fun p hp hnd => le_of_lt (primorial_hDlt D p hp hnd)
  have hSeqlt : ∀ i : Fin 5, hSeq 5 i < D := fun i => by
    have := hSeq_le_nineteen i; omega
  -- CRT residue base
  obtain ⟨ν₀, hν₀⟩ := exists_nu0W 5 (primorial D) hW'ne
  -- the θ₊-level coupled-EH lemma (constants obtained before choosing N')
  obtain ⟨C₀, B', N₀eh, hC₀0, hB'0, hS2fun⟩ :=
    S2mW_ge_compatMain_theta_uniform 5 64 (primorial D) D (by norm_num)
      (by norm_num) hW'sqf hDle hSeqlt hLoD
  -- EH range threshold
  obtain ⟨Nr, hNrfun⟩ := EH_range_theta (primorial D) hW'pos B' hB'0
  -- WindowPNT threshold (ε = 1/100)
  obtain ⟨Nc, hNc⟩ := eventually_atTop.mp (hPNT (1 / 100) (by norm_num))
  -- eventually `0 ≤ δ`
  have hδev : ∀ᶠ N' : ℕ in atTop,
      (19 : ℝ) ≤ (63 - 1 / 100) * (N' : ℝ) / Real.log N' := by
    have hev := eventually_poly_beats_polylog 1 1 1 (by norm_num)
    have hevN := tendsto_natCast_atTop_atTop.eventually hev
    filter_upwards [hevN, eventually_ge_atTop 2] with N' hN' hN2
    have hlogpos : 0 < Real.log N' := Real.log_pos (by exact_mod_cast (by omega : 1 < N'))
    simp only [pow_one, Real.rpow_one, one_mul] at hN'
    rw [le_div_iff₀ hlogpos]
    linarith [hN', hlogpos]
  -- combine every eventually fact
  have hcombined := (hslackEv C₀ hC₀0).and
    (hδev.and (eventually_ge_atTop (max (max Nr N₀eh) (max Nc 8))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hcombined
  set N' := max N₀ N with hN'def
  have hNleN' : N ≤ N' := le_max_right _ _
  have hN'geN₀ : N₀ ≤ N' := le_max_left _ _
  obtain ⟨hslack, hδ0', hgeThr⟩ := hN₀ N' hN'geN₀
  -- unpack thresholds
  have hNr' : Nr ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hgeThr
  have hN₀eh' : N₀eh ≤ N' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hgeThr
  have hNc' : Nc ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hgeThr
  have h8' : 8 ≤ N' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hgeThr
  have hN'8r : (8 : ℝ) ≤ (N' : ℝ) := by exact_mod_cast h8'
  have hN'pos : 0 < N' := by omega
  have hlogN'pos : 0 < Real.log N' := Real.log_pos (by exact_mod_cast (by omega : 1 < N'))
  -- R and its facts
  set R := ⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ with hRdef
  have hR2 : 2 ≤ R := R_ge_two_theta N' hN'8r
  have hRleN' : R ≤ N' := R_le_N'_theta N' (by omega)
  have hrange : primorial D * R ^ 2
      ≤ ⌊(N' : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log N') ^ B'⌋₊ := by
    rw [hRdef]; exact hNrfun N' hNr'
  have hyabs : ∀ r, |yF R (primorial D) Fstar1 r| ≤ 1 :=
    fun r => yF_Fstar1_abs_le_one R (primorial D) r
  -- δ, cval, errEH
  set δ : ℝ := (63 - 1 / 100) * (N' : ℝ) / Real.log N' - 19 with hδdef
  set cval : Fin 5 → ℝ :=
    fun m => Qdiag_mW 5 R (primorial D) m (yF R (primorial D) Fstar1) with hcvaldef
  set errEH : Fin 5 → ℝ :=
    fun m => deltaPi 5 64 N' m / (Nat.totient (primorial D) : ℝ)
          * (Qdiag_mW 5 R (primorial D) m (yF R (primorial D) Fstar1)
            - s2CompatFormM 5 R (primorial D) m (yF R (primorial D) Fstar1))
        + C₀ * (1 + Real.log R) ^ (2 * 5 + 2) * (N' : ℝ) / (Real.log N') ^ (2 * 5 + 4)
    with herrdef
  refine ⟨N', R, ν₀, δ, errEH, cval, hNleN', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- conjunct 1 : CRT collision-solvability
    intro d hd e he hcompat
    obtain ⟨hdsq, -, hdcopW, -⟩ := (mem_kSieveIndex_iff d).mp hd
    obtain ⟨hesq, -, hecopW, -⟩ := (mem_kSieveIndex_iff e).mp he
    exact cong_solvableW 5 (primorial D) d e ν₀ hW'pos
      (fun i => Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hdsq i).ne_zero (hesq i).ne_zero))
      (fun i => ((hdcopW i).symm.mul_right (hecopW i).symm).coprime_dvd_right
        (Nat.lcm_dvd_mul (d i) (e i)))
      (fun i j hij => lcm_pairwise_coprime_of_noncollision hd he hcompat hij)
  · -- conjunct 2 : `0 < φ W'`
    exact hφW'pos
  · -- conjunct 3 : `0 ≤ cval m`
    intro m
    simp only [hcvaldef]
    rw [qdiag_eq_yMsq_sum]
    exact Finset.sum_nonneg
      (fun u _ => div_nonneg (sq_nonneg _)
        (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)))
  · -- conjunct 4a : `0 ≤ δ`
    rw [hδdef]; linarith [hδ0']
  · -- conjunct 4b : `δ ≤ Δπ`
    intro m
    have hd := deltaPi_lower_of 5 (63 - 1 / 100) Nc hNc m N' hNc'
    have hhs : (hSeq 5 m : ℝ) ≤ 19 := by exact_mod_cast hSeq_le_nineteen m
    rw [hδdef]; linarith [hd, hhs]
  · -- conjunct 5 : `cval m ≤ Qdiag`
    intro m; exact le_refl _
  · -- conjunct 6 : the `S2ᵂ` lower bound
    intro m
    have hS2 := hS2fun R ν₀ (yF R (primorial D) Fstar1) hR2 hyabs hν₀ N'
      hN₀eh' hRleN' hrange m
    simp only [herrdef]
    have hid : deltaPi 5 64 N' m / (Nat.totient (primorial D) : ℝ)
          * Qdiag_mW 5 R (primorial D) m (yF R (primorial D) Fstar1)
        - (deltaPi 5 64 N' m / (Nat.totient (primorial D) : ℝ)
              * (Qdiag_mW 5 R (primorial D) m (yF R (primorial D) Fstar1)
                - s2CompatFormM 5 R (primorial D) m (yF R (primorial D) Fstar1))
            + C₀ * (1 + Real.log R) ^ (2 * 5 + 2) * (N' : ℝ) / (Real.log N') ^ (2 * 5 + 4))
      = deltaPi 5 64 N' m / (Nat.totient (primorial D) : ℝ)
            * s2CompatFormM 5 R (primorial D) m (yF R (primorial D) Fstar1)
          - C₀ * (1 + Real.log R) ^ (2 * 5 + 2) * (N' : ℝ) / (Real.log N') ^ (2 * 5 + 4) := by
      ring
    rw [hid]; linarith [hS2]
  · -- conjunct 7 : the assembled M-based ratio-slack (FABLE-QUEUE'd)
    exact hslack

/-! ## The interface capstone and its `EHall` compatibility corollary -/

/-- **Q3b — bounded prime gaps ≤ 12 from a single level of distribution.**  For
every `N` there are two primes `p ≠ q > N` with `|q − p| ≤ 12`, assuming only
`WindowPNT` and the single BV-shaped level hypothesis `HasLevel (3999/4000)`.

This is the weakest precisely-stated equidistribution interface that the landed
gaps ≤ 12 chain consumes: the whole chain touches `EHall` at exactly one point
(`FrontierM.lean:171`), and that point needs only `HasLevel (3999/4000)`.

**θ-caveat (see the module docstring):** `θ★ = 3999/4000` is near `1`, so this
hypothesis is EH-strength *in analytic depth*.  The extraction's content is a
minimal *shape* — one level + a `(log x)^B` modulus haircut — not a weaker
equidistribution range.  Cf. the θ = 1/2 instance of the same interface pattern,
`Salt.Maynard.bounded_gaps_from_level`. -/
theorem gaps_le_twelve_of_hasLevel (hPNT : WindowPNT) (hLoD : HasLevel (3999 / 4000)) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-12 : ℤ) 12 := by
  obtain ⟨D₀, hD₀300, hslackfun⟩ := winSlackM_ev
  have hFrontier : WinFrontierMWL D₀ :=
    winFrontierMW_of_hasLevel D₀ hD₀300 hLoD (hslackfun D₀ le_rfl)
  have hSeqlt : ∀ i : Fin 5, hSeq 5 i < D₀ := fun i => by
    have := hSeq_le_nineteen i; omega
  refine bounded_gaps_reduces_twelve (primorial D₀) (fun N => ?_)
  obtain ⟨N', R, ν₀, δ, errEH, cval, hNN', hsol, hφpos, hcvnn, hδ0, hDpi, hQlow,
    hS2low, hslack⟩ := hFrontier hPNT N
  refine ⟨N', R, ν₀, yF R (primorial D₀) Fstar1, hNN', ?_⟩
  exact win_core_M N' R ν₀ (primorial D₀) D₀ δ errEH cval
    (primorial_sqf' D₀) (primorial_hDlt D₀) hSeqlt (by omega) hsol hφpos hcvnn hδ0 hDpi
    hQlow hS2low hslack

/-- **Anti-vacuity check.**  The landed unconditional capstone `gaps_le_twelve`
(`Salt/Twelve/GapsUncond.lean`) is exactly the `EHall`-instance of the interface
theorem: `EHall` gives `EH (3999/4000)` (`EHall_hasEH`), hence
`HasLevel (3999/4000)` (`EH_hasLevel`), so `gaps_le_twelve_of_hasLevel` recovers
its conclusion verbatim.  This witnesses that `HasLevel (3999/4000)` is genuinely
weaker-or-equal to `EHall` as a hypothesis — the old theorem IS an instance of
the new one.  (Mirror of `Salt.Maynard.bounded_gaps_from_eh'` at θ = θ★.) -/
theorem gaps_le_twelve_of_EHall (hPNT : WindowPNT) (hEH : EHall) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-12 : ℤ) 12 :=
  gaps_le_twelve_of_hasLevel hPNT
    (EH_hasLevel (EHall_hasEH hEH (by norm_num) (by norm_num)))

end Salt.Twelve
