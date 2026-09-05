/-
# λ-BV wave 2-S, step F4b — THE AFFINE CIRCLE-METHOD ESTIMATE (the producer of F4a's slot)

**Frozen statement-only 2026-09-04 16:2x (math, Fable head on kriterion), from the price brief
`2026-09-04-math-PRICE-lbv-w2S-F4b-circle-estimate.md`; v1.1 cut 2026-09-04 17:xx on the helm's
refuter verdict (`2026-09-04-helm-REFUTER-VERDICT-lambda-bv-wave2S-F4b.md`, REPAIR-THEN-FIRE 4/4).**
Tao 1509.05422 Lemma 3.4 at the class filter `j + 1 ≡ p·b (mod a)`, over the affine
large-spectrum set `bigXiAff a b h eps H` (F1-X1), with the `h`-lane's constant `h·(1 + 2·C₀)` —
`a`-FREE (M1 LIVE).  Its crown `circle_method_estimate_sq_bounded_aff` has EXACTLY the shape of
F4a's slot `hcm` (`StrideShell.lean`, the head `log_chowla_aff_of_door`) after F4b S-1 (`a ∣ H →`
in the slot's `∀`-prefix), and `log_chowla_aff_of_door_unslotted` discharges the slot by one
class-A name.

THE v1.1 CUT (the verdict's §E(1), every kill→repair at file:line in the verdict's §A): A1 the dead
implicit `a` struck from `periodization_total_twist`'s binders (the ONE statement-level edit — the
body never mentions `a`, so the metavariable was unsynthesizable at every call); A2 the N9/N10
INVERSION — `circle_method_estimate_sq_bounded_aff` (N10, class C) carries the assembly with the
cap's `le_rfl` in the `refine`, and `circle_method_estimate_sq_aff_core` (N9, class A) is the
one-line `obtain` from it, so N10 precedes N9 in this file; A3 the `hgcd` positive control re-cut
from `(4,2,2)` (absorbed) to `(8,2,2)`; A4 the `/2` dropped from the display; A5 five dead names
replaced; A6 four `open private … in` lines; A7 N3's two bridging steps; A8 the `b = 0` strikes;
A10 the citations past EOF.  ERRATA: the freeze commit `3efd2e65`'s subject says "20 declarations";
this file holds 19 (2 defs + 17 theorems) and, with the MR twin, 20 declarations / 18 obligations.

THE ROUTE (the `h`-core `circle_method_estimate_sq_h_core`, `CircleMethod.lean:1366-1498`, with the
`η`-expansion of the class filter).  Write `d_η := η·(H/a) : ZMod H` (`twistOffset`), `χ_d(m) :=
stdAddChar(d·m)`, `Φ := (windowVal H x1 ·)` on `ZMod H`, `c_η := affOffset a b h H η = (b+h)·d_η`.
1. `1_{j+1 ≡ pb (a)} = (1/a)·Σ_{η<a} χ_{d_η}(j + 1 − pb)` (`classFilter_expand`, orthogonality on
   `ZMod a` lifted through `a ∣ H` — `stdAddChar_lift_of_dvd`); with
   `j + 1 − pb = (j + ph) + 1 − p(b+h)` the twist lands on the SECOND window factor:
   `L_aff = (1/a)·Σ_η χ_{d_η}(1)·L_η`, `L_η = Σ_p (1/p)·χ_{d_η}(−p(b+h))·
   Σ_{j<H} x_j·x_{j+ph}·χ_{d_η}(j+ph)` (`filteredCorr_eq_twistSum`).
2. Periodization at the twisted second window (`periodization_total_twist`): `‖L_η − T_η‖ ≤
   h·|𝒫_H|`.
3. Collapse (`T_collapse_twist`): `H·T_η = Σ_ξ 𝓕Φ(ξ)·𝓕(χ_{d_η}·Φ)(−ξ)·expSum(−(c_η + h·ξ).val/H)`
   — the per-`p` phase `χ_{d_η}(−p(b+h)) = stdAddChar(−p·c_η)` folded into `correlation_dft`'s
   character.
4. THE TRANSLATE (`dft_twist`): `𝓕(χ_d·Φ)(k) = 𝓕Φ(k − d)` — so the second Fourier factor sits at
   `−ξ − d_η`, and by the reality reflection at `ξ + d_η`: the `h`-lane's diagonal collapse
   `‖𝓕Φ ξ‖·‖𝓕Φ(−ξ)‖ = ‖𝓕Φ ξ‖²` FAILS here.  AM–GM leaves a PARTNER sum over the translate
   `Ξ_η + d_η` (`fourier_split_sq_twist`).
5. THE PARTNER LANDS (`xiEta_translate_mem_bigXiAff`): under **`gcd(b+h, a) ∣ h`** some `η' < a` has
   `(b+h)·η' ≡ b·η (mod a)`, so `c_{η'} + h(ξ + d_η) = c_η + hξ` and `ξ + d_η ∈ bigXiAff`.  This
   binder is the producer's, NOT the slot's: it lives on the discharge
   (`log_chowla_aff_of_door_unslotted`) and on F5's prize.  THE POSITIVE CONTROL (K2, re-cut by the
   verdict's A3): at `(a,b,h) = (8,2,2)`, `H = 8`, `ε = 4/5` (`W = {3,5}`, threshold `0.30777`,
   `bigXi = {0,1,3,4,5,7}`, `bigXiAff = {0,2,4,6}`, `xiEta(affOffset 1 = 4) = {0,2,4,6}`), at
   `η = 1`, `ξ = 0` the partner `0 + 1 = 1 ∉ bigXiAff` while every other hypothesis holds and
   `gcd(4,8) = 4 ∤ 2` — `xiEta_translate_mem_bigXiAff` MINUS `hgcd` is FALSE there.  At `(4,2,2)`
   the translate is ABSORBED whenever `2 ∉ primeWindow` (`a ∣ 2h`; `bigXi` is `+H/2`-invariant),
   which is the whole consuming regime — so `hgcd`'s necessity is a LEMMA-level fact (N7), not a
   fact about the core's conclusion at any exhibited point.
6. THE UNION (`sum_xiEta_le`, `sum_xiEta_translate_le`): each `η`-sum is `≤ Σ_{bigXiAff}`, so
   `(1/a)·Σ_η (S_η + S'_η)/2 ≤ S` — **the `(1/a)·a` cancellation**, `C = h·(1 + 2·C₀)`.  AM–GM's
   `1/2` is spent INSIDE N6's coefficient `C₀` (the `h`-lane's `fourier_split_sq_h` carries `2·C₀`
   where N6 carries `C₀`); the two union bounds supply the `2` of `2·C₀`.
7. Assembly (`circle_method_estimate_sq_bounded_aff`, N10 after the inversion): BYTE-IDENTICAL to
   the `h`-core's remainder line (`CircleMethod.lean:1457-1478`) after steps 2–6; the `H = 1` branch
   as at `h`, for every `a` and `b`.

⛔ HONEST LABEL.  LANDED 2026-09-04 17:4x: every declaration below is sorry-free (one Opus executor
in file order; 17 obligations, 17 landed, every theorem `[propext, Classical.choice, Quot.sound]`
or less, audited in `Salt.Entropy.All`).  F4b proves the affine circle-method estimate at the
`h`-lane's constant under two binders F4a's slot did not carry — `a ∣ H` (in the slot) and
`gcd(b+h, a) ∣ h` (the producer's, on the discharges).  It moves no door and closes no prize: the
`≈ 214.4` miss at `(210, 2)` is F5's, and F5's prize statement GAINS the binder `gcd(b+h, a) ∣ h`
— whose necessity is established at the LEMMA level (N7 at `(8,2,2)`, `H = 8`, `ε = 4/5`), not at
the core's conclusion.  Nothing here bears on twin primes.
-/
import Salt.Entropy.Chowla.StrideShell
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ## F4b-N0 — the twist offset and the `η`-fibre of the affine set -/

/-- **F4b-N0a (def).**  The twist offset `d_η := η·(H/a)` as an element of `ZMod H`: with `a ∣ H`
the character `m ↦ stdAddChar(d_η·m)` on `ZMod H` is `e(η·m/a)`.
`affOffset a b h H η = (b + h)·d_η` (`affOffset_eq_mul_twistOffset`). -/
def twistOffset (a H : ℕ) [NeZero H] (η : ℕ) : ZMod H :=
  ((η * (H / a) : ℕ) : ZMod H)

/-- **F4b-N0b (def).**  The `η`-fibre of the affine large-spectrum set at a generic offset `c`:
`Ξ_c := {ξ : c + h·ξ ∈ bigXi eps H}`.  At `c = affOffset a b h H η` this is the `η`-th member of the
union defining `bigXiAff` (`mem_bigXiAff_iff`). -/
noncomputable def xiEta (h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] (c : ZMod H) : Finset (ZMod H) := by
  classical
  exact Finset.univ.filter (fun ξ : ZMod H => c + (h : ZMod H) * ξ ∈ bigXi eps H)

/-- **F4b-N0c (class A).**  `affOffset a b h H η = ((b + h : ℕ) : ZMod H) * twistOffset a H η`:
`unfold affOffset twistOffset; push_cast; ring`. -/
theorem affOffset_eq_mul_twistOffset (a b h H : ℕ) [NeZero H] (η : ℕ) :
    affOffset a b h H η = ((b + h : ℕ) : ZMod H) * twistOffset a H η := by
  unfold affOffset twistOffset
  push_cast
  ring

/-- **F4b-N0d (class A).**  Membership in the `η`-fibre: `Finset.mem_filter`, `Finset.mem_univ`,
`true_and` after `unfold xiEta`. -/
theorem mem_xiEta {h : ℕ} {eps : ℚ} {H : ℕ} [NeZero H] {c ξ : ZMod H} :
    ξ ∈ xiEta h eps H c ↔ c + (h : ZMod H) * ξ ∈ bigXi eps H := by
  unfold xiEta
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-! ## F4b-N1 — THE TRANSLATE: a modulation moves the DFT -/

/-- **F4b-N1 (class B) — THE DFT TRANSLATE.**  Modulating by the character at `d` translates the
transform by `d`: `𝓕(χ_d·Φ)(k) = 𝓕Φ(k − d)`.  `ZMod.dft_apply` on both sides (`𝓕 Φ k = Σ_j
stdAddChar(−(j·k)) • Φ j`, `smul_eq_mul`), then termwise `stdAddChar(−(j·k)) * stdAddChar(d·j) =
stdAddChar(−(j·(k − d)))` by `← AddChar.map_add_eq_mul` and `congr 1; ring`.  THE SIGN (K1, held
by the refuters): mathlib's `dft_apply` carries `stdAddChar (-(j * k))`, so the modulation
`stdAddChar (d * j)` SUBTRACTS `d` from the frequency — derived, not copied. -/
theorem dft_twist {H : ℕ} [NeZero H] (Φ : ZMod H → ℂ) (d k : ZMod H) :
    ZMod.dft (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) k = ZMod.dft Φ (k - d) := by
  rw [ZMod.dft_apply, ZMod.dft_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [smul_eq_mul]
  have hj : -(j * k) + d * j = -(j * (k - d)) := by ring
  rw [← mul_assoc, ← ZMod.stdAddChar.map_add_eq_mul, hj]

/-- **F4b-N1b (class A).**  The modulated window keeps its pointwise bound:
`‖stdAddChar(d·m) * Φ m‖ = ‖Φ m‖` — `rw [norm_mul, AddChar.norm_apply, one_mul]`
(`AddChar.norm_apply`, `Mathlib/Analysis/Normed/Ring/Finite.lean:36`: an additive character into
a normed field on a finite group has norm `1`). -/
theorem norm_twist_mul {H : ℕ} [NeZero H] (Φ : ZMod H → ℂ) (d m : ZMod H) :
    ‖ZMod.stdAddChar (d * m) * Φ m‖ = ‖Φ m‖ := by
  rw [norm_mul, AddChar.norm_apply, one_mul]

/-! ## F4b-N2 — the class filter expanded over `η ∈ ℤ/aℤ`, lifted through `a ∣ H` -/

/-- **F4b-N2a (class B) — the character lift.**  With `a ∣ H`, `e(η·m/a)` on `ZMod a` IS
`stdAddChar` on `ZMod H` at `η·(H/a)·m`.  `ZMod.stdAddChar_coe (j : ℤ) : stdAddChar (j : ZMod N)
= Complex.exp (2 * π * I * j / N)` (`CircleAddChar.lean:85`; `Complex.exp` on an ℤ-cast — the
ℕ arguments `η, m` enter through `Int.cast_natCast`/`push_cast`) on both sides, then
`(η·(H/a)·m : ℂ)/H = (η·m : ℂ)/a` from `(H/a)·a = H` (`Nat.div_mul_cancel hdvd`,
`Nat.cast_div hdvd`, `field_simp`).  No cross-modulus `stdAddChar` lift exists in mathlib or in
`Salt/` — this IS the lift. -/
theorem stdAddChar_lift_of_dvd {a H : ℕ} [NeZero a] [NeZero H] (hdvd : a ∣ H) (η m : ℕ) :
    (ZMod.stdAddChar ((η * m : ℕ) : ZMod a) : ℂ)
      = ZMod.stdAddChar (twistOffset a H η * (m : ZMod H)) := by
  have hapos : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  obtain ⟨k, hk⟩ := hdvd
  have hka : H / a = k := by rw [hk]; exact Nat.mul_div_cancel_left k hapos
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact absurd (by rw [hk, hk0, Nat.mul_zero]) (NeZero.ne H)
    · exact hk0
  have haC : ((a : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  have hkC : ((k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hkpos.ne'
  have hHeq : ((H : ℕ) : ℂ) = ((a : ℕ) : ℂ) * ((k : ℕ) : ℂ) := by
    rw [hk]; push_cast; ring
  have hrw : twistOffset a H η * ((m : ℕ) : ZMod H)
      = ((((η * k * m : ℕ)) : ℤ) : ZMod H) := by
    unfold twistOffset
    rw [hka]
    push_cast
    ring
  have hlw : ((η * m : ℕ) : ZMod a) = ((((η * m : ℕ)) : ℤ) : ZMod a) := by
    push_cast
    ring
  rw [hrw, hlw, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  rw [hHeq, div_eq_div_iff haC (mul_ne_zero haC hkC)]
  push_cast
  ring

/-- **F4b-N2 (class B) — THE EXPANSION.**  For `0 < a`, `a ∣ H` and naturals `u v`:
`[u ≡ v (mod a)] = (1/a)·Σ_{η<a} stdAddChar(d_η·(u − v))` in `ℂ`.  Orthogonality on `ZMod a`: the
sum over POINTS `η ∈ ZMod a` at the fixed character `(ZMod.stdAddChar).mulShift t` is
`Σ_{η : ZMod a} stdAddChar (η * t) = a·[t = 0]` — THREE LINES: `AddChar.sum_mulShift`
(`NumberTheory/LegendreSymbol/AddCharacter.lean:258`) at `R := ZMod a`, `ψ := ZMod.stdAddChar`,
`hψ := ZMod.isPrimitive_stdAddChar a`, then `rw [ZMod.card]` (`Data/ZMod/Defs.lean:173`); mathlib
instantiates it at `stdAddChar` itself (`NumberTheory/LSeries/ZMod.lean:186`).  Alternate:
`AddChar.sum_eq_zero_of_ne_one` (`AddCharacter.lean:241`, the name mathlib's DFT uses) with
`AddChar.sum_eq_ite`.  The `range a` sum is the `ZMod a` sum through `ZMod.val`
(`Finset.sum_range` ↔ `Fin.sum_univ_eq_sum_range`, `ZMod.finEquiv`); lift each term through
`stdAddChar_lift_of_dvd` with `t := u − v` handled as `u = v + t` or `v = u + t` (`Nat.cast_sub`
avoided: state at `ZMod H` with `(u : ZMod H) − (v : ZMod H)` and use `AddChar.map_neg_eq_inv`/
`map_add_eq_mul`).  The `if`'s `Decidable` instance is `ZMod.decidableEq` (total in `a`; no
`classical` in the statement).  `ha` is redundant here (`[NeZero H]` + `hdvd` exclude `a = 0`) and
kept as the consumer's positional convenience; `hdvd` is the FALSE-making guard.  ~25 lines. -/
theorem classFilter_expand {a H : ℕ} [NeZero H] (ha : 0 < a) (hdvd : a ∣ H) (u v : ℕ) :
    (if ((u : ℕ) : ZMod a) = ((v : ℕ) : ZMod a) then (1 : ℂ) else 0)
      = (1 / (a : ℂ)) * ∑ η ∈ Finset.range a,
          ZMod.stdAddChar (twistOffset a H η * ((u : ZMod H) - (v : ZMod H))) := by
  classical
  haveI : NeZero a := ⟨ha.ne'⟩
  obtain ⟨k, hk⟩ := hdvd
  have hka : H / a = k := by rw [hk]; exact Nat.mul_div_cancel_left k ha
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact absurd (by rw [hk, hk0, Nat.mul_zero]) (NeZero.ne H)
    · exact hk0
  have haC : ((a : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  have hkC : ((k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hkpos.ne'
  have hHeq : ((H : ℕ) : ℂ) = ((a : ℕ) : ℂ) * ((k : ℕ) : ℂ) := by
    rw [hk]; push_cast; ring
  -- the cross-modulus lift at an INTEGER argument
  have hlift : ∀ (η : ℕ) (z : ℤ),
      (ZMod.stdAddChar ((((η : ℤ) * z : ℤ)) : ZMod a) : ℂ)
        = ZMod.stdAddChar (twistOffset a H η * ((z : ℤ) : ZMod H)) := by
    intro η z
    have hrw : twistOffset a H η * ((z : ℤ) : ZMod H)
        = (((((η * k : ℕ)) : ℤ) * z : ℤ) : ZMod H) := by
      unfold twistOffset
      rw [hka]
      push_cast
      ring
    rw [hrw, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
    congr 1
    rw [hHeq, div_eq_div_iff haC (mul_ne_zero haC hkC)]
    push_cast
    ring
  have hstep : ∀ η ∈ Finset.range a,
      (ZMod.stdAddChar (twistOffset a H η * ((u : ZMod H) - (v : ZMod H))) : ℂ)
        = ZMod.stdAddChar (((η : ℕ) : ZMod a)
            * (((u : ℕ) : ZMod a) - ((v : ℕ) : ZMod a))) := by
    intro η _
    have hz : ((u : ZMod H) - (v : ZMod H)) = (((((u : ℤ) - (v : ℤ))) : ℤ) : ZMod H) := by
      push_cast
      ring
    rw [hz, ← hlift η ((u : ℤ) - (v : ℤ))]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hstep]
  have hrange : ∑ η ∈ Finset.range a,
        (ZMod.stdAddChar (((η : ℕ) : ZMod a)
          * (((u : ℕ) : ZMod a) - ((v : ℕ) : ZMod a))) : ℂ)
      = ∑ η : ZMod a,
          (ZMod.stdAddChar (η * (((u : ℕ) : ZMod a) - ((v : ℕ) : ZMod a))) : ℂ) := by
    refine Finset.sum_nbij' (fun η : ℕ => ((η : ℕ) : ZMod a)) (fun y : ZMod a => y.val)
      (fun η _ => Finset.mem_univ _)
      (fun y _ => Finset.mem_range.mpr (ZMod.val_lt y))
      (fun η hη => ZMod.val_natCast_of_lt (Finset.mem_range.mp hη))
      (fun y _ => ZMod.natCast_zmod_val y)
      (fun η _ => rfl)
  rw [hrange]
  have horth : ∑ η : ZMod a,
        (ZMod.stdAddChar (η * (((u : ℕ) : ZMod a) - ((v : ℕ) : ZMod a))) : ℂ)
      = if (((u : ℕ) : ZMod a) - ((v : ℕ) : ZMod a)) = 0 then (a : ℂ) else 0 := by
    have hs := AddChar.sum_mulShift (((u : ℕ) : ZMod a) - ((v : ℕ) : ZMod a))
      (ZMod.isPrimitive_stdAddChar a)
    rw [ZMod.card, Nat.cast_ite, Nat.cast_zero] at hs
    exact hs
  rw [horth]
  by_cases huv : ((u : ℕ) : ZMod a) = ((v : ℕ) : ZMod a)
  · rw [if_pos huv, if_pos (sub_eq_zero.mpr huv), one_div, inv_mul_cancel₀ haC]
  · rw [if_neg huv, if_neg (fun hc => huv (sub_eq_zero.mp hc)), mul_zero]

/-- **F4b-N3 (class B) — the filtered correlation as the twist sum.**  The LHS is a REAL sum cast to
`ℂ` whose summand is an ℝ-valued `if` with the window PRODUCT in the then-branch; the bridging
steps FIRST: `Complex.ofReal_sum`, `Complex.ofReal_mul` to push the cast through the sums, then
`apply_ite Complex.ofReal` (+ `Complex.ofReal_zero`, `Complex.ofReal_one`) to push it through the
`if`, then `ite_mul, one_mul, zero_mul` to expose `(if P then 1 else 0) * A` — only THEN
`classFilter_expand` at `u := j + 1`, `v := p·b` inside the double sum,
`(j + 1) − p·b = ((j + p·h) + 1) − p·(b + h)` in `ZMod H` (`push_cast; ring`),
`AddChar.map_add_eq_mul` twice and `AddChar.map_neg_eq_inv`-shape for the `−p(b+h)` factor, then
`Finset.mul_sum`/`Finset.sum_comm` ×2 to bring `Σ_η` outside.  The window factors are cast `ℤ → ℂ`
(`Complex.ofReal_intCast`-shape). -/
theorem filteredCorr_eq_twistSum {a b h : ℕ} (ha : 0 < a) {eps : ℚ} {H : ℕ} [NeZero H]
    (hdvd : a ∣ H) (x1 : Fin H → ℤ) :
    ((∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
        if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
          (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ) else 0 : ℝ) : ℂ)
      = (1 / (a : ℂ)) * ∑ η ∈ Finset.range a,
          ZMod.stdAddChar (twistOffset a H η) *
            ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
              * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * twistOffset a H η))
              * ∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
                  * (ZMod.stdAddChar (twistOffset a H η * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                      * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ)) := by
  classical
  have hkey : ∀ (η : ℕ) (p : primeWindow eps H) (j : ℕ),
      ZMod.stdAddChar (twistOffset a H η)
        * ((1 / ((p : ℕ) : ℂ))
          * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * twistOffset a H η))
          * (((windowVal H x1 j : ℤ) : ℂ)
              * (ZMod.stdAddChar (twistOffset a H η * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                  * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ))))
        = (1 / ((p : ℕ) : ℂ))
            * (ZMod.stdAddChar (twistOffset a H η
                * ((((j + 1 : ℕ)) : ZMod H) - ((((p : ℕ) * b : ℕ)) : ZMod H)))
              * (((windowVal H x1 j : ℤ) : ℂ)
                  * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ))) := by
    intro η p j
    have harg : twistOffset a H η
        + (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * twistOffset a H η)
          + twistOffset a H η * ((j + (p : ℕ) * h : ℕ) : ZMod H))
        = twistOffset a H η
            * ((((j + 1 : ℕ)) : ZMod H) - ((((p : ℕ) * b : ℕ)) : ZMod H)) := by
      push_cast
      ring
    rw [← harg, ZMod.stdAddChar.map_add_eq_mul, ZMod.stdAddChar.map_add_eq_mul]
    ring
  have hexp : ∀ (p : primeWindow eps H) (j : ℕ),
      (if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then (1 : ℂ) else 0)
        = (1 / (a : ℂ)) * ∑ η ∈ Finset.range a,
            ZMod.stdAddChar (twistOffset a H η
              * ((((j + 1 : ℕ)) : ZMod H) - ((((p : ℕ) * b : ℕ)) : ZMod H))) :=
    fun p j => classFilter_expand ha hdvd (j + 1) ((p : ℕ) * b)
  have hL : ((∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
        if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
          (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ) else 0 : ℝ) : ℂ)
      = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H, ∑ η ∈ Finset.range a,
          (1 / (a : ℂ)) * ((1 / ((p : ℕ) : ℂ))
            * (ZMod.stdAddChar (twistOffset a H η
                * ((((j + 1 : ℕ)) : ZMod H) - ((((p : ℕ) * b : ℕ)) : ZMod H)))
              * (((windowVal H x1 j : ℤ) : ℂ)
                  * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ)))) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hR : (1 / ((p : ℕ) : ℂ))
          * (((1 / (a : ℂ)) * ∑ η ∈ Finset.range a,
              ZMod.stdAddChar (twistOffset a H η
                * ((((j + 1 : ℕ)) : ZMod H) - ((((p : ℕ) * b : ℕ)) : ZMod H))))
            * (((windowVal H x1 j : ℤ) : ℂ)
                * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ)))
        = ∑ η ∈ Finset.range a, (1 / (a : ℂ)) * ((1 / ((p : ℕ) : ℂ))
            * (ZMod.stdAddChar (twistOffset a H η
                * ((((j + 1 : ℕ)) : ZMod H) - ((((p : ℕ) * b : ℕ)) : ZMod H)))
              * (((windowVal H x1 j : ℤ) : ℂ)
                  * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ)))) := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun η _ => by ring)
    rw [← hR, ← hexp p j]
    by_cases hif : ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a)
    · rw [if_pos hif, if_pos hif]
      push_cast
      ring
    · rw [if_neg hif, if_neg hif]
      push_cast
      ring
  have hRHS : (1 / (a : ℂ)) * ∑ η ∈ Finset.range a,
        ZMod.stdAddChar (twistOffset a H η)
          * ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
              * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * twistOffset a H η))
              * ∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
                  * (ZMod.stdAddChar (twistOffset a H η * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                      * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ))
      = ∑ η ∈ Finset.range a, ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          (1 / (a : ℂ)) * ((1 / ((p : ℕ) : ℂ))
            * (ZMod.stdAddChar (twistOffset a H η
                * ((((j + 1 : ℕ)) : ZMod H) - ((((p : ℕ) * b : ℕ)) : ZMod H)))
              * (((windowVal H x1 j : ℤ) : ℂ)
                  * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ)))) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun η _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun j _ => ?_)))
    rw [← hkey η p j]
  rw [hL, hRHS]
  exact Eq.trans (Finset.sum_congr rfl (fun p _ => Finset.sum_comm)) Finset.sum_comm

/-! ## F4b-N4 / N5 — periodization and collapse at the twisted second window -/

open private windowVal_c_norm_le card_wrap_le from Salt.Entropy.Chowla.CircleMethod in
/-- **F4b-N4 (class B) — periodization at the twisted second window.**  The twin of
`periodization_total_h` (`CircleMethod.lean:1003`), whose landed per-prime bound
`perprime_diff_norm_le` is stated at INTEGER windows and is `private`: here the second window is
COMPLEX (the twist), so the per-prime bound is re-proved in place — the two sums differ exactly at
the `j` with `H ≤ j + p·h` (the ℕ-window is `0` there, `windowVal`'s `dif_neg`; the `ZMod`-window
wraps), at most `p·h` indices (`card_wrap_le` at offset `p·h`, private: `((range H).filter (fun j
=> H ≤ j + p·h)).card ≤ p·h`; or `Finset.card_le_card` against `Finset.Ico (H − p·h) H`), each term
of norm `≤ 1` (`windowVal_c_norm_le` ×2, `norm_twist_mul`), so `‖…‖ ≤ (1/p)·(p·h) = h` per prime
(`norm_sum_le`), and `Σ_p h = h·|𝒫_H|`.  The extra phase `stdAddChar(−p(b+h)·d)` has norm `1` and
factors out of the per-prime difference; the twist cancels in the difference by `Nat.cast_add`.
The binder list carries NO `a` (v1.1, A1: the body never mentions it). -/
theorem periodization_total_twist {b h : ℕ} {eps : ℚ} {H : ℕ} [NeZero H] (d : ZMod H)
    {x1 : Fin H → ℤ} (hx1 : ∀ i, |x1 i| ≤ 1) :
    ‖∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
        * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * d))
        * ((∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
              * (ZMod.stdAddChar (d * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                  * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ)))
          - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ)
              * (ZMod.stdAddChar (d * (m + (((p : ℕ) * h : ℕ) : ZMod H)))
                  * ((windowVal H x1 (m + (((p : ℕ) * h : ℕ) : ZMod H)).val : ℤ) : ℂ)))‖
      ≤ (h : ℝ) * ((primeWindow eps H).card : ℝ) := by
  classical
  have hchar1 : ∀ z : ZMod H, ‖(ZMod.stdAddChar z : ℂ)‖ = 1 := by
    intro z
    rw [ZMod.stdAddChar_apply, Circle.norm_coe]
  have wvn : ∀ n : ℕ, ‖((windowVal H x1 n : ℤ) : ℂ)‖ ≤ 1 := by
    intro n
    rw [show ((windowVal H x1 n : ℤ) : ℂ) = ((windowVal H x1 n : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real]
    exact windowVal_abs_le hx1 n
  have hprime : ∀ q : ℕ,
      ‖(∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
            * (ZMod.stdAddChar (d * ((j + q : ℕ) : ZMod H))
                * ((windowVal H x1 (j + q) : ℤ) : ℂ)))
          - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ)
              * (ZMod.stdAddChar (d * (m + ((q : ℕ) : ZMod H)))
                  * ((windowVal H x1 (m + ((q : ℕ) : ZMod H)).val : ℤ) : ℂ))‖ ≤ (q : ℝ) := by
    intro q
    have hright : ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ)
          * (ZMod.stdAddChar (d * (m + ((q : ℕ) : ZMod H)))
              * ((windowVal H x1 (m + ((q : ℕ) : ZMod H)).val : ℤ) : ℂ))
        = ∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
            * (ZMod.stdAddChar (d * (((j : ℕ) : ZMod H) + ((q : ℕ) : ZMod H)))
                * ((windowVal H x1 ((((j : ℕ) : ZMod H) + ((q : ℕ) : ZMod H)).val) : ℤ)
                    : ℂ)) := by
      refine Finset.sum_nbij' (fun m : ZMod H => m.val) (fun j : ℕ => (j : ZMod H))
        (fun m _ => Finset.mem_range.mpr (ZMod.val_lt m)) (fun j _ => Finset.mem_univ _)
        (fun m _ => ZMod.natCast_zmod_val m)
        (fun j hj => ZMod.val_natCast_of_lt (Finset.mem_range.mp hj))
        (fun m _ => by rw [ZMod.natCast_zmod_val])
    have hstep : ∑ j ∈ Finset.range H,
          ‖((windowVal H x1 j : ℤ) : ℂ)
              * (ZMod.stdAddChar (d * ((j + q : ℕ) : ZMod H))
                  * ((windowVal H x1 (j + q) : ℤ) : ℂ))
            - ((windowVal H x1 j : ℤ) : ℂ)
              * (ZMod.stdAddChar (d * (((j : ℕ) : ZMod H) + ((q : ℕ) : ZMod H)))
                  * ((windowVal H x1 ((((j : ℕ) : ZMod H) + ((q : ℕ) : ZMod H)).val) : ℤ)
                      : ℂ))‖
        ≤ ∑ j ∈ Finset.range H, (if H ≤ j + q then (1 : ℝ) else 0) := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      split_ifs with hjq
      · have hz : windowVal H x1 (j + q) = 0 := by rw [windowVal, dif_neg (by omega)]
        rw [hz]
        have h0 : ((windowVal H x1 j : ℤ) : ℂ)
            * (ZMod.stdAddChar (d * ((j + q : ℕ) : ZMod H)) * (((0 : ℤ)) : ℂ)) = 0 := by
          simp
        rw [h0, zero_sub, norm_neg, norm_mul, norm_mul, hchar1]
        calc ‖((windowVal H x1 j : ℤ) : ℂ)‖
              * (1 * ‖((windowVal H x1 ((((j : ℕ) : ZMod H) + ((q : ℕ) : ZMod H)).val) : ℤ)
                  : ℂ)‖)
            = ‖((windowVal H x1 j : ℤ) : ℂ)‖
                * ‖((windowVal H x1 ((((j : ℕ) : ZMod H) + ((q : ℕ) : ZMod H)).val) : ℤ)
                    : ℂ)‖ := by ring
          _ ≤ 1 * 1 := mul_le_mul (wvn j) (wvn _) (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      · have hlt : j + q < H := by omega
        have hcast : ((j : ℕ) : ZMod H) + ((q : ℕ) : ZMod H) = ((j + q : ℕ) : ZMod H) := by
          push_cast
          ring
        rw [hcast, ZMod.val_natCast_of_lt hlt, sub_self, norm_zero]
    rw [hright, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (hstep.trans ?_)
    rw [Finset.sum_boole]
    exact_mod_cast card_wrap_le q
  calc ‖∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
        * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * d))
        * ((∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
              * (ZMod.stdAddChar (d * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                  * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ)))
          - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ)
              * (ZMod.stdAddChar (d * (m + (((p : ℕ) * h : ℕ) : ZMod H)))
                  * ((windowVal H x1 (m + (((p : ℕ) * h : ℕ) : ZMod H)).val : ℤ) : ℂ)))‖
      ≤ ∑ p : primeWindow eps H, ‖(1 / ((p : ℕ) : ℂ))
          * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * d))
          * ((∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
                * (ZMod.stdAddChar (d * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                    * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ)))
            - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ)
                * (ZMod.stdAddChar (d * (m + (((p : ℕ) * h : ℕ) : ZMod H)))
                    * ((windowVal H x1 (m + (((p : ℕ) * h : ℕ) : ZMod H)).val : ℤ) : ℂ)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _p : primeWindow eps H, (h : ℝ) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        rw [norm_mul, norm_mul, norm_div, norm_one, Complex.norm_natCast, hchar1, mul_one]
        have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by
          exact_mod_cast (prime_of_mem_primeWindow p.2).pos
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hp0]
        refine le_trans (hprime ((p : ℕ) * h)) (le_of_eq ?_)
        push_cast
        ring
    _ = (h : ℝ) * ((primeWindow eps H).card : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_comm]

open private T_collapse_h correlation_dft expSum_eq_char_sum from
  Salt.Entropy.Chowla.CircleMethod in
/-- **F4b-N5 (class B) — the collapse at the twisted second window with the per-`p` phase.**
`T_collapse_h` (`CircleMethod.lean:961`, private — opened above) at `Φ₂ := χ_d·Φ₁` with the phase
`stdAddChar(−p·c)` folded in: `correlation_dft Φ₁ Φ₂ (p·h)` gives `stdAddChar(−(p·h·ξ))`, times
`stdAddChar(−p·c)` is `stdAddChar(−(p·(c + h·ξ)))` (`AddChar.map_add_eq_mul`, `push_cast; ring`),
then `expSum_eq_char_sum` (private, opened above) at `c + h·ξ`.  `c` is generic; the consumer
takes `c := affOffset a b h H η = (b+h)·d_η` (`affOffset_eq_mul_twistOffset`). -/
theorem T_collapse_twist {eps : ℚ} {H : ℕ} [NeZero H] (h : ℕ) (Φ₁ Φ₂ : ZMod H → ℂ) (c : ZMod H) :
    (H : ℂ) * ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
        * ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * c))
        * ∑ m : ZMod H, Φ₁ m * Φ₂ (m + (((p : ℕ) * h : ℕ) : ZMod H))
      = ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ)
          * expSum eps H (-(((c + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ)) := by
  have hfreq : ∀ (q : ℕ) (ξ : ZMod H),
      -(((q : ℕ) : ZMod H) * c) + -(((q * h : ℕ) : ZMod H) * ξ)
        = -(((q : ℕ) : ZMod H) * (c + (h : ZMod H) * ξ)) := by
    intro q ξ
    push_cast
    ring
  calc (H : ℂ) * ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
        * ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * c))
        * ∑ m : ZMod H, Φ₁ m * Φ₂ (m + (((p : ℕ) * h : ℕ) : ZMod H))
      = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
          * ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * c))
          * ((H : ℂ) * ∑ m : ZMod H, Φ₁ m * Φ₂ (m + (((p : ℕ) * h : ℕ) : ZMod H))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by ring)
    _ = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
          * ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * c))
          * ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ)
              * ZMod.stdAddChar (-(((((p : ℕ) * h : ℕ)) : ZMod H) * ξ)) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [correlation_dft Φ₁ Φ₂ ((((p : ℕ) * h : ℕ)) : ZMod H)]
    _ = ∑ p : primeWindow eps H, ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ)
          * ((1 / ((p : ℕ) : ℂ))
              * ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * (c + (h : ZMod H) * ξ)))) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ξ _ => ?_)
        rw [← hfreq (p : ℕ) ξ, ZMod.stdAddChar.map_add_eq_mul]
        ring
    _ = ∑ ξ : ZMod H, ∑ p : primeWindow eps H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ)
          * ((1 / ((p : ℕ) : ℂ))
              * ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * (c + (h : ZMod H) * ξ)))) :=
        Finset.sum_comm
    _ = ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ)
          * ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
              * ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * (c + (h : ZMod H) * ξ))) := by
        refine Finset.sum_congr rfl (fun ξ _ => by rw [Finset.mul_sum])
    _ = ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ)
          * expSum eps H (-(((c + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ)) := by
        exact Finset.sum_congr rfl
          (fun ξ _ => by rw [← expSum_eq_char_sum (c + (h : ZMod H) * ξ)])

/-! ## F4b-N6 — the squared Fourier split at a translated partner -/

open private dft_l1_reflect expSum_norm_le_major mem_bigXi from Salt.Entropy.Chowla.CircleMethod in
/-- **F4b-N6 (class C) — THE SPLIT WITH THE PARTNER.**  The twin of `fourier_split_sq_h`
(`CircleMethod.lean:1133`) at the second window `χ_d·Φ`: by `dft_twist` the second factor is
`𝓕Φ(−ξ − d)`, and by the reality reflection `hrefl` (at the REAL `Φ`) its norm is `‖𝓕Φ(ξ + d)‖`.
Minor arc (`ξ ∉ Ξ_c`): `‖expSum‖ < ε²/log H` (`mem_bigXi`, private, opened above; the
private-free alternative is `unfold xiEta bigXi; simp only [Finset.mem_filter, Finset.mem_univ,
true_and]` as at `StrideFork.lean:221-223`), then `dft_l1_reflect Φ (χ_d·Φ)` (private, opened
above; generic in two windows of pointwise norm `≤ 1` — `norm_twist_mul` at `m := j` discharges
the second verbatim) gives `ε²H²/log H`.  Major arc (`ξ ∈ Ξ_c`): `expSum_norm_le_major` (private,
opened above) gives `2C₀/log H`, and AM–GM `‖A‖·‖B‖ ≤ (‖A‖² + ‖B‖²)/2` (`two_mul_le_add_sq`)
splits the product into the two sums — the `h`-lane's `rw [hrefl ξ]` collapse is NOT available
(K1: the factors sit at `ξ` and `ξ + d`).  The `1/2` of AM–GM against the `2` of `2C₀/log H` is
why this statement carries `C₀`, not `2·C₀`. -/
theorem fourier_split_sq_twist {eps : ℚ} {H : ℕ} [NeZero H] (h : ℕ) (Φ : ZMod H → ℂ)
    (h1 : ∀ j, ‖Φ j‖ ≤ 1) (hrefl : ∀ ξ : ZMod H, ‖ZMod.dft Φ (-ξ)‖ = ‖ZMod.dft Φ ξ‖)
    (c d : ZMod H) {C₀ : ℝ} (hC₀ : 0 < C₀) (hlog : 0 < Real.log (H : ℝ))
    (hcard : ((primeWindow eps H).card : ℝ) ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))) :
    ‖∑ ξ : ZMod H, ZMod.dft Φ ξ * ZMod.dft (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) (-ξ)
        * expSum eps H (-(((c + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
      ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
        + (C₀ / Real.log (H : ℝ))
            * (∑ ξ ∈ xiEta h eps H c, ‖ZMod.dft Φ ξ‖ ^ 2
                + ∑ ξ ∈ xiEta h eps H c, ‖ZMod.dft Φ (ξ + d)‖ ^ 2) := by
  classical
  have h2 : ∀ j, ‖ZMod.stdAddChar (d * j) * Φ j‖ ≤ 1 := by
    intro j
    rw [norm_twist_mul]
    exact h1 j
  have hpart : ∀ ξ : ZMod H,
      ‖ZMod.dft (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) (-ξ)‖
        = ‖ZMod.dft Φ (ξ + d)‖ := by
    intro ξ
    rw [dft_twist Φ d (-ξ), show (-ξ - d) = -(ξ + d) by ring]
    exact hrefl (ξ + d)
  set g : ZMod H → ℝ := fun ξ =>
    ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) (-ξ)‖
      * ‖expSum eps H (-(((c + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖ with hg
  have hstep1 : ‖∑ ξ : ZMod H, ZMod.dft Φ ξ
      * ZMod.dft (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) (-ξ)
      * expSum eps H (-(((c + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
        ≤ ∑ ξ : ZMod H, g ξ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [hg]; simp only; rw [norm_mul, norm_mul]
  refine hstep1.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ξ => ξ ∈ xiEta h eps H c) g]
  have hfilt : Finset.univ.filter (fun ξ => ξ ∈ xiEta h eps H c) = xiEta h eps H c := by
    ext ξ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hmajor : ∑ ξ ∈ Finset.univ.filter (fun ξ => ξ ∈ xiEta h eps H c), g ξ
      ≤ (C₀ / Real.log (H : ℝ))
          * (∑ ξ ∈ xiEta h eps H c, ‖ZMod.dft Φ ξ‖ ^ 2
            + ∑ ξ ∈ xiEta h eps H c, ‖ZMod.dft Φ (ξ + d)‖ ^ 2) := by
    rw [hfilt, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum (fun ξ _ => ?_)
    rw [hg]; simp only
    rw [hpart ξ]
    have hbe : ‖expSum eps H (-(((c + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
        ≤ 2 * C₀ / Real.log (H : ℝ) := expSum_norm_le_major hC₀ hlog hcard _
    have hamgm : 2 * ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (ξ + d)‖
        ≤ ‖ZMod.dft Φ ξ‖ ^ 2 + ‖ZMod.dft Φ (ξ + d)‖ ^ 2 := two_mul_le_add_sq _ _
    calc ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (ξ + d)‖
          * ‖expSum eps H (-(((c + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
        ≤ ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (ξ + d)‖ * (2 * C₀ / Real.log (H : ℝ)) := by gcongr
      _ = C₀ / Real.log (H : ℝ) * (2 * ‖ZMod.dft Φ ξ‖ * ‖ZMod.dft Φ (ξ + d)‖) := by ring
      _ ≤ C₀ / Real.log (H : ℝ) * (‖ZMod.dft Φ ξ‖ ^ 2 + ‖ZMod.dft Φ (ξ + d)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hamgm (by positivity)
  have hminor : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ xiEta h eps H c), g ξ
      ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ) := by
    have hle : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ xiEta h eps H c), g ξ
        ≤ ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ xiEta h eps H c),
            ((eps : ℝ) ^ 2 / Real.log (H : ℝ))
              * (‖ZMod.dft Φ ξ‖
                  * ‖ZMod.dft (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) (-ξ)‖) := by
      refine Finset.sum_le_sum (fun ξ hξ => ?_)
      rw [Finset.mem_filter] at hξ
      have hlt : ‖expSum eps H (-(((c + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
          < (eps : ℝ) ^ 2 / Real.log (H : ℝ) :=
        not_le.mp (fun hc' => hξ.2 (mem_xiEta.mpr (mem_bigXi.mpr hc')))
      rw [hg]; simp only
      calc ‖ZMod.dft Φ ξ‖
            * ‖ZMod.dft (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) (-ξ)‖
            * ‖expSum eps H (-(((c + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
          ≤ ‖ZMod.dft Φ ξ‖
              * ‖ZMod.dft (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) (-ξ)‖
              * ((eps : ℝ) ^ 2 / Real.log (H : ℝ)) := by gcongr
        _ = (eps : ℝ) ^ 2 / Real.log (H : ℝ)
              * (‖ZMod.dft Φ ξ‖
                  * ‖ZMod.dft (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) (-ξ)‖) := by
            ring
    refine hle.trans ?_
    rw [← Finset.mul_sum]
    have hl1 : ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ xiEta h eps H c),
        (‖ZMod.dft Φ ξ‖
          * ‖ZMod.dft (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) (-ξ)‖)
          ≤ ∑ ξ : ZMod H, ‖ZMod.dft Φ ξ‖
              * ‖ZMod.dft (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) (-ξ)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun ξ _ _ => by positivity)
    have hl2 := dft_l1_reflect Φ (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) h1 h2
    calc (eps : ℝ) ^ 2 / Real.log (H : ℝ)
          * ∑ ξ ∈ Finset.univ.filter (fun ξ => ¬ ξ ∈ xiEta h eps H c),
              (‖ZMod.dft Φ ξ‖
                * ‖ZMod.dft (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) (-ξ)‖)
        ≤ (eps : ℝ) ^ 2 / Real.log (H : ℝ) * (H : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (hl1.trans hl2) (div_nonneg (by positivity) hlog.le)
      _ = (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ) := by ring
  linarith [hmajor, hminor]

/-! ## F4b-N7 — the fibre and its translate land in `bigXiAff` -/

/-- **F4b-N7a (class A).**  The `η`-fibre at `affOffset η` is inside `bigXiAff`:
`Finset.subset_iff`, `mem_xiEta`, `mem_bigXiAff_iff` with the witness `η`
(`Finset.mem_range.mpr hη`). -/
theorem xiEta_subset_bigXiAff (a b h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] {η : ℕ} (hη : η < a) :
    xiEta h eps H (affOffset a b h H η) ⊆ bigXiAff a b h eps H := by
  intro ξ hξ
  rw [mem_xiEta] at hξ
  exact mem_bigXiAff_iff.mpr ⟨η, Finset.mem_range.mpr hη, hξ⟩

/-- **F4b-N7 (class C, THE PARTNER LANDS) — the block's one real arithmetic.**  Under
`gcd(b+h, a) ∣ h` the translate of the `η`-fibre by `d_η` is inside `bigXiAff`: choose `η' < a`
with `(b+h)·η' ≡ b·η (mod a)` — write `g := gcd(b+h, a)`, `b + h = g·u`, `a = g·v` with
`Nat.Coprime u v` (`Nat.coprime_div_gcd_div_gcd`), `g ∣ b` from `g ∣ b + h` and `g ∣ h`
(`Nat.dvd_sub`, `Init/Data/Nat/Dvd.lean:128`: `k ∣ m → k ∣ n → k ∣ m - n`, at `m := b + h`,
`n := h`, `Nat.add_sub_cancel`), so the congruence is `u·η' ≡ (b/g)·η (mod v)`, solved by
`η' := ((b/g)·η·u⁻¹) % v` with `u⁻¹` the inverse of `u` mod `v` (`Nat.gcdA`/`ZMod.unitOfCoprime v`,
`ZMod.val`); then `η' < v ≤ a`.  The membership: `mem_bigXiAff_iff` with witness `η'`; the point
`affOffset η' + h·(ξ + d_η)` equals `affOffset η + h·ξ` in `ZMod H` because
`((b+h)η' + hη − (b+h)η)·(H/a) ≡ 0 (mod H)` — `affOffset_eq_mul_twistOffset`, `twistOffset`
unfolded, `a ∣ H` for `(k·a)·(H/a) = k·H` (`Nat.div_mul_cancel`), `ZMod.natCast_self`/
`ZMod.natCast_eq_zero_iff` (`Data/ZMod/Basic.lean:518`: `(a : ZMod b) = 0 ↔ b ∣ a`, the cast on
ℕ).  Uniform in `ξ`.  This is the lemma whose `hgcd` is NECESSARY: minus `hgcd` it is FALSE at
`(8,2,2)`, `H = 8`, `ε = 4/5`, `η = 1`, `ξ = 0` (the header's step 5). -/
theorem xiEta_translate_mem_bigXiAff {a b h : ℕ} (ha : 0 < a) (hgcd : Nat.gcd (b + h) a ∣ h)
    {eps : ℚ} {H : ℕ} [NeZero H] (hdvd : a ∣ H) {η : ℕ} (hη : η < a) {ξ : ZMod H}
    (hξ : ξ ∈ xiEta h eps H (affOffset a b h H η)) :
    ξ + twistOffset a H η ∈ bigXiAff a b h eps H := by
  classical
  -- `hη` is not consumed: the witness `η' := y.val` is bounded by `ZMod.val_lt`, not by `η < a`
  have _hη := hη
  haveI : NeZero a := ⟨ha.ne'⟩
  obtain ⟨k, hk⟩ := hdvd
  have hka : H / a = k := by rw [hk]; exact Nat.mul_div_cancel_left k ha
  have hgb : Nat.gcd (b + h) a ∣ b := by
    have hd1 : Nat.gcd (b + h) a ∣ b + h := Nat.gcd_dvd_left _ _
    have hd2 := Nat.dvd_sub hd1 hgcd
    simpa using hd2
  obtain ⟨b', hb'⟩ := hgb
  have hbez : ((Nat.gcd (b + h) a : ℕ) : ℤ)
      = ((b + h : ℕ) : ℤ) * Nat.gcdA (b + h) a + ((a : ℕ) : ℤ) * Nat.gcdB (b + h) a :=
    Nat.gcd_eq_gcd_ab (b + h) a
  have hgz : ((Nat.gcd (b + h) a : ℕ) : ZMod a)
      = ((b + h : ℕ) : ZMod a) * ((Nat.gcdA (b + h) a : ℤ) : ZMod a) := by
    have h0 := congrArg (fun z : ℤ => ((z : ℤ) : ZMod a)) hbez
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at h0
    rw [ZMod.natCast_self, zero_mul, add_zero] at h0
    exact h0
  set y : ZMod a := ((Nat.gcdA (b + h) a : ℤ) : ZMod a) * ((b' : ℕ) : ZMod a)
    * ((η : ℕ) : ZMod a) with hy
  have hyeq : ((b + h : ℕ) : ZMod a) * y = ((b : ℕ) : ZMod a) * ((η : ℕ) : ZMod a) := by
    have hbz : ((b : ℕ) : ZMod a)
        = ((Nat.gcd (b + h) a : ℕ) : ZMod a) * ((b' : ℕ) : ZMod a) := by
      conv_lhs => rw [hb']
      push_cast
      ring
    rw [hy, hbz, ← mul_assoc, ← mul_assoc, ← hgz]
  have hyv : ((y.val : ℕ) : ZMod a) = y := ZMod.natCast_zmod_val y
  have hdz : ((a : ℕ) : ℤ) ∣ (((b + h : ℕ) : ℤ) * ((y.val : ℕ) : ℤ)
      - ((b : ℕ) : ℤ) * ((η : ℕ) : ℤ)) := by
    have hzero : (((((b + h : ℕ) : ℤ) * ((y.val : ℕ) : ℤ)
        - ((b : ℕ) : ℤ) * ((η : ℕ) : ℤ)) : ℤ) : ZMod a) = 0 := by
      push_cast
      rw [sub_eq_zero, hyv]
      push_cast at hyeq
      exact hyeq
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ a).mp hzero
  obtain ⟨t, ht⟩ := hdz
  refine mem_bigXiAff_iff.mpr ⟨y.val, Finset.mem_range.mpr (ZMod.val_lt y), ?_⟩
  rw [mem_xiEta] at hξ
  have hz0 : ((k : ℕ) : ZMod H) * ((a : ℕ) : ZMod H) = 0 := by
    rw [← Nat.cast_mul, mul_comm k a, ← hk, ZMod.natCast_self]
  have hpt : affOffset a b h H y.val + (h : ZMod H) * (ξ + twistOffset a H η)
      = affOffset a b h H η + (h : ZMod H) * ξ := by
    rw [← sub_eq_zero]
    have hkeyz : (affOffset a b h H y.val + (h : ZMod H) * (ξ + twistOffset a H η))
        - (affOffset a b h H η + (h : ZMod H) * ξ)
        = ((k : ℕ) : ZMod H)
            * (((((b + h : ℕ) : ℤ) * ((y.val : ℕ) : ℤ)
                - ((b : ℕ) : ℤ) * ((η : ℕ) : ℤ)) : ℤ) : ZMod H) := by
      unfold affOffset twistOffset
      rw [hka]
      push_cast
      ring
    rw [hkeyz, ht, Int.cast_mul, Int.cast_natCast, ← mul_assoc, hz0, zero_mul]
  rw [hpt]
  exact hξ

/-! ## F4b-N8 — the union bound, twice -/

/-- **F4b-N8a (class B).**  For nonnegative `f`, the `a` fibre sums are each `≤ Σ_{bigXiAff} f`:
`Finset.sum_le_sum_of_subset_of_nonneg (xiEta_subset_bigXiAff …)` termwise, then
`Finset.sum_le_card_nsmul`/`Finset.card_range`, `smul_eq_mul`. -/
theorem sum_xiEta_le (a b h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] (f : ZMod H → ℝ)
    (hf : ∀ ξ, 0 ≤ f ξ) :
    ∑ η ∈ Finset.range a, ∑ ξ ∈ xiEta h eps H (affOffset a b h H η), f ξ
      ≤ (a : ℝ) * ∑ ξ ∈ bigXiAff a b h eps H, f ξ := by
  calc ∑ η ∈ Finset.range a, ∑ ξ ∈ xiEta h eps H (affOffset a b h H η), f ξ
      ≤ ∑ _η ∈ Finset.range a, ∑ ξ ∈ bigXiAff a b h eps H, f ξ := by
        refine Finset.sum_le_sum (fun η hη => ?_)
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (xiEta_subset_bigXiAff a b h eps H (Finset.mem_range.mp hη)) (fun ξ _ _ => hf ξ)
    _ = (a : ℝ) * ∑ ξ ∈ bigXiAff a b h eps H, f ξ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **F4b-N8b (class B).**  The same for the TRANSLATED fibres: reindex `ξ ↦ ξ + d_η` (injective:
`add_left_injective`; `Finset.sum_image`), the image is inside `bigXiAff` by
`xiEta_translate_mem_bigXiAff` (this is where `hgcd` is threaded to N7), then as N8a. -/
theorem sum_xiEta_translate_le {a b h : ℕ} (ha : 0 < a) (hgcd : Nat.gcd (b + h) a ∣ h) (eps : ℚ)
    (H : ℕ) [NeZero H] (hdvd : a ∣ H) (f : ZMod H → ℝ) (hf : ∀ ξ, 0 ≤ f ξ) :
    ∑ η ∈ Finset.range a, ∑ ξ ∈ xiEta h eps H (affOffset a b h H η), f (ξ + twistOffset a H η)
      ≤ (a : ℝ) * ∑ ξ ∈ bigXiAff a b h eps H, f ξ := by
  classical
  calc ∑ η ∈ Finset.range a, ∑ ξ ∈ xiEta h eps H (affOffset a b h H η),
        f (ξ + twistOffset a H η)
      ≤ ∑ _η ∈ Finset.range a, ∑ ξ ∈ bigXiAff a b h eps H, f ξ := by
        refine Finset.sum_le_sum (fun η hη => ?_)
        have hηa : η < a := Finset.mem_range.mp hη
        have hinj : ∀ x ∈ xiEta h eps H (affOffset a b h H η),
            ∀ y ∈ xiEta h eps H (affOffset a b h H η),
            x + twistOffset a H η = y + twistOffset a H η → x = y := by
          intro x _ y _ hxy
          exact add_right_cancel hxy
        rw [← Finset.sum_image hinj]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ξ _ _ => hf ξ)
        intro ζ hζ
        rw [Finset.mem_image] at hζ
        obtain ⟨ξ, hξ, rfl⟩ := hζ
        exact xiEta_translate_mem_bigXiAff ha hgcd hdvd hηa hξ
    _ = (a : ℝ) * ∑ ξ ∈ bigXiAff a b h eps H, f ξ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## F4b-N10 / N9 — THE ESTIMATE (N10 carries the body; N9 is its `obtain`: the v1.1 inversion) -/

open private windowVal_c_norm_le from Salt.Entropy.Chowla.CircleMethod in
/-- **F4b-N10 (class C, THE CROWN, CAPPED — THE BODY) — Tao Lemma 3.4 at the class filter, over
`bigXiAff`, constant `h·(1 + 2·C₀)`, with the cap conjunct: F4a's slot shape.**  The `h`-lane's
own move (`circle_method_estimate_sq_bounded_h_core`, `HeadPinLeavesH.lean:371-389`): the core's
proof (`CircleMethod.lean:1366-1498`) with the `η`-expansion, the witness pinned in the `refine` and
the cap discharged by `le_rfl` there — `refine ⟨(h : ℝ) * (1 + 2 * C₀), mul_pos hhR (by
positivity), le_rfl, ?_⟩; intro eps H _ x1 hx1 hdvd hcard; by_cases hH2 : 2 ≤ H`.  Main regime:
`Φ`, `hreal`, `hrefl` as at `h` (`h1 := windowVal_c_norm_le hx1 j`, private, opened above);
`L_aff` cast to `ℂ` (`|L_aff| = ‖(L_aff : ℂ)‖` is `(Complex.norm_real L).symm`, the `h`-core's own
move at `CircleMethod.lean:632`; `Complex.abs_ofReal` does not exist) and expanded by
`filteredCorr_eq_twistSum` into `(1/a)·Σ_η χ(d_η)·L_η`; per `η`: `‖L_η − T_η‖ ≤ h·|𝒫_H|`
(`periodization_total_twist` at `d := twistOffset a H η`), `H·T_η = W_η` (`T_collapse_twist` at
`Φ₂ := χ_{d_η}·Φ`, `c := affOffset η` via `affOffset_eq_mul_twistOffset`), `‖W_η‖ ≤ ε²H²/log H +
(C₀/log H)·(S_η + S'_η)` (`fourier_split_sq_twist`); sum over `η` with `‖χ(d_η)‖ = 1`
(`AddChar.norm_apply`), `Σ_η S_η ≤ a·S` and `Σ_η S'_η ≤ a·S` (`sum_xiEta_le`,
`sum_xiEta_translate_le` at `f := ‖𝓕Φ ·‖²`); the `(1/a)` cancels the `a`, leaving
`|L_aff| ≤ ε²H/log H + (2C₀/(H·log H))·S + h·|𝒫_H|` — BYTE-IDENTICAL to the `h`-core's
`hTle + hhcard` line, so `hrem_nn`/`heq`/`hhcard`/the final `calc` (`CircleMethod.lean:1457-1478`)
close with `C = h(1 + 2C₀)`.  Degenerate `H = 1`, for EVERY `a` and `b` (no `b = 0`, no `a = 1`
needed): `j = 0` and `1 ≤ p·h` (`Nat.mul_pos … hh`), so `windowVal H x1 (j + p·h) = 0` by
`dif_neg` and both `if`-arms are `0` — `split_ifs <;> simp`, `Finset.sum_eq_zero` — the `h`-core's
branch (`:1479-1496`).  `a ∣ H` is consumed terminally at `classFilter_expand` (the lift, N2a) and
at `xiEta_translate_mem_bigXiAff` (the cast, N7) — nowhere else (K8); `hgcd` terminally at N7,
threaded through N8b.  `a` is bound OUTSIDE the `∃ C`: the constant is `a`-free IN THE KERNEL
(K12) — and the cap conjunct is the certificate. -/
theorem circle_method_estimate_sq_bounded_aff (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hgcd : Nat.gcd (b + h) a ∣ h) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ C ≤ (h : ℝ) * (1 + 2 * C₀) ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      a ∣ H →
      ((primeWindow eps H).card : ℝ)
          ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ) else 0|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiAff a b h eps H, (1 / (H : ℝ) ^ 2)
                * ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2) := by
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  refine ⟨(h : ℝ) * (1 + 2 * C₀), mul_pos hhR (by positivity), le_rfl, ?_⟩
  intro eps H _ x1 hx1 hdvd hcard
  by_cases hH2 : 2 ≤ H
  · have hH1r : (1 : ℝ) < (H : ℝ) := by exact_mod_cast hH2
    have hlog : 0 < Real.log (H : ℝ) := Real.log_pos hH1r
    have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
    have hchar1 : ∀ z : ZMod H, ‖(ZMod.stdAddChar z : ℂ)‖ = 1 := by
      intro z
      rw [ZMod.stdAddChar_apply, Circle.norm_coe]
    set Φ : ZMod H → ℂ := fun m => ((windowVal H x1 m.val : ℤ) : ℂ) with hΦ
    have h1 : ∀ j, ‖Φ j‖ ≤ 1 := fun j => windowVal_c_norm_le hx1 j
    have hreal : Φ = fun j : ZMod H => ((windowVal H x1 (ZMod.val j) : ℝ) : ℂ) := by
      funext j
      simp only [hΦ]
      push_cast
      ring
    have hrefl : ∀ ξ : ZMod H, ‖ZMod.dft Φ (-ξ)‖ = ‖ZMod.dft Φ ξ‖ := by
      intro ξ
      rw [hreal]
      exact norm_dft_neg_of_real (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℝ)) ξ
    set S : ℝ := ∑ ξ ∈ bigXiAff a b h eps H, ‖ZMod.dft Φ ξ‖ ^ 2 with hS
    set L : ℝ := ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
        if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
          (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ) else 0 with hL
    have hkeyη : ∀ η ∈ Finset.range a,
        ‖∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
              * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * twistOffset a H η))
              * ∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
                  * (ZMod.stdAddChar (twistOffset a H η * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                      * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ))‖
          ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
            + C₀ / Real.log (H : ℝ) * (1 / (H : ℝ))
                * (∑ ξ ∈ xiEta h eps H (affOffset a b h H η), ‖ZMod.dft Φ ξ‖ ^ 2
                  + ∑ ξ ∈ xiEta h eps H (affOffset a b h H η),
                      ‖ZMod.dft Φ (ξ + twistOffset a H η)‖ ^ 2)
            + (h : ℝ) * ((primeWindow eps H).card : ℝ) := by
      intro η _
      set d : ZMod H := twistOffset a H η with hd
      set c : ZMod H := affOffset a b h H η with hc
      set Lη : ℂ := ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
              * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * d))
              * ∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
                  * (ZMod.stdAddChar (d * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                      * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ)) with hLη
      set Tη : ℂ := ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
              * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * d))
              * ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ)
                  * (ZMod.stdAddChar (d * (m + (((p : ℕ) * h : ℕ) : ZMod H)))
                      * ((windowVal H x1 (m + (((p : ℕ) * h : ℕ) : ZMod H)).val : ℤ) : ℂ)) with hTη
      have hph : ∀ p : primeWindow eps H,
          (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * d))
            = (-(((p : ℕ) : ZMod H) * c)) := by
        intro p
        rw [hc, hd, affOffset_eq_mul_twistOffset a b h H η]
        push_cast
        ring
      have hper : ‖Lη - Tη‖ ≤ (h : ℝ) * ((primeWindow eps H).card : ℝ) := by
        refine le_trans (le_of_eq (congrArg (fun z : ℂ => ‖z‖) ?_))
          (periodization_total_twist (b := b) (h := h) (eps := eps) d hx1)
        rw [hLη, hTη, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun p _ => by rw [mul_sub])
      have hTeq : Tη = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
          * ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * c))
          * ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ)
              * (ZMod.stdAddChar (d * (m + (((p : ℕ) * h : ℕ) : ZMod H)))
                  * ((windowVal H x1 (m + (((p : ℕ) * h : ℕ) : ZMod H)).val : ℤ) : ℂ)) := by
        rw [hTη]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [hph p]
      have hcol : (H : ℂ) * Tη
          = ∑ ξ : ZMod H, ZMod.dft Φ ξ
              * ZMod.dft (fun w : ZMod H => ZMod.stdAddChar (d * w) * Φ w) (-ξ)
              * expSum eps H (-(((c + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ)) := by
        rw [hTeq]
        exact T_collapse_twist h Φ (fun w : ZMod H => ZMod.stdAddChar (d * w) * Φ w) c
      have hsplit : ‖∑ ξ : ZMod H, ZMod.dft Φ ξ
            * ZMod.dft (fun w : ZMod H => ZMod.stdAddChar (d * w) * Φ w) (-ξ)
            * expSum eps H (-(((c + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖
          ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
            + (C₀ / Real.log (H : ℝ))
                * (∑ ξ ∈ xiEta h eps H c, ‖ZMod.dft Φ ξ‖ ^ 2
                  + ∑ ξ ∈ xiEta h eps H c, ‖ZMod.dft Φ (ξ + d)‖ ^ 2) :=
        fourier_split_sq_twist h Φ h1 hrefl c d hC₀ hlog hcard
      have hTle : ‖Tη‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
          + C₀ / Real.log (H : ℝ) * (1 / (H : ℝ))
              * (∑ ξ ∈ xiEta h eps H c, ‖ZMod.dft Φ ξ‖ ^ 2
                + ∑ ξ ∈ xiEta h eps H c, ‖ZMod.dft Φ (ξ + d)‖ ^ 2) := by
        have hHT : (H : ℝ) * ‖Tη‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
            + (C₀ / Real.log (H : ℝ))
                * (∑ ξ ∈ xiEta h eps H c, ‖ZMod.dft Φ ξ‖ ^ 2
                  + ∑ ξ ∈ xiEta h eps H c, ‖ZMod.dft Φ (ξ + d)‖ ^ 2) := by
          rw [show (H : ℝ) * ‖Tη‖ = ‖(H : ℂ) * Tη‖ by
            rw [norm_mul, Complex.norm_natCast], hcol]
          exact hsplit
        have key : (H : ℝ) * ‖Tη‖ ≤ (H : ℝ) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
            + C₀ / Real.log (H : ℝ) * (1 / (H : ℝ))
                * (∑ ξ ∈ xiEta h eps H c, ‖ZMod.dft Φ ξ‖ ^ 2
                  + ∑ ξ ∈ xiEta h eps H c, ‖ZMod.dft Φ (ξ + d)‖ ^ 2)) := by
          refine hHT.trans (le_of_eq ?_)
          field_simp
        exact le_of_mul_le_mul_left key hHpos
      have hLT : ‖Lη‖ ≤ ‖Tη‖ + (h : ℝ) * ((primeWindow eps H).card : ℝ) := by
        have hna := norm_add_le Tη (Lη - Tη)
        rw [add_sub_cancel] at hna
        linarith [hper, hna]
      linarith [hTle, hLT]
    have hLcast : ((L : ℝ) : ℂ) = (1 / (a : ℂ)) * ∑ η ∈ Finset.range a,
        ZMod.stdAddChar (twistOffset a H η)
          * ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
                * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * twistOffset a H η))
                * ∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
                    * (ZMod.stdAddChar (twistOffset a H η * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                        * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ)) := by
      rw [hL]
      exact filteredCorr_eq_twistSum ha hdvd x1
    have hnormL : |L| ≤ (1 / (a : ℝ)) * ∑ η ∈ Finset.range a,
        ‖∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
              * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * twistOffset a H η))
              * ∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
                  * (ZMod.stdAddChar (twistOffset a H η * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                      * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ))‖ := by
      calc |L| = ‖((L : ℝ) : ℂ)‖ := (Complex.norm_real L).symm
        _ = ‖(1 / (a : ℂ)) * ∑ η ∈ Finset.range a,
              ZMod.stdAddChar (twistOffset a H η)
                * ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
                      * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * twistOffset a H η))
                      * ∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
                          * (ZMod.stdAddChar (twistOffset a H η * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                              * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ))‖ := by
            rw [hLcast]
        _ = (1 / (a : ℝ)) * ‖∑ η ∈ Finset.range a,
              ZMod.stdAddChar (twistOffset a H η)
                * ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
                      * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * twistOffset a H η))
                      * ∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
                          * (ZMod.stdAddChar (twistOffset a H η * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                              * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ))‖ := by
            rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
        _ ≤ (1 / (a : ℝ)) * ∑ η ∈ Finset.range a,
              ‖∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
                    * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * twistOffset a H η))
                    * ∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
                        * (ZMod.stdAddChar (twistOffset a H η * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                            * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ))‖ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            exact Finset.sum_congr rfl (fun η _ => by rw [norm_mul, hchar1, one_mul])
    have hf_nn : ∀ ξ : ZMod H, 0 ≤ ‖ZMod.dft Φ ξ‖ ^ 2 := fun ξ => sq_nonneg _
    have hU1 : ∑ η ∈ Finset.range a, ∑ ξ ∈ xiEta h eps H (affOffset a b h H η), ‖ZMod.dft Φ ξ‖ ^ 2
        ≤ (a : ℝ) * S := by
      rw [hS]
      exact sum_xiEta_le a b h eps H (fun ξ => ‖ZMod.dft Φ ξ‖ ^ 2) hf_nn
    have hU2 : ∑ η ∈ Finset.range a, ∑ ξ ∈ xiEta h eps H (affOffset a b h H η),
            ‖ZMod.dft Φ (ξ + twistOffset a H η)‖ ^ 2
        ≤ (a : ℝ) * S := by
      rw [hS]
      exact sum_xiEta_translate_le ha hgcd eps H hdvd (fun ξ => ‖ZMod.dft Φ ξ‖ ^ 2) hf_nn
    have hdec : ∑ η ∈ Finset.range a, ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
          + C₀ / Real.log (H : ℝ) * (1 / (H : ℝ))
              * (∑ ξ ∈ xiEta h eps H (affOffset a b h H η), ‖ZMod.dft Φ ξ‖ ^ 2
                + ∑ ξ ∈ xiEta h eps H (affOffset a b h H η),
                    ‖ZMod.dft Φ (ξ + twistOffset a H η)‖ ^ 2)
          + (h : ℝ) * ((primeWindow eps H).card : ℝ))
        = (a : ℝ) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
          + C₀ / Real.log (H : ℝ) * (1 / (H : ℝ))
              * ((∑ η ∈ Finset.range a, ∑ ξ ∈ xiEta h eps H (affOffset a b h H η),
                    ‖ZMod.dft Φ ξ‖ ^ 2)
                + ∑ η ∈ Finset.range a, ∑ ξ ∈ xiEta h eps H (affOffset a b h H η),
                    ‖ZMod.dft Φ (ξ + twistOffset a H η)‖ ^ 2)
          + (a : ℝ) * ((h : ℝ) * ((primeWindow eps H).card : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib]
    have hsum2 : ∑ η ∈ Finset.range a, ‖∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
                * ZMod.stdAddChar (-((((p : ℕ) * (b + h) : ℕ) : ZMod H) * twistOffset a H η))
                * ∑ j ∈ Finset.range H, ((windowVal H x1 j : ℤ) : ℂ)
                    * (ZMod.stdAddChar (twistOffset a H η * ((j + (p : ℕ) * h : ℕ) : ZMod H))
                        * ((windowVal H x1 (j + (p : ℕ) * h) : ℤ) : ℂ))‖
        ≤ (a : ℝ) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
          + C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) * ((a : ℝ) * S + (a : ℝ) * S)
          + (a : ℝ) * ((h : ℝ) * ((primeWindow eps H).card : ℝ)) := by
      refine (Finset.sum_le_sum hkeyη).trans ?_
      rw [hdec]
      have hK : (0 : ℝ) ≤ C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) := by positivity
      have hmul := mul_le_mul_of_nonneg_left (add_le_add hU1 hU2) hK
      linarith
    have hane : (a : ℝ) ≠ 0 := ne_of_gt haR
    have hLfinal : |L| ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
        + 2 * C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) * S
        + (h : ℝ) * ((primeWindow eps H).card : ℝ) := by
      refine hnormL.trans ?_
      refine le_trans (mul_le_mul_of_nonneg_left hsum2 (by positivity)) (le_of_eq ?_)
      field_simp
      ring
    rw [← Finset.mul_sum, ← hS]
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun ξ _ => sq_nonneg _)
    have hA_nn : 0 ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) := by positivity
    have hB_nn : 0 ≤ S / ((H : ℝ) * Real.log (H : ℝ)) := div_nonneg hS_nn (by positivity)
    have hc1 : 0 ≤ (h : ℝ) - 1 + (h : ℝ) * C₀ := by nlinarith [mul_pos hhR hC₀]
    have hc2 : 0 ≤ (h : ℝ) + 2 * C₀ * ((h : ℝ) - 1) := by
      nlinarith [mul_nonneg hC₀.le (by linarith : (0 : ℝ) ≤ (h : ℝ) - 1)]
    have hrem_nn : 0 ≤ ((h : ℝ) - 1 + (h : ℝ) * C₀)
          * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
        + ((h : ℝ) + 2 * C₀ * ((h : ℝ) - 1)) * (S / ((H : ℝ) * Real.log (H : ℝ))) :=
      add_nonneg (mul_nonneg hc1 hA_nn) (mul_nonneg hc2 hB_nn)
    have hH0 : (H : ℝ) ≠ 0 := ne_of_gt hHpos
    have hLe0 : Real.log (H : ℝ) ≠ 0 := ne_of_gt hlog
    have heq : (h : ℝ) * (1 + 2 * C₀) * ((H : ℝ) / Real.log (H : ℝ))
          * ((eps : ℝ) ^ 2 + 1 / (H : ℝ) ^ 2 * S)
        = ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
            + 2 * C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) * S)
          + (h : ℝ) * (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
          + (((h : ℝ) - 1 + (h : ℝ) * C₀)
                * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
              + ((h : ℝ) + 2 * C₀ * ((h : ℝ) - 1))
                  * (S / ((H : ℝ) * Real.log (H : ℝ)))) := by
      field_simp
      ring
    have hhcard : (h : ℝ) * ((primeWindow eps H).card : ℝ)
        ≤ (h : ℝ) * (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))) :=
      mul_le_mul_of_nonneg_left hcard hhR.le
    refine hLfinal.trans ?_
    rw [heq]
    linarith [hhcard, hrem_nn]
  · have hH1 : H = 1 := by have := NeZero.pos H; omega
    have hlog0 : Real.log (H : ℝ) = 0 := by rw [hH1]; simp
    have hL0 : (∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
        if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
          (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun p _ => ?_)
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      have hph : 0 < (p : ℕ) * h := Nat.mul_pos (prime_of_mem_primeWindow p.2).pos hh
      have hge : ¬ (j + (p : ℕ) * h < H) := by omega
      have hz : windowVal H x1 (j + (p : ℕ) * h) = 0 := by rw [windowVal, dif_neg hge]
      rw [hz]
      split_ifs <;> simp
    rw [hL0, abs_zero]
    have hmid : (H : ℝ) / Real.log (H : ℝ) = 0 := by rw [hlog0, div_zero]
    rw [hmid]
    simp

/-- **F4b-N9 (class A, THE CORE, uncapped) — the `obtain` from N10.**  The v1.1 INVERSION (verdict
A2): an `obtain` from an `∃ C` leaves an OPAQUE witness, so the cap can only be read off where the
witness is PINNED — N10.  This is therefore the one-liner:
`obtain ⟨C, hC, _, hall⟩ := circle_method_estimate_sq_bounded_aff a b h ha hh hgcd C₀ hC₀;
exact ⟨C, hC, hall⟩`.  No in-file consumer other than the record. -/
theorem circle_method_estimate_sq_aff_core (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hgcd : Nat.gcd (b + h) a ∣ h) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      a ∣ H →
      ((primeWindow eps H).card : ℝ)
          ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ) else 0|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiAff a b h eps H, (1 / (H : ℝ) ^ 2)
                * ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2) := by
  obtain ⟨C, hC, _, hall⟩ := circle_method_estimate_sq_bounded_aff a b h ha hh hgcd C₀ hC₀
  exact ⟨C, hC, hall⟩

/-! ## F4b-N11 — THE DISCHARGE: F4a's head without its slot -/

/-- **F4b-N11 (class A) — the affine head UNSLOTTED.**  `log_chowla_aff_of_door a b h ha hh hba hah7
(circle_method_estimate_sq_bounded_aff a b h ha hh hgcd (2 * Real.log 4) (by positivity)) hcrown A₀`
— the slot `hcm` supplied by N10 at `C₀ = 2·log 4` (the cap reads `h·(1 + 2·(2·log 4))`, the head's
literal; `0 < 2·log 4` by `positivity` via `evalLogNatLit`).  The head's binder list is F4a's plus
`hgcd`; `hcrown` unchanged (the MR fence). -/
theorem log_chowla_aff_of_door_unslotted (a b h : ℕ) (ha : 0 < a) (hh : 0 < h) (hba : b < a)
    (hgcd : Nat.gcd (b + h) a ∣ h)
    (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7)
    (hcrown : ∀ A₀' : ℝ,
      ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
        ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀' ≤ A ∧
        ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
          flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
          ∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * ((a * h : ℕ) : ℝ) ^ 2) ∧
            1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
            E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
                * (Real.log (Ra.ω : ℝ) - 1)) ∧
            MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E))
    (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
        flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
        (∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * ((a * h : ℕ) : ℝ) ^ 2) ∧
          1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
          E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
              * (Real.log (Ra.ω : ℝ) - 1)) ∧
          MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E)) ∧
        ∃ δ₀ : ℝ, 0 < δ₀ ∧ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) ≤ δ₀ ∧
          ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ δ₀ → MRTUniformityXiL2AffW h Ra ρ' →
            ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω := by
  exact log_chowla_aff_of_door a b h ha hh hba hah7
    (circle_method_estimate_sq_bounded_aff a b h ha hh hgcd (2 * Real.log 4) (by positivity))
    hcrown A₀

end Salt.Entropy.Chowla
