/-
# λ-BV wave 2-S, step F4b — THE AFFINE CIRCLE-METHOD ESTIMATE (the producer of F4a's slot)

**Frozen statement-only 2026-09-04 16:2x (math, Fable head on kriterion), from the price brief
`2026-09-04-math-PRICE-lbv-w2S-F4b-circle-estimate.md`.**  Tao 1509.05422 Lemma 3.4 at the class
filter `j + 1 ≡ p·b (mod a)`, over the affine large-spectrum set `bigXiAff a b h eps H` (F1-X1),
with
the `h`-lane's constant `h·(1 + 2·C₀)` — `a`-FREE (M1 LIVE).  Its crown
`circle_method_estimate_sq_bounded_aff`
has EXACTLY the shape of F4a's slot `hcm` (`StrideShell.lean`, the head `log_chowla_aff_of_door`)
after
F4b S-1 (`a ∣ H →` in the slot's `∀`-prefix), and `log_chowla_aff_of_door_unslotted` discharges
the slot by
one class-A name.

THE ROUTE (the `h`-core `circle_method_estimate_sq_h_core`, `CircleMethod.lean:1366-1508`, with the
`η`-expansion of the class filter).  Write `d_η := η·(H/a) : ZMod H` (`twistOffset`), `χ_d(m) :=
stdAddChar(d·m)`, `Φ := (windowVal H x1 ·)` on `ZMod H`, `c_η := affOffset a b h H η = (b+h)·d_η`.
1. `1_{j+1 ≡ pb (a)} = (1/a)·Σ_{η<a} χ_{d_η}(j + 1 − pb)` (`classFilter_expand`, orthogonality on
`ZMod a`
   lifted through `a ∣ H` — `stdAddChar_lift_of_dvd`); with `j + 1 − pb = (j + ph) + 1 − p(b+h)`
   the twist
   lands on the SECOND window factor: `L_aff = (1/a)·Σ_η χ_{d_η}(1)·L_η`, `L_η = Σ_p
   (1/p)·χ_{d_η}(−p(b+h))·
   Σ_{j<H} x_j·x_{j+ph}·χ_{d_η}(j+ph)` (`filteredCorr_eq_twistSum`).
2. Periodization at the twisted second window (`periodization_total_twist`): `‖L_η − T_η‖ ≤
h·|𝒫_H|`.
3. Collapse (`T_collapse_twist`): `H·T_η = Σ_ξ 𝓕Φ(ξ)·𝓕(χ_{d_η}·Φ)(−ξ)·expSum(−(c_η + h·ξ).val/H)`
— the
   per-`p` phase `χ_{d_η}(−p(b+h)) = stdAddChar(−p·c_η)` folded into `correlation_dft`'s character.
4. THE TRANSLATE (`dft_twist`): `𝓕(χ_d·Φ)(k) = 𝓕Φ(k − d)` — so the second Fourier factor sits at
   `−ξ − d_η`, and by the reality reflection at `ξ + d_η`: the `h`-lane's diagonal collapse
   `‖𝓕Φ ξ‖·‖𝓕Φ(−ξ)‖ = ‖𝓕Φ ξ‖²` FAILS here.  AM–GM leaves a PARTNER sum over the translate `Ξ_η +
   d_η`
   (`fourier_split_sq_twist`).
5. THE PARTNER LANDS (`xiEta_translate_mem_bigXiAff`): under **`gcd(b+h, a) ∣ h`** some `η' < a` has
   `(b+h)·η' ≡ b·η (mod a)`, so `c_{η'} + h(ξ + d_η) = c_η + hξ` and `ξ + d_η ∈ bigXiAff`.  This
   binder is
   the producer's, NOT the slot's: it lives on the discharge (`log_chowla_aff_of_door_unslotted`)
   and on
   F5's prize.  Without it the partner leaves the set (price §1 F-2, `(a,b,h) = (4,2,2)`; K2).
6. THE UNION (`sum_xiEta_le`, `sum_xiEta_translate_le`): each `η`-sum is `≤ Σ_{bigXiAff}`, so
   `(1/a)·Σ_η (S_η + S'_η)/2 ≤ S` — **the `(1/a)·a` cancellation**, `C = h·(1 + 2·C₀)`.
7. Assembly (`circle_method_estimate_sq_aff_core`): BYTE-IDENTICAL to the `h`-core's remainder line
   (`CircleMethod.lean:1470-1500`) after steps 2–6; the `H = 1` branch as at `h`.

⛔ HONEST LABEL.  Every declaration below is statement-only at the freeze (sorry-bodied, recipe in
the
docstring), built as a module through `../saltbuild.sh`; NO executor fires before the helm's refuter
verdict.  F4b moves no door and closes no prize: the `≈ 214.4` miss at `(210, 2)` is F5's, and F5's
prize statement GAINS the binder `gcd(b+h, a) ∣ h`.  Nothing here bears on twin primes.  ⛔ MERGE
FENCE
(iron rule 2): `math/lbv-w2s-f4b` never reaches `main` until every obligation in this file lands
sorry-free.
-/
import Salt.Entropy.Chowla.StrideShell
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ## F4b-N0 — the twist offset and the `η`-fibre of the affine set -/

/-- **F4b-N0a (def).**  The twist offset `d_η := η·(H/a)` as an element of `ZMod H`: with `a ∣ H`
the
character `m ↦ stdAddChar(d_η·m)` on `ZMod H` is `e(η·m/a)`.  `affOffset a b h H η = (b + h)·d_η`
(`affOffset_eq_mul_twistOffset`). -/
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
  sorry

/-- **F4b-N0d (class A).**  Membership in the `η`-fibre: `Finset.mem_filter`, `Finset.mem_univ`,
`true_and` after `unfold xiEta`. -/
theorem mem_xiEta {h : ℕ} {eps : ℚ} {H : ℕ} [NeZero H] {c ξ : ZMod H} :
    ξ ∈ xiEta h eps H c ↔ c + (h : ZMod H) * ξ ∈ bigXi eps H := by
  sorry

/-! ## F4b-N1 — THE TRANSLATE: a modulation moves the DFT -/

/-- **F4b-N1 (class B) — THE DFT TRANSLATE.**  Modulating by the character at `d` translates the
transform by `d`: `𝓕(χ_d·Φ)(k) = 𝓕Φ(k − d)`.  `ZMod.dft_apply` on both sides (`𝓕 Φ k = Σ_j
stdAddChar(−(j·k)) • Φ j`, `smul_eq_mul`), then termwise `stdAddChar(−(j·k)) * stdAddChar(d·j) =
stdAddChar(−(j·(k − d)))` by `← AddChar.map_add_eq_mul` and `congr 1; ring`.  THE SIGN (K1):
mathlib's
`dft_apply` carries `stdAddChar (-(j * k))`, so the modulation `stdAddChar (d * j)` SUBTRACTS `d`
from the frequency — derived, not copied. -/
theorem dft_twist {H : ℕ} [NeZero H] (Φ : ZMod H → ℂ) (d k : ZMod H) :
    ZMod.dft (fun m : ZMod H => ZMod.stdAddChar (d * m) * Φ m) k = ZMod.dft Φ (k - d) := by
  sorry

/-- **F4b-N1b (class A).**  The modulated window keeps its pointwise bound: `‖stdAddChar(d·m) * Φ
m‖ =
‖Φ m‖` — `norm_mul`, `ZMod.stdAddChar_apply`, `Circle.norm_coe` (`‖(z : Circle)‖ = 1`), `one_mul`.
-/
theorem norm_twist_mul {H : ℕ} [NeZero H] (Φ : ZMod H → ℂ) (d m : ZMod H) :
    ‖ZMod.stdAddChar (d * m) * Φ m‖ = ‖Φ m‖ := by
  sorry

/-! ## F4b-N2 — the class filter expanded over `η ∈ ℤ/aℤ`, lifted through `a ∣ H` -/

/-- **F4b-N2a (class B) — the character lift.**  With `a ∣ H`, `e(η·m/a)` on `ZMod a` IS
`stdAddChar` on `ZMod H` at `η·(H/a)·m`: `ZMod.stdAddChar_coe` (`stdAddChar (j : ZMod N) =
Circle.exp
(2·π·j/N)`-shape) on both sides, then `(η·(H/a)·m : ℝ)/H = (η·m : ℝ)/a` from `(H/a)·a = H`
(`Nat.div_mul_cancel hdvd`, `Nat.cast_div hdvd`, `field_simp`). -/
theorem stdAddChar_lift_of_dvd {a H : ℕ} [NeZero a] [NeZero H] (hdvd : a ∣ H) (η m : ℕ) :
    (ZMod.stdAddChar ((η * m : ℕ) : ZMod a) : ℂ)
      = ZMod.stdAddChar (twistOffset a H η * (m : ZMod H)) := by
  sorry

/-- **F4b-N2 (class B) — THE EXPANSION.**  For `0 < a`, `a ∣ H` and naturals `u v`:
`[u ≡ v (mod a)] = (1/a)·Σ_{η<a} stdAddChar(d_η·(u − v))` in `ℂ`.  Orthogonality of the characters
of
`ZMod a`: the map `η ↦ stdAddChar_a(η·t)` is the character `(ZMod.stdAddChar).mulShift t`, whose
sum over
`ZMod a` is `a` if `(t : ZMod a) = 0` and `0` otherwise (`AddChar.sum_eq_ite` /
`AddChar.sum_eq_zero_iff_ne_one`
with `ZMod.stdAddChar`'s primitivity `ZMod.isPrimitive_stdAddChar`); the `range a` sum is the
`ZMod a`
sum through `ZMod.val` (`Finset.sum_range` ↔ `Fin.sum_univ_eq_sum_range`, `ZMod.finEquiv`); lift
each term
through `stdAddChar_lift_of_dvd` with `t := u − v` handled as `u = v + t` or `v = u + t`
(`Nat.cast_sub`
avoided: state at `ZMod H` with `(u : ZMod H) − (v : ZMod H)` and use `AddChar.map_neg_eq_inv`/
`map_add_eq_mul`).  ~25 lines. -/
theorem classFilter_expand {a H : ℕ} [NeZero H] (ha : 0 < a) (hdvd : a ∣ H) (u v : ℕ) :
    (if ((u : ℕ) : ZMod a) = ((v : ℕ) : ZMod a) then (1 : ℂ) else 0)
      = (1 / (a : ℂ)) * ∑ η ∈ Finset.range a,
          ZMod.stdAddChar (twistOffset a H η * ((u : ZMod H) - (v : ZMod H))) := by
  sorry

/-- **F4b-N3 (class B) — the filtered correlation as the twist sum.**  `classFilter_expand` at
`u := j + 1`, `v := p·b` inside the double sum, `(j + 1) − p·b = ((j + p·h) + 1) − p·(b + h)` in
`ZMod H`
(`push_cast; ring`), `AddChar.map_add_eq_mul` twice and `AddChar.map_neg_eq_inv`-shape for the
`−p(b+h)`
factor, then `Finset.mul_sum`/`Finset.sum_comm` ×2 to bring `Σ_η` outside.  The window factors are
cast `ℤ → ℂ` (`Complex.ofReal_intCast`-shape: the LHS is a REAL sum cast to `ℂ`,
`Complex.ofReal_sum`,
`Complex.ofReal_mul`, `Complex.ofReal_intCast`). -/
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
  sorry

/-! ## F4b-N4 / N5 — periodization and collapse at the twisted second window -/

/-- **F4b-N4 (class B) — periodization at the twisted second window.**  The twin of
`periodization_total_h` (`CircleMethod.lean:1003`), whose landed per-prime bound
`perprime_diff_norm_le`
is stated at INTEGER windows and is `private`: here the second window is COMPLEX (the twist), so the
per-prime bound is re-proved in place — the two sums differ exactly at the `j` with `H ≤ j + p·h`
(the ℕ-window is `0` there, `windowVal`'s `dif_neg`; the `ZMod`-window wraps), at most `p·h`
indices,
each term of norm `≤ 1` (`windowVal_c_norm_le`-shape ×2, `norm_twist_mul`), so `‖…‖ ≤ (1/p)·(p·h)
= h`
per prime (`norm_sum_le`, `Finset.card_le`), and `Σ_p h = h·|𝒫_H|`.  The extra phase
`stdAddChar(−p(b+h)·d)` has norm `1` and factors out of the per-prime difference. -/
theorem periodization_total_twist {a b h : ℕ} {eps : ℚ} {H : ℕ} [NeZero H] (d : ZMod H)
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
  sorry

/-- **F4b-N5 (class B) — the collapse at the twisted second window with the per-`p` phase.**
`T_collapse_h` (`CircleMethod.lean:961`, private — `open private … from
Salt.Entropy.Chowla.CircleMethod
in`, or its body replayed) at `Φ₂ := χ_d·Φ₁` with the phase `stdAddChar(−p·c)` folded in:
`correlation_dft
Φ₁ Φ₂ (p·h)` gives `stdAddChar(−(p·h·ξ))`, times `stdAddChar(−p·c)` is `stdAddChar(−(p·(c + h·ξ)))`
(`AddChar.map_add_eq_mul`, `push_cast; ring`), then `expSum_eq_char_sum` (private, same file) at
`c + h·ξ`.  `c` is generic; the consumer takes `c := affOffset a b h H η = (b+h)·d_η`
(`affOffset_eq_mul_twistOffset`). -/
theorem T_collapse_twist {eps : ℚ} {H : ℕ} [NeZero H] (h : ℕ) (Φ₁ Φ₂ : ZMod H → ℂ) (c : ZMod H) :
    (H : ℂ) * ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ))
        * ZMod.stdAddChar (-(((p : ℕ) : ZMod H) * c))
        * ∑ m : ZMod H, Φ₁ m * Φ₂ (m + (((p : ℕ) * h : ℕ) : ZMod H))
      = ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₂ (-ξ)
          * expSum eps H (-(((c + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ)) := by
  sorry

/-! ## F4b-N6 — the squared Fourier split at a translated partner -/

/-- **F4b-N6 (class C) — THE SPLIT WITH THE PARTNER.**  The twin of `fourier_split_sq_h`
(`CircleMethod.lean:1133`) at the second window `χ_d·Φ`: by `dft_twist` the second factor is
`𝓕Φ(−ξ − d)`, and by the reality reflection `hrefl` (at the REAL `Φ`) its norm is `‖𝓕Φ(ξ + d)‖`.
Minor arc (`ξ ∉ Ξ_c`): `‖expSum‖ < ε²/log H` (`mem_bigXi`), then `dft_l1_reflect Φ (χ_d·Φ)`
(private;
generic in two windows of norm `≤ 1` — `norm_twist_mul`) gives `ε²H²/log H`.  Major arc (`ξ ∈ Ξ_c`):
`expSum_norm_le_major` (private) gives `2C₀/log H`, and AM–GM `‖A‖·‖B‖ ≤ (‖A‖² + ‖B‖²)/2`
(`two_mul_le_add_sq`) splits the product into the two sums — the `h`-lane's `rw [hrefl ξ]` collapse
is NOT available (K1: the factors sit at `ξ` and `ξ + d`). -/
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
  sorry

/-! ## F4b-N7 — the fibre and its translate land in `bigXiAff` -/

/-- **F4b-N7a (class A).**  The `η`-fibre at `affOffset η` is inside `bigXiAff`:
`Finset.subset_iff`,
`mem_xiEta`, `mem_bigXiAff_iff` with the witness `η` (`Finset.mem_range.mpr hη`). -/
theorem xiEta_subset_bigXiAff (a b h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] {η : ℕ} (hη : η < a) :
    xiEta h eps H (affOffset a b h H η) ⊆ bigXiAff a b h eps H := by
  sorry

/-- **F4b-N7 (class C, THE PARTNER LANDS) — the block's one real arithmetic.**  Under `gcd(b+h, a)
∣ h`
the translate of the `η`-fibre by `d_η` is inside `bigXiAff`: choose `η' < a` with `(b+h)·η' ≡ b·η
(mod a)`
— write `g := gcd(b+h, a)`, `b + h = g·u`, `a = g·v` with `Nat.Coprime u v`
(`Nat.coprime_div_gcd_div_gcd`),
`g ∣ b` from `g ∣ b + h` and `g ∣ h` (`Nat.dvd_sub'`), so the congruence is `u·η' ≡ (b/g)·η (mod
v)`, solved
by `η' := ((b/g)·η·u⁻¹) % v` with `u⁻¹` the inverse of `u` mod `v` (`Nat.gcdA`/`ZMod.unitOfCoprime
v`,
`ZMod.val`); then `η' < v ≤ a`.  The membership: `mem_bigXiAff_iff` with witness `η'`; the point
`affOffset η' + h·(ξ + d_η)` equals `affOffset η + h·ξ` in `ZMod H` because `((b+h)η' + hη −
(b+h)η)·(H/a)
≡ 0 (mod H)` — `affOffset_eq_mul_twistOffset`, `twistOffset` unfolded, `a ∣ H` for
`(k·a)·(H/a) = k·H` (`Nat.div_mul_cancel`), `ZMod.natCast_self`/`ZMod.natCast_zmod_eq_zero_iff_dvd`.
Uniform in `ξ`. -/
theorem xiEta_translate_mem_bigXiAff {a b h : ℕ} (ha : 0 < a) (hgcd : Nat.gcd (b + h) a ∣ h)
    {eps : ℚ} {H : ℕ} [NeZero H] (hdvd : a ∣ H) {η : ℕ} (hη : η < a) {ξ : ZMod H}
    (hξ : ξ ∈ xiEta h eps H (affOffset a b h H η)) :
    ξ + twistOffset a H η ∈ bigXiAff a b h eps H := by
  sorry

/-! ## F4b-N8 — the union bound, twice -/

/-- **F4b-N8a (class B).**  For nonnegative `f`, the `a` fibre sums are each `≤ Σ_{bigXiAff} f`:
`Finset.sum_le_sum_of_subset_of_nonneg (xiEta_subset_bigXiAff …)` termwise, then
`Finset.sum_le_card_nsmul`/`Finset.card_range`, `smul_eq_mul`. -/
theorem sum_xiEta_le (a b h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] (f : ZMod H → ℝ)
    (hf : ∀ ξ, 0 ≤ f ξ) :
    ∑ η ∈ Finset.range a, ∑ ξ ∈ xiEta h eps H (affOffset a b h H η), f ξ
      ≤ (a : ℝ) * ∑ ξ ∈ bigXiAff a b h eps H, f ξ := by
  sorry

/-- **F4b-N8b (class B).**  The same for the TRANSLATED fibres: reindex `ξ ↦ ξ + d_η` (injective:
`add_left_injective`; `Finset.sum_image`), the image is inside `bigXiAff` by
`xiEta_translate_mem_bigXiAff`, then as N8a. -/
theorem sum_xiEta_translate_le {a b h : ℕ} (ha : 0 < a) (hgcd : Nat.gcd (b + h) a ∣ h) (eps : ℚ)
    (H : ℕ) [NeZero H] (hdvd : a ∣ H) (f : ZMod H → ℝ) (hf : ∀ ξ, 0 ≤ f ξ) :
    ∑ η ∈ Finset.range a, ∑ ξ ∈ xiEta h eps H (affOffset a b h H η), f (ξ + twistOffset a H η)
      ≤ (a : ℝ) * ∑ ξ ∈ bigXiAff a b h eps H, f ξ := by
  sorry

/-! ## F4b-N9 / N10 — THE ESTIMATE -/

/-- **F4b-N9 (class C, THE CORE) — Tao Lemma 3.4 at the class filter, over `bigXiAff`, constant
`h·(1 + 2·C₀)`.**  The `h`-core's proof (`CircleMethod.lean:1366-1508`) with the `η`-expansion:
`refine
⟨h·(1 + 2C₀), …⟩`; `by_cases hH2 : 2 ≤ H` — main regime: `Φ`, `hreal`, `hrefl` as at `h`; `L_aff`
cast to
`ℂ` and expanded by `filteredCorr_eq_twistSum` into `(1/a)·Σ_η χ(d_η)·L_η`; per `η`: `‖L_η − T_η‖ ≤
h·|𝒫_H|` (`periodization_total_twist`), `H·T_η = W_η` (`T_collapse_twist` at `Φ₂ := χ_{d_η}·Φ`, `c
:=
affOffset η` via `affOffset_eq_mul_twistOffset`), `‖W_η‖ ≤ ε²H²/log H + (C₀/log H)·(S_η + S'_η)`
(`fourier_split_sq_twist`); sum over `η` with `‖χ(d_η)‖ = 1`, `Σ_η S_η ≤ a·S` and `Σ_η S'_η ≤ a·S`
(`sum_xiEta_le`, `sum_xiEta_translate_le` at `f := ‖𝓕Φ ·‖²`); the `(1/a)` cancels the `a`, leaving
`|L_aff| ≤ ε²H/log H + (2C₀/(H·log H))·S + h·|𝒫_H|` — BYTE-IDENTICAL to the `h`-core's `hTle +
hhcard`
line, so `heq`/`hrem_nn`/the final `calc` (`:1470-1500`) close with `C = h(1 + 2C₀)`.  Degenerate
`H = 1`
(then `a = 1`, `b = 0` from `a ∣ H`, `b < a`): the `h`-core's branch.  `a ∣ H` is consumed at
`classFilter_expand` (the lift) and at `xiEta_translate_mem_bigXiAff` (the cast) — and nowhere
else (K8);
`gcd(b+h,a) ∣ h` at the partner only. -/
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
  sorry

/-- **F4b-N10 (class A) — THE CROWN, CAPPED: F4a's slot shape.**
`circle_method_estimate_sq_aff_core`
with the conjunct `C ≤ h·(1 + 2·C₀)` at the landed `refine` witness (as
`circle_method_estimate_sq_bounded_h_core`, `HeadPinLeavesH.lean:375`: the only edit is the extra
`le_rfl`) — either re-run the core's body with the extra conjunct, or `obtain` the core and read the
witness off (the core's `C` is `h·(1 + 2·C₀)` by construction; if the executor lands N9 with a
`refine ⟨h * (1 + 2 * C₀), …⟩` the cap is `le_rfl` here).  `a` is bound OUTSIDE the `∃ C`: the
constant
is `a`-free IN THE KERNEL (K12). -/
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
  sorry

/-! ## F4b-N11 — THE DISCHARGE: F4a's head without its slot -/

/-- **F4b-N11 (class A) — the affine head UNSLOTTED.**  `log_chowla_aff_of_door a b h ha hh hba hah7
(circle_method_estimate_sq_bounded_aff a b h ha hh hgcd (2 * Real.log 4) (by positivity)) hcrown A₀`
— the slot `hcm` supplied by N10 at `C₀ = 2·log 4` (the cap reads `h·(1 + 2·(2·log 4))`, the head's
literal).  The head's binder list is F4a's plus `hgcd`; `hcrown` unchanged (the MR fence). -/
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
  sorry

end Salt.Entropy.Chowla
