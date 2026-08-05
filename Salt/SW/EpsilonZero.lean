/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.ZetaZeroFree

/-!
# EPSILON-ZERO — the explicit low-height ζ zero-free strip (the `ε₀` floor)

Design: `docs/exploration/cmu-hunt-0802.md` §2/§4(a) (leaf #1), the RIDER-TRACE finding
"THE ONE GENUINELY OPEN STONE … the eps0 floor … ONE STONE, THREE RIDERS"
(`docs/blueprints/flags.md`), council v7 item C4 (`docs/exploration/council-0804.md`,
ruled *queued this week*).

`Salt.SW.zeta_zero_free_strip` produces its constant `ε₀` by **compactness**
(`IsCompact.exists_isMinOn` on the `Re = 1` segment): the constant exists but is opaque, and
every consumer that *divides* by it — `c₃ = min(1/75712, ε₀·log 2)` in
`zeta_zero_free_region`, hence `Cbig`, `T₀z`, the band-lane constant — is therefore
non-effective. This module abolishes that compactness step in the genre of
`Salt/SW/TauExt.lean`: an **explicit numeral** replaces the extremal-value minimum.

## The statement

`zeta_zero_free_strip_explicit : ζ ρ = 0 → |Im ρ| ≤ 1 → Re ρ ≤ 1 − 10⁻⁶`.

## The route (and why it is not circular)

The height-`≤ 1` box splits at `|γ| = 1/5`, and **neither branch touches
`zeta_zero_free_strip` or `zeta_zero_free_region`** (nor anything downstream of them):

1. **`|γ| ≤ 1/5` — pole dominance.** The corpus's own Abel identity
   `Zc_eq_series` (`Salt/SW/ZetaPartialFractions.lean`) says `(s−1)ζ(s) = 1 + (s−1)·R(s)` on
   `Re s > 0` with `‖R(s)‖ ≤ ‖s‖(1 + 1/Re s)` (`norm_R_le`). A zero forces
   `‖s−1‖·‖R(s)‖ = 1`, so `ζ` cannot vanish where `‖s−1‖·‖s‖(1+1/Re s) < 1` — a disk about the
   pole, here comfortably containing the sub-box `Re ≥ 1 − 10⁻⁶`, `|Im| ≤ 1/5`
   (the product is `≤ (1/5 + 10⁻⁶)·(6/5)·3 = 0.7200036`).
2. **`1/5 < |γ| ≤ 1` — the 3-4-1 keep-one chain.** Exactly the machinery
   `zeta_zero_free_region` uses in its `|γ| ≥ 1` branch (`three_four_one_logDeriv`,
   `neg_logDeriv_zeta_le`, `zeta_neg_re_logDeriv_le_keep`, `zeta_neg_re_logDeriv_le`), all of
   which sit *above* the strip in the dependency order. The only change is the pole real
   parts: `Re(1/(s₁−1)) ≤ 1/|γ| ≤ 5` and `Re(1/(s₂−1)) ≤ 1/(2|γ|) ≤ 5/2` instead of `≤ 1`,
   and `log(|γ|+2) ≤ log 4 ≤ 1.4`. At `σ = 1 + 1/15200` the chain reads
   `4/(σ−β) ≤ 3/(σ−1) + 53186`, which is incompatible with `β > 1 − 10⁻⁶`.

The `1/5` split point is exactly the trade: branch 1 wants `|γ|` small (the disk), branch 2
wants `|γ|` bounded away from `0` (the pole terms `1/|γ|`).

## What it unlocks

`ε₀ ≥ 10⁻⁶` makes `c₃ = min(1/75712, ε₀·log 2)` an explicit positive numeral
(`≥ log 2/10⁶ ≥ 6·10⁻⁷`), which is the floor the three riders named by RIDER-TRACE need:
the `cs`-genre leaves, the `T₀z` ceiling (`Cbig = 9000·c_vk + c_vk/(2δ₀) + 1`, `δ₀ = ε₀/2`),
and the band lane's effective discharge.
-/

namespace Salt.SW

open Complex DirichletCharacter Metric
open scoped LSeries.notation Topology

/-! ## 1. Pole dominance — the compactness-free disk about `s = 1` -/

/-- **Pole dominance.** If `Re s > 0` and `‖s−1‖·(‖s‖·(1 + 1/Re s)) < 1` then `ζ s ≠ 0`.

From the Abel identity `Zc s = 1 + (s−1)·∑ dTerm s` on `Re s > 0`: a zero of `ζ` at `s ≠ 1`
is a zero of `Zc`, forcing `(s−1)·∑ dTerm s = −1`, hence `‖s−1‖·‖∑ dTerm s‖ = 1`, which the
growth bound `norm_R_le` contradicts. No compactness, no extremal value — an explicit
inequality. -/
theorem zeta_ne_zero_of_pole_dominant {s : ℂ} (hs : 0 < s.re)
    (h : ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) < 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hne1 : s ≠ 1 := by
    intro h1
    rw [h1] at hz
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hz
  have hZc : Zc s = 0 := by rw [Zc_eq_of_ne hne1, hz, mul_zero]
  have hser := Zc_eq_series s hs
  rw [hZc] at hser
  have hR : (s - 1) * (∑' n : ℕ, dTerm s (n + 1)) = -1 := by linear_combination -hser
  have hnorm : ‖s - 1‖ * ‖∑' n : ℕ, dTerm s (n + 1)‖ = 1 := by
    rw [← norm_mul, hR, norm_neg, norm_one]
  have hRle : ‖∑' n : ℕ, dTerm s (n + 1)‖ ≤ ‖s‖ * (1 + 1 / s.re) := norm_R_le s hs
  have hs1 : (0 : ℝ) ≤ ‖s - 1‖ := norm_nonneg _
  nlinarith [hnorm, hRle, hs1, h]

/-! ## 2. The explicit strip -/

set_option maxHeartbeats 800000 in
-- Branch 2 runs the full 3-4-1 assembly (three heavy `LFunction`/`LSeries` log-derivative
-- rewrites plus the Davenport chain) inside a single declaration, exactly as
-- `zeta_zero_free_region` does; it needs more than the default budget.
/-- **EPSILON-ZERO — the explicit low-height ζ zero-free strip.** Every zero `ρ` of `ζ` with
`|Im ρ| ≤ 1` satisfies `Re ρ ≤ 1 − 10⁻⁶`.

The explicit replacement for `zeta_zero_free_strip`'s compactness constant: same conclusion
shape, with the opaque `ε₀` pinned at the numeral `10⁻⁶`. See the module docstring for the
two-branch route (pole dominance below `|γ| = 1/5`, the 3-4-1 keep-one chain above it) and
for the non-circularity argument. -/
theorem zeta_zero_free_strip_explicit {ρ : ℂ} (hρ : riemannZeta ρ = 0) (him : |ρ.im| ≤ 1) :
    ρ.re ≤ 1 - 1 / 10 ^ 6 := by
  by_contra hcon
  rw [not_le] at hcon
  have hβ1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hρ
  have hβhalf : (1 : ℝ) / 2 < ρ.re := by norm_num at hcon ⊢; linarith
  have hγ0 : (0 : ℝ) ≤ |ρ.im| := abs_nonneg _
  rcases le_or_gt |ρ.im| (1 / 5) with hγ | hγ
  · -- ⟦BRANCH 1⟧ `|γ| ≤ 1/5`: the pole-dominance disk
    refine zeta_ne_zero_of_pole_dominant (by linarith) ?_ hρ
    have hd1 : ‖ρ - 1‖ ≤ 1 / 5 + 1 / 10 ^ 6 := by
      have h := Complex.norm_le_abs_re_add_abs_im (ρ - 1)
      rw [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero] at h
      rw [abs_of_nonpos (by linarith : ρ.re - 1 ≤ 0)] at h
      norm_num at hcon
      linarith
    have hd2 : ‖ρ‖ ≤ 6 / 5 := by
      have h := Complex.norm_le_abs_re_add_abs_im ρ
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ.re)] at h
      linarith
    have hd3 : 1 + 1 / ρ.re ≤ 3 := by
      have : 1 / ρ.re ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have hd0 : (0 : ℝ) ≤ ‖ρ - 1‖ := norm_nonneg _
    have hd4 : (0 : ℝ) ≤ ‖ρ‖ := norm_nonneg _
    have hd5 : (0 : ℝ) ≤ 1 + 1 / ρ.re := by positivity
    have hA : ‖ρ‖ * (1 + 1 / ρ.re) ≤ 6 / 5 * 3 := mul_le_mul hd2 hd3 hd5 (by norm_num)
    have hAnn : (0 : ℝ) ≤ ‖ρ‖ * (1 + 1 / ρ.re) := mul_nonneg hd4 hd5
    have hB : ‖ρ - 1‖ * (‖ρ‖ * (1 + 1 / ρ.re)) ≤ (1 / 5 + 1 / 10 ^ 6) * (6 / 5 * 3) :=
      mul_le_mul hd1 hA hAnn (by norm_num)
    calc ‖ρ - 1‖ * (‖ρ‖ * (1 + 1 / ρ.re)) ≤ (1 / 5 + 1 / 10 ^ 6) * (6 / 5 * 3) := hB
      _ < 1 := by norm_num
  · -- ⟦BRANCH 2⟧ `1/5 < |γ| ≤ 1`: the 3-4-1 keep-one chain
    set σ : ℝ := 1 + 1 / 15200 with hσdef
    have hσ1 : 1 < σ := by rw [hσdef]; norm_num
    have hσ2 : σ < 2 := by rw [hσdef]; norm_num
    have h341 := three_four_one_logDeriv (1 : DirichletCharacter ℂ 1) hσ1 ρ.im
    rw [show ((1 : DirichletCharacter ℂ 1) ^ 2) = 1 from one_pow 2] at h341
    set s1 : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hs1def
    set s2 : ℂ := (σ : ℂ) + 2 * (ρ.im : ℂ) * I with hs2def
    have hσ0C : (1 : ℝ) < ((σ : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact hσ1
    have hσ1C : (1 : ℝ) < s1.re := by rw [hs1def]; simpa using hσ1
    have hσ2C : (1 : ℝ) < s2.re := by rw [hs2def]; simpa using hσ1
    rw [neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ0C,
        neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ1C,
        neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ2C] at h341
    simp only [LFunction_modOne_eq] at h341
    -- A₀ : the sharp real-`σ` pole bound
    have hA0 : (-logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
      rw [logDeriv_apply, ← neg_div]; exact neg_logDeriv_zeta_le hσ1 hσ2.le
    -- A₁ : the retained-zero bound at `s₁`
    have hA1 : (-logDeriv riemannZeta s1).re
        ≤ (1 / (s1 - 1)).re + 1080 * Real.log (|ρ.im| + 2) - 1 / (σ - ρ.re) := by
      have h := zeta_neg_re_logDeriv_le_keep hρ hβhalf hβ1 hσ1 hσ2
      rw [← hs1def] at h; exact h
    -- A₂ : the drop-all bound at `s₂`
    have hA2 : (-logDeriv riemannZeta s2).re
        ≤ (1 / (s2 - 1)).re + 1080 * Real.log (|ρ.im| + 2) := by
      have h := zeta_neg_re_logDeriv_le hσ1 hσ2.le (γ := ρ.im)
      rw [← hs2def] at h; exact h
    -- the pole real parts at height `≥ 1/5` (the ONLY change from the `|γ| ≥ 1` branch)
    have hP1 : (1 / (s1 - 1)).re ≤ 5 := by
      have him1 : (s1 - 1).im = ρ.im := by
        rw [hs1def]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have hn : (1 : ℝ) / 5 ≤ ‖s1 - 1‖ := by
        have h := Complex.abs_im_le_norm (s1 - 1); rw [him1] at h; linarith
      calc (1 / (s1 - 1)).re ≤ ‖1 / (s1 - 1)‖ :=
            le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
        _ = 1 / ‖s1 - 1‖ := by rw [norm_div, norm_one]
        _ ≤ 5 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hP2 : (1 / (s2 - 1)).re ≤ 5 / 2 := by
      have him2 : (s2 - 1).im = 2 * ρ.im := by
        rw [hs2def]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have hn : (2 : ℝ) / 5 ≤ ‖s2 - 1‖ := by
        have h := Complex.abs_im_le_norm (s2 - 1); rw [him2] at h
        have h2 : |2 * ρ.im| = 2 * |ρ.im| := by rw [abs_mul]; norm_num
        rw [h2] at h; linarith
      calc (1 / (s2 - 1)).re ≤ ‖1 / (s2 - 1)‖ :=
            le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
        _ = 1 / ‖s2 - 1‖ := by rw [norm_div, norm_one]
        _ ≤ 5 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    -- the `O(1)` log at height `≤ 1`
    have hLup : Real.log (|ρ.im| + 2) ≤ 1.4 := by
      have h1 : Real.log (|ρ.im| + 2) ≤ Real.log 4 :=
        Real.log_le_log (by linarith) (by linarith)
      have h2 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      have h3 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      linarith
    have hpole : (1 : ℝ) / (σ - 1) = 15200 := by rw [hσdef]; norm_num
    rw [hpole] at hA0
    -- the Davenport chain, all constants numeric at height `≤ 1`
    have hkey : 4 * (1 / (σ - ρ.re)) ≤ 53186 := by
      linarith [h341, hA0, hA1, hA2, hP1, hP2, hLup]
    -- the numeric contradiction with `β > 1 − 10⁻⁶`
    have hpos : 0 < σ - ρ.re := by rw [hσdef]; linarith
    have hlt : σ - ρ.re ≤ 1 / 15200 + 1 / 10 ^ 6 := by
      rw [hσdef]; norm_num at hcon ⊢; linarith
    have hinv : (1 : ℝ) / (1 / 15200 + 1 / 10 ^ 6) ≤ 1 / (σ - ρ.re) :=
      one_div_le_one_div_of_le hpos hlt
    have hnum : (1 : ℝ) / (1 / 15200 + 1 / 10 ^ 6) = 19000000 / 1269 := by norm_num
    rw [hnum] at hinv
    linarith

/-! ## 3. The `_bounded` twin — the drop-in shape with the floor carried -/

/-- **The floored fixed strip.** `zeta_zero_free_strip` with its constant bounded below by the
explicit numeral `10⁻⁶` — the `_bounded` conjunct-carry twin (the EPSPIN genre) that lets a
consumer of the `∃`-shape keep an effective handle on `ε₀`. -/
theorem zeta_zero_free_strip_bounded :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ 1 / 10 ^ 6 ≤ ε₀ ∧
      ∀ {ρ : ℂ}, riemannZeta ρ = 0 → |ρ.im| ≤ 1 → ρ.re ≤ 1 - ε₀ :=
  ⟨1 / 10 ^ 6, by norm_num, le_refl _, fun hρ him => zeta_zero_free_strip_explicit hρ him⟩

/-! ## 4. The explicit ζ zero-free region — what the three riders spend -/

set_option maxHeartbeats 800000 in
-- Same budget and same reason as `zeta_zero_free_region`, whose `|γ| ≥ 1` branch this
-- reproduces verbatim: the 3-4-1 assembly in one declaration exceeds the default.
/-- **The quantitative ζ zero-free region with an EXPLICIT constant.** Every zero `ρ` of `ζ`
with `Re ρ ≥ 1/2` satisfies `Re ρ ≤ 1 − 10⁻⁷/log(|Im ρ| + 2)`.

The effective twin of `zeta_zero_free_region`, whose `c₃ = min(1/75712, ε₀·log 2)` carries the
opaque compactness constant. The numeral `10⁻⁷` clears both branch requirements:
`10⁻⁷ ≤ 1/75712` (the `|γ| ≥ 1` Davenport extraction, `dd/7 = 1/75712`) and
`10⁻⁷ ≤ 10⁻⁶·log 2` (the low-height strip, now `zeta_zero_free_strip_explicit`).
Body of the `|γ| ≥ 1` branch verbatim from `zeta_zero_free_region`. -/
theorem zeta_zero_free_region_explicit {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hre : 1 / 2 ≤ ρ.re) :
    ρ.re ≤ 1 - (1 / 10 ^ 7) / Real.log (|ρ.im| + 2) := by
  set Lv : ℝ := Real.log (|ρ.im| + 2) with hLdef
  have hLlog2 : Real.log 2 ≤ Lv := by
    rw [hLdef]; exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg ρ.im])
  have hLpos : 0 < Lv := lt_of_lt_of_le (Real.log_pos (by norm_num)) hLlog2
  have hβ1 : ρ.re < 1 := by
    by_contra h; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hρ
  rcases le_or_gt 1 |ρ.im| with hγ1 | hγ1
  · -- Case `|γ| ≥ 1`: the 3-4-1 keep-one region (verbatim)
    have hL1 : (1 : ℝ) ≤ Lv := by
      rw [hLdef]
      have hexp : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      have h3 : (1 : ℝ) ≤ Real.log 3 := by
        rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hexp
      exact le_trans h3 (Real.log_le_log (by norm_num) (by linarith [hγ1]))
    rcases le_or_gt ρ.re (1 / 2) with hβ | hβ
    · have hc₃Lv : (1 / 10 ^ 7 : ℝ) / Lv ≤ 1 / 2 := by
        rw [div_le_iff₀ hLpos]; nlinarith [hL1]
      linarith
    · set dd : ℝ := 1 / 10816 with hdddef
      have hddpos : (0 : ℝ) < dd := by norm_num
      have hddlt1 : dd < 1 := by rw [hdddef]; norm_num
      set σ : ℝ := 1 + dd / Lv with hσdef
      have hddL : dd / Lv ≤ dd := by rw [div_le_iff₀ hLpos]; nlinarith [hL1, hddpos]
      have hσ1 : 1 < σ := by
        rw [hσdef]; have : 0 < dd / Lv := div_pos hddpos hLpos; linarith
      have hσ2 : σ < 2 := by rw [hσdef]; linarith [hddL, hddlt1]
      have h341 := three_four_one_logDeriv (1 : DirichletCharacter ℂ 1) hσ1 ρ.im
      rw [show ((1 : DirichletCharacter ℂ 1) ^ 2) = 1 from one_pow 2] at h341
      set s1 : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hs1def
      set s2 : ℂ := (σ : ℂ) + 2 * (ρ.im : ℂ) * I with hs2def
      have hσ0C : (1 : ℝ) < ((σ : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact hσ1
      have hσ1C : (1 : ℝ) < s1.re := by rw [hs1def]; simpa using hσ1
      have hσ2C : (1 : ℝ) < s2.re := by rw [hs2def]; simpa using hσ1
      rw [neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ0C,
          neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ1C,
          neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ2C] at h341
      simp only [LFunction_modOne_eq] at h341
      have hA0 : (-logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
        rw [logDeriv_apply, ← neg_div]; exact neg_logDeriv_zeta_le hσ1 hσ2.le
      have hA1 : (-logDeriv riemannZeta s1).re
          ≤ (1 / (s1 - 1)).re + 1080 * Real.log (|ρ.im| + 2) - 1 / (σ - ρ.re) := by
        have h := zeta_neg_re_logDeriv_le_keep hρ hβ hβ1 hσ1 hσ2
        rw [← hs1def] at h; exact h
      have hA2 : (-logDeriv riemannZeta s2).re
          ≤ (1 / (s2 - 1)).re + 1080 * Real.log (|ρ.im| + 2) := by
        have h := zeta_neg_re_logDeriv_le hσ1 hσ2.le (γ := ρ.im)
        rw [← hs2def] at h; exact h
      have hP1 : (1 / (s1 - 1)).re ≤ 1 := by
        have him : (s1 - 1).im = ρ.im := by
          rw [hs1def]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        have hn : (1 : ℝ) ≤ ‖s1 - 1‖ := by
          have h := Complex.abs_im_le_norm (s1 - 1); rw [him] at h; linarith [hγ1]
        calc (1 / (s1 - 1)).re ≤ ‖1 / (s1 - 1)‖ :=
              le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
          _ = 1 / ‖s1 - 1‖ := by rw [norm_div, norm_one]
          _ ≤ 1 := by rw [div_le_one (by linarith : (0 : ℝ) < ‖s1 - 1‖)]; exact hn
      have hP2 : (1 / (s2 - 1)).re ≤ 1 := by
        have him : (s2 - 1).im = 2 * ρ.im := by
          rw [hs2def]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        have hn : (1 : ℝ) ≤ ‖s2 - 1‖ := by
          have h := Complex.abs_im_le_norm (s2 - 1); rw [him] at h
          have h2 : (2 : ℝ) * |ρ.im| = |2 * ρ.im| := by rw [abs_mul]; norm_num
          nlinarith [hγ1, h, h2, abs_nonneg (2 * ρ.im)]
        calc (1 / (s2 - 1)).re ≤ ‖1 / (s2 - 1)‖ :=
              le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
          _ = 1 / ‖s2 - 1‖ := by rw [norm_div, norm_one]
          _ ≤ 1 := by rw [div_le_one (by linarith : (0 : ℝ) < ‖s2 - 1‖)]; exact hn
      have e8 : (8 : ℝ) ≤ 8 * Lv := by nlinarith [hL1]
      have key : 4 * (1 / (σ - ρ.re)) ≤ 3 * (1 / (σ - 1)) + 5408 * Lv := by
        linarith [h341, hA0, hA1, hA2, hP1, hP2, e8, hLdef]
      have hchain' : 4 / (dd / Lv + (1 - ρ.re)) ≤ 3 / (dd / Lv) + 5408 * Lv := by
        rw [mul_one_div, mul_one_div] at key
        have e1 : σ - ρ.re = dd / Lv + (1 - ρ.re) := by rw [hσdef]; ring
        have e2 : σ - 1 = dd / Lv := by rw [hσdef]; ring
        rw [e1, e2] at key; exact key
      have hCdd : (5408 : ℝ) * dd = 1 / 2 := by rw [hdddef]; norm_num
      have hext := zero_free_extraction hLpos hddpos hCdd hβ1 hchain'
      have hfin : (1 / 10 ^ 7 : ℝ) / Lv ≤ dd / (7 * Lv) := by
        rw [show dd / (7 * Lv) = dd / 7 / Lv from (div_div dd 7 Lv).symm,
            div_le_div_iff_of_pos_right hLpos, hdddef]
        norm_num
      linarith [hext, hfin]
  · -- Case `|γ| < 1`: the EXPLICIT fixed zero-free strip
    have hst := zeta_zero_free_strip_explicit hρ (le_of_lt hγ1)
    have hc₃Lv : (1 / 10 ^ 7 : ℝ) / Lv ≤ 1 / 10 ^ 6 := by
      rw [div_le_iff₀ hLpos]
      have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      linarith [hLlog2, h2]
    linarith

/-- The `∃`-shaped `_bounded` twin of `zeta_zero_free_region`: the same conclusion with the
constant floored by the explicit numeral `10⁻⁷`. -/
theorem zeta_zero_free_region_bounded :
    ∃ c₃ : ℝ, 0 < c₃ ∧ 1 / 10 ^ 7 ≤ c₃ ∧ ∀ {ρ : ℂ}, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re →
      ρ.re ≤ 1 - c₃ / Real.log (|ρ.im| + 2) :=
  ⟨1 / 10 ^ 7, by norm_num, le_refl _, fun hρ hre => zeta_zero_free_region_explicit hρ hre⟩


/-! ## 5. ZETA-INV-SHALLOW — explicit `‖Zc‖` floors on the pole patch

CMU-HUNT leaf #2 (`Salt/SW/ZetaInvShallow.lean:53`, `Zc_patch_lower`): `‖Zc‖` attains a
positive minimum `δ` on the rectangle `R = {a ≤ Re ≤ 3, |Im| ≤ 2}` by
`IsCompact.exists_isMinOn`, and `δ` sits under a division in `zeta_inv_shallow`'s `C`.

`R` splits into three pieces. Two of them fall to compactness-free arguments and are
proved here with generous explicit floors:

* `Re z ≥ 2` — `‖Zc z‖ = ‖z−1‖·‖ζ z‖ ≥ 1·(1/4)` (`Zc_lower_of_two_le_re`);
* `‖z − 1‖ ≤ 1/5` — pole dominance again, now used as a *lower* bound rather than a
  non-vanishing statement: `‖Zc z‖ = ‖1 + (z−1)R(z)‖ ≥ 1 − ‖z−1‖·‖R(z)‖ ≥ 1 − (1/5)(18/5)`
  (`Zc_lower_near_pole`). This is the tool minted by `zeta_ne_zero_of_pole_dominant`,
  applied exactly as the ZETA-INV-SHALLOW strategy predicted.

The third piece is **the residual band** `{a ≤ Re z ≤ 2, |Im z| ≤ 2, ‖z − 1‖ ≥ 1/5}`, and it
does **not** fall: it demands an explicit lower bound for `|ζ|` on a box abutting `Re = 1` at
heights up to `2`, which is the classical low-height input. `zeta_lower_shallow` cannot serve
it (that theorem carries a standing `2 ≤ |t|`, inherited from `zeta_log_bound`, precisely
because the pole intrudes below it). See `docs/blueprints/flags.md` for the two priced routes
and the honest constant estimate.

So the deliverable here is the **hypothesis-taking** form (`_of_band`, the corpus's
`_of_strip`/`_of_contour` refactor genre): every piece of the patch except the band is
discharged with an explicit numeral, and the band is exposed as a single named input whose
own floor `δ₁` is carried through to the conclusion. -/

/-- **The near-pole `Zc` floor.** For `1/2 ≤ Re z` and `‖z − 1‖ ≤ 1/5`, `7/25 ≤ ‖Zc z‖`.

Pole dominance in lower-bound form: `Zc z = 1 + (z−1)·R(z)` (`Zc_eq_series`) with
`‖R‖ ≤ ‖z‖(1 + 1/Re z) ≤ (6/5)·3` (`norm_R_le`), so `‖Zc z‖ ≥ 1 − (1/5)(18/5) = 7/25`. -/
theorem Zc_lower_near_pole {z : ℂ} (hre : 1 / 2 ≤ z.re) (hz : ‖z - 1‖ ≤ 1 / 5) :
    (7 : ℝ) / 25 ≤ ‖Zc z‖ := by
  have hzre : 0 < z.re := by linarith
  have hser := Zc_eq_series z hzre
  have hRle : ‖∑' n : ℕ, dTerm z (n + 1)‖ ≤ ‖z‖ * (1 + 1 / z.re) := norm_R_le z hzre
  have hznorm : ‖z‖ ≤ 6 / 5 := by
    calc ‖z‖ = ‖(1 : ℂ) + (z - 1)‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖z - 1‖ := norm_add_le _ _
      _ ≤ 6 / 5 := by rw [norm_one]; linarith
  have hinv : 1 + 1 / z.re ≤ 3 := by
    have h : 1 / z.re ≤ 2 := by rw [div_le_iff₀ hzre]; linarith
    linarith
  have hinv0 : (0 : ℝ) ≤ 1 + 1 / z.re := by positivity
  have hR3 : ‖∑' n : ℕ, dTerm z (n + 1)‖ ≤ 18 / 5 := by
    have hA : ‖z‖ * (1 + 1 / z.re) ≤ 6 / 5 * 3 :=
      mul_le_mul hznorm hinv hinv0 (by norm_num)
    linarith
  have hRnn : (0 : ℝ) ≤ ‖∑' n : ℕ, dTerm z (n + 1)‖ := norm_nonneg _
  have h1 : (1 : ℝ) ≤ ‖Zc z‖ + ‖z - 1‖ * ‖∑' n : ℕ, dTerm z (n + 1)‖ := by
    have hstep : (1 : ℝ) ≤ ‖Zc z‖ + ‖(z - 1) * ∑' n : ℕ, dTerm z (n + 1)‖ := by
      calc (1 : ℝ) = ‖(1 : ℂ)‖ := norm_one.symm
        _ = ‖Zc z - (z - 1) * ∑' n : ℕ, dTerm z (n + 1)‖ := by rw [hser]; ring_nf
        _ ≤ ‖Zc z‖ + ‖(z - 1) * ∑' n : ℕ, dTerm z (n + 1)‖ := norm_sub_le _ _
    rwa [norm_mul] at hstep
  nlinarith [h1, hz, hR3, hRnn, norm_nonneg (z - 1)]

/-- **The right-half `Zc` floor.** For `2 ≤ Re z`, `1/4 ≤ ‖Zc z‖`: here `‖z−1‖ ≥ Re z − 1 ≥ 1`
and `‖ζ z‖ ≥ 1/4` (`zeta_norm_ge`). -/
theorem Zc_lower_of_two_le_re {z : ℂ} (hre : 2 ≤ z.re) : (1 : ℝ) / 4 ≤ ‖Zc z‖ := by
  have hne1 : z ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hre; norm_num at hre
  rw [Zc_eq_of_ne hne1, norm_mul]
  have h1 : (1 : ℝ) ≤ ‖z - 1‖ := by
    have h := Complex.abs_re_le_norm (z - 1)
    rw [Complex.sub_re, Complex.one_re, abs_of_nonneg (by linarith : (0 : ℝ) ≤ z.re - 1)] at h
    linarith
  have h2 : (1 : ℝ) / 4 ≤ ‖riemannZeta z‖ := zeta_norm_ge hre
  nlinarith [h1, h2, norm_nonneg (riemannZeta z)]

/-- **The pole patch floored, modulo the residual band.** Given any explicit floor `δ₁` on the
band `{a ≤ Re z ≤ 2, |Im z| ≤ 2, 1/5 ≤ ‖z−1‖}`, the whole `Zc_patch_lower` rectangle carries
the explicit floor `min δ₁ (1/4)` — no compactness, no extremal value.

The two off-band pieces are discharged outright (`Zc_lower_of_two_le_re`,
`Zc_lower_near_pole`); the band is the single named input. Note what is *absent* from the
hypotheses: the zero-free region. `Zc_patch_lower` needs `Hzfr` and `hcompat` only to know
`Zc ≠ 0` on `R`; a quantitative band floor subsumes that, so the `c₃`-narrowing wrinkle
never arises here. -/
theorem Zc_patch_lower_of_band {a δ₁ : ℝ} (ha : 1 / 2 ≤ a)
    (hband : ∀ z : ℂ, a ≤ z.re → z.re ≤ 2 → |z.im| ≤ 2 → 1 / 5 ≤ ‖z - 1‖ → δ₁ ≤ ‖Zc z‖) :
    ∀ z : ℂ, a ≤ z.re → z.re ≤ 3 → |z.im| ≤ 2 → min δ₁ (1 / 4) ≤ ‖Zc z‖ := by
  intro z hzlo hzhi hzim
  have hzre : 1 / 2 ≤ z.re := le_trans ha hzlo
  rcases le_or_gt 2 z.re with h2 | h2
  · exact le_trans (min_le_right _ _) (Zc_lower_of_two_le_re h2)
  · rcases le_or_gt ‖z - 1‖ (1 / 5) with hnear | hfar
    · have := Zc_lower_near_pole hzre hnear
      have hm : min δ₁ (1 / 4 : ℝ) ≤ 1 / 4 := min_le_right _ _
      linarith
    · exact le_trans (min_le_left _ _) (hband z hzlo h2.le hzim hfar.le)

/-- The `∃`-shaped `_bounded` twin at `Zc_patch_lower`'s own call shape: the patch minimum
exists *and* is floored by the explicit `min δ₁ (1/4)`. -/
theorem Zc_patch_lower_bounded_of_band {a δ₁ : ℝ} (ha : 1 / 2 ≤ a) (hδ₁ : 0 < δ₁)
    (hband : ∀ z : ℂ, a ≤ z.re → z.re ≤ 2 → |z.im| ≤ 2 → 1 / 5 ≤ ‖z - 1‖ → δ₁ ≤ ‖Zc z‖) :
    ∃ δ₀ > 0, min δ₁ (1 / 4) ≤ δ₀ ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ 3 → |z.im| ≤ 2 → δ₀ ≤ ‖Zc z‖ :=
  ⟨min δ₁ (1 / 4), lt_min hδ₁ (by norm_num), le_refl _, Zc_patch_lower_of_band ha hband⟩


/-! ## 6. EPSILON-SHARP — the un-collapsed keep-one constant, and `ε₀ = 2·10⁻⁵`

§2's `ε₀ = 10⁻⁶` was short of the CMU-HUNT §2 target `ε₀ ≥ 1.9·10⁻⁵` by a factor `≈ 19`, and
the gap was traced (`docs/blueprints/flags.md`, EPSILON-ZERO) to **one pre-collapsed constant**:
`zeta_neg_re_logDeriv_le_keep` and `zeta_neg_re_logDeriv_le` both carry
`1080·log(|γ|+2)`, which is `120·log(4·M₀ζ)` after the *uniform* collapse
`log(4·M₀ζ(t₀)) ≤ 9·log(|t₀|+2)` (`log_4M0zeta_le_self`). At height `≤ 1` that collapse costs
a factor `≈ 1.57`: the honest `120·log(4·M₀ζ(γ)) ≈ 757` against the collapsed
`1080·log 3 ≈ 1186`. This section keeps the constant un-collapsed, and then sharpens `M₀ζ`
itself at low height, in three additive steps:

1. **`Zc_sphere_bound_sharp`** — the sphere bound re-derived with the triangle inequality taken
   at the *centre* `c = 2 + t₀i` rather than at the origin: `‖z‖ ≤ ‖c‖ + R` and
   `‖z−1‖ ≤ ‖c−1‖ + R` with the *exact* `‖c‖ = √(4+t₀²)`, `‖c−1‖ = √(1+t₀²)`, instead of
   `M0zeta`'s `‖z‖ ≤ 15/4+|t₀|`, `‖z−1‖ ≤ ‖z‖+1`. At `|t₀| ≤ 1` this gives `‖Zc‖ ≤ 66`
   against `M₀ζ(1) = 137.6`; at `|t₀| ≤ 2`, `96` against `195.1`.
2. **`zeta_neg_re_logDeriv_le_keep_of_growth` / `zeta_neg_re_logDeriv_le_of_growth`** — the
   keep-one and drop-all ζ log-derivative bounds in the corpus's hypothesis-taking genre: the
   growth majorant `M` on the sphere `‖z − (2+t₀i)‖ ≤ 7/4` is an *input*, and the conclusion
   carries `120·log(4M)` with no collapse. Instantiating `M := M0zeta t₀` recovers the landed
   lemmas verbatim; instantiating `M := 66`, `M := 96` gives the numerals used here.
3. **`zeta_zero_free_strip_sharp`** — the same two-branch route as
   `zeta_zero_free_strip_explicit` (pole dominance below `|γ| = 1/5`, 3-4-1 above it) with
   `4·120·log 264 + 120·log 384 ≤ 3395.3` in place of `5·1080·log 4 = 7560`, and the near-optimal
   `σ = 1 + 1/7700` in place of `1 + 1/15200`. The chain reads `4/(σ−β) ≤ 26521`, incompatible
   with `β > 1 − 2·10⁻⁵`.

**What the sharpening buys, exactly.** `zeta_zero_free_region`'s constant is
`c₃ = min(1/75712, ε₀·log 2)`, and `(1/75712)/log 2 = 1.9055·10⁻⁵` — *that* is where
CMU-HUNT's target `1.9·10⁻⁵` comes from. At `ε₀ = 2·10⁻⁵` the `min` is attained by its **first**
argument, so `zeta_zero_free_region_sharp` carries `c₃ = 1/75712` — the literal the compactness
version already had. The leaf does not merely become effective (§4's `c₃ = 10⁻⁷` did that); it
vanishes into the existing literal, which was the whole point of the hunt. -/

/-- **The sharp `Zc` sphere bound.** On the disk `‖z − (2+t₀i)‖ ≤ 7/4` (where `Re z ≥ 1/4`),
`‖Zc z‖ ≤ 1 + 5(7/4+a)(7/4+b)` for any `a ≥ ‖c−1‖ = √(1+t₀²)` and `b ≥ ‖c‖ = √(4+t₀²)`.

Same route as `Zc_sphere_bound` (`Zc_growth` plus `1 + 1/Re z ≤ 5`), but the two norm factors
are estimated from the **centre** outwards, which is where `M0zeta`'s slack lives: `M0zeta`
bounds `‖z‖ ≤ 2+|t₀|+7/4` and then `‖z−1‖ ≤ ‖z‖+1`, paying `|t₀|` where `√(4+t₀²)` is honest
and paying a full `+1` where `‖c−1‖ = √(1+t₀²)` is honest. -/
theorem Zc_sphere_bound_sharp {t₀ a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha2 : 1 + t₀ ^ 2 ≤ a ^ 2) (hb2 : 4 + t₀ ^ 2 ≤ b ^ 2) {z : ℂ}
    (hz : ‖z - (2 + (t₀ : ℂ) * I)‖ ≤ 7 / 4) :
    ‖Zc z‖ ≤ 1 + 5 * (7 / 4 + a) * (7 / 4 + b) := by
  set c : ℂ := 2 + (t₀ : ℂ) * I with hc
  have hcre : c.re = 2 := by rw [hc]; simp
  have hcim : c.im = t₀ := by rw [hc]; simp
  have hzc_re : (1 : ℝ) / 4 ≤ z.re := by
    have h := Complex.abs_re_le_norm (z - c)
    rw [Complex.sub_re, hcre] at h
    have h2 := abs_le.mp h
    linarith [h2.1, hz]
  have hre_pos : 0 < z.re := by linarith
  have hcn : ‖c‖ ≤ b := by
    have h2 : ‖c‖ ^ 2 = 4 + t₀ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hcre, hcim]; ring
    nlinarith [norm_nonneg c, h2, hb2, hb]
  have hc1n : ‖c - 1‖ ≤ a := by
    have hre1 : (c - 1).re = 1 := by rw [Complex.sub_re, hcre, Complex.one_re]; norm_num
    have him1 : (c - 1).im = t₀ := by rw [Complex.sub_im, hcim, Complex.one_im]; ring
    have h2 : ‖c - 1‖ ^ 2 = 1 + t₀ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre1, him1]; ring
    nlinarith [norm_nonneg (c - 1), h2, ha2, ha]
  have hznorm : ‖z‖ ≤ 7 / 4 + b := by
    calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
      _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ 7 / 4 + b := by linarith
  have hz1norm : ‖z - 1‖ ≤ 7 / 4 + a := by
    calc ‖z - 1‖ = ‖(c - 1) + (z - c)‖ := by ring_nf
      _ ≤ ‖c - 1‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ 7 / 4 + a := by linarith
  have h1re : (0 : ℝ) ≤ 1 / z.re := div_nonneg zero_le_one hre_pos.le
  have hinv : 1 + 1 / z.re ≤ 5 := by
    have h4 : 1 / z.re ≤ 4 := by rw [div_le_iff₀ hre_pos]; linarith
    linarith
  have hA : ‖z‖ * (1 + 1 / z.re) ≤ (7 / 4 + b) * 5 :=
    mul_le_mul hznorm hinv (by linarith) (by linarith)
  have hAnn : (0 : ℝ) ≤ ‖z‖ * (1 + 1 / z.re) := mul_nonneg (norm_nonneg _) (by linarith)
  have hB : ‖z - 1‖ * (‖z‖ * (1 + 1 / z.re)) ≤ (7 / 4 + a) * ((7 / 4 + b) * 5) :=
    mul_le_mul hz1norm hA hAnn (by linarith)
  calc ‖Zc z‖ ≤ 1 + ‖z - 1‖ * (‖z‖ * (1 + 1 / z.re)) := Zc_growth hre_pos
    _ ≤ 1 + (7 / 4 + a) * ((7 / 4 + b) * 5) := by linarith
    _ = 1 + 5 * (7 / 4 + a) * (7 / 4 + b) := by ring

/-- `‖Zc‖ ≤ 66` on the growth disk at any height `|t₀| ≤ 1` (`a = 3/2 ≥ √2`, `b = 9/4 ≥ √5`).
Against `M₀ζ(1) = 137.5625`: the log gain is `log(550.25/264) = 0.734`, i.e. `88` off the
`120·log(4M)` constant. -/
theorem Zc_sphere_bound_height_one {t₀ : ℝ} (ht : |t₀| ≤ 1) {z : ℂ}
    (hz : ‖z - (2 + (t₀ : ℂ) * I)‖ ≤ 7 / 4) : ‖Zc z‖ ≤ 66 := by
  have hsq : t₀ ^ 2 ≤ 1 := by
    have := sq_abs t₀; nlinarith [abs_nonneg t₀]
  have h := Zc_sphere_bound_sharp (a := 3 / 2) (b := 9 / 4) (by norm_num) (by norm_num)
    (by nlinarith) (by nlinarith) hz
  norm_num at h
  linarith

/-- `‖Zc‖ ≤ 96` on the growth disk at any height `|t₀| ≤ 2` (`a = 9/4 ≥ √5`, `b = 3 ≥ √8`) —
the `s₂ = σ + 2iγ` slot of the 3-4-1 at `|γ| ≤ 1`. Against `M₀ζ(2) = 195.0625`. -/
theorem Zc_sphere_bound_height_two {t₀ : ℝ} (ht : |t₀| ≤ 2) {z : ℂ}
    (hz : ‖z - (2 + (t₀ : ℂ) * I)‖ ≤ 7 / 4) : ‖Zc z‖ ≤ 96 := by
  have hsq : t₀ ^ 2 ≤ 4 := by
    have := sq_abs t₀; nlinarith [abs_nonneg t₀]
  have h := Zc_sphere_bound_sharp (a := 9 / 4) (b := 3) (by norm_num) (by norm_num)
    (by nlinarith) (by nlinarith) hz
  norm_num at h
  linarith

/-- **The keep-one ζ bound, un-collapsed.** `zeta_neg_re_logDeriv_le_keep` with the growth
majorant as an input and the conclusion carrying `120·log(4M)` instead of `1080·log(|γ|+2)`:
for a zero `ρ` with `1/2 < Re ρ < 1`, `1 < σ < 2`, and any `M ≥ 1` bounding `‖Zc‖` on the disk
`‖z − (2 + i·Im ρ)‖ ≤ 7/4`,
`Re(−ζ'/ζ(σ+i·Im ρ)) ≤ Re(1/(s−1)) + 120·log(4M) − 1/(σ − Re ρ)`.

Proof identical to `zeta_neg_re_logDeriv_le_keep`; only the final collapse step is dropped.
`M := M0zeta (Im ρ)` recovers the landed statement (via `Zc_sphere_bound`, `one_le_M0zeta` and
`log_4M0zeta_le_self`). -/
theorem zeta_neg_re_logDeriv_le_keep_of_growth {ρ : ℂ} (hρ0 : riemannZeta ρ = 0)
    (hβlt : 1 / 2 < ρ.re) (hβ1 : ρ.re < 1) {σ M : ℝ} (h1 : 1 < σ) (h2 : σ < 2) (hM : 1 ≤ M)
    (hgrow : ∀ z : ℂ, ‖z - (2 + (ρ.im : ℂ) * I)‖ ≤ 7 / 4 → ‖Zc z‖ ≤ M) :
    (-logDeriv riemannZeta ((σ : ℂ) + (ρ.im : ℂ) * I)).re
      ≤ (1 / (((σ : ℂ) + (ρ.im : ℂ) * I) - 1)).re + 120 * Real.log (4 * M)
        - 1 / (σ - ρ.re) := by
  set γ : ℝ := ρ.im with hγ
  set s : ℂ := (σ : ℂ) + (γ : ℂ) * I with hs
  set c : ℂ := 2 + (γ : ℂ) * I with hc
  have hsre : s.re = σ := by rw [hs]; simp [Complex.add_re, Complex.mul_re]
  have hσC : (1 : ℝ) < s.re := by rw [hsre]; exact h1
  have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hσC; norm_num at hσC
  have hζs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hσC)
  have hsplit := neg_logDeriv_zeta_split hs_ne1 hζs
  have hsphere74 : ∀ z ∈ sphere c (7 / 4), ‖Zc z‖ ≤ M := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz; exact hgrow z (le_of_eq hz)
  have hsphere32 : ∀ z ∈ sphere c (3 / 2), ‖Zc z‖ ≤ M := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz; exact hgrow z (by rw [hz]; norm_num)
  obtain ⟨Z, m, h, hmemb, -, hne_h, hEqOn, -, hnum⟩ :=
    entire_norm_logDeriv_sub_sum' Zc_differentiable hM (Zc_center_lower γ) hsphere74 hsphere32
  have hscnorm : ‖s - c‖ ≤ 23 / 20 := by
    have hsub : s - c = ((σ - 2 : ℝ) : ℂ) := by rw [hs, hc]; push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    linarith
  have hZcs : Zc s ≠ 0 := by
    rw [Zc_eq_of_ne hs_ne1]; exact mul_ne_zero (sub_ne_zero.mpr hs_ne1) hζs
  have hre := neg_re_logDeriv_le (hnum s hscnorm hZcs)
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hβ1; norm_num at hβ1
  have hZcρ : Zc ρ = 0 := by rw [Zc_eq_of_ne hρ1, hρ0, mul_zero]
  have hρball : ρ ∈ ball c (3 / 2) := by
    rw [mem_ball, dist_eq_norm]
    have hsub : ρ - c = ((ρ.re - 2 : ℝ) : ℂ) := by
      rw [hc, hγ]; apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : ρ.re - 2 ≤ 0)]
    linarith
  obtain ⟨hρZ, hmρ⟩ := mem_zeros_of_factorization_gen hne_h hEqOn hρball hZcρ
  have hpos : ∀ ρ' ∈ Z, 0 < (s - ρ').re := by
    intro ρ' hρ'
    have hρ'0 : Zc ρ' = 0 := (hmemb ρ' hρ').2
    have hρ'1 : ρ' ≠ 1 := fun h => by rw [h, Zc_one] at hρ'0; exact one_ne_zero hρ'0
    have hζρ' : riemannZeta ρ' = 0 := by
      rw [Zc_eq_of_ne hρ'1] at hρ'0
      exact (mul_eq_zero.mp hρ'0).resolve_left (sub_ne_zero.mpr hρ'1)
    have hlt : ρ'.re < 1 := by
      by_contra hcn; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcn) hζρ'
    rw [Complex.sub_re]; linarith [hσC]
  have hsρ : s - ρ = ((σ - ρ.re : ℝ) : ℂ) := by
    rw [hs, hγ]; apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
  have hσρpos : 0 < σ - ρ.re := by linarith
  have hterm_re : (1 / (s - ρ)).re = 1 / (σ - ρ.re) := by
    rw [hsρ, show (1 : ℂ) / ((σ - ρ.re : ℝ) : ℂ) = (((1 / (σ - ρ.re)) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have hsingle : (m ρ : ℝ) * (1 / (s - ρ)).re ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re :=
    Finset.single_le_sum (term_re_nonneg m hpos) hρZ
  have hlow : 1 / (σ - ρ.re) ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re := by
    have hm1 : (1 : ℝ) ≤ (m ρ : ℝ) := by exact_mod_cast hmρ
    have hnn : (0 : ℝ) ≤ 1 / (σ - ρ.re) := by positivity
    have h3 : 1 / (σ - ρ.re) ≤ (m ρ : ℝ) * (1 / (s - ρ)).re := by rw [hterm_re]; nlinarith
    linarith [h3, hsingle]
  rw [hsplit]
  linarith [hre, hlow]

/-- **The drop-all ζ bound at `σ + 2iγ`, un-collapsed.** `zeta_neg_re_logDeriv_le` with the
growth majorant as an input: `Re(−ζ'/ζ(σ+2iγ)) ≤ Re(1/(s−1)) + 120·log(4M)` for any `M ≥ 1`
bounding `‖Zc‖` on `‖z − (2 + 2iγ)‖ ≤ 7/4`. All partial-fraction zero terms dropped, exactly as
in the landed lemma; only the collapse `120·log(4M₀ζ(2γ)) ≤ 1080·log(|γ|+2)` is omitted. -/
theorem zeta_neg_re_logDeriv_le_of_growth {σ γ M : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) (hM : 1 ≤ M)
    (hgrow : ∀ z : ℂ, ‖z - (2 + ((2 * γ : ℝ) : ℂ) * I)‖ ≤ 7 / 4 → ‖Zc z‖ ≤ M) :
    (-logDeriv riemannZeta ((σ : ℂ) + 2 * (γ : ℂ) * I)).re
      ≤ (1 / (((σ : ℂ) + 2 * (γ : ℂ) * I) - 1)).re + 120 * Real.log (4 * M) := by
  set t₀ : ℝ := 2 * γ with ht₀
  set s : ℂ := (σ : ℂ) + 2 * (γ : ℂ) * I with hs
  set c : ℂ := 2 + (t₀ : ℂ) * I with hc
  have hsceq : s = (σ : ℂ) + (t₀ : ℂ) * I := by rw [hs, ht₀]; push_cast; ring
  have hsre : s.re = σ := by rw [hsceq]; simp [Complex.add_re, Complex.mul_re]
  have hσC : (1 : ℝ) < s.re := by rw [hsre]; exact h1
  have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hσC; norm_num at hσC
  have hζs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hσC)
  have hsplit := neg_logDeriv_zeta_split hs_ne1 hζs
  have hsphere74 : ∀ z ∈ sphere c (7 / 4), ‖Zc z‖ ≤ M := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz; exact hgrow z (le_of_eq hz)
  have hsphere32 : ∀ z ∈ sphere c (3 / 2), ‖Zc z‖ ≤ M := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz; exact hgrow z (by rw [hz]; norm_num)
  obtain ⟨Z, m, h, hmemb, -, -, -, -, hnum⟩ :=
    entire_norm_logDeriv_sub_sum' Zc_differentiable hM (Zc_center_lower t₀) hsphere74 hsphere32
  have hscnorm : ‖s - c‖ ≤ 23 / 20 := by
    have hsub : s - c = ((σ - 2 : ℝ) : ℂ) := by rw [hsceq, hc]; push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    linarith
  have hZcs : Zc s ≠ 0 := by
    rw [Zc_eq_of_ne hs_ne1]
    exact mul_ne_zero (sub_ne_zero.mpr hs_ne1) hζs
  have hbound := hnum s hscnorm hZcs
  have hdrop : 0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (s - ρ)).re := by
    refine Finset.sum_nonneg (fun ρ hρ => ?_)
    have hρ0 : Zc ρ = 0 := (hmemb ρ hρ).2
    have hρ1 : ρ ≠ 1 := fun h => by rw [h, Zc_one] at hρ0; exact one_ne_zero hρ0
    have hζρ : riemannZeta ρ = 0 := by
      rw [Zc_eq_of_ne hρ1] at hρ0
      exact (mul_eq_zero.mp hρ0).resolve_left (sub_ne_zero.mpr hρ1)
    have hρre : ρ.re < 1 := by
      by_contra hcn; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcn) hζρ
    refine mul_nonneg (by positivity) ?_
    rw [one_div, Complex.inv_re]
    refine div_nonneg ?_ (Complex.normSq_nonneg _)
    rw [Complex.sub_re]; linarith [hσC, hρre]
  have hZcnum : (-logDeriv Zc s).re ≤ 120 * Real.log (4 * M) := by
    have h := neg_re_logDeriv_le hbound
    linarith [h, hdrop]
  rw [hsplit]
  linarith [hZcnum]

/-- `log 264 ≤ 5.5765` — via `264 = 256·(33/32)`, `log 256 = 8 log 2` and
`log(1+x) ≤ x` (`Real.log_le_sub_one_of_pos`). The `s₁` slot's constant is `120·log 264`. -/
theorem log_264_le : Real.log 264 ≤ 5.5765 := by
  have h1 : Real.log 264 = Real.log 256 + Real.log (33 / 32) := by
    rw [show (264 : ℝ) = 256 * (33 / 32) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have h2 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have h3 : Real.log (33 / 32) ≤ 33 / 32 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h4 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [h1, h2]; linarith

/-- `log 384 ≤ 5.9884` — via `384 = 512·(3/4)`, `log 512 = 9 log 2` and `log(3/4) ≤ −1/4`.
The `s₂` slot's constant is `120·log 384`. -/
theorem log_384_le : Real.log 384 ≤ 5.9884 := by
  have h1 : Real.log 384 = Real.log 512 + Real.log (3 / 4) := by
    rw [show (384 : ℝ) = 512 * (3 / 4) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have h2 : Real.log 512 = 9 * Real.log 2 := by
    rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have h3 : Real.log (3 / 4) ≤ 3 / 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h4 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [h1, h2]; linarith

set_option maxHeartbeats 1200000 in
-- Same reason as `zeta_zero_free_strip_explicit`: the 3-4-1 assembly in one declaration.
/-- **EPSILON-SHARP — the sharpened explicit ζ zero-free strip.** Every zero `ρ` of `ζ` with
`|Im ρ| ≤ 1` satisfies `Re ρ ≤ 1 − 2·10⁻⁵`, twenty times `zeta_zero_free_strip_explicit`'s
`10⁻⁶` and past CMU-HUNT §2's `1.9·10⁻⁵` target.

Route as in §2, with three changes, all in branch 2: the keep-one and drop-all constants are
taken un-collapsed off the sharp sphere bounds (`120·log 264 ≤ 669.2` at `s₁`,
`120·log 384 ≤ 718.6` at `s₂`, against `1080·log 4 = 1512` each); the chain therefore reads
`4/(σ−β) ≤ 3·7700 + 3 + 4·5 + 5/2 + 4·669.2 + 718.6 ≤ 26521`; and `σ = 1 + 1/7700` is the
near-optimal offset for that constant (the maximum of `d(1−Cd)/(3+Cd)` sits at `C·d ≈ 0.464`).
Branch 1 (pole dominance, `|γ| ≤ 1/5`) is unchanged apart from the numeral: the disk product is
`(1/5 + 2·10⁻⁵)(6/5)(3) = 0.72007 < 1`. -/
theorem zeta_zero_free_strip_sharp {ρ : ℂ} (hρ : riemannZeta ρ = 0) (him : |ρ.im| ≤ 1) :
    ρ.re ≤ 1 - 1 / 50000 := by
  by_contra hcon
  rw [not_le] at hcon
  have hβ1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hρ
  have hβhalf : (1 : ℝ) / 2 < ρ.re := by norm_num at hcon ⊢; linarith
  have hγ0 : (0 : ℝ) ≤ |ρ.im| := abs_nonneg _
  rcases le_or_gt |ρ.im| (1 / 5) with hγ | hγ
  · -- ⟦BRANCH 1⟧ `|γ| ≤ 1/5`: the pole-dominance disk
    refine zeta_ne_zero_of_pole_dominant (by linarith) ?_ hρ
    have hd1 : ‖ρ - 1‖ ≤ 1 / 5 + 1 / 50000 := by
      have h := Complex.norm_le_abs_re_add_abs_im (ρ - 1)
      rw [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero] at h
      rw [abs_of_nonpos (by linarith : ρ.re - 1 ≤ 0)] at h
      norm_num at hcon
      linarith
    have hd2 : ‖ρ‖ ≤ 6 / 5 := by
      have h := Complex.norm_le_abs_re_add_abs_im ρ
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ.re)] at h
      linarith
    have hd3 : 1 + 1 / ρ.re ≤ 3 := by
      have : 1 / ρ.re ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have hd0 : (0 : ℝ) ≤ ‖ρ - 1‖ := norm_nonneg _
    have hd4 : (0 : ℝ) ≤ ‖ρ‖ := norm_nonneg _
    have hd5 : (0 : ℝ) ≤ 1 + 1 / ρ.re := by positivity
    have hA : ‖ρ‖ * (1 + 1 / ρ.re) ≤ 6 / 5 * 3 := mul_le_mul hd2 hd3 hd5 (by norm_num)
    have hAnn : (0 : ℝ) ≤ ‖ρ‖ * (1 + 1 / ρ.re) := mul_nonneg hd4 hd5
    have hB : ‖ρ - 1‖ * (‖ρ‖ * (1 + 1 / ρ.re)) ≤ (1 / 5 + 1 / 50000) * (6 / 5 * 3) :=
      mul_le_mul hd1 hA hAnn (by norm_num)
    calc ‖ρ - 1‖ * (‖ρ‖ * (1 + 1 / ρ.re)) ≤ (1 / 5 + 1 / 50000) * (6 / 5 * 3) := hB
      _ < 1 := by norm_num
  · -- ⟦BRANCH 2⟧ `1/5 < |γ| ≤ 1`: the 3-4-1 keep-one chain at the sharp constants
    have him2 : |2 * ρ.im| ≤ 2 := by
      rw [abs_mul]; norm_num; linarith [him]
    set σ : ℝ := 1 + 1 / 7700 with hσdef
    have hσ1 : 1 < σ := by rw [hσdef]; norm_num
    have hσ2 : σ < 2 := by rw [hσdef]; norm_num
    have h341 := three_four_one_logDeriv (1 : DirichletCharacter ℂ 1) hσ1 ρ.im
    rw [show ((1 : DirichletCharacter ℂ 1) ^ 2) = 1 from one_pow 2] at h341
    set s1 : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hs1def
    set s2 : ℂ := (σ : ℂ) + 2 * (ρ.im : ℂ) * I with hs2def
    have hσ0C : (1 : ℝ) < ((σ : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact hσ1
    have hσ1C : (1 : ℝ) < s1.re := by rw [hs1def]; simpa using hσ1
    have hσ2C : (1 : ℝ) < s2.re := by rw [hs2def]; simpa using hσ1
    rw [neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ0C,
        neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ1C,
        neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ2C] at h341
    simp only [LFunction_modOne_eq] at h341
    -- A₀ : the sharp real-`σ` pole bound
    have hA0 : (-logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
      rw [logDeriv_apply, ← neg_div]; exact neg_logDeriv_zeta_le hσ1 hσ2.le
    -- A₁ : the retained-zero bound at `s₁`, constant `120·log(4·66)`
    have hA1 : (-logDeriv riemannZeta s1).re
        ≤ (1 / (s1 - 1)).re + 120 * Real.log 264 - 1 / (σ - ρ.re) := by
      have h := zeta_neg_re_logDeriv_le_keep_of_growth hρ hβhalf hβ1 hσ1 hσ2 (M := 66)
        (by norm_num) (fun z hz => Zc_sphere_bound_height_one him hz)
      rw [show (4 : ℝ) * 66 = 264 by norm_num] at h
      rw [← hs1def] at h; exact h
    -- A₂ : the drop-all bound at `s₂`, constant `120·log(4·96)`
    have hA2 : (-logDeriv riemannZeta s2).re
        ≤ (1 / (s2 - 1)).re + 120 * Real.log 384 := by
      have h := zeta_neg_re_logDeriv_le_of_growth hσ1 hσ2.le (M := 96) (γ := ρ.im)
        (by norm_num) (fun z hz => Zc_sphere_bound_height_two him2 hz)
      rw [show (4 : ℝ) * 96 = 384 by norm_num] at h
      rw [← hs2def] at h; exact h
    -- the pole real parts at height `≥ 1/5`
    have hP1 : (1 / (s1 - 1)).re ≤ 5 := by
      have him1 : (s1 - 1).im = ρ.im := by
        rw [hs1def]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have hn : (1 : ℝ) / 5 ≤ ‖s1 - 1‖ := by
        have h := Complex.abs_im_le_norm (s1 - 1); rw [him1] at h; linarith
      calc (1 / (s1 - 1)).re ≤ ‖1 / (s1 - 1)‖ :=
            le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
        _ = 1 / ‖s1 - 1‖ := by rw [norm_div, norm_one]
        _ ≤ 5 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hP2 : (1 / (s2 - 1)).re ≤ 5 / 2 := by
      have himm : (s2 - 1).im = 2 * ρ.im := by
        rw [hs2def]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have hn : (2 : ℝ) / 5 ≤ ‖s2 - 1‖ := by
        have h := Complex.abs_im_le_norm (s2 - 1); rw [himm] at h
        have h2 : |2 * ρ.im| = 2 * |ρ.im| := by rw [abs_mul]; norm_num
        rw [h2] at h; linarith
      calc (1 / (s2 - 1)).re ≤ ‖1 / (s2 - 1)‖ :=
            le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
        _ = 1 / ‖s2 - 1‖ := by rw [norm_div, norm_one]
        _ ≤ 5 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hpole : (1 : ℝ) / (σ - 1) = 7700 := by rw [hσdef]; norm_num
    rw [hpole] at hA0
    -- the Davenport chain at the sharp constants
    have hkey : 4 * (1 / (σ - ρ.re)) ≤ 26521 := by
      linarith [h341, hA0, hA1, hA2, hP1, hP2, log_264_le, log_384_le]
    -- the numeric contradiction with `β > 1 − 2·10⁻⁵`
    have hpos : 0 < σ - ρ.re := by rw [hσdef]; linarith
    have hlt : σ - ρ.re ≤ 1 / 7700 + 1 / 50000 := by
      rw [hσdef]; norm_num at hcon ⊢; linarith
    have hinv : (1 : ℝ) / (1 / 7700 + 1 / 50000) ≤ 1 / (σ - ρ.re) :=
      one_div_le_one_div_of_le hpos hlt
    have hnum : (1 : ℝ) / (1 / 7700 + 1 / 50000) = 3850000 / 577 := by norm_num
    rw [hnum] at hinv
    linarith

/-- The `∃`-shaped `_bounded` twin of the sharpened strip: `zeta_zero_free_strip` with its
constant floored by `2·10⁻⁵`. -/
theorem zeta_zero_free_strip_sharp_bounded :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ 1 / 50000 ≤ ε₀ ∧
      ∀ {ρ : ℂ}, riemannZeta ρ = 0 → |ρ.im| ≤ 1 → ρ.re ≤ 1 - ε₀ :=
  ⟨1 / 50000, by norm_num, le_refl _, fun hρ him => zeta_zero_free_strip_sharp hρ him⟩

set_option maxHeartbeats 800000 in
-- Same budget and reason as `zeta_zero_free_region_explicit`.
/-- **The explicit ζ zero-free region at the ORIGINAL literal.** Every zero `ρ` of `ζ` with
`Re ρ ≥ 1/2` satisfies `Re ρ ≤ 1 − (1/75712)/log(|Im ρ| + 2)`.

`zeta_zero_free_region`'s constant is `c₃ = min(1/75712, ε₀·log 2)` with `ε₀` opaque. §4 made it
effective at the cost of the numeral (`c₃ = 10⁻⁷`); here the numeral is **recovered**: at
`ε₀ = 2·10⁻⁵` the second argument is `1.386·10⁻⁵ > 1.3208·10⁻⁵ = 1/75712`, so the `min` is its
first argument and the compactness leaf leaves no trace at all in the constant. The `|γ| ≥ 1`
branch is the Davenport extraction verbatim (`dd/7 = 1/75712` exactly); the `|γ| < 1` branch is
`zeta_zero_free_strip_sharp`. -/
theorem zeta_zero_free_region_sharp {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hre : 1 / 2 ≤ ρ.re) :
    ρ.re ≤ 1 - (1 / 75712) / Real.log (|ρ.im| + 2) := by
  set Lv : ℝ := Real.log (|ρ.im| + 2) with hLdef
  have hLlog2 : Real.log 2 ≤ Lv := by
    rw [hLdef]; exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg ρ.im])
  have hLpos : 0 < Lv := lt_of_lt_of_le (Real.log_pos (by norm_num)) hLlog2
  have hβ1 : ρ.re < 1 := by
    by_contra h; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hρ
  rcases le_or_gt 1 |ρ.im| with hγ1 | hγ1
  · -- Case `|γ| ≥ 1`: the 3-4-1 keep-one region (verbatim)
    have hL1 : (1 : ℝ) ≤ Lv := by
      rw [hLdef]
      have hexp : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      have h3 : (1 : ℝ) ≤ Real.log 3 := by
        rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hexp
      exact le_trans h3 (Real.log_le_log (by norm_num) (by linarith [hγ1]))
    rcases le_or_gt ρ.re (1 / 2) with hβ | hβ
    · have hc₃Lv : (1 / 75712 : ℝ) / Lv ≤ 1 / 2 := by
        rw [div_le_iff₀ hLpos]; nlinarith [hL1]
      linarith
    · set dd : ℝ := 1 / 10816 with hdddef
      have hddpos : (0 : ℝ) < dd := by norm_num
      have hddlt1 : dd < 1 := by rw [hdddef]; norm_num
      set σ : ℝ := 1 + dd / Lv with hσdef
      have hddL : dd / Lv ≤ dd := by rw [div_le_iff₀ hLpos]; nlinarith [hL1, hddpos]
      have hσ1 : 1 < σ := by
        rw [hσdef]; have : 0 < dd / Lv := div_pos hddpos hLpos; linarith
      have hσ2 : σ < 2 := by rw [hσdef]; linarith [hddL, hddlt1]
      have h341 := three_four_one_logDeriv (1 : DirichletCharacter ℂ 1) hσ1 ρ.im
      rw [show ((1 : DirichletCharacter ℂ 1) ^ 2) = 1 from one_pow 2] at h341
      set s1 : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hs1def
      set s2 : ℂ := (σ : ℂ) + 2 * (ρ.im : ℂ) * I with hs2def
      have hσ0C : (1 : ℝ) < ((σ : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact hσ1
      have hσ1C : (1 : ℝ) < s1.re := by rw [hs1def]; simpa using hσ1
      have hσ2C : (1 : ℝ) < s2.re := by rw [hs2def]; simpa using hσ1
      rw [neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ0C,
          neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ1C,
          neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ2C] at h341
      simp only [LFunction_modOne_eq] at h341
      have hA0 : (-logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
        rw [logDeriv_apply, ← neg_div]; exact neg_logDeriv_zeta_le hσ1 hσ2.le
      have hA1 : (-logDeriv riemannZeta s1).re
          ≤ (1 / (s1 - 1)).re + 1080 * Real.log (|ρ.im| + 2) - 1 / (σ - ρ.re) := by
        have h := zeta_neg_re_logDeriv_le_keep hρ hβ hβ1 hσ1 hσ2
        rw [← hs1def] at h; exact h
      have hA2 : (-logDeriv riemannZeta s2).re
          ≤ (1 / (s2 - 1)).re + 1080 * Real.log (|ρ.im| + 2) := by
        have h := zeta_neg_re_logDeriv_le hσ1 hσ2.le (γ := ρ.im)
        rw [← hs2def] at h; exact h
      have hP1 : (1 / (s1 - 1)).re ≤ 1 := by
        have him : (s1 - 1).im = ρ.im := by
          rw [hs1def]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        have hn : (1 : ℝ) ≤ ‖s1 - 1‖ := by
          have h := Complex.abs_im_le_norm (s1 - 1); rw [him] at h; linarith [hγ1]
        calc (1 / (s1 - 1)).re ≤ ‖1 / (s1 - 1)‖ :=
              le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
          _ = 1 / ‖s1 - 1‖ := by rw [norm_div, norm_one]
          _ ≤ 1 := by rw [div_le_one (by linarith : (0 : ℝ) < ‖s1 - 1‖)]; exact hn
      have hP2 : (1 / (s2 - 1)).re ≤ 1 := by
        have him : (s2 - 1).im = 2 * ρ.im := by
          rw [hs2def]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        have hn : (1 : ℝ) ≤ ‖s2 - 1‖ := by
          have h := Complex.abs_im_le_norm (s2 - 1); rw [him] at h
          have h2 : (2 : ℝ) * |ρ.im| = |2 * ρ.im| := by rw [abs_mul]; norm_num
          nlinarith [hγ1, h, h2, abs_nonneg (2 * ρ.im)]
        calc (1 / (s2 - 1)).re ≤ ‖1 / (s2 - 1)‖ :=
              le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
          _ = 1 / ‖s2 - 1‖ := by rw [norm_div, norm_one]
          _ ≤ 1 := by rw [div_le_one (by linarith : (0 : ℝ) < ‖s2 - 1‖)]; exact hn
      have e8 : (8 : ℝ) ≤ 8 * Lv := by nlinarith [hL1]
      have key : 4 * (1 / (σ - ρ.re)) ≤ 3 * (1 / (σ - 1)) + 5408 * Lv := by
        linarith [h341, hA0, hA1, hA2, hP1, hP2, e8, hLdef]
      have hchain' : 4 / (dd / Lv + (1 - ρ.re)) ≤ 3 / (dd / Lv) + 5408 * Lv := by
        rw [mul_one_div, mul_one_div] at key
        have e1 : σ - ρ.re = dd / Lv + (1 - ρ.re) := by rw [hσdef]; ring
        have e2 : σ - 1 = dd / Lv := by rw [hσdef]; ring
        rw [e1, e2] at key; exact key
      have hCdd : (5408 : ℝ) * dd = 1 / 2 := by rw [hdddef]; norm_num
      have hext := zero_free_extraction hLpos hddpos hCdd hβ1 hchain'
      have hfin : (1 / 75712 : ℝ) / Lv ≤ dd / (7 * Lv) := by
        rw [show dd / (7 * Lv) = dd / 7 / Lv from (div_div dd 7 Lv).symm,
            div_le_div_iff_of_pos_right hLpos, hdddef]
        norm_num
      linarith [hext, hfin]
  · -- Case `|γ| < 1`: the SHARPENED fixed zero-free strip
    have hst := zeta_zero_free_strip_sharp hρ (le_of_lt hγ1)
    have hc₃Lv : (1 / 75712 : ℝ) / Lv ≤ 1 / 50000 := by
      rw [div_le_iff₀ hLpos]
      have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      linarith [hLlog2, h2]
    linarith

/-- The `∃`-shaped `_bounded` twin of the sharpened region: `zeta_zero_free_region`'s constant
floored by `1/75712` — the literal of its own first `min` argument. -/
theorem zeta_zero_free_region_sharp_bounded :
    ∃ c₃ : ℝ, 0 < c₃ ∧ 1 / 75712 ≤ c₃ ∧ ∀ {ρ : ℂ}, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re →
      ρ.re ≤ 1 - c₃ / Real.log (|ρ.im| + 2) :=
  ⟨1 / 75712, by norm_num, le_refl _, fun hρ hre => zeta_zero_free_region_sharp hρ hre⟩

end Salt.SW
