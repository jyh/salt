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

end Salt.SW
