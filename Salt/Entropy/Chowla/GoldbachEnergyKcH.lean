/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.GoldbachEnergyKc
import Salt.Entropy.Chowla.ShiftFork
import Salt.Tactic.ExpLogNum

/-!
# ⟦THE LARGE-SPECTRUM COUNT CONSTANT AT SHIFT `h`⟧ — wave H2a, word 1(a)–(c)

`bigXi_bounded_ceiling_of_pin` (`GoldbachEnergyKc.lean:231`) carries the terminal road's rider
`C ≤ 2^539`, and it is pinned BY HYPOTHESIS at the literal `ε = 1/500`.  The `h` lane pins
`ε = 1/(500·h)`, so that lemma does not apply and the `h` head reached instead for the
EXISTENTIAL `bigXi_bounded` — which exports only `0 < C`.  That is why `Kc ≤ 2^539` was
unreachable on the `h` lane, and it is the same defect as wave H1's `Cg` artifact: one `obtain`
reaching for the unbounded sibling.  This file removes it.

⟦THE ARITHMETIC, AND WHY IT IS TWO CASES AND NOT ONE⟧  At `ε = 1/(500·h)` the sieve threshold
must move with the shift.  `T := 2^41·h²` is the choice that keeps `hTA : 4 ≤ ε²·T` **`h`-FREE**
(`ε²·T = 2^41/250000 = 8 796 093.02`), which `T := 2^41·h³` does not.  The `C₁` payoff is then

  `C₁'(h) ≤ 1.58277·10^10 + 2.58249·10^10·h²`   against   `2^35·h² = 3.43597·10^10·h²`,

which holds for every `h ≥ 2` (ratio 0.867 at `h = 2`, 0.752 at `h = 1096`) and **FAILS at
`h = 1` by 1.212×** — because at `h = 1` the uniform `(log T)² ≤ 1799.4` is far looser than the
true `807.70`.  So `h = 1` is discharged by the LANDED `hpt_const_le_pow35`
(`GoldbachEnergyN0.lean:809`, ratio 0.955) and `h ≥ 2` by the uniform bound.  Two cases, forced.
(2026-10-02: the numerals of ⟦THE ARITHMETIC, AND WHY IT IS TWO CASES AND NOT ONE⟧ above are those
of the cap-7 page `hpt_const_le_pow35_h`, which the XY debt lane's family 37 retired into its cap-9
twin `hpt_const_le_pow35_h_b9` (§6), noted in §1.  The twin's are in its docstring:
`(log T)² ≤ 2154.8164`, closing ratio `0.891` at `h² = 4`; it keeps the two cases.)

⟦THE TOTAL⟧  The count witness is `h · 32·exp 40·(2^35·h²)²/ε^10 = 32·exp 40·2^70·500^10·h^15`.
⚠️ The exponent is `h^15`, not `h^11`: `ε^{-10}` gives ten, the squared constant `C₁(h)² = 2^70·h^4`
gives four, and the fiber bound gives one.  At `h ≤ 1096` that is `2^379.53` against `2^539` —
**159.47 bits of headroom.**

Nothing here bears on twin primes: the count is a bound on `|Ξ_H(h)|`, conditional on nothing.
-/

noncomputable section

namespace Salt.Entropy.Chowla

open scoped BigOperators

/-! ## §1 — the `C₁` numeral at shift `h` -/

/-! ### `hpt_const_le_pow35_h` AT `log h ≤ 7` — RETIRED INTO ITS CAP-9 TWIN

⟦XY debt lane, family 37 (2026-10-02)⟧
`hpt_const_le_pow35_h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) : (800 / (1 / 256 : ℝ) +
102400 / (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) ^ 2) + ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) ^ 2 *
((2 ^ 41 * h ^ 2 : ℕ) : ℝ) + 2 + 1 / (2 * ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ)) ^ 2)) * (Real.log
((2 ^ 41 * h ^ 2 : ℕ) : ℝ)) ^ 2 ≤ 2 ^ 35 * (h : ℝ) ^ 2` stood here.  It is `hpt_const_le_pow35_h_b9`
(in §6 below) with the hypothesis strengthened: the two statements differ in that ONE binder,
`log h ≤ 7` against `log h ≤ 9`, and are token-identical elsewhere, so the twin implies it by
`linarith` — kernel-checked from the retired statement's own bytes before the removal was committed.
The twin's body is this page's NUMERAL-LIFT with ONE tactic dropped, five code lines changed.  The
page's `42.42` is `46.42` in the twin, at the local fact `hLub` and in the `calc` under `hLsq`, and
its `1799.4564` is `2154.8164`, at `hLsq` and in that `calc`.  Where the page closed its `h = 1`
case with `convert hl using 3 <;> norm_num`, the twin has `convert hl using 3` alone, under a
comment that says the trailing `<;> norm_num` is never executed.  After these changes the two bodies
are the same code, token for token.  Their comments differ in three places: that comment of the
twin's, the numeral in the comment above the closing `nlinarith`, and a two-line comment of the
page's on the `ℕ`-cast argument of the goal's logarithm, which the twin does not carry.  Neither
body names its cap binder.  At this retirement the page had NO call site.  When the lane opened
(main, 2026-09-25) it had one, in `hpt_holds_500h` (§3 of this file), which family 36 retired into
its own cap-9 twin (2026-10-01); that twin calls this page's twin.  Of the declared names the page's
code calls, none is left without a caller.

The page's docstring, verbatim:

**⟦THE `C₁` NUMERAL AT SHIFT `h`⟧** (`hpt_const_le_pow35_h`) — `hpt_const_le_pow35`
(`GoldbachEnergyN0.lean:809`) at `ε = 1/(500·h)`, `T = 2^41·h²`, `c₀ = 1/256`.

The two cases are forced, not stylistic: the `hh7`-uniform `(log T)² ≤ 1799.4` overshoots at
`h = 1` (giving `4.166·10^10 > 3.436·10^10`), while at `h = 1` the landed lemma's own tight
`(log T)² = 807.70` gives `3.283·10^10 ≤ 3.436·10^10`. -/

/-! ## §2 — the shift's own `ℕ` bound -/

/-- `hh7 : log h ≤ 7` gives `h ≤ 1096` (`e^7 = 1096.63…`).  ⚠️ `Salt.MR.h_le_1096_of_hh7`
(wave H1, `S16ProducersH.lean`) is the MR-side twin of this; the MR side imports Entropy and not
the reverse, so the Entropy-side copy is stated here rather than reached for.  A later wave may
collapse them — recorded so the duplication is deliberate and visible, not discovered. -/
theorem h_le_1096_of_log_le_seven {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) :
    h ≤ 1096 := by
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hhle : (h : ℝ) ≤ Real.exp 7 := by
    rw [← Real.exp_log hh0]; exact Real.exp_le_exp.mpr hh7
  have he7 : Real.exp 7 < 1097 := by exact_mod_cast Salt.Tactic.exp_nat_lt_of_pow_lt 7 (by norm_num)
  have : (h : ℝ) < 1097 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- **⟦THE SHIFT'S `ℕ` BOUND AT THE RAISED CAP⟧ (class A)** — the `log h ≤ 14` twin of
`h_le_1096_of_log_le_seven`, for the `h`-cap reach (council 2026-09-08 ruling ⑤, "(B)":
target `h ≤ 10⁶`).  `e^14 = 1202604.284…`, so `h ≤ ⌊e^14⌋ = 1202604`, which clears `10⁶` by
`1.2026×`.  ⚠️ `Salt.MR.h_le_1202604_of_hh14` (`StrideGradeReach.lean`) is the MR-side twin of
this, for the same reason the `7` pair is duplicated: the MR side imports Entropy and not the
reverse.  **This is a NEW name with its OWN binder — `h_le_1096_of_log_le_seven` is untouched and
every one of its consumers is unaffected.**  BODY: the sibling's, at the `14`th power. -/
theorem h_le_1202604_of_log_le_fourteen {h : ℕ} (hh : 0 < h) (hh14 : Real.log (h : ℝ) ≤ 14) :
    h ≤ 1202604 := by
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hhle : (h : ℝ) ≤ Real.exp 14 := by
    rw [← Real.exp_log hh0]; exact Real.exp_le_exp.mpr hh14
  have he14 : Real.exp 14 < 1202605 := by
    exact_mod_cast Salt.Tactic.exp_nat_lt_of_pow_lt 14 (by norm_num)
  have : (h : ℝ) < 1202605 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-! ## §3 — the `hpt` twin at `ε = 1/(500·h)` -/

/-! ### `hpt_holds_500h` AT `log h ≤ 7` — RETIRED INTO ITS CAP-9 TWIN

⟦XY debt lane, family 36 (2026-10-01)⟧
`hpt_holds_500h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) : ∀ H n : ℕ, (repCount
(primeWindow (1 / (500 * (h : ℚ))) H) (primeWindow (1 / (500 * (h : ℚ))) H) n : ℝ) ≤ ((2 : ℝ) ^ 35 *
(h : ℝ) ^ 2) * ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n` stood
here.  It is `hpt_holds_500h_b9` (in §6 below) with the hypothesis strengthened: the two statements
differ in that ONE binder, `log h ≤ 7` against `log h ≤ 9`, and are token-identical elsewhere, so
the twin implies it by `linarith` — kernel-checked from the retired statement's own bytes before the
removal was committed.  The twin's body is NOT this page's line for line: it is its NUMERAL-LIFT
with a SUPPLIER-SWAP, four code lines changed and one comment.  The page read `h ≤ 1096` off the cap
through `h_le_1096_of_log_le_seven`; the twin reads `h ≤ 8103` off its own cap through
`h_le_8103_of_log_le_nine`.  So the page's `1201216` is `65658609` in the twin, at the local facts
`hsqb` and `hb`, and the page's supplier `hpt_const_le_pow35_h` (§1) is `hpt_const_le_pow35_h_b9` in
the twin.  The cap's binder and the local fact that carries the shift's bound are renamed with them:
`hh7` to `hh9`, `h1096` to `h8103`.  After these substitutions the two bodies are the same code,
token for token; the comment that differs says where the constant comes from (§1 for the page, §6
for the twin).  At this retirement the page had NO call site.  When the lane opened (main,
2026-09-25) it had two: `bigXiH_bounded_ceiling_of_pin` (of this file), whose call family 35
re-pointed to this page's twin (2026-10-01), and `bigXiAff_bounded_ceiling_of_pin` (of
`StrideFork`), which family 34 retired into its own cap-9 twin (2026-10-01); that twin calls this
page's twin.  The retirement leaves `hpt_const_le_pow35_h` without a caller.

The page stood under the line `set_option exponentiation.threshold 4000 in`; the page's
docstring, verbatim:

**⟦THE `hpt` TWIN AT SHIFT `h`⟧** (`hpt_holds_500h`) — `hpt_holds_500`
(`GoldbachEnergyN0.lean:829`) at `ε = 1/(500·h)` and `T = 2^41·h²`, with the numeral constant
`2^35·h²` from §1.  The four threshold side conditions and their `h`-powers:
`hT0 : 2^20 ≤ 2^41·h²` (h², slack `2^21·h²`) · **`hTA : 4 ≤ ε²·T = 2^41/250000 = 8 796 093.02`
— `h`-FREE, and that is exactly what `T := 2^41·h²` buys over `2^41·h³`** ·
`hTB : 16^10 = 2^40 ≤ 2^41·h²` (h², slack `2h²`) ·
`hTD : (500000·h²)^10 ≤ (2^41·h²)^9`, i.e. `500000^10·h² ≤ 2^369`, i.e. `h² ≤ 1.23·10^54`
(slack `1.02·10^48` at `h = 1096`). -/

/-! (§4, the count ceiling at shift `h`, stands at the foot of this file, below §6:
2026-10-01, the XY debt lane, family 35.) -/

/-! ## §5 — the ε line at shift `h` (wave H2a word 2 — a LINE, not a name) -/

/-- **⟦THE ε LINE AT SHIFT `h`⟧** — the ten `by norm_num` sites that derive
`(1:ℚ)/2^9 ≤ R.eps` from the head's `1/500 ≤ ε` (S16Compose:1072, XThread:1387, V7Ks:372,
S16ComposeV4:921, S16Uniform:1667/:1001, V7B:1800, RegisterCompose:287,
S16FlatTerminalLinear · flat_L_width_priced, S16FlatFinal:200) are a **PASS-THROUGH at `h`**: both sides scale by
exactly `h`, and `512 > 500`.  This `example` is the check that the line elaborates at a SYMBOLIC
`h`.

⚠️ **THE NAME IS MINTED AFTER ALL, AND THAT IS A FORK I AM NAMING.** The helm's 20:27 bus line
withdrew `eps_line_h` ("the same one-liner at each `h`-twin site, NOT a new lemma"); the
H2b/H2c commission filed the same hour then CITES `eps_line_h h hh` by name twice (its §1 word 3
and the register call). A name a downstream commission consumes must exist, and the cost is one
class-A lemma, so it is minted here and the conflict is recorded rather than resolved silently. -/
theorem eps_line_h (h : ℕ) (hh : 0 < h) :
    (1 : ℚ) / (2 ^ 9 * (h : ℚ)) ≤ 1 / (500 * (h : ℚ)) := by
  have hq0 : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hq0]

/-! ## §6 — ⟦β W1 E1⟧ the cap-9 twins (build freeze v2 v1.1, 2026-09-13)

Additive only: every declaration above is untouched.  Each twin is its source's statement and body
with ONLY the freeze's §3.1 rule-2 raises (`log h ≤ 7 ↦ ≤ 9`, `1096 ↦ 8103`, `1201216 ↦ 65658609`,
and the census's in-body numerals at cap 9); no hypothesis is added and no conclusion weakened.
(2026-10-01: the XY debt lane's family 35 moved §4's count hook, which stood above, to the foot of
the file, below these twins, and re-pointed its one call of `hpt_holds_500h` to
`hpt_holds_500h_b9`; its statement is unchanged.)
(2026-10-01: the XY debt lane's family 36 retired §3's `hpt_holds_500h` into its twin
`hpt_holds_500h_b9` below, noted where it stood.)
(2026-10-02: the XY debt lane's family 37 retired §1's `hpt_const_le_pow35_h` into its twin
`hpt_const_le_pow35_h_b9` below, noted where it stood.) -/

/-- **⟦THE SHIFT'S `ℕ` BOUND AT CAP 9⟧ (class A)** — the `log h ≤ 9` twin of
`h_le_1096_of_log_le_seven`, the Entropy-side converter of the β lane (`StridePrize`, `StrideFork`
and this file import no MR module; the MR sibling is `Salt.MR.h_le_8103_of_hh9`).
`e^9 = 8103.0839…`, so `h ≤ ⌊e^9⌋ = 8103`; the numeral is sharp (`h = 8103` meets `log h ≤ 9`).
BODY: `h_le_1202604_of_log_le_fourteen`'s, at the `9`th power. -/
theorem h_le_8103_of_log_le_nine {h : ℕ} (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9) :
    h ≤ 8103 := by
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hhle : (h : ℝ) ≤ Real.exp 9 := by
    rw [← Real.exp_log hh0]; exact Real.exp_le_exp.mpr hh9
  have he9 : Real.exp 9 < 8104 := by exact_mod_cast Salt.Tactic.exp_nat_lt_of_pow_lt 9 (by norm_num)
  have : (h : ℝ) < 8104 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- **⟦THE `C₁` NUMERAL AT SHIFT `h`, CAP 9⟧** (`hpt_const_le_pow35_h_b9`; the former
`hpt_const_le_pow35_h`, at `log h ≤ 7`, retired into this, 2026-10-02) — `hpt_const_le_pow35_h`
at `log h ≤ 9`.  The census (band 3 row 2): `log T ≤ 41·log 2 + 2·9 = 46.419 ≤ 46.42`,
`(log T)² ≤ 2154.8164`; the closing ratio at `h² = 4` is `0.891` (cap 7: `0.867`).  `h = 1` is
cap-free (the landed `hpt_const_le_pow35`). -/
theorem hpt_const_le_pow35_h_b9 (h : ℕ) (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9) :
    (800 / (1 / 256 : ℝ) + 102400 / (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) ^ 2)
        + ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) ^ 2 * ((2 ^ 41 * h ^ 2 : ℕ) : ℝ) + 2
            + 1 / (2 * ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ)) ^ 2))
          * (Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ)) ^ 2
      ≤ 2 ^ 35 * (h : ℝ) ^ 2 := by
  have hx0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hcast : (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) := by
    push_cast; ring
  have hTcast : ((2 ^ 41 * h ^ 2 : ℕ) : ℝ) = (2 : ℝ) ^ (41 : ℕ) * (h : ℝ) ^ 2 := by
    push_cast; ring
  rcases Nat.lt_or_ge h 2 with h1 | h2
  · -- ⟦h = 1⟧ the landed lemma, whose tight `(log T)² = 807.70` is what carries it
    have : h = 1 := by omega
    subst this
    have hl := hpt_const_le_pow35
    norm_num at hl ⊢
    -- (the source's trailing `<;> norm_num` is never executed — dropped so the twin adds no lint)
    convert hl using 3
  · -- ⟦h ≥ 2⟧ the uniform bound, with `h² ≥ 4` paying the `h`-free residue
    have hx2 : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast h2
    have hsq4 : (4 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith [hx2]
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hlogh0 : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_nonneg (by linarith)
    have hlogT : Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ) = 41 * Real.log 2 + 2 * Real.log (h : ℝ) := by
      rw [hTcast, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast; ring
    have hLnn : (0 : ℝ) ≤ Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ) := by
      rw [hlogT]; nlinarith [Real.log_two_gt_d9, hlogh0]
    have hLub : Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ) ≤ 46.42 := by
      rw [hlogT]; linarith
    have hLsq : (Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ)) ^ 2 ≤ 2154.8164 := by
      have := pow_le_pow_left₀ hLnn hLub 2
      calc (Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ)) ^ 2 ≤ (46.42 : ℝ) ^ 2 := this
        _ = 2154.8164 := by norm_num
    rw [hcast]
    have e1 : (102400 : ℝ) / (1 / (500 * (h : ℝ))) ^ 2 = 25600000000 * (h : ℝ) ^ 2 := by
      field_simp; ring
    have e2 : (1 / (500 * (h : ℝ))) ^ 2 * ((2 ^ 41 * h ^ 2 : ℕ) : ℝ)
        = 2199023255552 / 250000 := by
      rw [hTcast]; field_simp; ring
    have e3 : (1 : ℝ) / (2 * (1 / (500 * (h : ℝ))) ^ 2) = 125000 * (h : ℝ) ^ 2 := by
      field_simp; ring
    have e0 : (800 : ℝ) / (1 / 256 : ℝ) = 204800 := by norm_num
    rw [e0, e1, e2, e3]
    -- `204800 + 2.56e10·h² + (8796093.02 + 2 + 125000·h²)·L² ≤ 2^35·h²` at `L² ≤ 2154.8164`
    nlinarith [hLsq, hsq4, sq_nonneg (Real.log ((2 ^ 41 * h ^ 2 : ℕ) : ℝ))]

set_option exponentiation.threshold 4000 in
/-- **⟦THE `hpt` TWIN AT SHIFT `h`, CAP 9⟧** (`hpt_holds_500h_b9`; the former `hpt_holds_500h`,
at `log h ≤ 7`, retired into this, 2026-10-01) — `hpt_holds_500h` at
`log h ≤ 9`: the shift bound from `h_le_8103_of_log_le_nine`, `hsqb : h² ≤ 65658609 = 8103²`,
`hb : 500000^10·65658609 ≤ 2^369` (`6.41·10^64` against `1.20·10^111`, census band 3 row 3), and
the constant from `hpt_const_le_pow35_h_b9`.  Every other step is the source's, verbatim (the
retired page's; its note stands above, in §3). -/
theorem hpt_holds_500h_b9 (h : ℕ) (hh : 0 < h) (hh9 : Real.log (h : ℝ) ≤ 9) :
    ∀ H n : ℕ,
      (repCount (primeWindow (1 / (500 * (h : ℚ))) H)
          (primeWindow (1 / (500 * (h : ℚ))) H) n : ℝ)
        ≤ ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2)
            * ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by
  have hx0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hq0 : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  have hq1 : (1 : ℚ) ≤ (h : ℚ) := by exact_mod_cast hh
  have hx1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hcast : (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) := by push_cast; ring
  have hTcast : ((2 ^ 41 * h ^ 2 : ℕ) : ℝ) = (2 : ℝ) ^ (41 : ℕ) * (h : ℝ) ^ 2 := by
    push_cast; ring
  have h8103 : (h : ℝ) ≤ 8103 := by exact_mod_cast h_le_8103_of_log_le_nine hh hh9
  intro H n
  refine le_trans (hpt_holds_thr (1 / (500 * (h : ℚ))) (by positivity) ?_ (1 / 256)
    (by norm_num) 16 repCount_even_le_primorial_sixteen (2 ^ 41 * h ^ 2) ?_ ?_ ?_ ?_ H n) ?_
  · -- `heps2 : ε² < 1/2`
    rw [hcast]
    have : (1 : ℝ) / (500 * (h : ℝ)) ≤ 1 / 500 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hx1]
    have h0 : (0 : ℝ) < 1 / (500 * (h : ℝ)) := by positivity
    nlinarith [this, h0]
  · -- `hT0 : N0' ≤ T`
    have : (2 : ℕ) ^ 20 ≤ 2 ^ 41 * h ^ 2 := by
      have hh2 : 1 ≤ h ^ 2 := Nat.one_le_pow _ _ hh
      calc (2 : ℕ) ^ 20 ≤ 2 ^ 41 := by norm_num
        _ = 2 ^ 41 * 1 := by ring
        _ ≤ 2 ^ 41 * h ^ 2 := Nat.mul_le_mul_left _ hh2
    simpa [N0'] using this
  · -- `hTA : 4 ≤ ε²·T` — h-FREE
    have hTq : (((2 ^ 41 * h ^ 2 : ℕ) : ℚ)) = 2 ^ 41 * (h : ℚ) ^ 2 := by push_cast; ring
    rw [hTq]
    have hid : (1 / (500 * (h : ℚ))) ^ 2 * (2 ^ 41 * (h : ℚ) ^ 2) = 2 ^ 41 / 250000 := by
      field_simp; ring
    rw [hid]; norm_num
  · -- `hTB : 16^10 ≤ T`
    rw [hTcast]
    have hsq1 : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith [hx1]
    have h16 : ((16 : ℕ) : ℝ) ^ (10 : ℕ) = 1099511627776 := by norm_num
    have h41 : (2 : ℝ) ^ (41 : ℕ) = 2199023255552 := by norm_num
    rw [h16, h41]
    nlinarith [hsq1]
  · -- `hTD : (2/ε²)^10 ≤ T^9`
    rw [hcast, hTcast]
    have hsq1 : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith [hx1]
    have hsqb : (h : ℝ) ^ 2 ≤ 65658609 := by nlinarith [hx1, h8103]
    have hL : (2 : ℝ) / (1 / (500 * (h : ℝ))) ^ 2 = 500000 * (h : ℝ) ^ 2 := by
      field_simp; ring
    rw [hL]
    have hexp : ((500000 : ℝ) * (h : ℝ) ^ 2) ^ (10 : ℕ)
        = 500000 ^ (10 : ℕ) * ((h : ℝ) ^ 2) ^ (10 : ℕ) := by ring
    have hexp9 : ((2 : ℝ) ^ (41 : ℕ) * (h : ℝ) ^ 2) ^ (9 : ℕ)
        = (2 : ℝ) ^ (369 : ℕ) * ((h : ℝ) ^ 2) ^ (9 : ℕ) := by
      rw [mul_pow, ← pow_mul]
    rw [hexp, hexp9]
    have hp9 : (0 : ℝ) < ((h : ℝ) ^ 2) ^ (9 : ℕ) := by positivity
    have hsplit : ((h : ℝ) ^ 2) ^ (10 : ℕ) = ((h : ℝ) ^ 2) ^ (9 : ℕ) * (h : ℝ) ^ 2 := by ring
    rw [hsplit]
    -- `500000^10 · (h²)^9 · h² ≤ 2^369 · (h²)^9`  ⟸  `500000^10 · h² ≤ 2^369`
    have hnum : (500000 : ℝ) ^ (10 : ℕ) * (h : ℝ) ^ 2 ≤ (2 : ℝ) ^ (369 : ℕ) := by
      have hb : (500000 : ℝ) ^ (10 : ℕ) * 65658609 ≤ (2 : ℝ) ^ (369 : ℕ) := by norm_num
      nlinarith [hsqb, hsq1]
    calc (500000 : ℝ) ^ (10 : ℕ) * (((h : ℝ) ^ 2) ^ (9 : ℕ) * (h : ℝ) ^ 2)
        = ((500000 : ℝ) ^ (10 : ℕ) * (h : ℝ) ^ 2) * ((h : ℝ) ^ 2) ^ (9 : ℕ) := by ring
      _ ≤ (2 : ℝ) ^ (369 : ℕ) * ((h : ℝ) ^ 2) ^ (9 : ℕ) :=
          mul_le_mul_of_nonneg_right hnum hp9.le
  · -- the constant, from §6
    have hnn : (0 : ℝ) ≤ ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) ^ 2 * H / (Real.log H) ^ 2)
        * sTrunc2 n :=
      mul_nonneg (div_nonneg (by positivity) (sq_nonneg _)) (sTrunc2_nonneg n)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hpt_const_le_pow35_h_b9 h hh hh9) (by positivity))
      (sTrunc2_nonneg n)

/-! ### §4, MOVED BELOW THE CAP-9 TWINS (XY debt lane, family 35, 2026-10-01)

The count ceiling stood between §3 and §5.  It read §3's supplier `hpt_holds_500h`; it now calls
that supplier's cap-9 twin `hpt_holds_500h_b9`, which stands in §6, so the page stands below it.
The §4 header, the `set_option` line, the statement and the body are byte-identical to the ones
that stood above, except ONE line of the body, the call re-pointed at the twin with `log h ≤ 9`
proved there from `hh7`; the docstring gains one dated paragraph. -/

/-! ## §4 — the count ceiling at shift `h` -/

set_option exponentiation.threshold 4000 in
/-- **⟦THE COMPOSE HOOK AT SHIFT `h`⟧** (`bigXiH_bounded_ceiling_of_pin`) —
`bigXi_bounded_ceiling_of_pin` (`GoldbachEnergyKc.lean:231`) at the `h` lane's own pin
`ε = 1/(500·h)`, carrying the terminal road's rider `C ≤ 2^539`.

**This is the lemma whose absence made `Kc ≤ 2^539` unreachable at `h`.** The `h` head obtains
`bigXiH_bounded` (`ShiftFork.lean:253`), which routes through the EXISTENTIAL `bigXi_bounded`
and exports only `0 < C`; the `h = 1` head obtains the pinned hook and gets the ceiling with it.
One `obtain` — the same shape as wave H1's `Cg` artifact.

⟦THE WITNESS AND ITS SIZE⟧ `h · 32·exp 40·(2^35·h²)²·(500h)^10 = 32·exp 40·2^70·500^10·h^15`.
The exponent is **`h^15`**: `ε^{-10}` gives ten, the squared constant `C₁(h)² = 2^70·h^4` gives
four, the fiber bound `bigXiH_card_le_mul` gives one. On the corpus's own chain
(`exp 40 ≤ 3^40`) that is `2^379.53` at `h ≤ 1096`, against `2^539` — **159.47 bits spare**.

(2026-10-01, the XY debt lane, family 35: the `hpt` supplier is called here at its cap-9 twin
`hpt_holds_500h_b9`, `log h ≤ 9` proved at the call from `hh7`; the ceiling still reads `h ≤ 1096`
off `hh7`.) -/
theorem bigXiH_bounded_ceiling_of_pin (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    (ε : ℚ) (hε : ε = 1 / (500 * (h : ℚ))) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 539 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((bigXiH h ε H).card : ℝ) ≤ C := by
  subst hε
  have hx0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hx1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hq0 : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  have h1096 : (h : ℝ) ≤ 1096 := by exact_mod_cast h_le_1096_of_log_le_seven hh hh7
  have hcast : (((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) := by push_cast; ring
  have heps2 : ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ)) ^ 2 < 1 / 2 := by
    rw [hcast]
    have hle : (1 : ℝ) / (500 * (h : ℝ)) ≤ 1 / 500 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hx1]
    have h0 : (0 : ℝ) < 1 / (500 * (h : ℝ)) := by positivity
    nlinarith [hle, h0]
  have hbase := bigXi_bounded_explicit (1 / (500 * (h : ℚ))) (by positivity) heps2
    ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) (Real.exp 40) (Real.exp_pos _) hFac2_lcm_sum_le_exp40
    (hpt_holds_500h_b9 h hh (le_trans hh7 (by norm_num)))
  -- ⟦THE WITNESS, DIVISION-FREE⟧
  refine ⟨32 * Real.exp 40 * ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) ^ 2 * (500 * (h : ℝ)) ^ (10 : ℕ)
      * (h : ℝ), by positivity, ?_, 2, le_rfl, ?_⟩
  · -- ⟦THE CEILING⟧ `32·exp 40·2^70·500^10·h^15 ≤ 2^539`
    have h40 : Real.exp 40 ≤ 3 ^ (40 : ℕ) := by
      simpa using exp_forty_le_pow40
    have hexp0 : (0 : ℝ) < Real.exp 40 := Real.exp_pos _
    have hfold : 32 * Real.exp 40 * ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) ^ 2 * (500 * (h : ℝ)) ^ (10 : ℕ)
        * (h : ℝ)
        = (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * Real.exp 40 * (h : ℝ) ^ (15 : ℕ) := by
      ring
    have hp15 : (h : ℝ) ^ (15 : ℕ) ≤ (1096 : ℝ) ^ (15 : ℕ) :=
      pow_le_pow_left₀ hx0.le h1096 15
    have hnn : (0 : ℝ) ≤ 32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ) := by positivity
    have hnum : (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * 3 ^ (40 : ℕ) * (1096 : ℝ) ^ (15 : ℕ)
        ≤ 2 ^ 539 := by norm_num
    rw [hfold]
    calc (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * Real.exp 40 * (h : ℝ) ^ (15 : ℕ)
        ≤ (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * 3 ^ (40 : ℕ) * (1096 : ℝ) ^ (15 : ℕ) := by
          have h1 : (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * Real.exp 40
              ≤ (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * 3 ^ (40 : ℕ) :=
            mul_le_mul_of_nonneg_left h40 hnn
          have h2 : (0 : ℝ) ≤ (32 * (2 : ℝ) ^ 70 * 500 ^ (10 : ℕ)) * 3 ^ (40 : ℕ) := by positivity
          nlinarith [h1, h2, hp15, pow_nonneg hx0.le 15]
      _ ≤ 2 ^ 539 := hnum
  · -- ⟦THE BOUND⟧ the fiber times the pinned count
    intro H _ hH2
    have hfib : ((bigXiH h (1 / (500 * (h : ℚ))) H).card : ℝ)
        ≤ (h : ℝ) * ((bigXi (1 / (500 * (h : ℚ))) H).card : ℝ) := by
      exact_mod_cast bigXiH_card_le_mul h hh (1 / (500 * (h : ℚ))) H
    have hb := hbase H hH2
    have hden : 32 * Real.exp 40 * ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) ^ 2
          / ((((1 : ℚ) / (500 * (h : ℚ)) : ℚ) : ℝ)) ^ 10
        = 32 * Real.exp 40 * ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) ^ 2 * (500 * (h : ℝ)) ^ (10 : ℕ) := by
      rw [hcast]; field_simp
    rw [hden] at hb
    calc ((bigXiH h (1 / (500 * (h : ℚ))) H).card : ℝ)
        ≤ (h : ℝ) * ((bigXi (1 / (500 * (h : ℚ))) H).card : ℝ) := hfib
      _ ≤ (h : ℝ) * (32 * Real.exp 40 * ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) ^ 2
            * (500 * (h : ℝ)) ^ (10 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hb hx0.le
      _ = 32 * Real.exp 40 * ((2 : ℝ) ^ 35 * (h : ℝ) ^ 2) ^ 2 * (500 * (h : ℝ)) ^ (10 : ℕ)
            * (h : ℝ) := by ring

end Salt.Entropy.Chowla

end
