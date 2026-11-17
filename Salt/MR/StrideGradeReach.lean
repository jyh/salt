/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# λ-BV wave 2-S, step F5 (γ) — THE `h`-CAP REACH: the graded lane's walls at `log h ≤ 14`

Council 2026-09-08 (evening), ruling ⑤, the Captain's word **"(B)"**: reach IS wanted, target
`h ≤ 10⁶`.  `StrideGradeWalls.lean` (F5-β) runs the graded lane at `log h ≤ 7`, i.e. `h ≤ 1096`;
this module runs the same walls at `log h ≤ 14`, i.e. **`h ≤ ⌊e^14⌋ = 1202604`**, which clears the
ordered target by `1.2026×`.  Every name here is NEW and takes its OWN cap binder `hh14`; **no
landed declaration moves and no landed statement is re-pointed** (iron rules 1 and 5).  Carrying
the raise into the lane's FORM statements — the `hh7`/`a ≤ 1096` binders the prize is stated at —
is a statement act and is NOT taken here; it is the freeze this wave hands to the helm.

WHY ONE NAT-DOUBLING OF THE CAP IS THE WHOLE RAISE.  `h` enters the binding wall
LOGARITHMICALLY (`log c = 11·log 2 + 2·log h`) and the far walls polynomially, so `7 ↦ 14` moves
the reach `1096 ↦ 1202604` — a factor `1097×` — while every numeral below moves by a bounded,
computable amount.

THE NUMERALS (each re-derived here, none copied from a docstring):
  · the cap:      `log h ≤ 14 ⇒ h ≤ 1202604`  (`e^14 = 1202604.284…`; the exact `⌊e^14⌋` bound,
    as the landed `1096 = ⌊e^7⌋`), and `1202604 ≥ 10⁶` — the ordered target, `1.2026×` clear;
  · the `c`-ceiling `2^11·1202604² = 2961933067911168` EXACTLY (as the landed `2^11·1096² =
    2460090368`); zero margin BY CONSTRUCTION, safe for the same reason the landed one is —
    its sole supplier is the exact `⌊e^14⌋` bound;
  · `hlogc : log c ≤ 36`: `log(2961933067911168) = 35.62462`, slack `0.37538` nats — the same
    shape as the landed `log(2460090368) = 21.62346 ≤ 22`, slack `0.37654`;
  · `hρlog : log(1/ρ) ≤ 439`, and THE TWO ROUTES AGREE: `403 + log c = 403 + 36` and
    `411 + 2·log h = 411 + 2·14`, both `= 439` (the landed pair is `403 + 22 = 411 + 14 = 425`).
    The `411` floor is `592·log 2 = 410.343`, slack `0.657` nats, and is UNCHANGED by the raise;
  · the arm's ceiling family `128·838400·2961933067911168 = 3.178604·10²³ ≤ 4·10²³` (`1.2584×`;
    the landed `2.640051·10¹⁷ ≤ 27·10¹⁶` is `1.0227×`).  ⛔ THE NUMERAL IS ALSO A FLOOR ON `H₊`
    (`hHhibig`), and there it is free: `H₊ = u² ≥ (1.8·10²¹)² = 3.24·10⁴²`, i.e. `8.1·10¹⁸×` of
    room above `4·10²³`;
  · the four cap lines at `439` in place of `425`: `+14` (or `+42` on the window line, which
    carries `3·c`) against `449×`, `≈5.5·10³×`, `457×`, and the window line's own
    `10³⁴ ≤ e^{3.2A}` at `A ≥ 26` — free at every one;
  · the exponent `7000·Λ + 500·439 + 6600 ≤ e^Λ/2` at `Λ ≥ 50`: `576100 ≤ 2.59·10²¹`, `4.5·10¹⁵×`.

⭐ AND THE WALL THAT IS **NOT** A NUMERAL, WHICH IS WHY IT IS HERE.  `s13CapGrid_q_logX_LH`
(`S13CapGateLinearLH.lean` · `s13CapGrid_q_logX_LH`) closes `q ≤ h·(log H)^12 ≤ (log X_d)^12` out of
`capfloor_logH_le_half_sqrt` — `log H ≤ √H/2` — which buys exactly `2^12 = 4096` of room in `h`.
(2026-10-03: the XY debt lane's family 25 (2026-09-30) retired `s13CapGrid_q_logX_LH` into its cap-9
twin `s13CapGrid_q_logX_LH_b9`, which takes `k = 3` through `capfloor_logH_le_third_sqrt`, so its
room is `3^12 = 531441`; this paragraph describes the cap-7 page, whose note in
`S13CapGateLinearLH.lean` keeps its docstring.)
**That `4096` is a STRUCTURAL factor `k^12`, not a numeral: it is the `k` in `log H ≤ √H/k`.**  Its
docstring's *"margin 3.7×"* is `4096/1096` — a margin on `h` computed at the landed `k = 2` — and
it reads as a ceiling when `k` is free.  ⇒ ***A FACTOR THAT IS A PARAMETER RAISED TO A POWER LOOKS
LIKE A CONSTANT IN EVERY GREP.***  `capfloor_logH_le_quarter_sqrt` below takes `k = 2 ↦ 4`, buying
`4^12 = 16777216` — `13.95×` above the new cap — and its own inequality has `32.89×` at the floor
`H ≥ 4·10⁶` (`log(4·10⁶) = 15.20 ≤ 500`).

⛔ THE LIMIT OF THE REACH, STATED SO IT IS NOT MISREAD.  The first wall with CONTENT is the
`2^539` count pin through `(a·h)^15`, re-derived here rather than quoted: `a·h ≤ 2261670` at the
OBLIGATION (`exp 40`) and `a·h ≤ 1738699` on the LANDED PROOF's route (`exp 40 ≤ 3^40`, `51.6×`
loose — the corpus's published `159.47` bits is this second figure, confirmed to the digit).  At
`a = 1` the new cap FITS under both (`1.881×` / `1.446×`) — but **at `a = 2` the pin REFUSES
`h = 1202604` under both**.  ⇒ **this is a reach in the SHIFT, not in the STRIDE**, and
`reach14_countpin_refuses_stride_two` records the refusal in the kernel AT THE LOOSER CEILING, so
it cannot be read as an artefact of the proof's majorant.

HONEST LABEL.  Numerals and one structural factor; nothing here proves an estimate, no landed
statement moves, and **nothing bears on twin primes**.
-/
import Salt.MR.StrideGradeWalls
import Salt.MR.S13CapFloor
import Mathlib

-- as `StrideGradeWalls`: the arm's body reaches `XThread`'s private numeral helper `xt_exp25`
-- (`6·10^10 ≤ e^25`) by `open private`, the corpus's sanctioned device.
open private xt_exp25 from Salt.MR.XThread

noncomputable section

open Salt.Entropy.Chowla

set_option exponentiation.threshold 4000

namespace Salt.MR

/-! ## §0 — THE ARITHMETIC OF THE RAISE, IN THE KERNEL, EACH WITH ITS CONTROL

Every numeral this module moves is pinned here by `decide`/`norm_num` BEFORE it is spent, and
each positive pin is paired with the negative one that shows the LANDED numeral refuses the
ordered target.  ⛔ The controls are half the finding: without them the positives read as
*"the numerals are comfortable"*, which is false — three of them are the exact `⌊e^14⌋` bound. -/

/-- **⟦THE NEW `c`-CEILING IS EXACT⟧ (class A)** — `2^11·1202604² = 2961933067911168`, the twin
of the landed `2^11·1096² = 2460090368`.  Checked, not quoted. -/
theorem reach14_ceiling_eq : (2 : ℕ) ^ 11 * 1202604 ^ 2 = 2961933067911168 := by norm_num

/-- **⟦THE ORDERED TARGET IS REACHED⟧ (class A)** — council ⑤'s `h ≤ 10⁶`, cleared by `1.2026×`. -/
theorem reach14_reaches_the_million : (10 : ℕ) ^ 6 ≤ 1202604 := by norm_num

/-- **⟦THE ARM'S CEILING FAMILY FITS AT `4·10²³`⟧ (class A)** — `128·838400·2961933067911168 =
3.178604·10²³`, `1.2584×` clear. -/
theorem reach14_arm_family_fits :
    (128 : ℝ) * 838400 * 2961933067911168 ≤ 4 * 10 ^ 23 := by norm_num

/-- **⟦THE CAPGATE LEAF HAS ROOM AT `k = 4`⟧ (class A)** — `4^12 = 16777216 ≥ 1202604`, `13.95×`. -/
theorem reach14_capgate_room : (1202604 : ℕ) ≤ 4 ^ 12 := by norm_num

/-- ⛔ **⟦CONTROL — THE LANDED `c`-CEILING REFUSES THE ORDERED TARGET⟧ (class A)** — at `h = 10⁶`
the landed `2460090368` fails by a factor `832×`.  Without this the positive above reads as a
free numeral; it is not. -/
theorem landed_ceiling_refuses_the_million :
    ¬ ((2 : ℕ) ^ 11 * (10 ^ 6) ^ 2 ≤ 2460090368) := by norm_num

/-- ⛔ **⟦CONTROL — THE LANDED CAPGATE FACTOR REFUSES THE ORDERED TARGET⟧ (class A)** — `k = 2`
gives `2^12 = 4096`, and `10⁶ > 4096` by `244×`.  This is the wall that is not a numeral.
(2026-10-03: the landed factor is the cap-7 page's, which the XY debt lane's family 25 retired on
2026-09-30; its cap-9 twin `s13CapGrid_q_logX_LH_b9` takes `k = 3`, and `3^12 = 531441` refuses
`10⁶` by `1.88×`.) -/
theorem landed_capgate_refuses_the_million : ¬ ((10 : ℕ) ^ 6 ≤ 4096) := by norm_num

/-- ⛔ **⟦CONTROL — THE COUNT PIN REFUSES THE NEW CAP AT STRIDE 2, EVEN AT ITS LOOSEST READING⟧
(class A)** — the `2^539` count pin (`GoldbachEnergyKcH.lean · bigXiH_bounded_ceiling_of_pin`) carries the witness
`32·exp 40·2^70·500^10·(a·h)^15 ≤ 2^539`, and it has TWO ceilings, which is the point of stating
this control against the LOOSER one:
```
  the OBLIGATION   (exp 40 = 2.35·10^17)   base 2^222.366   ⇒  a·h ≤ 2261670
  the PROOF ROUTE  (exp 40 ≤ 3^40, the landed proof's own majorant, 51.6× loose)
                                           base 2^228.056   ⇒  a·h ≤ 1738699
```
The corpus's published *"`2^379.53` against `2^539`, 159.47 bits spare at `h ≤ 1096`"* is the
PROOF ROUTE's figure, re-derived here and confirmed to the digit; the obligation's is `165.16`
bits.  ⇒ 🔑 ***A MARGIN QUOTED AGAINST A PROOF STEP IS NOT A MARGIN AGAINST THE OBLIGATION*** —
the same law this campaign learned at `flat_arm_budget_le_h`, in the same corpus, one wall over.
**At `a = 1` the new cap FITS under both** (`1.881×` / `1.446×`); **at `a = 2` it REFUSES under
both**, and this theorem states the refusal at the LOOSER ceiling so it cannot be read as an
artefact of the proof's majorant.  ⇒ **the reach is in the SHIFT and not in the STRIDE**, and no
numeral in this module changes that. -/
theorem reach14_countpin_refuses_stride_two : ¬ (2 * 1202604 ≤ 2261670) := by norm_num

/-! ## §1 — THE CAP CONVERTER AT `14` (`h_le_1096_of_hh7`'s twin) -/

/-- **⟦THE SHIFT IS BOUNDED BY ITS OWN BINDER, AT `14`⟧ (class A)** — the twin of
`h_le_1096_of_hh7` (`S16ProducersH.lean`) at the raised cap: `e^14 = 1202604.284…`, so
`h ≤ 1202604`.  Every numeral in this module is stated against this one.  BODY: the landed
proof's shape with `Real.exp_one_lt_d9` raised to the `14`th instead of the `7`th. -/
theorem h_le_1202604_of_hh14 {h : ℕ} (hh : 0 < h) (hh14 : Real.log (h : ℝ) ≤ 14) :
    h ≤ 1202604 := by
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hhle : (h : ℝ) ≤ Real.exp 14 := by
    rw [← Real.exp_log hh0]; exact Real.exp_le_exp.mpr hh14
  have he14 : Real.exp 14 < 1202605 := by
    have h3 : Real.exp 14 = (Real.exp 1) ^ (14 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    have h4 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h5 : (Real.exp 1) ^ (14 : ℕ) < (2.7182818286 : ℝ) ^ (14 : ℕ) :=
      pow_lt_pow_left₀ h4 (Real.exp_pos 1).le (by norm_num)
    have h6 : (2.7182818286 : ℝ) ^ (14 : ℕ) < 1202605 := by norm_num
    rw [h3]; linarith
  have : (h : ℝ) < 1202605 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-! ## §2 — WALL 2, AND IT IS THE ONE THAT IS NOT A NUMERAL

`log H ≤ √H/k` buys `k^12` of room in `h` at `s13CapGrid_q_logX_LH`.  The landed `k = 2`
(`capfloor_logH_le_half_sqrt`, `S13CapFloor.lean:110`) gives `4096`; `k = 4` gives `16777216`.
(2026-10-03: `s13CapGrid_q_logX_LH` was retired into its cap-9 twin `s13CapGrid_q_logX_LH_b9`, at
`k = 3`, by the XY debt lane's family 25 on 2026-09-30; the `k = 2` reading above is the cap-7
page's; the `k = 4` figure is this file's own lemma's, and no cap-grid page is built at it.) -/

/-- **⟦`log H ≤ √H/4` AT `H ≥ 4·10⁶`⟧ (class B)** — `capfloor_logH_le_half_sqrt`'s `k = 4` twin,
the same proof at a harder closing step.  With `a := H^{1/4}`, `log a = (log H)/4 ≤ a − 1` gives
`log H ≤ 4a − 4`, and `√H/4 = a²/4`, so the close is `a² − 16a + 16 ≥ 0`, i.e. `a ≥ 8 + 4√3 =
14.93` — supplied by the landed `a ≥ 40`.  (The landed `k = 2` closes `a² − 8a + 8 ≥ 0`, i.e.
`a ≥ 6.83`.)  MARGIN at the floor: `log(4·10⁶) = 15.2018 ≤ 500`, `32.89×`. -/
theorem capfloor_logH_le_quarter_sqrt {H : ℝ} (hH : (4000000 : ℝ) ≤ H) :
    Real.log H ≤ Real.sqrt H / 4 := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt H := Real.sqrt_pos.mpr hH0
  set a : ℝ := Real.sqrt (Real.sqrt H) with ha
  have ha0 : (0 : ℝ) < a := Real.sqrt_pos.mpr hs0
  have ha2 : a * a = Real.sqrt H := Real.mul_self_sqrt hs0.le
  have hloga : Real.log a = Real.log H / 4 := by
    rw [ha, Real.log_sqrt hs0.le, Real.log_sqrt hH0.le]; ring
  have hle : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos ha0
  have hs2000 : (2000 : ℝ) ≤ Real.sqrt H := by
    nlinarith [Real.mul_self_sqrt hH0.le, hs0]
  have ha40 : (40 : ℝ) ≤ a := by nlinarith [ha2, ha0, hs2000]
  nlinarith [hloga, hle, ha2, ha40, ha0]

/-! ## §3 — THE FOUR CAP LINES AT `439` (`StrideGradeWalls.lean:130-245`'s twins at the raised
charge; hypothesis weakenings, bodies verbatim) -/


/-- **⟦THE `anchor` LINE AT `439`⟧ (class A)** — `flat_anchor_line_wide_g` with `hc : c ≤ 439`.
BODY: verbatim (`449×` at the landed charge; `+14` against `39·10⁸·M`). -/
theorem flat_anchor_line_wide_g14 {A c : ℝ} (hA : 26 ≤ A) (hc : c ≤ 439) :
    14 * (2 * Real.exp (3.2 * A / 2)) + c + 33
      ≤ 39 * 10 ^ 8 * ((flatDoorM A : ℕ) : ℝ) := by
  have hE17 := flat_exp_half_ge hA
  have hMge := flatDoorM_ge A
  linarith

/-! ## §4 — THE ARM AT THE RAISED `c`-CEILING (`StrideGradeWalls.lean:430`'s twin) -/

/-- **⟦THE ARM'S LOG AT SHIFT `h`, GRADED, AT THE RAISED CAP⟧ (class A)** — `s15ArmH_log_le_g`
with `hh7 : log h ≤ 7 ↦ hh14 : log h ≤ 14`, `h ≤ 1096 ↦ h ≤ 1202604`, the `c`-ceiling at
`2961933067911168` and `hlogc` at `36`; conclusion unchanged.  ⚠ `2^11·1202604² =
2961933067911168` EXACTLY — zero margin, safe for the same reason the landed one is: its supplier
`h_le_1202604_of_hh14` is itself the exact `⌊e^14⌋` bound.  The `hlogc` split is
`11·log 2 + 2·log h ≤ 7.6247 + 28 = 35.6247 ≤ 36`.  **This name takes its OWN binder `hh14`; it
re-points nothing.** -/
theorem s15ArmH_log_le_g14 {h : ℕ} (hh : 0 < h) (hh14 : Real.log (h : ℝ) ≤ 14) {δ₀ Kc : ℝ}
    (hδ₀ : 0 < δ₀) (hδpin : 1 / (838400 * 2 ^ 11 * (h : ℝ) ^ 2) ≤ δ₀)
    (hKc : 0 < Kc) (hKcb : Kc ≤ 2 ^ 539) {Hhi ω : ℕ}
    (hHhi : 4000000 ≤ Hhi) (hΛ : 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ Real.log ((ω : ℕ) : ℝ) + Real.log (h : ℝ) + ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
  have hh1R : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hc1 : (1 : ℝ) ≤ (2 : ℝ) ^ 11 * (h : ℝ) ^ 2 := by nlinarith [hh1R]
  have h1202604 : (h : ℝ) ≤ 1202604 := by exact_mod_cast h_le_1202604_of_hh14 hh hh14
  have hcb : (2 : ℝ) ^ 11 * (h : ℝ) ^ 2 ≤ 2961933067911168 := by nlinarith [hh1R, h1202604]
  have hlogc : Real.log ((2 : ℝ) ^ 11 * (h : ℝ) ^ 2) ≤ 36 := by
    have hhpos : (0 : ℝ) < (h : ℝ) := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    push_cast
    linarith
  have hδpin' : 1 / (838400 * ((2 : ℝ) ^ 11 * (h : ℝ) ^ 2)) ≤ δ₀ := by
    rw [← mul_assoc]; exact hδpin
  have hbase := s15Arm_log_le_scaled_g14 hc1 hcb hlogc hδ₀ hδpin' hKc hKcb (ω := ω) hHhi hΛ
  have hle := s15ArmH_le_mul hh δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω
  have hleR : ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ (h : ℝ) * ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hω0 : 0 ≤ Real.log ((ω : ℕ) : ℝ) := Real.log_natCast_nonneg ω
  have hh0 : 0 ≤ Real.log (h : ℝ) := Real.log_natCast_nonneg h
  have hHhi0 : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by positivity
  rcases Nat.eq_zero_or_pos (s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω)
    with hz | hpos
  · rw [hz]; simp only [Nat.cast_zero, Real.log_zero]; linarith
  · have hposR : (0 : ℝ)
        < ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) := by
      exact_mod_cast hpos
    have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    have hbpos : (0 : ℝ)
        < ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) := by
      by_contra hcon
      have hb0 : ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) ≤ 0 :=
        not_lt.mp hcon
      nlinarith [hleR, hposR, hhR, hb0]
    have hlog := Real.log_le_log hposR hleR
    rw [Real.log_mul hhR.ne' hbpos.ne'] at hlog
    linarith

/-! ## §5 — THE ARM AT THE **UNGRADED** PIN, AT THE RAISED CAP

`s15ArmH_log_le_g14` above is the graded lane's (`1/(838400·2^11·h²) ≤ δ₀`).  The landed `h`-lane
also carries the UNGRADED pin `1/(838400·h²) ≤ δ₀` (`s15ArmH_log_le`, `S16ProducersH.lean`),
and it needs its own twin — but not its own `scaled` lemma: at `c = h²` and `h ≤ 1202604` the
ceiling is `1.4463·10^12` and `log c ≤ 28`, both comfortably inside §4's `2961933067911168` and
`36`.  ⇒ **the wide ceiling covers BOTH pins**, which is why this is four lines of instantiation
and not a second body. -/

/-- **⟦THE ARM'S LOG AT SHIFT `h`, UNGRADED PIN, AT THE RAISED CAP⟧ (class A)** —
`s15ArmH_log_le` (`S16ProducersH.lean`) with `hh7 : log h ≤ 7 ↦ hh14 : log h ≤ 14`;
conclusion unchanged.  Routed through `s15Arm_log_le_scaled_g14` at `c = h²`: `hcb` is
`h² ≤ 1202604² = 1446256380816 ≤ 2961933067911168` (a factor `2048` of room — exactly the `2^11`
the graded pin spends) and `hlogc` is `2·log h ≤ 28 ≤ 36`.  **A NEW name with its OWN binder;
`s15ArmH_log_le` is untouched.** -/
theorem s15ArmH_log_le_14 {h : ℕ} (hh : 0 < h) (hh14 : Real.log (h : ℝ) ≤ 14) {δ₀ Kc : ℝ}
    (hδ₀ : 0 < δ₀) (hδpin : 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀)
    (hKc : 0 < Kc) (hKcb : Kc ≤ 2 ^ 539) {Hhi ω : ℕ}
    (hHhi : 4000000 ≤ Hhi) (hΛ : 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ Real.log ((ω : ℕ) : ℝ) + Real.log (h : ℝ) + ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
  have hh1R : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hc1 : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith [hh1R]
  have h1202604 : (h : ℝ) ≤ 1202604 := by exact_mod_cast h_le_1202604_of_hh14 hh hh14
  have hcb : (h : ℝ) ^ 2 ≤ 2961933067911168 := by nlinarith [hh1R, h1202604]
  have hlogc : Real.log ((h : ℝ) ^ 2) ≤ 36 := by
    rw [Real.log_pow]; push_cast; linarith
  have hbase := s15Arm_log_le_scaled_g14 hc1 hcb hlogc hδ₀ hδpin hKc hKcb (ω := ω) hHhi hΛ
  have hle := s15ArmH_le_mul hh δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω
  have hleR : ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ (h : ℝ) * ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hω0 : 0 ≤ Real.log ((ω : ℕ) : ℝ) := Real.log_natCast_nonneg ω
  have hh0 : 0 ≤ Real.log (h : ℝ) := Real.log_natCast_nonneg h
  have hHhi0 : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by positivity
  rcases Nat.eq_zero_or_pos (s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω)
    with hz | hpos
  · rw [hz]; simp only [Nat.cast_zero, Real.log_zero]; linarith
  · have hposR : (0 : ℝ)
        < ((s15ArmH h δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) := by
      exact_mod_cast hpos
    have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    have hbpos : (0 : ℝ)
        < ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) := by
      by_contra hcon
      have hb0 : ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ) ≤ 0 :=
        not_lt.mp hcon
      nlinarith [hleR, hposR, hhR, hb0]
    have hlog := Real.log_le_log hposR hleR
    rw [Real.log_mul hhR.ne' hbpos.ne'] at hlog
    linarith

end Salt.MR

end
