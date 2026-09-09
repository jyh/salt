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
(`S13CapGateLinearLH.lean:381`) closes `q ≤ h·(log H)^12 ≤ (log X_d)^12` out of
`capfloor_logH_le_half_sqrt` — `log H ≤ √H/2` — which buys exactly `2^12 = 4096` of room in `h`.
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
gives `2^12 = 4096`, and `10⁶ > 4096` by `244×`.  This is the wall that is not a numeral. -/
theorem landed_capgate_refuses_the_million : ¬ ((10 : ℕ) ^ 6 ≤ 4096) := by norm_num

/-- ⛔ **⟦CONTROL — THE COUNT PIN REFUSES THE NEW CAP AT STRIDE 2, EVEN AT ITS LOOSEST READING⟧
(class A)** — the `2^539` count pin (`GoldbachEnergyKcH.lean:226`) carries the witness
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
`h_le_1096_of_hh7` (`S16ProducersH.lean:766`) at the raised cap: `e^14 = 1202604.284…`, so
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
(`capfloor_logH_le_half_sqrt`, `S13CapFloor.lean:110`) gives `4096`; `k = 4` gives `16777216`. -/

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


/-- **⟦THE WINDOW LINE AT `439`⟧ (class A)** — `flat_half_line_g` with `hc : c ≤ 425 ↦ c ≤ 439`.
BODY: verbatim; the closing `linarith [hsq, hE2, hc]` pays `3·14 = 42` more against
`e^{3.2A}/2 ≥ 5·10³³` at `A ≥ 26`.  THE BINDING LINE of the lane, and still free by `10³¹×`. -/
theorem flat_half_line_g14 {A c : ℝ} (hA : 26 ≤ A) (hc : c ≤ 439) :
    (7 / 10 : ℝ) * ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ) + 3 * c
      ≤ Real.exp (3.2 * A) / 2 := by
  have hE17 := flat_exp_half_ge hA
  have hE0 : (0 : ℝ) < Real.exp (3.2 * A / 2) := Real.exp_pos _
  have hMle := flatDoorM_le A
  have hM0 : (0 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := Nat.cast_nonneg _
  have hY := flat_exp_sq A
  have hrow : ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ)
      = 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 := by
    rw [doorRowFloorL, AdoorL]; push_cast; ring
  have h1 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 - ((flatDoorM A : ℕ) : ℝ) := by
    linarith
  have h2 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 + ((flatDoorM A : ℕ) : ℝ) := by
    positivity
  have hsq : ((flatDoorM A : ℕ) : ℝ) ^ 2
      ≤ Real.exp (3.2 * A / 2) ^ 2 / 96286710601 := by
    nlinarith [mul_nonneg h1 h2]
  have hE2 : (10 : ℝ) ^ 34 ≤ Real.exp (3.2 * A / 2) ^ 2 := by nlinarith [hE17, hE0]
  rw [hrow, ← hY]
  linarith [hsq, hE2, hc]

/-- **⟦THE `anchor` LINE AT `439`⟧ (class A)** — `flat_anchor_line_wide_g` with `hc : c ≤ 439`.
BODY: verbatim (`449×` at the landed charge; `+14` against `39·10⁸·M`). -/
theorem flat_anchor_line_wide_g14 {A c : ℝ} (hA : 26 ≤ A) (hc : c ≤ 439) :
    14 * (2 * Real.exp (3.2 * A / 2)) + c + 33
      ≤ 39 * 10 ^ 8 * ((flatDoorM A : ℕ) : ℝ) := by
  have hE17 := flat_exp_half_ge hA
  have hMge := flatDoorM_ge A
  linarith

/-- **⟦THE `𝒯`-LEG BUDGET AT `−439`⟧ (class A)** — `flat_gP1_line_g` with `hc : -439 ≤ c`.
BODY: verbatim (`≈5.5·10³×`). -/
theorem flat_gP1_line_g14 {A c Ct Λ : ℝ} (hA : 26 ≤ A) (hc : -439 ≤ c) (hCt : 0 < Ct)
    (hCtb : Ct ≤ 2 ^ 23) (hΛ : Λ ≤ 2 * Real.exp (3.2 * A / 2)) :
    29 + Real.log Ct + 14 * Λ ≤ ((AdoorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2 + c := by
  have hE17 := flat_exp_half_ge hA
  have hMge := flatDoorM_ge A
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hAdlo : 221460 * Real.exp (3.2 * A / 2) - 68719476737
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) := by linarith
  have hpos : (0 : ℝ) ≤ 221460 * Real.exp (3.2 * A / 2) - 68719476737 := by linarith
  have h1 : (221460 * Real.exp (3.2 * A / 2) - 68719476737) * Real.log 2
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hAdlo (by linarith)
  have hAdlog : 153000 * Real.exp (3.2 * A / 2)
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 := by
    nlinarith [hpos, hlog2lo, hE17]
  have hCtl : Real.log Ct ≤ 23 * Real.log 2 := by
    have h := Real.log_le_log hCt hCtb
    rwa [Real.log_pow] at h
  rw [AdoorL_cast]
  linarith

/-- **⟦THE `level1` BUDGET AT `439`⟧ (class A)** — `flat_lvl_line_g` with `hc : c ≤ 439`.
BODY: verbatim (`457×`). -/
theorem flat_lvl_line_g14 {A c Λ : ℝ} (hA : 26 ≤ A) (hc : c ≤ 439)
    (hΛ : Λ ≤ 2 * Real.exp (3.2 * A / 2)) :
    26 + 14 * Λ
        + (1 / 3) * Real.log (Real.log ((calQK (AdoorL (flatDoorM A))
            (3072 * flatDoorM A) (flatDoorM A) 1 : ℕ) : ℝ)) + c
      ≤ (1 / 12) * ((AdoorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2 := by
  have hE17 := flat_exp_half_ge hA
  have hE0 : (0 : ℝ) < Real.exp (3.2 * A / 2) := Real.exp_pos _
  have hMle := flatDoorM_le A
  have hMge := flatDoorM_ge A
  have hM0 : (0 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hrow : ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ)
      = 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 := by
    rw [doorRowFloorL, AdoorL]; push_cast; ring
  have hAdlo : 221460 * Real.exp (3.2 * A / 2) - 68719476737
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) := by linarith
  have hpos : (0 : ℝ) ≤ 221460 * Real.exp (3.2 * A / 2) - 68719476737 := by linarith
  have h1 : (221460 * Real.exp (3.2 * A / 2) - 68719476737) * Real.log 2
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hAdlo (by linarith)
  have hAdlog : 153000 * Real.exp (3.2 * A / 2)
      ≤ 68719476736 * ((flatDoorM A : ℕ) : ℝ) * Real.log 2 := by
    nlinarith [hpos, hlog2lo, hE17]
  rw [AdoorL_cast, s15_log_calQK_L_one, hrow]
  have hQpos : (0 : ℝ) < 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 * Real.log 2 := by
    have hM1N : 1 ≤ flatDoorM A := flatDoorM_one_le hA
    have hM1 : (1 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := by exact_mod_cast hM1N
    have : (0 : ℝ) < Real.log 2 := by linarith
    positivity
  have hd1 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 - ((flatDoorM A : ℕ) : ℝ) := by
    linarith
  have hd2 : (0 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 + ((flatDoorM A : ℕ) : ℝ) := by
    positivity
  have hsq : ((flatDoorM A : ℕ) : ℝ) ^ 2
      ≤ Real.exp (3.2 * A / 2) ^ 2 / 96286710601 := by
    nlinarith [mul_nonneg hd1 hd2]
  have hQle : 68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 * Real.log 2
      ≤ Real.exp (3.2 * A / 2) ^ 2 := by
    nlinarith [hsq, hlog2hi, sq_nonneg (Real.exp (3.2 * A / 2)), hM0,
      sq_nonneg ((flatDoorM A : ℕ) : ℝ)]
  have hlogQ : Real.log (68719476736 * ((flatDoorM A : ℕ) : ℝ) ^ 2 * Real.log 2)
      ≤ 2 * Real.log (Real.exp (3.2 * A / 2)) := by
    have h := Real.log_le_log hQpos hQle
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlogE : Real.log (Real.exp (3.2 * A / 2)) ≤ Real.exp (3.2 * A / 2) - 1 :=
    Real.log_le_sub_one_of_pos hE0
  have hbud : 12750 * Real.exp (3.2 * A / 2)
      ≤ 1 / 12 * (68719476736 * ((flatDoorM A : ℕ) : ℝ)) * Real.log 2 := by
    linarith [hAdlog]
  linarith [hΛ, hc, hlogQ, hlogE, hbud, hE17]

/-! ## §4 — THE ARM AT THE RAISED `c`-CEILING (`StrideGradeWalls.lean:433`'s twin) -/

set_option maxHeartbeats 2000000 in
-- as `StrideGradeWalls.lean:410` above the landed `s15Arm_log_le_scaled_g`: the arm's four
-- summands, the double exponential's collapse and the closing budget elaborate in one block
/-- **⟦THE ARM, PRICED, AT A `c`-CEILING THAT ADMITS `2^11·h²` FOR `h ≤ 1202604`⟧ (class B)** —
`s15Arm_log_le_scaled_g` with `hcb : c ≤ 2460090368 ↦ c ≤ 2961933067911168`, `hlogc : log c ≤ 22
↦ ≤ 36`; conclusion unchanged, and the lemma is PARAMETRIC IN `c` — it carries no cap binder, so
this re-cut is not a statement act on the `h`-lane.  BODY: `StrideGradeWalls.lean:433-622`
verbatim with TWELVE numeral sites moved in FOUR families (the F5-β docstring says nine in three;
it does not count the `hlogc`/`hρlog` binder pair, which is a family of its own):
  · `hρlog : log(1/ρ) ≤ 425 ↦ ≤ 439` — ONE site (`xt_log_inv_rho_le_scaled` gives `403 + log c`,
    `hlogc` gives `log c ≤ 36`);
  · `2460090368 ↦ 2961933067911168` — FIVE sites: the binder, `hceil1`'s statement, `hdiv`,
    `hpin'`, and `hstep`'s LHS.  ⛔ The last is not optional — with it left landed the closing
    `linarith [hceil1, hceil2, hstep, hmul]` is unclosable;
  · `27 * 10 ^ 16 ↦ 4 * 10 ^ 23` — FIVE sites: `hHhibig`, `hfac`, `h2`, `hstep`'s RHS, `hmul`;
    `128·838400·2961933067911168 = 3.1786·10²³ ≤ 4·10²³` (`1.2584×`), and as a floor on `H₊` it
    has `8.1·10¹⁸×` (`H₊ = u² ≥ (1.8·10²¹)²`);
  · `hlogc : ≤ 22 ↦ ≤ 36` — ONE site.
⛔ THE CONTROL (`landed_ceiling_refuses_the_million`, §0): the landed ceiling fails at `h = 10⁶`
by `832×`, so this re-cut is load-bearing and not a widening for its own sake. -/
theorem s15Arm_log_le_scaled_g14 {c δ₀ Kc : ℝ} (hc1 : 1 ≤ c) (hcb : c ≤ 2961933067911168)
    (hlogc : Real.log c ≤ 36) (hδ₀ : 0 < δ₀) (hδpin : 1 / (838400 * c) ≤ δ₀)
    (hKc : 0 < Kc) (hKcb : Kc ≤ 2 ^ 539) {Hhi ω : ℕ} (hHhi : 4000000 ≤ Hhi)
    (hΛ : 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log ((s15Arm δ₀ (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) Hhi ω : ℕ) : ℝ)
      ≤ Real.log ((ω : ℕ) : ℝ) + ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
  have hc0 : (0 : ℝ) < c := by linarith
  set ρ : ℝ := doorRhoOfDelta (s12DeltaSock δ₀ Kc) with hρdef
  have hδs : 0 < s12DeltaSock δ₀ Kc := s12DeltaSock_pos hδ₀ hKc
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρlog : Real.log (1 / ρ) ≤ 439 :=
    le_trans (xt_log_inv_rho_le_scaled hc1 hδ₀ hδpin hKc hKcb) (by linarith)
  -- ⟦THE SCALES⟧ `L = log H₊`, `Λ = loglog H₊`, and their two exponential witnesses
  set L : ℝ := Real.log ((Hhi : ℕ) : ℝ) with hLdef
  set Λ : ℝ := Real.log L with hΛdef
  have hHhiR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hHhi
  have hHhipos : (0 : ℝ) < ((Hhi : ℕ) : ℝ) := by linarith
  have hL0 : (0 : ℝ) ≤ L := Real.log_nonneg (by linarith)
  have hL1 : (1 : ℝ) < L := one_lt_log_of_loglog_ge hL0 (by norm_num : (0 : ℝ) < 50) hΛ
  have hΛ0 : (0 : ℝ) ≤ Λ := Real.log_nonneg hL1.le
  -- `v := e^{Λ/2}`, so `v² = L` and `v ≥ 6·10^{10}`
  set v : ℝ := Real.exp (Λ / 2) with hvdef
  have hvv : v * v = L := by
    rw [hvdef, ← Real.exp_add, show Λ / 2 + Λ / 2 = Λ by ring, hΛdef]
    exact Real.exp_log (by linarith)
  have hv : (6e10 : ℝ) ≤ v := by
    refine le_trans xt_exp25 ?_
    rw [hvdef]
    exact Real.exp_le_exp.mpr (by linarith)
  have hΛv : Λ ≤ 2 * (v - 1) := by
    have := Real.add_one_le_exp (Λ / 2)
    rw [← hvdef] at this
    linarith
  have hLbig : (3.6e21 : ℝ) ≤ L := by nlinarith [hvv, hv]
  -- `u := e^{L/2}`, so `u² = H₊`
  set u : ℝ := Real.exp (L / 2) with hudef
  have huu : u * u = ((Hhi : ℕ) : ℝ) := by
    rw [hudef, ← Real.exp_add, show L / 2 + L / 2 = L by ring, hLdef]
    exact Real.exp_log hHhipos
  have hLu : L ≤ 2 * (u - 1) := by
    have := Real.add_one_le_exp (L / 2)
    rw [← hudef] at this
    linarith
  have hu : (1.8e21 : ℝ) ≤ u := by linarith
  -- ⟦THE EXPONENT⟧ `E ≤ L/2`
  set E : ℝ := 7000 * Λ + 500 * Real.log (1 / ρ) + 6600 + 36 * 0 with hEdef
  have hE : E ≤ L / 2 := by
    rw [hEdef]
    nlinarith [hρlog, hΛv, hvv, hv]
  have hexpE : Real.exp E ≤ u := by
    rw [hudef]; exact Real.exp_le_exp.mpr hE
  -- ⟦THE ARM, BOUNDED⟧
  have hωnn : (0 : ℝ) ≤ ((ω : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlogωnn : (0 : ℝ) ≤ Real.log ((ω : ℕ) : ℝ) := Real.log_natCast_nonneg ω
  -- the `ρ`-arm's closed form
  have harc : arcDen 12 Hhi = Real.exp (12 * Λ) := by
    rw [arcDen, ← hLdef, Real.rpow_def_of_pos (by linarith), hΛdef]
    congr 1
    ring
  have hG : gArmDoorRho 0 0 ((ω : ℕ) : ℝ) ρ Hhi
      = 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by
    have hsplit : Real.exp (12 * Λ + Real.exp E)
        = Real.exp (12 * Λ) * Real.exp (Real.exp E) := Real.exp_add _ _
    have hnn : (0 : ℝ) ≤ 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ) * Real.exp (Real.exp E) := by
      positivity
    rw [gArmDoorRho, harc, ← hLdef, ← hΛdef, ← hEdef, max_eq_right hnn, hsplit]
    ring
  -- the sum, cast
  have hcast : ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
      = 2 * ((ω : ℕ) : ℝ) * (((Hhi : ℕ) : ℝ) + 2) + 8 * ((ω : ℕ) : ℝ)
        + ((⌈128 * ((ω : ℕ) : ℝ) / δ₀⌉₊ : ℕ) : ℝ)
        + ((⌈gArmDoorRho 0 0 ((ω : ℕ) : ℝ) ρ Hhi⌉₊ : ℕ) : ℝ) := by
    rw [s15Arm, s13GArm']
    push_cast
    ring
  have hceil1 : ((⌈128 * ((ω : ℕ) : ℝ) / δ₀⌉₊ : ℕ) : ℝ)
      ≤ 128 * 838400 * 2961933067911168 * ((ω : ℕ) : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ 128 * ((ω : ℕ) : ℝ) / δ₀ := by positivity
    have hlt : ((⌈128 * ((ω : ℕ) : ℝ) / δ₀⌉₊ : ℕ) : ℝ) < 128 * ((ω : ℕ) : ℝ) / δ₀ + 1 :=
      Nat.ceil_lt_add_one h0
    have hdiv : 128 * ((ω : ℕ) : ℝ) / δ₀ ≤ 128 * 838400 * 2961933067911168 * ((ω : ℕ) : ℝ) := by
      rw [div_le_iff₀ hδ₀]
      have hpin' : 1 / (838400 * 2961933067911168 : ℝ) ≤ δ₀ := by
        refine le_trans ?_ hδpin
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [hcb, hc0]
      nlinarith [hωnn, hpin']
    linarith
  have hceil2 : ((⌈gArmDoorRho 0 0 ((ω : ℕ) : ℝ) ρ Hhi⌉₊ : ℕ) : ℝ)
      ≤ 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) + 1 := by
    rw [hG]
    have h0 : (0 : ℝ) ≤ 16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by positivity
    linarith [Nat.ceil_lt_add_one h0]
  -- ⟦THE ENVELOPE⟧ `S ≤ (ω+1)·e^Y` at `Y = L + 12λ + e^E + 6`
  have hX1 : (1 : ℝ) ≤ Real.exp (12 * Λ + Real.exp E) :=
    Real.one_le_exp (by positivity)
  have hHhibig : (4 * 10 ^ 23 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by nlinarith [huu, hu]
  have he6 : (19 : ℝ) ≤ Real.exp 6 := by
    have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h : Real.exp (6 : ℝ) = (Real.exp 1) ^ (6 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    have hc : (2.7 : ℝ) ^ (6 : ℕ) ≤ (Real.exp 1) ^ (6 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he1.le 6
    have hn : (19 : ℝ) ≤ (2.7 : ℝ) ^ (6 : ℕ) := by norm_num
    linarith
  have hYeq : Real.exp (L + (12 * Λ + Real.exp E) + 6)
      = ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) * Real.exp 6 := by
    rw [Real.exp_add, Real.exp_add, hLdef, Real.exp_log hHhipos]
  have henv : ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
      ≤ (((ω : ℕ) : ℝ) + 1) * Real.exp (L + (12 * Λ + Real.exp E) + 6) := by
    rw [hcast, hYeq]
    have hfac : 2 * ((Hhi : ℕ) : ℝ) + 4 * 10 ^ 23
          + 16 * Real.exp (12 * Λ + Real.exp E)
        ≤ ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) * Real.exp 6 := by
      have h1 : 2 * ((Hhi : ℕ) : ℝ)
          ≤ 2 * (((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E)) := by
        nlinarith [hX1, hHhiR]
      have h2 : (4 * 10 ^ 23 : ℝ)
          ≤ ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by
        nlinarith [hX1, hHhibig]
      have h3 : 16 * Real.exp (12 * Λ + Real.exp E)
          ≤ 16 * (((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E)) := by
        nlinarith [hX1, hHhiR, Real.exp_pos (12 * Λ + Real.exp E)]
      have hprodnn : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) := by positivity
      nlinarith [h1, h2, h3, he6, hprodnn]
    have hstep : 2 * ((ω : ℕ) : ℝ) * (((Hhi : ℕ) : ℝ) + 2) + 8 * ((ω : ℕ) : ℝ)
        + (128 * 838400 * 2961933067911168 * ((ω : ℕ) : ℝ) + 1)
        + (16 * ((ω : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) + 1)
        ≤ (((ω : ℕ) : ℝ) + 1) * (2 * ((Hhi : ℕ) : ℝ) + 4 * 10 ^ 23
            + 16 * Real.exp (12 * Λ + Real.exp E)) := by
      nlinarith [hωnn, hX1, hHhiR, Real.exp_pos (12 * Λ + Real.exp E)]
    have hmul : (((ω : ℕ) : ℝ) + 1) * (2 * ((Hhi : ℕ) : ℝ) + 4 * 10 ^ 23
          + 16 * Real.exp (12 * Λ + Real.exp E))
        ≤ (((ω : ℕ) : ℝ) + 1)
          * (((Hhi : ℕ) : ℝ) * Real.exp (12 * Λ + Real.exp E) * Real.exp 6) :=
      mul_le_mul_of_nonneg_left hfac (by linarith)
    linarith [hceil1, hceil2, hstep, hmul]
  -- ⟦THE LOG⟧
  rcases Nat.eq_zero_or_pos (s15Arm δ₀ ρ Hhi ω) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    have : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by positivity
    linarith
  · have hSpos : (0 : ℝ) < ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ) := by exact_mod_cast hpos
    have hlog := Real.log_le_log hSpos henv
    have hprod : Real.log ((((ω : ℕ) : ℝ) + 1) * Real.exp (L + (12 * Λ + Real.exp E) + 6))
        = Real.log (((ω : ℕ) : ℝ) + 1) + (L + (12 * Λ + Real.exp E) + 6) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
    -- `log(ω+1) ≤ log ω + log 2`
    have hω1 : Real.log (((ω : ℕ) : ℝ) + 1) ≤ Real.log ((ω : ℕ) : ℝ) + Real.log 2 := by
      rcases Nat.eq_zero_or_pos ω with hz | hz
      · rw [hz]
        simp only [Nat.cast_zero, Real.log_zero, zero_add, Real.log_one]
        linarith [Real.log_two_gt_d9]
      · have hω1R : (1 : ℝ) ≤ ((ω : ℕ) : ℝ) := by exact_mod_cast hz
        have hle : ((ω : ℕ) : ℝ) + 1 ≤ 2 * ((ω : ℕ) : ℝ) := by linarith
        have h := Real.log_le_log (by linarith : (0 : ℝ) < ((ω : ℕ) : ℝ) + 1) hle
        rwa [Real.log_mul (by norm_num) (by linarith), add_comm (Real.log 2)] at h
    -- the closing budget
    have hΛL : Λ ≤ L := by nlinarith [hΛv, hvv, hv]
    have hclose : Real.log 2 + (L + (12 * Λ + Real.exp E) + 6)
        ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
      -- ⟦THE TOWER STEP⟧ `u = e^{L/2} = (e^{L/4})² ≥ (1 + L/4)²`, so with `L ≥ 3.6·10^21`
      -- the linear witness `u ≥ 1.8·10^21` is upgraded to `u ≥ 8.1·10^41` — which is what
      -- buys the deeper cut `H₊/10^20` in place of `H₊/10^6`.  The headroom here is a TOWER
      -- (`XCeilGate` carries `50 ≤ loglog H₊`), so the extra fourteen orders are free.
      have hq := Real.add_one_le_exp (L / 4)
      have hq0 : (0 : ℝ) ≤ Real.exp (L / 4) := (Real.exp_pos _).le
      have hqL : (9 * 10 ^ 20 : ℝ) ≤ Real.exp (L / 4) := by linarith only [hq, hLbig]
      have hsq : Real.exp (L / 4) * Real.exp (L / 4) = u := by
        rw [← Real.exp_add, show L / 4 + L / 4 = L / 2 by ring, hudef]
      have hu41 : (8 * 10 ^ 41 : ℝ) ≤ u := by
        rw [← hsq]
        calc (8 * 10 ^ 41 : ℝ) ≤ (9 * 10 ^ 20) * (9 * 10 ^ 20) := by norm_num
          _ ≤ Real.exp (L / 4) * Real.exp (L / 4) :=
              mul_le_mul hqL hqL (by norm_num) hq0
      -- keep every step LINEAR in `u`: the one product is isolated in `hsquare`.
      have hupos : (0 : ℝ) < u := by linarith only [hu41]
      have hlin : L + 12 * Λ + Real.exp E + 6.7 ≤ 27 * u := by
        linarith only [hexpE, hΛL, hLu]
      have h27 : (27 : ℝ) * 10 ^ 20 ≤ u := by linarith only [hu41]
      have hsquare : 27 * u * 10 ^ 20 ≤ u * u := by
        have hm := mul_le_mul_of_nonneg_right h27 hupos.le
        linarith only [hm]
      have hstep : L + 12 * Λ + Real.exp E + 6.7 ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
        rw [← huu, le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 20)]
        linarith only [hlin, hsquare]
      linarith [Real.log_two_lt_d9]
    linarith [hlog, hprod, hω1, hclose]

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

end Salt.MR

end
