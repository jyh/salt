/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S13CapFloor

/-!
# V7-A `KS-TRACE` — the `Ks` rider of `logChowla2_ineffective_v6`, traced and re-sized

`RegisterCompose.logChowla2_ineffective_v6` (:345-364) carries the inner rider
`e^{-100} ≤ Ks` on a constant its own `∃`-prefix mints.  `RiderTrace` did this job for `cs`
and `T₀`; this file does it for `Ks`.  **PURELY ADDITIVE** — no landed declaration is touched.

## §A THE TRACE (what `Ks` IS)

`Ks` travels to `v6` untouched through nine pass-throughs and is minted at ONE site:

```
PortAssembly.siegel_real_carve (:1180)      K  := min (min Cs (c₀/32)) (1/2)
  → NumeralKq.twisted_rect_zero_free_siegel_bounded (:502)   Ks := 10^8 · K
  → NumeralKq.usetGChi_window_meansq_gated_family_perBlock_bounded (:775)   pass-through
  → NumeralKq.m4_rowChi_capstone_perBlock_bounded (:958)                    pass-through
  → RegisterCompose.m4_hcap_at_door_perBlock_L_gk_bounded_khoist (:52)      pass-through
  → RegisterCompose.m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist (:117)        pass-through
  → RegisterCompose.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist (:164) pass-through
  → RegisterCompose.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist (:209)
  → RegisterCompose.logChowla2_ineffective_v6 (:345)
```

So `Ks = 10^8 · min(min(Cs, c₀/32), 1/2)` at its two leaves:

* `c₀` — `Salt.SW.zero_free_region_all'` (`SW/ZeroFreeReal.lean:642`), the classical
  imprimitive region.  **EFFECTIVE**: the bounded twin `NumeralKq.zero_free_region_all'_bounded`
  (:450) pins `1/126848 ≤ c₀`, so this leg gives `c₀/32 ≥ 2.46·10^{-7}`, and `1/2` is a
  literal.  Neither of these two legs can bind the rider.
* `Cs` — the constant of `Salt.SW.siegel_theorem (1/16)` (`SW/SiegelClose.lean:841`), whose own
  docstring reads *"there is an (ineffective) `C > 0`"*.  Its `∃`-prefix exports `0 < C` and
  nothing else.

⟦THE VERDICT⟧ `e^{-100} ≤ Ks` reduces EXACTLY to `Cs ≥ e^{-100}/10^8 ≈ 3.72·10^{-52}`, i.e. to
an explicit numerical lower bound on Siegel's constant at `ε = 1/16`.  That is the Siegel-zero
ineffectivity itself: the corpus exports no such bound, and none is available in the literature
(`PortAssembly` §7 states why the port cannot route around it — the arc's `q ≤ (log x)^{12}`
forces `ε = 1/16`, and an effective Page-type `q^{-1/2}` loses by `(log H)^{5.25}`).
**The rider is NOT provable as stated, and this file does not claim it.**

## §B THE RE-SIZING (what the socket actually needs)

The numeral is SPENT at exactly ONE place — `S13CapFloor.capfloor_floor4` (:449), the `floor4`
field of `S13FramesB.S13CapGatePerBlock`; the two bundles (`s13CapFloor_all` :649,
`s13CapFloor_all_gk` :733) only pass it through.  And `S13CapFloor`'s own header (:60-62) already
names the sharp form: `Ks ≥ e^{-3v/16}` with `v = log H ≥ 10^{21}`.

`capfloor_floor4_sharp` below pins that sharp form in the kernel — the exact analogue of the
landed `capfloor_T0_Tann_sharp` (`S13CapFloor:226`) for the `T₀` rider.  `ks_sharp_of_rider`
carries the certificate in the R1 direction: the landed rider IMPLIES the sharp one at the
working point, so `capfloor_floor4_of_sharp` re-derives the landed statement verbatim.  The
sharp rider is weaker by `e^{3·10^{21}/16 - 100}`.

⟦WHY THIS DISCHARGES⟧ unlike `e^{-100} ≤ Ks`, the sharp rider is **`A`-windowed**: it carries no
numeral and is met by ANY `Ks > 0` once the design base clears `1/Ks` (`ks_rider_absorbed`).
The terminal mints `Ks` at `RegisterCompose:242` and chooses its design constant `A` at `:246`
— i.e. `A` is chosen AFTER `Ks` — so `capfloor_floor4_of_design` is dischargeable at the
terminal against `v6`'s own exported conjunct `3.2·A ≤ loglog R.Hlo`, with no lower bound on
Siegel's constant anywhere.  Rethreading the sharp form through the hops that carry the rider is
V7-E's landing, not this node's; V7-A supplies the leaf it lands on.
-/

noncomputable section
open scoped BigOperators
namespace Salt.MR
open Salt.Entropy.Chowla

/-! ### §1 — the elementary window lemma -/

/-- `e^{-x} ≤ c` for `c > 0` as soon as `log(1/c) ≤ x`: the one-line absorption that turns a
POSITIVE constant into a floor rider with no numeral in it. -/
theorem exp_neg_le_of_log_inv_le {x c : ℝ} (hc : 0 < c) (h : Real.log (1 / c) ≤ x) :
    Real.exp (-x) ≤ c := by
  have hlog : Real.log (1 / c) = -Real.log c := by rw [one_div, Real.log_inv]
  rw [hlog] at h
  have hstep : Real.exp (-x) ≤ Real.exp (Real.log c) := Real.exp_le_exp.mpr (by linarith)
  rwa [Real.exp_log hc] at hstep

/-- **⟦THE ABSORPTION⟧** for EVERY `Ks > 0` there is a design floor past which the windowed
rider `e^{-3v/16} ≤ Ks` holds — no numeral, no lower bound on Siegel's constant.  This is the
whole content of the V7-A discharge route in one statement. -/
theorem ks_rider_absorbed {Ks : ℝ} (hKs : 0 < Ks) :
    ∃ v₀ : ℝ, 0 < v₀ ∧ ∀ v : ℝ, v₀ ≤ v → Real.exp (-(3 * v / 16)) ≤ Ks := by
  refine ⟨max 1 (16 * Real.log (1 / Ks) / 3), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro v hv
  refine exp_neg_le_of_log_inv_le hKs ?_
  have h : 16 * Real.log (1 / Ks) / 3 ≤ v := le_trans (le_max_right _ _) hv
  linarith

/-! ### §2 — `floor4`, SHARP -/

/-- **⟦`floor4`, SHARP⟧** the `Ks` arm of `S13CapGatePerBlock` (`S13FramesB:1018`) from the
socket's TRUE demand `Ks ≥ e^{-3v/16}`, `v = log H` — the analogue of `capfloor_T0_Tann_sharp`
for the `Ks` rider.  The proof pays `q^{1/16} ≤ v^{3/4} ≤ v` against
`Ks·μ^{3/4}·Λ^4 ≥ e^{-3v/16}·e^{3v/16}·(v/4)^4 = v^4/256 ≥ v`. -/
theorem capfloor_floor4_sharp {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hKs : Real.exp (-(3 * Real.log (H : ℝ) / 16)) ≤ Ks) :
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core hfl hb hAN hTlo
  obtain ⟨hμ, hΛ⟩ := capfloor_muLambda hfl hb hAN hTlo
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le h21 hv
  have hv256 : (256 : ℝ) ≤ Real.log (H : ℝ) := le_trans (by norm_num) hv
  -- ⟦LHS⟧ `q^{1/16} ≤ v^{3/4} ≤ v` (the modulus range `q ≤ arcDen 12 H`)
  have hqA : (q : ℝ) ≤ Real.log (H : ℝ) ^ (12 : ℕ) := by
    have h := hb.2.2.2.2.1
    have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
      rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [harcpow] at h
  have hstep1 : (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ (Real.log (H : ℝ) ^ (12 : ℕ)) ^ ((1 : ℝ) / 16) :=
    Real.rpow_le_rpow (Nat.cast_nonneg q) hqA (by norm_num)
  have hstep2 : (Real.log (H : ℝ) ^ (12 : ℕ)) ^ ((1 : ℝ) / 16)
      = Real.log (H : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_natCast (Real.log (H : ℝ)) 12, ← Real.rpow_mul hv0.le]
    norm_num
  have hv1 : (1 : ℝ) ≤ Real.log (H : ℝ) := by linarith
  have hstep3 : Real.log (H : ℝ) ^ ((3 : ℝ) / 4) ≤ Real.log (H : ℝ) := by
    calc Real.log (H : ℝ) ^ ((3 : ℝ) / 4) ≤ Real.log (H : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
      _ = Real.log (H : ℝ) := Real.rpow_one _
  have hLHS : (q : ℝ) ^ ((1 : ℝ) / 16) ≤ Real.log (H : ℝ) := by
    rw [hstep2] at hstep1; linarith
  -- ⟦RHS leg 1⟧ `e^{3v/16} ≤ μ^{3/4}` — the FULL exponential, not `capfloor_rhs_legs`' `e^{300}`
  have hleg1 : Real.exp (3 * Real.log (H : ℝ) / 16)
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4) := by
    have hstep : (Real.exp (Real.log (H : ℝ) / 4)) ^ ((3 : ℝ) / 4)
        ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (Real.exp_nonneg _) hμ (by norm_num)
    have heq : (Real.exp (Real.log (H : ℝ) / 4)) ^ ((3 : ℝ) / 4)
        = Real.exp (Real.log (H : ℝ) / 4 * (3 / 4)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [heq] at hstep
    refine le_trans (Real.exp_le_exp.mpr ?_) hstep
    linarith
  -- ⟦RHS leg 2⟧ `(v/4)^4 ≤ Λ^4`
  have hleg2 : (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
      ≤ (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hΛ 4
  have hexp0 : (0 : ℝ) < Real.exp (3 * Real.log (H : ℝ) / 16) := Real.exp_pos _
  have hlegs : Real.exp (3 * Real.log (H : ℝ) / 16) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) :=
    mul_le_mul hleg1 hleg2 (by positivity) (le_trans hexp0.le hleg1)
  -- ⟦the cancellation⟧ `Ks·e^{3v/16} ≥ 1`
  have hKs0 : (0 : ℝ) < Ks := lt_of_lt_of_le (Real.exp_pos _) hKs
  have hcancel : (1 : ℝ) ≤ Ks * Real.exp (3 * Real.log (H : ℝ) / 16) := by
    have hprod : Real.exp (-(3 * Real.log (H : ℝ) / 16))
        * Real.exp (3 * Real.log (H : ℝ) / 16) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [mul_le_mul_of_nonneg_right hKs hexp0.le, hprod]
  -- ⟦assemble⟧ `v ≤ v^4/256 ≤ (Ks·e^{3v/16})·(v/4)^4 ≤ Ks·(μ^{3/4}·Λ^4)`
  have hpow : (256 : ℝ) ≤ Real.log (H : ℝ) ^ (3 : ℕ) := by
    have hid : Real.log (H : ℝ) ^ (3 : ℕ)
        = Real.log (H : ℝ) * (Real.log (H : ℝ) * Real.log (H : ℝ)) := by ring
    rw [hid]; nlinarith [hv256]
  have hvq : Real.log (H : ℝ) ≤ (Real.log (H : ℝ) / 4) ^ (4 : ℕ) := by
    have hid : (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
        = Real.log (H : ℝ) * (Real.log (H : ℝ) ^ (3 : ℕ) / 256) := by ring
    rw [hid]; nlinarith [hpow, hv0]
  have hbase : (0 : ℝ) ≤ (Real.log (H : ℝ) / 4) ^ (4 : ℕ) := by positivity
  have hgrow : (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
      ≤ Ks * Real.exp (3 * Real.log (H : ℝ) / 16) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ) := by
    nlinarith [hcancel, hbase]
  have hfinal : Ks * (Real.exp (3 * Real.log (H : ℝ) / 16) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ))
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) :=
    mul_le_mul_of_nonneg_left hlegs hKs0.le
  have hassoc : Ks * (Real.exp (3 * Real.log (H : ℝ) / 16) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ))
      = Ks * Real.exp (3 * Real.log (H : ℝ) / 16) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ) := by
    ring
  rw [hassoc] at hfinal
  linarith [hLHS, hvq, hgrow, hfinal]

/-! ### §3 — the certificate: the landed rider IMPLIES the sharp one -/

/-- **⟦R1 CERTIFICATE⟧** at the socket's working point the landed rider `e^{-100} ≤ Ks` implies
the sharp rider `e^{-3v/16} ≤ Ks`, because `3v/16 ≥ 1.875·10^{20} ≥ 100`.  The implication is
STRICT by `e^{3·10^{21}/16 - 100}`: the landed numeral is over-strong by that factor. -/
theorem ks_sharp_of_rider {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hKs : Real.exp (-100) ≤ Ks) :
    Real.exp (-(3 * Real.log (H : ℝ) / 16)) ≤ Ks := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core hfl hb hAN hTlo
  have h533 : (533 : ℝ) ≤ Real.log (H : ℝ) := le_trans (by norm_num) hv
  exact le_trans (Real.exp_le_exp.mpr (by linarith)) hKs

/-- **⟦NO TRADE⟧** `S13CapFloor.capfloor_floor4` (:449) re-derived from the sharp sibling:
the sharp form subsumes the landed one, so nothing is given up by rethreading it. -/
theorem capfloor_floor4_of_sharp {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hKs : Real.exp (-100) ≤ Ks) :
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) :=
  capfloor_floor4_sharp hfl hb hAN hTlo (ks_sharp_of_rider hfl hb hAN hTlo hKs)

/-! ### §4 — the discharge: `floor4` from `0 < Ks` alone, windowed by the design constant -/

/-- **⟦`floor4` FROM POSITIVITY⟧** the `Ks` arm with NO numeral rider: `0 < Ks` plus the window
`log(1/Ks) ≤ 3·log H/16`.  Every `Ks > 0` meets the window at a large enough design base
(`ks_rider_absorbed`), so this form carries no ineffective content out of the port. -/
theorem capfloor_floor4_of_pos {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hKs0 : 0 < Ks) (hwin : Real.log (1 / Ks) ≤ 3 * Real.log (H : ℝ) / 16) :
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) :=
  capfloor_floor4_sharp hfl hb hAN hTlo (exp_neg_le_of_log_inv_le hKs0 hwin)

/-- **⟦THE V7-E LEAF⟧** the `Ks` arm discharged against the terminal's OWN design conjunct.
`logChowla2_ineffective_v6` exports `3.2·A ≤ loglog R.Hlo` (`RegisterCompose:357`) and mints
`Ks` (`:242`) BEFORE it chooses `A` (`:246`) — so a terminal may put
`log(1/Ks) ≤ 3·e^{3.2·A}/16` into its own `max` for `A` and read `floor4` off with no rider at
all.  The Siegel constant is then carried by name, never by numeral. -/
theorem capfloor_floor4_of_design {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Ks Tann Ad : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hKs0 : 0 < Ks)
    (hdes : 3.2 * Ad ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (hAwin : Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * Ad) / 16) :
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hHloR : (4000000 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast R.hHlo_floor
  have hlogHlo0 : (0 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hdes' : Real.exp (3.2 * Ad) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    have h := Real.exp_le_exp.mpr hdes
    rwa [Real.exp_log hlogHlo0] at h
  have hloR : ((R.Hlo : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo
  have hmono : Real.log ((R.Hlo : ℕ) : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hloR
  exact capfloor_floor4_of_pos hfl hb hAN hTlo hKs0 (by linarith)

end Salt.MR
