/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey
-/
import Salt.MR.S13CapGrid
import Salt.MR.S13CapFloor
import Salt.MR.S13CapEps
import Salt.MR.S13CapRbd
import Salt.MR.S12FuseCompose
import Salt.MR.S15Compose
import Salt.MR.S15Witness

/-!
# `S16Budget` — the `budget` field, the cap-gate supply, and the crossing bound

⟦THE LAST WIRE⟧ this file discharges `S15Compose.S15CrossingBound_gk` — the ONE surviving
supply object of `S15Witness.logChowla2_conditional_sharp2_nonvacuous_gk` — through the
per-block cap bundle, and composes the result with the sharp2 witness.

## §0 — ⟦THE BUDGET's HONEST DEMAND⟧ (and a correction to the width law)

`S13FramesB.S13CapGatePerBlock_gk.budget` asks, at every ram block `i`,

  `|I₂| · 1680 · VJ² · exp(2·(log S / log 𝒫₂)·loglog S) · X_d^{1−2η+ε_d} ≤ Mr X_d i`

at `S = q·T_ann`, `η = 5/48`, `Mr X_d i = ⌈2X_d e^{−i/H₈₃}⌉₊`.  Dividing by `X_d^{1−2η}` and
taking logs, the binding content is

  `2·(log S/log 𝒫₂)·loglog S ≤ 2η·log X_d − i/H₈₃ − …`,

and since `log S ≤ log X_d + 12 loglog X_d` (the socket's own `q ≤ μ^{12}`, `T_ann ≤ X_d`)
while `i/H₈₃ ≤ log Q ≤ μ/Λ`, this reduces to

  **`loglog X_d ≤ (5/48)·log 𝒫₂`**  —  a `loglog`, not a `log`.

⚠ **⟦ERRATUM, RETRACTED IN FULL — corrected per REF-FINAL-HONEST⟧** an earlier revision of
this header claimed the width law was "one log too strong", reading the socket's floor for
`loglog X_d` off `ERR-REF`'s arm bound `≈ 7000·λ₊` and concluding that the width wall never
existed at the budget leg.  **That retraction was itself the misread.**  This file's own
supplier chain proves the SHARP floor `s13CapGrid.s13CapGrid_Lambda_sharp`:

  `½·log H ≤ loglog X_d`   at every socket base,

so at `H = H₊` the floor is `e^{λ₊}/2`, not `7000·λ₊` — `LAMBDA-RECON`'s original reading was
right to within `log 2`.  **THE WIDTH WALL IS REAL at the budget leg**, the G-lever campaign
was correctly fired, and the cap below is a genuine constraint on `λ₊`, not a formality.
⟦THE LAW⟧ when two lower bounds compete, the reduction must be probed at the STRONGER one.

⟦WHAT THE CAP THEN DEMANDS OF THE LEVER⟧ `S16BaseScaleCap_gk` + the sharp floor cap `λ₊` by
`log(log 𝒫₂) − log 12`; the tower `λ₋³ ≤ λ₊` (`WIDTH-SCOPE`, standing) therefore forces

  `λ₋³ ≤ log (log 𝒫₂) = (K + 413.06)·log 2 + log log 2`.

At the sharp2 witness (`M = 2^355`, `λ₋ = 277.2589`, `λ₋³ = 2.1314·10^7`) that is
`K ≥ 3.075·10^7` — INSIDE the frame's own ceiling `1.7·10^8`, and 61.5× ABOVE the pin
`K = 500000` the landed terminal used.  §6 re-pins at `K = 3.2·10^7` and certifies the
demand met in the kernel (`s16_recut_cap_demand_met`, 4.07% of room).

## §1–§2 — the shape stones and the field

`s16_budget_field_gk` proves `budget` verbatim from the grid wave's own supplied fields
(`logX_eight`, `q_logX`, `Q_pos`, `Q_high`, `Q2_reg`, `Λ ≥ 10^21`) plus ONE new hypothesis:

  `hcap : loglog X_d ≤ log 𝒫₂ / 24`   (`S16BaseScaleCap_gk`),

a cap on the SOCKET's base scale.  It is not derivable from the compose: `SocketBase` pins
`X_d = A + s` to `R.x`-scale (`A ≤ 2R.x`, `R.x ≤ 16ω(log H)^{12}A`) and `ChowlaRegime` bounds
`R.x` only from BELOW (`hheadroom : Hhi ≤ x/ω`).  So it is carried, named, at `/24` — a
`1.5×` margin over what `s16_budget_num` actually spends (corrected per REF-FINAL-HONEST;
the earlier `2.4×` read the `(5/48)` prose demand, not the proof's own line).

## §3 — the cap gate

`s16_capGate_supply_gk` delivers all 37 fields of `S13CapGatePerBlock_gk` at every socket:
18 from `s13CapGrid_all_gk`, 7 from `s13CapFloor_all_gk`, 7 from `s13CapEps_all` (K-free by
the map; its `hP83`/`hgrade` from `s13CapEps_pins_supply` at the grid's own `⌈P₈₃⌉₊`/`⌊Q₈₃⌋₊`),
`budget` from §2, and the four co-factor fields from `S16CofactorSupply_gk` — ⟦RULING 9⟧'s
posture, carried named.  (`S13CapRbd.s13CapRbd_all_gk` is that predicate's supplier from the
31 wide-supply gates plus the two shelved lines `Rbd_grade`/`Cq_gate`; wiring it here would
move the debt, not discharge it, so the predicate is carried at the four fields directly.)

## §4–§5 — the crossing bound and the final object

`s15_crossing_supplied_gk` runs the gate family through `doorCapBundle_at_workingPoint_
perBlock_gk` and `m4_fuse_hcap_of_capWS_gk` at `cU := liouvilleC`, `ε ≡ θ₂₉₃ − 1/500`, and
lands `S15CrossingBound_gk K R M`.  `logChowla2_witnessed_scale_final` composes it with
`logChowla2_conditional_sharp2_nonvacuous_gk`.  ⟦THE SURVIVOR LIST, EXACT⟧ the twin's eight
numeral bounds, INCLUDING `hx0win` (Siegel, undischargeable — corrected per
REF-FINAL-HONEST: it is one of the eight, not a ninth); the five constant riders `1 ≤ cs`,
`T₀ ≤ e^{e^{100}}`, `Kq ≤ e^{100}`, `e^{−100} ≤ Ks`, `log C ≤ 40` on the fuse's and the band
lemma's own constants; `S16CofactorSupply_gk` (⟦RULING 9⟧'s shelved debt); and
`S16BaseScaleCap_gk` (§2's base-scale cap).  Nothing else, and nothing hidden.

**PURELY ADDITIVE.**  No landed declaration is touched. -/

open Salt.Entropy.Chowla

namespace Salt.MR

open Real



theorem s16_calE_two (A G : ℕ) : calE A G 2 = 4 * (A * G) := by
  rw [calE]; simp [Nat.factorial]; ring

theorem s16_logP2 (A G : ℕ) :
    Real.log ((calP A G 2 : ℕ) : ℝ) = ((4 * (A * G) : ℕ) : ℝ) * Real.log 2 := by
  rw [calP, s16_calE_two]
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

theorem s16_logQK2 (A G M : ℕ) :
    Real.log ((calQK A G M 2 : ℕ) : ℝ)
      = ((4 * M : ℕ) : ℝ) * Real.log ((calP A G 2 : ℕ) : ℝ) := by
  rw [calQK, s16_logP2, s16_calE_two]
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

theorem s16_logP1 (A G : ℕ) :
    Real.log ((calP A G 1 : ℕ) : ℝ) = (A : ℝ) * Real.log 2 := by
  rw [calP, calE_one]
  push_cast
  rw [Real.log_pow]

theorem s16_calH_two (H1 : ℝ) : calH H1 2 = 4 * H1 := by
  rw [calH]; norm_num

/-- `log(𝒫₁) ≤ log(𝒫₂)/12288` — the level-1 base against the levered level-2 base. -/
theorem s16_logP1_le_logP2 (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
      ≤ Real.log ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) / 12288 := by
  rw [s16_logP1, s16_logP2]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hG : 3072 ≤ s13GK K M := by
    rw [s13GK]
    have h2 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    calc 3072 = 3072 * 1 * 1 := by ring
      _ ≤ 3072 * 2 ^ K * M := by exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) hM
  have hA : (1 : ℝ) ≤ (Adoor M : ℝ) := by
    have := Adoor_ge M
    have h : (1 : ℕ) ≤ Adoor M := le_trans (by norm_num) this
    exact_mod_cast h
  have hGr : (3072 : ℝ) ≤ ((s13GK K M : ℕ) : ℝ) := by exact_mod_cast hG
  rw [le_div_iff₀ (by norm_num)]
  push_cast
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * ((s13GK K M : ℕ) : ℝ) - 12288)
    (mul_nonneg (by linarith : (0 : ℝ) ≤ ((Adoor M : ℕ) : ℝ)) hlog2.le)]

/-- `log(H₂) ≤ 2 + log(𝒫₂)/73728` where `H₂ = calH (H1door M) 2`. -/
theorem s16_logH2_le (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    Real.log (calH (H1door M) 2)
      ≤ 2 + Real.log ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) / 73728 := by
  have h2 : (2 : ℝ) ≤ H1door M := H1door_two hM
  have hpin := H1door_pin hM
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    have := calP_door_one_ge M; linarith
  have hcube : (0 : ℝ) < (H1door M) ^ 3 := by positivity
  have hmono := Real.log_le_log hcube hpin
  rw [Real.log_pow, Real.log_rpow hP0] at hmono
  have hlog1 : Real.log (H1door M)
      ≤ Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) / 6 := by linarith
  have hle := s16_logP1_le_logP2 K hM
  rw [s16_calH_two, Real.log_mul (by norm_num) (by linarith)]
  have hlog4 : Real.log 4 ≤ 2 := by
    have : (4 : ℝ) ≤ Real.exp 2 := by
      have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h2 : Real.exp 2 = (Real.exp 1) ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      rw [h2]; nlinarith [Real.exp_pos 1]
    calc Real.log 4 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) this
      _ = 2 := Real.log_exp 2
  linarith


/-! main assembly -/

theorem s16_budget_num {μ Λ Lp Lq lS llS lq : ℝ}
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Λ) (hμΛ : Real.log μ = Λ) (hμ : 0 < μ)
    (hLp0 : 0 < Lp) (hLpq : 4 * Lp ≤ Lq) (hLq : Lq ≤ Real.sqrt μ)
    (hcap : Λ ≤ Lp / 24)
    (hlq : lq ≤ 12 * Λ)
    (hlS0 : 0 < lS) (hlS : lS ≤ μ + 12 * Λ) (hllS : llS ≤ Λ + 1) :
    16 + Lp / 73728 + Λ / 2 + (7 / 24) * Lq + 2 * (lS / Lp) * llS + (7 / 24) * lq + μ / Λ
      ≤ (5 / 24) * μ := by
  have hΛ0 : (0 : ℝ) < Λ := by nlinarith
  have hexp : Real.exp Λ = μ := by rw [← hμΛ]; exact Real.exp_log hμ
  have hμbig : (10 : ℝ) ^ (21 : ℕ) ≤ μ := by
    have := Real.add_one_le_exp Λ
    rw [hexp] at this
    linarith
  have hsq : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ.le
  have hsq0 : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hsq10 : (10 : ℝ) ^ (10 : ℕ) ≤ Real.sqrt μ := by nlinarith [hsq, hμbig, hsq0]
  have hsqle : Real.sqrt μ ≤ μ / 10 ^ (10 : ℕ) := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hsq, hsq10, hsq0]
  have hLple : Lp ≤ μ / (4 * 10 ^ (10 : ℕ)) := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hLpq, hLq, hsqle]
  have hΛle : Λ ≤ μ / (96 * 10 ^ (10 : ℕ)) := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hcap, hLple]
  have hmain : 2 * (lS / Lp) * llS ≤ μ / 8 := by
    have hkey : 2 * lS * llS ≤ (μ / 8) * Lp := by
      have h24 : 24 * Λ ≤ Lp := by linarith
      nlinarith [hlS, hllS, hlS0.le, hΛ0, hμbig, hΛle, h24, hμ]
    have : 2 * (lS / Lp) * llS = (2 * lS * llS) / Lp := by field_simp
    rw [this, div_le_iff₀ hLp0]
    linarith
  have hLqle : (7 / 24) * Lq ≤ μ / 10 ^ (10 : ℕ) := by
    nlinarith [hLq, hsqle, hsq0]
  have hlqle : (7 / 24) * lq ≤ μ / 10 ^ (10 : ℕ) := by
    nlinarith [hlq, hΛle]
  have hdivle : μ / Λ ≤ μ / 10 ^ (21 : ℕ) :=
    div_le_div_of_nonneg_left hμ.le (by norm_num) hΛ
  have h9 : (16 : ℝ) ≤ μ / 10 ^ (10 : ℕ) := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith [hμbig]
  have hLp2 : Lp / 73728 ≤ μ / 10 ^ (10 : ℕ) := by
    have h : (10 : ℝ) ^ (10 : ℕ) = 10000000000 := by norm_num
    rw [h] at hLple ⊢
    norm_num at hLple ⊢
    linarith
  have hΛ2 : Λ / 2 ≤ μ / 10 ^ (10 : ℕ) := by
    have h : (10 : ℝ) ^ (10 : ℕ) = 10000000000 := by norm_num
    rw [h] at hΛle ⊢
    norm_num at hΛle ⊢
    linarith
  have hbig : (6 : ℝ) * (μ / 10 ^ (10 : ℕ)) + μ / 10 ^ (21 : ℕ) + μ / 8 ≤ (5 / 24) * μ := by
    have h1 : (10 : ℝ) ^ (10 : ℕ) = 10000000000 := by norm_num
    have h2 : (10 : ℝ) ^ (21 : ℕ) = 1000000000000000000000 := by norm_num
    rw [h1, h2]
    linarith [hμ.le]
  linarith

set_option maxHeartbeats 1000000 in
-- the whole `exp`/`rpow` reduction (card, `VJ²`, the `X`-power, the `Mr` floor) elaborates in
-- one term against the levered `𝒫₂`/`𝒬K₂` literals; the default budget is spent by the
-- `thinBundleGChi` unfold
theorem s16_budget_field_gk (K : ℕ) {M Nd q P Q i : ℕ} {Tann : ℝ}
    (hM : 1 ≤ M) (hq : 1 ≤ q) (hQpos : 0 < Q)
    (hmu8 : 8 ≤ Real.log (Nd : ℝ))
    (hLam : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (Nd : ℝ)))
    (hqlog : (q : ℝ) ≤ (Real.log (Nd : ℝ)) ^ 12)
    (hTann1 : 1 < Tann) (hTannhi : Tann ≤ (Nd : ℝ))
    (hQhigh : (Q : ℝ) ≤ Q83 (Nd : ℝ))
    (hQ2reg : Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (Nd : ℝ)))
    (hcap : Real.log (Real.log (Nd : ℝ))
      ≤ Real.log ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) / 24)
    (hi : i ∈ ramI (H83 (Nd : ℝ) theta293) P Q) :
    thinBundleGChi ((q : ℝ) * Tann) (s13VJ_gk K M) (calH (H1door M) 2)
        (calP (Adoor M) (s13GK K M) 2) (calQK (Adoor M) (s13GK K M) M 2)
      * (Nd : ℝ) ^ (1 - 2 * s13Eta + s13EpsD q Nd) ≤ ((s13Mr Nd i : ℕ) : ℝ) := by
  set X : ℝ := (Nd : ℝ) with hXdef
  set μ : ℝ := Real.log X with hmudef
  set Λ : ℝ := Real.log μ with hLamdef
  set Lp : ℝ := Real.log ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) with hLpdef
  set Lq : ℝ := Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ) with hLqdef
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hX0 : (0 : ℝ) < X := by
    rcases Nat.eq_zero_or_pos Nd with h0 | hpos
    · exfalso
      rw [hmudef, hXdef, h0] at hμ0
      simp only [Nat.cast_zero, Real.log_zero] at hμ0
      exact lt_irrefl 0 hμ0
    · rw [hXdef]; exact_mod_cast hpos
  have hXexp : Real.exp μ = X := Real.exp_log hX0
  -- the base logs
  have hLp0 : (0 : ℝ) < Lp := by
    rw [hLpdef, s16_logP2]
    have hA : (1 : ℕ) ≤ Adoor M := le_trans (by norm_num) (Adoor_ge M)
    have hG : (1 : ℕ) ≤ s13GK K M := one_le_s13GK K hM
    have h4 : (1 : ℝ) ≤ ((4 * (Adoor M * s13GK K M) : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 4 * (Adoor M * s13GK K M) := by
        have := Nat.mul_le_mul hA hG; omega
      exact_mod_cast this
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith
  have hLqval : Lq = ((4 * M : ℕ) : ℝ) * Lp := by rw [hLqdef, hLpdef, s16_logQK2]
  have hLpq : 4 * Lp ≤ Lq := by
    rw [hLqval]
    have : (4 : ℝ) ≤ ((4 * M : ℕ) : ℝ) := by
      have : (4 : ℕ) ≤ 4 * M := by omega
      exact_mod_cast this
    nlinarith [hLp0]
  have hΛ0 : (0 : ℝ) < Λ := by linarith [hLam]
  -- `12Λ ≤ μ`
  have h12 : 12 * Λ ≤ μ := by
    have hh : Real.exp Λ = μ := by rw [hLamdef]; exact Real.exp_log hμ0
    have h1 : Λ / 2 + 1 ≤ Real.exp (Λ / 2) := Real.add_one_le_exp _
    have h2 : Real.exp (Λ / 2) * Real.exp (Λ / 2) = μ := by
      rw [← Real.exp_add, show Λ / 2 + Λ / 2 = Λ by ring, hh]
    nlinarith [hLam, h1, h2, Real.exp_pos (Λ / 2)]
  -- `S = q·Tann`
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hS0 : (0 : ℝ) < (q : ℝ) * Tann := by nlinarith
  have hlogTann0 : (0 : ℝ) < Real.log Tann := Real.log_pos hTann1
  have hlogq0 : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
  have hlogq12 : Real.log (q : ℝ) ≤ 12 * Λ := by
    have hpow : Real.log ((Real.log X) ^ 12) = 12 * Λ := by
      rw [Real.log_pow]; push_cast; rw [← hmudef, ← hLamdef]
    calc Real.log (q : ℝ) ≤ Real.log ((Real.log X) ^ 12) :=
          Real.log_le_log (by linarith) hqlog
      _ = 12 * Λ := hpow
  have hlogTann : Real.log Tann ≤ μ := by
    rw [hmudef]; exact Real.log_le_log (by linarith) hTannhi
  have hlS : Real.log ((q : ℝ) * Tann) ≤ μ + 12 * Λ := by
    rw [Real.log_mul (by linarith) (by linarith)]
    linarith
  have hlS0 : (0 : ℝ) < Real.log ((q : ℝ) * Tann) := by
    rw [Real.log_mul (by linarith) (by linarith)]
    linarith
  have hllS : Real.log (Real.log ((q : ℝ) * Tann)) ≤ Λ + 1 := by
    have h2μ : Real.log ((q : ℝ) * Tann) ≤ Real.exp 1 * μ := by
      nlinarith [Real.add_one_le_exp (1 : ℝ), h12, hlS, hμ0]
    have hstep : Real.log (Real.log ((q : ℝ) * Tann)) ≤ Real.log (Real.exp 1 * μ) :=
      Real.log_le_log hlS0 h2μ
    have heq : Real.log (Real.exp 1 * μ) = 1 + Λ := by
      rw [Real.log_mul (Real.exp_pos 1).ne' hμ0.ne', Real.log_exp]
    linarith
  -- the numeric core
  have hnum := s16_budget_num (μ := μ) (Λ := Λ) (Lp := Lp) (Lq := Lq)
    (lS := Real.log ((q : ℝ) * Tann)) (llS := Real.log (Real.log ((q : ℝ) * Tann)))
    (lq := Real.log (q : ℝ)) hLam rfl hμ0 hLp0 hLpq (by rw [hLqdef]; exact hQ2reg)
    (by rw [hLpdef] at hcap ⊢; exact hcap) hlogq12 hlS0 hlS hllS
  -- ⟦THE CARD FACTOR⟧
  have hmr : mrAlpha (1 / 12) 2 = 7 / 48 := by rw [mrAlpha]; norm_num
  have hH2pos : (0 : ℝ) < calH (H1door M) 2 := by
    rw [s16_calH_two]; linarith [H1door_two hM]
  have hLq0 : (0 : ℝ) ≤ Lq := by rw [hLqval]; positivity
  have hcard := ramI_card_le (calH (H1door M) 2) (calP (Adoor M) (s13GK K M) 2)
    (calQK (Adoor M) (s13GK K M) M 2) (mul_nonneg hH2pos.le hLq0)
  have hH2le : calH (H1door M) 2 ≤ Real.exp (2 + Lp / 73728) := by
    have hlog := s16_logH2_le K hM
    rw [← hLpdef] at hlog
    calc calH (H1door M) 2 = Real.exp (Real.log (calH (H1door M) 2)) :=
          (Real.exp_log hH2pos).symm
      _ ≤ Real.exp (2 + Lp / 73728) := Real.exp_le_exp.mpr hlog
  have hexphalf : Real.exp (Λ / 2) * Real.exp (Λ / 2) = μ := by
    rw [← Real.exp_add, show Λ / 2 + Λ / 2 = Λ by ring, hLamdef]
    exact Real.exp_log hμ0
  have hLqexp : Lq ≤ Real.exp (Λ / 2) := by
    have hsqe : Real.sqrt μ = Real.exp (Λ / 2) := by
      rw [show μ = Real.exp (Λ / 2) ^ 2 by rw [sq]; exact hexphalf.symm]
      exact Real.sqrt_sq (Real.exp_pos _).le
    rw [← hsqe]; exact hQ2reg
  have hcardexp :
      ((ramI (calH (H1door M) 2) (calP (Adoor M) (s13GK K M) 2)
        (calQK (Adoor M) (s13GK K M) M 2)).card : ℝ)
        ≤ Real.exp (3 + Lp / 73728 + Λ / 2) := by
    have hstep : calH (H1door M) 2 * Lq + 1
        ≤ Real.exp (2 + Lp / 73728) * Real.exp (Λ / 2) + 1 := by
      have := mul_le_mul hH2le hLqexp hLq0 (Real.exp_pos _).le
      linarith
    have hcomb : Real.exp (2 + Lp / 73728) * Real.exp (Λ / 2)
        = Real.exp (2 + Lp / 73728 + Λ / 2) := by rw [← Real.exp_add]
    have hone : (1 : ℝ) ≤ Real.exp (2 + Lp / 73728 + Λ / 2) := by
      rw [Real.one_le_exp_iff]; positivity
    have hplus : Real.exp (2 + Lp / 73728 + Λ / 2) + 1
        ≤ Real.exp (3 + Lp / 73728 + Λ / 2) := by
      have : Real.exp (3 + Lp / 73728 + Λ / 2)
          = Real.exp 1 * Real.exp (2 + Lp / 73728 + Λ / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      nlinarith [Real.exp_one_gt_d9, hone]
    linarith [hcard, hstep, hcomb ▸ hstep]
  -- ⟦THE `VJ` FACTOR⟧
  have hVJ : (s13VJ_gk K M) ^ 2 = Real.exp ((7 / 24) * Lq) := by
    rw [s13VJ_gk, hmr, ← hLqdef, sq, ← Real.exp_add]
    congr 1; ring
  -- ⟦THE `X`-POWER⟧
  have hXr : X ^ (1 - 2 * s13Eta + s13EpsD q Nd)
      = Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ)) := by
    rw [Real.rpow_def_of_pos hX0, s13Eta, s13EpsD, hmr]
    congr 1
    rw [← hXdef, ← hmudef]
    field_simp
    ring
  -- ⟦THE ASSEMBLY⟧
  have h1680 : (1680 : ℝ) ≤ Real.exp 8 := by
    have h2 : Real.exp 8 = (Real.exp 1) ^ (8 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : (2.7182818283 : ℝ) ^ (8 : ℕ) ≤ (Real.exp 1) ^ (8 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 8
    have h5 : (1680 : ℝ) ≤ (2.7182818283 : ℝ) ^ (8 : ℕ) := by norm_num
    linarith
  rw [thinBundleGChi, hVJ, hXr]
  set E : ℝ := 2 * (Real.log ((q : ℝ) * Tann) / Lp)
    * Real.log (Real.log ((q : ℝ) * Tann)) with hEdef
  have hprod :
      ((ramI (calH (H1door M) 2) (calP (Adoor M) (s13GK K M) 2)
        (calQK (Adoor M) (s13GK K M) M 2)).card : ℝ)
          * (1680 * Real.exp ((7 / 24) * Lq) * Real.exp E)
          * Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ))
        ≤ Real.exp (3 + Lp / 73728 + Λ / 2)
          * (Real.exp 8 * Real.exp ((7 / 24) * Lq) * Real.exp E)
          * Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ)) := by
    have hA : (0 : ℝ) ≤ Real.exp ((7 / 24) * Lq) * Real.exp E := by positivity
    have hB : (0 : ℝ) ≤ Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ)) := by positivity
    have hC : (1680 : ℝ) * Real.exp ((7 / 24) * Lq) * Real.exp E
        ≤ Real.exp 8 * Real.exp ((7 / 24) * Lq) * Real.exp E := by
      have := mul_le_mul_of_nonneg_right h1680 hA
      calc (1680 : ℝ) * Real.exp ((7 / 24) * Lq) * Real.exp E
          = 1680 * (Real.exp ((7 / 24) * Lq) * Real.exp E) := by ring
        _ ≤ Real.exp 8 * (Real.exp ((7 / 24) * Lq) * Real.exp E) := this
        _ = Real.exp 8 * Real.exp ((7 / 24) * Lq) * Real.exp E := by ring
    have hcard0 : (0 : ℝ) ≤ ((ramI (calH (H1door M) 2) (calP (Adoor M) (s13GK K M) 2)
        (calQK (Adoor M) (s13GK K M) M 2)).card : ℝ) := Nat.cast_nonneg _
    have hmid := mul_le_mul hcardexp hC (by positivity) (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hmid hB
  have hsum : Real.exp (3 + Lp / 73728 + Λ / 2)
      * (Real.exp 8 * Real.exp ((7 / 24) * Lq) * Real.exp E)
      * Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ))
      = Real.exp (11 + Lp / 73728 + Λ / 2 + (7 / 24) * Lq + E
          + (7 / 24) * Real.log (q : ℝ) + (19 / 24) * μ) := by
    simp only [← Real.exp_add]
    congr 1
    ring
  -- ⟦THE RIGHT-HAND SIDE⟧
  have hH830 : (0 : ℝ) < H83 X theta293 := by
    rw [H83, ← hmudef]; exact Real.rpow_pos_of_pos hμ0 _
  have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQpos
  have hlogQ0 : (0 : ℝ) ≤ Real.log (Q : ℝ) := Real.log_nonneg hQR
  have hiQ : (i : ℝ) / H83 X theta293 ≤ μ / Λ := by
    rw [ramI, Finset.mem_Icc] at hi
    have h1 : (i : ℝ) ≤ H83 X theta293 * Real.log (Q : ℝ) := by
      have h2 : ((⌊H83 X theta293 * Real.log (Q : ℝ)⌋₊ : ℕ) : ℝ)
          ≤ H83 X theta293 * Real.log (Q : ℝ) :=
        Nat.floor_le (mul_nonneg hH830.le hlogQ0)
      have h3 : (i : ℝ) ≤ ((⌊H83 X theta293 * Real.log (Q : ℝ)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hi.2
      linarith
    have h4 : Real.log (Q : ℝ) ≤ μ / Λ := by
      have h5 : Real.log (Q83 X) = μ / Λ := by
        rw [Q83, Real.log_exp, ← hmudef, ← hLamdef]
      calc Real.log (Q : ℝ) ≤ Real.log (Q83 X) := Real.log_le_log (by linarith) hQhigh
        _ = μ / Λ := h5
    rw [div_le_iff₀ hH830]
    nlinarith [hH830, h1, h4]
  have hMr : 2 * X * Real.exp (-(i : ℝ) / H83 X theta293) ≤ ((s13Mr Nd i : ℕ) : ℝ) := by
    rw [hXdef, s13Mr]
    exact Nat.le_ceil _
  have hexpstep : Real.exp (μ - μ / Λ) ≤ 2 * X * Real.exp (-(i : ℝ) / H83 X theta293) := by
    have h1 : Real.exp (μ - μ / Λ) = X * Real.exp (-(μ / Λ)) := by
      rw [← hXexp, ← Real.exp_add]; congr 1
    have h2 : Real.exp (-(μ / Λ)) ≤ Real.exp (-(i : ℝ) / H83 X theta293) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      linarith [hiQ]
    have h3 : X * Real.exp (-(μ / Λ)) ≤ X * Real.exp (-(i : ℝ) / H83 X theta293) :=
      mul_le_mul_of_nonneg_left h2 hX0.le
    nlinarith [Real.exp_pos (-(i : ℝ) / H83 X theta293), hX0, h1, h3]
  have hfin : Real.exp (11 + Lp / 73728 + Λ / 2 + (7 / 24) * Lq + E
      + (7 / 24) * Real.log (q : ℝ) + (19 / 24) * μ) ≤ Real.exp (μ - μ / Λ) := by
    apply Real.exp_le_exp.mpr
    rw [hEdef] at *
    linarith [hnum]
  linarith [hprod, hsum ▸ hprod, hfin, hexpstep, hMr]

/-! ## §3 — THE CAP-GATE SUPPLY -/

/-- ⟦THE ONE NEW RIDER⟧ the socket's base-scale cap. -/
def S16BaseScaleCap_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
    Real.log (Real.log (((A + s : ℕ)) : ℝ))
      ≤ Real.log ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) / 24

/-- ⟦THE CO-FACTOR BLOCK, CARRIED⟧ (ruling 9's posture). -/
def S16CofactorSupply_gk (K : ℕ) (Cq : ℝ) (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
    ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
      ∃ Rrad Rbd CR : ℝ,
        0 ≤ Rbd
        ∧ Rbd ≤ CR * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-rho293)
        ∧ 1728 * Cq * CR ^ 2 ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (2 * theta293)
        ∧ (∀ (t₁ : ℝ) (χ : DirichletCharacter ℂ q),
            CofactorSocket (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) (A + s)
              (s13BandP (A + s)) (s13BandQ (A + s)) (2 * T) Rrad t₁ Rbd
              (doorCofactor0 χ (calP (Adoor M) (s13GK K M))
                (calQK (Adoor M) (s13GK K M) M) 2 1))

set_option maxHeartbeats 1000000 in
-- 37 structure fields are checked against the levered per-block gate in one `exact`
theorem s16_capGate_supply_gk (K : ℕ) {Cq cs T₀ Kq Ks C : ℝ} {R : ChowlaRegime} {M : ℕ}
    {epsf : ℕ → ℝ}
    (hM : 1 ≤ M) (hfl : loglogFloor50 ≤ R.Hlo) (hcs : 1 ≤ cs)
    (hblk : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor_gk K M ≤ A + s)
    (hT₀ : T₀ ≤ Real.exp (Real.exp 100)) (hKq : Kq ≤ Real.exp 100)
    (hKs : Real.exp (-100) ≤ Ks) (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hεr : ∀ A : ℕ, theta293 - 1 / 500 ≤ epsf A)
    (hcap : S16BaseScaleCap_gk K R M) (hcof : S16CofactorSupply_gk K Cq R M) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
        2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
        5 ≤ Real.log (Real.log (2 * T)) →
        ∃ (P Q : ℕ) (Rrad Rbd CR EP2 : ℝ),
          S13CapGatePerBlock_gk K Cq cs T₀ Kq Ks C M (A + s) q P Q H (2 * T)
            Rrad Rbd CR EP2 (epsf (A + s)) := by
  intro H L q j A s hb T hTlo hThi hTgate hTll
  obtain ⟨Rrad, Rbd, CR, hRbd0, hRbdg, hCqg, hRsock⟩ := hcof H L q j A s hb T hTlo hThi
  -- the grid wave
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18⟩ :=
    s13CapGrid_all_gk K hM hcs hfl hb (hblk H L q j A s hb) hTlo hThi
  -- `1 < 2T` off the annulus gate
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hT1 : (1 : ℝ) < 2 * T := by
    have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
    linarith
  have hT0le : (0 : ℝ) ≤ 2 * T := by linarith
  have hAN : A ≤ A + s := Nat.le_add_right _ _
  have hTflo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ 2 * T := by linarith
  -- the floor wave
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, -⟩ :=
    s13CapFloor_all_gk K hfl hb hM hAN hTflo g6 hT₀ hKq hKs
  -- the eps wave
  obtain ⟨hP83pin, hgradepin⟩ := s13CapEps_pins_supply hfl hb
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ :=
    s13CapEps_all hfl hb (hεr (A + s)) hC0 hC hT0le hThi hP83pin hgradepin
  refine ⟨s13BandP (A + s), s13BandQ (A + s), Rrad, Rbd, CR,
    s13CapEP2 C q (A + s) (s13BandP (A + s)) (s13BandQ (A + s)) (2 * T), ?_⟩
  exact
    { logX_eight := g1
      H83_two := g2
      QTann := f1
      kappa30Q := f2
      q_logX := g3
      T0_Tann := f3
      floor1 := f4
      floor2 := f5
      floor3 := f6
      floor4 := f7
      logqT_L := g4
      P_low := g5
      Q2_reg := g6
      Q_pos := g7
      Q_high := g8
      P_le_Q := g9
      budget := fun i hi =>
        s16_budget_field_gk K hM hb.2.2.2.1 g7 g1
          (s13CapGrid_Lambda_lo hfl hb) g3 hT1 hThi g8 g6 (hcap H L q j A s hb) hi
      Hj := g10
      B3 := g11
      BT := g12
      kappa30 := g13
      BT10 := g14
      WL := g15
      gate := g16
      Rbd_nonneg := hRbd0
      Rbd_grade := hRbdg
      Cq_gate := hCqg
      Rbd_socket := hRsock
      epsr_nonneg := e1
      abs8640 := e2
      EP2_gate := e3
      q_arcDen := e4
      phi_row := e5
      p2_row := e6
      tail_row := e7
      Q_hundred := g17
      band_product := g18 }

/-! ## §4 — THE CROSSING BOUND, SUPPLIED -/

set_option maxHeartbeats 1000000 in
-- the eighteen-slot `hcapWS` family re-elaborates against the wire's own shape (the same cause
-- as `S12FuseCompose` §GK, whose statement this consumes)
theorem s15_crossing_supplied_gk (K : ℕ) :
    ∃ Cq cs T₀ Kq Ks C : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      (1 ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks → Real.log C ≤ 40 →
        ∀ (R : ChowlaRegime) (M : ℕ), 1 ≤ M → loglogFloor50 ≤ R.Hlo →
          (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor_gk K M ≤ A + s) →
          S16CofactorSupply_gk K Cq R M → S16BaseScaleCap_gk K R M →
          S15CrossingBound_gk K R M) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs0, hT₀3, hKq0, hKs0, hwire⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨C, hC0, hband⟩ := m4_tail_mass_at_band
  refine ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, ?_⟩
  intro hcs hT₀ hKq hKs hC R M hM hfl hblk hcof hcap
  have hgate := s16_capGate_supply_gk K hM hfl hcs hblk hT₀ hKq hKs hC0 hC
    (fun _ => le_rfl) hcap hcof
  refine hwire R M liouvilleC (fun _ => theta293 - 1 / 500) liouvilleC_norm_le_one ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨P, Q, Rrad, Rbd, CR, EP2, hg⟩ := hgate H L q j A s hsb T hTlo hThi hTgate hTll
  have hq : 1 ≤ q := hsb.2.2.2.1
  have hA : 0 < A := hsb.2.2.2.2.2.2.2.1
  have hNd : 1 ≤ A + s := by omega
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by have := hg.logX_eight; linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
  have hT1 : (1 : ℝ) < 2 * T := by linarith
  exact doorCapBundle_at_workingPoint_perBlock_gk K hband hM hNd hq hg hT1 hThi hTll

/-! ## §5 — THE FINAL OBJECT -/

set_option maxHeartbeats 1000000 in
-- the twin's fifteen-binder prefix re-elaborates beside the crossing supply's six constants
theorem logChowla2_witnessed_scale_final :
    ∃ (K : ℕ) (ε : ℚ) (Cg Kc δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      ((1 : ℚ) / 2 ^ 9 ≤ ε → 24 * Cg / δ₀ ≤ 2 ^ 355 → 1 / 2 ^ 10 ≤ δ₀ → Kc ≤ 2 ^ 20 →
        Ct ≤ 2 ^ 20 → (x₀ : ℝ) ≤ Real.exp (Real.exp 275) → Mfl ≤ 2 ^ 355 →
        Hcap ≤ s15WitFloor2 →
        1 ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks → Real.log C ≤ 40 →
        ∀ g : ℕ → ℕ → ℕ, ∃ (R : ChowlaRegime) (M : ℕ),
          R.eps = ε ∧ R.Hlo = s15WitFloor2 ∧ g R.Hhi R.ω ≤ R.x ∧
          S15Sel''_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M ∧
          (S16CofactorSupply_gk K Cq R M → S16BaseScaleCap_gk K R M →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨K, ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1, hbody⟩ :=
    logChowla2_conditional_sharp2_nonvacuous_gk
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hsupply⟩ :=
    s15_crossing_supplied_gk K
  refine ⟨K, ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, ?_⟩
  intro h1 h2 h3 h4 h5 h6 h7 h8 hcs hT₀ hKq hKs hC g
  obtain ⟨R, M, hReps, hHlo, hRg, hsel, hfire⟩ := hbody h1 h2 h3 h4 h5 h6 h7 h8 g
  refine ⟨R, M, hReps, hHlo, hRg, hsel, ?_⟩
  intro hcof hcap
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact s15WitFloor2_ll
  have hblk : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor_gk K M ≤ A + s := by
    intro H L q j A s hb
    exact s15_block_at_socket_gk K hb (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (hsupply hcs hT₀ hKq hKs hC R M hsel.hM hfl hblk hcof hcap)

/-! ## §6 — ⟦REF-REPAIR⟧ THE REPAIRED TERMINAL, AT THE RE-CUT LEVER

⟦THE THREE DEFECTS REPAIRED⟧ (all found by the summit refuters, 2026-07-31)

1. **THE RIDER VACUITY** (`REF-FINAL-SAT`) — §5's object carries `1/2^10 ≤ δ₀`, FALSE at the
   chain's own pinned `δ₀ = s13Delta0 ≈ 2^{-19.68}` (818× short) and unreachable at any `ε`.
   Repaired in `S15Witness` §1'/§GK.8': the demand relaxes to `1/2^20` and the `ρ`-charge
   `36 → 43`; all five `ρ`-lines of the `M = 2^355` register still close.
2. **THE CARRIED PINS** (`REF-FINAL-SAT`) — the capstone consumed the UNPINNED road, so
   `ε`/`δ₀`/`Cg` had to ride as hypotheses.  Repaired by
   `S12ConstCompose.logChowla2_capstone_final_const'_graded_gk_pinned`, which consumes
   `HloExportMR.m4_second_road_L2_hloCap_pinned_gk`: `Cg ≤ 2·10^{12}`, `1/500 ≤ ε`,
   `1/838400 ≤ δ₀` are now `∃`-prefix THEOREMS, and the three riders they discharge are GONE
   from the hypothesis list — removed BECAUSE PROVEN, not weakened.
3. **THE MIS-PINNED LEVER** (`REF-FINAL-HONEST`) — `K = 500000` was calibrated to the OLD
   witness (`λ₋ = 69`) and never re-cut when `s15WitFloor2` moved `λ₋` to `277.2589`.  At
   `K = 500000` the base-scale cap and the tower are mutually exclusive (deficit 61.5×), so
   §5's inner implication is vacuous.  Re-pinned here at `K = 3.2·10^7`, with the demand
   certified in the kernel below.

⚠ ⟦THE ONE DEFECT **NOT** REPAIRED — READ THIS BEFORE ANY SEAL⟧ the rider `Mfl ≤ 2^355`.
The exported `Mfl` is the band-gate grade floor at the LEVERED band constant
`Cb = C·4^{Aexp}·(exp 26.25·(49152·2^K)^{1.05}) + 1`, so `Mfl` grows like `2^{2.63·K}` while
the register's `M`-window is capped near `2^{356}` by the `half` line.  The `Mfl` wire below
(`s11_grade_absorption'` in place of `s11_grade_absorption`) shrinks the floor by the full
`(4·10^{10})^{2.5·2.501} ≈ 2^{221}` that `S11HoistGrade` §4 restored — but `2^{221}` does not
close a `2^{2.63K}` gap.  The rider is satisfiable only for `K ≲ 160`, while §6.1's cap
certificate demands `K ≥ 3.075·10^7`.  **`Mfl` and `S16BaseScaleCap_gk` are jointly
unsatisfiable at EVERY `K` and every base floor**: the `M`-window gives
`K ≤ 0.55·λ₋ − 41`, the cap gives `K ≥ 1.443·λ₋³ − 413`, and the two meet only at
`λ₋ ≲ 6.4` — while `loglogFloor50` forces `λ₋ ≥ 50`.  (`M` grows like `log₂ log H₋`; the
cap's demand grows like `(log log H₋)³`.)  ⟦NOT KERNEL-CERTIFIED⟧ the band constant carries
an OPAQUE factor `C` (from `M4T0DatumDischarge.m4_hT0band_at_door_discharged_split_graded_gk`),
so no theorem states `Mfl > 2^355`; the read is at the proof's own witness, where
`X0MFL-TRACE`'s `probe_Mfl_overflow` already puts `Mfl ≥ 2^158` at `C = 1`, `K = 0`.
This is a DESIGN question, not a porting question; it is named here and reported, not hidden.

## §6.1 — the re-cut acceptance certificate -/

set_option exponentiation.threshold 4000 in
/-- The levered level-2 base at the witness modulus, from below:
`2^{K+413} ≤ calE (A(2^355)) (G_K(2^355)) 2 = 4·(A·G)`.  (`4·356·3072 = 4374528 ≥ 2^{22}`.) -/
theorem s16_recut_calE_ge (K : ℕ) :
    2 ^ (K + 413) ≤ 4 * (Adoor (2 ^ 355) * s13GK K (2 ^ 355)) := by
  rw [s15w2_Adoor, s13GK]
  have h1 : (4 : ℕ) * (2 ^ 36 * 356 * (3072 * 2 ^ K * 2 ^ 355))
      = (4 * 356 * 3072 * 2 ^ 36 * 2 ^ 355) * 2 ^ K := by ring
  have h2 : (2 : ℕ) ^ (K + 413) = 2 ^ 413 * 2 ^ K := by rw [pow_add]; ring
  rw [h1, h2]
  refine Nat.mul_le_mul_right _ ?_
  have h3 : (4 : ℕ) * 356 * 3072 * 2 ^ 36 * 2 ^ 355 = 4374528 * 2 ^ 391 := by
    rw [show (2 : ℕ) ^ 391 = 2 ^ 36 * 2 ^ 355 by rw [← pow_add]]; ring
  have h4 : (2 : ℕ) ^ 413 = 4194304 * 2 ^ 391 := by
    rw [show (413 : ℕ) = 22 + 391 by norm_num, pow_add]; norm_num
  rw [h3, h4]
  exact Nat.mul_le_mul_right _ (by norm_num)

set_option exponentiation.threshold 4000 in
/-- **⟦THE LEVER'S OWN CEILING, FROM BELOW⟧** `(K + 412)·log 2 ≤ log(log 𝒫₂)` at
`M = 2^355`.  (`log 𝒫₂ = 4(A·G)·log 2`; the `−log 2` pays `log(log 2) ≥ −log 2`.) -/
theorem s16_recut_logLogP2_ge (K : ℕ) :
    ((K : ℝ) + 412) * Real.log 2
      ≤ Real.log (Real.log ((calP (Adoor (2 ^ 355)) (s13GK K (2 ^ 355)) 2 : ℕ) : ℝ)) := by
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  set n : ℕ := 4 * (Adoor (2 ^ 355) * s13GK K (2 ^ 355)) with hn
  have hge : (2 : ℕ) ^ (K + 413) ≤ n := s16_recut_calE_ge K
  have hgeR : (2 : ℝ) ^ (K + 413) ≤ ((n : ℕ) : ℝ) := by
    have h : (((2 : ℕ) ^ (K + 413) : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hge
    calc (2 : ℝ) ^ (K + 413) = (((2 : ℕ) ^ (K + 413) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ _ := h
  have hn0 : (0 : ℝ) < ((n : ℕ) : ℝ) := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ (K + 413) := by positivity
    linarith
  have hlogn : ((K : ℝ) + 413) * Real.log 2 ≤ Real.log ((n : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (K + 413)) hgeR
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hll : -Real.log 2 ≤ Real.log (Real.log 2) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith : (1 : ℝ) / 2 ≤ Real.log 2)
    rwa [show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [one_div, Real.log_inv]] at h
  rw [s16_logP2, ← hn, Real.log_mul (by linarith) (by linarith)]
  linarith

/-- **⟦THE RE-CUT, CERTIFIED⟧** (`s16_recut_cap_demand_met`) — at the new pin
`K = 3.2·10^7` the base-scale cap's demand `λ₋³ ≤ log(log 𝒫₂)` HOLDS at the sharp2 witness:
`2.1314·10^7 ≤ 2.2181·10^7`, 4.07% of room.  (At the landed pin `K = 500000` the same
quantity is `3.47·10^5` — short by 61.5×, which is `REF-FINAL-HONEST`'s kill.)  ⟦WHY
`3.2·10^7` AND NOT `3.08·10^7`⟧ the bare demand is met at `K = 3.075·10^7` but with < 1% of
margin; `3.1·10^7` gives 0.82%, still under the amendment's 1% floor.  `3.2·10^7` gives
4.07%. -/
theorem s16_recut_cap_demand_met :
    (Real.log (Real.log ((s15WitFloor2 : ℕ) : ℝ))) ^ 3
      ≤ Real.log (Real.log
          ((calP (Adoor (2 ^ 355)) (s13GK 32000000 (2 ^ 355)) 2 : ℕ) : ℝ)) := by
  have hlam := s15WitFloor2_loglog_le
  have h50 := s15WitFloor2_loglog_ge
  set u : ℝ := Real.log (Real.log ((s15WitFloor2 : ℕ) : ℝ)) with hu
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hsq : u ^ 2 ≤ (2772589 / 10000 : ℝ) ^ 2 := by nlinarith
  have hcb : u ^ 3 ≤ (2772589 / 10000 : ℝ) ^ 3 := by nlinarith
  have hnum : (2772589 / 10000 : ℝ) ^ 3 ≤ 21313585 := by norm_num
  refine le_trans (le_trans hcb hnum) (le_trans ?_ (s16_recut_logLogP2_ge 32000000))
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  push_cast
  linarith

/-! ## §6.2 — ⟦THE REPAIRED TERMINAL⟧ -/

set_option maxHeartbeats 1000000 in
-- the twin's eighteen-binder prefix re-elaborates beside the crossing supply's six constants
/-- **⟦THE REPAIRED TERMINAL⟧** (`logChowla2_witnessed_scale_final'`) — §5's object with
repairs 1–3 of §6 in place, at the re-cut pin `K = 3.2·10^7`.

⟦THE HYPOTHESIS LIST, EXACT AND COMPLETE⟧ everything the inner implication asks for:

* `Kc ≤ 2^20`, `Ct ≤ 2^20` — the two constant-pool numerals (EPSPIN/CgPin genre);
* `(x₀ : ℝ) ≤ e^{e^{275}}` — ⟦`hx0win`⟧ **the one Siegel item**: `x₀` is Siegel-ineffective,
  no theorem places it in any window, and the conditional carries it named;
* `Mfl ≤ 2^355` — ⚠ see §6's warning: NOT satisfiable at this `K`;
* `Hcap ≤ s15WitFloor2` — the road's own base cap against the witness floor;
* `1 ≤ cs`, `T₀ ≤ e^{e^{100}}`, `Kq ≤ e^{100}`, `e^{−100} ≤ Ks`, `log C ≤ 40` — the five
  constant riders of the fuse and the band lemma;
* `S16CofactorSupply_gk` — ⟦RULING 9⟧'s shelved `Rbd`/`Cq` debt, carried not re-dressed;
* `S16BaseScaleCap_gk` — §2's base-scale cap, certified compatible with the tower at this
  `K` by `s16_recut_cap_demand_met`.

⟦WHAT LEFT THE LIST, AND WHY⟧ three hypotheses of §5 are GONE, each REMOVED-BECAUSE-PROVEN:

* `(1:ℚ)/2^9 ≤ ε` — discharged from `1/500 ≤ ε` (the `∃`-prefix conjunct, 2.4% margin);
* `1/2^10 ≤ δ₀` — was FALSE; its repaired form `1/2^20 ≤ δ₀` is discharged from
  `1/838400 ≤ δ₀` (the `∃`-prefix conjunct, 25% margin);
* `24·Cg/δ₀ ≤ 2^355` — discharged from `Cg ≤ 2·10^{12}` and the `δ₀` pin
  (`4.02·10^{19} ≤ 2^{355}`, 290 bits).

The three discharging facts ride in the `∃`-prefix, so a consumer can read them off. -/
theorem logChowla2_witnessed_scale_final' :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      (Kc ≤ 2 ^ 20 → Ct ≤ 2 ^ 20 → (x₀ : ℝ) ≤ Real.exp (Real.exp 275) → Mfl ≤ 2 ^ 355 →
        Hcap ≤ s15WitFloor2 →
        1 ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks → Real.log C ≤ 40 →
        ∀ g : ℕ → ℕ → ℕ, ∃ (R : ChowlaRegime) (M : ℕ),
          R.eps = ε ∧ R.Hlo = s15WitFloor2 ∧ g R.Hhi R.ω ≤ R.x ∧
          S15Sel''_gk 32000000 Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M ∧
          (S16CofactorSupply_gk 32000000 Cq R M → S16BaseScaleCap_gk 32000000 R M →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1, hCgle, hεpin,
    hδpin, hbody⟩ := logChowla2_conditional_sharp2_nonvacuous_gk' 32000000 (by norm_num)
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hsupply⟩ :=
    s15_crossing_supplied_gk 32000000
  refine ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0,
    hCgle, hεpin, hδpin, ?_⟩
  intro h4 h5 h6 h7 h8 hcs hT₀ hKq hKs hC g
  obtain ⟨R, M, hReps, hHlo, hRg, hsel, hfire⟩ := hbody h4 h5 h6 h7 h8 g
  refine ⟨R, M, hReps, hHlo, hRg, hsel, ?_⟩
  intro hcof hcap
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact s15WitFloor2_ll
  have hblk : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      s13BlockFloor_gk 32000000 M ≤ A + s := by
    intro H L q j A s hb
    exact s15_block_at_socket_gk 32000000 hb
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (hsupply hcs hT₀ hKq hKs hC R M hsel.hM hfl hblk hcof hcap)


/-! ## §6.3 — ⟦C4: THE RIDER LANE⟧ THE COMPANION CERTIFICATE, PAGE 1

⟦WHAT THIS IS⟧ THE WIDTH COUNCIL's C4 (2026-07-31, JYH-ratified): every opaque rider of
`logChowla2_witnessed_scale_final'` traced to the `∃`-site that MINTS its witness, and there
either PROVEN (§6.4) or given its honest bound with the gap to the rider's ceiling stated.
Nothing in §6.3 is consumed by a landed declaration — it is an audit page.

⚠ ⟦THE READS ARE PROOF-TERM READS⟧ each witness below is a `Classical.choose` of a landed
`∃`, which the kernel cannot evaluate (`ConstantsExposed` §0's reachability caveat).  What IS
kernel-certified here is the ARITHMETIC of the ceilings — the theorems of this section.
Where the descent is a chain of VERBATIM pass-throughs (every hop
`obtain ⟨C, hC, h⟩ := <lower>` then `refine ⟨C, hC, ?_⟩`) the read is mechanical rather than
interpretive; that is flagged per rider.

### ⟦THE TABLE⟧ (⛔ false at the witness · ❓ opaque · ✅ true)

| rider | verdict | the witness | honest ceiling |
|---|---|---|---|
| `Kc ≤ 2^20` | ⛔ | `bigXi_bounded`'s L²-count, `≈ 2^538` | `2^539` — and FREE |
| `Ct ≤ 2^20` | ⛔ | `6·e^{14} = 2^{22.78}` (mechanical read) | `2^23` — and FREE |
| `Hcap ≤ s15WitFloor2` | ⛔ | `budgetFloor ≈ ⌈e^{e^{e^{1.04·10^{31}}}}⌉` | NONE — THE SECOND WALL |
| `Mfl ≤ 2^355` | ⛔ | §6's warning, unchanged | NONE — THE FIRST WALL |
| `1 ≤ cs` | ⛔ | `cs ≤ 1/10` is a LANDED PROOF LINE | none as stated; carry `cs` |
| `T₀ ≤ e^{e^{100}}` | ❓ | `max e^{e^{100}} T₀z` | forces equality; 3 leaves |
| `Kq ≤ e^{100}` | ✅ | `1/(10^8·c₀) = 0.00126848` | 46 orders spare; not carried |
| `e^{-100} ≤ Ks` | ❓ | `10^8·min Cs_Siegel (1/4059136)` | Siegel — unprovable |
| `log C ≤ 40` | ✅ | `2·e^{19/log 2}+1 = 1.605·10^{12}` | **PROVEN — §6.4** |
| `x₀ ≤ e^{e^{275}}` | ❓ | unchanged | Siegel — the field's wall |

### ⟦RIDER `Ct`⟧ FALSE BY 6.88×; CEILING `2^23`; FREE

Thirteen hops, every one a verbatim pass-through except the one marked:
`final'` ← `S15Witness.logChowla2_conditional_sharp2_nonvacuous_gk'` (:1858)
← `S15Compose.logChowla2_conditional_sharp2_atK_gk_pinned` (:2757)
← `S12ConstCompose.logChowla2_capstone_final_const'_graded_gk_pinned` (:1460)
← `S12ConstCompose.m4_closure_fuse_zero'_const_nonneg_gk` (:934)
← `M4RowsChiZeroPrime.m4_hrowsSlot_at_door_zero'_gk` (:849)
← `…m4_hrowsSum_chi_door_zero'_gk` (:800) ← `…m4_hrowsSum_chi_zero'` (:570)
← `…m4_rowChi_number_of_capstone_zero'` (:448) ← `TLegExit.TLeg_feeds_capstone_gen` (:1228)
← `TLegExit.TLeg_bound_gen` (:1069) ← `TLegExit.Ej_bound_gen` (:765)
← `TLegKill.cell_bound_pinned` (:979) ← `TLegKill.cell_bound_raw` (:905)
← `TLegKill.mix_moment` (:803)
← `MomentsA2.lemma13_moment` (:246)  ⟵ THE ONE NON-IDENTITY HOP: `refine ⟨3 * C, …⟩`
← `MomentsA2.blockDiv_sq_div_sq_sum_le` (:127)
← `ShiuMoment.shiu_moment_sq` (:436)  ⟵ THE LITERAL: `refine ⟨2 * Real.exp 14, …⟩`.

So `Ct = 3·(2·e^{14}) = 6·e^{14} = 7.2156·10^6 = 2^{22.78}` — MR eq (18)'s absolute Shiu
constant, tripled by the dyadic geometric series.  Against `2^20 = 1.0486·10^6` the rider is
FALSE by 6.88× (`s16_audit_Ct_over_pin`) — the FOURTH register vacuity of the
`REF-FINAL-SAT` genre.  ⟦WHY THE REPAIR IS FREE⟧ `Ct` is read by EXACTLY ONE register line,
`S15Sel''_gk.gP1`, whose two sides at `M = 2^355` are `1.3818·10^{12}` and `1.6957·10^{13}`
— a factor of 12.3.  `s16_audit_Ct_ceiling` gives the ceiling `2^23` (14% of room) and
`s16_audit_Ct_gP1_room` certifies `gP1` AT THE TRUE `Ct` and at rider `Kc`'s widened
`ρ`-charge simultaneously.

### ⟦RIDER `Kc`⟧ FALSE BY ~515 BITS; CEILING `2^539`; ALSO FREE

`Kc` descends (all pass-throughs) `final'` ← … ← `logChowla2_capstone_final_const'_graded_gk_
pinned` ← `HloExportMR.m4_second_road_L2_hloCap_pinned_gk` (:698) ← `…_close_split_sq_
hloCap_pinned_gk` (:640) ← `…m4_exit_socket_split_sq_arc_hloCap_pinned` (:277) ←
`HloExport.log_chowla_two_budget_head_g_sq_count_hloCap_pinned` (:564), where it is minted as
`bigXi_bounded`'s `∃`-constant (`GoldbachEnergyFinal` :502) — the large-spectrum `L²` count.
`ConstantsExposed.KExpr` (:339) IS that constant's closed form at the same `ε`-pin; the two
landed numerals about it are `KExpr_le : KExpr ≤ 12·10^{161}` (:356) and
`S15Witness.s15w_KExpr_ge : 12·10^{65} ≤ KExpr` (:693).  The LOWER one settles the rider:
`Kc ≳ 2^{219}` at the closed form, `≈ 2^{538}` at the full tower — `2^20` is out by 199–518
bits.  (`bigXi_bounded_500`, the variant with the count in its statement, is NOT on this
chain and lands at `2^{221.6}` anyway.)
⟦WHY THIS IS ALSO FREE⟧ `Kc` enters the register only through the clearing charge
`−log ρ`, `ρ = doorRhoOfDelta (s12DeltaSock δ₀ Kc) = min 1 (δ₀/(1768400·Kc))`.  At
`Kc ≤ 2^539` (which covers `KExpr_le`'s `12·10^{161} = 2^{538.42}`) the charge is `403`
instead of `43` (`s16_audit_neglog_rho_le_wide`), and ALL FOUR charge-spending register lines
still close: `lvl` (the binding one, `3.13·10^{10}` of slack — `s16_audit_lvl_num_wide`),
`anchor` (`6.6·10^9` — `s16_audit_anchor_wide`), `half` (`6.8·2^{391}` —
`s16_audit_half_wide`) and `gP1` (`s16_audit_Ct_gP1_room`).  `rho`'s own ceiling is `10^{14}`.

### ⟦RIDER `Hcap`⟧ FALSE — AND THE SECOND FACE OF THE WALL

Exported `Hcap = max Hcap_road (max arcFloor36 loglogFloor50)`; the two right arms are
LANDED-fine (`s15WitFloor2_arc`, `s15WitFloor2_ll`).  `Hcap_road` descends to
`HloExportMR.m4_exit_socket_split_sq_arc_hloCap_pinned` (:303) as `max Hcap_head H₀arc`, with
`Hcap_head = max 4000000 (max A (4·⌈1/ε⌉^4))`, `A = max (max (max H₀red H₀D3) H₀xi)
(budgetFloor …)` (`HloExport` :566).  Leaf by leaf: `H₀xi = 2` (benign);
`H₀D3 = H₀red = max (96^8) (⌈e^{64·K_Chen}⌉+1)` with `K_Chen` the Siegel-ineffective PNT
constant (`Chen.lambda_mass_lower` ← `psiTot_pnt` ← `SW.siegelWalfisz_holds`) — FORMALLY
UNBOUNDED; `H₀arc`'s own exp-arm is `⌈e^{25^{25}·10^{40}·250001^9}⌉ ≈ e^{3.39·10^{123}}`;
and `budgetFloor (1/500) β = ⌈e^{e^{e^{1.036·10^{31}}}}⌉` (`BudgetCore` :21) — a HEIGHT-3
TOWER.  Against `s15WitFloor2 = ⌈e^{2^{400}}⌉` (a single exponential, `log = 2.582·10^{120}`)
the `H₀arc` arm alone overshoots by 1313× IN THE EXPONENT and `budgetFloor` by a whole tower
level.  ⚠ ⟦THE SECOND WALL⟧ unlike `Kc`/`Ct` this is NOT relaxable: `R.Hlo` must clear
`Hcap`, so `λ₋ = loglog R.Hlo` would inherit the tower, while `s16_audit_hcap_wall` shows the
base-scale cap's demand `λ₋³ ≤ (K+413)·log 2` FAILS at every `λ₋ ≥ 492` and every admissible
`K ≤ 1.7·10^8`.  `Hcap` and `S16BaseScaleCap_gk` are therefore jointly unsatisfiable at the
proof's own witnesses — a SECOND face of the wall §6 already records for `Mfl`, and
independent of it.

### ⟦THE FIVE CONSTANT RIDERS⟧ (`S16Budget` §4's supply)

`cs`/`T₀`/`Kq`/`Ks` share a nine-hop pass-through from `m4_fuse_hcap_of_capWS_gk` (:754 of
`S12FuseCompose`) down to `PortAssembly.halasz_primes_chi_pair_of_gates` (:1468).
* `cs` — minted at `PortAssembly.halaszPrimesChiGated_of_price` (:812) as
  `min (min (c_vk/(2·K₄)) (c₀/(2·Cκ))) (1/10)` at the LITERAL `c_vk = 1/10^8`, so
  `cs ≤ 1.86·10^{-10}`; and `cs ≤ 1/10` is a LANDED LINE OF THAT PROOF (:826).  The rider
  `1 ≤ cs` is FALSE.  The demand side (`S13CapGrid` :727's `gate`) has a `μ`-power margin
  `3/40 − 2θ₂₉₃ ≥ 0.068`, so the repair is to CARRY `cs` through the margin rather than to
  floor it — a design item, named here.
* `T₀ = max (e^{e^{100}}) T₀z` — the first arm is EXACTLY `e^{e^{100}}`
  (`TwistedEdge.twisted_edge_price_strip` :896, the `le_refl` tell), so the rider forces
  equality and reduces to `T₀z ≤ e^{e^{100}}`; `T₀z` rides three compactness/VK leaves
  (`HalaszPrimesCore` :1061's `δ₀`, :570's `ε₀`, the VK `c_pow`).  No landed bound.
* `Kq = 1/(10^8·c₀)` with `c₀ = min (1/50456) (1/126848) = 1/126848`
  (`SW.zero_free_region_all'` ← `ZeroFree` :262, `ZeroFreeReal` :392) — a RATIONAL NUMERAL
  `0.00126848`.  The rider is TRUE with 46 orders to spare; carrying it needs three
  `_bounded` twins on the zero-free chain (the cheapest open item of this lane).
* `Ks = 10^8·min (min Cs_Siegel (c₀/32)) (1/2)` — upper side closed (`Ks ≤ 24.63`), lower
  side is Siegel's own ineffective constant (`SiegelClose.siegel_theorem` :841).  TRUE but
  UNPROVABLE on this road; it joins `hx0win` as a genuine Siegel item.
* `C` — PROVEN, §6.4. -/

set_option exponentiation.threshold 4000 in
/-- ⟦AUDIT⟧ `e^{14}` bracketed off mathlib's `d9` decimals of `e`. -/
theorem s16_audit_exp14_bracket :
    (1200000 : ℝ) < Real.exp 14 ∧ Real.exp 14 < 1210000 := by
  have hpow : Real.exp 1 ^ (14 : ℕ) = Real.exp 14 := by
    rw [Real.exp_one_pow]; norm_num
  have hlo : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hhi : Real.exp 1 < 2.719 := by linarith [Real.exp_one_lt_d9]
  constructor
  · have h : (2.718 : ℝ) ^ (14 : ℕ) < Real.exp 1 ^ (14 : ℕ) := by gcongr
    rw [hpow] at h
    have hnum : (1200000 : ℝ) < (2.718 : ℝ) ^ (14 : ℕ) := by norm_num
    linarith
  · have h : Real.exp 1 ^ (14 : ℕ) < (2.719 : ℝ) ^ (14 : ℕ) := by gcongr
    rw [hpow] at h
    have hnum : (2.719 : ℝ) ^ (14 : ℕ) < 1210000 := by norm_num
    linarith

/-- ⟦AUDIT⟧ **THE RIDER `Ct ≤ 2^20` IS FALSE** at the chain's own witness `Ct = 6·e^{14}`. -/
theorem s16_audit_Ct_over_pin : (2 : ℝ) ^ 20 < 6 * Real.exp 14 := by
  have h := s16_audit_exp14_bracket.1
  norm_num
  linarith

/-- ⟦AUDIT⟧ `Ct`'s honest ceiling: `6·e^{14} ≤ 2^23` (14% of room). -/
theorem s16_audit_Ct_ceiling : 6 * Real.exp 14 ≤ (2 : ℝ) ^ 23 := by
  have h := s16_audit_exp14_bracket.2
  norm_num
  linarith

set_option exponentiation.threshold 4000 in
/-- ⟦AUDIT⟧ the `ρ` floor at the WIDE `Kc` ceiling `2^539` (which covers `KExpr_le`). -/
theorem s16_audit_rho_ge_wide {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K)
    (hδb : 1 / 2 ^ 20 ≤ δ₀) (hKb : K ≤ 2 ^ 539) :
    (1 : ℝ) / 2 ^ 581 ≤ doorRhoOfDelta (s12DeltaSock δ₀ K) := by
  rw [doorRhoOfDelta, le_min_iff]
  refine ⟨by norm_num, ?_⟩
  rw [s12DeltaSock_sq hδ hK, div_div, le_div_iff₀ (by positivity)]
  nlinarith [hKb, hδb, hK]

set_option exponentiation.threshold 4000 in
/-- ⟦AUDIT⟧ the clearing charge at the WIDE `Kc` ceiling: `log(1/ρ) ≤ 403` (was `43`). -/
theorem s16_audit_neglog_rho_le_wide {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K)
    (hδb : 1 / 2 ^ 20 ≤ δ₀) (hKb : K ≤ 2 ^ 539) :
    -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 403 := by
  have hge := s16_audit_rho_ge_wide hδ hK hδb hKb
  have h1 : Real.log ((1 : ℝ) / 2 ^ 581)
      ≤ Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) :=
    Real.log_le_log (by norm_num) hge
  have h2 : Real.log ((1 : ℝ) / 2 ^ 581) = -(581 * Real.log 2) := by
    rw [one_div, Real.log_inv, Real.log_pow]
    push_cast; ring
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [h2] at h1
  linarith

set_option exponentiation.threshold 4000 in
/-- ⟦AUDIT, AT SHIFT `h`⟧ **THE `ρ` FLOOR AT THE SCALED `δ₀` PIN** (`s16_audit_rho_ge_wide_h`) —
`s16_audit_rho_ge_wide` with the `h` lane's own pin `1/(2^20·h²) ≤ δ₀` (wave X's exit exports
`1/(838400·h²) ≤ δ₀`, and `838400 ≤ 2^20`).  The floor drops by exactly `h²`, and by nothing
else: `s12DeltaSock`'s square root cancels `doorRhoOfDelta`'s square, so a `h⁻²` pin costs
`h⁻²` in `ρ`, not `h⁻⁴`. -/
theorem s16_audit_rho_ge_wide_h {h : ℕ} (hh : 0 < h) {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K)
    (hδb : 1 / (2 ^ 20 * (h : ℝ) ^ 2) ≤ δ₀) (hKb : K ≤ 2 ^ 539) :
    (1 : ℝ) / (2 ^ 581 * (h : ℝ) ^ 2) ≤ doorRhoOfDelta (s12DeltaSock δ₀ K) := by
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hhsq : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith
  have hh0 : (0 : ℝ) < (h : ℝ) := by linarith
  have hinv : (0 : ℝ) < 1 / (h : ℝ) ^ 2 := by positivity
  rw [doorRhoOfDelta, le_min_iff]
  refine ⟨?_, ?_⟩
  · rw [div_le_one (by positivity)]
    nlinarith [hhsq]
  rw [s12DeltaSock_sq hδ hK, div_div, le_div_iff₀ (by positivity)]
  -- ⟦THE SPLIT⟧ the `h²` is a common factor on both sides; peel it off so the
  -- numeral comparison `1768400 ≤ 2^22` is seen by `nlinarith` on its own.
  have hkey : 1 / (2 : ℝ) ^ 581 * (16 * K * 110525) ≤ 1 / (2 : ℝ) ^ 20 := by
    nlinarith [hKb, hK]
  have hsplit1 : 1 / ((2 : ℝ) ^ 581 * (h : ℝ) ^ 2) * (16 * K * 110525)
      = 1 / (2 : ℝ) ^ 581 * (16 * K * 110525) * (1 / (h : ℝ) ^ 2) := by
    field_simp
  have hsplit2 : 1 / (2 : ℝ) ^ 20 * (1 / (h : ℝ) ^ 2)
      = 1 / ((2 : ℝ) ^ 20 * (h : ℝ) ^ 2) := by
    field_simp
  rw [hsplit1]
  refine le_trans (mul_le_mul_of_nonneg_right hkey hinv.le) ?_
  rw [hsplit2]
  exact hδb

set_option exponentiation.threshold 4000 in
/-- ⟦AUDIT, AT SHIFT `h`⟧ **THE CLEARING CHARGE AT SHIFT `h`** (`s16_audit_neglog_rho_le_wide_h`)
— `log(1/ρ) ≤ 403 + 2·log h`.  The `403` is `581·log 2 = 402.72`; the shift adds `2·log h` and
NOTHING ELSE.  ⛔ This is the number two successive design words priced at `4·log h` and then
`13·log h`: the compose pins `doorRhoOfDelta (s12DeltaSock δ₀ Kc)`, never `doorRhoOfDelta δ₀`,
and the sock's `√` exactly cancels the envelope's square. -/
theorem s16_audit_neglog_rho_le_wide_h {h : ℕ} (hh : 0 < h) {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K)
    (hδb : 1 / (2 ^ 20 * (h : ℝ) ^ 2) ≤ δ₀) (hKb : K ≤ 2 ^ 539) :
    -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 403 + 2 * Real.log (h : ℝ) := by
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hge := s16_audit_rho_ge_wide_h hh hδ hK hδb hKb
  have hpos : (0 : ℝ) < 1 / (2 ^ 581 * (h : ℝ) ^ 2) := by positivity
  have h1 : Real.log ((1 : ℝ) / (2 ^ 581 * (h : ℝ) ^ 2))
      ≤ Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := Real.log_le_log hpos hge
  have h2 : Real.log ((1 : ℝ) / (2 ^ 581 * (h : ℝ) ^ 2))
      = -(581 * Real.log 2) - 2 * Real.log (h : ℝ) := by
    rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow]
    push_cast; ring
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [h2] at h1
  linarith

/-- ⟦AUDIT, AT SHIFT `h`⟧ the charge under the `h`-family's own binder: `hh7 : log h ≤ 7` gives
`403 + 2·log h ≤ 417`.  417 is the number every `ρ`-carrying register line of the `h` lane
spends — 14 more than the `h = 1` lane's 403, for shifts up to `e^7 = 1096`. -/
theorem s16_audit_neglog_rho_le_417_h {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K)
    (hδb : 1 / (2 ^ 20 * (h : ℝ) ^ 2) ≤ δ₀) (hKb : K ≤ 2 ^ 539) :
    -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 417 :=
  le_trans (s16_audit_neglog_rho_le_wide_h hh hδ hK hδb hKb) (by linarith)

/-- ⟦AUDIT⟧ the BINDING `lvl` register line at the wide charge `403` (`s15w2_lvl_num'` at
`43`).  Slack `3.13·10^{10}`: the widened `Kc` ceiling is invisible against `14·λ₊`. -/
theorem s16_audit_lvl_num_wide {X Q Y : ℝ} (hX : X ≤ 987 * 10 ^ 8) (hQ : Q ≤ 277)
    (hY : -Y ≤ 403) :
    26 + 14 * X + 1 / 3 * Q + -Y ≤ 1 / 12 * 24464133718016 * Real.log 2 :=
  by linarith only [Real.log_two_gt_d9, hX, hQ, hY]

/-- ⟦AUDIT⟧ the `anchor` register line at the wide charge, at `M = 2^355`. -/
theorem s16_audit_anchor_wide {X Y : ℝ} (hX : X ≤ 987 * 10 ^ 8) (hY : Y ≤ 403) :
    14 * X + Y + 33 ≤ 39 * 10 ^ 8 * 356 := by linarith

set_option exponentiation.threshold 4000 in
/-- ⟦AUDIT⟧ the `half` window line at the wide charge, at `M = 2^355`. -/
theorem s16_audit_half_wide :
    (7 / 10 : ℝ) * (356 * 2 ^ 391) + 3 * 403 ≤ (2 : ℝ) ^ 400 / 2 := by norm_num

/-- ⟦AUDIT⟧ the `gP1` line at the TRUE `Ct = 6·e^{14}` AND the wide `ρ`-charge. -/
theorem s16_audit_Ct_gP1_room :
    29 + Real.log (6 * Real.exp 14) + 14 * (987 * 10 ^ 8)
      ≤ 24464133718016 * Real.log 2 + -403 := by
  have hlog : Real.log (6 * Real.exp 14) = Real.log 6 + 14 := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero 14), Real.log_exp]
  have h6 : Real.log 6 ≤ 5 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
    linarith
  linarith only [Real.log_two_gt_d9, hlog, h6]

/-- ⟦AUDIT⟧ **THE SECOND WALL** — at `λ₋ ≥ 492` the base-scale cap's demand
`λ₋³ ≤ log(log 𝒫₂) = (K + 413)·log 2` fails at EVERY admissible `K ≤ 1.7·10^8`.  `Hcap`'s own
`budgetFloor` leaf forces `λ₋ ≥ e^{e^{1.04·10^{31}}}`, so `Hcap ≤ s15WitFloor2` and
`S16BaseScaleCap_gk` are jointly unsatisfiable — independently of §6's `Mfl` defect. -/
theorem s16_audit_hcap_wall {lam : ℝ} (hlam : 492 ≤ lam) {K : ℕ} (hK : K ≤ 170000000) :
    ((K : ℝ) + 413) * Real.log 2 < lam ^ 3 := by
  have hKR : (K : ℝ) ≤ 170000000 := by exact_mod_cast hK
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl0 : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hcube : (492 : ℝ) ^ 3 ≤ lam ^ 3 := by gcongr
  nlinarith [hKR, hl2, hl0, hcube]



/-! ## §6.4 — ⟦C4: THE RIDER LANE, PAGE 2⟧ THE `C` RIDER, **PROVEN AND REMOVED**

⟦WHAT THIS SECTION DOES⟧ §6.3's table marks `log C ≤ 40` ✅: the band lemma's coprime-tail
constant IS `TypicalDensity`'s sieve-mass constant, whose value `CgExpr = 2·e^{19/log 2} + 1
= 1.605·10^{12}` carries a KERNEL ceiling `C ≤ 2·10^{12}`
(`ConstantsExposed.typical_density_le_bounded` — a fact about the THEOREM, not merely about a
closed form).  What kept the rider on the hypothesis list was a **WIRING GAP**:
`TypicalPrice.blockfree_sum_le` (hence `M4RowSupply.m4_tail_mass_at_band`, hence §4's supply)
reads the UNBOUNDED root `typical_density_le`, so the numeral never reached the `∃` that
`s15_crossing_supplied_gk` hands up.

The gap closes with two `_bounded` twins in the `CgPin` genre — each is its landed statement
with ONE conjunct inserted and its landed body replayed verbatim underneath against the
bounded root — and a re-run of §4 and §6.2 on them.  The terminal
`logChowla2_witnessed_scale_final'_Cproven` has `log C ≤ 40` OUT of the hypothesis list and
IN the `∃`-prefix: REMOVED-BECAUSE-PROVEN, the fourth such after `ε`, `δ₀`, `Cg`.

⟦THE MARGIN⟧ `log(1.605·10^{12}) = 28.11`, the ceiling is `40`: 11.9 nats spare.  The
kernel charges the crude route `C ≤ 2·10^{12} ≤ 2^{41}`, i.e. `log C ≤ 41·log 2 = 28.42`.

⚠ ⟦WHAT THIS DOES **NOT** TOUCH⟧ the band-lane constant of §6.5 is a DIFFERENT constant
(`MlambdaChi_rate`'s, through `MmuChiRate`'s opaque `C_mu`); this section says nothing about
it, and §6.5 carries it as a named rider.

**PURELY ADDITIVE.**  No landed declaration is touched. -/

/-- ⟦AUDIT⟧ the rider's arithmetic: `0 < C ≤ 2·10^{12} ⟹ log C ≤ 40`, charged through
`2·10^{12} ≤ 2^{41}` (`log C ≤ 41·log 2 = 28.42`; 11.6 nats spare at the ceiling). -/
theorem s16_audit_logC_le {C : ℝ} (hC0 : 0 < C) (hCle : C ≤ 2 * 10 ^ 12) :
    Real.log C ≤ 40 := by
  have h41 : (2 : ℝ) * 10 ^ 12 ≤ (2 : ℝ) ^ (41 : ℕ) := by norm_num
  have hstep : Real.log C ≤ Real.log ((2 : ℝ) ^ (41 : ℕ)) :=
    Real.log_le_log hC0 (le_trans hCle h41)
  rw [Real.log_pow] at hstep
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  push_cast at hstep
  linarith

/-- **THE WIRED TWIN of `TypicalPrice.blockfree_sum_le`** — the landed statement with the
conjunct `C ≤ 2·10^{12}` inserted after `0 < C`, and the landed body replayed verbatim
against `ConstantsExposed.typical_density_le_bounded` in place of `typical_density_le`.
⟦THE ONE CHANGE⟧ the `obtain`/`refine` line; every step below is byte-identical to
`TypicalPrice.lean:138–215`. -/
theorem blockfree_sum_le_bounded :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 * 10 ^ 12 ∧ ∀ (P Q W N : ℕ) (a : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ W →
      100 * Real.log Q ≤ Real.log W →
      ((Nat.sqrt W : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (W : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) →
      (∀ n, a n ≠ 0 → W ≤ n ∧ n ≤ 2 * W) →
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
          ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ C * (Real.log P / Real.log Q) / (W : ℝ) + 1 / (W : ℝ) ^ 2 := by  classical
  obtain ⟨C, hC, hCle, hden⟩ := typical_density_le_bounded
  refine ⟨C, hC, hCle, ?_⟩
  intro P Q W N a hP hPQ hW hgate herr ha hsupp
  have hW0 : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  -- ⟦STEP 1: only the window shell survives, and there `‖a n‖² ≤ 1`⟧
  have hpt : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
      ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ (if n ∈ Finset.Icc W (2 * W) then 1 / (n : ℝ) ^ 2 else 0) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1.1
    by_cases hmem : n ∈ Finset.Icc W (2 * W)
    · rw [if_pos hmem]
      have h1 : ‖a n‖ ^ 2 ≤ 1 := by
        have := ha n
        nlinarith [norm_nonneg (a n)]
      exact div_le_div_of_nonneg_right h1 (by positivity) |>.trans_eq rfl
    · rw [if_neg hmem]
      have haz : a n = 0 := by
        by_contra hne
        exact hmem (Finset.mem_Icc.mpr (hsupp n hne))
      rw [haz]
      simp
  have hstep1 : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ ∑ n ∈ ((Finset.Icc W (2 * W)).filter (fun n => blockOmega P Q n = 0)),
          1 / (n : ℝ) ^ 2 := by
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.2, hn.1.2⟩
  -- ⟦STEP 2: peel the endpoint `n = W`, which `Ioc W (2W)` misses⟧
  have hsub : (Finset.Icc W (2 * W)).filter (fun n => blockOmega P Q n = 0)
      ⊆ insert W ((Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases eq_or_lt_of_le hn.1.1 with h | h
    · exact Finset.mem_insert.mpr (Or.inl h.symm)
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨h, hn.1.2⟩, hn.2⟩
  have hnotmem : W ∉ (Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0) := by
    simp
  have hstep2 : ∑ n ∈ ((Finset.Icc W (2 * W)).filter (fun n => blockOmega P Q n = 0)),
        1 / (n : ℝ) ^ 2
      ≤ 1 / (W : ℝ) ^ 2
        + ∑ n ∈ ((Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0)),
            1 / (n : ℝ) ^ 2 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)).trans ?_
    rw [Finset.sum_insert hnotmem]
  -- ⟦STEP 3: the shell, by the density⟧
  have hcard : (((Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0)).card : ℝ)
      ≤ C * (Real.log P / Real.log Q) * W := by
    refine le_trans ?_ (hden P Q W hP hPQ hgate herr)
    have : ((Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0)).card
        ≤ ((Finset.Ioc W (2 * W)).filter (fun n => (bandProd P Q).Coprime n)).card := by
      refine Finset.card_le_card ?_
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
      exact ⟨hn.1, coprime_bandProd_of_blockOmega_zero (by omega) hn.2⟩
    exact_mod_cast this
  have hshell : ∑ n ∈ ((Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0)),
        1 / (n : ℝ) ^ 2
      ≤ C * (Real.log P / Real.log Q) / (W : ℝ) := by
    have hterm : ∀ n ∈ ((Finset.Ioc W (2 * W)).filter (fun n => blockOmega P Q n = 0)),
        1 / (n : ℝ) ^ 2 ≤ 1 / (W : ℝ) ^ 2 := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      have hnW : (W : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1.1.le
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have hb := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [nsmul_eq_mul] at hb
    refine hb.trans ?_
    have hmul := mul_le_mul_of_nonneg_right hcard
      (by positivity : (0 : ℝ) ≤ 1 / (W : ℝ) ^ 2)
    refine hmul.trans (le_of_eq ?_)
    field_simp
  linarith [hstep1, hstep2, hshell]

/-- **THE WIRED TWIN of `M4RowSupply.m4_tail_mass_at_band`** — the band lemma's `∃` now
carries the rider itself: `log C ≤ 40`.  This is the object §4's supply consumes, so the
rider stops being a hypothesis of the final theorem and becomes a conjunct of its prefix. -/
theorem m4_tail_mass_at_band_bounded :
    ∃ C : ℝ, 0 < C ∧ Real.log C ≤ 40 ∧ ∀ (P Q Xd N : ℕ) (a : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd →
      100 * Real.log Q ≤ Real.log Xd →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) →
      (∀ n, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
          ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2 := by
  obtain ⟨C, hC0, hCle, hbf⟩ := blockfree_sum_le_bounded
  exact ⟨C, hC0, s16_audit_logC_le hC0 hCle, hbf⟩

set_option maxHeartbeats 1000000 in
-- the eighteen-slot `hcapWS` family re-elaborates against the wire's own shape (§4's cause)
/-- **§4 AT THE BOUNDED BAND LEMMA** (`s15_crossing_supplied_bounded_gk`) —
`s15_crossing_supplied_gk` with `Real.log C ≤ 40` moved from the inner implication's
hypothesis list into the `∃`-prefix.  The body is §4's, verbatim, reading the prefix's own
`hC40` where §4 read its hypothesis. -/
theorem s15_crossing_supplied_bounded_gk (K : ℕ) :
    ∃ Cq cs T₀ Kq Ks C : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      (1 ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ (R : ChowlaRegime) (M : ℕ), 1 ≤ M → loglogFloor50 ≤ R.Hlo →
          (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor_gk K M ≤ A + s) →
          S16CofactorSupply_gk K Cq R M → S16BaseScaleCap_gk K R M →
          S15CrossingBound_gk K R M) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs0, hT₀3, hKq0, hKs0, hwire⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨C, hC0, hC40, hband⟩ := m4_tail_mass_at_band_bounded
  refine ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro hcs hT₀ hKq hKs R M hM hfl hblk hcof hcap
  have hgate := s16_capGate_supply_gk K hM hfl hcs hblk hT₀ hKq hKs hC0 hC40
    (fun _ => le_rfl) hcap hcof
  refine hwire R M liouvilleC (fun _ => theta293 - 1 / 500) liouvilleC_norm_le_one ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨P, Q, Rrad, Rbd, CR, EP2, hg⟩ := hgate H L q j A s hsb T hTlo hThi hTgate hTll
  have hq : 1 ≤ q := hsb.2.2.2.1
  have hA : 0 < A := hsb.2.2.2.2.2.2.2.1
  have hNd : 1 ≤ A + s := by omega
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by have := hg.logX_eight; linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
  have hT1 : (1 : ℝ) < 2 * T := by linarith
  exact doorCapBundle_at_workingPoint_perBlock_gk K hband hM hNd hq hg hT1 hThi hTll

set_option maxHeartbeats 1000000 in
-- the twin's eighteen-binder prefix re-elaborates beside the crossing supply's six constants
/-- **⟦THE TERMINAL, `C` PROVEN⟧** (`logChowla2_witnessed_scale_final'_Cproven`) — §6.2's
repaired terminal with the band-lemma rider `log C ≤ 40` REMOVED-BECAUSE-PROVEN: it now rides
the `∃`-prefix (fourth after `Cg ≤ 2·10^{12}`, `1/500 ≤ ε`, `1/838400 ≤ δ₀`).

⟦THE HYPOTHESIS LIST, EXACT⟧ `Kc ≤ 2^20`, `Ct ≤ 2^20`, `x₀ ≤ e^{e^{275}}` (Siegel),
`Mfl ≤ 2^355` (⚠ §6's first wall — dischargeable at the `K`-free band constant; see §6.5),
`Hcap ≤ s15WitFloor2` (⚠ §6.3's second wall), `1 ≤ cs`, `T₀ ≤ e^{e^{100}}`, `Kq ≤ e^{100}`,
`e^{−100} ≤ Ks`, plus `S16CofactorSupply_gk` and `S16BaseScaleCap_gk`.  `log C ≤ 40` is GONE
from that list. -/
theorem logChowla2_witnessed_scale_final'_Cproven :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Real.log C ≤ 40 ∧
      (Kc ≤ 2 ^ 20 → Ct ≤ 2 ^ 20 → (x₀ : ℝ) ≤ Real.exp (Real.exp 275) → Mfl ≤ 2 ^ 355 →
        Hcap ≤ s15WitFloor2 →
        1 ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, ∃ (R : ChowlaRegime) (M : ℕ),
          R.eps = ε ∧ R.Hlo = s15WitFloor2 ∧ g R.Hhi R.ω ≤ R.x ∧
          S15Sel''_gk 32000000 Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M ∧
          (S16CofactorSupply_gk 32000000 Cq R M → S16BaseScaleCap_gk 32000000 R M →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1, hCgle, hεpin,
    hδpin, hbody⟩ := logChowla2_conditional_sharp2_nonvacuous_gk' 32000000 (by norm_num)
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40, hsupply⟩ :=
    s15_crossing_supplied_bounded_gk 32000000
  refine ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0,
    hCgle, hεpin, hδpin, hC40, ?_⟩
  intro h4 h5 h6 h7 h8 hcs hT₀ hKq hKs g
  obtain ⟨R, M, hReps, hHlo, hRg, hsel, hfire⟩ := hbody h4 h5 h6 h7 h8 g
  refine ⟨R, M, hReps, hHlo, hRg, hsel, ?_⟩
  intro hcof hcap
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact s15WitFloor2_ll
  have hblk : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      s13BlockFloor_gk 32000000 M ≤ A + s := by
    intro H L q j A s hb
    exact s15_block_at_socket_gk 32000000 hb
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (hsupply hcs hT₀ hKq hKs R M hsel.hM hfl hblk hcof hcap)


/-! ## §6.5 — ⟦W5: THE BAND-LANE `C` RIDER AND THE `Mfl` DISCHARGE⟧

⟦THE SETTING⟧ `LEVEL2-PROD` re-witnessed `S11Hoist.m4_hband_at_door_slot_split_graded_gk`'s
band constant at the PER-BLOCK price `Cb = C·4^{Aexp}·(e^{52.5}·4^{1.05}) + 1` — **`K`-free**,
where the covering-window price carried `2^{1.05K}`.  `S11HoistGrade.
s11_grade_floor_hoistCb_prod_le` then prices the exported floor: `s11GradeFloor Cb ≤ 2^{355}`
whenever `0 < C` and `log C ≤ 40`, with 49 orders of margin (`Mfl ≤ 10^{58}` against
`2^{355} = 7.3·10^{106}`).  §6's FIRST WALL — `Mfl` vs the base-scale cap, jointly
unsatisfiable at every `K` — is therefore DEAD as an arithmetic obstruction.  What remained
was plumbing: `Mfl` is a `Classical.choose` five hops below this file.  §6.5 does that
plumbing.

⟦THE RIDER, NAMED HONESTLY⟧ `S16BandLaneCBounded K` is `log C ≤ 40` **on the band lane's own
constant** — a DIFFERENT constant from §6.4's coprime-tail `C` (which is now proven).  This
`C` descends `M4T0DatumDischarge.m4_hT0band_at_door_discharged_split_graded_prod_gk` ←
`m4_hpiece_at_door_split_graded_prod_gk` ← `piece_partial_sum_rate_split_graded_prod` ←
`LambdaRateTwisted.MlambdaChi_rate` (`:711`: `refine ⟨2·C_mu·4^A + 1, …⟩`), where `C_mu` is
the `∃`-witness of the slot `MmuChiRate` — a `Prop` whose constant is opaque even though the
slot itself is LANDED (`PortClose.mmuChiRate_holds_gated`).  No theorem of the corpus bounds
it, so it is CARRIED, and carried where the band chain's `∃` produces it: the rider is
exactly the graded hoist's own statement, at its own witness shape, with `log C ≤ 40` beside
`0 < C`.  It is minted TWICE — at the hoist (`S16BandLaneCBounded`, what the hops consume)
and one hop lower at the site that actually mints the constant (`S16BandT0CBounded`, the
`M4T0DatumDischarge` `∃`) — and the bridge `s16_bandRider_of_T0CBounded` derives the first
from the second by the landed hoist's own proof.  So the whole discharge rests on ONE
inequality about ONE named constant, kernel-visibly.  ⟦WHAT WOULD DISCHARGE IT⟧ a `_bounded`
twin of the `MlambdaChi_rate` chain (five links) once `MmuChiRate`'s witness is exposed with
a numeral — the same genre as §6.4's, and the cheapest open item of this lane.

⟦THE PLUMBING CHOICE, DOCUMENTED⟧ the alternative was to carry the rider at the terminal
only, as a bare `log Cband ≤ 40` on a constant the `∃`-prefix would have to export.  That
needs the SAME six hops (the prefix must carry `Cband` up), so it is not cheaper — and it is
weaker, since it would export a constant no consumer can identify.  The form chosen here
threads ONE proposition and converts the terminal's `Mfl ≤ 2^355` into a PROVEN prefix
conjunct at every hop, which is what "removed-because-proven" means.

⟦THE SIX HOPS⟧ `S11Hoist:1329` (the re-witness, landed) → the rider + its bridge (this
section) →
`logChowla2_capstone_final_const'_graded_gk_pinned_Mfl` (the cost centre: the ~120-line
statement, at `Aexp := s13Aexp`) → `logChowla2_conditional_sharp2_atK_gk_pinned_Mfl` →
`logChowla2_conditional_sharp2_nonvacuous_gk'_Mfl` (where `Mfl ≤ 2^355` LEAVES the
hypothesis list) → `logChowla2_witnessed_scale_final'_v2`.

**PURELY ADDITIVE.**  No landed declaration is touched. -/

section BandRider

open MeasureTheory

/-- **⟦THE BAND-LANE `C` RIDER⟧** (`S16BandLaneCBounded`) — the graded hoist
(`S11Hoist.m4_hband_at_door_slot_split_graded_gk` at `Aexp := s13Aexp`, whose `LEVEL2-PROD`
witness is written out here) with ONE conjunct added: `log C ≤ 40` on the band lane's opaque
constant.

Everything BUT that conjunct is a THEOREM (the landed hoist proves it verbatim at this very
witness); the conjunct is the honest rider, on `MlambdaChi_rate`'s `2·C_mu·4^A + 1` through
`MmuChiRate`'s opaque `C_mu`.  Under it, `s11_grade_floor_hoistCb_prod_le` gives
`Mfl = s11GradeFloor Cb ≤ 2^355` at 49 orders of margin. -/
def S16BandLaneCBounded (K : ℕ) : Prop :=
  ∃ (x₀ : ℕ) (Cband : ℝ), 0 < Cband ∧ Real.log Cband ≤ 40 ∧ ∀ (M : ℕ), 1 ≤ M →
    ∃ C' : ℝ, 0 < C' ∧
      C' ≤ (Cband * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1)
          * (M : ℝ) ^ (2.1 : ℝ) ∧
      ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
        ((∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
            DoorBandBase_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
          ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
            ∀ χ : DirichletCharacter ℂ q,
              (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                ≤ t0BandB (((A + s : ℕ)) : ℝ)
                    (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))


/-- **⟦THE RIDER'S PROVENANCE, KERNEL-VISIBLE⟧** (`S16BandT0CBounded`) — the same rider one
hop LOWER, at the `∃` that actually MINTS the opaque constant:
`M4T0DatumDischarge.m4_hT0band_at_door_discharged_split_graded_prod_gk` (:1417) at
`A := s13Aexp`, with `Real.log C ≤ 40` inserted after `0 < C`.  Every other conjunct is a
LANDED THEOREM at this very `C`; this def differs from that theorem by exactly one
inequality. -/
def S16BandT0CBounded (K : ℕ) : Prop :=
∃ (x₀ : ℕ) (C : ℝ), 0 < C ∧ Real.log C ≤ 40 ∧ ∀ (P Q P₁ Q₁ P₂ Q₂ : ℕ), 4 ≤ P → P ≤ Q →
    4 ≤ P₁ → P₁ ≤ Q₁ → 4 ≤ P₂ → P₂ ≤ Q₂ →
    ∃ C' : ℝ, 0 < C' ∧
      C' ≤ C * (4 : ℝ) ^ s13Aexp * (windowMassConst P₁ Q₁ * windowMassConst P₂ Q₂) + 1 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X C₁ M₀ : ℝ},
        ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
        x₀ ≤ Xd → 16 ≤ Xd →
        (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
        (∀ j ∈ Finset.Icc 1 2, P ≤ calP (Adoor M) (s13GK K M) j) →
        (∀ j ∈ Finset.Icc 1 2, calQK (Adoor M) (s13GK K M) M j ≤ Q) →
        (∀ j ∈ Finset.Icc 1 2,
            (P₁ ≤ calP (Adoor M) (s13GK K M) j
                ∧ calQK (Adoor M) (s13GK K M) M j ≤ Q₁)
              ∨ (P₂ ≤ calP (Adoor M) (s13GK K M) j
                ∧ calQK (Adoor M) (s13GK K M) M j ≤ Q₂)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          16 * s13Aexp * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          8 * s13Aexp * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          Real.exp (2 * Real.exp 1
              * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
            ≤ (Real.log (k : ℝ)) ^ s13Aexp) →
        8 * C' ≤ (Real.log X) ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) →
        4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
            ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
        (∫ t in (-(seamT0 X))..(seamT0 X),
            ‖dpolyA (winCutH Xd (doorChiCoeff_gk K χ M)) (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X (cfbC₁ X C₁) M₀

/-- **⟦THE BRIDGE⟧** (`s16_bandRider_of_T0CBounded`) — the T0-band rider IMPLIES the band-lane
rider, by `S11Hoist.m4_hband_at_door_slot_split_graded_gk`'s own proof (:1345–1388) replayed
at `Aexp := s13Aexp` against the assumed `∃` instead of the landed one.  ⟦WHAT THIS BUYS⟧ the
whole `Mfl` discharge now rests on ONE inequality about ONE named constant — `log C ≤ 40` at
`M4T0DatumDischarge`'s witness — and nothing else: the shape of `Cb`, the `M^{2.1}` slope and
the band conclusion are all landed. -/
theorem s16_bandRider_of_T0CBounded (K : ℕ) (hT0 : S16BandT0CBounded K) :
    S16BandLaneCBounded K := by
  obtain ⟨x₀, C, hCpos, hC40, hsplit⟩ := hT0
  refine ⟨x₀, C, hCpos, hC40, ?_⟩
  intro M hM
  obtain ⟨hP4, hPQ⟩ := door_window_bounds_gk K M hM
  obtain ⟨hP4₁, hPQ₁⟩ := door_block_bounds_gk K M hM (j := 1) le_rfl
  obtain ⟨hP4₂, hPQ₂⟩ := door_block_bounds_gk K M hM (j := 2) (by norm_num)
  obtain ⟨C', hC'pos, hC'le, hband⟩ := hsplit
    (calP (Adoor M) (s13GK K M) 1) (calQK (Adoor M) (s13GK K M) M 2)
    (calP (Adoor M) (s13GK K M) 1) (calQK (Adoor M) (s13GK K M) M 1)
    (calP (Adoor M) (s13GK K M) 2) (calQK (Adoor M) (s13GK K M) M 2)
    hP4 hPQ hP4₁ hPQ₁ hP4₂ hPQ₂
  obtain ⟨hcovP, hcovQ⟩ := door_cover_gk K M hM
  have hcovB := door_block_cover_gk K M
  refine ⟨C', hC'pos, ?_, ?_⟩
  · -- ⟦THE ABSORPTION⟧ the per-block mass, priced in `M` — `K`-FREE
    have hmass := s11_windowMassConst_door_prod_le_gk K M hM
    have hone := s11_one_le_rpow_M M hM
    have hstep : C * (4 : ℝ) ^ (s13Aexp)
        * (windowMassConst (calP (Adoor M) (s13GK K M) 1) (calQK (Adoor M) (s13GK K M) M 1)
            * windowMassConst (calP (Adoor M) (s13GK K M) 2)
                (calQK (Adoor M) (s13GK K M) M 2))
        ≤ C * (4 : ℝ) ^ (s13Aexp)
            * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ)) := by
      have hcoef : (0 : ℝ) ≤ C * (4 : ℝ) ^ (s13Aexp) := by positivity
      exact mul_le_mul_of_nonneg_left hmass hcoef
    have hexp : (C * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1)
        * (M : ℝ) ^ (2.1 : ℝ)
        = C * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ))
          + (M : ℝ) ^ (2.1 : ℝ) := by ring
    linarith
  · intro R C₁ M₀ hgates H L q j A s hb χ
    have hq : 0 < q := hb.2.2.2.1
    haveI : NeZero q := ⟨hq.ne'⟩
    have hD := hgates H L q j A s hb
    have h16 : 16 ≤ A + s := by
      have h400 : (400 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := hD.X400
      have : (16 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by linarith
      exact_mod_cast this
    exact hband q χ M (A + s) (2 * (A + s)) rfl hD.X400 (by omega) le_rfl hD.C₁_one
      hD.x₀_le h16 hD.qfit hcovP hcovQ hcovB hD.gHalf hD.gO1 hD.gWin hD.grade hD.err

set_option maxHeartbeats 1000000 in
-- ⟦HOP 3, THE COST CENTRE⟧ the ~120-line residue re-elaborates against the re-cut prefix
-- (the landed twin's own cause); the statement gains ONE conjunct and pins `Aexp := s13Aexp`.
/-- **⟦HOP 3⟧** (`logChowla2_capstone_final_const'_graded_gk_pinned_Mfl`) —
`S12ConstCompose.logChowla2_capstone_final_const'_graded_gk_pinned` (:1460) at
`Aexp := s13Aexp`, with the band leg taken from the rider instead of
`m4_fuse_hband_of_bandBase_graded_gk`, and ONE conjunct added to the `∃`-prefix:
`Mfl ≤ 2^355`, discharged by `s11_grade_floor_hoistCb_prod_le` at the rider's `C`.  The proof
is the landed one, byte-for-byte, except the band `obtain` and the two `refine`s that name
the floor. -/
theorem logChowla2_capstone_final_const'_graded_gk_pinned_Mfl (K : ℕ)
    (hK : K ≤ 170000000) (hband : S16BandLaneCBounded K) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks : ℝ) (x₀ Hcap Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
        ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
          ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
            R.Hlo ≤ max Hcap U1floor ∧
            ∀ (M : ℕ), Mfl ≤ M →
              ∃ C' : ℝ, 0 < C' ∧
                8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
                    ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                  -- ⟦A⟧ THE SPINE ARITHMETIC
                  M4DoorGates_gk K Cg R M k δ₀ →
                  8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloor M : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    arcDen 12 H < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    m4SmallGradeFits (doorRowFloor M)
                      (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                      (fun H => 2 * rStrWitness H) H) →
                  -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    GRowsZeroGate'''_gk K M (A + s) Cp
                      (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                        + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                      ≤ (theta293 - epsrf (A + s))
                          * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                      * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    calQK (Adoor M) (s13GK K M) M 2 ≤ A + s ∧
                      Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
                          ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                      ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                  -- ⟦B4 RAW⟧ the crossing bound, carried
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                      (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                      5 ≤ Real.log (Real.log (2 * T)) →
                      (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                          ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                        ≤ 8 * (0 : ℝ) ^ 2
                          + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                \ seamBall (((A + s : ℕ)) : ℝ) 0)
                              ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                  (calP (Adoor M) (s13GK K M))
                                  (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                                  (mrAlpha (1 / 12)) 2,
                              ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                          + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                              * (Real.log (((A + s : ℕ)) : ℝ))
                                  ^ (-theta293 + epsrf (A + s)))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorBandBase_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Hcap, hCg, hCgle, hε, hKc, hδ₀, hεpin, hδpin, hroad⟩ :=
    m4_second_road_L2_hloCap_pinned_gk K
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_gk K hK
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cband, hCband0, hCband40, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀,
    max Hcap (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, s11_grade_floor_hoistCb_prod_le Cband hCband0 hCband40, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hMfloor
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, s11_grade_absorption' _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorRowZeroBase_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (Adoor M) (s13GK K M))
          (calQK (Adoor M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (Adoor M) (s13GK K M))
        (calQK (Adoor M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hρpos (fun i m => norm_doorPunctCoeffU_le_one_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloor M ≤ j →
      m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloor M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloor M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloor M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloor M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloor M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
    have hKcpos : (0 : ℝ) < 16 * Kc := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]



set_option maxHeartbeats 1000000 in
-- ⟦HOP 4⟧ same cause as the landed §GK.10-PINNED: the residue re-elaborates against the prefix
/-- **⟦HOP 4⟧** (`logChowla2_conditional_sharp2_atK_gk_pinned_Mfl`) —
`S15Compose.logChowla2_conditional_sharp2_atK_gk_pinned` (:2757) reading HOP 3's twin, so the
`∃`-prefix carries `Mfl ≤ 2^355` one level higher.  Proof: the landed one, with `hMflb`
threaded through the `obtain`/`refine`. -/
theorem logChowla2_conditional_sharp2_atK_gk_pinned_Mfl (K : ℕ) (hK : K ≤ 170000000)
    (hband : S16BandLaneCBounded K) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
        ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          ∀ M : ℕ, S15Sel''_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
            S15CrossingBound_gk K R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀, Hcap, Mfl, hCg, hε, hKc, hδ₀, hCt, hCq,
    hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hMflb, hmain⟩ :=
    logChowla2_capstone_final_const'_graded_gk_pinned_Mfl K hK hband
  refine ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCgle, hεpin, hδpin, hMflb, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  -- ⟦THE BASE PIN⟧ `R.Hlo = U1floor`
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor
  intro hcap
  -- ⟦the two scale floors⟧
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) ^ ((9 : ℝ) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  -- ⟦the arm, both halves⟧
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the RESTORED anchor
  have harith := s15_doorArithFrameRho_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_of_halfWindow_gk K hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register, at the RESTORED `x0_le`⟧
  have hgate : S13BandGate'_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_gk K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor le_rfl (s13_g2_jfloor_of_MSelect'_gk K hsel.hM (by linarith) hS))
    (s15_gate8_gk K le_rfl (s13_gate8_of_MSelect'_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gk K hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_gk K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket hfl hb hlam50 htow hsel.rho le_rfl)
    (fun H L q j A s hb => s15_heps293_at_socket hfl hb hρ0 hlam50 htow hsel.rho)
    (fun H L q j A s hb => s15_hband4096_at_socket hfl hb hρ0 hlam50 htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_gk K hsel.hM (hgate.block H L q j A s hb) hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith


set_option exponentiation.threshold 4000 in
-- the `2^355` register numerals: `S15Witness` sets this file-wide, `S16Budget` per-theorem
/-- **⟦HOP 5 — `Mfl` LEAVES THE HYPOTHESIS LIST⟧**
(`logChowla2_conditional_sharp2_nonvacuous_gk'_Mfl`) — `S15Witness.
logChowla2_conditional_sharp2_nonvacuous_gk'` (:1858) reading HOP 4's twin.  This is the hop
where the discharge is SPENT: `Mfl ≤ 2^355` arrives as a prefix conjunct and is handed
straight to `s15_sel''_witness_gk'`, so the inner implication no longer asks for it.  ⚠
`hx0win` rides as before: `x₀` is Siegel-ineffective and NO theorem discharges it. -/
theorem logChowla2_conditional_sharp2_nonvacuous_gk'_Mfl (Klev : ℕ)
    (hKle : Klev ≤ 170000000) (hband : S16BandLaneCBounded Klev) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      (Kc ≤ 2 ^ 20 → Ct ≤ 2 ^ 20 → (x₀ : ℝ) ≤ Real.exp (Real.exp 275) →
        Hcap ≤ s15WitFloor2 →
        ∀ g : ℕ → ℕ → ℕ, ∃ (R : ChowlaRegime) (M : ℕ),
          R.eps = ε ∧ R.Hlo = s15WitFloor2 ∧ g R.Hhi R.ω ≤ R.x ∧
          S15Sel''_gk Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M ∧
          (S15CrossingBound_gk Klev R M → ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1, hCgle, hεpin,
    hδpin, hMflb, hbody⟩ :=
    logChowla2_conditional_sharp2_atK_gk_pinned_Mfl Klev hKle hband
  refine ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1, hCgle, hεpin,
    hδpin, hMflb, ?_⟩
  intro hKcb hCtb hx0b hHcap g
  -- ⟦THE THREE DISCHARGES⟧ the pinned road's own conjuncts, spent
  have hεb : (1 : ℚ) / 2 ^ 9 ≤ ε := le_trans (by norm_num) hεpin
  have hδb : (1 : ℝ) / 2 ^ 20 ≤ δ₀ := le_trans (by norm_num) hδpin
  have hbfl : 24 * Cg / δ₀ ≤ (2 : ℝ) ^ 355 := by
    rw [div_le_iff₀ hδ₀]
    have hnum : (24 : ℝ) * Cg ≤ 48 * 10 ^ 12 := by linarith
    have hkey : (48 : ℝ) * 10 ^ 12 ≤ (2 : ℝ) ^ 355 * (1 / 838400) := by norm_num
    have hmono : (2 : ℝ) ^ 355 * (1 / 838400) ≤ (2 : ℝ) ^ 355 * δ₀ :=
      mul_le_mul_of_nonneg_left hδpin (by positivity)
    linarith
  have hU : max Hcap (max arcFloor36 loglogFloor50) ≤ s15WitFloor2 := by
    have h1 := s15WitFloor2_arc
    have h2 := s15WitFloor2_ll
    omega
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hfire⟩ := hbody s15WitFloor2 g hU
  have hlo : (2 : ℝ) ^ 400 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact s15WitFloor2_log_ge
  have h50 : (50 : ℝ) ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) := by
    rw [hHlo]; exact s15WitFloor2_loglog_ge
  have hlam : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 2772589 / 10000 := by
    rw [hHlo]; exact s15WitFloor2_loglog_le
  have hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 987 * 10 ^ 8 := by
    refine le_trans (hRtow h50) ?_
    exact s15w2_tower_bound (by linarith) hlam
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by rw [hReps]; exact hεb
  have hwit := s15_sel''_witness_gk' Klev hKle hδ₀ hδb hKc hKcb hCt hCtb hbfl
    hMflb hx0b heps hlo hhi
  exact ⟨R, 2 ^ 355, hReps, hHlo, hRg, hwit, hfire (2 ^ 355) hwit⟩


set_option maxHeartbeats 1000000 in
-- the twin's seventeen-binder prefix re-elaborates beside the crossing supply's six constants
/-- **⟦HOP 6 — THE DELIVERABLE⟧** (`logChowla2_witnessed_scale_final'_v2`) — §6.4's
`logChowla2_witnessed_scale_final'_Cproven` with `Mfl ≤ 2^355` ALSO gone from the hypothesis
list, REMOVED-BECAUSE-PROVEN under the band-lane rider `S16BandLaneCBounded 32000000`
(honestly: `log C ≤ 40` on `MlambdaChi_rate`'s opaque constant — §6.5's header traces it to
`MmuChiRate`'s `C_mu`, which no theorem of the corpus bounds; `s16_bandRider_of_T0CBounded`
traces it to the single inequality `log C ≤ 40` at `M4T0DatumDischarge`'s own witness).
`Mfl ≤ 2^355` now rides the `∃`-prefix, where a consumer reads it off.

⟦THE HYPOTHESIS LIST, EXACT AND COMPLETE⟧ the inner implication asks for, in order:

* `Kc ≤ 2^20` — ⛔ FALSE at the witness (`≈ 2^538`); free at the wide ceiling `2^539`
  (§6.3's audit page: all four charge-spending register lines close at `−log ρ ≤ 403`);
* `Ct ≤ 2^20` — ⛔ FALSE at the witness (`6·e^{14} = 2^{22.78}`); free at `2^23`;
* `(x₀ : ℝ) ≤ e^{e^{275}}` — ⟦`hx0win`⟧ **the Siegel item**, undischargeable on this road;
* `Hcap ≤ s15WitFloor2` — ⛔ **THE WALL'S SECOND/THIRD FACE** (`budgetFloor`'s height-3
  tower; `HCAP-SCOPE` 2026-07-31); NOT relaxable, and the campaign's open design question;
* `1 ≤ cs` — ⛔ FALSE as stated (`cs ≤ 1/10` is a landed proof line); repair = carry `cs`
  through the `0.068` `μ`-margin;
* `T₀ ≤ e^{e^{100}}`, `Kq ≤ e^{100}`, `e^{−100} ≤ Ks` — the fuse's three, `Kq` TRUE with 46
  orders spare, `Ks` a second Siegel item, `T₀` forced-equality with three opaque leaves;
* `S16CofactorSupply_gk`, `S16BaseScaleCap_gk` — ⟦RULING 9⟧'s shelved debt and §2's cap.

⟦WHAT LEFT THE LIST, EACH REMOVED-BECAUSE-PROVEN⟧ `(1:ℚ)/2^9 ≤ ε`, `1/2^20 ≤ δ₀`,
`24·Cg/δ₀ ≤ 2^355` (§6.2), `log C ≤ 40` on the coprime-tail constant (§6.4), and now
`Mfl ≤ 2^355` (§6.5).  ⟦WHAT IS TRADED FOR THE LAST⟧ the rider `S16BandLaneCBounded`, which
is NOT a theorem — it is the band lane's own opaque constant, named.  The trade is honest
because the first wall was an ARITHMETIC conflict (`Mfl` vs the base-scale cap, jointly
unsatisfiable at every `K`) and it is now GONE: at the `K`-free per-block witness the floor
is `≤ 10^{58}` against `2^{355} = 7.3·10^{106}`, 49 orders clear, for ANY `K`. -/
theorem logChowla2_witnessed_scale_final'_v2 (hband : S16BandLaneCBounded 32000000) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Real.log C ≤ 40 ∧
      Mfl ≤ 2 ^ 355 ∧
      (Kc ≤ 2 ^ 20 → Ct ≤ 2 ^ 20 → (x₀ : ℝ) ≤ Real.exp (Real.exp 275) →
        Hcap ≤ s15WitFloor2 →
        1 ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, ∃ (R : ChowlaRegime) (M : ℕ),
          R.eps = ε ∧ R.Hlo = s15WitFloor2 ∧ g R.Hhi R.ω ≤ R.x ∧
          S15Sel''_gk 32000000 Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M ∧
          (S16CofactorSupply_gk 32000000 Cq R M → S16BaseScaleCap_gk 32000000 R M →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1, hCgle, hεpin,
    hδpin, hMflb, hbody⟩ :=
    logChowla2_conditional_sharp2_nonvacuous_gk'_Mfl 32000000 (by norm_num) hband
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40, hsupply⟩ :=
    s15_crossing_supplied_bounded_gk 32000000
  refine ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0,
    hCgle, hεpin, hδpin, hC40, hMflb, ?_⟩
  intro h4 h5 h6 h8 hcs hT₀ hKq hKs g
  obtain ⟨R, M, hReps, hHlo, hRg, hsel, hfire⟩ := hbody h4 h5 h6 h8 g
  refine ⟨R, M, hReps, hHlo, hRg, hsel, ?_⟩
  intro hcof hcap
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact s15WitFloor2_ll
  have hblk : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      s13BlockFloor_gk 32000000 M ≤ A + s := by
    intro H L q j A s hb
    exact s15_block_at_socket_gk 32000000 hb
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (hsupply hcs hT₀ hKq hKs R M hsel.hM hfl hblk hcof hcap)


end BandRider


/-! ## §6.6 — ⟦REPAIRS-LANE⟧ THE THREE FREE RE-CUTS (C3, council v3, 2026-08-01)

⟦WHAT THIS SECTION IS⟧ COUNCIL v3's C3 authorised three MECHANICAL repairs to the terminal's
rider list, each of them already certified by an earlier lane and none of them touching a
landed declaration:

* ⟦ITEM 1 — THE `Kc`/`Ct` WIDE RE-CUTS⟧ (`RIDER-LANE`, §6.3's audit page)  the two
  constant-pool riders `Kc ≤ 2^20` and `Ct ≤ 2^20` are FALSE at the chain's own witnesses
  (`≈ 2^538` and `6·e^{14} = 2^{22.78}`).  §6.3 already proved the arithmetic of the honest
  ceilings; this section SPENDS it: `s15_sel''_witness_wide` re-closes the whole `M = 2^355`
  register at `Kc ≤ 2^539`, `Ct ≤ 2^23` and the `ρ`-charge `43 → 403`, consuming
  `s16_audit_neglog_rho_le_wide`, `s16_audit_half_wide`, `s16_audit_anchor_wide` and
  `s16_audit_lvl_num_wide`.  The binding line stays `lvl`, with `3.13·10^{10}` of slack.

* ⟦ITEM 2 — THE `cs` RE-CARRY⟧ (`RIDER-LANE`'s fifth verdict)  `1 ≤ cs` is FALSE: `cs ≤ 1/10`
  is a LANDED LINE of `PortAssembly.halaszPrimesChiGated_of_price` and the witness is
  `≈ 1.86·10^{-10}`.  The demand side is `S13CapGrid`'s `gate` field, whose exponent margin
  `3/40 − 2θ₂₉₃ ≥ 0.068` (`capgrid_gate_margin`) is enormous at the socket base
  `Λ ≥ 10^{21}`.  So the repair is to SPEND the margin rather than to floor `cs`:
  `s16_capgrid_gate_numeric_cs` carries a whole factor `e^{100}` through the same numeric
  and `s16_capGrid_gate_cs` re-proves the field at `e^{-100} ≤ cs` — the `Ks`-genre form the
  constant pool can actually deliver.

* ⟦ITEM 3 — THE `/24 → /9.6` RELAXATION⟧ (`W-CENSUS` Q3)  the carried base-scale cap
  `S16BaseScaleCap_gk` asks `loglog X_d ≤ log 𝒫₂/24`, but `s16_budget_num`'s own proof
  spends only `9.6`: the leg `2·(lS/Lp)·llS` alone is `(2/9.6)·μ = (5/24)·μ`, so `9.6` is the
  SHARP divisor and everything else in the budget is paid by an `ε` of it.
  `s16_budget_num_96` re-proves the numeric at `9.60000096 = 9.6·(1 + 10^{-8})` and
  `S16BaseScaleCap96_gk` is the cap at that divisor — `2.5×` more room for every downstream
  consumer of the cap.

⟦THE DELIVERABLE⟧ `logChowla2_witnessed_scale_final'_v3`: §6.5's `v2` with `Kc`, `Ct` and
`cs` at their honest values and the cap relaxed.  After it, exactly ONE numeral rider of the
terminal is still false at the proof's own witness — `Hcap ≤ s15WitFloor2`, the wall's third
face — beside the two Siegel items (`x₀`, `Ks`) and the two carried predicates.

**PURELY ADDITIVE.**  No landed declaration is touched. -/

theorem s16_budget_num_96 {μ Λ Lp Lq lS llS lq : ℝ}
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Λ) (hμΛ : Real.log μ = Λ) (hμ : 0 < μ)
    (hLp0 : 0 < Lp) (hLpq : 4 * Lp ≤ Lq) (hLq : Lq ≤ Real.sqrt μ)
    (hcap : Λ ≤ Lp / 9.60000096)
    (hlq : lq ≤ 12 * Λ)
    (hlS0 : 0 < lS) (hlS : lS ≤ μ + 12 * Λ) (hllS : llS ≤ Λ + 1) :
    16 + Lp / 73728 + Λ / 2 + (7 / 24) * Lq + 2 * (lS / Lp) * llS + (7 / 24) * lq + μ / Λ
      ≤ (5 / 24) * μ := by
  have hΛ0 : (0 : ℝ) < Λ := by nlinarith
  have hexp : Real.exp Λ = μ := by rw [← hμΛ]; exact Real.exp_log hμ
  have hμbig : (10 : ℝ) ^ (21 : ℕ) ≤ μ := by
    have := Real.add_one_le_exp Λ
    rw [hexp] at this
    linarith
  have hsq : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ.le
  have hsq0 : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hsq10 : (10 : ℝ) ^ (10 : ℕ) ≤ Real.sqrt μ := by nlinarith [hsq, hμbig, hsq0]
  have hsqle : Real.sqrt μ ≤ μ / 10 ^ (10 : ℕ) := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hsq, hsq10, hsq0]
  have hLple : Lp ≤ μ / (4 * 10 ^ (10 : ℕ)) := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hLpq, hLq, hsqle]
  -- ⟦THE TIGHTER CAP⟧ `9.60000096·Λ ≤ Lp`
  have hc : 9.60000096 * Λ ≤ Lp := by
    rw [le_div_iff₀ (by norm_num)] at hcap; linarith
  have hΛle : Λ ≤ μ / (38 * 10 ^ (10 : ℕ)) := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hc, hLple]
  have hΛ38 : 38 * 10 ^ (10 : ℕ) * Λ ≤ μ := by
    rw [le_div_iff₀ (by norm_num)] at hΛle; linarith
  have hmain : 2 * (lS / Lp) * llS ≤ (5 / 24) * μ - 7 * (μ / 10 ^ (10 : ℕ)) := by
    have hcoef0 : (0 : ℝ) ≤ (5 / 24) * μ - 7 * (μ / 10 ^ (10 : ℕ)) := by
      have : (10 : ℝ) ^ (10 : ℕ) = 10000000000 := by norm_num
      rw [this]; linarith [hμ.le]
    have h1 : Λ * Λ * (38 * 10 ^ (10 : ℕ)) ≤ μ * Λ := by
      have := mul_le_mul_of_nonneg_right hΛ38 hΛ0.le
      linarith [this]
    have h2 : μ * 10 ^ (21 : ℕ) ≤ μ * Λ := mul_le_mul_of_nonneg_left hΛ hμ.le
    have h3 : 10 ^ (21 : ℕ) * Λ ≤ μ * Λ := mul_le_mul_of_nonneg_right hμbig hΛ0.le
    have hstep1 : 2 * lS * llS ≤ 2 * (μ + 12 * Λ) * (Λ + 1) := by
      nlinarith [hlS0.le, hlS, hllS, hΛ0.le]
    have hstep2 : 2 * (μ + 12 * Λ) * (Λ + 1)
        ≤ ((5 / 24) * μ - 7 * (μ / 10 ^ (10 : ℕ))) * (9.60000096 * Λ) := by
      have hp1 : (10 : ℝ) ^ (10 : ℕ) = 10000000000 := by norm_num
      have hp2 : (10 : ℝ) ^ (21 : ℕ) = 1000000000000000000000 := by norm_num
      rw [hp1] at h1 ⊢
      rw [hp2] at h2 h3
      linarith [h1, h2, h3]
    have hstep3 : ((5 / 24) * μ - 7 * (μ / 10 ^ (10 : ℕ))) * (9.60000096 * Λ)
        ≤ ((5 / 24) * μ - 7 * (μ / 10 ^ (10 : ℕ))) * Lp :=
      mul_le_mul_of_nonneg_left hc hcoef0
    have hkey : 2 * lS * llS ≤ ((5 / 24) * μ - 7 * (μ / 10 ^ (10 : ℕ))) * Lp := by
      linarith [hstep1, hstep2, hstep3]
    have hrw : 2 * (lS / Lp) * llS = (2 * lS * llS) / Lp := by field_simp
    rw [hrw, div_le_iff₀ hLp0]
    linarith
  have hLqle : (7 / 24) * Lq ≤ μ / 10 ^ (10 : ℕ) := by
    nlinarith [hLq, hsqle, hsq0]
  have hlqle : (7 / 24) * lq ≤ μ / 10 ^ (10 : ℕ) := by
    nlinarith [hlq, hΛle]
  have hdivle : μ / Λ ≤ μ / 10 ^ (21 : ℕ) :=
    div_le_div_of_nonneg_left hμ.le (by norm_num) hΛ
  have h9 : (16 : ℝ) ≤ μ / 10 ^ (10 : ℕ) := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith [hμbig]
  have hLp2 : Lp / 73728 ≤ μ / 10 ^ (10 : ℕ) := by
    have h : (10 : ℝ) ^ (10 : ℕ) = 10000000000 := by norm_num
    rw [h] at hLple ⊢
    norm_num at hLple ⊢
    linarith
  have hΛ2 : Λ / 2 ≤ μ / 10 ^ (10 : ℕ) := by
    have h : (10 : ℝ) ^ (10 : ℕ) = 10000000000 := by norm_num
    rw [h] at hΛle ⊢
    norm_num at hΛle ⊢
    linarith
  have hbig : (5 : ℝ) * (μ / 10 ^ (10 : ℕ)) + μ / 10 ^ (21 : ℕ)
      + ((5 / 24) * μ - 7 * (μ / 10 ^ (10 : ℕ))) ≤ (5 / 24) * μ := by
    have h1 : (10 : ℝ) ^ (10 : ℕ) = 10000000000 := by norm_num
    have h2 : (10 : ℝ) ^ (21 : ℕ) = 1000000000000000000000 := by norm_num
    rw [h1, h2]
    linarith [hμ.le]
  linarith


/-- ⟦REPAIRS-LANE ITEM 3⟧ the socket's base-scale cap at the RELAXED divisor `9.60000096`. -/
def S16BaseScaleCap96_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
    Real.log (Real.log (((A + s : ℕ)) : ℝ))
      ≤ Real.log ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) / 9.60000096

/-- ⟦ITEM 3, THE DIRECTION, KERNEL-VISIBLE⟧ the LANDED cap implies the relaxed one — `/24` is
`2.5×` the demand of `/9.60000096`.  So the relaxation is free AT THE INTERFACE: anything that
can supply `S16BaseScaleCap_gk` supplies the `v3` terminal's `S16BaseScaleCap96_gk`, and the
`2.5×` is room a future supplier may spend. -/
theorem s16_baseScaleCap96_of_baseScaleCap (K : ℕ) {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    (hcap : S16BaseScaleCap_gk K R M) : S16BaseScaleCap96_gk K R M := by
  intro H L q j A s hb
  have hLp0 : (0 : ℝ) < Real.log ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) := by
    rw [s16_logP2]
    have hA : (1 : ℕ) ≤ Adoor M := le_trans (by norm_num) (Adoor_ge M)
    have hG : (1 : ℕ) ≤ s13GK K M := one_le_s13GK K hM
    have h4 : (1 : ℝ) ≤ ((4 * (Adoor M * s13GK K M) : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 4 * (Adoor M * s13GK K M) := by
        have := Nat.mul_le_mul hA hG; omega
      exact_mod_cast this
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith
  have hdiv : Real.log ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) / 24
      ≤ Real.log ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) / 9.60000096 :=
    div_le_div_of_nonneg_left hLp0.le (by norm_num) (by norm_num)
  linarith [hcap H L q j A s hb, hdiv]

set_option maxHeartbeats 1000000 in
-- same cause as the landed `s16_budget_field_gk`: the whole `exp`/`rpow` reduction elaborates
-- in one term against the levered `𝒫₂`/`𝒬K₂` literals
theorem s16_budget_field_gk_96 (K : ℕ) {M Nd q P Q i : ℕ} {Tann : ℝ}
    (hM : 1 ≤ M) (hq : 1 ≤ q) (hQpos : 0 < Q)
    (hmu8 : 8 ≤ Real.log (Nd : ℝ))
    (hLam : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (Nd : ℝ)))
    (hqlog : (q : ℝ) ≤ (Real.log (Nd : ℝ)) ^ 12)
    (hTann1 : 1 < Tann) (hTannhi : Tann ≤ (Nd : ℝ))
    (hQhigh : (Q : ℝ) ≤ Q83 (Nd : ℝ))
    (hQ2reg : Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (Nd : ℝ)))
    (hcap : Real.log (Real.log (Nd : ℝ))
      ≤ Real.log ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) / 9.60000096)
    (hi : i ∈ ramI (H83 (Nd : ℝ) theta293) P Q) :
    thinBundleGChi ((q : ℝ) * Tann) (s13VJ_gk K M) (calH (H1door M) 2)
        (calP (Adoor M) (s13GK K M) 2) (calQK (Adoor M) (s13GK K M) M 2)
      * (Nd : ℝ) ^ (1 - 2 * s13Eta + s13EpsD q Nd) ≤ ((s13Mr Nd i : ℕ) : ℝ) := by
  set X : ℝ := (Nd : ℝ) with hXdef
  set μ : ℝ := Real.log X with hmudef
  set Λ : ℝ := Real.log μ with hLamdef
  set Lp : ℝ := Real.log ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) with hLpdef
  set Lq : ℝ := Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ) with hLqdef
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hX0 : (0 : ℝ) < X := by
    rcases Nat.eq_zero_or_pos Nd with h0 | hpos
    · exfalso
      rw [hmudef, hXdef, h0] at hμ0
      simp only [Nat.cast_zero, Real.log_zero] at hμ0
      exact lt_irrefl 0 hμ0
    · rw [hXdef]; exact_mod_cast hpos
  have hXexp : Real.exp μ = X := Real.exp_log hX0
  -- the base logs
  have hLp0 : (0 : ℝ) < Lp := by
    rw [hLpdef, s16_logP2]
    have hA : (1 : ℕ) ≤ Adoor M := le_trans (by norm_num) (Adoor_ge M)
    have hG : (1 : ℕ) ≤ s13GK K M := one_le_s13GK K hM
    have h4 : (1 : ℝ) ≤ ((4 * (Adoor M * s13GK K M) : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 4 * (Adoor M * s13GK K M) := by
        have := Nat.mul_le_mul hA hG; omega
      exact_mod_cast this
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith
  have hLqval : Lq = ((4 * M : ℕ) : ℝ) * Lp := by rw [hLqdef, hLpdef, s16_logQK2]
  have hLpq : 4 * Lp ≤ Lq := by
    rw [hLqval]
    have : (4 : ℝ) ≤ ((4 * M : ℕ) : ℝ) := by
      have : (4 : ℕ) ≤ 4 * M := by omega
      exact_mod_cast this
    nlinarith [hLp0]
  have hΛ0 : (0 : ℝ) < Λ := by linarith [hLam]
  -- `12Λ ≤ μ`
  have h12 : 12 * Λ ≤ μ := by
    have hh : Real.exp Λ = μ := by rw [hLamdef]; exact Real.exp_log hμ0
    have h1 : Λ / 2 + 1 ≤ Real.exp (Λ / 2) := Real.add_one_le_exp _
    have h2 : Real.exp (Λ / 2) * Real.exp (Λ / 2) = μ := by
      rw [← Real.exp_add, show Λ / 2 + Λ / 2 = Λ by ring, hh]
    nlinarith [hLam, h1, h2, Real.exp_pos (Λ / 2)]
  -- `S = q·Tann`
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hS0 : (0 : ℝ) < (q : ℝ) * Tann := by nlinarith
  have hlogTann0 : (0 : ℝ) < Real.log Tann := Real.log_pos hTann1
  have hlogq0 : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
  have hlogq12 : Real.log (q : ℝ) ≤ 12 * Λ := by
    have hpow : Real.log ((Real.log X) ^ 12) = 12 * Λ := by
      rw [Real.log_pow]; push_cast; rw [← hmudef, ← hLamdef]
    calc Real.log (q : ℝ) ≤ Real.log ((Real.log X) ^ 12) :=
          Real.log_le_log (by linarith) hqlog
      _ = 12 * Λ := hpow
  have hlogTann : Real.log Tann ≤ μ := by
    rw [hmudef]; exact Real.log_le_log (by linarith) hTannhi
  have hlS : Real.log ((q : ℝ) * Tann) ≤ μ + 12 * Λ := by
    rw [Real.log_mul (by linarith) (by linarith)]
    linarith
  have hlS0 : (0 : ℝ) < Real.log ((q : ℝ) * Tann) := by
    rw [Real.log_mul (by linarith) (by linarith)]
    linarith
  have hllS : Real.log (Real.log ((q : ℝ) * Tann)) ≤ Λ + 1 := by
    have h2μ : Real.log ((q : ℝ) * Tann) ≤ Real.exp 1 * μ := by
      nlinarith [Real.add_one_le_exp (1 : ℝ), h12, hlS, hμ0]
    have hstep : Real.log (Real.log ((q : ℝ) * Tann)) ≤ Real.log (Real.exp 1 * μ) :=
      Real.log_le_log hlS0 h2μ
    have heq : Real.log (Real.exp 1 * μ) = 1 + Λ := by
      rw [Real.log_mul (Real.exp_pos 1).ne' hμ0.ne', Real.log_exp]
    linarith
  -- the numeric core
  have hnum := s16_budget_num_96 (μ := μ) (Λ := Λ) (Lp := Lp) (Lq := Lq)
    (lS := Real.log ((q : ℝ) * Tann)) (llS := Real.log (Real.log ((q : ℝ) * Tann)))
    (lq := Real.log (q : ℝ)) hLam rfl hμ0 hLp0 hLpq (by rw [hLqdef]; exact hQ2reg)
    (by rw [hLpdef] at hcap ⊢; exact hcap) hlogq12 hlS0 hlS hllS
  -- ⟦THE CARD FACTOR⟧
  have hmr : mrAlpha (1 / 12) 2 = 7 / 48 := by rw [mrAlpha]; norm_num
  have hH2pos : (0 : ℝ) < calH (H1door M) 2 := by
    rw [s16_calH_two]; linarith [H1door_two hM]
  have hLq0 : (0 : ℝ) ≤ Lq := by rw [hLqval]; positivity
  have hcard := ramI_card_le (calH (H1door M) 2) (calP (Adoor M) (s13GK K M) 2)
    (calQK (Adoor M) (s13GK K M) M 2) (mul_nonneg hH2pos.le hLq0)
  have hH2le : calH (H1door M) 2 ≤ Real.exp (2 + Lp / 73728) := by
    have hlog := s16_logH2_le K hM
    rw [← hLpdef] at hlog
    calc calH (H1door M) 2 = Real.exp (Real.log (calH (H1door M) 2)) :=
          (Real.exp_log hH2pos).symm
      _ ≤ Real.exp (2 + Lp / 73728) := Real.exp_le_exp.mpr hlog
  have hexphalf : Real.exp (Λ / 2) * Real.exp (Λ / 2) = μ := by
    rw [← Real.exp_add, show Λ / 2 + Λ / 2 = Λ by ring, hLamdef]
    exact Real.exp_log hμ0
  have hLqexp : Lq ≤ Real.exp (Λ / 2) := by
    have hsqe : Real.sqrt μ = Real.exp (Λ / 2) := by
      rw [show μ = Real.exp (Λ / 2) ^ 2 by rw [sq]; exact hexphalf.symm]
      exact Real.sqrt_sq (Real.exp_pos _).le
    rw [← hsqe]; exact hQ2reg
  have hcardexp :
      ((ramI (calH (H1door M) 2) (calP (Adoor M) (s13GK K M) 2)
        (calQK (Adoor M) (s13GK K M) M 2)).card : ℝ)
        ≤ Real.exp (3 + Lp / 73728 + Λ / 2) := by
    have hstep : calH (H1door M) 2 * Lq + 1
        ≤ Real.exp (2 + Lp / 73728) * Real.exp (Λ / 2) + 1 := by
      have := mul_le_mul hH2le hLqexp hLq0 (Real.exp_pos _).le
      linarith
    have hcomb : Real.exp (2 + Lp / 73728) * Real.exp (Λ / 2)
        = Real.exp (2 + Lp / 73728 + Λ / 2) := by rw [← Real.exp_add]
    have hone : (1 : ℝ) ≤ Real.exp (2 + Lp / 73728 + Λ / 2) := by
      rw [Real.one_le_exp_iff]; positivity
    have hplus : Real.exp (2 + Lp / 73728 + Λ / 2) + 1
        ≤ Real.exp (3 + Lp / 73728 + Λ / 2) := by
      have : Real.exp (3 + Lp / 73728 + Λ / 2)
          = Real.exp 1 * Real.exp (2 + Lp / 73728 + Λ / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      nlinarith [Real.exp_one_gt_d9, hone]
    linarith [hcard, hstep, hcomb ▸ hstep]
  -- ⟦THE `VJ` FACTOR⟧
  have hVJ : (s13VJ_gk K M) ^ 2 = Real.exp ((7 / 24) * Lq) := by
    rw [s13VJ_gk, hmr, ← hLqdef, sq, ← Real.exp_add]
    congr 1; ring
  -- ⟦THE `X`-POWER⟧
  have hXr : X ^ (1 - 2 * s13Eta + s13EpsD q Nd)
      = Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ)) := by
    rw [Real.rpow_def_of_pos hX0, s13Eta, s13EpsD, hmr]
    congr 1
    rw [← hXdef, ← hmudef]
    field_simp
    ring
  -- ⟦THE ASSEMBLY⟧
  have h1680 : (1680 : ℝ) ≤ Real.exp 8 := by
    have h2 : Real.exp 8 = (Real.exp 1) ^ (8 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : (2.7182818283 : ℝ) ^ (8 : ℕ) ≤ (Real.exp 1) ^ (8 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 8
    have h5 : (1680 : ℝ) ≤ (2.7182818283 : ℝ) ^ (8 : ℕ) := by norm_num
    linarith
  rw [thinBundleGChi, hVJ, hXr]
  set E : ℝ := 2 * (Real.log ((q : ℝ) * Tann) / Lp)
    * Real.log (Real.log ((q : ℝ) * Tann)) with hEdef
  have hprod :
      ((ramI (calH (H1door M) 2) (calP (Adoor M) (s13GK K M) 2)
        (calQK (Adoor M) (s13GK K M) M 2)).card : ℝ)
          * (1680 * Real.exp ((7 / 24) * Lq) * Real.exp E)
          * Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ))
        ≤ Real.exp (3 + Lp / 73728 + Λ / 2)
          * (Real.exp 8 * Real.exp ((7 / 24) * Lq) * Real.exp E)
          * Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ)) := by
    have hA : (0 : ℝ) ≤ Real.exp ((7 / 24) * Lq) * Real.exp E := by positivity
    have hB : (0 : ℝ) ≤ Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ)) := by positivity
    have hC : (1680 : ℝ) * Real.exp ((7 / 24) * Lq) * Real.exp E
        ≤ Real.exp 8 * Real.exp ((7 / 24) * Lq) * Real.exp E := by
      have := mul_le_mul_of_nonneg_right h1680 hA
      calc (1680 : ℝ) * Real.exp ((7 / 24) * Lq) * Real.exp E
          = 1680 * (Real.exp ((7 / 24) * Lq) * Real.exp E) := by ring
        _ ≤ Real.exp 8 * (Real.exp ((7 / 24) * Lq) * Real.exp E) := this
        _ = Real.exp 8 * Real.exp ((7 / 24) * Lq) * Real.exp E := by ring
    have hcard0 : (0 : ℝ) ≤ ((ramI (calH (H1door M) 2) (calP (Adoor M) (s13GK K M) 2)
        (calQK (Adoor M) (s13GK K M) M 2)).card : ℝ) := Nat.cast_nonneg _
    have hmid := mul_le_mul hcardexp hC (by positivity) (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hmid hB
  have hsum : Real.exp (3 + Lp / 73728 + Λ / 2)
      * (Real.exp 8 * Real.exp ((7 / 24) * Lq) * Real.exp E)
      * Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ))
      = Real.exp (11 + Lp / 73728 + Λ / 2 + (7 / 24) * Lq + E
          + (7 / 24) * Real.log (q : ℝ) + (19 / 24) * μ) := by
    simp only [← Real.exp_add]
    congr 1
    ring
  -- ⟦THE RIGHT-HAND SIDE⟧
  have hH830 : (0 : ℝ) < H83 X theta293 := by
    rw [H83, ← hmudef]; exact Real.rpow_pos_of_pos hμ0 _
  have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQpos
  have hlogQ0 : (0 : ℝ) ≤ Real.log (Q : ℝ) := Real.log_nonneg hQR
  have hiQ : (i : ℝ) / H83 X theta293 ≤ μ / Λ := by
    rw [ramI, Finset.mem_Icc] at hi
    have h1 : (i : ℝ) ≤ H83 X theta293 * Real.log (Q : ℝ) := by
      have h2 : ((⌊H83 X theta293 * Real.log (Q : ℝ)⌋₊ : ℕ) : ℝ)
          ≤ H83 X theta293 * Real.log (Q : ℝ) :=
        Nat.floor_le (mul_nonneg hH830.le hlogQ0)
      have h3 : (i : ℝ) ≤ ((⌊H83 X theta293 * Real.log (Q : ℝ)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hi.2
      linarith
    have h4 : Real.log (Q : ℝ) ≤ μ / Λ := by
      have h5 : Real.log (Q83 X) = μ / Λ := by
        rw [Q83, Real.log_exp, ← hmudef, ← hLamdef]
      calc Real.log (Q : ℝ) ≤ Real.log (Q83 X) := Real.log_le_log (by linarith) hQhigh
        _ = μ / Λ := h5
    rw [div_le_iff₀ hH830]
    nlinarith [hH830, h1, h4]
  have hMr : 2 * X * Real.exp (-(i : ℝ) / H83 X theta293) ≤ ((s13Mr Nd i : ℕ) : ℝ) := by
    rw [hXdef, s13Mr]
    exact Nat.le_ceil _
  have hexpstep : Real.exp (μ - μ / Λ) ≤ 2 * X * Real.exp (-(i : ℝ) / H83 X theta293) := by
    have h1 : Real.exp (μ - μ / Λ) = X * Real.exp (-(μ / Λ)) := by
      rw [← hXexp, ← Real.exp_add]; congr 1
    have h2 : Real.exp (-(μ / Λ)) ≤ Real.exp (-(i : ℝ) / H83 X theta293) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      linarith [hiQ]
    have h3 : X * Real.exp (-(μ / Λ)) ≤ X * Real.exp (-(i : ℝ) / H83 X theta293) :=
      mul_le_mul_of_nonneg_left h2 hX0.le
    nlinarith [Real.exp_pos (-(i : ℝ) / H83 X theta293), hX0, h1, h3]
  have hfin : Real.exp (11 + Lp / 73728 + Λ / 2 + (7 / 24) * Lq + E
      + (7 / 24) * Real.log (q : ℝ) + (19 / 24) * μ) ≤ Real.exp (μ - μ / Λ) := by
    apply Real.exp_le_exp.mpr
    rw [hEdef] at *
    linarith [hnum]
  linarith [hprod, hsum ▸ hprod, hfin, hexpstep, hMr]


/-! ## ITEM 2 — THE `cs` RE-CARRY -/

/-- ⟦ITEM 2⟧ `capgrid_gate_numeric` with the margin exponent HALVED — the half that is not
spent on the `Λ`-polynomial is what pays the `e^{100}` of the honest `cs` floor. -/
theorem s16_capgrid_gate_numeric_half {Λ : ℝ} (hΛ : 7800 ≤ Λ) :
    420 * (11 / 10 * Λ) ^ 5 ≤ Real.exp (34 / 1000 * Λ) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  set y : ℝ := 34 / 1000 * Λ / 32 with hy
  have hy0 : (0 : ℝ) ≤ y := by rw [hy]; positivity
  have hye : y ≤ Real.exp y := by have := Real.add_one_le_exp y; linarith
  have hsplit : Real.exp (34 / 1000 * Λ) = (Real.exp y) ^ (32 : ℕ) := by
    rw [← Real.exp_nat_mul, hy]; ring_nf
  have hpow : y ^ (32 : ℕ) ≤ (Real.exp y) ^ (32 : ℕ) := pow_le_pow_left₀ hy0 hye 32
  rw [hsplit]
  refine le_trans ?_ hpow
  have hyv : y ^ (32 : ℕ) = ((17 : ℝ) / 16000) ^ (32 : ℕ) * (Λ ^ (27 : ℕ) * Λ ^ (5 : ℕ)) := by
    rw [hy]; ring
  have h27 : (7800 : ℝ) ^ (27 : ℕ) ≤ Λ ^ (27 : ℕ) := pow_le_pow_left₀ (by norm_num) hΛ 27
  have hc : 420 * ((11 : ℝ) / 10) ^ (5 : ℕ)
      ≤ ((17 : ℝ) / 16000) ^ (32 : ℕ) * (7800 : ℝ) ^ (27 : ℕ) := by norm_num
  have h5 : (0 : ℝ) < Λ ^ (5 : ℕ) := by positivity
  have hcpos : (0 : ℝ) < ((17 : ℝ) / 16000) ^ (32 : ℕ) := by positivity
  rw [hyv]
  have hstep : 420 * ((11 : ℝ) / 10) ^ (5 : ℕ)
      ≤ ((17 : ℝ) / 16000) ^ (32 : ℕ) * Λ ^ (27 : ℕ) :=
    le_trans hc (by nlinarith [h27, hcpos])
  calc 420 * (11 / 10 * Λ) ^ (5 : ℕ) = (420 * ((11 : ℝ) / 10) ^ (5 : ℕ)) * Λ ^ (5 : ℕ) := by
        ring
    _ ≤ (((17 : ℝ) / 16000) ^ (32 : ℕ) * Λ ^ (27 : ℕ)) * Λ ^ (5 : ℕ) :=
        mul_le_mul_of_nonneg_right hstep h5.le
    _ = ((17 : ℝ) / 16000) ^ (32 : ℕ) * (Λ ^ (27 : ℕ) * Λ ^ (5 : ℕ)) := by ring

/-- ⟦ITEM 2⟧ THE `cs`-GATE NUMERIC AT THE HONEST FLOOR — the `Λ`-polynomial with a whole
factor `e^{100}` in front is still swallowed by the margin exponent at `Λ ≥ 7800`. -/
theorem s16_capgrid_gate_numeric_cs {Λ : ℝ} (hΛ : 7800 ≤ Λ) :
    Real.exp 100 * (420 * (11 / 10 * Λ) ^ 5) ≤ Real.exp (68 / 1000 * Λ) := by
  have hstep : Real.exp (34 / 1000 * Λ) ≤ Real.exp (68 / 1000 * Λ - 100) :=
    Real.exp_le_exp.mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_left
    (le_trans (s16_capgrid_gate_numeric_half hΛ) hstep) (Real.exp_pos (100 : ℝ)).le
  calc Real.exp 100 * (420 * (11 / 10 * Λ) ^ 5)
      ≤ Real.exp 100 * Real.exp (68 / 1000 * Λ - 100) := hmul
    _ = Real.exp (68 / 1000 * Λ) := by rw [← Real.exp_add]; ring_nf

/-- ⟦ITEM 2 — THE `cs`-GATE AT THE HONEST FLOOR⟧ `S13CapGrid.s13CapGrid_gate` with the binder
`1 ≤ cs` replaced by `e^{-100} ≤ cs`, the value the constant pool can actually deliver.  The
whole difference is paid inside the `gate` exponent margin `3/40 − 2θ₂₉₃ ≥ 0.068`
(`capgrid_gate_margin`), which at the socket base `Λ ≥ 10^{21}` has room to spare. -/
theorem s16_capGrid_gate_cs {Nd : ℕ} {cs : ℝ} (hcs : Real.exp (-100) ≤ cs)
    (hμ : (2000 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ))
    (hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ))) :
    ∀ i ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) (s13BandQ Nd),
      420 * s13Lr Nd * (s13Lr Nd) ^ ((3 : ℝ) / 4) * (Real.log (s13Lr Nd)) ^ 5
        ≤ cs * (Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i)) ^ 2 := by
  intro i hi
  set μ : ℝ := Real.log ((Nd : ℕ) : ℝ) with hμdef
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hΛ0 : (0 : ℝ) < Real.log μ := by
    have : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    linarith
  have hΛ7800 : (7800 : ℝ) ≤ Real.log μ := by
    have : (7800 : ℝ) ≤ (10 : ℝ) ^ (21 : ℕ) := by norm_num
    linarith
  have hL1 : s13Lr Nd * (s13Lr Nd) ^ ((3 : ℝ) / 4) = μ ^ ((77 : ℝ) / 40) := by
    rw [s13Lr, ← hμdef, ← Real.rpow_mul hμ0.le, ← Real.rpow_add hμ0]
    norm_num
  have hlogLr : Real.log (s13Lr Nd) = 11 / 10 * Real.log μ := by
    rw [s13Lr, ← hμdef, Real.log_rpow hμ0]
  have hbase : μ ^ (1 - theta293)
      ≤ Real.log ((ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i : ℕ) : ℝ) := by
    refine le_trans (s13CapGrid_logP_ge Nd) (Real.log_le_log ?_ ?_)
    · have h3 := s13CapGrid_P_three hμ hΛ
      have : (3 : ℝ) ≤ ((s13BandP Nd : ℕ) : ℝ) := by exact_mod_cast h3
      linarith
    · exact_mod_cast ramQbase_ge_bot (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i
  have hpow2 : (μ ^ (1 - theta293)) ^ (2 : ℕ) = μ ^ ((2 : ℝ) - 2 * theta293) := by
    rw [← Real.rpow_natCast (μ ^ (1 - theta293)) 2, ← Real.rpow_mul hμ0.le]
    congr 1
    push_cast
    ring
  have hsplit : μ ^ ((2 : ℝ) - 2 * theta293)
      = μ ^ ((77 : ℝ) / 40) * μ ^ ((3 : ℝ) / 40 - 2 * theta293) := by
    rw [← Real.rpow_add hμ0]; congr 1; ring
  -- ⟦THE ONE CHANGED LINE⟧ the numeric carries the `e^{100}` of the honest floor
  have hgate : Real.exp 100 * (420 * (11 / 10 * Real.log μ) ^ 5)
      ≤ μ ^ ((3 : ℝ) / 40 - 2 * theta293) := by
    rw [Real.rpow_def_of_pos hμ0]
    refine le_trans (s16_capgrid_gate_numeric_cs hΛ7800) (Real.exp_le_exp.mpr ?_)
    nlinarith [capgrid_gate_margin, hΛ0]
  have he : Real.exp (-100) * Real.exp 100 = 1 := by rw [← Real.exp_add]; norm_num
  have hgate' : 420 * (11 / 10 * Real.log μ) ^ 5
      ≤ Real.exp (-100) * μ ^ ((3 : ℝ) / 40 - 2 * theta293) := by
    calc 420 * (11 / 10 * Real.log μ) ^ 5
        = Real.exp (-100) * (Real.exp 100 * (420 * (11 / 10 * Real.log μ) ^ 5)) := by
          rw [← mul_assoc, he, one_mul]
      _ ≤ Real.exp (-100) * μ ^ ((3 : ℝ) / 40 - 2 * theta293) :=
          mul_le_mul_of_nonneg_left hgate (Real.exp_pos _).le
  have hcs0 : (0 : ℝ) < cs := lt_of_lt_of_le (Real.exp_pos _) hcs
  calc 420 * s13Lr Nd * (s13Lr Nd) ^ ((3 : ℝ) / 4) * (Real.log (s13Lr Nd)) ^ 5
      = μ ^ ((77 : ℝ) / 40) * (420 * (11 / 10 * Real.log μ) ^ 5) := by
        rw [hlogLr, ← hL1]; ring
    _ ≤ μ ^ ((77 : ℝ) / 40) * (Real.exp (-100) * μ ^ ((3 : ℝ) / 40 - 2 * theta293)) :=
        mul_le_mul_of_nonneg_left hgate' (Real.rpow_nonneg hμ0.le _)
    _ = Real.exp (-100) * (μ ^ (1 - theta293)) ^ (2 : ℕ) := by
        rw [hpow2, hsplit]; ring
    _ ≤ cs * (μ ^ (1 - theta293)) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hcs (by positivity)
    _ ≤ cs * (Real.log ((ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) (s13BandP Nd) i : ℕ) : ℝ))
          ^ 2 := by
        have hmono := pow_le_pow_left₀ (Real.rpow_nonneg hμ0.le _) hbase 2
        exact mul_le_mul_of_nonneg_left hmono hcs0.le

/-! ## ITEM 2 + ITEM 3 — THE CAP-GATE SUPPLY, RE-CUT -/

set_option maxHeartbeats 1000000 in
-- 37 structure fields are checked against the levered per-block gate in one `exact`
/-- ⟦REPAIRS-LANE⟧ `s16_capGate_supply_gk` with TWO riders re-cut: the `cs` floor is the
honest `e^{-100}` (item 2, through `s16_capGrid_gate_cs`) and the base-scale cap is the
relaxed `S16BaseScaleCap96_gk` (item 3, through `s16_budget_field_gk_96`).  Every other field
is the landed one, at `cs := 1` where the grid wave does not read `cs`. -/
theorem s16_capGate_supply_wide_gk (K : ℕ) {Cq cs T₀ Kq Ks C : ℝ} {R : ChowlaRegime} {M : ℕ}
    {epsf : ℕ → ℝ}
    (hM : 1 ≤ M) (hfl : loglogFloor50 ≤ R.Hlo) (hcs : Real.exp (-100) ≤ cs)
    (hblk : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor_gk K M ≤ A + s)
    (hT₀ : T₀ ≤ Real.exp (Real.exp 100)) (hKq : Kq ≤ Real.exp 100)
    (hKs : Real.exp (-100) ≤ Ks) (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hεr : ∀ A : ℕ, theta293 - 1 / 500 ≤ epsf A)
    (hcap : S16BaseScaleCap96_gk K R M) (hcof : S16CofactorSupply_gk K Cq R M) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
        2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
        5 ≤ Real.log (Real.log (2 * T)) →
        ∃ (P Q : ℕ) (Rrad Rbd CR EP2 : ℝ),
          S13CapGatePerBlock_gk K Cq cs T₀ Kq Ks C M (A + s) q P Q H (2 * T)
            Rrad Rbd CR EP2 (epsf (A + s)) := by
  intro H L q j A s hb T hTlo hThi hTgate hTll
  obtain ⟨Rrad, Rbd, CR, hRbd0, hRbdg, hCqg, hRsock⟩ := hcof H L q j A s hb T hTlo hThi
  -- the grid wave
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, -, g17, g18⟩ :=
    s13CapGrid_all_gk K hM (le_refl (1 : ℝ)) hfl hb (hblk H L q j A s hb) hTlo hThi
  -- `1 < 2T` off the annulus gate
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hT1 : (1 : ℝ) < 2 * T := by
    have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
    linarith
  have hT0le : (0 : ℝ) ≤ 2 * T := by linarith
  have hAN : A ≤ A + s := Nat.le_add_right _ _
  have hTflo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ 2 * T := by linarith
  -- the floor wave
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, -⟩ :=
    s13CapFloor_all_gk K hfl hb hM hAN hTflo g6 hT₀ hKq hKs
  -- the eps wave
  obtain ⟨hP83pin, hgradepin⟩ := s13CapEps_pins_supply hfl hb
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ :=
    s13CapEps_all hfl hb (hεr (A + s)) hC0 hC hT0le hThi hP83pin hgradepin
  refine ⟨s13BandP (A + s), s13BandQ (A + s), Rrad, Rbd, CR,
    s13CapEP2 C q (A + s) (s13BandP (A + s)) (s13BandQ (A + s)) (2 * T), ?_⟩
  exact
    { logX_eight := g1
      H83_two := g2
      QTann := f1
      kappa30Q := f2
      q_logX := g3
      T0_Tann := f3
      floor1 := f4
      floor2 := f5
      floor3 := f6
      floor4 := f7
      logqT_L := g4
      P_low := g5
      Q2_reg := g6
      Q_pos := g7
      Q_high := g8
      P_le_Q := g9
      budget := fun i hi =>
        s16_budget_field_gk_96 K hM hb.2.2.2.1 g7 g1
          (s13CapGrid_Lambda_lo hfl hb) g3 hT1 hThi g8 g6 (hcap H L q j A s hb) hi
      Hj := g10
      B3 := g11
      BT := g12
      kappa30 := g13
      BT10 := g14
      WL := g15
      gate := s16_capGrid_gate_cs hcs (s13CapGrid_mu_2000 hfl hb)
        (s13CapGrid_Lambda_lo hfl hb)
      Rbd_nonneg := hRbd0
      Rbd_grade := hRbdg
      Cq_gate := hCqg
      Rbd_socket := hRsock
      epsr_nonneg := e1
      abs8640 := e2
      EP2_gate := e3
      q_arcDen := e4
      phi_row := e5
      p2_row := e6
      tail_row := e7
      Q_hundred := g17
      band_product := g18 }

/-! ## ITEM 1–3 — THE CROSSING BOUND AND THE TERMINAL, RE-CUT -/

set_option maxHeartbeats 1000000 in
-- the eighteen-slot `hcapWS` family re-elaborates against the wire's own shape (§4's cause)
/-- **§4 AT THE RE-CUT RIDERS** (`s15_crossing_supplied_wide_gk`) — §6.4's
`s15_crossing_supplied_bounded_gk` with the `cs` rider at its honest floor `e^{-100}` and
the base-scale cap at the relaxed `S16BaseScaleCap96_gk`.  The body is the landed one,
reading `s16_capGate_supply_wide_gk` where it read `s16_capGate_supply_gk`. -/
theorem s15_crossing_supplied_wide_gk (K : ℕ) :
    ∃ Cq cs T₀ Kq Ks C : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      (Real.exp (-100) ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ (R : ChowlaRegime) (M : ℕ), 1 ≤ M → loglogFloor50 ≤ R.Hlo →
          (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor_gk K M ≤ A + s) →
          S16CofactorSupply_gk K Cq R M → S16BaseScaleCap96_gk K R M →
          S15CrossingBound_gk K R M) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs0, hT₀3, hKq0, hKs0, hwire⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨C, hC0, hC40, hband⟩ := m4_tail_mass_at_band_bounded
  refine ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro hcs hT₀ hKq hKs R M hM hfl hblk hcof hcap
  have hgate := s16_capGate_supply_wide_gk K hM hfl hcs hblk hT₀ hKq hKs hC0 hC40
    (fun _ => le_rfl) hcap hcof
  refine hwire R M liouvilleC (fun _ => theta293 - 1 / 500) liouvilleC_norm_le_one ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨P, Q, Rrad, Rbd, CR, EP2, hg⟩ := hgate H L q j A s hsb T hTlo hThi hTgate hTll
  have hq : 1 ≤ q := hsb.2.2.2.1
  have hA : 0 < A := hsb.2.2.2.2.2.2.2.1
  have hNd : 1 ≤ A + s := by omega
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by have := hg.logX_eight; linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
  have hT1 : (1 : ℝ) < 2 * T := by linarith
  exact doorCapBundle_at_workingPoint_perBlock_gk K hband hM hNd hq hg hT1 hThi hTll

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 1600000 in
-- same cause as the landed `s15_sel''_witness_gk'`: eleven register lines at `M = 2^355`, the
-- `blk` line carrying `2^(2K+1542)`-sized casts and the `x0M` line an `exp∘exp` chain
/-- **⟦ITEM 1 — THE WIDE REGISTER⟧** (`s15_sel''_witness_wide`) — `s15_sel''_witness_gk'`
(`S15Witness` :1745) at the WIDE ceilings `Kc ≤ 2^539` and `Ct ≤ 2^23`, the honest ones
(§6.3's audit page: the witnesses are `≈ 2^538` and `6·e^{14} = 2^{22.78}`).  The `ρ`-charge
moves `43 → 403` (`s16_audit_neglog_rho_le_wide`) and the four charge-spending register lines
are re-closed by §6.3's certified stones: `half` (`s16_audit_half_wide`), `anchor`
(`s16_audit_anchor_wide`), `lvl` (`s16_audit_lvl_num_wide`, the binding one) and `gP1` at
`log Ct ≤ 23·log 2`.  Every other line is the landed one, byte-for-byte. -/
theorem s15_sel''_witness_wide (Klev : ℕ) (hKle : Klev ≤ 170000000) {Cg δ₀ Ct K : ℝ}
    {x₀ Mfl : ℕ} {R : ChowlaRegime}
    (hδ : 0 < δ₀) (hδb : 1 / 2 ^ 20 ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 539)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hbfl : 24 * Cg / δ₀ ≤ 2 ^ 355)
    (hMfl : Mfl ≤ 2 ^ 355)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp 275))
    (heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps)
    (hlo : (2 : ℝ) ^ 400 ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 987 * 10 ^ 8) :
    S15Sel''_gk Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R (2 ^ 355) := by
  have hρlog : -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 403 :=
    s16_audit_neglog_rho_le_wide hδ hK hδb hKb
  have hinv : Real.log (1 / doorRhoOfDelta (s12DeltaSock δ₀ K))
      = -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := by
    rw [one_div, Real.log_inv]
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  -- ⟦the door row, exactly⟧
  have hAdR : ((Adoor (2 ^ 355) : ℕ) : ℝ) = 24464133718016 := by
    rw [s15w2_Adoor]; norm_num
  have hdrfR : ((doorRowFloor (2 ^ 355) : ℕ) : ℝ) = 356 * 2 ^ 391 := by
    rw [s15w2_doorRowFloor]; push_cast; ring
  have hnR : ((Nat.log 2 (2 ^ 355) + 1 : ℕ) : ℝ) = 356 := by
    rw [Nat.log_pow (by norm_num)]; norm_num
  refine
    { hM := Nat.one_le_two_pow
      mfloor := hMfl
      bfloor := ?_
      gRows := ?_
      x0M := ?_
      blk := ?_
      half := ?_
      rho := ?_
      anchor := ?_
      gP1 := ?_
      lvl := ?_ }
  · -- ⟦`M`-LOWER 1⟧ the spine's `hMδ`, stated at the window
    exact_mod_cast hbfl
  · -- ⟦`M`-LOWER 2⟧ `242·λ₊ ≤ A(M)`
    rw [hAdR]; linarith [hhi]
  · -- ⟦RESTORED⟧ `x₀ ≤ 2^{doorRowFloor M}`
    have h398 : Real.exp 275 ≤ (2 : ℝ) ^ (398 : ℕ) := by
      have hl : (275 : ℝ) ≤ Real.log ((2 : ℝ) ^ (398 : ℕ)) := by
        rw [Real.log_pow]; push_cast; linarith
      calc Real.exp 275 ≤ Real.exp (Real.log ((2 : ℝ) ^ (398 : ℕ))) := Real.exp_le_exp.mpr hl
        _ = (2 : ℝ) ^ (398 : ℕ) := Real.exp_log (by positivity)
    have hrow : (2 : ℝ) ^ (398 : ℕ)
        ≤ ((doorRowFloor (2 ^ 355) : ℕ) : ℝ) * Real.log 2 := by
      rw [hdrfR]; nlinarith [hlog2lo]
    have hpowid : ((2 : ℝ) ^ (doorRowFloor (2 ^ 355) : ℕ))
        = Real.exp (((doorRowFloor (2 ^ 355) : ℕ) : ℝ) * Real.log 2) := by
      rw [← Real.log_pow]
      exact (Real.exp_log (by positivity)).symm
    have hfin : (x₀ : ℝ) ≤ (2 : ℝ) ^ (doorRowFloor (2 ^ 355) : ℕ) := by
      rw [hpowid]
      refine le_trans hx0win (Real.exp_le_exp.mpr ?_)
      linarith [h398, hrow]
    exact_mod_cast hfin
  · -- ⟦`M`-UPPER 1⟧ the block ceiling, at the LEVERED exponent `2^(2K+1542)`
    have hbe : ((s13BlockExp_gk Klev (2 ^ 355) : ℕ) : ℝ) ≤ 2 ^ (2 * Klev + 1542) := by
      have h := s15w2_blockExp_le_gk Klev
      have h' : ((s13BlockExp_gk Klev (2 ^ 355) : ℕ) : ℝ)
          ≤ ((2 ^ (2 * Klev + 1542) : ℕ) : ℝ) := by exact_mod_cast h
      calc ((s13BlockExp_gk Klev (2 ^ 355) : ℕ) : ℝ) ≤ ((2 ^ (2 * Klev + 1542) : ℕ) : ℝ) := h'
        _ = 2 ^ (2 * Klev + 1542) := by push_cast; ring
    have hfl := s15w2_blk_floor_gk Klev hKle heps hlo
    have hfl' : (2 : ℝ) ^ (2 * Klev + 1541) ≤ ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
      have h : ((2 ^ (2 * Klev + 1541) : ℕ) : ℝ) ≤ ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hfl
      calc (2 : ℝ) ^ (2 * Klev + 1541) = ((2 ^ (2 * Klev + 1541) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ _ := h
    have hdbl : (2 : ℝ) ^ (2 * Klev + 1542) = 2 * (2 : ℝ) ^ (2 * Klev + 1541) := by
      rw [show 2 * Klev + 1542 = (2 * Klev + 1541) + 1 by omega, pow_succ]; ring
    have hbig : (2 : ℝ) ^ (1541 : ℕ) ≤ (2 : ℝ) ^ (2 * Klev + 1541) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hnum : (1 : ℝ) + 18 * (987 * 10 ^ 8) ≤ (2 : ℝ) ^ (1541 : ℕ) := by norm_num
    linarith [hbe, hfl', hhi, hdbl, hbig, hnum]
  · -- ⟦`M`-UPPER 2⟧ the window gate, at the WIDE charge
    rw [hinv, hdrfR]
    linarith [s16_audit_half_wide, hρlog, hlo]
  · -- the clearing charge
    linarith [hρlog]
  · -- ⟦RESTORED⟧ the `ρ`-frame's anchor at `3.9·10^9·(log₂M + 1)`, at the WIDE charge
    rw [hinv, hnR]
    exact s16_audit_anchor_wide hhi hρlog
  · -- the `𝒯`-leg budget
    rw [hAdR]
    have hCtl : Real.log Ct ≤ 23 * Real.log 2 := by
      have h := Real.log_le_log hCt hCtb
      rwa [Real.log_pow] at h
    have hρ' : -(403 : ℝ) ≤ Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := by
      linarith [hρlog]
    nlinarith [hlog2lo, hhi, hCtl, hρ', hlog2hi]
  · -- the `level1` budget
    rw [hAdR, s15_log_calQK_one_gk Klev (2 ^ 355), hdrfR]
    have hQ : Real.log ((356 : ℝ) * 2 ^ 391 * Real.log 2) ≤ 277 := by
      have hl2 : (0 : ℝ) < Real.log 2 := by linarith only [hlog2lo]
      have hpos : (0 : ℝ) < 356 * 2 ^ 391 * Real.log 2 := by positivity
      have hle : (356 : ℝ) * 2 ^ 391 * Real.log 2 ≤ (2 : ℝ) ^ (399 : ℕ) := by
        linarith only [hlog2hi]
      have h := Real.log_le_log hpos hle
      rw [Real.log_pow] at h
      push_cast at h
      linarith only [h, hlog2hi]
    exact s16_audit_lvl_num_wide hhi hQ hρlog

set_option exponentiation.threshold 4000 in
-- the `2^355`/`2^539` register numerals: `S15Witness` sets this file-wide, `S16Budget`
-- per-theorem
/-- **⟦ITEM 1, HOP 5⟧** (`logChowla2_conditional_sharp2_nonvacuous_gk'_Mfl_wide`) —
`logChowla2_conditional_sharp2_nonvacuous_gk'_Mfl` (§6.5) reading `s15_sel''_witness_wide`,
so the two constant-pool riders arrive at their HONEST ceilings `Kc ≤ 2^539`, `Ct ≤ 2^23`.
The body is the landed one, byte-for-byte, except that one call. -/
theorem logChowla2_conditional_sharp2_nonvacuous_gk'_Mfl_wide (Klev : ℕ)
    (hKle : Klev ≤ 170000000) (hband : S16BandLaneCBounded Klev) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      (Kc ≤ 2 ^ 539 → Ct ≤ 2 ^ 23 → (x₀ : ℝ) ≤ Real.exp (Real.exp 275) →
        Hcap ≤ s15WitFloor2 →
        ∀ g : ℕ → ℕ → ℕ, ∃ (R : ChowlaRegime) (M : ℕ),
          R.eps = ε ∧ R.Hlo = s15WitFloor2 ∧ g R.Hhi R.ω ≤ R.x ∧
          S15Sel''_gk Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M ∧
          (S15CrossingBound_gk Klev R M → ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1, hCgle, hεpin,
    hδpin, hMflb, hbody⟩ :=
    logChowla2_conditional_sharp2_atK_gk_pinned_Mfl Klev hKle hband
  refine ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1, hCgle, hεpin,
    hδpin, hMflb, ?_⟩
  intro hKcb hCtb hx0b hHcap g
  -- ⟦THE THREE DISCHARGES⟧ the pinned road's own conjuncts, spent
  have hεb : (1 : ℚ) / 2 ^ 9 ≤ ε := le_trans (by norm_num) hεpin
  have hδb : (1 : ℝ) / 2 ^ 20 ≤ δ₀ := le_trans (by norm_num) hδpin
  have hbfl : 24 * Cg / δ₀ ≤ (2 : ℝ) ^ 355 := by
    rw [div_le_iff₀ hδ₀]
    have hnum : (24 : ℝ) * Cg ≤ 48 * 10 ^ 12 := by linarith
    have hkey : (48 : ℝ) * 10 ^ 12 ≤ (2 : ℝ) ^ 355 * (1 / 838400) := by norm_num
    have hmono : (2 : ℝ) ^ 355 * (1 / 838400) ≤ (2 : ℝ) ^ 355 * δ₀ :=
      mul_le_mul_of_nonneg_left hδpin (by positivity)
    linarith
  have hU : max Hcap (max arcFloor36 loglogFloor50) ≤ s15WitFloor2 := by
    have h1 := s15WitFloor2_arc
    have h2 := s15WitFloor2_ll
    omega
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hfire⟩ := hbody s15WitFloor2 g hU
  have hlo : (2 : ℝ) ^ 400 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact s15WitFloor2_log_ge
  have h50 : (50 : ℝ) ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) := by
    rw [hHlo]; exact s15WitFloor2_loglog_ge
  have hlam : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 2772589 / 10000 := by
    rw [hHlo]; exact s15WitFloor2_loglog_le
  have hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 987 * 10 ^ 8 := by
    refine le_trans (hRtow h50) ?_
    exact s15w2_tower_bound (by linarith) hlam
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by rw [hReps]; exact hεb
  have hwit := s15_sel''_witness_wide Klev hKle hδ₀ hδb hKc hKcb hCt hCtb hbfl
    hMflb hx0b heps hlo hhi
  exact ⟨R, 2 ^ 355, hReps, hHlo, hRg, hwit, hfire (2 ^ 355) hwit⟩

set_option exponentiation.threshold 4000 in
set_option maxHeartbeats 1000000 in
-- the twin's seventeen-binder prefix re-elaborates beside the crossing supply's six constants
/-- **⟦THE REPAIRS-LANE TERMINAL⟧** (`logChowla2_witnessed_scale_final'_v3`) — §6.5's
`logChowla2_witnessed_scale_final'_v2` with THREE of its four known-false riders re-cut to
their honest values and the base-scale cap widened `2.5×`.

⟦THE HYPOTHESIS LIST, EXACT AND COMPLETE⟧ the inner implication asks for, in order:

* `Kc ≤ 2^539` — ⟦ITEM 1⟧ the WIDE ceiling; it covers `ConstantsExposed.KExpr_le`'s
  `12·10^{161} = 2^{538.42}` and the full-tower read `≈ 2^{538}`.  Was `2^20` (FALSE by
  ~515 bits).  Paid by the `ρ`-charge `43 → 403`;
* `Ct ≤ 2^23` — ⟦ITEM 1⟧ the honest ceiling for `6·e^{14} = 2^{22.78}` (14% of room).
  Was `2^20` (FALSE by 6.88×);
* `(x₀ : ℝ) ≤ e^{e^{275}}` — ⟦`hx0win`⟧ **the Siegel item**, undischargeable on this road;
* `Hcap ≤ s15WitFloor2` — ⛔ **THE WALL'S THIRD FACE** (`budgetFloor`'s height-3 tower);
  NOT relaxable here, and the campaign's open design question;
* `e^{-100} ≤ cs` — ⟦ITEM 2⟧ the HONEST floor.  Was `1 ≤ cs`, FALSE at the witness
  (`cs ≤ 1/10` is a landed proof line; the true value is `≈ 1.86·10^{-10}`).  The
  re-carry is paid inside `S13CapGrid`'s own `gate` exponent margin `3/40 − 2θ₂₉₃ ≥ 0.068`
  (`s16_capgrid_gate_numeric_cs`), so `e^{-100}` is spent, not floored;
* `T₀ ≤ e^{e^{100}}`, `Kq ≤ e^{100}`, `e^{−100} ≤ Ks` — the fuse's three, unchanged
  (`Kq` TRUE with 46 orders spare, `Ks` a second Siegel item, `T₀` forced-equality);
* `S16CofactorSupply_gk` — ⟦RULING 9⟧'s shelved `Rbd`/`Cq` debt, carried;
* `S16BaseScaleCap96_gk` — ⟦ITEM 3⟧ the base-scale cap at the divisor `9.60000096`
  (`Lp ≥ 9.6Λ·(1 + 10^{-8})`) instead of `24`: `2.5×` more room for every consumer, at the
  exact point where `s16_budget_num_96` still closes (the `2(lS/Lp)·llS` leg alone spends
  `2/9.6 = 5/24` of `μ`, so `9.6` is the sharp divisor and the `10^{-8}` pays the rest).

⟦WHAT LEFT THE LIST, EACH REMOVED-BECAUSE-PROVEN⟧ unchanged from `v2`: `(1:ℚ)/2^9 ≤ ε`,
`1/2^20 ≤ δ₀`, `24·Cg/δ₀ ≤ 2^355` (§6.2), `log C ≤ 40` (§6.4), `Mfl ≤ 2^355` (§6.5, under
`S16BandLaneCBounded`).  ⟦WHAT REMAINS FALSE⟧ exactly ONE numeral rider — `Hcap` — plus the
two Siegel items (`x₀`, `Ks`) and the two carried predicates. -/
theorem logChowla2_witnessed_scale_final'_v3 (hband : S16BandLaneCBounded 32000000) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Real.log C ≤ 40 ∧
      Mfl ≤ 2 ^ 355 ∧
      (Kc ≤ 2 ^ 539 → Ct ≤ 2 ^ 23 → (x₀ : ℝ) ≤ Real.exp (Real.exp 275) →
        Hcap ≤ s15WitFloor2 →
        Real.exp (-100) ≤ cs → T₀ ≤ Real.exp (Real.exp 100) → Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, ∃ (R : ChowlaRegime) (M : ℕ),
          R.eps = ε ∧ R.Hlo = s15WitFloor2 ∧ g R.Hhi R.ω ≤ R.x ∧
          S15Sel''_gk 32000000 Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M ∧
          (S16CofactorSupply_gk 32000000 Cq R M → S16BaseScaleCap96_gk 32000000 R M →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1, hCgle, hεpin,
    hδpin, hMflb, hbody⟩ :=
    logChowla2_conditional_sharp2_nonvacuous_gk'_Mfl_wide 32000000 (by norm_num) hband
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hT₀3, hKq0, hKs0, hC0, hC40, hsupply⟩ :=
    s15_crossing_supplied_wide_gk 32000000
  refine ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hT₀3, hKq0, hKs0, hC0,
    hCgle, hεpin, hδpin, hC40, hMflb, ?_⟩
  intro h4 h5 h6 h8 hcs hT₀ hKq hKs g
  obtain ⟨R, M, hReps, hHlo, hRg, hsel, hfire⟩ := hbody h4 h5 h6 h8 g
  refine ⟨R, M, hReps, hHlo, hRg, hsel, ?_⟩
  intro hcof hcap
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact s15WitFloor2_ll
  have hblk : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      s13BlockFloor_gk 32000000 M ≤ A + s := by
    intro H L q j A s hb
    exact s15_block_at_socket_gk 32000000 hb
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (hsupply hcs hT₀ hKq hKs R M hsel.hM hfl hblk hcof hcap)



end Salt.MR

