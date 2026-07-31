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

