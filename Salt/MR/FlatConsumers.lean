/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S15Compose
import Salt.MR.DoorLinear
import Salt.Entropy.Chowla.TowerFlatExport

/-!
# THE FLAT SHAPE at the CONSUMERS — the λ-engine face (freeze F-5, probe F10)

The road's carrier twins (`Salt.MR.HloExportMRFlat`) move the tower conjunct

```
(50 ≤ loglog H₋ → loglog H₊ ≤ loglog H₋ ^ (9/2))          -- landed
(50 ≤ loglog H₋ → loglog H₊ ≤ exp (loglog H₋ / 2))        -- flat
```

through the `∃`-payloads for free.  This file pays for the OTHER side: the places
where the conjunct is a HYPOTHESIS and is READ AS A NUMBER.  Because
`λ^{9/2} ≤ e^{λ/2}` on the guard (`pow_nine_halves_le_exp_half`), each flat
consumer twin here is STRICTLY STRONGER than its landed original — that is the
genuine new content of the shape substitution, and `flat_lambda_core`
(FLAT-REF probe F10) is what pays for it.

## §1–§2 — the λ-engine consumers: NO NUMERAL MOVES

`s12c_eps_threshold_at_socket`, `eps_pool_const_pos_at_socket`,
`s15_heps293_at_socket`, `s15_hband4096_at_socket`, `s15_gRows_const_at_socket`
all charge the tower against the socket's `loglog X_d ≥ ½·e^{λ₋}`, i.e. against
an EXPONENTIAL in `λ₋`.  The flat shape `e^{λ₋/2}` is the square root of that, so
the engine closes with the same coefficients and the twins are the landed proofs
with `s12c_lambda_core`/`s15_lambda_core17` replaced by `flat_lambda_core` /
`flat_lambda_core_17`.  Every numeral (`376266`, `10^{14}`, `θ₂₉₃`, `4096`,
`1/500`) is untouched.

## §3 — THE WINDOW CEILING: THE ONE PLACE A NUMERAL MUST MOVE — NAMED LOUDLY

`s13_loglogHhi_le` reads the conjunct against a numeric `λ₋`-window
(`λ₋ ≤ 83.66`, resp. `81.184`) and exports a numeric `λ₊`.  At the `9/2` shape
that export is `4.481·10⁸` (resp. `3.92·10⁸`); at the flat shape the SAME window
gives `e^{41.83} ≤ 1.79·10¹⁸` (resp. `e^{40.592} ≤ 6.6·10¹⁷`) — a factor `4·10⁹`
larger.  The flat twins below are stated at the honest flat ceiling.

⚠ ⟦THE FRONTIER THIS OPENS⟧  Every register face calibrated against `4.481·10⁸`
must be re-priced at `e^{λ₋/2}` before it can consume these twins.  FLAT-REF's §2
says the re-pricing exists and is uniform (`λ₊ ≤ 400·e^{λ₋/2}` against a ceiling
`K ≤ 577·e^{λ₋/2}`, a `400×` margin independent of `A`) — but it goes through
S3's `Adoor M := 2^36·M` LINEAR re-cut, which is the door cone, not this one.
`s13_g2_jfloor` and `s13_gate8` take `Λ` as a PARAMETER, so no twin of them is
needed; they are simply instantiated at the flat ceiling once the door lands.

## §4 — THE FRONTIER, PRICED ON BOTH SIDES

The witness ceiling, the two `blk` gaps that survive it, and the ONE register line
that does not — `lvl` — together with its repair at the landed linear door
`Salt.MR.AdoorL`.  See §4's own preamble below.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — `S12ConstCompose`'s socket consumers at the flat shape -/

/-- `s12c_eps_threshold_at_socket` (`S12ConstCompose.lean:251`) at the FLAT tower
conjunct.  Landed proof, with `flat_lambda_core` in place of `s12c_lambda_core`;
no numeral moves. -/
theorem s12c_eps_threshold_at_socket_flat {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ ε : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000)
    (hε : ε ≤ theta293 - 1 / 500) :
    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
      ≤ (theta293 - ε) * Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hll := s12c_llX_ge hfl hb
  have hcore := flat_lambda_core hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by linarith
  have hcoef : (1 : ℝ) / 500 ≤ theta293 - ε := by linarith
  have hprod : (1 : ℝ) / 500 * ll ≤ (theta293 - ε) * ll :=
    mul_le_mul_of_nonneg_right hcoef hll0
  have h1 : 14 * Λ ≤ 14 * Real.exp (lam / 2) := by linarith
  linarith

/-- `eps_pool_const_pos_at_socket` (`S12ConstCompose.lean:278`) at the FLAT tower
conjunct — §1's stone composed with the flat socket discharge. -/
theorem eps_pool_const_pos_at_socket_flat {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ ε : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hρ : 0 < ρ)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000)
    (hε : ε ≤ theta293 - 1 / 500) :
    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε) ≤ constPool ρ R.Hhi := by
  refine eps_pool_const_pos ?_ hρ (s12c_eps_threshold_at_socket_flat hfl hb hlam htow hrho hε)
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
  have := Real.log_le_log hA0 hAX
  linarith

/-! ## §2 — `S15Compose`'s socket consumers at the flat shape -/

/-- `s15_heps293_at_socket` (`S15Compose.lean:359`) at the FLAT tower conjunct. -/
theorem s15_heps293_at_socket_flat {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hρ : 0 < ρ)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000) :
    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi := by
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpool : constPool ρ R.Hhi = Real.exp (Real.log ρ - Real.log 376266 - 14 * Λ) := by
    rw [constPool_def, hLamdef, Real.exp_sub, Real.exp_sub, Real.exp_log hρ,
      Real.exp_log (by norm_num : (0 : ℝ) < 376266), div_div]
  have hlhs : (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) = Real.exp (-(theta293 * ll)) := by
    rw [Real.rpow_def_of_pos hX0, hlldef]; congr 1; ring
  rw [hlhs, hpool]
  refine Real.exp_le_exp.mpr ?_
  have hθ : (0.0034 : ℝ) ≤ theta293 := by have := s13_theta293_margin_lo; linarith
  have hll := s12c_llX_ge hfl hb
  have hcore := flat_lambda_core_17 hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by
    have : (0 : ℝ) < Real.exp lam / 2 := by positivity
    linarith [hll]
  have hkey : 14 * Λ + 13 + (-Real.log ρ) ≤ theta293 * ll := by
    have h1 : 14 * Λ ≤ 14 * Real.exp (lam / 2) := by linarith [htow]
    have h2 : theta293 * ll ≥ 0.0034 * (Real.exp lam / 2) := by
      nlinarith [hθ, hll, hll0]
    nlinarith [h1, h2, hcore, hrho]
  linarith [hkey, hlog376]

/-- `s15_hband4096_at_socket` (`S15Compose.lean:400`) at the FLAT tower
conjunct. -/
theorem s15_hband4096_at_socket_flat {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hρ : 0 < ρ)
    (hlam : 50 ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000) :
    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500) * constPool ρ R.Hhi := by
  set lam : ℝ := Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) with hlamdef
  set Λ : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hLamdef
  set ll : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hlldef
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpool : constPool ρ R.Hhi = Real.exp (Real.log ρ - Real.log 376266 - 14 * Λ) := by
    rw [constPool_def, hLamdef, Real.exp_sub, Real.exp_sub, Real.exp_log hρ,
      Real.exp_log (by norm_num : (0 : ℝ) < 376266), div_div]
  have hlhs : (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
      = Real.exp ((1 - (1 : ℝ) / 500) * ll) := by
    rw [Real.rpow_def_of_pos hX0, hlldef]; congr 1; ring
  rw [hlhs, hpool, ← Real.exp_add]
  have h4096 : (4096 : ℝ) ≤ Real.exp 9 := by
    have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have hc : (2.7 : ℝ) ^ (9 : ℕ) ≤ (Real.exp 1) ^ (9 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 9
    have hn : (4096 : ℝ) ≤ (2.7 : ℝ) ^ (9 : ℕ) := by norm_num
    rw [h]; linarith
  refine le_trans h4096 (Real.exp_le_exp.mpr ?_)
  have hll := s12c_llX_ge hfl hb
  have hcore := flat_lambda_core_17 hlam
  have hlog376 := s12c_log376266
  have hexp0 : (0 : ℝ) < Real.exp lam := Real.exp_pos _
  have hll0 : (0 : ℝ) ≤ ll := by
    have : (0 : ℝ) < Real.exp lam / 2 := by positivity
    linarith [hll]
  have h1 : 14 * Λ ≤ 14 * Real.exp (lam / 2) := by linarith [htow]
  have h2 : (1 - (1 : ℝ) / 500) * ll ≥ 0.0017 * Real.exp lam := by nlinarith [hll, hll0]
  linarith [h1, h2, hcore, hrho, hlog376]

/-- `s15_gRows_const_at_socket` (`S15Compose.lean:447`) at the FLAT tower
conjunct — the `⟦B1'-3⟧` binder at the constant pool, flat. -/
theorem s15_gRows_const_at_socket_flat {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hM : 1 ≤ M)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000)
    (hbud : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        + (1 / 3) * Real.log (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ))
        + (-Real.log ρ)
      ≤ (1 / 12) * ((Adoor M : ℕ) : ℝ) * Real.log 2) :
    GRowsZeroGate''' M (A + s) 0 (constPool ρ R.Hhi) := by
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  have hQ0 := s15_loglogQ1_nonneg hM
  obtain ⟨-, hL50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hAs : 0 < A + s := by omega
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hllle : Real.log (Real.log (((A + s : ℕ)) : ℝ)) ≤ Real.log (((A + s : ℕ)) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hll := s12c_llX_ge hfl hb
  have hcore := flat_lambda_core_17 hlam50
  have hexp0 : (0 : ℝ) < Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) := Real.exp_pos _
  have hendbud : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + (-Real.log ρ)
      ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h1 : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        ≤ 14 * Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := by linarith
    linarith [hcore, hll, hllle, hrho, h1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact s15_level1_of_budget hM hρ0 (by linarith)
  · exact s15_endpt_at_constPool hAs hρ0 hendbud
  · refine s15_p2_of_budget hM hρ0 ?_
    linarith [hbud, hQ0, hL50, hlogρ]
  · exact s15_dens_at_zero hρ0.le

/-- `s15_gRows_const_at_socket_gk` (`S15Compose.lean:1866`) — the lever's copy — at
the FLAT tower conjunct.  This is the form `S16Budget`'s HOP 4 fires. -/
theorem s15_gRows_const_at_socket_gk_flat (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hM : 1 ≤ M)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000)
    (hbud : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        + (1 / 3) * Real.log (Real.log ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ))
        + (-Real.log ρ)
      ≤ (1 / 12) * ((Adoor M : ℕ) : ℝ) * Real.log 2) :
    GRowsZeroGate'''_gk K M (A + s) 0 (constPool ρ R.Hhi) := by
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  have hQ0 := s15_loglogQ1_nonneg_gk K hM
  obtain ⟨-, hL50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hAs : 0 < A + s := by omega
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hllle : Real.log (Real.log (((A + s : ℕ)) : ℝ)) ≤ Real.log (((A + s : ℕ)) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hll := s12c_llX_ge hfl hb
  have hcore := flat_lambda_core_17 hlam50
  have hexp0 : (0 : ℝ) < Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ))) := Real.exp_pos _
  have hendbud : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + (-Real.log ρ)
      ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h1 : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        ≤ 14 * Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := by linarith
    linarith [hcore, hll, hllle, hrho, h1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact s15_level1_of_budget_gk K hM hρ0 (by linarith)
  · exact s15_endpt_at_constPool hAs hρ0 hendbud
  · refine s15_p2_of_budget_gk K hM hρ0 ?_
    linarith [hbud, hQ0, hL50, hlogρ]
  · exact s15_dens_at_zero hρ0.le

/-! ## §3 — the window ceiling at the flat shape (THE ONE NUMERAL THAT MOVES) -/

/-- `e^{41.83} ≤ 1.79·10¹⁸` — the flat window ceiling's numeral, from
`e ≤ 2.72`. -/
theorem flat_exp_window_83 : Real.exp (8366 / 100 / 2) ≤ 1790000000000000000 := by
  have he1 : Real.exp 1 ≤ 2.72 := by have := Real.exp_one_lt_d9; linarith
  have hmono : Real.exp (8366 / 100 / 2) ≤ Real.exp (42 : ℝ) :=
    Real.exp_le_exp.mpr (by norm_num)
  have h42 : Real.exp (42 : ℝ) = (Real.exp 1) ^ (42 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  have hc : (Real.exp 1) ^ (42 : ℕ) ≤ (2.72 : ℝ) ^ (42 : ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he1 42
  have hn : (2.72 : ℝ) ^ (42 : ℕ) ≤ 1790000000000000000 := by norm_num
  rw [h42] at hmono
  linarith

/-- `e^{40.592} ≤ 6.6·10¹⁷` — the tight flat window ceiling's numeral. -/
theorem flat_exp_window_81 : Real.exp (81184 / 1000 / 2) ≤ 660000000000000000 := by
  have he1 : Real.exp 1 ≤ 2.72 := by have := Real.exp_one_lt_d9; linarith
  have hmono : Real.exp (81184 / 1000 / 2) ≤ Real.exp (41 : ℝ) :=
    Real.exp_le_exp.mpr (by norm_num)
  have h41 : Real.exp (41 : ℝ) = (Real.exp 1) ^ (41 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  have hc : (Real.exp 1) ^ (41 : ℕ) ≤ (2.72 : ℝ) ^ (41 : ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he1 41
  have hn : (2.72 : ℝ) ^ (41 : ℕ) ≤ 660000000000000000 := by norm_num
  rw [h41] at hmono
  linarith

/-- **⟦THE WINDOW CEILING, FLAT⟧** — `s13_loglogHhi_le` (`S13FramesA.lean:450`) at
the FLAT tower conjunct.  The window `λ₋ ≤ 83.66` is the landed one; the exported
ceiling is NOT: `4.481·10⁸` becomes `1.79·10¹⁸`.  See this file's ⚠ note — every
register face calibrated to the `9/2` ceiling must be re-priced against
`e^{λ₋/2}` (FLAT-REF §2's `400×`-margin accounting, through S3's `Adoor`-linear
re-cut) before it consumes this twin. -/
theorem s13_loglogHhi_le_flat {R : ChowlaRegime}
    (h50 : 50 ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (htow : 50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2))
    (hlam : Real.log (Real.log (R.Hlo : ℝ)) ≤ 8366 / 100) :
    Real.log (Real.log (R.Hhi : ℝ)) ≤ 1790000000000000000 := by
  refine le_trans (htow h50) (le_trans (Real.exp_le_exp.mpr ?_) flat_exp_window_83)
  linarith

/-- **⟦THE WINDOW CEILING, FLAT, AT THE HONEST `λ₋`⟧** — `s13_loglogHhi_le_tight`
(`S13FramesA.lean:1094`) at the FLAT tower conjunct: the census window
`λ₋ ≤ 81.184` exports `6.6·10¹⁷` in place of `3.92·10⁸`.  `s13_g2_jfloor` and
`s13_gate8` take `Λ` as a parameter, so they need no twin — they are instantiated
at this ceiling. -/
theorem s13_loglogHhi_le_tight_flat {R : ChowlaRegime}
    (h50 : 50 ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (htow : 50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2))
    (hlam : Real.log (Real.log (R.Hlo : ℝ)) ≤ 81184 / 1000) :
    Real.log (Real.log (R.Hhi : ℝ)) ≤ 660000000000000000 := by
  refine le_trans (htow h50) (le_trans (Real.exp_le_exp.mpr ?_) flat_exp_window_81)
  linarith

/-! ## §4 — THE FRONTIER, PRICED: the witness ceiling and the `lvl` line

`S16Budget`'s HOP 5 (`logChowla2_conditional_sharp2_nonvacuous_gk'_Mfl`) reads the
conjunct through `S15Witness.s15w2_tower_bound` at the witness window
`λ₋ ≤ 277.2589`, and hands the resulting `λ₊`-ceiling to `s15_sel''_witness_gk'`
as a LITERAL hypothesis `λ₊ ≤ 9.87·10¹⁰`.  That is where this wave stops.  The
four theorems below price the stop exactly, so the next wave does not have to
re-discover it.

**(1) THE FLAT CEILING IS `3·10⁶⁰`**, not `9.87·10¹⁰` (`flat_exp_window_277`,
`s15w2_tower_bound_flat`).

**(2) THE `blk` GAPS SURVIVE IT UNTOUCHED** — `s15w2_gap_flat`,
`s15w2_gap2_flat` are `S15Witness`' two `2^1541`-sized register gaps at the FLAT
ceiling; they clear by ~400 orders of magnitude.  Those lines need no re-cut.

**(3) THE `lvl` LINE IS THE ONE THAT BREAKS — AND THE LINEAR DOOR FIXES IT.**
`s15w2_lvl_num'` spends `26 + 14·λ₊ + loglog𝒬/3 + log(1/ρ)` against
`(1/12)·Adoor(2^355)·log 2 = (1/12)·2^36·356·log 2 ≈ 1.413·10¹²`, and at the
landed ceiling the `14·λ₊` term alone is `1.3818·10¹²` — 0.48% of margin (the
landed docstring says so).  At the flat ceiling `14·λ₊ ≈ 4.2·10⁶¹`: the line
fails by 49 orders of magnitude.  At S3's D1 LINEAR door
(`Salt.MR.AdoorL M = 2^36·M`, already landed) the same line reads
`(1/12)·2^391·log 2 ≈ 2.91·10¹¹⁶` and **clears by 55 orders of magnitude** —
`s15w2_lvl_num_flat_doorL`, with `adoorL_pow355` tying the numeral to the door.

So the frontier is not a wall: it is the `Adoor`-linear re-cut, exactly as
FLAT-REF §2 ruled, and the decisive line is now kernel-priced on both sides. -/

/-- `e^{138.63} ≤ 3·10⁶⁰` — the flat window ceiling at the WITNESS window
`λ₋ ≤ 277.2589` (`S15Witness.s15WitFloor2`). -/
theorem flat_exp_window_277 : Real.exp (2772589 / 10000 / 2) ≤ 3 * 10 ^ 60 := by
  have he1 : Real.exp 1 ≤ 2.72 := by have := Real.exp_one_lt_d9; linarith
  have hmono : Real.exp (2772589 / 10000 / 2) ≤ Real.exp (139 : ℝ) :=
    Real.exp_le_exp.mpr (by norm_num)
  have h139 : Real.exp (139 : ℝ) = (Real.exp 1) ^ (139 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  have hc : (Real.exp 1) ^ (139 : ℕ) ≤ (2.72 : ℝ) ^ (139 : ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he1 139
  have hn : (2.72 : ℝ) ^ (139 : ℕ) ≤ 3 * 10 ^ 60 := by norm_num
  rw [h139] at hmono
  linarith

/-- `S15Witness.s15w2_tower_bound` at the FLAT shape: on the witness window the
flat conjunct exports `λ₊ ≤ 3·10⁶⁰` (against the landed `9.87·10¹⁰`). -/
theorem s15w2_tower_bound_flat {x : ℝ} (_h50 : 50 ≤ x) (hx : x ≤ 2772589 / 10000) :
    Real.exp (x / 2) ≤ 3 * 10 ^ 60 :=
  le_trans (Real.exp_le_exp.mpr (by linarith)) flat_exp_window_277

set_option exponentiation.threshold 4000 in
/-- The linear door at the witness scale: `A_L(2^355) = 2^36·2^355 = 2^391`. -/
theorem adoorL_pow355 : ((AdoorL (2 ^ 355) : ℕ) : ℝ) = (2 : ℝ) ^ (391 : ℕ) := by
  rw [AdoorL_cast]
  push_cast
  ring

set_option exponentiation.threshold 4000 in
/-- **⟦THE `lvl` LINE AT THE FLAT CEILING, AT THE LINEAR DOOR⟧** — `s15w2_lvl_num'`
with `X ≤ 3·10⁶⁰` in place of `X ≤ 9.87·10¹⁰` and `Adoor(2^355) = 2^36·356`
replaced by `A_L(2^355) = 2^391`.  The line clears by a factor `~7·10⁵⁴`. -/
theorem s15w2_lvl_num_flat_doorL {X Q Y : ℝ} (hX : X ≤ 3 * 10 ^ 60) (hQ : Q ≤ 277)
    (hY : -Y ≤ 43) :
    26 + 14 * X + 1 / 3 * Q + -Y ≤ 1 / 12 * (2 : ℝ) ^ (391 : ℕ) * Real.log 2 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlow : (5 : ℝ) * 10 ^ 117 ≤ (2 : ℝ) ^ (391 : ℕ) := by norm_num
  have hmul : (5 * 10 ^ 117 : ℝ) * 0.6931471803 ≤ (2 : ℝ) ^ (391 : ℕ) * Real.log 2 :=
    mul_le_mul hlow h2.le (by norm_num) (by positivity)
  linarith [hmul, hX, hQ, hY]

set_option exponentiation.threshold 4000 in
/-- `S15Witness`' first `blk`-register gap at the FLAT ceiling: no re-cut needed. -/
theorem s15w2_gap_flat : (1 : ℝ) + 18 * (3 * 10 ^ 60) ≤ (2 : ℝ) ^ (1541 : ℕ) := by
  norm_num

set_option exponentiation.threshold 4000 in
/-- `S15Witness`' second `blk`-register gap at the FLAT ceiling: no re-cut needed. -/
theorem s15w2_gap2_flat :
    (2 : ℝ) ^ (1542 : ℕ) + 1 + 18 * (3 * 10 ^ 60) ≤ 4 * (2 : ℝ) ^ (1541 : ℕ) := by
  norm_num

end Salt.MR
