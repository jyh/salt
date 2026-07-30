/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# THE 318-BIT LEVER — the honest-threshold twins of the `hpt`/`bigXi` chain

`Salt.M5BigO.N0 = 2^100` is a Brun-lane convenience threshold (a power of two so
that `log N0 = 100·log 2` and `N0^(1/10) = 1024` are exact).  It is imported into
the Goldbach-energy chain by `hpt_large`, whose threshold is
`H₁ = max N0 (max tA (max tB tD))`, and `H₁` is then SQUARED inside
`hpt_holds`'s small-`H` absorption constant

  `CS = (ε²H₁+1)²·(log H₁)²/(2ε²)`,

which is squared AGAIN through `C₁²` in `hsq_holds3`'s `C = 2·K_lcm·C₁²·ε⁶`, into
`C_d`, into `K = 16·C_d/ε¹⁶`, into `1/δ₀`.  Every bit of `log₂ H₁` therefore costs
FOUR bits of `log₂ K`.  CG-SCOPE priced the resulting `N0` share at ≈318 of the
602 bits that block the S11 compose.

This file is purely ADDITIVE: nothing landed is touched.  It mints the twins that
run the same chain at an honest threshold.  THE HONEST-`H₁` AUDIT (byte-read of
every consumer):

* `N0` is consumed by `hpt_large` at exactly three places — `2 ≤ H`;
  `hz2 : 2 ≤ z` (via `M5BigO.zN_ge_z0`, i.e. `z ≥ M3Assembly.z0 = 100`); and
  `hLzsq` (via `M5BigO.logZ_ge`, i.e. `log z ≥ (1/20)·log H`).  The `z ≥ 100`
  fact is used ONLY to produce `2 ≤ z` — the sieve's own `z`-floor arrives
  separately as `tB`.  `logZ_ge`'s proof needs `N^(1/10) ≥ 2` and
  `log N ≥ 20·log 2`, i.e. `N ≥ 2^20`.  **The honest `N0` is `2^20`, not
  `2^100`** (`logZ_ge_twenty`, `z_ge_four` below).
* `tA = ⌈4/ε²⌉₊` (`four_le_threshold`) — `10^6` at `ε = 1/500`.
* `tD = ⌈(2/ε²)^(10/9)⌉₊ + 1` (`rpow_ge_threshold`) — `≈2.2·10^6` at `ε = 1/500`.
* `tB = ⌈z₀^10⌉₊ + 1` where `z₀` is the Selberg main-term threshold of
  `M3Assembly.exists_const_mainTermSum_ge`, i.e. `z₀ = M3Assembly.z0 = 100`
  raised to the tenth power by the truncation choice `z = ⌊H^(1/10)⌋₊`:
  **`tB = 10^20 + 1 ≈ 2^66.4`.**  So killing `N0` alone leaves `H₁ ≈ 2^66.4`
  and recovers only ≈137 of the 317 bits.  `tB` is therefore the SECOND honest
  threshold, and it is itself soft: `z₀ = 100` exists only to give
  `log z ≥ 4` in `M3Assembly.D3`.  Re-running that page at `γ = 1/16` instead of
  `γ = 1/8` gives `z₀ = 16` with `c₀ = 1/256` instead of `1/64`
  (`mainTermSum_ge_of_sixteen`), so `tB = 16^10 + 1 ≈ 2^40`, and the `c₀` loss is
  invisible (`800/c₀ = 204800` sits under `102400/ε² = 2.56·10^10`).
* The `(ε²H₁+1)²/(2ε²)` shape of `CS` is itself lossy by a factor `H₁/2`: the
  landed proof bounds the window card at `H₁` and the frozen fraction at `H = 2`
  SEPARATELY.  Doing both at the same `H` gives
  `CS' = (ε²H₁ + 2 + 1/(2ε²))·(log H₁)²` — the twin below.

THE LEDGER (at `ε = 1/500`, in bits of `log₂ C₁`; `log₂ K` moves by TWICE each):

| step | `H₁` | `log₂ C₁` | `Δ log₂ K` |
|---|---|---|---|
| landed | `2^100` | 193.30 | — |
| + honest `N0 = 2^20` (`H₁ → tB = 10^20+1`) | `2^66.4` | 125.00 | 136.6 |
| + sharpened `CS'` | `2^66.4` | 59.56 | 130.9 |
| + `z₀ = 16` (`H₁ → 16^10`, taken as `T = 2^41`) | `2^41` | 34.93 | 49.3 |
| **total** | | **`≤ 35`** | **316.6** |

i.e. `log₂ K : 538.2 → 221.6` (`bigXi_bounded_500`), the whole `N0` share of
CG-SCOPE's 602-bit ledger, landing on CG-SCOPE's `102400/ε²` floor
(`log₂ CL = 34.58`, worth 69 bits of `K` — the residual).

No `sorry`, no `native_decide`, no new axioms.
-/
import Salt.Entropy.Chowla.GoldbachEnergyFinal

open ArithmeticFunction Finset
open scoped BigOperators Pointwise

namespace Salt.Entropy.Chowla

/-! ## §1 — the Selberg main-term floor at `z₀ = 16`

`M3Assembly.exists_const_mainTermSum_ge` hides `(c₀, z₀) = (1/64, 100)` behind an
`∃`; `z₀ = 100` is forced only by `D3`'s `log z ≥ 4`.  Re-run the same three steps
at `γ = 1/16` (so `log z ≥ 8/3` suffices, and `log 16 = 4 log 2 = 2.7726 > 8/3`).
-/

/-- `log z ≥ 8/3` for `z ≥ 16` (`log 16 = 4·log 2`). -/
lemma log_ge_eight_thirds {z : ℕ} (hz : 16 ≤ z) : (8 / 3 : ℝ) ≤ Real.log z := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hzR : (16 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hmono : Real.log (16 : ℝ) ≤ Real.log z := Real.log_le_log (by norm_num) hzR
  rw [h16] at hmono; linarith

/-- The `γ = 1/16` twin of `M3Assembly.D3`: the numeric core of Step D at
`z₀ = 16`.  (The identity is `log(√z/2)/2 − (1−log 2)/2 = log z/4 − 1/2`, so the
requirement is exactly `(3/16)·log z ≥ 1/2`.) -/
lemma D3_sixteen {z : ℕ} (hz : 16 ≤ z) :
    Real.log (Real.sqrt (z : ℝ) / 2) / 2 - (1 - Real.log 2) / 2
      ≥ (1 / 16 : ℝ) * Real.log z := by
  have hzR : (0 : ℝ) ≤ (z : ℝ) := by positivity
  have hlogsqrt : Real.log (Real.sqrt (z : ℝ)) = Real.log z / 2 := Real.log_sqrt hzR
  have hzpos : (0 : ℝ) < (z : ℝ) := by
    have : (16 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    linarith
  have hlogdiv : Real.log (Real.sqrt (z : ℝ) / 2)
      = Real.log (Real.sqrt (z : ℝ)) - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num)]
  have h83 := log_ge_eight_thirds hz
  rw [hlogdiv, hlogsqrt]
  linarith

/-- The `γ = 1/16` twin of `M3Assembly.stepD`:
`oddHarmonicSum (√z − 1) ≥ (1/16)·log z` for `z ≥ 16`. -/
theorem stepD_sixteen {z : ℕ} (hz : 16 ≤ z) :
    _root_.oddHarmonicSum (z.sqrt - 1) ≥ (1 / 16 : ℝ) * Real.log z := by
  have hsqrt_ge4 : (4 : ℕ) ≤ z.sqrt := Nat.le_sqrt.mpr (by omega)
  have hsqrt_ge1 : (1 : ℕ) ≤ z.sqrt := by omega
  have hD2 : (z.sqrt : ℝ) > Real.sqrt (z : ℝ) - 1 := by
    have := Salt.M3Assembly.sqrt_real_lt_nat_sqrt_succ z
    linarith
  have hcast : ((z.sqrt - 1 : ℕ) : ℝ) = (z.sqrt : ℝ) - 1 := by
    push_cast [Nat.cast_sub hsqrt_ge1]
    ring
  have hsqrtR_ge4 : (4 : ℝ) ≤ Real.sqrt (z : ℝ) := by
    have hz16 : (16 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    have hmono := Real.sqrt_le_sqrt hz16
    have h4 : Real.sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h4] at hmono
  have hhalf : Real.sqrt (z : ℝ) - 2 ≥ Real.sqrt (z : ℝ) / 2 := by linarith
  have hkey : ((z.sqrt - 1 : ℕ) : ℝ) ≥ Real.sqrt (z : ℝ) / 2 := by
    rw [hcast]; linarith
  have hhalfpos : (0 : ℝ) < Real.sqrt (z : ℝ) / 2 := by linarith
  have hN35 := _root_.oddHarmonicSum_ge (z.sqrt - 1)
  have hmono : Real.log (Real.sqrt (z : ℝ) / 2) ≤ Real.log ((z.sqrt - 1 : ℕ) : ℝ) :=
    Real.log_le_log hhalfpos hkey
  have hD3 := D3_sixteen hz
  linarith

/-- **The `z₀ = 16` main-term floor** — the exposed, lowered twin of
`M3Assembly.exists_const_mainTermSum_ge` (which is `(c₀, z₀) = (1/64, 100)` behind
an `∃`).  Trading `c₀ = 1/64 → 1/256` buys `z₀ = 100 → 16`, i.e. `tB = z₀^10`
drops from `10^20` to `16^10 ≈ 2^40` — worth ≈49 bits of `log₂ K` (once the
sharpened `CS'` is in place), while the `c₀` loss (`800/c₀ : 51200 → 204800`)
never surfaces under `102400/ε² = 2.56·10^10`. -/
theorem mainTermSum_ge_of_sixteen {z : ℕ} (hz : 16 ≤ z) :
    (1 / 256 : ℝ) * (Real.log z) ^ 2 ≤ Salt.M3Assembly.mainTermSum z := by
  have hsqrt_ge1 : (1 : ℕ) ≤ z.sqrt := Nat.le_sqrt.mpr (by omega)
  have hlog := log_ge_eight_thirds hz
  have hD := stepD_sixteen hz
  have hpos : (0 : ℝ) ≤ (1 / 16 : ℝ) * Real.log z := by linarith
  have hsq : ((1 / 16 : ℝ) * Real.log z) ^ 2
      ≤ (_root_.oddHarmonicSum (z.sqrt - 1)) ^ 2 :=
    pow_le_pow_left₀ hpos hD 2
  have hchain := Salt.M3Assembly.mainTermSum_ge_oddHarmonicSum_sq hsqrt_ge1
  have heq : ((1 / 16 : ℝ) * Real.log z) ^ 2 = (1 / 256 : ℝ) * (Real.log z) ^ 2 := by ring
  rw [heq] at hsq
  linarith

/-! ## §2 — the `M5BigO` consumers at the honest threshold `2^20` -/

/-- **The honest small-`H` threshold**: `2^20`, replacing `M5BigO.N0 = 2^100`.
(Chosen as a power of two so that `N0'^(1/10) = 4` and `log N0' = 20·log 2` are
exact — the same design as `N0`, eighty bits lower.) -/
def N0' : ℕ := 2 ^ 20

lemma N0'_cast : (N0' : ℝ) = (2 : ℝ) ^ (20 : ℕ) := by unfold N0'; push_cast; ring

/-- `H^(1/10) ≥ 4` for `H ≥ N0' = 2^20` (exactly: `(2^20)^(1/10) = 4`). -/
lemma four_le_rpow_tenth {H : ℕ} (hH : N0' ≤ H) : (4 : ℝ) ≤ (H : ℝ) ^ (1 / 10 : ℝ) := by
  have hcast : (N0' : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hmono := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (N0' : ℝ)) hcast
    (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hval : (N0' : ℝ) ^ (1 / 10 : ℝ) = 4 := by
    rw [N0'_cast, ← Real.rpow_natCast (2 : ℝ) 20,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rwa [hval] at hmono

/-- `4 ≤ z H` for `H ≥ N0'` (the `2 ≤ z` that `M5BigO.zN_ge_z0` was supplying at
`2^100`, with room to spare). -/
lemma z_ge_four {H : ℕ} (hH : N0' ≤ H) : 4 ≤ Salt.M5Assembly.z H :=
  Nat.le_floor (by exact_mod_cast four_le_rpow_tenth hH)

/-- **The honest `logZ_ge`** (twin of `M5BigO.logZ_ge`, whose threshold is
`2^100`): `log z ≥ (1/20)·log H` for `H ≥ 2^20`.  The landed proof needs only
`H^(1/10) ≥ 2` and `log H ≥ 20·log 2`; both hold from `2^20`. -/
lemma logZ_ge_twenty {H : ℕ} (hH : N0' ≤ H) :
    (1 / 20 : ℝ) * Real.log H ≤ Real.log (Salt.M5Assembly.z H) := by
  have h4 := four_le_rpow_tenth hH
  have hlt : (H : ℝ) ^ (1 / 10 : ℝ) < (Salt.M5Assembly.z H : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hzgt : (Salt.M5Assembly.z H : ℝ) > (H : ℝ) ^ (1 / 10 : ℝ) / 2 := by linarith
  have hpos : (0 : ℝ) < (H : ℝ) ^ (1 / 10 : ℝ) / 2 := by linarith
  have hmono : Real.log ((H : ℝ) ^ (1 / 10 : ℝ) / 2)
      ≤ Real.log (Salt.M5Assembly.z H : ℝ) := Real.log_le_log hpos (le_of_lt hzgt)
  have hH1 : (1 : ℕ) ≤ H := le_trans (by unfold N0'; norm_num) hH
  have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  have hlogdiv : Real.log ((H : ℝ) ^ (1 / 10 : ℝ) / 2)
      = Real.log ((H : ℝ) ^ (1 / 10 : ℝ)) - Real.log 2 :=
    Real.log_div (by positivity) (by norm_num)
  have hlogrpow : Real.log ((H : ℝ) ^ (1 / 10 : ℝ)) = (1 / 10) * Real.log H :=
    Real.log_rpow hHpos _
  -- `log H ≥ 20 log 2` from `H ≥ 2^20`
  have h20log2 : (20 : ℝ) * Real.log 2 ≤ Real.log H := by
    have hcast : (N0' : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    have hpos0 : (0 : ℝ) < (N0' : ℝ) := by rw [N0'_cast]; positivity
    have hm : Real.log (N0' : ℝ) ≤ Real.log H := Real.log_le_log hpos0 hcast
    have hval : Real.log (N0' : ℝ) = 20 * Real.log 2 := by
      rw [N0'_cast, Real.log_pow]; norm_num
    linarith [hm, hval]
  rw [hlogdiv, hlogrpow] at hmono
  linarith

/-! ## §3 — threshold transfers (numeral-friendly, no `∃` witnesses) -/

/-- `z₀ ≤ z H` from `z₀^10 ≤ H` (the `tB` obligation, with the `⌈·⌉₊` witness of
`rpow_ge_threshold` replaced by a plain power inequality). -/
lemma z_ge_of_pow_le {z₀ H : ℕ} (h : ((z₀ : ℝ)) ^ (10 : ℕ) ≤ (H : ℝ)) :
    z₀ ≤ Salt.M5Assembly.z H := by
  refine Nat.le_floor ?_
  have hmono := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((z₀ : ℝ)) ^ (10 : ℕ)) h
    (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hval : (((z₀ : ℝ)) ^ (10 : ℕ)) ^ (1 / 10 : ℝ) = (z₀ : ℝ) := by
    rw [← Real.rpow_natCast (z₀ : ℝ) 10, ← Real.rpow_mul (by positivity)]
    norm_num
  rwa [hval] at hmono

/-- `c ≤ H^(9/10)` from `c^10 ≤ H^9` (the `tD` obligation, same device). -/
lemma le_rpow_nine_tenths {c : ℝ} (hc : 0 ≤ c) {H : ℕ}
    (h : c ^ (10 : ℕ) ≤ ((H : ℝ)) ^ (9 : ℕ)) : c ≤ (H : ℝ) ^ (9 / 10 : ℝ) := by
  have hmono := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ c ^ (10 : ℕ)) h
    (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hval1 : (c ^ (10 : ℕ)) ^ (1 / 10 : ℝ) = c := by
    rw [← Real.rpow_natCast c 10, ← Real.rpow_mul hc]; norm_num
  have hval2 : (((H : ℝ)) ^ (9 : ℕ)) ^ (1 / 10 : ℝ) = (H : ℝ) ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_natCast (H : ℝ) 9, ← Real.rpow_mul (by positivity)]
    norm_num
  rwa [hval1, hval2] at hmono

/-! ## §4 — the sieve core with `(c₀, z₀)` exposed

`goldBoundingSum_ge_uniform` and `repCount_even_le_primorial` unpack
`M3Assembly.exists_const_mainTermSum_ge`'s `∃`, so their `(c₀, z₀)` are opaque to
every consumer — which is why `hpt_large`'s `tB = ⌈z₀^10⌉₊+1` cannot be evaluated
downstream.  These twins take the main-term floor as a HYPOTHESIS; the proofs are
the landed ones verbatim. -/

/-- The `(c₀, z₀)`-parametric twin of `goldBoundingSum_ge_uniform`. -/
theorem goldBoundingSum_ge_uniform_param (c₀ : ℝ) (z₀ : ℕ)
    (hz₀ : ∀ z : ℕ, z₀ ≤ z → c₀ * (Real.log z) ^ 2 ≤ Salt.M3Assembly.mainTermSum z) :
    ∀ (n P : ℕ) (hn : 2 ∣ n) (hP : Squarefree P), n ≠ 0 →
      ∀ (z : ℕ), z₀ ≤ z → ∀ (hlvl : (1 : ℝ) ≤ (z : ℝ) ^ 2),
        (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)
            ⊆ P.divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ (z : ℝ) ^ 2) →
        c₀ * (Real.log z) ^ 2 / sTrunc2 n
          ≤ Salt.SelbergPort.selbergBoundingSum
              (goldSelbergSieve n P hn hP ((z : ℝ) ^ 2) hlvl) := by
  intro n P hn hP hn0 z hz hlvl hsub
  have hcop_le :
      (∑ m ∈ ((Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)).filter
          (fun m => Nat.Coprime m n), Salt.M3Expansion.gTwin m)
        ≤ ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ := by
    calc (∑ m ∈ ((Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)).filter
            (fun m => Nat.Coprime m n), Salt.M3Expansion.gTwin m)
        = ∑ m ∈ ((Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)).filter
            (fun m => Nat.Coprime m n), (goldEnergySieve n P hn hP).selbergTerms m := by
          refine Finset.sum_congr rfl (fun m hm => ?_)
          rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hm
          exact (selbergTerms_eq_gTwin_of_coprime m hm.1.2.1 hm.1.2.2 hm.2).symm
      _ ≤ ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun ℓ hℓ _ => ?_)
          rw [Finset.mem_filter, Finset.mem_range] at hℓ
          exact goldSelbergTerms_nonneg_of_odd hℓ.2.1 hℓ.2.2
  have hcarrier : c₀ * (Real.log z) ^ 2 / sTrunc2 n
      ≤ ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
          (goldEnergySieve n P hn hP).selbergTerms ℓ := by
    rw [div_le_iff₀ (sTrunc2_pos hn0)]
    calc c₀ * (Real.log z) ^ 2
        ≤ Salt.M3Assembly.mainTermSum z := hz₀ z hz
      _ ≤ sTrunc2 n * ∑ m ∈ ((Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)).filter
            (fun m => Nat.Coprime m n), Salt.M3Expansion.gTwin m :=
          mainTermSum_le_sTrunc2_mul_coprimeSum z hn0
      _ ≤ sTrunc2 n * ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ :=
          mul_le_mul_of_nonneg_left hcop_le (sTrunc2_nonneg n)
      _ = (∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ) * sTrunc2 n := mul_comm _ _
  exact le_trans hcarrier (carrierSum_le_selbergBoundingSum ((z : ℝ) ^ 2) hlvl z hsub)

/-- The `(c₀, z₀)`-parametric twin of `repCount_even_le_primorial`. -/
theorem repCount_even_le_primorial_param (c₀ : ℝ) (hc₀ : 0 < c₀) (z₀ : ℕ)
    (hz₀ : ∀ z : ℕ, z₀ ≤ z → c₀ * (Real.log z) ^ 2 ≤ Salt.M3Assembly.mainTermSum z) :
    ∀ (eps : ℚ) (H n : ℕ), 2 ∣ n → n ≠ 0 →
      ∀ (z : ℕ), z₀ ≤ z → 2 ≤ z → (∀ p ∈ primeWindow eps H, z < p) →
        (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
          ≤ (n : ℝ) * sTrunc2 n / (c₀ * (Real.log z) ^ 2) + ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4 := by
  intro eps H n hn hn0 z hz hz2 hwin
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hlvl : (1 : ℝ) ≤ (z : ℝ) ^ 2 := by nlinarith
  have hP : Squarefree (primorial z) := Salt.M5Assembly.primorial_squarefree z
  have hPz : ∀ q, q.Prime → q ∣ primorial z → q ≤ z :=
    fun q hq hdvd => (hq.dvd_primorial_iff).mp hdvd
  have hsub : (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)
      ⊆ (primorial z).divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ (z : ℝ) ^ 2) := by
    intro ℓ hℓ
    rw [Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hℓz, hℓodd, hℓsq⟩ := hℓ
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨(Squarefree.dvd_primorial hℓsq).trans (primorial_dvd_primorial (le_of_lt hℓz)),
      hP.ne_zero⟩, ?_⟩
    have hℓR : (ℓ : ℝ) ≤ (z : ℝ) := by exact_mod_cast (le_of_lt hℓz)
    exact pow_le_pow_left₀ (Nat.cast_nonneg ℓ) hℓR 2
  have hbound := goldBoundingSum_ge_uniform_param c₀ z₀ hz₀ n (primorial z) hn hP hn0 z hz
    hlvl hsub
  exact goldSiftedSum_le_main_add_err eps H n (primorial z) hn hn0 hP z hz2 hPz hwin
    c₀ hc₀ hlvl hbound

/-- The sieve core at the exposed pair `(c₀, z₀) = (1/256, 16)`. -/
theorem repCount_even_le_primorial_sixteen :
    ∀ (eps : ℚ) (H n : ℕ), 2 ∣ n → n ≠ 0 →
      ∀ (z : ℕ), 16 ≤ z → 2 ≤ z → (∀ p ∈ primeWindow eps H, z < p) →
        (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
          ≤ (n : ℝ) * sTrunc2 n / ((1 / 256 : ℝ) * (Real.log z) ^ 2)
              + ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4 :=
  repCount_even_le_primorial_param (1 / 256) (by norm_num) 16
    (fun _ hz => mainTermSum_ge_of_sixteen hz)

/-! ## §5 — the large-`H` core at an arbitrary honest threshold `T` -/

/-- **The threshold-parametric twin of `hpt_large`.**  Identical proof, with the
four threshold obligations of the landed `H₁ = max N0 (max tA (max tB tD))` taken
as explicit numeric hypotheses on a single `T`:

* `hT0 : 2^20 ≤ T` — replaces `N0 = 2^100` (the honest `logZ_ge`/`2 ≤ z` floor);
* `hTA : 4 ≤ ε²T` — replaces `tA = ⌈4/ε²⌉₊`;
* `hTB : z₀^10 ≤ T` — replaces `tB = ⌈z₀^10⌉₊+1`;
* `hTD : (2/ε²)^10 ≤ T^9` — replaces `tD = ⌈(2/ε²)^(10/9)⌉₊+1`.

All four are monotone in `T`, so `T` may be rounded up to any convenient numeral.
`C₁ = 800/c₀ + 102400/ε²` is now EXPLICIT (the landed statement hides it in an
`∃`). -/
theorem hpt_large_thr (eps : ℚ) (heps : 0 < eps)
    (c₀ : ℝ) (hc₀ : 0 < c₀) (z₀ : ℕ)
    (hsieve : ∀ (eps' : ℚ) (H n : ℕ), 2 ∣ n → n ≠ 0 →
      ∀ (z : ℕ), z₀ ≤ z → 2 ≤ z → (∀ p ∈ primeWindow eps' H, z < p) →
        (repCount (primeWindow eps' H) (primeWindow eps' H) n : ℝ)
          ≤ (n : ℝ) * sTrunc2 n / (c₀ * (Real.log z) ^ 2) + ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4)
    (T : ℕ) (hT0 : N0' ≤ T) (hTA : (4 : ℚ) ≤ eps ^ 2 * (T : ℚ))
    (hTB : ((z₀ : ℝ)) ^ (10 : ℕ) ≤ (T : ℝ))
    (hTD : (2 / (eps : ℝ) ^ 2) ^ (10 : ℕ) ≤ ((T : ℝ)) ^ (9 : ℕ)) :
    ∀ H : ℕ, T ≤ H → ∀ n : ℕ,
      (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
        ≤ (800 / c₀ + 102400 / (eps : ℝ) ^ 2)
            * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hepsq : (0 : ℝ) < (eps : ℝ) ^ 2 := by positivity
  intro H hH n
  have hTHR : (T : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hHN0 : N0' ≤ H := le_trans hT0 hH
  -- Basic facts about H.
  have hH2 : 2 ≤ H := by unfold N0' at hHN0; omega
  have hHpos : 0 < H := by omega
  have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast (by omega : 1 ≤ H)
  have hHposR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hHpos
  have hlogH : (0 : ℝ) < Real.log H := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  have hLnn : (0 : ℝ) ≤ Real.log H := hlogH.le
  -- The frozen main-term coefficient is nonnegative.
  have hfrac_nonneg : (0 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2 :=
    div_nonneg (by positivity) (sq_nonneg _)
  have hCLnn : (0 : ℝ) ≤ 800 / c₀ + 102400 / (eps : ℝ) ^ 2 := by positivity
  -- The window is all odd, and `4 ≤ ε²H`.
  have hAcond : 4 ≤ eps ^ 2 * (H : ℚ) := by
    have hTHQ : (T : ℚ) ≤ (H : ℚ) := by exact_mod_cast hH
    have := mul_le_mul_of_nonneg_left hTHQ (sq_nonneg eps)
    linarith
  -- The truncation `z := ⌊H^(1/10)⌋₊` and its threshold facts.
  set z := Salt.M5Assembly.z H with hzdef
  have hzB : z₀ ≤ z := z_ge_of_pow_le (le_trans hTB hTHR)
  have hz4 : 4 ≤ z := z_ge_four hHN0
  have hz2 : 2 ≤ z := by omega
  have hzR_le : (z : ℝ) ≤ (H : ℝ) ^ (1 / 10 : ℝ) := by
    rw [hzdef]; exact Nat.floor_le (by positivity)
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  -- Window primes exceed `z` (from `z ≤ H^(1/10) ≤ ε²H/2 < p`).
  have hz_le_half : (z : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 := by
    have hTD' : (2 / (eps : ℝ) ^ 2) ^ (10 : ℕ) ≤ ((H : ℝ)) ^ (9 : ℕ) := by
      refine le_trans hTD ?_
      exact pow_le_pow_left₀ (by positivity) hTHR 9
    have hD : 2 / (eps : ℝ) ^ 2 ≤ (H : ℝ) ^ (9 / 10 : ℝ) :=
      le_rpow_nine_tenths (by positivity) hTD'
    have hmul : (2 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ (9 / 10 : ℝ) := by
      rw [div_le_iff₀ hepsq] at hD
      linarith [hD, mul_comm ((H : ℝ) ^ (9 / 10 : ℝ)) ((eps : ℝ) ^ 2)]
    have hsplit : (H : ℝ) ^ (9 / 10 : ℝ) * (H : ℝ) ^ (1 / 10 : ℝ) = (H : ℝ) := by
      rw [← Real.rpow_add hHposR]; norm_num
    have h10nn : (0 : ℝ) ≤ (H : ℝ) ^ (1 / 10 : ℝ) := by positivity
    have hstep : 2 * (H : ℝ) ^ (1 / 10 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
      calc 2 * (H : ℝ) ^ (1 / 10 : ℝ)
          ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ (9 / 10 : ℝ) * (H : ℝ) ^ (1 / 10 : ℝ) :=
            mul_le_mul_of_nonneg_right hmul h10nn
        _ = (eps : ℝ) ^ 2 * (H : ℝ) := by rw [mul_assoc, hsplit]
    linarith [hzR_le]
  have hzwin : ∀ p ∈ primeWindow eps H, z < p := by
    intro p hp
    have hpmem := mem_primeWindow.mp hp
    have hplt : (eps : ℝ) ^ 2 * (H : ℝ) / 2 < (p : ℝ) := by
      have := hpmem.2.2
      have hcast : ((eps ^ 2 * (H : ℚ) / 2 : ℚ) : ℝ) < ((p : ℚ) : ℝ) := by exact_mod_cast this
      push_cast at hcast; linarith [hcast]
    have : (z : ℝ) < (p : ℝ) := lt_of_le_of_lt hz_le_half hplt
    exact_mod_cast this
  -- The key rpow comparison (reused across the branches).
  have hLzsq : (Real.log H) ^ 2 / 400 ≤ (Real.log z) ^ 2 := by
    have hE : (1 / 20 : ℝ) * Real.log H ≤ Real.log z := by
      rw [hzdef]; exact logZ_ge_twenty hHN0
    have h0 : (0 : ℝ) ≤ (1 / 20 : ℝ) * Real.log H := mul_nonneg (by norm_num) hLnn
    have := pow_le_pow_left₀ h0 hE 2
    calc (Real.log H) ^ 2 / 400 = ((1 / 20 : ℝ) * Real.log H) ^ 2 := by ring
      _ ≤ (Real.log z) ^ 2 := this
  -- The `n`-case analysis.
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [repCount_zero_target, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hCLnn hfrac_nonneg) (sTrunc2_nonneg 0)
  · by_cases hpar : Odd n
    · have hodd_win : ∀ p ∈ primeWindow eps H, Odd p := fun p hp =>
        primeWindow_odd_of_four_le hAcond hp
      rw [repCount_eq_zero_of_window_odd hodd_win hpar, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg hCLnn hfrac_nonneg) (sTrunc2_nonneg n)
    · have hne2 : 2 ∣ n := (Nat.not_odd_iff_even.mp hpar).two_dvd
      by_cases hrange : n ≤ 2 * ⌊eps ^ 2 * (H : ℚ)⌋₊
      · -- in range: the Selberg sieve core
        have hsb := hsieve eps H n hne2 hn0 z hzB hz2 hzwin
        have hn2 : (n : ℝ) ≤ 2 * (eps : ℝ) ^ 2 * (H : ℝ) := by
          have hfloor : ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
            have h0 : (0 : ℚ) ≤ eps ^ 2 * (H : ℚ) := by positivity
            calc ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ)
                = ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℚ) : ℝ) := by norm_cast
              _ ≤ ((eps ^ 2 * (H : ℚ) : ℚ) : ℝ) := by exact_mod_cast Nat.floor_le h0
              _ = (eps : ℝ) ^ 2 * (H : ℝ) := by push_cast; ring
          have hcast : (n : ℝ) ≤ 2 * ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hrange
          linarith
        have hnum : (n : ℝ) * sTrunc2 n ≤ 2 * (eps : ℝ) ^ 2 * (H : ℝ) * sTrunc2 n :=
          mul_le_mul_of_nonneg_right hn2 (sTrunc2_nonneg n)
        have hden : c₀ * ((Real.log H) ^ 2 / 400) ≤ c₀ * (Real.log z) ^ 2 :=
          mul_le_mul_of_nonneg_left hLzsq hc₀.le
        have hdpos : (0 : ℝ) < c₀ * ((Real.log H) ^ 2 / 400) :=
          mul_pos hc₀ (div_pos (pow_pos hlogH 2) (by norm_num))
        have hinv : 1 / (c₀ * (Real.log z) ^ 2) ≤ 1 / (c₀ * ((Real.log H) ^ 2 / 400)) :=
          one_div_le_one_div_of_le hdpos hden
        have hnn_nsT : (0 : ℝ) ≤ (n : ℝ) * sTrunc2 n :=
          mul_nonneg (Nat.cast_nonneg n) (sTrunc2_nonneg n)
        have hc₀ne : c₀ ≠ 0 := hc₀.ne'
        have hLsq_ne : (Real.log H) ^ 2 ≠ 0 := (pow_pos hlogH 2).ne'
        have hT1 : (n : ℝ) * sTrunc2 n / (c₀ * (Real.log z) ^ 2)
            ≤ 800 / c₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) * sTrunc2 n := by
          calc (n : ℝ) * sTrunc2 n / (c₀ * (Real.log z) ^ 2)
              = ((n : ℝ) * sTrunc2 n) * (1 / (c₀ * (Real.log z) ^ 2)) := by ring
            _ ≤ ((n : ℝ) * sTrunc2 n) * (1 / (c₀ * ((Real.log H) ^ 2 / 400))) :=
                mul_le_mul_of_nonneg_left hinv hnn_nsT
            _ ≤ (2 * (eps : ℝ) ^ 2 * (H : ℝ) * sTrunc2 n)
                  * (1 / (c₀ * ((Real.log H) ^ 2 / 400))) :=
                mul_le_mul_of_nonneg_right hnum (by positivity)
            _ = 800 / c₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) * sTrunc2 n := by
                field_simp; ring
        have hzp1 : (z : ℝ) + 1 ≤ 2 * (H : ℝ) ^ (1 / 10 : ℝ) := by
          have h1 : (1 : ℝ) ≤ (H : ℝ) ^ (1 / 10 : ℝ) := Real.one_le_rpow hH1R (by norm_num)
          linarith [hzR_le, h1]
        have hcast_z : ((z ^ 2 + 1 : ℕ) : ℝ) ≤ ((z : ℝ) + 1) ^ 2 := by
          push_cast; nlinarith [(Nat.cast_nonneg z : (0 : ℝ) ≤ (z : ℝ))]
        have hT2a : ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4 ≤ 256 * (H : ℝ) ^ (4 / 5 : ℝ) := by
          calc ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4
              ≤ (((z : ℝ) + 1) ^ 2) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcast_z 4
            _ = ((z : ℝ) + 1) ^ 8 := by ring
            _ ≤ (2 * (H : ℝ) ^ (1 / 10 : ℝ)) ^ 8 := pow_le_pow_left₀ (by positivity) hzp1 8
            _ = 256 * ((H : ℝ) ^ (1 / 10 : ℝ)) ^ 8 := by rw [mul_pow]; norm_num
            _ = 256 * (H : ℝ) ^ (4 / 5 : ℝ) := by
                rw [show ((H : ℝ) ^ (1 / 10 : ℝ)) ^ 8 = (H : ℝ) ^ (4 / 5 : ℝ) by
                  rw [← Real.rpow_natCast ((H : ℝ) ^ (1 / 10 : ℝ)) 8,
                    ← Real.rpow_mul (Nat.cast_nonneg H)]; norm_num]
        have hlog_le : Real.log H ≤ 20 * (H : ℝ) ^ (1 / 20 : ℝ) := by
          have h1 : Real.log ((H : ℝ) ^ (1 / 20 : ℝ)) ≤ (H : ℝ) ^ (1 / 20 : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
          rw [Real.log_rpow hHposR] at h1
          linarith [h1]
        have hlogsq : (Real.log H) ^ 2 ≤ 400 * (H : ℝ) ^ (1 / 10 : ℝ) := by
          have hmul := mul_le_mul hlog_le hlog_le hLnn (by positivity)
          calc (Real.log H) ^ 2 = Real.log H * Real.log H := by ring
            _ ≤ (20 * (H : ℝ) ^ (1 / 20 : ℝ)) * (20 * (H : ℝ) ^ (1 / 20 : ℝ)) := hmul
            _ = 400 * ((H : ℝ) ^ (1 / 20 : ℝ)) ^ 2 := by ring
            _ = 400 * (H : ℝ) ^ (1 / 10 : ℝ) := by
                rw [show ((H : ℝ) ^ (1 / 20 : ℝ)) ^ 2 = (H : ℝ) ^ (1 / 10 : ℝ) by
                  rw [← Real.rpow_natCast ((H : ℝ) ^ (1 / 20 : ℝ)) 2,
                    ← Real.rpow_mul (Nat.cast_nonneg H)]; norm_num]
        have hlogsq2 : (Real.log H) ^ 2 ≤ 400 * (H : ℝ) ^ (1 / 5 : ℝ) := by
          refine le_trans hlogsq ?_
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 400)
          exact Real.rpow_le_rpow_of_exponent_le hH1R (by norm_num)
        have hT2b : 256 * (H : ℝ) ^ (4 / 5 : ℝ) ≤ 102400 * (H : ℝ) / (Real.log H) ^ 2 := by
          rw [le_div_iff₀ (pow_pos hlogH 2)]
          calc 256 * (H : ℝ) ^ (4 / 5 : ℝ) * (Real.log H) ^ 2
              ≤ 256 * (H : ℝ) ^ (4 / 5 : ℝ) * (400 * (H : ℝ) ^ (1 / 5 : ℝ)) :=
                mul_le_mul_of_nonneg_left hlogsq2 (by positivity)
            _ = 102400 * ((H : ℝ) ^ (4 / 5 : ℝ) * (H : ℝ) ^ (1 / 5 : ℝ)) := by ring
            _ = 102400 * (H : ℝ) := by
                rw [← Real.rpow_add hHposR, show (4 / 5 : ℝ) + 1 / 5 = 1 by norm_num,
                  Real.rpow_one]
        have hT2c : 102400 * (H : ℝ) / (Real.log H) ^ 2
            = 102400 / (eps : ℝ) ^ 2 * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) := by
          field_simp
        have hT2 : ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4
            ≤ 102400 / (eps : ℝ) ^ 2 * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2)
                * sTrunc2 n := by
          calc ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4
              ≤ 256 * (H : ℝ) ^ (4 / 5 : ℝ) := hT2a
            _ ≤ 102400 * (H : ℝ) / (Real.log H) ^ 2 := hT2b
            _ = 102400 / (eps : ℝ) ^ 2 * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) := hT2c
            _ ≤ 102400 / (eps : ℝ) ^ 2 * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2)
                  * sTrunc2 n :=
                le_mul_of_one_le_right (by positivity) (one_le_sTrunc2 hn0)
        calc (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
            ≤ (n : ℝ) * sTrunc2 n / (c₀ * (Real.log z) ^ 2) + ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4 := hsb
          _ ≤ 800 / c₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) * sTrunc2 n
              + 102400 / (eps : ℝ) ^ 2 * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2)
                  * sTrunc2 n := add_le_add hT1 hT2
          _ = (800 / c₀ + 102400 / (eps : ℝ) ^ 2)
              * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) * sTrunc2 n := by ring
      · rw [repCount_eq_zero_of_large (by omega), Nat.cast_zero]
        exact mul_nonneg (mul_nonneg hCLnn hfrac_nonneg) (sTrunc2_nonneg n)

/-! ## §6 — the ungated `hpt` with the sharpened small-`H` constant

The landed `hpt_holds` absorbs `2 ≤ H < H₁` with
`CS = (ε²H₁+1)²·(log H₁)²/(2ε²)`: it bounds the window card at `H₁` and the frozen
fraction `ε²H/log²H ≥ 2ε²/log²H₁` at `H = 2` — two DIFFERENT `H`'s.  Running both
at the same `H` needs only

  `CS' = (ε²H₁ + 2 + 1/(2ε²))·(log H₁)²`,

because `(ε²H+1)²/(ε²H) = ε²H + 2 + 1/(ε²H) ≤ ε²H₁ + 2 + 1/(2ε²)` for
`2 ≤ H ≤ H₁`.  That is a factor `≈H₁/2` — on its own worth `2·log₂(H₁/2)` bits of
`log₂ K`. -/

/-- **The threshold-parametric twin of `hpt_holds`**, with both levers: the
honest threshold `T` (§5) and the sharpened small-`H` constant
`CS' = (ε²T + 2 + 1/(2ε²))·(log T)²`.  The constant is EXPLICIT — no `∃`. -/
theorem hpt_holds_thr (eps : ℚ) (heps : 0 < eps) (heps2 : (eps : ℝ) ^ 2 < 1 / 2)
    (c₀ : ℝ) (hc₀ : 0 < c₀) (z₀ : ℕ)
    (hsieve : ∀ (eps' : ℚ) (H n : ℕ), 2 ∣ n → n ≠ 0 →
      ∀ (z : ℕ), z₀ ≤ z → 2 ≤ z → (∀ p ∈ primeWindow eps' H, z < p) →
        (repCount (primeWindow eps' H) (primeWindow eps' H) n : ℝ)
          ≤ (n : ℝ) * sTrunc2 n / (c₀ * (Real.log z) ^ 2) + ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4)
    (T : ℕ) (hT0 : N0' ≤ T) (hTA : (4 : ℚ) ≤ eps ^ 2 * (T : ℚ))
    (hTB : ((z₀ : ℝ)) ^ (10 : ℕ) ≤ (T : ℝ))
    (hTD : (2 / (eps : ℝ) ^ 2) ^ (10 : ℕ) ≤ ((T : ℝ)) ^ (9 : ℕ)) :
    ∀ H n : ℕ,
      (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
        ≤ ((800 / c₀ + 102400 / (eps : ℝ) ^ 2)
              + ((eps : ℝ) ^ 2 * (T : ℝ) + 2 + 1 / (2 * (eps : ℝ) ^ 2)) * (Real.log T) ^ 2)
            * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hepsq : (0 : ℝ) < (eps : ℝ) ^ 2 := by positivity
  have hepsne : ((eps : ℝ) ^ 2) ≠ 0 := ne_of_gt hepsq
  have heps2Q : eps ^ 2 < 1 / 2 := by
    have h : ((eps ^ 2 : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by push_cast; linarith [heps2]
    exact_mod_cast h
  have hT2N : 2 ≤ T := by unfold N0' at hT0; omega
  have hlogT : (0 : ℝ) < Real.log T := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  set CL := 800 / c₀ + 102400 / (eps : ℝ) ^ 2 with hCLdef
  set CS := ((eps : ℝ) ^ 2 * (T : ℝ) + 2 + 1 / (2 * (eps : ℝ) ^ 2)) * (Real.log T) ^ 2 with hCSdef
  have hCLnn : (0 : ℝ) ≤ CL := by rw [hCLdef]; positivity
  have hCSnn : (0 : ℝ) ≤ CS := by rw [hCSdef]; positivity
  intro H n
  have hfrac_nonneg : (0 : ℝ) ≤ (eps : ℝ) ^ 2 * H / (Real.log H) ^ 2 :=
    div_nonneg (by positivity) (sq_nonneg _)
  have hF_nonneg : (0 : ℝ) ≤ ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n :=
    mul_nonneg hfrac_nonneg (sTrunc2_nonneg n)
  by_cases hHge : T ≤ H
  · -- large-`H` branch: scale `CL` up to `CL + CS`
    refine le_trans (hpt_large_thr eps heps c₀ hc₀ z₀ hsieve T hT0 hTA hTB hTD H hHge n) ?_
    calc CL * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n
        = CL * (((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) := by ring
      _ ≤ (CL + CS) * (((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) :=
          mul_le_mul_of_nonneg_right (by linarith) hF_nonneg
      _ = (CL + CS) * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by ring
  · -- small-`H` branch: `H < T`
    have hsmall : (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
        ≤ CS * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by
      rcases eq_or_ne n 0 with rfl | hn0
      · rw [repCount_zero_target, Nat.cast_zero]
        exact mul_nonneg (mul_nonneg hCSnn hfrac_nonneg) (sTrunc2_nonneg 0)
      · rcases Nat.lt_or_ge H 2 with hH1 | hH2
        · -- `H ∈ {0,1}`: the window is empty
          have hHle1 : (H : ℚ) ≤ 1 := by exact_mod_cast (by omega : H ≤ 1)
          have hlt2 : eps ^ 2 * (H : ℚ) < 2 := by
            have hle := mul_le_of_le_one_right (sq_nonneg eps) hHle1
            linarith [hle, heps2Q]
          have hempty : primeWindow eps H = ∅ := primeWindow_eq_empty_of_lt_two hlt2
          rw [repCount_eq_zero_of_empty hempty, Nat.cast_zero]
          exact mul_nonneg (mul_nonneg hCSnn hfrac_nonneg) (sTrunc2_nonneg n)
        · -- `2 ≤ H < T`: crude `card²`, both sides read at the SAME `H`
          have hlogH : (0 : ℝ) < Real.log H := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
          have hH2R : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH2
          have hHTR : (H : ℝ) ≤ (T : ℝ) := by exact_mod_cast (by omega : H ≤ T)
          have hcard_le : ((primeWindow eps H).card : ℝ) ≤ (eps : ℝ) ^ 2 * H + 1 := by
            have h1 : (primeWindow eps H).card ≤ ⌊eps ^ 2 * (H : ℚ)⌋₊ + 1 :=
              primeWindow_card_le eps H
            have hfloor : ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
              have h0 : (0 : ℚ) ≤ eps ^ 2 * (H : ℚ) := by positivity
              calc ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ)
                  = ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℚ) : ℝ) := by norm_cast
                _ ≤ ((eps ^ 2 * (H : ℚ) : ℚ) : ℝ) := by exact_mod_cast Nat.floor_le h0
                _ = (eps : ℝ) ^ 2 * (H : ℝ) := by push_cast; ring
            have h3 : ((primeWindow eps H).card : ℝ) ≤ ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) + 1 := by
              exact_mod_cast h1
            linarith
          have hrep_le : (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
              ≤ ((eps : ℝ) ^ 2 * H + 1) ^ 2 := by
            have hcs : (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
                ≤ ((primeWindow eps H).card : ℝ) ^ 2 := by
              have hle := repCount_le_card_mul (primeWindow eps H) (primeWindow eps H) n
              calc (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
                  ≤ (((primeWindow eps H).card * (primeWindow eps H).card : ℕ) : ℝ) := by
                    exact_mod_cast hle
                _ = ((primeWindow eps H).card : ℝ) ^ 2 := by push_cast; ring
            exact le_trans hcs (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard_le 2)
          -- the sharpened comparison: one `H` on both sides
          have hkey : ((eps : ℝ) ^ 2 * (H : ℝ) + 1) ^ 2
              ≤ ((eps : ℝ) ^ 2 * (T : ℝ) + 2 + 1 / (2 * (eps : ℝ) ^ 2))
                  * ((eps : ℝ) ^ 2 * (H : ℝ)) := by
            have hexp : ((eps : ℝ) ^ 2 * (T : ℝ) + 2 + 1 / (2 * (eps : ℝ) ^ 2))
                * ((eps : ℝ) ^ 2 * (H : ℝ))
                = (eps : ℝ) ^ 2 * (T : ℝ) * ((eps : ℝ) ^ 2 * (H : ℝ))
                    + 2 * ((eps : ℝ) ^ 2 * (H : ℝ)) + (H : ℝ) / 2 := by
              field_simp
            have h1 : (eps : ℝ) ^ 2 * (H : ℝ) * ((eps : ℝ) ^ 2 * (H : ℝ))
                ≤ (eps : ℝ) ^ 2 * (T : ℝ) * ((eps : ℝ) ^ 2 * (H : ℝ)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hHTR (sq_nonneg _)) (by positivity)
            rw [hexp]; nlinarith [h1, hH2R]
          have hlogmono : (Real.log H) ^ 2 ≤ (Real.log T) ^ 2 := by
            apply pow_le_pow_left₀ hlogH.le
            exact Real.log_le_log (by exact_mod_cast (show 0 < H by omega)) hHTR
          have hdiv : (eps : ℝ) ^ 2 * (H : ℝ) / (Real.log T) ^ 2
              ≤ (eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (pow_pos hlogH 2) hlogmono
          have heq : CS * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log T) ^ 2)
              = ((eps : ℝ) ^ 2 * (T : ℝ) + 2 + 1 / (2 * (eps : ℝ) ^ 2))
                  * ((eps : ℝ) ^ 2 * (H : ℝ)) := by
            rw [hCSdef]; field_simp
          calc (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
              ≤ ((eps : ℝ) ^ 2 * H + 1) ^ 2 := hrep_le
            _ ≤ CS * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log T) ^ 2) := by
                rw [heq]; exact hkey
            _ ≤ CS * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) :=
                mul_le_mul_of_nonneg_left hdiv hCSnn
            _ ≤ CS * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n :=
                le_mul_of_one_le_right (mul_nonneg hCSnn hfrac_nonneg) (one_le_sTrunc2 hn0)
    refine le_trans hsmall ?_
    calc CS * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n
        = CS * (((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) := by ring
      _ ≤ (CL + CS) * (((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) :=
          mul_le_mul_of_nonneg_right (by linarith) hF_nonneg
      _ = (CL + CS) * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by ring

/-! ## §7 — the second moment and `|Ξ_H|` with the constant EXPOSED

`hsq_holds_gen'`, `W3_AE_d_of_sieve` and `bigXi_bounded_of_sieve` each hide their
constant behind an `∃`, so the composite `K = 16·C_d/ε¹⁶ = 32·K_lcm·C₁²/ε¹⁰` is
invisible to the S11 accounting.  These twins carry it in the statement. -/

/-- The explicit-constant twin of `hsq_holds3`: for `H ≥ 2` the squared frozen
`rbound` sums to `≤ (2·K·C₁²·ε⁶)·H³/log⁴H`, with `K` the `hFac2` lcm majorant
supplied as a hypothesis (rather than unpacked from `hFac2_lcm_sum_le`'s `∃`). -/
theorem hsq_explicit (eps : ℚ) (heps : 0 < eps) (C₁ : ℝ) (K : ℝ) (hKpos : 0 < K)
    (hK : ∀ X : ℕ, ∑ d₁ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
            ∑ d₂ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
              hFac2 d₁ * hFac2 d₂ / (Nat.lcm d₁ d₂ : ℝ) ≤ K) :
    ∀ H : ℕ, 2 ≤ H →
      ∑ n ∈ primeWindow eps H + primeWindow eps H,
        (C₁ * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) ^ 2
        ≤ (2 * K * C₁ ^ 2 * (eps : ℝ) ^ 6) * (H : ℝ) ^ 3 / (Real.log H) ^ 4 := by
  intro H _
  simp only [sTrunc2_eq_sTruncW]
  set A := C₁ * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) with hAdef
  have hfloor : ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    have h0 : (0 : ℚ) ≤ eps ^ 2 * (H : ℚ) := by positivity
    calc ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) = ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℚ) : ℝ) := by norm_cast
      _ ≤ ((eps ^ 2 * (H : ℚ) : ℚ) : ℝ) := by exact_mod_cast Nat.floor_le h0
      _ = (eps : ℝ) ^ 2 * (H : ℝ) := by push_cast; ring
  have hMle : ((2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) ≤ 2 * (eps : ℝ) ^ 2 * (H : ℝ) := by
    have h2 : ((2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ)
        = 2 * ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) := by push_cast; ring
    rw [h2, mul_assoc]
    exact mul_le_mul_of_nonneg_left hfloor (by norm_num)
  calc ∑ n ∈ primeWindow eps H + primeWindow eps H, (A * sTruncW hFac2 n) ^ 2
      = A ^ 2 * ∑ n ∈ primeWindow eps H + primeWindow eps H, sTruncW hFac2 n ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => mul_pow _ _ _
    _ ≤ A ^ 2 * (((2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) * K) :=
        mul_le_mul_of_nonneg_left
          (sum_sTruncW_sq_le eps H hFac2 (fun _ _ hodd => hFac2_nonneg hodd) K (hK _))
          (sq_nonneg A)
    _ ≤ (2 * K * C₁ ^ 2 * (eps : ℝ) ^ 6) * (H : ℝ) ^ 3 / (Real.log H) ^ 4 := by
        have hAK : (0 : ℝ) ≤ A ^ 2 * K := mul_nonneg (sq_nonneg A) hKpos.le
        calc A ^ 2 * (((2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) * K)
            = (A ^ 2 * K) * ((2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) := by ring
          _ ≤ (A ^ 2 * K) * (2 * (eps : ℝ) ^ 2 * (H : ℝ)) :=
              mul_le_mul_of_nonneg_left hMle hAK
          _ = (2 * K * C₁ ^ 2 * (eps : ℝ) ^ 6) * (H : ℝ) ^ 3 / (Real.log H) ^ 4 := by
              rw [hAdef]; field_simp

/-- **`|Ξ_H|` with the constant in the statement.**  The explicit-constant twin of
`bigXi_bounded_of_sieve ∘ W3_AE_d_of_sieve ∘ hsq_holds3`:
`|Ξ_H| ≤ 16·C_d/ε¹⁶` with `C_d = 2·K·C₁²·ε⁶`, i.e.

  `|Ξ_H| ≤ 32·K_lcm·C₁²/ε¹⁰`.

This is the load-bearing `K` of the S11 budget (`δ₀ = cD3·ε/(32·C·K)`): every bit
saved on `C₁` is worth TWO bits here. -/
theorem bigXi_bounded_explicit (eps : ℚ) (heps : 0 < eps) (heps2 : (eps : ℝ) ^ 2 < 1 / 2)
    (C₁ K : ℝ) (hKpos : 0 < K)
    (hK : ∀ X : ℕ, ∑ d₁ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
            ∑ d₂ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
              hFac2 d₁ * hFac2 d₂ / (Nat.lcm d₁ d₂ : ℝ) ≤ K)
    (hpt : ∀ H n : ℕ, (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
      ≤ C₁ * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) :
    ∀ (H : ℕ) [NeZero H], 2 ≤ H →
      ((bigXi eps H).card : ℝ) ≤ 32 * K * C₁ ^ 2 / (eps : ℝ) ^ 10 := by
  have heQ : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have heps2Q : eps ^ 2 < 1 / 2 := by
    have h : ((eps ^ 2 : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by push_cast; linarith [heps2]
    exact_mod_cast h
  intro H hNe hH2
  haveI := hNe
  have hHpos : 0 < H := by omega
  have hHQ : (0 : ℚ) < (H : ℚ) := by exact_mod_cast hHpos
  have hHR1 : (1 : ℝ) < (H : ℝ) := by exact_mod_cast (show 1 < H by omega)
  -- The additive energy, via the pointwise bound and the second moment.
  have hE : (Finset.addEnergy (primeWindow eps H) (primeWindow eps H) : ℝ)
      ≤ (2 * K * C₁ ^ 2 * (eps : ℝ) ^ 6) * (H : ℝ) ^ 3 / (Real.log H) ^ 4 :=
    le_trans (addEnergy_le_of_r_bound (primeWindow eps H) (primeWindow eps H)
      (fun n => C₁ * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) (hpt H))
      (hsq_explicit eps heps C₁ K hKpos hK H hH2)
  -- Discharge the Fourier-embedding obligations from `ε² < 1/2`.
  have hxnn : (0 : ℚ) ≤ eps ^ 2 * (H : ℚ) := by positivity
  have hfloor : (⌊eps ^ 2 * (H : ℚ)⌋₊ : ℚ) ≤ eps ^ 2 * (H : ℚ) := Nat.floor_le hxnn
  have hwin : ∀ p ∈ primeWindow eps H, p < H := by
    intro p hp
    rw [mem_primeWindow] at hp
    have hpq : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) := le_trans (by exact_mod_cast hp.1) hfloor
    have : (p : ℚ) < (H : ℚ) := by nlinarith [hpq, heps2Q, hHQ]
    exact_mod_cast this
  have hwrap : ∀ p ∈ primeWindow eps H, ∀ q ∈ primeWindow eps H, p + q < H := by
    intro p hp q hq
    rw [mem_primeWindow] at hp hq
    have hpp : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) := le_trans (by exact_mod_cast hp.1) hfloor
    have hqq : (q : ℚ) ≤ eps ^ 2 * (H : ℚ) := le_trans (by exact_mod_cast hq.1) hfloor
    have : ((p + q : ℕ) : ℚ) < (H : ℚ) := by push_cast; nlinarith [hpp, hqq, heps2Q, hHQ]
    exact_mod_cast this
  -- The pure algebra of the cancellation, in abstract variables.
  have algebra : ∀ X e L Hr E Cd : ℝ, 0 < e → 0 < L → 0 < Hr → 0 ≤ X →
      X * (e ^ 2 / L) ^ 4 ≤ Hr * (2 / (e ^ 2 * Hr)) ^ 4 * E →
      E ≤ Cd * Hr ^ 3 / L ^ 4 →
      X ≤ 16 * Cd / e ^ 16 := by
    intro X e L Hr E Cd he hL hHr hX h1 h2
    have hne : e ≠ 0 := ne_of_gt he
    have hLne : L ≠ 0 := ne_of_gt hL
    have hHrne : Hr ≠ 0 := ne_of_gt hHr
    have hcoef : (0 : ℝ) ≤ Hr * (2 / (e ^ 2 * Hr)) ^ 4 := by positivity
    have h3 : X * (e ^ 2 / L) ^ 4 ≤ Hr * (2 / (e ^ 2 * Hr)) ^ 4 * (Cd * Hr ^ 3 / L ^ 4) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 hcoef)
    have hmul : (0 : ℝ) < L ^ 4 * e ^ 8 := by positivity
    have h4 := mul_le_mul_of_nonneg_right h3 (le_of_lt hmul)
    have hL4 : X * (e ^ 2 / L) ^ 4 * (L ^ 4 * e ^ 8) = X * e ^ 16 := by field_simp
    have hR4 : Hr * (2 / (e ^ 2 * Hr)) ^ 4 * (Cd * Hr ^ 3 / L ^ 4) * (L ^ 4 * e ^ 8)
        = 16 * Cd := by field_simp; ring
    rw [hL4, hR4] at h4
    rw [le_div_iff₀ (show (0 : ℝ) < e ^ 16 by positivity)]
    exact h4
  have hmain := algebra ((bigXi eps H).card : ℝ) (eps : ℝ) (Real.log (H : ℝ)) (H : ℝ)
    (Finset.addEnergy (primeWindow eps H) (primeWindow eps H) : ℝ)
    (2 * K * C₁ ^ 2 * (eps : ℝ) ^ 6)
    heQ (Real.log_pos hHR1) (by exact_mod_cast hHpos) (Nat.cast_nonneg _)
    (large_spectrum_energy eps H heps hwin hwrap) hE
  refine le_trans hmain (le_of_eq ?_)
  field_simp
  ring

/-! ## §8 — the payoff at `ε = 1/500`

`T = 2^41` clears all four honest thresholds at `ε = 1/500`:
`2^20 ≤ T`; `ε²T = 8.8·10^6 ≥ 4`; `16^10 = 1.0995·10^12 ≤ T = 2.199·10^12`;
`(2/ε²)^10 = 5·10^5 ^ 10 ≈ 9.77·10^56 ≤ T^9 = 2^369`. -/

/-- `log (2^41) ≤ 28.42`. -/
lemma log_pow41_le : Real.log ((2 ^ 41 : ℕ) : ℝ) ≤ 28.42 := by
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hcast : ((2 ^ 41 : ℕ) : ℝ) = (2 : ℝ) ^ (41 : ℕ) := by push_cast; ring
  have hval : Real.log ((2 ^ 41 : ℕ) : ℝ) = 41 * Real.log 2 := by
    rw [hcast, Real.log_pow]; norm_num
  rw [hval]; linarith

/-- **THE PAYOFF (the `C₁` numeral).**  At `ε = 1/500`, `T = 2^41`,
`(c₀, z₀) = (1/256, 16)`, the twin's `hpt` constant is

  `C₁' = (800/c₀ + 102400/ε²) + (ε²T + 2 + 1/(2ε²))·(log T)²`
       `= 2.56002·10^10 + 7.205·10^9 = 3.281·10^10 ≤ 2^35`,

against the landed `C₁ ≈ 1.544·10^58 = 2^193.30` (whose `CS` is
`(ε²·2^100+1)²(100 log 2)²/(2ε²)`).  `Δ log₂ C₁ = 158.30`. -/
theorem hpt_const_le_pow35 :
    (800 / (1 / 256 : ℝ) + 102400 / (((1 : ℚ) / 500 : ℚ) : ℝ) ^ 2)
        + ((((1 : ℚ) / 500 : ℚ) : ℝ) ^ 2 * ((2 ^ 41 : ℕ) : ℝ) + 2
            + 1 / (2 * ((((1 : ℚ) / 500 : ℚ) : ℝ)) ^ 2)) * (Real.log ((2 ^ 41 : ℕ) : ℝ)) ^ 2
      ≤ 2 ^ 35 := by
  have hlog := log_pow41_le
  have hlognn : (0 : ℝ) ≤ Real.log ((2 ^ 41 : ℕ) : ℝ) :=
    Real.log_nonneg (by push_cast; norm_num)
  have hsq : (Real.log ((2 ^ 41 : ℕ) : ℝ)) ^ 2 ≤ 807.6964 := by
    have h := pow_le_pow_left₀ hlognn hlog 2
    calc (Real.log ((2 ^ 41 : ℕ) : ℝ)) ^ 2 ≤ (28.42 : ℝ) ^ 2 := h
      _ = 807.6964 := by norm_num
  have hcast : ((((1 : ℚ) / 500 : ℚ) : ℝ)) = 1 / 500 := by norm_num
  rw [hcast]
  push_cast
  nlinarith [hsq, hlognn]

/-- **THE `hpt` TWIN AT `ε = 1/500`, with a numeral constant.**  The landed
`hpt_holds` yields `C₁ ≈ 1.54·10^58`; this one yields `2^35 = 3.44·10^10`, and the
statement is otherwise token-identical. -/
theorem hpt_holds_500 : ∀ H n : ℕ,
    (repCount (primeWindow (1 / 500) H) (primeWindow (1 / 500) H) n : ℝ)
      ≤ (2 : ℝ) ^ 35 * ((((1 : ℚ) / 500 : ℚ) : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by
  intro H n
  have h := hpt_holds_thr (1 / 500) (by norm_num) (by push_cast; norm_num) (1 / 256)
    (by norm_num) 16 repCount_even_le_primorial_sixteen (2 ^ 41)
    (by unfold N0'; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)
    (by push_cast; norm_num) H n
  refine le_trans h ?_
  have hF : (0 : ℝ) ≤ ((((1 : ℚ) / 500 : ℚ) : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n :=
    mul_nonneg (div_nonneg (by positivity) (sq_nonneg _)) (sTrunc2_nonneg n)
  calc (800 / (1 / 256 : ℝ) + 102400 / (((1 : ℚ) / 500 : ℚ) : ℝ) ^ 2
          + ((((1 : ℚ) / 500 : ℚ) : ℝ) ^ 2 * ((2 ^ 41 : ℕ) : ℝ) + 2
              + 1 / (2 * ((((1 : ℚ) / 500 : ℚ) : ℝ)) ^ 2))
            * (Real.log ((2 ^ 41 : ℕ) : ℝ)) ^ 2)
        * ((((1 : ℚ) / 500 : ℚ) : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n
      = (800 / (1 / 256 : ℝ) + 102400 / (((1 : ℚ) / 500 : ℚ) : ℝ) ^ 2
          + ((((1 : ℚ) / 500 : ℚ) : ℝ) ^ 2 * ((2 ^ 41 : ℕ) : ℝ) + 2
              + 1 / (2 * ((((1 : ℚ) / 500 : ℚ) : ℝ)) ^ 2))
            * (Real.log ((2 ^ 41 : ℕ) : ℝ)) ^ 2)
        * (((((1 : ℚ) / 500 : ℚ) : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) := by ring
    _ ≤ (2 : ℝ) ^ 35
        * (((((1 : ℚ) / 500 : ℚ) : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) :=
        mul_le_mul_of_nonneg_right hpt_const_le_pow35 hF
    _ = (2 : ℝ) ^ 35 * ((((1 : ℚ) / 500 : ℚ) : ℝ) ^ 2 * H / (Real.log H) ^ 2)
        * sTrunc2 n := by ring

/-- **THE PAYOFF (the `K` numeral).**  The unconditional large-spectrum bound at
`ε = 1/500` with the constant fully exposed:

  `|Ξ_H| ≤ 32·K_lcm·(2^35)²/ε¹⁰ = 32·K_lcm·2^70·500^10`,

`K_lcm = exp(24·ζ(2))` being the (effective) `hFac2` lcm majorant, carried as the
second conjunct.  `log₂` of the constant is `5 + 56.96 + 70 + 89.66 = 221.61`,
against the landed chain's `5 + 56.96 + 386.60 + 89.66 = 538.21`:
**a 316.6-bit reduction in `log₂ K`,** hence the same in `log₂(1/δ₀)` — the whole
`N0` share of CG-SCOPE's 602-bit ledger, landing on the `102400/ε²` floor. -/
theorem bigXi_bounded_500 :
    ∃ K : ℝ, 0 < K ∧
      (∀ X : ℕ, ∑ d₁ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
          ∑ d₂ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
            hFac2 d₁ * hFac2 d₂ / (Nat.lcm d₁ d₂ : ℝ) ≤ K) ∧
      ∀ (H : ℕ) [NeZero H], 2 ≤ H →
        ((bigXi (1 / 500) H).card : ℝ)
          ≤ 32 * K * ((2 : ℝ) ^ 35) ^ 2 / (((1 : ℚ) / 500 : ℚ) : ℝ) ^ 10 := by
  obtain ⟨K, hKpos, hK⟩ := hFac2_lcm_sum_le
  refine ⟨K, hKpos, hK, ?_⟩
  intro H _ hH2
  exact bigXi_bounded_explicit (1 / 500) (by norm_num) (by push_cast; norm_num)
    ((2 : ℝ) ^ 35) K hKpos hK hpt_holds_500 H hH2

end Salt.Entropy.Chowla
