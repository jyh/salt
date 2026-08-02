/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PortAssembly

/-!
# RIDER-TRACE — the `cs` and `T₀` riders of `logChowla2_ineffective_v3`, traced to their leaves

`S16Compose.logChowla2_ineffective_v3` carries three inner numeric riders on constants its own
`∃`-prefix mints: `e^{-100} ≤ cs`, `T₀ ≤ e^{e^{100}}`, `e^{-100} ≤ Ks`.  This file traces the
first two to the leaves that actually produce them and pins, in the kernel, what those leaves say.

## The shared mint

Both `cs` and `T₀` are minted at ONE site — `PortAssembly.halaszPrimesChiGated_of_price` (:802) —
and travel to `v3` untouched through a chain of pass-throughs:

```
halaszPrimesChiGated_of_price          cs := min (min (c_vk/(2·K₄)) (c₀/(2·Cκ))) (1/10)
                                       T₀ := max T₀e T₀z
  → halasz_primes_chi_pair_of_gates(_bounded)      T₀ := max T₀ T₀e
  → halaszPrimesChi_holds_gated(_bounded)          pass-through
  → halaszPrimesChi_pointwise_of_gates(_bounded)   pass-through
  → usetGChi_window_meansq_gated_family_perBlock(_bounded)   pass-through
  → m4_rowChi_capstone_perBlock(_bounded)          pass-through
  → m4_hcap_at_door_perBlock_L_gk(_bounded)        pass-through
  → m4_fuse_hcap_of_capWS_L_gk(_ceiling)           pass-through
  → s15_crossing_supplied_L_gk(_ceiling)           pass-through
  → logChowla2_witnessed_scale_flat_L_v2_uniform_win_ceiling → `_v3`
```

## `cs` — EFFECTIVE AT EVERY LEAF (three of four leaves are literals in the source)

* `c_vk = 1/10^8` — a LITERAL, visible at the call site: `halaszPrimesChiGated_of_price` is
  invoked on `TwistedWindowPriceGated (1/10^8)` (`TwistedEdge.twisted_window_price_gated_holds`,
  whose own `twisted_edge_price_strip` exports `c_vk = 1/10^8` as an equation).
* `K₄ = 2^{3/4}·16` and `Cκ = 2^{3/4}·8` — CLOSED-FORM `noncomputable def`s
  (`PortAssembly.lean:637`, `HalaszPrimesCore.lean:3456`).  ⟦ERRATUM to the 0802 summit dossier
  §3, which called `K₄`/`Cκ` "compactness existentials of our own port"⟧ — they are not
  existentials at all.
* `c₀` — `per_pair_contour`'s `c_vk`, a pass-through of `shifted_edge_price_strip`'s, itself a
  pass-through of `rect_zero_free_margin`'s, itself `Salt.Vk.zeta_zero_free_region_pow`'s `c`,
  which the source pins at the LITERAL `1/10^9` (`Vk/PowRegion.lean:365`).  It is hidden only by
  the `∃`-prefixes, which export positivity alone.

So `cs = min(min((1/10^8)/(2·2^{3/4}·16), (1/10^9)/(2·2^{3/4}·8)), 1/10) = 3.716·10^{-11}`,
against the rider's `e^{-100} = 3.72·10^{-44}` — **33 orders of room**.  §1 pins the arithmetic;
§2–§4 carry `1/10^9 ≤ c₀` up the three lowest rungs.  The remaining carry (`per_pair_contour`,
`halaszPrimesChiGated_of_price`, then the seven pass-throughs) is conjunct-carry with no new
analysis — see the closing note.

## `T₀` — UNREACHABLE ALONG THIS PROOF (the headline finding)

`T₀ = max T₀e T₀z`, and:

* `T₀e = e^{e^{100}}` EXACTLY (`twisted_edge_price_strip`'s third witness slot) — the rider is
  met, with equality, on this leaf;
* `T₀z = per_pair_contour`'s threshold `= max (max T₀s 3) (e^{e^{c_vk+1}})` with
  `T₀s = shifted_edge_price_strip`'s `= max (max T₁ 3) (e^{e^{Cbig}})`, and
  `T₁ = rect_zero_free_margin`'s `= max 3 (max M E)` with
  `M = zeta_zero_free_region_pow`'s own threshold `= e^{e^{A}} + t₀ + 3`,
  `A = 8·log(20000K) + 1100 ≥ 1100`.

Hence **`T₀ ≥ e^{e^{1100}}`** — the VK region's own threshold is a hard floor, and it exceeds the
rider's ceiling `e^{e^{100}}` by a factor `e^{e^{1100} - e^{100}}`.  (At the corpus's own `K` the
floor is `e^{e^{1251.2}}`.)  A second, worse floor sits above it: `e^{e^{Cbig}}` with
`Cbig = 9000·c_vk + c_vk/(2·δ₀) + 1`, `δ₀ = ε₀/2` and `ε₀` the OPAQUE compactness constant of
`zeta_zero_free_strip_height` at height `H = e^{e^{A}}` — so `T₀` currently has no effective
upper bound at all.

⟦THE HONEST VERDICT⟧ the rider is **not refutable as a proposition** (the `∃` could in principle
be witnessed by a different proof), but it is **unreachable along the corpus's proof**: nothing
short of an explicit zero-free region valid from moderate height can bring the socket's threshold
below `e^{e^{100}}`.  §2–§4 pin the first three rungs of that floor in the kernel
(`e^{e^{1100}} ≤ T₁`, `e^{e^{1100}} ≤ T₀s`); §5 pins the strict violation arithmetic.

⟦THE REPAIR, PRICED — AND THE CONSUMER'S TOLERANCE IS ALREADY LANDED⟧ the numeral `e^{e^{100}}`
is spent at exactly ONE place: `S13CapFloor.capfloor_T0_Tann` (:238), which converts it into the
socket's real need `T₀ ≤ Tann`.  Its SHARP sibling `capfloor_T0_Tann_sharp` (:226) is already in
the kernel and asks only `T₀ ≤ e^{√H/2}` — at the flat design base `H ≥ ⌈e^{e^{3.2A}}⌉` that is
`T₀ ≤ e^{e^{e^{3.2A}/2}/2}`, i.e. about `10^{10^{225}}` at the design floor `A = 162`, which
clears the corpus's own floor `e^{e^{1251}}` by two whole exponential levels.  So the rider is a
MIS-SIZED NUMERAL, not a wall — the same genre as the band lane's `log C ≤ 40` against a true
value of `22 661`.  The repair is therefore:

(a) rethread `capfloor_T0_Tann_sharp` for `capfloor_T0_Tann` and restate the rider in its
`A`-windowed form through the six hops that carry it (`s13CapFloor_all_L_gk`,
`s16_capGate_supply_L_gk`, `s15_crossing_supplied_L_gk(_ceiling)`,
`logChowla2_witnessed_scale_flat_L_v2(_uniform_win)(_ceiling)`, `_v3`) — class B, no analysis;
(b) supply an `A`-free EFFECTIVE ceiling on `T₀`, which needs `ε₀` floored — reachable through
the corpus's own classical region `Salt.SW.zeta_zero_free_region`
(`c₃ = min(1/75712, ε₀·log 2)`) once its height-1 `ε₀` is floored, giving
`ε₀(H) ≥ min(1/2, c₃/log(H+2))`.  That is the CMU-HUNT class-C stone, not new analysis.

Step (b) is the ONLY genuinely open item behind either rider.
-/

namespace Salt.MR

/-! ## §1 — THE `cs` CLOSED FORM, PRICED AT ITS OWN LEAVES -/

/-- `2^{3/4} ≤ 2`. -/
theorem two_rpow_three_quarters_le_two : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
  calc (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

/-- `e^{-100} ≤ 10^{-11}` — the rider's ceiling against a plain decimal, via `log 10 ≤ 9`. -/
theorem exp_neg_hundred_le_ten_pow_neg_eleven : Real.exp (-100) ≤ 1 / 10 ^ 11 := by
  have hlog10 : Real.log 10 ≤ 9 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num)]
  have h11 : Real.log ((10 : ℝ) ^ (11 : ℕ)) ≤ 100 := by
    rw [Real.log_pow]; push_cast; linarith
  have h100 : (10 : ℝ) ^ (11 : ℕ) ≤ Real.exp 100 := by
    have h := Real.exp_le_exp.mpr h11
    rwa [Real.exp_log (by positivity)] at h
  have hone : Real.exp (-100) * Real.exp 100 = 1 := by
    rw [← Real.exp_add]; norm_num
  have hmul : Real.exp (-100) * (10 : ℝ) ^ (11 : ℕ) ≤ Real.exp (-100) * Real.exp 100 :=
    mul_le_mul_of_nonneg_left h100 (Real.exp_pos _).le
  rw [hone] at hmul
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ (11 : ℕ))]
  exact hmul

/-- **⟦THE `cs` FLOOR⟧** the decay constant `halaszPrimesChiGated_of_price` mints —
`min (min (c_vk/(2·K₄)) (c₀/(2·Cκ))) (1/10)` at the source's own leaves `c_vk = 1/10^8`
(`twisted_edge_price_strip`) and `c₀ = 1/10^9` (`zeta_zero_free_region_pow`) — clears the
`v3` rider `e^{-100} ≤ cs` with 33 orders of room.  `K₄ = 2^{3/4}·16` and `Cκ = 2^{3/4}·8` are
closed-form `def`s, NOT compactness existentials. -/
theorem cs_closed_form_ge_exp_neg_hundred :
    Real.exp (-100)
      ≤ min (min ((1 / 10 ^ 8 : ℝ) / (2 * K₄)) ((1 / 10 ^ 9 : ℝ) / (2 * Cκ))) (1 / 10) := by
  have h2r := two_rpow_three_quarters_le_two
  have hK₄ : K₄ ≤ 32 := by rw [K₄]; linarith
  have hK₄0 : (0 : ℝ) < K₄ := by rw [K₄]; positivity
  have hCκ : Cκ ≤ 16 := by rw [Cκ]; linarith
  have hCκ0 : (0 : ℝ) < Cκ := by rw [Cκ]; positivity
  have hbase := exp_neg_hundred_le_ten_pow_neg_eleven
  have h1 : (1 : ℝ) / 10 ^ 11 ≤ (1 / 10 ^ 8 : ℝ) / (2 * K₄) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * K₄)]
    linarith
  have h2 : (1 : ℝ) / 10 ^ 11 ≤ (1 / 10 ^ 9 : ℝ) / (2 * Cκ) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * Cκ)]
    linarith
  have h3 : (1 : ℝ) / 10 ^ 11 ≤ 1 / 10 := by norm_num
  exact le_trans hbase (le_min (le_min h1 h2) h3)

/-! ## §5 — THE `T₀` VIOLATION, ARITHMETIC

`e^{e^{1100}}` — the floor §2–§4 carry — strictly exceeds the rider's ceiling `e^{e^{100}}`. -/

/-- **⟦THE `T₀` RIDER, VIOLATED AT THE CORPUS'S OWN FLOOR⟧** the socket threshold the chain
builds is at least `e^{e^{1100}}` (§4), and `e^{e^{100}} < e^{e^{1100}}`: no witness on this
route can meet `T₀ ≤ e^{e^{100}}`. -/
theorem exp_exp_hundred_lt_exp_exp_1100 :
    Real.exp (Real.exp 100) < Real.exp (Real.exp 1100) :=
  Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (by norm_num))

end Salt.MR

namespace Salt.MR

open Complex Salt.SW Salt.Vk

/-! ## §2 — RUNG 1: the VK power region leaf, both bounds exported

`Salt.Vk.zeta_zero_free_region_pow` pins `c = 1/10^9` and `T₀ = e^{e^{A}} + t₀ + 3` with
`A = 8·log(20000K) + 1100`, but exports only `0 < c` and `3 ≤ T₀`.  This twin exports the two
facts the riders need: the LOWER bound on `c` (for `cs`) and the LOWER bound on the threshold
(for `T₀`).  Body verbatim from `Vk/PowRegion.lean:354`. -/

/-- **⟦VK REGION, BOTH BOUNDS⟧** `Salt.Vk.zeta_zero_free_region_pow_of_growth` with
`1/10^9 ≤ c` and `e^{e^{1100}} ≤ T₀` carried.  Body verbatim. -/
theorem zeta_zero_free_region_pow_of_growth_bounded (hgrow : ZetaGrowthPow) :
    ∃ c T₀ : ℝ, 0 < c ∧ 1 / 10 ^ 9 ≤ c ∧ 3 ≤ T₀ ∧ Real.exp (Real.exp 1100) ≤ T₀ ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 → T₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - c / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ)) := by
  obtain ⟨K, t₀, hK, ht₀, hg⟩ := hgrow
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  set A : ℝ := 8 * Real.log (20000 * K) + 1100 with hAdef
  have hA1100 : 1100 ≤ A := by
    have : (0 : ℝ) ≤ Real.log (20000 * K) := Real.log_nonneg (by nlinarith [hK])
    rw [hAdef]; linarith
  have hEpos : 0 < Real.exp (Real.exp A) := Real.exp_pos _
  refine ⟨1 / 10 ^ 9, Real.exp (Real.exp A) + t₀ + 3, by norm_num, le_rfl,
    by linarith [hEpos, ht₀],
    by
      have h1 : Real.exp (Real.exp 1100) ≤ Real.exp (Real.exp A) :=
        Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hA1100)
      linarith [ht₀], ?_⟩
  -- the positive-height core (then conjugation for negative heights)
  have hpos : ∀ σ : ℂ, riemannZeta σ = 0 → Real.exp (Real.exp A) + t₀ + 3 ≤ σ.im →
      σ.re ≤ 1 - (1 / 10 ^ 9) / ((Real.log σ.im) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log σ.im)) ^ (3 : ℕ)) := by
    intro σ hσ0 hσim
    have hβ1 : σ.re < 1 := by
      by_contra h; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hσ0
    -- discharge the core thresholds
    have hσimE : Real.exp (Real.exp A) ≤ σ.im := by linarith [ht₀, hσim]
    have hγ2 : 2 ≤ σ.im := by linarith [hEpos, ht₀, hσim]
    have hexpA1 : 1 < Real.exp A := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith [hA1100])
    have hEe : Real.exp 1 < Real.exp (Real.exp A) := Real.exp_lt_exp.mpr hexpA1
    have hγe : Real.exp 1 < σ.im - 1 := by linarith [hEe, hσim, ht₀, hEpos]
    have hγt₀ : t₀ ≤ σ.im - 1 := by linarith [hEpos, hσim]
    have hlogE : Real.log (Real.exp (Real.exp A)) = Real.exp A := Real.log_exp _
    have hlogσE : Real.exp A ≤ Real.log σ.im := by
      rw [← hlogE]; exact Real.log_le_log hEpos hσimE
    have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have hexpA3 : (3 : ℝ) ≤ Real.exp A :=
      le_trans hexp2 (Real.exp_le_exp.mpr (by linarith [hA1100]))
    have hL3 : 3 ≤ Real.log σ.im := le_trans hexpA3 hlogσE
    have hℓK : 8 * Real.log (20000 * K) + 1100 ≤ Real.log (Real.log σ.im) := by
      rw [← hAdef]
      calc A = Real.log (Real.exp A) := (Real.log_exp A).symm
        _ ≤ Real.log (Real.log σ.im) := Real.log_le_log (Real.exp_pos A) hlogσE
    have hcore := zeta_zero_free_pow_core hK ht₀ hg hσ0 hβ1 hγ2 hγe hγt₀ hL3 hℓK
    rwa [mul_one_div] at hcore
  intro ρ hρ0 hγ
  by_cases hsign : 0 ≤ ρ.im
  · rw [abs_of_nonneg hsign] at hγ ⊢; exact hpos ρ hρ0 hγ
  · rw [abs_of_neg (not_le.mp hsign)] at hγ ⊢
    have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hsign; simp at hsign
    have hconj0 : riemannZeta ((starRingEnd ℂ) ρ) = 0 := riemannZeta_conj_zero hρ1 hρ0
    have h := hpos ((starRingEnd ℂ) ρ) hconj0 (by rw [Complex.conj_im]; exact hγ)
    rwa [Complex.conj_im, Complex.conj_re] at h

/-- **⟦VK REGION, BOTH BOUNDS, COMPOSED⟧** the twin at the machine-checked strip growth. -/
theorem zeta_zero_free_region_pow_bounded :
    ∃ c T₀ : ℝ, 0 < c ∧ 1 / 10 ^ 9 ≤ c ∧ 3 ≤ T₀ ∧ Real.exp (Real.exp 1100) ≤ T₀ ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 → T₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - c / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ)) :=
  zeta_zero_free_region_pow_of_growth_bounded zeta_growth_pow

end Salt.MR

namespace Salt.MR

open scoped BigOperators
open Complex MeasureTheory Set ArithmeticFunction Metric
open scoped LSeries.notation

/-! ## §3 — RUNG 2: ZFREE-RECT, both bounds carried

`rect_zero_free_margin` passes the region's `c` through verbatim and sets
`T₁ = max 3 (max M E)` with `M` the region's own threshold — so both bounds survive.
Body verbatim from `HalaszPrimesCore.lean:618`. -/

/-- **`D₃` monotonicity** — a verbatim copy of `HalaszPrimesCore`'s `private logD3_mono`
(:548), which the replayed body below needs and which `private` keeps out of reach. -/
private lemma riderTrace_logD3_mono {t₁ t₂ : ℝ} (h1 : Real.exp 1 < t₁) (h12 : t₁ ≤ t₂) :
    (Real.log t₁) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t₁)) ^ (3 : ℕ)
      ≤ (Real.log t₂) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t₂)) ^ (3 : ℕ) := by
  have ht1pos : 0 < t₁ := lt_trans (Real.exp_pos 1) h1
  have hlog1 : 1 < Real.log t₁ := by
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) h1
  have hlog12 : Real.log t₁ ≤ Real.log t₂ := Real.log_le_log ht1pos h12
  have hll1 : 0 < Real.log (Real.log t₁) := Real.log_pos hlog1
  have hll12 : Real.log (Real.log t₁) ≤ Real.log (Real.log t₂) :=
    Real.log_le_log (by linarith) hlog12
  have hbase : (Real.log t₁) ^ ((3 : ℝ) / 4) ≤ (Real.log t₂) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow (by linarith) hlog12 (by norm_num)
  have hll3 : (Real.log (Real.log t₁)) ^ (3 : ℕ) ≤ (Real.log (Real.log t₂)) ^ (3 : ℕ) :=
    pow_le_pow_left₀ hll1.le hll12 3
  exact mul_le_mul hbase hll3 (by positivity) (Real.rpow_nonneg (by linarith) _)

/-- **⟦ZFREE-RECT, BOTH BOUNDS⟧** `rect_zero_free_margin` with `1/10^9 ≤ c_vk` and
`e^{e^{1100}} ≤ T₁` carried.  Body verbatim. -/
theorem rect_zero_free_margin_bounded :
    ∃ (c_vk T₁ : ℝ), 0 < c_vk ∧ 1 / 10 ^ 9 ≤ c_vk ∧ 3 ≤ T₁ ∧
      Real.exp (Real.exp 1100) ≤ T₁ ∧
      ∀ (T : ℝ), T₁ ≤ T →
        0 < (Real.log (5 * T)) ^ ((3 : ℝ) / 4) * (Real.log (Real.log (5 * T))) ^ (3 : ℕ) ∧
        ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≤ 5 * T →
          ρ.re ≤ 1 - c_vk / ((Real.log (5 * T)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T))) ^ (3 : ℕ)) := by
  obtain ⟨c_pow, M, hc_pow, hc_pow9, hM3, hM1100, hregion⟩ := zeta_zero_free_region_pow_bounded
  obtain ⟨ε₀, hε₀, hstrip⟩ := zeta_zero_free_strip_height (M := M) (by linarith : (0 : ℝ) ≤ M)
  set B : ℝ := c_pow / ε₀ with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set E : ℝ := Real.exp (Real.exp 1 + B ^ ((4 : ℝ) / 3)) with hEdef
  set T₁ : ℝ := max 3 (max M E) with hT₁def
  refine ⟨c_pow, T₁, hc_pow, hc_pow9, le_max_left _ _,
    le_trans hM1100 (le_trans (le_max_left M E) (le_max_right 3 _)), ?_⟩
  intro T hT
  have hMle : M ≤ T := le_trans (le_trans (le_max_left M E) (le_max_right 3 _)) hT
  have hEle : E ≤ T := le_trans (le_trans (le_max_right M E) (le_max_right 3 _)) hT
  have hT0 : (0 : ℝ) < T := by linarith [le_trans (le_max_left 3 _) hT]
  have hE5T : E ≤ 5 * T := by linarith
  -- the key height fact: log(5T) ≥ e + B^{4/3}
  have hL5 : Real.exp 1 + B ^ ((4 : ℝ) / 3) ≤ Real.log (5 * T) := by
    rw [← Real.log_exp (Real.exp 1 + B ^ ((4 : ℝ) / 3)), ← hEdef]
    exact Real.log_le_log (Real.exp_pos _) hE5T
  have hB43nn : (0 : ℝ) ≤ B ^ ((4 : ℝ) / 3) := Real.rpow_nonneg hB0 _
  have hexp1_2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL5e : Real.exp 1 ≤ Real.log (5 * T) := by linarith
  have hL5_1 : (1 : ℝ) < Real.log (5 * T) := by linarith
  have hL5pos : (0 : ℝ) < Real.log (5 * T) := by linarith
  have hℓ5 : (1 : ℝ) ≤ Real.log (Real.log (5 * T)) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hL5e
  have hℓ5cube : (1 : ℝ) ≤ (Real.log (Real.log (5 * T))) ^ (3 : ℕ) := one_le_pow₀ hℓ5
  have hL534pos : (0 : ℝ) < (Real.log (5 * T)) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL5pos _
  set D : ℝ := (Real.log (5 * T)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * T))) ^ (3 : ℕ) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  -- L5^{3/4} ≥ B  (so D ≥ B)
  have hBrpow : B = (B ^ ((4 : ℝ) / 3)) ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_mul hB0]; norm_num
  have hL534geB : B ≤ (Real.log (5 * T)) ^ ((3 : ℝ) / 4) := by
    rw [hBrpow]
    exact Real.rpow_le_rpow hB43nn (by linarith) (by norm_num)
  have hDgeB : B ≤ D := by
    rw [hDdef]
    calc B = B * 1 := (mul_one B).symm
      _ ≤ (Real.log (5 * T)) ^ ((3 : ℝ) / 4) * (Real.log (Real.log (5 * T))) ^ (3 : ℕ) :=
          mul_le_mul hL534geB hℓ5cube (by norm_num) hL534pos.le
  -- c_pow / D ≤ ε₀
  have hcpowD : c_pow / D ≤ ε₀ := by
    rw [div_le_iff₀ hDpos]
    have hcε : c_pow = ε₀ * B := by rw [hBdef]; field_simp
    calc c_pow = ε₀ * B := hcε
      _ ≤ ε₀ * D := mul_le_mul_of_nonneg_left hDgeB hε₀.le
  refine ⟨hDpos, ?_⟩
  intro ρ hρ0 hρim
  by_cases hcase : M ≤ |ρ.im|
  · -- high height: the power region + `D₃` monotonicity
    have hργ : Real.exp 1 < |ρ.im| := by
      have h3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      exact lt_of_lt_of_le h3 (le_trans hM3 hcase)
    have hreg := hregion ρ hρ0 hcase
    have hmono := riderTrace_logD3_mono hργ hρim
    have hden_ρ_pos : 0 < (Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ) := by
      have hlρ : 1 < Real.log |ρ.im| := by
        rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hργ
      have : 0 < Real.log (Real.log |ρ.im|) := Real.log_pos hlρ
      positivity
    have hstep : c_pow / D ≤ c_pow / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ)) :=
      div_le_div_of_nonneg_left hc_pow.le hden_ρ_pos (by rw [hDdef]; exact hmono)
    linarith [hreg, hstep]
  · -- low height: the fixed strip
    have hlow : |ρ.im| < M := not_le.mp hcase
    have hst := hstrip hρ0 (le_of_lt hlow)
    linarith [hst, hcpowD]

end Salt.MR

namespace Salt.MR

open scoped BigOperators
open Complex MeasureTheory ArithmeticFunction
open scoped LSeries.notation

section RiderTraceShiftedEdge
open Complex Salt.SW Salt.Vk Metric Set

/-! ## §4 — RUNG 3: the shifted edge strip, both bounds carried

`shifted_edge_price_strip` passes `c_vk` through verbatim and sets
`T₀ = max (max T₁ 3) (e^{e^{Cbig}})` — so the ZFREE-RECT floor survives, and the SECOND floor
`e^{e^{Cbig}}`, `Cbig = 9000·c_vk + c_vk/(2·δ₀) + 1`, enters here with `δ₀` the opaque
compactness constant of `logDeriv_Zc_compact_bound` at height `H = e^{e^{A}}`.  That second
floor is why `T₀` has no effective ceiling today.  Body verbatim from
`HalaszPrimesCore.lean:2246`. -/

set_option maxHeartbeats 800000 in
-- Body verbatim from the landed `shifted_edge_price_strip`; the packaged case split needs the
-- landed declaration's own heartbeat room.
/-- **⟦SHIFTED EDGE STRIP, BOTH BOUNDS⟧** `shifted_edge_price_strip` with `1/10^9 ≤ c_vk` and
`e^{e^{1100}} ≤ T₀` carried.  Body verbatim. -/
theorem shifted_edge_price_strip_bounded :
    ∃ (c_vk CE T₀ : ℝ), 0 < c_vk ∧ 1 / 10 ^ 9 ≤ c_vk ∧ 0 < CE ∧ 3 ≤ T₀ ∧
      Real.exp (Real.exp 1100) ≤ T₀ ∧
      (∀ (T : ℝ), T₀ ≤ T → ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
          ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ))) ∧
      ∀ (T x γ : ℝ), T₀ ≤ T →
          1 - (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)) ≤ x →
          x ≤ 1 + (c_vk / 2) / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)) →
          |γ| ≤ 5 * T →
        ‖logDeriv Zc ((x : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ CE * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) := by
  obtain ⟨c_vk, T₁, hc_vk0, hc_vk9, hT₁, hT₁1100, hmarg⟩ := rect_zero_free_margin_bounded
  obtain ⟨K, t₀K, hK, ht₀K, hg⟩ := Salt.Vk.zeta_growth_pow
  set H : ℝ := Real.exp (Real.exp (8 * Real.log (20000 * K) + 1100)) + t₀K + 3 with hHdef
  have hH0 : 0 ≤ H := by
    rw [hHdef]; have := Real.exp_pos (Real.exp (8 * Real.log (20000 * K) + 1100)); linarith [ht₀K]
  obtain ⟨δ₀, C₀, hδ₀0, hcpt⟩ := logDeriv_Zc_compact_bound (M := H) (c := 2) hH0 (by norm_num)
  set Cbig : ℝ := 9000 * c_vk + c_vk / (2 * δ₀) + 1 with hCbigdef
  set CE : ℝ := (10 ^ 8 + 200 / c_vk) + (|C₀| + 1) with hCEdef
  set T₀ : ℝ := max (max T₁ 3) (Real.exp (Real.exp Cbig)) with hT₀def
  have hCE0 : 0 < CE := by rw [hCEdef]; positivity
  refine ⟨c_vk, CE, T₀, hc_vk0, hc_vk9, hCE0,
    le_trans (le_max_right _ _) (le_max_left _ _),
    le_trans hT₁1100 (le_trans (le_max_left T₁ 3) (le_max_left _ _)), ?_, ?_⟩
  · -- the margin clause (used by RES/ASM)
    intro T hT ρ hρ0 hρim
    have hTT₁ : T₁ ≤ T + 1 / 5 := by
      have := le_trans (le_trans (le_max_left T₁ 3) (le_max_left _ _)) hT; linarith
    have h := (hmarg (T + 1 / 5) hTT₁).2 ρ hρ0
    rw [show 5 * (T + 1 / 5) = 5 * T + 1 by ring] at h
    exact h hρim
  · -- the strip bound
    intro T x γ hT hxlb hxub hγ5T
    have hTT₁ : T₁ ≤ T + 1 / 5 := by
      have := le_trans (le_trans (le_max_left T₁ 3) (le_max_left _ _)) hT; linarith
    have hTexp : Real.exp (Real.exp Cbig) ≤ T := le_trans (le_max_right _ _) hT
    have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hTexp
    have h5T1exp : Real.exp (Real.exp Cbig) ≤ 5 * T + 1 := by linarith [hTexp, hTpos]
    have ha5 : 0 < Real.log (5 * T + 1) :=
      lt_of_lt_of_le (Real.exp_pos _) (by
        rw [← Real.log_exp (Real.exp Cbig)]; exact Real.log_le_log (Real.exp_pos _) h5T1exp)
    have hlog5T1 : Real.exp Cbig ≤ Real.log (5 * T + 1) := by
      rw [← Real.log_exp (Real.exp Cbig)]; exact Real.log_le_log (Real.exp_pos _) h5T1exp
    have hloglog : Cbig ≤ Real.log (Real.log (5 * T + 1)) := by
      rw [← Real.log_exp Cbig]; exact Real.log_le_log (Real.exp_pos _) hlog5T1
    -- the reused margin fact at 5T+1
    have hmargT : ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)) := by
      intro ρ hρ0 hρim
      have h := (hmarg (T + 1 / 5) hTT₁).2 ρ hρ0
      rw [show 5 * (T + 1 / 5) = 5 * T + 1 by ring] at h
      exact h hρim
    -- the hsc threshold for the disc
    have hsc_thr : 9000 * c_vk ≤ Real.log (Real.log (5 * T + 1)) := by
      have hnn : (0:ℝ) ≤ c_vk / (2 * δ₀) := by positivity
      have hle : 9000 * c_vk ≤ Cbig := by rw [hCbigdef]; linarith [hnn]
      linarith [hle, hloglog]
    -- D₃(5T+1), D₄(5T+1) facts
    set LT : ℝ := Real.log (5 * T + 1) with hLTdef
    set ℓT : ℝ := Real.log LT with hℓTdef
    have hℓTge : (1:ℝ) ≤ ℓT := by
      have hnn : (0:ℝ) ≤ 9000 * c_vk + c_vk / (2 * δ₀) := by positivity
      have hle : (1:ℝ) ≤ Cbig := by rw [hCbigdef]; linarith [hnn]
      linarith [hle, hloglog]
    have hℓTpos : 0 < ℓT := by linarith [hℓTge]
    have hLTge : Real.exp 1 ≤ LT := by
      have h1 : Real.exp 1 ≤ Real.exp ℓT := Real.exp_le_exp.mpr hℓTge
      rwa [hℓTdef, Real.exp_log ha5] at h1
    have hLT1 : (1:ℝ) ≤ LT := le_trans (by linarith [Real.add_one_le_exp (1:ℝ)]) hLTge
    have hLTpos : 0 < LT := by linarith [hLT1]
    set D3T : ℝ := LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) with hD3Tdef
    have hLT34ge : (1:ℝ) ≤ LT ^ ((3 : ℝ) / 4) := Real.one_le_rpow hLT1 (by norm_num)
    have hℓT4ge : (1:ℝ) ≤ ℓT ^ (4 : ℕ) := one_le_pow₀ hℓTge
    have hD3Tpos : 0 < D3T := by rw [hD3Tdef]; positivity
    have hD4nn : (0:ℝ) ≤ LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ) :=
      mul_nonneg (Real.rpow_nonneg hLTpos.le _) (pow_nonneg hℓTpos.le _)
    have hD41 : (1:ℝ) ≤ LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ) := by nlinarith [hLT34ge, hℓT4ge]
    -- the δ₀ condition: (c_vk/2)/D₃(5T+1) ≤ δ₀
    have hδcond : (c_vk / 2) / D3T ≤ δ₀ := by
      have hbase : c_vk / (2 * δ₀) ≤ ℓT := by
        have hnn : (0:ℝ) ≤ 9000 * c_vk := by positivity
        have hle : c_vk / (2 * δ₀) ≤ Cbig := by rw [hCbigdef]; linarith [hnn]
        linarith [hle, hloglog]
      have hcube3 : ℓT ≤ ℓT ^ (3 : ℕ) := by
        have h2 : (1:ℝ) ≤ ℓT ^ (2:ℕ) := one_le_pow₀ hℓTge
        nlinarith [mul_le_mul_of_nonneg_left h2 hℓTpos.le]
      have hD3ge : c_vk / (2 * δ₀) ≤ D3T := by
        rw [hD3Tdef]
        calc c_vk / (2 * δ₀) ≤ ℓT ^ (3 : ℕ) := le_trans hbase hcube3
          _ = 1 * ℓT ^ (3 : ℕ) := (one_mul _).symm
          _ ≤ LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) :=
              mul_le_mul_of_nonneg_right hLT34ge (pow_nonneg hℓTpos.le _)
      have hδpos : 0 < 2 * δ₀ := by linarith [hδ₀0]
      rw [div_le_iff₀ hδpos] at hD3ge
      rw [div_le_iff₀ hD3Tpos]
      nlinarith [hD3ge, hδ₀0, hD3Tpos]
    -- the strip's upper endpoint: (c_vk/2)/D₃(5T+1) ≤ 1, so 1+w ≤ 2
    have hwle1 : (c_vk / 2) / D3T ≤ 1 := by
      rw [div_le_one hD3Tpos]
      have hchalf : c_vk / 2 ≤ ℓT := by linarith [hsc_thr, hc_vk0]
      have hcube3 : ℓT ≤ ℓT ^ (3 : ℕ) := by
        have h2 : (1:ℝ) ≤ ℓT ^ (2:ℕ) := one_le_pow₀ hℓTge
        nlinarith [mul_le_mul_of_nonneg_left h2 hℓTpos.le]
      have hD3ge : ℓT ^ (3 : ℕ) ≤ D3T := by
        rw [hD3Tdef]
        calc ℓT ^ (3 : ℕ) = 1 * ℓT ^ (3 : ℕ) := (one_mul _).symm
          _ ≤ LT ^ ((3 : ℝ) / 4) * ℓT ^ (3 : ℕ) :=
              mul_le_mul_of_nonneg_right hLT34ge (pow_nonneg hℓTpos.le _)
      linarith [hchalf, hcube3, hD3ge]
    -- case split on |γ| vs H
    by_cases hcase : H ≤ |γ|
    · -- high height: disc-core-gen (+ conjugation for γ < 0)
      by_cases hsign : (0:ℝ) ≤ γ
      · have hγH : H ≤ γ := by rwa [abs_of_nonneg hsign] at hcase
        have hγT5 : γ ≤ 5 * T := by rwa [abs_of_nonneg hsign] at hγ5T
        have hbound := shifted_edge_disc_core_gen (T := T) (x := x) hK ht₀K hg hc_vk0 hxlb hxub
          (by rw [hHdef] at hγH; exact hγH) hγT5 hsc_thr hmargT
        rw [← hLTdef, ← hℓTdef] at hbound
        refine le_trans hbound ?_
        exact mul_le_mul_of_nonneg_right (by rw [hCEdef]; linarith [abs_nonneg C₀]) hD4nn
      · have hsignlt : γ < 0 := not_le.mp hsign
        have hγH : H ≤ -γ := by rw [abs_of_neg hsignlt] at hcase; exact hcase
        have hγT5 : -γ ≤ 5 * T := by rw [abs_of_neg hsignlt] at hγ5T; exact hγ5T
        have hbound := shifted_edge_disc_core_gen (T := T) (x := x) hK ht₀K hg hc_vk0 hxlb hxub
          (by rw [hHdef] at hγH; exact hγH) hγT5 hsc_thr hmargT
        rw [← hLTdef, ← hℓTdef] at hbound
        have hconj : (x : ℂ) + (γ : ℂ) * Complex.I
            = (starRingEnd ℂ) ((x : ℂ) + ((-γ : ℝ) : ℂ) * Complex.I) := by
          rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
          push_cast; ring
        rw [hconj, logDeriv_Zc_norm_conj]
        refine le_trans hbound ?_
        exact mul_le_mul_of_nonneg_right (by rw [hCEdef]; linarith [abs_nonneg C₀]) hD4nn
    · -- moderate height: the compact bound
      rw [not_le] at hcase
      set z : ℂ := (x : ℂ) + (γ : ℂ) * Complex.I with hzdef
      have hzre : z.re = x := by rw [hzdef]; simp
      have hzim : z.im = γ := by rw [hzdef]; simp
      have hσ₀ge : 1 - δ₀ ≤ z.re := by rw [hzre]; linarith [hδcond, hxlb]
      have hσ₀le : z.re ≤ 2 := by rw [hzre]; linarith [hwle1, hxub]
      have himle : |z.im| ≤ H := by rw [hzim]; exact le_of_lt hcase
      have hcptb := hcpt z hσ₀ge hσ₀le himle
      refine le_trans hcptb ?_
      calc C₀ ≤ |C₀| := le_abs_self _
        _ ≤ CE := by
          rw [hCEdef]
          have h200 : (0:ℝ) ≤ 200 / c_vk := by positivity
          linarith [h200]
        _ = CE * 1 := (mul_one _).symm
        _ ≤ CE * (LT ^ ((3 : ℝ) / 4) * ℓT ^ (4 : ℕ)) :=
            mul_le_mul_of_nonneg_left hD41 hCE0.le

end RiderTraceShiftedEdge

end Salt.MR
