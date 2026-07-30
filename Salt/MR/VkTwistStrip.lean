/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.VkTwistLadder
import Salt.MR.VkMidSharp

/-!
# STONE A — the twisted VK STRIP growth, in BOX form (`LFunctionGrowthPow`, twisted)

The KMT port's P-6 needs the χ-analogue of `Salt.Vk.zeta_growth_pow`: a growth ceiling for
`L(·,χ)` valid on the WHOLE Vinogradov–Korobov strip `Re z ≥ 1 − vkTheta(Im z)` — not merely at
the near-1-line bridge point `1 + 1/log X` where `VkTwistLadder.vkTwistUB_holds` delivers it.
The strip form is what `VkTwistRegionProbe.LFunction_region_of_uniform_growth` consumes (its
`hgrowth`/`hgrowth2` binders), and the box `Re z ∈ [1−Θ, 2]`, `Im z ∈ [γ−1, 3γ]` is the box
containing all four Borel–Carathéodory spheres of the 3-4-1 disc assembly.

## The route (three landed stones, one new fold)

1. **The per-block bound is ALREADY general-`σ`.**  `Salt.Vk.vk_dirichlet_block_twist_all` bounds
   every dyadic twisted block by `1348` on `σ ≥ 1 − vkTheta t` with **no upper gate on `σ`** and
   no Diophantine hypothesis on the twist `β`.  So on the strip no Abel fold is needed at all:
   the block bound applies at the actual `σ`.
2. **The dyadic ladder** (`vk_twist_strip_sum_le`) — `≤ 3(1 + log t)` blocks, each `≤ 1348`,
   giving `4050(1 + log t)`.  This is the exact twin of `Salt.Vk.vk_dirichlet_sum_le` (ζ's own
   strip ladder), with the twist carried through and the `σ ≥ 1` harmonic branch DELETED (the
   block bound covers `σ ≥ 1` too).
3. **The finite Fourier completion** (`VkTwistLadder.char_sum_fourier_le`, elementary
   orthogonality, `|c_a| ≤ q`, no Gauss sums) — one factor `q`.
4. **The truncation** at `N = ⌈t²⌉` through `Salt.SW.norm_LFunction_sub_partial_le` at the CRUDE
   level bound `M = q` (`VkMidSharp.norm_char_partial_sum_le`).  Gate `0 < Re s`: the strip's
   `σ ≥ 999/1000` clears it with room, and the tail is `≤ 4q` because `N^{−σ} ≤ 1/|t|`.

## The honest `q`-cost, and the honest growth SHAPE (both deviations, both favourable)

* **`Cq = 5000·q`, LINEAR in `q`** (`vkStripConst`).  The freeze's `q^{3/2}(1+log q)` came from
  Pólya–Vinogradov (`√q(1+log q)`, PRIMITIVE only) in the bridge-point ladder.  On the strip the
  truncation length `N ≍ t²` is so long that the CRUDE character-sum bound `M = q` suffices, so
  no `√q(1+log q)` and no imprimitivity adapter is needed: the completion's `q` is the whole
  price.  The constant is kept symbolic in every statement regardless (SPECTRUM-SCOPE's iron
  rule).
* **The growth is `Cq·(1 + log|t|)`, not `Cq·(log|t|)^{3/4}(loglog|t|)⁴`.**  The sharper
  `(3/4)`-profile is a NEAR-1-LINE phenomenon: it comes from the geometric decay `M^{−Θ/2}` of the
  Abel-folded blocks, which needs `σ ≥ 1 − Θ/2`, i.e. HALF the strip.  On the full strip the
  honest ceiling is the block count, `log t` — which is exactly ζ's own strip shape
  (`zeta_growth_pow`: `K·log t`).  This costs the region nothing: the width law
  (`VkTwistRegionProbe.LFunction_zero_free_width_law`) sees `M` only through `log M`, so the
  `(1/4)·loglog` difference is additive inside a logarithm, and keeping the FULL strip (rather
  than halving `Θ`) makes the final width constant about `2×` BETTER.  See
  `Salt.MR.VkTwistRegion` for the arithmetic.

## Traps observed

* the `Θ` convention is `Salt.Vk.vkTheta` verbatim — the same strip ζ uses, so
  `Salt.Vk.vkTheta_anti` supplies the box's uniformity exactly as in `Salt.Vk.pow_uniform_growth`;
* the height floor is the landed `exp(exp 100)`-genre one, carried honestly (the block bound's
  own `log t ≥ e^100`), and in the box form it reads `exp(exp 100) ≤ γ − 1` (ζ's `hγt₀` shape);
* the frequency `T` may be NEGATIVE (the probe's boxes sit at `Im ρ` and `2 Im ρ`, and the
  negative-height half of the region needs the mirrored box): `vk_twist_strip_abs_le` closes the
  sign by conjugating the twist, `β ↦ −β`;
* no `set L := …` anywhere (the banked `LSeries`-notation collision).
-/

noncomputable section

namespace Salt.MR

open Complex DirichletCharacter Salt.Vk Salt.ExpSum

/-! ## §1 — the twisted dyadic ladder on the WHOLE VK strip -/

/-- **The twisted strip head bound.**  For `log t ≥ e^100`, every `σ ≥ 1 − vkTheta t` (no upper
gate), every twist `β` and every `N ≤ t² + 1`,

  `‖∑_{n ≤ N} e(βn)·n^{−(σ+it)}‖ ≤ 4050·(1 + log t)`.

The `σ`-general twin of `VkTwistLadder.vk_twist_head_le` and the twisted twin of
`Salt.Vk.vk_dirichlet_sum_le`: `≤ 3(1+log t)` dyadic blocks (`vk_dirichlet_block_twist_all`),
each `≤ 1348`, plus the `n = 1` term. -/
theorem vk_twist_strip_sum_le {σ t β : ℝ} {N : ℕ}
    (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t)
    (hσlo : 1 - vkTheta t ≤ σ) (hN1 : 1 ≤ N) (hNle : (N : ℝ) ≤ t ^ 2 + 1) :
    ‖∑ n ∈ Finset.Icc 1 N, eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
      ≤ 4050 * (1 + Real.log t) := by
  have hlogtpos : 0 < Real.log t := lt_of_lt_of_le (Real.exp_pos 100) hL100
  have hexp101 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hlogtnn : (0 : ℝ) ≤ Real.log t := hlogtpos.le
  have ht1 : (1 : ℝ) ≤ t := by
    have h := Real.exp_lt_exp.mpr hlogtpos
    rw [Real.exp_zero, Real.exp_log ht0] at h; linarith
  have hNt2u : (N : ℝ) ≤ 2 * t ^ 2 := by nlinarith [hNle, ht1]
  -- every dyadic block inside `(1, N]` is `≤ 1348`
  have hblock : ∀ M x' : ℕ, 1 ≤ M → M < x' → x' ≤ 2 * M → x' ≤ N →
      ‖∑ n ∈ Finset.Ioc M x', eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
        ≤ 1348 := by
    intro M x' hM1 hMx' hx'2 hx'N
    have hMt2 : (M : ℝ) ≤ t ^ 2 := by
      have hMN : M + 1 ≤ N := by omega
      have hMNR : (M : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hMN
      linarith
    exact vk_dirichlet_block_twist_all ht0 hL100 hσlo hM1 hMx' hx'2 hMt2
  -- the ladder over `≤ J` blocks
  have hlad : ∀ (J Y : ℕ), 1 ≤ Y → Y ≤ 2 ^ J → Y ≤ N →
      ‖∑ n ∈ Finset.Ioc 1 Y, eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
        ≤ 1348 * J := by
    intro J
    induction J with
    | zero =>
        intro Y hY0 hY1 _
        simp only [pow_zero] at hY1
        have : Y = 1 := le_antisymm hY1 hY0
        subst this; simp
    | succ J ih =>
        intro Y hY0 hY1 hYN
        by_cases hc : Y ≤ 2 ^ J
        · refine le_trans (ih Y hY0 hc hYN) ?_
          have : (0 : ℝ) ≤ (J : ℝ) := by positivity
          push_cast; nlinarith
        · replace hc : 2 ^ J < Y := not_le.mp hc
          have hmid : 1 ≤ 2 ^ J := Nat.one_le_pow J 2 (by norm_num)
          have hsplit : ∑ n ∈ Finset.Ioc 1 Y,
                eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))
              = ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ J),
                  eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))
                + ∑ n ∈ Finset.Ioc (2 ^ J) Y,
                  eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) :=
            (Finset.sum_Ioc_consecutive _ hmid (le_of_lt hc)).symm
          rw [hsplit]
          refine le_trans (norm_add_le _ _) ?_
          have hb1 := ih (2 ^ J) hmid (le_refl _) (le_trans (le_of_lt hc) hYN)
          have hY2M : Y ≤ 2 * 2 ^ J := by
            rw [show 2 * 2 ^ J = 2 ^ (J + 1) from by rw [pow_succ]; ring]; exact hY1
          have hb2 := hblock (2 ^ J) Y hmid hc hY2M hYN
          calc _ ≤ 1348 * (J : ℝ) + 1348 := add_le_add hb1 hb2
            _ = 1348 * ((J + 1 : ℕ) : ℝ) := by push_cast; ring
  obtain ⟨J, hJspec⟩ : ∃ J : ℕ, N ≤ 2 ^ J := ⟨N, le_of_lt Nat.lt_two_pow_self⟩
  -- the block count
  have hex : ∃ J : ℕ, N ≤ 2 ^ J := ⟨J, hJspec⟩
  set J₀ := Nat.find hex with hJ₀def
  have hmain := hlad J₀ N hN1 (Nat.find_spec hex) (le_refl N)
  have hJcount : (J₀ : ℝ) ≤ 3 + 3 * Real.log t := by
    rcases Nat.eq_zero_or_pos J₀ with hJ0 | hJpos
    · rw [hJ0]; push_cast; linarith
    · have hJm1 : 2 ^ (J₀ - 1) < N :=
        not_le.mp (Nat.find_min hex (show J₀ - 1 < J₀ by omega))
      have h2lt : (2 : ℝ) ^ (J₀ - 1) < 2 * t ^ 2 := by
        have : ((2 : ℝ) ^ (J₀ - 1)) < (N : ℝ) := by exact_mod_cast hJm1
        linarith [hNt2u]
      have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hlogineq : ((J₀ : ℝ) - 1) * Real.log 2 < Real.log 2 + 2 * Real.log t := by
        have h := Real.log_lt_log (by positivity) h2lt
        rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
        have hcast : ((J₀ - 1 : ℕ) : ℝ) = (J₀ : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [hcast] at h; push_cast at h; linarith [h]
      have h23 : (2 : ℝ) ≤ 3 * Real.log 2 := by
        have := Real.log_two_gt_d9; nlinarith
      nlinarith [hlogineq, hlog2pos, h23, hlogtnn]
  -- the head term `n = 1`
  have hins : Finset.Icc 1 N = insert 1 (Finset.Ioc 1 N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
  have h1notin : (1 : ℕ) ∉ Finset.Ioc 1 N := by simp
  rw [hins, Finset.sum_insert h1notin]
  refine le_trans (norm_add_le _ _) ?_
  have h1n : ‖eR (β * ((1 : ℕ) : ℝ)) * ((1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ = 1 := by
    rw [norm_mul, norm_eR, Nat.cast_one, Complex.one_cpow, norm_one, one_mul]
  rw [h1n]
  linarith [hmain, hJcount]

/-- Conjugation passes through a positive-integer cpow (the private twin in
`VkTwistLadder`, re-derived here). -/
private lemma strip_conj_natCast_cpow {n : ℕ} (hn : 1 ≤ n) (w : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ w) = (n : ℂ) ^ ((starRingEnd ℂ) w) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hlog : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_conj,
    map_mul, hlog, Complex.conj_ofReal]

/-- **The twisted strip head bound at either sign of the frequency.**  The twist family is closed
under `β ↦ −β`, so conjugating the whole sum turns `(β, T)` into `(−β, −T)`: the positive branch
covers both signs. -/
theorem vk_twist_strip_abs_le {σ T β : ℝ} {N : ℕ}
    (hT : Real.exp (Real.exp 100) ≤ |T|)
    (hσlo : 1 - vkTheta |T| ≤ σ) (hN1 : 1 ≤ N) (hNle : (N : ℝ) ≤ T ^ 2 + 1) :
    ‖∑ n ∈ Finset.Icc 1 N, eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * I))‖
      ≤ 4050 * (1 + Real.log |T|) := by
  have habs0 : (0 : ℝ) < |T| := lt_of_lt_of_le (Real.exp_pos _) hT
  have hL100 : Real.exp 100 ≤ Real.log |T| := by
    have h := Real.log_le_log (Real.exp_pos _) hT
    rwa [Real.log_exp] at h
  rcases le_or_gt 0 T with hTpos | hTneg
  · rw [abs_of_nonneg hTpos] at hT hσlo hL100 ⊢
    exact vk_twist_strip_sum_le (by rw [abs_of_nonneg hTpos] at habs0; exact habs0) hL100
      hσlo hN1 hNle
  · rw [abs_of_neg hTneg] at hT hσlo hL100 ⊢
    have hswap : ∑ n ∈ Finset.Icc 1 N,
          eR ((-β) * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
        = (starRingEnd ℂ) (∑ n ∈ Finset.Icc 1 N,
            eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * I))) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Finset.mem_Icc] at hn
      rw [map_mul, conj_eR, strip_conj_natCast_cpow hn.1, neg_mul]
      congr 1
      congr 1
      simp only [map_neg, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      push_cast
      ring
    have hnorm : ‖∑ n ∈ Finset.Icc 1 N,
          eR ((-β) * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + ((-T : ℝ) : ℂ) * I))‖
        = ‖∑ n ∈ Finset.Icc 1 N,
            eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * I))‖ := by
      rw [hswap, RCLike.norm_conj]
    rw [← hnorm]
    exact vk_twist_strip_sum_le (by linarith) hL100 hσlo hN1
      (by rw [show (-T) ^ 2 = T ^ 2 from by ring]; exact hNle)

/-! ## §2 — the Fourier completion: the character head on the strip -/

/-- **The character strip head bound.**  Fourier completion (`char_sum_fourier_le`, one factor
`q`) applied to the twisted strip ladder: the length-`N` head of `L(·,χ)` at `σ + iT` with
`σ ≥ 1 − vkTheta|T|` is `≤ q·4050·(1 + log|T|)`. -/
theorem vk_char_strip_head_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ T : ℝ} {N : ℕ}
    (hT : Real.exp (Real.exp 100) ≤ |T|)
    (hσlo : 1 - vkTheta |T| ≤ σ) (hN1 : 1 ≤ N) (hNle : (N : ℝ) ≤ T ^ 2 + 1) :
    ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * I))‖
      ≤ (q : ℝ) * (4050 * (1 + Real.log |T|)) :=
  char_sum_fourier_le χ (Finset.Icc 1 N)
    (fun n => (n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * I)))
    (fun _a _ => vk_twist_strip_abs_le hT hσlo hN1 hNle)

/-! ## §3 — the truncation, and the strip growth for `L(·,χ)` -/

/-- **THE STRIP GROWTH CONSTANT** — `5000·q`, LINEAR in the level.  The completion's `q`
(`char_sum_fourier_le`) times the ladder's `4050`, plus the truncation's `4q`.  Symbolic
everywhere downstream: SPECTRUM-SCOPE's iron rule forbids absorbing the `q`-cost. -/
def vkStripConst (q : ℕ) : ℝ := 5000 * (q : ℝ)

lemma one_le_vkStripConst {q : ℕ} [NeZero q] : 1 ≤ vkStripConst q := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [vkStripConst]; linarith

/-- `vkTheta t ≤ 1/1000` past the schedule floor (both log factors are `≥ 1`). -/
lemma vkTheta_le_thousandth {t : ℝ} (hL1 : 1 ≤ Real.log t)
    (hℓ1 : 1 ≤ Real.log (Real.log t)) : vkTheta t ≤ 1 / 1000 := by
  rw [vkTheta]
  have h1 : (1 : ℝ) ≤ (Real.log t) ^ ((3 : ℝ) / 4) := Real.one_le_rpow hL1 (by norm_num)
  have h2 : (1 : ℝ) ≤ (Real.log (Real.log t)) ^ (2 : ℕ) := one_le_pow₀ hℓ1
  have hD : (1 : ℝ) ≤ (Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (2 : ℕ) := by
    nlinarith [h1, h2]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [hD]

set_option maxHeartbeats 1000000 in
-- The truncation/head assembly stages the rpow height bookkeeping through `nlinarith`, as in
-- `VkTwistLadder.vk_LFunction_bridge_le_primitive`'s own budget.
/-- **STONE A — THE TWISTED STRIP GROWTH.**  For every nonprincipal `χ mod q`, every height
`|T| ≥ exp(exp 100)` and every `σ` on the VK strip `1 − vkTheta|T| ≤ σ ≤ 2`,

  `‖L(σ + iT, χ)‖ ≤ vkStripConst q · (1 + log|T|)`,  `vkStripConst q = 5000 q`.

The χ-twin of `Salt.Vk.zeta_growth_pow` (whose own shape is `K·log t`), at the SAME half-width
`Salt.Vk.vkTheta`.  Head: `vk_char_strip_head_le`.  Tail: `Salt.SW.norm_LFunction_sub_partial_le`
at the crude level bound `M = q` and `N = ⌈T²⌉`, where `N^{−σ} ≤ 1/|T|` makes the error `≤ 4q`. -/
theorem vk_char_strip_growth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ T : ℝ} (hT : Real.exp (Real.exp 100) ≤ |T|)
    (hσlo : 1 - vkTheta |T| ≤ σ) (hσ2 : σ ≤ 2) :
    ‖LFunction χ ((σ : ℂ) + (T : ℂ) * I)‖ ≤ vkStripConst q * (1 + Real.log |T|) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with hlt | hge
    · exact absurd (χ.level_one' (by omega)) hχ
    · exact hge
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  -- height facts
  have habs0 : (0 : ℝ) < |T| := lt_of_lt_of_le (Real.exp_pos _) hT
  have hexp101 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hbig : (101 : ℝ) ≤ |T| := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) :=
      Real.exp_le_exp.mpr (by linarith [hexp101])
    linarith [hT, hexp101, h2]
  obtain ⟨hL100, hℓ100⟩ := vk_height_facts hT
  have hL1 : (1 : ℝ) ≤ Real.log |T| := by linarith [hL100, hexp101]
  have hℓ1 : (1 : ℝ) ≤ Real.log (Real.log |T|) := by linarith
  have hΘsmall : vkTheta |T| ≤ 1 / 1000 := vkTheta_le_thousandth hL1 hℓ1
  have hσlo' : (999 : ℝ) / 1000 ≤ σ := by linarith [hσlo, hΘsmall]
  have hσpos : 0 < σ := by linarith
  -- the truncation length
  set N : ℕ := ⌈T ^ 2⌉₊ with hNdef
  have hT2pos : (0 : ℝ) < T ^ 2 := by nlinarith [habs0, sq_abs T]
  have hN1 : 1 ≤ N := by rw [hNdef]; exact Nat.one_le_ceil_iff.mpr hT2pos
  have hNge : T ^ 2 ≤ (N : ℝ) := by rw [hNdef]; exact Nat.le_ceil _
  have hNle : (N : ℝ) ≤ T ^ 2 + 1 := by
    rw [hNdef]; exact le_of_lt (Nat.ceil_lt_add_one hT2pos.le)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  -- the point
  have hsre : ((σ : ℂ) + (T : ℂ) * I).re = σ := by simp
  have hsnorm : ‖(σ : ℂ) + (T : ℂ) * I‖ ≤ 2 + |T| := by
    have h1 : ‖((σ : ℝ) : ℂ)‖ = |σ| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖((T : ℝ) : ℂ) * I‖ = |T| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    calc ‖(σ : ℂ) + (T : ℂ) * I‖ ≤ ‖((σ : ℝ) : ℂ)‖ + ‖((T : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ = |σ| + |T| := by rw [h1, h2]
      _ ≤ 2 + |T| := by
          have : |σ| = σ := abs_of_nonneg hσpos.le
          rw [this]; linarith
  -- the truncation error
  have htrunc := Salt.SW.norm_LFunction_sub_partial_le χ hχ hq2 (norm_char_partial_sum_le χ hχ)
    (s := (σ : ℂ) + (T : ℂ) * I) (by rw [hsre]; exact hσpos) hN1
  rw [hsre] at htrunc
  have hNσ : (N : ℝ) ^ (-σ) ≤ 1 / |T| := by
    have h1 : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
    have h2 : (N : ℝ) ^ (-(1 / 2) : ℝ) ≤ (T ^ 2 : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hT2pos hNge (by norm_num)
    have h3 : (T ^ 2 : ℝ) ^ (-(1 / 2) : ℝ) = 1 / |T| := by
      rw [Real.rpow_neg hT2pos.le, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, one_div]
    linarith [h1, h2, h3]
  have herr : (q : ℝ) * (1 + ‖(σ : ℂ) + (T : ℂ) * I‖ * (1 + 1 / σ)) * (N : ℝ) ^ (-σ)
      ≤ 4 * (q : ℝ) := by
    have hinv : (1 : ℝ) + 1 / σ ≤ 3 := by
      have : 1 / σ ≤ 2 := by
        rw [div_le_iff₀ hσpos]; linarith [hσlo']
      linarith
    have hfac : (1 : ℝ) + ‖(σ : ℂ) + (T : ℂ) * I‖ * (1 + 1 / σ) ≤ 7 + 3 * |T| := by
      have hnn : (0 : ℝ) ≤ ‖(σ : ℂ) + (T : ℂ) * I‖ := norm_nonneg _
      nlinarith [hsnorm, hinv, hnn, habs0]
    have hfac0 : (0 : ℝ) ≤ 1 + ‖(σ : ℂ) + (T : ℂ) * I‖ * (1 + 1 / σ) := by
      have hnn : (0 : ℝ) ≤ ‖(σ : ℂ) + (T : ℂ) * I‖ := norm_nonneg _
      have : (0 : ℝ) ≤ 1 / σ := by positivity
      nlinarith [hnn]
    have hNσ0 : (0 : ℝ) ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg hNpos.le _
    have hratio : (7 + 3 * |T|) * (1 / |T|) ≤ 4 := by
      rw [mul_one_div, div_le_iff₀ habs0]; linarith [hbig]
    calc (q : ℝ) * (1 + ‖(σ : ℂ) + (T : ℂ) * I‖ * (1 + 1 / σ)) * (N : ℝ) ^ (-σ)
        ≤ (q : ℝ) * (7 + 3 * |T|) * (N : ℝ) ^ (-σ) := by
          apply mul_le_mul_of_nonneg_right _ hNσ0
          exact mul_le_mul_of_nonneg_left hfac (by linarith)
      _ ≤ (q : ℝ) * (7 + 3 * |T|) * (1 / |T|) := by
          apply mul_le_mul_of_nonneg_left hNσ
          positivity
      _ = (q : ℝ) * ((7 + 3 * |T|) * (1 / |T|)) := by ring
      _ ≤ (q : ℝ) * 4 := mul_le_mul_of_nonneg_left hratio (by linarith)
      _ = 4 * (q : ℝ) := by ring
  -- the head
  have hhead := vk_char_strip_head_le χ (σ := σ) (T := T) (N := N) hT hσlo hN1 hNle
  -- assemble
  have htri := norm_le_norm_add_norm_sub' (LFunction χ ((σ : ℂ) + (T : ℂ) * I))
    (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * I)))
  have htot : ‖LFunction χ ((σ : ℂ) + (T : ℂ) * I)‖
      ≤ (q : ℝ) * (4050 * (1 + Real.log |T|)) + 4 * (q : ℝ) := by
    linarith [htri, htrunc, herr, hhead]
  refine le_trans htot ?_
  rw [vkStripConst]
  nlinarith [hL1, hq1R]

/-! ## §4 — THE BOX FORM (the shape the probe's region consumes) -/

/-- **STONE A's EXIT — the twisted BOX growth.**  For a nonprincipal `χ mod q` and a height `γ`
above the honest floor `exp(exp 100) ≤ γ − 1`, the single uniform bound

  `‖L(z,χ)‖ ≤ vkStripConst q · (1 + log 3γ)`

holds on the whole box `Re z ∈ [1 − vkTheta(3γ), 2]`, `Im z ∈ [γ − 1, 3γ]` — the box containing
every keep/drop Borel–Carathéodory sphere.  This is EXACTLY the `hgrowth` shape of
`VkTwistRegionProbe.LFunction_region_of_uniform_growth`, and the twisted twin of
`Salt.Vk.pow_uniform_growth`: `vkTheta` is antitone, so `1 − vkTheta(3γ) ≤ Re z` implies the
strip hypothesis at the point's own height, and `log(Im z) ≤ log 3γ` gives the uniform ceiling. -/
theorem vk_char_box_growth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {γ : ℝ} (hγfloor : Real.exp (Real.exp 100) ≤ γ - 1) :
    ∀ z : ℂ, 1 - vkTheta (3 * γ) ≤ z.re → z.re ≤ 2 → γ - 1 ≤ z.im → z.im ≤ 3 * γ →
      ‖LFunction χ z‖ ≤ vkStripConst q * (1 + Real.log (3 * γ)) := by
  intro z hre1 hre2 him1 him2
  have hexp1 : Real.exp 1 < Real.exp (Real.exp 100) := by
    apply Real.exp_lt_exp.mpr
    linarith [Real.add_one_le_exp (100 : ℝ)]
  have hzim : Real.exp (Real.exp 100) ≤ z.im := le_trans hγfloor him1
  have hzimpos : 0 < z.im := lt_of_lt_of_le (Real.exp_pos _) hzim
  have hzabs : |z.im| = z.im := abs_of_pos hzimpos
  have hzime : Real.exp 1 < z.im := lt_of_lt_of_le hexp1 hzim
  -- the strip hypothesis at the point's own height
  have hθz : vkTheta (3 * γ) ≤ vkTheta z.im := vkTheta_anti hzime him2
  have hstrip : 1 - vkTheta |z.im| ≤ z.re := by rw [hzabs]; linarith [hre1, hθz]
  have hgrow := vk_char_strip_growth χ hχ (σ := z.re) (T := z.im)
    (by rw [hzabs]; exact hzim) hstrip hre2
  rw [Complex.re_add_im z] at hgrow
  rw [hzabs] at hgrow
  -- the uniform ceiling
  have hlogle : Real.log z.im ≤ Real.log (3 * γ) := Real.log_le_log hzimpos him2
  have hC0 : (0 : ℝ) ≤ vkStripConst q := by
    have := one_le_vkStripConst (q := q); linarith
  calc ‖LFunction χ z‖ ≤ vkStripConst q * (1 + Real.log z.im) := hgrow
    _ ≤ vkStripConst q * (1 + Real.log (3 * γ)) := by
        apply mul_le_mul_of_nonneg_left _ hC0; linarith

end Salt.MR

end
