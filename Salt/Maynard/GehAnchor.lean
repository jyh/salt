/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehMulti

/-!
# The GEH door — the ANCHORED multiblock combinator (design node N-REPLUMB)

Design freeze: `docs/exploration/s3-a3-design.md`, blocks
"N-REPLUMB — THE ANCHORED MULTIBLOCK RE-CUT" and "N-REPLUMB AMENDMENT 1".

This file lands `pieceObligationU_of_anchored_multiblock`, the re-cut of the
landed global-scale combinator `pieceObligationU_of_multiblock`
(`Salt/Maynard/GehMulti.lean`).  The defect it repairs: the landed combinator
demands every dyadic block be *globally* balanced (`x ≤ 4·Nᵢ·Mᵢ`), which is
jointly unsatisfiable with the Type-II dyadic decomposition (`vP3`'s block
products span `[x^{2/3}, x]`).  The repair: each block carries its OWN anchor
`s i x := 2·N i x·M i x`, and `GEH_min`'s `∀x` is instantiated **at the anchor**
per block.  At the anchor the balance `N·M ≤ s = 2NM ≤ 4NM` is definitional, so
no global-balance conflict can recur.

## The two regimes (design)

The proof splits blocks at the anchor floor `s ≥ x / (log x)^F`:

* **Deep anchors** (`s ≥ floor`): `GEH_min` is applied at `x := s i x` with the
  anchor-spike family `α' y := if y = s i x then α i x else 0` (so its `CoeffAt`
  and `SWAtData` are trivially the block's off the anchor and the block's own
  data ON the anchor).  Two house-caught traps are discharged here:
  - **the anchor-shift `k`-bump** — `CoeffAt` at the anchor needs
    `|α i x n| ≤ τ(n)^{k+1}·(log s)^{k+1}`; we hold `τ(n)^k·(log x)^k` and above
    the floor `log x ≤ 2·log s` (`deep_log_two_mul`), so `(log x)^k ≤ (log s)^{k+1}`
    once `log s ≥ 2^k`.  Hence `GEH_min` is invoked at exponent `k+1`.
  - **the modulus-range absorption** — the outer haircut swallows the deficit
    `s^θ < x^θ`: `⌊x^θ/(log x)^{B+θF+1}⌋ ≤ ⌊s^θ/(log s)^B⌋` (`anchor_modulus_absorb`).
  The SW slot shifts the *right* way (`1/(log x)^A ≤ 1/(log s)^A`, no bump).
* **Shallow anchors** (`s < floor`): routed through the amendment-1 interface
  hypothesis `hshiu` (see its docstring for the frozen final form).

The small-`x` corner (below the `F,k`-threshold where the deep-regime logs hold)
uses the crude universal bound, a finite `sup'` over the corner range — the
anchored analogue of the landed `x = 2` corner.

## `hshiu` — the amendment-1 shallow interface (final form; READ)

`N-SHIU` is designed against `hshiu`.  Its frozen form here (see the theorem
signature) is the **per-shallow-block summed obligation**: for every saving
`A' > 0` there is a haircut `Bsh` and constant `Csh` so that *every* block whose
anchor is shallow (`s i x < x/(log x)^F`) has its summed AP discrepancy
`≤ Csh·x/(log x)^{A'}`.  `F` is a combinator PARAMETER (design liberty: "F may be
a hypothesis parameter"), so `hshiu` is stated `A`-free and quantified over the
saving `A'` — it therefore composes at the inflated saving `A + p` exactly like
the deep regime.  The *intended internal decomposition* for `N-SHIU` (NOT part of
this interface, but its target) is the Shiu-shaped class-moment bound
`Σ_{n≤z,n≡a(q)} |dconv block| ≤ (z/q)·C·log^{pc}x + Sp(x)` summed over the modulus
range (harmonic sum `Σ 1/q ≤ log`, the `z/q` part eaten by `F`, the `Sp(x)` tail
by `Sp(x) ≤ x^{(1-θ)/2}`) — this arithmetic is the analytic debt `hshiu` carries.
-/

open Finset

namespace GehAnchor

/-! ## §1  Real-analysis helpers (the deep-regime log arithmetic) -/

/-- `log t ≤ 2√t` for `t > 0` (loglog domination, via `log √t ≤ √t - 1`). -/
lemma log_le_two_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have h1 : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt (le_of_lt ht)
  have h2 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht)
  rw [h1] at h2
  linarith

/-- `log` is unbounded above along `ℕ`: for every `M` there is a threshold `X0`
past which `log x ≥ M`.  Used to fold the deep-regime log inequalities into a
single corner threshold. -/
lemma exists_log_ge (M : ℝ) : ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x → M ≤ Real.log x := by
  refine ⟨⌈Real.exp M⌉₊ + 1, fun x hx => ?_⟩
  have hxR : Real.exp M ≤ (x : ℝ) := by
    have h1 : Real.exp M ≤ (⌈Real.exp M⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp M⌉₊ + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    push_cast at h2
    linarith
  calc M = Real.log (Real.exp M) := (Real.log_exp M).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos M) hxR

/-- **The deep-regime log bound.**  Above the floor `s ≥ x/(log x)^F` and past the
threshold `16F² ≤ log x`, the anchor's log tracks the outer log:
`log x ≤ 2·log s`.  This is the engine of both the `k`-bump and the deep-regime
`s`-rescaling. -/
lemma deep_log_two_mul {F : ℝ} (hF : 0 ≤ F) {x s : ℕ} (hlx : 1 ≤ Real.log x)
    (hdeep : (x : ℝ) / Real.log x ^ F ≤ (s : ℝ)) (hthr : 16 * F ^ 2 ≤ Real.log x) :
    Real.log x ≤ 2 * Real.log s := by
  have hlxpos : 0 < Real.log x := by linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp only [Nat.cast_zero, Real.log_zero] at hlx; linarith
    · exact_mod_cast h
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hlogFxpos : (0 : ℝ) < Real.log x ^ F := Real.rpow_pos_of_pos hlxpos F
  have hquot_pos : (0 : ℝ) < (x : ℝ) / Real.log x ^ F := div_pos hxpos hlogFxpos
  have hlog_div : Real.log ((x : ℝ) / Real.log x ^ F)
      = Real.log x - F * Real.log (Real.log x) := by
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hlogFxpos), Real.log_rpow hlxpos]
  have hkey : Real.log x - F * Real.log (Real.log x) ≤ Real.log s := by
    have := Real.log_le_log hquot_pos hdeep
    rwa [hlog_div] at this
  have hloglog : Real.log (Real.log x) ≤ 2 * Real.sqrt (Real.log x) :=
    log_le_two_sqrt hlxpos
  have hsqrt_nn : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hmul : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt (le_of_lt hlxpos)
  have h16 : Real.sqrt (16 * F ^ 2) ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt hthr
  have heq : Real.sqrt (16 * F ^ 2) = 4 * F := by
    rw [show (16 : ℝ) * F ^ 2 = (4 * F) ^ 2 by ring, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 4 * F)]
  rw [heq] at h16
  have hcomb : 2 * (F * Real.log (Real.log x)) ≤ Real.log x := by
    have a1 : 2 * (F * Real.log (Real.log x)) ≤ 2 * (F * (2 * Real.sqrt (Real.log x))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      exact mul_le_mul_of_nonneg_left hloglog hF
    have a3 : (4 * F) * Real.sqrt (Real.log x) ≤ Real.log x := by
      calc (4 * F) * Real.sqrt (Real.log x)
          ≤ Real.sqrt (Real.log x) * Real.sqrt (Real.log x) :=
            mul_le_mul_of_nonneg_right h16 hsqrt_nn
        _ = Real.log x := hmul
    nlinarith [a1, a3]
  linarith [hkey, hcomb]

/-- `0 ≤ log m` for every natural `m` (`log 0 = log 1 = 0`, `log ≥ 0` above). -/
lemma log_nat_nonneg (m : ℕ) : (0 : ℝ) ≤ Real.log m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- A nonzero coefficient supported on `Ioc N (2N)` sits at `n ≥ 1`, so `τ(n) ≥ 1`. -/
lemma divisors_card_one_le_of_mem {N : ℕ} {n : ℕ} (hmem : n ∈ Finset.Ioc N (2 * N)) :
    (1 : ℝ) ≤ (n.divisors.card : ℝ) := by
  rw [Finset.mem_Ioc] at hmem
  have hn0 : n ≠ 0 := by omega
  have : n.divisors.Nonempty := ⟨1, Nat.one_mem_divisors.mpr hn0⟩
  exact_mod_cast Finset.card_pos.mpr this

/-! ## §2  The absorption lemma (the heart of the deep regime) -/

/-- **The modulus-range absorption** (relaxed cap `s ≤ 2x`, catch #96).  Above the
anchor floor `s ≥ x/(log x)^F`, the outer haircut `B_out := B + Fθ + 1` swallows
BOTH the `s^θ < x^θ` deficit AND the relaxed-cap factor `log s ≤ 2 log x`:
`⌊x^θ/(log x)^{B+Fθ+1}⌋ ≤ ⌊s^θ/(log s)^B⌋`.  With `s` now up to `2x`, `log s` can
EXCEED `log x` (by up to `log 2`), so the `(log s)^B ≤ (log x)^B` step of the
tight-cap proof FLIPS; the `+1` haircut absorbs the deficit via
`(log s)^B ≤ (2 log x)^B = 2^B (log x)^B ≤ (log x)^{B+1}`, which needs the extra
hypothesis `2^B ≤ log x` (`h2B`, supplied by the combinator's log threshold). -/
lemma anchor_modulus_absorb {θ F B : ℝ} (hθ : 0 ≤ θ) (_hF : 0 ≤ F) (hB : 0 ≤ B)
    {x s : ℕ} (hlx : 1 ≤ Real.log x) (hs2 : (2 : ℝ) ≤ (s : ℝ))
    (hsx : (s : ℝ) ≤ 2 * (x : ℝ)) (h2B : (2 : ℝ) ^ B ≤ Real.log x)
    (hdeep : (x : ℝ) / Real.log x ^ F ≤ (s : ℝ)) :
    ⌊(x : ℝ) ^ θ / Real.log x ^ (B + F * θ + 1)⌋₊ ≤ ⌊(s : ℝ) ^ θ / Real.log s ^ B⌋₊ := by
  have hlxpos : (0 : ℝ) < Real.log x := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hs_pos : (0 : ℝ) < (s : ℝ) := by linarith
  have hls_pos : (0 : ℝ) < Real.log s := Real.log_pos (by linarith)
  have hlogs2x : Real.log s ≤ 2 * Real.log x := by
    have h1 : Real.log s ≤ Real.log (2 * (x : ℝ)) := Real.log_le_log hs_pos hsx
    rw [Real.log_mul two_ne_zero (ne_of_gt hxpos)] at h1
    have hlog2 : Real.log 2 ≤ Real.log x :=
      le_trans (le_of_lt Real.log_two_lt_d9) (le_trans (by norm_num) hlx)
    linarith
  have hlogFxpos : (0 : ℝ) < Real.log x ^ F := Real.rpow_pos_of_pos hlxpos F
  have hquot_pos : (0 : ℝ) < (x : ℝ) / Real.log x ^ F := div_pos hxpos hlogFxpos
  have hxθnn : (0 : ℝ) ≤ (x : ℝ) ^ θ := Real.rpow_nonneg (le_of_lt hxpos) θ
  have hlogsB : (0 : ℝ) < Real.log s ^ B := Real.rpow_pos_of_pos hls_pos B
  have hlogxFθpos : (0 : ℝ) < Real.log x ^ (F * θ) := Real.rpow_pos_of_pos hlxpos (F * θ)
  have hlogxB_nn : (0 : ℝ) ≤ Real.log x ^ B := Real.rpow_nonneg (le_of_lt hlxpos) B
  have hstep1 : (x : ℝ) ^ θ / Real.log x ^ (F * θ) ≤ (s : ℝ) ^ θ := by
    have h := Real.rpow_le_rpow (le_of_lt hquot_pos) hdeep hθ
    rw [Real.div_rpow (le_of_lt hxpos) (le_of_lt hlogFxpos),
      ← Real.rpow_mul (le_of_lt hlxpos) F θ] at h
    exact h
  have e2' : Real.log x ^ (B + F * θ + 1) = Real.log x ^ (F * θ) * Real.log x ^ (B + 1) := by
    rw [← Real.rpow_add hlxpos]; congr 1; ring
  have e3' : Real.log s ^ B ≤ Real.log x ^ (B + 1) := by
    calc Real.log s ^ B ≤ (2 * Real.log x) ^ B :=
          Real.rpow_le_rpow (le_of_lt hls_pos) hlogs2x hB
      _ = 2 ^ B * Real.log x ^ B := by rw [Real.mul_rpow (by norm_num) (le_of_lt hlxpos)]
      _ ≤ Real.log x * Real.log x ^ B := mul_le_mul_of_nonneg_right h2B hlogxB_nn
      _ = Real.log x ^ (B + 1) := by rw [Real.rpow_add hlxpos, Real.rpow_one]; ring
  have hreal : (x : ℝ) ^ θ / Real.log x ^ (B + F * θ + 1)
      ≤ (s : ℝ) ^ θ / Real.log s ^ B := by
    rw [e2', ← div_div]
    calc (x : ℝ) ^ θ / Real.log x ^ (F * θ) / Real.log x ^ (B + 1)
        ≤ (x : ℝ) ^ θ / Real.log x ^ (F * θ) / Real.log s ^ B :=
          div_le_div_of_nonneg_left (div_nonneg hxθnn (le_of_lt hlogxFθpos)) hlogsB e3'
      _ ≤ (s : ℝ) ^ θ / Real.log s ^ B := (div_le_div_iff_of_pos_right hlogsB).mpr hstep1
  exact Nat.floor_le_floor hreal

/-! ## §2a  The anchor-shift `k`-bump (CoeffAt at the anchor) -/

/-- **The anchor-shift `k`-bump.**  A block coefficient bounded by `τ(n)^k·(log x)^k`
(the `CoeffAt`-at-`k` bound at the outer scale) is bounded by
`τ(n)^{k+1}·(log s)^{k+1}` at the anchor, provided the deep-regime logs hold:
`log x ≤ 2·log s` and `2^k ≤ log s`.  This is exactly the `CoeffAt`-at-`(k+1)`
bound the anchor-spike family needs (the `∃ j` / `∀` re-index passes CONSTANT
families, so `GEH_min` is invoked at exponent `k+1`).  `hτ1` supplies `τ(n) ≥ 1`
when the coefficient is nonzero (from the block's support, `n ≥ 1`), needed
because at `k = 0` the bound alone cannot see `n`. -/
lemma kbump {k : ℕ} {x s : ℕ} {c : ℝ} {n : ℕ}
    (hlx0 : 0 ≤ Real.log x) (hlxs : Real.log x ≤ 2 * Real.log s)
    (h2k : (2 : ℝ) ^ k ≤ Real.log s)
    (hτ1 : c ≠ 0 → 1 ≤ (n.divisors.card : ℝ))
    (hc : |c| ≤ (n.divisors.card : ℝ) ^ k * Real.log x ^ k) :
    |c| ≤ (n.divisors.card : ℝ) ^ (k + 1) * Real.log s ^ (k + 1) := by
  have h1k : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hlspos : (0 : ℝ) < Real.log s := by linarith
  have hlogk_s_nn : (0 : ℝ) ≤ Real.log s ^ k := pow_nonneg (le_of_lt hlspos) k
  have hτnn : (0 : ℝ) ≤ (n.divisors.card : ℝ) := by positivity
  rcases eq_or_ne c 0 with h0 | h0
  · subst h0; rw [abs_zero]
    exact mul_nonneg (pow_nonneg hτnn (k + 1)) (pow_nonneg (le_of_lt hlspos) (k + 1))
  · have hτ1' : (1 : ℝ) ≤ (n.divisors.card : ℝ) := hτ1 h0
    have hlog_step : Real.log x ^ k ≤ Real.log s ^ (k + 1) := by
      calc Real.log x ^ k ≤ (2 * Real.log s) ^ k := pow_le_pow_left₀ hlx0 hlxs k
        _ = (2 : ℝ) ^ k * Real.log s ^ k := by rw [mul_pow]
        _ ≤ Real.log s * Real.log s ^ k := mul_le_mul_of_nonneg_right h2k hlogk_s_nn
        _ = Real.log s ^ (k + 1) := by rw [pow_succ']
    have hτ_step : (n.divisors.card : ℝ) ^ k ≤ (n.divisors.card : ℝ) ^ (k + 1) :=
      pow_le_pow_right₀ hτ1' (Nat.le_succ k)
    calc |c| ≤ (n.divisors.card : ℝ) ^ k * Real.log x ^ k := hc
      _ ≤ (n.divisors.card : ℝ) ^ (k + 1) * Real.log s ^ (k + 1) :=
          mul_le_mul hτ_step hlog_step (pow_nonneg hlx0 k) (pow_nonneg hτnn (k + 1))

/-! ## §2b  The anchor-spike family: its `CoeffAt` and `SWAtData` -/

/-- **`CoeffAt` of the anchor-spike family.**  The family `α' y := if y = sx then αb
else 0` (block coefficients ON the anchor `sx`, zero off it) satisfies `CoeffAt` at
exponent `k+1`: off the anchor everything is `0`; on the anchor the block's support
carries over and the `k`-bump upgrades the block's `τ^k·log^k x` bound to
`τ^{k+1}·log^{k+1} sx`. -/
lemma anchorCoeff {k : ℕ} {x sx Nb : ℕ} {αb : ℕ → ℝ}
    (hlx0 : 0 ≤ Real.log x) (hlxs : Real.log x ≤ 2 * Real.log sx)
    (h2k : (2 : ℝ) ^ k ≤ Real.log sx)
    (hsupp : ∀ n, αb n ≠ 0 → n ∈ Finset.Ioc Nb (2 * Nb))
    (hbd : ∀ n, |αb n| ≤ (n.divisors.card : ℝ) ^ k * Real.log x ^ k) :
    CoeffAt (fun y n => if y = sx then αb n else 0)
      (fun y => if y = sx then Nb else 0) (k + 1) := by
  intro x'' n
  refine ⟨fun hne => ?_, ?_⟩
  · by_cases hx'' : x'' = sx
    · subst hx''; simp only [if_true] at hne ⊢; exact hsupp n hne
    · simp only [if_neg hx''] at hne; exact absurd rfl hne
  · by_cases hx'' : x'' = sx
    · subst hx''; simp only [if_true]
      exact kbump hlx0 hlxs h2k (fun hne => divisors_card_one_le_of_mem (hsupp n hne)) (hbd n)
    · simp only [if_neg hx'']; rw [abs_zero]
      exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (log_nat_nonneg x'') _)

/-- **`SWAtData` of the anchor-spike family** (relaxed cap `sx ≤ 2x`, catch #96).
Off the anchor the family (and its scale `Mb`) is `0`, so the SW bound is `0 ≤ 0`.
On the anchor, the block's own `SWAtData` at the OUTER `x` (cutoff `x`) is
transported to cutoff `sx` (the block vanishes above `2Mb ≤ sx` and above
`2Mb ≤ x`, `seqDiscrepancy_truncate`).  With `sx` now up to `2x`, `log sx` can
EXCEED `log x` (by up to `log 2`), so the denominator shift `1/(log x)^{A'} ≤
1/(log sx)^{A'}` no longer holds; instead `(log sx)^{A'} ≤ (2 log x)^{A'} =
2^{A'}(log x)^{A'}`, so the transported bound carries an extra factor `2^{A'}` —
the output SW constant is `2^{A'}·KF A'`.  (The combinator instantiates `GEH_min`
at this inflated `KF`.) -/
lemma anchorSW {j : ℕ} {x sx Mb : ℕ} {βb : ℕ → ℝ} {KF : ℝ → ℝ}
    (hMb_le : 2 * Mb ≤ sx) (hMb_le_x : 2 * Mb ≤ x) (hlogsx0 : 0 < Real.log sx)
    (hlogsx_le_2x : Real.log sx ≤ 2 * Real.log x) (hKFnn : ∀ A', 0 ≤ KF A')
    (hβsupp : ∀ n, βb n ≠ 0 → n ∈ Finset.Ioc Mb (2 * Mb))
    (hSWx : ∀ A' : ℝ, 0 < A' → ∀ r q : ℕ, 0 < r → 0 < q →
      seqDiscrepancy (fun n => if Nat.Coprime n r then βb n else 0) x q
        ≤ KF A' * (((q * r).divisors.card : ℝ)) ^ j * (Mb : ℝ) / Real.log x ^ A') :
    SWAtData (fun y n => if y = sx then βb n else 0) (fun y => if y = sx then Mb else 0) j
      (fun A' => 2 ^ A' * KF A') := by
  intro A' hA' x'' r q _hx''2 hr hq
  by_cases hx'' : x'' = sx
  · subst hx''
    simp only [if_true]
    set tw : ℕ → ℝ := fun n => if Nat.Coprime n r then βb n else 0 with htw
    have hsupp_tw : ∀ n, 2 * Mb < n → tw n = 0 := by
      intro n hn; rw [htw]; by_cases hcop : Nat.Coprime n r
      · simp only [if_pos hcop]; by_contra hne
        have := hβsupp n hne; rw [Finset.mem_Ioc] at this; omega
      · simp only [if_neg hcop]
    have heq : seqDiscrepancy tw x'' q = seqDiscrepancy tw x q := by
      rw [seqDiscrepancy_truncate hsupp_tw x'' q hMb_le,
        seqDiscrepancy_truncate hsupp_tw x q hMb_le_x]
    rw [heq]
    have hlogx0 : (0 : ℝ) < Real.log x := by linarith
    have hnum : (0 : ℝ) ≤ KF A' * ((q * r).divisors.card : ℝ) ^ j * (Mb : ℝ) :=
      mul_nonneg (mul_nonneg (hKFnn A') (pow_nonneg (Nat.cast_nonneg _) _)) (Nat.cast_nonneg _)
    have hLx_pos : (0 : ℝ) < Real.log x ^ A' := Real.rpow_pos_of_pos hlogx0 A'
    have hLsx_pos : (0 : ℝ) < Real.log x'' ^ A' := Real.rpow_pos_of_pos hlogsx0 A'
    have hlogfac : Real.log x'' ^ A' ≤ 2 ^ A' * Real.log x ^ A' := by
      calc Real.log x'' ^ A' ≤ (2 * Real.log x) ^ A' :=
            Real.rpow_le_rpow (le_of_lt hlogsx0) hlogsx_le_2x (le_of_lt hA')
        _ = 2 ^ A' * Real.log x ^ A' := Real.mul_rpow (by norm_num) (le_of_lt hlogx0)
    have hstep : KF A' * ((q * r).divisors.card : ℝ) ^ j * (Mb : ℝ) / Real.log x ^ A'
        ≤ 2 ^ A' * KF A' * ((q * r).divisors.card : ℝ) ^ j * (Mb : ℝ) / Real.log x'' ^ A' := by
      rw [div_le_div_iff₀ hLx_pos hLsx_pos]
      calc (KF A' * ((q * r).divisors.card : ℝ) ^ j * (Mb : ℝ)) * Real.log x'' ^ A'
          ≤ (KF A' * ((q * r).divisors.card : ℝ) ^ j * (Mb : ℝ)) * (2 ^ A' * Real.log x ^ A') :=
            mul_le_mul_of_nonneg_left hlogfac hnum
        _ = 2 ^ A' * KF A' * ((q * r).divisors.card : ℝ) ^ j * (Mb : ℝ) * Real.log x ^ A' := by
            ring
    exact le_trans (hSWx A' hA' r q hr hq) hstep
  · simp only [if_neg hx'']
    have hz : (fun n => if Nat.Coprime n r then (0 : ℝ) else 0) = (fun _ => (0 : ℝ)) := by
      funext n; simp
    rw [hz, seqDiscrepancy_const_zero]
    simp

/-! ## §3  The deep-regime per-block bound (GEH at the anchor + absorption) -/

/-- **The deep-regime per-block bound** (relaxed cap `2·Nb·Mb ≤ 2x`, catch #96).
For a block whose anchor `sx := 2·Nb·Mb` is DEEP (`x/(log x)^F ≤ sx`) and past the
log threshold, `GEH_min` (destructured as `hbound` at exponent `k+1`, saving `A+p`,
haircut `B`, SW data `(j, 2^{·}·KF)`) applied to the anchor-spike family, plus the
absorption lemma and the `s`-rescaling, give the per-block bound at the outer scale.
The relaxed cap (`sx` up to `2x`, resolving the factor-2 boundary vs `hdecomp`)
costs: (i) an extra `2^{A'}` in the SW constant (`log sx` up to `log x + log 2`, so
`GEH_min` is fed `SWAtData … (2^{·}·KF)`); (ii) the `2^B ≤ log x` hypothesis for the
absorption's flipped `(log s)^B` step; (iii) the output constant grows to
`2^{A+p+1}·max C 0` (the `sx ≤ 2x` rescaling doubles).  `2Mb ≤ x` is recovered
threshold-free: the balance forces `Nb ≥ 2`, so `sx = 2Nb·Mb ≥ 4Mb ⟹ 2Mb ≤ x`. -/
lemma deep_perblock {θ ε A p C B F : ℝ} {k j : ℕ} {KF : ℝ → ℝ} {x : ℕ}
    (hθ : 0 ≤ θ) (hε : 0 < ε) (hApos : 0 < A + p) (hF : 0 ≤ F) (hB0 : 0 ≤ B)
    {αb βb : ℕ → ℝ} {Nb Mb : ℕ} {y : ℕ}
    (hαsupp : ∀ n, αb n ≠ 0 → n ∈ Finset.Ioc Nb (2 * Nb))
    (hαbd : ∀ n, |αb n| ≤ (n.divisors.card : ℝ) ^ k * Real.log x ^ k)
    (hβsupp : ∀ n, βb n ≠ 0 → n ∈ Finset.Ioc Mb (2 * Mb))
    (hβbd : ∀ n, |βb n| ≤ (n.divisors.card : ℝ) ^ k * Real.log x ^ k)
    (hSWx : ∀ A' : ℝ, 0 < A' → ∀ r q : ℕ, 0 < r → 0 < q →
      seqDiscrepancy (fun n => if Nat.Coprime n r then βb n else 0) x q
        ≤ KF A' * (((q * r).divisors.card : ℝ)) ^ j * (Mb : ℝ) / Real.log x ^ A')
    (hKFnn : ∀ A' : ℝ, 0 ≤ KF A')
    (hbound : ∀ α' β' : ℕ → ℕ → ℝ, ∀ N' M' : ℕ → ℕ,
      CoeffAt α' N' (k + 1) → CoeffAt β' M' (k + 1) →
        SWAtData β' M' j (fun A' => 2 ^ A' * KF A') →
      ∀ x' yy : ℕ, 2 ≤ x' → yy ≤ 4 * N' x' * M' x' →
        (x' : ℝ) ^ ε ≤ (N' x' : ℝ) → (N' x' : ℝ) ≤ (x' : ℝ) ^ (1 - ε) →
        (x' : ℝ) ^ ε ≤ (M' x' : ℝ) → (M' x' : ℝ) ≤ (x' : ℝ) ^ (1 - ε) →
        N' x' * M' x' ≤ x' → x' ≤ 4 * N' x' * M' x' →
        (∑ q ∈ Finset.Icc 1 ⌊(x' : ℝ) ^ θ / Real.log x' ^ B⌋₊,
            seqDiscrepancy (dconv (α' x') (β' x')) yy q) ≤ C * x' / Real.log x' ^ (A + p))
    (haNlo : ((2 * Nb * Mb : ℕ) : ℝ) ^ ε ≤ (Nb : ℝ))
    (haNhi : (Nb : ℝ) ≤ ((2 * Nb * Mb : ℕ) : ℝ) ^ (1 - ε))
    (haMlo : ((2 * Nb * Mb : ℕ) : ℝ) ^ ε ≤ (Mb : ℝ))
    (haMhi : (Mb : ℝ) ≤ ((2 * Nb * Mb : ℕ) : ℝ) ^ (1 - ε))
    (hsxx : 2 * Nb * Mb ≤ 2 * x)
    (hlogx1 : 1 ≤ Real.log x) (hthrA : 16 * F ^ 2 ≤ Real.log x)
    (hthrB : (2 : ℝ) ^ (k + 1) ≤ Real.log x) (h2B : (2 : ℝ) ^ B ≤ Real.log x)
    (hdeepF : (x : ℝ) / Real.log x ^ F ≤ ((2 * Nb * Mb : ℕ) : ℝ)) :
    (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ (B + F * θ + 1)⌋₊,
        seqDiscrepancy (dconv αb βb) y q)
      ≤ (2 : ℝ) ^ (A + p + 1) * max C 0 * (x : ℝ) / Real.log x ^ (A + p) := by
  set sx : ℕ := 2 * Nb * Mb with hsxdef
  have hlogx0 : (0 : ℝ) < Real.log x := by linarith
  have hlxs : Real.log x ≤ 2 * Real.log sx := deep_log_two_mul hF hlogx1 hdeepF hthrA
  have h1k : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have h2ksx : (2 : ℝ) ^ k ≤ Real.log sx := by
    have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by rw [pow_succ]; ring
    nlinarith [hlxs, hthrB, hpow]
  have hlogsx0 : (0 : ℝ) < Real.log sx := by nlinarith [h2ksx, h1k]
  have hsx2R : (2 : ℝ) ≤ (sx : ℝ) := by
    by_contra h
    push Not at h
    have hle1 : (sx : ℝ) ≤ 1 := by
      have hsx1 : sx ≤ 1 := by
        have h2 : sx < 2 := by exact_mod_cast h
        omega
      exact_mod_cast hsx1
    have : Real.log sx ≤ 0 := Real.log_nonpos (Nat.cast_nonneg sx) hle1
    linarith
  have hsx2 : 2 ≤ sx := by exact_mod_cast hsx2R
  have hsxpos : (0 : ℝ) < (sx : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    rcases Nat.eq_zero_or_pos x with h | h
    · exfalso; subst h; simp only [Nat.cast_zero, Real.log_zero] at hlogx1; linarith
    · exact_mod_cast h
  -- Relaxed-cap log bound: `sx ≤ 2x` gives `log sx ≤ log(2x) ≤ 2 log x` (`log 2 ≤ log x`).
  have hlogsx_le_2x : Real.log sx ≤ 2 * Real.log x := by
    have h2xR : (sx : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hsxx
    have h1 : Real.log sx ≤ Real.log (2 * (x : ℝ)) := Real.log_le_log hsxpos h2xR
    rw [Real.log_mul two_ne_zero (ne_of_gt hxpos)] at h1
    have hlog2 : Real.log 2 ≤ Real.log x :=
      le_trans (le_of_lt Real.log_two_lt_d9) (le_trans (by norm_num) hlogx1)
    linarith
  -- The balance conjunct `sx^ε ≤ Nb` forces `Nb ≥ 2` (since `sx ≥ 2 > 1`, `ε > 0`
  -- give `sx^ε > 1`), hence `sx = 2·Nb·Mb ≥ 4Mb`, so `4Mb ≤ sx ≤ 2x ⟹ 2Mb ≤ x`.
  have hNbR2 : (1 : ℝ) < (Nb : ℝ) := by
    have h1lt : (1 : ℝ) < (sx : ℝ) ^ ε := by
      rw [show (1 : ℝ) = (sx : ℝ) ^ (0 : ℝ) from (Real.rpow_zero _).symm]
      exact Real.rpow_lt_rpow_of_exponent_lt (by linarith : (1 : ℝ) < sx) hε
    linarith [haNlo, h1lt]
  have hNb2 : 2 ≤ Nb := by
    have : 1 < Nb := by exact_mod_cast hNbR2
    omega
  have h2Mb_le_sx : 2 * Mb ≤ sx := by
    rw [hsxdef]; exact Nat.mul_le_mul (show (2 : ℕ) ≤ 2 * Nb by omega) (le_refl Mb)
  have h4Mb_le_sx : 4 * Mb ≤ sx := by
    rw [hsxdef]; exact Nat.mul_le_mul (show (4 : ℕ) ≤ 2 * Nb by omega) (le_refl Mb)
  have h2Mb_le_x : 2 * Mb ≤ x := by omega
  have hCα' := anchorCoeff (x := x) (sx := sx) (Nb := Nb) (αb := αb)
    (le_of_lt hlogx0) hlxs h2ksx hαsupp hαbd
  have hCβ' := anchorCoeff (x := x) (sx := sx) (Nb := Mb) (αb := βb)
    (le_of_lt hlogx0) hlxs h2ksx hβsupp hβbd
  have hSW' := anchorSW (x := x) (sx := sx) (Mb := Mb) (βb := βb) (KF := KF)
    h2Mb_le_sx h2Mb_le_x hlogsx0 hlogsx_le_2x hKFnn hβsupp hSWx
  have haNsx : (if sx = sx then Nb else 0) = Nb := if_pos rfl
  have haMsx : (if sx = sx then Mb else 0) = Mb := if_pos rfl
  have haαsx : (fun n => if sx = sx then αb n else 0) = αb := by funext n; simp
  have haβsx : (fun n => if sx = sx then βb n else 0) = βb := by funext n; simp
  have hgeh := hbound (fun y n => if y = sx then αb n else 0)
    (fun y n => if y = sx then βb n else 0) (fun y => if y = sx then Nb else 0)
    (fun y => if y = sx then Mb else 0) hCα' hCβ' hSW' sx (min y (4 * Nb * Mb)) hsx2
    (by rw [haNsx, haMsx]; exact min_le_right _ _)
    (by rw [haNsx]; exact haNlo) (by rw [haNsx]; exact haNhi)
    (by rw [haMsx]; exact haMlo) (by rw [haMsx]; exact haMhi)
    (by rw [haNsx, haMsx, hsxdef]; exact Nat.mul_le_mul (by omega) (le_refl Mb))
    (by rw [haNsx, haMsx, hsxdef]; exact Nat.mul_le_mul (by omega) (le_refl Mb))
  rw [haαsx, haβsx] at hgeh
  have hsupp_dc : ∀ n, 4 * Nb * Mb < n → dconv αb βb n = 0 :=
    fun n hn => dconv_eq_zero_of_support hαsupp hβsupp hn
  have hcut : ∀ q, seqDiscrepancy (dconv αb βb) y q
      = seqDiscrepancy (dconv αb βb) (min y (4 * Nb * Mb)) q := by
    intro q
    rcases lt_or_ge (4 * Nb * Mb) y with hgt | hle
    · rw [min_eq_right (le_of_lt hgt)]
      exact seqDiscrepancy_truncate hsupp_dc y q (le_of_lt hgt)
    · rw [min_eq_left hle]
  have habs : ⌊(x : ℝ) ^ θ / Real.log x ^ (B + F * θ + 1)⌋₊
      ≤ ⌊(sx : ℝ) ^ θ / Real.log sx ^ B⌋₊ :=
    anchor_modulus_absorb hθ hF hB0 hlogx1 hsx2R
      (by exact_mod_cast hsxx : (sx : ℝ) ≤ 2 * (x : ℝ)) h2B hdeepF
  have hsub : Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ (B + F * θ + 1)⌋₊
      ⊆ Finset.Icc 1 ⌊(sx : ℝ) ^ θ / Real.log sx ^ B⌋₊ := Finset.Icc_subset_Icc_right habs
  have hLsx_pos : (0 : ℝ) < Real.log sx ^ (A + p) := Real.rpow_pos_of_pos hlogsx0 (A + p)
  have hLx_pos : (0 : ℝ) < Real.log x ^ (A + p) := Real.rpow_pos_of_pos hlogx0 (A + p)
  have hmax0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hLx_le : Real.log x ^ (A + p) ≤ 2 ^ (A + p) * Real.log sx ^ (A + p) := by
    have h1 : Real.log x ^ (A + p) ≤ (2 * Real.log sx) ^ (A + p) :=
      Real.rpow_le_rpow (le_of_lt hlogx0) hlxs (le_of_lt hApos)
    rwa [Real.mul_rpow (by norm_num) (le_of_lt hlogsx0)] at h1
  have hsx_le_2xR : (sx : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hsxx
  have h2exp : (2 : ℝ) ^ (A + p + 1) = 2 ^ (A + p) * 2 := by
    rw [show A + p + 1 = (A + p) + 1 by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_one]
  -- With `sx ≤ 2x` (not `sx ≤ x`) the rescaling picks up an extra factor 2, so the
  -- per-block constant is `2^{A+p+1}·max C 0` (was `2^{A+p}·max C 0`).
  have hscaling : C * (sx : ℝ) / Real.log sx ^ (A + p)
      ≤ 2 ^ (A + p + 1) * max C 0 * (x : ℝ) / Real.log x ^ (A + p) := by
    calc C * (sx : ℝ) / Real.log sx ^ (A + p)
        ≤ max C 0 * (sx : ℝ) / Real.log sx ^ (A + p) :=
          (div_le_div_iff_of_pos_right hLsx_pos).mpr
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
      _ ≤ max C 0 * (2 * (x : ℝ)) / Real.log sx ^ (A + p) :=
          (div_le_div_iff_of_pos_right hLsx_pos).mpr
            (mul_le_mul_of_nonneg_left hsx_le_2xR hmax0)
      _ ≤ 2 ^ (A + p + 1) * max C 0 * (x : ℝ) / Real.log x ^ (A + p) := by
          rw [div_le_div_iff₀ hLsx_pos hLx_pos]
          calc max C 0 * (2 * (x : ℝ)) * Real.log x ^ (A + p)
              ≤ max C 0 * (2 * (x : ℝ)) * (2 ^ (A + p) * Real.log sx ^ (A + p)) :=
                mul_le_mul_of_nonneg_left hLx_le
                  (mul_nonneg hmax0 (by positivity))
            _ = 2 ^ (A + p + 1) * max C 0 * (x : ℝ) * Real.log sx ^ (A + p) := by
                rw [h2exp]; ring
  calc (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ (B + F * θ + 1)⌋₊,
          seqDiscrepancy (dconv αb βb) y q)
      = ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ (B + F * θ + 1)⌋₊,
          seqDiscrepancy (dconv αb βb) (min y (4 * Nb * Mb)) q :=
        Finset.sum_congr rfl (fun q _ => hcut q)
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊(sx : ℝ) ^ θ / Real.log sx ^ B⌋₊,
          seqDiscrepancy (dconv αb βb) (min y (4 * Nb * Mb)) q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => seqDiscrepancy_nonneg _ _ _)
    _ ≤ C * (sx : ℝ) / Real.log sx ^ (A + p) := hgeh
    _ ≤ (2 : ℝ) ^ (A + p + 1) * max C 0 * (x : ℝ) / Real.log x ^ (A + p) := hscaling

/-! ## §4  The anchored multiblock combinator -/

/-- **The anchored multiblock combinator** (`N-REPLUMB`).  Like the landed
`pieceObligationU_of_multiblock`, but each block carries its OWN anchor
`s i x := 2·N i x·M i x` and `GEH_min` is instantiated at that anchor — deleting the
provably-unsatisfiable global-balance demand.  `hanch` replaces `hwin` (own-anchor
balance, cap `s ≤ 2x`, NO global `x ≤ 4NM`).  **Catch #96 (relaxed anchor cap):**
the cap is `2·N·M ≤ 2x` (was `≤ x`), TRUE for every nonzero double-dyadic block
(support ⟹ `N·M < x`) whereas `≤ x` was jointly unsatisfiable with `hdecomp_double`
at the top anti-diagonal `N·M ∈ [x/2, x)`.  The relaxation costs bounded constants:
`GEH_min` is fed the `2^{·}`-inflated `KF` (the `log sx ≤ log x + log 2` SW shift),
the threshold carries `2^B ≤ log x` (the absorption's flipped step), and the
per-block constant is `2^{A+p+1}·max C 0`.  `hshiu` is the amendment-1
shallow interface (see the module docstring): shallow blocks (`s < x/(log x)^{F A'}`)
are routed through it; deep blocks are discharged by `deep_perblock`
(`GEH_min`-at-anchor + `k`-bump + absorption).

**Catch-#54 replumb (2026-07-18):** the shallow floor is `F : ℝ → ℝ`, a FUNCTION of
the saving — a fixed `F : ℝ` caps the honest Shiu bound at saving `F − 3` while
`PieceObligationU` quantifies over all savings `A`, making the fixed-`F` `hshiu`
unprovable (N-HDOM re-discovery).  Every use of `F` sits inside the `intro A` scope,
so the combinator reads the floor at `F (A + p)`; the honest instantiation is
`F A' := A' + 3` (see `Salt.Maynard.hshiu_wire_sharp`).  `hKFnn`
asks the SW constant be nonnegative (the honest `KF` always is). -/
theorem pieceObligationU_of_anchored_multiblock {θ ε : ℝ}
    (hθ : 0 ≤ θ) (hε : 0 < ε) (F : ℝ → ℝ) (hF : ∀ A' : ℝ, 0 ≤ F A')
    (hGEH : GEH_min θ) (w : ℕ → ℕ → ℝ)
    (k j : ℕ) (KF : ℝ → ℝ) (hKFnn : ∀ A' : ℝ, 0 ≤ KF A')
    (p D : ℝ) (hp : 0 ≤ p) (_hD : 0 ≤ D)
    (m : ℕ → ℕ) (α β : ℕ → ℕ → ℕ → ℝ) (N M : ℕ → ℕ → ℕ)
    (hα : ∀ i, CoeffAt (α i) (N i) k)
    (hβ : ∀ i, CoeffAt (β i) (M i) k)
    (hSW : ∀ i, SWAtData (β i) (M i) j KF)
    (hanch : ∀ x, 3 ≤ x → ∀ i, i < m x →
      ((2 * N i x * M i x : ℕ) : ℝ) ^ ε ≤ (N i x : ℝ) ∧
      (N i x : ℝ) ≤ ((2 * N i x * M i x : ℕ) : ℝ) ^ (1 - ε) ∧
      ((2 * N i x * M i x : ℕ) : ℝ) ^ ε ≤ (M i x : ℝ) ∧
      (M i x : ℝ) ≤ ((2 * N i x * M i x : ℕ) : ℝ) ^ (1 - ε) ∧
      2 * N i x * M i x ≤ 2 * x)
    (hcount : ∀ x, 3 ≤ x → (m x : ℝ) ≤ D * Real.log x ^ p)
    (hdecomp : ∀ x, 3 ≤ x → ∀ y q : ℕ, y ≤ x →
      seqDiscrepancy (w x) y q
        ≤ ∑ i ∈ Finset.range (m x), seqDiscrepancy (dconv (α i x) (β i x)) y q)
    (hshiu : ∀ A' : ℝ, 0 < A' → ∃ Bsh Csh : ℝ, 0 ≤ Bsh ∧ ∀ x, 3 ≤ x → ∀ i, i < m x →
      ((2 * N i x * M i x : ℕ) : ℝ) < (x : ℝ) / Real.log x ^ F A' → ∀ y : ℕ, y ≤ x →
        (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ Bsh⌋₊,
            seqDiscrepancy (dconv (α i x) (β i x)) y q) ≤ Csh * (x : ℝ) / Real.log x ^ A') :
    PieceObligationU θ w := by
  intro A hA
  have hApos : 0 < A + p := by linarith
  -- The anchor SW transport (relaxed cap, catch #96) inflates `KF` by `2^{A'}`, so
  -- `GEH_min` is instantiated at `fun A' => 2^A' * KF A'`.
  obtain ⟨B, C, hB0, hbound⟩ := hGEH ε (A + p) hε hApos (k + 1) j (fun A' => 2 ^ A' * KF A')
  obtain ⟨Bsh, Csh, hBsh0, hshiubd⟩ := hshiu (A + p) hApos
  -- `(2:ℝ)^B ≤ log x` added to the threshold: the absorption's flipped `(log s)^B`
  -- step (relaxed cap) needs it.
  obtain ⟨X0, hX0⟩ := exists_log_ge
    (max (max (max (16 * F (A + p) ^ 2) ((2 : ℝ) ^ (k + 1))) ((2 : ℝ) ^ B)) 1)
  set Bout : ℝ := max (B + F (A + p) * θ + 1) Bsh with hBout
  have hBout0 : 0 ≤ Bout := le_trans hBsh0 (le_max_right _ _)
  set XC : ℕ := max X0 3 with hXC
  set Cblk : ℝ := max ((2 : ℝ) ^ (A + p + 1) * max C 0) Csh with hCblk
  have hne_ico : (Finset.Ico 2 XC).Nonempty :=
    Finset.nonempty_Ico.mpr (by omega)
  set cornerC : ℝ := (Finset.Ico 2 XC).sup' hne_ico (fun x' =>
    (⌊(x' : ℝ) ^ θ / Real.log x' ^ Bout⌋₊ : ℝ) *
      (2 * ∑ n ∈ Finset.Icc 1 x', |w x' n|) * Real.log x' ^ A / (x' : ℝ)) with hcornerC
  refine ⟨Bout, max (D * Cblk) cornerC, hBout0, fun x y hx hyx => ?_⟩
  rcases lt_or_ge x XC with hlt | hxge
  · -- Corner: 2 ≤ x < XC, crude universal bound folded into `cornerC`.
    have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hx1R : (1 : ℝ) < (x : ℝ) := by linarith
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    have hlogxpos : 0 < Real.log x := Real.log_pos hx1R
    have hlogApos : (0 : ℝ) < Real.log x ^ A := Real.rpow_pos_of_pos hlogxpos A
    set Q : ℕ := ⌊(x : ℝ) ^ θ / Real.log x ^ Bout⌋₊ with hQ
    have hterm : ∀ q : ℕ, seqDiscrepancy (w x) y q ≤ 2 * ∑ n ∈ Finset.Icc 1 x, |w x n| := by
      intro q
      exact (seqDiscrepancy_le_two_mul_sum_abs (w x) y q).trans
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right hyx) (fun n _ _ => abs_nonneg _)) (by norm_num))
    have hcrude : (∑ q ∈ Finset.Icc 1 Q, seqDiscrepancy (w x) y q)
        ≤ (Q : ℝ) * (2 * ∑ n ∈ Finset.Icc 1 x, |w x n|) := by
      refine (Finset.sum_le_sum (fun q _ => hterm q)).trans (le_of_eq ?_)
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast [Nat.add_sub_cancel]; ring
    have hmem : x ∈ Finset.Ico 2 XC := Finset.mem_Ico.mpr ⟨hx, hlt⟩
    have hgle : (Q : ℝ) * (2 * ∑ n ∈ Finset.Icc 1 x, |w x n|) * Real.log x ^ A / (x : ℝ)
        ≤ cornerC := by
      rw [hcornerC, hQ]
      exact Finset.le_sup' (fun x' : ℕ => (⌊(x' : ℝ) ^ θ / Real.log x' ^ Bout⌋₊ : ℝ) *
        (2 * ∑ n ∈ Finset.Icc 1 x', |w x' n|) * Real.log x' ^ A / (x' : ℝ)) hmem
    refine hcrude.trans ?_
    have hid : (Q : ℝ) * (2 * ∑ n ∈ Finset.Icc 1 x, |w x n|)
        = ((Q : ℝ) * (2 * ∑ n ∈ Finset.Icc 1 x, |w x n|) * Real.log x ^ A / (x : ℝ))
          * ((x : ℝ) / Real.log x ^ A) := by
      field_simp
    rw [hid]
    calc ((Q : ℝ) * (2 * ∑ n ∈ Finset.Icc 1 x, |w x n|) * Real.log x ^ A / (x : ℝ))
          * ((x : ℝ) / Real.log x ^ A)
        ≤ cornerC * ((x : ℝ) / Real.log x ^ A) :=
          mul_le_mul_of_nonneg_right hgle (div_nonneg (le_of_lt hxpos) (le_of_lt hlogApos))
      _ = cornerC * (x : ℝ) / Real.log x ^ A := by ring
      _ ≤ max (D * Cblk) cornerC * (x : ℝ) / Real.log x ^ A :=
          (div_le_div_iff_of_pos_right hlogApos).mpr
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hxpos))
  · -- Main regime: x ≥ XC ≥ 3, per-block deep/shallow, block-count absorbed at A+p.
    have hge3 : 3 ≤ x := le_trans (le_max_right X0 3) hxge
    have hX0x : X0 ≤ x := le_trans (le_max_left X0 3) hxge
    have hlogM :
        max (max (max (16 * F (A + p) ^ 2) ((2 : ℝ) ^ (k + 1))) ((2 : ℝ) ^ B)) 1 ≤ Real.log x :=
      hX0 x hX0x
    have hlogx1 : 1 ≤ Real.log x := le_trans (le_max_right _ 1) hlogM
    have hthrA : 16 * F (A + p) ^ 2 ≤ Real.log x :=
      le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ 1)) hlogM
    have hthrB : (2 : ℝ) ^ (k + 1) ≤ Real.log x :=
      le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ 1)) hlogM
    have hthrB2 : (2 : ℝ) ^ B ≤ Real.log x :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ 1)) hlogM
    have hxR3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hge3
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    have hx0 : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
    have hlogxpos : 0 < Real.log x := by linarith
    have hlogApos : (0 : ℝ) < Real.log x ^ A := Real.rpow_pos_of_pos hlogxpos A
    have hlogppos : (0 : ℝ) < Real.log x ^ p := Real.rpow_pos_of_pos hlogxpos p
    have hlogA'pos : (0 : ℝ) < Real.log x ^ (A + p) := Real.rpow_pos_of_pos hlogxpos (A + p)
    have hsplit : Real.log x ^ (A + p) = Real.log x ^ A * Real.log x ^ p :=
      Real.rpow_add hlogxpos A p
    have hCblk0 : (0 : ℝ) ≤ Cblk :=
      le_trans (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (le_max_right _ _)) (le_max_left _ _)
    have hxθnn : (0 : ℝ) ≤ (x : ℝ) ^ θ := Real.rpow_nonneg hx0 θ
    have mkSub : ∀ Bi : ℝ, Bi ≤ Bout →
        Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ Bout⌋₊
          ⊆ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ Bi⌋₊ := by
      intro Bi hBi
      apply Finset.Icc_subset_Icc_right
      apply Nat.floor_le_floor
      exact div_le_div_of_nonneg_left hxθnn (Real.rpow_pos_of_pos hlogxpos Bi)
        (Real.rpow_le_rpow_of_exponent_le hlogx1 hBi)
    have perBlock : ∀ i ∈ Finset.range (m x),
        (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ Bout⌋₊,
            seqDiscrepancy (dconv (α i x) (β i x)) y q)
          ≤ Cblk * (x : ℝ) / Real.log x ^ (A + p) := by
      intro i hi
      have hi' : i < m x := Finset.mem_range.mp hi
      obtain ⟨ha1, ha2, ha3, ha4, ha5⟩ := hanch x hge3 i hi'
      rcases lt_or_ge ((2 * N i x * M i x : ℕ) : ℝ) ((x : ℝ) / Real.log x ^ F (A + p))
        with hshallow | hdeep
      · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
          (mkSub Bsh (le_max_right _ _)) (fun q _ _ => seqDiscrepancy_nonneg _ _ _))
          ((hshiubd x hge3 i hi' hshallow y hyx).trans ?_)
        exact (div_le_div_iff_of_pos_right hlogA'pos).mpr
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hx0)
      · have hdp := deep_perblock (y := y) hθ hε hApos (hF (A + p)) hB0
          (fun n => (hα i x n).1) (fun n => (hα i x n).2)
          (fun n => (hβ i x n).1) (fun n => (hβ i x n).2)
          (fun A' hA'' r q hr hq => (hSW i) A' hA'' x r q (by omega) hr hq)
          hKFnn hbound ha1 ha2 ha3 ha4 ha5 hlogx1 hthrA hthrB hthrB2 hdeep
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
          (mkSub (B + F (A + p) * θ + 1) (le_max_left _ _))
          (fun q _ _ => seqDiscrepancy_nonneg _ _ _))
          (hdp.trans ?_)
        exact (div_le_div_iff_of_pos_right hlogA'pos).mpr
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0)
    calc (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ Bout⌋₊, seqDiscrepancy (w x) y q)
        ≤ ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ Bout⌋₊,
            ∑ i ∈ Finset.range (m x), seqDiscrepancy (dconv (α i x) (β i x)) y q :=
          Finset.sum_le_sum (fun q _ => hdecomp x hge3 y q hyx)
      _ = ∑ i ∈ Finset.range (m x),
            ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ Bout⌋₊,
              seqDiscrepancy (dconv (α i x) (β i x)) y q := Finset.sum_comm
      _ ≤ ∑ i ∈ Finset.range (m x), Cblk * (x : ℝ) / Real.log x ^ (A + p) :=
          Finset.sum_le_sum perBlock
      _ = (m x : ℝ) * (Cblk * (x : ℝ) / Real.log x ^ (A + p)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (D * Real.log x ^ p) * (Cblk * (x : ℝ) / Real.log x ^ (A + p)) :=
          mul_le_mul_of_nonneg_right (hcount x hge3)
            (div_nonneg (mul_nonneg hCblk0 hx0) (le_of_lt hlogA'pos))
      _ = D * Cblk * (x : ℝ) / Real.log x ^ A := by
          rw [hsplit]; field_simp [hlogApos.ne', hlogppos.ne']
      _ ≤ max (D * Cblk) cornerC * (x : ℝ) / Real.log x ^ A :=
          (div_le_div_iff_of_pos_right hlogApos).mpr
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0)

end GehAnchor


