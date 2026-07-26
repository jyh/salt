/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetThin
import Salt.MR.VdCSocket

/-!
# USetThinTS — the `𝒯_S` branch of `§8.3`'s `hU` (U-5)

MR §8.3 Step 4 splits the well-spaced set `𝒯 ⊆ 𝒰` at the size of the prime block factor
`Q_{j,H}(1+it)`, the two branches swapping *which* factor is pointwise small.  This file
lands the **`𝒯_S` branch** — the points where the prime factor is small (`‖Q_{j,H}‖ ≤ ε`;
MR's `ε = (log X)^{−100}`) — where the co-factor's mean square is priced by **Lemma 9
(Halász for integers)** and the `𝒰`-thinness is *consumed*: `|𝒯|·√T ≪ X^{1−2η}`.

## The mechanism, in the order the stones land

1. **The co-factor is a Dirichlet polynomial** (`ramRcoeff`, `ramR_eq_spoly`).  `ramR` is
   `spoly` on the masked, Ramaré-weighted coefficients `b_m·(ω(m;P,Q)+1)⁻¹`.  The length
   parameter is **`M`, not `N`** (in-statement, law #253): the co-factor range
   `ramRrange H N X j` sits at `m ≍ X·e^{−j/H}`, so pricing it at the full dyadic `N ≍ 2X`
   throws away exactly the `e^{j/H} ≍ p` that makes `M·Σ_m ‖r_m‖²/m² ≍ 1`.  Every statement
   takes any `M` with `ramRrange H N X j ⊆ [1,M]`.
2. **Lemma 9 on the co-factor** (`ramR_sq_sum_le`), through the landed unconditional
   `halasz_integers_unconditional_const` (`Cvdc = 640`, constant `2564`).  **The `−𝒯` sign
   bridge re-arms here** (catch #B, `USetThin.primeBlockPoly_eq_dpoly`): `spoly N a t =
   dpoly N (aₙ/n) (−t)`, so Lemma 9 is fed the **negated** ordinate set `𝒯.image (−·)`;
   `WellSpaced` and `⊆ [−T,T]` are both `t ↦ −t` stable, and the cardinality is preserved.
3. **The branch's pointwise gain** (`norm_ramMain_sq_le_of_small`): `‖Q·R‖² ≤ ε²·‖R‖²` on
   `TsetSmall`.  One inequality, no analysis.
4. **The thinness arithmetic** (`Uset_thin_alpha`, `thin_sqrt_kill`, `Uset_thin_sqrt_kill`):
   `USetThin.Uset_thin`'s count, repackaged at the `α_J` gate.  Lemma 8's exponent
   `2·log V/log P_Jb` is bounded by `2α` through the in-statement gate
   `log V ≤ α·log P_Jb` (at the ratified pin `δ := P_J^{−α_J}` and `V := K₀/δ` this reads
   `α = α_J + log K₀/log P_J`, the consumer's `o(1)` inflation of `α_J`).  Then
   `α ≤ 1/4 − η` **plus MR Step 0's `T ≤ X`** give
   `|𝒯|·√T ≤ W·T^{2α+1/2} ≤ W·T^{1−2η} ≤ W·X^{1−2η}` — this is where the thinness is spent.
5. **The exit** (`uset_TS_branch`, `uset_TS_branch_meanvalue`).

## The `Q_J²` union factor — the T-FREE absorption route (as-stated)

`Uset_thin`'s count carries `card (dyadicPairs P_Jb Q_Jb) ≤ (Q_Jb+1)²` (the D1 repair's true
cost).  It is absorbed **T-freely**, from the definition of `J` alone:
`dyadicPairs_card_le_exp` says `Q_J + 1 ≤ exp L ⟹ card 𝒫 ≤ exp (2L)`, and at
`L = (log X)^{1/2}` (the `J`-definition's own ceiling) that is `exp(2(log X)^{1/2}) =
X^{o(1)}`.  No `T` appears in that route, and none may: coupling `Q_J²` to `T` would eat the
`η` that the `α_J ≤ 1/4 − η` gate is paying for.  The factor rides inside `thinBundle`, which
is an explicit expression — never absorbed silently.

## Conventions checked byte-for-byte

* `ramQblock` is **half-open in `p`** (`e^{j/H} ≤ p < e^{(j+1)/H}`) and `ramRrange` is
  **closed in `m`** (`X e^{−j/H} ≤ m ≤ 2X e^{−j/H}`) — `RamareWindows.lean`:56/64.  Nothing
  here depends on either convention: the co-factor bridge goes through
  `ramRrange ⊆ Finset.Icc 1 M` only, and the prime factor is an opaque `ramQ` norm.
* `WellSpaced` (LargeValues:48) is `∀ t ∈ 𝒯, ∀ r ∈ 𝒯, t ≠ r → 1 ≤ |t − r|`; `Set.Icc (-T) T`
  is the closed window Lemma 9 wants.
* `Uset` (Decomp:231) is the *no small index* set; `Uset_thin`'s `hU` is consumed verbatim.

## What is NOT here

The `𝒯_L` branch (U-8, `USetThinTL.lean`), the balance (U-9), and the `Q_J² = X^{o(1)}` /
`W·X^{1−2η} ≤ M` numerics — all consumer-side, all named as hypotheses.

Source pins (D5): MR arXiv v4 (`1501.04585v4`) pp. 8, 15–16 (Lemma 8), 16–17 (Lemma 9),
19–20 (Lemma 12), 27–29 (§8.3); the scope freeze `docs/exploration/hu-scope-0724.md`
and `docs/exploration/hsup-design.md` ⟦V4⟧.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the Ramaré co-factor as a `σ = 1` Dirichlet polynomial -/

/-- **The co-factor coefficients.**  `ramR H N X P Q j b` is the `σ = 1` Dirichlet polynomial
of `m ↦ b m · (ω(m;P,Q)+1)⁻¹` masked to the co-factor range `ramRrange H N X j`. -/
noncomputable def ramRcoeff (H : ℝ) (N X P Q j : ℕ) (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  if m ∈ ramRrange H N X j then b m * ((blockOmega P Q m : ℂ) + 1)⁻¹ else 0

lemma ramRcoeff_of_notMem (H : ℝ) (N X P Q j : ℕ) (b : ℕ → ℂ) {m : ℕ}
    (hm : m ∉ ramRrange H N X j) : ramRcoeff H N X P Q j b m = 0 := by
  rw [ramRcoeff, if_neg hm]

lemma ramRrange_subset_Icc (H : ℝ) (N X j : ℕ) : ramRrange H N X j ⊆ Finset.Icc 1 N := by
  unfold ramRrange
  exact Finset.filter_subset _ _

/-- **The co-factor bridge.**  `ramR = spoly M (ramRcoeff)` for *any* length `M` containing
the co-factor range.  The sharp `M` (the consumer's `⌊2X e^{−j/H}⌋`) is what keeps the
`𝒯_S` grade: pricing at the dyadic `N` would lose the factor `e^{j/H}`. -/
lemma ramR_eq_spoly (H : ℝ) (N X P Q j M : ℕ) (b : ℕ → ℂ)
    (hM : ramRrange H N X j ⊆ Finset.Icc 1 M) (t : ℝ) :
    ramR H N X P Q j b t = spoly M (ramRcoeff H N X P Q j b) t := by
  rw [ramR, spoly,
    ← Finset.sum_subset hM (fun m _ hm => by rw [ramRcoeff_of_notMem H N X P Q j b hm, zero_div])]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [ramRcoeff, if_pos hm, div_mul_eq_mul_div]

/-! ## §2 — Lemma 9 (Halász for integers) on the co-factor, through the `−𝒯` sign bridge -/

/-- The negation of a well-spaced set is well-spaced (`|(-t) − (-r)| = |t − r|`). -/
lemma wellSpaced_neg_image {𝒮 : Finset ℝ} (hws : WellSpaced 𝒮) :
    WellSpaced (𝒮.image (fun t => -t)) := by
  intro s hs r hr hne
  rw [Finset.mem_image] at hs hr
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨u, hu, rfl⟩ := hr
  have htu : t ≠ u := fun h => hne (by rw [h])
  have h := hws t ht u hu htu
  rwa [show -t - -u = -(t - u) by ring, abs_neg]

/-- `Set.Icc (-T) T` is `t ↦ −t` stable. -/
lemma neg_image_subset_Icc {𝒮 : Finset ℝ} {T : ℝ} (hsub : ∀ t ∈ 𝒮, t ∈ Set.Icc (-T) T) :
    ∀ s ∈ 𝒮.image (fun t => -t), s ∈ Set.Icc (-T) T := by
  intro s hs
  rw [Finset.mem_image] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have h := Set.mem_Icc.mp (hsub t ht)
  exact Set.mem_Icc.mpr ⟨by linarith [h.2], by linarith [h.1]⟩

/-- **The co-factor mean square on a well-spaced set (MR Lemma 9).**  Through
`halasz_integers_unconditional_const` (`Cvdc = 640`, so the constant is `4·641 = 2564`), fed
the **negated** ordinate set: `spoly M a t = dpoly M (aₘ/m) (−t)` is the `−𝒯` sign bridge
(catch #B), and `WellSpaced`/`⊆ [−T,T]`/`card` are all `t ↦ −t` stable.

The `|𝒮|·√T` term is where the `𝒰`-thinness is spent (§4). -/
theorem ramR_sq_sum_le (H : ℝ) (N X P Q j M : ℕ) (b : ℕ → ℂ)
    (hM : ramRrange H N X j ⊆ Finset.Icc 1 M)
    (T : ℝ) (hT : 1 ≤ T) (𝒮 : Finset ℝ) (hws : WellSpaced 𝒮)
    (hsub : ∀ t ∈ 𝒮, t ∈ Set.Icc (-T) T) :
    ∑ t ∈ 𝒮, ‖ramR H N X P Q j b t‖ ^ 2
      ≤ 2564 * ((M : ℝ) + (𝒮.card : ℝ) * Real.sqrt T) * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  classical
  have hcard : (𝒮.image (fun t => -t)).card = 𝒮.card :=
    Finset.card_image_of_injective _ neg_injective
  have h9 := halasz_integers_unconditional_const M
    (fun n => ramRcoeff H N X P Q j b n / (n : ℂ)) T hT (𝒮.image (fun t => -t))
    (wellSpaced_neg_image hws) (neg_image_subset_Icc hsub)
  rw [hcard] at h9
  have himg : ∑ s ∈ 𝒮.image (fun t => -t),
        ‖dpoly M (fun n => ramRcoeff H N X P Q j b n / (n : ℂ)) s‖ ^ 2
      = ∑ t ∈ 𝒮, ‖dpoly M (fun n => ramRcoeff H N X P Q j b n / (n : ℂ)) (-t)‖ ^ 2 :=
    Finset.sum_image (fun x _ y _ h => neg_injective h)
  have hlhs : ∑ t ∈ 𝒮, ‖ramR H N X P Q j b t‖ ^ 2
      = ∑ t ∈ 𝒮, ‖dpoly M (fun n => ramRcoeff H N X P Q j b n / (n : ℂ)) (-t)‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [ramR_eq_spoly H N X P Q j M b hM t, spoly_eq_dpoly]
  have hmass : ∑ n ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b n / (n : ℂ)‖ ^ 2
      = ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [norm_div, Complex.norm_natCast, div_pow]
  rw [hlhs, ← himg]
  rw [hmass] at h9
  exact h9

/-! ## §3 — the small-`‖Q‖` branch: the pointwise gain -/

/-- **`𝒯_S`** (MR §8.3 Step 4): the points of a well-spaced `𝒯` where the *prime* block
factor is small.  MR's threshold is `ε = (log X)^{−100}`; it is a parameter here. -/
noncomputable def TsetSmall (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (ε : ℝ) (𝒯 : Finset ℝ) :
    Finset ℝ :=
  𝒯.filter (fun t => ‖ramQ H P Q j c t‖ ≤ ε)

lemma mem_TsetSmall {H : ℝ} {P Q j : ℕ} {c : ℕ → ℂ} {ε : ℝ} {𝒯 : Finset ℝ} {t : ℝ} :
    t ∈ TsetSmall H P Q j c ε 𝒯 ↔ t ∈ 𝒯 ∧ ‖ramQ H P Q j c t‖ ≤ ε := by
  rw [TsetSmall, Finset.mem_filter]

lemma TsetSmall_subset (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (ε : ℝ) (𝒯 : Finset ℝ) :
    TsetSmall H P Q j c ε 𝒯 ⊆ 𝒯 := Finset.filter_subset _ _

/-- **The branch's pointwise gain.**  On `𝒯_S` the main block polynomial `Q_{j,H}·R_{j,H}`
loses `ε²` to the small prime factor; nothing else happens pointwise (the analysis is all in
`ramR_sq_sum_le`). -/
lemma norm_ramMain_sq_le_of_small (H : ℝ) (N X P Q j : ℕ) (b c : ℕ → ℂ) (ε t : ℝ)
    (hsmall : ‖ramQ H P Q j c t‖ ≤ ε) :
    ‖ramMain H N X P Q b c j t‖ ^ 2 ≤ ε ^ 2 * ‖ramR H N X P Q j b t‖ ^ 2 := by
  rw [ramMain, norm_mul, mul_pow]
  have hq : ‖ramQ H P Q j c t‖ ^ 2 ≤ ε ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hsmall 2
  exact mul_le_mul_of_nonneg_right hq (sq_nonneg _)

/-- **The `𝒯_S` branch mean square** (the branch bound before the thinness is spent):
`Σ_{t∈𝒯_S} ‖Q_{j,H}R_{j,H}(1+it)‖² ≤ ε²·(Lemma 9 at length `M` on `𝒯`)`.  The count in the
Halász term is `|𝒯|` (not `|𝒯_S|`) — monotone, and it is `|𝒯|` that `Uset_thin` bounds. -/
theorem TS_branch_meansq (H : ℝ) (N X P Q j M : ℕ) (b c : ℕ → ℂ)
    (hM : ramRrange H N X j ⊆ Finset.Icc 1 M) (ε : ℝ)
    (T : ℝ) (hT : 1 ≤ T) (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯)
    (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) :
    ∑ t ∈ TsetSmall H P Q j c ε 𝒯, ‖ramMain H N X P Q b c j t‖ ^ 2
      ≤ ε ^ 2 * (2564 * ((M : ℝ) + (𝒯.card : ℝ) * Real.sqrt T) * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) := by
  have hsubT : TsetSmall H P Q j c ε 𝒯 ⊆ 𝒯 := TsetSmall_subset H P Q j c ε 𝒯
  have h1 : ∑ t ∈ TsetSmall H P Q j c ε 𝒯, ‖ramMain H N X P Q b c j t‖ ^ 2
      ≤ ∑ t ∈ TsetSmall H P Q j c ε 𝒯, ε ^ 2 * ‖ramR H N X P Q j b t‖ ^ 2 :=
    Finset.sum_le_sum (fun t ht =>
      norm_ramMain_sq_le_of_small H N X P Q j b c ε t (mem_TsetSmall.mp ht).2)
  rw [← Finset.mul_sum] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg ε))
  have h9 := ramR_sq_sum_le H N X P Q j M b hM T hT (TsetSmall H P Q j c ε 𝒯)
    (wellSpaced_of_subset hsubT hws) (fun t ht => hsub t (hsubT ht))
  refine h9.trans ?_
  have hcard : ((TsetSmall H P Q j c ε 𝒯).card : ℝ) ≤ (𝒯.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubT
  have hA : ((TsetSmall H P Q j c ε 𝒯).card : ℝ) * Real.sqrt T
      ≤ (𝒯.card : ℝ) * Real.sqrt T :=
    mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg T)
  have hlog : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hmass : (0 : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun m _ => by positivity)
  nlinarith [mul_nonneg (sub_nonneg.mpr hA) (mul_nonneg hlog hmass)]

/-! ## §4 — the thinness arithmetic: `|𝒯|·√T ≤ W·X^{1−2η}` -/

/-- **The `X^{o(1)}` bundle of the §8.3 thinness count**: the `Q_J²` union factor
(`card (dyadicPairs P_Jb Q_Jb) ≤ (Q_Jb+1)²`, the D1 repair's true cost), Lemma 8's absolute
`840`, the level `V²`, and Lemma 8's `exp(2(log T/log P)·loglog T)` tail.  Explicit by
construction — law #253: nothing that grows with `X` is absorbed into a numeral. -/
noncomputable def thinBundle (T V : ℝ) (Pj Qj : ℕ) : ℝ :=
  ((dyadicPairs Pj Qj).card : ℝ)
    * (840 * V ^ 2 * Real.exp (2 * (Real.log T / Real.log Pj) * Real.log (Real.log T)))

lemma thinBundle_nonneg (T V : ℝ) (Pj Qj : ℕ) : 0 ≤ thinBundle T V Pj Qj := by
  rw [thinBundle]
  have h := Real.exp_pos (2 * (Real.log T / Real.log Pj) * Real.log (Real.log T))
  positivity

/-- **The `Q_J²` union factor, absorbed T-FREELY.**  From the definition of `J` alone
(`Q_J + 1 ≤ exp L`, the intended `L = (log X)^{1/2}`), the candidate-block family has
`card 𝒫 ≤ exp (2L) = X^{o(1)}`.  No `T` enters — and none may: coupling `Q_J²` to `T` would
eat the `η` that `α_J ≤ 1/4 − η` is paying for. -/
lemma dyadicPairs_card_le_exp (Pj Qj : ℕ) (L : ℝ) (hQ : ((Qj : ℝ) + 1) ≤ Real.exp L) :
    ((dyadicPairs Pj Qj).card : ℝ) ≤ Real.exp (2 * L) := by
  have h1 : ((dyadicPairs Pj Qj).card : ℝ) ≤ ((Qj : ℝ) + 1) ^ 2 := by
    have h := card_dyadicPairs_le Pj Qj
    have h' : ((dyadicPairs Pj Qj).card : ℝ) ≤ (((Qj + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have h2 : ((Qj : ℝ) + 1) ^ 2 ≤ Real.exp L ^ 2 :=
    pow_le_pow_left₀ (by positivity) hQ 2
  have h3 : Real.exp L ^ 2 = Real.exp (2 * L) := by
    rw [show (2 : ℝ) * L = L + L by ring, Real.exp_add, sq]
  linarith [h1, h2, h3.ge, h3.le]

/-- **`Uset_thin` at the `α_J` gate.**  Lemma 8's exponent `2·log V/log P_Jb` is bounded by
`2α` through the in-statement gate `log V ≤ α·log P_Jb`; everything else is the explicit
`thinBundle`.  At the ratified pin `δ := P_J^{−α_J}`, `V := K₀/δ`, the gate reads
`α = α_J + log K₀/log P_J` — the consumer's `o(1)` inflation of `α_J`, which is why the
kill below only needs `α ≤ 1/4 − η`, not `α_J ≤ 1/4 − η`. -/
theorem Uset_thin_alpha (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (Pseq Qseq : ℕ → ℕ) (δ : ℝ)
    (J Jb : ℕ) (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J) (hδ0 : 0 < δ)
    (T V : ℝ) (hT : 1 < T) (hV : 1 ≤ V)
    (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log (Qseq Jb)) (hLL5 : 5 ≤ Real.log (Real.log T))
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hU : ∀ t ∈ 𝒯, t ∈ Uset f Pseq Qseq δ J)
    (α : ℝ) (hVα : Real.log V ≤ α * Real.log (Pseq Jb)) :
    (𝒯.card : ℝ) ≤ thinBundle T V (Pseq Jb) (Qseq Jb) * T ^ (2 * α) := by
  have hP1R : (1 : ℝ) < (Pseq Jb : ℝ) := by
    have h : (3 : ℝ) ≤ (Pseq Jb : ℝ) := by exact_mod_cast hP3
    linarith
  have hlogP : 0 < Real.log (Pseq Jb) := Real.log_pos hP1R
  have hexp : 2 * Real.log V / Real.log (Pseq Jb) ≤ 2 * α := by
    rw [div_le_iff₀ hlogP]
    nlinarith [hVα]
  have hrpow : T ^ (2 * Real.log V / Real.log (Pseq Jb)) ≤ T ^ (2 * α) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hT) hexp
  have hcount := Uset_thin f hf1 Pseq Qseq δ J Jb hJb1 hJbJ hδ0 T V hT hV hVinv hP3 hQT
    hκ30 hLL5 𝒯 hws hsub hU
  refine hcount.trans ?_
  rw [thinBundle]
  have hK : (0 : ℝ) ≤ ((dyadicPairs (Pseq Jb) (Qseq Jb)).card : ℝ)
      * (840 * V ^ 2
          * Real.exp (2 * (Real.log T / Real.log (Pseq Jb)) * Real.log (Real.log T))) := by
    have h := Real.exp_pos (2 * (Real.log T / Real.log (Pseq Jb)) * Real.log (Real.log T))
    positivity
  calc ((dyadicPairs (Pseq Jb) (Qseq Jb)).card : ℝ)
        * (840 * T ^ (2 * Real.log V / Real.log (Pseq Jb)) * V ^ 2
            * Real.exp (2 * (Real.log T / Real.log (Pseq Jb)) * Real.log (Real.log T)))
      = (((dyadicPairs (Pseq Jb) (Qseq Jb)).card : ℝ)
          * (840 * V ^ 2
              * Real.exp (2 * (Real.log T / Real.log (Pseq Jb)) * Real.log (Real.log T))))
        * T ^ (2 * Real.log V / Real.log (Pseq Jb)) := by ring
    _ ≤ (((dyadicPairs (Pseq Jb) (Qseq Jb)).card : ℝ)
          * (840 * V ^ 2
              * Real.exp (2 * (Real.log T / Real.log (Pseq Jb)) * Real.log (Real.log T))))
        * T ^ (2 * α) := mul_le_mul_of_nonneg_left hrpow hK

/-- **The kill (MR §8.3 Step 3 → Step 4, `𝒯_S`).**  With Lemma 8's count at exponent `2α`,
the `α_J ≤ 1/4 − η` gate and **MR Step 0's `T ≤ X`** (p.24: the mean value theorem already
gives `O(T/X+1)`, so `T > X` is trivial),

  `|𝒯|·√T ≤ W·T^{2α+1/2} ≤ W·T^{1−2η} ≤ W·X^{1−2η}`.

This is the *only* place the `𝒰`-thinness is spent in the `𝒯_S` branch. -/
theorem thin_sqrt_kill (T X W α η cnt : ℝ) (hT : 1 ≤ T) (hTX : T ≤ X) (hW : 0 ≤ W)
    (hα : α ≤ 1 / 4 - η) (hη2 : 2 * η ≤ 1) (hcnt : cnt ≤ W * T ^ (2 * α)) :
    cnt * Real.sqrt T ≤ W * X ^ (1 - 2 * η) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hstep1 : cnt * Real.sqrt T ≤ W * T ^ (2 * α) * Real.sqrt T :=
    mul_le_mul_of_nonneg_right hcnt (Real.sqrt_nonneg T)
  have hstep2 : W * T ^ (2 * α) * Real.sqrt T = W * T ^ (2 * α + 1 / 2) := by
    rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hT0]
  have hstep3 : T ^ (2 * α + 1 / 2) ≤ T ^ (1 - 2 * η) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hstep4 : T ^ (1 - 2 * η) ≤ X ^ (1 - 2 * η) :=
    Real.rpow_le_rpow (by linarith) hTX (by linarith)
  calc cnt * Real.sqrt T ≤ W * T ^ (2 * α) * Real.sqrt T := hstep1
    _ = W * T ^ (2 * α + 1 / 2) := hstep2
    _ ≤ W * T ^ (1 - 2 * η) := mul_le_mul_of_nonneg_left hstep3 hW
    _ ≤ W * X ^ (1 - 2 * η) := mul_le_mul_of_nonneg_left hstep4 hW

/-- **`Uset_thin` → the Halász term.**  The composed thinness feed: the well-spaced set of a
thin `𝒰` contributes `|𝒯|·√T ≤ thinBundle·X^{1−2η}` to Lemma 9's `(M + |𝒯|√T)`. -/
theorem Uset_thin_sqrt_kill (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (Pseq Qseq : ℕ → ℕ)
    (δ : ℝ) (J Jb : ℕ) (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J) (hδ0 : 0 < δ)
    (T V : ℝ) (hT : 1 < T) (hV : 1 ≤ V)
    (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log (Qseq Jb)) (hLL5 : 5 ≤ Real.log (Real.log T))
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hU : ∀ t ∈ 𝒯, t ∈ Uset f Pseq Qseq δ J)
    (α η X : ℝ) (hVα : Real.log V ≤ α * Real.log (Pseq Jb)) (hα : α ≤ 1 / 4 - η)
    (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) :
    (𝒯.card : ℝ) * Real.sqrt T ≤ thinBundle T V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η) :=
  thin_sqrt_kill T X (thinBundle T V (Pseq Jb) (Qseq Jb)) α η (𝒯.card : ℝ)
    (le_of_lt hT) hTX (thinBundle_nonneg T V (Pseq Jb) (Qseq Jb)) hα hη2
    (Uset_thin_alpha f hf1 Pseq Qseq δ J Jb hJb1 hJbJ hδ0 T V hT hV hVinv hP3 hQT hκ30 hLL5
      𝒯 hws hsub hU α hVα)

/-! ## §5 — the exit: the `𝒯_S` branch of `hU` -/

/-- **U-5 — THE `𝒯_S` BRANCH.**  MR §8.3 Step 4's small-prime-factor branch, assembled:
the pointwise `ε²` gain, Lemma 9 on the co-factor at the sharp length `M`, and the `𝒰`-
thinness spent through `|𝒯|·√T ≤ thinBundle·X^{1−2η}`.

Every growing quantity is in-statement (law #253): the co-factor length `M`, the branch
threshold `ε`, the Lemma-8 exponent gate `α`, the margin `η`, the Step-0 majorant `X`, and
the `X^{o(1)}` bundle `thinBundle` (which carries the `Q_J²` union factor — absorbed
T-freely by `dyadicPairs_card_le_exp`, never coupled to `T`).

Carried hypotheses, in order: the `Uset_thin` gates (`3 ≤ P_Jb`, `Q_Jb ≤ T`, `1 < T`,
`log T/log Q_Jb ≥ 30`, `loglog T ≥ 5`, `0 < δ`, `1 ≤ V`, `V⁻¹ ≤ δ/K₀`, `‖f n‖ ≤ 1`,
`1 ≤ Jb ≤ J`), the well-spaced data (`WellSpaced 𝒯`, `𝒯 ⊆ [−T,T]`, `𝒯 ⊆ 𝒰`), the `α`-gate
(`log V ≤ α·log P_Jb`, `α ≤ 1/4 − η`, `2η ≤ 1`), MR Step 0 (`T ≤ X`), and the co-factor
length (`ramRrange H N Xd j ⊆ [1,M]`). -/
theorem uset_TS_branch (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (Pseq Qseq : ℕ → ℕ)
    (δ : ℝ) (J Jb : ℕ) (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J) (hδ0 : 0 < δ)
    (T V : ℝ) (hT : 1 < T) (hV : 1 ≤ V)
    (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log (Qseq Jb)) (hLL5 : 5 ≤ Real.log (Real.log T))
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hU : ∀ t ∈ 𝒯, t ∈ Uset f Pseq Qseq δ J)
    (α η X : ℝ) (hVα : Real.log V ≤ α * Real.log (Pseq Jb)) (hα : α ≤ 1 / 4 - η)
    (hη2 : 2 * η ≤ 1) (hTX : T ≤ X)
    (H : ℝ) (N Xd P Q j M : ℕ) (b c : ℕ → ℂ) (ε : ℝ)
    (hM : ramRrange H N Xd j ⊆ Finset.Icc 1 M) :
    ∑ t ∈ TsetSmall H P Q j c ε 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2
      ≤ ε ^ 2 * (2564 * ((M : ℝ) + thinBundle T V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η))
          * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) := by
  refine (TS_branch_meansq H N Xd P Q j M b c hM ε T (le_of_lt hT) 𝒯 hws hsub).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ε)
  have hkill := Uset_thin_sqrt_kill f hf1 Pseq Qseq δ J Jb hJb1 hJbJ hδ0 T V hT hV hVinv
    hP3 hQT hκ30 hLL5 𝒯 hws hsub hU α η X hVα hα hη2 hTX
  have hlog : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hmass : (0 : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun m _ => by positivity)
  nlinarith [mul_nonneg (sub_nonneg.mpr hkill) (mul_nonneg hlog hmass)]

/-- **U-5 (exit) — the `𝒯_S` branch at the MEAN-VALUE grade.**  MR's actual conclusion: once
the thinness budget clears the co-factor length (`W·X^{1−2η} ≤ M`, the consumer's `X^{o(1)}`
arithmetic against `M ≍ X e^{−j/H}`), Lemma 9 degenerates to the mean value theorem and the
branch is priced at the trivial grade **times the pointwise gain `ε²`** — MR's
`(log X)^{−200}` at `ε = (log X)^{−100}`.  The Halász term has vanished: that is what the
`𝒰`-thinness bought. -/
theorem uset_TS_branch_meanvalue (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (Pseq Qseq : ℕ → ℕ)
    (δ : ℝ) (J Jb : ℕ) (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J) (hδ0 : 0 < δ)
    (T V : ℝ) (hT : 1 < T) (hV : 1 ≤ V)
    (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log (Qseq Jb)) (hLL5 : 5 ≤ Real.log (Real.log T))
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hU : ∀ t ∈ 𝒯, t ∈ Uset f Pseq Qseq δ J)
    (α η X : ℝ) (hVα : Real.log V ≤ α * Real.log (Pseq Jb)) (hα : α ≤ 1 / 4 - η)
    (hη2 : 2 * η ≤ 1) (hTX : T ≤ X)
    (H : ℝ) (N Xd P Q j M : ℕ) (b c : ℕ → ℂ) (ε : ℝ)
    (hM : ramRrange H N Xd j ⊆ Finset.Icc 1 M)
    (hbudget : thinBundle T V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η) ≤ (M : ℝ)) :
    ∑ t ∈ TsetSmall H P Q j c ε 𝒯, ‖ramMain H N Xd P Q b c j t‖ ^ 2
      ≤ 5128 * ε ^ 2 * (M : ℝ) * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  refine (uset_TS_branch f hf1 Pseq Qseq δ J Jb hJb1 hJbJ hδ0 T V hT hV hVinv hP3 hQT hκ30
    hLL5 𝒯 hws hsub hU α η X hVα hα hη2 hTX H N Xd P Q j M b c ε hM).trans ?_
  have hlog : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hmass : (0 : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun m _ => by positivity)
  have hε2 : (0 : ℝ) ≤ ε ^ 2 := sq_nonneg ε
  nlinarith [mul_nonneg hε2 (mul_nonneg (sub_nonneg.mpr hbudget) (mul_nonneg hlog hmass))]

/-! ## §6 — the co-factor mass (the trivial bound on Lemma 9's coefficient sum) -/

/-- **The co-factor's coefficient mass at `‖b‖ ≤ 1`.**  The Ramaré weight `(ω+1)⁻¹` has norm
`≤ 1`, so the mass is at most the harmonic-square mass of the co-factor range.  With
`M ≍ 2X e^{−j/H}` and `ramRrange` at `m ≍ X e^{−j/H}`, `M · (this) ≍ 1` — which is why §1's
sharp `M` is load-bearing. -/
lemma ramRcoeff_mass_le (H : ℝ) (N X P Q j M : ℕ) (b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1)
    (hM : ramRrange H N X j ⊆ Finset.Icc 1 M) :
    ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2
      ≤ ∑ m ∈ ramRrange H N X j, 1 / (m : ℝ) ^ 2 := by
  rw [← Finset.sum_subset hM (fun m _ hm => by
    rw [ramRcoeff_of_notMem H N X P Q j b hm, norm_zero]; simp)]
  refine Finset.sum_le_sum (fun m hm => ?_)
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (hM hm)).1
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hnorm : ‖ramRcoeff H N X P Q j b m‖ ≤ 1 := by
    rw [ramRcoeff, if_pos hm, norm_mul]
    have hw : ‖((blockOmega P Q m : ℂ) + 1)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      have heq : ‖(blockOmega P Q m : ℂ) + 1‖ = (blockOmega P Q m : ℝ) + 1 := by
        rw [show ((blockOmega P Q m : ℂ) + 1) = ((blockOmega P Q m + 1 : ℕ) : ℂ) by
          push_cast; ring, Complex.norm_natCast]
        push_cast; ring
      rw [heq]
      exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (by positivity))
    have hbm := hb m
    nlinarith [norm_nonneg (b m), norm_nonneg (((blockOmega P Q m : ℂ) + 1)⁻¹)]
  have hsq : ‖ramRcoeff H N X P Q j b m‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (ramRcoeff H N X P Q j b m)]
  exact div_le_div_of_nonneg_right hsq (by positivity)

end Salt.MR
