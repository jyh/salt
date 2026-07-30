/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetThinTL
import Salt.MR.HybridLargeValues
import Salt.MR.HybridMoments

/-!
# USetChi — the `χ`-lift of the `𝒰`-leg's index-set machinery (wave P-6, stone E, part 1)

The KMT port's `𝒰`-leg runs the landed `q = 1` machinery of `USetThin`/`USetThinTL`/
`USetThinTS`/`USetBalance` with the index of the spectrum sets moved from `t : ℝ` to a
**pair** `(χ, t) : DirichletCharacter ℂ q × ℝ`.  This file lands the index-set machinery,
the block objects at `χ̄`-twisted data, and the `𝒯_L` branch; `USetChiTS.lean` lands the
`𝒯_S` razor, the branch exits, and the balance twin.

## What is retyped and what is consumed

* **Consumed as landed, never re-defined** (wave P-3/P-4's supply floor):
  `FibreWellSpaced` (`HybridLargeValues`:90) is THE per-fibre spacing — ordinates sharing a
  character are `≥ 1` apart, ordinates on different characters unconstrained;
  `hybrid_large_value_count` (KMT Lemma 6.5 at `qT`) is THE count;
  `chiBarCoeff`/`spoly_chiBarCoeff_eq_dpolyChi` (`HybridMoments`:113/157) are THE twisted
  carriers.  The twisted block objects are the LANDED `ramQ`/`ramR`/`ramMain` applied to
  `chiBarCoeff q χ ·` — no new block carrier is minted.
* **Retyped here** (proofs near-verbatim, the datum being character-blind):
  the reflection involution, `UsetChi`, `hybridblock_count`, `UsetChi_thin`, `tLsetChi` and
  its three structure lemmas, `ramQChi_large_count`(`_Tfree`), and the `𝒯_L` kill/exit.
* **Reused verbatim, no retype needed** (character-free arithmetic): `dyadicPairs` and
  `card_dyadicPairs_le`, `ratioChain`/`primeBlockPoly_chain_split`/`exists_piece_large`,
  `largeblock_bound_mono`, `tL_kill`, `ramQbase` and its geometry, `ramQblock_inv_sum_le`
  (the prime-window gain), `ramQbase_le_pow_ten`.

## CATCH #B ∘ N1 — the reflection is a PAIR involution

`spoly N (chiBarCoeff q χ a) t = dpolyChi q (Icc 1 N) (aₙ/n) χ⁻¹ (−t)`
(`HybridMoments.spoly_chiBarCoeff_eq_dpolyChi`): the `σ = 1 → σ = 0` bridge negates the
ordinate (CATCH #B) *and* conjugates the character (N1).  So the "negated ordinate set" of
the `q = 1` files becomes the involution `(χ, t) ↦ (χ⁻¹, −t)` — `reflectPair` below.  It
preserves cardinality, `FibreWellSpaced` (inversion is injective on characters, so it
permutes fibres) and `[−T, T]`.  **Every statement of this file declares its sign
convention explicitly**: the `ramQ`/`primeBlockPoly` carriers are at `σ = 1`
(`n^{1+it}`, MR's convention), `dpolyChi` is at `n^{+it}` (KMT's), and the bridges below are
the only place the two meet.

## The height argument: `qT`, not `T`

`hybrid_large_value_count`'s `T`-legs read `q·T` (the fold's `φ(q)(T+1) + φ(q)(2P)^k/q ≤
2(qT + (2P)^k)` packaging).  Every count/kill statement here therefore carries
`Real.log ((q : ℝ) * T)` where the `q = 1` original carried `Real.log T`, and the gates
(`1 < qT`, `P ≤ qT`, `30 ≤ log qT/log base`, `5 ≤ loglog qT`) are the landed shapes at that
argument.  **LAW #253**: the `X₀` law (`hκ30`) stays in-statement, verbatim, at every rung —
never absorbed into a constant.

## The named hypothesis slot (`HalaszPrimesChi`)

The `𝒯_L` decay needs MR Lemma 11 (`halasz_primes_pow`) at `χ`-twisted prime data — wave
P-6-CORE's `halasz_primes_chi`, stone C, in flight at the time of writing.  It is consumed
here as the explicit socket `HalaszPrimesChi C c T₀` (below), whose shape is the landed
`halasz_primes_pow` with the pair index set, `FibreWellSpaced` spacing, the `χ̄`-twisted
integrand and the decay denominator read at `qT`.  Reading the denominator at `qT` rather
than `T` makes the socket the WEAKER hypothesis (a larger denominator is a weaker decay, and
`(log T)`-shaped decay implies it by monotonicity), so a sharper landed `halasz_primes_chi`
discharges this slot; P-7 connects them.

Source pins (D5): MR arXiv v4 (`1501.04585v4`) pp. 8, 15–16, 19–20, 27–29; KMT §6
(Lemmas 6.2/6.5); the port freeze `docs/exploration/port-freeze-0729.md` v2 and the
`⟦SPECTRUM-SCOPE⟧` census in `docs/blueprints/flags.md`.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the `(χ, t)` index set: the reflection involution (CATCH #B ∘ N1) -/

/-- **The reflection involution on `(χ, t)`-pairs**: `(χ, t) ↦ (χ⁻¹, −t)`.  CATCH #B (the
`t`-sign) composed with N1 (the `χ̄`-conjugation): `spoly N (χ̄ a) t = dpolyChi q _ (a/n) χ⁻¹
(−t)` moves both coordinates at once.  Packaged as an `Equiv` so that index sets travel by
`Finset.map` — no `DecidableEq` on characters enters any statement. -/
noncomputable def reflectPair (q : ℕ) :
    (DirichletCharacter ℂ q × ℝ) ≃ (DirichletCharacter ℂ q × ℝ) where
  toFun p := (p.1⁻¹, -p.2)
  invFun p := (p.1⁻¹, -p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- **The reflected index set** `{(χ⁻¹, −t) : (χ, t) ∈ ℰ}`. -/
noncomputable def reflectChi {q : ℕ} (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) :
    Finset (DirichletCharacter ℂ q × ℝ) :=
  ℰ.map (reflectPair q).toEmbedding

@[simp] lemma mem_reflectChi {q : ℕ} {ℰ : Finset (DirichletCharacter ℂ q × ℝ)}
    {r : DirichletCharacter ℂ q × ℝ} : r ∈ reflectChi ℰ ↔ (r.1⁻¹, -r.2) ∈ ℰ := by
  rw [reflectChi, Finset.mem_map_equiv]
  rfl

@[simp] lemma card_reflectChi {q : ℕ} (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) :
    (reflectChi ℰ).card = ℰ.card := Finset.card_map _

/-- Sums over the reflected index set, unfolded: `Σ_{ℰ'} g = Σ_{ℰ} g(χ⁻¹, −t)`. -/
lemma sum_reflectChi {q : ℕ} (ℰ : Finset (DirichletCharacter ℂ q × ℝ))
    (g : DirichletCharacter ℂ q × ℝ → ℝ) :
    ∑ r ∈ reflectChi ℰ, g r = ∑ r ∈ ℰ, g (r.1⁻¹, -r.2) := by
  rw [reflectChi, Finset.sum_map]
  exact Finset.sum_congr rfl (fun r _ => rfl)

/-- The reflection preserves per-fibre spacing: inversion is injective on characters, so it
permutes the fibres, and `|(−t) − (−u)| = |t − u|`. -/
lemma fibreWellSpaced_reflectChi {q : ℕ} {ℰ : Finset (DirichletCharacter ℂ q × ℝ)}
    (hws : FibreWellSpaced ℰ) : FibreWellSpaced (reflectChi ℰ) := by
  intro r hr s hs hchar hord
  rw [mem_reflectChi] at hr hs
  have hchar' : ((r.1⁻¹, -r.2) : DirichletCharacter ℂ q × ℝ).1
      = ((s.1⁻¹, -s.2) : DirichletCharacter ℂ q × ℝ).1 := by
    simpa using congrArg (fun χ : DirichletCharacter ℂ q => χ⁻¹) hchar
  have hord' : ((r.1⁻¹, -r.2) : DirichletCharacter ℂ q × ℝ).2
      ≠ ((s.1⁻¹, -s.2) : DirichletCharacter ℂ q × ℝ).2 := by
    simpa using fun h => hord (by linarith [h])
  have h := hws _ hr _ hs hchar' hord'
  simp only at h
  rwa [show -r.2 - -s.2 = -(r.2 - s.2) by ring, abs_neg] at h

/-- The reflection preserves the ordinate window `[−T, T]`. -/
lemma reflectChi_subset_Icc {q : ℕ} {ℰ : Finset (DirichletCharacter ℂ q × ℝ)} {T : ℝ}
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) :
    ∀ r ∈ reflectChi ℰ, r.2 ∈ Set.Icc (-T) T := by
  intro r hr
  rw [mem_reflectChi] at hr
  have h := Set.mem_Icc.mp (hsub _ hr)
  simp only at h
  exact Set.mem_Icc.mpr ⟨by linarith [h.2], by linarith [h.1]⟩

/-- A subset of a per-fibre well-spaced set is per-fibre well-spaced (the pair analogue of
`wellSpaced_of_subset`). -/
lemma fibreWellSpaced_of_subset {q : ℕ} {ℱ ℰ : Finset (DirichletCharacter ℂ q × ℝ)}
    (h : ℱ ⊆ ℰ) (hws : FibreWellSpaced ℰ) : FibreWellSpaced ℱ :=
  fun r hr s hs hchar hord => hws r (h hr) s (h hs) hchar hord

/-! ## §2 — the block objects at `χ̄`-twisted data

Every object here is a LANDED carrier evaluated at `chiBarCoeff q χ ·`; the content is that
the twist passes through the masking (`blockSrc`, `ramQsrc`) and the `1/n` of the `σ = 1`
convention, so the `σ = 1 → σ = 0` bridge lands on `dpolyChi` at `χ⁻¹` and `−t`. -/

/-- The `χ̄`-twist commutes with dividing by `n` (the `σ = 1` convention's `1/n`). -/
lemma chiBarCoeff_div (q : ℕ) (χ : DirichletCharacter ℂ q) (a : ℕ → ℂ) (n : ℕ) :
    chiBarCoeff q χ a n / (n : ℂ) = chiBarCoeff q χ (fun m => a m / (m : ℂ)) n := by
  rw [chiBarCoeff_apply, chiBarCoeff_apply, mul_div_assoc]

/-- The prime-block mask commutes with the `χ̄`-twist. -/
lemma blockSrc_chiBar (q : ℕ) (χ : DirichletCharacter ℂ q) (f : ℕ → ℂ) (P Q : ℕ) :
    blockSrc (chiBarCoeff q χ f) P Q = chiBarCoeff q χ (blockSrc f P Q) := by
  funext n
  rw [chiBarCoeff_apply]
  by_cases h : n.Prime ∧ P ≤ n ∧ n ≤ Q
  · rw [blockSrc, if_pos h, blockSrc, if_pos h, chiBarCoeff_apply]
  · rw [blockSrc, if_neg h, blockSrc, if_neg h, mul_zero]

/-- **The composed bridge (CATCH #B ∘ N1) at `primeBlockPoly`.**  The `σ = 1` prime block
polynomial of the `χ̄`-twisted datum is KMT's `σ = 0` twisted polynomial at the INVERTED
character and the NEGATED ordinate.  This is the shape `hybrid_large_value_count` consumes. -/
lemma primeBlockPoly_chiBar_eq_dpolyChi (q : ℕ) (χ : DirichletCharacter ℂ q) (f : ℕ → ℂ)
    (P Q N : ℕ) (hP : 1 ≤ P) (hQN : Q ≤ N) (t : ℝ) :
    primeBlockPoly (chiBarCoeff q χ f) P Q t
      = dpolyChi q (Finset.Icc 1 N) (fun n => blockSrc f P Q n / (n : ℂ)) χ⁻¹ (-t) := by
  rw [primeBlockPoly_eq_spoly (chiBarCoeff q χ f) P Q N hP hQN t, blockSrc_chiBar,
    spoly_chiBarCoeff_eq_dpolyChi]

/-- The Ramaré prime-block mask commutes with the `χ̄`-twist. -/
lemma ramQsrc_chiBar (q : ℕ) (χ : DirichletCharacter ℂ q) (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) :
    ramQsrc H P Q j (chiBarCoeff q χ c) = chiBarCoeff q χ (ramQsrc H P Q j c) := by
  funext n
  rw [chiBarCoeff_apply]
  by_cases h : n ∈ ramQblock H P Q j
  · rw [ramQsrc, if_pos h, ramQsrc, if_pos h, chiBarCoeff_apply]
  · rw [ramQsrc, if_neg h, ramQsrc, if_neg h, mul_zero]

/-- `ramQ` at twisted data is the `σ = 1` polynomial of its own twisted masked coefficients
(the mirror of `ramQ_eq_spoly`). -/
lemma ramQ_chiBar_eq_spoly (q : ℕ) (χ : DirichletCharacter ℂ q) (H : ℝ) (P Q N j : ℕ)
    (c : ℕ → ℂ) (hN : ∀ p ∈ ramQblock H P Q j, p ≤ N) (t : ℝ) :
    ramQ H P Q j (chiBarCoeff q χ c) t = spoly N (chiBarCoeff q χ (ramQsrc H P Q j c)) t := by
  rw [ramQ_eq_spoly H P Q N j (chiBarCoeff q χ c) hN t, ramQsrc_chiBar]

/-- **The composed bridge (CATCH #B ∘ N1) at `ramQ`.**  `Q_{j,H}(χ̄, 1+it)` is `dpolyChi` at
`χ⁻¹` and `−t`: a caller holding `‖Q_{j,H}(χ̄, 1+it)‖` large at `(χ, t)` hands the hybrid
count the REFLECTED pair `(χ⁻¹, −t)`. -/
lemma ramQ_chiBar_eq_dpolyChi (q : ℕ) (χ : DirichletCharacter ℂ q) (H : ℝ) (P Q N j : ℕ)
    (c : ℕ → ℂ) (hN : ∀ p ∈ ramQblock H P Q j, p ≤ N) (t : ℝ) :
    ramQ H P Q j (chiBarCoeff q χ c) t
      = dpolyChi q (Finset.Icc 1 N) (fun n => ramQsrc H P Q j c n / (n : ℂ)) χ⁻¹ (-t) := by
  rw [ramQ_chiBar_eq_spoly q χ H P Q N j c hN t, spoly_chiBarCoeff_eq_dpolyChi]

/-- **The Lemma-11 shape at twisted data (NO sign flip).**  `Q_{j,H}(χ̄, 1+it) =
Σ_p p^{−it}·χ̄(p)·(c_p/p)` — the integrand of a `χ`-twisted Halász-for-primes at
`a_p = c_p/p`.  The `σ = 1` convention already carries the `p^{−it}`, so this bridge is
sign-free; only the `dpolyChi` bridge above negates. -/
lemma ramQ_chiBar_eq_halaszSum (q : ℕ) (χ : DirichletCharacter ℂ q) (H : ℝ) (P Q j : ℕ)
    (c : ℕ → ℂ) (t : ℝ) :
    ramQ H P Q j (chiBarCoeff q χ c) t
      = ∑ p ∈ ramQblock H P Q j,
          (p : ℂ) ^ (-(t : ℂ) * Complex.I) * chiBarCoeff q χ (fun m => c m / (m : ℂ)) p := by
  rw [ramQ_eq_halaszSum H P Q j (chiBarCoeff q χ c) t]
  exact Finset.sum_congr rfl (fun p _ => by rw [chiBarCoeff_div])

/-! ## §3 — the hybrid block count and the `χ`-lifted thinness of `𝒰` -/

/-- Lemma 6.5's bound is monotone in the block base, at the hybrid constant `1680` and the
hybrid height argument (the landed `largeblock_bound_mono`, doubled). -/
lemma hybridblock_bound_mono (S V : ℝ) (hS : 1 < S) (hV : 1 ≤ V) (P p : ℕ) (hP3 : 3 ≤ P)
    (hPp : P ≤ p) (hLL : 0 ≤ Real.log (Real.log S)) :
    1680 * S ^ (2 * Real.log V / Real.log p) * V ^ 2
        * Real.exp (2 * (Real.log S / Real.log p) * Real.log (Real.log S))
      ≤ 1680 * S ^ (2 * Real.log V / Real.log P) * V ^ 2
        * Real.exp (2 * (Real.log S / Real.log P) * Real.log (Real.log S)) := by
  have h := largeblock_bound_mono S V hS hV P p hP3 hPp hLL
  linarith

/-- **The `t`-free hybrid Lemma-6.5 adapter (the pair analogue of `largeblock_count`).**  A
FIXED prime block `[p, qq]` of ratio at most `2` on which the `χ̄`-twisted `σ = 1` block
polynomial is `≥ V⁻¹` along a per-fibre well-spaced `ℰ ⊆ (characters) × [−T,T]` is counted
by `hybrid_large_value_count` at the hybrid constant `1680` and the height `qT`.

Sign convention: the hypothesis is at `σ = 1` (`primeBlockPoly … (1+it)`); the count is
applied at the reflected set `(χ⁻¹, −t)`, of the same cardinality (CATCH #B ∘ N1).  Gates
carried verbatim from Lemma 6.5. -/
theorem hybridblock_count (q : ℕ) [NeZero q] (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (p qq : ℕ) (T V : ℝ) (hp3 : 3 ≤ p) (hq2p : qq ≤ 2 * p) (hT1 : 1 ≤ T)
    (hqT : 1 < (q : ℝ) * T) (hpqT : (p : ℝ) ≤ (q : ℝ) * T) (hV : 1 ≤ V)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log p)
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hlb : ∀ r ∈ ℰ, V⁻¹ ≤ ‖primeBlockPoly (chiBarCoeff q r.1 f) p qq r.2‖) :
    (ℰ.card : ℝ)
      ≤ 1680 * ((q : ℝ) * T) ^ (2 * Real.log V / Real.log p) * V ^ 2
          * Real.exp (2 * (Real.log ((q : ℝ) * T) / Real.log p)
              * Real.log (Real.log ((q : ℝ) * T))) := by
  have hp1 : 1 ≤ p := by omega
  set src : ℕ → ℂ := fun n => blockSrc f p qq n / (n : ℂ) with hsrc
  have hsupp : ∀ m, src m ≠ 0 → m.Prime ∧ p ≤ m := by
    intro m hm
    by_cases hcond : m.Prime ∧ p ≤ m ∧ m ≤ qq
    · exact ⟨hcond.1, hcond.2.1⟩
    · exact absurd (by simp only [hsrc, blockSrc, if_neg hcond, zero_div]) hm
  have hcoeff : ∀ m, src m ≠ 0 → ‖src m‖ ≤ (m : ℝ)⁻¹ := by
    intro m hm
    obtain ⟨hpr, _⟩ := hsupp m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hpr.pos
    by_cases hcond : m.Prime ∧ p ≤ m ∧ m ≤ qq
    · simp only [hsrc, blockSrc, if_pos hcond, norm_div, Complex.norm_natCast]
      rw [inv_eq_one_div]
      gcongr
      exact hf1 m
    · exact absurd (by simp only [hsrc, blockSrc, if_neg hcond, zero_div]) hm
  have hlb' : ∀ r ∈ reflectChi ℰ,
      V⁻¹ ≤ ‖dpolyChi q (Finset.Icc 1 (2 * p)) src r.1 r.2‖ := by
    intro r hr
    have hmem := mem_reflectChi.mp hr
    have h := hlb _ hmem
    rw [primeBlockPoly_chiBar_eq_dpolyChi q r.1⁻¹ f p qq (2 * p) hp1 hq2p (-r.2)] at h
    simpa [hsrc] using h
  have h := hybrid_large_value_count q p src T V hp3 hT1 hqT hpqT hV hκ30 hLL5
    (reflectChi ℰ) (fibreWellSpaced_reflectChi hws) (reflectChi_subset_Icc hsub)
    hsupp hcoeff hlb'
  rwa [card_reflectChi] at h

/-- **`𝒰` at `(χ, t)`** — the `χ`-lift of `Decomp.Uset`: the pair `(χ, t)` is exceptional
when NO block index `j ∈ [1, J]` has all its subdivisions of the `χ̄`-twisted prime
polynomial small.  Definitionally the `q = 1` set of the twisted datum, fibre by fibre —
which is what makes the whole `USetThin` witness/pigeonhole page reusable. -/
def UsetChi (q : ℕ) (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J : ℕ) :
    Set (DirichletCharacter ℂ q × ℝ) :=
  {r | r.2 ∈ Uset (chiBarCoeff q r.1 f) Pseq Qseq δ J}

lemma mem_UsetChi {q : ℕ} {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {δ : ℝ} {J : ℕ}
    {r : DirichletCharacter ℂ q × ℝ} :
    r ∈ UsetChi q f Pseq Qseq δ J
      ↔ ∀ j, 1 ≤ j → j ≤ J → ¬ BlockSmallAt (chiBarCoeff q r.1 f) Pseq Qseq δ j r.2 :=
  Iff.rfl

/-- **U-4, `χ`-LIFTED — `𝒰` is thin on a per-fibre well-spaced PAIR set.**  Every pair of a
per-fibre well-spaced `ℰ ⊆ ((characters) × [−T,T]) ∩ 𝒰_χ` carries, at the block index `Jb`,
a sub-block of `[P_Jb, Q_Jb]` on which its own twisted prime polynomial exceeds `δ`;
refining along the ratio-2 chain and pigeonholing over the `K₀ = ⌊log₂(Q_Jb+1)⌋+1` pieces
puts the pair into one of the `dyadicPairs` count sets — each bounded by the HYBRID count.
The candidate family `dyadicPairs` is character-free and is reused verbatim; the character
count enters ONLY through the hybrid count's height `qT` (there is no `φ(q)` union factor:
Lemma 6.5 counts pairs).

Honest gates, all carried (law #253): `3 ≤ P_Jb`, `Q_Jb ≤ qT`, `1 ≤ T`, `1 < qT`,
`log qT/log Q_Jb ≥ 30`, `loglog qT ≥ 5`, `0 < δ`, `‖f n‖ ≤ 1`, `1 ≤ V`, `V⁻¹ ≤ δ/K₀`,
`1 ≤ Jb ≤ J`. -/
theorem UsetChi_thin (q : ℕ) [NeZero q] (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J Jb : ℕ) (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J) (hδ0 : 0 < δ)
    (T V : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T) (hV : 1 ≤ V)
    (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log (Qseq Jb))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetChi q f Pseq Qseq δ J) :
    (ℰ.card : ℝ)
      ≤ ((dyadicPairs (Pseq Jb) (Qseq Jb)).card : ℝ)
        * (1680 * ((q : ℝ) * T) ^ (2 * Real.log V / Real.log (Pseq Jb)) * V ^ 2
            * Real.exp (2 * (Real.log ((q : ℝ) * T) / Real.log (Pseq Jb))
                * Real.log (Real.log ((q : ℝ) * T)))) := by
  classical
  set S : ℝ := (q : ℝ) * T with hSdef
  set K₀ : ℕ := Nat.log 2 (Qseq Jb + 1) + 1 with hK₀
  set B : ℝ := 1680 * S ^ (2 * Real.log V / Real.log (Pseq Jb)) * V ^ 2
      * Real.exp (2 * (Real.log S / Real.log (Pseq Jb)) * Real.log (Real.log S)) with hB
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log S) := by linarith
  have hK₀pos : 0 < K₀ := by omega
  have hK₀R : (0 : ℝ) < (K₀ : ℝ) := by exact_mod_cast hK₀pos
  have hthr : (0 : ℝ) < δ / (K₀ : ℝ) := by positivity
  -- (i) each candidate block's count set is bounded by the HYBRID count
  have hpair : ∀ pq ∈ dyadicPairs (Pseq Jb) (Qseq Jb),
      ((ℰ.filter
          (fun r => V⁻¹ ≤ ‖primeBlockPoly (chiBarCoeff q r.1 f) pq.1 pq.2 r.2‖)).card : ℝ)
        ≤ B := by
    intro pq hpq
    rw [dyadicPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_Icc] at hpq
    obtain ⟨⟨⟨hp1, hp2⟩, hq1, hq2⟩, hratio⟩ := hpq
    have hp3' : 3 ≤ pq.1 := le_trans hP3 hp1
    have hp1R : (1 : ℝ) < (pq.1 : ℝ) := by
      have : (3 : ℝ) ≤ (pq.1 : ℝ) := by exact_mod_cast hp3'
      linarith
    have hlogp : 0 < Real.log pq.1 := Real.log_pos hp1R
    have hlogQ : Real.log pq.1 ≤ Real.log (Qseq Jb) := by
      refine Real.log_le_log (by linarith) ?_
      exact_mod_cast hp2
    have hpS : (pq.1 : ℝ) ≤ S := by
      have : (pq.1 : ℝ) ≤ (Qseq Jb : ℝ) := by exact_mod_cast hp2
      linarith
    have hlogSnn : (0 : ℝ) ≤ Real.log S := Real.log_nonneg (le_of_lt hqT)
    have hκ : 30 ≤ Real.log S / Real.log pq.1 := by
      refine le_trans hκ30 ?_
      gcongr
    have hcount := hybridblock_count q f hf1 pq.1 pq.2 T V hp3' hratio hT1 hqT hpS hV hκ
      hLL5 (ℰ.filter (fun r => V⁻¹ ≤ ‖primeBlockPoly (chiBarCoeff q r.1 f) pq.1 pq.2 r.2‖))
      (fibreWellSpaced_of_subset (Finset.filter_subset _ _) hws)
      (fun r hr => hsub r (Finset.mem_filter.mp hr).1)
      (fun r hr => (Finset.mem_filter.mp hr).2)
    exact le_trans hcount
      (hybridblock_bound_mono S V hqT hV (Pseq Jb) pq.1 hP3 hp1 hLL0)
  -- (ii) the count sets cover `ℰ`
  have hcover : ℰ ⊆ (dyadicPairs (Pseq Jb) (Qseq Jb)).biUnion
      (fun pq => ℰ.filter
        (fun r => V⁻¹ ≤ ‖primeBlockPoly (chiBarCoeff q r.1 f) pq.1 pq.2 r.2‖)) := by
    intro r hr
    have hUr := mem_UsetChi.mp (hU r hr) Jb hJb1 hJbJ
    obtain ⟨P, Q, hP, hQ, hlarge⟩ :
        ∃ P Q, Pseq Jb ≤ P ∧ Q ≤ Qseq Jb ∧
          δ < ‖primeBlockPoly (chiBarCoeff q r.1 f) P Q r.2‖ := by
      by_contra hcon
      refine hUr (fun P Q hP hQ => ?_)
      by_contra hcon2
      exact hcon ⟨P, Q, hP, hQ, not_le.mp hcon2⟩
    have hP1 : 1 ≤ P := le_trans (by omega) hP
    have hQK : Q < ratioChain P K₀ := by
      refine lt_of_lt_of_le (lt_ratioChain_log P Q) (ratioChain_mono P ?_)
      have h : Nat.log 2 (Q + 1) ≤ Nat.log 2 (Qseq Jb + 1) := Nat.log_mono_right (by omega)
      omega
    rw [primeBlockPoly_chain_split (chiBarCoeff q r.1 f) P Q K₀ hQK r.2] at hlarge
    obtain ⟨k, _, hbig⟩ := exists_piece_large hK₀pos
      (fun k => primeBlockPoly (chiBarCoeff q r.1 f) (ratioChain P k)
        (min (2 * ratioChain P k) Q) r.2) hlarge
    have hnz : primeBlockPoly (chiBarCoeff q r.1 f) (ratioChain P k)
        (min (2 * ratioChain P k) Q) r.2 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hbig
      linarith
    have hck : ratioChain P k ≤ Q := by
      by_contra hcon
      apply hnz
      unfold primeBlockPoly
      rw [Finset.Icc_eq_empty (by omega), Finset.filter_empty, Finset.sum_empty]
    have hkP : Pseq Jb ≤ ratioChain P k := le_trans hP (ratioChain_ge P k)
    refine Finset.mem_biUnion.mpr
      ⟨(ratioChain P k, min (2 * ratioChain P k) Q), ?_, ?_⟩
    · rw [dyadicPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨⟨hkP, by omega⟩, ⟨by omega, by omega⟩⟩, min_le_left _ _⟩
    · exact Finset.mem_filter.mpr ⟨hr, le_trans hVinv (le_of_lt hbig)⟩
  -- (iii) the union bound
  calc (ℰ.card : ℝ)
      ≤ ((((dyadicPairs (Pseq Jb) (Qseq Jb)).biUnion
          (fun pq => ℰ.filter (fun r =>
            V⁻¹ ≤ ‖primeBlockPoly (chiBarCoeff q r.1 f) pq.1 pq.2 r.2‖))).card : ℝ)) := by
        exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ pq ∈ dyadicPairs (Pseq Jb) (Qseq Jb),
          ((ℰ.filter (fun r =>
            V⁻¹ ≤ ‖primeBlockPoly (chiBarCoeff q r.1 f) pq.1 pq.2 r.2‖)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _pq ∈ dyadicPairs (Pseq Jb) (Qseq Jb), B := Finset.sum_le_sum hpair
    _ = ((dyadicPairs (Pseq Jb) (Qseq Jb)).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## §4 — the `𝒯_L` branch at `(χ, t)`

MR §8.3 p.29's `𝒯_L` (the pairs where the prime block factor is LARGE), retyped.  The count
is the hybrid Lemma 6.5 at `qT`; the decay is the `χ`-twisted Lemma 11 — the named socket
`HalaszPrimesChi`, wave P-6-CORE's `halasz_primes_chi`.  **LAW #253**: `hκ30` and the kill
gate stay in-statement at every rung. -/

/-- **`𝒯_L` at `(χ, t)`**: the pairs of a per-fibre well-spaced `ℰ` at which the `χ̄`-twisted
prime block polynomial `Q_{j,H}(χ̄, 1+it)` EXCEEDS the split level `δ'`. -/
noncomputable def tLsetChi (q : ℕ) (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (δ' : ℝ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) : Finset (DirichletCharacter ℂ q × ℝ) :=
  ℰ.filter (fun r => δ' < ‖ramQ H P Q j (chiBarCoeff q r.1 c) r.2‖)

lemma tLsetChi_subset (q : ℕ) (H : ℝ) (P Q j : ℕ) (c : ℕ → ℂ) (δ' : ℝ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) : tLsetChi q H P Q j c δ' ℰ ⊆ ℰ :=
  Finset.filter_subset _ _

lemma mem_tLsetChi {q : ℕ} {H : ℝ} {P Q j : ℕ} {c : ℕ → ℂ} {δ' : ℝ}
    {ℰ : Finset (DirichletCharacter ℂ q × ℝ)} {r : DirichletCharacter ℂ q × ℝ}
    (hr : r ∈ tLsetChi q H P Q j c δ' ℰ) :
    r ∈ ℰ ∧ δ' < ‖ramQ H P Q j (chiBarCoeff q r.1 c) r.2‖ := by
  rw [tLsetChi, Finset.mem_filter] at hr
  exact hr

lemma tLsetChi_fibreWellSpaced {q : ℕ} {H : ℝ} {P Q j : ℕ} {c : ℕ → ℂ} {δ' : ℝ}
    {ℰ : Finset (DirichletCharacter ℂ q × ℝ)} (hws : FibreWellSpaced ℰ) :
    FibreWellSpaced (tLsetChi q H P Q j c δ' ℰ) :=
  fibreWellSpaced_of_subset (tLsetChi_subset q H P Q j c δ' ℰ) hws

/-- **The raw hybrid count on the Ramaré block (the pair analogue of `ramQ_large_count`).**
`hybrid_large_value_count` at the block's own dyadic base `ramQbase`, through the composed
CATCH #B ∘ N1 bridge.  Gates carried verbatim at the height `qT`, `hκ30` included (the X₀
law, #253). -/
theorem ramQChi_large_count (q : ℕ) [NeZero q] {H : ℝ} (hH : 2 ≤ H) (P Q j : ℕ) (c : ℕ → ℂ)
    (hc1 : ∀ n : ℕ, ‖c n‖ ≤ 1) (T V : ℝ)
    (hB3 : 3 ≤ ramQbase H P j) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hBT : (ramQbase H P j : ℝ) ≤ (q : ℝ) * T) (hV : 1 ≤ V)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log (ramQbase H P j))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hlb : ∀ r ∈ ℰ, V⁻¹ ≤ ‖ramQ H P Q j (chiBarCoeff q r.1 c) r.2‖) :
    (ℰ.card : ℝ)
      ≤ 1680 * ((q : ℝ) * T) ^ (2 * Real.log V / Real.log (ramQbase H P j)) * V ^ 2
          * Real.exp (2 * (Real.log ((q : ℝ) * T) / Real.log (ramQbase H P j))
              * Real.log (Real.log ((q : ℝ) * T))) := by
  set B := ramQbase H P j with hBdef
  set src : ℕ → ℂ := fun n => ramQsrc H P Q j c n / (n : ℂ) with hsrcdef
  have hN : ∀ p ∈ ramQblock H P Q j, p ≤ 2 * B := fun p hp => ramQblock_le_two_base hH hp
  have hsupp : ∀ m, src m ≠ 0 → m.Prime ∧ B ≤ m := by
    intro m hm
    by_cases hmem : m ∈ ramQblock H P Q j
    · exact ⟨ramQblock_prime hmem, ramQbase_le_of_mem hmem⟩
    · exact absurd (by simp only [hsrcdef, ramQsrc_eq_zero hmem, zero_div]) hm
  have hcoeff : ∀ m, src m ≠ 0 → ‖src m‖ ≤ (m : ℝ)⁻¹ := by
    intro m hm
    obtain ⟨hpr, _⟩ := hsupp m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hpr.pos
    by_cases hmem : m ∈ ramQblock H P Q j
    · simp only [hsrcdef, ramQsrc, if_pos hmem, norm_div, Complex.norm_natCast]
      rw [inv_eq_one_div]
      gcongr
      exact hc1 m
    · exact absurd (by simp only [hsrcdef, ramQsrc_eq_zero hmem, zero_div]) hm
  have hlb' : ∀ r ∈ reflectChi ℰ,
      V⁻¹ ≤ ‖dpolyChi q (Finset.Icc 1 (2 * B)) src r.1 r.2‖ := by
    intro r hr
    have hmem := mem_reflectChi.mp hr
    have h := hlb _ hmem
    rw [ramQ_chiBar_eq_dpolyChi q r.1⁻¹ H P Q (2 * B) j c hN (-r.2)] at h
    simpa [hsrcdef] using h
  have h := hybrid_large_value_count q B src T V hB3 hT1 hqT hBT hV hκ30 hLL5
    (reflectChi ℰ) (fibreWellSpaced_reflectChi hws) (reflectChi_subset_Icc hsub)
    hsupp hcoeff hlb'
  rwa [card_reflectChi] at h

/-- **The `T`-free shape (MR Step 0), hybrid.**  With `log(qT) ≤ L` the count loses all
height dependence: `|ℰ| ≤ 1680·V²·exp(2(L/log base)(log V + log L))`.  At the §8.3 pin
(`base ≈ exp(L^{1−θ})`, `V = L^{100}`) this is `exp(L^{θ+o(1)})`. -/
theorem ramQChi_large_count_Tfree (q : ℕ) [NeZero q] {H : ℝ} (hH : 2 ≤ H) (P Q j : ℕ)
    (c : ℕ → ℂ) (hc1 : ∀ n : ℕ, ‖c n‖ ≤ 1) (T V L : ℝ)
    (hB3 : 3 ≤ ramQbase H P j) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hBT : (ramQbase H P j : ℝ) ≤ (q : ℝ) * T) (hV : 1 ≤ V)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log (ramQbase H P j))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (hTL : Real.log ((q : ℝ) * T) ≤ L)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hlb : ∀ r ∈ ℰ, V⁻¹ ≤ ‖ramQ H P Q j (chiBarCoeff q r.1 c) r.2‖) :
    (ℰ.card : ℝ)
      ≤ 1680 * V ^ 2 * Real.exp (2 * (L / Real.log (ramQbase H P j))
          * (Real.log V + Real.log L)) := by
  have hraw := ramQChi_large_count q hH P Q j c hc1 T V hB3 hT1 hqT hBT hV hκ30 hLL5
    ℰ hws hsub hlb
  set S : ℝ := (q : ℝ) * T with hSdef
  set W := Real.log (ramQbase H P j) with hWdef
  have hS0 : (0 : ℝ) < S := by linarith
  have hlogS0 : 0 < Real.log S := Real.log_pos hqT
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log S) := by linarith
  have hW0 : 0 < W := by
    rw [hWdef]
    refine Real.log_pos ?_
    have : (3 : ℝ) ≤ (ramQbase H P j : ℝ) := by exact_mod_cast hB3
    linarith
  have hlogV0 : 0 ≤ Real.log V := Real.log_nonneg hV
  have hL0 : 0 < L := by linarith
  have hlogL : Real.log (Real.log S) ≤ Real.log L := Real.log_le_log hlogS0 hTL
  have hpow : S ^ (2 * Real.log V / W) = Real.exp (2 * Real.log V / W * Real.log S) := by
    rw [Real.rpow_def_of_pos hS0]; ring_nf
  have hleg1 : S ^ (2 * Real.log V / W) ≤ Real.exp (2 * (L / W) * Real.log V) := by
    rw [hpow]
    refine Real.exp_le_exp.mpr ?_
    have hc : (0 : ℝ) ≤ 2 * Real.log V / W := by positivity
    calc 2 * Real.log V / W * Real.log S
        ≤ 2 * Real.log V / W * L := mul_le_mul_of_nonneg_left hTL hc
      _ = 2 * (L / W) * Real.log V := by ring
  have hleg2 : Real.exp (2 * (Real.log S / W) * Real.log (Real.log S))
      ≤ Real.exp (2 * (L / W) * Real.log L) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : Real.log S / W ≤ L / W := by gcongr
    have h2 : (0 : ℝ) ≤ Real.log S / W := by positivity
    nlinarith
  have hV0 : (0 : ℝ) < V := by linarith
  calc (ℰ.card : ℝ)
      ≤ 1680 * S ^ (2 * Real.log V / W) * V ^ 2
          * Real.exp (2 * (Real.log S / W) * Real.log (Real.log S)) := hraw
    _ ≤ 1680 * Real.exp (2 * (L / W) * Real.log V) * V ^ 2
          * Real.exp (2 * (L / W) * Real.log L) := by gcongr
    _ = 1680 * V ^ 2 * Real.exp (2 * (L / W) * (Real.log V + Real.log L)) := by
        rw [show 2 * (L / W) * (Real.log V + Real.log L)
              = 2 * (L / W) * Real.log V + 2 * (L / W) * Real.log L from by ring,
          Real.exp_add]
        ring

/-- **THE NAMED SLOT — the `χ`-twisted MR Lemma 11 (`halasz_primes_chi`, wave P-6-CORE's
stone C).**  The landed `halasz_primes_pow` with: the index set a per-fibre well-spaced set
of PAIRS; the integrand `Σ_{p ∈ S} p^{−it}·χ̄(p)·a_p` (the `σ = 1` sign convention — no
reflection: `ramQ_chiBar_eq_halaszSum` is sign-free); and the Vinogradov–Korobov decay
denominator read at the HYBRID height `qT`.

Reading the denominator at `qT` rather than `T` makes this the WEAKER hypothesis (a larger
denominator is a weaker decay), so a landed `halasz_primes_chi` at the sharper `log T`
discharges it by monotonicity of the bound in the denominator.  P-7 connects them; nothing
in this file depends on which form P-6-CORE delivers. -/
def HalaszPrimesChi (C c T₀ : ℝ) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
  ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
    (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
  ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
  ∀ (a : ℕ → ℂ),
    ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * Complex.I) * chiBarCoeff q r.1 a n‖ ^ 2
      ≤ C * (P + (ℰ.card : ℝ) * P
              * Real.exp (-c * Real.log P
                  / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                      * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
              * (Real.log ((q : ℝ) * T)) ^ 2)
          / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2

/-- **U-8c, `χ`-LIFTED — the twisted Lemma 11 on the Ramaré block.**  The socket
`HalaszPrimesChi` instantiated at `S = ramQblock H P Q j`, `a_p = c_p/p`,
`P = ramQbase H P j`: for any per-fibre well-spaced `ℰ ⊆ (characters) × [−T,T]`,

`Σ_{(χ,t)∈ℰ} ‖Q_{j,H}(χ̄, 1+it)‖² ≤ C·(B + |ℰ|·B·exp(−c log B/((log qT)^{3/4}(loglog qT)⁴))
  ·(log qT)²)/log B · Σ_{p∈block}‖c_p/p‖²`.

Sign convention: `σ = 1` on both sides, no reflection (the socket's integrand already
carries `p^{−it}`). -/
theorem tLChi_sumsq_ramQ {C c T₀ : ℝ} (hslot : HalaszPrimesChi C c T₀) (q : ℕ) (hq : 0 < q)
    {H : ℝ} (hH : 2 ≤ H) (P Q j : ℕ) (cf : ℕ → ℂ) (T : ℝ) (hT : T₀ ≤ T)
    (hB2 : (2 : ℝ) ≤ (ramQbase H P j : ℝ)) (hBT10 : (ramQbase H P j : ℝ) ≤ T ^ 10)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) :
    ∑ r ∈ ℰ, ‖ramQ H P Q j (chiBarCoeff q r.1 cf) r.2‖ ^ 2
      ≤ C * ((ramQbase H P j : ℝ) + (ℰ.card : ℝ) * (ramQbase H P j : ℝ)
              * Real.exp (-c * Real.log (ramQbase H P j)
                  / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                      * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
              * (Real.log ((q : ℝ) * T)) ^ 2)
          / Real.log (ramQbase H P j)
          * ∑ p ∈ ramQblock H P Q j, ‖cf p / (p : ℂ)‖ ^ 2 := by
  have hS : ∀ n ∈ ramQblock H P Q j,
      n.Prime ∧ (ramQbase H P j : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (ramQbase H P j : ℝ) := by
    intro n hn
    refine ⟨ramQblock_prime hn, ?_, ?_⟩
    · exact_mod_cast ramQbase_le_of_mem hn
    · have := ramQblock_le_two_base hH hn
      have hcast : (n : ℝ) ≤ ((2 * ramQbase H P j : ℕ) : ℝ) := by exact_mod_cast this
      rwa [Nat.cast_mul, Nat.cast_ofNat] at hcast
  have h := hslot q hq T (ramQbase H P j : ℝ) hT hB2 hBT10 ℰ hws hsub
    (ramQblock H P Q j) hS (fun p => cf p / (p : ℂ))
  have hcongr : ∑ r ∈ ℰ, ‖ramQ H P Q j (chiBarCoeff q r.1 cf) r.2‖ ^ 2
      = ∑ r ∈ ℰ, ‖∑ n ∈ ramQblock H P Q j, (n : ℂ) ^ (-(r.2 : ℂ) * Complex.I)
          * chiBarCoeff q r.1 (fun m => cf m / (m : ℂ)) n‖ ^ 2 :=
    Finset.sum_congr rfl (fun r _ => by rw [ramQ_chiBar_eq_halaszSum])
  rw [hcongr]
  exact h

set_option maxHeartbeats 800000 in
-- The `𝒯_L` kill composes four large in-statement expressions (the count, the VK decay,
-- the bracket and the coefficient mass); abbreviating them with `set` is not enough to keep
-- the unifier inside the default budget, so this rung and the exit below raise it.
/-- **U-8e, `χ`-LIFTED (the `Q`-side, killed).**  The twisted Lemma 11 on `𝒯_L` with the
hybrid Lemma-6.5 count fed into the Vinogradov–Korobov decay: the `|𝒯_L|` term dies, leaving

`Σ_{(χ,t)∈𝒯_L} ‖Q_{j,H}(χ̄, 1+it)‖² ≤ 3C·(Σ_{p∈block} 1/p)/log base`

— the `P/log P` shape of Lemma 11 with the prime-window gain already exposed.  Every
growing-quantity gate is in-statement (law #253): `hκ30`, `hLL5`, and the kill gate
`420·L·L^{3/4}(log L)^5 ≤ c·W²` at `L ≥ log(qT)`.  The kill arithmetic is the LANDED
`tL_kill`, instantiated at the height `qT` — the only change from `q = 1` is the argument.

**THE ONE CONSTANT DEBIT.**  Lemma 6.5's hybrid constant is `1680 = 2·840` (the bracket
domination `φ(q)(T+1) + φ(q)(2P)^k/q ≤ 2(qT + (2P)^k)`), so the landed `tL_kill` — whose
conclusion is at `840` — gives `|𝒯_L|·decay·(log qT)² ≤ 2`, not `≤ 1`.  The bracket therefore
collapses to `3·base` instead of `2·base` and the exit constant is `3C` where the `q = 1`
rung had `2C`.  Nothing else moves; downstream (`USetBalance.block_sum_bound`) absorbs it by
reading `Cq := 3C/2`. -/
theorem tLChi_ramQ_sumsq_killed {C c T₀ : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hslot : HalaszPrimesChi C c T₀)
    (q : ℕ) [NeZero q] {H : ℝ} (hH : 2 ≤ H) (P Q j : ℕ) (cf : ℕ → ℂ)
    (hcf1 : ∀ n : ℕ, ‖cf n‖ ≤ 1) (T V L δ' : ℝ) (ℰ : Finset (DirichletCharacter ℂ q × ℝ))
    (hws : FibreWellSpaced ℰ) (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hT₀T : T₀ ≤ T) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hB3 : 3 ≤ ramQbase H P j) (hBT : (ramQbase H P j : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log (ramQbase H P j))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T))) (hV1 : 1 ≤ V) (hVδ : V⁻¹ ≤ δ')
    (hBT10 : (ramQbase H P j : ℝ) ≤ T ^ 10)
    (hTL : Real.log ((q : ℝ) * T) ≤ L) (hlogT1 : 1 ≤ Real.log ((q : ℝ) * T))
    (hLe : Real.exp 1 ≤ L) (hWL : Real.log (ramQbase H P j) ≤ L)
    (hlogV : Real.log V ≤ 100 * Real.log L)
    (hgate : 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
      ≤ c * (Real.log (ramQbase H P j)) ^ 2) :
    ∑ r ∈ tLsetChi q H P Q j cf δ' ℰ, ‖ramQ H P Q j (chiBarCoeff q r.1 cf) r.2‖ ^ 2
      ≤ 3 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
          / Real.log (ramQbase H P j) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hB3R : (3 : ℝ) ≤ (ramQbase H P j : ℝ) := by exact_mod_cast hB3
  have hws' : FibreWellSpaced (tLsetChi q H P Q j cf δ' ℰ) := tLsetChi_fibreWellSpaced hws
  have hsub' : ∀ r ∈ tLsetChi q H P Q j cf δ' ℰ, r.2 ∈ Set.Icc (-T) T :=
    fun r hr => hsub r (tLsetChi_subset q H P Q j cf δ' ℰ hr)
  have hlb : ∀ r ∈ tLsetChi q H P Q j cf δ' ℰ,
      V⁻¹ ≤ ‖ramQ H P Q j (chiBarCoeff q r.1 cf) r.2‖ :=
    fun r hr => le_of_lt (lt_of_le_of_lt hVδ (mem_tLsetChi hr).2)
  have hcount := ramQChi_large_count_Tfree q hH P Q j cf hcf1 T V L hB3 hT1 hqT hBT hV1
    hκ30 hLL5 hTL (tLsetChi q H P Q j cf δ' ℰ) hws' hsub' hlb
  have hhal := tLChi_sumsq_ramQ hslot q hq hH P Q j cf T hT₀T (by linarith) hBT10
    (tLsetChi q H P Q j cf δ' ℰ) hws' hsub'
  have hkill := tL_kill (T := (q : ℝ) * T) hc hLe (by
      refine Real.log_pos ?_; linarith) hWL hV1 hlogV hlogT1 hTL (by linarith) hgate
  -- the abbreviations: the height, the base and its log, the count, the decay, the mass
  set S : ℝ := (q : ℝ) * T with hSdef
  set Bb : ℝ := (ramQbase H P j : ℝ) with hBbdef
  set W : ℝ := Real.log (ramQbase H P j) with hWdef
  set K : ℝ := ((tLsetChi q H P Q j cf δ' ℰ).card : ℝ) with hKdef
  set E : ℝ := Real.exp (-c * Real.log (ramQbase H P j)
      / ((Real.log S) ^ ((3 : ℝ) / 4) * (Real.log (Real.log S)) ^ (4 : ℕ))) with hEdef
  set mass : ℝ := ∑ p ∈ ramQblock H P Q j, ‖cf p / (p : ℂ)‖ ^ 2 with hmassdef
  have hW0 : 0 < W := by rw [hWdef]; refine Real.log_pos ?_; linarith
  have hB0 : (0 : ℝ) < Bb := by rw [hBbdef]; linarith
  have hE0 : (0 : ℝ) ≤ E := (Real.exp_pos _).le
  have hlogS2 : (0 : ℝ) ≤ (Real.log S) ^ 2 := sq_nonneg _
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  have hmass0 : (0 : ℝ) ≤ mass := by
    rw [hmassdef]; exact Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hWinv : (0 : ℝ) ≤ W⁻¹ := by positivity
  -- (i) the kill: `|𝒯_L|·decay·(log qT)² ≤ 2` (the `1680 = 2·840` debit)
  have hcardE : K * E * (Real.log S) ^ 2 ≤ 2 := by
    have hstep : K * E * (Real.log S) ^ 2
        ≤ (1680 * V ^ 2 * Real.exp (2 * (L / W) * (Real.log V + Real.log L)))
            * E * (Real.log S) ^ 2 := by gcongr
    linarith [hkill]
  -- (ii) the bracket collapses to `3·base`
  have hbracket : Bb + K * Bb * E * (Real.log S) ^ 2 ≤ 3 * Bb := by
    have hre : K * Bb * E * (Real.log S) ^ 2 = Bb * (K * E * (Real.log S) ^ 2) := by ring
    rw [hre]
    nlinarith
  -- (iii) the coefficient mass: `base · Σ‖c_p/p‖² ≤ Σ 1/p`
  have hA : Bb * mass ≤ ∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p := by
    rw [hmassdef, hBbdef]
    have hterm : ∀ p ∈ ramQblock H P Q j,
        ‖cf p / (p : ℂ)‖ ^ 2 ≤ (1 / (ramQbase H P j : ℝ)) * (1 / (p : ℝ)) := by
      intro p hp
      have hpr := ramQblock_prime hp
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpr.pos
      have hBp : (ramQbase H P j : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast ramQbase_le_of_mem hp
      have hnorm : ‖cf p / (p : ℂ)‖ ≤ 1 / (p : ℝ) := by
        rw [norm_div, Complex.norm_natCast, inv_eq_one_div] at *
        gcongr
        exact hcf1 p
      have hnn : (0 : ℝ) ≤ ‖cf p / (p : ℂ)‖ := norm_nonneg _
      have hsq : ‖cf p / (p : ℂ)‖ ^ 2 ≤ (1 / (p : ℝ)) ^ 2 := by nlinarith
      have hfin : (1 / (p : ℝ)) ^ 2 ≤ (1 / (ramQbase H P j : ℝ)) * (1 / (p : ℝ)) := by
        have h1 : (1 / (p : ℝ)) ^ 2 = 1 / ((p : ℝ) * (p : ℝ)) := by ring
        have h2 : (1 / (ramQbase H P j : ℝ)) * (1 / (p : ℝ))
            = 1 / ((ramQbase H P j : ℝ) * (p : ℝ)) := by ring
        rw [h1, h2]
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
      linarith
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    have hB0' : (0 : ℝ) < (ramQbase H P j : ℝ) := by linarith
    calc (ramQbase H P j : ℝ) * (∑ p ∈ ramQblock H P Q j, ‖cf p / (p : ℂ)‖ ^ 2)
        ≤ (ramQbase H P j : ℝ)
            * ((1 / (ramQbase H P j : ℝ)) * ∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt hB0')
      _ = ∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p := by field_simp
  -- (iv) assemble, dividing by `W` and multiplying by the mass by hand (no `gcongr`
  -- on the composed expression: the unifier does not need to see it twice)
  have hnum : C * (Bb + K * Bb * E * (Real.log S) ^ 2) ≤ C * (3 * Bb) :=
    mul_le_mul_of_nonneg_left hbracket hC
  have hdiv : C * (Bb + K * Bb * E * (Real.log S) ^ 2) / W ≤ C * (3 * Bb) / W := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum hWinv
  have hfirst : C * (Bb + K * Bb * E * (Real.log S) ^ 2) / W * mass
      ≤ C * (3 * Bb) / W * mass := mul_le_mul_of_nonneg_right hdiv hmass0
  have hsecond : C * (3 * Bb) / W * mass
      ≤ 3 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p) / W := by
    have hstep : (3 : ℝ) * C * (Bb * mass) ≤ 3 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p) :=
      mul_le_mul_of_nonneg_left hA (by linarith)
    have hstep' : (3 : ℝ) * C * (Bb * mass) * W⁻¹
        ≤ 3 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p) * W⁻¹ :=
      mul_le_mul_of_nonneg_right hstep hWinv
    have hrw1 : C * (3 * Bb) / W * mass = 3 * C * (Bb * mass) * W⁻¹ := by
      rw [div_eq_mul_inv]; ring
    have hrw2 : (3 : ℝ) * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p) * W⁻¹
        = 3 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p) / W := by
      rw [div_eq_mul_inv]
    rw [hrw1, ← hrw2]
    exact hstep'
  exact le_trans hhal (le_trans hfirst hsecond)

set_option maxHeartbeats 800000 in
-- Same cause as the rung above: the composed `𝒯_L` expression is large.
/-- **U-8, `χ`-LIFTED — THE `𝒯_L` EXIT.**  With the pointwise co-factor bound
`‖R_{j,H}(χ̄, 1+it)‖ ≤ Rbd` on `𝒯_L` (carried as a hypothesis — it is not a `𝒰`-property),

`Σ_{(χ,t)∈𝒯_L} ‖Q_{j,H}(χ̄)·R_{j,H}(χ̄)‖² ≤ 81·C·Rbd²·(H/j)² = 81·C·Rbd²/v²`

at the block height `v = j/H`: the Lemma-11 mass `1/log base` and the prime-window gain
`Σ_{p∈block}1/p ≍ 1/v` each contribute one factor `1/v` (MR p.29's "extra logarithm").  The
prime-window gain (`ramQblock_inv_sum_le`) is character-free and reused verbatim.

`81 = 3·27` is the `q = 1` rung's `54 = 2·27` at the hybrid count's `1680 = 2·840` debit;
`USetBalance.block_sum_bound` consumes it verbatim at `Cq := 3C/2`. -/
theorem tLChi_main_sumsq {C c T₀ : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hslot : HalaszPrimesChi C c T₀) (q : ℕ) [NeZero q] {H : ℝ} (hH : 2 ≤ H)
    (P Q j N X : ℕ) (cf bb : ℕ → ℂ)
    (hcf1 : ∀ n : ℕ, ‖cf n‖ ≤ 1) (hHj : H ≤ (j : ℝ))
    (T V L δ' Rbd : ℝ) (ℰ : Finset (DirichletCharacter ℂ q × ℝ))
    (hws : FibreWellSpaced ℰ) (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hT₀T : T₀ ≤ T) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hB3 : 3 ≤ ramQbase H P j) (hBT : (ramQbase H P j : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log (ramQbase H P j))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T))) (hV1 : 1 ≤ V) (hVδ : V⁻¹ ≤ δ')
    (hBT10 : (ramQbase H P j : ℝ) ≤ T ^ 10)
    (hTL : Real.log ((q : ℝ) * T) ≤ L) (hlogT1 : 1 ≤ Real.log ((q : ℝ) * T))
    (hLe : Real.exp 1 ≤ L) (hWL : Real.log (ramQbase H P j) ≤ L)
    (hlogV : Real.log V ≤ 100 * Real.log L)
    (hgate : 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
      ≤ c * (Real.log (ramQbase H P j)) ^ 2)
    (hRbd : 0 ≤ Rbd)
    (hR : ∀ r ∈ tLsetChi q H P Q j cf δ' ℰ,
      ‖ramR H N X P Q j (chiBarCoeff q r.1 bb) r.2‖ ≤ Rbd) :
    ∑ r ∈ tLsetChi q H P Q j cf δ' ℰ,
        ‖ramMain H N X P Q (chiBarCoeff q r.1 bb) (chiBarCoeff q r.1 cf) j r.2‖ ^ 2
      ≤ 81 * C * Rbd ^ 2 * (H / (j : ℝ)) ^ 2 := by
  have hQ := tLChi_ramQ_sumsq_killed (le_of_lt hC) hc hslot q hH P Q j cf hcf1 T V L δ' ℰ
    hws hsub hT₀T
    hT1 hqT hB3 hBT hκ30 hLL5 hV1 hVδ hBT10 hTL hlogT1 hLe hWL hlogV hgate
  have hB1 : (1 : ℝ) < (ramQbase H P j : ℝ) := by
    have : (3 : ℝ) ≤ (ramQbase H P j : ℝ) := by exact_mod_cast hB3
    linarith
  have hW0 : 0 < Real.log (ramQbase H P j) := Real.log_pos hB1
  have hH0 : (0 : ℝ) < H := by linarith
  have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
  have hWv : (j : ℝ) / H ≤ Real.log (ramQbase H P j) := by
    have h1 := Real.log_le_log (Real.exp_pos ((j : ℝ) / H)) (exp_le_ramQbase H P j)
    rwa [Real.log_exp] at h1
  have hvpos : (0 : ℝ) < (j : ℝ) / H := by positivity
  -- the pointwise `R` factor
  have hsplit : ∑ r ∈ tLsetChi q H P Q j cf δ' ℰ,
        ‖ramMain H N X P Q (chiBarCoeff q r.1 bb) (chiBarCoeff q r.1 cf) j r.2‖ ^ 2
      ≤ Rbd ^ 2 * ∑ r ∈ tLsetChi q H P Q j cf δ' ℰ,
          ‖ramQ H P Q j (chiBarCoeff q r.1 cf) r.2‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun r hr => ?_)
    have hnorm : ‖ramMain H N X P Q (chiBarCoeff q r.1 bb) (chiBarCoeff q r.1 cf) j r.2‖ ^ 2
        = ‖ramQ H P Q j (chiBarCoeff q r.1 cf) r.2‖ ^ 2
          * ‖ramR H N X P Q j (chiBarCoeff q r.1 bb) r.2‖ ^ 2 := by
      rw [ramMain, norm_mul, mul_pow]
    rw [hnorm]
    have h1 : ‖ramR H N X P Q j (chiBarCoeff q r.1 bb) r.2‖ ^ 2 ≤ Rbd ^ 2 := by
      have := hR r hr
      nlinarith [norm_nonneg (ramR H N X P Q j (chiBarCoeff q r.1 bb) r.2)]
    have h2 : (0 : ℝ) ≤ ‖ramQ H P Q j (chiBarCoeff q r.1 cf) r.2‖ ^ 2 := sq_nonneg _
    nlinarith
  -- the prime-window gain and `1/log base ≤ H/j`
  have hgain := ramQblock_inv_sum_le (H := H) hH (P := P) (Q := Q) (j := j) hHj
  have hnn : (0 : ℝ) ≤ ∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p :=
    Finset.sum_nonneg (fun p _ => by positivity)
  have hinvW : 1 / Real.log (ramQbase H P j) ≤ H / (j : ℝ) := by
    have h1 : 1 / Real.log (ramQbase H P j) ≤ 1 / ((j : ℝ) / H) :=
      one_div_le_one_div_of_le hvpos hWv
    have h2 : 1 / ((j : ℝ) / H) = H / (j : ℝ) := by field_simp
    linarith
  have hstep : 3 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
        / Real.log (ramQbase H P j)
      ≤ 81 * C * (H / (j : ℝ)) ^ 2 := by
    have hform : 3 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
          / Real.log (ramQbase H P j)
        = 3 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
            * (1 / Real.log (ramQbase H P j)) := by ring
    rw [hform]
    have h1 : 3 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
          * (1 / Real.log (ramQbase H P j))
        ≤ 3 * C * (27 * H / (j : ℝ)) * (H / (j : ℝ)) := by
      have hCnn : (0 : ℝ) ≤ 3 * C := by linarith
      have hA : 3 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
          ≤ 3 * C * (27 * H / (j : ℝ)) := mul_le_mul_of_nonneg_left hgain hCnn
      have hB : (0 : ℝ) ≤ 3 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p) := by positivity
      have hinv0 : (0 : ℝ) ≤ 1 / Real.log (ramQbase H P j) := by positivity
      nlinarith
    have h2 : 3 * C * (27 * H / (j : ℝ)) * (H / (j : ℝ))
        = 81 * C * (H / (j : ℝ)) ^ 2 := by ring
    linarith
  calc ∑ r ∈ tLsetChi q H P Q j cf δ' ℰ,
        ‖ramMain H N X P Q (chiBarCoeff q r.1 bb) (chiBarCoeff q r.1 cf) j r.2‖ ^ 2
      ≤ Rbd ^ 2 * ∑ r ∈ tLsetChi q H P Q j cf δ' ℰ,
          ‖ramQ H P Q j (chiBarCoeff q r.1 cf) r.2‖ ^ 2 := hsplit
    _ ≤ Rbd ^ 2 * (3 * C * (∑ p ∈ ramQblock H P Q j, (1 : ℝ) / p)
          / Real.log (ramQbase H P j)) := mul_le_mul_of_nonneg_left hQ (by positivity)
    _ ≤ Rbd ^ 2 * (81 * C * (H / (j : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = 81 * C * Rbd ^ 2 * (H / (j : ℝ)) ^ 2 := by ring

end Salt.MR
