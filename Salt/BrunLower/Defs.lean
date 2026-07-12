/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The Brun block-truncation carriers (blueprint `p0`, node B0)

Definitions for the both-sided Brun sieve of Halberstam–Richert, *A new look at
Brun's sieve*, Mém. SMF **25** (1971) 97–106 (numdam `10.24033/msmf.39`),
Théorème 2 and its proof (2.9)–(2.14).  The possibility-side keystone of the
twin-prime ladder (`docs/blueprints/p0.md`).

Contents:

* `bigLambda A lam = 2λ/A` — the ladder scale (the `e^{−nλ}` form is the `A = 2`
  specialisation only; flags #16 item 2).  The ladder `zLev` is parameterised by
  `Λ` directly, with `bigLambda` the H-R value.
* `zLev Λ z n = exp(e^{−nΛ} · log z)` — the partition (2.13), `z₀ = z` at the top,
  decreasing to the bottom `z_r = 2`; `minLevel` is the minimal `r` with `z_r ≤ 2`
  characterised by (2.14) `e^{rΛ} ≥ (log z)/(log 2)`.
* `chi Λ z side b d` — the block predicate `χ_ν(d)` of (2.10), `side = ν ∈ {1,2}`.
* the structural rules (2.1)–(2.4): `chi_one`, `chi_dvd_closed`, `chi_prime`,
  `chi_add_smaller_prime`.
* `W s` — the density product `W(z) = ∏_{p<z}(1 − ω(p)/p)` over a `BoundingSieve`.

## The block predicate: the restricted-count reading (load-bearing)

H-R's `χ_ν(d)` is stated in (2.10) via `d ∣ P(z_n, z) → Ω(d) ≤ 2b−ν+2n−1`.  The
**operative** meaning — the one for which the paper's own structural rules
(2.1)–(2.4) hold — is the *restricted count* form: for **every** level `n ≥ 1`,
the number of prime factors of `d` lying in `[z_n, z)` (`= Ω((d, P(z_n,z)))`) is
`≤ 2b−ν+2n−1`.  Formalised here as `chi` via `bigOmegaGe` (= that restricted
count).

The naive "all-of-`d`" reading — *`∀n`, if every prime of `d` is `≥ z_n` then the
full `Ω(d) ≤ 2b−ν+2n−1`* — is **NOT** divisor-closed (it fails (2.2)):
e.g. with `b=1, ν=1`, take `d = q₁q₂q₃q₄` with `q₁` at ladder level `3` and
`q₂,q₃,q₄` at level `1`; then the all-of-`d` reading makes `χ₁(d)=1` (its binding
level is `3`, `Ω(d)=4 ≤ 2·1−1+2·3−1=6`) yet `χ₁(t)=0` for `t=q₂q₃q₄` (binding
level `1`, `Ω(t)=3 > 2·1−1+2·1−1=2`), violating `χ(d)=1 ⇒ χ(t)=1`.  The restricted
form is monotone under divisors, so (2.2) is immediate.  The all-of-`d`
implication is recovered here only as a *consequence* (`chi_imp_windowed`); the
converse is false.  See `docs/blueprints/p0.md` (line 23) and flags #15/#16.

`side` (not `nu`) names the H-R index `ν ∈ {1,2}` to avoid the clash with
mathlib's `BoundingSieve.nu = ω/p`.
-/

open Finset Nat ArithmeticFunction

namespace Salt.BrunLower

/-! ## The ladder (H-R (2.13)–(2.14)) -/

/-- The H-R ladder scale `Λ = 2λ/A` (general).  The `e^{−nλ}` form is the `A = 2`
specialisation, since `bigLambda 2 lam = lam`. -/
noncomputable def bigLambda (A lam : ℝ) : ℝ := 2 * lam / A

@[simp] lemma bigLambda_two (lam : ℝ) : bigLambda 2 lam = lam := by
  unfold bigLambda; ring

/-- The partition (2.13): `z_n = exp(e^{−nΛ} · log z)`, i.e. `log z_n = e^{−nΛ} log z`.
Parameterised by `Λ = Lam` directly; the H-R value is `Lam = bigLambda A lam = 2λ/A`. -/
noncomputable def zLev (Lam z : ℝ) (n : ℕ) : ℝ :=
  Real.exp (Real.exp (-((n : ℝ) * Lam)) * Real.log z)

/-- `z₀ = z`: the top of the ladder. -/
lemma zLev_zero (Lam z : ℝ) (hz : 0 < z) : zLev Lam z 0 = z := by
  unfold zLev; simp [Real.exp_log hz]

/-- The ladder is antitone in the level index (`Λ ≥ 0`, `z ≥ 1`): `z₀ = z ≥ z₁ ≥ …`. -/
lemma zLev_antitone {Lam z : ℝ} (hLam : 0 ≤ Lam) (hz : 1 ≤ z) : Antitone (zLev Lam z) := by
  intro m n hmn
  simp only [zLev]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hz)
  apply Real.exp_le_exp.mpr
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  nlinarith [hLam]

/-- The level characterisation (2.14): `z_n ≤ 2 ↔ e^{nΛ} ≥ (log z)/(log 2)`. -/
lemma zLev_le_two_iff (Lam z : ℝ) (n : ℕ) (hz : 1 < z) :
    zLev Lam z n ≤ 2 ↔ Real.log z / Real.log 2 ≤ Real.exp ((n : ℝ) * Lam) := by
  have hlz : 0 < Real.log z := Real.log_pos hz
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : 0 < Real.exp ((n : ℝ) * Lam) := Real.exp_pos _
  unfold zLev
  conv_lhs => rw [show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm]
  rw [Real.exp_le_exp, Real.exp_neg, inv_mul_le_iff₀ hexp, div_le_iff₀ hl2]

/-- Some ladder level has value `≤ 2` (`Λ > 0`, `z > 1`): the ladder reaches the bottom. -/
lemma exists_zLev_le_two {Lam z : ℝ} (hLam : 0 < Lam) (hz : 1 < z) :
    ∃ n : ℕ, 1 ≤ n ∧ zLev Lam z n ≤ 2 := by
  have hlz : 0 < Real.log z := Real.log_pos hz
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_ge ((Real.log z / Real.log 2 - 1) / Lam)
  have hzn : zLev Lam z n ≤ 2 := by
    rw [zLev_le_two_iff Lam z n hz]
    have h1 : Real.log z / Real.log 2 - 1 ≤ (n : ℝ) * Lam := by
      rw [div_le_iff₀ hLam] at hn; linarith
    calc Real.log z / Real.log 2 = (Real.log z / Real.log 2 - 1) + 1 := by ring
      _ ≤ (n : ℝ) * Lam + 1 := by linarith
      _ ≤ Real.exp ((n : ℝ) * Lam) := by have := Real.add_one_le_exp ((n : ℝ) * Lam); linarith
  exact ⟨max n 1, le_max_right _ _,
    le_trans (zLev_antitone hLam.le hz.le (le_max_left n 1)) hzn⟩

/-- The bottom of the ladder: the least level `r ≥ 1` with `z_r ≤ 2` (H-R sets `z_r = 2`).
Junk value `0` if no such level exists (never, for `Λ > 0`, `z > 1`). -/
noncomputable def minLevel (Lam z : ℝ) : ℕ := sInf {n : ℕ | 1 ≤ n ∧ zLev Lam z n ≤ 2}

lemma minLevel_mem {Lam z : ℝ} (hLam : 0 < Lam) (hz : 1 < z) :
    1 ≤ minLevel Lam z ∧ zLev Lam z (minLevel Lam z) ≤ 2 := by
  have hne : {n : ℕ | 1 ≤ n ∧ zLev Lam z n ≤ 2}.Nonempty := by
    obtain ⟨n, h1, h2⟩ := exists_zLev_le_two hLam hz; exact ⟨n, h1, h2⟩
  exact Nat.sInf_mem hne

/-- `r` is minimal: any level `n ≥ 1` with `z_n ≤ 2` has `n ≥ minLevel`. -/
lemma minLevel_le {Lam z : ℝ} {n : ℕ} (hn : 1 ≤ n) (hz2 : zLev Lam z n ≤ 2) :
    minLevel Lam z ≤ n := Nat.sInf_le ⟨hn, hz2⟩

/-- The ladder bottom `z_r ≤ 2` (H-R sets `z_r = 2`). -/
lemma zLev_minLevel_le_two {Lam z : ℝ} (hLam : 0 < Lam) (hz : 1 < z) :
    zLev Lam z (minLevel Lam z) ≤ 2 := (minLevel_mem hLam hz).2

/-- The minimal-`r` characterisation (2.14): `e^{rΛ} ≥ (log z)/(log 2)`. -/
lemma exp_minLevel_ge {Lam z : ℝ} (hLam : 0 < Lam) (hz : 1 < z) :
    Real.log z / Real.log 2 ≤ Real.exp ((minLevel Lam z : ℝ) * Lam) :=
  (zLev_le_two_iff Lam z _ hz).1 (zLev_minLevel_le_two hLam hz)

/-! ## The block predicate `χ_ν` (H-R (2.10)) -/

/-- The number of prime factors of `d` lying in the window `[z_n, z)` — i.e.
`Ω((d, P(z_n, z)))`, the restricted prime-factor count of H-R.  For squarefree `d`
this counts the distinct prime factors `p ∣ d` with `z_n ≤ p`. -/
noncomputable def bigOmegaGe (Lam z : ℝ) (n : ℕ) (d : ℕ) : ℕ :=
  (d.primeFactors.filter (fun p : ℕ => zLev Lam z n ≤ (p : ℝ))).card

/-- The H-R block bound `2b − ν + 2n − 1` (as an integer; `side = ν ∈ {1,2}`). -/
def blockBound (side b n : ℕ) : ℤ := 2 * (b : ℤ) - (side : ℤ) + 2 * (n : ℤ) - 1

/-- **The block predicate `χ_ν(d)` of H-R (2.10)** (restricted-count form; `side = ν`):
`χ_ν(d) = 1` iff at every ladder level `n ≥ 1` the number of prime factors of `d`
lying in `[z_n, z)` is at most `2b − ν + 2n − 1`.  This is the form for which the
structural rules (2.1)–(2.4) hold; see the module docstring on why the "all-of-`d`"
reading fails (2.2). -/
def chi (Lam z : ℝ) (side b : ℕ) (d : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → (bigOmegaGe Lam z n d : ℤ) ≤ blockBound side b n

/-- `χ_ν` is (classically) decidable — it is used as a `{0,1}` indicator in the
remainder sum `Σ_{d∣P(z)} χ_ν(d)|R_d|`. -/
noncomputable instance instDecidableChi (Lam z : ℝ) (side b d : ℕ) :
    Decidable (chi Lam z side b d) := Classical.propDecidable _

/-- The restricted count equals the full prime-factor count exactly when *every* prime
factor of `d` lies in `[z_n, z)`, i.e. `d ∣ P(z_n, z)` in H-R's notation.  This is the
bridge between the `bigOmegaGe` form and the divisibility-window form of (2.10). -/
lemma bigOmegaGe_eq_card_iff (Lam z : ℝ) (n d : ℕ) :
    bigOmegaGe Lam z n d = d.primeFactors.card ↔ ∀ p ∈ d.primeFactors, zLev Lam z n ≤ (p : ℝ) := by
  unfold bigOmegaGe
  constructor
  · intro h p hp
    have hsub : d.primeFactors.filter (fun p : ℕ => zLev Lam z n ≤ (p : ℝ)) = d.primeFactors :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) h.ge
    have hpf : p ∈ d.primeFactors.filter (fun p : ℕ => zLev Lam z n ≤ (p : ℝ)) := by
      rw [hsub]; exact hp
    exact (Finset.mem_filter.mp hpf).2
  · intro h
    rw [Finset.filter_true_of_mem h]

/-- The H-R "`d ∣ P(z_n, z) → Ω(d) ≤ 2b−ν+2n−1`" reading of (2.10) is a **consequence**
of `chi` (the restricted-count form): at any level where *all* of `d`'s prime factors
lie in `[z_n, z)`, the full count `Ω(d) = card d.primeFactors` obeys the bound.  The
converse is false (see the module docstring); this is the derived "second form". -/
lemma chi_imp_windowed {Lam z : ℝ} {side b d : ℕ} (hchi : chi Lam z side b d)
    (n : ℕ) (hn : 1 ≤ n) (hall : ∀ p ∈ d.primeFactors, zLev Lam z n ≤ (p : ℝ)) :
    (d.primeFactors.card : ℤ) ≤ blockBound side b n := by
  have h := hchi n hn
  rwa [(bigOmegaGe_eq_card_iff Lam z n d).2 hall] at h

/-! ## The structural rules (H-R (2.1)–(2.4)) -/

/-- **(2.1)** `χ_ν(1) = 1` (for `b ≥ 1`, `ν ≤ 2`): `1` has no prime factors, so every
restricted count is `0`, and `0 ≤ 2b − ν + 2n − 1` at `n ≥ 1`. -/
lemma chi_one (Lam z : ℝ) {side b : ℕ} (hb : 1 ≤ b) (hs : side ≤ 2) :
    chi Lam z side b 1 := by
  intro n hn
  have h0 : bigOmegaGe Lam z n 1 = 0 := by
    unfold bigOmegaGe; simp [Nat.primeFactors_one]
  rw [h0]
  have hn' : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hb' : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
  have hs' : (side : ℤ) ≤ 2 := by exact_mod_cast hs
  unfold blockBound
  push_cast
  linarith

/-- **(2.2)** divisor closure: `χ_ν(d) = 1` and `t ∣ d` imply `χ_ν(t) = 1`.  Immediate from
monotonicity of the restricted count under divisors (`t.primeFactors ⊆ d.primeFactors`). -/
lemma chi_dvd_closed (Lam z : ℝ) {side b d t : ℕ} (hd : d ≠ 0) (htd : t ∣ d)
    (hchi : chi Lam z side b d) : chi Lam z side b t := by
  intro n hn
  calc (bigOmegaGe Lam z n t : ℤ)
      ≤ (bigOmegaGe Lam z n d : ℤ) := by
        have : bigOmegaGe Lam z n t ≤ bigOmegaGe Lam z n d :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Nat.primeFactors_mono htd hd))
        exact_mod_cast this
    _ ≤ blockBound side b n := hchi n hn

/-- **(2.4)** `χ_ν(p) = 1` for every prime `p` (for `b ≥ 1`, `ν ≤ 2`): each restricted
count is `≤ 1 ≤ 2b − ν + 2n − 1`.  (A special case of (2.3); proved directly.) -/
lemma chi_prime (Lam z : ℝ) {side b p : ℕ} (hp : p.Prime) (hb : 1 ≤ b) (hs : side ≤ 2) :
    chi Lam z side b p := by
  intro n hn
  have hle : bigOmegaGe Lam z n p ≤ 1 := by
    unfold bigOmegaGe
    calc (p.primeFactors.filter (fun q : ℕ => zLev Lam z n ≤ (q : ℝ))).card
        ≤ p.primeFactors.card := Finset.card_filter_le _ _
      _ = 1 := by rw [hp.primeFactors]; simp
  have hle' : (bigOmegaGe Lam z n p : ℤ) ≤ 1 := by exact_mod_cast hle
  have hn' : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hb' : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
  have hs' : (side : ℤ) ≤ 2 := by exact_mod_cast hs
  unfold blockBound
  linarith

/-- **(2.3)** the Brun/Tartakovskij closure with the parity twist: if `χ_ν(t) = 1`,
`μ(t) = (−1)^ν` (i.e. `Ω(t) ≡ ν (mod 2)`, here `t.primeFactors.card % 2 = side % 2`), and
`p` is a prime smaller than every prime factor of `t`, then `χ_ν(pt) = 1`.  The parity
turns the non-strict `Ω(t) ≤ 2b−ν+2n−1` into the strict `Ω(t) < 2b−ν+2n−1` at the level
where `p` first counts, absorbing the extra factor `p`.  (`t.primeFactors.card = Ω(t)` for
squarefree `t`.) -/
lemma chi_add_smaller_prime (Lam z : ℝ) {side b p t : ℕ} (hp : p.Prime) (ht : t ≠ 0)
    (hlt : ∀ q ∈ t.primeFactors, p < q)
    (hpar : t.primeFactors.card % 2 = side % 2)
    (hchi : chi Lam z side b t) :
    chi Lam z side b (p * t) := by
  have hpnotmem : p ∉ t.primeFactors := fun hmem => (lt_irrefl p) (hlt p hmem)
  have hpf : (p * t).primeFactors = insert p t.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero ht, hp.primeFactors, Finset.insert_eq]
  intro n hn
  by_cases hpz : zLev Lam z n ≤ (p : ℝ)
  · -- `p` counts, hence so do all (larger) primes of `t`; parity gives the strict step.
    have hall : ∀ q ∈ t.primeFactors, zLev Lam z n ≤ (q : ℝ) := by
      intro q hq
      have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast (hlt q hq).le
      linarith
    have hcount : bigOmegaGe Lam z n (p * t) = t.primeFactors.card + 1 := by
      unfold bigOmegaGe
      rw [hpf, Finset.filter_insert, if_pos hpz,
        Finset.card_insert_of_notMem (fun hmem => hpnotmem (Finset.filter_subset _ _ hmem)),
        Finset.filter_true_of_mem hall]
    have hchit : (t.primeFactors.card : ℤ) ≤ blockBound side b n := by
      have h := hchi n hn
      unfold bigOmegaGe at h
      rwa [Finset.filter_true_of_mem hall] at h
    rw [hcount]
    unfold blockBound at hchit ⊢
    omega
  · -- `p` does not count: the restricted count is unchanged.
    have hcount : bigOmegaGe Lam z n (p * t) = bigOmegaGe Lam z n t := by
      unfold bigOmegaGe
      rw [hpf, Finset.filter_insert, if_neg hpz]
    rw [hcount]
    exact hchi n hn

/-! ## The density product `W(z)` -/

/-- The H-R density product `W(z) = ∏_{p<z}(1 − ω(p)/p) = ∏_{p∣P}(1 − ν(p))`, over a
`BoundingSieve`'s `nu` (`ν = ω/p`).  `p ∣ prodPrimes` ranges over the sifting primes
(`= {p < z}` when `prodPrimes = ∏_{p<z} p`, matching `Salt/Brun/Sieve.lean`). -/
noncomputable def W (s : BoundingSieve) : ℝ :=
  ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)

/-- `W(z) > 0`: every factor `1 − ν(p)` is positive (`ν(p) < 1` on `p ∣ prodPrimes`). -/
lemma W_pos (s : BoundingSieve) : 0 < W s := by
  unfold W
  apply Finset.prod_pos
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors hp
  have := s.nu_lt_one_of_prime p hpp hdvd
  linarith

end Salt.BrunLower
