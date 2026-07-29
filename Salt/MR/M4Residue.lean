/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Sec9Glue
import Salt.MR.DoorFrameH1

/-!
# `M4Residue` — M4-2: the residue split and the `d₀`-dilation

Source: Matomäki–Radziwiłł–Tao, `1503.05121v3`, **§4 step (b)** (p. 14); the campaign
freeze `docs/exploration/s9-freeze-0726.md` :59–61 and its ⟦AMENDMENT B⟧ row M4-2 (:277).

MRT's step (b) splits the inner sum over a short interval into residue classes `b mod q`,
sets `d₀ := (b, q)`, writes `n = d₀ m`, and then *dilates*:

```
      1_𝒮(d₀ m) · g(d₀ m)  =  g(d₀) · 1_{𝒮'}(m) · g(m).
```

Two facts carry it, and they are the two halves of this file.

1. **`g` is COMPLETELY multiplicative**, so `g(d₀ m) = g(d₀) g(m)` with *no* coprimality
   side condition.  At the campaign's datum `g = λ` this is `liouville_apply_mul`
   (mathlib), whose statement carries no `Coprime` hypothesis at all — the fact that
   deletes MR Theorem 2.3's Möbius layer (freeze :72–74).

2. **The block indicator does not see `d₀`.**  `𝒮` is `MemS`: "at least one prime factor
   in every block `[P_j, Q_j]`, `1 ≤ j ≤ J`".  Under the gate `d₀ ≤ q ≤ W < P₁` every
   prime factor of `d₀` lies strictly below the *bottom* block bottom `P₁`, hence below
   every `P_j`; so `d₀` contributes nothing to any `BlockPrimeDivs`, and `𝒮' = 𝒮`
   *on the nose* — the dilated block condition is the undilated one.  That is
   `memS_dilate`, the ~120-line piece the M4 plan calls the genuinely new content.

## ⟦THE GATE IS A HYPOTHESIS, NOT A COMMENT⟧ (freeze :160)

`d₀ ≤ q ≤ W < P₁` is stated, carried and discharged.  §5 discharges it at the K-family
door inhabitant `(A, G, M, Jb) = (Adoor M, 3072M, M, 2)`, where

```
      P₁ = calP (Adoor M) (3072M) 1 = 2^{Adoor M} ≥ 2^{2^18} = 2^{262144},
```

against `W = (log H)^{12}` — a comparison with `10^{78000}`-fold room
(`door_dilation_gate`).  The gate lemma consumes only `Adoor_ge` (`DoorFrame`) plus
`calE_one`/`calE_mono` (`SeamCalibration`); the closed exponent is **never evaluated**
(⟦V9c⟧ / the freeze's "`norm_num` must never see closed `calP`" trap).

## ⟦TRAP — the two `lam`s⟧

`Salt.MR.lam` (`NonPret.lean:47`) is `fun _ => -1`: the *pretentious-distance datum*,
correct only on primes, because `pretDistSq` evaluates its arguments at primes only.  It
is **not** the Liouville function, and neither is `lamChi χ = lam · χ̄`.  The honest
`λ` is `ArithmeticFunction.liouville`; `liouvilleC` below is its ℂ-cast, the thin adapter
this file lands.  Do not cross-wire the two: `lam 4 = -1` while `liouvilleC 4 = 1`.

## ⟦TRAP — `blockOmega` counts DISTINCT primes⟧

`Decomp.blockOmega P Q n = (n.primeFactors.filter (P ≤ · ∧ · ≤ Q)).card` — multiplicity
is *not* counted (`Decomp.lean:51–57`).  That is what makes the dilation identity an
equality of `Finset`s (`blockPrimeDivs_dilate`) rather than a cardinality inequality: the
prime factors of `d₀` are removed as a *set*, so no `p² ∣ n` bookkeeping arises here (the
Ramaré-weight file is where that lives).

## ⟦TRAP — three log-scales, one glyph⟧ (M4 trap sheet #8)

This file speaks **H-scale** throughout: `W = (log H)^{12}`, `log W = 12·loglog H`.  No
`loglog X` threshold appears.  The only numeral pinned against `H` is
`door_dilation_gate`'s `log H ≤ 2^{21845}`, which is `12·21845 = 262140 < 262144` — the
gate's whole content, and roomier than the door floor's `log H ≈ 9·10^{38} < 2^{130}` by
a factor of `2^{21715}`.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the Liouville factorisation: `λ(d₀ m) = λ(d₀) λ(m)`, no coprimality

The corpus already spells `λ` twice: `ArithmeticFunction.liouville` (mathlib, ℤ-valued;
used by `Salt.HB.lamR` and `Salt.Entropy.Chowla`) and — in a *different* role — the
constant `Salt.MR.lam`.  MR §4's `g` is ℂ-valued, so what the row needs is the ℂ-cast.
Everything below is a thin adapter over `liouville_apply_mul`. -/

/-- **The Liouville function as a ℂ-valued multiplicative datum**, `λ(n) = (−1)^{Ω(n)}`
for `n ≠ 0` and `λ(0) = 0`.  The ℂ-cast of `ArithmeticFunction.liouville`; the `f`-side
datum of MR §4 at the campaign's instantiation `g := λ`.

⚠ Not to be confused with `Salt.MR.lam` — see the module docstring. -/
noncomputable def liouvilleC : ℕ → ℂ := fun n => ((ArithmeticFunction.liouville n : ℤ) : ℂ)

@[simp] lemma liouvilleC_zero : liouvilleC 0 = 0 := by
  simp [liouvilleC]

@[simp] lemma liouvilleC_one : liouvilleC 1 = 1 := by
  simp [liouvilleC, ArithmeticFunction.liouville_apply_one]

/-- **THE FACTORISATION — no coprimality hypothesis.**  `λ(m n) = λ(m) λ(n)` for *all*
`m, n`, which is exactly what "completely multiplicative" buys and exactly what MR §4
step (b) consumes at `m := d₀`, `n := m`.  This is the fact that deletes MR Theorem 2.3's
`g = g₁ ∗ h` Möbius layer on the λ-road (freeze :72–74). -/
theorem liouvilleC_mul (m n : ℕ) : liouvilleC (m * n) = liouvilleC m * liouvilleC n := by
  simp only [liouvilleC, ArithmeticFunction.liouville_apply_mul]
  push_cast
  ring

/-- `λ(p) = −1` at every prime: `Ω(p) = 1`. -/
theorem liouvilleC_prime {p : ℕ} (hp : p.Prime) : liouvilleC p = -1 := by
  simp only [liouvilleC, ArithmeticFunction.liouville_apply hp.pos.ne',
    ArithmeticFunction.cardFactors_apply_prime hp, pow_one]
  norm_num

/-- `|λ(n)| = 1` off zero: `λ` is `±1`-valued on positive arguments. -/
theorem liouvilleC_norm {n : ℕ} (hn : n ≠ 0) : ‖liouvilleC n‖ = 1 := by
  simp only [liouvilleC, ArithmeticFunction.liouville_apply hn]
  push_cast
  rw [norm_pow, norm_neg, norm_one, one_pow]

/-- **`λ` is 1-bounded** — the `‖g n‖ ≤ 1` binder every MR/MRT statement carries. -/
theorem liouvilleC_norm_le_one (n : ℕ) : ‖liouvilleC n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact (liouvilleC_norm hn).le

/-! ## §2 — the dilation kernel: `d₀` is invisible to `BlockPrimeDivs`

The honest chain the freeze demands.  `d₀ < P` does **not** by itself say anything about
the *prime factors* of `d₀`; what it says is that each such prime `p`, being a divisor of
the nonzero `d₀`, satisfies `p ≤ d₀ < P` (`Nat.le_of_dvd`).  `primeFactors_lt_of_lt`
writes that chain once; everything downstream consumes the *prime-level* smallness
hypothesis `∀ p ∈ d.primeFactors, p < P`, which is the honest one. -/

/-- **The honest smallness chain.**  Every prime factor of a nonzero `d < P` is `< P`,
because it divides `d`.  (Stated separately so that the dilation lemmas below can be
consumed at the prime level by callers who know more than `d < P`.) -/
theorem primeFactors_lt_of_lt {d P : ℕ} (hd : d ≠ 0) (hdP : d < P) :
    ∀ p ∈ d.primeFactors, p < P := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  exact lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hp.2.1) hdP

/-- A number all of whose prime factors are below the block bottom has **no** block
primes: `BlockPrimeDivs P Q d = ∅`. -/
theorem blockPrimeDivs_eq_empty_of_small {P Q d : ℕ} (hsm : ∀ p ∈ d.primeFactors, p < P) :
    BlockPrimeDivs P Q d = ∅ := by
  rw [BlockPrimeDivs, Finset.filter_eq_empty_iff]
  intro p hp
  exact fun hc => absurd hc.1 (Nat.not_le.mpr (hsm p hp))

/-- **THE DILATION IDENTITY, at the `Finset` level.**  If every prime factor of `d` lies
below the block bottom `P`, then the block primes of `d·m` are exactly those of `m`.

The proof is `Nat.primeFactors_mul` + `Finset.filter_union` + §2's emptiness: as *sets*
the `d`-side contributes nothing, so there is no multiplicity bookkeeping — see the
module's `blockOmega` trap. -/
theorem blockPrimeDivs_dilate {P Q d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (hsm : ∀ p ∈ d.primeFactors, p < P) :
    BlockPrimeDivs P Q (d * m) = BlockPrimeDivs P Q m := by
  rw [BlockPrimeDivs, BlockPrimeDivs, Nat.primeFactors_mul hd hm, Finset.filter_union,
    show (d.primeFactors.filter (fun p => P ≤ p ∧ p ≤ Q)) = ∅ from
      blockPrimeDivs_eq_empty_of_small (Q := Q) hsm, Finset.empty_union]

/-- `ω(d·m; P, Q) = ω(m; P, Q)` under the prime-level smallness gate. -/
theorem blockOmega_dilate {P Q d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (hsm : ∀ p ∈ d.primeFactors, p < P) :
    blockOmega P Q (d * m) = blockOmega P Q m := by
  rw [blockOmega, blockOmega, blockPrimeDivs_dilate hd hm hsm]

/-- `ω(d·m; P, Q) = ω(m; P, Q)` under the *size* gate `d < P` — the form MRT states
(`d₀ ≤ q ≤ W < P₁`), routed through `primeFactors_lt_of_lt`. -/
theorem blockOmega_dilate_of_lt {P Q d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0) (hdP : d < P) :
    blockOmega P Q (d * m) = blockOmega P Q m :=
  blockOmega_dilate hd hm (primeFactors_lt_of_lt hd hdP)

/-! ## §3 — the `𝒮`-transfer: `1_𝒮(d₀ m) = 1_𝒮(m)`

`MemS Pseq Qseq J n` reads `blockOmega (Pseq j) (Qseq j) n` for `j ∈ [1, J]` only
(`Sec9Glue.lean:118`), so §2 transfers block by block.  The gate is needed at every `j`,
which under a monotone `P`-ladder is one inequality at `j = 1`. -/

/-- **THE DILATED BLOCK CONDITION IS THE UNDILATED ONE.**  If every prime factor of `d`
lies below every block bottom `Pseq j`, `j ∈ [1, J]`, then `d·m ∈ 𝒮 ⟺ m ∈ 𝒮`.

This is MRT p. 14's `𝒮' = 𝒮` — the reason step (b)'s dilated set needs no separate name
on the K-road. -/
theorem memS_dilate {Pseq Qseq : ℕ → ℕ} {J d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (hsm : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ d.primeFactors, p < Pseq j) :
    MemS Pseq Qseq J (d * m) ↔ MemS Pseq Qseq J m := by
  constructor <;> intro h j hj
  · rw [← blockOmega_dilate (Q := Qseq j) hd hm (hsm j hj)]
    exact h j hj
  · rw [blockOmega_dilate (Q := Qseq j) hd hm (hsm j hj)]
    exact h j hj

/-- The `𝒮`-transfer at the size gate `d < Pseq j` for every block. -/
theorem memS_dilate_of_lt {Pseq Qseq : ℕ → ℕ} {J d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (hlt : ∀ j ∈ Finset.Icc 1 J, d < Pseq j) :
    MemS Pseq Qseq J (d * m) ↔ MemS Pseq Qseq J m :=
  memS_dilate hd hm (fun j hj => primeFactors_lt_of_lt hd (hlt j hj))

/-- The `𝒮`-transfer from **one** inequality: on a monotone `P`-ladder the gate at the
bottom block `j = 1` gates every block, because `j ∈ [1, J]` means `1 ≤ j`. -/
theorem memS_dilate_of_lt_bot {Pseq Qseq : ℕ → ℕ} {J d m : ℕ} (hmono : Monotone Pseq)
    (hd : d ≠ 0) (hm : m ≠ 0) (hlt : d < Pseq 1) :
    MemS Pseq Qseq J (d * m) ↔ MemS Pseq Qseq J m :=
  memS_dilate_of_lt hd hm (fun _ hj =>
    lt_of_lt_of_le hlt (hmono (Finset.mem_Icc.mp hj).1))

/-- **MRT step (b), pointwise**: `1_𝒮(d m) g(d m) = g(d) · 1_𝒮(m) g(m)` for any
completely multiplicative `g`, under the gate.  Both halves of the file meet here. -/
theorem indicator_mul_dilate {g : ℕ → ℂ} (hg : ∀ a b : ℕ, g (a * b) = g a * g b)
    {Pseq Qseq : ℕ → ℕ} {J d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (hlt : ∀ j ∈ Finset.Icc 1 J, d < Pseq j) :
    (if MemS Pseq Qseq J (d * m) then g (d * m) else 0)
      = g d * (if MemS Pseq Qseq J m then g m else 0) := by
  by_cases hS : MemS Pseq Qseq J m
  · rw [if_pos ((memS_dilate_of_lt hd hm hlt).mpr hS), if_pos hS, hg]
  · rw [if_neg (fun hc => hS ((memS_dilate_of_lt hd hm hlt).mp hc)), if_neg hS, mul_zero]

/-- The λ-instance of step (b): `1_𝒮(d m) λ(d m) = λ(d) · 1_𝒮(m) λ(m)`. -/
theorem indicator_mul_dilate_liouville {Pseq Qseq : ℕ → ℕ} {J d m : ℕ} (hd : d ≠ 0)
    (hm : m ≠ 0) (hlt : ∀ j ∈ Finset.Icc 1 J, d < Pseq j) :
    (if MemS Pseq Qseq J (d * m) then liouvilleC (d * m) else 0)
      = liouvilleC d * (if MemS Pseq Qseq J m then liouvilleC m else 0) :=
  indicator_mul_dilate liouvilleC_mul hd hm hlt

/-- **Step (b) under a sum, with a free weight.**  The shape M4-4's change of variables
consumes: the `d`-dilated sieved sum is `g(d)` times the undilated one, weight and all.
`S` is any finite index set of nonzero `m`'s. -/
theorem sum_memS_dilate {g w : ℕ → ℂ} (hg : ∀ a b : ℕ, g (a * b) = g a * g b)
    {Pseq Qseq : ℕ → ℕ} {J d : ℕ} {S : Finset ℕ} (hd : d ≠ 0) (hS : (0 : ℕ) ∉ S)
    (hlt : ∀ j ∈ Finset.Icc 1 J, d < Pseq j) :
    ∑ m ∈ S.filter (fun m => MemS Pseq Qseq J (d * m)), g (d * m) * w m
      = g d * ∑ m ∈ S.filter (fun m => MemS Pseq Qseq J m), g m * w m := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm0 : m ≠ 0 := fun h => hS (h ▸ hm)
  by_cases hmem : MemS Pseq Qseq J m
  · rw [if_pos ((memS_dilate_of_lt hd hm0 hlt).mpr hmem), if_pos hmem, hg]
    ring
  · rw [if_neg (fun hc => hmem ((memS_dilate_of_lt hd hm0 hlt).mp hc)), if_neg hmem,
      mul_zero]

/-! ## §4 — the residue split proper

MRT's `n ≡ b (mod q)`, `d₀ := (b, q)`, `n = d₀ m`, `m ≡ b₀ (mod q₀)` with
`b₀ := b/d₀`, `q₀ := q/d₀` coprime.  Three arithmetic facts and one reindexing. -/

/-- **`d₀ ∣ n` on the class.**  Every `n ≡ b (mod q)` is divisible by `d₀ = (b, q)`: the
gcd divides `q` and `b`, hence `b % q`, hence `n % q`, hence `n`.  (This is why the class
can be written `n = d₀ m` at all.) -/
theorem gcd_dvd_of_modEq {b q n : ℕ} (h : Nat.ModEq q n b) : Nat.gcd b q ∣ n := by
  have hq : Nat.gcd b q ∣ q := Nat.gcd_dvd_right b q
  have hb : Nat.gcd b q ∣ b := Nat.gcd_dvd_left b q
  have hmod : Nat.gcd b q ∣ b % q := (Nat.dvd_mod_iff hq).mpr hb
  rw [Nat.ModEq] at h
  rw [← h] at hmod
  exact (Nat.dvd_mod_iff hq).mp hmod

/-- **The reduced class is coprime**: `(b/d₀, q/d₀) = 1`.  MRT's `(b₀, q₀) = 1`, which is
what makes the orthogonality step (`(1/φ(q₀))Σ_χ χ(b₀)χ̄(m)`) legitimate downstream. -/
theorem coprime_reduced_of_gcd {b q : ℕ} (hq : 0 < q) :
    Nat.Coprime (b / Nat.gcd b q) (q / Nat.gcd b q) :=
  Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right b hq)

/-- **The class transfer**: with `d₀ := (b,q)`, `b₀ := b/d₀`, `q₀ := q/d₀`,

```
      d₀ · m ≡ b  (mod q)   ⟺   m ≡ b₀  (mod q₀).
```

Both sides of MRT's reindexing say the same thing; this is the `Nat.ModEq` cancellation
`c a ≡ c b [MOD c n] ↔ a ≡ b [MOD n]` at `c := d₀`. -/
theorem modEq_dilate_iff {b q m : ℕ} (hq : 0 < q) :
    Nat.ModEq q (Nat.gcd b q * m) b
      ↔ Nat.ModEq (q / Nat.gcd b q) m (b / Nat.gcd b q) := by
  have hd0 : 0 < Nat.gcd b q := Nat.gcd_pos_of_pos_right b hq
  have hqe : q = Nat.gcd b q * (q / Nat.gcd b q) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right b q)).symm
  have hbe : b = Nat.gcd b q * (b / Nat.gcd b q) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left b q)).symm
  constructor
  · intro h
    refine Nat.ModEq.mul_left_cancel' hd0.ne' ?_
    rw [← hqe, ← hbe]
    exact h
  · intro h
    have := Nat.ModEq.mul_left' (c := Nat.gcd b q) h
    rw [← hqe, ← hbe] at this
    exact this

/-- **The reindexing `n = d₀ m`.**  On a finite set `A` of multiples of `d`, summing over
`A` is summing over `A/d` after re-inflating: the map `n ↦ n/d` is injective there.
(No positivity on `d` is needed: `d ∣ n` for every `n ∈ A` already forces the map to be
injective on `A`.) -/
theorem sum_reindex_dilate {d : ℕ} {A : Finset ℕ} (hdvd : ∀ n ∈ A, d ∣ n)
    (F : ℕ → ℂ) :
    ∑ n ∈ A, F n = ∑ m ∈ A.image (fun n => n / d), F (d * m) := by
  have hinj : ∀ x ∈ A, ∀ y ∈ A, x / d = y / d → x = y := by
    intro x hx y hy hxy
    have hx' : d * (x / d) = x := Nat.mul_div_cancel' (hdvd x hx)
    have hy' : d * (y / d) = y := Nat.mul_div_cancel' (hdvd y hy)
    rw [← hx', ← hy', hxy]
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Nat.mul_div_cancel' (hdvd n hn)]

/-- **M4-2's headline — the residue split with the `d₀`-dilation performed.**

For a completely multiplicative `g`, a finite set `A` of nonzero integers all lying in the
residue class `b (mod q)`, and the gate "`d₀ = (b,q)` is below every block bottom":

```
      Σ_{n ∈ A, n ∈ 𝒮} g(n)  =  g(d₀) · Σ_{m ∈ A/d₀, m ∈ 𝒮} g(m).
```

The set `𝒮` on the right is the *same* `𝒮` — that is the whole content of the dilation
(MRT's `𝒮'`), and it is exactly what the gate `d₀ ≤ q ≤ W < P₁` buys. -/
theorem residue_split_dilate {g : ℕ → ℂ} (hg : ∀ a b : ℕ, g (a * b) = g a * g b)
    {b q J : ℕ} {Pseq Qseq : ℕ → ℕ} {A : Finset ℕ} (hq : 0 < q)
    (hA : ∀ n ∈ A, Nat.ModEq q n b) (h0 : (0 : ℕ) ∉ A)
    (hgate : ∀ j ∈ Finset.Icc 1 J, Nat.gcd b q < Pseq j) :
    ∑ n ∈ A.filter (fun n => MemS Pseq Qseq J n), g n
      = g (Nat.gcd b q)
        * ∑ m ∈ (A.image (fun n => n / Nat.gcd b q)).filter
            (fun m => MemS Pseq Qseq J m), g m := by
  have hd0 : 0 < Nat.gcd b q := Nat.gcd_pos_of_pos_right b hq
  have hdvd : ∀ n ∈ A, Nat.gcd b q ∣ n := fun n hn => gcd_dvd_of_modEq (hA n hn)
  have hkey := sum_reindex_dilate hdvd
    (fun n => if MemS Pseq Qseq J n then g n else 0)
  rw [Finset.sum_filter, hkey, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  obtain ⟨n, hn, hnm⟩ := Finset.mem_image.mp hm
  have hn0 : n ≠ 0 := fun h => h0 (h ▸ hn)
  have hm0 : m ≠ 0 := by
    rw [← hnm]
    exact Nat.div_ne_zero_iff_of_dvd (hdvd n hn) |>.mpr ⟨hn0, hd0.ne'⟩
  exact indicator_mul_dilate hg hd0.ne' hm0 hgate

/-- The λ-instance of the headline. -/
theorem residue_split_dilate_liouville {b q J : ℕ} {Pseq Qseq : ℕ → ℕ} {A : Finset ℕ}
    (hq : 0 < q) (hA : ∀ n ∈ A, Nat.ModEq q n b) (h0 : (0 : ℕ) ∉ A)
    (hgate : ∀ j ∈ Finset.Icc 1 J, Nat.gcd b q < Pseq j) :
    ∑ n ∈ A.filter (fun n => MemS Pseq Qseq J n), liouvilleC n
      = liouvilleC (Nat.gcd b q)
        * ∑ m ∈ (A.image (fun n => n / Nat.gcd b q)).filter
            (fun m => MemS Pseq Qseq J m), liouvilleC m :=
  residue_split_dilate liouvilleC_mul hq hA h0 hgate

/-! ## §5 — the gate at the K-family door: `d₀ ≤ q ≤ W < P₁`

`P₁ = calP (Adoor M) (3072M) 1 = 2^{Adoor M}` and `Adoor M ≥ 2^{18} = 262144`
(`DoorFrame.Adoor_ge`), so `P₁ ≥ 2^{262144}`.  The consumer's `W` is `(log H)^{12}`.
Every step below stays on base-2 exponents: **the closed power is never evaluated**
(⟦V9c⟧). -/

/-- `P₁ = 2^{A}` at the door: `calE A G 1 = A`. -/
theorem calP_door_one_eq (M : ℕ) : calP (Adoor M) (3072 * M) 1 = 2 ^ Adoor M := by
  rw [calP, calE_one]

/-- **`P₁ ≥ 2^{262144}`, symbolically.**  `Adoor M = 2^{18}(⌊log₂ M⌋+1) ≥ 2^{18}`, and
`2^{18} = 262144` is the only numeral evaluated. -/
theorem two_pow_le_calP_door_one (M : ℕ) :
    (2 : ℝ) ^ (262144 : ℕ) ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
  have hE : (262144 : ℕ) ≤ Adoor M := by
    have h := Adoor_ge M
    rwa [show (2 : ℕ) ^ 18 = 262144 by norm_num] at h
  have hcast : ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) = (2 : ℝ) ^ Adoor M := by
    rw [calP_door_one_eq]
    push_cast
    ring
  rw [hcast]
  exact pow_le_pow_right₀ (by norm_num) hE

/-- **The `W < P₁` arm.**  Anything strictly below `2^{262144}` is strictly below the
door's `P₁` — the "absurd-roomy" comparison in one line. -/
theorem lt_calP_door_one {M : ℕ} {W : ℝ} (hW : W < (2 : ℝ) ^ (262144 : ℕ)) :
    W < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) :=
  lt_of_lt_of_le hW (two_pow_le_calP_door_one M)

/-- **The `d₀ ≤ q ≤ W < P₁` chain, delivered as a ℕ-inequality.**  This is the exact
hypothesis `memS_dilate_of_lt` (and hence `residue_split_dilate`) demands at the door. -/
theorem d_lt_calP_door_one {M d q : ℕ} {W : ℝ} (hdq : d ≤ q) (hqW : (q : ℝ) ≤ W)
    (hW : W < (2 : ℝ) ^ (262144 : ℕ)) :
    d < calP (Adoor M) (3072 * M) 1 := by
  have hd : (d : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    have hdq' : (d : ℝ) ≤ (q : ℝ) := by exact_mod_cast hdq
    exact lt_of_le_of_lt (le_trans hdq' hqW) (lt_calP_door_one hW)
  exact_mod_cast hd

/-- **`W = (log H)^{12}` clears `2^{262144}`** as soon as `log H ≤ 2^{21845}`, since
`12 · 21845 = 262140 < 262144`.  The door floor's `log H ≈ 9·10^{38} < 2^{130}` clears
this by a factor of `2^{21715}` — the freeze's "absurd-roomy". -/
theorem logH_pow_twelve_lt {H : ℝ} (h1 : 1 ≤ Real.log H)
    (h2 : Real.log H ≤ (2 : ℝ) ^ (21845 : ℕ)) :
    Real.log H ^ (12 : ℕ) < (2 : ℝ) ^ (262144 : ℕ) := by
  have hstep : Real.log H ^ (12 : ℕ) ≤ ((2 : ℝ) ^ (21845 : ℕ)) ^ (12 : ℕ) :=
    pow_le_pow_left₀ (by linarith) h2 12
  have hmul : ((2 : ℝ) ^ (21845 : ℕ)) ^ (12 : ℕ) = (2 : ℝ) ^ (262140 : ℕ) := by
    rw [← pow_mul]
  have hlast : (2 : ℝ) ^ (262140 : ℕ) < (2 : ℝ) ^ (262144 : ℕ) :=
    pow_lt_pow_right₀ (by norm_num) (by norm_num)
  rw [hmul] at hstep
  exact lt_of_le_of_lt hstep hlast

/-- **THE GATE, assembled** (`d₀ ≤ q ≤ W = (log H)^{12} < P₁` at the K-family door).
H-scale throughout; the only `H`-side demand is `log H ≤ 2^{21845}`. -/
theorem door_dilation_gate {M d q : ℕ} {H : ℝ} (h1 : 1 ≤ Real.log H)
    (h2 : Real.log H ≤ (2 : ℝ) ^ (21845 : ℕ)) (hdq : d ≤ q)
    (hqW : (q : ℝ) ≤ Real.log H ^ (12 : ℕ)) :
    d < calP (Adoor M) (3072 * M) 1 :=
  d_lt_calP_door_one hdq hqW (logH_pow_twelve_lt h1 h2)

/-- **THE GATE, `M`-RELATIVE** (`door_dilation_gate'`).  The same chain `d₀ ≤ q ≤ W < P₁`
with the `H`-side numeral route BYPASSED: the ceiling is the door's OWN bottom block
`P₁ = 2^{Adoor M}` (`calP_door_one_eq`), so the gate no longer caps `log H` by a constant.
`door_dilation_gate` is the special case `W = (log H)^{12}` at `log H ≤ 2^{21845}`, and stays
— nothing landed moves.

⟦WHY⟧ ⟦gate 12⟧ of ⟦THE FINAL REGISTER⟧ was `log H ≤ 2^{21845}`, an UPPER bound on the window
length against a regime whose `R.Hhi` nothing bounds above (`M4Spine`'s ⟦WALL C⟧).  Read
against `2^{Adoor M}` instead — with `M` in the register's own witnessed group — the gate is a
demand on `M`, which the spine chooses AFTER `R`. -/
theorem door_dilation_gate' {M d q : ℕ} {W : ℝ} (hdq : d ≤ q) (hqW : (q : ℝ) ≤ W)
    (hW : W < (2 : ℝ) ^ Adoor M) :
    d < calP (Adoor M) (3072 * M) 1 := by
  have hcast : ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) = (2 : ℝ) ^ Adoor M := by
    rw [calP_door_one_eq]
    push_cast
    ring
  have hd : (d : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    rw [hcast]
    have hdq' : (d : ℝ) ≤ (q : ℝ) := by exact_mod_cast hdq
    exact lt_of_le_of_lt (le_trans hdq' hqW) hW
  exact_mod_cast hd

/-- The same read at `P₁` itself — the shape ⟦gate 12⟧ carries once the cap is `M`-relative
(`arcDen 12 H < ((calP (Adoor M) (3072M) 1 : ℕ) : ℝ)`), so no consumer converts. -/
theorem door_dilation_gate_calP {M d q : ℕ} {W : ℝ} (hdq : d ≤ q) (hqW : (q : ℝ) ≤ W)
    (hW : W < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) :
    d < calP (Adoor M) (3072 * M) 1 := by
  have hd : (d : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    have hdq' : (d : ℝ) ≤ (q : ℝ) := by exact_mod_cast hdq
    exact lt_of_le_of_lt (le_trans hdq' hqW) hW
  exact_mod_cast hd

/-- The door `P`-ladder is monotone (`calE_mono` at `G = 3072M ≥ 1`), so the bottom-block
gate gates every block. -/
theorem calP_door_mono {M : ℕ} (hM : 1 ≤ M) : Monotone (calP (Adoor M) (3072 * M)) := by
  intro i j hij
  refine Nat.pow_le_pow_right (by norm_num) ?_
  exact calE_mono (Adoor M) (by omega) hij

/-- **THE ROW'S CAPSTONE — `𝒮`-transfer at the K-family door inhabitant.**  Under the
door gate `d ≤ q ≤ (log H)^{12}` (with the roomy `log H ≤ 2^{21845}`), the block condition
at `(A, G, M) = (Adoor M, 3072M, M)` does not see `d`:

```
      d·m ∈ 𝒮_K  ⟺  m ∈ 𝒮_K       (every level J, in particular the door's Jb = 2).
```
-/
theorem memS_dilate_door {M J d q m : ℕ} {H : ℝ} (hM : 1 ≤ M) (h1 : 1 ≤ Real.log H)
    (h2 : Real.log H ≤ (2 : ℝ) ^ (21845 : ℕ)) (hd : d ≠ 0) (hm : m ≠ 0) (hdq : d ≤ q)
    (hqW : (q : ℝ) ≤ Real.log H ^ (12 : ℕ)) :
    MemS (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) J (d * m)
      ↔ MemS (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) J m :=
  memS_dilate_of_lt_bot (calP_door_mono hM) hd hm
    (door_dilation_gate (M := M) h1 h2 hdq hqW)

/-- **The residue split at the door**, the form M4-3/M4-4 consume: the gate arrives as
the two door-scale hypotheses, and the block set on both sides is the K-family `𝒮`. -/
theorem residue_split_dilate_door {g : ℕ → ℂ} (hg : ∀ a b : ℕ, g (a * b) = g a * g b)
    {b q J M : ℕ} {A : Finset ℕ} {H : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (h1 : 1 ≤ Real.log H) (h2 : Real.log H ≤ (2 : ℝ) ^ (21845 : ℕ))
    (hA : ∀ n ∈ A, Nat.ModEq q n b) (h0 : (0 : ℕ) ∉ A)
    (hqW : (q : ℝ) ≤ Real.log H ^ (12 : ℕ)) :
    ∑ n ∈ A.filter
        (fun n => MemS (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) J n), g n
      = g (Nat.gcd b q)
        * ∑ m ∈ (A.image (fun n => n / Nat.gcd b q)).filter
            (fun m =>
              MemS (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) J m), g m := by
  refine residue_split_dilate hg hq hA h0 (fun j hj => ?_)
  have hgate : Nat.gcd b q < calP (Adoor M) (3072 * M) 1 :=
    door_dilation_gate (M := M) h1 h2 (Nat.le_of_dvd hq (Nat.gcd_dvd_right b q)) hqW
  exact lt_of_lt_of_le hgate (calP_door_mono hM (Finset.mem_Icc.mp hj).1)

end Salt.MR
