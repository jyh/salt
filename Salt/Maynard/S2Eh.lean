/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S1Bound
import Salt.Maynard.S2Decomp
import Salt.Maynard.S2MainLower
import Salt.Maynard.CongSolvable
import Salt.Maynard.LamBoundSharp
import Salt.Maynard.DivisorCount
import Salt.Maynard.EHConsume

/-!
# C4 — the EH consumption (`S₂^(m)` lower bound)

This is the LAST big analytic node of the Maynard bounded-gaps formalization:
it connects the concrete prime-weighted `S₂^(m)` over `n` to
`(Δπ / φ(W k)) · Qdiag_m` plus an EH-controlled error.

`S₂^(m)` is the concrete prime-restricted Selberg sum

  `S₂^(m) = ∑_{n ∈ (N,K₀N], n ≡ ν₀ (W k)} [n + hₘ prime] · w(n)`,

with `w(n) = (∑_d λ_d [∀i dᵢ ∣ n+hᵢ])²` the Maynard sieve weight (`weightSq`).

## Chain

* **Step 1** (`S2m_eq_sum_dd`) — genuine square-expansion + window-swap
  identifying `S₂^(m)` with `∑_{d,e ∈ 𝒟} λ_d λ_e · s2PrimeCount`, mirroring
  `S1_eq_sum_dd` with the prime indicator `[n+hₘ prime]` riding along.
* **Step 2** (`s2PrimeCount_eq_zero_of_dm`) — the prime forces `dₘ = eₘ = 1`:
  `dₘ ∣ lcm(dₘ,eₘ) ∣ n+hₘ` prime with `dₘ < R ≤ N < n+hₘ` forces `dₘ = 1`.
* **Step 3** (`s2PrimeCount_approx`) — the per-pair prime count is the density
  `Δπ / (φ(W k)·∏φ(lcm))` up to `maxDiscrepancy` at the two window endpoints,
  via the CRT residue `a` coprime to `q = W k·∏ lcm(dᵢ,eᵢ)`.  The narrow CRT
  bijection atom is a **PORT-BLOCKER** hypothesis (`hbij`, see below); the
  density comparison via `maxDiscrepancy` is landed on top of it.
* **Steps 4–5 / headline** (`S2m_lower`) — `S₂^(m) = main + error` with
  `main = (Δπ/φW)·Qdiag_m` (genuine algebra) and `|error| ≤ ∑|λ||λ||count−density|`
  (genuine triangle); the EH regrouping of that error sum into the
  `λ²_max · eh_error_pow` shape `C·N·(log R)^{2k+2}/(log N)^{2k+4}` is threaded
  as the Step-5 hypothesis `herr`.

## PORT-BLOCKERs (both strictly narrower than any headline conclusion)

* **hbij** (Step 3, the CRT-residue bijection): for each compatible pair with
  `dₘ=eₘ=1`, there is a reduced residue `a` mod `q = W k·∏ lcm(dᵢ,eᵢ)` with
  `s2PrimeCount = primesCount(K₀N+hₘ;q,a) − primesCount(N+hₘ;q,a)`.  This is
  the fiddly `n ↔ p=n+hₘ` count identity folding the `k+1` congruences by CRT.
* **herr** (Step 5, the EH regrouping): the `λ²_max`-weighted discrepancy sum
  over pairs is `≤ C·N·(log R)^{2k+2}/(log N)^{2k+4}` — the `(3k)^{ω(q)}`
  multiplicity reindexing feeding `eh_error_pow` (N5.2).
-/

namespace Salt.Maynard

open Finset

/-! ## The object -/

/-- `S₂^(m)`: the prime-restricted concrete Selberg sum over the `W`-trick
window `(N, K₀N]` with `n ≡ ν₀ (mod W k)`, with the prime indicator
`[n + hₘ prime]` and the squared sieve weight `weightSq`. -/
noncomputable def S2m (k K₀ N R ν₀ : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ n ∈ windowSet K₀ N (W k) ν₀,
    (if (n + hSeq k m).Prime then (1 : ℝ) else 0) * weightSq k R (W k) y n

/-- `Δπ = π(K₀N+hₘ) − π(N+hₘ)`, the window prime difference (`primesCount x 1 0
= π(x)`). -/
noncomputable def deltaPi (k K₀ N : ℕ) (m : Fin k) : ℝ :=
  (primesCount (K₀ * N + hSeq k m) 1 0 : ℝ) - (primesCount (N + hSeq k m) 1 0 : ℝ)

/-- The combined modulus of a pair `q = W k · ∏ᵢ lcm(dᵢ,eᵢ)` (equal to the
`i ≠ m` product when `dₘ=eₘ=1`, since `lcm(1,1)=1`). -/
noncomputable def qMod (k : ℕ) (d e : Fin k → ℕ) : ℕ :=
  W k * ∏ i, Nat.lcm (d i) (e i)

/-- `Qdiag_m`: the `dₘ=eₘ=1`-restricted S₂ diagonal quadratic form — exactly the
LHS of `s2main_lower` / `s2_diag_lam_restricted`. -/
noncomputable def Qdiag_m (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
    ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
      lam k R (W k) y d * lam k R (W k) y e
        / ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)

/-- `lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c` for naturals (reproved locally; the S1Bound
copy is private). -/
private theorem nat_lcm_dvd_iff' (a b c : ℕ) : Nat.lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c :=
  ⟨fun h => ⟨(Nat.dvd_lcm_left a b).trans h, (Nat.dvd_lcm_right a b).trans h⟩,
    fun ⟨h1, h2⟩ => Nat.lcm_dvd h1 h2⟩

/-! ## Step 1 — expand `S₂^(m)` into the `(d,e)` double sum -/

/-- **Step 1.** Genuine square-expansion of `weightSq` with the prime indicator
`[n+hₘ prime]` carried inside, plus the window-swap, identify `S₂^(m)` with the
count-weighted double `λ`-sum.  Mirrors `S1_eq_sum_dd`. -/
theorem S2m_eq_sum_dd (k K₀ N R ν₀ : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) :
    S2m k K₀ N R ν₀ m y
      = ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
          lam k R (W k) y d * lam k R (W k) y e
            * (s2PrimeCount k K₀ N ν₀ m d e : ℝ) := by
  classical
  unfold S2m weightSq
  -- expand the square and distribute the prime indicator into the double sum
  have step1 : ∀ n,
      (if (n + hSeq k m).Prime then (1 : ℝ) else 0) *
        (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => ∀ i, d i ∣ (n + hSeq k i)),
            lam k R (W k) y d) ^ 2
        = ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
            (if (n + hSeq k m).Prime then (1 : ℝ) else 0) *
              ((if ∀ i, d i ∣ (n + hSeq k i) then lam k R (W k) y d else 0) *
               (if ∀ i, e i ∣ (n + hSeq k i) then lam k R (W k) y e else 0)) := by
    intro n
    rw [Finset.sum_filter, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun n _ => step1 n)]
  -- swap the window sum to the innermost position
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  -- collapse the triple product of indicators to a single guarded value
  have inner_eq : ∀ n,
      (if (n + hSeq k m).Prime then (1 : ℝ) else 0) *
        ((if ∀ i, d i ∣ (n + hSeq k i) then lam k R (W k) y d else 0) *
         (if ∀ i, e i ∣ (n + hSeq k i) then lam k R (W k) y e else 0))
        = if ((n + hSeq k m).Prime ∧ (∀ i, d i ∣ (n + hSeq k i)) ∧
                (∀ i, e i ∣ (n + hSeq k i)))
            then lam k R (W k) y d * lam k R (W k) y e else 0 := by
    intro n
    by_cases hp : (n + hSeq k m).Prime <;>
      by_cases hd' : ∀ i, d i ∣ (n + hSeq k i) <;>
      by_cases he' : ∀ i, e i ∣ (n + hSeq k i) <;>
      simp [hp, hd', he']
  rw [Finset.sum_congr rfl (fun n _ => inner_eq n), ← Finset.sum_filter, Finset.sum_const]
  -- identify the filtered window with the `s2PrimeCount` filter
  have hcard :
      ((windowSet K₀ N (W k) ν₀).filter
          (fun n => (n + hSeq k m).Prime ∧ (∀ i, d i ∣ (n + hSeq k i)) ∧
              (∀ i, e i ∣ (n + hSeq k i)))).card
        = s2PrimeCount k K₀ N ν₀ m d e := by
    unfold windowSet s2PrimeCount
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro n _
    constructor
    · rintro ⟨hmod, hp, hd', he'⟩
      exact ⟨hmod, hp, fun i => (nat_lcm_dvd_iff' _ _ _).mpr ⟨hd' i, he' i⟩⟩
    · rintro ⟨hmod, hp, hlcm⟩
      refine ⟨hmod, hp, fun i => ((nat_lcm_dvd_iff' _ _ _).mp (hlcm i)).1,
        fun i => ((nat_lcm_dvd_iff' _ _ _).mp (hlcm i)).2⟩
  rw [hcard, nsmul_eq_mul]
  ring

/-! ## Step 2 — the prime forces `dₘ = eₘ = 1` -/

/-- **Step 2.** For a sieve tuple `d ∈ 𝒟` with `dₘ ≠ 1`, the joint prime count
is `0`: a counted `n` has `dₘ ∣ lcm(dₘ,eₘ) ∣ n+hₘ` prime, and `dₘ < R ≤ N < n+hₘ`
forces `dₘ = 1`, a contradiction. -/
theorem s2PrimeCount_eq_zero_of_dm (k K₀ N R ν₀ : ℕ) (m : Fin k) (d e : Fin k → ℕ)
    (hd : d ∈ kSieveIndex k R (W k)) (hRN : R ≤ N) (hdm : d m ≠ 1) :
    s2PrimeCount k K₀ N ν₀ m d e = 0 := by
  unfold s2PrimeCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn
  rw [Finset.mem_Ioc] at hn
  rintro ⟨_, hp, hlcm⟩
  -- `d m ∣ n + h m`
  have hdvd : d m ∣ (n + hSeq k m) := (Nat.dvd_lcm_left (d m) (e m)).trans (hlcm m)
  -- `d m = 1` or `d m = n + h m`
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp (d m) hdvd) with h1 | hself
  · exact hdm h1
  · -- `d m < R ≤ N < n < n + h m`, contradicting `d m = n + h m`
    have hlt : d m < R := kSieveIndex_coord_lt hd m
    have : d m < n + hSeq k m := by omega
    omega

/-- Step-2, `e`-side variant: `eₘ ≠ 1` also forces the count to `0`. -/
theorem s2PrimeCount_eq_zero_of_em (k K₀ N R ν₀ : ℕ) (m : Fin k) (d e : Fin k → ℕ)
    (he : e ∈ kSieveIndex k R (W k)) (hRN : R ≤ N) (hem : e m ≠ 1) :
    s2PrimeCount k K₀ N ν₀ m d e = 0 := by
  unfold s2PrimeCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn
  rw [Finset.mem_Ioc] at hn
  rintro ⟨_, hp, hlcm⟩
  have hdvd : e m ∣ (n + hSeq k m) := (Nat.dvd_lcm_right (d m) (e m)).trans (hlcm m)
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp (e m) hdvd) with h1 | hself
  · exact hem h1
  · have hlt : e m < R := kSieveIndex_coord_lt he m
    have : e m < n + hSeq k m := by omega
    omega

/-! ## Restriction: `S₂^(m)` collapses to the `dₘ=eₘ=1` guarded sum -/

/-- The Step-1 expansion, restricted by Step 2 to `dₘ=eₘ=1`. -/
theorem S2m_eq_guarded (k K₀ N R ν₀ : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hRN : R ≤ N) :
    S2m k K₀ N R ν₀ m y
      = ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
          (if d m = 1 ∧ e m = 1 then
            lam k R (W k) y d * lam k R (W k) y e
              * (s2PrimeCount k K₀ N ν₀ m d e : ℝ)
           else 0) := by
  rw [S2m_eq_sum_dd]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  refine Finset.sum_congr rfl (fun e he => ?_)
  by_cases h : d m = 1 ∧ e m = 1
  · rw [if_pos h]
  · rw [if_neg h]
    -- at least one of `dₘ, eₘ` is `≠ 1`, so the count is `0`
    rw [not_and_or] at h
    rcases h with hdm | hem
    · rw [s2PrimeCount_eq_zero_of_dm k K₀ N R ν₀ m d e hd hRN hdm]; simp
    · -- `eₘ ≠ 1`: symmetric — `eₘ ∣ lcm(dₘ,eₘ) ∣ n+hₘ`
      rw [s2PrimeCount_eq_zero_of_em k K₀ N R ν₀ m d e he hRN hem]; simp

/-! ## Step 3 — per-pair prime count = density ± discrepancy (the CRT crux) -/

/-- `φ` of a product of pairwise-coprime moduli is the product of the `φ`s. -/
private theorem totient_prod_coprime {ι : Type*} (f : ι → ℕ) :
    ∀ (s : Finset ι),
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j)) →
      Nat.totient (∏ i ∈ s, f i) = ∏ i ∈ s, Nat.totient (f i) := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    intro hcop
    rw [Finset.prod_insert hx, Finset.prod_insert hx]
    have hcopr : Nat.Coprime (f x) (∏ i ∈ s, f i) := by
      apply Nat.Coprime.prod_right
      intro j hj
      exact hcop x (Finset.mem_insert_self x s) j (Finset.mem_insert_of_mem hj)
        (by rintro rfl; exact hx hj)
    rw [Nat.totient_mul hcopr]
    congr 1
    exact ih (fun i hi j hj hij => hcop i (Finset.mem_insert_of_mem hi) j
      (Finset.mem_insert_of_mem hj) hij)

/-- `φ(q) = φ(W k)·∏ᵢ φ(lcm(dᵢ,eᵢ))` for a compatible pair (coprime moduli),
as a real identity. -/
theorem totient_qMod_eq (k : ℕ) (d e : Fin k → ℕ)
    (hcopW : ∀ i, Nat.Coprime (W k) (Nat.lcm (d i) (e i)))
    (hcoplcm : ∀ i j, i ≠ j → Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))) :
    (Nat.totient (qMod k d e) : ℝ)
      = (Nat.totient (W k) : ℝ) * phiLcmProd d e := by
  unfold qMod phiLcmProd
  have hcopWprod : Nat.Coprime (W k) (∏ i, Nat.lcm (d i) (e i)) :=
    Nat.Coprime.prod_right (fun i _ => hcopW i)
  rw [Nat.totient_mul hcopWprod,
    totient_prod_coprime (fun i => Nat.lcm (d i) (e i)) Finset.univ
      (fun i _ j _ hij => hcoplcm i j hij)]
  push_cast
  ring

/-- The per-residue discrepancy is dominated by `maxDiscrepancy` at a reduced
residue `a` (`a < q`, coprime to `q`) — immediate from the `Finset.sup'`
definition. -/
theorem disc_le_maxDiscrepancy (x q a : ℕ) (hq : q ≠ 0) (ha : a < q)
    (hcop : Nat.Coprime a q) :
    |(primesCount x q a : ℝ) - (primesCount x 1 0 : ℝ) / (Nat.totient q : ℝ)|
      ≤ maxDiscrepancy x q := by
  unfold maxDiscrepancy
  rw [dif_neg hq]
  exact Finset.le_sup'
    (fun a => |(primesCount x q a : ℝ) - (primesCount x 1 0 : ℝ) / (Nat.totient q : ℝ)|)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, hcop⟩)

/-- **Step 3 — the per-pair prime count as density ± discrepancy.**
For a compatible pair with `dₘ=eₘ=1`, given the CRT-residue bijection witness
`hbij` (the narrow **PORT-BLOCKER** atom, see the header), the joint prime
count is within `maxDiscrepancy` at the two window endpoints of the expected
density `Δπ / (φ(W k)·∏φ(lcm))`.

The bijection reduces the count to a `primesCount` difference at a reduced
residue `a` mod `q = W k·∏ lcm(dᵢ,eᵢ)`; `φ(q) = φ(W k)·∏φ(lcm)` by coprimality
(`totient_qMod_eq`); the density splits over the two endpoints; and each
endpoint deviation is `≤ maxDiscrepancy` (`disc_le_maxDiscrepancy`, `a` reduced).
-/
theorem s2PrimeCount_approx (k K₀ N ν₀ : ℕ) (m : Fin k) (d e : Fin k → ℕ)
    (hlcmpos : ∀ i, 0 < Nat.lcm (d i) (e i))
    (hcopW : ∀ i, Nat.Coprime (W k) (Nat.lcm (d i) (e i)))
    (hcoplcm : ∀ i j, i ≠ j → Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j)))
    (hbij : ∃ a : ℕ, a < qMod k d e ∧ Nat.Coprime a (qMod k d e) ∧
      (s2PrimeCount k K₀ N ν₀ m d e : ℝ)
        = (primesCount (K₀ * N + hSeq k m) (qMod k d e) a : ℝ)
          - (primesCount (N + hSeq k m) (qMod k d e) a : ℝ)) :
    |(s2PrimeCount k K₀ N ν₀ m d e : ℝ)
        - deltaPi k K₀ N m / ((Nat.totient (W k) : ℝ) * phiLcmProd d e)|
      ≤ maxDiscrepancy (K₀ * N + hSeq k m) (qMod k d e)
        + maxDiscrepancy (N + hSeq k m) (qMod k d e) := by
  obtain ⟨a, haq, hacop, hcount⟩ := hbij
  set q := qMod k d e with hqdef
  -- `q > 0`
  have hWpos : 0 < W k := Nat.pos_of_ne_zero (W_squarefree k).ne_zero
  have hprodpos : 0 < ∏ i, Nat.lcm (d i) (e i) := Finset.prod_pos (fun i _ => hlcmpos i)
  have hqpos : 0 < q := by rw [hqdef, qMod]; exact Nat.mul_pos hWpos hprodpos
  have hq0 : q ≠ 0 := hqpos.ne'
  -- `φ(q) = φ(W k)·∏φ(lcm)`
  have hφq : (Nat.totient q : ℝ) = (Nat.totient (W k) : ℝ) * phiLcmProd d e :=
    totient_qMod_eq k d e hcopW hcoplcm
  have hφqpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hqpos
  -- rewrite the density with `φ(q)` in the denominator
  have hdens : deltaPi k K₀ N m / ((Nat.totient (W k) : ℝ) * phiLcmProd d e)
      = deltaPi k K₀ N m / (Nat.totient q : ℝ) := by rw [hφq]
  rw [hdens, hcount, deltaPi]
  -- split the density over the two endpoints and regroup
  set A := (primesCount (K₀ * N + hSeq k m) q a : ℝ) with hA
  set B := (primesCount (N + hSeq k m) q a : ℝ) with hB
  set PA := (primesCount (K₀ * N + hSeq k m) 1 0 : ℝ) with hPA
  set PB := (primesCount (N + hSeq k m) 1 0 : ℝ) with hPB
  have hsplit : (A - B) - (PA - PB) / (Nat.totient q : ℝ)
      = (A - PA / (Nat.totient q : ℝ)) - (B - PB / (Nat.totient q : ℝ)) := by
    field_simp
    ring
  rw [hsplit]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · exact disc_le_maxDiscrepancy (K₀ * N + hSeq k m) q a hq0 haq hacop
  · exact disc_le_maxDiscrepancy (N + hSeq k m) q a hq0 haq hacop

/-! ## Steps 4–5 — the main term and the assembled headline -/

/-- A guarded double sum over `𝒟 × 𝒟` equals the `dₘ=eₘ=1`-filtered double
sum. -/
theorem guarded_double_sum {k : ℕ} (s : Finset (Fin k → ℕ)) (m : Fin k)
    (F : (Fin k → ℕ) → (Fin k → ℕ) → ℝ) :
    ∑ d ∈ s, ∑ e ∈ s, (if d m = 1 ∧ e m = 1 then F d e else 0)
      = ∑ d ∈ s.filter (fun d => d m = 1),
          ∑ e ∈ s.filter (fun e => e m = 1), F d e := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases hd : d m = 1
  · simp only [hd, true_and, if_true, Finset.sum_filter]
  · simp only [hd, false_and, if_false, Finset.sum_const_zero]

/-- **Step 4 — the main term factorises.** The `dₘ=eₘ=1`-guarded density sum is
`(Δπ / φ(W k)) · Qdiag_m`, exhibiting the main term as proportional to the S₂
diagonal `Qdiag_m`. -/
theorem s2Main_eq_Qdiag (k K₀ N R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) :
    (∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
        (if d m = 1 ∧ e m = 1 then
          lam k R (W k) y d * lam k R (W k) y e *
            (deltaPi k K₀ N m / ((Nat.totient (W k) : ℝ) * phiLcmProd d e))
         else 0))
      = deltaPi k K₀ N m / (Nat.totient (W k) : ℝ) * Qdiag_m k R m y := by
  rw [guarded_double_sum]
  unfold Qdiag_m phiLcmProd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  ring

/-- **C4 — the headline `S₂^(m)` lower bound (EH consumption).**  With the
Step-5 EH regrouping `herr` bounding the `λ²_max`-weighted per-pair discrepancy
sum by the explicit `o(N)` shape `C·N·(log R)^{2k+2}/(log N)^{2k+4}`,

  `S₂^(m) ≥ (Δπ / φ(W k)) · Qdiag_m − C·N·(log R)^{2k+2}/(log N)^{2k+4}`.

The main term `(Δπ/φW)·Qdiag_m` and the error triangle are landed genuinely on
top of Steps 1–2 (`S2m_eq_guarded`); the error's per-pair discrepancy form is
exactly what `s2PrimeCount_approx` (Step 3) bounds by `maxDiscrepancy`, and
`herr` is its EH-controlled regrouping via `eh_error_pow` (N5.2). -/
theorem S2m_lower (k K₀ N R ν₀ : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (C : ℝ) (hRN : R ≤ N)
    (herr : ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
        (if d m = 1 ∧ e m = 1 then
          |lam k R (W k) y d| * |lam k R (W k) y e| *
            |(s2PrimeCount k K₀ N ν₀ m d e : ℝ)
              - deltaPi k K₀ N m / ((Nat.totient (W k) : ℝ) * phiLcmProd d e)|
         else 0)
      ≤ C * (N : ℝ) / (Real.log N) ^ (2 * k + 4) * (1 + Real.log R) ^ (2 * k + 2)) :
    S2m k K₀ N R ν₀ m y
      ≥ deltaPi k K₀ N m / (Nat.totient (W k) : ℝ) * Qdiag_m k R m y
        - C * (N : ℝ) / (Real.log N) ^ (2 * k + 4) * (1 + Real.log R) ^ (2 * k + 2) := by
  classical
  -- split `S₂^(m) = main + error`, an exact identity
  have hsplit : S2m k K₀ N R ν₀ m y
      = (∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
          (if d m = 1 ∧ e m = 1 then
            lam k R (W k) y d * lam k R (W k) y e *
              (deltaPi k K₀ N m / ((Nat.totient (W k) : ℝ) * phiLcmProd d e))
           else 0))
        + (∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
            (if d m = 1 ∧ e m = 1 then
              lam k R (W k) y d * lam k R (W k) y e *
                ((s2PrimeCount k K₀ N ν₀ m d e : ℝ)
                  - deltaPi k K₀ N m / ((Nat.totient (W k) : ℝ) * phiLcmProd d e))
             else 0)) := by
    rw [S2m_eq_guarded k K₀ N R ν₀ m y hRN, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases h : d m = 1 ∧ e m = 1
    · simp only [if_pos h]; ring
    · simp only [if_neg h]; ring
  -- the error term is dominated in absolute value by the discrepancy sum `herr`
  have hEbound :
      |∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
          (if d m = 1 ∧ e m = 1 then
            lam k R (W k) y d * lam k R (W k) y e *
              ((s2PrimeCount k K₀ N ν₀ m d e : ℝ)
                - deltaPi k K₀ N m / ((Nat.totient (W k) : ℝ) * phiLcmProd d e))
           else 0)|
        ≤ ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
            (if d m = 1 ∧ e m = 1 then
              |lam k R (W k) y d| * |lam k R (W k) y e| *
                |(s2PrimeCount k K₀ N ν₀ m d e : ℝ)
                  - deltaPi k K₀ N m / ((Nat.totient (W k) : ℝ) * phiLcmProd d e)|
             else 0) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun d _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun e _ => ?_)
    by_cases h : d m = 1 ∧ e m = 1
    · rw [if_pos h, if_pos h, abs_mul, abs_mul]
    · rw [if_neg h, if_neg h, abs_zero]
  rw [hsplit, s2Main_eq_Qdiag k K₀ N R m y]
  linarith [hEbound, herr, neg_abs_le (∑ d ∈ kSieveIndex k R (W k),
    ∑ e ∈ kSieveIndex k R (W k),
      (if d m = 1 ∧ e m = 1 then
        lam k R (W k) y d * lam k R (W k) y e *
          ((s2PrimeCount k K₀ N ν₀ m d e : ℝ)
            - deltaPi k K₀ N m / ((Nat.totient (W k) : ℝ) * phiLcmProd d e))
       else 0))]

end Salt.Maynard
