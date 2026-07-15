/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.GeneralBV
import Salt.Chen.BetaSW

/-!
# C3c — the count→twist duality bridge + the general-BV close (β-side of KEYSTONE 2)

Design: `docs/blueprints/chen.md`, the C3c row ("the fine-partition bookkeeping").
This node reconciles C3b's **count-form** SW-regularity (`prime_indicator_SW`) with
C3a's **twist-form** hypothesis slot (`hβSW` in `general_BV_weak`), and composes the
two into the closed general Bombieri–Vinogradov for the interval prime indicator.

## What this file lands (sorry-free, FULL)

1. **The count→twist duality bridge** (`bilinTwist_eq_sum_class`,
   `bilinTwist_le_of_classDisc`) — the finite-Fourier duality over `(ℤ/d)ˣ`:
   `bilinTwist β Y d χ = ∑_{r : ZMod d} χ(r)·Cnt(r)` where `Cnt(r)` is the count of
   the `β`-mass in the residue class `r`.  For a **non-principal** `χ`, orthogonality
   (`∑_r χ(r) = 0`, `MulChar.sum_eq_zero_of_ne_one`) kills the `Mass/φd` main term and
   `χ` vanishes off units (`MulChar.map_nonunit`), so
   `‖bilinTwist β Y d χ‖ ≤ d · (max class discrepancy) = d·δ`.  This is the exact
   dual of C3a's `apDiscBilin_orthogonality` (there over characters; here over
   residues) — the reusable "count ↔ twist" reconciliation the C3b note flagged.

2. **The prime-indicator instantiation** (`blockPrimeInd`, `blockPrimeInd_classCount`,
   `hβSW_of_prime_indicator`) — for `β = blockPrimeInd N` (the interval prime indicator
   of `(N, M]`), the class count `Cnt(r)` is exactly the residue-class prime count of
   C3b, so the bridge + `prime_indicator_SW` give
   `‖bilinTwist (blockPrimeInd N) M d χ‖ ≤ d·K·N/(log N)^A` (`χ ≠ 1`, `d ≤ (log N)^C`).

3. **The composed keystone** (`general_BV_closed`) — `general_BV_weak` with the
   small-conductor SW hypothesis `hβSW` **discharged** (via 1+2 and the log-power
   scale bookkeeping `A' = A + 2·C0`) for `β = blockPrimeInd N`.  What remains named:
   the coefficient bound `‖α‖ ≤ 1` (as designed), the residue coprimality, the
   scale-compatibility `K·(log XM)^{A+2C0} ≤ Kβ·(log N)^{A+2C0}` (`log XM`, `log N`
   are the same order — the constant absorbs into `Kβ/K`), and the **large-conductor
   dyadic energy `hLargeDisc`** (the dyadic-in-conductor descent).

## FLAG (Iron Rule 1 / STOP-AND-FLAG) — the bilinear conductor descent (`hLargeDisc`)

`general_BV_closed` still takes `hLargeDisc` (the large-conductor character energy
bound) as a **named hypothesis** — the same slot C3a exposed.  The genuine obstruction
(recorded in `docs/blueprints/flags.md`): the corpus' landed LINEAR conductor descent
(`Salt.BV.regroupL1_perq` + the primitive-reduction error
`Salt.LS.norm_psiChi_sub_primitiveCharacter_le` + `Salt.BV.swapPhi_le`) does **not**
mirror to the bilinear PRODUCT `‖A_d(χ)‖·‖B_d(χ)‖`: writing `A_d(χ) = A⋆ + errA`,
`B_d(χ) = B⋆ + errB` (primitive `⋆` at the conductor), the product carries cross-terms
`‖A⋆‖·‖errB‖ + ‖errA‖·‖B⋆‖`.  The `β`-side error `errB` is cheap (the prime indicator
`≤ ω(d)` — only primes `p ∣ d` contribute), matching the design note; but the `α`-side
`errA` is **not** small for a general `‖α‖ ≤ 1` sequence, so per-factor descent is
lossy.  The correct route keeps `A⋆, B⋆` primitive from the start and consumes the
landed shell engine `Salt.Chen.bilinTwist_energy_le` (the `(q/φq)`-weighted primitive
product energy) DYADICALLY in the conductor `f ∈ [F, 2F]`, recovering the `1/f`
per-block weight and closing the C3a `(q/φq)`↔`(1/φd)` weight mismatch.  That dyadic
reassembly is the remaining analytic core of C3c and is left as the single named
`hLargeDisc` input.

Only `[propext, Classical.choice, Quot.sound]` are used.
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## 1. The count→twist duality bridge -/

/-- The character twist written as a character-weighted sum over residue classes
mod `d`: `bilinTwist β Y d χ = ∑_{r : ZMod d} χ(r)·(class-`r` count of β)`.  The
finite-Fourier dual of C3a's `apDiscBilin_orthogonality`. -/
lemma bilinTwist_eq_sum_class {d : ℕ} [NeZero d] (β : ℕ → ℂ) (Y : ℕ)
    (χ : DirichletCharacter ℂ d) :
    bilinTwist β Y d χ
      = ∑ r : ZMod d, χ r *
          (∑ n ∈ Finset.Icc 1 Y, if (n : ZMod d) = r then β n else 0) := by
  classical
  unfold bilinTwist
  have hpt : ∀ r : ZMod d,
      χ r * (∑ n ∈ Finset.Icc 1 Y, if (n : ZMod d) = r then β n else 0)
        = ∑ n ∈ Finset.Icc 1 Y, (if (n : ZMod d) = r then χ r * β n else 0) := by
    intro r
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [mul_ite, mul_zero]
  rw [Finset.sum_congr rfl (fun r _ => hpt r), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.sum_ite_eq Finset.univ (n : ZMod d) (fun r => χ r * β n)]
  rw [if_pos (Finset.mem_univ _), mul_comm]

/-- **The count→twist duality bridge.** For a non-principal character `χ mod d`, the
character twist is controlled by the per-unit-class discrepancy against the common
mean `Mass/φd`: orthogonality (`∑_r χ(r) = 0`) kills the main term, and `χ`
vanishes off units, so `‖bilinTwist β Y d χ‖ ≤ d·δ`. -/
lemma bilinTwist_le_of_classDisc {d : ℕ} [NeZero d] (β : ℕ → ℂ) (Y : ℕ)
    (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1) (Mass : ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hdisc : ∀ r : ZMod d, IsUnit r →
      ‖(∑ n ∈ Finset.Icc 1 Y, if (n : ZMod d) = r then β n else 0)
          - Mass / (d.totient : ℂ)‖ ≤ δ) :
    ‖bilinTwist β Y d χ‖ ≤ (d : ℝ) * δ := by
  classical
  rw [bilinTwist_eq_sum_class]
  set Cnt : ZMod d → ℂ :=
    fun r => ∑ n ∈ Finset.Icc 1 Y, if (n : ZMod d) = r then β n else 0 with hCnt
  have hmain : ∑ r : ZMod d, χ r * (Mass / (d.totient : ℂ)) = 0 := by
    rw [← Finset.sum_mul, MulChar.sum_eq_zero_of_ne_one hχ, zero_mul]
  have hrw : ∑ r : ZMod d, χ r * Cnt r
      = ∑ r : ZMod d, χ r * (Cnt r - Mass / (d.totient : ℂ)) := by
    have hsplit : ∀ r : ZMod d,
        χ r * Cnt r
          = χ r * (Cnt r - Mass / (d.totient : ℂ)) + χ r * (Mass / (d.totient : ℂ)) := by
      intro r; ring
    rw [Finset.sum_congr rfl (fun r _ => hsplit r), Finset.sum_add_distrib, hmain, add_zero]
  rw [hrw]
  calc ‖∑ r : ZMod d, χ r * (Cnt r - Mass / (d.totient : ℂ))‖
      ≤ ∑ r : ZMod d, ‖χ r * (Cnt r - Mass / (d.totient : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ _r : ZMod d, δ := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        rw [norm_mul]
        by_cases hu : IsUnit r
        · calc ‖χ r‖ * ‖Cnt r - Mass / (d.totient : ℂ)‖ ≤ 1 * δ :=
                mul_le_mul (DirichletCharacter.norm_le_one χ r) (hdisc r hu)
                  (norm_nonneg _) (by norm_num)
            _ = δ := one_mul δ
        · rw [MulChar.map_nonunit χ hu, norm_zero, zero_mul]; exact hδ
    _ = (d : ℝ) * δ := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

/-! ## 2. The interval prime indicator -/

/-- The interval prime indicator on the block `(N, ∞)`: `1` at primes `> N`. Paired
with the range `Icc 1 M` in `bilinTwist`, it is the prime indicator of `(N, M]`. -/
noncomputable def blockPrimeInd (N : ℕ) (n : ℕ) : ℂ := if N < n ∧ n.Prime then 1 else 0

/-- The per-class count of `blockPrimeInd` equals the prime count of the block `(N, M]`
in the ZMod-`d` fiber of `r`. -/
lemma blockPrimeInd_classCount {d : ℕ} (N M : ℕ) (r : ZMod d) :
    (∑ n ∈ Finset.Icc 1 M, if (n : ZMod d) = r then blockPrimeInd N n else 0)
      = (((Finset.Ioc N M).filter (fun p : ℕ => p.Prime ∧ (p : ZMod d) = r)).card : ℂ) := by
  classical
  have hmerge : ∀ n : ℕ,
      (if (n : ZMod d) = r then blockPrimeInd N n else 0)
        = (if ((n : ZMod d) = r ∧ N < n ∧ n.Prime) then (1 : ℂ) else 0) := by
    intro n
    unfold blockPrimeInd
    by_cases h1 : (n : ZMod d) = r
    · by_cases h2 : N < n ∧ n.Prime
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
      · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
  rw [Finset.sum_congr rfl (fun n _ => hmerge n), Finset.sum_boole]
  congr 1
  apply Finset.card_bij (fun n _ => n)
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hn.2.2.1, hn.1.2⟩, hn.2.2.2, hn.2.1⟩
  · intro n _ m _ h; exact h
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    refine ⟨p, ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hp1 : 1 ≤ p := by omega
    exact ⟨⟨hp1, hp.1.2⟩, hp.2.2, hp.1.1, hp.2.1⟩

/-- **The count→twist bridge for the interval prime indicator (C3c bridge).** From
C3b's `prime_indicator_SW` (the residue-class prime-count discrepancy on a block
`(N,M]`, `M ≤ 2N`) the character twist of the interval prime indicator obeys
`‖bilinTwist (blockPrimeInd N) M d χ‖ ≤ d·K·N/(log N)^A` for `χ ≠ 1`, `d ≤ (log N)^C`.
Duality (`bilinTwist_le_of_classDisc`): `bilinTwist = ∑_a χ(a)·count_a`, orthogonality
kills the `Mass/φd` main term, and `χ` vanishes off units, so `≤ d·(max discrepancy)`. -/
theorem hβSW_of_prime_indicator {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (N M d : ℕ) (χ : DirichletCharacter ℂ d),
        N₀ ≤ N → N ≤ M → M ≤ 2 * N → 2 ≤ d →
        ((d : ℝ) ≤ (Real.log N) ^ C) → χ ≠ 1 →
        ‖bilinTwist (blockPrimeInd N) M d χ‖ ≤ (d : ℝ) * (K * N / (Real.log N) ^ A) := by
  obtain ⟨K, N₀, hK0, hb⟩ := prime_indicator_SW hA hC
  refine ⟨K, max N₀ 3, hK0, fun N M d χ hN hNM hM2N hd2 hdlog hχ => ?_⟩
  classical
  haveI : NeZero d := ⟨by omega⟩
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hLApos : (0 : ℝ) < (Real.log N) ^ A := Real.rpow_pos_of_pos hlogN A
  set δ : ℝ := K * N / (Real.log N) ^ A with hδdef
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  set Mass : ℂ := (((Finset.Ioc N M).filter (fun p : ℕ => p.Prime)).card : ℂ) with hMassdef
  refine bilinTwist_le_of_classDisc (blockPrimeInd N) M χ hχ Mass δ hδ0 (fun r hr => ?_)
  -- the discrepancy at the unit residue `r`, via `prime_indicator_SW` at `a = r.val`.
  have hrval : ((r.val : ℕ) : ZMod d) = r := ZMod.natCast_zmod_val r
  have hcop : Nat.Coprime r.val d := by
    rw [← ZMod.isUnit_iff_coprime]; rw [hrval]; exact hr
  -- filter predicates coincide: `↑p = r ↔ p % d = r.val % d`.
  have hpred : ∀ p : ℕ, ((p : ZMod d) = r) ↔ (p % d = r.val % d) := by
    intro p
    have h := ZMod.natCast_eq_natCast_iff' p r.val d
    rwa [hrval] at h
  have hcnt : ((Finset.Ioc N M).filter (fun p : ℕ => p.Prime ∧ (p : ZMod d) = r)).card
      = ((Finset.Ioc N M).filter (fun p : ℕ => p.Prime ∧ p % d = r.val % d)).card := by
    congr 1
    apply Finset.filter_congr
    intro p _; rw [hpred p]
  -- the C3b bound at `(N, M, d, r.val)`.
  have hbound := hb N M d r.val hNN₀ hNM hM2N (by omega) hcop hdlog
  -- convert the complex class-count discrepancy to the real one.
  rw [blockPrimeInd_classCount N M r, hcnt]
  set cc : ℝ := (((Finset.Ioc N M).filter (fun p : ℕ => p.Prime ∧ p % d = r.val % d)).card : ℝ)
    with hccdef
  set mc : ℝ := (((Finset.Ioc N M).filter (fun p : ℕ => p.Prime)).card : ℝ) with hmcdef
  have hconv : ((((Finset.Ioc N M).filter (fun p : ℕ => p.Prime ∧ p % d = r.val % d)).card : ℂ))
        - Mass / (d.totient : ℂ)
      = (((cc - mc / (d.totient : ℝ)) : ℝ) : ℂ) := by
    rw [hMassdef, hccdef, hmcdef]; push_cast; ring
  rw [hconv, Complex.norm_real, Real.norm_eq_abs]
  exact hbound

/-! ## 3. The composed keystone -/

open Classical in
/-- **C3c — general BV, closed for the interval prime indicator (KEYSTONE 2, β-side).**
`general_BV_weak` with the small-conductor SW hypothesis `hβSW` **discharged** (via the
count→twist bridge + C3b's `prime_indicator_SW`) for `β = blockPrimeInd N`, leaving
only: the coefficient bound `‖α‖ ≤ 1` (as designed), the residue coprimality, the
scale-compatibility `K·(log XM)^{A+2C0} ≤ Kβ·(log N)^{A+2C0}` (`log XM`, `log N` the
same order — the constant absorbs into `Kβ/K`), and the large-conductor dyadic energy
`hLargeDisc` (the dyadic-in-conductor descent — see the module FLAG). -/
theorem general_BV_closed {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M R₀ D0 : ℕ) (Dset : Finset ℕ) (Kβ Klarge : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → 3 ≤ N → N₀ ≤ N → N ≤ M → M ≤ 2 * N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime R₀ d) →
        (0 < Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 2 * C0)
            ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        (∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
              (1 / (d.totient : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
                  ‖bilinTwist α X d χ‖ * ‖bilinTwist (blockPrimeInd N) M d χ‖
            ≤ Klarge * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) →
        ∑ d ∈ Dset, ‖apDiscBilin α (blockPrimeInd N) X M R₀ d‖
          ≤ (Kβ + Klarge) * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K, N₀, hK0, hbSW⟩ :=
    hβSW_of_prime_indicator (A := A + 2 * C0) (C := C0) (by linarith) hC0
  refine ⟨K, N₀, hK0, fun α X N M R₀ D0 Dset Kβ Klarge hα hKβ hN3 hN hNM hM2N hDge1 hcop
    hLpos hD0 hD0N hscale hLargeDisc => ?_⟩
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hLAC0pos : (0 : ℝ) < L ^ (A + C0) := Real.rpow_pos_of_pos hLpos (A + C0)
  have hlogNApos : (0 : ℝ) < (Real.log N) ^ (A + 2 * C0) := Real.rpow_pos_of_pos hlogN _
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hLcomb : L ^ C0 * L ^ (A + C0) = L ^ (A + 2 * C0) := by
    rw [← Real.rpow_add hLpos]; congr 1; ring
  -- Discharge `hβSW` in `general_BV_weak`'s shape via the bridge + scale bookkeeping.
  have hβSW : ∀ (d : ℕ), 2 ≤ d → d ≤ D0 → ∀ χ : DirichletCharacter ℂ d, χ ≠ 1 →
      ‖bilinTwist (blockPrimeInd N) M d χ‖ ≤ Kβ * (M : ℝ) / L ^ (A + C0) := by
    intro d hd2 hdD0 χ hχ
    have hdR : (d : ℝ) ≤ (D0 : ℝ) := by exact_mod_cast hdD0
    have hdN : (d : ℝ) ≤ (Real.log N) ^ C0 := le_trans hdR hD0N
    have hdL : (d : ℝ) ≤ L ^ C0 := le_trans hdR hD0
    have hNM' : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
    have htwist := hbSW N M d χ hN hNM hM2N hd2 hdN hχ
    calc ‖bilinTwist (blockPrimeInd N) M d χ‖
        ≤ (d : ℝ) * (K * N / (Real.log N) ^ (A + 2 * C0)) := htwist
      _ = (d : ℝ) * K * N / (Real.log N) ^ (A + 2 * C0) := by ring
      _ ≤ Kβ * M / L ^ (A + C0) := by
          rw [div_le_div_iff₀ hlogNApos hLAC0pos]
          calc (d : ℝ) * K * N * L ^ (A + C0)
              ≤ L ^ C0 * K * M * L ^ (A + C0) := by
                have hdK : (d : ℝ) * K ≤ L ^ C0 * K := mul_le_mul_of_nonneg_right hdL hK0.le
                have hnum : (d : ℝ) * K * N ≤ L ^ C0 * K * M :=
                  mul_le_mul hdK hNM' (Nat.cast_nonneg N)
                    (mul_nonneg (Real.rpow_nonneg hLpos.le _) hK0.le)
                exact mul_le_mul_of_nonneg_right hnum (Real.rpow_nonneg hLpos.le _)
            _ = (K * L ^ (A + 2 * C0)) * M := by
                have hre : L ^ C0 * K * M * L ^ (A + C0)
                    = (L ^ C0 * L ^ (A + C0)) * K * M := by ring
                rw [hre, hLcomb]; ring
            _ ≤ (Kβ * (Real.log N) ^ (A + 2 * C0)) * M :=
                mul_le_mul_of_nonneg_right hscale hMnn
            _ = Kβ * M * (Real.log N) ^ (A + 2 * C0) := by ring
  -- Assemble via `general_BV_weak`.
  exact general_BV_weak α (blockPrimeInd N) X M R₀ D0 Dset (A := A) (C0 := C0)
    (Kβ := Kβ) (Klarge := Klarge) hα hKβ hDge1 hcop hLpos hD0 hβSW hLargeDisc

end Salt.Chen
