/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CapFreeArm3
import Salt.MR.CaseASocket
import Salt.MR.SPartStation
import Salt.MR.M4ErrRewire

/-!
# `CofactorSupplier` — THE SOCKET'S SUPPLIER AT THE DOOR'S DATUM

⟦THE SOCKET CUT⟧ (2026-07-28, `CapFreeArm3` §4′) freed the row's co-factor datum: the whole
`𝒰`/err leg now carries one predicate,

  `CofactorSocket H N X_d P Q T_ann R_rad t₁ R̄ b`
    `:= ∀ j ∈ I, ∀ |t| ≤ T_ann, R_rad ≤ |t − t₁| → ‖R_{j,H}(1+it)‖ ≤ R̄`,

and `cofactorSocket_of_ellLin` inhabits it at the squarefree-linearised datum `ellLin g`.
The door's own co-factor slot is NOT of that shape: it is the sieved

  `b(m) = 1_𝒮(P·m)·λ(m)·χ̄(m)`   (un-phased — the phase leaves before the row, ⟦U2⟧),

which is COMPLETELY multiplicative only after the sieve indicator is expanded.  This file is
the supplier at that datum.

## THE ROUTE (the residue design v4, `docs/exploration/m4-residue-design-0728.md`)

1. **§1 — the inclusion–exclusion.**  `Sec9Glue.prod_one_sub_gJ` at the argument `P·m`, with
   `gJ`'s complete multiplicativity splitting the shifted indicator: the door's cofactor is a
   SIGNED short combination of the `2^J` completely multiplicative pieces `λχ̄·g_𝒥`,
   `𝒥 ⊆ [1,J]`, with unimodular coefficients `(−1)^{|𝒥|}·g_𝒥(P)`.  `ramR` is linear in its
   datum slot (`CapFreeArm3.ramR_sum_fin`), so the sockets ADD: one socket per piece at `R̄₀`
   gives the door's socket at `2^J·R̄₀`.
2. **§2 — the mask.**  Each piece's prime datum is the block-masked `λχ̄`, which is exactly
   `RamWeight.gxDatum` at the damping parameter `x = 0`, iterated over `𝒥`.  The floor
   transfer therefore costs FACTOR 1 (`gxDatum_pretDistSq_ge_one`), and the debit is the
   block window's Mertens mass (`CofactorDist.blockWindow_mertens_const`).
3. **§3 — the masked floor.**  `CapFreeArm3.CapFreeFloor3` at each piece, from the `1/16`
   arms of the assembled χ-floor with the mask debit subtracted — the ONE place where the
   floor's own excess coefficient `1/16 − 1/32` is spent.

Everything here is ADDITIVE: no landed statement is touched.

## THE PRICING PAGE (the in-brief STOP-check, resolved)

The general-multiplicative CASE-A face pays `SPartCore.cSq = 20736` (Route III's dissection
constant) on the slowest `caseAS2` summand `C_far*₂·(log W)^{−1/(32e)}`, against the freed
ceiling's `(log X)^{−ρ₂₉₃}`.  The `W`-slot at the door instantiation is `kmin`
(`M4MeanSq.m4_cofactorSocket_at_witness` → `USetGradedPrice.Rbd34loc_uniform`), whose gate is
`(1 − 1/loglog X)·log X ≤ log kmin` — the `X^{1−1/loglog X}` corner, NOT the constant
`pin2Gate`.  So the margin exponent `1/(32e) − ρ₂₉₃ ≈ 1.255·10^{−3}` is spent against
`loglog X`, and `C_far*₂` CANCELS (`gradeCR2` carries `12·C_far*₂` itself): the threshold is
`(log X)^{1/(32e)−ρ₂₉₃} ≥ 4·cSq`, i.e. `loglog X ≳ 9.1·10³`.  A threshold, not an
obstruction.
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators
open Finset

/-! ## §1 — THE DOOR'S CO-FACTOR DATUM, SPLIT INTO COMPLETELY MULTIPLICATIVE PIECES -/

/-- **The `𝒥`-piece** `λχ̄·g_𝒥`: the row datum `liouChi χ` masked by `Sec9Glue.gJ`'s
block-avoidance indicator.  Completely multiplicative (both factors are), `1`-bounded, and
`1` at `1` — the three structural facts the CASE-A/B pocket machinery reads. -/
def pieceDatum {q : ℕ} (χ : DirichletCharacter ℂ q) (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) :
    ℕ → ℂ :=
  fun m => liouChi χ m * gJ 𝒥 Pseq Qseq m

/-- **The door's UN-PHASED co-factor slot** at the block pin `P`: `M4ErrRewire.doorCofactor`
with the phase removed (⟦U2⟧ — Part C's re-cut takes the phase off before the row). -/
def doorCofactor0 {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ) (J P : ℕ) :
    ℕ → ℂ :=
  fun m => (if MemS Pseq Qseq J (P * m) then (1 : ℂ) else 0) * liouChi χ m

/-- The signed coefficient of the `𝒥`-piece: `(−1)^{|𝒥|}·g_𝒥(P)`, unimodular. -/
def pieceSign (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (P : ℕ) : ℂ :=
  (-1) ^ 𝒥.card * gJ 𝒥 Pseq Qseq P

lemma norm_gJ_le_one (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (n : ℕ) :
    ‖gJ 𝒥 Pseq Qseq n‖ ≤ 1 := by
  unfold gJ
  split_ifs
  · rw [norm_one]
  · rw [norm_zero]; norm_num

lemma norm_pieceSign_le_one (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (P : ℕ) :
    ‖pieceSign 𝒥 Pseq Qseq P‖ ≤ 1 := by
  unfold pieceSign
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact norm_gJ_le_one 𝒥 Pseq Qseq P

lemma norm_pieceDatum_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (𝒥 : Finset ℕ)
    (Pseq Qseq : ℕ → ℕ) (m : ℕ) : ‖pieceDatum χ 𝒥 Pseq Qseq m‖ ≤ 1 := by
  unfold pieceDatum
  rw [norm_mul]
  have h1 := norm_liouChi_le_one χ m
  have h2 := norm_gJ_le_one 𝒥 Pseq Qseq m
  nlinarith [norm_nonneg (liouChi χ m), norm_nonneg (gJ 𝒥 Pseq Qseq m)]

@[simp] lemma gJ_one (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) : gJ 𝒥 Pseq Qseq 1 = 1 := by
  unfold gJ
  refine if_pos (fun j _ => ?_)
  unfold blockOmega BlockPrimeDivs
  simp

lemma pieceDatum_one {q : ℕ} (χ : DirichletCharacter ℂ q) (𝒥 : Finset ℕ)
    (Pseq Qseq : ℕ → ℕ) : pieceDatum χ 𝒥 Pseq Qseq 1 = 1 := by
  unfold pieceDatum liouChi
  simp

/-- **THE PIECE IS COMPLETELY MULTIPLICATIVE** — no coprimality, and no exception at `0`
(both `liouChi` and the piece vanish there). -/
lemma pieceDatum_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (𝒥 : Finset ℕ)
    (Pseq Qseq : ℕ → ℕ) (m n : ℕ) :
    pieceDatum χ 𝒥 Pseq Qseq (m * n)
      = pieceDatum χ 𝒥 Pseq Qseq m * pieceDatum χ 𝒥 Pseq Qseq n := by
  unfold pieceDatum
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [liouChi]
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [liouChi]
    · rw [liouChi_mul, gJ_mul 𝒥 Pseq Qseq (by omega) (by omega)]
      ring

/-- **The inclusion–exclusion expansion of `Sec9Glue.gJ`'s product form.**
`∏_{j∈s}(1 − g_{{j}}(n)) = Σ_{𝒥 ⊆ s} (−1)^{|𝒥|}·g_𝒥(n)` — `Finset.prod_add` at
`f = −g_{{·}}`, `g = 1`, with `prod_gJ_singleton` collapsing each subset product. -/
theorem prod_one_sub_gJ_expand (s : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (n : ℕ) :
    ∏ j ∈ s, (1 - gJ {j} Pseq Qseq n)
      = ∑ 𝒥 ∈ s.powerset, (-1) ^ 𝒥.card * gJ 𝒥 Pseq Qseq n := by
  classical
  have hrw : ∀ j ∈ s, (1 - gJ {j} Pseq Qseq n) = (-(gJ {j} Pseq Qseq n)) + 1 :=
    fun j _ => by ring
  rw [Finset.prod_congr rfl hrw,
    Finset.prod_add (fun j => -(gJ {j} Pseq Qseq n)) (fun _ => (1 : ℂ)) s]
  refine Finset.sum_congr rfl (fun 𝒥 h𝒥 => ?_)
  rw [Finset.prod_const_one, mul_one]
  have hneg : ∏ j ∈ 𝒥, (-(gJ {j} Pseq Qseq n))
      = (∏ _j ∈ 𝒥, (-1 : ℂ)) * ∏ j ∈ 𝒥, gJ {j} Pseq Qseq n := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => by ring)
  rw [hneg, Finset.prod_const, prod_gJ_singleton]

/-- **THE DOOR'S CO-FACTOR SLOT, SPLIT** (`doorCofactor0_split`).  At every `m` — including
`m = 0` and `P ∣ m` — the door's un-phased co-factor datum is the signed sum of the `2^J`
completely multiplicative pieces:

  `1_𝒮(P·m)·λ(m)χ̄(m) = Σ_{𝒥 ⊆ [1,J]} (−1)^{|𝒥|}·g_𝒥(P) · (λχ̄·g_𝒥)(m)`.

The shifted indicator factorises because `g_𝒥` is completely multiplicative (`gJ_mul`), which
is exactly what the un-shifted MR expansion cannot do. -/
theorem doorCofactor0_split {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J P : ℕ) (hP : 1 ≤ P) (m : ℕ) :
    doorCofactor0 χ Pseq Qseq J P m
      = ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
          pieceSign 𝒥 Pseq Qseq P * pieceDatum χ 𝒥 Pseq Qseq m := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hz : ∀ 𝒥 : Finset ℕ, pieceDatum χ 𝒥 Pseq Qseq 0 = 0 := by
      intro 𝒥; unfold pieceDatum liouChi; simp
    unfold doorCofactor0 liouChi
    simp [hz]
  · have hPm : P * m ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    have hind : (if MemS Pseq Qseq J (P * m) then (1 : ℂ) else 0)
        = ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
            (-1) ^ 𝒥.card * (gJ 𝒥 Pseq Qseq P * gJ 𝒥 Pseq Qseq m) := by
      rw [← prod_one_sub_gJ Pseq Qseq J (P * m), prod_one_sub_gJ_expand]
      exact Finset.sum_congr rfl
        (fun 𝒥 _ => by rw [gJ_mul 𝒥 Pseq Qseq (by omega) (by omega)])
    unfold doorCofactor0
    rw [hind, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun 𝒥 _ => ?_)
    unfold pieceSign pieceDatum
    ring

/-! ## §1′ — the socket adds over a `Finset` of pieces -/

/-- **`ramR` IS LINEAR IN ITS CO-FACTOR SLOT, over a `Finset`** (`ramR_sum_finset`).  The
`Finset`-indexed twin of `CapFreeArm3.ramR_sum_fin` — the index the inclusion–exclusion
actually carries is the powerset of `[1,J]`, not `Fin n`. -/
lemma ramR_sum_finset {ι : Type*} (s : Finset ι) (H : ℝ) (N Xd P Q j : ℕ) (ε : ι → ℂ)
    (bp : ι → ℕ → ℂ) (t : ℝ) :
    ramR H N Xd P Q j (fun m => ∑ i ∈ s, ε i * bp i m) t
      = ∑ i ∈ s, ε i * ramR H N Xd P Q j (bp i) t := by
  simp only [ramR, Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

/-- **THE SOCKET IS CLOSED UNDER SIGNED `Finset` COMBINATIONS**
(`cofactorSocket_of_pieces_finset`).  `CapFreeArm3.cofactorSocket_of_pieces` at a `Finset`
index; the proof is the same triangle inequality over `ramR_sum_finset`. -/
theorem cofactorSocket_of_pieces_finset {ι : Type*} {s : Finset ι} {H : ℝ} {N Xd P Q : ℕ}
    {Tann Rrad t₁ : ℝ} {b : ℕ → ℂ} {bp : ι → ℕ → ℂ} {ε : ι → ℂ} {Rb : ι → ℝ}
    (hε : ∀ i ∈ s, ‖ε i‖ ≤ 1) (hb : ∀ m, b m = ∑ i ∈ s, ε i * bp i m)
    (hs : ∀ i ∈ s, CofactorSocket H N Xd P Q Tann Rrad t₁ (Rb i) (bp i)) :
    CofactorSocket H N Xd P Q Tann Rrad t₁ (∑ i ∈ s, Rb i) b := by
  intro j hj t ht hfar
  have hbeq : b = fun m => ∑ i ∈ s, ε i * bp i m := funext hb
  rw [hbeq, ramR_sum_finset]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
  have hi' := hs i hi j hj t ht hfar
  rw [norm_mul]
  calc ‖ε i‖ * ‖ramR H N Xd P Q j (bp i) t‖
      ≤ 1 * Rb i := mul_le_mul (hε i hi) hi' (norm_nonneg _) (by norm_num)
    _ = Rb i := one_mul _

/-- **THE DOOR'S SOCKET FROM THE PIECES' SOCKETS** (`cofactorSocket_door_of_pieces`).  One
uniform per-piece ceiling `R̄₀` gives the door's un-phased co-factor datum a socket at
`2^J·R̄₀`: the `2^J` is `((Icc 1 J).powerset).card`, and every coefficient is unimodular.

This is the assembly the ⟦SOCKET CUT⟧ was made for; what remains is the per-piece socket,
which §§2–3 (the mask and the masked floor) and the CASE-A engine supply. -/
theorem cofactorSocket_door_of_pieces {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Pseq Qseq : ℕ → ℕ) {H : ℝ} {N Xd P Q J : ℕ} {Tann Rrad t₁ Rbar0 : ℝ} (hP : 1 ≤ P)
    (hs : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset,
      CofactorSocket H N Xd P Q Tann Rrad t₁ Rbar0 (pieceDatum χ 𝒥 Pseq Qseq)) :
    CofactorSocket H N Xd P Q Tann Rrad t₁ (2 ^ J * Rbar0)
      (doorCofactor0 χ Pseq Qseq J P) := by
  classical
  have hcard : ((Finset.Icc 1 J).powerset).card = 2 ^ J := by
    rw [Finset.card_powerset, Nat.card_Icc]
    simp
  have hsum : ∑ _𝒥 ∈ (Finset.Icc 1 J).powerset, Rbar0 = 2 ^ J * Rbar0 := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    norm_num
  rw [← hsum]
  exact cofactorSocket_of_pieces_finset
    (fun 𝒥 _ => norm_pieceSign_le_one 𝒥 Pseq Qseq P)
    (doorCofactor0_split χ Pseq Qseq J P hP) hs

/-! ## §2 — THE MASK: the piece's prime datum IS `gxDatum` at `x = 0`

`RamWeight.gxDatum g P Q x` multiplies the datum by `x` on the block window `[P,Q]`; at
`x = 0` that is exactly the block-AVOIDANCE mask `g_{{j}}` applies at primes.  So the
piece's floor transfer is `gxDatum_pretDistSq_ge_one` iterated over `𝒥`, at FACTOR 1 — the
`(1 − x)` of the damping page is `1`, and the debit is the block window's Mertens mass. -/

/-- `ω(p; P, Q)` at a bare prime (`blockOmega_prime_pow` at `k = 1`). -/
lemma blockOmega_prime {P Q p : ℕ} (hp : p.Prime) :
    blockOmega P Q p = if P ≤ p ∧ p ≤ Q then 1 else 0 := by
  have h := blockOmega_prime_pow (P := P) (Q := Q) hp (k := 1) one_ne_zero
  simpa using h

/-- The single-block avoidance factor at a prime: `1` off the block, `0` on it. -/
lemma gJ_singleton_prime (j : ℕ) (Pseq Qseq : ℕ → ℕ) {p : ℕ} (hp : p.Prime) :
    gJ {j} Pseq Qseq p = if Pseq j ≤ p ∧ p ≤ Qseq j then (0 : ℂ) else 1 := by
  have hiff : (∀ i ∈ ({j} : Finset ℕ), blockOmega (Pseq i) (Qseq i) p = 0)
      ↔ blockOmega (Pseq j) (Qseq j) p = 0 := by simp
  unfold gJ
  rw [if_congr hiff rfl rfl, blockOmega_prime hp]
  by_cases hw : Pseq j ≤ p ∧ p ≤ Qseq j
  · rw [if_pos hw, if_pos hw, if_neg one_ne_zero]
  · rw [if_neg hw, if_neg hw, if_pos rfl]

/-- `g_{insert j 𝒥} = g_{{j}}·g_𝒥` (for `j ∉ 𝒥`) — `gJ_eq_prod` at `Finset.prod_insert`. -/
lemma gJ_insert {j : ℕ} {𝒥 : Finset ℕ} (hj : j ∉ 𝒥) (Pseq Qseq : ℕ → ℕ) (n : ℕ) :
    gJ (insert j 𝒥) Pseq Qseq n = gJ {j} Pseq Qseq n * gJ 𝒥 Pseq Qseq n := by
  simp only [gJ_eq_prod, Finset.prod_insert hj, Finset.prod_singleton]

/-- **THE MASK, ONE BLOCK AT A TIME.**  At every prime, adding the block `j` to the piece's
index set is the `x = 0` damping of `RamWeight.gxDatum` at that block. -/
lemma pieceDatum_insert_prime {q : ℕ} (χ : DirichletCharacter ℂ q) {j : ℕ} {𝒥 : Finset ℕ}
    (hj : j ∉ 𝒥) (Pseq Qseq : ℕ → ℕ) {p : ℕ} (hp : p.Prime) :
    pieceDatum χ (insert j 𝒥) Pseq Qseq p
      = gxDatum (pieceDatum χ 𝒥 Pseq Qseq) (Pseq j) (Qseq j) 0 p := by
  unfold pieceDatum gxDatum
  rw [gJ_insert hj, gJ_singleton_prime j Pseq Qseq hp]
  by_cases hw : Pseq j ≤ p ∧ p ≤ Qseq j
  · rw [if_pos hw, if_pos hw]; push_cast; ring
  · rw [if_neg hw, if_neg hw]; ring

/-- **THE FLOOR TRANSFER TO THE MASKED PIECE** (`pretDistSq_pieceDatum_ge`).  Masking the row
datum on the blocks of `𝒥` costs at most the SUM of those blocks' Mertens window masses:

  `𝔻²(λχ̄, w; X) − Σ_{j∈𝒥} Σ_{P_j ≤ p ≤ Q_j, p ≤ X} 1/p  ≤  𝔻²(λχ̄·g_𝒥, w; X)`.

Factor `1`, not `(1 − x)`: `gxDatum_pretDistSq_ge_one` at `x = 0`, iterated over `𝒥` by
`Finset.induction`, with `CapFreeArm.pretDistSq_ellLin_eq` stripping the linearisation on
both sides (`𝔻²` reads its datum at primes only). -/
theorem pretDistSq_pieceDatum_ge {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    {w : ℕ → ℂ} (hw : ∀ p : ℕ, p.Prime → ‖w p‖ ≤ 1) (X : ℝ) (𝒥 : Finset ℕ) :
    pretDistSq (liouChi χ) w X
        - ∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)
      ≤ pretDistSq (pieceDatum χ 𝒥 Pseq Qseq) w X := by
  classical
  induction 𝒥 using Finset.induction_on with
  | empty =>
      have hbase : pretDistSq (pieceDatum χ ∅ Pseq Qseq) w X = pretDistSq (liouChi χ) w X := by
        refine pretDistSq_congr_primes (fun p _ => ?_) X
        unfold pieceDatum
        rw [gJ_empty, mul_one]
      rw [hbase, Finset.sum_empty]
      linarith
  | insert j 𝒥 hj ih =>
      have hpc : ∀ p : ℕ, p.Prime → ‖pieceDatum χ 𝒥 Pseq Qseq p‖ ≤ 1 :=
        fun p _ => norm_pieceDatum_le_one χ 𝒥 Pseq Qseq p
      have heq : pretDistSq (pieceDatum χ (insert j 𝒥) Pseq Qseq) w X
          = pretDistSq (gxDatum (pieceDatum χ 𝒥 Pseq Qseq) (Pseq j) (Qseq j) 0) w X :=
        pretDistSq_congr_primes (fun p hp => pieceDatum_insert_prime χ hj Pseq Qseq hp) X
      have hstep := gxDatum_pretDistSq_ge_one (g := pieceDatum χ 𝒥 Pseq Qseq)
        (w := w) (P := Pseq j) (Q := Qseq j) (x := 0) (X := X) le_rfl zero_le_one hpc hw
      rw [pretDistSq_ellLin_eq, pretDistSq_ellLin_eq] at hstep
      rw [heq, Finset.sum_insert hj]
      linarith [ih]

/-! ## §3 — THE MASKED FLOOR

`CapFreeArm3.CapFreeFloor3` demands `(1/32)loglog X + 25 < 𝔻²` on the whole `3X` box.  The
piece's floor is the row datum's LESS the mask debit, so the row datum must clear the demand
with that debit to spare — which is exactly the excess coefficient `1/16 − 1/32` the three
χ-floor arms carry.  §3a re-runs `CapFreeAssembly.capFreeFloor3_all_chi`'s assembly keeping
the margin `D` explicit; §3b spends it on the mask. -/

/-- **THE ASSEMBLED χ-FLOOR, WITH MARGIN** (`capFreeFloor3_margin_all_chi`).
`CapFreeAssembly.capFreeFloor3_all_chi` with an arbitrary extra margin `D ≥ 0` carried in the
threshold and delivered in the conclusion.  Same three arms, same splits; the VK arm is taken
at its POINTWISE form (`VkTwistClose.chi_floor_vk_pointwise` + `VkTwistLadder.vkTwistUB_holds`)
rather than through the margin-free `capFreeFloor3_lamChi_unconditional`, because the margin
is exactly what that wrapper spends. -/
theorem capFreeFloor3_margin_all_chi (Qm : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X D : ℝ), q ≤ Qm →
      Real.exp (Real.exp 1) ≤ X → 0 ≤ D →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + K + 25 + D)
        < Real.log (Real.log X) →
      ∀ v : ℝ, |v| ≤ 3 * X →
        (1 / 32) * Real.log (Real.log X) + 25 + D < pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨Kvk, hvk⟩ := chi_floor_vk_pointwise
  obtain ⟨Kbulk, hbulk⟩ := chi_floor_real_bulk
  obtain ⟨Kband, hband⟩ := chi_floor_band_arm Qm
  refine ⟨max 0 (max Kvk (max Kbulk Kband)), le_max_left _ _, ?_⟩
  set K : ℝ := max 0 (max Kvk (max Kbulk Kband)) with hKdef
  have hK0 : 0 ≤ K := le_max_left _ _
  have hKvk : Kvk ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKbulk : Kbulk ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hKband : Kband ≤ K :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  intro q _ χ X D hq hX hD0 hthr v hv
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hC1 : (1 : ℝ) ≤ vkEulerCorr q * vkTwistConst q := by
    nlinarith [one_le_vkEulerCorr q, one_le_vkTwistConst (q := q)]
  have hvkD : (0 : ℝ) ≤ vkDebitConst (vkEulerCorr q * vkTwistConst q) :=
    vkDebitConst_nonneg hC1
  have hvkM : (0 : ℝ) ≤ vkMidDebit q := vkMidDebit_nonneg q
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  by_cases hsq : χ ^ 2 = 1
  · by_cases hband2 : |v| ≤ 1 / 2
    · have h := hband q χ X v hq hX hband2
      linarith
    · have hvbig : 1 / 2 ≤ |v| := le_of_lt (not_le.mp hband2)
      have h := hbulk q χ X v hq0 hsq hX hvbig hv
      linarith
  · -- the VK arm, at its pointwise form (the socket is `vkTwistUB_holds`)
    have hψ : (χ ^ 2 : DirichletCharacter ℂ q) ≠ 1 := hsq
    have hsock : Real.exp (Real.exp 100) ≤ |v| →
        VkTwistUB (vkEulerCorr q * vkTwistConst q) (χ ^ 2) X (2 * v) := by
      intro hbig
      have h2v : Real.exp (Real.exp 100) ≤ |2 * v| := by
        have hle : |v| ≤ |2 * v| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          nlinarith [abs_nonneg v]
        linarith
      exact vkTwistUB_holds (χ ^ 2) hψ hXe h2v
    have h := hvk q χ (vkEulerCorr q * vkTwistConst q) X v hC1 hsq hX hv hsock
    linarith

/-- **THE MASKED FLOOR** (`capFreeFloor3_pieceDatum`).  Every inclusion–exclusion piece
`λχ̄·g_𝒥` carries `CapFreeArm3.CapFreeFloor3` at the row's own scale, provided the χ-floor's
threshold is met with the mask debit `D` — the sum of the masked blocks' Mertens masses —
added.  The debit is carried as a HYPOTHESIS (law #253): §4 evaluates it at the door's own
block ladder, where it is `X`-FREE. -/
theorem capFreeFloor3_pieceDatum (Qm : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X D : ℝ), q ≤ Qm →
      Real.exp (Real.exp 1) ≤ X → 0 ≤ D →
      (∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)) ≤ D →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + K + 25 + D)
        < Real.log (Real.log X) →
        CapFreeFloor3 (pieceDatum χ 𝒥 Pseq Qseq) X := by
  obtain ⟨K, hK0, hK⟩ := capFreeFloor3_margin_all_chi Qm
  refine ⟨K, hK0, ?_⟩
  intro q _ χ Pseq Qseq 𝒥 X D hq hX hD0 hdebit hthr v hv
  have hmargin := hK q χ X D hq hX hD0 hthr v hv
  have hcw : ∀ p : ℕ, p.Prime → ‖costwist v p‖ ≤ 1 :=
    fun p _ => le_of_eq (costwist_norm v p)
  have htr := pretDistSq_pieceDatum_ge χ Pseq Qseq hcw X 𝒥 (w := costwist v)
  rw [pretDistSq_liouChi_eq] at htr
  linarith

/-! ## §4 — THE DAMPED DATUM AT A GENERAL MULTIPLICATIVE `b`

`CofactorBall.ramRdampCoeff` is already datum-generic: at a general `b` its value inside the
co-factor window is `b(m)·x^{ω(m;P,Q)}`.  At `b = ellLin g` the ⟦V5⟧ absorption identity
rewrites that as `ellLin (g_x)` — which is why the whole landed CASE-A/B chain is stated in
the `ellLin` slot.  At a general `b` there is no such rewrite: the damped datum is
multiplicative on COPRIMES (`RamWeight.blockOmega_pow_mul_coprime`) but not completely
multiplicative, which is precisely why the general face pays Route III's `cSq`.

What IS free is the pretentious side: `𝔻²` reads its datum at primes only, and at a prime
`x^{ω(p)}` is the `gxDatum` window factor.  So every pocket/floor page transports verbatim. -/

/-- **The damped general datum** `b·x^{ω(·;P,Q)}` — `ramRdampCoeff`'s value on the window. -/
def dampDatum (b : ℕ → ℂ) (P Q : ℕ) (x : ℝ) : ℕ → ℂ :=
  fun m => b m * ((x : ℝ) : ℂ) ^ blockOmega P Q m

lemma ramRdampCoeff_damp (H : ℝ) (N Xn P Q j : ℕ) (b : ℕ → ℂ) (x : ℝ) (m : ℕ) :
    ramRdampCoeff H N Xn P Q j b x m
      = if m ∈ ramRrange H N Xn j then dampDatum b P Q x m else 0 := rfl

/-- At a prime the damping is `RamWeight.gxDatum`'s window factor (`ω(p) ∈ {0,1}`). -/
lemma dampDatum_prime {b : ℕ → ℂ} {P Q : ℕ} {x : ℝ} {p : ℕ} (hp : p.Prime) :
    dampDatum b P Q x p = gxDatum b P Q x p := by
  unfold dampDatum gxDatum
  rw [blockOmega_prime hp]
  by_cases hw : P ≤ p ∧ p ≤ Q
  · rw [if_pos hw, if_pos hw, pow_one]
  · rw [if_neg hw, if_neg hw, pow_zero]

/-- **THE POCKET SIDE IS FREE.**  `𝔻²` at the damped general datum IS `𝔻²` at the landed
`ellLin (g_x)` slot — the two agree at every prime. -/
lemma pretDistSq_dampDatum_eq (b : ℕ → ℂ) (P Q : ℕ) (x : ℝ) (w : ℕ → ℂ) (X : ℝ) :
    pretDistSq (dampDatum b P Q x) w X = pretDistSq (ellLin (gxDatum b P Q x)) w X :=
  pretDistSq_congr_primes
    (fun _p hp => (dampDatum_prime hp).trans
      (ellLin_apply_prime (g := gxDatum b P Q x) hp).symm) X

lemma norm_dampDatum_le_one {b : ℕ → ℂ} (hb : ∀ n : ℕ, ‖b n‖ ≤ 1) (P Q : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) : ‖dampDatum b P Q x m‖ ≤ 1 := by
  unfold dampDatum
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  have hp1 : x ^ blockOmega P Q m ≤ 1 := pow_le_one₀ hx0 hx1
  have hp0 : (0 : ℝ) ≤ x ^ blockOmega P Q m := pow_nonneg hx0 _
  nlinarith [hb m, norm_nonneg (b m)]

lemma blockOmega_one (P Q : ℕ) : blockOmega P Q 1 = 0 := by
  unfold blockOmega BlockPrimeDivs
  simp

lemma dampDatum_one {b : ℕ → ℂ} (hb1 : b 1 = 1) (P Q : ℕ) (x : ℝ) :
    dampDatum b P Q x 1 = 1 := by
  unfold dampDatum
  rw [blockOmega_one, pow_zero, hb1, one_mul]

lemma dampDatum_mul_coprime {b : ℕ → ℂ}
    (hbmul : ∀ m n : ℕ, Nat.Coprime m n → b (m * n) = b m * b n) (P Q : ℕ) (x : ℝ)
    {m n : ℕ} (hco : Nat.Coprime m n) :
    dampDatum b P Q x (m * n) = dampDatum b P Q x m * dampDatum b P Q x n := by
  unfold dampDatum
  rw [hbmul m n hco, blockOmega_pow_mul_coprime ((x : ℝ) : ℂ) hco]
  ring

/-! ### §4′ — the pocket socket and the contour box, at the general datum -/

/-- **THE COLLISION SOCKET AT THE GENERAL DATUM** (`PocketSocket3Gen`).
`CapFreeArm3.PocketSocket3` with its pocket stated at the damped general datum. -/
def PocketSocket3Gen (b : ℕ → ℂ) (P Q : ℕ) (X θ t₁ : ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ t₁' : ℝ, |t₁'| ≤ 3 * X →
    pretDistSq (dampDatum b P Q x) (costwist t₁') X
        ≤ (1 / 32 - θ) * Real.log (Real.log X) →
    |t₁' - t₁| < 1

/-- **THE CAP-FREE SUPPLIER AT THE GENERAL DATUM, VACUOUSLY** (`pocketSocket3Gen_of_floor3`).
`CapFreeArm3.pocketSocket_of_floor3` read through `pretDistSq_dampDatum_eq`: the floor kills
the pocket on the whole `3X` box, at every damping, for the general datum too. -/
theorem pocketSocket3Gen_of_floor3 {b : ℕ → ℂ} (hb : ∀ p : ℕ, p.Prime → ‖b p‖ ≤ 1) {P Q : ℕ}
    {X θ : ℝ} (hθ0 : 0 < θ) (hθ32 : θ ≤ 1 / 32) (hLX : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X θ ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q)
    (hfloor : CapFreeFloor3 b X) (t₁ : ℝ) :
    PocketSocket3Gen b P Q X θ t₁ := by
  intro x hx0 hx1 t₁' ht₁' hpock
  rw [pretDistSq_dampDatum_eq] at hpock
  exact absurd hpock
    (no_pocket_of_floor3 hb P Q hx0 hx1 hθ0 hθ32 hLX hPlow hQhigh hPQ hfloor ht₁')

/-- **THE CONTOUR BOX AT THE GENERAL DATUM** (`box_gate_le_3X_gen`).  `CapFreeArm3.box_gate_le_3X`
at the general datum's pretentious slot — the same dichotomy, transported by
`pretDistSq_dampDatum_eq`. -/
theorem box_gate_le_3X_gen {b : ℕ → ℂ} (hb : ∀ p : ℕ, p.Prime → ‖b p‖ ≤ 1) (P Q : ℕ)
    {k₀ M : ℕ} {X θ t x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hk₀pin : pin2Gate ≤ (k₀ : ℝ)) (hMX : (M : ℝ) ≤ X)
    (hTM : |t| + Tstar2 (M : ℝ) (Real.log (M : ℝ)) ≤ 3 * X) :
    (∀ k : ℕ, k₀ ≤ k → k ≤ M → ∀ v : ℝ, |v - t| ≤ Tstar2 (k : ℝ) (Real.log (k : ℝ)) →
        cofactorMfl X θ (k₀ : ℝ) ≤ pretDistSq (dampDatum b P Q x) (costwist v) (k : ℝ))
      ∨ (∃ t₁' : ℝ, |t - t₁'| ≤ Tstar2 (M : ℝ) (Real.log (M : ℝ)) ∧ |t₁'| ≤ 3 * X ∧
          pretDistSq (dampDatum b P Q x) (costwist t₁') X
            ≤ (1 / 32 - θ) * Real.log (Real.log X)) := by
  rcases box_gate_le_3X hb P Q hx0 hx1 hk₀pin hMX hTM with hA | hB
  · left
    intro k hk1 hk2 v hv
    rw [pretDistSq_dampDatum_eq]
    exact hA k hk1 hk2 v hv
  · right
    obtain ⟨t₁', h1, h2, h3⟩ := hB
    exact ⟨t₁', h1, h2, by rw [pretDistSq_dampDatum_eq]; exact h3⟩

/-! ## §5 — THE CO-FACTOR BOUND AT THE GENERAL DATUM

`CapFreeArm3.cofactor_Rbd34_local_nocap3` is the row's ONE reader of the datum's structure.
Its generic twin below reads exactly three facts — `b 1 = 1`, coprime multiplicativity and
`1`-boundedness — plus the two sockets, and pays the CASE-A exit constant `S` the caller
names.  `S` is FREE: at `b = ellLin g` the caller supplies `caseAS2 …`, and at the door's
general datum the Route-III face supplies its `cSq`-inflated twin. -/

/-- **THE CASE-A SOCKET AT THE GENERAL DATUM** (`CaseASocketGen`).  `USetGradedPrice.CaseASocket2`
at the damped general datum and at a FREE exit constant `S`: under the window floor on the
`T*₂`-windows, the damped datum's twisted partial sums are linear with constant `S`. -/
def CaseASocketGen (b : ℕ → ℂ) (P Q : ℕ) (X θ : ℝ) (k₀ M : ℕ) (t S : ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
    (∀ k : ℕ, k₀ ≤ k → k ≤ M → ∀ v : ℝ, |v - t| ≤ Tstar2 (k : ℝ) (Real.log (k : ℝ)) →
      cofactorMfl X θ (k₀ : ℝ) ≤ pretDistSq (dampDatum b P Q x) (costwist v) (k : ℝ)) →
    ∀ k : ℕ, k₀ ≤ k → k ≤ M →
      ‖∑ n ∈ Finset.Icc 1 k, dampDatum b P Q x n * eIu (-t) n‖ ≤ S * (k : ℝ)

/-- **The fused `Rbd` at the general datum** — `USetGradedPrice.cofactorRbd34loc` with the
CASE-A arm's constant free.  At `S := caseAS2 c Cb (cofactorMfl X θ W) W` the two agree. -/
def cofactorRbdGen (S W Y Rmax R : ℝ) : ℝ := 3 * max (2 * S) (farSupS34 W Y Rmax R)

lemma cofactorRbdGen_eq_loc (c Cb X θ W Y Rmax R : ℝ) :
    cofactorRbdGen (caseAS2 c Cb (cofactorMfl X θ W) W) W Y Rmax R
      = cofactorRbd34loc c Cb X θ W Y Rmax R := rfl

lemma cofactorRbdGen_nonneg {S W Y Rmax R : ℝ} (hS0 : 0 ≤ S) :
    0 ≤ cofactorRbdGen S W Y Rmax R := by
  unfold cofactorRbdGen
  have h : 2 * S ≤ max (2 * S) (farSupS34 W Y Rmax R) := le_max_left _ _
  linarith

/-- **E-2a AT THE GENERAL DATUM** (`caseA_damped_partial_gen`).
`CofactorGrade.caseA_damped_partial` with `ellLin (g_x)` replaced by the damped general
datum: the co-factor coefficient is supported in `(k₀, M]`, where it IS the damped datum, so
its twisted partial sum is the difference of two of the supply's — the exit's factor `2`. -/
theorem caseA_damped_partial_gen {b : ℕ → ℂ} {H : ℝ} {N Xn P Q j M k₀ : ℕ} {x t S : ℝ}
    (hS0 : 0 ≤ S) (hMN : M ≤ N) (hk₀M : k₀ ≤ M)
    (hk₀lo : (k₀ : ℝ) < ramRbot H Xn j) (hk₀hi : ramRbot H Xn j ≤ (k₀ : ℝ) + 1)
    (hhigh : (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1))
    (hsup : ∀ k : ℕ, k₀ ≤ k → k ≤ M →
      ‖∑ n ∈ Finset.Icc 1 k, dampDatum b P Q x n * eIu (-t) n‖ ≤ S * (k : ℝ)) :
    ∀ m : ℕ, m ≤ M →
      ‖spolyA (ramRdampCoeff H N Xn P Q j b x) t m‖ ≤ 2 * S * (m : ℝ) := by
  have hMtop2 : (M : ℝ) ≤ 2 * ramRbot H Xn j := by linarith
  have hsupp : ∀ n : ℕ, n ≤ k₀ → ramRdampCoeff H N Xn P Q j b x n = 0 := by
    intro n hn
    have hlt : (n : ℝ) < ramRbot H Xn j := by
      have : (n : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hn
      linarith
    rw [ramRdampCoeff, if_neg (notMem_ramRrange_of_lt hlt)]
  have hDatum : ∀ n : ℕ, k₀ < n → n ≤ M →
      ramRdampCoeff H N Xn P Q j b x n = dampDatum b P Q x n := by
    intro n hn1 hn2
    have hmem : n ∈ ramRrange H N Xn j := by
      have hnk : (k₀ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn1
      have hnM : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn2
      rw [ramRrange, Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, le_trans hn2 hMN⟩, ?_, ?_⟩
      · have : ramRbot H Xn j ≤ (n : ℝ) := by linarith
        rwa [ramRbot] at this
      · have : (n : ℝ) ≤ 2 * ramRbot H Xn j := le_trans hnM hMtop2
        rw [ramRbot] at this
        linarith
    rw [ramRdampCoeff_damp, if_pos hmem]
  intro m hm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rcases le_or_gt m k₀ with hcase | hcase
  · have hz : spolyA (ramRdampCoeff H N Xn P Q j b x) t m = 0 := by
      unfold spolyA
      refine Finset.sum_eq_zero (fun n hn => ?_)
      have hnm : n ≤ m := (Finset.mem_Icc.mp hn).2
      rw [hsupp n (le_trans hnm hcase), zero_div]
    rw [hz, norm_zero]
    exact mul_nonneg (by linarith) hm0
  · have hkm : k₀ ≤ m := hcase.le
    have hk₀m : (k₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    have hsplit := spolyA_window_split hsupp hDatum t hkm hm
    have h1 := hsup m hkm hm
    have h2 := hsup k₀ le_rfl hk₀M
    rw [hsplit]
    calc ‖(∑ n ∈ Finset.Icc 1 m, dampDatum b P Q x n * eIu (-t) n)
            - ∑ n ∈ Finset.Icc 1 k₀, dampDatum b P Q x n * eIu (-t) n‖
        ≤ ‖∑ n ∈ Finset.Icc 1 m, dampDatum b P Q x n * eIu (-t) n‖
          + ‖∑ n ∈ Finset.Icc 1 k₀, dampDatum b P Q x n * eIu (-t) n‖ := norm_sub_le _ _
      _ ≤ S * (m : ℝ) + S * (k₀ : ℝ) := add_le_add h1 h2
      _ ≤ 2 * S * (m : ℝ) := by nlinarith

/-- **THE CASE-B ADAPTER AT THE GENERAL DATUM** (`damped_partial_transfer_34_gen`).
`USetGradedPrice.damped_partial_transfer_34` at the damped general datum: `Transfer34`'s
binder shape is FULLY generic (`f 1 = 1`, coprime multiplicativity, `1`-boundedness), and the
damped datum meets it — `dampDatum_one`, `dampDatum_mul_coprime`, `norm_dampDatum_le_one`. -/
theorem damped_partial_transfer_34_gen {b : ℕ → ℂ} (hb1 : b 1 = 1)
    (hbmul : ∀ m n : ℕ, Nat.Coprime m n → b (m * n) = b m * b n) (hble : ∀ n : ℕ, ‖b n‖ ≤ 1)
    {H : ℝ} {N Xn P Q j M k₀ : ℕ} {x t t₁' Rmax R X θ : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hk₀th : ballQuarterThreshold ≤ (k₀ : ℝ)) (hMN : M ≤ N)
    (hk₀lo : (k₀ : ℝ) < ramRbot H Xn j) (hk₀hi : ramRbot H Xn j ≤ (k₀ : ℝ) + 1)
    (hhigh : (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1)) (hMX : (M : ℝ) ≤ X)
    (hgate : 18 + Real.log (Real.log X) - Real.log (Real.log (k₀ : ℝ))
      ≤ 32 * θ * Real.log (Real.log X))
    (hcap : pretDistSq (dampDatum b P Q x) (costwist t₁') X
      ≤ (1 / 32 - θ) * Real.log (Real.log X))
    (hR0 : 0 < R) (hRle : R ≤ 1 + |t - t₁'|) (hRmax : |t - t₁'| ≤ Rmax) :
    ∀ m : ℕ, m ≤ M →
      ‖spolyA (ramRdampCoeff H N Xn P Q j b x) t m‖
        ≤ farSupS34 (k₀ : ℝ) (M : ℝ) Rmax R * (m : ℝ) := by
  have hMk : (M : ℝ) ≤ 2 * (k₀ : ℝ) := by linarith
  have hMtop2 : (M : ℝ) ≤ 2 * ramRbot H Xn j := by linarith
  refine far_transfer_sup_34_of_pocket_cap (f := dampDatum b P Q x) hMk
    (dampDatum_one hb1 P Q x) (fun p q hpq => dampDatum_mul_coprime hbmul P Q x hpq)
    (fun n => norm_dampDatum_le_one hble P Q hx0 hx1 n) ?_ ?_ hk₀th hMX hgate hcap hR0 hRle
    hRmax
  · intro n hn
    have hlt : (n : ℝ) < ramRbot H Xn j := by
      have : (n : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hn
      linarith
    rw [ramRdampCoeff, if_neg (notMem_ramRrange_of_lt hlt)]
  · intro n hn1 hn2
    have hmem : n ∈ ramRrange H N Xn j := by
      have hnk : (k₀ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn1
      have hnM : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn2
      rw [ramRrange, Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, le_trans hn2 hMN⟩, ?_, ?_⟩
      · have : ramRbot H Xn j ≤ (n : ℝ) := by linarith
        rwa [ramRbot] at this
      · have : (n : ℝ) ≤ 2 * ramRbot H Xn j := le_trans hnM hMtop2
        rw [ramRbot] at this
        linarith
    rw [ramRdampCoeff_damp, if_pos hmem]

/-- **THE CO-FACTOR `Rbd` AT THE GENERAL DATUM** (`cofactor_Rbd34_local_nocap3_gen`).
`CapFreeArm3.cofactor_Rbd34_local_nocap3`'s body at a general `1`-bounded, coprime-multiplicative
`b` with `b 1 = 1`: the `by_cases` on the damping runs through `box_gate_le_3X_gen`, CASE A is
the carried `CaseASocketGen` at the free exit `S`, CASE B is §4's transfer adapter, and the
collision is the general pocket socket.

⟦THE SOCKET CUT⟧ this is the SECOND inhabitant of `CofactorSocket`'s pointwise fact — the
first being `cofactorSocket_of_ellLin`.  Neither is more general than the other: `ellLin g`
is not coprime-multiplicative-with-`f 1 = 1` in the same slot the Route-III face needs, and a
general `b` is not `ellLin`-shaped. -/
theorem cofactor_Rbd34_local_nocap3_gen {b : ℕ → ℂ} (hb1 : b 1 = 1)
    (hbmul : ∀ m n : ℕ, Nat.Coprime m n → b (m * n) = b m * b n) (hble : ∀ n : ℕ, ‖b n‖ ≤ 1)
    (H : ℝ) (N Xn P Q j M k₀ : ℕ) (X θ t t₁ R S : ℝ) (hS0 : 0 ≤ S)
    (hk₀th : ballQuarterThreshold ≤ (k₀ : ℝ))
    (hMN : M ≤ N) (hk₀lo : (k₀ : ℝ) < ramRbot H Xn j)
    (hk₀hi : ramRbot H Xn j ≤ (k₀ : ℝ) + 1) (hbot : 1 < ramRbot H Xn j)
    (hlow : ramRbot H Xn j - 1 ≤ (M : ℝ)) (hhigh : (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1))
    (hMtop : 2 * ramRbot H Xn j < (M : ℝ) + 3) (hMX : (M : ℝ) ≤ X)
    (hTM : |t| + Tstar2 (M : ℝ) (Real.log (M : ℝ)) ≤ 3 * X)
    (hgate32 : 18 + Real.log (Real.log X) - Real.log (Real.log (k₀ : ℝ))
      ≤ 32 * θ * Real.log (Real.log X))
    (hR0 : 0 < R) (hfar : R ≤ |t - t₁|)
    (hsock : PocketSocket3Gen b P Q X θ t₁)
    (hA2 : CaseASocketGen b P Q X θ k₀ M t S)
    (hend : 2 / ramRbot H Xn j
      ≤ cofactorRbdGen S (k₀ : ℝ) (M : ℝ) (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R / 3) :
    ‖ramR H N Xn P Q j b t‖
      ≤ cofactorRbdGen S (k₀ : ℝ) (M : ℝ) (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R := by
  have hbp : ∀ p : ℕ, p.Prime → ‖b p‖ ≤ 1 := fun p _ => hble p
  have hk₀3R : (3 : ℝ) ≤ (k₀ : ℝ) := le_trans three_le_ballQuarterThreshold hk₀th
  have hk₀1 : (1 : ℝ) ≤ (k₀ : ℝ) := by linarith
  have hk₀pin : pin2Gate ≤ (k₀ : ℝ) := le_trans pin2Gate_le_ballQuarterThreshold hk₀th
  set Sm : ℝ := max (2 * S) (farSupS34 (k₀ : ℝ) (M : ℝ)
    (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R) with hSm
  have hSA : 2 * S ≤ Sm := le_max_left _ _
  have hSB : farSupS34 (k₀ : ℝ) (M : ℝ) (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R ≤ Sm :=
    le_max_right _ _
  have hRbdS : cofactorRbdGen S (k₀ : ℝ) (M : ℝ)
      (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R = 3 * Sm := rfl
  have hendS : 2 / ramRbot H Xn j ≤ Sm := by
    rw [hRbdS] at hend; linarith
  rw [hRbdS]
  refine ramR_abel_sup hble hbot hlow hhigh hMtop hendS ?_
  intro m hm
  refine spolyA_ramRcoeff_le_of_damp ?_
  intro x hx
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rcases box_gate_le_3X_gen hbp P Q hx.1 hx.2 hk₀pin hMX hTM with hA | hB
  · have hk₀M : k₀ ≤ M := by
      have hk₀MR : (k₀ : ℝ) ≤ (M : ℝ) := by linarith
      exact_mod_cast hk₀MR
    have hbd := caseA_damped_partial_gen (b := b) (H := H) (N := N) (Xn := Xn) (P := P)
      (Q := Q) (j := j) (M := M) (k₀ := k₀) (x := x) (t := t) hS0 hMN hk₀M hk₀lo hk₀hi hhigh
      (hA2 x hx.1 hx.2 hA) m hm
    have hmul : 2 * S * (m : ℝ) ≤ Sm * (m : ℝ) := mul_le_mul_of_nonneg_right hSA hm0
    linarith
  · obtain ⟨t₁', hRmax, ht₁'abs, hpock⟩ := hB
    have hcoll := hsock x hx.1 hx.2 t₁' ht₁'abs hpock
    have hRle : R ≤ 1 + |t - t₁'| := by
      have := pocket_far_from_ball hcoll hfar
      linarith
    have hbd := damped_partial_transfer_34_gen hb1 hbmul hble hx.1 hx.2 hk₀th hMN hk₀lo hk₀hi
      hhigh hMX hgate32 hpock hR0 hRle hRmax m hm
    have hmul : farSupS34 (k₀ : ℝ) (M : ℝ) (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R * (m : ℝ)
        ≤ Sm * (m : ℝ) := mul_le_mul_of_nonneg_right hSB hm0
    linarith

/-- **THE GENERAL DATUM'S SOCKET** (`cofactorSocket_of_gen`).
`CapFreeArm3.cofactorSocket_of_ellLin`
at the general datum: §5 quantified over the block index set, with the window geometry read
off `USetGradedPrice.TLBlockGates34` (its `cofactorRbd34loc` endpoint charge is replaced by
the generic `hendGen`, since the CASE-A constant is free here).

⟦THE SOCKET CUT⟧ this is the supplier the door needs: `CofactorSocket` is exactly the fact
the whole `𝒰`/err leg reads, and nothing above §5 ever sees `b` again. -/
theorem cofactorSocket_of_gen {b : ℕ → ℂ} (hb1 : b 1 = 1)
    (hbmul : ∀ m n : ℕ, Nat.Coprime m n → b (m * n) = b m * b n) (hble : ∀ n : ℕ, ‖b n‖ ≤ 1)
    {H : ℝ} {N Xd P Q : ℕ} {Mt kk : ℕ → ℕ}
    {cq L cg Cb X θ Rrad Tann t₁ Rbar S : ℝ} (hS0 : 0 ≤ S) (hR0 : 0 < Rrad)
    (hsock : PocketSocket3Gen b P Q X θ t₁)
    (hblk : ∀ j ∈ ramI H P Q, TLBlockGates34 cq H P N Xd Mt kk Tann L cg Cb X θ Rrad j)
    (hbox : ∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
      |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X)
    (hA2 : ∀ j ∈ ramI H P Q, ∀ t : ℝ, CaseASocketGen b P Q X θ (kk j) (Mt j) t S)
    (hendGen : ∀ j ∈ ramI H P Q, 2 / ramRbot H Xd j
      ≤ cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
          (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad / 3)
    (hRbdU : ∀ j ∈ ramI H P Q,
      cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
          (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ≤ Rbar) :
    CofactorSocket H N Xd P Q Tann Rrad t₁ Rbar b := by
  intro j hj t ht hfar
  obtain ⟨-, -, -, -, -, -, hk₀th, hMN, hk₀lo, hk₀hi, hbot, hlow, hhigh, hMtop, hMX,
    hgate32, -⟩ := hblk j hj
  exact le_trans
    (cofactor_Rbd34_local_nocap3_gen hb1 hbmul hble H N Xd P Q j (Mt j) (kk j) X θ t t₁ Rrad S
      hS0 hk₀th hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hMX (hbox j hj t ht) hgate32 hR0 hfar
      hsock (hA2 j hj t) (hendGen j hj))
    (hRbdU j hj)

/-! ## §6 — THE DOOR'S SOCKET

The three suppliers, composed: §3's masked floor kills every pocket at every piece (§4′),
§5 turns the per-piece CASE-A socket into the per-piece `CofactorSocket`, and §1's
inclusion–exclusion adds the `2^J` of them.  The CASE-A socket itself is the ONE page this
file does not own — it is the Route-III dissection at the `y₂` pin (the residue design's
supplier wave, item 3), stated here as `CaseASocketGen` exactly as `USetGradedPrice` states
`CaseASocket2` (law #253). -/

/-- **THE SOCKET AT THE DOOR'S UN-PHASED CO-FACTOR DATUM** (`cofactorSocket_door`).

For every character in the door's modulus range, every sieve depth `J`, and the block pin
`P`: if each inclusion–exclusion piece `λχ̄·g_𝒥` carries the CASE-A socket at a common exit
constant `S` and the block ladder's gates hold, then the door's own co-factor datum
`1_𝒮(P·m)·λ(m)χ̄(m)` carries `CofactorSocket` at `2^J·R̄₀`.

The floor side is DISCHARGED, not assumed: `capFreeFloor3_pieceDatum` supplies
`CapFreeFloor3` at every piece from the χ-floor's own margin, and `pocketSocket3Gen_of_floor3`
turns it into the collision socket vacuously. -/
theorem cofactorSocket_door {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    {H : ℝ} {N Xd P Q J : ℕ} {Mt kk : ℕ → ℕ}
    {cq L cg Cb X θ Rrad Tann t₁ Rbar0 S : ℝ}
    (hP1 : 1 ≤ P) (hS0 : 0 ≤ S) (hR0 : 0 < Rrad)
    (hθ0 : 0 < θ) (hθ32 : θ ≤ 1 / 32) (hLX : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X θ ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q)
    (hfloor : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset, CapFreeFloor3 (pieceDatum χ 𝒥 Pseq Qseq) X)
    (hblk : ∀ j ∈ ramI H P Q, TLBlockGates34 cq H P N Xd Mt kk Tann L cg Cb X θ Rrad j)
    (hbox : ∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
      |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X)
    (hA2 : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset, ∀ j ∈ ramI H P Q, ∀ t : ℝ,
      CaseASocketGen (pieceDatum χ 𝒥 Pseq Qseq) P Q X θ (kk j) (Mt j) t S)
    (hendGen : ∀ j ∈ ramI H P Q, 2 / ramRbot H Xd j
      ≤ cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
          (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad / 3)
    (hRbdU : ∀ j ∈ ramI H P Q,
      cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
          (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ≤ Rbar0) :
    CofactorSocket H N Xd P Q Tann Rrad t₁ (2 ^ J * Rbar0)
      (doorCofactor0 χ Pseq Qseq J P) := by
  refine cofactorSocket_door_of_pieces χ Pseq Qseq hP1 (fun 𝒥 h𝒥 => ?_)
  have hble : ∀ n : ℕ, ‖pieceDatum χ 𝒥 Pseq Qseq n‖ ≤ 1 :=
    norm_pieceDatum_le_one χ 𝒥 Pseq Qseq
  exact cofactorSocket_of_gen (pieceDatum_one χ 𝒥 Pseq Qseq)
    (fun m n _ => pieceDatum_mul χ 𝒥 Pseq Qseq m n) hble hS0 hR0
    (pocketSocket3Gen_of_floor3 (fun p _ => hble p) hθ0 hθ32 hLX hPlow hQhigh hPQ
      (hfloor 𝒥 h𝒥) t₁)
    hblk hbox (hA2 𝒥 h𝒥) hendGen hRbdU

/-! ## §7 — THE DOOR'S MASK DEBIT IS `X`-FREE

⟦THE FLOOR-PAGE CHECK⟧ the residue design asks whether the door's blocks `[𝒫_j, 𝒬K_j]` are
§8.3-graded, i.e. `P83 X θ ≤ 𝒫_j` and `𝒬K_j ≤ Q83 X`, so that §3's mask debit could be
priced by `CofactorDist.blockWindow_mertens_pin` at `θ·loglog X + 25`.

**The verdict is better than the design's, and does not need the grading at all.**  The
lower endpoint `𝒫_j = 2^{e_j}` is `X`-FREE, so `P83 X θ ≤ 𝒫_j` FAILS for large `X` — but the
block's Mertens mass never needed the pin: the ladder's own ratio is
`log 𝒬K_j / log 𝒫_j = j²M` (`SeamCalibrationK.log_calP_div_log_calQK`), so
`CofactorDist.blockWindow_mertens_const` prices the whole window at

  `Σ_{𝒫_j ≤ p ≤ 𝒬K_j, p ≤ X} 1/p ≤ log(j²M) + 25`,

an `X`-free constant.  So the masked floor's threshold stays a THRESHOLD on `loglog X` with
an `X`-free debit — the same regime-absorbable shape as the χ-floor's own `K`. -/

/-- **THE DOOR BLOCK'S MERTENS MASS** (`blockWindow_calibrated_debit`).  `X`-free: the
calibrated ladder's log-ratio is exactly `j²M`. -/
theorem blockWindow_calibrated_debit (A G M j : ℕ) (X : ℝ)
    (hM : 1 ≤ M) (hj : 1 ≤ j) (hE : 2 ≤ calE A G j) :
    ∑ p ∈ blockWindowPrimes (calP A G j) (calQK A G M j) X, (1 : ℝ) / (p : ℝ)
      ≤ Real.log ((j : ℝ) ^ 2 * (M : ℝ)) + 25 := by
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hK1 : (1 : ℝ) ≤ (j : ℝ) ^ 2 * (M : ℝ) := by nlinarith
  have hER : (2 : ℝ) ≤ ((calE A G j : ℕ) : ℝ) := by exact_mod_cast hE
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the lower endpoint clears `e`
  have hP4nat : 4 ≤ calP A G j := by
    have h : (2 : ℕ) ^ 2 ≤ 2 ^ calE A G j := Nat.pow_le_pow_right (by norm_num) hE
    simpa [calP] using h
  have hP4 : (4 : ℝ) ≤ ((calP A G j : ℕ) : ℝ) := by exact_mod_cast hP4nat
  have hPe : Real.exp 1 ≤ ((calP A G j : ℕ) : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  -- the ladder is ordered
  have hPQ : calP A G j ≤ calQK A G M j := by
    have hpos : 0 < j ^ 2 * M := by positivity
    have hle : calE A G j ≤ (j ^ 2 * M) * calE A G j := Nat.le_mul_of_pos_left _ hpos
    have h : (2 : ℕ) ^ calE A G j ≤ 2 ^ ((j ^ 2 * M) * calE A G j) :=
      Nat.pow_le_pow_right (by norm_num) hle
    simpa [calP, calQK] using h
  -- the two endpoint logs, and their loglog difference
  have hlP : Real.log ((calP A G j : ℕ) : ℝ) = ((calE A G j : ℕ) : ℝ) * Real.log 2 :=
    log_calP A G j
  have hlQ : Real.log ((calQK A G M j : ℕ) : ℝ)
      = ((j : ℝ) ^ 2 * (M : ℝ)) * ((calE A G j : ℕ) : ℝ) * Real.log 2 := log_calQK A G M j
  have hc0 : (0 : ℝ) < ((calE A G j : ℕ) : ℝ) * Real.log 2 := by nlinarith
  have hK0 : (0 : ℝ) < (j : ℝ) ^ 2 * (M : ℝ) := by nlinarith
  have hdiff : Real.log (Real.log ((calQK A G M j : ℕ) : ℝ))
      - Real.log (Real.log ((calP A G j : ℕ) : ℝ)) = Real.log ((j : ℝ) ^ 2 * (M : ℝ)) := by
    rw [hlP, hlQ, show ((j : ℝ) ^ 2 * (M : ℝ)) * ((calE A G j : ℕ) : ℝ) * Real.log 2
        = ((j : ℝ) ^ 2 * (M : ℝ)) * (((calE A G j : ℕ) : ℝ) * Real.log 2) from by ring,
      Real.log_mul (ne_of_gt hK0) (ne_of_gt hc0)]
    ring
  have hmert := blockWindow_mertens_const (calP A G j) (calQK A G M j) X hPe hPQ
  linarith

/-- **THE DOOR'S TOTAL MASK DEBIT** (`blockWindow_calibrated_debit_sum`), over any sub-family
`𝒥 ⊆ [1,J]` of the door's blocks: `X`-free, and monotone in the sieve depth. -/
theorem blockWindow_calibrated_debit_sum (A G M J : ℕ) {𝒥 : Finset ℕ} (X : ℝ)
    (h𝒥 : 𝒥 ⊆ Finset.Icc 1 J) (hM : 1 ≤ M) (hE : ∀ j, 2 ≤ calE A G j) :
    ∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP A G j) (calQK A G M j) X, (1 : ℝ) / (p : ℝ)
      ≤ (J : ℝ) * (Real.log ((J : ℝ) ^ 2 * (M : ℝ)) + 25) := by
  classical
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ1
  · -- the empty ladder: `𝒥 ⊆ Icc 1 0 = ∅`
    subst hJ0
    have hemp : 𝒥 = ∅ := Finset.subset_empty.mp (by simpa using h𝒥)
    rw [hemp]
    simp
  · have hJ1R : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ1
    have hKJ : (1 : ℝ) ≤ (J : ℝ) ^ 2 * (M : ℝ) := by nlinarith
    have hB0 : (0 : ℝ) ≤ Real.log ((J : ℝ) ^ 2 * (M : ℝ)) + 25 := by
      have := Real.log_nonneg hKJ
      linarith
    have hbound : ∀ j ∈ 𝒥,
        (∑ p ∈ blockWindowPrimes (calP A G j) (calQK A G M j) X, (1 : ℝ) / (p : ℝ))
          ≤ Real.log ((J : ℝ) ^ 2 * (M : ℝ)) + 25 := by
      intro j hjmem
      obtain ⟨hj1, hjJ⟩ := Finset.mem_Icc.mp (h𝒥 hjmem)
      have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      have hjJR : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hjJ
      have hsq : (j : ℝ) ^ 2 ≤ (J : ℝ) ^ 2 := by nlinarith
      have hmono : Real.log ((j : ℝ) ^ 2 * (M : ℝ)) ≤ Real.log ((J : ℝ) ^ 2 * (M : ℝ)) := by
        refine Real.log_le_log (by nlinarith) ?_
        exact mul_le_mul_of_nonneg_right hsq (by linarith)
      have h := blockWindow_calibrated_debit A G M j X hM hj1 (hE j)
      linarith
    have hcard : (𝒥.card : ℝ) ≤ (J : ℝ) := by
      have h1 : 𝒥.card ≤ (Finset.Icc 1 J).card := Finset.card_le_card h𝒥
      have h2 : (Finset.Icc 1 J).card = J := by rw [Nat.card_Icc]; omega
      have h3 : 𝒥.card ≤ J := by omega
      exact_mod_cast h3
    calc ∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP A G j) (calQK A G M j) X, (1 : ℝ) / (p : ℝ)
        ≤ 𝒥.card • (Real.log ((J : ℝ) ^ 2 * (M : ℝ)) + 25) :=
          Finset.sum_le_card_nsmul _ _ _ hbound
      _ = (𝒥.card : ℝ) * (Real.log ((J : ℝ) ^ 2 * (M : ℝ)) + 25) := by rw [nsmul_eq_mul]
      _ ≤ (J : ℝ) * (Real.log ((J : ℝ) ^ 2 * (M : ℝ)) + 25) :=
          mul_le_mul_of_nonneg_right hcard hB0

/-! ## §8 — THE ROUTE-III BRIDGE: THE CASE-A SOCKET FROM THE DILATED INNER SUMS

The one page this file does not own is the CASE-A supply at the general datum.  §8 reduces it
to its ONLY residue: the landed `ellLin` supply, read at the DILATED scales `⌊k/d⌋`.

`SPartStation.hCenter_dissected` is Route III at a general `1`-bounded multiplicative `F`:

  `‖∑_{n≤k} F(n)·n^{−it}‖ ≤ (cSq·S + cSq·D^{−1/4})·k`
  whenever `‖∑_{m≤⌊k/d⌋} ℓ(F)(m)·m^{−it}‖ ≤ S·⌊k/d⌋` for every `d ≤ D`,

with `cSq = 20736` EXPLICIT.  The damped general datum `b·x^{ω}` meets its binder — coprime
multiplicativity is `RamWeight.blockOmega_pow_mul_coprime` — and its linearisation is the
LANDED slot `ellLin (g_x)`, because `ellLin` reads its datum at primes only.  So what is left
is exactly the `y₂`-pin CASE-A supply at a WIDE scale window (the dissection walks `[k/D, k]`,
not a dyadic window), which is `CaseASocket.caseA_partial_supply2`'s clone at
`SPartStation.center_halasz_supply_wide`'s window — item 3 of the supplier wave.

⚠ THE TRAP (design v4): the damped datum is multiplicative on COPRIMES only, never completely
multiplicative (`x^{ω(p^k)} = x ≠ x^k`), so the cheap completely-multiplicative constant does
NOT apply — the FULL `cSq` is paid.  That is what the pricing page prices. -/

/-- The damped general datum is multiplicative in mathlib's sense (the binder
`SPartStation.hCenter_dissected` reads). -/
theorem dampDatum_isMultiplicative {b : ℕ → ℂ} (hb1 : b 1 = 1)
    (hbmul : ∀ m n : ℕ, Nat.Coprime m n → b (m * n) = b m * b n) (P Q : ℕ) (x : ℝ) :
    (toArithmeticFunction (dampDatum b P Q x)).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [toAF_apply, dampDatum_one hb1], fun {m n} hm hn hco => ?_⟩
  simp only [toAF_apply, if_neg (Nat.mul_ne_zero hm hn), if_neg hm, if_neg hn]
  exact dampDatum_mul_coprime hbmul P Q x hco

/-- The damped datum's linearisation IS the landed `ellLin (g_x)` slot. -/
theorem ellLin_dampDatum (b : ℕ → ℂ) (P Q : ℕ) (x : ℝ) :
    ellLin (dampDatum b P Q x) = ellLin (gxDatum b P Q x) :=
  ellLin_congr_primes (fun _p hp => dampDatum_prime hp)

/-- **THE DISSECTION AT THE DAMPED GENERAL DATUM** (`caseA_dissect_gen`).
`SPartStation.hCenter_dissected` at `F := b·x^{ω}`, `t₀ = 0`: the damped datum's twisted
partial sums are controlled by the LANDED `ellLin (g_x)` sums at the dilated scales, at the
price `cSq·S + cSq·D^{−1/4}`. -/
theorem caseA_dissect_gen {b : ℕ → ℂ} (hb1 : b 1 = 1)
    (hbmul : ∀ m n : ℕ, Nat.Coprime m n → b (m * n) = b m * b n) (hble : ∀ n : ℕ, ‖b n‖ ≤ 1)
    (P Q : ℕ) {x t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {D k : ℕ} (hD : 1 ≤ D) (hDk : D ≤ k)
    {S : ℝ} (hS : 0 ≤ S)
    (hInner : ∀ d : ℕ, 1 ≤ d → d ≤ D →
      ‖∑ m ∈ Finset.Icc 1 (k / d), ellLin (gxDatum b P Q x) m * eIu (-t) m‖
        ≤ S * ((k / d : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.Icc 1 k, dampDatum b P Q x n * eIu (-t) n‖
      ≤ (cSq * S + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) * (k : ℝ) := by
  have hFm := dampDatum_isMultiplicative hb1 hbmul P Q x
  have hFb : ∀ n : ℕ, ‖dampDatum b P Q x n‖ ≤ 1 := norm_dampDatum_le_one hble P Q hx0 hx1
  have h := hCenter_dissected (F := dampDatum b P Q x) hFm hFb 0 t hD hDk hS ?_
  · rwa [sum_seamCoeff_zero_center] at h
  · intro d hd1 hd2
    rw [sum_seamCoeff_zero_center, ellLin_dampDatum]
    exact hInner d hd1 hd2

/-- **THE CASE-A SOCKET FROM THE DILATED SUPPLY** (`caseASocketGen_of_inner`).  The reduction
the supplier wave leaves open, in one statement: a common grade `S` for the LANDED `ellLin`
partial sums at every dilated scale `⌊k/d⌋`, `d ≤ D`, `k ∈ [k₀, M]`, gives the general datum's
CASE-A socket at `cSq·S + cSq·D^{−1/4}`.

The floor hypothesis rides through untouched — it is the CASE-A supply's own input, and at the
general datum it is stated in the damped slot, where `pretDistSq_dampDatum_eq` identifies it
with the landed `ellLin (g_x)` slot.  So the residue is EXACTLY the `y₂`-pin CASE-A supply on
a wide scale window. -/
theorem caseASocketGen_of_inner {b : ℕ → ℂ} (hb1 : b 1 = 1)
    (hbmul : ∀ m n : ℕ, Nat.Coprime m n → b (m * n) = b m * b n) (hble : ∀ n : ℕ, ‖b n‖ ≤ 1)
    (P Q : ℕ) (X θ : ℝ) (k₀ M D : ℕ) (t S : ℝ) (hD : 1 ≤ D) (hDk₀ : D ≤ k₀) (hS0 : 0 ≤ S)
    (hInner : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      (∀ k : ℕ, k₀ ≤ k → k ≤ M → ∀ v : ℝ, |v - t| ≤ Tstar2 (k : ℝ) (Real.log (k : ℝ)) →
        cofactorMfl X θ (k₀ : ℝ)
          ≤ pretDistSq (ellLin (gxDatum b P Q x)) (costwist v) (k : ℝ)) →
      ∀ k : ℕ, k₀ ≤ k → k ≤ M → ∀ d : ℕ, 1 ≤ d → d ≤ D →
        ‖∑ m ∈ Finset.Icc 1 (k / d), ellLin (gxDatum b P Q x) m * eIu (-t) m‖
          ≤ S * ((k / d : ℕ) : ℝ)) :
    CaseASocketGen b P Q X θ k₀ M t (cSq * S + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) := by
  intro x hx0 hx1 hfloor k hk1 hk2
  have hfloor' : ∀ k : ℕ, k₀ ≤ k → k ≤ M → ∀ v : ℝ,
      |v - t| ≤ Tstar2 (k : ℝ) (Real.log (k : ℝ)) →
      cofactorMfl X θ (k₀ : ℝ)
        ≤ pretDistSq (ellLin (gxDatum b P Q x)) (costwist v) (k : ℝ) := by
    intro k' h1 h2 v hv
    have h := hfloor k' h1 h2 v hv
    rwa [pretDistSq_dampDatum_eq] at h
  exact caseA_dissect_gen hb1 hbmul hble P Q hx0 hx1 hD (le_trans hDk₀ hk1) hS0
    (hInner x hx0 hx1 hfloor' k hk1 hk2)

/-- **THE FLOOR AT EVERY DILATED SCALE** (`caseA_floor_of_capFreeFloor3`).  Under the cap-free
floor there is NO pocket anywhere on the `3X` box, so the CASE-A window floor holds at EVERY
scale `k` below `X` — including the DILATED scales `⌊k/d⌋` that Route III's dissection walks,
which sit BELOW the co-factor window's own bottom `k₀`.

The value is read at the bottom scale `kbot` of whatever range the consumer walks: the
descent price `2·(S(X) − S(kbot))` is exactly what `CofactorSupply.cofactorMfl` carries, and
`S` is monotone, so a floor stated at `kbot` serves every `k ≥ kbot`.

This is the stone that lets §8's `hInner` be supplied on a WIDE scale window: without it the
dilated scales would have no floor at all. -/
theorem caseA_floor_of_capFreeFloor3 {b : ℕ → ℂ} (hb : ∀ p : ℕ, p.Prime → ‖b p‖ ≤ 1)
    (P Q : ℕ) {X θ x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hθ0 : 0 < θ) (hθ32 : θ ≤ 1 / 32) (hLX : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X θ ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q)
    (hfloor : CapFreeFloor3 b X) {kbot k : ℕ} (hkb : kbot ≤ k) (hkX : (k : ℝ) ≤ X)
    {v : ℝ} (hv : |v| ≤ 3 * X) :
    cofactorMfl X θ (kbot : ℝ) ≤ pretDistSq (dampDatum b P Q x) (costwist v) (k : ℝ) := by
  have hgx : ∀ p : ℕ, p.Prime → ‖gxDatum b P Q x p‖ ≤ 1 :=
    fun p hp => gxDatum_norm_le_one hx0 hx1 hb p hp
  have hEll : ∀ n : ℕ, ‖ellLin (gxDatum b P Q x) n‖ ≤ 1 := ellLin_norm_le_one _ hgx
  have hcw : ∀ n : ℕ, ‖costwist v n‖ ≤ 1 := fun n => le_of_eq (costwist_norm v n)
  have hnp := no_pocket_of_floor3 hb P Q hx0 hx1 hθ0 hθ32 hLX hPlow hQhigh hPQ hfloor hv
  have hXbig : (1 / 32 - θ) * Real.log (Real.log X)
      < pretDistSq (ellLin (gxDatum b P Q x)) (costwist v) X := not_le.mp hnp
  have hkfl : ⌊((k : ℕ) : ℝ)⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono hkX
  have htail := pretDistSq_tail_le (f := ellLin (gxDatum b P Q x)) (g := costwist v) hEll hcw
    hkfl
  have hSk : Salt.Mertens.SPartial ((kbot : ℕ) : ℝ) ≤ Salt.Mertens.SPartial ((k : ℕ) : ℝ) := by
    refine SPartial_mono_floor ?_
    rw [Nat.floor_natCast, Nat.floor_natCast]
    exact hkb
  rw [pretDistSq_dampDatum_eq]
  unfold cofactorMfl
  linarith

end Salt.MR
