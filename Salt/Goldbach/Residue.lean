/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# Goldbach residues — the CRT selection witness and the `Q·d` fused class (D2.2)

The Goldbach mirror of the twin residue layer.  Where the twin problem takes the trivial
witness `a = Q − 1` (`Salt/Chen/Assembly.lean`'s `residue_witness`/`residue_witness'`), the
even-`N` Goldbach split `N = p + q` needs a genuine CRT selection: a residue `a` mod the
fixed modulus `Q` with BOTH `a` and `N − a` reduced (so `n ≡ a (mod Q)` makes `n` and
`N − n` coprime to `Q`).  This file supplies:

* `exists_crt_finset` — a Finset CRT combiner over pairwise-coprime positive moduli.
* `goldbach_residue_witness` — D2.2's frozen shape: `∃ a < Q, Coprime Q a ∧
  Coprime Q (N − a) ∧ ∀ q ∈ Q.primeFactors, a % q ≠ 0 ∧ a % q ≠ N % q`.  The
  `Coprime Q (N − a)` conjunct is the Goldbach `hQa2` slot of `chen_of_hypotheses_W`
  (`Salt/Chen/Assembly.lean:720`), consumed through `crtClassG`.
* `crtClassG` + `crtClassG_coprime` — the Goldbach mirror of `crtClassW`
  (`Salt/Chen/SwitchW.lean:416`): the unique class mod `Q·d` fusing `N − a (mod Q)` with
  `N (mod d)` (the switch congruence `d ∣ n` gives `N − n ≡ N (mod d)`), reduced from
  `Coprime Q (N − a)` and `Coprime d N`.
* `crt_class_coprimeG` — the hypotheses-parametrized coprimality of a fused class, the
  Goldbach mirror of `crt_class_coprime` (`Salt/Chen/TwinA1W.lean:208`) as consumed by the
  `rosserRemainderW_le_split` residue routing.

Class B.  No `sorry`, no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset

/-! ## Part A — the Finset CRT combiner -/

/-- **Finset CRT.**  For a finite family of pairwise-coprime positive moduli `S` and any
residue prescription `r`, there is a common solution `a` with `a % q = r q % q` at every
`q ∈ S`.  Built by `Finset.induction` off the pairwise combiner `Nat.chineseRemainder`. -/
theorem exists_crt_finset (r : ℕ → ℕ) :
    ∀ S : Finset ℕ, (∀ q ∈ S, 0 < q) →
      (∀ q ∈ S, ∀ q' ∈ S, q ≠ q' → Nat.Coprime q q') →
      ∃ a : ℕ, ∀ q ∈ S, a % q = r q % q := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ _; exact ⟨0, by simp⟩
  | @insert q₀ S' hq₀ ih =>
    intro hpos hcop
    have hposS' : ∀ q ∈ S', 0 < q := fun q hq => hpos q (mem_insert_of_mem hq)
    have hcopS' : ∀ q ∈ S', ∀ q' ∈ S', q ≠ q' → Nat.Coprime q q' :=
      fun q hq q' hq' hne =>
        hcop q (mem_insert_of_mem hq) q' (mem_insert_of_mem hq') hne
    obtain ⟨a', ha'⟩ := ih hposS' hcopS'
    have hcop0 : Nat.Coprime q₀ (∏ q ∈ S', q) := by
      refine Nat.Coprime.prod_right ?_
      intro q hq
      exact hcop q₀ (mem_insert_self _ _) q (mem_insert_of_mem hq) (fun h => hq₀ (h ▸ hq))
    obtain ⟨a, hak0, hakP⟩ := Nat.chineseRemainder hcop0 (r q₀) a'
    refine ⟨a, ?_⟩
    intro q hq
    rcases mem_insert.mp hq with rfl | hq'
    · exact hak0
    · have hdvd : q ∣ ∏ q ∈ S', q := Finset.dvd_prod_of_mem _ hq'
      have hmod : a % q = a' % q := hakP.of_dvd hdvd
      rw [hmod]; exact ha' q hq'

/-! ## Part B — D2.2, the Goldbach residue witness -/

/-- **D2.2 — the Goldbach residue witness.**  For squarefree `Q` (the fixed `opQ` primorial;
`Q.primeFactors` are exactly its prime divisors), even `N`, and `Q ≤ N`, there is a residue
`a < Q` with both `a` and `N − a` reduced mod `Q`, avoiding `{0, N % q}` at every prime
`q ∣ Q`.  Per-prime choice: pick `1` (misses `0`, and `N % q ≠ 1`), or `2` when `N % q = 1`
(then `q ≠ 2` since `N` is even, so `q ≥ 3` leaves `2 ∉ {0, 1}` free); combined by CRT.
The `Coprime Q (N − a)` conjunct is what the Goldbach `hQa2` slot consumes. -/
theorem goldbach_residue_witness {Q N : ℕ} (hQ : Squarefree Q) (hN : Even N)
    (hQN : Q ≤ N) :
    ∃ a < Q, Nat.Coprime Q a ∧ Nat.Coprime Q (N - a) ∧
      ∀ q ∈ Q.primeFactors, a % q ≠ 0 ∧ a % q ≠ N % q := by
  have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ.ne_zero
  obtain ⟨a₀, ha₀⟩ := exists_crt_finset (fun q => if N % q = 1 then 2 else 1)
    Q.primeFactors
    (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
    (fun q hq q' hq' hne =>
      (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hq)
        (Nat.prime_of_mem_primeFactors hq')).mpr hne)
  have avoid : ∀ q ∈ Q.primeFactors,
      (a₀ % Q) % q ≠ 0 ∧ (a₀ % Q) % q ≠ N % q := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hq2 : 2 ≤ q := hqp.two_le
    have hqdvd : q ∣ Q := Nat.dvd_of_mem_primeFactors hq
    have hkey : (a₀ % Q) % q = (if N % q = 1 then 2 else 1) % q := by
      rw [Nat.mod_mod_of_dvd a₀ hqdvd]; exact ha₀ q hq
    by_cases hN1 : N % q = 1
    · have hqne2 : q ≠ 2 := by
        intro h; subst h
        have : N % 2 = 0 := Nat.even_iff.mp hN
        omega
      have hq3 : 3 ≤ q := by omega
      have h2 : (2 : ℕ) % q = 2 := Nat.mod_eq_of_lt (by omega)
      rw [if_pos hN1, h2] at hkey
      exact ⟨by rw [hkey]; norm_num, by rw [hkey, hN1]; norm_num⟩
    · have h1 : (1 : ℕ) % q = 1 := Nat.mod_eq_of_lt (by omega)
      rw [if_neg hN1, h1] at hkey
      exact ⟨by rw [hkey]; norm_num, by rw [hkey]; exact fun h => hN1 h.symm⟩
  refine ⟨a₀ % Q, Nat.mod_lt a₀ hQpos, ?_, ?_, avoid⟩
  · by_contra h
    obtain ⟨p, hp, hpQ, hpa⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hpmem : p ∈ Q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpQ, hQ.ne_zero⟩
    exact (avoid p hpmem).1 (Nat.mod_eq_zero_of_dvd hpa)
  · by_contra h
    obtain ⟨p, hp, hpQ, hpNa⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hpmem : p ∈ Q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpQ, hQ.ne_zero⟩
    have haN : a₀ % Q ≤ N := le_trans (le_of_lt (Nat.mod_lt a₀ hQpos)) hQN
    have hcong : (a₀ % Q) % p = N % p := (Nat.modEq_iff_dvd' haN).mpr hpNa
    exact (avoid p hpmem).2 hcong

/-! ## Part C — `crtClassG`, the Goldbach mirror of `crtClassW` (the switch side) -/

open Classical in
/-- **The CRT residue of the Goldbach switch.**  The unique class mod `Q·d` combining
`N − a (mod Q)` (the AP-membership of `N − n`) and `N (mod d)` (the switch congruence `d ∣ n`
gives `N − n ≡ N`); `0` off the coprime case (never consumed there). -/
noncomputable def crtClassG (Q d N a : ℕ) : ℕ :=
  if h : Nat.Coprime Q d then (Nat.chineseRemainder h (N - a) N).1 else 0

lemma crtClassG_modEq_left {Q d : ℕ} (N a : ℕ) (h : Nat.Coprime Q d) :
    crtClassG Q d N a ≡ N - a [MOD Q] := by
  unfold crtClassG
  rw [dif_pos h]
  exact (Nat.chineseRemainder h (N - a) N).2.1

lemma crtClassG_modEq_right {Q d : ℕ} (N a : ℕ) (h : Nat.Coprime Q d) :
    crtClassG Q d N a ≡ N [MOD d] := by
  unfold crtClassG
  rw [dif_pos h]
  exact (Nat.chineseRemainder h (N - a) N).2.2

/-- **`gcd(crtClassG, Q·d) = 1`.**  From `gcd(Q, N − a) = 1` (the witness `Coprime Q (N − a)`)
and `gcd(d, N) = 1` (the switch unit `Coprime d N`, free on `goldPs` since `d ∤ N`): the class
is `≡ N − a` mod `Q` and `≡ N` mod `d`.  Mirrors `crtClassW_coprime`. -/
theorem crtClassG_coprime {Q d N a : ℕ} (hQd : Nat.Coprime Q d)
    (hQNa : Nat.Coprime Q (N - a)) (hdN : Nat.Coprime d N) :
    Nat.Coprime (crtClassG Q d N a) (Q * d) := by
  have hmodL : crtClassG Q d N a % Q = (N - a) % Q := crtClassG_modEq_left N a hQd
  have hmodR : crtClassG Q d N a % d = N % d := crtClassG_modEq_right N a hQd
  have hL : Nat.gcd Q (crtClassG Q d N a) = Nat.gcd Q (N - a) := by
    rw [Nat.gcd_rec Q (crtClassG Q d N a), Nat.gcd_rec Q (N - a), hmodL]
  have hR : Nat.gcd d (crtClassG Q d N a) = Nat.gcd d N := by
    rw [Nat.gcd_rec d (crtClassG Q d N a), Nat.gcd_rec d N, hmodR]
  refine Nat.Coprime.mul_right ?_ ?_
  · refine Nat.coprime_comm.mp ?_
    unfold Nat.Coprime at hQNa ⊢
    rw [hL]
    exact hQNa
  · refine Nat.coprime_comm.mp ?_
    unfold Nat.Coprime at hdN ⊢
    rw [hR]
    exact hdN

/-! ## Part D — the residue-side coprimality mirror (`rosserRemainderW_le_split` consumer) -/

/-- **`gcd(c, Q·d) = 1` for a fused Goldbach class — the `crt_class_coprime` mirror.**
Hypotheses-parametrized in a class `c` with `c ≡ a (mod Q)` and `c ≡ N (mod d)`: from
`gcd(Q, a) = 1` and `gcd(d, N) = 1` (the switch unit — free on `goldPs` where `d ∤ N`,
replacing the twin's `coprime_sub_two` `hd` disjunction).  This is the `hr` input the
Goldbach windowed remainder chain consumes at the shifted moduli. -/
theorem crt_class_coprimeG {Q a d c N : ℕ}
    (hQa : Nat.Coprime Q a) (hdN : Nat.Coprime d N)
    (hcQ : c % Q = a % Q) (hcd : c % d = N % d) :
    Nat.Coprime (Q * d) c := by
  have hQc : Nat.Coprime Q c := by
    have h : Nat.gcd c Q = Nat.gcd a Q := Nat.ModEq.gcd_eq (show c ≡ a [MOD Q] from hcQ)
    rw [Nat.Coprime, Nat.gcd_comm, h, Nat.gcd_comm]
    exact hQa
  have hdc : Nat.Coprime d c := by
    have h : Nat.gcd c d = Nat.gcd N d := Nat.ModEq.gcd_eq (show c ≡ N [MOD d] from hcd)
    rw [Nat.Coprime, Nat.gcd_comm, h, Nat.gcd_comm]
    exact hdN
  exact Nat.Coprime.mul_left hQc hdc

end Salt.Goldbach
