/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cMasterUncond
import Salt.HB.Lemma3Uncond
import Salt.HB.HSigmaComp

/-!
# N8, THE CHAIN HALF — HB 1983 §2's reduction `S⁽⁰⁾ → S⁽³⁾` on ONE window (design freeze v2)

**STATUS: EXECUTED.  The v2 design freeze (after the refuter pass) is DISCHARGED — all
seven theorems below are proved, sorry-free, with no statement changed and no new axiom
(each `#print axioms` shows exactly `[propext, Classical.choice, Quot.sound]`).**  This
file is one half of node N8 of the Heath-Brown engine
(`docs/sources/hb1983-notes.md` §1–§2, pp.197–198): the swap `S⁽⁰⁾ → S⁽¹⁾`, HB Lemma 4 on
the window with the pretense sum SYMBOLIC, and HB Lemma 3 at the pretense-sum level at the
repulsion floor.  The other half — the sieve wire at the window, HB Lemma 6, HB Lemma 5 as
an interface, and the p.200 assembly — is `Salt/HB/CrownAssembly.lean`; the two files share
no declaration and neither imports the other, so two executors can work them in parallel in
one checkout (one file each).  Each docstring carries the row's **class**, its **line cap**,
the **red-first idea**, and the **consumer** of the statement by Lean name.

Nothing here bears on twin primes: N8 assembles nothing on its own.  The dichotomy
`fulcrum_dichotomy` stays conditional on `hEngine` until N7 (Waves A/B/C), N8, N4's
composition wave, the `z` witness (seam S3), N9, N10 and N12 land.  N11 is closed
(`twinPrimeConjecture_of_frequently_S1`, `Salt/HB/DoorBridge.lean`, sorry-free).  The four
joins of PR #33 landed with it; one of them, `hb_lemma3_at_repulsion_floor`, is off the crown
path (see the ⛔ below).

## THE WINDOW DECISION (seam S1 of the crown census)

**ONE WINDOW: `l2cWindow χ z x`** `= {n ∈ (x, 2x] : (n(n+2), q·excPrimorial χ z) = 1}` —
HB's `(l, qP) = 1` at the minimal honest modulus, the window the unconditional master
`hb_l2c_master_unconditional` is already proved on.  The star step reaches it for free
(`S2_sub_S3_window` takes any sub-window with `excPrimorial`-coprimality, which
`l2cWindow_excPrimorial_coprime` supplies); the door (`twinWindow (2x+2) = Ioc x (2x)`,
`twinWindow_two_mul_add_two`) is reached by the swap `S1_Ioc_sub_S1_l2cWindow_le`; the
sieve reaches it through the wire `hbDataN8` (`CrownAssembly.lean`).  `honestWindow` is
SUPERSEDED for the crown path (it stays landed, untouched).

## THE TWO STATEMENT REPAIRS OF v2 (the refuter pass, 2026-09-03 18:1x)

* **The divisor-bound constant is bound BEFORE `z x`.**  v1's Lemma-4 rows concluded
  `∃ C, 0 < C ∧ …` inside the `z x` binders, so `C` could depend on `q, x` and N9 could not
  print an absolute `K₁`.  The uniformity exists in the corpus (`card_divisors_le_rpow`:
  `C` depends on `ε` alone) and the landed proof obtains `C` before touching `x` — only the
  STATEMENT threw it away.  v2 adds `S2_sub_S3_window_of_tau` (the star step with `C` a
  parameter and its defining hypothesis `hCtau`) and restates `S2_sub_S3_l2cWindow` and
  `hb_lemma4_l2cWindow` against it.  N9 calls `card_divisors_le_rpow` ONCE, outside every `x`.
* **Lemma 3 fires at `Lp := 2L`, on the `(L1)` join's packet.**  v1's
  `pretenseSum_at_repulsion_floor` inherited the N3 join's `hCR : 1600·log(80√f(1+log f))
  ≤ 800·L`, which is UNSATISFIABLE at `L = log q` (it says `6400·q·(1+log q)² ≤ q`); the
  corpus's own consumer fires the core at `Lp := 2L` (`two_mul_pretenseSum_le_at_window`,
  `Lemma7F.lean`).  v2 states the row on the zero-side packet of
  `hb_L1_one_sided_at_repulsion_floor` (`HSigmaComp.lean`) CHARACTER-FOR-CHARACTER — `hCR :
  log(80√f(1+log f)) ≤ L` (satisfiable at `L = log q` for `q ≥ 10^6`), `hSinvC` at `(2L)²`,
  `hlarge` at `B = b·log Q/L` — and fires the core at `Lp := 2L`.  So N9 hands ONE packet to
  both landed joins and to this row: the `L`-scale is `log q` everywhere, and the `η` of this
  file is the `η` of `CrownAssembly.lean` and of N9.

## WHAT N8 KEEPS SYMBOLIC (and why)

* `PretenseSum χ (2x+2)` stays a SYMBOL in the Lemma-4 error `lemma4Err` — N8's reduction is
  zero-free, exactly as HB's §2 is.  The zero enters only through
  `pretenseSum_at_repulsion_floor` (the join the crown chain actually consumes).
* `z` is free with the landed binders carried (`hz100 hz8 hzx` of the master); N9 discharges
  them at HB's `z = q^{1/z₀}`, `z₀ = A·log log η` (seam S3 is N9's, not N8's).

⛔ **A FINDING ABOUT THE LANDED N3 JOIN.**  `hb_lemma3_at_repulsion_floor`
(`Salt/HB/Lemma3Floor.lean`) joins Lemma 3 to the PARAMETRIC `hb_lemma2` shape: its antecedent
`hres : overshootMajorant χ A ≤ …` is the τ-crude majorant that the L2c campaign declared
"provably `L²`-inflated at the worst pattern and BYPASSED" (`Salt/HB/L2cCore.lean` header).  No
producer of `hres` at HB's grade exists or is planned, so that join has no consumer on the crown
path.  The join the path needs is one level down — the pretense sum itself at the floor —
and it is `pretenseSum_at_repulsion_floor` below.  The landed join stays; it is simply not on
the road.

## THE ROWS (executor order; class per the salt CLAUDE.md table)

§1 the window inclusion · §2 the swap · §3 the star step with a uniform constant, and
Lemma 4 on the window · §4 Lemma 3 at the pretense sum.
-/

open Finset
open Salt.SW

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 — the window inclusion (S1) -/

/-- **`l2cWindow ⊆ honestWindow`.**  Coprimality to `q·excPrimorial` implies coprimality to
`excPrimorial`.  Class **A**, cap 30.  Red-first: `intro n hn; exact Finset.mem_filter.mpr
⟨l2cWindow_subset χ z x hn, l2cWindow_excPrimorial_coprime χ z x n hn⟩` (both landed,
`L2cCore.lean`); or `Finset.monotone_filter_right` — NOT `filter_subset_filter`, which is
set-monotone at a fixed predicate and this is predicate-monotone at a fixed set.
Consumer: N9 (the set-level form). -/
theorem l2cWindow_subset_honestWindow (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    l2cWindow χ z x ⊆ honestWindow χ z x := by
  intro n hn
  unfold honestWindow
  exact Finset.mem_filter.mpr
    ⟨l2cWindow_subset χ z x hn, l2cWindow_excPrimorial_coprime χ z x n hn⟩

/-! ## §2 — the swap `S⁽⁰⁾ → S⁽¹⁾` (seam S6, HB p.197) -/

open ArithmeticFunction in
/-- **The cut only removes mass.**  `S1 (l2cWindow) ≤ S1 (Ioc x (2x))`: a sub-window of
nonnegative terms.  Class **A**, cap 20.  Red-first: `Finset.sum_le_sum_of_subset_of_nonneg`
with `l2cWindow_subset` and `vonMangoldt_nonneg`.  Consumer: `hb_lemma4_l2cWindow`. -/
theorem S1_l2cWindow_le_S1_Ioc (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    S1 (l2cWindow χ z x) ≤ S1 (Finset.Ioc x (2 * x)) := by
  unfold S1
  exact Finset.sum_le_sum_of_subset_of_nonneg (l2cWindow_subset χ z x)
    (fun n _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)

/-- Every prime dividing `q · excPrimorial χ z` lies in `ω(q) ∪ {primes < z}`. -/
private lemma chain_prime_mem_PS (χ : DirichletCharacter ℂ q) (hq : 0 < q) {z p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ q * excPrimorial χ z) :
    p ∈ q.primeFactors ∪ (Finset.range z).filter (fun r => Nat.Prime r) := by
  classical
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · exact Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp, h, by omega⟩)
  · rw [excPrimorial] at h
    obtain ⟨r, hr, hpr⟩ := (hp.prime).exists_mem_finset_dvd h
    have hrmem := Finset.mem_filter.mp hr
    have hrz : r < z := Finset.mem_range.mp hrmem.1
    have hrp : r.Prime := hrmem.2.1
    have : p = r := (Nat.prime_dvd_prime_iff_eq hp hrp).mp hpr
    subst this
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrz, hp⟩)

/-- Two prime powers divisible by the same prime `p` cannot both lie in a window
`(c, d]` with `d ≤ 2c + 1`. -/
private lemma chain_primepow_unique {p a b c d : ℕ} (hp : p.Prime)
    (ha : IsPrimePow a) (hb : IsPrimePow b) (hpa : p ∣ a) (hpb : p ∣ b)
    (hac : c < a) (had : a ≤ d) (hbc : c < b) (hbd : b ≤ d) (hcd : d ≤ 2 * c + 1) :
    a = b := by
  obtain ⟨p1, k, hp1, hk, hak⟩ := (isPrimePow_nat_iff a).mp ha
  obtain ⟨p2, l, hp2, hl, hbl⟩ := (isPrimePow_nat_iff b).mp hb
  have hpp1 : p = p1 := by
    have hd : p ∣ p1 ^ k := hak ▸ hpa
    exact (Nat.prime_dvd_prime_iff_eq hp hp1).mp (hp.dvd_of_dvd_pow hd)
  have hpp2 : p = p2 := by
    have hd : p ∣ p2 ^ l := hbl ▸ hpb
    exact (Nat.prime_dvd_prime_iff_eq hp hp2).mp (hp.dvd_of_dvd_pow hd)
  subst hpp1
  subst hpp2
  subst hak
  subst hbl
  -- the key: a strictly larger exponent doubles, and the window has ratio < 2
  have hkey : ∀ i j : ℕ, c < p ^ i → p ^ i ≤ d → c < p ^ j → p ^ j ≤ d → ¬ (i < j) := by
    intro i j hi1 _hi2 _hj1 hj2 hij
    have h1 : p ^ (i + 1) ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : p ^ i * 2 ≤ p ^ i * p := Nat.mul_le_mul_left _ hp.two_le
    have h3 : p ^ (i + 1) = p ^ i * p := by rw [pow_succ]
    have h4 : c + 1 ≤ p ^ i := hi1
    have h5 : (c + 1) * 2 ≤ p ^ i * 2 := Nat.mul_le_mul_right _ h4
    omega
  have hij : k = l := by
    rcases Nat.lt_trichotomy k l with h | h | h
    · exact absurd h (hkey k l hac had hbc hbd)
    · exact h
    · exact absurd h (hkey l k hbc hbd hac had)
  rw [hij]

open ArithmeticFunction in
/-- **HB p.197, `S⁽⁰⁾ = S⁽¹⁾ + O(L⁴z)`, sharpened.**  A term `Λ(n)Λ(n+2)` dropped by the
coprimality cut has some prime `p ∣ q·excPrimorial χ z` dividing `n` or `n+2`; both are prime
powers, so `n = p^e` or `n + 2 = p^e`, and a dyadic window holds at most ONE power of each
prime on each side.  Hence at most `2` dropped terms per prime, each `≤ L′²`, over at most
`ω(q) + #{p < z} ≤ ω(q) + z` primes.  Class **B**, cap 250.  Red-first: express the
difference as a sum over `(Ioc x (2x)) \ l2cWindow`, bound the index set's cardinality by a
`biUnion` over the primes of `q·excPrimorial` of the two singleton-or-empty fibres
`{n ∈ Ioc : n = p^e}` / `{n : n + 2 = p^e}`, each `≤ 1` (`Nat.pow_lt_pow_right`-style doubling).
`hq : 0 < q` is needed: at `q = 0` the window collapses and the bound is false.
Pre-authorised amendment: `2(ω(q)+z) → ≤ 4(ω(q)+z)`.  Consumer: `hb_lemma4_l2cWindow`. -/
theorem S1_Ioc_sub_S1_l2cWindow_le (χ : DirichletCharacter ℂ q) (hq : 0 < q) (z x : ℕ) :
    S1 (Finset.Ioc x (2 * x)) - S1 (l2cWindow χ z x)
      ≤ 2 * ((q.primeFactors.card : ℝ) + (z : ℝ)) * Lwin x ^ 2 := by
  classical
  -- the removed set
  have hsplit : S1 (Finset.Ioc x (2 * x)) - S1 (l2cWindow χ z x)
      = ∑ n ∈ (Finset.Ioc x (2 * x)).filter
          (fun n => ¬ Nat.Coprime (n * (n + 2)) (q * excPrimorial χ z)),
          Λ n * Λ (n + 2) := by
    unfold S1 l2cWindow
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc x (2 * x))
      (fun n => Nat.Coprime (n * (n + 2)) (q * excPrimorial χ z)) (fun n => Λ n * Λ (n + 2))]
    ring
  rw [hsplit]
  -- restrict to the terms that can be nonzero
  set T := (Finset.Ioc x (2 * x)).filter
      (fun n => ¬ Nat.Coprime (n * (n + 2)) (q * excPrimorial χ z)) with hTdef
  set G := T.filter (fun n => Λ n ≠ 0 ∧ Λ (n + 2) ≠ 0) with hGdef
  have hGT : ∑ n ∈ G, Λ n * Λ (n + 2) = ∑ n ∈ T, Λ n * Λ (n + 2) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro n hnT hnG
    by_contra hne
    have h1 : Λ n ≠ 0 := fun h => hne (by rw [h]; ring)
    have h2 : Λ (n + 2) ≠ 0 := fun h => hne (by rw [h]; ring)
    exact hnG (Finset.mem_filter.mpr ⟨hnT, h1, h2⟩)
  rw [← hGT]
  -- every G-element sits in the window with both sides prime powers
  have hGmem : ∀ n ∈ G, (x < n ∧ n ≤ 2 * x) ∧ IsPrimePow n ∧ IsPrimePow (n + 2) := by
    intro n hn
    have h := Finset.mem_filter.mp hn
    have hT := Finset.mem_filter.mp h.1
    exact ⟨Finset.mem_Ioc.mp hT.1, vonMangoldt_ne_zero_iff.mp h.2.1,
      vonMangoldt_ne_zero_iff.mp h.2.2⟩
  -- termwise bound
  have hterm : ∀ n ∈ G, Λ n * Λ (n + 2) ≤ Lwin x ^ 2 := by
    intro n hn
    obtain ⟨⟨hn1, hn2⟩, _, _⟩ := hGmem n hn
    have hx1 : 1 ≤ x := by omega
    have h1 : Λ n ≤ Lwin x := by
      refine le_trans vonMangoldt_le_log ?_
      rw [Lwin]
      refine Real.log_le_log ?_ ?_
      · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
        linarith
      · have : (n : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hn2
        linarith
    have h2 : Λ (n + 2) ≤ Lwin x := by
      refine le_trans vonMangoldt_le_log ?_
      rw [Lwin]
      refine Real.log_le_log ?_ ?_
      · have : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 2)
        linarith
      · have : ((n + 2 : ℕ) : ℝ) ≤ 2 * (x : ℝ) + 2 := by
          push_cast
          have : (n : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hn2
          linarith
        exact this
    calc Λ n * Λ (n + 2) ≤ Lwin x * Lwin x :=
          mul_le_mul h1 h2 vonMangoldt_nonneg (Lwin_nonneg x)
      _ = Lwin x ^ 2 := by ring
  have hsum : ∑ n ∈ G, Λ n * Λ (n + 2) ≤ (G.card : ℝ) * Lwin x ^ 2 := by
    calc ∑ n ∈ G, Λ n * Λ (n + 2) ≤ ∑ _n ∈ G, Lwin x ^ 2 := Finset.sum_le_sum hterm
      _ = (G.card : ℝ) * Lwin x ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the cardinality bound
  set PS := q.primeFactors ∪ (Finset.range z).filter (fun r => Nat.Prime r) with hPSdef
  have hcover : G ⊆ PS.biUnion (fun p => G.filter (fun n => p ∣ n ∨ p ∣ (n + 2))) := by
    intro n hn
    have h := Finset.mem_filter.mp hn
    have hT := Finset.mem_filter.mp h.1
    have hncop : ¬ Nat.Coprime (n * (n + 2)) (q * excPrimorial χ z) := hT.2
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
      (show Nat.gcd (n * (n + 2)) (q * excPrimorial χ z) ≠ 1 from hncop)
    have hpn : p ∣ n * (n + 2) := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpm : p ∣ q * excPrimorial χ z := hpdvd.trans (Nat.gcd_dvd_right _ _)
    exact Finset.mem_biUnion.mpr ⟨p, chain_prime_mem_PS χ hq hp hpm,
      Finset.mem_filter.mpr ⟨hn, (Nat.Prime.dvd_mul hp).mp hpn⟩⟩
  have hprime : ∀ p ∈ PS, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact (Finset.mem_filter.mp h).2
  have hfib : ∀ p ∈ PS, (G.filter (fun n => p ∣ n ∨ p ∣ (n + 2))).card ≤ 2 := by
    intro p hpPS
    have hp := hprime p hpPS
    have hone1 : (G.filter (fun n => p ∣ n)).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro a ha b hb
      have hA := Finset.mem_filter.mp ha
      have hB := Finset.mem_filter.mp hb
      obtain ⟨⟨ha1, ha2⟩, happ, _⟩ := hGmem a hA.1
      obtain ⟨⟨hb1, hb2⟩, hbpp, _⟩ := hGmem b hB.1
      exact chain_primepow_unique hp happ hbpp hA.2 hB.2 ha1 ha2 hb1 hb2 (by omega)
    have hone2 : (G.filter (fun n => p ∣ (n + 2))).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro a ha b hb
      have hA := Finset.mem_filter.mp ha
      have hB := Finset.mem_filter.mp hb
      obtain ⟨⟨ha1, ha2⟩, _, happ⟩ := hGmem a hA.1
      obtain ⟨⟨hb1, hb2⟩, _, hbpp⟩ := hGmem b hB.1
      have := chain_primepow_unique (a := a + 2) (b := b + 2) (c := x + 2) (d := 2 * x + 2)
        hp happ hbpp hA.2 hB.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      omega
    calc (G.filter (fun n => p ∣ n ∨ p ∣ (n + 2))).card
        = ((G.filter (fun n => p ∣ n)) ∪ (G.filter (fun n => p ∣ (n + 2)))).card := by
          rw [← Finset.filter_or]
      _ ≤ (G.filter (fun n => p ∣ n)).card + (G.filter (fun n => p ∣ (n + 2))).card :=
          Finset.card_union_le _ _
      _ ≤ 2 := by omega
  have hcardG : G.card ≤ 2 * PS.card := by
    calc G.card ≤ (PS.biUnion (fun p => G.filter (fun n => p ∣ n ∨ p ∣ (n + 2)))).card :=
          Finset.card_le_card hcover
      _ ≤ ∑ p ∈ PS, (G.filter (fun n => p ∣ n ∨ p ∣ (n + 2))).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ PS, 2 := Finset.sum_le_sum hfib
      _ = 2 * PS.card := by rw [Finset.sum_const, smul_eq_mul]; ring
  have hPScard : PS.card ≤ q.primeFactors.card + z := by
    calc PS.card ≤ q.primeFactors.card + ((Finset.range z).filter (fun r => Nat.Prime r)).card :=
          Finset.card_union_le _ _
      _ ≤ q.primeFactors.card + (Finset.range z).card :=
          Nat.add_le_add_left (Finset.card_filter_le _ _) _
      _ = q.primeFactors.card + z := by rw [Finset.card_range]
  have hGcardR : (G.card : ℝ) ≤ 2 * ((q.primeFactors.card : ℝ) + (z : ℝ)) := by
    have : G.card ≤ 2 * (q.primeFactors.card + z) := le_trans hcardG (by omega)
    have h2 : ((G.card : ℕ) : ℝ) ≤ ((2 * (q.primeFactors.card + z) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at h2
    linarith
  have hL2 : (0 : ℝ) ≤ Lwin x ^ 2 := sq_nonneg _
  calc ∑ n ∈ G, Λ n * Λ (n + 2) ≤ (G.card : ℝ) * Lwin x ^ 2 := hsum
    _ ≤ 2 * ((q.primeFactors.card : ℝ) + (z : ℝ)) * Lwin x ^ 2 :=
        mul_le_mul_of_nonneg_right hGcardR hL2

/-! ## §3 — HB Lemma 4 on the N8 window (`S⁽⁰⁾ = S⁽³⁾ + error`, the pretense sum symbolic) -/

/-- **THE STAR STEP WITH A UNIFORM CONSTANT** — the landed `S2_sub_S3_window`
(`StarWindow.lean`) with the divisor-bound constant `C` a PARAMETER and its defining
hypothesis `hCtau` carried, instead of `∃ C` inside the `z x` binders.  Class **B**, cap 150.
Red-first: copy `hstar_window`'s proof (`StarWindow.lean`, from its `set Wcap` line on) with
the opening `obtain ⟨C, hC0, hCbound⟩ := card_divisors_le_rpow ε hε` DELETED — `C`, `hC0`,
`hCbound := hCtau` are now the binders — then compose with `S2_sub_S3_le` exactly as
`S2_sub_S3_window` does.  Landed files untouched.  Consumer: `S2_sub_S3_l2cWindow`. -/
theorem S2_sub_S3_window_of_tau (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ)
    (hz : 1 ≤ z) (A : Finset ℕ) (hAsub : A ⊆ Finset.Ioc x (2 * x))
    (hcop : ∀ n ∈ A, Nat.Coprime (n * (n + 2)) (excPrimorial χ z))
    {C ε : ℝ} (hε : 0 < ε) (hC0 : 0 < C)
    (hCtau : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε) :
    |S2 χ A - S3 χ z A|
      ≤ 2 * (C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2)) ^ 2
          * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)) := by
  classical
  refine le_trans (S2_sub_S3_le χ hsq z A) ?_
  set Wcap : ℝ := C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2) with hWcap
  have hbase1 : (1 : ℝ) ≤ 2 * (x : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) x; linarith
  have hWcap0 : 0 ≤ Wcap := by
    rw [hWcap]
    exact mul_nonneg (mul_nonneg hC0.le (Real.rpow_nonneg (by positivity) _))
      (Real.log_nonneg hbase1)
  have huniform : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * x + 2 → tauLog m ≤ Wcap := by
    intro m hm1 hm2
    rw [tauLog]
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmR2 : (m : ℝ) ≤ 2 * (x : ℝ) + 2 := by exact_mod_cast hm2
    have htau : (m.divisors.card : ℝ) ≤ C * (2 * (x : ℝ) + 2) ^ ε := by
      refine le_trans (hCtau m hm1) ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg m) hmR2 hε.le) hC0.le
    have hlog : Real.log (m : ℝ) ≤ Real.log (2 * (x : ℝ) + 2) :=
      Real.log_le_log (by linarith) hmR2
    have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
    calc (m.divisors.card : ℝ) * Real.log (m : ℝ)
        ≤ (C * (2 * (x : ℝ) + 2) ^ ε) * Real.log (2 * (x : ℝ) + 2) :=
          mul_le_mul htau hlog hlog0 (by positivity)
      _ = Wcap := by rw [hWcap]
  have hg_nonneg : ∀ n, 0 ≤ tauLog n * tauLog (n + 2) :=
    fun n => mul_nonneg (tauLog_nonneg n) (tauLog_nonneg (n + 2))
  have hW : ∀ n ∈ A, tauLog n * tauLog (n + 2) ≤ Wcap ^ 2 := by
    intro n hn
    have hmem := hAsub hn; rw [Finset.mem_Ioc] at hmem
    have h1 : tauLog n ≤ Wcap := huniform n (by omega) (by omega)
    have h2 : tauLog (n + 2) ≤ Wcap := huniform (n + 2) (by omega) (by omega)
    calc tauLog n * tauLog (n + 2) ≤ Wcap * Wcap :=
          mul_le_mul h1 h2 (tauLog_nonneg _) hWcap0
      _ = Wcap ^ 2 := by ring
  have htgt1 : ∀ n ∈ A, 1 ≤ n ∧ n ≤ 2 * x + 2 := by
    intro n hn; have := hAsub hn; rw [Finset.mem_Ioc] at this; omega
  have htgt2 : ∀ n ∈ A, 1 ≤ n + 2 ∧ n + 2 ≤ 2 * x + 2 := by
    intro n hn; have := hAsub hn; rw [Finset.mem_Ioc] at this; omega
  have hcollapse1 : ∀ n ∈ A, HasExcSq χ z n → ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n ∧ z ≤ p :=
    fun n hn hE => excSq_ge_z_of_window χ z (hcop n hn) (dvd_mul_right n (n + 2)) hE
  have hcollapse2 : ∀ n ∈ A, HasExcSq χ z (n + 2) →
      ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ (n + 2) ∧ z ≤ p :=
    fun n hn hE => excSq_ge_z_of_window χ z (hcop n hn) (dvd_mul_left (n + 2) n) hE
  have hcount1 : ∀ p : ℕ, 0 < p →
      ((A.filter (fun n => p ^ 2 ∣ n)).card : ℝ) ≤ (x : ℝ) / (p : ℝ) ^ 2 + 1 := by
    intro p hp
    have hsub : (A.filter (fun n => p ^ 2 ∣ n)).card
        ≤ ((Finset.Ioc x (2 * x)).filter (fun n => p ^ 2 ∣ n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ hAsub)
    exact le_trans (by exact_mod_cast hsub) (sq_dvd_count_le x p hp)
  have hcount2 : ∀ p : ℕ, 0 < p →
      ((A.filter (fun n => p ^ 2 ∣ (n + 2))).card : ℝ) ≤ (x : ℝ) / (p : ℝ) ^ 2 + 1 := by
    intro p hp
    have hsub : (A.filter (fun n => p ^ 2 ∣ (n + 2))).card
        ≤ ((Finset.Ioc x (2 * x)).filter (fun n => p ^ 2 ∣ (n + 2))).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ hAsub)
    exact le_trans (by exact_mod_cast hsub) (shift_count_le hp)
  have hexc1 := exc_sum_le χ z x hz A (fun n => n) htgt1 hcollapse1
    (fun n => tauLog n * tauLog (n + 2)) hg_nonneg (Wcap ^ 2) (by positivity) hW hcount1
  have hexc2 := exc_sum_le χ z x hz A (fun n => n + 2) htgt2 hcollapse2
    (fun n => tauLog n * tauLog (n + 2)) hg_nonneg (Wcap ^ 2) (by positivity) hW hcount2
  have hterm1 : ∀ n, starErrBound χ z n * tauLog (n + 2)
      = if HasExcSq χ z n then tauLog n * tauLog (n + 2) else 0 := by
    intro n; rw [starErrBound]; split_ifs with hE
    · rfl
    · exact zero_mul _
  have hterm2 : ∀ n, tauLog n * starErrBound χ z (n + 2)
      = if HasExcSq χ z (n + 2) then tauLog n * tauLog (n + 2) else 0 := by
    intro n; rw [starErrBound]; split_ifs with hE
    · rfl
    · exact mul_zero _
  have hside1 : ∑ n ∈ A, starErrBound χ z n * tauLog (n + 2)
      = ∑ n ∈ A.filter (fun n => HasExcSq χ z n), tauLog n * tauLog (n + 2) := by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl (fun n _ => hterm1 n)
  have hside2 : ∑ n ∈ A, tauLog n * starErrBound χ z (n + 2)
      = ∑ n ∈ A.filter (fun n => HasExcSq χ z (n + 2)), tauLog n * tauLog (n + 2) := by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl (fun n _ => hterm2 n)
  have key : ∑ n ∈ A, (starErrBound χ z n * tauLog (n + 2)
        + tauLog n * starErrBound χ z (n + 2))
      ≤ Wcap ^ 2 * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ))
        + Wcap ^ 2 * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)) := by
    rw [Finset.sum_add_distrib, hside1, hside2]
    exact add_le_add hexc1 hexc2
  refine le_trans key (le_of_eq ?_)
  ring

/-- **The star step at the N8 window** — `S2_sub_S3_window_of_tau` at `A := l2cWindow χ z x`.
Class **A**, cap 30.  Red-first: `S2_sub_S3_window_of_tau χ hsq z x hz _ (l2cWindow_subset
χ z x) (l2cWindow_excPrimorial_coprime χ z x) hε hC0 hCtau`.  Consumer: `hb_lemma4_l2cWindow`. -/
theorem S2_sub_S3_l2cWindow (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ)
    (hz : 1 ≤ z) {C ε : ℝ} (hε : 0 < ε) (hC0 : 0 < C)
    (hCtau : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε) :
    |S2 χ (l2cWindow χ z x) - S3 χ z (l2cWindow χ z x)|
      ≤ 2 * (C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2)) ^ 2
          * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)) :=
  S2_sub_S3_window_of_tau χ hsq z x hz _ (l2cWindow_subset χ z x)
    (l2cWindow_excPrimorial_coprime χ z x) hε hC0 hCtau

/-- **THE LEMMA-4 ERROR ON THE N8 WINDOW**, the three landed pieces summed with the pretense
sum SYMBOLIC: the swap (§2), the unconditional master's three terms (`hb_l2c_master_unconditional`,
`L2cMasterUncond.lean`, with `L2cCmain = 2^31` from `L2cMaster.lean`), and the star step's
`x^{1+2ε}L′²/z`-grade tail.  A definition (no obligation).  `C` is the divisor-bound
constant of `S2_sub_S3_window_of_tau` — a parameter, so N9 chooses it once.
N9 feeds `pretenseSum_at_repulsion_floor` into the middle term and chooses `z` so that the
whole is `O(x/z₀)` — HB's Lemma 4 at `z₀ ≤ A·log log η`.  ⚠ At N9's `z = ⌈q^{1/z₀}⌉` and
`x ∈ [q^250, q^500]` the corpus's `z0 z x = Lwin x / log z` is `≈ (250…500)·z₀`, so the
middle term's `exp(5·z0 z x)` is `(log η)^{≈2500·A}`; N9's design block must carry the two
inequalities this forces on `A` and on `C0 ≤ η` (the freeze brief §5). -/
noncomputable def lemma4Err (χ : DirichletCharacter ℂ q) (z x : ℕ) (C ε : ℝ) : ℝ :=
  2 * ((q.primeFactors.card : ℝ) + (z : ℝ)) * Lwin x ^ 2
  + (L2cCmain * ((x : ℝ) / z0 z x)
      + L2cCmain * ((x : ℝ) / Real.log x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2)
      + L2cCmain * Real.exp (2 * z0 z x)
          * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3)
  + 2 * (C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2)) ^ 2
      * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ))

/-- **HB LEMMA 4 ON THE N8 WINDOW — the reduction terminal.**  `|S⁽⁰⁾ − S⁽³⁾| ≤ lemma4Err`
from the bare master packet `{hsq, hz100, hz8, hzx}` (the landed master's binders verbatim,
`L2cMasterUncond.lean`), `hq`, and the divisor-bound packet `{hε, hC0, hCtau}` — `C` is
bound BEFORE `z x`, so the bound is uniform in `q, x` and N9 can print `K₁`.  Class **B**,
cap 150.  Red-first: `S⁽⁰⁾ − S⁽³⁾ = (S⁽⁰⁾ − S⁽¹⁾) + (S⁽¹⁾ − S⁽²⁾) + (S⁽²⁾ − S⁽³⁾)` on
`W := l2cWindow`; the first bracket is in `[0, swap]` (§2), the second in `[−master, 0]`
(`S1_le_S2` for the sign and `hb_l2c_master_unconditional` for the size — the master is
ONE-SIDED), the third `≤ star` in absolute value (`S2_sub_S3_l2cWindow`); `abs_add_le`
(NOT `abs_add`, which is not in the pin) three times.  Consumer: **N9** (`hb_theorem1`, the
next design block: HB Theorem 1 at `z = q^{1/z₀}`), thence
`twinPrimeConjecture_of_frequently_S1` (`DoorBridge.lean`), which consumes exactly a lower
bound on `S1 (Ioc x (2x))`. -/
theorem hb_lemma4_l2cWindow (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (hq : 0 < q)
    {C ε : ℝ} (hε : 0 < ε) (hC0 : 0 < C)
    (hCtau : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε)
    {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    |S1 (Finset.Ioc x (2 * x)) - S3 χ z (l2cWindow χ z x)| ≤ lemma4Err χ z x C ε := by
  have hz : 1 ≤ z := le_trans (by norm_num) hz100
  have hswap := S1_Ioc_sub_S1_l2cWindow_le χ hq z x
  have hmono := S1_l2cWindow_le_S1_Ioc χ z x
  have hmaster := hb_l2c_master_unconditional χ hsq hz100 hz8 hzx
  have hs12 := S1_le_S2 χ hsq (l2cWindow χ z x)
  have hstar := S2_sub_S3_l2cWindow χ hsq z x hz hε hC0 hCtau
  have hswapnn : (0 : ℝ) ≤ 2 * ((q.primeFactors.card : ℝ) + (z : ℝ)) * Lwin x ^ 2 := by
    positivity
  have h1 : |S1 (Finset.Ioc x (2 * x)) - S1 (l2cWindow χ z x)|
      ≤ 2 * ((q.primeFactors.card : ℝ) + (z : ℝ)) * Lwin x ^ 2 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |S1 (l2cWindow χ z x) - S2 χ (l2cWindow χ z x)|
      ≤ L2cCmain * ((x : ℝ) / z0 z x)
        + L2cCmain * ((x : ℝ) / Real.log x) * Real.exp (5 * z0 z x)
            * PretenseSum χ (2 * x + 2)
        + L2cCmain * Real.exp (2 * z0 z x)
            * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3 := by
    rw [abs_le]; constructor <;> linarith
  have hid : S1 (Finset.Ioc x (2 * x)) - S3 χ z (l2cWindow χ z x)
      = (S1 (Finset.Ioc x (2 * x)) - S1 (l2cWindow χ z x))
        + (S1 (l2cWindow χ z x) - S2 χ (l2cWindow χ z x))
        + (S2 χ (l2cWindow χ z x) - S3 χ z (l2cWindow χ z x)) := by ring
  rw [hid, lemma4Err]
  have e1 := abs_add_le ((S1 (Finset.Ioc x (2 * x)) - S1 (l2cWindow χ z x))
    + (S1 (l2cWindow χ z x) - S2 χ (l2cWindow χ z x)))
    (S2 χ (l2cWindow χ z x) - S3 χ z (l2cWindow χ z x))
  have e2 := abs_add_le (S1 (Finset.Ioc x (2 * x)) - S1 (l2cWindow χ z x))
    (S1 (l2cWindow χ z x) - S2 χ (l2cWindow χ z x))
  linarith

/-! ## §4 — HB Lemma 3 at the pretense-sum level, at the repulsion floor (the live N3 join) -/

/-- **THE PRETENSE SUM AT THE REPULSION FLOOR, at `Lp := 2L`.**
`pretenseSum_unconditional_absorbed` (`Lemma3Uncond.lean`) fired at the corpus's operating
point `σ = 1 + 1/(2L)`, `σ′ = 1 + √(log η)/(2L)` — the point `two_mul_pretenseSum_le_at_window`
(`Lemma7F.lean`) fires it at, and the ONLY point at which the rate's `hCR` is satisfiable
with `L = log q` — with the floor antecedent discharged from `hceil` by
`one_sub_ceiling_le_dist_one` and the rate absorbed by `hbCoreRate_at_hb_optimum_absorbed`.

**The binder list is the zero-side packet of `hb_L1_one_sided_at_repulsion_floor`
(`HSigmaComp.lean`) character-for-character** — `hLpos hη hell hηq hCs hSinvC hCR hβlo hβ1
hβ0 hb hQ hu hD hlarge hceil` — so N9 instantiates the `(L1)` join and this row from ONE
packet at ONE `L`-scale (`L = log q`, `η = 1/((1−β₀)L)`).  Class **B**, cap 200.
Red-first: `repulsion_floor_gives_hsigma hb hLpos hQ hβ1 hη hu hD hlarge` gives `hr0` and
`hσ'r : √(log η)/(2L) ≤ r0/2`; `hσr : 1/(2L) ≤ r0/2` follows from `1 ≤ √(log η)` (`hell`);
the operating-point side conditions `1 < σ ≤ σ′ ≤ 2` are `hell`/`hηq` (`√ℓ ≤ ℓ ≤ L ≤ 2L`,
`L ≥ 1/2`); the rate: `hbCoreRate_at_hb_optimum_absorbed (Lp := 2 * L) (ell := Real.log η)`
with `hellL : log η ≤ 2L` and `hCR' : 1600·log(80√f(1+log f)) ≤ 800·(2L)`, both `linarith`
from the packet; finally `(1−β₀)/(1/(2L))² = (1−β₀)(2L)²` by `field_simp`.
Consumer: **N9** (into `lemma4Err`'s `PretenseSum χ (2x+2)`).  `Sinv` is deliberately still
an antecedent (priced by `invSq_sum_split_le`; N9's).  ⚠ Two A-class nodes N9 must BOOK
before the fulcrum hands this packet over: `fulcrum_zero_real_zfr`'s `hcal` (the owed numeral
`c₀ = 1/126848`) and `hq3 : 3 ≤ q` (`Fulcrum/Basic.lean`). -/
theorem pretenseSum_at_repulsion_floor {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (N : ℕ)
    {β₀ Sinv Cs L η b c k Q u : ℝ}
    (hLpos : 0 < L) (hη : η = 1 / ((1 - β₀) * L))
    (hell : 1 ≤ Real.log η) (hηq : Real.log η ≤ L) (hCs : 0 ≤ Cs)
    (hSinvC : Sinv ≤ Cs * ((2 * L) ^ 2 / Real.log η))
    (hCR : Real.log (80 * Real.sqrt f * (1 + Real.log f)) ≤ L)
    (hβlo : 1 / 2 < β₀) (hβ1 : β₀ < 1)
    (hβ0 : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0)
    (hb : 0 < b) (hQ : 1 < Q) (hu : u = 1 - β₀)
    (hD : 0 ≤ Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
    (hlarge : (b * Real.log Q / L
        + (Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
            / (b * Real.log Q / L)) ^ 2 ≤ Real.log η)
    (hceil : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ ≠ (β₀ : ℂ) →
        ρ.re ≤ repulsionCeiling b c k Q u) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (β₀ : ℂ) ∈ Z ∧ 1 ≤ m (β₀ : ℂ) ∧
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ Z, (m ρ : ℝ) ≤ (Salt.SW.zeroMult χ ρ : ℝ)) ∧
      ((∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv) →
        PretenseSum χ N
          ≤ (N : ℝ) ^ (1 / (2 * L)) * ((1 - β₀) * (2 * L) ^ 2
              + (2 + (802 + 4 * Cs) * ((2 * L) / Real.sqrt (Real.log η)))) / 2) := by
  obtain ⟨hr0, hσ'r⟩ := repulsion_floor_gives_hsigma hb hLpos hQ hβ1 hη hu hD hlarge
  have hell0 : (0 : ℝ) < Real.log η := lt_of_lt_of_le zero_lt_one hell
  have hL1 : (1 : ℝ) ≤ L := le_trans hell hηq
  have hL2pos : (0 : ℝ) < 2 * L := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt (Real.log η) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hell
  have hmul : Real.sqrt (Real.log η) * Real.sqrt (Real.log η) = Real.log η :=
    Real.mul_self_sqrt hell0.le
  have hsle : Real.sqrt (Real.log η) ≤ 2 * L := by nlinarith [hmul]
  have hinv0 : (0 : ℝ) < 1 / (2 * L) := by positivity
  have hinv1 : 1 / (2 * L) ≤ 1 := (div_le_one hL2pos).mpr (by linarith)
  have hσ1 : (1 : ℝ) < 1 + 1 / (2 * L) := by linarith
  have hσ2 : 1 + 1 / (2 * L) ≤ 2 := by linarith
  have hlt : 1 + 1 / (2 * L) ≤ 1 + Real.sqrt (Real.log η) / (2 * L) := by
    have := (div_le_div_iff_of_pos_right hL2pos).mpr hs1
    linarith
  have hσ'2 : 1 + Real.sqrt (Real.log η) / (2 * L) ≤ 2 := by
    have := (div_le_one hL2pos).mpr hsle
    linarith
  obtain ⟨Z, m, hβZ, hmβ, hzero, hmz, hbody⟩ :=
    pretenseSum_unconditional_absorbed χ hχ hf N
      (σ := 1 + 1 / (2 * L)) (σ' := 1 + Real.sqrt (Real.log η) / (2 * L))
      (β₀ := β₀) (Sinv := Sinv)
      hσ1 hσ2 hlt hσ'2 hβlo hβ1 hβ0 hr0 (by linarith) (by linarith)
  refine ⟨Z, m, hβZ, hmβ, hzero, hmz, fun hSinv => ?_⟩
  have hfloor : ∀ ρ ∈ Z.erase ((β₀ : ℂ)),
      (Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q + 2))
        / (b * Real.log Q) ≤ ‖ρ - 1‖ := by
    intro ρ hρ
    exact one_sub_ceiling_le_dist_one
      (hceil ρ (hzero ρ (Finset.mem_of_mem_erase hρ)) (Finset.ne_of_mem_erase hρ))
  have hmain := hbody hfloor hSinv
  have hrate := hbCoreRate_at_hb_optimum_absorbed (Lp := 2 * L) (ell := Real.log η)
    (Sinv := Sinv) (Cs := Cs)
    (CR := 1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f)))
    hell (by linarith) hCs hSinvC (by linarith)
  have hexp : (1 + 1 / (2 * L)) - 1 = 1 / (2 * L) := by ring
  have hNn : (0 : ℝ) ≤ (N : ℝ) ^ (1 / (2 * L) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hstep : (N : ℝ) ^ ((1 + 1 / (2 * L)) - 1) * ((1 - β₀) / ((1 + 1 / (2 * L)) - 1) ^ 2
        + hbCoreRate (1 + 1 / (2 * L)) (1 + Real.sqrt (Real.log η) / (2 * L)) Sinv
            (1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f))
              * ((1 + Real.sqrt (Real.log η) / (2 * L)) - (1 + 1 / (2 * L)))))
      ≤ (N : ℝ) ^ (1 / (2 * L)) * ((1 - β₀) * (2 * L) ^ 2
          + (2 + (802 + 4 * Cs) * ((2 * L) / Real.sqrt (Real.log η)))) := by
    rw [hexp]
    have hpole : (1 - β₀) / (1 / (2 * L) : ℝ) ^ 2 = (1 - β₀) * (2 * L) ^ 2 := by
      field_simp
    rw [hpole]
    nlinarith [mul_le_mul_of_nonneg_left hrate hNn]
  linarith

end Salt.HB
