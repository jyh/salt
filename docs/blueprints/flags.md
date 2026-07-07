# Flags and claims

Append-only log. Sessions record here: node claims (to avoid duplicate work),
failed attempts (node id, model, what was tried, where it broke), and
statement concerns (never fix a statement yourself — flag it).

Format, one entry per line block:

```
## <date> <node-id> <model> <status: claimed | failed | statement-concern | done>
<free text: what was tried / where it broke / concern>
```

---

## 2026-07-07 N2.1 Haiku done
Implemented `rho` as a definition counting solutions to n(n+2) ≡ 0 (mod d).
Used pattern matching on d to handle d=0 case, and Finset.filter for d>0.
Clean build, axioms: [propext, Classical.choice, Quot.sound].

## 2026-07-07 N2.5 Haiku done
Implemented `twinProd_strictMono` lemma proving n ↦ n*(n+2) is strictly monotone.
Used calc chain with Nat arithmetic lemmas. 
Clean build, axioms: [propext, Quot.sound].

## 2026-07-07 N4.1 Haiku failed
Attempted to prove 6^ω(d) ≤ d³ for squarefree d. Requires product-of-factors
bound via unique factorization (showing ∏(p | d) p = d) and Finset manipulation.
This is class-B/C (requires squarefree API + finset product algebra), not class-A.
Blocked on tier. Escalate to Sonnet/Opus.

## 2026-07-07 N4.1 Sonnet done
Proved `six_pow_omega_le_d_cubed` using `Nat.prod_primeFactors_of_squarefree`
(d = ∏ p ∈ primeFactors, p for squarefree d), then `Finset.prod_le_prod` termwise
(6 ≤ p³ for prime p ≥ 2, via nlinarith) and `Finset.prod_pow` to fold back to d³.
Clean build, axioms: [propext, Classical.choice, Quot.sound].

## 2026-07-07 N2.3 Sonnet done
Proved `rho_two : rho 2 = 1` and `rho_odd_prime : p.Prime → p ≠ 2 → rho p = 2`.
Refactored `rho`'s definition (N2.1) from a `d+1` pattern-match to an
`if h : d = 0 then 0 else haveI : NeZero d := ⟨h⟩; ...` form — the pattern-match
version made `Fintype (ZMod d)` instances for general `d` fail to unify
definitionally when rewriting `p = (p-1)+1` (motive-not-type-correct errors),
since equal-but-syntactically-different `NeZero` proofs produced non-defeq
`Fintype` instances. The `if`/`haveI` form sidesteps this. Key mathlib lemmas:
`ZMod.natCast_eq_zero_iff`, `Nat.prime_dvd_prime_iff_eq`, `Finset.card_insert_of_notMem`
(not `_not_mem`, renamed in this mathlib version). Also note: `decide` fails with
"Expected type must not contain free variables" on ZMod-2 equalities when a local
`Fact p.Prime` instance is in scope (routes DecidableEq through the Field
instance); works fine decided in isolation before introducing Fact.
Clean build, axioms: [propext, Classical.choice, Quot.sound].

## 2026-07-07 N2.4 Sonnet done
Proved `progression_count_bound`: |#{n∈Icc 1 N : d∣n(n+2)} - N*rho(d)/d| ≤ rho(d).
Turned out substantially harder than a typical class-B lookup — no existing
mathlib lemma gives this directly (closest was `Nat.count_modEq_card`/
`Int.Ico_filter_modEq_card`, exact ceiling/floor formulas, but combining them
per-residue and summing over rho(d) roots led to fragile sign-error-prone
algebra). Instead proved a general reusable lemma in a new file
`Salt/Brun/CongruenceCounting.lean`: for any residue set S mod d, the count of
n∈Icc 1 N with n%d∈S differs from N*|S∩range d|/d by at most |S∩range d|.
Proof strategy: block decomposition — any d consecutive naturals hit every
residue exactly once (`block_mod_bij`, via injectivity + card + subset
argument), giving an exact step lemma `congCount(N+d) = congCount(N) + |S|`,
then induction gives `congCount(q*d+s) = q*|S| + congCount(s)`, and a base
case bound for s<d, then pure real algebra (isolated in its own lemma to keep
field_simp/ring from choking on Nat-cast noise). Connected to `rho` via a
`Rnat d` (nat-valued root set through `ZMod.val`) and
`dvd_iff_mem_Rnat : d∣n(n+2) ↔ n%d∈Rnat d`. Gotchas: `Nat.div_add_mod'` (not
`Nat.div_add_mod`, which has d*(N/d) not (N/d)*d); writing `(N%d:ℝ)` directly
in a real-typed argument position silently elaborates as real mod on casts of
N,d separately (need explicit `((N%d:ℕ):ℝ)` parens to force Nat mod first).
Clean build, axioms: [propext, Classical.choice, Quot.sound].

## 2026-07-07 N2.2 Sonnet done
Proved `rho_mul_of_coprime : m≠0 → n≠0 → m.Coprime n → rho(m*n) = rho m * rho n`.
Went via a direct CRT bijection on the nat-valued root sets (`Rnat`) rather
than through the `ZMod.chineseRemainder` ring-equiv API the blueprint
suggested — unpacking that equiv's internal `castHom`/case-split definition
looked more painful than just using `Nat.chineseRemainder` directly plus
`Nat.ModEq` congruence lemmas (`Nat.mod_modEq`, `.mul`, `.add_right`,
`Nat.modEq_and_modEq_iff_modEq_mul`, `Nat.Coprime.mul_dvd_of_dvd_of_dvd`) to
build the map/inj/surj three-part `Finset.card_bij` argument. Added helper
lemmas `mem_Rnat_iff` (membership for a representative already `< d`) and
`Rnat_lt`. Gotcha: `have h : r%m = a%m := hra` to peel a `Nat.ModEq` back to
its underlying equation works by defeq (`rw`/`rwa` directly on the ModEq term
does not, since `≡ [MOD]` notation doesn't unify against `_%_=_%_` patterns
syntactically). Clean build, axioms: [propext, Classical.choice, Quot.sound].

## 2026-07-07 N2.7 Sonnet done (part 2 only)
Proved `rho_squarefree_le : Squarefree d → rho d ≤ 2^ω(d)` in Salt/Brun/M2.lean
(M2 now imports M4 to reuse its `omega` def). Strong induction on d: peel off
one prime factor p via `Nat.exists_prime_and_dvd` + `Nat.squarefree_mul_iff`
(gives p.Coprime d' and Squarefree d'), apply `rho_mul_of_coprime` (N2.2) and
`omega_mul_coprime`/`omega_prime` (new small helpers, via `Nat.primeFactors_mul`
+ `Nat.Coprime.disjoint_primeFactors` and `Nat.Prime.primeFactors`), bound
rho(p)≤2 via rho_two/rho_odd_prime (N2.3), recurse on d'. Part 1 of N2.7
(`|rem d| ≤ rho d`) is not separately stated: it is exactly
`progression_count_bound` (N2.4) once `rem` is instantiated against an actual
SelbergSieve instance, which requires N2.6 first — noted in the docstring
rather than restated. Clean build, axioms:
[propext, Classical.choice, Quot.sound].

## 2026-07-07 N2.6 Sonnet not-attempted
Looked at mathlib's `BoundingSieve` structure (SelbergSieve.lean): it needs
`support`, `prodPrimes` (+ squarefree proof), `weights` (+ nonneg), `totalMass`,
`nu : ArithmeticFunction ℝ` (+ IsMultiplicative, positivity/sub-1 bounds on
primes). Building this instance requires choosing a sieve level `z` (a further
parameter not fixed anywhere in M2) and design decisions about `support`/
`weights` — this is "new definitions, real proof design" (class C per
CLAUDE.md's rubric), not a routine 2-5-lemma B lookup, even though the
blueprint pre-classified it as B. Flagging rather than attempting at this
tier; recommend Opus, and recommend the blueprint table be revisited (z's
role should probably be made explicit before N2.6 is attempted).

## 2026-07-07 N3.3 Sonnet done (part 1 only)
Proved `card_divisors_le_two_pow_cardFactors : m≠0 → m.divisors.card ≤ 2^Ω(m)`
in new file Salt/Brun/M3.lean (Ω = ArithmeticFunction.cardFactors, the "big
Omega" counted-with-multiplicity prime factor count; opened via
`scoped ArithmeticFunction.Omega`). Proof: `Nat.card_divisors` gives
τ(m)=∏(a_p+1) over the factorization; `cardFactors_eq_sum_factorization`
gives Ω(m)=Σa_p; bound each factor `a_p+1 ≤ 2^a_p` (`Nat.lt_two_pow_self`)
and fold via `Finset.prod_pow_eq_pow_sum`. Part 2 of N3.3 (`ν*(m)≥τ(m)/m` for
odd m) needs `ν*` from N3.2, which needs the sieve instance (N2.6, already
flagged class-C) — not restated here, same pattern as N2.7.
Clean build, axioms: [propext, Classical.choice, Quot.sound].
