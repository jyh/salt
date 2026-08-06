# WEIL-TRIO STATEMENT AUDIT — the landed W1 and W4Q exits against the freeze

**Date:** 2026-08-06. **Seat:** salt MATHEMATICS (tasked by the maestro, FLEET.md 10:06 item 2).
**Method:** three parallel read-only Opus auditors — W1, W4Q, and an adversarial vacuity lens —
plus this seat's own read of the W3 exit. **Zero Lean run** (the fleet's no-build order until
20:00); every verification is byte-reading plus independent Python arithmetic.
**Scope:** committed tree only, at HEAD `f6e0c12`.

**THE GENRE.** This is the sp1-lean check: hunting the failure an axiom audit *cannot* catch — a
theorem that is landed, sorry-free, three-axiom-clean, and **does not say what it is advertised to
say**. It audits STATEMENTS, not proofs.

**THE CONTRACT.** `docs/exploration/weil-trio-design-0806.md` §2 riders (`:46-53`), which read as a
ready-made kill-list: no `IsUnit` in any *exit-interface* statement (interior lemmas may); the gcd
factor never absorbed into a constant; no vacuous hypothesis pairs; width/normalization stated;
every promised theorem present; each exit carrying `#audit_axioms` and a "N7 quotes this as …"
docstring. Plus §3 (`:55-60`) and the v2 deltas D3/D4/D8/D9.

---

## 0. VERDICT

> **NO 🔴 MISMATCH. NO 🟠 WEAKER. The landed W1, W4Q and W3 exits deliver what the freeze
> promised, and the two riders that matter most — no `IsUnit` on an exit, gcd never absorbed —
> are met at every exit.** Seven 🟡 documentation/bookkeeping findings, none of them an axiom or
> soundness gap.

I said in advance that a clean audit would be reported as loudly as a red one. **It is clean.**

**But there is one finding that outranks all seven 🟡s, and it is not a defect in anyone's work —
it is a constraint on the CONSUMER.** See §2.

### What was attacked and survived
Every exit-grade and interior statement in all four files got an explicit satisfying assignment
and an edge sweep. No vacuous hypothesis pair; no `ZMod 0` leak into any exit; no `Nat`-subtraction
truncation; no `Real.sqrt` of a negative; no `gcd 0 0 = 0` degeneracy (at `A = B = 0` the value is
correctly `p^e`, not `0`); no `native_decide` anywhere (`grep` over `Salt/HB/` returns exactly one
hit, inside a docstring *asserting its absence*); no existing statement touched by either W4Q
commit (verified by `--numstat`: the 8 deleted lines are prose in a trailing comment block).

---

## 1. THE EXITS, ONE BY ONE — all ✅

### W1 — `norm_kloosterman_prime_pow_gcd` (`Salt/Weil/Estermann.lean:498`)
```lean
theorem norm_kloosterman_prime_pow_gcd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ e : ℕ, 1 ≤ e → ∀ A B : ℕ,
      ‖kloosterman ((A : ℕ) : ZMod (p ^ e)) ((B : ℕ) : ZMod (p ^ e))‖
        ≤ 2 * Real.sqrt ((p : ℝ) ^ e)
            * Real.sqrt ((Nat.gcd (p ^ e) (Nat.gcd A B) : ℕ) : ℝ)
```
- **Arbitrary `a,b`, NO `IsUnit`** ✅ (rider 1). The `∀ A B : ℕ` form is not a narrowing:
  `Nat.cast` is surjective onto `ZMod (p^e)`, and `min(e, v_p A) = min(e, v_p (A mod p^e))`, so the
  gcd is a genuine function of the residue pair — **representative-independence checked, no hole**.
- **gcd factor present and UNABSORBED** ✅ (rider 2) — its own `Real.sqrt` factor, separate from
  the constant `2` and the width `√(p^e)`.
- Conclusion is character-for-character what D8 promised; the "N7 quotes this as …" marker is
  present at `:497` ✅.
- **The constant 2 is sharp, not padded.** Independently recomputed
  `max ‖S(a,b;p^e)‖/√(p^e)`: `p=3,e=3 → 1.99662`; `p=3,e=4 → 1.99850`; `p=5,e=3 → 1.99937`;
  `p=7,e=3 → 1.99998`; `p=11,e=3 → 2.00000`. **Attained in the limit; cannot be lowered.**
- The `IsUnit` at `:268`/`:459` is *interior*, which rider 1 explicitly permits, and the docstring
  says "a **unit** `a`" in plain text — not advertised as unit-free anywhere.

### W1 — `kloosterman_descent` (`GcdBranch.lean:132`): D8's erratum is correctly landed
The landed statement is `S(pA,pB;p^{f+1}) = p·S(A,B;p^f)`, i.e. **`e−1`**, not the briefed `e−2`.
**Counterexample re-verified independently from the definition**: `S(3,3;9) = −3.0` exactly;
`3·S(1,1;3) = −3.0` ✓; `3·S(1,1;3^0) = +3.0` ✗. The identity was also checked exhaustively for
`p ∈ {3,5,7}`, `f ∈ {1,2}`. ✅

### W1-d — `factorization_two_kloosterman_modulus` (`GcdBranch.lean:347`)
Concludes exactly `v₂(D·δ₁·w₁) = v₂(D)` ✅, and the hypothesis set is **jointly satisfiable and
non-redundant** where it matters: `hα : 2 ∣ α`, `hδ`, `hw` each have explicit counterexamples
showing they are load-bearing (drop `hδ`, take `α=2, δ₁=2, w₁=1, D=1` → `v₂(2)=1 ≠ 0`).

### W3 — `norm_kloosterman_estermann` (`Salt/Weil/EstermannGlobal.lean:393`), read by this seat
```lean
theorem norm_kloosterman_estermann {k : ℕ} [NeZero k] (a b : ZMod k) :
    ‖kloosterman a b‖ ≤ Real.sqrt ((2:ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
        * Real.sqrt (k : ℝ) * Real.sqrt ((Nat.gcd k (Nat.gcd a.val b.val) : ℕ) : ℝ)
```
Matches D3's promised shape `2^{v₂(k)/2}·d(k)·k^{1/2}·(k,a,b)^{1/2}` exactly
(`√(2^κ) = 2^{κ/2}`, `d(k) = k.divisors.card`). **Arbitrary `a b : ZMod k`, no `IsUnit`; gcd
unabsorbed; and the `2^{v₂(k)/2}` factor is carried EXPLICITLY rather than hidden.** The `_road`
specialisation (`:418`) keeps `√(2^{D.factorization 2})` explicit too — so the maestro's "road
collapse honestly gated on W4-a" is accurate **at the bytes**, not merely in the prose. ✅
This closes the loop on this seat's own 10:02 finding: the gap I flagged is now visible in the
statement instead of buried.

### W4Q — `sum_two_forms_le_gcd_of_split` (`RealPrimitive.lean:381`), the p.217 exit
**Constant ONE** ✅ — no factor 2, no `2^ω`, no multiplicative constant at all. **No `IsUnit`, no
determinant-nonzero, no coefficient coprimality** — `u u' v v'` are bare universally-quantified
(`grep IsUnit` = zero hits in both files).
**NOT VACUOUS, at three levels**: (i) `χ` is a bare function `ZMod (e*m) → ℤ`, so `hχ` is
satisfiable by construction; (ii) the four admissible 2-parts are supplied in-file
(`_of_modulus_one`, `_chi4`, `_chi8`, `_chi8'` — exactly `a ∈ {0,2,3}`), and the full bundle was
instantiated and brute-forced at eight `(e,χ₂,m)` combinations with **zero violations**;
(iii) the road's χ satisfies it mathematically — and that discharge **is W4-a**, which the file
states honestly at `:53-54` and `:377`.
**The gcd is load-bearing, not decoration**: at `q = 12` the max `|Σ|` over all quadruples is
**12**, so any constant bound would be **FALSE**.

### W4Q — `sum_class_eq_zero_of_isPrimitive` (`RealPrimitive.lean:413`), the p.216 exit
"Over any domain" ✅ (`[CommRing R] [IsDomain R]`, `R` generic; χ not required real — **stronger
than HB p.216**). "No coprimality on `c`" ✅. `hprim` is **load-bearing, not idle**: the imprimitive
χ mod 9 induced from mod 3 gives `Σ = ±3` on the classes `c ≡ 1, 2 (mod 3)`. ✅

### W4Q — the 2-power rows, and the CRT engine
The three `decide` rows were **re-verified exhaustively and independently** (all 256 + 4096 + 4096
quadruples, against mathlib's exact value tables): **zero violations**, the bound is TIGHT at
`gcd ∈ {2,4,8}`, and `Σ = 0` at unit determinant is confirmed with 0 counterexamples. So the gcd
form is genuine, not a constant in disguise. `HasTwoFormGcdBound` carries **no `[NeZero q]`** — the
D9 trap is avoided ✅ — and `.mul` composes with **no `2^ω` residue**, constant 1 at every step ✅.

---

## 2. ⛔ THE FINDING THAT OUTRANKS THE 🟡s — A CONSUMER CONSTRAINT, NOT A DEFECT

**The W1 gcd exit is VACUOUS on the entire top gcd class, and N7 must not quote it there.**

Write `gcd(p^e, A, B) = p^j`, `0 ≤ j ≤ e`. The exit's RHS is `2·p^{(e+j)/2}`; the a-priori trivial
bound (`norm_kloosterman_le`, `Kloosterman.lean:54`) is `φ(p^e) = p^{e−1}(p−1)`. Solving
`2·p^{(e+j)/2} < p^{e−1}(p−1)` exactly:

| `p` | the exit beats the trivial bound iff |
|---|---|
| 3 | `e − j ≥ 3` |
| 5 | `e − j ≥ 2` |
| ≥ 7 | `e − j ≥ 1` |

> **At `j = e` — i.e. `p^e ∣ A` and `p^e ∣ B`, including `A = B = 0` — the bound is `2·p^e`,
> strictly WORSE than `φ(p^e)` and worse than `p^e`, for every `p` and every `e`.** The whole
> theorem is also vacuous at `p = 3, e ≤ 2` and at `p = 5, e = 1`.

This is the intrinsic shape of Estermann's estimate, **not** a defect in the statement or the
freeze — HB's (7.1) has the same character. But it is exactly the sp1-lean failure mode one step
downstream: *a true, sharp, three-axiom-clean theorem that says nothing in a regime where a
consumer might reach for it.* N7 assembles (7.7) by summing Kloosterman bounds over `s ≤ k₀`, and
the `s` with `p^e ∣ s·(stuff)` land in precisely this class. **N7 owes an explicit case split at
`j = e`, falling back to the trivial bound.** Recorded here so it is not discovered mid-wave.

The same analysis for the two-forms exits is *benign*: they carry no cancellation content on the
`det ≡ 0 (mod q)` class either, but they are informative on the **entire complement**, since
`gcd(q, det) < q` there. Nothing vacuous.

---

## 3. THE SEVEN 🟡 — documentation and bookkeeping, no soundness gap

**🟡 F1 — `RealPrimitive.lean:51-53` states a split-hypothesis form that CANNOT ELABORATE.**
*The one with real downstream risk.* The module docstring says the exact form is
`∀ n, χ n = χ₂ (cast n) * ∏ p ∈ m.primeFactors, quadraticChar (ZMod p) (cast n)`.
The landed binder at `:384` is `χ₂ (ZMod.cast n) * jacobiChar m (ZMod.cast n)`. The
`Finset.prod`-of-`quadraticChar` shape quoted in the docstring is **precisely the shape D9
(`:198-202`) and flags.md say does not land and cannot elaborate** — `quadraticChar (ZMod p)`
demands `Fact p.Prime`, unavailable at a *variable* `p ∈ m.primeFactors`. **Impact is concrete:
W4-a is the node that must supply this decomposition, and a W4-a executor reading the consuming
file's own header — the natural first move — will build an object that does not typecheck against
the exit.** Repair is docstring-only, no statement change.

**🟡 F2 — `quadraticChar_sum_two_forms_eq`'s right disjunct holds unconditionally.** At `a = 0`,
`quadraticChar F 0 = 0`, so `−(χa·χc) = 0` = the sum. Verified exhaustively over
`𝔽₃, 𝔽₅, 𝔽₇, 𝔽₁₁, 𝔽₁₃` (all `p⁴` quadruples with `ad − bc ≠ 0`): **zero counterexamples to the
unconditional equality, and zero cases where the left disjunct is strictly needed.** The sharp
landed form should be the equality, not the disjunction. Also the docstring claims a case-split
("`0` when one form is constant, `−χ(a)χ(c)` when both are linear") that the statement does not
carry. **Graded 🟡, not 🟠, because D4 (`:123`) asked for exactly the disjunction — the weakness is
in the freeze; the delivery is faithful.** Nothing downstream is harmed (`_bound_one` needs only
`|·| ≤ 1`).

**🟡 F3 — `hD : D ≠ 0` is redundant** on `factorization_two_mul_odd_mul_odd` (`:324`),
`factorization_two_kloosterman_modulus` (`:347`) and `two_pow_factorization_dvd_of_odd_cofactors`
(`:355`). At `D = 0` both sides are `0` (`Nat.factorization 0 = 0`), so the conclusion holds
anyway. Harmless — a real modulus is never 0 — but it is an unearned hypothesis on the row D8
says W3/N7 consumes.

**🟡 F4 — name-vs-meaning drift on `factorization_two_kloosterman_modulus`.** The name asserts
"kloosterman_modulus"; the statement is a pure `ℕ` identity with **no Kloosterman sum and no `k`**.
The identification `k = D·δ₁·w₁` (HB (5.11)/(5.12)) lives only in prose (`:337-346`), so nothing
machine-checks that the object bounded is a Kloosterman modulus — **N7 carries that identification
by hand.** Its docstring reads "W1-d (the form N7 quotes)", a paraphrase of §3's mandated literal
marker. (The three genuine exit rows — `Estermann.lean:497`, `RealPrimitive.lean:379`, `:411` —
all carry the literal marker correctly.)

**🟡 F5 — `HasTwoFormGcdBound q f` is content-free at `q = 0`, undocumented.** At `q = 0`,
`range 0 = ∅` so LHS `= 0` and RHS `= gcd 0 d = d ≥ 0`: **the predicate is true for every `f`
whatsoever.** Contained today (the exit carries `[NeZero e] [NeZero m]`, and `Squarefree m` rules
out `m = 0`), but any future consumer feeding a variable modulus must supply `q ≠ 0` itself, and
the docstring at `:148-150` — which does explain the `range q` design choice — never says so.

**🟡 F6 — the `#audit_axioms` roll-call is short by 7 of 28 in `Salt/Weil/All.lean`.** Missing:
`ushift3` (`Estermann.lean:77`), `ushift3_val` (`:100`), `ushift3_inv_val` (`:103`), `klSummand`
(`:111`), `norm_klSummand` (`:114`), `salieShift` (`:119`), `kloosterman_eq_sum_crit'` (`:123`) —
note the near-miss, the *unprimed* `kloosterman_eq_sum_crit` **is** listed. Also
`quadraticChar_sum_linear` (`QuadCharSum.lean:110`) from `Salt/HB/All.lean`.
**Enumeration gap, not a soundness gap**: each is referenced inside the proof of a listed name, so
`#audit_axioms` covers their axiom closure transitively. Fix is one line. **§3's actual requirement
is met** — all three exit rows are rolled.

**🟡 F7 — D8's "21 decls" is the roll-call size, not the declaration count.** `d1a5668 + 4a58e51`
add **28** declarations (`GcdBranch` 13 + `Estermann` 15); 21 is the audited-name count. Same units
slip in `4a58e51`'s body ("Estermann.lean 591 ln / 13 decls" — the file is 593 lines with 15
declarations) and, in the other direction, in D9 (21 audited theorems; 23 declarations, the two
extra being `def`s correctly absent from an axiom roll). Suggested D8 wording: *"28 decls, 21
audited by name (7 covered transitively), 3 axioms."*

---

## 4. CORRECTIONS TO THIS SEAT'S OWN PRIOR WORK

The audit caught two errors in the N7-prep dossier (`1019c0e`), both now fixed in place:

1. **Three line cites were 3 low** — `norm_kloosterman_prime_pow_odd_sharp`, `_unit_sharp` and
   `_gcd` were cited at `:265`/`:456`/`:495`; the committed numbers are **`:268`/`:459`/`:498`**.
   Cause: the scouts read the file while it was uncommitted and 3 lines shorter between `:167` and
   `:265`. (`norm_quadExpSum :167` was unaffected.) Corrected with a dated `[corrected]` marker.
2. **`Salt/Weil/EstermannGlobal.lean` is tracked and imported** at `Salt/Weil/All.lean:30` — my
   brief called it untracked in-flight work. It was, at dispatch; W3 landed mid-run.
3. **"six W1 declarations"** in the dossier — `GcdBranch.lean` has **13**.

All three are the same failure: **a snapshot of another seat's live tree ages in minutes.** It is
the hazard this dossier's own §0 warned about, and it caught its author twice in one morning.

---

## 5. WHAT THIS AUDIT RECOMMENDS

1. **Fix `RealPrimitive.lean:52`'s split-hypothesis formula** to
   `∀ n, χ n = χ₂ (ZMod.cast n) * jacobiChar m (ZMod.cast n)`, with the one-line reason
   (`jacobiSym` is instance-free; the product form needs `Fact p.Prime` at a variable `p`).
   **This is the only 🟡 with a concrete route to a wasted wave** — it misdirects W4-a's executor.
2. **N7: add the `j = e` case split** to the Lemma-10 assembly plan (§2). The gcd exit must not be
   quoted on the top gcd class; fall back to the trivial bound there.
3. Append the 7 + 1 missing roll-call names (one line each).
4. Consider strengthening `quadraticChar_sum_two_forms_eq` to the unconditional equality — and, if
   so, amend D4's own wording, since the disjunction came from the freeze.
5. Drop `hD : D ≠ 0` from the three `factorization_two_*` rows, or document why it stays.
6. Document the `q = 0` degeneracy of `HasTwoFormGcdBound`.

**NOT VERIFIED HERE:** no Lean was run, so this audit certifies **statements**, not that the files
kernel-check. The `EXIT=0` claims rest on the landing commits' own bodies. Statement-adequacy and
axiom-adequacy are different instruments — that is the whole premise of this document.
