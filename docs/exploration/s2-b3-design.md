# S2-B3 DESIGN FREEZE — the GEH_min door (narrowed, JYH-funded)

**Status: FROZEN (house, 2026-07-17 ~06:30) — PENDING GATE.**
Provenance: the B3 recon (NOT-PLACEABLE as registered; this is the
JYH-funded narrowed door: GEH_min stated + GEH_min ⟹ H₁ ≤ 12 +
the ≤6 sharpening stated-not-attempted). Primary source: Polymath8b
Claim 2.6 (arXiv:1407.4897), fetched 2026-07-17 via ar5iv TEXT
EXTRACTION — the gate re-verifies the statement against the source
(transcribe-first caveat). θ < 1/2 is their Thm 2.8 (Motohashi) —
the consistency anchor.

## House catches at freeze (vs the recon's sketch)

1. **The consumable target is π-based**: maxDiscrepancy
   (Salt/Maynard.lean:90) is |π(x;q,a) − π(x)/φ(q)| over
   primesCount — NOT ψ-weighted as the recon's report said. The
   N-N2 seam lands on prime COUNTS (trap-iv class, caught at
   freeze).
2. **1_prime is not a convolution** — "specialize α⋆β := Λ" cannot
   be N-N2's mechanism. The honest route: the corpus's OWN landed
   Vaughan machinery (Salt/BV/TypeI.lean, TypeII.lean,
   Dispersion.lean) with the level parameter freed — GEH_min feeds
   the Vaughan pieces, each a genuine mid-range convolution.
3. **Honest-direction rule**: GEH_min must be AT MOST as strong as
   P8b GEH (implied by it), never stronger. Two spots where this
   bites: the SW slot is FLAT-K (drops P8b's τ(qr)^{O(1)}
   allowance — demanding MORE of β ⟹ FEWER quantified pairs ⟹
   weaker conjecture, safe); the coefficient class carries the
   τ-exponent k OUTSIDE the ∃B∃C (every fixed exponent covered,
   faithful to ≪ τ^{O(1)}log^{O(1)}).

## Frozen Lean shape — Salt/Maynard/GehDoor.lean
(imports: Salt.Maynard.Level + Salt.BV.Defs; NO .All)

```lean
noncomputable def seqDiscrepancy (f : ℕ → ℝ) (x q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
  ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup'
    (exists_coprime_lt hq) (fun a =>
      |(∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0)
        - (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n else 0)
          / (q.totient : ℝ)|)

noncomputable def dconv (α β : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, α d * β (n / d)

def CoeffAt (α : ℕ → ℝ) (N x : ℕ) (k : ℕ) : Prop :=
  (∀ n, α n ≠ 0 → n ∈ Finset.Ioc N (2 * N)) ∧
  ∀ n, |α n| ≤ (n.divisors.card : ℝ) ^ k * Real.log x ^ k

def SWAt (β : ℕ → ℝ) (M x : ℕ) : Prop :=
  ∀ A C : ℝ, 0 < A → 0 < C → ∃ K, 0 ≤ K ∧ ∀ r q : ℕ, 0 < r → 0 < q →
    (q : ℝ) ≤ Real.log x ^ C →
    seqDiscrepancy (fun n => if Nat.Coprime n r then β n else 0) x q
      ≤ K * M / Real.log x ^ A

def GEH_min (θ : ℝ) : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∀ k : ℕ, ∃ B C : ℝ, 0 ≤ B ∧
  ∀ x N M : ℕ, 2 ≤ x →
    (x : ℝ) ^ ε ≤ N → (N : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
    (x : ℝ) ^ ε ≤ M → (M : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
    N * M ≤ x → x ≤ 4 * N * M →
  ∀ α β : ℕ → ℝ, CoeffAt α N x k → CoeffAt β M x k → SWAt β M x →
    (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
        seqDiscrepancy (dconv α β) x q)
      ≤ C * x / Real.log x ^ A
```

Binding notes: the coprime MEAN (not π(x)/φ(q)-style totals) is the
main term — P8b's Δ; the ∃B haircut mirrors HasLevel's BV shape;
quantifier order per III.4 (B, C uniform over x, N, M, α, β; k
outside ∃).

## Node plan

| Node | Class | Content | Est. |
|---|---|---|---|
| D-N1 | B/C | The defs above + trivia (nonneg, monotone-in-θ mirror of HasLevel_antitone) + **anti-vacuity**: (i) SWAt holds for the constant sequence 1 on a range (trivial discrepancy ≤ 1 + bookkeeping); (ii) seqDiscrepancy of 1_prime relates to maxDiscrepancy (the π-seam lemma, coprime-mean vs π(x)/φ(q): differ by ≤ ω(q)·bounded, polylog summed) | ~120k |
| D-N2 | **C** | `GEH_min (3999/4000) → HasLevel (3999/4000)`: Vaughan split (the corpus's TypeI/TypeII machinery re-read at AP-discrepancy level, level freed), pieces fed to GEH_min — smooth factor = the SW side (flat SW trivial for 1/log-on-range); Λ/μ-side SW from the LANDED siegelWalfisz_holds via psiAP endpoint subtraction; Type-I₁/I₂/II case table below | ~250k |
| D-N3 | A | Compose with the landed gaps_le_twelve_of_hasLevel → `GEH_min (3999/4000) → H₁ ≤ 12` (spelled at the landed gap theorem's exact conclusion) | ~15k |
| D-N5 | prose | The ≤6 sharpening STATED-NOT-ATTEMPTED (the ε-enlarged M₃^[ε] > 2 gap, per the recon; TwinDoor D5 discipline; R4) | in docstring |

## Case space (III.3‴ — the gate checks COMPLETENESS)

Vaughan pieces {I₁ (μ≤U ⋆ log), I₂ ((μ⋆1)≤UV ⋆ 1), II (bilinear)}
× SW-side selection per piece (smooth side for I₁/I₂; the
Λ-restricted side for II) × the range checks at U = V = x^{1/3}
(all piece scales ∈ [x^{1/3−o(1)}, x^{2/3+o(1)}] ⊂ [x^ε, x^{1−ε}]
at ε ≤ 1/4 — VERIFY against the corpus's actual U, V) × the NM≍x
window (dyadic decomposition of each piece into Ioc N 2N blocks —
the log x dyadic factor absorbed by A-inflation) × q = 0 / small-x
corners × the π-seam (1_prime vs Λ: partial summation or the
corpus's PsiToPi.lean — CHECK it exists at level θ).

## III.3″ witnesses

(i) SWAt-inhabitation: the constant sequence (D-N1, in-file).
(ii) The consistency anchor: GEH_min(θ) for θ < 1/2 is Motohashi
(prose + the P8b Thm 2.8 citation; NOT formalized — stated in the
docstring as the reason the Prop is not vacuously strong).
(iii) The operating point: at x = 10⁶, q = 3, f = 1_prime —
numerically evaluate seqDiscrepancy vs maxDiscrepancy (the π-seam
sanity check, mpmath/python, in-docstring).

## Honesty / R4

GEH_min is implied by P8b GEH[θ] (flat-K SW; k-outside). The door
reaches ONLY the landed H₁ ≤ 12 under the new named hypothesis;
H₁ ≤ 6 is explicitly out (the simplex/enlarged-functional gap, B3
recon). No unconditional gap claim anywhere; the implication's
conclusion is the landed theorem's exact statement.

## Gate charge (adversarial, Opus, BEFORE executors)

1. **Source fidelity**: re-verify Claim 2.6 against arXiv:1407.4897
   (the ar5iv extraction may lie about formulas); check every
   deviation is in the WEAKER direction (GEH_min ≤ GEH).
2. **The D-N2 route audit**: read Salt/BV/TypeI.lean, TypeII.lean,
   Dispersion.lean, PsiToPi.lean at proof level — are the Vaughan
   pieces re-spellable as AP discrepancies of convolutions at
   executor cost (the 2–4× shape-binding law), or is the
   character-twisted spelling load-bearing (⟹ D-N2 re-cut or
   re-cost)? Verify the U, V scales and the ε-window arithmetic.
   Verify the corpus's Vaughan identity covers ψ (not just χ-sums).
3. **Case completeness**: the table above vs the corpus's actual
   piece inventory.
4. **Vacuity probes**: SWAt at the constant sequence (arithmetic);
   the π-seam bound (ω(q)/φ(q) summed = polylog ≪ x/log^A);
   GEH_min not trivially FALSE (the sup' over a values at tiny q).
5. **R4/naming**: the Prop deserves the GEH name (≤ literature
   strength); the conclusion is exactly the landed theorems.

*Frozen by the house session. Statement shapes above are frozen;
names/hypothesis-order latitude as marked. Statement changes:
house/human only.*
