/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The `q ∣ k` discharge — HB 1983, §5's modulus (5.12)

Source math: `docs/sources/hb1983-notes.md:566` (`Δ = (α₁,q) = (α₂,q)`) and `:579`
(`D = α₂ q Δ^{−1}`, equations (5.11)/(5.12)).  Demand trace:
`docs/exploration/n7-prep-dossier-0806.md:290`, gap-list row 10 — supplier **nobody**,
*GENUINELY OPEN — HB leaves it implicit; N7 owes it*.  Lemma 10 (N7) carries `q ∣ k` as a
hypothesis, and §5 fires it at `k = D·δ₁·w₁`; the dossier's substitution table records the
discharge as **INFERRED**, spelled out nowhere in the source.

## 🔑 The finding: `D` **is** the lcm, so the discharge is one mathlib lemma

With `Δ = (α₂, q)`, HB's `D = α₂ q Δ^{−1}` is exactly `Nat.lcm α₂ q` — mathlib defines
`Nat.lcm m n = m * n / Nat.gcd m n`, the same expression on the nose.  So `q ∣ D` is
`Nat.dvd_lcm_right` and nothing more, and the divisibility HB leaves implicit is **harmless
rather than hidden**: it needs no hypothesis on `α₂`, `q`, `δ₁` or `w₁`, not even nonvanishing.

That is the whole content of gap-list row 10.  It is recorded here rather than left inferred
because the row read *"GENUINELY OPEN"*, which prices an unknown; the honest price is `A`.

## ⚠️ `D` is overloaded in the source — this module pins the §5 one

`hb1983-notes.md:975` flags it: the Rosser sieve level `D = q^{1/3}` of §2 collides with §5's
`D = α₂qΔ^{−1}`.  `roadModulus` names **only the latter**.  Nothing here is about the sieve level.
-/

namespace Salt.Weil

/-- **HB (5.12)'s modulus**, `D = α₂ q Δ^{−1}` with `Δ = (α₂, q)`.  Named to keep it apart from
the §2 Rosser sieve level, which the source also calls `D`. -/
def roadModulus (α₂ q : ℕ) : ℕ := α₂ * q / Nat.gcd α₂ q

/-- **`D` is the lcm.**  HB's `α₂ q Δ^{−1}` is `Nat.lcm α₂ q` on the nose — mathlib's `Nat.lcm`
is defined by that very expression.  This is the observation that collapses the whole row. -/
theorem roadModulus_eq_lcm (α₂ q : ℕ) : roadModulus α₂ q = Nat.lcm α₂ q := rfl

/-- **`q ∣ D`** — the step HB leaves implicit.  No hypotheses: it holds for every `α₂` and `q`. -/
theorem dvd_roadModulus (α₂ q : ℕ) : q ∣ roadModulus α₂ q := by
  rw [roadModulus_eq_lcm]
  exact Nat.dvd_lcm_right α₂ q

/-- **`q ∣ k` at `k = D·δ₁·w₁`** — the discharge in the shape §5 fires it, per the dossier's
substitution table (`n7-prep-dossier-0806.md`, the Lemma 10 slot table: `k = Dδ₁w₁`).
Again hypothesis-free. -/
theorem dvd_roadModulus_mul (α₂ q δ₁ w₁ : ℕ) : q ∣ roadModulus α₂ q * δ₁ * w₁ :=
  ((dvd_roadModulus α₂ q).mul_right δ₁).mul_right w₁

/-- `α₂ ∣ D` as well, recorded because §5 uses `D` on both sides of the CRT split. -/
theorem dvd_roadModulus_left (α₂ q : ℕ) : α₂ ∣ roadModulus α₂ q := by
  rw [roadModulus_eq_lcm]
  exact Nat.dvd_lcm_left α₂ q

/-! ### The 2-adic valuation of `D` — the hinge of the dossier's FINDING #1

`Salt/Weil/EstermannGlobal.lean`'s road exit row carries an explicit factor
`√(2 ^ D.factorization 2)`, and the dossier's **FINDING #1** — *"the single most important
finding in this dossier"* — is that this factor is **unbounded at general `k`** and collapses
to a constant only on road moduli, via **W4-a** (`q = 2^a·m`, `a ∈ {0,2,3}`).

🔑 **Because `D` is the lcm (`roadModulus_eq_lcm`), that collapse is a two-line computation
rather than an open question**: the 2-adic valuation of an lcm is the *max* of the valuations,
so `v₂(D)` is bounded as soon as `v₂(q)` is — and `α₂` is a fixed parameter of the linear
forms, so `v₂(α₂)` is a constant of the problem, not of the modulus. -/

/-- **`v₂(D) = max(v₂(α₂), v₂(q))`** — the 2-adic valuation of HB's (5.12) modulus. -/
theorem factorization_two_roadModulus {α₂ q : ℕ} (hα : α₂ ≠ 0) (hq : q ≠ 0) :
    (roadModulus α₂ q).factorization 2
      = max (α₂.factorization 2) (q.factorization 2) := by
  rw [roadModulus_eq_lcm, Nat.factorization_lcm hα hq]
  rfl

/-- **THE COLLAPSE, with W4-a's role made explicit.**  Under W4-a (`v₂(q) ≤ 3`), the road
modulus's 2-adic valuation is bounded by a constant of the *problem* (`v₂(α₂)`) rather than of
the *modulus* — so `EstermannGlobal`'s explicit `√(2 ^ v₂(D))` factor is `≤ √(2 ^ max(v₂ α₂, 3))`,
a constant, and (7.1) is recovered on road moduli.

⚠️ **`hw4a` is W4-a's contribution and nothing else here supplies it.**  This row makes the
dependency mechanical instead of prose: FINDING #1's *"needs W4-a, not W1-d alone"* is exactly
this hypothesis. -/
theorem factorization_two_roadModulus_le {α₂ q : ℕ} (hα : α₂ ≠ 0) (hq : q ≠ 0)
    (hw4a : q.factorization 2 ≤ 3) :
    (roadModulus α₂ q).factorization 2 ≤ max (α₂.factorization 2) 3 := by
  rw [factorization_two_roadModulus hα hq]
  exact max_le_max le_rfl hw4a

end Salt.Weil
