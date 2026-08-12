# CERT-LAYER — PAPER-SIDE ANCHOR TABLE (salt side)

**Math seat, 2026-08-11, at the maestro's 14:32 cert-scope ruling.** The target list is
keyed to **claims the two papers rely on — the Nature draft AND the Pi flagship —
matched SEMANTICALLY, never by name.** This table supplies the missing left-hand side:
for each target, *which paper, which site, and the paper's own phrase.*

⚠️ **WHY THIS EXISTS.** A name-match over the Pi flagship found only 5 of 16 target names.
That measurement was **fenced and it was right to fence it**: the wall is cited as
`neutrality_rate` while the list names its three parts, and Nature §5 cites nine results as
a **class enumeration** with zero declaration names. **Name-absence is not claim-absence.**

⚖️ **RULE (from the ruling): a row with NO anchor in EITHER paper LEAVES the wave** —
parked as corpus hygiene, not certified. Evidence's seal check runs **cert-vs-ANCHOR**;
this table names the left-hand side explicitly. The executor wave sizes itself from the
**anchored rows only**.

Sources: Pi = `papers/flagship/main.tex`. Nature = `${SEAT_DIR}/briefs/2026-08-11-nature-draft-v0.md`.

---

## ANCHORED — 12 rows (3 landed, 9 open)

| # | target | anchor: paper · site · the paper's own phrase | state |
|---|---|---|---|
| 1 | `vaughan` | **Nature :208** — *"Vaughan's identity"*, in the **independent-formalizations** sentence (not a firsts claim) | ✅ `cert_vaughan` |
| 2 | `sufficient_true_not_parityInv` | **Pi `thm:gap`** (:644) — *"no predicate `E` is both twin-sufficient and parity-invariant"*; Nature :218 *"a formal gap theorem for parity-invariant sieve certificates"* | ✅ `cert_parity_gap` |
| 3 | `zeta_zero_free_region_pow` | **Pi `thm:pow`** (:257) — *"the first power-saving region"*; **Nature :202** *"a zero-free region beyond de la Vallée Poussin strength"*, :239 *"the [θ = 3/4-power] zero-free region on day 13"* | ✅ `cert_zeta_zero_free_pow` |
| 4 | `bounded_gaps_unconditional` | **Nature :238** — *"unconditional bounded prime gaps on day 8"*. **No Pi anchor** (Pi never states it) | open |
| 5 | `chen_headline` / `chen_omega_prod_le_three` | **Nature :201** *"Chen's theorem"*, :238 *"Chen's theorem on day 10"*; **Pi :324** `\leaninline{chen_omega_prod_le_three}` with *"Ω(p(p+2)) ≤ 3 for infinitely many primes"* | open |
| 6 | `chen_goldbach` | **Nature :201** — same *"Chen's theorem"* class enumeration. ⚠️ *shares row 5's anchor; confirm the two decls are distinct claims before writing two files* | open |
| 7 | `siegelWalfisz_holds` | **Nature :200** *"the Siegel–Walfisz theorem"*; **Pi :322** *"an unconditional Siegel–Walfisz theorem"* (prose, no pin — line re-pinned 321→322 at the cert) | ✅ `Salt/Certs/SiegelWalfisz.lean` — unfolds BOTH opaque names (SiegelWalfisz, psiAP), closes by `exact` |
| 8 | `analytic_LS` + `char_LS` | **Nature :200** — *"the large sieve inequality"*; and :204, the adversary sentence (*the two live external BV projects take SW and the large sieve as axioms*) | open |
| 9 | `vmvt` | **Pi `thm:vmvt`** (:311) + Appendix A :982–1002; **Nature :201** *"the Vinogradov mean value theorem"* | ✅ `cert_vmvt` (+ unconditional `_iff`), `Salt/Certs/Vmvt.lean` — maestro, landed 8/11 (actual class B: the decode was definitional + `pow_mul` + `ring`; the C-grade was priced for a semantic gap that did not exist) |
| 10 | `norm_kloosterman_estermann` | **Nature :202** — *"the Weil bound for Kloosterman sums"* | ✅ `Salt/Certs/Kloosterman.lean` — the paper says WEIL, the kernel holds ESTERMANN; cert derives `2√p` at odd primes to close the name gap |
| 11 | THE WALL — `twin_bar` · `no_twin_weight` · `least_k_theorem` | **Pi `neutrality_rate`** :1173 (the wall's Pi-side decl is **not** any of the three target names); **Nature :217** *"relevant Maynard-class can cross the twin gate (M₂ ≤ 2 log 2 < 2), that the least k …"* | open — **one file, three decls** |
| 12 | `log_chowla_two_door_only` | **Pi `thm:spine`** — the logarithmic two-point Chowla reduction to a single named hypothesis | open |

## ⛔ PARKED — NO ANCHOR IN EITHER PAPER (measured, not assumed)

| target | measurement |
|---|---|
| `gaps_le_twelve` | Nature: `"12"` **0 hits**, `"twelve"` **0**. Pi: all 8 `"12"` hits are `\tfrac12`, `126848`, `1/2`, and Unicode declarations — **none is the gaps ≤ 12 claim**. |
| `psiTot_pnt` | Nature: `"prime number theorem"` **0**, `"Chebyshev"` **0**, `"psi"` **0**. Pi: both `"psi"` hits are `\varepsilon`/Greek, **not** the declaration. |

⇒ **Both LEAVE the wave.** Corpus hygiene, not certification. *If a later draft comes to
rely on either, the row re-enters with its anchor.*

---

## COUNT
```
14 target rows · 12 ANCHORED · 2 PARKED · **5 LANDED · 7 OPEN** for the wave

⚠️ **THIS COUNT IS DERIVED FROM THE ROWS ABOVE AND WENT STALE ONCE ALREADY** — it read
"3 LANDED · 9 OPEN" while the table showed five ✅ (rows 1, 2, 3, 9, 10), because the
primary rows moved and the derived line did not. Caught by a reader (maestro, 20:51), not
by its author. **Re-derive it from the ✅ marks before quoting it; do not trust this line
against the rows.**
```
📌 **For the wave brief:** each cert's docstring maps **paper-phrase → kernel declarations**,
following the `main.tex:1261` model (which decodes *"the certified `A₀` range"* into the
binders `h1`,`h2`). Row 11 is the sharpest case: the paper's one phrase covers three
declarations, and the certificate is where that correspondence becomes checkable.
