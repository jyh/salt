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

⚠️ **EVERY NATURE PIN IN THIS TABLE ROTTED BY +1 ON 2026-08-11 AND ALL ARE NOW RE-DERIVED.**
Cause measured, not guessed: the draft was 384 lines when this table was written (~14:35);
`98d7b91` at 17:33 inserted a net **+1 line at line 80** — above every pinned line — so
**nine pins moved together for one reason.** Found by evidence at the seal of rows 7 and 10
(2/2 in the certs), then swept here.
🔑 ***THE PHRASE IS THE ANCHOR; THE LINE NUMBER IS A HINT THAT ROTS.*** Each row quotes the
paper's own words for exactly this reason — **re-derive the line from the phrase before
citing it**, and never carry a pin from this table into a landed artifact without that step.

---

## ANCHORED — 12 rows (3 landed, 9 open)

| # | target | anchor: paper · site · the paper's own phrase | state |
|---|---|---|---|
| 1 | `vaughan` | **Nature :209** — *"Vaughan's identity"*, in the **independent-formalizations** sentence (not a firsts claim) | ✅ `cert_vaughan` |
| 2 | `sufficient_true_not_parityInv` | **Pi `thm:gap`** (:644) — *"no predicate `E` is both twin-sufficient and parity-invariant"*; Nature :219 *"a formal gap theorem for parity-invariant sieve certificates"* | ✅ `cert_parity_gap` |
| 3 | `zeta_zero_free_region_pow` | **Pi `thm:pow`** (:257) — *"the first power-saving region"*; **Nature :203** *"a zero-free region beyond de la Vallée Poussin strength"*, :240 *"the [θ = 3/4-power] zero-free region on day 13"* | ✅ `cert_zeta_zero_free_pow` |
| 4 | `bounded_gaps_unconditional` | **Nature :239** — *"unconditional bounded prime gaps on day 8"*. **No Pi anchor** (Pi never states it) | open |
| 5 | `chen_headline` / `chen_omega_prod_le_three` | **Nature :202** *"Chen's theorem"*, :239 *"Chen's theorem on day 10"*; **Pi :324** `\leaninline{chen_omega_prod_le_three}` with *"Ω(p(p+2)) ≤ 3 for infinitely many primes"* | open |
| 6 | `chen_goldbach` | **Nature :202** — same *"Chen's theorem"* class enumeration. ⚠️ *shares row 5's anchor; confirm the two decls are distinct claims before writing two files* | open |
| 7 | `siegelWalfisz_holds` | **Nature :201** *"the Siegel–Walfisz theorem"*; **Pi :322** *"an unconditional Siegel–Walfisz theorem"* (prose, no pin — line re-pinned 321→322 at the cert) | ✅ `Salt/Certs/SiegelWalfisz.lean` — unfolds BOTH opaque names (SiegelWalfisz, psiAP), closes by `exact` |
| 8 | `analytic_LS` + `char_LS` | **Nature :201** — *"the large sieve inequality"*; and :204, the adversary sentence (*the two live external BV projects take SW and the large sieve as axioms*) | open |
| 9 | `vmvt` | **Pi `thm:vmvt`** (:311) + Appendix A :982–1002; **Nature :202** *"the Vinogradov mean value theorem"* | ✅ `cert_vmvt` (+ unconditional `_iff`), `Salt/Certs/Vmvt.lean` — maestro, landed 8/11 (actual class B: the decode was definitional + `pow_mul` + `ring`; the C-grade was priced for a semantic gap that did not exist) |
| 10 | `norm_kloosterman_estermann` | **Nature :203** — *"the Weil bound for Kloosterman sums"* | ✅ `Salt/Certs/Kloosterman.lean` — the paper says WEIL, the kernel holds ESTERMANN; cert derives `2√p` at odd primes to close the name gap |
| 11 | THE WALL — `twin_bar` · `no_twin_weight` · `least_k_theorem` | **Pi `neutrality_rate`** :1173 (the wall's Pi-side decl is **not** any of the three target names); **Nature :218** *"relevant Maynard-class can cross the twin gate (M₂ ≤ 2 log 2 < 2), that the least k …"* | open — **one file, three decls** |
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
