# `docs/sources/` — REFETCH RECIPE (tracked; a recipe, NEVER a copy)

**Written 2026-08-25 by the math seat, approved by the helm.** Every file in `docs/sources/` is
**gitignored** by the pre-public-release gate (`.gitignore`: `docs/sources/*.pdf`, `*.txt`) — so a
**fresh clone has none of them**, and this campaign's pen rule requires reading them *directly*.

⛔ **THIS FILE TRACKS NO COPYRIGHTED TEXT.** It carries identifiers, fetch commands, sizes and
checksums only. Nothing here re-introduces what the pre-public-release history purge exists to remove.

## Backups that already exist (verified 2026-08-25)

| copy | what it covers | verified |
|---|---|---|
| `~/Documents/seat/salt-sources-backup-2026-08-25/` | **all 16 files**, same-disk, non-git, with `SHA256SUMS.txt` | 16/16 OK vs manifest; 0 differing vs live source, both directions |
| private `seat` repo, `sources/` | `chowla-v1-textdump.txt` + its provenance stamp **only** | sha matches the stamp; `git ls-files` confirms tracked |

⚠️ The same-disk backup kills the `rm` and clone-switch loss classes. It is **not** off-machine
protection; the disposition of the two non-arXiv files is docketed for the Captain.

## A. Re-fetchable from arXiv (8 of 16)

Run from `docs/sources/`:

```sh
curl -L -o 1501.04585v4.pdf https://arxiv.org/pdf/1501.04585v4
curl -L -o 1503.05121v3.pdf https://arxiv.org/pdf/1503.05121v3
curl -L -o 1509.05422v1.pdf https://arxiv.org/pdf/1509.05422v1
curl -L -o 1509.05422v2.pdf https://arxiv.org/pdf/1509.05422v2
curl -L -o 1509.05422v3.pdf https://arxiv.org/pdf/1509.05422v3
curl -L -o 1509.05422v4.pdf https://arxiv.org/pdf/1509.05422v4
curl -L -o 1706.03749v1.pdf https://arxiv.org/pdf/1706.03749v1
curl -L -o gs9911246.pdf https://arxiv.org/pdf/math/9911246v1
```

| file | arXiv id | bytes | sha256 |
|---|---|---|---|
| `1501.04585v4.pdf` | `1501.04585v4` | 421,378 | `ec546fdf256b3b3b26b161886c5bab5efb372978ab430c0032e55919f5329277` |
| `1503.05121v3.pdf` | `1503.05121v3` | 396,063 | `8a2633b1594615fe0c340bbca01ad059be5bd66d3495bd028e7e9d2264f1e688` |
| `1509.05422v1.pdf` | `1509.05422v1` | 325,774 | `b0f3bb7ce5b24282b430adc2071140891b0f94f1d1241332edd2c055145b1956` |
| `1509.05422v2.pdf` | `1509.05422v2` | 352,743 | `468c7e1cf214dd3f36cfbf59fff7e9ce833066987eb7657d3a3a547020d682d3` |
| `1509.05422v3.pdf` | `1509.05422v3` | 379,412 | `e43dd556768d31399eadf93b485967592bc5b774c8d60a7f8d99aa08ab2fdce7` |
| `1509.05422v4.pdf` | `1509.05422v4` | 376,175 | `467329ae414b669808555fddf131be3bc07025777ae3af8ccdea6e98db6722e9` |
| `1706.03749v1.pdf` | `1706.03749v1` | 455,962 | `f0e172b6d6a89bfda96c5b4f264641509742030a7567cc9f0ae9815dccde7d06` |
| `gs9911246.pdf` | `math/9911246v1` | 288,508 | `fb6d0964943be8ac7e081fefb090be16a2c23cf25db6afe238f9cad4379a775c` |

**Titles, for identification only:**
- `1501.04585v4.pdf` — Matomaki, Radziwill — Multiplicative functions in short intervals
- `1503.05121v3.pdf` — Matomaki, Radziwill, Tao — An averaged form of Chowla's conjecture
- `1509.05422v1.pdf` — Tao — The logarithmically averaged Chowla and Elliott conjectures (v1)
- `1509.05422v2.pdf` — Tao — ... (v2)
- `1509.05422v3.pdf` — Tao — ... (v3)
- `1509.05422v4.pdf` — Tao — ... (v4)
- `1706.03749v1.pdf` — Tao, Teravainen — Odd order cases of the logarithmically averaged Chowla conjecture
- `gs9911246.pdf` — Granville, Soundararajan — Decay of mean-values of multiplicative functions

⛔ **THE CHECKSUM IS A BONUS, NOT THE TEST.** arXiv may regenerate a PDF from source, so a re-fetched
file can be the correct paper with a **different** sha256. **If the sha differs, do not assume the
fetch failed** — verify the *version stamp printed in the paper's own left margin on page 1*, e.g.
`gs9911246.pdf` carries `arXiv:math/9911246v1 [math.NT] 12 Nov 1999`. That stamp is content and
survives regeneration; the checksum is a convenience for the case where the bytes do match.
*(The `math/9911246v1` id was read off that stamp, not inferred from the filename.)*

## B. NOT re-fetchable from arXiv (2 of 16) — restore from backup

These are the only genuinely irreplaceable files. **Restore from
`~/Documents/seat/salt-sources-backup-2026-08-25/`; there is no fetch command.**

| file | bytes | sha256 | note |
|---|---|---|---|
| `montgomery-ten-lectures-cbms84.pdf` | 99,238,486 | `ef47d587e58005eb095982f6b3f2db36b8869d83bad59a437c98235045ef2272` | Montgomery — Ten Lectures on the Interface Between Analytic Number Theory and Harmonic Analysis (CBMS 84). NOT an arXiv paper. |
| `mv1974-hilbert.pdf` | 541,697 | `6b5de0c625e47c2208a83892715b0ba920bdef8e6610c13b91d4c6b9d2e47f95` | Montgomery, Vaughan — Hilbert's inequality (J. London Math. Soc., 1974). NOT an arXiv paper. |

## C. Derived / seat-owned text files (6 of 16)

`chowla-v1-textdump.txt` (+ `.PROVENANCE.md`), `hb1983-notes.md`, `jutila1977-notes.md`,
`mr_extract.md`, `mrt_extract.md`. The textdump has a tracked durable copy in the private `seat`
repo at `sources/`; the four `.md` files are **salt-authored** notes and extractions.
⚠️ `mrt_extract.md` is load-bearing: it is a page-referenced grounded extraction, and on 2026-08-25 it
was the artifact that had MRT Theorem A.1's middle term **right** while the Lean transcription had it
wrong. Do not treat it as disposable.

## C-bis. ⛔ TWO FILES THIS RECIPE MISSED IN ITS FIRST CUT (added 2026-08-25, same day)

**Found by a migration-readiness audit, not by me.** Both were missed the same way: **this recipe and
the backup were built from the files PRESENT in `docs/sources/`, never from the files the tracked
documents CITE.** The demand side was never enumerated.

| file | where | why it was missed | sha256 |
|---|---|---|---|
| `articles/maynard.pdf` | `salt/articles/` | a **SEPARATE** ignore rule — `.gitignore:27  articles/*.pdf`. The "docs/sources/*.pdf" wording this file was written from does not reach it. | `dce1a7a03004186f7116efe64c1c62f0792db973cce4208ac1bfb5050d63cda9` |
| `montgomery3.txt` | **NOT IN THE LIVE TREE** | absent from `docs/sources/` entirely; its only copies were one rescue dir and three `.claude/worktrees/` checkouts a re-clone destroys | `8af7bae87738528716b0cd747d703df6b1dcbc574ab93ccb8c370ad8d0ec01ae` |

⛔ **`montgomery3.txt` IS CITED BY LINE NUMBER IN TRACKED DOCUMENTATION.**
`docs/exploration/fulcrum-pass2.md:15-17` cites `montgomery3.txt:7576-7614`, `:7504-7537`,
`:20087-20109`, `:23113-23124`, `:22945-22948`, `:23128-23140` as **GROUNDED-source** for effective
Siegel–Walfisz, Gallagher and Linnik. **Those citations were unverifiable from the live tree.**
✅ Verified before rescuing: all four on-disk copies are byte-identical, and line 7576 of the rescued
file reads `Corollary 24.24. Let c1 be the same constant as in Corollary 24.22.` — the citations
resolve against this exact file.

**Neither is re-fetchable.** Both now live in the same-disk backup, which the math seat extended from
16 to 18 files on 2026-08-25 (`SHA256SUMS.txt`, 18/18 verified; the helm's original manifest is
preserved beside it as `SHA256SUMS.txt.orig-16`, and `EXTENDED-2026-08-25-math.md` records why).

🔑 **THE LESSON, RECORDED HERE BECAUSE THE NEXT PERSON WILL EXTEND THIS FILE:** *when you write a
recovery recipe, enumerate what the corpus CITES, not what the directory CONTAINS.* A file that is
cited and absent is invisible to any `ls`-based audit — and it is exactly the file whose loss is
silent, because the citation still looks fine.

## D. Verify a restore (with a positive control — a bare `shasum -c` proves nothing if the harness is broken)

```sh
cd ~/Documents/seat/salt-sources-backup-2026-08-25 && shasum -a 256 -c SHA256SUMS.txt
# expect: 16 lines "OK", 0 "FAILED"
# CONTROL — the checker must be able to FAIL:
#   cp SHA256SUMS.txt /tmp/s.txt && printf 'x' >> hb1983-notes.md && shasum -a 256 -c /tmp/s.txt
#   ^ must report hb1983-notes.md: FAILED   (then restore the file)
```

