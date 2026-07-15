# Repo hygiene report — release pass (lane 3)

Read-only audit for the clone-and-continue release (`pre-outline.md` §5 item 5).
Generated on `main` @ HEAD `08baf5d` (writeup: method-stats compilation).
**Recommendations only — this pass deleted nothing and changed no history.**
New files added by this pass: `.github/workflows/ci.yml`, this report.

Scope: (a) branch inventory, (b) fresh-clone caveats, (c) repo-size / git-lfs,
(d) license-header spot-check, (e) other first-cloner trip hazards. Plus the
decision list at the end.

---

## (a) Branch inventory

Every non-`main` local branch is **fully merged into `main`** (`git branch
--merged main` lists all of them; `git branch --no-merged main` is empty).
Each has a matching `origin/*` remote mirror, so history survives even if a
local branch is deleted. "Ahead" = commits on the branch not on main; "behind"
= commits on main not on the branch.

| Branch | Last commit | Ahead / behind main | Merged? | Tip subject | Recommendation |
|---|---|---|---|---|---|
| `main` | 2026-07-15 | 0 / 0 | — | writeup: method-stats compilation | **KEEP** — canonical line |
| `explicit12` | 2026-07-11 | 0 / 306 | yes | RUNG CLOSED — `gaps_le_twelve` | **KEEP (active)** — CLAUDE.md names it the currently-active track; continuation branch |
| `twinbar` | 2026-07-15 | 0 / 15 | yes | chen THE HEADLINE — `chen_headline` | **ARCHIVE** — flagship history; tag `track/chen` then delete after release |
| `brun` | 2026-07-07 | 0 / 436 | yes | next-rung scoping (post-Brun) | **ARCHIVE** — Brun track complete; tag `track/brun` then delete |
| `bv` | 2026-07-12 | 0 / 258 | yes | tooling T1 probe: CertEval reflection | **ARCHIVE** — B–V rung complete; tag then delete |
| `largesieve` | 2026-07-11 | 0 / 292 | yes | L8.4 + W7 RUNG COMPLETE | **ARCHIVE** — LS rung complete; tag then delete |
| `maynard` | 2026-07-09 | 0 / 372 | yes | `bounded_gaps_from_eh_complete` COMPLETE | **ARCHIVE** — Maynard rung complete; tag then delete |
| `windowpnt` | 2026-07-11 | 0 / 291 | yes | PiAsymp seam | **ARCHIVE** — seam merged; tag then delete |

Rationale for ARCHIVE vs DELETE: these branches carry per-track development
history that is already in `main`, so nothing is *lost* by deletion — but the
release story ("here is where each rung was built") is cheap to preserve as an
annotated tag. Suggested pattern before deletion, per branch:
`git tag -a track/<name> <branch> -m "…"` (do the same on the remote, then
delete the branch on both). **KEEP `explicit12`** as a live branch because
CLAUDE.md still routes active work there; keeping a public track branch also
seeds the open-problems board (`pre-outline.md` §5 item 4).

---

## (b) Fresh-clone caveats

What a bare `git clone && lake build` on `main` would hit:

1. **`lake exe cache get` is mandatory before `lake build`.** A cold mathlib
   *compile* is hours; the cache download is ~7 GB (README documents this).
   The new CI workflow runs `lake exe cache get` before `lake build` for
   exactly this reason. README's Development section already spells out the
   `elan → cache get → build` sequence — accurate, no change needed.
2. **A stray untracked, unimported `.lean` file keeps appearing under
   `Salt/`.** During this audit the working tree carried
   `Salt/TwinBar/ThreeBarAsm.lean`, then moments later
   `Salt/Twelve/GapsOfLevel.lean` instead — a concurrent session is actively
   editing `main`'s working tree. In both cases the file was **untracked** and
   **imported by nothing** (`grep -rn <name> Salt/ Salt.lean` found no
   importer), so a fresh clone will not have it and builds fine. The specific
   name is a moving target; the standing caveat is "check for stray untracked
   `.lean` files under `Salt/` before cutting a release tag" — see the decision
   list.
3. **Scratch-file convention is clean.** CLAUDE.md documents
   `lake env lean Scratch.lean … (don't commit Scratch.lean)`; `.gitignore`
   correctly ignores `/Scratch.lean`, `/LintScratch.lean`,
   `/LintScratchHeadliners.lean`, and `/.lake`. The lint writes its scratch
   files at the repo root and unlinks them, and they are gitignored regardless
   — a clone stays clean. No hazard.
4. **No hardcoded absolute paths in scripts.** `grep -rE '/Users/|/home/'
   scripts/` is empty. `blueprint_lint.py` locates lake via
   `expanduser("~/.elan/bin/lake")` with a `"lake"`-on-PATH fallback — portable.
   Its only imports are stdlib (`os`, `re`, `subprocess`, `sys`), so CI needs
   no `pip install`.
5. **The lint needs a built `Salt` first.** Its axiom phases elaborate a
   `import Salt` scratch, so `lake build` must precede it. CI orders the steps
   correctly; a human running the lint from a fresh clone must build first.
6. **Certificate-generator scripts have an undocumented Python dep.**
   `scripts/cbar_cert.py` and `scripts/ss2_profile.py` both `import mpmath`
   (third-party) and `ss2_profile.py` defaults its output to
   `/tmp/ss2_profile.json` (overridable via `SS2_OUT`). These are
   **regeneration** tools for the committed certificate `.lean` files
   (`CbarCert.lean`, `SuperPanels{E,O}.lean`) — **not** part of `lake build`
   and not a clone requirement. Anyone who wants to *regenerate* a certificate
   needs `pip install mpmath`; worth a one-line note in a script header or
   README, but not a build blocker.

---

## (c) Repo-size / git-lfs

| Metric | Value |
|---|---|
| Tracked files | 402 |
| Total tracked bytes | 11.9 MB |
| `.git` directory | 51 MB |
| `.lake` (gitignored build/cache) | 9.7 GB |
| Largest tracked file | `Salt/Chen/CbarCert.lean` — 1.65 MB (21,189 machine-generated lines, 600 panels) |

Other large tracked files: `docs/blueprints/flags.md` 565 KB,
`Salt/Chen/SuperPanelsE.lean` 536 KB, `SuperPanelsO.lean` 241 KB,
`articles/maynard.pdf` 270 KB (the only sizeable **binary**).

**Recommendation: do NOT adopt git-lfs.** The tracked corpus is ~12 MB, almost
entirely text (`.lean` / `.md`) that diffs and compresses well; the certificate
files are large but are diffable source, not blobs. The single binary
(`maynard.pdf`, 270 KB) is trivial. LFS would add clone friction (smudge/clean
filters, a credential story, a lfs-enabled host) against the clone-and-continue
goal, for no size benefit. The 9.7 GB is `.lake`, which is gitignored and
reconstituted by `lake exe cache get` — not in the repo.

---

## (d) License / header spot-check

- `LICENSE` present at root: Apache-2.0 (11 KB).
- 20-file sample: **20/20** carry the header
  `Copyright (c) 2026 Jason Hickey … Released under Apache 2.0 … Authors:
  Jason Hickey, Claude`.
- Full census of tracked `Salt/**.lean` (357 files): **351 have the header, 6
  do not.**

The 6 missing (open a file, add the standard 4-line block before the first
`import`):

| File |
|---|
| `Salt/Chen/FseqAntitone.lean` |
| `Salt/Chen/HeadlineW2.lean` |
| `Salt/Chen/RosserChain.lean` |
| `Salt/Chen/Tail.lean` |
| `Salt/Maynard/GIntegrals.lean` |
| `Salt/Maynard/S2TensorClosed.lean` |

Low-risk, mechanical fix; recommend doing it before a public release for
uniformity. (Not fixed here — this pass is read-only and header edits are out
of the allowed file set.)

---

## (e) Other first-cloner trip hazards

- **Two overlapping build workflows.** `.github/workflows/lean_action_ci.yml`
  (uses `leanprover/lean-action`, then runs the blueprint lint) already builds
  on every push/PR. The new `ci.yml` is the requested hand-rolled,
  explicit-step equivalent. Running both on `main` double-builds. Consolidate —
  see decision list. (The other two existing workflows, `create-release.yml`
  and `update.yml`, are the standard mathlib template automations and are
  orthogonal — leave them.)
- **`claude.sh` runs `claude --dangerously-skip-permissions`.** Fine for the
  maintainer's unattended loop, but a first-time cloner should understand that
  flag before running it. A one-line comment in the script or README would help.
- **README GitHub-configuration section** references template setup (Actions PR
  permission, Pages source) that a forker must redo. Already documented; fine.

---

## Items needing a user decision

1. **CI consolidation.** Keep both `ci.yml` and `lean_action_ci.yml`, or fold
   one into the other? (They both build + lint on `main`.)
2. **Lint gate hardness.** `ci.yml` runs the blueprint lint with
   `continue-on-error: true` (it is currently green on `main`; the softening is
   defensive against known-manual docs drift on other tracks). Keep soft, or
   promote to a hard gate?
3. **Branch cleanup.** Approve the archive-as-tag-then-delete plan for the 6
   completed merged branches (`brun`, `bv`, `largesieve`, `maynard`, `twinbar`,
   `windowpnt`); keep `explicit12` live. Deletions are not done here.
4. **Missing Apache headers.** Add the standard header to the 6 listed files
   before release? (Mechanical.)
5. **Stray file.** An untracked, unreferenced `.lean` file under `Salt/`
   (`ThreeBarAsm.lean` / `GapsOfLevel.lean` during this audit — a concurrent
   session is churning it) — before a release tag, decide per stray whether to
   commit it (if wanted) or discard it from the working tree.
6. **git-lfs.** Confirm the recommendation to NOT adopt LFS.
7. **Generator-script deps.** Document the `mpmath` requirement (and the
   `/tmp` default output of `ss2_profile.py`) for certificate regeneration, or
   leave as-is.
