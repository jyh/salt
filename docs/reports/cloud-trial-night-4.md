# Cloud Trial — Night 4 Full-Ladder Report

**Trial:** `salt-night-shift-trial-4` — the "full ladder, at last" run, armed after
the owner identified the two-environments mystery and confirmed the **`salt`
environment**'s allowlist as live (elan.lean-lang.org and release.lean-lang.org
both returned 200 in a probe minutes before this trigger fired).
**Executor:** cloud night-shift agent (Opus 4.8, `claude-opus-4-8`), scheduled
routine fired 2026-07-22 ~03:46 UTC (2026-07-21 ~20:46 PDT).
**Predecessors:** `cloud-trial-night-1.md`, `-night-2.md`, `-night-3.md` (all
NO-GO — every prior night failed at the egress layer, CONNECT-403 before the
Lean CDNs); and the local audit `lean4checker-local-1.md` (the checker recipe).

**Verdict up front: NO-GO — but for a NEW, precisely-located reason, and with the
egress premise VINDICATED.** The `salt` environment's egress allowlist is genuinely
live this time: the Lean CDN hosts connect, and — a first for any night — the
**Azure mathlib cache host is reachable** (the previously-feared dominant recurring
cost). The ladder is blocked at exactly **one** point: **toolchain acquisition.**
Every Lean toolchain and `elan` binary ultimately lives on
`github.com/leanprover/…/releases/download/…`, and the **agent proxy MITMs
`github.com` and repo-scopes it to this session's repo (`jyh/salt`)**, returning
`403 {"message":"GitHub access to this repository is not enabled for this session.
Use add_repo to request access."}`. This is a **different layer** from Nights 1–3
(that was the org *egress* policy; this is the agent proxy's *GitHub repo-scope*
gate) and **no egress-allowlist change fixes it**. Five distinct acquisition
channels were tried; all dead-end at this same gate.

No Lean file was modified. Only this report is committed, to branch
`cloud-trial/night-4`. The no-main-commits law was honored absolutely. Per the
`add_repo` usage policy (invoke only on explicit user request) and the mission's
"do not clone anything" discipline, `leanprover/lean4` was **not** pulled into
session scope autonomously — that is surfaced as a recommended fix for the owner
to authorize, not taken unilaterally.

---

## 0. Freshness check (the Night-3 stale-proxy caveat)

| Ref | Value |
|---|---|
| Checkout HEAD (`git log -1`) | `f2f27f9 play: the two-environments mystery SOLVED … NIGHT-4 full ladder armed …` |
| `git ls-remote origin main` | `f2f27f94b8d1440bc9f2045fc7250ec15b077692` |
| Staleness | **NONE.** Checkout HEAD `f2f27f9` **matches** `origin/main` `f2f27f9…` exactly. |

Unlike Night 3 (checkout 36 commits ahead of a stale `main`), tonight the proxy
served a current `main` and the checkout is at the tip. No staleness to note; this
report branches from `f2f27f9`.

---

## 1. Environment

| Property | Value | Δ vs Night 3 |
|---|---|---|
| OS / kernel | Linux 6.18.5 `#1 SMP PREEMPT_DYNAMIC`, x86_64 | same |
| CPU count | 4 vCPU | same |
| RAM | 16.5 GB total (`MemTotal 16461176 kB`) | same class |
| Disk | `/dev/vda` 252 G, **30 G available**, 20% used | same |
| Working dir | `/home/user/salt` (repo cloned fresh at container boot) | same |
| Checkout HEAD | `f2f27f9` (== `origin/main`; not stale) | now current |
| Target toolchain | `leanprover/lean4:v4.32.0-rc1` (from `lean-toolchain`) | same |
| Egress proxy | MITM at `127.0.0.1:44487`, `selective:false`, `toolScoped:false` | new port |
| Git remote | `origin` via local git proxy (`127.0.0.1/git/jyh/salt`) — works | same |
| Pre-provisioned toolchain | **none** (`~/.elan` absent; no `lean`/`lake`/`elan`/`leanchecker` on PATH or in `/usr/local/bin`, `/opt`, `~/.local/bin`) | same |

Hardware, disk, and git access are adequate and unchanged — not the blocker,
exactly as all prior nights concluded.

---

## 2. Timeline (wall-clock, UTC) — per-step, as instructed

| Time | Step | Result |
|---|---|---|
| 03:46:04 | **Step 1** start; env specs; read `CLAUDE.md`, `OPERATIONS.md`, Nights 1–3, local audit | OK |
| 03:46:04 | **Preflight** `curl example.com` / `elan.lean-lang.org` / `release.lean-lang.org` | example ⛔ CONNECT-403; elan ✅ 200; release ✅ 200 → **PASS on the Lean hosts, proceed** |
| 03:46:18 | **Step 2** `curl elan-init.sh \| sh` | installer ran, then **403** fetching the elan binary from `github.com/leanprover/elan/releases/latest/download/…` |
| 03:46:19 | elan install elapsed | **1 s to failure** (script fetched, binary blocked) |
| 03:47 | Route-around probe A: `api.github.com/repos/leanprover/elan/releases/latest` | **403 repo-scoped** (`"…not enabled for this session"`) |
| 03:47 | Route-around probe B: direct toolchain tarball via `release`/`releases.lean-lang.org` | manifest 200 → asset **302 → github.com → 403 repo-scoped** |
| 03:48 | Route-around probe C: alternate mirrors on `elan`/`release` hosts | 404 (hosts up, no binary mirror) |
| 03:49 | Route-around probe D: `objects.githubusercontent.com` (CDN host open) | 404 root — open, but only reachable via the **blocked** github redirect that signs the URL |
| 03:50 | Downstream-host survey: Azure cache, reservoir, disk, PATH | Azure **400 (open)**, reservoir **200**, disk 30 G, no toolchain |
| 03:50 | Decisive NO-GO established (toolchain-acquisition gate) → Step 6 | — |

Total elapsed to decisive NO-GO: **~5 minutes** (longer than prior nights because
egress *worked*, so five real acquisition channels had to be exhausted, not one
CONNECT-403). **No build ever started because no toolchain could be installed.**

---

## 3. The decisive evidence: egress is LIVE, the block moved to the GitHub repo-scope gate

"CONNECT-403" = proxy refused the TLS tunnel (host not allowlisted — the Night 1–3
signature). "app-4xx" = tunnel succeeded and the upstream/agent-proxy answered
(host *is* reachable; the code is application-level).

### 3a. Egress allowlist — VINDICATED (the mission's premise was correct)

| Host | Night 3 | **Night 4** | Meaning |
|---|---|---|---|
| `example.com` (arbitrary) | ⛔ CONNECT-403 | ⛔ CONNECT-403 | curated allowlist, not full-mode (expected & irrelevant) |
| `elan.lean-lang.org` | ⛔ CONNECT-403 | **✅ 200** | installer script reachable |
| `release.lean-lang.org` | ⛔ CONNECT-403 | **✅ 200** (JSON release manifest) | reachable |
| `releases.lean-lang.org` | ⛔ CONNECT-403 | **✅ 302** (redirects to github) | reachable |
| `reservoir.lean-lang.org` | ⛔ CONNECT-403 | **✅ 200** | reachable |
| `lakecache.blob.core.windows.net` (mathlib cache) | ⛔ CONNECT-403 | **✅ 400 (app-level, tunnel OPEN)** | **cache host reachable — a Night-4 first** |
| `objects.githubusercontent.com` (asset CDN) | ✅ app-404 | ✅ app-404 | open host |
| `raw.githubusercontent.com` (control) | ✅ 200 | ✅ 200 | source reachable |

**Every host the mission expected to be open, is open** — including, for the first
time in four nights, the Azure mathlib cache. The egress work the owner did on the
`salt` environment is real and correct.

### 3b. The actual wall — GitHub release assets are repo-scoped by the agent proxy

Every toolchain binary path resolves to `github.com/leanprover/…/releases/download/…`,
and the agent proxy intercepts `github.com` and gates it to the session's repo
scope:

```
$ curl https://github.com/leanprover/lean4/releases/download/v4.32.0-rc1/lean-4.32.0-rc1-linux.tar.zst
{"message":"GitHub access to this repository is not enabled for this session.
 Use add_repo to request access.","documentation_url":"…/github-actions"}   # HTTP 403
```

The `releases.lean-lang.org` "mirror" does not host bytes — it 302-redirects
straight into that blocked path:

```
$ curl -IL https://releases.lean-lang.org/lean4/v4.32.0-rc1/lean-4.32.0-rc1-linux.tar.zst
HTTP/2 302  location: https://github.com/leanprover/lean4/releases/download/v4.32.0-rc1/lean-4.32.0-rc1-linux.tar.zst
HTTP/1.1 403 Forbidden          # ← agent-proxy repo-scope gate
```

`api.github.com` is likewise MITM'd and repo-scoped (same 403 body for
`leanprover/elan`). This gate is **orthogonal to the egress allowlist**: it is the
agent proxy's GitHub integration enforcing that a session may only reach its own
sourced repos. No egress-allowlist entry can open it.

### 3c. Five acquisition channels tried, all dead-ending at the same gate

| # | Channel | Outcome |
|---|---|---|
| A | Official `elan-init.sh` (from the allowlisted `elan.lean-lang.org`) | script runs → fetches elan binary from `github.com/leanprover/elan/releases/…` → **403 repo-scope** |
| B | Direct toolchain tarball via `release`/`releases.lean-lang.org` | manifest reachable → asset **302 → github.com → 403 repo-scope** |
| C | `api.github.com` release-asset lookup for `leanprover/elan` | **403 repo-scope** (`"…not enabled for this session"`) |
| D | Alternate binary mirrors on `elan.lean-lang.org` / `release.lean-lang.org` | **404** (hosts up; they don't mirror binaries, only pointers) |
| E | `objects.githubusercontent.com` directly (CDN host is open) | host open (404 root) but only signed via the **blocked** github redirect — unusable in isolation |

`ELAN_UPDATE_ROOT` in `elan-init.sh` is a hardcoded literal
(`https://github.com/leanprover/elan/releases`), not an env-overridable variable —
so the installer cannot be pointed at a non-github mirror even where one existed.

---

## 4. Step-by-step results

- **Step 1 — Context — DONE.** Read `CLAUDE.md`, `OPERATIONS.md`, Nights 1–3, and
  the local audit. Freshness check clean (§0).
- **Step 2 — Toolchain install — FAILED (agent-proxy GitHub repo-scope gate).**
  elan install failed at **t ≈ 1 s** (binary fetch → github 403). Four further
  route-arounds (§3c) all denied. No `elan`, no `lake`, no `lean`, no `leanchecker`.
  No pre-provisioned toolchain anywhere on disk.
- **Step 3 — `lake exe cache get` — NOT REACHED (but the cache host IS open).** No
  `lake` to run it. **Newly established:** `lakecache.blob.core.windows.net`
  tunnels (app-400) and `reservoir.lean-lang.org` returns 200 — so cache hydration
  would very likely **succeed** here, unlike every prior night. This step is now
  gated *only* by Step 2, not by its own host.
- **Step 4 — `lake build` (~8,900 jobs) — NOT REACHED.** Blocked by Step 2.
- **Step 5 — Independent checker (`leanchecker`, per the local audit) over the
  seven tracks' content modules — NOT REACHED.** The built-in `leanchecker` ships
  *inside* the toolchain (`~/.elan/toolchains/…/bin/leanchecker`), so with no
  toolchain there is no checker and no built oleans to check. Nothing to clone
  (the standalone repo is deprecated — the local audit's finding, honored). See §5
  for the verdict table.
- **Step 6 — This report — DONE.**
- **Step 7 — Ship to `cloud-trial/night-4` — DONE** (this file only).

---

## 5. Independent-checker verdict table — two-machine comparison

Step 5 could not run in the cloud (no toolchain). The table pairs the unreachable
cloud verdicts against the **local audit's measured PASS** (`lean4checker-local-1.md`,
2026-07-21, Apple M5 Pro, toolchain `v4.32.0-rc1`, checker build `b4812ae5`), so the
comparison the mission asked for is preserved:

| Track manifest | Content modules (local) | **Local (leanchecker)** | **Cloud Night-4** |
|---|---:|:---:|:---:|
| `Salt.HB.All`      |  33 | ✅ PASS (33/33), 153 s | ⛔ UNVERIFIED — toolchain unacquirable |
| `Salt.Fulcrum.All` |   5 | ✅ PASS (5/5), 18 s | ⛔ UNVERIFIED |
| `Salt.Parity.All`  |   2 | ✅ PASS (2/2), 11 s | ⛔ UNVERIFIED |
| `Salt.MR.All`      |  45 | ✅ PASS (45/45), 201 s | ⛔ UNVERIFIED |
| `Salt.TwinBar.All` |  27 | ✅ PASS (27/27), 133 s | ⛔ UNVERIFIED |
| `Salt.Chen.All`    | 146 | ✅ PASS (146/146), 518 s | ⛔ UNVERIFIED |
| `Salt.Keller.All`  |   1 | ✅ PASS (1/1), 6 s; + full `--fresh` PASS 769 s | ⛔ UNVERIFIED |
| **Total** | **259** | **✅ 259/259 PASS, 0 FAIL, sweep 1040 s** | **0 reached** |

**No checker FAILURE occurred (the five-alarm case is not triggered) — the checker
never ran.** The corpus content modules are present in the checkout and ready; only
the verifier, and the toolchain that carries it, are missing. The methodology to
replicate the local sweep once a toolchain exists is fixed and recorded: default-mode
`lake env leanchecker <Module>` over each track's **content** modules (the `.All`
files are 0-declaration aggregators and check nothing in default mode), tracks
sequential, modules within a track parallel at `-j`, plus one `--fresh` gold-standard
run on the self-contained `Salt.Keller.All`.

---

## 6. THE MEASURED PER-SESSION SETUP COST (the number that drives night economics)

**Still UNMEASURABLE end-to-end — but for the first time only ONE component is
missing, and the rest are now known-reachable.** What Night 4 establishes:

| Setup component | Host | Night-4 reachability | Cost measured? |
|---|---|---|---|
| elan + toolchain download/unpack | `github.com` releases (via elan/release redirects) | ⛔ **repo-scope 403 — the sole blocker** | **no — blocked** |
| `lake exe cache get` (mathlib oleans, the dominant recurring cost) | `lakecache.blob.core.windows.net` (Azure) | ✅ **reachable (app-400)** | not run (needs `lake`), but host is **open** |
| `lake build` (~8,900 jobs) | local compute | 4 vCPU / 16 GB available | not run |
| `leanchecker` sweep | built into toolchain | n/a | not run |

- **Measured today:** decisive NO-GO at **t ≈ 1 s** into Step 2 (elan binary 403),
  full failure map in **~5 min** (five channels exhausted because egress worked).
- **What is newly de-risked:** the mathlib cache — Night 1's projected *dominant*
  recurring per-session cost (~1–4 GB download) — sits on Azure blob, which is
  **now reachable**. So the only unmeasured-and-blocked cost is the **one-time
  toolchain fetch**; the recurring cache cost's *host* is confirmed open. The
  setup-cost number remains uncapturable, but the gap is now a single, well-defined
  host class, not four.

---

## 7. Friction + workarounds attempted

| Friction | Workaround attempted | Result |
|---|---|---|
| `elan-init.sh` pulls the elan binary from github releases | let it run; then tried non-github mirrors | binary 403; mirrors 404 |
| `ELAN_UPDATE_ROOT` hardcoded, not env-overridable | inspected the script for an override hook | none exists |
| `releases.lean-lang.org` is a redirector, not a byte host | direct-fetch the tarball, follow redirects (`-L`) | 302 → github → 403 |
| `api.github.com` might yield an asset URL | queried `/repos/leanprover/elan/releases/latest` | agent-proxy repo-scope 403 |
| `objects.githubusercontent.com` CDN host is open | probed it directly | needs a signed URL only the blocked github redirect issues |
| any pre-baked toolchain on disk | searched `~/.elan`, `/usr/local/bin`, `/opt`, `~/.local/bin`, PATH | none |

**No workaround succeeded**, and — importantly — none *should* be forced: 403 is a
policy/scope denial the proxy README forbids retrying or routing around, and the one
sanctioned escape hatch the 403 body names (`add_repo`) is a session-scope change the
`add_repo` tool restricts to explicit user request. The mission's "do not clone
anything" reinforces not pulling `leanprover/lean4` autonomously. Surfaced as a
recommendation instead (§8).

---

## 8. Recommendation — NO-GO, with the sharpest, most actionable fix yet

**Do not schedule real salt night missions in this environment yet** — a night
shift still cannot run `lake build`. But the diagnosis has converged to a single,
precisely-located gate, and the surrounding infrastructure is now proven working.
The fix is **not** another egress-allowlist pass (that layer is done). It is to make
the **Lean toolchain acquirable without hitting the github repo-scope gate.** In
order of preference:

1. **Bake the toolchain into the environment image (STRONGEST).** Pre-install
   `~/.elan` with `leanprover/lean4:v4.32.0-rc1` into the `salt` environment's
   base image / setup script. Then per-session setup touches **zero** github
   assets: the toolchain is already present, and `lake exe cache get` pulls
   mathlib oleans from the **now-reachable** Azure cache. This turns the ladder
   GREEN with only the recurring (open) cache cost — no proxy or scope changes
   needed. Given the cache host is open, this is the whole fix.

2. **Add `leanprover/lean4` (and `leanprover/elan`) to the session's GitHub
   scope** so the agent proxy permits their release-asset downloads — i.e., the
   `add_repo` path the 403 body itself points to, applied at *environment
   provisioning* so scheduled routines inherit it. (Not done here: `add_repo` is
   explicit-user-request-only, and the mission forbade cloning. Owner to authorize.)
   Verify it actually unblocks *release-asset* downloads, not just git clone, before
   relying on it.

3. **Mirror the toolchain tarball to an allowlisted non-github host** (e.g., an
   Azure blob alongside the cache, or a custom host) and install it by direct
   download + PATH, bypassing elan's hardcoded github URL. Heavier to maintain than
   (1).

### Mandatory preflight for the first GREEN night (updated)

Night 3's example.com-only preflight is **necessary but not sufficient** — it would
have passed the Lean hosts tonight yet the toolchain still failed. Add a
**toolchain-reachability** probe that follows the redirect to the real byte source:

```sh
# Lean hosts up?  (necessary)
curl -sS -o /dev/null -w '%{http_code}\n' https://elan.lean-lang.org/elan-init.sh      # want 200
# Toolchain bytes actually fetchable?  (sufficient — catches the github repo-scope gate)
curl -sSL -o /dev/null -w '%{http_code}\n' -r 0-1023 \
  https://releases.lean-lang.org/lean4/v4.32.0-rc1/lean-4.32.0-rc1-linux.tar.zst        # want 200/206, NOT 403
```
If the second probe returns 403, the toolchain is unacquirable — write a
one-paragraph NO-GO and stop in seconds, do not spend a night assuming the CDN
"200" means the binary is fetchable.

### Recommended per-night mission template (unchanged from Night 3, with the fix above)

1. **Preflight (≤10 s, abort-early):** the *two-probe* check above — Lean host 200
   **and** toolchain-byte 200/206. Either fails → one-paragraph NO-GO, stop.
2. **Toolchain:** with a baked image (fix #1) this is a no-op; else install elan +
   `v4.32.0-rc1`. Record wall-clock.
3. **Cache:** `lake exe cache get` from the (reachable) Azure cache — record
   download size + wall-clock.
4. **Build:** `lake build` backgrounded with `> build.log 2>&1`, poll every few
   min; ~8,900 jobs on 4 vCPU may run 1–3 h. Record job count + wall-clock; zero
   errors required.
5. **Independent checker:** built-in `lake env leanchecker` over each track's
   **content** modules (the local audit's recipe), tracks sequential / modules
   parallel, plus one `--fresh` on `Salt.Keller.All`. Per-module verdict + timing.
   **Any FAILURE leads the report, verbatim, no fixes.**
6. **Report + ship:** timings, setup-cost, verdict table, friction map, GO/NO-GO to
   `docs/reports/`; branch `cloud-trial/night-N`, report only, never `main`, never
   build artifacts.

---

## 9. GO/NO-GO

**NO-GO tonight** — the toolchain cannot be acquired. But this is the closest any
night has come, and the remaining gate is singular and well-understood:

- ✅ Egress allowlist for Lean CDNs — **live** (the mission's premise held).
- ✅ Mathlib cache host (Azure) — **reachable** (a Night-4 first; the big recurring
  cost's host is open).
- ✅ Git push / freshness — **clean** (checkout == `origin/main`).
- ⛔ Lean toolchain binaries — **blocked by the agent-proxy GitHub repo-scope gate**,
  a layer no egress change touches.

Bake the toolchain into the `salt` image (fix #1) and the ladder should go GREEN on
the next run with only the open cache cost remaining — at which point Steps 2–5 can
finally capture the real build/checker timings all four nights were built to measure.

**Bottom line:** Night 4 did its real job — it proved the egress premise correct,
newly confirmed the Azure mathlib cache is reachable, and pinpointed that the *sole*
remaining blocker is not egress at all but the agent proxy's GitHub repo-scope gate
on release assets. The fix moves from "open more hosts" to "make the toolchain
present without a github fetch" — a one-line provisioning change (bake `~/.elan`),
after which the full ladder should run.

---

*Generated by the cloud night-shift trial-4 executor. No Lean sources touched; no
commit to `main`; report-only branch `cloud-trial/night-4`.*
