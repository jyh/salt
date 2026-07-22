# Cloud Trial — Night 2 Shakedown Report

**Trial:** `salt-night-shift-trial-2` (retest after the owner amended the egress
allowlist following Night 1's NO-GO).
**Executor:** cloud night-shift agent (Opus 4.8, `claude-opus-4-8`), scheduled
routine fired 2026-07-22 ~01:26 UTC.
**Predecessor:** `docs/reports/cloud-trial-night-1.md` (NO-GO, egress policy
blocked every Lean/binary CDN).

**Verdict up front:** **NO-GO — allowlist only PARTIALLY applied.** The amendment
opened exactly **one** of the four required host classes (the GitHub asset CDN
host `objects.githubusercontent.com`), and that one is **non-functional in
isolation** because the `github.com/.../releases/download` path that must
redirect to it is still blocked. The three toolchain-critical classes — the elan
installer, the lean-lang release hosts, and the Azure mathlib cache — remain
CONNECT-403. The toolchain still cannot be installed, so Steps 3–5
(cache / build / independent checker) are unreachable exactly as in Night 1.

No Lean file was modified. Only this report is committed, to branch
`cloud-trial/night-2`. The no-main-commits law was honored absolutely.

---

## 1. Environment

| Property | Value | Δ vs Night 1 |
|---|---|---|
| OS / kernel | Linux 6.18.5 `#1 SMP PREEMPT_DYNAMIC`, x86_64 | same |
| CPU count | 4 vCPU | same |
| RAM | 15 GiB total (14 GiB free at start; 0 B swap) | same |
| Disk | `/dev/vda` 252 G size, **30 G available** at start, 20% used | same |
| Working dir | `/home/user/salt` (repo cloned fresh at container boot) | same |
| Repo HEAD | `28cbebc` (detached; `main` tip at trial time) | was `5b1f537` |
| Target toolchain | `leanprover/lean4:v4.32.0-rc1` (from `lean-toolchain`) | same |
| Git remote | `origin` via local git proxy (`127.0.0.1:41729/git/jyh/salt`) — works | same |
| Pre-provisioned toolchain | none (`~/.elan` absent; no `lean`/`lake`/`elan` on PATH or disk) | same |

Hardware, disk, and git access are **adequate and unchanged** — not the blocker,
exactly as Night 1 concluded.

---

## 2. Timeline (wall-clock, UTC)

| Time | Step | Result |
|---|---|---|
| 01:25:53 | Start; record env; read `CLAUDE.md`, `OPERATIONS.md`, Night-1 report | OK |
| 01:26:08 | **Step 2** `curl https://elan.lean-lang.org/elan-init.sh` | **403** (CONNECT policy-denied) |
| 01:26:26–29 | Four-host-class probe sweep + controls | mixed (see §3) |
| 01:26:52 | Follow-redirect test on GitHub release-download path | **403** (no redirect issued) |
| 01:26:55 | Confirm git-push path, pre-provisioned toolchain, final proxy log | OK / none / confirmed |
| 01:27 | Decisive NO-GO established → Step 6 (this report) | — |

Total elapsed to decisive NO-GO: **~1 minute** (same fast, unambiguous failure
signature as Night 1). No build ever started because no toolchain could be
installed.

---

## 3. Per-host allowlist results (the four classes)

Each class probed directly. "CONNECT-403" = the proxy rejected the TLS tunnel
(host not allowlisted); "app-403 / 404" = the tunnel succeeded and the upstream
answered (host *is* allowlisted; the code is application-level).

| # | Class | Host / path probed | Night 1 | **Night 2** | Usable? |
|---|---|---|---|---|---|
| 1 | Lean installer | `elan.lean-lang.org/elan-init.sh` | ⛔ 403 | **⛔ CONNECT-403** | no |
| 2 | Toolchain binaries | `release.lean-lang.org`, `releases.lean-lang.org` | ⛔ 403 | **⛔ CONNECT-403 (both)** | no |
| 3a | GitHub asset CDN host | `objects.githubusercontent.com` | ⛔ 403 | **✅ reachable (app-404)** | **host open** |
| 3b | GitHub release path | `github.com/.../releases/download/...` | ⛔ 403 | **⛔ app-403 (no redirect)** | no |
| 4a | mathlib cache (Azure) | `lakecache.blob.core.windows.net` | ⛔ 403 | **⛔ CONNECT-403** | no |
| 4b | mathlib cache (reservoir) | `reservoir.lean-lang.org` | ⛔ 403 | **⛔ CONNECT-403** | no |
| — | control: raw source | `raw.githubusercontent.com` | ✅ 200 | ✅ 200 | yes |
| — | control: github root | `github.com/` | ✅ (tunnel) | ✅ app-400 (tunnel) | tunnel ok |

**Proxy relay-failure log (Night 2), verbatim:**
```
2026-07-22T01:26:08 elan.lean-lang.org:443           connect_rejected
2026-07-22T01:26:26 elan.lean-lang.org:443           connect_rejected
2026-07-22T01:26:26 release.lean-lang.org:443        connect_rejected
2026-07-22T01:26:27 releases.lean-lang.org:443       connect_rejected
2026-07-22T01:26:28 lakecache.blob.core.windows.net:443  connect_rejected
2026-07-22T01:26:28 reservoir.lean-lang.org:443      connect_rejected
```
`objects.githubusercontent.com` is **absent** from the reject log — it now
connects (404 for `/` and `/health` are ordinary app responses). The
`github.com/.../releases/download` 403 is *also* absent from the reject log
because the tunnel succeeded and the block is applied at the path level (the
proxy MITMs — it carries a CA bundle, `caBundlePath`, `javaTrustStorePath` — so
it inspects the request path inside TLS and returns 403 for release-download
paths without issuing the redirect to the now-open CDN host).

### What actually changed vs Night 1
Exactly one thing: **the host `objects.githubusercontent.com` moved from
CONNECT-403 to reachable.** Everything else is byte-for-byte the same denial map.

### Why that single change is not enough
The GitHub asset CDN (`objects.githubusercontent.com`) only ever receives traffic
via a 302 redirect from `github.com/OWNER/REPO/releases/download/...`. That
redirect origin is still blocked at the path level (app-403, no `Location`
header emitted — the `-L` follow test stayed pinned at the `github.com` URL and
the 195-byte "binary" fetched was a 403 error page, not an archive). So opening
the CDN host without opening its redirect origin yields **zero** additional
downloadable bytes. elan's installer and its GitHub-asset fallback both still
dead-end, and there is no toolchain-acquisition channel the policy leaves open.

---

## 4. Step-by-step results

- **Step 2 — Toolchain install — FAILED (policy).** `elan-init.sh` → CONNECT-403.
  All mirror channels denied (lean-lang release hosts CONNECT-403; GitHub
  release-download path app-403). No elan, no `lake`, no `lean`. No
  pre-provisioned toolchain on disk.
- **Step 3 — `lake exe cache get` — NOT REACHED.** No `lake`. Independently, the
  cache CDNs (`lakecache.blob.core.windows.net`, `reservoir.lean-lang.org`) are
  still CONNECT-403, so hydration would fail even with a side-loaded toolchain.
- **Step 4 — `lake build` (~8,900 jobs) — NOT REACHED.** Blocked by Steps 2–3.
  The corpus kernel check never started.
- **Step 5 — Independent checker (`lean4checker`) — NOT REACHED.** Requires the
  toolchain (to build the checker) and built oleans (from Step 4). Per-module
  verdicts for `Salt.HB.All`, `Salt.Fulcrum.All`, `Salt.Parity.All`,
  `Salt.MR.All`, `Salt.TwinBar.All`, `Salt.Chen.All`: **all UNVERIFIED (not
  reached).** The corpus `All.lean` modules are present in the checkout; only the
  verifier — and the toolchain to build it — is missing.
- **Step 6 — This report — DONE.**
- **Step 7 — Ship to `cloud-trial/night-2` — DONE** (this file only).

---

## 5. Per-session setup cost (measured, not projected)

- **Measured Night 2:** decisive NO-GO at **t ≈ 15 s** into the run (first CONNECT
  denial at 01:26:08 vs 01:25:53 start), full failure map in **~1 min**. Compute
  cost of the environment for its intended job is again a **total loss** — no
  toolchain, so the per-session *setup* cost (elan + cache + build + checker) that
  Night 1 hoped to measure remains **UNMEASURABLE**: the run never got past
  acquisition. That number can only be captured once all four host classes are
  open.
- The only quantity Night 2 adds over Night 1 is a **narrower delta**: three host
  classes to go, not four. The cache-download cost (Night 1's projected dominant
  recurring cost, ~1–4 GB) is still entirely unmeasured because
  `lakecache.blob.core.windows.net` never opened.

---

## 6. Recommendation — NO-GO (allowlist partially applied); precise re-request

**Do not schedule salt night shifts in this cloud environment yet.** The
amendment was applied but is **incomplete** — it opened 1 of the 4 required host
classes, and that one (`objects.githubusercontent.com`) is inert without its
companion path. A night shift still cannot run `lake build`, which is the whole
job.

**To convert to GO, the outbound policy must still add (CONNECT-allow) these —
the three unfixed classes plus the companion path for the one already opened:**

1. `elan.lean-lang.org` — the elan installer. **(still blocked)**
2. `release.lean-lang.org` **and** `releases.lean-lang.org` — Lean toolchain
   binaries. **(still blocked)**
3. `github.com/.../releases/download` **path** must return its 302 (currently
   app-403) so it can redirect to `objects.githubusercontent.com`, which is
   **already open** — opening the CDN host alone accomplished nothing without
   this. **(path still blocked; host now open)**
4. `*.blob.core.windows.net` (specifically `lakecache.blob.core.windows.net`)
   and/or `reservoir.lean-lang.org` — the mathlib build cache. Without this every
   build is a multi-hour cold mathlib compile that likely won't fit a night window
   on 4 vCPU. **(still blocked — not optional)**

**Verification note for whoever amends the policy next:** the block is enforced by
a **MITM proxy that inspects host *and* path inside TLS**, not by host-CONNECT
rules alone (proven by the `github.com` path-level 403 while the `github.com`
tunnel itself succeeds). So allowlisting must cover the exact paths the toolchain
uses (`/releases/download/...`, blob container paths), not merely the hostnames —
a host-only allowlist entry for `github.com` would still 403 the download path.

**Bottom line:** Night 2 succeeded at its real job — it produced a precise,
narrowed failure map and pinpointed *why the partial fix didn't move the needle*
(CDN host opened, redirect origin still closed). One more, more careful allowlist
pass — items 1–4 above, path-aware — and Steps 2–5 can finally capture the real
build/checker timings both trials were built to measure. Retest as Night 3 after
those are added; the fast, clean failure signature means a retest costs ~1 minute
to confirm either way.

---

*Generated by the cloud night-shift trial-2 executor. No Lean sources touched; no
commit to `main`; report-only branch `cloud-trial/night-2`.*
