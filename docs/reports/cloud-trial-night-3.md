# Cloud Trial — Night 3 Shakedown Report

**Trial:** `salt-night-shift-trial-3` (`trig_0125eJjYWXMeUHCb49N9mTv8`) — the
"definitive full-ladder shakedown" armed after the owner reported switching the
environment's network access to **FULL (any domain)**.
**Executor:** cloud night-shift agent (Opus 4.8, `claude-opus-4-8`), scheduled
routine fired 2026-07-22 ~02:11 UTC (2026-07-21 ~19:11 PDT).
**Predecessors:** `cloud-trial-night-1.md` (NO-GO, every Lean/binary CDN blocked)
and `cloud-trial-night-2.md` (NO-GO, allowlist only *partially* applied — 1 of 4
host classes opened).

**Verdict up front:** **NO-GO — FULL MODE DID NOT TAKE EFFECT in this session's
environment.** The owner flipped the "any domain" setting (recorded in
`pilot.md`: *"FULL MODE FLIPPED (JYH: 'yes, flipped')"*, 2026-07-21 18:52 PDT),
but the container this routine booted into is running the **byte-for-byte
identical restrictive Custom allowlist from Night 2**. The proof is unambiguous
and new to Night 3: **arbitrary, unrelated domains — `example.com`,
`google.com`, `cloudflare.com`, `wikipedia.org` — are all CONNECT-403.** A true
any-domain policy allows those; this policy denies them. So the full ladder
(toolchain → cache → build → lean4checker over all seven manifests) is **as
unreachable as Nights 1–2**: no elan, no `lake`, no `lean`.

No Lean file was modified. Only this report is committed, to branch
`cloud-trial/night-3`. The no-main-commits law was honored absolutely.

---

## 1. Environment

| Property | Value | Δ vs Night 2 |
|---|---|---|
| OS / kernel | Linux 6.18.5 `#1 SMP PREEMPT_DYNAMIC`, x86_64 | same |
| CPU count | 4 vCPU | same |
| RAM | 15 GiB total (14 GiB free at start; 0 B swap) | same |
| Disk | `/dev/vda` 252 G size, **30 G available** at start, 20% used | same |
| Working dir | `/home/user/salt` (repo cloned fresh at container boot) | same |
| Checkout HEAD | `f4dc7fd` (detached; 36 commits **ahead** of stale `main`/`origin/main` `5b1f537`) | advanced |
| Target toolchain | `leanprover/lean4:v4.32.0-rc1` (from `lean-toolchain`) | same |
| Git remote | `origin` via local git proxy (`127.0.0.1:41729/git/jyh/salt`) — works | same |
| Egress proxy | MITM at `127.0.0.1:36411`, `selective:false`, same `noProxy` package set | same |
| Pre-provisioned toolchain | none (`~/.elan` absent; no `lean`/`lake`/`elan` on PATH or disk) | same |

Hardware, disk, and git access are **adequate and unchanged** — not the blocker,
exactly as Nights 1–2 concluded. Note the checkout is at `f4dc7fd` (which already
contains the Night-1 and Night-2 reports and the "night-3 armed" commit); the
`main` ref served by the proxy is stale at `5b1f537`, 36 commits behind. This
report branches from `f4dc7fd`, not `main`, so the prior reports are preserved.

---

## 2. Timeline (wall-clock, UTC)

| Time | Step | Result |
|---|---|---|
| 02:10:58 | Start; record env specs; read `CLAUDE.md`, `OPERATIONS.md`, Night-1 + Night-2 reports | OK |
| 02:11:07 | **Step 2** `curl https://elan.lean-lang.org/elan-init.sh -sSf` | **403** (CONNECT policy-denied) |
| 02:11:29 | Four-host-class probe sweep + controls | identical to Night 2 (see §3) |
| 02:11:53 | **Arbitrary-domain sweep** (google/cloudflare/wikipedia/example.com) | **all CONNECT-403** → FULL not applied |
| 02:11:xx | Redirect-follow test on release path; git-push path; pre-provisioned-toolchain check; fresh reject log | app-403 / OK / none / confirmed |
| 02:12 | Decisive NO-GO established (full-mode-not-applied) → Step 6 (this report) | — |

Total elapsed to decisive NO-GO: **~1 minute** (same fast, unambiguous failure
signature as Nights 1–2). No build ever started because no toolchain could be
installed.

---

## 3. The decisive evidence: this is NOT any-domain mode

Every probe below was run this session. "CONNECT-403" = the proxy refused the TLS
tunnel (host not allowlisted). "app-4xx" = the tunnel succeeded and the upstream
answered (host *is* allowlisted).

### 3a. The four toolchain host classes — identical to Night 2

| # | Class | Host / path | Night 2 | **Night 3** | Usable? |
|---|---|---|---|---|---|
| 1 | Lean installer | `elan.lean-lang.org/elan-init.sh` | ⛔ CONNECT-403 | **⛔ CONNECT-403** | no |
| 2a | Toolchain binaries | `release.lean-lang.org` | ⛔ CONNECT-403 | **⛔ CONNECT-403** | no |
| 2b | Toolchain binaries | `releases.lean-lang.org` | ⛔ CONNECT-403 | **⛔ CONNECT-403** | no |
| 3a | GitHub asset CDN host | `objects.githubusercontent.com` | ✅ app-404 | **✅ app-404** | host open |
| 3b | GitHub release path | `github.com/leanprover/lean4/releases/download/…` | ⛔ app-403 | **⛔ app-403, `num_redirects=0`** | no |
| 4a | mathlib cache (Azure) | `lakecache.blob.core.windows.net` | ⛔ CONNECT-403 | **⛔ CONNECT-403** | no |
| 4b | mathlib cache (reservoir) | `reservoir.lean-lang.org` | ⛔ CONNECT-403 | **⛔ CONNECT-403** | no |

Zero net change from Night 2 in the toolchain map. The one host Night 2 opened
(`objects.githubusercontent.com`) is still inert without its redirect origin
(the `-L` follow test issued **0 redirects** and returned the 403 error body).

### 3b. The NEW Night-3 datapoint — arbitrary domains are blocked

| Domain (unrelated to Lean) | Result |
|---|---|
| `example.com` | **⛔ CONNECT-403** |
| `www.google.com` | **⛔ CONNECT-403** |
| `cloudflare.com` | **⛔ CONNECT-403** |
| `www.wikipedia.org` | **⛔ CONNECT-403** |

**This is the smoking gun.** Under a genuine "FULL / any domain" egress policy,
these four would all connect. They do not. Therefore the environment this
routine is running in is **still governed by the Night-2 Custom allowlist**, not
the FULL policy the owner toggled. The only hosts that work are the exact
Night-2 set:

| Class | Host | Status |
|---|---|---|
| Git remote (session proxy) | `127.0.0.1:41729/git/jyh/salt` | ✅ works |
| Raw source | `raw.githubusercontent.com` | ✅ 200 |
| Package registries (`noProxy`) | pypi, crates (app-403 root, but tunnel open) | ✅ allowlisted |
| GitHub asset CDN host | `objects.githubusercontent.com` | ✅ app-404 |
| **Everything else** (Lean CDNs, Azure cache, and *all arbitrary domains*) | — | ⛔ CONNECT-403 |

**Proxy reject log (verbatim, this session):**
```
2026-07-22T02:11:07 elan.lean-lang.org:443              connect_rejected
2026-07-22T02:11:30 elan.lean-lang.org:443              connect_rejected
2026-07-22T02:11:30 release.lean-lang.org:443           connect_rejected
2026-07-22T02:11:31 releases.lean-lang.org:443          connect_rejected
2026-07-22T02:11:32 lakecache.blob.core.windows.net:443 connect_rejected
2026-07-22T02:11:32 reservoir.lean-lang.org:443         connect_rejected
2026-07-22T02:11:33 example.com:443                     connect_rejected
2026-07-22T02:11:53 www.google.com:443                  connect_rejected
```

### 3c. Root cause — the setting didn't propagate to this container

The owner flipped the FULL switch in the UI at **18:52 PDT**; this routine's
container booted and fired at **~19:11 PDT** yet inherited the **old** policy.
The near-certain explanation: **the network policy is bound to the environment /
container at provisioning time, and a scheduled routine firing into an existing
(or old-snapshot) environment carries the policy that was in effect when that
environment was created — not the live UI value.** Toggling the setting saved it
for *future* environments but did not rewrite the running one. This is consistent
with the `selective:false` proxy config being identical across all three nights.

---

## 4. Step-by-step results

- **Step 2 — Toolchain install — FAILED (policy).** `elan-init.sh` → CONNECT-403.
  All mirror channels denied (lean-lang release hosts CONNECT-403; GitHub
  release-download path app-403 with no redirect). No elan, no `lake`, no `lean`.
  No pre-provisioned toolchain on disk. Per the four-host + arbitrary-domain
  probe, **jumped to Step 6 with NO-GO (full-mode-not-applied)** exactly as the
  mission's contingency instructs.
- **Step 3 — `lake exe cache get` — NOT REACHED.** No `lake`; and the cache CDNs
  (`lakecache.blob.core.windows.net`, `reservoir.lean-lang.org`) are CONNECT-403.
- **Step 4 — `lake build` (~8,900 jobs) — NOT REACHED.** Blocked by Steps 2–3.
- **Step 5 — Independent checker (`lean4checker`) over the seven manifests — NOT
  REACHED.** Requires the toolchain (to build the checker) and built oleans. The
  clone origin (github.com) tunnels but its release assets are blocked; no
  toolchain to build it regardless. Per-module verdicts for `Salt.HB.All`,
  `Salt.Fulcrum.All`, `Salt.Parity.All`, `Salt.MR.All`, `Salt.TwinBar.All`,
  `Salt.Chen.All`, **and `Salt.Keller.All`: all UNVERIFIED (not reached).**
- **Step 6 — This report — DONE.**
- **Step 7 — Ship to `cloud-trial/night-3` — DONE** (this file only).

### Checker verdict table (Step 5 target — none reachable)

| Manifest | lean4checker verdict | Timing |
|---|---|---|
| `Salt.HB.All` | UNVERIFIED (toolchain absent) | — |
| `Salt.Fulcrum.All` | UNVERIFIED (toolchain absent) | — |
| `Salt.Parity.All` | UNVERIFIED (toolchain absent) | — |
| `Salt.MR.All` | UNVERIFIED (toolchain absent) | — |
| `Salt.TwinBar.All` | UNVERIFIED (toolchain absent) | — |
| `Salt.Chen.All` | UNVERIFIED (toolchain absent) | — |
| `Salt.Keller.All` | UNVERIFIED (toolchain absent) | — |

No checker FAILURE (the five-alarm case) occurred — the checker never ran. The
corpus `All.lean` manifests are present in the checkout and ready; only the
verifier and the toolchain to build it are missing.

---

## 5. Per-session setup cost — still UNMEASURABLE

The measured, honest number remains what Nights 1–2 reported: **the environment
reaches a decisive NO-GO at t ≈ 9–15 s** (first CONNECT denial at 02:11:07 vs
02:10:58 start), full failure map in **~1 minute**. The real per-session setup
cost this trial was built to measure — elan + toolchain + `cache get` + build +
lean4checker wall-clock — **remains unmeasurable**, because the run never got
past acquisition for the third consecutive night. That number can only be
captured once the FULL policy is actually live in the running container (or all
four host classes are allowlisted path-aware).

---

## 6. Recommendation — NO-GO (full-mode-not-applied); a different, sharper fix

**Do not schedule real salt night missions in this cloud environment yet.** The
FULL switch was toggled but **did not reach this session's container** — the
egress map is identical to Night 2 down to the byte, and arbitrary domains prove
it is not any-domain mode. A night shift still cannot run `lake build`, which is
the whole job.

Night 3's finding is *categorically different* from Nights 1–2 and changes the
ask. Nights 1–2 asked for allowlist *entries*. Night 3 shows the owner already
set the right value (**FULL**) — **it just isn't taking effect in the running
environment.** So the fix is not "add more hosts"; it is **make the setting
apply:**

1. **Re-provision / recreate the environment after flipping FULL**, then fire a
   fresh routine into the *new* environment. Verify the switch propagated with a
   one-line probe **before** committing a whole night to a build:
   `curl -sS -o /dev/null -w '%{http_code}\n' https://example.com/` — under FULL
   this returns `200/301`; under the current policy it is CONNECT-403. If it
   still fails, the setting did not propagate and the night is a no-op — abort in
   ~5 s instead of assuming.
2. Confirm the scheduled routine (`trig_0125eJjYWXMeUHCb49N9mTv8`) is bound to
   the environment that carries the FULL policy — a routine pinned to an old
   environment snapshot will keep booting the old allowlist no matter what the UI
   shows.
3. **Fallback if FULL is not desired long-term:** the path-aware Custom allowlist
   from Nights 1–2 still stands (`elan.lean-lang.org`;
   `release.lean-lang.org` + `releases.lean-lang.org`; the
   `github.com/.../releases/download` **path** so it can 302 to the already-open
   `objects.githubusercontent.com`; and `lakecache.blob.core.windows.net` /
   `reservoir.lean-lang.org` for the mathlib cache). A host-only rule will not
   work — the proxy MITMs and inspects the path inside TLS.

### GO/NO-GO for real night missions

**NO-GO tonight.** But the gate is now a *provisioning* gate, not a *policy-design*
gate — the owner has already chosen the correct value. Once probe #1 above returns
200 in a live container, the environment should go GO immediately and Steps 2–5
can finally capture real timings.

### Recommended per-night mission template (for the first GREEN night)

1. **Preflight (≤10 s, abort-early):** `curl example.com` → expect 200; `curl
   elan.lean-lang.org/elan-init.sh` head → expect 200. If either fails,
   write a one-paragraph NO-GO report to `docs/reports/` and stop. **Never spend
   a night on an environment that fails preflight.**
2. **Toolchain (background, log-redirected):** install elan; `elan toolchain
   install` the pinned `v4.32.0-rc1`. Record wall-clock.
3. **Cache:** `lake exe cache get` — record download size + wall-clock (expected
   dominant recurring cost; ~1–4 GB).
4. **Build:** `lake build` in background with `> build.log 2>&1`, poll every few
   min; ~8,900 jobs on 4 vCPU may run 1–3 h. Record job count + wall-clock; zero
   errors required.
5. **Independent checker:** clone `lean4checker`, checkout the tag matching
   `lean-toolchain`, `lake build` it, run over all seven manifests
   (`Salt.{HB,Fulcrum,Parity,MR,TwinBar,Chen,Keller}.All`). Per-module verdict +
   timing. **Any checker FAILURE leads the report, verbatim, no fixes.**
6. **Report + ship:** timings, setup-cost, verdict table, friction map, GO/NO-GO
   to `docs/reports/`; branch `cloud-trial/night-N`, report only, never `main`,
   never build artifacts, never the checker clone.

**Bottom line:** Night 3 did its real job — it caught that the FULL setting the
owner flipped is **not live in the running container**, proven by arbitrary
domains being CONNECT-403 (a test neither prior night ran). The fix moves from
"design the allowlist" to "re-provision so the chosen policy applies," plus a
mandatory ≤10-second preflight so no future night is wasted assuming a switch
took effect. Retest as Night 4 in a freshly-provisioned FULL environment; the
preflight makes confirming either outcome a ~5-second cost.

---

*Generated by the cloud night-shift trial-3 executor. No Lean sources touched; no
commit to `main`; report-only branch `cloud-trial/night-3`.*
