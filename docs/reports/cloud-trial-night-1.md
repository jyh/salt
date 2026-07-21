# Cloud Trial — Night 1 Shakedown Report

**Trial:** `salt-night-shift-trial-1` (per `docs/OPERATIONS.md`, the hybrid-seat
continuity-layer trial).
**Executor:** cloud night-shift agent (Opus 4.8), scheduled routine fired
2026-07-21 21:06 UTC.
**Verdict up front:** **NO-GO** for salt night shifts in this cloud environment
*as its egress policy is currently configured*. The environment cannot install
the Lean toolchain, hydrate the mathlib build cache, or fetch the independent
checker — every Lean/binary distribution CDN is blocked by the outbound network
policy. Source hosts and the git remote work fine, so the blocker is narrow,
identified precisely, and fixable by an allowlist change (see Recommendation).

No Lean file was modified. Only this report is committed, to branch
`cloud-trial/night-1`. The no-main-commits law was honored absolutely.

---

## 1. Environment

| Property | Value |
|---|---|
| OS / kernel | Linux 6.18.5 `#1 SMP PREEMPT_DYNAMIC`, x86_64 |
| CPU count | 4 vCPU |
| RAM | 15 GiB total (14 GiB free at start; 0 B swap) |
| Disk | `/dev/vda` 252 G size, 30 G available at start, 20% used |
| Working dir | `/home/user/salt` (repo cloned fresh at container boot) |
| Repo HEAD | `5b1f537` on `main` |
| Target toolchain | `leanprover/lean4:v4.32.0-rc1` (from `lean-toolchain`) |
| Git remote | `origin` via local git proxy (`127.0.0.1:41729/git/jyh/salt`) — works |
| Git identity | `Claude <noreply@anthropic.com>` (pre-configured) |

Hardware and disk are **adequate** for a mathlib build (4c/15G is tight but
workable; disk had 30 G free). Hardware is not the blocker.

---

## 2. Timeline (wall-clock, UTC)

The entire run was consumed by toolchain-acquisition attempts; no build ever
started because no toolchain could be installed.

| Time | Step | Result |
|---|---|---|
| 21:06:43 | Start; record env; read `CLAUDE.md` + `docs/OPERATIONS.md` | OK |
| 21:06:57 | **Step 2** `curl elan-init.sh` | **403** (`elan.lean-lang.org` policy-denied) |
| 21:07:19 | Probe `release.lean-lang.org`, `releases.lean-lang.org` | **403** both |
| 21:07:40 | Probe elan + Lean toolchain via **GitHub release assets** | **403** both |
| 21:08:10 | Probe generic GitHub release asset (ripgrep) + `raw.githubusercontent.com` | asset **403**, raw **200** |
| 21:08:43 | Probe mathlib cache CDNs (Azure blob, reservoir, gh-pages) | **403** all |
| 21:08:43 | End of acquisition attempts → NO-GO established | — |

Total elapsed to decisive NO-GO: **~2 minutes.** The failure is fast and
unambiguous, which is itself a good property for a trial.

---

## 3. Step-by-step results

### Step 2 — Toolchain install — **FAILED (policy)**
`curl https://elan.lean-lang.org/elan-init.sh` → the proxy answered **403 to
CONNECT** for `elan.lean-lang.org` (recorded in
`$HTTPS_PROXY/__agentproxy/status` → `recentRelayFailures`). Per the proxy
README, 403/407 are organization egress-policy denials that must **not** be
retried or routed around. No elan, no `lake`, no `lean`. No pre-installed
toolchain exists (`~/.elan` absent; no `lean`/`lake`/`elan` on `PATH` or on
disk).

Mirror attempts (all denied):
- `release.lean-lang.org`, `releases.lean-lang.org` (elan's default toolchain
  source) → 403.
- GitHub release assets for both elan (`leanprover/elan`) and the Lean
  toolchain (`leanprover/lean4` `v4.32.0-rc1` `.tar.zst`) → **403**. The CONNECT
  to `github.com` succeeds (`200 Connection Established`) but GitHub/asset CDN
  returns 403; a control download of an unrelated well-known asset
  (`BurntSushi/ripgrep`) **also** 403s, proving GitHub **release-asset / CDN
  downloads are categorically blocked**, not asset-specific.
- `raw.githubusercontent.com` returns **200** — source text is reachable, only
  binary release/CDN paths are denied.

### Step 3 — `lake exe cache get` — **NOT REACHED / would fail**
Cannot run without `lake`. Independently, the mathlib cache CDNs are blocked
too: `*.blob.core.windows.net` (Azure), `reservoir.lean-lang.org`, and
`leanprover-community.github.io` all → **403**. So even if a toolchain were
side-loaded, cache hydration would fail and the build would fall back to a
multi-hour cold compile of mathlib — likely beyond a night-shift budget on 4
vCPU even if it were allowed.

### Step 4 — `lake build` — **NOT REACHED**
Blocked by Steps 2–3. The ~9,400-job corpus kernel check never started.

### Step 5 — Independent checker (`lean4checker`) — **NOT REACHED**
Requires the toolchain (to `lake build` the checker) and built oleans (from
Step 4). Cloning the checker source would itself hit the same GitHub-asset
wall for any binary deps, though the source clone via git would work. Per-module
verdicts for `Salt.HB.All`, `Salt.Fulcrum.All`, `Salt.Parity.All`, `Salt.MR.All`,
`Salt.TwinBar.All`, `Salt.Chen.All`: **all UNVERIFIED (not reached).** All six
`All.lean` modules are present in the checkout, so the corpus is in place and
ready — only the verifier is missing.

### Step 6 — This report — **DONE**
### Step 7 — Ship to `cloud-trial/night-1` — **DONE** (this file only)

---

## 4. Friction map (root cause)

The environment's egress policy is **source-friendly, binary-hostile**:

| Class | Hosts | Status |
|---|---|---|
| Git remote (session proxy) | `127.0.0.1:41729/git/jyh/salt` | ✅ works |
| Raw source | `raw.githubusercontent.com` | ✅ 200 |
| Package registries (in `noProxy`) | npm, jsr, pypi, crates, go proxy | ✅ (allowlisted) |
| Lean installer | `elan.lean-lang.org` | ⛔ 403 |
| Lean toolchain binaries | `release.lean-lang.org`, `releases.lean-lang.org` | ⛔ 403 |
| GitHub release assets / CDN | `github.com/.../releases/download`, `objects.githubusercontent.com` | ⛔ 403 (categorical) |
| mathlib build cache | `*.blob.core.windows.net`, `reservoir.lean-lang.org`, `leanprover-community.github.io` | ⛔ 403 |

**Single root cause:** the outbound network policy for this session does not
allow the binary-distribution CDNs that the Lean/mathlib toolchain requires.
Nothing about the hardware, disk, git access, or repo state is at fault, and no
workaround exists from inside the session — 403/407 are policy denials that the
proxy README explicitly forbids retrying or circumventing. There is no other
Lean-toolchain acquisition channel that the policy leaves open.

**No workarounds were available.** (Attempted and exhausted: official installer,
both lean-lang release hosts, GitHub-release mirrors for elan and for the
toolchain, and a check for any pre-provisioned toolchain — 6+ distinct channels,
all denied or absent.)

---

## 5. Recommendation — NO-GO, with a concrete fix

**Do not schedule salt night shifts in this cloud environment until its egress
allowlist is amended.** The continuity-layer plan in `OPERATIONS.md`
("cloud = the continuity layer … boot from the repo's own book and push night
branches") is sound in principle and the git-push path is proven working — but
it is **inoperable** while the toolchain CDNs are blocked. A night shift that
cannot run `lake build` cannot verify a single proof, which is the whole job.

**To turn this into a GO,** the environment's network policy needs the following
hosts added to the outbound allowlist (or the `noProxy` set):

1. `elan.lean-lang.org` — the elan installer.
2. `release.lean-lang.org` and `releases.lean-lang.org` — Lean toolchain binaries.
3. GitHub release-asset delivery: `objects.githubusercontent.com` (and the
   `github.com/.../releases/download` path) — fallback for elan/toolchain and
   required to fetch/build `lean4checker`.
4. The mathlib cache CDN — `*.blob.core.windows.net` (currently
   `lakecache.blob.core.windows.net`) and/or `reservoir.lean-lang.org` — without
   this, every build is a cold multi-hour mathlib compile.

Item 4 is the difference between a ~few-minute warm build and a multi-hour cold
one; on a 4-vCPU box a cold mathlib compile may not fit a night window at all,
so the cache allowlist is **not optional** for practical night shifts.

### Per-session setup cost (quantified, as far as measurable)

- **Measured today:** elan install / toolchain / cache / build all **fail at
  t≈14 s** into the run (first CONNECT denial), i.e. the environment is
  unusable for ~$0 of compute but 100% of the mission — the cost today is a
  total loss, not a slow start.
- **Projected once allowlisted** (from known salt/mathlib norms; *not* measured
  here because the toolchain could not be installed):
  - elan + toolchain download/unpack: ~1–3 min.
  - `lake exe cache get` (warm mathlib oleans): typically ~1–4 GB download,
    ~2–6 min on a good link — the dominant recurring per-session cost because
    the container is ephemeral (fresh clone each boot, no warm cache carried
    over, unlike the "local = cockpit … warm build cache" seat).
  - `lake build` incremental over cached mathlib: minutes if the corpus oleans
    are also cached, else the full ~9,400-job kernel check.
  - `lean4checker` clone + build: one-time ~few min per session.
  - **Estimated floor: ~10–20 min of setup per cold cloud session** before any
    proof work begins, dominated by cache download — versus near-zero for the
    local cockpit seat with its persistent cache. This asymmetry argues for
    keeping cloud strictly as the *announced-drain / travel* continuity layer,
    not a daily driver, consistent with the "not cloud-by-default" ratification.

**Bottom line:** the shakedown succeeded at its real job — it produced a precise
failure map. The environment is one allowlist change away from viable; retest
after items 1–4 are added, at which point Steps 2–5 should be re-run to capture
the real build/checker timings this trial could not.

---

*Generated by the cloud night-shift trial executor. No Lean sources touched; no
commit to `main`; report-only branch `cloud-trial/night-1`.*
