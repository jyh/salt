#!/bin/bash
# replay_openai_seven_eighths.sh — rebuild OpenAI's Lean proof that every Dirichlet L-function is
# non-zero for Re s > 7/8, from their pinned source, and replay its whole environment through the
# Lean kernel with leanchecker.
#
# Source: github.com/openai/math at 1581d4cbdd69a0faf34b2089614fe2a814316a6a, directory lean/.
# Theorem: OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
#          (module OAI.NumberTheory.DirichletL.Nonvanishing; challenge statement in
#          lean/ComparatorChallenges/DirichletSevenEighths.lean).
# The same statement is restated in this repository as Salt.TwinBar.DirichletSevenEighths.
#
# Steps, each printing what it did:
#   1  partial clone of lean/ at the pinned sha
#   2  `lake exe cache get`: resolves the dependencies, applies the 11 patches the lakefile applies
#      before resolution, and fetches mathlib's compiled files from the community cache
#   3  the 12 patches the lakefile applies only under `lake update`, applied with `git apply` and
#      checked with `git apply --check --reverse` (what its post_update hook does); the manifest is
#      not changed
#   4  build the solution module
#   5  check the challenge statement against the theorem, and print its axioms, beside a planted
#      `sorry` that must print `sorryAx`
#   6  CONTROL: a module holding `math78_bad : False := True.intro`, added with the kernel's check
#      skipped; `leanchecker --fresh` on it must FAIL
#   7  `leanchecker --fresh` on the solution module: every imported declaration replayed into an
#      empty environment through the kernel; it stops at the first one the kernel rejects
#
# Measured 2026-10-22 on an Apple M-series machine with 64 GB: step 4 took 56 min (7,061 jobs) at
# LEAN_NUM_THREADS=4; step 7 replayed 561,427 constants in 614 s with a 7.3 GB peak; the tree
# reached 21 GB. Mathlib's compiled files in step 2 are upstream's; step 7 is what re-checks them.
# Not checked by this script: the content of the 23 patches; the statement match is by
# elaboration (step 5), not by OpenAI's comparator; nothing here reads the preprint.
#
# Usage: scripts/replay_openai_seven_eighths.sh WORKDIR [--dry-run]
# Environment: LEAN_NUM_THREADS (default 4). SALTBUILD=path/to/saltbuild.sh routes every build
# through that wrapper; FLEET_FLOCK=path/to/lockfile holds that flock around the bare `lake`
# commands (steps 2 and 6–7). Without them, plain `lake` is used.
# Exit: 0 the replay passed and the control failed · 1 a step failed · 3 the control PASSED (the
# replay proves nothing then).
set -u
SHA=1581d4cbdd69a0faf34b2089614fe2a814316a6a
MOD=OAI.NumberTheory.DirichletL.Nonvanishing
THM=OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
POST_PATCHES="fixed-point-theorems PrimeNumberTheoremAnd Zeta3Irrational rellich-kondrachov carleson StrongPNT AbsorptionCutoff AINTLIB ClassFieldTheory schoenflies-lean SphereEversion gromov"
WORK="${1:?usage: $0 WORKDIR [--dry-run]}"
DRY=0; [ "${2:-}" = "--dry-run" ] && DRY=1
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
LAKE="$(command -v lake || echo "$HOME/.elan/bin/lake")"

say() { printf '== %s\n' "$*"; }
run() { # run CMD...: print it; execute unless --dry-run; stop the script on failure
  printf '$ %s\n' "$*"
  [ "$DRY" = 1 ] && return 0
  "$@" || { echo "FAILED (rc $?): $*"; exit 1; }
}
bare() { # a bare lake command, under FLEET_FLOCK when it is set
  if [ -n "${FLEET_FLOCK:-}" ]; then run flock -w 14400 "$FLEET_FLOCK" "$LAKE" "$@"; else run "$LAKE" "$@"; fi
}
build() { # build a module or audit a file, through SALTBUILD when it is set
  if [ -n "${SALTBUILD:-}" ]; then
    printf '$ %s %s\n' "$SALTBUILD" "$1"; [ "$DRY" = 1 ] && return 0
    "$SALTBUILD" "$1" > "$WORK/build-$2.log" 2>&1; local rc=$?
    grep -a 'saltbuild EXIT=' "$WORK/build-$2.log"
    [ "$rc" = 0 ] || { echo "FAILED: build $1 (log $WORK/build-$2.log)"; exit 1; }
  elif [[ "$1" == *.lean ]]; then bare env lean "$1"
  else bare build "$1"
  fi
}

say "1  clone openai/math lean/ at $SHA into $WORK/oai"
run mkdir -p "$WORK"
run git clone -q --filter=blob:none --no-checkout https://github.com/openai/math.git "$WORK/oai"
run git -C "$WORK/oai" sparse-checkout set lean
run git -C "$WORK/oai" checkout -q "$SHA"
L="$WORK/oai/lean"
[ "$DRY" = 1 ] || cd "$L" || exit 1

say "2  lake exe cache get (resolution, pre-resolution patches, mathlib cache)"
bare exe cache get

say "3  the 12 post-update patches, applied and verified by git"
for p in $POST_PATCHES; do
  f="$L/patches/$p-lean4341.patch"
  run git -C "$L/.lake/packages/$p" apply "$f"
  run git -C "$L/.lake/packages/$p" apply --check --reverse "$f"
done
run git -C "$L" diff --exit-code -- lake-manifest.json

say "4  build $MOD"
build "$MOD" solution

say "5  the challenge statement, the axioms, and a planted sorry"
if [ "$DRY" = 0 ]; then cat > "$L/ScratchReplay78.lean" <<EOF
import $MOD

open scoped _root_.DirichletCharacter in
theorem replay78_challenge_statement
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  $THM χ hs hpole

#print axioms $THM
#print axioms replay78_challenge_statement

theorem replay78_control : (1 : ℕ) = 2 := by sorry
#print axioms replay78_control
EOF
fi
if [ -n "${SALTBUILD:-}" ]; then build ScratchReplay78.lean audit; A="$WORK/build-audit.log"
else A="$WORK/audit.log"; printf '$ %s env lean ScratchReplay78.lean > %s\n' "$LAKE" "$A"
  [ "$DRY" = 1 ] || "$LAKE" env lean ScratchReplay78.lean > "$A" 2>&1 || { echo "FAILED: audit (log $A)"; exit 1; }
fi
if [ "$DRY" = 0 ]; then
  # the theorem's axioms must be exactly the three; the planted sorry must show sorryAx
  tr '\n' ' ' < "$A" | grep -F -q "'$THM' depends on axioms: [propext, Classical.choice, Quot.sound]" \
    || { echo "FAILED: the axioms of $THM are not the three standard ones (log $A)"; exit 1; }
  grep -F -q "'replay78_control' depends on axioms: [sorryAx]" "$A" \
    || { echo "FAILED: the planted sorry did not print sorryAx, so the audit saw nothing (log $A)"; exit 1; }
  echo "AXIOMS: $THM depends on [propext, Classical.choice, Quot.sound]; the control prints [sorryAx]"
fi

say "6  CONTROL: leanchecker --fresh on a planted false declaration must FAIL"
if [ "$DRY" = 0 ]; then cat > "$L/OAI/NumberTheory/Replay78Bad.lean" <<'EOF'
import Lean
open Lean Elab Command

-- CONTROL for the leanchecker replay: a theorem of `False` whose value is `True.intro`, added with
-- the kernel's type check skipped so that it reaches the olean.
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl (Declaration.thmDecl
  { name := `replay78_bad, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })
EOF
fi
build OAI.NumberTheory.Replay78Bad control
printf '$ %s env leanchecker --fresh OAI.NumberTheory.Replay78Bad\n' "$LAKE"
if [ "$DRY" = 0 ]; then
  if [ -n "${FLEET_FLOCK:-}" ]; then
    flock -w 14400 "$FLEET_FLOCK" "$LAKE" env leanchecker --fresh OAI.NumberTheory.Replay78Bad
  else
    "$LAKE" env leanchecker --fresh OAI.NumberTheory.Replay78Bad
  fi
  if [ $? = 0 ]; then echo "CONTROL PASSED: the checker accepted a false declaration"; exit 3; fi
  echo "CONTROL REJECTED, as it must be"
fi

say "7  leanchecker --fresh $MOD"
bare env leanchecker --fresh -v "$MOD"
if [ "$DRY" = 1 ]; then say "DRY RUN: the commands above were printed, none was executed"; else say "REPLAY PASSED"; fi
exit 0
