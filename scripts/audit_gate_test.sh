#!/bin/bash
# audit_gate_test.sh — the arms for audit_gate.sh's DECLARATION matcher.
# Driven, not reasoned: every arm is a real added-line pair fed to the real regex.
# A fix whose only witness is a better number is not a fix (compiler, 08/10).
set -u
OLD='^\+(theorem|lemma|def|abbrev|structure|instance) '
NEW='^\+[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|nonrec|noncomputable|scoped|local|partial|unsafe)[[:space:]]+)*(theorem|lemma|def|abbrev|structure|instance)[[:space:]]'
pass=0; fail=0
arm() { # name  input  want_old  want_new  want_name
  local n="$1" in="$2" wo="$3" wn="$4" wname="$5"
  local go gn nm
  go=$(printf '%s\n' "$in" | grep -cE "$OLD"); [ "$go" -gt 0 ] && go=VIS || go=INV
  gn=$(printf '%s\n' "$in" | grep -cE "$NEW"); [ "$gn" -gt 0 ] && gn=VIS || gn=INV
  nm=$(printf '%s\n' "$in" | grep -E "$NEW" | sed -E "s/$NEW"'+([A-Za-z0-9_.'"'"']+).*/\5/' | sort -u | tr '\n' ',' | sed 's/,$//')
  if [ "$go" = "$wo" ] && [ "$gn" = "$wn" ] && [ "$nm" = "$wname" ]; then
    printf "  PASS  %-34s old=%-3s new=%-3s name=%s\n" "$n" "$go" "$gn" "${nm:-–}"; pass=$((pass+1))
  else
    printf "  FAIL  %-34s old=%s(want %s) new=%s(want %s) name=%s(want %s)\n" "$n" "$go" "$wo" "$gn" "$wn" "$nm" "$wname"; fail=$((fail+1))
  fi
}
echo "ARMS — old matcher vs widened matcher:"
arm "1 bare theorem"            '+theorem foo : True := trivial'        VIS VIS foo
arm "2 private theorem"         '+private theorem bar : True := trivial' INV VIS bar
arm "3 same-line @[simp]"       '+@[simp] theorem baz : True := trivial' INV VIS baz
arm "4 indented theorem"        '+  theorem qux : True := trivial'       INV VIS qux
arm "5 two-line attributed ⭐"   "$(printf '+@[simp]\n+theorem quux : True := trivial')" VIS VIS quux
arm "6 NEG: audit line"         '+#audit_axioms notadecl'                INV INV ''
arm "7 NEG: removed line"       '-theorem deleted : True := trivial'     INV INV ''
arm "8 private+noncomputable"   '+private noncomputable def d : Nat := 0' INV VIS d
echo
echo "RESULT: $pass pass, $fail fail"
[ "$fail" -eq 0 ] || exit 1

# ── AUDIT-SIDE ARMS — HERMETIC (rewritten 2026-08-28 before merge) ──────────────
# ⛔ THE FIRST VERSION OF THESE TWO ARMS CITED REAL SALT COMMITS (daa2dae8,
# e0fea691) AND WOULD HAVE FAILED IN EVERY FRESH CLONE: both live on an unmerged
# branch, so `git show <sha>` finds nothing on main.  They passed for me because
# my clone had the branch.
# ⇒ A TEST THAT PASSES IN THE AUTHOR'S CLONE HAS NOT BEEN SHOWN TO PASS IN A
#   CLONE THAT LACKS THE AUTHOR'S BRANCH.  Same class the Captain named one level
#   up ("passed against 87b78398 is not passed against what is there now"), and
#   worse here: those commits are work a ruling PARKED, so the test would have
#   depended on history that must not land.
# The arms now BUILD THEIR OWN FIXTURE REPO.  No salt history, no network.
echo
echo "AUDIT-SIDE ARMS (hermetic fixture repo, no salt history):"
GATE="$(cd "$(dirname "$0")" && pwd)/audit_gate.sh"
FIX=$(mktemp -d); trap 'rm -rf "$FIX"' EXIT
# ⛔⛔ EVERY GIT CALL BELOW IS `git -C "$FIX"` AND EVERY PATH IS ABSOLUTE, AND THAT IS NOT STYLE.
# 2026-08-29: an earlier version of this block opened a `( cd "$FIX" && ... )` subshell and I
# left a stray `)` in it while adding arms 11-12. Bash reported the syntax error -- AND HAD
# ALREADY RUN the commands that followed it, in the CALLER'S directory, because the `cd "$FIX"`
# lived inside the subshell that never opened. Result: three fixture commits (f3base, f3append,
# f4) and two files (c.lean, d.lean) landed in salt's own history and were pushed to a public
# remote before I noticed.
# ⇒ A TEST FIXTURE THAT REACHES ITS SANDBOX BY `cd` IS ONE SYNTAX ERROR AWAY FROM WRITING TO THE
#   REPOSITORY UNDER TEST. `git -C` and absolute paths cannot miss: there is no shell state to
#   get wrong, so the failure mode is deleted rather than made less likely.
git -C "$FIX" init -q . && git -C "$FIX" config user.email t@t && git -C "$FIX" config user.name t
# fixture 1 — a two-line, FULLY QUALIFIED roll-call covering both declarations
printf 'theorem hdiv_of_log_growth : True := trivial\ntheorem twinLogWeight_support : True := trivial\n#audit_axioms Fix.hdiv_of_log_growth\n  Fix.twinLogWeight_support\n' > "$FIX/a.lean"
git -C "$FIX" add a.lean && git -C "$FIX" commit -q -m f1
# fixture 2 — declarations with NO roll-call at all, incl. a PREFIXED one
printf 'theorem plain_one : True := trivial\nprivate theorem hidden_two : True := trivial\n@[simp] theorem attr_three : True := trivial\n' > "$FIX/b.lean"
git -C "$FIX" add b.lean && git -C "$FIX" commit -q -m f2
# fixture 3 — THE APPEND CASE: a commit that adds a declaration and puts its roll-call name at
# the END of an ALREADY-EXISTING block. The header is unchanged, so it is not in the diff, and
# the filler keeps it beyond diff context -- the REAL shape, where `Salt/MR/All.lean`'s header
# sits thousands of lines above the append point.
printf 'theorem f1 : True := trivial\ntheorem f2 : True := trivial\ntheorem f3 : True := trivial\ntheorem f4 : True := trivial\ntheorem f5 : True := trivial\ntheorem f6 : True := trivial\n#audit_axioms Fix.f1\n  Fix.f2\n  Fix.f3\n  Fix.f4\n  Fix.f5\n  Fix.f6\n' > "$FIX/c.lean"
git -C "$FIX" add c.lean && git -C "$FIX" commit -q -m f3base
printf 'theorem f1 : True := trivial\ntheorem f2 : True := trivial\ntheorem f3 : True := trivial\ntheorem f4 : True := trivial\ntheorem f5 : True := trivial\ntheorem f6 : True := trivial\ntheorem appended_seven : True := trivial\n#audit_axioms Fix.f1\n  Fix.f2\n  Fix.f3\n  Fix.f4\n  Fix.f5\n  Fix.f6\n  Fix.appended_seven\n' > "$FIX/c.lean"
git -C "$FIX" add c.lean && git -C "$FIX" commit -q -m f3append
# fixture 4 — the NEGATIVE control: a bare dotted line that is NOT inside any roll-call block.
printf 'theorem uncovered_eight : True := trivial\n-- Fix.uncovered_eight was discussed in\n  Fix.uncovered_eight\n' > "$FIX/d.lean"
git -C "$FIX" add d.lean && git -C "$FIX" commit -q -m f4
F1=$(git -C "$FIX" rev-parse HEAD~4); F2=$(git -C "$FIX" rev-parse HEAD~3)
F3=$(git -C "$FIX" rev-parse HEAD~1); F4=$(git -C "$FIX" rev-parse HEAD)
a2() { local n="$1" c="$2" want="$3" got
  got=$( cd "$FIX" && bash "$GATE" "$c" 2>/dev/null \
        | sed -n '/^--- declared but NOT audited/,/^--- audited/p' | grep -vE '^---' | grep -c . )
  if [ "$got" = "$want" ]; then printf "  PASS  %-46s unaudited=%s\n" "$n" "$got"
  else printf "  FAIL  %-46s unaudited=%s (want %s)\n" "$n" "$got" "$want"; fail=$((fail+1)); fi
}
a2 "9  continuation + qualified  -> NO false positives" "$F1" 0
a2 "10 genuine miss (incl. prefixed) -> STILL FLAGGED"  "$F2" 3
a2 "11 APPEND to an EXISTING block -> NO false positive" "$F3" 0
a2 "12 NEG: bare name OUTSIDE any block -> FLAGGED"      "$F4" 1
echo
echo "TOTAL: $fail failure(s)"
[ "$fail" -eq 0 ] || exit 1
