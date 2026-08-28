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
