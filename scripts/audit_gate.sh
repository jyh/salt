#!/bin/bash
# C9 AUDIT-LINE GATE — third-hand check that every declaration a commit INTRODUCES
# carries an #audit_axioms roll-call line in the SAME commit.
# Ships with its output per the extractor law (math life 9, finding D).
# METHOD: added lines only (^+), decl keywords, name = first token after keyword.
#         audit names = every token on an added #audit_axioms line.
C=$1
D=$(git show "$C" -- '*.lean')
# ⛔ WIDENED 2026-08-28 (math), on the helm's five driven arms at 15:37.
# THE BLIND SPOT WAS A PREFIX ON THE DECLARATION LINE ITSELF: the old regex
# required the keyword IMMEDIATELY after `+`, so `+private theorem`,
# `+@[simp] theorem` and an indented `+  theorem` were INVISIBLE -- never seen
# as declarations, therefore never reported as missing a roll-call line.
# MEASURED COST BEFORE THE FIX: 29 declarations that ARE on a roll-call were
# invisible to this gate (15 same-line-attributed, 14 private) -- they needed an
# audit line and this gate could never have flagged one missing.
# ⭐ THE TWO-LINE ATTRIBUTED FORM (`+@[simp]` then `+theorem ...`) was already
# VISIBLE via its second line and MUST STAY SO: arm 5 exists to keep it green.
DECL_RE='^\+[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|nonrec|noncomputable|scoped|local|partial|unsafe)[[:space:]]+)*(theorem|lemma|def|abbrev|structure|instance)[[:space:]]'
DECLS=$(echo "$D" | grep -E "$DECL_RE" \
        | sed -E "s/$DECL_RE"'+([A-Za-z0-9_.'"'"']+).*/\5/' | sort -u)
AUD=$(echo "$D" | grep -E '^\+#audit_axioms ' \
        | sed -E 's/^\+#audit_axioms +//' | tr ' ' '\n' | grep -v '^$' | sort -u)
echo "commit $C  decls=$(echo "$DECLS" | grep -c .)  audit-names=$(echo "$AUD" | grep -c .)"
echo "--- declared but NOT audited in this commit:"
comm -23 <(echo "$DECLS") <(echo "$AUD")
echo "--- audited but not declared here (lifted/restated elsewhere):"
comm -13 <(echo "$DECLS") <(echo "$AUD")
