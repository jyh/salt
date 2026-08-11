#!/bin/bash
# C9 AUDIT-LINE GATE — third-hand check that every declaration a commit INTRODUCES
# carries an #audit_axioms roll-call line in the SAME commit.
# Ships with its output per the extractor law (math life 9, finding D).
# METHOD: added lines only (^+), decl keywords, name = first token after keyword.
#         audit names = every token on an added #audit_axioms line.
C=$1
D=$(git show "$C" -- '*.lean')
DECLS=$(echo "$D" | grep -E '^\+(theorem|lemma|def|abbrev|structure|instance) ' \
        | sed -E 's/^\+(theorem|lemma|def|abbrev|structure|instance) +([A-Za-z0-9_.]+).*/\2/' | sort -u)
AUD=$(echo "$D" | grep -E '^\+#audit_axioms ' \
        | sed -E 's/^\+#audit_axioms +//' | tr ' ' '\n' | grep -v '^$' | sort -u)
echo "commit $C  decls=$(echo "$DECLS" | grep -c .)  audit-names=$(echo "$AUD" | grep -c .)"
echo "--- declared but NOT audited in this commit:"
comm -23 <(echo "$DECLS") <(echo "$AUD")
echo "--- audited but not declared here (lifted/restated elsewhere):"
comm -13 <(echo "$DECLS") <(echo "$AUD")
