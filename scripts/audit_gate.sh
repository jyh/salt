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
# ⛔ AUDIT SIDE, REPAIRED 2026-08-28 (math) — TWO artifacts, both exhibited on the
# real commit daa2dae8, where BOTH names it added were reported "NOT audited"
# while the commit's own roll-call audited BOTH:
#   (1) CONTINUATION LINES.  `^\+#audit_axioms ` reads ONE line, so
#       `+#audit_axioms A` / `+  B` lost B entirely.
#   (2) QUALIFIED vs BARE.  the block writes `Salt.TwinBar.foo`; the declaration
#       is `foo`.  Never matched, so an AUDITED theorem read as unaudited.
# Both fail toward FALSE POSITIVES -- the gate cries wolf -- and widening the
# DECLARATION side (above) fed more names into exactly that noise, so this is the
# other half of that change, not a new one.
# ⚠️ NORMALISE BOTH SIDES THE SAME WAY: names are dotted on BOTH sides, so the
# audited set holds each token AND its last component, and a declaration counts
# as audited if EITHER form is present.  (saltworks learned this on 08/10: a cure
# applied to one side only moved the count in the wrong direction.)
AUD=$(echo "$D" | awk '
  /^\+#audit_axioms/ { inb=1; sub(/^\+#audit_axioms[[:space:]]*/,""); print; next }
  inb && /^\+[[:space:]]+[A-Za-z0-9_.!?'"'"']+([[:space:]]+[A-Za-z0-9_.!?'"'"']+)*[[:space:]]*$/ {
        sub(/^\+[[:space:]]*/,""); print; next }
  { inb=0 }' | tr ' ' '\n' | grep -v '^$' | sort -u)
# ⛔ WIDENED 2026-08-29 (math) — THE THIRD ARTIFACT OF THIS EXACT CLASS, and the commit that
# found it was its own exhibit (`6a460109`: five declarations, all five genuinely audited and
# ticked `[3 axioms]` by the aggregate, ALL FIVE reported "NOT audited").
# THE BLIND SPOT: the awk above enters a block only on an ADDED `#audit_axioms` header. A name
# APPENDED to an ALREADY-EXISTING roll-call has no header in the diff -- in `Salt/MR/All.lean`
# the header sits thousands of lines above the append point, so it is not even a CONTEXT line,
# and no amount of widening the diff patterns can recover it.
# ⇒ THE DIFF CANNOT ANSWER THIS QUESTION AND THE POST-COMMIT FILE CAN. A name counts as
#   audited by this commit iff the commit ADDED its line AND that line sits inside a roll-call
#   block in the RESULTING file. Both halves are required: the first keeps the gate a delta
#   gate, the second is what the diff could not see.
# Like its two siblings this failed toward FALSE POSITIVES -- the gate cried wolf on audited
# work -- so the widening is driven against its negative control as well (arm 12: a bare dotted
# line outside any block must STILL be flagged, or the green was bought by accepting any
# indented name anywhere).
ADDED_BARE=$(echo "$D" | grep -E '^\+[[:space:]]+[A-Za-z0-9_.!?'"'"']+[[:space:]]*$' \
             | sed -E 's/^\+[[:space:]]*//;s/[[:space:]]*$//' | sort -u)
INBLOCK=$(for f in $(git show --name-only --format= "$C" -- '*.lean'); do
            git show "$C:$f" 2>/dev/null | awk '
              /^#audit_axioms/ { inb=1; sub(/^#audit_axioms[[:space:]]*/,""); print; next }
              inb && /^[[:space:]]+[A-Za-z0-9_.!?'"'"']+([[:space:]]+[A-Za-z0-9_.!?'"'"']+)*[[:space:]]*$/ {
                    sub(/^[[:space:]]*/,""); print; next }
              { inb=0 }'
          done | tr ' ' '\n' | grep -v '^$' | sort -u)
APPENDED=$(comm -12 <(echo "$ADDED_BARE") <(echo "$INBLOCK"))
AUD=$(printf '%s\n%s\n' "$AUD" "$APPENDED" | grep -v '^$' | sort -u)
# both forms of every audited token
AUDN=$(echo "$AUD" | awk '{print; n=split($0,a,"."); if (n>1) print a[n]}' | sort -u)
# a declaration is audited if its own name OR its last component is listed
UNAUD=$(echo "$DECLS" | while read -r d; do
          [ -z "$d" ] && continue
          last=${d##*.}
          echo "$AUDN" | grep -qx -e "$d" -e "$last" || echo "$d"
        done)
echo "commit $C  decls=$(echo "$DECLS" | grep -c .)  audit-names=$(echo "$AUD" | grep -c .)"
echo "--- declared but NOT audited in this commit:"
echo "$UNAUD" | grep -v '^$'
echo "--- audited but not declared here (lifted/restated elsewhere):"
echo "$AUD" | while read -r a; do
  [ -z "$a" ] && continue
  last=${a##*.}
  echo "$DECLS" | grep -qx -e "$a" -e "$last" || echo "$a"
done
