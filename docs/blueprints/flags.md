# Flags and claims

Append-only log. Sessions record here: node claims (to avoid duplicate work),
failed attempts (node id, model, what was tried, where it broke), and
statement concerns (never fix a statement yourself — flag it).

Format, one entry per line block:

```
## <date> <node-id> <model> <status: claimed | failed | statement-concern | done>
<free text: what was tried / where it broke / concern>
```

---
