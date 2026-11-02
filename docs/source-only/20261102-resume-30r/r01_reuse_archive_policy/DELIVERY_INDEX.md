# R03–R10 delivery snapshot

See [DELIVERY_INDEX.json](DELIVERY_INDEX.json) for the file-level inventory captured at **2026-11-02 13:35:41 UTC**. At that snapshot, 8 scopes contained 27 Lean files; REPORT and REGISTRY were present for R04, R05, and R06 only. Authors were still writing, so these are current counts, not final delivery totals.

The index records each Lean path, byte length, SHA256, and syntactic `import` lines. It classifies files as `new_code_reported` only where the available REPORT explicitly describes that source as new; all others are `unknown` until their author reports the source as a copy, repair, or new proof. Imports are listed as text and were not resolved or compiled. No proof, guard, CI, numerical replay, or generator script was run.
