# Source gate v3 correction

This is a separate successor. Frozen v2 and its mathematical/43-source plan bytes remain unchanged.

The native source census now calls `os.walk(..., onerror=walk_error)`, where every directory error is raised. An unreadable directory cannot silently disappear from a successful census.

Post-compile `verify_existing` now requires the installation-period receipt path and its independently bound SHA256. It checks matching source commit, run/attempt, native revision, plan, acceptance manifest and gate-script hash. The installation receipt's actual43 rows and observed post-install census must equal the current existing canonical paths and bytes. Its raw identity and normalized census/row identities are retained in the new post receipt. Missing files are rejected without repair; pre/post receipts must have distinct output identities.

The source gate also binds the complete future acceptance-manifest kernel set. It requires the independently reviewed legacy1607 set, SHA256 `7182083990021cce01c1e357f8de8148e636a4c24d7613c00be0b3328ec5f543`, as a subset of the new complete census. The real paid-I87 successor may add modules; it cannot drop the original gate or native43. This source gate itself never runs compilation or replay.

Ambiguous `flags_unchanged` credit is removed. The receipt distinguishes the installer's lack of flag writes from actual compiler flags and runtime ABI, which it explicitly leaves unverified. Guarded compilation, setup/import binding, full fresh kernel replay and actual terminal-type/axiom evidence remain separate mandatory gates.

`HISTORICAL_METADATA_FIELD_ERRATUM.json` separately clarifies the five file-table blob corrections plus four top-level version labels, and the1046-name count versus1021 byte-identical/25 different v2 core sources. No Lean normalization or source repair is performed.

Validation is limited to Python AST syntax and text/metadata inspection. The source gate, compiler, guard and proof/numerical code were not executed. The complete paid-I87 closure/type/resource manifest is the next independent step; this small correction does not claim that later installation scope is complete.
