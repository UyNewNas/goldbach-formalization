# Fresh rebuild acceptance, 30 October 2026

Base: `25afcbff11562df51ef7ac5113c879123fcd64c6`.

Batch 003 freshly compiles `ImbalancedChen.P2FiniteActiveBranchBuffer`, checks its complete defining-module declaration inventory and transitive axioms, and replays the selected module with the bundled Lean 4.33.0-rc1 `leanchecker`. All four gates succeeded. Only this selected module is accepted here, not the root or other working-tree candidate repairs.

The source change only narrows the previous blanket Mathlib import; theorem statements and proof bodies are unchanged. The original blanket-import audit exceeded the existing memory budget, so imports were reduced instead of raising that budget. The full source-freeze manifests include other candidate files but confer no acceptance on them.

Policy: trust 0, two Lean threads, 6144 MiB, 1800 seconds per compiler stage, 16200 seconds per batch, a serial compiler lock. Official pinned Mathlib cache dependencies are reused. `leanchecker` replays the target from imported dependencies, not all Mathlib from an empty environment. The standard axiom allowlist is propext, Classical.choice, Quot.sound.

The local runtime is an adaptation of the repository CI guard. It did not use or verify lean-action scripts. Batch 001 failed its audit; batch 002 was interrupted for a lock-ordering bug; neither is accepted. Batch 003 reran compilation, audit and replay after correcting that launch order. Evidence includes commands, logs, hashes, scope and runner source. Machine-local paths describe the observed execution and are not portable installation assumptions.
