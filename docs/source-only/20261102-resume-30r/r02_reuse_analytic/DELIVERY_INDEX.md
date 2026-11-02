# R11–R24 delivery snapshot

Machine-readable metadata is in [DELIVERY_INDEX.json](./DELIVERY_INDEX.json). This is a read-only snapshot taken while authors were still writing. It records every currently present `.lean` source's path, byte length, SHA256 and literal `import` lines, plus per-slot REPORT/REGISTRY presence and any non-Lean payload files.

At the 13:37 UTC snapshot, 62 Lean files are present across R11–R24. REPORTs exist for R15, R18, R19 and R23; REGISTRYs exist for R18 and R19. The reports explicitly classify 8 Lean files as new sources, 2 as minimal repairs and 2 as exact pinned Mathlib source copies. The remaining 50 files have provenance `unknown` because their slot reports were not yet present; exact-copy or minimal-repair status is not inferred from filenames or imports. Other source artifacts (including Mathlib `.txt` files in R20) are also listed with bytes and SHA.

The index does not assess proof validity or completion. It does not execute author scripts, Lean, a compiler, guards, CI or numerical replay. Since the authors are still active, hashes and presence statuses are a freeze candidate only and should be refreshed after their final reports/registries arrive.
