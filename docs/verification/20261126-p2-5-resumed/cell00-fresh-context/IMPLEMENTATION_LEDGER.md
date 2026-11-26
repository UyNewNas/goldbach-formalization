# SDD ledger — plan: docs/superpowers/plans/2026-11-26-p2-5-fresh-context-plan.md

## Scope and rulings

- Root explicitly authorized this implementation after reading the landed spec
  and plan. This does not claim new user approval of the design documents.
- Ruling: use the existing task checkout and disjoint new file paths, as root
  assigned, instead of creating another checkout. Root owns publication and
  cloud execution; the implementer changes no existing production source.
- Ruling: test the new archive/context/rematerialization boundaries only. The
  user's no-duplicate-work instruction and root's explicit test scope override
  a generic whole-project test rerun. No settled Lean work or remote scan is run.
- Pre-flight: history validation permits exactly five missing envelope tuples
  and pending approved object aliases; all other bytes remain strict. Normal
  rematerialization must finish with exact old object hashes before the original
  four-consumer owner validation is entered. No generic bind or Path override.
- Pre-flight: normal rematerialization and consumer verification are separate
  phases in attempt008. Aggregate accounting must expose all new normal stages;
  old owner/aggregate receipts and the unchanged v7/recovery remain immutable.
- Pre-flight: traverse the complete 41-object DAG, then filter actual missing
  normal candidates. An already available intermediary never hides a dependency.

## Progress

- Task 1–4: targeted boundary tests written before v8 implementation; initial
  run uses unchanged v7 as the baseline when v8 does not yet exist.
- Task 5: publication/cloud execution remains owned by root and is not claimed
  by local implementation evidence.

## Verified local implementation

- Task 1: exact five-envelope availability ledger implemented. The old `bind`
  and `artifact` functions remain AST-identical and cannot manufacture success.
  Targeted tests reject a sixth missing file and wrong path/hash/size tuples.
- Task 2: actual ordered provider resolution, companion identity, full runtime
  pins and fresh current timestamps are implemented. Local fixtures cover
  shadow providers, changed companions, incorrect module identity and a missing
  runtime pin. Actual P3 plan/context capture has not been executed by this agent.
- Task 3: full-41-DAG order followed by actual-missing filtering is implemented;
  normal stages are separate, exact-SHA admission precedes all historical alias
  installation, and available objects cannot be compiler targets.
- Task 4: all 22 original top-level helpers and 13 internal acceptance helpers
  remain AST-identical. Only the internal context check and stage runner gain
  additional post-stage/gap-availability checks. Eleven targeted checks passed;
  independent review is pending and no new Lean stage is claimed.
- Ruling: reuse the already completed exact restore, rather than repeating plan
  Task 5's originally prospective restore instruction. Root's actual P3 task
  `7e4a232db37746d5941508305c42a24c` restored 526 paths and produced
  `PARTIAL_RESTORE_ONLY`, with 74 unresolved paths (69 aliases of the ten missing
  objects plus five snapshot envelopes), no normal/replay/audit execution, and
  all 15,940 runtime pins passing. Its receipt is
  `/workspace/p25-q96-20261125/.lake/diagnostic/p25-cache-rematerialization-attempt001/RECOVERY_RESULT.json`,
  SHA256 `cf26553c585e5a5e4e2527095935af092d402381c47fc6595d9e5a08093cac17`.
  V8 binds that actual receipt and rechecks current bytes; it never invokes the
  old restoration driver. If the receipt or present context differs, v8 stops.
- The published spec/plan input hashes are kept stable during final review;
  completed implementation steps and the executed-restore sequencing adjustment
  are recorded here instead of silently changing a pinned design input.
