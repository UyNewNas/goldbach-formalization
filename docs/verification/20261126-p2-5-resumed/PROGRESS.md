# P2.5 continuation — 2026-11-26

User scope: complete Saving16 inside the November 6 manuscript, reuse existing work,
write source locally, use the supplied compiler environments, and submit to GitHub.
No new axiom, sorry, admit, native_decide or unsafe proof shortcut is permitted.

Baseline: remote `work/p2-5-saving16-20261125` at
`4e69759e3d27495c0e7bccfee23b7a0b42c48ea6`; its tree equals the previous
local `aeebee513ed88332ba4ef1c8f4b4222252898dcc` tree. The older dirty checkout
is preserved. This continuation uses `/workspace/library-files/p25-proof-work`.

## Execution ledger

- Recovery complete: original round3 task `ba9a22be4e61459497878039580c02c9`
  finished with 325/377 normal compilation records, 38/69 accepted owned audits,
  eight direct normal failures and 44 dependency-blocked modules. The complete
  task stdout is retained here. This is not a successful P2.5 acceptance.
- The published final cell00 decoder candidate was tested by task
  `1847725e973d4e2f866720eac3f6f4d9`, reusing 21 accepted dependency objects.
  It failed normal checking: the two mapM goals were resolved, but three existing
  array aliases remained, followed by a kernel memory limit. The exact failed
  receipt and logs are preserved under `field-final-attempt004`; no new formal
  credit follows from that attempt. A targeted proof-expression repair is pending.
- All eight complete original per-module logs have been recovered and checked
  against their recorded source hashes. Independent review approved four exact
  historically compiled source repairs and four existing draft repairs, with only
  the additional unused-simp removals established by the complete H5/H7 log.
  The unchanged 377-module closure and 69-target audit will decide current reuse.
- Published the reviewed analytic repairs and strict continuation at
  `168973571f795dbe8fb1c1bccfd7f7c54899b36a`. P2 task
  `381b23081efa4391a45337f2a1eb0ab8` reached 330/377 normal successes, reusing
  all 325 prior successes and adding five. Its completed owned audit accepted
  41/69 targets, reusing all 38 earlier successes and accepting three new owners
  containing 245 declarations. Six direct failures and 41 blocked modules remain.
  The complete original receipt and six failure logs were recovered byte exactly;
  all source, gate, runner, HEAD, history, baseline and external postflight checks
  matched. The aggregate remains failed.
- Published the explicit cell00 field composition at
  `b667409e7e7f23094637dfccfdceec6e6d34ee68`. P3 task
  `202af6f52a5c405eaa74fe1f00906a75` failed only on kernel memory at the final
  theorem. The exact failed receipt is retained under `field-explicit-attempt005`.
  The next candidate uses a private symbolic composition lemma, while preserving
  all public statements and discharging all helper premises in the closed theorem.
- Published that symbolic repair at `99ec807044cd865b9713e769c6a967094c4b3e34`.
  P3 task `271829aa21dd4513b8e2754b759fb241` accepted the final field decoder:
  normal compilation, independent replay and complete owned audit all exited zero.
  The audit covers seven declarations including the actual private composition
  helper. All 21 accepted dependency objects were reused without repeating their
  gates. The exact receipt, logs and accepted object are retained in
  `field-symbolic-attempt006/ACTUAL_EVIDENCE.json.xz`.
- Published the independently reviewed five-consumer continuation at
  `8fb0faace8f95a4ad4be26f32350575491445ac4`. P3 task
  `c9cc66562e934713bcf75ab704f8562d` failed on disk exhaustion while creating
  the first target directory, before any normal, replay or audit stage started.
  All five owners remain unaccepted; the exact receipt is preserved under
  `consumer-attempt004`. Existing proof sources remain unchanged. Resource
  recovery and a fresh continuation must preserve this failed attempt.
- Resource-guarded consumer v5 was published at
  `be20f0b050bb787ecb98f9afdd9b6a386706f45a`. Its actual attempt005 accepted
  `P2Saving16Cell00Decoded` with four owned declarations and then encountered
  kernel memory errors in `P2Saving16Cell00OriginalParse`. The aggregate remains
  failed and the three later owners remain pending. Complete actual evidence
  and the accepted Decoded object are preserved under `consumer-attempt005`.
  Continuation must reuse that owner and repair only the observed transport
  expression, with the public statements and original source data unchanged.
- The independently reviewed four-consumer v6 continuation keeps accepted Decoded
  as dependency 41 and changes only OriginalParse proof expressions. Three private
  symbolic-index wrappers preserve the same three public statements. All 46 offline
  guard tests passed; actual compiler gates remain pending. Earlier consumer004/005
  aggregates retain their failed status.
- P2 storage v2 task `f1014302ea974fc9a9a13ebb97cee682` stopped at its
  capacity guard before mutation. Its exact 1,406-byte receipt is retained under
  `p2-storage-round4-v2/apply002`; no storage recovery or proof credit is claimed.
- Four-consumer v6 is published at `4653b261828f127ba0b5082eaf1106a3fea09d46`
  and submitted as P3 task `c797343dbed9482482010ecb52e4b22e`. It was still
  queued at this checkpoint; source review supplies no compiler acceptance.
- Storage v3 adds only unreferenced `docs/evidence/owned-frontiers/` Git working
  copies. An exact read-only inventory found 1,278 ordinary blob-equal files and
  193,220,608 conservative allocated bytes; eight attribute files stay protected.
  All 15 policy/capacity tests passed independently. Every live protection, source,
  cache, history, and 1 GiB plus reserve check remains unchanged. Recovery itself
  is still pending and must pass before analytic round5 runs.
- Actual P2 storage v3 task `5a632d0956bc4390882e3ef172b3f6c1` verified
  recovery with all protected state preserved: 14,480 Git-backed working copies
  omitted, 1,207,435,264 bytes free afterward, and exact before/after inventories
  for .lake, untracked content, and Git objects. Its complete receipt is
  `p2-storage-round4-v3/apply003/RESULT.json` (SHA256 `1253123cda0c1633741162a0b40c2a657bab760ac98a4007db5e9b62c61bd134`).
  Analytic round5 is queued as task `a9e1b11909934ee9b9987468713ef5c3`, with
  the unchanged published c46d0d48 source and original 377/69 gates.
- P3 v6 task `c797343dbed9482482010ecb52e4b22e` stopped at its initial disk
  guard, before output-directory creation or any Lean stage. The exact stdout
  and read-only topology/capacity evidence are in `consumer-v6-disk-preflight`.
  The clean be20 checkout, original failed005 receipt, and executed runner bytes
  were confirmed; no proof source or acceptance changed.
- The P3 storage adapter is independently reviewed with all 20 offline checks
  passing. It permits only unreferenced owned-frontiers working copies, requires
  locally available exact Git blobs without lazy fetching, and preserves actual005
  history, current sources, all cache/untracked state, Git objects and siblings.
  Actual recovery is still pending.
- The live analytic round5 normal stage reached 336/377 successes, reusing all
  330 prior successes and adding six. Four direct normal failures remain. Owned
  audits are still running; final counts and postflight status remain pending.
- Whole P2.5 remains open: all fourteen original archives and 39,741 simplex
  operations, their exact individual Q96 floor sum, analytic ownership/integral
  closure, and the same-Q/rho signed distribution supplier.

## Decisions

- Reuse the existing plan in `docs/superpowers/plans/2026-11-25-p2-5-saving16.md`.
  This is continuation of the user's authorized design, not a new proof route.
- Preserve all selected source statements, data and complete modulus terms.
  Reuse historically compiled repairs only after current preimage comparison;
  old objects require current source/dependency/context identity before reuse.
- Lean theorem checking, independent kernel replay and full owned-declaration
  audit are the proof validation gates. Finite consumers transport proved
  equalities instead of repeating parser, determinant or floor evaluation.
- The manuscript and existing OwnedIntegral chain need a disjoint positive
  inner union, not an exhaustive triangulation. No extra coverage theorem is added.
- The manuscript freezes `3ffa2d1` and `a988cba` have identical release TeX;
  the intervening change only updated README. Existing manuscript pins are valid.

Formal credit in this ledger is limited to the explicitly identified accepted
owners and their exact receipts. It does not establish completion of P2.5.

## Continuation after c3eb1474

Round5 final receipt is confirmed: 336/377 normal successes, 44/69 owned audits, all seven postflight identity checks true. Four direct failures and 37 dependency-blocked modules remain. The three newly accepted owners contain 96 declarations: Full87SourceDictionary, H5H7SourceDispatch, and Full87PrefixBinding. This replaces the earlier running-state snapshot, without relabeling the failed aggregate.

Reusing the already written round6 candidates and cell00 v6 consumers. The existing plan remains authoritative; no new mathematical route is introduced. P3 storage v1 stopped before mutation due to a historical/current manifest provenance mismatch; the existing v2 minimal repair passed its 30 regression checks and was submitted as task 4731a36a0ec14dc38c38a5b134f2380f. Actual recovery is pending.

P3 storage v2 stopped before mutation on insufficient eligible space. Consumer v7 retains the exact proof and source-validation gates while using same-filesystem hardlinks for the 41 accepted imports and a measured resource budget (320 MiB startup, unchanged 256 MiB per-stage). Independent review found no old-owner output collision or weakened proof gate. Its three real-filesystem regressions passed after an observed failing baseline; actual Lean execution is pending.

Round6 restores three existing compatibility repairs and adds the reviewed Full87Ownership proof-expression repair. All 84 prior theorem statements remain unchanged. The four modified modules affect exactly the 41 previously failed/blocked modules and 25 unaccepted audit targets; the original source/dependency-qualified drivers control reuse of the other 336/44. Eight driver provenance/scope regressions passed. Also preserved the existing typed geometry package and added eight original-archive equality transports; none is claimed as accepted without its actual gates.

P3 task e0c09dd8206140688b00dd789250f8a2 stopped before a Lean stage because the old attempt004 receipt could not be found. Read-only task 9b36239fd5c840b49612f0e0b3406898 then observed that the entire p25-q96 .lake directory was absent, while HEAD remained be20f0b0 and free disk had risen to 9,719,013,376 bytes. The earlier storage-v2 receipt explicitly records mutation_started=false. Current cache recovery is under investigation; no old acceptance is relabeled and no missing object is invented.

Round6 source and runner are published at `7926999deb30b63976739355b3076990b370e66f`; task `de733cb34db040809cba4096a5cfc0b7` is running on the dedicated P2 compiler. The source tree matches the locally reviewed index exactly (`1c499b283fd6fa2ae83c8d66d0b2e1ea9e934099`). Preflight and actual Lean gates are pending; no new acceptance is claimed.

Round6 normal stage completed with 339/377 successes (336 reused, 3 fresh), four direct failures and 34 dependency-blocked modules. HistoryCore, VariableFourthContinuation and CoarseFourthCellLimit passed normal compilation. Full87Ownership failed inside simplification with a runtime stack trace; complete first-error evidence is still needed before diagnosis. Newly exposed P1 failures in FourthDescendantLevel, FifthContinuation and FourthProfileRegularity have exact historical repairs in batches75/58; the three source-only reuse candidates preserve 43 theorem statements. ProfileRegularity additionally needs the exact deprecated alias replacement continuous_finset_sum -> continuous_finsetSum. Owned audits and final postflight remain pending.

Round6 completed at 2026-11-26T07:38:33Z: 339/377 normal and 45/69 owned, all seven postflight checks true, aggregate false. The newly accepted HistoryCore owner has 33 declarations. Complete task stdout and its unedited final result payload are preserved under p2-round6-attempt006; separate observation of the remote saved-file hash is queued behind another compilation. Round7 still requires that saved-file hash to match before execution.

Round7 reuses three historical P1 source repairs and repairs Ownership using definitionally equal nine-coefficient vectors with explicit Fin index normalization. The original full tables reproduce the row-reduction failure; all 49 corrected real-table row instances passed the local strict diagnostic. Independent source review preserves all 58 theorem statements across the four modules. This is not whole-module acceptance. The driver preserves the original 377/69 checks and targets only the 38 currently failed/blocked modules; all 339/45 previous qualifications remain eligible for reuse.

Round7 was published at `1e80a5fa2fa2dbb346dbdef5760a7361a8001a46` (tree `c84d1ef5e2be52a3158182949bd4be7a3b788770`) and queued on P2 as `36dfc8a826654f0dad5ea96d51f96fe3`. It performs an additional read-only 1 GiB disk check before starting the unchanged guarded driver, so insufficient space cannot consume attempt007. No round7 Lean acceptance is inferred from submission.

## 2026-11-26: round7 early disk gate and exact round6 remote result

P2 task `36dfc8a826654f0dad5ea96d51f96fe3` ended before the round7 driver: free bytes 1,046,097,920 were below the unchanged 1,073,741,824-byte minimum. It created no attempt007 evidence and started no Lean gate. A read-only storage inventory was submitted; no cache or historical record has been deleted.

The separate read-only task `62128eea019a4f328c40227f554aae75` confirmed the actual remote round6 RUN_RESULT file has 103,970 bytes and SHA256 `9fe39608896832b25314f258da68615b8a1a98f6c63a184bb2359122f67f7bf7`, exactly equal to the lossless stdout reconstruction. Remote HEAD was `7926999deb30b63976739355b3076990b370e66f`. The first-error observation log preserves the four failed modules; the Ownership log prefix is explicitly partial (full remote log 6,549,500 bytes).

P3 recovery driver and final inventory passed independent static review. Thirty-one of forty-one dependencies have exact available bytes, including twenty-one already on P3 and ten requiring only byte transport. Fourteen original witness hashes match. The ten truly missing objects remain eligible only for the existing restricted recovery procedure after historical metadata resolution. No new mathematical acceptance is claimed.

## P3 recovery publication and byte delivery

Recovery publication `58b652df0144a0726818775e61d188c23ae40072` contains the frozen recovery/bootstrap runners and exact source closure. P3 payload task `4ced709f83574134929dfc45853c37a7` delivered the ten local-only existing objects in a 2,640,212-byte archive with SHA256 `b0719bd03bab9be02756e298cfef4bc44fa61cabbff722d00025ae460fe3ea80`. It executed no Lean and changed no project cache.

The first deployment task `036fc06a5eea42ef9a7b6ed0a3425a6f` stopped before checkout because tracked status was dirty. Read-only task `c36101f1b3d244169cd882ed734ba095` identified exactly eighteen missing tracked historical files, all under `.lake/proof-continuation/source-reviews/drafts/`; there were no edited contents or staged edits, and HEAD remained `be20f0b050bb787ecb98f9afdd9b6a386706f45a`. Follow-up task `f74f55cacb2d40ee807544c3a86c257d` will restore only those absent paths from the exact current Git blobs, refusing existing targets or changed inventory, before proceeding to bootstrap and a read-only recovery plan. No acceptance credit has been added.

P3 follow-up `f74f55cacb2d40ee807544c3a86c257d` has now restored the eighteen absent tracked files (133,383 original bytes) from the exact `be20...` Git blobs, checked out `58b652df...`, and restored all five original RESULT byte strings from their existing published xz capsules (24,565,777 bytes, all original SHA256 values matched). Its actual recovery resolver is running. This transport/decompression stage did not execute Lean or grant new proof credit.

The actual P3 plan completed (exit 2 means unresolved requirements): 390 of 419 unique hashes available, all 15,940 runtime paths verified, no conflicts. A subsequent exact-byte recovery prepared 14 of the 19 missing nonobject hashes: 4 already published source copies, 6 deterministic audit-template instantiations matching their old SHA, and 4 owned JSON files extracted from original receipts/logs and matching their old SHA. Five historical COMPLETE_EXTERNAL_BEFORE snapshots remain unavailable because their individual started/finished microsecond timestamps are absent from the preserved evidence; their deterministic runtime entries match, but no replacement old snapshot has been invented. Old v7 and recovery gates remain unchanged.

The narrow P2 baseline-document storage adapter passed independent static review with runner SHA `14bf7f893d51d4444b6cca68592b4fd7b5ce276d3fc87a0e21a5e820d879fe51`. Its 128 MiB storage target is separate from the unchanged 1 GiB proof gate. Actual capacity, sparse omission and subsequent round7 execution still require cloud results.
