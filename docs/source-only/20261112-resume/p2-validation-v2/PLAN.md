# P2 integer-mass ABI: v2 remote acceptance preparation

**STATIC ONLY — not installed, compiled, dispatched or accepted.** The frozen v1 remains unchanged. Root alone may deploy after T10 review and after deciding when the existing heavy work permits it. Stored009–019 run `43122130246` is untouched. This directory supplies no dispatch, push or cancellation client.

## Exact source composition and scope

The proof composition is unchanged from v1: repaired production baseline `eb035a259f2f40853e9899f6d98af25852184fee` plus the ABI source from `607d835f6e18f0013cbea63bbefdaf7f6867cd50`, installed at `ImbalancedChen/Certificates/P2HistoricalThirdIntegerMass.lean`. The ABI is 8,003 bytes, Git blob `0d6a149aa983cb914b0602567de663c82017cc5f`, SHA256 `389bf428903797900dbc07a7dbf3471909f268705a389e0d61e02d7173d1c2ca`.

`P2_VALIDATION_MANIFEST.json` is byte-identical to v1, SHA256 `54fe783fd7310114cd8012530ff6eedc52c3a01fa76eb4860e1641cfe3f52653`. Its natural ABI import group has 101 local modules; one separate mandatory diagnostic target, same-baseline `ImbalancedChen.FinitePiIntegral`, gives 102 total modules and 1,245,032 source bytes. All 102 must be built, kernel-replayed and censused in the same job. Passing the diagnostic in this combined import environment does not resolve the old P4 environment's inventory failure. `P2ThirdTailCertificateTruncation`, the fifth baseline repair, remains outside this closure and is not claimed validated. Old ZeroGeometry/HybridLedger and the whole P4 tree are not added.

## Why v2 and exactly what changes

The new v1 manual-only workflow is not registered on default master (lookup 404); publishing it only on an isolated branch does not establish a usable manual route. v2 uses only `push` with both the exact branch `ci/p2-integer-mass-20261112` and exact changed path `.github/workflows/p2-integer-mass-validation.yml`. Static publication on a codex branch does not match. No default-branch change or manual-registration claim is made.

The driver must be one root-authored commit directly on reviewed base `356c3782e9428098a2fcbfb18c689bef264d84fa`. `DRIVER_BASE_WORKFLOW_AUDIT.json` records all seven inherited workflows, including exact blobs, SHA256 and parsed event filters. Six stay byte-identical. `VE_DRIVER_ONLY.patch` and `variable-envelope.driver.yml` add only the new CI branch to VE's `push.branches-ignore`; its pull_request, manual and other branches remain unchanged. This excludes an otherwise unrelated VE heavy run on the new push. No patch or driver installation was executed locally.

The actual new driver has eight workflow files. Before any staging, `p2_validation.py select` checks the root-delivered selection and every actual workflow against immutable `GITHUB_SHA` bytes. It rejects an unexpected/missing workflow or edited workflow. It reads the real parent from the raw commit header, so a first push's all-zero `event.before` is irrelevant. The root-reviewed final driver/tree must still be inspected before publication.

## External root selection; no registry self-hash cycle

Root must install `verification/parts/p0/P2_INTEGER_MASS_DRIVER_SELECTION.json` in that same driver commit. This is outside the hashed validation bundle. It supplies schema, the reviewed exact bundle REGISTRY SHA256, source `607d835f…`, repair `eb035a25…`, manifest `54fe783f…`, base `356c3782…`, branch, bundle path and workflow path. Every value is checked; missing, empty, malformed or placeholder hashes fail. There is no unchecked default input.

`ROOT_SELECTION_TEMPLATE.json` is an inert hashed template. After freezing the registry, `ROOT_DELIVERED_SELECTION.proposed.json` supplies the concrete proposed root selection, and `ROOT_DELIVERED_SELECTION.IDENTITY.json` records its independent byte identity. These two delivery artifacts are explicitly excluded from the bundle registry to avoid a cycle; root reviews them alongside the registry and copies only the selection to the external standard path. They are not automatically authorized or installed by this packet. Root's eventual driver commit and independent review bind that choice. The external committed selection is also hashed in retained `DRIVER_BINDING.json`.

Root-only install mapping is in `DRIVER_INSTALL_RECIPE.json`: exact v2 bundle, new workflow, VE's single-line replacement, and the reviewed external selection. This is a static recipe, not an executable installer. No branch or remote was written here. The existing `goldbach-p0-heavy` concurrency group and `cancel-in-progress: false` remain.

## Original stage, runtime and proof gates retained

`reused/stage_p4.py` and `reused/ci_runtime_guard.py` are byte-identical originals from driver356. The latter is 22,947 bytes, SHA256 `837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877`: Lean `-t0 -j2 -M12288`, inherited flock-controlled compiler slot, native flags preserved, native checker `LEAN_NUM_THREADS=2`. No new memory policy, checker flag or trust shortcut is introduced.

The candidate collector has exactly the v1 input adaptations: manifest targets, exact computed-closure order and pinned diagnostic template. Its entire snapshot/verification tail remains byte-identical to the original collector. Original declaration/type/axiom/replay gates are unchanged. All inherited reference scripts/workflows are inert except the explicitly named stage and runtime guard.

`Round6Audit.lean` is the exact diagnostic source SHA256 `46eedd90437fae00921f2a5a6a39abb5996125f45033b230c17d1403d16eec95` (not a commit), 10,050 bytes, blob `853f1a12de896ae0857e2b7e3b3f0900d31788bc`. T10's prior diagnostic-only review is retained. The exact `owned.qsort Name.lt == data.constNames.qsort Name.lt` comparison and original `Serialized declarations and defining-module inventory differ` throw are retained. Diagnostics enumerate loaded `header.moduleData` occurrences, not every independent IR object. A mismatch rejects acceptance.

The prospective sequence is: bind actual driver/root selection; check both immutable source checkouts; use the original generic stage on a fresh destination; bind original configuration/dependency pins; prepare and hash the 102-module audit; compile all 102; snapshot all local sources and local/package `.olean*`; kernel-replay all 102; export every serialized owned declaration, including private/generated declarations, with explicit and readable complete types and transitive axioms; run original strict verification; run the unchanged runtime audit/probe; retain exact objects and evidence; then finalize.

Unsafe, partial, unproved axioms, truncated types, serialized/owner inventory mismatch, module replay mismatch or snapshot mutation reject. The transitive axiom allowlist remains exactly `propext`, `Classical.choice`, `Quot.sound`. Both declared module groups appear in the same build, replay and census lists.

## Evidence retention and final binding

The archive streams actual final project and package `.olean*`, exact local sources, owned module-stem artifacts (including available `.ilean` and trace), pins and generated audit. Full logs, diagnostic JSON, before/after source-object bindings, dependency/source receipts, runtime evidence and driver/root selection bindings are uploaded separately with the archive for 30 days. This is not a complete Lake native/setup/ABI/independent IR cache or an automatic warm-cache restoration package. Missing/changed/added/removed snapshot objects are retained as failure evidence and prevent acceptance.

All helper SHA256 file hashing, including the potentially multi-GiB compressed archive, now streams in 1 MiB chunks. The original collector is unchanged. Final acceptance independently recomputes both runtime audit `state_sha256` and `command_log_sha256` from the retained files and checks the recorded runtime guard identity. It also rechecks actual committed workflows/root selection, all installed source bytes, generated audit, before/after snapshot, all owned `.olean` presence and archive SHA.

`FINAL_ACCEPTANCE.json` can be created only after every preceding gate succeeds. Its scope is the exact ABI closure plus the separate diagnostic group; whole P2/P4, old P4 failure resolution, concrete CheckedBlockTable instances, Q80 totals, original tree/guard execution and executable fallback/full-reader acceptance remain false. Runtime-only or static-config success is not proof acceptance.

## What was actually checked

Only immutable Git/source/log reads, exact byte identities, Python AST parsing and YAML syntax/static filter inspection were performed. No module in this packet was imported or executed. No materializer, stage, collector mode, runtime setup/audit/probe, Lean/Lake/LSP, kernel checker, guard, numerical producer, quota check, child agent, push, dispatch or cancellation was run. `STATIC_CHECKS.json` records these limited checks. T10 independently reviews the exact frozen v2 packet; root alone decides deployment timing and future execution.
