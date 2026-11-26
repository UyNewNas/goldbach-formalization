# P-anchored entrypoint with original PerGroup@O acceptance

This candidate continues the existing current-corrections entrypoint. Its mathematical source anchor is **P `b45d33fc0f8e2b2ac97a5919d5c7af120f11fa9f`**. PerGroup retains its original acceptance at **O `dc1e74ee5c15471d6dd22e4e2c609d5e79b0169d`**, task `job_cda017c5183c4b5ba80a8a2182f446ba`, `runs/attempt-00000`, audit `370ebae525106ac7bd2e`, 68 owned / 58 public declarations.

## Publication and invocation contract

Publish `run_selected.py` and `SOURCE_MANIFEST.json` at their existing canonical paths under `docs/p1/20261126/p15-current-corrections/`. The entrypoint publication commit is distinct from P; pass that actual commit as `--source-commit`. The unchanged self-byte check requires the executed runner and manifest to match that entrypoint commit. P remains the fixed source anchor and the publication of the PerGroup public summary.

The source change is limited to `ImbalancedChen/Part3AllKLambdaChartCorrection.lean`: 11,416 bytes, SHA-256 `9d739aab99a7873daaf25f649cca910d11f02a08ae22a32a70f517734df67962`. The other 359 manifest source rows and every literal import list remain unchanged. AllK provenance appends `docs/p1/20261126/p15-allk-first-compile-repair/REPAIR_CANDIDATE.json` at P; earlier reviews remain present.

First select only `ImbalancedChen.Part3AllKLambdaChartCorrection`: the live closure is 73 sources with 72 preserved dependencies. The manifest's `subsequent_13_targets` gives the remaining compile-candidate set, including AllK, with closure 157 and 144 preserved dependencies. The previous 14- and 15-target lists remain historical; selection rejects their accepted prior owners. Existing same-commit completed-owner reuse remains unchanged, so a subsequent invocation at the same entrypoint commit can reuse an already accepted AllK.

Before invoking either `--check` or `--run`, use the separately reviewed installation/retirement flow. The failed O AllK `.lake/build/ir/ImbalancedChen/Part3AllKLambdaChartCorrection.setup.json` is 6,329,098 bytes, SHA-256 `14330c5ee87da605a861559cdd3adb035302ef8e4aa90d3f20cf467b751e0b87`. Preserve its exact bytes in the designated failure archive before removing only that known failed setup artifact. Preserve all old O receipts, logs and accepted artifacts. This candidate performs no installation or failure-artifact cleanup; the unchanged fresh-owner gate rejects unexpected existing artifacts.

## Reuse contract

The new fixed `pergroup_o` adapter exposes PerGroup only through a temporary manifest view to the unchanged `historical_group` and `retained_owner` readers. The active set and state maps are shared. The permanent partition remains 21 targets, 17 accepted suppliers, 303 fixed dependencies and 19 unaccepted P3 dependencies.

PerGroup is the fifth historical prior and cannot appear in a new selected-target request. The original four mappings and functions remain unchanged. The AllK closure revalidates HB@F, Licensed@M and PerGroup@O; the 13-target closure additionally revalidates Support@B and Cutoff@K. Each keeps its original source commit and receipt identity.

The adapter pins the P-published `PERGROUP_O_PUBLIC_ACCEPTANCE.json` (6,477 bytes, SHA-256 `3d69364fab09231361e4f551c2318147966c092ba2e56f3c8292675d6fb196c6`) and the original O RESULT (39,901 bytes, SHA-256 `48934d443e7598fb71c8c20eead738e63af03b4fa7ad11f5c00943b723db2bee`) and WORKER_RESULT (39,785 bytes, SHA-256 `d0886d01d8b06fc23db731d730fdd05bcb2445faa9fc45799cab766df9bd6cfd`). It checks the original exact 14-target order, accepted PerGroup, failed AllK, unstarted remaining 12, exit 1, and absent original final stock-readiness record. The partial group stays failed.

It validates the six original receipt bindings, original context/Git pairs, and current source-plus-five/full-21 artifact identities before and after the unchanged full normal/kernel/owned-audit reader. No receipt is rebound to P or to the new entrypoint publication. No prior owner is compiled by this adapter.

## Local verification

`STATIC_VERIFICATION.json` records **116 passing checks**, including **62 unchanged original O fixture cases** executed by importing its frozen `verify_static.py` directly. The old 88-case receipt and verifier fingerprints are preserved; this record does **not** claim that all 88 historical cases were rerun.

All 38 original functions outside `source_manifest` and `preflight` are byte-identical. Those two functions reconstruct exactly to O when the fixed PerGroup classification and dispatch additions are removed. The actual source-manifest function checked the exact local bytes of all 360 sources, source provenance and all 303 fixed-dependency policies. Its local reader used fixed commit/path inputs; this suite did not independently query the remote publication.

New isolated fixtures cover partial-run identity, selected/inactive prior rejection, original receipt paths, original RESULT/WORKER disagreement, changed retained context, and full-21/source-plus-five changes before or during reader validation. Synthetic receipt readers and a generic-reader result model are explicitly identified. Their serialized fixtures do not claim the original raw RESULT/WORKER digests. The public summary and captured RESULT contents are actual inputs supplied by the independent O collection.

`build_candidate.py` reproduces the candidate from the frozen local O tree and exact adjacent P inputs; every input has a fixed size and hash guard. `verify_delta.py` runs the checks without invoking driver main, worker, installer, Lean, kernel, cloud or Git writes. These helper scripts require the frozen O local tree and evidence files; the production runner has no dependency on those scratch paths.

This packet adds no owner acceptance. The successful AllK no-output probe at P is a source/typecheck observation; new owner acceptance still requires the normal and full-owned audit flow. P1.5 remains incomplete.
