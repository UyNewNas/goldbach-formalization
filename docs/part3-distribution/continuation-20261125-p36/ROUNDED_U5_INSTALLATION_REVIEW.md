# Rounded U5 canonical installation — independent source review

Status: **PASS — source installation only; no Lean compilation or acceptance credit.**

This review checks the canonical installation against the already reviewed, frozen source packets. It does not repeat their mathematical review and does not expand the active P1 EXTRA4 task.

## Source bindings

The integration record is `ROUNDED_U5_INTEGRATION.json`. Its parent/frozen reuse packet is `92a7e0062be2d180a92ecbcda7368b77a82f506c`; the beta packet is `4ee6c7c560a5c202ea73b28522d749faa6c303fb`; the retained old P15 source is pinned to `c6b89774822580c731a236ac66dcd7466ac8a0e6`.

All 11 canonical files match their recorded SHA-256. Ten were compared byte for byte with `git show` at the stated frozen commit and path. `P2ActualResidualUniverseMass.lean` was independently fetched from the exact P15 raw GitHub URL and compared byte for byte: 5,039 bytes, SHA-256 `f7a2ddd51c2be9df092abac6adc4f19886642164c9389edaec84037b97d8de21`.

The complete per-file bindings and independent comparison methods are in the companion JSON.

## Actual import graph

Imports were reparsed from the installed canonical sources with the frozen runner parser, without invoking Lean. All 274 selected source hashes match the new manifest. The previous 264 source hashes and bytes are unchanged. Starting from the 11 manifest targets gives exactly those 274 project modules, with no missing project import and no dependency cycle.

The actual full import graph is identical to the reviewed beta preflight graph. The 272-module reuse preflight project graph is also identical on its full recorded domain. All corresponding reviewed source hashes agree. There are 117 explicit external imports; none is new relative to the old selected sources' actual imports.

The count is consistent: 11 newly installed canonical files comprise nine newly selected files and two compatibility-only files. The already present, unchanged `UpperCoefficientPerturbation` becomes newly reachable. Thus the selected closure increases by 10, from 264 to 274. All seven compatibility companions remain outside the selected dependency graph.

## Tool and execution boundary

The tracked verification tree remains `879002f0dc10ca87c6c6069e13bdd7b2352cdfd2`, with no tracked difference from the frozen parent. Two pre-existing untracked Python bytecode cache files were observed and left untouched; they are listed in the JSON. Final source, manifest and integration-record snapshot rechecks passed.

No Lean command, compilation, kernel replay, axiom audit or remote task was started for this review. P1 job `job_bcdf2f96240744f2a9236f9da384f25b` remains the original four-target EXTRA task at initial pin `45428d4ef7eac2f19dfd17a3d3a9a4d0903296ce`. The manifest's 11 inventory targets are not that task's owned scope.

Manifest before: `ba82cc31a3931c89cf86f59ffe8edbf0f007946df3dcf16e79f99304b69f2965`.

Manifest after: `f77468ef3bbc9f49294df0242079a58594ceae0679cc5d4d038c3f12a2861d4d`.

The new source installation is pending compilation. This review does not close P3.6.
