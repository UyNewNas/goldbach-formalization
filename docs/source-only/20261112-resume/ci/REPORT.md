# Actions evidence inventory — 2026-11-12

Repository: UyNewNas/goldbach-formalization. Evidence retrieved read-only through the GitHub connector. Raw JSON snapshots are under `raw/`; exact job logs and run artifacts are retained below. Artifact ZIP SHA-256 hashes were checked locally against GitHub's API digests. No local Lean/Lake/LSP/guard execution was performed.

## Exact run inventory

| Gate | Run / job | Exact head | Conclusion / scope |
|---|---|---|---|
| Core | [43020290951](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43020290951) / 130561149621 | `eedb1361edec9c28f2ec56166bd719250b7e7e05` | success. Full project build; explicit round 4 targets; bundled leanchecker; root declaration/transitive axiom audit; complete round 3/4/6 type exports and historical conditional bridge. Artifact `core-verification-43020290951.zip`. |
| Stored 000–004 | [43033551155](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43033551155) / 130618353253 | `5db345d60c12ce03457a0a6174e0be7c8a65f1d6` | success. Compile + bundled-kernel replay + complete serialized types/transitive axioms for Stored000–004 and parent only; artifact marks `PASS_SELECTED_BLOCKS_ONLY`, 1,327 declarations; `whole_t01_accepted=false`. |
| Stored 005–008 | [43080955096](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43080955096) / 130733053017 | `4ba82a1b653fc2cb8ce73aa7c33d1d532265ea93` | success. Compile + bundled-kernel replay + complete serialized types/transitive axioms for Stored005–008 and parent only; artifact marks `PASS_SELECTED_BLOCKS_ONLY`, 1,067 declarations; `whole_t01_accepted=false`. |
| P4 latest validation | [43108198136](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43108198136) / 130816949339 | `fb34e16802e8d0dffdd7d77b3ab442fc84ad55ed` | run failure. 146-module exact closure compiled and candidate/closure kernel replay passed; full serialized declaration + transitive axiom export failed. First failure: job log line 3728, candidate root `CandidateAudit.lean:157:0`: `Serialized declarations and defining-module inventory differ for ImbalancedChen.FinitePiIntegral`. The command was `lake env lean -DwarningAsError=true CandidateAudit.lean`, followed by `verification/parts/p0/prepare_candidate_validation.py verify`. P4 artifact source receipt pins `ImbalancedChen/FinitePiIntegral.lean`, SHA-256 `22c7e16d66361c4aec2913237c8b8866db59575d36c50416805094e351f5c54c`. |
| P2 latest validation | [43115954951](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43115954951) / 130843878682 | `f12fde61ac82c5e001332dba4a5eca5f4eda24fb` | run failure during exact candidate + entire local closure compilation; kernel replay and declaration/axiom export skipped. First build failure (job log line 1086): `ImbalancedChen/ActualThirdOriginalPositive256LogRange32IntegerGuard.lean:125:50`, `Invalid field mp: The environment does not contain Function.mp`. Adjacent at line 125:23: `mul_le_mul_left` receives `0 < 128` where an inequality was expected; same module line 172:52, `linarith failed to find a contradiction`. Four additional failed modules followed: `P2ThirdTailCertificateTruncation`, `ActualThirdOriginalStoredNodeQueryLookup`, `ActualThirdOriginalP4ASymmetricBranchPermutation`, `ActualThirdOriginalSymmetricMassCeil`. Artifact is the retained closure/source/runtime audit. The current P2 repair commit `eb035a259f2f40853e9899f6d98af25852184fee` postdates this failing run and is not validated by it. |
| Stored 009–019 live | [43122130246](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43122130246) / 130864952699 | `356c3782e9428098a2fcbfb18c689bef264d84fa` | observed in progress. Compile step 10 passed; bundled-kernel replay step 11 was in progress at latest check; declaration/axiom export step 12 had not started. No artifact was yet available. Logs endpoint returned BlobNotFound while the job was live. |

The Core and Stored results describe only their exact run heads and named selected targets. Stored000–008 results do not establish any result for other main declarations, including main 24/26/27 responsibilities. This report records CI evidence only and makes no claim about mathematical applicability.

## Files

- ZIP artifacts and extracted contents are in this folder, named by run.
- Logs: `43020290951.log`, `43080955096.log`, `43115954951.log`, `43108198136.log`. Stored000–004 job-log retrieval returned a transport error; its downloaded artifact contains the batch build, kernel, and type logs.
- Raw API JSON: `raw/actions_api_snapshots.json`, `raw/live_43122130246_latest.json`; individual raw run/job/artifact JSON snapshots for Core and Stored batches also remain under `raw/`.


## Recent relevant Actions

Newest relevant runs in the 20-run API snapshot: 43122130246 Stored009–019 (in progress, head 356c3782); 43115954951 P2 repaired dependency closure (failure, head f12fde61); 43108198136 P4 compact profile closure (failure, head fb34e168); 43094090299 prior P2 validation (failure, head c6b5b8d6); 43080955096 Stored005–008 (success, head 4ba82a1b); 43073236934 prior P4 validation (failure, head d056bd56); 43064199752 P2 candidate closure (failure, head 20633f31); 43033551155 Stored000–004 (success, head 5db345d6); 43020290951 Core verification (success, head eedb1361); 43005584278 compile repair probe (success, head 82ced862).

