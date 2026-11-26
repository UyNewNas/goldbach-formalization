# Independent review of historical compile-report compatibility

**Verdict. Ready for the real evidence export.** Exporter SHA-256 `003d628292e0b1d067e9f87d3aad6b2c6f2a64db5b117e06cbe6bbf37743fcf5` accepts a narrowly specified set of earlier successful dependency compilations. Actual acceptance of a singleton still requires original report and log bytes, all live export checks, receipt transfer, and local verification.

| Git revision independently read | SHA-256 of verification/p36/compile_p36_local.py | Distinct prior report paths in diagnosis |
|---|---|---:|
| edc2e68c360bf66bd33e4a3a5211cafd6d95f218 | 229fbe9720e65982fd0241b7ddafe7f06e8894e19d128a6ac4ea255860945de9 | 1 |
| d90a01b0a388893dcf71bab0acf5bde259b93050 | 3ca5c1e971324ea770e0494fbbabcdc162c0cf9db036816e6d692cb24cdfa733 | 3 |
| e4ad395e4901628d85a27d17d0f87a16ea943433 | 895a8bc67d6c28e4db0ce6954344e20679cb581e3b861bafed469852d5ee5d30 | 12 |
| a65747d928f5d8110933ac14cb525e236680e189 | be263af86651402faf9d7c54e243a44f671177717dbfafca0b604bca4fcc5709 | 2 |

The diagnostic file SHA-256 is `5a87ea1b0b5eaa3801fb0bf51f84361ace01fa075354505381e2cbc1c51c8f86`. Its two parent runs identify 18 distinct earlier report paths with consistent hashes, writers and statuses. Seventeen earlier tasks finished FAILED and one finished COMPILED. The scope of evidence for each reused module is an individual successful compile stage.

**Compatibility.** Independently comparing four historical Git source blobs yielded identical syntax trees for digest_json, compile_command, object_hashes, can_reuse, the eight-field compile input map, and the successful record merging input fields, stage, key, exit status and object facets. Recursive signatures continue to bind imported signatures to the actual compiler identity, source, strictness, LEAN_PATH, trust and thread count. Runner source identity is recorded separately from that compile input. Older source resolution and namespace mirror policies differ. The current exporter independently checks the current run's complete graph, import resolution and object bindings. This review assigns no retrospective attestation of the entire old search environment.

**Whitelist application.** Lines 268–305 require the original earlier sibling run path and same schema, project and build. The code looks up the path before branching on writer. All 16 fixed legacy paths require both their expected writer and SHA-256 of the complete archived report. Relabeling a listed path with the present writer cannot bypass that comparison. Unlisted paths must have the present writer. Lines 309–318 and 442–465 require every candidate dependency to have an exact prior successful compiled action, matching recursive inputs, input key, compiler, objects and sidecars, command, exit, path, command header and log hash. No new permission was given to import an older runner for the present owner. Lines 575–577 separately expose each previous report and the limited dependency-stage scope.

**Independent checks.** Four focused tests passed covering the diagnostic-to-pin mapping, changed writer or bytes, unknown runner, failed or missing compile lineage and the historical regression graph. The sample for the pinned-report branch exercises a synthetic isolated fixture. No historical report obtained from the compiler host was passed through this review's local environment. No cloud, Lean, source mutation, index or branch operation was performed.
