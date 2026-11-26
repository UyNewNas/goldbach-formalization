# Second Cutoff source repair: J payload, K updater

This updater replaces only `ImbalancedChen.P1OriginalSingletonCutoffData` in the P1 member project. The payload is fixed at J, `7c59a3d125d99010a501c14f1ecc60710483f918`: 12744 bytes, SHA256 `ceb0d90a99b41455124802c5446d16499e11207f1042b790f0646d4c19272b22`. The inspected I preimage is 12670 bytes / `d0fb57566d511f7ab4ef9270e71f53fb13b98d1b793feca0abacc24f2db02ccc`. The one exact splice normalizes the existing list coercion before the original rewrite. Every other published source and every literal import remains unchanged.

`--source-commit` names the future K publication containing this updater and its frozen manifest. It does not select a new payload, original acceptance identity or repair scope.

## Separate failure and acceptance identities

- Failed Cutoff: I `f21a8601d99ea33ec572223f5267415ca4ead8db`, job `job_dad68eb4d5fb48c588bd027157e85adf`; original RESULT and WORKER accept no current target and fail only Cutoff.
- Accepted HB: F `080d4178711ae042235104f7f4768649f51da2ab`, job `job_f0761da7e6124e818d654afef54ff5c5`. Its original F RESULT/WORKER, complete 21-artifact map and six acceptance receipts remain fixed. Its 3109-byte public summary remains published at H `f6fdd7fffe17803c60914bf28b39b55715d34464`.
- Support retains its complete original B acceptance and 109-source preservation context. Neither HB nor Support is recompiled or relabelled as accepted under I, J or K.

The source-only inputs at J are `docs/p1/20261126/p15-cutoff-bind-pure-repair/ACTUAL_I_METADATA.json` (17430 bytes / `19ac2fdc7e23f190a2a856445b33b85c722efd45b8bb97c1b4c67089ce6b22a4`) and `REPAIR_CANDIDATE.json` (6592 bytes / `4119a1b346879b9fadc93a390eb95ab3c7e951cf367a6503625af36bcaa74383`). The actual I normal attempt failed; this updater and its local checks grant no new owner acceptance.

## Fixed execution order

The updater loads the original published I driver and reproduces only its read-only preflight prefix for Cutoff: the real 68-source closure, 67 preserved dependencies, original HB@F full audit through `retained_hb_f_target`, eight old supplier owners and the fixed dependency pins. It never calls I `preflight([HB])` or constructs an I HB acceptance receipt.

The sole permitted active artifact is the inspected failed Cutoff `.setup.json`, 6328247 bytes / `22dcba10ea7d8e0dc81ef381e7624afe4f1db0d0cafd94b5ecd4ac82bae811ff`. The other 20 Cutoff artifact slots must be absent. The unchanged archive algorithm creates an exclusive 0600 full-byte backup, flushes and fsyncs it and its metadata, rechecks the original file identity and bytes, and removes only that fixed active path. A different artifact, fingerprint or partial archive holds for inspection.

After archival, the **complete unchanged I `preflight([Cutoff])`** must pass. Its only current initial owner must be fresh Cutoff; HB must still resolve through its F historical supplier identity. Only then does the original `h.install_sources` replace the single exact source and preserve its preimage. All 148 watched source/artifact rows, the original failure receipts, HB@F evidence, Support@B evidence, runtime, configuration and dirty Git state remain protected. The original guard and serialized lane zero are unchanged.

After publication, root can execute the retained script with the fixed K commit:

```sh
python3 -B <retained-published-updater.py> --source-commit <K-full-SHA> --check
python3 -B <retained-published-updater.py> --source-commit <K-full-SHA> --apply
```

The later selected Cutoff acceptance must require this updater's actual successful receipt. No additive installer is needed for this existing source.

## Local verification

`verify_updater_static.py` was adapted from the published I updater verifier and run once after all J pins were filled. It passed 1136 checks: 1080 per-source checks for the 360 I preimages, the single J delta and all import lists; 56 other checks, including three pure exact-splice rejection cases. Fourteen existing updater functions, including all archive functions, remain byte-identical to I. The verifier executes only the pure payload reader with local Git data; it does not execute a driver/updater entrypoint or the real audit API.

`STATIC_VERIFICATION.json` records the exact script and manifest hashes and the scope. Remote Delta independently reviewed the frozen 40037-byte updater and 18064-byte manifest and found no concrete blocker; that review was read-only and did not rerun the fixtures, Lean or any cloud task. Full Cutoff normal/kernel/full-owned acceptance remains pending the separate K execution.
