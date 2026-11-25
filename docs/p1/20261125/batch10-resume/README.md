# Resume the existing Batch10 sources

This driver covers **75 source owners: 22 ordinary repairs/donors and all 53 Higher partition modules**. Its proof-source snapshot is fixed to `99c1f8ba1dc453b21f47e30b667db0de93d73387`. It reads that commit with `git show`; it does not check out, reset, clean, or modify the source repository. No Lean proof, prior manifest, compiler guard, accepted helper, or acceptance runner is changed by this package.

The driver supplies normal-build continuation and produces a **pending plan for the unchanged e9 independent-kernel/full-owned runner**. Python fixture tests are not Lean, cloud, kernel, or P1 acceptance. Successful normal compilation alone is never reported as complete formalization.

## Commands

Extract the published `resume_batch10.py` outside the dirty cloud source repository. The following commands assume that extracted file is `/workspace/p1-batch10-resume.py`:

```bash
python3 -B /workspace/p1-batch10-resume.py --check
python3 -B /workspace/p1-batch10-resume.py --install-and-run
```

Defaults are `/workspace/goldbach-formalization` for Git object reads, `/workspace/blue-member-build` for existing sources and objects, and `/workspace/p1-complete-proof/20261125-batch10-resume` for new receipts. `--source-repo`, `--project`, and `--receipt-root` allow explicit paths. Execution requires the original prepared cloud project and the existing pinned guard, serializer, runtime states, and full-owned audit template. No resource or environment overrides are introduced.

`--check` reads only Git objects and project files. It verifies all 75 actual preimages/postimages, all prospective project dependency sources against the fixed Git tree, input hashes, and the four protected P1 sources. It invokes no Lean/Lake command, creates no receipts, and changes no source. The local current-snapshot check found a 614-module project source closure.

`--install-and-run` enters the existing single validation lane and repeats source preflight before writes. It adapts the ordinary manifest to the unchanged Batch5 installer. That installer backs up the 22 ordinary preimages and old Higher facade. The 52 new providers require actual absence or an exact postimage; occupied paths, including dangling symlinks, are rejected during complete-batch preflight. Exact postimages retain their original inode and timestamp.

Normal builds run Core, the 51 proof units individually, the facade, then the 22 ordinary modules in dependency order. Every build has a no-build direct-import gate. The facade is blocked when a provider is unavailable, so it cannot cold-build all guards. Independent modules can continue after a failure. Existing runtime limits and compiler/checker choices are preserved.

The coordinator preserves complete worker stdout while relaying compact `NORMAL_START`, `NORMAL_PASS_AUDIT_PENDING`, `NORMAL_REUSED`, and failure records. A normal-build failure includes at most 3,000 characters from its actual diagnostic log; the complete log remains in the receipt directory.

## Interruption and reuse

Run the **same published driver, source snapshot, runtime, and receipt root** again after an interrupted task:

```bash
python3 -B /workspace/p1-batch10-resume.py --install-and-run
```

Each successful owner is recorded atomically in `normal/<module>/NORMAL_PASS.json` before the next owner starts. Reuse requires its exact source and five outputs, project source closure, dependency object/trace hashes, configuration/runtime hashes, command receipt, complete raw log, and actual single-owner `Built` entry. Stock no-build readiness must also still pass. The successful normal command is not repeated.

An existing ready object without a matching normal provenance receipt is reported as `READY_WITHOUT_NORMAL_PROVENANCE`; it is neither credited nor rebuilt. This also covers interruption after Lean completed but before all provenance could be frozen. Stale or changed receipts are reported and preserved. Source installation attempts use distinct backup directories, so partial installation can resume without overwriting earlier backups.

## Independent acceptance remains explicit

After the normal phase, `pending-audit/<binding>/AUDIT_PLAN.json` contains only actual validated normal successes. Its companion `PENDING_COMMANDS.json` gives the exact two existing-runner commands: `--prepare-only`, then **only populated lane 0** inside the existing serializer. The default e9 two-lane launcher is not used with an empty lane. The copied runner must retain SHA256 `e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1`.

A partial plan explicitly lists missing Higher owners and cannot establish acceptance of the whole partition. Complete Higher acceptance needs normal, independent kernel, and full-owned evidence for the union of Core, all 51 proof units, and the facade. The earlier audit12 and old probe receipts are never scheduled again.

A pending plan can be reconstructed from existing durable successes without invoking any compiler or changing sources:

```bash
python3 -B /workspace/p1-batch10-resume.py --audit-plan-only
```

Review or reuse an existing audit receipt before running the generated commands. The preparation command creates its target directory exclusively; do not run preparation again for an already-prepared audit. This driver does not execute or resume the separate kernel/full-owned audit automatically.

## Local verification

```bash
python3 -B docs/p1/20261125/batch10-resume/test_resume.py
```

The focused suite tests complete-batch refusal before any write, payload integrity, absent providers, exact postimage no-ops, dangling symlinks, interrupted normal resume, dependency/receipt tampering, unknown ready objects, facade blocking, source-snapshot scope, partial audit boundaries, runtime guard integrity, and live relay with complete raw-log preservation. Only the relay test runs a small ordinary Python subprocess; compiler responses in the normal-flow tests are explicitly local fixtures.
