# Offline Cell05 evidence readback

Readback uses the authenticated v2 recovery export and v1 single-owner Shape stage. The failed v1 recovery capture did not produce a certificate. Obtain the archive size, its SHA-256, the reviewed v2 workflow manifest SHA-256 and the successful capture certificate SHA-256 from retained external records. Never infer those CLI values from the archive.

Run the recovery check first.

```sh
python -I -B readback.py --recovery "$RECOVERY_ARCHIVE" --recovery-size "$RECOVERY_SIZE" --recovery-sha "$RECOVERY_SHA" --workflow-sha "$REVIEWED_WORKFLOW_SHA" --certificate-sha "$CERTIFICATE_SHA" --capture-external-observation "$CAPTURE_EXTERNAL_OBSERVATION"
```

For a completed Shape archive, append the three archive arguments and independently retained capture-specific binding SHA-256.

```sh
--shape "$SHAPE_ARCHIVE" --shape-size "$SHAPE_SIZE" --shape-sha "$SHAPE_SHA" --binding-sha "$BINDING_SHA"
```

Every archive is read in memory. Exact exterior pins, safe unique regular file members, manifest inventory, member lengths and SHA-256 are checked before declarations or historical claims are interpreted. Producer source is compared with the reviewed local manifest and files. Capture outputs are checked against the original full snapshot, both different physical guards, recorded old-guard failure, legacy raw receipts, historical counts and the original stock runtime identity. For the new Shape owner, readback independently reconstructs the three command lines, compares input/environment/argv, witnesses, sealed results, same object, print names, raw ownership records and all 126 project imports.

The two small historical archives alongside this script were copied from UyNewNas/goldbach-formalization commit 46d7a9b20373700d7e862116344abfb28243289f, docs/verification/20261126-p26/cell05-connections13-prefix/evidence.tar.xz and docs/verification/20261126-p26/cell05-shape-repair/evidence.tar.xz. They were independently matched against the published 273708-byte and 153380-byte pins in the remaining9 boundary. The remaining9 evidence is read from the preserved local stage. No live historical proof or runtime file is modified or recompiled. An offline readback authenticates exported evidence and cannot run a live check of the P2 filesystem.

Only an exit-zero execution with real externally pinned artifacts can emit an offline verification result. Fixture checks, source review and this checklist do not confer acceptance.

## Archived execution layout

The Python files here are the exact sources that produced the retained reports; their hashes are in each report. The recorded shell commands preserve their actual absolute paths. This directory is an evidence copy and is not a drop-in installed command. To reproduce the offline check in another checkout, preserve the following layout under an arbitrary temporary root `BASE`:

- Copy this directory to `BASE/shape_executor_review/readback`. Both Python scripts and the two historical `.tar.xz` files must remain together.
- Point `BASE/materials/p26-work` at the complete repository checkout containing the frozen protocol and Shape executor.
- Verify the 403524-byte `cell05-remaining8-recovery/evidence.tar.xz` against SHA256 `e556b30c03235d395c2a90fbb3daf213e22806fa4bdf2520d7ddfc8821aaa2a4`, and extract its safe regular `stage/` members into `BASE/materials/recovery-20261127/remaining9-v2-exact`. Do not import any archived Python.
- Run `shape_readback.py` with `--archive` pointing to `cell05-shape-completion/shape-evidence.tar.xz`, `--external-success` to its `EXTERNAL_SUCCESS.json`, `--run-stdout` to its `RUN_TASK.stdout`, `--recovery` to `cell05-runtime-recovery/evidence.tar.xz`, and `--capture-observation` to its `EXTERNAL_OBSERVATION.json`. Use a fresh `python3 -I -B` process.

The actual accepted command is preserved in `SHAPE_READBACK_COMMAND.sh`; adapt only input locations for the new layout. No Lean/kernel command is part of this offline procedure. The first recovery-checker failure was a field-name typo and is preserved in `READBACK_CHECKER_ATTEMPT1.stderr`; the original proof archives were not modified.
