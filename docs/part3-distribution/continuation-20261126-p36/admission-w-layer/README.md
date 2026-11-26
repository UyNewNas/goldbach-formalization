# P3.6 complete-word square inputs and full W layer

This increment reuses seven existing original-U5 modules and adds
`ImbalancedChen.P3OriginalU5FullWLayer`. Its mathematical scope and remaining
connections are recorded in `MATHEMATICAL_SCOPE.md`. It does not close P3.6:
`whole_p36_closed=false` and `currentVerified=false`.

## Verification checkpoint

The frozen source is `8495b3b274a046060faf2ce9020b2588665634c0`.
The original eight-owner task is `job_0bca8172a771479791602aa1ce575fbf`,
run `20261126T052649.111088Z`. The original gate returned `VERIFIED_OWNED`,
exit 0: all eight strict compilations, all eight exact kernel replays and the
complete defining-module inventory audit passed. Full evidence recovery and
local verification also passed. `ACCEPTANCE.json` records the accepted scope;
work-branch publication is tracked separately from this mathematical checkpoint.

The group has 313 complete declaration records. Across the prior seven groups
and this group there are 35 defining modules and 727 unique full names, with
no duplicates or conflicting types: 513 theorem, 180 definition, 9 inductive,
16 constructor and 9 recursor records. These are inventory counts, not a count
of newly written mathematical theorems. The new W module contributes 7 explicit
theorems, 1 explicit definition and 11 generated theorem records. The seven
other owners are reused source brought through the original formal gate.

| Owner | Role |
| --- | --- |
| `P5OriginalU5NativeRootCover` | Exact original root-level regrouping |
| `P3OriginalU5FreshFifthSquareSupplier` | Actual checked fresh-fifth source squares |
| `P3OriginalU5AllSourceSquares` | Complete source-word square provenance |
| `P3OriginalU5AllSignedSquares` | Actual small-factor attachment and selected-mask complements |
| `P3OriginalU5RootVInputs` | Actual root-V allocator inputs |
| `P3OriginalU5CoarseRootV` | Finite auxiliary coarse cover and V cell margins |
| `P3OriginalU5RoughEndpoints` | Original rough-word integer endpoint squares |
| `P3OriginalU5FullWLayer` | Exact closed W layer and signed complement partition |

The first seven are reused source. Four needed concrete elaboration/strict-lint
repairs; the new W source passed its first actual strict diagnostic unchanged.
Initial source hashes are in `INITIAL_REUSE_AUDIT.json`, and each frozen
attempt has its own immutable source bundle, source manifest record and original
terminal capture under `source-snapshots/` and `attempts/`.

## Frozen source recovery

The new source bundle extends `ebb6209fe06437c5522881030fc7c41c827a34ff`.
That prerequisite is recovered from the preceding normalized-density bundle.
Its own prerequisite, `d1db3a39797ec5e6427bce3e62c42b67c98b1492`, is an ancestor
of the published baseline `b3f306cc3b430fc40c3b3ec4110d323443d2f609`.
From a complete clone containing that baseline:

```sh
git fetch docs/part3-distribution/continuation-20261126-p36/normalized-density/source-snapshots/normalized-density-source.bundle refs/heads/compile/p36-normalized-density-20261126:refs/p36-evidence/normalized-density-20261126
git bundle verify docs/part3-distribution/continuation-20261126-p36/admission-w-layer/source-snapshots/admission-w-layer-source.bundle
git fetch docs/part3-distribution/continuation-20261126-p36/admission-w-layer/source-snapshots/admission-w-layer-source.bundle refs/heads/compile/p36-admission-w-layer-20261126:refs/p36-evidence/admission-w-layer-20261126
git rev-parse refs/p36-evidence/admission-w-layer-20261126
```

The final output must be `8495b3b274a046060faf2ce9020b2588665634c0`.
The bundle SHA-256 is
`df1fc846038be7f717be20d1ea941dc91b0b8b4dcf29b273893938adcf663787`.
The exact ordered owner manifest SHA-256 is
`f8c45ff830bc7f5e4468eb4a62dc5f45ce7a4b4435149ff83c79b888c5fbb919`.
The previous exporter and every original compiler/auditor file remain pinned.

## Evidence layers

`export_group_evidence.py` uses the previous exporter's original multi-owner
validators and archive implementation. The inner receipt retains its original
unknown singleton-runtime field. The outer group receipt separately binds the
original eight-owner runtime capture, source manifest, report, base receipt and
archive. Export inputs from the frozen original wrapper are checked again
against the original MCP terminal before acceptance or publication.

The only added historical compatibility pin is the exact RootQ dependency
report and successful compile stage, documented in
`validation/ROOT_Q_COMPATIBILITY_REVIEW.md`. The old report remains FAILED;
it supplies no standalone owned credit. Regression-fixture limitations and
independent reviews are recorded in `validation/INITIAL_ADAPTER_REVIEW.md`
and `EVIDENCE_ADAPTER.md`.

Local group verification and `validation/crosscheck_inventory_terminal.py`
perform no Lean compilation. The latter compares complete inventories with
original audit logs, counts unique full names across the prior seven groups
and this group, and checks the exact original strict/replay/audit terminal
records. Private diagnostic success never substitutes for the original gate.

The original report SHA-256 is
`dd61e7c35401d96c0cfbc22831411a3d2bc91f05e8e2918b16b1579711ad0529`.
The group receipt SHA-256 is
`34a4dded99425bd670e325dba6fbff3461626d64bda092e8f681a75cb6365dab`.
The 39,429,272-byte archive SHA-256 is
`9cce188eb1112d1ebaafef1c5b58ebccc5779a5c9a1dbbbadc019bbe76b8782a`.
The five original files were transported by additive artifact commit
`59cf6341935bc0b8b780526e2d9d2f12d5f1a893`; both the GitHub API readback and
the local exact-blob recovery agreed with that commit. Original runtime
before/after hashes for all six tools are identical and match the original
MCP terminal. The complete audit observed only `Classical.choice`, `Quot.sound`
and `propext` as transitive axioms.

After restoring the frozen source objects as above, run from the repository root:

```sh
mkdir -p .lake/p36-local-evidence-temp
TMPDIR="$PWD/.lake/p36-local-evidence-temp" python3 docs/part3-distribution/continuation-20261126-p36/admission-w-layer/export_group_evidence.py verify --project "$PWD" --source-commit 8495b3b274a046060faf2ce9020b2588665634c0 --evidence-dir docs/part3-distribution/continuation-20261126-p36/admission-w-layer/accepted-group --group-receipt-sha256 34a4dded99425bd670e325dba6fbff3461626d64bda092e8f681a75cb6365dab --owner-manifest-sha256 f8c45ff830bc7f5e4468eb4a62dc5f45ce7a4b4435149ff83c79b888c5fbb919 --runtime-binding-sha256 0831ee56de1aa406228c119fc0162cee20a8d237516064e127b3d7b298cc3dc8
python3 docs/part3-distribution/continuation-20261126-p36/admission-w-layer/validation/crosscheck_inventory_terminal.py --evidence-dir docs/part3-distribution/continuation-20261126-p36/admission-w-layer/accepted-group --attempt 006 --output .lake/p36-local-evidence-temp/crosscheck.json
```

`accepted-group/LOCAL_VERIFICATION.json` and
`validation/INVENTORY_AND_TERMINAL_CROSSCHECK.json` retain the actual successful
outputs. The independent crosscheck matches all 41 original formal command-end
records against the original report, including the 17 strict/replay/inventory
stages and their archived logs. It also confirms that all prior 27 owned source
files are byte-identical to the published baseline.

The local execution environment briefly disconnected after artifact publication.
P3 recovered the same five pinned files in an isolated fallback directory, but
performed no additional Lean run or formal acceptance. The original local
workspace then recovered and completed the above verification. The interruption
and unused fallback attempt are recorded in `execution/RECOVERY_INTERRUPTION.json`.

## Proof repairs and failed attempts

| Attempt | Observed result and response |
| --- | --- |
| 001 | Original strict compile stopped at an unnecessary tactic-sequence focus in AllSourceSquares. Only that proof expression changed. |
| 002 | Original strict compile passed the first four owners, then found four RootV elaboration failures. Targeted unfolding, names and equalities were made explicit. |
| 003 | Private diagnostics had an empty namespace-directory shadowing error; the original group gate did not run. File-level cache symlinks repaired the diagnostic setup without modifying the original cache. |
| 004 | Private strict RootV and W checks passed. CoarseRootV exposed finite-coordinate simplification and B-name ambiguity. Explicit coordinate goals and `VariableEnvelope.B` resolved the original intended expressions. |
| 005 | Private CoarseRootV passed. RoughEndpoints needed the existing endpoint lemma's cap/rank parameters and identity map made explicit. |
| 006 | Private CoarseRootV/RoughEndpoints passed, followed by the original eight-owner strict/replay/inventory gate. The full acceptance outcome is recorded separately. |

No mathematical hypothesis or conclusion was weakened, and no original lint,
driver or audit check was disabled. Existing donor headers recording their
earlier source-only state are retained as historical source bytes; the actual
formal acceptance record controls the verified scope.
