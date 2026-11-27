# Dictionary formal adapter — unbound review draft

`run_dictionary.py` and `install_dictionary_source.py` implement the independent
normal/kernel/full-owned acceptance route. Both retain **`INPUTS = None`**.
Their CLI entrypoints and loaders reject that state before any file lookup,
Git subprocess, worker dispatch or installation operation. They cannot be used
as a claim that the actual dictionary probe succeeded.

No cloud command, Lean command, Git write, source installation or old-worker
rerun was executed while preparing this draft. The previously published eight
AM probe-package files and the AK 9079-byte mathematical source are unchanged.

## Original APIs and scopes

The adapter loads the exact AM probe file (26465 bytes / SHA256
`93f5e3e93eaf6948ae63a072b65cae98bf90cd76bfe235b536499eaf3cecb106`) as a read-only
module. It reuses its existing `load_original`, `prepare_dependency_scopes` and
`retained_snapshot` functions. It does not call the probe's run/main functions.
The original AG driver, helper APIs and 21-target registry remain unchanged.

The normal and complete audit run uses the unchanged `g.run_owner`, which calls
the fixed `normal_one` and `audit` implementations. Complete existing acceptance
is read through `existing_owner`, `require_completed_existing_owner` and
`acceptance_binding`. The original root is preserved:

`/workspace/p1-complete-proof/20261126-p15-current-corrections-v1`.

A new dedicated formal publication selects only the dictionary owner. Its known
graph has 361 rows and its active graph has **289 sources**. Exactly **288
dependencies / 6048 artifact slots** are preserved. The four original initial4
supplier audits and 284 assigned fixed normal-context pins are revalidated
through the frozen probe readers. The separate original atlas witness remains
58 sources, including the 11 D-external modules. These are neither new selected
normal-build targets nor additions to the dictionary import graph.

The acceptance adapter uses the original AI/AE/AG preservation mechanism plus
the complete D288/W58 acceptance-backed snapshots, original supplier evidence
trees, and the actual successful dictionary probe evidence tree. An AG144
baseline or a two-artifact fixed-pin map cannot replace the full D288 inventory.

## Successful probe binding

Before activation, both files must receive the same actual `INPUTS` dictionary.
The required fields are:

* `canonical_source`: the exact AK 9079-byte / `b90556b0…` fingerprint.
* `probe_publication`: AM `45e8de70fb3045b04f3ef3ad2ff364c7ee2f390c`.
* `probe_job`: the real successful outer job, only after its terminal result.
* `probe_document`: bytes/SHA256 of the actual successful RESULT, also published
  under this package's `probe/ACTUAL_DICTIONARY_PROBE_RESULT.json`.
* `geometry`: an explicit prior-state binding as described below.

The original queued job `job_25681bd9f0064b41a35257f9be71f58c` was reported by root
as rejected before starting. It must not become a successful probe identity.
The replacement job `job_b852fda8ce794982b7938d5f29b5a9a8` remains unbound in this
draft; only an observed successful result can supply its actual binding.

`read_probe` checks the retained source/result/entrypoint, serialized whole Lean
command, all-three-import no-build readiness, exact log, original before/after
observations and acceptance contexts, empty original owner slot, and unchanged
D288/W58 original receipts. The whole source must be the exact frozen AK file,
with one completed no-output Lean command, exit 0 and all preservation fields
true. A failed or changed-source probe does not enable installation.

## Preserving Geometry without adding a dependency

The dictionary does not depend on Geometry. Its operational state nevertheless
must be preserved if Geometry has progressed before this formal publication.
`INPUTS.geometry` explicitly chooses one of two states:

* `unaccepted`: supplies the observed canonical Geometry source fingerprint (or
  explicit null). The live owner must have no history and all 21 artifact slots
  empty. If it gains normal/partial/accepted state, this mode stops and requires
  an actual accepted-reader binding.
* `accepted`: supplies its real accepting commit, the exact frozen
  `run_geometry.py` path and fingerprint, and a canonical fingerprint of its
  complete original read-only report. The adapter loads that immutable reader,
  calls its read-only `check`, and requires the original complete acceptance
  status, original accepting-run identity, all owned declarations, standard
  axioms, zero commands executed by the read, source equality and all 21 owner
  artifacts. The complete accepting-commit tree, install tree and probe tree
  are preserved before/after.

The accepted Geometry commit must differ from the dictionary's new formal
commit. The two owners cannot share a `ROOT/<commit>/runs` directory. Geometry's
source and artifacts never enter the dictionary's selected dependency map.
The `readonly_report` fingerprint uses the adapter's `value_fp` canonical JSON
encoding (sorted keys, compact separators and a final newline).

## Installation and formal execution

The independent installer only creates an absent canonical dictionary source,
or confirms already identical bytes before any owner history starts. It never
overwrites foreign bytes and does not follow symlink paths. All owner artifacts
must be absent, and started/foreign owner history stops installation. Existing
identical bytes are backed up in the installation evidence, as in the reviewed
single-owner installation pattern.

Both installation and formal acceptance use fresh, unique per-publication run
directories and the original serialized lane. Prior runs are inspected rather
than retried automatically. The installer writes its own terminal receipt with
zero Lean/kernel operations. The formal adapter reads that exact same-commit
installation chain before dispatch.

For the new owner, the original normal/audit APIs must produce the actual
single-owner normal build, named kernel replay and complete environment-owned
inventory. Counts are taken from the original audit; no declaration count is
pre-filled. Final no-build stock readiness and preservation checks must pass.
Complete prior owner acceptance uses only the read-only path. Partial normal,
partial audit or foreign accepting history is held without recompilation.

The outer dispatch saves worker failures and Git-after observations. The worker
retains after-context in `finally`. The result becomes accepted only after the
actual complete chain succeeds. The original 18/21 tally, its HOLD owners and
P1.5 OPEN state are reported separately.

## Local verification

`test_dictionary_formal_boundaries.py` contains only new adapter risks. Eleven
checks passed in the actual local run recorded by
`LOCAL_NEW_BOUNDARY_VERIFICATION.json`: zero-I/O unbound entries, incomplete
Geometry binding, full D288 artifact scope, two-slot/Geometry substitution,
exclusive exact installation, symlink/foreign-byte refusal, started/foreign
owner refusal, complete existing-owner read-only behavior, and rejection of
Geometry partial or normal-only state.

Mocked job IDs and receipt shapes occur only inside these local tests. They are
not copied into either draft's INPUTS and are not actual acceptance evidence.
No accepted test suite or old Lean worker was rerun.
