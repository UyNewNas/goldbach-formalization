# Four repaired targets: bounded validation caller

`retry_four.py` installs and validates only the four owners in
`SOURCE_REPAIRS.json`, using source commit
`220c14630ffd266f824bdbf0977147ecb740c0dd`. The receipt root is fixed at
`/workspace/p1-complete-proof/20261125-batch11-four-repairs-v1`.

## Invocation

Run the source-only preflight in the selected cloud environment:

```sh
python3 -B retry_four.py --check
```

After reviewing and publishing the caller, execute:

```sh
python3 -B retry_four.py --run
```

The read-only check also accepts explicit `--source-repo` and `--project`
paths for local verification. Execution is restricted to the existing cloud
project and source repository.

## Existing mechanisms and receipt boundaries

The caller reads exact Git objects and pins the unchanged Batch5 helper,
Batch6 operations, e9 auditor and Batch10 utility module. It uses only the
Batch10 module's source-independent snapshot, file, runtime and lane-lock
utilities; its fixed historical source constant is never changed.

All four existing source preimages and their dependency sources must match
before installation. The unchanged Batch5 installer provides whole-batch
preflight, exclusive preimage backups, exact-postimage reuse and atomic
replacement. The original four terminal source hashes and the dirty source
Git worktree are preserved.

One original lane-0 serializer covers installation, sequential normal
attempts and the explicit populated e9 lane. Each normal build requires
current direct dependencies and exactly its own genuine `Built` header.
The durable per-owner `NORMAL_PASS.json` binds source, complete project
closure, dependency `.olean`/`.trace` objects, configuration, runtime,
command/log and the source plus five generated outputs. Independent failures
retain their logs and do not suppress other targets.

Rerunning validates and reuses completed normal receipts. A ready target
without a complete normal receipt is held for inspection. Successful normals
enter an immutable e9 plan; e9 performs stock readiness, named `leanchecker`
and the full environment-owned type/axiom audit. Completed audit subsets are
validated and reused. An existing partial audit is held without overwriting
or automatically rerunning it. Empty lanes are never invoked.

The caller does not schedule the other 71 Batch10 owners. Their original
normal and audit receipts remain separate. `all_four_accepted` requires all
four complete audit receipts; every result keeps `whole_P1_complete: false`.

For subsequent unchanged owners at this same source commit, the callable
`context(project, module, graph, sources, helper, primitives)`,
`normal_valid(..., project=...)` and
`normal_one(..., root=..., project=...)` functions expose the same per-owner
provenance checks. The caller's CLI, source installer and audit scope remain
restricted to these four repairs.

Local preparation verification: Python `py_compile` passed and the read-only
check matched all four targets and their 342-module source closure. These
checks invoke no Lean, Lake or compiler service and establish no normal,
kernel or full-owned acceptance.
