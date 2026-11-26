# Frozen eleven-owner runner input contract

`family_run.py` consumes existing same-byte acceptance; it never runs a supplier proof.
The first interface needs exactly 625 suppliers (624 canonical and the accepted generic).
The source package is fixed to 122656 bytes, SHA256
`457b87938ea4f363ab9ef8a6049173c5577f922bd5a133213ccfdd026001dce5`.
No source, audit, old receipt, or old log is rewritten.

## CLI

```sh
python3 /ABS/CODE/family_run.py \
  --stage /ABS/NEW_STAGE \
  --source-root /ABS/EXTRACTED_SOURCE_PACKAGE \
  --source-archive /ABS/cell01-original-floor-family-v1.tar.xz \
  --runtime /ABS/RUNTIME.json \
  --join /ABS/INTERFACE_JOIN.json \
  --attempt interface-pilot-v1 --rss-gib 14 --wall-seconds 1800 --max-new-steps 3
```

Use `--validate-only` first: validates and installs exact inputs, writes the immutable
owner context, invokes zero proof commands. Use a **different** attempt ID for execution.
One `--join` may be repeated per owner in the frozen eleven-owner order. A continuation
reuses all validated prior stages and creates only missing stages. Stop after the
interface by supplying its join alone. Its three accepted steps produce
`PAUSED_ACCEPTED_PREFIX`, accepted_steps=3, accepted_owners=1. This is a successful
pilot, not eleven-owner success. Final success requires 33 chains and a read-back-verified
new-evidence archive. All outputs keep `P2_6_complete_claimed: false`.

The stage has one `project/` and one `objects/` namespace. Immutable per-owner input
snapshots are `inputs/<owner basename>.json`, contexts are `contexts/<basename>.json`,
and accepted anchors are `accepted/<basename>/{normal,kernel,owned}.json`. Later joins
may add required suppliers without changing prior owner snapshots. Code, runtime and
source-package pins must remain unchanged in this stage. Keep each deployed code release
in its own immutable directory.

All paths are absolute, canonical, non-symlink paths. The stage must be disjoint from
every code/source/runtime/evidence provider root in both ancestor directions. A supplier
object is hardlinked; no cross-device copy fallback is provided. An accepted object,
seal, successful raw result, or index with lost evidence stops continuation. It never
permits proof replay. Failed normal attempts with surviving output require explicit
preservation/restoration before continuation; no object is silently overwritten.

## Shared file identity

Every `pin` below means `{ "path": "/absolute/original/path", "bytes": 123,
"sha256": "64 lowercase hex digits" }`. Current source/object pins use current paths.
Historical references keep their original paths, bytes and hashes. Register each
historical body that the validator reads through the exact map below, even when its
current path equals its original path. No fallback path guessing occurs.

## Per-owner join

```json
{
  "schema": "p26_family_owner_join_v1",
  "module": "ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorInterface",
  "read_roots": ["/ABS/CANONICAL_EVIDENCE", "/ABS/GENERIC_STAGE", "/ABS/OTHER_PROVIDERS"],
  "bindings": [
    {"original": {"path":"/ORIGINAL/RUN.json","bytes":123,"sha256":"..."},
     "current_path": "/CURRENT/RUN.json"}
  ],
  "canonical_contexts": {
    "row000_23rd": {
      "run": "PIN: original 23rd RUN.json",
      "input": "PIN: original 23rd INPUT_FINGERPRINTS.json",
      "result": "PIN: original 23rd RESULT.json",
      "records": [
        {"mode":"normal","receipt":"PIN: original accepted normal seal"},
        {"mode":"kernel","receipt":"PIN: original accepted kernel seal"},
        {"mode":"owned","receipt":"PIN: original accepted owned seal"}
      ],
      "closure_refs": ["PINs: original historical closure/addendum files in INPUT.files"]
    }
  },
  "suppliers": [
    {"module":"ImbalancedChen.EXAMPLE", "source":"PIN: live source",
     "object":"PIN: live object", "sidecars":[], "kind":"canonical",
     "canonical_context":"row000_23rd"},
    {"module":"ImbalancedChen.P2OriginalSaving19OriginalFloorTransport",
     "source":"PIN: live source", "object":"PIN: live accepted generic object", "sidecars":[],
     "kind":"three_mode", "provenance": {
       "run":"PIN: actual generic-v2-r14 attempt RUN.json (or its CONTEXT.json)",
       "input":"PIN: generic INPUT_FINGERPRINTS.json",
       "index":"PIN: actual successful generic RESULT.json",
       "records":[
         {"mode":"normal","receipt":"PIN: actual accepted normal seal"},
         {"mode":"kernel","receipt":"PIN: actual accepted kernel seal"},
         {"mode":"owned","receipt":"PIN: actual accepted owned seal"}
       ]
     }}
  ],
  "external_imports": ["OPTIONAL exact nonproject import list for this owner's owned audit"]
}
```

The explanatory `"PIN: ..."` strings above must be replaced by identity objects.
`suppliers` must equal the owner's transitive source dependency closure minus all new
owners, **not all 791 suppliers for the pilot**. Source pins are checked against the
frozen package. Canonical objects/sidecars must equal the original INPUT canonical table
and object union. `closure_refs` must include the original
`INPUT.supplier_kernel_addendum`, with the historical pending boundary preserved.

The historical resolver reads the following bodies, so bindings are required for each:
RUN, INPUT, RESULT/index, each accepted seal, command result, command, log, any seal
`run` and `context`, owned audit source, owned-declarations, module-byte-context, before
and after byte checks, and closure/addenda. The raw INPUT's full body is retained; its
unused supplier bodies are not automatically copied or recompiled. Current supplier
source/object/sidecars are pinned directly and do not need self-bindings unless another
historical reference resolves them.

For finite rows002–143, `kind: three_mode` uses the actual RUN, INPUT and SUCCESS (or
the complete accepted-prefix PARTIAL) as provenance. The three receipt refs point to
the original `{normal,kernel,owned}-result.json`; these batches have no separate
ACCEPTED_STEP wrapper. Reused result refs remain unchanged. The full selected index
must cover its exact completed row-major triples. C-prefix098–106 never credits107–143.

Only row001 may use `kind: remote_verified_predecessor`; its provenance must be the
exact `evidence_store.verify_row001_remote` record: `mode`, `module`, `summary`,
`mcp_task`, `review_script`, `task_id`, `project_id`. The summary schema is
`p26_row001_remote_predecessor_join_v2`. The blocked archive/full receipt group cannot
be registered, resolved, reconstructed or exported. Only the independently permitted
source/object/sidecars and compact reviewed summary cross this boundary.

## Runtime JSON

```json
{
  "schema":"p26_family_runtime_v1", "mode":"complete_tree",
  "lean_binary":"PIN: actual stock lean binary",
  "leanchecker_binary":"PIN: actual stock leanchecker binary",
  "runtime_roots":["/ABS/PACKAGE/lib/lean", "/ABS/MATHLIB/.lake/build/lib/lean"],
  "runtime_trees":[{"root":"/ABS/ROOT","files":123,"file_bytes":456,"sha256":"..."}],
  "native_library_files":[],
  "external_modules":[{"module":"Lean.EXAMPLE", "object":"PIN", "sidecars":[]}],
  "external_imports":["Lean.EXAMPLE"],
  "accepted_module_context":"PIN: accepted generic owned module-byte-context.json"
}
```

`runtime_roots` is the external `LEAN_PATH` search order, excluding the new project
object root and normally excluding the toolchain default lib/lean. `runtime_trees`
uses the **unchanged** `GenericFloor_verify_v2.tree_signature` algorithm and must cover
every search root and the entire toolchain `lib` directory. Existing accepted P1
generic signatures can be reused only at identical current paths and exact bytes.
Every complete tree is rehashed before and after every new proof command.

`external_modules` is the fixed actual provider-byte inventory, same shape as
`GenericFloor_verify_v2.module_byte_context`; paths must agree with actual search
precedence. Only nonproject names belong here. They must match the accepted generic
module-byte-context by bytes and sidecar suffixes, and that context pin must be bound
by an accepted supplier owned seal. `external_imports` is the exact inventory expected
for the new audit; a per-owner join may override it with a subset of the same fixed
external modules. Unexpected or absent imported modules fail acceptance.

Native files outside covered runtime trees may be explicitly pinned in
`native_library_files`. The runner uses a sanitized environment (stock toolchain PATH,
fixed LEAN_PATH, one thread, C.UTF-8), with no inherited loader injection variables.
Sparse runtime materialization is deliberately not implemented here.

## Local checks

```sh
PYTHONDONTWRITEBYTECODE=1 python3 test_family_run.py
```

Tests are synthetic negative/recovery checks, not Lean proof evidence. The unchanged
vendored helpers have fixed SHA256 pins in `family_run.py`. `CODE_MANIFEST.json`
freezes the authoring files; the coordinator must also pin the transferred release.
