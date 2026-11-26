# Cell01 P3 exact supplier preparation

This is a local candidate for independent review. It has not run on P3 and does
not accept a new owner. `prepare_family_p3.py` invokes only source, byte,
runtime and existing-chain validation routines from the unchanged frozen
`cell01-family-run-20261126/releases/p3-v2` verifier. It never invokes that
verifier's main function, Lean, leanchecker, Git or any subprocess.

## Exact input and entry point

The concrete proposed paths are frozen in `INPUT_CONFIG_CANDIDATE_v3.json`.
The original v1 package remains a nondeployed candidate with its known runtime
prefix mismatch. The original v2 package and its actual P3 failure are also
preserved unchanged. Its metadata-only task stopped at the nullable source
locator guard before any provider or generated-input directory was created.
This v3 changes only the two optional locator reads: an explicit null denotes
unavailable source, and a nonnull reference must pass the frozen identity
validator. The complete 602-present/189-missing inventory regression passed.
After review,
the same bytes will be deployed as `INPUT_CONFIG.json` under the new control root
`/workspace/p26-continuation-557a12f3bcd7/cell01-family-p3-preparation-v3`.
The entry point is:

```sh
python3 -B /workspace/p26-continuation-557a12f3bcd7/cell01-family-p3-preparation-v3/prepare_family_p3.py --config /workspace/p26-continuation-557a12f3bcd7/cell01-family-p3-preparation-v3/INPUT_CONFIG.json
```

Every configured path is absolute and canonical. The future proof stage, source
package, verifier, input configuration, extracted provider, two extracted body
providers, the complete external runtime provider and generated input directory
are separate. The proposed preparation
root contains only this adapter and its two helpers, the exact frozen verifier, the
original 11-owner source archive and its exact 36-file extraction, three fixed
P3 inventories, the allowed canonical selected-body archive and manifest, and
the fixed configuration. It contains no compiled supplier object or row001
historical body.

The frozen verifier CODE_MANIFEST is 1800 bytes, SHA256
`34d65a335862bdc81a2f6df7c2a6c9fb511186e696759cb8b8a745b578bf62e9`.
The original source archive is 122656 bytes, SHA256
`457b87938ea4f363ab9ef8a6049173c5577f922bd5a133213ccfdd026001dce5`.
The adapter checks all frozen code and original source member pins before using
them. No generated or repaired Lean source is part of this operation.

## Physical supplier join

The exact old-supplier union is 791. The fixed P3 inventory supplies 602 current
source/object pairs at their existing canonical paths. The previously received
object transport supplies exactly 189 missing objects and 14 missing source
bodies, plus its exact manifest, for extraction to the new directory
`/workspace/p26-cell01-suppliers-v2-557a12f3bcd7`.

| Input | Bytes | SHA256 |
|---|---:|---|
| Object/source capsule | 39794840 | a16d07fe3489855e1c69a5c2658824b8b7fce7fc44ab527d3a88eb5e8451899b |
| Object/source manifest | 409031 | 8d001ee3a7bfbe4c2d6f7708c86b59977d3212053ba54bbe697143ed0a2064df |
| P3_PRESENT_FINAL.json | 450204 | 8d8c49452c45465f93d307a99f04abf2775ee094ce8dcff45e74c67702d7c217 |
| P3_MISSING_FINAL.json | 241935 | 60aa829ab21abf61b8e363cd8abd3235683f9c13fb6307e074cfc3fd284ea685 |
| P3_INVENTORY_SUMMARY.json | 6072 | 1379b5955b9bb350cb0e15cb752bcdc7cb33cb22ee0c20c55e33035e0e5421b3 |

All 791 live source/object identities are checked against the frozen source
catalog and their accepted provider pins. Their sidecar set must remain empty.
All source imports must match the catalog's project dependency edges. The nine
C-prefix sources already inventoried on P3 are read at the exact original
`cell01-rest-finite-v2/project` paths; the adapter does not guess other missing
source locations. No accepted supplier is compiled again.

## Original evidence bodies

Selected evidence packages preserve every original path/size/SHA identity and
map it to the exact unchanged bytes at a new content-addressed local path. An
embedded reference to another historical file does not cause that file to be
copied. Compact inventory summaries supply locators and fixed pins; they do not
stand in for any body that the frozen validator requires.

| Authority | How the actual original bodies are supplied |
|---|---|
| Canonical old suppliers and row000 original | Allowed canonical package: 21 original bodies, 22 regular archive members, including the original three-mode chain, original RUN/INPUT/RESULT, closure registries and kernel completion. The separate moment01 closure is included at its original byte identity. |
| Generic | Exact accepted generic-v2-r14 seals, context, original result chain, owned log/inventory and the original complete imported-module byte context, supplied by the P1 narrow package. |
| C-prefix rows 98–106 | Original fixed RUN/INPUT/PARTIAL and 27 accepted result/command/log chains plus their audit/inventory bodies, supplied by the same P1 package. Selection is anchored to the original fixed export manifest. |
| A/B/C-tail, 133 finite owners | Read at their original P3 stage paths, using the three RUN/SUCCESS pin pairs in the fixed inventory. The original index and all selected normal/kernel/owned chains are validated. |
| Finite row001 | Same-host reads only at its original P3 stage and original live supplier paths. No original row001 receipt/log/archive body is relocated or included in a package. |

The canonical archive is 329648 bytes, SHA256
`6ed9837ee38b7c94e6d6ca24e0f4f2e8d82fd7bdb8763531034d4ea6c0c9d97e`;
its manifest is 20170 bytes, SHA256
`da1b149115eef8011190a0cc08d21f80db2b67327ba9115fce8ad437a05caabf`.

The actual successful P1 generic/C-prefix package has 127 original references,
123 distinct body files and 124 regular archive members. Its archive is 2436040
bytes, SHA256
`ba07e0c42cb1e3b34da3353f0302ab3797fc10c9af36f85d58fdb543bfbf8cee`;
its manifest is 132787 bytes, SHA256
`3e009ff1f223705d2e52354776e41ebaceb40f6d9673b341c5f4fa78a196d241`.
That package must first arrive under the separate reviewed evidence transport
directory. The original three-file object transport remains unchanged.

The frozen row001 validator checks its fixed three receipt hashes, original
source/object paths, exact original RUN/SUCCESS/input relationships, original
399-supplier installation, 1596 live source/object pin checks, all original
input files, same-byte kernel completion and 292 owned declarations. It does
not open an old archive or execute a compiler. Generated joins and PREFLIGHT
retain only pins, paths, counts and the validation result for this exception.

## Runtime binding

The current stock Lean and leanchecker binaries must have the same bytes as the
accepted generic context. The adapter uses that context's exact 11517 external
modules. Canonical and generic owned logs must have that same external import
set, all finite owned imports must be a subset, and every current source/audit
direct external import must be covered.

By default, runtime roots come from the original P3 batch-A RUN.LEAN_PATH after
removing its exact `stage/objects` prefix. The original `cache_root` is a separate
historical supplier cache, as specified by Cell01Batch_verify.py and the original
finite exporter. It cannot replace the first LEAN_PATH root. The intervening
package roots must equal the original ordered `mathlib_package_object_roots`.
Canonical resolved paths preserve search
precedence. The fixed `runtime.additional_roots` has exactly one entry: the
new complete 515-module external provider. A reviewed configuration may specify
explicit standard `runtime.roots`; no fallback compiler is available.
The current object and every sidecar for each external module must match the
accepted generic bytes. The actual complete trees of every root and the entire
toolchain lib directory are sealed and checked by frozen `validate_runtime`.
Any runtime root exposing an ImbalancedChen namespace is rejected.

The external inventory includes exactly 515 modules outside the standard
Lean/Mathlib package set: MathlibNt (444), AnalyticNumberTheory (44), Architect
(9), and PrimeNumberTheoremAnd (18). The actual read-only P3 locator found 505
matching modules at two existing roots. Ten exact old MathlibNt objects were
missing. P1 task `job_3911445ef7364ea6a2e20066c714229f` packed those ten original
objects and rechecked them against the original generic accepted module context
(12878196 bytes, SHA256
`b36a9153969abb3cbac96c3d74bea3e0c366ca3a673cdfe7456a7e655f2241c0`).
The runtime capsule is 474128 bytes, SHA256
`2d2c7462f0cbec29ad7dca7d90a271748fd3ea477a5841a8b7884f75143e195f`;
its manifest is 10464 bytes, SHA256
`c680a64fc2ee71084a4158ddbeb5f5d6f7c41e42d66f267055bb0d5a43966a66`.
Its eleven regular members are ten `.olean` files and the manifest. There are
no sidecars, project objects, source bodies, receipts, logs or row001 files.

`external_runtime.py` creates the fresh provider
`/workspace/p26-cell01-external-runtime-515-557a12f3bcd7`.
The 505 existing modules and any sidecars required by their original context
are hardlinked at their exact bytes from
`/workspace/goldbach-p3/.lake/packages/goldbach/.lake/build/lib/lean` and
`/workspace/goldbach-p3/.lake/packages/LeanArchitect/.lake/build/lib/lean`.
Only the ten missing objects are written from the verified capsule. Every
planned member is pinned before the completion marker is written; extra,
changed, missing or partial state is refused. The old roots are never written.

This must be a single complete provider because the unchanged verifier chooses
the first root containing a namespace. A partial ten-module overlay would hide
the remaining modules in that namespace. The adapter uses the original
`module_byte_context` helper to resolve all 515 modules from the complete root
and compare every object and sidecar with the accepted context. The later
11517-module check and complete runtime tree seal remain required. No external
module is recompiled. The complete provider and final runtime have not yet been
validated on P3.

## Eleven immutable per-owner joins

After a single complete frozen runtime validation, the adapter validates each
owner's actual old-supplier closure using unchanged `validate_join`. It does
not mark a new owner accepted and does not require unresolved pins for an
uncompiled new owner.

| New owner group | Owners | Old suppliers per owner | Total project closure per owner |
|---|---:|---:|---:|
| Shared interface | 1 | 625 | 626 |
| Block000_015 | 1 | 663 | 665 |
| Other eight blocks | 8 | 642 | 644 |
| Complete endpoint | 1 | 791 | 802 |

Only after all old joins and the final frozen-input recheck pass does the
adapter write SUPPLIER_REGISTRY.json, RUNTIME.json, eleven joins and PREFLIGHT.json
under `/workspace/p26-cell01-family-p3-inputs-557a12f3bcd7`. PREFLIGHT's status is
`PASS_ALL_ELEVEN_EXISTING_SUPPLIER_JOINS_NO_PROOFS`. Its new proof credit remains
zero. This is not the later 33-step proof result or a P2.6 completion claim.

The later frozen runner must receive the source root/archive, generated runtime
and all eleven `--join` paths with
`--stage /workspace/p26-cell01-family-p3-stage-557a12f3bcd7 --rss-gib 12`.
The frozen runner owns sequential normal/kernel/full-owned execution and
reuses its preserved accepted prefix. Any initial three-step interface pilot
must use the same eventual stage and immutable runtime/join bytes. No earlier
accepted interface pilot exists to import. This adapter does not launch that
command. The runner's `--validate-only` entry point checks the first pending
owner; this adapter deliberately validates all eleven old joins beforehand.

## Preservation and recovery

Before any new directory is created, the adapter rejects destinations inside
the original OLD stage root, row001 stage, every inventoried old source/object
parent, either original external runtime root, the standard runtime roots, the
control package or any incoming archive directory.
PREPARATION_INPUT.json binds the exact configuration, all three adapter source files
and verifier manifest before extraction. A different configuration or adapter
version cannot reuse that output root. The same final Frozen check includes
all three adapter files, every frozen verifier file, all three fixed inventories,
the object capsule and manifest, both selected-body archive/manifest pairs, and
the exact external runtime capsule and manifest.
Each archive extracts only into a fresh directory, with regular, unique,
allowlisted members and pre-write/post-write size and hash checks. A complete
matching EXTRACTION.json permits read-only reuse of identical existing files.
Missing, changed, extra or partial extraction state stops; it is never replaced,
deleted or reconstructed automatically. The external runtime root similarly
requires its complete matching `PROVIDER.json` for read-only reuse; no partial
or changed member is repaired. Generated inputs use frozen `keep`,
which preserves identical bytes and rejects conflicting existing bytes.

The adapter leaves partial files for inspection after a failure. It never
touches an accepted proof stage or performs recovery by recompilation. A fresh
configuration/output path is required for an intentional reviewed change.

## Local evidence and remaining gates

Seven new synthetic tests passed, covering extra and symlink archive members,
unchanged complete extraction reuse, refusal to repair partial or changed
accepted extraction, an uninventoried source locator and row001-body exclusion.
A separate actual-data fixture extracted the canonical package into a temporary
directory and rechecked all 21 current paths against their original pins; its
two original input files were unchanged. That fixture did not rerun old chains.
Two additional focused control regressions check rejection of a new child
inside an old provider before any directory write, and rejection of changed
adapter bytes against an existing preparation identity before extraction.
Three new synthetic RUN fixtures exercise the actual stage/objects prefix and
reject replacement by cache_root or an unrelated project root. These fixtures
test the original verifier/exporter source schema; they do not claim a live P3
runtime validation. Four additional synthetic checks exercise the actual
first-namespace behavior, read-only reuse of identical complete provider files,
preservation of partial state, and refusal to repopulate missing or changed
complete provider objects. These four new tests passed in 0.009 seconds; no
compiler or old test suite was invoked.

Both the P1 generic/C-prefix original-body transport and the separate ten-object
runtime transport have arrived on P3 and were verified without extraction.
The latter used exact Git commit
`cad254f8ddbe55b1c35a05a8b495d4ddb004dcea`; P3 task
`b7afc7fe3f8943f288eb297ddff485e8` succeeded with exit 0 and read back all eleven
regular archive members. The independent increment source review passed for
adapter `75b2a9a960a1e30367c34303c7579783afdebf922f59f7e226e741fc0f0df0f8`,
runtime helper `c7531f1287af677a7d5f6aafef08d93cf224969e0191a84119ea420f267f6640`
and fixed configuration `7c4e1ae7e6281ff832bd7c82dd8d691880366fa6f4ea1fa1e70209dafb17c6b0`.
That reviewed v2 increment preceded the actual null-locator failure. The v3
source differs only at the two optional source locator reads; both now treat
null as unavailable and reject malformed nonnull references. The new regression
uses all 602 present and 189 missing records: 166 nonnull source references,
12 explicit null references and 11 omitted references. All 1370 protected parent
entries are preserved, along with the original 166 existing and nine explicit
C-prefix source selections. Four focused tests changed from three failures
before the fix to four passes after it. Exact v3 package readback, independent
increment review and the actual P3 runtime/791-supplier preflight remain
required. No prior proof or old test suite has been rerun for this adapter.
