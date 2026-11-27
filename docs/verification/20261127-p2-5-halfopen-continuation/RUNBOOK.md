# HalfOpen continuation: exact inputs and separate fresh evidence

This directory continues the existing P2.5 proof-body repair. It changes no Lean
source, original verifier, historical receipt, or historical counter. The
362/377 normal and 54/69 owned counts are historical references, not a statement
that the lost environment has now been revalidated.

## Minimum inputs

| Parent byte source | Objects | Action |
|---|---:|---|
| Existing R14 project LTAR | 214 | Restore exact old bytes |
| Five accepted standalone xz files from rounds 12/14/16/17 | 5 | Restore exact old bytes |
| Original CI packet payloads also named in the exact54 request | 54 | Restore exact old bytes |
| P4AOriginalCell0AffineChronology | 1 | Compile the unchanged f7a source; its original R18 object was lost |
| **Strict parents** | **274** | **273 byte restorations and 1 new compilation** |

Including HalfOpen, the source closure contains 275 modules. The candidate is
the already reviewed source with SHA256
c629a82f73a6ccd83286745cbbe235def6ed00d752e83e11f5854e1033bab9b0.
The prior source SHA is
f06ea67a68c218279ed051108ca17b1f77271e5bc680c207cf085188d9c89a9d.
The prior review established that seven proof bodies changed while all 31
declaration headers, including all 18 theorem statements, stayed unchanged.
The preflight pins this exact candidate; static review is not compilation.

MINIMAL_INPUT_MANIFEST.json is an input plan, never replacement records.json.
It joins the byte-identical R18 source closure and object index, R14 294-module
inventory, local exact-parent inventory, exact54 request, and original R16/R17
indexes. The R14 failed/blocked rows for AfterSeed7, Literal96, and Chronology
are replaced only by those specific later historical indexes. All 274 source,
object, direct-dependency, and closure-signature bindings recompute exactly:
92 schema-2 and 182 schema-3.

The five files in inputs/ preserve original bytes. Existing repository
R14/R16/R17 inputs and five xz payloads are referenced in place. The manifest SHA
is 9ed2e104e8578c08f359143f71c0bb6c5313fada79e3bb677d9a3c5059a65585.

## Why these are separate fresh checks

The original programs and original complete-owned template remain unchanged.
Full original ExternalSnapshot verification remains unavailable while 515
provider receipt bodies, STAGED.json, and one historical Architect.Command
actual.setup.json are missing. Nothing here synthesizes those bodies.

Prefer the original route when all original metadata is available: run the
unmodified ExternalSnapshot verifier and original normal/audit programs with
their actual historical records and baseline requirements. Original R19 also
requires a separate complete R18 capsule: 2,911,408 bytes, SHA256
337280f84e11796c9999764a8c902777b57f37fa165d67efe7bf7baaa9970524.
Physical runtime restoration alone does not satisfy that gate.

The scoped runner checks 69,342 physical execution inputs and all 11,516
recorded module resolutions before and after each process. It also keeps the
original Mathlib and native package Git pins. Historical producer metadata is
listed as omitted, never represented as restored. The sole excluded setup file
is fixed to its precise old path, 155-byte size, and SHA256
90681b8d0156649c34988c20e54489650dc9b510f39d44459c506b6f274a6af4.
That file belonged to the old Architect.Command invocation; none of the new
commands passes --setup or references that historical invocation.

The physical boundary rejects changed bytes, earlier package roots shadowing
original resolutions, and unbound executable companions. It records a fresh
observation of execution inputs, not original native qualification.

New receipts keep R19_accepted, P2_5_proved, old_records_reconstructed, and
original_external_snapshot_verified false. Their fresh_*_passed fields report
only actual new operations. Historical credit fields remain false. No old
counter is incremented.

## Reused original verification tools

- Project imports, historical closure signatures, and process logging use the
  original hash-pinned helpers.
- Normal and owned stages retain exactly the original flags:
  -t0 -j1 -M11264 -DwarningAsError=true -DmaxRecDepth=50000 -DmaxHeartbeats=40000000.
- Replay is stock leanchecker --verbose TARGET.
- The complete-owned template changes only its two target occurrences.
  The original parse_audit checks serialized/environment inventory equality,
  exact project closure, all declaration types, unsafe/partial/axiom flags, and
  the complete transitive axiom allowlist.

## Sequential P2 commands

Run from /workspace/p25-halfopen-validation-20261127. Use fresh output directories
on every attempt. Root manages the P2 job queue; these scripts submit no jobs.

### Read-only preflight and exact-byte staging

~~~bash
python docs/verification/20261127-p2-5-halfopen-continuation/prepare_halfopen.py

python docs/verification/20261127-p2-5-halfopen-continuation/prepare_halfopen.py \
  --stage-project-objects \
  --out-dir /workspace/p25-halfopen-stage-001 \
  --r14-archive /workspace/p25-r14-geometry-231-export-20261127/r14-project-231.ltar \
  --leantar /workspace/toolchains/lean-4.33.0-rc1-linux/bin/leantar \
  --ci-packets-dir /workspace/p25-runtime-recovery-current-20261127
~~~

The LTAR and leantar binary are SHA-pinned. The CI inner packets supply only
the requested 54 content-addressed payloads, each checked by complete size/SHA.
The stager does not repeat or claim whole-CI-archive authentication. Every missing
donor is checked before the first project write. Atomic no-overwrite links put
273 objects into .lake/p2-private/lib. Existing different bytes or destination
symlinks stop the operation. PROJECT_STAGE_RESULT.json is byte-restoration
evidence; no compilation records are written.

### Chronology normal, stock replay, and owned

~~~bash
python docs/verification/20261127-p2-5-halfopen-continuation/run_scoped_normal.py \
  --target ImbalancedChen.P4AOriginalCell0AffineChronology \
  --out-dir /workspace/p25-halfopen-validation-20261127/.lake/p2-private/scoped-halfopen/chronology-normal-001

python docs/verification/20261127-p2-5-halfopen-continuation/audit_scoped_halfopen.py \
  --normal-receipt /workspace/p25-halfopen-validation-20261127/.lake/p2-private/scoped-halfopen/chronology-normal-001/NORMAL_RESULT.json \
  --normal-sha256 ACTUAL_CHRONOLOGY_NORMAL_RECEIPT_SHA \
  --out-dir /workspace/p25-halfopen-validation-20261127/.lake/p2-private/scoped-halfopen/chronology-audit-001
~~~

Replace ACTUAL_CHRONOLOGY_NORMAL_RECEIPT_SHA with the actual digest printed by the
successful normal stage. Compilation writes into its new output directory.
Only a successful strict process with unchanged inputs publishes the new object.
Its receipt binds actual output bytes and actual direct-dependency signatures;
same-source recompilation is not described as recovering the lost old binary.

### HalfOpen normal, stock replay, and owned

~~~bash
python docs/verification/20261127-p2-5-halfopen-continuation/run_scoped_normal.py \
  --target ImbalancedChen.P4AOriginalCell0HalfOpenPrimeCarrier \
  --chronology-normal /workspace/p25-halfopen-validation-20261127/.lake/p2-private/scoped-halfopen/chronology-normal-001/NORMAL_RESULT.json \
  --chronology-normal-sha256 ACTUAL_CHRONOLOGY_NORMAL_RECEIPT_SHA \
  --out-dir /workspace/p25-halfopen-validation-20261127/.lake/p2-private/scoped-halfopen/halfopen-normal-001

python docs/verification/20261127-p2-5-halfopen-continuation/audit_scoped_halfopen.py \
  --normal-receipt /workspace/p25-halfopen-validation-20261127/.lake/p2-private/scoped-halfopen/halfopen-normal-001/NORMAL_RESULT.json \
  --normal-sha256 ACTUAL_HALFOPEN_NORMAL_RECEIPT_SHA \
  --chronology-normal /workspace/p25-halfopen-validation-20261127/.lake/p2-private/scoped-halfopen/chronology-normal-001/NORMAL_RESULT.json \
  --chronology-normal-sha256 ACTUAL_CHRONOLOGY_NORMAL_RECEIPT_SHA \
  --out-dir /workspace/p25-halfopen-validation-20261127/.lake/p2-private/scoped-halfopen/halfopen-audit-001
~~~

The audit saves separate replay and owned receipts, a combined result, complete
declaration JSON, full types, and untruncated logs. --through replay stops after
replay. A later invocation can pass --replay-receipt and --replay-sha256 to reuse
that exact fresh replay, after rechecking its inputs and log.

## Further continuation

These entry points deliberately pin this 275-module manifest and candidate.
A later HalfOpen repair or expanded downstream closure must preserve successful
new receipts. Do not recompile unchanged ancestors merely because a global
manifest changes. A later adapter can compare the actual ancestor closure,
source/object bytes, runtime, and direct-dependency signatures against the
original fresh receipt. Keep these original scripts and receipts unchanged.

The normal runner refuses to overwrite a fresh object. After an incomplete
stage, retain all completed normal/replay evidence and inspect the actual log.
An execution-preflight failure before Lean starts is not a Lean compilation
failure and grants no compilation credit.

## Local preparation checks

~~~bash
python -m unittest discover \
  -s docs/verification/20261127-p2-5-halfopen-continuation \
  -p 'test_*.py' -v
~~~

Thirteen local Python tests passed at preparation. They cover the real 275-module
join and all signatures, content/size rejection, no-overwrite and symlink
behavior, file mutation despite cached hashes, package-root shadowing, unknown
companions, and the narrow setup exception. They grant no Lean, kernel, or owned
credit. This directory's scripts have not themselves been executed on a cloud
compiler by the preparation agent.
