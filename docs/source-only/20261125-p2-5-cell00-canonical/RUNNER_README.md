# Two-stage canonical cell00 runner

**Current state: source-only preparation, NOT_READY, not executed.** The real
Input/Decoder normal, independent replay, complete owned and input-bound
receipts are pending. `RUNNER_MANIFEST.json` uses explicit `NOT_READY` values;
the runner refuses to advance the worktree or compile either candidate until
actual pins replace them and readiness is explicitly finalized.

## Reuse and exact boundary

`run_canonical_cell00.py` reuses the accepted raw003 runner's bounded subprocess,
file/object snapshot and original audit-parser loader, plus the unguarded
runner's fourteen-file physical/hash snapshot. Both helper sources are copied
exactly and hash-checked before import; neither old `main` is invoked.
The original audit template and its parser/helpers are unchanged. The raw
binding proof is imported from its existing accepted 1,902,224-byte object,
SHA `a16d72d38a3313c8654f48c1aae85755a8e810e4e53bcaa600ff78ccce07422a`.
The old raw proof is not compiled again and receives no invented cache record.

The fixed P3 worktree is `/workspace/p25-q96-20261125`. Its expected predecessor
is `448e03d6ce02fd7d3b8d008defcd5ffffc4fc426`, after the already queued unguarded
validation. The runner takes one already-fetched publication SHA. It checks
the exact runner, manifests, candidates, prerequisites and original gates in
that commit before a detached checkout of this one worktree. It performs no
fetch, clone, production installation, cache cleanup, dependency compilation,
or private-record write. Historical raw acceptance at `0669b915...` and reader
acceptance at `448e03d6...` remain historical provenance, not a requirement that
the new publication HEAD equal either old proof commit.

## Two independently recorded stages

1. **Canonical binding.** Import accepted OriginalInput and raw003 objects.
   Compile only `ImbalancedChen.P2Saving16CanonicalCell00Binding`, independently
   replay that new object, then run the complete original owned audit. Its
   serialized/environment inventory must match exactly, including every private
   or generated declaration. Both named binding goals must occur. The project
   import inventory must be the exact three-module closure.
2. **Full cell00 parse/decode diagnostic.** Start only after stage A has written
   its own accepted receipt. Copy A's original accepted object into a separate
   library with the other accepted prerequisites. Compile only
   `ImbalancedChen.P2Saving16CanonicalCell00ParseDiagnostic`, then independently
   replay and fully audit that object. The project import inventory must be the
   exact nine-module closure. A's source, object, logs and receipt are frozen
   throughout B. Timeout or failure of B leaves A's accepted evidence intact.

Each stage has a separate `src`, `lib`, `audit` and `RESULT.json` below
`.lake/diagnostic/p25-cell00-canonical-attempt001/`. There is one combined
`ImbalancedChen` object directory per stage: Lean's package-root lookup does
not make several same-package library paths into a per-file fallback. Only
exact regular-file copies of required accepted objects enter the library. The
new target must be absent beforehand, and successful normal compilation may
add only its one new object. Replay and audit may change no object.

All six private prerequisite records are read and frozen, not modified.
Their actual original closure-signature calculation and source/object/dependency
bindings are checked. Accepted receipts and every referenced artifact are
hash-checked. The raw003 diagnostic receipt and its existing complete audit log
are checked separately, without manufacturing a private compile record.

## Inputs, options and evidence

All fourteen original inputs (93,508,187 bytes) remain bound to the fixed
manifest. The raw object's historical cell00 physical/hash identity must still
match. OriginalInput must have an actual fresh `START`, successful strict record
and unchanged before/after/final fourteen-input snapshots in its accepted
outer receipt. New candidates do not read those files; their proof context is
explicitly a transitive reuse of these input-bound accepted objects. The runner
does not call that reuse a new `readFile` event.

The original normal/audit options remain `-t0 -j1 -M11264`, warnings as errors,
maximum recursion depth 50000 and 40,000,000 heartbeats. Neither candidate adds
a source option; raw003's local depth option is not inherited. Each of normal,
independent replay and full-owned audit receives the same 180-second wall bound
already used for raw003. The original `leanchecker --verbose` command is retained.
There is no `native_decide`, `skipKernelTC`, reduced decoder, alternate data,
success premise, or filtered owned audit.

Object-copy space is calculated from the observed prerequisite file sizes at
runtime. No size is guessed for the pending OriginalInput object. Current free
space and the exact known copy total are recorded before copies; this does not
predict the size or resource outcome of either new target.

The runner protects but never imports `FiniteArchive`; none of its four guards
runs. Even complete success earns only canonical cell00 binding and the exact
single-cell full parse/decode Boolean statement. It does not certify the other
thirteen cells, any Q96 arithmetic, geometry, integral, or final P2.5 endpoint.

## Remaining preparation

Fill only actual accepted b80 evidence into `RUNNER_MANIFEST.json`: Input and
Decoder object hashes, receipt hashes, closure signatures, owned counts, sizes,
and the accepted fresh-input outer receipt hash. Preserve the old evidence and
the current NOT_READY preparation history. Recheck the runner manifest's code
hash after any edit, obtain the independent runner review, and let the parent
agent publish and schedule the bounded execution. This preparation runs no
Lean process or remote operation.
