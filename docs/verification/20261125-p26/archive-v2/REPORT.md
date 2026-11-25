# Saving19 Archive loader repair and v2 diagnostic candidate

## Observed failure and proposed repair

Parent-reported cloud job `job_55c8ed8cfb6c45f9bd2d7dd4080c9e82` failed after
13.465 seconds: production-prefix lines 28 and 37 referenced unknown identifier
`liftIO`, followed by the two term elaborators being unavailable. Parse00 was
not run. These candidates have not been compiled and claim no repair success.

Each of the two loader lines changes exactly as follows:

```lean
let s ← liftIO <| IO.FS.readFile p
```

to the direct IO bind already used by repository term elaborators:

```lean
let s ← IO.FS.readFile p
```

The inspected reference is `aa8e91cd99e6b3f6c61417271ab105d3077d010d:ImbalancedChen/P4AOriginalNewFifthArchiveReader.lean`, source SHA256
`59d3c878507d07dff88790ed2c9fc626768fd7155dc3250c01763273e2f0d5b6`. It directly binds `IO.FS.readBinFile` twice inside a term
elaborator. This supports the implicit MonadLift form; it is not a fresh
compilation of the text loader.

## Exact byte boundary

Deleting `liftIO <| ` removes **10 ASCII bytes per occurrence**, including the
trailing space. The production file is 10816 bytes, reduced from
10836. The original 8,171-byte prefix becomes **8,151 bytes**; its SHA256 is
`714943068685d3a2fb3bf59ed8c027b5165ab777517733934231d0451f6862d6`. Core copies that repaired prefix byte-for-byte.
The rest of production Archive and the entire Parse00 source are byte-identical
to their originals. No record, parser, path, default, guard, theorem statement,
proof body outside the two IO binds, recursion limit, or witness is changed.

## Candidate files and installation boundary

- `ImbalancedChen/P2OriginalSaving19Archive.lean`: exactly the two production loader call repairs.
- `ImbalancedChen/P2OriginalSaving19ArchiveCore.lean`: the same two-call repair to the previous diagnostic Core.
- `ImbalancedChen/P2OriginalSaving19ArchiveParse00.lean`: unchanged two cell-00 closed parse proofs.
- `SOURCE_MANIFEST.json`: old/new source pins, exact prefix and source origins.
- `STATIC_AUDIT.json`: only checks performed while producing these files.
- `known_preimage_repairs.patch`: review aid for the two known-preimage edits.
- `build_candidate.py`: reproducible generator; never invokes Lean or loads witnesses.

Only Root may install the two known-preimage replacements after checking and
backing up the original production and failed Core files. The v2 diagnostic
driver accepts only an absent target or the exact new bytes. It never performs
the replacements. Publish the new diagnostic files under `docs/verification/20261125-p26/archive-v2/` and the
production repair at its normal path in a descendant of `aa8e91cd99e6b3f6c61417271ab105d3077d010d`.

The v1 directory, v1 driver and its failed evidence are retained. The independent
v2 evidence root starts without reusing the failed Core's build provenance.

## Acceptance boundary

Both original loaders still read all 26 original files from the unchanged
`../goldbach-research/` paths, including all thirteen cells. The v2 driver keeps
normal compilation, leanchecker, complete owned types/axioms, runtime review,
and actual loader-input before/after binding. It does not change audit limits,
templates, truncation gates or fixture checks. No external mathematical audit
is substituted for a proof.

Core contains no original parse-success proof. Parse00 still attempts only
the two cell-00 parse checks. `archive_complete` remains false; no cell is
reported proved before complete acceptance.
