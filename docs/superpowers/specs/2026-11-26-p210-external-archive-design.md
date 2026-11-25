# P2.10 receiver with an external evidence archive

## Goal and scope

Complete the already authorized P2.10 integration while preserving every
successful proof. The accepted public cohort contains 598 modules, 562 pages,
and 8978 rows. Receiving its validated files and complete evidence archive on
one constrained volume can exceed the receiver's available space.

The new tool changes storage placement only. It does not change a Lean source,
run a new numerical compilation or stock replay, or relax C/A/E acceptance.
The successful public producer and earlier complete receiver acceptance remain
historical facts with their original provenance.

The clean proof worktree is fixed by `WORKTREE_COMMIT` at W1,
`7c6fe1e249ffdbdf9b76b166022fc2236b2c69fb`, which includes the separately
checked finite-sum/API repair in `P4AOriginalFull87CellIndexedArchiveWeight`.
The numerical cohort's `SOURCE_COMMIT` remains
`94c7c507ab747cf4e05a4f19d8d4507cedfede38`: all numerical provenance, the
original importer's `--commit` argument and the binding's `source.commit`
retain that original identity. Neither historical artifacts nor their records
are rewritten to adopt W1.
The original importer remains SHA256
`b90f11e049080eff0ccc2d09e63f2d78ce88825791b5c4efdf6a92dc78be188c`;
the resume plan remains SHA256
`46e739a5a5ddfa3ad6b0dd4697f1bf95bb9cbb21ef84ce1c7f32e2cb33162978`.
Neither file is edited to accommodate this tool. The new storage adapter has
its own published Git commit and SHA, checked independently of proof provenance.

## Entry point and validation

Add a separate adapter in `verification/part2`. Its external-archive mode is
explicit and required; normal installation continues to use the existing
importer directly. Require `--archive-parent` and retain the original trusted
collection, run, commit, index and staging arguments.

The adapter can be copied from its fixed published Git version to an ignored
tooling directory inside the fixed W1 proof worktree. It runs with that
worktree as cwd, explicitly imports the original `verification/part2` modules,
and checks their actual module locations and original SHA values. The adapter
commit and adapter SHA are separate trusted inputs, verified against the
published file before execution.

Call the original `I.validate()` exactly once. Do not call `--check-only` first,
change its result, or claim to have invoked the original `I.install()` when
the new storage transaction is used. Reuse the original path, hash, transfer,
input-stability and dependency-snapshot helpers wherever applicable.

## Layout and path conditions

All validated objects, facets, compile logs, audit files and the live registry
remain in their original proof-worktree locations. The complete original
archive goes to a fixed run/attempt/index child of the explicit external parent.

The original internal `ci-imports/<child>` location contains exactly a storage
binding plus unchanged copies of `import-receipt.json` and
`local-records-before.json`. The complete original private registry snapshot
must remain in the proof worktree. An exclusive same-volume hard link to the
old registry preserves those bytes when the live registry is later replaced.

Validate the external parent and its ancestors independently: they must be
canonical directories without symlinks. The new external child must be absent
and must not overlap the proof root, incoming inputs, staging, or any temporary
directory that will be cleaned automatically. Do not pass an absolute path as
an archive-relative name or use a symlink to evade the original path checks.
Apply equivalent parent checks to the internal binding destination.

The binding records the original source/run/index/plan/importer pins, the
independent adapter commit/SHA, the canonical external archive root, every
original archive file's hash and size, the two internal original-copy hashes,
and the original before/after registry hashes. It states that validation ran
once, the original installer was not invoked, and proof compilation and stock
replay counts are zero. It is storage evidence, not a replacement C/A/E receipt.

## Transaction and preservation

1. Install only the original validated new files, using exclusive destinations.
2. Materialize every original archive member at the external destination.
3. Create the internal binding and both required original-byte copies.
4. Recheck the original inputs, old dependency snapshot and old registry digest.
5. Write exactly `verified['merged_raw']` to a temporary file beside the live
   registry, flush and fsync it, then publish with `os.replace`.

The registry replacement is the only commit point. Set the committed state
immediately after it returns. Before commit, roll back only files and
directories created by this transaction. After commit, preserve all installed
data even if later receipt generation or output fails. A forced termination
can leave uncommitted residues; a later attempt must stop for inspection rather
than overwrite or count them as accepted work.

Preserve the receiver's full old registry and add only the original 598 new
modules. The result is `old_registry_count + 598`; the earlier receiver's count
of 691 is not a universal target. Use actual local registry bytes when computing
archive sizes or hashes.

## Final integration gate

Keep the existing root-only `bound_file` restriction. Add a separate archive
reader that accepts only the single external root named by the internally
pinned binding and an independently supplied expected path. Check safe relative
names, canonical containment, all parents, the exact file inventory, each
expected hash, and the binding's adapter/source identities.

Only original archive reads move to that function. Root objects, preparation
evidence and the historical prefix remain on their existing path checks. Keep
all original installed-file comparisons, reconstructed merged-registry checks,
original receipt checks, old-record protection and the final three C/A/E gates.
Freeze evidence in both roots for the existing final verification guard.

## Resources and durability

Check actual writable capacity on both volumes at execution. After validation,
derive the installation requirement from actual file sizes and reserve room for
the live registry, pending registry, internal binding and final integration.
Place incoming inputs, staging and the external archive on a sufficiently large
volume without putting retained evidence inside an automatically cleaned tree.

An external temporary volume is not promised to be permanent. Keep the original
private registry snapshot in the proof worktree. Preserve complete public
evidence in the already successful persistent receiver and in its original
public CI sources. Do not upload private registries or environment receipts.

## Verification

Use small storage fixtures for same-volume and cross-volume behavior,
no-overwrite and symlink rejection, tampering, precommit rollback, exact merged
registry bytes, and postcommit preservation. Validate the final archive reader
against a generated binding and reject altered files or metadata before any
final compiler invocation. These fixtures run no Lean compiler or stock replay.
Focused worktree-identity tests accept clean W1, reject the old 94 worktree and
dirty W1, and preserve the original 94 numerical source pin. This identity
change does not alter the existing storage transaction fixtures.

Full P2.10 acceptance still requires the six preparation modules and all three
final integration modules to pass their original gates. Storage tests and
numerical reception alone do not establish that result.
