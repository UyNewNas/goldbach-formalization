# P2.5 original finite archive separation

## Goal and reason

The original saving16 archive currently imports the complete analytic
Jensen/atlas closure before its pure parser, rational operations and Q96
guards can be checked. The separate backup environment already has all
fourteen authenticated original files and the same pinned Lean/Mathlib,
but it does not have that complete project proof closure. Reusing a small
finite layer allows an independent arithmetic attempt while P2 continues
its analytic dependencies. No numerical feasibility or success is assumed.

## Exact mechanical change

Create `P2OriginalSaving16Q96FloorCore` with the existing single
`P2OriginalSaving16JensenFloor.q96Floor` definition, unchanged. Create
`P2OriginalSaving16FiniteArchive` by moving the existing original archive
reader, pure decoders, rational simplex operations and aggregate guards:
37 source commands, including 35 named declarations, one elaborator
registration and one anonymous Decidable instance. Preserve their original
namespace, statements, bodies, section context and fourteen file paths.

The original Jensen owner imports the floor core and removes only that
definition. The original archive imports the finite core and removes only
the 37 moved commands; all 15 remaining source/atlas/closure declarations
retain their original bytes. Keep `evalQ`, `interiorCandidate`, headers
and facet-index guards in their old owner because the finite layer does
not require them. No new mathematical theorem or premise is introduced.

## Verification and boundaries

Record exact preimages, postimages, command ranges and hashes, remaining
owner identity, actual imports and declaration ownership. Generated
elaborator/instance/private names must be tracked separately and later
covered by full owned-declaration audit. A second agent reviews this
mechanical scope before publication. Preserve the original pure parser,
all 39,741 simplex checks, determinant expression, factor four, ten means
and separate Q96 floors. Do not replace them with reported witness values,
native_decide, assumed guards, or the Winner9 numerical archive.

Publish the concrete sources before cloud work. Run the existing strict
compile, independent kernel replay and full owned-declaration checks for
the three-module finite project closure in an isolated P3 worktree,
using the original data and pinned Mathlib. Observe actual memory
and runtime before deciding whether further reuse of an existing proven
arithmetic evaluator is necessary. The original real-integral and source
ownership endpoint remains on the P2 analytic path.

Execution ruling: the backup service's next command was rejected by its
retained-job limit, and it exposes no job-archive tool. P3 has the matching
toolchain, standard Mathlib, an existing baseline Git object and enough
disk. Prepare only the fourteen original files there, using the already
published bounded installer. The Lean source and relative paths do not
change. Preserve a separate fresh-compile input binding: before/after
physical file identities and hashes, actual source/object/dependency
records, and all three owned audit receipts. The single-active-job service
lane and no input-writing subprocesses protect the actual read window;
kernel replay verifies the embedded literals and inherits that original
data-to-object provenance, rather than recreating it from later files.
