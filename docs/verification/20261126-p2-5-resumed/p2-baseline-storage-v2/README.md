# P2 baseline document recovery, bounded second scope

The first baseline-only plan stopped without mutation: task `2378ebc9004240b59747554ece8f16a1` found 192,819,200 reclaimable bytes but only 613,273,600 free bytes. Their sum was insufficient for the unchanged 1 GiB proof gate plus evidence/preparation reserves. Its failure and original runner remain unchanged.

This separately reviewed scope uses the same five document roots already enumerated by the pinned round4-v3 workflow, now only within this task's isolated baseline `8657cfff...`. The executable change is limited to an explicit five-prefix tuple, a 512 MiB storage target, and distinct v2 schema/output names. The complete proof context, references, all registered-worktree symlinks, real Git blob qualification, exact sparse rules, successful prior-plan binding and postflight checks are unchanged.

Only `.raw`, `.gz`, `.json`, `.txt`, and `.nul` ordinary, single-link files can qualify. All Lean sources, Python/script files, `.lake`, compiled objects, untracked/ignored inputs, symlinks/targets and protected references remain. Neither this task's proof root nor any other worktree is a deletion candidate. Git objects remain locally available and every omitted file is recoverable exactly.

The selected roots are `docs/source-only/`, `proof-continuation-data/`, `verification/proof-continuation/`, `verification/parts/`, and `docs/evidence/owned-frontiers/`. The additional read-only capacity task `372b9207500e47d8af5b1cdb5112db91` measured document allocation only; it did not qualify Git blobs or protected references, and its numbers are not a recovery claim. The full new plan must recompute these conditions before any change.

Plan and apply run sequentially with fresh v2 output directories. Apply requires the actual successful read-only result and exact plan SHA, then reruns every frozen check. The proof gate remains 1,073,741,824 bytes, with the same evidence/preparation reserves. A capacity failure stops before mutation. No compile, recovered-space or P2.5 acceptance is claimed by this package.
