# P2.2 acceptance consolidation

> For agentic workers: use the executing-plans workflow. This is an acceptance
> consolidation of an existing proof, not a new mathematical implementation.

**Goal:** Close the P2.2 first-integral endpoint node using the already compiled
source and exact evidence in commit `99c1f8ba1dc453b21f47e30b667db0de93d73387`.

**Architecture:** Preserve the accepted Lean files byte for byte. Add a small
reproducible verifier and a node-specific evidence record, publish them on an
isolated branch, and reconcile only P2.2 in the existing progress board.

**Tech stack:** Lean 4.33.0-rc1, the pinned project dependencies, Python 3 standard
library for evidence validation, existing Sites application for the board.

**Spec:** User request of 2026-11-25: complete P2.2 from the 1106 manuscript;
reuse reliable local/remote work; no manuscript-external theorem formalization.

## Constraints and review focus

- The exact original integral, parameters, endpoint and budget slot must agree.
- Receipt hashes, compiler exits, full declaration audit and source bytes must
  agree with the same immutable published snapshot.
- Only standard Lean axioms are permitted; do not introduce an assumed endpoint.
- Historical `SOURCE ONLY` comments remain unchanged to preserve accepted hashes;
  their later validation state is recorded in the external receipts.
- P2.2 acceptance does not imply completion of P2, Winner9, P4 or the main theorem.

## Tasks

1. Reconcile the manuscript and existing proof. Locate the three accepted modules
   and the original normal/kernel/audit receipts; verify the remote snapshot.
2. Add `verification/part2/verify_p22_acceptance.py` and
   `docs/verification/20261125-p2.2-acceptance/acceptance.json`. Run the verifier,
   including a negative hash case; retain its result and this concise explanation.
3. Independently review the consolidated acceptance and publish its exact files
   to GitHub without changing or recompiling the already accepted Lean sources.
4. Update only P2.2, its evidence and the resulting counters in the existing
   board. Run its existing tests, build and publish the saved source version.

## Progress

- Tasks 1 and 2: the existing 54/65/86 batch evidence was found and checked.
- Remaining execution and final results are recorded in the acceptance report
  and the GitHub/Sites publication results, rather than in a new proof wrapper.
