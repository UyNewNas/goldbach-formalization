# Cell01 remaining rows: Python boundary repair v2

## Current status

The 142 candidate owners for original ordinals 2 through 143 remain source-only.
Their Lean bytes and all frozen owned-audit Lean bytes are unchanged. Row001's
accepted source remains SHA256
c15da8c66ab55245dfab3ea2bbcdbc7c070dbe71bff6e7da38b476ce44808876.

Row001 passed normal, independent kernel, and complete owned audit in P3 job
ae159e9bafeb4b6baee1d6d5109a18fa. Its separate in-place evidence review has
completed, as reported by the coordinating agent. The complete row001 evidence
tar has not been retrieved. This repair neither reads nor transfers that tar.

No Lean command or new proof job ran during this repair. Two focused Python
regression tests passed in P3 job 19305c1577c846fb89632d905e452ed4.

## Exact changes

I1: the stager rejects either direction of overlap between the stage and each
input root. Every destination is checked for a canonical path within the stage,
including missing files, symlinked parents, and dangling final symlinks, before
writes. The batch driver applies the same checks to supplier installation,
objects and verification roots, JSON/log outputs, and target olean paths.

I2: an existing successful normal receipt for the same module and source creates
an obligation to preserve its exact object. If that object is missing or differs,
the validator stops with RESTORE_EXACT_ACCEPTED_OBJECT before context filtering
could treat the normal step as runnable. Restore the object fixed by the receipt;
do not rebuild it. Successful receipts with matching objects still undergo the
existing complete evidence checks. Failed or unexecuted normal/kernel/owned
steps remain eligible to resume. receipt_reuse.py has the exact same validator
AST as the batch driver.

The accepted row001 driver and all Lean source and audit files are unchanged.
The fixed 399-supplier manifest is unchanged. No supplier is recompiled.

## Preserved v1 history

The old checkout and old stage remain in place:

- /workspace/p26-continuation-59264dd64286/cell01-rest-source-checkout-v1
- /workspace/p26-continuation-59264dd64286/cell01-rest-finite

The original 293-member source-only package is 626564 bytes, SHA256
32cec51b78d94c71e4783e214715a7d356ed363ecac579b7481c00f85156ff20.
Its upload parts and original file fingerprints are retained. It is distinct
from the blocked row001 completed-evidence archive.

The available 293-file checkout did not contain prepare_batch_driver.py,
freeze_batches.py, the old BATCHES.md, or the old separate receipt_reuse.py.
The earlier local unpublished copies were lost with the execution environment.
Those two old builder scripts have not been recovered. The new receipt fragment
was extracted exactly from the corrected frozen driver; this document is the v2
handoff. Frozen candidate sources remain usable independently of those builders.

## Re-stage without touching v1

Use the corrected checkout:

    /workspace/p26-continuation-59264dd64286/cell01-rest-python-v2-repair/source-checkout

Use a fresh stage and the original candidate metadata supplier:

    python -B /workspace/p26-continuation-59264dd64286/cell01-rest-python-v2-repair/source-checkout/tools/p26/cell01-rest/stage_batch.py \
      --repo /workspace/p26-continuation-59264dd64286/cell01-rest-python-v2-repair/source-checkout \
      --stage /workspace/p26-continuation-59264dd64286/cell01-rest-finite-v2 \
      --base-stage /workspace/p26-continuation-59264dd64286/cell01-row001-finite \
      --check-only

Remove only --check-only to copy the exact 343 frozen files. The stager refuses
different existing destination bytes and creates no Lean source from formulas.
The --stage argument is explicit because historical defaults name the old stage.

After the coordinating agent allocates proof work and the independent patch
review passes, the corrected driver can be invoked with explicit --stage and
--cache-root. No such invocation is part of this repair. The available P3 cache
root is /workspace/p26-continuation-59264dd64286/cell01-row000.

Batch allocation remains A = 2..49 (48 rows), B = 50..97 (48), C = 98..143 (46).
An optional first measurement is --rows 2 3 4; its successful receipts can be
reused within the same stage and runtime context during batch A. Each row still
requires normal, independent kernel, and complete owned audit. Defaults remain
6 GiB RSS, 900 seconds per command, 3300 seconds task budget, and a row-start
reserve of at least 180 seconds. A budget pause is not batch completion.

## Recovery and publication

Restore the original source-only v1 package into a new destination, verify its
293 file pins, then overlay only the v2 Python/JSON/docs package. Its per-file
manifest distinguishes the four changed runtime/staging files from new support
files and evidence metadata. Keep the original package and v1 checkout.
The coordinating agent will restore and publish a source checkpoint.

The v2 patch does not claim any new row has compiled, any integral certificate
has been proved, or P2.6 has closed.
