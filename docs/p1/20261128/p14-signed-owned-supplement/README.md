# SignedMidpoint: supplement the missing complete-owned audit

This directory prepares one narrow supplement for
`ImbalancedChen.P5OriginalSignedMidpoint`. It is **not an execution receipt** and
does not establish that P1.4 is complete.

The published legacy review at commit
`a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52` already binds successful batch3 normal
and kernel commands, their original logs, the source plus five output snapshots,
and seven public declarations. Its old audit excluded private declarations. The
two private source theorems `anchored_remainder` and `half_weight_integral` must be
covered, together with every declaration dynamically owned by the module,
including generated declarations. The total is deliberately not assumed.

## Reused methods and exact differences

`OwnedOnlyAudit.lean` is the accepted
`member-repair-batch84/seed42-owned-only/OwnedOnlyAudit.lean` with only two byte
substitutions: the imported module and selected owner change from SeedBlock42 to
SignedMidpoint. All environment enumeration, unsafe/axiom rejection, full type
printing, type ASTs, universe parameters and transitive-axiom collection remain
identical. The manifest pins both originals and the resulting audit file.

The Python caller follows that existing owned-only pattern, using the original
batch5 serializer/guard helpers and batch10 snapshot, command-recording,
runtime-binding and lane-verification methods from their pinned Git objects.
The original implementations are not edited. Lane 0 is used because the reused
SignedMidpoint normal/kernel commands used that lane. The frozen runtime review,
resource arguments and actual guard journal must agree.

The wrapper adds explicit published-source binding, exact receipt pins, a strict
read-only check, original public type/AST/universe/axiom comparison, and a single
exclusive execution reservation. It invokes only the audit harness through
`lake env lean`; it never calls a target build, `leanchecker`, source installer,
`normal_one`, or any normal-provenance synthesis. The old command/log bytes are
copied unchanged to the supplement inputs and remain the primary normal/kernel
evidence.

## Mandatory execution conditions

- The live source, `.olean`, `.ilean`, `.c`, `.setup.json`, and `.trace` must match
  the **original batch3** sizes and SHA-256 digests before and after the audit.
- The source in the claimed Git revision must be the same original source.
- The existing guard, serializer, both runtime states, historical audit template,
  runtime configuration and protected roots must match the original fixed pins.
- The original serializer must hold lane 0, verified against its receipt and
  `/proc/locks`; the captured guard-journal tail must contain exactly the one
  actual audit process, with the existing resource arguments.
- Every dynamically inventoried owned name must have exactly one full record.
  All seven old public names, type ASTs, universes and axiom sets must match.
  Both source private theorems must occur as private owned names. No fixed
  complete-owned declaration count is used.
- An existing execution directory causes a hold, including an incomplete
  execution. Its evidence must be inspected and reused where reliable; this
  caller does not retry or overwrite it.

Missing or changed objects, runtime bindings, or old evidence cause a hold. They
do not authorize rebuilding the module, fabricating `NORMAL_PASS.json`, changing
the old validators, or modifying source and build artifacts.

## Root-coordinated use after publication

Only the root coordinator schedules P1 jobs. With the files published in one
explicit commit, extract the caller from that exact commit to an execution path
outside the repository, then run the read-only check first:

```sh
python3 -B /absolute/path/run_signed_owned_supplement.py \
  --source-commit FULL_PUBLISHED_COMMIT --check
```

When that succeeds and no existing reliable supplement covers this owner, use
the same bytes and commit with `--run`. The caller obtains the original serializer
itself. Receipts are written only beneath
`/workspace/p1-complete-proof/20261128-p14-signed-owned-supplement/`.

The resulting `SIGNED_COMPLETE_OWNED_SUPPLEMENT_RESULT.json`, if all checks pass,
distinguishes the old successful normal/kernel records from the single new audit.
It records dynamic owned/public/private counts, actual runtime evidence and
unchanged live object identity. It always leaves `whole_P1_4_complete` false.

TaylorFiveDimensionalMidpoint and StoredParentArchive already have complete
historical owned evidence. This supplement does not compile or audit them.
