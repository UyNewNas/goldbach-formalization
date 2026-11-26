# Round5 resume boundary

The runner is `docs/verification/20261126-p2-5-resumed/run_p2_round5.py`.
It is a 316-line adaptation of the approved round4 wrapper. The original
compile driver, owned-audit driver, baseline checks, external-environment
snapshot helper, and round2 helper remain unchanged.

## Exact prior evidence

The prior source commit is `168973571f795dbe8fb1c1bccfd7f7c54899b36a`.
The complete original round4 result SHA256 is
`bf84d4551c73db7ff634c95f797df967815d2e8c5ded65bd5f0b04a756b0c17e`.
It records 330 normal successes, including 325 reused and five new successes;
41 owned acceptances, including 38 reused and three new acceptances; and all
seven source/gate/runner/external/head/history/baseline postflight flags true.
The aggregate result is still failed, with no P2.5 completion credit.

The six original failure logs are byte/hash/source-bound to the saved collector
records and agree with the normal stream. The actual normal stream reports
`FAIL 1`; each later collector record contains code `125`. Those values are
preserved separately, and `125` is not described as the Lean process exit.

## Graph and cache handling

The runner loads the exact approved round4 wrapper and source-selection bytes.
It calls that existing graph validator to apply the eight round4 postimages
to the original pinned 377-module graph, then requires equality with the live
saved attempt004 graph. It verifies that saved attempt004 targets, selection,
runner, logs, result, and audit summary have the expected identities.

Only after constructing this exact prior graph does it apply the six new
postimages. It keeps the same five roots and all 69 audit targets. The two
changed audit owners, Full87SourceDictionary and H5H7SourceDispatch, are placed
first; the other four repairs are dependency-only modules. No audit target is
added or omitted.

The new attempt005 archives the current records, all 69 prior latest receipts,
and the prior result/summary, and checks that attempts001 through004 remain
unchanged. Cache reuse is decided by the existing drivers' source, dependency,
toolchain, and external-environment checks. The historical batch41/batch57
objects are not imported or relabeled.

## Resource and execution limits

Resources remain one worker, one Lean thread, 11264 MiB, the original
1400-second normal-stage budget, and the unchanged 1 GiB minimum free disk.
At preparation, the coordinator reported only 269,037,568 bytes free on P2.
Execution therefore waits for the separately reviewed storage recovery; the
runner does not relax the disk gate or delete anything.

After source installation and publication by the coordinator, the invocation
requires a full publication commit and the reviewed runner SHA256. The runner
checks its executed bytes against the published file before proceeding. This
package prepares that invocation but does not execute or publish it.
