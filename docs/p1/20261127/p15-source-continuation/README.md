# P1.5: source continuation after the Dictionary and Variation acceptance

This is a source checkpoint. It adds no formal acceptance and does not close P1.5.
The original 21-target register remains 18/21. The original accepted Dictionary
(040d4605) and Variation (f7e9219f) sources and receipt identities are retained.

## Restored original ShiftedTau repair

The canonical `ImbalancedChen/Part3ShiftedTauFiniteInterval.lean` now contains
the exact previously reviewed 10628-byte d006abee2c8dd632d9fd9712b29030dbff0a70f6c95ade6ffec92955a37444c2
repair. It was recovered by applying the recorded single explicit `Finset.sum_image`
summand to the original failed 5be137ee source, with exact full-file and inverse checks.
All eleven source declarations have the same interfaces. This is not a newly invented
proof and is not compiled acceptance. The five already accepted Tau predecessors
retain their original acceptance; their objects are absent in the current P1 receiver.
They have not been rebuilt to refill it. See `tau/RECOVERY.json` and `tau/DEPENDENCY_REUSE.json`.

## Pending GroupLog candidate

`group-log/P5OriginalGroupLogAbelVariation.lean` is the 9964-byte af213638 candidate.
It reuses the original group denominator log(A*y), with A from other occurrences
in the same HB group and H the logarithm product of other original groups. Its
original final bound is unchanged:

```text
G(y) = Phi(y/U) * exp(i*t*log(y/U)) / (H*log(A*y))
norm(G(v)) + integral_(u,v] norm(deriv G(y))
  <= abs(H)^(-1) * ((M+D)/ell + M/ell^2) * (1+abs(t)).
```

The original C1, size, derivative, interval, positivity and log-floor conditions
are retained. H=0 uses the existing totalized zero coefficient. Repairs address
actual parser/tactic/instance and algebra-normalization failures; the only
statement annotation change explicitly takes the real reciprocal-log derivative
before casting to Complex. The final theorem statement remains byte-identical.
The sole project import is the already accepted Variation. No SW theorem, full
signed PP result or downstream consumer is accepted by this source checkpoint.
Its v4 no-output probe is submitted as job_dbb5fffce613429ab41a8288ff6028ef;
this checkpoint does not infer success from submission.

## Original signed-exit chain and a new provenance bridge

The original Partition -> PolicyComparison -> CoefficientDifference -> Boundary
chain has been located with its source-only history. All other direct project
inputs belong to the existing Dictionary context. The original Partition probe
confirmed its forty project dependencies ready without builds and preserved
the old inputs, but exposed a record-literal layout error.

`partition/P1SignedExitPartition.lean` is the exact original source with that
one literal joined to one line: 15972 bytes, 19f59a09107d934a8230d58a11afd256dd6134d7e2bba958a4144331f191249c.
Removing whitespace gives exactly the original bytes. Its v2 no-output probe is
submitted as job_ffea0245489740cc997473431e9840f8, without claimed acceptance.
The canonical Partition file is not changed by this checkpoint.

`medium/P1OriginalHistoricalFirstDisagreement.lean` is a new unelaborated bridge.
It applies the accepted actual small/rough coefficient dictionary to derive
a changed rough mask from an actual nonzero complete-modulus coefficient.
It then uses the original Boundary first-disagreement API, keeping the same
target-deleted universe and proving that the witness primes divide the full
original modulus d. It does not supply a whole-atom family, the physical/free
collision correction, or the uniform signed medium estimate. See `medium/REVIEW.md`.

## Continuation boundaries

The proper-power receiver still has its recorded receiver/native-parent blocker.
The exact original FixedM source bytes remain unrecovered. Actual historical
medium and the full original hSmoothSignedPP remain unfinished. The existing
accepted owners are reused under their own original source commits. Raw failed
attempts and pending task identities remain separate from any later source
publication and formal acceptance. No extra assumption is used to claim closure.

`SOURCE_MANIFEST.json` binds every source and review file in this checkpoint.
The readiness files are bounded observations, not acceptance records; extra
queried names are not asserted to be prerequisites.
