# PerGroup first compile repair candidate

The M run `54c6e72732ce3a6d209960c396956f9cb2fe3f59` accepted
`P5LicensedOriginalIntegerProfile`, then failed in
`P5PerGroupIntegerHBAtlasPushforward.atlasEval_add` at `159:16`.
The complete bounded public diagnostic is retained in
`ACTUAL_M_METADATA.json`; it contains one residual finite-sum goal.

## Exact change

The candidate changes only line 161:

```diff
-      simp_rw [ih,mul_add,Finset.sum_add_distrib]
+      simp only [ih,mul_add,Finset.sum_add_distrib]
```

The fixed Mathlib implementation executes `simp_rw` rules in separate
`simp only` passes. The final finite-sum distribution exposes an outer
`scalar j * (sumF + sumG)` after the multiplication pass has finished.
Using the same three rules in one simplifier call continues distribution
through both the scalar and `psi/log` factors. The actual error goal
confirms this exact remaining expression. No Heath-Brown, support,
normalization, coefficient, carrier or list-test assumption is added.

The original archived 20261110 provider contains the identical
`atlasEval_add` proof, so it does not supply an already repaired version.
The manuscript's finite Heath-Brown expansion and original roughness
projector at lines 526–537 remain unchanged. `REPAIR_CANDIDATE.json`
binds the precise failed source, actual diagnostic, fixed API sources,
original provider and byte splice.

## Frozen source and verification boundary

| File identity | Bytes | SHA256 |
| --- | ---: | --- |
| Failed M source | 9091 | `090fc6f2140dcb74a01865d25f7c8158364cf31d2b6300884cd6d35f870730d9` |
| Scratch candidate | 9093 | `83ac50b41f5927c3e408611cb01cdc5d3712d730b49a507923179eba951606d6` |

The candidate is exactly reconstructed by one byte splice and reverses
to the failed source. All other bytes, imports and declaration statements
are unchanged. The independent one-line static review found no concrete
blocker. No Lean process, cloud task or acceptance gate was run for this
candidate here; root will perform the guarded whole-module no-output
probe. This candidate adds no acceptance credit. The accepted Licensed
module, project sources, objects, traces, guards and receipts were not
modified.

## Actual whole-module probe

After that frozen review, root executed the independently reviewed
`probe_pergroup_additivity.py` once through the original serializer and
guard. Task `job_61b286303db242948dfe69652fe8aba3` finished with exit 0 in
35.474 seconds. The full 9093-byte candidate passed
`lake --no-build env lean` without requesting an output object. The only
source message was the pre-existing unused-variable warning for `hone`.
The actual bounded stdout is preserved byte-for-byte in
`ACTUAL_PROBE_RESULT.json` (2130 bytes, SHA256
`5085f0795e082a5b8118d7fa0bd0f6d60916f5859aa2ca43821ef8dca0fe9809`);
the task and complete-read observation are in
`PROBE_EXECUTION_OBSERVATION.json`.

Five watched sources and all 105 watched artifacts, the 18 original M
failure records, six original Licensed receipts, accepted source-plus-five
bindings, runtime/configuration and Git state were unchanged. This is a
no-output typecheck, not a normal/kernel owner acceptance. Root then
adopted only the exact one-line splice into the canonical
`ImbalancedChen/P5PerGroupIntegerHBAtlasPushforward.lean`. The subsequent
formal run must reuse Licensed@M and continue fourteen fresh targets.
