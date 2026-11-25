# Batch16 Adaptive rootCell expansion

Status: source candidate; actual normal, kernel and full-owned verification is pending.

The ordinary retry `job_9c5d7cff27334c05a97b574a34e5a502` built source `95b96cb5fe1a26322b7ecbdc66f15c2775035138`. Adaptive alone retained one error at line 131:2. Its normal stage exited 1 after the reported 6.874 seconds; log SHA256 is `1a8e3567866d21cba47d5ee507fa2c09e99ddb5bba9c68863cfb7da74bb727d8`.

The actual stream event displays both equality types. The dictionary produces the explicit `compactRegion ∩ Icc ...` set and its explicit map function, while the expected type still contains `rootCell` in both positions. The previous `simpa only` did not perform that definitional conversion.

Only the proof body of `closedLeaves_sourceSplitTree` changes:

```lean
  unfold rootCell
  rw [compact_closedLeaves_eq_integer_boxes,
    integerLeafBoxes_sourceSplitTree c hwidth]
```

The explicit unfolding exposes the exact dictionary pattern on both sides. The source-child equality, integer midpoint, strict interior hypothesis, side order and all closed-domain portions are unchanged. No new mathematical input or hypothesis is introduced.

The before SHA256 is `adbcc11b297d4794b8174f82624e283ec708f49e32230c01d308e7e5f5d98df1`; the candidate SHA256 is `20b6c83c8dd52b05557fbcee9610536cb8c301fece24fc57ff462c72b468ead2`.

Static checks confirm that the candidate equals the published preimage plus exactly this one proof-body replacement. All ten theorem declarations, eight definitions, imports and options remain byte-identical; `git diff --check` passed. The four other ordinary owners still exactly match the task's published source commit and were not changed. `REPAIR.json` preserves the actual error event, normal-stage metadata, dictionary source hashes and the prior manuscript/parent-receipt reference.

No compiler call, Lean/Lake invocation, audit, source installation, staging or commit was performed for this repair. Root owns actual verification of this exact candidate.
