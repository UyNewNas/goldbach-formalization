# P2 handoff: explicit cons-sum shape repair

State: WAITING_FOR_P0. Request: REQUESTED. Verification: SOURCE_ONLY.

- Request: automation/parts/p2/requests/20261015T024700Z-rows-cons-shape.json
- Immutable record: automation/parts/p2/runs/20261015T024700Z-rows-cons-shape.json
- Worktree: /workspace/shared/chen-coordination/p2-data-split
- Changed file: ImbalancedChen/Certificates/PairedV2NaturalSumRows.lean
- Old source SHA-256: c1b98d2c39506cc9af9d89631eccae38b6302cb68cfcc654b791ca514f76db72
- New source SHA-256: 56eebe1e99f8dd6d79da3c49d0bcfb39fcc28f4c2468fdff8446a5876314cfbf
- Patch: automation/parts/p2/runs/20261015T024700Z-rows-cons-shape.patch
- Patch SHA-256: 26a453bf28b54b510b66ec7af0706756cb5004c36e5f2118e643e7634adde01e
- Effective 35-file snapshot SHA-256: 3619507e12cd13650305bfd7df1d76c1f558e4ef41e6a55df13c0a93b9d429c1
- Effective dependency fingerprint: e203a81a6d80dda5acef75e83b3f1e0f300e602ea14e5febc2dc578b96df98df

Real run 38672198005, source 8079c9aeb1a3dec6741d80480d8fbb394909369f, reached the light Rows
module after nine prerequisite compilations. Its strict -t0/-j2/-M4096 compilation
failed in 2.12 seconds at rw [Fin.sum_univ_succ], exit 1. This is a tactic matching
diagnostic, not a repeated FullCertificateData memory failure. Block11 and Block10
were not run after fail-fast. Exact artifact, receipt and log hashes are in the request.

The repair adds only two lines: explicitly change the cons-case finite domain to
Fin (xs.length + 1) and expose the mapped-list sum as f x + (xs.map f).sum before
the original rewrite. The theorem type, List/getD objects, imports and all other
proof steps remain unchanged. The other 34 frozen files match their prior hashes.

Static diff and patch reverse-apply checks pass. No Lean, Lake, checker, audit,
CI or push was run by P2; the corrected proof remains uncompiled. P0 alone owns
the retry and every subsequent gate. The 12 data leaves and global sum assembly
still require actual acceptance. Do not treat successful prerequisites as a pilot
or global proof success.

The old generator and manifests intentionally remain frozen. Reproduction is the
previous split followed by this exact single-file patch. The new request explicitly
binds the effective source hashes and dependency fingerprint. No other source or
manifest is silently rewritten.

Next: P0 checks corrected Rows, then the existing longest-strip/largest-data pilots
and full gates if successful. All original numerical/coverage/integral limitations
remain. No new analytic layer is added.
