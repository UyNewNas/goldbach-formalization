# P2.4 kernel memory diagnosis and early symbolic audit

Updated 2026-11-26 09:37 UTC. Production P2 remains pinned at
`909214bbfb5ca9caa74fcc1b6f95b469bf43e125`; the later publication commits contain
documentation and diagnostic sources only. No finite acceptance is granted here.

## Accepted boundary

The original compiler gate has accepted the same 321 symbolic modules. The complete
scope remains 324 modules with ordered fingerprint
`c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f`.
A remains unaccepted; B and W have not run. The full 324 owned audit is incomplete.
The numerical target, original source computation, two-million-split schedule,
all-leaf accounting and strict cutoff have not changed.

## Directly observed kernel failure

| Diagnostic | Task | Lean child result | Child seconds |
|---|---|---|---:|
| Original full map, raw exception | `548f0b1357034b6e8c16afe4aef9d1a5` | exit 1, kernel excessive memory consumption | 80.958 |
| Prefix map, raw exception | `423c0bbff0a54baea7e078a19d3f0c23` | exit 1, kernel excessive memory consumption | 169.200 |

Both outer wrappers exited 0 only because they successfully preserved diagnostic
results. Both proof children failed. The raw tactic retains the official
`mkDecideProof → mkAuxLemma` kernel path and propagates the original exception
instead of replacing it with the ordinary decide fallback message.

Each run used the original `-M11264` Lean budget. The production A source remained
`f3b608cd96e21bd7bc425526d3731f86ed2440874a00ff61f14f3cfeb77e0e54`; the registry
remained `0858a9bea92e7c436382ae96fcd63dc709b73f5b346d93e6980c0389d7718e5a`.
The canonical A object remained absent and the qualified native binding compared
equal before and after. These observations identify a Lean kernel memory-limit
exception in these diagnostics, not an operating-system OOM and not the unknown
masked exception from original A02.

The prefix candidate SHA256 was
`1b284797644b124a7864a6fa952ce1d10ce0686aad82d955e5296f5bdddd6800`.
Its generic and exact-source Q80 adapters had passed isolated checks, but the
complete closed proof failed. It is retained as evidence and has not replaced
the production source.

- [Raw full-map result](p2-finite-a-kernel-raw-05-summary.json)
- [Raw full-map exact log](p2-finite-a-kernel-raw-05.log)
- [Prefix full-proof result](p2-finite-a-map-prefix-06-summary.json)
- [Prefix full-proof exact log](p2-finite-a-map-prefix-06.log)

## Original exporter preflight

Task `31d2dbedc14d4731a3213ed93041ad09` ran the unchanged exporter on the complete
ordered 324-module list under the original project lock and source pin. It
completed in 5.924 seconds, with no compile-registry change.

The actual selection was:

- Selected valid owned audit receipts: **0**.
- Unselected modules: **324**.
- Eligible independently compiled symbolic modules needing audit: **321**.
- Duplicate owned declarations: **none**.
- Manifest SHA256: `43b5f8366283883a81766b6ccb16f9f2c12dc70d59f54bc5f26b9a18e42428c1`.

Exporter exit 0 here is a successful partial preflight, not full-scope acceptance.
The first two original-runner batches have now finished: 49 of the first 50
symbolic modules passed; the one original-rule failure is recorded below. The qualified external snapshot, original independent
leanchecker, complete-owned template and all type/safety/axiom rules remain
unchanged. After A/B/W pass, final selection must still cover every one of the
324 modules, with no unselected modules or duplicate declarations. The exporter's
separate `full_p2_complete: false` boundary remains unchanged.

- [Preflight selection summary](p2-symbolic-audit-preflight-01-summary.json)
- [Preflight exact log](p2-symbolic-audit-preflight-01.log)

## Bounded proof experiment: retained failures and Toy05 results

The isolated generator keeps computed normal forms in checked propositions,
proof terms and temporary expressions. It does not install computed node/table
outputs as evaluator definitions. Each private block must pass synchronous
kernel checking before its facts enter the committed cache. All generator and
generated declarations remain inside the complete owned audit.

Toy attempts 01--03 failed, respectively, on missing Inhabited instances,
Decidable synthesis for a manually built Nat.le proposition, and an invalid
auxiliary-name prefix. Toy04 compiled, but its subsequent original owned audit
failed: read-only enumeration found exactly `draftBlock._unsafe_rec` with
**partial=true, unsafe=false, axiom=false**. The repair replaced named recursion
with direct `Nat.rec`; the original audit rule was not changed. The earlier
[Toy04 result](p1-node-proof-blocks-toy-04-summary.json),
[owned failure](p1-node-proof-blocks-toy-owned-01-summary.json), and
[actual flags](p1-toy-safety-inspect-01-summary.json) remain available.

Toy05 source `78decf5bb633707f0de05a9b8c4043e2d6b540d1510dc9e654ba4be549d76ed6`
compiled in 3.345535568 seconds under task
`job_d1b8ba77d78b48a8802777330ee307b3`.
Its eight nodes and two four-fact blocks are diagnostic only.
See [summary](p1-node-proof-blocks-toy-05-evidence-01-summary.json) and [exact log](p1-node-proof-blocks-toy-05-evidence-01.log).

The subsequent task `job_bcb4aaa3a0234ef7ba0201a5bb38ed02` has a deliberately
preserved **overall failure**: independent replay passed in 16.430367858 seconds,
and the unchanged original owned audit passed in 2.441669297 seconds for all
122 declarations and 62,640 printed type bytes. Only the supplementary Inspector
failed, because its Nat parser did not accept the actual canonical OfNat form.
This is not an original-audit failure.
See [summary](p1-node-proof-blocks-toy-owned-02-evidence-01-summary.json) and [exact log](p1-node-proof-blocks-toy-owned-02-evidence-01.log).

The Inspector-only retry `job_db16c9f2bd824904b864aa088a3179c0` passed in
2.323374157 seconds. It reused the successful replay/audit under exact
source/object/tool/receipt/log hashes and did not rerun those stages. It
confirmed two private safe theorem blocks, four facts each, 317 Expr nodes per
block, and 6,608 combined printed block-type bytes. All previous inputs and
artifacts were unchanged. See [summary](p1-toy-inspector-01-summary.json).

## Original Q80 first 128 nodes

The exact Q80 recurrence factorization had passed separately as
`job_7006b0d3c9724f71bd377d22f58bf026`, source
`2f2e00982c0e28a4e93187106df1d0eed5d0912aec2b6473c0737689ac9c2a48`.
The first three Q80 block-generator attempts are retained as failed diagnostics:
[attempt01](p1-q80-node-proof-blocks-01-evidence-01-summary.json),
[attempt02](p1-q80-node-proof-blocks-02-evidence-01-summary.json), and
[attempt03](p1-q80-node-proof-blocks-03-summary.json).
They received no proof credit and their failed objects were not used for audit.
The normal-form checks were corrected to recognize the actual Int.ofNat and
canonical Nat OfNat syntax without normalizing sourceState.

Attempt04 source
`a1c8c5f4e28548f6e216b514b888b3f76f28f95b15e9d7d016f607e1d3dbae39`
compiled under `job_1fa1aa052e7641fc88c13fd4f20726df` in 5.844367127 seconds.
It checked exactly two private blocks of 64 node equalities: indices
32769--32832 and 32833--32896. Its public entry-point naming was also exercised.
See [summary](p1-q80-node-proof-blocks-04-summary.json).

The full diagnostic `job_9ea2eb99d26c45458e1a8047fd77a5d1` then passed all three
stages: independent replay 21.427813175 seconds, unchanged original owned audit
4.212234670 seconds, and supplementary block inspection 3.180516430 seconds.
It covered **all 239 owned declarations**, all original safety/axiom rules and
complete printed types (253,903 bytes). The two block types total 153,270 bytes
and 10,746 Expr nodes without sharing. Source, object and tools matched the
before/after hashes. The object size was **8,996,936 bytes**.
See [summary](p1-q80-node-proof-blocks-owned-01-summary.json) and
[exact log](p1-q80-node-proof-blocks-owned-01.log).

## Compact proof-term diagnostic, still only 128 nodes

The frozen original source remains unchanged. The separate compact source is
`a6e9808c67847e27d8e09a9c2d68f117690d8b5bf9f49678e4eda14a41820d3f`.
It still runs fresh cbvEntry on every node. It discards that evaluator's long
proof and supplies `mkEqRefl value` to the unchanged explicit Eq.trans term,
whose second proof must have type `arithmetic = value`. Thus the existing
synchronous whole-block kernel check must establish that conversion. There is
no new axiom, unchecked acceptance path, numeric output definition, native
proof, resource option or changed mathematical statement. Constant-prefix
predecessors are the closed initialNode constant; other predecessor values are
four-integer normal forms. The current arithmetic expression contains no
sourceState evaluation.

The P1 submission encountered a connection timeout. Root cancelled its own
queued P2 duplicate `1a77ba80e6d249de8dc6b880b87cdc2e` before execution; that
cancellation is not a Lean result. The same candidate ran on P3 instead.

P3 compilation `d7e40f1c3ed1476ea8cb838d0dba2d0e` passed in 3.539935766 seconds,
producing a **2,160,416-byte** object. Full diagnostic
`3a884a2251804c218f53e6c84512e238` also passed: independent replay
19.204545883 seconds, unchanged original owned audit 2.481176715 seconds, and
supplementary Inspector 2.072273204 seconds. It again covered 239 owned
declarations and both complete 64-fact blocks; all 255,113 printed owned-type
bytes were retained. The block types still total 153,270 bytes. All source,
object and tool snapshots were unchanged.
See [compile result](p3-q80-node-proof-blocks-compact-01-summary.json) and
[full diagnostic result](p3-q80-node-proof-blocks-compact-owned-01-summary.json).

| Isolated build | Invoked closed node proofs | Object bytes | Evidence |
|---|---:|---:|---|
| Original helper-only baseline | 0 | 1,685,176 | [summary](p1-q80-node-proof-blocks-baseline-01-summary.json) |
| Original block proof terms | 128 | 8,996,936 | [summary](p1-q80-node-proof-blocks-owned-01-summary.json) |
| Compact conversion proof terms | 128 | 2,160,416 | [summary](p3-q80-node-proof-blocks-compact-owned-01-summary.json) |

The helper baseline task `job_51af979eee5b4221b3446cfa0ba4abc7` compiled in
2.549563121 seconds. Its remote diagnostic.json has a malformed trailing escape;
**only the complete MCP stdout is used for this measurement**. That remote
receipt is not repaired or treated as audit provenance, and no baseline replay
or owned audit is claimed.

These are actual isolated measurements, not a linear model or a complete-table
resource bound. The compact object is smaller in this measured build; neither
this comparison nor the small diagnostic establishes the complete 131072-node
construction, final archived rational equality, A, B or W. A larger 258-block
experiment is being prepared separately; this checkpoint grants it no result.

## Archived-total interface: generic bridges only

P2 task `a1ec65064d4e4f73a55fab7759a0eca7` compiled source
`24d49de5de1cc57e88f30117c4c05b9be91e2e3bb6e9325a1d201111ad8f2e0e`
in 4.987300205 child seconds against the existing project imports. The three
checked interfaces are `fixedUpperWith_factor`, `fixedUpper_from_source_node`
and `cached_total_from_source_node`. Their printed axiom sets were permitted
subsets of propext, Classical.choice and Quot.sound.

The generic node premise was retained. The finisher was defined but **not
executed**, and this run did not prove the numerical endpoint. Canonical source,
registry, absent A object and qualified native binding were unchanged.
See [summary](p2-q80-archived-interface-01-summary.json) and [exact log](p2-q80-archived-interface-01.log).

## Completed original audit batches: 49 of 50 targets passed

Both batches used the unchanged original runner/template, source pin and ordered
324-module scope. Each completed its normal source/registry/native/checker
postchecks, including the failed second batch. The audit result of each module
remains distinct from the overall batch exit code.

| Batch | Task | Original runner result | Normal postchecks |
|---|---|---:|---|
| First 10 topological symbolic targets | `b7a273f404aa417cac93ae283d07340c` | 10/10 accepted, exit 0 | passed |
| Next 40 topological symbolic targets | `2d0e4b6dd5814357bc061ae6d3e3abe8` | 39/40 accepted, exit 1 | passed |

These batches cover disjoint targets and yield **49 successful original-runner
module audits out of 50 attempted**. The sole failure is
`ImbalancedChen.P2HistoricLogPointInterpreter`. The original exporter has not
been rerun to select a completed full-scope manifest, so this is not a claim
that a new export selected 49 receipts or that the full 324 audit passed.
See [first batch](p2-owned-symbolic-000-r01-evidence-01-summary.json) and
[second batch](p2-owned-symbolic-001-r01-summary.json).

Read-only retrieval `f41c76329eff474e8bcc7213772f8983` preserved the exact failed
receipt, source and 257,453-byte original audit log. The module's independent
replay had passed in 5.039 seconds, while the original owned audit failed in
4.764 seconds. A successful retrieval task does not change that failure.
The embedded compressed source/log/receipt payloads were independently decoded
and checked against all stated byte counts and SHA-256 hashes.
See [summary](p2-logpoint-owned-failure-01-summary.json).

The first flags attempt `989971f61afe4043ae844be846fded7f` failed because `rg`
was unavailable; the actual error is retained. The second attempt
`ea2ffa02ed8748129cd7faf79b6944d1` used git grep and completed read-only inspection:
**135 owned declarations, exactly one flagged declaration**,
`ImbalancedChen.Certificates.P2HistoricLogPointInterpreter.oddLoop._unsafe_rec`,
with **partial=true, unsafe=false, axiom=false**. No waiver or altered template
was introduced. See [failed flags attempt](p2-logpoint-flags-01-summary.json) and
[complete flags result](p2-logpoint-flags-02-summary.json).

## Remaining acceptance work and evidence integrity

The 321 symbolic compiler acceptance remains intact. A is unaccepted; B and W
have not run, and the full 324-module owned audit and final exporter selection
remain incomplete. There are 272 symbolic modules without a successful audit
in these two batches (including the one failure), plus the three finite/whole
modules. Any changed module and its affected proof/import closure must satisfy
the unchanged qualification and selection rules before a receipt is reused.
No board or production source was changed by this evidence checkpoint.

This update materializes 17 task records from two frozen transfer payloads:
51 log/status/summary files, with **1,374,296 exact task-output bytes** in total.
Every base64 chunk was checked for contiguous byte offsets, decoded length,
final EOF, task-reported total length and no truncation. Supplied structured
results were matched to complete JSON records in the exact stdout. Conflicting
older receipt files were retained under their existing names; new evidence
views use an `-evidence-01` suffix where needed.

The [evidence manifest](p24-node-blocks-evidence-manifest-20261126.json) records
payload hashes, every receipt/source/wrapper path and hash, and the preserved
acceptance boundaries. Its publication inventory contains only documents,
diagnostic source snapshots and wrappers; it does not modify production Lean
modules, original gates, other agents' candidates or plans.
