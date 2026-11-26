# P2.4 kernel memory diagnosis and early symbolic audit

Updated 2026-11-26 10:52 UTC. P2 source and the latest completed original 321 compiler gate
are now both at `6e616f4e0372555f7a78bcdba3e198d0e277eec8`.
Task `6a0e0788dce1478985474f7aa68bb4d6` exited 0: all 321 closure modules passed,
300 reused and 21 freshly compiled, with no pending/failed/blocked modules and
normal batch completion. Checker elapsed 311.821 seconds; outer elapsed 316.959 seconds;
peak memory 4,356,182,016 bytes. The original finite A4 task is running, with no
terminal A result. B/W have not run and full324 owned completion remains false.
See the [new-pin 321 receipt](p2-strict-symbolic-node-blocks-natrec-01-summary.json),
[exact 321 task log](p2-strict-symbolic-node-blocks-natrec-01.log), and
[source-promotion note](p24-source-node-blocks-promotion-20261126.md).

## Accepted boundary

The original compiler gate has accepted the same 321 symbolic modules at source 6e616. The complete
scope remains 324 modules with ordered fingerprint
`c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f`.
A remains unaccepted; B and W have not run. The full 324 owned audit is incomplete.
The numerical target, original Q80 recurrence, two-million-split schedule,
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
construction, final archived rational equality, A, B or W. The later 258-block compilation and complete diagnostic successes are recorded
in the [source-promotion note](p24-source-node-blocks-promotion-20261126.md).
The exact [258 evidence archive](p3-q80-compact258-evidence-20261126.tar.gz)
has been recovered and root verified all nine files by streaming, including all
495 owned declarations and the complete 16512-node range; the
[verification record](p3-q80-compact258-evidence-verification-20261126.json)
records those checks. This update checked the compressed archive hash and Git
blob identity without expanding the 31,504,409 raw bytes locally.

### Full2048 node-prefix diagnostic: compilation, replay and complete owned audit passed

P3 task `fa34b07b43b443c38d4ab199956d9443` completed the isolated full2048
compilation: 2048 blocks, 131072 nodes, indices 32769 through 163840. Child elapsed
1476.221009249 seconds; outer elapsed 1476.74 seconds; peak memory 3,390,763,008 bytes.
The object is 307,094,128 bytes, SHA-256
`98b8ff0edb6421f459c4e951afc901340fb144b735c3857d1c1d45bf42cc418a`.
The child compiler log SHA is
`ac2c57eeb9d07fcef13ba8d6bd3aef8c6914ffd9a14270e87709a27a007b3716`.
See the [full2048 compile receipt](p3-q80-node-proof-blocks-compact-2048-01-summary.json)
and [complete task log](p3-q80-node-proof-blocks-compact-2048-01.log).
The original diagnostic budgets and source options were not changed.

The separate full diagnostic task `62cdaa31f3c34ad7ae9ef34dce95c3df` has now
exited 0, outer 583.995 seconds and peak 2,992,013,312 bytes. All stages passed:
independent replay 197.00807145000726 seconds, unchanged original owned audit
352.904295019 seconds, and exact block/whole-index inspection 21.233076391 seconds.
All 2285 owned declarations passed the original inventory/safety/axiom/full-type
rules. Complete owned types total 167,176,820 bytes; block types total 167,074,216
bytes. The 2048 blocks cover exactly 131072 facts at indices 32769--163840.
Source, object and tools matched their before/after hashes; no output truncation
was reported. The 85-byte replay log SHA is
`67a85fd4a01236adc22803fd221966c1abbfc6eadaa85b54d16f32736d910c87`.

The original audit.log is 171,331,783 bytes, SHA
`8f83c9d54855bae7476c318ae6f63963f7ed85feebb25c52d23d642f65d619cb`;
blocks.log is 32,307,861 bytes, SHA
`0192f2fddabdd5d5b147b76ca4b9685312af698f7823dcce1b2ef0b6e90a6ffa`;
the complete receipt is 53,344,445 bytes, SHA
`b17cfc86710eb343a245b096c2bd925cd9081b0a7187a0eaae9c5cd272d6fdf8`.
Root is preserving the bounded receipt and complete compressed evidence separately;
this update neither expands nor overwrites those artifacts. This is a completed
isolated full2048 diagnostic. It does not establish the canonical archived
rational equality, formal finite A acceptance or the canonical full324 audit.

The [bounded full2048 owned receipt](p3-q80-node-proof-blocks-compact-2048-owned-01-summary.json)
and [exact bounded task output](p3-q80-node-proof-blocks-compact-2048-owned-01.log)
are preserved by root. The complete large archive will be supplemented separately;
its transfer is not a new compiler or audit run.


### Formal A4 running; next original audit batch queued

Original finite A4 task `b474be9062b8407eb0963018070ce4e4` is running on P2 at
source 6e616. Its original zero-budget 321 prerequisite passed with all 321 modules
reused in 78.264 seconds. At the latest 10:48 UTC report, task elapsed was about 1256
seconds and A was still running without a terminal result. An earlier 10:42 UTC
sample recorded peak memory 4,350,230,528 bytes. The original 3000-second A gate is
unchanged; no A acceptance is recorded.

P2 task `3632d273c69c4701bfdc6dc4ff1c2000` is queued to run the original full324
exporter selection and then the first 40 still-unaccepted symbolic targets under
the unchanged original owned-audit rules. No selected count or batch result is
assigned before that task returns. The ordered 324 scope and all original gates
remain unchanged.

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

## LogPoint Nat.rec diagnostics and the new source commit

The original pin909 LogPoint audit failure remains historical evidence.
Candidate natrec01, task `9d1e6a22309041f191186ec689f5e376`, failed compilation
in 14.833596205 seconds at the original zero-case simplification: the target
still displayed Nat.rec at zero. Its equation, replay and owned stages did not
run. The exact failed source, 354-byte compiler log, original diagnostic receipt
and complete MCP stdout are retained.
See [natrec01 summary](p2-logpoint-natrec-01-summary.json).

Candidate natrec02 adds an explicit zero-state change in that proof. Its source
SHA is `07798022d2370d12091d123a8f55ab106ee08a02b5dd104ce84d30aed3882552`.
Task `98f55f532ef9426b9a8aaf518362b973` passed all isolated stages:

| Stage | Seconds | Result |
|---|---:|---|
| Complete module compilation | 16.026089040 | passed |
| Both original base/successor recurrence equations | 3.682128901 | passed by rfl |
| Independent leanchecker replay | 21.231294658 | passed |
| Unchanged original owned audit | 4.559286492 | all 126 declarations passed |

The complete 294,635-byte audit log contains 126 declaration records and
identical serialized/environment inventories. All owned declarations are safe,
nonpartial and nonaxiom, with allowed transitive axiom sets. Full printed types
total 70,600 UTF-8 bytes. The audit source is exactly the original template with
its two target-module occurrences replaced; reverse substitution reproduces
SHA `2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b`.
The isolated object is 1,569,296 bytes. Protected canonical source, registry,
object state and qualified native binding were unchanged.
See [natrec02 summary](p2-logpoint-natrec-02-summary.json),
[full original audit log](p2-logpoint-natrec-02-audit.log),
[exact source snapshot](p2-logpoint-natrec-02-source.lean), and
[both recurrence equations](p2-logpoint-natrec-02-equations.lean).

These successful stages ran in an isolated module while P2 was at pin909.
They do not create a canonical audit receipt for the promoted source 6e616,
and do not establish new-pin 321 compilation. The source-promotion note records
the second changed source, finite A SHA
`03e45537c9309e79c46fd924383d850935cb2b82a5de7ac4205731f4df048fcd`.
The separate original new-pin 321 compiler task has now completed with normal
postchecks: 321/321 accepted, 300 reused and 21 freshly compiled. This completion
is supported by its own [canonical receipt](p2-strict-symbolic-node-blocks-natrec-01-summary.json),
not by the earlier isolated 126-declaration diagnostic.

The new [LogPoint evidence manifest](p24-logpoint-natrec-evidence-manifest-20261126.json)
binds both complete task outputs, all ten gzip-decoded original artifacts and
the source snapshots. The earlier 72-file node-block evidence publication is
frozen at `e3823834973080c35cbd8e0decbe8884896e5025`; its recorded checkpoint hash
belongs to that publication, not this later checkpoint revision.

The [original audit reuse review](p24-owned-audit-reuse-after-source-promotion-20261126.md)
confirms that reuse depends on exact closure/source/object/tool/native and
artifact bindings, not project Git HEAD alone. The exporter can select valid
historical attempts even if latest.json is a failure. The new compiler
batch is complete; queued task 3632d273c69c4701bfdc6dc4ff1c2000 will use the same
full324 selector, then audit only its unselected symbolic targets. The old 49 successful audits must be revalidated under the
new bindings; the isolated126 success is not counted as a fiftieth canonical
receipt.

## Remaining acceptance work and evidence integrity

The latest original 321 compiler acceptance is now for source 6e616. Formal A4 is
running without a terminal result; B/W have not run. The full2048 isolated
compilation, independent replay and complete owned audit passed. Those isolated
results do not complete formal A or the canonical full324 owned audit; final
exporter selection remains incomplete. At the
old pin, 271 symbolic modules were unattempted and one attempted module failed.
The new pending list also includes any formerly successful receipt invalidated
by changed source/dependency bindings, plus the three finite/whole modules. Any changed module and its affected proof/import closure must satisfy
the unchanged qualification and selection rules before a receipt is reused.
No board or production source was changed by this evidence checkpoint.

The earlier node-block evidence publication materialized 17 task records from two frozen transfer payloads:
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
