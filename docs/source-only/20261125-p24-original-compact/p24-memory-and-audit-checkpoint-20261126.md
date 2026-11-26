# P2.4 kernel memory diagnosis and early symbolic audit

## Nine-module recursion repair: pre-integration checkpoint

Recorded 2026-11-26 13:39:06 UTC. This source promotion contains exactly nine production module
changes. Every candidate has separately passed compilation, independent
leanchecker replay, and the unchanged original complete owned/type audit.
The active P2 checkout at this checkpoint is still `6e616f4e0372555f7a78bcdba3e198d0e277eec8`. The new combined
source has not yet passed the original 321/A/B/W or final full324 gates.
Historical 322 compiler passes and 87 accepted original receipts remain tied to
their old source/object bindings; they are not copied as new-source acceptance.

| Candidate | Successful isolated task | Complete owned declarations |
|---|---|---:|
| DataCore | `b9065e2fa34c495d8b6691e4c26474c4` | 58 |
| FiniteSelector | `f2ffa9d3726247abb92bbef7c85d9ada` | 89 |
| Q80Encloser | `8d56c275c9174285b46c320201d11d33` | 193 |
| Q80ArrayTable | `8d56c275c9174285b46c320201d11d33` | 19 |
| AdaptiveForestSourceIdentity | `5bf981f9bbd5432f8765bb099af95cd7` | 42 |
| PriorityForestLedger | `4164a39fc61e485ebabec90f4761301a` | 201 |
| ConcreteLoop | `df72bc1bd44d4eb3aabca7cd80785131` | 106 |
| ConcreteRun | `dd367ab8f2b643d5804840e840928551` | 155 |
| CachedRun | `af16794dc5d34e17b425b4556fca60ca` | 99 |

DataCore adds only `import Lean.Elab.Command`, allowing the unchanged original
audit command to elaborate. The other eight modules replace the 25 observed
partial structural recursion implementations with explicit safe recursors.
Existing public theorem statements, branches, queue/root/leaf order, serial
progression, zero-fuel behavior, original Q80 arithmetic and numerical targets
are retained. Proof edits normalize only the corresponding recursion equations.
The [exact source and status manifest](p24-nine-source-promotion-20261126.json)
and complete failed/successful diagnostics bind each candidate to its bytes.

The shared tree fold is computable and has a proved sufficient bound derived
from the original split geometry: sum of three nonnegative integer coordinate
widths plus one. A legal split strictly decreases the selected width and leaves
the other two unchanged. Its leaf/split equations were checked, and task
`e046315a0a574746859728913b59e07b` passed all three stages with 19 owned
declarations. The earlier direct `SourceTree.rec` code-generation failure and
the `sizeOf` missing-LCNF failure are preserved as failed attempts. The accepted
helper uses neither. No speed or whole-run endpoint claim follows from this
small helper test.

Downstream isolated candidates import only this SHA-bound helper alongside the
old lower modules. The original 321 compiler must therefore check all nine
changes together. Static review identifies proof normalization as a remaining
integration risk, especially when both sides change from generated pattern
equations to explicit List.rec. No isolated result substitutes for that gate.

Storage retention also completed its separate verification. Stage1 task
`1107b856458b46deadc06036604e39a7` preserved every potentially mutable original
archive member in a 28,798,608-byte xz and verified 1,752 shared, immutable native
members. Independent stage2 task `602f0f63825a48a295d3b799dd9df0b4` reconstructed
the exact original 581,735,403-byte gzip, SHA `3fae348f45b7bab70e3fb11f5c8f68ff26ff5b03892ff44d9046bad1e8b94463`,
and rechecked all 13,856 members / 4,302,650,543 payload bytes. Only after this
pass was that redundant gzip removed, freeing 581,735,403 bytes. The original
manifest, qualified native files, source, objects, audit logs and registry were
not removed. The retained xz, reconstruction recipe, exact native bindings and
release receipt remain persistent. The old gzip path is now explicitly marked
as requiring reconstruction, not presented as a downloadable archive.

Full P2.4, full P2, the main theorem and a 6.809 bound remain uncompleted.

## Preserved source6e checkpoint and historical evidence

Updated 2026-11-26 12:34 UTC. P2 source and the latest completed original 321 compiler gate
are now both at `6e616f4e0372555f7a78bcdba3e198d0e277eec8`.
Task `6a0e0788dce1478985474f7aa68bb4d6` exited 0: all 321 closure modules passed,
300 reused and 21 freshly compiled, with no pending/failed/blocked modules and
normal batch completion. Checker elapsed 311.821 seconds; outer elapsed 316.959 seconds;
peak memory 4,356,182,016 bytes. Original finite A4 has now also passed its complete
canonical compiler gate. The 321 symbolic modules plus A give **322 compiled modules**;
A's independent owned audit has not run. B was cancelled before starting, W has not run,
and full324 owned completion remains false. A complete auxiliary risk scan has
identified the nine-module repair set described below.
See the [new-pin 321 receipt](p2-strict-symbolic-node-blocks-natrec-01-summary.json),
[exact 321 task log](p2-strict-symbolic-node-blocks-natrec-01.log), and
[source-promotion note](p24-source-node-blocks-promotion-20261126.md).

A4 task `b474be9062b8407eb0963018070ce4e4` finished at 11:04:08 UTC, exit 0:
102 closure modules, 101 reused, no failed/pending modules, normal completion.
Target compilation took 2049.975 seconds, the original checker 2100.638 seconds,
and the outer task 2182.81143353 seconds; peak memory was 4,963,540,992 bytes.
Its checked construction reached 2048 blocks / 131072 nodes / query index 163840.
See the [original A4 summary](p2-finite-a-node-blocks-04-summary.json),
[task status](p2-finite-a-node-blocks-04-status.json), and
[complete exact task log](p2-finite-a-node-blocks-04.log).
The 533,953-byte log SHA256 is
`27230c9aa9611fc07d556e6b205efd226a158a72ee9d290540b32cd48cfa0dcc`.

The completed evidence publication `c5d40919eb0dd40e27d53231d83e903d4473c025`
was refetched and byte-checked. It is separate from the unchanged active canonical
source pin 6e616 and does not add compiler or owned-audit credit.

## Accepted boundary

The original compiler gate has accepted the same 321 symbolic modules at source 6e616. The complete
scope remains 324 modules with ordered fingerprint
`c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f`.
A has passed the original compiler gate; its independent owned audit remains
unaccepted. B was cancelled while queued before execution; W has not run.
The full 324 owned audit is incomplete.
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

## Historical original exporter preflight at pin909

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
The bounded receipt and complete original compressed evidence are both preserved. This is a completed
isolated full2048 diagnostic. It does not establish the canonical archived
rational equality, formal finite A acceptance or the canonical full324 audit.

The [bounded full2048 owned receipt](p3-q80-node-proof-blocks-compact-2048-owned-01-summary.json)
and [exact bounded task output](p3-q80-node-proof-blocks-compact-2048-owned-01.log)
are preserved together with the complete archive.

The complete original full2048 evidence is now published at
[p3-q80-compact2048-evidence-20261126](p3-q80-compact2048-evidence-20261126/README.md).
The 18,737,284-byte xz archive has SHA256
`d7bffacf6698777981a58e765706d0f1823f6d860ba340cdc309faa356b6e9c3`.
Three consecutive byte parts reconstruct the exact original archive; the full
257,495,040-byte tar and all nine original members were verified. The frozen
original audit parser rechecked all 2285 declaration records, complete types,
allowed axioms, 2048 blocks and exactly-once coverage of all 131072 nodes.
The original single-blob attempt exceeded the connector's 16 MiB request limit;
that failed transfer and the successful lossless split transfer are both retained.
This transport work grants no additional canonical compiler or audit credit.



### Current gates at source 6e616

The original 321 compiler gate and A4 compiler gate passed, giving 322/324 compiled
modules. A's independent canonical replay/full-owned audit has not run. B task
`03120f6c22dd4fd0a38756bc2a4a7488` was cancelled while queued, before started_at was
set, after actual prerequisite owned failures appeared. This is not a B compiler
failure. W has not run. Neither the whole-functional result nor full P2.4 is claimed.

Original batch `3632d273c69c4701bfdc6dc4ff1c2000` is complete: its unchanged full324
export first reselected 49 valid receipts, then the original runner attempted 40
disjoint symbolic modules and accepted 38. DataCore failed because the unchanged
owned template's Command namespace was unavailable under a Std-only import.
FiniteSelector failed at the original safety rule; a read-only diagnostic identified
firstMax._unsafe_rec as partial. Canonical LogPoint's full 126-declaration audit
passed within this batch. The original batch postchecks passed and registry/native
bindings did not change. See the [complete batch result](p2-owned-source6e-symbolic-000-r01-summary.json)
and [exact task output](p2-owned-source6e-symbolic-000-r01.log).

There are therefore 87 accepted original receipts at the unchanged 6e616 inputs
(49 reselected plus 38 new), not a final full324 selection. All affected receipts
must be revalidated after the pending nine-module source promotion.

The original preflight export was reconstructed exactly after an attempted move
exposed that remote /tmp is private to each job. Task a529c559dca147fca13579ec2a94075d
restored the original 581,735,403-byte gzip, SHA256
`3fae348f45b7bab70e3fb11f5c8f68ff26ff5b03892ff44d9046bad1e8b94463`.
All 13855 indexed files matched; the original package adds PACKAGE_MANIFEST.json,
so the complete tar has 13856 members / 4,302,650,543 payload bytes. The source,
objects, raw audits, native inputs and original manifest were retained unchanged.
A separately recorded retention procedure is being prepared to preserve every
potentially mutable member and share only SHA-bound immutable native originals;
the redundant gzip is not credited as released until cross-job exact reconstruction
and a release receipt both exist.

## Complete auxiliary risk scan and pending source repair

Task `cd81a620985346ccb4af4078d5b5de37` completed the diagnostic scan of all 321
symbolic modules: 9921 candidate occurrences, 9907 distinct declarations, and
zero missing ConstantInfo entries. It found **25 distinct partial declarations**
in eight modules. Each is an automatically generated `_unsafe_rec` with
partial=true, unsafe=false, axiom=false and no forbidden transitive axiom.
The Lean child exited 1 to report the actual negative result; the outer wrapper's
exit 0 means the complete diagnostic was preserved, not that an audit passed.

| Module suffix | Actual partial recursive implementation(s) |
|---|---|
| ActualThirdOriginalP4AOrdinaryFiniteSelector | firstMax |
| P2OriginalCompactQ80Encloser | firstSeries, logLoop |
| P2OriginalAdaptiveForestSourceIdentity | forestLeaves, sourceIntegerForest |
| P2OriginalPriorityForestLedger | entries, eraseForest, eraseTree, seedForest, treeEntries |
| P2OriginalCompactConcreteRun | forestJobs, putJobs, splitForestAt, splitTreeAt, treeJobs |
| P2OriginalCompactConcreteLoop | runFuel |
| P2OriginalCompactQ80ArrayTable | buildFrom |
| P2OriginalCompactCachedRun | cachedEntries, cachedForestJobs, cachedRunFuel, cachedSeedForest, cachedSplitForestAt, cachedSplitTreeAt, cachedTreeEntries, cachedTreeJobs |

The full raw log is 2,933,052 bytes, SHA256
`96a2cd3617b89ade3f607da66645d3d2421c9dbf4cd968ef8b99f2268ec307a4`;
its [lossless gzip](p2-owned-flags-risk-scan-01-child.log.gz), task/child status,
complete bad records, declaration ownership differences and exact templates are
preserved. The original owned template and its full-type/replay rules were never
modified by this auxiliary diagnostic.

Eight aggregate inventory mismatches consist only of fourteen serialized-only
`.eq_1` names whose actual owner is another imported module. All exist and have
acceptable flags; there are no environment-only names. For example, LogPoint's
126 serialized names versus 125 environment-owned names differ only by
`ImbalancedChen.Certificates.P2HistoricQ80DefectLookup.I80.Contains.eq_1`, actually
owned by P2HistoricSieveTableSemantics. This explains why a combined import scan
cannot substitute for the original per-module inventory check.

Together with the DataCore import failure, the repair set has nine source modules.
DataCore needs only `import Lean.Elab.Command`; the other eight need computable
structural recursion that does not create partial owned auxiliaries. All existing
public types, mathematical statements, branch order, numerical constants, source
resource options and original audit criteria remain fixed. The first DataCore
candidate passed compile/replay/full owned (58 declarations), and the firstMax
List.rec candidate passed all three stages (89 declarations). These are isolated
candidate results, not promoted canonical receipts.

The direct SourceTree.rec approach was actually rejected by Lean code generation
in the first CachedRun candidate. That complete failure is retained. No
noncomputable workaround is being substituted. Address operations are expressed
through the original address list/seed index. The later accepted tree fold uses
a bound proved from the original three coordinate widths. The intermediate
sizeOf candidate failed code generation and is not the accepted implementation.
The current original-gate integration status is recorded at the top of this file.

Both DataCore and FiniteSelector are in the original A102 and B103 closures.
DataCore's symbolic reverse closure contains 40 modules including itself;
FiniteSelector's contains 25, a subset of those 40. The additional seven repairs
will be integrated together. Reuse is decided only by the original compiler and
original receipt bindings after promotion, never by this source-only dependency
statistic. Canonical source remains 6e616 until the entire candidate set is ready.

#### Preserved 10:48--10:52 UTC report, before A4 completed

The following two paragraphs record that earlier observation only; their running
and queued states are superseded by the current results above.

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

## Historical pin909 audit batches: 49 of 50 targets passed

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
`ImbalancedChen.P2HistoricLogPointInterpreter`. At that historical checkpoint,
the original exporter had not been rerun; those batch results alone did not claim
a new 49-receipt selection or full324 completion. The later source6e selection
of 49 valid historical receipts is recorded separately in the current status.
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
batch is complete. Task `3632d273c69c4701bfdc6dc4ff1c2000` used that same full324
selector and revalidated 49 historical receipts, then finished a separate original
40-module batch with 38 accepted and two actual failures. The isolated126 success
is not counted as a canonical receipt; the later canonical LogPoint PASS belongs
to the 38 new accepted receipts, for 87 at unchanged 6e616 inputs.

## Remaining acceptance work and evidence integrity

At unchanged source 6e616, 322 compilation results and 87 original owned receipts
are supported by their distinct evidence. A's canonical owned audit, B, W and the
final complete original full324 export remain outstanding. The 25 partial
auxiliaries and DataCore import failure require the nine-module source repair
above before integration and revalidation. All historical failures, cancelled
before-start jobs, diagnostic-only results and actual successful gates retain
their separate status. No board, production source, threshold or original gate
was changed by this evidence checkpoint.

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
