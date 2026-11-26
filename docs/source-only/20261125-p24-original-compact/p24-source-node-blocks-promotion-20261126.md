# P2.4 compact node blocks and total logarithm loop: source promotion

## Current integration checkpoint: three proof adapters

Recorded 2026-11-26 14:07:54 UTC. P2 fast-forwarded to `1087bc663a46352f99b2e9a1da238aaf4b855fdf` and completed the unchanged original
321 compiler task `c8cd6d4256d4401da57be40cdb10ecb5` with **317/321 accepted**:
279 reused and 38 freshly compiled. The checker finished normally in 483.148 s;
the wrapper returned the original exit 1 after 616.948 s, peak 4,582,031,360 B.
The budget was not exhausted. All original source, runtime, native, full324
snapshot and unselected A/B/W-object postchecks passed.

Three actual proof failures remained: Q80Reachability, CachedRun and
Q80FixedBindings. Q80CompleteSoundness was blocked by a failed dependency.
The [complete task log](integration-proof-repairs/strict321-1087.log) and
[exact summary](integration-proof-repairs/strict321-1087-summary.json) preserve
this negative result. The prior nine isolated candidates remain individually
validated; that never implied joint acceptance.

This commit adapts only the following existing proofs:

- Reachability uses the proved treeEntries leaf/split equations, keeping the
  original subtree membership terms for its induction hypotheses.
- CachedRun unfolds the matching List.rec seed definitions once and rewrites
  the existing evaluator equality. It no longer feeds the unfolded induction
  hypothesis back into the same simp expansion. This is a static diagnosis
  of the observed maxRecDepth error; the new proof awaits the original gate.
- FixedBindings adds the locked Lean theorem `Nat.rec_eq_recCompiled` and
  `Nat.recCompiled` equations to the original norm_num list. These are proof
  rewrites used to expose the original 21-step recurrence; the firstSeries
  computation definition, comparison, constants and resource options are unchanged.

All three candidates retain the exact original statements, definitions, imports
and options. Their 27/6/20 original theorem headers are unchanged. Independent
static review has completed; compilation and original owned acceptance of these
new proof bodies remain pending. See the [source manifest](p24-integration-proof-repairs-20261126.json).

The original failed gate's complete raw receipts and snapshots remain persistent
on P2. A read-only archive retrieval inadvertently exceeded the MCP 2 MiB stdout
limit: 2,097,152 bytes were retained and 6,984,297 bytes discarded. That transfer
is explicitly incomplete and grants no acceptance. Bounded byte-preserving
retrieval is being performed from the unchanged originals.

A must still be revalidated at the eventual successful combined source. B, W,
complete original full324 owned/export acceptance, full P2.4/P2, the main theorem
and a 6.809 conclusion all remain pending.

## Preserved nine-source promotion checkpoint

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

Date: 2026-11-26. Parent publication: e3823834973080c35cbd8e0decbe8884896e5025.
Latest status update: 2026-11-26 12:34 UTC. Evidence publication
`c5d40919eb0dd40e27d53231d83e903d4473c025` has been published, refetched and
byte-checked; canonical production source remains 6e616.
The latest completed original 321 compiler gate is now at the active P2 source
`6e616f4e0372555f7a78bcdba3e198d0e277eec8`. Task
`6a0e0788dce1478985474f7aa68bb4d6` exited 0 with complete 321 closure: 300 reused,
21 freshly compiled, no pending/failed modules, and normal completion.
Checker elapsed 311.821 seconds; outer elapsed 316.959 seconds; peak 4,356,182,016 bytes.
See its [canonical summary](p2-strict-symbolic-node-blocks-natrec-01-summary.json)
and [complete exact task log](p2-strict-symbolic-node-blocks-natrec-01.log).
Formal A4 has also passed its original compiler gate, yielding **322 compiled
modules** across the fixed 321 plus A. A's canonical independent owned audit is
not complete; B was cancelled before starting and W has not run. Full324 acceptance
remains false. A4 finished at 11:04:08 UTC; its separate
[canonical summary](p2-finite-a-node-blocks-04-summary.json),
[task status](p2-finite-a-node-blocks-04-status.json), and
[complete exact task log](p2-finite-a-node-blocks-04.log) support that result.

## Source changes

| Module | SHA-256 | Change |
|---|---|---|
| P2HistoricLogPointInterpreter | 07798022d2370d12091d123a8f55ab106ee08a02b5dd104ce84d30aed3882552 | Express the same oddLoop base and successor operations directly by Nat.rec; expose the zero-step state with change in one existing proof. |
| P2OriginalCompactArchivedTotalCandidate | 03e45537c9309e79c46fd924383d850935cb2b82a5de7ac4205731f4df048fcd | Replace the failing full-map reduction with 2048 synchronously kernel-checked blocks, each containing 64 original Q80 node equalities, followed by the original archived-total formula. |

The first change addresses the actual owned-audit rejection of
oddLoop._unsafe_rec: partial=true, unsafe=false, axiom=false.
There is no new axiom, authored partial/unsafe declaration, or noncomputable workaround.

The second change retains the original public theorem statements, four original formula helpers,
archived rational, and complete second public proof. The two existing local zero resource options
remain scoped to the same first public theorem. The compiler/audit tools, memory limits,
ordered project-module scope, root order, split budget, and numerical targets are unchanged.

The Q80 arithmetic remains the original node update using i-1, (i-g)-1, and i-g.
Computed nodes exist only as temporary expressions and in checked theorem propositions/proofs.
No observed table/first/tail/charge output is installed as an evaluator definition.
Each arithmetic expression is evaluated by the existing cbv entry, and its short reflexivity proof
is placed in an explicit Eq.trans slot whose expected type is arithmetic = value.
The synchronous kernel check must validate that conversion before a block enters the certificate cache.
Only the completed point at 10*g is transported to the original full 12*g source table.

## Evidence available before this source change

- compact128: P3 d7e40f1c3ed1476ea8cb838d0dba2d0e compiled the exact first 128 nodes.
  P3 3a884a2251804c218f53e6c84512e238 passed independent replay, the unchanged complete
  owned audit (239 declarations), and both exact 64-node block checks.
  Object size: 2,160,416 bytes; the prior trace-proof object was 8,996,936 bytes.
- compact258: P3 56afa9b1d65d4947bf7fe4c99ebb6a69 compiled 258 blocks / 16,512 nodes,
  indices 32769 through 49280, including the branch after 3*g.
  Child elapsed: 141.7109706239862 seconds. Object size: 40,598,824 bytes.
  P3 b849920ca6d94061a84a0e771df2bdd5 passed independent replay, the unchanged complete
  owned audit (495 declarations), and exact block/whole-index shape checks.
  Full untruncated audit output: 20,743,054 bytes, SHA-256
  be9b1c930266aea56d31066fca41fd617a389ddaa09aa49ad57b46f07cfe3051.
- LogPoint natrec02: P2 98f55f532ef9426b9a8aaf518362b973 passed complete isolated compilation,
  both original recurrence equations, independent replay, and the unchanged complete owned audit
  (126 declarations, all safe/nonpartial/nonaxiom and allowed transitive axioms only).
  Stage seconds: compile 16.026089039994986; equations 3.6821289009967586;
  replay 21.231294657991384; audit 4.559286491989042.
  Audit log: 294,635 bytes, SHA-256
  66847256a4f499dc69ece1773f6fdef548abecd6ca8b9e264e3260a3e613a4a8.
  Source, canonical object state, registry, and external native binding were unchanged.
- Natrec01 P2 9d1e6a22309041f191186ec689f5e376 failed at the original zero-case simp proof.
  Natrec02 adds only the explicit zero-state change step beyond that candidate; the failure is retained.
- The final formula bridge helpers passed their isolated P2 interface compilation;
  that interface diagnostic did not invoke the closed final arithmetic finisher.
- Two independent source reviews found no specific mathematical/wiring defect in the full A candidate.
  Reviews are not compilation or acceptance receipts.

The exact 258-block evidence has now been recovered as
[p3-q80-compact258-evidence-20261126.tar.gz](p3-q80-compact258-evidence-20261126.tar.gz):
2,207,006 bytes, SHA-256 `0150828e634c9384d7524028a587f256be54646ca498861016028f85009c719c`.
Root streamed and verified all nine original files (31,504,409 bytes), complete
495-declaration inventory/safety/axioms/types and the full 258-by-64 index coverage.
The [verification record](p3-q80-compact258-evidence-verification-20261126.json)
preserves those checks. The archive was not expanded in the local recovery directory.
Its already-created Git blob is `acab78c20ddb6c7d348c79490462531eaa40f251`;
publish that blob as binary rather than decoding it as UTF-8.

## Current original gates and remaining work

1. P2 fast-forward to 6e616 and the original 321 compiler gate have completed successfully.
   All 321 modules passed: 300 reused, 21 fresh, no pending/failed modules and normal completion.
2. Original A4 task `b474be9062b8407eb0963018070ce4e4` passed at the same source:
   102 closure modules / 101 reused, no failed or pending modules, original normal
   completion and exit 0. Its zero-budget 321 prerequisite reused all 321 in
   78.264 seconds. Target compilation took 2049.975 seconds, the original checker
   2100.638 seconds, and the outer task 2182.81143353 seconds; peak memory was
   4,963,540,992 bytes. The checked construction reached 2048 blocks / 131072 nodes /
   query 163840, under the unchanged original 3000-second gate. The exact task log
   is 533,953 bytes, SHA `27230c9aa9611fc07d556e6b205efd226a158a72ee9d290540b32cd48cfa0dcc`.
   This is compilation acceptance; A's canonical independent replay/owned audit remains outstanding.
3. B was cancelled before starting after the actual owned failures below; W has
   not run. The existing W wrapper still requires original A and B prerequisites.
4. The unchanged full324 exporter reselected 49 receipts at 6e616. The following
   original 40-module batch completed with 38 accepted and two failures (DataCore
   Command import and FiniteSelector partial firstMax._unsafe_rec). Its normal
   postchecks passed. This supports 87 original receipts at unchanged inputs, not
   final full324 selection.
5. A complete auxiliary risk scan examined all 321 symbolic modules and found
   25 partial auxiliaries in eight modules. The detailed nine-module repair set,
   including DataCore, is below. Auxiliary scans grant no original audit credit.
6. After the entire candidate set is ready, the affected original compiler,
   independent replay, full-owned/type and final full324 selection gates must run
   under the same original resource envelopes. No unselected module or duplicate
   owned declaration may remain in the final selection.

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

### Preserved earlier gate status: 10:42--10:52 UTC

At 10:48 UTC, A4 was still running after about 1256 seconds, with no terminal
result; the 10:42 sample recorded peak memory 4,350,230,528 bytes. At the 10:52
checkpoint the 40-module original audit task was still queued and no new-pin
selection count was available. Those earlier observations are retained as history
and are superseded by the A4 pass and current audit progress above. All earlier
failed diagnostics and original-gate failures remain preserved in their receipts.

## Full2048 isolated fallback result

P3 compile task `fa34b07b43b443c38d4ab199956d9443` passed: 2048 blocks, 131072 nodes,
indices 32769--163840, child 1476.221009249 seconds, outer 1476.74 seconds and
peak 3,390,763,008 bytes. Its object is 307,094,128 bytes, SHA
`98b8ff0edb6421f459c4e951afc901340fb144b735c3857d1c1d45bf42cc418a`;
child-log SHA is `ac2c57eeb9d07fcef13ba8d6bd3aef8c6914ffd9a14270e87709a27a007b3716`.
See the [compile summary](p3-q80-node-proof-blocks-compact-2048-01-summary.json)
and [complete exact task output](p3-q80-node-proof-blocks-compact-2048-01.log).
This checks the entire 2048-block node prefix; it is not canonical finite A acceptance.

Full diagnostic task `62cdaa31f3c34ad7ae9ef34dce95c3df` has exited 0:
outer 583.995 seconds, peak 2,992,013,312 bytes. Independent replay passed in
197.00807145000726 seconds, the unchanged original owned audit in 352.904295019
seconds, and exact block/whole-index checks in 21.233076391 seconds.
All 2285 owned declarations passed the original rules; all 2048 blocks / 131072 facts
cover exactly 32769--163840. Full owned types total 167,176,820 bytes, including
167,074,216 block-type bytes. Source/object/tools were unchanged and no truncation
was reported. The replay log is 85 bytes, SHA
`67a85fd4a01236adc22803fd221966c1abbfc6eadaa85b54d16f32736d910c87`.
Audit.log is 171,331,783 bytes, SHA
`8f83c9d54855bae7476c318ae6f63963f7ed85feebb25c52d23d642f65d619cb`;
blocks.log is 32,307,861 bytes, SHA
`0192f2fddabdd5d5b147b76ca4b9685312af698f7823dcce1b2ef0b6e90a6ffa`;
the complete receipt is 53,344,445 bytes, SHA
`b17cfc86710eb343a245b096c2bd925cd9081b0a7187a0eaae9c5cd272d6fdf8`.
The bounded receipt and full original compressed archive have both been preserved.
This full2048 result remains diagnostic-only. Canonical A compilation is now
supported by the separate A4 receipt above, while A's canonical owned audit,
B, W and final full324 acceptance remain incomplete. All original budgets,
source-option boundaries and acceptance gates remain in force.


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

