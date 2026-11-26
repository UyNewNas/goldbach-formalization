# P2.4 compact node blocks and total logarithm loop: source promotion

Date: 2026-11-26. Parent publication: e3823834973080c35cbd8e0decbe8884896e5025.
The latest completed original 321 compiler gate is now at the active P2 source
`6e616f4e0372555f7a78bcdba3e198d0e277eec8`. Task
`6a0e0788dce1478985474f7aa68bb4d6` exited 0 with complete 321 closure: 300 reused,
21 freshly compiled, no pending/failed modules, and normal completion.
Checker elapsed 311.821 seconds; outer elapsed 316.959 seconds; peak 4,356,182,016 bytes.
See its [canonical summary](p2-strict-symbolic-node-blocks-natrec-01-summary.json)
and [complete exact task log](p2-strict-symbolic-node-blocks-natrec-01.log).
Formal A4 is running without a terminal result; full324 acceptance remains false.

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
2. Original A4 task `b474be9062b8407eb0963018070ce4e4` is running at the same source.
   Its original zero-budget 321 prerequisite passed with 321 reused in 78.264 seconds.
   At the latest 10:48 UTC report it was still running, elapsed about 1256 seconds.
   The earlier 10:42 sample recorded peak memory 4,350,230,528 bytes. The unchanged
   original 3000-second A gate has no terminal result; A is not accepted.
3. B and W have not run and still require original acceptance in order after A.
4. P2 task `3632d273c69c4701bfdc6dc4ff1c2000` is queued for original full324 historical
   receipt selection and the first 40 unaccepted symbolic owned audits. The previous 49
   successful audits were at pin909; the selector must validate their current bindings.
   No new selected count or audit success is assigned before that task returns.
5. Final full324 selection must still leave no unselected modules or duplicate declarations.

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
Root is preserving the bounded receipt and full compressed evidence separately.
This full2048 result remains diagnostic-only; A/B/W and canonical full324 remain
incomplete. All original budgets, source-option boundaries and acceptance gates
remain in force.


The [bounded full2048 owned receipt](p3-q80-node-proof-blocks-compact-2048-owned-01-summary.json)
and [exact bounded task output](p3-q80-node-proof-blocks-compact-2048-owned-01.log)
are preserved by root. The complete large archive will be supplemented separately;
its transfer is not a new compiler or audit run.
