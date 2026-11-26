# P2.4 compact node blocks and total logarithm loop: source promotion

Date: 2026-11-26. Parent publication: e3823834973080c35cbd8e0decbe8884896e5025.
The last accepted canonical symbolic compilation remains pinned to
909214bbfb5ca9caa74fcc1b6f95b469bf43e125 until the original checker finishes at the new source commit.

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

The 258-block full logs remain in their immutable P3 attempt directories; exact compressed retrieval
is queued as 7ec76d0e8d794337a1c90d0c2ebf588f. This does not replace the already successful audit result.

## Gates still required

1. Fast-forward the existing P2 checkout under its existing lock and verify both source hashes.
2. Run the unchanged original checker with a positive budget over all five symbolic roots / 321 modules,
   because the shared logarithm module changed.
3. Run the original finite A gate with the same prerequisites and resource limits.
4. If A is accepted, run the original B and W gates in order.
5. Re-select valid original owned-audit receipts against the new dependency bindings and complete
   all 324 modules with no unselected modules or duplicates.

At this source promotion, canonical A is not accepted, B/W have not run,
and full324 completion is false. The previous 49 accepted owned audits were at pin909;
their continued applicability must be checked after the dependency change.
The full2048 standalone diagnostic is prepared but unsubmitted, because the original A gate is prioritized.
