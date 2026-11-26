# P2.4 isolated node-proof-block experiment

## Scope and reason

Original A03 failed at source pin `909214bbfb5ca9caa74fcc1b6f95b469bf43e125`. Its original kernel exception remains unknown. Raw diagnostic task `548f0b1357034b6e8c16afe4aef9d1a5` is queued. The minimally changed map-prefix-03 candidate is separate and has not been promoted. This plan authorizes only a small, isolated proof-generation experiment while the original diagnostic waits; it does not choose a replacement production proof or grant P2 acceptance.

The design reviewer checked the pinned Lean implementation of `cbvEntry`, `mkAuxLemma`, per-theorem kernel checker lifetime and the unchanged owned-declaration audit. A small equation for each source node can be checked without reducing an entire table. A block theorem must contain only its own small node facts, because complete-tree snapshots would repeatedly expand in the mandatory full type audit.

## Invariants

- Keep all production sources, the 324-module closure, public statements, numerical parameters, checker, audit template and resource limits unchanged.
- No authored sorry/admit, axioms, native_decide, unsafe or partial owned declarations.
- No numerical table, first-integral, tail or charge-list output installed as an evaluator definition.
- Normal forms may occur only as checked equality outputs, proof terms and temporary generator expressions.
- Every block must pass synchronous kernel checking before its facts enter the committed temporary cache.
- Every private and generated declaration remains subject to the complete owned safety, axiom and untruncated-type rules.
- Use the existing `cbv.maxSteps` and no resource-option increase.

## Experiment architecture

Use one isolated Lean module with a four-Int node, a functional `Nat.rec` state that writes one increasing index per step, and a three-predecessor update. First prove the generic factorization and completed-index stability. A small instance uses grid 2, a proved four-node constant prefix, nodes 5 through 12 and two blocks of four facts. The final query at index 10 in the state completed through 12 exercises the stability transport.

For one node, instantiate the checked source recurrence and substitute the three previously proved node values by congruence. Run fresh `cbvEntry` only on that closed small formula. Require an actual constructor normal form and retain its equality proof. Keep within-block facts as proof-valued lets; build a balanced And tree, close the lets, then call `mkAuxLemma` with the official synchronous-check setting. Verify that the returned declaration is a safe private theorem. Across blocks, facts are projections of already checked theorem constants.

## Steps and evidence

1. Write complete generic source/recurrence/stability proofs and a bounded generator in a new scratch diagnostic file. Review the cache publication boundary and ensure the generator never replaces the source function by a numerical definition.
2. Compile the small isolated module under the pinned Lean and the recorded Std diagnostic flags. Preserve every actual failure and repair only its demonstrated cause.
3. Replay the resulting object with the pinned independent leanchecker, then inspect every declaration owned by the toy module using the original inventory, safety, axiom and full-type rules. This is diagnostic evidence only; it is not a canonical P2 receipt.
4. Record source/object sizes, generated block count, type sizes, time and memory. Confirm that block types contain only the current block's facts. Do not extrapolate an unmeasured full-size runtime.
5. Stop this experiment after its mechanism and audit compatibility are resolved. A production proposal requires the actual raw A result, exact original Q80 arithmetic factorization, further source review and the unchanged A/B/W/audit gates.

## Publication and execution

Root coordinates remote submissions so existing P1/P2/P3 work is preserved. The implementation agent may edit only its new diagnostic file and accompanying experiment notes; it must not publish or mutate production source. Git-backed evidence and the execution plan will be published by root with the actual outcome. Existing user authorization to continue P2.4 covers this reversible internal proof investigation; no new approval gate is introduced.
