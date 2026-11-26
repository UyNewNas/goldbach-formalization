# P2.4 isolated node-proof-block experiment

## Scope and reason

Original A03 failed at source pin `909214bbfb5ca9caa74fcc1b6f95b469bf43e125`. Its masked original exception is not retrospectively reclassified. The subsequent raw diagnostic task `548f0b1357034b6e8c16afe4aef9d1a5` actually reported `(kernel) excessive memory consumption detected` at the first closed A equality under the original 11264 MiB Lean budget. The full map-prefix-03 diagnostic `423c0bbff0a54baea7e078a19d3f0c23` reported the same kernel memory-limit exception despite reducing the evaluated update range. Both retained source/registry/native bindings and grant no acceptance. This establishes the concrete need for a proof method that releases kernel checking caches between bounded pieces. The map-prefix source was not promoted.

The small isolated block experiment remains a mechanism test, not production acceptance. Attempt01 exposed missing Inhabited instances from partial array access; attempt02 replaced those sites with checked optional access. Attempt02 then exposed a raw Nat.le expression without the expected Decidable instance shape; attempt03 uses Meta.mkLe at the two sites. Attempt03 reached block declaration insertion and exposed an auxiliary-name prefix restriction; attempt04 uses the active theorem's naming context and compiled successfully. Its independent leanchecker replay passed, but the unchanged complete owned audit rejected the generated draftBlock._unsafe_rec declaration. Actual complete flag enumeration identified exactly one offender, with partial=true, unsafe=false and axiom=false. The next minimal repair uses direct Nat.rec instead of named equation recursion, retaining the same let scopes and acceptance boundaries. Exact failed logs are retained; compiler recovery sorryAx is not an authored proof or a successful artifact.

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
