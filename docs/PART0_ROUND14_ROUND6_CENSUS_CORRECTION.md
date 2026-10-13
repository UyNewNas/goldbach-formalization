# P0 Round 14 — Round6 defining-module census correction (verification pending)

Frozen manuscript: `ba6ec11d800eccc54406490631895e174de85766`. Shared proof baseline: `1a80c1bcce67886f699d097fc37fd245cd3620bf`. No proof statement, imported production module, or pinned dependency is changed.

## Exact predecessor and failure

P0 parent: `fc05c12670901153176504bb6c68e84e5e7bdea4`. Its core run [38428024402](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38428024402) is **failure**; envelope run [38428024374](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38428024374) is **success**. The core built the existing root, replayed it with the bundled leanchecker, audited root axioms, and exported Round3/Round4 types. Round6 failed in the audit census before a complete Round6 receipt could be produced.

Raw Round6 diagnostic: `ImbalancedChen.ActualHistoricalFifthCellIntegral: expected 23, got 22`. The observed defining-module counts are 23, 22, 15 and 9, respectively, for `HistoricalUpperFiveCellGeometry`, `ActualHistoricalFifthCellIntegral`, `ActualHistoricalFifthSavingIntegral`, and `HistoricalFifthCutoffInvariance`: sum **69**.

The earlier P1 intake (`verification/parts/p0/round6/P1_HISTORY_INTAKE.json`) asserts 23 for `ActualHistoricalFifthCellIntegral`, in conflict with the actual P0 compiler-origin enumeration. Its published source blob `a273c195869a858bbc3110f275c3ce96eaf15530` matches the producer's published blob on P1 branch `f5a62f9bc862b89d03d5d211379664d8866d689f`. The P1 metadata assertion is retained as an **unresolved evidence inconsistency** rather than silently rewritten. This correction follows the observed P0 defining-module enumeration; CI must still rerun and confirm there is no missed generated/private declaration.

## Precise incremental change

Only `verification/parts/p0/Round6Audit.lean` and `verification/parts/p0/check_round6_types.py` adjust the relevant expected count (23 to 22) and total (70 to 69). All per-declaration compiler type export, unsafe/new-axiom prohibition, allowed transitive-axiom set, final-bridge isolation and explicit `-t0 -DwarningAsError=true` invocation remain mandatory. No validations are dropped or downgraded.

## Verification and next step

This commit is a **SOURCE_ONLY check correction** until its exact-head core CI passes. The predecessor's failed Round6 is not a receipt. On the exact published SHA, require complete root build, bundled stock root replay, root axiom audit and complete Round3/Round4/Round6 compiler-type exports with the raw receipts; compare complete Round6 module inventory with producer metadata and record that discrepancy in the final receipt. If a count fails again, diagnose the new actual inventory; never blindly modify counts.

The conditional final bridge `current_theorem_1_1_of_manuscript_bounds` still contains `hLower` and `hUpper`; numerical budget, tail floor and all analytic inputs remain open. Do not declare the 1+1.75 theorem unconditional.
