# P2 hybrid actual-integral to original Q80 tree ledger (2026-11-11, round 9)

SOURCE ONLY; UNCOMPILED.
Parent: 3b38dada03bd17331b428f80889f39e59ffa4671.
Branch: chatgpt/p2-integral-rounding-20261111.
Source: ImbalancedChen/Certificates/P2HybridThirdChargeLedger.lean (183 lines, 19 explicit source entries).
No Lean/lake/Elan, numerical producer/checker, Codex service, user computer or CI run. No workflow, pin, public root or existing source changed.

## Latest state and ownership

- Latest P2 head was the prior ordinary-dispatch request. Read MEAN_DISPATCH_HANDOFF.md and source 26b3b255860e7025f12457d42428e8445be5a3bf (blob 0b40ccb5944f7ca5e7fbef81ca7a3aaf80d2dbbe). Its request remains REQUESTED / WAITING_FOR_EXISTING_COMPILATION_REPAIR_FLOW; no exact-source run or acceptance was observed.
- Existing compilation-repair branch remains 5db345d60c12ce03457a0a6174e0be7c8a65f1d6, a bounded StoredBlock000-004 validation configuration, explicitly not full T01 acceptance. The predecessor P2 request is absent at that snapshot. This round does not select, dispatch or duplicate any run.
- Read current map c8c93a71f00811284d0aef149aa5efa7c66bc413, reuse audit 1611b2ba26eef96bf9d9a7b7e54718fd41b69c2f, historical review e7600f8a4819fdd5eb2ddaefec09f415dae269f9 and unchanged lock/toolchain.
- Manuscript master remains 3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e. Body d529bea2ecfcc74d64fc1664ac770a3becaa7c79 and paired JSON 49499697cca96de5f7b779e95077874ce5f9d119 are unchanged. Adopted paired scope remains 17572 rows / 186 strips. No finite row checks were repeated.
- Complete nonrecursive ImbalancedChen tree 4b2c223b8ad8bdd217404834923d4363f0b09a45 has 3138 entries; Certificates has 96; both truncated=false. Source lookup did not rely on the contents endpoint's first 1000 entries.
- P4 handoff remains eea9486f7b101d484e2938e97499c1d77cc1a67a; P1 actual-parent branch 1006a047bd5dea9ebad05478b806e6232ec6b96b was checked. Full87/history, fourth payload, All22 and complete-tail ownership are preserved. All new writes are P2 Certificates/** and its source-only report/static/request paths.

## Minimal missing bridge and reuse

R4 P2OriginalThirdTreeCertificate only accepted BoxGuard entries. R8 now supplies the complete ordinary P160 actual leaf upper, but it had no way to feed a SAME original positional Q80 ledger together with the existing BoxGuard rule. No equivalent mixed consumer was found in the inspected current sources; inaccessible local/unpublished material remains unverified.

Reused unchanged:
- R4 integerLeaves, literalLeaf, originalLeaves_eq_integerLeaves, root cover and existing BoxGuard local_integral_bounds.
- R8 checked_ordinary_integral_upper, including all optional-mean rejection/fallback behavior.
- P4AClosedTreeCoordinatePropagation's original DEN, min/max integer endpoints, cuts, empty children and closed-face identities.
- ClosedLeafStoredChargeAggregation's originalCompactThirdCorrection_le_sum_storedCharges and originalCompactThirdCorrection_le_originalAllowance. No tree labelling, integral-sum or overlap proof is reconstructed.
- Existing realBox_grid_binding and value_mono. Only the necessary fixed 80-to-160 scale dictionary is added.
- Fixed mathlib Forall2 imp/length/map APIs, read at e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, Mathlib/Data/List/Forall2.lean blob 6c8e708962b5c72aae9c34b539062589688a9877.

Generic rational roundUp/error lemmas were located in P2DirectedLogRounding but are NOT reimplemented or needed: this adapter does not generate a new ceiling or a replacement charge list. The paired fixed-width ledger and actual signed-fibre rounding suppliers have different scope and were not substituted.

## New mixed semantic ledger

Source is either an existing BoxGuard or an ordinary lo/hi integer box. Every Entry has ONE integer Q80 charge.

- Box entries reuse the existing R4 finite rational validity and actual integral rule, including outer-box containment.
- Ordinary entries must bind their own lo and hi EXACTLY to the current integerLeaves occurrence. Geometry acceptance at some other coordinates cannot pay this leaf.
- They must also supply the existing finite geometry check and the exact directed INTEGER comparison:
  ordinaryUpper(table,lo,hi) <= charge * 2^80.
- The existing value_mono plus the exact dictionary
  value160(charge*2^80) = charge/2^80
  converts this to the required real Q80 bound. It is valid for signed integers; no sign or bit-precision heuristic replaces the comparison.
- decode_eq_ordinary_point and literalLeaf_eq_ordinary_leaf identify the exact coordinate denominator and real compact intersection of both consumers.
- Entry.local_integral_bounds constructs the actual local integral bound and Q80 domination internally. No target integral, integrability or real containment estimate is an Entry field.
- entriesValid is List.Forall₂ over the exact original integerLeaves list. Length equality and the original mapped real-leaf list supply one bound per occurrence. No zip, truncation, deduplication or unbound permutation is used.
- realEntries feeds the existing closed-leaf scalar aggregator. compactIntegral_le_charge_sum gives the actual compact integral <= the exact sum of ALL stored Q80 integers divided once by 2^80.
- adoptedValid adds ONLY the original exact integer allowance from R4. adoptedValid_sound and the existing complete-third tail transport retain the adopted compact endpoint and Tnew once.

Both source bounds already contain the same compactKernel and factor four. This dictionary does not multiply by four again, divide by K or introduce the paired 1/80 factor.

## Directed domination and cumulative error boundary

No additional ceil or approximate rescaling is introduced. Every original Q80 margin must be sufficient for its actual entry, and the entire original charge sum must fit the adopted allowance. The exact scalar inequalities plus all-position summation account for every such margin. This does NOT say the two algorithms have zero difference.

Higher precision alone does not prove domination: their readers and nonlinear rounding can differ. Every actual integer comparison still needs proof. If those comparisons, the real tree/data bindings and the exact original sum are eventually established, this DIRECTED DOMINATION route is sufficient for the bound without first proving bitwise equality of the two algorithms. A separate claim of producer/runtime/stored-array identity would still require its own evidence.

The ledger is explicitly a NONCOMPUTABLE SEMANTIC PROP, not an executable whole-certificate Bool. ordinaryUpper still contains the real log/floor value-semantic backend. No Decidable instance or misleading runtime entriesCheck is supplied. The ordinary cost ABI/evaluator and actual finite acceptance remain unpaid.

All empty, zero-width, duplicate and shared-face occurrences are retained structurally. Their applicable valid entries and compatibility with their actual stored charges have NOT been constructed. In particular an ordinary rejection is not permission to omit a leaf; it still needs a valid existing BoxGuard or another separately established rule. No all-region/adopted-data closure is claimed.

## Verification and blockers

Two independent read-only reviews found no definite source, direction, position or normalization error. They checked the exact coordinate dictionary (explicit calc), signed scale, both local suppliers, Forall2/map transport, original sum/allowance and unchanged tail component.

Static proof-escape/comment/delimiter/import checks passed. No concrete tree, entry list, geometry check, cost, charge domination, adoptedValid witness or sum was evaluated.
Lean/Lake/Elan, kernel replay, complete expanded types/defining-module declarations including Source constructors/recursors, Entry projections and generated/private declarations, transitive axiom audit and audit replay: NOT RUN. No CI run, blue/green promotion or whole-P2 closure.

The public archive/source-manifest access point from the prior handoff is reused. Available-tool discovery found no release-ZIP extraction API; the safe workspace pwd probe returned No usable execution environment before executing a command. ZIP contents/exact independent producer/tree data remain unverified. No Codex service, user-host connection or substitute numerical route was used.

Still required:
- Exact-source compilation and full actual import-object/kernel/type/axiom acceptance.
- Actual original tree and complete per-occurrence entries/charge identities, not only the generic relation.
- All geometry/rational guards and integer domination proofs, plus the original integer sum.
- Executable ordinary cost semantics or another honest method for proving those concrete integer comparisons.
- Applicable outside/boundary/symmetric/above-mu/empty/zero-width suppliers where the current ordinary check cannot accept.
- Remaining adopted certificate-to-integral/error/normalization chains. P2.4 and whole P2 remain OPEN; P1 history/fourth data and P4 tails stay separately owned.

## Exact existing compilation delivery

Target: ImbalancedChen.Certificates.P2HybridThirdChargeLedger.
Direct imports:
- ImbalancedChen.Certificates.P2OriginalThirdTreeCertificate
- ImbalancedChen.Certificates.P2HistoricalThirdMeanDispatch

A following P2 request records the exact source SHA, source/report blobs and key actual suppliers. Serialize with existing work and reuse accepted exact objects; no duplicate run is requested. Compile the full actual import closure under unchanged current strict/resource/trust gates, then same-object kernel replay, complete compiler type/inventory/axiom audit and audit replay. Do not promote a semantic relation to executable acceptance merely because the target compiles.

Pins unchanged: leanprover/lean4:v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; goldbach 09b97db5764ade1246bfb77206baa1b124760958; LeanArchitect 78dd66840d3efe8c824c699fc03381cec817c271; Batteries 41bd267b3f6b7252f6676af46d4ffc6783b64de9.
lake-manifest.json remains 86cb11a7a4b1c8ee3cd1d583985b4c7877933a4f; lean-toolchain fd85b262bf1c734663aa8292b0101f672168788f.

Next: obtain actual entry data and prove the exact per-leaf directed comparisons; reuse this mixed positional consumer and the existing specialized nonordinary/zero-leaf rules. Do not recreate tree aggregation, generic rounding, P1 history, paired finite checks or P4 tail analysis.
